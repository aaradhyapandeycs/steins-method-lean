"""Lean side of the reader, read from one pinned git commit.

Everything comes from `git show <commit>:<path>`, so line numbers match the
GitHub links and uncommitted work in the checkout is never shown. Status is
taken only from the reviewed ledger (`docs/COVERAGE.md`) combined with the
full 122-environment paper inventory (`docs/source-inventory.json`); any
inventory item or statement entry without an accepted COVERAGE record is
shown as `open` (not yet reviewed), never as proved.
"""

from __future__ import annotations

import html
import json
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

REPO = "https://github.com/aaradhyapandeycs/steins-method-lean"

NUMBERED_KINDS = {
    "theorem", "proposition", "lemma", "corollary",
    "definition", "remark", "example", "case", "condition",
}

ENV_TITLES = {
    "theorem": "Theorem",
    "proposition": "Proposition",
    "lemma": "Lemma",
    "corollary": "Corollary",
    "definition": "Definition",
    "remark": "Remark",
    "example": "Example",
    "case": "Case",
    "condition": "Condition",
}

# Status chip labels aligned with docs/COVERAGE.md status vocabulary.
STATUS_LABELS = {
    "proved":       ("proved", "st-proved"),
    "defined":      ("defined", "st-defined"),
    "corrected":    ("corrected", "st-corrected"),
    "restricted":   ("restricted", "st-restricted"),
    "source-issue": ("source issue", "st-source-issue"),
    "open":         ("open", "st-open"),
}

ENTRY_LABELS = dict(
    STATUS_LABELS,
    partial=("partial", "st-partial"),
    incomplete=("open", "st-open"),
    supporting=("supporting entry, proved in Lean", "st-supporting"),
    pending=("proved in Lean, review pending", "st-pending"),
)

MARKERS = {
    "refuted":        "✕ refuted in Lean",
    "exercise":       "exercise",
    "also-corrected": "corrected",
}


def esc(t: str) -> str:
    return html.escape(str(t), quote=False)


def attr(t: str) -> str:
    return html.escape(str(t), quote=True)


def span(a: int, b: int) -> str:
    return str(a) if a == b else f"{a}–{b}"


_ROMAN_SMALL = ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x"]
_SHORTHAND_RANGE_RE = re.compile(
    r"`([A-Za-z_][A-Za-z0-9_']*?)_([0-9]+|[ivx]+)`\s*[–-]\s*`_([0-9]+|[ivx]+)`"
)


def expand_lean_shorthands(cell: str) -> str:
    """Expand backticked suffix ranges like `` `Sec5_3_item_1`–`_4` `` or `` `Sec5_3_step_i`–`_iii` ``."""

    def repl(m: re.Match[str]) -> str:
        prefix, start_tok, end_tok = m.group(1), m.group(2), m.group(3)
        if start_tok.isdigit() and end_tok.isdigit():
            a, b = int(start_tok), int(end_tok)
            if a <= b and b - a <= 50:
                return ", ".join(f"`{prefix}_{k}`" for k in range(a, b + 1))
        if start_tok in _ROMAN_SMALL and end_tok in _ROMAN_SMALL:
            ia, ib = _ROMAN_SMALL.index(start_tok), _ROMAN_SMALL.index(end_tok)
            if ia <= ib:
                return ", ".join(f"`{prefix}_{_ROMAN_SMALL[k]}`" for k in range(ia, ib + 1))
        return m.group(0)

    return _SHORTHAND_RANGE_RE.sub(repl, cell)


def split_md_row(line: str) -> list[str]:
    """Split a Markdown table row on unescaped `|` outside backticks."""
    s = line.strip()
    if s.startswith("|"):
        s = s[1:]
    if s.endswith("|") and not s.endswith(r"\|"):
        s = s[:-1]
    cells: list[str] = []
    cur: list[str] = []
    in_bt = False
    esc_next = False
    for ch in s:
        if esc_next:
            if ch != "|":
                cur.append("\\")
            cur.append(ch)
            esc_next = False
        elif ch == "\\":
            esc_next = True
        elif ch == "`":
            in_bt = not in_bt
            cur.append(ch)
        elif ch == "|" and not in_bt:
            cells.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    cells.append("".join(cur).strip())
    return cells


def chip(label: str | None, markers=(), sub: str = "", issues: str = "") -> str:
    """Status chip, optional markers (`refuted`, `exercise`), sub-reason, and issue links."""
    out = []
    if label:
        word, cls = ENTRY_LABELS.get(label, ENTRY_LABELS["open"])
        out.append(f'<span class="status {cls}">{esc(word)}</span>')
    for m in markers:
        m_text = MARKERS.get(m, m)
        out.append(f'<span class="marker mk-{attr(m)}">{esc(m_text)}</span>')
    if sub and label in ("open", "incomplete", "supporting", None):
        out.append(f'<span class="subreason">{esc(sub)}</span>')
    if issues:
        out.append(f'<span class="issues">{issues}</span>')
    return "".join(out)


def code_block(code: str, line_start: int = 1) -> str:
    lines = []
    for i, line in enumerate(code.rstrip("\n").split("\n"), line_start):
        lines.append(f'<span class="ln">{i}</span>{esc(line)}')
    content = "\n".join(lines)
    return f'<pre class="lean"><code>{content}</code></pre>'


class Git:
    def __init__(self, root: Path, rev: str):
        self.root = root
        self.rev = self.run("rev-parse", rev).strip()
        self.cache: dict[str, str] = {}

    def run(self, *args) -> str:
        r = subprocess.run(["git", "-C", str(self.root), *args], capture_output=True, text=True)
        if r.returncode != 0:
            raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
        return r.stdout

    def show(self, path: str) -> str:
        if path not in self.cache:
            self.cache[path] = self.run("show", f"{self.rev}:{path}")
        return self.cache[path]

    def ls(self, prefix: str) -> list[str]:
        return [l for l in self.run("ls-tree", "-r", "--name-only", self.rev, "--", prefix).splitlines() if l]

    def grep(self, pattern: str, prefix: str) -> list[tuple[str, int, str]]:
        r = subprocess.run(
            ["git", "-C", str(self.root), "grep", "-n", "-E", pattern, self.rev, "--", prefix],
            capture_output=True, text=True,
        )
        out = []
        for line in r.stdout.splitlines():
            parts = line.split(":", 3)
            if len(parts) >= 4:
                _, path, num, text = parts
                out.append((path, int(num), text))
        return out

    def blob(self, path: str, a: int | None = None, b: int | None = None) -> str:
        frag = f"#L{a}-L{b}" if a and b and b != a else (f"#L{a}" if a else "")
        return f"{REPO}/blob/{self.rev}/{path}{frag}"


@dataclass
class Entry:
    name: str
    full: str
    file: str
    line_start: int
    line_end: int
    source: str
    section: str = "1"
    primary_labels: list[str] = field(default_factory=list)
    labels: list[str] = field(default_factory=list)
    ranges: list[dict] = field(default_factory=list)
    proof: dict | None = None
    record: dict | None = None
    status: str = "open"
    markers: list[str] = field(default_factory=list)
    subreason: str = ""
    refutations: list[dict] = field(default_factory=list)
    exports: list[dict] = field(default_factory=list)
    issues: list[str] = field(default_factory=list)
    doc: str = ""


@dataclass
class DefCard:
    id: str
    env_id: str
    title: str
    section: str
    line_start: int
    line_end: int
    status: str
    subreason: str
    accepted: str
    markers: list[str] = field(default_factory=list)
    issues: list[str] = field(default_factory=list)
    decls: list[dict] = field(default_factory=list)


@dataclass
class LedgerCard:
    id: str
    source: str
    section: str
    labels: list[str]
    ranges: list[dict]
    status: str
    markers: list[str]
    subreason: str
    note: str
    accepted: str
    issues: list[str]
    decls: list[dict] = field(default_factory=list)
    env_id: str = ""


RANGE_RE = re.compile(r"`?((?:[\w-]+/)*[\w-]+\.tex):(\d+)(?:[–-](\d+))?`?")
TEX_LINE_RE = re.compile(r"(\d+)(?:[–-](\d+))?")
EXPL_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}|`([A-Za-z0-9_-]+:[^`\s]+)`|`([A-Za-z][\w-]*\d+[\w-]*)`")
ISSUE_RE = re.compile(r"\b(ISSUE-[\w.-]+)\b")
REFUT_DECL_RE = re.compile(
    r"\b(not_[\w']+|[\w']+_counterexample|[\w']+_noSolution|"
    r"antiVoterStep_support_nonconst|antiVoterStep_const_eq_zero|"
    r"zero_stdNormalLaw_isZeroBias_unbounded)\b"
)
REFUT_PHRASE_RE = re.compile(
    r"\b(?:not_[\w']+|[\w']+_counterexample|[\w']+_noSolution|"
    r"antiVoterStep_const_eq_zero|zero_stdNormalLaw_isZeroBias_unbounded|"
    r"machine-check(?:s|ed))\b"
)
DECL_RE = re.compile(
    r"/--(?P<doc>.*?)-/\s*\n(?P<decl>(?:noncomputable\s+)?def\s+(?P<name>[\w']+)\b.*?"
    r"(?=\n\s*\n|\n/--|\nend\b|\Z))", re.S
)
LIB_DECL_RE = re.compile(
    r"^(?:\s*)(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?P<kind>theorem|lemma|def|structure|class|abbrev|inductive)\s+(?P<name>[\w']+)\b"
)
DOC_DECL_RE = re.compile(
    r"/--(?P<doc>.*?)-/\s*\n(?P<decl>(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?:def|structure|class|abbrev|inductive)\s+(?P<name>[\w']+)\b)", re.S
)
TOP_DECL = re.compile(
    r"^(?:@\[|/--|theorem |lemma |def |noncomputable |private |protected |instance |"
    r"structure |class |abbrev |inductive |namespace |section |end\b|open |variable |"
    r"example |set_option |#|universe |attribute )"
)


def namespace_at(text: str, upto: int) -> str:
    stack = []
    for line in text.splitlines()[:upto - 1]:
        m = re.match(r"namespace\s+([\w.]+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"end\s+([\w.]+)\s*$", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    return ".".join(stack)


def decl_extent(lines: list[str], start: int, cap: int = 400):
    a = start
    while a > 1 and lines[a - 2].lstrip().startswith("@["):
        a -= 1
    if a > 1 and lines[a - 2].rstrip().endswith("-/"):
        k = a - 1
        while k >= 1 and "/-" not in lines[k - 1]:
            k -= 1
        if k >= 1:
            a = k
            while a > 1 and lines[a - 2].lstrip().startswith("@["):
                a -= 1
    b = start
    while b < len(lines) and not TOP_DECL.match(lines[b]):
        b += 1
    while b > start and not lines[b - 1].strip():
        b -= 1
    truncated = b - a + 1 > cap
    if truncated:
        b = a + cap - 1
    return a, b, truncated


class LeanIndex:
    def __init__(self, git: Git, inventory_labels: set):
        self.git = git
        self.inv_labels = inventory_labels
        self.entries: list[Entry] = []
        self.coverage_rows: list[dict] = []
        self.entries_by_lean_name: dict[str, dict] = {}
        self.issue_slugs: dict[str, dict] = {}
        self.lib_decls: dict[str, dict] = {}
        self.def_decls_by_num: dict[str, list[dict]] = {}
        self.accepted_defs: dict[str, dict] = {}
        self.extra_refutations_by_issue: dict[str, list[str]] = {}
        self.def_cards: list[DefCard] = []
        self.ledger_cards: list[LedgerCard] = []
        self.numbered_items: list[dict] = []
        self.prose_items: list[dict] = []
        self.unreviewed_prose_items: list[dict] = []

        # Load pinned source inventory
        try:
            inv_raw = self.git.show("docs/source-inventory.json")
        except Exception:
            inv_path = self.git.root / "docs/source-inventory.json"
            inv_raw = inv_path.read_text(encoding="utf-8") if inv_path.is_file() else '{"entries":[],"labels":[]}'
        self.inventory = json.loads(inv_raw)

        # Load SOURCE-ISSUES headings
        try:
            issues_text = self.git.show("docs/SOURCE-ISSUES.md")
            self.issue_slugs = self.parse_issues(issues_text)
        except Exception:
            self.issue_slugs = {}

        # Index library declarations (for refutation theorems and Definition X.Y objects)
        self.index_library_decls()

        # Load COVERAGE.md
        try:
            cov_text = self.git.show("docs/COVERAGE.md")
            self.parse_coverage(cov_text)
        except Exception as ex:
            print(f"Warning loading COVERAGE.md: {ex}")

        # Load Formalization/Statements/Sec*.lean
        self.load_entries()

        # Build full 122-environment + prose item inventory & auxiliary cards
        self.build_full_inventory()

    # ------------------------------------------------------------------
    # Library declarations index
    # ------------------------------------------------------------------

    def index_library_decls(self):
        for f in sorted(self.git.ls("Formalization")):
            if not f.endswith(".lean") or f.startswith("Formalization/Statements/"):
                continue
            try:
                text = self.git.show(f)
            except Exception:
                continue
            lines = text.splitlines()
            for idx, line in enumerate(lines, 1):
                m = LIB_DECL_RE.match(line)
                if m:
                    name = m.group("name")
                    a, b, trunc = decl_extent(lines, idx, cap=120)
                    info = {
                        "name": name,
                        "kind": m.group("kind"),
                        "file": f,
                        "line_start": a,
                        "line_end": b,
                        "source": "\n".join(lines[a - 1:b]),
                        "truncated": trunc,
                    }
                    self.lib_decls.setdefault(name, info)

            if f.startswith("Formalization/Defs/") and not f.endswith("Sanity.lean"):
                for dm in DOC_DECL_RE.finditer(text):
                    doc = dm.group("doc")
                    name = dm.group("name")
                    decl_line = text.count("\n", 0, dm.start("decl")) + 1
                    a, b, trunc = decl_extent(lines, decl_line, cap=120)
                    issues = list(dict.fromkeys(ISSUE_RE.findall(doc)))
                    for num_m in re.finditer(r"\bDefinition\s+(\d+\.\d+)\b", doc):
                        num = num_m.group(1)
                        self.def_decls_by_num.setdefault(num, []).append({
                            "name": name,
                            "file": f,
                            "line_start": a,
                            "line_end": b,
                            "source": "\n".join(lines[a - 1:b]),
                            "issues": issues,
                            "truncated": trunc,
                        })

    # ------------------------------------------------------------------
    # COVERAGE.md parsing
    # ------------------------------------------------------------------

    @staticmethod
    def parse_issues(text: str) -> dict:
        out = {}
        for line in text.splitlines():
            m = re.match(r"#+\s+(.*?\b(ISSUE-[\w.-]+)\b.*)$", line)
            if m:
                iss_id = m.group(2)
                title = m.group(1).strip()
                slug = re.sub(r"[^\w\- ]", "", title.lower()).replace(" ", "-")
                out[iss_id] = {"title": title, "slug": slug}
        return out

    def parse_coverage(self, cov_text: str):
        # First parse prose notes after the table for accepted definitions and extra refutation witnesses
        non_table_lines = [l for l in cov_text.splitlines() if not l.strip().startswith("|")]
        prose_text = "\n".join(non_table_lines)
        for para in prose_text.split("\n\n"):
            p_low = para.lower()
            if "not yet covered" in p_low:
                continue
            if "accepted" in p_low:
                rev_m = re.search(r"\breview-[\w-]+\b", para)
                rev_tag = rev_m.group(0) if rev_m else "COVERAGE.md"
                for m in re.finditer(r"`([\w']+)`(?:\s*\(([^)]*)\))?", para):
                    dname = m.group(1)
                    paren = m.group(2) or ""
                    self.accepted_defs[dname] = {
                        "status": "defined",
                        "corrected": "corrected" in paren.lower(),
                        "restricted": "restricted" in paren.lower(),
                        "issues": list(dict.fromkeys(ISSUE_RE.findall(paren))),
                        "accepted": rev_tag,
                        "note": paren,
                    }
                # Map refutation declarations mentioned in prose paragraphs to issues/items
                refuts = REFUT_DECL_RE.findall(para)
                if refuts:
                    for iss in ISSUE_RE.findall(para):
                        self.extra_refutations_by_issue.setdefault(iss, [])
                        for rf in refuts:
                            if rf not in self.extra_refutations_by_issue[iss]:
                                self.extra_refutations_by_issue[iss].append(rf)
                    for rf in refuts:
                        if rf.startswith("Ex3_9_"):
                            self.extra_refutations_by_issue.setdefault("ISSUE-3.9", [])
                            if rf not in self.extra_refutations_by_issue["ISSUE-3.9"]:
                                self.extra_refutations_by_issue["ISSUE-3.9"].append(rf)
                        if rf == "zero_stdNormalLaw_isZeroBias_unbounded":
                            self.extra_refutations_by_issue.setdefault("ISSUE-3.19-3.6", [])
                            if rf not in self.extra_refutations_by_issue["ISSUE-3.19-3.6"]:
                                self.extra_refutations_by_issue["ISSUE-3.19-3.6"].append(rf)

        rows = []
        for idx, raw_line in enumerate(cov_text.splitlines()):
            line = raw_line.strip()
            if not line.startswith("| ") or line.startswith("| ---") or line.startswith("| Source result"):
                continue
            cells = split_md_row(line)
            if len(cells) < 6:
                continue

            source_item, label_cell, tex_lines, lean_cell, raw_status, accepted = cells[:6]

            # Determine section number
            sec = "1"
            m_sec = re.search(
                r"(?:Proposition|Lemma|Theorem|Corollary|Example|Remark|Definition|Display)\s*\(?(\d+)",
                source_item,
            )
            if m_sec:
                sec = m_sec.group(1)
            else:
                m_sec2 = re.search(r"§(\d+)", source_item)
                if m_sec2:
                    sec = m_sec2.group(1)
                else:
                    m_sec3 = re.search(r"(?:Prop|Lem|Thm|Cor|Ex|Rem|Def|Sec)(\d+)", lean_cell)
                    if m_sec3:
                        sec = m_sec3.group(1)

            acc_clean = accepted.strip()
            is_accepted = bool(acc_clean and acc_clean not in ("—", "-"))
            labels = [l.strip("`") for l in re.findall(r"`([^`]+)`", label_cell)]
            expanded_lean_cell = expand_lean_shorthands(lean_cell)
            lean_names = [n.strip("`").replace("SteinMethod.", "") for n in re.findall(r"`([^`]+)`", expanded_lean_cell)]
            issues = list(dict.fromkeys(ISSUE_RE.findall(raw_status + " " + lean_cell)))

            # Parse TeX line ranges from column 3
            ranges = []
            for rm in TEX_LINE_RE.finditer(tex_lines):
                a = int(rm.group(1))
                b = int(rm.group(2) or rm.group(1))
                ranges.append({"file": "SteinIntro.tex", "line_start": a, "line_end": b})

            # Categorize row status (strictly using COVERAGE vocabulary)
            s_low = raw_status.lower()
            if s_low.startswith("source issue"):
                norm_status = "source-issue"
            elif not is_accepted:
                norm_status = "open"
            elif (
                s_low.startswith("definition accepted")
                or s_low.startswith("definition ")
                or source_item.startswith("Definition ")
            ):
                norm_status = "defined"
            elif s_low.startswith("corrected") or (
                "corrected" in s_low and not s_low.startswith("proved") and not s_low.startswith("restricted")
            ):
                norm_status = "corrected"
            elif s_low.startswith("restricted") or ("restricted" in s_low and not s_low.startswith("proved")):
                norm_status = "restricted"
            elif "proved" in s_low:
                if any("_corrected" in n for n in lean_names):
                    norm_status = "corrected"
                elif any("_restricted" in n for n in lean_names):
                    norm_status = "restricted"
                else:
                    norm_status = "proved"
            else:
                norm_status = "open"

            # Extract markers (`refuted`, `exercise`, `also-corrected`) and refutation theorem names
            markers: list[str] = []
            if norm_status == "defined" and "corrected" in s_low:
                markers.append("also-corrected")
            if s_low.startswith("exercise") or ("exercise" in s_low and not is_accepted):
                markers.append("exercise")
            if REFUT_PHRASE_RE.search(raw_status + " " + lean_cell):
                markers.append("refuted")

            refut_names = list(dict.fromkeys(REFUT_DECL_RE.findall(raw_status + " " + lean_cell)))
            for iss in issues:
                if iss in ("ISSUE-3.9", "ISSUE-3.8", "ISSUE-3.5"):
                    for extra_rf in self.extra_refutations_by_issue.get(iss, []):
                        if extra_rf not in refut_names:
                            refut_names.append(extra_rf)
            if "3.6.1" in source_item and "refuted" in markers:
                for extra_rf in self.extra_refutations_by_issue.get("ISSUE-3.19-3.6", []):
                    if extra_rf not in refut_names:
                        refut_names.append(extra_rf)

            refutations = [self.lib_decls[rn] for rn in refut_names if rn in self.lib_decls]

            subreason = ""
            if norm_status == "open":
                if "exercise" in markers:
                    subreason = "exercise left to the reader"
                elif "qualitative" in s_low:
                    subreason = "qualitative remark"
                else:
                    subreason = "not yet proved"

            rec = {
                "row_index": idx,
                "source": source_item,
                "label": label_cell.replace("`", "").strip(),
                "labels": labels,
                "tex_lines": tex_lines,
                "ranges": ranges,
                "lean": lean_cell.replace("`", "").replace("SteinMethod.", "").strip(),
                "lean_names": lean_names,
                "raw_status": raw_status,
                "accepted": acc_clean if is_accepted else "",
                "is_accepted": is_accepted,
                "section": sec,
                "status": norm_status,
                "markers": markers,
                "subreason": subreason,
                "issues": issues,
                "refutations": refutations,
                "note": raw_status,
            }
            rows.append(rec)

            for name in lean_names:
                if norm_status == "source-issue":
                    entry_status = "source-issue"
                elif not is_accepted:
                    entry_status = "open"
                elif norm_status == "defined":
                    entry_status = "defined"
                elif "_corrected" in name:
                    entry_status = "corrected"
                elif "_restricted" in name:
                    entry_status = "restricted"
                elif norm_status in ("corrected", "restricted") and len(lean_names) == 1:
                    entry_status = norm_status
                else:
                    entry_status = "proved" if is_accepted else "open"

                self.entries_by_lean_name[name] = dict(rec, status=entry_status)

        self.coverage_rows = rows

    # ------------------------------------------------------------------
    # Lean statement files parsing
    # ------------------------------------------------------------------

    def load_entries(self):
        files = [f for f in self.git.ls("Formalization/Statements")
                 if re.search(r"/Sec\d+\.lean$", f)]

        for f in sorted(files, key=lambda x: int(re.search(r"Sec(\d+)", x).group(1))):
            sec_num = re.search(r"Sec(\d+)", f).group(1)
            text = self.git.show(f)
            proof_file = f.replace(".lean", "Proofs.lean")
            proofs = self.parse_proofs(proof_file)

            for m in DECL_RE.finditer(text):
                doc = m.group("doc")
                start = text.count("\n", 0, m.start()) + 1
                end = text.count("\n", 0, m.end("decl")) + 1
                name = m.group("name")
                ns = namespace_at(text, start)
                full = f"{ns}.{name}" if ns else name

                expl_labels = list(dict.fromkeys(EXPL_LABEL_RE.findall(doc)))
                labels = list(expl_labels)
                for match in LABEL_RE.findall(doc):
                    for g in match:
                        if g and g not in labels and not g.endswith(".tex"):
                            labels.append(g)

                ranges = []
                for r in RANGE_RE.findall(doc):
                    ranges.append({
                        "file": r[0],
                        "line_start": int(r[1]),
                        "line_end": int(r[2] or r[1]),
                    })

                issues = list(dict.fromkeys(ISSUE_RE.findall(doc)))

                e = Entry(
                    name=name,
                    full=full,
                    file=f,
                    line_start=start,
                    line_end=end,
                    source=text[m.start():m.end("decl")],
                    section=sec_num,
                    primary_labels=expl_labels[:1],
                    labels=labels,
                    ranges=ranges,
                    issues=issues,
                    doc=doc,
                )
                e.proof = proofs.get(name)

                rec = self.entries_by_lean_name.get(name)
                if rec:
                    e.record = rec
                    e.status = rec["status"]
                    e.markers = list(rec.get("markers", []))
                    e.subreason = rec.get("subreason", "")
                    e.refutations = list(rec.get("refutations", []))
                    for iss in rec.get("issues", []):
                        if iss not in e.issues:
                            e.issues.append(iss)
                    if rec.get("labels"):
                        e.primary_labels = list(rec["labels"])
                        for lab in rec["labels"]:
                            if lab not in e.labels:
                                e.labels.insert(0, lab)
                    if not e.ranges and rec.get("ranges"):
                        e.ranges = list(rec["ranges"])
                else:
                    # Compiled in SecN.lean, but not yet accepted in COVERAGE.md
                    e.status = "open"
                    e.subreason = "Lean work in progress, not yet reviewed"

                self.entries.append(e)

    def parse_proofs(self, path: str) -> dict:
        try:
            text = self.git.show(path)
        except Exception:
            return {}
        lines = text.splitlines()
        out = {}
        for i, line in enumerate(lines, 1):
            m = re.match(r"^\s*(?:noncomputable\s+)?theorem\s+([\w']+)_holds\b", line)
            if m:
                a, b, trunc = decl_extent(lines, i, cap=200)
                out[m.group(1)] = {
                    "file": path,
                    "line_start": a,
                    "line_end": b,
                    "source": "\n".join(lines[a - 1:b]),
                    "truncated": trunc,
                    "name": f"{m.group(1)}_holds",
                }
        return out

    # ------------------------------------------------------------------
    # Full 122-environment + prose inventory construction
    # ------------------------------------------------------------------

    def build_full_inventory(self):
        stmt_names = {e.name: e for e in self.entries}
        matched_row_indices: set[int] = set()
        matched_stmt_names: set[str] = set()

        num_envs = [e for e in self.inventory.get("entries", []) if e.get("kind") in NUMBERED_KINDS]

        for env in num_envs:
            kind = env["kind"]
            kind_title = ENV_TITLES.get(kind, kind.capitalize())
            num = env["number"]
            sec = str(env.get("chapter") or num.split(".")[0])
            sr = (env.get("source_ranges") or [{"line_start": 0, "line_end": 0}])[0]
            ls, le = int(sr.get("line_start", 0)), int(sr.get("line_end", 0))
            elabs = list(env.get("labels") or [])

            pat = re.compile(rf"^{re.escape(kind_title)}\s+{re.escape(num)}(?:\b|\()")
            mrows = [r for r in self.coverage_rows if pat.match(r["source"])]
            for r in mrows:
                matched_row_indices.add(r["row_index"])
                r["env_id"] = env["id"]

            # Check any unreviewed compiled SecN.lean entries matching this environment
            wip_entries = []
            for e in self.entries:
                if e.record is not None:
                    continue
                hit = False
                if elabs and (set(elabs) & set(e.primary_labels or e.labels[:1])):
                    hit = True
                elif e.ranges and ls and le:
                    r0 = e.ranges[0]
                    if max(ls, r0["line_start"]) <= min(le, r0["line_end"]):
                        hit = True
                elif re.search(rf"\b{re.escape(kind_title)}\s+{re.escape(num)}\b", e.doc):
                    hit = True
                if hit:
                    wip_entries.append(e)
                    matched_stmt_names.add(e.name)

            for r in mrows:
                for ln in r["lean_names"]:
                    if ln in stmt_names:
                        matched_stmt_names.add(ln)

            markers: list[str] = []
            for r in mrows:
                for mk in r["markers"]:
                    if mk not in markers:
                        markers.append(mk)

            lean_names: list[str] = []
            for r in mrows:
                for ln in r["lean_names"]:
                    if ln not in lean_names:
                        lean_names.append(ln)
            for we in wip_entries:
                if we.name not in lean_names:
                    lean_names.append(we.name)

            status = "open"
            subreason = "not yet reviewed"
            note = ""

            if mrows:
                acc_rows = [r for r in mrows if r["is_accepted"]]
                note = "; ".join(r["raw_status"] for r in mrows)
                if acc_rows:
                    sts = [r["status"] for r in acc_rows]
                    if kind == "definition" or "defined" in sts:
                        status = "defined"
                        if "corrected" in sts and "also-corrected" not in markers:
                            markers.append("also-corrected")
                    elif "corrected" in sts:
                        status = "corrected"
                    elif "restricted" in sts:
                        status = "restricted"
                    elif "proved" in sts:
                        status = "proved"
                    elif "source-issue" in sts:
                        status = "source-issue"
                    else:
                        status = "open"
                    subreason = ""
                else:
                    if any(r["status"] == "source-issue" for r in mrows):
                        status = "source-issue"
                        subreason = ""
                    else:
                        status = "open"
                        subreason = mrows[0]["subreason"] or (
                            "Lean work in progress, not yet reviewed" if wip_entries else "not yet reviewed"
                        )
            elif kind == "definition" and num in self.def_decls_by_num:
                decls = self.def_decls_by_num[num]
                for d in decls:
                    if d["name"] not in lean_names:
                        lean_names.append(d["name"])
                acc_infos = [self.accepted_defs[d["name"]] for d in decls if d["name"] in self.accepted_defs]
                if acc_infos:
                    status = "defined"
                    if any(ai.get("corrected") for ai in acc_infos) and "also-corrected" not in markers:
                        markers.append("also-corrected")
                    subreason = ""
                    acc_rev = acc_infos[0]["accepted"]
                    note = f"Formalized in Formalization/Defs ({', '.join(d['name'] for d in decls)}); accepted in {acc_rev}."
                else:
                    status = "open"
                    subreason = "Lean work in progress, not yet reviewed"
                    note = f"Work in progress in Formalization/Defs ({', '.join(d['name'] for d in decls)}); not yet reviewed."

                all_issues: list[str] = []
                for d in decls:
                    for iss in d.get("issues", []):
                        if iss not in all_issues:
                            all_issues.append(iss)
                for ai in acc_infos:
                    for iss in ai.get("issues", []):
                        if iss not in all_issues:
                            all_issues.append(iss)
                self.def_cards.append(DefCard(
                    id=f"def-{num.replace('.', '-')}",
                    env_id=env["id"],
                    title=f"Definition {num}",
                    section=sec,
                    line_start=ls,
                    line_end=le,
                    status=status,
                    subreason=subreason,
                    accepted=acc_infos[0]["accepted"] if acc_infos else "",
                    markers=list(markers),
                    issues=all_issues,
                    decls=decls,
                ))
            elif wip_entries:
                status = "open"
                subreason = "Lean work in progress, not yet reviewed"
                note = "Compiled in Formalization/Statements, not yet reviewed."

            self.numbered_items.append({
                "id": env["id"],
                "kind": kind,
                "number": num,
                "source": f"{kind_title} {num}",
                "label": ", ".join(elabs) if elabs else "—",
                "labels": elabs,
                "section": sec,
                "line_start": ls,
                "line_end": le,
                "status": status,
                "markers": markers,
                "subreason": subreason,
                "lean": ", ".join(lean_names),
                "lean_names": lean_names,
                "note": note,
                "is_prose": False,
            })

        # Tracked prose & display items from COVERAGE.md (rows not part of the 122 numbered envs)
        for r in self.coverage_rows:
            for ln in r["lean_names"]:
                if ln in stmt_names:
                    matched_stmt_names.add(ln)

            # Build LedgerCard for any COVERAGE row that has no Sec*.lean Entry
            has_stmt_entry = any(ln in stmt_names for ln in r["lean_names"])
            if not has_stmt_entry:
                decls = [self.lib_decls[ln] for ln in r["lean_names"] if ln in self.lib_decls]
                for rf in r.get("refutations", []):
                    if rf not in decls:
                        decls.append(rf)
                slug = re.sub(r"[^A-Za-z0-9]+", "-", r["source"]).strip("-").lower()
                self.ledger_cards.append(LedgerCard(
                    id=f"cov-{r['row_index']}-{slug}",
                    source=r["source"],
                    section=r["section"],
                    labels=r["labels"],
                    ranges=r["ranges"],
                    status=r["status"],
                    markers=r["markers"],
                    subreason=r["subreason"],
                    note=r["raw_status"],
                    accepted=r["accepted"],
                    issues=r["issues"],
                    decls=decls,
                    env_id=r.get("env_id", ""),
                ))

            if r["row_index"] not in matched_row_indices:
                r0 = r["ranges"][0] if r["ranges"] else {"line_start": 0, "line_end": 0}
                self.prose_items.append({
                    "id": f"prose-{r['row_index']}",
                    "kind": "prose",
                    "number": "",
                    "source": r["source"],
                    "label": ", ".join(r["labels"]) if r["labels"] else "—",
                    "labels": r["labels"],
                    "section": r["section"],
                    "line_start": r0["line_start"],
                    "line_end": r0["line_end"],
                    "status": r["status"],
                    "markers": list(r["markers"]),
                    "subreason": r["subreason"],
                    "lean": ", ".join(r["lean_names"]),
                    "lean_names": list(r["lean_names"]),
                    "note": r["raw_status"],
                    "is_prose": True,
                })

        # Also capture any unreviewed prose SecN_* entries not yet in COVERAGE.md
        for e in self.entries:
            if e.name not in matched_stmt_names and e.record is None:
                r0 = e.ranges[0] if e.ranges else {"line_start": 0, "line_end": 0}
                self.unreviewed_prose_items.append({
                    "id": f"wip-{e.name}",
                    "kind": "prose",
                    "number": "",
                    "source": f"§{e.section} prose ({e.name})",
                    "label": ", ".join(e.primary_labels) if e.primary_labels else "—",
                    "labels": list(e.primary_labels),
                    "section": e.section,
                    "line_start": r0["line_start"],
                    "line_end": r0["line_end"],
                    "status": "open",
                    "markers": [],
                    "subreason": "Lean work in progress, not yet reviewed",
                    "lean": e.name,
                    "lean_names": [e.name],
                    "note": "Work in progress in Formalization/Statements; not yet reviewed.",
                    "is_prose": True,
                })

    # ------------------------------------------------------------------
    # Queries & Summary Counts
    # ------------------------------------------------------------------

    def coverage_status(self, entry_name: str) -> str:
        rec = self.entries_by_lean_name.get(entry_name)
        if rec:
            return rec.get("status", "open")
        return "open"

    def coverage_counts(self) -> dict:
        keys = ("proved", "defined", "corrected", "restricted", "source-issue", "open")
        num_total = {k: 0 for k in keys}
        by_sec: dict[str, dict[str, int]] = {
            str(s): {k: 0 for k in keys} | {"total": 0, "formalized": 0, "wip": 0}
            for s in range(1, 8)
        }
        num_wip = 0
        refuted_num = 0
        exercise_num = 0

        for item in self.numbered_items:
            st = item["status"]
            sec = item["section"]
            num_total[st] = num_total.get(st, 0) + 1
            sec_d = by_sec.setdefault(sec, {k: 0 for k in keys} | {"total": 0, "formalized": 0, "wip": 0})
            sec_d[st] = sec_d.get(st, 0) + 1
            sec_d["total"] += 1
            if st in ("proved", "defined", "corrected", "restricted"):
                sec_d["formalized"] += 1
            if st == "open" and "Lean work in progress" in item.get("subreason", ""):
                num_wip += 1
                sec_d["wip"] += 1
            if "refuted" in item.get("markers", ()):
                refuted_num += 1
            if "exercise" in item.get("markers", ()):
                exercise_num += 1

        formalized_total = (
            num_total["proved"] + num_total["defined"] + num_total["corrected"] + num_total["restricted"]
        )

        prose_total = {k: 0 for k in keys}
        prose_by_sec: dict[str, dict[str, int]] = {
            str(s): {k: 0 for k in keys} | {"total": 0, "formalized": 0}
            for s in range(1, 8)
        }
        refuted_prose = 0
        exercise_prose = 0
        for item in self.prose_items:
            st = item["status"]
            sec = item["section"]
            prose_total[st] = prose_total.get(st, 0) + 1
            psec = prose_by_sec.setdefault(sec, {k: 0 for k in keys} | {"total": 0, "formalized": 0})
            psec[st] = psec.get(st, 0) + 1
            psec["total"] += 1
            if st in ("proved", "defined", "corrected", "restricted"):
                psec["formalized"] += 1
            if "refuted" in item.get("markers", ()):
                refuted_prose += 1
            if "exercise" in item.get("markers", ()):
                exercise_prose += 1

        prose_formalized = (
            prose_total["proved"] + prose_total["defined"] + prose_total["corrected"] + prose_total["restricted"]
        )

        return {
            "total": num_total,
            "numbered": {
                **num_total,
                "total": len(self.numbered_items),
                "formalized": formalized_total,
                "modified": num_total["corrected"] + num_total["restricted"],
                "wip": num_wip,
                "refuted": refuted_num,
                "exercise": exercise_num,
            },
            "prose": {
                **prose_total,
                "total": len(self.prose_items),
                "formalized": prose_formalized,
                "wip_untracked": len(self.unreviewed_prose_items),
                "refuted": refuted_prose,
                "exercise": exercise_prose,
            },
            "markers": {
                "refuted": refuted_num + refuted_prose,
                "exercise": exercise_num + exercise_prose,
            },
            "by_section": by_sec,
            "prose_by_section": prose_by_sec,
        }

    def summary_data(self) -> dict:
        c = self.coverage_counts()
        return {
            "summary": {
                "numbered": c["numbered"],
                "prose": c["prose"],
                "markers": c["markers"],
                "by_section": c["by_section"],
                "prose_by_section": c["prose_by_section"],
            }
        }

    def all_result_items(self) -> list[dict]:
        combined = list(self.numbered_items) + list(self.prose_items) + list(self.unreviewed_prose_items)
        return sorted(combined, key=lambda r: (int(r["section"]) if str(r["section"]).isdigit() else 99, r["line_start"], 1 if r["is_prose"] else 0))

    def coverage_entries(self) -> list[dict]:
        return self.all_result_items()

    def mathjax_macros(self) -> dict:
        return {}

    def label_number(self, label: str):
        return None

    # ------------------------------------------------------------------
    # Rendering
    # ------------------------------------------------------------------

    def md(self, text: str) -> str:
        """Render minimal inline Markdown: links, code, math."""
        text = re.sub(r"(?<![\\$])\$([^$\n]+?)\$", r"\\(\1\\)", text)
        parts = re.split(r"(`[^`]*`|\\\(.*?\\\))", text)
        out = []
        for p in parts:
            if p.startswith("`") and p.endswith("`") and len(p) > 1:
                out.append(f"<code>{esc(p[1:-1])}</code>")
            elif p.startswith("\\(") and p.endswith("\\)"):
                out.append(p)
            else:
                p_esc = esc(p)
                p_esc = re.sub(
                    r"\[([^\]]+)\]\(([^)]+)\)",
                    lambda m: (
                        f'<a href="{attr(self.git.blob("docs/" + m.group(2)) if not m.group(2).startswith(("http", "docs/", "#")) else m.group(2))}">'
                        f'{m.group(1)}</a>'
                    ),
                    p_esc,
                )
                out.append(p_esc)
        return "".join(out)

    def issue_links(self, ids: list[str]) -> str:
        links = []
        for iss in ids:
            info = self.issue_slugs.get(iss)
            slug = info["slug"] if info else iss.lower()
            title = info["title"] if info else iss
            links.append(
                f'<a href="{attr(self.git.blob("docs/SOURCE-ISSUES.md"))}#{attr(slug)}" '
                f'title="{attr(title)}">{esc(iss)}</a>'
            )
        return " · ".join(links)

    FIDELITY = {
        "proved": "as printed in the paper",
        "corrected": "a disclosed corrected form of the printed result",
        "restricted": "the printed result under disclosed additional assumptions",
        "defined": "a formalized definition",
    }

    def verification_html(self, e: Entry) -> str:
        """Proof completeness and statement fidelity, stated separately."""
        rev = self.git.rev[:7]
        if e.status == "open" and e.proof:
            proof = (f'complete at commit <code>{esc(rev)}</code>: <code>{esc(e.name)}_holds</code> and every '
                     'declaration it depends on compile without <code>sorry</code>, and the transitive axiom audit '
                     'admits only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code> '
                     '(CI run linked in the footer)')
            fid = "not yet reviewed against the source, so not yet counted as proved"
            return (f'<dl class="verif"><dt>Proof</dt><dd>{proof}</dd>'
                    f'<dt>Statement</dt><dd>{fid}</dd></dl>')
        if e.status in self.FIDELITY:
            proof = (f'complete at commit <code>{esc(rev)}</code>: <code>{esc(e.name)}_holds</code> and every '
                     'declaration it depends on compile without <code>sorry</code>, and the transitive axiom audit '
                     'admits only <code>propext</code>, <code>Classical.choice</code> and <code>Quot.sound</code> '
                     '(CI run linked in the footer)')
            note = ((e.record or {}).get("note") or "").lower()
            what = ("the project's precise reading of a claim the paper states only informally (no printed "
                    "statement to match)") if "project reading" in note else self.FIDELITY[e.status]
            fid = f'{what}; reviewed by an AI critic against the source, not by the author'
        elif e.status == "source-issue":
            proof = "the printed statement is refuted or ill-posed; see the source issue"
            fid = "not applicable"
        else:
            proof = f'statement formalized at commit <code>{esc(rev)}</code>; proof not yet accepted'
            fid = "not yet reviewed"
        return (f'<dl class="verif"><dt>Proof</dt><dd>{proof}</dd>'
                f'<dt>Statement</dt><dd>{fid}</dd></dl>')

    def card(self, e: Entry) -> str:
        rec = e.record or {}
        st = e.status
        pending = st == "open" and bool(e.proof)
        sub = e.subreason if st == "open" and not pending else ""
        header_chips = chip("pending" if pending else st, markers=e.markers, sub=sub)

        links = [
            f'<a href="{attr(self.git.blob(e.file, e.line_start, e.line_end))}">Lean statement '
            f'({esc(e.file.rsplit("/", 1)[-1])}:{span(e.line_start, e.line_end)})</a>'
        ]
        if rec.get("accepted"):
            links.append(f'review: {self.md(rec["accepted"])}')
        if e.issues:
            links.append(self.issue_links(e.issues))
        for rf in e.refutations:
            links.append(
                f'refutation: <a href="{attr(self.git.blob(rf["file"], rf["line_start"], rf["line_end"]))}">'
                f'<code>{esc(rf["name"])}</code></a>'
            )

        body = []
        if rec.get("note"):
            lead = "Source issue" if st == "source-issue" else "What is proved"
            body.append(
                f'<p class="what tex2jax_process"><strong>{lead}</strong> (COVERAGE ledger). '
                f'{self.md(rec["note"])}</p>'
            )
        elif pending:
            body.append(
                '<p class="what"><em>Proved in Lean, review pending. The statement and its proof compile at '
                'this commit and pass the axiom audit, but the critic has not yet checked that the statement '
                'matches the source, so it is not yet counted as proved.</em></p>'
            )
        elif st == "open":
            body.append(
                '<p class="what"><em>Work in progress. This statement compiles in Lean at this commit, '
                'but has not yet been reviewed by the critic or accepted into COVERAGE.md.</em></p>'
            )

        parts = [
            f'<article class="lean-card" id="lean-{attr(e.name)}">',
            f'<header>{header_chips}<code class="decl" title="{attr(e.full)}">{esc(e.name)}</code></header>',
            "".join(body),
            self.verification_html(e),
            getattr(self, "connections", {}).get(e.name, ""),
            f'<div class="meta">{" · ".join(links)}</div>',
            '<details><summary>Lean statement</summary>',
            code_block(e.source, e.line_start),
            '</details>',
        ]
        if e.proof:
            pr = e.proof
            parts.append(
                f'<details><summary>Proof <code>{esc(pr["name"])}</code></summary>'
                f'<div class="meta"><a href="{attr(self.git.blob(pr["file"], pr["line_start"], pr["line_end"]))}">'
                f'{esc(pr["file"].rsplit("/", 1)[-1])}:{span(pr["line_start"], pr["line_end"])}</a></div>'
                f'{code_block(pr["source"], pr["line_start"])}</details>'
            )
        for rf in e.refutations:
            parts.append(
                f'<details><summary>Refutation <code>{esc(rf["name"])}</code></summary>'
                f'<div class="meta"><a href="{attr(self.git.blob(rf["file"], rf["line_start"], rf["line_end"]))}">'
                f'{esc(rf["file"].rsplit("/", 1)[-1])}:{span(rf["line_start"], rf["line_end"])}</a></div>'
                f'{code_block(rf["source"], rf["line_start"])}</details>'
            )
        for ex in e.exports:
            parts.append(
                f'<details><summary>Library theorem <code>{esc(ex["name"])}</code></summary>'
                f'{code_block(ex["source"], ex["line_start"])}</details>'
            )
        parts.append('</article>')
        return "".join(parts)

    def def_card_html(self, dc: DefCard) -> str:
        header_chips = chip(dc.status, markers=dc.markers, sub=dc.subreason if dc.status == "open" else "")
        decl_names = ", ".join(d["name"] for d in dc.decls)
        links = []
        for d in dc.decls:
            links.append(
                f'<a href="{attr(self.git.blob(d["file"], d["line_start"], d["line_end"]))}">'
                f'<code>{esc(d["name"])}</code> ({esc(d["file"].rsplit("/", 1)[-1])}:{span(d["line_start"], d["line_end"])})</a>'
            )
        if dc.accepted:
            links.append(f'review: {esc(dc.accepted)}')
        if dc.issues:
            links.append(self.issue_links(dc.issues))

        if dc.status != "open":
            corr_note = "disclosed corrected variant; " if "also-corrected" in dc.markers else ""
            note_html = (
                f'<p class="what"><strong>Formalized definition</strong> ({corr_note}accepted in {esc(dc.accepted)}).</p>'
            )
        else:
            note_html = (
                '<p class="what"><em>Work in progress. Definition compiled in Formalization/Defs, not yet reviewed in COVERAGE.md.</em></p>'
            )
        details = "".join(
            f'<details><summary>Lean definition <code>{esc(d["name"])}</code></summary>'
            f'{code_block(d["source"], d["line_start"])}</details>'
            for d in dc.decls
        )
        return (
            f'<article class="lean-card" id="lean-{attr(dc.id)}">'
            f'<header>{header_chips}<code class="decl">{esc(decl_names)}</code></header>'
            f'{note_html}'
            f'<div class="meta">{" · ".join(links)}</div>'
            f'{details}</article>'
        )

    def ledger_card_html(self, lc: LedgerCard) -> str:
        header_chips = chip(lc.status, markers=lc.markers, sub=lc.subreason if lc.status == "open" else "")
        title_html = (
            f'<code class="decl">{esc(", ".join(d["name"] for d in lc.decls))}</code>'
            if lc.decls else f'<span class="item-name">{esc(lc.source)}</span>'
        )
        links = []
        for d in lc.decls:
            links.append(
                f'<a href="{attr(self.git.blob(d["file"], d["line_start"], d["line_end"]))}">'
                f'<code>{esc(d["name"])}</code> ({esc(d["file"].rsplit("/", 1)[-1])}:{span(d["line_start"], d["line_end"])})</a>'
            )
        if lc.accepted:
            links.append(f'review: {self.md(lc.accepted)}')
        if lc.issues:
            links.append(self.issue_links(lc.issues))

        lead = (
            "Source issue" if lc.status == "source-issue"
            else (
                "Formalized definition" if lc.status == "defined"
                else ("Exercise" if "exercise" in lc.markers else "COVERAGE ledger")
            )
        )
        details = "".join(
            f'<details><summary>Lean declaration <code>{esc(d["name"])}</code></summary>'
            f'{code_block(d["source"], d["line_start"])}</details>'
            for d in lc.decls
        )
        meta_html = f'<div class="meta">{" · ".join(links)}</div>' if links else ""
        return (
            f'<article class="lean-card" id="{attr(lc.id)}">'
            f'<header>{header_chips}{title_html}</header>'
            f'<p class="what tex2jax_process"><strong>{lead}</strong>. {self.md(lc.note)}</p>'
            f'{meta_html}{details}</article>'
        )
