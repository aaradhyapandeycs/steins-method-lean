"""Paper model for the Stein's method reader.

Adapted from the RL site's book.py with the following key changes:
- Single-file paper: ``docs/source/SteinIntro_utf8.tex`` (UTF-8 normalised).
- Sections (not chapters) are top-level pages (level = 1 in HEADINGS).
- Bibliography is loaded from ``docs/source/SteinIntro.bbl`` (a ``.bbl`` file).
- ``verify_source()`` checks the SHA-256 of ``SteinIntro_utf8.tex`` against
  ``source/provenance.json``'s ``normalized_files`` field.
- Figure conversion is attempted but degrades gracefully when absent.
- No ``chapters/commands.tex``; macros come from the preamble and MATH_OVERRIDES.
- Ross's probability macros are pre-loaded in MATH_OVERRIDES.
"""

from __future__ import annotations

import hashlib
import html
import json
import re
import shutil
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from .tex import Block, FileConverter, assemble, expand_calligraphic, label_id, mask_comments, mathjax_compat, parse_macros, read_group

TEX = "docs/source"           # relative to repo root
MAIN = "SteinIntro_utf8.tex"  # UTF-8 normalised copy

ENV_NAMES = {"theorem": "Theorem", "lemma": "Lemma", "corollary": "Corollary",
             "proposition": "Proposition", "definition": "Definition", "assumption": "Assumption",
             "claim": "Claim", "example": "Example", "remark": "Remark", "conjecture": "Conjecture",
             "fact": "Fact"}

# Ross's probability macros and MathJax compatibility overrides.
# These shadow any same-named preamble definitions so that the reader always
# produces valid MathJax even when the preamble uses low-level TeX tricks.
MATH_OVERRIDES: dict = {
    # Probability / statistics shorthand
    "IE":   (0, None, "\\mathbb{E}"),          # expectation
    "IP":   (0, None, "\\mathbb{P}"),          # probability measure
    "I":    (0, None, "\\mathbb{I}"),          # indicator
    "dtv":  (0, None, "d_{\\mathrm{TV}}"),    # total-variation distance
    "dw":   (0, None, "d_{\\mathrm{W}}"),     # Wasserstein distance
    "dk":   (0, None, "d_{\\mathrm{K}}"),     # Kolmogorov distance
    "Po":   (0, None, "\\mathrm{Po}"),        # Poisson distribution
    "Exp":  (0, None, "\\mathrm{Exp}"),       # Exponential distribution
    "Ge":   (0, None, "\\mathrm{Ge}"),        # Geometric (one variant)
    "Geo":  (0, None, "\\mathrm{Ge}^0"),      # \def\Geo{\Ge^0}: geometric on {0, 1, ...}
    "ER":   (0, None, "Erdős-Rényi"),         # text macro: \def\ER{Erd\H{o}s-R\'enyi}
    "var":  (0, None, "\\mathrm{Var}"),       # variance
    "cov":  (0, None, "\\mathrm{Cov}"),       # covariance
    # One-argument macros
    "abs":  (1, None, "\\left|#1\\right|"),
    "norm": (1, None, "\\left\\|#1\\right\\|"),
    # Number sets and independence
    "enskip": (0, None, "\\enspace"),
    "klr":    (1, None, "(#1)"),
    "bklr":   (1, None, "\\bigl(#1\\bigr)"),
    "bbklr":  (1, None, "\\Bigl(#1\\Bigr)"),
    "bbbklr": (1, None, "\\biggl(#1\\biggr)"),
    "bbbbklr": (1, None, "\\Biggl(#1\\Biggr)"),
    "kle":    (1, None, "[#1]"),
    "bkle":   (1, None, "\\bigl[#1\\bigr]"),
    "bbkle":  (1, None, "\\Bigl[#1\\Bigr]"),
    "bbbkle": (1, None, "\\biggl[#1\\biggr]"),
    "bbbbkle": (1, None, "\\Biggl[#1\\Biggr]"),
    "klg":    (1, None, "\\{#1\\}"),
    "bklg":   (1, None, "\\bigl\\{#1\\bigr\\}"),
    "bbklg":  (1, None, "\\Bigl\\{#1\\Bigr\\}"),
    "bbbklg": (1, None, "\\biggl\\{#1\\biggr\\}"),
    "bbbbklg": (1, None, "\\Biggl\\{#1\\Biggr\\}"),
    "P":    (0, None, "\\mathcal{P}_\\lambda"),  # \def\P{\%P_\lambda}
    "s":    (0, None, "\\sigma"),
    "dh":   (0, None, "d_{\\mathcal{H}}"),
    "IC":   (0, None, "\\mathbb{C}"),
    "II":   (0, None, "\\mathbb{I}"),
    "IN":   (0, None, "\\mathbb{N}"),
    "IR":   (0, None, "\\mathbb{R}"),
    "IS":   (0, None, "\\mathbb{S}"),
    "IZ":   (0, None, "\\mathbb{Z}"),
    "indep": (0, None, "\\perp\\!\\!\\!\\perp"),
    "independenT": (0, None, ""),
    "mathbbm": (1, None, "\\mathbb{#1}"),
    "protect": (0, None, ""),
    "mathpalette": (2, None, "#2"),
    # MathJax compatibility
    "xspace":        (0, None, ""),
    "mathds":        (1, None, "\\mathbb{#1}"),
    "bm":            (1, None, "\\boldsymbol{#1}"),
    "ensuremath":    (1, None, "#1"),
}


def esc(t: str) -> str:
    return html.escape(t, quote=False)


def attr(t: str) -> str:
    return html.escape(t, quote=True)


@dataclass
class Page:
    id: str
    title: str
    number: str | None
    section: str | None   # top-level section number (replaces "chapter" for this paper)
    level: int
    blocks: list = field(default_factory=list)


class Book:
    """Model of the single-file Stein's method paper."""

    def __init__(self, root: Path, out: Path):
        self.root = root
        self.out = out
        self.tex_root = root / TEX
        self.provenance = json.loads((root / "source/provenance.json").read_text())
        self.verify_source()
        # Optional inventory (not strictly required; graceful fallback if absent)
        inv_path = root / "docs/source-inventory.json"
        if inv_path.is_file():
            self.inventory = json.loads(inv_path.read_text())
        else:
            self.inventory = {"entries": [], "labels": []}
        self.by_pos: dict = {}
        for e in self.inventory["entries"]:
            if e.get("source_ranges"):
                r = e["source_ranges"][0]
                self.by_pos.setdefault((r["file"], r["line_start"]), []).append(e)
        self.by_id = {e["id"]: e for e in self.inventory["entries"]}
        self.label_owner = {l["label"]: self.by_id.get(l["owner_id"]) for l in self.inventory.get("labels", [])}
        self.macros = self.load_macros()
        self.bib = self.load_bib()
        self.cited: dict = {}
        self.unknown: dict = {}
        self.warnings: list = []
        self.footnotes = 0
        self.images: dict = {}
        self.used_pos: dict = {}

        # Seamless delegation for lean label_number calls
        try:
            from .lean import LeanIndex
            Book._active_book = self
            LeanIndex.label_number = lambda l_self, label: (
                self.label_number(label)[0] if self.label_number(label)[0] is not None else None
            )
        except Exception:
            pass

    # source ----------------------------------------------------------------
    def verify_source(self):
        """Check the SHA-256 of SteinIntro_utf8.tex against provenance.json."""
        normalized = self.provenance.get("normalized_files", {})
        bad = []
        for rel_path, expected_digest in normalized.items():
            path = self.root / rel_path
            if not path.is_file():
                bad.append(rel_path)
                continue
            actual = hashlib.sha256(path.read_bytes()).hexdigest()
            if actual != expected_digest:
                bad.append(rel_path)
        if bad:
            raise SystemExit(
                f"Pinned TeX missing or modified ({', '.join(bad[:5])}); "
                "run `python3 scripts/fetch_source.py` first."
            )

    def rel(self, path: Path) -> str:
        return path.relative_to(self.root).as_posix()

    def load_macros(self) -> dict:
        """Parse macros from the preamble of the main TeX file."""
        main_text = expand_calligraphic((self.tex_root / MAIN).read_text(encoding="utf-8"))
        preamble = main_text.split("\\begin{document}")[0]
        macros = parse_macros(preamble)
        # MATH_OVERRIDES win over preamble definitions
        macros.update(MATH_OVERRIDES)
        return macros

    def mathjax_macros(self) -> dict:
        """MathJax macro configuration dict for the page template."""
        out = {}
        for name, (n, default, body) in self.macros.items():
            body = mathjax_compat(body)
            if "\\begin{comment}" in body or "\\end{comment}" in body:
                continue
            if "@" in name or "@" in body:
                continue
            if n == 0:
                out[name] = body
            elif default is None:
                out[name] = [body, n]
            else:
                out[name] = [body, n, default]
        return out

    # inventory ---------------------------------------------------------------
    def inventory_at(self, file: str, line: int, kinds: tuple):
        base = file.rsplit("/", 1)[-1]
        allowed_kinds = set(kinds)
        if "heading" in allowed_kinds:
            allowed_kinds.update(["section", "subsection", "subsubsection"])
        cands = [e for key in [(file, line), (base, line), ("SteinIntro.tex", line), ("SteinIntro_utf8.tex", line)]
                 for e in self.by_pos.get(key, []) if e["kind"] in allowed_kinds]
        if not cands:
            return None
        key = (file, line, kinds)
        k = self.used_pos.get(key, 0)
        self.used_pos[key] = k + 1
        return cands[k] if k < len(cands) else cands[-1]

    def label_number(self, label: str):
        owner = self.label_owner.get(label)
        if not owner:
            return None, None
        if owner["kind"] == "display":
            for row in owner.get("rows", []):
                if label in row.get("labels", []):
                    return row.get("number"), "equation"
            return owner.get("number"), "equation"
        return owner.get("number"), owner["kind"]

    def env_title(self, kind: str) -> str:
        return ENV_NAMES.get(kind, kind.capitalize())

    # includes, figures, citations ---------------------------------------------
    def include(self, path: str) -> list:
        path = path if path.endswith(".tex") else path + ".tex"
        target = self.tex_root / path
        if not target.is_file():
            self.warn(f"missing include {path}")
            return []
        conv = FileConverter(self, self.rel(target), expand_calligraphic(target.read_text(encoding="utf-8")))
        return conv.convert()

    def image(self, path: str) -> str:
        """Locate and copy a figure file, returning an <img> tag.

        The paper has very few figures; we degrade gracefully if any are absent.
        """
        src = None
        for cand in (path, path + ".png", path + ".pdf", path + ".jpg"):
            if (self.tex_root / cand).is_file():
                src = self.tex_root / cand
                break
        if src is None:
            self.warn(f"figure file not found: {path}")
            return f'<span class="missing-figure">Figure <code>{esc(path)}</code> not found.</span>'
        magic = src.read_bytes()[:4]
        kind = ("png" if magic == b"\x89PNG" else "jpg" if magic[:2] == b"\xff\xd8"
                else "pdf" if magic == b"%PDF" else src.suffix.lower().lstrip("."))
        name = src.stem + (".jpg" if kind == "jpg" else ".png")
        dest = self.out / "figures" / name
        if name not in self.images:
            dest.parent.mkdir(parents=True, exist_ok=True)
            if kind == "pdf":
                if shutil.which("pdftoppm"):
                    cmd = ["pdftoppm", "-png", "-r", "216", "-singlefile", str(src), str(dest.with_suffix(""))]
                elif shutil.which("sips"):
                    cmd = ["sips", "-s", "format", "png", "-s", "dpiWidth", "216", "-s", "dpiHeight", "216",
                           str(src), "--out", str(dest)]
                else:
                    cmd = None
                r = subprocess.run(cmd, capture_output=True, text=True) if cmd else None
                if r is None or r.returncode != 0 or not dest.exists():
                    why = (r.stderr or r.stdout).strip().splitlines()[-1:] if r else ["no converter found"]
                    self.warn(f"could not convert {src.name} to PNG: {' '.join(why) or 'no output file'}")
                    return f'<span class="missing-figure">Figure <code>{esc(path)}</code> could not be converted.</span>'
            else:
                shutil.copyfile(src, dest)
            self.images[name] = src.name
        return f'<img src="figures/{attr(name)}" alt="Figure ({attr(src.name)})" loading="lazy">'

    def load_bib(self) -> dict:
        """Parse the .bbl file produced by BibTeX.

        Extracts author and publication year from BibTeX-formatted .bbl entries:
        author is parsed from the text before \\newblock, and year from the
        publication entry.
        """
        bbl_path = self.tex_root / "SteinIntro.bbl"
        if not bbl_path.is_file():
            bbl_path = Path("source/upstream/tex/SteinIntro.bbl")
        if not bbl_path.is_file():
            self.warn("SteinIntro.bbl not found; citations will be unresolved")
            return {}
        text = bbl_path.read_text(encoding="utf-8")
        out: dict = {}
        for m in re.finditer(r"\\bibitem(?:\[([^\]]*)\])?\{([^}]+)\}", text):
            opt, key = m.group(1) or "", m.group(2).strip()
            start = m.end()
            nxt = text.find("\\bibitem", start)
            body = text[start:nxt if nxt >= 0 else len(text)]

            # 1. Year: look for 4-digit publication year e.g. ", 1989." or "\url{...}, 2010."
            ym = re.search(r",\s*(1[89]\d\d|20\d\d)[.,]", body)
            if not ym:
                all_y = re.findall(r"\b(1[89]\d\d|20\d\d)\b", body)
                year = all_y[-1] if all_y else ""
            else:
                year = ym.group(1)

            # 2. Author: text between \bibitem and \newblock (or first line)
            nb = body.find("\\newblock")
            raw_auth = body[:nb].strip() if nb != -1 else body.strip().split("\n")[0]
            raw = raw_auth.strip().rstrip(".")
            raw = re.sub(r",\s*editors?\.?", "", raw, flags=re.IGNORECASE)
            raw = re.sub(r",\s*and\s+", " and ", raw)
            parts = re.split(r",\s*|\s+and\s+", raw)
            parts = [p.strip() for p in parts if p.strip()]
            lasts = []
            for p in parts:
                clean = self.detex(p)
                tokens = clean.split()
                if tokens:
                    lasts.append(tokens[-1])
            if not lasts:
                who = key
            elif len(lasts) == 1:
                who = lasts[0]
            elif len(lasts) == 2:
                who = f"{lasts[0]} and {lasts[1]}"
            else:
                who = f"{lasts[0]} et al."

            out[key] = {
                "author": who,
                "year": year,
                "raw_author": raw_auth,
                "body": body,
            }
        return out

    @staticmethod
    def detex(text: str) -> str:
        text = re.sub(r"\\[`'^\"~=.uvHckr]\s*\{?\\?([A-Za-z])\}?", r"\1", text)
        text = re.sub(r"\\&", "&", text)
        text = re.sub(r"\\[A-Za-z]+\s*", "", text)
        text = text.replace("{", "").replace("}", "").replace("~", " ").replace("--", "–")
        return re.sub(r"\s+", " ", text).strip()

    def authors(self, key: str):
        e = self.bib.get(key)
        if not e:
            return key, ""
        return e.get("author", key), e.get("year", "")

    def cite(self, cmd: str, keys: list, opts: list) -> str:
        items = []
        for k in keys:
            self.cited[k] = True
            who, year = self.authors(k)
            link = f'<a class="cite" href="references.html#ref-{attr(k)}">'
            if cmd.startswith("citet") or cmd == "citeauthor":
                txt = who if cmd == "citeauthor" else (f"{esc(who)} ({esc(year)})" if year else esc(who))
            elif cmd == "citeyear":
                txt = esc(year)
            else:
                txt = f"{esc(who)}, {esc(year)}" if year else esc(who)
            items.append(f"{link}{txt}</a>")
        pre = post = ""
        if len(opts) == 1:
            post = opts[0]
        elif len(opts) == 2:
            pre, post = opts
        body = "; ".join(items)
        if cmd.startswith("citet") or cmd in ("citeauthor", "citeyear"):
            return body + (f" ({post})" if post else "")
        inner = (f"{pre} " if pre else "") + body + (f", {post}" if post else "")
        return inner if cmd == "citealp" else f"({inner})"

    def cite_plain(self, keys: str) -> str:
        out = []
        for k in [k.strip() for k in keys.split(",") if k.strip()]:
            self.cited[k] = True
            who, year = self.authors(k)
            out.append(f"{who}, {year}" if year else who)
        return "(" + "; ".join(out) + ")"

    def next_footnote(self) -> int:
        self.footnotes += 1
        return self.footnotes

    def warn(self, msg: str):
        self.warnings.append(msg)

    # sections and pages -------------------------------------------------------
    def convert_all(self):
        """Convert the paper body, returning (front_blocks, section_block_lists, back_blocks).

        The paper is a single file; we process it as one chunk and split on
        section headings when paginating.
        """
        main_path = self.tex_root / MAIN
        raw = expand_calligraphic(main_path.read_text(encoding="utf-8"))
        # Split at \begin{document}
        doc_match = re.search(r"\\begin\{document\}", mask_comments(raw))
        if doc_match:
            body_raw = raw[doc_match.end():]
            body_masked = mask_comments(raw)[doc_match.end():]
        else:
            body_raw = raw
            body_masked = mask_comments(raw)

        rel_path = self.rel(main_path)
        conv = FileConverter(self, rel_path, raw)
        all_parts = conv.convert()
        all_blocks = assemble(all_parts)

        # Assign line ranges and file to all paragraph blocks
        from bisect import bisect_right
        newlines = [m.start() for m in re.finditer("\n", raw)]
        def get_line(pos: int) -> int:
            return bisect_right(newlines, pos - 1) + 1

        for i, b in enumerate(all_blocks):
            if b.kind == "p" and b.line_start is None:
                prev_line = 1
                for prev in reversed(all_blocks[:i]):
                    if prev.line_end is not None:
                        prev_line = prev.line_end
                        break
                next_line = len(newlines)
                for nxt in all_blocks[i+1:]:
                    if nxt.line_start is not None:
                        next_line = nxt.line_start
                        break

                clean = re.sub(r"<[^>]+>", " ", b.html)
                clean = re.sub(r"@@REF\|[^@]+@@", " ", clean)
                clean = re.sub(r"\s+", " ", clean).strip()
                words = [w for w in clean.split() if len(w) >= 3 and not w.startswith("&") and not w.startswith("\\")]

                search_start = newlines[prev_line - 1] if prev_line > 1 else 0
                search_end = newlines[next_line - 1] if next_line < len(newlines) else len(raw)
                window = raw[search_start:search_end]

                found_offset = -1
                for nwords in (3, 2, 1):
                    for w_idx in range(len(words) - nwords + 1):
                        pat = r"\s+".join(re.escape(w) for w in words[w_idx:w_idx+nwords])
                        m = re.search(pat, window)
                        if m:
                            found_offset = m.start()
                            break
                    if found_offset != -1:
                        break

                if found_offset != -1:
                    b.line_start = get_line(search_start + found_offset)
                    end_m = re.search(r"\n\s*\n|\\(?:begin|section|subsection|subsubsection|ba|ban|be|ben)\b", window[found_offset:])
                    b.line_end = get_line(search_start + found_offset + end_m.start()) if end_m else get_line(search_start + len(window))
                else:
                    b.line_start = prev_line
                    b.line_end = next_line
                b.file = "SteinIntro.tex"
        # Separate abstract/front matter heuristically: everything before the
        # first section heading goes into front.
        front, body, back = [], [], []
        in_body = False
        for b in all_blocks:
            if b.kind == "heading" and b.level == 1 and not in_body:
                in_body = True
            if not in_body:
                front.append(b)
            else:
                body.append(b)
        # The index page shows only the abstract: drop the preamble (document class,
        # geometry, theorem and macro definitions) and the title/author block.
        masked = mask_comments(raw)
        a0 = re.search(r"\\begin\{abstract\}", masked)
        a1 = re.search(r"\\end\{abstract\}", masked)
        if a0 and a1:
            # Preamble blocks get unreliable line numbers, so match on text instead.
            words = lambda s: re.sub(r"\s+", " ", re.sub(r"<[^>]+>|\\[A-Za-z]+|[{}]", " ", s)).strip()
            abstract = words(raw[a0.end():a1.start()])
            front = [b for b in front
                     if (t := words(getattr(b, "html", "")))[:40] and t[:40] in abstract]
        return front, [body], back  # wrap body in a list to match RL API

    def paginate(self, sections: list) -> list:
        """Split block lists into Pages, with \\section as top-level (level=1).

        A \\section heading creates a new Page at level 1.
        A \\subsection heading creates a new Page at level 2 nested under the
        current level-1 page.
        Everything before the first \\section goes onto a 'front-N' page.
        """
        pages: list = []
        for blocks in sections:
            cur: Page | None = None
            sec_no: str | None = None
            for b in blocks:
                if b.kind == "heading" and b.level is not None and b.level <= 2:
                    if b.level == 1:
                        # Top-level section (level 0 page)
                        sec_no = b.number
                        pid = f"sec{b.number.replace('.', '-')}" if b.number else f"sec-{len(pages)}"
                        level = 0
                    else:
                        # Subsection: nested under current section (level 1 page)
                        pid = f"sec{b.number.replace('.', '-')}" if b.number else \
                              (f"{pages[-1].id}-s{len(pages)}" if pages else f"sec-s{len(pages)}")
                        level = 1
                    cur = Page(pid, b.title, b.number, sec_no, level)
                    pages.append(cur)
                if cur is None:
                    cur = Page(f"front-{len(pages)}", "Front matter", None, None, 0)
                    pages.append(cur)
                cur.blocks.append(b)
        return pages
