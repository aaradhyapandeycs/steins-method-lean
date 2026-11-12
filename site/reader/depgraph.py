"""Dependency-graph data for the reader: nodes are the paper's 122 numbered environments, edges are
the TeX cross-references (`\\ref`, `\\eqref`, `\\eq`) inside a result and its proof, filtered by the
reviewed decisions in `docs/graph/edge-review.json`.

A reference inside result B (or B's proof) to a label owned by result A is a *candidate* edge A -> B.
A label is owned by the numbered environment whose line range contains it, or by the result whose proof
contains it. Labels of sections and of displays in running prose own no node; references to them are
counted as context. Each candidate carries a review decision: `dependency` (drawn), `context`
(a comparison, definition or "see also" reference: listed, not drawn) or `drop` (not a reference to that
result, for example a proof header "Proof of Theorem X" or a reference to a later result as an example).
Candidates without a decision are drawn and counted as unreviewed, so new edges never disappear silently.
"""

from __future__ import annotations

import json
import re
from bisect import bisect_right
from pathlib import Path

from .tex import mask_comments

REF_RE = re.compile(r"\\(?:ref|eqref|eq)\s*\{([^}]+)\}")
LABEL_RE = re.compile(r"\\label\s*\{([^}]+)\}")
PROOF_RE = re.compile(r"\\begin\{proof\}(\[[^\]]*\])?(.*?)\\end\{proof\}", re.S)
PROVABLE = {"theorem", "lemma", "proposition", "corollary", "example", "remark"}
KIND_SHORT = {"theorem": "Thm", "lemma": "Lem", "proposition": "Prop", "corollary": "Cor",
              "example": "Ex", "remark": "Rem", "definition": "Def"}
REVIEW_PATH = "docs/graph/edge-review.json"


class DepGraph:
    def __init__(self, tex: str, items: list[dict], review: dict | None = None):
        self.tex = tex
        self.masked = mask_comments(tex)
        self.nl = [m.start() for m in re.finditer("\n", tex)]
        self.items = [i for i in items if not i.get("is_prose")]
        self.by_id = {i["id"]: i for i in self.items}
        self.review = review or {}
        self._build()

    def line(self, pos: int) -> int:
        return bisect_right(self.nl, pos - 1) + 1

    def text_line(self, ln: int) -> str:
        a = self.nl[ln - 2] + 1 if ln >= 2 else 0
        b = self.nl[ln - 1] if ln - 1 < len(self.nl) else len(self.tex)
        return self.tex[a:b].strip()

    def env_at(self, ln: int):
        """Innermost numbered environment containing line ln (environments nest: a theorem inside an
        example, a remark inside an example)."""
        hits = [i for i in self.items if i["line_start"] <= ln <= i["line_end"]]
        return min(hits, key=lambda i: i["line_end"] - i["line_start"]) if hits else None

    def scope_owner(self, ln: int):
        """Innermost result whose statement or owned proof contains line ln."""
        best, size = None, None
        for nid, ranges in self.scopes.items():
            for a, b in ranges:
                if a <= ln <= b and (size is None or b - a < size):
                    best, size = nid, b - a
        return best

    def _build(self):
        # scopes: env range plus owned proofs
        scopes = {i["id"]: [(i["line_start"], i["line_end"])] for i in self.items}
        labels_in_env = {}
        for m in LABEL_RE.finditer(self.masked):
            env = self.env_at(self.line(m.start()))
            if env:
                labels_in_env[m.group(1).strip()] = env["id"]
        self.proofs = []
        ordered = sorted(self.items, key=lambda i: i["line_start"])
        found = list(PROOF_RE.finditer(self.masked))
        # proofs whose header names their result ("Proof of Theorem \ref{X}")
        named = {}
        for m in found:
            for r in REF_RE.findall(m.group(1) or ""):
                if r.strip() in labels_in_env:
                    named[m.start()] = labels_in_env[r.strip()]
                    break
        has_proof = set(named.values())
        for m in found:
            ps, pe = self.line(m.start()), self.line(m.end())
            hdr = m.group(1) or ""
            owner = named.get(m.start())
            if owner is None:
                # Unlabeled proof: the nearest preceding theorem-like result still without a proof
                # (a remark may sit between a theorem and its proof, as with Theorem 5.7), else the
                # environment immediately before it (a remark or example with its own proof).
                prev = [i for i in ordered if i["line_end"] <= ps]
                thm = [i for i in prev if i["kind"] in ("theorem", "lemma", "proposition", "corollary")
                       and i["id"] not in has_proof]
                if thm and not any(p["kind"] in ("theorem", "lemma", "proposition", "corollary")
                                   for p in prev if p["line_start"] > thm[-1]["line_end"]):
                    owner = thm[-1]["id"]
                elif prev and prev[-1]["kind"] in PROVABLE:
                    owner = prev[-1]["id"]
                if owner:
                    has_proof.add(owner)
            if owner:
                scopes[owner].append((ps, pe))
                self.proofs.append((owner, ps, pe, m.start() + len("\\begin{proof}") + len(hdr)))
        self.scopes = scopes
        # label -> owning node: inside an environment, or inside an owned proof
        self.label_owner = dict(labels_in_env)
        for m in LABEL_RE.finditer(self.masked):
            lab = m.group(1).strip()
            if lab in self.label_owner:
                continue
            ln = self.line(m.start())
            for owner, ps, pe, _ in self.proofs:
                if ps <= ln <= pe:
                    self.label_owner[lab] = owner
                    break
        # candidate edges
        cands = {}
        self.context_refs = {i["id"]: 0 for i in self.items}
        for nid, ranges in scopes.items():
            for a, b in ranges:
                lo = self.nl[a - 2] + 1 if a >= 2 else 0
                hi = self.nl[b - 1] if b - 1 < len(self.nl) else len(self.masked)
                for m in REF_RE.finditer(self.masked, lo, hi):
                    # skip the "Proof of Theorem \ref{X}" header itself
                    if any(ps == self.line(m.start()) and m.start() < body
                           for o, ps, pe, body in self.proofs if o == nid):
                        continue
                    # a reference belongs only to the innermost result containing it
                    if self.scope_owner(self.line(m.start())) != nid:
                        continue
                    for lab in m.group(1).split(","):
                        lab = lab.strip()
                        src = self.label_owner.get(lab)
                        if src is None:
                            self.context_refs[nid] += 1
                            continue
                        if src == nid:
                            continue
                        ln = self.line(m.start())
                        key = f"{src}->{nid}"
                        c = cands.setdefault(key, {"from": src, "to": nid, "labels": [], "lines": []})
                        if lab not in c["labels"]:
                            c["labels"].append(lab)
                        if ln not in c["lines"]:
                            c["lines"].append(ln)
        for c in cands.values():
            c["decision"] = self.review.get(f'{c["from"]}->{c["to"]}', {}).get("decision", "unreviewed")
            c["why"] = self.review.get(f'{c["from"]}->{c["to"]}', {}).get("why", "")
        self.candidates = sorted(cands.values(), key=lambda c: (self.by_id[c["to"]]["line_start"],
                                                                self.by_id[c["from"]]["line_start"]))

    # ------------------------------------------------------------------
    def drawn(self) -> list[dict]:
        return [c for c in self.candidates if c["decision"] in ("dependency", "unreviewed")]

    def uses(self, nid: str, kinds=("dependency", "unreviewed")) -> list[str]:
        return [c["from"] for c in self.candidates if c["to"] == nid and c["decision"] in kinds]

    def summary(self) -> dict:
        from collections import Counter
        cnt = Counter(c["decision"] for c in self.candidates)
        return {"nodes": len(self.items), "candidates": len(self.candidates),
                "dependency": cnt["dependency"], "context": cnt["context"], "drop": cnt["drop"],
                "unreviewed": cnt["unreviewed"]}

    @staticmethod
    def short_name(i: dict) -> str:
        return f'{KIND_SHORT.get(i["kind"], i["kind"][:4].capitalize())} {i["number"]}'

    def review_sheet(self) -> str:
        """Plain-text sheet of every candidate with its source lines, for the edge review."""
        out = []
        for c in self.candidates:
            a, b = self.by_id[c["from"]], self.by_id[c["to"]]
            out.append(f'== {c["from"]}->{c["to"]}  [{self.short_name(a)} -> {self.short_name(b)}]  '
                       f'labels={",".join(c["labels"])}  decision={c["decision"]}')
            for ln in c["lines"][:4]:
                where = "statement" if b["line_start"] <= ln <= b["line_end"] else "proof"
                out.append(f'   L{ln} ({where}): {self.text_line(ln)[:200]}')
        return "\n".join(out)


def load_review(root: Path) -> dict:
    p = root / REVIEW_PATH
    if not p.is_file():
        return {}
    data = json.loads(p.read_text(encoding="utf-8"))
    return {k: v for k, v in data.get("edges", {}).items()}


# ----------------------------------------------------------------------
# page

import html as _html

from .lean import STATUS_LABELS, chip
from .tex import html_id

LEGEND_ORDER = ["proved", "corrected", "restricted", "defined", "source-issue", "open"]
LEGEND_WORDS = {"proved": "proved as stated", "corrected": "proved with corrections",
                "restricted": "proved under restrictions", "defined": "definition formalized",
                "source-issue": "source issue", "open": "open"}


def _esc(t) -> str:
    return _html.escape(str(t), quote=False)


def _attr(t) -> str:
    return _html.escape(str(t), quote=True)


class GraphPage:
    def __init__(self, site, graph: DepGraph, ldeps=None):
        self.site = site
        self.g = graph
        self.ld = ldeps
        self.lean_edges = ldeps.item_edges() if ldeps else []
        # Current iff the recorded tree hashes of the Lean sources match this revision's (commit ids differ
        # between the development repository and the public mirror; trees do not).
        self.current = False
        self.stale = ""
        rec = (ldeps.data.get("lean_sources") if ldeps else None) or {}
        if rec:
            git = site.lean.git
            now = git.run("rev-parse", f"{git.rev}:Formalization", f"{git.rev}:Formalization.lean").split()
            self.current = now == [rec.get("Formalization"), rec.get("Formalization.lean")]
        if ldeps and ldeps.entries and not self.current:
            self.stale = ('<div class="incomplete" role="note"><strong>Proof relations may be stale.</strong> '
                          'They were extracted from Lean sources that differ from this commit; rerun '
                          '<code>scripts/lean_deps/extract.py</code>.</div>')

    def status(self, i: dict) -> str:
        return i["status"] if i["status"] in STATUS_LABELS else "open"

    def long_name(self, i: dict) -> str:
        return i.get("source") or DepGraph.short_name(i)

    def sections(self) -> list:
        return sorted({i["section"] for i in self.g.items}, key=lambda s: int(s) if str(s).isdigit() else 99)

    def svg(self) -> str:
        cols = {}
        for i in sorted(self.g.items, key=lambda x: x["line_start"]):
            cols.setdefault(i["section"], []).append(i)
        secs = self.sections()
        W, H, GX, GY, TOP, LEFT = 112, 22, 84, 8, 46, 12
        pos = {}
        for ci, s in enumerate(secs):
            for ri, i in enumerate(cols[s]):
                pos[i["id"]] = (LEFT + ci * (W + GX), TOP + ri * (H + GY))
        width = LEFT * 2 + len(secs) * (W + GX) - GX
        height = TOP + max(len(v) for v in cols.values()) * (H + GY) + 10
        out = [f'<svg class="depgraph" xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
               f'viewBox="0 0 {width} {height}" data-w="{width}" data-h-all="{height}" data-h-named="{height}" '
               f'role="group" aria-labelledby="gtitle">'
               '<title id="gtitle">Dependency graph of the paper\'s numbered results, one column per section</title>'
               '<defs><marker id="arrow" viewBox="0 0 8 8" refX="7" refY="4" markerWidth="6" markerHeight="6" '
               'orient="auto-start-reverse"><path d="M0,0 L8,4 L0,8 z" class="gn-arrow"/></marker>'
               f'<clipPath id="nclip"><rect x="0" y="0" width="{W - 8}" height="{H}"/></clipPath></defs>']
        for ci, s in enumerate(secs):
            out.append(f'<text x="{LEFT + ci * (W + GX)}" y="22" class="gn-col" data-ch="{_attr(s)}">'
                       f'Section {_esc(s)}</text>')

        def path(p1, p2):
            (x1, y1), (x2, y2) = p1, p2
            y1c, y2c = y1 + H / 2, y2 + H / 2
            if x1 == x2:
                bend = W + 18 + min(60, abs(y2 - y1) / 8)
                return f"M{x1 + W},{y1c} C{x1 + bend},{y1c} {x2 + bend},{y2c} {x2 + W},{y2c}"
            if x1 < x2:
                return f"M{x1 + W},{y1c} C{x1 + W + GX / 2},{y1c} {x2 - GX / 2},{y2c} {x2},{y2c}"
            return f"M{x1},{y1c} C{x1 - GX / 2},{y1c} {x2 + W + GX / 2},{y2c} {x2 + W},{y2c}"

        # e-named: curated paper dependencies (default view); e-all: relations extracted from Lean
        for c in self.g.drawn():
            out.append(f'<path d="{path(pos[c["from"]], pos[c["to"]])}" class="gn-edge e-named" '
                       f'data-from="{_attr(html_id(c["from"]))}" data-to="{_attr(html_id(c["to"]))}" '
                       f'marker-end="url(#arrow)"/>')
        for a, b in self.lean_edges:
            out.append(f'<path d="{path(pos[a], pos[b])}" class="gn-edge e-all" '
                       f'data-from="{_attr(html_id(a))}" data-to="{_attr(html_id(b))}" marker-end="url(#arrow)"/>')
        lean_uses = {}
        for a, b in self.lean_edges:
            lean_uses.setdefault(b, []).append(a)
        for i in self.g.items:
            x, y = pos[i["id"]]
            st = self.status(i)
            uses = " ".join(html_id(u) for u in self.g.uses(i["id"]))
            luses = " ".join(html_id(u) for u in lean_uses.get(i["id"], []))
            text = DepGraph.short_name(i)
            title = f'{self.long_name(i)}{" (" + i["labels"][0] + ")" if i["labels"] else ""}: {LEGEND_WORDS[st]}'
            node = (f'<g class="gn gl-{st} named" data-id="{_attr(html_id(i["id"]))}" data-ch="{_attr(i["section"])}" '
                    f'data-named="1" data-uses="{_attr(luses)}" data-nuses="{_attr(uses)}" '
                    f'data-xy="{x},{y}" data-nxy="{x},{y}" transform="translate({x},{y})">'
                    f'<title>{_esc(title)}</title><rect x="0" y="0" width="{W}" height="{H}" rx="4"/>'
                    f'<text x="{W / 2}" y="15" clip-path="url(#nclip)">{_esc(text)}</text></g>')
            out.append(f'<a href="#n-{_attr(html_id(i["id"]))}" aria-label="{_attr(self.long_name(i))}">{node}</a>')
        out.append("</svg>")
        return "".join(out)

    def nodes_json(self) -> str:
        nodes = []
        for i in sorted(self.g.items, key=lambda x: x["line_start"]):
            nodes.append({
                "id": i["id"], "name": self.long_name(i), "kind": i["kind"], "number": i["number"],
                "section": i["section"], "labels": i["labels"],
                "tex": {"file": "SteinIntro.tex", "line_start": i["line_start"], "line_end": i["line_end"]},
                "status": self.status(i), "lean": i.get("lean_names", []),
                "uses": [{"id": c["from"], "decision": c["decision"], "labels": c["labels"], "lines": c["lines"]}
                         for c in self.g.candidates if c["to"] == i["id"]],
            })
        return json.dumps({"summary": self.g.summary(), "nodes": nodes}, indent=1, ensure_ascii=False) + "\n"

    def dot(self) -> str:
        fill = {"proved": "palegreen", "corrected": "khaki", "restricted": "thistle", "defined": "lightblue",
                "source-issue": "mistyrose", "open": "white"}
        lines = ["// Generated by site/build.py from the reviewed dependency edges; render with: dot -Tsvg graph.dot",
                 "digraph results {", "  rankdir=LR; node [shape=box, style=filled, fontsize=10];"]
        for i in self.g.items:
            lines.append(f'  "{i["id"]}" [label="{self.long_name(i)}", fillcolor={fill[self.status(i)]}];')
        for c in self.g.drawn():
            lines.append(f'  "{c["from"]}" -> "{c["to"]}";')
        lines.append("}")
        return "\n".join(lines) + "\n"

    def page(self) -> str:
        site = self.site
        s = self.g.summary()
        legend = "".join(
            f'<li><svg width="46" height="20" aria-hidden="true"><g class="gn gl-{k}">'
            f'<rect x="2" y="2" width="42" height="16" rx="3"/></g></svg> {_esc(LEGEND_WORDS[k])}</li>'
            for k in LEGEND_ORDER)
        trs, last = [], None
        for i in sorted(self.g.items, key=lambda x: (int(x["section"]) if str(x["section"]).isdigit() else 99,
                                                      x["line_start"])):
            if i["section"] != last:
                last = i["section"]
                trs.append(f'<tr class="ch-row" data-ch="{_attr(last)}"><th colspan="4">Section {_esc(last)} '
                           f'{_esc(_html.unescape(re.sub("<[^>]+>", "", site.section_titles.get(last, ""))))}</th></tr>')
            link = site.item_href(i)
            name = _esc(self.long_name(i))
            name = f'<a href="{_attr(link)}">{name}</a>' if link else name
            lab = f'<div class="label"><code>{_esc(i["labels"][0])}</code></div>' if i["labels"] else ""
            tex = f'<div class="label"><code>SteinIntro.tex:{i["line_start"]}–{i["line_end"]}</code></div>'
            cites = [c for c in self.g.candidates if c["to"] == i["id"]]

            def ref(c):
                a = self.g.by_id[c["from"]]
                return f'<a href="#n-{_attr(html_id(a["id"]))}">{_esc(self.long_name(a))}</a>'
            dep = ", ".join(ref(c) for c in cites if c["decision"] in ("dependency", "unreviewed"))
            ctx = [c for c in cites if c["decision"] == "context"]
            if ctx:
                dep += ('<div class="label">context: ' + ", ".join(
                    f'<span title="{_attr(c["why"])}">{_esc(self.long_name(self.g.by_id[c["from"]]))}</span>'
                    for c in ctx) + "</div>")
            lean = " ".join(f'<code>{_esc(n)}</code>' for n in i.get("lean_names", [])[:6])
            st = self.status(i)
            search = " ".join([self.long_name(i), " ".join(i["labels"]), " ".join(i.get("lean_names", []))]).lower()
            trs.append(f'<tr id="n-{_attr(html_id(i["id"]))}" data-label="{_attr(st)}" data-markers="" '
                       f'data-ch="{_attr(i["section"])}" data-named="1" data-search="{_attr(search)}">'
                       f'<td data-th="Item">{name}{lab}{tex}</td>'
                       f'<td data-th="Status">{chip(st, markers=i.get("markers", []))}</td>'
                       f'<td data-th="Lean" class="lean-names">{lean or "—"}</td>'
                       f'<td data-th="Uses">{dep or "—"}</td></tr>')
        secs = "".join(f'<option value="{_attr(x)}">Section {_esc(x)}</option>' for x in self.sections())
        chips = "".join(
            f'<button type="button" class="chip" data-filter="{k}" aria-pressed="false">'
            f'<span class="status {STATUS_LABELS[k][1]}">{_esc(STATUS_LABELS[k][0])}</span></button>'
            for k in LEGEND_ORDER)
        unrev = (f" {s['unreviewed']} edges are not yet reviewed and are drawn." if s["unreviewed"] else "")
        body = f"""<h1>Dependency graph</h1>
<div class="incomplete" role="note"><strong>AI-reviewed edges.</strong> Arrows are read from the TeX
cross-references (<code>\\ref</code>, <code>\\eqref</code>, <code>\\eq</code>) inside each numbered result and its
proof. Of the {s['candidates']} references between results, an AI critic classified {s['dependency']} as proof
dependencies (drawn) and {s['context']} as notation, comparison or interpretation (listed as context, not drawn);
the decisions are in <code>docs/graph/edge-review.json</code> and were not reviewed by the author.{unrev}
A real dependency may be used without a reference, so missing arrows are possible. The graph does not certify a
section or the paper.</div>
<p class="lede">Two kinds of edges, never mixed. <strong>Paper dependencies</strong> (default) are the curated
edges above. <strong>Proof relations</strong> are extracted mechanically from the compiled Lean proofs
({"of this commit's Lean sources" if self.current else "of an earlier version of the Lean sources"}; {len(self.lean_edges)} edges): result A points to
result B when B's Lean proof transitively uses a library theorem that A's statement entry applies and that no other
statement entry applies (a theorem applied by several entries is a shared tool and creates no edge). A proof
relation describes the formal proofs, not the paper's argument.</p>
<p class="lede">One node per numbered result ({s['nodes']}). The fill is the item's status; arrows point from a cited
result to the result that uses it. Click a node to highlight what it uses (transitively) and what uses it; click it
again to go to its row. <a href="status.html">Progress</a> · <a href="graph/nodes.json">nodes.json</a> ·
<a href="graph/graph.dot">graph.dot</a> (Graphviz).</p>
{self.stale}<ul class="glegend">{legend}</ul>
<div class="graph-controls" role="group" aria-label="Graph controls">
<select id="g-edges" aria-label="Edges"><option value="curated">Paper dependencies (curated)</option>
<option value="lean">Proof relations (extracted from Lean)</option></select>
<select id="g-ch" aria-label="Section"><option value="">All sections</option>{secs}</select>
<button type="button" class="chip" id="g-zoom-out" aria-label="Zoom out">−</button>
<button type="button" class="chip" id="g-zoom-in" aria-label="Zoom in">+</button>
<button type="button" class="chip" id="g-clear">Clear highlight</button>
<span id="g-info" class="g-info" aria-live="polite"></span></div>
<p class="scroll-hint">Scroll the graph sideways to see every section →</p>
<div class="graph-wrap">{self.svg()}</div>
<h2>All nodes</h2>
<div class="filters"><input type="search" id="q" placeholder="Search number, label or Lean name" aria-label="Search nodes">
<div class="chips"><button type="button" class="chip on" data-filter="" aria-pressed="true">All</button>{chips}</div>
<p class="filter-count" aria-live="polite"></p></div>
<div class="table-wrap"><table class="results stack graph-table"><thead><tr><th>Item</th><th>Status</th>
<th>Lean entries</th><th>Uses</th></tr></thead>
<tbody>{''.join(trs)}</tbody></table></div>"""
        return site.shell("Dependency graph · Fundamentals of Stein's method", body, "graph", toc=False)


# ----------------------------------------------------------------------
# Lean-extracted relations (docs/graph/lean-deps.json, written by scripts/lean_deps/ExtractDeps.lean)

LEAN_DEPS_PATH = "docs/graph/lean-deps.json"


def short(n: str) -> str:
    return n.split(".", 1)[1] if n.startswith("SteinMethod.") else n


class LeanDeps:
    """Entry-level and item-level relations extracted from the compiled proofs."""

    def __init__(self, data: dict | None, items: list[dict]):
        self.data = data or {}
        self.rev = self.data.get("extracted_at", "")
        self.entries = {short(e["entry"]): e for e in self.data.get("entries", [])}
        self.item_of = {}
        for i in items:
            if i.get("is_prose"):
                continue
            for n in i.get("lean_names", []):
                self.item_of.setdefault(n, i["id"])
        # A library theorem that is the root of several entries is a shared tool (for example the
        # generic Wasserstein bound behind Theorems 3.1-3.7); reaching it says nothing about one result
        # using another. Keep A -> B only through a root owned by A alone that B does not apply itself.
        root_count = {}
        for rec in self.entries.values():
            for r in rec.get("roots", []):
                root_count[r] = root_count.get(r, 0) + 1
        self.uses = {}
        for e, rec in self.entries.items():
            own_roots = set(rec.get("roots", []))
            kept = []
            for u in rec["uses"]:
                via = [v for v in u["via"] if root_count.get(v, 0) == 1 and v not in own_roots]
                if via:
                    kept.append((short(u["entry"]), [short(v) for v in via]))
            self.uses[e] = kept
        self.used_by = {}
        for e, us in self.uses.items():
            for a, via in us:
                self.used_by.setdefault(a, []).append((e, via))

    def roots(self, entry: str) -> list[str]:
        return [short(r) for r in self.entries.get(entry, {}).get("roots", [])]

    def item_edges(self) -> list[tuple[str, str]]:
        """Item-level edges A -> B: some entry of B uses some entry of A (A != B)."""
        out = set()
        for e, us in self.uses.items():
            b = self.item_of.get(e)
            for a_entry, _ in us:
                a = self.item_of.get(a_entry)
                if a and b and a != b:
                    out.add((a, b))
        return sorted(out)


def connections_html(entry: str, graph: DepGraph, ldeps: LeanDeps, lib_decls: dict, blob) -> str:
    """The 'Connections' block of a theorem card: curated paper dependencies (reviewed TeX references),
    Lean-extracted proof relations, and links to the library proofs. Links are placeholders resolved
    after all pages are rendered: @@ITEM|id|text@@ and @@LEAN|name@@."""
    rows = []
    item = ldeps.item_of.get(entry)
    if item:
        def items(ids):
            return ", ".join(f'@@ITEM|{x}|{_esc(DepGraph.short_name(graph.by_id[x]))}@@' for x in ids)
        up = graph.uses(item, kinds=("dependency",))
        down = [c["to"] for c in graph.candidates if c["from"] == item and c["decision"] == "dependency"]
        rows.append(f'<dt>Uses (paper)</dt><dd>{items(up) or "—"}</dd>')
        rows.append(f'<dt>Used by (paper)</dt><dd>{items(down) or "—"}</dd>')
    lu = ldeps.uses.get(entry, [])
    lb = ldeps.used_by.get(entry, [])

    def entries(pairs):
        return ", ".join(f'<span title="{_attr("shared: " + ", ".join(via))}">@@LEAN|{a}@@</span>'
                         for a, via in sorted(pairs)[:12]) + (f" and {len(pairs) - 12} more" if len(pairs) > 12 else "")
    if entry in ldeps.entries:
        rows.append(f'<dt>Proof uses (Lean)</dt><dd>{entries(lu) or "—"}</dd>')
        rows.append(f'<dt>Proof used by (Lean)</dt><dd>{entries(lb) or "—"}</dd>')
        libs = []
        for r in ldeps.roots(entry):
            d = lib_decls.get(r)
            if d:
                libs.append(f'<a href="{_attr(blob(d["file"], d["line_start"], d["line_end"]))}"><code>{_esc(r)}</code></a>')
            else:
                libs.append(f'<code>{_esc(r)}</code>')
        if libs:
            rows.append(f'<dt>Library proof</dt><dd>{", ".join(libs[:6])}</dd>')
    if not rows:
        return ""
    return ('<dl class="connections">' + "".join(rows) + '</dl>'
            '<p class="conn-note">Paper dependencies are reviewed TeX cross-references. Lean relations are '
            'extracted mechanically from the compiled proofs: an entry is listed when the other proof uses a '
            'library theorem that only this entry applies (hover for it); shared tools do not count.</p>')


# ----------------------------------------------------------------------
# Lean declaration index and selected results

SELECTED = [
    ("thm-3-7", "Normal approximation with exchangeable pairs in the Wasserstein metric"),
    ("thm-3-13", "Normal approximation with size-bias couplings"),
    ("thm-3-27", "Kolmogorov-metric bound via zero-bias couplings"),
    ("thm-4-14", "Poisson approximation for positively related indicators"),
    ("thm-5-4", "Exponential approximation with equilibrium couplings"),
    ("thm-5-8", "Yaglom's theorem for critical branching processes"),
    ("thm-6-5", "Geometric approximation with discrete equilibrium couplings"),
    ("thm-7-2", "Concentration inequalities from exchangeable pairs"),
]


def selected_results_html(site, graph: DepGraph) -> str:
    rows = []
    for nid, blurb in SELECTED:
        i = graph.by_id.get(nid)
        if not i:
            continue
        h = site.item_href(i)
        name = _esc(i.get("source") or DepGraph.short_name(i))
        name = f'<a href="{_attr(h)}">{name}</a>' if h else name
        st = i["status"] if i["status"] in STATUS_LABELS else "open"
        rows.append(f'<li><span class="sel-name">{name}</span> {chip(st, markers=i.get("markers", []))}'
                    f'<span class="sel-blurb">{_esc(blurb)}</span></li>')
    return ('<section><h2>Selected results</h2><ul class="selected">' + "".join(rows) + '</ul>'
            '<p class="lede">Every numbered result is listed on the <a href="results.html">results page</a>; '
            'its Lean statement, proof, dependencies and verification status sit next to the paper text.</p></section>')


def declarations_page(site, ldeps: LeanDeps, graph: DepGraph) -> str:
    lean = site.lean
    trs = []
    for e in sorted(lean.entries, key=lambda x: (x.file, x.line_start)):
        pid = site.where.get(f"lean-{e.name}")
        name = f'<a href="{pid}.html#lean-{_attr(e.name)}"><code>{_esc(e.name)}</code></a>' if pid else f'<code>{_esc(e.name)}</code>'
        item = ldeps.item_of.get(e.name)
        res = _esc(graph.by_id[item].get("source", "")) if item in graph.by_id else "prose claim or display"
        libs = []
        for r in ldeps.roots(e.name)[:4]:
            d = lean.lib_decls.get(r)
            libs.append(f'<a href="{_attr(lean.git.blob(d["file"], d["line_start"], d["line_end"]))}"><code>{_esc(r)}</code></a>'
                        if d else f'<code>{_esc(r)}</code>')
        st = e.status if e.status in STATUS_LABELS else "open"
        src = f'<a href="{_attr(lean.git.blob(e.file, e.line_start, e.line_end))}">{_esc(e.file.rsplit("/", 1)[-1])}:{e.line_start}</a>'
        search = " ".join([e.name, res, " ".join(ldeps.roots(e.name))]).lower()
        trs.append(f'<tr data-label="{_attr(st)}" data-markers="" data-named="1" data-search="{_attr(search)}">'
                   f'<td data-th="Statement entry">{name}<div class="label">{src}</div></td>'
                   f'<td data-th="Paper">{res}</td><td data-th="Status">{chip(st, markers=e.markers)}</td>'
                   f'<td data-th="Library proof" class="lean-names">{" ".join(libs) or "—"}</td></tr>')
    chips = "".join(
        f'<button type="button" class="chip" data-filter="{k}" aria-pressed="false">'
        f'<span class="status {STATUS_LABELS[k][1]}">{_esc(STATUS_LABELS[k][0])}</span></button>'
        for k in LEGEND_ORDER)
    rev = lean.git.rev[:7]
    body = f"""<h1>Lean declarations</h1>
<p class="lede">Every statement entry of the formalization at commit <code>{_esc(rev)}</code>, with the paper result it
states, its status, and the library theorems its proof applies (links go to the source lines). Each entry is a
<code>Prop</code> in <code>Formalization/Statements/SecN.lean</code> proved by <code>…_holds</code> in
<code>SecNProofs.lean</code>. Mathlib and core declarations are documented in the
<a href="https://leanprover-community.github.io/mathlib4_docs/">Mathlib documentation</a>; a doc-gen4 build of this
project is not published (see Methodology).</p>
<div class="filters"><input type="search" id="q" placeholder="Search entry, result or library theorem" aria-label="Search declarations">
<div class="chips"><button type="button" class="chip on" data-filter="" aria-pressed="true">All</button>{chips}</div>
<p class="filter-count" aria-live="polite"></p></div>
<div class="table-wrap"><table class="results stack decl-table"><thead><tr><th>Statement entry</th><th>Paper</th>
<th>Status</th><th>Library proof</th></tr></thead><tbody>{''.join(trs)}</tbody></table></div>"""
    return site.shell("Lean declarations · Fundamentals of Stein's method", body, "declarations", toc=False)
