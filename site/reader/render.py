"""HTML pages: paper text on the left, Lean on the right.

Ported from the Statistical-Foundations-RL reference site and adapted for
N. Ross, "Fundamentals of Stein's method", Probability Surveys 8 (2011)
210–293, DOI 10.1214/11-PS182, arXiv:1109.1880v1.

Key properties:
  - Paper has sections 1–7.
  - Progress counts are computed over the full 122-environment inventory
    (`docs/source-inventory.json`) plus the tracked running-text/display
    claims in `docs/COVERAGE.md`.
  - Uncovered inventory items and unreviewed compiled Lean statements are
    shown as `open`, never `proved`.
  - Status chips follow `docs/COVERAGE.md` (`proved`, `defined`, `corrected`,
    `restricted`, `source issue`, `open`) with `refuted` and `exercise`
    markers.
"""

from __future__ import annotations

import html
import json
import re
from datetime import datetime, timezone

from .info import InfoPages
from .lean import MARKERS, REPO, STATUS_LABELS, LeanIndex, chip

try:
    from .tex import html_id, label_id
except ImportError:
    def html_id(s: str) -> str:
        return re.sub(r"[^A-Za-z0-9_.-]", "-", s)

    def label_id(s: str) -> str:
        return "L-" + html_id(s)

MATHJAX = "https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml-full.js"
ARXIV = "https://arxiv.org/abs/1109.1880v1"
TITLE = "Fundamentals of Stein's method"
SUBTITLE = "arXiv:1109.1880v1"
MAINTAINER_HANDLE = "aaradhyapandeycs"
MAINTAINER_URL = "https://github.com/aaradhyapandeycs"
REPO_DISPLAY = REPO.split("//", 1)[1]

OURS = "proposed by this project; not confirmed by the author"

# Bar order for the 122 numbered results.
NUMBERED_BAR_KEYS = ("proved", "defined", "corrected", "restricted", "open")


def esc(t: str) -> str:
    return html.escape(str(t), quote=False)


def attr(t: str) -> str:
    return html.escape(str(t), quote=True)


def strip_tags(t: str) -> str:
    t = re.sub(r"<[^>]+>", "", t)
    return html.unescape(t)


_TEX_ACCENTS = {
    ('"', "a"): "ä", ('"', "o"): "ö", ('"', "u"): "ü", ('"', "A"): "Ä", ('"', "O"): "Ö", ('"', "U"): "Ü",
    ("'", "a"): "á", ("'", "e"): "é", ("'", "i"): "í", ("'", "o"): "ó", ("'", "u"): "ú", ("'", "c"): "ć",
    ("'", "n"): "ń", ("'", "s"): "ś", ("'", "z"): "ź", ("'", "y"): "ý", ("'", "E"): "É",
    ("`", "a"): "à", ("`", "e"): "è", ("`", "i"): "ì", ("`", "o"): "ò", ("`", "u"): "ù",
    ("^", "a"): "â", ("^", "e"): "ê", ("^", "i"): "î", ("^", "o"): "ô", ("^", "u"): "û",
    ("~", "a"): "ã", ("~", "n"): "ñ", ("~", "o"): "õ",
    ("v", "c"): "č", ("v", "s"): "š", ("v", "z"): "ž", ("v", "r"): "ř", ("v", "C"): "Č", ("v", "S"): "Š",
    ("c", "c"): "ç", ("c", "C"): "Ç", ("c", "s"): "ş",
    ("H", "o"): "ő", ("H", "u"): "ű",
    ("u", "a"): "ă", ("u", "g"): "ğ",
    (".", "z"): "ż",
}


def clean_bbl_item(raw: str) -> str:
    """Convert a .bbl \\bibitem body to clean HTML while keeping $...$ math for MathJax."""
    # Split out inline math $...$ first so we never corrupt TeX math
    parts = re.split(r"(?<!\\)\$([^$]+)\$", raw)
    out = []
    for idx, part in enumerate(parts):
        if idx % 2 == 1:
            out.append(f"\\({esc(part)}\\)")
            continue
        s = part
        s = re.sub(r"\\newblock\b\s*", " ", s)
        s = re.sub(r"\\url\{([^}]+)\}", lambda m: f"@@URL|{m.group(1).strip()}@@", s)
        s = re.sub(r"\\href\{([^}]+)\}\{([^}]+)\}", lambda m: f"@@HREF|{m.group(1).strip()}|{m.group(2).strip()}@@", s)
        # {\em ...} and \emph{...} / \textit{...}
        s = re.sub(r"\{\\(?:em|it|itshape)\b\s*([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", r"@@EM|\1@@", s)
        s = re.sub(r"\\(?:emph|textit)\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}", r"@@EM|\1@@", s)
        s = re.sub(r"\{\\bf\b\s*([^{}]*)\}|\\textbf\{([^{}]*)\}", lambda m: f"@@BF|{m.group(1) or m.group(2)}@@", s)
        # TeX accents: \"o, \"{o}, \'{\i}, \H o, \H{o}, \v{c}, \l, \o, etc.
        s = re.sub(r"\\([\"'`^~vcuH.])\{\\?([A-Za-z])\}", lambda m: _TEX_ACCENTS.get((m.group(1), m.group(2)), m.group(2)), s)
        s = re.sub(r"\\([vcuH])\s+\\?([A-Za-z])", lambda m: _TEX_ACCENTS.get((m.group(1), m.group(2)), m.group(2)), s)
        s = re.sub(r"\\([\"'`^~])\\?([A-Za-z])", lambda m: _TEX_ACCENTS.get((m.group(1), m.group(2)), m.group(2)), s)
        s = s.replace(r"\l{}", "ł").replace(r"\L{}", "Ł").replace(r"\o{}", "ø").replace(r"\O{}", "Ø")
        s = re.sub(r"\\l(?![A-Za-z])", "ł", s)
        s = re.sub(r"\\L(?![A-Za-z])", "Ł", s)
        s = re.sub(r"\\o(?![A-Za-z])", "ø", s)
        s = s.replace("---", "—").replace("--", "–").replace("~", " ").replace(r"\&", "&")
        # Strip protective braces like {S}tein -> Stein
        while re.search(r"\{([^{}]*)\}", s):
            s = re.sub(r"\{([^{}]*)\}", r"\1", s)
        s = re.sub(r"\s+", " ", s)
        s_esc = esc(s)
        s_esc = re.sub(r"@@EM\|(.*?)@@", r"<em>\1</em>", s_esc)
        s_esc = re.sub(r"@@BF\|(.*?)@@", r"<strong>\1</strong>", s_esc)
        s_esc = re.sub(
            r"@@URL\|(.*?)@@",
            lambda m: f'<a href="{attr(html.unescape(m.group(1)))}">{m.group(1)}</a>',
            s_esc,
        )
        s_esc = re.sub(
            r"@@HREF\|(.*?)\|(.*?)@@",
            lambda m: f'<a href="{attr(html.unescape(m.group(1)))}">{m.group(2)}</a>',
            s_esc,
        )
        out.append(s_esc)
    return "".join(out).strip()


class Site(InfoPages):
    """The reader site for the Stein's method formalization."""

    def __init__(
        self,
        book,
        lean: LeanIndex,
        pages: list,
        front: list,
        back: list,
        ci_run_url: str | None = None,
        audit_line: str | None = None,
    ):
        self.book = book
        self.lean = lean
        self.pages = pages
        self.front = front
        self.back = back
        self.ci_run_url = ci_run_url
        self.audit_line = audit_line
        self.where: dict[str, str] = {}
        self.built = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
        self.data = self.lean.summary_data()
        self.section_titles = {p.section: p.title for p in pages if p.level == 0}
        self.numbered_by_id = {item["id"]: item for item in self.lean.numbered_items}
        self.place()

    # ------------------------------------------------------------------
    # placement: map each Lean entry, Definition card, and Ledger card to a paper block

    def place(self):
        """Associate each Lean entry and ledger item with the paper block it covers."""
        self.matches: dict[int, list] = {}
        self.home: dict[int, list] = {}
        self.placed: dict[str, tuple[str, str, int, int]] = {}
        self.extra_col_cards: dict[int, list[str]] = {}

        raw_units = [
            (page, top, b)
            for page in self.pages
            for top in page.blocks
            for b in self._units(top)
        ]

        # Read source TeX lines once for exact paragraph disambiguation when needed
        tex_lines: list[str] = []
        tex_file = getattr(self.book, "tex_root", None)
        if tex_file is not None and (tex_file / "SteinIntro_utf8.tex").is_file():
            tex_lines = (tex_file / "SteinIntro_utf8.tex").read_text(encoding="utf-8").splitlines()
        total_tex_lines = len(tex_lines) or 9999

        # Precompute anchors and effective line spans (exact or bracketed) for every unit
        unit_info = []
        n_units = len(raw_units)
        known_starts = [getattr(u[2], "line_start", None) for u in raw_units]
        known_ends = [getattr(u[2], "line_end", None) for u in raw_units]

        next_known = [total_tex_lines] * n_units
        nxt = total_tex_lines
        for i in range(n_units - 1, -1, -1):
            if known_starts[i] is not None:
                nxt = known_starts[i]
            next_known[i] = nxt

        prev_end = 1
        for i, (page, top, b) in enumerate(raw_units):
            h = getattr(b, "html", "") or ""
            anchors = set(html.unescape(m.group(1)) for m in re.finditer(r'id="([^"]+)"', h))
            b_labels = set(getattr(b, "labels", None) or [])
            for a in anchors:
                if a.startswith("L-"):
                    b_labels.add(a[2:])
            ls = known_starts[i]
            le = known_ends[i]
            if ls is not None and le is not None:
                eff_s, eff_e, exact = ls, le, True
                prev_end = max(prev_end, le)
            else:
                eff_s = prev_end + 1
                eff_e = max(eff_s, next_known[i] - 1)
                exact = False
            plain_words = set(re.findall(r"[A-Za-z]{4,}", strip_tags(h).lower()))
            unit_info.append({
                "page": page,
                "top": top,
                "b": b,
                "anchors": anchors,
                "labels": b_labels,
                "eff_s": eff_s,
                "eff_e": eff_e,
                "exact": exact,
                "words": plain_words,
            })

        def tex_words_for_range(a: int, b_line: int) -> set[str]:
            if not tex_lines or a <= 0:
                return set()
            chunk = " ".join(tex_lines[max(0, a - 1):min(len(tex_lines), b_line)])
            chunk = re.sub(r"\\[A-Za-z@]+", " ", chunk)
            return set(re.findall(r"[A-Za-z]{4,}", chunk.lower()))

        def best_block_for(primary_labels: list[str], ranges: list[dict], sec: str | None, env_id: str | None = None):
            # 1. Exact environment id anchor E-<env_id>
            if env_id:
                target_eid = f"E-{html_id(env_id)}"
                for ui in unit_info:
                    if target_eid in ui["anchors"]:
                        return ui

            # 2. Primary label match (prefer non-heading blocks when both heading & body carry label)
            if primary_labels:
                lab_ids = {label_id(l) for l in primary_labels}
                lab_set = set(primary_labels)
                cands = [
                    ui for ui in unit_info
                    if (ui["labels"] & lab_set) or (ui["anchors"] & lab_ids)
                ]
                if cands:
                    non_head = [ui for ui in cands if getattr(ui["b"], "kind", "") != "heading"]
                    return (non_head or cands)[0]

            # 3. Line-range overlap (prefer same section, exact span over bracketed, non-heading, word overlap)
            for r in ranges:
                ra, rb = r["line_start"], r["line_end"]
                twords = tex_words_for_range(ra, rb)
                cands = []
                for idx, ui in enumerate(unit_info):
                    if max(ui["eff_s"], ra) <= min(ui["eff_e"], rb):
                        same_sec = 1 if (not sec or getattr(ui["page"], "section", None) == sec) else 0
                        not_head = 1 if getattr(ui["b"], "kind", "") != "heading" else 0
                        exact = 1 if ui["exact"] else 0
                        overlap_words = len(twords & ui["words"]) if twords else 0
                        span_len = max(1, ui["eff_e"] - ui["eff_s"] + 1)
                        cands.append(((same_sec, exact, not_head, overlap_words, -span_len, -idx), ui))
                if cands:
                    cands.sort(key=lambda x: x[0], reverse=True)
                    return cands[0][1]
            return None

        def put_entry(e, ui):
            page, top, b = ui["page"], ui["top"], ui["b"]
            if e.name not in self.placed:
                self.placed[e.name] = (page.id, self._anchor(b, ui["anchors"]), id(top), id(b))
                self.home.setdefault(id(b), []).append(e)
                self.matches.setdefault(id(b), [])
                if e not in self.matches[id(b)]:
                    self.matches[id(b)].append(e)

        # Place all Formalization/Statements/Sec*.lean entries
        for e in self.lean.entries:
            ui = best_block_for(e.primary_labels, e.ranges, e.section)
            if ui is None and e.labels:
                ui = best_block_for(e.labels, e.ranges, e.section)
            if ui is not None:
                put_entry(e, ui)

        self.unplaced = [e for e in self.lean.entries if e.name not in self.placed]

        # Place Definition cards (Def 3.1, 3.2, 3.7, 3.10, 6.1, ...)
        for dc in self.lean.def_cards:
            rng = [{"file": "SteinIntro.tex", "line_start": dc.line_start, "line_end": dc.line_end}] if dc.line_start else []
            ui = best_block_for([], rng, dc.section, env_id=dc.env_id)
            if ui is not None:
                self.extra_col_cards.setdefault(id(ui["top"]), []).append(self.lean.def_card_html(dc))

        # Place Ledger-only COVERAGE cards (e.g. Definition 6.1, §3.3.1 prose irreducibility, Example 3.8, ...)
        for lc in self.lean.ledger_cards:
            ui = best_block_for(lc.labels, lc.ranges, lc.section, env_id=lc.env_id or None)
            if ui is not None:
                self.extra_col_cards.setdefault(id(ui["top"]), []).append(self.lean.ledger_card_html(lc))

    def placement_problems(self) -> list:
        return []

    @staticmethod
    def _units(b) -> list:
        """A top-level block followed by its nested numbered or labelled children."""
        return [b] + list(getattr(b, "children", []))

    @staticmethod
    def _anchor(b, anchors: set[str] | None = None) -> str:
        if getattr(b, "anchor", None):
            return b.anchor
        if anchors:
            for pref in ("E-", "L-", "sec-"):
                for a in sorted(anchors):
                    if a.startswith(pref):
                        return a
        labels = getattr(b, "labels", None) or []
        return label_id(labels[0]) if labels else ""

    # ------------------------------------------------------------------
    # status chips derived from COVERAGE.md + inventory

    def coverage_status(self, entry_name: str) -> str:
        return self.lean.coverage_status(entry_name)

    def status_chip(self, entry_name: str) -> str:
        status = self.coverage_status(entry_name)
        label = STATUS_LABELS.get(status, STATUS_LABELS["open"])
        return f'<span class="status {label[1]}">{esc(label[0])}</span>'

    def entry_chip(self, e) -> str:
        return chip(e.status, markers=e.markers, sub=e.subreason if e.status == "open" else "")

    # ------------------------------------------------------------------
    # Lean column

    def lean_column(self, page, top) -> str:
        out = []
        seen = set()
        for b in self._units(top):
            entries = self.matches.get(id(b), [])
            for e in entries:
                if e.name in seen:
                    continue
                seen.add(e.name)
                pid, _, top_id, _ = self.placed[e.name]
                if pid == page.id and top_id == id(top):
                    out.append(self.lean.card(e))

        for extra_html in self.extra_col_cards.get(id(top), []):
            out.append(extra_html)

        # If this block is one of the 122 numbered environments and has no card yet,
        # show its explicit `open (not yet reviewed)` status right beside it.
        if not out and getattr(top, "kind", "") == "env":
            h = getattr(top, "html", "") or ""
            m_env = re.search(r'id="E-([^"]+)"', h)
            if m_env:
                env_id = m_env.group(1)
                inv_item = self.numbered_by_id.get(env_id)
                if inv_item and inv_item["status"] == "open":
                    chips_html = chip("open", markers=inv_item.get("markers", ()), sub=inv_item.get("subreason", "not yet reviewed"))
                    out.append(f'<div class="lean-none">{chips_html}</div>')

        return "".join(out)

    # ------------------------------------------------------------------
    # page pieces

    def block_html(self, b) -> str:
        h = getattr(b, "html", "") or ""
        if getattr(b, "in_proof", False):
            h = f'<div class="in-proof">{h}</div>'
        return h

    def page_body(self, page) -> str:
        rows, buf = [], []

        def flush():
            if buf:
                rows.append(
                    f'<div class="row"><div class="book-col">{"".join(buf)}</div>'
                    f'<aside class="lean-col" aria-hidden="true"></aside></div>'
                )
                buf.clear()

        for b in page.blocks:
            col = self.lean_column(page, b)
            if col:
                flush()
                rows.append(
                    f'<div class="row paired"><div class="book-col">{self.block_html(b)}</div>'
                    f'<aside class="lean-col" aria-label="Lean">{col}</aside></div>'
                )
            else:
                buf.append(self.block_html(b))
        flush()
        return "".join(rows)

    def toc(self, current: str | None) -> str:
        sections, cur_sec = [], None
        current_page = next((p for p in self.pages if p.id == current), None)
        for p in self.pages:
            if p.level == 0:
                cur_sec = {"page": p, "subsections": []}
                sections.append(cur_sec)
            elif cur_sec:
                cur_sec["subsections"].append(p)
        out = ['<nav class="toc" aria-label="Paper contents"><a class="toc-home" href="book.html">Contents</a><ol>']
        for sec in sections:
            p = sec["page"]
            is_open = current_page is not None and getattr(current_page, "section", None) == getattr(p, "section", None)
            items = "".join(
                f'<li><a href="{s.id}.html"{" aria-current=page" if s.id == current else ""}>'
                f'<span class="secnum">{esc(s.number or "")}</span> {s.title}</a></li>'
                for s in sec["subsections"]
            )
            out.append(
                f'<li><details{" open" if is_open else ""}><summary><a href="{p.id}.html"'
                f'{" aria-current=page" if p.id == current else ""}>'
                f'<span class="secnum">{esc(p.number or "")}</span> '
                f'{p.title}</a></summary><ol>{items}</ol></details></li>'
            )
        out.append('<li class="toc-extra"><a href="references.html">References</a></li></ol></nav>')
        return "".join(out)

    NAV = [
        ("index",       "Overview"),
        ("results",     "Results"),
        ("book",        "Paper"),
        ("graph",       "Dependency graph"),
        ("declarations", "Lean"),
        ("status",      "Status", [("status", "Progress"), ("errata", "Source issues")]),
        ("methodology", "Methodology"),
        ("contribute",  "Contribute"),
        ("credits",     "Credits"),
    ]

    def nav_html(self, current: str | None, mobile: bool = False) -> str:
        cur = current or ""
        book_ids = {p.id for p in self.pages} | {"book", "references"}
        out = []
        for item in self.NAV:
            pid, word = item[0], item[1]
            here = (
                cur == pid
                or (pid == "book" and cur in book_ids)
                or (len(item) > 2 and cur in {x[0] for x in item[2]})
            )
            mark = ' aria-current="page"' if here else ""
            if len(item) > 2:
                subs = "".join(
                    f'<a href="{x}.html"{" aria-current=page" if cur == x else ""}>{w}</a>'
                    for x, w in item[2]
                )
                if mobile:
                    out.append(f'<span class="menu-group">{word}</span>{subs}')
                else:
                    out.append(
                        f'<details class="dd"><summary{mark}>{word}</summary>'
                        f'<div class="dd-menu">{subs}</div></details>'
                    )
            else:
                out.append(f'<a href="{pid}.html"{mark}>{word}</a>')
        out.append(f'<a href="{REPO}">GitHub ↗</a>')
        return "".join(out)

    def shell(self, title: str, body: str, current: str | None = None, toc: bool = True) -> str:
        """Generate the full HTML page frame (WIP banner + attribution footer + CI status link)."""
        rev = self.lean.git.rev
        layout = (
            f'<div class="layout">{self.toc(current)}<main id="main">{body}</main></div>'
            if toc
            else f'<div class="layout single"><main id="main">{body}</main></div>'
        )
        toc_btn = (
            '<button class="toc-toggle" type="button" aria-label="Show paper contents">☰</button>'
            if toc
            else ""
        )
        ci_link = (
            f'<a href="{attr(self.ci_run_url)}">CI run</a>'
            if self.ci_run_url
            else f'<a href="{REPO}/commit/{rev}">CI status for this commit</a>'
        )
        return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{esc(title)}</title>
<link rel="stylesheet" href="assets/style.css">
<script src="assets/theme.js"></script>
<script>{self.inline_mathjax_config()}</script>
<script defer src="{MATHJAX}"></script>
</head>
<body class="tex2jax_ignore">
<a class="skip" href="#main">Skip to content</a>
<header class="top">
  {toc_btn}<a class="brand" href="index.html">Stein's method <span>in Lean</span></a>
  <nav class="links" aria-label="Site">{self.nav_html(current)}</nav>
  <details class="menu"><summary aria-label="Menu">Menu</summary><nav class="menu-links" aria-label="Site">{self.nav_html(current, True)}</nav></details>
  <button class="theme" type="button" aria-label="Switch between light and dark">◐</button>
</header>
<div class="banner"><strong>Work in progress.</strong> The paper is not yet fully formalized.
<a href="status.html">Progress</a></div>
{layout}
<footer>
<p>Paper text: N. Ross, <em>Fundamentals of Stein's method</em>,
Probability Surveys 8 (2011) 210–293,
<a href="https://doi.org/10.1214/11-PS182">DOI 10.1214/11-PS182</a>,
published under the journal's <a href="https://imstat.org/journals-and-publications/probability-surveys/probability-surveys-manuscript-submission/">Creative Commons Attribution License</a>;
rendered from the author's preprint <a href="{ARXIV}">{SUBTITLE}</a>.
Text rendered unofficially; may differ from the published version.
Lean code: Apache-2.0, commit <a href="{REPO}/tree/{rev}"><code>{rev[:10]}</code></a>
({ci_link}), Lean <code>{esc(self.toolchain())}</code>, Mathlib
<code>{esc(self.mathlib_rev()[:10])}</code>. Built {self.built}.
<a href="credits.html">Credits</a> ·
<a href="methodology.html#verify">Check it yourself</a></p>
</footer>
<script src="assets/app.js"></script>
</body>
</html>
"""

    # ------------------------------------------------------------------
    # pages

    def book_pages(self) -> dict:
        out = {}
        for i, page in enumerate(self.pages):
            prev_ = self.pages[i - 1] if i else None
            next_ = self.pages[i + 1] if i + 1 < len(self.pages) else None
            nav = '<nav class="pager">'
            if prev_:
                nav += f'<a class="prev" href="{prev_.id}.html">← {esc(prev_.number or "")} {prev_.title}</a>'
            if next_:
                nav += f'<a class="next" href="{next_.id}.html">{esc(next_.number or "")} {next_.title} →</a>'
            nav += "</nav>"
            head = '<div class="cols-head"><span>Paper text</span><span>Lean</span></div>'
            body = head + self.page_body(page) + nav
            title = f"{page.number + ' ' if page.number else ''}{strip_tags(page.title)} · {TITLE}"
            out[page.id] = self.shell(title, body, page.id)
        return out

    # ------------------------------------------------------------------
    # full-inventory counts derived from source-inventory.json + COVERAGE.md

    def coverage_counts(self) -> dict:
        return self.lean.coverage_counts()

    def cnt_tag(self, path: str, val: int) -> str:
        """Count span machine-checked against `self.data["summary"]` by `build.py`."""
        return f'<span class="n" data-count="{attr(path)}">{val}</span>'

    def stacked_bar(self) -> str:
        num = self.coverage_counts()["numbered"]
        total = num["total"] or 1
        segs = []
        legend_items = []
        for status in NUMBERED_BAR_KEYS:
            label, _ = STATUS_LABELS[status]
            v = num.get(status, 0)
            if v:
                segs.append(
                    f'<span class="seg seg-{status}" style="width:{100 * v / total:.3f}%" '
                    f'title="{v} {attr(label)} (of {total} numbered environments)"></span>'
                )
            legend_items.append(
                f'<li><span class="sw seg-{status}"></span>'
                f'{self.cnt_tag(f"numbered.{status}", v)} {esc(label)}</li>'
            )
        return (
            f'<div class="bar" role="img" aria-label="Status of all {total} numbered environments in the paper">'
            f'{"".join(segs)}</div>'
            f'<ul class="bar-legend">{"".join(legend_items)}</ul>'
        )

    def count_sentence(self) -> str:
        c = self.coverage_counts()
        num = c["numbered"]
        pr = c["prose"]
        mk = c["markers"]

        prose_bits = []
        for s in ("proved", "defined", "corrected", "restricted", "source-issue", "open"):
            v = pr.get(s, 0)
            if v:
                lbl, cls = STATUS_LABELS[s]
                prose_bits.append(
                    f'{self.cnt_tag(f"prose.{s}", v)} <span class="status {cls}">{esc(lbl)}</span>'
                )

        ref_note = ""
        if mk.get("refuted", 0):
            ref_note = (
                f' ({self.cnt_tag("markers.refuted", mk["refuted"])} with a machine-checked '
                f'<span class="marker mk-refuted">{esc(MARKERS["refuted"])}</span> witness)'
            )

        return (
            f'{self.cnt_tag("numbered.formalized", num["formalized"])} of '
            f'{self.cnt_tag("numbered.total", num["total"])} numbered results formalized '
            f'({self.cnt_tag("numbered.proved", num["proved"])} '
            f'<span class="status st-proved">proved</span>, '
            f'{self.cnt_tag("numbered.defined", num["defined"])} '
            f'<span class="status st-defined">defined</span>, '
            f'{self.cnt_tag("numbered.corrected", num["corrected"])} '
            f'<span class="status st-corrected">corrected</span>, '
            f'{self.cnt_tag("numbered.restricted", num["restricted"])} '
            f'<span class="status st-restricted">restricted</span>{ref_note}); '
            f'{self.cnt_tag("numbered.open", num["open"])} '
            f'<span class="status st-open">open</span>. '
            f'In addition, {self.cnt_tag("prose.total", pr["total"])} running-text and display claims '
            f'are tracked in <code>COVERAGE.md</code> ({", ".join(prose_bits)}).'
        )

    def section_count_summary(self, sec: str) -> str:
        sc = self.coverage_counts()["by_section"].get(sec, {})
        tot = sc.get("total", 0)
        form = sc.get("formalized", 0)
        opn = sc.get("open", 0)
        wip = sc.get("wip", 0)
        if not tot:
            return ""
        detail_parts = []
        for s in ("proved", "defined", "corrected", "restricted"):
            if sc.get(s, 0):
                detail_parts.append(f'{sc[s]} {STATUS_LABELS[s][0]}')
        detail = f' ({", ".join(detail_parts)})' if detail_parts else ""
        wip_note = f', {wip} Lean WIP unreviewed' if wip else ""
        return f'{form} of {tot} numbered results formalized{detail}; {opn} open{wip_note}'

    def snapshot_line(self) -> str:
        rev = self.lean.git.rev
        return (
            f'Inventory and ledgers at commit <a href="{REPO}/tree/{rev}"><code>{rev[:10]}</code></a> · '
            f'Lean <code>{esc(self.toolchain())}</code> · Mathlib <code>{esc(self.mathlib_rev()[:10])}</code> · '
            f'built {esc(self.built)}'
        )

    # ------------------------------------------------------------------
    # anchors and links

    def index_anchors(self, html_pages: dict):
        for pid, text in html_pages.items():
            for m in re.finditer(r'id="([^"]+)"', text):
                self.where.setdefault(html.unescape(m.group(1)), pid)

    def item_href(self, item: dict) -> str | None:
        if not item.get("is_prose") and item.get("id"):
            eid = f'E-{html_id(item["id"])}'
            if eid in self.where:
                return f'{self.where[eid]}.html#{attr(eid)}'
        for lab in item.get("labels", []):
            lid = label_id(lab)
            if lid in self.where:
                return f'{self.where[lid]}.html#{attr(lid)}'
        for ln in item.get("lean_names", []):
            cid = f'lean-{ln}'
            if cid in self.where:
                return f'{self.where[cid]}.html#{attr(cid)}'
        return None

    # ------------------------------------------------------------------
    # results page (full 122-environment inventory + tracked prose claims)

    def result_rows(self) -> list:
        return self.lean.all_result_items()

    def results_page(self) -> str:
        rows_data = self.result_rows()
        entry_by_name = {e.name: e for e in self.lean.entries}
        trs, last_sec = [], None

        for r in rows_data:
            if r["section"] != last_sec:
                last_sec = r["section"]
                sec_sum = self.section_count_summary(last_sec)
                trs.append(
                    f'<tr class="ch-row" data-ch="{attr(last_sec)}"><th colspan="4">'
                    f'Section {esc(last_sec)} {esc(self.section_titles.get(last_sec, ""))} '
                    f'<span class="ch-count">{esc(sec_sum)}</span></th></tr>'
                )

            status = r["status"] if r["status"] in STATUS_LABELS else "open"
            markers = r.get("markers", [])
            sub = r.get("subreason", "") if status == "open" else ""
            st_html = chip(status, markers=markers, sub=sub)

            lean_links = []
            for x in r.get("lean_names", []):
                if x in entry_by_name:
                    ent = entry_by_name[x]
                    lean_links.append(
                        f'<a href="{attr(self.lean.git.blob(ent.file, ent.line_start, ent.line_end))}">'
                        f'<code>{esc(x)}</code></a>'
                    )
                elif x in self.lean.lib_decls:
                    ld = self.lean.lib_decls[x]
                    lean_links.append(
                        f'<a href="{attr(self.lean.git.blob(ld["file"], ld["line_start"], ld["line_end"]))}">'
                        f'<code>{esc(x)}</code></a>'
                    )
                else:
                    lean_links.append(f'<code>{esc(x)}</code>')
            lean_code = " ".join(lean_links) or "—"

            href = self.item_href(r)
            source_html = (
                f'<a href="{href}">{esc(r["source"])}</a>'
                if href else esc(r["source"])
            )
            tex_label = esc(r.get("label", "—"))
            search = " ".join([
                r["source"],
                r.get("label", ""),
                r.get("lean", ""),
                status,
                " ".join(markers),
                sub,
            ]).lower()
            markers_attr = " ".join(markers)
            trs.append(
                f'<tr data-label="{attr(status)}" data-markers="{attr(markers_attr)}" '
                f'data-ch="{attr(r["section"])}" data-search="{attr(search)}">'
                f'<td data-th="Item">{source_html}</td>'
                f'<td data-th="Label"><code>{tex_label}</code></td>'
                f'<td data-th="Status">{st_html}</td>'
                f'<td data-th="Lean" class="lean-names">{lean_code}</td></tr>'
            )

        chips = "".join(
            f'<button type="button" class="chip" data-filter="{s}" aria-pressed="false">'
            f'<span class="status {STATUS_LABELS[s][1]}">{esc(STATUS_LABELS[s][0])}</span></button>'
            for s in STATUS_LABELS
        )
        sections_opts = "".join(
            f'<option value="{attr(p.section)}">Section {esc(p.section)}</option>'
            for p in self.pages if p.level == 0 and getattr(p, "section", None)
        )

        unplaced = ""
        if self.unplaced:
            items = "".join(
                f'<li><a href="{attr(self.lean.git.blob(e.file, e.line_start, e.line_end))}">'
                f'<code>{esc(e.name)}</code></a></li>'
                for e in self.unplaced
            )
            unplaced = (
                '<section class="unplaced"><h2>Lean entries not matched to a paper location</h2>'
                '<p>These statement-index entries cite no label or line range the reader could match. '
                f'They are listed so nothing is hidden.</p><ul>{items}</ul></section>'
            )

        body = f"""<h1>Results</h1>
<p class="lede">All {self.cnt_tag("numbered.total", self.coverage_counts()["numbered"]["total"])} numbered environments
from <code>docs/source-inventory.json</code> together with all tracked running-text and display claims from
<code>docs/COVERAGE.md</code>, in paper order at commit <code>{self.lean.git.rev[:10]}</code>.</p>
<p class="lede">{self.count_sentence()}</p>
<div class="filters" role="search"><input type="search" id="q"
  placeholder="Search number, label, status, or Lean name" aria-label="Search results">
<div class="chips" role="group" aria-label="Filter by status">
<button type="button" class="chip on" data-filter="" aria-pressed="true">All</button>{chips}
<label class="toggle"><input type="checkbox" id="f-refuted"> {esc(MARKERS["refuted"])}</label>
<select id="f-ch" aria-label="Section"><option value="">All sections</option>{sections_opts}</select>
</div>
<p class="filter-count" aria-live="polite"></p></div>
<div class="table-wrap"><table class="results stack"><thead><tr><th>Item</th><th>Label</th>
<th>Status</th><th>Lean declarations</th></tr></thead>
<tbody>{''.join(trs)}</tbody></table></div>{unplaced}"""
        return self.shell(f"Results · {TITLE}", body, "results", toc=False)

    # ------------------------------------------------------------------
    # overview

    def section_pages(self) -> list:
        return [p for p in self.pages if p.level == 0]

    def section_title(self, sec) -> str:
        p = next((p for p in self.pages if p.level == 0 and getattr(p, "section", None) == sec), None)
        return p.title if p else ""

    def index_page(self) -> str:
        sections = self.section_pages()
        lis = []
        for sec_page in sections:
            sec = getattr(sec_page, "section", None) or ""
            summary = self.section_count_summary(sec)
            subsections = [
                p for p in self.pages
                if p.level == 1 and getattr(p, "section", None) == sec
            ]
            subs_html = "".join(
                f'<li><a href="{s.id}.html"><span class="secnum">{esc(s.number or "")}</span> {s.title}</a></li>'
                for s in subsections
            )
            lis.append(
                f'<li><a href="{sec_page.id}.html">'
                f'<span class="secnum">{esc(sec_page.number or "")}</span> {sec_page.title}</a>'
                f'<span class="ch-count">{esc(summary)}</span>'
                f'{"<ol class=sections>" + subs_html + "</ol>" if subs_html else ""}</li>'
            )

        body = f"""<section class="hero">
<h1>{TITLE}<span>{SUBTITLE}</span></h1>
<p class="authors">N. Ross · <a href="{ARXIV}">arXiv:1109.1880v1</a></p>
<p>The paper, with a Lean&nbsp;4 formalization shown next to the results it covers.
This formalization is <strong>not complete</strong>, it is <strong>not endorsed by the author</strong>, and its
reviews were done by AI agents, <strong>not by a human referee</strong>.</p>
<p class="actions"><a class="button primary" href="book.html">Read the paper</a>
<a class="button" href="status.html">Progress</a>
<a class="button" href="graph.html">Dependency graph</a>
<a class="button" href="declarations.html">Lean declarations</a>
<a class="button" href="methodology.html">Methodology</a></p>
</section>
<section><h2>At a glance</h2>
<p class="lede">Full paper inventory (<code>docs/source-inventory.json</code>) combined with
<code>docs/COVERAGE.md</code> at build time:</p>
{self.stacked_bar()}
<p>{self.count_sentence()}</p>
<p class="snapshot">{self.snapshot_line()}</p></section>
{getattr(self, "selected_html", "")}
<section><h2>Sections</h2><ol class="chapters">{''.join(lis)}</ol></section>
<section class="abstract"><details><summary><h2>About the paper</h2></summary>
<p>N. Ross, <em>Fundamentals of Stein's method</em>, Probability Surveys 8 (2011) 210–293,
<a href="https://doi.org/10.1214/11-PS182">DOI 10.1214/11-PS182</a>.
An introduction to Stein's method for distributional approximation, covering
the normal, Poisson, exponential, and geometric distributions as well as concentration of measure.</p>
{''.join(getattr(b, "html", "") for b in self.front)}
</details></section>"""
        return self.shell(TITLE, body, "index", toc=False)

    # ------------------------------------------------------------------
    # references page

    def references_page(self) -> str:
        """Render the bibliography from the paper's .bbl file."""
        bbl = ""
        candidates = []
        if hasattr(self.book, "tex_root"):
            candidates.append(self.book.tex_root / "SteinIntro.bbl")
        if hasattr(self.book, "root"):
            candidates.extend([
                self.book.root / "docs/source/SteinIntro.bbl",
                self.book.root / "source/upstream/SteinIntro.bbl",
                self.book.root / "source/upstream/tex/SteinIntro.bbl",
            ])
        for p in candidates:
            if p.is_file():
                bbl = p.read_text(encoding="utf-8", errors="replace")
                break

        items = []
        if bbl:
            for m in re.finditer(
                r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}(.*?)(?=\\bibitem|\\end\{thebibliography\}|\Z)",
                bbl,
                re.S,
            ):
                key = m.group(1).strip()
                rendered = clean_bbl_item(m.group(2))
                items.append(f'<li id="ref-{attr(key)}">{rendered}</li>')

        body = (
            '<h1>References</h1>'
            f'<ol class="refs tex2jax_process">{"".join(items) or "<li>Bibliography not available.</li>"}</ol>'
        )
        return self.shell(f"References · {TITLE}", body, "references")

    # ------------------------------------------------------------------
    # MathJax config

    def inline_mathjax_config(self) -> str:
        if not hasattr(self, "_mathjax_inline"):
            self._mathjax_inline = self.mathjax_config().replace("</", "<\\/")
        return self._mathjax_inline

    def mathjax_config(self) -> str:
        cfg = {
            "tex": {
                "packages": {"[+]": ["mathtools", "boldsymbol", "color", "html", "cancel", "textmacros"]},
                "macros": self.book.mathjax_macros() if hasattr(self.book, "mathjax_macros") else {},
                "tags": "none",
                "processEscapes": True,
                "processEnvironments": True,
                "inlineMath":   [["\\(", "\\)"]],
                "displayMath":  [["\\[", "\\]"]],
            },
            "options": {
                "ignoreHtmlClass": "tex2jax_ignore",
                "processHtmlClass": "tex2jax_process",
            },
            "chtml": {"scale": 1.0},
        }
        return "window.MathJax = " + json.dumps(cfg, ensure_ascii=False, indent=1) + ";\n"

    def search_data(self) -> str:
        return json.dumps(self.result_rows(), ensure_ascii=False)

    # ------------------------------------------------------------------
    # cross-references between pages

    def resolve(self, pages: dict) -> dict:
        where: dict[str, str] = {}
        for pid, text in pages.items():
            for m in re.finditer(r'id="([^"]+)"', text):
                where.setdefault(html.unescape(m.group(1)), pid)
        missing: dict[str, int] = {}

        def fmt(mode: str, cmd: str, label: str) -> str:
            label_clean = label.strip()
            num, kind = None, None
            if hasattr(self.book, "label_number"):
                res = self.book.label_number(label_clean)
                if isinstance(res, tuple):
                    num = res[0]
                    kind = res[1] if len(res) > 1 else None
                else:
                    num = res
            if num is None and hasattr(self.lean, "label_number"):
                res2 = self.lean.label_number(label_clean)
                if isinstance(res2, tuple):
                    num = res2[0]
                    kind = res2[1] if len(res2) > 1 else None
                else:
                    num = res2

            if num is None:
                missing[label_clean] = missing.get(label_clean, 0) + 1
                return "??"

            is_eq = cmd in ("eqref", "eq") or (cmd in ("cref", "Cref") and kind in ("equation", "display"))
            text_out = f"({num})" if is_eq else str(num)
            if cmd in ("cref", "Cref") and not is_eq:
                word = (
                    "Section" if kind in ("heading", "section", "subsection", "subsubsection")
                    else (self.book.env_title(kind) if hasattr(self.book, "env_title") and kind else "")
                )
                if word:
                    text_out = f"{word} {text_out}"

            if mode == "m":
                return text_out

            anchor = label_id(label_clean)
            pid = where.get(anchor)
            if not pid and hasattr(self.book, "label_owner"):
                owner = self.book.label_owner.get(label_clean)
                if owner:
                    for cand in (f'E-{html_id(owner["id"])}', f'sec-{owner.get("number")}'):
                        if cand in where:
                            anchor, pid = cand, where[cand]
                            break
            if not pid:
                return esc(text_out)
            return f'<a class="ref" href="{pid}.html#{attr(anchor)}">{esc(text_out)}</a>'

        out = {}
        for pid, text in pages.items():
            out[pid] = re.sub(
                r"@@REF\|(\w)\|(\w+)\|([^@]*)@@",
                lambda m: fmt(m.group(1), m.group(2), m.group(3)),
                text,
            )
        self.missing_refs = missing
        for pid in out:
            out[pid] = re.sub(
                r"<title>(.*?)</title>",
                lambda m: "<title>" + esc(strip_tags(m.group(1))) + "</title>",
                out[pid],
                count=1,
                flags=re.S,
            )
        return out

    # ------------------------------------------------------------------
    # version facts

    def toolchain(self) -> str:
        return self.lean.git.show("lean-toolchain").strip()

    def mathlib_rev(self) -> str:
        m = json.loads(self.lean.git.show("lake-manifest.json"))
        return next(p["rev"] for p in m["packages"] if p["name"] == "mathlib")

    def authors_text(self) -> str:
        return "N. Ross"
