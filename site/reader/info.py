"""Overview-level pages: paper contents, progress/status, methodology, credits, contribute, errata.

A mixin for `render.Site`. Every count is derived from the full 122-environment
inventory (`docs/source-inventory.json`) combined with the critic ledger
(`docs/COVERAGE.md`) at build time; every version fact (commit, Lean toolchain,
Mathlib revision, source hashes) is read from the pinned git commit.
"""

from __future__ import annotations

import html
import re

from .lean import MARKERS, STATUS_LABELS

ARXIV = "https://arxiv.org/abs/1109.1880v1"
TITLE = "Fundamentals of Stein's method"
MAINTAINER = "aaradhyapandeycs"
MAINTAINER_URL = "https://github.com/aaradhyapandeycs"
REPO = "https://github.com/aaradhyapandeycs/steins-method-lean"


def esc(t: str) -> str:
    return html.escape(str(t), quote=False)


def attr(t: str) -> str:
    return html.escape(str(t), quote=True)


class InfoPages:
    # ------------------------------------------------------------------
    # Table of contents / paper landing
    # ------------------------------------------------------------------

    def book_landing_page(self) -> str:
        sections, cur = [], None
        for p in self.pages:
            if p.level == 0:
                cur = {"page": p, "subsections": []}
                sections.append(cur)
            elif cur:
                cur["subsections"].append(p)

        items = []
        for sec in sections:
            p = sec["page"]
            sec_no = getattr(p, "section", None) or ""
            summary = self.section_count_summary(sec_no)
            c_text = f'<span class="ch-count">{esc(summary)}</span>' if summary else ""

            subs = "".join(
                f'<li><a href="{s.id}.html"><span class="secnum">{esc(s.number or "")}</span> {s.title}</a></li>'
                for s in sec["subsections"]
            )
            items.append(
                f'<li><h2><a href="{p.id}.html"><span class="secnum">{esc(p.number or "")}</span> {p.title}</a></h2>'
                f'{c_text}{"<ol class=sections>" + subs + "</ol>" if subs else ""}</li>'
            )

        body = f"""<h1>The Paper</h1>
<p class="lede"><em>{TITLE}</em>, by N. Ross (<a href="{ARXIV}">arXiv:1109.1880v1</a>,
<em>Probability Surveys</em> 8 (2011) 210–293, <a href="https://doi.org/10.1214/11-PS182">DOI 10.1214/11-PS182</a>),
rendered from the pinned arXiv TeX source with Ross's numbering and notation.
Counts after each section report formalized results out of the full section inventory in
<code>docs/source-inventory.json</code>, accepted in <code>docs/COVERAGE.md</code>.</p>
<ol class="book-toc">{''.join(items)}
<li><h2><a href="acknowledgements.html">Acknowledgements</a></h2></li>
<li><h2><a href="references.html">References</a></h2></li></ol>"""
        return self.shell(f"Paper · {TITLE}", body, "book", toc=False)

    # ------------------------------------------------------------------
    # Progress / Status dashboard
    # ------------------------------------------------------------------

    def status_page(self) -> str:
        counts = self.coverage_counts()
        num = counts["numbered"]
        pr = counts["prose"]
        mk = counts["markers"]
        by_sec = counts["by_section"]
        prose_by_sec = counts["prose_by_section"]
        rev = self.lean.git.rev

        sec_pages = [p for p in self.pages if p.level == 0]
        trs = []
        for p in sec_pages:
            sec_no = getattr(p, "section", None) or ""
            sc = by_sec.get(sec_no, {})
            trs.append(
                f'<tr><td><a href="{p.id}.html">Section {esc(sec_no)}</a></td>'
                f'<td>{p.title}</td>'
                f'<td class="num">{self.cnt_tag(f"by_section.{sec_no}.total", sc.get("total", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"by_section.{sec_no}.formalized", sc.get("formalized", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"by_section.{sec_no}.proved", sc.get("proved", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"by_section.{sec_no}.defined", sc.get("defined", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"by_section.{sec_no}.corrected", sc.get("corrected", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"by_section.{sec_no}.restricted", sc.get("restricted", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"by_section.{sec_no}.open", sc.get("open", 0))}</td></tr>'
            )

        trs.append(
            f'<tr class="ch-row"><th colspan="2">All sections (numbered inventory)</th>'
            f'<td class="num"><strong>{self.cnt_tag("numbered.total", num["total"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("numbered.formalized", num["formalized"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("numbered.proved", num["proved"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("numbered.defined", num["defined"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("numbered.corrected", num["corrected"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("numbered.restricted", num["restricted"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("numbered.open", num["open"])}</strong></td></tr>'
        )

        prose_trs = []
        for p in sec_pages:
            sec_no = getattr(p, "section", None) or ""
            psc = prose_by_sec.get(sec_no, {})
            if not psc.get("total", 0):
                continue
            prose_trs.append(
                f'<tr><td><a href="{p.id}.html">Section {esc(sec_no)}</a></td>'
                f'<td class="num">{self.cnt_tag(f"prose_by_section.{sec_no}.total", psc.get("total", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"prose_by_section.{sec_no}.proved", psc.get("proved", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"prose_by_section.{sec_no}.corrected", psc.get("corrected", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"prose_by_section.{sec_no}.restricted", psc.get("restricted", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"prose_by_section.{sec_no}.source-issue", psc.get("source-issue", 0))}</td>'
                f'<td class="num">{self.cnt_tag(f"prose_by_section.{sec_no}.open", psc.get("open", 0))}</td></tr>'
            )
        prose_trs.append(
            f'<tr class="ch-row"><th>Tracked running-text &amp; display total</th>'
            f'<td class="num"><strong>{self.cnt_tag("prose.total", pr["total"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("prose.proved", pr["proved"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("prose.corrected", pr["corrected"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("prose.restricted", pr["restricted"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("prose.source-issue", pr["source-issue"])}</strong></td>'
            f'<td class="num"><strong>{self.cnt_tag("prose.open", pr["open"])}</strong></td></tr>'
        )

        wip_note = ""
        if num.get("wip", 0) or pr.get("wip_untracked", 0):
            wip_note = (
                f' Of the {num["open"]} open numbered results, '
                f'{self.cnt_tag("numbered.wip", num["wip"])} currently have compiled Lean work in progress '
                f'awaiting critic review.'
            )

        body = f"""<h1>Progress</h1>
<div class="incomplete" role="note"><strong>Work in progress.</strong> The paper is not yet fully formalized.
Progress is measured over all <strong>{self.cnt_tag("numbered.total", num["total"])} numbered environments</strong>
in <code>docs/source-inventory.json</code> together with the running-text and display claims tracked in
<code>docs/COVERAGE.md</code> at commit <code>{rev[:10]}</code>.
Reviews were conducted by independent AI critic agents under the maintainer's direction (no author endorsement,
no human referee). Every inventory item without an accepted <code>COVERAGE.md</code> record is counted as
<strong>open</strong>—even when unreviewed Lean statements already compile.{wip_note}</div>
<p class="lede">{self.count_sentence()}</p>
{self.stacked_bar()}

<div class="dash">
  <div class="tile">
    <div class="big">{self.cnt_tag("numbered.formalized", num["formalized"])} <span>/ {self.cnt_tag("numbered.total", num["total"])}</span></div>
    <div>Numbered environments formalized ({self.cnt_tag("numbered.proved", num["proved"])} proved as printed,
    {self.cnt_tag("numbered.defined", num["defined"])} defined,
    {self.cnt_tag("numbered.modified", num["modified"])} corrected or restricted)</div>
  </div>
  <div class="tile">
    <div class="big">{self.cnt_tag("numbered.open", num["open"])}</div>
    <div>Open numbered environments ({self.cnt_tag("numbered.exercise", num["exercise"])} marked exercise)</div>
  </div>
  <div class="tile">
    <div class="big">{self.cnt_tag("prose.formalized", pr["formalized"])} <span>/ {self.cnt_tag("prose.total", pr["total"])}</span></div>
    <div>Tracked prose &amp; display claims formalized ({self.cnt_tag("prose.source-issue", pr["source-issue"])} source issue,
    {self.cnt_tag("prose.open", pr["open"])} open)</div>
  </div>
  <div class="tile">
    <div class="big">{self.cnt_tag("markers.refuted", mk["refuted"])}</div>
    <div>Items with a machine-checked Lean refutation or counterexample</div>
  </div>
</div>

<h2>By Section (All {num["total"]} Numbered Environments)</h2>
<div class="table-wrap"><table class="results dash-table">
<thead>
<tr>
  <th>Section</th><th>Title</th><th>Inventory</th><th>Formalized</th>
  <th><span class="status st-proved">proved</span></th>
  <th><span class="status st-defined">defined</span></th>
  <th><span class="status st-corrected">corrected</span></th>
  <th><span class="status st-restricted">restricted</span></th>
  <th><span class="status st-open">open</span></th>
</tr>
</thead>
<tbody>
{''.join(trs)}
</tbody>
</table></div>

<h2>Tracked Running-Text &amp; Display Claims</h2>
<div class="table-wrap"><table class="results dash-table">
<thead>
<tr>
  <th>Section</th><th>Tracked</th>
  <th><span class="status st-proved">proved</span></th>
  <th><span class="status st-corrected">corrected</span></th>
  <th><span class="status st-restricted">restricted</span></th>
  <th><span class="status st-source-issue">source issue</span></th>
  <th><span class="status st-open">open</span></th>
</tr>
</thead>
<tbody>
{''.join(prose_trs)}
</tbody>
</table></div>

<h2>Status Vocabulary and Markers</h2>
<ul>
  <li><span class="status st-proved">proved</span>: the printed item, formalized and accepted in <code>docs/COVERAGE.md</code> under its natural reading.</li>
  <li><span class="status st-defined">defined</span>: a numbered definition environment formalized in <code>Formalization/Defs/</code> and accepted in <code>docs/COVERAGE.md</code>.</li>
  <li><span class="status st-corrected">corrected</span>: a disclosed repair recorded with rationale (and counterexample where feasible) in <a href="errata.html">Source issues</a>.</li>
  <li><span class="status st-restricted">restricted</span>: proved under a disclosed domain or non-degeneracy hypothesis (e.g. positive mean or variance).</li>
  <li><span class="status st-source-issue">source issue</span>: a printed claim in the source that fails as stated and has no accepted repaired theorem yet (e.g. anti-voter irreducibility on the full state space, refuted in Lean).</li>
  <li><span class="status st-open">open</span>: every inventory item not yet accepted in <code>docs/COVERAGE.md</code> (including unreviewed Lean work in progress and exercises).</li>
  <li><span class="marker mk-refuted">{esc(MARKERS["refuted"])}</span>: accompanied by a machine-checked Lean refutation or counterexample to the printed statement.</li>
  <li><span class="marker mk-exercise">{esc(MARKERS["exercise"])}</span>: left as an exercise or unworked remark in the source.</li>
</ul>

<h2>Snapshot</h2>
<p class="snapshot">{self.snapshot_line()}</p>"""
        return self.shell(f"Progress · {TITLE}", body, "status", toc=False)

    # ------------------------------------------------------------------
    # Methodology
    # ------------------------------------------------------------------

    def methodology_page(self) -> str:
        rev = self.lean.git.rev
        prov = self.book.provenance
        tar = prov.get("artifacts", {}).get("1109.1880v1.tar", "")
        pdf = prov.get("artifacts", {}).get("1109.1880v1.pdf", "")

        ci = (
            f'<p>This build was generated by the GitHub Pages workflow after the Lean checks '
            f'succeeded on this commit: <a href="{attr(self.ci_run_url)}">CI run</a>.</p>'
            if self.ci_run_url
            else f'<p>This build was generated locally or via manual dispatch. The Lean CI status of this commit is at '
            f'<a href="{REPO}/commit/{rev}">its GitHub commit page</a>.</p>'
        )

        body = f"""<h1>Methodology and Verification</h1>
<nav class="page-toc"><a href="#sources">Sources and scope</a> · <a href="#formalized">Formalization architecture</a> ·
<a href="#review">Review process</a> · <a href="#verify">Verification snapshot</a> · <a href="#establishes">Axioms and guarantees</a> ·
<a href="#reproduce">Reproduce</a></nav>

<h2 id="sources">Sources and Scope</h2>
<p>The formalized source is the pinned arXiv e-print of Nathan Ross, <em>{TITLE}</em>
(<a href="{ARXIV}">arXiv:1109.1880v1</a>, <em>Probability Surveys</em> 8 (2011) 210–293,
<a href="https://doi.org/10.1214/11-PS182">DOI 10.1214/11-PS182</a>).
Source files are restored and hash-verified at build time:
source archive SHA-256 <code>{esc(tar)}</code>,
PDF SHA-256 <code>{esc(pdf)}</code> (recorded in <code>source/provenance.json</code>).
Numbering and labels follow <code>docs/source-inventory.json</code> (122 numbered environments across Sections 1–7).</p>

<h2 id="formalized">Formalization Architecture</h2>
<p>To prevent definition drift and ensure mathematical transparency, every proved result receives:</p>
<ol>
  <li>A self-contained <code>Prop</code> in <code>Formalization/Statements/SecN.lean</code> importing definitions only, stating all hypotheses explicitly and referencing the TeX lines and labels.</li>
  <li>A proof wrapper in <code>Formalization/Statements/SecNProofs.lean</code> establishing <code>theorem &lt;Name&gt;_holds : &lt;Name&gt;</code> by applying the underlying library theorem from <code>Formalization/</code>.</li>
  <li>Corrected or restricted statements carry an explicit <code>_corrected</code> or <code>_restricted</code> suffix and cite an entry in <a href="errata.html"><code>docs/SOURCE-ISSUES.md</code></a>. Where feasible, a machine-checked Lean refutation of the printed claim is proved alongside the repair.</li>
</ol>

<h2 id="review">Review Process</h2>
<p>Work is organized into independent parallel tracks. Builder agents formalize statements and proofs;
an independent critic agent reviews each statement against the source mathematics, checks fidelity,
runs counterexamples and mutation tests, and records accepted results in <code>docs/COVERAGE.md</code>.
A builder never certifies its own statement and never edits the coverage ledger.</p>

<h2 id="verify">Verification Snapshot</h2>
<table class="facts"><tbody>
<tr><th>Repository</th><td><a href="{REPO}">{esc(REPO.split("//", 1)[1])}</a></td></tr>
<tr><th>Commit</th><td><a href="{REPO}/tree/{rev}"><code>{rev}</code></a></td></tr>
<tr><th>Lean toolchain</th><td><code>{esc(self.toolchain())}</code></td></tr>
<tr><th>Mathlib revision</th><td><a href="https://github.com/leanprover-community/mathlib4/tree/{attr(self.mathlib_rev())}"><code>{esc(self.mathlib_rev()[:12])}</code></a></td></tr>
<tr><th>Source PDF SHA-256</th><td><code>{esc(pdf)}</code></td></tr>
<tr><th>Built</th><td>{esc(self.built)}</td></tr>
</tbody></table>
{ci}

<h2 id="establishes">Axioms and Guarantees</h2>
<p>Every exported theorem is checked by the Lean 4 kernel. The project enforces strict axiom hygiene:
only the standard Lean foundation (<code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>) is permitted.
No <code>sorry</code>, <code>admit</code>, custom axioms, or <code>native_decide</code> are allowed in any declaration;
this is machine-verified by <a href="{attr(self.lean.git.blob('Audit.lean'))}"><code>Audit.lean</code></a>.</p>

<h2 id="reproduce">Reproduce Locally</h2>
<pre class="cite">git clone {REPO}.git
cd steins-method-lean
git checkout {rev}
python3 scripts/fetch_source.py       # restore and hash-check the arXiv source
lake exe cache get                    # prebuilt Mathlib cache
lake build                            # build Lean formalization
lake env lean Audit.lean              # transitive axiom check
python3 scripts/check.py              # automated project check
python3 site/build.py                 # build this reader website
python3 site/check_fidelity.py        # fidelity and macro check</pre>"""
        return self.shell(f"Methodology · {TITLE}", body, "methodology", toc=False)

    # ------------------------------------------------------------------
    # Credits
    # ------------------------------------------------------------------

    def credits_page(self) -> str:
        body = f"""<h1>Credits and Citation</h1>

<h2>The Paper</h2>
<p>N. Ross, <em>{TITLE}</em>, <em>Probability Surveys</em> 8 (2011) 210–293,
<a href="https://doi.org/10.1214/11-PS182">DOI 10.1214/11-PS182</a>,
<a href="{ARXIV}">arXiv:1109.1880v1</a>.</p>
<p>The paper text is licensed under <a href="https://creativecommons.org/licenses/by/4.0/">CC BY 4.0</a>.
Text rendered unofficially from arXiv:1109.1880v1; it may differ from the published journal version.
The author of the paper has not reviewed and does not endorse this formalization.</p>

<h2>The Lean Formalization</h2>
<ul>
  <li><strong>Maintainer:</strong> <a href="{MAINTAINER_URL}">{MAINTAINER}</a> on GitHub.</li>
  <li><strong>AI Assistance:</strong> Lean 4 formalization, statement indexing, independent critic reviews, and reader website produced with AI builder and critic agents under the maintainer's direction.</li>
  <li><strong>Code License:</strong> Apache-2.0.</li>
</ul>

<h2>Tools and Community</h2>
<ul>
  <li><a href="https://lean-lang.org/">Lean 4</a> (<code>{esc(self.toolchain())}</code>) and <a href="https://github.com/leanprover-community/mathlib4">Mathlib</a>.</li>
  <li><a href="https://www.mathjax.org/">MathJax 3.2.2</a> for client-side formula rendering.</li>
  <li>Website design and architecture adapted from the <a href="https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean">Statistical Foundations of RL</a> reader.</li>
</ul>

<h2 id="cite">How to Cite</h2>
<p>To cite the paper:</p>
<pre class="cite">{esc(self.bibtex_book())}</pre>

<p>To cite this formalization (cite the commit hash used):</p>
<pre class="cite">{esc(self.bibtex_repo())}</pre>"""
        return self.shell(f"Credits · {TITLE}", body, "credits", toc=False)

    # ------------------------------------------------------------------
    # Contribute
    # ------------------------------------------------------------------

    def contribute_page(self) -> str:
        body = f"""<h1>Contribute</h1>
<p class="lede">Reader corrections, bug reports, and mathematical critiques are welcomed.</p>

<h2>Reporting an Issue</h2>
<p>Open an issue at <a href="{REPO}/issues">{esc(REPO.split("//", 1)[1])}/issues</a> with:</p>
<ul>
  <li>The source result (number and label, e.g. Theorem 3.5, <code>\\label{{thm41}}</code>) and TeX lines.</li>
  <li>The Lean statement name (e.g. <code>Thm3_5_corrected</code>) and the commit hash.</li>
  <li>What appears incorrect or imprecise, and the suggested repair.</li>
</ul>

<h2>Repository Guidelines</h2>
<ul>
  <li>Zero-sorry policy: only sound proofs without admissions or custom axioms.</li>
  <li>Fidelity: no silent modification of hypotheses or weakening of conclusions. Any departure must be recorded in <code>docs/SOURCE-ISSUES.md</code> and named with <code>_corrected</code> or <code>_restricted</code>.</li>
  <li>Statements and proof wrappers: every result gets a <code>Prop</code> in <code>SecN.lean</code> and a <code>_holds</code> proof in <code>SecNProofs.lean</code>.</li>
</ul>"""
        return self.shell(f"Contribute · {TITLE}", body, "contribute", toc=False)

    # ------------------------------------------------------------------
    # About
    # ------------------------------------------------------------------

    def about_page(self) -> str:
        body = f"""<h1>About This Project</h1>
<p>This reader presents an interactive view of Nathan Ross's <em>Fundamentals of Stein's method</em>
alongside a machine-checked Lean 4 formalization.</p>
<ul>
  <li><a href="status.html">Progress &amp; status</a></li>
  <li><a href="methodology.html">Methodology &amp; verification</a></li>
  <li><a href="errata.html">Source issues &amp; errata</a></li>
  <li><a href="credits.html">Credits &amp; citations</a></li>
</ul>"""
        return self.shell(f"About · {TITLE}", body, "about", toc=False)

    # ------------------------------------------------------------------
    # Acknowledgements
    # ------------------------------------------------------------------

    def ack_page(self) -> str:
        back_html = "".join(getattr(b, "html", "") for b in self.back)
        body = f"""<h1>Acknowledgements</h1>
<p>We thank Nathan Ross for his clear, foundational exposition in <em>Fundamentals of Stein's method</em>
and the Institute of Mathematical Statistics for publishing <em>Probability Surveys</em> under open-access CC BY 4.0 licensing.</p>
<p>We also gratefully acknowledge the Lean 4 and Mathlib developer community for providing the interactive theorem proving infrastructure.</p>
{back_html}"""
        return self.shell(f"Acknowledgements · {TITLE}", body, "acknowledgements", toc=False)

    # ------------------------------------------------------------------
    # Errata / Source issues
    # ------------------------------------------------------------------

    def errata_page(self) -> str:
        rev = self.lean.git.rev
        issues_list = []
        for iss_id, info in sorted(self.lean.issue_slugs.items()):
            title = info["title"]
            title = re.sub(r"\\(?:label|ref|eqref)\{([^}]+)\}", r"(\1)", title)
            title_html = self.lean.md(title)
            issues_list.append(
                f'<li><a href="{attr(self.lean.git.blob("docs/SOURCE-ISSUES.md"))}#{attr(info["slug"])}">'
                f'<strong>{esc(iss_id)}</strong></a>: <span class="tex2jax_process">{title_html}</span></li>'
            )

        body = f"""<h1>Source Issues and Deviations</h1>
<p class="lede">Every departure from the printed paper is documented in
<a href="{attr(self.lean.git.blob("docs/SOURCE-ISSUES.md"))}"><code>docs/SOURCE-ISSUES.md</code></a>
and summarized in <a href="{attr(self.lean.git.blob("docs/ERRATA-AND-DEVIATIONS.md"))}"><code>docs/ERRATA-AND-DEVIATIONS.md</code></a>.
When a printed statement is false or underspecified, the repository records the issue (and a counterexample where feasible) and
proves a <code>_corrected</code> or <code>_restricted</code> variant instead of modifying the source claim silently.</p>

<h2>Catalogued Issues ({len(self.lean.issue_slugs)})</h2>
<ul>
{''.join(issues_list) or "<li>None recorded.</li>"}
</ul>

<p>See the full ledger at commit <code>{rev[:10]}</code>: <a href="{attr(self.lean.git.blob("docs/SOURCE-ISSUES.md"))}">docs/SOURCE-ISSUES.md</a>.</p>"""
        return self.shell(f"Source Issues · {TITLE}", body, "errata", toc=False)

    # ------------------------------------------------------------------
    # BibTeX helpers
    # ------------------------------------------------------------------

    def bibtex_book(self) -> str:
        return """@article{ross2011fundamentals,
  title={Fundamentals of Stein's method},
  author={Ross, Nathan},
  journal={Probability Surveys},
  volume={8},
  pages={210--293},
  year={2011},
  doi={10.1214/11-PS182}
}"""

    def bibtex_repo(self) -> str:
        rev = self.lean.git.rev
        return f"""@misc{{steins-method-lean,
  title={{Fundamentals of Stein's method in Lean 4}},
  author={{Pandey, Aaradhya}},
  year={{2026}},
  howpublished={{\\url{{{REPO}}}}},
  note={{Commit {rev[:10]}; work in progress}}
}}"""
