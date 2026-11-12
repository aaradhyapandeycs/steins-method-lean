#!/usr/bin/env python3
"""Build the book-alongside-Lean reader into site/_build/.

    python3 scripts/fetch_source.py      # restore and verify the pinned arXiv TeX
    python3 site/build.py                # build from the pushed commit (origin/main)
    python3 site/build.py --rev HEAD     # or from another committed revision

Reads, never writes, project files. Lean files and ledgers are read with
`git show <rev>:<path>`, so uncommitted work is never shown and every Lean
link points at a commit that exists on GitHub. No Lean or Lake process runs.
"""

from __future__ import annotations

import argparse
import html
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

from reader.book import Book  # noqa: E402
from reader.lean import REPO, Git, LeanIndex  # noqa: E402
from reader.links import repo_link_problems  # noqa: E402
from reader.render import Site  # noqa: E402
from reader.depgraph import (DepGraph, GraphPage, LeanDeps, LEAN_DEPS_PATH, REVIEW_PATH,  # noqa: E402
                              connections_html, declarations_page, selected_results_html)
import json  # noqa: E402


def default_rev(repo: Path) -> str:
    r = subprocess.run(["git", "-C", str(repo), "rev-parse", "--abbrev-ref", "@{upstream}"],
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else "HEAD"


COUNT_RE = re.compile(r'<span class="n" data-count="([^"]+)">([^<]*)</span>')


def check_counts(pages: dict, data: dict) -> list:
    """Every count shown is tagged with its summary path; each must equal nodes.json's summary.
    Returns the problems."""
    s = data.get("summary", {})
    problems = []
    # Walk any count tags and verify them against summary data
    seen = 0
    for pid, text in pages.items():
        for path, shown in COUNT_RE.findall(text):
            seen += 1
            v = s
            try:
                for k in html.unescape(path).split("."):
                    v = v[k]
            except (KeyError, TypeError):
                problems.append(f"{pid}.html: count path {path} is not in the summary")
                continue
            if str(v) != shown:
                problems.append(f"{pid}.html: {path} shows {shown}, summary has {v}")
    # Only warn if there are count tags but nothing matched — an empty site may have no tags at all.
    return problems


def pinned_commit_warning(repo: Path, rev: str) -> str | None:
    """Best effort, no network: warn when the pinned commit is on no remote-tracking branch, so its GitHub
    links would 404 until it is pushed. Silent when the repository has no remote or git fails."""
    def git(*a):
        r = subprocess.run(["git", "-C", str(repo), *a], capture_output=True, text=True)
        return r.stdout.strip() if r.returncode == 0 else None
    remotes = git("remote")
    if not remotes:
        return None
    contains = git("branch", "-r", "--contains", rev)
    if contains is None or contains:
        return None
    return (f"WARNING: the pinned commit {rev[:12]} is not on any remote-tracking branch of "
            f"{', '.join(remotes.split())} (as of the last fetch). Every pinned GitHub link and the CI-status link "
            f"will return 404 until this commit is pushed; publish only a build of a pushed commit.")


def incomplete_banner_check(pages: dict) -> list:
    """Check that incomplete sections carry a visible banner so readers know the
    formalization is in progress. Returns a list of warning strings (not fatal)."""
    warnings = []
    for pid, text in pages.items():
        if re.search(r'sec\d+', pid) and "incomplete" not in text.lower() and "in progress" not in text.lower():
            warnings.append(f"{pid}.html: no incomplete/in-progress banner found")
    return warnings


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rev", default=None, help="git revision for Lean files and ledgers (default: upstream branch)")
    ap.add_argument("--out", default=str(HERE / "_build"), help="output directory")
    ap.add_argument("--lean-repo", default=str(ROOT),
                    help="git repository to read Lean files and ledgers from (default: this checkout); "
                         "any clone of the project works, e.g. when local git objects are unavailable")
    ap.add_argument("--ci-run-url", default=None,
                    help="URL of the Lean CI run that gated this deploy (pages.yml passes it); omit for local builds")
    ap.add_argument("--audit-log", default=None,
                    help="file with the CI axiom-audit output; its 'Axiom audit passed ...' line is shown verbatim")
    args = ap.parse_args()

    final = Path(args.out).resolve()
    if final.exists() and not (final / ".stein-reader").exists():
        raise SystemExit(f"{final} exists and was not made by this builder; refusing to replace it")
    # Build next to the target and swap at the end, so a failed or interrupted
    # build never leaves the served site empty.
    out = final.with_name(final.name + ".new")
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    (out / ".stein-reader").write_text("generated by site/build.py\n")

    book = Book(ROOT, out)
    lean_repo = Path(args.lean_repo).resolve()
    git = Git(lean_repo, args.rev or default_rev(lean_repo))
    labels = {l["label"] for l in book.inventory["labels"]}
    lean = LeanIndex(git, labels)

    front, sections, back = book.convert_all()
    pages = book.paginate(sections)
    audit_line = None
    if args.audit_log:
        audit_line = next((l.strip() for l in Path(args.audit_log).read_text().splitlines()
                           if "Axiom audit passed for" in l), None)
        if audit_line is None:
            raise SystemExit(f"{args.audit_log}: no 'Axiom audit passed for' line")
    site = Site(book, lean, pages, front, back, ci_run_url=args.ci_run_url, audit_line=audit_line)
    bad = site.placement_problems()
    if bad:
        raise SystemExit("Lean cards not at their ledger item:\n  " + "\n  ".join(bad))

    # Dependency data: curated (TeX cross-references, critic-reviewed) and extracted from the compiled
    # Lean proofs (docs/graph/lean-deps.json). Both are read from the reader's Lean revision.
    def committed_json(path):
        try:
            return json.loads(git.show(path))
        except Exception:
            return None
    review = (committed_json(REVIEW_PATH) or {}).get("edges", {})
    graph = DepGraph((book.tex_root / "SteinIntro_utf8.tex").read_text(encoding="utf-8"), lean.numbered_items, review)
    ldeps = LeanDeps(committed_json(LEAN_DEPS_PATH), lean.numbered_items)
    lean.connections = {e.name: connections_html(e.name, graph, ldeps, lean.lib_decls, git.blob) for e in lean.entries}
    depgraph = GraphPage(site, graph, ldeps)

    html_pages = site.book_pages()
    html_pages["acknowledgements"] = site.ack_page()
    site.index_anchors(html_pages)  # anchors of book items, for links from the overview pages
    site.selected_html = selected_results_html(site, graph)
    html_pages["index"] = site.index_page()
    html_pages["results"] = site.results_page()
    html_pages["book"] = site.book_landing_page()
    html_pages["status"] = site.status_page()
    html_pages["methodology"] = site.methodology_page()
    html_pages["credits"] = site.credits_page()
    html_pages["contribute"] = site.contribute_page()
    html_pages["about"] = site.about_page()
    html_pages["errata"] = site.errata_page()
    html_pages["graph"] = depgraph.page()
    html_pages["declarations"] = declarations_page(site, ldeps, graph)
    html_pages["references"] = site.references_page()  # last: citations are collected above
    html_pages = site.resolve(html_pages)

    def resolve_links(text):
        def item(m):
            h = site.item_href(graph.by_id[m.group(1)]) if m.group(1) in graph.by_id else None
            return f'<a href="{h}">{m.group(2)}</a>' if h else m.group(2)

        def leanref(m):
            pid = site.where.get(f"lean-{m.group(1)}")
            return (f'<a href="{pid}.html#lean-{m.group(1)}"><code>{m.group(1)}</code></a>' if pid
                    else f'<code>{m.group(1)}</code>')
        text = re.sub(r"@@ITEM\|([^|@]+)\|([^@]+)@@", item, text)
        return re.sub(r"@@LEAN\|([^@]+)@@", leanref, text)
    html_pages = {k: resolve_links(v) for k, v in html_pages.items()}

    problems = check_counts(html_pages, getattr(site, "data", {}))
    if problems:
        raise SystemExit("counts on the site disagree with the summary:\n  " + "\n  ".join(problems[:40]))

    if site.missing_refs:
        sample = ", ".join(f"{k} ({v})" for k, v in list(site.missing_refs.items())[:20])
        raise SystemExit(f"unresolved \\ref/\\eqref labels ({len(site.missing_refs)}): {sample}")

    if site.unplaced:
        raise SystemExit(
            f"unplaced statement entries ({len(site.unplaced)}): "
            + ", ".join(e.name for e in site.unplaced)
        )

    # Strict check for unresolved '??' references or raw .bbl citation keys in rendered paper HTML
    bib_keys = set(getattr(book, "bib", {}).keys())
    bbl_path = ROOT / "docs/source/SteinIntro.bbl"
    if bbl_path.is_file():
        bib_keys |= {
            m.group(1).strip()
            for m in re.finditer(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}", bbl_path.read_text(encoding="utf-8", errors="replace"))
        }
    ref_cite_problems = []
    for pid, text in html_pages.items():
        # Strip verbatim TeX/Lean blocks and script tags before scanning visible text
        cleaned = re.sub(r"<details class=\"tex-src\">.*?</details>", "", text, flags=re.S)
        cleaned = re.sub(r"<pre\b[^>]*>.*?</pre>", "", cleaned, flags=re.S)
        cleaned = re.sub(r"<script\b[^>]*>.*?</script>", "", cleaned, flags=re.S)
        if "??" in re.sub(r"<[^>]+>", " ", cleaned):
            ref_cite_problems.append(f"{pid}.html: contains unresolved '??' reference")
        for cm in re.finditer(r'<a\s+class="cite"[^>]*>(.*?)</a>', cleaned, flags=re.S):
            cite_vis = html.unescape(re.sub(r"<[^>]+>", "", cm.group(1))).strip()
            for bk in bib_keys:
                if re.search(rf"\b{re.escape(bk)}\b", cite_vis):
                    ref_cite_problems.append(f"{pid}.html: raw citation key '{bk}' in citation '{cite_vis}'")
                    break
        for bm in re.finditer(r'<div class="book-col">(.*?)</div>\s*<aside', cleaned, flags=re.S):
            vis = html.unescape(re.sub(r"<[^>]+>", " ", bm.group(1)))
            if "\\cite" in vis or "@@REF|" in vis:
                ref_cite_problems.append(f"{pid}.html: unexpanded \\cite or @@REF placeholder in paper text")
            for bk in bib_keys:
                if re.search(rf"\b{re.escape(bk)}\b", vis):
                    ref_cite_problems.append(f"{pid}.html: raw citation key '{bk}' in paper text")
                    break
    if ref_cite_problems:
        raise SystemExit(
            "unresolved references or raw citation keys in rendered HTML:\n  "
            + "\n  ".join(ref_cite_problems[:40])
        )

    tracked_files = set(git.ls("."))
    local_files = tracked_files | {p.relative_to(ROOT).as_posix() for p in ROOT.glob("docs/*.md")}

    def read_blob(path: str) -> str:
        try:
            return git.show(path)
        except Exception:
            p = ROOT / path
            if p.is_file():
                return p.read_text(encoding="utf-8")
            raise

    link_problems = repo_link_problems(html_pages, REPO, git.rev, local_files, read_blob)
    if link_problems:
        raise SystemExit("links into the repository with no target at the pinned commit:\n  "
                         + "\n  ".join(link_problems[:60]))

    for pid, text in html_pages.items():
        (out / f"{pid}.html").write_text(text)
    assets = out / "assets"
    assets.mkdir(exist_ok=True)
    for f in (HERE / "static").iterdir():
        shutil.copyfile(f, assets / f.name)
    (assets / "mathjax-config.js").write_text(site.mathjax_config())
    (out / "results.json").write_text(site.search_data())
    (out / ".nojekyll").write_text("")
    (out / "graph").mkdir(exist_ok=True)
    (out / "graph" / "nodes.json").write_text(depgraph.nodes_json())
    (out / "graph" / "graph.dot").write_text(depgraph.dot())

    old = final.with_name(final.name + ".old")
    if old.exists():
        shutil.rmtree(old)
    if final.exists():
        final.rename(old)
    out.rename(final)
    if old.exists():
        shutil.rmtree(old)
    out = final

    # Incomplete-banner check (advisory, not fatal)
    banner_warns = incomplete_banner_check(html_pages)
    for w in banner_warns[:10]:
        print("banner-check: " + w)

    placed = len(lean.entries) - len(site.unplaced)
    print(f"Lean commit {git.rev}")
    warn = pinned_commit_warning(lean_repo, git.rev)
    if warn:
        print(warn)
    print(f"{len(html_pages)} pages, {len(pages)} sections, {len(book.images)} figures")
    print(f"{len(lean.entries)} statement entries, {placed} placed next to book text, {len(site.unplaced)} unplaced")
    if site.unplaced:
        print("  unplaced: " + ", ".join(e.name for e in site.unplaced))
    if book.unknown:
        top = sorted(book.unknown.items(), key=lambda x: -x[1])[:40]
        print("unhandled TeX commands (count): " + ", ".join(f"{k}={v}" for k, v in top))
    if site.missing_refs:
        print(f"unresolved references: {len(site.missing_refs)} labels, e.g. " + ", ".join(list(site.missing_refs)[:10]))
    for w in book.warnings[:40]:
        print("warning: " + w)
    if len(book.warnings) > 40:
        print(f"... {len(book.warnings) - 40} more warnings")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
