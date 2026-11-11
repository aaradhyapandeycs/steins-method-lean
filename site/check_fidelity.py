#!/usr/bin/env python3
"""Check that the built site reproduces the paper faithfully.

    python3 site/check_fidelity.py [--build site/_build]

Three independent checks, none using the site's own converter:

1. Section headings: every \\section{...} heading in the TeX must appear
   somewhere in the site HTML (case-insensitive, stripped).
2. Source-file hygiene: no .tex, .cls, or .sty file appears inside
   site/_build/, and no local filesystem path leaks into the HTML.
3. Macros (site/check_macros.py): no raw TeX control sequence outside typeset
   math, and every macro inside math defined by the page's MathJax
   configuration or by MathJax itself.

PDF hash is verified against source/provenance.json
(field artifacts["1109.1880v1.pdf"]).

Exit status 1 if anything is unresolved.
"""

from __future__ import annotations

import argparse
import glob
import hashlib
import html
import json
import os
import re
import sys
import unicodedata
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PDF = ROOT / "source/upstream/1109.1880v1.pdf"
TEX = ROOT / "docs/source/SteinIntro_utf8.tex"
PROVENANCE = ROOT / "source/provenance.json"

# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def letters(t: str) -> str:
    return re.sub(r"[^a-z]", "", unicodedata.normalize("NFKC", t).lower())


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------------------
# 1. Section heading check
# ---------------------------------------------------------------------------

def tex_section_headings() -> list[str]:
    """Extract \\section{...} titles from the TeX source (not commented)."""
    text = TEX.read_text(encoding="utf-8", errors="replace")
    text = re.sub(r"(?<!\\)%[^\n]*", "", text)  # strip comments
    headings = []
    for m in re.finditer(r"\\section\s*\{([^}]+)\}", text):
        raw = m.group(1).strip()
        # strip simple TeX formatting for comparison
        clean = re.sub(r"\\[A-Za-z]+\s*", "", raw)
        clean = re.sub(r"[{}]", "", clean).strip()
        if clean:
            headings.append(clean)
    return headings


def site_all_text(build: Path) -> str:
    """Concatenate the stripped text of all built HTML pages."""
    parts = []
    for f in sorted(glob.glob(str(build / "*.html"))):
        raw = Path(f).read_text(errors="replace")
        raw = re.sub(r"<[^>]+>", " ", raw)
        parts.append(html.unescape(raw))
    return " ".join(parts).lower()


def check_section_headings(build: Path) -> list[str]:
    """Return problems: headings from the TeX missing from the site."""
    headings = tex_section_headings()
    site_text = site_all_text(build)
    problems = []
    for h in headings:
        if h.lower() not in site_text:
            problems.append(f"section heading not found in site HTML: {h!r}")
    return problems


# ---------------------------------------------------------------------------
# 2. Hygiene checks
# ---------------------------------------------------------------------------

def check_hygiene(build: Path) -> list[str]:
    """No .tex/.cls/.sty files in _build/; no local path leaks in HTML."""
    problems = []
    # 2a. Source files should not be copied into the build
    for ext in ("*.tex", "*.cls", "*.sty"):
        for f in glob.glob(str(build / "**" / ext), recursive=True):
            problems.append(f"source file in build output: {f}")
    # 2b. No local absolute paths leaking into HTML
    local_path_re = re.compile(r"/Users/[A-Za-z0-9_. -]+/[A-Za-z0-9_./ -]{4,}")  # release-scan: allow
    for f in sorted(glob.glob(str(build / "*.html"))):
        content = Path(f).read_text(errors="replace")
        # Ignore paths inside <script> blocks (may contain build-time info
        # intentionally embedded for debugging); check visible HTML only.
        content_no_script = re.sub(r"<script[^>]*>.*?</script>", "", content, flags=re.S)
        for m in local_path_re.finditer(content_no_script):
            problems.append(f"{Path(f).name}: local path in HTML: {m.group()!r}")
    return problems


# ---------------------------------------------------------------------------
# 3. PDF hash verification
# ---------------------------------------------------------------------------

def check_pdf_hash() -> list[str]:
    """Verify the PDF against the pinned hash in provenance.json."""
    problems = []
    if not PROVENANCE.exists():
        problems.append(f"provenance.json not found: {PROVENANCE}")
        return problems
    prov = json.loads(PROVENANCE.read_text())
    expected = prov.get("artifacts", {}).get("1109.1880v1.pdf")
    if not expected:
        problems.append("provenance.json has no artifacts[\"1109.1880v1.pdf\"] field")
        return problems
    if not PDF.exists():
        problems.append(f"PDF not found: {PDF}")
        return problems
    actual = sha256_file(PDF)
    if actual != expected:
        problems.append(
            f"PDF hash mismatch: expected {expected}, got {actual}\n"
            f"  Run scripts/fetch_source.py to restore the pinned PDF."
        )
    return problems


# ---------------------------------------------------------------------------
# 4. Cross-references and citations check
# ---------------------------------------------------------------------------

def check_unresolved_and_citations(build: Path) -> list[str]:
    """Fail on any '??' in visible HTML, raw citation keys, or @@REF markers."""
    problems = []
    bbl_path = ROOT / "docs/source/SteinIntro.bbl"
    if not bbl_path.is_file():
        bbl_path = ROOT / "source/upstream/tex/SteinIntro.bbl"
    cite_keys = []
    if bbl_path.is_file():
        cite_keys = re.findall(r"\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}", bbl_path.read_text(encoding="utf-8"))

    for f in sorted(glob.glob(str(build / "*.html"))):
        content = Path(f).read_text(encoding="utf-8", errors="replace")
        fname = Path(f).name
        # Remove <script> and <style>
        no_script = re.sub(r"<(script|style)[^>]*>.*?</\1>", "", content, flags=re.S)

        # 4a. Check for unresolved '??'
        text_only = re.sub(r"<[^>]+>", " ", no_script)
        if "??" in text_only:
            for m in re.finditer(r"(?:[A-Za-z0-9_(). -]{0,25}\?\?[A-Za-z0-9_(). -]{0,25})", text_only):
                snippet = m.group().strip()
                problems.append(f"{fname}: unresolved cross-reference: {snippet!r}")
                break

        # 4b. Check for raw citation keys in <a class="cite">
        for m in re.finditer(r'<a class="cite"[^>]*>([^<]+)</a>', no_script):
            link_txt = m.group(1).strip()
            for k in cite_keys:
                if link_txt == k or link_txt.startswith(f"{k},") or link_txt.startswith(f"({k}"):
                    problems.append(f"{fname}: raw citation key displayed: {link_txt!r} (expected Author (Year))")
                    break

        # 4c. Check for unhandled @@REF markers
        if "@@REF" in content:
            problems.append(f"{fname}: unhandled @@REF marker remaining in HTML")

    return problems


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

LOG: list = []


def out(line: str) -> None:
    print(line)
    LOG.append(line)


def annotate(failures: int) -> None:
    """In GitHub Actions, repeat the report as an annotation."""
    if os.environ.get("GITHUB_ACTIONS") == "true":
        level = "error" if failures else "notice"
        body = "\n".join(LOG)[:30000].replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print(f"::{level} title=Fidelity check::{body}")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--build", default=str(HERE / "_build"))
    args = ap.parse_args()
    build = Path(args.build)
    failures = 0

    # 0. PDF hash
    pdf_problems = check_pdf_hash()
    out(f"PDF hash: {'OK' if not pdf_problems else f'{len(pdf_problems)} problem(s)'}")
    for p in pdf_problems:
        out(f"    {p}")
    failures += len(pdf_problems)

    # 1. Section headings
    heading_problems = check_section_headings(build)
    out(f"section headings: {len(tex_section_headings())} in TeX, "
        f"{len(heading_problems)} missing from site HTML")
    for p in heading_problems:
        out(f"    {p}")
    failures += len(heading_problems)

    # 2. Hygiene
    hygiene_problems = check_hygiene(build)
    out(f"hygiene: {len(hygiene_problems)} problem(s)")
    for p in hygiene_problems[:20]:
        out(f"    {p}")
    failures += len(hygiene_problems)

    # 3. Macros
    sys.path.insert(0, str(HERE))
    import check_macros
    macro_problems = check_macros.check(build)
    out(f"macros: {len(macro_problems)} raw or undefined TeX macros on the site")
    for page, kind, detail in macro_problems[:20]:
        out(f"    {page}: {kind}: {detail}")
    failures += len(macro_problems)

    # 4. Cross-references and citations
    ref_problems = check_unresolved_and_citations(build)
    out(f"references & citations: {len(ref_problems)} problem(s) (no ?? or raw keys allowed)")
    for p in ref_problems[:20]:
        out(f"    {p}")
    failures += len(ref_problems)

    out("FIDELITY OK" if not failures else f"FIDELITY PROBLEMS: {failures}")
    annotate(failures)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
