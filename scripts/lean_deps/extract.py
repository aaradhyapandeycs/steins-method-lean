#!/usr/bin/env python3
"""Regenerate docs/graph/lean-deps.json from the compiled proofs.

Run from the repository root after `lake build`, with a clean `Formalization/` tree, so the commit
recorded in the file is the one whose proofs were read:

    python3 scripts/lean_deps/extract.py

The reader site shows the recorded commit next to the extracted edges and labels them as stale when
the site is built from a later commit whose Lean files differ.
"""

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main() -> int:
    dirty = subprocess.run(["git", "status", "--porcelain", "--untracked-files=no", "--", "Formalization",
                            "Formalization.lean"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    if dirty:
        print("Formalization/ has uncommitted changes; commit them first:\n" + dirty, file=sys.stderr)
        return 1
    rev = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    out = subprocess.run(["lake", "env", "lean", "scripts/lean_deps/ExtractDeps.lean"], cwd=ROOT,
                         capture_output=True, text=True)
    if out.returncode != 0:
        print(out.stderr, file=sys.stderr)
        return out.returncode
    data = json.loads(out.stdout)
    # Tree hashes identify the Lean sources independently of the commit (the public mirror has
    # different commit ids but identical trees), so readers can check the data is current.
    tree = subprocess.run(["git", "rev-parse", "HEAD:Formalization", "HEAD:Formalization.lean"], cwd=ROOT,
                          capture_output=True, text=True).stdout.split()
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    doc = {"_about": "Relations between statement entries extracted from the compiled Lean proofs by "
                     "scripts/lean_deps/ExtractDeps.lean (roots: project theorems a wrapper applies; closure: "
                     "project declarations reachable through types and proof terms). Not a curated "
                     "mathematical dependency graph.",
           "lean_sources": {"Formalization": tree[0], "Formalization.lean": tree[1]},
           "lean_toolchain": toolchain, "entries": data["entries"]}
    path = ROOT / "docs/graph/lean-deps.json"
    path.write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n")
    print(f"wrote {path.relative_to(ROOT)}: {len(doc['entries'])} entries at {rev[:7]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
