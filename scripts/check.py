#!/usr/bin/env python3
"""Repository build, kernel-audit, forbidden-token, and statement-wrapper checks."""
from __future__ import annotations

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

FORBIDDEN_RE = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|opaque|implemented_by|extern|unsafe)\b"
    r"|debug\.skipKernelTC"
)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.«»]+)\s*$", re.MULTILINE)
STMT_DEF_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z0-9_']+)\b[^:]*:\s*Prop\s*:=",
    re.MULTILINE,
)


def strip_lean_comments_and_strings(src: str) -> str:
    """Replace Lean comments and string literals with spaces, preserving newlines."""
    out: list[str] = []
    i = 0
    n = len(src)
    block_depth = 0
    in_line_comment = False
    in_string = False
    in_char = False

    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append(" ")
                out.append("\n" if nxt == "\n" else " ")
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_char:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif ch == "'":
                in_char = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.append("  ")
            i += 2
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue

        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        if ch == "'" and i + 2 < n and (src[i + 2] == "'" or (nxt == "\\" and i + 3 < n and src[i + 3] == "'")):
            in_char = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def tracked_or_imported_formalization_files() -> list[Path]:
    """Return all git-tracked/staged and Formalization.lean-imported .lean files."""
    found: set[Path] = set()
    form_dir = ROOT / "Formalization"
    git_proc = subprocess.run(
        ["git", "ls-files", "--cached", "Formalization"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    if git_proc.returncode == 0:
        for line in git_proc.stdout.splitlines():
            rel = line.strip()
            if rel.endswith(".lean"):
                found.add(ROOT / rel)
    elif form_dir.is_dir():
        found.update(form_dir.rglob("*.lean"))

    root_lean = ROOT / "Formalization.lean"
    if root_lean.is_file():
        cleaned = strip_lean_comments_and_strings(root_lean.read_text(encoding="utf-8"))
        for imp in IMPORT_RE.findall(cleaned):
            if imp.startswith("Formalization."):
                found.add(ROOT.joinpath(*imp.split(".")).with_suffix(".lean"))
    return sorted(found)


def check_forbidden_tokens() -> list[str]:
    errors: list[str] = []
    targets: list[Path] = [ROOT / "Audit.lean", ROOT / "Formalization.lean"]
    targets.extend(tracked_or_imported_formalization_files())

    for path in targets:
        if not path.is_file():
            errors.append(f"Missing expected Lean file: {path.relative_to(ROOT)}")
            continue
        raw = path.read_text(encoding="utf-8")
        cleaned = strip_lean_comments_and_strings(raw)
        for lineno, line in enumerate(cleaned.splitlines(), start=1):
            for match in FORBIDDEN_RE.finditer(line):
                col = match.start() + 1
                token = match.group(0)
                errors.append(f"{path.relative_to(ROOT)}:{lineno}:{col}: forbidden token `{token}`")
    return errors


def check_statement_wrappers() -> list[str]:
    errors: list[str] = []
    stmts_dir = ROOT / "Formalization" / "Statements"
    root_lean = ROOT / "Formalization.lean"
    if not root_lean.is_file():
        return ["Missing Formalization.lean"]

    root_cleaned = strip_lean_comments_and_strings(root_lean.read_text(encoding="utf-8"))
    root_imports = set(IMPORT_RE.findall(root_cleaned))

    if not stmts_dir.is_dir():
        errors.append("Missing directory Formalization/Statements")
        return errors

    sec_files = sorted(
        p for p in stmts_dir.glob("Sec*.lean") if not p.stem.endswith("Proofs")
    )
    if not sec_files:
        errors.append("No Formalization/Statements/Sec*.lean files found")
        return errors

    for sec_path in sec_files:
        sec_stem = sec_path.stem  # e.g. Sec1
        sec_mod = f"Formalization.Statements.{sec_stem}"
        proofs_path = ROOT / "Formalization" / "Statements" / f"{sec_stem}Proofs.lean"
        proofs_mod = f"Formalization.Statements.{sec_stem}Proofs"

        if sec_mod not in root_imports:
            errors.append(f"Formalization.lean does not import `{sec_mod}`")
        if proofs_mod not in root_imports:
            errors.append(f"Formalization.lean does not import `{proofs_mod}`")

        sec_cleaned = strip_lean_comments_and_strings(sec_path.read_text(encoding="utf-8"))
        sec_imports = IMPORT_RE.findall(sec_cleaned)
        for imp in sec_imports:
            if imp != "Formalization.Defs" and not imp.startswith("Formalization.Defs."):
                errors.append(
                    f"{sec_path.relative_to(ROOT)} imports `{imp}`; "
                    f"statement files may import definitions only (AGENTS.md Rule 5)"
                )

        stmt_names = STMT_DEF_RE.findall(sec_cleaned)
        if not stmt_names:
            errors.append(f"{sec_path.relative_to(ROOT)} declares no `: Prop` statements")
            continue

        if not proofs_path.is_file():
            errors.append(f"Missing proof wrapper file {proofs_path.relative_to(ROOT)}")
            continue

        proofs_cleaned = strip_lean_comments_and_strings(proofs_path.read_text(encoding="utf-8"))
        for name in stmt_names:
            holds_pat = re.compile(
                rf"\btheorem\s+{re.escape(name)}_holds\s*:\s*(?:SteinMethod\.)?{re.escape(name)}\b"
            )
            if not holds_pat.search(proofs_cleaned):
                errors.append(
                    f"{proofs_path.relative_to(ROOT)} is missing `theorem {name}_holds : {name}`"
                )

    return errors


def run_cmd(cmd: list[str]) -> None:
    print(f"$ {' '.join(cmd)}", flush=True)
    proc = subprocess.run(cmd, cwd=ROOT)
    if proc.returncode != 0:
        sys.exit(proc.returncode)


def main() -> None:
    run_cmd(["lake", "build"])
    run_cmd(["lake", "env", "lean", "Audit.lean"])

    token_errors = check_forbidden_tokens()
    if token_errors:
        print("Forbidden token check FAILED:", file=sys.stderr)
        for err in token_errors:
            print(f"  {err}", file=sys.stderr)
        sys.exit(1)
    print("Forbidden token check passed (0 hits outside comments/strings).")

    wrapper_errors = check_statement_wrappers()
    if wrapper_errors:
        print("Statement wrapper check FAILED:", file=sys.stderr)
        for err in wrapper_errors:
            print(f"  {err}", file=sys.stderr)
        sys.exit(1)
    print("Statement wrapper check passed (all Statements/SecN.lean entries have _holds proofs).")


if __name__ == "__main__":
    main()
