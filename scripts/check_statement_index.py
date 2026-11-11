#!/usr/bin/env python3
"""W3a: Statement-index consistency check.

Fails if:
1. Any `docs/COVERAGE.md` table row names a `SteinMethod.` statement entry that
   does not exist in `Formalization/Statements/SecN.lean` (rows with status
   starting with `source issue` may reference refutation theorems in
   `Formalization/**/*.lean`, which must exist there).
2. Any `: Prop` entry in `Formalization/Statements/SecN.lean` lacks a
   corresponding `theorem <Name>_holds` wrapper in
   `Formalization/Statements/SecNProofs.lean`.

Usage:
  python3 scripts/check_statement_index.py [--git-rev <rev>]
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys
from typing import Callable, Optional

ROOT = Path(__file__).resolve().parents[1]

_BACKTICK_IDENT_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_']*)`")
_STMT_DEF_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+([A-Za-z0-9_']+)\b[^:]*:\s*Prop\s*:=",
    re.MULTILINE,
)
_DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class)\s+([A-Za-z_][A-Za-z0-9_']*)",
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

        if ch == "'" and i + 2 < n and (
            src[i + 2] == "'" or (nxt == "\\" and i + 3 < n and src[i + 3] == "'")
        ):
            in_char = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def read_file_disk(rel_path: str) -> Optional[str]:
    p = ROOT / rel_path
    if not p.is_file():
        return None
    return p.read_text(encoding="utf-8", errors="replace")


def read_file_git(rev: str, rel_path: str) -> Optional[str]:
    res = subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{rev}:{rel_path}"],
        capture_output=True,
    )
    if res.returncode != 0:
        return None
    return res.stdout.decode("utf-8", errors="replace")


def list_lean_files_disk(rel_dir: str) -> list[str]:
    d = ROOT / rel_dir
    if not d.is_dir():
        return []
    return sorted(
        p.relative_to(ROOT).as_posix() for p in d.rglob("*.lean") if p.is_file()
    )


def list_lean_files_git(rev: str, rel_dir: str) -> list[str]:
    res = subprocess.run(
        ["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only", rev, rel_dir],
        capture_output=True,
        text=True,
    )
    if res.returncode != 0:
        return []
    return sorted(p for p in res.stdout.splitlines() if p.endswith(".lean"))


def parse_coverage_rows(coverage_text: str) -> list[dict]:
    """Parse COVERAGE.md table rows into structured records."""
    rows: list[dict] = []
    in_table = False
    header_seen = False

    for line in coverage_text.splitlines():
        if not line.startswith("|"):
            if in_table:
                break
            continue
        in_table = True
        cols = [c.strip() for c in line.split("|")[1:-1]]
        if len(cols) < 6:
            continue
        if not header_seen:
            header_seen = True
            continue
        if all(set(c) <= {"-", ":", " "} for c in cols if c):
            continue

        source_res, label_col, lines_col, lean_col, status_col, accepted_col = cols[:6]
        names = [m.group(1) for m in _BACKTICK_IDENT_RE.finditer(lean_col)]
        is_source_issue_only = status_col.lower().startswith("source issue")
        is_definition_row = status_col.lower().startswith("definition")
        rows.append(
            {
                "source_result": source_res,
                "lean_names": names,
                "status": status_col,
                "accepted_in": accepted_col,
                "is_source_issue_only": is_source_issue_only,
                "is_definition_row": is_definition_row,
            }
        )
    return rows


def run_checks(
    read_fn: Callable[[str], Optional[str]],
    list_fn: Callable[[str], list[str]],
) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    notes: list[str] = []

    coverage_text = read_fn("docs/COVERAGE.md")
    if coverage_text is None:
        return ["Missing docs/COVERAGE.md"], []

    cov_rows = parse_coverage_rows(coverage_text)
    if not cov_rows:
        return ["No table rows found in docs/COVERAGE.md"], []

    stmt_files = [
        p
        for p in list_fn("Formalization/Statements")
        if re.search(r"/Sec\d+\.lean$", p)
    ]
    if not stmt_files:
        return ["No Formalization/Statements/SecN.lean files found"], []

    # Map section -> statement Prop declarations, and verify _holds wrappers for ALL SecN.lean entries
    sec_stmts: dict[int, list[str]] = {}
    entry_to_secs: dict[str, list[int]] = {}

    for spath in stmt_files:
        m = re.search(r"Sec(\d+)\.lean$", spath)
        assert m is not None
        sec = int(m.group(1))
        raw = read_fn(spath)
        if raw is None:
            errors.append(f"Could not read {spath}")
            continue
        cleaned = strip_lean_comments_and_strings(raw)
        names = _STMT_DEF_RE.findall(cleaned)
        sec_stmts[sec] = names
        for name in names:
            entry_to_secs.setdefault(name, []).append(sec)

        ppath = f"Formalization/Statements/Sec{sec}Proofs.lean"
        praw = read_fn(ppath)
        if praw is None:
            errors.append(f"Missing proof wrapper file {ppath} for {spath}")
            continue
        pcleaned = strip_lean_comments_and_strings(praw)
        for name in names:
            holds_pat = re.compile(
                rf"\btheorem\s+{re.escape(name)}_holds\s*:\s*(?:SteinMethod\.)?{re.escape(name)}\b"
            )
            if not holds_pat.search(pcleaned):
                errors.append(
                    f"{ppath} is missing `theorem {name}_holds : {name}` (declared in {spath})"
                )

    # Lazily index library declarations if needed for `source issue` refutation rows
    all_lib_decls: Optional[set[str]] = None

    def get_all_lib_decls() -> set[str]:
        nonlocal all_lib_decls
        if all_lib_decls is None:
            decls: set[str] = set()
            for lpath in list_fn("Formalization"):
                lraw = read_fn(lpath)
                if lraw is None:
                    continue
                lcleaned = strip_lean_comments_and_strings(lraw)
                decls.update(_DECL_RE.findall(lcleaned))
            all_lib_decls = decls
        return all_lib_decls

    cov_stmt_names: set[str] = set()
    for row in cov_rows:
        has_sec_stmt = any(n in entry_to_secs for n in row["lean_names"])
        for name in row["lean_names"]:
            if name in entry_to_secs:
                cov_stmt_names.add(name)
                continue
            if has_sec_stmt and name in get_all_lib_decls():
                notes.append(
                    f"COVERAGE row `{row['source_result']}` cites auxiliary library "
                    f"declaration `{name}` alongside a Statements/SecN.lean `: Prop`."
                )
                continue
            if row["is_source_issue_only"] and name in get_all_lib_decls():
                notes.append(
                    f"COVERAGE source-issue row `{row['source_result']}` cites library "
                    f"refutation declaration `{name}` (verified in Formalization/)."
                )
                continue
            if row["is_definition_row"] and name in get_all_lib_decls():
                notes.append(
                    f"COVERAGE definition row `{row['source_result']}` cites library "
                    f"definition `{name}` (verified in Formalization/)."
                )
                continue
            errors.append(
                f"COVERAGE row `{row['source_result']}` names `{name}`, which does not "
                f"exist as a `: Prop` statement in any Formalization/Statements/SecN.lean"
            )

    for sec, names in sorted(sec_stmts.items()):
        for name in names:
            if name not in cov_stmt_names:
                notes.append(
                    f"Formalization/Statements/Sec{sec}.lean: `{name}` is compiled with "
                    f"`{name}_holds` but not yet listed in docs/COVERAGE.md (unreviewed WIP)."
                )

    return errors, notes


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check docs/COVERAGE.md statement index and SecNProofs _holds wrappers."
    )
    parser.add_argument(
        "--git-rev",
        metavar="REV",
        default=None,
        help="Read files via `git show <rev>:<path>` instead of disk.",
    )
    args = parser.parse_args()

    if args.git_rev is not None:
        rev = args.git_rev
        errors, notes = run_checks(
            lambda p: read_file_git(rev, p),
            lambda d: list_lean_files_git(rev, d),
        )
    else:
        errors, notes = run_checks(read_file_disk, list_lean_files_disk)

    if notes:
        for n in notes:
            print(f"NOTE: {n}")

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)

    print("Statement index check passed: all COVERAGE entries and _holds wrappers verified.")


if __name__ == "__main__":
    main()
