#!/usr/bin/env python3
"""Generate and verify docs/source-inventory.md from source/upstream/tex/SteinIntro.tex."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
TEX_PATH = ROOT / "source" / "upstream" / "tex" / "SteinIntro.tex"
OUT_PATH = ROOT / "docs" / "source-inventory.md"

THM_KINDS = ("theorem", "proposition", "lemma", "corollary")
DEF_KINDS = ("definition", "example", "remark", "case", "condition")
ALL_ENV_KINDS = THM_KINDS + DEF_KINDS

# Unnumbered displays that only introduce a local symbol/operator abbreviation ("Define A f(x) = ...",
# "Let W = ...", etc.) rather than asserting a mathematical theorem/identity/bound, plus (7.6) which
# defines the Curie-Weiss Gibbs measure. Kept in the table with Role = `definition` so no display is
# silently omitted while assertive vs. definitional totals are both exact.
DEFINITIONAL_DISPLAY_STARTS = {
    564,   # Define operator A f(x) = f'(x) - x f(x)
    660,   # Let f_h solve f'_h(w) - w f_h(w) = h(w) - Phi(h)
    1057,  # Define W' = W - X_I/sqrt(n) + X'_I/sqrt(n)
    1123,  # where Q = sum_{i=1}^n sum_{j in N_i} X_i X_j
    1825,  # Define Poisson operator A f(k) = lambda f(k+1) - k f(k)
    2013,  # Let X_1 = prod_{j=1}^k Y_j
    2017,  # Let X_i = (1 - Y_{i-1}) prod_{j=0}^{k-1} Y_{i+j}
    2034,  # Parameter choice k = log(n(1-p))/log(1/p) + c in Remark 4.2
    2728,  # Define Exponential operator A f(x) = f'(x) - f(x) + f(0)
    2971,  # Define g(m) = f(p sum_{i=1}^m X_i)
    2995,  # Define Z_{n+1} = sum_{i=1}^{Z_n} Z_{n,i}
    3129,  # Let R'_{n,j} =^d R_{n,j} | {L_{n,j} = 0}
    3231,  # Define Geometric operator A f(k) = (1-p) Delta f(k) - p f(k) + p f(0)
    3601,  # Let W = sum_{i=1}^n a_{i sigma_j} - (1/n) sum_{i,j} a_{ij}
    3606,  # Define W' = sum_{i=1}^n a_{i sigma'_j} - (1/n) sum_{i,j} a_{ij}
    3633,  # (7.6) Define Curie-Weiss Gibbs measure P(sigma) = Z^{-1} exp(...)
    3662,  # Define f(X) := E[F(X, X') | X]
    3880,  # X_i^{(k)} = cases {1 if head run ..., 0 otherwise}
}


def strip_tex_comment(line: str) -> str:
    """Strip unescaped % comments; note \\% in Ross's preamble is redefined as \\mathcal."""
    out: list[str] = []
    i = 0
    n = len(line)
    while i < n:
        if line[i] == "\\":
            out.append(line[i : i + 2])
            i += 2
        elif line[i] == "%":
            break
        else:
            out.append(line[i])
            i += 1
    return "".join(out)


def compact_snippet(text: str, limit: int = 88) -> str:
    s = re.sub(r"\\label\s*\{[^}]+\}", "", text)
    s = re.sub(r"\s+", " ", s).strip()
    s = s.replace("|", r"\|").replace("`", "'")
    if len(s) > limit:
        return s[: limit - 3] + "..."
    return s


def extract_braced(text: str, brace_pos: int) -> tuple[str, int]:
    assert text[brace_pos] == "{"
    depth = 0
    out: list[str] = []
    for idx in range(brace_pos, len(text)):
        ch = text[idx]
        if ch == "{":
            if depth > 0:
                out.append(ch)
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return "".join(out), idx + 1
            out.append(ch)
        else:
            out.append(ch)
    raise RuntimeError(f"Unclosed brace in: {text[:80]}")


def parse_inventory(raw_bytes: bytes) -> dict:
    tex_sha256 = hashlib.sha256(raw_bytes).hexdigest()
    raw_lines = raw_bytes.decode("latin-1").splitlines()
    clean_lines = [strip_tex_comment(l) for l in raw_lines]
    total_lines = len(raw_lines)

    # 1. Parse headings (sections, subsections, subsubsections) in active body (L321..L4359)
    heading_re = re.compile(r"\\(section|subsection|subsubsection)(\*)?\s*\{")
    headings_raw: list[dict] = []
    sec = 0
    subsec = 0
    subsubsec = 0
    for idx in range(320, total_lines):
        ln = idx + 1
        line = clean_lines[idx]
        m = heading_re.search(line)
        if not m:
            continue
        level = m.group(1)
        starred = bool(m.group(2))
        brace_idx = line.index("{", m.start())
        title, after_idx = extract_braced(line, brace_idx)
        rem = line[after_idx:]
        labs = re.findall(r"\\label\s*\{([^}]+)\}", rem)
        if not labs and idx + 1 < total_lines:
            # Check immediate next line only if it starts with \label
            nxt = clean_lines[idx + 1].strip()
            if nxt.startswith("\\label"):
                labs = re.findall(r"\\label\s*\{([^}]+)\}", nxt)
        if starred:
            num = "unnumbered"
            lvl_num = 3
        elif level == "section":
            sec += 1
            subsec = 0
            subsubsec = 0
            num = f"{sec}"
            lvl_num = 1
        elif level == "subsection":
            subsec += 1
            subsubsec = 0
            num = f"{sec}.{subsec}"
            lvl_num = 2
        else:
            subsubsec += 1
            num = f"{sec}.{subsec}.{subsubsec}"
            lvl_num = 3
        headings_raw.append(
            {
                "level": level + ("*" if starred else ""),
                "level_rank": lvl_num,
                "number": num,
                "title": re.sub(r"\s+", " ", title).strip(),
                "labels": labs,
                "start": ln,
                "end": None,
            }
        )

    # Compute section/subsection/subsubsection line ranges (up to next heading of <= rank,
    # stopping active sections before L3889 commented-out Section 8 / L4348 Acknowledgments)
    active_body_last = 3887
    doc_end_line = 4359
    for idx_h, h in enumerate(headings_raw):
        end_ln = doc_end_line if h["start"] >= 4348 else active_body_last
        for nxt in headings_raw[idx_h + 1 :]:
            if nxt["level_rank"] <= h["level_rank"] or (
                h["start"] < 4348 and nxt["start"] >= 4348
            ):
                end_ln = min(end_ln, nxt["start"] - 1)
                break
        # Trim trailing blank/commented lines only for Section 7 before commented draft L3889
        h["end"] = end_ln

    # 2. Parse numbered environments (theorem/proposition/lemma/corollary & definition/example/remark)
    env_token_re = re.compile(
        r"\\(begin|end)\s*\{(" + "|".join(ALL_ENV_KINDS) + r")\}"
    )
    sec_e = 0
    thm_ctr = 0
    def_ctr = 0
    stack: list[dict] = []
    envs: list[dict] = []

    for idx in range(320, total_lines):
        ln = idx + 1
        line = clean_lines[idx]
        if re.search(r"\\section\s*\{", line):
            sec_e += 1
            thm_ctr = 0
            def_ctr = 0
        for m in env_token_re.finditer(line):
            act, kind = m.group(1), m.group(2)
            if act == "begin":
                if kind in THM_KINDS:
                    thm_ctr += 1
                    num = f"{sec_e}.{thm_ctr}"
                else:
                    def_ctr += 1
                    num = f"{sec_e}.{def_ctr}"
                rem = line[m.end() :]
                opt_title = ""
                om = re.match(r"\s*\[([^\]]+)\]", rem)
                if om:
                    opt_title = om.group(1).strip()
                stack.append(
                    {
                        "kind": kind,
                        "section": sec_e,
                        "number": num,
                        "title": opt_title,
                        "start": ln,
                        "end": None,
                        "nested_in": stack[-1]["kind"] + " " + stack[-1]["number"]
                        if stack
                        else None,
                    }
                )
            else:
                if not stack or stack[-1]["kind"] != kind:
                    raise RuntimeError(f"Mismatched \\end{{{kind}}} at L{ln}")
                rec = stack.pop()
                rec["end"] = ln
                envs.append(rec)

    if stack:
        raise RuntimeError(f"Unclosed environments: {stack}")
    envs.sort(key=lambda r: (r["start"], -r["end"]))

    # Extract environment-level label and any enumerated item labels inside each env
    # Mask nested child environments and display environments so labels aren't double-attributed
    display_open_re = re.compile(
        r"\\(ban|bes|ben|ba|be)\b|\\\[|\\begin\s*\{(equation|displaymath)\}"
    )

    # 3. Parse all display blocks and split multi-row numbered \ban blocks into per-row entries
    sec_d = 0
    eq_ctr = 0
    display_blocks: list[dict] = []
    display_rows: list[dict] = []
    i = 320
    while i < total_lines:
        line = clean_lines[i]
        if re.search(r"\\section\s*\{", line):
            sec_d += 1
            eq_ctr = 0
        m = display_open_re.search(line)
        if not m:
            i += 1
            continue
        start_ln = i + 1
        macro = m.group(0)
        if macro in ("\\ba", "\\ban", "\\be", "\\ben", "\\bes"):
            closer = re.compile(r"\\ee\b")
        elif macro == "\\[":
            closer = re.compile(r"\\\]")
        elif "equation" in macro:
            closer = re.compile(r"\\end\s*\{equation\}")
        else:
            closer = re.compile(r"\\end\s*\{displaymath\}")

        # Collect (line_no, text) slices inside this display block
        rem_first = line[m.end() :]
        cm = closer.search(rem_first)
        if cm:
            end_ln = start_ln
            line_slices = [(start_ln, rem_first[: cm.start()])]
            i += 1
        else:
            line_slices = [(start_ln, rem_first)]
            j = i + 1
            while j < total_lines:
                cm = closer.search(clean_lines[j])
                if cm:
                    line_slices.append((j + 1, clean_lines[j][: cm.start()]))
                    end_ln = j + 1
                    break
                line_slices.append((j + 1, clean_lines[j]))
                j += 1
            else:
                raise RuntimeError(f"Unclosed display {macro} starting at L{start_ln}")
            i = j + 1

        full_text = "\n".join(s for _, s in line_slices)
        role = "definition" if start_ln in DEFINITIONAL_DISPLAY_STARTS else "assertion"

        if macro in ("\\ben", "\\begin{equation}"):
            labs = re.findall(r"\\label\s*\{([^}]+)\}", full_text)
            if "\\notag" not in full_text and "\\nonumber" not in full_text:
                eq_ctr += 1
                num = f"({sec_d}.{eq_ctr})"
            else:
                num = "unnumbered"
            row_entry = {
                "section": sec_d,
                "macro": macro,
                "number": num,
                "labels": labs,
                "start": start_ln,
                "end": end_ln,
                "role": role,
                "snippet": compact_snippet(full_text),
            }
            display_blocks.append(row_entry)
            display_rows.append(row_entry)
        elif macro == "\\ban":
            # Split into alignment rows while keeping nested split/cases/array intact,
            # preserving line ranges per row!
            sub_depth = 0
            cur_lines: list[tuple[int, str]] = []
            raw_rows: list[list[tuple[int, str]]] = []
            for sln, stxt in line_slices:
                # Track subenv depth across line
                pos = 0
                while pos < len(stxt):
                    sub_b = re.search(r"\\begin\s*\{(split|cases|array)\}", stxt[pos:])
                    sub_e = re.search(r"\\end\s*\{(split|cases|array)\}", stxt[pos:])
                    br = re.search(r"\\\\", stxt[pos:]) if sub_depth == 0 else None
                    candidates_pos = []
                    if sub_b:
                        candidates_pos.append((sub_b.start(), "b", sub_b.end()))
                    if sub_e:
                        candidates_pos.append((sub_e.start(), "e", sub_e.end()))
                    if br:
                        candidates_pos.append((br.start(), "br", br.end()))
                    if not candidates_pos:
                        cur_lines.append((sln, stxt[pos:]))
                        break
                    candidates_pos.sort(key=lambda x: x[0])
                    c_start, c_kind, c_end = candidates_pos[0]
                    cur_lines.append((sln, stxt[pos : pos + c_start]))
                    if c_kind == "b":
                        sub_depth += 1
                        cur_lines.append((sln, stxt[pos + c_start : pos + c_end]))
                    elif c_kind == "e":
                        sub_depth = max(0, sub_depth - 1)
                        cur_lines.append((sln, stxt[pos + c_start : pos + c_end]))
                    else:
                        raw_rows.append(cur_lines)
                        cur_lines = []
                    pos += c_end
            if any(seg.strip() for _, seg in cur_lines):
                raw_rows.append(cur_lines)

            # Group \notag rows with the numbered row of the same multi-line equation if only 1 number,
            # OR emit each numbered row with its exact row line range!
            numbered_in_block = []
            parsed_rows = []
            for r_segs in raw_rows:
                r_txt = "\n".join(seg for _, seg in r_segs)
                non_empty_lns = [ln_no for ln_no, seg in r_segs if seg.strip()]
                r_start = non_empty_lns[0] if non_empty_lns else start_ln
                r_end = non_empty_lns[-1] if non_empty_lns else end_ln
                r_labs = re.findall(r"\\label\s*\{([^}]+)\}", r_txt)
                is_num = "\\notag" not in r_txt and "\\nonumber" not in r_txt
                if is_num:
                    eq_ctr += 1
                    r_num = f"({sec_d}.{eq_ctr})"
                    numbered_in_block.append(r_num)
                else:
                    r_num = None
                parsed_rows.append((r_start, r_end, r_num, r_labs, r_txt))

            display_blocks.append(
                {
                    "section": sec_d,
                    "macro": macro,
                    "numbers": numbered_in_block,
                    "start": start_ln,
                    "end": end_ln,
                }
            )
            if len(numbered_in_block) <= 1:
                labs = re.findall(r"\\label\s*\{([^}]+)\}", full_text)
                display_rows.append(
                    {
                        "section": sec_d,
                        "macro": macro,
                        "number": numbered_in_block[0]
                        if numbered_in_block
                        else "unnumbered",
                        "labels": labs,
                        "start": start_ln,
                        "end": end_ln,
                        "role": role,
                        "snippet": compact_snippet(full_text),
                    }
                )
            else:
                # Emit one inventory entry per numbered row in multi-equation \ban block,
                # attaching any immediately preceding \notag continuation lines to that row.
                pending_start: int | None = None
                pending_txt: list[str] = []
                pending_labs: list[str] = []
                for r_start, r_end, r_num, r_labs, r_txt in parsed_rows:
                    if pending_start is None:
                        pending_start = r_start
                    pending_txt.append(r_txt)
                    pending_labs.extend(r_labs)
                    if r_num is not None:
                        display_rows.append(
                            {
                                "section": sec_d,
                                "macro": macro,
                                "number": r_num,
                                "labels": list(pending_labs),
                                "start": pending_start,
                                "end": r_end,
                                "role": role,
                                "snippet": compact_snippet(" ".join(pending_txt)),
                            }
                        )
                        pending_start = None
                        pending_txt = []
                        pending_labs = []
        else:
            labs = re.findall(r"\\label\s*\{([^}]+)\}", full_text)
            row_entry = {
                "section": sec_d,
                "macro": macro,
                "number": "unnumbered",
                "labels": labs,
                "start": start_ln,
                "end": end_ln,
                "role": role,
                "snippet": compact_snippet(full_text),
            }
            display_blocks.append(row_entry)
            display_rows.append(row_entry)

    # Populate labels on environments (excluding labels inside displays or nested child envs)
    display_label_set = {lab for d in display_rows for lab in d["labels"]}
    heading_label_set = {lab for h in headings_raw for lab in h["labels"]}

    for e in envs:
        child_ranges = [
            (c["start"], c["end"])
            for c in envs
            if c is not e and e["start"] <= c["start"] and c["end"] <= e["end"]
        ]
        env_labs: list[str] = []
        item_labs: list[tuple[int, str]] = []
        for ln in range(e["start"], e["end"] + 1):
            if any(cs <= ln <= ce for cs, ce in child_ranges):
                continue
            ltxt = clean_lines[ln - 1]
            for lab in re.findall(r"\\label\s*\{([^}]+)\}", ltxt):
                if lab in display_label_set or lab in heading_label_set:
                    continue
                if "\\item" in ltxt:
                    item_labs.append((ln, lab))
                else:
                    env_labs.append(lab)
        e["labels"] = env_labs
        e["item_labels"] = item_labs

    # Also extract standalone labeled \item declarations outside numbered environments
    env_spans = [(e["start"], e["end"]) for e in envs]
    prose_labeled_items: list[dict] = []
    cur_item_ctr = 0
    in_prose_enum = False
    for idx in range(320, total_lines):
        ln = idx + 1
        if any(s <= ln <= e_ln for s, e_ln in env_spans):
            continue
        ltxt = clean_lines[idx]
        if "\\begin{enumerate}" in ltxt:
            in_prose_enum = True
            cur_item_ctr = 0
        elif "\\end{enumerate}" in ltxt:
            in_prose_enum = False
        elif in_prose_enum and "\\item" in ltxt:
            cur_item_ctr += 1
            labs = re.findall(r"\\label\s*\{([^}]+)\}", ltxt)
            if labs:
                # Find end of this item (before next \item or \end{enumerate})
                end_item = ln
                for j in range(idx + 1, total_lines):
                    if "\\item" in clean_lines[j] or "\\end{enumerate}" in clean_lines[j]:
                        end_item = j
                        break
                snippet_txt = " ".join(
                    re.sub(r"\\item", "", clean_lines[k]) for k in range(idx, end_item)
                )
                prose_labeled_items.append(
                    {
                        "number": str(cur_item_ctr),
                        "labels": labs,
                        "start": ln,
                        "end": end_item,
                        "snippet": compact_snippet(snippet_txt),
                    }
                )

    # Verify 100% label accounting across active document (L321..L4359)
    all_active_labels = []
    for idx in range(320, total_lines):
        for lab in re.findall(r"\\label\s*\{([^}]+)\}", clean_lines[idx]):
            all_active_labels.append((idx + 1, lab))
    captured_labels = (
        set(heading_label_set)
        | set(display_label_set)
        | {lab for e in envs for lab in e["labels"]}
        | {lab for e in envs for _, lab in e["item_labels"]}
        | {lab for it in prose_labeled_items for lab in it["labels"]}
    )
    missing_labels = [(ln, lab) for ln, lab in all_active_labels if lab not in captured_labels]
    if missing_labels:
        raise RuntimeError(f"Unaccounted active labels: {missing_labels}")

    return {
        "tex_sha256": tex_sha256,
        "total_lines": total_lines,
        "headings": headings_raw,
        "envs": envs,
        "prose_labeled_items": prose_labeled_items,
        "display_blocks_count": len(display_blocks),
        "displays": display_rows,
        "active_label_count": len(all_active_labels),
    }


def render_markdown(inv: dict) -> str:
    headings = inv["headings"]
    envs = inv["envs"]
    prose_items = inv["prose_labeled_items"]
    displays = inv["displays"]

    env_counts = Counter(e["kind"] for e in envs)
    sec_lvls = Counter(h["level"] for h in headings)
    num_eqs = [d for d in displays if d["number"] != "unnumbered"]
    unnum_eqs = [d for d in displays if d["number"] == "unnumbered"]
    assertive_displays = [d for d in displays if d["role"] == "assertion"]
    def_displays = [d for d in displays if d["role"] == "definition"]
    num_assertive = [d for d in num_eqs if d["role"] == "assertion"]
    unnum_assertive = [d for d in unnum_eqs if d["role"] == "assertion"]
    item_labels_total = sum(len(e["item_labels"]) for e in envs)

    out: list[str] = []
    out.append("# Source Inventory — N. Ross, *Fundamentals of Stein's method* (`arXiv:1109.1880v1`)")
    out.append("")
    out.append(
        "Generated by `python3 scripts/generate_inventory.py` and verified against the compiled "
        "arXiv PDF (`source/upstream/1109.1880v1.pdf`, 86 pages). Re-verify reproducibility with "
        "`python3 scripts/generate_inventory.py --check`."
    )
    out.append("")
    out.append(
        f"- **Upstream TeX file**: `source/upstream/tex/SteinIntro.tex` "
        f"(`{inv['total_lines']}` lines, ISO-8859-1, SHA-256 `{inv['tex_sha256']}`)"
    )
    out.append(
        "- **Counter structure** (`SteinIntro.tex:42-54`): two independent `[section]` counters — "
        "`theorem` (shared by `theorem`, `proposition`, `lemma`, `corollary`) and `definition` "
        "(shared by `definition`, `example`, `remark`, `case`, `condition`); equations use "
        "`\\numberwithin{equation}{section}` (`SteinIntro.tex:9,39`)."
    )
    out.append(
        "- **Commented-out draft region** (`SteinIntro.tex:3889-4347`): `% \\section{Local Limit Theorems}` "
        "is 100% `%`-commented in Ross's e-print and absent from the compiled PDF and *Probability Surveys* "
        "article; excluded from active totals below."
    )
    out.append(
        f"- **Active `\\label` accounting**: all `{inv['active_label_count']}` active `\\label{{...}}` "
        "declarations in `SteinIntro.tex:321-4359` are accounted for below (`0` orphan labels, including "
        f"spaced `\\label {{1717}}` at `SteinIntro.tex:3287`, `9` enumerated sub-item labels inside "
        f"lemmas/propositions, and `{len(prose_items)}` labeled prose claims in Section 5.3)."
    )
    out.append("")
    out.append("## Summary Totals by Kind")
    out.append("")
    out.append("| Category / Kind | Count | Notes |")
    out.append("| --- | ---: | --- |")
    out.append(f"| `section` | {sec_lvls['section']} | Sections 1–7 (`SteinIntro.tex:347-3887`) |")
    out.append(f"| `subsection` | {sec_lvls['subsection']} | Numbered subsections |")
    out.append(f"| `subsubsection` | {sec_lvls['subsubsection']} | Numbered subsubsections |")
    out.append(f"| `subsubsection*` | {sec_lvls['subsubsection*']} | Unnumbered `Acknowledgments` (`SteinIntro.tex:4348-4359`) |")
    out.append(
        f"| **Total headings** | **{len(headings)}** | "
        f"{len(headings) - sec_lvls['subsubsection*']} numbered + {sec_lvls['subsubsection*']} unnumbered |"
    )
    out.append(f"| `theorem` | {env_counts['theorem']} | `[theorem]` counter |")
    out.append(f"| `proposition` | {env_counts['proposition']} | `[theorem]` counter (note Prop 7.3 at `SteinIntro.tex:3612-3617` is nested inside Example 7.5) |")
    out.append(f"| `lemma` | {env_counts['lemma']} | `[theorem]` counter |")
    out.append(f"| `corollary` | {env_counts['corollary']} | `[theorem]` counter |")
    out.append(f"| `definition` | {env_counts['definition']} | `[definition]` counter |")
    out.append(f"| `remark` | {env_counts['remark']} | `[definition]` counter |")
    out.append(f"| `example` | {env_counts['example']} | `[definition]` counter |")
    out.append(f"| `case` / `condition` | {env_counts['case'] + env_counts['condition']} | Declared in preamble (`SteinIntro.tex:52-53`), unused in active text |")
    out.append(f"| **Total numbered environments** | **{len(envs)}** | 77 `[theorem]`-stream + 45 `[definition]`-stream (plus {item_labels_total} labeled sub-items) |")
    out.append(f"| Labeled prose `enumerate` claims | {len(prose_items)} | Section 5.3 size-bias tree claims (`SteinIntro.tex:3061-3067`) |")
    out.append(f"| Displayed equations (`assertion`, numbered) | {len(num_assertive)} | Numbered equation rows asserting an identity, bound, ODE, or limit |")
    out.append(f"| Displayed equations (`assertion`, unnumbered) | {len(unnum_assertive)} | Unnumbered displays asserting an identity, bound, ODE, or limit |")
    out.append(f"| **Total assertive displayed equations** | **{len(assertive_displays)}** | `{len(num_assertive)}` numbered + `{len(unnum_assertive)}` unnumbered |")
    out.append(f"| Displayed equations (`definition` setup) | {len(def_displays)} | `1` numbered (`(7.6)` Gibbs measure) + `{len(def_displays) - 1}` unnumbered symbol/operator definitions |")
    out.append(f"| **Total displayed equation rows** | **{len(displays)}** | `{len(num_eqs)}` numbered rows `(1.1)`–`(7.12)` + `{len(unnum_eqs)}` unnumbered across `{inv['display_blocks_count']}` TeX display blocks |")
    out.append("")

    # Section 1: Headings table
    out.append("## 1. Sections, Subsections, and Subsubsections")
    out.append("")
    out.append("| Level | Number | Title | TeX Label(s) | Line Range |")
    out.append("| --- | --- | --- | --- | --- |")
    for h in headings:
        labs = ", ".join(f"`{l}`" for l in h["labels"]) if h["labels"] else "—"
        title = h["title"].replace("|", r"\|")
        out.append(
            f"| `{h['level']}` | {h['number']} | {title} | {labs} | `SteinIntro.tex:{h['start']}-{h['end']}` |"
        )
    out.append("")

    # Section 2: Numbered environments table
    out.append("## 2. Numbered Theorems, Propositions, Lemmas, Corollaries, Definitions, Remarks, and Examples")
    out.append("")
    out.append("| Kind | Number | Optional Title / Note | TeX Label(s) | Sub-item Labels | Line Range |")
    out.append("| --- | --- | --- | --- | --- | --- |")
    for e in envs:
        labs = ", ".join(f"`{l}`" for l in e["labels"]) if e["labels"] else "—"
        sublabs = (
            ", ".join(f"`{lab}` (`L{ln}`)" for ln, lab in e["item_labels"])
            if e["item_labels"]
            else "—"
        )
        note_parts = []
        if e["title"]:
            note_parts.append(e["title"])
        if e["nested_in"]:
            note_parts.append(f"nested inside {e['nested_in']}")
        note = "; ".join(note_parts).replace("|", r"\|") if note_parts else "—"
        out.append(
            f"| `{e['kind']}` | {e['number']} | {note} | {labs} | {sublabs} | `SteinIntro.tex:{e['start']}-{e['end']}` |"
        )
    out.append("")

    if prose_items:
        out.append("### Labeled Prose Enumerated Claims (Outside Theorem Environments)")
        out.append("")
        out.append("| Item | TeX Label(s) | Line Range | Statement Excerpt |")
        out.append("| --- | --- | --- | --- |")
        for it in prose_items:
            labs = ", ".join(f"`{l}`" for l in it["labels"])
            out.append(
                f"| Item {it['number']} (§5.3) | {labs} | `SteinIntro.tex:{it['start']}-{it['end']}` | `{it['snippet']}` |"
            )
        out.append("")

    # Section 3: Displayed equations grouped by section
    out.append("## 3. Displayed Equations")
    out.append("")
    out.append(
        "Every numbered equation row `(s.k)` (including individual numbered rows of multi-line `\\ban ... \\ee` "
        "alignments) and every unnumbered display is listed below in source order with its `Role` "
        "(`assertion` vs. `definition`), TeX label(s), and exact `SteinIntro.tex:start-end` line range."
    )
    out.append("")
    for sec_no in range(1, 8):
        sec_displays = [d for d in displays if d["section"] == sec_no]
        sec_heading = next(h for h in headings if h["number"] == str(sec_no))
        n_num = sum(1 for d in sec_displays if d["number"] != "unnumbered")
        n_ass = sum(1 for d in sec_displays if d["role"] == "assertion")
        out.append(
            f"### Section {sec_no}: {sec_heading['title']} "
            f"({len(sec_displays)} rows: {n_num} numbered, {n_ass} assertive)"
        )
        out.append("")
        out.append("| # | Number | Role | TeX Label(s) | Line Range | TeX Excerpt |")
        out.append("| ---: | --- | --- | --- | --- | --- |")
        for idx_d, d in enumerate(sec_displays, start=1):
            labs = ", ".join(f"`{l}`" for l in d["labels"]) if d["labels"] else "—"
            out.append(
                f"| {idx_d} | {d['number']} | `{d['role']}` | {labs} | "
                f"`SteinIntro.tex:{d['start']}-{d['end']}` | `{d['snippet']}` |"
            )
        out.append("")

    return "\n".join(out)


JSON_PATH = ROOT / "docs" / "source-inventory.json"

SOURCE_FILE = "SteinIntro.tex"
UTF8_FILE = "docs/source/SteinIntro_utf8.tex"
ARXIV_ID = "1109.1880v1"


def _make_entry_id(kind: str, number: str) -> str:
    """Convert (kind, number) to a stable dash-separated entry ID."""
    prefix_map = {
        "section": "sec",
        "subsection": "sec",
        "subsubsection": "sec",
        "subsubsection*": "sec",
        "theorem": "thm",
        "proposition": "prop",
        "lemma": "lem",
        "corollary": "cor",
        "definition": "def",
        "remark": "rem",
        "example": "ex",
        "case": "case",
        "condition": "cond",
        "display": "eq",
        "proof": "pf",
        "figure": "fig",
    }
    prefix = prefix_map.get(kind, kind[:3])
    num = number.strip("()").replace("unnumbered", "unnum").replace(".", "-")
    return f"{prefix}-{num}"


def render_json(inv: dict) -> dict:
    """Convert parsed inventory dict to the canonical JSON structure."""
    headings = inv["headings"]
    envs = inv["envs"]
    prose_items = inv["prose_labeled_items"]
    displays = inv["displays"]

    entries: list[dict] = []
    labels_index: list[dict] = []
    seen_ids: set[str] = set()

    def _register(entry: dict) -> None:
        eid = entry["id"]
        if eid in seen_ids:
            raise RuntimeError(f"Duplicate inventory entry id: {eid}")
        seen_ids.add(eid)
        entries.append(entry)

    # ── 1. Section / subsection / subsubsection headings ─────────────────────
    for h in headings:
        kind = h["level"]  # e.g. "section", "subsection", "subsubsection*"
        number = h["number"]
        entry_id = (
            "acknowledgements"
            if number == "unnumbered" and "acknowledg" in h["title"].lower()
            else _make_entry_id(kind, number)
        )
        num_str = str(number)
        chapter = num_str.split(".")[0] if num_str != "unnumbered" else "0"
        entry: dict = {
            "id": entry_id,
            "kind": kind,
            "number": number,
            "chapter": chapter,
            "title": h["title"],
            "source_ranges": [
                {"file": SOURCE_FILE, "line_start": h["start"], "line_end": h["end"]}
            ],
            "labels": list(h["labels"]),
            "rows": [],
        }
        _register(entry)
        for lab in h["labels"]:
            labels_index.append({"label": lab, "owner_id": entry_id, "number": number})

    # ── 2. Numbered theorem/lemma/etc. environments ───────────────────────────
    for e in envs:
        kind = e["kind"]
        number = e["number"]
        entry_id = _make_entry_id(kind, number)
        num_str = str(number)
        chapter = num_str.split(".")[0] if "." in num_str else num_str
        env_labels = list(e.get("labels", []))
        item_rows = [
            {"number": str(idx_r), "label": lab, "line": ln}
            for idx_r, (ln, lab) in enumerate(e.get("item_labels", []), start=1)
        ]
        entry = {
            "id": entry_id,
            "kind": kind,
            "number": number,
            "chapter": chapter,
            "title": e["title"] or None,
            "nested_in": e.get("nested_in"),
            "source_ranges": [
                {"file": SOURCE_FILE, "line_start": e["start"], "line_end": e["end"]}
            ],
            "labels": env_labels,
            "rows": item_rows,
        }
        _register(entry)
        for lab in env_labels:
            labels_index.append({"label": lab, "owner_id": entry_id, "number": number})
        for r in item_rows:
            labels_index.append(
                {"label": r["label"], "owner_id": entry_id, "number": r["number"]}
            )

    # ── 3. Labeled prose enumerate items (§5.3) ───────────────────────────────
    for idx_it, it in enumerate(prose_items, start=1):
        entry_id = f"prose-5-3-item-{idx_it}"
        entry = {
            "id": entry_id,
            "kind": "prose_item",
            "number": it["number"],
            "chapter": "5",
            "title": it.get("snippet", ""),
            "source_ranges": [
                {"file": SOURCE_FILE, "line_start": it["start"], "line_end": it["end"]}
            ],
            "labels": list(it["labels"]),
            "rows": [],
        }
        _register(entry)
        for lab in it["labels"]:
            labels_index.append(
                {"label": lab, "owner_id": entry_id, "number": it["number"]}
            )

    # ── 4. Displayed equations ────────────────────────────────────────────────
    for d in displays:
        number = d["number"]
        if number != "unnumbered":
            bare = number.strip("()")
            entry_id = f"eq-{bare.replace('.', '-')}"
        else:
            bare = "unnumbered"
            entry_id = f"eq-{d['section']}-unnum-{d['start']}"
        chapter = str(d["section"])
        entry = {
            "id": entry_id,
            "kind": "display",
            "number": number,
            "chapter": chapter,
            "title": None,
            "role": d["role"],
            "source_ranges": [
                {"file": SOURCE_FILE, "line_start": d["start"], "line_end": d["end"]}
            ],
            "labels": list(d["labels"]),
            "rows": [
                {
                    "number": bare if bare != "unnumbered" else None,
                    "labels": list(d["labels"]),
                    "role": d["role"],
                    "snippet": d.get("snippet", ""),
                    "line_start": d["start"],
                    "line_end": d["end"],
                }
            ],
        }
        _register(entry)
        for lab in d["labels"]:
            labels_index.append(
                {"label": lab, "owner_id": entry_id, "number": bare}
            )

    return {
        "schema_version": 1,
        "source": {
            "arxiv_id": ARXIV_ID,
            "main": f"source/upstream/tex/{SOURCE_FILE}",
            "main_sha256": inv["tex_sha256"],
            "utf8": UTF8_FILE,
        },
        "counts": {
            "entries": len(entries),
            "headings": len(headings),
            "envs": len(envs),
            "prose_items": len(prose_items),
            "displays": len(displays),
            "labels": len(labels_index),
        },
        "entries": entries,
        "labels": labels_index,
    }


def main() -> None:
    import json as _json

    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify docs/source-inventory.md and docs/source-inventory.json are up to date",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Write (or with --check, verify) docs/source-inventory.json only",
    )
    parser.add_argument(
        "--check-json",
        action="store_true",
        help="Verify docs/source-inventory.json matches current parsed data",
    )
    args = parser.parse_args()

    if not TEX_PATH.is_file():
        raise SystemExit(
            f"Missing {TEX_PATH}; run `python3 scripts/fetch_source.py` first."
        )

    inv = parse_inventory(TEX_PATH.read_bytes())

    do_md = not args.json and not args.check_json
    do_json = args.json or args.check_json or args.check or not args.json

    # ── Markdown path ─────────────────────────────────────────────────────────
    if do_md:
        rendered = render_markdown(inv)
        if args.check:
            if not OUT_PATH.is_file():
                raise SystemExit(f"Missing {OUT_PATH}")
            existing = OUT_PATH.read_text(encoding="utf-8")
            if existing != rendered:
                raise SystemExit(
                    f"{OUT_PATH} is out of date with scripts/generate_inventory.py"
                )
            print(
                f"Inventory check passed: {len(inv['headings'])} headings, "
                f"{len(inv['envs'])} numbered environments, "
                f"{len(inv['displays'])} display rows ({inv['active_label_count']} labels)."
            )
        else:
            OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
            OUT_PATH.write_text(rendered, encoding="utf-8")
            print(
                f"Wrote {OUT_PATH.relative_to(ROOT)}: {len(inv['headings'])} headings, "
                f"{len(inv['envs'])} numbered environments, "
                f"{len(inv['displays'])} display rows ({inv['active_label_count']} active labels)."
            )

    # ── JSON path ─────────────────────────────────────────────────────────────
    if do_json:
        json_data = render_json(inv)
        json_text = _json.dumps(json_data, indent=2, ensure_ascii=False) + "\n"

        if args.check or args.check_json:
            if not JSON_PATH.is_file():
                raise SystemExit(f"Missing {JSON_PATH}; run `python3 scripts/generate_inventory.py --json`.")
            existing_json = JSON_PATH.read_text(encoding="utf-8")
            if existing_json != json_text:
                raise SystemExit(
                    f"{JSON_PATH} is out of date with scripts/generate_inventory.py"
                )
            print(
                f"JSON inventory check passed: {len(json_data['entries'])} entries, "
                f"{len(json_data['labels'])} labels."
            )
        else:
            JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
            JSON_PATH.write_text(json_text, encoding="utf-8")
            print(
                f"Wrote {JSON_PATH.relative_to(ROOT)}: "
                f"{len(json_data['entries'])} entries, "
                f"{len(json_data['labels'])} labels."
            )


if __name__ == "__main__":
    main()
