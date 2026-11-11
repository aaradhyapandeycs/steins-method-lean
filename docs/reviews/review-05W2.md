# Critic review 05W2: Track W fixes W-1 to W-5, `d9b4055`

- **Critic:** Claude, 2026-11-11.

## Verdict

**ACCEPTED. W-1 to W-5 are resolved.** Two small fixes, W2-1 and W2-2, are required before the public push; neither blocks preparing the release. The release plan now goes to the owner (ruling R3).

## What I ran

| Check | Result |
|---|---|
| `python3 site/build.py --rev HEAD` | exit 0, 1.7 s. There are 6 warnings, all "k rows vs 1 inventory rows; numbers omitted" for multi-row displays (cosmetic). |
| `python3 site/check_fidelity.py` | `FIDELITY OK`: PDF hash, 7/7 headings, 0 hygiene problems, 0 raw macros, **0 `??` or raw citation keys** |
| `python3 site/check_macros.py --build site/_build` | `MACROS OK` |
| `python3 scripts/export_public.py --preview <scratch>` | exit 0, 149 files, 0 lint findings |
| Independent scan of the export | no `<local>`, `<local>`, `<local>`, scratch area, <token>, product names or UUIDs; no `.tex`/`.pdf`/`.bbl`; no `sorry`/`admit`/`native_decide` in Lean; `review-00-setup.md` is excluded |
| `\eqref`/`\ref{` text in the HTML | only the MathJax macro table and issue titles that quote the source typos (expected) |

## W-1 to W-5

- **W-1.** The headline now reads "56 of 122 numbered results formalized (44 proved, 8 corrected, 4 restricted); 66 open", computed over the full inventory. Per-section lines follow the same rule. Compiled but unreviewed work is shown as "Lean WIP unreviewed" and is **not** counted.
- **W-2.** Cross-references resolve to printed numbers, and citations render author–year (e.g. "Aldous and Fill, 2010"). The build check now fails on `??` or raw keys.
- **W-3.** The markers are correct:
  - §3.3.1 and the §6 opening display show **source issue** with ✕ *refuted in Lean*;
  - Example 3.8 shows **exercise**;
  - all 75 entries are placed on their pages, with 0 unplaced.
- **W-4.** The README now says "every substantive claim in the running text" and "where feasible, a machine-checked refutation", and it contains no hard-coded counts.
- **W-5.** The allowlist excludes `review-00-setup.md`, and the shipped process wording is generic ("builder agents", "critic agents").

## Required before the public push

- **W2-1. Definition status.**
  - Accepted definitions show as **proved**. Use **defined**, or "formalized (definition)", for them.
  - Parse a COVERAGE row whose status begins "definition accepted" (Definition 6.1) as defined, not open. It currently shows as open, which is why the site says 56 where COVERAGE gives 57.
  - Count definitions under "formalized", with their own sub-count.
- **W2-2. README axiom sentence.** "depends on exactly the three … axioms … no others" should read "depends on no axioms other than `propext`, `Classical.choice` and `Quot.sound`". Some declarations use fewer than the three.

## Owner decisions to surface (not defects)

- The citation's `author` field is the GitHub handle `aaradhyapandeycs`, while the Lean file headers say "Aaradhya Pandey". The owner chooses which to use.
- The fresh-checkout build is verified by CI in the private repository before anything goes public (R3 step order).
