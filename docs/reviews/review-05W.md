# Critic review 05W: Track W (early public release: site, CI, README, export), `4f86dfa`

- **Critic:** Claude, 2026-11-11.

## Verdict

**NOT YET READY TO PUBLISH. Five required fixes (W-1 to W-5) remain.** The infrastructure is solid: the build, fidelity check and export all work. But the progress page currently overstates progress, so nothing goes public until W-1 is fixed.

## What I ran

| Check | Result |
|---|---|
| `python3 site/build.py --rev HEAD` | exit 0, 0.8 s, 1.0 MB site |
| `python3 site/check_fidelity.py` | `FIDELITY OK`: PDF hash OK; 7/7 section headings; 0 hygiene problems; 0 raw or undefined macros |
| `python3 scripts/export_public.py --preview <scratch>` | exit 0, 124 files, `0 lint findings` |
| Independent scan of the export | no `<local>`, `<local>`, `<local>`, scratch area or <token> strings; no conversation UUIDs; no `.tex`/`.pdf`/`.bbl`; no `sorry`/`admit`/`native_decide` in Lean; workflows present |
| Visual check in a browser (§3.3 page, results page) | WIP banner present; footer has the CC BY 4.0 attribution, commit, toolchain and CI link; maths renders; status badges link the Lean entries |

## Required fixes

- **W-1. The progress page overstates progress (blocking).**
  - It says "Of the 56 tracked results: 39 proved, 6 corrected, 4 restricted, 7 incomplete". The denominator is only the rows already in COVERAGE. The paper has **122 numbered results**, plus the tracked prose claims.
  - Compute counts over the **full inventory** (`docs/source-inventory.json`, 122 numbered environments) plus the prose items tracked in COVERAGE. Every inventory item without a COVERAGE row shows as *open (not yet reviewed)*.
  - Headline example: "42 of 122 numbered results proved (n corrected or restricted); m open". Never show a fraction of COVERAGE rows alone.
  - Follow the `lean-proof-status-display` skill (`reference/skills/…`).
- **W-2. Unresolved cross-references and citations.**
  - The build reports **137 unresolved labels**. Pages show "Theorem ??" (22 times on the §3.3 page alone).
  - Resolve `\ref{…}` and `\eqref{…}` to the printed numbers using `docs/source-inventory.json`, the way the RL reader does.
  - Citations render as raw keys, e.g. "(riro97, 1997)". Render author–year from `SteinIntro.bbl`, e.g. "Rinott and Rotar (1997)".
  - Add a build check that fails if any `??` or raw key appears.
- **W-3. Status vocabulary.**
  - Items that are source issues (for example "§3.3.1 prose (irreducibility)", which is refuted in Lean) must show a **source issue / refuted** marker, not "incomplete".
  - Exercises (Example 3.8) show **exercise**.
  - Results with a machine-checked `not_…_printed` get a refuted marker next to the corrected status.
  - Place the 8 "unplaced" prose-claim entries (`Sec3_dK_le_dW`, `Sec3_4_sizeBias_identity`, `Sec3_5_zeroBias_fixedPoint`, the Lindeberg entries, `Sec3_6_zeroBias_bdd_*`) on the page at their TeX line ranges.
- **W-4. README wording.**
  - "a disclosed _corrected or _restricted variant is formalized alongside a machine-checked refutation of the printed text" should read "…and, where feasible, a machine-checked refutation…". Typos and proof slips have no refutation.
  - "selected prose displays" should read "every substantive claim in the running text", which is the project's actual target.
- **W-5. Export contents.**
  - Exclude `docs/reviews/review-00-setup.md` from the allowlist. It contains an internal "Next prompt for …" section and process instructions.
  - Optional, for consistency with the RL repository: describe the process generically ("builder agents" and "critic agents") rather than by product name in the shipped review files. The critic's reviews mention tool names only in review-00.

After W-1 to W-5: rebuild, rerun the fidelity check and export lint, and hand off again as `batch-05W2`. The critic then re-checks and presents the release plan to the user. The plan is: create the repository privately, push the export, require CI green, then make it public and enable Pages. The user's go-ahead is needed for that.
