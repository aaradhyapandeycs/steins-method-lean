# Statement review: SWEEP-B (§3 prose-claim sweep, `docs/tracks/SWEEP-B.md`)

- **Critic:** Claude, 2026-11-11.
- **Method:** an independent read-only pass with numerical checks. The critic re-checked the two most serious findings against the TeX:
  - L1045 prints ‖f″‖·E|W′−W|³/(6a), not the sweep's ‖f″‖/(4a);
  - "First follow Corollary" does not occur in the source.

## Verdict: returned for revision

**Several "verbatim" quotes are paraphrased or invented. This is a process failure.**
- Every quote in a sweep must be copied from `docs/source/SteinIntro_utf8.tex` at the cited lines, character for character.
- A drafted entry built on a misquote is not reviewable.
- The sweep also claims L685–1815, which overlaps SWEEP-A's L347–949.

| Item | Verdict |
|---|---|
| B1–B6, S1–S6, T1–T2 | **reject**: SWEEP-A's range (L347–949). B1(1) is also false: for h = \|·\|, f_h′ is not differentiable at 0. |
| B7a (display (3.18), L1044–1046) | approve with change SB-2 |
| B7b (L1095–1096) | status line (hedged remark; the typo is already ISSUE-TYPO-3.5) |
| B8 (anti-voter non-reversible, L1130–1131) | approve with change SB-4. True: on the prism K₃□K₂, P(x,y) = 1/6 while P(y,x) = 0. |
| B9a, B9b (L1389–1392, L1422–1425) | status lines (proof steps of `Ex3_9_moments` and `Thm3_17`) |
| B10 (L1512–1513) | **approve** (general claim inside the proof of Prop 3.19; true) |
| S7, S12, S15 | approve |
| S8–S11, S13, S14 | approve once the quotes are made verbatim (SB-6) |
| T3, T5, T6 | **reject** (duplicates or not a typo) |
| T4 (L1304, L1306) | approve as a new ISSUE-TYPO: `W` should be the sum `X`, with the real quote |

## Required changes

- **SB-1. Scope.** Restrict to L950–1815 and delete B1–B6, S1–S6 and T1–T2.
- **SB-2. B7a.** Quote L1045 exactly. Index the printed **function-level** inequality (3.18) as `Sec3_3_eq3_18`:
  - for an a-Stein pair (W, W′) and f with bounded f, f′, f″, |E[f′(W) − Wf(W)]| ≤ ‖f′‖·E|1 − E[(W′−W)²|W]/(2a)| + ‖f″‖·E|W′−W|³/(6a);
  - write the cubic term as an ℝ≥0∞ lintegral, so that a non-L³ increment gives ⊤ rather than the junk value 0;
  - the reviewer's draft is in the critic's notes and can be supplied on request.

  If the d_W corollary is also kept, use the coefficient 1/(3a).
- **SB-4. B8.** Do not depend on uniqueness. State: there is a stationary law, and **every** stationary law violates detailed balance at some (x, y).
- **SB-5. B9.** Status lines only.
  - Replace the invented first sentence with the real L1389.
  - The lemma path is `Formalization/RandomGraph/IsolatedMoments.lean:511`.
- **SB-6. Verbatim quotes.** Re-copy S7–S14 from the TeX. The specific errors:
  - **S9:** "coalescing random walks" is not in the text; the range is L1216–1217.
  - **S10:** the two quotes are swapped or invented.
  - **S14:** there is no `\ref{prop83}`.
  - **S7:** the stated reason is wrong. L1076–1077 is about expressing E|Xᵢ − Xᵢ′|³ through lower moments.
- **SB-7. Typos.** Keep T4, with the real quote from L1304/L1306. Delete T3, T5 and T6.
- **SB-8. Missing status lines.**
  - L1206–1207, L1516–1518, L1576–1577, L1676 and L1432–1433;
  - the heuristics at L1231–1232, L1450–1452, L1565, L1696, L1706–1710, L1748 and L1766–1767;
  - the trivial typo "labal" at L1159.

No uncovered substantive claim was found in L950–1815 beyond B7a, B8 and B10.

## Re-review of the revised SWEEP-B (2026-11-11, 19:35 EST): approved with minor changes

All of SB-1 to SB-8 are applied. All 39 fenced TeX quotes were checked by script against the cited line ranges and match exactly.

The approved entries:
- `Sec3_3_eq3_18`, display (3.18): cubic term ‖f″‖·E|W′−W|³/(6a) as an ℝ≥0∞ lintegral;
- its d_W corollary, with coefficient 1/(3a);
- `Sec3_3_1_antiVoter_not_reversible`;
- `Sec3_5_identDistrib_of_integral_deriv_compactSupport`.

Each is mathematically sound and free of junk values. None duplicates an existing entry.

Remaining changes:
- Copy the two T4 inline quotes exactly: L1308 `\IE[X_i f(\textbf{X})]=\mu_i\IE[f(\textbf{X}^i)]` and L1297 `X=\sum_{i=1}^n X_i`.
- Use the heading `### `ISSUE-TYPO-3.14` — …`.
- Optional: note that `G.Connected` in B8 goes beyond the printed hypotheses (harmless, since the statement is existential).
- The drafts' elaboration has not been verified yet. Compile them before integration.
