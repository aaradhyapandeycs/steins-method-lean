# Statement review: SWEEP-C (§4.1–4.2 and §6, prose-claim sweep, `docs/tracks/SWEEP-C.md`)

- **Critic:** Claude, 2026-11-11.
- **Method:** an independent read-only pass.
  - Every TeX quote was confirmed verbatim.
  - D-C3 was checked at 250-digit precision.
  - D-C5 was checked over every 0/1 sequence with n ≤ 10.
  - D-E2, D-E4 and D-E5 were checked with exact rationals for n ≤ 6.

## Verdict: approved with changes SC-1 to SC-7

**Rule applied.** A claim inside a proof that the library already formalizes, even in another encoding, gets a status line that cites the library declaration. It does not get a duplicate entry (AGENTS rule 10, ruling P1).

| Item | Verdict |
|---|---|
| D-C1 (L1871–1875), D-C2 (L1875–1876) | status lines: this is the route of `Lem4_1_2` (`map_eq_poissonLaw_of_integral_poissonSteinOp_eq_zero`) and an alternative-proof pointer |
| D-C3 (L1889–1899) | approve with SC-2: the sign of f_j, Δf_j(j) ≥ 0 and Δf_j(j) ≤ 1/j go beyond the needs of `Lem4_4`'s proof; all verified |
| `not_Sec4_0_fwdDiff_f0_neg_printed` (L1899) | approve with SC-2 (rename). Δf₀(0) = (1 − e^{−λ})/λ > 0. |
| D-C4 (L1899–1907) | status line: `poissonSteinSol_union`, `poissonSteinSol_compl`, `fwdDiff_poissonSteinSol_le` |
| D-C5 (L2006–2023) | approve with SC-5: ties the printed "number of head runs" to `headRunCount` |
| D-C6 (L2040–2048) | status line: proof steps inside `tvDist_headRunCount_le`; no `_corrected` suffix |
| D-E1 (L3342–3343) | **approve** (cited claim; follows from `Thm6_6`) |
| D-E2–D-E5 (L3353–3385) | status lines. They are the library's own proof route (`swapTargetEquiv`, `integral_zeroTailCount_step`, `sum_ByParts_fin`, `uniformAttachment_inDegree_equilibrium_coupling`). The §2.1 note claiming the library "bypasses" Ross's route is wrong; delete it. |
| S-C1–S-C12 | approve |
| S-E1–S-E8 | approve with SC-6 and SC-7 |

## Required changes

- **SC-1.** Reclassify D-C1, D-C2, D-C4, D-C6 and D-E2–D-E5 as status lines that cite the declarations above. Update S-E8, the §2.1 note and the summary counts.
- **SC-2. Names.**
  - `Sec4_poissonSteinSol_pointMass_corrected` (no `_0`).
  - `not_Sec4_fwdDiff_f0_neg_printed`.
  - Optional: drop conjunct (1), the L1891 rewrite, which is only algebra.
- **SC-3. ISSUE-4.4-PROSE** (Part III, prose note). "Δf₀(k) < 0" fails at k = 0 and holds strictly for k ≥ 1. `Lem4_4` is unaffected. Add one sentence: at k = 0 with 0 ∈ A, the positive term Δf₀(0) attains the bound (1 − e^{−λ})/λ exactly. The printed bullets cover only j ≥ 1.
- **SC-4. ISSUE-TYPO-4.8.**
  - Delete the remark that dropping min{1, λ⁻¹} is an error. It is a valid weakening.
  - Note that, under the natural convention Xᵢ ≡ 0 for i > n − k + 1, the printed sum to n has the same value. The typo is cosmetic: keep it as a Part I typo only.
- **SC-5. D-C5.**
  - Use `{im : ℕ × ℕ | …}`, not `{(im : ℕ × ℕ) | …}`. The parenthesised form triggers Mathlib's pattern-matching set-builder.
  - The reading note is wrong as written: the identity also holds at k = 0. Keep `1 ≤ k` as the source's domain, not as a condition needed for truth.
- **SC-6.** Status-line pointers must cite declaration names, not line numbers, which have drifted.
- **SC-7. New entry `Sec6_3_not_exponential` (missed claim, L3211–3212).** The text says uniform attachment is "an example … where exponential approximation does not hold".
  - E[Wₙ] = 1 and P(Wₙ = 0) = (n − 1)/(2n). This was checked exactly for n ≤ 6, and it telescopes in general.
  - So d_K(L(Wₙ), Exp(1)) ≥ (n − 1)/(2n) ≥ 1/4 for every n ≥ 2, and the distance does not tend to 0.
  - State the exact P(Wₙ = 0) and the d_K lower bound.
  - Also add a status line for the heuristic at L3193–3194 ("we expect that W will be approximately geometrically distributed").
