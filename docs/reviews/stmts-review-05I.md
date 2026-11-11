# Statement review: Track I (§5.3 critical branching, Yaglom), drafts in `docs/tracks/I.md`

- **Critic:** Claude, 2026-11-11.
- **Method:** a first-pass independent review, with exact-rational enumeration of the spine for three critical laws ({0,2}, {0,1,2}, {0,3}) at n ≤ 3–4, re-checked by the critic against the TeX (L3114–3146, L3165–3180).

## Verdict

The drafts are **approved with required changes I-1 to I-10.** The core statements match the source:
- `IsGaltonWatson` and the planar tree encoding;
- `Thm5_8_restricted` and `Thm5_9_restricted`, which disclose σ² > 0 and n ≥ 2;
- items 1–4 and (5.12);
- steps (i) and (ii).

The enumeration verified these exactly:
- P(S_n = k) = k·P(Z_n = k);
- P(L_n = m, S_n = k) = P(S_n = k)/k for m < k;
- (5.9);
- E S_n − 1 = nσ², E S_{n,j} = σ², and E Y_nᵉ = (nσ² + 1)/2.

## Required changes

- **I-1. Connect the two size-bias tree encodings.**
  - G_n and G_nˢ are defined by formula and recursion, so (5.7) and (5.8) are identities about those definitions. Say so; the claim at L3085–3092 is definitional.
  - No entry links `gwProb` to the generation-size law or `gwSizeBiasProbV` to the spine, which leaves L3074–3079 uncovered. Add:
    - (a) Σ over t with t_n = k of `gwProb p t` equals P(Z_n = k);
    - (b) the spine joint law P(S_n = k, L_n = m) is the matching sum of `gwSizeBiasProbV`;
    - (c) normalization of both.
  - Add a reading note: the spine is a law-level encoding of the generation-n data of the size-biased tree.
- **I-2. Non-vacuity with σ² > 0.** Every existing witness has σ² = 0 (Z ≡ 1), which never meets the hypotheses of Thm 5.8 or 5.9. Add existence entries:
  - an `IsGaltonWatson` process for a non-degenerate critical offspring law, e.g. {0, 2} with probabilities ½, ½;
  - `IsSizeBiasSpineCoupling` at every n for every critical Galton–Watson process with finite variance.

  The construction at L3030–3044 and L3128–3136 is itself an existence claim.
- **I-3. Drop hypotheses the TeX does not state.**
  - `Sec5_3_lpp_mean_diff_log`: drop σ² > 0. At σ² = 0, E\|Y_n − Y_nᵉ\| = ½ ≤ log n for n ≥ 2.
  - `Sec5_3_step_iii`: drop `0 < σsq`.
  - Split the o(n) claim out of `Sec5_3_kolmogorov_survival` into `Sec5_3_lpp_mean_diff_o_n`, which needs no σ² > 0.
- **I-4. n ≥ 2 in `Sec5_3_lpp_mean_diff_log` is a disclosed restriction.** At n = 1, Y₁ − Y₁ᵉ = U + (an integer), so E\|·\| > 0 = C·log 1 for every law. The printed claim at L3023 and L3141 fails at n = 1; extend ISSUE-5.9 to cover it and use the `_restricted` suffix.
- **I-5. σ² > 0 in the Kolmogorov limit at L3186** is a needed but added hypothesis: at σ² = 0, n·P(Z_n > 0) = n → ∞, and 2/σ² is undefined. Disclose it and cite a new ISSUE-5.8 (ill-defined at σ² = 0).
- **I-6. Printed error at L3143 (ISSUE-TYPO):** with Y_nᵉ = 1 + ΣR − U, the difference Y_n − Y_nᵉ is **U** + Σ(R′ − R)·1[L > 0], not 1 − U + …. It is harmless in expectation, since U and 1 − U have the same law. Record the typo and state the assembled bound with U.
- **I-7. Missed claim at L3024:** (cY_n)ᵉ =ᵈ c·Y_nᵉ "for any constant c". Cover it by citing Track D's scaling entry (c > 0), and disclose that c ≤ 0 fails under the literal `IsEquilibrium`.
- **I-8. Missed claim at L3158** (S_{n,j} and 1[L_{n,j} = 0] are negatively correlated) and the corrected chain at L3160–3163, E R′ = E[S \| L = 0] ≤ E S = σ². Add entries; Harris/FKG monotonicity is the natural route.
- **I-9. Printed error at L3176 (proof note).** E[R·1[L > 0] \| X_j] ≤ X_j·1[L > 0] is false as an almost-sure inequality, because the right-hand side is not σ(X_j)-measurable. Counterexample: Z₁ ∈ {0, 3} with probabilities (⅔, ⅓) and n − j = 1. Only the integrated inequality is true.
- **I-10. Refutations and the ledger.**
  - Draft the printed `Thm5_8` and `Thm5_9` Props.
  - `not_Thm5_9_printed` must refute the genuine n = 1 failure (with σ² > 0 and n ≥ 1), not the n = 0 junk case.
  - `not_Thm5_8_printed` refutes only the x/0 reading, so its docstring must say the printed statement is ill-defined at σ² = 0, not false.
  - Reconcile ISSUE-5.9's `_corrected` name with the `_restricted` used here, and add ISSUE-5.8.

## Also

- **ISSUE-5.9-proof.** Say explicitly that L3161 is false as written (on {L = 0}, R = S), and that L3163 should read E S_n − 1 = nσ².
- **Hygiene.** The I.md §3 tree definition must match the committed `def GWTree`. Fix the Basic.lean line citations: (5.7) is at L3054–3056, (5.8) at L3070–3072, and the size-bias positivity claim at L3077–3078.
- **Minor prose claims** (entry or status line): L3043–3044 (the tree is infinite), L3080–3081, L3122–3126 (L and R are not independent; witness Z₁ ∈ {0, 2}, j = n), L3154–3156.
- **Typos:** L3182 is missing ")", and L2998 has "of of".
