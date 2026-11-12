# Critic review: batch-05F-followup (cf897fe), batch-SWEEP-E (0ff8bf9), batch-05G4-followup (fb0c3eb)

Verdict: **ACCEPTED** (all three).

Verified at HEAD bfe0e52 (clean Formalization tree), under `.locks/CRITIC-HOLD`:

- `lake build`: success (3561 jobs). `lake env lean Audit.lean`: axiom audit passed for 6694 declarations.
- Re-elaborated `Formalization/Concentration/Followups.lean`, `Formalization/Sweep/SweepE1.lean`, and
  committed `Statements/Sec5`, `Sec5Proofs`, `Sec7`, `Sec7Proofs`: 0 errors.
- Probes (`example : E := E_holds` + `#print axioms`) for Ex7_1, Ex7_2, Ex7_4_2_order, Sec7_eq7_4,
  Ex7_5_steinPair_restricted, Sec7_curieWeiss_mode, Sec5_1_equilibrium_rhs_wellDefined,
  Sec5_3_scaled_Yn_mean_gt_one_witness, Ex4_15_asymptotic_ineq, Ex4_15_rate, Ex4_15_restricted:
  all depend only on [propext, Classical.choice, Quot.sound].
- Mutations (all rejected by Lean):
  - Followups.lean L58: limit `Real.exp (2 * μ)` -> `Real.exp μ`: application type mismatch.
  - SweepE1.lean witness: `1 < ∫ ...` -> `(∫ ...) < 1`: rewrite failure in proof (a first attempt
    without parentheses only failed to parse and was discarded as non-evidence).
  - CouponUniform.lean L695: `k / (n(n-2))` -> `k / (n(n-1))` (false at n = 3): type mismatch.

Fidelity:

- `Ex7_4_2_order`: exp(-t²/(2μ+t))/e^{-t} = exp(2μt/(2μ+t)) -> e^{2μ} > 0 formalizes "of the order
  e^{-t}" at L3528 for constant μ ≥ 0.
- `Sec7_eq7_4`: cleared-denominator form of display (7.4) at L3549-3552 (`\label{2212a}`), valid for
  all x, y (the printed form needs x > y only to divide).
- `Ex7_5_steinPair_restricted` now covers n ≥ 2 for E[W] = 0, exchangeability and the regression
  identity, keeping the Stein-pair `a ≤ 1` conclusion at n ≥ 3 only; a strengthening.
- `Sec7_curieWeiss_mode` h = 0 clause assumes β > 0; strict dominance of the constant configurations
  is then correct.
- `Sec5_3_scaled_Yn_mean_gt_one_witness` is an explicit-witness existence statement supporting
  ISSUE-5.9-PROOF-MEAN; it does not replace any printed claim.
- Ex 4.15 bounds: identity and upper bound strengthened from n ≥ 3 to n ≥ 2; log bounds kept at n ≥ 3.
- Remark 4.17 docstring: at n = 3, k = 1, m = 1, p uniform, Thm 4.14's bound is
  Var W − λ + 2Σq_i² = 0 − 1 + 2/3 = −1/3, as stated (docstring only; the Lean refutation uses n = 2).

Statement index: 232 -> 236 accepted entries (47 corrected/restricted); numbered coverage unchanged at 121/122.
