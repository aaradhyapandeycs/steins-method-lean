# Review: batch-CANON-phase2b (Mathlib follow-up bridges)

Commit reviewed: `aa325ce` plus the lead's uncommitted polish of `Formalization/Canon/Followups.lean`
(corrected line citations, `Dirac.Basic` import, removal of `set_option linter.deprecated false`,
`Measure.ext_of_singleton` in `rademacherPairMeasure_eq_prod`), committed together with this review.

Verdict: **ACCEPTED.** All eight bridges required by review-CANON-phase2 are proved; none is recorded as KEEP.

1. `wassersteinDist_eq_iSup_lipschitz_one`: finite first moments, unconditioned 1-Lipschitz supremum.
2. `isExchangeablePair_iff_map_swap`, `isExchangeableTuple_fin_two_iff_isExchangeablePair`
   (plus `isExchangeablePair_iff_map_eq`).
3. `isSizeBias_iff_map_eq_withDensity`: both directions. Hypotheses: `X` measurable, a.s. non-negative,
   integrable, positive mean (the latter three are the definition's own side conditions or the setting
   of `SteinIntro.tex:1224-1230`); no hidden assumptions on `Xs` beyond the a.e.-measurability that
   appears in the conclusion.
4. `poissonLaw_real_singleton_eq_poissonPMFReal`; 5. `rademacherPairMeasure_eq_prod`;
6. `gwTreeGenSize_eq_card_gwVertex`; 7. `subgraphCount_eq_card_filter_le`;
8. `erdosRenyi_eq_binomialRandom_of_mem_Icc` (for `p ∈ [0,1]`, the range where Mathlib's law is defined).

Evidence (critic, local, CRITIC-HOLD held):
- `lake build`: success (3598 jobs). `lake env lean Audit.lean`: axiom audit passed for 7113 project declarations.
- `Formalization/Canon/Followups.lean` elaborates with 0 errors and 0 warnings.
- Axiom probes for all 10 public theorems: `[propext, Classical.choice, Quot.sound]` only.
- Statement index: no change to `Formalization/Statements/` since `7cafdf2`.
- Docstring citations spot-checked against `SteinIntro.tex` (516-519, 952-960, 1224-1230, 1823-1848,
  2148-2154, 2993-3001, 919, 1355).
- Mutation controls (each fails semantically):
  - Wasserstein bridge with the moment hypothesis on `ν` removed: application type mismatch.
  - Size-bias density `x / E[X]` replaced by `x / (2 E[X])`: type mismatch against
    `map_sizeBias_eq_withDensity` (first run hit the default heartbeat limit; rerun with a raised limit).
  - `Prod.swap` invariance replaced by a wrong pushforward `(W', W')`: unsolved goals.
