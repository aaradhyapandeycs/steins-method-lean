# Critic review: batch-CANON phase 2 (Formalization/Canon/*.lean)

Verdict: **ACCEPTED as delivered, with a required follow-up (batch-CANON-phase2b).**

Integration note: the lead agent was unresponsive (no step since 07:45Z), so the critic copied the CANON agent's
files verbatim from its worktree (<local> after verifying them there; no file content was
changed by the critic.

Scope: six new files in Formalization/Canon (55 declarations), `Formalization/Canon.lean`, and one import line in
`Formalization.lean`. No `Formalization/Defs` definition was replaced and no Statements file imports Canon, so every
statement entry is untouched (Defs unchanged since the worktree base).

Verification:
- Worktree and main repo: `lake build` success (3597 jobs); axiom audit passed for 7099 declarations.
- Each Canon file re-elaborates with 0 errors and 0 warnings.
- Axiom probes (only propext, Classical.choice, Quot.sound): `signedMeasure_totalVariation_univ_eq_two_mul_tvDist`,
  `kolmogorovDist_eq_iSup_cdf`, `erdosRenyi_eq_binomialRandom`, `isAntiVoterStationary_iff_kernel_invariant`,
  `klDivBernoulli_eq_klDiv`.
- Mutations rejected: TV factor `2 * tvDist` -> `tvDist` (unsolved goals); Kolmogorov bridge with `cdf ν` removed
  (type mismatch).
- Statements checked by the critic: Kolmogorov distance = sup_x |F_μ(x) − F_ν(x)| for probability measures;
  tvDist = sup over measurable sets (finite measures); Mathlib's total variation of μ − ν on univ = 2·tvDist
  (probability measures); Erdős–Rényi law = `SimpleGraph.binomialRandom`; anti-voter stationarity iff
  `Kernel.Invariant` of the anti-voter kernel; KL of Bernoulli laws = Mathlib `klDiv`.

Findings (follow-up required): the phase-1 plan listed bridges that were neither proved nor recorded as KEEP:
1. `wassersteinDist_eq_iSup_lipschitz_one` (finite first moments make the integrability side condition vacuous);
   only the definitional `wassersteinDist_eq_ipm_lipschitzWith_one := rfl` was delivered.
2. `isExchangeablePair_iff_map_swap` and `isExchangeableTuple_fin_two_iff_isExchangeablePair`.
3. `isSizeBias_iff_map_eq_withDensity`: only one direction (`map_sizeBias_eq_withDensity`) was delivered.
4. `poissonLaw_real_singleton_eq_poissonPMFReal`; 5. `rademacherPairMeasure_eq_prod`;
6. `gwTreeGenSize_eq_card_gwVertex`; 7. `subgraphCount_eq_card_filter_le`; 8. `erdosRenyi_eq_binomialRandom_of_mem_Icc`.
batch-CANON-phase2b must prove each or record it in canon-audit.md as KEEP with the precise obstruction.
