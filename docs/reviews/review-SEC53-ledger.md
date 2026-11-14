# Critic review: ledger repair for 14 compiled entries (Section 5.3 and others)

Verdict: **ACCEPTED**, with a disclosed ledger error corrected.

## What was wrong

All 243 statement entries have compiled `_holds` proofs, but 14 of them were not named in the
Lean-entry column of COVERAGE.md. The reader site therefore showed them as "open", even though
dependent results that use them were shown as proved. Nathan Ross noticed this on the Section 5.3
page. The COVERAGE status line already counted all 243 entries as critic-accepted, so for the
three entries listed under (b) below that line overstated the review state until this review.

(a) Eleven entries had already been reviewed and accepted, but never recorded in COVERAGE:
- `Sec3_5_1_zeroBias_of_steinPair`, `Sec3_6_1_indepSum_kolmogorov`, `Sec3_6_1_combinatorial_kolmogorov`,
  `Sec3_6_2_indepSum_kolmogorov`, `Sec3_6_2_antiVoter_kolmogorov`: review-EXER (ACCEPTED), with
  crosscheck-XC-A and crosscheck-XC-B reporting all items OK.
- `Sec5_1_equilibrium_rhs_wellDefined`, `Sec5_3_scaled_Yn_mean_gt_one_witness`, `Ex7_4_2_order`,
  `Sec7_eq7_4`: review-05F-followup-SWEEP-E-05G4-followup (ACCEPTED); `Ex7_4_2_order` and `Sec7_eq7_4`
  also in review-05F.
- `Ex5_4_weak_conv`: named in the Example 5.4 note (review-05D) but not in the Lean-entry column.
- `Sec5_3_exists_isSizeBiasSpineCoupling`: reviewed in review-05I as a dependency of Theorems 5.8 and
  5.9. Follow-up 1 there (a trailing tautology) has since been removed: the statement now ends with
  `IsSizeBiasSpineCoupling P Z P' n X L R R' U`.

(b) Three entries had never been reviewed. They are reviewed here:
- `Sec5_3_gwProb_sum_genSize` (`SteinIntro.tex:3047-3048, 3074-3076`): summing G_n(t) over depth-n
  planar trees with t_n = k gives P(Z_n = k), and the G_n(t) sum to 1. This matches the source's
  description of G_n(t) as the probability that the Galton–Watson tree agrees with t up to
  generation n. The proof constructs the random planar tree `gwTreeOfArray` from the i.i.d.
  offspring array and proves `measureReal_gwTreeOfArray_eq_gwProb`, so P(T_n = t) = G_n(t).
- `Sec5_3_gwSizeBiasProbV_sum_spine` (`SteinIntro.tex:3047-3056, 3070-3079, 3100-3101`): the
  size-biased planar-tree probabilities G_n^s(t, v), defined by the printed recursion, sum to the
  spine joint law of (S_n, L_n) and to P(S_n = k), and they are normalized.
- `Sec5_3_exists_isGaltonWatson_pos_var`: a non-vacuity witness (offspring law ½δ₀ + ½δ₂).

## Evidence (critic, local)

- Axiom probes: the `_holds` theorems of all five Section 5.3 entries depend only on
  `[propext, Classical.choice, Quot.sound]`.
- Dependency closure, computed with a Lean metaprogram over the environment:
  `Thm5_8_restricted_holds` and `Thm5_9_restricted_holds` both use
  `sec5_3_exists_isSizeBiasSpineCoupling` and `sec5_3_item_1`, so the coupling is constructed inside
  their proofs, not assumed. Neither uses `sec5_3_gwProb_sum_genSize`. The planar-tree links are
  fidelity checks against the source's tree formulas, not inputs to those theorems.
- Mutation controls, each in a copy of the library file, all rejected:
  - `Sec5_3_gwProb_sum_genSize_stmt` with P(Z_n = k) replaced by P(Z_{n+1} = k): unsolved goals.
  - `Sec5_3_gwSizeBiasProbV_sum_spine_stmt` with L_n = m replaced by L_n = m + 1: the proof's rewrite
    no longer matches.
  - `Sec5_3_item_1_stmt` with "S_n is size-biased for Z_n" replaced by Z_{n+1}: `assumption` fails,
    plus 2 further errors.
- Statement bodies are unchanged. Only COVERAGE.md and the reader site's status display change.

## Site change

An entry with a compiled `_holds` proof that the critic has not yet accepted is now labeled
"proved in Lean, review pending", not "open". Its card states that the proof compiles and passes
the axiom audit but that the statement has not been checked against the source. "Open" is now
used only for entries with no proof.
