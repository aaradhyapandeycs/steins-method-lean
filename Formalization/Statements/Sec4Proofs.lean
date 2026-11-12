/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Poisson.SteinLemma
import Formalization.PoissonDep.ErdosRenyiCounterexample
import Formalization.PoissonDep.ErdosRenyiLaw
import Formalization.PoissonDep.HeadRunAsymptotics
import Formalization.PoissonDep.HeadRuns
import Formalization.PoissonDep.LocalDependence
import Formalization.PoissonExch.AuxLawSmallNumbers
import Formalization.PoissonExch.Basic
import Formalization.PoissonExch.FixedPoints
import Formalization.PoissonExch.FixedPointsMoments
import Formalization.PoissonExch.FixedPointsTrueRate
import Formalization.PoissonExch.Thm420
import Formalization.PoissonSizeBias.Core.DegreeD
import Formalization.PoissonSizeBias.Monotone.Examples
import Formalization.PoissonSizeBias.Negative.Basic
import Formalization.PoissonSizeBias.Negative.CouponNonUniform
import Formalization.PoissonSizeBias.Negative.CouponUniform
import Formalization.PoissonSizeBias.Negative.Ex416Coupling
import Formalization.PoissonSizeBias.Negative.Hypergeometric
import Formalization.PoissonSizeBias.Negative.Occupancy
import Formalization.PoissonSizeBias.Negative.Rem417Coupling
import Formalization.PoissonSizeBias.Subgraph.Increasing
import Formalization.Sweep.SweepC4
import Formalization.Sweep.SweepDIsolated
import Formalization.Sweep.SweepDMonotone
import Formalization.Sweep.SweepDPoissonExch
import Formalization.Statements.Sec4

/-!
# Section 4 Proof Wrappers (`Formalization.Statements.Sec4Proofs`)

Connects each `: Prop` entry in `Formalization.Statements.Sec4` to its library theorem in
`Formalization.Poisson.SteinLemma` (`AGENTS.md` Rule 5).
-/

namespace SteinMethod

/-- Lemma 4.1(1) (`\label{lem101}`, `SteinIntro.tex:1823-1830`) holds. -/
theorem Lem4_1_1_holds : Lem4_1_1 := by
  intro _ _ P _ _ _ hr hZ hmap _ hf
  exact integral_poissonSteinOp_eq_zero_of_map_eq P hr hZ hmap hf

/-- Lemma 4.1(2) (`\label{lem101}`, `SteinIntro.tex:1831-1835`) holds. -/
theorem Lem4_1_2_holds : Lem4_1_2 := by
  intro _ _ P _ _ _ hr hW hOp
  exact map_eq_poissonLaw_of_integral_poissonSteinOp_eq_zero P hr hW hOp

/-- Lemma 4.2 (`\label{lem102}`, `SteinIntro.tex:1837-1848`) holds. -/
theorem Lem4_2_holds : Lem4_2 :=
  fun {r} hr A ↦
    ⟨poissonSteinSol_zero r A,
      poissonSteinOp_poissonSteinSol hr A,
      fun _ hg0 hg ↦ eq_poissonSteinSol_of_poissonSteinOp_eq hr A hg0 hg⟩

/-- Corollary 4.3 (`\label{cor101}`, `SteinIntro.tex:1850-1855`) holds. -/
theorem Cor4_3_holds : Cor4_3 := by
  intro _ _ P _ _ _ A hr hW _ _
  exact abs_measureReal_sub_poissonLaw_eq P hr hW A

/-- Lemma 4.4 (`\label{lem103}`, `SteinIntro.tex:1879-1886`; `ISSUE-4.4`) holds. -/
theorem Lem4_4_holds : Lem4_4 :=
  fun hr A k ↦
    ⟨abs_poissonSteinSol_le hr A k,
      abs_fwdDiff_poissonSteinSol_le hr A k,
      one_sub_exp_neg_div_le_min hr⟩

/-- Proof of Lemma 4.4 point-mass solution properties, corrected at $j = 0, k = 0$
(`SteinIntro.tex:1889-1899`; `ISSUE-4.4-PROSE`) holds. -/
theorem Sec4_poissonSteinSol_pointMass_corrected_holds :
    Sec4_poissonSteinSol_pointMass_corrected :=
  sec4_poissonSteinSol_pointMass_corrected_proof

/-- Theorem 4.5 (`\label{thm101}`, eq. `(4.4)` `\label{1019}`, `SteinIntro.tex:1911-1916`) holds. -/
theorem Thm4_5_holds : Thm4_5 := by
  intro _ _ _ _ P _ P' _ _ _ _ hr hW hInt hMean hZ hlaw
  exact tvDist_map_le_iSup_poissonSteinClass P P' hr hW hInt hMean hZ hlaw

/-- Section 4.1 opening binomial limit (`SteinIntro.tex:1938-1939`) holds. -/
theorem Sec4_1_binomial_limit_holds : Sec4_1_binomial_limit := by
  intro _ _ P _ _ _ hX
  exact tendsto_tvDist_binomial_poissonLaw P hX

/-- Theorem 4.6 (`\label{thm102}`, `SteinIntro.tex:1942-1949`; `ISSUE-TYPO-4.6`) holds. -/
theorem Thm4_6_holds : Thm4_6 := by
  intro _ _ _ _ P _ P' _ _ hn _ _ _ hX hX01 hIndep hr hZ hlaw
  exact tvDist_sum_indep_indicator_le P P' hn hX hX01 hIndep hr hZ hlaw

/-- Theorem 4.7, corrected (`\label{thm103}`, `SteinIntro.tex:1970-1977`; `ISSUE-4.7`) holds. -/
theorem Thm4_7_corrected_holds : Thm4_7_corrected := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ hX hX01 hDep hNi hr hZ hlaw
  exact tvDist_sum_dep_indicator_le P P' hX hX01 hDep hNi hr hZ hlaw

/-- Remark 4.1 (`SteinIntro.tex:1978-1981`) holds. -/
theorem Rem4_1_holds : Rem4_1 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ hX hX01 hNi hr hZ hlaw
  exact tvDist_sum_indicator_condExp_le P P' hX hX01 hNi hr hZ hlaw

/-- Section 4.2.1 head-run de-clumping identity (`SteinIntro.tex:2006-2023`) holds. -/
theorem Sec4_2_1_headRun_declumping_holds : Sec4_2_1_headRun_declumping :=
  sec4_2_1_headRun_declumping_proof

/-- Theorem 4.8 (`\label{thm104}`, eq. `(4.8)` `\label{1011}`, `SteinIntro.tex:2024-2030`) holds. -/
theorem Thm4_8_holds : Thm4_8 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ _ hk1 hkn hp0 hp1 hY hY01 hIndep hYp hr hZ hlaw
  exact tvDist_headRunCount_le P P' hk1 hkn hp0 hp1 hY hY01 hIndep hYp hr hZ hlaw

/-- Remark 4.2 (`\label{re101}`, `SteinIntro.tex:2031-2038`; `stmts-review-05C` `C1`) holds. -/
theorem Rem4_2_holds : Rem4_2 :=
  headRun_mean_and_error_asymptotics

/-- Section 4.2.1 longest-run approximation (`SteinIntro.tex:2054-2061`) holds. -/
theorem Sec4_2_1_longestRun_holds : Sec4_2_1_longestRun :=
  longestRun_event_and_gumbel_approx

/-- Theorem 4.9, corrected (`[\ER\ Law]`, `SteinIntro.tex:2071-2078`; `ISSUE-4.9`) holds. -/
theorem Thm4_9_corrected_holds : Thm4_9_corrected := by
  intro _ _ P _ _ _ _ hp0 hpa ha1 hY hY01 hIndep hYp
  exact erdos_renyi_longestQualityRun_ae P hp0 hpa ha1 hY hY01 hIndep hYp

/-- Remark 4.3 (`SteinIntro.tex:2079-2110`) holds. -/
theorem Rem4_3_holds : Rem4_3 := by
  intro _ _ P _ _ _ _ _ hA hB hIA hIB hIAB hAq hBq
  exact ⟨(dna_match_iIndepFun_and_prob P hA hB hIA hIB hIAB hAq hBq).1,
    (dna_match_map_eq_pi P hA hB hIA hIB hIAB hAq hBq).1,
    (dna_match_iIndepFun_and_prob P hA hB hIA hIB hIAB hAq hBq).2⟩

/-- Theorem 4.10 (`\label{thm121}`, `SteinIntro.tex:2120-2127`) holds. -/
theorem Thm4_10_holds : Thm4_10 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hr hW hMean hSB hZ hlaw
  exact tvDist_poisson_le_of_isSizeBias P P' hr hW hMean hSB hZ hlaw

/-- Corollary 4.11 (`\label{cor121}`, `SteinIntro.tex:2142-2147`; `ISSUE-TYPO-4.11`) holds. -/
theorem Cor4_11_holds : Cor4_11 := by
  intro _ _ P _ _ _ _ _ hX_meas hX_zo
  exact sizeBias_sum_of_zero_one P hX_meas hX_zo

/-- Corollary 4.12 (`\label{cor122}`, `SteinIntro.tex:2148-2154`; `ISSUE-TYPO-4.12`) holds. -/
theorem Cor4_12_holds : Cor4_12 := by
  intro _ _ _ _ P _ P' _ _ hn _ _ hX hX01 hexch hY hcond
  exact sizeBias_sum_of_exchangeable_zero_one_fin P P' hn hX hX01 hexch hY hcond

/-- Example 4.4 (*Law of small numbers*, `SteinIntro.tex:2162-2172`) holds. -/
theorem Ex4_4_holds : Ex4_4 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ hX hX01 hindep _ _ _ hr hsum hI hI_prob hI_indep hZ hZ_law
  exact lawOfSmallNumbers_sizeBias_and_tvDist P P' hX hX01 hindep hr hsum hI hI_prob hI_indep
    hZ hZ_law

/-- Example 4.5 footnote comparison (`SteinIntro.tex:2181-2186`; `SD-4`) holds. -/
theorem Ex4_5_footnote_comparison_holds : Ex4_5_footnote_comparison :=
  ex4_5_footnote_comparison

/-- Example 4.5 coupling and $L^1$ increment calculation (`\label{ex122}`,
`SteinIntro.tex:2189-2207`) holds. -/
theorem Ex4_5_coupling_holds : Ex4_5_coupling := by
  intro _ _ P _ _ hn _ _ hp0 hp1 hG hG_law
  exact isolatedVertices_coupling P hn hp0 hp1 hG hG_law

/-- Proposition 4.13 (`SteinIntro.tex:2208-2214`, nested in Example 4.5) holds. -/
theorem Prop4_13_holds : Prop4_13 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ hn hp0 hp1 hG hG_law _ hr hZ hZ_law
  exact isolatedVertices_tvDist_poisson P P' hn hp0 hp1 hG hG_law hr hZ hZ_law

/-- Example 4.5 asymptotic interpretation (`SteinIntro.tex:2215-2217`) holds. -/
theorem Ex4_5_asymptotics_holds : Ex4_5_asymptotics :=
  fun hp hc1 hlam ↦ isolatedVertices_asymptotics hp hc1 hlam

/-- Example 4.6 (*Degree $d$ vertices*, `SteinIntro.tex:2220-2246`; `ISSUE-TYPO-EX4.6`) holds. -/
theorem Ex4_6_holds : Ex4_6 :=
  fun hn hd hp0 hp1 ↦ degreeDVertices_coupling hn hd hp0 hp1

/-- Theorem 4.14 (`\label{thm122}`, `SteinIntro.tex:2253-2277`) holds. -/
theorem Thm4_14_holds : Thm4_14 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ _ hX_meas hX_zo
  exact thm4_14_variance_proof P P' hX_meas hX_zo

/-- Theorem 4.15 (`\label{thm123}`, `SteinIntro.tex:2289-2295`) holds. -/
theorem Thm4_15_holds : Thm4_15 := by
  intro _ _ H _ _ _ _ P _ P' _ _ _ _ _ _ hV0 hVn hiso hp0 hp1 hG_meas hG_law
  exact thm4_15_variance_proof H P P' hV0 hVn hiso hp0 hp1 hG_meas hG_law

/-- Section 4.3.2 Theorem 4.15 coupling verification (`SteinIntro.tex:2299-2307` items 1–3)
holds. -/
theorem Sec4_3_2_subgraph_coupling_holds : Sec4_3_2_subgraph_coupling := by
  intro _ _ H _ _ _ hV0 hVn hiso hp0 hp1 hα
  exact sec4_3_2_subgraph_coupling_proof H hV0 hVn hiso hp0 hp1 hα

/-- Corollary 4.16 (`\label{cor123}`, `SteinIntro.tex:2313-2331`) holds. -/
theorem Cor4_16_holds : Cor4_16 := by
  intro _ _ H _ _ _ _ P _ P' _ _ _ _ _ _ _ hV0 hVn hiso hp0 hp1 hα hG_meas hG_law
  exact cor4_16_holds_proof H P P' hV0 hVn hiso hp0 hp1 hα hG_meas hG_law

/-- Example 4.7 (*Triangles*, `SteinIntro.tex:2334-2343`, eq. `(4.13)` `\label{124}`) holds. -/
theorem Ex4_7_holds : Ex4_7 := ex4_7_holds_proof

/-- Example 4.8 (*$k$-cycles*, `SteinIntro.tex:2344-2366`, eq. `(4.14)` `\label{125}`) holds. -/
theorem Ex4_8_holds : Ex4_8 := ex4_8_holds_proof

/-- Theorem 4.17, corrected (`\label{thm124}`, `SteinIntro.tex:2382-2390`;
`ISSUE-4.17`) holds. -/
theorem Thm4_17_corrected_holds : Thm4_17_corrected := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ _ hY_meas hY_01 hY_indep hf_01 hf_mono _ _ _ hr_eq hZ_meas
    hZ_law
  exact thm4_17_corrected P P' hY_meas hY_01 hY_indep hf_01 hf_mono hr_eq hZ_meas hZ_law

/-- Theorem 4.17 proof implicit coupling existence, corrected (`SteinIntro.tex:2392-2394`;
`ISSUE-4.17`) holds. -/
theorem Thm4_17_implicit_coupling_corrected_holds : Thm4_17_implicit_coupling_corrected :=
  @thm4_17_implicit_coupling_corrected

/-- Theorem 4.17 proof composition monotonicity step, corrected (`SteinIntro.tex:2395-2396`;
`ISSUE-4.17`) holds. -/
theorem Thm4_17_comp_monotone_corrected_holds : Thm4_17_comp_monotone_corrected :=
  @thm4_17_comp_monotone_corrected

/-- Section 4.3.3 FKG inequality (`SteinIntro.tex:2395-2401`) holds. -/
theorem Thm4_17_fkg_holds : Thm4_17_fkg := by
  intro _ _ P _ _ _ _ _ hY_meas hY_01 hY_indep h_mono
  exact fkg_independent_indicators_on P hY_meas hY_01 hY_indep h_mono

/-- Lemma 4.18 (`\label{lem121}`, `SteinIntro.tex:2404-2423`) holds. -/
theorem Lem4_18_holds : Lem4_18 := by
  intro _ _ _ _ P _ P' _ _ _ _ i hX_meas hX_01 hXc_meas hp_pos h_law
  exact lem4_18_cond P P' i hX_meas hX_01 hXc_meas hp_pos h_law

/-- Section 4.3.3 one-dimensional Strassen theorem (`SteinIntro.tex:2415-2417`) holds. -/
theorem Lem4_18_strassen_1d_holds : Lem4_18_strassen_1d := by
  intro _ _ _ _ P _ P' _ _ _ hX hY
  exact lem4_18_strassen_1d_iff P P' hX hY

/-- Example 4.10 (`[Subgraph counts]`, `SteinIntro.tex:2424-2427`) holds. -/
theorem Ex4_10_holds : Ex4_10 := by
  intro _ _ H _ _ _ _ P _ P' _ _ _ _ _ _ hp0 hp1 hG_meas hG_law _ _ hr_eq hZ_meas hZ_law
  exact ex4_10 H P P' hp0 hp1 hG_meas hG_law hr_eq hZ_meas hZ_law

/-- Example 4.11 (`[Large degree vertices]`, `SteinIntro.tex:2428-2439`) holds. -/
theorem Ex4_11_holds : Ex4_11 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ _ hn hdn hp0 hp1 hG_meas hG_law _ _ hr_eq hZ_meas hZ_law
  exact ex4_11 P P' hn hdn hp0 hp1 hG_meas hG_law hr_eq hZ_meas hZ_law

/-- Example 4.12 (`[Small degree vertices]`, `SteinIntro.tex:2440-2449`) holds. -/
theorem Ex4_12_holds : Ex4_12 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ _ hn hp0 hp1 hG_meas hG_law _ _ hr_eq hZ_meas hZ_law
  exact ex4_12 P P' hn hp0 hp1 hG_meas hG_law hr_eq hZ_meas hZ_law

/-- Proof witness for `SteinMethod.Thm4_19` (`\label{thm125}`, `SteinIntro.tex:2455-2465`). -/
theorem Thm4_19_holds : Thm4_19 := by
  intro Ω Ω' _ _ P _ P' _ n X Y I r Z hX_meas hX_zo
  exact thm4_19 P P' hX_meas hX_zo

/-- Proof witness for `SteinMethod.Ex4_13_sizeBias` (`SteinIntro.tex:2487-2498`). -/
theorem Ex4_13_sizeBias_holds : Ex4_13_sizeBias := by
  intro N n m hn1 hnN hm1 hmN Ω _ P _ S U hS hS_unif hU_meas hSU_indep hU_unif
  exact ex4_13_sizeBias hn1 hnN hm1 hmN P hS hS_unif hU_meas hSU_indep hU_unif

/-- Proof witness for `SteinMethod.Ex4_13_moments_corrected` (`SteinIntro.tex:2499-2501`). -/
theorem Ex4_13_moments_corrected_holds : Ex4_13_moments_corrected := by
  intro N n m Ω _ P _ S hn1 hnN hm1 hmN hS hS_unif
  exact ex4_13_moments_corrected P hn1 hnN hm1 hmN hS hS_unif

/-- Proof witness for `SteinMethod.Ex4_13_restricted` (`SteinIntro.tex:2480-2505`). -/
theorem Ex4_13_restricted_holds : Ex4_13_restricted := by
  intro N n m Ω Ω' _ _ P _ P' _ S r Z hN2 hn1 hnN hm1 hmN hS hS_unif hr hZ_meas hZ_law
  exact ex4_13_restricted P P' hN2 hn1 hnN hm1 hmN hS hS_unif hr hZ_meas hZ_law

/-- Proof witness for `SteinMethod.Rem4_14` (`SteinIntro.tex:2506-2510`). -/
theorem Rem4_14_holds : Rem4_14 := by
  intro N n m Ω _ P _ S hn1 hnN hm1 hmN hS hS_unif
  exact rem4_14 P hn1 hnN hm1 hmN hS hS_unif

/-- Proof witness for `SteinMethod.Ex4_15_allTypes_iff` (`SteinIntro.tex:2522-2525`). -/
theorem Ex4_15_allTypes_iff_holds : Ex4_15_allTypes_iff := by
  intro n k b
  exact ex4_15_allTypes_iff b

/-- Proof witness for `SteinMethod.Ex4_15_sizeBias` (`SteinIntro.tex:2529-2539`). -/
theorem Ex4_15_sizeBias_holds : Ex4_15_sizeBias := by
  intro n k hn Ω _ P _ B R hB_meas hB_indep hB_prob hR_meas hR_indep hR_prob hBR_indep
  exact ex4_15_sizeBias hn P hB_meas hB_indep hB_prob hR_meas hR_indep hR_prob hBR_indep

/-- Proof witness for `SteinMethod.Ex4_15_restricted` (`SteinIntro.tex:2526-2551`). -/
theorem Ex4_15_restricted_holds : Ex4_15_restricted := by
  intro n k Ω Ω' _ _ P _ P' _ B r Z hn hB_meas hB_indep hB_prob
  exact ex4_15_restricted P P' hn hB_meas hB_indep hB_prob

/-- Proof witness for `SteinMethod.Ex4_15_asymptotic_ineq` (`SteinIntro.tex:2554-2560`). -/
theorem Ex4_15_asymptotic_ineq_holds : Ex4_15_asymptotic_ineq := by
  intro n k
  exact ex4_15_asymptotic_bounds

/-- Proof witness for `SteinMethod.Ex4_15_rate` (`SteinIntro.tex:2553-2564`). -/
theorem Ex4_15_rate_holds : Ex4_15_rate := by
  intro c k hk
  exact ex4_15_rate hk

/-- Proof witness for `SteinMethod.Ex4_16_sizeBias` (`SteinIntro.tex:2581-2587`). -/
theorem Ex4_16_sizeBias_holds : Ex4_16_sizeBias :=
  ex4_16_sizeBias_holds

/-- Proof witness for `SteinMethod.Ex4_16_restricted` (`SteinIntro.tex:2566-2592`). -/
theorem Ex4_16_restricted_holds : Ex4_16_restricted := by
  intro n k hn Ω Ω' _ _ P _ P' _ p B r Z hk1 hp_nn hp_sum hB_meas hB_indep hB_prob
  exact ex4_16_restricted hn P P' hk1 hp_nn hp_sum hB_meas hB_indep hB_prob

/-- Proof witness for `SteinMethod.Ex4_16_exists_zero_denom` (`SteinIntro.tex:2590`). -/
theorem Ex4_16_exists_zero_denom_holds : Ex4_16_exists_zero_denom :=
  ex4_16_exists_zero_denom

/-- Proof witness for `SteinMethod.Rem4_17_atMost` (`SteinIntro.tex:2594-2598`). -/
theorem Rem4_17_atMost_holds : Rem4_17_atMost :=
  rem4_17_atMost_holds

/-- Proof witness for `SteinMethod.Rem4_17_atLeast_corrected` (`SteinIntro.tex:2600`). -/
theorem Rem4_17_atLeast_corrected_holds : Rem4_17_atLeast_corrected :=
  rem4_17_atLeast_corrected_holds

/-- Theorem 4.20 (`\label{thm161}`, `SteinIntro.tex:2618-2626`; `stmts-review-05H` `H1`) holds. -/
theorem Thm4_20_holds : Thm4_20 := by
  intro Ω mΩ P _ r W W' hr hW hW' hex F hFle hWF c
  let _ : MeasurableSpace Ω := mΩ
  exact tvDist_poissonLaw_exchangeable_le P hr hW hW' hex hFle hWF c

/-- Remark 4.18 (`SteinIntro.tex:2628-2632`) holds. -/
theorem Rem4_18_holds : Rem4_18 :=
  fun P _ _ _ hW hW' hex ↦ exchangeable_jump_prob_eq P hW hW' hex

/-- Remark 4.19 (`SteinIntro.tex:2633-2641`; `stmts-review-05H`) holds. -/
theorem Rem4_19_holds : Rem4_19 :=
  ⟨poisson_detailed_balance, poisson_stationary_birth_death⟩

/-- Theorem 4.20 proof anti-symmetry sub-claim (`SteinIntro.tex:2647-2650`) holds. -/
theorem Thm4_20_antisym_holds : Thm4_20_antisym :=
  fun P _ _ _ hW hW' hex f _hf ↦ integral_poissonExchTestFn_eq_zero P hW hW' hex f

/-- Theorem 4.20 proof key identity eq. `(4.3)` (`\label{161}`, `SteinIntro.tex:2656-2660`;
`stmts-review-05H` `H2`) holds. -/
theorem Thm4_20_identity_holds : Thm4_20_identity := by
  intro Ω mΩ P _ r W W' hr hW hW' hex hIntW F hFle hWF f hf c
  let _ : MeasurableSpace Ω := mΩ
  exact integral_poissonSteinOp_exchangeable_eq P hr hW hW' hex hIntW hFle hWF f hf c

/-- Example 4.20 coupling and conditional jump probabilities (`SteinIntro.tex:2664-2671`;
`stmts-review-05H` `H3`) hold. -/
theorem Ex4_20_coupling_holds : Ex4_20_coupling := by
  intro _ _ P _ _ hn _ _ _ _ hval hm hm' hp hind hId hXX' hIm hIi hIu
  exact bernoulli_replaceOne_coupling P hn hval hm hm' hp hind hId hXX' hIm hIi hIu

/-- Example 4.20 (`SteinIntro.tex:2663-2680`) holds. -/
theorem Ex4_20_holds : Ex4_20 := by
  intro _ _ P _ _ _ _ hn hval hm hp hpb hind _ hr hlam
  exact aux_tvDist_indep_bernoulli_sum_poissonLaw_le P hn hval hm hp hpb hind hr hlam

/-- Example 4.20 direct bound of eq. `(4.15)` (`\label{161}`, `SteinIntro.tex:2678-2679`; `SD-5`)
holds. -/
theorem Ex4_20_direct_eq161_holds : Ex4_20_direct_eq161 :=
  @ex4_20_direct_eq161

/-- Example 4.21 transposition coupling and conditional jump probabilities
(`SteinIntro.tex:2682-2688`; `stmts-review-05H` `H3`) hold. -/
theorem Ex4_21_coupling_holds : Ex4_21_coupling := by
  intro _ _ P _ _ hn _ _ hσ hτ hind hσu hτu
  exact fixedPoints_transposition_coupling P hn hσ hτ hind hσu hτu

/-- Example 4.21 first-moment sub-claim (`SteinIntro.tex:2693`) holds. -/
theorem Ex4_21_EW_holds : Ex4_21_EW :=
  fun hn ↦ expected_fixed_points hn

/-- Example 4.21 second-moment sub-claim (`SteinIntro.tex:2701-2702`) holds. -/
theorem Ex4_21_EW2_holds : Ex4_21_EW2 :=
  fun hn ↦ expected_fixed_points_sq hn

/-- Example 4.21 2-cycle expectation sub-claim (`SteinIntro.tex:2701-2702`) holds. -/
theorem Ex4_21_EW2cycles_holds : Ex4_21_EW2cycles :=
  fun hn ↦ expected_two_cycles hn

/-- Example 4.21 (`SteinIntro.tex:2694-2699`) holds. -/
theorem Ex4_21_holds : Ex4_21 :=
  fun hn ↦ tvDist_fixedPoints_poissonLaw_le hn

/-- Example 4.21 true-rate prose claim (`SteinIntro.tex:2702-2703`, citing `[abt03]`;
`stmts-review-05H` `H4`, `stmts-review-BL6` `BL6-1`, Backlog item 6) holds. -/
theorem Ex4_21_true_rate_holds : Ex4_21_true_rate :=
  fixedPoints_true_rate

end SteinMethod
