/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.AntiVoter
import Formalization.Exchangeable.AntiVoterGraph
import Formalization.Exchangeable.AntiVoterUnique
import Formalization.Exchangeable.Basic
import Formalization.Exchangeable.IndepSumPair
import Formalization.Exchangeable.IndepSumPairBounds
import Formalization.Exchangeable.SteinPairBound
import Formalization.Exer.AntiVoterKolmogorov
import Formalization.Exer.CombinatorialKolmogorov
import Formalization.Exer.GoldsteinReinert
import Formalization.Exer.IndepSumZeroBiasKolmogorov
import Formalization.Exer.PermSwapCoupling
import Formalization.Exer.Thm328Applications
import Formalization.Kolmogorov.BinomialOrder
import Formalization.Kolmogorov.ExchangeableBound
import Formalization.Leftovers.Ex36SmallN
import Formalization.Leftovers.Ex38IndepSum
import Formalization.Leftovers.OUUniqueness
import Formalization.Leftovers.OrnsteinUhlenbeck
import Formalization.Leftovers.RandomGraphAddenda
import Formalization.Leftovers.TrianglesKolm
import Formalization.Normal.DependencyNeighborhoods
import Formalization.Normal.IndependentSums
import Formalization.Normal.WassersteinBound
import Formalization.RandomGraph.ErdosRenyi
import Formalization.RandomGraph.IsolatedCoupling
import Formalization.RandomGraph.IsolatedMoments
import Formalization.RandomGraph.IsolatedVertices
import Formalization.RandomGraph.Triangles
import Formalization.RandomGraph.TrianglesRucinskiCLT
import Formalization.SizeBias.Basic
import Formalization.SizeBias.Coupling
import Formalization.ZeroBias.Basic
import Formalization.ZeroBias.Coupling
import Formalization.ZeroBias.Density
import Formalization.ZeroBias.Lindeberg
import Formalization.ZeroBias.LindebergFeller
import Formalization.Sweep.SweepASec3a
import Formalization.Sweep.SweepASec3b
import Formalization.Sweep.SweepASec3c
import Formalization.Sweep.SweepBAntiVoter
import Formalization.Sweep.SweepBSteinPair
import Formalization.Sweep.SweepBZeroBias
import Formalization.Statements.Sec3

/-!
# Section 3 Proof Wrappers (`Formalization.Statements.Sec3Proofs`)

Connects each `: Prop` entry in `Formalization.Statements.Sec3` to its library theorem
(`AGENTS.md` Rule 5).
-/

namespace SteinMethod

/-- Section 3 Kolmogorov–Wasserstein normal comparison (`SteinIntro.tex:703-707`) holds. -/
theorem Sec3_dK_le_dW_holds : Sec3_dK_le_dW := by
  intro _ _ _ _ P _ P' _ _ _ hW hZ hZ_law
  exact kolmogorovDist_map_le_stdNormal_rpow_wassersteinDist_map P P' hW hZ hZ_law

/-- Claim A8a (`SteinIntro.tex:711-716`): Stein solution regularity. -/
theorem Sec3_opening_steinSol_regularity_holds : Sec3_opening_steinSol_regularity :=
  sec3_opening_steinSol_regularity_proof

/-- Theorem 3.1 (`\label{thm31}`, eq. `(3.1)` `\label{35}`, `SteinIntro.tex:719-724`) holds. -/
theorem Thm3_1_holds : Thm3_1 := by
  intro _ _ _ _ P _ P' _ _ _ hW hZ hZ_law
  exact wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P' hW hZ hZ_law

/-- Theorem 3.2 (`\label{thm32}`, `SteinIntro.tex:736-742`) holds. -/
theorem Thm3_2_holds : Thm3_2 := by
  intro _ _ _ _ P _ P' _ _ _ _ hn hX_meas h_indep hX4 hX0 hX2 hZ hZ_law
  exact (wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P'
    (indepSum_aemeasurable_W hX_meas) hZ hZ_law).trans
      (indepSum_iSup_normalWassersteinClass_le P hn hX_meas h_indep hX4 hX0 hX2)

/-- Claim A9 (`SteinIntro.tex:743-744`): i.i.d. rate O(n^{-1/2}) and optimality. -/
theorem Sec3_1_iid_wasserstein_rate_holds : Sec3_1_iid_wasserstein_rate :=
  sec3_1_iid_wasserstein_rate_proof

/-- Claim SA-8 (`SteinIntro.tex:746-747`): third-moment independent sum bound. -/
theorem Sec3_1_indepSum_thirdMoment_holds : Sec3_1_indepSum_thirdMoment := by
  intro _ _ _ _ P _ P' _ _ hn _ _ hX_meas h_indep hX3 hX0 hX2 hZ hZ_law
  exact sec3_1_indepSum_thirdMoment_proof P P' hn hX_meas h_indep hX3 hX0 hX2 hZ hZ_law

/-- Lemma 3.3 (`\label{lem33}`, `SteinIntro.tex:753-759`; `ISSUE-TYPO-3.3`, `ISSUE-3.3`) holds. -/
theorem Lem3_3_holds : Lem3_3 := by
  intro _ _ P _ _ _ _ hn hX_meas h_indep hX4 hX0 hX2 hf1 hb0 hb1
  exact indepSum_stein_expansion P hn hX_meas h_indep hX4 hX0 hX2 hf1 hb0 hb1

/-- Lemma 3.4 (`\label{lem33aa}`, eq. `(3.6)` `\label{337}`, `SteinIntro.tex:771-776`) holds. -/
theorem Lem3_4_holds : Lem3_4 := by
  intro _ _ P _ _ _ _ hn hX_meas h_indep hX4 hX0 hX2 hf hb0 _ _ hb1 hb2
  exact indepSum_normalSteinOp_bound P hn hX_meas h_indep hX4 hX0 hX2 hf hb0 hb1 hb2

/-- Theorem 3.5, corrected (`\label{thm41}`, eq. `(3.8)` `\label{41}`, `SteinIntro.tex:815-822`;
`ISSUE-3.5`) holds. -/
theorem Thm3_5_corrected_holds : Thm3_5_corrected := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hX_meas hX4 hX0 hG hVar hZ hZ_law
  exact (wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P'
    (depGraph_aemeasurable_W hX_meas) hZ hZ_law).trans
      (depGraph_iSup_normalWassersteinClass_le P hX_meas hX4 hX0 hG hVar)

/-- Claim A10 (`SteinIntro.tex:827-828`): independent variables form a dependency graph. -/
theorem Sec3_2_indep_isDependencyGraph_holds : Sec3_2_indep_isDependencyGraph :=
  sec3_2_indep_isDependencyGraph_proof

/-- Claim A11 (`SteinIntro.tex:908-911`): intermediate dependency neighborhood bound. -/
theorem Sec3_2_depNeighborhoods_intermediate_bound_holds :
    Sec3_2_depNeighborhoods_intermediate_bound :=
  sec3_2_depNeighborhoods_intermediate_bound_proof

/-- Claim A12 (`SteinIntro.tex:919-928`): triangle setup, moments, and dependency graph. -/
theorem Sec3_2_1_triangles_setup_and_moments_holds :
    Sec3_2_1_triangles_setup_and_moments :=
  sec3_2_1_triangles_setup_and_moments_proof

/-- Section 3.2.1 application, restricted (`SteinIntro.tex:918-949`; `ISSUE-TYPO-3.2.1`,
`ISSUE-3.2.1`) holds. -/
theorem Sec3_2_1_triangles_restricted_holds : Sec3_2_1_triangles_restricted :=
  Sec3_2_1_triangles_restricted_proof

/-- Section 3.2.1 literal $d_{\mathrm{K}}$ inequality, restricted to $0 < p < 1$
(`SteinIntro.tex:935-939`; `ISSUE-TYPO-3.2.1`, `ISSUE-3.2.1`) holds. -/
theorem Sec3_2_1_triangles_kolmogorov_restricted_holds :
    Sec3_2_1_triangles_kolmogorov_restricted :=
  erdosRenyi_triangles_kolmogorovDist_le

/-- Section 3.2.1 triangle-count variance divergence and CLT regime, restricted
(`SteinIntro.tex:941-944`; `ISSUE-TYPO-3.2.1`, `ISSUE-3.2.1`) holds. -/
theorem Sec3_2_1_triangles_clt_regime_restricted_holds :
    Sec3_2_1_triangles_clt_regime_restricted :=
  Sec3_2_1_triangles_clt_regime_restricted_proof

/-- Section 3.2.1 Ruciński triangle-count CLT criterion (`SteinIntro.tex:943-944`, `[ruc88]`)
holds. -/
theorem Sec3_2_1_triangles_rucinski_holds : Sec3_2_1_triangles_rucinski :=
  Sec3_2_1_triangles_rucinski_proof

/-- Section 3.2.1 power-law normal-convergence regime (`SteinIntro.tex:942-944`, `[ruc88]`)
holds. -/
theorem Sec3_2_1_triangles_rucinski_power_regime_holds :
    Sec3_2_1_triangles_rucinski_power_regime :=
  Sec3_2_1_triangles_rucinski_power_regime_proof

/-- Proposition 3.6(1) (`\label{prop51}`, `SteinIntro.tex:962-971`) holds. -/
theorem Prop3_6_1_holds : Prop3_6_1 := by
  intro _ _ _ _ _ _ _ hExch hF hAnti
  exact hExch.integral_antisymm_eq_zero hF hAnti

/-- Proposition 3.6(2) (`\label{prop51}`, `SteinIntro.tex:967-971`) holds. -/
theorem Prop3_6_2_holds : Prop3_6_2 := by
  intro _ _ _ _ _ _ _ hSP hW2
  exact hSP.integral_eq_zero_and_sq_sub_eq hW2

/-- Theorem 3.7 (`\label{thm51}`, `SteinIntro.tex:983-988`) holds. -/
theorem Thm3_7_holds : Thm3_7 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hSP hW2 hZ hZ_law
  rcases hSP with ⟨hExch, ha, _, hW_meas, _, hCond⟩
  exact (wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P'
    hW_meas.aemeasurable hZ hZ_law).trans
      (steinPair_iSup_normalWassersteinClass_le P hExch ha hW_meas hCond hW2)

/-- Remark 3.3 (`SteinIntro.tex:990-999`) holds. -/
theorem Rem3_3_holds : Rem3_3 := by
  intro _ _ _ _ μ _ κ _ _ hrev hW
  exact reversibleMarkov_isExchangeablePair μ κ hrev hW

/-- Remark 3.4 (`SteinIntro.tex:1000-1008`) holds. -/
theorem Rem3_4_holds : Rem3_4 := by
  intro _ _ P _ _ _ _ hm₁₂ hm₂₀ hY
  exact evariance_condExp_mono P hm₁₂ hm₂₀ hY

/-- Remark 3.5 (`SteinIntro.tex:1009-1024`; `ISSUE-TYPO-3.5`) holds. -/
theorem Rem3_5_holds : Rem3_5 :=
  rem3_5_proof

/-- Remark 3.5 uniqueness, restricted (`SteinIntro.tex:1009-1024`; `BL8`) holds. -/
theorem Rem3_5_uniqueness_restricted_holds : Rem3_5_uniqueness_restricted :=
  rem3_5_uniqueness_restricted_proof

/-- Display `(3.18)` (`\label{511}`, `SteinIntro.tex:1043-1046`) holds. -/
theorem Sec3_3_eq3_18_holds : Sec3_3_eq3_18 := by
  intro _ _ P _ _ _ _ _ _ _ _ hSP hf1 hf2 hf_bdd hf'_bdd hf''_bdd
  exact sec3_3_eq3_18_proof P hSP hf1 hf2 hf_bdd hf'_bdd hf''_bdd

/-- Wasserstein corollary of `(3.18)` (`\label{511}`, `SteinIntro.tex:1043-1048`) holds. -/
theorem Sec3_3_eq3_18_wasserstein_holds : Sec3_3_eq3_18_wasserstein := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hSP hZ hZ_law
  exact sec3_3_eq3_18_wasserstein_proof P P' hSP hZ hZ_law

/-- Example 3.6, Stein-pair verification (`SteinIntro.tex:1053-1069`) holds. -/
theorem Ex3_6_steinPair_holds : Ex3_6_steinPair := by
  intro _ _ P _ _ hn _ _ _ hX_meas hX'_meas h_indep hX4 hX0 hX_var hId hXX'_indep hI_meas
    hI_indep hI_unif
  exact indepSum_replaceOne_isSteinPair P hn hX_meas hX'_meas h_indep hX4 hX0 hX_var hId
    hXX'_indep hI_meas hI_indep hI_unif

/-- Example 3.6, corrected Wasserstein bound (`SteinIntro.tex:1053-1097`; `ISSUE-3.6`) holds. -/
theorem Ex3_6_corrected_holds : Ex3_6_corrected := by
  intro _ _ _ _ P _ P' _ _ hn _ _ _ _ hX_meas hX'_meas h_indep hX4 hX0 hX_var hId hXX'_indep
    hI_meas hI_indep hI_unif hZ hZ_law
  have hSP := indepSum_replaceOne_isSteinPair P hn hX_meas hX'_meas h_indep hX4 hX0 hX_var hId
    hXX'_indep hI_meas hI_indep hI_unif
  have hW2 := indepSum_replaceOne_integral_W_sq P hn hX_meas h_indep hX4 hX0 hX_var
  exact (Thm3_7_holds P P' hSP hW2 hZ hZ_law).trans
    (indepSum_replaceOne_thm3_7_rhs_le_corrected P hn hX_meas hX'_meas h_indep hX4 hX0 hX_var
      hId hXX'_indep hI_meas hI_indep hI_unif)

/-- Example 3.6, restricted printed bound (`SteinIntro.tex:1053-1097`, `L1089`; `ISSUE-3.6`)
holds. -/
theorem Ex3_6_restricted_holds : Ex3_6_restricted := by
  intro _ _ _ _ P _ P' _ _ hn _ _ _ _ hX_meas hX'_meas h_indep hX4 hX0 hX_var hId hXX'_indep
    hI_meas hI_indep hI_unif hZ hZ_law hn16
  exact (Ex3_6_corrected_holds P P' hn hX_meas hX'_meas h_indep hX4 hX0 hX_var hId hXX'_indep
    hI_meas hI_indep hI_unif hZ hZ_law).trans
      (indepSum_replaceOne_corrected_rhs_le_restricted P hn16)

/-- Example 3.6, printed Wasserstein bound (`SteinIntro.tex:1053-1097`, `L1089`; `ISSUE-3.6`)
holds for all $n \ge 1$. -/
theorem Ex3_6_printed_holds : Ex3_6_printed := by
  intro _ _ _ _ P _ P' _ _ _ _ hn hX_meas h_indep hX4 hX0 hX_var hZ_meas hZ_law
  exact indepSum_wassersteinDist_le_ex3_6_printed P P' hn hX_meas h_indep hX4 hX0 hX_var
    hZ_meas hZ_law

/-- Section 3.3.1 anti-voter ergodicity, corrected (`SteinIntro.tex:1101-1111`; `ISSUE-3.8`)
holds. -/
theorem Sec3_3_1_antiVoter_ergodic_corrected_holds : Sec3_3_1_antiVoter_ergodic_corrected := by
  intro V _ _ G _ r hReg hConn hBip hCyc
  have hcard : 3 ≤ Fintype.card V := three_le_card_of_not_isBipartite G hBip
  have hpos : 0 < Fintype.card V := by omega
  have : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hV : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hr : 1 ≤ r := one_le_degree_of_not_isBipartite G hReg hBip
  have hN : ∀ v : V, (G.neighborFinset v).Nonempty := fun v ↦
    Finset.card_pos.mp (by rw [G.card_neighborFinset_eq_degree, hReg v]; omega)
  exact ⟨fun _ _ hne ↦ antiVoterStep_support_nonconst G hV hN hne,
    antiVoter_ergodic_and_unique_stationary G hConn hBip hCyc⟩

/-- Literal printed Section 3.3.1 stationary-uniqueness claim without `G.Connected`
(`SteinIntro.tex:1101-1111`; `ISSUE-3.8`). -/
def Sec3_3_1_antiVoter_unique_printed : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ},
    G.IsRegularOfDegree r →
    ¬ G.IsBipartite →
    IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) →
    ∀ μ₁ μ₂ : MeasureTheory.Measure (V → Bool),
      MeasureTheory.IsProbabilityMeasure μ₁ → MeasureTheory.IsProbabilityMeasure μ₂ →
      IsAntiVoterStationary G μ₁ → IsAntiVoterStationary G μ₂ → μ₁ = μ₂

/-- **Refutation of printed Section 3.3.1 stationary uniqueness without `G.Connected`**
(`SteinIntro.tex:1101-1111`; `ISSUE-3.8`): refuted by $G = K_3 \sqcup C_4$ on `Fin 7`. -/
theorem not_Sec3_3_1_antiVoter_unique_printed : ¬ Sec3_3_1_antiVoter_unique_printed := by
  intro hall
  obtain ⟨G, hDec, ν₁, ν₂, hReg, hBip, hCyc, hP₁, hP₂, hS₁, hS₂, hne, _⟩ :=
    antiVoter_disconnected_counterexample
  exact hne (@hall (Fin 7) _ _ G hDec 2 hReg hBip hCyc ν₁ ν₂ hP₁ hP₂ hS₁ hS₂)

/-- Theorem 3.8 (`\label{thm52}`, `SteinIntro.tex:1114-1127`) holds. -/
theorem Thm3_8_holds : Thm3_8 := by
  intro _ _ _ G _ _ _ _ _ _ P _ P' _ _ _ _ hReg hBip hCyc hX hX' hStat hStep hZ hZ_law
  exact antiVoter_steinPair_and_wasserstein_bound G P P' hReg hBip hCyc hX hX' hStat hStep
    hZ hZ_law

/-- Section 3.3.1 non-reversibility of the anti-voter Markov chain (`SteinIntro.tex:1130-1131`)
holds. -/
theorem Sec3_3_1_antiVoter_not_reversible_holds : Sec3_3_1_antiVoter_not_reversible :=
  sec3_3_1_antiVoter_not_reversible_proof

/-- Lemma 3.9 (`\label{lem51}`, `SteinIntro.tex:1133-1136`) holds. -/
theorem Lem3_9_holds : Lem3_9 := by
  intro _ _ P _ _ _ hId hStep
  exact isExchangeablePair_of_identDistrib_int_abs_sub_le_one P hId hStep

/-- Lemma 3.10 (`SteinIntro.tex:1208-1214`) holds. -/
theorem Lem3_10_holds : Lem3_10 := by
  intro _ _ _ G _ _ _ _ P _ _ hReg hr hX hStat
  exact antiVoter_variance_bounds G P hReg hr hX hStat

/-- Section 3.4 size-bias Stein identity (eq. `(3.23)` `\label{71}`, `SteinIntro.tex:1232-1236`;
`ISSUE-TYPO-3.4a`) holds. -/
theorem Sec3_4_sizeBias_identity_holds : Sec3_4_sizeBias_identity := by
  intro _ _ P _ _ _ _ hX_nn hX2 hVar hSB hf _ _ _ hXfW hFW
  exact sizeBias_stein_identity P hX_nn hX2 hVar hSB hf hXfW hFW

/-- Proposition 3.11, restricted to $\mu > 0$ (`SteinIntro.tex:1239-1245`; `ISSUE-3.11`, `D8`)
holds. -/
theorem Prop3_11_restricted_holds : Prop3_11_restricted := by
  intro _ _ _ _ P _ _ hX_nn hX_int hμ
  exact sizeBias_law_characterization P hX_nn hX_int hμ

/-- Corollary 3.12, restricted to $\mu > 0$ (`SteinIntro.tex:1246-1252`; `ISSUE-3.11`) holds. -/
theorem Cor3_12_restricted_holds : Cor3_12_restricted := by
  intro _ _ _ _ P _ P' _ _ _ hNat hX_int hμ hSB
  exact sizeBias_nat_pmf P P' hNat hX_int hμ hSB

/-- Theorem 3.13 (`\label{thm71}`, `SteinIntro.tex:1255-1261`) holds. -/
theorem Thm3_13_holds : Thm3_13 := by
  intro _ _ _ _ P _ P' _ _ _ _ hX_meas hX_nn hX2 hVar hSB hZ hZ_law
  exact sizeBias_wassersteinDist_le P P' hX_meas hX_nn hX2 hVar hSB hZ hZ_law

/-- Proposition 3.14 (`\label{prop71}`, `SteinIntro.tex:1284-1299`) holds. -/
theorem Prop3_14_holds : Prop3_14 := by
  intro _ _ P _ _ _ _ _ _ hX_meas hX_nn hX_int hμ hXs hY hXY hI hIp hIi
  exact sizeBias_sum_of_condDistrib_recipe P hX_meas hX_nn hX_int hμ hXs hY hXY hI hIp hIi

/-- Corollary 3.15 (`\label{cor71}`, `SteinIntro.tex:1319-1325`; `ISSUE-TYPO-3.15`) holds. -/
theorem Cor3_15_holds : Cor3_15 := by
  intro _ _ P _ _ _ _ _ hX_meas hX_nn hX_int hInd hXs hXsi hI hIp hIi hμ
  exact sizeBias_sum_of_iIndepFun P hX_meas hX_nn hX_int hInd hXs hXsi hI hIp hIi hμ

/-- Corollary 3.16 (`\label{cor72}`, `SteinIntro.tex:1326-1332`) holds. -/
theorem Cor3_16_holds : Cor3_16 := by
  intro _ _ P _ _ _ _ _ hX_meas hX_zo
  exact sizeBias_sum_of_zero_one P hX_meas hX_zo

/-- Example 3.8 (`\label{ex71}`, `SteinIntro.tex:1349-1353`; Backlog item 9) holds. -/
theorem Ex3_8_holds : Ex3_8 := by
  intro _ _ _ _ P _ P' _ _ _ _ hX_nn hX3 hX_indep hVar hZ hZ_law
  exact sizeBias_indepSum_wassersteinDist_le P P' hX_nn hX3 hX_indep hVar hZ hZ_law

/-- Example 3.9, size-bias realization and increment identity (`\label{ex72}`,
`SteinIntro.tex:1354-1367, 1380-1383`) holds. -/
theorem Ex3_9_sizeBias_holds : Ex3_9_sizeBias :=
  Ex3_9_sizeBias_le_one_proof

/-- Example 3.9, verified moment formulas (`\label{ex72}`, `SteinIntro.tex:1370-1379, 1406-1409`,
eq. `\label{77}`; `ISSUE-3.9`) holds. -/
theorem Ex3_9_moments_holds : Ex3_9_moments :=
  Ex3_9_moments_proof

/-- Theorem 3.17 (`SteinIntro.tex:1413-1420`) holds. -/
theorem Thm3_17_holds : Thm3_17 :=
  Thm3_17_proof

/-- Section 3.5 fixed-point characterization (`SteinIntro.tex:1450-1451`) holds. -/
theorem Sec3_5_zeroBias_fixedPoint_holds : Sec3_5_zeroBias_fixedPoint := by
  intro _ _ P _ _ hW
  exact isZeroBias_self_iff_normalLaw P hW

/-- Theorem 3.18 (`\label{thm81}`, `SteinIntro.tex:1454-1461`) holds. -/
theorem Thm3_18_holds : Thm3_18 := by
  intro _ _ _ _ P _ P' _ _ _ _ hVar hZB hZ hZ_law
  exact zeroBias_wassersteinDist_le P P' hVar hZB hZ hZ_law

/-- Proposition 3.19, corrected (`\label{i81}`, `\label{i82}`, eqs. `(3.31)`–`(3.32)`
`\label{81}`–`\label{82}`, `SteinIntro.tex:1471-1485`; `ISSUE-3.10`, `ISSUE-3.19`, `D9`) holds. -/
theorem Prop3_19_corrected_holds : Prop3_19_corrected := by
  intro _ _ _ _ P _ _ hW2 hMean hVar
  exact zeroBias_law_characterization P hW2 hMean hVar

/-- Section 3.5 distributional uniqueness from $C_c^1$ derivatives (`SteinIntro.tex:1512-1513`)
holds. -/
theorem Sec3_5_identDistrib_of_integral_deriv_compactSupport_holds :
    Sec3_5_identDistrib_of_integral_deriv_compactSupport := by
  intro _ _ _ _ P _ P' _ _ _ hX hY hHyp
  exact sec3_5_identDistrib_of_integral_deriv_compactSupport_proof P P' hX hY hHyp

/-- Proposition 3.20 (`SteinIntro.tex:1519-1521`, existence reading) holds. -/
theorem Prop3_20_holds : Prop3_20 := by
  intro _ _ _ _ _ _ _ _ a hZB
  exact hZB.const_mul a

/-- Proposition 3.20, restricted (`SteinIntro.tex:1519-1521`, law-identity reading; `ISSUE-3.20`)
holds. -/
theorem Prop3_20_restricted_holds : Prop3_20_restricted := by
  intro _ _ _ _ _ _ P _ P' _ P'' _ _ _ _ _ hVar ha hZB
  exact zeroBias_const_mul_restricted P P' P'' hVar ha hZB

/-- Section 3.5.1 zero-bias construction from a Stein pair (`SteinIntro.tex:1527-1528`,
`%XXXX Exercise 3`) holds. -/
theorem Sec3_5_1_zeroBias_of_steinPair_holds : Sec3_5_1_zeroBias_of_steinPair := by
  intro _ _ P _ _ _ _ hSP hW2 hVar
  rcases hSP with ⟨hExch, ha, _, hW_meas, _, hCond⟩
  exact goldstein_reinert_zeroBias_of_comap P hExch ha hW_meas hW2 hCond hVar

/-- Proposition 3.21 (`\label{prop81}`, `SteinIntro.tex:1530-1551`; `ISSUE-TYPO-3.21`) holds. -/
theorem Prop3_21_holds : Prop3_21 := by
  intro _ _ P _ _ _ _ _ hX hXz hInd hL2 hMean hVar hZB hXzi hI hIp hIi
  exact zeroBias_sum_of_iIndepFun P hX hXz hInd hL2 hMean hVar hZB hXzi hI hIp hIi

/-- Section 3.5.2 Lindeberg sufficiency (`SteinIntro.tex:1558-1564`, eq. `(3.34)` `\label{85}`;
`ISSUE-3.22` prose note) holds. -/
theorem Sec3_5_2_lindeberg_sufficient_holds : Sec3_5_2_lindeberg_sufficient := by
  intro _ _ P _ _ hX hInd hL2 hMean hVar hLind
  exact tendsto_stdNormalLaw_of_lindeberg P hX hInd hL2 hMean hVar hLind

/-- Section 3.5.2 prose counterexample, corrected (`SteinIntro.tex:1565-1566`; `ISSUE-3.5.2-PROSE`)
holds. -/
theorem Sec3_5_2_lindeberg_not_necessary_corrected_holds :
    Sec3_5_2_lindeberg_not_necessary_corrected :=
  lindeberg_not_necessary_for_clt

/-- Theorem 3.22 (`\label{thm82}`, eqs. `(3.34)`–`(3.35)` `\label{85}`–`\label{86}`,
`SteinIntro.tex:1568-1575`; `ISSUE-3.22`) holds. -/
theorem Thm3_22_holds : Thm3_22 := by
  intro _ _ P _ _ _ _ hX hXz hInd hL2 hMean hVar hZB _hXzi hI hIp hIi
  exact lindeberg_iff_tendstoInMeasure_zeroBias P hX hXz hInd hL2 hMean hVar hZB hI hIp hIi

/-- Section 3.5.2 prose implication (`SteinIntro.tex:1585-1586, 1625-1646`) holds. -/
theorem Sec3_5_2_zeroBias_imp_tendstoInMeasure_holds :
    Sec3_5_2_zeroBias_imp_tendstoInMeasure := by
  intro _ _ P _ _ _ _ hX hXz hInd hL2 hMean hVar hZB _hXzi hI hIp hIi hConv
  exact tendstoInMeasure_and_max_variance_tendsto_of_zeroBias P hX hXz hInd hL2 hMean hVar hZB hI
    hIp hIi hConv

/-- Theorem 3.23 (`\label{thm83}`, `SteinIntro.tex:1578-1581`; `ISSUE-3.22`) holds. -/
theorem Thm3_23_holds : Thm3_23 := by
  intro _ _ P _ _ _ _ hX hXz hInd hL2 hMean hVar hZB hXzi hI hIp hIi hConv
  exact tendsto_stdNormalLaw_of_tendstoInMeasure_zeroBias P hX hXz hInd hL2 hMean hVar hZB hXzi hI
    hIp hIi hConv

/-- Section 3.6 motivating binomial rate claim (`SteinIntro.tex:1655-1657`; Backlog item 1)
holds. -/
theorem Sec3_6_binomial_order_holds : Sec3_6_binomial_order := by
  intro _ hp0 hp1
  exact binomial_kolmogorovDist_and_wassersteinDist_order hp0 hp1

/-- Theorem 3.24, corrected (`\label{thm91}`, eq. `(3.38)` `\label{91}`,
`SteinIntro.tex:1666-1675`; `ISSUE-2.2`, `D4`) holds. -/
theorem Thm3_24_corrected_holds : Thm3_24_corrected := by
  intro _ _ _ _ P _ P' _ _ _ hW hZ hZ_law
  exact kolmogorovDist_map_stdNormal_eq_iSup_normalSteinOpLeft P P' hW.aemeasurable hZ hZ_law

/-- Lemma 3.25, corrected (`\label{lem91}`, `SteinIntro.tex:1677-1686`; `ISSUE-2.2`, `ISSUE-3.25`,
`D4`) holds. -/
theorem Lem3_25_corrected_holds : Lem3_25_corrected :=
  lem3_25_corrected_bounds

/-- Corollary 3.26 (`\label{cor91}`, `SteinIntro.tex:1688-1694`) holds. -/
theorem Cor3_26_holds : Cor3_26 := by
  intro _ _ _ _ P _ P' _ _ _ hW hZ hZ_law
  exact kolmogorovDist_map_stdNormal_le_iSup_normalSteinOp P P' hW hZ hZ_law

/-- Theorem 3.27 (`SteinIntro.tex:1697-1704`, §3.6.1; `ISSUE-3.10`, `D9`) holds. -/
theorem Thm3_27_holds : Thm3_27 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hvar hWz hδ hZ hZ_law
  exact kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd P P' hvar hWz hδ hZ hZ_law

/-- Section 3.6.1 zero-bias boundedness inheritance, restricted to positive variance
(`SteinIntro.tex:1741-1742`; `ISSUE-3.19`, `ISSUE-TYPO-3.27`) holds. -/
theorem Sec3_6_zeroBias_bdd_restricted_holds : Sec3_6_zeroBias_bdd_restricted := by
  intro _ _ _ _ P _ P' _ _ _ _ hvar hWz hbdd
  exact ae_abs_le_of_isZeroBias_of_ae_abs_le P P' hvar hWz hbdd

/-- Section 3.6.1 zero-bias boundedness inheritance, existence reading (`SteinIntro.tex:1741-1742`)
holds. -/
theorem Sec3_6_zeroBias_bdd_exists_holds : Sec3_6_zeroBias_bdd_exists := by
  intro _ _ P _ _ _ hW hmean hbdd
  exact exists_bdd_zeroBias_of_pos_var_exists P hW hmean hbdd fun hpos ↦
    ⟨_, (@zeroBias_law_characterization _ Unit _ _ P _ _ hW hmean hpos).2.2⟩

/-- Section 3.6.1 bounded independent-sum Kolmogorov bound (`SteinIntro.tex:1741-1742`,
`%%XXXX Exercise 3`; `ISSUE-TYPO-3.27`) holds. -/
theorem Sec3_6_1_indepSum_kolmogorov_holds : Sec3_6_1_indepSum_kolmogorov := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hX_meas hX_indep hX_mean hX_bdd hVar hZ hZ_law
  exact sec3_6_1_indepSum_kolmogorov_proof P P' hX_meas hX_indep hX_mean hX_bdd hVar hZ hZ_law

/-- Section 3.6.1 Kolmogorov bound in Hoeffding's combinatorial CLT (`SteinIntro.tex:1742-1743`,
`%%XXXX Exercise 3`) holds. -/
theorem Sec3_6_1_combinatorial_kolmogorov_holds : Sec3_6_1_combinatorial_kolmogorov := by
  intro _ _ _ _ P _ P' _ _ _ _ _ _ hC hπ hπ_unif hvar_S hZ hZ_law
  exact sec3_6_1_combinatorial_kolmogorov P P' hC hπ hπ_unif hvar_S hZ hZ_law

/-- Theorem 3.28 (`\label{thm92}`, `SteinIntro.tex:1750-1755`; `ISSUE-3.25` proof note) holds. -/
theorem Thm3_28_holds : Thm3_28 := by
  intro _ _ _ _ _ _ P' _ _ _ _ _ _ hSP hvar hδ hZ hZ_law
  exact hSP.kolmogorovDist_map_stdNormal_le P' hvar hδ hZ hZ_law

/-- Lemma 3.29 (`\label{lem92}`, `SteinIntro.tex:1793-1798`) holds. -/
theorem Lem3_29_holds : Lem3_29 := by
  intro _ _ _ _ _ _ _ _ x hSP hvar hδ
  exact hSP.integral_sq_sub_mul_indicator_Ioc_le x hvar hδ

/-- Section 3.6.2 bounded independent-sum Kolmogorov bound via exchangeable pairs
(`SteinIntro.tex:1810`) holds. -/
theorem Sec3_6_2_indepSum_kolmogorov_holds : Sec3_6_2_indepSum_kolmogorov := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hX_meas h_indep hX0 hX_bdd hVar_pos hZ hZ_law
  exact sec3_6_2_indepSum_kolmogorov P P' hX_meas h_indep hX0 hX_bdd hVar_pos hZ hZ_law

/-- Section 3.6.2 anti-voter Kolmogorov bound (`SteinIntro.tex:1810-1812`) holds. -/
theorem Sec3_6_2_antiVoter_kolmogorov_holds : Sec3_6_2_antiVoter_kolmogorov :=
  sec3_6_2_antiVoter_kolmogorov

end SteinMethod
