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
import Formalization.PoissonExch.FixedPointsTrueRate
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

/-- Example 4.21 true-rate prose claim (`SteinIntro.tex:2702-2703`, citing `[abt03]`;
`stmts-review-05H` `H4`, `stmts-review-BL6` `BL6-1`, Backlog item 6) holds. -/
theorem Ex4_21_true_rate_holds : Ex4_21_true_rate :=
  fixedPoints_true_rate

end SteinMethod
