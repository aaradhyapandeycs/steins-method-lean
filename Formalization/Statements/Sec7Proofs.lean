/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Statements.Sec7
import Formalization.Concentration.Basic
import Formalization.Concentration.CircularRuns
import Formalization.Concentration.Exchangeable
import Formalization.Concentration.IndepSum
import Formalization.Concentration.Combinatorial
import Formalization.Concentration.CurieWeiss
import Formalization.Concentration.Followups
import Formalization.Concentration.SizeBias
import Formalization.Sweep.SweepF

/-!
# Section 7 Proof Wrappers (`Formalization.Statements.Sec7Proofs`)

Connects every `: Prop` entry in `Formalization.Statements.Sec7` (`\label{conc}`,
`SteinIntro.tex:3398-3884`) to its library theorem (`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace SteinMethod

/-- Proposition 7.1 (`\label{prop211}`, `SteinIntro.tex:3411-3417`) holds. -/
theorem Prop7_1_holds : Prop7_1 := by
  intro _ _ P _ _ _ hW hδ hint _ _ ht hθ0 hθδ
  exact chernoff_tail_bounds P hW hδ hint ht hθ0 hθδ

/-- Example 7.1 (`\label{ex211}`, `SteinIntro.tex:3428-3445`) holds. -/
theorem Ex7_1_holds : Ex7_1 := by
  intro _ _ P _ _ hZ hlaw
  exact stdNormal_concentration_with_minimizer P hZ hlaw

/-- Example 7.2 (`\label{ex212}`, `SteinIntro.tex:3447-3461`) holds. -/
theorem Ex7_2_holds : Ex7_2 := by
  intro _ _ P _ _ _ hr hZ hlaw
  exact poisson_concentration_with_minimizer P hr hZ hlaw

/-- Example 7.2 corrected lower-order comparison (`\label{ex212}`, `SteinIntro.tex:3458`,
`SteinIntro.tex:3447`; `ISSUE-EX7.2`) holds. -/
theorem Ex7_2_order_corrected_holds : Ex7_2_order_corrected :=
  fun hlam hc ↦ poisson_bound_order_corrected hlam hc

/-- Example 7.2 restricted lower-order comparison (`\label{ex212}`, `SteinIntro.tex:3458`,
`SteinIntro.tex:3447`; `ISSUE-EX7.2`) holds. -/
theorem Ex7_2_order_restricted_holds : Ex7_2_order_restricted :=
  fun hlam ↦ poisson_bound_order_restricted hlam

/-- Section 7 prose MGF derivative identity (unlabeled prose, `SteinIntro.tex:3464-3469`)
holds. -/
theorem Sec7_mgf_hasDerivAt_holds : Sec7_mgf_hasDerivAt := by
  intro _ _ P _ _ _ hW hδ hint θ hθ
  exact mgf_integrable_mul_and_hasDerivAt P hW hδ hint hθ

/-- Theorem 7.2 (`\label{thm211a}`, eq. `(7.1)` `\label{122g}`, `SteinIntro.tex:3479-3489`)
holds. -/
theorem Thm7_2_holds : Thm7_2 := by
  intro Ω m₀ P _ a B C W W' hSP hW2 hInt m hWm hm hB hC hVarCond t ht
  exact @steinPair_tail_bounds Ω m₀ P _ a B C W W' hSP hW2 hInt m hWm hm hB hC hVarCond t ht

/-- Remark 7.3 (unlabeled `remark`, `SteinIntro.tex:3490-3495`) holds. -/
theorem Rem7_3_holds : Rem7_3 := by
  intro Ω m₀ P m a B C W W' ha hm hCond
  exact @condVar_linear_bound_nonneg Ω m₀ P a B C W W' m ha hm hCond

/-- Example 7.4 Stein-pair setup (unlabeled `example`, `SteinIntro.tex:3497-3502`) holds. -/
theorem Ex7_4_steinPair_holds : Ex7_4_steinPair := by
  intro _ _ P _ _ hn _ _ _ hX hX' hInd hX2 hId hXX' hI hIind hIunif
  exact indepSum_unscaled_isSteinPair P hn hX hX' hInd hX2 hId hXX' hI hIind hIunif

/-- Example 7.4(1) (unlabeled `example` item 1, `SteinIntro.tex:3503-3515`) holds. -/
theorem Ex7_4_1_holds : Ex7_4_1 := by
  intro _ _ P _ _ _ _ hn hX hInd hC hBdd
  exact indepSum_hoeffding_tail_bound P hn hX hInd hC hBdd

/-- Example 7.4(2), corrected (unlabeled `example` item 2, eq. `(7.2)` `\label{21198}`,
`SteinIntro.tex:3516-3536`; `ISSUE-EX7.4`) holds. -/
theorem Ex7_4_2_corrected_holds : Ex7_4_2_corrected := by
  intro _ _ P _ _ _ hn hX hInd hUnit
  exact indepSum_unitInterval_tail_bound P hn hX hInd hUnit

/-- Example 7.4(2), exponential order of `(7.2)` (`\label{21198}`, `SteinIntro.tex:3528-3529`,
`SteinIntro.tex:3526`) holds. -/
theorem Ex7_4_2_order_holds : Ex7_4_2_order :=
  fun hμ ↦ indepSum_unitInterval_bound_order hμ

/-- Section 7.1 display `(7.4)` (`\label{2212a}`, `SteinIntro.tex:3549-3552`) holds. -/
theorem Sec7_eq7_4_holds : Sec7_eq7_4 :=
  fun x y ↦ (abs_exp_sub_exp_le x y).trans_eq (mul_div_assoc _ _ _).symm

/-- Example 7.5 Stein-pair property, restricted (unlabeled `example`,
`SteinIntro.tex:3597-3611`; `ISSUE-TYPO-7.5`, `ISSUE-7.5`) holds. -/
theorem Ex7_5_steinPair_restricted_holds : Ex7_5_steinPair_restricted := by
  intro _ _ P _ _ hn a _ _ hσ hτ hInd hσu hτu
  exact combinatorial_isSteinPair_relaxed P hn a hσ hτ hInd hσu hτu

/-- Proposition 7.3 (unlabeled `proposition`, `SteinIntro.tex:3612-3617`; `ISSUE-TYPO-7.5`,
`ISSUE-7.5`) holds. -/
theorem Prop7_3_holds : Prop7_3 := by
  intro _ _ P _ _ _ _ ha hσ hσu
  exact combinatorial_concentration P ha hσ hσu

/-- Section 7.2 Curie–Weiss ground-state mode claim (unlabeled prose for `(7.6)`
(`\ref{2199}`), `SteinIntro.tex:3641`) holds. -/
theorem Sec7_curieWeiss_mode_holds : Sec7_curieWeiss_mode :=
  fun hβ ↦ curieWeiss_mode_extended hβ

/-- Proposition 7.4 (`\label{prop2112y}`, `SteinIntro.tex:3645-3653`) holds. -/
theorem Prop7_4_holds : Prop7_4 := by
  intro _ _ P _ _ _ _ _ _ hn hβ ht hX hlaw
  exact curieWeiss_concentration_of_map P hn hβ ht hX hlaw

/-- Theorem 7.5 (`\label{thm211b}`, `SteinIntro.tex:3658-3676`) holds. -/
theorem Thm7_5_holds : Thm7_5 := by
  intro _ _ _ _ _ _ _ P _ _ _ _ _ _ _ hX hExch hF hAnti hf hfeq hInt hB hC hCond t ht
  obtain ⟨_, hUpStrict, hLow, hZero⟩ :=
    exchangeable_antisymm_tail_bound P hX hExch hF hAnti hf hfeq hInt hB hC hCond ht
  exact ⟨hUpStrict, hLow, fun hC0 ↦ ⟨(hZero hC0).1, (hZero hC0).2.2⟩⟩

/-- Section 7.2 prose reduction from Theorem 7.5 to Theorem 7.2 (unlabeled prose,
`SteinIntro.tex:3677-3681`) holds. -/
theorem Sec7_thm7_2_from_thm7_5_holds : Sec7_thm7_2_from_thm7_5 := by
  intro _ _ P _ _ _ _ hSP
  exact steinPair_reduction_to_antisymm P hSP

/-- Theorem 7.6, corrected (`\label{thm211c}`, `SteinIntro.tex:3814-3826`; `ISSUE-7.6`) holds. -/
theorem Thm7_6_corrected_holds : Thm7_6_corrected := by
  intro _ _ P _ _ _ _ hX_nn hX2 hVar hSB hDiff
  exact sizeBias_tail_bounds P hX_nn hX2 hVar hSB hDiff

/-- Proof of Theorem 7.6(2), corrected optimization of `(7.12)` (`\label{2134b}`,
`SteinIntro.tex:3863-3870`; `ISSUE-7.6-PROOF`) holds. -/
theorem Sec7_3_eq7_12_minimizer_corrected_holds : Sec7_3_eq7_12_minimizer_corrected :=
  fun hC hμ hσ ht ↦ sec7_3_eq7_12_minimizer_corrected hC hμ hσ ht

/-- Example 7.6, corrected (unlabeled `example`, `SteinIntro.tex:3878-3884`; `ISSUE-EX7.6`,
`ISSUE-7.6`) holds. -/
theorem Ex7_6_corrected_holds : Ex7_6_corrected := by
  intro _ _ P _ _ _ hn _ _ hk hp0 hp1 hY_meas hIndep hY01 hProb
  exact circularRuns_sizeBias_concentration P hn hk hp0 hp1 hY_meas hIndep hY01 hProb

end SteinMethod
