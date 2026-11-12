/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.KolmogorovSolution
import Formalization.Normal.SolutionBounds
import Formalization.Normal.SteinLemma
import Formalization.Statements.Sec2
import Formalization.Sweep.SweepASec2

/-!
# Section 2 Proof Wrappers (`Formalization.Statements.Sec2Proofs`)

Connects every `: Prop` entry in `Formalization.Statements.Sec2` (`\label{stnorm}`,
`SteinIntro.tex:558-698`) to its library theorem in `Formalization.Normal` and
`Formalization.Sweep.SweepASec2` (`AGENTS.md` Rule 5).
-/

namespace SteinMethod

/-- Lemma 2.1(1) (`\label{lem1}`, unlabeled item 1, `SteinIntro.tex:562-569`) holds. -/
theorem Lem2_1_1_holds : Lem2_1_1 := by
  intro _ _ P _ _ _ hZ hZ_law hf hf'
  exact integral_normalSteinOp_eq_zero_of_map_eq P hZ hZ_law hf hf'

/-- Lemma 2.1(2) (`\label{lem1}`, unlabeled item 2, `SteinIntro.tex:562-574`; `D5` literal)
holds. -/
theorem Lem2_1_2_holds : Lem2_1_2 := by
  intro _ _ P _ _ hW hStein
  exact map_eq_stdNormalLaw_of_integral_normalSteinOp_eq_zero P hW hStein

/-- Lemma 2.2, corrected (`\label{lem2}`, eq. `(2.1)` `\label{1a}`, `SteinIntro.tex:578-588`;
`ISSUE-2.2`, `D4`) holds. -/
theorem Lem2_2_corrected_holds : Lem2_2_corrected :=
  fun x ↦
    ⟨bdd_normalSteinSolKolm x,
      continuous_normalSteinSolKolm x,
      hasDerivWithinAt_Iic_normalSteinSolKolm x,
      fun _ hw ↦ hasDerivAt_normalSteinSolKolm_of_ne x hw,
      normalSteinSolKolm_eq_neg_integral_Iic x,
      fun _ hBdd hCont hDeriv ↦ eq_normalSteinSolKolm_of_continuous_bounded x hBdd hCont hDeriv⟩

/-- Corollary 2.3, corrected (`\label{cor1}`, eq. `(2.2)` `\label{1}`, `SteinIntro.tex:591-596`;
`ISSUE-2.2`, `D4`) holds. -/
theorem Cor2_3_corrected_holds : Cor2_3_corrected := by
  intro _ _ P _ _ x hW
  exact abs_measureReal_Iic_sub_stdNormalCDF_eq P hW x

/-- Post-Corollary 2.3 all-$x$ characterization of $\mathcal{N}(0, 1)$ (unlabeled prose referencing
eq. `(2.2)` `\label{1}`, `SteinIntro.tex:597-600`; `ISSUE-2.2`) holds. -/
theorem Sec2_cor2_3_iff_stdNormal_holds : Sec2_cor2_3_iff_stdNormal :=
  sec2_cor2_3_iff_stdNormal_proof

/-- Gaussian upper-tail bound in the proof of Lemma 2.2 (unlabeled display,
`SteinIntro.tex:612-614`, Lemma 2.2 `\label{lem2}` at `SteinIntro.tex:578-588`) holds. -/
theorem Sec2_stdNormalCDF_tail_le_holds : Sec2_stdNormalCDF_tail_le :=
  sec2_stdNormalCDF_tail_le_proof

/-- Proposition 2.4 (`\label{prop31}`, eq. `(2.5)` `\label{31}`, `SteinIntro.tex:665-670`; `D4`
literal, `D1` guard) holds. -/
theorem Prop2_4_holds : Prop2_4 := by
  intro _ _ _ _ P _ P' _ _ _ H f hW _ hZ_law hf
  exact ipm_map_stdNormalLaw_eq_iSup_normalSteinOp P P' hW hZ_law H f hf

/-- Lemma 2.5, solution formula (`\label{lem31}`, eq. `(2.6)` `\label{33}`,
`SteinIntro.tex:674-684`; `ISSUE-2.2`) holds. -/
theorem Lem2_5_formula_holds : Lem2_5_formula :=
  ⟨fun _ hInt w ↦ normalSteinSol_eq_neg_integral_Iic hInt w,
    fun _ hInt hCont w ↦ hasDerivAt_normalSteinSol_of_continuous hInt hCont w⟩

/-- Lemma 2.5, pointwise ODE at continuity points (`\label{lem31}`, eq. `(2.6)` `\label{33}`,
`SteinIntro.tex:674-684`; `ISSUE-2.2`) holds. -/
theorem Lem2_5_ode_contAt_holds : Lem2_5_ode_contAt :=
  fun _ hInt _ hCont ↦ hasDerivAt_normalSteinSol hInt hCont

/-- Lemma 2.5(1) (`\label{lem31}` item 1 `\label{i31}`, `SteinIntro.tex:674-689`) holds. -/
theorem Lem2_5_1_holds : Lem2_5_1 :=
  fun hMeas hM w ↦
    ⟨abs_normalSteinSol_le_of_bounded hMeas hM w,
      abs_deriv_normalSteinSol_le_of_bounded hMeas hM w⟩

/-- Lemma 2.5(2) (`\label{lem31}` item 2 `\label{i32}`, `SteinIntro.tex:674-684`,
`SteinIntro.tex:690-695`; `D5`) holds. -/
theorem Lem2_5_2_holds : Lem2_5_2 :=
  fun hac hL w ↦
    ⟨abs_normalSteinSol_le_of_lipschitzDeriv hac hL w,
      abs_deriv_normalSteinSol_le_of_lipschitzDeriv hac hL w,
      abs_iteratedDeriv_two_normalSteinSol_le_of_lipschitzDeriv hac hL w⟩

end SteinMethod
