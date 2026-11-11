/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Geometric.Basic
import Formalization.Geometric.Equilibrium
import Formalization.Geometric.OpeningBound
import Formalization.Geometric.UniformAttachment
import Formalization.Statements.Sec6

/-!
# Section 6 Proof Wrappers (`Formalization.Statements.Sec6Proofs`)

Connects each `: Prop` entry in `Formalization.Statements.Sec6` to its library theorem in
`Formalization.Geometric.*` (`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-- Refutation of the printed unscaled Section 6 opening Wasserstein display
(`SteinIntro.tex:3193-3198`; `ISSUE-6.0`) using $p = 1/4$ and $W \equiv 4$. -/
theorem not_Sec6_opening_wasserstein_printed :
    ¬ (∀ {Ω Ω' Ω'' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      (P'' : Measure Ω'') [IsProbabilityMeasure P'']
      {p : ℝ} {W : Ω → ℕ} {X : Ω' → ℕ} {Z : Ω'' → ℝ},
      0 < p →
      p ≤ 1 →
      AEMeasurable W P →
      (∀ᵐ ω ∂P, 0 < W ω) →
      Integrable (fun ω ↦ (W ω : ℝ)) P →
      ∫ ω, (W ω : ℝ) ∂P = 1 / p →
      AEMeasurable X P' →
      P'.map X = posGeomLaw p →
      AEMeasurable Z P'' →
      P''.map Z = ProbabilityTheory.expMeasure 1 →
      |(wassersteinDist (P.map (fun ω ↦ p * (W ω : ℝ))) (P''.map Z)).toReal -
          (wassersteinDist (P'.map (fun ω' ↦ (X ω' : ℝ)))
            (P.map (fun ω ↦ (W ω : ℝ)))).toReal| ≤ p) :=
  not_opening_wasserstein_printed

/-- Section 6 opening support-mismatch formula and limit (`SteinIntro.tex:3199-3200`) holds. -/
theorem Sec6_supportMismatch_holds : Sec6_supportMismatch := by
  refine ⟨?_, fun hk ↦ tendsto_supportMismatch hk⟩
  intro _ _ _ _ P _ P' _ _ _ _ _ hp0 hp1 hk hX hX_law hW_law
  exact tvDist_mul_posGeomLaw P P' hp0 hp1 hk hX hX_law hW_law

/-- Lemma 6.1(1) (`\label{lem173}`, `SteinIntro.tex:3229-3236`) holds. -/
theorem Lem6_1_1_holds : Lem6_1_1 := by
  intro _ _ P _ _ _ hp0 hp1 hZ hZ_law _ hf
  exact integral_geomSteinOp_eq_zero_of_map_eq P hp0 hp1 hZ hZ_law hf

/-- Lemma 6.1(2) (`\label{lem173}`, `SteinIntro.tex:3229-3241`; `ISSUE-6.1`) holds. -/
theorem Lem6_1_2_holds : Lem6_1_2 := by
  intro _ _ P _ _ _ hp0 hp1 hW hOp
  exact map_eq_geomLaw_of_integral_geomSteinOp_eq_zero P hp0 hp1 hW hOp

/-- Lemma 6.2 (`\label{lem174}`, `SteinIntro.tex:3243-3249, 3264-3274`; `ISSUE-TYPO-6.2`) holds. -/
theorem Lem6_2_holds : Lem6_2 :=
  fun {p} hp0 hp1 A ↦
    ⟨geomSteinSol_zero p A,
      geomSteinSol_steinEq hp0 hp1 A,
      fun _ hg0 hg ↦ eq_geomSteinSol_of_steinEq hp0 hp1 A hg0 hg,
      fwdDiff_geomSteinSol hp0 hp1 A,
      fwdDiff_geomSteinSol_bounds hp0 hp1 A⟩

/-- Theorem 6.3 (`\label{thm178}`, `SteinIntro.tex:3251-3258`) holds. -/
theorem Thm6_3_holds : Thm6_3 := by
  intro _ _ _ _ P _ P' _ _ _ _ hp0 hp1 hW _ _ _ hN_law
  exact tvDist_geomLaw_le P P' hp0 hp1 hW hN_law

/-- Proposition 6.4 (`\label{prop172}`, `SteinIntro.tex:3292-3296`; `ISSUE-6.4`) holds. -/
theorem Prop6_4_holds : Prop6_4 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hp0 hp1 hW hW_int hW_mean hSB hWe hUnif
  exact isDiscreteEquilibrium_of_isSizeBias_uniform P P' hp0 hp1 hW hW_int hW_mean hSB hWe hUnif

/-- Remark 6.2 & discrete equilibrium existence/uniqueness (`\label{rem175}`,
`SteinIntro.tex:3290-3291, 3304-3310`; `ISSUE-6.4`) holds for $0 < p < 1$. -/
theorem Rem6_2_restricted_holds : Rem6_2_restricted := by
  intro _ _ _ _ P _ _ _ hp0 hp1 hW hW_int hW_mean
  exact ⟨existsUnique_isDiscreteEquilibrium_measure P hp0 hp1 hW hW_int hW_mean,
    fun P' _ {_} hWe ↦ isDiscreteEquilibrium_iff_tail P P' hp0 hp1 hW hW_int hW_mean hWe⟩

/-- Theorem 6.5 (`\label{thm177}`, `SteinIntro.tex:3312-3319`) holds. -/
theorem Thm6_5_holds : Thm6_5 := by
  intro _ _ _ _ P _ P' _ _ _ _ _ hW2 hEq _ hN_law
  exact tvDist_le_of_isDiscreteEquilibrium P P' hW2 hEq hN_law

/-- Theorem 6.6 (`\label{thm1716}`, `SteinIntro.tex:3345-3350`; `ISSUE-TYPO-6.6`, `ISSUE-6.6`)
holds. -/
theorem Thm6_6_holds : Thm6_6 := by
  intro _ _ _ _ P _ P' _ _ hn _ _ _ hG hG_law hI hIndep hI_law hN hN_law
  exact tvDist_uniformAttachment_inDegree_le P P' hn hG hG_law hI hIndep hI_law hN hN_law

end SteinMethod
