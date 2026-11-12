/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.VectorMeasure.Operations
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-!
# Canonical Probability Metric Bridges

Formalization of canonical bridges connecting project definitions in
`Formalization/Defs/Metrics.lean` with Mathlib's probability metric and vector measure
library (`ProbabilityTheory.cdf`, `SignedMeasure.totalVariation`,
`Measure.toSignedMeasure`, `LipschitzWith 1`).

Reference: Nathan Ross, *Fundamentals of Stein's method*, `SteinIntro.tex:503-535`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-- Lower bound for integral probability metrics. -/
private lemma le_ipm {α : Type*} [MeasurableSpace α] {H : Set (α → ℝ)} {μ ν : Measure α}
    {g : α → ℝ} (hg : g ∈ H) (hint_μ : Integrable g μ) (hint_ν : Integrable g ν) :
    ENNReal.ofReal |(∫ x, g x ∂μ) - (∫ x, g x ∂ν)| ≤ ipm H μ ν := by
  refine le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le ⟨hint_μ, hint_ν⟩ le_rfl))

/-- Upper bound for integral probability metrics. -/
private lemma ipm_le {α : Type*} [MeasurableSpace α] {H : Set (α → ℝ)} {μ ν : Measure α}
    {c : ℝ≥0∞}
    (hbound : ∀ g ∈ H, Integrable g μ → Integrable g ν →
      ENNReal.ofReal |(∫ x, g x ∂μ) - (∫ x, g x ∂ν)| ≤ c) :
    ipm H μ ν ≤ c := by
  refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun ⟨h1, h2⟩ ↦ hbound g hg h1 h2

/-- Supremum characterization of Kolmogorov distance `kolmogorovDist`
(`Formalization/Defs/Metrics.lean:32`, `SteinIntro.tex:513-515`) in terms of Mathlib's
cumulative distribution function `ProbabilityTheory.cdf`. -/
theorem kolmogorovDist_eq_iSup_cdf (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kolmogorovDist μ ν =
      ⨆ x : ℝ, ENNReal.ofReal |ProbabilityTheory.cdf μ x - ProbabilityTheory.cdf ν x| := by
  apply le_antisymm
  · refine ipm_le fun g ⟨x, hx⟩ _ _ ↦ ?_
    subst hx
    rw [integral_indicator_one measurableSet_Iic, integral_indicator_one measurableSet_Iic,
      ← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real]
    exact le_iSup (fun y : ℝ ↦
      ENNReal.ofReal |ProbabilityTheory.cdf μ y - ProbabilityTheory.cdf ν y|) x
  · refine iSup_le fun x ↦ ?_
    have hint_μ : Integrable ((Set.Iic x).indicator (1 : ℝ → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Iic
    have hint_ν : Integrable ((Set.Iic x).indicator (1 : ℝ → ℝ)) ν :=
      (integrable_const (1 : ℝ)).indicator measurableSet_Iic
    have hle := le_ipm (H := {h | ∃ y, h = (Set.Iic y).indicator 1}) ⟨x, rfl⟩ hint_μ hint_ν
    rw [integral_indicator_one measurableSet_Iic,
      integral_indicator_one measurableSet_Iic,
      ← ProbabilityTheory.cdf_eq_real, ← ProbabilityTheory.cdf_eq_real] at hle
    exact hle

/-- Supremum characterization of total variation distance `tvDist`
(`Formalization/Defs/Metrics.lean:44`, `SteinIntro.tex:520-521`) over measurable events. -/
theorem tvDist_eq_iSup_abs_measureReal_sub {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν =
      ⨆ (A : Set α) (_ : MeasurableSet A), ENNReal.ofReal |μ.real A - ν.real A| := by
  apply le_antisymm
  · refine ipm_le fun g ⟨A, hA, hg⟩ _ _ ↦ ?_
    subst hg
    rw [integral_indicator_one hA, integral_indicator_one hA]
    exact le_iSup₂_of_le A hA le_rfl
  · refine iSup₂_le fun A hA ↦ ?_
    have hint_μ : Integrable (A.indicator (1 : α → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hA
    have hint_ν : Integrable (A.indicator (1 : α → ℝ)) ν :=
      (integrable_const (1 : ℝ)).indicator hA
    have hle := le_ipm (H := {h | ∃ B, MeasurableSet B ∧ h = B.indicator 1})
      ⟨A, hA, rfl⟩ hint_μ hint_ν
    rw [integral_indicator_one hA, integral_indicator_one hA] at hle
    exact hle

/-- Exact factor-2 relation between Mathlib's Hahn–Jordan total variation of
`(μ.toSignedMeasure - ν.toSignedMeasure)` (`Mathlib.MeasureTheory.SignedMeasure.totalVariation`)
and Ross's supremum-over-events total variation metric `tvDist μ ν`
(`Formalization/Defs/Metrics.lean:44`,
`SteinIntro.tex:520-521, 532-535`) on probability measures. -/
theorem signedMeasure_totalVariation_univ_eq_two_mul_tvDist {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ = 2 * tvDist μ ν := by
  set s : SignedMeasure α := μ.toSignedMeasure - ν.toSignedMeasure
  set j := s.toJordanDecomposition
  obtain ⟨T, hT, hposT, hnegTc⟩ := j.mutuallySingular
  set E := Tᶜ
  have hE : MeasurableSet E := hT.compl
  have hpos_Ec : j.posPart (Eᶜ) = 0 := by
    rw [show Eᶜ = T from compl_compl T]
    exact hposT
  have hneg_E : j.negPart E = 0 := hnegTc
  have hpos_univ : j.posPart Set.univ = j.posPart E := by
    have huni : Set.univ = E ∪ Eᶜ := (Set.union_compl_self E).symm
    rw [huni, measure_union disjoint_compl_right hE.compl, hpos_Ec, add_zero]
  have hneg_univ : j.negPart Set.univ = j.negPart (Eᶜ) := by
    have huni : Set.univ = E ∪ Eᶜ := (Set.union_compl_self E).symm
    rw [huni, measure_union disjoint_compl_right hE.compl, hneg_E, zero_add]
  have hs_apply (A : Set α) (hA : MeasurableSet A) : s A = μ.real A - ν.real A :=
    Measure.toSignedMeasure_sub_apply hA
  have hs_decomp (A : Set α) (hA : MeasurableSet A) : s A = j.posPart.real A - j.negPart.real A :=
    s.apply_eq_posPart_real_sub_negPart_real hA
  have hs_univ : s Set.univ = 0 := by
    rw [hs_apply Set.univ MeasurableSet.univ, measureReal_def, measureReal_def,
      measure_univ, measure_univ, sub_self]
  have hpos_real_univ : j.posPart.real Set.univ = j.negPart.real Set.univ := by
    have := hs_decomp Set.univ MeasurableSet.univ
    rw [hs_univ] at this
    exact sub_eq_zero.mp this.symm
  have hsE : s E = j.posPart.real Set.univ := by
    have h1 := hs_decomp E hE
    have h2 : j.negPart.real E = 0 := by
      rw [measureReal_def, hneg_E, ENNReal.toReal_zero]
    have h3 : j.posPart.real Set.univ = j.posPart.real E := by
      rw [measureReal_def, measureReal_def, hpos_univ]
    linarith
  have hpos_enn : j.posPart Set.univ = ENNReal.ofReal (s E) := by
    rw [hsE, ofReal_measureReal]
  have hneg_enn : j.negPart Set.univ = ENNReal.ofReal (s E) := by
    rw [hsE, hpos_real_univ, ofReal_measureReal]
  have htot : s.totalVariation Set.univ = 2 * ENNReal.ofReal (s E) := by
    rw [SignedMeasure.totalVariation, Measure.add_apply, hpos_enn, hneg_enn, ← two_mul]
  have htv_eq_sE : tvDist μ ν = ENNReal.ofReal (s E) := by
    rw [tvDist_eq_iSup_abs_measureReal_sub μ ν]
    apply le_antisymm
    · refine iSup₂_le fun A hA ↦ ?_
      rw [← hs_apply A hA]
      have hsA := hs_decomp A hA
      have hsA_le : s A ≤ s E := by
        rw [hsE]
        have hneg_nonneg : 0 ≤ j.negPart.real A := measureReal_nonneg
        have hpos_mono : j.posPart.real A ≤ j.posPart.real Set.univ :=
          measureReal_mono (Set.subset_univ A)
        linarith
      have hneg_sA_le : - s A ≤ s E := by
        rw [hsE, hpos_real_univ]
        have hpos_nonneg : 0 ≤ j.posPart.real A := measureReal_nonneg
        have hneg_mono : j.negPart.real A ≤ j.negPart.real Set.univ :=
          measureReal_mono (Set.subset_univ A)
        linarith
      have habs_le : |s A| ≤ s E := abs_le.mpr ⟨by linarith, hsA_le⟩
      exact ENNReal.ofReal_le_ofReal habs_le
    · have hsE_nonneg : 0 ≤ s E := by
        rw [hsE]
        exact measureReal_nonneg
      have hle : ENNReal.ofReal |μ.real E - ν.real E| ≤
          ⨆ (A : Set α) (_ : MeasurableSet A), ENNReal.ofReal |μ.real A - ν.real A| :=
        le_iSup₂
          (f := fun A (_ : MeasurableSet A) ↦ ENNReal.ofReal |μ.real A - ν.real A|) E hE
      rw [← hs_apply E hE, abs_of_nonneg hsE_nonneg] at hle
      exact hle
  rw [htot, htv_eq_sE]

/-- Half total variation formula:
`tvDist μ ν = (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ / 2`
for probability measures (`Formalization/Defs/Metrics.lean:44`,
`SteinIntro.tex:520-521, 532-535`). -/
theorem tvDist_eq_half_signedMeasure_totalVariation {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ / 2 := by
  rw [signedMeasure_totalVariation_univ_eq_two_mul_tvDist μ ν,
    mul_comm, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

/-- Definitional equivalence of `wassersteinDist` (`Formalization/Defs/Metrics.lean:37`,
`SteinIntro.tex:516-519`) and IPM over $1$-Lipschitz functions `LipschitzWith 1`. -/
theorem wassersteinDist_eq_ipm_lipschitzWith_one (μ ν : Measure ℝ) :
    wassersteinDist μ ν = ipm {h : ℝ → ℝ | LipschitzWith 1 h} μ ν := rfl

end SteinMethod
