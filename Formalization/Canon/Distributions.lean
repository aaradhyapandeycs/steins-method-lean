/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.Sanity
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Canonical Probability Distribution Bridges

Formalization of canonical bridges connecting project definitions in `Formalization/Defs/Laws.lean`,
`Formalization/Defs/Exponential.lean`, `Formalization/Defs/Geometric.lean`,
`Formalization/Defs/Sanity.lean`, and `Formalization/Defs/Couplings.lean` with Mathlib's
distribution library (`ProbabilityTheory.gaussianReal`, `ProbabilityTheory.cdf`,
`ProbabilityTheory.poissonMeasure`, `ProbabilityTheory.expMeasure`,
`ProbabilityTheory.geometricMeasure`, `ProbabilityTheory.bernoulliMeasure`,
`ProbabilityTheory.cond volume`).

Reference: Nathan Ross, *Fundamentals of Stein's method*, `SteinIntro.tex`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-- Equivalence of project `normalLaw` (`Formalization/Defs/Laws.lean:24`, `SteinIntro.tex:562-574`)
and Mathlib's Gaussian measure `ProbabilityTheory.gaussianReal`. -/
theorem normalLaw_eq_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    normalLaw μ v = ProbabilityTheory.gaussianReal μ v := rfl

/-- Equivalence of project `stdNormalLaw` (`Formalization/Defs/Laws.lean:29`,
`SteinIntro.tex:562-574`) and Mathlib's `ProbabilityTheory.gaussianReal 0 1`. -/
theorem stdNormalLaw_eq_gaussianReal :
    stdNormalLaw = ProbabilityTheory.gaussianReal 0 1 := rfl

/-- Equivalence of project `stdNormalPDF` (`Formalization/Defs/Laws.lean:34`,
`SteinIntro.tex:630-635`) and Mathlib's `ProbabilityTheory.gaussianPDFReal 0 1`. -/
theorem stdNormalPDF_eq_gaussianPDFReal :
    stdNormalPDF = ProbabilityTheory.gaussianPDFReal 0 1 := rfl

/-- Equivalence of project `stdNormalCDF` (`Formalization/Defs/Laws.lean:40`, `SteinIntro.tex:353`)
and Mathlib's cumulative distribution function `ProbabilityTheory.cdf stdNormalLaw`. -/
theorem stdNormalCDF_eq_cdf_stdNormalLaw :
    stdNormalCDF = ProbabilityTheory.cdf stdNormalLaw := rfl

/-- Equivalence of project `stdNormalExpect` (`Formalization/Defs/NormalStein.lean:23`,
`SteinIntro.tex:663`) and the Bochner integral against `stdNormalLaw` /
`ProbabilityTheory.gaussianReal 0 1`. -/
theorem stdNormalExpect_eq_integral (h : ℝ → ℝ) :
    stdNormalExpect h = ∫ x, h x ∂stdNormalLaw := rfl

/-- Equivalence of project `poissonLaw` (`Formalization/Defs/Laws.lean:45`,
`SteinIntro.tex:1823-1848`) and Mathlib's `ProbabilityTheory.poissonMeasure`. -/
theorem poissonLaw_eq_poissonMeasure (r : ℝ≥0) :
    poissonLaw r = ProbabilityTheory.poissonMeasure r := rfl

/-- Equivalence of project `expLaw` (`Formalization/Defs/Exponential.lean:32`,
`SteinIntro.tex:2721-2724`) and Mathlib's `ProbabilityTheory.expMeasure`. -/
theorem expLaw_eq_expMeasure (r : ℝ) :
    expLaw r = ProbabilityTheory.expMeasure r := rfl

/-- Equivalence of project `stdExpLaw` (`Formalization/Defs/Exponential.lean:37`,
`SteinIntro.tex:2721-2724`) and Mathlib's `ProbabilityTheory.expMeasure 1`. -/
theorem stdExpLaw_eq_expMeasure_one :
    stdExpLaw = ProbabilityTheory.expMeasure 1 := rfl

/-- Equivalence of project `stdExpExpect` (`Formalization/Defs/Exponential.lean:42`,
`SteinIntro.tex:2741-2745`) and Bochner integral against Mathlib's
`ProbabilityTheory.expMeasure 1`. -/
theorem stdExpExpect_eq_integral (h : ℝ → ℝ) :
    stdExpExpect h = ∫ x, h x ∂stdExpLaw := rfl

/-- Definitional agreement of shifted geometric laws (`Formalization/Defs/Exponential.lean:84`
and `Formalization/Defs/Geometric.lean:47`, `SteinIntro.tex:2884`, `SteinIntro.tex:3194-3198`). -/
theorem shiftedGeomLaw_eq_posGeomLaw (p : ℝ) :
    shiftedGeomLaw p = posGeomLaw p := rfl

/-- Connection between project `geomLaw` (`Formalization/Defs/Geometric.lean:40`,
`SteinIntro.tex:3223-3225`) and Mathlib's `ProbabilityTheory.geometricMeasure` on `unitInterval`. -/
theorem geomLaw_eq_geometricMeasure (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    geomLaw p = ProbabilityTheory.geometricMeasure ⟨p, hp⟩ := by
  rw [geomLaw, Set.projIcc_of_mem _ hp]

/-- Connection of project `bernoulliHalfMeasure` (`Formalization/Defs/Sanity.lean:150`,
`SteinIntro.tex:1224-1230`) with Mathlib's `ProbabilityTheory.bernoulliMeasure`. -/
theorem bernoulliHalfMeasure_eq_bernoulliMeasure :
    bernoulliHalfMeasure =
      ProbabilityTheory.bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩ := by
  ext s hs
  simp only [bernoulliHalfMeasure, ProbabilityTheory.bernoulliMeasure_def, Measure.coe_add,
    Pi.add_apply, Measure.coe_nnreal_smul_apply]
  have h1 : unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ = (1 / 2 : ℝ≥0) := rfl
  have h2 : unitInterval.toNNReal (unitInterval.symm ⟨1 / 2, by norm_num, by norm_num⟩) =
      (1 / 2 : ℝ≥0) := by
    ext; norm_num [unitInterval.symm]
  rw [h1, h2]

/-- Project `bernoulliHalfRV` (`Formalization/Defs/Sanity.lean:164`, `SteinIntro.tex:1224-1230`)
equals core Lean's `Bool.toNat` cast to `ℝ`. -/
theorem bernoulliHalfRV_eq_toNat :
    bernoulliHalfRV = fun b : Bool ↦ (b.toNat : ℝ) := by
  funext b; cases b <;> simp [bernoulliHalfRV]

/-- Equivalence between `rademacherVal` (`Formalization/Defs/Sanity.lean:228`)
and `spin` (`Formalization/Defs/AntiVoter.lean:28`, `SteinIntro.tex:1102-1107`). -/
theorem rademacherVal_eq_spin :
    rademacherVal = spin := by
  funext b; cases b <;> rfl

/-- Project `uniformIccNegOneOne` (`Formalization/Defs/Sanity.lean:342`, `SteinIntro.tex:1442-1449`)
equals continuous conditional Lebesgue measure
`ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1)`.
(Note: Mathlib's `uniformOn` is counting measure conditioned on `s`, which vanishes on uncountable
sets; continuous uniform distributions are expressed via `ProbabilityTheory.cond volume` or
`MeasureTheory.pdf.IsUniform`.) -/
theorem uniformIccNegOneOne_eq_cond_volume :
    uniformIccNegOneOne = ProbabilityTheory.cond volume (Set.Icc (-1 : ℝ) 1) := by
  rw [uniformIccNegOneOne, ProbabilityTheory.cond, Real.volume_Icc]
  have htwo : ENNReal.ofReal ((1 : ℝ) - -1) = (2 : ℝ≥0∞) := by
    rw [show (1 : ℝ) - -1 = 2 by norm_num]
    simp only [ENNReal.ofReal_ofNat]
  rw [htwo]

/-- Project `uniformIccNegOneOne` (`Formalization/Defs/Sanity.lean:342`, `SteinIntro.tex:1442-1449`)
witnesses Mathlib's `MeasureTheory.pdf.IsUniform`. -/
theorem isUniform_id_uniformIccNegOneOne :
    MeasureTheory.pdf.IsUniform id (Set.Icc (-1 : ℝ) 1) uniformIccNegOneOne where
  aemeasurable := aemeasurable_id
  map_eq := by rw [Measure.map_id, uniformIccNegOneOne_eq_cond_volume]

/-- Radon–Nikodym characterization of `IsSizeBias` (`Formalization/Defs/Couplings.lean:39`,
`SteinIntro.tex:1224-1230`) via Mathlib's `Measure.withDensity` when $\mathbb{E}[X] > 0$. -/
theorem map_sizeBias_eq_withDensity
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Xs : Ω' → ℝ}
    (hX_meas : Measurable X) (hX_int : Integrable X P)
    (hX_pos : 0 < ∫ ω, X ω ∂P) (hsb : IsSizeBias P X P' Xs) :
    P'.map Xs = (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / ∫ ω, X ω ∂P)) := by
  rcases hsb with ⟨hX_nn, _, hXs_meas, hsb_eq⟩
  set μX : ℝ := ∫ ω, X ω ∂P
  refine Measure.ext fun A hA ↦ ?_
  let indA : ℝ → ℝ := A.indicator (fun _ ↦ (1 : ℝ))
  have hindA_meas : Measurable indA := measurable_const.indicator hA
  have hX_ind_eq : (fun ω ↦ X ω * indA (X ω)) = (X ⁻¹' A).indicator X := by
    funext ω
    by_cases hω : X ω ∈ A <;> simp [indA, hω]
  have hX_ind_int : Integrable (fun ω ↦ X ω * indA (X ω)) P := by
    rw [hX_ind_eq]
    exact hX_int.indicator (hX_meas hA)
  have hXs_real : (P'.map Xs).real A = ∫ ω', indA (Xs ω') ∂P' := by
    rw [← integral_map hXs_meas hindA_meas.stronglyMeasurable.aestronglyMeasurable,
      integral_indicator hA, setIntegral_one_eq_measureReal]
  have hreal_eq : (P'.map Xs).real A = ∫ ω, μX⁻¹ * (X ω * indA (X ω)) ∂P := by
    have hsb_val := hsb_eq indA hindA_meas hX_ind_int
    rw [← hXs_real] at hsb_val
    rw [integral_const_mul]
    have hdiv : (P'.map Xs).real A = (∫ ω, X ω * indA (X ω) ∂P) / μX := by
      rw [hsb_val, mul_div_cancel_left₀ _ hX_pos.ne']
    rw [hdiv]
    ring
  have hscaled_nn : 0 ≤ᵐ[P] fun ω ↦ μX⁻¹ * (X ω * indA (X ω)) := by
    filter_upwards [hX_nn] with ω hω
    have hind_nn : 0 ≤ indA (X ω) := by
      by_cases hx : X ω ∈ A <;> simp [indA, hx]
    exact mul_nonneg (inv_nonneg.mpr hX_pos.le) (mul_nonneg hω hind_nn)
  have hscaled_int : Integrable (fun ω ↦ μX⁻¹ * (X ω * indA (X ω))) P :=
    hX_ind_int.const_mul μX⁻¹
  have hd_meas : Measurable (fun x : ℝ ↦ ENNReal.ofReal (x / μX)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.div_const μX)
  calc
    (P'.map Xs) A = ENNReal.ofReal ((P'.map Xs).real A) := (ofReal_measureReal).symm
    _ = ENNReal.ofReal (∫ ω, μX⁻¹ * (X ω * indA (X ω)) ∂P) := by rw [hreal_eq]
    _ = ∫⁻ ω, ENNReal.ofReal (μX⁻¹ * (X ω * indA (X ω))) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hscaled_int hscaled_nn
    _ = ∫⁻ ω, A.indicator (fun x ↦ ENNReal.ofReal (x / μX)) (X ω) ∂P := by
      refine lintegral_congr fun ω ↦ ?_
      by_cases hω : X ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have hind : indA (X ω) = 1 := Set.indicator_of_mem hω _
        rw [hind, mul_one]
        congr 1
        ring
      · rw [Set.indicator_of_notMem hω]
        have hind : indA (X ω) = 0 := Set.indicator_of_notMem hω _
        rw [hind, mul_zero, mul_zero, ENNReal.ofReal_zero]
    _ = ∫⁻ x, A.indicator (fun x ↦ ENNReal.ofReal (x / μX)) x ∂(P.map X) :=
      (lintegral_map (hd_meas.indicator hA) hX_meas).symm
    _ = ∫⁻ x in A, ENNReal.ofReal (x / μX) ∂(P.map X) := lintegral_indicator hA _
    _ = ((P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μX))) A :=
      (withDensity_apply _ hA).symm

end SteinMethod
