/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Metrics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Basic Properties of Integral Probability Metrics (`Formalization.Metrics.Basic`)

Measure-level and random-variable-level properties of `ipm`, `kolmogorovDist`, `wassersteinDist`,
and `tvDist` in `ℝ≥0∞`, supporting Section 1 Proposition 1.2 (`\label{prop22}`,
`SteinIntro.tex:523-537`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### General integral probability metric (`ipm`) lemmas -/

/-- Any integrable test function in `H` gives a lower bound on `ipm H μ ν`
(eq. `(1.1)` `\label{23}`, `SteinIntro.tex:503-509`). -/
theorem le_ipm {α : Type*} [MeasurableSpace α] {H : Set (α → ℝ)} {μ ν : Measure α}
    {h : α → ℝ} (hh : h ∈ H) (hμ : Integrable h μ) (hν : Integrable h ν) :
    ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| ≤ ipm H μ ν := by
  unfold ipm
  exact le_iSup₂_of_le h hh (le_iSup_of_le ⟨hμ, hν⟩ le_rfl)

/-- Upper bound criterion for `ipm H μ ν`
(eq. `(1.1)` `\label{23}`, `SteinIntro.tex:503-509`). -/
theorem ipm_le {α : Type*} [MeasurableSpace α] {H : Set (α → ℝ)} {μ ν : Measure α} {c : ℝ≥0∞}
    (hc : ∀ h ∈ H, Integrable h μ → Integrable h ν →
      ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| ≤ c) :
    ipm H μ ν ≤ c :=
  iSup₂_le fun h hh ↦ iSup_le fun hInt ↦ hc h hh hInt.1 hInt.2

/-- The integral probability metric of a measure with itself is zero
(eq. `(1.1)` `\label{23}`, `SteinIntro.tex:503-509`). -/
@[simp]
theorem ipm_self {α : Type*} [MeasurableSpace α] (H : Set (α → ℝ)) (μ : Measure α) :
    ipm H μ μ = 0 := by
  refine le_antisymm ?_ zero_le
  exact ipm_le fun _ _ _ _ ↦ by simp only [sub_self, abs_zero, ENNReal.ofReal_zero, le_rfl]

/-- Symmetry of `ipm H μ ν` in `(μ, ν)`
(eq. `(1.1)` `\label{23}`, `SteinIntro.tex:503-509`). -/
theorem ipm_symm {α : Type*} [MeasurableSpace α] (H : Set (α → ℝ)) (μ ν : Measure α) :
    ipm H μ ν = ipm H ν μ := by
  have aux : ∀ μ' ν' : Measure α, ipm H μ' ν' ≤ ipm H ν' μ' := fun μ' ν' ↦
    ipm_le fun _ hh hμ' hν' ↦ by
      rw [abs_sub_comm]
      exact le_ipm hh hν' hμ'
  exact le_antisymm (aux μ ν) (aux ν μ)

/-- Monotonicity of `ipm` with respect to inclusion of test-function classes
(eq. `(1.1)` `\label{23}`, `SteinIntro.tex:503-509`). -/
theorem ipm_mono {α : Type*} [MeasurableSpace α] {H₁ H₂ : Set (α → ℝ)}
    (hH : H₁ ⊆ H₂) (μ ν : Measure α) :
    ipm H₁ μ ν ≤ ipm H₂ μ ν :=
  ipm_le fun _ hh hμ hν ↦ le_ipm (hH hh) hμ hν

/-! ### Explicit `iSup` characterizations and Proposition 1.2(1) -/

/-- Supremum characterization of `kolmogorovDist` over half-lines `(-∞, x]` for finite measures
(Section 1.1.1 item 1 `\label{probmet}`, `SteinIntro.tex:513-515`). -/
theorem kolmogorovDist_eq_iSup (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kolmogorovDist μ ν =
      ⨆ x : ℝ, ENNReal.ofReal |μ.real (Set.Iic x) - ν.real (Set.Iic x)| := by
  apply le_antisymm
  · refine ipm_le fun h hh _ _ ↦ ?_
    rcases hh with ⟨x, rfl⟩
    rw [integral_indicator_one measurableSet_Iic, integral_indicator_one measurableSet_Iic]
    exact le_iSup (fun y : ℝ ↦ ENNReal.ofReal |μ.real (Set.Iic y) - ν.real (Set.Iic y)|) x
  · refine iSup_le fun x ↦ ?_
    rw [← integral_indicator_one (μ := μ) measurableSet_Iic,
      ← integral_indicator_one (μ := ν) measurableSet_Iic]
    exact le_ipm ⟨x, rfl⟩
      ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
      ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)

/-- Supremum characterization of `tvDist` over measurable events `A` for finite measures
(Section 1.1.1 item 3 `\label{probmet}`, `SteinIntro.tex:520-521`). -/
theorem tvDist_eq_iSup {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν =
      ⨆ (A : Set α) (_ : MeasurableSet A), ENNReal.ofReal |μ.real A - ν.real A| := by
  apply le_antisymm
  · refine ipm_le fun h hh _ _ ↦ ?_
    rcases hh with ⟨A, hA, rfl⟩
    rw [integral_indicator_one hA, integral_indicator_one hA]
    exact le_iSup₂_of_le A hA le_rfl
  · refine iSup₂_le fun A hA ↦ ?_
    rw [← integral_indicator_one (μ := μ) hA, ← integral_indicator_one (μ := ν) hA]
    exact le_ipm ⟨A, hA, rfl⟩
      ((integrable_const (1 : ℝ)).indicator hA)
      ((integrable_const (1 : ℝ)).indicator hA)

/-- Measure-level Proposition 1.2(1) (`\label{prop22}`, `SteinIntro.tex:523-526`):
`kolmogorovDist μ ν ≤ tvDist μ ν` since every half-line `Set.Iic x` is measurable. -/
theorem kolmogorovDist_le_tvDist (μ ν : Measure ℝ) :
    kolmogorovDist μ ν ≤ tvDist μ ν := by
  refine ipm_mono (fun h hh ↦ ?_) μ ν
  rcases hh with ⟨x, rfl⟩
  exact ⟨Set.Iic x, measurableSet_Iic, rfl⟩

/-- Random-variable-level Proposition 1.2(1) (`\label{prop22}`, `SteinIntro.tex:523-526`):
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z))$. -/
theorem kolmogorovDist_map_le_tvDist_map {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (W : Ω → ℝ) (Z : Ω' → ℝ) :
    kolmogorovDist (P.map W) (P'.map Z) ≤ tvDist (P.map W) (P'.map Z) :=
  kolmogorovDist_le_tvDist (P.map W) (P'.map Z)

/-! ### Proposition 1.2(2): Kolmogorov–Wasserstein inequality under bounded Lebesgue density -/

private def kolmRamp (a ε w : ℝ) : ℝ :=
  min ε (max 0 (a + ε - w))

private lemma lipschitzWith_kolmRamp (a ε : ℝ) : LipschitzWith 1 (kolmRamp a ε) := by
  have hlin : LipschitzWith 1 (fun w : ℝ ↦ a + ε - w) :=
    LipschitzWith.mk_one fun u v ↦ by
      have hsub : (a + ε - u) - (a + ε - v) = -(u - v) := by ring
      rw [Real.dist_eq, Real.dist_eq, hsub, abs_neg]
  exact (hlin.const_max 0).const_min ε

private lemma kolmRamp_mem_Icc {a ε : ℝ} (hε : 0 ≤ ε) (w : ℝ) :
    kolmRamp a ε w ∈ Set.Icc 0 ε :=
  ⟨le_min hε (le_max_left 0 (a + ε - w)), min_le_left ε (max 0 (a + ε - w))⟩

private lemma integrable_kolmRamp (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (kolmRamp a ε) μ :=
  Integrable.of_mem_Icc 0 ε (lipschitzWith_kolmRamp a ε).continuous.aemeasurable
    (Filter.Eventually.of_forall (kolmRamp_mem_Icc hε))

private lemma indicator_Iic_le_kolmRamp (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (w : ℝ) :
    (Set.Iic x).indicator (fun _ ↦ ε) w ≤ kolmRamp x ε w := by
  by_cases hw : w ≤ x
  · have hmem : w ∈ Set.Iic x := hw
    simp only [kolmRamp, Set.indicator_of_mem hmem]
    exact le_min le_rfl (le_trans (by linarith) (le_max_right 0 (x + ε - w)))
  · have hnot : w ∉ Set.Iic x := hw
    simp only [Set.indicator_of_notMem hnot]
    exact (kolmRamp_mem_Icc hε w).1

private lemma kolmRamp_sub_indicator_Iic (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (w : ℝ) :
    kolmRamp x ε w - (Set.Iic x).indicator (fun _ ↦ ε) w =
      (Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u) w := by
  by_cases hw1 : w ≤ x
  · have hmem : w ∈ Set.Iic x := hw1
    have hnot : w ∉ Set.Ioc x (x + ε) := fun h ↦ not_lt_of_ge hw1 h.1
    simp only [kolmRamp, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot]
    have hmax : max 0 (x + ε - w) = x + ε - w := max_eq_right (by linarith)
    have hmin : min ε (x + ε - w) = ε := min_eq_left (by linarith)
    rw [hmax, hmin, sub_self]
  · have hlt1 : x < w := lt_of_not_ge hw1
    have hnotIic : w ∉ Set.Iic x := hw1
    by_cases hw2 : w ≤ x + ε
    · have hmem : w ∈ Set.Ioc x (x + ε) := ⟨hlt1, hw2⟩
      simp only [kolmRamp, Set.indicator_of_notMem hnotIic, Set.indicator_of_mem hmem, sub_zero]
      have hmax : max 0 (x + ε - w) = x + ε - w := max_eq_right (by linarith)
      rw [hmax]
      exact min_eq_right (by linarith)
    · have hnot : w ∉ Set.Ioc x (x + ε) := fun h ↦ hw2 h.2
      simp only [kolmRamp, Set.indicator_of_notMem hnotIic, Set.indicator_of_notMem hnot, sub_zero]
      have hmax : max 0 (x + ε - w) = 0 := max_eq_left (by linarith)
      rw [hmax]
      exact min_eq_right hε

private lemma kolmRamp_sub_le_indicator_Iic (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (w : ℝ) :
    kolmRamp (x - ε) ε w ≤ (Set.Iic x).indicator (fun _ ↦ ε) w := by
  by_cases hw : w ≤ x
  · have hmem : w ∈ Set.Iic x := hw
    simp only [Set.indicator_of_mem hmem]
    exact (kolmRamp_mem_Icc hε w).2
  · have hnot : w ∉ Set.Iic x := hw
    simp only [kolmRamp, Set.indicator_of_notMem hnot]
    have hmax : max 0 (x - ε + ε - w) = 0 := max_eq_left (by linarith)
    rw [hmax]
    exact min_le_right ε 0

private lemma indicator_Iic_sub_kolmRamp (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (w : ℝ) :
    (Set.Iic x).indicator (fun _ ↦ ε) w - kolmRamp (x - ε) ε w =
      (Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)) w := by
  by_cases hw1 : w ≤ x - ε
  · have hmem : w ∈ Set.Iic x := Set.mem_Iic.mpr (by linarith)
    have hnot : w ∉ Set.Ioc (x - ε) x := fun h ↦ not_lt_of_ge hw1 h.1
    simp only [kolmRamp, Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot]
    have hmax : max 0 (x - ε + ε - w) = x - ε + ε - w := max_eq_right (by linarith)
    have hmin : min ε (x - ε + ε - w) = ε := min_eq_left (by linarith)
    rw [hmax, hmin, sub_self]
  · have hlt1 : x - ε < w := lt_of_not_ge hw1
    by_cases hw2 : w ≤ x
    · have hmemIic : w ∈ Set.Iic x := hw2
      have hmem : w ∈ Set.Ioc (x - ε) x := ⟨hlt1, hw2⟩
      simp only [kolmRamp, Set.indicator_of_mem hmemIic, Set.indicator_of_mem hmem]
      have hmax : max 0 (x - ε + ε - w) = x - ε + ε - w := max_eq_right (by linarith)
      have hmin : min ε (x - ε + ε - w) = x - ε + ε - w := min_eq_right (by linarith)
      rw [hmax, hmin]
      ring
    · have hnotIic : w ∉ Set.Iic x := hw2
      have hnot : w ∉ Set.Ioc (x - ε) x := fun h ↦ hw2 h.2
      simp only [kolmRamp, Set.indicator_of_notMem hnotIic, Set.indicator_of_notMem hnot, zero_sub]
      have hmax : max 0 (x - ε + ε - w) = 0 := max_eq_left (by linarith)
      have hmin : min ε 0 = 0 := min_eq_right hε
      rw [hmax, hmin, neg_zero]

private lemma integral_upper_ramp_diff (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∫ u, (Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u) u ∂volume = ε ^ 2 / 2 := by
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : x ≤ x + ε),
    intervalIntegral.integral_comp_sub_left (fun t : ℝ ↦ t) (x + ε),
    integral_id]
  ring

private lemma integral_lower_ramp_diff (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∫ u, (Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)) u ∂volume = ε ^ 2 / 2 := by
  rw [integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : x - ε ≤ x),
    intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ t) (x - ε),
    integral_id]
  ring

private lemma kolmogorov_eps_bound (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 < C) (hν_le : ν ≤ ENNReal.ofReal C • (volume : Measure ℝ))
    (hd : wassersteinDist μ ν ≠ ⊤) (x : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ε * |μ.real (Set.Iic x) - ν.real (Set.Iic x)| ≤
      (wassersteinDist μ ν).toReal + C * (ε ^ 2 / 2) := by
  let d : ℝ := (wassersteinDist μ ν).toReal
  have hwass : ∀ a : ℝ, |(∫ w, kolmRamp a ε w ∂μ) - (∫ w, kolmRamp a ε w ∂ν)| ≤ d := fun a ↦ by
    have hle : ENNReal.ofReal |(∫ w, kolmRamp a ε w ∂μ) - (∫ w, kolmRamp a ε w ∂ν)| ≤
        ENNReal.ofReal d := by
      rw [ENNReal.ofReal_toReal hd]
      exact le_ipm (lipschitzWith_kolmRamp a ε)
        (integrable_kolmRamp μ a hε) (integrable_kolmRamp ν a hε)
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hle
  have hIic : ∀ μ' : Measure ℝ, [IsFiniteMeasure μ'] →
      ∫ w, (Set.Iic x).indicator (fun _ ↦ ε) w ∂μ' = ε * μ'.real (Set.Iic x) := fun μ' _ ↦ by
    rw [integral_indicator_const ε measurableSet_Iic, smul_eq_mul, mul_comm]
  rcases le_total (ν.real (Set.Iic x)) (μ.real (Set.Iic x)) with hle | hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle), mul_sub]
    have hμ_le : ε * μ.real (Set.Iic x) ≤ ∫ w, kolmRamp x ε w ∂μ := by
      rw [← hIic μ]
      exact integral_mono ((integrable_const ε).indicator measurableSet_Iic)
        (integrable_kolmRamp μ x hε) (indicator_Iic_le_kolmRamp x hε)
    have hν_diff : (∫ w, kolmRamp x ε w ∂ν) - ε * ν.real (Set.Iic x) ≤ C * (ε ^ 2 / 2) := by
      have heq : (∫ w, kolmRamp x ε w ∂ν) - ε * ν.real (Set.Iic x) =
          ∫ w, (Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u) w ∂ν := by
        rw [← hIic ν, ← integral_sub (integrable_kolmRamp ν x hε)
          ((integrable_const ε).indicator measurableSet_Iic)]
        exact congrArg (fun g ↦ ∫ w, g w ∂ν) (funext (kolmRamp_sub_indicator_Iic x hε))
      rw [heq]
      have hnn : 0 ≤ᵐ[ENNReal.ofReal C • (volume : Measure ℝ)]
          (Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u) :=
        Filter.Eventually.of_forall fun w ↦ by
          change 0 ≤ (Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u) w
          rw [← kolmRamp_sub_indicator_Iic x hε w]
          exact sub_nonneg.mpr (indicator_Iic_le_kolmRamp x hε w)
      have hint : Integrable ((Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u))
          (ENNReal.ofReal C • (volume : Measure ℝ)) :=
        (((continuous_const.sub continuous_id').integrableOn_Ioc).integrable_indicator
          measurableSet_Ioc).smul_measure ENNReal.ofReal_ne_top
      calc
        ∫ w, (Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u) w ∂ν
          ≤ ∫ w, (Set.Ioc x (x + ε)).indicator (fun u ↦ x + ε - u) w
              ∂(ENNReal.ofReal C • (volume : Measure ℝ)) :=
            integral_mono_measure hν_le hnn hint
        _ = C * (ε ^ 2 / 2) := by
            rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul,
              integral_upper_ramp_diff x hε]
    have hwass1 : (∫ w, kolmRamp x ε w ∂μ) - (∫ w, kolmRamp x ε w ∂ν) ≤ d :=
      le_of_abs_le (hwass x)
    linarith [hμ_le, hwass1, hν_diff]
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle), mul_sub]
    have hμ_ge : ∫ w, kolmRamp (x - ε) ε w ∂μ ≤ ε * μ.real (Set.Iic x) := by
      rw [← hIic μ]
      exact integral_mono (integrable_kolmRamp μ (x - ε) hε)
        ((integrable_const ε).indicator measurableSet_Iic)
        (kolmRamp_sub_le_indicator_Iic x hε)
    have hν_diff : ε * ν.real (Set.Iic x) - (∫ w, kolmRamp (x - ε) ε w ∂ν) ≤ C * (ε ^ 2 / 2) := by
      have heq : ε * ν.real (Set.Iic x) - (∫ w, kolmRamp (x - ε) ε w ∂ν) =
          ∫ w, (Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)) w ∂ν := by
        rw [← hIic ν, ← integral_sub ((integrable_const ε).indicator measurableSet_Iic)
          (integrable_kolmRamp ν (x - ε) hε)]
        exact congrArg (fun g ↦ ∫ w, g w ∂ν) (funext (indicator_Iic_sub_kolmRamp x hε))
      rw [heq]
      have hnn : 0 ≤ᵐ[ENNReal.ofReal C • (volume : Measure ℝ)]
          (Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)) :=
        Filter.Eventually.of_forall fun w ↦ by
          change 0 ≤ (Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)) w
          rw [← indicator_Iic_sub_kolmRamp x hε w]
          exact sub_nonneg.mpr (kolmRamp_sub_le_indicator_Iic x hε w)
      have hint : Integrable ((Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)))
          (ENNReal.ofReal C • (volume : Measure ℝ)) :=
        (((continuous_id'.sub continuous_const).integrableOn_Ioc).integrable_indicator
          measurableSet_Ioc).smul_measure ENNReal.ofReal_ne_top
      calc
        ∫ w, (Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)) w ∂ν
          ≤ ∫ w, (Set.Ioc (x - ε) x).indicator (fun u ↦ u - (x - ε)) w
              ∂(ENNReal.ofReal C • (volume : Measure ℝ)) :=
            integral_mono_measure hν_le hnn hint
        _ = C * (ε ^ 2 / 2) := by
            rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul,
              integral_lower_ramp_diff x hε]
    have hwass2 : (∫ w, kolmRamp (x - ε) ε w ∂ν) - (∫ w, kolmRamp (x - ε) ε w ∂μ) ≤ d := by
      have hcomm := hwass (x - ε)
      rw [abs_sub_comm] at hcomm
      exact le_of_abs_le hcomm
    linarith [hμ_ge, hwass2, hν_diff]

private lemma optimize_eps_bound {a C d : ℝ} (ha : 0 ≤ a) (hC : 0 < C)
    (hbound : ∀ ε : ℝ, 0 < ε → ε * a ≤ d + C * (ε ^ 2 / 2)) :
    a ≤ √(2 * C * d) := by
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · exact Real.sqrt_nonneg _
  · have h1 : (a / C) * a ≤ d + C * ((a / C) ^ 2 / 2) := hbound (a / C) (div_pos ha_pos hC)
    have h2 : C * ((a / C) * a) ≤ C * (d + C * ((a / C) ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left h1 hC.le
    have hC_ne : C ≠ 0 := hC.ne'
    have hlhs : C * ((a / C) * a) = a ^ 2 := by
      calc
        C * ((a / C) * a) = (C * (a / C)) * a := by ring
        _ = a * a := by rw [mul_div_cancel₀ a hC_ne]
        _ = a ^ 2 := by ring
    have hrhs : C * (d + C * ((a / C) ^ 2 / 2)) = C * d + a ^ 2 / 2 := by
      calc
        C * (d + C * ((a / C) ^ 2 / 2)) = C * d + (C * (a / C)) ^ 2 / 2 := by ring
        _ = C * d + a ^ 2 / 2 := by rw [mul_div_cancel₀ a hC_ne]
    rw [hlhs, hrhs] at h2
    have hsq : a ^ 2 ≤ 2 * C * d := by linarith
    calc
      a = √(a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ √(2 * C * d) := Real.sqrt_le_sqrt hsq

/-- Measure-level Proposition 1.2(2) (`\label{prop22}`, `SteinIntro.tex:527-531`): if `ν` is a
probability measure on `ℝ` with Lebesgue density bounded almost everywhere by `C`, then
`kolmogorovDist μ ν ≤ (2 * ENNReal.ofReal C * wassersteinDist μ ν) ^ (1 / 2 : ℝ)`. -/
theorem kolmogorovDist_le_rpow_wassersteinDist (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : ℝ} (f : ℝ → ℝ≥0∞)
    (hν : ν = volume.withDensity f)
    (hf : ∀ᵐ x ∂volume, f x ≤ ENNReal.ofReal C) :
    kolmogorovDist μ ν ≤ (2 * ENNReal.ofReal C * wassersteinDist μ ν) ^ (1 / 2 : ℝ) := by
  have hν_le : ν ≤ ENNReal.ofReal C • (volume : Measure ℝ) := by
    rw [hν, ← withDensity_const (ENNReal.ofReal C)]
    exact withDensity_mono hf
  have hC : 0 < C := by
    by_contra hC_le
    have hzero : ENNReal.ofReal C = 0 := ENNReal.ofReal_eq_zero.mpr (not_lt.mp hC_le)
    have huniv : ν Set.univ ≤ 0 := by
      calc
        ν Set.univ ≤ (ENNReal.ofReal C • (volume : Measure ℝ)) Set.univ := hν_le Set.univ
        _ = 0 := by simp only [hzero, zero_smul, Measure.coe_zero, Pi.zero_apply]
    have hone : (1 : ℝ≥0∞) ≤ 0 := by rwa [measure_univ] at huniv
    exact one_ne_zero (le_antisymm hone zero_le)
  rcases eq_or_ne (wassersteinDist μ ν) ⊤ with hd_top | hd_ne_top
  · have h2C_ne_zero : (2 : ℝ≥0∞) * ENNReal.ofReal C ≠ 0 :=
      mul_ne_zero two_ne_zero (ENNReal.ofReal_pos.mpr hC).ne'
    rw [hd_top, ENNReal.mul_top h2C_ne_zero,
      ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact le_top
  · let d : ℝ := (wassersteinDist μ ν).toReal
    have hrhs : (2 * ENNReal.ofReal C * wassersteinDist μ ν) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (√(2 * C * d)) := by
      have h2C : (2 : ℝ≥0∞) * ENNReal.ofReal C = ENNReal.ofReal (2 * C) := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat 2]
      have hprod : 2 * ENNReal.ofReal C * wassersteinDist μ ν = ENNReal.ofReal (2 * C * d) := by
        rw [h2C, ← ENNReal.ofReal_toReal hd_ne_top,
          ← ENNReal.ofReal_mul (mul_nonneg zero_le_two hC.le)]
      rw [hprod, ENNReal.ofReal_rpow_of_nonneg
        (mul_nonneg (mul_nonneg zero_le_two hC.le) ENNReal.toReal_nonneg)
        (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.sqrt_eq_rpow]
    rw [kolmogorovDist_eq_iSup, hrhs]
    refine iSup_le fun x ↦ ENNReal.ofReal_le_ofReal ?_
    exact optimize_eps_bound (abs_nonneg _) hC fun ε hε_pos ↦
      kolmogorov_eps_bound μ ν hC hν_le hd_ne_top x hε_pos.le

/-- Random-variable-level Proposition 1.2(2) (`\label{prop22}`, `SteinIntro.tex:527-531`): if
`P'.map Z` has Lebesgue density bounded almost everywhere by `C`, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
(2 C \, d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)))^{1/2}$. -/
theorem kolmogorovDist_map_le_rpow_wassersteinDist_map {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ} {C : ℝ} (f : ℝ → ℝ≥0∞)
    (hZ_dens : P'.map Z = volume.withDensity f)
    (hf : ∀ᵐ x ∂volume, f x ≤ ENNReal.ofReal C) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      (2 * ENNReal.ofReal C * wassersteinDist (P.map W) (P'.map Z)) ^ (1 / 2 : ℝ) :=
  kolmogorovDist_le_rpow_wassersteinDist (P.map W) (P'.map Z) f hZ_dens hf

/-! ### Proposition 1.2(3): Discrete total variation identity -/

private lemma measureReal_eq_tsum_indicator {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] (A : Set S) :
    μ.real A = ∑' s : S, A.indicator (fun s ↦ μ.real {s}) s := by
  have hA : MeasurableSet A := (Set.to_countable A).measurableSet
  have h1 : μ.real A = (∑' s : S, A.indicator (fun s ↦ μ {s}) s).toReal := by
    rw [Measure.tsum_indicator_apply_singleton μ A hA, measureReal_def]
  rw [h1, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun s ↦ ?_
    by_cases hs : s ∈ A
    · simp only [Set.indicator_of_mem hs, measureReal_def]
    · simp only [Set.indicator_of_notMem hs, ENNReal.toReal_zero]
  · intro s
    by_cases hs : s ∈ A
    · rw [Set.indicator_of_mem hs]
      exact measure_ne_top μ {s}
    · rw [Set.indicator_of_notMem hs]
      exact ENNReal.zero_ne_top

private lemma summable_measureReal_singleton {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsFiniteMeasure μ] :
    Summable (fun s : S ↦ μ.real {s}) := by
  have hsum : (∑' s : S, μ {s}) ≠ ⊤ := by
    have heq : (∑' s : S, μ {s}) = μ Set.univ := by
      simpa only [Set.indicator_univ] using
        Measure.tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ
    rw [heq]
    exact measure_ne_top μ Set.univ
  simpa only [measureReal_def] using ENNReal.summable_toReal hsum

/-- Measure-level Proposition 1.2(3) (`\label{prop22}`, `SteinIntro.tex:532-537`): for probability
measures `μ` and `ν` on a countable measurable-singleton space `S`,
`tvDist μ ν = (1 / 2 : ℝ≥0∞) * ∑' s : S, ENNReal.ofReal |μ.real {s} - ν.real {s}|`. -/
theorem tvDist_eq_half_tsum {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν =
      (1 / 2 : ℝ≥0∞) * ∑' s : S, ENNReal.ofReal |μ.real {s} - ν.real {s}| := by
  let d : S → ℝ := fun s ↦ μ.real {s} - ν.real {s}
  have hsum_μ : Summable (fun s : S ↦ μ.real {s}) := summable_measureReal_singleton μ
  have hsum_ν : Summable (fun s : S ↦ ν.real {s}) := summable_measureReal_singleton ν
  have hsum_d : Summable d := hsum_μ.sub hsum_ν
  have hsum_abs : Summable (fun s : S ↦ |d s|) := hsum_d.abs
  have hdiff_A : ∀ A : Set S, μ.real A - ν.real A = ∑' s : S, A.indicator d s := fun A ↦ by
    rw [measureReal_eq_tsum_indicator μ A, measureReal_eq_tsum_indicator ν A,
      ← (hsum_μ.indicator A).tsum_sub (hsum_ν.indicator A)]
    refine tsum_congr fun s ↦ ?_
    by_cases hs : s ∈ A
    · simp only [d, Set.indicator_of_mem hs]
    · simp only [Set.indicator_of_notMem hs, sub_zero]
  have htsum_d : (∑' s : S, d s) = 0 := by
    have huniv := hdiff_A Set.univ
    simp only [probReal_univ, sub_self, Set.indicator_univ] at huniv
    exact huniv.symm
  have htwo_mul : ∀ A : Set S,
      2 * (μ.real A - ν.real A) = ∑' s : S, (A.indicator d s - Aᶜ.indicator d s) := fun A ↦ by
    have hadd : (∑' s : S, A.indicator d s) + (∑' s : S, Aᶜ.indicator d s) = 0 := by
      rw [← (hsum_d.indicator A).tsum_add (hsum_d.indicator Aᶜ)]
      have hcongr : (fun s : S ↦ A.indicator d s + Aᶜ.indicator d s) = d := by
        ext s
        by_cases hs : s ∈ A
        · have hnot : s ∉ Aᶜ := fun h ↦ h hs
          simp only [Set.indicator_of_mem hs, Set.indicator_of_notMem hnot, add_zero]
        · have hmem : s ∈ Aᶜ := hs
          simp only [Set.indicator_of_notMem hs, Set.indicator_of_mem hmem, zero_add]
      rw [hcongr, htsum_d]
    rw [hdiff_A A, (hsum_d.indicator A).tsum_sub (hsum_d.indicator Aᶜ)]
    linarith
  have hle_A : ∀ A : Set S, |μ.real A - ν.real A| ≤ (1 / 2 : ℝ) * ∑' s : S, |d s| := fun A ↦ by
    have hnorm_eq : (fun s : S ↦ ‖A.indicator d s - Aᶜ.indicator d s‖) = fun s ↦ |d s| := by
      ext s
      rw [Real.norm_eq_abs]
      by_cases hs : s ∈ A
      · have hnot : s ∉ Aᶜ := fun h ↦ h hs
        simp only [Set.indicator_of_mem hs, Set.indicator_of_notMem hnot, sub_zero]
      · have hmem : s ∈ Aᶜ := hs
        simp only [Set.indicator_of_notMem hs, Set.indicator_of_mem hmem, zero_sub, abs_neg]
    have hsum_norm : Summable (fun s : S ↦ ‖A.indicator d s - Aᶜ.indicator d s‖) := by
      rw [hnorm_eq]
      exact hsum_abs
    have htsum_le : |2 * (μ.real A - ν.real A)| ≤ ∑' s : S, |d s| := by
      rw [htwo_mul A, ← Real.norm_eq_abs]
      simpa only [hnorm_eq] using norm_tsum_le_tsum_norm hsum_norm
    have habs_two : |2 * (μ.real A - ν.real A)| = 2 * |μ.real A - ν.real A| := by
      rw [abs_mul, abs_of_nonneg zero_le_two]
    rw [habs_two] at htsum_le
    linarith
  let Apos : Set S := {s : S | 0 ≤ d s}
  have hApos_eq : |μ.real Apos - ν.real Apos| = (1 / 2 : ℝ) * ∑' s : S, |d s| := by
    have hcongr : (fun s : S ↦ Apos.indicator d s - Aposᶜ.indicator d s) = fun s ↦ |d s| := by
      ext s
      by_cases hs : s ∈ Apos
      · have hnot : s ∉ Aposᶜ := fun h ↦ h hs
        simp only [Set.indicator_of_mem hs, Set.indicator_of_notMem hnot, sub_zero]
        exact (abs_of_nonneg hs).symm
      · have hmem : s ∈ Aposᶜ := hs
        have hlt : d s < 0 := lt_of_not_ge hs
        simp only [Set.indicator_of_notMem hs, Set.indicator_of_mem hmem, zero_sub]
        exact (abs_of_neg hlt).symm
    have h2 : 2 * (μ.real Apos - ν.real Apos) = ∑' s : S, |d s| := by
      rw [htwo_mul Apos, hcongr]
    have hsum_nn : 0 ≤ ∑' s : S, |d s| := tsum_nonneg fun s ↦ abs_nonneg (d s)
    have hdiff_nn : 0 ≤ μ.real Apos - ν.real Apos := by linarith
    rw [abs_of_nonneg hdiff_nn]
    linarith
  have hrhs : ENNReal.ofReal ((1 / 2 : ℝ) * ∑' s : S, |d s|) =
      (1 / 2 : ℝ≥0∞) * ∑' s : S, ENNReal.ofReal |d s| := by
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_one, ENNReal.ofReal_ofNat 2]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), hhalf,
      ENNReal.ofReal_tsum_of_nonneg (fun s ↦ abs_nonneg (d s)) hsum_abs]
  rw [tvDist_eq_iSup, ← hrhs]
  apply le_antisymm
  · exact iSup₂_le fun A _ ↦ ENNReal.ofReal_le_ofReal (hle_A A)
  · rw [← hApos_eq]
    exact le_iSup₂_of_le Apos (Set.to_countable Apos).measurableSet le_rfl

/-- Random-variable-level Proposition 1.2(3) (`\label{prop22}`, `SteinIntro.tex:532-537`): for
a.e.-measurable random variables `W` and `Z` valued in a countable measurable-singleton space `S`,
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) =
\frac{1}{2} \sum_{s \in S} |\mathbb{P}(W = s) - \mathbb{P}(Z = s)|$. -/
theorem tvDist_map_eq_half_tsum {Ω Ω' S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → S} {Z : Ω' → S}
    (hW : AEMeasurable W P) (hZ : AEMeasurable Z P') :
    tvDist (P.map W) (P'.map Z) =
      (1 / 2 : ℝ≥0∞) *
        ∑' s : S, ENNReal.ofReal |P.real {ω | W ω = s} - P'.real {ω' | Z ω' = s}| := by
  rw [tvDist_eq_half_tsum (P.map W) (P'.map Z)]
  refine congrArg ((1 / 2 : ℝ≥0∞) * ·) (tsum_congr fun s ↦ ?_)
  have h1 : (P.map W).real {s} = P.real {ω | W ω = s} := by
    rw [map_measureReal_apply_of_aemeasurable hW (measurableSet_singleton s)]
    exact congrArg P.real (Set.ext fun _ ↦ Set.mem_singleton_iff)
  have h2 : (P'.map Z).real {s} = P'.real {ω' | Z ω' = s} := by
    rw [map_measureReal_apply_of_aemeasurable hZ (measurableSet_singleton s)]
    exact congrArg P'.real (Set.ext fun _ ↦ Set.mem_singleton_iff)
  rw [h1, h2]

end SteinMethod
