/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.PoissonSizeBiasMonotone
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.CDF
import Mathlib.Tactic.Linarith

/-!
# Coordinatewise Monotone Functions and 1D Strassen Theorem
(`Formalization.PoissonSizeBias.Monotone.Basic`)

Formalizes Definition 4.9 (`SteinIntro.tex:2377-2381`) equivalences and non-vacuity witnesses,
together with the one-dimensional Strassen theorem (`SteinIntro.tex:2415-2417`).
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-! ### Part 1: Definition 4.9 Equivalences and Non-Vacuity Witnesses -/

/-- `IsIncreasing` is definitionally equivalent to Mathlib's `Monotone` under the coordinatewise
order on `Fin n → ℝ`. -/
theorem isIncreasing_iff_monotone {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    IsIncreasing f ↔ Monotone f :=
  Iff.rfl

/-- `IsDecreasing` is definitionally equivalent to Mathlib's `Antitone` under the coordinatewise
order on `Fin n → ℝ`. -/
theorem isDecreasing_iff_antitone {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    IsDecreasing f ↔ Antitone f :=
  Iff.rfl

/-- Non-vacuity witness for `IsIncreasing` (`SteinIntro.tex:2377-2381`): for `0 < n`, coordinate
projection `x ↦ x 0` is increasing and not decreasing. -/
theorem exists_isIncreasing_not_isDecreasing {n : ℕ} (hn : 0 < n) :
    ∃ f : (Fin n → ℝ) → ℝ, IsIncreasing f ∧ ¬ IsDecreasing f := by
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨fun x ↦ x i₀, fun x y hxy ↦ hxy i₀, fun hdec ↦ ?_⟩
  have h := hdec (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ zero_le_one)
  linarith

/-- Non-vacuity witness for `IsDecreasing` (`SteinIntro.tex:2377-2381`): for `0 < n`, negated
coordinate projection `x ↦ -x 0` is decreasing and not increasing. -/
theorem exists_isDecreasing_not_isIncreasing {n : ℕ} (hn : 0 < n) :
    ∃ f : (Fin n → ℝ) → ℝ, IsDecreasing f ∧ ¬ IsIncreasing f := by
  let i₀ : Fin n := ⟨0, hn⟩
  refine ⟨fun x ↦ -x i₀, fun x y hxy ↦ neg_le_neg (hxy i₀), fun hinc ↦ ?_⟩
  have h := hinc (fun _ ↦ 0) (fun _ ↦ 1) (fun _ ↦ zero_le_one)
  linarith

/-! ### Part 2: One-Dimensional Strassen Theorem (`SteinIntro.tex:2415-2417`) -/

/-- Generalized inverse (quantile function) of the CDF of `μ`, clamped to `(0, 1)`. -/
noncomputable def cdfQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if 1 ≤ u then 0 else sInf {z : ℝ | u ≤ cdf μ z}

private lemma nonempty_cdf_ge (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu1 : u < 1) :
    ({z : ℝ | u ≤ cdf μ z}).Nonempty := by
  have ht := tendsto_cdf_atTop μ
  have h_ev := (tendsto_order.mp ht).1 u hu1
  rcases Filter.Eventually.exists h_ev with ⟨z, hz⟩
  exact ⟨z, le_of_lt hz⟩

private lemma bddBelow_cdf_ge (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {z : ℝ | u ≤ cdf μ z} := by
  have ht := tendsto_cdf_atBot μ
  have h_ev := (tendsto_order.mp ht).2 u hu0
  rw [Filter.eventually_atBot] at h_ev
  rcases h_ev with ⟨b, hb⟩
  refine ⟨b, fun z hz ↦ ?_⟩
  by_contra hlt
  have h1 := hb z (le_of_lt (not_le.mp hlt))
  linarith [Set.mem_ofPred.mp hz]

private lemma sInf_cdf_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (z : ℝ) :
    sInf {x : ℝ | u ≤ cdf μ x} ≤ z ↔ u ≤ cdf μ z := by
  set S : Set ℝ := {x : ℝ | u ≤ cdf μ x}
  have hne : S.Nonempty := nonempty_cdf_ge μ hu1
  have hbdd : BddBelow S := bddBelow_cdf_ge μ hu0
  constructor
  · intro hle
    have h_mem : u ≤ cdf μ (sInf S) := by
      have h_rc : Filter.Tendsto (cdf μ) (nhdsWithin (sInf S) (Set.Ioi (sInf S)))
          (nhds (cdf μ (sInf S))) :=
        tendsto_nhdsWithin_mono_left Set.Ioi_subset_Ici_self ((cdf μ).right_continuous (sInf S))
      have h_ev : ∀ᶠ x in nhdsWithin (sInf S) (Set.Ioi (sInf S)), u ≤ cdf μ x := by
        rw [eventually_nhdsWithin_iff]
        refine Filter.Eventually.of_forall fun x hx ↦ ?_
        obtain ⟨y, hyS, hyx⟩ := exists_lt_of_csInf_lt hne (Set.mem_Ioi.mp hx)
        exact le_trans (Set.mem_ofPred.mp hyS) ((cdf μ).mono (le_of_lt hyx))
      exact ge_of_tendsto h_rc h_ev
    exact le_trans h_mem ((cdf μ).mono hle)
  · intro hz
    exact csInf_le hbdd hz

private lemma preimage_cdfQuantile_Iic_inter_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (z : ℝ) :
    cdfQuantile μ ⁻¹' Set.Iic z ∩ Set.Ioo 0 1 =
      if cdf μ z < 1 then Set.Ioc 0 (cdf μ z) else Set.Ioo 0 1 := by
  by_cases hlt : cdf μ z < 1
  · simp only [hlt, ↓reduceIte]
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo, Set.mem_Ioc]
    constructor
    · rintro ⟨hq, hu0, hu1⟩
      have h1 : ¬ u ≤ 0 := not_le_of_gt hu0
      have h2 : ¬ 1 ≤ u := not_le_of_gt hu1
      unfold cdfQuantile at hq
      simp only [h1, h2, ↓reduceIte] at hq
      rw [sInf_cdf_le_iff μ hu0 hu1 z] at hq
      exact ⟨hu0, hq⟩
    · rintro ⟨hu0, hle⟩
      have hu1 : u < 1 := lt_of_le_of_lt hle hlt
      have h1 : ¬ u ≤ 0 := not_le_of_gt hu0
      have h2 : ¬ 1 ≤ u := not_le_of_gt hu1
      refine ⟨?_, hu0, hu1⟩
      unfold cdfQuantile
      simp only [h1, h2, ↓reduceIte]
      rwa [sInf_cdf_le_iff μ hu0 hu1 z]
  · simp only [hlt, ↓reduceIte]
    have hcdf1 : cdf μ z = 1 := le_antisymm (cdf_le_one μ z) (not_lt.mp hlt)
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨_, hu0, hu1⟩
      exact ⟨hu0, hu1⟩
    · rintro ⟨hu0, hu1⟩
      have h1 : ¬ u ≤ 0 := not_le_of_gt hu0
      have h2 : ¬ 1 ≤ u := not_le_of_gt hu1
      refine ⟨?_, hu0, hu1⟩
      unfold cdfQuantile
      simp only [h1, h2, ↓reduceIte]
      rw [sInf_cdf_le_iff μ hu0 hu1 z, hcdf1]
      exact le_of_lt hu1

private lemma measurable_cdfQuantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (cdfQuantile μ) := by
  refine measurable_of_Iic fun z ↦ ?_
  have h_split : cdfQuantile μ ⁻¹' Set.Iic z =
      (cdfQuantile μ ⁻¹' Set.Iic z ∩ Set.Ioo 0 1) ∪
      (cdfQuantile μ ⁻¹' Set.Iic z ∩ (Set.Ioo 0 1)ᶜ) :=
    (Set.inter_union_compl _ _).symm
  have h_compl : cdfQuantile μ ⁻¹' Set.Iic z ∩ (Set.Ioo 0 1)ᶜ =
      if 0 ≤ z then (Set.Ioo 0 1)ᶜ else ∅ := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_compl_iff, Set.mem_Ioo]
    by_cases hu : 0 < u ∧ u < 1
    · split_ifs <;> simp [hu]
    · have hq0 : cdfQuantile μ u = 0 := by
        unfold cdfQuantile
        by_cases h1 : u ≤ 0
        · simp [h1]
        · have h2 : 1 ≤ u := le_of_not_gt fun hlt ↦ hu ⟨not_le.mp h1, hlt⟩
          simp [h1, h2]
      by_cases hz : 0 ≤ z <;> simp [hu, hq0, hz]
  rw [h_split, preimage_cdfQuantile_Iic_inter_Ioo, h_compl]
  refine MeasurableSet.union ?_ ?_
  · split_ifs
    · exact measurableSet_Ioc
    · exact measurableSet_Ioo
  · split_ifs
    · exact measurableSet_Ioo.compl
    · exact MeasurableSet.empty

private noncomputable def unitIooMeasure : Measure ℝ :=
  volume.restrict (Set.Ioo 0 1)

private instance instIsProbabilityMeasureUnitIooMeasure :
    IsProbabilityMeasure unitIooMeasure where
  measure_univ := by
    unfold unitIooMeasure
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]

lemma isProbabilityMeasure_map' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (μ.map f) :=
  ⟨by rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ,
    Set.preimage_univ, measure_univ]⟩

private lemma map_cdfQuantile_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    unitIooMeasure.map (cdfQuantile μ) = μ := by
  have hq_meas : Measurable (cdfQuantile μ) := measurable_cdfQuantile μ
  have : IsProbabilityMeasure (unitIooMeasure.map (cdfQuantile μ)) :=
    isProbabilityMeasure_map' hq_meas.aemeasurable
  refine Measure.eq_of_cdf _ _ ?_
  ext z
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hq_meas measurableSet_Iic]
  unfold unitIooMeasure
  rw [measureReal_restrict_apply (hq_meas measurableSet_Iic),
    preimage_cdfQuantile_Iic_inter_Ioo]
  by_cases hlt : cdf μ z < 1
  · simp only [hlt, ↓reduceIte]
    rw [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (cdf_nonneg μ z),
      cdf_eq_real]
  · simp only [hlt, ↓reduceIte]
    have hcdf1 : cdf μ z = 1 := le_antisymm (cdf_le_one μ z) (not_lt.mp hlt)
    rw [← cdf_eq_real, hcdf1, Measure.real, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one]

/-- One-dimensional Strassen theorem (`SteinIntro.tex:2415-2417`): if
$\mu(z, \infty) \le \nu(z, \infty)$ for all $z \in \mathbb{R}$, then there exists a coupling
$(X, Y)$ of $\mu$ and $\nu$ with $X \le Y$ pointwise. -/
theorem strassen_1d
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_dom : ∀ z : ℝ, μ.real (Set.Ioi z) ≤ ν.real (Set.Ioi z)) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (X Y : Ω → ℝ),
      @IsProbabilityMeasure Ω mΩ P ∧
      @Measurable Ω ℝ mΩ _ X ∧ @Measurable Ω ℝ mΩ _ Y ∧
      @Measure.map Ω ℝ mΩ _ X P = μ ∧
      @Measure.map Ω ℝ mΩ _ Y P = ν ∧
      ∀ ω : Ω, X ω ≤ Y ω := by
  refine ⟨ℝ, inferInstance, unitIooMeasure, cdfQuantile μ, cdfQuantile ν,
    inferInstance, measurable_cdfQuantile μ, measurable_cdfQuantile ν,
    map_cdfQuantile_eq μ, map_cdfQuantile_eq ν, fun u ↦ ?_⟩
  unfold cdfQuantile
  split_ifs with h1 h2
  · exact le_rfl
  · exact le_rfl
  · have hu0 : 0 < u := not_le.mp h1
    have hu1 : u < 1 := not_le.mp h2
    refine le_csInf (nonempty_cdf_ge ν hu1) fun z hz ↦ ?_
    rw [sInf_cdf_le_iff μ hu0 hu1 z]
    have h_cdf : cdf ν z ≤ cdf μ z := by
      rw [cdf_eq_real, cdf_eq_real]
      have hμ_compl : μ.real (Set.Ioi z) = 1 - μ.real (Set.Iic z) := by
        have hc : (Set.Iic z)ᶜ = Set.Ioi z := Set.compl_Iic
        rw [← hc, probReal_compl_eq_one_sub measurableSet_Iic]
      have hν_compl : ν.real (Set.Ioi z) = 1 - ν.real (Set.Iic z) := by
        have hc : (Set.Iic z)ᶜ = Set.Ioi z := Set.compl_Iic
        rw [← hc, probReal_compl_eq_one_sub measurableSet_Iic]
      linarith [h_dom z]
    exact le_trans (Set.mem_ofPred.mp hz) h_cdf


/-- One-dimensional Strassen theorem (`SteinIntro.tex:2415-2417`, cited in the proof of Lemma 4.18
from `[lig05]` and proved from scratch): for real-valued random variables $X$ and $Y$, there exists
a coupling $(\hat{X}, \hat{Y})$ with $\mathcal{L}(\hat{X}) = \mathcal{L}(X)$,
$\mathcal{L}(\hat{Y}) = \mathcal{L}(Y)$, and $\hat{Y} \le \hat{X}$ almost surely if and only if
$F_X(z) \le F_Y(z)$ ($\mathbb{P}(X \le z) \le \mathbb{P}(Y \le z)$) for all $z \in \mathbb{R}$. -/
theorem lem4_18_strassen_1d_iff
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P') :
    ((∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
        (Xh Yh : Ωc → ℝ),
        Measurable Xh ∧ Measurable Yh ∧
        Pc.map Xh = P.map X ∧ Pc.map Yh = P'.map Y ∧
        ∀ᵐ ωc ∂Pc, Yh ωc ≤ Xh ωc) ↔
      ∀ z : ℝ, P.real {ω | X ω ≤ z} ≤ P'.real {ω' | Y ω' ≤ z}) := by
  constructor
  · rintro ⟨Ωc, mΩc, Pc, hPc, Xh, Yh, hXh, hYh, hmapX, hmapY, hle⟩ z
    have hX_eq : P.real {ω | X ω ≤ z} = Pc.real {ωc | Xh ωc ≤ z} := by
      change P.real (X ⁻¹' Set.Iic z) = Pc.real (Xh ⁻¹' Set.Iic z)
      rw [← map_measureReal_apply_of_aemeasurable hX measurableSet_Iic, ← hmapX,
        map_measureReal_apply hXh measurableSet_Iic]
    have hY_eq : P'.real {ω' | Y ω' ≤ z} = Pc.real {ωc | Yh ωc ≤ z} := by
      change P'.real (Y ⁻¹' Set.Iic z) = Pc.real (Yh ⁻¹' Set.Iic z)
      rw [← map_measureReal_apply_of_aemeasurable hY measurableSet_Iic, ← hmapY,
        map_measureReal_apply hYh measurableSet_Iic]
    rw [hX_eq, hY_eq]
    unfold Measure.real
    refine ENNReal.toReal_mono (measure_ne_top Pc _) (measure_mono_ae ?_)
    filter_upwards [hle] with ωc hωc hXz
    exact le_trans hωc hXz
  · intro h_cdf
    have : IsProbabilityMeasure (P.map X) := isProbabilityMeasure_map' hX
    have : IsProbabilityMeasure (P'.map Y) := isProbabilityMeasure_map' hY
    have h_dom : ∀ z : ℝ, (P'.map Y).real (Set.Ioi z) ≤ (P.map X).real (Set.Ioi z) := by
      intro z
      have hc : (Set.Iic z)ᶜ = Set.Ioi z := Set.compl_Iic
      rw [← hc, probReal_compl_eq_one_sub measurableSet_Iic,
        probReal_compl_eq_one_sub measurableSet_Iic,
        map_measureReal_apply_of_aemeasurable hY measurableSet_Iic,
        map_measureReal_apply_of_aemeasurable hX measurableSet_Iic]
      exact sub_le_sub_left (h_cdf z) 1
    obtain ⟨Ωc, mΩc, Pc, Yh, Xh, hPc, hYh, hXh, hmapY, hmapX, hle⟩ :=
      strassen_1d (P'.map Y) (P.map X) h_dom
    exact ⟨Ωc, mΩc, Pc, hPc, Xh, Yh, hXh, hYh, hmapX, hmapY,
      Filter.Eventually.of_forall hle⟩


end SteinMethod
