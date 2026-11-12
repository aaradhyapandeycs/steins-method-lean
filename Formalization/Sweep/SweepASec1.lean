/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Metrics.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF

/-!
# SWEEP-A Section 1 Library Proofs (`Formalization.Sweep.SweepASec1`)

Proves the approved Section 1.1.1 prose claims from `docs/tracks/SWEEP-A.md`
(`SteinIntro.tex:503-522`, `708`):

* `sec1_1_1_metrics_axioms_proof` (`Sec1_1_1_metrics_axioms`): symmetry, triangle inequality,
  and separation (`d μ ν = 0 ↔ μ = ν`) for `kolmogorovDist` and `wassersteinDist` on Borel
  probability measures on `ℝ`, and for `tvDist` on probability measures on any space `α`.
* `sec1_1_1_kolmogorov_cdf_and_weakConv_proof` (`Sec1_1_1_kolmogorov_cdf_and_weakConv`): supremum
  CDF representation of `kolmogorovDist` and `kolmogorovDist (μ n) ν → 0 ⇒` weak convergence
  in `ProbabilityMeasure ℝ`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Extended-Metric Axioms (`Sec1_1_1_metrics_axioms`) -/

private lemma kolmogorovDist_triangle (μ ν ρ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    kolmogorovDist μ ρ ≤ kolmogorovDist μ ν + kolmogorovDist ν ρ := by
  rw [kolmogorovDist_eq_iSup μ ρ]
  refine iSup_le fun x ↦ ?_
  have htri : |μ.real (Iic x) - ρ.real (Iic x)| ≤
      |μ.real (Iic x) - ν.real (Iic x)| + |ν.real (Iic x) - ρ.real (Iic x)| :=
    abs_sub_le (μ.real (Iic x)) (ν.real (Iic x)) (ρ.real (Iic x))
  calc
    ENNReal.ofReal |μ.real (Iic x) - ρ.real (Iic x)|
      ≤ ENNReal.ofReal
          (|μ.real (Iic x) - ν.real (Iic x)| + |ν.real (Iic x) - ρ.real (Iic x)|) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |μ.real (Iic x) - ν.real (Iic x)| +
          ENNReal.ofReal |ν.real (Iic x) - ρ.real (Iic x)| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ kolmogorovDist μ ν + kolmogorovDist ν ρ := by
        rw [kolmogorovDist_eq_iSup μ ν, kolmogorovDist_eq_iSup ν ρ]
        exact add_le_add
          (le_iSup (fun y : ℝ ↦ ENNReal.ofReal |μ.real (Iic y) - ν.real (Iic y)|) x)
          (le_iSup (fun y : ℝ ↦ ENNReal.ofReal |ν.real (Iic y) - ρ.real (Iic y)|) x)

private lemma kolmogorovDist_eq_zero_iff (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    kolmogorovDist μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ ipm_self _ μ⟩
  refine Measure.eq_of_cdf μ ν (StieltjesFunction.ext fun x ↦ ?_)
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  have hle : ENNReal.ofReal |μ.real (Iic x) - ν.real (Iic x)| ≤ 0 := by
    rw [← h0, kolmogorovDist_eq_iSup μ ν]
    exact le_iSup (fun y : ℝ ↦ ENNReal.ofReal |μ.real (Iic y) - ν.real (Iic y)|) x
  have habs : |μ.real (Iic x) - ν.real (Iic x)| ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp (le_antisymm hle zero_le)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp habs)

private lemma tvDist_triangle {α : Type*} [MeasurableSpace α] (μ ν ρ : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  rw [tvDist_eq_iSup μ ρ]
  refine iSup₂_le fun A hA ↦ ?_
  have htri : |μ.real A - ρ.real A| ≤ |μ.real A - ν.real A| + |ν.real A - ρ.real A| :=
    abs_sub_le (μ.real A) (ν.real A) (ρ.real A)
  calc
    ENNReal.ofReal |μ.real A - ρ.real A|
      ≤ ENNReal.ofReal (|μ.real A - ν.real A| + |ν.real A - ρ.real A|) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |μ.real A - ν.real A| + ENNReal.ofReal |ν.real A - ρ.real A| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ tvDist μ ν + tvDist ν ρ := by
        rw [tvDist_eq_iSup μ ν, tvDist_eq_iSup ν ρ]
        exact add_le_add (le_iSup₂_of_le A hA le_rfl) (le_iSup₂_of_le A hA le_rfl)

private lemma tvDist_eq_zero_iff {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h0 ↦ Measure.ext fun A hA ↦ ?_, fun h ↦ h ▸ ipm_self _ μ⟩
  have hle : ENNReal.ofReal |μ.real A - ν.real A| ≤ 0 := by
    rw [← h0, tvDist_eq_iSup μ ν]
    exact le_iSup₂_of_le A hA le_rfl
  have hreal : μ.real A = ν.real A :=
    sub_eq_zero.mp (abs_nonpos_iff.mp (ENNReal.ofReal_eq_zero.mp (le_antisymm hle zero_le)))
  rw [← ofReal_measureReal (measure_ne_top μ A),
    ← ofReal_measureReal (measure_ne_top ν A), hreal]

private lemma lipschitzWith_truncAbs {h : ℝ → ℝ} (hh : LipschitzWith 1 h) (n : ℕ) :
    LipschitzWith 1 (fun x ↦ min (n : ℝ) |h x|) := by
  have habs : LipschitzWith 1 (fun x ↦ |h x|) :=
    LipschitzWith.mk_one fun u v ↦ by
      have hd := hh.dist_le_mul u v
      rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq] at hd
      rw [Real.dist_eq, Real.dist_eq]
      exact (abs_abs_sub_abs_le_abs_sub (h u) (h v)).trans hd
  exact habs.const_min (n : ℝ)

private lemma integrable_of_wassersteinDist_lt_top {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfin : wassersteinDist μ ν < ⊤) {h : ℝ → ℝ} (hh : LipschitzWith 1 h)
    (hμ : Integrable h μ) :
    Integrable h ν := by
  let g : ℕ → ℝ → ℝ := fun n x ↦ min (n : ℝ) |h x|
  have hg_lip : ∀ n : ℕ, LipschitzWith 1 (g n) := lipschitzWith_truncAbs hh
  have hg_nn : ∀ (n : ℕ) (x : ℝ), 0 ≤ g n x := fun n x ↦
    le_min (Nat.cast_nonneg n) (abs_nonneg (h x))
  have hg_bdd : ∀ (n : ℕ) (x : ℝ), g n x ∈ Icc 0 (n : ℝ) := fun n x ↦
    ⟨hg_nn n x, min_le_left _ _⟩
  have hg_int : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ), Integrable (g n) ρ :=
    fun ρ _ n ↦ Integrable.of_mem_Icc 0 (n : ℝ) (hg_lip n).continuous.aemeasurable
      (Eventually.of_forall (hg_bdd n))
  let C : ℝ := (∫ x, |h x| ∂μ) + (wassersteinDist μ ν).toReal
  have hbound : ∀ n : ℕ, ∫ x, g n x ∂ν ≤ C := fun n ↦ by
    have hipm : ENNReal.ofReal |(∫ x, g n x ∂μ) - (∫ x, g n x ∂ν)| ≤
        wassersteinDist μ ν :=
      le_ipm (hg_lip n) (hg_int μ n) (hg_int ν n)
    have hdiff : |(∫ x, g n x ∂μ) - (∫ x, g n x ∂ν)| ≤ (wassersteinDist μ ν).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp hipm
    have hle_μ : ∫ x, g n x ∂μ ≤ ∫ x, |h x| ∂μ :=
      integral_mono (hg_int μ n) hμ.abs fun x ↦ min_le_right (n : ℝ) |h x|
    linarith [(abs_le.mp hdiff).1]
  have hmono : Monotone (fun n : ℕ ↦ fun x : ℝ ↦ ENNReal.ofReal (g n x)) :=
    fun m n hmn x ↦ ENNReal.ofReal_le_ofReal (min_le_min_right |h x| (Nat.cast_le.mpr hmn))
  have hsup : ∀ x : ℝ, (⨆ n : ℕ, ENNReal.ofReal (g n x)) = ENNReal.ofReal |h x| :=
    fun x ↦ by
    refine le_antisymm (iSup_le fun n ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge |h x|
    have heq : g N x = |h x| := min_eq_right hN
    have hEq : ENNReal.ofReal (g N x) = ENNReal.ofReal |h x| := by rw [heq]
    exact hEq ▸ le_iSup (fun n : ℕ ↦ ENNReal.ofReal (g n x)) N
  have hlint : ∫⁻ x, ENNReal.ofReal |h x| ∂ν ≤ ENNReal.ofReal C := by
    simp_rw [← hsup]
    rw [lintegral_iSup (fun n ↦ (hg_lip n).continuous.measurable.ennreal_ofReal) hmono]
    refine iSup_le fun n ↦ ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hg_int ν n) (Eventually.of_forall (hg_nn n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  refine ⟨hh.continuous.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs]
  exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top

private lemma wassersteinDist_triangle (μ ν ρ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    wassersteinDist μ ρ ≤ wassersteinDist μ ν + wassersteinDist ν ρ := by
  by_cases h1 : wassersteinDist μ ν = ⊤
  · simp [h1]
  by_cases h2 : wassersteinDist ν ρ = ⊤
  · simp [h2]
  have hlt1 : wassersteinDist μ ν < ⊤ := lt_top_iff_ne_top.mpr h1
  have hlt2 : wassersteinDist ν ρ < ⊤ := lt_top_iff_ne_top.mpr h2
  refine ipm_le fun h hh hμ hρ ↦ ?_
  have hν : Integrable h ν := integrable_of_wassersteinDist_lt_top hlt1 hh hμ
  have htri : |(∫ x, h x ∂μ) - (∫ x, h x ∂ρ)| ≤
      |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| + |(∫ x, h x ∂ν) - (∫ x, h x ∂ρ)| :=
    abs_sub_le _ _ _
  calc
    ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ρ)|
      ≤ ENNReal.ofReal
          (|(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| + |(∫ x, h x ∂ν) - (∫ x, h x ∂ρ)|) :=
        ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| +
          ENNReal.ofReal |(∫ x, h x ∂ν) - (∫ x, h x ∂ρ)| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ wassersteinDist μ ν + wassersteinDist ν ρ :=
        add_le_add (le_ipm hh hμ hν) (le_ipm hh hν hρ)

private lemma cdf_le_of_wassersteinDist_eq_zero {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h0 : wassersteinDist μ ν = 0) (x : ℝ) :
    ProbabilityTheory.cdf μ x ≤ ProbabilityTheory.cdf ν x := by
  have hstep : ∀ ε : ℝ, 0 < ε →
      ProbabilityTheory.cdf μ x ≤ ProbabilityTheory.cdf ν (x + ε) := by
    intro ε hε
    let r : ℝ → ℝ := fun w ↦ min ε (max 0 (x + ε - w))
    have hr_lip : LipschitzWith 1 r := by
      have hlin : LipschitzWith 1 (fun w : ℝ ↦ x + ε - w) :=
        LipschitzWith.mk_one fun u v ↦ by
          have hsub : (x + ε - u) - (x + ε - v) = -(u - v) := by ring
          rw [Real.dist_eq, Real.dist_eq, hsub, abs_neg]
      exact (hlin.const_max 0).const_min ε
    have hr_mem : ∀ w : ℝ, r w ∈ Icc 0 ε := fun w ↦
      ⟨le_min hε.le (le_max_left 0 _), min_le_left _ _⟩
    have hr_int : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable r ρ := fun ρ _ ↦
      Integrable.of_mem_Icc 0 ε hr_lip.continuous.aemeasurable (Eventually.of_forall hr_mem)
    have heq_int : (∫ w, r w ∂μ) = ∫ w, r w ∂ν := by
      have hle : ENNReal.ofReal |(∫ w, r w ∂μ) - (∫ w, r w ∂ν)| ≤ 0 := by
        rw [← h0]
        exact le_ipm hr_lip (hr_int μ) (hr_int ν)
      exact sub_eq_zero.mp
        (abs_nonpos_iff.mp (ENNReal.ofReal_eq_zero.mp (le_antisymm hle zero_le)))
    have hlow : ∀ w : ℝ, (Iic x).indicator (fun _ ↦ ε) w ≤ r w := fun w ↦ by
      by_cases hw : w ≤ x
      · have hmem : w ∈ Iic x := hw
        rw [indicator_of_mem hmem]
        exact le_min le_rfl (le_trans (by linarith) (le_max_right 0 (x + ε - w)))
      · have hnot : w ∉ Iic x := hw
        rw [indicator_of_notMem hnot]
        exact (hr_mem w).1
    have hhigh : ∀ w : ℝ, r w ≤ (Iic (x + ε)).indicator (fun _ ↦ ε) w := fun w ↦ by
      by_cases hw : w ≤ x + ε
      · have hmem : w ∈ Iic (x + ε) := hw
        rw [indicator_of_mem hmem]
        exact (hr_mem w).2
      · have hnot : w ∉ Iic (x + ε) := hw
        rw [indicator_of_notMem hnot]
        have hlt : x + ε < w := lt_of_not_ge hw
        have hmax : max 0 (x + ε - w) = 0 := max_eq_left (by linarith)
        dsimp only [r]
        rw [hmax, min_eq_right hε.le]
    have h1 : ε * μ.real (Iic x) ≤ ∫ w, r w ∂μ := by
      have hi := integral_mono ((integrable_const ε).indicator measurableSet_Iic) (hr_int μ) hlow
      rwa [integral_indicator_const ε measurableSet_Iic, smul_eq_mul, mul_comm] at hi
    have h2 : (∫ w, r w ∂ν) ≤ ε * ν.real (Iic (x + ε)) := by
      have hi := integral_mono (hr_int ν) ((integrable_const ε).indicator measurableSet_Iic) hhigh
      rwa [integral_indicator_const ε measurableSet_Iic, smul_eq_mul, mul_comm] at hi
    rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
    exact le_of_mul_le_mul_left (by linarith) hε
  have hseq : Tendsto (fun n : ℕ ↦ x + 1 / ((n : ℝ) + 1)) atTop (𝓝[≥] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
    · simpa only [add_zero] using
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact mem_Ici.mpr (le_add_of_nonneg_right (by positivity))
  have htend : Tendsto (fun n : ℕ ↦ ProbabilityTheory.cdf ν (x + 1 / ((n : ℝ) + 1)))
      atTop (𝓝 (ProbabilityTheory.cdf ν x)) :=
    ((ProbabilityTheory.cdf ν).right_continuous x).tendsto.comp hseq
  exact ge_of_tendsto htend (Eventually.of_forall fun n ↦ hstep _ (by positivity))

private lemma wassersteinDist_eq_zero_iff (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinDist μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ ipm_self _ μ⟩
  have hsymm : wassersteinDist ν μ = 0 := by rw [wassersteinDist] at h0 ⊢; rwa [ipm_symm]
  refine Measure.eq_of_cdf μ ν (StieltjesFunction.ext fun x ↦ le_antisymm
    (cdf_le_of_wassersteinDist_eq_zero h0 x) (cdf_le_of_wassersteinDist_eq_zero hsymm x))

/-- Library proof of `Sec1_1_1_metrics_axioms` (`SteinIntro.tex:503-522`). -/
theorem sec1_1_1_metrics_axioms_proof :
    (∀ (μ ν ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
        [IsProbabilityMeasure ρ],
      kolmogorovDist μ ν = kolmogorovDist ν μ ∧
      kolmogorovDist μ ρ ≤ kolmogorovDist μ ν + kolmogorovDist ν ρ ∧
      (kolmogorovDist μ ν = 0 ↔ μ = ν)) ∧
    (∀ (μ ν ρ : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
        [IsProbabilityMeasure ρ],
      wassersteinDist μ ν = wassersteinDist ν μ ∧
      wassersteinDist μ ρ ≤ wassersteinDist μ ν + wassersteinDist ν ρ ∧
      (wassersteinDist μ ν = 0 ↔ μ = ν)) ∧
    (∀ {α : Type*} [MeasurableSpace α] (μ ν ρ : Measure α) [IsProbabilityMeasure μ]
        [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ],
      tvDist μ ν = tvDist ν μ ∧
      tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ ∧
      (tvDist μ ν = 0 ↔ μ = ν)) :=
  ⟨fun μ ν ρ _ _ _ ↦
     ⟨ipm_symm _ μ ν, kolmogorovDist_triangle μ ν ρ, kolmogorovDist_eq_zero_iff μ ν⟩,
   fun μ ν ρ _ _ _ ↦
     ⟨ipm_symm _ μ ν, wassersteinDist_triangle μ ν ρ, wassersteinDist_eq_zero_iff μ ν⟩,
   fun μ ν ρ _ _ _ ↦
     ⟨ipm_symm _ μ ν, tvDist_triangle μ ν ρ, tvDist_eq_zero_iff μ ν⟩⟩

/-! ### Section 2: Kolmogorov CDF Supremum & Weak Convergence (`A2`, `SteinIntro.tex:513-515`) -/

private noncomputable def stepApprox
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  f (t n) +
    ∑ k ∈ Finset.range n, (f (t k) - f (t (k + 1))) * (Iic (t k)).indicator (1 : ℝ → ℝ) x

private lemma abs_stepApprox_sub_clamp_le
    {f : ℝ → ℝ} {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hf : ∀ u v : ℝ, |f u - f v| ≤ K * |u - v|) {t : ℕ → ℝ} (ht_mono : Monotone t)
    (ht_step : ∀ k : ℕ, t (k + 1) - t k ≤ δ) (n : ℕ) (x : ℝ) :
    |stepApprox f t n x - f (max (t 0) (min (t n) x))| ≤ K * δ := by
  induction n with
  | zero =>
    have hclamp : max (t 0) (min (t 0) x) = t 0 := max_eq_left (min_le_left _ _)
    simp only [stepApprox, Finset.range_zero, Finset.sum_empty, add_zero, hclamp, sub_self,
      abs_zero]
    exact mul_nonneg hK hδ
  | succ m ih =>
    by_cases hx : x ≤ t m
    · have hstep_eq : stepApprox f t (m + 1) x = stepApprox f t m x := by
        have hmem : x ∈ Iic (t m) := hx
        simp only [stepApprox, Finset.sum_range_succ]
        rw [indicator_of_mem hmem, Pi.one_apply, mul_one]
        ring
      have hmin : min (t (m + 1)) x = min (t m) x := by
        rw [min_eq_right (hx.trans (ht_mono (Nat.le_succ m))), min_eq_right hx]
      rwa [hstep_eq, hmin]
    · have hgt : t m < x := lt_of_not_ge hx
      have hstep_eq : stepApprox f t (m + 1) x = f (t (m + 1)) := by
        simp only [stepApprox]
        have hsum_zero :
            (∑ k ∈ Finset.range (m + 1),
              (f (t k) - f (t (k + 1))) * (Iic (t k)).indicator (1 : ℝ → ℝ) x) = 0 := by
          refine Finset.sum_eq_zero fun k hk ↦ ?_
          have hkx : x ∉ Iic (t k) := not_le_of_gt
            (lt_of_le_of_lt (ht_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))) hgt)
          rw [indicator_of_notMem hkx, mul_zero]
        rw [hsum_zero, add_zero]
      have ht0_lt : t 0 < x := lt_of_le_of_lt (ht_mono (Nat.zero_le m)) hgt
      have hclamp : max (t 0) (min (t (m + 1)) x) = min (t (m + 1)) x :=
        max_eq_right (le_min (ht_mono (Nat.zero_le _)) ht0_lt.le)
      rw [hstep_eq, hclamp]
      refine (hf (t (m + 1)) (min (t (m + 1)) x)).trans (mul_le_mul_of_nonneg_left ?_ hK)
      have hle1 : min (t (m + 1)) x ≤ t (m + 1) := min_le_left _ _
      have hle2 : t m ≤ min (t (m + 1)) x := le_min (ht_mono (Nat.le_succ m)) hgt.le
      rw [abs_of_nonneg (sub_nonneg.mpr hle1)]
      linarith [ht_step m]

private lemma integral_stepApprox (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f : ℝ → ℝ) (t : ℕ → ℝ) (n : ℕ) :
    ∫ x, stepApprox f t n x ∂ρ =
      f (t n) + ∑ k ∈ Finset.range n, (f (t k) - f (t (k + 1))) * ρ.real (Iic (t k)) := by
  unfold stepApprox
  have hint_term : ∀ k ∈ Finset.range n,
      Integrable
        (fun x ↦ (f (t k) - f (t (k + 1))) * (Iic (t k)).indicator (1 : ℝ → ℝ) x) ρ :=
    fun k _ ↦ ((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul _
  have hint_sum : Integrable
      (fun x ↦ ∑ k ∈ Finset.range n,
        (f (t k) - f (t (k + 1))) * (Iic (t k)).indicator (1 : ℝ → ℝ) x) ρ :=
    integrable_finsetSum _ hint_term
  rw [integral_add (integrable_const _) hint_sum, integral_const, probReal_univ, one_smul,
    integral_finsetSum _ hint_term]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_const_mul, integral_indicator_one measurableSet_Iic]

private lemma abs_integral_clamp_sub_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf_cont : Continuous f) {K M : ℝ} (hK : 0 ≤ K) (hM : 0 < M)
    (hf_lip : ∀ u v : ℝ, |f u - f v| ≤ K * |u - v|)
    (hfin : kolmogorovDist μ ν < ⊤) :
    |(∫ x, f (max (-M) (min M x)) ∂μ) - (∫ x, f (max (-M) (min M x)) ∂ν)| ≤
      2 * K * M * (kolmogorovDist μ ν).toReal := by
  let g : ℝ → ℝ := fun x ↦ f (max (-M) (min M x))
  have hg_cont : Continuous g :=
    hf_cont.comp (continuous_const.max (continuous_const.min continuous_id))
  have hg_bdd : ∀ x : ℝ, |g x| ≤ |f 0| + K * M := fun x ↦ by
    have hmem : max (-M) (min M x) ∈ Icc (-M) M :=
      ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    have hd := hf_lip (max (-M) (min M x)) 0
    have habs : |max (-M) (min M x) - 0| ≤ M := by
      rw [sub_zero, abs_le]
      exact hmem
    linarith [abs_sub_abs_le_abs_sub (g x) (f 0), mul_le_mul_of_nonneg_left habs hK]
  have hg_int : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable g ρ := fun ρ _ ↦
    Integrable.of_bound hg_cont.aestronglyMeasurable (|f 0| + K * M)
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hg_bdd x)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨N0, hN0⟩ := exists_nat_gt (4 * K * M / ε)
  let N : ℕ := N0 + 1
  have hN_pos : 0 < (N : ℝ) := by positivity
  let δ : ℝ := 2 * M / (N : ℝ)
  have hδ_pos : 0 < δ := by positivity
  let t : ℕ → ℝ := fun k ↦ -M + (k : ℝ) * δ
  have ht0 : t 0 = -M := by simp [t]
  have htN : t N = M := by
    dsimp only [t, δ]
    field_simp [hN_pos.ne']
    ring
  have ht_mono : Monotone t := fun a b hab ↦
    add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hδ_pos.le) (-M)
  have ht_step : ∀ k : ℕ, t (k + 1) - t k ≤ δ := fun k ↦ by
    dsimp only [t]
    push_cast
    linarith
  have happrox : ∀ x : ℝ, |stepApprox f t N x - g x| ≤ K * δ := fun x ↦ by
    simpa only [g, ht0, htN] using
      abs_stepApprox_sub_clamp_le hK hδ_pos.le hf_lip ht_mono ht_step N x
  have hs_int : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      Integrable (stepApprox f t N) ρ :=
    fun ρ _ ↦ (integrable_const _).add (integrable_finsetSum _ fun k _ ↦
      ((integrable_const (1 : ℝ)).indicator measurableSet_Iic).const_mul _)
  have hdiff_ρ : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      |(∫ x, g x ∂ρ) - (∫ x, stepApprox f t N x ∂ρ)| ≤ K * δ := fun ρ _ ↦ by
    rw [← integral_sub (hg_int ρ) (hs_int ρ)]
    refine abs_integral_le_integral_abs.trans ?_
    have hsub_int : Integrable (fun x ↦ |g x - stepApprox f t N x|) ρ :=
      ((hg_int ρ).sub (hs_int ρ)).abs
    have hi := integral_mono hsub_int (integrable_const (K * δ)) fun x ↦ by
      rw [abs_sub_comm]
      exact happrox x
    simpa only [integral_const, probReal_univ, one_smul] using hi
  have hstep_diff :
      |(∫ x, stepApprox f t N x ∂μ) - (∫ x, stepApprox f t N x ∂ν)| ≤
        2 * K * M * (kolmogorovDist μ ν).toReal := by
    rw [integral_stepApprox μ f t N, integral_stepApprox ν f t N]
    have hsub :
        (f (t N) + ∑ k ∈ Finset.range N, (f (t k) - f (t (k + 1))) * μ.real (Iic (t k))) -
          (f (t N) + ∑ k ∈ Finset.range N, (f (t k) - f (t (k + 1))) * ν.real (Iic (t k))) =
        ∑ k ∈ Finset.range N,
          (f (t k) - f (t (k + 1))) * (μ.real (Iic (t k)) - ν.real (Iic (t k))) := by
      rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ (mul_sub _ _ _).symm
    rw [hsub]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ Finset.range N,
        |(f (t k) - f (t (k + 1))) * (μ.real (Iic (t k)) - ν.real (Iic (t k)))| ≤
          (K * δ) * (kolmogorovDist μ ν).toReal := fun k _ ↦ by
      rw [abs_mul]
      have hf_k : |f (t k) - f (t (k + 1))| ≤ K * δ := by
        refine (hf_lip (t k) (t (k + 1))).trans (mul_le_mul_of_nonneg_left ?_ hK)
        have hsub_t : t k - t (k + 1) = -δ := by dsimp only [t]; push_cast; ring
        rw [hsub_t, abs_neg, abs_of_pos hδ_pos]
      have hcdf_k : |μ.real (Iic (t k)) - ν.real (Iic (t k))| ≤
          (kolmogorovDist μ ν).toReal := by
        refine (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp ?_
        rw [kolmogorovDist_eq_iSup μ ν]
        exact le_iSup (fun y : ℝ ↦ ENNReal.ofReal |μ.real (Iic y) - ν.real (Iic y)|) (t k)
      exact mul_le_mul hf_k hcdf_k (abs_nonneg _) (mul_nonneg hK hδ_pos.le)
    calc
      (∑ k ∈ Finset.range N,
          |(f (t k) - f (t (k + 1))) * (μ.real (Iic (t k)) - ν.real (Iic (t k)))|)
        ≤ ∑ _k ∈ Finset.range N, (K * δ) * (kolmogorovDist μ ν).toReal :=
          Finset.sum_le_sum hterm
      _ = (N : ℝ) * ((K * δ) * (kolmogorovDist μ ν).toReal) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = 2 * K * M * (kolmogorovDist μ ν).toReal := by
          dsimp only [δ]
          field_simp [hN_pos.ne']
  have h2Kδ : 2 * (K * δ) ≤ ε := by
    dsimp only [δ]
    have hN_gt : 4 * K * M / ε < (N : ℝ) := by
      have : (N0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self N0
      linarith
    have hmul : 4 * K * M < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN_gt
    rw [show 2 * (K * (2 * M / (N : ℝ))) = 4 * K * M / (N : ℝ) by ring, div_le_iff₀ hN_pos]
    linarith
  have htri :
      |(∫ x, g x ∂μ) - (∫ x, g x ∂ν)| ≤
        |(∫ x, g x ∂μ) - (∫ x, stepApprox f t N x ∂μ)| +
          |(∫ x, stepApprox f t N x ∂μ) - (∫ x, stepApprox f t N x ∂ν)| +
          |(∫ x, stepApprox f t N x ∂ν) - (∫ x, g x ∂ν)| := by
    have h1 := abs_sub_le (∫ x, g x ∂μ) (∫ x, stepApprox f t N x ∂μ) (∫ x, g x ∂ν)
    have h2 := abs_sub_le (∫ x, stepApprox f t N x ∂μ)
      (∫ x, stepApprox f t N x ∂ν) (∫ x, g x ∂ν)
    linarith
  have hν_comm :
      |(∫ x, stepApprox f t N x ∂ν) - (∫ x, g x ∂ν)| =
        |(∫ x, g x ∂ν) - (∫ x, stepApprox f t N x ∂ν)| := abs_sub_comm _ _
  linarith [hdiff_ρ μ, hdiff_ρ ν]

private lemma abs_integral_sub_clamp_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {f : ℝ → ℝ} (hf_cont : Continuous f) {B M : ℝ} (hB : 0 ≤ B) (_hM : 0 < M)
    (hf_bdd : ∀ x : ℝ, |f x| ≤ B) :
    |(∫ x, f x ∂ρ) - (∫ x, f (max (-M) (min M x)) ∂ρ)| ≤
      2 * B * (ProbabilityTheory.cdf ρ (-M) + (1 - ProbabilityTheory.cdf ρ M)) := by
  let g : ℝ → ℝ := fun x ↦ f (max (-M) (min M x))
  have hg_cont : Continuous g :=
    hf_cont.comp (continuous_const.max (continuous_const.min continuous_id))
  have hf_int : Integrable f ρ :=
    Integrable.of_bound hf_cont.aestronglyMeasurable B
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hf_bdd x)
  have hg_int : Integrable g ρ :=
    Integrable.of_bound hg_cont.aestronglyMeasurable B
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hf_bdd _)
  let tailSet : Set ℝ := Iic (-M) ∪ Ioi M
  have htail_meas : MeasurableSet tailSet := measurableSet_Iic.union measurableSet_Ioi
  have hpt : ∀ x : ℝ, |f x - g x| ≤ 2 * B * tailSet.indicator (1 : ℝ → ℝ) x :=
    fun x ↦ by
    by_cases hx : x ∈ tailSet
    · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
      linarith [abs_sub (f x) (g x), hf_bdd x, hf_bdd (max (-M) (min M x))]
    · rw [indicator_of_notMem hx, mul_zero]
      have hge : -M < x := not_le.mp fun h ↦ hx (Or.inl h)
      have hle : x ≤ M := not_lt.mp fun h ↦ hx (Or.inr h)
      have hclamp : max (-M) (min M x) = x := by
        rw [min_eq_right hle, max_eq_right hge.le]
      simp only [g, hclamp, sub_self, abs_zero, le_rfl]
  rw [← integral_sub hf_int hg_int]
  refine abs_integral_le_integral_abs.trans ?_
  have hdom : Integrable (fun x ↦ 2 * B * tailSet.indicator (1 : ℝ → ℝ) x) ρ :=
    ((integrable_const (1 : ℝ)).indicator htail_meas).const_mul (2 * B)
  have hsub_int : Integrable (fun x ↦ |f x - g x|) ρ := (hf_int.sub hg_int).abs
  have hi := integral_mono hsub_int hdom hpt
  rw [integral_const_mul, integral_indicator_one htail_meas] at hi
  have hunion : ρ.real tailSet ≤ ρ.real (Iic (-M)) + ρ.real (Ioi M) :=
    measureReal_union_le _ _
  have hIoi : ρ.real (Ioi M) = 1 - ρ.real (Iic M) := by
    have hcompl : Ioi M = (Iic M)ᶜ := compl_Iic.symm
    rw [hcompl, measureReal_compl measurableSet_Iic, probReal_univ]
  rw [hIoi] at hunion
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  exact hi.trans (mul_le_mul_of_nonneg_left hunion (by positivity))

private lemma tendsto_probabilityMeasure_of_kolmogorovDist
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n : ℕ, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (hK : Tendsto (fun n : ℕ ↦ kolmogorovDist (μ n) ν) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (μ n).toProbabilityMeasure) atTop (𝓝 ν.toProbabilityMeasure) := by
  rw [MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  simp only [Measure.coe_toProbabilityMeasure]
  let B : ℝ := |f 0| + max C 0 + 1
  have hB_pos : 0 < B := by positivity
  have hf_bdd : ∀ x : ℝ, |f x| ≤ B := fun x ↦ by
    have hd : |f x - f 0| ≤ C := by simpa [Real.dist_eq] using hC x 0
    have hmax : C ≤ max C 0 := le_max_left C 0
    dsimp only [B]
    linarith [abs_sub_abs_le_abs_sub (f x) (f 0)]
  let K : ℝ := max (L : ℝ) 1
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hf_lip : ∀ u v : ℝ, |f u - f v| ≤ K * |u - v| := fun u v ↦ by
    have hd := hL.dist_le_mul u v
    rw [Real.dist_eq, Real.dist_eq] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  have htoReal : Tendsto (fun n : ℕ ↦ (kolmogorovDist (μ n) ν).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hK
  have hev_lt : ∀ᶠ n : ℕ in atTop, kolmogorovDist (μ n) ν < ⊤ :=
    hK.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htail_tend :
      Tendsto (fun M : ℝ ↦ ProbabilityTheory.cdf ν (-M) + (1 - ProbabilityTheory.cdf ν M))
        atTop (𝓝 0) := by
    have h1 : Tendsto (fun M : ℝ ↦ ProbabilityTheory.cdf ν (-M)) atTop (𝓝 0) :=
      (ProbabilityTheory.tendsto_cdf_atBot ν).comp tendsto_neg_atTop_atBot
    have h2 : Tendsto (fun M : ℝ ↦ 1 - ProbabilityTheory.cdf ν M) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (ProbabilityTheory.tendsto_cdf_atTop ν)
    simpa using h1.add h2
  have hev_M : ∀ᶠ M : ℝ in atTop,
      0 < M ∧ ProbabilityTheory.cdf ν (-M) + (1 - ProbabilityTheory.cdf ν M) < ε / (8 * B) :=
    (eventually_gt_atTop 0).and
      (htail_tend.eventually (Iio_mem_nhds (div_pos hε (by positivity))))
  obtain ⟨M, hM_pos, hM_tail⟩ := hev_M.exists
  let W : ℝ := 4 * B + 2 * K * M
  have hW_pos : 0 < W := by positivity
  have hev_n : ∀ᶠ n : ℕ in atTop,
      kolmogorovDist (μ n) ν < ⊤ ∧ (kolmogorovDist (μ n) ν).toReal < ε / (2 * W) :=
    hev_lt.and (htoReal.eventually (Iio_mem_nhds (div_pos hε (by positivity))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev_n
  refine ⟨N₀, fun n hn ↦ ?_⟩
  obtain ⟨hfin, hsmall⟩ := hN₀ n hn
  rw [Real.dist_eq]
  have h1 := abs_integral_sub_clamp_le (μ n) hL.continuous hB_pos.le hM_pos hf_bdd
  have h2 := abs_integral_clamp_sub_le (μ n) ν hL.continuous hK_pos.le hM_pos hf_lip hfin
  have h3 := abs_integral_sub_clamp_le ν hL.continuous hB_pos.le hM_pos hf_bdd
  have hcdf_diff :
      ProbabilityTheory.cdf (μ n) (-M) + (1 - ProbabilityTheory.cdf (μ n) M) ≤
        ProbabilityTheory.cdf ν (-M) + (1 - ProbabilityTheory.cdf ν M) +
          2 * (kolmogorovDist (μ n) ν).toReal := by
    have hd : ∀ y : ℝ,
        |ProbabilityTheory.cdf (μ n) y - ProbabilityTheory.cdf ν y| ≤
          (kolmogorovDist (μ n) ν).toReal := fun y ↦ by
      rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
      refine (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp ?_
      rw [kolmogorovDist_eq_iSup (μ n) ν]
      exact le_iSup (fun z : ℝ ↦ ENNReal.ofReal |(μ n).real (Iic z) - ν.real (Iic z)|) y
    linarith [(abs_le.mp (hd (-M))).2, (abs_le.mp (hd M)).1]
  have htri :
      |(∫ x, f x ∂μ n) - (∫ x, f x ∂ν)| ≤
        |(∫ x, f x ∂μ n) - (∫ x, f (max (-M) (min M x)) ∂μ n)| +
          |(∫ x, f (max (-M) (min M x)) ∂μ n) - (∫ x, f (max (-M) (min M x)) ∂ν)| +
          |(∫ x, f x ∂ν) - (∫ x, f (max (-M) (min M x)) ∂ν)| := by
    have ha := abs_sub_le (∫ x, f x ∂μ n) (∫ x, f (max (-M) (min M x)) ∂μ n)
      (∫ x, f x ∂ν)
    have hb := abs_sub_le (∫ x, f (max (-M) (min M x)) ∂μ n)
      (∫ x, f (max (-M) (min M x)) ∂ν) (∫ x, f x ∂ν)
    have hc := abs_sub_comm (∫ x, f (max (-M) (min M x)) ∂ν) (∫ x, f x ∂ν)
    linarith
  have hcomb :
      |(∫ x, f x ∂μ n) - (∫ x, f x ∂ν)| ≤
        4 * B * (ProbabilityTheory.cdf ν (-M) + (1 - ProbabilityTheory.cdf ν M)) +
          W * (kolmogorovDist (μ n) ν).toReal := by
    dsimp only [W]
    nlinarith
  have hpart1 :
      4 * B * (ProbabilityTheory.cdf ν (-M) + (1 - ProbabilityTheory.cdf ν M)) < ε / 2 := by
    have hm := mul_lt_mul_of_pos_left hM_tail (by positivity : 0 < 4 * B)
    have hsimpl : 4 * B * (ε / (8 * B)) = ε / 2 := by field_simp [hB_pos.ne']; ring
    rwa [hsimpl] at hm
  have hpart2 : W * (kolmogorovDist (μ n) ν).toReal < ε / 2 := by
    have hm := mul_lt_mul_of_pos_left hsmall hW_pos
    have hsimpl : W * (ε / (2 * W)) = ε / 2 := by field_simp [hW_pos.ne']
    rwa [hsimpl] at hm
  linarith

/-- Library proof of `Sec1_1_1_kolmogorov_cdf_and_weakConv` (`SteinIntro.tex:513-515`, `708`). -/
theorem sec1_1_1_kolmogorov_cdf_and_weakConv_proof :
    (∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      kolmogorovDist μ ν =
        ⨆ x : ℝ, ENNReal.ofReal |ProbabilityTheory.cdf μ x - ProbabilityTheory.cdf ν x|) ∧
    (∀ (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
        [∀ n : ℕ, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν],
      Tendsto (fun n : ℕ ↦ kolmogorovDist (μ n) ν) atTop (𝓝 0) →
      Tendsto (fun n : ℕ ↦ (μ n).toProbabilityMeasure) atTop
        (𝓝 ν.toProbabilityMeasure)) := by
  refine ⟨fun μ ν _ _ ↦ ?_,
    fun μ ν _ _ hK ↦ tendsto_probabilityMeasure_of_kolmogorovDist μ ν hK⟩
  rw [kolmogorovDist_eq_iSup μ ν]
  refine iSup_congr fun x ↦ ?_
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]

end SteinMethod
