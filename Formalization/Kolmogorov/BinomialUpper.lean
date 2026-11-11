/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Kolmogorov.ZeroBiasBound
import Formalization.Normal.IndependentSums
import Formalization.Normal.WassersteinBound
import Formalization.ZeroBias.Basic
import Formalization.ZeroBias.Coupling
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

/-!
# Standardized Binomial Upper Bounds in Wasserstein and Kolmogorov Metrics

Proves the $O(n^{-1/2})$ upper bounds for standardized $\mathrm{Bin}(n, p)$ random variables
supporting `Sec3_6_binomial_order` (`SteinIntro.tex:1655-1657`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `bernoulli_scaled_props` and `bernoulli_stdSum_props`: shared moment, $L^p$, and independence
  properties of centered and scaled Bernoulli summands.
* `binomial_wassersteinDist_le`: upper bound
  $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le C_{\mathrm{W}}\, n^{-1/2}$ via Theorem 3.1
  and Theorem 3.2 (`indepSum_iSup_normalWassersteinClass_le`).
* `binomial_kolmogorovDist_le`: upper bound
  $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le C_{\mathrm{K}}\, n^{-1/2}$ via Proposition
  3.19 (`zeroBias_law_characterization`), boundedness inheritance
  (`ae_abs_le_of_isZeroBias_of_ae_abs_le`), Proposition 3.21 (`zeroBias_sum_of_iIndepFun`), and
  Theorem 3.27 (`kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Bernoulli Summand and Measure-Preserving Independence Helpers -/

lemma rpow_neg_half_eq_one_div_sqrt (n : ℕ) :
    (n : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt n := by
  have hneg : -(1 : ℝ) / 2 = -(1 / 2 : ℝ) := by ring
  rw [hneg, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]

lemma memLp_of_ae_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (M : ℝ) (hf : Measurable f)
    (hbdd : ∀ᵐ x ∂μ, |f x| ≤ M) (q : ℝ≥0∞) : MemLp f q μ := by
  have hnorm : ∀ᵐ x ∂μ, ‖f x‖ ≤ M := by
    filter_upwards [hbdd] with x hx
    rwa [Real.norm_eq_abs]
  exact memLp_iff.mpr
    ((eLpNorm_mono_ae_real hf.aestronglyMeasurable hnorm).trans_lt
      (memLp_const M).eLpNorm_lt_top)

private lemma indepFun_comp_measurePreserving
    {α α' β β' : Type*} [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β'] {μ : Measure α} {ν : Measure α'}
    {π : α → α'} {f : α' → β} {g : α' → β'}
    (hf : Measurable f) (hg : Measurable g)
    (hind : ProbabilityTheory.IndepFun f g ν) (hmp : MeasurePreserving π μ ν) :
    ProbabilityTheory.IndepFun (f ∘ π) (g ∘ π) μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro s t hs ht
  have hpre_inter :
      (f ∘ π) ⁻¹' s ∩ (g ∘ π) ⁻¹' t = π ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) := rfl
  have hpre_s : (f ∘ π) ⁻¹' s = π ⁻¹' (f ⁻¹' s) := rfl
  have hpre_t : (g ∘ π) ⁻¹' t = π ⁻¹' (g ⁻¹' t) := rfl
  rw [hpre_inter, hpre_s, hpre_t,
    hmp.measure_preimage ((hf hs).inter (hg ht)).nullMeasurableSet,
    hmp.measure_preimage (hf hs).nullMeasurableSet,
    hmp.measure_preimage (hg ht).nullMeasurableSet]
  exact hind s t hs ht

private lemma iIndepFun_comp_measurePreserving
    {α α' ι : Type*} {β : ι → Type*} [MeasurableSpace α] [MeasurableSpace α']
    [∀ i, MeasurableSpace (β i)] {μ : Measure α} {ν : Measure α'}
    {π : α → α'} {f : ∀ i, α' → β i}
    (hf : ∀ i, Measurable (f i))
    (hind : ProbabilityTheory.iIndepFun f ν) (hmp : MeasurePreserving π μ ν) :
    ProbabilityTheory.iIndepFun (fun i ↦ f i ∘ π) μ := by
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro S sets hsets
  have hpre :
      (⋂ i ∈ S, (f i ∘ π) ⁻¹' sets i) = π ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext x; simp
  have hmeas_inter : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi ↦ hf i (hsets i hi)
  rw [hpre, hmp.measure_preimage hmeas_inter.nullMeasurableSet, hind S hsets]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hpre_i : (f i ∘ π) ⁻¹' sets i = π ⁻¹' (f i ⁻¹' sets i) := rfl
  rw [hpre_i, hmp.measure_preimage (hf i (hsets i hi)).nullMeasurableSet]

private lemma bernoulli_integral_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B : Ω → ℝ} {p : ℝ} (hB_meas : Measurable B)
    (hB_01 : ∀ᵐ ω ∂P, B ω = 0 ∨ B ω = 1) (hB_prob : P.real (B ⁻¹' {1}) = p) :
    ∫ ω, B ω ∂P = p := by
  have hm1 : MeasurableSet (B ⁻¹' {(1 : ℝ)}) := hB_meas (measurableSet_singleton 1)
  have hae : B =ᵐ[P] (B ⁻¹' {1}).indicator (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hB_01] with ω hω
    rcases hω with h0 | h1
    · simp [Set.indicator, h0]
    · simp [Set.indicator, h1]
  rw [integral_congr_ae hae, integral_indicator_const (1 : ℝ) hm1, smul_eq_mul, mul_one, hB_prob]

private lemma bernoulli_probReal_preimage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B : Ω → ℝ} {p : ℝ} (hB_meas : Measurable B)
    (hB_01 : ∀ᵐ ω ∂P, B ω = 0 ∨ B ω = 1) (hB_prob : P.real (B ⁻¹' {1}) = p)
    {s : Set ℝ} (hs : MeasurableSet s) :
    P.real (B ⁻¹' s) =
      s.indicator (fun _ ↦ (1 : ℝ)) 0 * (1 - p) + s.indicator (fun _ ↦ (1 : ℝ)) 1 * p := by
  let c₀ : ℝ := s.indicator (fun _ ↦ (1 : ℝ)) 0
  let c₁ : ℝ := s.indicator (fun _ ↦ (1 : ℝ)) 1
  have hm_s : MeasurableSet (B ⁻¹' s) := hB_meas hs
  have hm1 : MeasurableSet (B ⁻¹' {(1 : ℝ)}) := hB_meas (measurableSet_singleton 1)
  have hae : (B ⁻¹' s).indicator (fun _ ↦ (1 : ℝ)) =ᵐ[P]
      fun ω ↦ c₀ + (c₁ - c₀) * (B ⁻¹' {1}).indicator (fun _ ↦ (1 : ℝ)) ω := by
    filter_upwards [hB_01] with ω hω
    have hpre : (B ⁻¹' s).indicator (fun _ ↦ (1 : ℝ)) ω =
        s.indicator (fun _ ↦ (1 : ℝ)) (B ω) := by
      by_cases hmem : B ω ∈ s
      · rw [indicator_of_mem hmem, indicator_of_mem (show ω ∈ B ⁻¹' s from hmem)]
      · rw [indicator_of_notMem hmem, indicator_of_notMem (show ω ∉ B ⁻¹' s from hmem)]
    rw [hpre]
    rcases hω with h0 | h1
    · have hnot1 : ω ∉ B ⁻¹' {(1 : ℝ)} := by simp [h0]
      rw [h0, indicator_of_notMem hnot1, mul_zero, add_zero]
    · have hmem1 : ω ∈ B ⁻¹' {(1 : ℝ)} := by simp [h1]
      rw [h1, indicator_of_mem hmem1, mul_one, add_sub_cancel]
  have hint1 : Integrable ((B ⁻¹' {1}).indicator (fun _ ↦ (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hm1
  have hint := integral_congr_ae hae
  rw [integral_indicator_const (1 : ℝ) hm_s, smul_eq_mul, mul_one,
    integral_add (integrable_const c₀) (hint1.const_mul (c₁ - c₀)),
    integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul,
    integral_indicator_const (1 : ℝ) hm1, smul_eq_mul, mul_one, hB_prob] at hint
  rw [hint]
  dsimp [c₀, c₁]
  ring

private lemma bernoulli_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B₁ B₂ : Ω → ℝ} {p : ℝ} (hm₁ : Measurable B₁) (hm₂ : Measurable B₂)
    (h01₁ : ∀ᵐ ω ∂P, B₁ ω = 0 ∨ B₁ ω = 1)
    (h01₂ : ∀ᵐ ω ∂P, B₂ ω = 0 ∨ B₂ ω = 1)
    (hp₁ : P.real (B₁ ⁻¹' {1}) = p) (hp₂ : P.real (B₂ ⁻¹' {1}) = p) :
    ProbabilityTheory.IdentDistrib B₁ B₂ P P := by
  refine ⟨hm₁.aemeasurable, hm₂.aemeasurable, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply hm₁ hs, Measure.map_apply hm₂ hs,
    ← ENNReal.ofReal_toReal (measure_ne_top P (B₁ ⁻¹' s)),
    ← ENNReal.ofReal_toReal (measure_ne_top P (B₂ ⁻¹' s)),
    ← measureReal_def, ← measureReal_def,
    bernoulli_probReal_preimage P hm₁ h01₁ hp₁ hs,
    bernoulli_probReal_preimage P hm₂ h01₂ hp₂ hs]

lemma bernoulli_scaled_props
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B : Ω → ℝ} {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha : 0 < a)
    (hB_meas : Measurable B) (hB_01 : ∀ᵐ ω ∂P, B ω = 0 ∨ B ω = 1)
    (hB_prob : P.real (B ⁻¹' {1}) = p) :
    let Z : Ω → ℝ := fun ω ↦ (B ω - p) / a
    Measurable Z ∧
      (∀ᵐ ω ∂P, |Z ω| ≤ 1 / a) ∧
      (∀ q : ℝ≥0∞, MemLp Z q P) ∧
      (∫ ω, Z ω ∂P = 0) ∧
      (∫ ω, Z ω ^ 2 ∂P = p * (1 - p) / a ^ 2) ∧
      (ProbabilityTheory.variance Z P = p * (1 - p) / a ^ 2) := by
  intro Z
  have hZ_meas : Measurable Z := (hB_meas.sub_const p).div_const a
  have hZ_bdd : ∀ᵐ ω ∂P, |Z ω| ≤ 1 / a := by
    filter_upwards [hB_01] with ω hω
    dsimp [Z]
    rw [abs_div, abs_of_pos ha]
    have hnum : |B ω - p| ≤ 1 := by
      rcases hω with h0 | h1
      · rw [h0, zero_sub, abs_neg, abs_of_pos hp0]; linarith
      · rw [h1, abs_of_pos (by linarith)]; linarith
    exact div_le_div_of_nonneg_right hnum ha.le
  have hZ_Lp : ∀ q : ℝ≥0∞, MemLp Z q P :=
    fun q ↦ memLp_of_ae_abs_le (1 / a) hZ_meas hZ_bdd q
  have hB_int : Integrable B P := by
    refine memLp_one_iff_integrable.mp (memLp_of_ae_abs_le 1 hB_meas ?_ 1)
    filter_upwards [hB_01] with ω hω
    rcases hω with h0 | h1
    · simp [h0]
    · simp [h1]
  have hZ_mean : ∫ ω, Z ω ∂P = 0 := by
    dsimp [Z]
    rw [integral_div, integral_sub hB_int (integrable_const p),
      bernoulli_integral_eq P hB_meas hB_01 hB_prob, integral_const, probReal_univ, smul_eq_mul,
      one_mul, sub_self, zero_div]
  have hZ_sq : ∫ ω, Z ω ^ 2 ∂P = p * (1 - p) / a ^ 2 := by
    have hae_sq : (fun ω ↦ (B ω - p) ^ 2) =ᵐ[P] fun ω ↦ B ω * (1 - 2 * p) + p ^ 2 := by
      filter_upwards [hB_01] with ω hω
      rcases hω with h0 | h1
      · rw [h0]; ring
      · rw [h1]; ring
    have hnum_sq : ∫ ω, (B ω - p) ^ 2 ∂P = p * (1 - p) := by
      rw [integral_congr_ae hae_sq,
        integral_add (hB_int.mul_const (1 - 2 * p)) (integrable_const (p ^ 2)),
        integral_mul_const, bernoulli_integral_eq P hB_meas hB_01 hB_prob, integral_const,
        probReal_univ, smul_eq_mul, one_mul]
      ring
    have hrew : (fun ω ↦ Z ω ^ 2) = fun ω ↦ (B ω - p) ^ 2 / a ^ 2 := by
      ext ω; dsimp [Z]; rw [div_pow]
    rw [hrew, integral_div, hnum_sq]
  have hZ_var : ProbabilityTheory.variance Z P = p * (1 - p) / a ^ 2 := by
    rw [ProbabilityTheory.variance_of_integral_eq_zero hZ_meas.aemeasurable hZ_mean, hZ_sq]
  exact ⟨hZ_meas, hZ_bdd, hZ_Lp, hZ_mean, hZ_sq, hZ_var⟩

lemma bernoulli_stdSum_props
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {n : ℕ} (hn : 1 ≤ n)
    {X : Fin n → Ω → ℝ} (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (hX_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hX_prob : ∀ i : Fin n, P.real (X i ⁻¹' {1}) = p) :
    let s : ℝ := Real.sqrt ((n : ℝ) * p * (1 - p))
    let U : Fin n → Ω → ℝ := fun i ω ↦ (X i ω - p) / s
    let W : Ω → ℝ := fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / s
    0 < s ∧
      s = Real.sqrt n * Real.sqrt (p * (1 - p)) ∧
      W = (fun ω ↦ ∑ i : Fin n, U i ω) ∧
      Measurable W ∧
      (∀ i : Fin n, Measurable (U i)) ∧
      (∀ i : Fin n, ∀ᵐ ω ∂P, |U i ω| ≤ 1 / s) ∧
      (∀ i : Fin n, MemLp (U i) 2 P) ∧
      (∀ i : Fin n, ∫ ω, U i ω ∂P = 0) ∧
      (∀ i : Fin n, ProbabilityTheory.variance (U i) P = 1 / (n : ℝ)) ∧
      ProbabilityTheory.iIndepFun U P ∧
      MemLp W 2 P ∧
      ∫ ω, W ω ^ 2 ∂P = 1 := by
  intro s U W
  have hp_sub : 0 < 1 - p := sub_pos.mpr hp1
  have hpq : 0 < p * (1 - p) := mul_pos hp0 hp_sub
  have hn0 : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hs_eq : s = Real.sqrt n * Real.sqrt (p * (1 - p)) := by
    dsimp [s]; rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg n)]
  have hs_pos : 0 < s := by rw [hs_eq]; positivity
  have hs_sq : s ^ 2 = (n : ℝ) * (p * (1 - p)) := by
    dsimp [s]; rw [mul_assoc, Real.sq_sqrt (by positivity)]
  have hU_pr := fun i : Fin n ↦
    bernoulli_scaled_props P hp0 hp1 hs_pos (hX_meas i) (hX_01 i) (hX_prob i)
  have hU_meas : ∀ i : Fin n, Measurable (U i) := fun i ↦ (hU_pr i).1
  have hU_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |U i ω| ≤ 1 / s := fun i ↦ (hU_pr i).2.1
  have hU_L2 : ∀ i : Fin n, MemLp (U i) 2 P := fun i ↦ (hU_pr i).2.2.1 2
  have hU_mean : ∀ i : Fin n, ∫ ω, U i ω ∂P = 0 := fun i ↦ (hU_pr i).2.2.2.1
  have hU_var : ∀ i : Fin n, ProbabilityTheory.variance (U i) P = 1 / (n : ℝ) := fun i ↦ by
    rw [(hU_pr i).2.2.2.2.2, hs_sq]
    field_simp [hn_pos.ne', hp0.ne', hp_sub.ne']
  have hU_indep : ProbabilityTheory.iIndepFun U P :=
    hX_indep.comp (fun _ x ↦ (x - p) / s) (fun _ ↦ (measurable_id.sub_const p).div_const s)
  have hW_sum : W = fun ω ↦ ∑ i : Fin n, U i ω := by
    ext ω; dsimp [W, U]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hW_meas : Measurable W := by
    rw [hW_sum]; exact Finset.measurable_fun_sum _ fun i _ ↦ hU_meas i
  have hW_L2 : MemLp W 2 P := by
    rw [hW_sum]; exact memLp_finsetSum Finset.univ fun i _ ↦ hU_L2 i
  have hW_mean : ∫ ω, W ω ∂P = 0 := by
    rw [hW_sum, integral_finsetSum Finset.univ fun i _ ↦ (hU_L2 i).integrable one_le_two]
    simp [hU_mean]
  have hW_sq : ∫ ω, W ω ^ 2 ∂P = 1 := by
    have hvar : ProbabilityTheory.variance W P = 1 := by
      have hW_fn : W = ∑ i ∈ Finset.univ, U i := by ext ω; simp [hW_sum]
      rw [hW_fn, IndepFun.variance_sum (fun i _ ↦ hU_L2 i)
        (fun i _ j _ hij ↦ hU_indep.indepFun hij)]
      simp_rw [hU_var]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one_div_cancel hn_pos.ne']
    rwa [ProbabilityTheory.variance_of_integral_eq_zero hW_meas.aemeasurable hW_mean] at hvar
  exact ⟨hs_pos, hs_eq, hW_sum, hW_meas, hU_meas, hU_bdd, hU_L2, hU_mean, hU_var, hU_indep,
    hW_L2, hW_sq⟩

lemma sum_bernoulli_eq_card_filter {n : ℕ} {x : Fin n → ℝ}
    (hx : ∀ i : Fin n, x i = 0 ∨ x i = 1) :
    ∑ i : Fin n, x i = ((Finset.univ.filter (fun i : Fin n ↦ x i = 1)).card : ℝ) := by
  have hterm : ∀ i : Fin n, x i = if x i = 1 then (1 : ℝ) else 0 := fun i ↦ by
    rcases hx i with h0 | h1
    · simp [h0]
    · simp [h1]
  calc ∑ i : Fin n, x i
      = ∑ i : Fin n, (if x i = 1 then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = ((Finset.univ.filter (fun i : Fin n ↦ x i = 1)).card : ℝ) := by simp

/-! ### Section 2: Wasserstein Upper Bound (`binomial_wassersteinDist_le`) -/

/-- Quantitative Wasserstein-1 upper bound of order $n^{-1/2}$ for standardized $\mathrm{Bin}(n,p)$
(`SteinIntro.tex:1655-1657`, via Theorem 3.1 and Theorem 3.2). -/
theorem binomial_wassersteinDist_le
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hn : 1 ≤ n) (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (hX_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hX_prob : ∀ i : Fin n, P.real (X i ⁻¹' {1}) = p)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let σ₀ : ℝ := Real.sqrt (p * (1 - p))
    let W : Ω → ℝ :=
      fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        ((1 / σ₀ ^ 3 + Real.sqrt 2 / (Real.sqrt Real.pi * σ₀ ^ 2)) *
          (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  intro σ₀ W
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr hpq
  have hσ₀_sq : σ₀ ^ 2 = p * (1 - p) := Real.sq_sqrt hpq.le
  have hn0 : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  let Y : Fin n → Ω → ℝ := fun i ω ↦ (X i ω - p) / σ₀
  have hY_pr := fun i : Fin n ↦
    bernoulli_scaled_props P hp0 hp1 hσ₀_pos (hX_meas i) (hX_01 i) (hX_prob i)
  have hY_meas : ∀ i : Fin n, Measurable (Y i) := fun i ↦ (hY_pr i).1
  have hY_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |Y i ω| ≤ 1 / σ₀ := fun i ↦ (hY_pr i).2.1
  have hY4 : ∀ i : Fin n, MemLp (Y i) 4 P := fun i ↦ (hY_pr i).2.2.1 4
  have hY0 : ∀ i : Fin n, ∫ ω, Y i ω ∂P = 0 := fun i ↦ (hY_pr i).2.2.2.1
  have hY2 : ∀ i : Fin n, ∫ ω, Y i ω ^ 2 ∂P = 1 := fun i ↦ by
    rw [(hY_pr i).2.2.2.2.1, hσ₀_sq, div_self hpq.ne']
  have hY_indep : ProbabilityTheory.iIndepFun Y P :=
    hX_indep.comp (fun _ x ↦ (x - p) / σ₀)
      (fun _ ↦ (measurable_id.sub_const p).div_const σ₀)
  have hW_pt : ∀ ω : Ω, (∑ i : Fin n, Y i ω) / Real.sqrt n = W ω := fun ω ↦ by
    dsimp [Y, W]
    have hsum : ∑ i : Fin n, (X i ω - p) / σ₀ =
        ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / σ₀ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hden : Real.sqrt ((n : ℝ) * p * (1 - p)) = σ₀ * Real.sqrt n := by
      rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg n), mul_comm]
    rw [hsum, hden, div_div]
  have hW_meas : Measurable W :=
    ((Finset.measurable_fun_sum _ fun i _ ↦ hX_meas i).sub_const _).div_const _
  have habs_pow4 : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x ↦ by
    calc |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [sq_abs]
      _ = x ^ 4 := by ring
  have hY3_le : ∀ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P ≤ 1 / σ₀ ^ 3 := fun i ↦ by
    have hint3 : Integrable (fun ω ↦ |Y i ω| ^ 3) P := by
      have h3 : MemLp (Y i) 3 P := (hY4 i).mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ 4)
      simpa only [Real.norm_eq_abs] using h3.integrable_norm_pow'
    have hae3 : ∀ᵐ ω ∂P, |Y i ω| ^ 3 ≤ 1 / σ₀ ^ 3 := by
      filter_upwards [hY_bdd i] with ω hω
      simpa [one_pow, div_pow] using pow_le_pow_left₀ (abs_nonneg _) hω 3
    calc ∫ ω, |Y i ω| ^ 3 ∂P
        ≤ ∫ _ : Ω, (1 / σ₀ ^ 3) ∂P := integral_mono_ae hint3 (integrable_const _) hae3
      _ = 1 / σ₀ ^ 3 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hY4_le : ∀ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P ≤ 1 / σ₀ ^ 4 := fun i ↦ by
    have hint4 : Integrable (fun ω ↦ Y i ω ^ 4) P := by
      have h4 := (hY4 i).integrable_norm_pow'
      simpa only [Real.norm_eq_abs, habs_pow4] using h4
    have hae4 : ∀ᵐ ω ∂P, Y i ω ^ 4 ≤ 1 / σ₀ ^ 4 := by
      filter_upwards [hY_bdd i] with ω hω
      rw [← habs_pow4]
      simpa [one_pow, div_pow] using pow_le_pow_left₀ (abs_nonneg _) hω 4
    calc ∫ ω, Y i ω ^ 4 ∂P
        ≤ ∫ _ : Ω, (1 / σ₀ ^ 4) ∂P := integral_mono_ae hint4 (integrable_const _) hae4
      _ = 1 / σ₀ ^ 4 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hsum3 : ∑ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P ≤ (n : ℝ) * (1 / σ₀ ^ 3) := by
    calc ∑ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P
        ≤ ∑ _ : Fin n, (1 / σ₀ ^ 3) := Finset.sum_le_sum fun i _ ↦ hY3_le i
      _ = (n : ℝ) * (1 / σ₀ ^ 3) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum4 :
      Real.sqrt (∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P) ≤ Real.sqrt n * (1 / σ₀ ^ 2) := by
    have hle : ∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P ≤ (n : ℝ) * (1 / σ₀ ^ 2) ^ 2 := by
      calc ∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P
          ≤ ∑ _ : Fin n, (1 / σ₀ ^ 4) := Finset.sum_le_sum fun i _ ↦ hY4_le i
        _ = (n : ℝ) * (1 / σ₀ ^ 2) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc Real.sqrt (∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P)
        ≤ Real.sqrt ((n : ℝ) * (1 / σ₀ ^ 2) ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt n * (1 / σ₀ ^ 2) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (by positivity)]
  have hrpow32 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hn_pos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hsqrt_div_n : Real.sqrt n / (n : ℝ) = 1 / Real.sqrt n := by
    rw [div_eq_div_iff hn_pos.ne' hsqrt_n_pos.ne', one_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have halg :
      1 / (n : ℝ) ^ (3 / 2 : ℝ) * (∑ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P) +
        Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) *
          Real.sqrt (∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P) ≤
      (1 / σ₀ ^ 3 + Real.sqrt 2 / (Real.sqrt Real.pi * σ₀ ^ 2)) *
        (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    have ht1 : 1 / (n : ℝ) ^ (3 / 2 : ℝ) * (∑ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P) ≤
        (1 / σ₀ ^ 3) * (1 / Real.sqrt n) := by
      calc 1 / (n : ℝ) ^ (3 / 2 : ℝ) * (∑ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P)
          ≤ 1 / (n : ℝ) ^ (3 / 2 : ℝ) * ((n : ℝ) * (1 / σ₀ ^ 3)) :=
            mul_le_mul_of_nonneg_left hsum3 (by positivity)
        _ = (1 / σ₀ ^ 3) * (1 / Real.sqrt n) := by
            rw [hrpow32]; field_simp [hn_pos.ne', hsqrt_n_pos.ne', hσ₀_pos.ne']
    have ht2 : Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) *
          Real.sqrt (∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P) ≤
        (Real.sqrt 2 / (Real.sqrt Real.pi * σ₀ ^ 2)) * (1 / Real.sqrt n) := by
      calc Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) *
            Real.sqrt (∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P)
          ≤ Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) * (Real.sqrt n * (1 / σ₀ ^ 2)) :=
            mul_le_mul_of_nonneg_left hsum4 (by positivity)
        _ = (Real.sqrt 2 / (Real.sqrt Real.pi * σ₀ ^ 2)) * (Real.sqrt n / (n : ℝ)) := by ring
        _ = (Real.sqrt 2 / (Real.sqrt Real.pi * σ₀ ^ 2)) * (1 / Real.sqrt n) := by
            rw [hsqrt_div_n]
    rw [rpow_neg_half_eq_one_div_sqrt]; linarith
  have hstep1 := wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P' hW_meas.aemeasurable
    hZ hZ_law
  have hstep2 := indepSum_iSup_normalWassersteinClass_le P hn0 (fun i ↦ (hY_meas i).aemeasurable)
    hY_indep hY4 hY0 hY2
  dsimp only at hstep2
  simp_rw [hW_pt] at hstep2
  exact (hstep1.trans hstep2).trans (ENNReal.ofReal_le_ofReal halg)

/-! ### Section 3: Kolmogorov Upper Bound (`binomial_kolmogorovDist_le`) -/

/-- Quantitative Kolmogorov upper bound of order $n^{-1/2}$ for standardized $\mathrm{Bin}(n,p)$
(`SteinIntro.tex:1655-1657`, via Proposition 3.19, Proposition 3.21, and Theorem 3.27). -/
theorem binomial_kolmogorovDist_le
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hn : 1 ≤ n) (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (hX_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hX_prob : ∀ i : Fin n, P.real (X i ⁻¹' {1}) = p)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let σ₀ : ℝ := Real.sqrt (p * (1 - p))
    let W : Ω → ℝ :=
      fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 / σ₀)) *
          (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  intro σ₀ W
  have hpq : 0 < p * (1 - p) := mul_pos hp0 (sub_pos.mpr hp1)
  have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr hpq
  have hn0 : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  obtain ⟨_, hs_eq, hW_sum_U, hW_meas, hU_meas, hU_bdd, hU_L2, hU_mean, hU_var, hU_indep,
    _, _⟩ := bernoulli_stdSum_props P hp0 hp1 hn hX_meas hX_indep hX_01 hX_prob
  let s : ℝ := Real.sqrt ((n : ℝ) * p * (1 - p))
  let i₀ : Fin n := ⟨0, hn0⟩
  let U : Fin n → Ω → ℝ := fun i ω ↦ (X i ω - p) / s
  have hU0_var_pos : 0 < ProbabilityTheory.variance (U i₀) P := by rw [hU_var i₀]; positivity
  have hU_id : ∀ i : Fin n, ProbabilityTheory.IdentDistrib (U i₀) (U i) P P := fun i ↦
    (bernoulli_identDistrib P (hX_meas i₀) (hX_meas i) (hX_01 i₀) (hX_01 i)
      (hX_prob i₀) (hX_prob i)).comp ((measurable_id.sub_const p).div_const s)
  let ν : Measure ℝ :=
    volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P (U i₀) w))
  have hchar := zeroBias_law_characterization (Ω' := ℝ) P (hU_L2 i₀) (hU_mean i₀) hU0_var_pos
  have : IsProbabilityMeasure ν := hchar.2.2.1
  have hZB0 : IsZeroBias P (U i₀) ν id := hchar.2.2.2
  have hν_bdd : ∀ᵐ z ∂ν, |z| ≤ 1 / s :=
    ae_abs_le_of_isZeroBias_of_ae_abs_le P ν hU0_var_pos hZB0 (hU_bdd i₀)
  let μI : Measure (Fin n) := (@PMF.uniformOfFintype (Fin n) inferInstance ⟨i₀⟩).toMeasure
  let P_p : Measure ((Ω × ℝ) × Fin n) := (P.prod ν).prod μI
  let π₁ : (Ω × ℝ) × Fin n → Ω × ℝ := Prod.fst
  let πΩ : (Ω × ℝ) × Fin n → Ω := fun q ↦ q.1.1
  let πR : (Ω × ℝ) × Fin n → ℝ := fun q ↦ q.1.2
  let Ip : (Ω × ℝ) × Fin n → Fin n := Prod.snd
  have hmp₁ : MeasurePreserving π₁ P_p (P.prod ν) := measurePreserving_fst
  have hmpΩ : MeasurePreserving πΩ P_p P := measurePreserving_fst.comp hmp₁
  have hmpR : MeasurePreserving πR P_p ν := measurePreserving_snd.comp hmp₁
  have hmpI : MeasurePreserving Ip P_p μI := measurePreserving_snd
  let Up : Fin n → (Ω × ℝ) × Fin n → ℝ := fun i q ↦ U i (πΩ q)
  let Uz : Fin n → (Ω × ℝ) × Fin n → ℝ := fun _ q ↦ πR q
  have hUp_meas : ∀ i : Fin n, Measurable (Up i) := fun i ↦
    (hU_meas i).comp (measurable_fst.comp measurable_fst)
  have hUz_meas : ∀ i : Fin n, Measurable (Uz i) := fun _ ↦ measurable_snd.comp measurable_fst
  have hUp_id : ∀ i : Fin n, ProbabilityTheory.IdentDistrib (U i) (Up i) P P_p := fun i ↦
    ⟨(hU_meas i).aemeasurable, (hUp_meas i).aemeasurable, by
      have hcomp : Up i = U i ∘ πΩ := rfl
      rw [hcomp, ← Measure.map_map (hU_meas i) hmpΩ.measurable, hmpΩ.map_eq]⟩
  have hUz_id : ∀ i : Fin n, ProbabilityTheory.IdentDistrib id (Uz i) ν P_p := fun i ↦
    ⟨aemeasurable_id, (hUz_meas i).aemeasurable, by rw [Measure.map_id]; exact hmpR.map_eq.symm⟩
  have hUp_indep : ProbabilityTheory.iIndepFun Up P_p :=
    iIndepFun_comp_measurePreserving hU_meas hU_indep hmpΩ
  have hUp_L2 : ∀ i : Fin n, MemLp (Up i) 2 P_p := fun i ↦ (hUp_id i).memLp_snd (hU_L2 i)
  have hUp_mean : ∀ i : Fin n, ∫ q, Up i q ∂P_p = 0 := fun i ↦ by
    rw [← (hUp_id i).integral_eq, hU_mean i]
  have hUp_var : ∀ i : Fin n,
      ProbabilityTheory.variance (Up i) P_p = 1 / (n : ℝ) := fun i ↦ by
    rw [← (hUp_id i).variance_eq, hU_var i]
  have hVar_sum : (∑ i : Fin n, ProbabilityTheory.variance (Up i) P_p) = 1 := by
    simp_rw [hUp_var]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div_cancel hn_pos.ne']
  have hUz_zb : ∀ i : Fin n, IsZeroBias P_p (Up i) P_p (Uz i) := fun i ↦
    hZB0.congr_identDistrib ((hU_id i).trans (hUp_id i)) (hUz_id i)
  have hUz_indep : ∀ i : Fin n,
      ProbabilityTheory.IndepFun (Uz i) (fun q (j : {j : Fin n // j ≠ i}) ↦ Up j q) P_p := by
    intro i
    let f_not : Ω → {j : Fin n // j ≠ i} → ℝ := fun ω j ↦ U j.1 ω
    have hf_not : Measurable f_not := Measurable.of_eval fun j ↦ hU_meas j.1
    have hind_base :
        ProbabilityTheory.IndepFun (fun r : Ω × ℝ ↦ r.2)
          (fun r : Ω × ℝ ↦ f_not r.1) (P.prod ν) :=
      (ProbabilityTheory.indepFun_prod hf_not measurable_id).symm
    exact indepFun_comp_measurePreserving measurable_snd (hf_not.comp measurable_fst)
      hind_base hmp₁
  have hIp_prob :
      ∀ i : Fin n, P_p.real (Ip ⁻¹' {i}) = ProbabilityTheory.variance (Up i) P_p := by
    intro i
    have : Nonempty (Fin n) := ⟨i₀⟩
    have hmeas : P_p (Ip ⁻¹' {i}) = (n : ℝ≥0∞)⁻¹ := by
      rw [← Measure.map_apply measurable_snd (measurableSet_singleton i), hmpI.map_eq,
        PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
        PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [measureReal_def, hmeas, ENNReal.toReal_inv, ENNReal.toReal_natCast, ← one_div, hUp_var i]
  have hIp_indep :
      ProbabilityTheory.IndepFun Ip (fun q ↦ (fun i ↦ Up i q, fun i ↦ Uz i q)) P_p := by
    let pairFn : Ω × ℝ → (Fin n → ℝ) × (Fin n → ℝ) :=
      fun r ↦ (fun i ↦ U i r.1, fun _ ↦ r.2)
    have hpair_meas : Measurable pairFn :=
      (Measurable.of_eval fun i ↦ (hU_meas i).comp measurable_fst).prodMk
        (Measurable.of_eval fun _ ↦ measurable_snd)
    exact (ProbabilityTheory.indepFun_prod hpair_meas measurable_id).symm
  have hZB_sum := zeroBias_sum_of_iIndepFun P_p hUp_meas hUz_meas hUp_indep hUp_L2 hUp_mean
    hVar_sum hUz_zb hUz_indep measurable_snd hIp_prob hIp_indep
  let Wp : (Ω × ℝ) × Fin n → ℝ := fun q ↦ ∑ i : Fin n, Up i q
  let Wzp : (Ω × ℝ) × Fin n → ℝ :=
    fun q ↦ (∑ j ∈ Finset.univ.erase (Ip q), Up j q) + Uz (Ip q) q
  have hWp_comp : Wp = W ∘ πΩ := by
    ext q
    exact (congr_fun hW_sum_U (πΩ q)).symm
  have hmap_Wp : P_p.map Wp = P.map W := by
    rw [hWp_comp, ← Measure.map_map hW_meas hmpΩ.measurable, hmpΩ.map_eq]
  have hWp_var : ProbabilityTheory.variance Wp P_p = 1 := by
    have hWp_fn : Wp = ∑ i ∈ Finset.univ, Up i := by ext q; simp [Wp]
    rw [hWp_fn, IndepFun.variance_sum (fun i _ ↦ hUp_L2 i)
      (fun i _ j _ hij ↦ hUp_indep.indepFun hij), hVar_sum]
  have hdiff_bdd : ∀ᵐ q ∂P_p, |Wzp q - Wp q| ≤ 2 / s := by
    have hR_bdd : ∀ᵐ q ∂P_p, |πR q| ≤ 1 / s := hmpR.quasiMeasurePreserving.ae hν_bdd
    have hUp_all_bdd : ∀ᵐ q ∂P_p, ∀ i : Fin n, |Up i q| ≤ 1 / s :=
      ae_all_iff.mpr fun i ↦ hmpΩ.quasiMeasurePreserving.ae (hU_bdd i)
    filter_upwards [hR_bdd, hUp_all_bdd] with q hqR hqU
    have hsub : Wzp q - Wp q = πR q - Up (Ip q) q := by
      dsimp [Wzp, Wp, Uz]
      have herase := Finset.add_sum_erase Finset.univ (fun j ↦ Up j q) (Finset.mem_univ (Ip q))
      linarith
    rw [hsub]
    have htri : |πR q - Up (Ip q) q| ≤ |πR q| + |Up (Ip q) q| := by
      simpa [Real.norm_eq_abs] using norm_sub_le (πR q) (Up (Ip q) q)
    have hqUi := hqU (Ip q)
    linarith [show (1 : ℝ) / s + 1 / s = 2 / s by ring]
  have hthm := kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd P_p P' hWp_var hZB_sum hdiff_bdd
    hZ hZ_law
  rw [hmap_Wp] at hthm
  have hrhs_eq :
      (1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 / s) =
        ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 / σ₀)) *
          (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [rpow_neg_half_eq_one_div_sqrt, show s = Real.sqrt n * σ₀ from hs_eq]
    field_simp [hsqrt_n_pos.ne', hσ₀_pos.ne']
  rwa [hrhs_eq] at hthm

end SteinMethod
