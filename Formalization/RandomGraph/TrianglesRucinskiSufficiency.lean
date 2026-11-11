/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.SteinPairBound
import Formalization.RandomGraph.TrianglesRucinskiMoments
import Formalization.SizeBias.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Sufficiency Direction for Ruciński's Triangle CLT (`TrianglesRucinskiSufficiency`)

Combines `triangles_sizeBias_coupling` (`TrianglesRucinskiCoupling`),
`sum_triangles_sup_tripleGraph_sub` (`TrianglesRucinskiIdentities`),
`variance_rucTwoEdgeSum_le` and `delta_slice_sq_integral_le` (`TrianglesRucinskiMoments`),
and Theorem 3.13 (`sizeBias_wassersteinDist_le`) to establish:

* `triangles_wassersteinDist_le_rucinskiRate`: unified Wasserstein normal approximation bound
  $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{N}(0, 1)) \le
  \text{ENNReal.ofReal}(2500 / \sqrt{n p} + 2500 / \sqrt{n^2 (1 - p)})$ for $n \ge 6$, $0 < p < 1$,
  and $1 \le n p$ (`SteinIntro.tex:943-944`, `\cite{ruc88}`).
* `tendsto_triangles_wassersteinDist_zero_of_rucinski`: sufficiency ($n p_n \to \infty \land
  n^2 (1 - p_n) \to \infty \implies d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1)) \to 0$).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### 1. Finite-Space $L^p$, Variance, and Product Conditional-Expectation Helpers -/

private lemma memLp_of_finite_ruc {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (q : ℝ≥0∞) :
    MemLp f q μ := by
  have := Fintype.ofFinite α
  exact MemLp.of_bound (measurable_of_finite f).aestronglyMeasurable
    (∑ x : α, ‖f x‖) (Eventually.of_forall fun x ↦
      Finset.single_le_sum (fun y _ ↦ norm_nonneg (f y)) (Finset.mem_univ x))

private lemma variance_fun_add_le_ruc {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {A B : α → ℝ} (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    ProbabilityTheory.variance (fun x ↦ A x + B x) μ ≤
      2 * ProbabilityTheory.variance A μ + 2 * ProbabilityTheory.variance B μ := by
  have hAi : Integrable A μ := hA.integrable one_le_two
  have hBi : Integrable B μ := hB.integrable one_le_two
  have hA2 : Integrable (fun x ↦ (A x - ∫ y, A y ∂μ) ^ 2) μ :=
    (hA.sub (memLp_const _)).integrable_sq
  have hB2 : Integrable (fun x ↦ (B x - ∫ y, B y ∂μ) ^ 2) μ :=
    (hB.sub (memLp_const _)).integrable_sq
  have hAB : MemLp (fun x ↦ A x + B x) 2 μ := hA.add hB
  rw [ProbabilityTheory.variance_eq_integral hAB.aemeasurable,
    ProbabilityTheory.variance_eq_integral hA.aemeasurable,
    ProbabilityTheory.variance_eq_integral hB.aemeasurable,
    integral_add hAi hBi, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hA2.const_mul 2) (hB2.const_mul 2)]
  refine integral_mono_ae ((hAB.sub (memLp_const _)).integrable_sq)
    ((hA2.const_mul 2).add (hB2.const_mul 2)) (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  nlinarith [sq_nonneg ((A x - ∫ y, A y ∂μ) - (B x - ∫ y, B y ∂μ))]

private lemma condExp_fst_prod_finite_ruc {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : α × β → ℝ) :
    (fun ω : α × β ↦ ∫ b, f (ω.1, b) ∂ν) =ᵐ[μ.prod ν]
      (μ.prod ν)[f | MeasurableSpace.comap Prod.fst inferInstance] := by
  let g₀ : α → ℝ := fun a ↦ ∫ b, f (a, b) ∂ν
  have hg_sm : StronglyMeasurable[MeasurableSpace.comap (Prod.fst : α × β → α) inferInstance]
      (g₀ ∘ Prod.fst) :=
    (measurable_of_finite g₀).stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
  have hf_int : Integrable f (μ.prod ν) := Integrable.of_finite
  have hg_int : Integrable (g₀ ∘ Prod.fst) (μ.prod ν) := Integrable.of_finite
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf_int
    (fun _ _ _ ↦ hg_int.integrableOn) (fun s hs _ ↦ ?_) hg_sm.aestronglyMeasurable
  rcases hs with ⟨A, hA, rfl⟩
  have hs_meas : MeasurableSet (Prod.fst ⁻¹' A : Set (α × β)) := measurable_fst hA
  change ∫ x in Prod.fst ⁻¹' A, (g₀ ∘ Prod.fst) x ∂(μ.prod ν) = _
  rw [← integral_indicator hs_meas, ← integral_indicator hs_meas,
    integral_prod _ (hg_int.indicator hs_meas), integral_prod _ (hf_int.indicator hs_meas)]
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  dsimp only
  by_cases ha : a ∈ A
  · have h1 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator (g₀ ∘ Prod.fst) (a, b)) =
        fun _ ↦ g₀ a :=
      funext fun _ ↦ Set.indicator_of_mem (s := Prod.fst ⁻¹' A) ha (g₀ ∘ Prod.fst)
    have h2 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator f (a, b)) = fun b ↦ f (a, b) :=
      funext fun _ ↦ Set.indicator_of_mem (s := Prod.fst ⁻¹' A) ha f
    rw [h1, h2, integral_const, probReal_univ, one_smul]
  · have h1 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator (g₀ ∘ Prod.fst) (a, b)) = 0 :=
      funext fun _ ↦ Set.indicator_of_notMem (s := Prod.fst ⁻¹' A) ha (g₀ ∘ Prod.fst)
    have h2 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator f (a, b)) = 0 :=
      funext fun _ ↦ Set.indicator_of_notMem (s := Prod.fst ⁻¹' A) ha f
    rw [h1, h2]

/-! ### 2. Real-Arithmetic Rate Combination and Theorem 3.13 Bound -/

private lemma inv_npq_le_max_inv {n : ℕ} {p : ℝ} (hn : 6 ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hnp : 1 ≤ (n : ℝ) * p) :
    let A := (n : ℝ) * p
    let B := (n : ℝ) ^ 2 * (1 - p)
    1 / ((n : ℝ) ^ 2 * p * (1 - p)) ≤ 2 / A + 2 / B ∧
      1 / ((n : ℝ) ^ 3 * p ^ 3 * (1 - p)) ≤ 2 / A + 2 / B := by
  intro A B
  have hn_cast : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hA_pos : 0 < A := by linarith
  have hB_pos : 0 < B := mul_pos (by positivity) (by linarith)
  by_cases hp_half : p ≤ 1 / 2
  · have hq_half : 1 / 2 ≤ 1 - p := by linarith
    have h1 : A / 2 ≤ (n : ℝ) ^ 2 * p * (1 - p) := by
      have hn_le_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
      have : (n : ℝ) * p ≤ (n : ℝ) ^ 2 * p := mul_le_mul_of_nonneg_right hn_le_sq hp0.le
      nlinarith
    have h2 : A / 2 ≤ (n : ℝ) ^ 3 * p ^ 3 * (1 - p) := by
      have hA3 : A ≤ A ^ 3 := by nlinarith [sq_nonneg (A - 1)]
      have hA3_eq : A ^ 3 = (n : ℝ) ^ 3 * p ^ 3 := by ring
      nlinarith
    have hB_nn : 0 ≤ 2 / B := by positivity
    refine ⟨?_, ?_⟩
    · have := one_div_le_one_div_of_le (by linarith : 0 < A / 2) h1
      rw [one_div_div] at this
      linarith
    · have := one_div_le_one_div_of_le (by linarith : 0 < A / 2) h2
      rw [one_div_div] at this
      linarith
  · push Not at hp_half
    have h1 : B / 2 ≤ (n : ℝ) ^ 2 * p * (1 - p) := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (1 - p) := hB_pos.le
      nlinarith
    have h2 : B / 2 ≤ (n : ℝ) ^ 3 * p ^ 3 * (1 - p) := by
      have hp3 : (1 / 8 : ℝ) ≤ p ^ 3 := by nlinarith [sq_nonneg p]
      have hn3 : 6 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
      have hqp : 0 ≤ 1 - p := by linarith
      calc B / 2 = (1 / 2 : ℝ) * ((n : ℝ) ^ 2 * (1 - p)) := by ring
        _ ≤ (6 * (1 / 8 : ℝ)) * ((n : ℝ) ^ 2 * (1 - p)) :=
            mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = (6 * (n : ℝ) ^ 2) * (1 / 8 : ℝ) * (1 - p) := by ring
        _ ≤ (n : ℝ) ^ 3 * p ^ 3 * (1 - p) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hn3 hp3 (by positivity) (by positivity)) hqp
    have hA_nn : 0 ≤ 2 / A := by positivity
    refine ⟨?_, ?_⟩
    · have := one_div_le_one_div_of_le (by linarith : 0 < B / 2) h1
      rw [one_div_div] at this
      linarith
    · have := one_div_le_one_div_of_le (by linarith : 0 < B / 2) h2
      rw [one_div_div] at this
      linarith

private lemma combine_rucinski_stein_bounds {n : ℕ} {p μ v vQ intD2 : ℝ}
    (hn : 6 ≤ n) (hp0 : 0 < p) (hp1 : p < 1) (hnp : 1 ≤ (n : ℝ) * p)
    (hμ_pos : 0 < μ) (hμ_le : μ ≤ (n : ℝ) ^ 3 * p ^ 3 / 6)
    (hv_lo1 : (n : ℝ) ^ 3 * p ^ 3 * (1 - p) / 24 ≤ v)
    (hv_lo2 : (n : ℝ) ^ 4 * p ^ 5 * (1 - p) / 16 ≤ v)
    (_hvQ_nn : 0 ≤ vQ)
    (hvQ_le : vQ ≤ 2 * (24 / (n : ℝ) ^ 3) ^ 2 * v + 5760 * p ^ 3 * (1 - p))
    (hintD2_nn : 0 ≤ intD2)
    (hintD2_le : intD2 ≤ 36 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4)) :
    let σ := Real.sqrt v
    (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt vQ + (μ / σ ^ 3) * intD2 ≤
      2500 / Real.sqrt ((n : ℝ) * p) + 2500 / Real.sqrt ((n : ℝ) ^ 2 * (1 - p)) := by
  intro σ
  have hn_cast : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < 1 - p := by linarith
  have hv_pos : 0 < v := lt_of_lt_of_le (by positivity) hv_lo1
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hv_pos
  have hσ_sq : σ ^ 2 = v := Real.sq_sqrt hv_pos.le
  let A := (n : ℝ) * p
  let B := (n : ℝ) ^ 2 * (1 - p)
  have hA_pos : 0 < A := by linarith
  have hB_pos : 0 < B := by positivity
  obtain ⟨hinv1, hinv2⟩ := inv_npq_le_max_inv hn hp0 hp1 hnp
  have hsqrt_2pi : Real.sqrt (2 / Real.pi) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact div_le_one_of_le₀ Real.two_le_pi Real.pi_pos.le
  have hsqrt_vQ : Real.sqrt vQ ≤
      (36 / (n : ℝ) ^ 3) * σ + 80 * p * Real.sqrt (p * (1 - p)) := by
    have hrhs_nn : 0 ≤ (36 / (n : ℝ) ^ 3) * σ + 80 * p * Real.sqrt (p * (1 - p)) := by positivity
    rw [← Real.sqrt_sq hrhs_nn]
    refine Real.sqrt_le_sqrt (hvQ_le.trans ?_)
    have h1 : 2 * (24 / (n : ℝ) ^ 3) ^ 2 * v ≤ ((36 / (n : ℝ) ^ 3) * σ) ^ 2 := by
      rw [mul_pow, hσ_sq]
      have : 2 * (24 : ℝ) ^ 2 ≤ (36 : ℝ) ^ 2 := by norm_num
      have hden : 0 ≤ v / ((n : ℝ) ^ 3) ^ 2 := by positivity
      nlinarith [show (24 / (n : ℝ) ^ 3) ^ 2 * v = (24 : ℝ) ^ 2 * (v / ((n : ℝ) ^ 3) ^ 2) by ring,
        show (36 / (n : ℝ) ^ 3) ^ 2 * v = (36 : ℝ) ^ 2 * (v / ((n : ℝ) ^ 3) ^ 2) by ring]
    have h2 : 5760 * p ^ 3 * (1 - p) ≤ (80 * p * Real.sqrt (p * (1 - p))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have : (0 : ℝ) ≤ p ^ 3 * (1 - p) := by positivity
      nlinarith
    have hcross : 0 ≤ 2 * ((36 / (n : ℝ) ^ 3) * σ) * (80 * p * Real.sqrt (p * (1 - p))) := by
      positivity
    linarith [show ((36 / (n : ℝ) ^ 3) * σ + 80 * p * Real.sqrt (p * (1 - p))) ^ 2 =
      ((36 / (n : ℝ) ^ 3) * σ) ^ 2 + (80 * p * Real.sqrt (p * (1 - p))) ^ 2 +
        2 * ((36 / (n : ℝ) ^ 3) * σ) * (80 * p * Real.sqrt (p * (1 - p))) by ring]
  have hterm1 : (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt vQ ≤
      6 * p ^ 3 / σ + 14 * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) / v := by
    calc (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt vQ
        ≤ (μ / σ ^ 2 * 1) * ((36 / (n : ℝ) ^ 3) * σ + 80 * p * Real.sqrt (p * (1 - p))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_2pi (by positivity)) hsqrt_vQ
            (Real.sqrt_nonneg _) (by positivity)
      _ ≤ (((n : ℝ) ^ 3 * p ^ 3 / 6) / σ ^ 2) *
            ((36 / (n : ℝ) ^ 3) * σ + 80 * p * Real.sqrt (p * (1 - p))) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hμ_le (sq_nonneg σ)) (by positivity)
      _ = 6 * p ^ 3 / σ + (40 / 3 : ℝ) * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) / v := by
          have hn3_ne : (n : ℝ) ^ 3 ≠ 0 := by positivity
          have hσ_ne : σ ≠ 0 := hσ_pos.ne'
          rw [mul_add, hσ_sq]
          congr 1
          · rw [← hσ_sq]
            field_simp [hn3_ne, hσ_ne]
            ring
          · ring
      _ ≤ 6 * p ^ 3 / σ + 14 * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) / v := by
          refine add_le_add le_rfl (div_le_div_of_nonneg_right ?_ hv_pos.le)
          calc (40 / 3 : ℝ) * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p))
              = (40 / 3 : ℝ) * ((n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p))) := by ring
            _ ≤ 14 * ((n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p))) :=
                mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = 14 * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) := by ring
  have hterm2 : (μ / σ ^ 3) * intD2 ≤
      6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p) / σ ^ 3 +
        6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p) / σ ^ 3 := by
    calc (μ / σ ^ 3) * intD2
        ≤ (((n : ℝ) ^ 3 * p ^ 3 / 6) / σ ^ 3) * (36 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4)) :=
          mul_le_mul (div_le_div_of_nonneg_right hμ_le (pow_nonneg hσ_pos.le 3)) hintD2_le
            hintD2_nn (by positivity)
      _ = 6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p) / σ ^ 3 +
            6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p) / σ ^ 3 := by ring
  let R := 1 / Real.sqrt A + 1 / Real.sqrt B
  have hR_pos : 0 < R := by positivity
  have hAB_to_R2 : ∀ x : ℝ, x ≤ 2 / ((n : ℝ) * p) + 2 / ((n : ℝ) ^ 2 * (1 - p)) →
      x ≤ 2 * R ^ 2 := by
    intro x hx
    have hsqR : 1 / ((n : ℝ) * p) + 1 / ((n : ℝ) ^ 2 * (1 - p)) ≤ R ^ 2 := by
      dsimp only [R, A, B]
      rw [add_sq, div_pow, div_pow, one_pow,
        Real.sq_sqrt (by linarith : 0 ≤ (n : ℝ) * p),
        Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) ^ 2 * (1 - p))]
      have : 0 ≤ 2 * (1 / Real.sqrt ((n : ℝ) * p)) * (1 / Real.sqrt ((n : ℝ) ^ 2 * (1 - p))) := by
        positivity
      linarith
    have htwo : 2 / ((n : ℝ) * p) + 2 / ((n : ℝ) ^ 2 * (1 - p)) =
        2 * (1 / ((n : ℝ) * p) + 1 / ((n : ℝ) ^ 2 * (1 - p))) := by ring
    linarith
  have hb1 : 6 * p ^ 3 / σ ≤ 42 * R := by
    have hsq : (6 * p ^ 3 / σ) ^ 2 ≤ (42 * R) ^ 2 := by
      rw [div_pow, hσ_sq]
      have h1 : (6 * p ^ 3) ^ 2 / v ≤ 864 * (p ^ 3 / ((n : ℝ) ^ 3 * (1 - p))) := by
        calc (6 * p ^ 3) ^ 2 / v
            ≤ (6 * p ^ 3) ^ 2 / ((n : ℝ) ^ 3 * p ^ 3 * (1 - p) / 24) :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hv_lo1
          _ = 864 * (p ^ 3 / ((n : ℝ) ^ 3 * (1 - p))) := by
              field_simp [hp0.ne', hq.ne', (show (n : ℝ) ≠ 0 by positivity)]
              ring
      have h2 : p ^ 3 / ((n : ℝ) ^ 3 * (1 - p)) ≤ 1 / ((n : ℝ) ^ 2 * p * (1 - p)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hp4 : p ^ 4 ≤ 1 := pow_le_one₀ hp0.le hp1.le
        have hn23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by nlinarith [sq_nonneg (n : ℝ)]
        calc p ^ 3 * ((n : ℝ) ^ 2 * p * (1 - p))
            = p ^ 4 * ((n : ℝ) ^ 2 * (1 - p)) := by ring
          _ ≤ 1 * ((n : ℝ) ^ 3 * (1 - p)) :=
              mul_le_mul hp4 (mul_le_mul_of_nonneg_right hn23 hq.le) (by positivity) zero_le_one
      have h3 := hAB_to_R2 _ (h2.trans hinv1)
      calc (6 * p ^ 3) ^ 2 / v
          ≤ 864 * (p ^ 3 / ((n : ℝ) ^ 3 * (1 - p))) := h1
        _ ≤ 864 * (2 * R ^ 2) := mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 1728 * R ^ 2 := by ring
        _ ≤ 1764 * R ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg R)
        _ = (42 * R) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hsqrt
  have hb2 : 14 * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) / v ≤ 320 * R := by
    have hle : 14 * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) / v ≤
        224 / Real.sqrt ((n : ℝ) ^ 2 * p * (1 - p)) := by
      calc 14 * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) / v
          ≤ 14 * (n : ℝ) ^ 3 * p ^ 4 * Real.sqrt (p * (1 - p)) /
              ((n : ℝ) ^ 4 * p ^ 5 * (1 - p) / 16) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hv_lo2
        _ = 224 * Real.sqrt (p * (1 - p)) / ((n : ℝ) * p * (1 - p)) := by
            field_simp [hp0.ne', hq.ne', (show (n : ℝ) ≠ 0 by positivity)]
            ring
        _ = 224 / Real.sqrt ((n : ℝ) ^ 2 * p * (1 - p)) := by
            have hpos_pq : 0 < p * (1 - p) := mul_pos hp0 hq
            have hsqrt_den : Real.sqrt ((n : ℝ) ^ 2 * p * (1 - p)) =
                (n : ℝ) * Real.sqrt (p * (1 - p)) := by
              rw [mul_assoc, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
            rw [hsqrt_den]
            field_simp [hpos_pq.ne', (Real.sqrt_pos.mpr hpos_pq).ne',
              (show (n : ℝ) ≠ 0 by positivity)]
            rw [Real.sq_sqrt hpos_pq.le]
    refine hle.trans ?_
    have hsq : (224 / Real.sqrt ((n : ℝ) ^ 2 * p * (1 - p))) ^ 2 ≤ (320 * R) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by positivity)]
      have h3 := hAB_to_R2 _ hinv1
      calc (224 : ℝ) ^ 2 / ((n : ℝ) ^ 2 * p * (1 - p))
          = 50176 * (1 / ((n : ℝ) ^ 2 * p * (1 - p))) := by ring
        _ ≤ 50176 * (2 * R ^ 2) := mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 100352 * R ^ 2 := by ring
        _ ≤ 102400 * R ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg R)
        _ = (320 * R) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hsqrt
  have hσ6 : σ ^ 6 = v ^ 3 := by
    calc σ ^ 6 = (σ ^ 2) ^ 3 := by ring
      _ = v ^ 3 := by rw [hσ_sq]
  have hb3 : 6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p) / σ ^ 3 ≤ 1000 * R := by
    have hsq : (6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p) / σ ^ 3) ^ 2 ≤ (1000 * R) ^ 2 := by
      rw [div_pow, ← pow_mul, hσ6]
      have h1 : (6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p)) ^ 2 / v ^ 3 ≤
          497664 * (1 / ((n : ℝ) ^ 3 * p ^ 3 * (1 - p))) := by
        calc (6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p)) ^ 2 / v ^ 3
            ≤ (6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p)) ^ 2 /
                ((n : ℝ) ^ 3 * p ^ 3 * (1 - p) / 24) ^ 3 :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
                (pow_le_pow_left₀ (by positivity) hv_lo1 3)
          _ = 497664 * (1 / ((n : ℝ) ^ 3 * p ^ 3 * (1 - p))) := by
              field_simp [hp0.ne', hq.ne', (show (n : ℝ) ≠ 0 by positivity)]
              ring
      have h3 := hAB_to_R2 _ hinv2
      calc (6 * (n : ℝ) ^ 3 * p ^ 3 * (1 - p)) ^ 2 / v ^ 3
          ≤ 497664 * (1 / ((n : ℝ) ^ 3 * p ^ 3 * (1 - p))) := h1
        _ ≤ 497664 * (2 * R ^ 2) := mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 995328 * R ^ 2 := by ring
        _ ≤ 1000000 * R ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg R)
        _ = (1000 * R) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hsqrt
  have hb4 : 6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p) / σ ^ 3 ≤ 550 * R := by
    have hsq : (6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p) / σ ^ 3) ^ 2 ≤ (550 * R) ^ 2 := by
      rw [div_pow, ← pow_mul, hσ6]
      have h1 : (6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p)) ^ 2 / v ^ 3 ≤
          147456 * (1 / ((n : ℝ) ^ 2 * p * (1 - p))) := by
        calc (6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p)) ^ 2 / v ^ 3
            ≤ (6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p)) ^ 2 /
                ((n : ℝ) ^ 4 * p ^ 5 * (1 - p) / 16) ^ 3 :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
                (pow_le_pow_left₀ (by positivity) hv_lo2 3)
          _ = 147456 * (1 / ((n : ℝ) ^ 2 * p * (1 - p))) := by
              field_simp [hp0.ne', hq.ne', (show (n : ℝ) ≠ 0 by positivity)]
              ring
      have h3 := hAB_to_R2 _ hinv1
      calc (6 * (n : ℝ) ^ 5 * p ^ 7 * (1 - p)) ^ 2 / v ^ 3
          ≤ 147456 * (1 / ((n : ℝ) ^ 2 * p * (1 - p))) := h1
        _ ≤ 147456 * (2 * R ^ 2) := mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 294912 * R ^ 2 := by ring
        _ ≤ 302500 * R ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg R)
        _ = (550 * R) ^ 2 := by ring
    have hsqrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hsqrt
  have hsumR : (42 + 320 + 1000 + 550 : ℝ) * R ≤ 2500 * R :=
    mul_le_mul_of_nonneg_right (by norm_num) hR_pos.le
  have htot : (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt vQ + (μ / σ ^ 3) * intD2 ≤
      2500 * R := by linarith
  refine htot.trans_eq ?_
  dsimp only [R, A, B]
  ring

/-- Unified Theorem 3.13 size-bias Wasserstein normal approximation bound for triangle counts in
$G(n, p)$ across all regimes with $n \ge 6$, $0 < p < 1$, and $1 \le n p$
(`SteinIntro.tex:943-944`, `\cite{ruc88}`). -/
theorem triangles_wassersteinDist_le_rucinskiRate {n : ℕ} {p : ℝ}
    (hn : 6 ≤ n) (hp0 : 0 < p) (hp1 : p < 1) (hnp : 1 ≤ (n : ℝ) * p) :
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℝ := ∫ G, T G ∂erdosRenyi n p
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance T (erdosRenyi n p))
    let W : SimpleGraph (Fin n) → ℝ := fun G ↦ (T G - μ) / σ
    wassersteinDist ((erdosRenyi n p).map W) stdNormalLaw ≤
      ENNReal.ofReal
        (2500 / Real.sqrt ((n : ℝ) * p) + 2500 / Real.sqrt ((n : ℝ) ^ 2 * (1 - p))) := by
  intro T μ σ W
  have hn3 : 3 ≤ n := by omega
  have hch_pos : 0 < n.choose 3 := Nat.choose_pos hn3
  obtain ⟨hμ_eq, _⟩ := erdosRenyi_triangles_mean_and_variance hn3 hp0 hp1
  obtain ⟨hv_lo1, hv_lo2⟩ := erdosRenyi_triangles_variance_lower_bounds hn hp0 hp1
  obtain ⟨hch_lo, hch_hi⟩ := choose_three_bounds (by omega : 4 ≤ n)
  have hq : 0 < 1 - p := by linarith
  have hv_pos : 0 < ProbabilityTheory.variance T (erdosRenyi n p) :=
    lt_of_lt_of_le (by positivity) hv_lo1
  have hμ_pos : 0 < μ := by
    dsimp only [μ, T]
    rw [hμ_eq]
    exact mul_pos (Nat.cast_pos.mpr hch_pos) (pow_pos hp0 3)
  have hμ_le : μ ≤ (n : ℝ) ^ 3 * p ^ 3 / 6 := by
    dsimp only [μ, T]
    rw [hμ_eq]
    calc (n.choose 3 : ℝ) * p ^ 3
        ≤ ((n : ℝ) ^ 3 / 6) * p ^ 3 :=
          mul_le_mul_of_nonneg_right hch_hi (pow_nonneg hp0.le 3)
      _ = (n : ℝ) ^ 3 * p ^ 3 / 6 := by ring
  let μG : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
  let unif_pmf : PMF (Fin (n.choose 3)) :=
    @PMF.uniformOfFintype (Fin (n.choose 3)) inferInstance ⟨⟨0, hch_pos⟩⟩
  let unif : Measure (Fin (n.choose 3)) := unif_pmf.toMeasure
  let P : Measure (SimpleGraph (Fin n) × Fin (n.choose 3)) := μG.prod unif
  have hmap_fst : P.map Prod.fst = μG := (measurePreserving_fst (μ := μG) (ν := unif)).map_eq
  let X_Ω : SimpleGraph (Fin n) × Fin (n.choose 3) → ℝ := fun ω ↦ T ω.1
  let Xs : SimpleGraph (Fin n) × Fin (n.choose 3) → ℝ :=
    fun ω ↦ (((ω.1 ⊔ tripleGraph (rucTripleOf ω.2)).cliqueSet 3).ncard : ℝ)
  let Δ : SimpleGraph (Fin n) × Fin (n.choose 3) → ℝ := fun ω ↦ Xs ω - X_Ω ω
  have hSB : IsSizeBias P X_Ω P Xs := triangles_sizeBias_coupling hn3 hp0 hp1.le
  have hXΩ_meas : Measurable X_Ω := (measurable_of_finite T).comp measurable_fst
  have hXΩ_nn : 0 ≤ᵐ[P] X_Ω := Eventually.of_forall fun _ ↦ Nat.cast_nonneg _
  have hXΩ_Lp : MemLp X_Ω 2 P := memLp_of_finite_ruc P X_Ω 2
  have hμ_Ω : ∫ ω, X_Ω ω ∂P = μ := by
    change ∫ ω, T ω.1 ∂P = ∫ G, T G ∂μG
    rw [← hmap_fst]
    exact (integral_map measurable_fst.aemeasurable
      (measurable_of_finite T).aestronglyMeasurable).symm
  have hv_Ω : ProbabilityTheory.variance X_Ω P = ProbabilityTheory.variance T μG := by
    have h := ProbabilityTheory.variance_map (μ := P) (Y := Prod.fst) (X := T)
      (hmap_fst ▸ (measurable_of_finite T).aemeasurable) measurable_fst.aemeasurable
    rw [hmap_fst] at h
    exact h.symm
  have hσ_Ω : Real.sqrt (ProbabilityTheory.variance X_Ω P) = σ := congrArg Real.sqrt hv_Ω
  have hW_map : P.map (fun ω ↦ (X_Ω ω - ∫ ω', X_Ω ω' ∂P) /
      Real.sqrt (ProbabilityTheory.variance X_Ω P)) = μG.map W := by
    rw [hμ_Ω, hσ_Ω, ← hmap_fst, Measure.map_map (measurable_of_finite W) measurable_fst]
    rfl
  have hWass := sizeBias_wassersteinDist_le P stdNormalLaw hXΩ_meas hXΩ_nn hXΩ_Lp
    (hv_Ω.symm ▸ hv_pos) hSB measurable_id.aemeasurable Measure.map_id
  dsimp only at hWass
  rw [hW_map, Measure.map_id, hμ_Ω, hσ_Ω] at hWass
  let Q_X : SimpleGraph (Fin n) × Fin (n.choose 3) → ℝ :=
    P[Δ | MeasurableSpace.comap X_Ω inferInstance]
  have hm_XG : MeasurableSpace.comap X_Ω inferInstance ≤
      MeasurableSpace.comap
        (Prod.fst : SimpleGraph (Fin n) × Fin (n.choose 3) → SimpleGraph (Fin n))
        inferInstance := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨T ⁻¹' s, measurable_of_finite T hs, rfl⟩
  have hevar_mono : ProbabilityTheory.evariance Q_X P ≤
      ProbabilityTheory.evariance
        (P[Δ | MeasurableSpace.comap Prod.fst inferInstance]) P :=
    evariance_condExp_mono P hm_XG measurable_fst.comap_le Integrable.of_finite
  let avgDelta : SimpleGraph (Fin n) → ℝ := fun G ↦
    1 + (-(n.choose 3 : ℝ)⁻¹ * T G +
      (((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹) * ∑ j : Fin (n.choose 3), rucTwoEdgeInd j G)
  have hg_avg : ∀ H : SimpleGraph (Fin n), ∫ i, Δ (H, i) ∂unif = avgDelta H := by
    intro H
    rw [PMF.integral_eq_sum]
    have hunif_toReal : ∀ i : Fin (n.choose 3), (unif_pmf i).toReal = (n.choose 3 : ℝ)⁻¹ :=
      fun _ ↦ by simp [unif_pmf, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    have hN_ne : (n.choose 3 : ℝ) ≠ 0 := (Nat.cast_pos.mpr hch_pos).ne'
    simp_rw [hunif_toReal, smul_eq_mul, ← Finset.mul_sum]
    change (n.choose 3 : ℝ)⁻¹ * (∑ i : Fin (n.choose 3),
        ((((H ⊔ tripleGraph (rucTripleOf i)).cliqueSet 3).ncard : ℝ) -
          ((H.cliqueSet 3).ncard : ℝ))) = avgDelta H
    rw [sum_triangles_sup_tripleGraph_sub hn3 H]
    dsimp only [avgDelta, T]
    field_simp [hN_ne]
    ring
  have hcond_ae : (avgDelta ∘ Prod.fst) =ᵐ[P]
      P[Δ | MeasurableSpace.comap Prod.fst inferInstance] := by
    refine (condExp_fst_prod_finite_ruc μG unif Δ).mp (Eventually.of_forall fun ω hω ↦ ?_)
    exact (hg_avg ω.1).symm.trans hω
  have hQ_Lp : MemLp Q_X 2 P := memLp_of_finite_ruc P Q_X 2
  have hvar_avg : ProbabilityTheory.variance avgDelta μG ≤
      2 * (24 / (n : ℝ) ^ 3) ^ 2 * ProbabilityTheory.variance T μG +
        5760 * p ^ 3 * (1 - p) := by
    have hshift_avg : avgDelta = fun G ↦
        (-(n.choose 3 : ℝ)⁻¹ * T G +
          (((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹) *
            ∑ j : Fin (n.choose 3), rucTwoEdgeInd j G) + 1 :=
      funext fun _ ↦ add_comm _ _
    rw [hshift_avg,
      ProbabilityTheory.variance_add_const Measurable.of_discrete.aestronglyMeasurable]
    have hsplit := variance_fun_add_le_ruc μG
      (memLp_of_finite_ruc μG (fun G ↦ -(n.choose 3 : ℝ)⁻¹ * T G) 2)
      (memLp_of_finite_ruc μG
        (fun G ↦ (((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹) * ∑ j, rucTwoEdgeInd j G) 2)
    have hv1 : ProbabilityTheory.variance (fun G ↦ -(n.choose 3 : ℝ)⁻¹ * T G) μG ≤
        (24 / (n : ℝ) ^ 3) ^ 2 * ProbabilityTheory.variance T μG := by
      rw [ProbabilityTheory.variance_const_mul]
      have hinv_le : (n.choose 3 : ℝ)⁻¹ ≤ 24 / (n : ℝ) ^ 3 := by
        have hn3_pos : 0 < (n : ℝ) ^ 3 / 24 := by positivity
        have := one_div_le_one_div_of_le hn3_pos hch_lo
        simpa [one_div_div] using this
      have hsq : (-(n.choose 3 : ℝ)⁻¹) ^ 2 ≤ (24 / (n : ℝ) ^ 3) ^ 2 := by
        rw [neg_sq]
        exact pow_le_pow_left₀ (by positivity) hinv_le 2
      exact mul_le_mul_of_nonneg_right hsq (ProbabilityTheory.variance_nonneg T μG)
    have hv2 : ProbabilityTheory.variance
          (fun G ↦ (((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹) * ∑ j, rucTwoEdgeInd j G) μG ≤
        2880 * p ^ 3 * (1 - p) := by
      rw [ProbabilityTheory.variance_const_mul]
      have hn_cast : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hcoef_nn : 0 ≤ ((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹ :=
        mul_nonneg (by linarith) (by positivity)
      have hcoef_le : ((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹ ≤ 24 / (n : ℝ) ^ 2 := by
        have hinv_le : (n.choose 3 : ℝ)⁻¹ ≤ 24 / (n : ℝ) ^ 3 := by
          have := one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) ^ 3 / 24) hch_lo
          simpa [one_div_div] using this
        calc ((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹
            ≤ (n : ℝ) * (24 / (n : ℝ) ^ 3) :=
              mul_le_mul (by linarith) hinv_le (by positivity) (by positivity)
          _ = 24 / (n : ℝ) ^ 2 := by
              field_simp [(show (n : ℝ) ≠ 0 by positivity)]
      have hvarZ := variance_rucTwoEdgeSum_le hn3 hp0.le hp1.le
      have hvarZ_le : ProbabilityTheory.variance
            (fun G ↦ ∑ j : Fin (n.choose 3), rucTwoEdgeInd j G) μG ≤
          5 * (n : ℝ) ^ 4 * p ^ 3 * (1 - p) := by
        calc ProbabilityTheory.variance
                (fun G ↦ ∑ j : Fin (n.choose 3), rucTwoEdgeInd j G) μG
            ≤ (n.choose 3 : ℝ) * p ^ 2 * (1 - p) * (3 + 27 * (n : ℝ) * p) := hvarZ
          _ ≤ ((n : ℝ) ^ 3 / 6) * p ^ 2 * (1 - p) * (30 * (n : ℝ) * p) :=
              mul_le_mul
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hch_hi (sq_nonneg p)) hq.le)
                (by linarith)
                (by positivity)
                (by positivity)
          _ = 5 * (n : ℝ) ^ 4 * p ^ 3 * (1 - p) := by ring
      calc (((n : ℝ) - 3) * (n.choose 3 : ℝ)⁻¹) ^ 2 *
              ProbabilityTheory.variance (fun G ↦ ∑ j, rucTwoEdgeInd j G) μG
          ≤ (24 / (n : ℝ) ^ 2) ^ 2 * (5 * (n : ℝ) ^ 4 * p ^ 3 * (1 - p)) :=
            mul_le_mul (pow_le_pow_left₀ hcoef_nn hcoef_le 2) hvarZ_le
              (ProbabilityTheory.variance_nonneg _ μG) (by positivity)
        _ = 2880 * p ^ 3 * (1 - p) := by
            field_simp [(show (n : ℝ) ≠ 0 by positivity)]
            ring
    linarith
  have hvar_QX : ProbabilityTheory.variance Q_X P ≤
      2 * (24 / (n : ℝ) ^ 3) ^ 2 * ProbabilityTheory.variance T μG +
        5760 * p ^ 3 * (1 - p) := by
    have hg_map : ProbabilityTheory.variance (avgDelta ∘ Prod.fst) P =
        ProbabilityTheory.variance avgDelta μG := by
      have h := ProbabilityTheory.variance_map (μ := P) (Y := Prod.fst) (X := avgDelta)
        (hmap_fst ▸ (measurable_of_finite avgDelta).aemeasurable) measurable_fst.aemeasurable
      rw [hmap_fst] at h
      exact h.symm
    have hev_le : ProbabilityTheory.evariance Q_X P ≤
        ENNReal.ofReal (2 * (24 / (n : ℝ) ^ 3) ^ 2 * ProbabilityTheory.variance T μG +
          5760 * p ^ 3 * (1 - p)) := calc
      ProbabilityTheory.evariance Q_X P
        ≤ ProbabilityTheory.evariance
            (P[Δ | MeasurableSpace.comap Prod.fst inferInstance]) P := hevar_mono
      _ = ProbabilityTheory.evariance (avgDelta ∘ Prod.fst) P :=
          ProbabilityTheory.evariance_congr hcond_ae.symm
      _ = ENNReal.ofReal (ProbabilityTheory.variance (avgDelta ∘ Prod.fst) P) :=
          (ProbabilityTheory.ofReal_variance
            (memLp_of_finite_ruc P (avgDelta ∘ Prod.fst) 2)).symm
      _ ≤ ENNReal.ofReal (2 * (24 / (n : ℝ) ^ 3) ^ 2 * ProbabilityTheory.variance T μG +
            5760 * p ^ 3 * (1 - p)) :=
          ENNReal.ofReal_le_ofReal (hg_map ▸ hvar_avg)
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ProbabilityTheory.ofReal_variance hQ_Lp]
    exact hev_le
  have hΔ2_int_le : ∫ ω, Δ ω ^ 2 ∂P ≤ 36 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4) := by
    rw [integral_prod_symm _ (Integrable.of_finite : Integrable (fun ω ↦ Δ ω ^ 2) P)]
    calc ∫ i, (∫ H, Δ (H, i) ^ 2 ∂μG) ∂unif
        ≤ ∫ _, 36 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4) ∂unif :=
          integral_mono_ae Integrable.of_finite (integrable_const _)
            (Eventually.of_forall fun i ↦ delta_slice_sq_integral_le hn3 hp0.le hp1.le i)
      _ = 36 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4) := by simp [integral_const, probReal_univ]
  have hevar_rpow : ProbabilityTheory.evariance Q_X P ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q_X P)) := by
    rw [← ProbabilityTheory.ofReal_variance hQ_Lp,
      ENNReal.ofReal_rpow_of_nonneg (ProbabilityTheory.variance_nonneg Q_X P) (by positivity),
      ← Real.sqrt_eq_rpow]
  have hlintegral_Δ2 : (∫⁻ ω, ENNReal.ofReal (Δ ω ^ 2) ∂P) =
      ENNReal.ofReal (∫ ω, Δ ω ^ 2 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (Eventually.of_forall fun _ ↦ sq_nonneg _)).symm
  have hInt_nn : 0 ≤ ∫ ω, Δ ω ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  have hreal := combine_rucinski_stein_bounds hn hp0 hp1 hnp hμ_pos hμ_le hv_lo1 hv_lo2
    (ProbabilityTheory.variance_nonneg Q_X P) hvar_QX hInt_nn hΔ2_int_le
  have hC1_nn : 0 ≤ μ / σ ^ 2 * Real.sqrt (2 / Real.pi) := by positivity
  have hC2_nn : 0 ≤ μ / σ ^ 3 := by positivity
  calc wassersteinDist (μG.map W) stdNormalLaw
      ≤ ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) *
            ProbabilityTheory.evariance Q_X P ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (μ / σ ^ 3) * ∫⁻ ω, ENNReal.ofReal (Δ ω ^ 2) ∂P := hWass
    _ = ENNReal.ofReal
          ((μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt (ProbabilityTheory.variance Q_X P) +
            (μ / σ ^ 3) * (∫ ω, Δ ω ^ 2 ∂P)) := by
        rw [hevar_rpow, hlintegral_Δ2, ← ENNReal.ofReal_mul hC1_nn, ← ENNReal.ofReal_mul hC2_nn,
          ← ENNReal.ofReal_add (mul_nonneg hC1_nn (Real.sqrt_nonneg _)) (mul_nonneg hC2_nn hInt_nn)]
    _ ≤ ENNReal.ofReal
          (2500 / Real.sqrt ((n : ℝ) * p) + 2500 / Real.sqrt ((n : ℝ) ^ 2 * (1 - p))) :=
        ENNReal.ofReal_le_ofReal hreal

/-- Sufficiency direction of Ruciński's triangle CLT criterion (`SteinIntro.tex:943-944`,
`\cite{ruc88}`): if $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$, then
$d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1)) \to 0$. -/
theorem tendsto_triangles_wassersteinDist_zero_of_rucinski {p : ℕ → ℝ}
    (_hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1)
    (hnp : Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop)
    (hn2q : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop) :
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    Tendsto (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
      atTop (nhds 0) := by
  intro T μ σ W
  let rate : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal
    (2500 / Real.sqrt ((n : ℝ) * p n) + 2500 / Real.sqrt ((n : ℝ) ^ 2 * (1 - p n)))
  have hrate_zero : Tendsto rate atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ 2500 / Real.sqrt ((n : ℝ) * p n)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hnp)
    have h2 : Tendsto (fun n : ℕ ↦ 2500 / Real.sqrt ((n : ℝ) ^ 2 * (1 - p n))) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hn2q)
    have hsum : Tendsto
        (fun n : ℕ ↦ 2500 / Real.sqrt ((n : ℝ) * p n) +
          2500 / Real.sqrt ((n : ℝ) ^ 2 * (1 - p n))) atTop (nhds 0) := by
      simpa using h1.add h2
    simpa [rate] using ENNReal.tendsto_ofReal hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate_zero
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop 6, hnp.eventually (eventually_ge_atTop 1),
    hn2q.eventually (eventually_gt_atTop 0)] with n hn6 hnp1 hn2q_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hp0 : 0 < p n := pos_of_mul_pos_right (by linarith : 0 < (n : ℝ) * p n) hn_pos.le
  have hq0 : 0 < 1 - p n := pos_of_mul_pos_right hn2q_pos (sq_nonneg (n : ℝ))
  exact triangles_wassersteinDist_le_rucinskiRate hn6 hp0 (by linarith) hnp1

end SteinMethod
