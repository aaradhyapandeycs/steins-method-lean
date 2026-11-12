/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Poisson.SteinBounds
import Formalization.PoissonExch.AuxLawSmallNumbers

/-!
# SWEEP-D Section 4.4 Library Proofs (`Formalization.Sweep.SweepDPoissonExch`)

Proves `ex4_20_direct_eq161` (`Ex4_20_direct_eq161`, `SteinIntro.tex:2678-2679`;
`docs/reviews/stmts-review-SWEEP-D.md` `D-D4` / `SD-5`): in the replace-one exchangeable-pair
coupling of Example 4.20 with $\mathcal{F} = \sigma(X_1, \dots, X_n)$ and $c = n$, both
conditional-jump discrepancy coefficients in equation `(4.15)` (`\label{161}`) equal
$\sum_{i=1}^n p_i X_i$ almost surely, collapsing the right-hand side of `(4.15)` to
$\mathbb{E}[(\sum_{i=1}^n p_i X_i) \Delta f(W)]$ so that bounding its absolute value directly via
$\|\Delta f\| \le \min\{1, \lambda^{-1}\}$ recovers the size-biasing bound
$\min\{1, \lambda^{-1}\} \sum_{i=1}^n p_i^2 < 2 \min\{1, \lambda^{-1/2}\} \sum_{i=1}^n p_i^2$.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SteinMethod

private lemma min_one_inv_lt_two_mul_min_one_rpow {r : ℝ≥0} (hr : 0 < r) :
    min 1 (r : ℝ)⁻¹ < 2 * min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  rcases le_or_gt (r : ℝ) 1 with hle | hgt
  · have hinv : 1 ≤ (r : ℝ)⁻¹ := one_le_inv₀ hr_pos |>.mpr hle
    have hrpow : 1 ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr_pos hle (by norm_num)
    rw [min_eq_left hinv, min_eq_left hrpow]
    norm_num
  · have hinv_lt : (r : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
    have hrpow_lt : (r : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hgt (by norm_num)
    have hrpow_pos : 0 < (r : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr_pos _
    have hlt_exp : (r : ℝ)⁻¹ < (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_neg_one (r : ℝ)]
      exact Real.rpow_lt_rpow_of_exponent_lt hgt (by norm_num)
    rw [min_eq_right hinv_lt.le, min_eq_right hrpow_lt.le]
    linarith

/-- Example 4.20 direct bound of eq. `(4.15)` (`\label{161}`, `SteinIntro.tex:2678-2679`;
`docs/reviews/stmts-review-SWEEP-D.md` `D-D4` / `SD-5`). -/
theorem ex4_20_direct_eq161
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    {X X' : Fin n → Ω → ℕ} {p : Fin n → ℝ} {I : Ω → Fin n} {r : ℝ≥0}
    (hval : ∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1)
    (hm : ∀ i, Measurable (X i))
    (hm' : ∀ i, Measurable (X' i))
    (hp : ∀ i, P.real {ω | X i ω = 1} = p i)
    (hind : ProbabilityTheory.iIndepFun X P)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (hr : 0 < r)
    (hr_eq : (r : ℝ) = ∑ i : Fin n, p i) :
    let _ : MeasurableSpace Ω := mΩ
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let W' : Ω → ℕ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    (∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, (((r : ℝ) - (n : ℝ) *
            condExpAt (MeasurableSpace.comap (fun ω' i ↦ X i ω') inferInstance) mΩ P
              ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω + 1) -
          ((W ω : ℝ) - (n : ℝ) *
            condExpAt (MeasurableSpace.comap (fun ω' i ↦ X i ω') inferInstance) mΩ P
              ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω)) ∂P =
        ∫ ω, (∑ i : Fin n, p i * (X i ω : ℝ)) * fwdDiff 1 f (W ω) ∂P) ∧
    (∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      (∀ k : ℕ, |fwdDiff 1 f k| ≤ min 1 (r : ℝ)⁻¹) →
        |∫ ω, poissonSteinOp r f (W ω) ∂P| ≤
          min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2) ∧
    min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2 <
      2 * min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) * ∑ i : Fin n, p i ^ 2 := by
  let _ : MeasurableSpace Ω := mΩ
  let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
  let W' : Ω → ℕ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
  dsimp only
  obtain ⟨hExch, hCond_up, hCond_down⟩ :=
    bernoulli_replaceOne_coupling P hn hval hm hm' hp hind hId hXX'_indep hI_meas hI_indep hI_unif
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let VX : Ω → Fin n → ℕ := fun ω i ↦ X i ω
  have hVX_meas : Measurable VX := .of_eval hm
  have hFle : MeasurableSpace.comap VX inferInstance ≤ mΩ := hVX_meas.comap_le
  have hW_meas : Measurable W := Finset.measurable_sum Finset.univ fun i _ ↦ hm i
  have hW'_meas : Measurable W' := by
    have hX_I : Measurable (fun ω ↦ X (I ω) ω) := by
      have heq : (fun ω ↦ X (I ω) ω) = fun ω ↦ ∑ i : Fin n, if I ω = i then X i ω else 0 := by
        funext ω; simp
      rw [heq]
      refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
      have hset : {ω : Ω | I ω = i} = I ⁻¹' {i} := by ext ω; simp
      exact Measurable.ite (hset ▸ hI_meas (measurableSet_singleton i)) (hm i) measurable_const
    have hX'_I : Measurable (fun ω ↦ X' (I ω) ω) := by
      have heq : (fun ω ↦ X' (I ω) ω) = fun ω ↦ ∑ i : Fin n, if I ω = i then X' i ω else 0 := by
        funext ω; simp
      rw [heq]
      refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
      have hset : {ω : Ω | I ω = i} = I ⁻¹' {i} := by ext ω; simp
      exact Measurable.ite (hset ▸ hI_meas (measurableSet_singleton i)) (hm' i) measurable_const
    exact (hW_meas.sub hX_I).add hX'_I
  have hWF : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap VX inferInstance := by
    have hsum_meas : Measurable (fun v : Fin n → ℕ ↦ ∑ i : Fin n, v i) :=
      Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i
    have hcomp : W = (fun v : Fin n → ℕ ↦ ∑ i : Fin n, v i) ∘ VX := rfl
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hsum_meas.comap_le
  have hp_nn : ∀ i : Fin n, 0 ≤ p i := fun i ↦ hp i ▸ measureReal_nonneg
  have hX_int : ∀ i : Fin n,
      Integrable (fun ω ↦ (X i ω : ℝ)) P ∧ ∫ ω, (X i ω : ℝ) ∂P = p i := by
    intro i
    have hset : MeasurableSet {ω : Ω | X i ω = 1} := hm i (measurableSet_singleton 1)
    have hind_eq : (fun ω ↦ (X i ω : ℝ)) = {ω : Ω | X i ω = 1}.indicator (1 : Ω → ℝ) := by
      funext ω
      rcases hval i ω with h0 | h1
      · simp [h0]
      · simp [h1]
    rw [hind_eq]
    exact ⟨(integrable_const (1 : ℝ)).indicator hset,
      (integral_indicator_one hset).trans (hp i)⟩
  have hIntW : Integrable (fun ω ↦ (W ω : ℝ)) P := by
    have heq : (fun ω ↦ (W ω : ℝ)) = fun ω ↦ ∑ i : Fin n, (X i ω : ℝ) := by
      funext ω; simp [W]
    rw [heq]
    exact integrable_finsetSum Finset.univ fun i _ ↦ (hX_int i).1
  let S_pX : Ω → ℝ := fun ω ↦ ∑ i : Fin n, p i * (X i ω : ℝ)
  have hS_pX_nn : ∀ ω, 0 ≤ S_pX ω := fun ω ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nn i) (Nat.cast_nonneg _)
  have hS_pX_int : Integrable S_pX P :=
    integrable_finsetSum Finset.univ fun i _ ↦ ((hX_int i).1).const_mul (p i)
  have hS_pX_mean : ∫ ω, S_pX ω ∂P = ∑ i : Fin n, p i ^ 2 := by
    dsimp [S_pX]
    rw [integral_finsetSum Finset.univ fun i _ ↦ ((hX_int i).1).const_mul (p i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, (hX_int i).2, sq]
  have h_id_fn : ∀ f : ℕ → ℝ,
      (∫ ω, (((r : ℝ) - (n : ℝ) *
            condExpAt (MeasurableSpace.comap VX inferInstance) mΩ P
              ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω + 1) -
          ((W ω : ℝ) - (n : ℝ) *
            condExpAt (MeasurableSpace.comap VX inferInstance) mΩ P
              ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω)) ∂P) =
        ∫ ω, S_pX ω * fwdDiff 1 f (W ω) ∂P := by
    intro f
    refine integral_congr_ae ?_
    filter_upwards [hCond_up, hCond_down] with ω hup hdn
    change (((r : ℝ) - (n : ℝ) *
          P[{ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ) |
            MeasurableSpace.comap VX inferInstance] ω) * f (W ω + 1) -
        ((W ω : ℝ) - (n : ℝ) *
          P[{ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ) |
            MeasurableSpace.comap VX inferInstance] ω) * f (W ω)) =
      S_pX ω * fwdDiff 1 f (W ω)
    rw [hup, hdn, hr_eq, show (W ω : ℝ) = ∑ i : Fin n, (X i ω : ℝ) from
      Nat.cast_sum Finset.univ fun i ↦ X i ω]
    have h1 :
        (∑ i : Fin n, p i) -
            (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (1 - (X i ω : ℝ)) * p i) =
          S_pX ω := by
      have hmul : (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (1 - (X i ω : ℝ)) * p i) =
          ∑ i : Fin n, (1 - (X i ω : ℝ)) * p i := by field_simp [hn_ne]
      rw [hmul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have h2 :
        (∑ i : Fin n, (X i ω : ℝ)) -
            (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (X i ω : ℝ) * (1 - p i)) =
          S_pX ω := by
      have hmul : (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (X i ω : ℝ) * (1 - p i)) =
          ∑ i : Fin n, (X i ω : ℝ) * (1 - p i) := by field_simp [hn_ne]
      rw [hmul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [h1, h2]
    simp only [fwdDiff]
    ring
  refine ⟨fun f _ ↦ h_id_fn f, ?_, ?_⟩
  · intro f hf_bdd hf_diff
    have hid := integral_poissonSteinOp_exchangeable_eq P hr hW_meas hW'_meas hExch hIntW
      hFle hWF f hf_bdd (n : ℝ)
    rw [hid, h_id_fn f]
    set M : ℝ := min 1 (r : ℝ)⁻¹
    have hdf_meas : AEStronglyMeasurable (fun ω ↦ fwdDiff 1 f (W ω)) P :=
      ((Measurable.of_discrete (f := fwdDiff 1 f)).comp hW_meas).aestronglyMeasurable
    have hprod_int : Integrable (fun ω ↦ S_pX ω * fwdDiff 1 f (W ω)) P := by
      refine Integrable.mono' (hS_pX_int.mul_const M)
        (hS_pX_int.aestronglyMeasurable.mul hdf_meas)
        (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hS_pX_nn ω)]
      exact mul_le_mul_of_nonneg_left (hf_diff (W ω)) (hS_pX_nn ω)
    calc |∫ ω, S_pX ω * fwdDiff 1 f (W ω) ∂P|
      _ ≤ ∫ ω, |S_pX ω * fwdDiff 1 f (W ω)| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, M * S_pX ω ∂P := by
        refine integral_mono_ae hprod_int.abs (hS_pX_int.const_mul M)
          (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        rw [abs_mul, abs_of_nonneg (hS_pX_nn ω), mul_comm M]
        exact mul_le_mul_of_nonneg_left (hf_diff (W ω)) (hS_pX_nn ω)
      _ = M * ∑ i : Fin n, p i ^ 2 := by rw [integral_const_mul, hS_pX_mean]
  · have hr_pos : (0 : ℝ) < ∑ i : Fin n, p i := hr_eq ▸ NNReal.coe_pos.mpr hr
    have hex_pos : ∃ i₀ : Fin n, 0 < p i₀ := by
      by_contra h_all
      push Not at h_all
      have hle0 : (∑ i : Fin n, p i) ≤ 0 := Finset.sum_nonpos fun i _ ↦ h_all i
      linarith
    rcases hex_pos with ⟨i₀, hi₀⟩
    have hsq_pos : 0 < ∑ i : Fin n, p i ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_pos hi₀)
        (Finset.single_le_sum (fun i _ ↦ sq_nonneg (p i)) (Finset.mem_univ i₀))
    exact mul_lt_mul_of_pos_right (min_one_inv_lt_two_mul_min_one_rpow hr) hsq_pos

end SteinMethod
