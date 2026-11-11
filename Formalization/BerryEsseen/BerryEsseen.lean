/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.BerryEsseen.CharFunBounds
import Formalization.BerryEsseen.FejerSmoothing
import Formalization.Defs.Metrics

/-!
# Berry–Esseen Theorem with Constant `1.88` (`Formalization.BerryEsseen.BerryEsseen`)

Proves **Theorem 1.1** (`\label{thm1}`, `SteinIntro.tex:351-357`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`) from scratch (Roadmap Milestone M10):
for independent and identically distributed mean-zero, unit-variance random variables
$X_1, \dots, X_n \in L^3(P)$ ($n \ge 1$) and $W_n = \frac{1}{\sqrt{n}} \sum_{i=1}^n X_i$,
$$
  \left|\mathbb{P}(W_n \le x) - \Phi(x)\right|
    \le \frac{1.88 \, \mathbb{E}|X_1|^3}{\sqrt{n}}
  \qquad \forall x \in \mathbb{R},
$$
together with the corresponding `kolmogorovDist` formulation.

## Proof Architecture
Splits at the dimensionless Lyapunov ratio $\beta = \mathbb{E}|X_0|^3 / \sqrt{n}$:
* **Large-$\beta$ regime ($\beta \ge 3 / 10$)**: Closed-tail Cantelli–Normal bound
  $|F_{W_n}(x) - \Phi(x)| \le \frac{11}{20} = 0.55 < 0.564 = 1.88 \times \frac{3}{10} \le 1.88\beta$
  (`abs_measureReal_Iic_sub_stdNormalCDF_le` in `Cantelli.lean`).
* **Small-$\beta$ regime ($\beta < 3 / 10$, forcing $n \ge 12$)**: Refined Esseen–Fejér
  de-smoothing (`esseen_fejer_smoothing` in `FejerSmoothing.lean`) at $T = \frac{7}{5\beta}$ and
  $R = \frac{16}{5}$, combined with the degree-8 Fejér mass bound
  (`setIntegral_Ioo_fejerKernel_ge` in `FejerKernel.lean`) and characteristic-function Gaussian
  dominating integral at $a = \frac{11}{45}$ (`integral_charFun_standardizedSum_diff_le` in
  `CharFunBounds.lean`), yielding total constant $< 1.795 < 1.88$.
-/

open Complex MeasureTheory ProbabilityTheory Set
open scoped ENNReal Real

namespace SteinMethod.BerryEsseen

/-! ### Section 1: Numerical Constant Verification (`< 1.795 < 1.88`) -/

private theorem small_beta_constant_le {α : ℝ}
    (hα : (422368336 / 172265625 : ℝ) / π ≤ α) :
    let a : ℝ := 11 / 45
    1 / (2 * α - 1) * (1 / π * (√π / (24 * a * √a) + 3 / (160 * a ^ 2))) +
      α / (2 * α - 1) * ((16 / 7 : ℝ) / √(2 * π)) ≤ 1.88 := by
  intro a
  have hpi_gt : (31415 / 10000 : ℝ) < π := by linarith [Real.pi_gt_d4]
  have hpi_lt : π < (31416 / 10000 : ℝ) := by linarith [Real.pi_lt_d4]
  have hα_low : (1951 / 2500 : ℝ) ≤ α := by
    have h1 : (422368336 / 172265625 : ℝ) / (31416 / 10000) ≤
        (422368336 / 172265625 : ℝ) / π :=
      div_le_div_of_nonneg_left (by norm_num) Real.pi_pos hpi_lt.le
    have h2 : (1951 / 2500 : ℝ) ≤ (422368336 / 172265625 : ℝ) / (31416 / 10000) := by norm_num
    exact (h2.trans h1).trans hα
  have h2α_pos : 0 < 2 * α - 1 := by linarith
  have hc1 : 1 / (2 * α - 1) ≤ 1250 / 701 := by
    rw [div_le_div_iff₀ h2α_pos (by norm_num)]; linarith
  have hc2 : α / (2 * α - 1) ≤ 1951 / 1402 := by
    rw [div_le_div_iff₀ h2α_pos (by norm_num)]; linarith
  have hinv_pi : 1 / π ≤ 2000 / 6283 := by
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]; linarith
  have hsqrt_pi : √π ≤ 1773 / 1000 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by linarith)
  have hsqrt_a : 494 / 1000 ≤ √a :=
    Real.le_sqrt_of_sq_le (by norm_num [a])
  have hsqrt_2pi : 2506 / 1000 ≤ √(2 * π) :=
    Real.le_sqrt_of_sq_le (by linarith)
  have ha_pos : 0 < a := by norm_num [a]
  have ht1 : √π / (24 * a * √a) ≤ (1773 / 1000) / (24 * a * (494 / 1000)) := by
    refine div_le_div₀ (by norm_num) hsqrt_pi (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hsqrt_a (by positivity)
  have hI : √π / (24 * a * √a) + 3 / (160 * a ^ 2) ≤
      (1773 / 1000) / (24 * a * (494 / 1000)) + 3 / (160 * a ^ 2) := by
    linarith
  have hB : 1 / π * (√π / (24 * a * √a) + 3 / (160 * a ^ 2)) ≤
      (2000 / 6283) * ((1773 / 1000) / (24 * a * (494 / 1000)) + 3 / (160 * a ^ 2)) :=
    mul_le_mul hinv_pi hI (by positivity) (by norm_num)
  have hterm1 : 1 / (2 * α - 1) * (1 / π * (√π / (24 * a * √a) + 3 / (160 * a ^ 2))) ≤
      (1250 / 701) * ((2000 / 6283) *
        ((1773 / 1000) / (24 * a * (494 / 1000)) + 3 / (160 * a ^ 2))) :=
    mul_le_mul hc1 hB (by positivity) (by norm_num)
  have hrad : (16 / 7 : ℝ) / √(2 * π) ≤ (16 / 7 : ℝ) / (2506 / 1000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrt_2pi
  have hterm2 : α / (2 * α - 1) * ((16 / 7 : ℝ) / √(2 * π)) ≤
      (1951 / 1402) * ((16 / 7 : ℝ) / (2506 / 1000)) :=
    mul_le_mul hc2 hrad (by positivity) (by norm_num)
  have hnum : (1250 / 701 : ℝ) * ((2000 / 6283) *
        ((1773 / 1000) / (24 * a * (494 / 1000)) + 3 / (160 * a ^ 2))) +
      (1951 / 1402) * ((16 / 7 : ℝ) / (2506 / 1000)) ≤ 1.88 := by
    norm_num [a]
  linarith

/-! ### Section 2: Main Berry–Esseen Theorem (`Theorem 1.1`) -/

/-- **Theorem 1.1** (`\label{thm1}`, `SteinIntro.tex:351-357`):
Berry–Esseen bound with constant `1.88` for standardized sums of i.i.d. mean-zero, unit-variance
$L^3$ random variables. -/
theorem berry_esseen_iid
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {n : ℕ} (x : ℝ)
    (hn : 0 < n)
    (hXm : ∀ i : ℕ, AEMeasurable (X i) P)
    (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX3 : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hvar : variance (X 0) P = 1) :
    let W_n : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / √n
    |P.real {ω | W_n ω ≤ x} - stdNormalCDF x| ≤
      1.88 * (∫ ω, |X 0 ω| ^ 3 ∂P) / √n := by
  intro W_n
  obtain ⟨hWm, hW_prob, hW_int1, hW_int2, hW_m1, hW_m2⟩ :=
    standardizedSum_moments P hn hXm hindep hident hX3 hmean hvar
  let μ : Measure ℝ := P.map W_n
  have : IsProbabilityMeasure μ := hW_prob
  have hmap_cdf : P.real {ω | W_n ω ≤ x} = μ.real (Iic x) := by
    simp only [μ, measureReal_def]
    rw [Measure.map_apply_of_aemeasurable hWm measurableSet_Iic]
    rfl
  rw [hmap_cdf]
  set ρ : ℝ := ∫ ω, |X 0 ω| ^ 3 ∂P
  set β : ℝ := ρ / √n
  have hρ1 : 1 ≤ ρ := one_le_integral_abs_cube hX3 hmean hvar
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqn_pos : 0 < √n := Real.sqrt_pos.mpr hn_pos
  have hβ_pos : 0 < β := div_pos (by linarith) hsqn_pos
  have hrhs_eq : 1.88 * ρ / √n = 1.88 * β := by simp only [β]; ring
  rw [hrhs_eq]
  rcases le_or_gt (3 / 10 : ℝ) β with hβ_ge | hβ_lt
  · have hcant := abs_measureReal_Iic_sub_stdNormalCDF_le hW_int1 hW_int2 hW_m1 hW_m2 x
    linarith
  · let T : ℝ := 7 / (5 * β)
    have hT_pos : 0 < T := by positivity
    let r : ℝ := 16 / 5 / T
    let α : ℝ := ∫ y in Ioo (-r) r, fejerKernel T y
    have hα_ge : (422368336 / 172265625 : ℝ) / π ≤ α := setIntegral_Ioo_fejerKernel_ge hT_pos
    have h2α_pos : 0 < 2 * α - 1 := by
      have hpi4 : π < 4 := Real.pi_lt_four
      have h1' : (422368336 / 172265625 : ℝ) / 4 < (422368336 / 172265625 : ℝ) / π :=
        div_lt_div_of_pos_left (by norm_num) Real.pi_pos hpi4
      linarith
    have hsm : |cdfDiff μ x| ≤
        1 / (2 * α - 1) * (1 / π * ∫ t in Ioc 0 T,
          (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t)) +
        α / (2 * α - 1) * (r / √(2 * π)) :=
      esseen_fejer_smoothing hW_int1 hT_pos x
    let a : ℝ := 11 / 45
    have hcf_int : ∫ t in Ioc 0 T,
        (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t) ≤
        β * (√π / (24 * a * √a) + 3 / (160 * a ^ 2)) :=
      integral_charFun_standardizedSum_diff_le P hn hindep hident hX3 hmean hvar hβ_lt
    have hr_eq : r = (16 / 7 : ℝ) * β := by
      simp only [r, T]
      field_simp
    have hstep1 : 1 / (2 * α - 1) * (1 / π * ∫ t in Ioc 0 T,
          (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t)) +
        α / (2 * α - 1) * (r / √(2 * π)) ≤
        (1 / (2 * α - 1) * (1 / π * (√π / (24 * a * √a) + 3 / (160 * a ^ 2))) +
          α / (2 * α - 1) * ((16 / 7 : ℝ) / √(2 * π))) * β := by
      have hm1 : 1 / (2 * α - 1) * (1 / π * ∫ t in Ioc 0 T,
            (1 - t / T) * (‖charFun μ t - cexp (-(t : ℂ) ^ 2 / 2)‖ / t)) ≤
          1 / (2 * α - 1) * (1 / π * (β * (√π / (24 * a * √a) + 3 / (160 * a ^ 2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcf_int (by positivity))
          (by positivity)
      refine (add_le_add hm1 (le_refl _)).trans_eq ?_
      rw [hr_eq]
      ring
    have hconst : 1 / (2 * α - 1) * (1 / π * (√π / (24 * a * √a) + 3 / (160 * a ^ 2))) +
        α / (2 * α - 1) * ((16 / 7 : ℝ) / √(2 * π)) ≤ 1.88 :=
      small_beta_constant_le hα_ge
    have hstep2 : (1 / (2 * α - 1) * (1 / π * (√π / (24 * a * √a) + 3 / (160 * a ^ 2))) +
          α / (2 * α - 1) * ((16 / 7 : ℝ) / √(2 * π))) * β ≤ 1.88 * β :=
      mul_le_mul_of_nonneg_right hconst hβ_pos.le
    change |cdfDiff μ x| ≤ 1.88 * β
    exact (hsm.trans hstep1).trans hstep2

/-- `kolmogorovDist` corollary of **Theorem 1.1** (`\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem kolmogorovDist_berry_esseen_iid
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {n : ℕ}
    (hn : 0 < n)
    (hXm : ∀ i : ℕ, AEMeasurable (X i) P)
    (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX3 : MemLp (X 0) 3 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hvar : variance (X 0) P = 1) :
    let W_n : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / √n
    kolmogorovDist (P.map W_n) stdNormalLaw ≤
      ENNReal.ofReal (1.88 * (∫ ω, |X 0 ω| ^ 3 ∂P) / √n) := by
  intro W_n
  have hWm : AEMeasurable W_n P :=
    (Finset.aemeasurable_fun_sum _ fun i _ ↦ hXm i).div_const _
  unfold kolmogorovDist ipm
  refine iSup₂_le fun h hh ↦ iSup_le fun _ ↦ ?_
  rcases hh with ⟨x, rfl⟩
  rw [integral_indicator_one measurableSet_Iic,
    show ∫ y, (Iic x).indicator (1 : ℝ → ℝ) y ∂stdNormalLaw = stdNormalCDF x from
      stdNormalExpect_indicator_Iic x]
  have hmap_cdf : (P.map W_n).real (Iic x) = P.real {ω | W_n ω ≤ x} := by
    simp only [measureReal_def, Measure.map_apply_of_aemeasurable hWm measurableSet_Iic]
    rfl
  rw [hmap_cdf]
  exact ENNReal.ofReal_le_ofReal
    (berry_esseen_iid P x hn hXm hindep hident hX3 hmean hvar)

end SteinMethod.BerryEsseen
