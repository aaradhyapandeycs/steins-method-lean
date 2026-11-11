/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.IndependentSums
import Formalization.Normal.WassersteinBound
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Helper Kernel Bounds for Example 3.6 (`Formalization.Leftovers.Ex36SmallNHelper`)

Rational constant bounds, summand moment inequalities, and exact rational SOS/Bernstein/Taylor
polynomial certificates for the leave-one-out Stein kernel in Example 3.6 (`n ≥ 2`) of
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:1053-1097`;
`ISSUE-3.6`, Backlog Item 3).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SteinMethod.Ex36SmallN

/-! ### Section 1: Rational Constant Bounds and Summand Moment Inequalities -/

theorem sqrt_two_div_pi_gt : (7978 : ℝ) / 10000 < Real.sqrt (2 / Real.pi) := by
  rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ Real.pi_pos]
  linarith [Real.pi_lt_d4]

theorem sqrt_two_div_pi_lt : Real.sqrt (2 / Real.pi) < (7979 : ℝ) / 10000 := by
  rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ Real.pi_pos]
  linarith [Real.pi_gt_d4]

theorem stdNormalPDF_zero_lt : stdNormalPDF 0 < 2 / 5 := by
  rw [stdNormalPDF_zero]
  have hsqrt_gt : (5 : ℝ) / 2 < Real.sqrt (2 * Real.pi) := by
    rw [Real.lt_sqrt (by norm_num)]; linarith [Real.pi_gt_d4]
  simpa using inv_strictAnti₀ (by norm_num : (0 : ℝ) < 5 / 2) hsqrt_gt

theorem sqrt_two_gt : (7071 : ℝ) / 5000 < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem sqrt_three_gt : (433 : ℝ) / 250 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem integral_sq_eq_one_of_variance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY_meas : AEMeasurable Y P)
    (hY0 : ∫ ω, Y ω ∂P = 0) (hY_var : variance Y P = 1) :
    ∫ ω, Y ω ^ 2 ∂P = 1 := by
  linarith [variance_of_integral_eq_zero hY_meas hY0]

theorem one_le_integral_pow_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY4 : MemLp Y 4 P) (hY2 : ∫ ω, Y ω ^ 2 ∂P = 1) :
    1 ≤ ∫ ω, Y ω ^ 4 ∂P := by
  have h4 := integrable_pow_four_of_memLp_four hY4
  have h2 := integrable_sq_of_memLp_four hY4
  have hsub : Integrable (fun ω ↦ Y ω ^ 4 - 2 * Y ω ^ 2) P := h4.sub (h2.const_mul 2)
  have hnn : 0 ≤ ∫ ω, (Y ω ^ 2 - 1) ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  have heq : (fun ω ↦ (Y ω ^ 2 - 1) ^ 2) = fun ω ↦ (Y ω ^ 4 - 2 * Y ω ^ 2) + 1 := by ext ω; ring
  rw [heq, integral_add hsub (integrable_const 1), integral_sub h4 (h2.const_mul 2),
    integral_const_mul, integral_const] at hnn
  simp only [probReal_univ, smul_eq_mul, one_mul] at hnn; linarith

theorem base_const_le_first_term
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P) (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) :
    Real.sqrt (2 / Real.pi) / (2 * Real.sqrt n) ≤
      Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) / (2 * (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsum_ge : (n : ℝ) ≤ ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P := by
    calc (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P :=
          Finset.sum_le_sum fun i _ ↦ one_le_integral_pow_four (hX4 i) (hX2 i)
  have hid : Real.sqrt (2 / Real.pi) / (2 * Real.sqrt n) =
      Real.sqrt (2 / Real.pi) * Real.sqrt n / (2 * (n : ℝ)) := by
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn_pos.le
    field_simp [hn_pos.ne', hsqrt_pos.ne']; rw [sq, hsq]
  rw [hid]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum_ge) (Real.sqrt_nonneg _)) (by positivity)

theorem one_le_integral_abs_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY4 : MemLp Y 4 P) (hY2 : ∫ ω, Y ω ^ 2 ∂P = 1) :
    1 ≤ ∫ ω, |Y ω| ^ 3 ∂P := by
  have h3 := integrable_abs_cube_of_memLp_four hY4
  have h2 := integrable_sq_of_memLp_four hY4
  have hsub : Integrable (fun ω ↦ |Y ω| ^ 3 - (3 / 2 : ℝ) * Y ω ^ 2) P :=
    h3.sub (h2.const_mul (3 / 2))
  have hnn : 0 ≤ ∫ ω, (|Y ω| - 1) ^ 2 * (|Y ω| + 1 / 2) ∂P :=
    integral_nonneg fun ω ↦ mul_nonneg (sq_nonneg _) (by linarith [abs_nonneg (Y ω)])
  have heq : (fun ω ↦ (|Y ω| - 1) ^ 2 * (|Y ω| + 1 / 2)) =
      fun ω ↦ (|Y ω| ^ 3 - (3 / 2 : ℝ) * Y ω ^ 2) + 1 / 2 := by
    ext ω; linear_combination -(3 / 2 : ℝ) * sq_abs (Y ω)
  rw [heq, integral_add hsub (integrable_const (1 / 2)), integral_sub h3 (h2.const_mul (3 / 2)),
    integral_const_mul, integral_const] at hnn
  simp only [probReal_univ, smul_eq_mul, one_mul] at hnn; linarith

/-! ### Section 2: Leave-One-Out Kernel and Exact Polynomial Certificates (`n ≥ 2`) -/

/-- Leave-one-out normal Stein kernel around $w = W_i$ with increment $d = X_i / \sqrt{n}$
(Example 3.6, `SteinIntro.tex:1053-1097`; `ISSUE-3.6`). -/
noncomputable def looKernel (n : ℕ) (f : ℝ → ℝ) (w d : ℝ) : ℝ :=
  (1 / (n : ℝ)) * (deriv f (w + d) - deriv f w) - d * (f (w + d) - f w - d * deriv f w)

theorem neg_mem_normalWassersteinClass {f : ℝ → ℝ} (hf : f ∈ normalWassersteinClass) :
    (fun x ↦ -f x) ∈ normalWassersteinClass := by
  rcases hf with ⟨hf1, hf2, hb0, hb1, hb2⟩
  have hd1 : deriv (fun x ↦ -f x) = fun x ↦ -deriv f x := funext fun _ ↦ deriv.neg
  have hd2 : deriv (deriv (fun x ↦ -f x)) = fun x ↦ -deriv (deriv f) x := by
    rw [hd1]; exact funext fun _ ↦ deriv.neg
  exact ⟨hf1.neg, hd1 ▸ hf2.neg, fun w ↦ by simpa only [abs_neg] using hb0 w,
    fun w ↦ by rw [hd1]; dsimp only; simpa only [abs_neg] using hb1 w,
    fun w ↦ by rw [hd2]; dsimp only; simpa only [abs_neg] using hb2 w⟩

theorem neg_comp_neg_mem_normalWassersteinClass {f : ℝ → ℝ}
    (hf : f ∈ normalWassersteinClass) :
    (fun x ↦ -f (-x)) ∈ normalWassersteinClass := by
  rcases hf with ⟨hf1, hf2, hb0, hb1, hb2⟩
  have hd1_at : ∀ x : ℝ, HasDerivAt (fun t ↦ -f (-t)) (deriv f (-x)) x := fun x ↦
    (((hf1 (-x)).hasDerivAt.neg).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
  have hd1 : deriv (fun t ↦ -f (-t)) = fun x ↦ deriv f (-x) := funext fun x ↦ (hd1_at x).deriv
  have hd2_at : ∀ x : ℝ, HasDerivAt (fun t ↦ deriv f (-t)) (-deriv (deriv f) (-x)) x := fun x ↦
    ((hf2 (-x)).hasDerivAt.comp x (hasDerivAt_neg x)).congr_deriv (by ring)
  have hd2 : deriv (deriv (fun t ↦ -f (-t))) = fun x ↦ -deriv (deriv f) (-x) := by
    rw [hd1]; exact funext fun x ↦ (hd2_at x).deriv
  exact ⟨fun x ↦ (hd1_at x).differentiableAt, hd1 ▸ fun x ↦ (hd2_at x).differentiableAt,
    fun w ↦ by simpa only [abs_neg] using hb0 (-w), fun w ↦ by rw [hd1]; exact hb1 (-w),
    fun w ↦ by rw [hd2]; dsimp only; simpa only [abs_neg] using hb2 (-w)⟩

theorem looKernel_neg (n : ℕ) (f : ℝ → ℝ) (w d : ℝ) :
    looKernel n (fun x ↦ -f x) w d = -looKernel n f w d := by
  have hd1 : deriv (fun x ↦ -f x) = fun x ↦ -deriv f x := funext fun _ ↦ deriv.neg
  unfold looKernel; rw [hd1]; ring

theorem looKernel_neg_comp_neg (n : ℕ) (f : ℝ → ℝ) (hf1 : Differentiable ℝ f) (w d : ℝ) :
    looKernel n (fun x ↦ -f (-x)) (-w) (-d) = looKernel n f w d := by
  have hd1 : deriv (fun t ↦ -f (-t)) = fun x ↦ deriv f (-x) := funext fun x ↦
    ((((hf1 (-x)).hasDerivAt.neg).comp x (hasDerivAt_neg x)).congr_deriv (by ring)).deriv
  unfold looKernel; rw [hd1]; dsimp only
  rw [show -w + -d = -(w + d) by ring, neg_neg, neg_neg]; ring

/-- Lower bound $f(w + b) - f(w + a) \ge (b - a) f'(w + a) - (b - a)^2$ for $a \le b$ when
$|f''| \le 2$ (`SteinIntro.tex:1053-1097`). -/
private lemma sub_ge_left_slope_sub_sq {f : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hb2 : ∀ z : ℝ, |deriv (deriv f) z| ≤ 2) (w : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * deriv f (w + a) - (b - a) ^ 2 ≤ f (w + b) - f (w + a) := by
  let G : ℝ → ℝ := fun u ↦ f (w + u) - (u - a) * deriv f (w + a) + (u - a) ^ 2
  have hG : ∀ u : ℝ, HasDerivAt G (deriv f (w + u) - deriv f (w + a) + 2 * (u - a)) u := fun u ↦ by
    have h1 : HasDerivAt (fun t ↦ f (w + t)) (deriv f (w + u)) u :=
      ((hf1 (w + u)).hasDerivAt.comp u ((hasDerivAt_id u).const_add w)).congr_deriv (mul_one _)
    have h2 := ((hasDerivAt_id u).sub_const a).mul_const (deriv f (w + a))
    have h3 := ((hasDerivAt_id u).sub_const a).pow 2
    exact ((h1.sub h2).add h3).congr_deriv (by dsimp; ring)
  have hmono : MonotoneOn G (Ici a) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
      (fun u _ ↦ (hG u).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hG u).hasDerivWithinAt) fun u hu ↦ by
        have hu' : a < u := by rwa [interior_Ici, mem_Ioi] at hu
        have hlip := convex_univ.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
          (fun z _ ↦ hf2 z) (fun z _ ↦ by simpa [Real.norm_eq_abs] using hb2 z)
          trivial trivial (x := w + a) (y := w + u)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, show (w + u) - (w + a) = u - a by ring,
          abs_of_pos (sub_pos.mpr hu')] at hlip
        linarith [(abs_le.mp hlip).1]
  have hle := hmono self_mem_Ici hab hab
  dsimp [G] at hle; linarith

/-- Lower bound $f(w + b) - f(w + a) \ge (b - a) f'(w + b) - (b - a)^2$ for $a \le b$ when
$|f''| \le 2$ (`SteinIntro.tex:1053-1097`). -/
private lemma sub_ge_right_slope_sub_sq {f : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hb2 : ∀ z : ℝ, |deriv (deriv f) z| ≤ 2) (w : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * deriv f (w + b) - (b - a) ^ 2 ≤ f (w + b) - f (w + a) := by
  let G : ℝ → ℝ := fun u ↦ f (w + u) - (u - b) * deriv f (w + b) - (b - u) ^ 2
  have hG : ∀ u : ℝ, HasDerivAt G (deriv f (w + u) - deriv f (w + b) + 2 * (b - u)) u := fun u ↦ by
    have h1 : HasDerivAt (fun t ↦ f (w + t)) (deriv f (w + u)) u :=
      ((hf1 (w + u)).hasDerivAt.comp u ((hasDerivAt_id u).const_add w)).congr_deriv (mul_one _)
    have h2 := ((hasDerivAt_id u).sub_const b).mul_const (deriv f (w + b))
    have h3 := ((hasDerivAt_const u b).sub (hasDerivAt_id u)).pow 2
    exact ((h1.sub h2).sub h3).congr_deriv (by dsimp; ring)
  have hmono : MonotoneOn G (Iic b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic b)
      (fun u _ ↦ (hG u).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hG u).hasDerivWithinAt) fun u hu ↦ by
        have hu' : u < b := by rwa [interior_Iic, mem_Iio] at hu
        have hlip := convex_univ.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
          (fun z _ ↦ hf2 z) (fun z _ ↦ by simpa [Real.norm_eq_abs] using hb2 z)
          trivial trivial (x := w + b) (y := w + u)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, show (w + u) - (w + b) = -(b - u) by ring,
          abs_neg, abs_of_pos (sub_pos.mpr hu')] at hlip
        linarith [(abs_le.mp hlip).1]
  have hle := hmono hab self_mem_Iic hab
  dsimp [G] at hle; linarith

private noncomputable def psiKernel (x : ℝ) : ℝ :=
  if x ≤ 1 then 2 * x - x ^ 3 else ((x ^ 2 - 1) ^ 2 + 1) / x

/-- Two-piece $2$-Lipschitz tent upper bound on `n * looKernel n f w r` for $r \ge 0$
(Example 3.6, `SteinIntro.tex:1053-1097`; `ISSUE-3.6`). -/
private lemma mul_looKernel_le_psiKernel_div_sqrt
    {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ} (hf : f ∈ normalWassersteinClass)
    (w : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (n : ℝ) * looKernel n f w r ≤ psiKernel (r * Real.sqrt n) / Real.sqrt n := by
  rcases hf with ⟨hf1, hf2, _, _, hb2⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  set δ : ℝ := (deriv f (w + r) - deriv f w) / 2
  have hδ_abs : |δ| ≤ r := by
    have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
      (fun z _ ↦ hf2 z) (fun z _ ↦ by simpa [Real.norm_eq_abs] using hb2 z)
      trivial trivial (x := w) (y := w + r)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hr] at h
    have habs : |deriv f (w + r) - deriv f w| = 2 * |δ| := by
      rw [show deriv f (w + r) - deriv f w = 2 * δ by dsimp [δ]; ring,
        abs_mul, abs_of_pos zero_lt_two]
    linarith
  have hδ_lo : -r ≤ δ := (abs_le.mp hδ_abs).1
  have hδ_hi : δ ≤ r := (abs_le.mp hδ_abs).2
  set ustar : ℝ := (r - δ) / 2
  have h1 := sub_ge_left_slope_sub_sq hf1 hf2 hb2 w (a := 0) (b := ustar)
    (by dsimp [ustar]; linarith)
  have h2 := sub_ge_right_slope_sub_sq hf1 hf2 hb2 w (a := ustar) (b := r)
    (by dsimp [ustar]; linarith)
  rw [add_zero, sub_zero] at h1
  have htent : r * δ - (r ^ 2 - δ ^ 2) / 2 ≤ f (w + r) - f w - r * deriv f w := by
    have hv : deriv f (w + r) = deriv f w + 2 * δ := by dsimp [δ]; ring
    have halg : ustar * deriv f w - ustar ^ 2 +
        ((r - ustar) * (deriv f w + 2 * δ) - (r - ustar) ^ 2) - r * deriv f w =
          r * δ - (r ^ 2 - δ ^ 2) / 2 := by dsimp [ustar]; ring
    rw [hv] at h2; linarith
  have hK_quad : looKernel n f w r ≤ (2 / (n : ℝ) - r ^ 2) * δ + r ^ 3 / 2 - r / 2 * δ ^ 2 := by
    have hv : deriv f (w + r) - deriv f w = 2 * δ := by dsimp [δ]; ring
    have halg2 : (1 / (n : ℝ)) * (2 * δ) - r * (r * δ - (r ^ 2 - δ ^ 2) / 2) =
        (2 / (n : ℝ) - r ^ 2) * δ + r ^ 3 / 2 - r / 2 * δ ^ 2 := by ring
    unfold looKernel; rw [hv]
    linarith [mul_le_mul_of_nonneg_left htent hr]
  set x : ℝ := r * Real.sqrt n
  have hr_eq : r = x / Real.sqrt n := by dsimp [x]; rw [mul_div_cancel_right₀ r hsqrt_pos.ne']
  have hs2 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
  have hs4 : Real.sqrt n ^ 4 = (n : ℝ) ^ 2 := by
    calc Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 := by rw [hs2]
  unfold psiKernel
  by_cases hx1 : x ≤ 1
  · simp only [hx1, ↓reduceIte]
    have hr2_le : r ^ 2 ≤ 1 / (n : ℝ) := by
      rw [hr_eq, div_pow, hs2]
      exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hr hsqrt_pos.le]) hn_pos.le
    have hK_le : looKernel n f w r ≤ (2 / (n : ℝ) - r ^ 2) * r := by
      have hid : (2 / (n : ℝ) - r ^ 2) * r -
          ((2 / (n : ℝ) - r ^ 2) * δ + r ^ 3 / 2 - r / 2 * δ ^ 2) =
          (r - δ) * (2 / (n : ℝ) - 3 / 2 * r ^ 2 - r * δ / 2) := by ring
      have hrd : r * δ ≤ r ^ 2 := by nlinarith
      have h2n : 2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
      have hfac : 0 ≤ 2 / (n : ℝ) - 3 / 2 * r ^ 2 - r * δ / 2 := by linarith
      have hprod : 0 ≤ (r - δ) * (2 / (n : ℝ) - 3 / 2 * r ^ 2 - r * δ / 2) :=
        mul_nonneg (sub_nonneg.mpr hδ_hi) hfac
      linarith
    calc (n : ℝ) * looKernel n f w r
        ≤ (n : ℝ) * ((2 / (n : ℝ) - r ^ 2) * r) := mul_le_mul_of_nonneg_left hK_le hn_pos.le
      _ = (2 * x - x ^ 3) / Real.sqrt n := by
          rw [hr_eq]; field_simp [hn_pos.ne', hsqrt_pos.ne']; rw [hs2]; ring
  · simp only [hx1, ↓reduceIte]
    have hx_gt : 1 < x := lt_of_not_ge hx1
    have hr_pos : 0 < r := by rw [hr_eq]; exact div_pos (lt_trans zero_lt_one hx_gt) hsqrt_pos
    have hK_le : looKernel n f w r ≤ r ^ 3 - 2 * r / (n : ℝ) + 2 / ((n : ℝ) ^ 2 * r) := by
      have hid : (r ^ 3 - 2 * r / (n : ℝ) + 2 / ((n : ℝ) ^ 2 * r)) -
          ((2 / (n : ℝ) - r ^ 2) * δ + r ^ 3 / 2 - r / 2 * δ ^ 2) =
          (r * δ - (2 / (n : ℝ) - r ^ 2)) ^ 2 / (2 * r) := by
        field_simp [hn_pos.ne', hr_pos.ne']; ring
      have hnn : 0 ≤ (r * δ - (2 / (n : ℝ) - r ^ 2)) ^ 2 / (2 * r) :=
        div_nonneg (sq_nonneg _) (by positivity)
      linarith
    calc (n : ℝ) * looKernel n f w r
        ≤ (n : ℝ) * (r ^ 3 - 2 * r / (n : ℝ) + 2 / ((n : ℝ) ^ 2 * r)) :=
          mul_le_mul_of_nonneg_left hK_le hn_pos.le
      _ = ((x ^ 2 - 1) ^ 2 + 1) / x / Real.sqrt n := by
          have hx_ne : x ≠ 0 := (lt_trans zero_lt_one hx_gt).ne'
          rw [hr_eq]; field_simp [hn_pos.ne', hsqrt_pos.ne', hx_ne]; rw [hs2, hs4]; ring

/-- Single-ramp bound on `2 * looKernel 2 f w r` for $r \ge 3 / 2$, exploiting $|f'| \le B_1$
(Example 3.6 at $n = 2$, `SteinIntro.tex:1053-1097`; `ISSUE-3.6`). -/
private lemma two_mul_looKernel_two_le_ramp
    {f : ℝ → ℝ} (hf : f ∈ normalWassersteinClass) (w : ℝ) {r : ℝ} (hr : (3 : ℝ) / 2 ≤ r) :
    2 * looKernel 2 f w r ≤
      2 * Real.sqrt (2 / Real.pi) * (r * Real.sqrt 2) ^ 2 -
        Real.sqrt 2 * Real.sqrt (2 / Real.pi) ^ 2 * (r * Real.sqrt 2) := by
  rcases hf with ⟨hf1, hf2, _, hb1, hb2⟩
  set B₁ : ℝ := Real.sqrt (2 / Real.pi)
  have hB1_lt : B₁ < 4 / 5 := lt_trans sqrt_two_div_pi_lt (by norm_num)
  have hr_pos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  set s₀ : ℝ := (deriv f w + B₁) / 2
  have hs0_lo : 0 ≤ s₀ := by dsimp [s₀]; linarith [(abs_le.mp (hb1 w)).1]
  have hs0_hi : s₀ ≤ B₁ := by dsimp [s₀]; linarith [(abs_le.mp (hb1 w)).2]
  have hs0_le_r : s₀ ≤ r := le_trans hs0_hi (le_trans hB1_lt.le (by linarith))
  have h1 := sub_ge_left_slope_sub_sq hf1 hf2 hb2 w (a := 0) (b := s₀) hs0_lo
  rw [add_zero, sub_zero] at h1
  have h2 : -(r - s₀) * B₁ ≤ f (w + r) - f (w + s₀) := by
    let G : ℝ → ℝ := fun u ↦ f (w + u) + u * B₁
    have hG : ∀ u : ℝ, HasDerivAt G (deriv f (w + u) + B₁) u := fun u ↦ by
      have hf_u : HasDerivAt (fun t ↦ f (w + t)) (deriv f (w + u)) u :=
        ((hf1 (w + u)).hasDerivAt.comp u ((hasDerivAt_id u).const_add w)).congr_deriv (mul_one _)
      exact (hf_u.add ((hasDerivAt_id u).mul_const B₁)).congr_deriv (by ring)
    have hmono : MonotoneOn G (Ici s₀) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici s₀)
        (fun u _ ↦ (hG u).continuousAt.continuousWithinAt)
        (fun u _ ↦ (hG u).hasDerivWithinAt) fun u _ ↦ by linarith [(abs_le.mp (hb1 (w + u))).1]
    have hle := hmono self_mem_Ici hs0_le_r hs0_le_r
    dsimp [G] at hle; linarith
  have hramp : s₀ ^ 2 - 2 * r * s₀ ≤ f (w + r) - f w - r * deriv f w := by
    have hv0 : deriv f w = 2 * s₀ - B₁ := by dsimp [s₀]; ring
    rw [hv0] at h1 ⊢; nlinarith
  have hK_s0 : 2 * looKernel 2 f w r ≤ 2 * B₁ + (4 * r ^ 2 - 2) * s₀ - 2 * r * s₀ ^ 2 := by
    have hvr : deriv f (w + r) ≤ B₁ := (abs_le.mp (hb1 (w + r))).2
    have hv0 : deriv f w = 2 * s₀ - B₁ := by dsimp [s₀]; ring
    have hmul := mul_le_mul_of_nonneg_left hramp (by positivity : 0 ≤ 2 * r)
    unfold looKernel; norm_num; linarith
  have hs0_max : 2 * B₁ + (4 * r ^ 2 - 2) * s₀ - 2 * r * s₀ ^ 2 ≤
      4 * B₁ * r ^ 2 - 2 * B₁ ^ 2 * r := by
    have hid : (4 * B₁ * r ^ 2 - 2 * B₁ ^ 2 * r) -
        (2 * B₁ + (4 * r ^ 2 - 2) * s₀ - 2 * r * s₀ ^ 2) =
        2 * (B₁ - s₀) * (2 * r ^ 2 - 1 - r * (B₁ + s₀)) := by ring
    have hrb : r * (B₁ + s₀) ≤ r * (8 / 5) :=
      mul_le_mul_of_nonneg_left (by linarith) hr_pos.le
    have hfac : 0 ≤ 2 * r ^ 2 - 1 - r * (B₁ + s₀) := by nlinarith
    have hprod : 0 ≤ 2 * (B₁ - s₀) * (2 * r ^ 2 - 1 - r * (B₁ + s₀)) :=
      mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr hs0_hi)) hfac
    linarith
  have hsq2 : (r * Real.sqrt 2) ^ 2 = 2 * r ^ 2 := by rw [mul_pow, Real.sq_sqrt zero_le_two]; ring
  have hprod2 : Real.sqrt 2 * B₁ ^ 2 * (r * Real.sqrt 2) = 2 * B₁ ^ 2 * r := by
    calc Real.sqrt 2 * B₁ ^ 2 * (r * Real.sqrt 2)
        = (Real.sqrt 2 * Real.sqrt 2) * B₁ ^ 2 * r := by ring
      _ = 2 * B₁ ^ 2 * r := by rw [Real.mul_self_sqrt zero_le_two]
  rw [hsq2, hprod2]; linarith

private lemma psiKernel_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psiKernel x := by
  unfold psiKernel; split_ifs with hx1
  · have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hx3 : x ^ 3 ≤ x := by nlinarith
    linarith
  · have : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx1); positivity

private lemma psiKernel_div_two_le {x : ℝ} (hx : 0 ≤ x) :
    psiKernel x / 2 ≤ -(89 / 100 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3 := by
  unfold psiKernel
  by_cases hx1 : x ≤ 1
  · simp only [hx1, ↓reduceIte]
    have hid : (-(89 / 100 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3) - (2 * x - x ^ 3) / 2 =
        (x - 71 / 100) ^ 2 * (7 / 6 * x + 23 / 30) +
          151057 / 300000 * (1 - x) + 611 / 150000 * x := by ring
    have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    have hnn : 0 ≤ (x - 71 / 100) ^ 2 * (7 / 6 * x + 23 / 30) +
        151057 / 300000 * (1 - x) + 611 / 150000 * x := by positivity
    linarith
  · simp only [hx1, ↓reduceIte]
    have hx_gt : 1 < x := lt_of_not_ge hx1
    rw [div_div, div_le_iff₀ (mul_pos (lt_trans zero_lt_one hx_gt) zero_lt_two)]
    set u : ℝ := x - 1
    have hu : 0 ≤ u := sub_nonneg.mpr hx_gt.le
    rw [show x = u + 1 by dsimp [u]; ring]
    have hid : (-(89 / 100 : ℝ) * ((u + 1) ^ 2 - 1) + 2 / 3 * (u + 1) ^ 3) * ((u + 1) * 2) -
        (((u + 1) ^ 2 - 1) ^ 2 + 1) =
        2 * ((u - 173 / 100) ^ 2 * (1 / 6 * u ^ 2 + 53 / 150 * u + 3223 / 60000) +
          1179611 / 200000000 + 3007 / 200000 * u) := by ring
    have hnn : 0 ≤ 2 * ((u - 173 / 100) ^ 2 * (1 / 6 * u ^ 2 + 53 / 150 * u + 3223 / 60000) +
        1179611 / 200000000 + 3007 / 200000 * u) := by positivity
    linarith

private lemma psiKernel_div_sqrt_three_le {x : ℝ} (hx : 0 ≤ x) :
    psiKernel x / Real.sqrt 3 ≤ 1 / 5 - (2 / 3 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3 := by
  refine (div_le_div_of_nonneg_left (psiKernel_nonneg hx) (by norm_num) sqrt_three_gt.le).trans ?_
  unfold psiKernel
  by_cases hx1 : x ≤ 1
  · simp only [hx1, ↓reduceIte]
    have hid : (1 / 5 - (2 / 3 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3) -
        (2 * x - x ^ 3) / (433 / 250 : ℝ) =
        (x - 16 / 25) ^ 2 * ((2 / 3 + 250 / 433 : ℝ) * x + 30062 / 32475) +
          3298251 / 6765625 * (1 - x) + 164453 / 20296875 * x := by ring
    have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    have hnn : 0 ≤ (x - 16 / 25) ^ 2 * ((2 / 3 + 250 / 433 : ℝ) * x + 30062 / 32475) +
        3298251 / 6765625 * (1 - x) + 164453 / 20296875 * x := by positivity
    linarith
  · simp only [hx1, ↓reduceIte]
    have hx_gt : 1 < x := lt_of_not_ge hx1
    rw [div_div, div_le_iff₀ (mul_pos (lt_trans zero_lt_one hx_gt) (by norm_num))]
    set u : ℝ := x - 1
    have hu : 0 ≤ u := sub_nonneg.mpr hx_gt.le
    rw [show x = u + 1 by dsimp [u]; ring]
    have hid : (1 / 5 - (2 / 3 : ℝ) * ((u + 1) ^ 2 - 1) + 2 / 3 * (u + 1) ^ 3) *
        ((u + 1) * (433 / 250 : ℝ)) - (((u + 1) ^ 2 - 1) ^ 2 + 1) =
        (433 / 250 : ℝ) *
          ((u - 137 / 50) ^ 2 * (116 / 1299 * u ^ 2 + 5842 / 32475 * u + 1601 / 270625) +
            497039993 / 2029687500 + 2911841 / 13531250 * u) := by ring
    have hnn : 0 ≤ (433 / 250 : ℝ) *
        ((u - 137 / 50) ^ 2 * (116 / 1299 * u ^ 2 + 5842 / 32475 * u + 1601 / 270625) +
          497039993 / 2029687500 + 2911841 / 13531250 * u) := by positivity
    linarith

private lemma psiKernel_div_sqrt_two_le_of_le {x : ℝ} (hx : 0 ≤ x) (hx_hi : x ≤ 121 / 50) :
    psiKernel x / Real.sqrt 2 ≤ 11 / 40 - (13 / 25 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3 := by
  refine (div_le_div_of_nonneg_left (psiKernel_nonneg hx) (by norm_num) sqrt_two_gt.le).trans ?_
  unfold psiKernel
  by_cases hx1 : x ≤ 1
  · simp only [hx1, ↓reduceIte]
    have hid : (11 / 40 - (13 / 25 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3) -
        (2 * x - x ^ 3) / (7071 / 5000 : ℝ) =
        (x - 18 / 25) ^ 2 * ((2 / 3 + 5000 / 7071 : ℝ) * x + 85927 / 58925) +
          11504091 / 294625000 * (1 - x) + 11068273 / 883875000 * x := by ring
    have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
    have hnn : 0 ≤ (x - 18 / 25) ^ 2 * ((2 / 3 + 5000 / 7071 : ℝ) * x + 85927 / 58925) +
        11504091 / 294625000 * (1 - x) + 11068273 / 883875000 * x := by positivity
    linarith
  · simp only [hx1, ↓reduceIte]
    have hx_gt : 1 < x := lt_of_not_ge hx1
    rw [div_div, div_le_iff₀ (mul_pos (lt_trans zero_lt_one hx_gt) (by norm_num))]
    set u : ℝ := x - 1
    set v : ℝ := 121 / 50 - x
    have hu : 0 ≤ u := sub_nonneg.mpr hx_gt.le
    have hv : 0 ≤ v := sub_nonneg.mpr hx_hi
    have hid : (71 / 50 : ℝ) ^ 4 *
        ((11 / 40 - (13 / 25 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3) * (x * (7071 / 5000 : ℝ)) -
          ((x ^ 2 - 1) ^ 2 + 1)) =
        (7071 / 5000 : ℝ) * (66341 / 282840 * v ^ 4 + 85761309 / 23570000 * u * v ^ 3 +
          15423865309 / 1767750000 * u ^ 2 * v ^ 2 + 81325337473 / 14731250000 * u ^ 3 * v +
          1548312053 / 44193750000 * u ^ 4) := by dsimp [u, v]; ring
    have hnn : 0 ≤ (7071 / 5000 : ℝ) * (66341 / 282840 * v ^ 4 + 85761309 / 23570000 * u * v ^ 3 +
        15423865309 / 1767750000 * u ^ 2 * v ^ 2 + 81325337473 / 14731250000 * u ^ 3 * v +
        1548312053 / 44193750000 * u ^ 4) := by positivity
    have hpos71 : (0 : ℝ) < (71 / 50 : ℝ) ^ 4 := by norm_num
    nlinarith

private lemma ramp_two_le_of_ge {x : ℝ} (hx : 121 / 50 ≤ x) :
    2 * Real.sqrt (2 / Real.pi) * x ^ 2 -
      Real.sqrt 2 * Real.sqrt (2 / Real.pi) ^ 2 * x ≤
        11 / 40 - (13 / 25 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3 := by
  have hb_lo := sqrt_two_div_pi_gt
  have hb_hi := sqrt_two_div_pi_lt
  have hx_nn : 0 ≤ x := le_trans (by norm_num) hx
  have h1 : 2 * Real.sqrt (2 / Real.pi) * x ^ 2 ≤ 2 * (7979 / 10000 : ℝ) * x ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb_hi.le zero_le_two) (sq_nonneg x)
  have h2 : (7071 / 5000 : ℝ) * (7978 / 10000 : ℝ) ^ 2 * x ≤
      Real.sqrt 2 * Real.sqrt (2 / Real.pi) ^ 2 * x :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul sqrt_two_gt.le (by nlinarith) (by norm_num) (Real.sqrt_nonneg _)) hx_nn
  set u : ℝ := x - 121 / 50
  have hu : 0 ≤ u := sub_nonneg.mpr hx
  have hid : (11 / 40 - (13 / 25 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3) -
      (2 * (7979 / 10000 : ℝ) * x ^ 2 - (7071 / 5000 : ℝ) * (7978 / 10000 : ℝ) ^ 2 * x) =
      574444055533 / 18750000000000 + 296555607591 / 125000000000 * u +
        13621 / 5000 * u ^ 2 + 2 / 3 * u ^ 3 := by dsimp [u]; ring
  have hnn : 0 ≤ 574444055533 / 18750000000000 + 296555607591 / 125000000000 * u +
      13621 / 5000 * u ^ 2 + 2 / 3 * u ^ 3 := by positivity
  linarith

/-- Pointwise polynomial majorant for `n * |looKernel n f w d|` across all $n \ge 2$
(Example 3.6, `SteinIntro.tex:1053-1097`; `ISSUE-3.6`). -/
theorem mul_abs_looKernel_le_for_ge_two
    {n : ℕ} (hn2 : 2 ≤ n) {f : ℝ → ℝ} (hf : f ∈ normalWassersteinClass) :
    ∃ α γ : ℝ, α ≤ Real.sqrt (2 / Real.pi) / (2 * Real.sqrt n) ∧
      ∀ w d : ℝ,
        (n : ℝ) * |looKernel n f w d| ≤
          α + γ * ((d * Real.sqrt n) ^ 2 - 1) + 2 / 3 * |d * Real.sqrt n| ^ 3 := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le zero_lt_two hn2
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsymm : ∀ (M : ℝ → ℝ),
      (∀ {g : ℝ → ℝ}, g ∈ normalWassersteinClass → ∀ (w : ℝ) {r : ℝ}, 0 ≤ r →
        (n : ℝ) * looKernel n g w r ≤ M (r * Real.sqrt n)) →
      ∀ w d : ℝ, (n : ℝ) * |looKernel n f w d| ≤ M (|d| * Real.sqrt n) := by
    intro M hpos w d
    have h_abs : |(n : ℝ) * looKernel n f w d| = (n : ℝ) * |looKernel n f w d| := by
      rw [abs_mul, abs_of_pos hn_pos]
    rw [← h_abs, abs_le]
    rcases le_total 0 d with hd | hd
    · rw [abs_of_nonneg hd]
      have h_lo := hpos (neg_mem_normalWassersteinClass hf) w hd
      rw [looKernel_neg] at h_lo
      exact ⟨by linarith, hpos hf w hd⟩
    · rw [abs_of_nonpos hd]
      have hnd := neg_nonneg.mpr hd
      have hf_refl := neg_comp_neg_mem_normalWassersteinClass hf
      have h_up := hpos hf_refl (-w) hnd
      have h_lo := hpos (neg_mem_normalWassersteinClass hf_refl) (-w) hnd
      rw [looKernel_neg_comp_neg n f hf.1 w d] at h_up
      rw [looKernel_neg, looKernel_neg_comp_neg n f hf.1 w d] at h_lo
      exact ⟨by linarith, h_up⟩
  have hnorm_arg : ∀ d : ℝ, ((|d| * Real.sqrt n) ^ 2 = (d * Real.sqrt n) ^ 2) ∧
      (|d| * Real.sqrt n = |d * Real.sqrt n|) := fun d ↦
    ⟨by rw [mul_pow, sq_abs, ← mul_pow], by rw [abs_mul, abs_of_pos hsqrt_pos]⟩
  by_cases hn4 : 4 ≤ n
  · refine ⟨0, -(89 / 100 : ℝ), by positivity, fun w d ↦ ?_⟩
    have hsqrt_ge : (2 : ℝ) ≤ Real.sqrt n := by
      rw [Real.le_sqrt zero_le_two hn_pos.le]; norm_num; exact_mod_cast hn4
    have hM := hsymm (fun x ↦ 0 + -(89 / 100 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3)
      (fun {g} hg w' {r} hr ↦ by
        have hx : 0 ≤ r * Real.sqrt n := mul_nonneg hr hsqrt_pos.le
        have h1 := mul_looKernel_le_psiKernel_div_sqrt hn_pos_nat hg w' hr
        have h2 := div_le_div_of_nonneg_left (psiKernel_nonneg hx) zero_lt_two hsqrt_ge
        linarith [psiKernel_div_two_le hx]) w d
    rwa [(hnorm_arg d).1, (hnorm_arg d).2] at hM
  · interval_cases n
    · have hα : (11 / 40 : ℝ) ≤ Real.sqrt (2 / Real.pi) / (2 * Real.sqrt 2) := by
        rw [le_div_iff₀ (by positivity)]
        have hs2 : Real.sqrt 2 < 7072 / 5000 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        linarith [sqrt_two_div_pi_gt]
      refine ⟨11 / 40, -(13 / 25 : ℝ), hα, fun w d ↦ ?_⟩
      have hM := hsymm (fun x ↦ 11 / 40 + -(13 / 25 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3)
        (fun {g} hg w' {r} hr ↦ by
          by_cases hx_hi : r * Real.sqrt 2 ≤ 121 / 50
          · have h1 := mul_looKernel_le_psiKernel_div_sqrt (by decide : 0 < 2) hg w' hr
            simp only [Nat.cast_ofNat] at h1
            linarith [psiKernel_div_sqrt_two_le_of_le (mul_nonneg hr (Real.sqrt_nonneg 2)) hx_hi]
          · have hx_ge : (121 / 50 : ℝ) ≤ r * Real.sqrt 2 := le_of_not_ge hx_hi
            have hs2_ub : Real.sqrt 2 < 8 / 5 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
            have h1 := two_mul_looKernel_two_le_ramp hg w'
              (by nlinarith [Real.sqrt_nonneg 2] : (3 : ℝ) / 2 ≤ r)
            simpa only [Nat.cast_ofNat] using h1.trans (by linarith [ramp_two_le_of_ge hx_ge])) w d
      rwa [(hnorm_arg d).1, (hnorm_arg d).2] at hM
    · have hα : (1 / 5 : ℝ) ≤ Real.sqrt (2 / Real.pi) / (2 * Real.sqrt 3) := by
        rw [le_div_iff₀ (by positivity)]
        have hs3 : Real.sqrt 3 < 7 / 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
        linarith [sqrt_two_div_pi_gt]
      refine ⟨1 / 5, -(2 / 3 : ℝ), hα, fun w d ↦ ?_⟩
      have hM := hsymm (fun x ↦ 1 / 5 + -(2 / 3 : ℝ) * (x ^ 2 - 1) + 2 / 3 * x ^ 3)
        (fun {g} hg w' {r} hr ↦ by
          have h1 := mul_looKernel_le_psiKernel_div_sqrt (by decide : 0 < 3) hg w' hr
          simp only [Nat.cast_ofNat] at h1
          linarith [psiKernel_div_sqrt_three_le (mul_nonneg hr (Real.sqrt_nonneg 3))]) w d
      rwa [(hnorm_arg d).1, (hnorm_arg d).2] at hM

end SteinMethod.Ex36SmallN
