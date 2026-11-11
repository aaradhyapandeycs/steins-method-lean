/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

/-!
# Normal Approximation of Sums of Independent Random Variables

Establishes the leave-one-out Stein expansion and Wasserstein-1 error bounds for standardized sums
of independent random variables in Section 3.1 of Nathan Ross, *"Fundamentals of Stein's method"*
(`SteinIntro.tex:730-800`):

* `SteinMethod.abs_sub_deriv_mul_le_half_sq`: first-order Taylor remainder bound for functions with
  bounded second derivative.
* `SteinMethod.integral_abs_le_sqrt_integral_sq`: $L^1$–$L^2$ inequality on a probability space.
* `SteinMethod.indepSum_stein_expansion`: **Lemma 3.3** (`\label{lem33}`, eqs. `(3.3)`–`(3.4)`
  `\label{345}`–`\label{345a}`, `SteinIntro.tex:753-759`).
* `SteinMethod.indepSum_normalSteinOp_bound`: **Lemma 3.4** (`\label{lem33aa}`, eq. `(3.6)`
  `\label{337}`, `SteinIntro.tex:771-776`).
* `SteinMethod.indepSum_iSup_normalWassersteinClass_le` and
  `SteinMethod.indepSum_wasserstein_clt_of_stein_bound`: supremum over `normalWassersteinClass` and
  assembly for **Theorem 3.2** (`\label{thm32}`, `SteinIntro.tex:736-742`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SteinMethod

/-! ### Moment, $L^p$, measurability, and calculus helper lemmas -/

/-- `MemLp Y 4 P` implies integrability of the fourth absolute moment `fun ω ↦ |Y ω| ^ 4`
(Section 3.1 moment helper for Theorem 3.2 `\label{thm32}`, `SteinIntro.tex:736-742`). -/
theorem integrable_abs_pow_four_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    Integrable (fun ω ↦ |Y ω| ^ 4) P := by
  simpa [Real.norm_eq_abs] using hY4.integrable_norm_pow (by decide)

/-- `MemLp Y 4 P` implies integrability of `fun ω ↦ Y ω ^ 4`
(Section 3.1 moment helper for Theorem 3.2 `\label{thm32}`, `SteinIntro.tex:736-742`). -/
theorem integrable_pow_four_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    Integrable (fun ω ↦ Y ω ^ 4) P := by
  refine (integrable_abs_pow_four_of_memLp_four hY4).congr
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  calc
    |Y ω| ^ 4 = (|Y ω| ^ 2) ^ 2 := by ring
    _ = (Y ω ^ 2) ^ 2 := by rw [sq_abs]
    _ = Y ω ^ 4 := by ring

/-- On a probability space, `MemLp Y 4 P` implies `MemLp Y 3 P`
(Section 3.1 moment helper for Theorem 3.2 `\label{thm32}`, `SteinIntro.tex:736-742`). -/
theorem memLp_three_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    MemLp Y 3 P :=
  hY4.mono_exponent (by norm_num)

/-- On a probability space, `MemLp Y 4 P` implies `MemLp Y 2 P`
(Section 3.1 moment helper for Theorem 3.2 `\label{thm32}`, `SteinIntro.tex:736-742`). -/
theorem memLp_two_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    MemLp Y 2 P :=
  hY4.mono_exponent (by norm_num)

/-- On a probability space, `MemLp Y 4 P` implies `Integrable Y P`
(Section 3.1 moment helper for Lemma 3.3 `\label{lem33}`, `SteinIntro.tex:753-759`). -/
theorem integrable_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    Integrable Y P :=
  memLp_one_iff_integrable.mp (hY4.mono_exponent (by norm_num))

/-- On a probability space, `MemLp Y 4 P` implies square integrability `Integrable (Y ^ 2) P`
(Section 3.1 moment helper for Lemma 3.3 `\label{lem33}`, `SteinIntro.tex:753-759`). -/
theorem integrable_sq_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    Integrable (fun ω ↦ Y ω ^ 2) P :=
  (memLp_two_of_memLp_four hY4).integrable_sq

/-- On a probability space, `MemLp Y 4 P` implies third absolute moment integrability
(Section 3.1 moment helper for Lemma 3.4 `\label{lem33aa}`, `SteinIntro.tex:771-776`). -/
theorem integrable_abs_cube_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    Integrable (fun ω ↦ |Y ω| ^ 3) P := by
  simpa [Real.norm_eq_abs] using
    (memLp_three_of_memLp_four hY4).integrable_norm_pow (by decide)

/-- `MemLp Y 4 P` implies `MemLp (fun ω ↦ Y ω ^ 2) 2 P`
(Section 3.1 moment helper for Lemma 3.4 `\label{lem33aa}`, `SteinIntro.tex:771-776`). -/
theorem memLp_two_sq_of_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ}
    (hY4 : MemLp Y 4 P) :
    MemLp (fun ω ↦ Y ω ^ 2) 2 P := by
  change MemLp (Y ^ 2) 2 P
  rw [memLp_two_iff_integrable_sq (hY4.aestronglyMeasurable.pow 2)]
  refine (integrable_pow_four_of_memLp_four hY4).congr
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  dsimp
  ring

/-- Almost-everywhere measurability of the standardized sum
$W = (\sum_{i=1}^n X_i)/\sqrt{n}$ in Theorem 3.2 (`\label{thm32}`, `SteinIntro.tex:736-742`). -/
theorem indepSum_aemeasurable_W
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P) :
    AEMeasurable (fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n) P :=
  (Finset.univ.aemeasurable_fun_sum fun i _ ↦ hX_meas i).div_const (Real.sqrt n)

/-- Product of an integrable real random variable with a bounded a.e.-strongly measurable factor
is integrable (Section 3.1 helper for Lemma 3.3 `\label{lem33}`, `SteinIntro.tex:753-759`). -/
theorem integrable_mul_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U V : Ω → ℝ} {B : ℝ}
    (hU : Integrable U P) (hV : AEStronglyMeasurable V P) (hB : ∀ ω, |V ω| ≤ B) :
    Integrable (fun ω ↦ U ω * V ω) P := by
  refine (hU.abs.const_mul (max B 0)).mono' (hU.aestronglyMeasurable.mul hV)
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hB ω).trans (le_max_left B 0)) (abs_nonneg _)

/-- First-order Taylor remainder bound used in the proof of Lemma 3.4 (`\label{lem33aa}`,
`SteinIntro.tex:780-790`): if `f` and `deriv f` are differentiable on `ℝ` and
`|deriv (deriv f) x| ≤ M` everywhere, then
`|f w - f w_i - (w - w_i) * deriv f w| ≤ (M / 2) * (w - w_i) ^ 2`. -/
theorem abs_sub_deriv_mul_le_half_sq
    {f : ℝ → ℝ} {M : ℝ}
    (hf1 : Differentiable ℝ f)
    (hf2 : Differentiable ℝ (deriv f))
    (hM : ∀ x : ℝ, |deriv (deriv f) x| ≤ M)
    (w w_i : ℝ) :
    |f w - f w_i - (w - w_i) * deriv f w| ≤ (M / 2) * (w - w_i) ^ 2 := by
  have hlip : ∀ t : ℝ, |deriv f t - deriv f w| ≤ M * |t - w| := by
    intro t
    have h :=
      convex_univ.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (fun x _ ↦ hf2 x)
        (fun x _ ↦ by simpa [Real.norm_eq_abs] using hM x)
        trivial trivial (x := w) (y := t)
    simpa [Real.norm_eq_abs] using h
  have hftc :
      ∫ t in w..w_i, (deriv f t - deriv f w) = f w_i - f w - (w_i - w) * deriv f w := by
    let g : ℝ → ℝ := fun s ↦ f s - (s - w) * deriv f w
    have hderiv : ∀ t ∈ Set.uIcc w w_i, HasDerivAt g (deriv f t - deriv f w) t := by
      intro t _
      have h1 : HasDerivAt f (deriv f t) t := (hf1 t).hasDerivAt
      have h2 := ((hasDerivAt_id' t).fun_sub (hasDerivAt_const t w)).mul_const (deriv f w)
      convert h1.fun_sub h2 using 1
      ring
    have hint : IntervalIntegrable (fun t ↦ deriv f t - deriv f w) volume w w_i :=
      (hf2.continuous.sub continuous_const).intervalIntegrable w w_i
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp only [g]
    ring
  have h_eq :
      |f w - f w_i - (w - w_i) * deriv f w| = |∫ t in w..w_i, (deriv f t - deriv f w)| := by
    rw [hftc, ← abs_neg]
    congr 1
    ring
  rw [h_eq]
  rcases le_total w w_i with hle | hge
  · have hbound :
        ‖∫ t in w..w_i, (deriv f t - deriv f w)‖ ≤ ∫ t in w..w_i, M * (t - w) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hle ?_
        ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable w w_i)
      filter_upwards with t ht
      rw [Real.norm_eq_abs, ← abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      exact hlip t
    have heval : ∫ t in w..w_i, M * (t - w) = (M / 2) * (w - w_i) ^ 2 := by
      let q : ℝ → ℝ := fun s ↦ (M / 2) * ((s - w) * (s - w))
      have hd : ∀ t ∈ Set.uIcc w w_i, HasDerivAt q (M * (t - w)) t := by
        intro t _
        have hu := (hasDerivAt_id' t).fun_sub (hasDerivAt_const t w)
        have h := (hu.fun_mul hu).const_mul (M / 2)
        convert h using 1
        ring
      have hi : IntervalIntegrable (fun t ↦ M * (t - w)) volume w w_i :=
        (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable w w_i
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
      dsimp only [q]
      ring
    simpa [Real.norm_eq_abs, heval] using hbound
  · rw [intervalIntegral.integral_symm w_i w, abs_neg]
    have hbound :
        ‖∫ t in w_i..w, (deriv f t - deriv f w)‖ ≤ ∫ t in w_i..w, M * (w - t) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hge ?_
        ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable w_i w)
      filter_upwards with t ht
      have hsub : |t - w| = w - t := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      rw [Real.norm_eq_abs, ← hsub]
      exact hlip t
    have heval : ∫ t in w_i..w, M * (w - t) = (M / 2) * (w - w_i) ^ 2 := by
      let q : ℝ → ℝ := fun s ↦ -(M / 2) * ((w - s) * (w - s))
      have hd : ∀ t ∈ Set.uIcc w_i w, HasDerivAt q (M * (w - t)) t := by
        intro t _
        have hu := (hasDerivAt_const t w).fun_sub (hasDerivAt_id' t)
        have h := (hu.fun_mul hu).const_mul (-(M / 2))
        convert h using 1
        ring
      have hi : IntervalIntegrable (fun t ↦ M * (w - t)) volume w_i w :=
        (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable w_i w
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
      dsimp only [q]
      ring
    simpa [Real.norm_eq_abs, heval] using hbound

/-- Cauchy–Schwarz / $L^1$–$L^2$ inequality on a probability space used in the proof of Lemma 3.4
(`\label{lem33aa}`, `SteinIntro.tex:792-799`):
`∫ ω, |Y ω| ∂P ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂P)`. -/
theorem integral_abs_le_sqrt_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    ∫ ω, |Y ω| ∂P ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂P) := by
  set c : ℝ := ∫ ω, |Y ω| ∂P
  have hc_nonneg : 0 ≤ c := integral_nonneg fun _ ↦ abs_nonneg _
  have hY_int : Integrable Y P := memLp_one_iff_integrable.mp (hY.mono_exponent one_le_two)
  have hY_abs : Integrable (fun ω ↦ |Y ω|) P := hY_int.abs
  have hY_sq : Integrable (fun ω ↦ Y ω ^ 2) P := hY.integrable_sq
  have h_nonneg : 0 ≤ ∫ ω, (|Y ω| - c) ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  have h_sub_int : Integrable (fun ω ↦ Y ω ^ 2 - 2 * c * |Y ω|) P :=
    hY_sq.sub (hY_abs.const_mul (2 * c))
  have h_expand : ∫ ω, (|Y ω| - c) ^ 2 ∂P = (∫ ω, Y ω ^ 2 ∂P) - c ^ 2 := by
    have h_eq :
        (fun ω ↦ (|Y ω| - c) ^ 2) = fun ω ↦ (Y ω ^ 2 - 2 * c * |Y ω|) + c ^ 2 := by
      ext ω
      calc
        (|Y ω| - c) ^ 2 = |Y ω| ^ 2 - 2 * c * |Y ω| + c ^ 2 := by ring
        _ = (Y ω ^ 2 - 2 * c * |Y ω|) + c ^ 2 := by rw [sq_abs]
    rw [h_eq, integral_add h_sub_int (integrable_const (c ^ 2)),
      integral_sub hY_sq (hY_abs.const_mul (2 * c)), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
    ring
  have h_sq_le : c ^ 2 ≤ ∫ ω, Y ω ^ 2 ∂P := by linarith
  calc
    c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc_nonneg).symm
    _ ≤ Real.sqrt (∫ ω, Y ω ^ 2 ∂P) := Real.sqrt_le_sqrt h_sq_le

/-! ### Leave-one-out Stein expansion and operator bound -/

/-- Lemma 3.3 (`\label{lem33}`, eqs. `(3.3)`–`(3.4)` `\label{345}`–`\label{345a}`,
`SteinIntro.tex:753-759`, proof at `SteinIntro.tex:760-770`; `ISSUE-TYPO-3.3`, `ISSUE-3.3`):
leave-one-out Stein expansion for $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ and
$W_i = (\sum_{j \ne i} X_j)/\sqrt{n}$. -/
theorem indepSum_stein_expansion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {f : ℝ → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1)
    (hf1 : Differentiable ℝ f)
    (hb0 : ∃ B₀ : ℝ, ∀ w : ℝ, |f w| ≤ B₀)
    (hb1 : ∃ B₁ : ℝ, ∀ w : ℝ, |deriv f w| ≤ B₁) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ Finset.univ.erase i, X j ω) / Real.sqrt n
    ∫ ω, W ω * f (W ω) ∂P =
      (∫ ω, (1 / Real.sqrt n) * ∑ i : Fin n,
          X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) ∂P) +
        ∫ ω, (1 / Real.sqrt n) * ∑ i : Fin n,
          X i ω * (W ω - W_i i ω) * deriv f (W ω) ∂P := by
  have _ : ∫ ω, X ⟨0, hn⟩ ω ^ 2 ∂P = 1 := hX2 ⟨0, hn⟩
  intro W W_i
  obtain ⟨B₀, hB₀⟩ := hb0
  obtain ⟨B₁, hB₁⟩ := hb1
  have hX1 : ∀ i : Fin n, Integrable (X i) P :=
    fun i ↦ integrable_of_memLp_four (hX4 i)
  have hX_sq : ∀ i : Fin n, Integrable (fun ω ↦ X i ω ^ 2) P :=
    fun i ↦ integrable_sq_of_memLp_four (hX4 i)
  have hW_meas : AEMeasurable W P := indepSum_aemeasurable_W hX_meas
  have hWi_meas : ∀ i : Fin n, AEMeasurable (W_i i) P := fun i ↦
    ((Finset.univ.erase i).aemeasurable_fun_sum fun j _ ↦ hX_meas j).div_const (Real.sqrt n)
  have hfW_asm : AEStronglyMeasurable (fun ω ↦ f (W ω)) P :=
    (hf1.continuous.measurable.comp_aemeasurable hW_meas).aestronglyMeasurable
  have hfWi_asm : ∀ i : Fin n, AEStronglyMeasurable (fun ω ↦ f (W_i i ω)) P := fun i ↦
    (hf1.continuous.measurable.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
  have hdfW_asm : AEStronglyMeasurable (fun ω ↦ deriv f (W ω)) P :=
    ((measurable_deriv f).comp_aemeasurable hW_meas).aestronglyMeasurable
  have h_diff : ∀ (i : Fin n) (ω : Ω), W ω - W_i i ω = X i ω / Real.sqrt n := by
    intro i ω
    dsimp only [W, W_i]
    rw [← sub_div, ← Finset.add_sum_erase Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)]
    ring
  have h_int_XfW : ∀ i : Fin n, Integrable (fun ω ↦ X i ω * f (W ω)) P := fun i ↦
    integrable_mul_of_bound (hX1 i) hfW_asm fun ω ↦ hB₀ (W ω)
  have h_int_XfWi : ∀ i : Fin n, Integrable (fun ω ↦ X i ω * f (W_i i ω)) P := fun i ↦
    integrable_mul_of_bound (hX1 i) (hfWi_asm i) fun ω ↦ hB₀ (W_i i ω)
  have h_int_B :
      ∀ i : Fin n, Integrable (fun ω ↦ X i ω * (W ω - W_i i ω) * deriv f (W ω)) P := by
    intro i
    have h_eq :
        (fun ω ↦ X i ω * (W ω - W_i i ω) * deriv f (W ω)) =
          fun ω ↦ (X i ω ^ 2 / Real.sqrt n) * deriv f (W ω) := by
      ext ω
      rw [h_diff i ω]
      ring
    rw [h_eq]
    exact integrable_mul_of_bound ((hX_sq i).div_const (Real.sqrt n)) hdfW_asm fun ω ↦ hB₁ (W ω)
  have h_int_A :
      ∀ i : Fin n,
        Integrable
          (fun ω ↦ X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))) P := by
    intro i
    have h_eq :
        (fun ω ↦ X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))) =
          fun ω ↦
            X i ω * f (W ω) - X i ω * f (W_i i ω) -
              X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
      ext ω
      ring
    rw [h_eq]
    exact ((h_int_XfW i).sub (h_int_XfWi i)).sub (h_int_B i)
  have h_int_term1 :
      Integrable
        (fun ω ↦
          (1 / Real.sqrt n) *
            ∑ i : Fin n,
              X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))) P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ h_int_A i).const_mul (1 / Real.sqrt n)
  have h_int_term2 :
      Integrable
        (fun ω ↦
          (1 / Real.sqrt n) *
            ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ h_int_B i).const_mul (1 / Real.sqrt n)
  have h_zero_cross : ∀ i : Fin n, ∫ ω, X i ω * f (W_i i ω) ∂P = 0 := by
    intro i
    let g : ℝ → ℝ := fun x ↦ f (x / Real.sqrt n)
    have hg_meas : Measurable g :=
      hf1.continuous.measurable.comp (measurable_id.div_const (Real.sqrt n))
    have h_ind_sum : IndepFun (X i) (∑ j ∈ Finset.univ.erase i, X j) P :=
      (h_indep.indepFun_finsetSum_of_notMem₀ hX_meas (Finset.notMem_erase i Finset.univ)).symm
    have h_ind_comp : IndepFun (id ∘ X i) (g ∘ ∑ j ∈ Finset.univ.erase i, X j) P :=
      h_ind_sum.comp measurable_id hg_meas
    have h_eq_fn :
        (fun ω ↦ X i ω * f (W_i i ω)) =
          fun ω ↦ (id ∘ X i) ω * (g ∘ ∑ j ∈ Finset.univ.erase i, X j) ω := by
      ext ω
      simp [g, W_i, Finset.sum_apply]
    rw [h_eq_fn,
      h_ind_comp.integral_fun_mul_eq_mul_integral (hX_meas i).aestronglyMeasurable
        (by simpa [g, W_i, Function.comp_def, Finset.sum_apply] using hfWi_asm i)]
    simp [hX0 i]
  rw [← integral_add h_int_term1 h_int_term2]
  have h_comb :
      (fun ω ↦
        (1 / Real.sqrt n) *
          (∑ i : Fin n,
            X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))) +
        (1 / Real.sqrt n) *
          ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) =
      fun ω ↦ W ω * f (W ω) - (1 / Real.sqrt n) * ∑ i : Fin n, X i ω * f (W_i i ω) := by
    ext ω
    rw [← mul_add, ← Finset.sum_add_distrib]
    have h_inner :
        (∑ i : Fin n,
          (X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) +
            X i ω * (W ω - W_i i ω) * deriv f (W ω))) =
          (∑ i : Fin n, X i ω * f (W ω)) - ∑ i : Fin n, X i ω * f (W_i i ω) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [h_inner, ← Finset.sum_mul]
    dsimp only [W]
    ring
  rw [h_comb,
    integral_sub
      (integrable_mul_of_bound
        ((integrable_finsetSum Finset.univ fun i _ ↦ hX1 i).div_const (Real.sqrt n))
        hfW_asm fun ω ↦ hB₀ (W ω))
      ((integrable_finsetSum Finset.univ fun i _ ↦ h_int_XfWi i).const_mul (1 / Real.sqrt n)),
    integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ h_int_XfWi i]
  simp [h_zero_cross, W]

/-- Lemma 3.4 (`\label{lem33aa}`, eq. `(3.6)` `\label{337}`, `SteinIntro.tex:771-776`, proof at
`SteinIntro.tex:777-800`): bound on $|\mathbb{E}[f'(W) - W f(W)]|$ for
$W = (\sum_{i=1}^n X_i)/\sqrt{n}$ when $f$ is bounded with bounded first and second
derivatives. -/
theorem indepSum_normalSteinOp_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {f : ℝ → ℝ} {B₁ B₂ : ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1)
    (hf : Differentiable ℝ f ∧ Differentiable ℝ (deriv f))
    (hb0 : ∃ B₀ : ℝ, ∀ w : ℝ, |f w| ≤ B₀)
    (hb1 : ∀ w : ℝ, |deriv f w| ≤ B₁)
    (hb2 : ∀ w : ℝ, |deriv (deriv f) w| ≤ B₂) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    |∫ ω, normalSteinOp f (W ω) ∂P| ≤
      B₂ / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
        B₁ / (n : ℝ) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) := by
  rcases hf with ⟨hf1, hf2⟩
  intro W
  let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ Finset.univ.erase i, X j ω) / Real.sqrt n
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := hn_pos.le
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have h_rpow : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    have h32 : (3 / 2 : ℝ) = 1 + (1 : ℝ) / 2 := by norm_num
    rw [h32, Real.rpow_add hn_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hB1_nonneg : 0 ≤ B₁ := (abs_nonneg (deriv f 0)).trans (hb1 0)
  have hX1 : ∀ i : Fin n, Integrable (X i) P :=
    fun i ↦ integrable_of_memLp_four (hX4 i)
  have hX_sq : ∀ i : Fin n, Integrable (fun ω ↦ X i ω ^ 2) P :=
    fun i ↦ integrable_sq_of_memLp_four (hX4 i)
  have hX_cube : ∀ i : Fin n, Integrable (fun ω ↦ |X i ω| ^ 3) P :=
    fun i ↦ integrable_abs_cube_of_memLp_four (hX4 i)
  have hW_meas : AEMeasurable W P := indepSum_aemeasurable_W hX_meas
  have hfW_asm : AEStronglyMeasurable (fun ω ↦ f (W ω)) P :=
    (hf1.continuous.measurable.comp_aemeasurable hW_meas).aestronglyMeasurable
  have hdfW_asm : AEStronglyMeasurable (fun ω ↦ deriv f (W ω)) P :=
    ((measurable_deriv f).comp_aemeasurable hW_meas).aestronglyMeasurable
  have h_diff : ∀ (i : Fin n) (ω : Ω), W ω - W_i i ω = X i ω / Real.sqrt n := by
    intro i ω
    dsimp only [W, W_i]
    rw [← sub_div, ← Finset.add_sum_erase Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)]
    ring
  have h_int_dfW : Integrable (fun ω ↦ deriv f (W ω)) P := by
    refine (integrable_const B₁).mono' hdfW_asm (Filter.Eventually.of_forall fun ω ↦ ?_)
    simpa [Real.norm_eq_abs] using hb1 (W ω)
  have h_int_WfW : Integrable (fun ω ↦ W ω * f (W ω)) P := by
    obtain ⟨B₀, hB₀⟩ := hb0
    exact integrable_mul_of_bound
      ((integrable_finsetSum Finset.univ fun i _ ↦ hX1 i).div_const (Real.sqrt n))
      hfW_asm fun ω ↦ hB₀ (W ω)
  have h_int_term2 :
      Integrable
        (fun ω ↦
          (1 / Real.sqrt n) *
            ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) P := by
    refine (integrable_finsetSum Finset.univ fun i _ ↦ ?_).const_mul (1 / Real.sqrt n)
    have h_eq :
        (fun ω ↦ X i ω * (W ω - W_i i ω) * deriv f (W ω)) =
          fun ω ↦ (X i ω ^ 2 / Real.sqrt n) * deriv f (W ω) := by
      ext ω
      rw [h_diff i ω]
      ring
    rw [h_eq]
    exact integrable_mul_of_bound ((hX_sq i).div_const (Real.sqrt n)) hdfW_asm fun ω ↦ hb1 (W ω)
  have h_exp :=
    indepSum_stein_expansion P hn hX_meas h_indep hX4 hX0 hX2 hf1 hb0 ⟨B₁, hb1⟩
  dsimp only at h_exp
  have h_split :
      ∫ ω, normalSteinOp f (W ω) ∂P =
        -(∫ ω, (1 / Real.sqrt n) *
            ∑ i : Fin n,
              X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) ∂P) +
          ((∫ ω, deriv f (W ω) ∂P) -
            ∫ ω, (1 / Real.sqrt n) *
              ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) ∂P) := by
    change ∫ ω, (deriv f (W ω) - W ω * f (W ω)) ∂P = _
    rw [integral_sub h_int_dfW h_int_WfW, h_exp]
    ring
  have h_tri :
      |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        |∫ ω, (1 / Real.sqrt n) *
            ∑ i : Fin n,
              X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) ∂P| +
          |(∫ ω, deriv f (W ω) ∂P) -
            ∫ ω, (1 / Real.sqrt n) *
              ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) ∂P| := by
    rw [h_split]
    exact (abs_add_le _ _).trans (by rw [abs_neg])
  -- Bound the first (Taylor remainder) term
  have h_bound1 :
      |∫ ω, (1 / Real.sqrt n) *
          ∑ i : Fin n,
            X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) ∂P| ≤
        B₂ / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := by
    have h_dom_int :
        Integrable
          (fun ω ↦ B₂ / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) * ∑ i : Fin n, |X i ω| ^ 3) P :=
      (integrable_finsetSum Finset.univ fun i _ ↦ hX_cube i).const_mul _
    have h_le_int :
        ‖∫ ω, (1 / Real.sqrt n) *
            ∑ i : Fin n,
              X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) ∂P‖ ≤
          ∫ ω, B₂ / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) * ∑ i : Fin n, |X i ω| ^ 3 ∂P := by
      refine norm_integral_le_of_norm_le h_dom_int (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (one_div_pos.mpr hsqrt_pos)]
      have h_sum_le :
          |∑ i : Fin n,
              X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))| ≤
            ∑ i : Fin n, (B₂ / (2 * (n : ℝ))) * |X i ω| ^ 3 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        rw [abs_mul]
        have htay := abs_sub_deriv_mul_le_half_sq hf1 hf2 hb2 (W ω) (W_i i ω)
        have hmul := mul_le_mul_of_nonneg_left htay (abs_nonneg (X i ω))
        refine hmul.trans_eq ?_
        rw [h_diff i ω, div_pow, Real.sq_sqrt hn_nonneg, ← sq_abs]
        ring
      calc
        (1 / Real.sqrt n) *
            |∑ i : Fin n,
              X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))| ≤
          (1 / Real.sqrt n) * ∑ i : Fin n, (B₂ / (2 * (n : ℝ))) * |X i ω| ^ 3 :=
          mul_le_mul_of_nonneg_left h_sum_le (one_div_nonneg.mpr hsqrt_pos.le)
        _ = B₂ / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) * ∑ i : Fin n, |X i ω| ^ 3 := by
          rw [← Finset.mul_sum, h_rpow]
          field_simp [hn_pos.ne', hsqrt_pos.ne']
    rw [Real.norm_eq_abs] at h_le_int
    refine h_le_int.trans_eq ?_
    rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ hX_cube i]
  -- Bound the second (quadratic variation / variance) term
  have h_bound2 :
      |(∫ ω, deriv f (W ω) ∂P) -
          ∫ ω, (1 / Real.sqrt n) *
            ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) ∂P| ≤
        B₁ / (n : ℝ) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) := by
    let Z : Fin n → Ω → ℝ := fun i ω ↦ X i ω ^ 2
    let Zsum : Ω → ℝ := ∑ i ∈ Finset.univ, Z i
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω ^ 2 - 1)
    have hZ_memLp : ∀ i : Fin n, MemLp (Z i) 2 P :=
      fun i ↦ memLp_two_sq_of_memLp_four (hX4 i)
    have hS_memLp : MemLp S 2 P := by
      have h_sub : ∀ i : Fin n, MemLp (fun ω ↦ X i ω ^ 2 - 1) 2 P :=
        fun i ↦ (hZ_memLp i).sub (memLp_const 1)
      exact memLp_finsetSum Finset.univ fun i _ ↦ h_sub i
    have hS_abs_int : Integrable (fun ω ↦ |S ω|) P :=
      (memLp_one_iff_integrable.mp (hS_memLp.mono_exponent one_le_two)).abs
    rw [← integral_sub h_int_dfW h_int_term2]
    have h_step1 :
        |∫ ω, (deriv f (W ω) -
            (1 / Real.sqrt n) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) ∂P| ≤
          B₁ / (n : ℝ) * ∫ ω, |S ω| ∂P := by
      have h_le_int :
          ‖∫ ω, (deriv f (W ω) -
              (1 / Real.sqrt n) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) ∂P‖ ≤
            ∫ ω, B₁ / (n : ℝ) * |S ω| ∂P := by
        refine norm_integral_le_of_norm_le (hS_abs_int.const_mul (B₁ / (n : ℝ)))
          (Filter.Eventually.of_forall fun ω ↦ ?_)
        have h_alg :
            deriv f (W ω) -
                (1 / Real.sqrt n) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) =
              -(deriv f (W ω) * (S ω / (n : ℝ))) := by
          have h_sum_eq :
              (∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) =
                (deriv f (W ω) / Real.sqrt n) * ∑ i : Fin n, X i ω ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [h_diff i ω]
            ring
          have hS_expand : S ω = (∑ i : Fin n, X i ω ^ 2) - (n : ℝ) := by
            dsimp only [S]
            rw [Finset.sum_sub_distrib]
            simp
          rw [h_sum_eq, hS_expand]
          have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn_nonneg
          field_simp [hn_pos.ne', hsqrt_pos.ne']
          rw [sq, hsq]
          ring
        rw [h_alg, Real.norm_eq_abs, abs_neg, abs_mul, abs_div, abs_of_pos hn_pos]
        have h1 :=
          mul_le_mul_of_nonneg_right (hb1 (W ω)) (div_nonneg (abs_nonneg (S ω)) hn_nonneg)
        exact h1.trans_eq (by ring)
      simpa [Real.norm_eq_abs, integral_const_mul] using h_le_int
    have h_var : ∫ ω, S ω ^ 2 ∂P ≤ ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P := by
      have hZsum_meas : AEMeasurable Zsum P :=
        Finset.univ.aemeasurable_sum fun i _ ↦ (hX_meas i).pow_const 2
      have hZsum_exp : P[Zsum] = (n : ℝ) := by
        have h_eq : Zsum = fun ω ↦ ∑ i ∈ Finset.univ, Z i ω := by
          ext ω
          simp [Zsum]
        rw [h_eq, integral_finsetSum Finset.univ fun i _ ↦ hX_sq i]
        simp [hX2]
      have hS_eq_var : ∫ ω, S ω ^ 2 ∂P = variance Zsum P := by
        rw [variance_eq_integral hZsum_meas, hZsum_exp]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        dsimp only [S, Zsum, Z]
        rw [Finset.sum_apply, Finset.sum_sub_distrib]
        simp
      have hZ_indep : iIndepFun Z P := by
        change iIndepFun (fun i ↦ (fun x : ℝ ↦ x ^ 2) ∘ X i) P
        exact h_indep.comp (fun _ x ↦ x ^ 2) fun _ ↦ measurable_id.pow_const 2
      have h_var_sum : variance Zsum P = ∑ i ∈ Finset.univ, variance (Z i) P :=
        IndepFun.variance_sum (fun i _ ↦ hZ_memLp i) fun i _ j _ hij ↦ hZ_indep.indepFun hij
      rw [hS_eq_var, h_var_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hv := variance_le_expectation_sq (μ := P) (hZ_memLp i).aestronglyMeasurable
      refine hv.trans_eq ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
      simp only [Pi.pow_apply, Z]
      ring
    have h_cs : ∫ ω, |S ω| ∂P ≤ Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) :=
      (integral_abs_le_sqrt_integral_sq hS_memLp).trans (Real.sqrt_le_sqrt h_var)
    exact h_step1.trans
      (mul_le_mul_of_nonneg_left h_cs (div_nonneg hB1_nonneg hn_nonneg))
  linarith

/-! ### Supremum over `normalWassersteinClass` and Wasserstein CLT assembly -/

/-- Extended-nonnegative-real supremum bound over `normalWassersteinClass` for
$W = (\sum_{i=1}^n X_i)/\sqrt{n}$, yielding the quantitative right-hand side of Theorem 3.2
(`\label{thm32}`, `SteinIntro.tex:736-742`, proof at `SteinIntro.tex:748-800`). -/
theorem indepSum_iSup_normalWassersteinClass_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    (⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|) ≤
      ENNReal.ofReal
        (1 / (n : ℝ) ^ (3 / 2 : ℝ) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P)) := by
  intro W
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_rpow_pos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have h1 : (2 : ℝ) / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) = 1 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    field_simp [h_rpow_pos.ne']
  have h2 : Real.sqrt (2 / Real.pi) / (n : ℝ) = Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), div_div]
  refine iSup₂_le fun f hf ↦ ENNReal.ofReal_le_ofReal ?_
  rcases hf with ⟨hf1, hf2, hf0, hf1_le, hf2_le⟩
  have h_op :=
    indepSum_normalSteinOp_bound P hn hX_meas h_indep hX4 hX0 hX2
      ⟨hf1, hf2⟩ ⟨2, hf0⟩ hf1_le hf2_le
  dsimp only at h_op
  rw [h1, h2] at h_op
  exact h_op

/-- Assembly helper combining a Stein Wasserstein-1 bound over `normalWassersteinClass` (Theorem 3.1
`\label{thm31}`, `SteinIntro.tex:719-724`) with `indepSum_iSup_normalWassersteinClass_le` to deduce
Theorem 3.2 (`\label{thm32}`, `SteinIntro.tex:736-742`). -/
theorem indepSum_wasserstein_clt_of_stein_bound
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω')
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1)
    (hStein :
      let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
      wassersteinDist (P.map W) (P'.map Z) ≤
        ⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / (n : ℝ) ^ (3 / 2 : ℝ) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P)) :=
  hStein.trans (indepSum_iSup_normalWassersteinClass_le P hn hX_meas h_indep hX4 hX0 hX2)

end SteinMethod
