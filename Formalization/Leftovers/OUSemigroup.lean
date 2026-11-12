/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Leftovers.OrnsteinUhlenbeck
import Formalization.Normal.SteinLemma
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Ornstein–Uhlenbeck Semigroup and Backward Equation (`Formalization.Leftovers.OUSemigroup`)

Develops the analytic properties of the Ornstein–Uhlenbeck transition semigroup
`ouSemigroup t f x := ∫ y, f y ∂ouKernel t x` ($Q_t f(x)$) associated with `ouKernel` from
Remark 3.5 (`SteinIntro.tex:1009-1024`):

* **Mehler representation**: `ouKernel_eq_map_stdNormalLaw`, `ouSemigroup_eq_integral_stdNormalLaw`,
  and `ouSemigroup_eq_mehler` express $Q_t f(x) = \mathbb{E}[f(e^{-t} x + \sqrt{1 - e^{-2t}}\,Z)]$
  for $Z \sim \mathcal{N}(0, 1)$ and $t \ge 0$.
* **Spatial $C^2$ regularity and derivative contraction**: `deriv_ouSemigroup`,
  `deriv_deriv_ouSemigroup`, `contDiff_two_ouSemigroup`, `iSup_abs_deriv_ouSemigroup_le`, and
  `iSup_abs_deriv_deriv_ouSemigroup_le` establish $Q_t : C_b^2(\mathbb{R}) \to C^2(\mathbb{R})$
  with $(Q_t f)' = e^{-t} Q_t(f')$ and $(Q_t f)'' = e^{-2t} Q_t(f'')$.
* **Time continuity and backward Kolmogorov equation**: `ouSemigroup_zero`,
  `continuousOn_ouSemigroup_Ici`, `hasDerivAt_ouSemigroup_time`, and `deriv_ouSemigroup_time`
  prove continuity of $t \mapsto Q_t f(x)$ on $[0, \infty)$ and
  $\partial_t Q_t f(x) = (Q_t f)''(x) - x (Q_t f)'(x)$ for $t > 0$ via Stein's Gaussian
  integration by parts (`integrable_mul_and_integral_eq_deriv_stdNormal`).
* **Ergodic weak convergence**: `tendsto_ouSemigroup_atTop` and
  `tendsto_ouKernel_atTop_stdNormalLaw` prove weak convergence of `ouKernel t x` to `stdNormalLaw`
  as $t \to \infty$ for every starting point $x \in \mathbb{R}$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace SteinMethod

/-- Ornstein–Uhlenbeck transition semigroup $Q_t f(x) := \int f(y)\,d(\mathrm{ouKernel}\,t\,x)(y)$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
noncomputable def ouSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f y ∂ouKernel t x

/-! ### Section 1: Mehler Representation and Initial Condition -/

/-- For $t \ge 0$, `ouKernel t x` is the Gaussian law $\mathcal{N}(e^{-t} x, 1 - e^{-2t})$,
including the degenerate case $t = 0$ where `gaussianReal x 0 = Measure.dirac x`
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem ouKernel_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ouKernel t x =
      gaussianReal (Real.exp (-t) * x) (Real.toNNReal (1 - Real.exp (-2 * t))) := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · rw [ouKernel_of_nonpos le_rfl, Kernel.id_apply]
    simp
  · exact ouKernel_of_pos hpos x

/-- **Mehler representation at the measure level** (Remark 3.5, `SteinIntro.tex:1009-1024`):
for $t \ge 0$ and $x \in \mathbb{R}$, `ouKernel t x` is the pushforward of `stdNormalLaw` under
$z \mapsto e^{-t} x + \sqrt{1 - e^{-2t}}\,z$. -/
theorem ouKernel_eq_map_stdNormalLaw {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    ouKernel t x =
      stdNormalLaw.map
        (fun z : ℝ ↦ Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) := by
  set m : ℝ := Real.exp (-t) * x
  set s : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  have h1m : 0 ≤ 1 - Real.exp (-2 * t) := by
    have hexp : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  calc
    ouKernel t x
      = gaussianReal (s * 0 + m) (NNReal.mk (s ^ 2) (sq_nonneg s) * 1) := by
          rw [ouKernel_of_nonneg ht x]
          congr 1
          · ring
          · ext
            rw [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one,
              Real.coe_toNNReal _ h1m, Real.sq_sqrt h1m]
    _ = ((gaussianReal 0 1).map (s * ·)).map (m + ·) := by
          rw [gaussianReal_map_const_mul, gaussianReal_map_const_add]
    _ = stdNormalLaw.map (fun z : ℝ ↦ m + s * z) := by
          rw [stdNormalLaw, Measure.map_map (measurable_const_add m) (measurable_const_mul s)]
          rfl

/-- **Mehler representation of the O-U semigroup** (Remark 3.5, `SteinIntro.tex:1009-1024`):
for $t \ge 0$, $Q_t f(x) = \int f(e^{-t} x + \sqrt{1 - e^{-2t}}\,z)\,d\mathcal{N}(0, 1)(z)$. -/
theorem ouSemigroup_eq_integral_stdNormalLaw {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ} {x : ℝ}
    (hf : AEStronglyMeasurable f (ouKernel t x)) :
    ouSemigroup t f x =
      ∫ z, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) ∂stdNormalLaw := by
  have hm : AEMeasurable
      (fun z : ℝ ↦ Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) stdNormalLaw :=
    (measurable_const.add (measurable_const.mul measurable_id)).aemeasurable
  have hf_map : AEStronglyMeasurable f
      (stdNormalLaw.map
        (fun z : ℝ ↦ Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)) := by
    rwa [← ouKernel_eq_map_stdNormalLaw ht x]
  rw [ouSemigroup, ouKernel_eq_map_stdNormalLaw ht x, integral_map hm hf_map]

/-- Mehler representation of `ouSemigroup t f x` for measurable `f` and $t \ge 0$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem ouSemigroup_eq_mehler {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : Measurable f) (x : ℝ) :
    ouSemigroup t f x =
      ∫ z, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z) ∂stdNormalLaw :=
  ouSemigroup_eq_integral_stdNormalLaw ht hf.aestronglyMeasurable

/-- For $t \le 0$, `ouSemigroup t f = f` (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem ouSemigroup_of_nonpos {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) :
    ouSemigroup t f = f := by
  ext x
  rw [ouSemigroup, ouKernel_of_nonpos ht, Kernel.id_apply, integral_dirac]

/-- Initial condition $Q_0 f = f$ (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
@[simp]
theorem ouSemigroup_zero (f : ℝ → ℝ) : ouSemigroup 0 f = f :=
  ouSemigroup_of_nonpos le_rfl f

/-! ### Section 2: Gaussian Moment Dominance and Linear-Growth Helpers -/

private lemma integrable_abs_stdNormalLaw : Integrable (fun z : ℝ ↦ |z|) stdNormalLaw := by
  have hid : Integrable (fun z : ℝ ↦ z) stdNormalLaw := by
    rw [stdNormalLaw]
    exact (memLp_id_gaussianReal 1).integrable le_rfl
  simpa only [Real.norm_eq_abs] using hid.norm

private lemma abs_le_linear_of_deriv_le {g : ℝ → ℝ} (hg : Differentiable ℝ g) {B : ℝ}
    (hB : ∀ u : ℝ, |deriv g u| ≤ B) (u : ℝ) :
    |g u| ≤ |g 0| + max B 0 * |u| := by
  have hderiv_le : ∀ w ∈ (univ : Set ℝ), ‖deriv g w‖ ≤ max B 0 := fun w _ ↦ by
    rw [Real.norm_eq_abs]
    exact (hB w).trans (le_max_left B 0)
  have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun w _ ↦ hg w) hderiv_le (mem_univ (0 : ℝ)) (mem_univ u)
  simp only [sub_zero, Real.norm_eq_abs] at hmvt
  have htri : |g u| - |g 0| ≤ |g u - g 0| := abs_sub_abs_le_abs_sub (g u) (g 0)
  linarith

private lemma ouStdDev_le_one (t : ℝ) :
    Real.sqrt (1 - Real.exp (-2 * t)) ≤ 1 :=
  Real.sqrt_le_one.mpr (by have := Real.exp_pos (-2 * t); linarith)

private lemma abs_ouAffine_le {t : ℝ} (ht : 0 ≤ t) (x z : ℝ) :
    |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| ≤ |x| + |z| := by
  have hexp_le : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp_pos : 0 ≤ Real.exp (-t) := (Real.exp_pos (-t)).le
  have hs_nonneg : 0 ≤ Real.sqrt (1 - Real.exp (-2 * t)) := Real.sqrt_nonneg _
  have hs_le : Real.sqrt (1 - Real.exp (-2 * t)) ≤ 1 := ouStdDev_le_one t
  calc
    |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z|
      ≤ |Real.exp (-t) * x| + |Real.sqrt (1 - Real.exp (-2 * t)) * z| := abs_add_le _ _
    _ = Real.exp (-t) * |x| + Real.sqrt (1 - Real.exp (-2 * t)) * |z| := by
        rw [abs_mul, abs_of_nonneg hexp_pos, abs_mul, abs_of_nonneg hs_nonneg]
    _ ≤ 1 * |x| + 1 * |z| :=
        add_le_add (mul_le_mul_of_nonneg_right hexp_le (abs_nonneg x))
          (mul_le_mul_of_nonneg_right hs_le (abs_nonneg z))
    _ = |x| + |z| := by ring

private lemma integrable_affine_stdNormalLaw {g : ℝ → ℝ} (hg : Continuous g)
    {A B : ℝ} (hlin : ∀ u : ℝ, |g u| ≤ A + B * |u|) (a b : ℝ) :
    Integrable (fun z : ℝ ↦ g (a + b * z)) stdNormalLaw := by
  let A' : ℝ := max A 0
  let B' : ℝ := max B 0
  have hB'_nn : 0 ≤ B' := le_max_right B 0
  have hdom : Integrable (fun z : ℝ ↦ (A' + B' * |a|) + (B' * |b|) * |z|) stdNormalLaw :=
    (integrable_const _).add (integrable_abs_stdNormalLaw.const_mul _)
  refine hdom.mono' (hg.comp (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_eq_abs]
  have hu := hlin (a + b * z)
  have hAA' : A ≤ A' := le_max_left A 0
  have hBB' : B * |a + b * z| ≤ B' * |a + b * z| :=
    mul_le_mul_of_nonneg_right (le_max_left B 0) (abs_nonneg _)
  have habz : |a + b * z| ≤ |a| + |b| * |z| := by
    calc |a + b * z| ≤ |a| + |b * z| := abs_add_le _ _
      _ = |a| + |b| * |z| := by rw [abs_mul]
  have hmul : B' * |a + b * z| ≤ B' * (|a| + |b| * |z|) :=
    mul_le_mul_of_nonneg_left habz hB'_nn
  linarith

private lemma continuous_ouSemigroup_of_linear_growth {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℝ}
    (hg : Continuous g) (hlin : ∃ A B : ℝ, ∀ u : ℝ, |g u| ≤ A + B * |u|) :
    Continuous (ouSemigroup t g) := by
  rcases hlin with ⟨A, B, hAB⟩
  let A' : ℝ := max A 0
  let B' : ℝ := max B 0
  have hB'_nn : 0 ≤ B' := le_max_right B 0
  let s : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  rw [continuous_iff_continuousAt]
  intro x₀
  have hEq : ouSemigroup t g = fun x ↦ ∫ z, g (Real.exp (-t) * x + s * z) ∂stdNormalLaw := by
    ext x
    exact ouSemigroup_eq_mehler ht hg.measurable x
  rw [hEq, ContinuousAt]
  let bound : ℝ → ℝ := fun z ↦ (A' + B' * (|x₀| + 1)) + B' * |z|
  have hbound_int : Integrable bound stdNormalLaw :=
    (integrable_const _).add (integrable_abs_stdNormalLaw.const_mul B')
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
  · exact Eventually.of_forall fun x ↦ (hg.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ zero_lt_one] with x hx
    refine Eventually.of_forall fun z ↦ ?_
    rw [Real.norm_eq_abs]
    have hx_lt : |x - x₀| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hx
    have hx_le : |x| ≤ |x₀| + 1 := by
      have htri : |x| - |x₀| ≤ |x - x₀| := abs_sub_abs_le_abs_sub x x₀
      linarith
    have haff : |Real.exp (-t) * x + s * z| ≤ |x₀| + 1 + |z| :=
      (abs_ouAffine_le ht x z).trans (by linarith)
    have hg_le : |g (Real.exp (-t) * x + s * z)| ≤ A' + B' * |Real.exp (-t) * x + s * z| := by
      have h1 := hAB (Real.exp (-t) * x + s * z)
      have h2 : A ≤ A' := le_max_left A 0
      have h3 : B * |Real.exp (-t) * x + s * z| ≤ B' * |Real.exp (-t) * x + s * z| :=
        mul_le_mul_of_nonneg_right (le_max_left B 0) (abs_nonneg _)
      linarith
    have hmul : B' * |Real.exp (-t) * x + s * z| ≤ B' * (|x₀| + 1 + |z|) :=
      mul_le_mul_of_nonneg_left haff hB'_nn
    dsimp only [bound]
    linarith
  · exact Eventually.of_forall fun z ↦
      ((hg.comp (by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-t) * x + s * z)).continuousAt)

/-! ### Section 3: Spatial $C^2$ Regularity and Derivative Contraction -/

/-- Spatial differentiation under the O-U semigroup for $C^1$ functions with bounded derivative:
$x \mapsto Q_t f(x)$ has derivative $e^{-t} Q_t(f')(x)$ for $t \ge 0$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem hasDerivAt_ouSemigroup_space {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hf' : ∃ B : ℝ, ∀ u : ℝ, |deriv f u| ≤ B) (x : ℝ) :
    HasDerivAt (ouSemigroup t f) (Real.exp (-t) * ouSemigroup t (deriv f) x) x := by
  rcases hf' with ⟨B, hB⟩
  let M : ℝ := max B 0
  let s : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  let F : ℝ → ℝ → ℝ := fun y z ↦ f (Real.exp (-t) * y + s * z)
  let F' : ℝ → ℝ → ℝ := fun y z ↦ deriv f (Real.exp (-t) * y + s * z) * Real.exp (-t)
  have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hf'_cont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hEq : ouSemigroup t f = fun y ↦ ∫ z, F y z ∂stdNormalLaw := by
    ext y
    exact ouSemigroup_eq_mehler ht hf.continuous.measurable y
  have hF_int : Integrable (F x) stdNormalLaw :=
    integrable_affine_stdNormalLaw hf.continuous (abs_le_linear_of_deriv_le hf_diff hB)
      (Real.exp (-t) * x) s
  have hF'_meas : AEStronglyMeasurable (F' x) stdNormalLaw :=
    ((hf'_cont.comp (by fun_prop)).mul continuous_const).aestronglyMeasurable
  have h_bound :
      ∀ᵐ z ∂stdNormalLaw, ∀ y ∈ (univ : Set ℝ), ‖F' y z‖ ≤ M * Real.exp (-t) := by
    refine Eventually.of_forall fun z y _ ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (-t))]
    exact mul_le_mul_of_nonneg_right ((hB _).trans (le_max_left B 0)) (Real.exp_pos (-t)).le
  have h_diff :
      ∀ᵐ z ∂stdNormalLaw, ∀ y ∈ (univ : Set ℝ), HasDerivAt (F · z) (F' y z) y := by
    refine Eventually.of_forall fun z y _ ↦ ?_
    have hinner : HasDerivAt (fun y : ℝ ↦ Real.exp (-t) * y + s * z) (Real.exp (-t)) y := by
      simpa using ((hasDerivAt_id y).const_mul (Real.exp (-t))).add_const (s * z)
    exact (hf_diff (Real.exp (-t) * y + s * z)).hasDerivAt.comp y hinner
  have hF_meas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) stdNormalLaw :=
    Eventually.of_forall fun y ↦ (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    Filter.univ_mem hF_meas hF_int hF'_meas h_bound (integrable_const _) h_diff
  rw [hEq]
  refine hderiv.congr_deriv ?_
  calc
    (∫ z, F' x z ∂stdNormalLaw)
      = Real.exp (-t) * ∫ z, deriv f (Real.exp (-t) * x + s * z) ∂stdNormalLaw := by
          simp only [F', mul_comm (deriv f _) (Real.exp (-t)), integral_const_mul]
    _ = Real.exp (-t) * ouSemigroup t (deriv f) x := by
          rw [ouSemigroup_eq_mehler ht hf'_cont.measurable x]

/-- Spatial derivative formula $(Q_t f)'(x) = e^{-t} Q_t(f')(x)$ for $t \ge 0$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem deriv_ouSemigroup {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf' : ∃ B : ℝ, ∀ u : ℝ, |deriv f u| ≤ B) (x : ℝ) :
    deriv (ouSemigroup t f) x = Real.exp (-t) * ouSemigroup t (deriv f) x :=
  (hasDerivAt_ouSemigroup_space ht hf hf' x).deriv

/-- Spatial $C^1$ preservation: if $f \in C^1(\mathbb{R})$ has bounded derivative and $t \ge 0$,
then $Q_t f \in C^1(\mathbb{R})$ (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem contDiff_one_ouSemigroup {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hf' : ∃ B : ℝ, ∀ u : ℝ, |deriv f u| ≤ B) :
    ContDiff ℝ 1 (ouSemigroup t f) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_ouSemigroup_space ht hf hf' x).differentiableAt, ?_⟩
  have hEq : deriv (ouSemigroup t f) = fun x ↦ Real.exp (-t) * ouSemigroup t (deriv f) x :=
    funext (deriv_ouSemigroup ht hf hf')
  rw [hEq]
  rcases hf' with ⟨B, hB⟩
  have hcont_g : Continuous (ouSemigroup t (deriv f)) :=
    continuous_ouSemigroup_of_linear_growth ht (hf.continuous_deriv le_rfl)
      ⟨B, 0, fun u ↦ by simpa using hB u⟩
  exact continuous_const.mul hcont_g

/-- Pointwise first-derivative contraction $|(Q_t f)'(x)| \le e^{-t} B$ when $|f'| \le B$ and
$t \ge 0$ (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem abs_deriv_ouSemigroup_le {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {B : ℝ} (hB : ∀ u : ℝ, |deriv f u| ≤ B) (x : ℝ) :
    |deriv (ouSemigroup t f) x| ≤ Real.exp (-t) * B := by
  have hf'_cont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  let s : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  have hf'_int : Integrable
      (fun z : ℝ ↦ deriv f (Real.exp (-t) * x + s * z)) stdNormalLaw :=
    integrable_affine_stdNormalLaw hf'_cont (A := B) (B := 0)
      (fun u ↦ by simpa using hB u) _ _
  rw [deriv_ouSemigroup ht hf ⟨B, hB⟩ x, abs_mul, abs_of_pos (Real.exp_pos (-t)),
    ouSemigroup_eq_mehler ht hf'_cont.measurable x]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos (-t)).le
  calc
    |∫ z, deriv f (Real.exp (-t) * x + s * z) ∂stdNormalLaw|
      ≤ ∫ z, |deriv f (Real.exp (-t) * x + s * z)| ∂stdNormalLaw :=
          abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℝ, B ∂stdNormalLaw :=
          integral_mono hf'_int.abs (integrable_const B) fun z ↦ hB _
    _ = B := by rw [integral_const, probReal_univ, one_smul]

/-- Supremum first-derivative contraction $\sup_x |(Q_t f)'(x)| \le \sup_x |f'(x)|$ for $t \ge 0$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem iSup_abs_deriv_ouSemigroup_le {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hf' : ∃ B : ℝ, ∀ u : ℝ, |deriv f u| ≤ B) :
    (⨆ x : ℝ, |deriv (ouSemigroup t f) x|) ≤ ⨆ x : ℝ, |deriv f x| := by
  rcases hf' with ⟨B, hB⟩
  have hbdd : BddAbove (range fun u : ℝ ↦ |deriv f u|) :=
    ⟨B, by rintro _ ⟨u, rfl⟩; exact hB u⟩
  let S : ℝ := ⨆ u : ℝ, |deriv f u|
  have hS : ∀ u : ℝ, |deriv f u| ≤ S := fun u ↦ le_ciSup hbdd u
  have hS_nn : 0 ≤ S := (abs_nonneg (deriv f 0)).trans (hS 0)
  have hexp_le : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ciSup_le fun x ↦ ?_
  calc
    |deriv (ouSemigroup t f) x| ≤ Real.exp (-t) * S := abs_deriv_ouSemigroup_le ht hf hS x
    _ ≤ 1 * S := mul_le_mul_of_nonneg_right hexp_le hS_nn
    _ = S := one_mul S

private lemma contDiff_one_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (deriv f) := by
  have hf' : ContDiff ℝ (1 + 1) f := hf
  exact (contDiff_succ_iff_deriv.mp hf').2.2

/-- Spatial second-derivative formula $(Q_t f)''(x) = e^{-2t} Q_t(f'')(x)$ for $t \ge 0$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem deriv_deriv_ouSemigroup {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf' : ∃ B₁ : ℝ, ∀ u : ℝ, |deriv f u| ≤ B₁)
    (hf'' : ∃ B₂ : ℝ, ∀ u : ℝ, |deriv (deriv f) u| ≤ B₂) (x : ℝ) :
    deriv (deriv (ouSemigroup t f)) x =
      Real.exp (-2 * t) * ouSemigroup t (deriv (deriv f)) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le one_le_two
  have hdf1 : ContDiff ℝ 1 (deriv f) := contDiff_one_deriv_of_contDiff_two hf
  have hEq : deriv (ouSemigroup t f) = fun y ↦ Real.exp (-t) * ouSemigroup t (deriv f) y :=
    funext (deriv_ouSemigroup ht hf1 hf')
  have h2 : HasDerivAt (deriv (ouSemigroup t f))
      (Real.exp (-t) * (Real.exp (-t) * ouSemigroup t (deriv (deriv f)) x)) x := by
    rw [hEq]
    exact (hasDerivAt_ouSemigroup_space ht hdf1 hf'' x).const_mul (Real.exp (-t))
  rw [h2.deriv, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- Spatial $C^2$ preservation: if $f \in C^2(\mathbb{R})$ has bounded first and second derivatives
and $t \ge 0$, then $Q_t f \in C^2(\mathbb{R})$ (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem contDiff_two_ouSemigroup {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf' : ∃ B₁ : ℝ, ∀ u : ℝ, |deriv f u| ≤ B₁)
    (hf'' : ∃ B₂ : ℝ, ∀ u : ℝ, |deriv (deriv f) u| ≤ B₂) :
    ContDiff ℝ 2 (ouSemigroup t f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le one_le_two
  have hdf1 : ContDiff ℝ 1 (deriv f) := contDiff_one_deriv_of_contDiff_two hf
  change ContDiff ℝ (1 + 1) (ouSemigroup t f)
  rw [contDiff_succ_iff_deriv]
  refine ⟨(contDiff_one_ouSemigroup ht hf1 hf').differentiable one_ne_zero,
    fun hω ↦ by simp at hω, ?_⟩
  have hEq : deriv (ouSemigroup t f) = fun y ↦ Real.exp (-t) * ouSemigroup t (deriv f) y :=
    funext (deriv_ouSemigroup ht hf1 hf')
  rw [hEq]
  exact contDiff_const.mul (contDiff_one_ouSemigroup ht hdf1 hf'')

/-- Pointwise second-derivative contraction $|(Q_t f)''(x)| \le e^{-2t} B_2$ when $|f''| \le B_2$
and $t \ge 0$ (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem abs_deriv_deriv_ouSemigroup_le {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hf' : ∃ B₁ : ℝ, ∀ u : ℝ, |deriv f u| ≤ B₁)
    {B₂ : ℝ} (hB₂ : ∀ u : ℝ, |deriv (deriv f) u| ≤ B₂) (x : ℝ) :
    |deriv (deriv (ouSemigroup t f)) x| ≤ Real.exp (-2 * t) * B₂ := by
  have hdf1 : ContDiff ℝ 1 (deriv f) := contDiff_one_deriv_of_contDiff_two hf
  have hf''_cont : Continuous (deriv (deriv f)) := hdf1.continuous_deriv le_rfl
  let s : ℝ := Real.sqrt (1 - Real.exp (-2 * t))
  have hf''_int : Integrable
      (fun z : ℝ ↦ deriv (deriv f) (Real.exp (-t) * x + s * z)) stdNormalLaw :=
    integrable_affine_stdNormalLaw hf''_cont (A := B₂) (B := 0)
      (fun u ↦ by simpa using hB₂ u) _ _
  rw [deriv_deriv_ouSemigroup ht hf hf' ⟨B₂, hB₂⟩ x, abs_mul,
    abs_of_pos (Real.exp_pos (-2 * t)), ouSemigroup_eq_mehler ht hf''_cont.measurable x]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos (-2 * t)).le
  calc
    |∫ z, deriv (deriv f) (Real.exp (-t) * x + s * z) ∂stdNormalLaw|
      ≤ ∫ z, |deriv (deriv f) (Real.exp (-t) * x + s * z)| ∂stdNormalLaw :=
          abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℝ, B₂ ∂stdNormalLaw :=
          integral_mono hf''_int.abs (integrable_const B₂) fun z ↦ hB₂ _
    _ = B₂ := by rw [integral_const, probReal_univ, one_smul]

/-- Supremum second-derivative contraction $\sup_x |(Q_t f)''(x)| \le \sup_x |f''(x)|$ for $t \ge 0$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem iSup_abs_deriv_deriv_ouSemigroup_le {t : ℝ} (ht : 0 ≤ t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hf' : ∃ B₁ : ℝ, ∀ u : ℝ, |deriv f u| ≤ B₁)
    (hf'' : ∃ B₂ : ℝ, ∀ u : ℝ, |deriv (deriv f) u| ≤ B₂) :
    (⨆ x : ℝ, |deriv (deriv (ouSemigroup t f)) x|) ≤ ⨆ x : ℝ, |deriv (deriv f) x| := by
  rcases hf'' with ⟨B₂, hB₂⟩
  have hbdd : BddAbove (range fun u : ℝ ↦ |deriv (deriv f) u|) :=
    ⟨B₂, by rintro _ ⟨u, rfl⟩; exact hB₂ u⟩
  let S : ℝ := ⨆ u : ℝ, |deriv (deriv f) u|
  have hS : ∀ u : ℝ, |deriv (deriv f) u| ≤ S := fun u ↦ le_ciSup hbdd u
  have hS_nn : 0 ≤ S := (abs_nonneg (deriv (deriv f) 0)).trans (hS 0)
  have hexp_le : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  refine ciSup_le fun x ↦ ?_
  calc
    |deriv (deriv (ouSemigroup t f)) x|
      ≤ Real.exp (-2 * t) * S := abs_deriv_deriv_ouSemigroup_le ht hf hf' hS x
    _ ≤ 1 * S := mul_le_mul_of_nonneg_right hexp_le hS_nn
    _ = S := one_mul S

/-! ### Section 4: Time Continuity on `[0, ∞)` and Backward Kolmogorov Equation -/

/-- Continuity of $t \mapsto Q_t f(x)$ on $[0, \infty)$ for any continuous $f$ of at most linear
growth (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem continuousOn_ouSemigroup_Ici {f : ℝ → ℝ} (hf : Continuous f)
    (hlin : ∃ A B : ℝ, ∀ u : ℝ, |f u| ≤ A + B * |u|) (x : ℝ) :
    ContinuousOn (fun t : ℝ ↦ ouSemigroup t f x) (Ici 0) := by
  rcases hlin with ⟨A, B, hAB⟩
  let A' : ℝ := max A 0
  let B' : ℝ := max B 0
  have hB'_nn : 0 ≤ B' := le_max_right B 0
  let F : ℝ → ℝ → ℝ := fun t z ↦
    f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
  let bound : ℝ → ℝ := fun z ↦ (A' + B' * |x|) + B' * |z|
  have hbound_int : Integrable bound stdNormalLaw :=
    (integrable_const _).add (integrable_abs_stdNormalLaw.const_mul B')
  intro t₀ (ht₀ : 0 ≤ t₀)
  rw [ContinuousWithinAt]
  have hlim : Tendsto (fun t : ℝ ↦ ∫ z, F t z ∂stdNormalLaw)
      (𝓝[Ici 0] t₀) (𝓝 (∫ z, F t₀ z ∂stdNormalLaw)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
    · exact Eventually.of_forall fun t ↦ (hf.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
      refine Eventually.of_forall fun z ↦ ?_
      rw [Real.norm_eq_abs]
      have haff := abs_ouAffine_le ht x z
      have h1 := hAB (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
      have h2 : A ≤ A' := le_max_left A 0
      have h3 : B * |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| ≤
          B' * |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| :=
        mul_le_mul_of_nonneg_right (le_max_left B 0) (abs_nonneg _)
      have h4 : B' * |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| ≤
          B' * (|x| + |z|) := mul_le_mul_of_nonneg_left haff hB'_nn
      dsimp only [bound]
      linarith
    · refine Eventually.of_forall fun z ↦ ?_
      have hcont : Continuous (fun t : ℝ ↦ F t z) := hf.comp (by fun_prop)
      exact hcont.continuousWithinAt.tendsto
  rw [ouSemigroup_eq_mehler ht₀ hf.measurable x]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
  exact (ouSemigroup_eq_mehler ht hf.measurable x).symm

/-- Continuity of $t \mapsto Q_t f(x)$ on $[0, \infty)$ for any $f \in C^1(\mathbb{R})$ with
bounded derivative (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem continuousOn_ouSemigroup_Ici_of_contDiff_one {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hf' : ∃ B : ℝ, ∀ u : ℝ, |deriv f u| ≤ B) (x : ℝ) :
    ContinuousOn (fun t : ℝ ↦ ouSemigroup t f x) (Ici 0) := by
  rcases hf' with ⟨B, hB⟩
  exact continuousOn_ouSemigroup_Ici hf.continuous
    ⟨|f 0|, max B 0, abs_le_linear_of_deriv_le (hf.differentiable one_ne_zero) hB⟩ x

private lemma hasDerivAt_ouStdDev {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun u : ℝ ↦ Real.sqrt (1 - Real.exp (-2 * u)))
      (Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s))) s := by
  have hexp_lt : Real.exp (-2 * s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hrad_pos : 0 < 1 - Real.exp (-2 * s) := by linarith
  have hsqrt_ne : Real.sqrt (1 - Real.exp (-2 * s)) ≠ 0 := (Real.sqrt_pos.mpr hrad_pos).ne'
  have h1 : HasDerivAt (fun u : ℝ ↦ -2 * u) (-2) s := by
    simpa using (hasDerivAt_id s).const_mul (-2 : ℝ)
  have h2 : HasDerivAt (fun u : ℝ ↦ 1 - Real.exp (-2 * u)) (2 * Real.exp (-2 * s)) s :=
    (h1.exp.const_sub 1).congr_deriv (by ring)
  exact (h2.sqrt hrad_pos.ne').congr_deriv (by field_simp [hsqrt_ne])

/-- **Backward Kolmogorov Equation for the Ornstein–Uhlenbeck Semigroup**
(Remark 3.5, `SteinIntro.tex:1009-1024`): for $t > 0$ and $f \in C^2(\mathbb{R})$ with bounded
first and second derivatives,
$$\frac{d}{dt} Q_t f(x) = (Q_t f)''(x) - x (Q_t f)'(x).$$ -/
theorem hasDerivAt_ouSemigroup_time {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hf' : ∃ B₁ : ℝ, ∀ u : ℝ, |deriv f u| ≤ B₁)
    (hf'' : ∃ B₂ : ℝ, ∀ u : ℝ, |deriv (deriv f) u| ≤ B₂) (x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ouSemigroup s f x)
      (deriv (deriv (ouSemigroup t f)) x - x * deriv (ouSemigroup t f) x) t := by
  rcases hf' with ⟨B₁, hB₁⟩
  rcases hf'' with ⟨B₂, hB₂⟩
  have hf1 : ContDiff ℝ 1 f := hf.of_le one_le_two
  have hdf1 : ContDiff ℝ 1 (deriv f) := contDiff_one_deriv_of_contDiff_two hf
  have hf_diff : Differentiable ℝ f := hf1.differentiable one_ne_zero
  have hf'_diff : Differentiable ℝ (deriv f) := hdf1.differentiable one_ne_zero
  have hf'_cont : Continuous (deriv f) := hdf1.continuous
  have hf''_cont : Continuous (deriv (deriv f)) := hdf1.continuous_deriv le_rfl
  let M₁ : ℝ := max B₁ 0
  have hM₁_nn : 0 ≤ M₁ := le_max_right B₁ 0
  let b : ℝ → ℝ := fun s ↦ Real.sqrt (1 - Real.exp (-2 * s))
  let F : ℝ → ℝ → ℝ := fun s z ↦ f (Real.exp (-s) * x + b s * z)
  let F' : ℝ → ℝ → ℝ := fun s z ↦
    deriv f (Real.exp (-s) * x + b s * z) *
      (-Real.exp (-s) * x + (Real.exp (-2 * s) / b s) * z)
  have ht2_pos : 0 < t / 2 := half_pos ht
  have hb_t2_pos : 0 < b (t / 2) := by
    have hexp : Real.exp (-2 * (t / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact Real.sqrt_pos.mpr (by linarith)
  have hs_nhds : Ioi (t / 2) ∈ 𝓝 t := Ioi_mem_nhds (half_lt_self ht)
  have hF_int : Integrable (F t) stdNormalLaw :=
    integrable_affine_stdNormalLaw hf.continuous (abs_le_linear_of_deriv_le hf_diff hB₁) _ _
  have hF'_meas : AEStronglyMeasurable (F' t) stdNormalLaw :=
    ((hf'_cont.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  let bound : ℝ → ℝ := fun z ↦ M₁ * |x| + (M₁ / b (t / 2)) * |z|
  have hbound_int : Integrable bound stdNormalLaw :=
    (integrable_const _).add (integrable_abs_stdNormalLaw.const_mul _)
  have h_bound : ∀ᵐ z ∂stdNormalLaw, ∀ s ∈ Ioi (t / 2), ‖F' s z‖ ≤ bound z := by
    refine Eventually.of_forall fun z s (hs : t / 2 < s) ↦ ?_
    have hs_pos : 0 < s := ht2_pos.trans hs
    have hexp_s_le : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hexp_2s_le : Real.exp (-2 * s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hb_mono : b (t / 2) ≤ b s := by
      refine Real.sqrt_le_sqrt ?_
      have hexp_le : Real.exp (-2 * s) ≤ Real.exp (-2 * (t / 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hb_s_pos : 0 < b s := hb_t2_pos.trans_le hb_mono
    have hdiv_le : Real.exp (-2 * s) / b s ≤ 1 / b (t / 2) := by
      calc
        Real.exp (-2 * s) / b s ≤ 1 / b s :=
          div_le_div_of_nonneg_right hexp_2s_le hb_s_pos.le
        _ ≤ 1 / b (t / 2) :=
          one_div_le_one_div_of_le hb_t2_pos hb_mono
    have hvel_le : |-Real.exp (-s) * x + (Real.exp (-2 * s) / b s) * z| ≤
        |x| + (1 / b (t / 2)) * |z| := by
      calc
        |-Real.exp (-s) * x + (Real.exp (-2 * s) / b s) * z|
          ≤ |-Real.exp (-s) * x| + |(Real.exp (-2 * s) / b s) * z| := abs_add_le _ _
        _ = Real.exp (-s) * |x| + (Real.exp (-2 * s) / b s) * |z| := by
            rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos (-s)), abs_mul,
              abs_of_pos (div_pos (Real.exp_pos (-2 * s)) hb_s_pos)]
        _ ≤ 1 * |x| + (1 / b (t / 2)) * |z| :=
            add_le_add (mul_le_mul_of_nonneg_right hexp_s_le (abs_nonneg x))
              (mul_le_mul_of_nonneg_right hdiv_le (abs_nonneg z))
        _ = |x| + (1 / b (t / 2)) * |z| := by ring
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |deriv f (Real.exp (-s) * x + b s * z)| *
          |-Real.exp (-s) * x + (Real.exp (-2 * s) / b s) * z|
        ≤ M₁ * (|x| + (1 / b (t / 2)) * |z|) :=
          mul_le_mul ((hB₁ _).trans (le_max_left B₁ 0)) hvel_le (abs_nonneg _) hM₁_nn
      _ = bound z := by
          dsimp only [bound]
          ring
  have h_diff :
      ∀ᵐ z ∂stdNormalLaw, ∀ s ∈ Ioi (t / 2), HasDerivAt (F · z) (F' s z) s := by
    refine Eventually.of_forall fun z s (hs : t / 2 < s) ↦ ?_
    have hs_pos : 0 < s := ht2_pos.trans hs
    have hd1 : HasDerivAt (fun u : ℝ ↦ Real.exp (-u) * x) (-Real.exp (-s) * x) s :=
      (((hasDerivAt_id s).neg.exp).mul_const x).congr_deriv (by simp)
    have hd2 : HasDerivAt (fun u : ℝ ↦ b u * z) ((Real.exp (-2 * s) / b s) * z) s :=
      (hasDerivAt_ouStdDev hs_pos).mul_const z
    exact (hf_diff (Real.exp (-s) * x + b s * z)).hasDerivAt.comp s (hd1.add hd2)
  obtain ⟨_, hderiv_int⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds
    (Eventually.of_forall fun s ↦ (hf.continuous.comp (by fun_prop)).aestronglyMeasurable)
    hF_int hF'_meas h_bound hbound_int h_diff
  have hev :
      (fun s : ℝ ↦ ouSemigroup s f x) =ᶠ[𝓝 t] fun s : ℝ ↦ ∫ z, F s z ∂stdNormalLaw := by
    filter_upwards [hs_nhds] with s (hs : t / 2 < s)
    exact ouSemigroup_eq_mehler (ht2_pos.trans hs).le hf.continuous.measurable x
  refine (hderiv_int.congr_of_eventuallyEq hev).congr_deriv ?_
  let g : ℝ → ℝ := fun z ↦ deriv f (Real.exp (-t) * x + b t * z)
  have hg_cd : ContDiff ℝ 1 g := hdf1.comp (by fun_prop)
  have hg_ac : ∀ u v : ℝ, AbsolutelyContinuousOnInterval g u v :=
    fun u v ↦ hg_cd.contDiffOn.absolutelyContinuousOnInterval
  have hg_deriv : deriv g = fun z ↦ deriv (deriv f) (Real.exp (-t) * x + b t * z) * b t := by
    ext z
    have hinner : HasDerivAt (fun w : ℝ ↦ Real.exp (-t) * x + b t * w) (b t) z := by
      simpa using ((hasDerivAt_id z).const_mul (b t)).const_add (Real.exp (-t) * x)
    exact ((hf'_diff (Real.exp (-t) * x + b t * z)).hasDerivAt.comp z hinner).deriv
  have hg_int : Integrable g stdNormalLaw :=
    integrable_affine_stdNormalLaw hf'_cont (A := B₁) (B := 0)
      (fun u ↦ by simpa using hB₁ u) _ _
  have hfg2_int : Integrable
      (fun z ↦ deriv (deriv f) (Real.exp (-t) * x + b t * z)) stdNormalLaw :=
    integrable_affine_stdNormalLaw hf''_cont (A := B₂) (B := 0)
      (fun u ↦ by simpa using hB₂ u) _ _
  have hg'_int : Integrable (deriv g) stdNormalLaw := by
    rw [hg_deriv]
    exact hfg2_int.mul_const (b t)
  obtain ⟨hzg_int, hibp⟩ := integrable_mul_and_integral_eq_deriv_stdNormal hg_ac hg'_int
  have hbt_pos : 0 < b t := by
    have hexp : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact Real.sqrt_pos.mpr (by linarith)
  have hbt_ne : b t ≠ 0 := hbt_pos.ne'
  have hF'_split : F' t = fun z ↦ (-Real.exp (-t) * x) * g z +
      (Real.exp (-2 * t) / b t) * (z * g z) := by
    ext z
    dsimp only [F', g]
    ring
  have hI1 : (∫ z, g z ∂stdNormalLaw) = ouSemigroup t (deriv f) x :=
    (ouSemigroup_eq_mehler ht.le hf'_cont.measurable x).symm
  have hI2 : (∫ z, deriv (deriv f) (Real.exp (-t) * x + b t * z) ∂stdNormalLaw) =
      ouSemigroup t (deriv (deriv f)) x :=
    (ouSemigroup_eq_mehler ht.le hf''_cont.measurable x).symm
  rw [hF'_split, integral_add (hg_int.const_mul _) (hzg_int.const_mul _),
    integral_const_mul, integral_const_mul, hibp, hg_deriv, integral_mul_const,
    hI1, hI2,
    deriv_deriv_ouSemigroup ht.le hf ⟨B₁, hB₁⟩ ⟨B₂, hB₂⟩ x,
    deriv_ouSemigroup ht.le hf1 ⟨B₁, hB₁⟩ x]
  field_simp [hbt_ne]
  ring

/-- Backward Kolmogorov equation written in terms of `normalSteinOp`:
for $t > 0$, $\partial_t Q_t f(x) = \mathcal{A}((Q_t f)')(x)$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem deriv_ouSemigroup_time {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf' : ∃ B₁ : ℝ, ∀ u : ℝ, |deriv f u| ≤ B₁)
    (hf'' : ∃ B₂ : ℝ, ∀ u : ℝ, |deriv (deriv f) u| ≤ B₂) (x : ℝ) :
    deriv (fun s : ℝ ↦ ouSemigroup s f x) t = normalSteinOp (deriv (ouSemigroup t f)) x :=
  (hasDerivAt_ouSemigroup_time ht hf hf' hf'' x).deriv

/-! ### Section 5: Ergodic Convergence as $t \to \infty$ -/

private lemma tendsto_exp_neg_atTop :
    Tendsto (fun t : ℝ ↦ Real.exp (-t)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot

private lemma tendsto_ouStdDev_atTop :
    Tendsto (fun t : ℝ ↦ Real.sqrt (1 - Real.exp (-2 * t))) atTop (𝓝 1) := by
  have hexp2 : Tendsto (fun t : ℝ ↦ Real.exp (-2 * t)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun t : ℝ ↦ Real.exp (-t) ^ 2) atTop (𝓝 (0 ^ 2)) :=
      tendsto_exp_neg_atTop.pow 2
    refine (by simpa using hsq : Tendsto (fun t : ℝ ↦ Real.exp (-t) ^ 2) atTop (𝓝 0)).congr
      fun t ↦ ?_
    rw [← Real.exp_nat_mul]
    ring_nf
  have h1 : Tendsto (fun t : ℝ ↦ 1 - Real.exp (-2 * t)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hexp2
  simpa [Function.comp_def] using (Real.continuous_sqrt.continuousAt.tendsto.comp h1)

/-- Pointwise ergodic convergence of the O-U semigroup: for any continuous $f$ of at most linear
growth and every $x \in \mathbb{R}$, $Q_t f(x) \to \int f\,d\mathcal{N}(0, 1)$ as $t \to \infty$
(Remark 3.5, `SteinIntro.tex:1018-1019`). -/
theorem tendsto_ouSemigroup_atTop {f : ℝ → ℝ} (hf : Continuous f)
    (hlin : ∃ A B : ℝ, ∀ u : ℝ, |f u| ≤ A + B * |u|) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ ouSemigroup t f x) atTop (𝓝 (∫ z, f z ∂stdNormalLaw)) := by
  rcases hlin with ⟨A, B, hAB⟩
  let A' : ℝ := max A 0
  let B' : ℝ := max B 0
  have hB'_nn : 0 ≤ B' := le_max_right B 0
  let F : ℝ → ℝ → ℝ := fun t z ↦
    f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
  let bound : ℝ → ℝ := fun z ↦ (A' + B' * |x|) + B' * |z|
  have hbound_int : Integrable bound stdNormalLaw :=
    (integrable_const _).add (integrable_abs_stdNormalLaw.const_mul B')
  have hlim : Tendsto (fun t : ℝ ↦ ∫ z, F t z ∂stdNormalLaw)
      atTop (𝓝 (∫ z, f z ∂stdNormalLaw)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
    · exact Eventually.of_forall fun t ↦ (hf.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [Ici_mem_atTop (0 : ℝ)] with t (ht : 0 ≤ t)
      refine Eventually.of_forall fun z ↦ ?_
      rw [Real.norm_eq_abs]
      have haff := abs_ouAffine_le ht x z
      have h1 := hAB (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
      have h2 : A ≤ A' := le_max_left A 0
      have h3 : B * |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| ≤
          B' * |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| :=
        mul_le_mul_of_nonneg_right (le_max_left B 0) (abs_nonneg _)
      have h4 : B' * |Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z| ≤
          B' * (|x| + |z|) := mul_le_mul_of_nonneg_left haff hB'_nn
      dsimp only [bound]
      linarith
    · refine Eventually.of_forall fun z ↦ ?_
      have haff_lim : Tendsto
          (fun t : ℝ ↦ Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * z)
          atTop (𝓝 z) := by
        simpa using (tendsto_exp_neg_atTop.mul_const x).add (tendsto_ouStdDev_atTop.mul_const z)
      exact hf.continuousAt.tendsto.comp haff_lim
  refine hlim.congr' ?_
  filter_upwards [Ici_mem_atTop (0 : ℝ)] with t (ht : 0 ≤ t)
  exact (ouSemigroup_eq_mehler ht hf.measurable x).symm

/-- **Ergodic weak convergence of `ouKernel`** (Remark 3.5, `SteinIntro.tex:1018-1019`):
for every $x \in \mathbb{R}$, `(ouKernel t x).toProbabilityMeasure` converges weakly to
`stdNormalLaw.toProbabilityMeasure` as $t \to \infty$. -/
theorem tendsto_ouKernel_atTop_stdNormalLaw (x : ℝ) :
    Tendsto (fun t : ℝ ↦ (ouKernel t x).toProbabilityMeasure)
      atTop (𝓝 stdNormalLaw.toProbabilityMeasure) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simpa [ouSemigroup] using
    tendsto_ouSemigroup_atTop f.continuous
      ⟨‖f‖, 0, fun u ↦ by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm u⟩ x

end SteinMethod
