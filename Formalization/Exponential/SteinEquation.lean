/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.Basic
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exponential Stein Operator and ODE Solutions (`Formalization.Exponential.SteinEquation`)

Formalizes the characterizing operator and Stein equation theory opening Section 5 of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:2712-2833`):
* **Lemma 5.2** (`\label{lem172}`, eqs. `(5.1)`–`(5.2)` `\label{171}`–`\label{172}`,
  `SteinIntro.tex:2740-2756, 2774-2803`): `lem5_2_formula`, `lem5_2_ode_contAt`,
  `lem5_2_1`, `lem5_2_2` (including Lipschitz and left-derivative regularity per `D2` and `D5-3`),
  plus the Darboux jump witness `not_exists_hasDerivAt_expStein_Iic`.
* **Lemma 5.1(1) & 5.1(2)** (`\label{lem171}`, `SteinIntro.tex:2726-2738, 2804-2821`):
  `lem5_1_1_integrable`, `lem5_1_1`, and `lem5_1_2` (proved without polynomial moment assumptions
  via bounded $C^1$ ramp solutions).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Master Exponential Tail-Integral Bounds & Lipschitz Regularity -/

private noncomputable def expTailTransform (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -Real.exp x * ∫ t in Ioi x, ψ t * Real.exp (-t)

private lemma integrableOn_mul_exp_neg_of_bounded {ψ : ℝ → ℝ} {C : ℝ}
    (hψ_meas : AEStronglyMeasurable ψ volume) (hψ_le : ∀ t : ℝ, |ψ t| ≤ C) (x : ℝ) :
    IntegrableOn (fun t ↦ ψ t * Real.exp (-t)) (Ioi x) volume := by
  refine ((integrableOn_exp_neg_Ioi x).const_mul C).mono'
    (hψ_meas.mul (Continuous.aestronglyMeasurable (by fun_prop))).restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hψ_le t) (Real.exp_pos _).le

private lemma abs_setIntegral_Ioi_mul_exp_neg_le {ψ : ℝ → ℝ} {C : ℝ}
    (hψ_meas : AEStronglyMeasurable ψ volume) (hψ_le : ∀ t : ℝ, |ψ t| ≤ C) (x : ℝ) :
    |∫ t in Ioi x, ψ t * Real.exp (-t)| ≤ C * Real.exp (-x) := by
  have h1 := norm_integral_le_integral_norm (μ := volume.restrict (Ioi x))
    (f := fun t ↦ ψ t * Real.exp (-t))
  rw [Real.norm_eq_abs] at h1
  have h2 : ∫ t in Ioi x, ‖ψ t * Real.exp (-t)‖ ≤ ∫ t in Ioi x, C * Real.exp (-t) := by
    refine setIntegral_mono_on
      (integrableOn_mul_exp_neg_of_bounded hψ_meas hψ_le x).norm
      ((integrableOn_exp_neg_Ioi x).const_mul C) measurableSet_Ioi fun t _ ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hψ_le t) (Real.exp_pos _).le
  rw [integral_const_mul, integral_exp_neg_Ioi] at h2
  exact h1.trans h2

private lemma abs_expTailTransform_le {ψ : ℝ → ℝ} {C : ℝ}
    (hψ_meas : AEStronglyMeasurable ψ volume) (hψ_le : ∀ t : ℝ, |ψ t| ≤ C) (x : ℝ) :
    |expTailTransform ψ x| ≤ C := by
  unfold expTailTransform
  rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos x)]
  calc
    Real.exp x * |∫ t in Ioi x, ψ t * Real.exp (-t)|
      ≤ Real.exp x * (C * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left (abs_setIntegral_Ioi_mul_exp_neg_le hψ_meas hψ_le x)
          (Real.exp_pos x).le
    _ = C * (Real.exp x * Real.exp (-x)) := by ring
    _ = C := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

private lemma lipschitzWith_expTailTransform {ψ : ℝ → ℝ} {C : ℝ}
    (hψ_meas : AEStronglyMeasurable ψ volume) (hψ_le : ∀ t : ℝ, |ψ t| ≤ C) :
    LipschitzWith (Real.toNNReal (2 * C)) (expTailTransform ψ) := by
  have hC0 : 0 ≤ C := (abs_nonneg (ψ 0)).trans (hψ_le 0)
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal (2 * C) (by positivity)]
  have step : ∀ a b : ℝ, a ≤ b →
      |expTailTransform ψ b - expTailTransform ψ a| ≤ 2 * C * (b - a) := by
    intro a b hab
    have hunion : Ioc a b ∪ Ioi b = Ioi a := Ioc_union_Ioi_eq_Ioi hab
    have hdisj : Disjoint (Ioc a b) (Ioi b) := Ioc_disjoint_Ioi le_rfl
    have hsplit : (∫ t in Ioi a, ψ t * Real.exp (-t)) =
        (∫ t in Ioc a b, ψ t * Real.exp (-t)) + ∫ t in Ioi b, ψ t * Real.exp (-t) := by
      rw [← hunion, setIntegral_union hdisj measurableSet_Ioi
        ((integrableOn_mul_exp_neg_of_bounded hψ_meas hψ_le a).mono_set Ioc_subset_Ioi_self)
        (integrableOn_mul_exp_neg_of_bounded hψ_meas hψ_le b)]
    have hJ_le : |∫ t in Ioc a b, ψ t * Real.exp (-t)| ≤ C * (Real.exp (-a) - Real.exp (-b)) := by
      have h1 := norm_integral_le_integral_norm (μ := volume.restrict (Ioc a b))
        (f := fun t ↦ ψ t * Real.exp (-t))
      rw [Real.norm_eq_abs] at h1
      have h2 : ∫ t in Ioc a b, ‖ψ t * Real.exp (-t)‖ ≤ ∫ t in Ioc a b, C * Real.exp (-t) := by
        refine setIntegral_mono_on
          ((integrableOn_mul_exp_neg_of_bounded hψ_meas hψ_le a).mono_set Ioc_subset_Ioi_self).norm
          (((integrableOn_exp_neg_Ioi a).mono_set Ioc_subset_Ioi_self).const_mul C)
          measurableSet_Ioc fun t _ ↦ ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hψ_le t) (Real.exp_pos _).le
      have hexp_split : (∫ t in Ioc a b, Real.exp (-t)) = Real.exp (-a) - Real.exp (-b) := by
        have hs := setIntegral_union hdisj measurableSet_Ioi
          ((integrableOn_exp_neg_Ioi a).mono_set Ioc_subset_Ioi_self) (integrableOn_exp_neg_Ioi b)
        rw [hunion, integral_exp_neg_Ioi, integral_exp_neg_Ioi] at hs
        linarith
      rw [integral_const_mul, hexp_split] at h2
      exact h1.trans h2
    have hI_le := abs_setIntegral_Ioi_mul_exp_neg_le hψ_meas hψ_le b
    have hdiff : expTailTransform ψ b - expTailTransform ψ a =
        -(Real.exp b - Real.exp a) * (∫ t in Ioi b, ψ t * Real.exp (-t)) +
          Real.exp a * ∫ t in Ioc a b, ψ t * Real.exp (-t) := by
      unfold expTailTransform
      rw [hsplit]
      ring
    have hexp_le : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
    have htri : |expTailTransform ψ b - expTailTransform ψ a| ≤
        (Real.exp b - Real.exp a) * |∫ t in Ioi b, ψ t * Real.exp (-t)| +
          Real.exp a * |∫ t in Ioc a b, ψ t * Real.exp (-t)| := by
      rw [hdiff]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hexp_le),
        abs_mul, abs_of_pos (Real.exp_pos a)]
    have halg : (Real.exp b - Real.exp a) * (C * Real.exp (-b)) +
        Real.exp a * (C * (Real.exp (-a) - Real.exp (-b))) =
        2 * C * (1 - Real.exp (-(b - a))) := by
      have h1 : Real.exp b * Real.exp (-b) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h2 : Real.exp a * Real.exp (-a) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h3 : Real.exp a * Real.exp (-b) = Real.exp (-(b - a)) := by
        rw [← Real.exp_add]; ring_nf
      calc
        (Real.exp b - Real.exp a) * (C * Real.exp (-b)) +
            Real.exp a * (C * (Real.exp (-a) - Real.exp (-b)))
          = C * (Real.exp b * Real.exp (-b) + Real.exp a * Real.exp (-a) -
              2 * (Real.exp a * Real.exp (-b))) := by ring
        _ = 2 * C * (1 - Real.exp (-(b - a))) := by rw [h1, h2, h3]; ring
    have h1_sub : 1 - Real.exp (-(b - a)) ≤ b - a := by
      linarith [Real.add_one_le_exp (-(b - a))]
    calc
      |expTailTransform ψ b - expTailTransform ψ a|
        ≤ (Real.exp b - Real.exp a) * (C * Real.exp (-b)) +
            Real.exp a * (C * (Real.exp (-a) - Real.exp (-b))) :=
          htri.trans (add_le_add
            (mul_le_mul_of_nonneg_left hI_le (sub_nonneg.mpr hexp_le))
            (mul_le_mul_of_nonneg_left hJ_le (Real.exp_pos a).le))
      _ = 2 * C * (1 - Real.exp (-(b - a))) := halg
      _ ≤ 2 * C * (b - a) := mul_le_mul_of_nonneg_left h1_sub (by positivity)
  rcases le_total y x with hyx | hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact step y x hyx
  · rw [abs_sub_comm x y, abs_sub_comm (expTailTransform ψ x) (expTailTransform ψ y),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact step x y hxy

private lemma abs_derivWithin_Iic_le_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hLip : LipschitzWith K f) (x : ℝ) :
    |derivWithin f (Iic x) x| ≤ K := by
  by_cases hd : DifferentiableWithinAt ℝ f (Iic x) x
  · have htend := (hasDerivWithinAt_iff_tendsto_slope.mp hd.hasDerivWithinAt).norm
    rw [Iic_sdiff_right] at htend
    rw [← Real.norm_eq_abs]
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with z (hz : z < x)
    have hdist := hLip.dist_le_mul z x
    rw [dist_eq_norm, dist_eq_norm] at hdist
    have hpos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.ne)
    rw [slope_def_module, norm_smul, norm_inv]
    calc
      ‖z - x‖⁻¹ * ‖f z - f x‖ ≤ ‖z - x‖⁻¹ * ((K : ℝ) * ‖z - x‖) :=
        mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = K := by field_simp [hpos.ne']
  · rw [derivWithin_zero_of_not_differentiableWithinAt hd, abs_zero]
    exact NNReal.coe_nonneg K

/-! ### Section 2: Lemma 5.2 — Formula, Continuity-Point ODE, Uniqueness, and Solution Bounds -/

private lemma integrableOn_stein_integrand_Ioi {h : ℝ → ℝ}
    (hLoc : LocallyIntegrable h volume) (hInt : Integrable h stdExpLaw) (x : ℝ) :
    IntegrableOn (fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)) (Ioi x) volume := by
  have hIoi0 : IntegrableOn (fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)) (Ioi 0) volume := by
    have h1 := integrable_stdExpLaw_iff.mp hInt
    have h2 := (integrableOn_exp_neg_Ioi 0).const_mul (stdExpExpect h)
    refine (h1.sub h2).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply]
    ring
  rcases le_or_gt 0 x with hx0 | hx0
  · exact hIoi0.mono_set (Ioi_subset_Ioi hx0)
  · have hunion : Ioc x 0 ∪ Ioi 0 = Ioi x := Ioc_union_Ioi_eq_Ioi hx0.le
    rw [← hunion, integrableOn_union]
    refine ⟨?_, hIoi0⟩
    have hsub : LocallyIntegrable (fun t ↦ h t - stdExpExpect h) volume :=
      hLoc.sub (locallyIntegrable_const (stdExpExpect h))
    have hmul : LocallyIntegrable (fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)) volume :=
      hsub.mul_continuous (by fun_prop)
    exact (hmul.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self

private lemma setIntegral_Ioi_zero_stein_integrand {h : ℝ → ℝ}
    (hInt : Integrable h stdExpLaw) :
    ∫ t in Ioi 0, (h t - stdExpExpect h) * Real.exp (-t) = 0 := by
  have h1 := integrable_stdExpLaw_iff.mp hInt
  have h2 := (integrableOn_exp_neg_Ioi 0).const_mul (stdExpExpect h)
  have heq : (fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)) =
      fun t ↦ h t * Real.exp (-t) - stdExpExpect h * Real.exp (-t) := by
    ext t; ring
  rw [heq, integral_sub h1 h2, ← stdExpExpect_eq_setIntegral_Ioi, integral_const_mul,
    integral_exp_neg_Ioi, neg_zero, Real.exp_zero, mul_one, sub_self]

/-- Boundary value $f_h(0) = 0$ of `expSteinSol h`
(Lemma 5.2 `\label{lem172}`, `SteinIntro.tex:2745`). -/
theorem expSteinSol_zero {h : ℝ → ℝ} (hInt : Integrable h stdExpLaw) :
    expSteinSol h 0 = 0 := by
  rw [expSteinSol, setIntegral_Ioi_zero_stein_integrand hInt, mul_zero]

/-- Interval-integral representation
$f_h(x) = e^x \int_0^x (h(t) - \mathbb{E}[h(Z)]) e^{-t}\,dt$ of `expSteinSol h`
(Lemma 5.2 `\label{lem172}`, eqs. `(5.1)`–`(5.2)`, `SteinIntro.tex:2740-2745, 2774-2779`). -/
theorem expSteinSol_eq_exp_mul_intervalIntegral {h : ℝ → ℝ}
    (hLoc : LocallyIntegrable h volume) (hInt : Integrable h stdExpLaw) (x : ℝ) :
    expSteinSol h x =
      Real.exp x * ∫ t in (0 : ℝ)..x, (h t - stdExpExpect h) * Real.exp (-t) := by
  set g : ℝ → ℝ := fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)
  have h0 : ∫ t in Ioi 0, g t = 0 := setIntegral_Ioi_zero_stein_integrand hInt
  rcases le_total 0 x with hx | hx
  · have hdisj : Disjoint (Ioc 0 x) (Ioi x) := Ioc_disjoint_Ioi le_rfl
    have hunion := setIntegral_union hdisj measurableSet_Ioi
      ((integrableOn_stein_integrand_Ioi hLoc hInt 0).mono_set Ioc_subset_Ioi_self)
      (integrableOn_stein_integrand_Ioi hLoc hInt x)
    rw [Ioc_union_Ioi_eq_Ioi hx, h0] at hunion
    rw [expSteinSol, intervalIntegral.integral_of_le hx]
    have hneg : -(∫ t in Ioi x, g t) = ∫ t in Ioc 0 x, g t := by linarith
    calc
      -Real.exp x * ∫ t in Ioi x, g t = Real.exp x * -(∫ t in Ioi x, g t) := by ring
      _ = Real.exp x * ∫ t in Ioc 0 x, g t := by rw [hneg]
  · have hdisj : Disjoint (Ioc x 0) (Ioi 0) := Ioc_disjoint_Ioi le_rfl
    have hunion := setIntegral_union hdisj measurableSet_Ioi
      ((integrableOn_stein_integrand_Ioi hLoc hInt x).mono_set Ioc_subset_Ioi_self)
      (integrableOn_stein_integrand_Ioi hLoc hInt 0)
    rw [Ioc_union_Ioi_eq_Ioi hx, h0, add_zero] at hunion
    rw [expSteinSol, intervalIntegral.integral_of_ge hx, ← hunion]
    ring

/-- **Lemma 5.2, pointwise ODE at continuity points** (`\label{lem172}`, eq. `(5.1)` `\label{171}`,
`SteinIntro.tex:2740-2745, 2774-2779`; `ISSUE-5.2-ODE`): `expSteinSol h` satisfies
$f_h'(x) - f_h(x) = h(x) - \mathbb{E}[h(Z)]$ at every continuity point $x$ of $h$. -/
theorem lem5_2_ode_contAt {h : ℝ → ℝ}
    (hLoc : LocallyIntegrable h volume) (hInt : Integrable h stdExpLaw)
    {x : ℝ} (hcont : ContinuousAt h x) :
    HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x := by
  set g : ℝ → ℝ := fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)
  have hg_loc : LocallyIntegrable g volume :=
    (hLoc.sub (locallyIntegrable_const _)).mul_continuous (by fun_prop)
  have hg_contAt : ContinuousAt g x :=
    (hcont.sub continuousAt_const).mul (Continuous.continuousAt (by fun_prop))
  have hg_iint : ∀ u : ℝ, IntervalIntegrable g volume 0 u := fun u ↦
    intervalIntegrable_iff.mpr
      ((hg_loc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hg_smaf : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
      (hg_loc.integrableOn_isCompact isCompact_Icc).aestronglyMeasurable⟩
  have hF : HasDerivAt (fun u ↦ ∫ t in (0 : ℝ)..u, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg_iint x) hg_smaf hg_contAt
  have heq : expSteinSol h = fun u ↦ Real.exp u * ∫ t in (0 : ℝ)..u, g t :=
    funext (expSteinSol_eq_exp_mul_intervalIntegral hLoc hInt)
  rw [heq]
  convert (Real.hasDerivAt_exp x).mul hF using 1
  dsimp only [g]
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    Real.exp x * (∫ t in (0 : ℝ)..x, g t) + h x - stdExpExpect h
      = Real.exp x * (∫ t in (0 : ℝ)..x, g t) +
          (h x - stdExpExpect h) * (Real.exp x * Real.exp (-x)) := by rw [hexp]; ring
    _ = Real.exp x * (∫ t in (0 : ℝ)..x, g t) +
          Real.exp x * ((h x - stdExpExpect h) * Real.exp (-x)) := by ring

/-- **Lemma 5.2, solution formula, boundary value, and uniqueness for continuous $h$**
(`\label{lem172}`, eqs. `(5.1)`–`(5.2)` `\label{171}`–`\label{172}`,
`SteinIntro.tex:2740-2745, 2774-2779`). -/
theorem lem5_2_formula :
    (∀ {h : ℝ → ℝ}, LocallyIntegrable h volume → Integrable h stdExpLaw →
      expSteinSol h 0 = 0 ∧
        ∀ x : ℝ, expSteinSol h x =
          Real.exp x * ∫ t in (0 : ℝ)..x, (h t - stdExpExpect h) * Real.exp (-t)) ∧
    (∀ {h : ℝ → ℝ}, Continuous h → Integrable h stdExpLaw →
      (∀ x : ℝ, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x) ∧
        ∀ g : ℝ → ℝ, g 0 = 0 →
          (∀ x : ℝ, HasDerivAt g (g x + h x - stdExpExpect h) x) →
          g = expSteinSol h) := by
  refine ⟨fun hLoc hInt ↦ ⟨expSteinSol_zero hInt,
    expSteinSol_eq_exp_mul_intervalIntegral hLoc hInt⟩, ?_⟩
  intro h hCont hInt
  have hode : ∀ x : ℝ, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x :=
    fun x ↦ lem5_2_ode_contAt hCont.locallyIntegrable hInt hCont.continuousAt
  refine ⟨hode, fun g hg0 hg_ode ↦ ?_⟩
  set d : ℝ → ℝ := fun x ↦ Real.exp (-x) * (g x - expSteinSol h x)
  have hd_deriv : ∀ x : ℝ, HasDerivAt d 0 x := by
    intro x
    have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_id x).neg.exp
    have hdiff : HasDerivAt (fun u ↦ g u - expSteinSol h u)
        (g x + h x - stdExpExpect h - (expSteinSol h x + h x - stdExpExpect h)) x :=
      (hg_ode x).fun_sub (hode x)
    convert hexp.fun_mul hdiff using 1
    ring
  have hd_const : ∀ x : ℝ, d x = d 0 := fun x ↦
    is_const_of_deriv_eq_zero (fun u ↦ (hd_deriv u).differentiableAt)
      (fun u ↦ (hd_deriv u).deriv) x 0
  have hd0 : d 0 = 0 := by simp [d, hg0, expSteinSol_zero hInt]
  ext x
  have hx := (hd_const x).trans hd0
  simp only [d, mul_eq_zero, Real.exp_ne_zero, false_or, sub_eq_zero] at hx
  exact hx

/-- **Darboux jump witness for `ISSUE-5.2-ODE`**: for the bounded non-negative step function
$h = \mathbf{1}_{(-\infty, 1]}$, no function $g : \mathbb{R} \to \mathbb{R}$ satisfies the
two-sided exponential Stein ODE $g'(x) - g(x) = h(x) - \mathbb{E}[h(Z)]$ everywhere on
$\mathbb{R}$. -/
theorem not_exists_hasDerivAt_expStein_Iic :
    let h : ℝ → ℝ := (Iic (1 : ℝ)).indicator 1
    ¬ ∃ g : ℝ → ℝ, ∀ x : ℝ, HasDerivAt g (g x + h x - stdExpExpect h) x := by
  intro h ⟨g, hg⟩
  have hg_diff : Differentiable ℝ g := fun x ↦ (hg x).differentiableAt
  have hg_cont : Continuous g := hg_diff.continuous
  let G : ℝ → ℝ := fun x ↦ g x - ∫ t in (0 : ℝ)..x, g t
  have hG : ∀ x : ℝ, HasDerivAt G (h x - stdExpExpect h) x := by
    intro x
    have hint := intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable 0 x)
      hg_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hg_cont.continuousAt
    convert (hg x).fun_sub hint using 1
    ring
  have hh0 : h 0 = 1 := indicator_of_mem (by norm_num : (0 : ℝ) ≤ 1) 1
  have hh2 : h 2 = 0 := indicator_of_notMem (by norm_num : ¬ (2 : ℝ) ≤ 1) 1
  obtain ⟨c, _, hc_eq⟩ :=
    exists_hasDerivWithinAt_eq_of_lt_of_gt (a := (0 : ℝ)) (b := 2)
      (f := G) (f' := fun x ↦ h x - stdExpExpect h) (m := 1 / 2 - stdExpExpect h)
      (by norm_num) (fun x _ ↦ (hG x).hasDerivWithinAt) (by linarith) (by linarith)
  dsimp only at hc_eq
  by_cases hc : c ≤ 1
  · have : h c = 1 := indicator_of_mem hc 1
    linarith
  · have : h c = 0 := indicator_of_notMem hc 1
    linarith

/-- **Lemma 5.2(1)** (`\label{lem172}` item 1 `\label{i171}`, `SteinIntro.tex:2747-2750, 2781-2789`;
`D2`, `D5-3`): for measurable non-negative bounded $h : \mathbb{R} \to \mathbb{R}$ with
$0 \le h(t) \le M$ for all $t \in \mathbb{R}$, `expSteinSol h` is $2 M$-Lipschitz on $\mathbb{R}$,
and $|f_h(x)| \le M$, $|f_h'(x)| \le 2 M$, and $|D_- f_h(x)| \le 2 M$ for all $x \in \mathbb{R}$.
(Note Lean's `deriv` and `derivWithin` return `0` where the two-sided or left derivative does not
exist — e.g. jump points of $h$ for `deriv`, or measurable $h = \mathbf{1}_A$ with oscillating
Lebesgue density at $x$ for `derivWithin` — whereas `LipschitzWith` holds globally without
vacuity.) -/
theorem lem5_2_1 {h : ℝ → ℝ} {M : ℝ}
    (hMeas : Measurable h) (hNonneg : ∀ t : ℝ, 0 ≤ h t) (hLe : ∀ t : ℝ, h t ≤ M) :
    LipschitzWith (Real.toNNReal (2 * M)) (expSteinSol h) ∧
      ∀ x : ℝ,
        |expSteinSol h x| ≤ M ∧
        |deriv (expSteinSol h) x| ≤ 2 * M ∧
        |derivWithin (expSteinSol h) (Iic x) x| ≤ 2 * M := by
  have hM0 : 0 ≤ M := (hNonneg 0).trans (hLe 0)
  have hInt : Integrable h stdExpLaw := by
    refine Integrable.of_bound hMeas.aestronglyMeasurable M (ae_of_all _ fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hNonneg t)]
    exact hLe t
  have hexp_nn : 0 ≤ stdExpExpect h :=
    integral_nonneg fun t ↦ hNonneg t
  have hexp_le : stdExpExpect h ≤ M := by
    have := integral_mono hInt (integrable_const M) fun t ↦ hLe t
    simpa [stdExpExpect] using this
  have htilde_le : ∀ t : ℝ, |h t - stdExpExpect h| ≤ M := fun t ↦
    abs_le.mpr ⟨by linarith [hNonneg t], by linarith [hLe t]⟩
  have htilde_meas : AEStronglyMeasurable (fun t ↦ h t - stdExpExpect h) volume :=
    (hMeas.sub measurable_const).aestronglyMeasurable
  have heq : expSteinSol h = expTailTransform (fun t ↦ h t - stdExpExpect h) := rfl
  have hLip : LipschitzWith (Real.toNNReal (2 * M)) (expSteinSol h) := by
    rw [heq]
    exact lipschitzWith_expTailTransform htilde_meas htilde_le
  refine ⟨hLip, fun x ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [heq]
    exact abs_expTailTransform_le htilde_meas htilde_le x
  · have hd := norm_deriv_le_of_lipschitz (x₀ := x) hLip
    rwa [Real.norm_eq_abs, Real.coe_toNNReal (2 * M) (by positivity)] at hd
  · have hd := abs_derivWithin_Iic_le_of_lipschitz hLip x
    rwa [Real.coe_toNNReal (2 * M) (by positivity)] at hd

private lemma lipschitzWith_of_ac_deriv_le {h : ℝ → ℝ} {L : ℝ}
    (hh : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b)
    (hderiv : ∀ t : ℝ, |deriv h t| ≤ L) :
    LipschitzWith (Real.toNNReal L) h := by
  have hL0 : 0 ≤ L := (abs_nonneg (deriv h 0)).trans (hderiv 0)
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL0]
  have step : ∀ a b : ℝ, a ≤ b → |h b - h a| ≤ L * (b - a) := by
    intro a b hab
    rw [← (hh a b).integral_deriv_eq_sub]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := L)
      (f := deriv h) fun t _ ↦ by rw [Real.norm_eq_abs]; exact hderiv t
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm x y, abs_sub_comm (h x) (h y), abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact step x y hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact step y x hyx

private lemma deriv_expSteinSol_eq_expTailTransform {h : ℝ → ℝ} {L : ℝ}
    (hh : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b)
    (hderiv : ∀ t : ℝ, |deriv h t| ≤ L) :
    Differentiable ℝ (expSteinSol h) ∧
      deriv (expSteinSol h) = expTailTransform (deriv h) := by
  have hL0 : 0 ≤ L := (abs_nonneg (deriv h 0)).trans (hderiv 0)
  have hLip := lipschitzWith_of_ac_deriv_le hh hderiv
  have hCont : Continuous h := hLip.continuous
  have hInt : Integrable h stdExpLaw := by
    have hdom : Integrable (fun x : ℝ ↦ |h 0| + L * |x|) stdExpLaw :=
      (integrable_const |h 0|).add (integrable_id_stdExpLaw.norm.const_mul L)
    refine hdom.mono' hCont.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hd := hLip.dist_le_mul x 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero, Real.coe_toNNReal L hL0] at hd
    rw [Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (h x) (h 0)]
  have hode := (lem5_2_formula.2 hCont hInt).1
  refine ⟨fun x ↦ (hode x).differentiableAt, funext fun x ↦ ?_⟩
  rw [(hode x).deriv]
  let gx : ℝ → ℝ := fun u ↦ h (x + u)
  have hgx_lip : LipschitzWith (Real.toNNReal L) gx :=
    LipschitzWith.of_dist_le_mul fun u v ↦ by
      simpa [gx, Real.dist_eq, add_sub_add_left_eq_sub] using hLip.dist_le_mul (x + u) (x + v)
  have hgx_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval gx a b :=
    fun a b ↦ hgx_lip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hgx_deriv : deriv gx = fun u ↦ deriv h (x + u) :=
    funext fun u ↦ deriv_comp_const_add h x u
  have hgx_int : Integrable (deriv gx) stdExpLaw := by
    refine Integrable.of_bound (measurable_deriv gx).aestronglyMeasurable L
      (ae_of_all _ fun u ↦ ?_)
    rw [hgx_deriv, Real.norm_eq_abs]
    exact hderiv (x + u)
  have hfub := (integrable_and_integral_sub_eq_deriv_stdExpLaw hgx_ac hgx_int).2
  have hfub_int : ∫ u in Ioi 0, (h (x + u) - h x) * Real.exp (-u) =
      ∫ u in Ioi 0, deriv h (x + u) * Real.exp (-u) := by
    have hgx_int0 := (integrable_and_integral_sub_eq_deriv_stdExpLaw hgx_ac hgx_int).1
    have hsub : (∫ u, gx u ∂stdExpLaw) - gx 0 = ∫ u, (gx u - gx 0) ∂stdExpLaw := by
      rw [integral_sub hgx_int0 (integrable_const (gx 0)), integral_const]
      simp
    rw [hsub, integral_stdExpLaw_eq_setIntegral_Ioi,
      integral_stdExpLaw_eq_setIntegral_Ioi, hgx_deriv] at hfub
    simpa [gx] using hfub
  have hshift_lhs : ∫ t in Ioi x, (h t - h x) * Real.exp (-t) =
      Real.exp (-x) * ∫ u in Ioi 0, (h (x + u) - h x) * Real.exp (-u) := by
    rw [← integral_const_mul]
    have hind : ∫ t, (Ioi x).indicator (fun t ↦ (h t - h x) * Real.exp (-t)) t =
        ∫ u, (Ioi x).indicator (fun t ↦ (h t - h x) * Real.exp (-t)) (x + u) :=
      (integral_add_left_eq_self
        (fun t ↦ (Ioi x).indicator (fun t ↦ (h t - h x) * Real.exp (-t)) t) x).symm
    rw [integral_indicator measurableSet_Ioi] at hind
    have hcongr : (fun u ↦ (Ioi x).indicator (fun t ↦ (h t - h x) * Real.exp (-t)) (x + u)) =
        (Ioi (0 : ℝ)).indicator
          (fun u ↦ Real.exp (-x) * ((h (x + u) - h x) * Real.exp (-u))) := by
      ext u
      by_cases hu : 0 < u
      · have hmem1 : x + u ∈ Ioi x := by simp [hu]
        have hmem2 : u ∈ Ioi (0 : ℝ) := hu
        rw [indicator_of_mem hmem1, indicator_of_mem hmem2, neg_add, Real.exp_add]
        ring
      · have hnot1 : x + u ∉ Ioi x := by simp [hu]
        have hnot2 : u ∉ Ioi (0 : ℝ) := hu
        rw [indicator_of_notMem hnot1, indicator_of_notMem hnot2]
    rw [hcongr, integral_indicator measurableSet_Ioi] at hind
    exact hind
  have hshift_rhs : ∫ t in Ioi x, deriv h t * Real.exp (-t) =
      Real.exp (-x) * ∫ u in Ioi 0, deriv h (x + u) * Real.exp (-u) := by
    rw [← integral_const_mul]
    have hind : ∫ t, (Ioi x).indicator (fun t ↦ deriv h t * Real.exp (-t)) t =
        ∫ u, (Ioi x).indicator (fun t ↦ deriv h t * Real.exp (-t)) (x + u) :=
      (integral_add_left_eq_self
        (fun t ↦ (Ioi x).indicator (fun t ↦ deriv h t * Real.exp (-t)) t) x).symm
    rw [integral_indicator measurableSet_Ioi] at hind
    have hcongr : (fun u ↦ (Ioi x).indicator (fun t ↦ deriv h t * Real.exp (-t)) (x + u)) =
        (Ioi (0 : ℝ)).indicator (fun u ↦ Real.exp (-x) * (deriv h (x + u) * Real.exp (-u))) := by
      ext u
      by_cases hu : 0 < u
      · have hmem1 : x + u ∈ Ioi x := by simp [hu]
        have hmem2 : u ∈ Ioi (0 : ℝ) := hu
        rw [indicator_of_mem hmem1, indicator_of_mem hmem2, neg_add, Real.exp_add]
        ring
      · have hnot1 : x + u ∉ Ioi x := by simp [hu]
        have hnot2 : u ∉ Ioi (0 : ℝ) := hu
        rw [indicator_of_notMem hnot1, indicator_of_notMem hnot2]
    rw [hcongr, integral_indicator measurableSet_Ioi] at hind
    exact hind
  have hdecomp : ∫ t in Ioi x, (h t - stdExpExpect h) * Real.exp (-t) =
      (∫ t in Ioi x, (h t - h x) * Real.exp (-t)) +
        (h x - stdExpExpect h) * Real.exp (-x) := by
    have h1 := integrableOn_stein_integrand_Ioi hCont.locallyIntegrable hInt x
    have h2 := (integrableOn_exp_neg_Ioi x).const_mul (h x - stdExpExpect h)
    have hdiff_int : IntegrableOn (fun t ↦ (h t - h x) * Real.exp (-t)) (Ioi x) volume := by
      refine (h1.sub h2).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
      dsimp only [Pi.sub_apply]
      ring
    have heq : (fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)) =
        fun t ↦ (h t - h x) * Real.exp (-t) + (h x - stdExpExpect h) * Real.exp (-t) := by
      ext t; ring
    rw [heq, integral_add hdiff_int h2, integral_const_mul, integral_exp_neg_Ioi]
  unfold expSteinSol expTailTransform
  rw [hdecomp, hshift_lhs, hfub_int, ← hshift_rhs]
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    -Real.exp x * ((∫ t in Ioi x, deriv h t * Real.exp (-t)) +
        (h x - stdExpExpect h) * Real.exp (-x)) + h x - stdExpExpect h
      = -Real.exp x * (∫ t in Ioi x, deriv h t * Real.exp (-t)) -
          (h x - stdExpExpect h) * (Real.exp x * Real.exp (-x)) + h x - stdExpExpect h := by ring
    _ = -Real.exp x * ∫ t in Ioi x, deriv h t * Real.exp (-t) := by rw [hexp]; ring

/-- **Lemma 5.2(2)** (`\label{lem172}` item 2 `\label{i172}`, `SteinIntro.tex:2751-2754, 2790-2796`;
`stmts-review-05D.md` `D2`): for locally absolutely continuous $h : \mathbb{R} \to \mathbb{R}$
(`D5`) with $|h'(t)| \le L$ for all $t \in \mathbb{R}$, `expSteinSol h` is everywhere
differentiable, `deriv (expSteinSol h)` is $2 L$-Lipschitz on $\mathbb{R}$, and
$|f_h'(x)| \le L$ and $|f_h''(x)| \le 2 L$ for all $x \in \mathbb{R}$ (with Lean's outer `deriv`
returning `0` at points where $f_h'$ has a corner, while `LipschitzWith` holds everywhere). -/
theorem lem5_2_2 {h : ℝ → ℝ} {L : ℝ}
    (hh : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b)
    (hderiv : ∀ t : ℝ, |deriv h t| ≤ L) :
    Differentiable ℝ (expSteinSol h) ∧
      LipschitzWith (Real.toNNReal (2 * L)) (deriv (expSteinSol h)) ∧
      ∀ x : ℝ,
        |deriv (expSteinSol h) x| ≤ L ∧
        |deriv (deriv (expSteinSol h)) x| ≤ 2 * L := by
  have hL0 : 0 ≤ L := (abs_nonneg (deriv h 0)).trans (hderiv 0)
  obtain ⟨hdiff, hderiv_eq⟩ := deriv_expSteinSol_eq_expTailTransform hh hderiv
  have hmeas : AEStronglyMeasurable (deriv h) volume := (measurable_deriv h).aestronglyMeasurable
  have hLip : LipschitzWith (Real.toNNReal (2 * L)) (deriv (expSteinSol h)) := by
    rw [hderiv_eq]
    exact lipschitzWith_expTailTransform hmeas hderiv
  refine ⟨hdiff, hLip, fun x ↦ ⟨?_, ?_⟩⟩
  · rw [hderiv_eq]
    exact abs_expTailTransform_le hmeas hderiv x
  · have hd := norm_deriv_le_of_lipschitz (x₀ := x) hLip
    rwa [Real.norm_eq_abs, Real.coe_toNNReal (2 * L) (by positivity)] at hd

/-! ### Section 3: Lemma 5.1(1) & 5.1(2) — Exponential Characterizing Operator -/

/-- **Lemma 5.1(1), with explicit integrability** (`\label{lem171}`,
`SteinIntro.tex:2726-2733, 2805-2810`; `N1`): if $Z \sim \mathrm{Exp}(1)$, then for every locally
absolutely continuous $f : \mathbb{R} \to \mathbb{R}$ with $\mathbb{E}|f'(Z)| < \infty$,
$\mathcal{A}f(Z)$ is integrable and $\mathbb{E}[\mathcal{A}f(Z)] = 0$. -/
theorem lem5_1_1_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} {f : ℝ → ℝ}
    (hZ : AEMeasurable Z P) (hZ_law : P.map Z = stdExpLaw)
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (fun ω ↦ deriv f (Z ω)) P) :
    Integrable (fun ω ↦ expSteinOp f (Z ω)) P ∧ ∫ ω, expSteinOp f (Z ω) ∂P = 0 := by
  have hf'_std : Integrable (deriv f) stdExpLaw := by
    rw [← hZ_law]
    exact (integrable_map_measure (measurable_deriv f).aestronglyMeasurable hZ).mpr hf'
  obtain ⟨hf_std, heq_std⟩ := integrable_and_integral_sub_eq_deriv_stdExpLaw hf hf'_std
  have hf_cont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    have hc := (hf (x - 1) (x + 1)).continuousOn
    rw [uIcc_of_le (by linarith)] at hc
    exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hop_meas : Measurable (expSteinOp f) :=
    ((measurable_deriv f).sub hf_cont.measurable).add measurable_const
  have heq_fn : expSteinOp f = fun x ↦ deriv f x - (f x - f 0) := by
    ext x; unfold expSteinOp; ring
  have hsub_int : Integrable (fun x ↦ f x - f 0) stdExpLaw := hf_std.sub (integrable_const (f 0))
  have hop_int_std : Integrable (expSteinOp f) stdExpLaw := by
    rw [heq_fn]; exact hf'_std.sub hsub_int
  have hop_int : Integrable (fun ω ↦ expSteinOp f (Z ω)) P := by
    refine (integrable_map_measure hop_meas.aestronglyMeasurable hZ).mp ?_
    rwa [hZ_law]
  refine ⟨hop_int, ?_⟩
  rw [← integral_map hZ hop_meas.aestronglyMeasurable, hZ_law, heq_fn,
    integral_sub hf'_std hsub_int, integral_sub hf_std (integrable_const (f 0)), integral_const]
  simp [heq_std]

/-- **Lemma 5.1(1)** (`\label{lem171}`, `SteinIntro.tex:2726-2733, 2805-2810`): if
$Z \sim \mathrm{Exp}(1)$, then $\mathbb{E}[\mathcal{A}f(Z)] = 0$ for every locally absolutely
continuous $f : \mathbb{R} \to \mathbb{R}$ with $\mathbb{E}|f'(Z)| < \infty$. -/
theorem lem5_1_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} {f : ℝ → ℝ}
    (hZ : AEMeasurable Z P) (hZ_law : P.map Z = stdExpLaw)
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (hf' : Integrable (fun ω ↦ deriv f (Z ω)) P) :
    ∫ ω, expSteinOp f (Z ω) ∂P = 0 :=
  (lem5_1_1_integrable P hZ hZ_law hf hf').2

/-- Continuous `[0, 1]`-valued ramp approximating $\mathbf{1}_{(-\infty, x]}$ from above as
$n \to \infty$, used in `lem5_1_2` and `sec5_1_equilibrium_ac`. -/
def expRamp (x : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max 0 (min 1 (1 - ((n : ℝ) + 1) * (t - x)))

theorem continuous_expRamp (x : ℝ) (n : ℕ) : Continuous (expRamp x n) := by
  unfold expRamp
  fun_prop

theorem expRamp_nonneg (x : ℝ) (n : ℕ) (t : ℝ) : 0 ≤ expRamp x n t :=
  le_max_left 0 _

theorem expRamp_le_one (x : ℝ) (n : ℕ) (t : ℝ) : expRamp x n t ≤ 1 :=
  max_le zero_le_one (min_le_left 1 _)

theorem abs_expRamp_le_one (x : ℝ) (n : ℕ) (t : ℝ) : |expRamp x n t| ≤ 1 := by
  rw [abs_of_nonneg (expRamp_nonneg x n t)]
  exact expRamp_le_one x n t

private lemma tendsto_expRamp (x t : ℝ) :
    Tendsto (fun n ↦ expRamp x n t) atTop (𝓝 ((Iic x).indicator (1 : ℝ → ℝ) t)) := by
  by_cases htx : t ≤ x
  · have hmem : t ∈ Iic x := htx
    rw [indicator_of_mem hmem, Pi.one_apply]
    have heq : ∀ n : ℕ, expRamp x n t = 1 := by
      intro n
      have hmul : ((n : ℝ) + 1) * (t - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr htx)
      simp [expRamp, min_eq_left (by linarith : 1 ≤ 1 - ((n : ℝ) + 1) * (t - x))]
    simp_rw [heq]
    exact tendsto_const_nhds
  · have hnot : t ∉ Iic x := htx
    rw [indicator_of_notMem hnot]
    have hxt : 0 < t - x := sub_pos.mpr (lt_of_not_ge htx)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ici_mem_atTop ⌈(t - x)⁻¹⌉₊] with n hn
    have hn1 : (t - x)⁻¹ ≤ (n : ℝ) + 1 := by
      linarith [(Nat.le_ceil (t - x)⁻¹).trans (Nat.cast_le.mpr hn)]
    have hmul : 1 ≤ ((n : ℝ) + 1) * (t - x) := by
      have := mul_le_mul_of_nonneg_right hn1 hxt.le
      rwa [inv_mul_cancel₀ hxt.ne'] at this
    exact (max_eq_left ((min_le_right 1 _).trans (by linarith))).symm

theorem tendsto_integral_expRamp (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    Tendsto (fun n ↦ ∫ t, expRamp x n t ∂ν) atTop (𝓝 (cdf ν x)) := by
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ (1 : ℝ))
    (fun n ↦ (continuous_expRamp x n).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun n ↦ ae_of_all ν fun t ↦ by rw [Real.norm_eq_abs]; exact abs_expRamp_le_one x n t)
    (ae_of_all ν fun t ↦ tendsto_expRamp x t)
  have hind : ∫ t, (Iic x).indicator (1 : ℝ → ℝ) t ∂ν = cdf ν x := by
    rw [integral_indicator measurableSet_Iic, Pi.one_def, setIntegral_const, smul_eq_mul,
      mul_one, ← cdf_eq_real]
  rwa [hind] at hlim

/-- **Lemma 5.1(2)** (`\label{lem171}`, `SteinIntro.tex:2734-2736, 2811-2820`; `D5` literal):
if $W \ge 0$ a.s. satisfies $\mathbb{E}[\mathcal{A}f(W)] = 0$ for all locally absolutely continuous
$f$ with $\mathbb{E}|f'(Z)| < \infty$, then $W \sim \mathrm{Exp}(1)$. Proved without moment
hypotheses on $W$ using bounded $C^1$ ramp solutions of the exponential Stein equation. -/
theorem lem5_1_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW : AEMeasurable W P) (_hW_nn : 0 ≤ᵐ[P] W)
    (hStein : ∀ f : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
      Integrable (deriv f) stdExpLaw → ∫ ω, expSteinOp f (W ω) ∂P = 0) :
    P.map W = stdExpLaw := by
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  refine Measure.eq_of_cdf (P.map W) stdExpLaw ?_
  ext x
  have heq_n : ∀ n : ℕ,
      ∫ t, expRamp x n t ∂P.map W = ∫ z, expRamp x n z ∂stdExpLaw := by
    intro n
    set g := expRamp x n
    have hg_cont : Continuous g := continuous_expRamp x n
    have hg_int : Integrable g stdExpLaw :=
      Integrable.of_bound hg_cont.aestronglyMeasurable 1
        (ae_of_all _ fun t ↦ by rw [Real.norm_eq_abs]; exact abs_expRamp_le_one x n t)
    set f := expSteinSol g
    have hf_ode := (lem5_2_formula.2 hg_cont hg_int).1
    have hf_bounds := lem5_2_1 hg_cont.measurable (expRamp_nonneg x n) (expRamp_le_one x n)
    have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
      fun a b ↦ hf_bounds.1.lipschitzOnWith.absolutelyContinuousOnInterval
    have hf'_int : Integrable (deriv f) stdExpLaw := by
      refine Integrable.of_bound (measurable_deriv f).aestronglyMeasurable 2
        (ae_of_all _ fun t ↦ ?_)
      rw [Real.norm_eq_abs]
      simpa using (hf_bounds.2 t).2.1
    have h0 := hStein f hf_ac hf'_int
    have hop_eq : ∀ u : ℝ, expSteinOp f u = g u - stdExpExpect g := by
      intro u
      unfold expSteinOp
      dsimp only [f]
      rw [(hf_ode u).deriv, expSteinSol_zero hg_int]
      ring
    simp_rw [hop_eq] at h0
    have hgW_int : Integrable (fun ω ↦ g (W ω)) P :=
      Integrable.of_bound (hg_cont.measurable.comp_aemeasurable hW).aestronglyMeasurable 1
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_expRamp_le_one x n (W ω))
    rw [integral_sub hgW_int (integrable_const _), integral_const, probReal_univ, one_smul,
      sub_eq_zero] at h0
    rw [integral_map hW hg_cont.aestronglyMeasurable]
    exact h0
  have hlim_W := tendsto_integral_expRamp (P.map W) x
  have hlim_Z := tendsto_integral_expRamp stdExpLaw x
  simp_rw [heq_n] at hlim_W
  exact tendsto_nhds_unique hlim_W hlim_Z

end SteinMethod
