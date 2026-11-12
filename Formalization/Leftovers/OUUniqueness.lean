/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Leftovers.OUSemigroup
import Formalization.Leftovers.OUUniquenessAux

/-!
# Ornstein–Uhlenbeck Infinitesimal Uniqueness (`Formalization.Leftovers.OUUniqueness`)

Formalizes the uniqueness assertions of Remark 3.5 (`SteinIntro.tex:1009-1024`; `BL8`):
* `ouKernel_comp`, `ouKernel_lindeberg_tail`, `ouKernel_quadratic_domination`
  (re-exported from `Formalization.Leftovers.OUUniquenessAux`, Part 1).
* `tendsto_ouGenerator_normalSteinOp`, `eq_stdNormalLaw_of_stationary_infinitesimal` (Part 2).
* `eq_ouKernel_of_infinitesimal`, `eq_stdNormalLaw_of_bind_ouKernel` (Part 3).
* `rem3_5_uniqueness_restricted_proof` (master theorem for `Rem3_5_uniqueness_restricted`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

open OUUniquenessAux

private lemma integrable_charFun_kernel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (θ : ℝ) :
    Integrable (fun y ↦ charFun (κ y) θ) μ := by
  have hi : Integrable (fun p : ℝ × ℝ ↦ cexpI θ p.2) (μ ⊗ₘ κ) :=
    Integrable.of_bound ((continuous_cexpI θ).comp continuous_snd).aestronglyMeasurable
      1 (ae_of_all _ fun p ↦ (norm_cexpI θ p.2).le)
  have h2 := hi.integral_compProd
  simp only [Kernel.prodMkLeft_apply, Kernel.const_apply, ← charFun_eq_integral_cexpI] at h2
  exact h2

/-! ### Sections 3 & 4: Infinitesimal Generator, Stationary Law, and Semigroup Uniqueness -/

section Infinitesimal

variable {K : ℝ → Kernel ℝ ℝ}
  (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
  (hDrift : ∀ x : ℝ,
    Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a) (𝓝[>] 0) (𝓝 0))
  (hDiff : ∀ x : ℝ,
    Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a) (𝓝[>] 0) (𝓝 0))
  (hLind : ∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
    Tendsto (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂K a x) / a)
      (𝓝[>] 0) (𝓝 0))
include hMarkov hDrift hDiff hLind

/-- Pointwise infinitesimal Stein generator identity (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem tendsto_ouGenerator_normalSteinOp
    (hInt2_loc : ∀ x : ℝ, ∀ᶠ a in 𝓝[>] 0,
      Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hB : ∃ B : ℝ, (∀ u : ℝ, |f u| ≤ B) ∧ (∀ u : ℝ, |deriv f u| ≤ B)) (x : ℝ) :
    Tendsto (fun a : ℝ ↦
        (∫ y, ((∫ u in (0 : ℝ)..y, f u) - (∫ u in (0 : ℝ)..x, f u)) ∂K a x) / a)
      (𝓝[>] 0) (𝓝 (normalSteinOp f x)) := by
  obtain ⟨B, hBf, hBdf⟩ := hB
  have hB_nn : 0 ≤ B := (abs_nonneg (f 0)).trans (hBf 0)
  set G : ℝ → ℝ := fun z ↦ ∫ u in (0 : ℝ)..z, f u
  have hG_cont : Continuous G := continuous_iff_continuousAt.mpr fun z ↦
    (hasDerivAt_primitive hf.continuous z).continuousAt
  set R : ℝ → ℝ := fun y ↦ G y - G x - f x * (y - x) - (1 / 2) * deriv f x * (y - x) ^ 2
  have hR_cont : Continuous R := by fun_prop
  have hR_global : ∀ y : ℝ, |R y| ≤ (2 * B) * (y - x) ^ 2 := fun y ↦
    abs_primitive_taylor_two_le hf x y fun u _ ↦ by
      linarith [abs_sub (deriv f u) (deriv f x), hBdf u, hBdf x]
  have hDrift' := tendsto_div_of_sub_littleO (c := -x) ((hDrift x).congr fun a ↦ by ring)
  have hDiff' := tendsto_div_of_sub_littleO (hDiff x)
  have hR_lim : Tendsto (fun a : ℝ ↦ (∫ y, R y ∂K a x) / a) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_remainder_zero hMarkov hDiff' (hLind x) (hInt2_loc x)
      (r := fun _ ↦ R) (Eventually.of_forall fun _ ↦ hR_cont.aestronglyMeasurable)
      (B := 2 * B) (by positivity)
      (Eventually.of_forall fun _ y ↦ by simpa [Real.norm_eq_abs] using hR_global y) ?_).congr
      fun a ↦ by simp [div_eq_inv_mul]
    intro η hη
    obtain ⟨δ, hδ_pos, hδ⟩ :=
      Metric.continuousAt_iff.mp ((hf.continuous_deriv le_rfl).continuousAt (x := x)) η hη
    refine ⟨δ / 2, half_pos hδ_pos, Eventually.of_forall fun _ y hy ↦ ?_⟩
    rw [Real.norm_eq_abs]
    exact abs_primitive_taylor_two_le hf x y fun u hu ↦
      (hδ (by rw [Real.dist_eq]; exact (hu.trans hy).trans_lt (half_lt_self hδ_pos))).le
  have hmain := ((hDrift'.const_mul (f x)).add (hDiff'.const_mul ((1 / 2) * deriv f x))).add hR_lim
  rw [show f x * (-x) + (1 / 2) * deriv f x * 2 + 0 = normalSteinOp f x by
    unfold normalSteinOp; ring] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hInt2_loc x] with a ha hInt2
  have := hMarkov a (mem_Ioi.mp ha); have hInt1 := integrable_sub_of_integrable_sq hInt2
  have hR_int : Integrable R (K a x) := (hInt2.const_mul (2 * B)).mono'
    hR_cont.aestronglyMeasurable
    (ae_of_all _ fun y ↦ by simpa [Real.norm_eq_abs] using hR_global y)
  have hG_eq : (fun y : ℝ ↦ G y - G x) =
      fun y ↦ (f x * (y - x) + ((1 / 2) * deriv f x) * (y - x) ^ 2) + R y := by
    ext y; dsimp only [R]; ring
  rw [hG_eq, integral_add (iAdd (hInt1.const_mul _) (hInt2.const_mul _)) hR_int,
    integral_add (hInt1.const_mul _) (hInt2.const_mul _), integral_const_mul, integral_const_mul]
  ring

private lemma cexp_step_bound_and_limit {a₀ C : ℝ} (ha₀ : 0 < a₀) (hC : 0 ≤ C)
    (hDom : QuadDom K a₀ C) :
    (∀ θ_max : ℝ, 0 ≤ θ_max → ∀ θ : ℝ, |θ| ≤ θ_max →
      ∀ a ∈ Ioo 0 a₀, ∀ y : ℝ,
        ‖(charFun (K a y) θ - cexpI θ y) / (a : ℂ)‖ ≤
          (θ_max + 3 * θ_max ^ 2) * C * (1 + |y| + y ^ 2)) ∧
    (∀ (θ_fn : ℝ → ℝ) (θ₀ y : ℝ), Tendsto θ_fn (𝓝[>] 0) (𝓝 θ₀) →
      Tendsto (fun a : ℝ ↦ (charFun (K a y) (θ_fn a) - cexpI (θ_fn a) y) / (a : ℂ))
        (𝓝[>] 0)
        (𝓝 (cexpI θ₀ y *
          (Complex.I * ((-θ₀ * y : ℝ) : ℂ) - ((θ₀ ^ 2 : ℝ) : ℂ))))) := by
  set r : ℝ → ℂ := fun u ↦
    Complex.exp ((u : ℂ) * Complex.I) - (1 + (u : ℂ) * Complex.I - ((u ^ 2 / 2 : ℝ) : ℂ))
  have hdecomp : ∀ a ∈ Ioo 0 a₀, ∀ θ y : ℝ,
      (charFun (K a y) θ - cexpI θ y) / (a : ℂ) =
      cexpI θ y * (Complex.I * ((θ * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ) -
        (((θ ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ) +
        (∫ z, r (θ * (z - y)) ∂K a y) / (a : ℂ)) := by
    intro a ha θ y; have ha_pos := ha.1; have := hMarkov a ha_pos
    have hInt2 := (hDom a ha y).1; have hInt1 := integrable_sub_of_integrable_sq hInt2
    have hr_int : Integrable (fun z : ℝ ↦ r (θ * (z - y))) (K a y) :=
      (hInt2.const_mul (2 * θ ^ 2)).mono' (by fun_prop) (ae_of_all _ fun z ↦
        (norm_cexp_taylor_two_le (θ * (z - y))).trans ((min_le_left _ _).trans_eq (by ring)))
    have hp : (fun z : ℝ ↦ cexpI θ z - cexpI θ y) = fun z ↦ cexpI θ y *
        ((((θ * (z - y) : ℝ) : ℂ) * Complex.I - ((((θ ^ 2 / 2) * (z - y) ^ 2 : ℝ) : ℂ))) +
          r (θ * (z - y))) := funext fun z ↦ by
      have hexp_z : cexpI θ z =
          cexpI θ y * Complex.exp (((θ * (z - y) : ℝ) : ℂ) * Complex.I) := by
        simp only [cexpI, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub]
        congr 1; ring
      rw [hexp_z]; dsimp only [r]
      rw [show (θ * (z - y)) ^ 2 / 2 = (θ ^ 2 / 2) * (z - y) ^ 2 by ring]; ring
    have hw1_i : Integrable (fun z : ℝ ↦ ((θ * (z - y) : ℝ) : ℂ) * Complex.I) (K a y) :=
      (hInt1.const_mul θ).ofReal.mul_const Complex.I
    have hw2_i : Integrable (fun z : ℝ ↦ (((θ ^ 2 / 2) * (z - y) ^ 2 : ℝ) : ℂ)) (K a y) :=
      (hInt2.const_mul (θ ^ 2 / 2)).ofReal
    have hsub_one : charFun (K a y) θ - cexpI θ y =
        ∫ z, (cexpI θ z - cexpI θ y) ∂K a y := by
      rw [charFun_eq_integral_cexpI, integral_sub (integrable_cexpI (K a y) θ)
        (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [hsub_one, hp, integral_const_mul, integral_add (iSub hw1_i hw2_i) hr_int,
      integral_sub hw1_i hw2_i, integral_mul_const, integral_complex_ofReal, integral_const_mul,
      integral_complex_ofReal, integral_const_mul]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr ha_pos.ne']
  constructor
  · intro θ_max hθ_nn θ hθ a ha y
    have ha_pos := ha.1; have := hMarkov a ha_pos; obtain ⟨hInt2, hD1, hD2⟩ := hDom a ha y
    have hθ2 : θ ^ 2 ≤ θ_max ^ 2 := by
      rw [← sq_abs θ]; exact pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    rw [hdecomp a ha θ y, norm_mul, norm_cexpI, one_mul]
    have hb1 : |(∫ z, (z - y) ∂K a y) / a| ≤ C * (1 + |y|) := by
      rw [abs_div, abs_of_pos ha_pos, div_le_iff₀ ha_pos]; linarith
    have hb2 : (∫ z, (z - y) ^ 2 ∂K a y) / a ≤ C * (1 + y ^ 2) := by
      rw [div_le_iff₀ ha_pos]; linarith
    have hsq_nn : 0 ≤ (∫ z, (z - y) ^ 2 ∂K a y) / a :=
      div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) ha_pos.le
    have ht1 : ‖Complex.I * ((θ * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ)‖ ≤
        θ_max * C * (1 + |y|) := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul hθ hb1 (abs_nonneg _) hθ_nn).trans_eq (by ring)
    have ht2 : ‖(((θ ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)‖ ≤
        (θ_max ^ 2 / 2) * C * (1 + y ^ 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity),
        abs_of_nonneg hsq_nn]
      exact (mul_le_mul (div_le_div_of_nonneg_right hθ2 zero_le_two) hb2 hsq_nn
        (by positivity)).trans_eq (by ring)
    have ht3 : ‖(∫ z, r (θ * (z - y)) ∂K a y) / (a : ℂ)‖ ≤
        2 * θ_max ^ 2 * C * (1 + y ^ 2) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha_pos]
      have hint_le : ‖∫ z, r (θ * (z - y)) ∂K a y‖ ≤
          2 * θ_max ^ 2 * ∫ z, (z - y) ^ 2 ∂K a y := by
        refine (norm_integral_le_of_norm_le (hInt2.const_mul (2 * θ_max ^ 2))
          (ae_of_all _ fun z ↦ ?_)).trans_eq (integral_const_mul _ _)
        refine (norm_cexp_taylor_two_le _).trans ((min_le_left _ _).trans ?_)
        rw [mul_pow]; exact (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hθ2 (sq_nonneg _)) zero_le_two).trans_eq (by ring)
      refine (div_le_div_of_nonneg_right hint_le ha_pos.le).trans ?_
      rw [mul_div_assoc]; exact (mul_le_mul_of_nonneg_left hb2 (by positivity)).trans_eq (by ring)
    refine ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ht1 ht2))
      ht3)).trans ?_
    nlinarith [abs_nonneg y, sq_nonneg y, mul_nonneg hθ_nn hC, mul_nonneg (sq_nonneg θ_max) hC]
  · intro θ_fn θ₀ y hθ_lim
    have hDrift' := tendsto_div_of_sub_littleO (c := -y) ((hDrift y).congr fun a ↦ by ring)
    have hDiff' := tendsto_div_of_sub_littleO (hDiff y)
    set κ : ℝ := |θ₀| + 1; have hκ_pos : 0 < κ := by positivity
    have hθ_ev : ∀ᶠ a in 𝓝[>] 0, |θ_fn a| ≤ κ := by
      filter_upwards [(Metric.tendsto_nhds.mp hθ_lim) 1 zero_lt_one] with a ha
      rw [Real.dist_eq] at ha; dsimp [κ]
      linarith [abs_sub_abs_le_abs_sub (θ_fn a) θ₀, (abs_lt.mp ha).2]
    have hr_lim : Tendsto (fun a : ℝ ↦ (∫ z, r (θ_fn a * (z - y)) ∂K a y) / (a : ℂ))
        (𝓝[>] 0) (𝓝 0) := by
      refine (tendsto_remainder_zero hMarkov hDiff' (hLind y)
        (eventually_of_mem (Ioo_mem_nhdsGT ha₀) fun a ha ↦ (hDom a ha y).1)
        (r := fun a z ↦ r (θ_fn a * (z - y)))
        (Eventually.of_forall fun a ↦ (by fun_prop : Continuous fun z ↦
          r (θ_fn a * (z - y))).aestronglyMeasurable)
        (B := 2 * κ ^ 2) (by positivity) ?_ ?_).congr
        fun a ↦ by simp [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
      · refine hθ_ev.mono fun a hθa z ↦ ?_
        have hθ2 : θ_fn a ^ 2 ≤ κ ^ 2 := by
          rw [← sq_abs (θ_fn a)]; exact pow_le_pow_left₀ (abs_nonneg _) hθa 2
        have h1 : ‖r (θ_fn a * (z - y))‖ ≤ 2 * (θ_fn a * (z - y)) ^ 2 :=
          (norm_cexp_taylor_two_le _).trans (min_le_left _ _)
        rw [mul_pow] at h1
        exact h1.trans ((mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hθ2 (sq_nonneg _)) zero_le_two).trans_eq (by ring))
      · intro η hη; refine ⟨η / (κ ^ 3), by positivity, hθ_ev.mono fun a hθa z hz ↦ ?_⟩
        have hθ3 : |θ_fn a| ^ 3 ≤ κ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hθa 3
        have h1 : ‖r (θ_fn a * (z - y))‖ ≤ |θ_fn a * (z - y)| ^ 3 :=
          (norm_cexp_taylor_two_le _).trans (min_le_right _ _)
        rw [abs_mul, mul_pow] at h1
        have h2 : |z - y| ^ 3 ≤ (η / κ ^ 3) * (z - y) ^ 2 := by
          rw [show |z - y| ^ 3 = |z - y| * (z - y) ^ 2 by rw [← sq_abs]; ring]
          exact mul_le_mul_of_nonneg_right hz (sq_nonneg _)
        exact (h1.trans (mul_le_mul hθ3 h2 (by positivity) (by positivity))).trans_eq
          (by field_simp [hκ_pos.ne'])
    have hcexp_lim : Tendsto (fun a : ℝ ↦ cexpI (θ_fn a) y)
        (𝓝[>] 0) (𝓝 (cexpI θ₀ y)) :=
      ((hasDerivAt_cexpI_comp (hasDerivAt_id' θ₀) y).continuousAt.tendsto).comp hθ_lim
    have ht1 : Tendsto (fun a : ℝ ↦ ((θ_fn a * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 ((-θ₀ * y : ℝ) : ℂ)) := by
      have hr1 := hθ_lim.mul hDrift'; rw [show θ₀ * -y = -θ₀ * y by ring] at hr1
      exact (Complex.continuous_ofReal.tendsto _).comp hr1
    have ht2 : Tendsto
        (fun a : ℝ ↦ ((((θ_fn a ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)))
        (𝓝[>] 0) (𝓝 ((θ₀ ^ 2 : ℝ) : ℂ)) := by
      have hr2 := ((hθ_lim.pow 2).div_const 2).mul hDiff'
      rw [show (θ₀ ^ 2 / 2) * 2 = θ₀ ^ 2 by ring] at hr2
      exact (Complex.continuous_ofReal.tendsto _).comp hr2
    have hcomb := hcexp_lim.mul (((ht1.const_mul Complex.I).sub ht2).add hr_lim)
    rw [add_zero] at hcomb
    exact hcomb.congr' (eventually_of_mem (Ioo_mem_nhdsGT ha₀)
      fun a ha ↦ (hdecomp a ha (θ_fn a) y).symm)

/-- Stationary-law uniqueness (Remark 3.5, `SteinIntro.tex:1018-1019`):
any square-integrable probability measure stationary for small `a > 0` equals `stdNormalLaw`. -/
theorem eq_stdNormalLaw_of_stationary_infinitesimal
    (hDom : ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ QuadDom K a₀ C)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ2 : Integrable (fun x : ℝ ↦ x ^ 2) μ)
    (hStat : ∀ᶠ a in 𝓝[>] 0, μ.bind (K a) = μ) : μ = stdNormalLaw := by
  obtain ⟨a₀, ha₀, C, hC, hDom'⟩ := hDom
  obtain ⟨hStep_bnd, hStep_lim⟩ :=
    cexp_step_bound_and_limit hMarkov hDrift hDiff hLind ha₀ hC hDom'
  have hμ1 := integrable_abs_of_integrable_sq hμ2
  set φ' : ℝ → ℂ := fun ξ ↦ ∫ y, cexpI ξ y * (Complex.I * (y : ℂ)) ∂μ
  have hcf_cont : Continuous (charFun μ) := continuous_iff_continuousAt.mpr fun ξ₀ ↦ by
    rw [ContinuousAt]
    simp_rw [show charFun μ = fun ξ ↦ ∫ z, cexpI ξ z ∂μ from
      funext (charFun_eq_integral_cexpI μ)]
    exact tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ ↦ (1 : ℝ))
      (Eventually.of_forall fun ξ ↦ (continuous_cexpI ξ).aestronglyMeasurable)
      (Eventually.of_forall fun ξ ↦ ae_of_all _ fun y ↦ (norm_cexpI ξ y).le)
      (integrable_const 1)
      (ae_of_all _ fun y ↦ (hasDerivAt_cexpI_comp (hasDerivAt_id' ξ₀) y).continuousAt.tendsto)
  have hcf_rderiv : ∀ ξ : ℝ,
      HasDerivWithinAt (charFun μ) (φ' ξ) (Ici ξ) ξ := fun ξ ↦ by
    refine hasDerivWithinAt_Ici_of_tendsto_right ?_
    have hlim : Tendsto
        (fun a : ℝ ↦ ∫ y, (cexpI (ξ + a) y - cexpI ξ y) / (a : ℂ) ∂μ)
        (𝓝[>] (0 : ℝ)) (𝓝 (φ' ξ)) :=
      tendsto_integral_filter_of_dominated_convergence (fun y : ℝ ↦ |y|)
        (Eventually.of_forall fun a ↦
          ((iSub (integrable_cexpI μ (ξ + a)) (integrable_cexpI μ ξ)).div_const
            (a : ℂ)).aestronglyMeasurable)
        (eventually_of_mem self_mem_nhdsWithin fun a (ha : 0 < a) ↦ ae_of_all _ fun y ↦ by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_le_iff₀ ha]
          have hb := norm_cexpI_sub_le ξ (ξ + a) y
          rw [add_sub_cancel_left, abs_of_pos ha] at hb; linarith) hμ1
        (ae_of_all _ fun y ↦ by
          have hd := hasDerivAt_cexpI_comp (hasDerivAt_id' ξ) y
          rw [one_mul] at hd
          exact hd.tendsto_slope_zero_right.congr fun a ↦ by
            simp [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul])
    exact hlim.congr' (Eventually.of_forall fun a ↦ by
      simp_rw [charFun_eq_integral_cexpI,
        ← integral_sub (integrable_cexpI μ (ξ + a)) (integrable_cexpI μ ξ), ← integral_div])
  have hode : ∀ ξ : ℝ, 0 < ξ → φ' ξ = -((ξ : ℂ) * charFun μ ξ) := fun ξ hξ ↦ by
    set L : ℝ := (|ξ| + 3 * |ξ| ^ 2) * C
    have hdom_int : Integrable (fun y : ℝ ↦ L * (1 + |y| + y ^ 2)) μ :=
      (iAdd (iAdd (integrable_const 1) hμ1) hμ2).const_mul L
    have hF_ev : ∀ᶠ a in 𝓝[>] 0,
        AEStronglyMeasurable (fun y ↦ (charFun (K a y) ξ - cexpI ξ y) / (a : ℂ)) μ ∧
          (∀ y : ℝ, ‖(charFun (K a y) ξ - cexpI ξ y) / (a : ℂ)‖ ≤
            L * (1 + |y| + y ^ 2)) ∧
          (∫ y, (charFun (K a y) ξ - cexpI ξ y) / (a : ℂ) ∂μ) = 0 := by
      filter_upwards [Ioo_mem_nhdsGT ha₀, hStat] with a ha ha_stat
      have := hMarkov a ha.1
      have hcf_i : Integrable (fun y ↦ charFun (K a y) ξ) μ :=
        integrable_charFun_kernel μ (K a) ξ
      refine ⟨((iSub hcf_i (integrable_cexpI μ ξ)).div_const (a : ℂ)).aestronglyMeasurable,
        fun y ↦ hStep_bnd |ξ| (abs_nonneg ξ) ξ le_rfl a ha y, ?_⟩
      rw [integral_div, integral_sub hcf_i (integrable_cexpI μ ξ),
        ← charFun_bind_eq μ (K a) ξ, ha_stat, charFun_eq_integral_cexpI, sub_self, zero_div]
    have hlim := tendsto_integral_filter_of_dominated_convergence _
      (hF_ev.mono fun _ h ↦ h.1) (hF_ev.mono fun _ h ↦ ae_of_all _ h.2.1) hdom_int
      (ae_of_all _ fun y ↦ hStep_lim (fun _ ↦ ξ) ξ y tendsto_const_nhds)
    have hzero : (∫ y, cexpI ξ y *
        (Complex.I * ((-ξ * y : ℝ) : ℂ) - ((ξ ^ 2 : ℝ) : ℂ)) ∂μ) = 0 :=
      tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hF_ev.mono fun _ h ↦ h.2.2.symm))
    have hc1_i : Integrable (fun y ↦ cexpI ξ y * (Complex.I * (y : ℂ))) μ :=
      hμ1.mono' ((continuous_cexpI ξ).mul (by fun_prop)).aestronglyMeasurable
        (ae_of_all _ fun y ↦ by
          rw [norm_mul, norm_cexpI, one_mul, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs])
    have heq_int : (fun y : ℝ ↦ cexpI ξ y *
        (Complex.I * ((-ξ * y : ℝ) : ℂ) - ((ξ ^ 2 : ℝ) : ℂ))) =
        fun y ↦ (-(ξ : ℂ)) * (cexpI ξ y * (Complex.I * (y : ℂ))) -
          ((ξ ^ 2 : ℝ) : ℂ) * cexpI ξ y := funext fun y ↦ by
      simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow]; ring
    rw [heq_int, integral_sub (hc1_i.const_mul _) ((integrable_cexpI μ ξ).const_mul _),
      integral_const_mul, integral_const_mul, ← charFun_eq_integral_cexpI] at hzero
    have hmul0 : (-(ξ : ℂ)) * (φ' ξ + (ξ : ℂ) * charFun μ ξ) = 0 := by
      dsimp only [φ']; rw [← hzero]; simp only [Complex.ofReal_pow]; ring
    have hξ_ne : -(ξ : ℂ) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hξ.ne')
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hmul0).resolve_left hξ_ne)
  set Ψ : ℝ → ℂ := fun ξ ↦ Complex.exp (((ξ ^ 2 / 2 : ℝ) : ℂ)) * charFun μ ξ
  have hΨ_cont : Continuous Ψ :=
    (by fun_prop : Continuous fun ξ : ℝ ↦
      Complex.exp (((ξ ^ 2 / 2 : ℝ) : ℂ))).mul hcf_cont
  have hΨ_rderiv : ∀ s : ℝ, 0 < s → HasDerivWithinAt Ψ 0 (Ici s) s := fun s hs ↦ by
    have hd_sq : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 2) s s := by
      simpa only [sub_zero] using
        ((hasDerivAt_sq_sub 0 s).div_const (2 : ℝ)).congr_deriv (by ring)
    have hd_exp : HasDerivAt (fun u : ℝ ↦ Complex.exp (((u ^ 2 / 2 : ℝ) : ℂ)))
        ((s : ℂ) * Complex.exp (((s ^ 2 / 2 : ℝ) : ℂ))) s := by
      simpa only [mul_comm] using hd_sq.ofReal_comp.cexp
    exact (hd_exp.hasDerivWithinAt.mul (hcf_rderiv s)).congr_deriv (by rw [hode s hs]; ring)
  have h_nonneg : ∀ ξ : ℝ, 0 ≤ ξ →
      charFun μ ξ = charFun stdNormalLaw ξ := fun ξ hξ ↦ by
    rcases eq_or_lt_of_le hξ with rfl | hξ_pos
    · simp [charFun_zero]
    · have hΨ_const : ∀ ε ∈ Ioo 0 ξ, Ψ ξ = Ψ ε := fun ε hε ↦
        constant_of_has_deriv_right_zero hΨ_cont.continuousOn
          (fun s hs ↦ hΨ_rderiv s (lt_of_lt_of_le hε.1 hs.1)) ξ ⟨hε.2.le, le_rfl⟩
      have hΨ_lim : Tendsto Ψ (𝓝[>] 0) (𝓝 (Ψ 0)) :=
        (hΨ_cont.tendsto 0).mono_left nhdsWithin_le_nhds
      have hΨ_eq : Ψ ξ = Ψ 0 := tendsto_nhds_unique tendsto_const_nhds
        (hΨ_lim.congr' (eventually_of_mem (Ioo_mem_nhdsGT hξ_pos)
          fun ε hε ↦ (hΨ_const ε hε).symm))
      have hΨ0 : Ψ 0 = 1 := by simp [Ψ, charFun_zero]
      rw [hΨ0] at hΨ_eq; rw [charFun_stdNormalLaw]
      calc charFun μ ξ
        _ = Complex.exp (-(((ξ ^ 2 / 2 : ℝ) : ℂ))) * Ψ ξ := by
            dsimp only [Ψ]; rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel,
              Complex.exp_zero, one_mul]
        _ = Complex.exp (-(((ξ ^ 2 / 2 : ℝ) : ℂ))) := by rw [hΨ_eq, mul_one]
  refine Measure.ext_of_charFun (funext fun ξ ↦ ?_)
  rcases le_or_gt 0 ξ with hξ | hξ
  · exact h_nonneg ξ hξ
  · calc charFun μ ξ = charFun μ (- -ξ) := by rw [neg_neg]
      _ = (starRingEnd ℂ) (charFun μ (-ξ)) := charFun_neg (-ξ)
      _ = (starRingEnd ℂ) (charFun stdNormalLaw (-ξ)) := by rw [h_nonneg (-ξ) (by linarith)]
      _ = charFun stdNormalLaw (- -ξ) := (charFun_neg (-ξ)).symm
      _ = charFun stdNormalLaw ξ := by rw [neg_neg]

/-- Transition semigroup uniqueness (Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem eq_ouKernel_of_infinitesimal
    (hDom : ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ QuadDom K a₀ C)
    (hSemi : ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → K (s + t) = Kernel.comp (K t) (K s))
    {t : ℝ} (ht : 0 < t) : K t = ouKernel t := by
  obtain ⟨a₀, ha₀, C, hC, hDom'⟩ := hDom
  obtain ⟨hStep_bnd, hStep_lim⟩ :=
    cexp_step_bound_and_limit hMarkov hDrift hDiff hLind ha₀ hC hDom'
  refine Kernel.ext fun x ↦ ?_; have := hMarkov t ht
  refine Measure.ext_of_charFun (funext fun ξ₀ ↦ ?_)
  obtain ⟨M, hM_nn, hM⟩ := uniform_sq_bound_of_semigroup hMarkov ha₀ hC hDom' hSemi ht x
  set μs : ℝ → Measure ℝ := fun s ↦ if 0 < s then K s x else Measure.dirac x
  have hμs_prob : ∀ s : ℝ, IsProbabilityMeasure (μs s) := fun s ↦ by
    by_cases hs : 0 < s
    · simp only [μs, hs, ↓reduceIte]; exact (hMarkov s hs).isProbabilityMeasure x
    · simp only [μs, hs, ↓reduceIte]; infer_instance
  have hμs_bind : ∀ s a : ℝ, 0 ≤ s → 0 < a →
      (μs s).bind (K a) = μs (s + a) := fun s a hs ha ↦ by
    rcases eq_or_lt_of_le hs with rfl | hs_pos
    · simp [μs, ha, Measure.dirac_bind (Kernel.measurable _)]
    · have hsa : 0 < s + a := add_pos hs_pos ha
      simp [μs, hs_pos, hsa, hSemi s hs_pos a ha, Kernel.comp_apply]
  set M₀ : ℝ := max (x ^ 2) M
  have hM₀_nn : 0 ≤ M₀ := le_max_of_le_right hM_nn
  have hμs_sq : ∀ s ∈ Icc 0 t,
      Integrable (fun y : ℝ ↦ y ^ 2) (μs s) ∧
        (∫ y, y ^ 2 ∂μs s) ≤ M₀ := fun s hs ↦ by
    rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
    · simp only [μs, lt_irrefl, ↓reduceIte, integral_dirac]
      exact ⟨integrable_dirac (by simp), le_max_left _ _⟩
    · simp only [μs, hs_pos, ↓reduceIte]
      obtain ⟨hI, hL⟩ := hM s ⟨hs_pos, hs.2⟩; exact ⟨hI, hL.trans (le_max_right _ _)⟩
  set ξ : ℝ → ℝ := fun s ↦ Real.exp (-(t - s)) * ξ₀
  have hd_ξ : ∀ s : ℝ, HasDerivAt ξ (ξ s) s := fun s ↦ by
    have h1 : HasDerivAt (fun u : ℝ ↦ -(t - u)) 1 s :=
      (((hasDerivAt_id' s).const_sub t).neg).congr_deriv (by ring)
    exact (h1.exp.mul_const ξ₀).congr_deriv (by dsimp only [ξ]; ring)
  have hξ_le : ∀ s : ℝ, s ≤ t → |ξ s| ≤ |ξ₀| := fun s hs ↦ by
    dsimp only [ξ]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg ξ₀) (Real.exp_le_one_iff.mpr (by linarith))
  have hξ_lip : ∀ s a : ℝ, 0 ≤ a → s + a ≤ t → |ξ (s + a) - ξ s| ≤ |ξ₀| * a :=
    fun s a ha_nn hsa ↦ by
      simpa [Real.norm_eq_abs, abs_of_nonneg ha_nn] using
        norm_sub_le_of_hasDerivAt_ball (x := s) (y := s + a) (C := |ξ₀|) hd_ξ fun u hu ↦ by
          rw [Real.norm_eq_abs]
          exact hξ_le u (by linarith [(abs_le.mp (by simpa [abs_of_nonneg ha_nn] using hu)).2])
  have hcexp_le : ∀ s a y : ℝ, 0 < a → s + a ≤ t →
      ‖(cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)‖ ≤
        |ξ₀| * |y| := fun s a y ha hsa ↦ by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_le_iff₀ ha]
    exact (norm_cexpI_sub_le _ _ _).trans
      ((mul_le_mul_of_nonneg_right (hξ_lip s a ha.le hsa) (abs_nonneg y)).trans_eq (by ring))
  set L₁ : ℝ := (|ξ₀| + 3 * |ξ₀| ^ 2) * C
  have hL₁_nn : 0 ≤ L₁ := by positivity
  set Φ : ℝ → ℂ := fun s ↦ charFun (μs s) (ξ s)
  have hchar_int : ∀ s a : ℝ, 0 ≤ s → 0 < a →
      Integrable (fun y ↦ charFun (K a y) (ξ (s + a))) (μs s) := fun s a _ ha ↦ by
    have := hμs_prob s; have := hMarkov a ha
    exact integrable_charFun_kernel (μs s) (K a) (ξ (s + a))
  have hΦ_decomp : ∀ s a : ℝ, 0 ≤ s → 0 < a → (Φ (s + a) - Φ s) / (a : ℂ) =
      ∫ y, ((charFun (K a y) (ξ (s + a)) - cexpI (ξ (s + a)) y) / (a : ℂ) +
        (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)) ∂μs s := fun s a hs ha ↦ by
    have := hμs_prob s; have := hMarkov a ha
    dsimp only [Φ]; rw [← hμs_bind s a hs ha, charFun_bind_eq (μs s) (K a) (ξ (s + a)),
      charFun_eq_integral_cexpI (μs s) (ξ s),
      ← integral_sub (hchar_int s a hs ha) (integrable_cexpI (μs s) (ξ s)), ← integral_div]
    exact integral_congr_ae (ae_of_all _ fun y ↦ by ring)
  set K_lip : ℝ := L₁ * (2 + 2 * M₀) + |ξ₀| * (1 + M₀)
  have hK_nn : 0 ≤ K_lip := by positivity
  have hdom_info : ∀ s ∈ Icc 0 t,
      Integrable (fun y : ℝ ↦ L₁ * (1 + |y| + y ^ 2) + |ξ₀| * |y|) (μs s) ∧
        (∫ y, (L₁ * (1 + |y| + y ^ 2) + |ξ₀| * |y|) ∂μs s) ≤ K_lip := fun s hs ↦ by
    have := hμs_prob s; obtain ⟨hInt_y2, hInt_y2_le⟩ := hμs_sq s hs
    have hInt_abs := integrable_abs_of_integrable_sq hInt_y2
    have h1 := (iAdd (iAdd (integrable_const 1) hInt_abs) hInt_y2).const_mul L₁
    refine ⟨iAdd h1 (hInt_abs.const_mul |ξ₀|), ?_⟩
    rw [integral_add h1 (hInt_abs.const_mul |ξ₀|), integral_const_mul, integral_const_mul,
      integral_add (iAdd (integrable_const 1) hInt_abs) hInt_y2,
      integral_add (integrable_const 1) hInt_abs, integral_const, probReal_univ, one_smul]
    have habs_le : (∫ y, |y| ∂μs s) ≤ 1 + M₀ := by
      have hm := integral_mono hInt_abs (iAdd (integrable_const 1) hInt_y2)
        fun y ↦ by dsimp only; nlinarith [sq_abs y, abs_nonneg y]
      rw [integral_add (integrable_const 1) hInt_y2, integral_const, probReal_univ,
        one_smul] at hm
      linarith
    dsimp only [K_lip]; nlinarith [abs_nonneg ξ₀]
  have hΦ_cont : ContinuousOn Φ (Icc 0 t) := by
    rw [Metric.continuousOn_iff]; intro s₁ hs₁ ε hε
    refine ⟨min a₀ (ε / (K_lip + 1)), lt_min ha₀ (by positivity), fun s₂ hs₂ hd ↦ ?_⟩
    rw [Real.dist_eq] at hd; rw [dist_eq_norm]
    have hp : ∀ u v : ℝ, u ∈ Icc 0 t → v ∈ Icc 0 t → u ≤ v →
        v - u < min a₀ (ε / (K_lip + 1)) → ‖Φ v - Φ u‖ < ε :=
      fun u v hu hv huv hvu ↦ by
        rcases eq_or_lt_of_le huv with rfl | hlt
        · simpa using hε
        · set a : ℝ := v - u; have ha_pos : 0 < a := sub_pos.mpr hlt
          have ha : a ∈ Ioo 0 a₀ := ⟨ha_pos, lt_of_lt_of_le hvu (min_le_left _ _)⟩
          have hsa : u + a ≤ t := by linarith [hv.2]
          have := hμs_prob u; obtain ⟨hdom_u, hdom_le⟩ := hdom_info u hu
          have hb : ‖(Φ (u + a) - Φ u) / (a : ℂ)‖ ≤ K_lip := by
            rw [hΦ_decomp u a hu.1 ha_pos]
            exact (norm_integral_le_of_norm_le hdom_u (ae_of_all _ fun y ↦
              (norm_add_le _ _).trans (add_le_add
                (hStep_bnd |ξ₀| (abs_nonneg _) (ξ (u + a)) (hξ_le _ hsa) a ha y)
                (hcexp_le u a y ha_pos hsa)))).trans hdom_le
          rw [show u + a = v by ring, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ha_pos, div_le_iff₀ ha_pos] at hb
          nlinarith [(lt_div_iff₀' (by positivity : 0 < K_lip + 1)).mp
            (lt_of_lt_of_le hvu (min_le_right _ _))]
    rcases le_total s₁ s₂ with hle | hle
    · exact hp s₁ s₂ hs₁ hs₂ hle (by rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at hd)
    · rw [norm_sub_rev]
      exact hp s₂ s₁ hs₂ hs₁ hle
        (by rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at hd)
  have hΦ_rderiv : ∀ s ∈ Ico 0 t,
      HasDerivWithinAt Φ (-(((ξ s ^ 2 : ℝ) : ℂ) * Φ s)) (Ici s) s := fun s hs ↦ by
    refine hasDerivWithinAt_Ici_of_tendsto_right ?_
    have := hμs_prob s; obtain ⟨hdom_s, -⟩ := hdom_info s ⟨hs.1, hs.2.le⟩
    have hξ_lim : Tendsto (fun a : ℝ ↦ ξ (s + a)) (𝓝[>] 0) (𝓝 (ξ s)) := by
      have hc : Continuous (fun a : ℝ ↦ ξ (s + a)) := by dsimp [ξ]; fun_prop
      simpa only [add_zero] using (hc.continuousWithinAt (x := 0) (s := Ioi 0)).tendsto
    have hpw_lim : ∀ y : ℝ, Tendsto (fun a : ℝ ↦
        (charFun (K a y) (ξ (s + a)) - cexpI (ξ (s + a)) y) / (a : ℂ) +
        (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ))
        (𝓝[>] 0) (𝓝 (-(((ξ s ^ 2 : ℝ) : ℂ) * cexpI (ξ s) y))) := fun y ↦ by
      have hcexp_lim : Tendsto
          (fun a : ℝ ↦ (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ))
          (𝓝[>] 0) (𝓝 (cexpI (ξ s) y * (Complex.I * ((ξ s * y : ℝ) : ℂ)))) :=
        (hasDerivAt_cexpI_comp (hd_ξ s) y).tendsto_slope_zero_right.congr
          fun a ↦ by simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
      convert (hStep_lim _ (ξ s) y hξ_lim).add hcexp_lim using 2
      simp only [Complex.ofReal_mul, Complex.ofReal_neg]; ring
    set F : ℝ → ℝ → ℂ := fun a y ↦
      (charFun (K a y) (ξ (s + a)) - cexpI (ξ (s + a)) y) / (a : ℂ) +
      (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)
    have hF_ev : ∀ᶠ a in 𝓝[>] 0, AEStronglyMeasurable (F a) (μs s) ∧
        (∀ y : ℝ, ‖F a y‖ ≤ L₁ * (1 + |y| + y ^ 2) + |ξ₀| * |y|) ∧
        (Φ (s + a) - Φ s) / (a : ℂ) = ∫ y, F a y ∂μs s := by
      filter_upwards [Ioo_mem_nhdsGT (lt_min ha₀ (sub_pos.mpr hs.2))] with a ha
      have ha_pos := ha.1; have ha_a₀ := lt_of_lt_of_le ha.2 (min_le_left _ _)
      have hsa : s + a ≤ t := by linarith [lt_of_lt_of_le ha.2 (min_le_right _ _)]
      have hF_int : Integrable (F a) (μs s) :=
        iAdd ((iSub (hchar_int s a hs.1 ha_pos) (integrable_cexpI _ _)).div_const (a : ℂ))
          ((iSub (integrable_cexpI _ _) (integrable_cexpI _ _)).div_const (a : ℂ))
      exact ⟨hF_int.aestronglyMeasurable, fun y ↦ (norm_add_le _ _).trans (add_le_add
        (hStep_bnd |ξ₀| (abs_nonneg _) (ξ (s + a)) (hξ_le _ hsa) a ⟨ha_pos, ha_a₀⟩ y)
        (hcexp_le s a y ha_pos hsa)), hΦ_decomp s a hs.1 ha_pos⟩
    have hlim_int := tendsto_integral_filter_of_dominated_convergence _
      (hF_ev.mono fun _ h ↦ h.1) (hF_ev.mono fun _ h ↦ ae_of_all _ h.2.1) hdom_s
      (ae_of_all _ hpw_lim)
    rw [integral_neg, integral_const_mul, ← charFun_eq_integral_cexpI] at hlim_int
    exact hlim_int.congr' (hF_ev.mono fun _ h ↦ h.2.2.symm)
  set Ψ : ℝ → ℂ := fun s ↦ Complex.exp (((ξ s ^ 2 / 2 : ℝ) : ℂ)) * Φ s
  have hΨ_cont : ContinuousOn Ψ (Icc 0 t) :=
    (by dsimp [ξ]; fun_prop : Continuous fun s : ℝ ↦
      Complex.exp (((ξ s ^ 2 / 2 : ℝ) : ℂ))).continuousOn.mul hΦ_cont
  have hΨ_deriv : ∀ s ∈ Ico 0 t, HasDerivWithinAt Ψ 0 (Ici s) s := fun s hs ↦ by
    have hd_sq : HasDerivAt (fun u : ℝ ↦ ξ u ^ 2 / 2) (ξ s ^ 2) s := by
      have hm : HasDerivAt (fun u : ℝ ↦ (ξ u * ξ u) / 2) (ξ s ^ 2) s :=
        (((hd_ξ s).fun_mul (hd_ξ s)).div_const (2 : ℝ)).congr_deriv (by ring)
      exact (show (fun u : ℝ ↦ (ξ u * ξ u) / 2) = fun u ↦ ξ u ^ 2 / 2 from
        funext fun u ↦ by rw [sq]) ▸ hm
    have hd_cexp : HasDerivAt (fun u : ℝ ↦ Complex.exp (((ξ u ^ 2 / 2 : ℝ) : ℂ)))
        (((ξ s ^ 2 : ℝ) : ℂ) * Complex.exp (((ξ s ^ 2 / 2 : ℝ) : ℂ))) s := by
      simpa only [mul_comm] using hd_sq.ofReal_comp.cexp
    exact (hd_cexp.hasDerivWithinAt.mul (hΦ_rderiv s hs)).congr_deriv (by ring)
  have hΨ_eq : Ψ t = Ψ 0 :=
    constant_of_has_deriv_right_zero hΨ_cont hΨ_deriv t ⟨ht.le, le_rfl⟩
  have hΦ0 : Φ 0 = cexpI (Real.exp (-t) * ξ₀) x := by
    have hμ0 : μs 0 = Measure.dirac x := by simp [μs]
    dsimp only [Φ, ξ]
    rw [hμ0, sub_zero, charFun_eq_integral_cexpI, integral_dirac]
  have hΦt : Φ t = charFun (K t x) ξ₀ := by
    have hμt : μs t = K t x := by simp [μs, ht]
    dsimp only [Φ, ξ]
    rw [hμt, sub_self, neg_zero, Real.exp_zero, one_mul]
  rw [show Ψ t = Complex.exp (((ξ₀ ^ 2 / 2 : ℝ) : ℂ)) * charFun (K t x) ξ₀ by
        dsimp only [Ψ]; rw [hΦt]; simp only [ξ, sub_self, neg_zero, Real.exp_zero, one_mul],
      show Ψ 0 = Complex.exp ((((Real.exp (-t) * ξ₀) ^ 2 / 2 : ℝ) : ℂ)) *
        cexpI (Real.exp (-t) * ξ₀) x by dsimp only [Ψ]; rw [hΦ0]; simp only [ξ, sub_zero]]
    at hΨ_eq
  have hcancel : charFun (K t x) ξ₀ = Complex.exp (-(((ξ₀ ^ 2 / 2 : ℝ) : ℂ))) *
      (Complex.exp ((((Real.exp (-t) * ξ₀) ^ 2 / 2 : ℝ) : ℂ)) *
        cexpI (Real.exp (-t) * ξ₀) x) := by
    rw [← hΨ_eq, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rw [hcancel, cexpI_eq_ofReal_mul, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add,
    charFun_ouKernel ht x ξ₀]
  congr 1
  have hre : (1 - Real.exp (-2 * t)) * ξ₀ ^ 2 / 2 =
      ξ₀ ^ 2 / 2 - (Real.exp (-t) * ξ₀) ^ 2 / 2 := by
    have he2 : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by rw [sq, ← Real.exp_add]; congr 1; ring
    rw [mul_pow, he2]; ring
  have him : (Real.exp (-t) * ξ₀) * x = ξ₀ * (Real.exp (-t) * x) := by ring
  rw [him, hre, Complex.ofReal_sub]; ring

end Infinitesimal

/-- Moment-free stationary-law uniqueness for `ouKernel`
(Remark 3.5, `SteinIntro.tex:1018-1019`). -/
theorem eq_stdNormalLaw_of_bind_ouKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hStat : μ.bind (ouKernel t₀) = μ) : μ = stdNormalLaw := by
  have hbind : ∀ n : ℕ, μ.bind (ouKernel (((n : ℝ) + 1) * t₀)) = μ := fun n ↦ by
    induction n with
    | zero => simpa using hStat
    | succ n ih =>
      have hn : 0 < ((n : ℝ) + 1) * t₀ := by positivity
      have hadd : (((n + 1 : ℕ) : ℝ) + 1) * t₀ = ((n : ℝ) + 1) * t₀ + t₀ := by
        push_cast; ring
      rw [hadd, ouKernel_comp hn ht₀, ← Measure.comp_assoc, ih, hStat]
  refine Measure.ext_of_charFun (funext fun ξ ↦ ?_)
  set tn : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) * t₀
  have htn_pos : ∀ n : ℕ, 0 < tn n := fun n ↦ by dsimp [tn]; positivity
  have hdecay : ∀ c : ℝ, c < 0 →
      Tendsto (fun n : ℕ ↦ Real.exp (c * tn n)) atTop (𝓝 0) := fun c hc ↦ by
    have h1 : Tendsto tn atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const ht₀
    have h2 : Tendsto (fun n : ℕ ↦ c * tn n) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp (h1.atTop_mul_const (neg_pos.mpr hc))).congr
        fun n ↦ by dsimp only [Function.comp_apply]; ring
    exact Real.tendsto_exp_atBot.comp h2
  have hpw : ∀ y : ℝ, Tendsto (fun n : ℕ ↦ charFun (ouKernel (tn n) y) ξ)
      atTop (𝓝 (Complex.exp (-(((ξ ^ 2 / 2 : ℝ) : ℂ))))) := fun y ↦ by
    simp_rw [fun n ↦ charFun_ouKernel (htn_pos n) y ξ]
    have h1 : Tendsto (fun n : ℕ ↦ ξ * (Real.exp (-tn n) * y)) atTop (𝓝 0) := by
      have hd : Tendsto (fun n : ℕ ↦ Real.exp (-tn n)) atTop (𝓝 0) :=
        (hdecay (-1) (by norm_num)).congr fun n ↦ by congr 1; ring
      simpa using ((hd.mul_const y).const_mul ξ)
    have h2 : Tendsto (fun n : ℕ ↦ (1 - Real.exp (-2 * tn n)) * ξ ^ 2 / 2)
        atTop (𝓝 (ξ ^ 2 / 2)) := by
      simpa only [sub_zero, one_mul] using
        (((tendsto_const_nhds (x := (1 : ℝ))).sub (hdecay (-2) (by norm_num))).mul_const
          (ξ ^ 2)).div_const 2
    have hc : Tendsto (fun n : ℕ ↦
        (((ξ * (Real.exp (-tn n) * y) : ℝ) : ℂ) * Complex.I) -
          ((((1 - Real.exp (-2 * tn n)) * ξ ^ 2 / 2 : ℝ) : ℂ)))
        atTop (𝓝 (-(((ξ ^ 2 / 2 : ℝ) : ℂ)))) := by
      simpa using (((Complex.continuous_ofReal.tendsto 0).comp h1).mul_const Complex.I).sub
        ((Complex.continuous_ofReal.tendsto _).comp h2)
    exact hc.cexp
  have hdom := tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ (1 : ℝ))
    (fun n ↦ (integrable_charFun_kernel μ (ouKernel (tn n)) ξ).aestronglyMeasurable)
    (integrable_const (1 : ℝ)) (fun n ↦ ae_of_all _ fun y ↦ norm_charFun_le_one ξ)
    (ae_of_all _ hpw)
  rw [integral_const, probReal_univ, one_smul] at hdom
  have hconst : Tendsto (fun _ : ℕ ↦ charFun μ ξ) atTop
      (𝓝 (Complex.exp (-(((ξ ^ 2 / 2 : ℝ) : ℂ))))) :=
    hdom.congr fun n ↦ by rw [← charFun_bind_eq μ (ouKernel (tn n)) ξ, hbind n]
  rw [charFun_stdNormalLaw]
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-! ### Section 5: Master Uniqueness Theorem (`Rem3_5_uniqueness_restricted`) -/

/-- Full proof of `Rem3_5_uniqueness_restricted` (`SteinIntro.tex:1009-1024`; `BL8`). -/
theorem rem3_5_uniqueness_restricted_proof :
    ((∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t →
        ouKernel (s + t) = Kernel.comp (ouKernel t) (ouKernel s)) ∧
      (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
        Tendsto
          (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂ouKernel a x) / a)
          (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Ioo 0 a₀, ∀ x : ℝ,
        Integrable (fun y : ℝ ↦ (y - x) ^ 2) (ouKernel a x) ∧
          |∫ y, (y - x) ∂ouKernel a x| ≤ C * a * (1 + |x|) ∧
          (∫ y, (y - x) ^ 2 ∂ouKernel a x) ≤ C * a * (1 + x ^ 2))) ∧
    (∀ K : ℝ → Kernel ℝ ℝ,
      (∀ a : ℝ, 0 < a → IsMarkovKernel (K a)) →
      (∀ x : ℝ, Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) →
      (∀ x : ℝ, Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) →
      (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
        Tendsto (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂K a x) / a)
          (nhdsWithin 0 (Ioi 0)) (nhds 0)) →
      (((∀ x : ℝ, ∀ᶠ a in nhdsWithin 0 (Ioi 0),
            Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x)) →
          ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
            (∃ B : ℝ, (∀ u : ℝ, |f u| ≤ B) ∧ (∀ u : ℝ, |deriv f u| ≤ B)) →
            ∀ x : ℝ, Tendsto
              (fun a : ℝ ↦
                (∫ y, ((∫ u in (0 : ℝ)..y, f u) - (∫ u in (0 : ℝ)..x, f u)) ∂K a x) / a)
              (nhdsWithin 0 (Ioi 0)) (nhds (normalSteinOp f x))) ∧
        ((∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Ioo 0 a₀, ∀ x : ℝ,
            Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x) ∧
              |∫ y, (y - x) ∂K a x| ≤ C * a * (1 + |x|) ∧
              (∫ y, (y - x) ^ 2 ∂K a x) ≤ C * a * (1 + x ^ 2)) →
          (∀ μ : Measure ℝ, IsProbabilityMeasure μ →
            Integrable (fun x : ℝ ↦ x ^ 2) μ →
            (∀ᶠ a in nhdsWithin 0 (Ioi 0), μ.bind (K a) = μ) → μ = stdNormalLaw) ∧
          ((∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → K (s + t) = Kernel.comp (K t) (K s)) →
            (∀ t : ℝ, 0 < t → K t = ouKernel t) ∧
              (∀ μ : Measure ℝ, IsProbabilityMeasure μ →
                (∃ t₀ : ℝ, 0 < t₀ ∧ μ.bind (K t₀) = μ) →
                  μ = stdNormalLaw))))) := by
  refine ⟨⟨fun _ hs _ ht ↦ ouKernel_comp hs ht, fun x _ hε ↦ ouKernel_lindeberg_tail x hε,
    ⟨1, zero_lt_one, 2, zero_le_two, ouKernel_quadratic_domination⟩⟩, ?_⟩
  intro K hMarkov hDrift hDiff hLind
  refine ⟨fun hInt2_loc _ hf hB x ↦
      tendsto_ouGenerator_normalSteinOp hMarkov hDrift hDiff hLind hInt2_loc hf hB x,
    fun hDom ↦ ⟨fun μ _ hμ2 hStat ↦
        eq_stdNormalLaw_of_stationary_infinitesimal hMarkov hDrift hDiff hLind hDom μ hμ2 hStat,
      fun hSemi ↦ ⟨fun _ ht ↦
          eq_ouKernel_of_infinitesimal hMarkov hDrift hDiff hLind hDom hSemi ht,
        fun μ _ ⟨t₀, ht₀, hStat⟩ ↦ ?_⟩⟩⟩
  rw [eq_ouKernel_of_infinitesimal hMarkov hDrift hDiff hLind hDom hSemi ht₀] at hStat
  exact eq_stdNormalLaw_of_bind_ouKernel μ ht₀ hStat

end SteinMethod
