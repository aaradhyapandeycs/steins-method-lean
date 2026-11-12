/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.Concentration
import Formalization.Concentration.Basic
import Formalization.Concentration.Exchangeable
import Formalization.Concentration.IndepSumPair
import Formalization.Concentration.IndepSum
import Formalization.Concentration.CombinatorialPair
import Formalization.Concentration.Combinatorial
import Formalization.Concentration.CurieWeiss

/-!
# Section 7 Concentration Follow-ups (`Formalization.Concentration.Followups`)

Addresses follow-up items F5-1 to F5-8 from `docs/reviews/review-05F.md` for Section 7
(*Concentration Inequalities*, `SteinIntro.tex:3389-3804`):

* `Sec7_eq7_4` / `Sec7_eq7_4_holds` (**F5-8**, eq. `(7.4)` `\label{2212a}`,
  `SteinIntro.tex:3549-3552`):
  cleared-denominator exponential chord inequality $|e^x - e^y| \le |x - y|\frac{e^x + e^y}{2}$.
* `indepSum_unitInterval_bound_order` / `Ex7_4_2_order` / `Ex7_4_2_order_holds` (**F5-6**,
  Example 7.4(2) exponential order `L3528`): $\exp(-t^2/(2\mu+t))/e^{-t} \to e^{2\mu}$ as
  $t \to \infty$ for constant $\mu \ge 0$.
* `stdNormal_minimizer`, `stdNormal_concentration_with_minimizer` (**F5-5**, Example 7.1,
  `SteinIntro.tex:3439`): optimality of the minimizer $\theta = t$,
  $e^{-t^2/2} \le e^{\theta^2/2 - \theta t}$ for all $\theta \in \mathbb{R}$ and $t > 0$.
* `poisson_minimizer`, `poisson_concentration_with_minimizer` (**F5-5**, Example 7.2,
  `SteinIntro.tex:3454`): optimality of the minimizer $\theta = \log(1 + t/\lambda)$,
  $B(\lambda, t) \le \exp(\lambda(e^\theta - 1) - \theta(t + \lambda))$ for all $\theta$.
* `poisson_bound_order_not_tendsto_of_le`, `not_poisson_bound_order_printed_strengthened` (**F5-3**,
  Example 7.2 `SteinIntro.tex:3458`; `ISSUE-EX7.2`): machine-checked refutation that
  $\lim_{t \to \infty} e^{-t\log t}/B(\lambda, t) = 0$ fails for every $\lambda \in (0, e^{-1}]$.
* `curieWeiss_mode_extended` (**F5-7**, Section 7.2 Curie–Weiss mode, `SteinIntro.tex:3640-3641`):
  includes the $h = 0$ constant-spin tie and strict dominance over non-constant configurations.
* `combinatorial_isSteinPair_relaxed` (**F5-1**, Example 7.5, `SteinIntro.tex:3597-3611`;
  `ISSUE-TYPO-7.5`, `ISSUE-7.5`): relaxes binder to $n \ge 2$, proving $\mathbb{E}[W] = 0$, pair
  exchangeability, conditional linearity $\mathbb{E}[W' \mid W] = (1 - \frac{2}{n-1})W$, and
  $3 \le n \to \text{IsSteinPair}$ (differs only by dropping Def 3.2's $a \le 1$ at $n = 2$).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Nat Topology

namespace SteinMethod

/-! ### F5-6: Example 7.4(2) Exponential Order of Bound `(7.2)` (`Ex7_4_2_order`) -/

/-- **Example 7.4(2), exponential order of `(7.2)`** (`Ex7_4_2_order`, `\label{21198}`,
`SteinIntro.tex:3528`): for constant $\mu \ge 0$,
$\exp(-t^2 / (2\mu + t)) / e^{-t} \to e^{2\mu}$ as $t \to \infty$, so the upper bound `(7.2)` is
of order $e^{-t}$. -/
theorem indepSum_unitInterval_bound_order {μ : ℝ} (hμ : 0 ≤ μ) :
    Tendsto (fun t : ℝ ↦ Real.exp (-t ^ 2 / (2 * μ + t)) / Real.exp (-t))
      atTop (nhds (Real.exp (2 * μ))) := by
  have hfrac : ∀ t : ℝ, 0 < t →
      -t ^ 2 / (2 * μ + t) - -t = 2 * μ / (2 * μ / t + 1) := by
    intro t ht
    have hden : 2 * μ + t ≠ 0 := by positivity
    have ht_ne : t ≠ 0 := ht.ne'
    field_simp
    ring
  have hlim_inner : Tendsto (fun t : ℝ ↦ 2 * μ / (2 * μ / t + 1))
      atTop (nhds (2 * μ)) := by
    have h1 : Tendsto (fun t : ℝ ↦ 2 * μ / t) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun t : ℝ ↦ 2 * μ / t + 1) atTop (nhds (0 + 1)) :=
      h1.add tendsto_const_nhds
    rw [zero_add] at h2
    have h3 : Tendsto (fun t : ℝ ↦ 2 * μ / (2 * μ / t + 1)) atTop
        (nhds (2 * μ / 1)) :=
      (tendsto_const_nhds (x := 2 * μ)).div h2 one_ne_zero
    rwa [div_one] at h3
  have hlim_exp : Tendsto (fun t : ℝ ↦ Real.exp (2 * μ / (2 * μ / t + 1)))
      atTop (nhds (Real.exp (2 * μ))) :=
    (Real.continuous_exp.tendsto (2 * μ)).comp hlim_inner
  refine Tendsto.congr' ?_ hlim_exp
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [← Real.exp_sub, hfrac t ht]

/-! ### F5-5: Minimizer Conjuncts for Example 7.1 and Example 7.2 -/

/-- Example 7.1 minimizer optimality (`SteinIntro.tex:3439`): for every $\theta \in \mathbb{R}$
and $t > 0$, $e^{-t^2/2} \le e^{\theta^2/2 - \theta t}$. -/
theorem stdNormal_minimizer (θ t : ℝ) (_ht : 0 < t) :
    Real.exp (-t ^ 2 / 2) ≤ Real.exp (θ ^ 2 / 2 - θ * t) :=
  Real.exp_le_exp.mpr (by have := sq_nonneg (θ - t); nlinarith)

/-- Example 7.1 extended with the minimizer optimality conjunct (`SteinIntro.tex:3428-3445`). -/
theorem stdNormal_concentration_with_minimizer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ : AEMeasurable Z P) (hlaw : P.map Z = stdNormalLaw) :
    (∀ t : ℝ, 0 < t →
        P.real {ω | t ≤ Z ω} ≤ Real.exp (-t ^ 2 / 2) / (t * Real.sqrt (2 * Real.pi))) ∧
      (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * Z ω)) P ∧
        ∫ ω, Real.exp (θ * Z ω) ∂P = Real.exp (θ ^ 2 / 2)) ∧
      (∀ θ t : ℝ, 0 < θ → 0 < t →
        P.real {ω | t ≤ Z ω} ≤ Real.exp (θ ^ 2 / 2 - θ * t)) ∧
      (∀ θ t : ℝ, 0 < t → Real.exp (-t ^ 2 / 2) ≤ Real.exp (θ ^ 2 / 2 - θ * t)) ∧
      (∀ t : ℝ, 0 < t → P.real {ω | t ≤ Z ω} ≤ Real.exp (-t ^ 2 / 2)) := by
  obtain ⟨h1, h2, h3, h5⟩ := stdNormal_concentration P hZ hlaw
  exact ⟨h1, h2, h3, stdNormal_minimizer, h5⟩

/-- Example 7.2 minimizer optimality (`SteinIntro.tex:3454`): for every $\lambda > 0$,
$\theta \in \mathbb{R}$, and $t > 0$,
$B(\lambda, t) \le e^{\lambda(e^\theta - 1) - \theta(t+\lambda)}$. -/
theorem poisson_minimizer (lam : ℝ) (hlam : 0 < lam) (θ t : ℝ) (ht : 0 < t) :
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    B t ≤ Real.exp (lam * (Real.exp θ - 1) - θ * (t + lam)) := by
  dsimp only
  refine Real.exp_le_exp.mpr ?_
  have hu_pos : 0 < 1 + t / lam := by linarith [div_pos ht hlam]
  have h1 : 1 + (θ - Real.log (1 + t / lam)) ≤ Real.exp (θ - Real.log (1 + t / lam)) := by
    linarith [Real.add_one_le_exp (θ - Real.log (1 + t / lam))]
  rw [Real.exp_sub, Real.exp_log hu_pos] at h1
  have htpl_pos : 0 < t + lam := add_pos ht hlam
  have hmul : (1 + (θ - Real.log (1 + t / lam))) * (t + lam) ≤
      (Real.exp θ / (1 + t / lam)) * (t + lam) := mul_le_mul_of_nonneg_right h1 htpl_pos.le
  have hdiv_cancel : (Real.exp θ / (1 + t / lam)) * (t + lam) = lam * Real.exp θ := by
    have heq : t + lam = lam * (1 + t / lam) := by field_simp [hlam.ne']; ring
    rw [heq]
    have : 1 + t / lam ≠ 0 := hu_pos.ne'
    field_simp
  rw [hdiv_cancel] at hmul
  have hlin : (1 + (θ - Real.log (1 + t / lam))) * (t + lam) =
      (t + lam) + θ * (t + lam) - (t + lam) * Real.log (1 + t / lam) := by ring
  rw [hlin] at hmul
  have hB_exp : -t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam) =
      (t + lam) - (t + lam) * Real.log (1 + t / lam) - lam := by ring
  have hR_exp : lam * (Real.exp θ - 1) - θ * (t + lam) =
      lam * Real.exp θ - lam - θ * (t + lam) := by ring
  linarith

/-- Example 7.2 extended with the minimizer optimality conjunct (`SteinIntro.tex:3447-3461`). -/
theorem poisson_concentration_with_minimizer
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {Z : Ω → ℕ}
    (hr : 0 < r) (hZ : AEMeasurable Z P) (hlaw : P.map Z = poissonLaw r) :
    let lam : ℝ := (r : ℝ)
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * (Z ω : ℝ))) P ∧
        ∫ ω, Real.exp (θ * (Z ω : ℝ)) ∂P = Real.exp (lam * (Real.exp θ - 1))) ∧
      (∀ θ t : ℝ, 0 < θ → 0 < t →
        P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤
          Real.exp (lam * (Real.exp θ - 1) - θ * (t + lam))) ∧
      (∀ θ t : ℝ, 0 < t → B t ≤ Real.exp (lam * (Real.exp θ - 1) - θ * (t + lam))) ∧
      (∀ t : ℝ, 0 < t → P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤ B t) ∧
      (∀ c : ℝ, 0 < c →
        Filter.Tendsto (fun t : ℝ ↦ B t / Real.exp (-c * t)) Filter.atTop (nhds 0)) := by
  dsimp only
  obtain ⟨h1, h2, h4, h5⟩ := poisson_concentration P hr hZ hlaw
  set lam : ℝ := (r : ℝ)
  have hlam : 0 < lam := NNReal.coe_pos.mpr hr
  exact ⟨h1, h2, poisson_minimizer lam hlam, h4, h5⟩

/-! ### F5-3: Asymptotic Refutation for all $\lambda \in (0, e^{-1}]$ (`ISSUE-EX7.2`) -/

/-- For every $\lambda \in (0, e^{-1}]$, the ratio $e^{-t\log t}/B(\lambda, t) \ge 1$ for all
$t \ge 1$, refuting $\lim_{t \to \infty} e^{-t\log t}/B(\lambda, t) = 0$
(strengthening `not_poisson_bound_order_printed`, `SteinIntro.tex:3458`; `ISSUE-EX7.2`). -/
theorem poisson_bound_order_not_tendsto_of_le {lam : ℝ} (hlam_pos : 0 < lam)
    (hlam_le : lam ≤ Real.exp (-1)) :
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    ¬ Filter.Tendsto (fun t : ℝ ↦ Real.exp (-t * Real.log t) / B t) Filter.atTop (nhds 0) := by
  dsimp only
  intro htend
  have hlog_lam_le : Real.log lam ≤ -1 := by
    rw [← Real.log_exp (-1)]
    exact Real.log_le_log hlam_pos hlam_le
  have hge1 : ∀ᶠ t : ℝ in atTop,
      1 ≤ Real.exp (-t * Real.log t) /
        Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    rw [← Real.exp_sub, Real.one_le_exp_iff]
    have hle_arg : t / lam ≤ 1 + t / lam := by linarith
    have hlog_ge : Real.log t - Real.log lam ≤ Real.log (1 + t / lam) := by
      have h1 := Real.log_le_log (div_pos ht0 hlam_pos) hle_arg
      rw [Real.log_div ht0.ne' hlam_pos.ne'] at h1
      linarith
    have hlog_nn : 0 ≤ Real.log (1 + t / lam) := by
      have : 0 ≤ Real.log t := Real.log_nonneg ht
      linarith
    have hE : -t * Real.log t - (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam)) =
        t * (Real.log (1 + t / lam) - Real.log t - 1) + lam * Real.log (1 + t / lam) := by ring
    rw [hE]
    nlinarith [mul_nonneg ht0.le (show 0 ≤ Real.log (1 + t / lam) - Real.log t - 1 by linarith),
      mul_nonneg hlam_pos.le hlog_nn]
  have h1le0 : (1 : ℝ) ≤ 0 := ge_of_tendsto htend hge1
  linarith

/-- Refutation of the printed Example 7.2 order claim across all $\lambda > 0$ (`ISSUE-EX7.2`). -/
theorem not_poisson_bound_order_printed_strengthened :
    ¬ (∀ {lam : ℝ}, 0 < lam →
      let B : ℝ → ℝ := fun t ↦
        Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
      Filter.Tendsto (fun t : ℝ ↦ Real.exp (-t * Real.log t) / B t) Filter.atTop (nhds 0)) :=
  fun hall ↦
    poisson_bound_order_not_tendsto_of_le (Real.exp_pos (-1)) le_rfl (hall (Real.exp_pos (-1)))

/-! ### F5-7: Curie–Weiss Ground-State Mode Maximizers Including $h = 0$ Tie -/

/-- Ground-state mode maximizers of the Curie–Weiss Gibbs weight and probability mass
(`SteinIntro.tex:3640-3641`): for $\beta > 0$, the all-$(+1)$ configuration uniquely maximizes
`(7.6)` when $h > 0$, the all-$(-1)$ configuration uniquely maximizes `(7.6)` when $h < 0$, and at
$h = 0$ both constant configurations tie as maximizers and strictly dominate every non-constant
configuration. -/
theorem curieWeiss_mode_extended {n : ℕ} {β h : ℝ} (hβ : 0 < β) :
    (0 < h →
        ∀ x : Fin n → Bool,
          x ≠ (fun _ ↦ true) →
          curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ true) ∧
            (curieWeissMeasure n β h).real {x} <
              (curieWeissMeasure n β h).real {fun _ ↦ true}) ∧
      (h < 0 →
        ∀ x : Fin n → Bool,
          x ≠ (fun _ ↦ false) →
          curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ false) ∧
            (curieWeissMeasure n β h).real {x} <
              (curieWeissMeasure n β h).real {fun _ ↦ false}) ∧
      (h = 0 →
        curieWeissWeight n β h (fun _ ↦ true) = curieWeissWeight n β h (fun _ ↦ false) ∧
          (curieWeissMeasure n β h).real {fun _ ↦ true} =
            (curieWeissMeasure n β h).real {fun _ ↦ false} ∧
          ∀ x : Fin n → Bool,
            x ≠ (fun _ ↦ true) →
            x ≠ (fun _ ↦ false) →
            curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ true) ∧
              (curieWeissMeasure n β h).real {x} <
                (curieWeissMeasure n β h).real {fun _ ↦ true}) := by
  have hpair_le : ∀ (x : Fin n → Bool) (b : Bool),
      β / (n : ℝ) *
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin (x i) * spin (x j)) ≤
        β / (n : ℝ) *
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin b * spin b) := by
    intro x b
    refine mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_)
      (div_nonneg hβ.le (Nat.cast_nonneg n))
    cases hxi : x i <;> cases hxj : x j <;> cases b <;> simp [spin]
  have hZinv : 0 < (curieWeissPartition n β h)⁻¹ := inv_pos.mpr (curieWeissPartition_pos n β h)
  refine ⟨?_, ?_, ?_⟩
  · intro hh x hx
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    have hxi₀ : x i₀ = false := Bool.eq_false_iff.mpr hi₀
    have hsum_lt : (∑ i : Fin n, spin (x i)) < ∑ _i : Fin n, spin true :=
      Finset.sum_lt_sum (fun i _ ↦ by cases x i <;> simp [spin])
        ⟨i₀, Finset.mem_univ i₀, by simp [hxi₀, spin]⟩
    have hfield_lt : β * h * (∑ i : Fin n, spin (x i)) < β * h * ∑ _i : Fin n, spin true :=
      mul_lt_mul_of_pos_left hsum_lt (mul_pos hβ hh)
    have hw_lt : curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ true) :=
      Real.exp_lt_exp.mpr (add_lt_add_of_le_of_lt (hpair_le x true) hfield_lt)
    refine ⟨hw_lt, ?_⟩
    rw [curieWeissMeasure_real_singleton, curieWeissMeasure_real_singleton]
    exact mul_lt_mul_of_pos_left hw_lt hZinv
  · intro hh x hx
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    have hxi₀ : x i₀ = true := by cases h : x i₀ <;> simp_all
    have hsum_gt : (∑ _i : Fin n, spin false) < ∑ i : Fin n, spin (x i) :=
      Finset.sum_lt_sum (fun i _ ↦ by cases x i <;> simp [spin])
        ⟨i₀, Finset.mem_univ i₀, by simp [hxi₀, spin]⟩
    have hfield_lt : β * h * (∑ i : Fin n, spin (x i)) < β * h * ∑ _i : Fin n, spin false :=
      mul_lt_mul_of_neg_left hsum_gt (mul_neg_of_pos_of_neg hβ hh)
    have hw_lt : curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ false) :=
      Real.exp_lt_exp.mpr (add_lt_add_of_le_of_lt (hpair_le x false) hfield_lt)
    refine ⟨hw_lt, ?_⟩
    rw [curieWeissMeasure_real_singleton, curieWeissMeasure_real_singleton]
    exact mul_lt_mul_of_pos_left hw_lt hZinv
  · rintro rfl
    have hw_tf : curieWeissWeight n β 0 (fun _ ↦ true) =
        curieWeissWeight n β 0 (fun _ ↦ false) := by
      unfold curieWeissWeight; simp only [mul_zero, zero_mul, add_zero]
      have hpair : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin true * spin true) =
          ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin false * spin false := by
        congr 1; ext i; congr 1; ext j; simp [spin]
      rw [hpair]
    have hm_tf : (curieWeissMeasure n β 0).real {fun _ ↦ true} =
        (curieWeissMeasure n β 0).real {fun _ ↦ false} := by
      rw [curieWeissMeasure_real_singleton, curieWeissMeasure_real_singleton, hw_tf]
    refine ⟨hw_tf, hm_tf, fun x hxt hxf ↦ ?_⟩
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hxt
    have hxi₀ : x i₀ = false := by cases h : x i₀ <;> simp_all
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hxf
    have hxj₀ : x j₀ = true := by cases h : x j₀ <;> simp_all
    have hne : i₀ ≠ j₀ := by rintro rfl; rw [hxi₀] at hxj₀; cases hxj₀
    have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr i₀.pos
    obtain ⟨a, b, hab_lt, hab_ne⟩ : ∃ a b : Fin n, a < b ∧
        spin (x a) * spin (x b) < spin true * spin true := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨i₀, j₀, hlt, by simp [hxi₀, hxj₀, spin]⟩
      · exact ⟨j₀, i₀, hgt, by simp [hxi₀, hxj₀, spin]⟩
    have hinner_le : ∀ i : Fin n,
        (∑ j ∈ Finset.univ.filter (i < ·), spin (x i) * spin (x j)) ≤
          ∑ j ∈ Finset.univ.filter (i < ·), spin true * spin true := by
      intro i; refine Finset.sum_le_sum fun j _ ↦ ?_; cases x i <;> cases x j <;> simp [spin]
    have hinner_lt :
        (∑ j ∈ Finset.univ.filter (a < ·), spin (x a) * spin (x j)) <
          ∑ j ∈ Finset.univ.filter (a < ·), spin true * spin true := by
      have hb_mem : b ∈ Finset.univ.filter (a < ·) := by simp [hab_lt]
      refine Finset.sum_lt_sum (fun j _ ↦ ?_) ⟨b, hb_mem, hab_ne⟩
      cases x a <;> cases x j <;> simp [spin]
    have hsum_lt : (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin (x i) * spin (x j)) <
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin true * spin true :=
      Finset.sum_lt_sum (fun i _ ↦ hinner_le i) ⟨a, Finset.mem_univ a, hinner_lt⟩
    have hpow_lt : β / (n : ℝ) *
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin (x i) * spin (x j)) <
        β / (n : ℝ) *
          ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin true * spin true :=
      mul_lt_mul_of_pos_left hsum_lt (div_pos hβ hrn_pos)
    have hw_lt : curieWeissWeight n β 0 x < curieWeissWeight n β 0 (fun _ ↦ true) := by
      unfold curieWeissWeight; simp only [mul_zero, zero_mul, add_zero]
      exact Real.exp_lt_exp.mpr hpow_lt
    refine ⟨hw_lt, ?_⟩
    rw [curieWeissMeasure_real_singleton, curieWeissMeasure_real_singleton]
    exact mul_lt_mul_of_pos_left hw_lt (inv_pos.mpr (curieWeissPartition_pos n β 0))

/-! ### F5-1: Relaxed Combinatorial Stein Pair Theorem ($n \ge 2$) -/

/-- **Example 7.5, Stein-pair property restricted to $n \ge 2$** (`Ex7_5_steinPair_restricted`,
`SteinIntro.tex:3597-3611`; `ISSUE-TYPO-7.5`, `ISSUE-7.5`): for an array
$(a_{ij})_{1 \le i,j \le n}$ with $n \ge 2$, a uniform permutation $\sigma$, and an independent
uniform transposition $\tau$, $\mathbb{E}[W] = 0$, $(W, W')$ is exchangeable with linear
regression $\mathbb{E}[W' \mid W] = (1 - \frac{2}{n - 1}) W$, and when $n \ge 3$ it forms a
$\frac{2}{n - 1}$-Stein pair (differs only by dropping Def 3.2's $a \le 1$ at $n = 2$). -/
theorem combinatorial_isSteinPair_relaxed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n) (a : Fin n → Fin n → ℝ)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → {π : Equiv.Perm (Fin n) // π.IsSwap}}
    (hσ_meas : Measurable σ) (hτ_meas : Measurable τ)
    (h_indep : ProbabilityTheory.IndepFun σ τ P)
    (hσ_unif : P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
    (hτ_unif : P.map τ =
      (@PMF.uniformOfFintype {π : Equiv.Perm (Fin n) // π.IsSwap} inferInstance
        ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
          ⟨⟨0, by omega⟩, ⟨1, by omega⟩,
            Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩).toMeasure) :
    let W : Ω → ℝ :=
      fun ω ↦ (∑ i : Fin n, a i (σ ω i)) -
        (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    let W' : Ω → ℝ :=
      fun ω ↦
        (∑ i : Fin n, a i ((σ ω * (τ ω).1) i)) -
          (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    ∫ ω, W ω ∂P = 0 ∧
      IsExchangeablePair P W W' ∧
      P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        (fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω) ∧
      (3 ≤ n → IsSteinPair P (2 / ((n : ℝ) - 1)) W W') := by
  intro W W'
  have hW_def : W = fun ω ↦ combStat a (σ ω) := rfl
  have hW'_def : W' = fun ω ↦ combStat a (σ ω * (τ ω).1) := rfl
  rw [hW_def, hW'_def]
  have hn1 : 1 ≤ n := by omega
  have hMean : ∫ ω, combStat a (σ ω) ∂P = 0 := by
    have hmap : ∫ ω, combStat a (σ ω) ∂P =
        ∫ π, combStat a π ∂(P.map σ) :=
      (integral_map hσ_meas.aemeasurable
        (Measurable.of_discrete (f := combStat a)).aestronglyMeasurable).symm
    rw [hmap, hσ_unif, PMF.integral_eq_sum]
    simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, ← Finset.mul_sum, sum_combStat_eq_zero hn1 a, mul_zero]
  obtain ⟨hExch, hW_meas, hW2, _, hCond_W⟩ :=
    combinatorial_exchangeable_and_linear P hn a hσ_meas hτ_meas h_indep hσ_unif hτ_unif
  refine ⟨hMean, hExch, hCond_W, fun hn3 ↦ ?_⟩
  have hrn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have ha_pos : 0 < 2 / ((n : ℝ) - 1) := div_pos zero_lt_two (by linarith)
  have ha_le1 : 2 / ((n : ℝ) - 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  exact ⟨hExch, ha_pos, ha_le1, hW_meas, hW2.integrable one_le_two, hCond_W⟩

end SteinMethod
