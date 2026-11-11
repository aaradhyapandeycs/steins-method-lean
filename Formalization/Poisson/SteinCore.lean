/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonStein
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Poisson Stein Characterization and Stein Equation (`Formalization.Poisson.SteinCore`)

Core Chen–Stein theory for Poisson approximation from Section 4 of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:1816-1877`):

* **Lemma 4.1(1)** (`\label{lem101}`, `SteinIntro.tex:1823-1830`, `1861-1867`):
  `integral_poissonSteinOp_poissonLaw` and `integral_poissonSteinOp_eq_zero_of_map_eq`.
* **Lemma 4.1(2)** (`\label{lem101}`, `SteinIntro.tex:1823-1835`, `1868-1877`):
  `map_eq_poissonLaw_of_integral_poissonSteinOp_eq_zero`.
* **Lemma 4.2** (`\label{lem102}`, `SteinIntro.tex:1837-1848`, `1856-1860`):
  `poissonSteinSol_zero`, `poissonSteinOp_poissonSteinSol`, and
  `eq_poissonSteinSol_of_poissonSteinOp_eq`.
* **Corollary 4.3** (`\label{cor101}`, `SteinIntro.tex:1850-1855`):
  `abs_measureReal_sub_poissonLaw_eq`.
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-! ### Lemma 4.1: Characterizing Operator of the Poisson Distribution -/

private lemma poisson_weight_succ_mul (r : ℝ≥0) (k : ℕ) :
    (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) *
        ((k + 1 : ℕ) : ℝ) =
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ)) * (r : ℝ) := by
  have hb : (Nat.factorial (k + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k + 1))
  have hd : (Nat.factorial k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hb hd, pow_succ,
    Nat.factorial_succ, Nat.cast_mul]
  ring

/-- **Lemma 4.1(1)** (measure level, `\label{lem101}`, `SteinIntro.tex:1823-1830`, `1861-1867`):
for any bounded `f : ℕ → ℝ`, the Poisson Stein operator has expectation zero under
`poissonLaw r`. -/
theorem integral_poissonSteinOp_poissonLaw {r : ℝ≥0} (_hr : 0 < r)
    {f : ℕ → ℝ} (hf : ∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) :
    ∫ k, poissonSteinOp r f k ∂(poissonLaw r) = 0 := by
  obtain ⟨C, hC⟩ := hf
  have hf_shift : Integrable (fun k : ℕ ↦ f (k + 1)) (poissonLaw r) :=
    ⟨.of_discrete, .of_bounded (Filter.Eventually.of_forall fun k ↦ by
      rw [Real.norm_eq_abs]
      exact hC (k + 1))⟩
  have hg₁ : Integrable (fun k : ℕ ↦ (r : ℝ) * f (k + 1)) (poissonLaw r) :=
    hf_shift.const_mul (r : ℝ)
  have hg₁_sum : Summable (fun k : ℕ ↦
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ) *
        ‖(r : ℝ) * f (k + 1)‖) :=
    ProbabilityTheory.integrable_poissonMeasure_iff.mp hg₁
  let w : ℕ → ℝ := fun k ↦
    Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ) * ‖(k : ℝ) * f k‖
  have hw_succ : (fun k : ℕ ↦ w (k + 1)) =
      fun k : ℕ ↦ Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ) *
        ‖(r : ℝ) * f (k + 1)‖ := by
    ext k
    dsimp only [w]
    have hk_nn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg (k + 1)
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) := NNReal.coe_nonneg r
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hk_nn, Real.norm_of_nonneg hr_nn,
      ← mul_assoc, poisson_weight_succ_mul r k, mul_assoc]
  rw [← hw_succ] at hg₁_sum
  have hg₂ : Integrable (fun k : ℕ ↦ (k : ℝ) * f k) (poissonLaw r) :=
    ProbabilityTheory.integrable_poissonMeasure_iff.mpr
      ((summable_nat_add_iff 1).mp hg₁_sum)
  let v : ℕ → ℝ := fun k ↦
    (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ)) * ((k : ℝ) * f k)
  have h₁ : HasSum (fun k : ℕ ↦
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ)) *
        ((r : ℝ) * f (k + 1)))
      (∫ k, (r : ℝ) * f (k + 1) ∂(poissonLaw r)) :=
    ProbabilityTheory.hasSum_integral_poissonMeasure hg₁
  have h₂ : HasSum v (∫ k, (k : ℝ) * f k ∂(poissonLaw r)) :=
    ProbabilityTheory.hasSum_integral_poissonMeasure hg₂
  have hv_succ : (fun k : ℕ ↦ v (k + 1)) =
      fun k : ℕ ↦ (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ)) *
        ((r : ℝ) * f (k + 1)) := by
    ext k
    dsimp only [v]
    rw [← mul_assoc, poisson_weight_succ_mul r k, mul_assoc]
  rw [← hv_succ] at h₁
  have hv0 : v 0 = 0 := by
    simp only [v, Nat.cast_zero, zero_mul, mul_zero]
  have h₁' : HasSum v (∫ k, (r : ℝ) * f (k + 1) ∂(poissonLaw r)) := by
    have hz := h₁.zero_add
    rwa [hv0, zero_add] at hz
  have h_eq_int : ∫ k, (r : ℝ) * f (k + 1) ∂(poissonLaw r) =
      ∫ k, (k : ℝ) * f k ∂(poissonLaw r) :=
    h₁'.unique h₂
  simp_rw [poissonSteinOp]
  rw [integral_sub hg₁ hg₂, h_eq_int, sub_self]

/-- **Lemma 4.1(1)** (random-variable level, `\label{lem101}`, `SteinIntro.tex:1823-1830`):
if `Z` has distribution `poissonLaw r`, then `𝔼[𝒜f(Z)] = 0` for all bounded `f : ℕ → ℝ`. -/
theorem integral_poissonSteinOp_eq_zero_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {Z : Ω → ℕ} (hZ : AEMeasurable Z P)
    (hlaw : P.map Z = poissonLaw r)
    {f : ℕ → ℝ} (hf : ∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) :
    ∫ ω, poissonSteinOp r f (Z ω) ∂P = 0 := by
  rw [← integral_map hZ .of_discrete, hlaw]
  exact integral_poissonSteinOp_poissonLaw hr hf

/-- **Lemma 4.1(2)** (`\label{lem101}`, `SteinIntro.tex:1823-1835`, `1868-1877`):
if `W : Ω → ℕ` satisfies `𝔼[𝒜f(W)] = 0` for every bounded `f : ℕ → ℝ`, then `W` has
distribution `poissonLaw r` (requiring no moment assumptions on `W`). -/
theorem map_eq_poissonLaw_of_integral_poissonSteinOp_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hStein : ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, poissonSteinOp r f (W ω) ∂P = 0) :
    P.map W = poissonLaw r := by
  have _ := hr
  have h_rec : ∀ j : ℕ,
      (r : ℝ) * (P.map W).real {j} = ((j + 1 : ℕ) : ℝ) * (P.map W).real {j + 1} := by
    intro j
    have hf_bdd : ∃ C : ℝ, ∀ k : ℕ, |({j + 1} : Set ℕ).indicator (1 : ℕ → ℝ) k| ≤ C := by
      refine ⟨1, fun k ↦ ?_⟩
      by_cases hk : k ∈ ({j + 1} : Set ℕ)
      · rw [Set.indicator_of_mem hk, Pi.one_apply, abs_one]
      · rw [Set.indicator_of_notMem hk, abs_zero]
        exact zero_le_one
    have h_op : ∀ k : ℕ, poissonSteinOp r (({j + 1} : Set ℕ).indicator 1) k =
        ({j} : Set ℕ).indicator (fun _ : ℕ ↦ (r : ℝ)) k -
          ({j + 1} : Set ℕ).indicator (fun _ : ℕ ↦ ((j + 1 : ℕ) : ℝ)) k := by
      intro k
      simp only [poissonSteinOp]
      congr 1
      · by_cases hk : k = j
        · rw [hk, Set.indicator_of_mem (Set.mem_singleton (j + 1)),
            Set.indicator_of_mem (Set.mem_singleton j), Pi.one_apply, mul_one]
        · have hk1 : k + 1 ∉ ({j + 1} : Set ℕ) := by
            rw [Set.mem_singleton_iff]
            exact fun h ↦ hk (Nat.add_right_cancel h)
          have hk0 : k ∉ ({j} : Set ℕ) := by
            rw [Set.mem_singleton_iff]
            exact hk
          rw [Set.indicator_of_notMem hk1, Set.indicator_of_notMem hk0, mul_zero]
      · by_cases hk : k = j + 1
        · rw [hk, Set.indicator_of_mem (Set.mem_singleton (j + 1)),
            Set.indicator_of_mem (Set.mem_singleton (j + 1)), Pi.one_apply, mul_one]
        · have hk1 : k ∉ ({j + 1} : Set ℕ) := by
            rw [Set.mem_singleton_iff]
            exact hk
          rw [Set.indicator_of_notMem hk1, Set.indicator_of_notMem hk1, mul_zero]
    have h_int0 : ∫ k, poissonSteinOp r (({j + 1} : Set ℕ).indicator 1) k ∂(P.map W) = 0 := by
      rw [integral_map hW .of_discrete]
      exact hStein _ hf_bdd
    simp_rw [h_op] at h_int0
    rw [integral_sub ((integrable_const (r : ℝ)).indicator .of_discrete)
        ((integrable_const ((j + 1 : ℕ) : ℝ)).indicator .of_discrete),
      integral_indicator_const (r : ℝ) .of_discrete,
      integral_indicator_const ((j + 1 : ℕ) : ℝ) .of_discrete,
      smul_eq_mul, smul_eq_mul, mul_comm ((P.map W).real {j}),
      mul_comm ((P.map W).real {j + 1})] at h_int0
    exact sub_eq_zero.mp h_int0
  have h_fact : ∀ k : ℕ,
      (Nat.factorial k : ℝ) * (P.map W).real {k} = (P.map W).real {0} * (r : ℝ) ^ k := by
    intro k
    induction k with
    | zero =>
        rw [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, mul_one]
    | succ k ih =>
        calc
          (Nat.factorial (k + 1) : ℝ) * (P.map W).real {k + 1}
            = (Nat.factorial k : ℝ) * (((k + 1 : ℕ) : ℝ) * (P.map W).real {k + 1}) := by
                rw [Nat.factorial_succ, Nat.cast_mul]
                ring
          _ = (r : ℝ) * ((Nat.factorial k : ℝ) * (P.map W).real {k}) := by
                rw [← h_rec k]
                ring
          _ = (P.map W).real {0} * (r : ℝ) ^ (k + 1) := by
                rw [ih, pow_succ]
                ring
  have h_pmf_form : ∀ k : ℕ,
      (P.map W).real {k} = (P.map W).real {0} * (r : ℝ) ^ k / (Nat.factorial k : ℝ) := by
    intro k
    have hkf : (Nat.factorial k : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    rw [eq_div_iff hkf, mul_comm ((P.map W).real {k}), h_fact k]
  have h_tsum_one : ∑' k : ℕ, (P.map W).real {k} = 1 := by
    have h_cnt := integral_countable (integrable_const (μ := P.map W) (1 : ℝ))
    rw [integral_const, probReal_univ, one_smul] at h_cnt
    simpa only [smul_eq_mul, mul_one] using h_cnt.symm
  have h_sum : HasSum (fun k : ℕ ↦ (P.map W).real {k})
      (((P.map W).real {0} * Real.exp (r : ℝ)) * 1) := by
    have h_mul := (ProbabilityTheory.hasSum_one_poissonMeasure r).mul_left
      ((P.map W).real {0} * Real.exp (r : ℝ))
    have h_eq : (fun k : ℕ ↦ ((P.map W).real {0} * Real.exp (r : ℝ)) *
        (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ))) =
        fun k : ℕ ↦ (P.map W).real {k} := by
      ext k
      rw [h_pmf_form k, ← mul_div_assoc]
      congr 1
      calc
        ((P.map W).real {0} * Real.exp (r : ℝ)) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k)
          = (P.map W).real {0} * (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) * (r : ℝ) ^ k := by
              ring
        _ = (P.map W).real {0} * (r : ℝ) ^ k := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    rwa [h_eq] at h_mul
  have h_p0 : (P.map W).real {0} = Real.exp (-(r : ℝ)) := by
    have h_prod : (P.map W).real {0} * Real.exp (r : ℝ) = 1 := by
      have h_eq := h_sum.tsum_eq
      rw [h_tsum_one, mul_one] at h_eq
      exact h_eq.symm
    calc
      (P.map W).real {0}
        = ((P.map W).real {0} * Real.exp (r : ℝ)) * Real.exp (-(r : ℝ)) := by
            rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ = Real.exp (-(r : ℝ)) := by
            rw [h_prod, one_mul]
  refine Measure.ext_of_measureReal_singleton fun k ↦ ?_
  have h_pois : (poissonLaw r).real {k} =
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ) :=
    ProbabilityTheory.poissonMeasure_real_singleton r k
  rw [h_pmf_form k, h_p0, h_pois]

/-! ### Lemma 4.2: Solution of the Chen–Stein Equation -/

/-- **Lemma 4.2** (boundary condition, `\label{lem102}`, `SteinIntro.tex:1837-1848`):
the canonical Chen–Stein solution `poissonSteinSol r A` vanishes at `0`. -/
theorem poissonSteinSol_zero (r : ℝ≥0) (A : Set ℕ) : poissonSteinSol r A 0 = 0 :=
  rfl

private lemma natCast_mul_poissonSteinSol (r : ℝ≥0) (A : Set ℕ) (k : ℕ) :
    (k : ℝ) * poissonSteinSol r A k =
      ((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
        ((poissonLaw r).real (A ∩ Set.Iio k) -
          (poissonLaw r).real A * (poissonLaw r).real (Set.Iio k)) := by
  cases k with
  | zero =>
      have hIio0 : Set.Iio (0 : ℕ) = ∅ := by
        ext n
        simp only [Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
        exact Nat.not_lt_zero n
      rw [Nat.cast_zero, zero_mul, hIio0, Set.inter_empty, measureReal_empty, mul_zero,
        sub_self, mul_zero]
  | succ m =>
      simp only [poissonSteinSol, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      ring

private lemma mul_poissonSteinSol_succ {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) (k : ℕ) :
    (r : ℝ) * poissonSteinSol r A (k + 1) =
      ((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
        ((poissonLaw r).real (A ∩ Set.Iio (k + 1)) -
          (poissonLaw r).real A * (poissonLaw r).real (Set.Iio (k + 1))) := by
  have hr0 : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr.ne'
  have hrk : (r : ℝ) ^ k ≠ 0 := pow_ne_zero k hr0
  have hrk1 : (r : ℝ) ^ (k + 1) ≠ 0 := pow_ne_zero (k + 1) hr0
  have h_pow : (r : ℝ) * ((r : ℝ) ^ (k + 1))⁻¹ = ((r : ℝ) ^ k)⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul₀ hrk1, pow_succ, ← mul_assoc, inv_mul_cancel₀ hrk, one_mul]
  simp only [poissonSteinSol]
  calc
    (r : ℝ) * (((r : ℝ) ^ (k + 1))⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
        ((poissonLaw r).real (A ∩ Set.Iio (k + 1)) -
          (poissonLaw r).real A * (poissonLaw r).real (Set.Iio (k + 1))))
      = ((r : ℝ) * ((r : ℝ) ^ (k + 1))⁻¹) * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
          ((poissonLaw r).real (A ∩ Set.Iio (k + 1)) -
            (poissonLaw r).real A * (poissonLaw r).real (Set.Iio (k + 1))) := by ring
    _ = ((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
          ((poissonLaw r).real (A ∩ Set.Iio (k + 1)) -
            (poissonLaw r).real A * (poissonLaw r).real (Set.Iio (k + 1))) := by rw [h_pow]

private lemma poissonLaw_Iio_diff (r : ℝ≥0) (A : Set ℕ) (k : ℕ) :
    ((poissonLaw r).real (A ∩ Set.Iio (k + 1)) -
        (poissonLaw r).real A * (poissonLaw r).real (Set.Iio (k + 1))) -
      ((poissonLaw r).real (A ∩ Set.Iio k) -
        (poissonLaw r).real A * (poissonLaw r).real (Set.Iio k)) =
      (A.indicator 1 k - (poissonLaw r).real A) * (poissonLaw r).real {k} := by
  have hIio : Set.Iio (k + 1) = Set.Iio k ∪ {k} := by
    ext n
    simp only [Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff]
    omega
  have hdisj : Disjoint (Set.Iio k) {k} := Set.disjoint_singleton_right.mpr (lt_irrefl k)
  have hU : (poissonLaw r).real (Set.Iio (k + 1)) =
      (poissonLaw r).real (Set.Iio k) + (poissonLaw r).real {k} := by
    rw [hIio, measureReal_union hdisj .of_discrete (measure_ne_top _ _) (measure_ne_top _ _)]
  have hdisjA : Disjoint (A ∩ Set.Iio k) (A ∩ {k}) :=
    hdisj.mono Set.inter_subset_right Set.inter_subset_right
  have hAU : (poissonLaw r).real (A ∩ Set.Iio (k + 1)) =
      (poissonLaw r).real (A ∩ Set.Iio k) +
        A.indicator (1 : ℕ → ℝ) k * (poissonLaw r).real {k} := by
    rw [hIio, Set.inter_union_distrib_left,
      measureReal_union hdisjA .of_discrete (measure_ne_top _ _) (measure_ne_top _ _)]
    congr 1
    by_cases hk : k ∈ A
    · have hAk : A ∩ {k} = {k} := by
        ext n
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        exact ⟨And.right, fun h ↦ ⟨h ▸ hk, h⟩⟩
      rw [hAk, Set.indicator_of_mem hk, Pi.one_apply, one_mul]
    · have hAk : A ∩ {k} = ∅ := by
        ext n
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun ⟨hn, hnk⟩ ↦ hk (hnk ▸ hn)
      rw [hAk, measureReal_empty, Set.indicator_of_notMem hk, zero_mul]
  rw [hAU, hU]
  ring

private lemma poisson_inv_weight_mul {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    ((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
      (poissonLaw r).real {k} = 1 := by
  have hrk : (r : ℝ) ^ k ≠ 0 := pow_ne_zero k (NNReal.coe_ne_zero.mpr hr.ne')
  have hkf : (Nat.factorial k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h_pois : (poissonLaw r).real {k} =
      Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (Nat.factorial k : ℝ) :=
    ProbabilityTheory.poissonMeasure_real_singleton r k
  rw [h_pois, mul_assoc (((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ)), mul_div_cancel₀ _ hkf]
  calc
    (((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ)) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k)
      = (((r : ℝ) ^ k)⁻¹ * (r : ℝ) ^ k) * (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) := by ring
    _ = 1 := by
        rw [inv_mul_cancel₀ hrk, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- **Lemma 4.2** (Stein equation, `\label{lem102}`, eq. `(4.1)` `\label{101}`,
`SteinIntro.tex:1837-1848`, `1856-1860`):
`poissonSteinSol r A` solves `r f_A(k + 1) - k f_A(k) = 𝕀[k ∈ A] - Po(r)(A)`. -/
theorem poissonSteinOp_poissonSteinSol {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) (k : ℕ) :
    poissonSteinOp r (poissonSteinSol r A) k = A.indicator 1 k - (poissonLaw r).real A := by
  rw [poissonSteinOp, mul_poissonSteinSol_succ hr A k, natCast_mul_poissonSteinSol r A k,
    ← mul_sub, poissonLaw_Iio_diff r A k]
  calc
    ((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
        ((A.indicator 1 k - (poissonLaw r).real A) * (poissonLaw r).real {k})
      = (((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
          (poissonLaw r).real {k}) * (A.indicator 1 k - (poissonLaw r).real A) := by ring
    _ = A.indicator 1 k - (poissonLaw r).real A := by
        rw [poisson_inv_weight_mul hr k, one_mul]

/-- **Lemma 4.2** (uniqueness, `\label{lem102}`, `SteinIntro.tex:1837-1848`, `1856-1860`):
`poissonSteinSol r A` is the unique solution of the Chen–Stein equation `(4.1)` vanishing at `0`. -/
theorem eq_poissonSteinSol_of_poissonSteinOp_eq {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) {g : ℕ → ℝ}
    (hg0 : g 0 = 0)
    (hg : ∀ k : ℕ, poissonSteinOp r g k = A.indicator 1 k - (poissonLaw r).real A) :
    g = poissonSteinSol r A := by
  ext k
  induction k with
  | zero =>
      rw [hg0, poissonSteinSol_zero]
  | succ k ih =>
      have hr0 : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr.ne'
      have h_eq : poissonSteinOp r g k = poissonSteinOp r (poissonSteinSol r A) k := by
        rw [hg k, poissonSteinOp_poissonSteinSol hr A k]
      simp only [poissonSteinOp, ih] at h_eq
      have h_mul : (r : ℝ) * g (k + 1) = (r : ℝ) * poissonSteinSol r A (k + 1) := by
        simpa only [sub_add_cancel] using
          congrArg (· + (k : ℝ) * poissonSteinSol r A k) h_eq
      exact mul_left_cancel₀ hr0 h_mul

/-! ### Corollary 4.3: Stein Identity for Set Probabilities -/

/-- **Corollary 4.3** (`\label{cor101}`, `SteinIntro.tex:1850-1855`):
for any `ℕ`-valued random variable `W`, `|ℙ(W ∈ A) - Po(r)(A)| = |𝔼[r f_A(W + 1) - W f_A(W)]|`. -/
theorem abs_measureReal_sub_poissonLaw_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W : Ω → ℕ} (hW : AEMeasurable W P) (A : Set ℕ) :
    |P.real {ω | W ω ∈ A} - (poissonLaw r).real A| =
      |∫ ω, ((r : ℝ) * poissonSteinSol r A (W ω + 1) -
        (W ω : ℝ) * poissonSteinSol r A (W ω)) ∂P| := by
  have h_int : ∫ ω, poissonSteinOp r (poissonSteinSol r A) (W ω) ∂P =
      P.real {ω | W ω ∈ A} - (poissonLaw r).real A := by
    rw [← integral_map hW .of_discrete]
    simp_rw [poissonSteinOp_poissonSteinSol hr A]
    have hA_int : Integrable (A.indicator (1 : ℕ → ℝ)) (P.map W) :=
      (integrable_const (1 : ℝ)).indicator .of_discrete
    rw [integral_sub hA_int (integrable_const _),
      integral_indicator_one .of_discrete, integral_const, probReal_univ, one_smul,
      map_measureReal_apply_of_aemeasurable hW .of_discrete]
    rfl
  exact congrArg abs h_int.symm

end SteinMethod
