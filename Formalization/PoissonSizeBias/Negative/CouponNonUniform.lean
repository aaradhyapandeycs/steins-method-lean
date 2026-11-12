/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Negative.Occupancy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Non-Uniform Coupon Collecting (`Formalization.PoissonSizeBias.Negative.CouponNonUniform`)

Formalizes **Example 4.16** (`[Coupon collecting continued]`, `SteinIntro.tex:2566-2592`, citing
`[bhj92]` §6.2 and proved from scratch; `ISSUE-4.16`):

- `ex4_16_sizeBias`: explicit non-uniform ball-redistribution conditional coupling, monotonicity,
  and size-bias representation (`SteinIntro.tex:2581-2587`).
- `ex4_16_restricted`: under `1 ≤ k`, `0 < r`, and `(k : ℝ) ≠ Real.log (r : ℝ)` (guarding the
  interior-simplex zero denominator `k - log λ = 0` at `L2590`), the empty-box count $W$ has mean
  $\lambda = \sum_{i=1}^n (1 - p_i)^k$ and satisfies
  $$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
    \min\{1, \lambda\}\left[\max_i (1 - p_i)^k +
      \frac{k}{\lambda}\left(\frac{\lambda \log k}{k - \log \lambda} +
        \frac{4}{k}\right)^2\right].$$
- `ex4_16_exists_zero_denom`: proves on the interior of the probability simplex at $k = 2, n = 9$
  that there exist $p_1, \dots, p_9 > 0$ with $\sum_{i=1}^9 p_i = 1$ and
  $\lambda = \sum_{i=1}^9 (1 - p_i)^2 = e^2$, witnessing the $k - \log \lambda = 0$ singularity in
  `SteinIntro.tex:2590` (`ISSUE-4.16`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Part 1: Elementary Algebraic & Logarithmic Lemmas for BHJ §6.2 -/

/-- Total variation distance between any two probability measures is at most `1`. -/
lemma tvDist_le_one_of_prob {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  rw [tvDist_eq_iSup]
  refine iSup₂_le fun A _ ↦ ?_
  have hμ0 : 0 ≤ μ.real A := measureReal_nonneg
  have hμ1 : μ.real A ≤ 1 := measureReal_le_one
  have hν0 : 0 ≤ ν.real A := measureReal_nonneg
  have hν1 : ν.real A ≤ 1 := measureReal_le_one
  have habs : |μ.real A - ν.real A| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc ENNReal.ofReal |μ.real A - ν.real A|
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal habs
    _ = 1 := ENNReal.ofReal_one

/-- For `0 ≤ b ≤ a` and `k : ℕ`, `a ^ k - b ^ k ≤ k * (a - b) * a ^ (k - 1)`. -/
lemma pow_sub_pow_le_mul_sub {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    ∀ k : ℕ, a ^ k - b ^ k ≤ (k : ℝ) * (a - b) * a ^ (k - 1)
  | 0 => by simp
  | 1 => by simp
  | k + 2 => by
      have ha : 0 ≤ a := hb.trans hba
      have ih := pow_sub_pow_le_mul_sub hb hba (k + 1)
      simp only [Nat.add_sub_cancel] at ih ⊢
      have hdiff_nn : 0 ≤ a ^ (k + 1) - b ^ (k + 1) :=
        sub_nonneg.mpr (pow_le_pow_left₀ hb hba (k + 1))
      calc a ^ (k + 2) - b ^ (k + 2)
        _ = (a - b) * a ^ (k + 1) + b * (a ^ (k + 1) - b ^ (k + 1)) := by ring
        _ ≤ (a - b) * a ^ (k + 1) + a * (((k + 1 : ℕ) : ℝ) * (a - b) * a ^ k) :=
          add_le_add le_rfl (mul_le_mul hba ih hdiff_nn ha)
        _ = ((k + 2 : ℕ) : ℝ) * (a - b) * a ^ (k + 1) := by
          push_cast
          rw [pow_succ' a k]
          ring

/-- Rational enclosure `70 / 51 ≤ Real.log 4 ≤ 24 / 17` from `Real.log_le_sub_one_of_pos`. -/
lemma log_four_bounds : 70 / 51 ≤ Real.log 4 ∧ Real.log 4 ≤ 24 / 17 := by
  constructor
  · have h1 : Real.log (50 / 51 : ℝ) ≤ 50 / 51 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hinv : Real.log (50 / 51 : ℝ) = -Real.log (51 / 50 : ℝ) := by
      have heq : (50 / 51 : ℝ) = (51 / 50 : ℝ)⁻¹ := by norm_num
      rw [heq, Real.log_inv]
    have h2 : (1 / 51 : ℝ) ≤ Real.log (51 / 50 : ℝ) := by linarith
    have h3 : (70 / 51 : ℝ) ≤ Real.log ((51 / 50 : ℝ) ^ 70) := by
      rw [Real.log_pow]
      linarith
    have h4 : Real.log ((51 / 50 : ℝ) ^ 70) ≤ Real.log 4 :=
      Real.log_le_log (by positivity) (by norm_num)
    exact h3.trans h4
  · have h1 : Real.log (35 / 34 : ℝ) ≤ 35 / 34 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log ((35 / 34 : ℝ) ^ 48) ≤ 24 / 17 := by
      rw [Real.log_pow]
      linarith
    have h3 : Real.log 4 ≤ Real.log ((35 / 34 : ℝ) ^ 48) :=
      Real.log_le_log (by positivity) (by norm_num)
    exact h3.trans h2

/-- Derivative-free proof that
`x * log 4 + (5 * log 4 - 1) * log x - 3 * (log x)^2 - 2 * (log 4)^2`
is non-negative for all integers `k ≥ 5` (`x = (k : ℝ)`), via the fourth-root substitution
`u = √(√x)`. -/
lemma bhj_poly_nonneg {k : ℕ} (hk : 5 ≤ k) :
    0 ≤ (k : ℝ) * Real.log 4 + (5 * Real.log 4 - 1) * Real.log (k : ℝ) -
      3 * (Real.log (k : ℝ)) ^ 2 - 2 * (Real.log 4) ^ 2 := by
  set x : ℝ := (k : ℝ)
  have hx5 : (5 : ℝ) ≤ x := by
    change (5 : ℝ) ≤ (k : ℝ)
    exact_mod_cast hk
  have hx0 : 0 ≤ x := by linarith
  set l4 : ℝ := Real.log 4
  set lx : ℝ := Real.log x
  obtain ⟨hl4_lo, hl4_hi⟩ := log_four_bounds
  set u : ℝ := Real.sqrt (Real.sqrt x)
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
  have hu_pos : 0 < u := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hu2 : u ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have hu4 : u ^ 4 = x := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (Real.sqrt x) ^ 2 := by rw [hu2]
      _ = x := Real.sq_sqrt hx0
  have hu_ge : (7 / 5 : ℝ) ≤ u := by
    by_contra hlt
    push Not at hlt
    have h1 : u ^ 2 < (7 / 5 : ℝ) ^ 2 := by nlinarith
    have h2 : (u ^ 2) ^ 2 < ((7 / 5 : ℝ) ^ 2) ^ 2 := by nlinarith [sq_nonneg u]
    linarith
  have hlx_gt : l4 < lx := Real.log_lt_log (by positivity) (by linarith)
  have hlx_nn : 0 ≤ lx := by linarith
  have hl4_two : 2 * Real.log 2 = l4 := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    dsimp [l4]
    rw [h4, Real.log_pow]
    ring
  have hlx_ub : lx ≤ 2 * l4 + 2 * u - 4 := by
    have hlog_u4 : lx = 4 * Real.log u := by
      change Real.log x = 4 * Real.log u
      rw [← hu4, Real.log_pow]
      ring
    have hsplit : Real.log u = Real.log 2 + Real.log (u / 2) := by
      have heq : u = 2 * (u / 2) := by ring
      conv_lhs => rw [heq]
      exact Real.log_mul (by norm_num) (by positivity)
    have hub_div : Real.log (u / 2) ≤ u / 2 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hsq1 : lx ^ 2 ≤ (2 * l4 + 2 * u - 4) ^ 2 := by nlinarith
  have hsq2 : (2 * l4 + 2 * u - 4) ^ 2 ≤ (2 * (24 / 17 : ℝ) + 2 * u - 4) ^ 2 := by nlinarith
  have hlin_term : (5 * l4 - 1) * l4 ≤ (5 * l4 - 1) * lx := by nlinarith
  have hquad_l4 : 3 * (70 / 51 : ℝ) ^ 2 - (24 / 17 : ℝ) ≤ 3 * l4 ^ 2 - l4 := by nlinarith
  have hmain_lb : (70 / 51 : ℝ) * u ^ 4 + (3 * (70 / 51 : ℝ) ^ 2 - (24 / 17 : ℝ)) -
      3 * (2 * (24 / 17 : ℝ) + 2 * u - 4) ^ 2 ≤
      x * l4 + (5 * l4 - 1) * lx - 3 * lx ^ 2 - 2 * l4 ^ 2 := by
    rw [← hu4]
    nlinarith [pow_nonneg hu_nn 4]
  set v : ℝ := u - 7 / 5
  have hv_nn : 0 ≤ v := sub_nonneg.mpr hu_ge
  have huv : u = v + 7 / 5 := by ring
  have hquartic_pos :
      0 ≤ (70 / 51 : ℝ) * u ^ 4 + (3 * (70 / 51 : ℝ) ^ 2 - (24 / 17 : ℝ)) -
        3 * (2 * (24 / 17 : ℝ) + 2 * u - 4) ^ 2 := by
    rw [huv]
    have hv4 : 0 ≤ v ^ 4 := pow_nonneg hv_nn 4
    have hv3 : 0 ≤ v ^ 3 := pow_nonneg hv_nn 3
    have hvsq : 0 ≤ (v - 8 / 15) ^ 2 := sq_nonneg (v - 8 / 15)
    linarith
  exact hquartic_pos.trans hmain_lb

/-! ### Part 2: Core BHJ §6.2 Sum Inequality (`log λ < k`) -/

/-- Core threshold inequality for Example 4.16 (`SteinIntro.tex:2588-2590`, citing `[bhj92]` §6.2
and proved from scratch):
for `1 ≤ k`, simplex weights `p : Fin n → ℝ` (`0 ≤ p_i`, `∑ p_i = 1`), and
`lam = ∑ (1 - p_i)^k > 0` with `Real.log lam < k`,
`∑ p_i (1 - p_i)^{k - 1} ≤ lam * Real.log k / (k - Real.log lam) + 4 / k`. -/
lemma bhj_weighted_sum_le {n k : ℕ} {p : Fin n → ℝ}
    (hk1 : 1 ≤ k) (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1)
    (hlam_pos : 0 < ∑ i : Fin n, (1 - p i) ^ k)
    (hlog_lt : Real.log (∑ i : Fin n, (1 - p i) ^ k) < (k : ℝ)) :
    let lam : ℝ := ∑ i : Fin n, (1 - p i) ^ k
    (∑ i : Fin n, p i * (1 - p i) ^ (k - 1)) ≤
      lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ) := by
  classical
  intro lam
  have hp_le_one : ∀ i : Fin n, p i ≤ 1 := fun i ↦ by
    rw [← hp_sum]
    exact Finset.single_le_sum (fun j _ ↦ hp_nn j) (Finset.mem_univ i)
  have h1mp_nn : ∀ i : Fin n, 0 ≤ 1 - p i := fun i ↦ sub_nonneg.mpr (hp_le_one i)
  have h1mp_le : ∀ i : Fin n, 1 - p i ≤ 1 := fun i ↦ by linarith [hp_nn i]
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hlogk_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
  have hdenom_pos : 0 < (k : ℝ) - Real.log lam := sub_pos.mpr hlog_lt
  have hfirst_nn : 0 ≤ lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) :=
    div_nonneg (mul_nonneg hlam_pos.le hlogk_nn) hdenom_pos.le
  -- Case 1: `k ≤ 4`, where `∑ p_i (1 - p_i)^{k - 1} ≤ ∑ p_i = 1 ≤ 4 / k`
  by_cases hk4 : k ≤ 4
  · have hsum_le_one : (∑ i : Fin n, p i * (1 - p i) ^ (k - 1)) ≤ 1 := by
      calc ∑ i : Fin n, p i * (1 - p i) ^ (k - 1)
        _ ≤ ∑ i : Fin n, p i :=
          Finset.sum_le_sum fun i _ ↦
            mul_le_of_le_one_right (hp_nn i) (pow_le_one₀ (h1mp_nn i) (h1mp_le i))
        _ = 1 := hp_sum
    have hone_le_four : (1 : ℝ) ≤ 4 / (k : ℝ) := by
      rw [le_div_iff₀ hk_pos]
      have hk4_real : (k : ℝ) ≤ 4 := by exact_mod_cast hk4
      linarith
    linarith
  -- Now `5 ≤ k`
  push Not at hk4
  have hk5 : 5 ≤ k := hk4
  -- Case 2: `lam ≤ (4 / k)^2`, where every `(1 - p_i)^{k - 1} ≤ 4 / k`
  by_cases hlam_small : lam ≤ (4 / (k : ℝ)) ^ 2
  · have hterm_le : ∀ i : Fin n, (1 - p i) ^ (k - 1) ≤ 4 / (k : ℝ) := by
      intro i
      have hi_le_lam : (1 - p i) ^ k ≤ lam :=
        Finset.single_le_sum (fun j _ ↦ pow_nonneg (h1mp_nn j) k) (Finset.mem_univ i)
      have hi_le_sq : (1 - p i) ^ k ≤ (4 / (k : ℝ)) ^ 2 := hi_le_lam.trans hlam_small
      have hpow_k : ((1 - p i) ^ (k - 1)) ^ k ≤ (4 / (k : ℝ)) ^ k := by
        have hswap : ((1 - p i) ^ (k - 1)) ^ k = ((1 - p i) ^ k) ^ (k - 1) := by
          rw [← pow_mul, mul_comm, pow_mul]
        rw [hswap]
        have h1 : ((1 - p i) ^ k) ^ (k - 1) ≤ ((4 / (k : ℝ)) ^ 2) ^ (k - 1) :=
          pow_le_pow_left₀ (pow_nonneg (h1mp_nn i) k) hi_le_sq (k - 1)
        have h2 : ((4 / (k : ℝ)) ^ 2) ^ (k - 1) = (4 / (k : ℝ)) ^ (2 * (k - 1)) :=
          (pow_mul (4 / (k : ℝ)) 2 (k - 1)).symm
        have h4k_le1 : 4 / (k : ℝ) ≤ 1 := by
          rw [div_le_one hk_pos]
          have : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk5
          linarith
        have h3 : (4 / (k : ℝ)) ^ (2 * (k - 1)) ≤ (4 / (k : ℝ)) ^ k :=
          pow_le_pow_of_le_one (by positivity) h4k_le1 (by omega)
        exact h1.trans (h2 ▸ h3)
      exact le_of_pow_le_pow_left₀ (by omega : k ≠ 0) (by positivity) hpow_k
    have hsum_le : (∑ i : Fin n, p i * (1 - p i) ^ (k - 1)) ≤ 4 / (k : ℝ) := by
      calc ∑ i : Fin n, p i * (1 - p i) ^ (k - 1)
        _ ≤ ∑ i : Fin n, p i * (4 / (k : ℝ)) :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hterm_le i) (hp_nn i)
        _ = (∑ i : Fin n, p i) * (4 / (k : ℝ)) := (Finset.sum_mul _ _ _).symm
        _ = 4 / (k : ℝ) := by rw [hp_sum, one_mul]
    linarith
  -- Case 3: `5 ≤ k` and `(4 / k)^2 < lam < exp k`
  have hlam_small : (4 / (k : ℝ)) ^ 2 < lam := lt_of_not_ge hlam_small
  set α : ℝ := Real.log (k : ℝ) / ((k : ℝ) - Real.log lam)
  have hlarge_term : ∀ i : Fin n, α * (1 - p i) < p i → (1 - p i) ^ (k - 1) ≤ 4 / (k : ℝ) := by
    intro i hgt
    by_cases h1mp_zero : 1 - p i = 0
    · rw [h1mp_zero, zero_pow (by omega : k - 1 ≠ 0)]
      positivity
    have h1mp_pos : 0 < 1 - p i := lt_of_le_of_ne (h1mp_nn i) (Ne.symm h1mp_zero)
    have hlog_lam_gt : 2 * (Real.log 4 - Real.log (k : ℝ)) < Real.log lam := by
      have hlt := Real.log_lt_log (by positivity) hlam_small
      rw [Real.log_pow, Real.log_div (by norm_num) hk_pos.ne'] at hlt
      push_cast at hlt
      linarith
    set D₀ : ℝ := (k : ℝ) + 2 * Real.log (k : ℝ) - 2 * Real.log 4
    have hD_lt : (k : ℝ) - Real.log lam < D₀ := by linarith
    have hD₀_pos : 0 < D₀ := lt_trans hdenom_pos hD_lt
    have hlogk_pos : 0 < Real.log (k : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    set a₀ : ℝ := Real.log (k : ℝ) / D₀
    have ha₀_pos : 0 < a₀ := div_pos hlogk_pos hD₀_pos
    have ha₀_lt_α : a₀ < α := div_lt_div_of_pos_left hlogk_pos hdenom_pos hD_lt
    have hinv_gt : 1 + a₀ < (1 - p i)⁻¹ := by
      have hdiv_gt : α < p i / (1 - p i) := (lt_div_iff₀ h1mp_pos).mpr hgt
      have hsum_id : 1 + p i / (1 - p i) = (1 - p i)⁻¹ := by
        field_simp [h1mp_pos.ne']
        ring
      linarith
    have hlog_1pa₀ : a₀ / (1 + a₀) ≤ Real.log (1 + a₀) := by
      have hub := Real.log_le_sub_one_of_pos (inv_pos.mpr (by linarith : 0 < 1 + a₀))
      rw [Real.log_inv] at hub
      have hsimp : (1 + a₀)⁻¹ - 1 = -(a₀ / (1 + a₀)) := by
        field_simp [(by linarith : (1 + a₀) ≠ 0)]
        ring
      linarith
    have ha₀_ratio : a₀ / (1 + a₀) = Real.log (k : ℝ) / (D₀ + Real.log (k : ℝ)) := by
      dsimp [a₀]
      field_simp [hD₀_pos.ne', (by linarith : D₀ + Real.log (k : ℝ) ≠ 0)]
    have hk_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1]
      simp
    have hlog_pow_ge : Real.log ((k : ℝ) / 4) ≤ ((k - 1 : ℕ) : ℝ) * Real.log (1 + a₀) := by
      have hpoly := bhj_poly_nonneg hk5
      have hden2_pos : 0 < D₀ + Real.log (k : ℝ) := by linarith
      have hrat_ge : Real.log (k : ℝ) - Real.log 4 ≤
          ((k - 1 : ℕ) : ℝ) * (Real.log (k : ℝ) / (D₀ + Real.log (k : ℝ))) := by
        rw [hk_sub, mul_div_assoc', le_div_iff₀ hden2_pos]
        dsimp [D₀]
        linarith
      rw [Real.log_div hk_pos.ne' (by norm_num)]
      refine hrat_ge.trans ?_
      rw [← ha₀_ratio]
      exact mul_le_mul_of_nonneg_left hlog_1pa₀ (Nat.cast_nonneg _)
    have hpow_ge : (k : ℝ) / 4 ≤ (1 + a₀) ^ (k - 1) := by
      have hlog_le : Real.log ((k : ℝ) / 4) ≤ Real.log ((1 + a₀) ^ (k - 1)) := by
        rwa [Real.log_pow]
      exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_le
    have hpow_inv : (1 + a₀) ^ (k - 1) ≤ ((1 - p i)⁻¹) ^ (k - 1) :=
      pow_le_pow_left₀ (by positivity) hinv_gt.le (k - 1)
    have hk4_le_inv : (k : ℝ) / 4 ≤ ((1 - p i) ^ (k - 1))⁻¹ := by
      rw [← inv_pow]
      exact hpow_ge.trans hpow_inv
    have hpos_pow : 0 < (1 - p i) ^ (k - 1) := pow_pos h1mp_pos (k - 1)
    rw [le_inv_comm₀ (by positivity) hpos_pow] at hk4_le_inv
    simpa [inv_div] using hk4_le_inv
  -- Combine the two parts of `Fin n`
  calc ∑ i : Fin n, p i * (1 - p i) ^ (k - 1)
    _ ≤ ∑ i : Fin n,
          (if p i ≤ α * (1 - p i) then α * (1 - p i) ^ k else p i * (4 / (k : ℝ))) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        split_ifs with hle
        · calc p i * (1 - p i) ^ (k - 1)
            _ ≤ (α * (1 - p i)) * (1 - p i) ^ (k - 1) :=
              mul_le_mul_of_nonneg_right hle (pow_nonneg (h1mp_nn i) (k - 1))
            _ = α * ((1 - p i) * (1 - p i) ^ (k - 1)) := by ring
            _ = α * (1 - p i) ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk1]
        · exact mul_le_mul_of_nonneg_left (hlarge_term i (lt_of_not_ge hle)) (hp_nn i)
    _ ≤ (∑ i : Fin n, α * (1 - p i) ^ k) + ∑ i : Fin n, p i * (4 / (k : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ ↦ ?_
        split_ifs
        · exact le_add_of_nonneg_right (mul_nonneg (hp_nn i) (by positivity))
        · exact le_add_of_nonneg_left (mul_nonneg (div_nonneg hlogk_nn hdenom_pos.le)
            (pow_nonneg (h1mp_nn i) k))
    _ = α * lam + (∑ i : Fin n, p i) * (4 / (k : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ = lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ) := by
        rw [hp_sum, one_mul]
        dsimp [α]
        ring

/-! ### Part 3: Complementary Regime `k < log λ` (`RHS > 1`) -/

/-- When `1 ≤ k` and `(k : ℝ) < Real.log lam`, the printed right-hand side in Example 4.16 is at
least `1`, so it bounds `tvDist` trivially via `tvDist_le_one_of_prob`. -/
lemma bhj_rhs_ge_one_of_gt {n k : ℕ} (hn : 0 < n) {p : Fin n → ℝ}
    (hk1 : 1 ≤ k) (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1)
    (hlam_pos : 0 < ∑ i : Fin n, (1 - p i) ^ k)
    (hlog_gt : (k : ℝ) < Real.log (∑ i : Fin n, (1 - p i) ^ k)) :
    let lam : ℝ := ∑ i : Fin n, (1 - p i) ^ k
    1 ≤ min 1 lam *
      ((Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i : Fin n ↦ (1 - p i) ^ k) +
        (k : ℝ) / lam *
          (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2) := by
  intro lam
  have hlam_pos' : 0 < lam := hlam_pos
  have hlog_gt' : (k : ℝ) < Real.log lam := hlog_gt
  have hexp_lt : Real.exp (k : ℝ) < lam := by
    rw [← Real.exp_log hlam_pos']
    exact Real.exp_lt_exp.mpr hlog_gt'
  have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hexp1_ge : (1 : ℝ) < Real.exp (k : ℝ) := Real.one_lt_exp_iff.mpr (by positivity)
  have hlam_gt1 : 1 < lam := lt_trans hexp1_ge hexp_lt
  have hmin1 : min 1 lam = 1 := min_eq_left hlam_gt1.le
  rw [hmin1, one_mul]
  -- Subcase `k = 1`: `lam = n - 1`, `max_i (1 - p_i) ≥ 1 - 1 / n`, and `16 / (n - 1) > 1 / n`
  by_cases hk_eq1 : k = 1
  · subst hk_eq1
    have hlam_eq : lam = (n : ℝ) - 1 := by
      dsimp [lam]
      simp only [pow_one, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, hp_sum]
    have hn_gt2 : (2 : ℝ) < (n : ℝ) := by linarith
    -- By averaging, some `i₀` has `p i₀ ≤ 1 / n`
    have hex_min : ∃ i₀ : Fin n, p i₀ ≤ 1 / (n : ℝ) := by
      by_contra hall
      push Not at hall
      have hgt : 1 < ∑ i : Fin n, p i := by
        have hconst : (1 : ℝ) = ∑ _i : Fin n, (1 / (n : ℝ)) := by
          simp [hn.ne']
        rw [hconst]
        exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ ↦ hall i
      linarith [hp_sum]
    rcases hex_min with ⟨i₀, hi₀⟩
    have hsup_ge : 1 - 1 / (n : ℝ) ≤
        Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i : Fin n ↦ (1 - p i) ^ 1) := by
      have hle := Finset.le_sup' (f := fun i : Fin n ↦ (1 - p i) ^ 1) (Finset.mem_univ i₀)
      have h1 : 1 - 1 / (n : ℝ) ≤ (1 - p i₀) ^ 1 := by
        rw [pow_one]
        linarith
      exact h1.trans hle
    have hsecond_eq : ((1 : ℕ) : ℝ) / lam *
        (lam * Real.log ((1 : ℕ) : ℝ) / (((1 : ℕ) : ℝ) - Real.log lam) +
          4 / ((1 : ℕ) : ℝ)) ^ 2 = 16 / ((n : ℝ) - 1) := by
      simp only [Nat.cast_one, Real.log_one, mul_zero, zero_div, zero_add, div_one, one_div]
      rw [hlam_eq]
      ring
    rw [hsecond_eq]
    have hfrac : 1 / (n : ℝ) ≤ 16 / ((n : ℝ) - 1) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      linarith
    linarith
  -- Subcase `2 ≤ k`: the second term `(k / lam) * (...)^2` alone exceeds `1`
  have hk2 : 2 ≤ k := by omega
  have hsup_nn : 0 ≤
      Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i : Fin n ↦ (1 - p i) ^ k) := by
    have hle := Finset.le_sup' (f := fun i : Fin n ↦ (1 - p i) ^ k)
      (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    have hp0_le : p ⟨0, hn⟩ ≤ 1 := by
      rw [← hp_sum]
      exact Finset.single_le_sum (fun j _ ↦ hp_nn j) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    exact (pow_nonneg (sub_nonneg.mpr hp0_le) k).trans hle
  set u : ℝ := Real.log lam - (k : ℝ)
  have hu_pos : 0 < u := sub_pos.mpr hlog_gt'
  set s : ℝ := Real.sqrt lam
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hlam_pos'
  have hs_sq : s ^ 2 = lam := Real.sq_sqrt hlam_pos'.le
  have hs_exp : s = Real.exp ((k : ℝ) / 2) * Real.exp (u / 2) := by
    have hlam_exp : lam = Real.exp ((k : ℝ) + u) := by
      have hku : (k : ℝ) + u = Real.log lam := by
        dsimp [u]
        ring
      rw [hku, Real.exp_log hlam_pos']
    have hsq_eq : (Real.exp ((k : ℝ) / 2) * Real.exp (u / 2)) ^ 2 = lam := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, hlam_exp]
      congr 1
      ring
    dsimp [s]
    rw [← hsq_eq, Real.sqrt_sq (by positivity)]
  have hexp1_lb : (8 / 3 : ℝ) ≤ Real.exp 1 := by
    have htaylor := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at htaylor
    exact htaylor
  have hexpk2_lb : (8 / 3 : ℝ) ≤ Real.exp ((k : ℝ) / 2) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) / 2 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      linarith
    exact hexp1_lb.trans (Real.exp_le_exp.mpr h1)
  have hexpu2_lb : 1 + u / 2 + u ^ 2 / 8 ≤ Real.exp (u / 2) := by
    have htaylor := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ u / 2) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at htaylor
    linarith
  have hs_lb : (8 / 3 : ℝ) * (1 + u / 2 + u ^ 2 / 8) ≤ s := by
    rw [hs_exp]
    exact mul_le_mul hexpk2_lb hexpu2_lb (by positivity) (by positivity)
  have hlog2_lb : (2 / 3 : ℝ) ≤ Real.log (k : ℝ) := by
    have h4 := log_four_bounds.1
    have h4_eq : Real.log 4 = 2 * Real.log 2 := by
      have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, Real.log_pow]
      ring
    have hl2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith
    have hk_ge2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    exact hl2.trans (Real.log_le_log (by norm_num) hk_ge2)
  have h4ks_ub : 4 / ((k : ℝ) * s) ≤ 3 / 4 := by
    have hks_lb : (16 / 3 : ℝ) ≤ (k : ℝ) * s := by
      have hk_ge2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      have hs_ge : (8 / 3 : ℝ) ≤ s := by nlinarith [sq_nonneg u]
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hquad_pos : s < lam * Real.log (k : ℝ) / u - 4 / (k : ℝ) := by
    have hstep1 : 0 < s * Real.log (k : ℝ) - (4 / ((k : ℝ) * s) + 1) * u := by
      have hprod_lb : (8 / 3 : ℝ) * (1 + u / 2 + u ^ 2 / 8) * (2 / 3) ≤ s * Real.log (k : ℝ) :=
        mul_le_mul hs_lb hlog2_lb (by norm_num) hs_pos.le
      have hsub_ub : (4 / ((k : ℝ) * s) + 1) * u ≤ (3 / 4 + 1) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu_pos.le
      nlinarith [sq_nonneg (u - 7 / 4)]
    have hstep2 : 0 < s * (s * Real.log (k : ℝ) - (4 / ((k : ℝ) * s) + 1) * u) / u :=
      div_pos (mul_pos hs_pos hstep1) hu_pos
    have hident : s * (s * Real.log (k : ℝ) - (4 / ((k : ℝ) * s) + 1) * u) / u =
        lam * Real.log (k : ℝ) / u - 4 / (k : ℝ) - s := by
      have hk_ne : (k : ℝ) ≠ 0 := by positivity
      rw [← hs_sq]
      field_simp [hu_pos.ne', hk_ne, hs_pos.ne']
      ring
    linarith
  have hsq_gt_lam : lam ≤
      (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2 := by
    have hneg_eq : lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ) =
        -(lam * Real.log (k : ℝ) / u - 4 / (k : ℝ)) := by
      have hsub_neg : (k : ℝ) - Real.log lam = -u := by
        dsimp [u]
        ring
      rw [hsub_neg, div_neg]
      ring
    calc lam = s ^ 2 := hs_sq.symm
      _ ≤ (lam * Real.log (k : ℝ) / u - 4 / (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hs_pos.le hquad_pos.le 2
      _ = (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2 := by
        rw [hneg_eq, neg_sq]
  have hsecond_ge : 1 ≤ (k : ℝ) / lam *
      (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2 := by
    have hk_ge2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    calc (1 : ℝ) ≤ (k : ℝ) / lam * lam := by
          rw [div_mul_cancel₀ _ hlam_pos.ne']
          linarith
      _ ≤ (k : ℝ) / lam *
          (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq_gt_lam (div_nonneg (by positivity) hlam_pos.le)
  linarith

/-! ### Part 4: Size-Bias Coupling (`ex4_16_sizeBias`), Main Bound & Singularity Witness -/

/-- **Example 4.16, non-uniform redistribution size-bias coupling** (`[Coupon collecting
continued]`, `SteinIntro.tex:2581-2587`): for $k$ balls tossed independently into $n$ boxes with
probabilities $(p_1, \dots, p_n)$, redirecting each ball in box $i$ ($p_i < 1$) independently to
box $j \ne i$ with probability $p_j / (1 - p_i)$ yields $(X_j^{(i)})_{j \ne i}$ with the
conditional distribution of $(X_j)_{j \ne i}$ given $X_i = 1$, satisfies $X_j^{(i)} \le X_j$
pointwise, and with independent index $I$ (`ℙ(I = i) = (1 - p_i)^k / r`) gives a size-bias
representation $W^s = \sum_{j \ne I} X_j^{(I)} + 1$ of $W = \sum_{i=1}^n X_i$. -/
theorem ex4_16_sizeBias
    {n k : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n}
    {R : (i : Fin n) → Fin k → Ω → {j : Fin n // j ≠ i}}
    {I : Ω → Fin n} {r : ℝ≥0}
    (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1)
    (hB_meas : ∀ t : Fin k, Measurable (B t))
    (hB_indep : ProbabilityTheory.iIndepFun B P)
    (hB_prob : ∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i)
    (hR_meas : ∀ (i : Fin n) (t : Fin k), Measurable (R i t))
    (hR_indep : ∀ i : Fin n, p i < 1 → ProbabilityTheory.iIndepFun (R i) P)
    (hR_prob : ∀ i : Fin n, p i < 1 → ∀ t : Fin k, ∀ j : {j : Fin n // j ≠ i},
      P.real {ω | R i t ω = j} = p j.1 / (1 - p i))
    (hBR_indep : ∀ i : Fin n, p i < 1 →
      ProbabilityTheory.IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ R i t ω) P)
    (hI_meas : Measurable I)
    (hr_eq : (r : ℝ) = ∑ i : Fin n, (1 - p i) ^ k)
    (hI_prob : ∀ i : Fin n, P.real (I ⁻¹' {i}) = (1 - p i) ^ k / (r : ℝ))
    (hI_indep : ProbabilityTheory.IndepFun I
      (fun ω ↦ (fun t ↦ B t ω, fun i t ↦ R i t ω)) P) :
    let B' : (i : Fin n) → Fin k → Ω → Fin n :=
      fun i t ω ↦ if B t ω = i then (R i t ω).1 else B t ω
    let X : Fin n → Ω → ℕ := fun i ω ↦ if ∀ t : Fin k, B t ω ≠ i then 1 else 0
    let X' : (i : Fin n) → {j : Fin n // j ≠ i} → Ω → ℕ :=
      fun i j ω ↦ if ∀ t : Fin k, B' i t ω ≠ j.1 then 1 else 0
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω : ℝ)
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, (X' (I ω) j ω : ℝ)) + 1
    (∀ i : Fin n, p i < 1 →
      P.map (fun ω (j : {j : Fin n // j ≠ i}) ↦ X' i j ω) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i}, X' i j ω ≤ X j.1 ω) ∧
      IsSizeBias P W P Ws := by
  classical
  intro B' X X' W Ws
  let Bvec : Ω → (Fin k → Fin n) := fun ω t ↦ B t ω
  have hBv_meas : Measurable Bvec := Measurable.of_eval hB_meas
  let μB := ballBoxMeasure p hp_nn hp_sum k
  have hmap_B : P.map Bvec = μB :=
    map_pi_eq_ballBoxMeasure P hp_nn hp_sum hB_meas hB_indep hB_prob
  have hp_le_one : ∀ i : Fin n, p i ≤ 1 := fun i ↦ by
    rw [← hp_sum]
    exact Finset.single_le_sum (fun j _ ↦ hp_nn j) (Finset.mem_univ i)
  -- Conjunct 1: conditional law for every `i` with `p i < 1`
  have hcond_law : ∀ i : Fin n, p i < 1 →
      P.map (fun ω (j : {j : Fin n // j ≠ i}) ↦ X' i j ω) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) := by
    intro i hpi_lt
    have h1mp_pos : 0 < 1 - p i := sub_pos.mpr hpi_lt
    let Rvec : Ω → (Fin k → {j : Fin n // j ≠ i}) := fun ω t ↦ R i t ω
    have hRv_meas : Measurable Rvec := Measurable.of_eval (hR_meas i)
    let Jvec : Ω → (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i}) := fun ω ↦ (Bvec ω, Rvec ω)
    have hJv_meas : Measurable Jvec := hBv_meas.prodMk hRv_meas
    have hB_sing : ∀ b : Fin k → Fin n,
        P {ω | Bvec ω = b} = ENNReal.ofReal (∏ t : Fin k, p (b t)) := by
      intro b
      have hm : P {ω | Bvec ω = b} = μB {b} := by
        rw [← hmap_B, Measure.map_apply hBv_meas .of_discrete]
        rfl
      rw [hm, ballBoxMeasure_singleton, ballBoxWeight_eq_ofReal hp_nn]
      rfl
    have hR_sing : ∀ u : Fin k → {j : Fin n // j ≠ i},
        P {ω | Rvec ω = u} = ENNReal.ofReal (∏ t : Fin k, (p (u t).1 / (1 - p i))) := by
      intro u
      have hpre : {ω | Rvec ω = u} =
          ⋂ t ∈ (Finset.univ : Finset (Fin k)), R i t ⁻¹' {u t} := by
        ext ω
        simp [Rvec, funext_iff]
      rw [hpre, (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp
        (hR_indep i hpi_lt)) Finset.univ (fun _ _ ↦ .of_discrete)]
      have hprod : (∏ t : Fin k, P (R i t ⁻¹' {u t})) =
          ∏ t : Fin k, ENNReal.ofReal (p (u t).1 / (1 - p i)) := by
        refine Finset.prod_congr rfl fun t _ ↦ ?_
        rw [← ofReal_measureReal]
        congr 1
        exact hR_prob i hpi_lt t (u t)
      rw [hprod, ENNReal.ofReal_prod_of_nonneg fun t _ ↦ div_nonneg (hp_nn _) h1mp_pos.le]
    have hJ_sing : ∀ bu : (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i}),
        (P.map Jvec) {bu} =
          ENNReal.ofReal (∏ t : Fin k, (p (bu.1 t) * (p (bu.2 t).1 / (1 - p i)))) := by
      rintro ⟨b, u⟩
      rw [Measure.map_apply hJv_meas .of_discrete]
      have hpre : Jvec ⁻¹' {(b, u)} = Bvec ⁻¹' {b} ∩ Rvec ⁻¹' {u} := by
        ext ω
        simp [Jvec]
      rw [hpre, (hBR_indep i hpi_lt).measure_inter_preimage_eq_mul {b} {u}
        .of_discrete .of_discrete]
      change P {ω | Bvec ω = b} * P {ω | Rvec ω = u} = _
      rw [hB_sing b, hR_sing u,
        ← ENNReal.ofReal_mul (Finset.prod_nonneg fun t _ ↦ hp_nn (b t)),
        Finset.prod_mul_distrib]
    let redir : (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i}) → (Fin k → Fin n) :=
      fun bu t ↦ if bu.1 t = i then (bu.2 t).1 else bu.1 t
    let B'vec : Ω → (Fin k → Fin n) := fun ω t ↦ B' i t ω
    have hB'_comp : B'vec = redir ∘ Jvec := rfl
    have havoid_prob : μB.real {b | ∀ t : Fin k, b t ≠ i} = (1 - p i) ^ k :=
      ballBox_prob_avoid_one hp_nn hp_sum i
    have havoid_pos : 0 < μB.real {b | ∀ t : Fin k, b t ≠ i} := by
      rw [havoid_prob]
      exact pow_pos h1mp_pos k
    -- Sum of redirected target probabilities `∑_{j ≠ i} p_j / (1 - p_i) = 1`
    have hsum_sub_prob : (∑ j : {j : Fin n // j ≠ i}, p j.1 / (1 - p i)) = 1 := by
      rw [← Finset.sum_div]
      have hsub : (∑ j : {j : Fin n // j ≠ i}, p j.1) = ∑ x ∈ Finset.univ.erase i, p x :=
        (Finset.sum_subtype (Finset.univ.erase i) (by simp) p).symm
      have her : (∑ x ∈ Finset.univ.erase i, p x) = 1 - p i := by
        have h1 := Finset.add_sum_erase Finset.univ p (Finset.mem_univ i)
        linarith
      rw [hsub, her, div_self h1mp_pos.ne']
    have hmap_B'vec : P.map B'vec = ProbabilityTheory.cond μB {b | ∀ t : Fin k, b t ≠ i} := by
      have hcomp : P.map B'vec = (P.map Jvec).map redir := by
        rw [hB'_comp, Measure.map_map Measurable.of_discrete hJv_meas]
      rw [hcomp]
      refine measure_ext_of_singleton_fintype fun b₀ ↦ ?_
      rw [measure_map_singleton_fintype (P.map Jvec) redir b₀,
        ProbabilityTheory.cond_apply .of_discrete]
      by_cases hb₀ : ∀ t : Fin k, b₀ t ≠ i
      · have hinter : ({b | ∀ t : Fin k, b t ≠ i} ∩ {b₀}) = {b₀} := by
          ext b
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
          exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hb₀, h⟩⟩
        rw [hinter]
        simp_rw [hJ_sing]
        have hsum_ofReal :
            (∑ bu ∈ Finset.univ.filter (fun bu ↦ redir bu = b₀),
              ENNReal.ofReal (∏ t : Fin k, (p (bu.1 t) * (p (bu.2 t).1 / (1 - p i))))) =
            ENNReal.ofReal
              (∑ bu : (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i}),
                if redir bu = b₀ then
                  ∏ t : Fin k, (p (bu.1 t) * (p (bu.2 t).1 / (1 - p i)))
                else 0) := by
          rw [← Finset.sum_filter]
          exact (ENNReal.ofReal_sum_of_nonneg fun bu _ ↦
            Finset.prod_nonneg fun t _ ↦
              mul_nonneg (hp_nn _) (div_nonneg (hp_nn _) h1mp_pos.le)).symm
        rw [hsum_ofReal]
        -- Factor the sum over `(Fin k → Fin n) × (Fin k → {j // j ≠ i})` across `t : Fin k`
        let pairEquiv : ((Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i})) ≃
            (Fin k → Fin n × {j : Fin n // j ≠ i}) :=
          { toFun := fun bu t ↦ (bu.1 t, bu.2 t)
            invFun := fun f ↦ (fun t ↦ (f t).1, fun t ↦ (f t).2)
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
        have hfactor :
            (∑ bu : (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i}),
              if redir bu = b₀ then
                ∏ t : Fin k, (p (bu.1 t) * (p (bu.2 t).1 / (1 - p i)))
              else 0) =
            ∏ t : Fin k, (p (b₀ t) / (1 - p i)) := by
          rw [← Equiv.sum_comp pairEquiv.symm]
          have hprod_sum := (Fintype.prod_sum fun (t : Fin k)
            (xu : Fin n × {j : Fin n // j ≠ i}) ↦
            if (if xu.1 = i then xu.2.1 else xu.1) = b₀ t then
              p xu.1 * (p xu.2.1 / (1 - p i))
            else 0).symm
          have hmatch :
              (∑ f : Fin k → Fin n × {j : Fin n // j ≠ i},
                if redir (pairEquiv.symm f) = b₀ then
                  ∏ t : Fin k,
                    (p ((pairEquiv.symm f).1 t) * (p ((pairEquiv.symm f).2 t).1 / (1 - p i)))
                else 0) =
              ∑ f : Fin k → Fin n × {j : Fin n // j ≠ i},
                ∏ t : Fin k,
                  if (if (f t).1 = i then (f t).2.1 else (f t).1) = b₀ t then
                    p (f t).1 * (p (f t).2.1 / (1 - p i))
                  else 0 := by
            refine Finset.sum_congr rfl fun f _ ↦ ?_
            by_cases hf : redir (pairEquiv.symm f) = b₀
            · rw [ite_eq_left hf]
              refine Finset.prod_congr rfl fun t _ ↦ ?_
              have hft : (if (f t).1 = i then (f t).2.1 else (f t).1) = b₀ t := congrFun hf t
              rw [ite_eq_left hft]
              rfl
            · rw [ite_eq_right hf]
              have hex_t :
                  ∃ t₀ : Fin k, (if (f t₀).1 = i then (f t₀).2.1 else (f t₀).1) ≠ b₀ t₀ := by
                by_contra hall
                push Not at hall
                exact hf (funext hall)
              rcases hex_t with ⟨t₀, ht₀⟩
              exact (Finset.prod_eq_zero (Finset.mem_univ t₀) (ite_eq_right ht₀)).symm
          rw [hmatch, hprod_sum]
          refine Finset.prod_congr rfl fun t _ ↦ ?_
          rw [Fintype.sum_prod_type]
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
          have hi_term :
              (∑ u : {j : Fin n // j ≠ i},
                if (if i = i then u.1 else i) = b₀ t then p i * (p u.1 / (1 - p i)) else 0) =
              p i * (p (b₀ t) / (1 - p i)) := by
            rw [Finset.sum_eq_single ⟨b₀ t, hb₀ t⟩]
            · simp
            · intro u _ hu
              have hval : u.1 ≠ b₀ t := fun h ↦ hu (Subtype.ext h)
              simp [hval]
            · intro hnot
              exact False.elim (hnot (Finset.mem_univ _))
          have hrest_term :
              (∑ x ∈ Finset.univ.erase i, ∑ u : {j : Fin n // j ≠ i},
                if (if x = i then u.1 else x) = b₀ t then p x * (p u.1 / (1 - p i)) else 0) =
              p (b₀ t) := by
            have hb₀_mem : b₀ t ∈ Finset.univ.erase i :=
              Finset.mem_erase.mpr ⟨hb₀ t, Finset.mem_univ _⟩
            rw [← Finset.add_sum_erase (Finset.univ.erase i) _ hb₀_mem]
            have hhit :
                (∑ u : {j : Fin n // j ≠ i},
                  if (if b₀ t = i then u.1 else b₀ t) = b₀ t then
                    p (b₀ t) * (p u.1 / (1 - p i))
                  else 0) = p (b₀ t) := by
              simp only [hb₀ t, ↓reduceIte, ← Finset.mul_sum, hsum_sub_prob, mul_one]
            have hmiss : ∀ x ∈ (Finset.univ.erase i).erase (b₀ t),
                (∑ u : {j : Fin n // j ≠ i},
                  if (if x = i then u.1 else x) = b₀ t then
                    p x * (p u.1 / (1 - p i))
                  else 0) = 0 := by
              intro x hx
              have hxb : x ≠ b₀ t := (Finset.mem_erase.mp hx).1
              have hxi : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
              simp [hxi, hxb]
            rw [hhit, Finset.sum_eq_zero hmiss, add_zero]
          rw [hi_term, hrest_term]
          field_simp [h1mp_pos.ne']
          ring
        rw [hfactor]
        rw [← ofReal_measureReal (μ := μB) (s := {b₀}),
          ← ofReal_measureReal (μ := μB) (s := {b | ∀ t : Fin k, b t ≠ i}),
          havoid_prob, ballBoxMeasure_real_singleton,
          ← ENNReal.ofReal_inv_of_pos (havoid_prob ▸ havoid_pos),
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (havoid_prob ▸ havoid_pos.le))]
        congr 1
        unfold ballBoxRealWeight
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        ring
      · have hinter : ({b | ∀ t : Fin k, b t ≠ i} ∩ {b₀}) = ∅ := by
          ext b
          simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro h1 h2
          exact hb₀ (h2 ▸ h1)
        rw [hinter, measure_empty, mul_zero]
        have hempty_filt : (Finset.univ.filter fun bu ↦ redir bu = b₀) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro bu _ hbu
          push Not at hb₀
          rcases hb₀ with ⟨t, ht⟩
          have hbt := congrFun hbu t
          rw [ht] at hbt
          dsimp [redir] at hbt
          by_cases h1 : bu.1 t = i
          · rw [ite_eq_left h1] at hbt
            exact (bu.2 t).2 hbt
          · rw [ite_eq_right h1] at hbt
            exact h1 hbt
        rw [hempty_filt, Finset.sum_empty]
    -- Push forward from `Fin k → Fin n` to `{j // j ≠ i} → ℕ`
    let indRest : (Fin k → Fin n) → ({j : Fin n // j ≠ i} → ℕ) :=
      fun b j ↦ if ∀ t : Fin k, b t ≠ j.1 then 1 else 0
    have hlhs : P.map (fun ω (j : {j : Fin n // j ≠ i}) ↦ X' i j ω) =
        (P.map B'vec).map indRest := by
      have hB'v_m : Measurable B'vec := by
        rw [hB'_comp]
        exact Measurable.of_discrete.comp hJv_meas
      have hcomp : (fun ω (j : {j : Fin n // j ≠ i}) ↦ X' i j ω) = indRest ∘ B'vec := rfl
      rw [hcomp, Measure.map_map Measurable.of_discrete hB'v_m]
    have hrhs :
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) =
        (ProbabilityTheory.cond μB {b | ∀ t : Fin k, b t ≠ i}).map indRest := by
      have hset_pre : {ω | X i ω = 1} = Bvec ⁻¹' {b | ∀ t : Fin k, b t ≠ i} := by
        ext ω
        by_cases h : ∀ t : Fin k, B t ω ≠ i <;> simp [X, Bvec, h]
      rw [hset_pre]
      refine Measure.ext fun E hE ↦ ?_
      have hind_m : Measurable indRest := .of_discrete
      have hX_comp : (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) = indRest ∘ Bvec := rfl
      rw [hX_comp, Measure.map_apply (hind_m.comp hBv_meas) hE, Measure.map_apply hind_m hE,
        ProbabilityTheory.cond_apply (hBv_meas .of_discrete),
        ProbabilityTheory.cond_apply .of_discrete]
      have hm1 : P (Bvec ⁻¹' {b | ∀ t : Fin k, b t ≠ i}) = μB {b | ∀ t : Fin k, b t ≠ i} := by
        rw [← hmap_B, Measure.map_apply hBv_meas .of_discrete]
      have hm2 : P (Bvec ⁻¹' {b | ∀ t : Fin k, b t ≠ i} ∩ (indRest ∘ Bvec) ⁻¹' E) =
          μB ({b | ∀ t : Fin k, b t ≠ i} ∩ indRest ⁻¹' E) := by
        rw [Set.preimage_comp, ← Set.preimage_inter, ← hmap_B,
          Measure.map_apply hBv_meas .of_discrete]
      rw [hm1, hm2]
    rw [hlhs, hmap_B'vec, hrhs]
  -- Conjunct 2: pointwise monotonicity `X' i j ω ≤ X j.1 ω`
  have hmono : ∀ i : Fin n, ∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i}, X' i j ω ≤ X j.1 ω := by
    intro i ω j
    dsimp [X', X]
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      push Not at h2
      rcases h2 with ⟨t, ht⟩
      have hb' : B' i t ω = j.1 := by
        dsimp [B']
        rw [ht, ite_eq_right j.2]
      exact h1 t hb'
    · exact Nat.zero_le _
    · exact le_rfl
  -- Conjunct 3: `IsSizeBias P W P Ws` via `sizeBias_sum_of_nat_zero_one_fintype`
  have hSB : IsSizeBias P W P Ws := by
    have hr_pos : 0 < r := pos_of_index_prob P hI_meas hI_prob
    have hX_meas : ∀ i : Fin n, Measurable (X i) := fun i ↦ by
      have hcomp :
          X i = (fun b : Fin k → Fin n ↦ if ∀ t : Fin k, b t ≠ i then 1 else 0) ∘ Bvec := rfl
      rw [hcomp]
      exact Measurable.of_discrete.comp hBv_meas
    have hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1 :=
      fun i ↦ Eventually.of_forall fun ω ↦ by
        by_cases h : ∀ t : Fin k, B t ω ≠ i <;> simp [X, h]
    have hpX_eq : ∀ i : Fin n, P.real {ω | X i ω = 1} = (1 - p i) ^ k := by
      intro i
      have hset : {ω | X i ω = 1} = Bvec ⁻¹' {b | ∀ t : Fin k, b t ≠ i} := by
        ext ω
        by_cases h : ∀ t : Fin k, B t ω ≠ i <;> simp [X, Bvec, h]
      rw [hset, ← map_measureReal_apply hBv_meas .of_discrete, hmap_B]
      exact ballBox_prob_avoid_one hp_nn hp_sum i
    have hlam_pos : 0 < ∑ i : Fin n, P.real {ω | X i ω = 1} := by
      simp_rw [hpX_eq, ← hr_eq]
      exact NNReal.coe_pos.mpr hr_pos
    let Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℕ) := fun i ω j ↦ X' i j ω
    have hBR_all_meas : Measurable
        (fun ω : Ω ↦ (fun t : Fin k ↦ B t ω, fun (i : Fin n) (t : Fin k) ↦ R i t ω)) :=
      hBv_meas.prodMk (Measurable.of_eval fun i ↦ Measurable.of_eval (hR_meas i))
    let Φ_XY : (Fin k → Fin n) × ((i : Fin n) → Fin k → {j : Fin n // j ≠ i}) →
        (Fin n → ℕ) × ((i : Fin n) → {j : Fin n // j ≠ i} → ℕ) :=
      fun br ↦
        (fun i ↦ if ∀ t : Fin k, br.1 t ≠ i then 1 else 0,
         fun i j ↦ if ∀ t : Fin k,
           (if br.1 t = i then (br.2 i t).1 else br.1 t) ≠ j.1 then 1 else 0)
    have hY_meas : ∀ i : Fin n, AEMeasurable (Y i) P := fun i ↦ by
      have hcomp : Y i = (fun xy ↦ xy.2 i) ∘ Φ_XY ∘
          (fun ω ↦ (fun t ↦ B t ω, fun i' t ↦ R i' t ω)) := rfl
      rw [hcomp]
      exact (Measurable.of_discrete.comp (Measurable.of_discrete.comp hBR_all_meas)).aemeasurable
    have hY_law : ∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
        P.map (Y i) =
          (ProbabilityTheory.cond P {ω | X i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) := by
      intro i hi_pos
      by_cases hpi_lt : p i < 1
      · exact hcond_law i hpi_lt
      · -- When `p i = 1`, `(1 - p i)^k > 0` forces `k = 0`, where both vectors are const `1`
        have hpi_eq : p i = 1 := le_antisymm (hp_le_one i) (not_lt.mp hpi_lt)
        rw [hpX_eq i, hpi_eq, sub_self] at hi_pos
        have hk0 : k = 0 := by
          by_contra hkne
          rw [zero_pow hkne] at hi_pos
          exact lt_irrefl 0 hi_pos
        subst hk0
        have hY_const : Y i = fun _ _ ↦ 1 := by
          ext ω j
          simp [Y, X']
        have hX_const : (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) = fun _ _ ↦ 1 := by
          ext ω j
          simp [X]
        have hA_univ : {ω | X i ω = 1} = Set.univ := by
          ext ω
          simp [X]
        have : IsProbabilityMeasure (ProbabilityTheory.cond P {ω | X i ω = 1}) := by
          rw [hA_univ, ProbabilityTheory.cond_univ]
          infer_instance
        rw [hY_const, hX_const, Measure.map_const, Measure.map_const, measure_univ, measure_univ]
    have hI_prob' : ∀ i : Fin n,
        P.real (I ⁻¹' {i}) = P.real {ω | X i ω = 1} / ∑ m : Fin n, P.real {ω | X m ω = 1} := by
      intro i
      simp_rw [hpX_eq, ← hr_eq]
      exact hI_prob i
    have hXY_indep :
        ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P :=
      hI_indep.comp measurable_id (Measurable.of_discrete (f := Φ_XY))
    have hSB_nat := sizeBias_sum_of_nat_zero_one_fintype P hX_meas hX_zo hlam_pos hY_meas hY_law
      hI_meas hI_prob' hXY_indep
    have hW_eq : (fun ω ↦ ((∑ i : Fin n, X i ω : ℕ) : ℝ)) = W := by
      ext ω
      simp [W]
    have hWs_eq :
        (fun ω ↦ (((∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1 : ℕ) : ℝ)) = Ws := by
      ext ω
      simp [Ws, Y]
    rwa [hW_eq, hWs_eq] at hSB_nat
  exact ⟨hcond_law, hmono, hSB⟩

/-- **Example 4.16, restricted away from zero denominators** (`[Coupon collecting continued]`,
`SteinIntro.tex:2566-2592`, citing `[bhj92]` §6.2 and proved from scratch; `ISSUE-4.16`,
`review-05G4` item 1): for `1 ≤ k` balls placed independently into `n ≥ 1` boxes with probabilities
`(p_1, …, p_n)`, if `λ = ∑ (1 - p_i)^k > 0` and `(k : ℝ) ≠ Real.log λ`, then the printed bound
holds everywhere on this domain (both for `log λ < k` and for `k < log λ`). The printed bound is
true wherever defined; `k ≠ log λ` is an omitted domain guard, not a source error. -/
theorem ex4_16_restricted
    {n k : ℕ} (hn : 0 < n)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hk1 : 1 ≤ k)
    (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1)
    (hB_meas : ∀ t : Fin k, Measurable (B t))
    (hB_indep : ProbabilityTheory.iIndepFun B P)
    (hB_prob : ∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) :
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, if ∀ t : Fin k, B t ω ≠ i then 1 else 0
    let lam : ℝ := ∑ i : Fin n, (1 - p i) ^ k
    0 < r →
    (r : ℝ) = lam →
    (k : ℝ) ≠ Real.log (r : ℝ) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    ∫ ω, (W ω : ℝ) ∂P = lam ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 lam *
            ((Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i : Fin n ↦ (1 - p i) ^ k) +
              (k : ℝ) / lam *
                (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2)) := by
  intro W lam hr hr_lam hk_ne_log hZ_meas hZ_law
  let μ := ballBoxMeasure p hp_nn hp_sum k
  have hBM : Measurable (fun ω t ↦ B t ω) := Measurable.of_eval hB_meas
  have hmap_B : P.map (fun ω t ↦ B t ω) = μ :=
    map_pi_eq_ballBoxMeasure P hp_nn hp_sum hB_meas hB_indep hB_prob
  have hmean : ∫ ω, (W ω : ℝ) ∂P = lam := by
    let f_emp : (Fin k → Fin n) → ℝ := fun b ↦ (emptyBoxCount b : ℝ)
    have hcomp : ∀ ω, (W ω : ℝ) = f_emp (fun t ↦ B t ω) := fun _ ↦ rfl
    simp_rw [hcomp]
    rw [(integral_map hBM.aemeasurable
      (Measurable.of_discrete (f := f_emp)).aestronglyMeasurable).symm, hmap_B]
    exact ballBox_empty_mean hp_nn hp_sum
  refine ⟨hmean, ?_⟩
  have hlam_pos : 0 < lam := by
    rw [← hr_lam]
    exact NNReal.coe_pos.mpr hr
  have hk_ne_log_lam : (k : ℝ) ≠ Real.log lam := by rwa [← hr_lam]
  -- Split into `Real.log lam < k` (BHJ §6.2) vs `k < Real.log lam` (`RHS ≥ 1`)
  rcases lt_or_gt_of_ne hk_ne_log_lam.symm with hlog_lt | hlog_gt
  · -- Regime 1: `Real.log lam < k`
    let W₀ : Ω → ℕ := fun ω ↦
      ∑ i : Fin n, if ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card ≤ 0
        then 1 else 0
    have hW_eq : W = W₀ := by
      funext ω
      exact emptyBoxCount_eq_atMost_zero (fun t ↦ B t ω)
    have hr_int : (r : ℝ) = ∫ ω, (W₀ ω : ℝ) ∂P := by
      rw [← hW_eq, hmean, hr_lam]
    have htv_base := (rem4_17_atMost P P' hp_nn hp_sum hB_meas hB_indep hB_prob hr hr_int
      hZ_meas hZ_law).2
    change tvDist (P.map W₀) (P'.map Z) ≤ ENNReal.ofReal
      (min 1 (r : ℝ) * (1 - ProbabilityTheory.variance (fun ω ↦ (W₀ ω : ℝ)) P / (r : ℝ)))
      at htv_base
    rw [← hW_eq] at htv_base
    refine htv_base.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hr_lam]
    have hmin_nn : 0 ≤ min 1 lam := le_min zero_le_one hlam_pos.le
    refine mul_le_mul_of_nonneg_left ?_ hmin_nn
    -- Express `ProbabilityTheory.variance W P` via `ballBox_empty_variance`
    have hvar : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
        (∑ i : Fin n, ((1 - p i) ^ k - (1 - p i) ^ (2 * k))) +
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ((1 - p i - p j) ^ k - (1 - p i) ^ k * (1 - p j) ^ k) := by
      have hv := ProbabilityTheory.variance_map (μ := P)
        (X := fun b : Fin k → Fin n ↦ (emptyBoxCount b : ℝ)) (Y := fun ω t ↦ B t ω)
        Measurable.of_discrete.aemeasurable hBM.aemeasurable
      rw [hmap_B] at hv
      change ProbabilityTheory.variance ((fun b ↦ (emptyBoxCount b : ℝ)) ∘ (fun ω t ↦ B t ω)) P = _
      rw [← hv, ballBox_empty_variance]
    have h1_sub_var : 1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / lam =
        ((∑ i : Fin n, (1 - p i) ^ (2 * k)) +
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ((1 - p i) ^ k * (1 - p j) ^ k - (1 - p i - p j) ^ k)) / lam := by
      rw [hvar, one_sub_div hlam_pos.ne']
      congr 1
      have hdiag_split :
          (∑ i : Fin n, ((1 - p i) ^ k - (1 - p i) ^ (2 * k))) =
            lam - ∑ i : Fin n, (1 - p i) ^ (2 * k) := by
        rw [Finset.sum_sub_distrib]
      have hoff_neg :
          (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ((1 - p i - p j) ^ k - (1 - p i) ^ k * (1 - p j) ^ k)) =
          -(∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ((1 - p i) ^ k * (1 - p j) ^ k - (1 - p i - p j) ^ k)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        ring
      rw [hdiag_split, hoff_neg]
      ring
    rw [h1_sub_var, add_div]
    -- Bound first part `(∑ (1 - p_i)^{2k}) / lam ≤ sup_i (1 - p_i)^k`
    let M : ℝ := Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i : Fin n ↦ (1 - p i) ^ k
    have hp_le_one : ∀ i : Fin n, p i ≤ 1 := fun i ↦ by
      rw [← hp_sum]
      exact Finset.single_le_sum (fun j _ ↦ hp_nn j) (Finset.mem_univ i)
    have h1mp_nn : ∀ i : Fin n, 0 ≤ 1 - p i := fun i ↦ sub_nonneg.mpr (hp_le_one i)
    have hpart1 : (∑ i : Fin n, (1 - p i) ^ (2 * k)) / lam ≤ M := by
      rw [div_le_iff₀ hlam_pos]
      calc ∑ i : Fin n, (1 - p i) ^ (2 * k)
        _ = ∑ i : Fin n, (1 - p i) ^ k * (1 - p i) ^ k := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [two_mul, pow_add]
        _ ≤ ∑ i : Fin n, M * (1 - p i) ^ k := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            have hle_M : (1 - p i) ^ k ≤ M :=
              Finset.le_sup' (f := fun j : Fin n ↦ (1 - p j) ^ k) (Finset.mem_univ i)
            exact mul_le_mul_of_nonneg_right hle_M (pow_nonneg (h1mp_nn i) k)
        _ = M * lam := (Finset.mul_sum _ _ _).symm
    -- Bound second part via `pow_sub_pow_le_mul_sub` and `bhj_weighted_sum_le`
    let S : ℝ := ∑ i : Fin n, p i * (1 - p i) ^ (k - 1)
    have hS_nn : 0 ≤ S :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp_nn i) (pow_nonneg (h1mp_nn i) (k - 1))
    have hoff_le :
        (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ((1 - p i) ^ k * (1 - p j) ^ k - (1 - p i - p j) ^ k)) ≤ (k : ℝ) * S ^ 2 := by
      have hpair : ∀ (i : Fin n) (j : Fin n), j ≠ i →
          (1 - p i) ^ k * (1 - p j) ^ k - (1 - p i - p j) ^ k ≤
            (k : ℝ) * ((p i * (1 - p i) ^ (k - 1)) * (p j * (1 - p j) ^ (k - 1))) := by
        intro i j hij
        have hij_sum_le : p i + p j ≤ 1 := by
          rw [← hp_sum, ← Finset.sum_pair hij.symm]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ ↦ hp_nn x
        have hb_nn : 0 ≤ 1 - p i - p j := by linarith
        have hba : 1 - p i - p j ≤ (1 - p i) * (1 - p j) := by
          nlinarith [hp_nn i, hp_nn j]
        have hstep := pow_sub_pow_le_mul_sub hb_nn hba k
        rw [← mul_pow]
        refine hstep.trans (le_of_eq ?_)
        have hdiff : (1 - p i) * (1 - p j) - (1 - p i - p j) = p i * p j := by ring
        rw [hdiff, mul_pow]
        ring
      calc ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ((1 - p i) ^ k * (1 - p j) ^ k - (1 - p i - p j) ^ k)
        _ ≤ ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            (k : ℝ) * ((p i * (1 - p i) ^ (k - 1)) * (p j * (1 - p j) ^ (k - 1))) := by
            refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ ?_
            exact hpair i j (Finset.mem_erase.mp hj).1
        _ ≤ ∑ i : Fin n, ∑ j : Fin n,
            (k : ℝ) * ((p i * (1 - p i) ^ (k - 1)) * (p j * (1 - p j) ^ (k - 1))) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact Finset.sum_le_univ_sum_of_nonneg fun j ↦
              mul_nonneg (Nat.cast_nonneg k)
                (mul_nonneg (mul_nonneg (hp_nn i) (pow_nonneg (h1mp_nn i) (k - 1)))
                  (mul_nonneg (hp_nn j) (pow_nonneg (h1mp_nn j) (k - 1))))
        _ = (k : ℝ) * S ^ 2 := by
            dsimp [S]
            rw [sq, Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    have hS_ub := bhj_weighted_sum_le hk1 hp_nn hp_sum hlam_pos hlog_lt
    have hpart2 :
        (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ((1 - p i) ^ k * (1 - p j) ^ k - (1 - p i - p j) ^ k)) / lam ≤
        (k : ℝ) / lam *
          (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2 := by
      have hsq_le : S ^ 2 ≤
          (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hS_nn hS_ub 2
      calc (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            ((1 - p i) ^ k * (1 - p j) ^ k - (1 - p i - p j) ^ k)) / lam
        _ ≤ ((k : ℝ) * S ^ 2) / lam := div_le_div_of_nonneg_right hoff_le hlam_pos.le
        _ = (k : ℝ) / lam * S ^ 2 := mul_div_right_comm (k : ℝ) (S ^ 2) lam
        _ ≤ (k : ℝ) / lam *
            (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq_le (div_nonneg (Nat.cast_nonneg k) hlam_pos.le)
    exact add_le_add hpart1 hpart2
  · -- Regime 2: `k < Real.log lam` (`RHS ≥ 1 ≥ tvDist`)
    have hW_meas : Measurable W :=
      Finset.measurable_sum Finset.univ fun i _ ↦ by
        have hset : MeasurableSet {ω : Ω | ∀ t : Fin k, B t ω ≠ i} := by
          have heq : {ω : Ω | ∀ t : Fin k, B t ω ≠ i} =
              ⋂ t : Fin k, (B t ⁻¹' ({i}ᶜ : Set (Fin n))) := by
            ext ω
            simp
          rw [heq]
          exact MeasurableSet.iInter fun t ↦ hB_meas t .of_discrete
        exact Measurable.ite hset measurable_const measurable_const
    have : IsProbabilityMeasure (P.map W) :=
      (Measure.isProbabilityMeasure_map_iff hW_meas.aemeasurable).mpr ‹_›
    have : IsProbabilityMeasure (P'.map Z) :=
      (Measure.isProbabilityMeasure_map_iff hZ_meas).mpr ‹_›
    have htv1 : tvDist (P.map W) (P'.map Z) ≤ 1 := tvDist_le_one_of_prob (P.map W) (P'.map Z)
    have hrhs1 := bhj_rhs_ge_one_of_gt hn hk1 hp_nn hp_sum hlam_pos hlog_gt
    calc tvDist (P.map W) (P'.map Z)
      _ ≤ 1 := htv1
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal
          (min 1 lam *
            ((Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i : Fin n ↦ (1 - p i) ^ k) +
              (k : ℝ) / lam *
                (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2)) :=
        ENNReal.ofReal_le_ofReal hrhs1

/-- **Zero-Denominator Singularity Witness on the Interior of the Simplex** (`ISSUE-4.16`,
`SteinIntro.tex:2590`): at $k = 2$ and $n = 9$, there exist strictly positive box probabilities
$p_1, \dots, p_9 > 0$ with $\sum_{i=1}^9 p_i = 1$ such that
$\lambda = \sum_{i=1}^9 (1 - p_i)^2 = e^2 > 0$, hence $(k : \mathbb{R}) - \log \lambda = 0$. -/
theorem ex4_16_exists_zero_denom :
    ∃ p : Fin 9 → ℝ,
      (∀ i : Fin 9, 0 < p i) ∧
      ∑ i : Fin 9, p i = 1 ∧
      let lam : ℝ := ∑ i : Fin 9, (1 - p i) ^ 2
      0 < lam ∧ ((2 : ℕ) : ℝ) - Real.log lam = 0 := by
  let p_of : ℝ → Fin 9 → ℝ := fun t i ↦
    if i = 0 then (1 - t) / 9 + t else (1 - t) / 9
  let f : ℝ → ℝ := fun t ↦ (1 - ((1 - t) / 9 + t)) ^ 2 + 8 * (1 - (1 - t) / 9) ^ 2
  have hf_eq : ∀ t : ℝ, (∑ i : Fin 9, (1 - p_of t i) ^ 2) = f t := by
    intro t
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin 9))]
    have h0 : (1 - p_of t 0) ^ 2 = (1 - ((1 - t) / 9 + t)) ^ 2 := by simp [p_of]
    have hrest : ∀ i ∈ (Finset.univ : Finset (Fin 9)).erase 0,
        (1 - p_of t i) ^ 2 = (1 - (1 - t) / 9) ^ 2 := by
      intro i hi
      have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
      simp [p_of, hne]
    rw [h0, Finset.sum_congr rfl hrest, Finset.sum_const]
    have hcard : ((Finset.univ : Finset (Fin 9)).erase 0).card = 8 := by decide
    rw [hcard, nsmul_eq_mul]
    norm_num [f]
  have hf_cont : ContinuousOn f (Set.Icc 0 (15 / 16)) := by
    dsimp [f]
    fun_prop
  have hf0_lt : f 0 ≤ Real.exp 2 := by
    have hf0 : f 0 = 64 / 9 := by norm_num [f]
    have hexp1 : (65 / 24 : ℝ) ≤ Real.exp 1 := by
      have ht := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 5
      norm_num [Finset.sum_range_succ, Nat.factorial] at ht
      exact ht
    have hexp2 : (65 / 24 : ℝ) ^ 2 ≤ Real.exp 2 := by
      have hsq : Real.exp 2 = (Real.exp 1) ^ 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add, sq]
      rw [hsq]
      exact pow_le_pow_left₀ (by norm_num) hexp1 2
    rw [hf0]
    linarith
  have hf1_gt : Real.exp 2 ≤ f (15 / 16) := by
    have hf1 : f (15 / 16) = 2273 / 288 := by norm_num [f]
    have hexp_neg : (15 / 16 : ℝ) ≤ Real.exp (-1 / 16) := by
      have h := Real.add_one_le_exp (-1 / 16 : ℝ)
      linarith
    have hpow_neg : (15 / 16 : ℝ) ^ 32 ≤ Real.exp (-2) := by
      have h1 := pow_le_pow_left₀ (by norm_num) hexp_neg 32
      rw [← Real.exp_nat_mul, show (32 : ℕ) * (-1 / 16 : ℝ) = -2 by norm_num] at h1
      exact h1
    have hexp2_ub : Real.exp 2 ≤ (16 / 15 : ℝ) ^ 32 := by
      have hprod : Real.exp 2 * Real.exp (-2) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have hmul := mul_le_mul_of_nonneg_left hpow_neg (Real.exp_pos 2).le
      rw [hprod] at hmul
      have hmul2 := mul_le_mul_of_nonneg_right hmul (by positivity : (0 : ℝ) ≤ (16 / 15) ^ 32)
      have hcancel : Real.exp 2 * (15 / 16 : ℝ) ^ 32 * (16 / 15 : ℝ) ^ 32 = Real.exp 2 := by
        rw [mul_assoc, ← mul_pow]
        norm_num
      linarith
    rw [hf1]
    have hnum : (16 / 15 : ℝ) ^ 32 ≤ 2273 / 288 := by norm_num
    exact hexp2_ub.trans hnum
  have hmem : Real.exp 2 ∈ Set.Icc (f 0) (f (15 / 16)) := ⟨hf0_lt, hf1_gt⟩
  obtain ⟨t, ht_mem, hft⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 15 / 16) hf_cont hmem
  refine ⟨p_of t, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases ht_mem with ⟨ht0, ht1⟩
    dsimp [p_of]
    split_ifs <;> linarith
  · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : Fin 9))]
    have h0 : p_of t 0 = (1 - t) / 9 + t := by simp [p_of]
    have hrest : ∀ i ∈ (Finset.univ : Finset (Fin 9)).erase 0, p_of t i = (1 - t) / 9 := by
      intro i hi
      simp [p_of, (Finset.mem_erase.mp hi).1]
    have hcard : ((Finset.univ : Finset (Fin 9)).erase 0).card = 8 := by decide
    rw [h0, Finset.sum_congr rfl hrest, Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  · rw [hf_eq t, hft]
    exact Real.exp_pos 2
  · rw [hf_eq t, hft, Real.log_exp]
    norm_num

end SteinMethod
