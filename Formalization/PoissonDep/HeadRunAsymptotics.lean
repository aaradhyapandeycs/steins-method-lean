/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonDep.HeadRuns

/-!
# Head-Run Scaling Asymptotics and Gumbel Extreme-Value Limit
(`Formalization.PoissonDep.HeadRunAsymptotics`)

Covers Remark 4.2 (`\label{re101}`, `SteinIntro.tex:2031-2038`) and the qualified Gumbel longest-run
approximation in Section 4.2.1 (`SteinIntro.tex:2054-2061`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* **Remark 4.2** (`\label{re101}`, `SteinIntro.tex:2031-2038`; `stmts-review-05C` C1):
  `headRun_real_asymptotics` (real `k_n` scaling `λ_n → p^c` and `Θ(log n / n)` error),
  `headRun_int_asymptotics` (integer `k_n` with bounded offset `x_n`,
  `|λ_n - p^{x_n}| = O(log n / n)` and `(4.8)` error `O(log n / n)`), and combined
  `headRun_mean_and_error_asymptotics`.
* **Section 4.2.1 longest-run Gumbel approximation** (`SteinIntro.tex:2054-2061`):
  `longestRun_event_and_gumbel_approx`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Elementary `log n / n → 0` and exponential Lipschitz helpers -/

private lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsq : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 := Real.log_le_sub_one_of_pos hsq
  rw [Real.log_sqrt hx.le] at h1
  linarith

private lemma tendsto_sqrt_natCast_atTop :
    Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  let B : ℝ := max 0 b
  refine ⟨Nat.ceil (B ^ 2), fun n hn ↦ ?_⟩
  have hBn : B ^ 2 ≤ (n : ℝ) :=
    (Nat.le_ceil (B ^ 2)).trans (by exact_mod_cast hn)
  calc b
    _ ≤ B := le_max_right 0 b
    _ = Real.sqrt (B ^ 2) := (Real.sqrt_sq (le_max_left 0 b)).symm
    _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hBn

/-- Elementary limit `log n / n → 0` as `n → ∞`. -/
theorem tendsto_log_div_natCast_atTop :
    Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto (fun n : ℕ ↦ 2 / Real.sqrt (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_sqrt_natCast_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    calc Real.log (n : ℝ) / (n : ℝ)
      _ ≤ (2 * Real.sqrt (n : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right (log_le_two_mul_sqrt hn_pos) hn_pos.le
      _ = (2 * Real.sqrt (n : ℝ)) / (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by
        rw [Real.mul_self_sqrt hn_pos.le]
      _ = 2 / Real.sqrt (n : ℝ) := mul_div_mul_right 2 (Real.sqrt (n : ℝ)) hsq_pos.ne'

private lemma abs_exp_neg_sub_exp_neg_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.exp (-u) - Real.exp (-v)| ≤ |u - v| := by
  have aux : ∀ a b : ℝ, 0 ≤ a → a ≤ b → |Real.exp (-a) - Real.exp (-b)| ≤ b - a := by
    intro a b ha hab
    have hexp_le : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hexp_le)]
    have hfac : Real.exp (-a) - Real.exp (-b) = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      have hexp_eq : -a + -(b - a) = -b := by ring
      rw [hexp_eq]
    have hexpa1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h1sub : 1 - Real.exp (-(b - a)) ≤ b - a := by
      linarith [Real.add_one_le_exp (-(b - a))]
    have h1nn : 0 ≤ 1 - Real.exp (-(b - a)) := by
      have : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    calc Real.exp (-a) - Real.exp (-b)
      _ = Real.exp (-a) * (1 - Real.exp (-(b - a))) := hfac
      _ ≤ 1 * (b - a) := mul_le_mul hexpa1 h1sub h1nn zero_le_one
      _ = b - a := one_mul _
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm u v, abs_of_nonneg (sub_nonneg.mpr huv)]
    exact aux u v hu huv
  · rw [abs_sub_comm (Real.exp (-u)) (Real.exp (-v)), abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact aux v u hv hvu

/-! ### Shared offset asymptotic helper -/

private lemma headRun_offset_asymptotics {p M : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hM : 0 ≤ M)
    {x : ℕ → ℝ} (hx : ∀ᶠ n : ℕ in Filter.atTop, |x n| ≤ M) :
    let L : ℝ := Real.log (1 / p)
    let κ : ℕ → ℝ := fun n ↦ Real.log ((n : ℝ) * (1 - p)) / L + x n
    let lam : ℕ → ℝ := fun n ↦ p ^ (κ n) * (((n : ℝ) - κ n) * (1 - p) + 1)
    let err : ℕ → ℝ := fun n ↦
      lam n ^ 2 * ((2 * κ n + 1) / ((n : ℝ) - κ n + 1)) + 2 * lam n * p ^ (κ n)
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ κ n ∧ κ n ≤ (n : ℝ) / 2 ∧ 0 ≤ lam n ∧
        |lam n - p ^ (x n)| ≤ C₂ * (Real.log (n : ℝ) / (n : ℝ)) ∧
        C₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n ∧
        err n ≤ C₂ * (Real.log (n : ℝ) / (n : ℝ)) := by
  intro L κ lam err
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hL_pos : 0 < L := Real.log_pos (one_lt_one_div hp0 hp1)
  have hL_eq : L = -Real.log p := by
    dsimp only [L]
    rw [one_div, Real.log_inv]
  have hlogp_neg : Real.log p < 0 := Real.log_neg hp0 hp1
  set pMin : ℝ := p ^ M
  set pMax : ℝ := p ^ (-M)
  have hpMin_pos : 0 < pMin := Real.rpow_pos_of_pos hp0 M
  have hpMax_pos : 0 < pMax := Real.rpow_pos_of_pos hp0 (-M)
  let C_lam : ℝ := pMax * ((2 / L) * (1 - p) + 1) / (1 - p)
  have hC_lam_pos : 0 < C_lam := by positivity
  let C₁ : ℝ := ((1 / 2) * pMin) ^ 2 * ((1 / L) / 2)
  have hC₁_pos : 0 < C₁ := by positivity
  let C₂_err : ℝ := (pMax + 1) ^ 2 * (2 * (4 / L + 1)) +
    2 * (pMax + 1) * pMax / (1 - p)
  let C₂ : ℝ := max C_lam C₂_err
  have hC₂_pos : 0 < C₂ := lt_max_of_lt_left hC_lam_pos
  have hlog_atTop : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev_log_big : ∀ᶠ n : ℕ in Filter.atTop,
      max 1 (2 * (|Real.log (1 - p)| + L * (M + 1))) ≤ Real.log (n : ℝ) :=
    hlog_atTop.eventually_ge_atTop _
  have hev_ratio_small : ∀ᶠ n : ℕ in Filter.atTop,
      Real.log (n : ℝ) / (n : ℝ) ≤ min (L / 4) ((1 / 2) * pMin / C_lam) := by
    have hpos_eps : 0 < min (L / 4) ((1 / 2) * pMin / C_lam) := by positivity
    exact (tendsto_order.mp tendsto_log_div_natCast_atTop).2 _ hpos_eps |>.mono
      fun _ h ↦ h.le
  refine ⟨C₁, C₂, hC₁_pos, hC₂_pos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1, hx, hev_log_big, hev_ratio_small] with
    n hn1 hxn hlog_big hratio
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog_ge1 : 1 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hlog_big
  have hlog_ge2 : 2 * (|Real.log (1 - p)| + L * (M + 1)) ≤ Real.log (n : ℝ) :=
    (le_max_right _ _).trans hlog_big
  have hx_lo : -M ≤ x n := (abs_le.mp hxn).1
  have hx_hi : x n ≤ M := (abs_le.mp hxn).2
  have hpx_lo : pMin ≤ p ^ (x n) := by
    dsimp only [pMin]
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx_hi hlogp_neg.le)
  have hpx_hi : p ^ (x n) ≤ pMax := by
    dsimp only [pMax]
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx_lo hlogp_neg.le)
  have hpx_pos : 0 < p ^ (x n) := Real.rpow_pos_of_pos hp0 (x n)
  have hk0_decomp : Real.log ((n : ℝ) * (1 - p)) = Real.log (n : ℝ) + Real.log (1 - p) :=
    Real.log_mul hn_pos.ne' h1p.ne'
  have hκ_eq : κ n = (Real.log (n : ℝ) + Real.log (1 - p) + L * x n) / L := by
    dsimp only [κ]
    rw [hk0_decomp]
    field_simp
  have habs_shift : |Real.log (1 - p) + L * x n| ≤ |Real.log (1 - p)| + L * M := by
    calc |Real.log (1 - p) + L * x n|
      _ ≤ |Real.log (1 - p)| + |L * x n| := abs_add_le _ _
      _ = |Real.log (1 - p)| + L * |x n| := by rw [abs_mul, abs_of_pos hL_pos]
      _ ≤ |Real.log (1 - p)| + L * M := by gcongr
  have hκ_lo_log : (1 / (2 * L)) * Real.log (n : ℝ) ≤ κ n := by
    have hrew : (1 / (2 * L)) * Real.log (n : ℝ) = (Real.log (n : ℝ) / 2) / L := by
      field_simp
    rw [hrew, hκ_eq]
    refine div_le_div_of_nonneg_right ?_ hL_pos.le
    have hlo := (neg_abs_le (Real.log (1 - p) + L * x n)).trans'
      (neg_le_neg habs_shift)
    linarith
  have hκ_ge1 : 1 ≤ κ n := by
    rw [hκ_eq, le_div_iff₀ hL_pos, one_mul]
    have hlo := (neg_abs_le (Real.log (1 - p) + L * x n)).trans'
      (neg_le_neg habs_shift)
    linarith
  have hκ_hi_log : κ n ≤ (2 / L) * Real.log (n : ℝ) := by
    rw [hκ_eq, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL_pos]
    have hhi := (le_abs_self (Real.log (1 - p) + L * x n)).trans habs_shift
    linarith
  have hκ_le_half_n : κ n ≤ (n : ℝ) / 2 := by
    have hr1 : Real.log (n : ℝ) / (n : ℝ) ≤ L / 4 := (hratio.trans (min_le_left _ _))
    have hlog_le : Real.log (n : ℝ) ≤ (L / 4) * (n : ℝ) := (div_le_iff₀ hn_pos).mp hr1
    have hm := mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ 2 / L)
    have hsimp : (2 / L) * ((L / 4) * (n : ℝ)) = (n : ℝ) / 2 := by field_simp; norm_num
    linarith
  have hp_κ : p ^ (κ n) = p ^ (x n) / ((n : ℝ) * (1 - p)) := by
    dsimp only [κ]
    rw [Real.rpow_add hp0]
    have hp_k0 : p ^ (Real.log ((n : ℝ) * (1 - p)) / L) = ((n : ℝ) * (1 - p))⁻¹ := by
      rw [Real.rpow_def_of_pos hp0]
      have hexp : Real.log p * (Real.log ((n : ℝ) * (1 - p)) / L) =
          -Real.log ((n : ℝ) * (1 - p)) := by
        rw [hL_eq, div_neg, mul_neg, mul_div_cancel₀ _ hlogp_neg.ne]
      rw [hexp, Real.exp_neg, Real.exp_log (by positivity)]
    rw [hp_k0, div_eq_mul_inv, mul_comm]
  have hlam_diff_eq : lam n - p ^ (x n) =
      -(p ^ (x n) * ((κ n * (1 - p) - 1) / ((n : ℝ) * (1 - p)))) := by
    dsimp only [lam]
    rw [hp_κ]
    field_simp
    ring
  have hlam_diff_bound : |lam n - p ^ (x n)| ≤ C_lam * (Real.log (n : ℝ) / (n : ℝ)) := by
    rw [hlam_diff_eq, abs_neg, abs_mul, abs_of_pos hpx_pos, abs_div,
      abs_of_pos (mul_pos hn_pos h1p)]
    have hnum : |κ n * (1 - p) - 1| ≤ ((2 / L) * (1 - p) + 1) * Real.log (n : ℝ) := by
      have hκ_pos : 0 ≤ κ n * (1 - p) := mul_nonneg (by linarith) h1p.le
      calc |κ n * (1 - p) - 1|
        _ ≤ |κ n * (1 - p)| + |(-1 : ℝ)| := by
          simpa [sub_eq_add_neg] using abs_add_le (κ n * (1 - p)) (-1)
        _ = κ n * (1 - p) + 1 := by rw [abs_of_nonneg hκ_pos, abs_neg, abs_one]
        _ ≤ (2 / L) * Real.log (n : ℝ) * (1 - p) + 1 * Real.log (n : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_right hκ_hi_log h1p.le) (by linarith)
        _ = ((2 / L) * (1 - p) + 1) * Real.log (n : ℝ) := by ring
    calc p ^ (x n) * (|κ n * (1 - p) - 1| / ((n : ℝ) * (1 - p)))
      _ ≤ pMax * ((((2 / L) * (1 - p) + 1) * Real.log (n : ℝ)) / ((n : ℝ) * (1 - p))) := by
        refine mul_le_mul hpx_hi ?_ (by positivity) hpMax_pos.le
        exact div_le_div_of_nonneg_right hnum (by positivity)
      _ = C_lam * (Real.log (n : ℝ) / (n : ℝ)) := by
        dsimp only [C_lam]
        field_simp
  have hlam_diff_small : |lam n - p ^ (x n)| ≤ (1 / 2) * pMin := by
    have hr2 : Real.log (n : ℝ) / (n : ℝ) ≤ (1 / 2) * pMin / C_lam :=
      hratio.trans (min_le_right _ _)
    have hm := mul_le_mul_of_nonneg_left hr2 hC_lam_pos.le
    have hsimp : C_lam * ((1 / 2) * pMin / C_lam) = (1 / 2) * pMin :=
      mul_div_cancel₀ _ hC_lam_pos.ne'
    linarith
  have hlam_lo : (1 / 2) * pMin ≤ lam n := by
    have h1 := (abs_le.mp hlam_diff_small).1
    linarith
  have hlam_hi : lam n ≤ pMax + 1 := by
    have h1 := (abs_le.mp hlam_diff_small).2
    have hpMin_le1 : pMin ≤ 1 := Real.rpow_le_one hp0.le hp1.le hM
    linarith
  have hlam_nn : 0 ≤ lam n := by linarith
  have hdenom_lo : (n : ℝ) / 2 ≤ (n : ℝ) - κ n + 1 := by linarith
  have hdenom_hi : (n : ℝ) - κ n + 1 ≤ 2 * (n : ℝ) := by
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have herr_lo : C₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n := by
    have hterm2_nn : 0 ≤ 2 * lam n * p ^ (κ n) := by
      have hpκ_nn : 0 ≤ p ^ (κ n) := (Real.rpow_pos_of_pos hp0 (κ n)).le
      positivity
    have hnum_lo : (1 / L) * Real.log (n : ℝ) ≤ 2 * κ n + 1 := by
      have h2L : 2 * ((1 / (2 * L)) * Real.log (n : ℝ)) = (1 / L) * Real.log (n : ℝ) := by
        field_simp
      linarith [hκ_lo_log, h2L]
    have hquot_lo : ((1 / L) * Real.log (n : ℝ)) / (2 * (n : ℝ)) ≤
        (2 * κ n + 1) / ((n : ℝ) - κ n + 1) := by
      calc ((1 / L) * Real.log (n : ℝ)) / (2 * (n : ℝ))
        _ ≤ (2 * κ n + 1) / (2 * (n : ℝ)) :=
          div_le_div_of_nonneg_right hnum_lo (by positivity)
        _ ≤ (2 * κ n + 1) / ((n : ℝ) - κ n + 1) :=
          div_le_div_of_nonneg_left (by linarith) (by linarith) hdenom_hi
    have hsq_lo : ((1 / 2) * pMin) ^ 2 ≤ lam n ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlam_lo 2
    dsimp only [err, C₁]
    calc ((1 / 2) * pMin) ^ 2 * ((1 / L) / 2) * (Real.log (n : ℝ) / (n : ℝ))
      _ = ((1 / 2) * pMin) ^ 2 * (((1 / L) * Real.log (n : ℝ)) / (2 * (n : ℝ))) := by ring
      _ ≤ lam n ^ 2 * ((2 * κ n + 1) / ((n : ℝ) - κ n + 1)) :=
        mul_le_mul hsq_lo hquot_lo (by positivity) (sq_nonneg _)
      _ ≤ lam n ^ 2 * ((2 * κ n + 1) / ((n : ℝ) - κ n + 1)) + 2 * lam n * p ^ (κ n) :=
        le_add_of_nonneg_right hterm2_nn
  have herr_hi : err n ≤ C₂_err * (Real.log (n : ℝ) / (n : ℝ)) := by
    have hnum_hi : 2 * κ n + 1 ≤ (4 / L + 1) * Real.log (n : ℝ) := by
      have h4L : 2 * ((2 / L) * Real.log (n : ℝ)) + Real.log (n : ℝ) =
          (4 / L + 1) * Real.log (n : ℝ) := by ring
      linarith [hκ_hi_log, hlog_ge1, h4L]
    have hquot_hi : (2 * κ n + 1) / ((n : ℝ) - κ n + 1) ≤
        2 * (4 / L + 1) * (Real.log (n : ℝ) / (n : ℝ)) := by
      calc (2 * κ n + 1) / ((n : ℝ) - κ n + 1)
        _ ≤ ((4 / L + 1) * Real.log (n : ℝ)) / ((n : ℝ) - κ n + 1) :=
          div_le_div_of_nonneg_right hnum_hi (by linarith)
        _ ≤ ((4 / L + 1) * Real.log (n : ℝ)) / ((n : ℝ) / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom_lo
        _ = 2 * (4 / L + 1) * (Real.log (n : ℝ) / (n : ℝ)) := by field_simp
    have hsq_hi : lam n ^ 2 ≤ (pMax + 1) ^ 2 :=
      pow_le_pow_left₀ hlam_nn hlam_hi 2
    have ht1_hi : lam n ^ 2 * ((2 * κ n + 1) / ((n : ℝ) - κ n + 1)) ≤
        (pMax + 1) ^ 2 * (2 * (4 / L + 1)) * (Real.log (n : ℝ) / (n : ℝ)) := by
      calc lam n ^ 2 * ((2 * κ n + 1) / ((n : ℝ) - κ n + 1))
        _ ≤ (pMax + 1) ^ 2 * (2 * (4 / L + 1) * (Real.log (n : ℝ) / (n : ℝ))) :=
          mul_le_mul hsq_hi hquot_hi (div_nonneg (by linarith) (by linarith)) (by positivity)
        _ = (pMax + 1) ^ 2 * (2 * (4 / L + 1)) * (Real.log (n : ℝ) / (n : ℝ)) := by ring
    have ht2_hi : 2 * lam n * p ^ (κ n) ≤
        (2 * (pMax + 1) * pMax / (1 - p)) * (Real.log (n : ℝ) / (n : ℝ)) := by
      rw [hp_κ]
      calc 2 * lam n * (p ^ (x n) / ((n : ℝ) * (1 - p)))
        _ ≤ 2 * (pMax + 1) * (pMax / ((n : ℝ) * (1 - p))) := by
          refine mul_le_mul (by linarith) ?_ (by positivity) (by positivity)
          exact div_le_div_of_nonneg_right hpx_hi (by positivity)
        _ = (2 * (pMax + 1) * pMax / (1 - p)) * (1 / (n : ℝ)) := by field_simp
        _ ≤ (2 * (pMax + 1) * pMax / (1 - p)) * (Real.log (n : ℝ) / (n : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_right hlog_ge1 hn_pos.le
    dsimp only [err, C₂_err]
    linarith
  have hlog_div_nn : 0 ≤ Real.log (n : ℝ) / (n : ℝ) :=
    div_nonneg (by linarith) hn_pos.le
  refine ⟨hκ_ge1, hκ_le_half_n, hlam_nn, ?_, herr_lo, ?_⟩
  · exact hlam_diff_bound.trans
      (mul_le_mul_of_nonneg_right (le_max_left C_lam C₂_err) hlog_div_nn)
  · exact herr_hi.trans
      (mul_le_mul_of_nonneg_right (le_max_right C_lam C₂_err) hlog_div_nn)

/-! ### Remark 4.2 (`\label{re101}`, `stmts-review-05C` C1) -/

/-- **Remark 4.2** (real-`k` scaling, `\label{re101}`, `SteinIntro.tex:2031-2038`;
`stmts-review-05C` C1): treating $k_n = \frac{\log(n(1 - p))}{\log(1 / p)} + c$ as a real quantity
(matching *"Roughly"* at `SteinIntro.tex:2033`), $\lambda_n \to p^c$ and the `(4.8)` error bound is
of exact order $\Theta(\log(n) / n)$. -/
theorem headRun_real_asymptotics {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    let k : ℕ → ℝ := fun n ↦ Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + c
    let lam : ℕ → ℝ := fun n ↦ p ^ (k n) * (((n : ℝ) - k n) * (1 - p) + 1)
    let err : ℕ → ℝ := fun n ↦
      lam n ^ 2 * ((2 * k n + 1) / ((n : ℝ) - k n + 1)) + 2 * lam n * p ^ (k n)
    Filter.Tendsto lam Filter.atTop (nhds (p ^ c)) ∧
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        C₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n ∧
          err n ≤ C₂ * (Real.log (n : ℝ) / (n : ℝ)) := by
  intro k lam err
  obtain ⟨C₁, C₂, hC₁, hC₂, hev⟩ :=
    headRun_offset_asymptotics hp0 hp1 (abs_nonneg c)
      (x := fun _ ↦ c) (Eventually.of_forall fun _ ↦ le_rfl)
  refine ⟨?_, C₁, C₂, hC₁, hC₂, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hupper : Filter.Tendsto (fun n : ℕ ↦ C₂ * (Real.log (n : ℝ) / (n : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_log_div_natCast_atTop.const_mul C₂
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs]
    exact hn.2.2.2.1
  · filter_upwards [hev] with n hn
    exact ⟨hn.2.2.2.2.1, hn.2.2.2.2.2⟩

/-- **Remark 4.2** (integer-`k_n` scaling, `\label{re101}`, `SteinIntro.tex:2031-2038`, `2058-2061`;
`stmts-review-05C` C1): for integer thresholds `k : ℕ → ℕ` with bounded offset
`x_n = k_n - \log(n(1 - p)) / \log(1 / p)`, `λ_n - p^{x_n} → 0` at rate `O(log n / n)`,
`1 ≤ k_n ≤ n` eventually, and the `(4.8)` error bound evaluated at `k_n` is `O(log n / n)`. -/
theorem headRun_int_asymptotics {p M : ℝ} {k : ℕ → ℕ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hx_bdd : ∀ᶠ n : ℕ in Filter.atTop,
      |(k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)| ≤ M) :
    let x : ℕ → ℝ := fun n ↦ (k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)
    let lam : ℕ → ℝ := fun n ↦ p ^ (k n) * (((n : ℝ) - (k n : ℝ)) * (1 - p) + 1)
    let err : ℕ → ℝ := fun n ↦
      lam n ^ 2 * ((2 * (k n : ℝ) + 1) / ((n : ℝ) - (k n : ℝ) + 1)) +
        2 * lam n * p ^ (k n)
    Filter.Tendsto (fun n ↦ lam n - p ^ (x n)) Filter.atTop (nhds 0) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
        1 ≤ k n ∧ k n ≤ n ∧ 0 ≤ lam n ∧
          |lam n - p ^ (x n)| ≤ C * (Real.log (n : ℝ) / (n : ℝ)) ∧
          err n ≤ C * (Real.log (n : ℝ) / (n : ℝ)) := by
  intro x lam err
  have hx_bdd' : ∀ᶠ n : ℕ in Filter.atTop, |x n| ≤ max 0 M :=
    hx_bdd.mono fun n hn ↦ hn.trans (le_max_right 0 M)
  obtain ⟨_C₁, C₂, _hC₁, hC₂, hev⟩ :=
    headRun_offset_asymptotics hp0 hp1 (le_max_left 0 M) hx_bdd'
  have hκ_eq_k : ∀ n : ℕ,
      Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + x n = (k n : ℝ) := by
    intro n; dsimp only [x]; ring
  have hlam_eq : ∀ n : ℕ,
      p ^ (Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + x n) *
          (((n : ℝ) - (Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + x n)) *
            (1 - p) + 1) = lam n := by
    intro n
    rw [hκ_eq_k n, Real.rpow_natCast]
  have herr_eq : ∀ n : ℕ,
      (lam n) ^ 2 * ((2 * (Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + x n) + 1) /
          ((n : ℝ) - (Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + x n) + 1)) +
        2 * lam n * p ^ (Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + x n) = err n := by
    intro n
    rw [hκ_eq_k n, Real.rpow_natCast]
  have hev_int : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ k n ∧ k n ≤ n ∧ 0 ≤ lam n ∧
        |lam n - p ^ (x n)| ≤ C₂ * (Real.log (n : ℝ) / (n : ℝ)) ∧
        err n ≤ C₂ * (Real.log (n : ℝ) / (n : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1, hev] with n _hn1 hn
    obtain ⟨hκ1, hκhalf, hlam_nn, hdiff, _herr_lo, herr_hi⟩ := hn
    rw [hκ_eq_k n] at hκ1 hκhalf
    rw [hlam_eq n] at hlam_nn hdiff herr_hi
    rw [herr_eq n] at herr_hi
    have hk1 : 1 ≤ k n := by exact_mod_cast hκ1
    have hkn_r : (k n : ℝ) ≤ (n : ℝ) := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hkn : k n ≤ n := by exact_mod_cast hkn_r
    exact ⟨hk1, hkn, hlam_nn, hdiff, herr_hi⟩
  refine ⟨?_, C₂, hC₂, hev_int⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hupper : Filter.Tendsto (fun n : ℕ ↦ C₂ * (Real.log (n : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_log_div_natCast_atTop.const_mul C₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
  filter_upwards [hev_int] with n hn
  simpa only [sub_zero, Real.norm_eq_abs] using hn.2.2.2.1

/-- **Remark 4.2**, combined real-`k` and integer-`k_n` statement (`\label{re101}`,
`SteinIntro.tex:2031-2038`; `stmts-review-05C` C1).

*Reading note (`stmts-review-05C` C1)*: At `SteinIntro.tex:2033`, Ross treats
$k = \frac{\log(n(1 - p))}{\log(1 / p)} + c$ as a real expression (*"Roughly"*), giving
$\lambda_n \to p^c$ and $\Theta(\log(n) / n)$ error (first conjunct). Because Theorem 4.8 requires
an integer run-length threshold $k_n \in \mathbb{N}$ (where $\lambda_n$ oscillates along the
fractional part), the second conjunct gives the exact integer-$k_n$ version used in Section 4.2.1:
for bounded offsets $x_n = k_n - \frac{\log(n(1 - p))}{\log(1 / p)}$, $|\lambda_n - p^{x_n}|$ and
the `(4.8)` error bound are both $O(\log(n) / n)$, so $\lambda_n - p^{x_n} \to 0$. -/
theorem headRun_mean_and_error_asymptotics :
    (∀ {p c : ℝ},
        0 < p →
        p < 1 →
        let k : ℕ → ℝ := fun n ↦ Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + c
        let lam : ℕ → ℝ := fun n ↦ p ^ (k n) * (((n : ℝ) - k n) * (1 - p) + 1)
        let err : ℕ → ℝ := fun n ↦
          lam n ^ 2 * ((2 * k n + 1) / ((n : ℝ) - k n + 1)) + 2 * lam n * p ^ (k n)
        Filter.Tendsto lam Filter.atTop (nhds (p ^ c)) ∧
          ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
            C₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n ∧
              err n ≤ C₂ * (Real.log (n : ℝ) / (n : ℝ))) ∧
    (∀ {p M : ℝ} {k : ℕ → ℕ},
        0 < p →
        p < 1 →
        (∀ᶠ n : ℕ in Filter.atTop,
          |(k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)| ≤ M) →
        let x : ℕ → ℝ := fun n ↦ (k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)
        let lam : ℕ → ℝ := fun n ↦ p ^ (k n) * (((n : ℝ) - (k n : ℝ)) * (1 - p) + 1)
        let err : ℕ → ℝ := fun n ↦
          lam n ^ 2 * ((2 * (k n : ℝ) + 1) / ((n : ℝ) - (k n : ℝ) + 1)) +
            2 * lam n * p ^ (k n)
        Filter.Tendsto (fun n ↦ lam n - p ^ (x n)) Filter.atTop (nhds 0) ∧
          ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
            1 ≤ k n ∧ k n ≤ n ∧
              |lam n - p ^ (x n)| ≤ C * (Real.log (n : ℝ) / (n : ℝ)) ∧
              err n ≤ C * (Real.log (n : ℝ) / (n : ℝ))) := by
  refine ⟨fun hp0 hp1 ↦ headRun_real_asymptotics hp0 hp1, fun hp0 hp1 hx ↦ ?_⟩
  obtain ⟨htend, C, hC, hev⟩ := headRun_int_asymptotics hp0 hp1 hx
  exact ⟨htend, C, hC, hev.mono fun n hn ↦ ⟨hn.1, hn.2.1, hn.2.2.2.1, hn.2.2.2.2⟩⟩

/-! ### Section 4.2.1: Longest-Run Event Identity and Qualified Gumbel Approximation -/

/-- **Section 4.2.1 longest-head-run event identity and qualified Gumbel approximation**
(`SteinIntro.tex:2054-2061`): (1) `ℙ(W = 0) = ℙ(R_n < k)` for `1 ≤ k ≤ n`; (2) for integer
thresholds `k_n` with bounded offset `x_n = k_n - \log(n(1 - p)) / \log(1 / p)`,
`|ℙ(R_n - \log(n(1 - p)) / \log(1 / p) < x_n) - e^{-p^{x_n}}| ≤ C \log(n) / n` eventually. -/
theorem longestRun_event_and_gumbel_approx :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n k : ℕ} {Y : Fin n → Ω → ℕ},
        1 ≤ k →
        k ≤ n →
        (∀ i : Fin n, AEMeasurable (Y i) P) →
        (∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
        P.real {ω | headRunCount k (fun i ↦ Y i ω) = 0} =
          P.real {ω | longestQualityRun 1 (fun i ↦ Y i ω) < k}) ∧
    (∀ {p M : ℝ} {k : ℕ → ℕ},
        0 < p →
        p < 1 →
        (∀ᶠ n : ℕ in Filter.atTop,
          |(k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)| ≤ M) →
        ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
          ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            {Y : Fin n → Ω → ℕ},
            (∀ i : Fin n, AEMeasurable (Y i) P) →
            (∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
            ProbabilityTheory.iIndepFun Y P →
            (∀ i : Fin n, P.real {ω | Y i ω = 1} = p) →
            let x : ℝ := (k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)
            |P.real {ω |
                (longestQualityRun 1 (fun i ↦ Y i ω) : ℝ) -
                  Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) < x} -
              Real.exp (-(p ^ x))| ≤ C * (Real.log (n : ℝ) / (n : ℝ))) := by
  refine ⟨?_, ?_⟩
  · intro Ω _ P _ n k Y hk1 hkn hY hY01
    exact probReal_headRunCount_eq_zero_eq P hk1 hkn hY hY01
  intro p M k hp0 hp1 hx_bdd
  obtain ⟨_htend, C₀, _hC₀, hev⟩ := headRun_int_asymptotics hp0 hp1 hx_bdd
  refine ⟨2 * C₀, ?_⟩
  filter_upwards [hev] with n hn Ω _ P _ Y hY hY01 hIndep hYp
  obtain ⟨hk1, hkn, hlam_nn, hlam_diff, herr_hi⟩ := hn
  intro x
  let lam_n : ℝ := p ^ (k n) * (((n : ℝ) - (k n : ℝ)) * (1 - p) + 1)
  let r_n : ℝ≥0 := ⟨lam_n, hlam_nn⟩
  let W : Ω → ℕ := fun ω ↦ headRunCount (k n) (fun i ↦ Y i ω)
  have hevent_eq : {ω : Ω |
      (longestQualityRun 1 (fun i ↦ Y i ω) : ℝ) -
        Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) < x} =
      {ω : Ω | longestQualityRun 1 (fun i ↦ Y i ω) < k n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, x]
    constructor <;> intro h
    · have hlt : (longestQualityRun 1 (fun i ↦ Y i ω) : ℝ) < (k n : ℝ) := by linarith
      exact Nat.cast_lt.mp hlt
    · have hlt : (longestQualityRun 1 (fun i ↦ Y i ω) : ℝ) < (k n : ℝ) := Nat.cast_lt.mpr h
      linarith
  rw [hevent_eq, ← probReal_headRunCount_eq_zero_eq P hk1 hkn hY hY01]
  have hW_ae : AEMeasurable W P := by
    let tupY : Ω → (Fin n → ℕ) := fun ω i ↦ Y i ω
    have htup : AEMeasurable tupY P := .of_eval hY
    exact (Measurable.of_discrete : Measurable (headRunCount (k n))).comp_aemeasurable htup
  have : IsProbabilityMeasure (P.map W) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hW_ae .univ, Set.preimage_univ, measure_univ]⟩
  have htv_bound := (tvDist_headRunCount_le P (poissonLaw r_n) hk1 hkn hp0.le hp1.le
    hY hY01 hIndep hYp (r := r_n) (Z := id) rfl aemeasurable_id Measure.map_id).2
  rw [Measure.map_id] at htv_bound
  have h0_le_tv : ENNReal.ofReal |(P.map W).real {0} - (poissonLaw r_n).real {0}| ≤
      tvDist (P.map W) (poissonLaw r_n) := by
    rw [tvDist_eq_iSup]
    exact le_iSup₂_of_le ({0} : Set ℕ) .of_discrete le_rfl
  have hreal_tv : |P.real {ω | W ω = 0} - Real.exp (-lam_n)| ≤
      (r_n : ℝ) ^ 2 * ((2 * (k n : ℝ) + 1) / ((n : ℝ) - (k n : ℝ) + 1)) +
        2 * (r_n : ℝ) * p ^ (k n) := by
    have hle_enn := h0_le_tv.trans htv_bound
    have hrhs_nn : 0 ≤ (r_n : ℝ) ^ 2 * ((2 * (k n : ℝ) + 1) / ((n : ℝ) - (k n : ℝ) + 1)) +
        2 * (r_n : ℝ) * p ^ (k n) := by
      have hden_pos : 0 < (n : ℝ) - (k n : ℝ) + 1 := by
        have hkn_r : (k n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
        linarith
      positivity
    have hle_r := (ENNReal.ofReal_le_ofReal_iff hrhs_nn).mp hle_enn
    have hmap0 : (P.map W).real {0} = P.real {ω | W ω = 0} :=
      map_measureReal_apply_of_aemeasurable hW_ae .of_discrete
    have hpois0 : (poissonLaw r_n).real {0} = Real.exp (-lam_n) := by
      have h0 := ProbabilityTheory.poissonMeasure_real_singleton r_n 0
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] at h0
      exact h0
    rwa [hmap0, hpois0] at hle_r
  have hexp_diff : |Real.exp (-lam_n) - Real.exp (-(p ^ x))| ≤ |lam_n - p ^ x| :=
    abs_exp_neg_sub_exp_neg_le hlam_nn (Real.rpow_pos_of_pos hp0 x).le
  have htri := abs_sub_le (P.real {ω | W ω = 0}) (Real.exp (-lam_n)) (Real.exp (-(p ^ x)))
  have herr_rn : (r_n : ℝ) ^ 2 * ((2 * (k n : ℝ) + 1) / ((n : ℝ) - (k n : ℝ) + 1)) +
      2 * (r_n : ℝ) * p ^ (k n) ≤ C₀ * (Real.log (n : ℝ) / (n : ℝ)) := herr_hi
  linarith

end SteinMethod
