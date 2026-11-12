/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Leftovers.TrianglesEfronStein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Kolmogorov Normal Approximation for Triangle Counts (`Formalization.Leftovers.TrianglesKolm`)

Resolves Backlog Item 4 (`SteinIntro.tex:935-941`; `ISSUE-TYPO-3.2.1`, `ISSUE-3.2.1`):
* `erdosRenyi_triangles_kolmogorovDist_le`: proves that the literal printed Kolmogorov-distance
  inequality in Section 3.2.1 (`SteinIntro.tex:936-939`) holds unconditionally for all $n \ge 3$
  and $0 \lt p \lt 1$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

private lemma kolmogorovDist_le_one (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : kolmogorovDist μ ν ≤ 1 := by
  unfold kolmogorovDist ipm
  refine iSup_le fun h ↦ iSup_le fun ⟨x, hx⟩ ↦ iSup_le fun ⟨hi₁, hi₂⟩ ↦ ?_
  subst hx
  have hb : ∀ ρ : Measure ℝ, [IsProbabilityMeasure ρ] → Integrable ((Iic x).indicator 1) ρ →
      0 ≤ (∫ y, (Iic x).indicator (1 : ℝ → ℝ) y ∂ρ) ∧
        (∫ y, (Iic x).indicator (1 : ℝ → ℝ) y ∂ρ) ≤ 1 := fun ρ _ hi ↦
    ⟨integral_nonneg fun y ↦ by by_cases hy : y ∈ Iic x <;> simp [hy],
      (integral_mono hi (integrable_const 1) fun y ↦ by by_cases hy : y ∈ Iic x <;> simp [hy])
        |>.trans_eq (by rw [integral_const, probReal_univ, one_smul])⟩
  obtain ⟨h1, h2⟩ := hb μ hi₁; obtain ⟨h3, h4⟩ := hb ν hi₂
  exact (ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨by linarith, by linarith⟩)).trans_eq
    ENNReal.ofReal_one

private lemma pi_lt_63_div_20 : Real.pi < 63 / 20 := by
  by_contra! h
  have h1 : (1 / 2 : ℝ) < Real.sin (21 / 40) :=
    (by norm_num : (1 / 2 : ℝ) < 21 / 40 - (21 / 40) ^ 3 / 6).trans
      (Real.sin_gt_sub_cube (by norm_num))
  have hle := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ 21 / 40)
    (by linarith [Real.pi_pos] : Real.pi / 6 ≤ Real.pi / 2)
    (by linarith : (21 / 40 : ℝ) ≤ Real.pi / 6)
  rw [Real.sin_pi_div_six] at hle; linarith

private lemma sq_rpow_three_div_two {a : ℝ} (ha : 0 ≤ a) : (a ^ ((3 : ℝ) / 2)) ^ 2 = a ^ 3 := by
  rw [← Real.rpow_natCast (a ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul ha,
    show ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private lemma three_mul_choose_three {n : ℕ} (hn : 3 ≤ n) :
    3 * (n.choose 3 : ℝ) = (n.choose 2 : ℝ) * ((n : ℝ) - 2) := by
  have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq n 2)
  push_cast [Nat.cast_sub (by omega : 2 ≤ n)] at h; linarith

private lemma six_mul_choose_three {n : ℕ} (hn : 3 ≤ n) :
    6 * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  have h1 := three_mul_choose_three hn
  have h2 := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq n 1)
  rw [Nat.choose_one_right] at h2; push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h2
  calc 6 * (n.choose 3 : ℝ) = 2 * (3 * (n.choose 3 : ℝ)) := by ring
    _ = ((n.choose 2 : ℝ) * 2) * ((n : ℝ) - 2) := by rw [h1]; ring
    _ = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by rw [h2]

private lemma poly_le_of_le_31 {n : ℕ} (hn : 3 ≤ n) (hn31 : n ≤ 31) :
    63 * (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) ^ 3 ≤ 3120 * (3 * (n : ℝ) - 8) ^ 3 := by
  interval_cases n <;> norm_num

private lemma degree_nine_sos {p : ℝ} (hp0 : 0 ≤ p) :
    2 + 40 * (1 - p) ≤ 42 * (1 + p + p ^ 2) * ((1 - p ^ 3) ^ 3 + p ^ 9) := by
  have hsos : 42 * (1 + p + p ^ 2) * ((1 - p ^ 3) ^ 3 + p ^ 9) - (2 + 40 * (1 - p)) =
      p * (126 * p * (p ^ 3 - 1 / 3) ^ 2 + 126 * (p ^ 3 - p + 7 / 12) ^ 2 +
        126 * p * (p ^ 2 + 5 / 6 * p - 103 / 72) ^ 2 +
        581 / 12 * (p - 23863 / 27888) ^ 2 + 8434457 / 2294784) := by ring
  have hnn : 0 ≤ p * (126 * p * (p ^ 3 - 1 / 3) ^ 2 + 126 * (p ^ 3 - p + 7 / 12) ^ 2 +
      126 * p * (p ^ 2 + 5 / 6 * p - 103 / 72) ^ 2 +
      581 / 12 * (p - 23863 / 27888) ^ 2 + 8434457 / 2294784) := by positivity
  linarith

private lemma one_sub_cube_pos {p : ℝ} (hp1 : p < 1) : 0 < 1 - p ^ 3 := by
  rw [show 1 - p ^ 3 = (1 - p) * ((p + 1 / 2) ^ 2 + 3 / 4) by ring]
  exact mul_pos (sub_pos.mpr hp1) (by positivity)

private noncomputable def triQ₄ (n : ℕ) (p : ℝ) : ℝ :=
  (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9)
private noncomputable def triT₂ (n : ℕ) (p σ : ℝ) : ℝ :=
  Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
    (Real.sqrt Real.pi * σ ^ 2) * Real.sqrt (triQ₄ n p)

private lemma triT₂_pos_and_sq {n : ℕ} {p σ : ℝ} (hn : 3 ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hσ_pos : 0 < σ) : 0 < triQ₄ n p ∧ 0 < triT₂ n p σ ∧
      (triT₂ n p σ) ^ 2 = 26 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p / (Real.pi * σ ^ 4) := by
  have hn_cast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1p3 := one_sub_cube_pos hp1
  have hchoose3_pos : (0 : ℝ) < (n.choose 3 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hn)
  have hQ₄_pos : 0 < triQ₄ n p := by dsimp only [triQ₄]; positivity
  have h3n8 : 0 < 3 * (n : ℝ) - 8 := by linarith
  have hrpow : 0 < (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos h3n8 _
  refine ⟨hQ₄_pos, by dsimp only [triT₂]; positivity, ?_⟩; dsimp only [triT₂]
  calc (Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
          (Real.sqrt Real.pi * σ ^ 2) * Real.sqrt (triQ₄ n p)) ^ 2
      = (Real.sqrt 26) ^ 2 * ((3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2)) ^ 2 *
          (Real.sqrt (triQ₄ n p)) ^ 2 / ((Real.sqrt Real.pi) ^ 2 * σ ^ 4) := by ring
    _ = 26 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p / (Real.pi * σ ^ 4) := by
        rw [Real.sq_sqrt (by norm_num), sq_rpow_three_div_two h3n8.le,
          Real.sq_sqrt hQ₄_pos.le, Real.sq_sqrt Real.pi_pos.le]

private lemma var_factor_le {n : ℕ} {p : ℝ} (hn : 3 ≤ n) (hp0 : 0 < p) :
    1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p) ≤ ((n : ℝ) - 2) * (1 - p ^ 3) := by
  have hn_cast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hid : ((n : ℝ) - 2) * (1 - p ^ 3) - (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) =
      ((n : ℝ) - 3) * (1 - p) ^ 2 * (1 + 2 * p) := by ring
  linarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 3) (sq_nonneg (1 - p)))
    (by positivity : 0 ≤ 1 + 2 * p)]

private lemma one_le_triT₂_of_le_31 {n : ℕ} {p σ : ℝ} (hn : 3 ≤ n) (hn31 : n ≤ 31)
    (hp0 : 0 < p) (hp1 : p < 1) (hσ_pos : 0 < σ)
    (hσ_sq : σ ^ 2 = (n.choose 3 : ℝ) * p ^ 3 *
      (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p))) : 1 ≤ triT₂ n p σ := by
  obtain ⟨hQ₄_pos, hT₂_pos, hT₂_sq⟩ := triT₂_pos_and_sq hn hp0 hp1 hσ_pos
  have h1p3 := one_sub_cube_pos hp1
  have hchoose3_pos : (0 : ℝ) < (n.choose 3 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hn)
  have hp_id : p ^ 3 * (1 - p ^ 3) ≤ (1 - p ^ 3) ^ 3 + p ^ 9 := by
    linarith [show ((1 - p ^ 3) ^ 3 + p ^ 9) - p ^ 3 * (1 - p ^ 3) = (2 * p ^ 3 - 1) ^ 2 by ring,
      sq_nonneg (2 * p ^ 3 - 1)]
  have hσ2_le : σ ^ 2 ≤ (n.choose 3 : ℝ) * p ^ 3 * ((n : ℝ) - 2) * (1 - p ^ 3) := by
    rw [hσ_sq]; nlinarith [mul_pos hchoose3_pos (pow_pos hp0 3), var_factor_le hn hp0]
  have hσ4_le : σ ^ 4 ≤ (n.choose 3 : ℝ) * ((n : ℝ) - 2) ^ 2 * triQ₄ n p := by
    refine (show σ ^ 4 ≤ ((n.choose 3 : ℝ) * p ^ 3 * ((n : ℝ) - 2) * (1 - p ^ 3)) ^ 2 by
      rw [show σ ^ 4 = (σ ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (sq_nonneg σ) hσ2_le 2).trans ?_
    dsimp only [triQ₄]
    have hpos : 0 ≤ (n.choose 3 : ℝ) ^ 2 * ((n : ℝ) - 2) ^ 2 * p ^ 3 * (1 - p ^ 3) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hp_id hpos]
  have hchoose_le : (63 / 20 : ℝ) * (n.choose 3 : ℝ) * ((n : ℝ) - 2) ^ 2 ≤
      26 * (3 * (n : ℝ) - 8) ^ 3 := by
    have h6 : 6 * (n.choose 3 : ℝ) * ((n : ℝ) - 2) ^ 2 =
        (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) ^ 3 := by
      linear_combination ((n : ℝ) - 2) ^ 2 * six_mul_choose_three hn
    linarith [poly_le_of_le_31 hn hn31]
  have h1_le_sq : 1 ≤ (triT₂ n p σ) ^ 2 := by
    rw [hT₂_sq, one_le_div (by positivity)]
    exact (mul_le_mul pi_lt_63_div_20.le hσ4_le (by positivity) (by norm_num)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hchoose_le hQ₄_pos.le])
  nlinarith

private lemma stein_bound_le_triT₂_of_ge_32 {n : ℕ} {p σ vTA : ℝ} (hn32 : 32 ≤ n)
    (hp0 : 0 < p) (hp1 : p < 1) (hσ_pos : 0 < σ)
    (hσ_sq : σ ^ 2 = (n.choose 3 : ℝ) * p ^ 3 *
      (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)))
    (hT₂_lt : triT₂ n p σ < 1)
    (hvTA : vTA ≤ 3 * (n.choose 3 : ℝ) * ((n : ℝ) - 2) ^ 3 * p ^ 3 * (1 - p) *
      (2 + 40 * (1 - p)) / (2 * σ ^ 4)) :
    (1 + ((n : ℝ) - 2) / σ) * Real.sqrt vTA + 5 * (((n : ℝ) - 2) / σ) / 2 ≤ triT₂ n p σ := by
  have hn : 3 ≤ n := by omega
  obtain ⟨hQ₄_pos, hT₂_pos, hT₂_sq⟩ := triT₂_pos_and_sq hn hp0 hp1 hσ_pos
  have hn32_cast : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn32
  have h3n8 : 0 < 3 * (n : ℝ) - 8 := by linarith
  have h1p : 0 < 1 - p := sub_pos.mpr hp1; have h1p3 := one_sub_cube_pos hp1
  have hchoose3_pos : (0 : ℝ) < (n.choose 3 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hn)
  have hratio_n : ((n : ℝ) - 2) ^ 3 ≤ (15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3 := by
    have hpow := pow_le_pow_left₀ (by linarith)
      (by linarith : (n : ℝ) - 2 ≤ (15 / 44 : ℝ) * (3 * (n : ℝ) - 8)) 3
    linarith [show ((15 / 44 : ℝ) * (3 * (n : ℝ) - 8)) ^ 3 =
      (15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3 by ring]
  have hpos_f : 0 ≤ (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p * σ ^ 4 := by positivity
  have hsdTA_le : Real.sqrt vTA ≤ (14 / 25 : ℝ) * triT₂ n p σ := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have hsos_mul : (1 - p) * (2 + 40 * (1 - p)) ≤
        42 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9) := by
      rw [show 1 - p ^ 3 = (1 - p) * (1 + p + p ^ 2) by ring]
      linarith [mul_le_mul_of_nonneg_left (degree_nine_sos hp0.le) h1p.le]
    have hnum_le : 3 * (n.choose 3 : ℝ) * ((n : ℝ) - 2) ^ 3 * p ^ 3 * (1 - p) *
          (2 + 40 * (1 - p)) ≤ 126 * (15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p :=
      calc 3 * (n.choose 3 : ℝ) * ((n : ℝ) - 2) ^ 3 * p ^ 3 * (1 - p) * (2 + 40 * (1 - p))
          = 3 * (n.choose 3 : ℝ) * p ^ 3 * ((n : ℝ) - 2) ^ 3 *
              ((1 - p) * (2 + 40 * (1 - p))) := by ring
        _ ≤ 3 * (n.choose 3 : ℝ) * p ^ 3 * ((15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3) *
              (42 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hratio_n (by positivity))
              hsos_mul (by positivity) (by positivity)
        _ = 126 * (15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p := by dsimp [triQ₄]; ring
    have h1 : vTA ≤ 63 * (15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p / σ ^ 4 :=
      hvTA.trans (by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [pow_pos hσ_pos 4])
    refine h1.trans ?_
    rw [mul_pow, hT₂_sq, show (14 / 25 : ℝ) ^ 2 * (26 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p /
      (Real.pi * σ ^ 4)) = (14 / 25 : ℝ) ^ 2 * 26 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p /
        (Real.pi * σ ^ 4) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpi_le : 63 * (15 / 44 : ℝ) ^ 3 * Real.pi ≤ (14 / 25 : ℝ) ^ 2 * 26 :=
      (mul_le_mul_of_nonneg_left pi_lt_63_div_20.le (by norm_num)).trans (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hpi_le hpos_f]
  set δ : ℝ := ((n : ℝ) - 2) / σ
  have hδ_le : δ ≤ (7 / 50 : ℝ) * triT₂ n p σ := by
    have hδ_sq : δ ^ 2 ≤ ((7 / 50 : ℝ) * triT₂ n p σ) ^ 2 := by
      have h4 : (1 : ℝ) ≤ 4 * ((1 - p ^ 3) ^ 3 + p ^ 9) := by
        rw [show (1 - p ^ 3) ^ 3 + p ^ 9 = 1 / 4 + 3 * (p ^ 3 - 1 / 2) ^ 2 by ring]
        linarith [sq_nonneg (p ^ 3 - 1 / 2)]
      have hnum_δ : ((n : ℝ) - 2) ^ 2 * σ ^ 2 ≤
          4 * (15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p := by
        rw [hσ_sq]
        refine (show ((n : ℝ) - 2) ^ 2 * ((n.choose 3 : ℝ) * p ^ 3 *
              (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p))) ≤
            (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((n : ℝ) - 2) ^ 3 by
          nlinarith [mul_nonneg (sq_nonneg ((n : ℝ) - 2))
            (mul_pos hchoose3_pos (pow_pos hp0 3)).le, var_factor_le hn hp0]).trans ?_
        calc (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((n : ℝ) - 2) ^ 3
            ≤ (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) *
                ((15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3) * 1 := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_left hratio_n (by positivity)
          _ ≤ (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) *
                ((15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3) *
                (4 * ((1 - p ^ 3) ^ 3 + p ^ 9)) := mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = 4 * (15 / 44 : ℝ) ^ 3 * (3 * (n : ℝ) - 8) ^ 3 * triQ₄ n p := by dsimp [triQ₄]; ring
      rw [show δ ^ 2 = ((n : ℝ) - 2) ^ 2 * σ ^ 2 / σ ^ 4 by dsimp [δ]; field_simp [hσ_pos.ne'],
        mul_pow, hT₂_sq, show (7 / 50 : ℝ) ^ 2 * (26 * (3 * (n : ℝ) - 8) ^ 3 *
          triQ₄ n p / (Real.pi * σ ^ 4)) = (7 / 50 : ℝ) ^ 2 * 26 * (3 * (n : ℝ) - 8) ^ 3 *
            triQ₄ n p / (Real.pi * σ ^ 4) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
      have hpi_le : 4 * (15 / 44 : ℝ) ^ 3 * Real.pi ≤ (7 / 50 : ℝ) ^ 2 * 26 :=
        (mul_le_mul_of_nonneg_left pi_lt_63_div_20.le (by norm_num)).trans (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hnum_δ (by positivity : 0 ≤ Real.pi * σ ^ 4),
        mul_le_mul_of_nonneg_right hpi_le hpos_f]
    nlinarith [abs_le_of_sq_le_sq' hδ_sq (by positivity)]
  have h1_δ_sd : (1 + δ) * Real.sqrt vTA ≤ (1 + 7 / 50 : ℝ) * ((14 / 25 : ℝ) * triT₂ n p σ) :=
    mul_le_mul (by linarith) hsdTA_le (Real.sqrt_nonneg _) (by norm_num)
  linarith

/-- Section 3.2.1 literal $d_{\mathrm{K}}$ inequality (`SteinIntro.tex:935-939`; `ISSUE-TYPO-3.2.1`,
`ISSUE-3.2.1`): although Theorem 3.5 bounds $d_{\mathrm{W}}(W, Z)$
(`Sec3_2_1_triangles_restricted`), the literal printed bound with $d_{\mathrm{K}}(W, Z)$ on the
left-hand side also holds unconditionally for all $n \ge 3$ and $0 \lt p \lt 1$. -/
theorem erdosRenyi_triangles_kolmogorovDist_le
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {Z : Ω' → ℝ} (hn : 3 ≤ n) (hp0 : 0 < p) (hp1 : p < 1)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℝ := ∫ G, T G ∂erdosRenyi n p
    let σ : ℝ := Real.sqrt (variance T (erdosRenyi n p))
    let W : SimpleGraph (Fin n) → ℝ := fun G ↦ (T G - μ) / σ
    μ = (n.choose 3 : ℝ) * p ^ 3 ∧
      variance T (erdosRenyi n p) =
        (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) ∧
      kolmogorovDist ((erdosRenyi n p).map W) (P'.map Z) ≤
        ENNReal.ofReal
          ((3 * (n : ℝ) - 8) ^ 2 / σ ^ 3 *
              ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 2 + p ^ 6)) +
            Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
              (Real.sqrt Real.pi * σ ^ 2) *
              Real.sqrt
                ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9))) := by
  intro T μ σ W
  obtain ⟨hμ, hVarT, -⟩ := Sec3_2_1_triangles_restricted_proof P' hn hp0 hp1 hZ hZ_law
  change μ = _ at hμ; change variance T (erdosRenyi n p) = _ at hVarT
  refine ⟨hμ, hVarT, ?_⟩
  have hn_cast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1p3 := one_sub_cube_pos hp1
  have hVar_pos : 0 < variance T (erdosRenyi n p) := by
    rw [hVarT]
    have hextra : 0 ≤ 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg p))
        (sub_pos.mpr hp1).le
    exact mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.choose_pos hn)) (pow_pos hp0 3)) (by linarith)
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar_pos
  have hσ_sq : σ ^ 2 = (n.choose 3 : ℝ) * p ^ 3 *
      (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) :=
    (Real.sq_sqrt hVar_pos.le).trans hVarT
  set T₁ : ℝ := (3 * (n : ℝ) - 8) ^ 2 / σ ^ 3 *
    ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 2 + p ^ 6))
  have h3n8 : 0 ≤ 3 * (n : ℝ) - 8 := by linarith
  have hT₁_nn : 0 ≤ T₁ := by dsimp [T₁]; positivity
  change kolmogorovDist ((erdosRenyi n p).map W) (P'.map Z) ≤ ENNReal.ofReal (T₁ + triT₂ n p σ)
  by_cases hT₂_ge : 1 ≤ triT₂ n p σ
  · have hprobW : IsProbabilityMeasure ((erdosRenyi n p).map W) :=
      (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance
    have hprobZ : IsProbabilityMeasure (P'.map Z) :=
      (Measure.isProbabilityMeasure_map_iff hZ).mpr inferInstance
    exact (@kolmogorovDist_le_one _ _ hprobW hprobZ).trans
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
  push Not at hT₂_ge
  rcases le_or_gt n 31 with hn31 | hn32
  · exact (not_le_of_gt hT₂_ge (one_le_triT₂_of_le_31 hn hn31 hp0 hp1 hσ_pos hσ_sq)).elim
  · set q : unitInterval := ⟨p, hp0.le, hp1.le⟩; set μ₀ := bernoulliMeasure true false q
    set ν := bitPi (n.choose 2) μ₀; set P₂ := bitProd (n.choose 2) μ₀
    have hmapG : ν.map (bitsToGraph n) = erdosRenyi n p :=
      map_bitsToGraph_eq_erdosRenyi hp0.le hp1.le
    let Wb : EdgeBits n → ℝ := W ∘ bitsToGraph n
    have hmapW : ν.map Wb = (erdosRenyi n p).map W := by
      rw [← hmapG, Measure.map_map .of_discrete .of_discrete]
    let C : EdgeIdx n → EdgeBits n → ℝ := fun k x ↦ wedgeSum n k x / σ
    set δ : ℝ := ((n : ℝ) - 2) / σ
    have hδ_nn : 0 ≤ δ := div_nonneg (by linarith) hσ_pos.le
    have hWb0 : ∫ x, Wb x ∂ν = 0 := by
      have hm := integral_map (μ := ν) (φ := bitsToGraph n) Measurable.of_discrete.aemeasurable
        (f := W) Measurable.of_discrete.aestronglyMeasurable
      rw [hmapG] at hm; dsimp only [Wb, Function.comp_apply]; rw [← hm]
      simp only [W, div_eq_mul_inv]
      rw [integral_mul_const, integral_sub (finite_discrete_integrable _) (integrable_const μ),
        integral_const, probReal_univ, one_smul]
      change (μ - μ) * σ⁻¹ = 0; ring
    have hWb_var : variance Wb ν = 1 := by
      rw [← show variance W (erdosRenyi n p) = variance Wb ν by
        rw [← hmapG, variance_map Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable],
        show W = fun G ↦ σ⁻¹ * (T G + (-μ)) from funext fun G ↦ by dsimp [W]; ring,
        variance_const_mul, variance_add_const Measurable.of_discrete.aestronglyMeasurable (-μ),
        show variance T (erdosRenyi n p) = σ ^ 2 from (Real.sq_sqrt hVar_pos.le).symm]
      field_simp [hσ_pos.ne']
    have hWb_diff : ∀ (k : EdgeIdx n) (x : EdgeBits n) (b : Bool),
        Wb x - Wb (Function.update x k b) = (bitVal (x k) - bitVal b) * C k x := fun k x b ↦ by
      dsimp only [Wb, Function.comp_apply, W, C]
      rw [show ((T (bitsToGraph n x) - μ) / σ) -
        ((T (bitsToGraph n (Function.update x k b)) - μ) / σ) =
        (triCountBits n x - triCountBits n (Function.update x k b)) / σ by
          dsimp [T, triCountBits]; ring, triCountBits_sub_update n k x b, mul_div_assoc]
    have hC_bdd : ∀ (k : EdgeIdx n) (x : EdgeBits n), 0 ≤ C k x ∧ C k x ≤ δ := fun k x ↦
      ⟨div_nonneg (wedgeSum_nonneg n k x) hσ_pos.le,
        div_le_div_of_nonneg_right (wedgeSum_le hn k x) hσ_pos.le⟩
    have hkolm := monotone_pi_kolmogorovDist_le μ₀ P' hZ hZ_law hδ_nn hWb0 hWb_var hWb_diff hC_bdd
    dsimp only at hkolm; rw [hmapW] at hkolm
    refine hkolm.trans (ENNReal.ofReal_le_ofReal ?_)
    let TA : EdgePairs n → ℝ := fun z ↦
      (1 / 2 : ℝ) * ∑ k : EdgeIdx n,
        (bitVal (z.1 k) - bitVal (z.2 k)) ^ 2 * C k z.1 * C k (hybVec k.1 z)
    have hTA_eq : TA = fun z ↦ (1 / (2 * σ ^ 2)) * triTA₀ n z := funext fun z ↦ by
      simp_rw [TA, triTA₀, C, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ ↦ by ring
    have hvarTA_le : variance TA P₂ ≤
        3 * (n.choose 3 : ℝ) * ((n : ℝ) - 2) ^ 3 * p ^ 3 * (1 - p) * (2 + 40 * (1 - p)) /
          (2 * σ ^ 4) := by
      rw [hTA_eq, variance_const_mul]
      refine (mul_le_mul_of_nonneg_left (variance_triTA₀_le hn q)
        (sq_nonneg (1 / (2 * σ ^ 2)))).trans_eq ?_
      have hq_val : (q : ℝ) = p := rfl
      have hdiv : ∀ A : ℝ, (1 / (2 * σ ^ 2)) ^ 2 * (2 * A) = A / (2 * σ ^ 4) := fun A ↦ by
        field_simp [hσ_pos.ne']
      have hrw : (n.choose 2 : ℝ) * 2 * p ^ 3 * (1 - p) * ((n : ℝ) - 2) ^ 4 * (2 + 40 * (1 - p)) =
          2 * (((n.choose 2 : ℝ) * ((n : ℝ) - 2)) * ((n : ℝ) - 2) ^ 3 * p ^ 3 * (1 - p) *
            (2 + 40 * (1 - p))) := by ring
      rw [hq_val, hrw, hdiv, ← three_mul_choose_three hn]
    linarith [stein_bound_le_triT₂_of_ge_32 hn32 hp0 hp1 hσ_pos hσ_sq hT₂_ge hvarTA_le]

end SteinMethod
