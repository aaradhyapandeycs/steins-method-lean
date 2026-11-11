/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonStein
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Stein Solution Bounds for the Poisson Distribution (`Formalization.Poisson.SteinBounds`)

Elementary proofs from scratch of the Barbour–Holst–Janson (1992) uniform and forward-difference
bounds on `poissonSteinSol` (Lemma 4.4 `\label{lem103}`, eq. `(4.2)` `\label{102}`,
`SteinIntro.tex:1879-1908`).
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-! ### Auxiliary Poisson point-mass and tail identities -/

private noncomputable def poissonPMFVal (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)

private lemma poissonPMFVal_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ poissonPMFVal r n := by
  unfold poissonPMFVal
  positivity

private lemma hasSum_poissonPMFVal (r : ℝ≥0) : HasSum (poissonPMFVal r) 1 := by
  unfold poissonPMFVal
  exact ProbabilityTheory.hasSum_one_poissonMeasure r

private lemma summable_poissonPMFVal (r : ℝ≥0) : Summable (poissonPMFVal r) :=
  (hasSum_poissonPMFVal r).summable

private lemma tsum_poissonPMFVal (r : ℝ≥0) : ∑' n, poissonPMFVal r n = 1 :=
  (hasSum_poissonPMFVal r).tsum_eq

private lemma poissonPMFVal_zero (r : ℝ≥0) : poissonPMFVal r 0 = Real.exp (-(r : ℝ)) := by
  simp [poissonPMFVal]

private lemma sum_range_poissonPMFVal_le_one (r : ℝ≥0) (N : ℕ) :
    ∑ n ∈ Finset.range N, poissonPMFVal r n ≤ 1 := by
  calc ∑ n ∈ Finset.range N, poissonPMFVal r n
    _ ≤ ∑' n, poissonPMFVal r n :=
      Summable.sum_le_tsum (Finset.range N) (fun i _ ↦ poissonPMFVal_nonneg r i)
        (summable_poissonPMFVal r)
    _ = 1 := tsum_poissonPMFVal r

private lemma poissonLaw_real_singleton_eq (r : ℝ≥0) (n : ℕ) :
    (poissonLaw r).real {n} = poissonPMFVal r n := by
  simpa [poissonPMFVal] using ProbabilityTheory.poissonMeasure_real_singleton r n

private lemma poissonLaw_real_Iio (r : ℝ≥0) (m : ℕ) :
    (poissonLaw r).real (Set.Iio m) = ∑ i ∈ Finset.range m, poissonPMFVal r i := by
  rw [← Finset.coe_range m, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun i _ ↦ poissonLaw_real_singleton_eq r i

private lemma poissonLaw_real_Ici (r : ℝ≥0) (m : ℕ) :
    (poissonLaw r).real (Set.Ici m) = ∑' l : ℕ, poissonPMFVal r (l + m) := by
  have hsplit : (∑ i ∈ Finset.range m, poissonPMFVal r i) + ∑' l, poissonPMFVal r (l + m) = 1 := by
    rw [Summable.sum_add_tsum_nat_add m (summable_poissonPMFVal r), tsum_poissonPMFVal]
  rw [← Set.compl_Iio, probReal_compl_eq_one_sub .of_discrete, poissonLaw_real_Iio]
  linarith

private lemma exp_pos_mul_neg (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-! ### Elementary exponential inequality -/

/-- Elementary exponential bound `(1 - e^{-r}) / r ≤ min(1, r⁻¹)` for `r > 0`
(Lemma 4.4 `\label{lem103}`, eq. `(4.2)` `\label{102}`, `SteinIntro.tex:1879-1886`). -/
theorem one_sub_exp_neg_div_le_min {r : ℝ≥0} (hr : 0 < r) :
    (1 - Real.exp (-(r : ℝ))) / (r : ℝ) ≤ min 1 (r : ℝ)⁻¹ := by
  have hr' : (0 : ℝ) < r := by positivity
  refine le_min ?_ ?_
  · rw [div_le_one hr']
    linarith [Real.add_one_le_exp (-(r : ℝ))]
  · rw [← one_div]
    refine div_le_div_of_nonneg_right ?_ hr'.le
    linarith [Real.exp_pos (-(r : ℝ))]

/-! ### Combinatorial unimodality and uniform bound `|f_A(k)| ≤ min(1, r^{-1/2})` -/

private noncomputable def steinQuadBound (r : ℝ≥0) (k : ℕ) : ℝ :=
  ((r : ℝ) ^ (k + 1))⁻¹ * Real.exp (r : ℝ) * (k.factorial : ℝ) *
    ((poissonLaw r).real (Set.Iio (k + 1)) * (poissonLaw r).real (Set.Ici (k + 1)))

private lemma abs_poissonSteinSol_succ_le_quad (r : ℝ≥0) (A : Set ℕ) (k : ℕ) :
    |poissonSteinSol r A (k + 1)| ≤ steinQuadBound r k := by
  set U : Set ℕ := Set.Iio (k + 1)
  have hU_compl : Uᶜ = Set.Ici (k + 1) := Set.compl_Iio
  have hA_split : (poissonLaw r).real A =
      (poissonLaw r).real (A ∩ U) + (poissonLaw r).real (A \ U) :=
    (measureReal_inter_add_sdiff .of_discrete).symm
  have hU_sum : (poissonLaw r).real U + (poissonLaw r).real Uᶜ = 1 := by
    rw [measureReal_add_measureReal_compl .of_discrete, probReal_univ]
  have hid : (poissonLaw r).real (A ∩ U) - (poissonLaw r).real A * (poissonLaw r).real U =
      (poissonLaw r).real (A ∩ U) * (poissonLaw r).real Uᶜ -
        (poissonLaw r).real (A \ U) * (poissonLaw r).real U := by
    calc (poissonLaw r).real (A ∩ U) - (poissonLaw r).real A * (poissonLaw r).real U
      _ = (poissonLaw r).real (A ∩ U) * 1 -
            ((poissonLaw r).real (A ∩ U) + (poissonLaw r).real (A \ U)) *
              (poissonLaw r).real U := by
        rw [mul_one, ← hA_split]
      _ = (poissonLaw r).real (A ∩ U) * ((poissonLaw r).real U + (poissonLaw r).real Uᶜ) -
            ((poissonLaw r).real (A ∩ U) + (poissonLaw r).real (A \ U)) *
              (poissonLaw r).real U := by
        rw [hU_sum]
      _ = (poissonLaw r).real (A ∩ U) * (poissonLaw r).real Uᶜ -
            (poissonLaw r).real (A \ U) * (poissonLaw r).real U := by
        ring
  have h1_nonneg : 0 ≤ (poissonLaw r).real (A ∩ U) * (poissonLaw r).real Uᶜ :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  have h2_nonneg : 0 ≤ (poissonLaw r).real (A \ U) * (poissonLaw r).real U :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  have h1_le : (poissonLaw r).real (A ∩ U) * (poissonLaw r).real Uᶜ ≤
      (poissonLaw r).real U * (poissonLaw r).real Uᶜ :=
    mul_le_mul_of_nonneg_right (measureReal_mono Set.inter_subset_right) measureReal_nonneg
  have h2_le : (poissonLaw r).real (A \ U) * (poissonLaw r).real U ≤
      (poissonLaw r).real Uᶜ * (poissonLaw r).real U :=
    mul_le_mul_of_nonneg_right (measureReal_mono fun _ hx ↦ hx.2) measureReal_nonneg
  have habs_cov :
      |(poissonLaw r).real (A ∩ U) - (poissonLaw r).real A * (poissonLaw r).real U| ≤
        (poissonLaw r).real U * (poissonLaw r).real (Set.Ici (k + 1)) := by
    rw [hid, ← hU_compl]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hpref : 0 ≤ ((r : ℝ) ^ (k + 1))⁻¹ * Real.exp (r : ℝ) * (k.factorial : ℝ) := by positivity
  rw [poissonSteinSol, steinQuadBound, abs_mul, abs_of_nonneg hpref]
  exact mul_le_mul_of_nonneg_left habs_cov hpref

private noncomputable def steinCoeff (n k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (min (k + 1) (n + 1)),
    ((n.factorial : ℝ) * (k.factorial : ℝ)) /
      ((i.factorial : ℝ) * ((k + 1 + n - i).factorial : ℝ))

private lemma steinCoeff_nonneg (n k : ℕ) : 0 ≤ steinCoeff n k :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

private lemma steinCoeff_eq_mul_sum_choose (n k : ℕ) :
    steinCoeff n k =
      (((n.factorial : ℝ) * (k.factorial : ℝ)) / ((k + 1 + n).factorial : ℝ)) *
        ∑ i ∈ Finset.range (min (k + 1) (n + 1)), ((k + 1 + n).choose i : ℝ) := by
  rw [steinCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi_le : i ≤ k + 1 + n := by
    rw [Finset.mem_range] at hi
    omega
  have hch : (((k + 1 + n).choose i : ℝ) * (i.factorial : ℝ) *
      ((k + 1 + n - i).factorial : ℝ)) = ((k + 1 + n).factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi_le
  have hden : (i.factorial : ℝ) * ((k + 1 + n - i).factorial : ℝ) ≠ 0 := by positivity
  have hN : ((k + 1 + n).factorial : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_div_iff hden hN, ← hch]
  ring

private lemma sum_range_choose_succ_succ (N k : ℕ) :
    (∑ i ∈ Finset.range (k + 2), (N + 1).choose i) =
      2 * (∑ i ∈ Finset.range (k + 1), N.choose i) + N.choose (k + 1) := by
  rw [Finset.sum_range_succ']
  simp_rw [Nat.choose_succ_succ', Finset.sum_add_distrib, Nat.choose_zero_right]
  have hshift :
      (∑ x ∈ Finset.range (k + 1), N.choose (x + 1)) + 1 =
        (∑ i ∈ Finset.range (k + 1), N.choose i) + N.choose (k + 1) := by
    have h1 := Finset.sum_range_succ' N.choose (k + 1)
    have h2 := Finset.sum_range_succ N.choose (k + 1)
    rw [Nat.choose_zero_right] at h1
    rw [← h1, h2]
  rw [add_assoc, hshift]
  ring

private lemma steinCoeff_succ_below_diag {n k : ℕ} (hk : k < n) :
    ((k : ℝ) + 2 + (n : ℝ)) * steinCoeff n (k + 1) =
      2 * ((k : ℝ) + 1) * steinCoeff n k + 1 := by
  rw [steinCoeff_eq_mul_sum_choose n (k + 1), steinCoeff_eq_mul_sum_choose n k]
  have hmin1 : min (k + 1 + 1) (n + 1) = k + 2 := by omega
  have hmin0 : min (k + 1) (n + 1) = k + 1 := by omega
  have hN : k + 1 + 1 + n = k + 1 + n + 1 := by omega
  rw [hmin1, hmin0, hN]
  set S : ℝ := ∑ i ∈ Finset.range (k + 1), ((k + 1 + n).choose i : ℝ)
  set C : ℝ := (((k + 1 + n).choose (k + 1) : ℕ) : ℝ)
  set F : ℝ := ((k + 1 + n).factorial : ℝ)
  have hsum : (∑ i ∈ Finset.range (k + 2), ((k + 1 + n + 1).choose i : ℝ)) = 2 * S + C := by
    dsimp only [S, C]
    exact_mod_cast sum_range_choose_succ_succ (k + 1 + n) k
  have hden_succ : (((k + 1 + n + 1).factorial : ℕ) : ℝ) =
      ((k : ℝ) + 2 + (n : ℝ)) * F := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hk_succ : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hch : C * (((k : ℝ) + 1) * (k.factorial : ℝ)) * (n.factorial : ℝ) = F := by
    rw [← hk_succ]
    have hnat := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (k + 1) n)
    rw [Nat.add_sub_cancel_left] at hnat
    dsimp only [C, F]
    exact_mod_cast hnat
  have ha : (k : ℝ) + 2 + (n : ℝ) ≠ 0 := by positivity
  have hF : F ≠ 0 := by positivity
  rw [hsum, hden_succ, hk_succ]
  have hlhs : ((k : ℝ) + 2 + (n : ℝ)) *
      (((n.factorial : ℝ) * (((k : ℝ) + 1) * (k.factorial : ℝ)) /
        (((k : ℝ) + 2 + (n : ℝ)) * F)) * (2 * S + C)) =
      ((n.factorial : ℝ) * (((k : ℝ) + 1) * (k.factorial : ℝ)) * (2 * S + C)) / F := by
    rw [div_mul_eq_mul_div, ← mul_div_assoc, mul_div_mul_left _ _ ha]
  rw [hlhs, div_eq_iff hF]
  have hrhs : (2 * ((k : ℝ) + 1) * (((n.factorial : ℝ) * (k.factorial : ℝ) / F) * S) + 1) * F =
      2 * ((k : ℝ) + 1) * (((n.factorial : ℝ) * (k.factorial : ℝ) / F * F) * S) + F := by
    ring
  rw [hrhs, div_mul_cancel₀ _ hF, ← hch]
  ring

private lemma steinCoeff_zero_right (n : ℕ) : steinCoeff n 0 = 1 / ((n : ℝ) + 1) := by
  have hmin : min (0 + 1) (n + 1) = 1 := by omega
  have hN : 0 + 1 + n = n + 1 := by omega
  rw [steinCoeff, hmin, Finset.range_one, Finset.sum_singleton]
  simp only [Nat.factorial_zero, Nat.cast_one, mul_one, one_mul, Nat.sub_zero, hN,
    Nat.factorial_succ]
  push_cast
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [div_eq_div_iff (mul_ne_zero hn1 hn) hn1]
  ring

private lemma mul_steinCoeff_le_one {n k : ℕ} (hk : k ≤ n) :
    ((n : ℝ) - (k : ℝ) + 1) * steinCoeff n k ≤ 1 := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, sub_zero, steinCoeff_zero_right, mul_one_div,
      div_self (by positivity : (n : ℝ) + 1 ≠ 0)]
  | succ k ih =>
    have hlt : k < n := Nat.lt_of_succ_le hk
    have ihk : ((n : ℝ) - (k : ℝ) + 1) * steinCoeff n k ≤ 1 := ih hlt.le
    have hstep : ((n : ℝ) - (k : ℝ)) * steinCoeff n k ≤ 1 := by
      linarith [steinCoeff_nonneg n k]
    have hrec := steinCoeff_succ_below_diag hlt
    have hpos : 0 < (k : ℝ) + 2 + (n : ℝ) := by positivity
    have hsub : (n : ℝ) - ((k + 1 : ℕ) : ℝ) + 1 = (n : ℝ) - (k : ℝ) := by
      push_cast
      ring
    rw [hsub]
    have hprod : ((k : ℝ) + 2 + (n : ℝ)) * (((n : ℝ) - (k : ℝ)) * steinCoeff n (k + 1)) ≤
        ((k : ℝ) + 2 + (n : ℝ)) * 1 := by
      have hid : ((k : ℝ) + 2 + (n : ℝ)) * (((n : ℝ) - (k : ℝ)) * steinCoeff n (k + 1)) =
          ((n : ℝ) - (k : ℝ)) * (((k : ℝ) + 2 + (n : ℝ)) * steinCoeff n (k + 1)) := by ring
      rw [hid, hrec]
      calc ((n : ℝ) - (k : ℝ)) * (2 * ((k : ℝ) + 1) * steinCoeff n k + 1)
        _ = 2 * ((k : ℝ) + 1) * (((n : ℝ) - (k : ℝ)) * steinCoeff n k) +
              ((n : ℝ) - (k : ℝ)) := by ring
        _ ≤ 2 * ((k : ℝ) + 1) * 1 + ((n : ℝ) - (k : ℝ)) := by
          have hk1 : 0 ≤ 2 * ((k : ℝ) + 1) := by positivity
          linarith [mul_le_mul_of_nonneg_left hstep hk1]
        _ = ((k : ℝ) + 2 + (n : ℝ)) * 1 := by ring
    exact le_of_mul_le_mul_left hprod hpos

private lemma steinCoeff_le_succ_below_diag {n k : ℕ} (hk : k < n) :
    steinCoeff n k ≤ steinCoeff n (k + 1) := by
  have hrec := steinCoeff_succ_below_diag hk
  have hle : ((n : ℝ) - (k : ℝ)) * steinCoeff n k ≤ 1 := by
    linarith [mul_steinCoeff_le_one hk.le, steinCoeff_nonneg n k]
  have hpos : 0 < (k : ℝ) + 2 + (n : ℝ) := by positivity
  have hmul : ((k : ℝ) + 2 + (n : ℝ)) * steinCoeff n k ≤
      ((k : ℝ) + 2 + (n : ℝ)) * steinCoeff n (k + 1) := by
    rw [hrec]
    have hid : ((k : ℝ) + 2 + (n : ℝ)) * steinCoeff n k =
        2 * ((k : ℝ) + 1) * steinCoeff n k + ((n : ℝ) - (k : ℝ)) * steinCoeff n k := by ring
    linarith
  exact le_of_mul_le_mul_left hmul hpos

private lemma steinCoeff_succ_le_above_diag {n k : ℕ} (hnk : n ≤ k) :
    steinCoeff n (k + 1) ≤ steinCoeff n k := by
  have hmin1 : min (k + 1 + 1) (n + 1) = n + 1 := by omega
  have hmin0 : min (k + 1) (n + 1) = n + 1 := by omega
  rw [steinCoeff, steinCoeff, hmin1, hmin0]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hi_le : i ≤ n := by
    rw [Finset.mem_range] at hi
    omega
  set m : ℕ := k + 1 + n - i
  have hsub : k + 1 + 1 + n - i = m + 1 := by omega
  have hkm : k ≤ m := by omega
  rw [hsub, Nat.factorial_succ k, Nat.factorial_succ m]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hnum : (k : ℝ) + 1 ≤ (m : ℝ) + 1 := by
    have : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hkm
    linarith
  have hfac_nonneg : 0 ≤ (n.factorial : ℝ) * (k.factorial : ℝ) *
      (i.factorial : ℝ) * (m.factorial : ℝ) := by positivity
  calc ((n.factorial : ℝ) * (((k : ℝ) + 1) * (k.factorial : ℝ))) *
        ((i.factorial : ℝ) * (m.factorial : ℝ))
    _ = ((k : ℝ) + 1) * ((n.factorial : ℝ) * (k.factorial : ℝ) *
          (i.factorial : ℝ) * (m.factorial : ℝ)) := by ring
    _ ≤ ((m : ℝ) + 1) * ((n.factorial : ℝ) * (k.factorial : ℝ) *
          (i.factorial : ℝ) * (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hnum hfac_nonneg
    _ = ((n.factorial : ℝ) * (k.factorial : ℝ)) *
          ((i.factorial : ℝ) * (((m : ℝ) + 1) * (m.factorial : ℝ))) := by ring

private lemma steinCoeff_le_diag (n k : ℕ) : steinCoeff n k ≤ steinCoeff n n := by
  rcases le_total k n with hkn | hnk
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hkn
    clear hkn
    induction d generalizing k with
    | zero =>
      have hk : k = n := by omega
      rw [hk]
    | succ d ih =>
      have hlt : k < n := by omega
      exact (steinCoeff_le_succ_below_diag hlt).trans (ih (k + 1) (by omega))
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
    clear hnk
    induction d with
    | zero => simp
    | succ d ih =>
      exact (steinCoeff_succ_le_above_diag (Nat.le_add_right n d)).trans ih

private lemma steinCoeff_diag_eq (n : ℕ) :
    steinCoeff n n =
      (((n.factorial : ℝ) * (n.factorial : ℝ)) / (((2 * n + 1).factorial : ℕ) : ℝ)) *
        (4 : ℝ) ^ n := by
  have hmin : min (n + 1) (n + 1) = n + 1 := by omega
  have h2n : n + 1 + n = 2 * n + 1 := by omega
  rw [steinCoeff_eq_mul_sum_choose n n, hmin, h2n]
  have hhalf : (∑ i ∈ Finset.range (n + 1), ((2 * n + 1).choose i : ℝ)) = (4 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose_halfway n
  rw [hhalf]

private lemma steinCoeff_diag_zero : steinCoeff 0 0 = 1 := by
  rw [steinCoeff_diag_eq]
  norm_num

private lemma steinCoeff_diag_succ (n : ℕ) :
    steinCoeff (n + 1) (n + 1) =
      steinCoeff n n * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) := by
  rw [steinCoeff_diag_eq (n + 1), steinCoeff_diag_eq n]
  have h2n : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
  have hfac2 : (((2 * (n + 1) + 1).factorial : ℕ) : ℝ) =
      (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 2) * (((2 * n + 1).factorial : ℕ) : ℝ) := by
    rw [h2n, Nat.factorial_succ ((2 * n + 1) + 1), Nat.factorial_succ (2 * n + 1)]
    push_cast
    ring
  have hfac1 : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac2, hfac1, pow_succ]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_div_comm,
    div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma steinCoeff_diag_le_one (n : ℕ) : steinCoeff n n ≤ 1 := by
  induction n with
  | zero => rw [steinCoeff_diag_zero]
  | succ n ih =>
    rw [steinCoeff_diag_succ]
    have hfac : (2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc steinCoeff n n * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3))
      _ ≤ 1 * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ 1 := by linarith

private lemma steinCoeff_diag_sq_le (n : ℕ) :
    (steinCoeff n n) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    rw [steinCoeff_diag_zero]
    norm_num
  | succ n ih =>
    rw [steinCoeff_diag_succ, mul_pow]
    calc (steinCoeff n n) ^ 2 * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) ^ 2
      _ ≤ (1 / ((n : ℝ) + 1)) * ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3)) ^ 2 :=
        mul_le_mul_of_nonneg_right ih (sq_nonneg _)
      _ ≤ 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have hdiff : 1 * (((n : ℝ) + 1) * (2 * (n : ℝ) + 3) ^ 2) -
            (1 * (2 * (n : ℝ) + 2) ^ 2) * ((n : ℝ) + 1 + 1) = (n : ℝ) + 1 := by ring
        linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

private lemma steinQuadBound_eq_tsum {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    steinQuadBound r k = ∑' n : ℕ, steinCoeff n k * poissonPMFVal r n := by
  let f : ℕ → ℝ := fun i ↦ if i < k + 1 then poissonPMFVal r i else 0
  let g : ℕ → ℝ := fun l ↦ poissonPMFVal r (l + (k + 1))
  have hf_eq : (poissonLaw r).real (Set.Iio (k + 1)) = ∑' i, f i := by
    rw [poissonLaw_real_Iio]
    have htsum : (∑' i, f i) = ∑ i ∈ Finset.range (k + 1), f i :=
      tsum_eq_sum fun i hi ↦ by
        dsimp only [f]
        split_ifs with hik
        · exact absurd (Finset.mem_range.mpr hik) hi
        · rfl
    rw [htsum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    dsimp only [f]
    split_ifs with hik
    · rfl
    · exact absurd (Finset.mem_range.mp hi) hik
  have hg_eq : (poissonLaw r).real (Set.Ici (k + 1)) = ∑' l, g l :=
    poissonLaw_real_Ici r (k + 1)
  have hf_norm : Summable fun i ↦ ‖f i‖ :=
    summable_of_ne_finset_zero (s := Finset.range (k + 1)) fun i hi ↦ by
      dsimp only [f]
      split_ifs with hik
      · exact absurd (Finset.mem_range.mpr hik) hi
      · exact norm_zero
  have hg_norm : Summable fun l ↦ ‖g l‖ := by
    have hg_sum : Summable g :=
      (summable_nat_add_iff (k + 1)).mpr (summable_poissonPMFVal r)
    convert hg_sum using 1
    ext l
    rw [Real.norm_eq_abs, abs_of_nonneg (poissonPMFVal_nonneg r _)]
  rw [steinQuadBound, hf_eq, hg_eq,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf_norm hg_norm, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  have hsub_sum :
      (∑ i ∈ Finset.range (n + 1), f i * g (n - i)) =
        ∑ i ∈ Finset.range (min (k + 1) (n + 1)),
          poissonPMFVal r i * poissonPMFVal r (n - i + (k + 1)) := by
    trans ∑ i ∈ Finset.range (min (k + 1) (n + 1)), f i * g (n - i)
    · refine (Finset.sum_subset
        (Finset.range_mono (by omega : min (k + 1) (n + 1) ≤ n + 1)) ?_).symm
      intro i hi hni
      rw [Finset.mem_range] at hi hni
      dsimp only [f]
      split_ifs with hik
      · omega
      · exact zero_mul _
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      dsimp only [f, g]
      split_ifs with hik
      · rfl
      · rw [Finset.mem_range] at hi
        omega
  rw [hsub_sum, Finset.mul_sum, steinCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hin : n - i + (k + 1) = k + 1 + n - i := by
    rw [Finset.mem_range] at hi
    omega
  set m : ℕ := k + 1 + n - i
  have hpow : (r : ℝ) ^ i * (r : ℝ) ^ m = (r : ℝ) ^ (k + 1) * (r : ℝ) ^ n := by
    rw [← pow_add, ← pow_add]
    congr 1
    rw [Finset.mem_range] at hi
    omega
  rw [hin]
  change (((r : ℝ) ^ (k + 1))⁻¹ * Real.exp (r : ℝ) * (k.factorial : ℝ)) *
      (poissonPMFVal r i * poissonPMFVal r m) =
    (((n.factorial : ℝ) * (k.factorial : ℝ)) /
      ((i.factorial : ℝ) * (m.factorial : ℝ))) * poissonPMFVal r n
  simp only [poissonPMFVal]
  rw [inv_eq_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_div_comm,
    div_mul_div_comm, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  calc ((1 * Real.exp (r : ℝ) * (k.factorial : ℝ)) *
          ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ i) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ m))) *
        (((i.factorial : ℝ) * (m.factorial : ℝ)) * (n.factorial : ℝ))
    _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) * ((r : ℝ) ^ i * (r : ℝ) ^ m) *
          (Real.exp (-(r : ℝ)) * (k.factorial : ℝ) * (i.factorial : ℝ) *
            (m.factorial : ℝ) * (n.factorial : ℝ)) := by ring
    _ = 1 * ((r : ℝ) ^ (k + 1) * (r : ℝ) ^ n) *
          (Real.exp (-(r : ℝ)) * (k.factorial : ℝ) * (i.factorial : ℝ) *
            (m.factorial : ℝ) * (n.factorial : ℝ)) := by
      rw [exp_pos_mul_neg, hpow]
    _ = (((n.factorial : ℝ) * (k.factorial : ℝ)) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n)) *
          ((r : ℝ) ^ (k + 1) * ((i.factorial : ℝ) * (m.factorial : ℝ))) := by ring

private lemma steinQuadBound_le_one {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    steinQuadBound r k ≤ 1 := by
  rw [steinQuadBound_eq_tsum hr k]
  refine Real.tsum_le_of_sum_range_le
    (fun n ↦ mul_nonneg (steinCoeff_nonneg n k) (poissonPMFVal_nonneg r n)) fun N ↦ ?_
  calc ∑ n ∈ Finset.range N, steinCoeff n k * poissonPMFVal r n
    _ ≤ ∑ n ∈ Finset.range N, 1 * poissonPMFVal r n := by
      refine Finset.sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_right ?_ (poissonPMFVal_nonneg r n)
      exact (steinCoeff_le_diag n k).trans (steinCoeff_diag_le_one n)
    _ = ∑ n ∈ Finset.range N, poissonPMFVal r n := by simp
    _ ≤ 1 := sum_range_poissonPMFVal_le_one r N

private lemma one_div_succ_mul_poissonPMFVal {r : ℝ≥0} (hr : 0 < r) (n : ℕ) :
    (1 / ((n : ℝ) + 1)) * poissonPMFVal r n = poissonPMFVal r (n + 1) / (r : ℝ) := by
  have hfac : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  simp only [poissonPMFVal, hfac, pow_succ]
  rw [div_mul_div_comm, div_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

private lemma steinQuadBound_le_rpow {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    steinQuadBound r k ≤ (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [steinQuadBound_eq_tsum hr k]
  refine Real.tsum_le_of_sum_range_le
    (fun n ↦ mul_nonneg (steinCoeff_nonneg n k) (poissonPMFVal_nonneg r n)) fun N ↦ ?_
  set S : ℝ := ∑ n ∈ Finset.range N, steinCoeff n k * poissonPMFVal r n
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun n _ ↦ mul_nonneg (steinCoeff_nonneg n k) (poissonPMFVal_nonneg r n)
  have hcs : S ^ 2 ≤
      (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) * poissonPMFVal r n) *
        ∑ n ∈ Finset.range N, poissonPMFVal r n := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range N)
      (fun n _ ↦ mul_nonneg (by positivity) (poissonPMFVal_nonneg r n))
      (fun n _ ↦ poissonPMFVal_nonneg r n) fun n _ ↦ ?_
    have hle : steinCoeff n k ≤ steinCoeff n n := steinCoeff_le_diag n k
    have hsq_le : (steinCoeff n k) ^ 2 ≤ 1 / ((n : ℝ) + 1) := by
      calc (steinCoeff n k) ^ 2
        _ ≤ (steinCoeff n n) ^ 2 := by
          rw [sq, sq]
          exact mul_le_mul hle hle (steinCoeff_nonneg n k) (steinCoeff_nonneg n n)
        _ ≤ 1 / ((n : ℝ) + 1) := steinCoeff_diag_sq_le n
    calc (steinCoeff n k * poissonPMFVal r n) ^ 2
      _ = (steinCoeff n k) ^ 2 * (poissonPMFVal r n * poissonPMFVal r n) := by ring
      _ ≤ (1 / ((n : ℝ) + 1)) * (poissonPMFVal r n * poissonPMFVal r n) :=
        mul_le_mul_of_nonneg_right hsq_le
          (mul_nonneg (poissonPMFVal_nonneg r n) (poissonPMFVal_nonneg r n))
      _ = ((1 / ((n : ℝ) + 1)) * poissonPMFVal r n) * poissonPMFVal r n := by ring
  have hsum1 : (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) * poissonPMFVal r n) ≤ (r : ℝ)⁻¹ := by
    have hcongr : (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) * poissonPMFVal r n) =
        (∑ n ∈ Finset.range N, poissonPMFVal r (n + 1)) / (r : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun n _ ↦ one_div_succ_mul_poissonPMFVal hr n
    rw [hcongr, ← one_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have htot := sum_range_poissonPMFVal_le_one r (N + 1)
    rw [Finset.sum_range_succ'] at htot
    linarith [poissonPMFVal_nonneg r 0]
  have hsum2 : (∑ n ∈ Finset.range N, poissonPMFVal r n) ≤ 1 :=
    sum_range_poissonPMFVal_le_one r N
  set c : ℝ := (r : ℝ) ^ (-(1 / 2 : ℝ))
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hS_sq : S ^ 2 ≤ c ^ 2 := by
    have hrpow_sq : c ^ 2 = (r : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast c 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r)]
      have hexp : -(1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = -1 := by norm_num
      rw [hexp, Real.rpow_neg_one]
    rw [hrpow_sq]
    calc S ^ 2
      _ ≤ (∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1)) * poissonPMFVal r n) *
            ∑ n ∈ Finset.range N, poissonPMFVal r n := hcs
      _ ≤ (r : ℝ)⁻¹ * 1 :=
        mul_le_mul hsum1 hsum2
          (Finset.sum_nonneg fun n _ ↦ poissonPMFVal_nonneg r n) (by positivity)
      _ = (r : ℝ)⁻¹ := mul_one _
  have hmul : (S + c) * S ≤ (S + c) * c := by
    have hid : (S + c) * c - (S + c) * S = c ^ 2 - S ^ 2 := by ring
    linarith
  exact le_of_mul_le_mul_left hmul (by linarith)

/-- Uniform bound `|f_A(k)| ≤ min(1, r^{-1/2})` on the canonical Chen–Stein solution
`poissonSteinSol` for `r > 0`
(Lemma 4.4 `\label{lem103}`, eq. `(4.2)` `\label{102}`, `SteinIntro.tex:1879-1886`). -/
theorem abs_poissonSteinSol_le {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) (k : ℕ) :
    |poissonSteinSol r A k| ≤ min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) := by
  cases k with
  | zero =>
    simp only [poissonSteinSol, abs_zero]
    exact le_min zero_le_one (Real.rpow_nonneg (by positivity) _)
  | succ m =>
    exact (abs_poissonSteinSol_succ_le_quad r A m).trans
      (le_min (steinQuadBound_le_one hr m) (steinQuadBound_le_rpow hr m))

/-! ### Forward-difference bound `|Δ f_A(k)| ≤ (1 - e^{-r}) / r` -/

private lemma poissonSteinSol_empty (r : ℝ≥0) (m : ℕ) : poissonSteinSol r ∅ m = 0 := by
  cases m with
  | zero => rfl
  | succ _ => simp [poissonSteinSol]

private lemma poissonSteinSol_univ (r : ℝ≥0) (m : ℕ) : poissonSteinSol r Set.univ m = 0 := by
  cases m with
  | zero => rfl
  | succ _ =>
    simp only [poissonSteinSol, Set.univ_inter, probReal_univ, one_mul, sub_self, mul_zero]

private lemma poissonSteinSol_union (r : ℝ≥0) {B₁ B₂ : Set ℕ} (h : Disjoint B₁ B₂) (m : ℕ) :
    poissonSteinSol r (B₁ ∪ B₂) m = poissonSteinSol r B₁ m + poissonSteinSol r B₂ m := by
  cases m with
  | zero => simp [poissonSteinSol]
  | succ k =>
    have hd : Disjoint (B₁ ∩ Set.Iio (k + 1)) (B₂ ∩ Set.Iio (k + 1)) :=
      Set.disjoint_left.mpr fun _ hx₁ hx₂ ↦ Set.disjoint_left.mp h hx₁.1 hx₂.1
    simp only [poissonSteinSol, Set.union_inter_distrib_right]
    rw [measureReal_union hd .of_discrete, measureReal_union h .of_discrete]
    ring

private lemma poissonSteinSol_compl (r : ℝ≥0) (A : Set ℕ) (m : ℕ) :
    poissonSteinSol r Aᶜ m = -poissonSteinSol r A m := by
  have hsum : poissonSteinSol r A m + poissonSteinSol r Aᶜ m = 0 := by
    rw [← poissonSteinSol_union r disjoint_compl_right m, A.union_compl_self,
      poissonSteinSol_univ]
  linarith

private noncomputable def upperFactor (r : ℝ≥0) (m : ℕ) : ℝ :=
  ((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ) *
    (poissonLaw r).real (Set.Ici (m + 1))

private lemma poissonSteinSol_eq_mul_upperFactor (r : ℝ≥0) {B : Set ℕ} (m : ℕ)
    (hB : B ⊆ Set.Iio (m + 1)) :
    poissonSteinSol r B (m + 1) = (poissonLaw r).real B * upperFactor r m := by
  have hinter : B ∩ Set.Iio (m + 1) = B := Set.inter_eq_left.mpr hB
  have hcompl : (poissonLaw r).real (Set.Ici (m + 1)) =
      1 - (poissonLaw r).real (Set.Iio (m + 1)) := by
    rw [← Set.compl_Iio, probReal_compl_eq_one_sub .of_discrete]
  simp only [poissonSteinSol, upperFactor, hinter, hcompl]
  ring

private lemma upperFactor_succ_le {r : ℝ≥0} (hr : 0 < r) (m : ℕ) :
    upperFactor r (m + 1) ≤ upperFactor r m := by
  have hsum_shift : ∀ n : ℕ, Summable (fun l ↦ poissonPMFVal r (l + n)) :=
    fun n ↦ (summable_nat_add_iff n).mpr (summable_poissonPMFVal r)
  have hterm : ∀ (n l : ℕ),
      (((r : ℝ) ^ (n + 1))⁻¹ * Real.exp (r : ℝ) * (n.factorial : ℝ)) *
        poissonPMFVal r (l + (n + 1)) =
      ((r : ℝ) ^ l * (n.factorial : ℝ)) / (((l + (n + 1)).factorial : ℕ) : ℝ) := by
    intro n l
    simp only [poissonPMFVal]
    rw [pow_add (r : ℝ) l (n + 1), inv_eq_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    calc ((1 * Real.exp (r : ℝ) * (n.factorial : ℝ)) *
            (Real.exp (-(r : ℝ)) * ((r : ℝ) ^ l * (r : ℝ) ^ (n + 1)))) *
          (((l + (n + 1)).factorial : ℕ) : ℝ)
      _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) *
            (((r : ℝ) ^ l * (n.factorial : ℝ)) *
              ((r : ℝ) ^ (n + 1) * (((l + (n + 1)).factorial : ℕ) : ℝ))) := by ring
      _ = 1 * (((r : ℝ) ^ l * (n.factorial : ℝ)) *
            ((r : ℝ) ^ (n + 1) * (((l + (n + 1)).factorial : ℕ) : ℝ))) := by
        rw [exp_pos_mul_neg]
      _ = ((r : ℝ) ^ l * (n.factorial : ℝ)) *
            ((r : ℝ) ^ (n + 1) * (((l + (n + 1)).factorial : ℕ) : ℝ)) := one_mul _
  rw [upperFactor, upperFactor, poissonLaw_real_Ici r (m + 2), poissonLaw_real_Ici r (m + 1),
    ← tsum_mul_left, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun l ↦ ?_)
    ((hsum_shift (m + 2)).mul_left _) ((hsum_shift (m + 1)).mul_left _)
  rw [hterm (m + 1) l, hterm m l]
  set q : ℕ := l + (m + 1)
  have hlm : l + (m + 2) = q + 1 := by omega
  have hmq : m ≤ q := by omega
  rw [hlm, Nat.factorial_succ m, Nat.factorial_succ q]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hle_mq : (m : ℝ) + 1 ≤ (q : ℝ) + 1 := by
    have : (m : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr hmq
    linarith
  have hfac_nn : 0 ≤ (r : ℝ) ^ l * (m.factorial : ℝ) * (q.factorial : ℝ) := by positivity
  calc ((r : ℝ) ^ l * (((m : ℝ) + 1) * (m.factorial : ℝ))) * (q.factorial : ℝ)
    _ = ((m : ℝ) + 1) * ((r : ℝ) ^ l * (m.factorial : ℝ) * (q.factorial : ℝ)) := by ring
    _ ≤ ((q : ℝ) + 1) * ((r : ℝ) ^ l * (m.factorial : ℝ) * (q.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hle_mq hfac_nn
    _ = ((r : ℝ) ^ l * (m.factorial : ℝ)) * (((q : ℝ) + 1) * (q.factorial : ℝ)) := by ring

private lemma fwdDiff_poissonSteinSol_nonpos_of_subset_Iio {r : ℝ≥0} (hr : 0 < r)
    {B : Set ℕ} {k : ℕ} (hB : B ⊆ Set.Iio k) :
    fwdDiff 1 (poissonSteinSol r B) k ≤ 0 := by
  cases k with
  | zero =>
    have hempty : B = ∅ :=
      Set.ext fun x ↦ ⟨fun hx ↦ absurd (Set.mem_Iio.mp (hB hx)) (Nat.not_lt_zero x), False.elim⟩
    simp [fwdDiff, hempty, poissonSteinSol_empty]
  | succ m =>
    have hB2 : B ⊆ Set.Iio (m + 2) := fun x hx ↦ by
      have hx1 : x < m + 1 := Set.mem_Iio.mp (hB hx)
      exact Set.mem_Iio.mpr (by omega)
    change poissonSteinSol r B (m + 2) - poissonSteinSol r B (m + 1) ≤ 0
    rw [poissonSteinSol_eq_mul_upperFactor r (m + 1) hB2,
      poissonSteinSol_eq_mul_upperFactor r m hB]
    have hle := mul_le_mul_of_nonneg_left (upperFactor_succ_le hr m)
      (measureReal_nonneg (μ := poissonLaw r) (s := B))
    linarith

private noncomputable def lowerFactor (r : ℝ≥0) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
      ((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ) *
        (poissonLaw r).real (Set.Iio (m + 1))

private lemma poissonSteinSol_eq_neg_mul_lowerFactor (r : ℝ≥0) {B : Set ℕ} (n : ℕ)
    (hB : B ∩ Set.Iio n = ∅) :
    poissonSteinSol r B n = -(poissonLaw r).real B * lowerFactor r n := by
  cases n with
  | zero => simp [poissonSteinSol, lowerFactor]
  | succ _ =>
    simp only [poissonSteinSol, lowerFactor, hB, measureReal_empty]
    ring

private lemma lowerFactor_le_succ {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    lowerFactor r k ≤ lowerFactor r (k + 1) := by
  cases k with
  | zero =>
    rw [lowerFactor, lowerFactor]
    positivity
  | succ m =>
    rw [lowerFactor, lowerFactor, poissonLaw_real_Iio r (m + 1), poissonLaw_real_Iio r (m + 2),
      Finset.sum_range_succ' (poissonPMFVal r) (m + 1), mul_add, Finset.mul_sum, Finset.mul_sum]
    have h0_nonneg : 0 ≤ (((r : ℝ) ^ (m + 2))⁻¹ * Real.exp (r : ℝ) *
        (((m + 1).factorial : ℕ) : ℝ)) * poissonPMFVal r 0 :=
      mul_nonneg (by positivity) (poissonPMFVal_nonneg r 0)
    suffices hsum_le :
        (∑ i ∈ Finset.range (m + 1),
          (((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ)) * poissonPMFVal r i) ≤
        ∑ i ∈ Finset.range (m + 1),
          (((r : ℝ) ^ (m + 2))⁻¹ * Real.exp (r : ℝ) * (((m + 1).factorial : ℕ) : ℝ)) *
            poissonPMFVal r (i + 1) by
      linarith
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hi_le : i ≤ m := by
      rw [Finset.mem_range] at hi
      omega
    simp only [poissonPMFVal]
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ (r : ℝ) (m + 1), pow_succ (r : ℝ) i,
      Nat.factorial_succ m, Nat.factorial_succ i]
    push_cast
    rw [inv_eq_one_div, inv_eq_one_div,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_div_comm,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have him_real : (i : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (i : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hi_le
      linarith
    set W : ℝ := Real.exp (r : ℝ) * Real.exp (-(r : ℝ)) * (m.factorial : ℝ) * (i.factorial : ℝ) *
      (r : ℝ) ^ i * (r : ℝ) ^ (m + 1) * (r : ℝ)
    have hW : 0 ≤ W := by positivity
    calc ((1 * Real.exp (r : ℝ) * (m.factorial : ℝ)) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ i)) *
          (((r : ℝ) ^ (m + 1) * (r : ℝ)) * (((i : ℝ) + 1) * (i.factorial : ℝ)))
      _ = ((i : ℝ) + 1) * W := by ring
      _ ≤ ((m : ℝ) + 1) * W := mul_le_mul_of_nonneg_right him_real hW
      _ = ((1 * Real.exp (r : ℝ) * (((m : ℝ) + 1) * (m.factorial : ℝ))) *
            (Real.exp (-(r : ℝ)) * ((r : ℝ) ^ i * (r : ℝ)))) *
          ((r : ℝ) ^ (m + 1) * (i.factorial : ℝ)) := by ring

private lemma fwdDiff_poissonSteinSol_nonpos_of_subset_Ici {r : ℝ≥0} (hr : 0 < r)
    {B : Set ℕ} {k : ℕ} (hB : B ⊆ Set.Ici (k + 1)) :
    fwdDiff 1 (poissonSteinSol r B) k ≤ 0 := by
  have hdisj0 : B ∩ Set.Iio k = ∅ :=
    Set.ext fun x ↦ ⟨fun ⟨hxB, hxk⟩ ↦ by
      have hge : k + 1 ≤ x := Set.mem_Ici.mp (hB hxB)
      have hlt : x < k := Set.mem_Iio.mp hxk
      omega, False.elim⟩
  have hdisj1 : B ∩ Set.Iio (k + 1) = ∅ :=
    Set.ext fun x ↦ ⟨fun ⟨hxB, hxk⟩ ↦ by
      have hge : k + 1 ≤ x := Set.mem_Ici.mp (hB hxB)
      have hlt : x < k + 1 := Set.mem_Iio.mp hxk
      omega, False.elim⟩
  change poissonSteinSol r B (k + 1) - poissonSteinSol r B k ≤ 0
  rw [poissonSteinSol_eq_neg_mul_lowerFactor r (k + 1) hdisj1,
    poissonSteinSol_eq_neg_mul_lowerFactor r k hdisj0]
  have hle := mul_le_mul_of_nonneg_left (lowerFactor_le_succ hr k)
    (measureReal_nonneg (μ := poissonLaw r) (s := B))
  linarith

private lemma fwdDiff_poissonSteinSol_singleton_le {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    fwdDiff 1 (poissonSteinSol r {k}) k ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ) := by
  cases k with
  | zero =>
    have hIio1 : ({0} : Set ℕ) ∩ Set.Iio 1 = {0} :=
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Set.mem_Iio.mpr Nat.zero_lt_one))
    have hsetIio1 : (Set.Iio 1 : Set ℕ) = {0} := by
      ext x
      simp only [Set.mem_Iio, Set.mem_singleton_iff]
      omega
    have h1 : poissonSteinSol r {0} 1 = (1 - Real.exp (-(r : ℝ))) / (r : ℝ) := by
      rw [poissonSteinSol, hIio1, hsetIio1, poissonLaw_real_singleton_eq, poissonPMFVal_zero,
        pow_one, Nat.factorial_zero, Nat.cast_one, mul_one, inv_eq_one_div,
        div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      calc ((1 * Real.exp (r : ℝ)) *
              (Real.exp (-(r : ℝ)) - Real.exp (-(r : ℝ)) * Real.exp (-(r : ℝ)))) * (r : ℝ)
        _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) *
              ((1 - Real.exp (-(r : ℝ))) * (r : ℝ)) := by ring
        _ = 1 * ((1 - Real.exp (-(r : ℝ))) * (r : ℝ)) := by rw [exp_pos_mul_neg]
        _ = (1 - Real.exp (-(r : ℝ))) * (r : ℝ) := one_mul _
    change poissonSteinSol r {0} 1 - poissonSteinSol r {0} 0 ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ)
    rw [h1, poissonSteinSol]
    linarith
  | succ m =>
    set k : ℕ := m + 1
    have hdisj : ({k} : Set ℕ) ∩ Set.Iio k = ∅ :=
      Set.ext fun x ↦ ⟨fun ⟨hxk, hxl⟩ ↦ by
        have h1 : x = k := Set.mem_singleton_iff.mp hxk
        have h2 : x < k := Set.mem_Iio.mp hxl
        omega, False.elim⟩
    have hsub : ({k} : Set ℕ) ⊆ Set.Iio (k + 1) :=
      Set.singleton_subset_iff.mpr (Set.mem_Iio.mpr (Nat.lt_succ_self k))
    have hsol_k : poissonSteinSol r {k} k = -((poissonLaw r).real (Set.Iio k) / (k : ℝ)) := by
      rw [poissonSteinSol_eq_neg_mul_lowerFactor r k hdisj, neg_mul]
      congr 1
      rw [poissonLaw_real_singleton_eq, poissonPMFVal]
      change (Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / (k.factorial : ℝ)) *
          (((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ) *
            (poissonLaw r).real (Set.Iio k)) =
        (poissonLaw r).real (Set.Iio k) / (k : ℝ)
      have hk_fac : (k.factorial : ℝ) = (k : ℝ) * (m.factorial : ℝ) := by
        change (((m + 1).factorial : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)
        rw [Nat.factorial_succ, Nat.cast_mul]
      rw [hk_fac, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      calc ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ k) *
              (((r : ℝ) ^ k)⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ) *
                (poissonLaw r).real (Set.Iio k))) * (k : ℝ)
        _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) *
              ((r : ℝ) ^ k * ((r : ℝ) ^ k)⁻¹) *
              ((poissonLaw r).real (Set.Iio k) * ((k : ℝ) * (m.factorial : ℝ))) := by ring
        _ = 1 * 1 * ((poissonLaw r).real (Set.Iio k) *
              ((k : ℝ) * (m.factorial : ℝ))) := by
          rw [exp_pos_mul_neg, mul_inv_cancel₀ (by positivity)]
        _ = (poissonLaw r).real (Set.Iio k) *
              ((k : ℝ) * (m.factorial : ℝ)) := by ring
    have hsol_k1 :
        poissonSteinSol r {k} (k + 1) = (poissonLaw r).real (Set.Ici (k + 1)) / (r : ℝ) := by
      rw [poissonSteinSol_eq_mul_upperFactor r k hsub, poissonLaw_real_singleton_eq,
        poissonPMFVal, upperFactor, div_mul_eq_mul_div,
        div_eq_div_iff (by positivity) (by positivity)]
      calc ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ k) *
              (((r : ℝ) ^ (k + 1))⁻¹ * Real.exp (r : ℝ) * (k.factorial : ℝ) *
                (poissonLaw r).real (Set.Ici (k + 1)))) * (r : ℝ)
        _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) *
              (((r : ℝ) ^ k * (r : ℝ)) * ((r : ℝ) ^ (k + 1))⁻¹) *
              ((poissonLaw r).real (Set.Ici (k + 1)) * (k.factorial : ℝ)) := by ring
        _ = 1 * 1 * ((poissonLaw r).real (Set.Ici (k + 1)) * (k.factorial : ℝ)) := by
          rw [exp_pos_mul_neg, ← pow_succ (r : ℝ) k, mul_inv_cancel₀ (by positivity)]
        _ = (poissonLaw r).real (Set.Ici (k + 1)) * (k.factorial : ℝ) := by ring
    change poissonSteinSol r {k} (k + 1) - poissonSteinSol r {k} k ≤
      (1 - Real.exp (-(r : ℝ))) / (r : ℝ)
    have hIci : (poissonLaw r).real (Set.Ici (k + 1)) =
        (1 - Real.exp (-(r : ℝ))) - ∑ i ∈ Finset.range k, poissonPMFVal r (i + 1) := by
      rw [← Set.compl_Iio, probReal_compl_eq_one_sub .of_discrete,
        poissonLaw_real_Iio r (k + 1), Finset.sum_range_succ', poissonPMFVal_zero]
      ring
    have hrew : poissonSteinSol r {k} (k + 1) - poissonSteinSol r {k} k =
        (1 - Real.exp (-(r : ℝ))) / (r : ℝ) -
          (∑ i ∈ Finset.range k, poissonPMFVal r (i + 1)) / (r : ℝ) +
          (poissonLaw r).real (Set.Iio k) / (k : ℝ) := by
      rw [hsol_k1, hsol_k, hIci, sub_div]
      ring
    rw [hrew]
    suffices hcmp :
        (poissonLaw r).real (Set.Iio k) / (k : ℝ) ≤
          (∑ i ∈ Finset.range k, poissonPMFVal r (i + 1)) / (r : ℝ) by
      linarith
    rw [poissonLaw_real_Iio r k, Finset.sum_div, Finset.sum_div]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hi_le : i + 1 ≤ k := by
      rw [Finset.mem_range] at hi
      omega
    simp only [poissonPMFVal]
    rw [div_div, div_div, pow_succ (r : ℝ) i, Nat.factorial_succ i]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hik : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hi_le
    set V : ℝ := Real.exp (-(r : ℝ)) * (r : ℝ) ^ i * (i.factorial : ℝ) * (r : ℝ)
    have hV : 0 ≤ V := by positivity
    calc (Real.exp (-(r : ℝ)) * (r : ℝ) ^ i) *
          ((((i : ℝ) + 1) * (i.factorial : ℝ)) * (r : ℝ))
      _ = ((i : ℝ) + 1) * V := by ring
      _ ≤ (k : ℝ) * V := mul_le_mul_of_nonneg_right hik hV
      _ = (Real.exp (-(r : ℝ)) * ((r : ℝ) ^ i * (r : ℝ))) *
            ((i.factorial : ℝ) * (k : ℝ)) := by ring

private lemma fwdDiff_poissonSteinSol_inter_singleton_le {r : ℝ≥0} (hr : 0 < r)
    (A : Set ℕ) (k : ℕ) :
    fwdDiff 1 (poissonSteinSol r (A ∩ {k})) k ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ) := by
  by_cases hkA : k ∈ A
  · have heq : A ∩ {k} = {k} :=
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hkA)
    rw [heq]
    exact fwdDiff_poissonSteinSol_singleton_le hr k
  · have heq : A ∩ {k} = ∅ :=
      Set.ext fun _ ↦ ⟨fun ⟨hxA, hxk⟩ ↦ hkA (Set.mem_singleton_iff.mp hxk ▸ hxA), False.elim⟩
    rw [heq]
    simp only [fwdDiff, poissonSteinSol_empty, sub_zero]
    have hr' : (0 : ℝ) < r := by positivity
    have hexp : Real.exp (-(r : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact div_nonneg (by linarith) hr'.le

private lemma fwdDiff_poissonSteinSol_le {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) (k : ℕ) :
    fwdDiff 1 (poissonSteinSol r A) k ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ) := by
  set A₁ : Set ℕ := A ∩ Set.Iio k
  set A₂ : Set ℕ := A ∩ {k}
  set A₃ : Set ℕ := A ∩ Set.Ici (k + 1)
  have hA : A = (A₁ ∪ A₂) ∪ A₃ := by
    ext x
    constructor
    · intro hx
      by_cases h1 : x < k
      · exact Or.inl (Or.inl ⟨hx, Set.mem_Iio.mpr h1⟩)
      · by_cases h2 : x = k
        · exact Or.inl (Or.inr ⟨hx, Set.mem_singleton_iff.mpr h2⟩)
        · exact Or.inr ⟨hx, Set.mem_Ici.mpr (by omega)⟩
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  have hd12 : Disjoint A₁ A₂ :=
    Set.disjoint_left.mpr fun x hx1 hx2 ↦ by
      have h1 : x < k := Set.mem_Iio.mp hx1.2
      have h2 : x = k := Set.mem_singleton_iff.mp hx2.2
      omega
  have hd123 : Disjoint (A₁ ∪ A₂) A₃ :=
    Set.disjoint_left.mpr fun x hx12 hx3 ↦ by
      have h3 : k + 1 ≤ x := Set.mem_Ici.mp hx3.2
      rcases hx12 with hx1 | hx2
      · have h1 : x < k := Set.mem_Iio.mp hx1.2
        omega
      · have h2 : x = k := Set.mem_singleton_iff.mp hx2.2
        omega
  have hsol : ∀ m : ℕ,
      poissonSteinSol r A m =
        poissonSteinSol r A₁ m + poissonSteinSol r A₂ m + poissonSteinSol r A₃ m := by
    intro m
    rw [hA, poissonSteinSol_union r hd123 m, poissonSteinSol_union r hd12 m]
  have hdiff :
      fwdDiff 1 (poissonSteinSol r A) k =
        fwdDiff 1 (poissonSteinSol r A₁) k +
          fwdDiff 1 (poissonSteinSol r A₂) k +
          fwdDiff 1 (poissonSteinSol r A₃) k := by
    simp only [fwdDiff, hsol]
    ring
  have h1 := fwdDiff_poissonSteinSol_nonpos_of_subset_Iio hr
    (B := A₁) (Set.inter_subset_right)
  have h2 := fwdDiff_poissonSteinSol_inter_singleton_le hr A k
  have h3 := fwdDiff_poissonSteinSol_nonpos_of_subset_Ici hr
    (B := A₃) (Set.inter_subset_right)
  rw [hdiff]
  linarith

/-- Uniform forward-difference bound `|Δ f_A(k)| ≤ (1 - e^{-r}) / r` on the canonical Chen–Stein
solution `poissonSteinSol` for `r > 0`
(Lemma 4.4 `\label{lem103}`, eq. `(4.2)` `\label{102}`, `SteinIntro.tex:1879-1908`). -/
theorem abs_fwdDiff_poissonSteinSol_le {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) (k : ℕ) :
    |fwdDiff 1 (poissonSteinSol r A) k| ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ) := by
  have hpos := fwdDiff_poissonSteinSol_le hr A k
  have hneg := fwdDiff_poissonSteinSol_le hr Aᶜ k
  have hcompl_diff :
      fwdDiff 1 (poissonSteinSol r Aᶜ) k = -fwdDiff 1 (poissonSteinSol r A) k := by
    simp only [fwdDiff, poissonSteinSol_compl]
    ring
  rw [hcompl_diff] at hneg
  exact abs_le.mpr ⟨by linarith, hpos⟩

end SteinMethod
