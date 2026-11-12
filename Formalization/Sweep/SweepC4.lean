/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Poisson.SteinBounds
import Formalization.PoissonDep.HeadRuns

/-!
# SWEEP-C Section 4 Library Proofs (`Formalization.Sweep.SweepC4`)

Library theorems for the approved Section 4 entries in `docs/tracks/SWEEP-C.md` (`SC-1`–`SC-7`):

* `sec4_poissonSteinSol_pointMass_corrected_proof`: sign and forward-difference bounds for the
  point-mass Chen–Stein solutions $f_j = f_{\{j\}}$ (`SteinIntro.tex:1889-1899`;
  `ISSUE-4.4-PROSE`, `SC-2`).
* `not_sec4_fwdDiff_f0_neg_printed_proof`: refutation of `"Δf₀(k) < 0"` at $k = 0$
  (`SteinIntro.tex:1899`; `ISSUE-4.4-PROSE`, `SC-2`).
* `sec4_2_1_headRun_declumping_proof`: combinatorial de-clumping identity equating
  `headRunCount k y` with the number of maximal contiguous runs of ones of length at least $k$
  (`SteinIntro.tex:2006-2023`; `SC-5`).
-/

open MeasureTheory Set
open scoped NNReal

namespace SteinMethod

/-! ### Section 4.0: Point-Mass Chen–Stein Solution Properties (`D-C3`, `SC-2`) -/

private noncomputable def pmfVal (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)

private lemma pmfVal_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ pmfVal r n := by
  unfold pmfVal; positivity

private lemma pmfVal_pos {r : ℝ≥0} (hr : 0 < r) (n : ℕ) : 0 < pmfVal r n := by
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  unfold pmfVal; positivity

private lemma summable_pmfVal (r : ℝ≥0) : Summable (pmfVal r) :=
  (ProbabilityTheory.hasSum_one_poissonMeasure r).summable

private lemma tsum_pmfVal (r : ℝ≥0) : ∑' n, pmfVal r n = 1 :=
  (ProbabilityTheory.hasSum_one_poissonMeasure r).tsum_eq

private lemma poissonLaw_real_singleton (r : ℝ≥0) (n : ℕ) :
    (poissonLaw r).real {n} = pmfVal r n := by
  simpa [pmfVal] using ProbabilityTheory.poissonMeasure_real_singleton r n

private lemma poissonLaw_real_Iio_eq (r : ℝ≥0) (m : ℕ) :
    (poissonLaw r).real (Set.Iio m) = ∑ i ∈ Finset.range m, pmfVal r i := by
  rw [← Finset.coe_range m, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun i _ ↦ poissonLaw_real_singleton r i

private lemma poissonLaw_real_Ici_eq (r : ℝ≥0) (m : ℕ) :
    (poissonLaw r).real (Set.Ici m) = ∑' l : ℕ, pmfVal r (l + m) := by
  have hsplit : (∑ i ∈ Finset.range m, pmfVal r i) + ∑' l, pmfVal r (l + m) = 1 := by
    rw [Summable.sum_add_tsum_nat_add m (summable_pmfVal r), tsum_pmfVal]
  rw [← Set.compl_Iio, probReal_compl_eq_one_sub .of_discrete, poissonLaw_real_Iio_eq]
  linarith

private lemma exp_mul_exp_neg (x : ℝ) : Real.exp x * Real.exp (-x) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

private noncomputable def upperFac (r : ℝ≥0) (m : ℕ) : ℝ :=
  ((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ) *
    (poissonLaw r).real (Set.Ici (m + 1))

private noncomputable def lowerFac (r : ℝ≥0) : ℕ → ℝ
  | 0 => 0
  | m + 1 =>
      ((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ) *
        (poissonLaw r).real (Set.Iio (m + 1))

private lemma sol_singleton_eq_neg_lowerFac (r : ℝ≥0) {j k : ℕ} (hkj : k ≤ j) :
    poissonSteinSol r {j} k = -(poissonLaw r).real {j} * lowerFac r k := by
  cases k with
  | zero => simp [poissonSteinSol, lowerFac]
  | succ m =>
    have hempty : ({j} : Set ℕ) ∩ Set.Iio (m + 1) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_Iio,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl; omega
    simp only [poissonSteinSol, lowerFac, hempty, measureReal_empty]
    ring

private lemma sol_singleton_eq_upperFac (r : ℝ≥0) {j m : ℕ} (hjm : j ≤ m) :
    poissonSteinSol r {j} (m + 1) = (poissonLaw r).real {j} * upperFac r m := by
  have hinter : ({j} : Set ℕ) ∩ Set.Iio (m + 1) = {j} :=
    Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (Set.mem_Iio.mpr (by omega)))
  have hcompl : (poissonLaw r).real (Set.Ici (m + 1)) =
      1 - (poissonLaw r).real (Set.Iio (m + 1)) := by
    rw [← Set.compl_Iio, probReal_compl_eq_one_sub .of_discrete]
  simp only [poissonSteinSol, upperFac, hinter, hcompl]
  ring

private lemma upperFac_term_eq {r : ℝ≥0} (hr : 0 < r) (n l : ℕ) :
    (((r : ℝ) ^ (n + 1))⁻¹ * Real.exp (r : ℝ) * (n.factorial : ℝ)) * pmfVal r (l + (n + 1)) =
      ((r : ℝ) ^ l * (n.factorial : ℝ)) / (((l + (n + 1)).factorial : ℕ) : ℝ) := by
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  simp only [pmfVal]
  rw [pow_add (r : ℝ) l (n + 1), inv_eq_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  calc ((1 * Real.exp (r : ℝ) * (n.factorial : ℝ)) *
          (Real.exp (-(r : ℝ)) * ((r : ℝ) ^ l * (r : ℝ) ^ (n + 1)))) *
        (((l + (n + 1)).factorial : ℕ) : ℝ)
    _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) *
          (((r : ℝ) ^ l * (n.factorial : ℝ)) *
            ((r : ℝ) ^ (n + 1) * (((l + (n + 1)).factorial : ℕ) : ℝ))) := by ring
    _ = ((r : ℝ) ^ l * (n.factorial : ℝ)) *
          ((r : ℝ) ^ (n + 1) * (((l + (n + 1)).factorial : ℕ) : ℝ)) := by
      rw [exp_mul_exp_neg, one_mul]

private lemma upperFac_succ_lt {r : ℝ≥0} (hr : 0 < r) (m : ℕ) :
    upperFac r (m + 1) < upperFac r m := by
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hsum_shift : ∀ n : ℕ, Summable (fun l ↦
      (((r : ℝ) ^ (n + 1))⁻¹ * Real.exp (r : ℝ) * (n.factorial : ℝ)) *
        pmfVal r (l + (n + 1))) :=
    fun n ↦ ((summable_nat_add_iff (n + 1)).mpr (summable_pmfVal r)).mul_left _
  rw [upperFac, upperFac, poissonLaw_real_Ici_eq r (m + 2), poissonLaw_real_Ici_eq r (m + 1),
    ← tsum_mul_left, ← tsum_mul_left,
    (hsum_shift (m + 1)).tsum_eq_zero_add, (hsum_shift m).tsum_eq_zero_add]
  have h0_lt : (((r : ℝ) ^ (m + 2))⁻¹ * Real.exp (r : ℝ) * (((m + 1).factorial : ℕ) : ℝ)) *
        pmfVal r (0 + (m + 2)) <
      (((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ)) *
        pmfVal r (0 + (m + 1)) := by
    rw [upperFac_term_eq hr (m + 1) 0, upperFac_term_eq hr m 0]
    simp only [zero_add, pow_zero, one_mul]
    rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
    push_cast
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    set F : ℝ := (m.factorial : ℝ) * (((m : ℝ) + 1) * (m.factorial : ℝ))
    have hF : 0 < F := by positivity
    have h1 : ((m : ℝ) + 1) * (m.factorial : ℝ) * (((m : ℝ) + 1) * (m.factorial : ℝ)) =
        ((m : ℝ) + 1) * F := by ring
    have h2 : (m.factorial : ℝ) * (((m : ℝ) + 1 + 1) * (((m : ℝ) + 1) * (m.factorial : ℝ))) =
        ((m : ℝ) + 2) * F := by ring
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right (by linarith) hF
  have htail_le : (∑' l : ℕ, (((r : ℝ) ^ (m + 2))⁻¹ * Real.exp (r : ℝ) *
        (((m + 1).factorial : ℕ) : ℝ)) * pmfVal r (l + 1 + (m + 2))) ≤
      ∑' l : ℕ, (((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ)) *
        pmfVal r (l + 1 + (m + 1)) := by
    refine Summable.tsum_le_tsum (fun l ↦ ?_)
      ((summable_nat_add_iff 1).mpr (hsum_shift (m + 1)))
      ((summable_nat_add_iff 1).mpr (hsum_shift m))
    rw [upperFac_term_eq hr (m + 1) (l + 1), upperFac_term_eq hr m (l + 1)]
    set q : ℕ := l + 1 + (m + 1)
    have hlm : l + 1 + (m + 2) = q + 1 := by omega
    have hmq : m ≤ q := by omega
    rw [hlm, Nat.factorial_succ m, Nat.factorial_succ q]
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hle_mq : (m : ℝ) + 1 ≤ (q : ℝ) + 1 := by
      have : (m : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr hmq
      linarith
    have hnn : 0 ≤ (r : ℝ) ^ (l + 1) * (m.factorial : ℝ) * (q.factorial : ℝ) := by positivity
    nlinarith
  linarith

private lemma lowerFac_le_succ {r : ℝ≥0} (hr : 0 < r) (k : ℕ) :
    lowerFac r k ≤ lowerFac r (k + 1) := by
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  cases k with
  | zero =>
    rw [lowerFac, lowerFac]
    exact mul_nonneg (by positivity) measureReal_nonneg
  | succ m =>
    rw [lowerFac, lowerFac, poissonLaw_real_Iio_eq r (m + 1), poissonLaw_real_Iio_eq r (m + 2),
      Finset.sum_range_succ' (pmfVal r) (m + 1), mul_add, Finset.mul_sum, Finset.mul_sum]
    have h0_nn : 0 ≤ (((r : ℝ) ^ (m + 2))⁻¹ * Real.exp (r : ℝ) *
        (((m + 1).factorial : ℕ) : ℝ)) * pmfVal r 0 :=
      mul_nonneg (by positivity) (pmfVal_nonneg r 0)
    suffices hsum :
        (∑ i ∈ Finset.range (m + 1),
          (((r : ℝ) ^ (m + 1))⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ)) * pmfVal r i) ≤
        ∑ i ∈ Finset.range (m + 1),
          (((r : ℝ) ^ (m + 2))⁻¹ * Real.exp (r : ℝ) * (((m + 1).factorial : ℕ) : ℝ)) *
            pmfVal r (i + 1) by
      linarith
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [pmfVal]
    rw [show m + 2 = (m + 1) + 1 from rfl, pow_succ (r : ℝ) (m + 1), pow_succ (r : ℝ) i,
      Nat.factorial_succ m, Nat.factorial_succ i]
    push_cast
    rw [inv_eq_one_div, inv_eq_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_div_comm,
      div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have him : (i : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hi_le
    set W : ℝ := Real.exp (r : ℝ) * Real.exp (-(r : ℝ)) * (m.factorial : ℝ) * (i.factorial : ℝ) *
      (r : ℝ) ^ i * (r : ℝ) ^ (m + 1) * (r : ℝ)
    have hW : 0 ≤ W := by positivity
    calc ((1 * Real.exp (r : ℝ) * (m.factorial : ℝ)) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ i)) *
          (((r : ℝ) ^ (m + 1) * (r : ℝ)) * (((i : ℝ) + 1) * (i.factorial : ℝ)))
      _ = ((i : ℝ) + 1) * W := by ring
      _ ≤ ((m : ℝ) + 1) * W := mul_le_mul_of_nonneg_right him hW
      _ = ((1 * Real.exp (r : ℝ) * (((m : ℝ) + 1) * (m.factorial : ℝ))) *
            (Real.exp (-(r : ℝ)) * ((r : ℝ) ^ i * (r : ℝ)))) *
          ((r : ℝ) ^ (m + 1) * (i.factorial : ℝ)) := by ring

private lemma fwdDiff_sol_singleton_zero_at_zero {r : ℝ≥0} (hr : 0 < r) :
    fwdDiff 1 (poissonSteinSol r {0}) 0 = (1 - Real.exp (-(r : ℝ))) / (r : ℝ) := by
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hIio1 : (Set.Iio 1 : Set ℕ) = {0} := by
    ext x; simp only [Set.mem_Iio, Set.mem_singleton_iff]; omega
  have hinter : ({0} : Set ℕ) ∩ Set.Iio 1 = {0} := by rw [hIio1, Set.inter_self]
  change poissonSteinSol r {0} 1 - poissonSteinSol r {0} 0 = _
  rw [poissonSteinSol, poissonSteinSol, sub_zero, hinter, hIio1,
    poissonLaw_real_singleton r 0]
  simp only [pmfVal, zero_add, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
    pow_one]
  rw [inv_eq_one_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hr'.ne' hr'.ne']
  calc (1 * Real.exp (r : ℝ) * (Real.exp (-(r : ℝ)) -
          Real.exp (-(r : ℝ)) * Real.exp (-(r : ℝ)))) * (r : ℝ)
    _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) *
          ((1 - Real.exp (-(r : ℝ))) * (r : ℝ)) := by ring
    _ = (1 - Real.exp (-(r : ℝ))) * (r : ℝ) := by rw [exp_mul_exp_neg, one_mul]

private lemma fwdDiff_sol_singleton_diag_le_inv {r : ℝ≥0} (hr : 0 < r) {j : ℕ} (hj : 1 ≤ j) :
    fwdDiff 1 (poissonSteinSol r {j}) j ≤ (j : ℝ)⁻¹ := by
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  set j := m + 1
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos m)
  have hsol_j : poissonSteinSol r {j} j = -((poissonLaw r).real (Set.Iio j) / (j : ℝ)) := by
    rw [sol_singleton_eq_neg_lowerFac r le_rfl, poissonLaw_real_singleton, pmfVal, lowerFac]
    have hj_fac : (j.factorial : ℝ) = (j : ℝ) * (m.factorial : ℝ) := by
      change (((m + 1).factorial : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ)
      rw [Nat.factorial_succ, Nat.cast_mul]
    rw [neg_mul, neg_inj, hj_fac, div_mul_eq_mul_div,
      div_eq_div_iff (by positivity) hj_pos.ne']
    calc ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ j) *
            (((r : ℝ) ^ j)⁻¹ * Real.exp (r : ℝ) * (m.factorial : ℝ) *
              (poissonLaw r).real (Set.Iio j))) * (j : ℝ)
      _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) * ((r : ℝ) ^ j * ((r : ℝ) ^ j)⁻¹) *
            ((poissonLaw r).real (Set.Iio j) * ((j : ℝ) * (m.factorial : ℝ))) := by ring
      _ = (poissonLaw r).real (Set.Iio j) * ((j : ℝ) * (m.factorial : ℝ)) := by
        rw [exp_mul_exp_neg, mul_inv_cancel₀ (by positivity), mul_one, one_mul]
  have hsol_j1 : poissonSteinSol r {j} (j + 1) =
      (poissonLaw r).real (Set.Ici (j + 1)) / (r : ℝ) := by
    rw [sol_singleton_eq_upperFac r le_rfl, poissonLaw_real_singleton, pmfVal, upperFac,
      div_mul_eq_mul_div, div_eq_div_iff (by positivity) hr'.ne']
    calc ((Real.exp (-(r : ℝ)) * (r : ℝ) ^ j) *
            (((r : ℝ) ^ (j + 1))⁻¹ * Real.exp (r : ℝ) * (j.factorial : ℝ) *
              (poissonLaw r).real (Set.Ici (j + 1)))) * (r : ℝ)
      _ = (Real.exp (r : ℝ) * Real.exp (-(r : ℝ))) *
            (((r : ℝ) ^ j * (r : ℝ)) * ((r : ℝ) ^ (j + 1))⁻¹) *
            ((poissonLaw r).real (Set.Ici (j + 1)) * (j.factorial : ℝ)) := by ring
      _ = (poissonLaw r).real (Set.Ici (j + 1)) * (j.factorial : ℝ) := by
        rw [exp_mul_exp_neg, ← pow_succ (r : ℝ) j, mul_inv_cancel₀ (by positivity),
          mul_one, one_mul]
  have hpart : (poissonLaw r).real (Set.Iio j) + (poissonLaw r).real (Set.Ici j) = 1 := by
    rw [← Set.compl_Iio, probReal_compl_eq_one_sub .of_discrete]; ring
  have htail_cmp : (j : ℝ) * (poissonLaw r).real (Set.Ici (j + 1)) ≤
      (r : ℝ) * (poissonLaw r).real (Set.Ici j) := by
    rw [poissonLaw_real_Ici_eq r (j + 1), poissonLaw_real_Ici_eq r j, ← tsum_mul_left,
      ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun l ↦ ?_)
      (((summable_nat_add_iff (j + 1)).mpr (summable_pmfVal r)).mul_left _)
      (((summable_nat_add_iff j).mpr (summable_pmfVal r)).mul_left _)
    have hrec : ((l + j + 1 : ℕ) : ℝ) * pmfVal r (l + (j + 1)) = (r : ℝ) * pmfVal r (l + j) := by
      simp only [pmfVal]
      rw [show l + (j + 1) = (l + j) + 1 by omega, pow_succ (r : ℝ) (l + j),
        Nat.factorial_succ (l + j)]
      push_cast
      have hne : ((l + j : ℝ) + 1) ≠ 0 := by positivity
      field_simp [hne]
    have hle : (j : ℝ) ≤ ((l + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ l + j + 1)
    calc (j : ℝ) * pmfVal r (l + (j + 1))
      _ ≤ ((l + j + 1 : ℕ) : ℝ) * pmfVal r (l + (j + 1)) :=
        mul_le_mul_of_nonneg_right hle (pmfVal_nonneg r _)
      _ = (r : ℝ) * pmfVal r (l + j) := hrec
  have hdiv_le : (poissonLaw r).real (Set.Ici (j + 1)) / (r : ℝ) ≤
      (poissonLaw r).real (Set.Ici j) / (j : ℝ) := by
    rw [div_le_div_iff₀ hr' hj_pos]
    linarith
  change poissonSteinSol r {j} (j + 1) - poissonSteinSol r {j} j ≤ (j : ℝ)⁻¹
  rw [hsol_j1, hsol_j, sub_neg_eq_add, inv_eq_one_div]
  calc (poissonLaw r).real (Set.Ici (j + 1)) / (r : ℝ) +
          (poissonLaw r).real (Set.Iio j) / (j : ℝ)
    _ ≤ (poissonLaw r).real (Set.Ici j) / (j : ℝ) +
          (poissonLaw r).real (Set.Iio j) / (j : ℝ) := add_le_add_left hdiv_le _
    _ = ((poissonLaw r).real (Set.Iio j) + (poissonLaw r).real (Set.Ici j)) / (j : ℝ) := by ring
    _ = 1 / (j : ℝ) := by rw [hpart]

/-- Corrected point-mass Chen–Stein solution properties (`SteinIntro.tex:1889-1899`;
`ISSUE-4.4-PROSE`, `SC-2`): for $\lambda > 0$,
(1) for $j \ge 1$, $f_j = \mathrm{poissonSteinSol}\,r\,\{j\}$ satisfies $f_j(k) \le 0$ for
$k \le j$, $f_j(k) \ge 0$ for $k > j$, $\Delta f_j(k) \le 0$ for $k \ne j$, $\Delta f_j(j) \ge 0$,
and $\Delta f_j(j) \le \min\{j^{-1}, (1 - e^{-\lambda})/\lambda\}$;
(2) for $j = 0$, $\Delta f_0(0) = (1 - e^{-\lambda})/\lambda > 0$ (correcting `L1899`), while
$\Delta f_0(k) < 0$ for all $k \ge 1$. -/
theorem sec4_poissonSteinSol_pointMass_corrected_proof :
    ∀ {r : ℝ≥0}, 0 < r →
      (∀ {j : ℕ}, 1 ≤ j →
        (∀ k : ℕ, k ≤ j → poissonSteinSol r {j} k ≤ 0) ∧
        (∀ k : ℕ, j < k → 0 ≤ poissonSteinSol r {j} k) ∧
        (∀ k : ℕ, k ≠ j → fwdDiff 1 (poissonSteinSol r {j}) k ≤ 0) ∧
        0 ≤ fwdDiff 1 (poissonSteinSol r {j}) j ∧
        fwdDiff 1 (poissonSteinSol r {j}) j ≤
          min ((j : ℝ)⁻¹) ((1 - Real.exp (-(r : ℝ))) / (r : ℝ))) ∧
      fwdDiff 1 (poissonSteinSol r {0}) 0 = (1 - Real.exp (-(r : ℝ))) / (r : ℝ) ∧
      0 < fwdDiff 1 (poissonSteinSol r {0}) 0 ∧
      (∀ k : ℕ, 1 ≤ k → fwdDiff 1 (poissonSteinSol r {0}) k < 0) := by
  intro r hr
  have hr' : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hgt_neg : ∀ (j k : ℕ), j < k → fwdDiff 1 (poissonSteinSol r {j}) k < 0 := by
    intro j k hjk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hjm : j ≤ m := by omega
    change poissonSteinSol r {j} (m + 2) - poissonSteinSol r {j} (m + 1) < 0
    rw [sol_singleton_eq_upperFac r (by omega : j ≤ m + 1), sol_singleton_eq_upperFac r hjm,
      poissonLaw_real_singleton]
    have hpj : 0 < pmfVal r j := pmfVal_pos hr j
    nlinarith [upperFac_succ_lt hr m]
  refine ⟨fun {j} hj ↦ ?_, fwdDiff_sol_singleton_zero_at_zero hr, ?_, fun k hk ↦ hgt_neg 0 k hk⟩
  · have hle_nonpos : ∀ k : ℕ, k ≤ j → poissonSteinSol r {j} k ≤ 0 := by
      intro k hkj
      rw [sol_singleton_eq_neg_lowerFac r hkj]
      have hlf_nn : 0 ≤ lowerFac r k := by
        cases k with
        | zero => simp [lowerFac]
        | succ m => exact mul_nonneg (by positivity) measureReal_nonneg
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr measureReal_nonneg) hlf_nn
    have hgt_nonneg : ∀ k : ℕ, j < k → 0 ≤ poissonSteinSol r {j} k := by
      intro k hjk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [sol_singleton_eq_upperFac r (by omega : j ≤ m)]
      exact mul_nonneg measureReal_nonneg (mul_nonneg (by positivity) measureReal_nonneg)
    refine ⟨hle_nonpos, hgt_nonneg, ?_, ?_, ?_⟩
    · intro k hkj
      rcases lt_or_gt_of_ne hkj with hlt | hgt
      · change poissonSteinSol r {j} (k + 1) - poissonSteinSol r {j} k ≤ 0
        rw [sol_singleton_eq_neg_lowerFac r (by omega : k + 1 ≤ j),
          sol_singleton_eq_neg_lowerFac r hlt.le]
        have hle := mul_le_mul_of_nonneg_left (lowerFac_le_succ hr k)
          (measureReal_nonneg (μ := poissonLaw r) (s := {j}))
        linarith
      · exact (hgt_neg j k hgt).le
    · change 0 ≤ poissonSteinSol r {j} (j + 1) - poissonSteinSol r {j} j
      linarith [hle_nonpos j le_rfl, hgt_nonneg (j + 1) (Nat.lt_succ_self j)]
    · exact le_min (fwdDiff_sol_singleton_diag_le_inv hr hj)
        ((le_abs_self _).trans (abs_fwdDiff_poissonSteinSol_le hr {j} j))
  · rw [fwdDiff_sol_singleton_zero_at_zero hr]
    have hexp : Real.exp (-(r : ℝ)) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    exact div_pos (by linarith) hr'

/-- Refutation of the literal `SteinIntro.tex:1899` claim that $\Delta f_0(k) < 0$ for all
$k \in \mathbb{N}$ (`ISSUE-4.4-PROSE`, `SC-2`: at $k = 0$,
$\Delta f_0(0) = (1 - e^{-\lambda})/\lambda > 0$). -/
theorem not_sec4_fwdDiff_f0_neg_printed_proof :
    ¬ (∀ {r : ℝ≥0}, 0 < r → ∀ k : ℕ, fwdDiff 1 (poissonSteinSol r {0}) k < 0) := by
  intro h
  have hpos := (sec4_poissonSteinSol_pointMass_corrected_proof (r := 1) zero_lt_one).2.2.1
  exact lt_asymm (h zero_lt_one 0) hpos

/-! ### Section 4.2.1: Combinatorial Head-Run De-Clumping Identity (`D-C5`, `SC-5`) -/

private lemma prod_fin_eq_one_iff_of_zero_or_one {m : ℕ} {g : Fin m → ℕ}
    (hg : ∀ r : Fin m, g r = 0 ∨ g r = 1) :
    (∏ r : Fin m, g r) = 1 ↔ ∀ r : Fin m, g r = 1 := by
  constructor
  · intro hprod r
    rcases hg r with hr0 | hr1
    · exfalso
      have h0 : ∏ s : Fin m, g s = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ r) hr0
      omega
    · exact hr1
  · intro hall
    simp [hall]

private lemma headRunIndicator_zero_or_one {n : ℕ} (k : ℕ) {y : Fin n → ℕ}
    (hy : ∀ t : Fin n, y t = 0 ∨ y t = 1) (i : ℕ) :
    headRunIndicator k y i = 0 ∨ headRunIndicator k y i = 1 := by
  have hprod_01 : ∀ {i : ℕ} (hik : i + k ≤ n),
      (∏ j : Fin k, y ⟨i + j.1, by omega⟩) = 0 ∨ (∏ j : Fin k, y ⟨i + j.1, by omega⟩) = 1 := by
    intro i hik
    by_cases hall : ∀ j : Fin k, y ⟨i + j.1, by omega⟩ = 1
    · exact Or.inr (by simp [hall])
    · push Not at hall
      rcases hall with ⟨j, hj⟩
      rcases hy ⟨i + j.1, by omega⟩ with h0 | h1
      · exact Or.inl (Finset.prod_eq_zero (Finset.mem_univ j) h0)
      · exact False.elim (hj h1)
  cases i with
  | zero =>
    unfold headRunIndicator
    split_ifs with hik
    · simpa using hprod_01 hik
    · exact Or.inl rfl
  | succ r =>
    unfold headRunIndicator
    split_ifs with hik
    · rcases hy ⟨r, by omega⟩ with hr0 | hr1 <;> rcases hprod_01 hik with hp0 | hp1
      · exact Or.inl (by simp [hr0, hp0])
      · exact Or.inr (by simp [hr0, hp1])
      · exact Or.inl (by simp [hr1, hp0])
      · exact Or.inl (by simp [hr1, hp1])
    · exact Or.inl rfl

private lemma headRunIndicator_eq_one_iff {n : ℕ} (k : ℕ) {y : Fin n → ℕ}
    (hy : ∀ t : Fin n, y t = 0 ∨ y t = 1) (i : ℕ) :
    headRunIndicator k y i = 1 ↔
      ∃ h : i + k ≤ n,
        (∀ j : Fin k, y ⟨i + j.1, by omega⟩ = 1) ∧
        (i = 0 ∨ ∃ h₀ : i - 1 < n, y ⟨i - 1, h₀⟩ = 0) := by
  cases i with
  | zero =>
    unfold headRunIndicator
    split_ifs with hik
    · rw [one_mul, prod_fin_eq_one_iff_of_zero_or_one (fun j ↦ hy ⟨0 + j.1, by omega⟩)]
      exact ⟨fun hr ↦ ⟨hik, hr, Or.inl rfl⟩, fun ⟨_, hr, _⟩ ↦ hr⟩
    · simp only [false_iff]
      rintro ⟨h, _, _⟩
      exact hik h
  | succ r =>
    unfold headRunIndicator
    split_ifs with hik
    · rw [mul_eq_one,
        prod_fin_eq_one_iff_of_zero_or_one (fun j ↦ hy ⟨r + 1 + j.1, by omega⟩)]
      refine ⟨fun ⟨hl, hr⟩ ↦ ⟨hik, hr, ?_⟩, fun ⟨_, hr, hl⟩ ↦ ⟨?_, hr⟩⟩
      · right
        refine ⟨by omega, ?_⟩
        rcases hy ⟨r, by omega⟩ with h0 | h1
        · simpa using h0
        · simp [h1] at hl
      · rcases hl with h0 | ⟨h₀, hy0⟩
        · exact h0.elim
        · simp only [Nat.add_sub_cancel] at hy0
          change 1 - y ⟨r, h₀⟩ = 1
          omega
    · simp only [false_iff]
      rintro ⟨h, _, _⟩
      exact hik h

/-- Combinatorial head-run de-clumping identity (`SteinIntro.tex:2006-2023`; `SC-5`): for $k \ge 1$
and any $\{0, 1\}$-valued sequence $y : \mathrm{Fin}\,n \to \mathbb{N}$, `headRunCount k y` equals
the exact number of maximal contiguous runs of ones in $y$ of length at least $k$. -/
theorem sec4_2_1_headRun_declumping_proof :
    ∀ {n k : ℕ}, 1 ≤ k → ∀ {y : Fin n → ℕ},
      (∀ t : Fin n, y t = 0 ∨ y t = 1) →
      headRunCount k y =
        {im : ℕ × ℕ |
          k ≤ im.2 ∧
          ∃ h : im.1 + im.2 ≤ n,
            (∀ r : Fin im.2, y ⟨im.1 + r.1, by omega⟩ = 1) ∧
            (im.1 = 0 ∨ ∃ h₀ : im.1 - 1 < n, y ⟨im.1 - 1, h₀⟩ = 0) ∧
            (im.1 + im.2 = n ∨ ∃ h₁ : im.1 + im.2 < n, y ⟨im.1 + im.2, h₁⟩ = 0)}.ncard := by
  intro n k _hk y hy
  classical
  let S : Set (ℕ × ℕ) :=
    {im : ℕ × ℕ |
      k ≤ im.2 ∧
      ∃ h : im.1 + im.2 ≤ n,
        (∀ r : Fin im.2, y ⟨im.1 + r.1, by omega⟩ = 1) ∧
        (im.1 = 0 ∨ ∃ h₀ : im.1 - 1 < n, y ⟨im.1 - 1, h₀⟩ = 0) ∧
        (im.1 + im.2 = n ∨ ∃ h₁ : im.1 + im.2 < n, y ⟨im.1 + im.2, h₁⟩ = 0)}
  let A : Finset ℕ := (Finset.range (n - k + 1)).filter fun i ↦ headRunIndicator k y i = 1
  have hcount_eq : headRunCount k y = A.card := by
    unfold headRunCount
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases headRunIndicator_zero_or_one k hy i with h0 | h1
    · simp [h0]
    · simp [h1]
  let P_run : ℕ → ℕ → Prop :=
    fun i m ↦ ∃ h : i + m ≤ n, ∀ r : Fin m, y ⟨i + r.1, by omega⟩ = 1
  let maxLen : ℕ → ℕ := fun i ↦ Nat.findGreatest (P_run i) n
  have hmax_spec : ∀ i ∈ A, (i, maxLen i) ∈ S := by
    intro i hiA
    have hi_one : headRunIndicator k y i = 1 := (Finset.mem_filter.mp hiA).2
    obtain ⟨hik, hones_k, hleft⟩ := (headRunIndicator_eq_one_iff k hy i).mp hi_one
    have hk_le_n : k ≤ n := by omega
    have hkm : k ≤ maxLen i :=
      Nat.le_findGreatest hk_le_n (P := P_run i) ⟨hik, hones_k⟩
    have hP0 : P_run i 0 := ⟨by omega, fun r ↦ Fin.elim0 r⟩
    have hspec : P_run i (maxLen i) :=
      Nat.findGreatest_spec (P := P_run i) (Nat.zero_le n) hP0
    obtain ⟨him, hones_m⟩ := hspec
    refine ⟨hkm, him, hones_m, hleft, ?_⟩
    by_cases heq : i + maxLen i = n
    · exact Or.inl heq
    · right
      have hlt : i + maxLen i < n := by omega
      refine ⟨hlt, ?_⟩
      rcases hy ⟨i + maxLen i, hlt⟩ with h0 | h1
      · exact h0
      · exfalso
        have hmax_le : maxLen i ≤ n := Nat.findGreatest_le n
        have hsucc_le : maxLen i + 1 ≤ n := by omega
        have hsucc_sat : P_run i (maxLen i + 1) := by
          refine ⟨by omega, fun r ↦ ?_⟩
          by_cases hr : r.1 < maxLen i
          · exact hones_m ⟨r.1, hr⟩
          · have hreq : r.1 = maxLen i := by omega
            have hidx : (⟨i + r.1, by omega⟩ : Fin n) = ⟨i + maxLen i, hlt⟩ := by
              ext; simp [hreq]
            rw [hidx]; exact h1
        have hle : maxLen i + 1 ≤ maxLen i :=
          Nat.le_findGreatest hsucc_le (P := P_run i) hsucc_sat
        omega
  have hS_iff : ∀ p : ℕ × ℕ, p ∈ S ↔ p.1 ∈ A ∧ p.2 = maxLen p.1 := by
    rintro ⟨i, m⟩
    constructor
    · rintro ⟨hkm, him, hones_m, hleft, hright⟩
      have hik : i + k ≤ n := by omega
      have hones_k : ∀ j : Fin k, y ⟨i + j.1, by omega⟩ = 1 :=
        fun j ↦ hones_m ⟨j.1, by omega⟩
      have hi_one : headRunIndicator k y i = 1 :=
        (headRunIndicator_eq_one_iff k hy i).mpr ⟨hik, hones_k, hleft⟩
      have hiA : i ∈ A :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi_one⟩
      have hm_le : m ≤ maxLen i :=
        Nat.le_findGreatest (by omega : m ≤ n) (P := P_run i) ⟨him, hones_m⟩
      have hm_eq : m = maxLen i := by
        by_contra hne
        have hlt : m < maxLen i := by omega
        obtain ⟨_, ⟨him', hones_max, _, _⟩⟩ := hmax_spec i hiA
        have h_at_m : y ⟨i + m, by omega⟩ = 1 := hones_max ⟨m, hlt⟩
        rcases hright with heq_n | ⟨h₁, hy0⟩
        · omega
        · have hidx : (⟨i + m, by omega⟩ : Fin n) = ⟨i + m, h₁⟩ := rfl
          rw [hidx, hy0] at h_at_m
          omega
      exact ⟨hiA, hm_eq⟩
    · rintro ⟨hiA, hm⟩
      dsimp only at hiA hm
      rw [hm]
      exact hmax_spec i hiA
  have hS_eq_image : S = (fun i ↦ (i, maxLen i)) '' (A : Set ℕ) := by
    ext ⟨i, m⟩
    simp only [hS_iff, Set.mem_image, Finset.mem_coe, Prod.mk.injEq]
    exact ⟨fun ⟨hi, hm⟩ ↦ ⟨i, hi, rfl, hm.symm⟩,
      fun ⟨j, hj, hji, hmj⟩ ↦ ⟨hji ▸ hj, hji ▸ hmj.symm⟩⟩
  change headRunCount k y = S.ncard
  rw [hcount_eq, hS_eq_image,
    Set.ncard_image_of_injective _ (fun i₁ i₂ h ↦ (Prod.mk.inj h).1)]
  simp [Set.ncard_def, Set.encard_coe_eq_coe_finsetCard]

/-- Negation of the literal `SteinIntro.tex:1899` claim that `Δf₀(k) < 0` for all `k ∈ ℕ`
(`ISSUE-4.4-PROSE`: at `k = 0`, `Δf₀(0) = (1 - e^{−λ})/λ > 0`). -/
theorem not_Sec4_fwdDiff_f0_neg_printed :
    ¬ (∀ {r : ℝ≥0}, 0 < r → ∀ k : ℕ, fwdDiff 1 (poissonSteinSol r {0}) k < 0) :=
  not_sec4_fwdDiff_f0_neg_printed_proof

end SteinMethod
