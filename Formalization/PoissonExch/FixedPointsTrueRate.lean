/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Metrics.Basic
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
# Example 4.21 True Rate: Fixed Points of Random Permutations

Formalizes the prose rate claim at the end of Example 4.21 (`SteinIntro.tex:2702-2703`, citing
Arratia–Barbour–Tavaré `[abt03]`; `stmts-review-05H` item `H4`, Backlog item 6) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `fixedPoints_uniform_measureReal_singleton_eq_sum`: exact inclusion-exclusion / derangement law
  $\mathbb{P}(W_n = k) = \frac{1}{k!} \sum_{j=0}^{n-k} \frac{(-1)^j}{j!}$ for $k \le n$ (and $0$
  for $k > n$), proved from scratch via `derangements.subtypeEquiv` and `numDerangements`.
* `tvDist_fixedPoints_poissonLaw_le_two_pow_div_factorial`: super-exponential factorial bound
  $d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)) \le \frac{2^n}{(n + 1)!}$ in `ℝ≥0∞` for all
  $n \in \mathbb{N}$ (`stmts-review-BL6` `BL6-1`).
* `tendsto_mul_tvDist_fixedPoints_poissonLaw` and `fixedPoints_true_rate` (`Ex4_21_true_rate`):
  $\lim_{n \to \infty} n \, d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)) = 0$ in `ℝ≥0∞`
  together with the factorial bound (plus `tendsto_mul_tvDist_toReal_fixedPoints_poissonLaw` in
  `ℝ`).
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Exact Distribution of Fixed-Point Counts via Derangements -/

private abbrev permFixedPointCount (n : ℕ) (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ π i = i).card

private noncomputable abbrev permFixedPointLaw (n : ℕ) : Measure ℕ :=
  ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).map (permFixedPointCount n)).toMeasure

private lemma card_filter_fixedPointSet_eq {n : ℕ} (A : Finset (Fin n)) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦
      (Finset.univ.filter fun i : Fin n ↦ π i = i) = A).card =
        numDerangements (n - A.card) := by
  let p : Fin n → Prop := fun a ↦ a ∉ A
  have hp_card : Fintype.card (Subtype p) = n - A.card := by
    rw [Fintype.card_subtype]
    have hflt : (Finset.univ.filter p) = Aᶜ := by
      ext a; simp [p]
    rw [hflt, Finset.card_compl, Fintype.card_fin]
  have hequiv :
      {π : Equiv.Perm (Fin n) // (Finset.univ.filter fun i : Fin n ↦ π i = i) = A} ≃
        derangements (Subtype p) := by
    refine (Equiv.subtypeEquivRight ?_).trans (derangements.subtypeEquiv p).symm
    intro π
    simp only [Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and, p,
      Classical.not_not, Function.mem_fixedPoints]
    exact forall_congr' fun _ ↦ Iff.comm
  rw [← Fintype.card_subtype, Fintype.card_congr hequiv, card_derangements_eq_numDerangements,
    hp_card]

private lemma card_filter_permFixedPointCount_eq (n k : ℕ) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ permFixedPointCount n π = k).card =
      n.choose k * numDerangements (n - k) := by
  let S := (Finset.univ : Finset (Fin n)).powersetCard k
  let fib : Finset (Fin n) → Finset (Equiv.Perm (Fin n)) := fun A ↦
    Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦
      (Finset.univ.filter fun i : Fin n ↦ π i = i) = A
  have hbi :
      (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ permFixedPointCount n π = k) =
        S.biUnion fib := by
    ext π
    simp only [permFixedPointCount, S, fib, Finset.mem_filter, Finset.mem_univ,
      Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨A, hA, hπ⟩
      rw [hπ, hA]
  have hdisj : (S : Set (Finset (Fin n))).PairwiseDisjoint fib := by
    intro A₁ _ A₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  rw [hbi, Finset.card_biUnion hdisj]
  have hterm : ∀ A ∈ S, (fib A).card = numDerangements (n - k) := by
    intro A hA
    rw [card_filter_fixedPointSet_eq A, (Finset.mem_powersetCard.mp hA).2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

private lemma numDerangements_div_factorial_eq_sum (m : ℕ) :
    (numDerangements m : ℝ) / (m.factorial : ℝ) =
      ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ) := by
  rw [← Int.cast_natCast (numDerangements m), numDerangements_sum]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have h_le : j ≤ m := Finset.mem_range_succ_iff.mp hj
  rw [Nat.ascFactorial_eq_div, add_tsub_cancel_of_le h_le]
  push_cast [Nat.factorial_dvd_factorial h_le]
  have hfac_ne : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hm_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  field_simp [hfac_ne, hm_ne]

private lemma permFixedPointLaw_real_singleton_raw (n k : ℕ) :
    (permFixedPointLaw n).real {k} =
      ((n.choose k * numDerangements (n - k) : ℕ) : ℝ) / (n.factorial : ℝ) := by
  have hm :
      permFixedPointLaw n {k} =
        ((n.choose k * numDerangements (n - k) : ℕ) : ℝ≥0∞) * (n.factorial : ℝ≥0∞)⁻¹ := by
    rw [permFixedPointLaw, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k),
      PMF.map_apply, tsum_fintype]
    trans (∑ π : Equiv.Perm (Fin n),
        if permFixedPointCount n π = k then (n.factorial : ℝ≥0∞)⁻¹ else 0)
    · refine Finset.sum_congr rfl fun π _ ↦ ?_
      by_cases h : permFixedPointCount n π = k
      · simp [h, PMF.uniformOfFintype_apply, Fintype.card_perm, Fintype.card_fin]
      · have h' : k ≠ permFixedPointCount n π := Ne.symm h
        simp [h, h']
    · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_filter_permFixedPointCount_eq]
  rw [measureReal_def, hm, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, div_eq_mul_inv]

/-- Exact distribution of the fixed-point count $W_n$ of a uniform random permutation of `Fin n`
(`SteinIntro.tex:2702-2703`, `[abt03]`; `stmts-review-05H` item `H4`):
$\mathbb{P}(W_n = k) = \frac{1}{k!} \sum_{j=0}^{n-k} \frac{(-1)^j}{j!}$ for $k \le n$, and $0$
for $k > n$. -/
theorem fixedPoints_uniform_measureReal_singleton_eq_sum (n k : ℕ) :
    (((PMF.uniformOfFintype (Equiv.Perm (Fin n))).map
        (fun π ↦ (Finset.univ.filter fun i : Fin n ↦ π i = i).card)).toMeasure).real {k} =
      if k ≤ n then
        (1 / (k.factorial : ℝ)) *
          ∑ j ∈ Finset.range (n - k + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)
      else 0 := by
  rw [permFixedPointLaw_real_singleton_raw]
  split_ifs with hk
  · rw [← numDerangements_div_factorial_eq_sum (n - k)]
    have hchoose :
        (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) = (n.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
    have hch_ne : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
    have hk_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hnk_ne : ((n - k).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
    have hn_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    push_cast
    rw [← hchoose]
    field_simp [hch_ne, hk_ne, hnk_ne, hn_ne]
  · have hlt : n < k := lt_of_not_ge hk
    simp [Nat.choose_eq_zero_of_lt hlt]

/-! ### Section 2: Alternating-Series Remainder and Factorial Total-Variation Bound -/

private lemma abs_sum_neg_one_pow_div_factorial_sub_exp_neg_one_le (m : ℕ) :
    |(∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)) - Real.exp (-1)| ≤
      1 / ((m + 1).factorial : ℝ) := by
  let f : ℕ → ℝ := fun j ↦ (-1 : ℝ) ^ j / (j.factorial : ℝ)
  have hf : HasSum f (Real.exp (-1)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-1 : ℝ)
  have htail : HasSum (fun r : ℕ ↦ f (r + (m + 1)))
      (Real.exp (-1) - ∑ j ∈ Finset.range (m + 1), f j) :=
    (hasSum_nat_add_iff' (m + 1)).mpr hf
  let u : ℕ → ℝ := fun r ↦ 1 / ((r + (m + 1)).factorial : ℝ)
  have hu_nn : ∀ r : ℕ, 0 ≤ u r := fun r ↦ by positivity
  have hu_anti : ∀ r : ℕ, u (r + 1) ≤ u r := fun r ↦ by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact_mod_cast Nat.factorial_le (by omega : r + (m + 1) ≤ (r + 1) + (m + 1))
  let g : ℕ → ℝ := fun r ↦ (-1 : ℝ) ^ r * u r
  let S : ℝ := (-1 : ℝ) ^ (m + 1) * (Real.exp (-1) - ∑ j ∈ Finset.range (m + 1), f j)
  have hg_eq : (fun r : ℕ ↦ (-1 : ℝ) ^ (m + 1) * f (r + (m + 1))) = g := by
    funext r
    dsimp only [f, g, u]
    have hpow : (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (r + (m + 1)) = (-1 : ℝ) ^ r := by
      calc
        (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (r + (m + 1))
            = ((-1 : ℝ) ^ 2) ^ (m + 1) * (-1 : ℝ) ^ r := by
              rw [← pow_add, ← pow_mul]
              ring_nf
        _ = (-1 : ℝ) ^ r := by norm_num
    calc
      (-1 : ℝ) ^ (m + 1) * ((-1 : ℝ) ^ (r + (m + 1)) / ((r + (m + 1)).factorial : ℝ))
          = ((-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ (r + (m + 1))) *
              (1 / ((r + (m + 1)).factorial : ℝ)) := by ring
      _ = (-1 : ℝ) ^ r * (1 / ((r + (m + 1)).factorial : ℝ)) := by rw [hpow]
  have hg : HasSum g S := by
    rw [← hg_eq]
    exact htail.mul_left ((-1 : ℝ) ^ (m + 1))
  let T : ℕ → ℝ := fun R ↦ ∑ r ∈ Finset.range R, g r
  have hg_even : ∀ q : ℕ, g (2 * q) = u (2 * q) := fun q ↦ by
    dsimp only [g]
    rw [pow_mul]
    norm_num
  have hg_odd : ∀ q : ℕ, g (2 * q + 1) = -u (2 * q + 1) := fun q ↦ by
    dsimp only [g]
    rw [pow_succ, pow_mul]
    norm_num
  have hpair : ∀ q : ℕ, 0 ≤ T (2 * q) ∧ T (2 * q + 1) ≤ u 0 := by
    intro q
    induction q with
    | zero =>
      simp [T, hg_even 0]
    | succ q ih =>
      have hT1 : T (2 * (q + 1)) = T (2 * q) + u (2 * q) - u (2 * q + 1) := by
        have hidx : 2 * (q + 1) = (2 * q + 1) + 1 := by omega
        rw [hidx]
        simp only [T, Finset.sum_range_succ, hg_even q, hg_odd q]
        ring
      have hT2 : T (2 * (q + 1) + 1) = T (2 * q + 1) - u (2 * q + 1) + u (2 * q + 2) := by
        have hidx1 : 2 * (q + 1) + 1 = (2 * q + 2) + 1 := by omega
        have hidx2 : 2 * q + 2 = 2 * (q + 1) := by omega
        rw [hidx1]
        simp only [T, Finset.sum_range_succ, hg_odd q]
        rw [hidx2, hg_even (q + 1), ← hidx2]
        ring
      exact ⟨by linarith [ih.1, hu_anti (2 * q)], by linarith [ih.2, hu_anti (2 * q + 1)]⟩
  have hT_bounds : ∀ R : ℕ, 0 ≤ T R ∧ T R ≤ u 0 := by
    intro R
    let q := R / 2
    have hdiv : 2 * q + R % 2 = R := Nat.div_add_mod R 2
    have hmod : R % 2 = 0 ∨ R % 2 = 1 := by omega
    have hstep : T (2 * q + 1) = T (2 * q) + u (2 * q) := by
      simp only [T, Finset.sum_range_succ, hg_even q]
    rcases hmod with h0 | h1
    · have hR : R = 2 * q := by omega
      rw [hR]
      exact ⟨(hpair q).1, by linarith [(hpair q).2, hu_nn (2 * q), hstep]⟩
    · have hR : R = 2 * q + 1 := by omega
      rw [hR]
      exact ⟨by linarith [(hpair q).1, hu_nn (2 * q), hstep], (hpair q).2⟩
  have hS_nn : 0 ≤ S := ge_of_tendsto' hg.tendsto_sum_nat fun R ↦ (hT_bounds R).1
  have hS_le : S ≤ u 0 := le_of_tendsto' hg.tendsto_sum_nat fun R ↦ (hT_bounds R).2
  have habs_S :
      |(∑ j ∈ Finset.range (m + 1), f j) - Real.exp (-1)| = |S| := by
    rw [abs_sub_comm]
    dsimp only [S]
    rw [abs_mul, abs_neg_one_pow, one_mul]
  rw [habs_S, abs_of_nonneg hS_nn]
  simpa [u] using hS_le

private lemma abs_permFixedPointLaw_sub_poissonLaw_le_of_le {n k : ℕ} (hk : k ≤ n) :
    |(permFixedPointLaw n).real {k} - (poissonLaw 1).real {k}| ≤
      ((n + 1).choose k : ℝ) / ((n + 1).factorial : ℝ) := by
  have hW :
      (permFixedPointLaw n).real {k} =
        (1 / (k.factorial : ℝ)) *
          ∑ j ∈ Finset.range (n - k + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ) := by
    have h := fixedPoints_uniform_measureReal_singleton_eq_sum n k
    simpa only [hk, ↓reduceIte] using h
  have hP : (poissonLaw 1).real {k} = (1 / (k.factorial : ℝ)) * Real.exp (-1) := by
    simp only [poissonLaw, ProbabilityTheory.poissonMeasure_real_singleton, NNReal.coe_one,
      one_pow, mul_one]
    ring
  rw [hW, hP, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (k.factorial : ℝ))]
  have hsub_eq : n - k + 1 = n + 1 - k := by omega
  have hrem :
      |(∑ j ∈ Finset.range (n - k + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)) - Real.exp (-1)| ≤
        1 / ((n + 1 - k).factorial : ℝ) :=
    (abs_sum_neg_one_pow_div_factorial_sub_exp_neg_one_le (n - k)).trans_eq (by rw [hsub_eq])
  have hchoose :
      ((n + 1).choose k : ℝ) * (k.factorial : ℝ) * ((n + 1 - k).factorial : ℝ) =
        ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ n + 1)
  have hch_ne : ((n + 1).choose k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega : k ≤ n + 1)).ne'
  have hk_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnk_ne : ((n + 1 - k).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1 - k))
  have hn1_ne : ((n + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
  calc
    (1 / (k.factorial : ℝ)) *
        |(∑ j ∈ Finset.range (n - k + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)) - Real.exp (-1)|
      ≤ (1 / (k.factorial : ℝ)) * (1 / ((n + 1 - k).factorial : ℝ)) := by gcongr
    _ = ((n + 1).choose k : ℝ) / ((n + 1).factorial : ℝ) := by
      rw [← hchoose]
      field_simp [hch_ne, hk_ne, hnk_ne, hn1_ne]

private lemma tsum_tail_permFixedPointLaw_sub_poissonLaw_le (n : ℕ) :
    (∑' r : ℕ,
        |(permFixedPointLaw n).real {r + (n + 1)} - (poissonLaw 1).real {r + (n + 1)}|) ≤
      1 / ((n + 1).factorial : ℝ) := by
  have hexp1 : HasSum (fun r : ℕ ↦ (1 : ℝ) / (r.factorial : ℝ)) (Real.exp 1) := by
    have h := NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)
    rw [← Real.exp_eq_exp_ℝ] at h
    simpa only [one_pow] using h
  let maj : ℕ → ℝ :=
    fun r ↦ (Real.exp (-1) / ((n + 1).factorial : ℝ)) * ((1 : ℝ) / (r.factorial : ℝ))
  have hmaj_sum : HasSum maj (1 / ((n + 1).factorial : ℝ)) := by
    have h := hexp1.mul_left (Real.exp (-1) / ((n + 1).factorial : ℝ))
    have hval :
        (Real.exp (-1) / ((n + 1).factorial : ℝ)) * Real.exp 1 =
          1 / ((n + 1).factorial : ℝ) := by
      calc
        (Real.exp (-1) / ((n + 1).factorial : ℝ)) * Real.exp 1
            = (Real.exp (-1) * Real.exp 1) / ((n + 1).factorial : ℝ) := by ring
        _ = 1 / ((n + 1).factorial : ℝ) := by rw [← Real.exp_add]; norm_num
    rwa [hval] at h
  have hpt : ∀ r : ℕ,
      |(permFixedPointLaw n).real {r + (n + 1)} - (poissonLaw 1).real {r + (n + 1)}| ≤ maj r := by
    intro r
    have hnot : ¬ r + (n + 1) ≤ n := by omega
    have hW0 : (permFixedPointLaw n).real {r + (n + 1)} = 0 := by
      have h := fixedPoints_uniform_measureReal_singleton_eq_sum n (r + (n + 1))
      simpa only [hnot, ↓reduceIte] using h
    have hP :
        (poissonLaw 1).real {r + (n + 1)} = Real.exp (-1) / ((r + (n + 1)).factorial : ℝ) := by
      simp [poissonLaw, ProbabilityTheory.poissonMeasure_real_singleton]
    rw [hW0, hP, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have hfac_le :
        (r.factorial : ℝ) * ((n + 1).factorial : ℝ) ≤ ((r + (n + 1)).factorial : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
        (Nat.factorial_mul_factorial_dvd_factorial_add r (n + 1))
    have hdiv_le :
        1 / ((r + (n + 1)).factorial : ℝ) ≤
          1 / ((r.factorial : ℝ) * ((n + 1).factorial : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hfac_le
    calc
      Real.exp (-1) / ((r + (n + 1)).factorial : ℝ)
          = Real.exp (-1) * (1 / ((r + (n + 1)).factorial : ℝ)) := by ring
      _ ≤ Real.exp (-1) * (1 / ((r.factorial : ℝ) * ((n + 1).factorial : ℝ))) := by gcongr
      _ = maj r := by dsimp [maj]; ring
  have hdom : Summable fun r : ℕ ↦
      |(permFixedPointLaw n).real {r + (n + 1)} - (poissonLaw 1).real {r + (n + 1)}| :=
    Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hpt hmaj_sum.summable
  exact (hdom.tsum_le_tsum hpt hmaj_sum.summable).trans_eq hmaj_sum.tsum_eq

/-- Explicit super-exponential total-variation bound for the number of fixed points $W_n$ of a
uniform random permutation of `Fin n` against $\mathrm{Po}(1)$ (`SteinIntro.tex:2702-2703`,
`[abt03]`; `stmts-review-05H` item `H4`, `stmts-review-BL6` `BL6-1`): for every $n \in \mathbb{N}$,
$$d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)) \le \frac{2^n}{(n + 1)!}$$
in `ℝ≥0∞`. -/
theorem tvDist_fixedPoints_poissonLaw_le_two_pow_div_factorial (n : ℕ) :
    tvDist
        (((PMF.uniformOfFintype (Equiv.Perm (Fin n))).map
          (fun π ↦ (Finset.univ.filter fun i : Fin n ↦ π i = i).card)).toMeasure)
        (poissonLaw 1) ≤
      (2 : ENNReal) ^ n / (Nat.factorial (n + 1) : ENNReal) := by
  have hrhs :
      (2 : ENNReal) ^ n / (Nat.factorial (n + 1) : ENNReal) =
        ENNReal.ofReal ((2 : ℝ) ^ n / (Nat.factorial (n + 1) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat 2, ENNReal.ofReal_natCast]
  rw [hrhs]
  let d : ℕ → ℝ := fun k ↦ |(permFixedPointLaw n).real {k} - (poissonLaw 1).real {k}|
  have hd_nn : ∀ k : ℕ, 0 ≤ d k := fun k ↦ abs_nonneg _
  have hsum_μ : Summable fun k : ℕ ↦ (permFixedPointLaw n).real {k} := by
    have h : (∑' k : ℕ, permFixedPointLaw n {k}) ≠ ⊤ := by
      have heq : (∑' k : ℕ, permFixedPointLaw n {k}) = permFixedPointLaw n Set.univ := by
        simpa only [Set.indicator_univ] using
          Measure.tsum_indicator_apply_singleton (permFixedPointLaw n) Set.univ MeasurableSet.univ
      rw [heq]
      exact measure_ne_top _ _
    simpa only [measureReal_def] using ENNReal.summable_toReal h
  have hsum_ν : Summable fun k : ℕ ↦ (poissonLaw 1).real {k} := by
    have h : (∑' k : ℕ, poissonLaw 1 {k}) ≠ ⊤ := by
      have heq : (∑' k : ℕ, poissonLaw 1 {k}) = poissonLaw 1 Set.univ := by
        simpa only [Set.indicator_univ] using
          Measure.tsum_indicator_apply_singleton (poissonLaw 1) Set.univ MeasurableSet.univ
      rw [heq]
      exact measure_ne_top _ _
    simpa only [measureReal_def] using ENNReal.summable_toReal h
  have hd_sum : Summable d := (hsum_μ.sub hsum_ν).abs
  rw [tvDist_eq_half_tsum (permFixedPointLaw n) (poissonLaw 1)]
  have htsum_ofReal :
      (1 / 2 : ℝ≥0∞) * (∑' k : ℕ, ENNReal.ofReal (d k)) =
        ENNReal.ofReal ((1 / 2 : ℝ) * ∑' k : ℕ, d k) := by
    have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_one, ENNReal.ofReal_ofNat 2]
    rw [hhalf, ← ENNReal.ofReal_tsum_of_nonneg hd_nn hd_sum,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  change (1 / 2 : ℝ≥0∞) * (∑' k : ℕ, ENNReal.ofReal (d k)) ≤ _
  rw [htsum_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hd_sum.sum_add_tsum_nat_add (n + 1)]
  have hhead :
      (∑ k ∈ Finset.range (n + 1), d k) ≤
        (∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℝ)) / ((n + 1).factorial : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun k hk ↦
      abs_permFixedPointLaw_sub_poissonLaw_le_of_le (Finset.mem_range_succ_iff.mp hk)
  have htail : (∑' r : ℕ, d (r + (n + 1))) ≤ 1 / ((n + 1).factorial : ℝ) :=
    tsum_tail_permFixedPointLaw_sub_poissonLaw_le n
  have hbinom :
      (∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℝ)) + 1 = (2 : ℝ) ^ (n + 1) := by
    have hnat : (∑ k ∈ Finset.range (n + 1), (n + 1).choose k) + 1 = 2 ^ (n + 1) := by
      calc
        (∑ k ∈ Finset.range (n + 1), (n + 1).choose k) + 1
            = (∑ k ∈ Finset.range (n + 1), (n + 1).choose k) + (n + 1).choose (n + 1) := by
              rw [Nat.choose_self]
        _ = ∑ k ∈ Finset.range (n + 2), (n + 1).choose k := (Finset.sum_range_succ _ (n + 1)).symm
        _ = 2 ^ (n + 1) := Nat.sum_range_choose (n + 1)
    exact_mod_cast hnat
  calc
    (1 / 2 : ℝ) * ((∑ k ∈ Finset.range (n + 1), d k) + ∑' r : ℕ, d (r + (n + 1)))
      ≤ (1 / 2 : ℝ) *
          ((∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℝ)) / ((n + 1).factorial : ℝ) +
            1 / ((n + 1).factorial : ℝ)) := by
        gcongr
    _ = (1 / 2 : ℝ) *
          (((∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℝ)) + 1) /
            ((n + 1).factorial : ℝ)) := by
        ring
    _ = (1 / 2 : ℝ) * ((2 : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by rw [hbinom]
    _ = (2 : ℝ) ^ n / ((n + 1).factorial : ℝ) := by rw [pow_succ]; ring

/-! ### Section 3: Asymptotic `o(1/n)` Rate (`Ex4_21_true_rate`) -/

/-- For the number of fixed points $W_n(\pi) = |\{i \in \mathrm{Fin}\,n \mid \pi(i) = i\}|$ of a
uniform random permutation of `Fin n`, the total-variation error to $\mathrm{Po}(1)$ satisfies
$\lim_{n \to \infty} n \, d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)) = 0$ in `ℝ≥0∞`. -/
theorem tendsto_mul_tvDist_fixedPoints_poissonLaw :
    let W : (n : ℕ) → Equiv.Perm (Fin n) → ℕ :=
      fun n π ↦ (Finset.univ.filter fun i : Fin n ↦ π i = i).card
    let μW : ℕ → Measure ℕ :=
      fun n ↦ ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).map (W n)).toMeasure
    Filter.Tendsto
      (fun n : ℕ ↦ (n : ENNReal) * tvDist (μW n) (poissonLaw 1))
      Filter.atTop (nhds 0) := by
  intro W μW
  have hupper_real :
      Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n / (n.factorial : ℝ)) Filter.atTop (nhds 0) :=
    (NormedSpace.expSeries_div_hasSum_exp (2 : ℝ)).summable.tendsto_atTop_zero
  have hupper_ennreal :
      Filter.Tendsto
        (fun n : ℕ ↦ ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hupper_real
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper_ennreal
    (fun _ ↦ bot_le) fun n ↦ ?_
  have hrhs :
      (2 : ENNReal) ^ n / (Nat.factorial (n + 1) : ENNReal) =
        ENNReal.ofReal ((2 : ℝ) ^ n / (Nat.factorial (n + 1) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
      ENNReal.ofReal_ofNat 2, ENNReal.ofReal_natCast]
  have hbound :
      tvDist (μW n) (poissonLaw 1) ≤ (2 : ENNReal) ^ n / (Nat.factorial (n + 1) : ENNReal) :=
    tvDist_fixedPoints_poissonLaw_le_two_pow_div_factorial n
  calc
    (n : ENNReal) * tvDist (μW n) (poissonLaw 1)
      ≤ (n : ENNReal) * ((2 : ENNReal) ^ n / (Nat.factorial (n + 1) : ENNReal)) := by gcongr
    _ = ENNReal.ofReal ((n : ℝ) * ((2 : ℝ) ^ n / ((n + 1).factorial : ℝ))) := by
        rw [hrhs, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n / (n.factorial : ℝ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hn_le : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
        have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        calc
          (n : ℝ) * ((2 : ℝ) ^ n / ((n + 1).factorial : ℝ))
            ≤ ((n + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ))) := by
              rw [Nat.factorial_succ, Nat.cast_mul]
              gcongr
          _ = (2 : ℝ) ^ n / (n.factorial : ℝ) := by
              field_simp [hn1_pos.ne']

/-- **Example 4.21 true-rate prose claim** (`SteinIntro.tex:2702-2703`, citing `[abt03]`;
`stmts-review-05H` item `H4`, `stmts-review-BL6` `BL6-1`, Backlog item 6): for the number of fixed
points $W_n(\pi) = |\{i \in \mathrm{Fin}\,n \mid \pi(i) = i\}|$ of a uniform random permutation of
`Fin n`, $d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)) \le 2^n / (n + 1)!$ for all
$n \in \mathbb{N}$ and $\lim_{n \to \infty} n \, d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1))
= 0$ in `ℝ≥0∞`. -/
theorem fixedPoints_true_rate :
    let W : (n : ℕ) → Equiv.Perm (Fin n) → ℕ :=
      fun n π ↦ (Finset.univ.filter fun i : Fin n ↦ π i = i).card
    let μW : ℕ → Measure ℕ :=
      fun n ↦ ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).map (W n)).toMeasure
    (∀ n : ℕ,
      tvDist (μW n) (poissonLaw 1) ≤
        (2 : ENNReal) ^ n / (Nat.factorial (n + 1) : ENNReal)) ∧
    Filter.Tendsto
      (fun n : ℕ ↦ (n : ENNReal) * tvDist (μW n) (poissonLaw 1))
      Filter.atTop (nhds 0) :=
  ⟨tvDist_fixedPoints_poissonLaw_le_two_pow_div_factorial,
    tendsto_mul_tvDist_fixedPoints_poissonLaw⟩

/-- Real-valued `.toReal` version of `tendsto_mul_tvDist_fixedPoints_poissonLaw`:
$\lim_{n \to \infty} n \, d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)).\mathrm{toReal} = 0$. -/
theorem tendsto_mul_tvDist_toReal_fixedPoints_poissonLaw :
    let W : (n : ℕ) → Equiv.Perm (Fin n) → ℕ :=
      fun n π ↦ (Finset.univ.filter fun i : Fin n ↦ π i = i).card
    let μW : ℕ → Measure ℕ :=
      fun n ↦ ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).map (W n)).toMeasure
    Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) * (tvDist (μW n) (poissonLaw 1)).toReal)
      Filter.atTop (nhds 0) := by
  intro W μW
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    tendsto_mul_tvDist_fixedPoints_poissonLaw
  simp only [ENNReal.toReal_zero] at hlim
  refine hlim.congr fun n ↦ ?_
  dsimp only [Function.comp_apply]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

end SteinMethod
