/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.CombinatorialPair

/-!
# Two-Swap Permutation Coupling Combinatorics (`Formalization.Exer.PermSwapCoupling`)

Pure combinatorial and finite-sum machinery for the two-swap square-increment-biased permutation
coupling in Hoeffding's combinatorial CLT (`EXER-3`, `Sec3_6_1_combinatorial_kolmogorov`,
`SteinIntro.tex:1742-1743`):

* `permTwoSwap` and `permTwoSwapPair`: given distinct input indices $i_1 \ne i_2$, distinct output
  indices $j_1 \ne j_2$, and $\pi \in S_n$,
  $\pi_1 = (j_1\;\pi(i_1)) \circ \pi$, $\pi^\dagger = (j_2\;\pi_1(i_2)) \circ \pi_1$, and
  $\pi'^\dagger = \pi^\dagger \circ (i_1\;i_2)$.
* `permTwoSwap_apply_first`, `permTwoSwap_apply_second`, `permTwoSwapPair_apply_first`,
  `permTwoSwapPair_apply_second`: $\pi^\dagger(i_1) = j_1$, $\pi^\dagger(i_2) = j_2$,
  $\pi'^\dagger(i_1) = j_2$, and $\pi'^\dagger(i_2) = j_1$.
* `card_permTwoSwapChangedSet_le`, `permTwoSwap_apply_of_notMem`,
  `permTwoSwapPair_apply_of_notMem`, `abs_combStat_permTwoSwap_sub_le`,
  `abs_combStat_permTwoSwapPair_sub_le`, `abs_combStat_convex_permTwoSwap_sub_le`: both
  $\pi^\dagger$ and $\pi'^\dagger$ agree with $\pi$ outside a set of at most $4$ positions, so
  $|S(\pi^\dagger) - S(\pi)| \le 8 C$, $|S(\pi'^\dagger) - S(\pi)| \le 8 C$, and any convex
  combination differs from $S(\pi)$ by at most $8 C$ whenever $|a_{ij}| \le C$.
* `card_filter_permTwoSwap_eq` and `sum_permTwoSwap_eq_mul_sum_fiber`: for $i_1 \ne i_2$ and
  $j_1 \ne j_2$, each fibre $\{\rho \in S_n : \rho(i_1) = j_1 \wedge \rho(i_2) = j_2\}$ is hit
  by $\pi \mapsto \pi^\dagger$ exactly $n(n - 1)$ times.
* `sum_twoSwapWeight_mul_sum_permTwoSwap`: summing over all quadruples $(i_1, i_2, j_1, j_2)$ with
  weights $(a_{i_1, j_2} + a_{i_2, j_1} - a_{i_1, j_1} - a_{i_2, j_2})^2$ and over $\pi \in S_n$
  recovers $2 n (n - 1)$ times the square-increment-weighted sum over
  $(\rho, \tau) \in S_n \times \mathrm{SwapType}\,n$.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SteinMethod

/-- First intermediate permutation $\pi_1 = (j_1\;\pi(i_1)) \circ \pi$ in the two-swap coupling,
sending $i_1 \mapsto j_1$. -/
def permOneSwap {n : ℕ} (i₁ j₁ : Fin n) (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Equiv.swap j₁ (π i₁) * π

/-- Two-swap coupled permutation $\pi^\dagger = (j_2\;\pi_1(i_2)) \circ \pi_1$ where
$\pi_1 = (j_1\;\pi(i_1)) \circ \pi$, sending $(i_1, i_2) \mapsto (j_1, j_2)$ whenever
$i_1 \ne i_2$ and $j_1 \ne j_2$ (`SteinIntro.tex:1742-1743`). -/
def permTwoSwap {n : ℕ} (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  let π₁ := permOneSwap i₁ j₁ π
  Equiv.swap j₂ (π₁ i₂) * π₁

/-- Companion coupled permutation $\pi'^\dagger = \pi^\dagger \circ (i_1\;i_2)$, sending
$(i_1, i_2) \mapsto (j_2, j_1)$ whenever $i_1 \ne i_2$ and $j_1 \ne j_2$. -/
def permTwoSwapPair {n : ℕ} (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n) :=
  permTwoSwap i₁ i₂ j₁ j₂ π * Equiv.swap i₁ i₂

@[simp]
lemma permOneSwap_apply_self {n : ℕ} (i₁ j₁ : Fin n) (π : Equiv.Perm (Fin n)) :
    permOneSwap i₁ j₁ π i₁ = j₁ := by
  simp [permOneSwap]

lemma permTwoSwap_apply_first {n : ℕ} {i₁ i₂ j₁ j₂ : Fin n}
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) (π : Equiv.Perm (Fin n)) :
    permTwoSwap i₁ i₂ j₁ j₂ π i₁ = j₁ := by
  dsimp [permTwoSwap]
  have h1 : permOneSwap i₁ j₁ π i₁ = j₁ := permOneSwap_apply_self i₁ j₁ π
  have hne : j₁ ≠ permOneSwap i₁ j₁ π i₂ :=
    fun h ↦ hi ((permOneSwap i₁ j₁ π).injective (h1.trans h))
  rw [h1, Equiv.swap_apply_of_ne_of_ne hj hne]

@[simp]
lemma permTwoSwap_apply_second {n : ℕ} (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    permTwoSwap i₁ i₂ j₁ j₂ π i₂ = j₂ := by
  simp [permTwoSwap]

lemma permTwoSwapPair_apply_first {n : ℕ} (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    permTwoSwapPair i₁ i₂ j₁ j₂ π i₁ = j₂ := by
  simp [permTwoSwapPair, Equiv.Perm.mul_apply]

lemma permTwoSwapPair_apply_second {n : ℕ} {i₁ i₂ j₁ j₂ : Fin n}
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) (π : Equiv.Perm (Fin n)) :
    permTwoSwapPair i₁ i₂ j₁ j₂ π i₂ = j₁ := by
  simp [permTwoSwapPair, Equiv.Perm.mul_apply, permTwoSwap_apply_first hi hj]

/-! ### Section 1: At Most Four Changed Positions and $8 C$ Difference Bound -/

/-- Candidate set of at most $4$ input indices on which `permTwoSwap` or `permTwoSwapPair` can
differ from `π`. -/
def permTwoSwapChangedSet {n : ℕ} (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    Finset (Fin n) :=
  {i₁, i₂, π.symm j₁, (permOneSwap i₁ j₁ π).symm j₂}

lemma card_permTwoSwapChangedSet_le {n : ℕ} (i₁ i₂ j₁ j₂ : Fin n)
    (π : Equiv.Perm (Fin n)) :
    (permTwoSwapChangedSet i₁ i₂ j₁ j₂ π).card ≤ 4 := by
  unfold permTwoSwapChangedSet
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  simp

lemma permOneSwap_apply_of_ne {n : ℕ} {i₁ j₁ k : Fin n} {π : Equiv.Perm (Fin n)}
    (hk1 : k ≠ i₁) (hk2 : k ≠ π.symm j₁) :
    permOneSwap i₁ j₁ π k = π k := by
  dsimp [permOneSwap]
  have hne1 : π k ≠ j₁ := fun h ↦ hk2 (by rw [← h, π.symm_apply_apply])
  have hne2 : π k ≠ π i₁ := π.injective.ne hk1
  exact Equiv.swap_apply_of_ne_of_ne hne1 hne2

lemma permTwoSwap_apply_of_notMem {n : ℕ} {i₁ i₂ j₁ j₂ k : Fin n}
    {π : Equiv.Perm (Fin n)} (hk : k ∉ permTwoSwapChangedSet i₁ i₂ j₁ j₂ π) :
    permTwoSwap i₁ i₂ j₁ j₂ π k = π k := by
  simp only [permTwoSwapChangedSet, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rcases hk with ⟨hk1, hk2, hk3, hk4⟩
  dsimp [permTwoSwap]
  have hπ₁ : permOneSwap i₁ j₁ π k = π k := permOneSwap_apply_of_ne hk1 hk3
  have hne1 : permOneSwap i₁ j₁ π k ≠ j₂ :=
    fun h ↦ hk4 (by rw [← h, Equiv.symm_apply_apply])
  have hne2 : permOneSwap i₁ j₁ π k ≠ permOneSwap i₁ j₁ π i₂ :=
    (permOneSwap i₁ j₁ π).injective.ne hk2
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2, hπ₁]

lemma permTwoSwapPair_apply_of_notMem {n : ℕ} {i₁ i₂ j₁ j₂ k : Fin n}
    {π : Equiv.Perm (Fin n)} (hk : k ∉ permTwoSwapChangedSet i₁ i₂ j₁ j₂ π) :
    permTwoSwapPair i₁ i₂ j₁ j₂ π k = π k := by
  have hk' := hk
  simp only [permTwoSwapChangedSet, Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
  rcases hk' with ⟨hk1, hk2, _, _⟩
  rw [permTwoSwapPair, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hk1 hk2,
    permTwoSwap_apply_of_notMem hk]

/-- If two permutations $\sigma, \tau \in S_n$ agree outside a finset $D$ of cardinality at most
$m$ and $|a_{ij}| \le C$ with $C \ge 0$, then
$|\sum_k a_{k, \sigma(k)} - \sum_k a_{k, \tau(k)}| \le 2 m C$. -/
lemma abs_sum_sub_le_of_agree_outside {n m : ℕ} {a : Fin n → Fin n → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (ha : ∀ i j : Fin n, |a i j| ≤ C)
    {σ τ : Equiv.Perm (Fin n)} {D : Finset (Fin n)}
    (hD_card : D.card ≤ m) (hagree : ∀ k : Fin n, k ∉ D → σ k = τ k) :
    |(∑ k : Fin n, a k (σ k)) - ∑ k : Fin n, a k (τ k)| ≤ 2 * (m : ℝ) * C := by
  rw [← Finset.sum_sub_distrib]
  have hsub : (∑ k : Fin n, (a k (σ k) - a k (τ k))) =
      ∑ k ∈ D, (a k (σ k) - a k (τ k)) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ D) fun k _ hk ↦ ?_
    rw [hagree k hk, sub_self]
  rw [hsub]
  calc
    |∑ k ∈ D, (a k (σ k) - a k (τ k))|
        ≤ ∑ k ∈ D, |a k (σ k) - a k (τ k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ D, (2 * C) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          calc
            |a k (σ k) - a k (τ k)| ≤ |a k (σ k)| + |a k (τ k)| := abs_sub _ _
            _ ≤ C + C := add_le_add (ha k (σ k)) (ha k (τ k))
            _ = 2 * C := by ring
    _ = (D.card : ℝ) * (2 * C) := by simp [nsmul_eq_mul]
    _ ≤ (m : ℝ) * (2 * C) := by
          gcongr
    _ = 2 * (m : ℝ) * C := by ring

lemma abs_combStat_permTwoSwap_sub_le {n : ℕ} {a : Fin n → Fin n → ℝ} {C : ℝ}
    (ha : ∀ i j : Fin n, |a i j| ≤ C) (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    |combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) - combStat a π| ≤ 8 * C := by
  have hC0 : 0 ≤ C := (abs_nonneg (a i₁ j₁)).trans (ha i₁ j₁)
  have heq : combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) - combStat a π =
      (∑ k : Fin n, a k (permTwoSwap i₁ i₂ j₁ j₂ π k)) - ∑ k : Fin n, a k (π k) := by
    unfold combStat
    ring
  rw [heq]
  have hle := abs_sum_sub_le_of_agree_outside hC0 ha
    (card_permTwoSwapChangedSet_le i₁ i₂ j₁ j₂ π)
    (fun k hk ↦ permTwoSwap_apply_of_notMem hk)
  norm_num at hle
  exact hle

lemma abs_combStat_permTwoSwapPair_sub_le {n : ℕ} {a : Fin n → Fin n → ℝ} {C : ℝ}
    (ha : ∀ i j : Fin n, |a i j| ≤ C) (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    |combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π| ≤ 8 * C := by
  have hC0 : 0 ≤ C := (abs_nonneg (a i₁ j₁)).trans (ha i₁ j₁)
  have heq : combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π =
      (∑ k : Fin n, a k (permTwoSwapPair i₁ i₂ j₁ j₂ π k)) - ∑ k : Fin n, a k (π k) := by
    unfold combStat
    ring
  rw [heq]
  have hle := abs_sum_sub_le_of_agree_outside hC0 ha
    (card_permTwoSwapChangedSet_le i₁ i₂ j₁ j₂ π)
    (fun k hk ↦ permTwoSwapPair_apply_of_notMem hk)
  norm_num at hle
  exact hle

/-- For any $u \in [0, 1]$, the convex interpolation between `combStat` at `permTwoSwap` and at
`permTwoSwapPair` differs from `combStat a π` by at most $8 C$. -/
lemma abs_combStat_convex_permTwoSwap_sub_le {n : ℕ} {a : Fin n → Fin n → ℝ} {C u : ℝ}
    (ha : ∀ i j : Fin n, |a i j| ≤ C) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (i₁ i₂ j₁ j₂ : Fin n) (π : Equiv.Perm (Fin n)) :
    |u * combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) +
        (1 - u) * combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π| ≤ 8 * C := by
  have hsplit :
      u * combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) +
          (1 - u) * combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π =
        u * (combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) - combStat a π) +
          (1 - u) * (combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π) := by
    ring
  have hu1' : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hb1 := abs_combStat_permTwoSwap_sub_le ha i₁ i₂ j₁ j₂ π
  have hb2 := abs_combStat_permTwoSwapPair_sub_le ha i₁ i₂ j₁ j₂ π
  rw [hsplit]
  calc
    |u * (combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) - combStat a π) +
        (1 - u) * (combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π)|
        ≤ |u * (combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) - combStat a π)| +
            |(1 - u) * (combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π)| :=
          abs_add_le _ _
    _ = u * |combStat a (permTwoSwap i₁ i₂ j₁ j₂ π) - combStat a π| +
          (1 - u) * |combStat a (permTwoSwapPair i₁ i₂ j₁ j₂ π) - combStat a π| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hu1']
    _ ≤ u * (8 * C) + (1 - u) * (8 * C) :=
          add_le_add (mul_le_mul_of_nonneg_left hb1 hu0) (mul_le_mul_of_nonneg_left hb2 hu1')
    _ = 8 * C := by ring

/-! ### Section 2: Exact Fibre Size $n(n - 1)$ and Weighted Sum Identity -/

/-- Inverse reconstruction of $\pi \in S_n$ from
$\rho = \mathrm{permTwoSwap}\,i_1\,i_2\,j_1\,j_2\,\pi$ and the two intermediate values
$(y_1, y_2) = (\pi(i_1), \pi_1(i_2))$. -/
def permTwoSwapReconstruct {n : ℕ} (j₁ j₂ : Fin n) (ρ : Equiv.Perm (Fin n))
    (p : Fin n × Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap j₁ p.1 * (Equiv.swap j₂ p.2 * ρ)

/-- Each fixed-index fibre $\{\rho \in S_n : \rho(i_1) = j_1 \wedge \rho(i_2) = j_2\}$ is hit by
`permTwoSwap i₁ i₂ j₁ j₂` exactly $n(n - 1)$ times. -/
lemma card_filter_permTwoSwap_eq_of_mem_fiber {n : ℕ} {i₁ i₂ j₁ j₂ : Fin n}
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) {ρ : Equiv.Perm (Fin n)}
    (hρ1 : ρ i₁ = j₁) (hρ2 : ρ i₂ = j₂) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦
      permTwoSwap i₁ i₂ j₁ j₂ π = ρ).card = n * (n - 1) := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (Fin.pos i₁).ne'
  have htarget_card :
      ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ.erase j₁)).card = n * (n - 1) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Finset.card_erase_of_mem (Finset.mem_univ j₁), Finset.card_univ, Fintype.card_fin]
  rw [← htarget_card]
  refine Finset.card_bij
    (fun π _ ↦ (π i₁, permOneSwap i₁ j₁ π i₂))
    (fun π _ ↦ ?_)
    (fun π₁ hπ₁ π₂ hπ₂ heq ↦ ?_)
    (fun p hp ↦ ?_)
  · rw [Finset.mem_product, Finset.mem_erase]
    refine ⟨Finset.mem_univ _, ?_, Finset.mem_univ _⟩
    have h1 : permOneSwap i₁ j₁ π i₁ = j₁ := permOneSwap_apply_self i₁ j₁ π
    exact fun h ↦ hi.symm ((permOneSwap i₁ j₁ π).injective (h.trans h1.symm))
  · rw [Finset.mem_filter] at hπ₁ hπ₂
    have hy1 : π₁ i₁ = π₂ i₁ := congrArg Prod.fst heq
    have hy2 : permOneSwap i₁ j₁ π₁ i₂ = permOneSwap i₁ j₁ π₂ i₂ := congrArg Prod.snd heq
    have h1 : Equiv.swap j₂ (permOneSwap i₁ j₁ π₁ i₂) * permOneSwap i₁ j₁ π₁ =
        Equiv.swap j₂ (permOneSwap i₁ j₁ π₂ i₂) * permOneSwap i₁ j₁ π₂ :=
      hπ₁.2.trans hπ₂.2.symm
    rw [hy2, mul_right_inj] at h1
    dsimp [permOneSwap] at h1
    rw [hy1, mul_right_inj] at h1
    exact h1
  · rw [Finset.mem_product, Finset.mem_erase] at hp
    have hp2_ne : p.2 ≠ j₁ := hp.2.1
    let π₁ : Equiv.Perm (Fin n) := Equiv.swap j₂ p.2 * ρ
    let π : Equiv.Perm (Fin n) := Equiv.swap j₁ p.1 * π₁
    have hπ₁_i₁ : π₁ i₁ = j₁ := by
      dsimp [π₁]
      rw [hρ1, Equiv.swap_apply_of_ne_of_ne hj hp2_ne.symm]
    have hπ₁_i₂ : π₁ i₂ = p.2 := by
      dsimp [π₁]
      rw [hρ2, Equiv.swap_apply_left]
    have hπ_i₁ : π i₁ = p.1 := by
      dsimp [π]
      rw [hπ₁_i₁, Equiv.swap_apply_left]
    have h_one : permOneSwap i₁ j₁ π = π₁ := by
      unfold permOneSwap
      rw [hπ_i₁]
      dsimp only [π]
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
    have h_two : permTwoSwap i₁ i₂ j₁ j₂ π = ρ := by
      unfold permTwoSwap
      dsimp only
      rw [h_one, hπ₁_i₂]
      dsimp only [π₁]
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
    refine ⟨π, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_two⟩, ?_⟩
    exact Prod.ext hπ_i₁ (by rw [h_one, hπ₁_i₂])

lemma card_filter_permTwoSwap_eq_zero_of_not_mem_fiber {n : ℕ} {i₁ i₂ j₁ j₂ : Fin n}
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) {ρ : Equiv.Perm (Fin n)}
    (hρ : ¬ (ρ i₁ = j₁ ∧ ρ i₂ = j₂)) :
    (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦
      permTwoSwap i₁ i₂ j₁ j₂ π = ρ).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro π _ hEq
  apply hρ
  rw [← hEq]
  exact ⟨permTwoSwap_apply_first hi hj π, permTwoSwap_apply_second i₁ i₂ j₁ j₂ π⟩

/-- Summing $F(\mathrm{permTwoSwap}\,i_1\,i_2\,j_1\,j_2\,\pi)$ over $\pi \in S_n$ equals $n(n - 1)$
times the sum of $F(\rho)$ over the fibre
$\{\rho \in S_n : \rho(i_1) = j_1 \wedge \rho(i_2) = j_2\}$. -/
lemma sum_permTwoSwap_eq_mul_sum_fiber {n : ℕ} {i₁ i₂ j₁ j₂ : Fin n}
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) (F : Equiv.Perm (Fin n) → ℝ) :
    (∑ π : Equiv.Perm (Fin n), F (permTwoSwap i₁ i₂ j₁ j₂ π)) =
      (n * (n - 1) : ℕ) *
        ∑ ρ ∈ Finset.univ.filter (fun ρ : Equiv.Perm (Fin n) ↦ ρ i₁ = j₁ ∧ ρ i₂ = j₂), F ρ := by
  have hpart :
      (∑ π : Equiv.Perm (Fin n), F (permTwoSwap i₁ i₂ j₁ j₂ π)) =
        ∑ ρ : Equiv.Perm (Fin n),
          ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ permTwoSwap i₁ i₂ j₁ j₂ π = ρ),
            F (permTwoSwap i₁ i₂ j₁ j₂ π) := by
    symm
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext π
      simp
    · intro ρ₁ _ ρ₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro π _ h1 h2
      exact hne (h1.symm.trans h2)
  rw [hpart]
  have hinner : ∀ ρ : Equiv.Perm (Fin n),
      (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ permTwoSwap i₁ i₂ j₁ j₂ π = ρ),
          F (permTwoSwap i₁ i₂ j₁ j₂ π)) =
        if ρ i₁ = j₁ ∧ ρ i₂ = j₂ then ((n * (n - 1) : ℕ) : ℝ) * F ρ else 0 := by
    intro ρ
    have hcongr :
        (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ permTwoSwap i₁ i₂ j₁ j₂ π = ρ),
            F (permTwoSwap i₁ i₂ j₁ j₂ π)) =
          ∑ _π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ permTwoSwap i₁ i₂ j₁ j₂ π = ρ),
            F ρ :=
      Finset.sum_congr rfl fun π hπ ↦ by rw [(Finset.mem_filter.mp hπ).2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    by_cases hρ : ρ i₁ = j₁ ∧ ρ i₂ = j₂
    · simp [hρ, card_filter_permTwoSwap_eq_of_mem_fiber hi hj hρ.1 hρ.2]
    · simp [hρ, card_filter_permTwoSwap_eq_zero_of_not_mem_fiber hi hj hρ]
  simp_rw [hinner, ← Finset.sum_filter, ← Finset.mul_sum]

/-- Index quadruple $((i_1, i_2), (j_1, j_2))$ with $i_1 \ne i_2$ and $j_1 \ne j_2$. -/
abbrev TwoSwapQuad (n : ℕ) : Type :=
  {q : (Fin n × Fin n) × (Fin n × Fin n) // q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2}

/-- Squared swap increment $(a_{i_1, j_2} + a_{i_2, j_1} - a_{i_1, j_1} - a_{i_2, j_2})^2$
for a quadruple $q = ((i_1, i_2), (j_1, j_2))$. -/
def twoSwapWeight {n : ℕ} (a : Fin n → Fin n → ℝ) (q : TwoSwapQuad n) : ℝ :=
  (a q.1.1.1 q.1.2.2 + a q.1.1.2 q.1.2.1 - a q.1.1.1 q.1.2.1 - a q.1.1.2 q.1.2.2) ^ 2

lemma twoSwapWeight_nonneg {n : ℕ} (a : Fin n → Fin n → ℝ) (q : TwoSwapQuad n) :
    0 ≤ twoSwapWeight a q :=
  sq_nonneg _

/-- Master combinatorial identity relating the quadruple-weighted two-swap sum to the
square-increment-weighted sum over $(\rho, \tau) \in S_n \times \mathrm{SwapType}\,n$. -/
lemma sum_twoSwapWeight_mul_sum_permTwoSwap {n : ℕ} (a : Fin n → Fin n → ℝ)
    (G : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) → ℝ) :
    (∑ q : TwoSwapQuad n, twoSwapWeight a q *
        ∑ π : Equiv.Perm (Fin n),
          G (permTwoSwap q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 π,
            permTwoSwapPair q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 π)) =
      2 * ((n * (n - 1) : ℕ) : ℝ) *
        ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1) := by
  have hfiber : ∀ q : TwoSwapQuad n,
      twoSwapWeight a q *
          (∑ π : Equiv.Perm (Fin n),
            G (permTwoSwap q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 π,
              permTwoSwapPair q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 π)) =
        ((n * (n - 1) : ℕ) : ℝ) *
          ∑ ρ ∈ Finset.univ.filter
              (fun ρ : Equiv.Perm (Fin n) ↦ ρ q.1.1.1 = q.1.2.1 ∧ ρ q.1.1.2 = q.1.2.2),
            (combStat a (ρ * Equiv.swap q.1.1.1 q.1.1.2) - combStat a ρ) ^ 2 *
              G (ρ, ρ * Equiv.swap q.1.1.1 q.1.1.2) := by
    intro q
    have hsum := sum_permTwoSwap_eq_mul_sum_fiber q.2.1 q.2.2
      (fun ρ ↦ G (ρ, ρ * Equiv.swap q.1.1.1 q.1.1.2))
    dsimp only [permTwoSwapPair]
    rw [hsum, ← mul_assoc, mul_comm (twoSwapWeight a q), mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    have hρ' := (Finset.mem_filter.mp hρ).2
    have hdiff := combStat_mul_swap_sub a ρ q.2.1.symm
    rw [hdiff, hρ'.1, hρ'.2]
    rfl
  simp_rw [hfiber, ← Finset.mul_sum]
  have hquad_sum :
      (∑ q : TwoSwapQuad n,
          ∑ ρ ∈ Finset.univ.filter
              (fun ρ : Equiv.Perm (Fin n) ↦ ρ q.1.1.1 = q.1.2.1 ∧ ρ q.1.1.2 = q.1.2.2),
            (combStat a (ρ * Equiv.swap q.1.1.1 q.1.1.2) - combStat a ρ) ^ 2 *
              G (ρ, ρ * Equiv.swap q.1.1.1 q.1.1.2)) =
        2 * ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1) := by
    let term : Fin n → Fin n → Equiv.Perm (Fin n) → ℝ := fun i₁ i₂ ρ ↦
      (combStat a (ρ * Equiv.swap i₁ i₂) - combStat a ρ) ^ 2 * G (ρ, ρ * Equiv.swap i₁ i₂)
    have hbij :
        (∑ q : TwoSwapQuad n,
            ∑ ρ ∈ Finset.univ.filter
                (fun ρ : Equiv.Perm (Fin n) ↦ ρ q.1.1.1 = q.1.2.1 ∧ ρ q.1.1.2 = q.1.2.2),
              term q.1.1.1 q.1.1.2 ρ) =
          ∑ p ∈ Finset.univ.filter
              (fun p : (Fin n × Fin n) × (Fin n × Fin n) ↦ p.1.1 ≠ p.1.2 ∧ p.2.1 ≠ p.2.2),
            ∑ ρ ∈ Finset.univ.filter
                (fun ρ : Equiv.Perm (Fin n) ↦ ρ p.1.1 = p.2.1 ∧ ρ p.1.2 = p.2.2),
              term p.1.1 p.1.2 ρ :=
      Finset.sum_bij (fun q _ ↦ q.1)
        (fun q _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun p hp ↦ ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    change (∑ q : TwoSwapQuad n,
        ∑ ρ ∈ Finset.univ.filter
            (fun ρ : Equiv.Perm (Fin n) ↦ ρ q.1.1.1 = q.1.2.1 ∧ ρ q.1.1.2 = q.1.2.2),
          term q.1.1.1 q.1.1.2 ρ) = _
    rw [hbij, Finset.sum_filter, Fintype.sum_prod_type]
    have hinner_j : ∀ p₁ : Fin n × Fin n,
        (∑ p₂ : Fin n × Fin n,
            if p₁.1 ≠ p₁.2 ∧ p₂.1 ≠ p₂.2 then
              ∑ ρ ∈ Finset.univ.filter
                  (fun ρ : Equiv.Perm (Fin n) ↦ ρ p₁.1 = p₂.1 ∧ ρ p₁.2 = p₂.2),
                term p₁.1 p₁.2 ρ
            else 0) =
          if p₁.1 ≠ p₁.2 then ∑ ρ : Equiv.Perm (Fin n), term p₁.1 p₁.2 ρ else 0 := by
      intro p₁
      by_cases hp₁ : p₁.1 ≠ p₁.2
      · rw [ite_eq_left_iff.mpr fun h ↦ absurd hp₁ h]
        have hdrop : ∀ p₂ : Fin n × Fin n,
            (if p₁.1 ≠ p₁.2 ∧ p₂.1 ≠ p₂.2 then
                ∑ ρ ∈ Finset.univ.filter
                    (fun ρ : Equiv.Perm (Fin n) ↦ ρ p₁.1 = p₂.1 ∧ ρ p₁.2 = p₂.2),
                  term p₁.1 p₁.2 ρ
              else 0) =
              ∑ ρ ∈ Finset.univ.filter
                  (fun ρ : Equiv.Perm (Fin n) ↦ ρ p₁.1 = p₂.1 ∧ ρ p₁.2 = p₂.2),
                term p₁.1 p₁.2 ρ := by
          intro p₂
          by_cases hp₂ : p₂.1 ≠ p₂.2
          · exact ite_eq_left_iff.mpr fun h ↦ absurd ⟨hp₁, hp₂⟩ h
          · rw [ite_eq_right_iff.mpr fun h ↦ absurd h.2 hp₂]
            have hp₂' : p₂.1 = p₂.2 := not_ne_iff.mp hp₂
            symm
            refine Finset.sum_eq_zero fun ρ hρ ↦ ?_
            have hρ' := (Finset.mem_filter.mp hρ).2
            exact False.elim (hp₁ (ρ.injective (hρ'.1.trans (hp₂'.trans hρ'.2.symm))))
        simp_rw [hdrop]
        rw [← Finset.sum_biUnion]
        · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
          ext ρ
          simp
        · intro q₁ _ q₂ _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_filter]
          intro ρ _ h1 h2
          exact hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))
      · rw [ite_eq_right_iff.mpr fun h ↦ absurd h hp₁]
        refine Finset.sum_eq_zero fun p₂ _ ↦
          ite_eq_right_iff.mpr fun h ↦ absurd h.1 hp₁
    simp_rw [hinner_j]
    rw [Fintype.sum_prod_type]
    have herase : ∀ i₁ : Fin n,
        (∑ i₂ : Fin n, if i₁ ≠ i₂ then ∑ ρ : Equiv.Perm (Fin n), term i₁ i₂ ρ else 0) =
          ∑ i₂ ∈ Finset.univ.erase i₁, ∑ ρ : Equiv.Perm (Fin n), term i₁ i₂ ρ := by
      intro i₁
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext i₂
      simp [ne_comm]
    simp_rw [herase]
    have hcomm :
        (∑ i₁ : Fin n, ∑ i₂ ∈ Finset.univ.erase i₁, ∑ ρ : Equiv.Perm (Fin n), term i₁ i₂ ρ) =
          ∑ ρ : Equiv.Perm (Fin n), ∑ i₁ : Fin n, ∑ i₂ ∈ Finset.univ.erase i₁, term i₁ i₂ ρ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i₁ _ ↦ ?_
      rw [Finset.sum_comm]
    rw [hcomm]
    have hswap : ∀ ρ : Equiv.Perm (Fin n),
        (∑ i₁ : Fin n, ∑ i₂ ∈ Finset.univ.erase i₁, term i₁ i₂ ρ) =
          2 * ∑ τ : SwapType n,
            (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1) :=
      fun ρ ↦ (two_mul_sum_swapType
        (fun τπ ↦ (combStat a (ρ * τπ) - combStat a ρ) ^ 2 * G (ρ, ρ * τπ))).symm
    simp_rw [hswap, ← Finset.mul_sum]
  rw [hquad_sum]
  ring

/-! ### Section 3: Two-Swap Coupled Pair Distribution and Variance Guard -/

/-- If $\operatorname{Var}(\sum_{i=1}^n a_{i, \pi(i)}) > 0$, then $n \ge 2$ (for $n \le 1$,
`Equiv.Perm (Fin n)` is a subsingleton so the sum is constant and has variance $0$). -/
lemma two_le_of_pos_variance_perm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {n : ℕ} {a : Fin n → Fin n → ℝ} {π : Ω → Equiv.Perm (Fin n)}
    (hvar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, a i (π ω i)) P) :
    2 ≤ n := by
  by_contra hlt
  have : Subsingleton (Fin n) := ⟨fun x y ↦ Fin.ext (by omega)⟩
  have hconst : (fun ω ↦ ∑ i : Fin n, a i (π ω i)) =
      fun _ ↦ ∑ i : Fin n, a i ((1 : Equiv.Perm (Fin n)) i) := by
    funext ω
    rw [Subsingleton.elim (π ω) 1]
  rw [hconst] at hvar
  simp [ProbabilityTheory.variance, ProbabilityTheory.evariance] at hvar

/-- Coupled permutation pair $(\pi^\dagger, \pi'^\dagger)$ associated with
$(\pi, q) \in S_n \times \mathrm{TwoSwapQuad}\,n$. -/
def twoSwapCoupledPair {n : ℕ} (x : Equiv.Perm (Fin n) × TwoSwapQuad n) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin n) :=
  (permTwoSwap x.2.1.1.1 x.2.1.1.2 x.2.1.2.1 x.2.1.2.2 x.1,
    permTwoSwapPair x.2.1.1.1 x.2.1.1.2 x.2.1.2.1 x.2.1.2.2 x.1)

/-- Specializing `sum_twoSwapWeight_mul_sum_permTwoSwap` to $G \equiv 1$ relates the total
quadruple weight $\sum_q \mathrm{twoSwapWeight}\,a\,q$ to the sum of squared increments. -/
lemma sum_twoSwapWeight_mul_card_perm {n : ℕ} (a : Fin n → Fin n → ℝ) :
    (∑ q : TwoSwapQuad n, twoSwapWeight a q) * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      2 * ((n * (n - 1) : ℕ) : ℝ) *
        ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 := by
  have h := sum_twoSwapWeight_mul_sum_permTwoSwap a (fun _ ↦ (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ← Finset.sum_mul] at h
  exact h

/-- Probability mass function on `TwoSwapQuad n` proportional to `twoSwapWeight a q`. -/
noncomputable def twoSwapQuadPMF {n : ℕ} (a : Fin n → Fin n → ℝ)
    (hQ_pos : 0 < ∑ q : TwoSwapQuad n, twoSwapWeight a q) : PMF (TwoSwapQuad n) :=
  PMF.ofFintype
    (fun q ↦ ENNReal.ofReal (twoSwapWeight a q / ∑ q' : TwoSwapQuad n, twoSwapWeight a q'))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun q _ ↦ div_nonneg (twoSwapWeight_nonneg a q) hQ_pos.le),
        ← Finset.sum_div, div_self hQ_pos.ne', ENNReal.ofReal_one])

@[simp]
lemma twoSwapQuadPMF_apply {n : ℕ} (a : Fin n → Fin n → ℝ)
    (hQ_pos : 0 < ∑ q : TwoSwapQuad n, twoSwapWeight a q) (q : TwoSwapQuad n) :
    twoSwapQuadPMF a hQ_pos q =
      ENNReal.ofReal (twoSwapWeight a q / ∑ q' : TwoSwapQuad n, twoSwapWeight a q') :=
  rfl

/-- Expectation of $G(\mathrm{twoSwapCoupledPair}\,x)$ under $\mu_\sigma \otimes \mu_q$ equals the
square-increment-weighted average over $(\rho, \tau) \in S_n \times \mathrm{SwapType}\,n$. -/
lemma integral_twoSwapCoupledPair_eq {n : ℕ} (hn : 2 ≤ n) (a : Fin n → Fin n → ℝ)
    (hQ_pos : 0 < ∑ q : TwoSwapQuad n, twoSwapWeight a q)
    (G : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) → ℝ) :
    let μσ : Measure (Equiv.Perm (Fin n)) :=
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
    let μq : Measure (TwoSwapQuad n) := (twoSwapQuadPMF a hQ_pos).toMeasure
    ∫ x, G (twoSwapCoupledPair x) ∂(μσ.prod μq) =
      (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1)) /
        (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2) := by
  intro μσ μq
  have : DiscreteMeasurableSpace (TwoSwapQuad n) := inferInstance
  have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μq := PMF.toMeasure.isProbabilityMeasure _
  have hInt : Integrable (fun x ↦ G (twoSwapCoupledPair x)) (μσ.prod μq) := .of_finite
  rw [integral_prod _ hInt]
  have hinner : ∀ π : Equiv.Perm (Fin n),
      ∫ q, G (twoSwapCoupledPair (π, q)) ∂μq =
        ∑ q : TwoSwapQuad n,
          (twoSwapWeight a q / ∑ q' : TwoSwapQuad n, twoSwapWeight a q') *
            G (twoSwapCoupledPair (π, q)) := by
    intro π
    rw [PMF.integral_eq_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [twoSwapQuadPMF_apply,
      ENNReal.toReal_ofReal (div_nonneg (twoSwapWeight_nonneg a q) hQ_pos.le), smul_eq_mul]
  simp_rw [hinner]
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    ← Finset.mul_sum]
  have hcomm :
      (∑ π : Equiv.Perm (Fin n),
          ∑ q : TwoSwapQuad n,
            (twoSwapWeight a q / ∑ q' : TwoSwapQuad n, twoSwapWeight a q') *
              G (twoSwapCoupledPair (π, q))) =
        (∑ q' : TwoSwapQuad n, twoSwapWeight a q')⁻¹ *
          ∑ q : TwoSwapQuad n, twoSwapWeight a q *
            ∑ π : Equiv.Perm (Fin n), G (twoSwapCoupledPair (π, q)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    simp_rw [div_eq_mul_inv, mul_comm (twoSwapWeight a q), mul_assoc, ← Finset.mul_sum]
    ring
  rw [hcomm]
  dsimp only [twoSwapCoupledPair]
  rw [sum_twoSwapWeight_mul_sum_permTwoSwap a G]
  have hcard_pos : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := Nat.cast_pos.mpr Fintype.card_pos
  have h2n_pos : (0 : ℝ) < 2 * ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    positivity
  have hQ_eq := sum_twoSwapWeight_mul_card_perm a
  have hS_pos : 0 < ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
      (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 := by
    by_contra hle
    have hle' : ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
        (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 ≤ 0 := not_lt.mp hle
    have hprod_le : (∑ q : TwoSwapQuad n, twoSwapWeight a q) *
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ 0 := by
      rw [hQ_eq]
      exact mul_nonpos_of_nonneg_of_nonpos h2n_pos.le hle'
    exact absurd (mul_pos hQ_pos hcard_pos) (not_lt.mpr hprod_le)
  rw [eq_div_iff hS_pos.ne']
  calc
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
        ((∑ q' : TwoSwapQuad n, twoSwapWeight a q')⁻¹ *
          (2 * ((n * (n - 1) : ℕ) : ℝ) *
            ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
              (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1))) *
        (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2)
        = (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
            ((∑ q' : TwoSwapQuad n, twoSwapWeight a q')⁻¹ *
              ((2 * ((n * (n - 1) : ℕ) : ℝ) *
                ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
                  (combStat a (ρ * τ.1) - combStat a ρ) ^ 2) *
                (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
                  (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1)))) := by ring
    _ = (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
          ((∑ q' : TwoSwapQuad n, twoSwapWeight a q')⁻¹ *
            (((∑ q : TwoSwapQuad n, twoSwapWeight a q) *
              (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) *
              (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
                (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1)))) := by
          rw [← hQ_eq]
    _ = ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1) := by
          field_simp [hcard_pos.ne', hQ_pos.ne']

/-- Integral of any function $H : S_n \times \mathrm{SwapType}\,n \to \mathbb{R}$ under the product
of uniform measures $\mu_\sigma \otimes \mu_\tau$. -/
lemma integral_prod_uniform_perm_swapType {n : ℕ} (hn : 2 ≤ n)
    (H : Equiv.Perm (Fin n) × SwapType n → ℝ) :
    let hne : Nonempty (SwapType n) :=
      ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩
    let μσ : Measure (Equiv.Perm (Fin n)) :=
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
    let μτ : Measure (SwapType n) :=
      (@PMF.uniformOfFintype (SwapType n) inferInstance hne).toMeasure
    ∫ p, H p ∂(μσ.prod μτ) =
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
        ((Fintype.card (SwapType n) : ℝ)⁻¹ *
          ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n, H (ρ, τ)) := by
  intro hne μσ μτ
  have : DiscreteMeasurableSpace (SwapType n) := inferInstance
  have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μτ := PMF.toMeasure.isProbabilityMeasure _
  have hInt : Integrable H (μσ.prod μτ) := .of_finite
  rw [integral_prod H hInt]
  have hinner : ∀ ρ : Equiv.Perm (Fin n),
      ∫ τ, H (ρ, τ) ∂μτ =
        (Fintype.card (SwapType n) : ℝ)⁻¹ * ∑ τ : SwapType n, H (ρ, τ) := by
    intro ρ
    rw [PMF.integral_eq_sum]
    simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
      ← Finset.mul_sum]
  simp_rw [hinner]
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    ← Finset.mul_sum]

/-- For a uniform random permutation $\pi$, $\operatorname{Var}(\sum_{i=1}^n a_{i, \pi(i)})$ equals
$\operatorname{Var}(\mathrm{combStat}\,a)$ under the uniform measure on $S_n$. -/
lemma variance_combStat_eq_variance_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 1 ≤ n) (a : Fin n → Fin n → ℝ) {π : Ω → Equiv.Perm (Fin n)}
    (hπ : AEMeasurable π P)
    (hπ_unif : P.map π = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure) :
    ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, a i (π ω i)) P =
      ProbabilityTheory.variance (combStat a)
        (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure := by
  let μσ : Measure (Equiv.Perm (Fin n)) :=
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
  have hId : IdentDistrib (fun ω ↦ combStat a (π ω)) (combStat a) P μσ :=
    ⟨(Measurable.of_discrete (f := combStat a)).comp_aemeasurable hπ,
      (Measurable.of_discrete (f := combStat a)).aemeasurable,
      by
        change P.map (combStat a ∘ π) = μσ.map (combStat a)
        rw [← AEMeasurable.map_map_of_aemeasurable
          (Measurable.of_discrete (f := combStat a)).aemeasurable hπ, hπ_unif]⟩
  have hMean_μσ : ∫ ρ, combStat a ρ ∂μσ = 0 := by
    rw [PMF.integral_eq_sum]
    simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, ← Finset.mul_sum, sum_combStat_eq_zero hn a, mul_zero]
  have hMean_P : ∫ ω, combStat a (π ω) ∂P = 0 := hId.integral_eq.trans hMean_μσ
  have hInt_P : Integrable (fun ω ↦ combStat a (π ω)) P :=
    hId.symm.integrable_snd Integrable.of_finite
  let μ : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
  have hS_eq : (fun ω ↦ ∑ i : Fin n, a i (π ω i)) = fun ω ↦ combStat a (π ω) + μ := by
    funext ω; unfold combStat; ring
  have hMean_S : ∫ ω, (∑ i : Fin n, a i (π ω i)) ∂P = μ := by
    rw [hS_eq, integral_add hInt_P (integrable_const μ), hMean_P, zero_add,
      integral_const, probReal_univ, one_smul]
  have hevar : ProbabilityTheory.evariance (fun ω ↦ ∑ i : Fin n, a i (π ω i)) P =
      ProbabilityTheory.evariance (fun ω ↦ combStat a (π ω)) P := by
    unfold ProbabilityTheory.evariance
    refine lintegral_congr fun ω ↦ ?_
    rw [hMean_S, hMean_P, sub_zero]
    rfl
  rw [ProbabilityTheory.variance, hevar, ← ProbabilityTheory.variance, hId.variance_eq]

/-- Positivity of $\operatorname{Var}(\mathrm{combStat}\,a)$ implies positivity of the total
quadruple weight $\sum_q \mathrm{twoSwapWeight}\,a\,q$ and relates the sum of squared swap
increments to the variance. -/
lemma sum_sq_combStat_swap_and_twoSwapWeight_pos {n : ℕ} (hn : 2 ≤ n) (a : Fin n → Fin n → ℝ)
    (hVar : 0 < ProbabilityTheory.variance (combStat a)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure) :
    let hne : Nonempty (SwapType n) :=
      ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩
    let μσ : Measure (Equiv.Perm (Fin n)) :=
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
    let μτ : Measure (SwapType n) :=
      (@PMF.uniformOfFintype (SwapType n) inferInstance hne).toMeasure
    ∫ p, (combStat a (p.1 * p.2.1) - combStat a p.1) ^ 2 ∂(μσ.prod μτ) =
        2 * (2 / ((n : ℝ) - 1)) * ProbabilityTheory.variance (combStat a) μσ ∧
      0 < ∑ q : TwoSwapQuad n, twoSwapWeight a q := by
  intro hne μσ μτ
  have : DiscreteMeasurableSpace (SwapType n) := inferInstance
  have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μτ := PMF.toMeasure.isProbabilityMeasure _
  have h1 : (μσ.prod μτ).map Prod.fst = μσ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h2 : (μσ.prod μτ).map Prod.snd = μτ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hindep : ProbabilityTheory.IndepFun
      (Prod.fst : Equiv.Perm (Fin n) × SwapType n → Equiv.Perm (Fin n))
      (Prod.snd : Equiv.Perm (Fin n) × SwapType n → SwapType n) (μσ.prod μτ) :=
    ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  obtain ⟨hExch, hW_meas, hW2, _, hCond_W⟩ :=
    combinatorial_exchangeable_and_linear (μσ.prod μτ) hn a
      measurable_fst measurable_snd hindep h1 h2
  have ha_pos : 0 < 2 / ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact div_pos zero_lt_two (by linarith)
  have hsq := (steinPair_integral_eq_zero_and_sq_sub_eq (μσ.prod μτ)
    hExch ha_pos hW_meas hW2 hCond_W).2
  have hId_W : IdentDistrib (fun p : Equiv.Perm (Fin n) × SwapType n ↦ combStat a p.1)
      (combStat a) (μσ.prod μτ) μσ :=
    ⟨hW_meas.aemeasurable, (Measurable.of_discrete (f := combStat a)).aemeasurable,
      by
        change (μσ.prod μτ).map (combStat a ∘ Prod.fst) = μσ.map (combStat a)
        rw [← Measure.map_map .of_discrete measurable_fst, h1]⟩
  rw [hId_W.variance_eq] at hsq
  refine ⟨hsq, ?_⟩
  have hInt_pos : 0 < ∫ p, (combStat a (p.1 * p.2.1) - combStat a p.1) ^ 2 ∂(μσ.prod μτ) := by
    rw [hsq]
    exact mul_pos (mul_pos zero_lt_two ha_pos) hVar
  rw [integral_prod_uniform_perm_swapType hn] at hInt_pos
  have hc1 : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := Nat.cast_pos.mpr Fintype.card_pos
  have hc2 : (0 : ℝ) < Fintype.card (SwapType n) := Nat.cast_pos.mpr Fintype.card_pos
  have hS_pos : 0 < ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
      (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 := by
    by_contra hle
    have hle' : ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
        (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 ≤ 0 := not_lt.mp hle
    have h1_le : (Fintype.card (SwapType n) : ℝ)⁻¹ *
        ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc2.le) hle'
    have h2_le : (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
        ((Fintype.card (SwapType n) : ℝ)⁻¹ *
          ∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
            (combStat a (ρ * τ.1) - combStat a ρ) ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hc1.le) h1_le
    exact absurd hInt_pos (not_lt.mpr h2_le)
  have h2n_pos : (0 : ℝ) < 2 * ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    positivity
  have hQ_mul : 0 < (∑ q : TwoSwapQuad n, twoSwapWeight a q) *
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    rw [sum_twoSwapWeight_mul_card_perm a]
    exact mul_pos h2n_pos hS_pos
  by_contra hQ_le
  have hQ_le' : ∑ q : TwoSwapQuad n, twoSwapWeight a q ≤ 0 := not_lt.mp hQ_le
  exact absurd hQ_mul (not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg hQ_le' hc1.le))

end SteinMethod
