/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.PoissonExch
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform

/-!
# Example 4.21 Moments: Fixed Points and 2-Cycles (`Formalization.PoissonExch.FixedPointsMoments`)

Combinatorial fiber-counting and moment identities for the number of fixed points
$W = \mathrm{numFixedPoints}(\pi)$ and the number of 2-cycles $W_2 = \mathrm{numTwoCycles}(\pi)$
of a uniform random permutation $\pi$ on `Fin n`, from Example 4.21 (`SteinIntro.tex:2681-2702`)
of Nathan Ross, *"Fundamentals of Stein's method"*:

* `expected_fixed_points`: $\mathbb{E}[W] = 1$ for $n \ge 1$ (`SteinIntro.tex:2693`).
* `expected_fixed_points_sq`: $\mathbb{E}[W^2] = 2$ for $n \ge 2$ (`SteinIntro.tex:2698-2702`).
* `two_mul_numTwoCycles_eq_card_filter`: $2 W_2(\pi) = |\{x \mid \pi(x) \ne x \wedge
  \pi(\pi(x)) = x\}|$.
* `expected_two_cycles`: $\mathbb{E}[W_2] = 1/2$ for $n \ge 2$ (`SteinIntro.tex:2701`).
-/

open MeasureTheory ProbabilityTheory Finset PMF
open scoped NNReal ENNReal

namespace SteinMethod

/-! ### Fiber counting on `Equiv.Perm (Fin n)` -/

private lemma card_filter_perm_apply_eq {n : ℕ} (i j₁ j₂ : Fin n) :
    (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₁).card =
      (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₂).card := by
  refine Finset.card_bij (fun π _ ↦ Equiv.swap j₁ j₂ * π) ?_ ?_ ?_
  · intro π hπ
    rw [Finset.mem_filter] at hπ ⊢
    exact ⟨Finset.mem_univ _, by simp [hπ.2]⟩
  · intro π₁ _ π₂ _ h
    have h' := congrArg (fun τ ↦ Equiv.swap j₁ j₂ * τ) h
    simpa [← mul_assoc] using h'
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    refine ⟨Equiv.swap j₁ j₂ * π, ?_, by simp [← mul_assoc]⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simp [hπ.2]⟩

private lemma mul_card_filter_perm_apply_eq {n : ℕ} (i j₀ : Fin n) :
    n * (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₀).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
  calc
    n * (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₀).card
        = ∑ j : Fin n, (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j).card := by
          trans (∑ _j : Fin n, (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₀).card)
          · simp
          · exact Finset.sum_congr rfl fun j _ ↦ card_filter_perm_apply_eq i j₀ j
    _ = Fintype.card (Equiv.Perm (Fin n)) := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext π
            simp
          · intro j₁ _ j₂ _ hne
            dsimp only [Function.onFun]
            rw [Finset.disjoint_filter]
            intro π _ h1 h2
            exact hne (h1.symm.trans h2)

private lemma card_filter_perm_apply_eq_and_eq {n : ℕ} (i₁ i₂ j₁ j₂ j₂' : Fin n)
    (hj₂ : j₂ ≠ j₁) (hj₂' : j₂' ≠ j₁) :
    (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁ ∧ π i₂ = j₂).card =
      (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁ ∧ π i₂ = j₂').card := by
  refine Finset.card_bij (fun π _ ↦ Equiv.swap j₂ j₂' * π) ?_ ?_ ?_
  · intro π hπ
    rw [Finset.mem_filter] at hπ ⊢
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hπ.2.1]
      exact Equiv.swap_apply_of_ne_of_ne hj₂.symm hj₂'.symm
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hπ.2.2, Equiv.swap_apply_left]
  · intro π₁ _ π₂ _ h
    have h' := congrArg (fun τ ↦ Equiv.swap j₂ j₂' * τ) h
    simpa [← mul_assoc] using h'
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    refine ⟨Equiv.swap j₂ j₂' * π, ?_, by simp [← mul_assoc]⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hπ.2.1]
      exact Equiv.swap_apply_of_ne_of_ne hj₂.symm hj₂'.symm
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, hπ.2.2, Equiv.swap_apply_right]

private lemma mul_card_filter_perm_apply_eq_and_eq {n : ℕ} {i₁ i₂ j₁ j₂ : Fin n}
    (hij : i₁ ≠ i₂) (hjj : j₂ ≠ j₁) :
    n * (n - 1) *
        (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁ ∧ π i₂ = j₂).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
  have hsub :
      (n - 1) * (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁ ∧ π i₂ = j₂).card =
        (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁).card := by
    calc
      (n - 1) * (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁ ∧ π i₂ = j₂).card
          = ∑ k ∈ univ.erase j₁,
              (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁ ∧ π i₂ = k).card := by
            trans (∑ _k ∈ univ.erase j₁,
              (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁ ∧ π i₂ = j₂).card)
            · simp [Finset.card_erase_of_mem (Finset.mem_univ j₁)]
            · exact Finset.sum_congr rfl fun k hk ↦
                card_filter_perm_apply_eq_and_eq i₁ i₂ j₁ j₂ k hjj (Finset.mem_erase.mp hk).1
      _ = (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₁ = j₁).card := by
            rw [← Finset.card_biUnion]
            · congr 1
              ext π
              simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true,
                Finset.mem_filter, true_and]
              constructor
              · rintro ⟨k, _, h1, _⟩
                exact h1
              · intro h1
                refine ⟨π i₂, ?_, h1, rfl⟩
                intro h2
                exact hij (π.injective (h1.trans h2.symm))
            · intro k₁ _ k₂ _ hne
              dsimp only [Function.onFun]
              rw [Finset.disjoint_filter]
              intro π _ h1 h2
              exact hne (h1.2.symm.trans h2.2)
  rw [mul_assoc, hsub, mul_card_filter_perm_apply_eq i₁ j₁]

/-- Indicator-sum expansion of `(numFixedPoints π : ℝ)` over `Fin n`. -/
lemma numFixedPoints_cast_eq_sum {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (numFixedPoints π : ℝ) = ∑ i : Fin n, if π i = i then (1 : ℝ) else 0 := by
  unfold numFixedPoints
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : π i = i <;> simp [h]

/-! ### E[W] = 1 -/

/-- The expected number of fixed points of a uniform random permutation on `Fin n` is $1$
for $n \ge 1$ (Example 4.21, `SteinIntro.tex:2693`). -/
theorem expected_fixed_points {n : ℕ} (hn : 1 ≤ n) :
    ∫ π, (numFixedPoints π : ℝ) ∂(uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 1 := by
  let N : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hN_pos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (∑ π : Equiv.Perm (Fin n), (numFixedPoints π : ℝ)) = N := by
    simp_rw [numFixedPoints_cast_eq_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ i : Fin n,
        (∑ π : Equiv.Perm (Fin n), if π i = i then (1 : ℝ) else 0) =
          ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i).card : ℝ) := by
      intro i
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun π _ ↦ ?_
      by_cases h : π i = i <;> simp [h]
    simp_rw [hinner]
    let i₀ : Fin n := ⟨0, by omega⟩
    have hconst : ∀ i : Fin n,
        ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i).card : ℝ) =
          ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₀ = i₀).card : ℝ) := by
      intro i
      have h1 :
          (n : ℝ) * ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i).card : ℝ) = N := by
        dsimp [N]; exact_mod_cast mul_card_filter_perm_apply_eq i i
      have h2 :
          (n : ℝ) * ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i₀ = i₀).card : ℝ) = N := by
        dsimp [N]; exact_mod_cast mul_card_filter_perm_apply_eq i₀ i₀
      have hn_ne : (n : ℝ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hn_ne (h1.trans h2.symm)
    rw [Finset.sum_congr rfl fun i _ ↦ hconst i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp [N]; exact_mod_cast mul_card_filter_perm_apply_eq i₀ i₀
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, hsum]
  change N⁻¹ * N = 1
  exact inv_mul_cancel₀ hN_pos.ne'

/-! ### E[W²] = 2 -/

/-- The expected value of $W^2$ (number of fixed points squared) of a uniform random permutation
on `Fin n` is $2$ for $n \ge 2$ (Example 4.21, `SteinIntro.tex:2698-2702`). -/
theorem expected_fixed_points_sq {n : ℕ} (hn : 2 ≤ n) :
    ∫ π, ((numFixedPoints π : ℝ) ^ 2)
      ∂(uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 2 := by
  let N : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hN_pos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hrn_ne : (n : ℝ) ≠ 0 := by positivity
  have hrn1_ne : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsq_expand : ∀ π : Equiv.Perm (Fin n),
      (numFixedPoints π : ℝ) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, if π i = i ∧ π j = j then (1 : ℝ) else 0 := by
    intro π
    rw [sq, numFixedPoints_cast_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hi : π i = i <;> by_cases hj : π j = j <;> simp [hi, hj]
  have hinner_sum : ∀ i j : Fin n,
      (∑ π : Equiv.Perm (Fin n), if π i = i ∧ π j = j then (1 : ℝ) else 0) =
        ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i ∧ π j = j).card : ℝ) := by
    intro i j
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun π _ ↦ ?_
    by_cases h : π i = i ∧ π j = j <;> simp [h]
  have hdiag : ∀ i : Fin n,
      ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i ∧ π i = i).card : ℝ) =
        N / (n : ℝ) := by
    intro i
    have heq : (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i ∧ π i = i) =
        univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i := by
      ext π; simp
    rw [heq]
    have hmul :
        (n : ℝ) * ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i).card : ℝ) = N := by
      dsimp [N]; exact_mod_cast mul_card_filter_perm_apply_eq i i
    field_simp [hrn_ne]
    linarith
  have hoff : ∀ i : Fin n, ∀ j ∈ univ.erase i,
      ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i ∧ π j = j).card : ℝ) =
        N / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro i j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hmul :
        (n : ℝ) * ((n : ℝ) - 1) *
            ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i ∧ π j = j).card : ℝ) = N := by
      have hnat := mul_card_filter_perm_apply_eq_and_eq hne.symm hne
      have hn1 : 1 ≤ n := by omega
      have hcast : ((n * (n - 1) *
          (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = i ∧ π j = j).card : ℕ) : ℝ) = N := by
        dsimp [N]; exact_mod_cast hnat
      simpa [Nat.cast_sub hn1] using hcast
    field_simp [hrn_ne, hrn1_ne]
    linarith
  have hsum : (∑ π : Equiv.Perm (Fin n), (numFixedPoints π : ℝ) ^ 2) = 2 * N := by
    simp_rw [hsq_expand]
    rw [Finset.sum_comm]
    have hrow : ∀ i : Fin n,
        (∑ π : Equiv.Perm (Fin n), ∑ j : Fin n, if π i = i ∧ π j = j then (1 : ℝ) else 0) =
          2 * (N / (n : ℝ)) := by
      intro i
      rw [Finset.sum_comm]
      simp_rw [hinner_sum]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag i,
        Finset.sum_congr rfl (hoff i), Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      field_simp [hrn_ne, hrn1_ne]
      ring
    simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hrn_ne]
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, hsum]
  change N⁻¹ * (2 * N) = 2
  field_simp [hN_pos.ne']

/-! ### Characterization of `2 * numTwoCycles` and E[W₂] = 1/2 -/

/-- Twice the number of 2-cycles of $\pi$ equals the number of elements $x$ in an orbit of size 2
($\pi(x) \ne x$ and $\pi(\pi(x)) = x$). -/
theorem two_mul_numTwoCycles_eq_card_filter {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) :
    2 * numTwoCycles π = (univ.filter fun x : α ↦ π x ≠ x ∧ π (π x) = x).card := by
  let S₂ := π.cycleFactorsFinset.filter fun c ↦ c.support.card = 2
  have hbi :
      S₂.biUnion (fun c ↦ c.support) =
        univ.filter (fun x : α ↦ π x ≠ x ∧ π (π x) = x) := by
    ext x
    simp only [S₂, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, ⟨hc_mem, hc_card⟩, hx_supp⟩
      obtain ⟨_, hc_eq⟩ := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc_mem
      have hcx : c x = π x := hc_eq x hx_supp
      have hne : π x ≠ x := by
        rw [← hcx]
        exact Equiv.Perm.mem_support.mp hx_supp
      have hcx_supp : c x ∈ c.support := Equiv.Perm.apply_mem_support.mpr hx_supp
      have hccx : c (c x) = π (π x) := by
        rw [hc_eq (c x) hcx_supp, hcx]
      obtain ⟨u, v, _, rfl⟩ := Equiv.Perm.card_support_eq_two.mp hc_card
      exact ⟨hne, by rw [← hccx, Equiv.swap_apply_self]⟩
    · rintro ⟨hne, hsq⟩
      have hx_ne : x ≠ π x := hne.symm
      refine ⟨Equiv.swap x (π x), ⟨?_, Equiv.Perm.card_support_swap hx_ne⟩, ?_⟩
      · rw [Equiv.Perm.mem_cycleFactorsFinset_iff]
        refine ⟨Equiv.Perm.isCycle_swap hx_ne, fun a ha ↦ ?_⟩
        rw [Equiv.Perm.support_swap hx_ne] at ha
        rcases Finset.mem_insert.mp ha with ha1 | ha'
        · rw [ha1, Equiv.swap_apply_left]
        · rw [Finset.mem_singleton.mp ha', Equiv.swap_apply_right, hsq]
      · rw [Equiv.Perm.support_swap hx_ne]
        exact Finset.mem_insert_self x {π x}
  have hdisj :
      (S₂ : Set (Equiv.Perm α)).Pairwise (fun c₁ c₂ ↦ Disjoint c₁.support c₂.support) := by
    intro c₁ hc₁ c₂ hc₂ hne
    exact (π.cycleFactorsFinset_pairwise_disjoint
      (Finset.mem_filter.mp hc₁).1 (Finset.mem_filter.mp hc₂).1 hne).disjoint_support
  rw [← hbi, Finset.card_biUnion hdisj]
  have hsum : (∑ c ∈ S₂, c.support.card) = ∑ _c ∈ S₂, 2 :=
    Finset.sum_congr rfl fun c hc ↦ (Finset.mem_filter.mp hc).2
  rw [hsum, Finset.sum_const, smul_eq_mul, mul_comm]
  rfl

/-- The expected number of 2-cycles of a uniform random permutation on `Fin n` is $1/2$
for $n \ge 2$ (Example 4.21, `SteinIntro.tex:2701`). -/
theorem expected_two_cycles {n : ℕ} (hn : 2 ≤ n) :
    ∫ π, (numTwoCycles π : ℝ) ∂(uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 1 / 2 := by
  let N : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hN_pos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hrn_ne : (n : ℝ) ≠ 0 := by positivity
  have hrn1_ne : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2_pt : ∀ π : Equiv.Perm (Fin n),
      2 * (numTwoCycles π : ℝ) =
        ∑ i : Fin n, ∑ j ∈ univ.erase i, if π i = j ∧ π j = i then (1 : ℝ) else 0 := by
    intro π
    have hcard : 2 * (numTwoCycles π : ℝ) =
        ((univ.filter fun i : Fin n ↦ π i ≠ i ∧ π (π i) = i).card : ℝ) := by
      exact_mod_cast two_mul_numTwoCycles_eq_card_filter π
    rw [hcard, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with h
    · rw [Nat.cast_one]
      have hmem : π i ∈ univ.erase i := Finset.mem_erase.mpr ⟨h.1, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hmem]
      have h1 : (if π i = π i ∧ π (π i) = i then (1 : ℝ) else 0) = 1 := by simp [h.2]
      have h0 : ∑ j ∈ (univ.erase i).erase (π i),
          (if π i = j ∧ π j = i then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun j hj ↦ by
          split_ifs with h'
          · exact False.elim ((Finset.mem_erase.mp hj).1 h'.1.symm)
          · rfl
      rw [h1, h0, add_zero]
    · rw [Nat.cast_zero]
      symm
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      split_ifs with h'
      · rcases h' with ⟨rfl, hji⟩
        exact False.elim (h ⟨(Finset.mem_erase.mp hj).1, hji⟩)
      · rfl
  have hsum2 : (∑ π : Equiv.Perm (Fin n), 2 * (numTwoCycles π : ℝ)) = N := by
    simp_rw [h2_pt]
    rw [Finset.sum_comm]
    have hrow : ∀ i : Fin n,
        (∑ π : Equiv.Perm (Fin n), ∑ j ∈ univ.erase i,
            if π i = j ∧ π j = i then (1 : ℝ) else 0) = N / (n : ℝ) := by
      intro i
      rw [Finset.sum_comm]
      have hterm : ∀ j ∈ univ.erase i,
          (∑ π : Equiv.Perm (Fin n), if π i = j ∧ π j = i then (1 : ℝ) else 0) =
            N / ((n : ℝ) * ((n : ℝ) - 1)) := by
        intro j hj
        have hne : j ≠ i := (Finset.mem_erase.mp hj).1
        have hflt :
            (∑ π : Equiv.Perm (Fin n), if π i = j ∧ π j = i then (1 : ℝ) else 0) =
              ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j ∧ π j = i).card : ℝ) := by
          rw [Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun π _ ↦ ?_
          by_cases h : π i = j ∧ π j = i <;> simp [h]
        rw [hflt]
        have hnat := mul_card_filter_perm_apply_eq_and_eq hne.symm hne.symm
        have hn1 : 1 ≤ n := by omega
        have hcast : ((n * (n - 1) *
            (univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j ∧ π j = i).card : ℕ) : ℝ) = N := by
          dsimp [N]; exact_mod_cast hnat
        have hmul :
            (n : ℝ) * ((n : ℝ) - 1) *
              ((univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j ∧ π j = i).card : ℝ) = N := by
          simpa [Nat.cast_sub hn1] using hcast
        field_simp [hrn_ne, hrn1_ne]
        linarith
      rw [Finset.sum_congr rfl hterm, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      field_simp [hrn_ne, hrn1_ne]
    simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hrn_ne]
  have hsum : (∑ π : Equiv.Perm (Fin n), (numTwoCycles π : ℝ)) = N / 2 := by
    rw [← Finset.mul_sum] at hsum2
    linarith
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum, hsum]
  change N⁻¹ * (N / 2) = 1 / 2
  field_simp [hN_pos.ne']

/-! ### Fixed-point jump counting under multiplication by a transposition -/

private lemma numFixedPoints_mul_swap_add {n : ℕ} (π : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : j ≠ i) :
    numFixedPoints (π * Equiv.swap i j) +
        ((if π i = i then 1 else 0) + (if π j = j then 1 else 0)) =
      numFixedPoints π +
        ((if π j = i then 1 else 0) + (if π i = j then 1 else 0)) := by
  have hsplit : ∀ σ : Equiv.Perm (Fin n),
      numFixedPoints σ =
        (if σ i = i then 1 else 0) +
          ((if σ j = j then 1 else 0) +
            ∑ k ∈ (univ.erase i).erase j, if σ k = k then 1 else 0) := by
    intro σ
    unfold numFixedPoints
    rw [Finset.card_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)]
  have hrest :
      (∑ k ∈ (univ.erase i).erase j, if (π * Equiv.swap i j) k = k then 1 else 0) =
        ∑ k ∈ (univ.erase i).erase j, if π k = k then 1 else 0 := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hsplit (π * Equiv.swap i j), hsplit π, hrest]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  omega

private lemma numFixedPoints_mul_swap_eq_add_one_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : j ≠ i) :
    numFixedPoints (π * Equiv.swap i j) = numFixedPoints π + 1 ↔
      (π i = j ∧ π j ≠ i) ∨ (π j = i ∧ π i ≠ j) := by
  have h_add := numFixedPoints_mul_swap_add π hij
  have hex1 : π i = i → π i ≠ j := fun h1 h2 ↦ hij (h2.symm.trans h1)
  have hex2 : π i = i → π j ≠ i := fun h1 h2 ↦ hij (π.injective (h2.trans h1.symm))
  have hex3 : π j = j → π j ≠ i := fun h1 h2 ↦ hij (h1.symm.trans h2)
  have hex4 : π j = j → π i ≠ j := fun h1 h2 ↦ hij (π.injective (h1.trans h2.symm))
  split_ifs at h_add <;>
    (try exact False.elim (hex1 ‹_› ‹_›)) <;>
    (try exact False.elim (hex2 ‹_› ‹_›)) <;>
    (try exact False.elim (hex3 ‹_› ‹_›)) <;>
    (try exact False.elim (hex4 ‹_› ‹_›)) <;>
    constructor <;> intro h <;> omega

private lemma numFixedPoints_eq_mul_swap_add_one_iff {n : ℕ} (π : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : j ≠ i) :
    numFixedPoints π = numFixedPoints (π * Equiv.swap i j) + 1 ↔
      (π i = i ∧ π j ≠ j) ∨ (π i ≠ i ∧ π j = j) := by
  have h_add := numFixedPoints_mul_swap_add π hij
  have hex1 : π i = i → π i ≠ j := fun h1 h2 ↦ hij (h2.symm.trans h1)
  have hex2 : π i = i → π j ≠ i := fun h1 h2 ↦ hij (π.injective (h2.trans h1.symm))
  have hex3 : π j = j → π j ≠ i := fun h1 h2 ↦ hij (h1.symm.trans h2)
  have hex4 : π j = j → π i ≠ j := fun h1 h2 ↦ hij (π.injective (h1.trans h2.symm))
  split_ifs at h_add <;>
    (try exact False.elim (hex1 ‹_› ‹_›)) <;>
    (try exact False.elim (hex2 ‹_› ‹_›)) <;>
    (try exact False.elim (hex3 ‹_› ‹_›)) <;>
    (try exact False.elim (hex4 ‹_› ‹_›)) <;>
    constructor <;> intro h <;> omega

/-- Sum of upward fixed-point jump indicators over all ordered distinct pairs `(i, j)`. -/
lemma sum_up_jump_eq {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, ∑ j ∈ univ.erase i,
        if numFixedPoints (π * Equiv.swap i j) = numFixedPoints π + 1 then (1 : ℝ) else 0) =
      2 * ((n : ℝ) - (numFixedPoints π : ℝ) - 2 * (numTwoCycles π : ℝ)) := by
  have hterm : ∀ i : Fin n, ∀ j ∈ univ.erase i,
      (if numFixedPoints (π * Equiv.swap i j) = numFixedPoints π + 1 then (1 : ℝ) else 0) =
        (if π i = j ∧ π j ≠ i then (1 : ℝ) else 0) +
          (if π j = i ∧ π i ≠ j then (1 : ℝ) else 0) := by
    intro i j hj
    rw [if_congr (numFixedPoints_mul_swap_eq_add_one_iff π (Finset.mem_erase.mp hj).1) rfl rfl]
    by_cases h1 : π i = j ∧ π j ≠ i <;> by_cases h2 : π j = i ∧ π i ≠ j
    · exact False.elim (h1.2 h2.1)
    · simp [h1]
    · simp [h2]
    · simp [h1, h2]
  have hsplit :
      (∑ i : Fin n, ∑ j ∈ univ.erase i,
          if numFixedPoints (π * Equiv.swap i j) = numFixedPoints π + 1 then (1 : ℝ) else 0) =
        (∑ i : Fin n, ∑ j ∈ univ.erase i, if π i = j ∧ π j ≠ i then (1 : ℝ) else 0) +
          ∑ i : Fin n, ∑ j ∈ univ.erase i, if π j = i ∧ π i ≠ j then (1 : ℝ) else 0 := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl (hterm i)
  have hsymm :
      (∑ i : Fin n, ∑ j ∈ univ.erase i, if π j = i ∧ π i ≠ j then (1 : ℝ) else 0) =
        ∑ i : Fin n, ∑ j ∈ univ.erase i, if π i = j ∧ π j ≠ i then (1 : ℝ) else 0 := by
    have herase : ∀ (f : Fin n → Fin n → ℝ),
        (∀ i : Fin n, f i i = 0) →
        (∑ i : Fin n, ∑ j ∈ univ.erase i, f i j) = ∑ i : Fin n, ∑ j : Fin n, f i j := by
      intro f hf0
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hf0 i, zero_add]
    rw [herase (fun i j ↦ if π j = i ∧ π i ≠ j then (1 : ℝ) else 0) (fun i ↦ by simp),
      herase (fun i j ↦ if π i = j ∧ π j ≠ i then (1 : ℝ) else 0) (fun i ↦ by simp),
      Finset.sum_comm]
  have hinner : ∀ i : Fin n,
      (∑ j ∈ univ.erase i, if π i = j ∧ π j ≠ i then (1 : ℝ) else 0) =
        (1 : ℝ) - (if π i = i then (1 : ℝ) else 0) -
          (if π i ≠ i ∧ π (π i) = i then (1 : ℝ) else 0) := by
    intro i
    by_cases hfix : π i = i
    · simp only [hfix, ↓reduceIte, ne_eq, not_true_eq_false, false_and, sub_self]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      split_ifs with h
      · exact False.elim ((Finset.mem_erase.mp hj).1 h.1.symm)
      · rfl
    · have hmem : π i ∈ univ.erase i := Finset.mem_erase.mpr ⟨hfix, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hmem]
      have h0 :
          ∑ j ∈ (univ.erase i).erase (π i), (if π i = j ∧ π j ≠ i then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun j hj ↦ by
          split_ifs with h
          · exact False.elim ((Finset.mem_erase.mp hj).1 h.1.symm)
          · rfl
      rw [h0, add_zero]
      by_cases h2 : π (π i) = i <;> simp [hfix, h2]
  have h2cyc :
      (∑ i : Fin n, if π i ≠ i ∧ π (π i) = i then (1 : ℝ) else 0) =
        2 * (numTwoCycles π : ℝ) := by
    have hcard : 2 * (numTwoCycles π : ℝ) =
        ((univ.filter fun i : Fin n ↦ π i ≠ i ∧ π (π i) = i).card : ℝ) := by
      exact_mod_cast two_mul_numTwoCycles_eq_card_filter π
    rw [hcard, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : π i ≠ i ∧ π (π i) = i <;> simp [h]
  rw [hsplit, hsymm]
  simp_rw [hinner, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← numFixedPoints_cast_eq_sum, h2cyc]
  ring

/-- Sum of downward fixed-point jump indicators over all ordered distinct pairs `(i, j)`. -/
lemma sum_down_jump_eq {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, ∑ j ∈ univ.erase i,
        if numFixedPoints π = numFixedPoints (π * Equiv.swap i j) + 1 then (1 : ℝ) else 0) =
      2 * ((numFixedPoints π : ℝ) * ((n : ℝ) - (numFixedPoints π : ℝ))) := by
  have hterm : ∀ i : Fin n, ∀ j ∈ univ.erase i,
      (if numFixedPoints π = numFixedPoints (π * Equiv.swap i j) + 1 then (1 : ℝ) else 0) =
        (if π i = i ∧ π j ≠ j then (1 : ℝ) else 0) +
          (if π i ≠ i ∧ π j = j then (1 : ℝ) else 0) := by
    intro i j hj
    rw [if_congr (numFixedPoints_eq_mul_swap_add_one_iff π (Finset.mem_erase.mp hj).1) rfl rfl]
    by_cases h1 : π i = i <;> by_cases h2 : π j = j <;> simp [h1, h2]
  have hsplit :
      (∑ i : Fin n, ∑ j ∈ univ.erase i,
          if numFixedPoints π = numFixedPoints (π * Equiv.swap i j) + 1 then (1 : ℝ) else 0) =
        (∑ i : Fin n, ∑ j ∈ univ.erase i, if π i = i ∧ π j ≠ j then (1 : ℝ) else 0) +
          ∑ i : Fin n, ∑ j ∈ univ.erase i, if π i ≠ i ∧ π j = j then (1 : ℝ) else 0 := by
    simp_rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl (hterm i)
  have h1 : ∀ i : Fin n,
      (∑ j ∈ univ.erase i, if π i = i ∧ π j ≠ j then (1 : ℝ) else 0) =
        (if π i = i then (1 : ℝ) else 0) * ((n : ℝ) - (numFixedPoints π : ℝ)) := by
    intro i
    have heq : (∑ j ∈ univ.erase i, if π i = i ∧ π j ≠ j then (1 : ℝ) else 0) =
        ∑ j : Fin n, if π i = i ∧ π j ≠ j then (1 : ℝ) else 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have : (if π i = i ∧ π i ≠ i then (1 : ℝ) else 0) = 0 := by simp
      rw [this, zero_add]
    rw [heq]
    have hprod : ∀ j : Fin n,
        (if π i = i ∧ π j ≠ j then (1 : ℝ) else 0) =
          (if π i = i then (1 : ℝ) else 0) * ((1 : ℝ) - if π j = j then (1 : ℝ) else 0) := by
      intro j
      by_cases hi : π i = i <;> by_cases hj : π j = j <;> simp [hi, hj]
    simp_rw [hprod, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← numFixedPoints_cast_eq_sum]
  have h2 : ∀ i : Fin n,
      (∑ j ∈ univ.erase i, if π i ≠ i ∧ π j = j then (1 : ℝ) else 0) =
        ((1 : ℝ) - if π i = i then (1 : ℝ) else 0) * (numFixedPoints π : ℝ) := by
    intro i
    have heq : (∑ j ∈ univ.erase i, if π i ≠ i ∧ π j = j then (1 : ℝ) else 0) =
        ∑ j : Fin n, if π i ≠ i ∧ π j = j then (1 : ℝ) else 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have : (if π i ≠ i ∧ π i = i then (1 : ℝ) else 0) = 0 := by simp
      rw [this, zero_add]
    rw [heq]
    have hprod : ∀ j : Fin n,
        (if π i ≠ i ∧ π j = j then (1 : ℝ) else 0) =
          ((1 : ℝ) - if π i = i then (1 : ℝ) else 0) * (if π j = j then (1 : ℝ) else 0) := by
      intro j
      by_cases hi : π i = i <;> by_cases hj : π j = j <;> simp [hi, hj]
    simp_rw [hprod, ← Finset.mul_sum, ← numFixedPoints_cast_eq_sum]
  rw [hsplit]
  simp_rw [h1, h2, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← numFixedPoints_cast_eq_sum]
  ring

end SteinMethod
