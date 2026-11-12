/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.Exchangeable
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Combinatorial Permutation-Swap Pair (`Formalization.Concentration.CombinatorialPair`)

Develops the transposition-coupling machinery and Stein-pair verification for **Example 7.5**
(`SteinIntro.tex:3597-3611`; `ISSUE-TYPO-7.5`, `ISSUE-7.5`, ruling `D7`):

* `combinatorial_isSteinPair_restricted` (**Example 7.5** restricted to $n \ge 3$,
  `Ex7_5_steinPair_restricted`, `SteinIntro.tex:3597-3611`): $\mathbb{E}[W] = 0$ and $(W, W')$ is a
  $\frac{2}{n - 1}$-Stein pair for all $n \ge 3$.
* `not_combinatorial_isSteinPair_n2` (`ISSUE-7.5`): at $n = 2$, $2 / (2 - 1) = 2 > 1$ violates
  `IsSteinPair`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-- Type of transpositions in `Equiv.Perm (Fin n)` (`SteinIntro.tex:3604-3605`). -/
abbrev SwapType (n : ℕ) : Type :=
  {π : Equiv.Perm (Fin n) // π.IsSwap}

/-- Unnormalized combinatorial statistic on `Equiv.Perm (Fin n)` (`SteinIntro.tex:3601-3603`,
`ISSUE-TYPO-7.5`). -/
noncomputable def combStat {n : ℕ} (a : Fin n → Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : ℝ :=
  (∑ i : Fin n, a i (π i)) - (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j

lemma swapType_mul_self {n : ℕ} (τ : SwapType n) : τ.1 * τ.1 = 1 := by
  rcases τ with ⟨_, x, y, _, rfl⟩
  exact Equiv.swap_mul_self x y

/-- Bijection between strict ordered pairs `i < j` in `Fin n` and transpositions `SwapType n`. -/
private noncomputable def swapEquivLt (n : ℕ) :
    {p : Fin n × Fin n // p.1 < p.2} ≃ SwapType n :=
  Equiv.ofBijective
    (fun p ↦ ⟨Equiv.swap p.1.1 p.1.2, ⟨p.1.1, p.1.2, p.2.ne, rfl⟩⟩)
    ⟨by
      rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨i', j'⟩, hij'⟩ h
      have hswap : Equiv.swap i j = Equiv.swap i' j' := Subtype.ext_iff.mp h
      have hsupp : ({i, j} : Finset (Fin n)) = {i', j'} := by
        have h1 := Equiv.Perm.support_swap hij.ne
        have h2 := Equiv.Perm.support_swap hij'.ne
        rw [← h1, ← h2, hswap]
      have hi_mem : i ∈ ({i', j'} : Finset (Fin n)) := by
        rw [← hsupp]; exact Finset.mem_insert_self i {j}
      have hj_mem : j ∈ ({i', j'} : Finset (Fin n)) := by
        rw [← hsupp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem hj_mem
      ext <;> dsimp
      · rcases hi_mem with rfl | rfl
        · rfl
        · rcases hj_mem with rfl | rfl
          · exact False.elim (lt_asymm hij hij')
          · exact False.elim (hij.ne rfl)
      · rcases hj_mem with rfl | rfl
        · rcases hi_mem with rfl | rfl
          · exact False.elim (hij.ne rfl)
          · exact False.elim (lt_asymm hij hij')
        · rfl,
     by
      rintro ⟨π, x, y, hxy, rfl⟩
      rcases lt_trichotomy x y with hlt | rfl | hgt
      · exact ⟨⟨(x, y), hlt⟩, rfl⟩
      · exact absurd rfl hxy
      · refine ⟨⟨(y, x), hgt⟩, ?_⟩
        ext z
        simp [Equiv.swap_comm]⟩

private lemma swapEquivLt_apply_coe (n : ℕ) (q : {p : Fin n × Fin n // p.1 < p.2}) :
    (swapEquivLt n q).1 = Equiv.swap q.1.1 q.1.2 :=
  congrArg Subtype.val (Equiv.ofBijective_apply _ _ q)

/-- Double sum of `g (Equiv.swap i j)` over ordered distinct pairs `i ≠ j` equals twice the sum over
all transpositions `τ : SwapType n`. -/
lemma two_mul_sum_swapType {n : ℕ} (g : Equiv.Perm (Fin n) → ℝ) :
    2 * (∑ τ : SwapType n, g τ.1) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, g (Equiv.swap i j) := by
  have hlt_sum :
      (∑ τ : SwapType n, g τ.1) =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), g (Equiv.swap i j) := by
    rw [← Equiv.sum_comp (swapEquivLt n) (fun τ ↦ g τ.1)]
    simp_rw [swapEquivLt_apply_coe]
    have hbij :
        (∑ q : {p : Fin n × Fin n // p.1 < p.2}, g (Equiv.swap q.1.1 q.1.2)) =
          ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n ↦ p.1 < p.2),
            g (Equiv.swap p.1 p.2) :=
      Finset.sum_bij (fun q _ ↦ q.1)
        (fun q _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun p hp ↦ ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    rw [hbij, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_filter]
  have hgt_sum :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (· < i), g (Equiv.swap i j)) =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), g (Equiv.swap i j) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Equiv.swap_comm]
  have hsplit : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, g (Equiv.swap i j) =
        (∑ j ∈ Finset.univ.filter (i < ·), g (Equiv.swap i j)) +
          ∑ j ∈ Finset.univ.filter (· < i), g (Equiv.swap i j) := by
    intro i
    have hunion :
        Finset.univ.erase i =
          Finset.univ.filter (i < ·) ∪ Finset.univ.filter (· < i) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
        true_and]
      exact ne_iff_lt_or_gt.trans or_comm
    have hdisj :
        Disjoint (Finset.univ.filter (i < ·)) (Finset.univ.filter (· < i)) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact lt_asymm h1 h2
    rw [hunion, Finset.sum_union hdisj]
  simp_rw [hsplit, Finset.sum_add_distrib, hgt_sum, ← hlt_sum]
  ring

lemma two_mul_card_swapType {n : ℕ} (hn : 1 ≤ n) :
    2 * (Fintype.card (SwapType n) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  have h1 := two_mul_sum_swapType (n := n) (fun _ ↦ (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ _)] at h1
  rw [h1, Nat.cast_sub hn]
  push_cast
  rfl

/-- Uniform average over `SwapType n` expressed as $\frac{1}{n(n-1)}\sum_{i}\sum_{j \ne i}$. -/
lemma avg_swapType_eq {n : ℕ} (hn : 2 ≤ n) (g : Equiv.Perm (Fin n) → ℝ) :
    (Fintype.card (SwapType n) : ℝ)⁻¹ * (∑ τ : SwapType n, g τ.1) =
      (1 / ((n : ℝ) * ((n : ℝ) - 1))) *
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, g (Equiv.swap i j) := by
  have hn1 : 1 ≤ n := by omega
  have hrn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrn1_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcard := two_mul_card_swapType hn1
  have hc_pos : (0 : ℝ) < Fintype.card (SwapType n) := by nlinarith [mul_pos hrn_pos hrn1_pos]
  have hsum := two_mul_sum_swapType g
  field_simp [hc_pos.ne', hrn_pos.ne', hrn1_pos.ne']
  linear_combination (∑ τ : SwapType n, g τ.1) * hcard.symm +
    (Fintype.card (SwapType n) : ℝ) * hsum

/-- Uniform expectation of `combStat a` on `Equiv.Perm (Fin n)` is `0` (`SteinIntro.tex:3610`). -/
lemma sum_combStat_eq_zero {n : ℕ} (hn : 1 ≤ n) (a : Fin n → Fin n → ℝ) :
    ∑ π : Equiv.Perm (Fin n), combStat a π = 0 := by
  have hrn_pos : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hfiber_card : ∀ (i j₁ j₂ : Fin n),
      (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₁).card =
        (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₂).card := by
    intro i j₁ j₂
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
  let j₀ : Fin n := ⟨0, by omega⟩
  have hcard_mul : ∀ i : Fin n,
      n * (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₀).card =
        Fintype.card (Equiv.Perm (Fin n)) := by
    intro i
    calc
      n * (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₀).card
          = ∑ j : Fin n, (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j).card := by
            trans (∑ _j : Fin n,
              (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₀).card)
            · simp
            · exact Finset.sum_congr rfl fun j _ ↦ hfiber_card i j₀ j
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
  have hrow_sum : ∀ i : Fin n,
      (∑ π : Equiv.Perm (Fin n), a i (π i)) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (1 / (n : ℝ)) * ∑ j : Fin n, a i j := by
    intro i
    let c : ℕ := (Finset.univ.filter fun π : Equiv.Perm (Fin n) ↦ π i = j₀).card
    have hc_eq : (c : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (1 / (n : ℝ)) := by
      have hcast : (n : ℝ) * (c : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
        exact_mod_cast hcard_mul i
      field_simp [hrn_pos]
      linarith
    have hpart :
        (∑ π : Equiv.Perm (Fin n), a i (π i)) =
          ∑ j : Fin n,
            ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ π i = j), a i (π i) := by
      symm
      rw [← Finset.sum_biUnion]
      · refine Finset.sum_congr ?_ fun _ _ ↦ rfl
        ext π; simp
      · intro j₁ _ j₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_filter]
        intro π _ h1 h2
        exact hne (h1.symm.trans h2)
    rw [hpart]
    have hinner : ∀ j : Fin n,
        (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ π i = j), a i (π i)) =
          (c : ℝ) * a i j := by
      intro j
      have h1 :
          (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ π i = j), a i (π i)) =
            ∑ _π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) ↦ π i = j), a i j :=
        Finset.sum_congr rfl fun π hπ ↦ by rw [(Finset.mem_filter.mp hπ).2]
      rw [h1, Finset.sum_const, nsmul_eq_mul, ← hfiber_card i j₀ j]
    simp_rw [hinner, ← Finset.mul_sum, hc_eq]
  unfold combStat
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp_rw [hrow_sum, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hrn_pos]
  ring

/-- Difference `combStat a (π * swap i j) - combStat a π` for $i \ne j$
(`SteinIntro.tex:3621`). -/
lemma combStat_mul_swap_sub {n : ℕ} (a : Fin n → Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) {i j : Fin n} (hij : j ≠ i) :
    combStat a (π * Equiv.swap i j) - combStat a π =
      a i (π j) + a j (π i) - a i (π i) - a j (π j) := by
  unfold combStat
  have hsub :
      (∑ k : Fin n, a k ((π * Equiv.swap i j) k)) - (∑ k : Fin n, a k (π k)) =
        ∑ k : Fin n, (a k (π (Equiv.swap i j k)) - a k (π k)) := by
    rw [← Finset.sum_sub_distrib]
    rfl
  have hrest :
      ∀ k ∈ (Finset.univ.erase i).erase j, a k (π (Equiv.swap i j k)) - a k (π k) = 0 := by
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj, sub_self]
  have hi_sum :
      (∑ k : Fin n, (a k (π (Equiv.swap i j k)) - a k (π k))) =
        (a i (π (Equiv.swap i j i)) - a i (π i)) +
          ((a j (π (Equiv.swap i j j)) - a j (π j)) +
            ∑ k ∈ (Finset.univ.erase i).erase j, (a k (π (Equiv.swap i j k)) - a k (π k))) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)]
  calc
    ((∑ k : Fin n, a k ((π * Equiv.swap i j) k)) -
        (1 / (n : ℝ)) * ∑ k : Fin n, ∑ l : Fin n, a k l) -
        ((∑ k : Fin n, a k (π k)) - (1 / (n : ℝ)) * ∑ k : Fin n, ∑ l : Fin n, a k l)
        = (∑ k : Fin n, a k ((π * Equiv.swap i j) k)) - ∑ k : Fin n, a k (π k) := by ring
    _ = ∑ k : Fin n, (a k (π (Equiv.swap i j k)) - a k (π k)) := hsub
    _ = (a i (π j) - a i (π i)) + ((a j (π i) - a j (π j)) + 0) := by
          rw [hi_sum, Finset.sum_eq_zero hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
    _ = a i (π j) + a j (π i) - a i (π i) - a j (π j) := by ring

lemma sum_erase_perm_apply {n : ℕ} (a : Fin n → Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, a i (π j)) =
      (∑ i : Fin n, ∑ j : Fin n, a i j) - ∑ i : Fin n, a i (π i) := by
  have h1 : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, a i (π j) = (∑ j : Fin n, a i (π j)) - a i (π i) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  have h2 : ∀ i : Fin n, (∑ j : Fin n, a i (π j)) = ∑ j : Fin n, a i j :=
    fun i ↦ Equiv.sum_comp π (a i)
  simp_rw [h1, h2, Finset.sum_sub_distrib]

lemma sum_erase_perm_apply_symm {n : ℕ} (a : Fin n → Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, a j (π i)) =
      (∑ i : Fin n, ∑ j : Fin n, a i j) - ∑ i : Fin n, a i (π i) := by
  have hcomm :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, a j (π i)) =
        ∑ j : Fin n, ∑ i ∈ Finset.univ.erase j, a j (π i) := by
    simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  rw [hcomm, sum_erase_perm_apply]

/-- Conditional expectation given `σ` when `σ` and `τ` are independent with `τ` uniform on
`SwapType n`. -/
lemma combinatorial_condExp_given_sigma
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → SwapType n}
    (hσ_meas : Measurable σ) (hτ_meas : Measurable τ)
    (h_indep : ProbabilityTheory.IndepFun σ τ P)
    (hτ_unif : P.map τ =
      (@PMF.uniformOfFintype (SwapType n) inferInstance
        ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
          ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩).toMeasure)
    (H : Equiv.Perm (Fin n) × SwapType n → ℝ) :
    P[fun ω ↦ H (σ ω, τ ω) | MeasurableSpace.comap σ inferInstance] =ᵐ[P]
      fun ω ↦ (Fintype.card (SwapType n) : ℝ)⁻¹ * ∑ t₀ : SwapType n, H (σ ω, t₀) := by
  have hne : Nonempty (SwapType n) :=
    ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩
  have : DiscreteMeasurableSpace (SwapType n) := inferInstance
  have hmσ := hσ_meas.comap_le
  let g : Equiv.Perm (Fin n) → ℝ :=
    fun π ↦ (Fintype.card (SwapType n) : ℝ)⁻¹ * ∑ t₀ : SwapType n, H (π, t₀)
  have hg_meas : Measurable g := .of_discrete
  have hRHS_sm : StronglyMeasurable[MeasurableSpace.comap σ inferInstance] (g ∘ σ) :=
    (hg_meas.comp (comap_measurable (m := inferInstance) σ)).stronglyMeasurable
  let M : ℝ := ∑ p : Equiv.Perm (Fin n) × SwapType n, |H p|
  have hH_meas : Measurable (fun ω ↦ H (σ ω, τ ω)) :=
    (Measurable.of_discrete (f := H)).comp (hσ_meas.prodMk hτ_meas)
  have hLHS_int : Integrable (fun ω ↦ H (σ ω, τ ω)) P := by
    refine Integrable.of_bound hH_meas.aestronglyMeasurable M (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (H p)) (Finset.mem_univ (σ ω, τ ω))
  have hRHS_int : Integrable (g ∘ σ) P := by
    refine Integrable.of_bound (hg_meas.comp hσ_meas).aestronglyMeasurable
      ((Fintype.card (SwapType n) : ℝ)⁻¹ * M) (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    dsimp [g]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      ∑ t₀ : SwapType n, |H (σ ω, t₀)|
          ≤ ∑ p : Equiv.Perm (Fin n) × SwapType n, |H p| := by
            rw [Fintype.sum_prod_type]
            exact Finset.single_le_sum
              (fun π _ ↦ Finset.sum_nonneg fun t₀ _ ↦ abs_nonneg (H (π, t₀)))
              (Finset.mem_univ (σ ω))
      _ = M := rfl
  have hτ_prob : ∀ t₀ : SwapType n, P.real {ω | τ ω = t₀} = (Fintype.card (SwapType n) : ℝ)⁻¹ := by
    intro t₀
    have hpre : {ω | τ ω = t₀} = τ ⁻¹' {t₀} := rfl
    have hm : P {ω | τ ω = t₀} = (Fintype.card (SwapType n) : ℝ≥0∞)⁻¹ := by
      rw [hpre, ← Measure.map_apply hτ_meas (measurableSet_singleton t₀), hτ_unif,
        PMF.toMeasure_apply_singleton _ t₀ (measurableSet_singleton t₀),
        PMF.uniformOfFintype_apply]
    rw [measureReal_def, hm, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmσ hLHS_int
    (fun s _ _ ↦ hRHS_int.integrableOn) (fun s hs _ ↦ ?_)
    hRHS_sm.aestronglyMeasurable).symm
  rcases hs with ⟨T, hT, rfl⟩
  have hDecomp :
      (σ ⁻¹' T).indicator (fun ω ↦ H (σ ω, τ ω)) =
        fun ω ↦ ∑ t₀ : SwapType n,
          (T.indicator (fun π ↦ H (π, t₀)) (σ ω)) *
            (({t₀} : Set (SwapType n)).indicator 1 (τ ω)) := by
    funext ω
    by_cases hω : σ ω ∈ T
    · simp only [Set.mem_preimage, hω, Set.indicator_of_mem]
      have hterm : ∀ t₀ : SwapType n,
          H (σ ω, t₀) * ({t₀} : Set (SwapType n)).indicator (1 : SwapType n → ℝ) (τ ω) =
            if τ ω = t₀ then H (σ ω, t₀) else 0 := by
        intro t₀
        by_cases ht : τ ω = t₀ <;> simp [ht]
      simp_rw [hterm]
      simp
    · simp [hω]
  have hIntTerm : ∀ t₀ : SwapType n,
      Integrable (fun ω ↦
        (T.indicator (fun π ↦ H (π, t₀)) (σ ω)) *
          (({t₀} : Set (SwapType n)).indicator 1 (τ ω))) P := by
    intro t₀
    have hm1 : Measurable (fun ω ↦ T.indicator (fun π ↦ H (π, t₀)) (σ ω)) :=
      (Measurable.of_discrete (f := T.indicator (fun π ↦ H (π, t₀)))).comp hσ_meas
    have hm2 :
        Measurable (fun ω ↦ ({t₀} : Set (SwapType n)).indicator (1 : SwapType n → ℝ) (τ ω)) :=
      (Measurable.of_discrete (f := ({t₀} : Set (SwapType n)).indicator 1)).comp hτ_meas
    have hM : 0 ≤ M := Finset.sum_nonneg fun p _ ↦ abs_nonneg (H p)
    refine Integrable.of_bound (hm1.mul hm2).aestronglyMeasurable M
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    by_cases hω : σ ω ∈ T
    · by_cases ht : τ ω = t₀
      · subst ht
        simp only [hω, Set.indicator_of_mem, Set.mem_singleton_iff, Pi.one_apply, mul_one]
        exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (H p)) (Finset.mem_univ (σ ω, τ ω))
      · simp [ht, hM]
    · simp [hω, hM]
  symm
  rw [← integral_indicator (hσ_meas hT), hDecomp,
    integral_finsetSum Finset.univ fun t₀ _ ↦ hIntTerm t₀]
  have hFactor : ∀ t₀ : SwapType n,
      ∫ ω, (T.indicator (fun π ↦ H (π, t₀)) (σ ω)) *
          (({t₀} : Set (SwapType n)).indicator 1 (τ ω)) ∂P =
        (Fintype.card (SwapType n) : ℝ)⁻¹ * ∫ ω in σ ⁻¹' T, H (σ ω, t₀) ∂P := by
    intro t₀
    have hf1 : Measurable (T.indicator (fun π ↦ H (π, t₀))) := .of_discrete
    have hf2 : Measurable (({t₀} : Set (SwapType n)).indicator (1 : SwapType n → ℝ)) :=
      .of_discrete
    rw [h_indep.integral_fun_comp_mul_comp hσ_meas.aemeasurable hτ_meas.aemeasurable
      hf1.stronglyMeasurable.aestronglyMeasurable hf2.stronglyMeasurable.aestronglyMeasurable]
    have h2 : ∫ ω, ({t₀} : Set (SwapType n)).indicator (1 : SwapType n → ℝ) (τ ω) ∂P =
        (Fintype.card (SwapType n) : ℝ)⁻¹ := by
      have heq : (fun ω ↦ ({t₀} : Set (SwapType n)).indicator (1 : SwapType n → ℝ) (τ ω)) =
          {ω | τ ω = t₀}.indicator (fun _ ↦ (1 : ℝ)) := by
        funext ω; by_cases ht : τ ω = t₀ <;> simp [ht]
      have hms : MeasurableSet {ω | τ ω = t₀} := hτ_meas (measurableSet_singleton t₀)
      rw [heq, integral_indicator_const (1 : ℝ) hms, smul_eq_mul, mul_one, hτ_prob t₀]
    have h1 : ∫ ω, T.indicator (fun π ↦ H (π, t₀)) (σ ω) ∂P =
        ∫ ω in σ ⁻¹' T, H (σ ω, t₀) ∂P := by
      have heq : (fun ω ↦ T.indicator (fun π ↦ H (π, t₀)) (σ ω)) =
          (σ ⁻¹' T).indicator (fun ω ↦ H (σ ω, t₀)) := by
        funext ω; by_cases hω : σ ω ∈ T <;> simp [hω]
      rw [heq, integral_indicator (hσ_meas hT)]
    rw [h1, h2, mul_comm]
  simp_rw [hFactor, ← Finset.mul_sum]
  have hIntHt : ∀ t₀ : SwapType n, Integrable (fun ω ↦ H (σ ω, t₀)) P := by
    intro t₀
    refine Integrable.of_bound ((Measurable.of_discrete (f := fun π ↦ H (π, t₀))).comp
      hσ_meas).aestronglyMeasurable M (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (H p)) (Finset.mem_univ (σ ω, t₀))
  symm
  have hg_comp : g ∘ σ =
      fun ω ↦ (Fintype.card (SwapType n) : ℝ)⁻¹ * ∑ t₀ : SwapType n, H (σ ω, t₀) := rfl
  rw [hg_comp, integral_const_mul,
    integral_finsetSum Finset.univ fun t₀ _ ↦ (hIntHt t₀).integrableOn]

/-- Exchangeability and linear regression $(1 - \frac{2}{n-1}) W$ for the permutation-transposition
pair at any $n \ge 2$ (`SteinIntro.tex:3597-3611`, `D7`). -/
lemma combinatorial_exchangeable_and_linear
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n) (a : Fin n → Fin n → ℝ)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → SwapType n}
    (hσ_meas : Measurable σ) (hτ_meas : Measurable τ)
    (h_indep : ProbabilityTheory.IndepFun σ τ P)
    (hσ_unif : P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
    (hτ_unif : P.map τ =
      (@PMF.uniformOfFintype (SwapType n) inferInstance
        ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
          ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩).toMeasure) :
    let W : Ω → ℝ := fun ω ↦ combStat a (σ ω)
    let W' : Ω → ℝ := fun ω ↦ combStat a (σ ω * (τ ω).1)
    IsExchangeablePair P W W' ∧
      Measurable W ∧
      MemLp W 2 P ∧
      P[W' | MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        (fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω) ∧
      P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        (fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω) := by
  intro W W'
  have hne : Nonempty (SwapType n) :=
    ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩
  have : DiscreteMeasurableSpace (SwapType n) := inferInstance
  let μσ := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  let μτ := (@PMF.uniformOfFintype (SwapType n) inferInstance hne).toMeasure
  let stepInv : Equiv.Perm (Fin n) × SwapType n ≃ Equiv.Perm (Fin n) × SwapType n :=
    { toFun := fun p ↦ (p.1 * p.2.1, p.2)
      invFun := fun p ↦ (p.1 * p.2.1, p.2)
      left_inv := fun p ↦ by simp [mul_assoc, swapType_mul_self]
      right_inv := fun p ↦ by simp [mul_assoc, swapType_mul_self] }
  have hMapPair : P.map (fun ω ↦ (σ ω, τ ω)) = μσ.prod μτ := by
    rw [ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
      hσ_meas.aemeasurable hτ_meas.aemeasurable h_indep, hσ_unif, hτ_unif]
  have hMP_step : MeasurePreserving stepInv (μσ.prod μτ) (μσ.prod μτ) := by
    refine ⟨.of_discrete, ?_⟩
    ext s hs
    rw [Measure.map_apply .of_discrete hs]
    have hsingleton : ∀ p : Equiv.Perm (Fin n) × SwapType n,
        (μσ.prod μτ) {p} =
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ *
            (Fintype.card (SwapType n) : ℝ≥0∞)⁻¹ := by
      intro p
      have hp : ({p} : Set (Equiv.Perm (Fin n) × SwapType n)) = {p.1} ×ˢ {p.2} := by
        ext q; simp [Prod.ext_iff]
      rw [hp, Measure.prod_prod,
        PMF.toMeasure_apply_singleton _ p.1 (measurableSet_singleton p.1),
        PMF.toMeasure_apply_singleton _ p.2 (measurableSet_singleton p.2),
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
    classical
    let fs : Finset (Equiv.Perm (Fin n) × SwapType n) := s.toFinite.toFinset
    let fpre : Finset (Equiv.Perm (Fin n) × SwapType n) := (stepInv ⁻¹' s).toFinite.toFinset
    have hcard_eq : fpre.card = fs.card := by
      refine Finset.card_bij (fun p _ ↦ stepInv p) ?_ ?_ ?_
      · intro p hp
        simpa [fs, fpre] using hp
      · intro p₁ _ p₂ _ h
        exact stepInv.injective h
      · intro q hq
        refine ⟨stepInv.symm q, ?_, stepInv.apply_symm_apply q⟩
        simpa [fs, fpre] using hq
    have hmeas_eq : ∀ ft : Finset (Equiv.Perm (Fin n) × SwapType n),
        (μσ.prod μτ) (↑ft : Set _) =
          ft.card • ((Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ *
            (Fintype.card (SwapType n) : ℝ≥0∞)⁻¹) := by
      intro ft
      induction ft using Finset.induction_on with
      | empty => simp
      | insert p ft hp ih =>
        rw [Finset.coe_insert, Set.insert_eq,
          measure_union (Set.disjoint_singleton_left.mpr (by simpa using hp))
            (measurableSet_singleton p |> fun _ ↦ .of_discrete),
          ih, Finset.card_insert_of_notMem hp, add_nsmul, one_nsmul, hsingleton p, add_comm]
    have hfpre_coe : stepInv ⁻¹' s = (↑fpre : Set _) :=
      (Set.Finite.coe_toFinset (stepInv ⁻¹' s).toFinite).symm
    have hfs_coe : s = (↑fs : Set _) :=
      (Set.Finite.coe_toFinset s.toFinite).symm
    rw [hfpre_coe, hfs_coe, hmeas_eq fpre, hmeas_eq fs, hcard_eq]
  let pairVal : Equiv.Perm (Fin n) × SwapType n → ℝ × ℝ :=
    fun p ↦ (combStat a p.1, combStat a (p.1 * p.2.1))
  have hpairVal_meas : Measurable pairVal := .of_discrete
  have hJ_meas : Measurable (fun ω ↦ (σ ω, τ ω)) := hσ_meas.prodMk hτ_meas
  have hWW'_meas : Measurable (fun ω ↦ (W ω, W' ω)) := hpairVal_meas.comp hJ_meas
  have hExch : IsExchangeablePair P W W' := by
    refine ⟨hWW'_meas.aemeasurable, (measurable_swap.comp hWW'_meas).aemeasurable, ?_⟩
    have hpt : pairVal ∘ stepInv = Prod.swap ∘ pairVal := by
      funext p
      dsimp [pairVal, stepInv]
      rw [mul_assoc, swapType_mul_self, mul_one]
    calc
      P.map (fun ω ↦ (W ω, W' ω))
          = (P.map (fun ω ↦ (σ ω, τ ω))).map pairVal :=
            (Measure.map_map hpairVal_meas hJ_meas).symm
      _ = (μσ.prod μτ).map pairVal := by rw [hMapPair]
      _ = ((μσ.prod μτ).map stepInv).map pairVal := by rw [hMP_step.map_eq]
      _ = (μσ.prod μτ).map (pairVal ∘ stepInv) :=
            Measure.map_map hpairVal_meas .of_discrete
      _ = (μσ.prod μτ).map (Prod.swap ∘ pairVal) := by rw [hpt]
      _ = (P.map (fun ω ↦ (σ ω, τ ω))).map (Prod.swap ∘ pairVal) := by rw [← hMapPair]
      _ = P.map (fun ω ↦ (W' ω, W ω)) :=
            Measure.map_map (measurable_swap.comp hpairVal_meas) hJ_meas
  have hW_meas : Measurable W := (Measurable.of_discrete (f := combStat a)).comp hσ_meas
  have hW2 : MemLp W 2 P := by
    let B : ℝ := ∑ π : Equiv.Perm (Fin n), |combStat a π|
    refine MemLp.of_bound hW_meas.aestronglyMeasurable B (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun π _ ↦ abs_nonneg (combStat a π)) (Finset.mem_univ (σ ω))
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := (hExch.fst_identDistrib_snd).integrable_snd hW_int
  have hCondDiff_sigma :
      P[fun ω ↦ W' ω - W ω | MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        fun ω ↦ -(2 / ((n : ℝ) - 1)) * W ω := by
    have h1 := combinatorial_condExp_given_sigma P hn hσ_meas hτ_meas h_indep hτ_unif
      (fun p ↦ combStat a (p.1 * p.2.1) - combStat a p.1)
    have hrn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hrn1_pos : 0 < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    filter_upwards [h1] with ω hω
    rw [hω]
    have havg := avg_swapType_eq hn (fun τπ ↦ combStat a (σ ω * τπ) - combStat a (σ ω))
    rw [havg]
    have hsum_ij :
        (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
            (combStat a (σ ω * Equiv.swap i j) - combStat a (σ ω))) =
          -2 * (n : ℝ) * combStat a (σ ω) := by
      have hcongr : ∀ i : Fin n,
          (∑ j ∈ Finset.univ.erase i,
              (combStat a (σ ω * Equiv.swap i j) - combStat a (σ ω))) =
            ∑ j ∈ Finset.univ.erase i,
              (a i (σ ω j) + a j (σ ω i) - a i (σ ω i) - a j (σ ω j)) :=
        fun i ↦ Finset.sum_congr rfl fun j hj ↦
          combStat_mul_swap_sub a (σ ω) (Finset.mem_erase.mp hj).1
      simp_rw [hcongr, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      have hs1 := sum_erase_perm_apply a (σ ω)
      have hs2 := sum_erase_perm_apply_symm a (σ ω)
      have hs3 : (∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, a i (σ ω i)) =
          ((n : ℝ) - 1) * ∑ i : Fin n, a i (σ ω i) := by
        have hn1 : 1 ≤ n := by omega
        simp [Finset.card_erase_of_mem (Finset.mem_univ _), Nat.cast_sub hn1, Finset.mul_sum]
      have hs4 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, a j (σ ω j)) =
          ((n : ℝ) - 1) * ∑ i : Fin n, a i (σ ω i) := by
        simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [hs1, hs2, hs3, hs4]
      unfold combStat
      field_simp [hrn_pos.ne']
      ring
    rw [hsum_ij]
    dsimp [W]
    field_simp [hrn_pos.ne', hrn1_pos.ne']
  have hW_sm_sigma : StronglyMeasurable[MeasurableSpace.comap σ inferInstance] W :=
    ((Measurable.of_discrete (f := combStat a)).comp
      (comap_measurable (m := inferInstance) σ)).stronglyMeasurable
  have hCondW_sigma : P[W | MeasurableSpace.comap σ inferInstance] = W :=
    condExp_of_stronglyMeasurable hσ_meas.comap_le hW_sm_sigma hW_int
  have hSub_sigma := condExp_sub hW'_int hW_int (MeasurableSpace.comap σ inferInstance)
  have hCond_sigma :
      P[W' | MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω := by
    filter_upwards [hCondDiff_sigma, hSub_sigma] with ω h1 h2
    have h3 := h2.symm.trans h1
    rw [Pi.sub_apply, hCondW_sigma] at h3
    linarith
  have hmW_le_σ :
      MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap σ inferInstance := by
    change MeasurableSpace.comap (combStat a ∘ σ) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.of_discrete (f := combStat a)).comap_le
  have hW_sm_W : StronglyMeasurable[MeasurableSpace.comap W inferInstance] W :=
    Measurable.stronglyMeasurable (comap_measurable (m := inferInstance) W)
  have hCond_W :
      P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω := by
    have htower :
        P[P[W' | MeasurableSpace.comap σ inferInstance] |
            MeasurableSpace.comap W inferInstance] =ᵐ[P]
          P[W' | MeasurableSpace.comap W inferInstance] :=
      condExp_condExp_of_le hmW_le_σ hσ_meas.comap_le
    have hcongr :
        P[P[W' | MeasurableSpace.comap σ inferInstance] |
            MeasurableSpace.comap W inferInstance] =ᵐ[P]
          P[fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω |
            MeasurableSpace.comap W inferInstance] :=
      condExp_congr_ae hCond_sigma
    have hself :
        P[fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω |
            MeasurableSpace.comap W inferInstance] =
          fun ω ↦ (1 - 2 / ((n : ℝ) - 1)) * W ω :=
      condExp_of_stronglyMeasurable hW_meas.comap_le
        (hW_sm_W.const_mul _) (hW_int.const_mul _)
    exact htower.symm.trans (hcongr.trans (EventuallyEq.of_eq hself))
  exact ⟨hExch, hW_meas, hW2, hCond_sigma, hCond_W⟩

/-- **Example 7.5, Stein-pair property restricted to $n \ge 3$** (`Ex7_5_steinPair_restricted`,
`SteinIntro.tex:3597-3611`; `ISSUE-TYPO-7.5`, `ISSUE-7.5`): for an array
$(a_{ij})_{1 \le i,j \le n}$ with $n \ge 3$, a uniform permutation $\sigma$, and an independent
uniform transposition $\tau$, $\mathbb{E}[W] = 0$ and $(W, W')$ is a $\frac{2}{n - 1}$-Stein
pair. -/
theorem combinatorial_isSteinPair_restricted
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 3 ≤ n) (a : Fin n → Fin n → ℝ)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → {π : Equiv.Perm (Fin n) // π.IsSwap}}
    (hσ_meas : Measurable σ) (hτ_meas : Measurable τ)
    (h_indep : ProbabilityTheory.IndepFun σ τ P)
    (hσ_unif : P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
    (hτ_unif : P.map τ =
      (@PMF.uniformOfFintype {π : Equiv.Perm (Fin n) // π.IsSwap} inferInstance
        ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
          ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩).toMeasure) :
    let W : Ω → ℝ :=
      fun ω ↦ (∑ i : Fin n, a i (σ ω i)) - (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    let W' : Ω → ℝ :=
      fun ω ↦
        (∑ i : Fin n, a i ((σ ω * (τ ω).1) i)) -
          (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    ∫ ω, W ω ∂P = 0 ∧ IsSteinPair P (2 / ((n : ℝ) - 1)) W W' := by
  intro W W'
  have hW_def : W = fun ω ↦ combStat a (σ ω) := rfl
  have hW'_def : W' = fun ω ↦ combStat a (σ ω * (τ ω).1) := rfl
  rw [hW_def, hW'_def]
  have hn2 : 2 ≤ n := by omega
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
    combinatorial_exchangeable_and_linear P hn2 a hσ_meas hτ_meas h_indep hσ_unif hτ_unif
  have hrn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha_pos : 0 < 2 / ((n : ℝ) - 1) := div_pos zero_lt_two (by linarith)
  have ha_le1 : 2 / ((n : ℝ) - 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  exact ⟨hMean, hExch, ha_pos, ha_le1, hW_meas, hW2.integrable one_le_two, hCond_W⟩

/-- **Counterexample to the printed Example 7.5 Stein-pair claim at $n = 2$** (`ISSUE-7.5`,
`SteinIntro.tex:3609-3611`): at $n = 2$, $a = 2 / (2 - 1) = 2 > 1$ violates `IsSteinPair` on every
probability space. -/
theorem not_combinatorial_isSteinPair_n2 :
    ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (a : Fin 2 → Fin 2 → ℝ)
        {σ : Ω → Equiv.Perm (Fin 2)} {τ : Ω → {π : Equiv.Perm (Fin 2) // π.IsSwap}},
        Measurable σ →
        Measurable τ →
        ProbabilityTheory.IndepFun σ τ P →
        P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin 2))).toMeasure →
        P.map τ =
          (@PMF.uniformOfFintype {π : Equiv.Perm (Fin 2) // π.IsSwap} inferInstance
            ⟨⟨Equiv.swap 0 1,
              ⟨0, 1, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩).toMeasure →
        let W : Ω → ℝ :=
          fun ω ↦ (∑ i : Fin 2, a i (σ ω i)) - (1 / (2 : ℝ)) * ∑ i : Fin 2, ∑ j : Fin 2, a i j
        let W' : Ω → ℝ :=
          fun ω ↦
            (∑ i : Fin 2, a i ((σ ω * (τ ω).1) i)) -
              (1 / (2 : ℝ)) * ∑ i : Fin 2, ∑ j : Fin 2, a i j
        IsSteinPair P (2 / ((2 : ℝ) - 1)) W W') := by
  intro h
  have hne : Nonempty (SwapType 2) :=
    ⟨⟨Equiv.swap 0 1, ⟨0, 1, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩
  set μσ : Measure (Equiv.Perm (Fin 2)) :=
    (PMF.uniformOfFintype (Equiv.Perm (Fin 2))).toMeasure
  set μτ : Measure (SwapType 2) :=
    (@PMF.uniformOfFintype (SwapType 2) inferInstance hne).toMeasure
  have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μτ := PMF.toMeasure.isProbabilityMeasure _
  have hprob : IsProbabilityMeasure (μσ.prod μτ) := inferInstance
  have h1 : (μσ.prod μτ).map Prod.fst = μσ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h2 : (μσ.prod μτ).map Prod.snd = μτ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hindep : ProbabilityTheory.IndepFun
      (Prod.fst : Equiv.Perm (Fin 2) × SwapType 2 → Equiv.Perm (Fin 2))
      (Prod.snd : Equiv.Perm (Fin 2) × SwapType 2 → SwapType 2) (μσ.prod μτ) :=
    ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hSP := @h (Equiv.Perm (Fin 2) × SwapType 2) inferInstance (μσ.prod μτ) hprob
    (fun _ _ ↦ 0) Prod.fst Prod.snd measurable_fst measurable_snd hindep h1 h2
  have ha_le1 : 2 / ((2 : ℝ) - 1) ≤ 1 := hSP.2.2.1
  norm_num at ha_le1

end SteinMethod
