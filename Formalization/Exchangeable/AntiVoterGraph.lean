/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.AntiVoter
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Anti-Voter Model Combinatorial and Step Identities (`Formalization.Exchangeable.AntiVoterGraph`)

Graph-combinatorial bounds and one-step transition identities for the anti-voter Markov chain on a
finite simple graph $G = (V, E)$ (Section 3.3.1, `SteinIntro.tex:1099-1219`):
* `totalSpin`: total spin $S(x) = \sum_{v \in V} \sigma(x_v)$ (`SteinIntro.tex:1106-1107`).
* `quadSpin`: quadratic spin sum $\sum_{i \in V} \sum_{j \sim i} \sigma(x_i)\sigma(x_j)$
  (`SteinIntro.tex:1141-1149`).
* `trueCount`: integer count of `+1` (`true`) vertices in configuration `x`.
* Support and bounded-jump properties of `antiVoterStep`, positivity of `kappa G`, vertex count,
  and degree on non-bipartite graphs, first- and second-moment step formulas on `r`-regular graphs
  (`SteinIntro.tex:1126-1152`), and the cut-counting bounds comparing `kappa G` with `quadSpin G x`
  (`SteinIntro.tex:1209-1219`).
-/

open scoped ENNReal

namespace SteinMethod

/-- Total spin $\sum_{v \in V} \sigma(x_v)$ of a Boolean vertex configuration `x : V → Bool`
(`SteinIntro.tex:1106-1107`). -/
def totalSpin {V : Type*} [Fintype V] (x : V → Bool) : ℝ :=
  ∑ v : V, spin (x v)

/-- Quadratic neighbor-spin sum $\sum_{i \in V} \sum_{j \in N(i)} \sigma(x_i)\sigma(x_j)$ along
directed edges of `G` (`SteinIntro.tex:1141-1149`). -/
def quadSpin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool) : ℝ :=
  ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (x i) * spin (x j)

/-- Number of vertices carrying label `true` (`+1` spin) in `x : V → Bool`, cast to `ℤ`
(`SteinIntro.tex:1102-1107`). -/
def trueCount {V : Type*} [Fintype V] (x : V → Bool) : ℤ :=
  ((Finset.univ.filter fun v : V ↦ x v = true).card : ℤ)

private lemma spin_eq_two_ite_sub_one (b : Bool) :
    spin b = 2 * (if b = true then (1 : ℝ) else 0) - 1 := by
  cases b <;> norm_num [spin]

private lemma spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> norm_num [spin]

private lemma sq_neg_spin_sub_spin (b₁ b₂ : Bool) :
    (-spin b₂ - spin b₁) ^ 2 = 2 + 2 * (spin b₁ * spin b₂) := by
  cases b₁ <;> cases b₂ <;> norm_num [spin]

private lemma two_add_two_mul_spin_eq_four_ite (b₁ b₂ : Bool) :
    2 + 2 * (spin b₁ * spin b₂) = 4 * (if b₁ = b₂ then (1 : ℝ) else 0) := by
  cases b₁ <;> cases b₂ <;> norm_num [spin]

private lemma two_add_two_mul_spin_le_four (b₁ b₂ : Bool) :
    2 + 2 * (spin b₁ * spin b₂) ≤ 4 := by
  cases b₁ <;> cases b₂ <;> norm_num [spin]

/-- Total spin equals twice the number of `true` vertices minus `|V|` (`SteinIntro.tex:1102-1107`).
-/
theorem totalSpin_eq_two_trueCount_sub {V : Type*} [Fintype V] (x : V → Bool) :
    totalSpin x = 2 * (trueCount x : ℝ) - (Fintype.card V : ℝ) := by
  unfold totalSpin trueCount
  have hsum :
      (∑ v : V, spin (x v)) =
        ∑ v : V, (2 * (if x v = true then (1 : ℝ) else 0) - 1) :=
    Finset.sum_congr rfl fun v _ ↦ spin_eq_two_ite_sub_one (x v)
  rw [hsum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, Int.cast_natCast]

private lemma exists_adj_update_of_antiVoterStep_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : (Finset.univ : Finset V).Nonempty)
    (hN : ∀ v : V, (G.neighborFinset v).Nonempty)
    {x y : V → Bool} (hy : antiVoterStep G x y ≠ 0) :
    ∃ v u : V, G.Adj v u ∧ y = Function.update x v (!x u) := by
  rw [← PMF.mem_support_iff] at hy
  unfold antiVoterStep at hy
  simp only [hV, ↓reduceDIte, PMF.mem_support_bind_iff] at hy
  rcases hy with ⟨v, _, hv⟩
  simp only [hN v, ↓reduceDIte, PMF.mem_support_map_iff] at hv
  rcases hv with ⟨u, hu, hy_eq⟩
  rw [PMF.mem_support_uniformOfFinset_iff, G.mem_neighborFinset v u] at hu
  exact ⟨v, u, hu, hy_eq.symm⟩

/-- Every configuration reachable in one anti-voter step on a nonempty graph without isolated
vertices contains both a `true` vertex and a `false` vertex (`SteinIntro.tex:1103-1105`). -/
theorem antiVoterStep_support_nonconst {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : (Finset.univ : Finset V).Nonempty)
    (hN : ∀ v : V, (G.neighborFinset v).Nonempty)
    {x y : V → Bool} (hy : antiVoterStep G x y ≠ 0) :
    (∃ a : V, y a = true) ∧ (∃ b : V, y b = false) := by
  obtain ⟨v, u, hadj, rfl⟩ := exists_adj_update_of_antiVoterStep_ne_zero G hV hN hy
  have huv : u ≠ v := (G.ne_of_adj hadj).symm
  cases hxu : x u
  · refine ⟨⟨v, ?_⟩, ⟨u, ?_⟩⟩
    · simp [Function.update_self]
    · simp [Function.update_of_ne huv, hxu]
  · refine ⟨⟨u, ?_⟩, ⟨v, ?_⟩⟩
    · simp [Function.update_of_ne huv, hxu]
    · simp [Function.update_self]

/-- Constant configurations have zero transition probability under `antiVoterStep` when `V` is
nonempty and every vertex has at least one neighbor (`SteinIntro.tex:1103-1105`). -/
theorem antiVoterStep_const_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : (Finset.univ : Finset V).Nonempty)
    (hN : ∀ v : V, (G.neighborFinset v).Nonempty)
    (x : V → Bool) (c : Bool) :
    antiVoterStep G x (fun _ ↦ c) = 0 := by
  by_contra hne
  obtain ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ := antiVoterStep_support_nonconst G hV hN hne
  exact Bool.noConfusion (ha.symm.trans hb)

/-- If `G` is not bipartite, every cut `A ⊆ V` leaves at least one monochromatic edge, so
`1 ≤ kappa G` (`SteinIntro.tex:1209-1215`). -/
theorem one_le_kappa_of_not_isBipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hBip : ¬ G.IsBipartite) :
    1 ≤ kappa G := by
  unfold kappa
  rw [Finset.le_inf'_iff]
  intro A _
  rw [Nat.one_le_iff_ne_zero]
  intro hcard
  rw [Finset.card_filter_eq_zero_iff] at hcard
  apply hBip
  refine ⟨SimpleGraph.Coloring.mk (fun v ↦ if v ∈ A then (0 : Fin 2) else 1) ?_⟩
  intro v w hadj hcol
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have he : s(v, w) ∈ G.edgeFinset := G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadj)
  have hnot : ¬ (s(v, w) ∈ A.sym2 ∨ s(v, w) ∈ Aᶜ.sym2) := hcard s(v, w) he
  by_cases hv : v ∈ A <;> by_cases hw : w ∈ A
  · exact hnot (Or.inl (Finset.mk_mem_sym2_iff.mpr ⟨hv, hw⟩))
  · simp only [hv, hw, ↓reduceIte] at hcol
    exact h01 hcol
  · simp only [hv, hw, ↓reduceIte] at hcol
    exact h01 hcol.symm
  · exact hnot (Or.inr (Finset.mk_mem_sym2_iff.mpr ⟨Finset.mem_compl.mpr hv,
      Finset.mem_compl.mpr hw⟩))

set_option linter.unusedDecidableInType false in
/-- Any non-bipartite finite simple graph has at least `3` vertices (`SteinIntro.tex:1099-1102`).
-/
theorem three_le_card_of_not_isBipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hBip : ¬ G.IsBipartite) :
    3 ≤ Fintype.card V := by
  by_contra hlt
  have hle : Fintype.card V ≤ 2 := by omega
  exact hBip (G.colorable_of_fintype.mono hle)

set_option linter.unusedDecidableInType false in
/-- An `r`-regular non-bipartite finite simple graph has degree `1 ≤ r`
(`SteinIntro.tex:1099-1102`). -/
theorem one_le_degree_of_not_isBipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hReg : G.IsRegularOfDegree r) (hBip : ¬ G.IsBipartite) :
    1 ≤ r := by
  by_contra hlt
  have hr0 : r = 0 := by omega
  apply hBip
  refine ⟨SimpleGraph.Coloring.mk (fun _ ↦ (0 : Fin 2)) ?_⟩
  intro u w hadj
  have hpos : 0 < (G.neighborFinset u).card :=
    Finset.card_pos.mpr ⟨w, (G.mem_neighborFinset u w).mpr hadj⟩
  rw [G.card_neighborFinset_eq_degree, hReg u, hr0] at hpos
  exact (Nat.lt_irrefl 0 hpos).elim

private lemma eq_or_exists_update_of_antiVoterStep_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V → Bool} (hy : antiVoterStep G x y ≠ 0) :
    y = x ∨ ∃ (v : V) (b : Bool), y = Function.update x v b := by
  rw [← PMF.mem_support_iff] at hy
  unfold antiVoterStep at hy
  split_ifs at hy
  · rw [PMF.mem_support_bind_iff] at hy
    rcases hy with ⟨v, _, hv⟩
    split_ifs at hv
    · rw [PMF.mem_support_map_iff] at hv
      rcases hv with ⟨u, _, hy_eq⟩
      exact Or.inr ⟨v, !x u, hy_eq.symm⟩
    · rw [PMF.mem_support_pure_iff] at hv
      exact Or.inl hv
  · rw [PMF.mem_support_pure_iff] at hy
    exact Or.inl hy

private lemma trueCount_update_sub {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) (v : V) (b : Bool) :
    trueCount (Function.update x v b) - trueCount x =
      (if b = true then (1 : ℤ) else 0) - (if x v = true then (1 : ℤ) else 0) := by
  unfold trueCount
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ v),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ v), Function.update_self]
  have hrest :
      (∑ w ∈ Finset.univ.erase v, if Function.update x v b w = true then (1 : ℤ) else 0) =
        ∑ w ∈ Finset.univ.erase v, if x w = true then (1 : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  rw [hrest]
  ring

private lemma totalSpin_update_sub {V : Type*} [Fintype V] [DecidableEq V]
    (x : V → Bool) (v : V) (b : Bool) :
    totalSpin (Function.update x v b) - totalSpin x = spin b - spin (x v) := by
  unfold totalSpin
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ v), Function.update_self]
  have hrest :
      (∑ w ∈ Finset.univ.erase v, spin (Function.update x v b w)) =
        ∑ w ∈ Finset.univ.erase v, spin (x w) := by
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  rw [hrest]
  ring

/-- One step of the anti-voter chain changes `trueCount` by at most `1`
(`SteinIntro.tex:1103-1107`). -/
theorem antiVoterStep_trueCount_abs_sub_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V → Bool} (hy : antiVoterStep G x y ≠ 0) :
    |trueCount y - trueCount x| ≤ 1 := by
  rcases eq_or_exists_update_of_antiVoterStep_ne_zero G hy with rfl | ⟨v, b, rfl⟩
  · norm_num
  · rw [trueCount_update_sub]
    cases b <;> cases x v <;> norm_num

/-- One step of the anti-voter chain changes `totalSpin` by at most `2` in absolute value
(`SteinIntro.tex:1126-1135`). -/
theorem antiVoterStep_totalSpin_abs_sub_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V → Bool} (hy : antiVoterStep G x y ≠ 0) :
    |totalSpin y - totalSpin x| ≤ 2 := by
  rcases eq_or_exists_update_of_antiVoterStep_ne_zero G hy with rfl | ⟨v, b, rfl⟩
  · norm_num
  · rw [totalSpin_update_sub]
    cases b <;> cases x v <;> norm_num [spin]

private lemma antiVoterStep_toReal_regular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hV : (Finset.univ : Finset V).Nonempty)
    (hReg : G.IsRegularOfDegree r) (hr : 0 < r)
    (x y : V → Bool) [DecidableEq (V → Bool)] :
    (antiVoterStep G x y).toReal =
      ∑ v : V, (Fintype.card V : ℝ)⁻¹ *
        ∑ u ∈ G.neighborFinset v,
          if y = Function.update x v (!x u) then (r : ℝ)⁻¹ else 0 := by
  have hN : ∀ v : V, (G.neighborFinset v).Nonempty := by
    intro v
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree, hReg v]
    exact hr
  have hstep : antiVoterStep G x y =
      ∑ v : V, (Fintype.card V : ℝ≥0∞)⁻¹ *
        ∑ u ∈ G.neighborFinset v,
          if y = Function.update x v (!x u) then (r : ℝ≥0∞)⁻¹ else 0 := by
    unfold antiVoterStep
    simp only [hV, ↓reduceDIte]
    rw [PMF.bind_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [PMF.uniformOfFinset_apply_of_mem hV (Finset.mem_univ v), Finset.card_univ]
    simp only [hN v, ↓reduceDIte]
    rw [PMF.map_apply]
    congr 1
    rw [tsum_eq_sum (s := G.neighborFinset v)]
    · refine Finset.sum_congr rfl fun u hu ↦ ?_
      rw [PMF.uniformOfFinset_apply_of_mem (hN v) hu, G.card_neighborFinset_eq_degree, hReg v]
      by_cases hyu : y = Function.update x v (!x u) <;> simp [hyu]
    · intro u hu
      by_cases hyu : y = Function.update x v (!x u)
      · simp [hyu, PMF.uniformOfFinset_apply_of_notMem (hN v) hu]
      · simp [hyu]
  have hcard_inv : (Fintype.card V : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [ENNReal.inv_ne_top, Nat.cast_ne_zero, ← Finset.card_univ]
    exact (Finset.card_pos.mpr hV).ne'
  have hr_inv : (r : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [ENNReal.inv_ne_top, Nat.cast_ne_zero]
    exact hr.ne'
  have hite_ne_top : ∀ v u : V,
      (if y = Function.update x v (!x u) then (r : ℝ≥0∞)⁻¹ else 0) ≠ ∞ := by
    intro v u
    split_ifs
    · exact hr_inv
    · simp
  rw [hstep, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_sum]
    · congr 1
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      split_ifs
      · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
      · simp
    · exact fun u _ ↦ hite_ne_top v u
  · intro v _
    exact ENNReal.mul_ne_top hcard_inv (ENNReal.sum_ne_top.mpr fun u _ ↦ hite_ne_top v u)

/-- Expectation of `F` after one `antiVoterStep` on an `r`-regular graph (`r > 0`) as the normalized
double sum over directed edges `(v, u)` (`SteinIntro.tex:1103-1105`, `1126-1149`). -/
theorem sum_antiVoterStep_toReal_mul {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hV : (Finset.univ : Finset V).Nonempty)
    (hReg : G.IsRegularOfDegree r) (hr : 0 < r)
    (x : V → Bool) (F : (V → Bool) → ℝ) :
    (∑ y : V → Bool, (antiVoterStep G x y).toReal * F y) =
      ((Fintype.card V : ℝ) * (r : ℝ))⁻¹ *
        ∑ v : V, ∑ u ∈ G.neighborFinset v, F (Function.update x v (!x u)) := by
  classical
  calc
    (∑ y : V → Bool, (antiVoterStep G x y).toReal * F y) =
        ∑ y : V → Bool,
          (∑ v : V, (Fintype.card V : ℝ)⁻¹ *
            ∑ u ∈ G.neighborFinset v,
              if y = Function.update x v (!x u) then (r : ℝ)⁻¹ else 0) * F y := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [antiVoterStep_toReal_regular G hV hReg hr x y]
    _ = ∑ y : V → Bool, ∑ v : V,
          (Fintype.card V : ℝ)⁻¹ *
            ∑ u ∈ G.neighborFinset v,
              (if y = Function.update x v (!x u) then (r : ℝ)⁻¹ else 0) * F y := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [mul_assoc, Finset.sum_mul]
    _ = ∑ v : V, (Fintype.card V : ℝ)⁻¹ *
          ∑ y : V → Bool, ∑ u ∈ G.neighborFinset v,
            (if y = Function.update x v (!x u) then (r : ℝ)⁻¹ else 0) * F y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [← Finset.mul_sum]
    _ = ∑ v : V, (Fintype.card V : ℝ)⁻¹ *
          ∑ u ∈ G.neighborFinset v, (r : ℝ)⁻¹ * F (Function.update x v (!x u)) := by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [Finset.sum_eq_single (Function.update x v (!x u))]
      · simp
      · intro y _ hy
        simp [hy]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    _ = ∑ v : V, ((Fintype.card V : ℝ)⁻¹ * (r : ℝ)⁻¹) *
          ∑ u ∈ G.neighborFinset v, F (Function.update x v (!x u)) := by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [← Finset.mul_sum, mul_assoc]
    _ = ((Fintype.card V : ℝ) * (r : ℝ))⁻¹ *
          ∑ v : V, ∑ u ∈ G.neighborFinset v, F (Function.update x v (!x u)) := by
      rw [← Finset.mul_sum, mul_inv_rev, mul_comm (r : ℝ)⁻¹]

private lemma sum_neighborFinset_const {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hReg : G.IsRegularOfDegree r) (c : ℝ) :
    (∑ v : V, ∑ _u ∈ G.neighborFinset v, c) = (Fintype.card V : ℝ) * (r : ℝ) * c := by
  have hinner : ∀ v : V, (∑ _u ∈ G.neighborFinset v, c) = (r : ℝ) * c := by
    intro v
    rw [Finset.sum_const, G.card_neighborFinset_eq_degree, hReg v, nsmul_eq_mul]
  calc
    (∑ v : V, ∑ _u ∈ G.neighborFinset v, c) = ∑ _v : V, (r : ℝ) * c :=
      Finset.sum_congr rfl fun v _ ↦ hinner v
    _ = (Fintype.card V : ℝ) * (r : ℝ) * c := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

private lemma sum_neighborFinset_right {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hReg : G.IsRegularOfDegree r) (g : V → ℝ) :
    (∑ v : V, ∑ u ∈ G.neighborFinset v, g u) = (r : ℝ) * ∑ u : V, g u := by
  have hswap :
      (∑ v ∈ Finset.univ, ∑ u ∈ G.neighborFinset v, g u) =
        ∑ u ∈ Finset.univ, ∑ _v ∈ G.neighborFinset u, g u := by
    refine Finset.sum_comm' fun v u ↦ ?_
    simp only [Finset.mem_univ, true_and, and_true, G.mem_neighborFinset]
    exact G.adj_comm v u
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_const, G.card_neighborFinset_eq_degree, hReg u, nsmul_eq_mul]

/-- Conditional drift identity $\mathbb{E}[S(X') - S(X) \mid X = x] = -(2/|V|) S(x)$ for one step of
the anti-voter chain on an `r`-regular graph (`SteinIntro.tex:1126-1133`). -/
theorem sum_antiVoterStep_sub_totalSpin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hV : (Finset.univ : Finset V).Nonempty)
    (hReg : G.IsRegularOfDegree r) (hr : 0 < r) (x : V → Bool) :
    (∑ y : V → Bool, (antiVoterStep G x y).toReal * (totalSpin y - totalSpin x)) =
      -(2 / (Fintype.card V : ℝ)) * totalSpin x := by
  rw [sum_antiVoterStep_toReal_mul G hV hReg hr x (fun y ↦ totalSpin y - totalSpin x)]
  have hdiff :
      (∑ v : V, ∑ u ∈ G.neighborFinset v,
          (totalSpin (Function.update x v (!x u)) - totalSpin x)) =
        -(2 * (r : ℝ) * totalSpin x) := by
    have hcongr :
        (∑ v : V, ∑ u ∈ G.neighborFinset v,
            (totalSpin (Function.update x v (!x u)) - totalSpin x)) =
          ∑ v : V, ∑ u ∈ G.neighborFinset v, (-spin (x u) - spin (x v)) := by
      refine Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
      rw [totalSpin_update_sub, spin_not]
    have hleft :
        (∑ v : V, ∑ _u ∈ G.neighborFinset v, spin (x v)) = (r : ℝ) * totalSpin x := by
      unfold totalSpin
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Finset.sum_const, G.card_neighborFinset_eq_degree, hReg v, nsmul_eq_mul]
    have hright :
        (∑ v : V, ∑ u ∈ G.neighborFinset v, -spin (x u)) = -((r : ℝ) * totalSpin x) := by
      rw [sum_neighborFinset_right G hReg (fun u ↦ -spin (x u)), Finset.sum_neg_distrib]
      unfold totalSpin
      ring
    calc
      (∑ v : V, ∑ u ∈ G.neighborFinset v,
          (totalSpin (Function.update x v (!x u)) - totalSpin x)) =
          (∑ v : V, ∑ u ∈ G.neighborFinset v, -spin (x u)) -
            ∑ v : V, ∑ _u ∈ G.neighborFinset v, spin (x v) := by
        rw [hcongr, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [Finset.sum_sub_distrib]
      _ = -(2 * (r : ℝ) * totalSpin x) := by
        rw [hleft, hright]
        ring
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  rw [hdiff, mul_inv_rev, div_eq_mul_inv]
  calc
    (r : ℝ)⁻¹ * (Fintype.card V : ℝ)⁻¹ * -(2 * (r : ℝ) * totalSpin x) =
        -((r : ℝ)⁻¹ * (r : ℝ)) * (2 * (Fintype.card V : ℝ)⁻¹ * totalSpin x) := by ring
    _ = -(2 * (Fintype.card V : ℝ)⁻¹) * totalSpin x := by
      rw [inv_mul_cancel₀ hr_ne]
      ring

/-- Conditional second-moment step identity
$\mathbb{E}[(S(X') - S(X))^2 \mid X = x] = 2 + \frac{2}{|V| r} \text{quadSpin}(G, x)$ on an
`r`-regular graph (`SteinIntro.tex:1141-1149`). -/
theorem sum_antiVoterStep_sq_sub_totalSpin {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hV : (Finset.univ : Finset V).Nonempty)
    (hReg : G.IsRegularOfDegree r) (hr : 0 < r) (x : V → Bool) :
    (∑ y : V → Bool, (antiVoterStep G x y).toReal * (totalSpin y - totalSpin x) ^ 2) =
      2 + 2 / ((Fintype.card V : ℝ) * (r : ℝ)) * quadSpin G x := by
  rw [sum_antiVoterStep_toReal_mul G hV hReg hr x (fun y ↦ (totalSpin y - totalSpin x) ^ 2)]
  have hsq :
      (∑ v : V, ∑ u ∈ G.neighborFinset v,
          (totalSpin (Function.update x v (!x u)) - totalSpin x) ^ 2) =
        2 * ((Fintype.card V : ℝ) * (r : ℝ)) + 2 * quadSpin G x := by
    have hcongr :
        (∑ v : V, ∑ u ∈ G.neighborFinset v,
            (totalSpin (Function.update x v (!x u)) - totalSpin x) ^ 2) =
          ∑ v : V, ∑ u ∈ G.neighborFinset v, (2 + 2 * (spin (x v) * spin (x u))) := by
      refine Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun u _ ↦ ?_
      rw [totalSpin_update_sub, spin_not, sq_neg_spin_sub_spin]
    calc
      (∑ v : V, ∑ u ∈ G.neighborFinset v,
          (totalSpin (Function.update x v (!x u)) - totalSpin x) ^ 2) =
          (∑ v : V, ∑ _u ∈ G.neighborFinset v, (2 : ℝ)) +
            ∑ v : V, ∑ u ∈ G.neighborFinset v, 2 * (spin (x v) * spin (x u)) := by
        rw [hcongr, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ ↦ ?_
        rw [Finset.sum_add_distrib]
      _ = 2 * ((Fintype.card V : ℝ) * (r : ℝ)) + 2 * quadSpin G x := by
        rw [sum_neighborFinset_const G hReg 2]
        unfold quadSpin
        rw [Finset.mul_sum]
        have hquad :
            (∑ v : V, ∑ u ∈ G.neighborFinset v, 2 * (spin (x v) * spin (x u))) =
              ∑ i : V, 2 * ∑ j ∈ G.neighborFinset i, spin (x i) * spin (x j) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]
        rw [hquad]
        ring
  have hcard_ne : (Fintype.card V : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero, ← Finset.card_univ]
    exact (Finset.card_pos.mpr hV).ne'
  have hr_ne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hnr_ne : (Fintype.card V : ℝ) * (r : ℝ) ≠ 0 := mul_ne_zero hcard_ne hr_ne
  rw [hsq, div_eq_mul_inv]
  calc
    ((Fintype.card V : ℝ) * (r : ℝ))⁻¹ *
        (2 * ((Fintype.card V : ℝ) * (r : ℝ)) + 2 * quadSpin G x) =
        2 * (((Fintype.card V : ℝ) * (r : ℝ))⁻¹ * ((Fintype.card V : ℝ) * (r : ℝ))) +
          2 * ((Fintype.card V : ℝ) * (r : ℝ))⁻¹ * quadSpin G x := by ring
    _ = 2 + 2 * ((Fintype.card V : ℝ) * (r : ℝ))⁻¹ * quadSpin G x := by
      rw [inv_mul_cancel₀ hnr_ne, mul_one]

private lemma two_card_mul_deg_add_two_quadSpin_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hReg : G.IsRegularOfDegree r) (x : V → Bool) :
    2 * (Fintype.card V : ℝ) * (r : ℝ) + 2 * quadSpin G x =
      ∑ i : V, ∑ j ∈ G.neighborFinset i, (2 + 2 * (spin (x i) * spin (x j))) := by
  have hconst := sum_neighborFinset_const G hReg 2
  unfold quadSpin
  calc
    2 * (Fintype.card V : ℝ) * (r : ℝ) + 2 * ∑ i : V, ∑ j ∈ G.neighborFinset i,
        spin (x i) * spin (x j) =
        (∑ i : V, ∑ _j ∈ G.neighborFinset i, (2 : ℝ)) +
          ∑ i : V, ∑ j ∈ G.neighborFinset i, 2 * (spin (x i) * spin (x j)) := by
      have htwo : 2 * (Fintype.card V : ℝ) * (r : ℝ) = (Fintype.card V : ℝ) * (r : ℝ) * 2 := by
        ring
      rw [htwo, ← hconst, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
    _ = ∑ i : V, ∑ j ∈ G.neighborFinset i, (2 + 2 * (spin (x i) * spin (x j))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_add_distrib]

/-- Lower bound $8\kappa(G) \le 2|V|r + 2\,\text{quadSpin}(G, x)$ on an `r`-regular graph by
counting monochromatic edges of the cut $A = \{v \in V : x_v = \text{true}\}$
(`SteinIntro.tex:1209-1219`). -/
theorem eight_mul_kappa_le_two_card_mul_deg_add_two_quadSpin
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hReg : G.IsRegularOfDegree r) (x : V → Bool) :
    8 * (kappa G : ℝ) ≤ 2 * (Fintype.card V : ℝ) * (r : ℝ) + 2 * quadSpin G x := by
  let A : Finset V := Finset.univ.filter fun v : V ↦ x v = true
  let M : Finset (Sym2 V) := G.edgeFinset.filter fun e ↦ e ∈ A.sym2 ∨ e ∈ Aᶜ.sym2
  let S : Finset (V × V) :=
    (Finset.univ ×ˢ Finset.univ).filter fun p ↦ G.Adj p.1 p.2 ∧ x p.1 = x p.2
  have hkappa : kappa G ≤ M.card := by
    unfold kappa
    exact Finset.inf'_le _ (Finset.mem_univ A)
  have hScard : S.card = 2 * M.card := by
    classical
    have hmaps : (S : Set (V × V)).MapsTo (fun p : V × V ↦ s(p.1, p.2)) M := by
      intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      rcases hp with ⟨_, hadj, hxeq⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadj), ?_⟩
      cases hxp1 : x p.1
      · have hxp2 : x p.2 = false := hxeq.symm.trans hxp1
        right
        rw [Finset.mk_mem_sym2_iff]
        simp [A, hxp1, hxp2]
      · have hxp2 : x p.2 = true := hxeq.symm.trans hxp1
        left
        rw [Finset.mk_mem_sym2_iff]
        simp [A, hxp1, hxp2]
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib_card : ∀ e ∈ M, (S.filter fun p : V × V ↦ s(p.1, p.2) = e).card = 2 :=
      Sym2.ind fun a b hab ↦ by
        rw [Finset.mem_filter] at hab
        rcases hab with ⟨hedge, hcut⟩
        have hadj : G.Adj a b := G.mem_edgeSet.mp (G.mem_edgeFinset.mp hedge)
        have hab_ne : a ≠ b := G.ne_of_adj hadj
        have hxab : x a = x b := by
          rcases hcut with hA | hAc
          · rw [Finset.mk_mem_sym2_iff] at hA
            have ha : x a = true := (Finset.mem_filter.mp hA.1).2
            have hb : x b = true := (Finset.mem_filter.mp hA.2).2
            exact ha.trans hb.symm
          · rw [Finset.mk_mem_sym2_iff, Finset.mem_compl, Finset.mem_compl] at hAc
            have ha : ¬ x a = true :=
              fun h ↦ hAc.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩)
            have hb : ¬ x b = true :=
              fun h ↦ hAc.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ b, h⟩)
            cases hxa : x a <;> cases hxb : x b
            · rfl
            · exact (hb hxb).elim
            · exact (ha hxa).elim
            · exact (ha hxa).elim
        have hfib : (S.filter fun p : V × V ↦ s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
          ext ⟨u, v⟩
          simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
            Sym2.eq, Sym2.rel_iff, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
          constructor
          · rintro ⟨_, huv⟩
            exact huv
          · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · exact ⟨⟨hadj, hxab⟩, Or.inl ⟨rfl, rfl⟩⟩
            · exact ⟨⟨hadj.symm, hxab.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
        rw [hfib]
        exact Finset.card_pair fun hpair ↦ hab_ne (Prod.mk.inj hpair).1
    rw [Finset.sum_const_nat hfib_card, mul_comm]
  have hsum_eq :
      (∑ i : V, ∑ j ∈ G.neighborFinset i, (if x i = x j then (1 : ℝ) else 0)) =
        (S.card : ℝ) := by
    dsimp only [S]
    rw [Finset.natCast_card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    trans ∑ j ∈ G.neighborFinset i, (if G.Adj i j ∧ x i = x j then (1 : ℝ) else 0)
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hadj : G.Adj i j := (G.mem_neighborFinset i j).mp hj
      simp [hadj]
    · refine Fintype.sum_subset fun j hj ↦ (G.mem_neighborFinset i j).mpr ?_
      by_contra hna
      exact hj (by simp [hna])
  have hrhs :
      2 * (Fintype.card V : ℝ) * (r : ℝ) + 2 * quadSpin G x = 8 * (M.card : ℝ) := by
    rw [two_card_mul_deg_add_two_quadSpin_eq G hReg x]
    have hfour :
        (∑ i : V, ∑ j ∈ G.neighborFinset i, (2 + 2 * (spin (x i) * spin (x j)))) =
          4 * ∑ i : V, ∑ j ∈ G.neighborFinset i, (if x i = x j then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ two_add_two_mul_spin_eq_four_ite (x i) (x j)
    rw [hfour, hsum_eq, hScard, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hkappaR : (kappa G : ℝ) ≤ (M.card : ℝ) := Nat.cast_le.mpr hkappa
  linarith

/-- Upper bound $2|V|r + 2\,\text{quadSpin}(G, x) \le 4|V|r$ on an `r`-regular graph since
$\sigma(x_i)\sigma(x_j) \le 1$ (`SteinIntro.tex:1209-1219`). -/
theorem two_card_mul_deg_add_two_quadSpin_le_four_card_mul_deg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hReg : G.IsRegularOfDegree r) (x : V → Bool) :
    2 * (Fintype.card V : ℝ) * (r : ℝ) + 2 * quadSpin G x ≤
      4 * (Fintype.card V : ℝ) * (r : ℝ) := by
  rw [two_card_mul_deg_add_two_quadSpin_eq G hReg x]
  have hle :
      (∑ i : V, ∑ j ∈ G.neighborFinset i, (2 + 2 * (spin (x i) * spin (x j)))) ≤
        ∑ i : V, ∑ _j ∈ G.neighborFinset i, (4 : ℝ) :=
    Finset.sum_le_sum fun i _ ↦
      Finset.sum_le_sum fun j _ ↦ two_add_two_mul_spin_le_four (x i) (x j)
  have hconst := sum_neighborFinset_const G hReg 4
  linarith

end SteinMethod
