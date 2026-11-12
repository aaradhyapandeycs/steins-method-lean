/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Subgraph.Triangles
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

/-!
# $k$-Cycle Copy Combinatorics and Asymptotics (`Formalization.PoissonSizeBias.Subgraph.Cycles`)

Develops the combinatorial, asymptotic, and counterexample results for Example 4.8 (*$k$-cycles*,
`SteinIntro.tex:2344-2366`, eq. `(4.14)` `\label{125}`; `ISSUE-TYPO-4.8`):

* `ncard_edgeSet_cycleGraph`: for `3 ≤ k`, `(SimpleGraph.cycleGraph k).edgeSet.ncard = k`.
* `not_isIsolated_cycleGraph`: for `3 ≤ k`, `SimpleGraph.cycleGraph k` has no isolated vertices.
* `card_subgraphCopies_cycleGraph`: for `3 ≤ k`,
  `(subgraphCopies (SimpleGraph.cycleGraph k) n).card = n.choose k * (k - 1).factorial / 2`.
* `not_Ex4_8_L2361_printed`: refutation of the printed display `L2361`
  ($|\Gamma| = \binom{n}{k}\frac{(k - 1)!}{2} p^k$) at $k = 3, n = 3, p = 1/2$ (`ISSUE-TYPO-4.8`).
* `card_subgraphCopiesWithDiffEdges_cycleGraph_le`: for `3 ≤ k`, `k ≤ n`,
  `α ∈ subgraphCopies (SimpleGraph.cycleGraph k) n`, and `1 ≤ t < k`,
  $|\Gamma_\alpha^t| \le \binom{k}{k - t} c_t n^{t - 1} \le C_k n^{t - 1}$ (`SteinIntro.tex:2348`).
* `ex4_8_asymptotics`: when $p_n \asymp 1/n$, $\lambda_n \asymp 1$ and the Example 4.8 bound
  `(4.14)` is of exact order $1/n$ (`SteinIntro.tex:2364-2365`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### 1. Edge count and non-isolation of `SimpleGraph.cycleGraph k` (`3 ≤ k`) -/

/-- For `3 ≤ k`, `SimpleGraph.cycleGraph k` has `k` edges (`SteinIntro.tex:2345-2356`). -/
theorem ncard_edgeSet_cycleGraph {k : ℕ} (hk : 3 ≤ k) :
    (SimpleGraph.cycleGraph k).edgeSet.ncard = k := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, by omega⟩
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (SimpleGraph.cycleGraph (m + 3))
  have hdeg : ∀ v : Fin (m + 3), (SimpleGraph.cycleGraph (m + 3)).degree v = 2 :=
    fun _ ↦ SimpleGraph.cycleGraph_degree_three_le
  simp_rw [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- For `3 ≤ k`, `SimpleGraph.cycleGraph k` has no isolated vertices. -/
theorem not_isIsolated_cycleGraph {k : ℕ} (hk : 3 ≤ k) (v : Fin k) :
    ¬ (SimpleGraph.cycleGraph k).IsIsolated v := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, by omega⟩
  intro hiso
  have hadj : (SimpleGraph.cycleGraph (m + 3)).Adj v (v + 1) :=
    SimpleGraph.cycleGraph_adj.mpr (Or.inr (add_sub_cancel_left v 1))
  exact hiso (v + 1) hadj

/-! ### 2. Dihedral automorphisms of `cycleGraph k` and exact copy count $|\Gamma|$ -/

/-- Dihedral permutation on `Fin (m + 3)`: rotation `x ↦ a + x` when `b = true`, reflection
`x ↦ a - x` when `b = false`. -/
def dihedralPerm (m : ℕ) (a : Fin (m + 3)) (b : Bool) : Equiv.Perm (Fin (m + 3)) :=
  if b then Equiv.addLeft a else (Equiv.neg (Fin (m + 3))).trans (Equiv.addLeft a)

@[simp]
theorem dihedralPerm_apply_true (m : ℕ) (a x : Fin (m + 3)) :
    dihedralPerm m a true x = a + x := rfl

@[simp]
theorem dihedralPerm_apply_false (m : ℕ) (a x : Fin (m + 3)) :
    dihedralPerm m a false x = a - x := by simp [dihedralPerm, sub_eq_add_neg]

@[simp]
theorem dihedralPerm_apply_zero (m : ℕ) (a : Fin (m + 3)) (b : Bool) :
    dihedralPerm m a b 0 = a := by cases b <;> simp

private lemma one_add_one_ne_zero_fin_add_three (m : ℕ) :
    (1 : Fin (m + 3)) + 1 ≠ 0 := by
  intro h
  have hval : ((1 : Fin (m + 3)) + 1).val = (0 : Fin (m + 3)).val := congrArg Fin.val h
  have hlt1 : 1 < m + 3 := by omega
  have h1 : (1 : Fin (m + 3)).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt hlt1
  have hlt2 : 2 < m + 3 := by omega
  have h2 : ((1 : Fin (m + 3)) + 1).val = 2 := by rw [Fin.val_add, h1]; exact Nat.mod_eq_of_lt hlt2
  simp [h2] at hval

theorem dihedralPerm_injective (m : ℕ) :
    Function.Injective (fun p : Fin (m + 3) × Bool ↦ dihedralPerm m p.1 p.2) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have ha : a₁ = a₂ := by
    simpa using congrArg (fun σ : Equiv.Perm (Fin (m + 3)) ↦ σ 0) h
  subst ha
  refine Prod.ext rfl ?_
  by_contra hb
  have h1 := congrArg (fun σ : Equiv.Perm (Fin (m + 3)) ↦ σ 1) h
  cases b₁ <;> cases b₂
  · exact hb rfl
  · simp only [dihedralPerm_apply_false, dihedralPerm_apply_true] at h1
    have h2 : (1 : Fin (m + 3)) + 1 = 0 :=
      (by abel : (1 : Fin (m + 3)) + 1 = (a₁ + 1) - (a₁ - 1)).trans (sub_eq_zero.mpr h1.symm)
    exact one_add_one_ne_zero_fin_add_three m h2
  · simp only [dihedralPerm_apply_true, dihedralPerm_apply_false] at h1
    have h2 : (1 : Fin (m + 3)) + 1 = 0 :=
      (by abel : (1 : Fin (m + 3)) + 1 = (a₁ + 1) - (a₁ - 1)).trans (sub_eq_zero.mpr h1)
    exact one_add_one_ne_zero_fin_add_three m h2
  · exact hb rfl

theorem dihedralPerm_adj_iff (m : ℕ) (a : Fin (m + 3)) (b : Bool) (x y : Fin (m + 3)) :
    (SimpleGraph.cycleGraph (m + 3)).Adj (dihedralPerm m a b x) (dihedralPerm m a b y) ↔
      (SimpleGraph.cycleGraph (m + 3)).Adj x y := by
  rw [SimpleGraph.cycleGraph_adj, SimpleGraph.cycleGraph_adj]
  cases b
  · simp only [dihedralPerm_apply_false]
    have h1 : (a - x) - (a - y) = y - x := by abel
    have h2 : (a - y) - (a - x) = x - y := by abel
    rw [h1, h2, or_comm]
  · simp only [dihedralPerm_apply_true]
    have h1 : (a + x) - (a + y) = x - y := by abel
    have h2 : (a + y) - (a + x) = y - x := by abel
    rw [h1, h2]

theorem embedGraph_cycleGraph_dihedralPerm (m : ℕ) (a : Fin (m + 3)) (b : Bool) :
    embedGraph (SimpleGraph.cycleGraph (m + 3)) (dihedralPerm m a b).toEmbedding =
      SimpleGraph.cycleGraph (m + 3) := by
  let σ := dihedralPerm m a b
  ext u v
  obtain ⟨x, rfl⟩ := σ.surjective u
  obtain ⟨y, rfl⟩ := σ.surjective v
  change (embedGraph (SimpleGraph.cycleGraph (m + 3)) σ.toEmbedding).Adj
      (σ.toEmbedding x) (σ.toEmbedding y) ↔
    (SimpleGraph.cycleGraph (m + 3)).Adj (σ x) (σ y)
  rw [embedGraph_adj_apply, dihedralPerm_adj_iff]

private lemma fin_mk_add_one_eq {m r : ℕ} (hr1 : r + 1 < m + 3) :
    (⟨r, Nat.lt_of_succ_lt hr1⟩ : Fin (m + 3)) + 1 = ⟨r + 1, hr1⟩ := by
  ext
  have hlt1 : 1 < m + 3 := by omega
  have h1 : (1 : Fin (m + 3)).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt hlt1
  rw [Fin.val_add, h1]; exact Nat.mod_eq_of_lt hr1

/-- Any permutation `τ` of `Fin (m + 3)` that preserves `cycleGraph (m + 3)` and fixes `0` and `1`
is the identity permutation. -/
private lemma eq_refl_of_cycleGraph_aut_fix_zero_one {m : ℕ}
    (τ : Equiv.Perm (Fin (m + 3)))
    (hτ_adj : ∀ x y : Fin (m + 3),
      (SimpleGraph.cycleGraph (m + 3)).Adj (τ x) (τ y) ↔
        (SimpleGraph.cycleGraph (m + 3)).Adj x y)
    (hτ0 : τ 0 = 0) (hτ1 : τ 1 = 1) :
    τ = Equiv.refl (Fin (m + 3)) := by
  have hall : ∀ r : ℕ, ∀ hr : r < m + 3, τ ⟨r, hr⟩ = ⟨r, hr⟩ := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr
      rcases r with _ | _ | s
      · exact hτ0
      · have h1_eq : (⟨1, hr⟩ : Fin (m + 3)) = 1 := by
          ext; rw [Fin.val_one']; exact (Nat.mod_eq_of_lt hr).symm
        rw [h1_eq, hτ1]
      · let x : Fin (m + 3) := ⟨s, by omega⟩
        let y : Fin (m + 3) := ⟨s + 1, by omega⟩
        let z : Fin (m + 3) := ⟨s + 2, hr⟩
        have hx : τ x = x := ih s (by omega) (by omega)
        have hy : τ y = y := ih (s + 1) (by omega) (by omega)
        have hxy : x + 1 = y := fin_mk_add_one_eq (by omega)
        have hyz : y + 1 = z := fin_mk_add_one_eq hr
        have hadj_zy : (SimpleGraph.cycleGraph (m + 3)).Adj z y :=
          SimpleGraph.cycleGraph_adj.mpr (Or.inl (by rw [← hyz, add_sub_cancel_left]))
        have hadj_τ : (SimpleGraph.cycleGraph (m + 3)).Adj (τ z) y := by
          rw [← hy]; exact (hτ_adj z y).mpr hadj_zy
        rcases SimpleGraph.cycleGraph_adj.mp hadj_τ with hpos | hneg
        · rw [eq_add_of_sub_eq' hpos, hyz]
        · have hτz : τ z = x := by
            calc
              τ z = y - (y - τ z) := by abel
              _ = (x + 1) - 1 := by rw [hneg, ← hxy]
              _ = x := by abel
          have hval : s + 2 = s := congrArg Fin.val (τ.injective (hτz.trans hx.symm))
          omega
  ext ⟨r, hr⟩ : 1
  exact hall r hr

/-- Every permutation `σ` preserving `cycleGraph (m + 3)` is a dihedral permutation. -/
theorem exists_dihedralPerm_of_cycleGraph_aut {m : ℕ}
    (σ : Equiv.Perm (Fin (m + 3)))
    (hσ : ∀ x y : Fin (m + 3),
      (SimpleGraph.cycleGraph (m + 3)).Adj (σ x) (σ y) ↔
        (SimpleGraph.cycleGraph (m + 3)).Adj x y) :
    ∃ p : Fin (m + 3) × Bool, dihedralPerm m p.1 p.2 = σ := by
  let a : Fin (m + 3) := σ 0
  have hadj10 : (SimpleGraph.cycleGraph (m + 3)).Adj 1 0 :=
    SimpleGraph.cycleGraph_adj.mpr (Or.inl (sub_zero 1))
  have hadj_σ : (SimpleGraph.cycleGraph (m + 3)).Adj (σ 1) a := (hσ 1 0).mpr hadj10
  let b : Bool := decide (σ 1 = a + 1)
  have hd0 : dihedralPerm m a b 0 = σ 0 := dihedralPerm_apply_zero m a b
  have hd1 : dihedralPerm m a b 1 = σ 1 := by
    dsimp [b]
    by_cases h1 : σ 1 = a + 1
    · rw [decide_eq_true h1, dihedralPerm_apply_true, h1]
    · rw [decide_eq_false h1, dihedralPerm_apply_false]
      rcases SimpleGraph.cycleGraph_adj.mp hadj_σ with hpos | hneg
      · exact (h1 (eq_add_of_sub_eq' hpos)).elim
      · calc
          a - 1 = a - (a - σ 1) := by rw [hneg]
          _ = σ 1 := by abel
  let d := dihedralPerm m a b
  let τ : Equiv.Perm (Fin (m + 3)) := σ.trans d.symm
  have hτ_adj : ∀ x y : Fin (m + 3),
      (SimpleGraph.cycleGraph (m + 3)).Adj (τ x) (τ y) ↔
        (SimpleGraph.cycleGraph (m + 3)).Adj x y := by
    intro x y
    change (SimpleGraph.cycleGraph (m + 3)).Adj (d.symm (σ x)) (d.symm (σ y)) ↔ _
    rw [← dihedralPerm_adj_iff m a b (d.symm (σ x)) (d.symm (σ y)),
      d.apply_symm_apply, d.apply_symm_apply, hσ]
  have hτ0 : τ 0 = 0 := by change d.symm (σ 0) = 0; rw [← hd0, d.symm_apply_apply]
  have hτ1 : τ 1 = 1 := by change d.symm (σ 1) = 1; rw [← hd1, d.symm_apply_apply]
  have hτ_refl := eq_refl_of_cycleGraph_aut_fix_zero_one τ hτ_adj hτ0 hτ1
  refine ⟨(a, b), ?_⟩
  ext x : 1
  have hx := congrArg (fun π : Equiv.Perm (Fin (m + 3)) ↦ d (π x)) hτ_refl
  simpa [τ] using hx.symm

/-- If two embeddings `f, f₀ : Fin (m + 3) ↪ Fin n` produce the same copy of
`cycleGraph (m + 3)`, then `f = (dihedralPerm m a b).toEmbedding.trans f₀` for a unique
`(a, b)`. -/
theorem embedGraph_cycleGraph_eq_iff {m n : ℕ} (f f₀ : Fin (m + 3) ↪ Fin n) :
    embedGraph (SimpleGraph.cycleGraph (m + 3)) f =
      embedGraph (SimpleGraph.cycleGraph (m + 3)) f₀ ↔
      ∃ p : Fin (m + 3) × Bool,
        f = (dihedralPerm m p.1 p.2).toEmbedding.trans f₀ := by
  let H := SimpleGraph.cycleGraph (m + 3)
  constructor
  · intro heq
    have hrange : ∀ x : Fin (m + 3), f x ∈ Set.range f₀ := by
      intro x
      have hadj : H.Adj x (x + 1) :=
        SimpleGraph.cycleGraph_adj.mpr (Or.inr (add_sub_cancel_left x 1))
      have hadj_f : (embedGraph H f).Adj (f x) (f (x + 1)) :=
        (embedGraph_adj_apply H f x (x + 1)).mpr hadj
      rw [heq] at hadj_f
      rcases hadj_f with ⟨x', _, hx', _, _⟩
      exact ⟨x', hx'⟩
    choose g hg using hrange
    have hg_inj : Function.Injective g := fun x₁ x₂ hgx ↦
      f.injective (by rw [← hg x₁, ← hg x₂, hgx])
    let σ : Equiv.Perm (Fin (m + 3)) :=
      Equiv.ofBijective g ⟨hg_inj, Finite.surjective_of_injective hg_inj⟩
    have hσ_f₀ : ∀ x : Fin (m + 3), f₀ (σ x) = f x := hg
    have hσ_aut : ∀ x y : Fin (m + 3), H.Adj (σ x) (σ y) ↔ H.Adj x y := by
      intro x y
      rw [← embedGraph_adj_apply H f₀ (σ x) (σ y), hσ_f₀, hσ_f₀, ← heq,
        embedGraph_adj_apply H f x y]
    obtain ⟨p, hp⟩ := exists_dihedralPerm_of_cycleGraph_aut σ hσ_aut
    exact ⟨p, by ext x; simp [hp, ← hσ_f₀ x]⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    rw [← embedGraph_embedGraph, embedGraph_cycleGraph_dihedralPerm]

open Classical in
/-- For every `α ∈ subgraphCopies (SimpleGraph.cycleGraph (m + 3)) n`, the fiber of embeddings
`f : Fin (m + 3) ↪ Fin n` with `embedGraph (cycleGraph (m + 3)) f = α` has cardinality
`2 * (m + 3)`. -/
theorem card_fiber_embedGraph_cycleGraph {m n : ℕ} {α : SimpleGraph (Fin n)}
    (hα : α ∈ subgraphCopies (SimpleGraph.cycleGraph (m + 3)) n) :
    (Finset.univ.filter fun f : Fin (m + 3) ↪ Fin n ↦
      embedGraph (SimpleGraph.cycleGraph (m + 3)) f = α).card = 2 * (m + 3) := by
  rcases mem_subgraphCopies.mp hα with ⟨f₀, rfl⟩
  have hcard_dom : (Finset.univ : Finset (Fin (m + 3) × Bool)).card = 2 * (m + 3) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
  rw [← hcard_dom]
  symm
  refine Finset.card_bij
    (fun (p : Fin (m + 3) × Bool) _ ↦ (dihedralPerm m p.1 p.2).toEmbedding.trans f₀) ?_ ?_ ?_
  · intro p _
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (embedGraph_cycleGraph_eq_iff _ f₀).mpr ⟨p, rfl⟩⟩
  · intro p₁ _ p₂ _ h
    apply dihedralPerm_injective m
    ext x : 1
    exact f₀.injective (Function.Embedding.ext_iff.mp h x)
  · intro f hf
    rcases (embedGraph_cycleGraph_eq_iff f f₀).mp (Finset.mem_filter.mp hf).2 with ⟨p, rfl⟩
    exact ⟨p, Finset.mem_univ p, rfl⟩

/-- For `3 ≤ k`, `2` divides `(k - 1).factorial`. -/
theorem two_dvd_factorial_pred {k : ℕ} (hk : 3 ≤ k) :
    2 ∣ (k - 1).factorial :=
  Nat.dvd_factorial (by decide) (by omega)

/-- For `3 ≤ k`, the number of copies of `SimpleGraph.cycleGraph k` in $K_n$ is
$\binom{n}{k} \frac{(k - 1)!}{2}$ (`SteinIntro.tex:2361-2364`; `ISSUE-TYPO-4.8`). -/
theorem card_subgraphCopies_cycleGraph {k n : ℕ} (hk : 3 ≤ k) :
    (subgraphCopies (SimpleGraph.cycleGraph k) n).card =
      n.choose k * (k - 1).factorial / 2 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, by omega⟩
  let H := SimpleGraph.cycleGraph (m + 3)
  have hfiber :
      (Finset.univ : Finset (Fin (m + 3) ↪ Fin n)).card =
        ∑ α ∈ subgraphCopies H n,
          (Finset.univ.filter fun f : Fin (m + 3) ↪ Fin n ↦ embedGraph H f = α).card :=
    Finset.card_eq_sum_card_fiberwise fun f _ ↦ mem_subgraphCopies.mpr ⟨f, rfl⟩
  have hsum :
      ∑ α ∈ subgraphCopies H n,
          (Finset.univ.filter fun f : Fin (m + 3) ↪ Fin n ↦ embedGraph H f = α).card =
        (subgraphCopies H n).card * (2 * (m + 3)) := by
    rw [Finset.sum_congr rfl fun α hα ↦ card_fiber_embedGraph_cycleGraph hα,
      Finset.sum_const, smul_eq_mul]
  have hcard_emb :
      (Finset.univ : Finset (Fin (m + 3) ↪ Fin n)).card =
        n.choose (m + 3) * (m + 3).factorial := by
    rw [Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
      Nat.descFactorial_eq_factorial_mul_choose, mul_comm]
  have hfac_split : (m + 3).factorial = (m + 3) * (m + 2).factorial :=
    Nat.factorial_succ (m + 2)
  obtain ⟨q, hq⟩ := two_dvd_factorial_pred (k := m + 3) (by omega)
  change (m + 2).factorial = 2 * q at hq
  have hm_eq : (subgraphCopies H n).card * (2 * (m + 3)) =
      (n.choose (m + 3) * q) * (2 * (m + 3)) := by
    calc
      (subgraphCopies H n).card * (2 * (m + 3))
        = n.choose (m + 3) * (m + 3).factorial := by rw [← hsum, ← hfiber, hcard_emb]
      _ = n.choose (m + 3) * ((m + 3) * (2 * q)) := by rw [hfac_split, hq]
      _ = (n.choose (m + 3) * q) * (2 * (m + 3)) := by ring
  have hcard_q : (subgraphCopies H n).card = n.choose (m + 3) * q :=
    Nat.eq_of_mul_eq_mul_right (by omega) hm_eq
  have hdiv_q : n.choose (m + 3) * (m + 2).factorial / 2 = n.choose (m + 3) * q := by
    rw [hq, show n.choose (m + 3) * (2 * q) = 2 * (n.choose (m + 3) * q) by ring,
      Nat.mul_div_right _ (by decide)]
  exact hcard_q.trans hdiv_q.symm

/-- Real-cast version of `card_subgraphCopies_cycleGraph` (`SteinIntro.tex:2361-2364`). -/
theorem card_subgraphCopies_cycleGraph_cast {k n : ℕ} (hk : 3 ≤ k) :
    ((subgraphCopies (SimpleGraph.cycleGraph k) n).card : ℝ) =
      (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 := by
  rw [card_subgraphCopies_cycleGraph hk]
  obtain ⟨q, hq⟩ := two_dvd_factorial_pred hk
  have hprod : n.choose k * (k - 1).factorial = 2 * (n.choose k * q) := by rw [hq]; ring
  rw [hprod, Nat.mul_div_right _ (by decide)]
  push_cast; rw [hq]; push_cast; ring

/-- **Counterexample (`ISSUE-TYPO-4.8`)**: the printed equation at `SteinIntro.tex:2361`
($|\Gamma| = \binom{n}{k}\frac{(k - 1)!}{2} p^k$) is false at $k = 3, n = 3, p = 1/2$, where
$|\Gamma| = 1$ while the printed right-hand side equals $1/8$. -/
theorem not_Ex4_8_L2361_printed :
    ¬ ∀ (k n : ℕ) (p : ℝ), 3 ≤ k → k ≤ n → 0 < p → p < 1 →
      ((subgraphCopies (SimpleGraph.cycleGraph k) n).card : ℝ) =
        (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * p ^ k := by
  intro h
  have h3 := h 3 3 (1 / 2) le_rfl le_rfl (by norm_num) (by norm_num)
  rw [card_subgraphCopies_cycleGraph_cast (by decide)] at h3
  norm_num at h3

/-! ### 3. Edge-difference bound $|\Gamma_\alpha^t| \le C_k n^{t - 1}$ -/

/-- If a nonempty proper subset `S` of `Fin (m + 3)` is given, there is an element `i₀ ∈ S`
whose cyclic successor `i₀ + 1` is not in `S`. -/
private lemma exists_mem_add_one_notMem {m : ℕ} {S : Finset (Fin (m + 3))}
    (hne : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ i₀ ∈ S, i₀ + 1 ∉ S := by
  by_contra h
  have h' : ∀ i₀ ∈ S, i₀ + 1 ∈ S := fun i₀ hi₀ ↦
    Classical.byContradiction fun hni ↦ h ⟨i₀, hi₀, hni⟩
  rcases hne with ⟨x₀, hx₀⟩
  have hshift : ∀ r : ℕ, x₀ + r • (1 : Fin (m + 3)) ∈ S := by
    intro r
    induction r with
    | zero => simpa using hx₀
    | succ r ih =>
      rw [succ_nsmul, ← add_assoc]
      exact h' (x₀ + r • (1 : Fin (m + 3))) ih
  have hnsmul_mk : ∀ r : ℕ, ∀ hr : r < m + 3, r • (1 : Fin (m + 3)) = ⟨r, hr⟩ := by
    intro r
    induction r with
    | zero => intro _; ext; simp
    | succ r ih => intro hr; rw [succ_nsmul, ih (Nat.lt_of_succ_lt hr), fin_mk_add_one_eq hr]
  apply hproper
  ext y
  simp only [Finset.mem_univ, iff_true]
  have hy : x₀ + (y - x₀).val • (1 : Fin (m + 3)) = y := by
    rw [hnsmul_mk (y - x₀).val (y - x₀).isLt, Fin.eta]; abel
  rw [← hy]; exact hshift (y - x₀).val

/-- Every edge of `embedGraph (cycleGraph (m + 3)) f` is of the form `s(f i, f (i + 1))` for some
`i : Fin (m + 3)`. -/
private lemma mem_edgeSet_embedGraph_cycleGraph_iff {m n : ℕ}
    (f : Fin (m + 3) ↪ Fin n) (e : Sym2 (Fin n)) :
    e ∈ (embedGraph (SimpleGraph.cycleGraph (m + 3)) f).edgeSet ↔
      ∃ i : Fin (m + 3), e = s(f i, f (i + 1)) := by
  revert e
  refine Sym2.ind fun u v ↦ ?_
  rw [SimpleGraph.mem_edgeSet, embedGraph_adj]
  constructor
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    rcases SimpleGraph.cycleGraph_adj.mp hxy with h1 | h2
    · exact ⟨y, by rw [eq_add_of_sub_eq' h1, Sym2.eq_swap]⟩
    · exact ⟨x, by rw [eq_add_of_sub_eq' h2]⟩
  · rintro ⟨i, heq⟩
    have hadj : (SimpleGraph.cycleGraph (m + 3)).Adj i (i + 1) :=
      SimpleGraph.cycleGraph_adj.mpr (Or.inr (add_sub_cancel_left i 1))
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨i, i + 1, rfl, rfl, hadj⟩
    · exact ⟨i + 1, i, rfl, rfl, hadj.symm⟩

/-- Both endpoints of any edge in `(embedGraph H f).edgeSet` lie in `Finset.univ.map f`. -/
private lemma endpoints_mem_map_of_mem_edgeSet_embedGraph {V : Type*} [Fintype V] {n : ℕ}
    {H : SimpleGraph V} {f : V ↪ Fin n} {u v : Fin n}
    (he : s(u, v) ∈ (embedGraph H f).edgeSet) :
    u ∈ Finset.univ.map f ∧ v ∈ Finset.univ.map f := by
  rw [SimpleGraph.mem_edgeSet, embedGraph_adj] at he
  rcases he with ⟨x, y, rfl, rfl, _⟩
  exact ⟨Finset.mem_map_of_mem f (Finset.mem_univ x),
    Finset.mem_map_of_mem f (Finset.mem_univ y)⟩

/-- If `β = embedGraph (cycleGraph (m + 3)) f_β` has `t` edges not in
`α = embedGraph (cycleGraph (m + 3)) f_α` with `1 ≤ t < m + 3`, then `f_β` maps at least
`(m + 3) - t + 1` vertices of `Fin (m + 3)` into `Finset.univ.map f_α`. -/
private lemma exists_subset_card_succ_mapped_into {m n : ℕ}
    (f_α f_β : Fin (m + 3) ↪ Fin n) {t : ℕ}
    (ht1 : 1 ≤ t) (htk : t < m + 3)
    (hdiff : ((embedGraph (SimpleGraph.cycleGraph (m + 3)) f_β).edgeSet \
      (embedGraph (SimpleGraph.cycleGraph (m + 3)) f_α).edgeSet).ncard = t) :
    ∃ U ∈ (Finset.univ : Finset (Fin (m + 3))).powersetCard ((m + 3) - t + 1),
      ∀ j ∈ U, f_β j ∈ Finset.univ.map f_α := by
  classical
  let H := SimpleGraph.cycleGraph (m + 3)
  let α := embedGraph H f_α
  let β := embedGraph H f_β
  let e_β : Fin (m + 3) → Sym2 (Fin n) := fun i ↦ s(f_β i, f_β (i + 1))
  let S : Finset (Fin (m + 3)) := Finset.univ.filter fun i : Fin (m + 3) ↦ e_β i ∈ α.edgeSet
  have hβ_card : β.edgeSet.ncard = m + 3 := by
    rw [ncard_edgeSet_embedGraph, ncard_edgeSet_cycleGraph (by omega)]
  have hinter_card : (β.edgeSet ∩ α.edgeSet).ncard = (m + 3) - t := by
    have hsub : β.edgeSet ∩ α.edgeSet ⊆ β.edgeSet := Set.inter_subset_left
    have hdiff_eq : β.edgeSet \ (β.edgeSet ∩ α.edgeSet) = β.edgeSet \ α.edgeSet := by
      ext e; simp
    have hnc := Set.ncard_sdiff hsub (Set.toFinite _)
    have hle : (β.edgeSet ∩ α.edgeSet).ncard ≤ m + 3 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans_eq hβ_card
    rw [hdiff_eq, hdiff, hβ_card] at hnc
    omega
  have hinter_sub : β.edgeSet ∩ α.edgeSet ⊆ e_β '' (S : Set (Fin (m + 3))) := by
    intro e ⟨heβ, heα⟩
    obtain ⟨i, rfl⟩ := (mem_edgeSet_embedGraph_cycleGraph_iff f_β e).mp heβ
    exact ⟨i, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, heα⟩), rfl⟩
  have hS_ge : (m + 3) - t ≤ S.card := by
    rw [← hinter_card, ← Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard hinter_sub (Set.toFinite _)).trans
      (Set.ncard_image_le (Set.toFinite _))
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hS_proper : S ≠ Finset.univ := by
    intro huniv
    have hsub_all : β.edgeSet ⊆ α.edgeSet := by
      intro e heβ
      obtain ⟨i, rfl⟩ := (mem_edgeSet_embedGraph_cycleGraph_iff f_β e).mp heβ
      have hiS : i ∈ S := huniv ▸ Finset.mem_univ i
      exact (Finset.mem_filter.mp hiS).2
    have hdiff0 : (β.edgeSet \ α.edgeSet).ncard = 0 := by
      rw [Set.sdiff_eq_empty.mpr hsub_all, Set.ncard_empty]
    have hdiff_t : (β.edgeSet \ α.edgeSet).ncard = t := hdiff
    omega
  obtain ⟨i₀, hi₀_mem, hi₀_succ_not⟩ := exists_mem_add_one_notMem hS_ne hS_proper
  let U_full : Finset (Fin (m + 3)) := insert (i₀ + 1) S
  have hU_full_card : (m + 3) - t + 1 ≤ U_full.card := by
    rw [Finset.card_insert_of_notMem hi₀_succ_not]; omega
  have hU_full_map : ∀ j ∈ U_full, f_β j ∈ Finset.univ.map f_α := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjS
    · exact (endpoints_mem_map_of_mem_edgeSet_embedGraph (Finset.mem_filter.mp hi₀_mem).2).2
    · exact (endpoints_mem_map_of_mem_edgeSet_embedGraph (Finset.mem_filter.mp hjS).2).1
  obtain ⟨U, hU_sub, hU_card⟩ := Finset.exists_subset_card_eq hU_full_card
  exact ⟨U, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ U, hU_card⟩,
    fun j hj ↦ hU_full_map j (hU_sub hj)⟩

/-- Cardinality of functions `g : Fin k → Fin n` sending a subset `U` of size `s` into a subset
`V_α` of size `k`. -/
private lemma card_piFinset_ite_eq {k n : ℕ} {U : Finset (Fin k)} {V_α : Finset (Fin n)}
    (hV : V_α.card = k) :
    (Fintype.piFinset (fun j : Fin k ↦ if j ∈ U then V_α else Finset.univ)).card =
      k ^ U.card * n ^ (k - U.card) := by
  rw [Fintype.card_piFinset]
  have hcard_ite :
      (∏ j : Fin k, (if j ∈ U then V_α else (Finset.univ : Finset (Fin n))).card) =
        ∏ j : Fin k, if j ∈ U then k else n := by
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    split_ifs <;> simp [hV]
  rw [hcard_ite, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 2
  have hcompl : (Finset.univ.filter fun x : Fin k ↦ x ∉ U) = Finset.univ \ U := by ext x; simp
  rw [hcompl, Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ,
    Fintype.card_fin]

/-- Natural-number upper bound on `(subgraphCopiesWithDiffEdges (cycleGraph k) n α t).card` for
`3 ≤ k`, `1 ≤ t < k`, and `α ∈ subgraphCopies (cycleGraph k) n`. -/
theorem card_subgraphCopiesWithDiffEdges_cycleGraph_nat_le {k n : ℕ}
    (hk : 3 ≤ k) {α : SimpleGraph (Fin n)}
    (hα : α ∈ subgraphCopies (SimpleGraph.cycleGraph k) n)
    {t : ℕ} (ht1 : 1 ≤ t) (htk : t < k) :
    (subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph k) n α t).card ≤
      k.choose (k - t + 1) * k ^ (k - t + 1) * n ^ (t - 1) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, by omega⟩
  let H := SimpleGraph.cycleGraph (m + 3)
  rcases mem_subgraphCopies.mp hα with ⟨f_α, rfl⟩
  let V_α : Finset (Fin n) := Finset.univ.map f_α
  have hV_card : V_α.card = m + 3 := by simp [V_α]
  let P_sets : Finset (Finset (Fin (m + 3))) :=
    (Finset.univ : Finset (Fin (m + 3))).powersetCard ((m + 3) - t + 1)
  let Box : Finset (Fin (m + 3)) → Finset (Fin (m + 3) → Fin n) :=
    fun U ↦ Fintype.piFinset (fun j : Fin (m + 3) ↦ if j ∈ U then V_α else Finset.univ)
  let TotalBox : Finset (Fin (m + 3) → Fin n) := P_sets.biUnion Box
  let Γ_t := subgraphCopiesWithDiffEdges H n (embedGraph H f_α) t
  have hβ_fn : ∀ β ∈ Γ_t, ∃ g ∈ TotalBox,
      ∃ h_inj : Function.Injective g, β = embedGraph H ⟨g, h_inj⟩ := by
    intro β hβ
    rcases mem_subgraphCopiesWithDiffEdges.mp hβ with ⟨hβ_mem, hβ_diff⟩
    rcases mem_subgraphCopies.mp hβ_mem with ⟨f_β, rfl⟩
    obtain ⟨U, hU_mem, hU_map⟩ :=
      exists_subset_card_succ_mapped_into f_α f_β ht1 htk hβ_diff
    refine ⟨f_β, Finset.mem_biUnion.mpr ⟨U, hU_mem, ?_⟩, f_β.injective, rfl⟩
    rw [Fintype.mem_piFinset]
    intro j
    split_ifs with hj
    · exact hU_map j hj
    · exact Finset.mem_univ _
  choose g hg_mem hg_inj hg_eq using hβ_fn
  have hcard_le_total : Γ_t.card ≤ TotalBox.card := by
    refine Finset.card_le_card_of_injOn
      (fun β ↦ if hβ : β ∈ Γ_t then g β hβ else fun _ ↦ f_α 0)
      (fun β hβ ↦ by simp only [Finset.mem_coe] at hβ ⊢; simp [hβ, hg_mem β hβ]) ?_
    intro β₁ hβ₁ β₂ hβ₂ heq
    simp only [Finset.mem_coe] at hβ₁ hβ₂
    simp only [hβ₁, hβ₂, ↓reduceDIte] at heq
    rw [hg_eq β₁ hβ₁, hg_eq β₂ hβ₂]
    exact congrArg (embedGraph H) (Function.Embedding.ext (congrFun heq))
  have htotal_le :
      TotalBox.card ≤
        (m + 3).choose ((m + 3) - t + 1) * (m + 3) ^ ((m + 3) - t + 1) * n ^ (t - 1) := by
    calc
      TotalBox.card ≤ ∑ U ∈ P_sets, (Box U).card := Finset.card_biUnion_le
      _ = ∑ U ∈ P_sets, ((m + 3) ^ ((m + 3) - t + 1) * n ^ (t - 1)) := by
          refine Finset.sum_congr rfl fun U hU ↦ ?_
          have hU_card : U.card = (m + 3) - t + 1 := (Finset.mem_powersetCard.mp hU).2
          have hsub : (m + 3) - U.card = t - 1 := by omega
          dsimp [Box]; rw [card_piFinset_ite_eq hV_card, hsub, hU_card]
      _ = (m + 3).choose ((m + 3) - t + 1) * (m + 3) ^ ((m + 3) - t + 1) * n ^ (t - 1) := by
          rw [Finset.sum_const, smul_eq_mul, ← mul_assoc]; simp [P_sets]
  exact hcard_le_total.trans htotal_le

/-- Explicit positive constants `c_cycle k t` and `C_cycle k` for Example 4.8
(`SteinIntro.tex:2346-2349`). -/
def c_cycle (k t : ℕ) : ℝ :=
  (k.choose (k - t + 1) * k ^ (k - t + 1) + 1 : ℝ)

def C_cycle (k : ℕ) : ℝ :=
  (∑ t ∈ Finset.Ico 1 k, (k.choose (k - t) : ℝ) * c_cycle k t) + 1

theorem c_cycle_pos (k t : ℕ) : 0 < c_cycle k t := by unfold c_cycle; positivity

theorem C_cycle_pos (k : ℕ) : 0 < C_cycle k := by
  unfold C_cycle
  have hsum : 0 ≤ ∑ t ∈ Finset.Ico 1 k, (k.choose (k - t) : ℝ) * c_cycle k t :=
    Finset.sum_nonneg fun t _ ↦ mul_nonneg (Nat.cast_nonneg _) (c_cycle_pos k t).le
  linarith

/-- Edge-difference upper bounds for $k$-cycles (`SteinIntro.tex:2347-2349`):
$|\Gamma_\alpha^t| \le \binom{k}{k - t} c_t n^{t - 1} \le C_k n^{t - 1}$ for $1 \le t \le k - 1$. -/
theorem card_subgraphCopiesWithDiffEdges_cycleGraph_le {k n : ℕ}
    (hk : 3 ≤ k) (_hkn : k ≤ n) {α : SimpleGraph (Fin n)}
    (hα : α ∈ subgraphCopies (SimpleGraph.cycleGraph k) n)
    {t : ℕ} (ht : t ∈ Finset.Ico 1 k) :
    ((subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph k) n α t).card : ℝ) ≤
        (k.choose (k - t) : ℝ) * c_cycle k t * (n : ℝ) ^ (t - 1) ∧
      (k.choose (k - t) : ℝ) * c_cycle k t * (n : ℝ) ^ (t - 1) ≤
        C_cycle k * (n : ℝ) ^ (t - 1) := by
  rcases Finset.mem_Ico.mp ht with ⟨ht1, htk⟩
  have hnat := card_subgraphCopiesWithDiffEdges_cycleGraph_nat_le hk hα ht1 htk
  have hcast :
      ((subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph k) n α t).card : ℝ) ≤
        (k.choose (k - t + 1) * k ^ (k - t + 1) : ℝ) * (n : ℝ) ^ (t - 1) := by
    exact_mod_cast hnat
  have hch_pos : 1 ≤ k.choose (k - t) := Nat.choose_pos (by omega)
  have hch_r : (1 : ℝ) ≤ (k.choose (k - t) : ℝ) := by exact_mod_cast hch_pos
  have hc_ge : (k.choose (k - t + 1) * k ^ (k - t + 1) : ℝ) ≤
      (k.choose (k - t) : ℝ) * c_cycle k t := by
    calc
      (k.choose (k - t + 1) * k ^ (k - t + 1) : ℝ)
        ≤ 1 * c_cycle k t := by rw [one_mul]; dsimp [c_cycle]; linarith
      _ ≤ (k.choose (k - t) : ℝ) * c_cycle k t :=
          mul_le_mul_of_nonneg_right hch_r (c_cycle_pos k t).le
  have hC_ge : (k.choose (k - t) : ℝ) * c_cycle k t ≤ C_cycle k := by
    have hle_sum :
        (k.choose (k - t) : ℝ) * c_cycle k t ≤
          ∑ s ∈ Finset.Ico 1 k, (k.choose (k - s) : ℝ) * c_cycle k s :=
      Finset.single_le_sum (f := fun s ↦ (k.choose (k - s) : ℝ) * c_cycle k s)
        (fun s _ ↦ mul_nonneg (Nat.cast_nonneg _) (c_cycle_pos k s).le) ht
    dsimp [C_cycle]; linarith
  exact ⟨hcast.trans (mul_le_mul_of_nonneg_right hc_ge (by positivity)),
    mul_le_mul_of_nonneg_right hC_ge (by positivity)⟩

/-! ### 4. Asymptotics of $\lambda_n$ and the Example 4.8 bound (`SteinIntro.tex:2358-2365`) -/

/-- Two-sided comparison showing that $\lambda = \binom{n}{k}\frac{(k - 1)!}{2}p^k$ is of order
$(np)^k$ (`SteinIntro.tex:2364`): for $k \ge 3$, $2k \le n$, and $p \ge 0$,
$\frac{(np)^k}{2k \cdot 2^k} \le \lambda \le \frac{(np)^k}{2k}$. -/
theorem lam_cycleGraph_bounds {k n : ℕ} (hk : 3 ≤ k) (hn2k : 2 * k ≤ n)
    {p : ℝ} (hp0 : 0 ≤ p) :
    let lam : ℝ := (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * p ^ k
    ((n : ℝ) * p) ^ k / (2 * (k : ℝ) * 2 ^ k) ≤ lam ∧
      lam ≤ ((n : ℝ) * p) ^ k / (2 * (k : ℝ)) := by
  intro lam
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  obtain ⟨hch_lo, hch_hi⟩ := choose_real_bounds_of_two_mul_le hn2k
  have hfac_split : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : k ≠ 0)).symm
  have hfac_pred_pos : (0 : ℝ) < ((k - 1).factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hp_pow : 0 ≤ p ^ k := pow_nonneg hp0 k
  constructor
  · calc
      ((n : ℝ) * p) ^ k / (2 * (k : ℝ) * 2 ^ k)
        = (((n : ℝ) / 2) ^ k / (k.factorial : ℝ)) * ((k - 1).factorial : ℝ) / 2 * p ^ k := by
          rw [hfac_split, mul_pow, div_pow]; field_simp [hk_pos.ne', hfac_pred_pos.ne']
      _ ≤ lam := by
          refine mul_le_mul_of_nonneg_right ?_ hp_pow
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hch_lo hfac_pred_pos.le) (by norm_num)
  · calc
      lam ≤ ((n : ℝ) ^ k / (k.factorial : ℝ)) * ((k - 1).factorial : ℝ) / 2 * p ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ hp_pow
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hch_hi hfac_pred_pos.le) (by norm_num)
      _ = ((n : ℝ) * p) ^ k / (2 * (k : ℝ)) := by
        rw [hfac_split, mul_pow]; field_simp [hk_pos.ne', hfac_pred_pos.ne']

/-- When $p_n \asymp 1/n$ and $k \ge 3$ is fixed,
$\lambda_n = \binom{n}{k} \frac{(k - 1)!}{2} p_n^k \asymp 1$
and the Example 4.8 upper bound `(4.14)` is of exact order $1/n$ (`SteinIntro.tex:2358-2365`). -/
theorem ex4_8_asymptotics {k : ℕ} (hk : 3 ≤ k) {C_k : ℝ} (hCk : 0 < C_k)
    {p : ℕ → ℝ} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hp : ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) :
    let lam : ℕ → ℝ :=
      fun n ↦ (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * (p n) ^ k
    let err : ℕ → ℝ :=
      fun n ↦ min 1 (lam n) *
        ((p n) ^ k + C_k * p n * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1))
    ∃ L₁ L₂ B₁ B₂ : ℝ, 0 < L₁ ∧ 0 < L₂ ∧ 0 < B₁ ∧ 0 < B₂ ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        (L₁ ≤ lam n ∧ lam n ≤ L₂) ∧
          (B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ)) := by
  intro lam err
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  let L₁ : ℝ := (c₁ / 2) ^ k / (2 * (k : ℝ))
  let L₂ : ℝ := c₂ ^ k / (2 * (k : ℝ))
  have hL₁_pos : 0 < L₁ := by positivity
  have hL₂_pos : 0 < L₂ := by positivity
  let S_hi : ℝ := ∑ t ∈ Finset.Ico 1 k, c₂ ^ (t - 1)
  have hS_hi_pos : 0 < S_hi := by
    have h1_mem : 1 ∈ Finset.Ico 1 k := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hle := Finset.single_le_sum (f := fun t ↦ c₂ ^ (t - 1))
      (fun t _ ↦ by positivity) h1_mem
    simpa using lt_of_lt_of_le zero_lt_one hle
  let B₁ : ℝ := min 1 L₁ * (C_k * c₁)
  let B₂ : ℝ := c₂ ^ k + C_k * c₂ * S_hi
  have hB₁_pos : 0 < B₁ := mul_pos (lt_min zero_lt_one hL₁_pos) (by positivity)
  have hB₂_pos : 0 < B₂ := by positivity
  refine ⟨L₁, L₂, B₁, B₂, hL₁_pos, hL₂_pos, hB₁_pos, hB₂_pos, ?_⟩
  filter_upwards [hp, Filter.eventually_ge_atTop (2 * k)] with n ⟨hp0, _hp1, hplo, hphi⟩ hn2k
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨hlam_b_lo, hlam_b_hi⟩ := lam_cycleGraph_bounds hk hn2k hp0
  have hnp_lo : c₁ ≤ (n : ℝ) * p n := by
    have h := mul_le_mul_of_nonneg_left hplo hn_pos.le
    rwa [mul_div_cancel₀ c₁ hn_pos.ne'] at h
  have hnp_hi : (n : ℝ) * p n ≤ c₂ := by
    have h := mul_le_mul_of_nonneg_left hphi hn_pos.le
    rwa [mul_div_cancel₀ c₂ hn_pos.ne'] at h
  have hlam_lo : L₁ ≤ lam n := by
    have hpow : c₁ ^ k ≤ ((n : ℝ) * p n) ^ k := pow_le_pow_left₀ hc₁.le hnp_lo k
    have h1 : L₁ = c₁ ^ k / (2 * (k : ℝ) * 2 ^ k) := by dsimp [L₁]; rw [div_pow]; ring
    rw [h1]
    exact (div_le_div_of_nonneg_right hpow (by positivity)).trans hlam_b_lo
  have hlam_hi : lam n ≤ L₂ := by
    have hpow : ((n : ℝ) * p n) ^ k ≤ c₂ ^ k := pow_le_pow_left₀ (by positivity) hnp_hi k
    exact hlam_b_hi.trans (div_le_div_of_nonneg_right hpow (by positivity))
  have hsum_lo : (1 : ℝ) ≤ ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1) := by
    have h1_mem : 1 ∈ Finset.Ico 1 k := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have h := Finset.single_le_sum (f := fun t ↦ ((n : ℝ) * p n) ^ (t - 1))
      (fun t _ ↦ by positivity) h1_mem
    simpa using h
  have hsum_hi : (∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1)) ≤ S_hi :=
    Finset.sum_le_sum fun t _ ↦ pow_le_pow_left₀ (by positivity) hnp_hi (t - 1)
  have herr_lo : B₁ / (n : ℝ) ≤ err n := by
    have hmin_lo : min 1 L₁ ≤ min 1 (lam n) := min_le_min_left 1 hlam_lo
    have hterm_lo :
        (C_k * c₁) / (n : ℝ) ≤
          (p n) ^ k + C_k * p n * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1) := by
      have h1 : (C_k * c₁) / (n : ℝ) = C_k * (c₁ / (n : ℝ)) * 1 := by ring
      have h2 : C_k * (c₁ / (n : ℝ)) * 1 ≤
          C_k * p n * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hplo hCk.le) hsum_lo zero_le_one (by positivity)
      have hpk_nn : 0 ≤ (p n) ^ k := pow_nonneg hp0 k
      linarith
    calc
      B₁ / (n : ℝ) = min 1 L₁ * ((C_k * c₁) / (n : ℝ)) := by dsimp [B₁]; ring
      _ ≤ err n :=
        mul_le_mul hmin_lo hterm_lo (by positivity) (le_min zero_le_one (by positivity))
  have herr_hi : err n ≤ B₂ / (n : ℝ) := by
    have hmin_hi : min 1 (lam n) ≤ 1 := min_le_left 1 (lam n)
    have hpk_hi : (p n) ^ k ≤ c₂ ^ k / (n : ℝ) := by
      have h1 : (p n) ^ k ≤ (c₂ / (n : ℝ)) ^ k := pow_le_pow_left₀ hp0 hphi k
      have h2 : (c₂ / (n : ℝ)) ^ k ≤ c₂ ^ k / (n : ℝ) := by
        rw [div_pow, div_le_div_iff_of_pos_left (by positivity) (by positivity) hn_pos]
        exact le_self_pow₀ hn1 (by omega)
      exact h1.trans h2
    have hsum_term_hi :
        C_k * p n * (∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1)) ≤
          (C_k * c₂ * S_hi) / (n : ℝ) := by
      calc
        C_k * p n * (∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1))
          ≤ C_k * (c₂ / (n : ℝ)) * S_hi :=
            mul_le_mul (mul_le_mul_of_nonneg_left hphi hCk.le) hsum_hi
              (by linarith [hsum_lo]) (by positivity)
        _ = (C_k * c₂ * S_hi) / (n : ℝ) := by ring
    have hterm_hi :
        (p n) ^ k + C_k * p n * (∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1)) ≤
          B₂ / (n : ℝ) := by
      dsimp [B₂]; rw [add_div]; exact add_le_add hpk_hi hsum_term_hi
    calc
      err n ≤ 1 * (B₂ / (n : ℝ)) :=
        mul_le_mul hmin_hi hterm_hi (by positivity) zero_le_one
      _ = B₂ / (n : ℝ) := one_mul _
  exact ⟨⟨hlam_lo, hlam_hi⟩, ⟨herr_lo, herr_hi⟩⟩

end SteinMethod
