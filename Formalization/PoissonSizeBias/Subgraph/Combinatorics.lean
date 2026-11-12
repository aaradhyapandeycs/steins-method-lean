/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Subgraph.Defs
import Formalization.RandomGraph.ErdosRenyi
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Card
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Variance

/-!
# Subgraph Copy Combinatorics and Moments (`Formalization.PoissonSizeBias.Subgraph.Combinatorics`)

Develops the subgraph-copy combinatorics and Erdős–Rényi probability, coupling, expectation, and
variance formulas for Section 4.3.2 (*Application: Subgraph counts*, `SteinIntro.tex:2279-2332`):

* Edge-set pushforward and cardinality preservation for `embedGraph` and `subgraphCopies`.
* Transitive vertex-permutation action on `subgraphCopies H n` and invariance of
  `(subgraphCopiesWithDiffEdges H n α t).card` across `α ∈ subgraphCopies H n`.
* Partition of `(subgraphCopies H n).erase α` into `subgraphCopiesWithDiffEdges H n α t` for
  `1 ≤ t ≤ e_H`.
* Erdős–Rényi marginal and joint subgraph-copy probabilities, the `G ⊔ α` conditional-law
  coupling (`SteinIntro.tex:2299-2307` items 1–3), and the exact variance formula of
  Corollary 4.16 (`SteinIntro.tex:2324-2330`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### 1. Edge sets and permutation action on `embedGraph` and `subgraphCopies` -/

/-- Pushing `embedGraph H f` forward along `g : Fin m ↪ Fin n` equals
`embedGraph H (f.trans g)`. -/
@[simp]
theorem embedGraph_embedGraph {V : Type*} {m n : ℕ} (H : SimpleGraph V)
    (f : V ↪ Fin m) (g : Fin m ↪ Fin n) :
    embedGraph (embedGraph H f) g = embedGraph H (f.trans g) := by
  ext u v
  simp only [embedGraph_adj, Function.Embedding.trans_apply]
  constructor
  · rintro ⟨x, y, rfl, rfl, x', y', rfl, rfl, hxy⟩
    exact ⟨x', y', rfl, rfl, hxy⟩
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    exact ⟨f x, f y, rfl, rfl, x, y, rfl, rfl, hxy⟩

@[simp]
theorem embedGraph_perm_symm {n : ℕ} (α : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    embedGraph (embedGraph α σ.toEmbedding) σ.symm.toEmbedding = α := by
  rw [embedGraph_embedGraph, ← Equiv.trans_toEmbedding, Equiv.self_trans_symm]
  exact embedGraph_refl α

@[simp]
theorem embedGraph_symm_perm {n : ℕ} (α : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    embedGraph (embedGraph α σ.symm.toEmbedding) σ.toEmbedding = α := by
  rw [embedGraph_embedGraph, ← Equiv.trans_toEmbedding, Equiv.symm_trans_self]
  exact embedGraph_refl α

theorem embedGraph_perm_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun α : SimpleGraph (Fin n) ↦ embedGraph α σ.toEmbedding) := by
  intro α₁ α₂ h
  have h' := congrArg (fun β ↦ embedGraph β σ.symm.toEmbedding) h
  simpa using h'

theorem mem_subgraphCopies_perm {V : Type*} {H : SimpleGraph V} {n : ℕ}
    {α : SimpleGraph (Fin n)} (σ : Equiv.Perm (Fin n)) (hα : α ∈ subgraphCopies H n) :
    embedGraph α σ.toEmbedding ∈ subgraphCopies H n := by
  rcases mem_subgraphCopies.mp hα with ⟨f, rfl⟩
  rw [embedGraph_embedGraph]
  exact mem_subgraphCopies.mpr ⟨f.trans σ.toEmbedding, rfl⟩

@[simp]
theorem mem_subgraphCopies_perm_iff {V : Type*} {H : SimpleGraph V} {n : ℕ}
    {α : SimpleGraph (Fin n)} (σ : Equiv.Perm (Fin n)) :
    embedGraph α σ.toEmbedding ∈ subgraphCopies H n ↔ α ∈ subgraphCopies H n := by
  refine ⟨fun h ↦ ?_, mem_subgraphCopies_perm σ⟩
  simpa using mem_subgraphCopies_perm σ.symm h

/-- The edge set of `embedGraph H f` is the image of `H.edgeSet` under `Sym2.map f`. -/
theorem edgeSet_embedGraph {V : Type*} {n : ℕ} (H : SimpleGraph V) (f : V ↪ Fin n) :
    (embedGraph H f).edgeSet = Sym2.map f '' H.edgeSet := by
  ext e
  refine Sym2.ind (fun u v ↦ ?_) e
  simp only [SimpleGraph.mem_edgeSet, embedGraph_adj, Set.mem_image]
  constructor
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    exact ⟨s(x, y), hxy, rfl⟩
  · rintro ⟨e', he', hmap⟩
    revert he' hmap
    refine Sym2.ind (fun x y hxy hmap ↦ ?_) e'
    change H.Adj x y at hxy
    change s(f x, f y) = s(u, v) at hmap
    rcases Sym2.eq_iff.mp hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨x, y, rfl, rfl, hxy⟩
    · exact ⟨y, x, rfl, rfl, hxy.symm⟩

/-- Embedding a graph preserves the number of edges (`SteinIntro.tex:2280-2287`). -/
theorem ncard_edgeSet_embedGraph {V : Type*} {n : ℕ} (H : SimpleGraph V) (f : V ↪ Fin n) :
    (embedGraph H f).edgeSet.ncard = H.edgeSet.ncard := by
  rw [edgeSet_embedGraph]
  exact Set.ncard_image_of_injective H.edgeSet (Sym2.map.injective f.injective)

/-- Every copy `α ∈ subgraphCopies H n` has `H.edgeSet.ncard` edges
(`SteinIntro.tex:2280-2287`). -/
theorem ncard_edgeSet_of_mem_subgraphCopies {V : Type*} {H : SimpleGraph V} {n : ℕ}
    {α : SimpleGraph (Fin n)} (hα : α ∈ subgraphCopies H n) :
    α.edgeSet.ncard = H.edgeSet.ncard := by
  rcases mem_subgraphCopies.mp hα with ⟨f, rfl⟩
  exact ncard_edgeSet_embedGraph H f

/-- Vertex permutations preserve the number of edges in `β.edgeSet \ α.edgeSet`. -/
theorem ncard_edgeSet_diff_embedGraph_perm {n : ℕ} (α β : SimpleGraph (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    ((embedGraph β σ.toEmbedding).edgeSet \ (embedGraph α σ.toEmbedding).edgeSet).ncard =
      (β.edgeSet \ α.edgeSet).ncard := by
  have hinj : Function.Injective (Sym2.map σ.toEmbedding) :=
    Sym2.map.injective σ.injective
  rw [edgeSet_embedGraph, edgeSet_embedGraph, ← Set.image_sdiff hinj]
  exact Set.ncard_image_of_injective _ hinj

/-- If `Fintype.card V ≤ n`, then `subgraphCopies H n` is nonempty
(`SteinIntro.tex:2280-2287`). -/
theorem subgraphCopies_nonempty {V : Type*} [Fintype V] (H : SimpleGraph V) {n : ℕ}
    (hVn : Fintype.card V ≤ n) :
    (subgraphCopies H n).Nonempty := by
  have hcard : Fintype.card V ≤ Fintype.card (Fin n) := by simpa using hVn
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨embedGraph H f, mem_subgraphCopies.mpr ⟨f, rfl⟩⟩

/-- Any two vertex embeddings `f₁ f₂ : V ↪ Fin n` are related by a permutation
`σ : Equiv.Perm (Fin n)` satisfying `f₁.trans σ.toEmbedding = f₂`. -/
theorem exists_perm_trans_embedding {V : Type*} {n : ℕ}
    (f₁ f₂ : V ↪ Fin n) :
    ∃ σ : Equiv.Perm (Fin n), f₁.trans σ.toEmbedding = f₂ := by
  classical
  have : Finite V := Finite.of_injective f₁ f₁.injective
  let _ : Fintype V := Fintype.ofFinite V
  let s₁ : Set (Fin n) := Set.range f₁
  let s₂ : Set (Fin n) := Set.range f₂
  let e₁ : V ≃ s₁ := Equiv.ofInjective f₁ f₁.injective
  let e₂ : V ≃ s₂ := Equiv.ofInjective f₂ f₂.injective
  let e_range : s₁ ≃ s₂ := e₁.symm.trans e₂
  have hcard_s : Fintype.card s₁ = Fintype.card s₂ := Fintype.card_congr e_range
  have hcard_compl :
      Fintype.card {x : Fin n // x ∉ s₁} = Fintype.card {x : Fin n // x ∉ s₂} := by
    have h₁ := Fintype.card_subtype_compl (fun x : Fin n ↦ x ∈ s₁)
    have h₂ := Fintype.card_subtype_compl (fun x : Fin n ↦ x ∈ s₂)
    change Fintype.card {x : Fin n // ¬ x ∈ s₁} = Fintype.card {x : Fin n // ¬ x ∈ s₂}
    rw [h₁, h₂, hcard_s]
  let e_compl : {x : Fin n // x ∉ s₁} ≃ {x : Fin n // x ∉ s₂} :=
    Fintype.equivOfCardEq hcard_compl
  let σ : Equiv.Perm (Fin n) :=
    (Equiv.sumCompl (· ∈ s₁)).symm.trans
      ((Equiv.sumCongr e_range e_compl).trans (Equiv.sumCompl (· ∈ s₂)))
  refine ⟨σ, ?_⟩
  apply Function.Embedding.ext
  intro v
  have hv₁ : f₁ v ∈ s₁ := ⟨v, rfl⟩
  have hsymm : (Equiv.sumCompl (· ∈ s₁)).symm (f₁ v) = Sum.inl ⟨f₁ v, hv₁⟩ := by
    simp [Equiv.sumCompl, hv₁]
  have he₁ : e₁.symm ⟨f₁ v, hv₁⟩ = v := e₁.symm_apply_apply v
  change (Equiv.sumCompl (· ∈ s₂))
    ((Equiv.sumCongr e_range e_compl) ((Equiv.sumCompl (· ∈ s₁)).symm (f₁ v))) = f₂ v
  rw [hsymm]
  change (e₂ (e₁.symm ⟨f₁ v, hv₁⟩)).1 = f₂ v
  rw [he₁]
  rfl

/-- Transitivity of `Equiv.Perm (Fin n)` on `subgraphCopies H n`: any two copies `α₁, α₂`
of `H` in $K_n$ are related by a vertex permutation `σ`. -/
theorem exists_perm_embedGraph_eq_of_mem_subgraphCopies {V : Type*}
    {H : SimpleGraph V} {n : ℕ} {α₁ α₂ : SimpleGraph (Fin n)}
    (hα₁ : α₁ ∈ subgraphCopies H n) (hα₂ : α₂ ∈ subgraphCopies H n) :
    ∃ σ : Equiv.Perm (Fin n), embedGraph α₁ σ.toEmbedding = α₂ := by
  rcases mem_subgraphCopies.mp hα₁ with ⟨f₁, rfl⟩
  rcases mem_subgraphCopies.mp hα₂ with ⟨f₂, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_perm_trans_embedding f₁ f₂
  exact ⟨σ, by rw [embedGraph_embedGraph, hσ]⟩

/-- The cardinality of `subgraphCopiesWithDiffEdges H n α t` (`|\Gamma_\alpha^t|`) is independent
of the representative `α ∈ subgraphCopies H n` (`SteinIntro.tex:2315-2330`). -/
theorem card_subgraphCopiesWithDiffEdges_eq {V : Type*} (H : SimpleGraph V)
    {n : ℕ} {α₁ α₂ : SimpleGraph (Fin n)}
    (hα₁ : α₁ ∈ subgraphCopies H n) (hα₂ : α₂ ∈ subgraphCopies H n) (t : ℕ) :
    (subgraphCopiesWithDiffEdges H n α₁ t).card =
      (subgraphCopiesWithDiffEdges H n α₂ t).card := by
  obtain ⟨σ, rfl⟩ := exists_perm_embedGraph_eq_of_mem_subgraphCopies hα₁ hα₂
  refine Finset.card_bij (fun β _ ↦ embedGraph β σ.toEmbedding) ?_ ?_ ?_
  · intro β hβ
    rcases mem_subgraphCopiesWithDiffEdges.mp hβ with ⟨hβ_mem, hβ_diff⟩
    rw [mem_subgraphCopiesWithDiffEdges]
    exact ⟨mem_subgraphCopies_perm σ hβ_mem,
      (ncard_edgeSet_diff_embedGraph_perm α₁ β σ).trans hβ_diff⟩
  · intro β₁ _ β₂ _ h
    exact embedGraph_perm_injective σ h
  · intro γ hγ
    rcases mem_subgraphCopiesWithDiffEdges.mp hγ with ⟨hγ_mem, hγ_diff⟩
    refine ⟨embedGraph γ σ.symm.toEmbedding, ?_, embedGraph_symm_perm γ σ⟩
    rw [mem_subgraphCopiesWithDiffEdges]
    refine ⟨mem_subgraphCopies_perm σ.symm hγ_mem, ?_⟩
    have h := ncard_edgeSet_diff_embedGraph_perm α₁ (embedGraph γ σ.symm.toEmbedding) σ
    rw [embedGraph_symm_perm] at h
    exact h.symm.trans hγ_diff

/-! ### 2. Edge-difference partition of `(subgraphCopies H n).erase α` -/

/-- If `H` is a graph on `0 < Fintype.card V` vertices with no isolated vertices, then `H` has at
least one edge (`0 < H.edgeSet.ncard`). -/
theorem ncard_edgeSet_pos_of_not_isIsolated {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hV : 0 < Fintype.card V) (hiso : ∀ v : V, ¬ H.IsIsolated v) :
    0 < H.edgeSet.ncard := by
  have : Nonempty V := Fintype.card_pos_iff.mp hV
  obtain ⟨v₀⟩ := ‹Nonempty V›
  obtain ⟨w₀, hnot_w₀⟩ := Classical.not_forall.mp (hiso v₀)
  have hadj : H.Adj v₀ w₀ := Classical.not_not.mp hnot_w₀
  have hne : H.edgeSet.Nonempty := ⟨s(v₀, w₀), hadj⟩
  exact (Set.ncard_pos (Set.toFinite _)).mpr hne

/-- For `α, β ∈ subgraphCopies H n`, `(β.edgeSet \ α.edgeSet).ncard ≤ H.edgeSet.ncard`. -/
theorem ncard_edgeSet_diff_le {V : Type*} {H : SimpleGraph V} {n : ℕ}
    {α β : SimpleGraph (Fin n)} (hβ : β ∈ subgraphCopies H n) :
    (β.edgeSet \ α.edgeSet).ncard ≤ H.edgeSet.ncard := by
  rw [← ncard_edgeSet_of_mem_subgraphCopies hβ]
  exact Set.ncard_le_ncard Set.sdiff_subset (Set.toFinite _)

/-- For `α, β ∈ subgraphCopies H n`, `(β.edgeSet \ α.edgeSet).ncard = 0` iff `β = α`. -/
theorem ncard_edgeSet_diff_eq_zero_iff {V : Type*} {H : SimpleGraph V} {n : ℕ}
    {α β : SimpleGraph (Fin n)}
    (hα : α ∈ subgraphCopies H n) (hβ : β ∈ subgraphCopies H n) :
    (β.edgeSet \ α.edgeSet).ncard = 0 ↔ β = α := by
  rw [Set.ncard_eq_zero (Set.toFinite _), Set.sdiff_eq_empty]
  constructor
  · intro hsub
    have hcard_eq : α.edgeSet.ncard = β.edgeSet.ncard := by
      rw [ncard_edgeSet_of_mem_subgraphCopies hα, ncard_edgeSet_of_mem_subgraphCopies hβ]
    have heq : β.edgeSet = α.edgeSet :=
      Set.eq_of_subset_of_ncard_le hsub (hcard_eq.le) (Set.toFinite _)
    exact SimpleGraph.edgeSet_inj.mp heq
  · rintro rfl
    exact Set.Subset.rfl

open Classical in
/-- Partition of `(subgraphCopies H n).erase α` into the disjoint subsets
`subgraphCopiesWithDiffEdges H n α t` for `1 ≤ t ≤ e_H` (`SteinIntro.tex:2325-2326`). -/
theorem erase_subgraphCopies_eq_biUnion {V : Type*} (H : SimpleGraph V)
    {n : ℕ} {α : SimpleGraph (Fin n)} (hα : α ∈ subgraphCopies H n) :
    (subgraphCopies H n).erase α =
      (Finset.Ico 1 (H.edgeSet.ncard + 1)).biUnion (subgraphCopiesWithDiffEdges H n α) := by
  ext β
  simp only [Finset.mem_erase, Finset.mem_biUnion, Finset.mem_Ico, mem_subgraphCopiesWithDiffEdges]
  constructor
  · rintro ⟨hne, hβ⟩
    have hpos : 1 ≤ (β.edgeSet \ α.edgeSet).ncard := by
      have h0 : (β.edgeSet \ α.edgeSet).ncard ≠ 0 :=
        mt (ncard_edgeSet_diff_eq_zero_iff hα hβ).mp hne
      omega
    have hle : (β.edgeSet \ α.edgeSet).ncard < H.edgeSet.ncard + 1 :=
      Nat.lt_succ_of_le (ncard_edgeSet_diff_le hβ)
    exact ⟨(β.edgeSet \ α.edgeSet).ncard, ⟨hpos, hle⟩, hβ, rfl⟩
  · rintro ⟨t, ⟨ht1, _⟩, hβ, rfl⟩
    refine ⟨?_, hβ⟩
    intro hba
    subst hba
    simp at ht1

theorem pairwiseDisjoint_subgraphCopiesWithDiffEdges {V : Type*} (H : SimpleGraph V)
    (n : ℕ) (α : SimpleGraph (Fin n)) :
    (Set.univ : Set ℕ).PairwiseDisjoint (subgraphCopiesWithDiffEdges H n α) := by
  intro t₁ _ t₂ _ hne
  change Disjoint (subgraphCopiesWithDiffEdges H n α t₁)
    (subgraphCopiesWithDiffEdges H n α t₂)
  rw [Finset.disjoint_left]
  intro β h₁ h₂
  rw [mem_subgraphCopiesWithDiffEdges] at h₁ h₂
  exact hne (h₁.2.symm.trans h₂.2)

/-! ### 3. Edge-pair representation and Erdős–Rényi probabilities -/

/-- Off-diagonal edge pairs belonging to `α.edgeSet`. -/
noncomputable def edgePairsOfGraph {n : ℕ} (α : SimpleGraph (Fin n)) : Finset (EdgePair n) := by
  classical exact Finset.univ.filter fun e : EdgePair n ↦ e.1 ∈ α.edgeSet

@[simp]
theorem mem_edgePairsOfGraph {n : ℕ} {α : SimpleGraph (Fin n)} {e : EdgePair n} :
    e ∈ edgePairsOfGraph α ↔ e.1 ∈ α.edgeSet := by
  classical
  unfold edgePairsOfGraph
  simp

theorem card_edgePairsOfGraph {n : ℕ} (α : SimpleGraph (Fin n)) :
    (edgePairsOfGraph α).card = α.edgeSet.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
  · intro e he
    simpa using mem_edgePairsOfGraph.mp he
  · intro e₁ _ e₂ _ h
    exact Subtype.ext h
  · intro e he
    have hmem : e ∈ α.edgeSet := Set.mem_toFinset.mp he
    have hnd : ¬ e.IsDiag := α.not_isDiag_of_mem_edgeSet hmem
    exact ⟨⟨e, hnd⟩, mem_edgePairsOfGraph.mpr hmem, rfl⟩

theorem card_edgePairsOfGraph_sdiff {n : ℕ} (α β : SimpleGraph (Fin n)) :
    (edgePairsOfGraph β \ edgePairsOfGraph α).card = (β.edgeSet \ α.edgeSet).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
  · intro e he
    rw [Finset.mem_sdiff, mem_edgePairsOfGraph, mem_edgePairsOfGraph] at he
    exact Set.mem_toFinset.mpr he
  · intro e₁ _ e₂ _ h
    exact Subtype.ext h
  · intro e he
    have hmem : e ∈ β.edgeSet \ α.edgeSet := Set.mem_toFinset.mp he
    have hnd : ¬ e.IsDiag := β.not_isDiag_of_mem_edgeSet hmem.1
    refine ⟨⟨e, hnd⟩, ?_, rfl⟩
    rw [Finset.mem_sdiff, mem_edgePairsOfGraph, mem_edgePairsOfGraph]
    exact hmem

theorem card_edgePairsOfGraph_union {n : ℕ} (α β : SimpleGraph (Fin n)) :
    (edgePairsOfGraph α ∪ edgePairsOfGraph β).card =
      α.edgeSet.ncard + (β.edgeSet \ α.edgeSet).ncard := by
  have hunion : edgePairsOfGraph α ∪ edgePairsOfGraph β =
      edgePairsOfGraph α ∪ (edgePairsOfGraph β \ edgePairsOfGraph α) :=
    (Finset.union_sdiff_self_eq_union).symm
  rw [hunion, Finset.card_union_of_disjoint Finset.disjoint_sdiff,
    card_edgePairsOfGraph, card_edgePairsOfGraph_sdiff]

theorem le_iff_forall_edgePairsOfGraph {n : ℕ} (α G : SimpleGraph (Fin n)) :
    α ≤ G ↔ ∀ e ∈ edgePairsOfGraph α, e.1 ∈ G.edgeSet := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  constructor
  · intro h e he
    exact h (mem_edgePairsOfGraph.mp he)
  · intro h e he
    have hnd : ¬ e.IsDiag := α.not_isDiag_of_mem_edgeSet he
    exact h ⟨e, hnd⟩ (mem_edgePairsOfGraph.mpr he)

/-- Under $G \sim G(n, p)$ ($0 \le p \le 1$), $\mathbb{P}(\alpha \subseteq G) = p^{|E(\alpha)|}$. -/
theorem erdosRenyi_real_subgraphCopyIndicator_eq_one {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (α : SimpleGraph (Fin n)) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} =
      p ^ α.edgeSet.ncard := by
  have hset : {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ edgePairsOfGraph α, e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
    ext G
    simp [subgraphCopyIndicator_eq_one_iff, le_iff_forall_edgePairsOfGraph]
  rw [hset, erdosRenyi_real_cylinder hp0 hp1 _ _ (Finset.disjoint_empty_right _),
    card_edgePairsOfGraph, Finset.card_empty, pow_zero, mul_one]

/-- Under $G \sim G(n, p)$ ($0 \le p \le 1$),
$\mathbb{P}(\alpha \subseteq G \wedge \beta \subseteq G) =
p^{|E(\alpha)| + |E(\beta) \setminus E(\alpha)|}$. -/
theorem erdosRenyi_real_subgraphCopyIndicator_pair_eq_one {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (α β : SimpleGraph (Fin n)) :
    (erdosRenyi n p).real
        {G : SimpleGraph (Fin n) |
          subgraphCopyIndicator α G = 1 ∧ subgraphCopyIndicator β G = 1} =
      p ^ α.edgeSet.ncard * p ^ (β.edgeSet \ α.edgeSet).ncard := by
  have hset : {G : SimpleGraph (Fin n) |
        subgraphCopyIndicator α G = 1 ∧ subgraphCopyIndicator β G = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ edgePairsOfGraph α ∪ edgePairsOfGraph β, e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
    ext G
    change (subgraphCopyIndicator α G = 1 ∧ subgraphCopyIndicator β G = 1) ↔
      (∀ e ∈ edgePairsOfGraph α ∪ edgePairsOfGraph β, e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)
    simp only [subgraphCopyIndicator_eq_one_iff,
      le_iff_forall_edgePairsOfGraph, Finset.mem_union, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, and_true]
    exact ⟨fun ⟨hα, hβ⟩ e he ↦ he.elim (hα e) (hβ e),
      fun h ↦ ⟨fun e he ↦ h e (Or.inl he), fun e he ↦ h e (Or.inr he)⟩⟩
  rw [hset, erdosRenyi_real_cylinder hp0 hp1 _ _ (Finset.disjoint_empty_right _),
    card_edgePairsOfGraph_union, Finset.card_empty, pow_zero, mul_one, pow_add]

/-- Expectation of a single copy indicator `subgraphCopyIndicator α` under `erdosRenyi n p`
(`SteinIntro.tex:2307`). -/
theorem integral_subgraphCopyIndicator {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (α : SimpleGraph (Fin n)) :
    ∫ G, (subgraphCopyIndicator α G : ℝ) ∂erdosRenyi n p = p ^ α.edgeSet.ncard := by
  have hind : (fun G : SimpleGraph (Fin n) ↦ (subgraphCopyIndicator α G : ℝ)) =
      {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1}.indicator 1 := by
    ext G
    by_cases h1 : subgraphCopyIndicator α G = 1
    · have hmem : G ∈ {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} := h1
      rw [Set.indicator_of_mem hmem, h1]
      norm_num
    · have hnot : G ∉ {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} := h1
      have h0 : subgraphCopyIndicator α G = 0 :=
        (subgraphCopyIndicator_zero_or_one α G).resolve_right h1
      rw [Set.indicator_of_notMem hnot, h0, Nat.cast_zero]
  rw [hind, integral_indicator_one MeasurableSet.of_discrete,
    erdosRenyi_real_subgraphCopyIndicator_eq_one hp0 hp1 α]

/-- Expectation of the product of two copy indicators under `erdosRenyi n p`
(`SteinIntro.tex:2326-2330`). -/
theorem integral_subgraphCopyIndicator_mul {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (α β : SimpleGraph (Fin n)) :
    ∫ G, (subgraphCopyIndicator α G : ℝ) *
        (subgraphCopyIndicator β G : ℝ) ∂erdosRenyi n p =
      p ^ α.edgeSet.ncard * p ^ (β.edgeSet \ α.edgeSet).ncard := by
  have hind : (fun G : SimpleGraph (Fin n) ↦
        (subgraphCopyIndicator α G : ℝ) * (subgraphCopyIndicator β G : ℝ)) =
      {G : SimpleGraph (Fin n) |
        subgraphCopyIndicator α G = 1 ∧ subgraphCopyIndicator β G = 1}.indicator 1 := by
    ext G
    by_cases h : subgraphCopyIndicator α G = 1 ∧ subgraphCopyIndicator β G = 1
    · have hmem : G ∈ {G : SimpleGraph (Fin n) |
          subgraphCopyIndicator α G = 1 ∧ subgraphCopyIndicator β G = 1} := h
      rw [Set.indicator_of_mem hmem, h.1, h.2]
      norm_num
    · have hnot : G ∉ {G : SimpleGraph (Fin n) |
          subgraphCopyIndicator α G = 1 ∧ subgraphCopyIndicator β G = 1} := h
      rw [Set.indicator_of_notMem hnot]
      rcases not_and_or.mp h with hα | hβ
      · have hα0 : subgraphCopyIndicator α G = 0 :=
          (subgraphCopyIndicator_zero_or_one α G).resolve_right hα
        simp [hα0]
      · have hβ0 : subgraphCopyIndicator β G = 0 :=
          (subgraphCopyIndicator_zero_or_one β G).resolve_right hβ
        simp [hβ0]
  rw [hind, integral_indicator_one MeasurableSet.of_discrete,
    erdosRenyi_real_subgraphCopyIndicator_pair_eq_one hp0 hp1 α β]

/-- Expectation of `subgraphCount H n` under `erdosRenyi n p` (`SteinIntro.tex:2290, 2330`). -/
theorem integral_subgraphCount {V : Type*} (H : SimpleGraph V) {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ G, (subgraphCount H n G : ℝ) ∂erdosRenyi n p =
      ((subgraphCopies H n).card : ℝ) * p ^ H.edgeSet.ncard := by
  have hfun : (fun G : SimpleGraph (Fin n) ↦ (subgraphCount H n G : ℝ)) =
      fun G ↦ ∑ α ∈ subgraphCopies H n, (subgraphCopyIndicator α G : ℝ) := by
    ext G
    simp [subgraphCount, Nat.cast_sum]
  rw [hfun, integral_finsetSum (subgraphCopies H n) fun _ _ ↦ Integrable.of_finite]
  have hterm : ∀ α ∈ subgraphCopies H n,
      ∫ G, (subgraphCopyIndicator α G : ℝ) ∂erdosRenyi n p = p ^ H.edgeSet.ncard := by
    intro α hα
    rw [integral_subgraphCopyIndicator hp0 hp1 α, ncard_edgeSet_of_mem_subgraphCopies hα]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

/-! ### 4. Conditional law of `G ⊔ α` and proof of `Sec4_3_2_subgraph_coupling` -/

private lemma singleton_inter_le_eq_cylinder {n : ℕ}
    (α K : SimpleGraph (Fin n)) (hαK : α ≤ K) :
    ({G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} ∩ {K}) =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ edgePairsOfGraph α ∪ (edgePairsOfGraph K \ edgePairsOfGraph α),
          e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ Finset.univ \ edgePairsOfGraph K, e.1 ∉ G.edgeSet)} := by
  have hsub : edgePairsOfGraph α ⊆ edgePairsOfGraph K := by
    intro e he
    rw [mem_edgePairsOfGraph] at he ⊢
    exact SimpleGraph.edgeSet_mono hαK he
  have hunion : edgePairsOfGraph α ∪ (edgePairsOfGraph K \ edgePairsOfGraph α) =
      edgePairsOfGraph K := Finset.union_sdiff_of_subset hsub
  rw [hunion]
  ext G
  change (subgraphCopyIndicator α G = 1 ∧ G ∈ ({K} : Set (SimpleGraph (Fin n)))) ↔
    (∀ e ∈ edgePairsOfGraph K, e.1 ∈ G.edgeSet) ∧
      (∀ e ∈ Finset.univ \ edgePairsOfGraph K, e.1 ∉ G.edgeSet)
  simp only [Set.mem_singleton_iff,
    subgraphCopyIndicator_eq_one_iff, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_edgePairsOfGraph]
  constructor
  · rintro ⟨_, rfl⟩
    exact ⟨fun _ he ↦ he, fun _ he ↦ he⟩
  · rintro ⟨hpos, hneg⟩
    have hGK : G = K := by
      rw [← SimpleGraph.edgeSet_inj]
      ext z
      by_cases hz : z.IsDiag
      · exact iff_of_false (G.not_mem_edgeSet_of_isDiag hz) (K.not_mem_edgeSet_of_isDiag hz)
      · let e : EdgePair n := ⟨z, hz⟩
        by_cases hmem : e.1 ∈ K.edgeSet
        · exact iff_of_true (hpos e hmem) hmem
        · exact iff_of_false (hneg e hmem) hmem
    exact ⟨hGK ▸ hαK, hGK⟩

private lemma preimage_sup_eq_cylinder {n : ℕ} (α K : SimpleGraph (Fin n)) (hαK : α ≤ K) :
    (fun G : SimpleGraph (Fin n) ↦ G ⊔ α) ⁻¹' {K} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ edgePairsOfGraph K \ edgePairsOfGraph α, e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ Finset.univ \ edgePairsOfGraph K, e.1 ∉ G.edgeSet)} := by
  ext G
  change G ⊔ α ∈ ({K} : Set (SimpleGraph (Fin n))) ↔
    (∀ e ∈ edgePairsOfGraph K \ edgePairsOfGraph α, e.1 ∈ G.edgeSet) ∧
      (∀ e ∈ Finset.univ \ edgePairsOfGraph K, e.1 ∉ G.edgeSet)
  simp only [Set.mem_singleton_iff, Finset.mem_sdiff,
    Finset.mem_univ, true_and, mem_edgePairsOfGraph]
  constructor
  · rintro rfl
    refine ⟨fun e he ↦ ?_, fun e he hG ↦ he (SimpleGraph.edgeSet_mono le_sup_left hG)⟩
    rw [SimpleGraph.edgeSet_sup, Set.mem_union] at he
    exact he.1.resolve_right he.2
  · rintro ⟨hpos, hneg⟩
    rw [← SimpleGraph.edgeSet_inj, SimpleGraph.edgeSet_sup]
    ext z
    by_cases hz : z.IsDiag
    · exact iff_of_false
        (fun h ↦ h.elim (G.not_mem_edgeSet_of_isDiag hz) (α.not_mem_edgeSet_of_isDiag hz))
        (K.not_mem_edgeSet_of_isDiag hz)
    · let e : EdgePair n := ⟨z, hz⟩
      change e.1 ∈ G.edgeSet ∪ α.edgeSet ↔ e.1 ∈ K.edgeSet
      by_cases hα : e.1 ∈ α.edgeSet
      · exact iff_of_true (Or.inr hα) (SimpleGraph.edgeSet_mono hαK hα)
      · by_cases hK : e.1 ∈ K.edgeSet
        · exact iff_of_true (Or.inl (hpos e ⟨hK, hα⟩)) hK
        · exact iff_of_false (fun h ↦ h.elim (hneg e hK) hα) hK

/-- Conditioning $G \sim G(n, p)$ ($0 < p \le 1$) on $\alpha \subseteq G$ has the same law as
$G \sqcup \alpha$ (`SteinIntro.tex:2299-2304`). -/
theorem erdosRenyi_cond_subgraphCopyIndicator_eq_map_sup {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (α : SimpleGraph (Fin n)) :
    ProbabilityTheory.cond (erdosRenyi n p)
        {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} =
      (erdosRenyi n p).map (fun G ↦ G ⊔ α) := by
  classical
  set S_α : Set (SimpleGraph (Fin n)) := {G | subgraphCopyIndicator α G = 1}
  set sup_α : SimpleGraph (Fin n) → SimpleGraph (Fin n) := fun G ↦ G ⊔ α
  have hsup_meas : Measurable sup_α := Measurable.of_discrete
  have hS_meas : MeasurableSet S_α := MeasurableSet.of_discrete
  refine Measure.ext_of_singleton fun K ↦ ?_
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top (ProbabilityTheory.cond (erdosRenyi n p) S_α) {K})
    (measure_ne_top ((erdosRenyi n p).map sup_α) {K})).mp ?_
  rw [measureReal_def, ProbabilityTheory.cond_apply hS_meas (erdosRenyi n p) {K},
    ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def,
    map_measureReal_apply hsup_meas (measurableSet_singleton K)]
  by_cases hαK : α ≤ K
  · let S_pos : Finset (EdgePair n) := edgePairsOfGraph K \ edgePairsOfGraph α
    let S_neg : Finset (EdgePair n) := Finset.univ \ edgePairsOfGraph K
    have hdisj_α_pos : Disjoint (edgePairsOfGraph α) S_pos := Finset.disjoint_sdiff
    have hdisj_pos_neg : Disjoint S_pos S_neg := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      exact (Finset.mem_sdiff.mp he2).2 (Finset.mem_sdiff.mp he1).1
    have hdisj_α_neg : Disjoint (edgePairsOfGraph α) S_neg := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      have hsub := SimpleGraph.edgeSet_mono hαK (mem_edgePairsOfGraph.mp he1)
      exact (Finset.mem_sdiff.mp he2).2 (mem_edgePairsOfGraph.mpr hsub)
    have hdisj_u_neg : Disjoint (edgePairsOfGraph α ∪ S_pos) S_neg :=
      Finset.disjoint_union_left.mpr ⟨hdisj_α_neg, hdisj_pos_neg⟩
    have hprob_α : (erdosRenyi n p).real S_α = p ^ α.edgeSet.ncard :=
      erdosRenyi_real_subgraphCopyIndicator_eq_one hp0.le hp1 α
    have hprob_ne : p ^ α.edgeSet.ncard ≠ 0 := pow_ne_zero _ hp0.ne'
    rw [hprob_α]
    dsimp only [S_α, sup_α]
    rw [singleton_inter_le_eq_cylinder α K hαK, preimage_sup_eq_cylinder α K hαK,
      erdosRenyi_real_cylinder hp0.le hp1 (edgePairsOfGraph α ∪ S_pos) S_neg hdisj_u_neg,
      erdosRenyi_real_cylinder hp0.le hp1 S_pos S_neg hdisj_pos_neg,
      Finset.card_union_of_disjoint hdisj_α_pos, card_edgePairsOfGraph, pow_add]
    calc
      (p ^ α.edgeSet.ncard)⁻¹ *
          (p ^ α.edgeSet.ncard * p ^ S_pos.card * (1 - p) ^ S_neg.card)
        = (p ^ α.edgeSet.ncard * (p ^ α.edgeSet.ncard)⁻¹) *
            (p ^ S_pos.card * (1 - p) ^ S_neg.card) := by ring
      _ = p ^ S_pos.card * (1 - p) ^ S_neg.card := by rw [mul_inv_cancel₀ hprob_ne, one_mul]
  · have hinter : S_α ∩ {K} = ∅ := by
      ext G
      change (subgraphCopyIndicator α G = 1 ∧ G ∈ ({K} : Set (SimpleGraph (Fin n)))) ↔
        G ∈ (∅ : Set (SimpleGraph (Fin n)))
      simp only [Set.mem_singleton_iff,
        subgraphCopyIndicator_eq_one_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro hG rfl
      exact hαK hG
    have hpre : sup_α ⁻¹' {K} = ∅ := by
      ext G
      simp only [sup_α, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro hGK
      exact hαK (hGK ▸ le_sup_right)
    rw [hinter, hpre, measureReal_empty, mul_zero]

/-- Monotonicity of `subgraphCopyIndicator` under adding edges (`SteinIntro.tex:2305`). -/
theorem subgraphCopyIndicator_le_sup {n : ℕ} (α β G : SimpleGraph (Fin n)) :
    subgraphCopyIndicator β G ≤ subgraphCopyIndicator β (G ⊔ α) := by
  by_cases h : β ≤ G
  · rw [subgraphCopyIndicator_of_le h, subgraphCopyIndicator_of_le (h.trans le_sup_left)]
  · rw [subgraphCopyIndicator_of_not_le h]
    exact Nat.zero_le _

open Classical in
/-- Proof of the three coupling facts in the proof of Theorem 4.15 (`SteinIntro.tex:2299-2307`). -/
theorem subgraph_coupling_facts {V : Type*} [Fintype V] (H : SimpleGraph V)
    {n : ℕ} {p : ℝ} {α : SimpleGraph (Fin n)}
    (_hV0 : 0 < Fintype.card V) (_hVn : Fintype.card V ≤ n)
    (_hiso : ∀ v : V, ¬ H.IsIsolated v)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hα : α ∈ subgraphCopies H n) :
    let Γ : Finset (SimpleGraph (Fin n)) := subgraphCopies H n
    let e_H : ℕ := H.edgeSet.ncard
    (0 < p →
      (erdosRenyi n p).map
          (fun G (β : {β : SimpleGraph (Fin n) // β ∈ Γ.erase α}) ↦
            subgraphCopyIndicator β.1 (G ⊔ α)) =
        (ProbabilityTheory.cond (erdosRenyi n p) {G | subgraphCopyIndicator α G = 1}).map
          (fun G (β : {β : SimpleGraph (Fin n) // β ∈ Γ.erase α}) ↦
            subgraphCopyIndicator β.1 G)) ∧
    (∀ β ∈ Γ.erase α, ∀ G : SimpleGraph (Fin n),
      subgraphCopyIndicator β G ≤ subgraphCopyIndicator β (G ⊔ α)) ∧
    (∫ G, (subgraphCopyIndicator α G : ℝ) ∂erdosRenyi n p = p ^ e_H) := by
  intro Γ e_H
  refine ⟨fun hp_pos ↦ ?_, fun β _ G ↦ subgraphCopyIndicator_le_sup α β G, ?_⟩
  · let proj :
        SimpleGraph (Fin n) → ({β : SimpleGraph (Fin n) // β ∈ Γ.erase α} → ℕ) :=
      fun G β ↦ subgraphCopyIndicator β.1 G
    have hproj_meas : Measurable proj := Measurable.of_discrete
    have hsup_meas : Measurable (fun G : SimpleGraph (Fin n) ↦ G ⊔ α) := Measurable.of_discrete
    rw [erdosRenyi_cond_subgraphCopyIndicator_eq_map_sup hp_pos hp1 α,
      Measure.map_map hproj_meas hsup_meas]
    rfl
  · rw [integral_subgraphCopyIndicator hp0 hp1 α, ncard_edgeSet_of_mem_subgraphCopies hα]

/-! ### 5. Exact variance of `subgraphCount` (Corollary 4.16 variance display) -/

/-- Exact covariance of two subgraph copy indicators `α, β ∈ subgraphCopies H n` under
`erdosRenyi n p` (`SteinIntro.tex:2325-2330`). -/
theorem covariance_subgraphCopyIndicator {V : Type*} {H : SimpleGraph V}
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {α β : SimpleGraph (Fin n)}
    (hα : α ∈ subgraphCopies H n) (hβ : β ∈ subgraphCopies H n) :
    let e_H : ℕ := H.edgeSet.ncard
    ∫ G, ((subgraphCopyIndicator α G : ℝ) - p ^ e_H) *
        ((subgraphCopyIndicator β G : ℝ) - p ^ e_H) ∂erdosRenyi n p =
      p ^ e_H * (p ^ (β.edgeSet \ α.edgeSet).ncard - p ^ e_H) := by
  intro e_H
  have hexpand : (fun G : SimpleGraph (Fin n) ↦
        ((subgraphCopyIndicator α G : ℝ) - p ^ e_H) *
          ((subgraphCopyIndicator β G : ℝ) - p ^ e_H)) =
      fun G ↦ ((subgraphCopyIndicator α G : ℝ) * (subgraphCopyIndicator β G : ℝ) -
        p ^ e_H * (subgraphCopyIndicator α G : ℝ)) -
        p ^ e_H * (subgraphCopyIndicator β G : ℝ) + p ^ e_H * p ^ e_H := by
    ext G
    ring
  rw [hexpand,
    integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_subgraphCopyIndicator_mul hp0 hp1 α β,
    integral_subgraphCopyIndicator hp0 hp1 α,
    integral_subgraphCopyIndicator hp0 hp1 β,
    ncard_edgeSet_of_mem_subgraphCopies hα,
    ncard_edgeSet_of_mem_subgraphCopies hβ]
  ring

/-- Exact variance of `subgraphCount H n` under `erdosRenyi n p` (`SteinIntro.tex:2324-2330`,
Corollary 4.16 proof display). -/
theorem variance_subgraphCount_erdosRenyi {V : Type*} (H : SimpleGraph V)
    {n : ℕ} {p : ℝ} {α : SimpleGraph (Fin n)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hα : α ∈ subgraphCopies H n) :
    let Γ : Finset (SimpleGraph (Fin n)) := subgraphCopies H n
    let e_H : ℕ := H.edgeSet.ncard
    let lam : ℝ := (Γ.card : ℝ) * p ^ e_H
    let Γ_t : ℕ → Finset (SimpleGraph (Fin n)) := subgraphCopiesWithDiffEdges H n α
    ProbabilityTheory.variance (fun G ↦ (subgraphCount H n G : ℝ)) (erdosRenyi n p) =
      lam * (1 - p ^ e_H +
        ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H)) := by
  classical
  intro Γ e_H lam Γ_t
  let Xc : SimpleGraph (Fin n) → SimpleGraph (Fin n) → ℝ :=
    fun γ G ↦ (subgraphCopyIndicator γ G : ℝ) - p ^ e_H
  have hmean : ∫ G, (subgraphCount H n G : ℝ) ∂erdosRenyi n p = lam :=
    integral_subgraphCount H hp0 hp1
  have hcentered : ∀ G : SimpleGraph (Fin n),
      (subgraphCount H n G : ℝ) - lam = ∑ γ ∈ Γ, Xc γ G := by
    intro G
    simp only [Xc, subgraphCount, Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, lam, Γ]
  have hVar : ProbabilityTheory.variance (fun G ↦ (subgraphCount H n G : ℝ)) (erdosRenyi n p) =
      ∫ G, (∑ γ ∈ Γ, Xc γ G) ^ 2 ∂erdosRenyi n p := by
    rw [ProbabilityTheory.variance_eq_integral Measurable.of_discrete.aemeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun G ↦ ?_)
    dsimp only
    rw [hmean, hcentered G]
  rw [hVar]
  have hsq : (fun G : SimpleGraph (Fin n) ↦ (∑ γ ∈ Γ, Xc γ G) ^ 2) =
      fun G ↦ ∑ γ ∈ Γ, ∑ β ∈ Γ, Xc γ G * Xc β G := by
    ext G
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ _ ↦ ?_
    rw [Finset.mul_sum]
  rw [hsq, integral_finsetSum Γ fun _ _ ↦ Integrable.of_finite]
  have hinner : ∀ γ ∈ Γ,
      (∫ G, ∑ β ∈ Γ, Xc γ G * Xc β G ∂erdosRenyi n p) =
        p ^ e_H * (1 - p ^ e_H +
          ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H)) := by
    intro γ hγ
    rw [integral_finsetSum Γ fun _ _ ↦ Integrable.of_finite,
      ← Finset.insert_erase hγ, Finset.sum_insert (Finset.notMem_erase γ Γ)]
    have hdiag : ∫ G, Xc γ G * Xc γ G ∂erdosRenyi n p = p ^ e_H * (1 - p ^ e_H) := by
      have hcov := covariance_subgraphCopyIndicator hp0 hp1 hγ hγ
      simpa [Xc, e_H] using hcov
    have herase_part : Γ.erase γ =
        (Finset.Ico 1 (e_H + 1)).biUnion (subgraphCopiesWithDiffEdges H n γ) :=
      erase_subgraphCopies_eq_biUnion H hγ
    have hdisj : (Finset.Ico 1 (e_H + 1) : Set ℕ).PairwiseDisjoint
        (subgraphCopiesWithDiffEdges H n γ) :=
      (pairwiseDisjoint_subgraphCopiesWithDiffEdges H n γ).subset (Set.subset_univ _)
    rw [hdiag, herase_part, Finset.sum_biUnion hdisj]
    have hsum_t : ∀ t ∈ Finset.Ico 1 (e_H + 1),
        (∑ β ∈ subgraphCopiesWithDiffEdges H n γ t,
            ∫ G, Xc γ G * Xc β G ∂erdosRenyi n p) =
          ((Γ_t t).card : ℝ) * (p ^ e_H * (p ^ t - p ^ e_H)) := by
      intro t _
      have hterm : ∀ β ∈ subgraphCopiesWithDiffEdges H n γ t,
          ∫ G, Xc γ G * Xc β G ∂erdosRenyi n p = p ^ e_H * (p ^ t - p ^ e_H) := by
        intro β hβ
        rcases mem_subgraphCopiesWithDiffEdges.mp hβ with ⟨hβ_mem, hβ_diff⟩
        have hcov := covariance_subgraphCopyIndicator hp0 hp1 hγ hβ_mem
        dsimp only [Xc]
        rw [hcov, hβ_diff]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
        card_subgraphCopiesWithDiffEdges_eq H hγ hα t]
    rw [Finset.sum_congr rfl hsum_t]
    have hdrop_top :
        (∑ t ∈ Finset.Ico 1 (e_H + 1), ((Γ_t t).card : ℝ) * (p ^ e_H * (p ^ t - p ^ e_H))) =
          ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ e_H * (p ^ t - p ^ e_H)) := by
      rcases Nat.eq_zero_or_pos e_H with he0 | he_pos
      · simp [he0]
      · rw [Finset.sum_Ico_succ_top he_pos, sub_self, mul_zero, mul_zero, add_zero]
    rw [hdrop_top, mul_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  dsimp only [lam]
  ring

end SteinMethod
