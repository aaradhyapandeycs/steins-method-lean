/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonSizeBiasSubgraph

/-!
# Subgraph Copy Basic Lemmas and Non-Vacuity (`Formalization.PoissonSizeBias.Subgraph.Defs`)

Basic `@[simp]` characterizations and non-vacuity sanity witnesses for the subgraph-count
definitions in `Formalization.Defs.PoissonSizeBiasSubgraph` (`SteinIntro.tex:2279-2369`).
-/

namespace SteinMethod

@[simp]
theorem embedGraph_adj {V : Type*} {n : ℕ} (H : SimpleGraph V) (f : V ↪ Fin n) (u v : Fin n) :
    (embedGraph H f).Adj u v ↔ ∃ x y : V, f x = u ∧ f y = v ∧ H.Adj x y :=
  Iff.rfl

@[simp]
theorem embedGraph_adj_apply {V : Type*} {n : ℕ} (H : SimpleGraph V) (f : V ↪ Fin n) (x y : V) :
    (embedGraph H f).Adj (f x) (f y) ↔ H.Adj x y := by
  constructor
  · rintro ⟨x', y', hx, hy, hxy⟩
    exact (f.injective hx) ▸ (f.injective hy) ▸ hxy
  · intro hxy
    exact ⟨x, y, rfl, rfl, hxy⟩

@[simp]
theorem embedGraph_refl {n : ℕ} (H : SimpleGraph (Fin n)) :
    embedGraph H (Function.Embedding.refl (Fin n)) = H := by
  ext u v
  simp

@[simp]
theorem mem_subgraphCopies {V : Type*} {H : SimpleGraph V} {n : ℕ} {α : SimpleGraph (Fin n)} :
    α ∈ subgraphCopies H n ↔ ∃ f : V ↪ Fin n, α = embedGraph H f := by
  simp [subgraphCopies]

theorem subgraphCopyIndicator_of_le {n : ℕ} {α G : SimpleGraph (Fin n)} (h : α ≤ G) :
    subgraphCopyIndicator α G = 1 := by
  simp [subgraphCopyIndicator, h]

theorem subgraphCopyIndicator_of_not_le {n : ℕ} {α G : SimpleGraph (Fin n)} (h : ¬ α ≤ G) :
    subgraphCopyIndicator α G = 0 := by
  simp [subgraphCopyIndicator, h]

@[simp]
theorem subgraphCopyIndicator_eq_one_iff {n : ℕ} {α G : SimpleGraph (Fin n)} :
    subgraphCopyIndicator α G = 1 ↔ α ≤ G := by
  by_cases h : α ≤ G
  · simp [subgraphCopyIndicator_of_le h, h]
  · simp [subgraphCopyIndicator_of_not_le h, h]

@[simp]
theorem subgraphCopyIndicator_eq_zero_iff {n : ℕ} {α G : SimpleGraph (Fin n)} :
    subgraphCopyIndicator α G = 0 ↔ ¬ α ≤ G := by
  by_cases h : α ≤ G
  · simp [subgraphCopyIndicator_of_le h, h]
  · simp [subgraphCopyIndicator_of_not_le h, h]

theorem subgraphCopyIndicator_zero_or_one {n : ℕ} (α G : SimpleGraph (Fin n)) :
    subgraphCopyIndicator α G = 0 ∨ subgraphCopyIndicator α G = 1 := by
  by_cases h : α ≤ G
  · exact Or.inr (subgraphCopyIndicator_of_le h)
  · exact Or.inl (subgraphCopyIndicator_of_not_le h)

@[simp]
theorem mem_subgraphCopiesWithDiffEdges {V : Type*} {H : SimpleGraph V} {n : ℕ}
    {α β : SimpleGraph (Fin n)} {t : ℕ} :
    β ∈ subgraphCopiesWithDiffEdges H n α t ↔
      β ∈ subgraphCopies H n ∧ (β.edgeSet \ α.edgeSet).ncard = t := by
  unfold subgraphCopiesWithDiffEdges
  simp

/-! ### Non-vacuity sanity witnesses -/

/-- Non-vacuity witness for `embedGraph`: embedding $K_2$ via the identity on `Fin 2` makes `0` and
`1` adjacent. -/
theorem embedGraph_nonvacuous :
    (embedGraph (⊤ : SimpleGraph (Fin 2)) (Function.Embedding.refl (Fin 2))).Adj 0 1 := by
  rw [embedGraph_refl]
  decide

/-- Non-vacuity witness for `subgraphCopies`: $K_2$ is a copy of $K_2$ in $K_2$. -/
theorem subgraphCopies_nonvacuous :
    (⊤ : SimpleGraph (Fin 2)) ∈ subgraphCopies (⊤ : SimpleGraph (Fin 2)) 2 := by
  rw [mem_subgraphCopies]
  exact ⟨Function.Embedding.refl (Fin 2), (embedGraph_refl _).symm⟩

/-- Non-vacuity witness for `subgraphCopyIndicator`: the indicator of $K_2$ is `1` on $K_2$ and `0`
on the empty graph $\bot$ on `Fin 2`. -/
theorem subgraphCopyIndicator_nonvacuous :
    subgraphCopyIndicator (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 2)) = 1 ∧
      subgraphCopyIndicator (⊤ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2)) = 0 := by
  refine ⟨subgraphCopyIndicator_of_le le_rfl, subgraphCopyIndicator_of_not_le ?_⟩
  intro h
  have hadj : (⊥ : SimpleGraph (Fin 2)).Adj 0 1 :=
    h (by decide : (⊤ : SimpleGraph (Fin 2)).Adj 0 1)
  exact hadj

/-- Non-vacuity witness for `subgraphCount`: $K_2$ contains `1` copy of $K_2$, whereas the empty
graph on `Fin 2` contains `0` copies of $K_2$. -/
theorem subgraphCount_nonvacuous :
    subgraphCount (⊤ : SimpleGraph (Fin 2)) 2 (⊤ : SimpleGraph (Fin 2)) = 1 ∧
      subgraphCount (⊤ : SimpleGraph (Fin 2)) 2 (⊥ : SimpleGraph (Fin 2)) = 0 := by
  have hsub : subgraphCopies (⊤ : SimpleGraph (Fin 2)) 2 = {⊤} := by
    ext α
    rw [mem_subgraphCopies, Finset.mem_singleton]
    refine ⟨?_, fun h ↦
      ⟨Function.Embedding.refl (Fin 2), h.trans (embedGraph_refl _).symm⟩⟩
    rintro ⟨f, rfl⟩
    ext u v
    constructor
    · intro h
      exact SimpleGraph.top_adj u v |>.mpr h.ne
    · intro h
      have huv : u ≠ v := h.ne
      have hsurj : Function.Surjective f :=
        Finite.surjective_of_injective f.injective
      obtain ⟨x, rfl⟩ := hsurj u
      obtain ⟨y, rfl⟩ := hsurj v
      have hxy : x ≠ y := fun hxy ↦ huv (congrArg f hxy)
      exact (embedGraph_adj_apply _ f x y).mpr (SimpleGraph.top_adj x y |>.mpr hxy)
  unfold subgraphCount
  rw [hsub, Finset.sum_singleton, Finset.sum_singleton]
  exact subgraphCopyIndicator_nonvacuous

/-- Non-vacuity witness for `subgraphCopiesWithDiffEdges`: $K_2$ has `0` edges not in $K_2$. -/
theorem subgraphCopiesWithDiffEdges_nonvacuous :
    (⊤ : SimpleGraph (Fin 2)) ∈
      subgraphCopiesWithDiffEdges (⊤ : SimpleGraph (Fin 2)) 2 (⊤ : SimpleGraph (Fin 2)) 0 := by
  rw [mem_subgraphCopiesWithDiffEdges]
  exact ⟨subgraphCopies_nonvacuous, by simp⟩

end SteinMethod
