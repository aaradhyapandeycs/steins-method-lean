/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Subgraph.Combinatorics
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Triangle Copy Combinatorics and Asymptotics (`Formalization.PoissonSizeBias.Subgraph.Triangles`)

Develops the combinatorial and asymptotic components of Example 4.7 (*Triangles*,
`SteinIntro.tex:2334-2343`, eq. `(4.13)` `\label{124}`):

* `ncard_edgeSet_cycleGraph_three`: `(SimpleGraph.cycleGraph 3).edgeSet.ncard = 3`.
* `card_subgraphCopies_cycleGraph_three`:
  `(subgraphCopies (SimpleGraph.cycleGraph 3) n).card = n.choose 3`.
* `card_subgraphCopiesWithDiffEdges_cycleGraph_three_one`:
  `(subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph 3) n α 1).card = 0`.
* `card_subgraphCopiesWithDiffEdges_cycleGraph_three_two`:
  `(subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph 3) n α 2).card = 3 * (n - 3)`.
* `subgraphCount_cycleGraph_three_eq_ncard_cliqueSet`:
  `subgraphCount (SimpleGraph.cycleGraph 3) n G = (G.cliqueSet 3).ncard`.
* `Ex4_7_asymptotics`: order-$1/n$ asymptotic behavior of the Example 4.7 bound when
  $p_n \asymp 1/n$.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### 1. Edge count and non-isolation of `cycleGraph 3` -/

/-- `SimpleGraph.cycleGraph 3` has `3` edges (`SteinIntro.tex:2335`). -/
theorem ncard_edgeSet_cycleGraph_three :
    (SimpleGraph.cycleGraph 3).edgeSet.ncard = 3 := by
  rw [SimpleGraph.cycleGraph_three_eq_top, ← card_edgePairsOfGraph]
  have huniv : edgePairsOfGraph (⊤ : SimpleGraph (Fin 3)) = Finset.univ := by
    ext ⟨e, hnd⟩
    simp only [mem_edgePairsOfGraph, Finset.mem_univ, iff_true]
    revert hnd
    refine Sym2.ind (fun u v hnd ↦ ?_) e
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
    simpa [Sym2.mk_isDiag_iff] using hnd
  rw [huniv, Finset.card_univ, card_edgePair]
  decide

theorem not_isIsolated_cycleGraph_three (v : Fin 3) :
    ¬ (SimpleGraph.cycleGraph 3).IsIsolated v := by
  rw [SimpleGraph.cycleGraph_three_eq_top]
  intro hiso
  fin_cases v
  · exact hiso 1 (by decide)
  · exact hiso 0 (by decide)
  · exact hiso 0 (by decide)

/-! ### 2. Bijection between vertex triples and `subgraphCopies (cycleGraph 3) n` -/

/-- Subgraph of $K_n$ whose edges are all pairs of distinct vertices in `t : Finset (Fin n)`. -/
def triangleSubgraph {n : ℕ} (t : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ∈ t ∧ v ∈ t ∧ u ≠ v
  symm := ⟨fun _ _ ⟨hu, hv, huv⟩ ↦ ⟨hv, hu, huv.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, hne⟩ ↦ hne rfl⟩

@[simp]
theorem triangleSubgraph_adj {n : ℕ} (t : Finset (Fin n)) (u v : Fin n) :
    (triangleSubgraph t).Adj u v ↔ u ∈ t ∧ v ∈ t ∧ u ≠ v :=
  Iff.rfl

/-- Pushing `cycleGraph 3` along `f` gives `triangleSubgraph (Finset.univ.map f)`. -/
theorem embedGraph_cycleGraph_three_eq {n : ℕ} (f : Fin 3 ↪ Fin n) :
    embedGraph (SimpleGraph.cycleGraph 3) f = triangleSubgraph (Finset.univ.map f) := by
  rw [SimpleGraph.cycleGraph_three_eq_top]
  ext u v
  simp only [embedGraph_adj, SimpleGraph.top_adj, triangleSubgraph_adj, Finset.mem_map,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, y, rfl, rfl, hxy⟩
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩, f.injective.ne hxy⟩
  · rintro ⟨⟨x, rfl⟩, ⟨y, rfl⟩, huv⟩
    exact ⟨x, y, rfl, rfl, fun hxy ↦ huv (congrArg f hxy)⟩

/-- For any `t : Finset (Fin n)` with `2 ≤ t.card`, a vertex `u` is incident to an edge of
`triangleSubgraph t` iff `u ∈ t`. -/
theorem exists_adj_triangleSubgraph_iff {n : ℕ} {t : Finset (Fin n)} (ht : 2 ≤ t.card)
    (u : Fin n) :
    (∃ v : Fin n, (triangleSubgraph t).Adj u v) ↔ u ∈ t := by
  constructor
  · rintro ⟨v, hu, _, _⟩
    exact hu
  · intro hu
    have hcard_erase : 0 < (t.erase u).card := by
      rw [Finset.card_erase_of_mem hu]
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard_erase
    rcases Finset.mem_erase.mp hv with ⟨hvu, hvt⟩
    exact ⟨v, hu, hvt, hvu.symm⟩

/-- `triangleSubgraph` is injective on `Finset`s of cardinality at least `2`. -/
theorem triangleSubgraph_injective_of_two_le_card {n : ℕ} {t₁ t₂ : Finset (Fin n)}
    (ht₁ : 2 ≤ t₁.card) (ht₂ : 2 ≤ t₂.card)
    (h : triangleSubgraph t₁ = triangleSubgraph t₂) :
    t₁ = t₂ := by
  ext u
  rw [← exists_adj_triangleSubgraph_iff ht₁, ← exists_adj_triangleSubgraph_iff ht₂, h]

/-- Every `t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3` yields a copy of `cycleGraph 3` in
$K_n$. -/
theorem triangleSubgraph_mem_subgraphCopies {n : ℕ} {t : Finset (Fin n)}
    (ht : t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3) :
    triangleSubgraph t ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n := by
  have ht_card : t.card = 3 := (Finset.mem_powersetCard.mp ht).2
  let e : Fin 3 ≃ {x : Fin n // x ∈ t} :=
    (Fintype.equivFinOfCardEq
      ((Fintype.card_coe t).trans ht_card)).symm
  let f : Fin 3 ↪ Fin n := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hmap : Finset.univ.map f = t := by
    ext u
    simp only [Finset.mem_map, Finset.mem_univ, true_and, f, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hu
      exact ⟨e.symm ⟨u, hu⟩, by simp⟩
  rw [mem_subgraphCopies]
  exact ⟨f, by rw [embedGraph_cycleGraph_three_eq, hmap]⟩

/-- Characterization of `subgraphCopies (SimpleGraph.cycleGraph 3) n` as the image of
`(Finset.univ : Finset (Fin n)).powersetCard 3` under `triangleSubgraph`. -/
theorem mem_subgraphCopies_cycleGraph_three_iff {n : ℕ} {α : SimpleGraph (Fin n)} :
    α ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n ↔
      ∃ t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3, α = triangleSubgraph t := by
  rw [mem_subgraphCopies]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨Finset.univ.map f, ?_, embedGraph_cycleGraph_three_eq f⟩
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by simp⟩
  · rintro ⟨t, ht, rfl⟩
    exact mem_subgraphCopies.mp (triangleSubgraph_mem_subgraphCopies ht)

/-- There are $\binom{n}{3}$ copies of a triangle in $K_n$ (`SteinIntro.tex:2341`). -/
theorem card_subgraphCopies_cycleGraph_three (n : ℕ) :
    (subgraphCopies (SimpleGraph.cycleGraph 3) n).card = n.choose 3 := by
  have hpow : ((Finset.univ : Finset (Fin n)).powersetCard 3).card = n.choose 3 := by simp
  rw [← hpow]
  symm
  refine Finset.card_bij (fun t _ ↦ triangleSubgraph t) ?_ ?_ ?_
  · intro t ht
    exact triangleSubgraph_mem_subgraphCopies ht
  · intro t₁ ht₁ t₂ ht₂ h
    have h₁ : t₁.card = 3 := (Finset.mem_powersetCard.mp ht₁).2
    have h₂ : t₂.card = 3 := (Finset.mem_powersetCard.mp ht₂).2
    exact triangleSubgraph_injective_of_two_le_card (by omega) (by omega) h
  · intro α hα
    rcases mem_subgraphCopies_cycleGraph_three_iff.mp hα with ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-! ### 3. Agreement of `subgraphCount (cycleGraph 3) n G` with `(G.cliqueSet 3).ncard` -/

theorem triangleSubgraph_le_iff_isNClique {n : ℕ} {t : Finset (Fin n)} (ht : t.card = 3)
    (G : SimpleGraph (Fin n)) :
    triangleSubgraph t ≤ G ↔ G.IsNClique 3 t := by
  rw [SimpleGraph.isNClique_iff]
  constructor
  · intro hle
    refine ⟨fun u hu v hv huv ↦ hle ⟨hu, hv, huv⟩, ht⟩
  · rintro ⟨hcl, _⟩ u v ⟨hu, hv, huv⟩
    exact hcl hu hv huv

/-- For every graph `G` on `Fin n`, `subgraphCount (SimpleGraph.cycleGraph 3) n G` equals
`(G.cliqueSet 3).ncard` (`SteinIntro.tex:2334-2338`). -/
theorem subgraphCount_cycleGraph_three_eq_ncard_cliqueSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    subgraphCount (SimpleGraph.cycleGraph 3) n G = (G.cliqueSet 3).ncard := by
  classical
  let T : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard 3
  let S : Finset (Finset (Fin n)) := T.filter fun t ↦ G.IsNClique 3 t
  have hS : (S : Set (Finset (Fin n))) = G.cliqueSet 3 := by
    ext t
    simp only [S, T, Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, SimpleGraph.mem_cliqueSet_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.card_eq, h⟩⟩
  rw [← hS, Set.ncard_coe_finset]
  unfold subgraphCount
  have hsum_bij :
      (∑ α ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n, subgraphCopyIndicator α G) =
        ∑ t ∈ T, subgraphCopyIndicator (triangleSubgraph t) G := by
    symm
    refine Finset.sum_bij (fun t _ ↦ triangleSubgraph t) ?_ ?_ ?_ (fun _ _ ↦ rfl)
    · intro t ht
      exact triangleSubgraph_mem_subgraphCopies ht
    · intro t₁ ht₁ t₂ ht₂ h
      have h₁ : t₁.card = 3 := (Finset.mem_powersetCard.mp ht₁).2
      have h₂ : t₂.card = 3 := (Finset.mem_powersetCard.mp ht₂).2
      exact triangleSubgraph_injective_of_two_le_card (by omega) (by omega) h
    · intro α hα
      rcases mem_subgraphCopies_cycleGraph_three_iff.mp hα with ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
  rw [hsum_bij]
  have hterm : ∀ t ∈ T,
      subgraphCopyIndicator (triangleSubgraph t) G = if G.IsNClique 3 t then 1 else 0 := by
    intro t ht
    have ht_card : t.card = 3 := (Finset.mem_powersetCard.mp ht).2
    by_cases hcl : G.IsNClique 3 t
    · have hle := (triangleSubgraph_le_iff_isNClique ht_card G).mpr hcl
      simp [hcl, subgraphCopyIndicator_of_le hle]
    · have hnle := mt (triangleSubgraph_le_iff_isNClique ht_card G).mp hcl
      simp [hcl, subgraphCopyIndicator_of_not_le hnle]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]

/-! ### 4. Edge-difference counts $|\Gamma_\alpha^1| = 0$ and $|\Gamma_\alpha^2| = 3(n - 3)$ -/

theorem triangleSubgraph_inf {n : ℕ} (s t : Finset (Fin n)) :
    triangleSubgraph s ⊓ triangleSubgraph t = triangleSubgraph (s ∩ t) := by
  ext u v
  simp only [SimpleGraph.inf_adj, triangleSubgraph_adj, Finset.mem_inter]
  tauto

theorem ncard_edgeSet_triangleSubgraph_of_card_le_one {n : ℕ} {s : Finset (Fin n)}
    (hs : s.card ≤ 1) :
    (triangleSubgraph s).edgeSet.ncard = 0 := by
  rw [Set.ncard_eq_zero (Set.toFinite _), Set.eq_empty_iff_forall_notMem]
  intro e he
  revert he
  refine Sym2.ind (fun u v he ↦ ?_) e
  rw [SimpleGraph.mem_edgeSet, triangleSubgraph_adj] at he
  rcases he with ⟨hu, hv, huv⟩
  exact huv (Finset.card_le_one.mp hs u hu v hv)

theorem ncard_edgeSet_triangleSubgraph_of_card_eq_two {n : ℕ} {s : Finset (Fin n)}
    (hs : s.card = 2) :
    (triangleSubgraph s).edgeSet.ncard = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs
  have heq : (triangleSubgraph {a, b}).edgeSet = {s(a, b)} := by
    ext e
    refine Sym2.ind (fun u v ↦ ?_) e
    simp only [SimpleGraph.mem_edgeSet, triangleSubgraph_adj, Finset.mem_insert,
      Finset.mem_singleton, Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨ rfl | rfl, rfl | rfl, huv⟩
      · exact (huv rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (huv rfl).elim
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨Or.inl rfl, Or.inr rfl, hab⟩
      · exact ⟨Or.inr rfl, Or.inl rfl, hab.symm⟩
  rw [heq, Set.ncard_singleton]

theorem ncard_edgeSet_triangleSubgraph_of_card_eq_three {n : ℕ} {t : Finset (Fin n)}
    (ht : t.card = 3) :
    (triangleSubgraph t).edgeSet.ncard = 3 := by
  have hmem : t ∈ (Finset.univ : Finset (Fin n)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ t, ht⟩
  rw [ncard_edgeSet_of_mem_subgraphCopies (triangleSubgraph_mem_subgraphCopies hmem),
    ncard_edgeSet_cycleGraph_three]

theorem ncard_edgeSet_diff_triangleSubgraph {n : ℕ} {t₁ t₂ : Finset (Fin n)}
    (_ht₁ : t₁.card = 3) (ht₂ : t₂.card = 3) :
    ((triangleSubgraph t₂).edgeSet \ (triangleSubgraph t₁).edgeSet).ncard =
      3 - (triangleSubgraph (t₁ ∩ t₂)).edgeSet.ncard := by
  have hinter : (triangleSubgraph t₂).edgeSet ∩ (triangleSubgraph t₁).edgeSet =
      (triangleSubgraph (t₁ ∩ t₂)).edgeSet := by
    rw [Set.inter_comm, ← SimpleGraph.edgeSet_inf, triangleSubgraph_inf]
  have hdiff : (triangleSubgraph t₂).edgeSet \ (triangleSubgraph t₁).edgeSet =
      (triangleSubgraph t₂).edgeSet \
        ((triangleSubgraph t₂).edgeSet ∩ (triangleSubgraph t₁).edgeSet) := by
    ext e
    simp
  have hsub : (triangleSubgraph (t₁ ∩ t₂)).edgeSet ⊆ (triangleSubgraph t₂).edgeSet := by
    rw [← hinter]
    exact Set.inter_subset_left
  rw [hdiff, hinter, Set.ncard_sdiff hsub (Set.toFinite _),
    ncard_edgeSet_triangleSubgraph_of_card_eq_three ht₂]

/-- No two copies of a triangle in $K_n$ differ by exactly `1` edge (`|\Gamma_\alpha^1| = 0`,
`SteinIntro.tex:2335-2336`). -/
theorem card_subgraphCopiesWithDiffEdges_cycleGraph_three_one {n : ℕ}
    {α : SimpleGraph (Fin n)} (hα : α ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n) :
    (subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph 3) n α 1).card = 0 := by
  rcases mem_subgraphCopies_cycleGraph_three_iff.mp hα with ⟨t₁, ht₁_mem, rfl⟩
  have ht₁ : t₁.card = 3 := (Finset.mem_powersetCard.mp ht₁_mem).2
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro β hβ
  rcases mem_subgraphCopiesWithDiffEdges.mp hβ with ⟨hβ_mem, hdiff⟩
  rcases mem_subgraphCopies_cycleGraph_three_iff.mp hβ_mem with ⟨t₂, ht₂_mem, rfl⟩
  have ht₂ : t₂.card = 3 := (Finset.mem_powersetCard.mp ht₂_mem).2
  rw [ncard_edgeSet_diff_triangleSubgraph ht₁ ht₂] at hdiff
  have hle3 : (t₁ ∩ t₂).card ≤ 3 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq ht₁
  rcases le_or_gt (t₁ ∩ t₂).card 1 with hle1 | hgt1
  · rw [ncard_edgeSet_triangleSubgraph_of_card_le_one hle1] at hdiff
    omega
  · rcases eq_or_ne (t₁ ∩ t₂).card 2 with h2 | hne2
    · rw [ncard_edgeSet_triangleSubgraph_of_card_eq_two h2] at hdiff
      omega
    · have h3 : (t₁ ∩ t₂).card = 3 := by omega
      rw [ncard_edgeSet_triangleSubgraph_of_card_eq_three h3] at hdiff
      omega

private lemma card_filter_inter_eq_two_powersetCard {n : ℕ} {t₁ : Finset (Fin n)}
    (ht₁ : t₁.card = 3) :
    (((Finset.univ : Finset (Fin n)).powersetCard 3).filter
        fun t₂ ↦ (t₁ ∩ t₂).card = 2).card =
      3 * (n - 3) := by
  let P : Finset (Finset (Fin n) × Finset (Fin n)) :=
    t₁.powersetCard 2 ×ˢ ((Finset.univ \ t₁).powersetCard 1)
  have hbij :
      (((Finset.univ : Finset (Fin n)).powersetCard 3).filter
          fun t₂ ↦ (t₁ ∩ t₂).card = 2).card = P.card := by
    refine Finset.card_nbij' (fun s ↦ (t₁ ∩ s, s \ t₁)) (fun p ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and] at hs
      simp only [P, Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hs.2⟩, ⟨?_, ?_⟩⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ x, hx.2⟩
      · have hsum := Finset.card_sdiff_add_card_inter s t₁
        rw [Finset.inter_comm, hs.2, hs.1] at hsum
        omega
    · rintro ⟨u, v⟩ hp
      simp only [P, Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hp
      rcases hp with ⟨⟨hu_sub, hu_card⟩, ⟨hv_sub, hv_card⟩⟩
      have hdisj_tv : Disjoint t₁ v := by
        rw [Finset.disjoint_left]
        intro x hxt hxv
        exact (Finset.mem_sdiff.mp (hv_sub hxv)).2 hxt
      have hdisj_uv : Disjoint u v := hdisj_tv.mono_left hu_sub
      have htu : t₁ ∩ (u ∪ v) = u := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        refine ⟨fun ⟨hxt, hxuv⟩ ↦ ?_, fun hxu ↦ ⟨hu_sub hxu, Or.inl hxu⟩⟩
        rcases hxuv with hxu | hxv
        · exact hxu
        · exact ((Finset.mem_sdiff.mp (hv_sub hxv)).2 hxt).elim
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      exact ⟨by rw [Finset.card_union_of_disjoint hdisj_uv, hu_card, hv_card],
        by rw [htu, hu_card]⟩
    · intro s _
      ext x
      by_cases hxt : x ∈ t₁ <;> simp [hxt]
    · rintro ⟨u, v⟩ hp
      simp only [P, Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hp
      rcases hp with ⟨⟨hu_sub, _⟩, ⟨hv_sub, _⟩⟩
      refine Prod.ext ?_ ?_
      · ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        refine ⟨fun ⟨hxt, hxuv⟩ ↦ ?_, fun hxu ↦ ⟨hu_sub hxu, Or.inl hxu⟩⟩
        rcases hxuv with hxu | hxv
        · exact hxu
        · exact ((Finset.mem_sdiff.mp (hv_sub hxv)).2 hxt).elim
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        refine ⟨fun ⟨hxuv, hxt⟩ ↦ ?_,
          fun hxv ↦ ⟨Or.inr hxv, (Finset.mem_sdiff.mp (hv_sub hxv)).2⟩⟩
        rcases hxuv with hxu | hxv
        · exact (hxt (hu_sub hxu)).elim
        · exact hxv
  have h32 : Nat.choose 3 2 = 3 := rfl
  rw [hbij]
  simp only [P, Finset.card_product, Finset.card_powersetCard, ht₁, h32, Nat.choose_one_right,
    Finset.card_sdiff_of_subset (Finset.subset_univ t₁), Finset.card_univ, Fintype.card_fin]

/-- For every triangle $\alpha \in \Gamma$ in $K_n$, there are $3(n - 3)$ triangles sharing
exactly one edge with $\alpha$ (`|\Gamma_\alpha^2| = 3(n - 3)`, `SteinIntro.tex:2335-2336`). -/
theorem card_subgraphCopiesWithDiffEdges_cycleGraph_three_two {n : ℕ}
    {α : SimpleGraph (Fin n)} (hα : α ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n) :
    (subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph 3) n α 2).card = 3 * (n - 3) := by
  rcases mem_subgraphCopies_cycleGraph_three_iff.mp hα with ⟨t₁, ht₁_mem, rfl⟩
  have ht₁ : t₁.card = 3 := (Finset.mem_powersetCard.mp ht₁_mem).2
  rw [← card_filter_inter_eq_two_powersetCard ht₁]
  symm
  refine Finset.card_bij (fun t₂ _ ↦ triangleSubgraph t₂) ?_ ?_ ?_
  · intro t₂ ht₂
    rcases Finset.mem_filter.mp ht₂ with ⟨ht₂_mem, hinter2⟩
    have ht₂_card : t₂.card = 3 := (Finset.mem_powersetCard.mp ht₂_mem).2
    rw [mem_subgraphCopiesWithDiffEdges]
    refine ⟨triangleSubgraph_mem_subgraphCopies ht₂_mem, ?_⟩
    rw [ncard_edgeSet_diff_triangleSubgraph ht₁ ht₂_card,
      ncard_edgeSet_triangleSubgraph_of_card_eq_two hinter2]
  · intro s₁ hs₁ s₂ hs₂ h
    have h₁ : s₁.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs₁).1).2
    have h₂ : s₂.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs₂).1).2
    exact triangleSubgraph_injective_of_two_le_card (by omega) (by omega) h
  · intro β hβ
    rcases mem_subgraphCopiesWithDiffEdges.mp hβ with ⟨hβ_mem, hdiff2⟩
    rcases mem_subgraphCopies_cycleGraph_three_iff.mp hβ_mem with ⟨t₂, ht₂_mem, rfl⟩
    have ht₂ : t₂.card = 3 := (Finset.mem_powersetCard.mp ht₂_mem).2
    refine ⟨t₂, Finset.mem_filter.mpr ⟨ht₂_mem, ?_⟩, rfl⟩
    rw [ncard_edgeSet_diff_triangleSubgraph ht₁ ht₂] at hdiff2
    have hle3 : (t₁ ∩ t₂).card ≤ 3 :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq ht₁
    rcases le_or_gt (t₁ ∩ t₂).card 1 with hle1 | hgt1
    · rw [ncard_edgeSet_triangleSubgraph_of_card_le_one hle1] at hdiff2
      omega
    · rcases eq_or_ne (t₁ ∩ t₂).card 2 with h2 | hne2
      · exact h2
      · have h3 : (t₁ ∩ t₂).card = 3 := by omega
        rw [ncard_edgeSet_triangleSubgraph_of_card_eq_three h3] at hdiff2
        omega

/-! ### 5. Falling-factorial / binomial bounds and Example 4.7 asymptotics -/

/-- Lower and upper bounds on `n.descFactorial k` for `2 * k ≤ n`:
`(n - k) ^ k ≤ n.descFactorial k ≤ n ^ k`. -/
theorem pow_sub_le_descFactorial (n k : ℕ) :
    (n - k) ^ k ≤ n.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, pow_succ']
    have h1 : (n - (k + 1)) ^ k ≤ (n - k) ^ k :=
      Nat.pow_le_pow_left (by omega) k
    exact Nat.mul_le_mul (by omega) (h1.trans ih)

theorem choose_real_bounds_of_two_mul_le {n k : ℕ} (hk : 2 * k ≤ n) :
    ((n : ℝ) / 2) ^ k / (k.factorial : ℝ) ≤ (n.choose k : ℝ) ∧
      (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (k.factorial : ℝ) := by
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hdesc_eq : (n.descFactorial k : ℝ) = (k.factorial : ℝ) * (n.choose k : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n k
  have hlo_nat : (((n - k) ^ k : ℕ) : ℝ) ≤ (n.descFactorial k : ℝ) :=
    Nat.cast_le.mpr (pow_sub_le_descFactorial n k)
  have hhi_nat : (n.descFactorial k : ℝ) ≤ ((n ^ k : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.descFactorial_le_pow n k)
  have hsub_ge : (n : ℝ) / 2 ≤ ((n - k : ℕ) : ℝ) := by
    have hle : k ≤ n := by omega
    rw [Nat.cast_sub hle]
    have h2k : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    linarith
  have hpow_lo : ((n : ℝ) / 2) ^ k ≤ (n.descFactorial k : ℝ) := by
    have h1 : ((n : ℝ) / 2) ^ k ≤ ((n - k : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) hsub_ge k
    exact h1.trans (by simpa only [Nat.cast_pow] using hlo_nat)
  constructor
  · rw [div_le_iff₀ hfac_pos, mul_comm]
    exact hpow_lo.trans_eq hdesc_eq
  · rw [le_div_iff₀ hfac_pos, mul_comm, ← hdesc_eq]
    simpa using hhi_nat

/-- Asymptotic rate of the Example 4.7 triangle Poisson bound (`SteinIntro.tex:2341-2342`):
when $p_n \asymp 1/n$, the upper bound `(4.13)` is of exact order $1/n$. -/
theorem ex4_7_asymptotics {p : ℕ → ℝ} {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hp : ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) :
    let lam : ℕ → ℝ := fun n ↦ (n.choose 3 : ℝ) * (p n) ^ 3
    let err : ℕ → ℝ :=
      fun n ↦ min 1 (lam n) * ((p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n))
    ∃ B₁ B₂ : ℝ, 0 < B₁ ∧ 0 < B₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ) := by
  intro lam err
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  let L₁ : ℝ := (c₁ / 2) ^ 3 / (Nat.factorial 3 : ℝ)
  have hL₁_pos : 0 < L₁ := by positivity
  let B₁ : ℝ := min 1 L₁ * (3 * c₁ ^ 2 / 4)
  let B₂ : ℝ := c₂ ^ 3 + 3 * c₂ ^ 2
  have hB₁_pos : 0 < B₁ := mul_pos (lt_min zero_lt_one hL₁_pos) (by positivity)
  have hB₂_pos : 0 < B₂ := by positivity
  refine ⟨B₁, B₂, hB₁_pos, hB₂_pos, ?_⟩
  let N₀ : ℕ := max 6 (Nat.ceil (2 * c₂))
  filter_upwards [hp, Filter.eventually_ge_atTop N₀] with n ⟨hp0, hp1, hplo, hphi⟩ hnN₀
  have hn6 : 6 ≤ n := (le_max_left 6 _).trans hnN₀
  have hn_2c2 : 2 * c₂ ≤ (n : ℝ) :=
    (Nat.le_ceil (2 * c₂)).trans (by exact_mod_cast (le_max_right 6 _).trans hnN₀)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  obtain ⟨hch_lo, _⟩ := choose_real_bounds_of_two_mul_le (k := 3) hn6
  have hlam_lo : L₁ ≤ lam n := by
    have hpow_lo : (c₁ / (n : ℝ)) ^ 3 ≤ (p n) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hplo 3
    have hch_nn : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
    calc
      L₁ = (((n : ℝ) / 2) ^ 3 / (Nat.factorial 3 : ℝ)) * (c₁ / (n : ℝ)) ^ 3 := by
        dsimp [L₁]
        field_simp [hn_pos.ne']
      _ ≤ (n.choose 3 : ℝ) * (p n) ^ 3 :=
        mul_le_mul hch_lo hpow_lo (by positivity) hch_nn
  have hmin_lo : min 1 L₁ ≤ min 1 (lam n) := min_le_min_left 1 hlam_lo
  have hmin_hi : min 1 (lam n) ≤ 1 := min_le_left 1 (lam n)
  have hp_le_half : p n ≤ 1 / 2 := by
    have h1 : c₂ / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hn_pos]
      linarith
    exact hphi.trans h1
  have h1p_ge_half : 1 / 2 ≤ 1 - p n := by linarith
  have hn3_ge_half : (n : ℝ) / 2 ≤ (n : ℝ) - 3 := by
    have hn6_r : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    linarith
  have hterm_lo :
      (3 * c₁ ^ 2 / 4) / (n : ℝ) ≤
        (p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n) := by
    have hsq_lo : (c₁ / (n : ℝ)) ^ 2 ≤ (p n) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hplo 2
    have hprod_lo :
        (3 * c₁ ^ 2 / 4) / (n : ℝ) ≤ 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n) := calc
      (3 * c₁ ^ 2 / 4) / (n : ℝ)
        = 3 * ((n : ℝ) / 2) * (c₁ / (n : ℝ)) ^ 2 * (1 / 2) := by
          field_simp [hn_pos.ne']
          ring
      _ ≤ 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n) := by
          have h1 : 3 * ((n : ℝ) / 2) ≤ 3 * ((n : ℝ) - 3) := by linarith
          have h2 :
              3 * ((n : ℝ) / 2) * (c₁ / (n : ℝ)) ^ 2 ≤ 3 * ((n : ℝ) - 3) * (p n) ^ 2 :=
            mul_le_mul h1 hsq_lo (by positivity) (by linarith)
          exact mul_le_mul h2 h1p_ge_half (by positivity)
            (mul_nonneg (by linarith) (sq_nonneg _))
    have hp3_nn : 0 ≤ (p n) ^ 3 := pow_nonneg hp0 3
    linarith
  have hterm_hi :
      (p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n) ≤ B₂ / (n : ℝ) := by
    have hpow3_hi : (p n) ^ 3 ≤ c₂ ^ 3 / (n : ℝ) := by
      have h1 : (p n) ^ 3 ≤ (c₂ / (n : ℝ)) ^ 3 := pow_le_pow_left₀ hp0 hphi 3
      have h2 : (c₂ / (n : ℝ)) ^ 3 ≤ c₂ ^ 3 / (n : ℝ) := by
        rw [div_pow, div_le_div_iff_of_pos_left (by positivity) (by positivity) hn_pos]
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
      exact h1.trans h2
    have hpow2_hi : 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n) ≤ 3 * c₂ ^ 2 / (n : ℝ) := by
      have hsq_hi : (p n) ^ 2 ≤ (c₂ / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hp0 hphi 2
      have h1 : 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n) ≤
          3 * (n : ℝ) * (c₂ / (n : ℝ)) ^ 2 * 1 := by
        refine mul_le_mul ?_ (by linarith) (by linarith) (by positivity)
        exact mul_le_mul (by linarith) hsq_hi (sq_nonneg _) (by positivity)
      have h2 : 3 * (n : ℝ) * (c₂ / (n : ℝ)) ^ 2 * 1 = 3 * c₂ ^ 2 / (n : ℝ) := by
        field_simp [hn_pos.ne']
      exact h1.trans_eq h2
    dsimp [B₂]
    rw [add_div]
    exact add_le_add hpow3_hi hpow2_hi
  constructor
  · calc
      B₁ / (n : ℝ) = min 1 L₁ * ((3 * c₁ ^ 2 / 4) / (n : ℝ)) := by
        dsimp [B₁]
        ring
      _ ≤ min 1 (lam n) * ((p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n)) :=
        mul_le_mul hmin_lo hterm_lo (by positivity) (le_min zero_le_one (by positivity))
  · calc
      min 1 (lam n) * ((p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n))
        ≤ 1 * (B₂ / (n : ℝ)) :=
          mul_le_mul hmin_hi hterm_hi
            (by linarith [hterm_lo,
              show (0 : ℝ) ≤ (3 * c₁ ^ 2 / 4) / (n : ℝ) by positivity])
            zero_le_one
      _ = B₂ / (n : ℝ) := one_mul _

end SteinMethod
