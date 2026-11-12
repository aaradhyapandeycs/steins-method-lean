/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.PoissonExch
import Formalization.Defs.PoissonSizeBias
import Formalization.Defs.PoissonSizeBiasSubgraph
import Formalization.Defs.RandomGraph
import Formalization.RandomGraph.ErdosRenyi
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
# Canonical Graph and Permutation Bridges (`Formalization.Canon.GraphsAndPerms`)

Bridges project-specific definitions for random graphs, subgraph copies, and permutations to
canonical Mathlib counterparts:
* `edgePairEquivOffDiag`: equivalence of `EdgePair n` with `Sym2.diagSetᶜ`
  (`SteinIntro.tex:918-920`, `Formalization/Defs/RandomGraph.lean:28`).
* `embedGraph_eq_map`: `embedGraph H f` matches Mathlib's `SimpleGraph.map`
  (`SteinIntro.tex:2280-2287`, `Formalization/Defs/PoissonSizeBiasSubgraph.lean:33`).
* `mem_subgraphCopies_iff_exists_map`: copy characterization via `H.map`
  (`SteinIntro.tex:2282-2287`, `Formalization/Defs/PoissonSizeBiasSubgraph.lean:42`).
* `coe_edgeIndNat_eq_edgeIndicator`: natural and real edge indicator agreement
  (`SteinIntro.tex:2424-2449`, `Formalization/Defs/PoissonSizeBias.lean:64`).
* `subgraphEdgeFn_eq_subgraphCopyIndicator`: subgraph vector indicator agreement
  (`SteinIntro.tex:2424-2427`, `Formalization/Defs/PoissonSizeBias.lean:76`).
* `numFixedPoints_eq_ncard_fixedPoints` & `numFixedPoints_eq_sub_support_card`:
  fixed point count matching `Function.fixedPoints` and `Equiv.Perm.support`
  (`SteinIntro.tex:2683`, `Formalization/Defs/PoissonExch.lean:44`).
* `numTwoCycles_eq_count_cycleType`: 2-cycle count matching `Multiset.count 2 π.cycleType`
  (`SteinIntro.tex:2684`, `Formalization/Defs/PoissonExch.lean:50`).
* `erdosRenyi_eq_binomialRandom`: exact equality of `erdosRenyi n p` with Mathlib's
  `SimpleGraph.binomialRandom (Fin n) p` (`SteinIntro.tex:919, 1355`).
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace SteinMethod

/-! ### Edge Pairs and Graph Embeddings -/

/-- Equivalence between project's `EdgePair n` (`SteinIntro.tex:918-920`,
`Formalization/Defs/RandomGraph.lean:28`) and off-diagonal 2-element subsets
`Sym2.diagSetᶜ` on `Fin n`. -/
def edgePairEquivOffDiag (n : ℕ) :
    EdgePair n ≃ ↥(Sym2.diagSetᶜ : Set (Sym2 (Fin n))) :=
  Equiv.refl _

/-- Subgraph embedding `embedGraph H f` (`SteinIntro.tex:2280-2287`,
`Formalization/Defs/PoissonSizeBiasSubgraph.lean:33`) equals Mathlib's `SimpleGraph.map f H`
(`Mathlib/Combinatorics/SimpleGraph/Maps.lean:493`). -/
theorem embedGraph_eq_map {V : Type*} (H : SimpleGraph V) {n : ℕ} (f : V ↪ Fin n) :
    embedGraph H f = H.map f := by
  ext u v
  simp only [embedGraph, SimpleGraph.map_adj]
  constructor
  · rintro ⟨x, y, rfl, rfl, hAdj⟩
    exact ⟨x, y, hAdj, rfl, rfl⟩
  · rintro ⟨x, y, hAdj, rfl, rfl⟩
    exact ⟨x, y, rfl, rfl, hAdj⟩

/-- Membership in `subgraphCopies H n` (`SteinIntro.tex:2282-2287`,
`Formalization/Defs/PoissonSizeBiasSubgraph.lean:42`) characterized by Mathlib's `H.map`. -/
theorem mem_subgraphCopies_iff_exists_map {V : Type*} (H : SimpleGraph V) (n : ℕ)
    (α : SimpleGraph (Fin n)) :
    α ∈ subgraphCopies H n ↔ ∃ f : V ↪ Fin n, α = H.map f := by
  change α ∈ (Set.toFinite {α | ∃ f : V ↪ Fin n, α = embedGraph H f}).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  simp_rw [embedGraph_eq_map]
  rfl

/-- Natural edge indicator `edgeIndNat` (`Formalization/Defs/PoissonSizeBias.lean:64`,
`SteinIntro.tex:2424-2449`) cast to `ℝ` equals real indicator `edgeIndicator`
(`Formalization/Defs/RandomGraph.lean:55`). -/
theorem coe_edgeIndNat_eq_edgeIndicator {n : ℕ} (e : EdgePair n) (G : SimpleGraph (Fin n)) :
    ((edgeIndNat e G : ℕ) : ℝ) = edgeIndicator e G := by
  dsimp [edgeIndNat, edgeIndicator, Set.indicator]
  split_ifs <;> simp

/-- Edge vector representation `subgraphEdgeFn α y` (`SteinIntro.tex:2424-2427`,
`Formalization/Defs/PoissonSizeBias.lean:76`) equals subgraph copy indicator
`subgraphCopyIndicator α (graphOfNatEdgeVec y)`. -/
theorem subgraphEdgeFn_eq_subgraphCopyIndicator {n : ℕ} (α : SimpleGraph (Fin n))
    (y : Fin (Fintype.card (EdgePair n)) → ℕ) :
    subgraphEdgeFn α y = subgraphCopyIndicator α (graphOfNatEdgeVec y) :=
  rfl

/-! ### Permutation Fixed Points and Cycle Types -/

/-- Permutation fixed point count `numFixedPoints π` (`SteinIntro.tex:2683`,
`Formalization/Defs/PoissonExch.lean:44`) equals `Function.fixedPoints π` set cardinality
(`Mathlib/Dynamics/FixedPoints/Basic.lean`). -/
theorem numFixedPoints_eq_ncard_fixedPoints {n : ℕ} (π : Equiv.Perm (Fin n)) :
    numFixedPoints π = (Function.fixedPoints π).ncard := by
  have heq : Function.fixedPoints π = (Finset.univ.filter fun i ↦ π i = i : Set (Fin n)) := by
    ext x
    simp only [Function.fixedPoints, Function.IsFixedPt, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl
  rw [heq, Set.ncard_coe_finset]
  rfl

/-- Permutation fixed point count `numFixedPoints π` equals $n - |\mathrm{supp}(\pi)|$
(`Mathlib/GroupTheory/Perm/Support.lean:252`). -/
theorem numFixedPoints_eq_sub_support_card {n : ℕ} (π : Equiv.Perm (Fin n)) :
    numFixedPoints π = n - π.support.card := by
  have heq : Finset.univ.filter (fun i ↦ π i = i) = Finset.univ \ π.support := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Equiv.Perm.mem_support, Classical.not_not]
  dsimp [numFixedPoints]
  rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]

/-- Permutation 2-cycle count `numTwoCycles π` (`SteinIntro.tex:2684`,
`Formalization/Defs/PoissonExch.lean:50`) equals `Multiset.count 2 π.cycleType`
(`Mathlib/GroupTheory/Perm/Cycle/Type.lean:53`). -/
theorem numTwoCycles_eq_count_cycleType {n : ℕ} (π : Equiv.Perm (Fin n)) :
    numTwoCycles π = Multiset.count 2 π.cycleType := by
  simp only [numTwoCycles, Equiv.Perm.cycleType, Multiset.count_map, Function.comp_apply,
    eq_comm]
  rfl

/-! ### Erdős–Rényi Random Graph Law -/

/-- The Erdős–Rényi random graph law `erdosRenyi n p` (`SteinIntro.tex:919, 1355`,
`Formalization/Defs/RandomGraph.lean:45`) equals Mathlib's `SimpleGraph.binomialRandom`
(`Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean:46`) clamped to $[0, 1]$. -/
theorem erdosRenyi_eq_binomialRandom (n : ℕ) (p : ℝ) :
    erdosRenyi n p =
      SimpleGraph.binomialRandom (Fin n) (Set.projIcc 0 1 zero_le_one p) := by
  classical
  set p' := Set.projIcc 0 1 zero_le_one p
  rw [Measure.ext_iff_singleton]
  intro G
  rw [SimpleGraph.binomialRandom_singleton, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hpre : graphOfEdgeBits ⁻¹' ({G} : Set (SimpleGraph (Fin n))) = {edgeBitsOfGraph G} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      subst h
      exact (edgeBitsOfGraph_graphOfEdgeBits ω).symm
    · intro h
      subst h
      exact graphOfEdgeBits_edgeBitsOfGraph G
  dsimp [erdosRenyi]
  rw [Measure.map_apply measurable_graphOfEdgeBits (measurableSet_singleton G), hpre]
  rw [Measure.pi_singleton]
  have h_split : (Finset.univ : Finset (EdgePair n)) =
      (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∈ G.edgeSet) ∪
      (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∉ G.edgeSet) := by
    ext e; simp [em]
  have h_disj : Disjoint
      (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∈ G.edgeSet)
      (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∉ G.edgeSet) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_filter] at he1 he2
    exact he2.2 he1.2
  have h_prod_split : (∏ e : EdgePair n, (bernoulliMeasure true false p') {edgeBitsOfGraph G e}) =
      (∏ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∈ G.edgeSet),
        (bernoulliMeasure true false p') {edgeBitsOfGraph G e}) *
      (∏ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∉ G.edgeSet),
        (bernoulliMeasure true false p') {edgeBitsOfGraph G e}) := by
    rw [Finset.prod_congr h_split (fun _ _ ↦ rfl), Finset.prod_union h_disj]
  rw [h_prod_split]
  have h_true : ∀ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∈ G.edgeSet),
      (bernoulliMeasure true false p') {edgeBitsOfGraph G e} = unitInterval.toNNReal p' := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    dsimp [edgeBitsOfGraph]
    have hdec : decide (e.1 ∈ G.edgeSet) = true := decide_eq_true he
    rw [hdec]
    exact bernoulliMeasure_apply_of_mem_of_notMem p' (measurableSet_singleton true) rfl
      (by decide)
  have h_false : ∀ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∉ G.edgeSet),
      (bernoulliMeasure true false p') {edgeBitsOfGraph G e} =
        unitInterval.toNNReal (unitInterval.symm p') := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    dsimp [edgeBitsOfGraph]
    have hdec : decide (e.1 ∈ G.edgeSet) = false := decide_eq_false he
    rw [hdec]
    exact bernoulliMeasure_apply_of_notMem_of_mem p' (measurableSet_singleton false)
      (by decide) rfl
  rw [Finset.prod_congr rfl h_true, Finset.prod_congr rfl h_false]
  rw [Finset.prod_const, Finset.prod_const]
  have hequiv_edges : (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∈ G.edgeSet).card =
      G.edgeSet.ncard := by
    have heq_card : (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∈ G.edgeSet).card =
        (G.edgeFinset).card := by
      have hinj : Function.Injective (fun e : EdgePair n ↦ e.1) := Subtype.val_injective
      have himg : (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∈ G.edgeSet).image
          (fun e ↦ e.1) = G.edgeFinset := by
        ext e
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          SimpleGraph.mem_edgeFinset]
        constructor
        · rintro ⟨⟨e', he'⟩, he'G, rfl⟩; exact he'G
        · intro heG
          exact ⟨⟨e, G.not_isDiag_of_mem_edgeSet heG⟩, heG, rfl⟩
      rw [← Finset.card_image_of_injective _ hinj, himg]
    rw [heq_card]
    exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm
  have hcard_all : Fintype.card (EdgePair n) = n.choose 2 := by
    have : Fintype.card (EdgePair n) =
        Fintype.card ↥(Sym2.diagSetᶜ : Set (Sym2 (Fin n))) := rfl
    rw [this, Sym2.card_diagSet_compl, Fintype.card_fin]
  have hequiv_nonedges : (Finset.univ.filter fun e : EdgePair n ↦ e.1 ∉ G.edgeSet).card =
      n.choose 2 - G.edgeSet.ncard := by
    have h_sum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (EdgePair n))) (fun e ↦ e.1 ∈ G.edgeSet)
    rw [Finset.card_univ, hcard_all, hequiv_edges] at h_sum
    omega
  rw [hequiv_edges, hequiv_nonedges]

end SteinMethod
