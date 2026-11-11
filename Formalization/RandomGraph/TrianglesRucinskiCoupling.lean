/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.RandomGraph.ErdosRenyi
import Formalization.SizeBias.Coupling
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Size-Bias Coupling for Triangle Counts (`TrianglesRucinskiCoupling`)

Establishes the size-bias coupling for triangle counts $T(G) = |(G.\text{cliqueSet } 3)|$ in
$G(n, p)$, supporting the from-scratch proof of Ruciński's (1988) triangle CLT criterion
(`SteinIntro.tex:943-944`, `\cite{ruc88}`):

* `erdosRenyi_cond_isNClique_three_eq_map_sup_tripleGraph`: conditioning $G \sim G(n, p)$
  ($0 < p \le 1$) on triple `i` forming a triangle has the same law as adding the three edges of
  triple `i` (`G ⊔ tripleGraph (rucTripleOf i)`).
* `triangles_sizeBias_coupling`: choosing an independent uniform vertex triple $I$ and adding its
  three edges yields a size-biased version $T^s$ of $T$ via Corollary 3.16
  (`sizeBias_sum_of_zero_one`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### 1. Vertex Triples, Potential Edges, and Neighborhoods -/

/-- Unordered vertex triples in `Fin n` (`SteinIntro.tex:920-921, 943-944`). -/
def rucTriples (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard 3

lemma card_rucTriples (n : ℕ) : (rucTriples n).card = n.choose 3 := by
  simp [rucTriples]

/-- Enumeration of `rucTriples n` by `Fin (n.choose 3)` (`SteinIntro.tex:920-921`). -/
noncomputable def rucTripleEquiv (n : ℕ) :
    Fin (n.choose 3) ≃ {t : Finset (Fin n) // t ∈ rucTriples n} :=
  (Fintype.equivFinOfCardEq
    ((Fintype.card_of_subtype (rucTriples n) fun _ ↦ Iff.rfl).trans (card_rucTriples n))).symm

/-- The `i`-th unordered vertex triple in `Fin n` (`SteinIntro.tex:920-921`). -/
noncomputable def rucTripleOf {n : ℕ} (i : Fin (n.choose 3)) : Finset (Fin n) :=
  (rucTripleEquiv n i).1

lemma rucTripleOf_mem {n : ℕ} (i : Fin (n.choose 3)) : rucTripleOf i ∈ rucTriples n :=
  (rucTripleEquiv n i).2

lemma card_rucTripleOf {n : ℕ} (i : Fin (n.choose 3)) : (rucTripleOf i).card = 3 :=
  (Finset.mem_powersetCard.mp (rucTripleOf_mem i)).2

lemma rucTripleOf_injective {n : ℕ} : Function.Injective (rucTripleOf (n := n)) :=
  fun _ _ h ↦ (rucTripleEquiv n).injective (Subtype.ext h)

private def mkRucEdge {n : ℕ} {u v : Fin n} (hne : u ≠ v) : EdgePair n :=
  ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using hne⟩

/-- Potential undirected edges with both endpoints in `t : Finset (Fin n)`
(`SteinIntro.tex:921-923`). -/
def rucEdgesOfFinset {n : ℕ} (t : Finset (Fin n)) : Finset (EdgePair n) :=
  Finset.univ.filter fun e : EdgePair n ↦ ∀ v ∈ e.1, v ∈ t

@[simp]
lemma mem_rucEdgesOfFinset {n : ℕ} {e : EdgePair n} {t : Finset (Fin n)} :
    e ∈ rucEdgesOfFinset t ↔ ∀ v ∈ e.1, v ∈ t := by
  simp [rucEdgesOfFinset]

lemma rucEdgesOfFinset_inter {n : ℕ} (s t : Finset (Fin n)) :
    rucEdgesOfFinset (s ∩ t) = rucEdgesOfFinset s ∩ rucEdgesOfFinset t := by
  ext e
  simp only [Finset.mem_inter, mem_rucEdgesOfFinset]
  exact ⟨fun h ↦ ⟨fun v hv ↦ (h v hv).1, fun v hv ↦ (h v hv).2⟩,
    fun ⟨hs, ht⟩ v hv ↦ ⟨hs v hv, ht v hv⟩⟩

lemma rucEdgesOfFinset_eq_empty_of_card_le_one {n : ℕ} {u : Finset (Fin n)}
    (hu : u.card ≤ 1) : rucEdgesOfFinset u = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨z, hne⟩ he
  rw [mem_rucEdgesOfFinset] at he
  revert hne he
  refine Sym2.ind (fun x y hne he ↦ ?_) z
  have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hne
  exact hxy (Finset.card_le_one.mp hu x (he x (Sym2.mem_mk_left x y))
    y (he y (Sym2.mem_mk_right x y)))

lemma card_rucEdgesOfFinset_of_card_eq_two {n : ℕ} {u : Finset (Fin n)}
    (hu : u.card = 2) : (rucEdgesOfFinset u).card = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hu
  suffices h : rucEdgesOfFinset {a, b} = {mkRucEdge hab} by
    rw [h, Finset.card_singleton]
  ext ⟨z, hne⟩
  rw [Finset.mem_singleton, mem_rucEdgesOfFinset]
  revert hne
  refine Sym2.ind (fun x y hne ↦ ?_) z
  have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hne
  constructor
  · intro he
    have hx : x = a ∨ x = b := by simpa using he x (Sym2.mem_mk_left x y)
    have hy : y = a ∨ y = b := by simpa using he y (Sym2.mem_mk_right x y)
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · rfl
    · exact Subtype.ext Sym2.eq_swap
    · exact (hxy rfl).elim
  · intro h v hv
    change v ∈ s(x, y) at hv
    have hz : s(x, y) = s(a, b) := congrArg Subtype.val h
    rw [hz] at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp

lemma card_rucEdgesOfFinset_of_card_eq_three {n : ℕ} {t : Finset (Fin n)}
    (ht : t.card = 3) : (rucEdgesOfFinset t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht
  have heq : rucEdgesOfFinset {a, b, c} = {mkRucEdge hab, mkRucEdge hac, mkRucEdge hbc} := by
    ext ⟨z, hne⟩
    rw [mem_rucEdgesOfFinset]
    revert hne
    refine Sym2.ind (fun x y hne ↦ ?_) z
    have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hne
    constructor
    · intro he
      have hx : x = a ∨ x = b ∨ x = c := by simpa using he x (Sym2.mem_mk_left x y)
      have hy : y = a ∨ y = b ∨ y = c := by simpa using he y (Sym2.mem_mk_right x y)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact (hxy rfl).elim
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Subtype.ext Sym2.eq_swap)
      · exact (hxy rfl).elim
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl (Subtype.ext Sym2.eq_swap))
      · exact Or.inr (Or.inr (Subtype.ext Sym2.eq_swap))
      · exact (hxy rfl).elim
    · intro h v hv
      change v ∈ s(x, y) at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · have hz : s(x, y) = s(a, b) := congrArg Subtype.val h
        rw [hz] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
      · have hz : s(x, y) = s(a, c) := congrArg Subtype.val h
        rw [hz] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
      · have hz : s(x, y) = s(b, c) := congrArg Subtype.val h
        rw [hz] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> simp
  have h12 : mkRucEdge hab ≠ mkRucEdge hac := fun h ↦
    hbc (Sym2.congr_right.mp (congrArg Subtype.val h))
  have h13 : mkRucEdge hab ≠ mkRucEdge hbc := fun h ↦
    hac (Sym2.congr_right.mp (Sym2.eq_swap.trans (congrArg Subtype.val h)))
  have h23 : mkRucEdge hac ≠ mkRucEdge hbc := fun h ↦
    hab (Sym2.congr_left.mp (congrArg Subtype.val h))
  rw [heq]
  exact Finset.card_triple_eq_three_iff.mpr ⟨h12, h13, h23⟩

lemma card_rucEdgesOfFinset_union_of_inter_two {n : ℕ} {s t : Finset (Fin n)}
    (hs : s.card = 3) (ht : t.card = 3) (hst : (s ∩ t).card = 2) :
    (rucEdgesOfFinset s ∪ rucEdgesOfFinset t).card = 5 := by
  have hinter : (rucEdgesOfFinset s ∩ rucEdgesOfFinset t).card = 1 := by
    rw [← rucEdgesOfFinset_inter]
    exact card_rucEdgesOfFinset_of_card_eq_two hst
  have hiu := Finset.card_union_add_card_inter (rucEdgesOfFinset s) (rucEdgesOfFinset t)
  rw [card_rucEdgesOfFinset_of_card_eq_three hs, card_rucEdgesOfFinset_of_card_eq_three ht,
    hinter] at hiu
  omega

lemma isNClique_three_iff_rucEdges {n : ℕ} {G : SimpleGraph (Fin n)} {t : Finset (Fin n)}
    (ht : t.card = 3) :
    G.IsNClique 3 t ↔ ∀ e ∈ rucEdgesOfFinset t, e.1 ∈ G.edgeSet := by
  rw [SimpleGraph.isNClique_iff]
  constructor
  · rintro ⟨hcl, _⟩ ⟨z, hne⟩ he
    rw [mem_rucEdgesOfFinset] at he
    revert hne he
    refine Sym2.ind (fun u v hne he ↦ ?_) z
    have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hne
    rw [SimpleGraph.mem_edgeSet]
    exact hcl (he u (Sym2.mem_mk_left u v)) (he v (Sym2.mem_mk_right u v)) huv
  · intro hedges
    refine ⟨fun u hu v hv huv ↦ ?_, ht⟩
    have he : mkRucEdge huv ∈ rucEdgesOfFinset t := by
      simp only [mem_rucEdgesOfFinset, mkRucEdge, Sym2.ball]
      exact ⟨hu, hv⟩
    simpa [mkRucEdge, SimpleGraph.mem_edgeSet] using hedges (mkRucEdge huv) he

/-- `{0, 1}`-valued indicator that the `i`-th triple forms a triangle in `G`
(`SteinIntro.tex:920`). -/
noncomputable def rucTriInd {n : ℕ} (i : Fin (n.choose 3)) (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | H.IsNClique 3 (rucTripleOf i)}.indicator 1 G

lemma rucTriInd_of_isNClique {n : ℕ} {i : Fin (n.choose 3)} {G : SimpleGraph (Fin n)}
    (h : G.IsNClique 3 (rucTripleOf i)) : rucTriInd i G = 1 :=
  Set.indicator_of_mem h 1

lemma rucTriInd_of_not_isNClique {n : ℕ} {i : Fin (n.choose 3)} {G : SimpleGraph (Fin n)}
    (h : ¬ G.IsNClique 3 (rucTripleOf i)) : rucTriInd i G = 0 :=
  Set.indicator_of_notMem h 1

lemma ncard_cliqueSet_three_eq_sum_rucTriInd {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((G.cliqueSet 3).ncard : ℝ) = ∑ i : Fin (n.choose 3), rucTriInd i G := by
  classical
  let S : Finset (Finset (Fin n)) := (rucTriples n).filter fun s ↦ G.IsNClique 3 s
  have hS : (S : Set (Finset (Fin n))) = G.cliqueSet 3 := by
    ext s
    simp only [S, Finset.mem_coe, Finset.mem_filter, rucTriples, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, SimpleGraph.mem_cliqueSet_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.card_eq, h⟩⟩
  rw [← hS, Set.ncard_coe_finset]
  have hcard : (S.card : ℝ) = ∑ s ∈ rucTriples n,
      {H : SimpleGraph (Fin n) | H.IsNClique 3 s}.indicator (1 : SimpleGraph (Fin n) → ℝ) G := by
    calc (S.card : ℝ)
        = ∑ _s ∈ S, (1 : ℝ) := by simp
      _ = ∑ s ∈ rucTriples n, if G.IsNClique 3 s then (1 : ℝ) else 0 := by simp [S]
      _ = ∑ s ∈ rucTriples n,
            {H : SimpleGraph (Fin n) | H.IsNClique 3 s}.indicator
              (1 : SimpleGraph (Fin n) → ℝ) G :=
          Finset.sum_congr rfl fun s _ ↦ by
            by_cases hs : G.IsNClique 3 s
            · simp only [hs, ↓reduceIte]; exact (Set.indicator_of_mem hs 1).symm
            · simp only [hs, ↓reduceIte]; exact (Set.indicator_of_notMem hs 1).symm
  rw [hcard, Finset.sum_subtype (rucTriples n) fun _ ↦ Iff.rfl]
  exact ((rucTripleEquiv n).sum_comp fun s : {t // t ∈ rucTriples n} ↦
    {H : SimpleGraph (Fin n) | H.IsNClique 3 s.1}.indicator
      (1 : SimpleGraph (Fin n) → ℝ) G).symm

/-- Dependency neighborhood of triple `i`: triples sharing at least `2` vertices with `i`
(`SteinIntro.tex:921-925`). -/
noncomputable def rucTriNhbd {n : ℕ} (i : Fin (n.choose 3)) : Finset (Fin (n.choose 3)) :=
  Finset.univ.filter fun j ↦ 2 ≤ (rucTripleOf i ∩ rucTripleOf j).card

lemma mem_rucTriNhbd {n : ℕ} {i j : Fin (n.choose 3)} :
    j ∈ rucTriNhbd i ↔ 2 ≤ (rucTripleOf i ∩ rucTripleOf j).card := by
  simp [rucTriNhbd]

lemma self_mem_rucTriNhbd {n : ℕ} (i : Fin (n.choose 3)) : i ∈ rucTriNhbd i := by
  rw [mem_rucTriNhbd, Finset.inter_self, card_rucTripleOf]
  decide

lemma rucTriNhbd_symm {n : ℕ} {i j : Fin (n.choose 3)} (h : j ∈ rucTriNhbd i) :
    i ∈ rucTriNhbd j := by
  rw [mem_rucTriNhbd] at h ⊢
  rwa [Finset.inter_comm]

lemma mem_erase_rucTriNhbd_iff {n : ℕ} {i j : Fin (n.choose 3)} :
    j ∈ (rucTriNhbd i).erase i ↔ (rucTripleOf i ∩ rucTripleOf j).card = 2 := by
  rw [Finset.mem_erase, mem_rucTriNhbd]
  constructor
  · rintro ⟨hne, hle⟩
    have hub : (rucTripleOf i ∩ rucTripleOf j).card ≤ 3 :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq (card_rucTripleOf i)
    by_contra hnot2
    have h3 : (rucTripleOf i ∩ rucTripleOf j).card = 3 := by omega
    have hi_eq : rucTripleOf i ∩ rucTripleOf j = rucTripleOf i :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [card_rucTripleOf, h3])
    have hj_eq : rucTripleOf i ∩ rucTripleOf j = rucTripleOf j :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [card_rucTripleOf, h3])
    exact hne (rucTripleOf_injective (hj_eq.symm.trans hi_eq))
  · intro h2
    refine ⟨?_, by omega⟩
    rintro rfl
    rw [Finset.inter_self, card_rucTripleOf] at h2
    omega

private lemma card_filter_rucTriples_inter_eq_two {n : ℕ} {t : Finset (Fin n)} (ht : t.card = 3) :
    ((rucTriples n).filter fun s ↦ (t ∩ s).card = 2).card = 3 * (n - 3) := by
  let P : Finset (Finset (Fin n) × Finset (Fin n)) :=
    t.powersetCard 2 ×ˢ ((Finset.univ \ t).powersetCard 1)
  have hbij : ((rucTriples n).filter fun s ↦ (t ∩ s).card = 2).card = P.card := by
    refine Finset.card_nbij' (fun s ↦ (t ∩ s, s \ t)) (fun p ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, rucTriples, Finset.mem_powersetCard,
        Finset.subset_univ, true_and] at hs
      simp only [P, Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hs.2⟩, ⟨?_, ?_⟩⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ x, hx.2⟩
      · have hsum := Finset.card_sdiff_add_card_inter s t
        rw [Finset.inter_comm, hs.2, hs.1] at hsum
        omega
    · rintro ⟨u, v⟩ hp
      simp only [P, Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hp
      rcases hp with ⟨⟨hu_sub, hu_card⟩, ⟨hv_sub, hv_card⟩⟩
      have hdisj_tv : Disjoint t v := by
        rw [Finset.disjoint_left]
        intro x hxt hxv
        exact (Finset.mem_sdiff.mp (hv_sub hxv)).2 hxt
      have hdisj_uv : Disjoint u v := hdisj_tv.mono_left hu_sub
      have htu : t ∩ (u ∪ v) = u := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        refine ⟨fun ⟨hxt, hxuv⟩ ↦ ?_, fun hxu ↦ ⟨hu_sub hxu, Or.inl hxu⟩⟩
        rcases hxuv with hxu | hxv
        · exact hxu
        · exact ((Finset.mem_sdiff.mp (hv_sub hxv)).2 hxt).elim
      simp only [Finset.mem_coe, Finset.mem_filter, rucTriples, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      exact ⟨by rw [Finset.card_union_of_disjoint hdisj_uv, hu_card, hv_card],
        by rw [htu, hu_card]⟩
    · intro s _
      ext x
      by_cases hxt : x ∈ t <;> simp [hxt]
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
  simp only [P, Finset.card_product, Finset.card_powersetCard, ht, h32, Nat.choose_one_right,
    Finset.card_sdiff_of_subset (Finset.subset_univ t), Finset.card_univ, Fintype.card_fin]

lemma card_erase_rucTriNhbd {n : ℕ} (i : Fin (n.choose 3)) :
    ((rucTriNhbd i).erase i).card = 3 * (n - 3) := by
  rw [← card_filter_rucTriples_inter_eq_two (card_rucTripleOf i)]
  refine Finset.card_bij (fun j _ ↦ rucTripleOf j) ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_filter.mpr ⟨rucTripleOf_mem j, mem_erase_rucTriNhbd_iff.mp hj⟩
  · intro _ _ _ _ h
    exact rucTripleOf_injective h
  · intro s hs
    rcases Finset.mem_filter.mp hs with ⟨hs_mem, hs_inter⟩
    let j : Fin (n.choose 3) := (rucTripleEquiv n).symm ⟨s, hs_mem⟩
    have hj_eq : rucTripleOf j = s :=
      congrArg Subtype.val ((rucTripleEquiv n).apply_symm_apply ⟨s, hs_mem⟩)
    refine ⟨j, mem_erase_rucTriNhbd_iff.mpr ?_, hj_eq⟩
    rwa [hj_eq]

/-! ### 2. Adding the Three Edges of a Triple and Size-Bias Realization -/

/-- Simple graph on `Fin n` consisting of all edges with both endpoints in `t`
(`SteinIntro.tex:943-944`). -/
def tripleGraph {n : ℕ} (t : Finset (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | ∀ v ∈ e, v ∈ t}

@[simp]
lemma mem_edgeSet_sup_tripleGraph {n : ℕ} (G : SimpleGraph (Fin n)) (t : Finset (Fin n))
    (e : EdgePair n) :
    e.1 ∈ (G ⊔ tripleGraph t).edgeSet ↔ e.1 ∈ G.edgeSet ∨ e ∈ rucEdgesOfFinset t := by
  rw [SimpleGraph.edgeSet_sup, Set.mem_union, tripleGraph, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Sym2.mem_diagSet, mem_rucEdgesOfFinset]
  exact ⟨fun h ↦ h.elim Or.inl fun h2 ↦ Or.inr h2.1,
    fun h ↦ h.elim Or.inl fun h2 ↦ Or.inr ⟨h2, e.2⟩⟩

lemma isNClique_three_sup_tripleGraph_self {n : ℕ} (G : SimpleGraph (Fin n))
    (i : Fin (n.choose 3)) :
    (G ⊔ tripleGraph (rucTripleOf i)).IsNClique 3 (rucTripleOf i) := by
  rw [isNClique_three_iff_rucEdges (card_rucTripleOf i)]
  intro e he
  exact (mem_edgeSet_sup_tripleGraph G (rucTripleOf i) e).mpr (Or.inr he)

private lemma cond_preimage_map_ruc {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) {G : Ω → α} (hG : Measurable G) {S : Set α} (hS : MeasurableSet S) :
    (ProbabilityTheory.cond P (G ⁻¹' S)).map G = ProbabilityTheory.cond (P.map G) S := by
  refine Measure.ext fun T hT ↦ ?_
  rw [Measure.map_apply hG hT, ProbabilityTheory.cond_apply (hG hS) P (G ⁻¹' T),
    ProbabilityTheory.cond_apply hS (P.map G) T, Measure.map_apply hG hS,
    Measure.map_apply hG (hS.inter hT), Set.preimage_inter]

private lemma cond_measureReal_apply_ruc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    (ProbabilityTheory.cond μ s).real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp only [measureReal_def, ProbabilityTheory.cond_apply hs μ t, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

/-- Probability that triple `i` forms a triangle in $G(n, p)$ (`SteinIntro.tex:925-928`). -/
lemma erdosRenyi_real_isNClique_ruc {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.IsNClique 3 (rucTripleOf i)} = p ^ 3 := by
  have hset : {G : SimpleGraph (Fin n) | G.IsNClique 3 (rucTripleOf i)} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ rucEdgesOfFinset (rucTripleOf i), e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
    ext G
    simp [isNClique_three_iff_rucEdges (card_rucTripleOf i)]
  rw [hset, erdosRenyi_real_cylinder hp0 hp1 _ _ (Finset.disjoint_empty_right _),
    card_rucEdgesOfFinset_of_card_eq_three (card_rucTripleOf i)]
  simp

/-- Conditioning $G \sim G(n, p)$ ($0 < p \le 1$) on triple `i` forming a triangle has the same law
as adding the three edges of `rucTripleOf i` (`SteinIntro.tex:943-944, 1326-1332`). -/
theorem erdosRenyi_cond_isNClique_three_eq_map_sup_tripleGraph {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (i : Fin (n.choose 3)) :
    ProbabilityTheory.cond (erdosRenyi n p)
        {G : SimpleGraph (Fin n) | G.IsNClique 3 (rucTripleOf i)} =
      (erdosRenyi n p).map (fun G ↦ G ⊔ tripleGraph (rucTripleOf i)) := by
  classical
  let t := rucTripleOf i
  let E_t := rucEdgesOfFinset t
  set S_cliq : Set (SimpleGraph (Fin n)) := {G | G.IsNClique 3 t}
  set addT : SimpleGraph (Fin n) → SimpleGraph (Fin n) := fun G ↦ G ⊔ tripleGraph t
  have hadd_meas : Measurable addT := measurable_of_finite addT
  have hS_meas : MeasurableSet S_cliq := MeasurableSet.of_discrete
  refine Measure.ext_of_singleton fun H ↦ ?_
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top (ProbabilityTheory.cond (erdosRenyi n p) S_cliq) {H})
    (measure_ne_top ((erdosRenyi n p).map addT) {H})).mp ?_
  rw [cond_measureReal_apply_ruc (erdosRenyi n p) hS_meas {H},
    map_measureReal_apply hadd_meas (measurableSet_singleton H)]
  by_cases hH : H.IsNClique 3 t
  · have hH_edges : ∀ e ∈ E_t, e.1 ∈ H.edgeSet :=
      (isNClique_three_iff_rucEdges (card_rucTripleOf i)).mp hH
    let S_pos : Finset (EdgePair n) :=
      Finset.univ.filter fun e : EdgePair n ↦ e ∉ E_t ∧ e.1 ∈ H.edgeSet
    let S_neg : Finset (EdgePair n) :=
      Finset.univ.filter fun e : EdgePair n ↦ e ∉ E_t ∧ e.1 ∉ H.edgeSet
    have hdisj_pn : Disjoint S_pos S_neg :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ h2.2 h1.2
    have hdisj_tp : Disjoint E_t S_pos :=
      Finset.disjoint_left.mpr fun _ ht' h1 ↦ (Finset.mem_filter.mp h1).2.1 ht'
    have hdisj_tn : Disjoint E_t S_neg :=
      Finset.disjoint_left.mpr fun _ ht' h2 ↦ (Finset.mem_filter.mp h2).2.1 ht'
    have hdisj_un : Disjoint (E_t ∪ S_pos) S_neg :=
      Finset.disjoint_union_left.mpr ⟨hdisj_tn, hdisj_pn⟩
    have hinter_eq : S_cliq ∩ {H} =
        {G : SimpleGraph (Fin n) |
          (∀ e ∈ E_t ∪ S_pos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ S_neg, e.1 ∉ G.edgeSet)} := by
      ext G
      simp only [S_cliq, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, Finset.mem_union,
        S_pos, S_neg, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, rfl⟩
        exact ⟨fun e he ↦ he.elim (hH_edges e) And.right, fun _ he ↦ he.2⟩
      · rintro ⟨hpos, hneg⟩
        have hGH : G = H := by
          rw [← SimpleGraph.edgeSet_inj]
          ext z
          by_cases hz : z.IsDiag
          · exact iff_of_false (G.not_mem_edgeSet_of_isDiag hz) (H.not_mem_edgeSet_of_isDiag hz)
          · let e : EdgePair n := ⟨z, hz⟩
            change e.1 ∈ G.edgeSet ↔ e.1 ∈ H.edgeSet
            by_cases het : e ∈ E_t
            · exact iff_of_true (hpos e (Or.inl het)) (hH_edges e het)
            · by_cases hmem : e.1 ∈ H.edgeSet
              · exact iff_of_true (hpos e (Or.inr ⟨het, hmem⟩)) hmem
              · exact iff_of_false (hneg e ⟨het, hmem⟩) hmem
        exact ⟨hGH ▸ hH, hGH⟩
    have hpre_eq : addT ⁻¹' {H} =
        {G : SimpleGraph (Fin n) |
          (∀ e ∈ S_pos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ S_neg, e.1 ∉ G.edgeSet)} := by
      ext G
      simp only [addT, mem_preimage, mem_singleton_iff, mem_ofPred_eq, S_pos, S_neg,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hGH
        rw [← hGH] at *
        refine ⟨fun e ⟨het, hmem⟩ ↦ ?_, fun e ⟨het, hnmem⟩ hmemG ↦ hnmem ?_⟩
        · exact ((mem_edgeSet_sup_tripleGraph G t e).mp hmem).resolve_right het
        · exact (mem_edgeSet_sup_tripleGraph G t e).mpr (Or.inl hmemG)
      · rintro ⟨hpos, hneg⟩
        rw [← SimpleGraph.edgeSet_inj]
        ext z
        by_cases hz : z.IsDiag
        · exact iff_of_false ((G ⊔ tripleGraph t).not_mem_edgeSet_of_isDiag hz)
            (H.not_mem_edgeSet_of_isDiag hz)
        · let e : EdgePair n := ⟨z, hz⟩
          change e.1 ∈ (G ⊔ tripleGraph t).edgeSet ↔ e.1 ∈ H.edgeSet
          rw [mem_edgeSet_sup_tripleGraph]
          by_cases het : e ∈ E_t
          · exact iff_of_true (Or.inr het) (hH_edges e het)
          · by_cases hmem : e.1 ∈ H.edgeSet
            · exact iff_of_true (Or.inl (hpos e ⟨het, hmem⟩)) hmem
            · exact iff_of_false (fun h ↦ h.elim (hneg e ⟨het, hmem⟩) het) hmem
    have hprob_cliq : (erdosRenyi n p).real S_cliq = p ^ 3 :=
      erdosRenyi_real_isNClique_ruc hp0.le hp1 i
    have hp3_ne : p ^ 3 ≠ 0 := pow_ne_zero 3 hp0.ne'
    have hcard_Et : E_t.card = 3 := card_rucEdgesOfFinset_of_card_eq_three (card_rucTripleOf i)
    rw [hprob_cliq, hinter_eq, hpre_eq,
      erdosRenyi_real_cylinder hp0.le hp1 (E_t ∪ S_pos) S_neg hdisj_un,
      erdosRenyi_real_cylinder hp0.le hp1 S_pos S_neg hdisj_pn,
      Finset.card_union_of_disjoint hdisj_tp, hcard_Et, pow_add]
    field_simp [hp3_ne]
  · have hinter : S_cliq ∩ {H} = ∅ := by
      ext G
      simp only [S_cliq, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      rintro hcl rfl
      exact hH hcl
    have hpre : addT ⁻¹' {H} = ∅ := by
      ext G
      simp only [addT, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hEq
      exact hH (hEq ▸ isNClique_three_sup_tripleGraph_self G i)
    simp [hinter, hpre]

/-- Size-bias realization for triangle counts (`SteinIntro.tex:943-944, 1326-1332`): for
$G \sim G(n, p)$ ($n \ge 3$, $0 < p \le 1$) and an independent uniform vertex triple $I$, adding
the three edges of $I$ yields a size-biased version of $T(G) = |(G.\text{cliqueSet } 3)|$. -/
theorem triangles_sizeBias_coupling {n : ℕ} {p : ℝ} (hn : 3 ≤ n) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    let hpos : 0 < n.choose 3 := Nat.choose_pos hn
    let unif : Measure (Fin (n.choose 3)) :=
      (@PMF.uniformOfFintype (Fin (n.choose 3)) inferInstance ⟨⟨0, hpos⟩⟩).toMeasure
    let P : Measure (SimpleGraph (Fin n) × Fin (n.choose 3)) := (erdosRenyi n p).prod unif
    IsSizeBias P (fun ω ↦ ((ω.1.cliqueSet 3).ncard : ℝ)) P
      (fun ω ↦ (((ω.1 ⊔ tripleGraph (rucTripleOf ω.2)).cliqueSet 3).ncard : ℝ)) := by
  intro hpos unif P
  let μG := erdosRenyi n p
  have hmap_fst : P.map Prod.fst = μG := (measurePreserving_fst (μ := μG) (ν := unif)).map_eq
  have hmap_snd : P.map Prod.snd = unif := (measurePreserving_snd (μ := μG) (ν := unif)).map_eq
  have hindep : IndepFun (Prod.snd : SimpleGraph (Fin n) × Fin (n.choose 3) → Fin (n.choose 3))
      Prod.fst P :=
    (indepFun_prod (μ := μG) (ν := unif) measurable_id measurable_id).symm
  let Xi : Fin (n.choose 3) → SimpleGraph (Fin n) × Fin (n.choose 3) → ℝ :=
    fun i ω ↦ rucTriInd i ω.1
  let Y : (i : Fin (n.choose 3)) → SimpleGraph (Fin n) × Fin (n.choose 3) →
      ({j : Fin (n.choose 3) // j ≠ i} → ℝ) :=
    fun i ω j ↦ rucTriInd j.1 (ω.1 ⊔ tripleGraph (rucTripleOf i))
  have hXi_meas : ∀ i, Measurable (Xi i) :=
    fun i ↦ (measurable_of_finite (rucTriInd i)).comp measurable_fst
  have hXi_zo : ∀ i, ∀ᵐ ω ∂P, Xi i ω = 0 ∨ Xi i ω = 1 := fun i ↦
    Eventually.of_forall fun ω ↦ by
      by_cases h : ω.1.IsNClique 3 (rucTripleOf i)
      · exact Or.inr (rucTriInd_of_isNClique h)
      · exact Or.inl (rucTriInd_of_not_isNClique h)
  have hXi_pre : ∀ i,
      Xi i ⁻¹' {(1 : ℝ)} = Prod.fst ⁻¹' {H : SimpleGraph (Fin n) | H.IsNClique 3 (rucTripleOf i)} :=
    fun i ↦ by
      ext ω
      by_cases h : ω.1.IsNClique 3 (rucTripleOf i)
      · simp [Xi, rucTriInd_of_isNClique h, h]
      · simp [Xi, rucTriInd_of_not_isNClique h, h]
  have hpi_eq : ∀ i, P.real (Xi i ⁻¹' {(1 : ℝ)}) = p ^ 3 := fun i ↦ by
    rw [hXi_pre i, ← map_measureReal_apply measurable_fst MeasurableSet.of_discrete,
      hmap_fst, erdosRenyi_real_isNClique_ruc hp0.le hp1 i]
  have hN_pos : (0 : ℝ) < (n.choose 3 : ℝ) := Nat.cast_pos.mpr hpos
  have hp3_pos : (0 : ℝ) < p ^ 3 := pow_pos hp0 3
  have hμ_eq : (∑ i : Fin (n.choose 3), P.real (Xi i ⁻¹' {(1 : ℝ)})) =
      (n.choose 3 : ℝ) * p ^ 3 := by simp [hpi_eq]
  have hμ_pos : 0 < ∑ i : Fin (n.choose 3), P.real (Xi i ⁻¹' {(1 : ℝ)}) := by
    rw [hμ_eq]; positivity
  let Yi_graph : (i : Fin (n.choose 3)) → SimpleGraph (Fin n) →
      ({j : Fin (n.choose 3) // j ≠ i} → ℝ) :=
    fun i H j ↦ rucTriInd j.1 (H ⊔ tripleGraph (rucTripleOf i))
  let rest_graph : (i : Fin (n.choose 3)) → SimpleGraph (Fin n) →
      ({j : Fin (n.choose 3) // j ≠ i} → ℝ) :=
    fun i H j ↦ rucTriInd j.1 H
  have hY_meas : ∀ i, Measurable (Y i) :=
    fun i ↦ (measurable_of_finite (Yi_graph i)).comp measurable_fst
  have hY_law : ∀ i, 0 < P.real (Xi i ⁻¹' {(1 : ℝ)}) →
      P.map (Y i) =
        (ProbabilityTheory.cond P (Xi i ⁻¹' {(1 : ℝ)})).map
          (fun ω (j : {j : Fin (n.choose 3) // j ≠ i}) ↦ Xi j.1 ω) := by
    intro i _
    have hrest_meas : Measurable (rest_graph i) := .of_discrete
    have hadd_meas : Measurable (fun H : SimpleGraph (Fin n) ↦ H ⊔ tripleGraph (rucTripleOf i)) :=
      .of_discrete
    calc
      P.map (Y i)
        = (P.map Prod.fst).map (Yi_graph i) :=
          (Measure.map_map (measurable_of_finite (Yi_graph i)) measurable_fst).symm
      _ = (μG.map (fun H ↦ H ⊔ tripleGraph (rucTripleOf i))).map (rest_graph i) := by
          rw [hmap_fst, Measure.map_map hrest_meas hadd_meas]; rfl
      _ = (ProbabilityTheory.cond μG
            {H : SimpleGraph (Fin n) | H.IsNClique 3 (rucTripleOf i)}).map (rest_graph i) := by
          rw [← erdosRenyi_cond_isNClique_three_eq_map_sup_tripleGraph hp0 hp1 i]
      _ = ((ProbabilityTheory.cond P
            (Prod.fst ⁻¹' {H : SimpleGraph (Fin n) |
              H.IsNClique 3 (rucTripleOf i)})).map Prod.fst).map (rest_graph i) := by
          rw [cond_preimage_map_ruc P measurable_fst MeasurableSet.of_discrete, hmap_fst]
      _ = (ProbabilityTheory.cond P (Xi i ⁻¹' {(1 : ℝ)})).map
            (fun ω (j : {j : Fin (n.choose 3) // j ≠ i}) ↦ Xi j.1 ω) := by
          rw [hXi_pre i, Measure.map_map hrest_meas measurable_fst]; rfl
  have hI_prob : ∀ i,
      P.real (Prod.snd ⁻¹' {i}) =
        P.real (Xi i ⁻¹' {(1 : ℝ)}) / ∑ k, P.real (Xi k ⁻¹' {(1 : ℝ)}) := by
    intro i
    let upmf : PMF (Fin (n.choose 3)) :=
      @PMF.uniformOfFintype (Fin (n.choose 3)) inferInstance ⟨⟨0, hpos⟩⟩
    have hmapI : P.real (Prod.snd ⁻¹' {i}) = (upmf.toMeasure).real {i} := by
      rw [← map_measureReal_apply measurable_snd (measurableSet_singleton i), hmap_snd]
    have hunif : (upmf.toMeasure).real {i} = (n.choose 3 : ℝ)⁻¹ := by
      rw [measureReal_def, upmf.toMeasure_apply_singleton i (measurableSet_singleton i)]
      simp [upmf, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    rw [hmapI, hunif, hpi_eq i, hμ_eq]
    field_simp [hN_pos.ne', hp3_pos.ne']
  let Φ : SimpleGraph (Fin n) →
      (Fin (n.choose 3) → ℝ) × ((i : Fin (n.choose 3)) → ({j // j ≠ i} → ℝ)) :=
    fun H ↦ (fun i ↦ rucTriInd i H, fun i j ↦ rucTriInd j.1 (H ⊔ tripleGraph (rucTripleOf i)))
  have hΦ_meas : Measurable Φ :=
    (Measurable.of_eval fun _ ↦ measurable_of_finite _).prodMk
      (Measurable.of_eval fun _ ↦ Measurable.of_eval fun _ ↦ measurable_of_finite _)
  have hIndep : IndepFun Prod.snd (fun ω ↦ (fun i ↦ Xi i ω, fun i ↦ Y i ω)) P :=
    hindep.comp measurable_id hΦ_meas
  have hSB := sizeBias_sum_of_zero_one P hXi_meas hXi_zo hμ_pos
    (fun i ↦ (hY_meas i).aemeasurable) hY_law measurable_snd hI_prob hIndep
  have hX_eq : (fun ω : SimpleGraph (Fin n) × Fin (n.choose 3) ↦ ∑ i, Xi i ω) =
      fun ω ↦ ((ω.1.cliqueSet 3).ncard : ℝ) :=
    funext fun ω ↦ (ncard_cliqueSet_three_eq_sum_rucTriInd ω.1).symm
  have hXs_eq : (fun ω : SimpleGraph (Fin n) × Fin (n.choose 3) ↦
        (∑ j : {j // j ≠ ω.2}, Y ω.2 ω j) + 1) =
      fun ω ↦ (((ω.1 ⊔ tripleGraph (rucTripleOf ω.2)).cliqueSet 3).ncard : ℝ) := by
    funext ω
    rw [ncard_cliqueSet_three_eq_sum_rucTriInd]
    have hsub : (∑ j : {j // j ≠ ω.2}, Y ω.2 ω j) =
        ∑ j ∈ Finset.univ.erase ω.2, rucTriInd j (ω.1 ⊔ tripleGraph (rucTripleOf ω.2)) :=
      (Finset.sum_subtype (Finset.univ.erase ω.2) (by simp)
        (fun j ↦ rucTriInd j (ω.1 ⊔ tripleGraph (rucTripleOf ω.2)))).symm
    have hi_one : rucTriInd ω.2 (ω.1 ⊔ tripleGraph (rucTripleOf ω.2)) = 1 :=
      rucTriInd_of_isNClique (isNClique_three_sup_tripleGraph_self ω.1 ω.2)
    rw [hsub, ← hi_one, Finset.sum_erase_add Finset.univ _ (Finset.mem_univ ω.2)]
  rwa [hX_eq, hXs_eq] at hSB

end SteinMethod
