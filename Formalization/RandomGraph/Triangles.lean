/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Normal.DependencyNeighborhoods
import Formalization.Normal.WassersteinBound
import Formalization.RandomGraph.ErdosRenyi
import Formalization.Statements.Sec3
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset

/-!
# Normal Approximation for Triangle Counts in $G(n, p)$ (`SteinIntro.tex:918-949`)

Proves the Section 3.2.1 application (`Sec3_2_1_triangles_restricted_proof`; `ISSUE-TYPO-3.2.1`,
`ISSUE-3.2.1`): exact expectation, exact variance, and the Theorem 3.5 Wasserstein normal
approximation bound for the number of triangles $T = |(G.\text{cliqueSet } 3)|$ in the Erdős–Rényi
random graph $G(n, p)$ for $n \ge 3$ and $0 < p < 1$.
-/

open MeasureTheory

namespace SteinMethod

/-! ### 1. Vertex triples and undirected edge sets -/

/-- The $\binom{n}{3}$ unordered vertex triples in `Fin n` (`SteinIntro.tex:920-921`). -/
private def triples (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard 3

private lemma card_triples (n : ℕ) : (triples n).card = n.choose 3 := by
  simp [triples]

/-- Enumeration of the $\binom{n}{3}$ vertex triples by `Fin (n.choose 3)`. -/
private noncomputable def tripleEquiv (n : ℕ) :
    Fin (n.choose 3) ≃ {t : Finset (Fin n) // t ∈ triples n} :=
  (Fintype.equivFinOfCardEq
    ((Fintype.card_of_subtype (triples n) fun _ ↦ Iff.rfl).trans (card_triples n))).symm

/-- The `i`-th vertex triple in `Fin n` (`i : Fin (n.choose 3)`). -/
private noncomputable def tripleOf {n : ℕ} (i : Fin (n.choose 3)) : Finset (Fin n) :=
  (tripleEquiv n i).1

private lemma tripleOf_mem {n : ℕ} (i : Fin (n.choose 3)) : tripleOf i ∈ triples n :=
  (tripleEquiv n i).2

private lemma card_tripleOf {n : ℕ} (i : Fin (n.choose 3)) : (tripleOf i).card = 3 :=
  (Finset.mem_powersetCard.mp (tripleOf_mem i)).2

private lemma tripleOf_injective {n : ℕ} : Function.Injective (tripleOf (n := n)) := by
  intro i j hij
  exact (tripleEquiv n).injective (Subtype.ext hij)

/-- Construct an `EdgePair n` from two distinct vertices `u ≠ v` in `Fin n`. -/
private def mkEdgePair {n : ℕ} {u v : Fin n} (hne : u ≠ v) : EdgePair n :=
  ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using hne⟩

/-- Potential edges of `SimpleGraph (Fin n)` with both endpoints in `t : Finset (Fin n)`. -/
private def edgesOfFinset {n : ℕ} (t : Finset (Fin n)) : Finset (EdgePair n) :=
  Finset.univ.filter fun e : EdgePair n ↦ ∀ v ∈ e.1, v ∈ t

private lemma mem_edgesOfFinset {n : ℕ} {e : EdgePair n} {t : Finset (Fin n)} :
    e ∈ edgesOfFinset t ↔ ∀ v ∈ e.1, v ∈ t := by
  simp [edgesOfFinset]

private lemma edgesOfFinset_inter {n : ℕ} (s t : Finset (Fin n)) :
    edgesOfFinset (s ∩ t) = edgesOfFinset s ∩ edgesOfFinset t := by
  ext e
  simp only [Finset.mem_inter, mem_edgesOfFinset]
  exact ⟨fun h ↦ ⟨fun v hv ↦ (h v hv).1, fun v hv ↦ (h v hv).2⟩,
    fun ⟨hs, ht⟩ v hv ↦ ⟨hs v hv, ht v hv⟩⟩

private lemma edgesOfFinset_eq_empty_of_card_le_one {n : ℕ} {u : Finset (Fin n)}
    (hu : u.card ≤ 1) : edgesOfFinset u = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨z, hne⟩ he
  rw [mem_edgesOfFinset] at he
  revert hne he
  refine Sym2.ind (fun x y hne he ↦ ?_) z
  have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hne
  exact hxy (Finset.card_le_one.mp hu x (he x (Sym2.mem_mk_left x y))
    y (he y (Sym2.mem_mk_right x y)))

private lemma card_edgesOfFinset_of_card_eq_two {n : ℕ} {u : Finset (Fin n)}
    (hu : u.card = 2) : (edgesOfFinset u).card = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hu
  suffices h : edgesOfFinset {a, b} = {mkEdgePair hab} by
    rw [h, Finset.card_singleton]
  ext ⟨z, hne⟩
  rw [Finset.mem_singleton, mem_edgesOfFinset]
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

private lemma card_edgesOfFinset_of_card_eq_three {n : ℕ} {t : Finset (Fin n)}
    (ht : t.card = 3) : (edgesOfFinset t).card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht
  have heq : edgesOfFinset {a, b, c} = {mkEdgePair hab, mkEdgePair hac, mkEdgePair hbc} := by
    ext ⟨z, hne⟩
    rw [mem_edgesOfFinset]
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
  have h12 : mkEdgePair hab ≠ mkEdgePair hac := fun h ↦
    hbc (Sym2.congr_right.mp (congrArg Subtype.val h))
  have h13 : mkEdgePair hab ≠ mkEdgePair hbc := fun h ↦ by
    have hz : s(b, a) = s(b, c) := Sym2.eq_swap.trans (congrArg Subtype.val h)
    exact hac (Sym2.congr_right.mp hz)
  have h23 : mkEdgePair hac ≠ mkEdgePair hbc := fun h ↦
    hab (Sym2.congr_left.mp (congrArg Subtype.val h))
  rw [heq]
  exact Finset.card_triple_eq_three_iff.mpr ⟨h12, h13, h23⟩

private lemma card_edgesOfFinset_union_of_inter_two {n : ℕ} {s t : Finset (Fin n)}
    (hs : s.card = 3) (ht : t.card = 3) (hst : (s ∩ t).card = 2) :
    (edgesOfFinset s ∪ edgesOfFinset t).card = 5 := by
  have h := Finset.card_union_add_card_inter (edgesOfFinset s) (edgesOfFinset t)
  rw [← edgesOfFinset_inter, card_edgesOfFinset_of_card_eq_two hst,
    card_edgesOfFinset_of_card_eq_three hs, card_edgesOfFinset_of_card_eq_three ht] at h
  omega

private lemma isNClique_three_iff_edges {n : ℕ} {G : SimpleGraph (Fin n)} {t : Finset (Fin n)}
    (ht : t.card = 3) :
    G.IsNClique 3 t ↔ ∀ e ∈ edgesOfFinset t, e.1 ∈ G.edgeSet := by
  rw [SimpleGraph.isNClique_iff]
  constructor
  · rintro ⟨hcl, _⟩ ⟨z, hne⟩ he
    rw [mem_edgesOfFinset] at he
    revert hne he
    refine Sym2.ind (fun u v hne he ↦ ?_) z
    have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hne
    rw [SimpleGraph.mem_edgeSet]
    exact hcl (he u (Sym2.mem_mk_left u v)) (he v (Sym2.mem_mk_right u v)) huv
  · intro hedges
    refine ⟨fun u hu v hv huv ↦ ?_, ht⟩
    have he : mkEdgePair huv ∈ edgesOfFinset t := by
      simp only [mem_edgesOfFinset, mkEdgePair, Sym2.ball]
      exact ⟨hu, hv⟩
    simpa [mkEdgePair, SimpleGraph.mem_edgeSet] using hedges (mkEdgePair huv) he

/-- `{0, 1}`-valued indicator that the `i`-th vertex triple forms a triangle in `G`
(`SteinIntro.tex:920`). -/
private noncomputable def triIndicator {n : ℕ} (i : Fin (n.choose 3))
    (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | H.IsNClique 3 (tripleOf i)}.indicator 1 G

private lemma triIndicator_of_isNClique {n : ℕ} {i : Fin (n.choose 3)} {G : SimpleGraph (Fin n)}
    (hG : G.IsNClique 3 (tripleOf i)) : triIndicator i G = 1 := by
  unfold triIndicator
  exact Set.indicator_of_mem hG 1

private lemma triIndicator_of_not_isNClique {n : ℕ} {i : Fin (n.choose 3)}
    {G : SimpleGraph (Fin n)} (hG : ¬ G.IsNClique 3 (tripleOf i)) : triIndicator i G = 0 := by
  unfold triIndicator
  exact Set.indicator_of_notMem hG 1

private lemma edgeIndicator_of_mem {n : ℕ} {e : EdgePair n} {G : SimpleGraph (Fin n)}
    (he : e.1 ∈ G.edgeSet) : edgeIndicator e G = 1 := by
  unfold edgeIndicator
  exact Set.indicator_of_mem he 1

private lemma edgeIndicator_of_notMem {n : ℕ} {e : EdgePair n} {G : SimpleGraph (Fin n)}
    (he : e.1 ∉ G.edgeSet) : edgeIndicator e G = 0 := by
  unfold edgeIndicator
  exact Set.indicator_of_notMem he 1

private lemma triIndicator_eq_prod_edgeIndicator {n : ℕ} (i : Fin (n.choose 3))
    (G : SimpleGraph (Fin n)) :
    triIndicator i G = ∏ e ∈ edgesOfFinset (tripleOf i), edgeIndicator e G := by
  by_cases hG : G.IsNClique 3 (tripleOf i)
  · rw [triIndicator_of_isNClique hG]
    refine (Finset.prod_eq_one fun e he ↦ ?_).symm
    exact edgeIndicator_of_mem ((isNClique_three_iff_edges (card_tripleOf i)).mp hG e he)
  · rw [triIndicator_of_not_isNClique hG]
    have hnotall : ¬ ∀ e ∈ edgesOfFinset (tripleOf i), e.1 ∈ G.edgeSet :=
      mt (isNClique_three_iff_edges (card_tripleOf i)).mpr hG
    obtain ⟨e, he1⟩ := not_forall.mp hnotall
    obtain ⟨he, hnot⟩ := not_imp.mp he1
    exact (Finset.prod_eq_zero he (edgeIndicator_of_notMem hnot)).symm

private lemma ncard_cliqueSet_three_eq_sum {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((G.cliqueSet 3).ncard : ℝ) = ∑ i : Fin (n.choose 3), triIndicator i G := by
  classical
  let S : Finset (Finset (Fin n)) := (triples n).filter fun s ↦ G.IsNClique 3 s
  have hS : (S : Set (Finset (Fin n))) = G.cliqueSet 3 := by
    ext s
    simp only [S, Finset.mem_coe, Finset.mem_filter, triples, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, SimpleGraph.mem_cliqueSet_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.card_eq, h⟩⟩
  rw [← hS, Set.ncard_coe_finset]
  have hcard : (S.card : ℝ) = ∑ s ∈ triples n,
      {H : SimpleGraph (Fin n) | H.IsNClique 3 s}.indicator (1 : SimpleGraph (Fin n) → ℝ) G := by
    calc (S.card : ℝ)
        = ∑ _s ∈ S, (1 : ℝ) := by simp
      _ = ∑ s ∈ triples n, if G.IsNClique 3 s then (1 : ℝ) else 0 := by
          simp [S]
      _ = ∑ s ∈ triples n,
            {H : SimpleGraph (Fin n) | H.IsNClique 3 s}.indicator
              (1 : SimpleGraph (Fin n) → ℝ) G := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          by_cases hs : G.IsNClique 3 s <;> simp [hs]
  rw [hcard, Finset.sum_subtype (triples n) fun _ ↦ Iff.rfl]
  exact ((tripleEquiv n).sum_comp fun s : {t // t ∈ triples n} ↦
    {H : SimpleGraph (Fin n) | H.IsNClique 3 s.1}.indicator
      (1 : SimpleGraph (Fin n) → ℝ) G).symm

/-! ### 2. Dependency neighborhoods and exact degree $3n - 8$ -/

/-- Dependency neighborhood of triple `i`: triples sharing at least $2$ vertices with `i`
(`SteinIntro.tex:921-925`). -/
private noncomputable def triNhbd {n : ℕ} (i : Fin (n.choose 3)) : Finset (Fin (n.choose 3)) :=
  Finset.univ.filter fun j ↦ 2 ≤ (tripleOf i ∩ tripleOf j).card

private lemma mem_triNhbd {n : ℕ} {i j : Fin (n.choose 3)} :
    j ∈ triNhbd i ↔ 2 ≤ (tripleOf i ∩ tripleOf j).card := by
  simp [triNhbd]

private lemma self_mem_triNhbd {n : ℕ} (i : Fin (n.choose 3)) : i ∈ triNhbd i := by
  rw [mem_triNhbd, Finset.inter_self, card_tripleOf]
  decide

private lemma triNhbd_symm {n : ℕ} {i j : Fin (n.choose 3)} (h : j ∈ triNhbd i) :
    i ∈ triNhbd j := by
  rw [mem_triNhbd] at h ⊢
  rwa [Finset.inter_comm]

private lemma mem_erase_triNhbd_iff {n : ℕ} {i j : Fin (n.choose 3)} :
    j ∈ (triNhbd i).erase i ↔ (tripleOf i ∩ tripleOf j).card = 2 := by
  rw [Finset.mem_erase, mem_triNhbd]
  constructor
  · rintro ⟨hne, hle⟩
    have hub : (tripleOf i ∩ tripleOf j).card ≤ 3 :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq (card_tripleOf i)
    by_contra hnot2
    have h3 : (tripleOf i ∩ tripleOf j).card = 3 := by omega
    have hi_eq : tripleOf i ∩ tripleOf j = tripleOf i :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [card_tripleOf, h3])
    have hj_eq : tripleOf i ∩ tripleOf j = tripleOf j :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [card_tripleOf, h3])
    exact hne (tripleOf_injective (hj_eq.symm.trans hi_eq))
  · intro h2
    refine ⟨?_, by omega⟩
    rintro rfl
    rw [Finset.inter_self, card_tripleOf] at h2
    omega

private lemma card_filter_inter_eq_two {n : ℕ} {t : Finset (Fin n)} (ht : t.card = 3) :
    ((triples n).filter fun s ↦ (t ∩ s).card = 2).card = 3 * (n - 3) := by
  let P : Finset (Finset (Fin n) × Finset (Fin n)) :=
    t.powersetCard 2 ×ˢ ((Finset.univ \ t).powersetCard 1)
  have hbij : ((triples n).filter fun s ↦ (t ∩ s).card = 2).card = P.card := by
    refine Finset.card_nbij' (fun s ↦ (t ∩ s, s \ t)) (fun p ↦ p.1 ∪ p.2) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, triples, Finset.mem_powersetCard,
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
      simp only [Finset.mem_coe, Finset.mem_filter, triples, Finset.mem_powersetCard,
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

private lemma card_erase_triNhbd {n : ℕ} (i : Fin (n.choose 3)) :
    ((triNhbd i).erase i).card = 3 * (n - 3) := by
  rw [← card_filter_inter_eq_two (card_tripleOf i)]
  refine Finset.card_bij (fun j _ ↦ tripleOf j) ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_filter.mpr ⟨tripleOf_mem j, mem_erase_triNhbd_iff.mp hj⟩
  · intro j₁ _ j₂ _ h
    exact tripleOf_injective h
  · intro s hs
    rcases Finset.mem_filter.mp hs with ⟨hs_mem, hs_inter⟩
    let j : Fin (n.choose 3) := (tripleEquiv n).symm ⟨s, hs_mem⟩
    have hj_eq : tripleOf j = s :=
      congrArg Subtype.val ((tripleEquiv n).apply_symm_apply ⟨s, hs_mem⟩)
    refine ⟨j, mem_erase_triNhbd_iff.mpr ?_, hj_eq⟩
    rwa [hj_eq]

private lemma card_triNhbd {n : ℕ} (hn : 3 ≤ n) (i : Fin (n.choose 3)) :
    (triNhbd i).card = 3 * n - 8 := by
  have h := Finset.card_erase_add_one (self_mem_triNhbd i)
  rw [card_erase_triNhbd] at h
  omega

private lemma sup_card_triNhbd_cast {n : ℕ} (hn : 3 ≤ n) :
    ((Finset.univ.sup fun i : Fin (n.choose 3) ↦ (triNhbd i).card : ℕ) : ℝ) =
      3 * (n : ℝ) - 8 := by
  have hne : (Finset.univ : Finset (Fin (n.choose 3))).Nonempty :=
    ⟨⟨0, Nat.choose_pos hn⟩, Finset.mem_univ _⟩
  have hfn : (fun i : Fin (n.choose 3) ↦ (triNhbd i).card) = fun _ ↦ 3 * n - 8 :=
    funext fun i ↦ card_triNhbd hn i
  have hsup : (Finset.univ.sup fun i : Fin (n.choose 3) ↦ (triNhbd i).card) = 3 * n - 8 := by
    rw [hfn, Finset.sup_const hne]
  have hle : 8 ≤ 3 * n := by omega
  rw [hsup, Nat.cast_sub hle]
  push_cast
  ring

/-! ### 3. Centered triangle indicators and dependency graph property -/

/-- Centered triangle indicator $X_i = Y_i - p^3$ (`SteinIntro.tex:920-926`). -/
private noncomputable def triCentered {n : ℕ} (p : ℝ) (i : Fin (n.choose 3))
    (G : SimpleGraph (Fin n)) : ℝ :=
  triIndicator i G - p ^ 3

private lemma isDependencyGraph_triCentered {n : ℕ} (p : ℝ) :
    IsDependencyGraph (erdosRenyi n p) (triCentered (n := n) p) triNhbd := by
  refine ⟨self_mem_triNhbd, fun _ _ ↦ triNhbd_symm, ?_⟩
  intro A B hAB
  let E_A : Finset (EdgePair n) := A.biUnion fun a ↦ edgesOfFinset (tripleOf a)
  let E_B : Finset (EdgePair n) := B.biUnion fun b ↦ edgesOfFinset (tripleOf b)
  have hdisj : Disjoint E_A E_B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    obtain ⟨a, ha, hea⟩ := Finset.mem_biUnion.mp heA
    obtain ⟨b, hb, heb⟩ := Finset.mem_biUnion.mp heB
    have hnot : ¬ 2 ≤ (tripleOf a ∩ tripleOf b).card := by
      simpa [mem_triNhbd] using hAB a ha b hb
    have hle1 : (tripleOf a ∩ tripleOf b).card ≤ 1 := by omega
    have he_inter : e ∈ edgesOfFinset (tripleOf a ∩ tripleOf b) := by
      rw [edgesOfFinset_inter]
      exact Finset.mem_inter.mpr ⟨hea, heb⟩
    rw [edgesOfFinset_eq_empty_of_card_le_one hle1] at he_inter
    exact Finset.notMem_empty e he_inter
  let f_A : (E_A → ℝ) → (A → ℝ) := fun x a ↦
    (∏ e ∈ (edgesOfFinset (tripleOf a.1)).attach,
      x ⟨e.1, Finset.mem_biUnion.mpr ⟨a.1, a.2, e.2⟩⟩) - p ^ 3
  let f_B : (E_B → ℝ) → (B → ℝ) := fun y b ↦
    (∏ e ∈ (edgesOfFinset (tripleOf b.1)).attach,
      y ⟨e.1, Finset.mem_biUnion.mpr ⟨b.1, b.2, e.2⟩⟩) - p ^ 3
  have hf_A : Measurable f_A := by
    rw [measurable_pi_iff]
    intro a
    refine Measurable.sub_const ?_ (p ^ 3)
    exact Finset.measurable_prod _ fun e _ ↦
      measurable_pi_apply (⟨e.1, Finset.mem_biUnion.mpr ⟨a.1, a.2, e.2⟩⟩ : E_A)
  have hf_B : Measurable f_B := by
    rw [measurable_pi_iff]
    intro b
    refine Measurable.sub_const ?_ (p ^ 3)
    exact Finset.measurable_prod _ fun e _ ↦
      measurable_pi_apply (⟨e.1, Finset.mem_biUnion.mpr ⟨b.1, b.2, e.2⟩⟩ : E_B)
  have heq_A : (fun G : SimpleGraph (Fin n) ↦ f_A (fun e ↦ edgeIndicator e.1 G)) =
      fun G (a : A) ↦ triCentered p a.1 G := by
    ext G a
    simp only [f_A, triCentered, triIndicator_eq_prod_edgeIndicator]
    rw [Finset.prod_attach _ (fun e ↦ edgeIndicator e G)]
  have heq_B : (fun G : SimpleGraph (Fin n) ↦ f_B (fun e ↦ edgeIndicator e.1 G)) =
      fun G (b : B) ↦ triCentered p b.1 G := by
    ext G b
    simp only [f_B, triCentered, triIndicator_eq_prod_edgeIndicator]
    rw [Finset.prod_attach _ (fun e ↦ edgeIndicator e G)]
  simpa only [heq_A, heq_B] using
    erdosRenyi_indepFun_of_disjoint_edges E_A E_B hdisj hf_A hf_B

/-! ### 4. Moments, exact variance, and Theorem 3.5 bound -/

private lemma erdosRenyi_integrable {n : ℕ} {p : ℝ} (f : SimpleGraph (Fin n) → ℝ) :
    Integrable f (erdosRenyi n p) :=
  depGraph_integrable_of_memLp_four MemLp.of_discrete

private lemma integral_eq_of_two_values {n : ℕ} {p : ℝ}
    (E : Set (SimpleGraph (Fin n))) {f : SimpleGraph (Fin n) → ℝ} {c₁ c₀ : ℝ}
    (h₁ : ∀ G ∈ E, f G = c₁) (h₀ : ∀ G ∉ E, f G = c₀) :
    ∫ G, f G ∂erdosRenyi n p = c₀ + (c₁ - c₀) * (erdosRenyi n p).real E := by
  have hf : f = fun G ↦ c₀ + (c₁ - c₀) * E.indicator (fun _ ↦ (1 : ℝ)) G := by
    ext G
    by_cases hG : G ∈ E
    · rw [Set.indicator_of_mem hG, h₁ G hG]
      ring
    · rw [Set.indicator_of_notMem hG, h₀ G hG]
      ring
  rw [hf, integral_add (erdosRenyi_integrable _) (erdosRenyi_integrable _),
    integral_const_mul, integral_indicator MeasurableSet.of_discrete,
    setIntegral_one_eq_measureReal]
  simp

private lemma erdosRenyi_real_isNClique_three {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.IsNClique 3 (tripleOf i)} = p ^ 3 := by
  have hset : {G : SimpleGraph (Fin n) | G.IsNClique 3 (tripleOf i)} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ edgesOfFinset (tripleOf i), e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
    ext G
    simp [isNClique_three_iff_edges (card_tripleOf i)]
  rw [hset, erdosRenyi_real_cylinder hp0 hp1 _ _ (Finset.disjoint_empty_right _),
    card_edgesOfFinset_of_card_eq_three (card_tripleOf i)]
  simp

private lemma erdosRenyi_real_isNClique_pair {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {i j : Fin (n.choose 3)} (hj : j ∈ (triNhbd i).erase i) :
    (erdosRenyi n p).real
        {G : SimpleGraph (Fin n) |
          G.IsNClique 3 (tripleOf i) ∧ G.IsNClique 3 (tripleOf j)} = p ^ 5 := by
  let S_pos : Finset (EdgePair n) :=
    edgesOfFinset (tripleOf i) ∪ edgesOfFinset (tripleOf j)
  have hset : {G : SimpleGraph (Fin n) |
        G.IsNClique 3 (tripleOf i) ∧ G.IsNClique 3 (tripleOf j)} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ S_pos, e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_ofPred_eq, isNClique_three_iff_edges (card_tripleOf i),
      isNClique_three_iff_edges (card_tripleOf j), S_pos, Finset.mem_union,
      Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨fun ⟨hi', hj'⟩ e he ↦ he.elim (hi' e) (hj' e),
      fun h ↦ ⟨fun e he ↦ h e (Or.inl he), fun e he ↦ h e (Or.inr he)⟩⟩
  have hcard : S_pos.card = 5 :=
    card_edgesOfFinset_union_of_inter_two (card_tripleOf i) (card_tripleOf j)
      (mem_erase_triNhbd_iff.mp hj)
  rw [hset, erdosRenyi_real_cylinder hp0 hp1 _ _ (Finset.disjoint_empty_right _), hcard]
  simp

private lemma integral_triIndicator {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, triIndicator i G ∂erdosRenyi n p = p ^ 3 := by
  rw [integral_eq_of_two_values {G | G.IsNClique 3 (tripleOf i)}
    (c₁ := 1) (c₀ := 0)
    (fun G hG ↦ by simp [triIndicator, Set.indicator_of_mem hG])
    (fun G hG ↦ by simp [triIndicator, Set.indicator_of_notMem hG]),
    erdosRenyi_real_isNClique_three hp0 hp1 i]
  ring

private lemma integral_cliqueSet_three {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ G, ((G.cliqueSet 3).ncard : ℝ) ∂erdosRenyi n p = (n.choose 3 : ℝ) * p ^ 3 := by
  simp_rw [ncard_cliqueSet_three_eq_sum]
  rw [integral_finsetSum Finset.univ fun i _ ↦ erdosRenyi_integrable _]
  simp [integral_triIndicator hp0 hp1]

private lemma integral_triCentered {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, triCentered p i G ∂erdosRenyi n p = 0 := by
  rw [integral_eq_of_two_values {G | G.IsNClique 3 (tripleOf i)}
    (c₁ := 1 - p ^ 3) (c₀ := -p ^ 3)
    (fun G hG ↦ by simp [triCentered, triIndicator, Set.indicator_of_mem hG])
    (fun G hG ↦ by simp [triCentered, triIndicator, Set.indicator_of_notMem hG]),
    erdosRenyi_real_isNClique_three hp0 hp1 i]
  ring

private lemma one_sub_pow_three_nonneg {p : ℝ} (hp1 : p ≤ 1) : 0 ≤ 1 - p ^ 3 := by
  have hfac : 1 - p ^ 3 = (1 - p) * ((p + 1 / 2) ^ 2 + 3 / 4) := by ring
  rw [hfac]
  exact mul_nonneg (by linarith) (by positivity)

private lemma integral_abs_triCentered_cubed {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, |triCentered p i G| ^ 3 ∂erdosRenyi n p =
      p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 2 + p ^ 6) := by
  have h1p3 : 0 ≤ 1 - p ^ 3 := one_sub_pow_three_nonneg hp1
  have hp3 : 0 ≤ p ^ 3 := pow_nonneg hp0 3
  rw [integral_eq_of_two_values {G | G.IsNClique 3 (tripleOf i)}
    (c₁ := (1 - p ^ 3) ^ 3) (c₀ := p ^ 9)
    (fun G hG ↦ by
      simp [triCentered, triIndicator, Set.indicator_of_mem hG, abs_of_nonneg h1p3])
    (fun G hG ↦ by
      simp only [triCentered, triIndicator, Set.indicator_of_notMem hG, zero_sub,
        abs_neg, abs_of_nonneg hp3]
      ring),
    erdosRenyi_real_isNClique_three hp0 hp1 i]
  ring

private lemma integral_triCentered_pow_four {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, triCentered p i G ^ 4 ∂erdosRenyi n p =
      p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9) := by
  rw [integral_eq_of_two_values {G | G.IsNClique 3 (tripleOf i)}
    (c₁ := (1 - p ^ 3) ^ 4) (c₀ := p ^ 12)
    (fun G hG ↦ by simp [triCentered, triIndicator, Set.indicator_of_mem hG])
    (fun G hG ↦ by
      simp only [triCentered, triIndicator, Set.indicator_of_notMem hG]
      ring),
    erdosRenyi_real_isNClique_three hp0 hp1 i]
  ring

private lemma integral_triCentered_sq {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, triCentered p i G * triCentered p i G ∂erdosRenyi n p = p ^ 3 * (1 - p ^ 3) := by
  rw [integral_eq_of_two_values {G | G.IsNClique 3 (tripleOf i)}
    (c₁ := (1 - p ^ 3) ^ 2) (c₀ := p ^ 6)
    (fun G hG ↦ by
      simp only [triCentered, triIndicator, Set.indicator_of_mem hG, Pi.one_apply]
      ring)
    (fun G hG ↦ by
      simp only [triCentered, triIndicator, Set.indicator_of_notMem hG]
      ring),
    erdosRenyi_real_isNClique_three hp0 hp1 i]
  ring

private lemma integral_triCentered_mul_of_mem_erase {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {i j : Fin (n.choose 3)} (hj : j ∈ (triNhbd i).erase i) :
    ∫ G, triCentered p i G * triCentered p j G ∂erdosRenyi n p =
      p ^ 3 * p ^ 2 * (1 - p) := by
  have hprod : ∫ G, triIndicator i G * triIndicator j G ∂erdosRenyi n p = p ^ 5 := by
    rw [integral_eq_of_two_values
      {G | G.IsNClique 3 (tripleOf i) ∧ G.IsNClique 3 (tripleOf j)}
      (c₁ := 1) (c₀ := 0)
      (fun G hG ↦ by
        rw [triIndicator_of_isNClique hG.1, triIndicator_of_isNClique hG.2, mul_one])
      (fun G hG ↦ by
        by_cases hi : G.IsNClique 3 (tripleOf i)
        · have hnj : ¬ G.IsNClique 3 (tripleOf j) := fun hj' ↦ hG ⟨hi, hj'⟩
          rw [triIndicator_of_not_isNClique hnj, mul_zero]
        · rw [triIndicator_of_not_isNClique hi, zero_mul]),
      erdosRenyi_real_isNClique_pair hp0 hp1 hj]
    ring
  have hexpand : (fun G ↦ triCentered p i G * triCentered p j G) =
      fun G ↦ (triIndicator i G * triIndicator j G - p ^ 3 * triIndicator i G) -
        p ^ 3 * triIndicator j G + p ^ 6 := by
    ext G
    simp only [triCentered]
    ring
  rw [hexpand, integral_add (erdosRenyi_integrable _) (erdosRenyi_integrable _),
    integral_sub (erdosRenyi_integrable _) (erdosRenyi_integrable _),
    integral_sub (erdosRenyi_integrable _) (erdosRenyi_integrable _),
    integral_const_mul, integral_const_mul, hprod,
    integral_triIndicator hp0 hp1 i, integral_triIndicator hp0 hp1 j]
  simp only [integral_const, probReal_univ, one_smul]
  ring

private lemma variance_triCentered_sum {n : ℕ} {p : ℝ} (hn : 3 ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.variance
        (fun G ↦ ∑ i : Fin (n.choose 3), triCentered p i G) (erdosRenyi n p) =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) := by
  rw [← depGraph_integral_quadSum_eq_variance (erdosRenyi n p)
    (N := triNhbd)
    (fun _ ↦ Measurable.of_discrete.aemeasurable)
    (fun _ ↦ MemLp.of_discrete)
    (fun i ↦ integral_triCentered hp0 hp1 i)
    (isDependencyGraph_triCentered p)]
  rw [integral_finsetSum Finset.univ fun i _ ↦ erdosRenyi_integrable _]
  have hinner : ∀ i : Fin (n.choose 3),
      (∫ G, ∑ k ∈ triNhbd i, triCentered p i G * triCentered p k G ∂erdosRenyi n p) =
        p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) := by
    intro i
    rw [integral_finsetSum (triNhbd i) fun k _ ↦ erdosRenyi_integrable _,
      ← Finset.insert_erase (self_mem_triNhbd i),
      Finset.sum_insert (Finset.notMem_erase _ _),
      integral_triCentered_sq hp0 hp1 i]
    have herase : ∑ k ∈ (triNhbd i).erase i,
          (∫ G, triCentered p i G * triCentered p k G ∂erdosRenyi n p) =
        ∑ _k ∈ (triNhbd i).erase i, (p ^ 3 * p ^ 2 * (1 - p)) :=
      Finset.sum_congr rfl fun k hk ↦ integral_triCentered_mul_of_mem_erase hp0 hp1 hk
    have hcast : (((3 * (n - 3) : ℕ) : ℝ)) = 3 * ((n : ℝ) - 3) := by
      rw [Nat.cast_mul, Nat.cast_sub hn]
      norm_num
    rw [herase, Finset.sum_const, card_erase_triNhbd i, nsmul_eq_mul, hcast]
    ring
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Section 3.2.1 application, restricted (`SteinIntro.tex:918-949`; `ISSUE-TYPO-3.2.1`,
`ISSUE-3.2.1`): exact expectation, exact variance, and Theorem 3.5 Wasserstein normal
approximation bound for the triangle count in $G(n, p)$ when $n \ge 3$ and $0 < p < 1$. -/
theorem Sec3_2_1_triangles_restricted_proof : Sec3_2_1_triangles_restricted := by
  intro Ω' _ P' _ n p Z hn hp0 hp1 hZ hZ_law T μ σ W
  have hμ : μ = (n.choose 3 : ℝ) * p ^ 3 := integral_cliqueSet_three hp0.le hp1.le
  have hsum_X : ∀ G : SimpleGraph (Fin n),
      (∑ i : Fin (n.choose 3), triCentered p i G) = T G - μ := by
    intro G
    simp only [triCentered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← ncard_cliqueSet_three_eq_sum, T, hμ]
  have hfun_X : (fun G : SimpleGraph (Fin n) ↦ ∑ i : Fin (n.choose 3), triCentered p i G) =
      fun G ↦ T G + (-μ) := by
    ext G
    rw [hsum_X G, sub_eq_add_neg]
  have hVar_eq : ProbabilityTheory.variance
        (fun G ↦ ∑ i : Fin (n.choose 3), triCentered p i G) (erdosRenyi n p) =
      ProbabilityTheory.variance T (erdosRenyi n p) := by
    rw [hfun_X]
    exact ProbabilityTheory.variance_add_const Measurable.of_discrete.aestronglyMeasurable (-μ)
  have hVarT : ProbabilityTheory.variance T (erdosRenyi n p) =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) := by
    rw [← hVar_eq, variance_triCentered_sum hn hp0.le hp1.le]
  have hVar_pos : 0 < ProbabilityTheory.variance
      (fun G ↦ ∑ i : Fin (n.choose 3), triCentered p i G) (erdosRenyi n p) := by
    rw [variance_triCentered_sum hn hp0.le hp1.le]
    have hchoose : (0 : ℝ) < (n.choose 3 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hn)
    have hp3_pos : 0 < p ^ 3 := pow_pos hp0 3
    have h1p3_pos : 0 < 1 - p ^ 3 := by
      have hfac : 1 - p ^ 3 = (1 - p) * ((p + 1 / 2) ^ 2 + 3 / 4) := by ring
      rw [hfac]
      exact mul_pos (by linarith) (by positivity)
    have hn3_nonneg : 0 ≤ (n : ℝ) - 3 := by
      have hn_cast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hextra : 0 ≤ 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hn3_nonneg) (sq_nonneg p))
        (by linarith)
    exact mul_pos (mul_pos hchoose hp3_pos) (by linarith)
  refine ⟨hμ, hVarT, ?_⟩
  have h1 := wassersteinDist_map_stdNormal_le_iSup_normalSteinOp
    (erdosRenyi n p) P' (W := W) Measurable.of_discrete.aemeasurable hZ hZ_law
  have h2 := depGraph_iSup_normalWassersteinClass_le (erdosRenyi n p)
    (X := triCentered p) (N := triNhbd)
    (fun _ ↦ Measurable.of_discrete.aemeasurable)
    (fun _ ↦ MemLp.of_discrete)
    (fun i ↦ integral_triCentered hp0.le hp1.le i)
    (isDependencyGraph_triCentered p)
    hVar_pos
  dsimp only at h2
  have hσ_eq : Real.sqrt (ProbabilityTheory.variance
      (fun G ↦ ∑ i : Fin (n.choose 3), triCentered p i G) (erdosRenyi n p)) = σ := by
    rw [hVar_eq]
  have hW_app : ∀ ω : SimpleGraph (Fin n),
      (∑ i : Fin (n.choose 3), triCentered p i ω) / σ = W ω := by
    intro ω
    dsimp only [W]
    rw [hsum_X ω]
  have hsum3 : (∑ i : Fin (n.choose 3), ∫ G, |triCentered p i G| ^ 3 ∂erdosRenyi n p) =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 2 + p ^ 6) := by
    simp_rw [integral_abs_triCentered_cubed hp0.le hp1.le]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hsum4 : (∑ i : Fin (n.choose 3), ∫ G, triCentered p i G ^ 4 ∂erdosRenyi n p) =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9) := by
    simp_rw [integral_triCentered_pow_four hp0.le hp1.le]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hσ_eq, hW_app] at h2
  rw [sup_card_triNhbd_cast hn, hsum3, hsum4] at h2
  exact h1.trans h2

end SteinMethod
