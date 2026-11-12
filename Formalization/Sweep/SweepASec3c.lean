/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Dependency
import Formalization.Defs.RandomGraph
import Formalization.RandomGraph.ErdosRenyi
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic

/-!
# Section 3.2.1 Gap Proofs (`SWEEP-A`: `A12`)

Proves the Section 3.2.1 Erdős–Rényi triangle decomposition, dependency degree, central moment
formula, and pairwise-independence characterization in Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:919-928`):

* `sec3_2_1_triangles_setup_and_moments_proof` (`A12`, `Sec3_2_1_triangles_setup_and_moments`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-- The $3$-element subsets of vertices in `Fin n`. -/
def triples (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard 3

/-- Construct an `EdgePair n` from two distinct vertices `u ≠ v` in `Fin n`. -/
def mkEdgePair {n : ℕ} {u v : Fin n} (hne : u ≠ v) : EdgePair n :=
  ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using hne⟩

/-- Potential edges of `SimpleGraph (Fin n)` with both endpoints in `t : Finset (Fin n)`. -/
def edgesOfFinset {n : ℕ} (t : Finset (Fin n)) : Finset (EdgePair n) :=
  Finset.univ.filter fun e : EdgePair n ↦ ∀ v ∈ e.1, v ∈ t

lemma mem_edgesOfFinset {n : ℕ} {e : EdgePair n} {t : Finset (Fin n)} :
    e ∈ edgesOfFinset t ↔ ∀ v ∈ e.1, v ∈ t := by
  simp [edgesOfFinset]

lemma edgesOfFinset_inter {n : ℕ} (s t : Finset (Fin n)) :
    edgesOfFinset (s ∩ t) = edgesOfFinset s ∩ edgesOfFinset t := by
  ext e
  simp only [Finset.mem_inter, mem_edgesOfFinset]
  exact ⟨fun h ↦ ⟨fun v hv ↦ (h v hv).1, fun v hv ↦ (h v hv).2⟩,
    fun ⟨hs, ht⟩ v hv ↦ ⟨hs v hv, ht v hv⟩⟩

lemma edgesOfFinset_eq_empty_of_card_le_one {n : ℕ} {u : Finset (Fin n)}
    (hu : u.card ≤ 1) : edgesOfFinset u = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨z, hne⟩ he
  rw [mem_edgesOfFinset] at he
  revert hne he
  refine Sym2.ind (fun x y hne he ↦ ?_) z
  have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hne
  exact hxy (Finset.card_le_one.mp hu x (he x (Sym2.mem_mk_left x y))
    y (he y (Sym2.mem_mk_right x y)))

lemma card_edgesOfFinset_of_card_eq_two {n : ℕ} {u : Finset (Fin n)}
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

lemma card_edgesOfFinset_of_card_eq_three {n : ℕ} {t : Finset (Fin n)}
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

lemma card_edgesOfFinset_union_of_inter_two {n : ℕ} {s t : Finset (Fin n)}
    (hs : s.card = 3) (ht : t.card = 3) (hst : (s ∩ t).card = 2) :
    (edgesOfFinset s ∪ edgesOfFinset t).card = 5 := by
  have h := Finset.card_union_add_card_inter (edgesOfFinset s) (edgesOfFinset t)
  rw [← edgesOfFinset_inter, card_edgesOfFinset_of_card_eq_two hst,
    card_edgesOfFinset_of_card_eq_three hs, card_edgesOfFinset_of_card_eq_three ht] at h
  omega

lemma isNClique_three_iff_edges {n : ℕ} {G : SimpleGraph (Fin n)} {t : Finset (Fin n)}
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

lemma mem_cliqueSet_three_iff_edges {n : ℕ} {G : SimpleGraph (Fin n)} {t : Finset (Fin n)}
    (ht : t.card = 3) :
    t ∈ G.cliqueSet 3 ↔ ∀ e ∈ edgesOfFinset t, e.1 ∈ G.edgeSet := by
  rw [SimpleGraph.mem_cliqueSet_iff, isNClique_three_iff_edges ht]

lemma card_filter_inter_eq_two {n : ℕ} {t : Finset (Fin n)} (ht : t.card = 3) :
    (((triples n).filter fun s ↦ (t ∩ s).card = 2)).card = 3 * (n - 3) := by
  let P : Finset (Finset (Fin n) × Finset (Fin n)) :=
    t.powersetCard 2 ×ˢ ((Finset.univ \ t).powersetCard 1)
  have hbij : (((triples n).filter fun s ↦ (t ∩ s).card = 2)).card = P.card := by
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

/-- Statement type for `sec3_2_1_triangles_setup_and_moments_proof`
(`SteinIntro.tex:919-928`, `A12`). -/
abbrev sec3_2_1_triangles_setup_and_moments_stmt : Prop :=
  ∀ {n : ℕ}, 3 ≤ n →
    Nonempty (Fin (n.choose 3) ≃ {s : Finset (Fin n) // s.card = 3}) ∧
    ∀ (enum : Fin (n.choose 3) ≃ {s : Finset (Fin n) // s.card = 3}),
      let Y : Fin (n.choose 3) → SimpleGraph (Fin n) → ℝ :=
        fun i ↦ {G : SimpleGraph (Fin n) | (enum i).1 ∈ G.cliqueSet 3}.indicator 1
      let N_nbhd : Fin (n.choose 3) → Finset (Fin (n.choose 3)) :=
        fun i ↦ Finset.univ.filter (fun j ↦ j = i ∨ ((enum i).1 ∩ (enum j).1).card = 2)
      (∀ G : SimpleGraph (Fin n),
        ((G.cliqueSet 3).ncard : ℝ) = ∑ i : Fin (n.choose 3), Y i G) ∧
      (∀ i : Fin (n.choose 3),
        (N_nbhd i).card = 3 * (n - 3) + 1 ∧
        ((N_nbhd i).card : ℝ) = 3 * (n : ℝ) - 8) ∧
      (∀ {p : ℝ}, 0 ≤ p → p ≤ 1 →
        let X : Fin (n.choose 3) → SimpleGraph (Fin n) → ℝ := fun i G ↦ Y i G - p ^ 3
        IsDependencyGraph (erdosRenyi n p) X N_nbhd ∧
        ∀ (i : Fin (n.choose 3)) (k : ℕ), 1 ≤ k →
          ∫ G, |X i G| ^ k ∂erdosRenyi n p =
            p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ (k - 1) + p ^ (3 * (k - 1)))) ∧
      (∀ {p : ℝ}, 0 < p → p < 1 →
        ∀ i j : Fin (n.choose 3), i ≠ j →
          (ProbabilityTheory.IndepFun (Y i) (Y j) (erdosRenyi n p) ↔
            Disjoint {e : EdgePair n | ∀ v ∈ e.1, v ∈ (enum i).1}
              {e : EdgePair n | ∀ v ∈ e.1, v ∈ (enum j).1}))

/-- Library proof of `Sec3_2_1_triangles_setup_and_moments` (`SteinIntro.tex:919-928`). -/
theorem sec3_2_1_triangles_setup_and_moments_proof :
    sec3_2_1_triangles_setup_and_moments_stmt := by
  classical
  intro n hn
  have h_prop (s : Finset (Fin n)) : s ∈ triples n ↔ s.card = 3 := by
    simp only [triples, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  let e_sub : {s : Finset (Fin n) // s ∈ triples n} ≃ {s : Finset (Fin n) // s.card = 3} :=
    Equiv.subtypeEquivRight (fun s ↦ h_prop s)
  have hcard_triples : (triples n).card = n.choose 3 := by
    simp only [triples, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hcard_sub : Fintype.card {s : Finset (Fin n) // s.card = 3} = n.choose 3 := by
    rw [← Fintype.card_congr e_sub, Fintype.card_of_subtype (triples n) fun _ ↦ Iff.rfl,
      hcard_triples]
  have hnonempty : Nonempty (Fin (n.choose 3) ≃ {s : Finset (Fin n) // s.card = 3}) :=
    ⟨(Fintype.equivFinOfCardEq hcard_sub).symm⟩
  refine ⟨hnonempty, fun enum ↦ ?_⟩
  dsimp only
  let Y : Fin (n.choose 3) → SimpleGraph (Fin n) → ℝ :=
    fun i ↦ {G : SimpleGraph (Fin n) | (enum i).1 ∈ G.cliqueSet 3}.indicator 1
  let N_nbhd : Fin (n.choose 3) → Finset (Fin (n.choose 3)) :=
    fun i ↦ Finset.univ.filter (fun j ↦ j = i ∨ ((enum i).1 ∩ (enum j).1).card = 2)
  have hclique_eq : ∀ G : SimpleGraph (Fin n),
      ((G.cliqueSet 3).ncard : ℝ) = ∑ i : Fin (n.choose 3), Y i G := by
    intro G
    let S : Finset (Fin (n.choose 3)) :=
      Finset.univ.filter fun i ↦ (enum i).1 ∈ G.cliqueSet 3
    have hsum : (∑ i : Fin (n.choose 3), Y i G) = (S.card : ℝ) := by
      have hY : (fun i : Fin (n.choose 3) ↦ Y i G) =
          fun i ↦ if (enum i).1 ∈ G.cliqueSet 3 then (1 : ℝ) else 0 := by
        ext i
        dsimp only [Y]
        rw [Set.indicator_apply]
        simp only [Pi.one_apply, Set.mem_ofPred_eq]
      rw [hY]
      simp [S]
    have hS_card : S.card = (G.cliqueSet 3).ncard := by
      let C : Finset (Finset (Fin n)) :=
        Finset.univ.filter fun s ↦ s ∈ G.cliqueSet 3
      have hC_ncard : C.card = (G.cliqueSet 3).ncard := by
        rw [Set.ncard_eq_toFinset_card (G.cliqueSet 3)]
        congr 1
        ext s
        simp [C]
      rw [← hC_ncard]
      refine Finset.card_bij (fun i _ ↦ (enum i).1) ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_univ _, hi.2⟩
      · intro i₁ _ i₂ _ h
        exact enum.injective (Subtype.ext h)
      · intro s hs
        rw [Finset.mem_filter] at hs
        have hs3 : s.card = 3 := (SimpleGraph.mem_cliqueSet_iff.mp hs.2).2
        let j := enum.symm ⟨s, hs3⟩
        have hj_eq : (enum j).1 = s := by
          change (enum (enum.symm ⟨s, hs3⟩)).1 = s
          rw [Equiv.apply_symm_apply]
        refine ⟨j, ?_, hj_eq⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hj_eq]
        exact hs.2
    rw [hsum, hS_card]
  have hN_card : ∀ i : Fin (n.choose 3),
      (N_nbhd i).card = 3 * (n - 3) + 1 ∧
      ((N_nbhd i).card : ℝ) = 3 * (n : ℝ) - 8 := by
    intro i
    let t := (enum i).1
    have ht : t.card = 3 := (enum i).2
    have herase : (N_nbhd i).erase i =
        Finset.univ.filter fun j ↦ ((enum i).1 ∩ (enum j).1).card = 2 := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, N_nbhd]
      constructor
      · rintro ⟨hne, rfl | h2⟩
        · exact (hne rfl).elim
        · exact h2
      · intro h2
        refine ⟨fun h_eq ↦ ?_, Or.inr h2⟩
        subst h_eq
        rw [Finset.inter_self, ht] at h2
        norm_num at h2
    have herase_card : ((N_nbhd i).erase i).card = 3 * (n - 3) := by
      rw [herase]
      have hbij := card_filter_inter_eq_two ht
      rw [← hbij]
      refine Finset.card_bij (fun j _ ↦ (enum j).1) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        simp only [triples, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        exact ⟨(enum j).2, hj.2⟩
      · intro j₁ _ j₂ _ h
        exact enum.injective (Subtype.ext h)
      · intro s hs
        rw [Finset.mem_filter] at hs
        have hs3 : s.card = 3 := by
          simp only [triples, Finset.mem_powersetCard] at hs
          exact hs.1.2
        let j := enum.symm ⟨s, hs3⟩
        have hj_eq : (enum j).1 = s := by
          change (enum (enum.symm ⟨s, hs3⟩)).1 = s
          rw [Equiv.apply_symm_apply]
        refine ⟨j, ?_, hj_eq⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hj_eq]
        exact hs.2
    have hi_mem : i ∈ N_nbhd i := by
      simp [N_nbhd]
    have hcard1 : (N_nbhd i).card = 3 * (n - 3) + 1 := by
      have h := Finset.card_erase_add_one hi_mem
      rw [herase_card] at h
      omega
    have hcard2 : ((N_nbhd i).card : ℝ) = 3 * (n : ℝ) - 8 := by
      rw [hcard1]
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn]
      push_cast
      ring
    exact ⟨hcard1, hcard2⟩
  refine ⟨hclique_eq, hN_card, fun {p} hp0 hp1 ↦ ?_, fun {p} hp0 hp1 ↦ ?_⟩
  · let X : Fin (n.choose 3) → SimpleGraph (Fin n) → ℝ := fun i G ↦ Y i G - p ^ 3
    have hY_eq_prod (i : Fin (n.choose 3)) (G : SimpleGraph (Fin n)) :
        Y i G = ∏ e ∈ edgesOfFinset (enum i).1, edgeIndicator e G := by
      dsimp only [Y]
      have ht : (enum i).1.card = 3 := (enum i).2
      by_cases hG : (enum i).1 ∈ G.cliqueSet 3
      · have hG' : G ∈ {G' : SimpleGraph (Fin n) | (enum i).1 ∈ G'.cliqueSet 3} := hG
        rw [Set.indicator_of_mem hG' 1]
        refine (Finset.prod_eq_one fun e he ↦ ?_).symm
        unfold edgeIndicator
        exact Set.indicator_of_mem ((mem_cliqueSet_three_iff_edges ht).mp hG e he) 1
      · have hG' : G ∉ {G' : SimpleGraph (Fin n) | (enum i).1 ∈ G'.cliqueSet 3} := hG
        rw [Set.indicator_of_notMem hG' 1]
        have hnot := mt (mem_cliqueSet_three_iff_edges ht).mpr hG
        obtain ⟨e, he1⟩ := not_forall.mp hnot
        obtain ⟨he, hnot_edge⟩ := not_imp.mp he1
        have hz : edgeIndicator e G = 0 := by
          unfold edgeIndicator
          exact Set.indicator_of_notMem hnot_edge 1
        exact (Finset.prod_eq_zero he hz).symm
    have hdep : IsDependencyGraph (erdosRenyi n p) X N_nbhd := by
      refine ⟨fun i ↦ by simp [N_nbhd], fun i j hij ↦ ?_, fun A B hAB ↦ ?_⟩
      · simp only [N_nbhd, Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
        rcases hij with rfl | h2
        · exact Or.inl rfl
        · rw [Finset.inter_comm] at h2
          exact Or.inr h2
      · let E_A : Finset (EdgePair n) := A.biUnion fun a ↦ edgesOfFinset (enum a).1
        let E_B : Finset (EdgePair n) := B.biUnion fun b ↦ edgesOfFinset (enum b).1
        have hdisj : Disjoint E_A E_B := by
          rw [Finset.disjoint_left]
          intro e heA heB
          obtain ⟨a, ha, hea⟩ := Finset.mem_biUnion.mp heA
          obtain ⟨b, hb, heb⟩ := Finset.mem_biUnion.mp heB
          have hnot : b ∉ N_nbhd a := hAB a ha b hb
          simp only [N_nbhd, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hnot
          have hcard_inter : ((enum a).1 ∩ (enum b).1).card ≤ 1 := by
            have hsub : (enum a).1 ∩ (enum b).1 ⊆ (enum a).1 := Finset.inter_subset_left
            have hle3 : ((enum a).1 ∩ (enum b).1).card ≤ 3 :=
              (Finset.card_le_card hsub).trans_eq (enum a).2
            have hne3 : ((enum a).1 ∩ (enum b).1).card ≠ 3 := fun h3 ↦ by
              have heq : (enum a).1 ∩ (enum b).1 = (enum a).1 :=
                Finset.eq_of_subset_of_card_le hsub (by rw [h3, (enum a).2])
              have heq' : (enum a).1 ⊆ (enum b).1 := by
                rw [← heq]
                exact Finset.inter_subset_right
              have heq_set : (enum a).1 = (enum b).1 :=
                Finset.eq_of_subset_of_card_le heq' (by rw [(enum a).2, (enum b).2])
              exact hnot.1 (enum.injective (Subtype.ext heq_set.symm))
            have hne2 : ((enum a).1 ∩ (enum b).1).card ≠ 2 := hnot.2
            omega
          have he_inter : e ∈ edgesOfFinset ((enum a).1 ∩ (enum b).1) := by
            rw [edgesOfFinset_inter]
            exact Finset.mem_inter.mpr ⟨hea, heb⟩
          rw [edgesOfFinset_eq_empty_of_card_le_one hcard_inter] at he_inter
          exact Finset.notMem_empty e he_inter
        let f_A : (E_A → ℝ) → (A → ℝ) := fun x a ↦
          (∏ e ∈ (edgesOfFinset (enum a.1).1).attach,
            x ⟨e.1, Finset.mem_biUnion.mpr ⟨a.1, a.2, e.2⟩⟩) - p ^ 3
        let f_B : (E_B → ℝ) → (B → ℝ) := fun y b ↦
          (∏ e ∈ (edgesOfFinset (enum b.1).1).attach,
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
            fun G (a : A) ↦ X a.1 G := by
          ext G a
          dsimp only [f_A, X]
          rw [hY_eq_prod a.1 G, Finset.prod_attach _ (fun e ↦ edgeIndicator e G)]
        have heq_B : (fun G : SimpleGraph (Fin n) ↦ f_B (fun e ↦ edgeIndicator e.1 G)) =
            fun G (b : B) ↦ X b.1 G := by
          ext G b
          dsimp only [f_B, X]
          rw [hY_eq_prod b.1 G, Finset.prod_attach _ (fun e ↦ edgeIndicator e G)]
        simpa only [heq_A, heq_B] using
          erdosRenyi_indepFun_of_disjoint_edges E_A E_B hdisj hf_A hf_B
    have hprob_cyl (S : Finset (EdgePair n)) :
        (erdosRenyi n p).real
          {G : SimpleGraph (Fin n) | ∀ e ∈ S, e.1 ∈ G.edgeSet} = p ^ S.card := by
      have heq_pos : {G : SimpleGraph (Fin n) | ∀ e ∈ S, e.1 ∈ G.edgeSet} =
          {G : SimpleGraph (Fin n) |
            (∀ e ∈ S, e.1 ∈ G.edgeSet) ∧
            (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
        ext G
        simp only [Set.mem_ofPred_eq, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
          and_true]
      rw [heq_pos, erdosRenyi_real_cylinder hp0 hp1 S ∅ (Finset.disjoint_empty_right S)]
      simp only [Finset.card_empty, pow_zero, mul_one]
    have hmoment : ∀ (i : Fin (n.choose 3)) (k : ℕ), 1 ≤ k →
        ∫ G, |X i G| ^ k ∂erdosRenyi n p =
          p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ (k - 1) + p ^ (3 * (k - 1))) := by
      intro i k hk
      have ht : (enum i).1.card = 3 := (enum i).2
      have he_card : (edgesOfFinset (enum i).1).card = 3 :=
        card_edgesOfFinset_of_card_eq_three ht
      have hpos_prob : (erdosRenyi n p).real {G | (enum i).1 ∈ G.cliqueSet 3} = p ^ 3 := by
        have heq_set : {G : SimpleGraph (Fin n) | (enum i).1 ∈ G.cliqueSet 3} =
            {G : SimpleGraph (Fin n) | ∀ e ∈ edgesOfFinset (enum i).1, e.1 ∈ G.edgeSet} := by
          ext G
          simp only [Set.mem_ofPred_eq, mem_cliqueSet_three_iff_edges ht]
        rw [heq_set, hprob_cyl, he_card]
      have hval1 (G : SimpleGraph (Fin n)) (hG : (enum i).1 ∈ G.cliqueSet 3) :
          |X i G| ^ k = (1 - p ^ 3) ^ k := by
        dsimp only [X, Y]
        have hG' : G ∈ {G' | (enum i).1 ∈ G'.cliqueSet 3} := hG
        rw [Set.indicator_of_mem hG' 1, Pi.one_apply]
        have hsub : 0 ≤ 1 - p ^ 3 := by
          have hp3 : p ^ 3 ≤ 1 := by
            nlinarith [pow_le_one₀ hp0 hp1 (n := 3)]
          linarith
        rw [abs_of_nonneg hsub]
      have hval0 (G : SimpleGraph (Fin n)) (hG : (enum i).1 ∉ G.cliqueSet 3) :
          |X i G| ^ k = (p ^ 3) ^ k := by
        dsimp only [X, Y]
        have hG' : G ∉ {G' | (enum i).1 ∈ G'.cliqueSet 3} := hG
        rw [Set.indicator_of_notMem hG' 1]
        simp only [zero_sub, abs_neg, abs_of_nonneg (pow_nonneg hp0 3)]
      have hint : ∫ G, |X i G| ^ k ∂erdosRenyi n p =
          (p ^ 3) ^ k + ((1 - p ^ 3) ^ k - (p ^ 3) ^ k) * p ^ 3 := by
        let E := {G : SimpleGraph (Fin n) | (enum i).1 ∈ G.cliqueSet 3}
        have hf : (fun G ↦ |X i G| ^ k) =
            fun G ↦ (p ^ 3) ^ k + ((1 - p ^ 3) ^ k - (p ^ 3) ^ k) *
              E.indicator (fun _ ↦ (1 : ℝ)) G := by
          ext G
          by_cases hG : G ∈ E
          · rw [Set.indicator_of_mem hG, hval1 G hG]
            ring
          · rw [Set.indicator_of_notMem hG, hval0 G hG]
            ring
        have hint_const1 :
            Integrable (fun _ : SimpleGraph (Fin n) ↦ (p ^ 3) ^ k) (erdosRenyi n p) :=
          integrable_const _
        have hint_ind : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) (erdosRenyi n p) :=
          (integrable_const (1 : ℝ)).indicator MeasurableSet.of_discrete
        have hint_const2 : Integrable (fun G ↦ ((1 - p ^ 3) ^ k - (p ^ 3) ^ k) *
            E.indicator (fun _ ↦ (1 : ℝ)) G) (erdosRenyi n p) :=
          hint_ind.const_mul _
        rw [hf, integral_add hint_const1 hint_const2, integral_const, probReal_univ, one_smul,
          integral_const_mul, integral_indicator MeasurableSet.of_discrete,
          setIntegral_one_eq_measureReal]
        simp only [E, hpos_prob]
      rw [hint]
      have hk1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
      have hpow1 : (1 - p ^ 3) ^ k = (1 - p ^ 3) * (1 - p ^ 3) ^ (k - 1) := by
        conv_lhs => rw [hk1, pow_add, pow_one]
        ring
      have hpow2 : (p ^ 3) ^ k = p ^ 3 * p ^ (3 * (k - 1)) := by
        conv_lhs => rw [hk1, pow_add, pow_one, ← pow_mul]
        ring
      rw [hpow1, hpow2]
      ring
    exact ⟨hdep, hmoment⟩
  · intro i j hij
    let E_i : Finset (EdgePair n) := edgesOfFinset (enum i).1
    let E_j : Finset (EdgePair n) := edgesOfFinset (enum j).1
    have hE_i_card : E_i.card = 3 := card_edgesOfFinset_of_card_eq_three (enum i).2
    have hE_j_card : E_j.card = 3 := card_edgesOfFinset_of_card_eq_three (enum j).2
    have hY_eq_prod (k : Fin (n.choose 3)) (G : SimpleGraph (Fin n)) :
        Y k G = ∏ e ∈ edgesOfFinset (enum k).1, edgeIndicator e G := by
      dsimp only [Y]
      have ht : (enum k).1.card = 3 := (enum k).2
      by_cases hG : (enum k).1 ∈ G.cliqueSet 3
      · have hG' : G ∈ {G' : SimpleGraph (Fin n) | (enum k).1 ∈ G'.cliqueSet 3} := hG
        rw [Set.indicator_of_mem hG' 1]
        refine (Finset.prod_eq_one fun e he ↦ ?_).symm
        unfold edgeIndicator
        exact Set.indicator_of_mem ((mem_cliqueSet_three_iff_edges ht).mp hG e he) 1
      · have hG' : G ∉ {G' : SimpleGraph (Fin n) | (enum k).1 ∈ G'.cliqueSet 3} := hG
        rw [Set.indicator_of_notMem hG' 1]
        have hnot := mt (mem_cliqueSet_three_iff_edges ht).mpr hG
        obtain ⟨e, he1⟩ := not_forall.mp hnot
        obtain ⟨he, hnot_edge⟩ := not_imp.mp he1
        have hz : edgeIndicator e G = 0 := by
          unfold edgeIndicator
          exact Set.indicator_of_notMem hnot_edge 1
        exact (Finset.prod_eq_zero he hz).symm
    have hprob_cyl (S : Finset (EdgePair n)) :
        (erdosRenyi n p).real
          {G : SimpleGraph (Fin n) | ∀ e ∈ S, e.1 ∈ G.edgeSet} = p ^ S.card := by
      have heq_pos : {G : SimpleGraph (Fin n) | ∀ e ∈ S, e.1 ∈ G.edgeSet} =
          {G : SimpleGraph (Fin n) |
            (∀ e ∈ S, e.1 ∈ G.edgeSet) ∧
            (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
        ext G
        simp only [Set.mem_ofPred_eq, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
          and_true]
      rw [heq_pos, erdosRenyi_real_cylinder hp0.le hp1.le S ∅ (Finset.disjoint_empty_right S)]
      simp only [Finset.card_empty, pow_zero, mul_one]
    have hset_i : {e : EdgePair n | ∀ v ∈ e.1, v ∈ (enum i).1} =
        (E_i : Set (EdgePair n)) := by
      ext e; simp [E_i, mem_edgesOfFinset]
    have hset_j : {e : EdgePair n | ∀ v ∈ e.1, v ∈ (enum j).1} =
        (E_j : Set (EdgePair n)) := by
      ext e; simp [E_j, mem_edgesOfFinset]
    rw [hset_i, hset_j, Finset.disjoint_coe]
    constructor
    · intro hindep
      by_contra hnot_disj
      have hcard_inter : ((enum i).1 ∩ (enum j).1).card = 2 := by
        have hne : (enum i).1 ≠ (enum j).1 := fun heq ↦
          hij (enum.injective (Subtype.ext heq))
        have hsub : (enum i).1 ∩ (enum j).1 ⊆ (enum i).1 := Finset.inter_subset_left
        have hle3 : ((enum i).1 ∩ (enum j).1).card ≤ 3 :=
          (Finset.card_le_card hsub).trans_eq (enum i).2
        have hne3 : ((enum i).1 ∩ (enum j).1).card ≠ 3 := fun h3 ↦ by
          have heq : (enum i).1 ∩ (enum j).1 = (enum i).1 :=
            Finset.eq_of_subset_of_card_le hsub (by rw [h3, (enum i).2])
          have heq' : (enum i).1 ⊆ (enum j).1 := by
            rw [← heq]
            exact Finset.inter_subset_right
          have heq_all : (enum i).1 = (enum j).1 :=
            Finset.eq_of_subset_of_card_le heq' (by rw [(enum i).2, (enum j).2])
          exact hne heq_all
        have hle2 : ((enum i).1 ∩ (enum j).1).card ≤ 2 := by omega
        have hge2 : 2 ≤ ((enum i).1 ∩ (enum j).1).card := by
          by_contra hlt2
          have hle1 : ((enum i).1 ∩ (enum j).1).card ≤ 1 := by omega
          have he_empty : edgesOfFinset ((enum i).1 ∩ (enum j).1) = ∅ :=
            edgesOfFinset_eq_empty_of_card_le_one hle1
          rw [edgesOfFinset_inter] at he_empty
          exact hnot_disj (Finset.disjoint_iff_inter_eq_empty.mpr he_empty)
        omega
      have hunion_card : (E_i ∪ E_j).card = 5 :=
        card_edgesOfFinset_union_of_inter_two (enum i).2 (enum j).2 hcard_inter
      have heq_Yi (G : SimpleGraph (Fin n)) : Y i G = 1 ↔ ∀ e ∈ E_i, e.1 ∈ G.edgeSet := by
        dsimp only [Y]
        rw [Set.indicator_apply]
        simp only [Set.mem_ofPred_eq, Pi.one_apply]
        have ht : (enum i).1.card = 3 := (enum i).2
        rw [mem_cliqueSet_three_iff_edges ht]
        constructor
        · intro h
          split_ifs at h with h1
          · exact h1
          · norm_num at h
        · intro h
          split_ifs with h1
          · rfl
          · exact (h1 h).elim
      have heq_Yj (G : SimpleGraph (Fin n)) : Y j G = 1 ↔ ∀ e ∈ E_j, e.1 ∈ G.edgeSet := by
        dsimp only [Y]
        rw [Set.indicator_apply]
        simp only [Set.mem_ofPred_eq, Pi.one_apply]
        have ht : (enum j).1.card = 3 := (enum j).2
        rw [mem_cliqueSet_three_iff_edges ht]
        constructor
        · intro h
          split_ifs at h with h1
          · exact h1
          · norm_num at h
        · intro h
          split_ifs with h1
          · rfl
          · exact (h1 h).elim
      have heq_both : {G : SimpleGraph (Fin n) | Y i G = 1 ∧ Y j G = 1} =
          {G : SimpleGraph (Fin n) | ∀ e ∈ E_i ∪ E_j, e.1 ∈ G.edgeSet} := by
        ext G
        simp only [Set.mem_ofPred_eq, Finset.mem_union, heq_Yi G, heq_Yj G]
        exact ⟨fun ⟨hi, hj⟩ e he ↦ he.elim (hi e) (hj e),
          fun h ↦ ⟨fun e he ↦ h e (Or.inl he), fun e he ↦ h e (Or.inr he)⟩⟩
      have hprob_both : (erdosRenyi n p).real
          {G : SimpleGraph (Fin n) | Y i G = 1 ∧ Y j G = 1} = p ^ 5 := by
        rw [heq_both, hprob_cyl (E_i ∪ E_j), hunion_card]
      have hprob_i : (erdosRenyi n p).real {G | Y i G = 1} = p ^ 3 := by
        have hset : {G : SimpleGraph (Fin n) | Y i G = 1} =
            {G | ∀ e ∈ E_i, e.1 ∈ G.edgeSet} := by
          ext G; simp [heq_Yi G]
        rw [hset, hprob_cyl E_i, hE_i_card]
      have hprob_j : (erdosRenyi n p).real {G | Y j G = 1} = p ^ 3 := by
        have hset : {G : SimpleGraph (Fin n) | Y j G = 1} =
            {G | ∀ e ∈ E_j, e.1 ∈ G.edgeSet} := by
          ext G; simp [heq_Yj G]
        rw [hset, hprob_cyl E_j, hE_j_card]
      have hmeas_i :
          MeasurableSet[MeasurableSpace.comap (Y i) inferInstance] (Y i ⁻¹' {1}) :=
        ⟨{1}, MeasurableSet.singleton 1, rfl⟩
      have hmeas_j :
          MeasurableSet[MeasurableSpace.comap (Y j) inferInstance] (Y j ⁻¹' {1}) :=
        ⟨{1}, MeasurableSet.singleton 1, rfl⟩
      have hind_meas := hindep.meas_inter hmeas_i hmeas_j
      have hind_real : (erdosRenyi n p).real ((Y i ⁻¹' {1}) ∩ (Y j ⁻¹' {1})) =
          (erdosRenyi n p).real (Y i ⁻¹' {1}) * (erdosRenyi n p).real (Y j ⁻¹' {1}) := by
        change ((erdosRenyi n p) ((Y i ⁻¹' {1}) ∩ (Y j ⁻¹' {1}))).toReal =
          ((erdosRenyi n p) (Y i ⁻¹' {1})).toReal * ((erdosRenyi n p) (Y j ⁻¹' {1})).toReal
        rw [hind_meas, ENNReal.toReal_mul]
      have hset_both : {G | Y i G = 1 ∧ Y j G = 1} = (Y i ⁻¹' {1}) ∩ (Y j ⁻¹' {1}) := by
        ext G; simp
      have hset_i' : {G | Y i G = 1} = Y i ⁻¹' {1} := by ext G; simp
      have hset_j' : {G | Y j G = 1} = Y j ⁻¹' {1} := by ext G; simp
      rw [← hset_both, ← hset_i', ← hset_j'] at hind_real
      rw [hprob_both, hprob_i, hprob_j] at hind_real
      have hp33 : p ^ 3 * p ^ 3 = p ^ 6 := by ring
      rw [hp33] at hind_real
      have hcontra : p ^ 5 * (1 - p) = 0 := by
        calc p ^ 5 * (1 - p) = p ^ 5 - p ^ 6 := by ring
          _ = p ^ 5 - p ^ 5 := by rw [← hind_real]
          _ = 0 := sub_self _
      have hp_pos5 : 0 < p ^ 5 := pow_pos hp0 5
      have h1p_pos : 0 < 1 - p := sub_pos.mpr hp1
      have hprod_pos : 0 < p ^ 5 * (1 - p) := mul_pos hp_pos5 h1p_pos
      linarith
    · intro hdisj
      let f_i : (E_i → ℝ) → ℝ := fun x ↦ ∏ e ∈ E_i.attach, x e
      let f_j : (E_j → ℝ) → ℝ := fun y ↦ ∏ e ∈ E_j.attach, y e
      have hf_i : Measurable f_i :=
        Finset.measurable_prod _ fun e _ ↦ measurable_pi_apply e
      have hf_j : Measurable f_j :=
        Finset.measurable_prod _ fun e _ ↦ measurable_pi_apply e
      have heq_i : (fun G ↦ f_i (fun e ↦ edgeIndicator e.1 G)) = Y i := by
        ext G
        dsimp only [f_i]
        rw [Finset.prod_attach E_i (fun e ↦ edgeIndicator e G), ← hY_eq_prod i G]
      have heq_j : (fun G ↦ f_j (fun e ↦ edgeIndicator e.1 G)) = Y j := by
        ext G
        dsimp only [f_j]
        rw [Finset.prod_attach E_j (fun e ↦ edgeIndicator e G), ← hY_eq_prod j G]
      simpa only [heq_i, heq_j] using
        erdosRenyi_indepFun_of_disjoint_edges E_i E_j hdisj hf_i hf_j

end SteinMethod
