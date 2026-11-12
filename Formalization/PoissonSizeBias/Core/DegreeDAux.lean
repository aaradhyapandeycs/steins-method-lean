/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Core.IsolatedVerticesCoupling

/-!
# Neighborhood Replacement (`Formalization.PoissonSizeBias.Core.DegreeDAux`)

Neighborhood-replacement decomposition (`replaceNeighbors`, `nbrCouplingPMF`), symmetry under
vertex permutations fixing `v`, and the non-vacuity witness `degreeDCouplingPMF_ncard_neighborSet`
for Example 4.6 (`SteinIntro.tex:2220-2246`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Neighborhood replacement and decomposition of `degreeDCouplingPMF` -/

open Classical in
/-- Replace the neighborhood of vertex `v` in `G` by `T \ {v}`, leaving all edges not incident to
`v` unchanged (`SteinIntro.tex:2227-2234`). -/
noncomputable def replaceNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (T : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj x y :=
    if x = v then y ≠ v ∧ y ∈ T
    else if y = v then x ≠ v ∧ x ∈ T
    else G.Adj x y
  symm := ⟨fun x y h ↦ by
    by_cases hxv : x = v
    · subst hxv
      simp only [↓reduceIte] at h
      simp [h.1, h.2]
    · by_cases hyv : y = v
      · subst hyv
        simp only [hxv, ↓reduceIte] at h ⊢
        exact h
      · simp only [hxv, hyv, ↓reduceIte] at h ⊢
        exact G.adj_symm h⟩
  loopless := ⟨fun x h ↦ by
    by_cases hxv : x = v
    · subst hxv
      simp at h
    · simp only [hxv, ↓reduceIte] at h
      exact G.loopless.irrefl x h⟩

@[simp]
lemma replaceNeighbors_adj_left {n : ℕ} (G : SimpleGraph (Fin n)) (v y : Fin n)
    (T : Finset (Fin n)) :
    (replaceNeighbors G v T).Adj v y ↔ y ≠ v ∧ y ∈ T := by
  simp [replaceNeighbors]

lemma replaceNeighbors_adj_off {n : ℕ} (G : SimpleGraph (Fin n)) {v x y : Fin n}
    (hxv : x ≠ v) (hyv : y ≠ v) (T : Finset (Fin n)) :
    (replaceNeighbors G v T).Adj x y ↔ G.Adj x y := by
  simp [replaceNeighbors, hxv, hyv]

lemma neighborFinset_subset_erase {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    [Fintype (G.neighborSet v)] :
    G.neighborFinset v ⊆ Finset.univ.erase v := by
  intro u hu
  rw [SimpleGraph.mem_neighborFinset] at hu
  exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hu).symm, Finset.mem_univ u⟩

open Classical in
lemma replaceNeighbors_neighborFinset {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    {T : Finset (Fin n)} (hT : T ⊆ Finset.univ.erase v) :
    (replaceNeighbors G v T).neighborFinset v = T := by
  ext u
  rw [SimpleGraph.mem_neighborFinset, replaceNeighbors_adj_left]
  refine ⟨fun h ↦ h.2, fun hu ↦ ⟨Finset.ne_of_mem_erase (hT hu), hu⟩⟩

private lemma replaceNeighbors_ncard_neighborSet {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    {T : Finset (Fin n)} (hT : T ⊆ Finset.univ.erase v) :
    ((replaceNeighbors G v T).neighborSet v).ncard = T.card := by
  classical
  have hfin : (replaceNeighbors G v T).neighborSet v = (T : Set (Fin n)) := by
    ext u
    rw [SimpleGraph.mem_neighborSet, replaceNeighbors_adj_left]
    exact ⟨fun h ↦ h.2, fun hu ↦ ⟨Finset.ne_of_mem_erase (hT hu), hu⟩⟩
  rw [hfin, Set.ncard_coe_finset]

private lemma replaceNeighbors_deleteIncidenceSet_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) :
    replaceNeighbors (G.deleteIncidenceSet v) v T = replaceNeighbors G v T := by
  ext x y
  by_cases hxv : x = v
  · subst hxv
    simp [replaceNeighbors]
  · by_cases hyv : y = v
    · subst hyv
      simp [replaceNeighbors, hxv]
    · simp [replaceNeighbors, hxv, hyv, SimpleGraph.deleteIncidenceSet_adj]

lemma deleteIncidenceSet_replaceNeighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) (T : Finset (Fin n)) :
    (replaceNeighbors G v T).deleteIncidenceSet v = G.deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj]
  by_cases hxv : x = v
  · simp [hxv]
  · by_cases hyv : y = v
    · simp [hyv]
    · simp [replaceNeighbors_adj_off G hxv hyv T, hxv, hyv]

open Classical in
lemma self_eq_replaceNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    replaceNeighbors (G.deleteIncidenceSet v) v (G.neighborFinset v) = G := by
  rw [replaceNeighbors_deleteIncidenceSet_eq]
  ext x y
  by_cases hxv : x = v
  · subst hxv
    rw [replaceNeighbors_adj_left, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(G.ne_of_adj h).symm, h⟩⟩
  · by_cases hyv : y = v
    · subst hyv
      rw [SimpleGraph.adj_comm, replaceNeighbors_adj_left, SimpleGraph.mem_neighborFinset,
        SimpleGraph.adj_comm]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hxv, h⟩⟩
    · exact replaceNeighbors_adj_off G hxv hyv _

lemma replaceNeighbors_inj {n : ℕ} {K₁ K₂ : SimpleGraph (Fin n)} {v : Fin n}
    (hK₁ : K₁.IsIsolated v) (hK₂ : K₂.IsIsolated v)
    {T₁ T₂ : Finset (Fin n)} (hT₁ : T₁ ⊆ Finset.univ.erase v) (hT₂ : T₂ ⊆ Finset.univ.erase v)
    (heq : replaceNeighbors K₁ v T₁ = replaceNeighbors K₂ v T₂) :
    K₁ = K₂ ∧ T₁ = T₂ := by
  classical
  have hT : T₁ = T₂ := by
    have h := congrArg (fun H ↦ H.neighborFinset v) heq
    rwa [replaceNeighbors_neighborFinset K₁ v hT₁, replaceNeighbors_neighborFinset K₂ v hT₂] at h
  have hK : K₁ = K₂ := by
    have h := congrArg (fun H ↦ H.deleteIncidenceSet v) heq
    rw [deleteIncidenceSet_replaceNeighbors, deleteIncidenceSet_replaceNeighbors] at h
    have hdel : ∀ K : SimpleGraph (Fin n), K.IsIsolated v → K.deleteIncidenceSet v = K := by
      intro K hiso
      ext x y
      rw [SimpleGraph.deleteIncidenceSet_adj]
      refine ⟨fun h' ↦ h'.1, fun hxy ↦ ⟨hxy, ?_, ?_⟩⟩
      · rintro rfl; exact hiso y hxy
      · rintro rfl; exact hiso x hxy.symm
    rwa [hdel K₁ hK₁, hdel K₂ hK₂] at h
  exact ⟨hK, hT⟩

open Classical in
/-- Pure neighborhood-level transition underlying `degreeDCouplingPMF d v`. -/
noncomputable def nbrCouplingPMF (n d : ℕ) (v : Fin n)
    (N : Finset (Fin n)) : PMF (Finset (Fin n)) :=
  if d ≤ N.card then
    let choices := N.powersetCard (N.card - d)
    have hne : choices.Nonempty := Finset.powersetCard_nonempty.mpr (Nat.sub_le N.card d)
    (PMF.uniformOfFinset choices hne).map fun E ↦ N \ E
  else
    let nonNbrs : Finset (Fin n) := Finset.univ.erase v \ N
    let choices := nonNbrs.powersetCard (d - N.card)
    if hne : choices.Nonempty then
      (PMF.uniformOfFinset choices hne).map fun A ↦ N ∪ A
    else
      PMF.pure N

open Classical in
private lemma deleteEdges_eq_replaceNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    {E : Finset (Fin n)} (hE : E ⊆ G.neighborFinset v) :
    G.deleteEdges ((E.image fun u ↦ s(v, u)) : Set (Sym2 (Fin n))) =
      replaceNeighbors (G.deleteIncidenceSet v) v (G.neighborFinset v \ E) := by
  rw [replaceNeighbors_deleteIncidenceSet_eq]
  ext x y
  rw [SimpleGraph.deleteEdges_adj, Finset.coe_image, Set.mem_image]
  by_cases hxv : x = v
  · subst hxv
    rw [replaceNeighbors_adj_left, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hadj, hnot⟩
      refine ⟨(G.ne_of_adj hadj).symm, hadj, fun hyE ↦ hnot ⟨y, Finset.mem_coe.mpr hyE, rfl⟩⟩
    · rintro ⟨hyv, hadj, hyE⟩
      refine ⟨hadj, ?_⟩
      rintro ⟨u, huE, hsym⟩
      rcases Sym2.eq_iff.mp hsym with ⟨_, rfl⟩ | ⟨hxy, _⟩
      · exact hyE (Finset.mem_coe.mp huE)
      · exact hyv hxy.symm
  · by_cases hyv : y = v
    · subst hyv
      rw [SimpleGraph.adj_comm (replaceNeighbors _ _ _), replaceNeighbors_adj_left,
        Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hadj, hnot⟩
        refine ⟨hxv, hadj.symm, fun hxE ↦ hnot ⟨x, Finset.mem_coe.mpr hxE, Sym2.eq_swap⟩⟩
      · rintro ⟨_, hadj, hxE⟩
        refine ⟨hadj.symm, ?_⟩
        rintro ⟨u, huE, hsym⟩
        rcases Sym2.eq_iff.mp hsym with ⟨hyx, _⟩ | ⟨_, rfl⟩
        · exact hxv hyx.symm
        · exact hxE (Finset.mem_coe.mp huE)
    · rw [replaceNeighbors_adj_off G hxv hyv]
      refine ⟨fun h ↦ h.1, fun hadj ↦ ⟨hadj, ?_⟩⟩
      rintro ⟨u, _, hsym⟩
      rcases Sym2.eq_iff.mp hsym with ⟨hvx, _⟩ | ⟨hvy, _⟩
      · exact hxv hvx.symm
      · exact hyv hvy.symm

open Classical in
private lemma sup_fromEdgeSet_eq_replaceNeighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    {A : Finset (Fin n)} (hA : A ⊆ Finset.univ.erase v \ G.neighborFinset v) :
    G ⊔ SimpleGraph.fromEdgeSet ((A : Set (Fin n)).image fun u ↦ s(v, u)) =
      replaceNeighbors (G.deleteIncidenceSet v) v (G.neighborFinset v ∪ A) := by
  rw [replaceNeighbors_deleteIncidenceSet_eq]
  ext x y
  rw [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  by_cases hxv : x = v
  · subst hxv
    rw [replaceNeighbors_adj_left, Finset.mem_union, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (hadj | ⟨⟨u, huA, hsym⟩, hxy⟩)
      · exact ⟨(G.ne_of_adj hadj).symm, Or.inl hadj⟩
      · rcases Sym2.eq_iff.mp hsym with ⟨_, rfl⟩ | ⟨hxy', _⟩
        · exact ⟨hxy.symm, Or.inr (Finset.mem_coe.mp huA)⟩
        · exact absurd hxy' hxy
    · rintro ⟨hyx, hadj | hyA⟩
      · exact Or.inl hadj
      · exact Or.inr ⟨⟨y, Finset.mem_coe.mpr hyA, rfl⟩, hyx.symm⟩
  · by_cases hyv : y = v
    · subst hyv
      rw [SimpleGraph.adj_comm (replaceNeighbors _ _ _), replaceNeighbors_adj_left,
        Finset.mem_union, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro (hadj | ⟨⟨u, huA, hsym⟩, _⟩)
        · exact ⟨hxv, Or.inl hadj.symm⟩
        · rcases Sym2.eq_iff.mp hsym with ⟨hyx, _⟩ | ⟨_, rfl⟩
          · exact absurd hyx.symm hxv
          · exact ⟨hxv, Or.inr (Finset.mem_coe.mp huA)⟩
      · rintro ⟨_, hadj | hxA⟩
        · exact Or.inl hadj.symm
        · exact Or.inr ⟨⟨x, Finset.mem_coe.mpr hxA, Sym2.eq_swap⟩, hxv⟩
    · rw [replaceNeighbors_adj_off G hxv hyv]
      refine ⟨?_, fun hadj ↦ Or.inl hadj⟩
      rintro (hadj | ⟨⟨u, _, hsym⟩, _⟩)
      · exact hadj
      · rcases Sym2.eq_iff.mp hsym with ⟨hvx, _⟩ | ⟨hvy, _⟩
        · exact absurd hvx.symm hxv
        · exact absurd hvy.symm hyv

open Classical in
lemma degreeDCouplingPMF_eq_map_nbrCouplingPMF {n : ℕ} (d : ℕ) (v : Fin n)
    (G : SimpleGraph (Fin n)) :
    degreeDCouplingPMF d v G =
      (nbrCouplingPMF n d v (G.neighborFinset v)).map
        (replaceNeighbors (G.deleteIncidenceSet v) v) := by
  dsimp only [degreeDCouplingPMF, nbrCouplingPMF]
  split_ifs with h_ge hne
  · rw [PMF.map_comp]
    refine PMF.ext fun H ↦ ?_
    simp only [PMF.map_apply, Function.comp_apply]
    refine tsum_congr fun E ↦ ?_
    by_cases hE : E ∈ (G.neighborFinset v).powersetCard ((G.neighborFinset v).card - d)
    · have hsub : E ⊆ G.neighborFinset v := (Finset.mem_powersetCard.mp hE).1
      simp only [deleteEdges_eq_replaceNeighbors G v hsub]
    · have hne0 :
          ((G.neighborFinset v).powersetCard ((G.neighborFinset v).card - d)).Nonempty :=
        Finset.powersetCard_nonempty.mpr (Nat.sub_le (G.neighborFinset v).card d)
      have h0 :
          (PMF.uniformOfFinset
            ((G.neighborFinset v).powersetCard ((G.neighborFinset v).card - d)) hne0) E = 0 :=
        PMF.uniformOfFinset_apply_of_notMem hne0 hE
      rw [h0]
      simp only [ite_self]
  · have hlift : (do
        let a ← PMF.uniformOfFinset
          ((Finset.univ.erase v \ G.neighborFinset v).powersetCard
            (d - (G.neighborFinset v).card)) hne
        pure (a : Set (Fin n))) =
      (PMF.uniformOfFinset
        ((Finset.univ.erase v \ G.neighborFinset v).powersetCard
          (d - (G.neighborFinset v).card)) hne).map
        (fun A : Finset (Fin n) ↦ (A : Set (Fin n))) :=
      PMF.bind_pure_comp (fun A : Finset (Fin n) ↦ (A : Set (Fin n))) _
    rw [hlift, PMF.map_comp, PMF.map_comp]
    refine PMF.ext fun H ↦ ?_
    simp only [PMF.map_apply, Function.comp_apply]
    refine tsum_congr fun A ↦ ?_
    by_cases hA :
        A ∈ (Finset.univ.erase v \ G.neighborFinset v).powersetCard
          (d - (G.neighborFinset v).card)
    · have hsub : A ⊆ Finset.univ.erase v \ G.neighborFinset v :=
        (Finset.mem_powersetCard.mp hA).1
      simp only [sup_fromEdgeSet_eq_replaceNeighbors G v hsub]
    · have h0 :
          (PMF.uniformOfFinset
            ((Finset.univ.erase v \ G.neighborFinset v).powersetCard
              (d - (G.neighborFinset v).card)) hne) A = 0 :=
        PMF.uniformOfFinset_apply_of_notMem hne hA
      rw [h0]
      simp only [ite_self]
  · rw [PMF.pure_map, self_eq_replaceNeighbors]

open Classical in
lemma nbrCouplingPMF_support_subset_powersetCard {n d : ℕ} (hd : d < n) (v : Fin n)
    {N : Finset (Fin n)} (hN : N ⊆ Finset.univ.erase v) {T : Finset (Fin n)}
    (hT : T ∈ (nbrCouplingPMF n d v N).support) :
    T ∈ (Finset.univ.erase v).powersetCard d := by
  have hv_pos : 0 < n := v.pos
  dsimp only [nbrCouplingPMF] at hT
  split_ifs at hT with h_ge hne
  · rw [PMF.support_map, Set.mem_image] at hT
    rcases hT with ⟨E, hE, rfl⟩
    rw [PMF.support_uniformOfFinset] at hE
    obtain ⟨hEN, hEcard⟩ := Finset.mem_powersetCard.mp hE
    refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset.trans hN, ?_⟩
    rw [Finset.card_sdiff_of_subset hEN, hEcard]
    omega
  · rw [PMF.support_map, Set.mem_image] at hT
    rcases hT with ⟨A, hA, rfl⟩
    rw [PMF.support_uniformOfFinset] at hA
    obtain ⟨hAnon, hAcard⟩ := Finset.mem_powersetCard.mp hA
    have hA_erase : A ⊆ Finset.univ.erase v := hAnon.trans Finset.sdiff_subset
    have hdisj : Disjoint N A :=
      Finset.disjoint_left.mpr fun x hxN hxA ↦ (Finset.mem_sdiff.mp (hAnon hxA)).2 hxN
    refine Finset.mem_powersetCard.mpr ⟨Finset.union_subset hN hA_erase, ?_⟩
    rw [Finset.card_union_of_disjoint hdisj, hAcard]
    omega
  · exfalso
    apply hne
    refine Finset.powersetCard_nonempty.mpr ?_
    have hcard_erase : (Finset.univ.erase v).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_sdiff_of_subset hN, hcard_erase]
    omega

/-- **Non-vacuity sanity witness** for `degreeDCouplingPMF` (`SteinIntro.tex:2227-2236`):
when `d < n`, every graph `H` in the support of `degreeDCouplingPMF d v G` gives vertex `v` degree
`d`. -/
theorem degreeDCouplingPMF_ncard_neighborSet {n d : ℕ} (hd : d < n) (v : Fin n)
    (G : SimpleGraph (Fin n)) {H : SimpleGraph (Fin n)}
    (hH : H ∈ (degreeDCouplingPMF d v G).support) :
    (H.neighborSet v).ncard = d := by
  classical
  rw [degreeDCouplingPMF_eq_map_nbrCouplingPMF, PMF.support_map, Set.mem_image] at hH
  rcases hH with ⟨T, hT, rfl⟩
  have hT_mem :=
    nbrCouplingPMF_support_subset_powersetCard hd v (neighborFinset_subset_erase G v) hT
  obtain ⟨hT_sub, hT_card⟩ := Finset.mem_powersetCard.mp hT_mem
  rw [replaceNeighbors_ncard_neighborSet _ v hT_sub, hT_card]

/-! ### Symmetry and transitivity on `d`-subsets of `Finset.univ.erase v` -/

open Classical in
private lemma uniformOfFinset_powersetCard_image_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (k : ℕ) (hne : (S.powersetCard k).Nonempty)
    (hne' : ((S.image σ).powersetCard k).Nonempty) (B : Finset (Fin n)) :
    (PMF.uniformOfFinset ((S.image σ).powersetCard k) hne') (B.image σ) =
      (PMF.uniformOfFinset (S.powersetCard k) hne) B := by
  have hmem_iff : B.image σ ∈ (S.image σ).powersetCard k ↔ B ∈ S.powersetCard k := by
    simp only [Finset.mem_powersetCard, Finset.card_image_of_injective _ σ.injective]
    refine ⟨fun ⟨hsub, hk⟩ ↦ ⟨fun x hx ↦ ?_, hk⟩,
      fun ⟨hsub, hk⟩ ↦ ⟨Finset.image_subset_image hsub, hk⟩⟩
    have hx_im : σ x ∈ S.image σ := hsub (Finset.mem_image_of_mem σ hx)
    rcases Finset.mem_image.mp hx_im with ⟨y, hyS, hxy⟩
    exact σ.injective hxy ▸ hyS
  have hcard_eq : ((S.image σ).powersetCard k).card = (S.powersetCard k).card := by
    rw [Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_image_of_injective S σ.injective]
  by_cases hB : B ∈ S.powersetCard k
  · have hB' : B.image σ ∈ (S.image σ).powersetCard k := hmem_iff.mpr hB
    rw [PMF.uniformOfFinset_apply_of_mem hne' hB',
      PMF.uniformOfFinset_apply_of_mem hne hB, hcard_eq]
  · have hB' : B.image σ ∉ (S.image σ).powersetCard k := mt hmem_iff.mp hB
    rw [PMF.uniformOfFinset_apply_of_notMem hne' hB',
      PMF.uniformOfFinset_apply_of_notMem hne hB]

open Classical in
lemma nbrCouplingPMF_perm_eq {n d : ℕ} {v : Fin n} {σ : Equiv.Perm (Fin n)}
    (hσv : σ v = v) {N : Finset (Fin n)} (hN : N ⊆ Finset.univ.erase v) (T : Finset (Fin n)) :
    (nbrCouplingPMF n d v (N.image σ)) (T.image σ) = (nbrCouplingPMF n d v N) T := by
  have hcard_N : (N.image σ).card = N.card := Finset.card_image_of_injective N σ.injective
  have herase_im : (Finset.univ.erase v).image σ = Finset.univ.erase v := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨y, hyv, rfl⟩
      exact fun h ↦ hyv (σ.injective (h.trans hσv.symm))
    · intro hxv
      refine ⟨σ.symm x, fun h ↦ hxv ?_, σ.apply_symm_apply x⟩
      simpa [hσv] using congrArg σ h
  have hsdiff_im : Finset.univ.erase v \ N.image σ = (Finset.univ.erase v \ N).image σ := by
    rw [Finset.image_sdiff (Finset.univ.erase v) N σ.injective, herase_im]
  dsimp only [nbrCouplingPMF]
  by_cases h_ge : d ≤ N.card
  · simp only [hcard_N, h_ge, ↓reduceIte, PMF.map_apply]
    let ePerm : Finset (Fin n) ≃ Finset (Fin n) :=
      { toFun := fun E ↦ E.image σ
        invFun := fun E ↦ E.image σ.symm
        left_inv := fun E ↦ by
          ext x; simp
        right_inv := fun E ↦ by
          ext x; simp }
    rw [← ePerm.tsum_eq]
    refine tsum_congr fun E ↦ ?_
    simp only [ePerm, Equiv.coe_fn_mk]
    have hsdiff_eq : (T.image σ = N.image σ \ E.image σ) ↔ (T = N \ E) := by
      rw [← Finset.image_sdiff N E σ.injective]
      exact ⟨fun h ↦ by
          have := congrArg (fun S ↦ S.image σ.symm) h
          simpa [Finset.image_image] using this,
        fun h ↦ congrArg (fun S ↦ S.image σ) h⟩
    have hunif := uniformOfFinset_powersetCard_image_perm σ N (N.card - d)
      (Finset.powersetCard_nonempty.mpr (Nat.sub_le N.card d))
      (Finset.powersetCard_nonempty.mpr (by rw [hcard_N]; exact Nat.sub_le N.card d)) E
    by_cases hEq : T = N \ E
    · subst hEq
      simp only [Finset.image_sdiff N E σ.injective, ↓reduceIte]
      exact hunif
    · have hEq' : ¬ (T.image σ = N.image σ \ E.image σ) := mt hsdiff_eq.mp hEq
      simp only [hEq', hEq, ↓reduceIte]
  · simp only [hcard_N, h_ge, ↓reduceIte]
    by_cases hne : ((Finset.univ.erase v \ N).powersetCard (d - N.card)).Nonempty
    · have hne' :
          ((Finset.univ.erase v \ N.image σ).powersetCard (d - N.card)).Nonempty := by
        rwa [hsdiff_im, Finset.powersetCard_nonempty,
          Finset.card_image_of_injective _ σ.injective, ← Finset.powersetCard_nonempty]
      simp only [hne', hne, ↓reduceDIte, PMF.map_apply]
      let ePerm : Finset (Fin n) ≃ Finset (Fin n) :=
        { toFun := fun A ↦ A.image σ
          invFun := fun A ↦ A.image σ.symm
          left_inv := fun A ↦ by ext x; simp
          right_inv := fun A ↦ by ext x; simp }
      rw [← ePerm.tsum_eq]
      refine tsum_congr fun A ↦ ?_
      simp only [ePerm, Equiv.coe_fn_mk]
      have hunion_eq : (T.image σ = N.image σ ∪ A.image σ) ↔ (T = N ∪ A) := by
        rw [← Finset.image_union]
        exact ⟨fun h ↦ by
            have := congrArg (fun S ↦ S.image σ.symm) h
            simpa [Finset.image_image] using this,
          fun h ↦ congrArg (fun S ↦ S.image σ) h⟩
      have hunif :
          (PMF.uniformOfFinset
            ((Finset.univ.erase v \ N.image σ).powersetCard (d - N.card)) hne')
            (A.image σ) =
          (PMF.uniformOfFinset
            ((Finset.univ.erase v \ N).powersetCard (d - N.card)) hne) A := by
        have h1 := uniformOfFinset_powersetCard_image_perm σ (Finset.univ.erase v \ N)
          (d - N.card) hne (by rwa [← hsdiff_im]) A
        rw [PMF.uniformOfFinset_apply, PMF.uniformOfFinset_apply] at h1 ⊢
        rwa [hsdiff_im]
      by_cases hEq : T = N ∪ A
      · subst hEq
        simp only [Finset.image_union, ↓reduceIte]
        exact hunif
      · have hEq' : ¬ (T.image σ = N.image σ ∪ A.image σ) := mt hunion_eq.mp hEq
        simp only [hEq', hEq, ↓reduceIte]
    · have hne' :
          ¬ ((Finset.univ.erase v \ N.image σ).powersetCard (d - N.card)).Nonempty := by
        rwa [hsdiff_im, Finset.powersetCard_nonempty,
          Finset.card_image_of_injective _ σ.injective, ← Finset.powersetCard_nonempty]
      simp only [hne', hne, ↓reduceDIte, PMF.pure_apply]
      have hiff : T.image σ = N.image σ ↔ T = N :=
        ⟨fun h ↦ by
            have := congrArg (fun S ↦ S.image σ.symm) h
            simpa [Finset.image_image] using this,
          fun h ↦ congrArg (fun S ↦ S.image σ) h⟩
      by_cases hTN : T = N
      · subst hTN
        simp only [↓reduceIte]
      · have hTN' : ¬ (T.image σ = N.image σ) := mt hiff.mp hTN
        simp only [hTN', hTN, ↓reduceIte]

open Classical in
/-- Given two `d`-subsets `T₁, T₂` of `Finset.univ.erase v`, there is a permutation of `Fin n`
fixing `v` that maps `T₁` onto `T₂`. -/
lemma exists_perm_fixing_and_image_eq {n d : ℕ} {v : Fin n}
    {T₁ T₂ : Finset (Fin n)}
    (hT₁ : T₁ ∈ (Finset.univ.erase v).powersetCard d)
    (hT₂ : T₂ ∈ (Finset.univ.erase v).powersetCard d) :
    ∃ σ : Equiv.Perm (Fin n), σ v = v ∧ T₁.image σ = T₂ := by
  obtain ⟨hT₁_sub, hT₁_card⟩ := Finset.mem_powersetCard.mp hT₁
  obtain ⟨hT₂_sub, hT₂_card⟩ := Finset.mem_powersetCard.mp hT₂
  let R₁ : Finset (Fin n) := Finset.univ.erase v \ T₁
  let R₂ : Finset (Fin n) := Finset.univ.erase v \ T₂
  have hcard_T : Fintype.card T₁ = Fintype.card T₂ := by
    simp [hT₁_card, hT₂_card]
  have hcard_R : Fintype.card R₁ = Fintype.card R₂ := by
    rw [Fintype.card_coe, Fintype.card_coe]
    dsimp only [R₁, R₂]
    rw [Finset.card_sdiff_of_subset hT₁_sub, Finset.card_sdiff_of_subset hT₂_sub,
      hT₁_card, hT₂_card]
  let eT : T₁ ≃ T₂ := Fintype.equivOfCardEq hcard_T
  let eR : R₁ ≃ R₂ := Fintype.equivOfCardEq hcard_R
  have hmem_R₁ : ∀ x : Fin n, x ≠ v → x ∉ T₁ → x ∈ R₁ := fun x hxv hxT ↦
    Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩, hxT⟩
  have hmem_R₂ : ∀ x : Fin n, x ≠ v → x ∉ T₂ → x ∈ R₂ := fun x hxv hxT ↦
    Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩, hxT⟩
  let toF : Fin n → Fin n := fun x ↦
    if hxv : x = v then v
    else if hxT : x ∈ T₁ then (eT ⟨x, hxT⟩).1
    else (eR ⟨x, hmem_R₁ x hxv hxT⟩).1
  let invF : Fin n → Fin n := fun y ↦
    if hyv : y = v then v
    else if hyT : y ∈ T₂ then (eT.symm ⟨y, hyT⟩).1
    else (eR.symm ⟨y, hmem_R₂ y hyv hyT⟩).1
  let σ : Equiv.Perm (Fin n) :=
    { toFun := toF
      invFun := invF
      left_inv := fun x ↦ by
        by_cases hxv : x = v
        · simp [toF, invF, hxv]
        · by_cases hxT : x ∈ T₁
          · have hyT : (eT ⟨x, hxT⟩).1 ∈ T₂ := (eT ⟨x, hxT⟩).2
            have hyv : (eT ⟨x, hxT⟩).1 ≠ v := Finset.ne_of_mem_erase (hT₂_sub hyT)
            simp [toF, invF, hxv, hxT, hyv, hyT]
          · have hyR : (eR ⟨x, hmem_R₁ x hxv hxT⟩).1 ∈ R₂ := (eR ⟨x, hmem_R₁ x hxv hxT⟩).2
            have hyv : (eR ⟨x, hmem_R₁ x hxv hxT⟩).1 ≠ v :=
              Finset.ne_of_mem_erase ((Finset.mem_sdiff.mp hyR).1)
            have hyT : (eR ⟨x, hmem_R₁ x hxv hxT⟩).1 ∉ T₂ := (Finset.mem_sdiff.mp hyR).2
            simp [toF, invF, hxv, hxT, hyv, hyT]
      right_inv := fun y ↦ by
        by_cases hyv : y = v
        · simp [toF, invF, hyv]
        · by_cases hyT : y ∈ T₂
          · have hxT : (eT.symm ⟨y, hyT⟩).1 ∈ T₁ := (eT.symm ⟨y, hyT⟩).2
            have hxv : (eT.symm ⟨y, hyT⟩).1 ≠ v := Finset.ne_of_mem_erase (hT₁_sub hxT)
            simp [toF, invF, hyv, hyT, hxv, hxT]
          · have hxR : (eR.symm ⟨y, hmem_R₂ y hyv hyT⟩).1 ∈ R₁ :=
              (eR.symm ⟨y, hmem_R₂ y hyv hyT⟩).2
            have hxv : (eR.symm ⟨y, hmem_R₂ y hyv hyT⟩).1 ≠ v :=
              Finset.ne_of_mem_erase ((Finset.mem_sdiff.mp hxR).1)
            have hxT : (eR.symm ⟨y, hmem_R₂ y hyv hyT⟩).1 ∉ T₁ := (Finset.mem_sdiff.mp hxR).2
            simp [toF, invF, hyv, hyT, hxv, hxT] }
  refine ⟨σ, by simp [σ, toF], ?_⟩
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hxT, rfl⟩
    have hxv : x ≠ v := Finset.ne_of_mem_erase (hT₁_sub hxT)
    simp [σ, toF, hxv, hxT]
  · intro hyT
    refine ⟨(eT.symm ⟨y, hyT⟩).1, (eT.symm ⟨y, hyT⟩).2, ?_⟩
    have hxT : (eT.symm ⟨y, hyT⟩).1 ∈ T₁ := (eT.symm ⟨y, hyT⟩).2
    have hxv : (eT.symm ⟨y, hyT⟩).1 ≠ v := Finset.ne_of_mem_erase (hT₁_sub hxT)
    simp [σ, toF, hxv, hxT]

end SteinMethod
