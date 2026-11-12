/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Monotone.SubgraphMonotone

/-!
# Vertex Degree Distributions and Pairwise Covariances on $G(n, p)$
(`Formalization.PoissonSizeBias.Monotone.DegreeCovariance`)

Establishes monotonicity/antitonicity of `largeDegEdgeFn`/`smallDegEdgeFn`, exact binomial degree
laws, and pairwise degree-indicator covariances under `erdosRenyi n p` for Examples 4.11 and 4.12.
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-! ### Part 3: Degree Distributions and Pairwise Covariance under $G(n, p)$ -/

private lemma degree_mono_of_le {n : ℕ} {G₁ G₂ : SimpleGraph (Fin n)}
    (h : G₁ ≤ G₂) (v : Fin n) : G₁.degree v ≤ G₂.degree v := by
  rw [← G₁.card_neighborFinset_eq_degree, ← G₂.card_neighborFinset_eq_degree]
  refine Finset.card_le_card fun u hu ↦ ?_
  rw [SimpleGraph.mem_neighborFinset] at hu ⊢
  exact h hu

theorem monotone_largeDegEdgeFn {n : ℕ} (v : Fin n) (d : ℕ) :
    Monotone (largeDegEdgeFn v d) := by
  intro y₁ y₂ hy
  unfold largeDegEdgeFn
  have hdeg := degree_mono_of_le (graphOfNatEdgeVec_mono hy) v
  split_ifs with h1 h2
  · exact le_rfl
  · exact False.elim (h2 (le_trans h1 hdeg))
  · exact zero_le_one
  · exact le_rfl

theorem antitone_smallDegEdgeFn {n : ℕ} (v : Fin n) (d : ℕ) :
    Antitone (smallDegEdgeFn v d) := by
  intro y₁ y₂ hy
  unfold smallDegEdgeFn
  have hdeg := degree_mono_of_le (graphOfNatEdgeVec_mono hy) v
  by_cases h1 : (graphOfNatEdgeVec y₂).degree v ≤ d <;>
    by_cases h2 : (graphOfNatEdgeVec y₁).degree v ≤ d
  · simp only [h1, h2, ↓reduceIte, le_rfl]
  · exact False.elim (h2 (le_trans hdeg h1))
  · simp only [h1, h2, ↓reduceIte, zero_le_one]
  · simp only [h1, h2, ↓reduceIte, le_rfl]

@[simp]
theorem largeDegEdgeFn_edgeIndNat {n : ℕ} (v : Fin n) (d : ℕ) (G : SimpleGraph (Fin n)) :
    largeDegEdgeFn v d
      (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G) =
      if d ≤ G.degree v then 1 else 0 := by
  unfold largeDegEdgeFn
  rw [graphOfNatEdgeVec_edgeIndNat]

@[simp]
theorem smallDegEdgeFn_edgeIndNat {n : ℕ} (v : Fin n) (d : ℕ) (G : SimpleGraph (Fin n)) :
    smallDegEdgeFn v d
      (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G) =
      if G.degree v ≤ d then 1 else 0 := by
  unfold smallDegEdgeFn
  rw [graphOfNatEdgeVec_edgeIndNat]

/-- Embedding of a vertex subset `U` (not containing `v`) into `EdgePair n` via `u ↦ s(v, u)`. -/
private def edgeWith {n : ℕ} (v : Fin n) (U : Finset (Fin n)) (hvU : v ∉ U) :
    {u // u ∈ U} ↪ EdgePair n where
  toFun u := ⟨s(v, u.1), fun hd ↦ hvU ((Sym2.mk_isDiag_iff.mp hd) ▸ u.2)⟩
  inj' u₁ u₂ h := by
    apply Subtype.ext
    have h1 := Subtype.ext_iff.mp h
    dsimp at h1
    rw [Sym2.eq_iff] at h1
    rcases h1 with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · exfalso; exact hvU (h1 ▸ u₂.2)

/-- The set of potential edges between `v` and vertices in `U` (`v ∉ U`). -/
private def starEdgeSet {n : ℕ} (v : Fin n) (U : Finset (Fin n)) (hvU : v ∉ U) :
    Finset (EdgePair n) :=
  U.attach.map (edgeWith v U hvU)

private lemma card_starEdgeSet {n : ℕ} (v : Fin n) (U : Finset (Fin n)) (hvU : v ∉ U) :
    (starEdgeSet v U hvU).card = U.card := by
  simp [starEdgeSet]

private lemma mem_starEdgeSet_iff {n : ℕ} (v : Fin n) (U : Finset (Fin n)) (hvU : v ∉ U)
    (e : EdgePair n) :
    e ∈ starEdgeSet v U hvU ↔ ∃ u ∈ U, e.1 = s(v, u) := by
  simp only [starEdgeSet, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, edgeWith,
    Subtype.ext_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, h.symm⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, hu, h.symm⟩

private lemma disjoint_starEdgeSet {n : ℕ} (v : Fin n) {S₁ S₂ : Finset (Fin n)}
    (hv₁ : v ∉ S₁) (hv₂ : v ∉ S₂) (hdisj : Disjoint S₁ S₂) :
    Disjoint (starEdgeSet v S₁ hv₁) (starEdgeSet v S₂ hv₂) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rcases (mem_starEdgeSet_iff v S₁ hv₁ e).mp he₁ with ⟨u₁, hu₁, h1⟩
  rcases (mem_starEdgeSet_iff v S₂ hv₂ e).mp he₂ with ⟨u₂, hu₂, h2⟩
  have heq : s(v, u₁) = s(v, u₂) := h1.symm.trans h2
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨_, rfl⟩ | ⟨rfl, _⟩
  · exact Finset.disjoint_left.mp hdisj hu₁ hu₂
  · exact hv₂ hu₂

private lemma erdosRenyi_real_neighborFinset_inter_eq {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : Fin n) (U : Finset (Fin n)) (hvU : v ∉ U)
    {S : Finset (Fin n)} (hSU : S ⊆ U) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.neighborFinset v ∩ U = S} =
      p ^ S.card * (1 - p) ^ (U.card - S.card) := by
  have hvS : v ∉ S := fun h ↦ hvU (hSU h)
  have hvUS : v ∉ U \ S := fun h ↦ hvU (Finset.sdiff_subset h)
  have hdisj : Disjoint (starEdgeSet v S hvS) (starEdgeSet v (U \ S) hvUS) :=
    disjoint_starEdgeSet v hvS hvUS disjoint_sdiff_self_right
  have h_set : {G : SimpleGraph (Fin n) | G.neighborFinset v ∩ U = S} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ starEdgeSet v S hvS, e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ starEdgeSet v (U \ S) hvUS, e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hG
      refine ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩
      · rcases (mem_starEdgeSet_iff v S hvS e).mp he with ⟨u, hu, he_eq⟩
        have hu_mem : u ∈ G.neighborFinset v ∩ U := hG.symm ▸ hu
        have hadj : G.Adj v u := by simpa using (Finset.mem_inter.mp hu_mem).1
        rw [he_eq]
        exact hadj
      · rcases (mem_starEdgeSet_iff v (U \ S) hvUS e).mp he with ⟨u, hu, he_eq⟩
        rw [he_eq]
        intro hadj
        have hu_inter : u ∈ G.neighborFinset v ∩ U :=
          Finset.mem_inter.mpr ⟨by simpa using hadj, (Finset.mem_sdiff.mp hu).1⟩
        rw [hG] at hu_inter
        exact (Finset.mem_sdiff.mp hu).2 hu_inter
    · rintro ⟨hpos, hneg⟩
      ext u
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hadj, huU⟩
        by_contra huS
        have huUS : u ∈ U \ S := Finset.mem_sdiff.mpr ⟨huU, huS⟩
        let e : EdgePair n := edgeWith v (U \ S) hvUS ⟨u, huUS⟩
        have he : e ∈ starEdgeSet v (U \ S) hvUS :=
          Finset.mem_map.mpr ⟨⟨u, huUS⟩, Finset.mem_attach _ _, rfl⟩
        exact hneg e he hadj
      · intro huS
        refine ⟨?_, hSU huS⟩
        let e : EdgePair n := edgeWith v S hvS ⟨u, huS⟩
        have he : e ∈ starEdgeSet v S hvS :=
          Finset.mem_map.mpr ⟨⟨u, huS⟩, Finset.mem_attach _ _, rfl⟩
        exact hpos e he
  rw [h_set, erdosRenyi_real_cylinder hp0 hp1 _ _ hdisj, card_starEdgeSet, card_starEdgeSet,
    Finset.card_sdiff, Finset.inter_eq_left.mpr hSU]

private lemma erdosRenyi_real_card_neighborFinset_inter_eq {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : Fin n) (U : Finset (Fin n)) (hvU : v ∉ U) (k : ℕ) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | (G.neighborFinset v ∩ U).card = k} =
      (U.card.choose k : ℝ) * p ^ k * (1 - p) ^ (U.card - k) := by
  have h_union : {G : SimpleGraph (Fin n) | (G.neighborFinset v ∩ U).card = k} =
      ⋃ S ∈ U.powersetCard k, {G : SimpleGraph (Fin n) | G.neighborFinset v ∩ U = S} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_powersetCard]
    constructor
    · intro hk
      exact ⟨G.neighborFinset v ∩ U, ⟨Finset.inter_subset_right, hk⟩, rfl⟩
    · rintro ⟨S, ⟨_, rfl⟩, rfl⟩
      rfl
  have h_disj : Set.PairwiseDisjoint (U.powersetCard k : Set (Finset (Fin n)))
      (fun S ↦ {G : SimpleGraph (Fin n) | G.neighborFinset v ∩ U = S}) := by
    intro S₁ _ S₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro G h₁ h₂
    exact hne (h₁.symm.trans h₂)
  rw [h_union, measureReal_biUnion_finset h_disj (fun _ _ ↦ .of_discrete)]
  have h_each : ∀ S ∈ U.powersetCard k,
      (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.neighborFinset v ∩ U = S} =
        p ^ k * (1 - p) ^ (U.card - k) := by
    intro S hS
    rcases Finset.mem_powersetCard.mp hS with ⟨hSU, rfl⟩
    exact erdosRenyi_real_neighborFinset_inter_eq hp0 hp1 v U hvU hSU
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul,
    mul_assoc]

private lemma neighborFinset_inter_univ_erase {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.neighborFinset v ∩ Finset.univ.erase v = G.neighborFinset v := by
  ext u
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ,
    and_true, and_iff_left_iff_imp]
  intro hadj
  exact (G.ne_of_adj hadj).symm

private lemma erdosRenyi_real_degree_eq {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) (k : ℕ) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.degree v = k} =
      ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k) := by
  have h_eq : {G : SimpleGraph (Fin n) | G.degree v = k} =
      {G : SimpleGraph (Fin n) | (G.neighborFinset v ∩ Finset.univ.erase v).card = k} := by
    ext G
    simp only [Set.mem_ofPred_eq, neighborFinset_inter_univ_erase, G.card_neighborFinset_eq_degree]
  rw [h_eq, erdosRenyi_real_card_neighborFinset_inter_eq hp0 hp1 v (Finset.univ.erase v)
    (by simp) k]
  simp [Finset.card_erase_of_mem (Finset.mem_univ v)]

lemma erdosRenyi_real_degree_ge {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) (d : ℕ) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | d ≤ G.degree v} =
      ∑ k ∈ Finset.Ico d n, ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k) := by
  have h_union : {G : SimpleGraph (Fin n) | d ≤ G.degree v} =
      ⋃ k ∈ Finset.Ico d n, {G : SimpleGraph (Fin n) | G.degree v = k} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Ico]
    constructor
    · intro hle
      exact ⟨G.degree v, ⟨hle, by simpa using G.degree_lt_card_verts v⟩, rfl⟩
    · rintro ⟨k, ⟨hdk, _⟩, rfl⟩
      exact hdk
  have h_disj : Set.PairwiseDisjoint (Finset.Ico d n : Set ℕ)
      (fun k ↦ {G : SimpleGraph (Fin n) | G.degree v = k}) := by
    intro k₁ _ k₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro G h₁ h₂
    exact hne (h₁.symm.trans h₂)
  rw [h_union, measureReal_biUnion_finset h_disj (fun _ _ ↦ .of_discrete)]
  exact Finset.sum_congr rfl fun k _ ↦ erdosRenyi_real_degree_eq hp0 hp1 v k

lemma erdosRenyi_real_degree_le {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n) (d : ℕ) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.degree v ≤ d} =
      ∑ k ∈ Finset.range (d + 1), ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k) := by
  have h_union : {G : SimpleGraph (Fin n) | G.degree v ≤ d} =
      ⋃ k ∈ Finset.range (d + 1), {G : SimpleGraph (Fin n) | G.degree v = k} := by
    ext G
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
    exact ⟨fun h ↦ ⟨G.degree v, h, rfl⟩, fun ⟨k, hk, hG⟩ ↦ hG ▸ hk⟩
  have h_disj : Set.PairwiseDisjoint (Finset.range (d + 1) : Set ℕ)
      (fun k ↦ {G : SimpleGraph (Fin n) | G.degree v = k}) := by
    intro k₁ _ k₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro G h₁ h₂
    exact hne (h₁.symm.trans h₂)
  rw [h_union, measureReal_biUnion_finset h_disj (fun _ _ ↦ .of_discrete)]
  exact Finset.sum_congr rfl fun k _ ↦ erdosRenyi_real_degree_eq hp0 hp1 v k

/-! ### Part 4: Disjoint-Edge-Bit Independence and Bilinear Covariance Formula -/

private lemma erdosRenyi_indepFun_of_disjoint_edgeBits {n : ℕ} {p : ℝ}
    (E_A E_B : Finset (EdgePair n)) (hdisj : Disjoint E_A E_B)
    (g₁ : (E_A → Bool) → ℝ) (g₂ : (E_B → Bool) → ℝ) :
    IndepFun
      (fun G : SimpleGraph (Fin n) ↦ g₁ (fun e : E_A ↦ edgeBitsOfGraph G e.1))
      (fun G : SimpleGraph (Fin n) ↦ g₂ (fun e : E_B ↦ edgeBitsOfGraph G e.1))
      (erdosRenyi n p) := by
  let toBoolA : (E_A → ℝ) → (E_A → Bool) := fun z e ↦ decide (1 ≤ z e)
  let toBoolB : (E_B → ℝ) → (E_B → Bool) := fun z e ↦ decide (1 ≤ z e)
  have h_meas_decide : Measurable (fun t : ℝ ↦ decide (1 ≤ t)) := by
    have h_eq : (fun t : ℝ ↦ decide (1 ≤ t)) =
        fun t : ℝ ↦ if t ∈ Set.Ici (1 : ℝ) then true else false := by
      funext t
      by_cases h : 1 ≤ t <;> simp [h]
    rw [h_eq]
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hA : Measurable toBoolA :=
    measurable_pi_iff.mpr fun e ↦ h_meas_decide.comp (measurable_pi_apply e)
  have hB : Measurable toBoolB :=
    measurable_pi_iff.mpr fun e ↦ h_meas_decide.comp (measurable_pi_apply e)
  have hf : Measurable (g₁ ∘ toBoolA) := Measurable.of_discrete.comp hA
  have hg : Measurable (g₂ ∘ toBoolB) := Measurable.of_discrete.comp hB
  have h_ind := erdosRenyi_indepFun_of_disjoint_edges (n := n) (p := p) E_A E_B hdisj hf hg
  have h_eq_bit : ∀ (e : EdgePair n) (G : SimpleGraph (Fin n)),
      decide (1 ≤ edgeIndicator e G) = edgeBitsOfGraph G e := by
    intro e G
    unfold edgeIndicator edgeBitsOfGraph
    by_cases h : e.1 ∈ G.edgeSet <;> simp [h]
  simpa [toBoolA, toBoolB, Function.comp_def, h_eq_bit] using h_ind

/-- General bilinear covariance identity on a finite discrete probability space: if
$X_1 = A_1 + K B_1$ and $X_2 = A_2 + K B_2$ where $K \in \{0, 1\}$ and $(A_1, B_1)$, $(A_2, B_2)$,
$K$ have the required pairwise independences, then
$\mathrm{Cov}(X_1, X_2) = \mathbb{E}[K](1 - \mathbb{E}[K])\mathbb{E}[B_1]\mathbb{E}[B_2]$. -/
private lemma cov_bilinear_indicator {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [DiscreteMeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A₁ B₁ A₂ B₂ K : Ω → ℝ)
    (hK01 : ∀ ω : Ω, K ω = 0 ∨ K ω = 1)
    (hX₁ : Ω → ℝ) (hX₁_eq : ∀ ω, hX₁ ω = A₁ ω + K ω * B₁ ω)
    (hX₂ : Ω → ℝ) (hX₂_eq : ∀ ω, hX₂ ω = A₂ ω + K ω * B₂ ω)
    (hind_A1_A2 : IndepFun A₁ A₂ P)
    (hind_A1_KB2 : IndepFun A₁ (fun ω ↦ K ω * B₂ ω) P)
    (hind_KB1_A2 : IndepFun (fun ω ↦ K ω * B₁ ω) A₂ P)
    (hind_K_B1B2 : IndepFun K (fun ω ↦ B₁ ω * B₂ ω) P)
    (hind_K_B1 : IndepFun K B₁ P)
    (hind_K_B2 : IndepFun K B₂ P)
    (hind_B1_B2 : IndepFun B₁ B₂ P) :
    cov[hX₁, hX₂; P] =
      (∫ ω, K ω ∂P) * (1 - ∫ ω, K ω ∂P) *
        (∫ ω, B₁ ω ∂P) * (∫ ω, B₂ ω ∂P) := by
  have hmem₁ : MemLp hX₁ 2 P := MemLp.of_discrete
  have hmem₂ : MemLp hX₂ 2 P := MemLp.of_discrete
  rw [covariance_eq_sub hmem₁ hmem₂]
  have h_prod : (fun ω ↦ hX₁ ω * hX₂ ω) =
      fun ω ↦ (A₁ ω * A₂ ω + A₁ ω * (K ω * B₂ ω)) +
        ((K ω * B₁ ω) * A₂ ω + K ω * (B₁ ω * B₂ ω)) := by
    funext ω
    rw [hX₁_eq ω, hX₂_eq ω]
    have hK_sq : K ω * K ω = K ω := by
      rcases hK01 ω with h0 | h1
      · simp [h0]
      · simp [h1]
    calc (A₁ ω + K ω * B₁ ω) * (A₂ ω + K ω * B₂ ω)
      _ = (A₁ ω * A₂ ω + A₁ ω * (K ω * B₂ ω)) +
          ((K ω * B₁ ω) * A₂ ω + (K ω * K ω) * (B₁ ω * B₂ ω)) := by ring
      _ = (A₁ ω * A₂ ω + A₁ ω * (K ω * B₂ ω)) +
          ((K ω * B₁ ω) * A₂ ω + K ω * (B₁ ω * B₂ ω)) := by rw [hK_sq]
  have h_int_prod : ∫ ω, hX₁ ω * hX₂ ω ∂P =
      (∫ ω, A₁ ω ∂P) * (∫ ω, A₂ ω ∂P) +
      (∫ ω, A₁ ω ∂P) * ((∫ ω, K ω ∂P) * (∫ ω, B₂ ω ∂P)) +
      ((∫ ω, K ω ∂P) * (∫ ω, B₁ ω ∂P)) * (∫ ω, A₂ ω ∂P) +
      (∫ ω, K ω ∂P) * ((∫ ω, B₁ ω ∂P) * (∫ ω, B₂ ω ∂P)) := by
    rw [h_prod,
      integral_add Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,
      hind_A1_A2.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable,
      hind_A1_KB2.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable,
      hind_KB1_A2.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable,
      hind_K_B1B2.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable,
      hind_K_B1.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable,
      hind_K_B2.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable,
      hind_B1_B2.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable]
    ring
  have h_int_1 :
      ∫ ω, hX₁ ω ∂P =
        (∫ ω, A₁ ω ∂P) + (∫ ω, K ω ∂P) * (∫ ω, B₁ ω ∂P) := by
    have h1 : hX₁ = fun ω ↦ A₁ ω + K ω * B₁ ω := funext hX₁_eq
    rw [h1, integral_add Integrable.of_finite Integrable.of_finite,
      hind_K_B1.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable]
  have h_int_2 :
      ∫ ω, hX₂ ω ∂P =
        (∫ ω, A₂ ω ∂P) + (∫ ω, K ω ∂P) * (∫ ω, B₂ ω ∂P) := by
    have h2 : hX₂ = fun ω ↦ A₂ ω + K ω * B₂ ω := funext hX₂_eq
    rw [h2, integral_add Integrable.of_finite Integrable.of_finite,
      hind_K_B2.integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable]
  change ∫ ω, hX₁ ω * hX₂ ω ∂P - (∫ ω, hX₁ ω ∂P) * (∫ ω, hX₂ ω ∂P) = _
  rw [h_int_prod, h_int_1, h_int_2]
  ring

/-! ### Part 5: Pairwise Degree Indicator Covariances under $G(n, p)$ -/

private abbrev otherVertices {n : ℕ} (v₁ v₂ : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase v₁).erase v₂

private lemma not_mem_otherVertices_left {n : ℕ} (v₁ v₂ : Fin n) :
    v₁ ∉ otherVertices v₁ v₂ := by
  simp [otherVertices, Finset.mem_erase]

private lemma not_mem_otherVertices_right {n : ℕ} (v₁ v₂ : Fin n) :
    v₂ ∉ otherVertices v₁ v₂ := by
  simp [otherVertices, Finset.mem_erase]

private def starOtherEdges {n : ℕ} (v₁ v₂ : Fin n) : Finset (EdgePair n) :=
  starEdgeSet v₁ (otherVertices v₁ v₂) (not_mem_otherVertices_left v₁ v₂)

def pairEdge {n : ℕ} {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂) : EdgePair n :=
  ⟨s(v₁, v₂), fun hd ↦ h12 (Sym2.mk_isDiag_iff.mp hd)⟩

noncomputable def reducedDeg {n : ℕ} (v₁ v₂ : Fin n) (G : SimpleGraph (Fin n)) : ℕ :=
  (G.neighborFinset v₁ ∩ otherVertices v₁ v₂).card

private def reducedDegFromSub {n : ℕ} (v₁ v₂ : Fin n)
    {E : Finset (EdgePair n)} (hsub : starOtherEdges v₁ v₂ ⊆ E)
    (b : E → Bool) : ℕ :=
  ∑ u : {u // u ∈ otherVertices v₁ v₂},
    if b ⟨edgeWith v₁ (otherVertices v₁ v₂) (not_mem_otherVertices_left v₁ v₂) u,
      hsub (Finset.mem_map_of_mem _ (Finset.mem_attach _ u))⟩ then 1 else 0

private lemma reducedDegFromSub_eq {n : ℕ} (v₁ v₂ : Fin n)
    {E : Finset (EdgePair n)} (hsub : starOtherEdges v₁ v₂ ⊆ E)
    (G : SimpleGraph (Fin n)) :
    reducedDegFromSub v₁ v₂ hsub (fun e : E ↦ edgeBitsOfGraph G e.1) =
      reducedDeg v₁ v₂ G := by
  unfold reducedDegFromSub reducedDeg
  have h_sum : (∑ u : {u // u ∈ otherVertices v₁ v₂},
      if edgeBitsOfGraph G (edgeWith v₁ (otherVertices v₁ v₂)
        (not_mem_otherVertices_left v₁ v₂) u) = true then 1 else 0) =
      ∑ u ∈ otherVertices v₁ v₂, if u ∈ G.neighborFinset v₁ then 1 else 0 := by
    rw [← Finset.sum_attach (otherVertices v₁ v₂)
      (fun u ↦ if u ∈ G.neighborFinset v₁ then 1 else 0)]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    have h_iff : edgeBitsOfGraph G (edgeWith v₁ (otherVertices v₁ v₂)
        (not_mem_otherVertices_left v₁ v₂) u) = true ↔ u.1 ∈ G.neighborFinset v₁ := by
      dsimp [edgeWith, edgeBitsOfGraph]
      rw [decide_eq_true_iff, SimpleGraph.mem_neighborFinset]
      rfl
    by_cases h : u.1 ∈ G.neighborFinset v₁
    · simp only [h, h_iff.mpr h, ↓reduceIte]
    · have hbf : edgeBitsOfGraph G (edgeWith v₁ (otherVertices v₁ v₂)
          (not_mem_otherVertices_left v₁ v₂) u) = false :=
        Bool.eq_false_iff.mpr (mt h_iff.mp h)
      simp only [h, hbf, Bool.false_eq_true, ↓reduceIte]
  rw [h_sum, ← Finset.card_filter]
  congr 1
  ext u
  simp [Finset.mem_inter, Finset.mem_filter, and_comm]

private lemma disjoint_starOtherEdges_self {n : ℕ} {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂) :
    Disjoint (starOtherEdges v₁ v₂) (starOtherEdges v₂ v₁) := by
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rcases (mem_starEdgeSet_iff v₁ (otherVertices v₁ v₂)
    (not_mem_otherVertices_left v₁ v₂) e).mp he₁ with ⟨u₁, hu₁, h1⟩
  rcases (mem_starEdgeSet_iff v₂ (otherVertices v₂ v₁)
    (not_mem_otherVertices_left v₂ v₁) e).mp he₂ with ⟨u₂, hu₂, h2⟩
  have heq : s(v₁, u₁) = s(v₂, u₂) := h1.symm.trans h2
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h_eq, _⟩ | ⟨h_eq, _⟩
  · exact h12 h_eq
  · exact not_mem_otherVertices_right v₂ v₁ (h_eq ▸ hu₂)

private lemma disjoint_starOtherEdges_pairEdge_left
    {n : ℕ} {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂) :
    Disjoint (starOtherEdges v₁ v₂) {pairEdge h12} := by
  rw [Finset.disjoint_singleton_right]
  intro he
  rcases (mem_starEdgeSet_iff v₁ (otherVertices v₁ v₂)
    (not_mem_otherVertices_left v₁ v₂) (pairEdge h12)).mp he with ⟨u, hu, heq⟩
  dsimp [pairEdge] at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
  · rw [← h2] at hu
    exact not_mem_otherVertices_right v₁ v₂ hu
  · rw [← h1] at hu
    exact not_mem_otherVertices_left v₁ v₂ hu

private lemma disjoint_starOtherEdges_pairEdge_right
    {n : ℕ} {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂) :
    Disjoint (starOtherEdges v₂ v₁) {pairEdge h12} := by
  rw [Finset.disjoint_singleton_right]
  intro he
  rcases (mem_starEdgeSet_iff v₂ (otherVertices v₂ v₁)
    (not_mem_otherVertices_left v₂ v₁) (pairEdge h12)).mp he with ⟨u, hu, heq⟩
  dsimp [pairEdge] at heq
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h12 h1
  · rw [← h1] at hu
    exact not_mem_otherVertices_right v₂ v₁ hu

lemma cov_degree_bilinear {n : ℕ} {p : ℝ}
    {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂)
    (φ_A φ_B : ℕ → ℝ) (φ_K : Bool → ℝ)
    (hK01 : ∀ b : Bool, φ_K b = 0 ∨ φ_K b = 1)
    (X₁ X₂ : SimpleGraph (Fin n) → ℝ)
    (hX₁ : ∀ G, X₁ G = φ_A (reducedDeg v₁ v₂ G) +
      φ_K (edgeBitsOfGraph G (pairEdge h12)) * φ_B (reducedDeg v₁ v₂ G))
    (hX₂ : ∀ G, X₂ G = φ_A (reducedDeg v₂ v₁ G) +
      φ_K (edgeBitsOfGraph G (pairEdge h12)) * φ_B (reducedDeg v₂ v₁ G)) :
    cov[X₁, X₂; erdosRenyi n p] =
      (∫ G, φ_K (edgeBitsOfGraph G (pairEdge h12)) ∂(erdosRenyi n p)) *
      (1 - ∫ G, φ_K (edgeBitsOfGraph G (pairEdge h12)) ∂(erdosRenyi n p)) *
      (∫ G, φ_B (reducedDeg v₁ v₂ G) ∂(erdosRenyi n p)) *
      (∫ G, φ_B (reducedDeg v₂ v₁ G) ∂(erdosRenyi n p)) := by
  classical
  let E₁ := starOtherEdges v₁ v₂
  let E₂ := starOtherEdges v₂ v₁
  let E₁₂ : Finset (EdgePair n) := {pairEdge h12}
  have hd12 : Disjoint E₁ E₂ := disjoint_starOtherEdges_self h12
  have hd1_12 : Disjoint E₁ E₁₂ := disjoint_starOtherEdges_pairEdge_left h12
  have hd2_12 : Disjoint E₂ E₁₂ := disjoint_starOtherEdges_pairEdge_right h12
  have hd1_2u12 : Disjoint E₁ (E₁₂ ∪ E₂) :=
    Finset.disjoint_union_right.mpr ⟨hd1_12, hd12⟩
  have hd12u1_2 : Disjoint (E₁₂ ∪ E₁) E₂ :=
    Finset.disjoint_union_left.mpr ⟨hd2_12.symm, hd12⟩
  have hd12_1u2 : Disjoint E₁₂ (E₁ ∪ E₂) :=
    Finset.disjoint_union_right.mpr ⟨hd1_12.symm, hd2_12.symm⟩
  let A₁ : SimpleGraph (Fin n) → ℝ := fun G ↦ φ_A (reducedDeg v₁ v₂ G)
  let B₁ : SimpleGraph (Fin n) → ℝ := fun G ↦ φ_B (reducedDeg v₁ v₂ G)
  let A₂ : SimpleGraph (Fin n) → ℝ := fun G ↦ φ_A (reducedDeg v₂ v₁ G)
  let B₂ : SimpleGraph (Fin n) → ℝ := fun G ↦ φ_B (reducedDeg v₂ v₁ G)
  let K : SimpleGraph (Fin n) → ℝ := fun G ↦ φ_K (edgeBitsOfGraph G (pairEdge h12))
  have hA₁_sub : ∀ {E : Finset (EdgePair n)} (h : E₁ ⊆ E) (G : SimpleGraph (Fin n)),
      A₁ G = φ_A (reducedDegFromSub v₁ v₂ h (fun e : E ↦ edgeBitsOfGraph G e.1)) :=
    fun h G ↦ by rw [reducedDegFromSub_eq]
  have hB₁_sub : ∀ {E : Finset (EdgePair n)} (h : E₁ ⊆ E) (G : SimpleGraph (Fin n)),
      B₁ G = φ_B (reducedDegFromSub v₁ v₂ h (fun e : E ↦ edgeBitsOfGraph G e.1)) :=
    fun h G ↦ by rw [reducedDegFromSub_eq]
  have hA₂_sub : ∀ {E : Finset (EdgePair n)} (h : E₂ ⊆ E) (G : SimpleGraph (Fin n)),
      A₂ G = φ_A (reducedDegFromSub v₂ v₁ h (fun e : E ↦ edgeBitsOfGraph G e.1)) :=
    fun h G ↦ by rw [reducedDegFromSub_eq]
  have hB₂_sub : ∀ {E : Finset (EdgePair n)} (h : E₂ ⊆ E) (G : SimpleGraph (Fin n)),
      B₂ G = φ_B (reducedDegFromSub v₂ v₁ h (fun e : E ↦ edgeBitsOfGraph G e.1)) :=
    fun h G ↦ by rw [reducedDegFromSub_eq]
  have hK_sub : ∀ {E : Finset (EdgePair n)} (h : pairEdge h12 ∈ E) (G : SimpleGraph (Fin n)),
      K G = φ_K ((fun e : E ↦ edgeBitsOfGraph G e.1) ⟨pairEdge h12, h⟩) :=
    fun _ _ ↦ rfl
  refine cov_bilinear_indicator (erdosRenyi n p) A₁ B₁ A₂ B₂ K
    (fun G ↦ hK01 _) X₁ hX₁ X₂ hX₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `IndepFun A₁ A₂`
    simpa [← hA₁_sub Finset.Subset.rfl, ← hA₂_sub Finset.Subset.rfl] using
      erdosRenyi_indepFun_of_disjoint_edgeBits E₁ E₂ hd12
        (fun b ↦ φ_A (reducedDegFromSub v₁ v₂ Finset.Subset.rfl b))
        (fun b ↦ φ_A (reducedDegFromSub v₂ v₁ Finset.Subset.rfl b))
  · -- `IndepFun A₁ (K * B₂)`
    have h_mem : pairEdge h12 ∈ E₁₂ ∪ E₂ :=
      Finset.mem_union_left E₂ (Finset.mem_singleton_self _)
    have h_sub : E₂ ⊆ E₁₂ ∪ E₂ := Finset.subset_union_right
    have h_eq : (fun G ↦ K G * B₂ G) =
        fun G ↦ (fun b : (E₁₂ ∪ E₂ : Finset (EdgePair n)) → Bool ↦
          φ_K (b ⟨pairEdge h12, h_mem⟩) * φ_B (reducedDegFromSub v₂ v₁ h_sub b))
          (fun e ↦ edgeBitsOfGraph G e.1) := by
      funext G
      rw [hK_sub h_mem G, hB₂_sub h_sub G]
    rw [h_eq]
    simpa [← hA₁_sub Finset.Subset.rfl] using
      erdosRenyi_indepFun_of_disjoint_edgeBits E₁ (E₁₂ ∪ E₂) hd1_2u12
        (fun b ↦ φ_A (reducedDegFromSub v₁ v₂ Finset.Subset.rfl b))
        (fun b ↦ φ_K (b ⟨pairEdge h12, h_mem⟩) * φ_B (reducedDegFromSub v₂ v₁ h_sub b))
  · -- `IndepFun (K * B₁) A₂`
    have h_mem : pairEdge h12 ∈ E₁₂ ∪ E₁ :=
      Finset.mem_union_left E₁ (Finset.mem_singleton_self _)
    have h_sub : E₁ ⊆ E₁₂ ∪ E₁ := Finset.subset_union_right
    have h_eq : (fun G ↦ K G * B₁ G) =
        fun G ↦ (fun b : (E₁₂ ∪ E₁ : Finset (EdgePair n)) → Bool ↦
          φ_K (b ⟨pairEdge h12, h_mem⟩) * φ_B (reducedDegFromSub v₁ v₂ h_sub b))
          (fun e ↦ edgeBitsOfGraph G e.1) := by
      funext G
      rw [hK_sub h_mem G, hB₁_sub h_sub G]
    rw [h_eq]
    simpa [← hA₂_sub Finset.Subset.rfl] using
      erdosRenyi_indepFun_of_disjoint_edgeBits (E₁₂ ∪ E₁) E₂ hd12u1_2
        (fun b ↦ φ_K (b ⟨pairEdge h12, h_mem⟩) * φ_B (reducedDegFromSub v₁ v₂ h_sub b))
        (fun b ↦ φ_A (reducedDegFromSub v₂ v₁ Finset.Subset.rfl b))
  · -- `IndepFun K (B₁ * B₂)`
    have h_mem : pairEdge h12 ∈ E₁₂ := Finset.mem_singleton_self _
    have h_sub1 : E₁ ⊆ E₁ ∪ E₂ := Finset.subset_union_left
    have h_sub2 : E₂ ⊆ E₁ ∪ E₂ := Finset.subset_union_right
    have h_eq : (fun G ↦ B₁ G * B₂ G) =
        fun G ↦ (fun b : (E₁ ∪ E₂ : Finset (EdgePair n)) → Bool ↦
          φ_B (reducedDegFromSub v₁ v₂ h_sub1 b) * φ_B (reducedDegFromSub v₂ v₁ h_sub2 b))
          (fun e ↦ edgeBitsOfGraph G e.1) := by
      funext G
      rw [hB₁_sub h_sub1 G, hB₂_sub h_sub2 G]
    rw [h_eq]
    simpa [← hK_sub h_mem] using
      erdosRenyi_indepFun_of_disjoint_edgeBits E₁₂ (E₁ ∪ E₂) hd12_1u2
        (fun b ↦ φ_K (b ⟨pairEdge h12, h_mem⟩))
        (fun b ↦ φ_B (reducedDegFromSub v₁ v₂ h_sub1 b) *
          φ_B (reducedDegFromSub v₂ v₁ h_sub2 b))
  · -- `IndepFun K B₁`
    have h_mem : pairEdge h12 ∈ E₁₂ := Finset.mem_singleton_self _
    simpa [← hK_sub h_mem, ← hB₁_sub Finset.Subset.rfl] using
      erdosRenyi_indepFun_of_disjoint_edgeBits E₁₂ E₁ hd1_12.symm
        (fun b ↦ φ_K (b ⟨pairEdge h12, h_mem⟩))
        (fun b ↦ φ_B (reducedDegFromSub v₁ v₂ Finset.Subset.rfl b))
  · -- `IndepFun K B₂`
    have h_mem : pairEdge h12 ∈ E₁₂ := Finset.mem_singleton_self _
    simpa [← hK_sub h_mem, ← hB₂_sub Finset.Subset.rfl] using
      erdosRenyi_indepFun_of_disjoint_edgeBits E₁₂ E₂ hd2_12.symm
        (fun b ↦ φ_K (b ⟨pairEdge h12, h_mem⟩))
        (fun b ↦ φ_B (reducedDegFromSub v₂ v₁ Finset.Subset.rfl b))
  · -- `IndepFun B₁ B₂`
    simpa [← hB₁_sub Finset.Subset.rfl, ← hB₂_sub Finset.Subset.rfl] using
      erdosRenyi_indepFun_of_disjoint_edgeBits E₁ E₂ hd12
        (fun b ↦ φ_B (reducedDegFromSub v₁ v₂ Finset.Subset.rfl b))
        (fun b ↦ φ_B (reducedDegFromSub v₂ v₁ Finset.Subset.rfl b))

lemma degree_eq_reducedDeg_add_ite {n : ℕ} {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂)
    (G : SimpleGraph (Fin n)) :
    G.degree v₁ = reducedDeg v₁ v₂ G +
      if edgeBitsOfGraph G (pairEdge h12) = true then 1 else 0 := by
  rw [← G.card_neighborFinset_eq_degree, ← neighborFinset_inter_univ_erase G v₁]
  unfold reducedDeg otherVertices
  have h_bit : edgeBitsOfGraph G (pairEdge h12) = true ↔ G.Adj v₁ v₂ := by
    simp [pairEdge, SimpleGraph.mem_edgeSet]
  by_cases hadj : G.Adj v₁ v₂
  · simp only [h_bit.mpr hadj, ↓reduceIte]
    have hmem : v₂ ∈ G.neighborFinset v₁ ∩ Finset.univ.erase v₁ :=
      Finset.mem_inter.mpr ⟨by simpa using hadj,
        Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_univ v₂⟩⟩
    have h_inter : G.neighborFinset v₁ ∩ (Finset.univ.erase v₁).erase v₂ =
        (G.neighborFinset v₁ ∩ Finset.univ.erase v₁).erase v₂ := by
      ext u
      simp [Finset.mem_inter, Finset.mem_erase, and_left_comm]
    rw [h_inter, ← Finset.card_erase_add_one hmem]
  · have hbf : edgeBitsOfGraph G (pairEdge h12) = false :=
      Bool.eq_false_iff.mpr (mt h_bit.mp hadj)
    simp only [hbf, Bool.false_eq_true, ↓reduceIte, add_zero]
    congr 1
    ext u
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase,
      Finset.mem_univ, and_true]
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, ⟨fun h ↦ hadj (h ▸ h1), h2⟩⟩,
      fun ⟨h1, ⟨_, h2⟩⟩ ↦ ⟨h1, h2⟩⟩

lemma degree_right_eq_reducedDeg_add_ite {n : ℕ} {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂)
    (G : SimpleGraph (Fin n)) :
    G.degree v₂ = reducedDeg v₂ v₁ G +
      if edgeBitsOfGraph G (pairEdge h12) = true then 1 else 0 := by
  rw [degree_eq_reducedDeg_add_ite h12.symm G]
  have h_eq : pairEdge h12.symm = pairEdge h12 := by
    apply Subtype.ext
    dsimp [pairEdge]
    exact Sym2.eq_swap
  rw [h_eq]

lemma integral_pairEdge_indicator {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂) :
    ∫ G, (if edgeBitsOfGraph G (pairEdge h12) = true then (1 : ℝ) else 0)
      ∂(erdosRenyi n p) = p := by
  have h_ind : (fun G : SimpleGraph (Fin n) ↦
      if edgeBitsOfGraph G (pairEdge h12) = true then (1 : ℝ) else 0) =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ ({pairEdge h12} : Finset (EdgePair n)), e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)}.indicator 1 := by
    funext G
    by_cases h : (pairEdge h12).1 ∈ G.edgeSet <;> simp [h, edgeBitsOfGraph]
  rw [h_ind, integral_indicator_one .of_discrete,
    erdosRenyi_real_cylinder hp0 hp1 {pairEdge h12} ∅ (Finset.disjoint_empty_right _)]
  simp

lemma integral_reducedDeg_eq {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hn : 2 ≤ n) {v₁ v₂ : Fin n} (h12 : v₁ ≠ v₂) (k : ℕ) :
    ∫ G, (if reducedDeg v₁ v₂ G = k then (1 : ℝ) else 0) ∂(erdosRenyi n p) =
      ((n - 2).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 2 - k) := by
  have h_ind :
      (fun G : SimpleGraph (Fin n) ↦ if reducedDeg v₁ v₂ G = k then (1 : ℝ) else 0) =
      {G : SimpleGraph (Fin n) |
        (G.neighborFinset v₁ ∩ otherVertices v₁ v₂).card = k}.indicator 1 := by
    funext G
    unfold reducedDeg
    by_cases h : (G.neighborFinset v₁ ∩ otherVertices v₁ v₂).card = k <;> simp [h]
  have h_card : (otherVertices v₁ v₂).card = n - 2 := by
    unfold otherVertices
    have hv₂ : v₂ ∈ Finset.univ.erase v₁ :=
      Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_univ v₂⟩
    rw [Finset.card_erase_of_mem hv₂, Finset.card_erase_of_mem (Finset.mem_univ v₁),
      Finset.card_fin]
    omega
  rw [h_ind, integral_indicator_one .of_discrete,
    erdosRenyi_real_card_neighborFinset_inter_eq hp0 hp1 v₁ (otherVertices v₁ v₂)
      (not_mem_otherVertices_left v₁ v₂) k,
    h_card]

lemma variance_sum_const_diag_offDiag {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [DiscreteMeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (q c : ℝ)
    (hX_01 : ∀ (v : Fin n) (ω : Ω), X v ω = 0 ∨ X v ω = 1)
    (hX_mean : ∀ v : Fin n, ∫ ω, X v ω ∂P = q)
    (hX_cov : ∀ v₁ v₂ : Fin n, v₁ ≠ v₂ → cov[X v₁, X v₂; P] = c) :
    ProbabilityTheory.variance (fun ω ↦ ∑ v : Fin n, X v ω) P - (n : ℝ) * q +
      2 * (n : ℝ) * q ^ 2 =
      (n : ℝ) * ((n : ℝ) - 1) * c + (n : ℝ) * q ^ 2 := by
  have h_var_self : ∀ v : Fin n, ProbabilityTheory.variance (X v) P = q - q ^ 2 := by
    intro v
    have hmem : MemLp (X v) 2 P := MemLp.of_discrete
    rw [variance_eq_integral hmem.aemeasurable, hX_mean v]
    have h_pt : (fun ω ↦ (X v ω - q) ^ 2) =
        fun ω ↦ X v ω - 2 * q * X v ω + q ^ 2 := by
      funext ω
      have hsq : X v ω ^ 2 = X v ω := by
        rcases hX_01 v ω with h0 | h1
        · simp [h0]
        · simp [h1]
      calc (X v ω - q) ^ 2 = X v ω ^ 2 - 2 * q * X v ω + q ^ 2 := by ring
        _ = X v ω - 2 * q * X v ω + q ^ 2 := by rw [hsq]
    rw [h_pt, integral_add Integrable.of_finite (integrable_const _),
      integral_sub Integrable.of_finite Integrable.of_finite,
      integral_const_mul, hX_mean v, integral_const, probReal_univ, smul_eq_mul]
    ring
  have h_var_sum : ProbabilityTheory.variance (fun ω ↦ ∑ v : Fin n, X v ω) P =
      (n : ℝ) * (q - q ^ 2) + (n : ℝ) * ((n : ℝ) - 1) * c := by
    have h_eq : (fun ω ↦ ∑ v : Fin n, X v ω) = ∑ v : Fin n, X v := by
      funext ω; simp
    rw [h_eq, variance_sum (fun _ ↦ MemLp.of_discrete)]
    have h_split : ∀ v₁ : Fin n,
        (∑ v₂ : Fin n, cov[X v₁, X v₂; P]) =
          ProbabilityTheory.variance (X v₁) P +
            ∑ v₂ ∈ Finset.univ.erase v₁, cov[X v₁, X v₂; P] := by
      intro v₁
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v₁),
        covariance_self Measurable.of_discrete.aemeasurable]
    have h_diag :
        (∑ v : Fin n, ProbabilityTheory.variance (X v) P) = (n : ℝ) * (q - q ^ 2) := by
      simp_rw [h_var_self, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have h_off : (∑ v₁ : Fin n, ∑ v₂ ∈ Finset.univ.erase v₁, cov[X v₁, X v₂; P]) =
        (n : ℝ) * ((n : ℝ) - 1) * c := by
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · simp
      · have h_inner : ∀ v₁ : Fin n,
            (∑ v₂ ∈ Finset.univ.erase v₁, cov[X v₁, X v₂; P]) =
              ((n : ℝ) - 1) * c := by
          intro v₁
          have h_each : ∀ v₂ ∈ Finset.univ.erase v₁, cov[X v₁, X v₂; P] = c :=
            fun v₂ hv₂ ↦ hX_cov v₁ v₂ (Finset.ne_of_mem_erase hv₂).symm
          rw [Finset.sum_congr rfl h_each, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ v₁), Finset.card_fin, nsmul_eq_mul,
            Nat.cast_sub hn_pos, Nat.cast_one]
        simp_rw [h_inner, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_assoc]
    simp_rw [h_split, Finset.sum_add_distrib]
    rw [h_diag, h_off]
  rw [h_var_sum]
  ring

end SteinMethod
