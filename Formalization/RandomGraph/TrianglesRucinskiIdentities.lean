/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.RandomGraph.TrianglesRucinskiCoupling

/-!
# Combinatorial Increment and Cylinder Identities (`TrianglesRucinskiIdentities`)

Proves the deterministic triple-averaged and slice increment decompositions and cylinder indicator
identities for triangle counts under `G ↦ G ⊔ tripleGraph (rucTripleOf i)`
(`SteinIntro.tex:943-944`, `\cite{ruc88}`):

* `sum_triangles_sup_tripleGraph_sub`: $\sum_i (T(G \sqcup K_{t_i}) - T(G)) =
  (\binom{n}{3} - T(G)) + (n - 3) \sum_j \text{rucTwoEdgeInd } j\ G$.
* `triangles_sup_tripleGraph_sub_eq`: slice increment decomposition over `(rucTriNhbd i).erase i`.
* Cylinder indicator formulas `rucTwoEdgeTerm_mul_eq_indicator` and `rucSliceDiff_eq_indicator`,
  plus neighborhood overlap counts for variance and second-moment bounds.
-/

open MeasureTheory ProbabilityTheory Set

namespace SteinMethod

/-! ### 1. Two-Edge Indicators and Cylinder Products -/

/-- Single-missing-edge indicator term $(1 - \mathbf{1}_{e \in G}) \prod_{e' \in E \setminus \{e\}}
\mathbf{1}_{e' \in G}$ (`SteinIntro.tex:943-944`). -/
noncomputable def rucTwoEdgeTerm {n : ℕ} (E : Finset (EdgePair n)) (e : EdgePair n)
    (G : SimpleGraph (Fin n)) : ℝ :=
  (1 - edgeIndicator e G) * ∏ e' ∈ E.erase e, edgeIndicator e' G

/-- `{0, 1}`-valued indicator that the `i`-th triple induces **exact two edges** in `G`
(`SteinIntro.tex:943-944`). -/
noncomputable def rucTwoEdgeInd {n : ℕ} (i : Fin (n.choose 3)) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ e ∈ rucEdgesOfFinset (rucTripleOf i),
    rucTwoEdgeTerm (rucEdgesOfFinset (rucTripleOf i)) e G

lemma rucTwoEdgeTerm_eq_indicator {n : ℕ} (E : Finset (EdgePair n)) (e : EdgePair n)
    (G : SimpleGraph (Fin n)) :
    rucTwoEdgeTerm E e G =
      {H : SimpleGraph (Fin n) |
        (∀ e' ∈ E.erase e, e'.1 ∈ H.edgeSet) ∧ e.1 ∉ H.edgeSet}.indicator 1 G := by
  dsimp only [rucTwoEdgeTerm]
  by_cases he : e.1 ∈ G.edgeSet
  · have h1 : edgeIndicator e G = 1 := Set.indicator_of_mem he 1
    have hnot : G ∉ {H : SimpleGraph (Fin n) |
        (∀ e' ∈ E.erase e, e'.1 ∈ H.edgeSet) ∧ e.1 ∉ H.edgeSet} := fun h ↦ h.2 he
    rw [h1, sub_self, zero_mul, Set.indicator_of_notMem hnot]
  · have h0 : edgeIndicator e G = 0 := Set.indicator_of_notMem he 1
    by_cases hall : ∀ e' ∈ E.erase e, e'.1 ∈ G.edgeSet
    · have hprod : (∏ e' ∈ E.erase e, edgeIndicator e' G) = 1 :=
        Finset.prod_eq_one fun e' he' ↦ Set.indicator_of_mem (hall e' he') 1
      have hmem : G ∈ {H : SimpleGraph (Fin n) |
          (∀ e' ∈ E.erase e, e'.1 ∈ H.edgeSet) ∧ e.1 ∉ H.edgeSet} := ⟨hall, he⟩
      rw [h0, sub_zero, one_mul, hprod, Set.indicator_of_mem hmem, Pi.one_apply]
    · push Not at hall
      rcases hall with ⟨e', he', he'_not⟩
      have hprod : (∏ e'' ∈ E.erase e, edgeIndicator e'' G) = 0 :=
        Finset.prod_eq_zero he' (Set.indicator_of_notMem he'_not 1)
      have hnot : G ∉ {H : SimpleGraph (Fin n) |
          (∀ e'' ∈ E.erase e, e''.1 ∈ H.edgeSet) ∧ e.1 ∉ H.edgeSet} :=
        fun h ↦ he'_not (h.1 e' he')
      rw [hprod, mul_zero, Set.indicator_of_notMem hnot]

lemma rucTwoEdgeTerm_mul_eq_indicator {n : ℕ} (E₁ E₂ : Finset (EdgePair n))
    (e₁ e₂ : EdgePair n) (G : SimpleGraph (Fin n)) :
    rucTwoEdgeTerm E₁ e₁ G * rucTwoEdgeTerm E₂ e₂ G =
      {H : SimpleGraph (Fin n) |
        (∀ e ∈ E₁.erase e₁ ∪ E₂.erase e₂, e.1 ∈ H.edgeSet) ∧
          (∀ e ∈ ({e₁, e₂} : Finset (EdgePair n)), e.1 ∉ H.edgeSet)}.indicator 1 G := by
  rw [rucTwoEdgeTerm_eq_indicator, rucTwoEdgeTerm_eq_indicator]
  let A₁ : Set (SimpleGraph (Fin n)) :=
    {H | (∀ e' ∈ E₁.erase e₁, e'.1 ∈ H.edgeSet) ∧ e₁.1 ∉ H.edgeSet}
  let A₂ : Set (SimpleGraph (Fin n)) :=
    {H | (∀ e' ∈ E₂.erase e₂, e'.1 ∈ H.edgeSet) ∧ e₂.1 ∉ H.edgeSet}
  let A₁₂ : Set (SimpleGraph (Fin n)) :=
    {H | (∀ e ∈ E₁.erase e₁ ∪ E₂.erase e₂, e.1 ∈ H.edgeSet) ∧
      (∀ e ∈ ({e₁, e₂} : Finset (EdgePair n)), e.1 ∉ H.edgeSet)}
  have hiff : G ∈ A₁ ∧ G ∈ A₂ ↔ G ∈ A₁₂ := by
    simp only [A₁, A₂, A₁₂, mem_ofPred_eq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, hn1⟩, ⟨h2, hn2⟩⟩
      refine ⟨fun e he ↦ he.elim (h1 e) (h2 e), fun e he ↦ ?_⟩
      rcases he with rfl | rfl
      · exact hn1
      · exact hn2
    · rintro ⟨hall, hnone⟩
      exact ⟨⟨fun e he ↦ hall e (Or.inl he), hnone e₁ (Or.inl rfl)⟩,
        ⟨fun e he ↦ hall e (Or.inr he), hnone e₂ (Or.inr rfl)⟩⟩
  change A₁.indicator 1 G * A₂.indicator 1 G = A₁₂.indicator 1 G
  by_cases h1 : G ∈ A₁ <;> by_cases h2 : G ∈ A₂
  · have h12 : G ∈ A₁₂ := hiff.mp ⟨h1, h2⟩
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem h12]
    simp
  · have hn : G ∉ A₁₂ := fun h ↦ h2 (hiff.mpr h).2
    rw [Set.indicator_of_notMem h2, mul_zero, Set.indicator_of_notMem hn]
  · have hn : G ∉ A₁₂ := fun h ↦ h1 (hiff.mpr h).1
    rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem hn]
  · have hn : G ∉ A₁₂ := fun h ↦ h1 (hiff.mpr h).1
    rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem hn]

private lemma rucTwoEdgeInd_of_missing_finset {n : ℕ} (j : Fin (n.choose 3))
    (G : SimpleGraph (Fin n)) (M : Finset (EdgePair n))
    (hM : ∀ e, e ∈ M ↔ e ∈ rucEdgesOfFinset (rucTripleOf j) ∧ e.1 ∉ G.edgeSet) :
    (M.card = 0 → rucTwoEdgeInd j G = 0) ∧
    (M.card = 1 → rucTwoEdgeInd j G = 1) ∧
    (2 ≤ M.card → rucTwoEdgeInd j G = 0) := by
  classical
  let E_j := rucEdgesOfFinset (rucTripleOf j)
  have hterm : ∀ e ∈ E_j,
      rucTwoEdgeTerm E_j e G = if M = {e} then (1 : ℝ) else 0 := by
    intro e he
    rw [rucTwoEdgeTerm_eq_indicator]
    let A_e : Set (SimpleGraph (Fin n)) :=
      {H | (∀ e' ∈ E_j.erase e, e'.1 ∈ H.edgeSet) ∧ e.1 ∉ H.edgeSet}
    have hcond_iff : G ∈ A_e ↔ M = {e} := by
      simp only [A_e, mem_ofPred_eq]
      constructor
      · rintro ⟨hall, he_not⟩
        ext x
        rw [hM, Finset.mem_singleton]
        refine ⟨fun ⟨hxE, hx_not⟩ ↦ ?_, fun hx ↦ hx ▸ ⟨he, he_not⟩⟩
        by_contra hne
        exact hx_not (hall x (Finset.mem_erase.mpr ⟨hne, hxE⟩))
      · intro hMeq
        have heM : e ∈ M := hMeq ▸ Finset.mem_singleton_self e
        refine ⟨fun e' he' ↦ ?_, (hM e).mp heM |>.2⟩
        by_contra hnot
        have he'M : e' ∈ M := (hM e').mpr ⟨Finset.mem_of_mem_erase he', hnot⟩
        rw [hMeq, Finset.mem_singleton] at he'M
        exact (Finset.ne_of_mem_erase he') he'M
    change A_e.indicator 1 G = if M = {e} then (1 : ℝ) else 0
    by_cases hMeq : M = {e}
    · simp only [hMeq, ↓reduceIte]
      rw [Set.indicator_of_mem (hcond_iff.mpr hMeq), Pi.one_apply]
    · simp only [hMeq, ↓reduceIte]
      rw [Set.indicator_of_notMem (mt hcond_iff.mp hMeq)]
  have hsum : rucTwoEdgeInd j G = ∑ e ∈ E_j, if M = {e} then (1 : ℝ) else 0 :=
    Finset.sum_congr rfl hterm
  refine ⟨fun h0 ↦ ?_, fun h1 ↦ ?_, fun h2 ↦ ?_⟩
  · rw [hsum]
    refine Finset.sum_eq_zero fun e _ ↦ ?_
    have hne : M ≠ {e} := fun h ↦ by simp [h] at h0
    simp [hne]
  · obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp h1
    have he₀_mem : e₀ ∈ E_j := ((hM e₀).mp (he₀ ▸ Finset.mem_singleton_self e₀)).1
    rw [hsum, ← Finset.add_sum_erase E_j _ he₀_mem]
    have hrest : (∑ e ∈ E_j.erase e₀, if M = {e} then (1 : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero fun e he ↦ by
        have hne : M ≠ {e} := by
          rw [he₀]
          intro h
          exact (Finset.ne_of_mem_erase he) (Finset.singleton_injective h).symm
        simp [hne]
    rw [hrest, add_zero]
    simp [he₀]
  · rw [hsum]
    refine Finset.sum_eq_zero fun e _ ↦ ?_
    have hne : M ≠ {e} := fun h ↦ by rw [h, Finset.card_singleton] at h2; omega
    simp [hne]

lemma rucTwoEdgeInd_zo {n : ℕ} (j : Fin (n.choose 3)) (G : SimpleGraph (Fin n)) :
    rucTwoEdgeInd j G = 0 ∨ rucTwoEdgeInd j G = 1 := by
  classical
  let M := (rucEdgesOfFinset (rucTripleOf j)).filter fun e ↦ e.1 ∉ G.edgeSet
  obtain ⟨h0, h1, h2⟩ := rucTwoEdgeInd_of_missing_finset j G M (fun _ ↦ Finset.mem_filter)
  rcases eq_or_ne M.card 0 with hc0 | hc0
  · exact Or.inl (h0 hc0)
  · rcases eq_or_ne M.card 1 with hc1 | hc1
    · exact Or.inr (h1 hc1)
    · exact Or.inl (h2 (by omega))

lemma rucTwoEdgeInd_sq {n : ℕ} (j : Fin (n.choose 3)) (G : SimpleGraph (Fin n)) :
    rucTwoEdgeInd j G ^ 2 = rucTwoEdgeInd j G := by
  rcases rucTwoEdgeInd_zo j G with h | h <;> simp [h]

/-! ### 2. Exact Triple-Averaged Increment Identity -/

private lemma card_filter_rucTriples_superset_pair {n : ℕ} {pair : Finset (Fin n)}
    (hp : pair.card = 2) :
    ((rucTriples n).filter fun t ↦ pair ⊆ t).card = n - 2 := by
  let compl1 : Finset (Finset (Fin n)) := (Finset.univ \ pair).powersetCard 1
  have hbij : ((rucTriples n).filter fun t ↦ pair ⊆ t).card = compl1.card := by
    refine Finset.card_nbij' (fun t ↦ t \ pair) (fun s ↦ pair ∪ s) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, rucTriples, Finset.mem_powersetCard,
        Finset.subset_univ, true_and] at ht
      simp only [compl1, Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨fun x hx ↦ Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩, ?_⟩
      rw [Finset.card_sdiff_of_subset ht.2, ht.1, hp]
    · intro s hs
      simp only [compl1, Finset.mem_coe, Finset.mem_powersetCard] at hs
      have hdisj : Disjoint pair s := by
        rw [Finset.disjoint_left]
        intro x hxp hxs
        exact (Finset.mem_sdiff.mp (hs.1 hxs)).2 hxp
      simp only [Finset.mem_coe, Finset.mem_filter, rucTriples, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      exact ⟨by rw [Finset.card_union_of_disjoint hdisj, hp, hs.2], Finset.subset_union_left⟩
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter] at ht
      exact Finset.union_sdiff_of_subset ht.2
    · intro s hs
      simp only [compl1, Finset.mem_coe, Finset.mem_powersetCard] at hs
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun ⟨hxps, hxp⟩ ↦ hxps.elim (fun h ↦ (hxp h).elim) id,
        fun hxs ↦ ⟨Or.inr hxs, (Finset.mem_sdiff.mp (hs.1 hxs)).2⟩⟩
  rw [hbij]
  simp [compl1, Finset.card_sdiff_of_subset (Finset.subset_univ pair), hp]

private lemma card_triples_superset_edge {n : ℕ} (e : EdgePair n) :
    (Finset.univ.filter fun i : Fin (n.choose 3) ↦ e ∈ rucEdgesOfFinset (rucTripleOf i)).card =
      n - 2 := by
  rcases e with ⟨z, hne⟩
  revert hne
  refine Sym2.ind (fun u v hne ↦ ?_) z
  have huv : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hne
  let pair : Finset (Fin n) := {u, v}
  have he_iff : ∀ t : Finset (Fin n),
      (⟨s(u, v), hne⟩ : EdgePair n) ∈ rucEdgesOfFinset t ↔ pair ⊆ t := by
    intro t
    rw [mem_rucEdgesOfFinset]
    constructor
    · intro h x hx
      rcases Finset.mem_insert.mp hx with hxu | hx'
      · rw [hxu]
        exact h u (Sym2.mem_mk_left u v)
      · rw [Finset.mem_singleton.mp hx']
        exact h v (Sym2.mem_mk_right u v)
    · intro h w hw
      rcases Sym2.mem_iff.mp hw with hwu | hwv
      · rw [hwu]
        exact h (Finset.mem_insert_self u {v})
      · rw [hwv]
        exact h (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
  rw [← card_filter_rucTriples_superset_pair (Finset.card_pair huv)]
  refine Finset.card_bij (fun i _ ↦ rucTripleOf i) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨rucTripleOf_mem i,
      (he_iff _).mp (Finset.mem_filter.mp hi).2⟩
  · intro _ _ _ _ h
    exact rucTripleOf_injective h
  · intro t ht
    rcases Finset.mem_filter.mp ht with ⟨ht_mem, ht_sub⟩
    let i : Fin (n.choose 3) := (rucTripleEquiv n).symm ⟨t, ht_mem⟩
    have hi_eq : rucTripleOf i = t :=
      congrArg Subtype.val ((rucTripleEquiv n).apply_symm_apply ⟨t, ht_mem⟩)
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩, hi_eq⟩
    rwa [he_iff, hi_eq]

/-- Exact triple-averaged increment identity (`SteinIntro.tex:943-944`): summing
$T(G \sqcup K_{t_i}) - T(G)$ over all $\binom{n}{3}$ triples yields
$(\binom{n}{3} - T(G)) + (n - 3) \sum_j Z_j(G)$. -/
theorem sum_triangles_sup_tripleGraph_sub {n : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) :
    (∑ i : Fin (n.choose 3),
        ((((G ⊔ tripleGraph (rucTripleOf i)).cliqueSet 3).ncard : ℝ) -
          ((G.cliqueSet 3).ncard : ℝ))) =
      ((n.choose 3 : ℝ) - ((G.cliqueSet 3).ncard : ℝ)) +
        ((n : ℝ) - 3) * ∑ j : Fin (n.choose 3), rucTwoEdgeInd j G := by
  classical
  simp_rw [ncard_cliqueSet_three_eq_sum_rucTriInd, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have hper_j : ∀ j : Fin (n.choose 3),
      (∑ i : Fin (n.choose 3), (rucTriInd j (G ⊔ tripleGraph (rucTripleOf i)) - rucTriInd j G)) =
        (1 - rucTriInd j G) + ((n : ℝ) - 3) * rucTwoEdgeInd j G := by
    intro j
    let E_j := rucEdgesOfFinset (rucTripleOf j)
    let M := E_j.filter fun e ↦ e.1 ∉ G.edgeSet
    obtain ⟨hM0, hM1, hM2⟩ := rucTwoEdgeInd_of_missing_finset j G M (fun _ ↦ Finset.mem_filter)
    have hsup_iff : ∀ i : Fin (n.choose 3),
        (G ⊔ tripleGraph (rucTripleOf i)).IsNClique 3 (rucTripleOf j) ↔
          M ⊆ rucEdgesOfFinset (rucTripleOf i) := by
      intro i
      rw [isNClique_three_iff_rucEdges (card_rucTripleOf j)]
      simp_rw [mem_edgeSet_sup_tripleGraph]
      constructor
      · intro h e heM
        rcases Finset.mem_filter.mp heM with ⟨heE, henot⟩
        exact (h e heE).resolve_left henot
      · intro hsub e heE
        by_cases heG : e.1 ∈ G.edgeSet
        · exact Or.inl heG
        · exact Or.inr (hsub (Finset.mem_filter.mpr ⟨heE, heG⟩))
    rcases eq_or_ne M.card 0 with hc0 | hc_ne0
    · have hM_empty : M = ∅ := Finset.card_eq_zero.mp hc0
      have hG_cliq : G.IsNClique 3 (rucTripleOf j) := by
        rw [isNClique_three_iff_rucEdges (card_rucTripleOf j)]
        intro e heE
        by_contra hnot
        have : e ∈ M := Finset.mem_filter.mpr ⟨heE, hnot⟩
        simp [hM_empty] at this
      have h1 : rucTriInd j G = 1 := rucTriInd_of_isNClique hG_cliq
      have hall1 : ∀ i, rucTriInd j (G ⊔ tripleGraph (rucTripleOf i)) = 1 := fun i ↦
        rucTriInd_of_isNClique ((hsup_iff i).mpr (hM_empty ▸ Finset.empty_subset _))
      simp [h1, hall1, hM0 hc0]
    · have hnG_cliq : ¬ G.IsNClique 3 (rucTripleOf j) := by
        obtain ⟨e, heM⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc_ne0)
        rw [isNClique_three_iff_rucEdges (card_rucTripleOf j)]
        intro hall
        exact (Finset.mem_filter.mp heM).2 (hall e (Finset.mem_filter.mp heM).1)
      have h0 : rucTriInd j G = 0 := rucTriInd_of_not_isNClique hnG_cliq
      rcases eq_or_ne M.card 1 with hc1 | hc_ne1
      · obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp hc1
        have hsum_i :
            (∑ i : Fin (n.choose 3),
              (rucTriInd j (G ⊔ tripleGraph (rucTripleOf i)) - rucTriInd j G)) =
              ((Finset.univ.filter fun i : Fin (n.choose 3) ↦
                e₀ ∈ rucEdgesOfFinset (rucTripleOf i)).card : ℝ) := by
          simp_rw [h0, sub_zero, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
            Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hiff : (G ⊔ tripleGraph (rucTripleOf i)).IsNClique 3 (rucTripleOf j) ↔
              e₀ ∈ rucEdgesOfFinset (rucTripleOf i) := by
            rw [hsup_iff i, he₀, Finset.singleton_subset_iff]
          by_cases hi : e₀ ∈ rucEdgesOfFinset (rucTripleOf i)
          · simp only [hi, ↓reduceIte, rucTriInd_of_isNClique (hiff.mpr hi)]
          · simp only [hi, ↓reduceIte, rucTriInd_of_not_isNClique (mt hiff.mp hi)]
        rw [hsum_i, card_triples_superset_edge e₀, h0, hM1 hc1,
          Nat.cast_sub (by omega : 2 ≤ n)]
        push_cast
        ring
      · have hc2 : 2 ≤ M.card := by omega
        obtain ⟨e₁, he₁, e₂, he₂, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < M.card)
        have he₁_j : e₁ ∈ E_j := (Finset.mem_filter.mp he₁).1
        have he₂_j : e₂ ∈ E_j := (Finset.mem_filter.mp he₂).1
        have honly_j : ∀ i : Fin (n.choose 3),
            M ⊆ rucEdgesOfFinset (rucTripleOf i) ↔ i = j := by
          intro i
          refine ⟨fun hsub ↦ ?_, fun h ↦ h ▸ fun e heM ↦ (Finset.mem_filter.mp heM).1⟩
          have he₁_i : e₁ ∈ rucEdgesOfFinset (rucTripleOf i) := hsub he₁
          have he₂_i : e₂ ∈ rucEdgesOfFinset (rucTripleOf i) := hsub he₂
          by_contra hij
          have hinter_le2 : (rucTripleOf i ∩ rucTripleOf j).card ≤ 2 := by
            have hub : (rucTripleOf i ∩ rucTripleOf j).card ≤ 3 :=
              (Finset.card_le_card Finset.inter_subset_left).trans_eq (card_rucTripleOf i)
            by_contra hgt
            have h3 : (rucTripleOf i ∩ rucTripleOf j).card = 3 := by omega
            have hi_eq := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
              (by rw [card_rucTripleOf, h3])
            have hj_eq := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
              (by rw [card_rucTripleOf, h3])
            exact hij (rucTripleOf_injective (hi_eq.symm.trans hj_eq))
          have hcard_le1 : (rucEdgesOfFinset (rucTripleOf i ∩ rucTripleOf j)).card ≤ 1 := by
            rcases Nat.lt_or_eq_of_le hinter_le2 with hlt | heq2
            · rw [rucEdgesOfFinset_eq_empty_of_card_le_one (by omega), Finset.card_empty]
              omega
            · rw [card_rucEdgesOfFinset_of_card_eq_two heq2]
          have hpair_sub : ({e₁, e₂} : Finset (EdgePair n)) ⊆
              rucEdgesOfFinset (rucTripleOf i ∩ rucTripleOf j) := by
            rw [rucEdgesOfFinset_inter]
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx'
            · exact Finset.mem_inter.mpr ⟨he₁_i, he₁_j⟩
            · rw [Finset.mem_singleton.mp hx']
              exact Finset.mem_inter.mpr ⟨he₂_i, he₂_j⟩
          have h2le : 2 ≤ (rucEdgesOfFinset (rucTripleOf i ∩ rucTripleOf j)).card := by
            have := Finset.card_le_card hpair_sub
            rwa [Finset.card_pair hne12] at this
          omega
        have hsum_i :
            (∑ i : Fin (n.choose 3),
              (rucTriInd j (G ⊔ tripleGraph (rucTripleOf i)) - rucTriInd j G)) = 1 := by
          simp_rw [h0, sub_zero]
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
          have hj1 : rucTriInd j (G ⊔ tripleGraph (rucTripleOf j)) = 1 :=
            rucTriInd_of_isNClique (isNClique_three_sup_tripleGraph_self G j)
          have hrest : (∑ i ∈ Finset.univ.erase j,
              rucTriInd j (G ⊔ tripleGraph (rucTripleOf i))) = 0 :=
            Finset.sum_eq_zero fun i hi ↦ by
              have hnot : ¬ (G ⊔ tripleGraph (rucTripleOf i)).IsNClique 3 (rucTripleOf j) := by
                rw [hsup_iff i, honly_j i]
                exact Finset.ne_of_mem_erase hi
              exact rucTriInd_of_not_isNClique hnot
          linarith
        rw [hsum_i, h0, hM2 hc2]
        ring
  simp_rw [hper_j]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-! ### 3. Slice Increment Decomposition and Cylinder Characterization -/

/-- Change in triangle indicator `j` upon adding the edges of triple `i`
(`SteinIntro.tex:943-944`). -/
noncomputable def rucSliceDiff {n : ℕ} (i j : Fin (n.choose 3)) (G : SimpleGraph (Fin n)) : ℝ :=
  rucTriInd j (G ⊔ tripleGraph (rucTripleOf i)) - rucTriInd j G

/-- Exact slice decomposition (`SteinIntro.tex:943-944`): for each triple `i`,
$T(G \sqcup K_{t_i}) - T(G)$ decomposes into $(1 - Y_i(G))$ plus `rucSliceDiff i j G` over
`j ∈ (rucTriNhbd i).erase i`. -/
theorem triangles_sup_tripleGraph_sub_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (i : Fin (n.choose 3)) :
    (((G ⊔ tripleGraph (rucTripleOf i)).cliqueSet 3).ncard : ℝ) -
        ((G.cliqueSet 3).ncard : ℝ) =
      (1 - rucTriInd i G) +
        ∑ j ∈ (rucTriNhbd i).erase i, rucSliceDiff i j G := by
  simp_rw [ncard_cliqueSet_three_eq_sum_rucTriInd, ← Finset.sum_sub_distrib]
  have hzero_outside : ∀ j ∉ rucTriNhbd i,
      rucTriInd j (G ⊔ tripleGraph (rucTripleOf i)) - rucTriInd j G = 0 := by
    intro j hj
    have hle1 : (rucTripleOf i ∩ rucTripleOf j).card ≤ 1 := by
      rw [mem_rucTriNhbd] at hj; omega
    have hdisj_edges : rucEdgesOfFinset (rucTripleOf i) ∩ rucEdgesOfFinset (rucTripleOf j) = ∅ := by
      rw [← rucEdgesOfFinset_inter]
      exact rucEdgesOfFinset_eq_empty_of_card_le_one hle1
    have hiff : (G ⊔ tripleGraph (rucTripleOf i)).IsNClique 3 (rucTripleOf j) ↔
        G.IsNClique 3 (rucTripleOf j) := by
      rw [isNClique_three_iff_rucEdges (card_rucTripleOf j),
        isNClique_three_iff_rucEdges (card_rucTripleOf j)]
      refine forall₂_congr fun e he_j ↦ ?_
      rw [mem_edgeSet_sup_tripleGraph]
      have hnot_i : e ∉ rucEdgesOfFinset (rucTripleOf i) := fun he_i ↦ by
        have : e ∈ (∅ : Finset (EdgePair n)) := hdisj_edges ▸ Finset.mem_inter.mpr ⟨he_i, he_j⟩
        exact Finset.notMem_empty e this
      exact ⟨fun h ↦ h.resolve_right hnot_i, Or.inl⟩
    by_cases hG : G.IsNClique 3 (rucTripleOf j)
    · rw [rucTriInd_of_isNClique hG, rucTriInd_of_isNClique (hiff.mpr hG), sub_self]
    · rw [rucTriInd_of_not_isNClique hG, rucTriInd_of_not_isNClique (mt hiff.mp hG), sub_self]
  rw [← Finset.sum_subset (Finset.subset_univ (rucTriNhbd i)) fun j _ hj ↦ hzero_outside j hj,
    ← Finset.add_sum_erase (rucTriNhbd i) _ (self_mem_rucTriNhbd i)]
  rw [rucTriInd_of_isNClique (isNClique_three_sup_tripleGraph_self G i)]
  rfl

lemma card_inter_rucEdges_of_mem_erase {n : ℕ} {i j : Fin (n.choose 3)}
    (hj : j ∈ (rucTriNhbd i).erase i) :
    (rucEdgesOfFinset (rucTripleOf i) ∩ rucEdgesOfFinset (rucTripleOf j)).card = 1 := by
  rw [← rucEdgesOfFinset_inter]
  exact card_rucEdgesOfFinset_of_card_eq_two (mem_erase_rucTriNhbd_iff.mp hj)

lemma card_sdiff_rucEdges_of_mem_erase {n : ℕ} {i j : Fin (n.choose 3)}
    (hj : j ∈ (rucTriNhbd i).erase i) :
    (rucEdgesOfFinset (rucTripleOf j) \ rucEdgesOfFinset (rucTripleOf i)).card = 2 := by
  have hsum := Finset.card_sdiff_add_card_inter
    (rucEdgesOfFinset (rucTripleOf j)) (rucEdgesOfFinset (rucTripleOf i))
  rw [Finset.inter_comm, card_inter_rucEdges_of_mem_erase hj,
    card_rucEdgesOfFinset_of_card_eq_three (card_rucTripleOf j)] at hsum
  omega

lemma rucSliceDiff_eq_indicator {n : ℕ} {i j : Fin (n.choose 3)}
    (hj : j ∈ (rucTriNhbd i).erase i) (G : SimpleGraph (Fin n)) :
    rucSliceDiff i j G =
      {H : SimpleGraph (Fin n) |
        (∀ e ∈ rucEdgesOfFinset (rucTripleOf j) \ rucEdgesOfFinset (rucTripleOf i),
          e.1 ∈ H.edgeSet) ∧
        (∀ e ∈ rucEdgesOfFinset (rucTripleOf i) ∩ rucEdgesOfFinset (rucTripleOf j),
          e.1 ∉ H.edgeSet)}.indicator 1 G := by
  let E_i := rucEdgesOfFinset (rucTripleOf i)
  let E_j := rucEdgesOfFinset (rucTripleOf j)
  obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp (card_inter_rucEdges_of_mem_erase hj)
  have hsup_iff : (G ⊔ tripleGraph (rucTripleOf i)).IsNClique 3 (rucTripleOf j) ↔
      ∀ e ∈ E_j \ E_i, e.1 ∈ G.edgeSet := by
    rw [isNClique_three_iff_rucEdges (card_rucTripleOf j)]
    simp_rw [mem_edgeSet_sup_tripleGraph]
    constructor
    · intro h e he
      rcases Finset.mem_sdiff.mp he with ⟨he_j, he_ni⟩
      exact (h e he_j).resolve_right he_ni
    · intro h e he_j
      by_cases he_i : e ∈ E_i
      · exact Or.inr he_i
      · exact Or.inl (h e (Finset.mem_sdiff.mpr ⟨he_j, he_i⟩))
  have hG_iff : G.IsNClique 3 (rucTripleOf j) ↔
      (∀ e ∈ E_j \ E_i, e.1 ∈ G.edgeSet) ∧ e₀.1 ∈ G.edgeSet := by
    rw [isNClique_three_iff_rucEdges (card_rucTripleOf j)]
    have he₀_j : e₀ ∈ E_j := (Finset.mem_inter.mp (he₀ ▸ Finset.mem_singleton_self e₀)).2
    constructor
    · intro h
      exact ⟨fun e he ↦ h e (Finset.mem_sdiff.mp he).1, h e₀ he₀_j⟩
    · rintro ⟨hsdiff, he₀_in⟩ e he_j
      by_cases he_i : e ∈ E_i
      · have he_eq : e = e₀ := Finset.mem_singleton.mp (he₀ ▸ Finset.mem_inter.mpr ⟨he_i, he_j⟩)
        exact he_eq ▸ he₀_in
      · exact hsdiff e (Finset.mem_sdiff.mpr ⟨he_j, he_i⟩)
  have hneg_iff : (∀ e ∈ E_i ∩ E_j, e.1 ∉ G.edgeSet) ↔ e₀.1 ∉ G.edgeSet :=
    ⟨fun h ↦ h e₀ (he₀ ▸ Finset.mem_singleton_self e₀),
      fun hn e he ↦ Finset.mem_singleton.mp (he₀ ▸ he) ▸ hn⟩
  dsimp only [rucSliceDiff]
  by_cases hsdiff : ∀ e ∈ E_j \ E_i, e.1 ∈ G.edgeSet
  · rw [rucTriInd_of_isNClique (hsup_iff.mpr hsdiff)]
    by_cases he₀_in : e₀.1 ∈ G.edgeSet
    · have hnot : G ∉ {H : SimpleGraph (Fin n) |
          (∀ e ∈ E_j \ E_i, e.1 ∈ H.edgeSet) ∧ (∀ e ∈ E_i ∩ E_j, e.1 ∉ H.edgeSet)} :=
        fun h ↦ (hneg_iff.mp h.2) he₀_in
      rw [rucTriInd_of_isNClique (hG_iff.mpr ⟨hsdiff, he₀_in⟩), sub_self,
        Set.indicator_of_notMem hnot]
    · have hnotG : ¬ G.IsNClique 3 (rucTripleOf j) := fun h ↦ he₀_in (hG_iff.mp h).2
      have hmem : G ∈ {H : SimpleGraph (Fin n) |
          (∀ e ∈ E_j \ E_i, e.1 ∈ H.edgeSet) ∧ (∀ e ∈ E_i ∩ E_j, e.1 ∉ H.edgeSet)} :=
        ⟨hsdiff, hneg_iff.mpr he₀_in⟩
      rw [rucTriInd_of_not_isNClique hnotG, sub_zero, Set.indicator_of_mem hmem, Pi.one_apply]
  · have hnot_sup : ¬ (G ⊔ tripleGraph (rucTripleOf i)).IsNClique 3 (rucTripleOf j) :=
      mt hsup_iff.mp hsdiff
    have hnot_G : ¬ G.IsNClique 3 (rucTripleOf j) := fun h ↦ hsdiff (hG_iff.mp h).1
    have hnot : G ∉ {H : SimpleGraph (Fin n) |
        (∀ e ∈ E_j \ E_i, e.1 ∈ H.edgeSet) ∧ (∀ e ∈ E_i ∩ E_j, e.1 ∉ H.edgeSet)} :=
      fun h ↦ hsdiff h.1
    rw [rucTriInd_of_not_isNClique hnot_sup, rucTriInd_of_not_isNClique hnot_G, sub_self,
      Set.indicator_of_notMem hnot]

lemma rucSliceDiff_mul_eq_indicator {n : ℕ} {i j₁ j₂ : Fin (n.choose 3)}
    (hj₁ : j₁ ∈ (rucTriNhbd i).erase i) (hj₂ : j₂ ∈ (rucTriNhbd i).erase i)
    (G : SimpleGraph (Fin n)) :
    rucSliceDiff i j₁ G * rucSliceDiff i j₂ G =
      {H : SimpleGraph (Fin n) |
        (∀ e ∈ (rucEdgesOfFinset (rucTripleOf j₁) \ rucEdgesOfFinset (rucTripleOf i)) ∪
            (rucEdgesOfFinset (rucTripleOf j₂) \ rucEdgesOfFinset (rucTripleOf i)),
          e.1 ∈ H.edgeSet) ∧
        (∀ e ∈ (rucEdgesOfFinset (rucTripleOf i) ∩ rucEdgesOfFinset (rucTripleOf j₁)) ∪
            (rucEdgesOfFinset (rucTripleOf i) ∩ rucEdgesOfFinset (rucTripleOf j₂)),
          e.1 ∉ H.edgeSet)}.indicator 1 G := by
  rw [rucSliceDiff_eq_indicator hj₁, rucSliceDiff_eq_indicator hj₂]
  let P₁ := rucEdgesOfFinset (rucTripleOf j₁) \ rucEdgesOfFinset (rucTripleOf i)
  let P₂ := rucEdgesOfFinset (rucTripleOf j₂) \ rucEdgesOfFinset (rucTripleOf i)
  let N₁ := rucEdgesOfFinset (rucTripleOf i) ∩ rucEdgesOfFinset (rucTripleOf j₁)
  let N₂ := rucEdgesOfFinset (rucTripleOf i) ∩ rucEdgesOfFinset (rucTripleOf j₂)
  let A₁ : Set (SimpleGraph (Fin n)) :=
    {H | (∀ e ∈ P₁, e.1 ∈ H.edgeSet) ∧ (∀ e ∈ N₁, e.1 ∉ H.edgeSet)}
  let A₂ : Set (SimpleGraph (Fin n)) :=
    {H | (∀ e ∈ P₂, e.1 ∈ H.edgeSet) ∧ (∀ e ∈ N₂, e.1 ∉ H.edgeSet)}
  let A₁₂ : Set (SimpleGraph (Fin n)) :=
    {H | (∀ e ∈ P₁ ∪ P₂, e.1 ∈ H.edgeSet) ∧ (∀ e ∈ N₁ ∪ N₂, e.1 ∉ H.edgeSet)}
  have hiff : G ∈ A₁ ∧ G ∈ A₂ ↔ G ∈ A₁₂ := by
    simp only [A₁, A₂, A₁₂, mem_ofPred_eq, Finset.mem_union]
    exact ⟨fun ⟨⟨h1, hn1⟩, ⟨h2, hn2⟩⟩ ↦
        ⟨fun e he ↦ he.elim (h1 e) (h2 e), fun e he ↦ he.elim (hn1 e) (hn2 e)⟩,
      fun ⟨hp, hn⟩ ↦
        ⟨⟨fun e he ↦ hp e (Or.inl he), fun e he ↦ hn e (Or.inl he)⟩,
          ⟨fun e he ↦ hp e (Or.inr he), fun e he ↦ hn e (Or.inr he)⟩⟩⟩
  change A₁.indicator 1 G * A₂.indicator 1 G = A₁₂.indicator 1 G
  by_cases h1 : G ∈ A₁ <;> by_cases h2 : G ∈ A₂
  · have h12 : G ∈ A₁₂ := hiff.mp ⟨h1, h2⟩
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_mem h12]
    simp
  · have hn : G ∉ A₁₂ := fun h ↦ h2 (hiff.mpr h).2
    rw [Set.indicator_of_notMem h2, mul_zero, Set.indicator_of_notMem hn]
  · have hn : G ∉ A₁₂ := fun h ↦ h1 (hiff.mpr h).1
    rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem hn]
  · have hn : G ∉ A₁₂ := fun h ↦ h1 (hiff.mpr h).1
    rw [Set.indicator_of_notMem h1, zero_mul, Set.indicator_of_notMem hn]

lemma disjoint_sdiff_rucEdges_of_sdiff_ne {n : ℕ} {i j₁ j₂ : Fin (n.choose 3)}
    (hj₁ : j₁ ∈ (rucTriNhbd i).erase i) (hj₂ : j₂ ∈ (rucTriNhbd i).erase i)
    (hne : rucTripleOf j₁ \ rucTripleOf i ≠ rucTripleOf j₂ \ rucTripleOf i) :
    Disjoint (rucEdgesOfFinset (rucTripleOf j₁) \ rucEdgesOfFinset (rucTripleOf i))
      (rucEdgesOfFinset (rucTripleOf j₂) \ rucEdgesOfFinset (rucTripleOf i)) := by
  have hc₁ : (rucTripleOf j₁ \ rucTripleOf i).card = 1 := by
    have hsum := Finset.card_sdiff_add_card_inter (rucTripleOf j₁) (rucTripleOf i)
    rw [Finset.inter_comm, mem_erase_rucTriNhbd_iff.mp hj₁, card_rucTripleOf j₁] at hsum
    omega
  have hc₂ : (rucTripleOf j₂ \ rucTripleOf i).card = 1 := by
    have hsum := Finset.card_sdiff_add_card_inter (rucTripleOf j₂) (rucTripleOf i)
    rw [Finset.inter_comm, mem_erase_rucTriNhbd_iff.mp hj₂, card_rucTripleOf j₂] at hsum
    omega
  obtain ⟨v₁, hv₁⟩ := Finset.card_eq_one.mp hc₁
  obtain ⟨v₂, hv₂⟩ := Finset.card_eq_one.mp hc₂
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  rcases Finset.mem_sdiff.mp he₁ with ⟨hej₁, heni⟩
  have hex_not : ∃ v ∈ e.1, v ∉ rucTripleOf i := by
    by_contra! hall
    exact heni (mem_rucEdgesOfFinset.mpr hall)
  rcases hex_not with ⟨v, hve, hvni⟩
  have hv_in1 : v ∈ rucTripleOf j₁ \ rucTripleOf i :=
    Finset.mem_sdiff.mpr ⟨mem_rucEdgesOfFinset.mp hej₁ v hve, hvni⟩
  have hv_in2 : v ∈ rucTripleOf j₂ \ rucTripleOf i :=
    Finset.mem_sdiff.mpr ⟨mem_rucEdgesOfFinset.mp (Finset.mem_sdiff.mp he₂).1 v hve, hvni⟩
  have hv_eq1 : v = v₁ := Finset.mem_singleton.mp (hv₁ ▸ hv_in1)
  have hv_eq2 : v = v₂ := Finset.mem_singleton.mp (hv₂ ▸ hv_in2)
  exact hne (hv₁.trans (hv_eq1.symm.trans hv_eq2 ▸ hv₂.symm))

lemma card_filter_same_sdiff_le_four {n : ℕ} {i j₁ : Fin (n.choose 3)}
    (hj₁ : j₁ ∈ (rucTriNhbd i).erase i) :
    (((rucTriNhbd i).erase i).filter fun j₂ ↦
      rucTripleOf j₂ \ rucTripleOf i = rucTripleOf j₁ \ rucTripleOf i).card ≤ 4 := by
  let U : Finset (Fin n) := rucTripleOf i ∪ (rucTripleOf j₁ \ rucTripleOf i)
  have hc₁ : (rucTripleOf j₁ \ rucTripleOf i).card = 1 := by
    have hsum := Finset.card_sdiff_add_card_inter (rucTripleOf j₁) (rucTripleOf i)
    rw [Finset.inter_comm, mem_erase_rucTriNhbd_iff.mp hj₁, card_rucTripleOf j₁] at hsum
    omega
  have hU_card : U.card = 4 := by
    rw [Finset.card_union_of_disjoint Finset.disjoint_sdiff, card_rucTripleOf i, hc₁]
  have hpow_card : (U.powersetCard 3).card = 4 := by
    rw [Finset.card_powersetCard, hU_card]
    rfl
  rw [← hpow_card]
  refine Finset.card_le_card_of_injOn rucTripleOf ?_ fun _ _ _ _ h ↦ rucTripleOf_injective h
  intro j₂ hj₂
  have heq : rucTripleOf j₂ \ rucTripleOf i = rucTripleOf j₁ \ rucTripleOf i :=
    (Finset.mem_filter.mp (Finset.mem_coe.mp hj₂)).2
  simp only [Finset.mem_coe, Finset.mem_powersetCard]
  refine ⟨fun x hx ↦ ?_, card_rucTripleOf j₂⟩
  by_cases hxi : x ∈ rucTripleOf i
  · exact Finset.mem_union_left _ hxi
  · exact Finset.mem_union_right _ (heq ▸ Finset.mem_sdiff.mpr ⟨hx, hxi⟩)

end SteinMethod
