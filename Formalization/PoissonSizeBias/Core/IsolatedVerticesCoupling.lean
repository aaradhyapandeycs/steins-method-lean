/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Core.Exchangeable
import Formalization.RandomGraph.IsolatedCoupling
import Formalization.RandomGraph.IsolatedMoments

/-!
# Isolated-Vertex Deletion Coupling (`Formalization.PoissonSizeBias.Core.IsolatedVerticesCoupling`)

Vertex-permutation invariance of `erdosRenyi n p` (`permGraph`, `erdosRenyi_map_permGraph`,
`isExchangeableTuple_of_permGraph_invariant`) and the Example 4.5 vertex-deletion coupling and
$L^1$ increment identities (`isolatedVertices_coupling`, `\label{ex122}`,
`SteinIntro.tex:2189-2207`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Vertex-permutation action on `SimpleGraph (Fin n)` and invariance of `erdosRenyi n p` -/

/-- Pushforward of `G : SimpleGraph (Fin n)` along a vertex permutation `σ : Equiv.Perm (Fin n)`:
`u` and `v` are adjacent in `permGraph σ G` iff `σ.symm u` and `σ.symm v` are adjacent in `G`. -/
def permGraph {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := G.Adj (σ.symm u) (σ.symm v)
  symm := ⟨fun _ _ h ↦ G.adj_symm h⟩
  loopless := ⟨fun _ h ↦ G.loopless.irrefl _ h⟩

@[simp]
theorem permGraph_adj {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (permGraph σ G).Adj u v ↔ G.Adj (σ.symm u) (σ.symm v) :=
  Iff.rfl

@[simp]
theorem permGraph_refl {n : ℕ} (G : SimpleGraph (Fin n)) :
    permGraph (Equiv.refl (Fin n)) G = G := by
  ext u v
  rfl

@[simp]
theorem permGraph_trans {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    permGraph τ (permGraph σ G) = permGraph (σ.trans τ) G := by
  ext u v
  rfl

@[simp]
theorem permGraph_symm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    permGraph σ.symm (permGraph σ G) = G := by
  ext u v
  simp [permGraph]

@[simp]
theorem permGraph_apply_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    permGraph σ (permGraph σ.symm G) = G := by
  ext u v
  simp [permGraph]

theorem permGraph_neighborSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n))
    (i : Fin n) :
    (permGraph σ G).neighborSet (σ i) = σ '' G.neighborSet i := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, permGraph_adj, Equiv.symm_apply_apply, Set.mem_image]
  constructor
  · intro h
    exact ⟨σ.symm w, h, σ.apply_symm_apply w⟩
  · rintro ⟨u, hu, rfl⟩
    simpa using hu

theorem permGraph_ncard_neighborSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n))
    (i : Fin n) :
    ((permGraph σ G).neighborSet (σ i)).ncard = (G.neighborSet i).ncard := by
  rw [permGraph_neighborSet, Set.ncard_image_of_injective _ σ.injective]

theorem permGraph_isIsolated_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n))
    (i : Fin n) :
    (permGraph σ G).IsIsolated (σ i) ↔ G.IsIsolated i := by
  constructor
  · intro h w hw
    exact h (σ w) (by simpa [permGraph] using hw)
  · intro h w hw
    simp only [permGraph_adj, Equiv.symm_apply_apply] at hw
    exact h (σ.symm w) hw

private def permEdgePair {n : ℕ} (σ : Equiv.Perm (Fin n)) : EdgePair n ≃ EdgePair n where
  toFun e := ⟨Sym2.map σ e.1, by
    rcases e with ⟨z, hz⟩
    refine Sym2.ind (fun u v huv ↦ ?_) z hz
    rw [Sym2.mk_isDiag_iff] at huv
    change ¬ (s(σ u, σ v)).IsDiag
    rw [Sym2.mk_isDiag_iff]
    exact σ.injective.ne huv⟩
  invFun e := ⟨Sym2.map σ.symm e.1, by
    rcases e with ⟨z, hz⟩
    refine Sym2.ind (fun u v huv ↦ ?_) z hz
    rw [Sym2.mk_isDiag_iff] at huv
    change ¬ (s(σ.symm u, σ.symm v)).IsDiag
    rw [Sym2.mk_isDiag_iff]
    exact σ.symm.injective.ne huv⟩
  left_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv e := by
    apply Subtype.ext
    simp [Sym2.map_map]

private lemma mem_permGraph_edgeSet_iff {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) (e : EdgePair n) :
    e.1 ∈ (permGraph σ G).edgeSet ↔ (permEdgePair σ.symm e).1 ∈ G.edgeSet := by
  rcases e with ⟨z, hz⟩
  refine Sym2.ind (fun u v _ ↦ ?_) z hz
  simp [permEdgePair, SimpleGraph.mem_edgeSet, permGraph_adj]

private lemma singleton_graph_eq_cylinder {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidablePred fun e : EdgePair n ↦ e.1 ∈ H.edgeSet] :
    ({H} : Set (SimpleGraph (Fin n))) =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∈ H.edgeSet), e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∉ H.edgeSet), e.1 ∉ G.edgeSet)} := by
  ext G
  simp only [Set.mem_singleton_iff, Set.mem_ofPred, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl
    exact ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  · rintro ⟨hpos, hneg⟩
    ext u v
    by_cases huv : u = v
    · subst huv
      simp [SimpleGraph.irrefl]
    · let e : EdgePair n := ⟨s(u, v), by rwa [Sym2.mk_isDiag_iff]⟩
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet]
      change e.1 ∈ G.edgeSet ↔ e.1 ∈ H.edgeSet
      by_cases hmem : e.1 ∈ H.edgeSet
      · exact iff_of_true (hpos e hmem) hmem
      · exact iff_of_false (hneg e hmem) hmem

/-- `erdosRenyi n p` (`0 ≤ p ≤ 1`) is invariant under every vertex permutation `σ`. -/
theorem erdosRenyi_map_permGraph {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Equiv.Perm (Fin n)) :
    (erdosRenyi n p).map (permGraph σ) = erdosRenyi n p := by
  classical
  have hmeas : Measurable (permGraph σ) := measurable_of_finite _
  refine Measure.ext_of_singleton fun H ↦ ?_
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top ((erdosRenyi n p).map (permGraph σ)) {H})
    (measure_ne_top (erdosRenyi n p) {H})).mp ?_
  rw [map_measureReal_apply hmeas (measurableSet_singleton H)]
  have hpre : permGraph σ ⁻¹' ({H} : Set (SimpleGraph (Fin n))) = {permGraph σ.symm H} := by
    ext G
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ by simpa using congrArg (permGraph σ.symm) h,
      fun h ↦ by simpa using congrArg (permGraph σ) h⟩
  let H' := permGraph σ.symm H
  let S_pos : Finset (EdgePair n) := Finset.univ.filter fun e ↦ e.1 ∈ H.edgeSet
  let S_neg : Finset (EdgePair n) := Finset.univ.filter fun e ↦ e.1 ∉ H.edgeSet
  let S'_pos : Finset (EdgePair n) := Finset.univ.filter fun e ↦ e.1 ∈ H'.edgeSet
  let S'_neg : Finset (EdgePair n) := Finset.univ.filter fun e ↦ e.1 ∉ H'.edgeSet
  have hdisj : Disjoint S_pos S_neg := Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ h2 h1
  have hdisj' : Disjoint S'_pos S'_neg := Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ h2 h1
  have hcard_pos : S'_pos.card = S_pos.card := by
    refine Finset.card_bij (fun e _ ↦ permEdgePair σ e)
      (fun e he ↦ ?_)
      (fun e₁ _ e₂ _ h ↦ (permEdgePair σ).injective h)
      (fun e he ↦ ⟨permEdgePair σ.symm e, ?_, (permEdgePair σ).right_inv e⟩)
    · simp only [S'_pos, S_pos, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      have hiff := mem_permGraph_edgeSet_iff σ.symm H e
      simpa [H'] using hiff.mp he
    · simp only [S'_pos, S_pos, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      have hiff := mem_permGraph_edgeSet_iff σ.symm H (permEdgePair σ.symm e)
      refine hiff.mpr ?_
      have heq : permEdgePair σ (permEdgePair σ.symm e) = e := (permEdgePair σ).right_inv e
      simpa [heq] using he
  have hcard_neg : S'_neg.card = S_neg.card := by
    refine Finset.card_bij (fun e _ ↦ permEdgePair σ e)
      (fun e he ↦ ?_)
      (fun e₁ _ e₂ _ h ↦ (permEdgePair σ).injective h)
      (fun e he ↦ ⟨permEdgePair σ.symm e, ?_, (permEdgePair σ).right_inv e⟩)
    · simp only [S'_neg, S_neg, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      have hiff := mem_permGraph_edgeSet_iff σ.symm H e
      simpa [H'] using mt hiff.mpr he
    · simp only [S'_neg, S_neg, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      have hiff := mem_permGraph_edgeSet_iff σ.symm H (permEdgePair σ.symm e)
      have heq : permEdgePair σ (permEdgePair σ.symm e) = e := (permEdgePair σ).right_inv e
      exact mt hiff.mp (by simpa [heq] using he)
  rw [hpre, singleton_graph_eq_cylinder H', singleton_graph_eq_cylinder H,
    erdosRenyi_real_cylinder hp0 hp1 S'_pos S'_neg hdisj',
    erdosRenyi_real_cylinder hp0 hp1 S_pos S_neg hdisj,
    hcard_pos, hcard_neg]

/-- Any vertex-equivariant observable `φ : SimpleGraph (Fin n) → Fin n → α` produces an
exchangeable tuple `(fun i ω ↦ φ (G ω) i)` when `P.map G = erdosRenyi n p` (`0 ≤ p ≤ 1`). -/
theorem isExchangeableTuple_of_permGraph_invariant
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {G : Ω → SimpleGraph (Fin n)} (hG_meas : AEMeasurable G P)
    (hG_law : P.map G = erdosRenyi n p)
    {φ : SimpleGraph (Fin n) → Fin n → α}
    (hφ_eq : ∀ (σ : Equiv.Perm (Fin n)) (H : SimpleGraph (Fin n)) (i : Fin n),
      φ (permGraph σ H) (σ i) = φ H i) :
    IsExchangeableTuple P (fun i ω ↦ φ (G ω) i) := by
  intro σ
  let f₁ : SimpleGraph (Fin n) → Fin n → α := fun H i ↦ φ H (σ i)
  let f₂ : SimpleGraph (Fin n) → Fin n → α := fun H i ↦ φ H i
  have hf₁ : Measurable f₁ := measurable_of_finite _
  have hf₂ : Measurable f₂ := measurable_of_finite _
  refine ⟨hf₁.comp_aemeasurable hG_meas, hf₂.comp_aemeasurable hG_meas, ?_⟩
  have h1 : P.map (f₁ ∘ G) = (erdosRenyi n p).map f₁ := by
    rw [← hG_law, map_map_of_measurable_aemeasurable hf₁ hG_meas]
  have h2 : P.map (f₂ ∘ G) = (erdosRenyi n p).map f₂ := by
    rw [← hG_law, map_map_of_measurable_aemeasurable hf₂ hG_meas]
  have hcomp : f₁ ∘ permGraph σ = f₂ := by
    ext H i
    exact hφ_eq σ H i
  have hperm : (erdosRenyi n p).map f₁ = (erdosRenyi n p).map f₂ := by
    rw [← erdosRenyi_map_permGraph hp0 hp1 σ,
      Measure.map_map hf₁ (measurable_of_finite _), hcomp, erdosRenyi_map_permGraph hp0 hp1 σ]
  exact h1.trans (hperm.trans h2.symm)

/-! ### Example 4.5 (`\label{ex122}`): Vertex-$1$ deletion coupling and increment formula -/

private lemma cond_preimage_map_local {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) {G : Ω → α} (hG : Measurable G) {S : Set α} (hS : MeasurableSet S) :
    (ProbabilityTheory.cond P (G ⁻¹' S)).map G = ProbabilityTheory.cond (P.map G) S := by
  refine Measure.ext fun T hT ↦ ?_
  rw [Measure.map_apply hG hT, ProbabilityTheory.cond_apply (hG hS) P (G ⁻¹' T),
    ProbabilityTheory.cond_apply hS (P.map G) T, Measure.map_apply hG hS,
    Measure.map_apply hG (hS.inter hT), Set.preimage_inter]

private lemma deleteIncidenceSet_eq_self_of_isIsolated {n : ℕ} {G : SimpleGraph (Fin n)}
    {i : Fin n} (hiso : G.IsIsolated i) :
    G.deleteIncidenceSet i = G := by
  ext u v
  rw [SimpleGraph.deleteIncidenceSet_adj]
  refine ⟨fun h ↦ h.1, fun huv ↦ ⟨huv, ?_, ?_⟩⟩
  · rintro rfl
    exact hiso v huv
  · rintro rfl
    exact hiso u huv.symm

private lemma deleteIncidenceSet_isIsolated_iff_ne_local {n : ℕ} (G : SimpleGraph (Fin n))
    {i j : Fin n} (hji : j ≠ i) :
    (G.deleteIncidenceSet i).IsIsolated j ↔
      G.IsIsolated j ∨ (G.Adj i j ∧ (G.neighborSet j).ncard = 1) := by
  constructor
  · intro hdel
    by_cases hiso : G.IsIsolated j
    · exact Or.inl hiso
    · right
      have hall : ∀ w : Fin n, G.Adj j w → w = i := by
        intro w hjw
        by_contra hwi
        exact hdel w (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hjw, hji, hwi⟩)
      have hex : ∃ w : Fin n, G.Adj j w := by
        by_contra hno
        exact hiso fun w hw ↦ hno ⟨w, hw⟩
      rcases hex with ⟨v, hjv⟩
      have hvi : v = i := hall v hjv
      have hji_adj : G.Adj j i := hvi ▸ hjv
      have hnb : G.neighborSet j = {i} := by
        ext w
        simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
        exact ⟨hall w, fun hw ↦ hw ▸ hji_adj⟩
      exact ⟨hji_adj.symm, by rw [hnb, Set.ncard_singleton]⟩
  · rintro (hiso | ⟨hij, hcard⟩)
    · intro w hw
      exact hiso w (SimpleGraph.deleteIncidenceSet_adj.mp hw).1
    · obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard
      have hix : i = x := by
        have hi_mem : i ∈ G.neighborSet j := hij.symm
        rwa [hx, Set.mem_singleton_iff] at hi_mem
      intro w hw
      rcases SimpleGraph.deleteIncidenceSet_adj.mp hw with ⟨hjw, _, hwi⟩
      have hw_mem : w ∈ G.neighborSet j := hjw
      rw [hx, ← hix, Set.mem_singleton_iff] at hw_mem
      exact hwi hw_mem

private lemma erdosRenyi_real_degOneAdj {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {i j : Fin n} (hij : i ≠ j) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.Adj i j ∧ (G.neighborSet j).ncard = 1} =
      p * (1 - p) ^ (n - 2) := by
  classical
  let e_ij : EdgePair n := ⟨s(i, j), by simpa [Sym2.mk_isDiag_iff] using hij⟩
  let other_j : Finset (EdgePair n) :=
    Finset.univ.filter fun e : EdgePair n ↦ j ∈ e.1 ∧ i ∉ e.1
  have hdisj : Disjoint ({e_ij} : Finset (EdgePair n)) other_j := by
    rw [Finset.disjoint_singleton_left]
    simp [other_j, e_ij]
  have hcyl : {G : SimpleGraph (Fin n) | G.Adj i j ∧ (G.neighborSet j).ncard = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ ({e_ij} : Finset (EdgePair n)), e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ other_j, e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_ofPred, Finset.mem_singleton, forall_eq, other_j, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hadj, hcard⟩
      refine ⟨G.mem_edgeSet.mpr hadj, fun e ⟨hj_mem, hi_not⟩ heG ↦ ?_⟩
      obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp hcard
      have hi_u : i = u := by
        have hi_nb : i ∈ G.neighborSet j := hadj.symm
        rwa [hu, Set.mem_singleton_iff] at hi_nb
      obtain ⟨w, hw_eq⟩ := Sym2.mem_iff_exists.mp hj_mem
      have hjw : G.Adj j w := G.mem_edgeSet.mp (hw_eq ▸ heG)
      have hw_i : w = i := by
        have hw_nb : w ∈ G.neighborSet j := hjw
        rwa [hu, ← hi_u, Set.mem_singleton_iff] at hw_nb
      exact hi_not (by rw [hw_eq, hw_i]; exact Sym2.mem_mk_right j i)
    · rintro ⟨hpos, hneg⟩
      have hadj : G.Adj i j := G.mem_edgeSet.mp hpos
      have hnb : G.neighborSet j = {i} := by
        ext w
        simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
        refine ⟨fun hjw ↦ ?_, fun hw ↦ hw ▸ hadj.symm⟩
        by_contra hwi
        have hwj : w ≠ j := G.ne_of_adj hjw.symm
        let ew : EdgePair n := ⟨s(w, j), by simpa [Sym2.mk_isDiag_iff] using hwj⟩
        have hi_not : i ∉ ew.1 := by
          simp only [ew, Sym2.mem_iff, not_or]
          exact ⟨Ne.symm hwi, hij⟩
        exact hneg ew ⟨Sym2.mem_mk_right w j, hi_not⟩ (G.mem_edgeSet.mpr hjw.symm)
      exact ⟨hadj, by rw [hnb, Set.ncard_singleton]⟩
  have hcard_other : other_j.card = n - 2 := by
    have hn2 : 2 ≤ n := by
      have : i.1 ≠ j.1 := fun hv ↦ hij (Fin.ext hv)
      omega
    have hbij : ((Finset.univ.erase j).erase i).card = other_j.card := by
      refine Finset.card_bij
        (fun w hw ↦ ⟨s(j, w), by
          rw [Sym2.mk_isDiag_iff]
          exact (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw)).symm⟩)
        (fun w hw ↦ ?_)
        (fun w₁ _ w₂ _ h ↦ Sym2.congr_right.mp (Subtype.ext_iff.mp h))
        (fun e he ↦ ?_)
      · have hwi : w ≠ i := Finset.ne_of_mem_erase hw
        simp only [other_j, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Sym2.mem_mk_left j w, by simp [Sym2.mem_iff, hij, Ne.symm hwi]⟩
      · simp only [other_j, Finset.mem_filter, Finset.mem_univ, true_and] at he
        refine ⟨Sym2.Mem.other he.1, ?_, Subtype.ext (Sym2.other_spec he.1)⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨Sym2.other_ne e.2 he.1,
          Finset.mem_univ _⟩⟩
        intro h_eq
        apply he.2
        rw [← Sym2.other_spec he.1, h_eq]
        exact Sym2.mem_mk_right j i
    have hcard_lhs : ((Finset.univ.erase j).erase i).card = n - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩),
        Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
      omega
    exact hbij.symm.trans hcard_lhs
  rw [hcyl, erdosRenyi_real_cylinder hp0 hp1 _ _ hdisj,
    Finset.card_singleton, pow_one, hcard_other]

/-- **Example 4.5** (`\label{ex122}`, `SteinIntro.tex:2189-2207`): vertex-$1$ edge-deletion
size-bias coupling and $L^1$ increment calculation for isolated vertices in $G(n, p)$. -/
theorem isolatedVertices_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {p : ℝ} {G : Ω → SimpleGraph (Fin n)}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hG_meas : Measurable G)
    (hG_law : P.map G = erdosRenyi n p) :
    let v0 : Fin n := ⟨0, hn⟩
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let X : Fin n → Ω → ℝ := fun i ω ↦ X_ind i (G ω)
    let X1 : {j : Fin n // j ≠ v0} → Ω → ℝ :=
      fun j ω ↦ X_ind j.1 ((G ω).deleteIncidenceSet v0)
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ v0}, X1 j ω) + 1
    (p < 1 →
      P.map (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X1 j ω) =
        (ProbabilityTheory.cond P {ω | X v0 ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X j.1 ω)) ∧
      IsSizeBias P W P Ws ∧
      (∀ (ω : Ω) (j : {j : Fin n // j ≠ v0}), X j.1 ω ≤ X1 j ω) ∧
      (∀ j : {j : Fin n // j ≠ v0},
        (∀ ω : Ω, X1 j ω - X j.1 ω = 0 ∨ X1 j ω - X j.1 ω = 1) ∧
          P.real {ω | X1 j ω - X j.1 ω = 1} = p * (1 - p) ^ (n - 2)) ∧
      ∫ ω, |W ω + 1 - Ws ω| ∂P =
        ∫ ω, |X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)| ∂P ∧
      ∫ ω, |X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)| ∂P =
        ∫ ω, X v0 ω ∂P + ∑ j : {j : Fin n // j ≠ v0}, ∫ ω, (X1 j ω - X j.1 ω) ∂P ∧
      ∫ ω, X v0 ω ∂P + ∑ j : {j : Fin n // j ≠ v0}, ∫ ω, (X1 j ω - X j.1 ω) ∂P =
        (1 - p) ^ (n - 1) + ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) := by
  intro v0 X_ind X X1 W Ws
  have hX_meas : ∀ i : Fin n, Measurable (X i) :=
    fun i ↦ (measurable_of_finite (X_ind i)).comp hG_meas
  have hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1 := fun i ↦
    Eventually.of_forall fun ω ↦ by
      by_cases h : (G ω).IsIsolated i
      · exact Or.inr (Set.indicator_of_mem h 1)
      · exact Or.inl (Set.indicator_of_notMem h 1)
  have hexch : IsExchangeableTuple P X := by
    refine isExchangeableTuple_of_permGraph_invariant P hp0 hp1 hG_meas.aemeasurable hG_law
      (φ := fun H i ↦ X_ind i H) ?_
    intro σ H i
    dsimp [X_ind]
    by_cases h : H.IsIsolated i
    · have h' : (permGraph σ H).IsIsolated (σ i) := (permGraph_isIsolated_iff σ H i).mpr h
      simp [h, h']
    · have h' : ¬ (permGraph σ H).IsIsolated (σ i) := mt (permGraph_isIsolated_iff σ H i).mp h
      simp [h, h']
  have hcond : p < 1 →
      P.map (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X1 j ω) =
        (ProbabilityTheory.cond P {ω | X v0 ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X j.1 ω) := by
    intro hp_lt
    let S_iso : Set (SimpleGraph (Fin n)) := {H | H.IsIsolated v0}
    have hpre : {ω : Ω | X v0 ω = 1} = G ⁻¹' S_iso := by
      ext ω
      simp only [Set.mem_ofPred, Set.mem_preimage, X, X_ind, S_iso]
      by_cases h : (G ω).IsIsolated v0 <;> simp [h]
    let proj : SimpleGraph (Fin n) → ({j : Fin n // j ≠ v0} → ℝ) :=
      fun H j ↦ X_ind j.1 H
    let del : SimpleGraph (Fin n) → SimpleGraph (Fin n) := fun H ↦ H.deleteIncidenceSet v0
    have hproj_meas : Measurable proj := measurable_of_finite _
    have hdel_meas : Measurable del := measurable_of_finite _
    have hlhs : P.map (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X1 j ω) =
        ((erdosRenyi n p).map del).map proj := by
      have h1 : (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X1 j ω) = proj ∘ del ∘ G := rfl
      rw [h1, ← Measure.map_map hproj_meas (hdel_meas.comp hG_meas),
        ← Measure.map_map hdel_meas hG_meas, hG_law]
    have hrhs : (ProbabilityTheory.cond P {ω | X v0 ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X j.1 ω) =
        (ProbabilityTheory.cond (erdosRenyi n p) S_iso).map proj := by
      have h2 : (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X j.1 ω) = proj ∘ G := rfl
      rw [hpre, h2, ← Measure.map_map hproj_meas hG_meas,
        cond_preimage_map_local P hG_meas MeasurableSet.of_discrete, hG_law]
    rw [hlhs, hrhs, erdosRenyi_cond_isIsolated_eq_map_deleteIncidenceSet hp0 hp_lt v0]
  have hY_meas : AEMeasurable (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X1 j ω) P :=
    (Measurable.of_eval fun (j : {j : Fin n // j ≠ v0}) ↦
      (measurable_of_finite fun H : SimpleGraph (Fin n) ↦
        X_ind j.1 (H.deleteIncidenceSet v0)).comp hG_meas).aemeasurable
  have hSB : IsSizeBias P W P Ws := by
    refine sizeBias_sum_of_exchangeable_zero_one_fin P P hn hX_meas hX_zo hexch hY_meas ?_
    intro hpos
    rcases hp1.eq_or_lt with rfl | hp_lt
    · by_cases hn1 : n = 1
      · subst hn1
        have : Subsingleton ({j : Fin 1 // j ≠ v0} → ℝ) :=
          ⟨fun f g ↦ funext fun ⟨j, hj⟩ ↦ False.elim (hj (Subsingleton.elim j v0))⟩
        have : IsProbabilityMeasure
            (P.map (fun ω (j : {j : Fin 1 // j ≠ v0}) ↦ X1 j ω)) :=
          (Measure.isProbabilityMeasure_map_iff hY_meas).mpr ‹_›
        have hPA0 : P (X v0 ⁻¹' {1}) ≠ 0 := by
          intro h0
          have : P.real (X v0 ⁻¹' {1}) = 0 := by simp [Measure.real, h0]
          linarith
        have : IsProbabilityMeasure (ProbabilityTheory.cond P (X v0 ⁻¹' {1})) :=
          ProbabilityTheory.cond_isProbabilityMeasure hPA0
        have : IsProbabilityMeasure
            ((ProbabilityTheory.cond P (X v0 ⁻¹' {1})).map
              (fun ω (j : {j : Fin 1 // j ≠ v0}) ↦ X j.1 ω)) :=
          (Measure.isProbabilityMeasure_map_iff
            (Measurable.of_eval fun (j : {j : Fin 1 // j ≠ v0}) ↦
              hX_meas j.1).aemeasurable).mpr ‹_›
        ext s hs
        rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
        · simp
        · have hs_univ : s = Set.univ :=
            Set.eq_univ_of_forall fun y ↦ Subsingleton.elim x y ▸ hx
          rw [hs_univ, measure_univ, measure_univ]
      · have hn2 : 2 ≤ n := by omega
        have hpre : X v0 ⁻¹' {(1 : ℝ)} = G ⁻¹' {H | H.IsIsolated v0} := by
          ext ω
          by_cases h : (G ω).IsIsolated v0 <;> simp [X, X_ind, h]
        have hp_zero : P.real (X v0 ⁻¹' {1}) = 0 := by
          rw [hpre, ← map_measureReal_apply hG_meas MeasurableSet.of_discrete, hG_law,
            erdosRenyi_real_isIsolated hp0 le_rfl v0]
          have hpow : (0 : ℝ) ^ (n - 1) = 0 := zero_pow (by omega)
          simpa using hpow
        linarith
    · exact hcond hp_lt
  have hpt_eq1 : ∀ ω : Ω,
      W ω + 1 - Ws ω = X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω) := by
    intro ω
    have hsplit : W ω = (∑ j : {j : Fin n // j ≠ v0}, X j.1 ω) + X v0 ω := by
      dsimp [W]
      rw [← Finset.sum_erase_add Finset.univ (fun k ↦ X k ω) (Finset.mem_univ v0),
        Finset.sum_subtype (Finset.univ.erase v0) (p := fun k ↦ k ≠ v0) (fun k ↦ by simp)
          (fun k ↦ X k ω)]
    have hsub : (∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)) =
        (∑ j : {j : Fin n // j ≠ v0}, X j.1 ω) - ∑ j : {j : Fin n // j ≠ v0}, X1 j ω :=
      Finset.sum_sub_distrib _ _
    dsimp [Ws]
    linarith
  have hmono : ∀ (ω : Ω) (j : {j : Fin n // j ≠ v0}), X j.1 ω ≤ X1 j ω := by
    intro ω j
    by_cases hj : (G ω).IsIsolated j.1
    · have hj' : ((G ω).deleteIncidenceSet v0).IsIsolated j.1 :=
        (deleteIncidenceSet_isIsolated_iff_ne_local (G ω) j.2).mpr (Or.inl hj)
      have h1 : X j.1 ω = 1 := Set.indicator_of_mem hj 1
      have h2 : X1 j ω = 1 := Set.indicator_of_mem hj' 1
      linarith
    · have h1 : X j.1 ω = 0 := Set.indicator_of_notMem hj 1
      have h2 : 0 ≤ X1 j ω := by
        by_cases hj' : ((G ω).deleteIncidenceSet v0).IsIsolated j.1 <;>
          simp [X1, X_ind, hj']
      linarith
  have hpt_abs : ∀ ω : Ω,
      |X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)| =
        X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X1 j ω - X j.1 ω) := by
    intro ω
    by_cases hiso : (G ω).IsIsolated v0
    · have hdel_eq : (G ω).deleteIncidenceSet v0 = G ω :=
        deleteIncidenceSet_eq_self_of_isIsolated hiso
      have hX1_eq : ∀ j : {j : Fin n // j ≠ v0}, X1 j ω = X j.1 ω := fun j ↦ by
        simp [X1, X, hdel_eq]
      have hXv0 : X v0 ω = 1 := Set.indicator_of_mem hiso 1
      simp [hX1_eq, hXv0]
    · have hXv0 : X v0 ω = 0 := Set.indicator_of_notMem hiso 1
      have hsum_neg : (∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)) =
          -(∑ j : {j : Fin n // j ≠ v0}, (X1 j ω - X j.1 ω)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by ring
      have hsum_nn : 0 ≤ ∑ j : {j : Fin n // j ≠ v0}, (X1 j ω - X j.1 ω) :=
        Finset.sum_nonneg fun j _ ↦ sub_nonneg.mpr (hmono ω j)
      rw [hXv0, zero_add, zero_add, hsum_neg, abs_neg, abs_of_nonneg hsum_nn]
  have hint1 : ∫ ω, |W ω + 1 - Ws ω| ∂P =
      ∫ ω, |X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)| ∂P := by
    simp_rw [hpt_eq1]
  have hXv0_int : Integrable (X v0) P :=
    (integrable_const (1 : ℝ)).mono' (hX_meas v0).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        by_cases h : (G ω).IsIsolated v0 <;> simp [X, X_ind, h])
  have hdiff_int : ∀ j : {j : Fin n // j ≠ v0}, Integrable (fun ω ↦ X1 j ω - X j.1 ω) P := by
    intro j
    have hX1_int : Integrable (X1 j) P :=
      (integrable_const (1 : ℝ)).mono'
        (((measurable_of_finite fun H : SimpleGraph (Fin n) ↦
          X_ind j.1 (H.deleteIncidenceSet v0)).comp hG_meas).aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          by_cases h : ((G ω).deleteIncidenceSet v0).IsIsolated j.1 <;> simp [X1, X_ind, h])
    have hXj_int : Integrable (X j.1) P :=
      (integrable_const (1 : ℝ)).mono' (hX_meas j.1).aestronglyMeasurable
        (Eventually.of_forall fun ω ↦ by
          by_cases h : (G ω).IsIsolated j.1 <;> simp [X, X_ind, h])
    exact hX1_int.sub hXj_int
  have hint2 : ∫ ω, |X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)| ∂P =
      ∫ ω, X v0 ω ∂P + ∑ j : {j : Fin n // j ≠ v0}, ∫ ω, (X1 j ω - X j.1 ω) ∂P := by
    simp_rw [hpt_abs]
    rw [integral_add hXv0_int (integrable_finsetSum Finset.univ fun j _ ↦ hdiff_int j),
      integral_finsetSum Finset.univ fun j _ ↦ hdiff_int j]
  have hEXv0 : ∫ ω, X v0 ω ∂P = (1 - p) ^ (n - 1) := by
    have hmap := integral_map (μ := P) hG_meas.aemeasurable
      (measurable_of_finite (X_ind v0)).aestronglyMeasurable
    rw [← hmap, hG_law, MeasureTheory.integral_indicator MeasurableSet.of_discrete]
    simp [erdosRenyi_real_isIsolated hp0 hp1 v0]
  have hper_j : ∀ j : {j : Fin n // j ≠ v0},
      (∀ ω : Ω, X1 j ω - X j.1 ω = 0 ∨ X1 j ω - X j.1 ω = 1) ∧
        P.real {ω | X1 j ω - X j.1 ω = 1} = p * (1 - p) ^ (n - 2) ∧
        ∫ ω, (X1 j ω - X j.1 ω) ∂P = p * (1 - p) ^ (n - 2) := by
    intro j
    let deg1Set : Set (SimpleGraph (Fin n)) :=
      {H | H.Adj v0 j.1 ∧ (H.neighborSet j.1).ncard = 1}
    have hpt_deg1 : ∀ H : SimpleGraph (Fin n),
        X_ind j.1 (H.deleteIncidenceSet v0) - X_ind j.1 H =
          deg1Set.indicator (1 : SimpleGraph (Fin n) → ℝ) H := by
      intro H
      by_cases hj : H.IsIsolated j.1
      · have hj' : (H.deleteIncidenceSet v0).IsIsolated j.1 :=
          (deleteIncidenceSet_isIsolated_iff_ne_local H j.2).mpr (Or.inl hj)
        have hnot : H ∉ deg1Set := fun h ↦ hj v0 h.1.symm
        simp [X_ind, hj, hj', Set.indicator_of_notMem hnot]
      · by_cases hd1 : H ∈ deg1Set
        · have hj' : (H.deleteIncidenceSet v0).IsIsolated j.1 :=
            (deleteIncidenceSet_isIsolated_iff_ne_local H j.2).mpr (Or.inr hd1)
          simp [X_ind, hj, hj', Set.indicator_of_mem hd1]
        · have hj' : ¬ (H.deleteIncidenceSet v0).IsIsolated j.1 := by
            intro hc
            rcases (deleteIncidenceSet_isIsolated_iff_ne_local H j.2).mp hc with h1 | h2
            · exact hj h1
            · exact hd1 h2
          simp [X_ind, hj, hj', Set.indicator_of_notMem hd1]
    have hfun : (fun ω ↦ X1 j ω - X j.1 ω) = fun ω ↦ deg1Set.indicator 1 (G ω) :=
      funext fun ω ↦ hpt_deg1 (G ω)
    have hzo_j : ∀ ω : Ω, X1 j ω - X j.1 ω = 0 ∨ X1 j ω - X j.1 ω = 1 := fun ω ↦ by
      rw [hpt_deg1 (G ω)]
      by_cases h : G ω ∈ deg1Set
      · exact Or.inr (Set.indicator_of_mem h 1)
      · exact Or.inl (Set.indicator_of_notMem h 1)
    have hpre_j : {ω : Ω | X1 j ω - X j.1 ω = 1} = G ⁻¹' deg1Set := by
      ext ω
      rw [Set.mem_ofPred, hpt_deg1 (G ω)]
      by_cases h : G ω ∈ deg1Set <;> simp [h]
    have hprob_j : P.real {ω | X1 j ω - X j.1 ω = 1} = p * (1 - p) ^ (n - 2) := by
      rw [hpre_j, ← map_measureReal_apply hG_meas MeasurableSet.of_discrete, hG_law]
      exact erdosRenyi_real_degOneAdj hp0 hp1 j.2.symm
    have hint_j : ∫ ω, (X1 j ω - X j.1 ω) ∂P = p * (1 - p) ^ (n - 2) := by
      have hmap := integral_map (μ := P) hG_meas.aemeasurable
        (measurable_of_finite
          (deg1Set.indicator (1 : SimpleGraph (Fin n) → ℝ))).aestronglyMeasurable
      rw [hfun, ← hmap, hG_law, integral_indicator_one MeasurableSet.of_discrete]
      exact erdosRenyi_real_degOneAdj hp0 hp1 j.2.symm
    exact ⟨hzo_j, hprob_j, hint_j⟩
  have hEdiff : ∀ j : {j : Fin n // j ≠ v0},
      ∫ ω, (X1 j ω - X j.1 ω) ∂P = p * (1 - p) ^ (n - 2) :=
    fun j ↦ (hper_j j).2.2
  have hint3 : ∫ ω, X v0 ω ∂P + ∑ j : {j : Fin n // j ≠ v0}, ∫ ω, (X1 j ω - X j.1 ω) ∂P =
      (1 - p) ^ (n - 1) + ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) := by
    rw [hEXv0]
    simp_rw [hEdiff, Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card {j : Fin n // j ≠ v0} = n - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    rw [hcard, nsmul_eq_mul, Nat.cast_sub hn, Nat.cast_one]
    ring
  exact ⟨hcond, hSB, hmono, fun j ↦ ⟨(hper_j j).1, (hper_j j).2.1⟩, hint1, hint2, hint3⟩

end SteinMethod
