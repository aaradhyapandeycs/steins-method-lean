/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.RandomGraph.ErdosRenyi
import Formalization.SizeBias.Coupling
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Size-Bias Coupling for Isolated Vertices (`Formalization.RandomGraph.IsolatedCoupling`)

Implements Example 3.9 (`Ex3_9_sizeBias_proof`, `SteinIntro.tex:1354-1367, 1380-1383`) of Nathan
Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `erdosRenyi_cond_isIsolated_eq_map_deleteIncidenceSet`: conditioning $G \sim G(n, p)$
  ($0 \le p < 1$) on vertex `i` being isolated has the same law as erasing all edges incident to
  `i` (`SimpleGraph.deleteIncidenceSet`).
* `Ex3_9_sizeBias_proof`: erasing all edges incident to an independent uniform vertex $I$ produces
  a size-biased version $X^s$ of the isolated-vertex count $X$ in $G(n, p)$ ($0 \le p < 1$) via
  Corollary 3.16 (`sizeBias_sum_of_zero_one`), with deterministic increment
  $X^s - X = D_I + \mathbf{1}_{d_I > 0}$.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### Conditioning and Cardinality Helpers -/

section Helpers

private lemma cond_preimage_map {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) {G : Ω → α} (hG : Measurable G) {S : Set α} (hS : MeasurableSet S) :
    (ProbabilityTheory.cond P (G ⁻¹' S)).map G = ProbabilityTheory.cond (P.map G) S := by
  refine Measure.ext fun T hT ↦ ?_
  rw [Measure.map_apply hG hT, ProbabilityTheory.cond_apply (hG hS) P (G ⁻¹' T),
    ProbabilityTheory.cond_apply hS (P.map G) T, Measure.map_apply hG hS,
    Measure.map_apply hG (hS.inter hT), Set.preimage_inter]

private lemma cond_measureReal_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {s : Set Ω} (hs : MeasurableSet s) (t : Set Ω) :
    (ProbabilityTheory.cond μ s).real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  simp only [measureReal_def, ProbabilityTheory.cond_apply hs μ t, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

private lemma ncard_set_eq_sum_ite {n : ℕ} (s : Set (Fin n)) [DecidablePred (· ∈ s)] :
    (s.ncard : ℝ) = ∑ j : Fin n, if j ∈ s then (1 : ℝ) else 0 := by
  rw [Set.ncard_eq_toFinset_card']
  have h : s.toFinset = Finset.univ.filter (· ∈ s) := by
    ext j
    simp
  rw [h, ← Finset.sum_filter]
  simp

end Helpers

/-! ### Conditional Law of `deleteIncidenceSet` under $G(n, p)$ -/

section CondDeleteIncidence

private def incidentEdges {n : ℕ} (i : Fin n) : Finset (EdgePair n) :=
  Finset.univ.filter (fun e ↦ i ∈ e.1)

private lemma card_incidentEdges {n : ℕ} (i : Fin n) :
    (incidentEdges i).card = n - 1 := by
  have hbij : (Finset.univ.erase i).card = (incidentEdges i).card := by
    refine Finset.card_bij
      (fun j hj ↦ ⟨s(i, j), by
        rw [Sym2.mk_isDiag_iff]
        exact (Finset.ne_of_mem_erase hj).symm⟩)
      (fun j _ ↦ by simp [incidentEdges])
      (fun j₁ _ j₂ _ h ↦ Sym2.congr_right.mp (Subtype.ext_iff.mp h))
      (fun e he ↦ ?_)
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact ⟨Sym2.Mem.other he,
      Finset.mem_erase.mpr ⟨Sym2.other_ne e.2 he, Finset.mem_univ _⟩,
      Subtype.ext (Sym2.other_spec he)⟩
  simpa using hbij.symm

private lemma isIsolated_iff_forall_incidentEdges {n : ℕ} (i : Fin n) (G : SimpleGraph (Fin n)) :
    G.IsIsolated i ↔ ∀ e ∈ incidentEdges i, e.1 ∉ G.edgeSet := by
  constructor
  · intro hiso e he hmem
    simp only [incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [← Sym2.other_spec he, SimpleGraph.mem_edgeSet] at hmem
    exact hiso (Sym2.Mem.other he) hmem
  · intro h v hadj
    have hne : i ≠ v := G.ne_of_adj hadj
    let e : EdgePair n := ⟨s(i, v), by rwa [Sym2.mk_isDiag_iff]⟩
    have he : e ∈ incidentEdges i := by simp [incidentEdges, e]
    exact h e he (G.mem_edgeSet.mpr hadj)

/-- Probability that a fixed vertex `i` is isolated in $G(n, p)$ (`SteinIntro.tex:1370`). -/
lemma erdosRenyi_real_isIsolated {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.IsIsolated i} = (1 - p) ^ (n - 1) := by
  have hset : {G : SimpleGraph (Fin n) | G.IsIsolated i} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ incidentEdges i, e.1 ∉ G.edgeSet)} := by
    ext G
    simp [isIsolated_iff_forall_incidentEdges]
  rw [hset, erdosRenyi_real_cylinder hp0 hp1 ∅ (incidentEdges i) (Finset.disjoint_empty_left _),
    Finset.card_empty, pow_zero, one_mul, card_incidentEdges]

private lemma deleteIncidenceSet_isIsolated_self {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    (G.deleteIncidenceSet i).IsIsolated i := by
  intro v hadj
  exact (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.1 rfl

private lemma singleton_eq_cylinder_of_isIsolated {n : ℕ} {i : Fin n} {H : SimpleGraph (Fin n)}
    [DecidablePred fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∈ H.edgeSet]
    [DecidablePred fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∉ H.edgeSet]
    (hH : H.IsIsolated i) :
    ({G : SimpleGraph (Fin n) | G.IsIsolated i} ∩ {H}) =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∈ H.edgeSet),
          e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ incidentEdges i ∪
            Finset.univ.filter (fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∉ H.edgeSet),
          e.1 ∉ G.edgeSet)} := by
  have hH_inc := (isIsolated_iff_forall_incidentEdges i H).mp hH
  ext G
  simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, rfl⟩
    refine ⟨fun e he ↦ he.2, fun e he ↦ ?_⟩
    rcases he with he | he
    · exact hH_inc e he
    · exact he.2
  · rintro ⟨hpos, hneg⟩
    have hGH : G = H := by
      ext u v
      by_cases huv : u = v
      · subst huv
        simp [SimpleGraph.irrefl]
      · let e : EdgePair n := ⟨s(u, v), by rwa [Sym2.mk_isDiag_iff]⟩
        rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeSet]
        change e.1 ∈ G.edgeSet ↔ e.1 ∈ H.edgeSet
        by_cases hi : i ∈ e.1
        · have he_inc : e ∈ incidentEdges i := by simp [incidentEdges, hi]
          exact iff_of_false (hneg e (Or.inl he_inc)) (hH_inc e he_inc)
        · by_cases hmem : e.1 ∈ H.edgeSet
          · exact iff_of_true (hpos e ⟨hi, hmem⟩) hmem
          · exact iff_of_false (hneg e (Or.inr ⟨hi, hmem⟩)) hmem
    exact ⟨hGH ▸ hH, hGH⟩

private lemma preimage_deleteIncidenceSet_eq_cylinder_of_isIsolated {n : ℕ} {i : Fin n}
    {H : SimpleGraph (Fin n)}
    [DecidablePred fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∈ H.edgeSet]
    [DecidablePred fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∉ H.edgeSet]
    (hH : H.IsIsolated i) :
    (fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet i) ⁻¹' {H} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∈ H.edgeSet),
          e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ Finset.univ.filter (fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∉ H.edgeSet),
          e.1 ∉ G.edgeSet)} := by
  have hdel_mem : ∀ (G : SimpleGraph (Fin n)) (e : EdgePair n), i ∉ e.1 →
      (e.1 ∈ (G.deleteIncidenceSet i).edgeSet ↔ e.1 ∈ G.edgeSet) := by
    rintro G ⟨z, _⟩
    change i ∉ z → (z ∈ (G.deleteIncidenceSet i).edgeSet ↔ z ∈ G.edgeSet)
    refine Sym2.ind (fun u v hi' ↦ ?_) z
    simp only [Sym2.mem_iff, not_or] at hi'
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.deleteIncidenceSet_adj]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, Ne.symm hi'.1, Ne.symm hi'.2⟩⟩
  ext G
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro rfl
    exact ⟨fun e he ↦ (hdel_mem G e he.1).mp he.2, fun e he ↦ mt (hdel_mem G e he.1).mpr he.2⟩
  · rintro ⟨hpos, hneg⟩
    ext u v
    by_cases huv : u = v
    · subst huv
      simp [SimpleGraph.irrefl]
    · rw [SimpleGraph.deleteIncidenceSet_adj]
      by_cases hui : u = i
      · subst hui
        exact iff_of_false (fun h ↦ h.2.1 rfl) (hH v)
      · by_cases hvi : v = i
        · subst hvi
          exact iff_of_false (fun h ↦ h.2.2 rfl) (fun h ↦ hH u h.symm)
        · let e : EdgePair n := ⟨s(u, v), by rwa [Sym2.mk_isDiag_iff]⟩
          have hi : i ∉ e.1 := by
            simp only [e, Sym2.mem_iff, not_or]
            exact ⟨Ne.symm hui, Ne.symm hvi⟩
          have hG_iff : G.Adj u v ↔ e.1 ∈ G.edgeSet := G.mem_edgeSet.symm
          have hH_iff : H.Adj u v ↔ e.1 ∈ H.edgeSet := H.mem_edgeSet.symm
          rw [hG_iff, hH_iff]
          by_cases hmem : e.1 ∈ H.edgeSet
          · exact iff_of_true ⟨hpos e ⟨hi, hmem⟩, hui, hvi⟩ hmem
          · exact iff_of_false (fun h ↦ hneg e ⟨hi, hmem⟩ h.1) hmem

/-- Conditioning $G \sim G(n, p)$ ($0 \le p < 1$) on vertex `i` being isolated has the same law as
erasing all edges incident to `i` (`SteinIntro.tex:1360-1365`). -/
lemma erdosRenyi_cond_isIsolated_eq_map_deleteIncidenceSet {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) (i : Fin n) :
    ProbabilityTheory.cond (erdosRenyi n p) {G : SimpleGraph (Fin n) | G.IsIsolated i} =
      (erdosRenyi n p).map (fun G ↦ G.deleteIncidenceSet i) := by
  classical
  set S_iso : Set (SimpleGraph (Fin n)) := {G | G.IsIsolated i}
  set del : SimpleGraph (Fin n) → SimpleGraph (Fin n) := fun G ↦ G.deleteIncidenceSet i
  have hdel_meas : Measurable del := measurable_of_finite del
  have hS_iso_meas : MeasurableSet S_iso := MeasurableSet.of_discrete
  refine Measure.ext_of_singleton fun H ↦ ?_
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top (ProbabilityTheory.cond (erdosRenyi n p) S_iso) {H})
    (measure_ne_top ((erdosRenyi n p).map del) {H})).mp ?_
  rw [cond_measureReal_apply (erdosRenyi n p) hS_iso_meas {H},
    map_measureReal_apply hdel_meas (measurableSet_singleton H)]
  by_cases hH : H.IsIsolated i
  · let S_pos : Finset (EdgePair n) :=
      Finset.univ.filter (fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∈ H.edgeSet)
    let S_neg : Finset (EdgePair n) :=
      Finset.univ.filter (fun e : EdgePair n ↦ i ∉ e.1 ∧ e.1 ∉ H.edgeSet)
    have hdisj_pn : Disjoint S_pos S_neg :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ h2.2 h1.2
    have hdisj_in : Disjoint (incidentEdges i) S_neg :=
      Finset.disjoint_filter.mpr fun _ _ hi h2 ↦ h2.1 hi
    have hdisj_pi : Disjoint S_pos (incidentEdges i) :=
      Finset.disjoint_filter.mpr fun _ _ h1 hi ↦ h1.1 hi
    have hdisj_pu : Disjoint S_pos (incidentEdges i ∪ S_neg) :=
      Finset.disjoint_union_right.mpr ⟨hdisj_pi, hdisj_pn⟩
    have hprob_iso : (erdosRenyi n p).real S_iso = (1 - p) ^ (n - 1) :=
      erdosRenyi_real_isIsolated hp0 hp1.le i
    have hprob_pos : (1 - p) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by linarith)
    rw [hprob_iso]
    dsimp only [S_iso, del]
    rw [singleton_eq_cylinder_of_isIsolated hH,
      preimage_deleteIncidenceSet_eq_cylinder_of_isIsolated hH,
      erdosRenyi_real_cylinder hp0 hp1.le S_pos (incidentEdges i ∪ S_neg) hdisj_pu,
      erdosRenyi_real_cylinder hp0 hp1.le S_pos S_neg hdisj_pn,
      Finset.card_union_of_disjoint hdisj_in, card_incidentEdges, pow_add]
    calc
      ((1 - p) ^ (n - 1))⁻¹ * (p ^ S_pos.card * ((1 - p) ^ (n - 1) * (1 - p) ^ S_neg.card))
        = ((1 - p) ^ (n - 1) * ((1 - p) ^ (n - 1))⁻¹) *
            (p ^ S_pos.card * (1 - p) ^ S_neg.card) := by ring
      _ = p ^ S_pos.card * (1 - p) ^ S_neg.card := by rw [mul_inv_cancel₀ hprob_pos, one_mul]
  · have hinter : S_iso ∩ {H} = ∅ := by
      ext G
      simp only [S_iso, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      rintro hiso rfl
      exact hH hiso
    have hpre : del ⁻¹' {H} = ∅ := by
      ext G
      simp only [del, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hEq
      exact hH (hEq ▸ deleteIncidenceSet_isIsolated_self G i)
    simp [hinter, hpre]

end CondDeleteIncidence

/-! ### Deterministic Increment & Proof of Example 3.9 (`Ex3_9_sizeBias_proof`) -/

section Ex3_9

private lemma deleteIncidenceSet_isIsolated_iff_of_ne {n : ℕ} (G : SimpleGraph (Fin n))
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
        simp only [SimpleGraph.mem_neighborSet, mem_singleton_iff]
        exact ⟨hall w, fun hw ↦ hw ▸ hji_adj⟩
      exact ⟨hji_adj.symm, by rw [hnb, Set.ncard_singleton]⟩
  · rintro (hiso | ⟨hij, hcard⟩)
    · intro w hw
      exact hiso w (SimpleGraph.deleteIncidenceSet_adj.mp hw).1
    · obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hcard
      have hix : i = x := by
        have hi_mem : i ∈ G.neighborSet j := hij.symm
        rwa [hx, mem_singleton_iff] at hi_mem
      intro w hw
      rcases SimpleGraph.deleteIncidenceSet_adj.mp hw with ⟨hjw, _, hwi⟩
      have hw_mem : w ∈ G.neighborSet j := hjw
      rw [hx, ← hix, mem_singleton_iff] at hw_mem
      exact hwi hw_mem

private lemma isIsolated_iff_neighborSet_ncard_eq_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (i : Fin n) :
    G.IsIsolated i ↔ (G.neighborSet i).ncard = 0 := by
  rw [Set.ncard_eq_zero (Set.toFinite _), SimpleGraph.neighborSet_eq_empty]

/-- Vertex `i` is non-isolated iff its neighbor set has positive cardinality. -/
lemma not_isIsolated_iff_neighborSet_ncard_pos {n : ℕ} (G : SimpleGraph (Fin n))
    (i : Fin n) :
    ¬ G.IsIsolated i ↔ 0 < (G.neighborSet i).ncard := by
  rw [isIsolated_iff_neighborSet_ncard_eq_zero, Nat.pos_iff_ne_zero]

private lemma deleteIncidenceSet_isolatedCount_sub {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    (∑ k : Fin n, {K : SimpleGraph (Fin n) | K.IsIsolated k}.indicator
        (1 : SimpleGraph (Fin n) → ℝ) (G.deleteIncidenceSet i)) -
      (∑ k : Fin n, {K : SimpleGraph (Fin n) | K.IsIsolated k}.indicator
        (1 : SimpleGraph (Fin n) → ℝ) G) =
    ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ) +
      {K : SimpleGraph (Fin n) | 0 < (K.neighborSet i).ncard}.indicator
        (1 : SimpleGraph (Fin n) → ℝ) G := by
  classical
  let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
    fun k H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated k}.indicator 1 H
  have hsplit_del :
      (∑ k : Fin n, X_ind k (G.deleteIncidenceSet i)) =
        (∑ j ∈ Finset.univ.erase i, X_ind j (G.deleteIncidenceSet i)) +
          X_ind i (G.deleteIncidenceSet i) :=
    (Finset.sum_erase_add Finset.univ (fun k ↦ X_ind k (G.deleteIncidenceSet i))
      (Finset.mem_univ i)).symm
  have hsplit_G :
      (∑ k : Fin n, X_ind k G) =
        (∑ j ∈ Finset.univ.erase i, X_ind j G) + X_ind i G :=
    (Finset.sum_erase_add Finset.univ (fun k ↦ X_ind k G) (Finset.mem_univ i)).symm
  have hi_del : X_ind i (G.deleteIncidenceSet i) = 1 :=
    Set.indicator_of_mem (deleteIncidenceSet_isIsolated_self G i) 1
  have hi_diff : 1 - X_ind i G =
      {K : SimpleGraph (Fin n) | 0 < (K.neighborSet i).ncard}.indicator
        (1 : SimpleGraph (Fin n) → ℝ) G := by
    by_cases hiso : G.IsIsolated i
    · have hnot : ¬ 0 < (G.neighborSet i).ncard := by
        rwa [← not_isIsolated_iff_neighborSet_ncard_pos, not_not]
      have h1 : X_ind i G = 1 := Set.indicator_of_mem hiso 1
      have h2 : {K : SimpleGraph (Fin n) | 0 < (K.neighborSet i).ncard}.indicator
          (1 : SimpleGraph (Fin n) → ℝ) G = 0 := Set.indicator_of_notMem hnot 1
      linarith
    · have hpos : 0 < (G.neighborSet i).ncard :=
        (not_isIsolated_iff_neighborSet_ncard_pos G i).mp hiso
      have h1 : X_ind i G = 0 := Set.indicator_of_notMem hiso 1
      have h2 : {K : SimpleGraph (Fin n) | 0 < (K.neighborSet i).ncard}.indicator
          (1 : SimpleGraph (Fin n) → ℝ) G = 1 := Set.indicator_of_mem hpos 1
      linarith
  have hj_diff : ∀ j ∈ Finset.univ.erase i,
      X_ind j (G.deleteIncidenceSet i) - X_ind j G =
        if G.Adj i j ∧ (G.neighborSet j).ncard = 1 then (1 : ℝ) else 0 := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hiff := deleteIncidenceSet_isIsolated_iff_of_ne G hji
    by_cases hiso : G.IsIsolated j
    · have hdel : (G.deleteIncidenceSet i).IsIsolated j := hiff.mpr (Or.inl hiso)
      have hnadj : ¬ (G.Adj i j ∧ (G.neighborSet j).ncard = 1) :=
        fun h ↦ hiso i h.1.symm
      have h1 : X_ind j (G.deleteIncidenceSet i) = 1 := by exact Set.indicator_of_mem hdel 1
      have h2 : X_ind j G = 1 := by exact Set.indicator_of_mem hiso 1
      simp only [h1, h2, sub_self, hnadj, ↓reduceIte]
    · by_cases hdeg1 : G.Adj i j ∧ (G.neighborSet j).ncard = 1
      · have hdel : (G.deleteIncidenceSet i).IsIsolated j := hiff.mpr (Or.inr hdeg1)
        have h1 : X_ind j (G.deleteIncidenceSet i) = 1 := by exact Set.indicator_of_mem hdel 1
        have h2 : X_ind j G = 0 := by exact Set.indicator_of_notMem hiso 1
        simp only [h1, h2, sub_zero, hdeg1, and_self, ↓reduceIte]
      · have hndel : ¬ (G.deleteIncidenceSet i).IsIsolated j := by
          rw [hiff, not_or]
          exact ⟨hiso, hdeg1⟩
        have h1 : X_ind j (G.deleteIncidenceSet i) = 0 := by exact Set.indicator_of_notMem hndel 1
        have h2 : X_ind j G = 0 := by exact Set.indicator_of_notMem hiso 1
        simp only [h1, h2, sub_self, hdeg1, ↓reduceIte]
  have hsum_deg1 :
      (∑ j ∈ Finset.univ.erase i,
        (if G.Adj i j ∧ (G.neighborSet j).ncard = 1 then (1 : ℝ) else 0)) =
      ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ) := by
    rw [ncard_set_eq_sum_ite]
    have hi_zero : (if G.Adj i i ∧ (G.neighborSet i).ncard = 1 then (1 : ℝ) else 0) = 0 := by
      simp [SimpleGraph.irrefl]
    have htot := (Finset.sum_erase_add Finset.univ
      (fun j : Fin n ↦ if G.Adj i j ∧ (G.neighborSet j).ncard = 1 then (1 : ℝ) else 0)
      (Finset.mem_univ i)).symm
    simp only [mem_ofPred_eq]
    linarith
  calc
    (∑ k : Fin n, X_ind k (G.deleteIncidenceSet i)) - (∑ k : Fin n, X_ind k G)
      = (∑ j ∈ Finset.univ.erase i, (X_ind j (G.deleteIncidenceSet i) - X_ind j G)) +
          (1 - X_ind i G) := by
        rw [hsplit_del, hsplit_G, hi_del, Finset.sum_sub_distrib]
        ring
    _ = (∑ j ∈ Finset.univ.erase i,
          (if G.Adj i j ∧ (G.neighborSet j).ncard = 1 then (1 : ℝ) else 0)) +
          {K : SimpleGraph (Fin n) | 0 < (K.neighborSet i).ncard}.indicator
            (1 : SimpleGraph (Fin n) → ℝ) G := by
        rw [Finset.sum_congr rfl hj_diff, hi_diff]
    _ = ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ) +
          {K : SimpleGraph (Fin n) | 0 < (K.neighborSet i).ncard}.indicator
            (1 : SimpleGraph (Fin n) → ℝ) G := by
        rw [hsum_deg1]

/-- Example 3.9, size-bias realization and increment identity (`\label{ex72}`,
`SteinIntro.tex:1354-1367, 1380-1383`): erasing all edges incident to an independent uniform
vertex $I$ in $G \sim G(n, p)$ ($0 \le p < 1$) yields a size-biased version $X^s$ of the
isolated-vertex count $X$ with $X^s - X = D_I + \mathbf{1}_{d_I > 0}$. -/
theorem Ex3_9_sizeBias_proof :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {n : ℕ} (hn : 0 < n) {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {I : Ω → Fin n},
      0 ≤ p →
      p < 1 →
      Measurable G →
      P.map G = erdosRenyi n p →
      Measurable I →
      ProbabilityTheory.IndepFun I G P →
      P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
      let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
        fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
      let X : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i (G ω)
      let Xs : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i ((G ω).deleteIncidenceSet (I ω))
      let d : Fin n → Ω → ℕ := fun i ω ↦ ((G ω).neighborSet i).ncard
      let D : Fin n → Ω → ℝ :=
        fun i ω ↦ ({j : Fin n | (G ω).Adj i j ∧ ((G ω).neighborSet j).ncard = 1}.ncard : ℝ)
      IsSizeBias P X P Xs ∧
        ∀ ω : Ω, Xs ω - X ω = D (I ω) ω + {ω' : Ω | 0 < d (I ω') ω'}.indicator 1 ω := by
  intro Ω _ P _ n hn p G I hp0 hp1 hG_meas hG_law hI_meas hIG_indep hI_law
  dsimp only
  set X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
    fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
  set X : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i (G ω)
  set Xs : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i ((G ω).deleteIncidenceSet (I ω))
  set d : Fin n → Ω → ℕ := fun i ω ↦ ((G ω).neighborSet i).ncard
  set D : Fin n → Ω → ℝ :=
    fun i ω ↦ ({j : Fin n | (G ω).Adj i j ∧ ((G ω).neighborSet j).ncard = 1}.ncard : ℝ)
  refine ⟨?_, fun ω ↦ ?_⟩
  · let Xi : Fin n → Ω → ℝ := fun i ω ↦ X_ind i (G ω)
    let Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ) :=
      fun i ω j ↦ X_ind j.1 ((G ω).deleteIncidenceSet i)
    have hXi_meas : ∀ i : Fin n, Measurable (Xi i) :=
      fun i ↦ (measurable_of_finite (X_ind i)).comp hG_meas
    have hXi_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, Xi i ω = 0 ∨ Xi i ω = 1 := by
      intro i
      refine Eventually.of_forall fun ω ↦ ?_
      by_cases h : (G ω).IsIsolated i <;> simp [Xi, X_ind, h]
    have hXi_pre : ∀ i : Fin n,
        Xi i ⁻¹' {(1 : ℝ)} = G ⁻¹' {H : SimpleGraph (Fin n) | H.IsIsolated i} := by
      intro i
      ext ω
      by_cases h : (G ω).IsIsolated i <;> simp [Xi, X_ind, h]
    have hpi_eq : ∀ i : Fin n, P.real (Xi i ⁻¹' {(1 : ℝ)}) = (1 - p) ^ (n - 1) := by
      intro i
      rw [hXi_pre i,
        ← map_measureReal_apply hG_meas (MeasurableSet.of_discrete),
        hG_law, erdosRenyi_real_isIsolated hp0 hp1.le i]
    have hpi_pos : (0 : ℝ) < (1 - p) ^ (n - 1) := pow_pos (by linarith) (n - 1)
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hμ_eq : (∑ i : Fin n, P.real (Xi i ⁻¹' {(1 : ℝ)})) = (n : ℝ) * (1 - p) ^ (n - 1) := by
      simp [hpi_eq]
    have hμ_pos : 0 < ∑ i : Fin n, P.real (Xi i ⁻¹' {(1 : ℝ)}) := by
      rw [hμ_eq]
      positivity
    let Yi_graph : (i : Fin n) → SimpleGraph (Fin n) → ({j : Fin n // j ≠ i} → ℝ) :=
      fun i H j ↦ X_ind j.1 (H.deleteIncidenceSet i)
    let rest_graph : (i : Fin n) → SimpleGraph (Fin n) → ({j : Fin n // j ≠ i} → ℝ) :=
      fun i H j ↦ X_ind j.1 H
    have hYi_meas : ∀ i : Fin n, Measurable (Yi_graph i) := fun _ ↦ .of_discrete
    have hY_meas : ∀ i : Fin n, Measurable (Y i) := fun i ↦ (hYi_meas i).comp hG_meas
    have hY_law : ∀ i : Fin n, 0 < P.real (Xi i ⁻¹' {(1 : ℝ)}) →
        P.map (Y i) =
          (ProbabilityTheory.cond P (Xi i ⁻¹' {(1 : ℝ)})).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ Xi j.1 ω) := by
      intro i _
      have hrest_meas : Measurable (rest_graph i) := .of_discrete
      have hdel_meas : Measurable (fun H : SimpleGraph (Fin n) ↦ H.deleteIncidenceSet i) :=
        .of_discrete
      calc
        P.map (Y i)
          = (P.map G).map (Yi_graph i) := (Measure.map_map (hYi_meas i) hG_meas).symm
        _ = ((erdosRenyi n p).map (fun H ↦ H.deleteIncidenceSet i)).map (rest_graph i) := by
            rw [hG_law, Measure.map_map hrest_meas hdel_meas]
            rfl
        _ = (ProbabilityTheory.cond (erdosRenyi n p)
              {H : SimpleGraph (Fin n) | H.IsIsolated i}).map (rest_graph i) := by
            rw [← erdosRenyi_cond_isIsolated_eq_map_deleteIncidenceSet hp0 hp1 i]
        _ = ((ProbabilityTheory.cond P
              (G ⁻¹' {H : SimpleGraph (Fin n) | H.IsIsolated i})).map G).map (rest_graph i) := by
            rw [cond_preimage_map P hG_meas MeasurableSet.of_discrete, hG_law]
        _ = (ProbabilityTheory.cond P (Xi i ⁻¹' {(1 : ℝ)})).map
              (fun ω (j : {j : Fin n // j ≠ i}) ↦ Xi j.1 ω) := by
            rw [hXi_pre i, Measure.map_map hrest_meas hG_meas]
            rfl
    have hI_prob : ∀ i : Fin n,
        P.real (I ⁻¹' {i}) =
          P.real (Xi i ⁻¹' {(1 : ℝ)}) / ∑ k : Fin n, P.real (Xi k ⁻¹' {(1 : ℝ)}) := by
      intro i
      let unif : PMF (Fin n) := @PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩
      have hmapI : P.real (I ⁻¹' {i}) = (unif.toMeasure).real {i} := by
        rw [← map_measureReal_apply hI_meas (measurableSet_singleton i), hI_law]
      have hunif : (unif.toMeasure).real {i} = (n : ℝ)⁻¹ := by
        rw [measureReal_def, unif.toMeasure_apply_singleton i (measurableSet_singleton i)]
        simp [unif, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
      rw [hmapI, hunif, hpi_eq i, hμ_eq]
      field_simp [hn_pos.ne', hpi_pos.ne']
    let Φ : SimpleGraph (Fin n) →
        (Fin n → ℝ) × ((i : Fin n) → ({j : Fin n // j ≠ i} → ℝ)) :=
      fun H ↦ (fun i ↦ X_ind i H, fun i j ↦ X_ind j.1 (H.deleteIncidenceSet i))
    have hΦ_meas : Measurable Φ :=
      (Measurable.of_eval fun i ↦ measurable_of_finite _).prodMk
        (Measurable.of_eval fun i ↦ Measurable.of_eval fun j ↦ measurable_of_finite _)
    have hIndep : ProbabilityTheory.IndepFun I
        (fun ω ↦ (fun i ↦ Xi i ω, fun i ↦ Y i ω)) P :=
      hIG_indep.comp measurable_id hΦ_meas
    have hSB := sizeBias_sum_of_zero_one P hXi_meas hXi_zo hμ_pos
      (fun i ↦ (hY_meas i).aemeasurable) hY_law hI_meas hI_prob hIndep
    have hXs_eq : (fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1) = Xs := by
      funext ω
      have hsub : (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) =
          ∑ j ∈ Finset.univ.erase (I ω), X_ind j ((G ω).deleteIncidenceSet (I ω)) :=
        (Finset.sum_subtype (Finset.univ.erase (I ω)) (by simp)
          (fun j ↦ X_ind j ((G ω).deleteIncidenceSet (I ω)))).symm
      have hi_one : X_ind (I ω) ((G ω).deleteIncidenceSet (I ω)) = 1 :=
        Set.indicator_of_mem (deleteIncidenceSet_isIsolated_self (G ω) (I ω)) 1
      rw [hsub, ← hi_one, Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (I ω))]
    rwa [hXs_eq] at hSB
  · have hstep := deleteIncidenceSet_isolatedCount_sub (G ω) (I ω)
    have hind_eq :
        {K : SimpleGraph (Fin n) | 0 < (K.neighborSet (I ω)).ncard}.indicator
          (1 : SimpleGraph (Fin n) → ℝ) (G ω) =
          {ω' : Ω | 0 < d (I ω') ω'}.indicator (1 : Ω → ℝ) ω := by
      by_cases hpos : 0 < ((G ω).neighborSet (I ω)).ncard
      · have h1 : {K : SimpleGraph (Fin n) | 0 < (K.neighborSet (I ω)).ncard}.indicator
            (1 : SimpleGraph (Fin n) → ℝ) (G ω) = 1 := Set.indicator_of_mem hpos 1
        have h2 : {ω' : Ω | 0 < d (I ω') ω'}.indicator (1 : Ω → ℝ) ω = 1 :=
          Set.indicator_of_mem hpos 1
        exact h1.trans h2.symm
      · have h1 : {K : SimpleGraph (Fin n) | 0 < (K.neighborSet (I ω)).ncard}.indicator
            (1 : SimpleGraph (Fin n) → ℝ) (G ω) = 0 := Set.indicator_of_notMem hpos 1
        have h2 : {ω' : Ω | 0 < d (I ω') ω'}.indicator (1 : Ω → ℝ) ω = 0 :=
          Set.indicator_of_notMem hpos 1
        exact h1.trans h2.symm
    exact hstep.trans (congrArg (D (I ω) ω + ·) hind_eq)

end Ex3_9

end SteinMethod
