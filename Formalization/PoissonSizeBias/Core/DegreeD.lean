/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Core.DegreeDAux
import Formalization.PoissonSizeBias.Core.IsolatedVertices

/-!
# Degree-$d$ Vertices in Erdős–Rényi Graphs (`Formalization.PoissonSizeBias.Core.DegreeD`)

Formalizes the Erdős–Rényi neighborhood factorization, the conditional-law sanity witness
`erdosRenyi_bind_degreeDCouplingPMF_eq_cond`, and Example 4.6 (`degreeDVertices_coupling`,
`SteinIntro.tex:2220-2246`; `ISSUE-TYPO-EX4.6`), re-exporting `DegreeDAux` and `IsolatedVertices`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Erdős–Rényi factorization along `(G.deleteIncidenceSet v, G.neighborFinset v)` -/

open Classical in
private lemma erdosRenyi_real_replaceNeighbors {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {v : Fin n} {K : SimpleGraph (Fin n)} (hK : K.IsIsolated v)
    {S : Finset (Fin n)} (hS : S ⊆ Finset.univ.erase v) :
    (erdosRenyi n p).real {replaceNeighbors K v S} =
      (erdosRenyi n p).real ((fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet v) ⁻¹' {K}) *
        (p ^ S.card * (1 - p) ^ ((n - 1) - S.card)) := by
  let offPos : Finset (EdgePair n) :=
    Finset.univ.filter fun e : EdgePair n ↦ v ∉ e.1 ∧ e.1 ∈ K.edgeSet
  let offNeg : Finset (EdgePair n) :=
    Finset.univ.filter fun e : EdgePair n ↦ v ∉ e.1 ∧ e.1 ∉ K.edgeSet
  let incPos : Finset (EdgePair n) :=
    Finset.univ.filter fun e : EdgePair n ↦ ∃ hv : v ∈ e.1, Sym2.Mem.other hv ∈ S
  let incNeg : Finset (EdgePair n) :=
    Finset.univ.filter fun e : EdgePair n ↦ ∃ hv : v ∈ e.1, Sym2.Mem.other hv ∉ S
  have hpre_cyl : (fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet v) ⁻¹' {K} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ offPos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ offNeg, e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred, offPos, offNeg,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl
      refine ⟨fun e ⟨hv, he⟩ ↦ ?_, fun e ⟨hv, he⟩ hG ↦ he ?_⟩
      · rcases e with ⟨z, hz⟩
        refine Sym2.ind (fun x y hxy ↦ ?_) z hz hv he
        intro hv' he'
        simp only [Sym2.mem_iff, not_or] at hv'
        simp only [SimpleGraph.mem_edgeSet, SimpleGraph.deleteIncidenceSet_adj] at he'
        exact G.mem_edgeSet.mpr he'.1
      · rcases e with ⟨z, hz⟩
        refine Sym2.ind (fun x y hxy ↦ ?_) z hz hv hG
        intro hv' hG'
        simp only [Sym2.mem_iff, not_or] at hv'
        rw [SimpleGraph.mem_edgeSet, SimpleGraph.deleteIncidenceSet_adj]
        exact ⟨G.mem_edgeSet.mp hG', Ne.symm hv'.1, Ne.symm hv'.2⟩
    · rintro ⟨hpos, hneg⟩
      ext x y
      by_cases hxy : x = y
      · subst hxy; simp [SimpleGraph.irrefl]
      · rw [SimpleGraph.deleteIncidenceSet_adj]
        by_cases hxv : x = v
        · subst hxv
          exact iff_of_false (fun h ↦ h.2.1 rfl) (hK y)
        · by_cases hyv : y = v
          · subst hyv
            exact iff_of_false (fun h ↦ h.2.2 rfl) (fun h ↦ hK x h.symm)
          · let e : EdgePair n := ⟨s(x, y), by rwa [Sym2.mk_isDiag_iff]⟩
            have hv : v ∉ e.1 := by
              simp only [e, Sym2.mem_iff, not_or]
              exact ⟨Ne.symm hxv, Ne.symm hyv⟩
            by_cases hmem : e.1 ∈ K.edgeSet
            · exact iff_of_true ⟨G.mem_edgeSet.mp (hpos e ⟨hv, hmem⟩), hxv, hyv⟩
                (K.mem_edgeSet.mp hmem)
            · exact iff_of_false (fun h ↦ hneg e ⟨hv, hmem⟩ (G.mem_edgeSet.mpr h.1))
                (fun h ↦ hmem (K.mem_edgeSet.mpr h))
  have hsing_cyl : ({replaceNeighbors K v S} : Set (SimpleGraph (Fin n))) =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ offPos ∪ incPos, e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ offNeg ∪ incNeg, e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_singleton_iff, Set.mem_ofPred, Finset.mem_union]
    constructor
    · rintro rfl
      refine ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩
      · rcases he with he | he
        · simp only [offPos, Finset.mem_filter, Finset.mem_univ, true_and] at he
          rcases e with ⟨z, hz⟩
          refine Sym2.ind (fun x y _ ↦ ?_) z hz he
          rintro ⟨hv, hKxy⟩
          simp only [Sym2.mem_iff, not_or] at hv
          exact (replaceNeighbors K v S).mem_edgeSet.mpr
            ((replaceNeighbors_adj_off K (Ne.symm hv.1) (Ne.symm hv.2) S).mpr
              (K.mem_edgeSet.mp hKxy))
        · simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and] at he
          rcases he with ⟨hv, hother⟩
          let u := Sym2.Mem.other hv
          have he_eq : e.1 = s(v, u) := (Sym2.other_spec hv).symm
          rw [he_eq, SimpleGraph.mem_edgeSet, replaceNeighbors_adj_left]
          exact ⟨Finset.ne_of_mem_erase (hS hother), hother⟩
      · rcases he with he | he
        · simp only [offNeg, Finset.mem_filter, Finset.mem_univ, true_and] at he
          rcases e with ⟨z, hz⟩
          refine Sym2.ind (fun x y _ ↦ ?_) z hz he
          rintro ⟨hv, hKxy⟩ hmem
          simp only [Sym2.mem_iff, not_or] at hv
          have hadj := (replaceNeighbors_adj_off K (Ne.symm hv.1) (Ne.symm hv.2) S).mp
            ((replaceNeighbors K v S).mem_edgeSet.mp hmem)
          exact hKxy (K.mem_edgeSet.mpr hadj)
        · simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and] at he
          rcases he with ⟨hv, hother⟩
          intro hmem
          let u := Sym2.Mem.other hv
          have he_eq : e.1 = s(v, u) := (Sym2.other_spec hv).symm
          rw [he_eq, SimpleGraph.mem_edgeSet, replaceNeighbors_adj_left] at hmem
          exact hother hmem.2
    · rintro ⟨hpos, hneg⟩
      ext x y
      by_cases hxy : x = y
      · subst hxy; simp [SimpleGraph.irrefl]
      · by_cases hxv : x = v
        · subst hxv
          rw [replaceNeighbors_adj_left]
          let e : EdgePair n := ⟨s(x, y), by rwa [Sym2.mk_isDiag_iff]⟩
          have hv : x ∈ e.1 := Sym2.mem_mk_left x y
          have hother_eq : Sym2.Mem.other hv = y :=
            Sym2.congr_right.mp (Sym2.other_spec hv)
          by_cases hyS : y ∈ S
          · have he_in : e ∈ incPos := by
              simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hv, hother_eq.symm ▸ hyS⟩
            exact iff_of_true (G.mem_edgeSet.mp (hpos e (Or.inr he_in))) ⟨Ne.symm hxy, hyS⟩
          · have he_in : e ∈ incNeg := by
              simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hv, hother_eq.symm ▸ hyS⟩
            exact iff_of_false (fun h ↦ hneg e (Or.inr he_in) (G.mem_edgeSet.mpr h))
              (fun h ↦ hyS h.2)
        · by_cases hyv : y = v
          · subst hyv
            rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (replaceNeighbors K y S),
              replaceNeighbors_adj_left]
            let e : EdgePair n := ⟨s(x, y), by rwa [Sym2.mk_isDiag_iff]⟩
            let e' : EdgePair n := ⟨s(y, x), by simpa [Sym2.mk_isDiag_iff] using Ne.symm hxy⟩
            have he_eq : e' = e := Subtype.ext Sym2.eq_swap
            have hv : y ∈ e'.1 := Sym2.mem_mk_left y x
            have hother_eq : Sym2.Mem.other hv = x :=
              Sym2.congr_right.mp (Sym2.other_spec hv)
            by_cases hxS : x ∈ S
            · have he_in : e' ∈ incPos := by
                simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hv, hother_eq.symm ▸ hxS⟩
              have he_in' : e ∈ incPos := he_eq ▸ he_in
              have hmem_e' : e'.1 ∈ G.edgeSet := by
                rw [he_eq]
                exact hpos e (Or.inr he_in')
              exact iff_of_true (G.mem_edgeSet.mp hmem_e') ⟨hxv, hxS⟩
            · have he_in : e' ∈ incNeg := by
                simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hv, hother_eq.symm ▸ hxS⟩
              have he_in' : e ∈ incNeg := he_eq ▸ he_in
              exact iff_of_false
                (fun h ↦ hneg e (Or.inr he_in') (by
                  rw [← he_eq]
                  exact G.mem_edgeSet.mpr h))
                (fun h ↦ hxS h.2)
          · let e : EdgePair n := ⟨s(x, y), by rwa [Sym2.mk_isDiag_iff]⟩
            rw [replaceNeighbors_adj_off K hxv hyv S]
            have hv : v ∉ e.1 := by
              simp only [e, Sym2.mem_iff, not_or]
              exact ⟨Ne.symm hxv, Ne.symm hyv⟩
            by_cases hmem : e.1 ∈ K.edgeSet
            · exact iff_of_true (G.mem_edgeSet.mp (hpos e (Or.inl (by simp [offPos, hv, hmem]))))
                (K.mem_edgeSet.mp hmem)
            · exact iff_of_false
                (fun h ↦ hneg e (Or.inl (by simp [offNeg, hv, hmem])) (G.mem_edgeSet.mpr h))
                (fun h ↦ hmem (K.mem_edgeSet.mpr h))
  have hdisj_off : Disjoint offPos offNeg :=
    Finset.disjoint_filter.mpr fun _ _ h1 h2 ↦ h2.2 h1.2
  have hdisj_pos_inc : Disjoint offPos incPos :=
    Finset.disjoint_filter.mpr fun _ _ h1 ⟨hv, _⟩ ↦ h1.1 hv
  have hdisj_neg_inc : Disjoint offNeg incNeg :=
    Finset.disjoint_filter.mpr fun _ _ h1 ⟨hv, _⟩ ↦ h1.1 hv
  have hdisj_all : Disjoint (offPos ∪ incPos) (offNeg ∪ incNeg) := by
    refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr ⟨hdisj_off, ?_⟩,
      Finset.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
    · exact Finset.disjoint_filter.mpr fun _ _ h1 ⟨hv, _⟩ ↦ h1.1 hv
    · exact Finset.disjoint_filter.mpr fun _ _ ⟨hv, _⟩ h2 ↦ h2.1 hv
    · exact Finset.disjoint_filter.mpr fun _ _ ⟨_, h1⟩ ⟨_, h2⟩ ↦ h2 h1
  have hcard_incPos : incPos.card = S.card := by
    symm
    refine Finset.card_bij
      (fun u hu ↦ ⟨s(v, u), by
        rw [Sym2.mk_isDiag_iff]
        exact (Finset.ne_of_mem_erase (hS hu)).symm⟩)
      (fun u hu ↦ ?_)
      (fun u₁ _ u₂ _ h ↦ Sym2.congr_right.mp (Subtype.ext_iff.mp h))
      (fun e he ↦ ?_)
    · simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Sym2.mem_mk_left v u, ?_⟩
      have hoth : Sym2.Mem.other (Sym2.mem_mk_left v u) = u :=
        Sym2.congr_right.mp (Sym2.other_spec (Sym2.mem_mk_left v u))
      rwa [hoth]
    · simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases he with ⟨hv, hoth⟩
      exact ⟨Sym2.Mem.other hv, hoth, Subtype.ext (Sym2.other_spec hv)⟩
  have hcard_incNeg : incNeg.card = (n - 1) - S.card := by
    have hbij : (Finset.univ.erase v \ S).card = incNeg.card := by
      refine Finset.card_bij
        (fun u hu ↦ ⟨s(v, u), by
          rw [Sym2.mk_isDiag_iff]
          exact (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hu).1).symm⟩)
        (fun u hu ↦ ?_)
        (fun u₁ _ u₂ _ h ↦ Sym2.congr_right.mp (Subtype.ext_iff.mp h))
        (fun e he ↦ ?_)
      · simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Sym2.mem_mk_left v u, ?_⟩
        have hoth : Sym2.Mem.other (Sym2.mem_mk_left v u) = u :=
          Sym2.congr_right.mp (Sym2.other_spec (Sym2.mem_mk_left v u))
        rw [hoth]
        exact (Finset.mem_sdiff.mp hu).2
      · simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases he with ⟨hv, hoth⟩
        refine ⟨Sym2.Mem.other hv, ?_, Subtype.ext (Sym2.other_spec hv)⟩
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_erase.mpr ⟨Sym2.other_ne e.2 hv, Finset.mem_univ _⟩, hoth⟩
    rw [← hbij, Finset.card_sdiff_of_subset hS, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin]
  rw [hsing_cyl, hpre_cyl,
    erdosRenyi_real_cylinder hp0 hp1 (offPos ∪ incPos) (offNeg ∪ incNeg) hdisj_all,
    erdosRenyi_real_cylinder hp0 hp1 offPos offNeg hdisj_off,
    Finset.card_union_of_disjoint hdisj_pos_inc,
    Finset.card_union_of_disjoint hdisj_neg_inc,
    hcard_incPos, hcard_incNeg, pow_add, pow_add]
  ring

open Classical in
private lemma erdosRenyi_real_neighborFinset {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {v : Fin n} {S : Finset (Fin n)} (hS : S ⊆ Finset.univ.erase v) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | G.neighborFinset v = S} =
      p ^ S.card * (1 - p) ^ ((n - 1) - S.card) := by
  let incPos : Finset (EdgePair n) :=
    Finset.univ.filter fun e : EdgePair n ↦ ∃ hv : v ∈ e.1, Sym2.Mem.other hv ∈ S
  let incNeg : Finset (EdgePair n) :=
    Finset.univ.filter fun e : EdgePair n ↦ ∃ hv : v ∈ e.1, Sym2.Mem.other hv ∉ S
  have hdisj : Disjoint incPos incNeg :=
    Finset.disjoint_filter.mpr fun _ _ ⟨_, h1⟩ ⟨_, h2⟩ ↦ h2 h1
  have hcyl : {G : SimpleGraph (Fin n) | G.neighborFinset v = S} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ incPos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ incNeg, e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_ofPred]
    constructor
    · rintro rfl
      refine ⟨fun e he ↦ ?_, fun e he hmem ↦ ?_⟩
      · simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases he with ⟨hv, hoth⟩
        rw [SimpleGraph.mem_neighborFinset] at hoth
        rw [← Sym2.other_spec hv, SimpleGraph.mem_edgeSet]
        exact hoth
      · simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases he with ⟨hv, hoth⟩
        rw [← Sym2.other_spec hv, SimpleGraph.mem_edgeSet] at hmem
        exact hoth ((SimpleGraph.mem_neighborFinset G v _).mpr hmem)
    · rintro ⟨hpos, hneg⟩
      ext u
      rw [SimpleGraph.mem_neighborFinset]
      by_cases huv : u = v
      · subst huv
        exact iff_of_false (G.loopless.irrefl u) (fun hu ↦ Finset.ne_of_mem_erase (hS hu) rfl)
      · let e : EdgePair n := ⟨s(v, u), by simpa [Sym2.mk_isDiag_iff] using Ne.symm huv⟩
        have hv : v ∈ e.1 := Sym2.mem_mk_left v u
        have hoth : Sym2.Mem.other hv = u := Sym2.congr_right.mp (Sym2.other_spec hv)
        by_cases huS : u ∈ S
        · have he_in : e ∈ incPos := by
            simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hv, hoth.symm ▸ huS⟩
          exact iff_of_true (G.mem_edgeSet.mp (hpos e he_in)) huS
        · have he_in : e ∈ incNeg := by
            simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hv, hoth.symm ▸ huS⟩
          exact iff_of_false (fun h ↦ hneg e he_in (G.mem_edgeSet.mpr h)) huS
  have hcard_pos : incPos.card = S.card := by
    symm
    refine Finset.card_bij
      (fun u hu ↦ ⟨s(v, u), by
        rw [Sym2.mk_isDiag_iff]; exact (Finset.ne_of_mem_erase (hS hu)).symm⟩)
      (fun u hu ↦ by
        simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨Sym2.mem_mk_left v u, ?_⟩
        rwa [Sym2.congr_right.mp (Sym2.other_spec (Sym2.mem_mk_left v u))])
      (fun u₁ _ u₂ _ h ↦ Sym2.congr_right.mp (Subtype.ext_iff.mp h))
      (fun e he ↦ by
        simp only [incPos, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases he with ⟨hv, hoth⟩
        exact ⟨Sym2.Mem.other hv, hoth, Subtype.ext (Sym2.other_spec hv)⟩)
  have hcard_neg : incNeg.card = (n - 1) - S.card := by
    have hbij : (Finset.univ.erase v \ S).card = incNeg.card := by
      refine Finset.card_bij
        (fun u hu ↦ ⟨s(v, u), by
          rw [Sym2.mk_isDiag_iff]
          exact (Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hu).1).symm⟩)
        (fun u hu ↦ by
          simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨Sym2.mem_mk_left v u, ?_⟩
          rw [Sym2.congr_right.mp (Sym2.other_spec (Sym2.mem_mk_left v u))]
          exact (Finset.mem_sdiff.mp hu).2)
        (fun u₁ _ u₂ _ h ↦ Sym2.congr_right.mp (Subtype.ext_iff.mp h))
        (fun e he ↦ by
          simp only [incNeg, Finset.mem_filter, Finset.mem_univ, true_and] at he
          rcases he with ⟨hv, hoth⟩
          refine ⟨Sym2.Mem.other hv, ?_, Subtype.ext (Sym2.other_spec hv)⟩
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_erase.mpr ⟨Sym2.other_ne e.2 hv, Finset.mem_univ _⟩, hoth⟩)
    rw [← hbij, Finset.card_sdiff_of_subset hS, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin]
  rw [hcyl, erdosRenyi_real_cylinder hp0 hp1 incPos incNeg hdisj, hcard_pos, hcard_neg]

/-! ### Exact conditional graph law of `degreeDCouplingPMF` -/

private instance instIsProbabilityMeasureBindDegreeD {n d : ℕ} (v : Fin n)
    (P : Measure (SimpleGraph (Fin n))) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (P.bind fun G ↦ (degreeDCouplingPMF d v G).toMeasure) := by
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ
    (measurable_of_finite fun G : SimpleGraph (Fin n) ↦
      (degreeDCouplingPMF d v G).toMeasure).aemeasurable]
  simp

/-- Whenever `d < n`, `0 ≤ p ≤ 1`, and `ℙ_{G ~ G(n, p)}(deg(v) = d) > 0`, sampling from
`degreeDCouplingPMF d v G` for `G ~ erdosRenyi n p` produces the exact conditional graph law
`cond (erdosRenyi n p) {G | (G.neighborSet v).ncard = d}` (`SteinIntro.tex:2227-2239`). -/
theorem erdosRenyi_bind_degreeDCouplingPMF_eq_cond
    {n d : ℕ} (hd : d < n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : Fin n)
    (hpos : 0 < (erdosRenyi n p).real {G : SimpleGraph (Fin n) | (G.neighborSet v).ncard = d}) :
    (erdosRenyi n p).bind (fun G ↦ (degreeDCouplingPMF d v G).toMeasure) =
      ProbabilityTheory.cond (erdosRenyi n p)
        {G : SimpleGraph (Fin n) | (G.neighborSet v).ncard = d} := by
  classical
  let P := erdosRenyi n p
  let Q := P.bind fun G ↦ (degreeDCouplingPMF d v G).toMeasure
  let S_deg : Set (SimpleGraph (Fin n)) := {G | (G.neighborSet v).ncard = d}
  let cards := (Finset.univ.erase v).powersetCard d
  let pows := (Finset.univ.erase v).powerset
  let w : Finset (Fin n) → ℝ := fun T ↦
    ∑ S ∈ pows, (p ^ S.card * (1 - p) ^ ((n - 1) - S.card)) *
      ((nbrCouplingPMF n d v S) T).toReal
  have hw_perm : ∀ {σ : Equiv.Perm (Fin n)}, σ v = v → ∀ T : Finset (Fin n),
      w (T.image σ) = w T := by
    intro σ hσv T
    have herase_im : (Finset.univ.erase v).image σ = Finset.univ.erase v := by
      ext x
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun ⟨y, hyv, hyx⟩ ↦ hyx ▸ fun h ↦ hyv (σ.injective (h.trans hσv.symm)),
        fun hxv ↦ ⟨σ.symm x, fun h ↦ hxv (by simpa [hσv] using congrArg σ h),
          σ.apply_symm_apply x⟩⟩
    symm
    refine Finset.sum_bij (fun S _ ↦ S.image σ)
      (fun S hS ↦ by
        rw [Finset.mem_powerset] at hS ⊢
        exact (Finset.image_subset_image hS).trans (le_of_eq herase_im))
      (fun S₁ _ S₂ _ h ↦ by
        have := congrArg (fun A ↦ A.image σ.symm) h
        simpa [Finset.image_image] using this)
      (fun S hS ↦ ⟨S.image σ.symm, ?_, by ext x; simp⟩)
      (fun S hS ↦ ?_)
    · rw [Finset.mem_powerset] at hS ⊢
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hyS, rfl⟩
      have hyv : y ≠ v := Finset.ne_of_mem_erase (hS hyS)
      exact Finset.mem_erase.mpr
        ⟨fun h ↦ hyv (by simpa [hσv] using congrArg σ h), Finset.mem_univ _⟩
    · have hS_sub : S ⊆ Finset.univ.erase v := Finset.mem_powerset.mp hS
      rw [Finset.card_image_of_injective S σ.injective,
        nbrCouplingPMF_perm_eq hσv hS_sub T]
  have hw_sum_one : ∑ T ∈ cards, w T = 1 := by
    dsimp only [w]
    rw [Finset.sum_comm]
    have hinner : ∀ S ∈ pows,
        ∑ T ∈ cards, ((nbrCouplingPMF n d v S) T).toReal = 1 := by
      intro S hS
      have hS_sub : S ⊆ Finset.univ.erase v := Finset.mem_powerset.mp hS
      have htsum : (∑' T : Finset (Fin n), (nbrCouplingPMF n d v S) T) = 1 :=
        (nbrCouplingPMF n d v S).tsum_coe
      rw [tsum_fintype] at htsum
      have hfin_eq : (∑ T : Finset (Fin n), (nbrCouplingPMF n d v S) T) =
          ∑ T ∈ cards, (nbrCouplingPMF n d v S) T := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun T _ hT_not ↦ ?_
        by_contra hne0
        exact hT_not (nbrCouplingPMF_support_subset_powersetCard hd v hS_sub hne0)
      rw [hfin_eq] at htsum
      have htoReal := congrArg ENNReal.toReal htsum
      rwa [ENNReal.toReal_sum (fun T _ ↦ PMF.apply_ne_top _ T), ENNReal.toReal_one] at htoReal
    have hmul_sum : ∀ S ∈ pows,
        (∑ T ∈ cards, (p ^ S.card * (1 - p) ^ ((n - 1) - S.card)) *
          ((nbrCouplingPMF n d v S) T).toReal) =
        p ^ S.card * (1 - p) ^ ((n - 1) - S.card) := by
      intro S hS
      rw [← Finset.mul_sum, hinner S hS, mul_one]
    rw [Finset.sum_congr rfl hmul_sum]
    have hprob_sum : ∑ S ∈ pows, (p ^ S.card * (1 - p) ^ ((n - 1) - S.card)) =
        P.real (⋃ S ∈ pows, {G : SimpleGraph (Fin n) | G.neighborFinset v = S}) := by
      rw [measureReal_biUnion_finset
        (fun S₁ _ S₂ _ hne ↦ Set.disjoint_left.mpr fun G h1 h2 ↦ hne (h1.symm.trans h2))
        (fun _ _ ↦ MeasurableSet.of_discrete)]
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      exact (erdosRenyi_real_neighborFinset hp0 hp1 (Finset.mem_powerset.mp hS)).symm
    have huniv : (⋃ S ∈ pows, {G : SimpleGraph (Fin n) | G.neighborFinset v = S}) = Set.univ := by
      ext G
      simp only [Set.mem_iUnion, Set.mem_ofPred, Set.mem_univ, iff_true]
      exact ⟨G.neighborFinset v, Finset.mem_powerset.mpr (neighborFinset_subset_erase G v), rfl⟩
    rw [hprob_sum, huniv, probReal_univ]
  have hcards_ne : cards.Nonempty := by
    refine Finset.powersetCard_nonempty.mpr ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    omega
  have hw_val : ∀ T ∈ cards, w T = (cards.card : ℝ)⁻¹ := by
    intro T hT
    have hconst : ∀ T' ∈ cards, w T' = w T := by
      intro T' hT'
      obtain ⟨σ, hσv, him⟩ := exists_perm_fixing_and_image_eq hT hT'
      rw [← him, hw_perm hσv T]
    have hsum_eq : (∑ T' ∈ cards, w T') = (cards.card : ℝ) * w T := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rw [hw_sum_one] at hsum_eq
    have hcard_pos : (0 : ℝ) < cards.card := Nat.cast_pos.mpr hcards_ne.card_pos
    exact eq_inv_of_mul_eq_one_right hsum_eq.symm
  have hS_deg_prob : P.real S_deg = (cards.card : ℝ) * (p ^ d * (1 - p) ^ ((n - 1) - d)) := by
    have hunion : S_deg = ⋃ T ∈ cards, {G : SimpleGraph (Fin n) | G.neighborFinset v = T} := by
      ext G
      simp only [S_deg, Set.mem_ofPred, Set.mem_iUnion]
      constructor
      · intro hdeg
        refine ⟨G.neighborFinset v, Finset.mem_powersetCard.mpr
          ⟨neighborFinset_subset_erase G v, ?_⟩, rfl⟩
        rwa [← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
      · rintro ⟨T, hT, hGT⟩
        obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hT
        have hset : G.neighborSet v = (T : Set (Fin n)) := by
          rw [← SimpleGraph.coe_neighborFinset, hGT]
        rw [hset, Set.ncard_coe_finset, hcard]
    rw [hunion, measureReal_biUnion_finset
      (fun T₁ _ T₂ _ hne ↦ Set.disjoint_left.mpr fun G h1 h2 ↦ hne (h1.symm.trans h2))
      (fun _ _ ↦ MeasurableSet.of_discrete)]
    have hterm : ∀ T ∈ cards,
        P.real {G : SimpleGraph (Fin n) | G.neighborFinset v = T} =
          p ^ d * (1 - p) ^ ((n - 1) - d) := by
      intro T hT
      obtain ⟨hT_sub, hT_card⟩ := Finset.mem_powersetCard.mp hT
      rw [erdosRenyi_real_neighborFinset hp0 hp1 hT_sub, hT_card]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  refine Measure.ext_of_singleton fun H ↦ ?_
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top Q {H})
    (measure_ne_top (ProbabilityTheory.cond P S_deg) {H})).mp ?_
  have hQ_sing : Q.real {H} =
      ∑ G : SimpleGraph (Fin n), P.real {G} * ((degreeDCouplingPMF d v G) H).toReal := by
    dsimp only [Q, Measure.real]
    rw [Measure.bind_apply (measurableSet_singleton H)
      (measurable_of_finite fun G : SimpleGraph (Fin n) ↦
        (degreeDCouplingPMF d v G).toMeasure).aemeasurable,
      lintegral_fintype,
      ENNReal.toReal_sum (s := Finset.univ)
        (fun G _ ↦ ENNReal.mul_ne_top (measure_ne_top _ {H}) (measure_ne_top P {G}))]
    refine Finset.sum_congr rfl fun G _ ↦ ?_
    rw [ENNReal.toReal_mul, PMF.toMeasure_apply_singleton _ H MeasurableSet.of_discrete, mul_comm]
  have hcond_sing : (ProbabilityTheory.cond P S_deg).real {H} =
      (P.real S_deg)⁻¹ * P.real (S_deg ∩ {H}) := by
    simp [Measure.real, ProbabilityTheory.cond_apply MeasurableSet.of_discrete P {H},
      ENNReal.toReal_mul, ENNReal.toReal_inv]
  by_cases hH_deg : (H.neighborSet v).ncard = d
  · let K := H.deleteIncidenceSet v
    let T := H.neighborFinset v
    have hK_iso : K.IsIsolated v :=
      fun u hadj ↦ (SimpleGraph.deleteIncidenceSet_adj.mp hadj).2.1 rfl
    have hT_sub : T ⊆ Finset.univ.erase v := neighborFinset_subset_erase H v
    have hT_card : T.card = d := by
      rwa [← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
    have hT_cards : T ∈ cards := Finset.mem_powersetCard.mpr ⟨hT_sub, hT_card⟩
    have hH_rep : H = replaceNeighbors K v T := (self_eq_replaceNeighbors H v).symm
    have hQ_calc : Q.real {H} =
        P.real ((fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet v) ⁻¹' {K}) * w T := by
      rw [hQ_sing]
      have hterm : ∀ G : SimpleGraph (Fin n),
          ((degreeDCouplingPMF d v G) H).toReal =
            if G.deleteIncidenceSet v = K then
              ((nbrCouplingPMF n d v (G.neighborFinset v)) T).toReal
            else 0 := by
        intro G
        rw [degreeDCouplingPMF_eq_map_nbrCouplingPMF, PMF.map_apply, tsum_fintype]
        by_cases hGK : G.deleteIncidenceSet v = K
        · simp only [hGK, ↓reduceIte]
          have hsum_eq : (∑ T' : Finset (Fin n),
              if H = replaceNeighbors K v T' then
                (nbrCouplingPMF n d v (G.neighborFinset v)) T'
              else 0) = (nbrCouplingPMF n d v (G.neighborFinset v)) T := by
            rw [Finset.sum_eq_single T]
            · simp only [← hH_rep, ↓reduceIte]
            · intro T' _ hT'ne
              by_cases hsupp : T' ∈ (nbrCouplingPMF n d v (G.neighborFinset v)).support
              · have hneEq : H ≠ replaceNeighbors K v T' := by
                  intro hEq
                  have hT'_sub : T' ⊆ Finset.univ.erase v := (Finset.mem_powersetCard.mp
                    (nbrCouplingPMF_support_subset_powersetCard hd v
                      (neighborFinset_subset_erase G v) hsupp)).1
                  have hinj := replaceNeighbors_inj hK_iso hK_iso hT_sub hT'_sub
                    (hH_rep.symm.trans hEq)
                  exact hT'ne hinj.2.symm
                simp only [hneEq, ↓reduceIte]
              · have h0 : (nbrCouplingPMF n d v (G.neighborFinset v)) T' = 0 := by
                  rwa [PMF.mem_support_iff, not_not] at hsupp
                simp [h0]
            · intro hnot
              exact absurd (Finset.mem_univ T) hnot
          rw [hsum_eq]
        · simp only [hGK, ↓reduceIte]
          have hsum_zero : (∑ T' : Finset (Fin n),
              if H = replaceNeighbors (G.deleteIncidenceSet v) v T' then
                (nbrCouplingPMF n d v (G.neighborFinset v)) T'
              else 0) = 0 := by
            refine Finset.sum_eq_zero fun T' _ ↦ ?_
            have hneEq : H ≠ replaceNeighbors (G.deleteIncidenceSet v) v T' := by
              intro hEq
              have hdel_eq := congrArg (fun M ↦ M.deleteIncidenceSet v) hEq
              rw [deleteIncidenceSet_replaceNeighbors] at hdel_eq
              have hdel_idem : (G.deleteIncidenceSet v).deleteIncidenceSet v =
                  G.deleteIncidenceSet v := by
                ext x y
                rw [SimpleGraph.deleteIncidenceSet_adj]
                refine ⟨fun h ↦ h.1, fun hxy ↦ ⟨hxy, ?_, ?_⟩⟩
                · rintro rfl
                  exact (SimpleGraph.deleteIncidenceSet_adj.mp hxy).2.1 rfl
                · rintro rfl
                  exact (SimpleGraph.deleteIncidenceSet_adj.mp hxy).2.2 rfl
              rw [hdel_idem] at hdel_eq
              exact hGK hdel_eq.symm
            simp only [hneEq, ↓reduceIte]
          rw [hsum_zero, ENNReal.toReal_zero]
      simp_rw [hterm]
      have hsum_filter :
          (∑ G : SimpleGraph (Fin n),
            P.real {G} *
              (if G.deleteIncidenceSet v = K then
                ((nbrCouplingPMF n d v (G.neighborFinset v)) T).toReal
              else 0)) =
          ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet v = K),
            P.real {G} * ((nbrCouplingPMF n d v (G.neighborFinset v)) T).toReal := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun G _ ↦ ?_
        by_cases hGK : G.deleteIncidenceSet v = K <;> simp [hGK]
      rw [hsum_filter]
      have hbij :
          (∑ G ∈ Finset.univ.filter (fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet v = K),
            P.real {G} * ((nbrCouplingPMF n d v (G.neighborFinset v)) T).toReal) =
          ∑ S ∈ pows,
            (P.real ((fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet v) ⁻¹' {K}) *
              (p ^ S.card * (1 - p) ^ ((n - 1) - S.card))) *
              ((nbrCouplingPMF n d v S) T).toReal := by
        symm
        refine Finset.sum_bij (fun S _ ↦ replaceNeighbors K v S)
          (fun S _ ↦ ?_)
          (fun S₁ hS₁ S₂ hS₂ h ↦ (replaceNeighbors_inj hK_iso hK_iso
            (Finset.mem_powerset.mp hS₁) (Finset.mem_powerset.mp hS₂) h).2)
          (fun G hG ↦ ?_)
          (fun S hS ↦ ?_)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [deleteIncidenceSet_replaceNeighbors]
          ext x y
          rw [SimpleGraph.deleteIncidenceSet_adj]
          refine ⟨fun h ↦ h.1, fun hxy ↦ ⟨hxy, ?_, ?_⟩⟩
          · rintro rfl; exact hK_iso y hxy
          · rintro rfl; exact hK_iso x hxy.symm
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
          refine ⟨G.neighborFinset v, Finset.mem_powerset.mpr (neighborFinset_subset_erase G v), ?_⟩
          rw [← hG]
          exact self_eq_replaceNeighbors G v
        · have hS_sub : S ⊆ Finset.univ.erase v := Finset.mem_powerset.mp hS
          rw [replaceNeighbors_neighborFinset K v hS_sub,
            erdosRenyi_real_replaceNeighbors hp0 hp1 hK_iso hS_sub]
      rw [hbij]
      dsimp only [w]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ ↦ ?_
      ring
    have hS_inter : S_deg ∩ {H} = {H} :=
      Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hH_deg)
    have hPH : P.real {H} =
        P.real ((fun G : SimpleGraph (Fin n) ↦ G.deleteIncidenceSet v) ⁻¹' {K}) *
          (p ^ d * (1 - p) ^ ((n - 1) - d)) := by
      have h := erdosRenyi_real_replaceNeighbors hp0 hp1 hK_iso hT_sub
      rwa [← hH_rep, hT_card] at h
    have hq_ne : p ^ d * (1 - p) ^ ((n - 1) - d) ≠ 0 := by
      intro hq0
      have h0 : P.real S_deg = 0 := by rw [hS_deg_prob, hq0, mul_zero]
      linarith
    have hp_ne : p ^ d ≠ 0 := left_ne_zero_of_mul hq_ne
    have h1p_ne : (1 - p) ^ ((n - 1) - d) ≠ 0 := right_ne_zero_of_mul hq_ne
    have hcard_ne : (cards.card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hcards_ne.card_pos.ne'
    rw [hQ_calc, hw_val T hT_cards, hcond_sing, hS_inter, hPH, hS_deg_prob]
    field_simp [hp_ne, h1p_ne, hcard_ne]
  · have hQ0 : Q.real {H} = 0 := by
      rw [hQ_sing]
      refine Finset.sum_eq_zero fun G _ ↦ ?_
      have h0 : (degreeDCouplingPMF d v G) H = 0 := by
        by_contra hne0
        have hsupp : H ∈ (degreeDCouplingPMF d v G).support :=
          (PMF.mem_support_iff _ _).mpr hne0
        exact hH_deg (degreeDCouplingPMF_ncard_neighborSet hd v G hsupp)
      simp [h0]
    have hcond0 : (ProbabilityTheory.cond P S_deg).real {H} = 0 := by
      rw [hcond_sing]
      have hempty : S_deg ∩ {H} = ∅ := by
        ext M
        simp only [S_deg, Set.mem_inter_iff, Set.mem_ofPred, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro hdeg rfl
        exact hH_deg hdeg
      simp [hempty]
    rw [hQ0, hcond0]

/-! ### Example 4.6: Size-bias coupling for degree-$d$ vertex counts -/

/-- **Example 4.6** (*Degree $d$ vertices*, `SteinIntro.tex:2220-2246`; `ISSUE-TYPO-EX4.6`
correcting `L2240` to degree-$d$ vertices): in $G \sim G(n, p)$ ($0 < n$, $d < n$,
$0 \le p \le 1$), sampling $G^{(1)}$ from `degreeDCouplingPMF d ⟨0, hn⟩ G` forces
$\deg_{G^{(1)}}(v_1) = d$, yields coupled degree-$d$ indicators $(X_j^{(1)})_{j \ne 1}$ having
the conditional distribution of $(X_j)_{j \ne 1}$ given $X_1 = 1$ whenever
$\mathbb{P}(X_1 = 1) > 0$, and gives a size-bias representation
$W^s = \sum_{j \ne 1} X_j^{(1)} + 1$ of the degree-$d$ vertex count $W = \sum_{i=1}^n X_i$. -/
theorem degreeDVertices_coupling
    {n d : ℕ} (hn : 0 < n) (hd : d < n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let v0 : Fin n := ⟨0, hn⟩
    let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
    let Q : Measure (SimpleGraph (Fin n)) :=
      P.bind fun G ↦ (degreeDCouplingPMF d v0 G).toMeasure
    let X : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i G ↦ {H : SimpleGraph (Fin n) | (H.neighborSet i).ncard = d}.indicator 1 G
    let W : SimpleGraph (Fin n) → ℝ := fun G ↦ ∑ i : Fin n, X i G
    let Ws : SimpleGraph (Fin n) → ℝ :=
      fun G1 ↦ (∑ j : {j : Fin n // j ≠ v0}, X j.1 G1) + 1
    (∀ G : SimpleGraph (Fin n), ∀ H ∈ (degreeDCouplingPMF d v0 G).support,
      (H.neighborSet v0).ncard = d) ∧
    (0 < P.real {G | X v0 G = 1} →
      Q.map (fun G1 (j : {j : Fin n // j ≠ v0}) ↦ X j.1 G1) =
        (ProbabilityTheory.cond P {G | X v0 G = 1}).map
          (fun G (j : {j : Fin n // j ≠ v0}) ↦ X j.1 G)) ∧
    IsSizeBias P W Q Ws := by
  intro v0 P Q X W Ws
  have hS_eq : {G : SimpleGraph (Fin n) | X v0 G = 1} =
      {G : SimpleGraph (Fin n) | (G.neighborSet v0).ncard = d} := by
    ext G
    by_cases h : (G.neighborSet v0).ncard = d <;> simp [X, h]
  have hcond : 0 < P.real {G | X v0 G = 1} →
      Q.map (fun G1 (j : {j : Fin n // j ≠ v0}) ↦ X j.1 G1) =
        (ProbabilityTheory.cond P {G | X v0 G = 1}).map
          (fun G (j : {j : Fin n // j ≠ v0}) ↦ X j.1 G) := by
    intro hpos
    rw [hS_eq] at hpos ⊢
    have hQ_eq : Q = ProbabilityTheory.cond P {G | (G.neighborSet v0).ncard = d} :=
      erdosRenyi_bind_degreeDCouplingPMF_eq_cond hd hp0 hp1 v0 hpos
    rw [hQ_eq]
  have hX_meas : ∀ i : Fin n, Measurable (X i) := fun _ ↦ measurable_of_finite _
  have hX_zo : ∀ i : Fin n, ∀ᵐ G ∂P, X i G = 0 ∨ X i G = 1 := fun i ↦
    Eventually.of_forall fun G ↦ by
      by_cases h : (G.neighborSet i).ncard = d
      · exact Or.inr (Set.indicator_of_mem h 1)
      · exact Or.inl (Set.indicator_of_notMem h 1)
  have hexch : IsExchangeableTuple P X := by
    refine isExchangeableTuple_of_permGraph_invariant P hp0 hp1 measurable_id.aemeasurable
      Measure.map_id (φ := fun H i ↦ X i H) ?_
    intro σ H i
    dsimp [X]
    by_cases h : (H.neighborSet i).ncard = d
    · have h' : ((permGraph σ H).neighborSet (σ i)).ncard = d := by
        rwa [permGraph_ncard_neighborSet]
      simp [h, h']
    · have h' : ((permGraph σ H).neighborSet (σ i)).ncard ≠ d := by
        rwa [permGraph_ncard_neighborSet]
      simp [h, h']
  have hSB : IsSizeBias P W Q Ws :=
    sizeBias_sum_of_exchangeable_zero_one_fin P Q hn hX_meas hX_zo hexch
      (measurable_of_finite fun G1 (j : {j : Fin n // j ≠ v0}) ↦ X j.1 G1).aemeasurable hcond
  exact ⟨fun G H hH ↦ degreeDCouplingPMF_ncard_neighborSet hd v0 G hH, hcond, hSB⟩

end SteinMethod
