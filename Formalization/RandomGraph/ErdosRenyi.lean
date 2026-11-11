/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.RandomGraph
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic

/-!
# Erdős–Rényi Random Graph Foundations (`SteinIntro.tex:918-920, 1354-1358`)

Implements Part C.1 of the formalization of Nathan Ross, *Fundamentals of Stein's method*
(`arXiv:1109.1880v1`):

* Edge-bit bijection (`edgeBitsOfGraph`, `graphOfEdgeBits_edgeBitsOfGraph`,
  `edgeBitsOfGraph_graphOfEdgeBits`, `mem_edgeSet_graphOfEdgeBits`) and measurability of
  `graphOfEdgeBits`, `edgeBitsOfGraph`, and `edgeIndicator`.
* Finite and discrete measurable space instances on `SimpleGraph (Fin n)` and the probability
  measure instance on `erdosRenyi n p`.
* Sanity theorems: `card_edgePair` ($\binom{n}{2}$ potential edges) and
  `erdosRenyi_edgeIndicator_iIndepFun_and_hasLaw` (mutual independence and $\mathrm{Ber}(p)$
  marginal laws of the undirected edge indicators).
* Cylinder-event probability formula `erdosRenyi_real_cylinder` and disjoint-edge-set
  independence lemma `erdosRenyi_indepFun_of_disjoint_edges`.
-/

open MeasureTheory

namespace SteinMethod

/-! ### Edge-bit bijection and measurability -/

/-- Extract the boolean edge-presence vector on `EdgePair n` from a simple graph on `Fin n`
(`SteinIntro.tex:918-920, 1354-1358`). -/
noncomputable def edgeBitsOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) (e : EdgePair n) : Bool := by
  classical exact decide (e.1 ∈ G.edgeSet)

@[simp]
private lemma edgeBitsOfGraph_eq_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) (e : EdgePair n) :
    edgeBitsOfGraph G e = true ↔ e.1 ∈ G.edgeSet := by
  simp [edgeBitsOfGraph]

/-- Membership of an undirected off-diagonal vertex pair in `(graphOfEdgeBits ω).edgeSet` is
characterized by the corresponding bit of `ω` (`SteinIntro.tex:918-920, 1354-1358`). -/
@[simp]
theorem mem_edgeSet_graphOfEdgeBits {n : ℕ} (ω : EdgePair n → Bool) (e : EdgePair n) :
    e.1 ∈ (graphOfEdgeBits ω).edgeSet ↔ ω e = true := by
  rw [graphOfEdgeBits, SimpleGraph.edgeSet_fromEdgeSet]
  change (∃ h : ¬ e.1.IsDiag, ω ⟨e.1, h⟩ = true) ∧ e.1 ∉ Sym2.diagSet ↔ ω e = true
  rw [Sym2.mem_diagSet]
  refine ⟨?_, fun h ↦ ⟨⟨e.2, h⟩, e.2⟩⟩
  rintro ⟨⟨h', hω⟩, -⟩
  have he : (⟨e.1, h'⟩ : EdgePair n) = e := Subtype.ext rfl
  rwa [he] at hω

/-- Reconstructing a graph from its extracted edge bits recovers the original graph
(`SteinIntro.tex:918-920, 1354-1358`). -/
@[simp]
theorem graphOfEdgeBits_edgeBitsOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphOfEdgeBits (edgeBitsOfGraph G) = G := by
  rw [← SimpleGraph.edgeSet_inj]
  ext e
  by_cases he : e.IsDiag
  · exact iff_of_false ((graphOfEdgeBits _).not_mem_edgeSet_of_isDiag he)
      (G.not_mem_edgeSet_of_isDiag he)
  · exact (mem_edgeSet_graphOfEdgeBits (edgeBitsOfGraph G) ⟨e, he⟩).trans
      (edgeBitsOfGraph_eq_true_iff G ⟨e, he⟩)

/-- Extracting the edge bits of `graphOfEdgeBits ω` recovers `ω`
(`SteinIntro.tex:918-920, 1354-1358`). -/
@[simp]
theorem edgeBitsOfGraph_graphOfEdgeBits {n : ℕ} (ω : EdgePair n → Bool) :
    edgeBitsOfGraph (graphOfEdgeBits ω) = ω := by
  funext e
  cases h₁ : edgeBitsOfGraph (graphOfEdgeBits ω) e <;> cases h₂ : ω e
  · rfl
  · have ht := (edgeBitsOfGraph_eq_true_iff _ e).mpr ((mem_edgeSet_graphOfEdgeBits ω e).mpr h₂)
    rw [h₁] at ht
    cases ht
  · have ht := (mem_edgeSet_graphOfEdgeBits ω e).mp ((edgeBitsOfGraph_eq_true_iff _ e).mp h₁)
    rw [h₂] at ht
    cases ht
  · rfl

/-! ### Finite, discrete measurable, and probability measure instances -/

/-- `SimpleGraph (Fin n)` is finite (`SteinIntro.tex:918-920`). -/
instance instFiniteSimpleGraphFin (n : ℕ) : Finite (SimpleGraph (Fin n)) :=
  SimpleGraph.instFinite

/-- Every subset of `SimpleGraph (Fin n)` is measurable (`SteinIntro.tex:918-920`). -/
instance instDiscreteMeasurableSpaceSimpleGraphFin (n : ℕ) :
    DiscreteMeasurableSpace (SimpleGraph (Fin n)) := by
  have : MeasurableSingletonClass (SimpleGraph (Fin n)) := ⟨fun G ↦ by
    have h : ({G} : Set (SimpleGraph (Fin n))) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
      ext H
      exact Set.mem_singleton_iff.trans (SimpleGraph.ext_iff.trans Set.mem_singleton_iff.symm)
    rw [h]
    exact SimpleGraph.measurable_adj (measurableSet_singleton G.Adj)⟩
  infer_instance

/-- `graphOfEdgeBits` is measurable (`SteinIntro.tex:918-920, 1354-1358`). -/
theorem measurable_graphOfEdgeBits {n : ℕ} : Measurable (graphOfEdgeBits (n := n)) :=
  SimpleGraph.measurable_iff_adj.2 fun u v ↦ by
    by_cases huv : u = v
    · subst huv
      have h : (fun ω : EdgePair n → Bool ↦ (graphOfEdgeBits ω).Adj u u) = fun _ ↦ False := by
        funext ω
        exact propext (iff_false_intro (graphOfEdgeBits ω).irrefl)
      rw [h]
      exact measurable_const
    · have hdiag : ¬ s(u, v).IsDiag := fun hd ↦ huv (Sym2.mk_isDiag_iff.mp hd)
      let e₀ : EdgePair n := ⟨s(u, v), hdiag⟩
      have h : (fun ω : EdgePair n → Bool ↦ (graphOfEdgeBits ω).Adj u v) =
          fun ω ↦ ω e₀ ∈ ({true} : Set Bool) := by
        funext ω
        exact propext ((mem_edgeSet_graphOfEdgeBits ω e₀).trans Set.mem_singleton_iff.symm)
      rw [h]
      exact (measurableSet_singleton true).mem.comp (measurable_pi_apply e₀)

/-- `edgeBitsOfGraph` is measurable (`SteinIntro.tex:918-920, 1354-1358`). -/
theorem measurable_edgeBitsOfGraph {n : ℕ} : Measurable (edgeBitsOfGraph (n := n)) :=
  .of_discrete

/-- Every undirected edge indicator `edgeIndicator e` is measurable
(`SteinIntro.tex:918-920, 1354-1358`). -/
theorem measurable_edgeIndicator {n : ℕ} (e : EdgePair n) :
    Measurable (edgeIndicator e) :=
  .of_discrete

/-- The Erdős–Rényi random graph law `erdosRenyi n p` is a probability measure for all `n` and `p`
(`SteinIntro.tex:919, 1355`). -/
instance instIsProbabilityMeasureErdosRenyi (n : ℕ) (p : ℝ) :
    IsProbabilityMeasure (erdosRenyi n p) := by
  unfold erdosRenyi
  infer_instance

/-! ### Sanity theorems: edge-pair cardinality, mutual independence, and marginal laws -/

/-- There are $\binom{n}{2}$ unordered distinct-vertex pairs on `Fin n`
(`SteinIntro.tex:919, 1355`). -/
theorem card_edgePair (n : ℕ) : Fintype.card (EdgePair n) = n.choose 2 := by
  calc
    Fintype.card (EdgePair n) = (Fintype.card (Fin n)).choose 2 := Sym2.card_subtype_not_diag
    _ = n.choose 2 := by rw [Fintype.card_fin]

private def bitToReal : Bool → ℝ
  | true => 1
  | false => 0

private lemma edgeIndicator_graphOfEdgeBits {n : ℕ} (e : EdgePair n) (ω : EdgePair n → Bool) :
    edgeIndicator e (graphOfEdgeBits ω) = bitToReal (ω e) := by
  unfold edgeIndicator
  cases h : ω e
  · exact Set.indicator_of_notMem
      (by rw [Set.mem_ofPred, mem_edgeSet_graphOfEdgeBits, h]; decide) 1
  · exact Set.indicator_of_mem
      (by rw [Set.mem_ofPred, mem_edgeSet_graphOfEdgeBits, h]) 1

private theorem erdosRenyi_edgeIndicator_iIndepFun (n : ℕ) (p : ℝ) :
    ProbabilityTheory.iIndepFun (edgeIndicator (n := n)) (erdosRenyi n p) := by
  let μ₀ : Measure Bool :=
    ProbabilityTheory.bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)
  let ν : Measure (EdgePair n → Bool) := Measure.pi fun _ : EdgePair n ↦ μ₀
  have hbit : Measurable bitToReal := .of_discrete
  have hpi : ProbabilityTheory.iIndepFun
      (fun (e : EdgePair n) (ω : EdgePair n → Bool) ↦ bitToReal (ω e)) ν :=
    ProbabilityTheory.iIndepFun_pi (fun _ ↦ hbit.aemeasurable)
  refine ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.2 fun S {sets} hsets ↦ ?_
  have hpre_single : ∀ e : EdgePair n,
      graphOfEdgeBits ⁻¹' (edgeIndicator e ⁻¹' sets e) =
        (fun ω : EdgePair n → Bool ↦ bitToReal (ω e)) ⁻¹' sets e := by
    intro e
    ext ω
    simp [edgeIndicator_graphOfEdgeBits]
  have hpre_inter :
      graphOfEdgeBits ⁻¹' (⋂ e ∈ S, edgeIndicator e ⁻¹' sets e) =
        ⋂ e ∈ S, (fun ω : EdgePair n → Bool ↦ bitToReal (ω e)) ⁻¹' sets e := by
    ext ω
    simp [edgeIndicator_graphOfEdgeBits]
  change ν.map graphOfEdgeBits (⋂ e ∈ S, edgeIndicator e ⁻¹' sets e) =
    ∏ e ∈ S, ν.map graphOfEdgeBits (edgeIndicator e ⁻¹' sets e)
  rw [Measure.map_apply measurable_graphOfEdgeBits .of_discrete, hpre_inter]
  have hrhs : ∀ e ∈ S,
      ν.map graphOfEdgeBits (edgeIndicator e ⁻¹' sets e) =
        ν ((fun ω : EdgePair n → Bool ↦ bitToReal (ω e)) ⁻¹' sets e) := by
    intro e _
    rw [Measure.map_apply measurable_graphOfEdgeBits .of_discrete, hpre_single e]
  rw [Finset.prod_congr rfl hrhs]
  exact hpi.measure_inter_preimage_eq_mul S hsets

private theorem erdosRenyi_edgeIndicator_hasLaw {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : EdgePair n) :
    ProbabilityTheory.HasLaw (edgeIndicator e)
      (ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 ⟨p, hp0, hp1⟩) (erdosRenyi n p) where
  aemeasurable := (measurable_edgeIndicator e).aemeasurable
  map_eq := by
    let μ₀ : Measure Bool :=
      ProbabilityTheory.bernoulliMeasure true false (Set.projIcc 0 1 zero_le_one p)
    have hbit : Measurable bitToReal := .of_discrete
    have hcomp : edgeIndicator e ∘ graphOfEdgeBits = bitToReal ∘ Function.eval e := by
      funext ω
      exact edgeIndicator_graphOfEdgeBits e ω
    calc
      (erdosRenyi n p).map (edgeIndicator e)
          = (Measure.pi fun _ : EdgePair n ↦ μ₀).map (edgeIndicator e ∘ graphOfEdgeBits) :=
        Measure.map_map (measurable_edgeIndicator e) measurable_graphOfEdgeBits
      _ = (Measure.pi fun _ : EdgePair n ↦ μ₀).map (bitToReal ∘ Function.eval e) := by
        rw [hcomp]
      _ = ((Measure.pi fun _ : EdgePair n ↦ μ₀).map (Function.eval e)).map bitToReal :=
        (Measure.map_map hbit (measurable_pi_apply e)).symm
      _ = μ₀.map bitToReal := by
        rw [(measurePreserving_eval (fun _ : EdgePair n ↦ μ₀) e).map_eq]
      _ = (ProbabilityTheory.bernoulliMeasure true false ⟨p, hp0, hp1⟩).map bitToReal := by
        simp only [μ₀, Set.projIcc_of_mem zero_le_one ⟨hp0, hp1⟩]
      _ = ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 ⟨p, hp0, hp1⟩ :=
        ProbabilityTheory.map_bernoulliMeasure' true false hbit ⟨p, hp0, hp1⟩

/-- Under $G(n, p)$ with $p \in [0, 1]$, the $\binom{n}{2}$ undirected edge indicators
`edgeIndicator e` are mutually independent with $\mathrm{Ber}(p)$ marginal laws on
$\{0, 1\} \subset \mathbb{R}$ (`SteinIntro.tex:918-920, 1354-1358`). -/
theorem erdosRenyi_edgeIndicator_iIndepFun_and_hasLaw {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.iIndepFun (edgeIndicator (n := n)) (erdosRenyi n p) ∧
      ∀ e : EdgePair n,
        ProbabilityTheory.HasLaw (edgeIndicator e)
          (ProbabilityTheory.bernoulliMeasure (1 : ℝ) 0 ⟨p, hp0, hp1⟩) (erdosRenyi n p) :=
  ⟨erdosRenyi_edgeIndicator_iIndepFun n p, erdosRenyi_edgeIndicator_hasLaw hp0 hp1⟩

/-! ### Cylinder-event probabilities and disjoint-edge independence -/

/-- Under $G(n, p)$ with $p \in [0, 1]$, the probability that all edges in `S_pos` are present and
all edges in a disjoint set `S_neg` are absent equals $p^{|S_{\mathrm{pos}}|} (1 -
p)^{|S_{\mathrm{neg}}|}$ (`SteinIntro.tex:918-920, 1354-1358`). -/
theorem erdosRenyi_real_cylinder {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S_pos S_neg : Finset (EdgePair n)) (hdisj : Disjoint S_pos S_neg) :
    (erdosRenyi n p).real
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ S_pos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ S_neg, e.1 ∉ G.edgeSet)} =
      p ^ S_pos.card * (1 - p) ^ S_neg.card := by
  classical
  let q : unitInterval := ⟨p, hp0, hp1⟩
  let μ₀ : Measure Bool := ProbabilityTheory.bernoulliMeasure true false q
  let C : Set (SimpleGraph (Fin n)) :=
    {G | (∀ e ∈ S_pos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ S_neg, e.1 ∉ G.edgeSet)}
  let box : EdgePair n → Set Bool := fun e ↦
    if e ∈ S_pos then {true} else if e ∈ S_neg then {false} else Set.univ
  have hpre : graphOfEdgeBits ⁻¹' C = Set.univ.pi box := by
    ext ω
    simp only [Set.mem_preimage, C, Set.mem_ofPred_eq, mem_edgeSet_graphOfEdgeBits,
      Set.mem_univ_pi, box]
    constructor
    · rintro ⟨hpos, hneg⟩ e
      by_cases hp : e ∈ S_pos
      · simp only [hp, ↓reduceIte, Set.mem_singleton_iff]
        exact hpos e hp
      · by_cases hn : e ∈ S_neg
        · simp only [hp, hn, ↓reduceIte, Set.mem_singleton_iff]
          have hne := hneg e hn
          cases hω : ω e
          · rfl
          · exact False.elim (hne hω)
        · simp only [hp, hn, ↓reduceIte]
          exact Set.mem_univ _
    · intro hω
      refine ⟨fun e he ↦ ?_, fun e he htrue ↦ ?_⟩
      · have h := hω e
        simp only [he, ↓reduceIte, Set.mem_singleton_iff] at h
        exact h
      · have hnotpos : e ∉ S_pos := Finset.disjoint_right.mp hdisj he
        have h := hω e
        simp only [hnotpos, he, ↓reduceIte, Set.mem_singleton_iff] at h
        rw [htrue] at h
        cases h
  have her : erdosRenyi n p = (Measure.pi fun _ : EdgePair n ↦ μ₀).map graphOfEdgeBits := by
    simp only [erdosRenyi, μ₀, q, Set.projIcc_of_mem zero_le_one ⟨hp0, hp1⟩]
  change (erdosRenyi n p).real C = p ^ S_pos.card * (1 - p) ^ S_neg.card
  rw [her, map_measureReal_apply measurable_graphOfEdgeBits .of_discrete, hpre,
    measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  have hfactor : ∀ e : EdgePair n,
      (μ₀ (box e)).toReal = (if e ∈ S_pos then p else 1) * (if e ∈ S_neg then 1 - p else 1) := by
    intro e
    change μ₀.real (box e) = _
    by_cases hp : e ∈ S_pos
    · have hn : e ∉ S_neg := Finset.disjoint_left.mp hdisj hp
      simp only [box, hp, hn, ↓reduceIte, mul_one]
      exact ProbabilityTheory.bernoulliMeasure_real_apply_of_mem_of_notMem q
        .of_discrete (by simp) (by simp)
    · by_cases hn : e ∈ S_neg
      · simp only [box, hp, hn, ↓reduceIte, one_mul]
        exact ProbabilityTheory.bernoulliMeasure_real_apply_of_notMem_of_mem q
          .of_discrete (by simp) (by simp)
      · simp only [box, hp, hn, ↓reduceIte, mul_one]
        exact probReal_univ
  simp_rw [hfactor]
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const]

/-- Measurable functions of the edge indicators on disjoint edge sets `E_A` and `E_B` are
independent under `erdosRenyi n p` (`SteinIntro.tex:918-920, 1354-1358`). -/
theorem erdosRenyi_indepFun_of_disjoint_edges {n : ℕ} {p : ℝ}
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (E_A E_B : Finset (EdgePair n)) (hdisj : Disjoint E_A E_B)
    {f : (E_A → ℝ) → α} {g : (E_B → ℝ) → β}
    (hf : Measurable f) (hg : Measurable g) :
    ProbabilityTheory.IndepFun
      (fun G : SimpleGraph (Fin n) ↦ f (fun e ↦ edgeIndicator e.1 G))
      (fun G : SimpleGraph (Fin n) ↦ g (fun e ↦ edgeIndicator e.1 G))
      (erdosRenyi n p) :=
  (ProbabilityTheory.iIndepFun.indepFun_finset E_A E_B hdisj
    (erdosRenyi_edgeIndicator_iIndepFun n p) measurable_edgeIndicator).comp hf hg

end SteinMethod
