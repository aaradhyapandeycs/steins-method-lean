/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonSizeBias
import Formalization.PoissonSizeBias.Monotone.FKG
import Formalization.PoissonSizeBias.Subgraph.Defs
import Formalization.RandomGraph.ErdosRenyi
import Mathlib.Probability.Moments.Covariance

/-!
# Theorem 4.17 on $G(n, p)$ and Example 4.10
(`Formalization.PoissonSizeBias.Monotone.SubgraphMonotone`)

Proves the edge-indicator specialization `thm4_17_erdosRenyi` of Theorem 4.17 on $G(n, p)$ and
Example 4.10 (`[Subgraph counts]`, `SteinIntro.tex:2424-2427`: `ex4_10` and `ex4_10_general`).
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-! ### Part 1: Edge-Indicator Representation and Theorem 4.17 on $G(n, p)$ -/

private lemma graphOfEdgeBits_mono {n : ℕ} {ω₁ ω₂ : EdgePair n → Bool}
    (h : ∀ e : EdgePair n, ω₁ e ≤ ω₂ e) :
    graphOfEdgeBits ω₁ ≤ graphOfEdgeBits ω₂ := by
  intro u v huv
  have hne : u ≠ v := (graphOfEdgeBits ω₁).ne_of_adj huv
  have hdiag : ¬ s(u, v).IsDiag := fun hd ↦ hne (Sym2.mk_isDiag_iff.mp hd)
  let e : EdgePair n := ⟨s(u, v), hdiag⟩
  have hmem₁ : e.1 ∈ (graphOfEdgeBits ω₁).edgeSet := huv
  have hω₁ : ω₁ e = true := (mem_edgeSet_graphOfEdgeBits ω₁ e).mp hmem₁
  have hle := h e
  rw [hω₁] at hle
  have hω₂ : ω₂ e = true := by
    cases h2 : ω₂ e
    · rw [h2] at hle; exact False.elim (Bool.noConfusion (hle rfl))
    · rfl
  exact (mem_edgeSet_graphOfEdgeBits ω₂ e).mpr hω₂

theorem graphOfNatEdgeVec_mono {n : ℕ} :
    Monotone (@graphOfNatEdgeVec n) := by
  intro y₁ y₂ hy
  refine graphOfEdgeBits_mono fun e ↦ ?_
  by_cases h1 : 1 ≤ y₁ (Fintype.equivFin (EdgePair n) e)
  · have h2 : 1 ≤ y₂ (Fintype.equivFin (EdgePair n) e) :=
      le_trans h1 (hy (Fintype.equivFin (EdgePair n) e))
    simp [h1, h2]
  · simp [h1]

@[simp]
theorem graphOfNatEdgeVec_edgeIndNat {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphOfNatEdgeVec
      (fun j : Fin (Fintype.card (EdgePair n)) ↦
        edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G) = G := by
  unfold graphOfNatEdgeVec
  have h_bits : (fun e : EdgePair n ↦
      decide (1 ≤ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm
        (Fintype.equivFin (EdgePair n) e)) G)) = edgeBitsOfGraph G := by
    funext e
    simp only [Equiv.symm_apply_apply, edgeIndNat, edgeBitsOfGraph]
    by_cases he : e.1 ∈ G.edgeSet <;> simp [he]
  rw [h_bits, graphOfEdgeBits_edgeBitsOfGraph]

private lemma edgeIndNat_zero_or_one {n : ℕ} (e : EdgePair n) (G : SimpleGraph (Fin n)) :
    edgeIndNat e G = 0 ∨ edgeIndNat e G = 1 := by
  unfold edgeIndNat
  split_ifs <;> simp

private lemma iIndepFun_edgeIndNat_reindex {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    iIndepFun
      (fun (j : Fin (Fintype.card (EdgePair n))) (G : SimpleGraph (Fin n)) ↦
        edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G)
      (erdosRenyi n p) := by
  let equivE := (Fintype.equivFin (EdgePair n)).symm
  have hind_real := (erdosRenyi_edgeIndicator_iIndepFun_and_hasLaw (n := n) hp0 hp1).1
  let toNat : ℝ → ℕ := fun x ↦ if x = 1 then 1 else 0
  have h_meas_toNat : Measurable toNat :=
    Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const
  have h_comp : ∀ e : EdgePair n,
      edgeIndNat e = toNat ∘ edgeIndicator e := by
    intro e
    funext G
    unfold toNat edgeIndNat edgeIndicator
    by_cases h : e.1 ∈ G.edgeSet <;> simp [h]
  have hind_nat : iIndepFun (edgeIndNat (n := n)) (erdosRenyi n p) := by
    have h := hind_real.comp (fun _ ↦ toNat) (fun _ ↦ h_meas_toNat)
    simpa [← h_comp] using h
  refine iIndepFun_iff_measure_inter_preimage_eq_mul.mpr fun S {sets} _ ↦ ?_
  let S' : Finset (EdgePair n) := S.map equivE.toEmbedding
  let sets' : EdgePair n → Set ℕ := fun e ↦ sets (equivE.symm e)
  have hsets' : ∀ e ∈ S', MeasurableSet (sets' e) := fun _ _ ↦ .of_discrete
  have h_eq := iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind_nat S' hsets'
  have h_inter : (⋂ j ∈ S, (fun G ↦ edgeIndNat (equivE j) G) ⁻¹' sets j) =
      ⋂ e ∈ S', edgeIndNat e ⁻¹' sets' e := by
    ext G
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h e he
      rcases Finset.mem_map.mp he with ⟨j, hj, rfl⟩
      simpa [sets'] using h j hj
    · intro h j hj
      have he : equivE j ∈ S' := Finset.mem_map_of_mem equivE.toEmbedding hj
      simpa [sets'] using h (equivE j) he
  have h_prod :
      (∏ j ∈ S, (erdosRenyi n p) ((fun G ↦ edgeIndNat (equivE j) G) ⁻¹' sets j)) =
      ∏ e ∈ S', (erdosRenyi n p) (edgeIndNat e ⁻¹' sets' e) := by
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [sets']
  rw [h_inter, h_prod]
  exact h_eq

/-- Specialization of `thm4_17_corrected` to functions of the edge indicators of an Erdős–Rényi
random graph $G \sim G(n, p)$. -/
theorem thm4_17_erdosRenyi
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n m : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)}
    {f : Fin m → (Fin (Fintype.card (EdgePair n)) → ℕ) → ℕ}
    {r : ℝ≥0} {Z : Ω' → ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hG_meas : AEMeasurable G P)
    (hG_law : P.map G = erdosRenyi n p)
    (hf_01 : ∀ i : Fin m, ∀ y : Fin (Fintype.card (EdgePair n)) → ℕ,
      (∀ j, y j ≤ 1) → f i y = 0 ∨ f i y = 1)
    (hf_mono :
      (∀ i : Fin m, MonotoneOn (f i) {y | ∀ j, y j ≤ 1}) ∨
      (∀ i : Fin m, AntitoneOn (f i) {y | ∀ j, y j ≤ 1}))
    (hr_eq : (r : ℝ) = ∑ i : Fin m,
      P.real {ω | f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1})
    (hZ_meas : AEMeasurable Z P')
    (hZ_law : P'.map Z = poissonLaw r) :
    let Y : Fin (Fintype.card (EdgePair n)) → SimpleGraph (Fin n) → ℕ :=
      fun j H ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) H
    let X : Fin m → SimpleGraph (Fin n) → ℕ := fun i H ↦ f i (fun j ↦ Y j H)
    let q : Fin m → ℝ := fun i ↦ P.real {ω | X i (G ω) = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin m, X i (G ω)
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
            2 * ∑ i : Fin m, q i ^ 2)) := by
  intro Y X q W
  let W_G : SimpleGraph (Fin n) → ℕ := fun H ↦ ∑ i : Fin m, X i H
  have hY_meas : ∀ j, AEMeasurable (Y j) (erdosRenyi n p) :=
    fun _ ↦ Measurable.of_discrete.aemeasurable
  have hY_01 : ∀ j, ∀ᵐ H ∂(erdosRenyi n p), Y j H = 0 ∨ Y j H = 1 :=
    fun _ ↦ Filter.Eventually.of_forall (edgeIndNat_zero_or_one _)
  have hY_indep : iIndepFun Y (erdosRenyi n p) := iIndepFun_edgeIndNat_reindex hp0 hp1
  have hq_eq : ∀ i : Fin m, q i = (erdosRenyi n p).real {H | X i H = 1} := by
    intro i
    rw [← hG_law, map_measureReal_apply_of_aemeasurable hG_meas .of_discrete]
    rfl
  have hr_eq' : (r : ℝ) = ∑ i : Fin m, (erdosRenyi n p).real {H | X i H = 1} := by
    rw [hr_eq]
    exact Finset.sum_congr rfl fun i _ ↦ hq_eq i
  have h_bound := thm4_17_corrected (erdosRenyi n p) P' hY_meas hY_01 hY_indep hf_01 hf_mono
    hr_eq' hZ_meas hZ_law
  have h_map_W : P.map W = (erdosRenyi n p).map W_G := by
    rw [← hG_law,
      AEMeasurable.map_map_of_aemeasurable Measurable.of_discrete.aemeasurable hG_meas]
    rfl
  have h_var_W : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      ProbabilityTheory.variance (fun H ↦ (W_G H : ℝ)) (erdosRenyi n p) := by
    rw [← hG_law, ProbabilityTheory.variance_map Measurable.of_discrete.aemeasurable hG_meas]
    rfl
  have h_sum_q : (∑ i : Fin m, q i ^ 2) =
      ∑ i : Fin m, ((erdosRenyi n p).real {H | X i H = 1}) ^ 2 :=
    Finset.sum_congr rfl fun i _ ↦ by rw [hq_eq i]
  rw [h_map_W, h_var_W, h_sum_q]
  exact h_bound

/-! ### Part 2: Example 4.10 (`[Subgraph counts]`, `SteinIntro.tex:2424-2427`) -/

theorem monotone_subgraphEdgeFn {n : ℕ} (α : SimpleGraph (Fin n)) :
    Monotone (subgraphEdgeFn α) := by
  intro y₁ y₂ hy
  unfold subgraphEdgeFn
  have h_le : graphOfNatEdgeVec y₁ ≤ graphOfNatEdgeVec y₂ := graphOfNatEdgeVec_mono hy
  split_ifs with h1 h2
  · exact le_rfl
  · exact False.elim (h2 (le_trans h1 h_le))
  · exact zero_le_one
  · exact le_rfl

theorem subgraphEdgeFn_zero_or_one {n : ℕ} (α : SimpleGraph (Fin n))
    (y : Fin (Fintype.card (EdgePair n)) → ℕ) :
    subgraphEdgeFn α y = 0 ∨ subgraphEdgeFn α y = 1 := by
  unfold subgraphEdgeFn
  split_ifs <;> simp

@[simp]
theorem subgraphEdgeFn_edgeIndNat {n : ℕ} (α G : SimpleGraph (Fin n)) :
    subgraphEdgeFn α
      (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G) =
      subgraphCopyIndicator α G := by
  unfold subgraphEdgeFn subgraphCopyIndicator
  rw [graphOfNatEdgeVec_edgeIndNat]

private lemma card_filter_edgeSet_eq_ncard {n : ℕ} (α : SimpleGraph (Fin n)) :
    (Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∈ α.edgeSet)).card = α.edgeSet.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  refine Finset.card_bij (fun (e : EdgePair n) _ ↦ e.1)
    (fun e he ↦ Set.mem_toFinset.mpr (Finset.mem_filter.mp he).2)
    (fun e₁ _ e₂ _ h ↦ Subtype.ext h)
    (fun e' he' ↦ ?_)
  have hmem : e' ∈ α.edgeSet := Set.mem_toFinset.mp he'
  have hnd : ¬ e'.IsDiag := α.not_isDiag_of_mem_edgeSet hmem
  exact ⟨⟨e', hnd⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, rfl⟩

private lemma ncard_edgeSet_embedGraph {V : Type*}
    (H : SimpleGraph V) {n : ℕ} (f : V ↪ Fin n) :
    (embedGraph H f).edgeSet.ncard = H.edgeSet.ncard := by
  have h_img : (embedGraph H f).edgeSet = Sym2.map f '' H.edgeSet := by
    ext e'
    constructor
    · refine Sym2.ind (fun u v huv ↦ ?_) e'
      change (embedGraph H f).Adj u v at huv
      rw [embedGraph_adj] at huv
      rcases huv with ⟨x, y, rfl, rfl, hxy⟩
      exact ⟨s(x, y), hxy, rfl⟩
    · rintro ⟨e, he, rfl⟩
      revert he
      refine Sym2.ind (fun x y hxy ↦ ?_) e
      change H.Adj x y at hxy
      change (embedGraph H f).Adj (f x) (f y)
      exact (embedGraph_adj_apply H f x y).mpr hxy
  rw [h_img, Set.ncard_image_of_injective _ (Sym2.map.injective f.injective)]

private lemma erdosRenyi_real_subgraphCopyIndicator_eq {V : Type*} [Fintype V]
    (H : SimpleGraph V) {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {α : SimpleGraph (Fin n)} (hα : α ∈ subgraphCopies H n) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} =
      p ^ H.edgeSet.ncard := by
  let S_α : Finset (EdgePair n) := Finset.univ.filter (fun e : EdgePair n ↦ e.1 ∈ α.edgeSet)
  have h_set : {G : SimpleGraph (Fin n) | subgraphCopyIndicator α G = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ S_α, e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_ofPred_eq, subgraphCopyIndicator_eq_one_iff, Finset.notMem_empty,
      IsEmpty.forall_iff, implies_true, and_true, S_α, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hle e he
      exact SimpleGraph.edgeSet_mono hle he
    · intro h u v huv
      have hne : u ≠ v := α.ne_of_adj huv
      have hnd : ¬ s(u, v).IsDiag := fun hd ↦ hne (Sym2.mk_isDiag_iff.mp hd)
      exact h ⟨s(u, v), hnd⟩ huv
  rw [h_set, erdosRenyi_real_cylinder hp0 hp1 S_α ∅ (Finset.disjoint_empty_right S_α)]
  simp only [Finset.card_empty, pow_zero, mul_one]
  rcases mem_subgraphCopies.mp hα with ⟨f, rfl⟩
  rw [card_filter_edgeSet_eq_ncard, ncard_edgeSet_embedGraph]

/-- **Example 4.10** (`[Subgraph counts]`, `SteinIntro.tex:2424-2427`): in Section 4.3.2, each
subgraph copy indicator $X_\alpha(G) = \mathbb{I}[\alpha \subseteq G]$ is an increasing function
`subgraphEdgeFn α` of the edge indicators, and applying Theorem 4.17 to
$W = \mathrm{subgraphCount}\,H\,n\,G = \sum_{\alpha \in \Gamma} X_\alpha(G)$ yields the exact bound
$\min\{1, \lambda^{-1}\}(\operatorname{Var}(W) - \lambda + 2 \lambda p^{e_H})$ of Theorem 4.15. -/
theorem ex4_10
    {V : Type*} [Fintype V] (H : SimpleGraph V)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hG_meas : AEMeasurable G P)
    (hG_law : P.map G = erdosRenyi n p)
    (hr_eq : (r : ℝ) = ∫ ω, (subgraphCount H n (G ω) : ℝ) ∂P)
    (hZ_meas : AEMeasurable Z P')
    (hZ_law : P'.map Z = poissonLaw r) :
    let e_H : ℕ := H.edgeSet.ncard
    let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
    (∀ α ∈ subgraphCopies H n,
      Monotone (subgraphEdgeFn α) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        subgraphCopyIndicator α G₀ =
          subgraphEdgeFn α
            (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀)) ∧
    ∫ ω, (W ω : ℝ) ∂P = ((subgraphCopies H n).card : ℝ) * p ^ e_H ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
            2 * (r : ℝ) * p ^ e_H)) := by
  intro e_H W
  let Γ := subgraphCopies H n
  let m := Γ.card
  let equivΓ : Fin m ≃ {α // α ∈ Γ} := Fintype.equivOfCardEq (by simp [m])
  let f : Fin m → (Fin (Fintype.card (EdgePair n)) → ℕ) → ℕ :=
    fun i ↦ subgraphEdgeFn (equivΓ i).1
  have h1 : ∀ α ∈ Γ,
      Monotone (subgraphEdgeFn α) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        subgraphCopyIndicator α G₀ =
          subgraphEdgeFn α (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) :=
    fun α _ ↦
      ⟨monotone_subgraphEdgeFn α, fun G₀ ↦ (subgraphEdgeFn_edgeIndNat α G₀).symm⟩
  have hW_eq_sum : ∀ G₀ : SimpleGraph (Fin n),
      subgraphCount H n G₀ =
        ∑ i : Fin m,
          f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) := by
    intro G₀
    unfold subgraphCount
    have h_attach : (∑ α ∈ Γ, subgraphCopyIndicator α G₀) =
        ∑ α : {α // α ∈ Γ}, subgraphCopyIndicator α.1 G₀ := by
      rw [← Finset.sum_attach]
      rfl
    rw [h_attach, ← equivΓ.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [f, subgraphEdgeFn_edgeIndNat]
  have h_prob_i : ∀ i : Fin m,
      P.real {ω |
        f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1} =
        p ^ e_H := by
    intro i
    change P.real (G ⁻¹' {G₀ |
      f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) = 1}) = p ^ e_H
    rw [← map_measureReal_apply_of_aemeasurable hG_meas .of_discrete, hG_law]
    simp only [f, subgraphEdgeFn_edgeIndNat]
    exact erdosRenyi_real_subgraphCopyIndicator_eq H hp0 hp1 (equivΓ i).2
  have h_mean : ∫ ω, (W ω : ℝ) ∂P = (Γ.card : ℝ) * p ^ e_H := by
    have h_map := integral_map hG_meas
      (f := fun G₀ : SimpleGraph (Fin n) ↦ (subgraphCount H n G₀ : ℝ))
      Measurable.of_discrete.aestronglyMeasurable
    have h_comp : (∫ ω, (W ω : ℝ) ∂P) =
        ∫ ω,
          (fun G₀ : SimpleGraph (Fin n) ↦ (subgraphCount H n G₀ : ℝ)) (G ω) ∂P := rfl
    rw [h_comp, ← h_map, hG_law]
    have h_cast : (fun G₀ : SimpleGraph (Fin n) ↦ (subgraphCount H n G₀ : ℝ)) =
        fun G₀ ↦ ∑ α ∈ Γ, (subgraphCopyIndicator α G₀ : ℝ) := by
      funext G₀
      unfold subgraphCount
      simp [Γ]
    rw [h_cast, integral_finsetSum Γ (fun _ _ ↦ Integrable.of_finite)]
    have h_each : ∀ α ∈ Γ,
        ∫ G₀, (subgraphCopyIndicator α G₀ : ℝ) ∂(erdosRenyi n p) = p ^ e_H := by
      intro α hα
      have h_ind : (fun G₀ : SimpleGraph (Fin n) ↦ (subgraphCopyIndicator α G₀ : ℝ)) =
          {G₀ | subgraphCopyIndicator α G₀ = 1}.indicator 1 := by
        funext G₀
        rcases subgraphCopyIndicator_zero_or_one α G₀ with h0 | h1
        · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h0, zero_ne_one, ↓reduceIte,
            Nat.cast_zero]
        · simp only [Set.indicator_apply, Set.mem_ofPred_eq, h1, ↓reduceIte, Nat.cast_one,
            Pi.one_apply]
      rw [h_ind, integral_indicator_one .of_discrete,
        erdosRenyi_real_subgraphCopyIndicator_eq H hp0 hp1 hα]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, nsmul_eq_mul]
  have hr_sum : (r : ℝ) = ∑ i : Fin m,
      P.real {ω |
        f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1} := by
    rw [hr_eq, h_mean]
    simp_rw [h_prob_i, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, m]
  have hf_01 : ∀ i : Fin m, ∀ y : Fin (Fintype.card (EdgePair n)) → ℕ,
      (∀ j, y j ≤ 1) → f i y = 0 ∨ f i y = 1 :=
    fun i y _ ↦ subgraphEdgeFn_zero_or_one (equivΓ i).1 y
  have hf_mono : (∀ i : Fin m, MonotoneOn (f i) {y | ∀ j, y j ≤ 1}) ∨
      (∀ i : Fin m, AntitoneOn (f i) {y | ∀ j, y j ≤ 1}) :=
    Or.inl fun i ↦ (monotone_subgraphEdgeFn (equivΓ i).1).monotoneOn _
  have h_thm :=
    thm4_17_erdosRenyi P P' hp0 hp1 hG_meas hG_law hf_01 hf_mono hr_sum hZ_meas hZ_law
  have hW_pt : ∀ ω,
      (∑ i : Fin m,
        f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω))) = W ω :=
    fun ω ↦ (hW_eq_sum (G ω)).symm
  have h_sum_sq : 2 * (∑ i : Fin m,
      (P.real {ω |
        f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1}) ^ 2) =
      2 * (r : ℝ) * p ^ e_H := by
    simp_rw [h_prob_i, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [hr_eq, h_mean]
    dsimp [m]
    ring
  refine ⟨h1, h_mean, ?_⟩
  dsimp only at h_thm
  simp_rw [hW_pt] at h_thm
  rwa [h_sum_sq] at h_thm

/-- General edge-subset product version of **Example 4.10** (`[Subgraph counts]`,
`SteinIntro.tex:2424-2427`): for any finite family of edge subsets $\Gamma_1, \dots, \Gamma_m$,
each indicator $f_i(y) = \prod_{e \in \Gamma_i} y_e$ is increasing, equals the indicator that all
edges of $\Gamma_i$ are present in $G$, and $W = \sum_{i=1}^m f_i(\mathbf{Y}(G))$ satisfies the
Theorem 4.17 bound. -/
theorem ex4_10_general
    {n m : ℕ} {p : ℝ} (Γ : Fin m → Finset (EdgePair n)) {r : ℝ≥0}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let f : Fin m → (Fin (Fintype.card (EdgePair n)) → ℕ) → ℕ :=
      fun i y ↦ ∏ e ∈ Γ i, y (Fintype.equivFin (EdgePair n) e)
    let X : Fin m → SimpleGraph (Fin n) → ℕ :=
      fun i G ↦ f i (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G)
    let q : Fin m → ℝ := fun i ↦ (erdosRenyi n p).real {G | X i G = 1}
    let W : SimpleGraph (Fin n) → ℕ := fun G ↦ ∑ i : Fin m, X i G
    (r : ℝ) = ∑ i : Fin m, q i →
    (∀ i : Fin m, Monotone (f i)) ∧
      tvDist ((erdosRenyi n p).map W) (poissonLaw r) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ)⁻¹ *
            (ProbabilityTheory.variance (fun G ↦ (W G : ℝ)) (erdosRenyi n p) - (r : ℝ) +
              2 * ∑ i : Fin m, q i ^ 2)) := by
  intro f X q W hr_eq
  have hf_mono_all : ∀ i : Fin m, Monotone (f i) := by
    intro i y₁ y₂ hy
    exact Finset.prod_le_prod fun e _ ↦ hy (Fintype.equivFin (EdgePair n) e)
  refine ⟨hf_mono_all, ?_⟩
  have hf_01 : ∀ i : Fin m, ∀ y : Fin (Fintype.card (EdgePair n)) → ℕ,
      (∀ j, y j ≤ 1) → f i y = 0 ∨ f i y = 1 := by
    intro i y hy
    by_cases hall : ∀ e ∈ Γ i, y (Fintype.equivFin (EdgePair n) e) = 1
    · right
      exact Finset.prod_eq_one hall
    · left
      push Not at hall
      rcases hall with ⟨e, he, hne1⟩
      have hle1 := hy (Fintype.equivFin (EdgePair n) e)
      have heq0 : y (Fintype.equivFin (EdgePair n) e) = 0 := by omega
      exact Finset.prod_eq_zero he heq0
  have hf_mono : (∀ i : Fin m, MonotoneOn (f i) {y | ∀ j, y j ≤ 1}) ∨
      (∀ i : Fin m, AntitoneOn (f i) {y | ∀ j, y j ≤ 1}) :=
    Or.inl fun i ↦ (hf_mono_all i).monotoneOn _
  have h_thm := thm4_17_erdosRenyi (erdosRenyi n p) (poissonLaw r)
    hp0 hp1 aemeasurable_id (Measure.map_id) hf_01 hf_mono hr_eq
    aemeasurable_id (Measure.map_id)
  dsimp only at h_thm
  rwa [Measure.map_id] at h_thm

end SteinMethod
