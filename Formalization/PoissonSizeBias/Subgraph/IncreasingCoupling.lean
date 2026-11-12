/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonSizeBias
import Formalization.PoissonSizeBias.Core.Basic
import Formalization.PoissonSizeBias.Subgraph.Triangles
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Increasing Size-Bias Couplings & Subgraph Coupling (`IncreasingCoupling`)

Core coupling theorems and counterexamples for Section 4.3.1–4.3.2 (`SteinIntro.tex:2253-2312`):

* `erdosRenyi_real_subgraphCopyIndicator_sup_eq_one`, `integral_subgraphCopyIndicator_sup`,
  `sum_erase_integral_subgraphCopyIndicator_sup_sub`: coupled copy-indicator expectations and
  edge-overlap sum identity (`SteinIntro.tex:2316-2321`).
* `not_isExchangeableTuple_subgraphCopyIndicator_triangles`: **Counterexample
  (`ISSUE-SEC4.3.2-EXCH`, Critic G2-1)** refuting exchangeability of
  $(X_\alpha)_{\alpha \in \Gamma}$ at `SteinIntro.tex:2298` (triangles at $n = 5, p = 1/2$).
* `thm4_14_proof`: **Theorem 4.14** (`\label{thm122}`, `SteinIntro.tex:2257-2277`;
  `ISSUE-THM-4.14`).
* `thm4_15_proof`: **Theorem 4.15** (`\label{thm123}`, `SteinIntro.tex:2288-2295`), proved via
  Theorem 4.14 with a uniform random index $I$ on $\Gamma$ and vertex-permutation symmetry.
* `sec4_3_2_subgraph_coupling_proof`: Theorem 4.15 coupling verification
  (`SteinIntro.tex:2299-2307` items 1–3).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### 1. Coupled copy-indicator expectation and edge-difference sum identity -/

theorem le_sup_iff_forall_edgePairsOfGraph_sdiff {n : ℕ} (α β G : SimpleGraph (Fin n)) :
    β ≤ G ⊔ α ↔ ∀ e ∈ edgePairsOfGraph β \ edgePairsOfGraph α, e.1 ∈ G.edgeSet := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet, SimpleGraph.edgeSet_sup]
  constructor
  · intro h e he
    rcases Finset.mem_sdiff.mp he with ⟨heβ, heα⟩
    rw [mem_edgePairsOfGraph] at heβ heα
    exact (h heβ).resolve_right heα
  · intro h z hzβ
    by_cases hzα : z ∈ α.edgeSet
    · exact Or.inr hzα
    · have hnd : ¬ z.IsDiag := β.not_isDiag_of_mem_edgeSet hzβ
      have hmem : (⟨z, hnd⟩ : EdgePair n) ∈ edgePairsOfGraph β \ edgePairsOfGraph α := by
        rw [Finset.mem_sdiff, mem_edgePairsOfGraph, mem_edgePairsOfGraph]
        exact ⟨hzβ, hzα⟩
      exact Or.inl (h ⟨z, hnd⟩ hmem)

/-- Under $G \sim G(n, p)$ ($0 \le p \le 1$),
$\mathbb{P}(\beta \subseteq G \sqcup \alpha) = p^{|E(\beta) \setminus E(\alpha)|}$
(`SteinIntro.tex:2320`). -/
theorem erdosRenyi_real_subgraphCopyIndicator_sup_eq_one {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (α β : SimpleGraph (Fin n)) :
    (erdosRenyi n p).real {G : SimpleGraph (Fin n) | subgraphCopyIndicator β (G ⊔ α) = 1} =
      p ^ (β.edgeSet \ α.edgeSet).ncard := by
  have hset : {G : SimpleGraph (Fin n) | subgraphCopyIndicator β (G ⊔ α) = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ edgePairsOfGraph β \ edgePairsOfGraph α, e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
    ext G
    change subgraphCopyIndicator β (G ⊔ α) = 1 ↔
      (∀ e ∈ edgePairsOfGraph β \ edgePairsOfGraph α, e.1 ∈ G.edgeSet) ∧
        (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)
    simp [subgraphCopyIndicator_eq_one_iff, le_sup_iff_forall_edgePairsOfGraph_sdiff]
  rw [hset, erdosRenyi_real_cylinder hp0 hp1 _ _ (Finset.disjoint_empty_right _),
    card_edgePairsOfGraph_sdiff, Finset.card_empty, pow_zero, mul_one]

/-- Expectation of `subgraphCopyIndicator β (G ⊔ α)` under `erdosRenyi n p`
(`SteinIntro.tex:2320`). -/
theorem integral_subgraphCopyIndicator_sup {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (α β : SimpleGraph (Fin n)) :
    ∫ G, (subgraphCopyIndicator β (G ⊔ α) : ℝ) ∂erdosRenyi n p =
      p ^ (β.edgeSet \ α.edgeSet).ncard := by
  have hind : (fun G : SimpleGraph (Fin n) ↦ (subgraphCopyIndicator β (G ⊔ α) : ℝ)) =
      {G : SimpleGraph (Fin n) | subgraphCopyIndicator β (G ⊔ α) = 1}.indicator 1 := by
    ext G
    by_cases h1 : subgraphCopyIndicator β (G ⊔ α) = 1
    · have hmem : G ∈ {G : SimpleGraph (Fin n) | subgraphCopyIndicator β (G ⊔ α) = 1} := h1
      rw [Set.indicator_of_mem hmem, h1]; norm_num
    · have hnot : G ∉ {G : SimpleGraph (Fin n) | subgraphCopyIndicator β (G ⊔ α) = 1} := h1
      have h0 := (subgraphCopyIndicator_zero_or_one β (G ⊔ α)).resolve_right h1
      rw [Set.indicator_of_notMem hnot, h0, Nat.cast_zero]
  rw [hind, integral_indicator_one MeasurableSet.of_discrete,
    erdosRenyi_real_subgraphCopyIndicator_sup_eq_one hp0 hp1 α β]

open Classical in
/-- Edge-overlap sum identity (`SteinIntro.tex:2316-2321`): for any `α, γ ∈ subgraphCopies H n`,
$\sum_{\beta \in \Gamma \setminus \{\gamma\}} \mathbb{E}[X_\beta(G \sqcup \gamma) - X_\beta(G)] =
\sum_{t=1}^{e_H - 1} |\Gamma_\alpha^t| (p^t - p^{e_H})$. -/
theorem sum_erase_integral_subgraphCopyIndicator_sup_sub {V : Type*} (H : SimpleGraph V)
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {α γ : SimpleGraph (Fin n)}
    (hα : α ∈ subgraphCopies H n) (hγ : γ ∈ subgraphCopies H n) :
    (∑ β ∈ (subgraphCopies H n).erase γ,
        ∫ G, ((subgraphCopyIndicator β (G ⊔ γ) : ℝ) -
          (subgraphCopyIndicator β G : ℝ)) ∂erdosRenyi n p) =
      ∑ t ∈ Finset.Ico 1 H.edgeSet.ncard,
        ((subgraphCopiesWithDiffEdges H n α t).card : ℝ) * (p ^ t - p ^ H.edgeSet.ncard) := by
  let e_H := H.edgeSet.ncard
  let Γ_t := subgraphCopiesWithDiffEdges H n α
  have herase : (subgraphCopies H n).erase γ =
      (Finset.Ico 1 (e_H + 1)).biUnion (subgraphCopiesWithDiffEdges H n γ) :=
    erase_subgraphCopies_eq_biUnion H hγ
  have hdisj : (Finset.Ico 1 (e_H + 1) : Set ℕ).PairwiseDisjoint
      (subgraphCopiesWithDiffEdges H n γ) :=
    (pairwiseDisjoint_subgraphCopiesWithDiffEdges H n γ).subset (Set.subset_univ _)
  rw [herase, Finset.sum_biUnion hdisj]
  have hsum_t : ∀ t ∈ Finset.Ico 1 (e_H + 1),
      (∑ β ∈ subgraphCopiesWithDiffEdges H n γ t,
        ∫ G, ((subgraphCopyIndicator β (G ⊔ γ) : ℝ) -
          (subgraphCopyIndicator β G : ℝ)) ∂erdosRenyi n p) =
        ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H) := by
    intro t _
    have hterm : ∀ β ∈ subgraphCopiesWithDiffEdges H n γ t,
        ∫ G, ((subgraphCopyIndicator β (G ⊔ γ) : ℝ) -
          (subgraphCopyIndicator β G : ℝ)) ∂erdosRenyi n p = p ^ t - p ^ e_H := by
      intro β hβ
      rcases mem_subgraphCopiesWithDiffEdges.mp hβ with ⟨hβ_mem, hβ_diff⟩
      rw [integral_sub Integrable.of_finite Integrable.of_finite,
        integral_subgraphCopyIndicator_sup hp0 hp1 γ β,
        integral_subgraphCopyIndicator hp0 hp1 β,
        hβ_diff, ncard_edgeSet_of_mem_subgraphCopies hβ_mem]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      card_subgraphCopiesWithDiffEdges_eq H hγ hα t]
  rw [Finset.sum_congr rfl hsum_t]
  rcases Nat.eq_zero_or_pos e_H with he0 | he_pos
  · simp [e_H, he0]
  · rw [Finset.sum_Ico_succ_top he_pos, sub_self, mul_zero, add_zero]

/-! ### 2. Counterexample to exchangeability of subgraph indicators (`SteinIntro.tex:2298`, G2-1) -/

/-- **Counterexample (`ISSUE-SEC4.3.2-EXCH`, Critic G2-1)**: the claim at `SteinIntro.tex:2298`
that the subgraph copy indicators $(X_\alpha)_{\alpha \in \Gamma}$ are exchangeable is false for
$n \ge 5$: for triangles ($H = K_3$) in $G(5, 1/2)$, the two pairs of triangles
$\alpha_0 = \{0, 1, 2\}, \alpha_1 = \{0, 1, 3\}$ (sharing an edge) and
$\alpha_0 = \{0, 1, 2\}, \alpha_2 = \{0, 3, 4\}$ (sharing only a vertex) satisfy
$\mathbb{E}[X_{\alpha_0} X_{\alpha_1}] = (1/2)^5 = 1/32 \ne 1/64 = (1/2)^6 =
\mathbb{E}[X_{\alpha_0} X_{\alpha_2}]$. -/
theorem not_isExchangeableTuple_subgraphCopyIndicator_triangles :
    let Γ := subgraphCopies (SimpleGraph.cycleGraph 3) 5
    let X : {α : SimpleGraph (Fin 5) // α ∈ Γ} → SimpleGraph (Fin 5) → ℕ :=
      fun α G ↦ subgraphCopyIndicator α.1 G
    ¬ IsExchangeableTuple (erdosRenyi 5 (1 / 2)) X := by
  classical
  intro Γ X hEx
  let t₀ : Finset (Fin 5) := {0, 1, 2}
  let t₁ : Finset (Fin 5) := {0, 1, 3}
  let t₂ : Finset (Fin 5) := {0, 3, 4}
  have ht₀ : t₀.card = 3 := by decide
  have ht₁ : t₁.card = 3 := by decide
  have ht₂ : t₂.card = 3 := by decide
  have ht₀_mem : t₀ ∈ (Finset.univ : Finset (Fin 5)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ht₀⟩
  have ht₁_mem : t₁ ∈ (Finset.univ : Finset (Fin 5)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ht₁⟩
  have ht₂_mem : t₂ ∈ (Finset.univ : Finset (Fin 5)).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ht₂⟩
  let i₀ : {α : SimpleGraph (Fin 5) // α ∈ Γ} :=
    ⟨triangleSubgraph t₀, triangleSubgraph_mem_subgraphCopies ht₀_mem⟩
  let i₁ : {α : SimpleGraph (Fin 5) // α ∈ Γ} :=
    ⟨triangleSubgraph t₁, triangleSubgraph_mem_subgraphCopies ht₁_mem⟩
  let i₂ : {α : SimpleGraph (Fin 5) // α ∈ Γ} :=
    ⟨triangleSubgraph t₂, triangleSubgraph_mem_subgraphCopies ht₂_mem⟩
  have hi₀₁ : i₀ ≠ i₁ := by
    intro h
    have hts := triangleSubgraph_injective_of_two_le_card (by omega) (by omega)
      (congrArg Subtype.val h)
    revert hts; decide
  have hi₀₂ : i₀ ≠ i₂ := by
    intro h
    have hts := triangleSubgraph_injective_of_two_le_card (by omega) (by omega)
      (congrArg Subtype.val h)
    revert hts; decide
  let σ : Equiv.Perm {α : SimpleGraph (Fin 5) // α ∈ Γ} := Equiv.swap i₁ i₂
  have hσ₀ : σ i₀ = i₀ := Equiv.swap_apply_of_ne_of_ne hi₀₁ hi₀₂
  have hσ₁ : σ i₁ = i₂ := Equiv.swap_apply_left i₁ i₂
  let φ : ({α : SimpleGraph (Fin 5) // α ∈ Γ} → ℕ) → ℝ :=
    fun u ↦ (u i₀ : ℝ) * (u i₁ : ℝ)
  have hφ_meas : Measurable φ := Measurable.of_discrete
  have hid := (hEx σ).comp hφ_meas
  have hint_eq := hid.integral_eq
  dsimp [φ, X] at hint_eq
  rw [hσ₀, hσ₁] at hint_eq
  have hp0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  rw [integral_subgraphCopyIndicator_mul hp0 hp1 i₀.1 i₂.1,
    integral_subgraphCopyIndicator_mul hp0 hp1 i₀.1 i₁.1] at hint_eq
  have he₀ : i₀.1.edgeSet.ncard = 3 := ncard_edgeSet_triangleSubgraph_of_card_eq_three ht₀
  have hinter₀₂ : (t₀ ∩ t₂).card ≤ 1 := by decide
  have hinter₀₁ : (t₀ ∩ t₁).card = 2 := by decide
  have hdiff₀₂ : (i₂.1.edgeSet \ i₀.1.edgeSet).ncard = 3 := by
    dsimp [i₀, i₂]
    rw [ncard_edgeSet_diff_triangleSubgraph ht₀ ht₂,
      ncard_edgeSet_triangleSubgraph_of_card_le_one hinter₀₂]
  have hdiff₀₁ : (i₁.1.edgeSet \ i₀.1.edgeSet).ncard = 2 := by
    dsimp [i₀, i₁]
    rw [ncard_edgeSet_diff_triangleSubgraph ht₀ ht₁,
      ncard_edgeSet_triangleSubgraph_of_card_eq_two hinter₀₁]
  rw [he₀, hdiff₀₂, hdiff₀₁] at hint_eq
  norm_num at hint_eq

/-! ### 3. Theorem 4.14: Increasing coupling bound (`\label{thm122}`, `SteinIntro.tex:2257-2277`) -/

lemma sum_fintype_eq_add_sum_subtype_ne {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (v : ι → ℝ) :
    (∑ k : ι, v k) = v i + ∑ j : {j : ι // j ≠ i}, v j.1 := by
  have hsub : (∑ j : {j : ι // j ≠ i}, v j.1) = ∑ j ∈ Finset.univ.erase i, v j :=
    (Finset.sum_subtype (Finset.univ.erase i) (by simp) v).symm
  rw [hsub, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]

/-- **Theorem 4.14** (`\label{thm122}`, `SteinIntro.tex:2257-2277`; `ISSUE-THM-4.14` recording
`≤` in place of `=` at `L2268`). -/
theorem thm4_14_proof
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : ι → Ω → ℕ}
    {Y : (i : ι) → Ω → ({j : ι // j ≠ i} → ℕ)}
    {I : Ω → ι} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX_meas : ∀ i : ι, Measurable (X i))
    (hX_zo : ∀ i : ι, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : ι → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : ι, X i ω
    let Ws : Ω → ℕ := fun ω ↦ (∑ j : {j : ι // j ≠ I ω}, Y (I ω) ω j) + 1
    0 < r →
    (∑ i : ι, p i = (r : ℝ)) →
    (∀ i : ι, AEMeasurable (Y i) P) →
    (∀ i : ι,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : ι // j ≠ i}) ↦ X j.1 ω)) →
    (∀ i : ι, ∀ j : {j : ι // j ≠ i}, ∀ᵐ ω ∂P, X j.1 ω ≤ Y i ω j) →
    Measurable I →
    (∀ i : ι, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P (fun ω ↦ (Ws ω : ℝ)) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ) *
            ∑ i : ι, (p i / (r : ℝ)) * (p i + ∑ j : {j : ι // j ≠ i},
              ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P)) := by
  intro p W Ws hr hlam hY_meas hY_law hmono hI_meas hI_prob hI_indep _hZ_meas hZ_law
  have hr_pos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hlam_pos : 0 < ∑ i : ι, p i := by rw [hlam]; exact hr_pos
  have hI_prob_sum : ∀ i : ι, P.real (I ⁻¹' {i}) = p i / ∑ k : ι, p k := fun i ↦ by
    rw [hlam, hI_prob i]
  have hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P (fun ω ↦ (Ws ω : ℝ)) := by
    have h := sizeBias_sum_of_nat_zero_one_fintype P hX_meas hX_zo hlam_pos hY_meas hY_law
      hI_meas hI_prob_sum hI_indep
    simpa only [W, Ws] using h
  refine ⟨hSB, ?_⟩
  have hset_meas : ∀ i : ι, MeasurableSet {ω | X i ω = 1} :=
    fun i ↦ hX_meas i (measurableSet_singleton 1)
  have hX_ae_ind : ∀ i : ι,
      (fun ω ↦ (X i ω : ℝ)) =ᵐ[P]
        ({ω | X i ω = 1} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) := by
    intro i
    refine (hX_zo i).mono fun ω hω ↦ ?_
    rcases hω with h0 | h1
    · simp [h0]
    · simp [h1]
  have hX_int : ∀ i : ι, Integrable (fun ω ↦ (X i ω : ℝ)) P := fun i ↦
    ((integrable_const (1 : ℝ)).indicator (hset_meas i)).congr (hX_ae_ind i).symm
  have hX_mean : ∀ i : ι, ∫ ω, (X i ω : ℝ) ∂P = p i := fun i ↦ by
    rw [integral_congr_ae (hX_ae_ind i),
      integral_indicator (hset_meas i), setIntegral_one_eq_measureReal]
  have hW_meas : Measurable W := Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas i
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) := by
    have hfun : (fun ω ↦ (W ω : ℝ)) = fun ω ↦ ∑ i : ι, (X i ω : ℝ) := by
      ext ω; simp [W, Nat.cast_sum]
    rw [hfun, integral_finsetSum Finset.univ fun i _ ↦ hX_int i,
      Finset.sum_congr rfl fun i _ ↦ hX_mean i, hlam]
  have hY_le_one :
      ∀ i : ι, 0 < p i → ∀ j : {j : ι // j ≠ i}, ∀ᵐ ω ∂P, Y i ω j ≤ 1 := by
    intro i hpi j
    have hX_le : ∀ᵐ ω ∂P, X j.1 ω ≤ 1 :=
      (hX_zo j.1).mono fun ω hω ↦ by rcases hω with h | h <;> omega
    have hcond_le : ∀ᵐ ω ∂(ProbabilityTheory.cond P {ω | X i ω = 1}), X j.1 ω ≤ 1 :=
      ProbabilityTheory.cond_absolutelyContinuous.ae_le hX_le
    let rest : Ω → ({k : ι // k ≠ i} → ℕ) := fun ω k ↦ X k.1 ω
    have hrest_meas : Measurable rest := Measurable.of_eval fun k ↦ hX_meas k.1
    let S : Set ({k : ι // k ≠ i} → ℕ) := {u | u j ≤ 1}
    have hS_meas : MeasurableSet S := MeasurableSet.of_discrete
    have hmap_cond : ∀ᵐ u ∂((ProbabilityTheory.cond P {ω | X i ω = 1}).map rest), u ∈ S :=
      (ae_map_iff hrest_meas.aemeasurable hS_meas).mpr hcond_le
    rw [← hY_law i hpi] at hmap_cond
    exact (ae_map_iff (hY_meas i) hS_meas).mp hmap_cond
  have hY_int : ∀ i : ι, 0 < p i → ∀ j : {j : ι // j ≠ i},
      Integrable (fun ω ↦ (Y i ω j : ℝ)) P := by
    intro i hpi j
    let proj : ({k : ι // k ≠ i} → ℕ) → ℝ := fun u ↦ (u j : ℝ)
    have hproj : Measurable proj :=
      (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply j)
    have hm : AEMeasurable (fun ω ↦ (Y i ω j : ℝ)) P := hproj.comp_aemeasurable (hY_meas i)
    refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
    refine (hY_le_one i hpi j).mono fun ω hω ↦ ?_
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hω
  let V_all : Ω → (ι → ℕ) × ((i : ι) → {j : ι // j ≠ i} → ℕ) :=
    fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)
  have hV_meas : AEMeasurable V_all P :=
    (Measurable.of_eval hX_meas).aemeasurable.prodMk (AEMeasurable.of_eval hY_meas)
  let g_D : ι → ((ι → ℕ) × ((i : ι) → {j : ι // j ≠ i} → ℕ)) → ℝ :=
    fun i v ↦ (v.1 i : ℝ) + ∑ j : {j : ι // j ≠ i}, ((v.2 i j : ℝ) - (v.1 j.1 : ℝ))
  have hg_D_meas : ∀ i : ι, Measurable (g_D i) := fun _ ↦ Measurable.of_discrete
  let D : ι → Ω → ℝ := fun i ω ↦ g_D i (V_all ω)
  let term : ι → Ω → ℝ := fun i ↦ (I ⁻¹' {i}).indicator (D i)
  have hsub_j_int : ∀ i : ι, 0 < p i → ∀ j : {j : ι // j ≠ i},
      Integrable (fun ω ↦ (Y i ω j : ℝ) - (X j.1 ω : ℝ)) P :=
    fun i hpi j ↦ (hY_int i hpi j).sub (hX_int j.1)
  have hsum_j_int : ∀ i : ι, 0 < p i →
      Integrable
        (fun ω ↦ ∑ j : {j : ι // j ≠ i}, ((Y i ω j : ℝ) - (X j.1 ω : ℝ))) P :=
    fun i hpi ↦ integrable_finsetSum Finset.univ fun j _ ↦ hsub_j_int i hpi j
  have hD_int : ∀ i : ι, 0 < p i → Integrable (D i) P :=
    fun i hpi ↦ (hX_int i).add (hsum_j_int i hpi)
  have hterm_int_eq : ∀ i : ι,
      Integrable (term i) P ∧
        ∫ ω, term i ω ∂P =
          (p i / (r : ℝ)) *
            (p i +
              ∑ j : {j : ι // j ≠ i}, ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P) := by
    intro i
    have hpi_nn : 0 ≤ p i := measureReal_nonneg
    rcases hpi_nn.eq_or_lt with hpi0 | hpi_pos
    · have hPI_real0 : P.real (I ⁻¹' {i}) = 0 := by rw [hI_prob i, ← hpi0, zero_div]
      have hPI0 : P (I ⁻¹' {i}) = 0 := (measureReal_eq_zero_iff).mp hPI_real0
      have hterm_ae0 : term i =ᵐ[P] 0 :=
        (measure_eq_zero_iff_ae_notMem.mp hPI0).mono fun ω hω ↦
          Set.indicator_of_notMem hω _
      refine ⟨(integrable_zero Ω ℝ P).congr hterm_ae0.symm, ?_⟩
      rw [integral_eq_zero_of_ae hterm_ae0, ← hpi0, zero_div, zero_mul]
    · have hIi_meas : MeasurableSet (I ⁻¹' {i}) := hI_meas (measurableSet_singleton i)
      refine ⟨(hD_int i hpi_pos).indicator hIi_meas, ?_⟩
      let fI : ι → ℝ := ({i} : Set ι).indicator (fun _ ↦ (1 : ℝ))
      have hfI_meas : Measurable fI := measurable_const.indicator (measurableSet_singleton i)
      have hpt : term i = fun ω ↦ fI (I ω) * g_D i (V_all ω) := by
        ext ω; by_cases hω : I ω = i <;> simp [term, D, fI, hω]
      have hfI_comp : (fun ω ↦ fI (I ω)) = (I ⁻¹' {i}).indicator (fun _ ↦ (1 : ℝ)) := by
        ext ω; by_cases hω : I ω = i <;> simp [fI, hω]
      have hint_prod : ∫ ω, term i ω ∂P = (p i / (r : ℝ)) * ∫ ω, D i ω ∂P := by
        rw [hpt,
          hI_indep.integral_fun_comp_mul_comp hI_meas.aemeasurable hV_meas
            hfI_meas.stronglyMeasurable.aestronglyMeasurable
            (hg_D_meas i).stronglyMeasurable.aestronglyMeasurable,
          hfI_comp, integral_indicator hIi_meas, setIntegral_one_eq_measureReal, hI_prob i]
      have hint_D : ∫ ω, D i ω ∂P =
          p i +
            ∑ j : {j : ι // j ≠ i}, ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P := by
        dsimp [D, g_D, V_all]
        rw [integral_add (hX_int i) (hsum_j_int i hpi_pos), hX_mean i,
          integral_finsetSum Finset.univ fun j _ ↦ hsub_j_int i hpi_pos j]
      rw [hint_prod, hint_D]
  have hsum_term_eq : (fun ω ↦ D (I ω) ω) = fun ω ↦ ∑ i : ι, term i ω := by
    ext ω; symm
    rw [Finset.sum_eq_single (I ω)]
    · simp [term]
    · intro i _ hi; exact Set.indicator_of_notMem (by simpa using hi.symm) _
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hDI_int : Integrable (fun ω ↦ D (I ω) ω) P := by
    rw [hsum_term_eq]
    exact integrable_finsetSum Finset.univ fun i _ ↦ (hterm_int_eq i).1
  have hmono_all : ∀ᵐ ω ∂P, ∀ i : ι, ∀ j : {j : ι // j ≠ i}, X j.1 ω ≤ Y i ω j :=
    eventually_all.mpr fun i ↦ eventually_all.mpr fun j ↦ hmono i j
  have habs_le_ae : ∀ᵐ ω ∂P, |(W ω : ℝ) + 1 - (Ws ω : ℝ)| ≤ D (I ω) ω := by
    refine hmono_all.mono fun ω hω ↦ ?_
    let i := I ω
    have hW_split :
        (W ω : ℝ) = (X i ω : ℝ) + ∑ j : {j : ι // j ≠ i}, (X j.1 ω : ℝ) := by
      dsimp [W]; rw [Nat.cast_sum]
      exact sum_fintype_eq_add_sum_subtype_ne i (fun k ↦ (X k ω : ℝ))
    have hWs_split : (Ws ω : ℝ) = (∑ j : {j : ι // j ≠ i}, (Y i ω j : ℝ)) + 1 := by
      simp [Ws, i, Nat.cast_add, Nat.cast_sum]
    have hdiff_eq : (W ω : ℝ) + 1 - (Ws ω : ℝ) =
        (X i ω : ℝ) - ∑ j : {j : ι // j ≠ i}, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) := by
      rw [hW_split, hWs_split, Finset.sum_sub_distrib]; ring
    have hXi_nn : 0 ≤ (X i ω : ℝ) := Nat.cast_nonneg _
    have hsum_nn : 0 ≤ ∑ j : {j : ι // j ≠ i}, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) :=
      Finset.sum_nonneg fun j _ ↦ sub_nonneg.mpr (Nat.cast_le.mpr (hω i j))
    rw [hdiff_eq]
    dsimp [D, g_D, V_all, i]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hXi_nn, abs_of_nonneg hsum_nn])
  have hlintegral_le :
      (∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - (Ws ω : ℝ)| ∂P) ≤
        ENNReal.ofReal
          (∑ i : ι, (p i / (r : ℝ)) * (p i +
            ∑ j : {j : ι // j ≠ i}, ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P)) := by
    have h1 : (∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - (Ws ω : ℝ)| ∂P) ≤
        ∫⁻ ω, ENNReal.ofReal (D (I ω) ω) ∂P :=
      lintegral_mono_ae (habs_le_ae.mono fun ω hω ↦ ENNReal.ofReal_le_ofReal hω)
    have hDI_nn : 0 ≤ᵐ[P] fun ω ↦ D (I ω) ω :=
      habs_le_ae.mono fun ω hω ↦ (abs_nonneg _).trans hω
    have h2 : (∫⁻ ω, ENNReal.ofReal (D (I ω) ω) ∂P) =
        ENNReal.ofReal (∫ ω, D (I ω) ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hDI_int hDI_nn).symm
    have h3 : ∫ ω, D (I ω) ω ∂P =
        ∑ i : ι, (p i / (r : ℝ)) *
          (p i +
            ∑ j : {j : ι // j ≠ i}, ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P) := by
      rw [hsum_term_eq, integral_finsetSum Finset.univ fun i _ ↦ (hterm_int_eq i).1,
        Finset.sum_congr rfl fun i _ ↦ (hterm_int_eq i).2]
    rw [← h3, ← h2]
    exact h1
  have htv := tvDist_poisson_le_of_isSizeBias P P' hr hW_meas.aemeasurable hW_mean hSB
    _hZ_meas hZ_law
  refine htv.trans ?_
  have hmin_nn : 0 ≤ min 1 (r : ℝ) := le_min zero_le_one hr_pos.le
  rw [ENNReal.ofReal_mul hmin_nn]
  exact mul_le_mul_of_nonneg_left hlintegral_le zero_le

/-! ### 4. Theorem 4.15 and Coupling Facts (`SteinIntro.tex:2288-2312`) -/

private lemma map_fst_cond_prod_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [DiscreteMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (A : Set α) :
    (ProbabilityTheory.cond (μ.prod ν) (A ×ˢ Set.univ)).map Prod.fst =
      ProbabilityTheory.cond μ A := by
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have hAU : MeasurableSet (A ×ˢ (Set.univ : Set β)) := hA.prod MeasurableSet.univ
  refine Measure.ext_of_singleton fun x ↦ ?_
  rw [Measure.map_apply measurable_fst (measurableSet_singleton x),
    ProbabilityTheory.cond_apply hAU, ProbabilityTheory.cond_apply hA]
  have hpre : Prod.fst ⁻¹' ({x} : Set α) = {x} ×ˢ (Set.univ : Set β) := by ext p; simp
  have hinter :
      (A ×ˢ (Set.univ : Set β)) ∩ ({x} ×ˢ Set.univ) = (A ∩ {x}) ×ˢ Set.univ := by
    ext p; simp
  rw [hpre, hinter, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, mul_one]

private lemma poissonLaw_zero : poissonLaw 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun k ↦ ?_
  rw [poissonLaw, ProbabilityTheory.poissonMeasure_singleton,
    Measure.dirac_apply' _ (measurableSet_singleton k)]
  rcases k with _ | k <;> simp

open Classical in
/-- **Theorem 4.15** (`\label{thm123}`, `SteinIntro.tex:2288-2295`), proved via Theorem 4.14 with
a uniform random index $I$ on $\Gamma$ (bypassing the false exchangeability claim at `L2298`, per
Critic G2-1). -/
theorem thm4_15_proof
    {Ω Ω' V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (H : SimpleGraph V) {n : ℕ} {p : ℝ} {r : ℝ≥0}
    {G : Ω → SimpleGraph (Fin n)} {Z : Ω' → ℕ}
    (hV0 : 0 < Fintype.card V) (_hVn : Fintype.card V ≤ n)
    (hiso : ∀ v : V, ¬ H.IsIsolated v)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hG_meas : AEMeasurable G P) (hG_law : P.map G = erdosRenyi n p) :
    let Γ : Finset (SimpleGraph (Fin n)) := subgraphCopies H n
    let e_H : ℕ := H.edgeSet.ncard
    let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
    ((r : ℝ) = (Γ.card : ℝ) * p ^ e_H) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    ∀ α ∈ Γ,
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ) *
            (p ^ e_H +
              ∑ β ∈ Γ.erase α,
                ∫ ω,
                  ((subgraphCopyIndicator β (G ω ⊔ α) : ℝ) -
                    (subgraphCopyIndicator β (G ω) : ℝ)) ∂P)) := by
  intro Γ e_H W hr_eq hZ_meas hZ_law α hα
  have hcount_meas : Measurable (subgraphCount H n) := Measurable.of_discrete
  have hmap_W : P.map W = (erdosRenyi n p).map (subgraphCount H n) := by
    rw [← hG_law, map_map_of_measurable_aemeasurable hcount_meas hG_meas]; rfl
  have hint_P_eq : ∀ β : SimpleGraph (Fin n),
      ∫ ω, ((subgraphCopyIndicator β (G ω ⊔ α) : ℝ) -
          (subgraphCopyIndicator β (G ω) : ℝ)) ∂P =
        ∫ G₀, ((subgraphCopyIndicator β (G₀ ⊔ α) : ℝ) -
          (subgraphCopyIndicator β G₀ : ℝ)) ∂erdosRenyi n p := by
    intro β
    let φ : SimpleGraph (Fin n) → ℝ := fun G₀ ↦
      (subgraphCopyIndicator β (G₀ ⊔ α) : ℝ) - (subgraphCopyIndicator β G₀ : ℝ)
    have hφ_meas : Measurable φ := Measurable.of_discrete
    rw [← hG_law, integral_map hG_meas hφ_meas.stronglyMeasurable.aestronglyMeasurable]
  simp_rw [hint_P_eq]
  have he_H_pos : 0 < e_H := ncard_edgeSet_pos_of_not_isIsolated H hV0 hiso
  rcases hp0.eq_or_lt with rfl | hp_pos
  · have hpow0 : (0 : ℝ) ^ e_H = 0 := zero_pow he_H_pos.ne'
    have hr0_real : (r : ℝ) = 0 := by rw [hr_eq, hpow0, mul_zero]
    have hr0 : r = 0 := NNReal.coe_eq_zero.mp hr0_real
    subst hr0
    have hW_ae0 : ∀ᵐ G₀ ∂erdosRenyi n 0, subgraphCount H n G₀ = 0 := by
      have hall : ∀ γ ∈ Γ, ∀ᵐ G₀ ∂erdosRenyi n 0,
          subgraphCopyIndicator γ G₀ = 0 := by
        intro γ hγ
        have hprob0 : (erdosRenyi n 0).real {G₀ | subgraphCopyIndicator γ G₀ = 1} = 0 := by
          rw [erdosRenyi_real_subgraphCopyIndicator_eq_one le_rfl zero_le_one γ,
            ncard_edgeSet_of_mem_subgraphCopies hγ, hpow0]
        have hmeas0 : (erdosRenyi n 0) {G₀ | subgraphCopyIndicator γ G₀ = 1} = 0 :=
          (measureReal_eq_zero_iff).mp hprob0
        refine (measure_eq_zero_iff_ae_notMem.mp hmeas0).mono fun G₀ hG₀ ↦ ?_
        exact (subgraphCopyIndicator_zero_or_one γ G₀).resolve_right hG₀
      have hall' :
          ∀ᵐ G₀ ∂erdosRenyi n 0, ∀ γ ∈ Γ, subgraphCopyIndicator γ G₀ = 0 :=
        (Filter.eventually_all_finset Γ).mpr hall
      refine hall'.mono fun G₀ hG₀ ↦ ?_
      dsimp [subgraphCount]; exact Finset.sum_eq_zero hG₀
    have hmap_zero : (erdosRenyi n 0).map (subgraphCount H n) = Measure.dirac 0 := by
      have hconst : (erdosRenyi n 0).map (fun _ : SimpleGraph (Fin n) ↦ (0 : ℕ)) =
          Measure.dirac 0 := by simp [Measure.map_const]
      rw [Measure.map_congr hW_ae0, hconst]
    rw [hmap_W, hmap_zero, hZ_law, poissonLaw_zero]
    simp [tvDist, ipm]
  · have hΓ_pos : 0 < Γ.card := Finset.card_pos.mpr ⟨α, hα⟩
    have hΓ_r_pos : (0 : ℝ) < (Γ.card : ℝ) := Nat.cast_pos.mpr hΓ_pos
    have hp_pow_pos : 0 < p ^ e_H := pow_pos hp_pos e_H
    have hr_pos : 0 < r := NNReal.coe_pos.mp (by rw [hr_eq]; positivity)
    let ι := {γ : SimpleGraph (Fin n) // γ ∈ Γ}
    have : Nonempty ι := ⟨⟨α, hα⟩⟩
    let μ := erdosRenyi n p
    let ν := (PMF.uniformOfFintype ι).toMeasure
    let Q := μ.prod ν
    let X : ι → SimpleGraph (Fin n) × ι → ℕ :=
      fun i ω₀ ↦ subgraphCopyIndicator i.1 ω₀.1
    let Y : (i : ι) → SimpleGraph (Fin n) × ι → ({j : ι // j ≠ i} → ℕ) :=
      fun i ω₀ j ↦ subgraphCopyIndicator j.1.1 (ω₀.1 ⊔ i.1)
    let I : SimpleGraph (Fin n) × ι → ι := Prod.snd
    have hQ_fst : Q.map Prod.fst = μ := by simp [Q, Measure.map_fst_prod]
    have hQ_snd : Q.map Prod.snd = ν := by simp [Q, Measure.map_snd_prod]
    have hX_meas : ∀ i : ι, Measurable (X i) := fun _ ↦ Measurable.of_discrete
    have hX_zo : ∀ i : ι, ∀ᵐ ω₀ ∂Q, X i ω₀ = 0 ∨ X i ω₀ = 1 :=
      fun i ↦ Filter.Eventually.of_forall fun ω₀ ↦
        subgraphCopyIndicator_zero_or_one i.1 ω₀.1
    have hpi_eq : ∀ i : ι, Q.real {ω₀ | X i ω₀ = 1} = p ^ e_H := by
      intro i
      have hpre : {ω₀ : SimpleGraph (Fin n) × ι | X i ω₀ = 1} =
          Prod.fst ⁻¹' {G₀ : SimpleGraph (Fin n) | subgraphCopyIndicator i.1 G₀ = 1} := rfl
      rw [hpre, ← map_measureReal_apply measurable_fst MeasurableSet.of_discrete, hQ_fst,
        erdosRenyi_real_subgraphCopyIndicator_eq_one hp_pos.le hp1 i.1,
        ncard_edgeSet_of_mem_subgraphCopies i.2]
    have hlam_Q : (∑ i : ι, Q.real {ω₀ | X i ω₀ = 1}) = (r : ℝ) := by
      simp_rw [hpi_eq]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, hr_eq]
    have hY_meas : ∀ i : ι, AEMeasurable (Y i) Q :=
      fun _ ↦ Measurable.of_discrete.aemeasurable
    have hY_law : ∀ i : ι, 0 < Q.real {ω₀ | X i ω₀ = 1} →
        Q.map (Y i) =
          (ProbabilityTheory.cond Q {ω₀ | X i ω₀ = 1}).map
            (fun ω₀ (j : {j : ι // j ≠ i}) ↦ X j.1 ω₀) := by
      intro i _
      let rest : SimpleGraph (Fin n) → ({j : ι // j ≠ i} → ℕ) :=
        fun G₀ j ↦ subgraphCopyIndicator j.1.1 G₀
      let sup_i : SimpleGraph (Fin n) → SimpleGraph (Fin n) := fun G₀ ↦ G₀ ⊔ i.1
      have hrest_meas : Measurable rest := Measurable.of_discrete
      have hsup_meas : Measurable sup_i := Measurable.of_discrete
      have hY_comp : Y i = (rest ∘ sup_i) ∘ Prod.fst := rfl
      have h1 : Q.map (Y i) = (μ.map sup_i).map rest := by
        rw [hY_comp, ← Measure.map_map (hrest_meas.comp hsup_meas) measurable_fst, hQ_fst,
          Measure.map_map hrest_meas hsup_meas]
      have hset_prod : {ω₀ : SimpleGraph (Fin n) × ι | X i ω₀ = 1} =
          {G₀ : SimpleGraph (Fin n) | subgraphCopyIndicator i.1 G₀ = 1} ×ˢ Set.univ := by
        ext ⟨G₀, k⟩; simp [X]
      have h2 : (ProbabilityTheory.cond Q {ω₀ | X i ω₀ = 1}).map
            (fun ω₀ (j : {j : ι // j ≠ i}) ↦ X j.1 ω₀) =
          (ProbabilityTheory.cond μ {G₀ | subgraphCopyIndicator i.1 G₀ = 1}).map rest := by
        rw [hset_prod, ← map_fst_cond_prod_univ μ ν, Measure.map_map hrest_meas measurable_fst]
        rfl
      rw [h1, h2, erdosRenyi_cond_subgraphCopyIndicator_eq_map_sup hp_pos hp1 i.1]
    have hmono :
        ∀ i : ι, ∀ j : {j : ι // j ≠ i}, ∀ᵐ ω₀ ∂Q, X j.1 ω₀ ≤ Y i ω₀ j :=
      fun i j ↦ Filter.Eventually.of_forall fun ω₀ ↦
        subgraphCopyIndicator_le_sup i.1 j.1.1 ω₀.1
    have hI_meas : Measurable I := measurable_snd
    have hI_prob :
        ∀ i : ι, Q.real (I ⁻¹' {i}) = Q.real {ω₀ | X i ω₀ = 1} / (r : ℝ) := by
      intro i
      rw [hpi_eq i, hr_eq,
        ← map_measureReal_apply measurable_snd (measurableSet_singleton i),
        hQ_snd, measureReal_def]
      dsimp [ν]
      rw [PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
        PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
        Fintype.card_coe, ← one_div,
        ← mul_div_mul_right 1 (Γ.card : ℝ) hp_pow_pos.ne', one_mul]
    have hI_indep :
        ProbabilityTheory.IndepFun I
          (fun ω₀ ↦ (fun i ↦ X i ω₀, fun i ↦ Y i ω₀)) Q := by
      let φ : SimpleGraph (Fin n) → (ι → ℕ) × ((i : ι) → {j : ι // j ≠ i} → ℕ) :=
        fun G₀ ↦ (fun i ↦ subgraphCopyIndicator i.1 G₀,
          fun i j ↦ subgraphCopyIndicator j.1.1 (G₀ ⊔ i.1))
      have hφ_meas : Measurable φ := Measurable.of_discrete
      exact (ProbabilityTheory.indepFun_prod (μ := μ) (ν := ν) hφ_meas measurable_id).symm
    have h14 := (thm4_14_proof Q P' hX_meas hX_zo hr_pos hlam_Q hY_meas hY_law hmono
      hI_meas hI_prob hI_indep hZ_meas hZ_law).2
    have hW_Q_eq : (fun ω₀ : SimpleGraph (Fin n) × ι ↦ ∑ i : ι, X i ω₀) =
        subgraphCount H n ∘ Prod.fst := by
      ext ⟨G₀, _⟩; dsimp [X, subgraphCount]
      exact Finset.sum_coe_sort Γ (fun γ ↦ subgraphCopyIndicator γ G₀)
    have hmap_WQ : Q.map (fun ω₀ ↦ ∑ i : ι, X i ω₀) = P.map W := by
      rw [hW_Q_eq, ← Measure.map_map hcount_meas measurable_fst, hQ_fst, hmap_W]
    rw [hmap_WQ] at h14
    refine h14.trans (le_of_eq ?_)
    congr 2
    have hterm_i : ∀ i : ι,
        (Q.real {ω₀ | X i ω₀ = 1} / (r : ℝ)) *
          (Q.real {ω₀ | X i ω₀ = 1} +
            ∑ j : {j : ι // j ≠ i},
              ∫ ω₀, ((Y i ω₀ j : ℝ) - (X j.1 ω₀ : ℝ)) ∂Q) =
          (1 / (Γ.card : ℝ)) *
            (p ^ e_H +
              ∑ β ∈ Γ.erase α,
                ∫ G₀, ((subgraphCopyIndicator β (G₀ ⊔ α) : ℝ) -
                  (subgraphCopyIndicator β G₀ : ℝ)) ∂erdosRenyi n p) := by
      intro i
      have hdiv : Q.real {ω₀ | X i ω₀ = 1} / (r : ℝ) = 1 / (Γ.card : ℝ) := by
        rw [hpi_eq i, hr_eq, ← mul_div_mul_right 1 (Γ.card : ℝ) hp_pow_pos.ne', one_mul]
      rw [hdiv, hpi_eq i]
      congr 2
      have hij_int : ∀ j : {j : ι // j ≠ i},
          ∫ ω₀, ((Y i ω₀ j : ℝ) - (X j.1 ω₀ : ℝ)) ∂Q =
            ∫ G₀, ((subgraphCopyIndicator j.1.1 (G₀ ⊔ i.1) : ℝ) -
              (subgraphCopyIndicator j.1.1 G₀ : ℝ)) ∂μ := by
        intro j
        let ψ : SimpleGraph (Fin n) → ℝ :=
          fun G₀ ↦ (subgraphCopyIndicator j.1.1 (G₀ ⊔ i.1) : ℝ) -
            (subgraphCopyIndicator j.1.1 G₀ : ℝ)
        have hψ_meas : Measurable ψ := Measurable.of_discrete
        rw [← hQ_fst, integral_map measurable_fst.aemeasurable
          hψ_meas.stronglyMeasurable.aestronglyMeasurable]
      simp_rw [hij_int]
      have hbij :
          (∑ j : {j : ι // j ≠ i},
            ∫ G₀, ((subgraphCopyIndicator j.1.1 (G₀ ⊔ i.1) : ℝ) -
              (subgraphCopyIndicator j.1.1 G₀ : ℝ)) ∂μ) =
            ∑ β ∈ Γ.erase i.1,
              ∫ G₀, ((subgraphCopyIndicator β (G₀ ⊔ i.1) : ℝ) -
                (subgraphCopyIndicator β G₀ : ℝ)) ∂μ := by
        refine Finset.sum_bij (fun j _ ↦ j.1.1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
        · intro j _; exact Finset.mem_erase.mpr ⟨fun h ↦ j.2 (Subtype.ext h), j.1.2⟩
        · intro j₁ _ j₂ _ h; exact Subtype.ext (Subtype.ext h)
        · intro β hβ
          rcases Finset.mem_erase.mp hβ with ⟨hne, hβΓ⟩
          exact ⟨⟨⟨β, hβΓ⟩, fun h ↦ hne (congrArg Subtype.val h)⟩,
            Finset.mem_univ _, rfl⟩
      rw [hbij,
        sum_erase_integral_subgraphCopyIndicator_sup_sub H hp_pos.le hp1 hα i.2,
        ← sum_erase_integral_subgraphCopyIndicator_sup_sub H hp_pos.le hp1 hα hα]
    rw [Finset.sum_congr rfl fun i _ ↦ hterm_i i, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, nsmul_eq_mul, ← mul_assoc, mul_one_div_cancel hΓ_r_pos.ne', one_mul]

open Classical in
/-- Proof of `Sec4_3_2_subgraph_coupling` (`SteinIntro.tex:2299-2307` items 1–3). -/
theorem sec4_3_2_subgraph_coupling_proof
    {V : Type*} [Fintype V] (H : SimpleGraph V)
    {n : ℕ} {p : ℝ} {α : SimpleGraph (Fin n)}
    (hV0 : 0 < Fintype.card V) (hVn : Fintype.card V ≤ n)
    (hiso : ∀ v : V, ¬ H.IsIsolated v)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hα : α ∈ subgraphCopies H n) :
    let Γ : Finset (SimpleGraph (Fin n)) := subgraphCopies H n
    let e_H : ℕ := H.edgeSet.ncard
    (0 < p →
      (erdosRenyi n p).map
          (fun G (β : {β : SimpleGraph (Fin n) // β ∈ Γ.erase α}) ↦
            subgraphCopyIndicator β.1 (G ⊔ α)) =
        (ProbabilityTheory.cond (erdosRenyi n p) {G | subgraphCopyIndicator α G = 1}).map
          (fun G (β : {β : SimpleGraph (Fin n) // β ∈ Γ.erase α}) ↦
            subgraphCopyIndicator β.1 G)) ∧
    (∀ β ∈ Γ.erase α, ∀ G : SimpleGraph (Fin n),
      subgraphCopyIndicator β G ≤ subgraphCopyIndicator β (G ⊔ α)) ∧
    (∫ G, (subgraphCopyIndicator α G : ℝ) ∂erdosRenyi n p = p ^ e_H) :=
  subgraph_coupling_facts H hV0 hVn hiso hp0 hp1 hα

end SteinMethod
