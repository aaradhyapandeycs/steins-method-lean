/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Subgraph.Cycles
import Formalization.PoissonSizeBias.Subgraph.IncreasingCoupling

/-!
# Subgraph Count Bounds, Variance Wrappers, and Examples 4.7–4.8 (`Increasing`)

Completes Section 4.3.1–4.3.2 (`SteinIntro.tex:2253-2376`), re-exporting
`Formalization.PoissonSizeBias.Subgraph.IncreasingCoupling` and proving:

* `cor4_16_proof`, `cor4_16_holds_proof`: **Corollary 4.16** (`\label{cor123}`,
  `SteinIntro.tex:2313-2331`), edge-overlap decomposition and variance formula.
* `ex4_7_proof`, `ex4_7_holds_proof`: **Example 4.7** (*Triangles*, `SteinIntro.tex:2334-2343`,
  eq. `(4.13)` `\label{124}`).
* `ex4_8_proof`, `ex4_8_holds_proof`: **Example 4.8** (*$k$-cycles*, `SteinIntro.tex:2344-2366`,
  eq. `(4.14)` `\label{125}`; `ISSUE-TYPO-4.8`).
* `thm4_14_variance_proof`, `thm4_15_variance_proof`: variance-form statements matching `Thm4_14`
  and `Thm4_15` in `Formalization/Statements/Sec4.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### 1. Corollary 4.16 (`\label{cor123}`, `SteinIntro.tex:2316-2330`) -/

open Classical in
/-- **Corollary 4.16** (`\label{cor123}`, `SteinIntro.tex:2316-2330`). -/
theorem cor4_16_proof
    {Ω Ω' V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype V]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (H : SimpleGraph V) {n : ℕ} {p : ℝ} {r : ℝ≥0}
    {G : Ω → SimpleGraph (Fin n)} {Z : Ω' → ℕ}
    (hV0 : 0 < Fintype.card V) (hVn : Fintype.card V ≤ n)
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
      let Γ_t : ℕ → Finset (SimpleGraph (Fin n)) := subgraphCopiesWithDiffEdges H n α
      let B1 : ℝ :=
        min 1 (r : ℝ) *
          (p ^ e_H + ∑ β ∈ Γ.erase α,
            ∫ ω,
              ((subgraphCopyIndicator β (G ω ⊔ α) : ℝ) -
                (subgraphCopyIndicator β (G ω) : ℝ)) ∂P)
      let B2 : ℝ :=
        min 1 (r : ℝ) *
          (p ^ e_H + ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H))
      let B3 : ℝ :=
        min 1 (r : ℝ)⁻¹ *
          (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
            2 * (r : ℝ) * p ^ e_H)
      tvDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal B1 ∧
      B1 = B2 ∧
      (0 < r → B2 = B3) ∧
      ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
        (r : ℝ) * (1 - p ^ e_H +
          ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H)) := by
  intro Γ e_H W hr_eq hZ_meas hZ_law α hα Γ_t B1 B2 B3
  have h15 := thm4_15_proof P P' H hV0 hVn hiso hp0 hp1 hG_meas hG_law hr_eq hZ_meas hZ_law α hα
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
  have hB12 : B1 = B2 := by
    dsimp [B1, B2]; congr 2; simp_rw [hint_P_eq]
    exact sum_erase_integral_subgraphCopyIndicator_sup_sub H hp0 hp1 hα hα
  have hVar_P : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      (r : ℝ) * (1 - p ^ e_H +
        ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H)) := by
    let f_count : SimpleGraph (Fin n) → ℝ := fun G₀ ↦ (subgraphCount H n G₀ : ℝ)
    have hf_meas : Measurable f_count := Measurable.of_discrete
    have hVar_map : ProbabilityTheory.variance f_count (P.map G) =
        ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P :=
      ProbabilityTheory.variance_map hf_meas.aemeasurable hG_meas
    rw [← hVar_map, hG_law, variance_subgraphCount_erdosRenyi H hp0 hp1 hα, ← hr_eq]
  have hB23 : 0 < r → B2 = B3 := by
    intro hr
    have hr_pos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
    have hmin_mul : min 1 (r : ℝ)⁻¹ * (r : ℝ) = min 1 (r : ℝ) := by
      rw [min_mul_of_nonneg _ _ hr_pos.le, one_mul, inv_mul_cancel₀ hr_pos.ne', min_comm]
    dsimp [B2, B3]; rw [hVar_P, ← hmin_mul]; ring
  exact ⟨h15, hB12, hB23, hVar_P⟩

/-! ### 2. Example 4.7 (*Triangles*, `SteinIntro.tex:2334-2343`) and Example 4.8 (*$k$-cycles*) -/

/-- **Example 4.7** (*Triangles*, `SteinIntro.tex:2334-2343`, eq. `(4.13)` `\label{124}`). -/
theorem ex4_7_proof :
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {n : ℕ} {p : ℝ} {r : ℝ≥0}
      {G : Ω → SimpleGraph (Fin n)} {Z : Ω' → ℕ},
      3 ≤ n → 0 ≤ p → p ≤ 1 →
      AEMeasurable G P → P.map G = erdosRenyi n p →
      let W : Ω → ℕ := fun ω ↦ ((G ω).cliqueSet 3).ncard
      ((r : ℝ) = (n.choose 3 : ℝ) * p ^ 3) →
      AEMeasurable Z P' → P'.map Z = poissonLaw r →
      (∀ α ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n,
        (subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph 3) n α 1).card = 0 ∧
        (subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph 3) n α 2).card = 3 * (n - 3)) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ) * (p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)))) ∧
    (∀ {p : ℕ → ℝ} {c₁ c₂ : ℝ},
      0 < c₁ → c₁ ≤ c₂ →
      (∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) →
      let lam : ℕ → ℝ := fun n ↦ (n.choose 3 : ℝ) * (p n) ^ 3
      let err : ℕ → ℝ :=
        fun n ↦ min 1 (lam n) * ((p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n))
      ∃ B₁ B₂ : ℝ, 0 < B₁ ∧ 0 < B₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ)) := by
  refine ⟨?_, fun hc₁ hc₁₂ hp ↦ ex4_7_asymptotics hc₁ hc₁₂ hp⟩
  intro Ω Ω' _ _ P _ P' _ n p r G Z hn3 hp0 hp1 hG_meas hG_law W hr_eq hZ_meas hZ_law
  let H := SimpleGraph.cycleGraph 3
  have hdiff_cards : ∀ α ∈ subgraphCopies H n,
      (subgraphCopiesWithDiffEdges H n α 1).card = 0 ∧
      (subgraphCopiesWithDiffEdges H n α 2).card = 3 * (n - 3) :=
    fun α hα ↦ ⟨card_subgraphCopiesWithDiffEdges_cycleGraph_three_one hα,
      card_subgraphCopiesWithDiffEdges_cycleGraph_three_two hα⟩
  refine ⟨hdiff_cards, ?_⟩
  have hV0 : 0 < Fintype.card (Fin 3) := by decide
  have hVn : Fintype.card (Fin 3) ≤ n := by simpa using hn3
  obtain ⟨α₀, hα₀⟩ := subgraphCopies_nonempty H hVn
  have hr_eq' : (r : ℝ) = ((subgraphCopies H n).card : ℝ) * p ^ H.edgeSet.ncard := by
    rw [card_subgraphCopies_cycleGraph_three, ncard_edgeSet_cycleGraph_three, hr_eq]
  have hcor := cor4_16_proof P P' H hV0 hVn not_isIsolated_cycleGraph_three hp0 hp1
    hG_meas hG_law hr_eq' hZ_meas hZ_law α₀ hα₀
  have hW_eq : W = fun ω ↦ subgraphCount H n (G ω) :=
    funext fun ω ↦ (subgraphCount_cycleGraph_three_eq_ncard_cliqueSet (G ω)).symm
  rw [hW_eq]
  refine (hcor.1.trans_eq (by rw [hcor.2.1])).trans (le_of_eq ?_)
  congr 1; congr 1
  have he3 : H.edgeSet.ncard = 3 := ncard_edgeSet_cycleGraph_three
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  rw [he3, hIco, Finset.sum_pair (by decide),
    (hdiff_cards α₀ hα₀).1, (hdiff_cards α₀ hα₀).2,
    Nat.cast_zero, zero_mul, zero_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn3]
  ring

/-- **Example 4.8** (*$k$-cycles*, `SteinIntro.tex:2344-2366`, eq. `(4.14)` `\label{125}`;
`ISSUE-TYPO-4.8` and Critic G2-3 `(np)^k` order comparison). -/
theorem ex4_8_proof :
    ∀ {k : ℕ}, 3 ≤ k →
      ∃ (c : ℕ → ℝ) (C_k : ℝ),
        (∀ t ∈ Finset.Ico 1 k, 0 < c t) ∧
        0 < C_k ∧
        (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
          (P : Measure Ω) [IsProbabilityMeasure P]
          (P' : Measure Ω') [IsProbabilityMeasure P']
          {n : ℕ} {p : ℝ} {r : ℝ≥0}
          {G : Ω → SimpleGraph (Fin n)} {Z : Ω' → ℕ},
          k ≤ n → 0 ≤ p → p ≤ 1 →
          AEMeasurable G P → P.map G = erdosRenyi n p →
          let H : SimpleGraph (Fin k) := SimpleGraph.cycleGraph k
          let Γ : Finset (SimpleGraph (Fin n)) := subgraphCopies H n
          let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
          ((r : ℝ) = (Γ.card : ℝ) * p ^ k) →
          AEMeasurable Z P' → P'.map Z = poissonLaw r →
          (Γ.card : ℝ) = (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 ∧
          (r : ℝ) = (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * p ^ k ∧
          (2 * k ≤ n →
            ((n : ℝ) * p) ^ k / (2 * (k : ℝ) * 2 ^ k) ≤ (r : ℝ) ∧
              (r : ℝ) ≤ ((n : ℝ) * p) ^ k / (2 * (k : ℝ))) ∧
          ∀ α ∈ Γ,
            let Γ_t : ℕ → Finset (SimpleGraph (Fin n)) := subgraphCopiesWithDiffEdges H n α
            (∀ t ∈ Finset.Ico 1 k,
              ((Γ_t t).card : ℝ) ≤ (k.choose (k - t) : ℝ) * c t * (n : ℝ) ^ (t - 1) ∧
              (k.choose (k - t) : ℝ) * c t * (n : ℝ) ^ (t - 1) ≤
                C_k * (n : ℝ) ^ (t - 1)) ∧
            tvDist (P.map W) (P'.map Z) ≤
              ENNReal.ofReal
                (min 1 (r : ℝ) *
                  (p ^ k +
                    ∑ t ∈ Finset.Ico 1 k, ((Γ_t t).card : ℝ) * (p ^ t - p ^ k))) ∧
            min 1 (r : ℝ) *
                (p ^ k + ∑ t ∈ Finset.Ico 1 k, ((Γ_t t).card : ℝ) * (p ^ t - p ^ k)) ≤
              min 1 (r : ℝ) *
                (p ^ k + C_k * p * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p) ^ (t - 1))) ∧
        (∀ {p : ℕ → ℝ} {c₁ c₂ : ℝ},
          0 < c₁ → c₁ ≤ c₂ →
          (∀ᶠ n : ℕ in Filter.atTop,
            0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) →
          let lam : ℕ → ℝ :=
            fun n ↦ (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * (p n) ^ k
          let err : ℕ → ℝ :=
            fun n ↦ min 1 (lam n) *
              ((p n) ^ k + C_k * p n * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1))
          ∃ L₁ L₂ B₁ B₂ : ℝ, 0 < L₁ ∧ 0 < L₂ ∧ 0 < B₁ ∧ 0 < B₂ ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              (L₁ ≤ lam n ∧ lam n ≤ L₂) ∧
                (B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ))) := by
  intro k hk
  refine ⟨c_cycle k, C_cycle k, fun t _ ↦ c_cycle_pos k t, C_cycle_pos k, ?_,
    fun hc₁ hc₁₂ hp ↦ ex4_8_asymptotics hk (C_cycle_pos k) hc₁ hc₁₂ hp⟩
  intro Ω Ω' _ _ P _ P' _ n p r G Z hkn hp0 hp1 hG_meas hG_law H Γ W hr_eq hZ_meas hZ_law
  have hΓ_card : (Γ.card : ℝ) = (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 :=
    card_subgraphCopies_cycleGraph_cast hk
  have hr_lam : (r : ℝ) = (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * p ^ k := by
    rw [hr_eq, hΓ_card]
  have hlam_ord : 2 * k ≤ n →
      ((n : ℝ) * p) ^ k / (2 * (k : ℝ) * 2 ^ k) ≤ (r : ℝ) ∧
        (r : ℝ) ≤ ((n : ℝ) * p) ^ k / (2 * (k : ℝ)) := by
    intro hn2k; rw [hr_lam]; exact lam_cycleGraph_bounds hk hn2k hp0
  refine ⟨hΓ_card, hr_lam, hlam_ord, ?_⟩
  intro α hα Γ_t
  have hdiff_le : ∀ t ∈ Finset.Ico 1 k,
      ((Γ_t t).card : ℝ) ≤ (k.choose (k - t) : ℝ) * c_cycle k t * (n : ℝ) ^ (t - 1) ∧
      (k.choose (k - t) : ℝ) * c_cycle k t * (n : ℝ) ^ (t - 1) ≤
        C_cycle k * (n : ℝ) ^ (t - 1) :=
    fun t ht ↦ card_subgraphCopiesWithDiffEdges_cycleGraph_le hk hkn hα ht
  have hV0 : 0 < Fintype.card (Fin k) := by rw [Fintype.card_fin]; omega
  have hVn : Fintype.card (Fin k) ≤ n := by simpa using hkn
  have he_k : H.edgeSet.ncard = k := ncard_edgeSet_cycleGraph hk
  have hr_eq' : (r : ℝ) = (Γ.card : ℝ) * p ^ H.edgeSet.ncard := by rw [he_k, hr_eq]
  have hcor := cor4_16_proof P P' H hV0 hVn (not_isIsolated_cycleGraph hk) hp0 hp1
    hG_meas hG_law hr_eq' hZ_meas hZ_law α hα
  have htv : tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (p ^ k + ∑ t ∈ Finset.Ico 1 k, ((Γ_t t).card : ℝ) * (p ^ t - p ^ k))) := by
    exact hcor.1.trans_eq (by rw [hcor.2.1]; dsimp [Γ_t]; rw [he_k])
  have hbound_le :
      min 1 (r : ℝ) *
          (p ^ k + ∑ t ∈ Finset.Ico 1 k, ((Γ_t t).card : ℝ) * (p ^ t - p ^ k)) ≤
        min 1 (r : ℝ) *
          (p ^ k + C_cycle k * p * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p) ^ (t - 1)) := by
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_)
      (le_min zero_le_one (NNReal.coe_nonneg r))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht ↦ ?_
    rcases Finset.mem_Ico.mp ht with ⟨ht1, _⟩
    have hΓt_le : ((Γ_t t).card : ℝ) ≤ C_cycle k * (n : ℝ) ^ (t - 1) :=
      (hdiff_le t ht).1.trans (hdiff_le t ht).2
    have hpt_sub : p ^ t - p ^ k ≤ p ^ t := sub_le_self _ (pow_nonneg hp0 k)
    have hpt_split : p ^ t = p * p ^ (t - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel ht1, pow_succ']
    calc
      ((Γ_t t).card : ℝ) * (p ^ t - p ^ k)
        ≤ ((Γ_t t).card : ℝ) * p ^ t :=
          mul_le_mul_of_nonneg_left hpt_sub (Nat.cast_nonneg _)
      _ ≤ (C_cycle k * (n : ℝ) ^ (t - 1)) * p ^ t :=
          mul_le_mul_of_nonneg_right hΓt_le (pow_nonneg hp0 t)
      _ = C_cycle k * p * ((n : ℝ) * p) ^ (t - 1) := by rw [hpt_split, mul_pow]; ring
  exact ⟨hdiff_le, htv, hbound_le⟩

/-! ### 3. Variance-form Theorem 4.14 and statement-matching wrappers (`docs/tracks/G2.md`) -/

/-- **Theorem 4.14** (`\label{thm122}`, `SteinIntro.tex:2253-2277`), in the variance form matching
`Thm4_14` in `docs/tracks/G2.md`. -/
theorem thm4_14_variance_proof
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℕ)}
    {I : Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℕ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n, 0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ω ∂P, X j.1 ω ≤ Y i ω j) →
    AEMeasurable Z P' → P'.map Z = poissonLaw r →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P (fun ω ↦ (Ws ω : ℝ)) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ)⁻¹ *
            (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
              2 * ∑ i : Fin n, p i ^ 2)) := by
  intro p W Ws hr_eq hY_meas hY_law hI_meas hI_prob hI_indep hmono hZ_meas hZ_law
  have hr : 0 < r := by
    by_contra! hle
    have hr0 : r = 0 := le_bot_iff.mp hle
    have hnull : ∀ i : Fin n, P (I ⁻¹' {i}) = 0 := fun i ↦ by
      apply (measureReal_eq_zero_iff).mp
      rw [hI_prob i, hr0, NNReal.coe_zero, div_zero]
    have huniv : (Set.univ : Set Ω) = ⋃ i : Fin n, I ⁻¹' {i} := by ext ω; simp
    have h1 : P Set.univ = 0 := by rw [huniv]; exact measure_iUnion_null hnull
    rw [measure_univ] at h1
    exact one_ne_zero h1
  have hr_pos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have h14 := thm4_14_proof P P' hX_meas hX_zo hr hr_eq.symm hY_meas hY_law hmono
    hI_meas hI_prob hI_indep hZ_meas hZ_law
  refine ⟨h14.1, h14.2.trans (le_of_eq ?_)⟩
  congr 1
  have hset_meas : ∀ i : Fin n, MeasurableSet {ω | X i ω = 1} :=
    fun i ↦ hX_meas i (measurableSet_singleton 1)
  have hX_ae_ind : ∀ i : Fin n,
      (fun ω ↦ (X i ω : ℝ)) =ᵐ[P]
        ({ω | X i ω = 1} : Set Ω).indicator (fun _ ↦ (1 : ℝ)) := by
    intro i
    refine (hX_zo i).mono fun ω hω ↦ ?_
    rcases hω with h0 | h1
    · simp [h0]
    · simp [h1]
  have hX_int : ∀ i : Fin n, Integrable (fun ω ↦ (X i ω : ℝ)) P := fun i ↦
    ((integrable_const (1 : ℝ)).indicator (hset_meas i)).congr (hX_ae_ind i).symm
  have hX_mean : ∀ i : Fin n, ∫ ω, (X i ω : ℝ) ∂P = p i := fun i ↦ by
    rw [integral_congr_ae (hX_ae_ind i),
      integral_indicator (hset_meas i), setIntegral_one_eq_measureReal]
  have hW_rcast_meas : Measurable (fun ω ↦ (W ω : ℝ)) :=
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp
      (Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas i)
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) := by
    have hfun : (fun ω ↦ (W ω : ℝ)) = fun ω ↦ ∑ i : Fin n, (X i ω : ℝ) := by
      ext ω; simp [W, Nat.cast_sum]
    rw [hfun, integral_finsetSum Finset.univ fun i _ ↦ hX_int i,
      Finset.sum_congr rfl fun i _ ↦ hX_mean i, hr_eq]
  have hW_le : ∀ᵐ ω ∂P, (W ω : ℝ) ≤ (n : ℝ) := by
    have hall : ∀ᵐ ω ∂P, ∀ i : Fin n, X i ω ≤ 1 :=
      eventually_all.mpr fun i ↦ (hX_zo i).mono fun ω hω ↦ by rcases hω with h | h <;> omega
    refine hall.mono fun ω hω ↦ ?_
    have hle : W ω ≤ n := by
      calc
        W ω = ∑ i : Fin n, X i ω := rfl
        _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ ↦ hω i
        _ = n := by simp
    exact_mod_cast hle
  have hW2_int : Integrable (fun ω ↦ (W ω : ℝ) * (W ω : ℝ)) P := by
    refine (integrable_const ((n : ℝ) * (n : ℝ))).mono'
      (hW_rcast_meas.mul hW_rcast_meas).aestronglyMeasurable ?_
    refine hW_le.mono fun ω hω ↦ ?_
    have hnn : 0 ≤ (W ω : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hnn hnn)]
    exact mul_le_mul hω hω hnn (Nat.cast_nonneg n)
  have hY_le_one : ∀ i : Fin n, 0 < p i →
      ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ω ∂P, Y i ω j ≤ 1 := by
    intro i hpi j
    have hX_le : ∀ᵐ ω ∂P, X j.1 ω ≤ 1 :=
      (hX_zo j.1).mono fun ω hω ↦ by rcases hω with h | h <;> omega
    have hcond_le : ∀ᵐ ω ∂(ProbabilityTheory.cond P {ω | X i ω = 1}), X j.1 ω ≤ 1 :=
      ProbabilityTheory.cond_absolutelyContinuous.ae_le hX_le
    let rest : Ω → ({k : Fin n // k ≠ i} → ℕ) := fun ω k ↦ X k.1 ω
    have hrest_meas : Measurable rest := Measurable.of_eval fun k ↦ hX_meas k.1
    let S : Set ({k : Fin n // k ≠ i} → ℕ) := {u | u j ≤ 1}
    have hS_meas : MeasurableSet S := MeasurableSet.of_discrete
    have hmap_cond : ∀ᵐ u ∂((ProbabilityTheory.cond P {ω | X i ω = 1}).map rest), u ∈ S :=
      (ae_map_iff hrest_meas.aemeasurable hS_meas).mpr hcond_le
    rw [← hY_law i hpi] at hmap_cond
    exact (ae_map_iff (hY_meas i) hS_meas).mp hmap_cond
  have hY_int : ∀ i : Fin n, 0 < p i → ∀ j : {j : Fin n // j ≠ i},
      Integrable (fun ω ↦ (Y i ω j : ℝ)) P := by
    intro i hpi j
    let proj : ({k : Fin n // k ≠ i} → ℕ) → ℝ := fun u ↦ (u j : ℝ)
    have hproj : Measurable proj :=
      (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply j)
    have hm : AEMeasurable (fun ω ↦ (Y i ω j : ℝ)) P := hproj.comp_aemeasurable (hY_meas i)
    refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
    refine (hY_le_one i hpi j).mono fun ω hω ↦ ?_
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hω
  let V_all : Ω → (Fin n → ℕ) × ((i : Fin n) → {j : Fin n // j ≠ i} → ℕ) :=
    fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)
  have hV_meas : AEMeasurable V_all P :=
    (Measurable.of_eval hX_meas).aemeasurable.prodMk (AEMeasurable.of_eval hY_meas)
  let g_Ws : Fin n →
      ((Fin n → ℕ) × ((i : Fin n) → {j : Fin n // j ≠ i} → ℕ)) → ℝ :=
    fun i v ↦ (∑ j : {j : Fin n // j ≠ i}, (v.2 i j : ℝ)) + 1
  have hg_Ws_meas : ∀ i : Fin n, Measurable (g_Ws i) := fun _ ↦ Measurable.of_discrete
  let termWs : Fin n → Ω → ℝ :=
    fun i ↦ (I ⁻¹' {i}).indicator (fun ω ↦ g_Ws i (V_all ω))
  have htermWs_int_eq : ∀ i : Fin n,
      Integrable (termWs i) P ∧
        ∫ ω, termWs i ω ∂P =
          (p i / (r : ℝ)) *
            ((∑ j : {j : Fin n // j ≠ i}, ∫ ω, (Y i ω j : ℝ) ∂P) + 1) := by
    intro i
    have hpi_nn : 0 ≤ p i := measureReal_nonneg
    rcases hpi_nn.eq_or_lt with hpi0 | hpi_pos
    · have hPI_real0 : P.real (I ⁻¹' {i}) = 0 := by rw [hI_prob i, ← hpi0, zero_div]
      have hPI0 : P (I ⁻¹' {i}) = 0 := (measureReal_eq_zero_iff).mp hPI_real0
      have hterm_ae0 : termWs i =ᵐ[P] 0 :=
        (measure_eq_zero_iff_ae_notMem.mp hPI0).mono fun ω hω ↦
          Set.indicator_of_notMem hω _
      refine ⟨(integrable_zero Ω ℝ P).congr hterm_ae0.symm, ?_⟩
      rw [integral_eq_zero_of_ae hterm_ae0, ← hpi0, zero_div, zero_mul]
    · have hIi_meas : MeasurableSet (I ⁻¹' {i}) := hI_meas (measurableSet_singleton i)
      have hg_int : Integrable (fun ω ↦ g_Ws i (V_all ω)) P :=
        (integrable_finsetSum Finset.univ fun j _ ↦ hY_int i hpi_pos j).add (integrable_const 1)
      refine ⟨hg_int.indicator hIi_meas, ?_⟩
      let fI : Fin n → ℝ := ({i} : Set (Fin n)).indicator (fun _ ↦ (1 : ℝ))
      have hfI_meas : Measurable fI := measurable_const.indicator (measurableSet_singleton i)
      have hpt : termWs i = fun ω ↦ fI (I ω) * g_Ws i (V_all ω) := by
        ext ω; by_cases hω : I ω = i <;> simp [termWs, fI, hω]
      have hfI_comp : (fun ω ↦ fI (I ω)) = (I ⁻¹' {i}).indicator (fun _ ↦ (1 : ℝ)) := by
        ext ω; by_cases hω : I ω = i <;> simp [fI, hω]
      have hint_prod :
          ∫ ω, termWs i ω ∂P = (p i / (r : ℝ)) * ∫ ω, g_Ws i (V_all ω) ∂P := by
        rw [hpt,
          hI_indep.integral_fun_comp_mul_comp hI_meas.aemeasurable hV_meas
            hfI_meas.stronglyMeasurable.aestronglyMeasurable
            (hg_Ws_meas i).stronglyMeasurable.aestronglyMeasurable,
          hfI_comp, integral_indicator hIi_meas, setIntegral_one_eq_measureReal, hI_prob i]
      rw [hint_prod]; congr 1; dsimp [g_Ws, V_all]
      rw [integral_add (integrable_finsetSum Finset.univ fun j _ ↦ hY_int i hpi_pos j)
        (integrable_const 1),
        integral_finsetSum Finset.univ fun j _ ↦ hY_int i hpi_pos j,
        integral_const, probReal_univ, one_smul]
  have hWs_sum_term : (fun ω ↦ (Ws ω : ℝ)) = fun ω ↦ ∑ i : Fin n, termWs i ω := by
    ext ω; symm
    rw [Finset.sum_eq_single (I ω)]
    · simp [termWs, g_Ws, V_all, Ws, Nat.cast_add, Nat.cast_sum]
    · intro i _ hi; exact Set.indicator_of_notMem (by simpa using hi.symm) _
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hWs_int_eq : ∫ ω, (Ws ω : ℝ) ∂P =
      ∑ i : Fin n, (p i / (r : ℝ)) *
        ((∑ j : {j : Fin n // j ≠ i}, ∫ ω, (Y i ω j : ℝ) ∂P) + 1) := by
    rw [hWs_sum_term, integral_finsetSum Finset.univ fun i _ ↦ (htermWs_int_eq i).1,
      Finset.sum_congr rfl fun i _ ↦ (htermWs_int_eq i).2]
  have hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P := h14.1.2.1
  have hSB_id :
      ∫ ω, (W ω : ℝ) * (W ω : ℝ) ∂P =
        (∫ ω, (W ω : ℝ) ∂P) * ∫ ω, (Ws ω : ℝ) ∂P :=
    h14.1.2.2.2 id measurable_id hW2_int
  have hVar_eq : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      (r : ℝ) * (∫ ω, (Ws ω : ℝ) ∂P) - (r : ℝ) ^ 2 := by
    rw [ProbabilityTheory.variance_eq_integral hW_rcast_meas.aemeasurable, hW_mean]
    have hsq_exp : (fun ω ↦ ((W ω : ℝ) - (r : ℝ)) ^ 2) =
        fun ω ↦
          ((W ω : ℝ) * (W ω : ℝ) - 2 * (r : ℝ) * (W ω : ℝ)) + (r : ℝ) ^ 2 := by
      ext ω; ring
    have hmul_int : Integrable (fun ω ↦ 2 * (r : ℝ) * (W ω : ℝ)) P :=
      hW_int.const_mul (2 * (r : ℝ))
    have hsub_int :
        Integrable (fun ω ↦ (W ω : ℝ) * (W ω : ℝ) - 2 * (r : ℝ) * (W ω : ℝ)) P :=
      hW2_int.sub hmul_int
    rw [hsq_exp, integral_add hsub_int (integrable_const ((r : ℝ) ^ 2)),
      integral_sub hW2_int hmul_int, integral_const_mul, integral_const, probReal_univ,
      one_smul, hSB_id, hW_mean]
    ring
  have hterm_diff : ∀ i : Fin n,
      (p i / (r : ℝ)) *
        (p i + ∑ j : {j : Fin n // j ≠ i}, ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P) =
      (p i / (r : ℝ)) * ((∑ j : {j : Fin n // j ≠ i}, ∫ ω, (Y i ω j : ℝ) ∂P) + 1) -
        (p i / (r : ℝ)) * ((r : ℝ) + 1) + 2 * (p i ^ 2 / (r : ℝ)) := by
    intro i
    have hpi_nn : 0 ≤ p i := measureReal_nonneg
    rcases hpi_nn.eq_or_lt with hpi0 | hpi_pos
    · rw [← hpi0]; ring
    · have hsub_sum :
          (∑ j : {j : Fin n // j ≠ i},
              ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P) =
            (∑ j : {j : Fin n // j ≠ i}, ∫ ω, (Y i ω j : ℝ) ∂P) -
              ((r : ℝ) - p i) := by
        have h1 :
            (∑ j : {j : Fin n // j ≠ i},
                ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P) =
              (∑ j : {j : Fin n // j ≠ i}, ∫ ω, (Y i ω j : ℝ) ∂P) -
                ∑ j : {j : Fin n // j ≠ i}, p j.1 := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [integral_sub (hY_int i hpi_pos j) (hX_int j.1), hX_mean j.1]
        have h2 : (r : ℝ) = p i + ∑ j : {j : Fin n // j ≠ i}, p j.1 := by
          rw [hr_eq]; exact sum_fintype_eq_add_sum_subtype_ne i p
        linarith
      rw [hsub_sum]; ring
  have hsum_pi_div : (∑ i : Fin n, p i / (r : ℝ)) = 1 := by
    rw [← Finset.sum_div, ← hr_eq, div_self hr_pos.ne']
  have hsum_D :
      (∑ i : Fin n, (p i / (r : ℝ)) *
        (p i +
          ∑ j : {j : Fin n // j ≠ i}, ∫ ω, ((Y i ω j : ℝ) - (X j.1 ω : ℝ)) ∂P)) =
      (∫ ω, (Ws ω : ℝ) ∂P) - ((r : ℝ) + 1) +
        (2 / (r : ℝ)) * ∑ i : Fin n, p i ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ ↦ hterm_diff i,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← hWs_int_eq,
      ← Finset.sum_mul, hsum_pi_div, one_mul]
    congr 1; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hmin_eq : min 1 (r : ℝ) = min 1 (r : ℝ)⁻¹ * (r : ℝ) := by
    rw [min_mul_of_nonneg _ _ hr_pos.le, one_mul, inv_mul_cancel₀ hr_pos.ne', min_comm]
  rw [hsum_D, hmin_eq, mul_assoc]
  congr 1; rw [hVar_eq]
  have hr_ne : (r : ℝ) ≠ 0 := hr_pos.ne'
  field_simp [hr_ne]; ring

/-- **Theorem 4.15** (`\label{thm123}`, `SteinIntro.tex:2289-2295`), in the variance form matching
`Thm4_15` in `docs/tracks/G2.md`. -/
theorem thm4_15_variance_proof
    {V : Type*} [Fintype V] (H : SimpleGraph V)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hV0 : 0 < Fintype.card V) (hVn : Fintype.card V ≤ n)
    (hiso : ∀ v : V, ¬ H.IsIsolated v)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hG_meas : AEMeasurable G P) (hG_law : P.map G = erdosRenyi n p) :
    let e_H : ℕ := H.edgeSet.ncard
    let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' → P'.map Z = poissonLaw r →
    ∫ ω, (W ω : ℝ) ∂P = ((subgraphCopies H n).card : ℝ) * p ^ e_H ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ)⁻¹ *
            (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
              2 * (r : ℝ) * p ^ e_H)) := by
  intro e_H W hr_mean hZ_meas hZ_law
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = ((subgraphCopies H n).card : ℝ) * p ^ e_H := by
    let f_count : SimpleGraph (Fin n) → ℝ := fun G₀ ↦ (subgraphCount H n G₀ : ℝ)
    have hf_meas : Measurable f_count := Measurable.of_discrete
    have hmap : ∫ G₀, f_count G₀ ∂(P.map G) = ∫ ω, (W ω : ℝ) ∂P :=
      integral_map hG_meas hf_meas.stronglyMeasurable.aestronglyMeasurable
    rw [← hmap, hG_law, integral_subgraphCount H hp0 hp1]
  have hr_eq : (r : ℝ) = ((subgraphCopies H n).card : ℝ) * p ^ e_H := hr_mean.trans hW_mean
  refine ⟨hW_mean, ?_⟩
  obtain ⟨α₀, hα₀⟩ := subgraphCopies_nonempty H hVn
  have hcor :=
    cor4_16_proof P P' H hV0 hVn hiso hp0 hp1 hG_meas hG_law hr_eq hZ_meas hZ_law α₀ hα₀
  rcases eq_or_ne r 0 with rfl | hr_ne
  · exact (by simpa using hcor.1 : tvDist (P.map W) (P'.map Z) ≤ 0).trans zero_le
  · exact hcor.1.trans_eq (by rw [hcor.2.1, hcor.2.2.1 (pos_iff_ne_zero.mpr hr_ne)])

/-- **Corollary 4.16** (`\label{cor123}`, `SteinIntro.tex:2313-2331`), matching `Cor4_16` in
`docs/tracks/G2.md`. -/
theorem cor4_16_holds_proof
    {V : Type*} [Fintype V] (H : SimpleGraph V)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {α : SimpleGraph (Fin n)}
    {r : ℝ≥0} {Z : Ω' → ℕ}
    (hV0 : 0 < Fintype.card V) (hVn : Fintype.card V ≤ n)
    (hiso : ∀ v : V, ¬ H.IsIsolated v)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hα : α ∈ subgraphCopies H n)
    (hG_meas : AEMeasurable G P) (hG_law : P.map G = erdosRenyi n p) :
    let e_H : ℕ := H.edgeSet.ncard
    let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
    let Γ_t : ℕ → Finset (SimpleGraph (Fin n)) := subgraphCopiesWithDiffEdges H n α
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' → P'.map Z = poissonLaw r →
    ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
        (r : ℝ) * (1 - p ^ e_H +
          ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H)) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ) *
            (p ^ e_H + ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H))) := by
  intro e_H W Γ_t hr_mean hZ_meas hZ_law
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = ((subgraphCopies H n).card : ℝ) * p ^ e_H := by
    let f_count : SimpleGraph (Fin n) → ℝ := fun G₀ ↦ (subgraphCount H n G₀ : ℝ)
    have hf_meas : Measurable f_count := Measurable.of_discrete
    have hmap : ∫ G₀, f_count G₀ ∂(P.map G) = ∫ ω, (W ω : ℝ) ∂P :=
      integral_map hG_meas hf_meas.stronglyMeasurable.aestronglyMeasurable
    rw [← hmap, hG_law, integral_subgraphCount H hp0 hp1]
  have hr_eq : (r : ℝ) = ((subgraphCopies H n).card : ℝ) * p ^ e_H := hr_mean.trans hW_mean
  have hcor := cor4_16_proof P P' H hV0 hVn hiso hp0 hp1 hG_meas hG_law hr_eq hZ_meas hZ_law α hα
  exact ⟨hcor.2.2.2, hcor.1.trans_eq (by rw [hcor.2.1])⟩

/-- **Example 4.7** (`SteinIntro.tex:2334-2343`, eq. `(4.13)` `\label{124}`), matching `Ex4_7` in
`docs/tracks/G2.md`. -/
theorem ex4_7_holds_proof :
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {α : SimpleGraph (Fin n)}
        {r : ℝ≥0} {Z : Ω' → ℕ},
        3 ≤ n → 0 ≤ p → p ≤ 1 →
        α ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n →
        AEMeasurable G P → P.map G = erdosRenyi n p →
        let H := SimpleGraph.cycleGraph 3
        let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
        (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
        AEMeasurable Z P' → P'.map Z = poissonLaw r →
        H.edgeSet.ncard = 3 ∧
          (subgraphCopies H n).card = n.choose 3 ∧
          (subgraphCopiesWithDiffEdges H n α 1).card = 0 ∧
          (subgraphCopiesWithDiffEdges H n α 2).card = 3 * (n - 3) ∧
          (∀ H₀ : SimpleGraph (Fin n), subgraphCount H n H₀ = (H₀.cliqueSet 3).ncard) ∧
          ∫ ω, (W ω : ℝ) ∂P = (n.choose 3 : ℝ) * p ^ 3 ∧
          ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
            (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) ∧
          tvDist (P.map W) (P'.map Z) ≤
            ENNReal.ofReal (min 1 (r : ℝ) * (p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)))) ∧
    (∀ {p : ℕ → ℝ} {c₁ c₂ : ℝ},
        0 < c₁ → c₁ ≤ c₂ →
        (∀ᶠ n : ℕ in Filter.atTop,
          0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) →
        let lam : ℕ → ℝ := fun n ↦ (n.choose 3 : ℝ) * (p n) ^ 3
        let err : ℕ → ℝ :=
          fun n ↦ min 1 (lam n) * ((p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n))
        ∃ B₁ B₂ : ℝ, 0 < B₁ ∧ 0 < B₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
          B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ)) := by
  refine ⟨?_, fun hc₁ hc₁₂ hp ↦ ex4_7_asymptotics hc₁ hc₁₂ hp⟩
  intro Ω Ω' _ _ P _ P' _ n p G α r Z hn3 hp0 hp1 hα hG_meas hG_law H W hr_mean hZ_meas hZ_law
  have he3 : H.edgeSet.ncard = 3 := ncard_edgeSet_cycleGraph_three
  have hΓ3 : (subgraphCopies H n).card = n.choose 3 := card_subgraphCopies_cycleGraph_three n
  have hdiff1 : (subgraphCopiesWithDiffEdges H n α 1).card = 0 :=
    card_subgraphCopiesWithDiffEdges_cycleGraph_three_one hα
  have hdiff2 : (subgraphCopiesWithDiffEdges H n α 2).card = 3 * (n - 3) :=
    card_subgraphCopiesWithDiffEdges_cycleGraph_three_two hα
  have hclique : ∀ H₀ : SimpleGraph (Fin n),
      subgraphCount H n H₀ = (H₀.cliqueSet 3).ncard :=
    subgraphCount_cycleGraph_three_eq_ncard_cliqueSet
  have hV0 : 0 < Fintype.card (Fin 3) := by decide
  have hVn : Fintype.card (Fin 3) ≤ n := by simpa using hn3
  have h15 := thm4_15_variance_proof H P P' hV0 hVn not_isIsolated_cycleGraph_three hp0 hp1
    hG_meas hG_law hr_mean hZ_meas hZ_law
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = (n.choose 3 : ℝ) * p ^ 3 := by
    have h := h15.1; rw [hΓ3, he3] at h; exact h
  have hcor := cor4_16_holds_proof H P P' hV0 hVn not_isIsolated_cycleGraph_three hp0 hp1 hα
    hG_meas hG_law hr_mean hZ_meas hZ_law
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  have hsum_eq :
      ∑ t ∈ Finset.Ico 1 H.edgeSet.ncard,
          ((subgraphCopiesWithDiffEdges H n α t).card : ℝ) * (p ^ t - p ^ H.edgeSet.ncard) =
        3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p) := by
    rw [he3, hIco, Finset.sum_pair (by decide), hdiff1, hdiff2,
      Nat.cast_zero, zero_mul, zero_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn3]
    ring
  have hVar : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) := by
    have hv := hcor.1; rw [hv, hr_mean, hW_mean, hsum_eq, he3]
  have htv : tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (min 1 (r : ℝ) * (p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p))) := by
    have ht := hcor.2; rwa [hsum_eq, he3] at ht
  exact ⟨he3, hΓ3, hdiff1, hdiff2, hclique, hW_mean, hVar, htv⟩

/-- **Example 4.8** (`SteinIntro.tex:2344-2366`, eq. `(4.14)` `\label{125}`; `ISSUE-TYPO-4.8` and
Critic G2-3), matching `Ex4_8` in `docs/tracks/G2.md`. -/
theorem ex4_8_holds_proof :
    ∀ {k : ℕ}, 3 ≤ k →
      ∃ (c : ℕ → ℝ) (C_k : ℝ), (∀ t, 0 < c t) ∧ 0 < C_k ∧
        (∀ {n : ℕ} {α : SimpleGraph (Fin n)},
          k ≤ n → α ∈ subgraphCopies (SimpleGraph.cycleGraph k) n →
          ∀ t ∈ Finset.Ico 1 k,
            ((subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph k) n α t).card : ℝ) ≤
                (k.choose (k - t) : ℝ) * c t * (n : ℝ) ^ (t - 1) ∧
              (k.choose (k - t) : ℝ) * c t * (n : ℝ) ^ (t - 1) ≤
                C_k * (n : ℝ) ^ (t - 1)) ∧
        (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
          (P : Measure Ω) [IsProbabilityMeasure P]
          (P' : Measure Ω') [IsProbabilityMeasure P']
          {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ},
          k ≤ n → 0 ≤ p → p ≤ 1 →
          AEMeasurable G P → P.map G = erdosRenyi n p →
          let H := SimpleGraph.cycleGraph k
          let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
          (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
          AEMeasurable Z P' → P'.map Z = poissonLaw r →
          (subgraphCopies H n).card = n.choose k * (k - 1).factorial / 2 ∧
            ∫ ω, (W ω : ℝ) ∂P =
              (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * p ^ k ∧
            (2 * k ≤ n →
              ((n : ℝ) * p) ^ k / (2 * (k : ℝ) * 2 ^ k) ≤ (r : ℝ) ∧
                (r : ℝ) ≤ ((n : ℝ) * p) ^ k / (2 * (k : ℝ))) ∧
            tvDist (P.map W) (P'.map Z) ≤
              ENNReal.ofReal
                (min 1 (r : ℝ) *
                  (p ^ k + C_k * p * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p) ^ (t - 1)))) ∧
        (∀ {p : ℕ → ℝ} {c₁ c₂ : ℝ},
          0 < c₁ → c₁ ≤ c₂ →
          (∀ᶠ n : ℕ in Filter.atTop,
            0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) →
          let lam : ℕ → ℝ :=
            fun n ↦ (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * (p n) ^ k
          let err : ℕ → ℝ :=
            fun n ↦ min 1 (lam n) *
              ((p n) ^ k + C_k * p n * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1))
          ∃ L₁ L₂ B₁ B₂ : ℝ, 0 < L₁ ∧ 0 < L₂ ∧ 0 < B₁ ∧ 0 < B₂ ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              (L₁ ≤ lam n ∧ lam n ≤ L₂) ∧
                (B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ))) := by
  intro k hk
  refine ⟨c_cycle k, C_cycle k, c_cycle_pos k, C_cycle_pos k,
    fun hkn hα t ht ↦ card_subgraphCopiesWithDiffEdges_cycleGraph_le hk hkn hα ht, ?_,
    fun hc₁ hc₁₂ hp ↦ ex4_8_asymptotics hk (C_cycle_pos k) hc₁ hc₁₂ hp⟩
  intro Ω Ω' _ _ P _ P' _ n p G r Z hkn hp0 hp1 hG_meas hG_law H W hr_mean hZ_meas hZ_law
  have hΓ_nat : (subgraphCopies H n).card = n.choose k * (k - 1).factorial / 2 :=
    card_subgraphCopies_cycleGraph hk
  have hΓ_cast : ((subgraphCopies H n).card : ℝ) =
      (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 :=
    card_subgraphCopies_cycleGraph_cast hk
  have he_k : H.edgeSet.ncard = k := ncard_edgeSet_cycleGraph hk
  have hV0 : 0 < Fintype.card (Fin k) := by rw [Fintype.card_fin]; omega
  have hVn : Fintype.card (Fin k) ≤ n := by simpa using hkn
  have h15 := thm4_15_variance_proof H P P' hV0 hVn (not_isIsolated_cycleGraph hk) hp0 hp1
    hG_meas hG_law hr_mean hZ_meas hZ_law
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P =
      (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * p ^ k := by
    have h := h15.1; rw [hΓ_cast, he_k] at h; exact h
  have hlam_ord : 2 * k ≤ n →
      ((n : ℝ) * p) ^ k / (2 * (k : ℝ) * 2 ^ k) ≤ (r : ℝ) ∧
        (r : ℝ) ≤ ((n : ℝ) * p) ^ k / (2 * (k : ℝ)) := by
    intro hn2k; rw [hr_mean, hW_mean]; exact lam_cycleGraph_bounds hk hn2k hp0
  obtain ⟨α₀, hα₀⟩ := subgraphCopies_nonempty H hVn
  have hcor := cor4_16_holds_proof H P P' hV0 hVn (not_isIsolated_cycleGraph hk) hp0 hp1 hα₀
    hG_meas hG_law hr_mean hZ_meas hZ_law
  have htv : tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (p ^ k + C_cycle k * p * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p) ^ (t - 1))) := by
    have h1 := hcor.2
    rw [he_k] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_)
      (le_min zero_le_one (NNReal.coe_nonneg r))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht ↦ ?_
    rcases Finset.mem_Ico.mp ht with ⟨ht1, _⟩
    have hdiff_t := card_subgraphCopiesWithDiffEdges_cycleGraph_le hk hkn hα₀ ht
    have hΓt_le :
        ((subgraphCopiesWithDiffEdges H n α₀ t).card : ℝ) ≤
          C_cycle k * (n : ℝ) ^ (t - 1) :=
      hdiff_t.1.trans hdiff_t.2
    have hpt_sub : p ^ t - p ^ k ≤ p ^ t := sub_le_self _ (pow_nonneg hp0 k)
    have hpt_split : p ^ t = p * p ^ (t - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel ht1, pow_succ']
    calc
      ((subgraphCopiesWithDiffEdges H n α₀ t).card : ℝ) * (p ^ t - p ^ k)
        ≤ ((subgraphCopiesWithDiffEdges H n α₀ t).card : ℝ) * p ^ t :=
          mul_le_mul_of_nonneg_left hpt_sub (Nat.cast_nonneg _)
      _ ≤ (C_cycle k * (n : ℝ) ^ (t - 1)) * p ^ t :=
          mul_le_mul_of_nonneg_right hΓt_le (pow_nonneg hp0 t)
      _ = C_cycle k * p * ((n : ℝ) * p) ^ (t - 1) := by rw [hpt_split, mul_pow]; ring
  exact ⟨hΓ_nat, hW_mean, hlam_ord, htv⟩

end SteinMethod
