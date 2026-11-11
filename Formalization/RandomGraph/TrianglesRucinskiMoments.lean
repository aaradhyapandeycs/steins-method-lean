/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.RandomGraph.Triangles
import Formalization.RandomGraph.TrianglesRucinskiIdentities

/-!
# Size-Bias Moment Bounds for Ruciński's Triangle CLT (`TrianglesRucinskiMoments`)

Establishes the binomial, variance, dependency-graph two-edge variance, and slice second-moment
bounds for triangle counts in $G(n, p)$ (`SteinIntro.tex:943-944`, `\cite{ruc88}`):

* `erdosRenyi_triangles_variance_lower_bounds`: simultaneous sparse and dense lower bounds on
  $\operatorname{Var}(T)$.
* `variance_rucTwoEdgeSum_le`: dependency-graph variance bound for two-edge triple indicators.
* `delta_slice_sq_integral_le`: second-moment bound for size-bias slice increments.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### 1. Binomial and Variance Lower Bounds -/

section Helpers

lemma six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  calc 6 * n.choose 3
      = Nat.factorial 3 * n.choose 3 := rfl
    _ = n.descFactorial 3 := (Nat.descFactorial_eq_factorial_mul_choose n 3).symm
    _ = n * (n - 1) * (n - 2) := by
        simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
        ring

lemma choose_three_bounds {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ 3 / 24 ≤ (n.choose 3 : ℝ) ∧ (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
  have h6 := six_mul_choose_three n
  have hlo_nat : n * n * n ≤ 24 * n.choose 3 := by
    have h1 : n ≤ 2 * (n - 1) := by omega
    have h2 : n ≤ 2 * (n - 2) := by omega
    calc n * n * n
        ≤ n * (2 * (n - 1)) * (2 * (n - 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left n h1) h2
      _ = 4 * (n * (n - 1) * (n - 2)) := by ring
      _ = 24 * n.choose 3 := by linarith
  have hhi_nat : 6 * n.choose 3 ≤ n * n * n := by
    rw [h6]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left n (Nat.sub_le n 1)) (Nat.sub_le n 2)
  have hlo_r : (n : ℝ) * (n : ℝ) * (n : ℝ) ≤ 24 * (n.choose 3 : ℝ) := by exact_mod_cast hlo_nat
  have hhi_r : 6 * (n.choose 3 : ℝ) ≤ (n : ℝ) * (n : ℝ) * (n : ℝ) := by exact_mod_cast hhi_nat
  have hpow : (n : ℝ) ^ 3 = (n : ℝ) * (n : ℝ) * (n : ℝ) := by ring
  exact ⟨by linarith, by linarith⟩

lemma erdosRenyi_triangles_mean_and_variance {n : ℕ} {p : ℝ}
    (hn : 3 ≤ n) (hp0 : 0 < p) (hp1 : p < 1) :
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    (∫ G, T G ∂erdosRenyi n p = (n.choose 3 : ℝ) * p ^ 3) ∧
      ProbabilityTheory.variance T (erdosRenyi n p) =
        (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) := by
  obtain ⟨hμ, hv, _⟩ := Sec3_2_1_triangles_restricted_proof stdNormalLaw hn hp0 hp1
    measurable_id.aemeasurable Measure.map_id
  exact ⟨hμ, hv⟩

lemma erdosRenyi_triangles_variance_lower_bounds {n : ℕ} {p : ℝ}
    (hn : 6 ≤ n) (hp0 : 0 < p) (hp1 : p < 1) :
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    (n : ℝ) ^ 3 * p ^ 3 * (1 - p) / 24 ≤ ProbabilityTheory.variance T (erdosRenyi n p) ∧
      (n : ℝ) ^ 4 * p ^ 5 * (1 - p) / 16 ≤ ProbabilityTheory.variance T (erdosRenyi n p) := by
  intro T
  obtain ⟨_, hv⟩ := erdosRenyi_triangles_mean_and_variance (by omega : 3 ≤ n) hp0 hp1
  obtain ⟨hch_lo, _⟩ := choose_three_bounds (by omega : 4 ≤ n)
  have hq : 0 < 1 - p := by linarith
  have hn_cast : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1p3_ge : 1 - p ≤ 1 - p ^ 3 := by
    have : 1 - p ^ 3 - (1 - p) = (1 - p) * (p + p ^ 2) := by ring
    nlinarith [sq_nonneg p]
  have h1p3_nn : 0 ≤ 1 - p ^ 3 := by linarith
  have hextra_nn : 0 ≤ 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg p)) hq.le
  have hextra_ge : (3 / 2 : ℝ) * (n : ℝ) * p ^ 2 * (1 - p) ≤
      3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p) := by
    have hlin : (3 / 2 : ℝ) * (n : ℝ) ≤ 3 * ((n : ℝ) - 3) := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlin (sq_nonneg p)) hq.le
  rw [hv]
  constructor
  · calc (n : ℝ) ^ 3 * p ^ 3 * (1 - p) / 24
        = ((n : ℝ) ^ 3 / 24) * p ^ 3 * (1 - p) := by ring
      _ ≤ (n.choose 3 : ℝ) * p ^ 3 * (1 - p) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hch_lo (pow_nonneg hp0.le 3)) hq.le
      _ ≤ (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0.le 3))
  · calc (n : ℝ) ^ 4 * p ^ 5 * (1 - p) / 16
        = ((n : ℝ) ^ 3 / 24) * p ^ 3 * ((3 / 2 : ℝ) * (n : ℝ) * p ^ 2 * (1 - p)) := by ring
      _ ≤ (n.choose 3 : ℝ) * p ^ 3 * ((3 / 2 : ℝ) * (n : ℝ) * p ^ 2 * (1 - p)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hch_lo (pow_nonneg hp0.le 3))
            (by positivity)
      _ ≤ (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0.le 3))

end Helpers

/-! ### 2. Dependency-Graph Variance Bound for Two-Edge Indicators -/

/-- Centered two-edge indicator $Z_i - 3 p^2 (1 - p)$ (`SteinIntro.tex:943-944`). -/
noncomputable def rucTwoEdgeCentered {n : ℕ} (p : ℝ) (i : Fin (n.choose 3))
    (G : SimpleGraph (Fin n)) : ℝ :=
  rucTwoEdgeInd i G - 3 * p ^ 2 * (1 - p)

private lemma isDependencyGraph_rucTwoEdgeCentered {n : ℕ} (p : ℝ) :
    IsDependencyGraph (erdosRenyi n p) (rucTwoEdgeCentered (n := n) p) rucTriNhbd := by
  refine ⟨self_mem_rucTriNhbd, fun _ _ ↦ rucTriNhbd_symm, ?_⟩
  intro A B hAB
  let E_A : Finset (EdgePair n) := A.biUnion fun a ↦ rucEdgesOfFinset (rucTripleOf a)
  let E_B : Finset (EdgePair n) := B.biUnion fun b ↦ rucEdgesOfFinset (rucTripleOf b)
  have hdisj : Disjoint E_A E_B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    obtain ⟨a, ha, hea⟩ := Finset.mem_biUnion.mp heA
    obtain ⟨b, hb, heb⟩ := Finset.mem_biUnion.mp heB
    have hnot : ¬ 2 ≤ (rucTripleOf a ∩ rucTripleOf b).card := by
      simpa [mem_rucTriNhbd] using hAB a ha b hb
    have he_inter : e ∈ rucEdgesOfFinset (rucTripleOf a ∩ rucTripleOf b) := by
      rw [rucEdgesOfFinset_inter]
      exact Finset.mem_inter.mpr ⟨hea, heb⟩
    rw [rucEdgesOfFinset_eq_empty_of_card_le_one (by omega)] at he_inter
    exact Finset.notMem_empty e he_inter
  let f_A : (E_A → ℝ) → (A → ℝ) := fun x a ↦
    (∑ e ∈ (rucEdgesOfFinset (rucTripleOf a.1)).attach,
      (1 - x ⟨e.1, Finset.mem_biUnion.mpr ⟨a.1, a.2, e.2⟩⟩) *
        ∏ e' ∈ ((rucEdgesOfFinset (rucTripleOf a.1)).erase e.1).attach,
          x ⟨e'.1, Finset.mem_biUnion.mpr ⟨a.1, a.2, Finset.mem_of_mem_erase e'.2⟩⟩) -
      3 * p ^ 2 * (1 - p)
  let f_B : (E_B → ℝ) → (B → ℝ) := fun y b ↦
    (∑ e ∈ (rucEdgesOfFinset (rucTripleOf b.1)).attach,
      (1 - y ⟨e.1, Finset.mem_biUnion.mpr ⟨b.1, b.2, e.2⟩⟩) *
        ∏ e' ∈ ((rucEdgesOfFinset (rucTripleOf b.1)).erase e.1).attach,
          y ⟨e'.1, Finset.mem_biUnion.mpr ⟨b.1, b.2, Finset.mem_of_mem_erase e'.2⟩⟩) -
      3 * p ^ 2 * (1 - p)
  have hf_A : Measurable f_A := by
    rw [measurable_pi_iff]
    intro a
    refine Measurable.sub_const ?_ _
    refine Finset.measurable_sum _ fun e _ ↦ Measurable.mul ?_ ?_
    · exact measurable_const.sub
        (measurable_pi_apply (⟨e.1, Finset.mem_biUnion.mpr ⟨a.1, a.2, e.2⟩⟩ : E_A))
    · exact Finset.measurable_prod _ fun e' _ ↦ measurable_pi_apply
        (⟨e'.1, Finset.mem_biUnion.mpr ⟨a.1, a.2, Finset.mem_of_mem_erase e'.2⟩⟩ : E_A)
  have hf_B : Measurable f_B := by
    rw [measurable_pi_iff]
    intro b
    refine Measurable.sub_const ?_ _
    refine Finset.measurable_sum _ fun e _ ↦ Measurable.mul ?_ ?_
    · exact measurable_const.sub
        (measurable_pi_apply (⟨e.1, Finset.mem_biUnion.mpr ⟨b.1, b.2, e.2⟩⟩ : E_B))
    · exact Finset.measurable_prod _ fun e' _ ↦ measurable_pi_apply
        (⟨e'.1, Finset.mem_biUnion.mpr ⟨b.1, b.2, Finset.mem_of_mem_erase e'.2⟩⟩ : E_B)
  have heq_A : (fun G : SimpleGraph (Fin n) ↦ f_A (fun e ↦ edgeIndicator e.1 G)) =
      fun G (a : A) ↦ rucTwoEdgeCentered p a.1 G := by
    ext G a
    simp only [f_A, rucTwoEdgeCentered, rucTwoEdgeInd, rucTwoEdgeTerm]
    congr 1
    conv_lhs =>
      arg 2
      ext e
      rw [Finset.prod_attach ((rucEdgesOfFinset (rucTripleOf a.1)).erase e.1)
        (fun e' ↦ edgeIndicator e' G)]
    exact Finset.sum_attach (rucEdgesOfFinset (rucTripleOf a.1))
      (fun e ↦ (1 - edgeIndicator e G) *
        ∏ e' ∈ (rucEdgesOfFinset (rucTripleOf a.1)).erase e, edgeIndicator e' G)
  have heq_B : (fun G : SimpleGraph (Fin n) ↦ f_B (fun e ↦ edgeIndicator e.1 G)) =
      fun G (b : B) ↦ rucTwoEdgeCentered p b.1 G := by
    ext G b
    simp only [f_B, rucTwoEdgeCentered, rucTwoEdgeInd, rucTwoEdgeTerm]
    congr 1
    conv_lhs =>
      arg 2
      ext e
      rw [Finset.prod_attach ((rucEdgesOfFinset (rucTripleOf b.1)).erase e.1)
        (fun e' ↦ edgeIndicator e' G)]
    exact Finset.sum_attach (rucEdgesOfFinset (rucTripleOf b.1))
      (fun e ↦ (1 - edgeIndicator e G) *
        ∏ e' ∈ (rucEdgesOfFinset (rucTripleOf b.1)).erase e, edgeIndicator e' G)
  simpa only [heq_A, heq_B] using
    erdosRenyi_indepFun_of_disjoint_edges E_A E_B hdisj hf_A hf_B

private lemma integral_indicator_one_er {n : ℕ} {p : ℝ} (S : Set (SimpleGraph (Fin n))) :
    ∫ G, S.indicator (1 : SimpleGraph (Fin n) → ℝ) G ∂erdosRenyi n p =
      (erdosRenyi n p).real S := by
  rw [integral_indicator MeasurableSet.of_discrete]
  simp

private lemma integral_rucTwoEdgeInd {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, rucTwoEdgeInd i G ∂erdosRenyi n p = 3 * p ^ 2 * (1 - p) := by
  let E_i := rucEdgesOfFinset (rucTripleOf i)
  have hE_card : E_i.card = 3 := card_rucEdgesOfFinset_of_card_eq_three (card_rucTripleOf i)
  dsimp only [rucTwoEdgeInd]
  rw [integral_finsetSum E_i fun _ _ ↦ Integrable.of_finite]
  have hterm : ∀ e ∈ E_i,
      ∫ G, rucTwoEdgeTerm E_i e G ∂erdosRenyi n p = p ^ 2 * (1 - p) := by
    intro e he
    simp_rw [rucTwoEdgeTerm_eq_indicator]
    rw [integral_indicator_one_er]
    have hset : {H : SimpleGraph (Fin n) |
          (∀ e' ∈ E_i.erase e, e'.1 ∈ H.edgeSet) ∧ e.1 ∉ H.edgeSet} =
        {H : SimpleGraph (Fin n) |
          (∀ e' ∈ E_i.erase e, e'.1 ∈ H.edgeSet) ∧
            (∀ e'' ∈ ({e} : Finset (EdgePair n)), e''.1 ∉ H.edgeSet)} := by
      ext H; simp
    have hdisj : Disjoint (E_i.erase e) ({e} : Finset (EdgePair n)) :=
      Finset.disjoint_singleton_right.mpr (Finset.notMem_erase e E_i)
    have hcard_er : (E_i.erase e).card = 2 := by
      have := Finset.card_erase_add_one he
      omega
    rw [hset, erdosRenyi_real_cylinder hp0 hp1 _ _ hdisj, hcard_er, Finset.card_singleton, pow_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, hE_card, nsmul_eq_mul]
  ring

private lemma integral_rucTwoEdgeCentered {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, rucTwoEdgeCentered p i G ∂erdosRenyi n p = 0 := by
  dsimp only [rucTwoEdgeCentered]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_rucTwoEdgeInd hp0 hp1 i,
    integral_const, probReal_univ, one_smul, sub_self]

private lemma integral_rucTwoEdgeCentered_sq_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, rucTwoEdgeCentered p i G * rucTwoEdgeCentered p i G ∂erdosRenyi n p ≤
      3 * p ^ 2 * (1 - p) := by
  let c := 3 * p ^ 2 * (1 - p)
  have hexp : (fun G ↦ rucTwoEdgeCentered p i G * rucTwoEdgeCentered p i G) =
      fun G ↦ rucTwoEdgeInd i G - 2 * c * rucTwoEdgeInd i G + c ^ 2 := by
    ext G
    have hsq := rucTwoEdgeInd_sq i G
    dsimp only [rucTwoEdgeCentered]
    nlinarith
  rw [hexp, integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_rucTwoEdgeInd hp0 hp1 i, integral_const, probReal_univ, one_smul]
  nlinarith [sq_nonneg c]

private lemma integral_rucTwoEdgeCentered_mul_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {i k : Fin (n.choose 3)} (hk : k ∈ (rucTriNhbd i).erase i) :
    ∫ G, rucTwoEdgeCentered p i G * rucTwoEdgeCentered p k G ∂erdosRenyi n p ≤
      9 * p ^ 3 * (1 - p) := by
  let c := 3 * p ^ 2 * (1 - p)
  have hexp : (fun G ↦ rucTwoEdgeCentered p i G * rucTwoEdgeCentered p k G) =
      fun G ↦ (rucTwoEdgeInd i G * rucTwoEdgeInd k G - c * rucTwoEdgeInd i G) -
        c * rucTwoEdgeInd k G + c ^ 2 := by
    ext G; dsimp only [rucTwoEdgeCentered]; ring
  rw [hexp, integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, integral_const_mul, integral_rucTwoEdgeInd hp0 hp1 i,
    integral_rucTwoEdgeInd hp0 hp1 k, integral_const, probReal_univ, one_smul]
  suffices hprod : ∫ G, rucTwoEdgeInd i G * rucTwoEdgeInd k G ∂erdosRenyi n p ≤
      9 * p ^ 3 * (1 - p) by
    nlinarith [sq_nonneg c]
  let E_i := rucEdgesOfFinset (rucTripleOf i)
  let E_k := rucEdgesOfFinset (rucTripleOf k)
  have hprod_sum : (fun G ↦ rucTwoEdgeInd i G * rucTwoEdgeInd k G) =
      fun G ↦ ∑ e₁ ∈ E_i, ∑ e₂ ∈ E_k, rucTwoEdgeTerm E_i e₁ G * rucTwoEdgeTerm E_k e₂ G := by
    ext G; dsimp only [rucTwoEdgeInd]; rw [Finset.sum_mul_sum]
  rw [hprod_sum, integral_finsetSum E_i fun _ _ ↦ Integrable.of_finite]
  have hpair : ∀ e₁ ∈ E_i, ∀ e₂ ∈ E_k,
      ∫ G, rucTwoEdgeTerm E_i e₁ G * rucTwoEdgeTerm E_k e₂ G ∂erdosRenyi n p ≤
        p ^ 3 * (1 - p) := by
    intro e₁ he₁ e₂ he₂
    simp_rw [rucTwoEdgeTerm_mul_eq_indicator]
    rw [integral_indicator_one_er]
    let S_pos := E_i.erase e₁ ∪ E_k.erase e₂
    let S_neg : Finset (EdgePair n) := {e₁, e₂}
    by_cases hdisj : Disjoint S_pos S_neg
    · rw [erdosRenyi_real_cylinder hp0 hp1 S_pos S_neg hdisj]
      have hunion : S_pos ∪ S_neg = E_i ∪ E_k := by
        ext x
        simp only [S_pos, S_neg, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ((⟨_, hx⟩ | ⟨_, hx⟩) | rfl | rfl)
          · exact Or.inl hx
          · exact Or.inr hx
          · exact Or.inl he₁
          · exact Or.inr he₂
        · rintro (hx | hx)
          · by_cases hxe : x = e₁
            · exact Or.inr (Or.inl hxe)
            · exact Or.inl (Or.inl ⟨hxe, hx⟩)
          · by_cases hxe : x = e₂
            · exact Or.inr (Or.inr hxe)
            · exact Or.inl (Or.inr ⟨hxe, hx⟩)
      have hsum_card : S_pos.card + S_neg.card = 5 := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
        exact card_rucEdgesOfFinset_union_of_inter_two (card_rucTripleOf i) (card_rucTripleOf k)
          (mem_erase_rucTriNhbd_iff.mp hk)
      have hneg_ge1 : 1 ≤ S_neg.card :=
        Finset.one_le_card.mpr ⟨e₁, Finset.mem_insert_self e₁ {e₂}⟩
      have hneg_le2 : S_neg.card ≤ 2 :=
        (Finset.card_insert_le e₁ {e₂}).trans (by simp)
      have hpos_ge3 : 3 ≤ S_pos.card := by omega
      exact mul_le_mul
        (pow_le_pow_of_le_one hp0 hp1 hpos_ge3)
        ((pow_le_pow_of_le_one (by linarith) (by linarith) hneg_ge1).trans_eq (pow_one _))
        (pow_nonneg (by linarith) _) (pow_nonneg hp0 3)
    · obtain ⟨e, he_pos, he_neg⟩ := Finset.not_disjoint_iff.mp hdisj
      have hempty : {H : SimpleGraph (Fin n) |
          (∀ x ∈ S_pos, x.1 ∈ H.edgeSet) ∧ (∀ x ∈ S_neg, x.1 ∉ H.edgeSet)} = ∅ := by
        ext H
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro hp hn
        exact hn e he_neg (hp e he_pos)
      rw [hempty, measureReal_empty]
      exact mul_nonneg (pow_nonneg hp0 3) (by linarith)
  have hEi : E_i.card = 3 := card_rucEdgesOfFinset_of_card_eq_three (card_rucTripleOf i)
  have hEk : E_k.card = 3 := card_rucEdgesOfFinset_of_card_eq_three (card_rucTripleOf k)
  calc ∑ e₁ ∈ E_i, ∫ G, (∑ e₂ ∈ E_k,
          rucTwoEdgeTerm E_i e₁ G * rucTwoEdgeTerm E_k e₂ G) ∂erdosRenyi n p
      = ∑ e₁ ∈ E_i, ∑ e₂ ∈ E_k,
          ∫ G, rucTwoEdgeTerm E_i e₁ G * rucTwoEdgeTerm E_k e₂ G ∂erdosRenyi n p :=
        Finset.sum_congr rfl fun _ _ ↦ integral_finsetSum E_k fun _ _ ↦ Integrable.of_finite
    _ ≤ ∑ _e₁ ∈ E_i, ∑ _e₂ ∈ E_k, (p ^ 3 * (1 - p)) :=
        Finset.sum_le_sum fun e₁ he₁ ↦ Finset.sum_le_sum fun e₂ he₂ ↦ hpair e₁ he₁ e₂ he₂
    _ = 9 * p ^ 3 * (1 - p) := by
        simp only [Finset.sum_const, hEi, hEk, nsmul_eq_mul]
        ring

/-- Variance bound for the sum of two-edge indicators (`SteinIntro.tex:943-944`). -/
theorem variance_rucTwoEdgeSum_le {n : ℕ} {p : ℝ} (hn : 3 ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.variance
        (fun G ↦ ∑ j : Fin (n.choose 3), rucTwoEdgeInd j G) (erdosRenyi n p) ≤
      (n.choose 3 : ℝ) * p ^ 2 * (1 - p) * (3 + 27 * (n : ℝ) * p) := by
  have hshift : (fun G ↦ ∑ j : Fin (n.choose 3), rucTwoEdgeCentered p j G) =
      fun G ↦ (∑ j : Fin (n.choose 3), rucTwoEdgeInd j G) +
        (-((n.choose 3 : ℝ) * (3 * p ^ 2 * (1 - p)))) := by
    ext G
    simp only [rucTwoEdgeCentered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hvar_eq : ProbabilityTheory.variance
        (fun G ↦ ∑ j : Fin (n.choose 3), rucTwoEdgeInd j G) (erdosRenyi n p) =
      ProbabilityTheory.variance
        (fun G ↦ ∑ j : Fin (n.choose 3), rucTwoEdgeCentered p j G) (erdosRenyi n p) := by
    rw [hshift]
    exact (ProbabilityTheory.variance_add_const Measurable.of_discrete.aestronglyMeasurable _).symm
  rw [hvar_eq, ← depGraph_integral_quadSum_eq_variance (erdosRenyi n p)
    (N := rucTriNhbd)
    (fun _ ↦ Measurable.of_discrete.aemeasurable)
    (fun _ ↦ MemLp.of_discrete)
    (fun i ↦ integral_rucTwoEdgeCentered hp0 hp1 i)
    (isDependencyGraph_rucTwoEdgeCentered p),
    integral_finsetSum Finset.univ fun _ _ ↦ Integrable.of_finite]
  have hper_i : ∀ i : Fin (n.choose 3),
      (∫ G, ∑ k ∈ rucTriNhbd i,
          rucTwoEdgeCentered p i G * rucTwoEdgeCentered p k G ∂erdosRenyi n p) ≤
        p ^ 2 * (1 - p) * (3 + 27 * (n : ℝ) * p) := by
    intro i
    rw [integral_finsetSum (rucTriNhbd i) fun _ _ ↦ Integrable.of_finite,
      ← Finset.add_sum_erase (rucTriNhbd i) _ (self_mem_rucTriNhbd i)]
    have hdiag := integral_rucTwoEdgeCentered_sq_le hp0 hp1 i
    have hoff : (∑ k ∈ (rucTriNhbd i).erase i,
          ∫ G, rucTwoEdgeCentered p i G * rucTwoEdgeCentered p k G ∂erdosRenyi n p) ≤
        3 * ((n : ℝ) - 3) * (9 * p ^ 3 * (1 - p)) := by
      calc (∑ k ∈ (rucTriNhbd i).erase i,
              ∫ G, rucTwoEdgeCentered p i G * rucTwoEdgeCentered p k G ∂erdosRenyi n p)
          ≤ ∑ _k ∈ (rucTriNhbd i).erase i, (9 * p ^ 3 * (1 - p)) :=
            Finset.sum_le_sum fun k hk ↦ integral_rucTwoEdgeCentered_mul_le hp0 hp1 hk
        _ = 3 * ((n : ℝ) - 3) * (9 * p ^ 3 * (1 - p)) := by
            rw [Finset.sum_const, card_erase_rucTriNhbd i, nsmul_eq_mul, Nat.cast_mul,
              Nat.cast_sub hn]
            norm_num
    have hsub_le : 3 * ((n : ℝ) - 3) * (9 * p ^ 3 * (1 - p)) ≤
        27 * (n : ℝ) * p ^ 3 * (1 - p) := by
      have : 27 * (n : ℝ) * p ^ 3 * (1 - p) - 3 * ((n : ℝ) - 3) * (9 * p ^ 3 * (1 - p)) =
          81 * p ^ 3 * (1 - p) := by ring
      linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) (pow_nonneg hp0 3))
        (by linarith : 0 ≤ 1 - p)]
    linarith [show p ^ 2 * (1 - p) * (3 + 27 * (n : ℝ) * p) =
      3 * p ^ 2 * (1 - p) + 27 * (n : ℝ) * p ^ 3 * (1 - p) by ring]
  calc ∑ i : Fin (n.choose 3),
          ∫ G, (∑ k ∈ rucTriNhbd i,
            rucTwoEdgeCentered p i G * rucTwoEdgeCentered p k G) ∂erdosRenyi n p
      ≤ ∑ _i : Fin (n.choose 3), (p ^ 2 * (1 - p) * (3 + 27 * (n : ℝ) * p)) :=
        Finset.sum_le_sum fun i _ ↦ hper_i i
    _ = (n.choose 3 : ℝ) * p ^ 2 * (1 - p) * (3 + 27 * (n : ℝ) * p) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### 3. Slice Second-Moment Bound -/

/-- Second-moment bound for each slice increment $T(G \sqcup K_{t_i}) - T(G)$
(`SteinIntro.tex:943-944`). -/
theorem delta_slice_sq_integral_le {n : ℕ} {p : ℝ} (hn : 3 ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin (n.choose 3)) :
    ∫ G, ((((G ⊔ tripleGraph (rucTripleOf i)).cliqueSet 3).ncard : ℝ) -
        ((G.cliqueSet 3).ncard : ℝ)) ^ 2 ∂erdosRenyi n p ≤
      36 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4) := by
  let S := (rucTriNhbd i).erase i
  let A : SimpleGraph (Fin n) → ℝ := fun G ↦ 1 - rucTriInd i G
  let B : SimpleGraph (Fin n) → ℝ := fun G ↦ ∑ j ∈ S, rucSliceDiff i j G
  have hpoint : ∀ G : SimpleGraph (Fin n),
      ((((G ⊔ tripleGraph (rucTripleOf i)).cliqueSet 3).ncard : ℝ) -
        ((G.cliqueSet 3).ncard : ℝ)) ^ 2 ≤ 2 * A G ^ 2 + 2 * B G ^ 2 := by
    intro G
    rw [triangles_sup_tripleGraph_sub_eq G i]
    dsimp only [A, B]
    nlinarith [sq_nonneg (A G - B G)]
  have hle_sum : ∫ G, ((((G ⊔ tripleGraph (rucTripleOf i)).cliqueSet 3).ncard : ℝ) -
        ((G.cliqueSet 3).ncard : ℝ)) ^ 2 ∂erdosRenyi n p ≤
      2 * (∫ G, A G ^ 2 ∂erdosRenyi n p) + 2 * (∫ G, B G ^ 2 ∂erdosRenyi n p) := by
    calc ∫ G, ((((G ⊔ tripleGraph (rucTripleOf i)).cliqueSet 3).ncard : ℝ) -
            ((G.cliqueSet 3).ncard : ℝ)) ^ 2 ∂erdosRenyi n p
        ≤ ∫ G, (2 * A G ^ 2 + 2 * B G ^ 2) ∂erdosRenyi n p :=
          integral_mono_ae Integrable.of_finite Integrable.of_finite (Eventually.of_forall hpoint)
      _ = 2 * (∫ G, A G ^ 2 ∂erdosRenyi n p) + 2 * (∫ G, B G ^ 2 ∂erdosRenyi n p) := by
          rw [integral_add Integrable.of_finite Integrable.of_finite,
            integral_const_mul, integral_const_mul]
  have hA2 : ∫ G, A G ^ 2 ∂erdosRenyi n p ≤ 3 * (1 - p) := by
    have hAsq : (fun G ↦ A G ^ 2) = fun G ↦ 1 - rucTriInd i G := by
      ext G
      by_cases hG : G.IsNClique 3 (rucTripleOf i)
      · simp [A, rucTriInd_of_isNClique hG]
      · simp [A, rucTriInd_of_not_isNClique hG]
    rw [hAsq, integral_sub Integrable.of_finite Integrable.of_finite, integral_const,
      probReal_univ, one_smul]
    have htri : ∫ G, rucTriInd i G ∂erdosRenyi n p = p ^ 3 := by
      dsimp only [rucTriInd]
      rw [integral_indicator_one_er, erdosRenyi_real_isNClique_ruc hp0 hp1 i]
    rw [htri]
    have hfac : 3 * (1 - p) - (1 - p ^ 3) = (1 - p) * (2 - p - p ^ 2) := by ring
    have h2 : 0 ≤ 2 - p - p ^ 2 := by nlinarith
    linarith [mul_nonneg (by linarith : 0 ≤ 1 - p) h2]
  have hpair_int : ∀ j₁ ∈ S, ∀ j₂ ∈ S,
      0 ≤ ∫ G, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G ∂erdosRenyi n p ∧
        (∫ G, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G ∂erdosRenyi n p ≤ p ^ 2 * (1 - p)) ∧
        (rucTripleOf j₁ \ rucTripleOf i ≠ rucTripleOf j₂ \ rucTripleOf i →
          ∫ G, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G ∂erdosRenyi n p ≤ p ^ 4 * (1 - p)) := by
    intro j₁ hj₁ j₂ hj₂
    simp_rw [rucSliceDiff_mul_eq_indicator hj₁ hj₂]
    rw [integral_indicator_one_er]
    let E_i := rucEdgesOfFinset (rucTripleOf i)
    let P₁ := rucEdgesOfFinset (rucTripleOf j₁) \ E_i
    let P₂ := rucEdgesOfFinset (rucTripleOf j₂) \ E_i
    let N₁ := E_i ∩ rucEdgesOfFinset (rucTripleOf j₁)
    let N₂ := E_i ∩ rucEdgesOfFinset (rucTripleOf j₂)
    have hdisj : Disjoint (P₁ ∪ P₂) (N₁ ∪ N₂) := by
      rw [Finset.disjoint_left]
      intro e heP heN
      have he_ni : e ∉ E_i := by
        rcases Finset.mem_union.mp heP with h | h <;> exact (Finset.mem_sdiff.mp h).2
      have he_i : e ∈ E_i := by
        rcases Finset.mem_union.mp heN with h | h <;> exact (Finset.mem_inter.mp h).1
      exact he_ni he_i
    rw [erdosRenyi_real_cylinder hp0 hp1 (P₁ ∪ P₂) (N₁ ∪ N₂) hdisj]
    have hN_ge1 : 1 ≤ (N₁ ∪ N₂).card := by
      have h1 : N₁.card = 1 := card_inter_rucEdges_of_mem_erase hj₁
      exact h1 ▸ Finset.card_le_card Finset.subset_union_left
    have hP_ge2 : 2 ≤ (P₁ ∪ P₂).card := by
      have h2 : P₁.card = 2 := card_sdiff_rucEdges_of_mem_erase hj₁
      exact h2 ▸ Finset.card_le_card Finset.subset_union_left
    have hq_le : (1 - p) ^ (N₁ ∪ N₂).card ≤ 1 - p :=
      (pow_le_pow_of_le_one (by linarith) (by linarith) hN_ge1).trans_eq (pow_one _)
    refine ⟨mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _),
      mul_le_mul (pow_le_pow_of_le_one hp0 hp1 hP_ge2) hq_le
        (pow_nonneg (by linarith) _) (pow_nonneg hp0 2),
      fun hne ↦ ?_⟩
    have hP_eq4 : (P₁ ∪ P₂).card = 4 := by
      rw [Finset.card_union_of_disjoint (disjoint_sdiff_rucEdges_of_sdiff_ne hj₁ hj₂ hne),
        card_sdiff_rucEdges_of_mem_erase hj₁, card_sdiff_rucEdges_of_mem_erase hj₂]
    rw [hP_eq4]
    exact mul_le_mul_of_nonneg_left hq_le (pow_nonneg hp0 4)
  have hS_le : (S.card : ℝ) ≤ 3 * (n : ℝ) := by
    have hnat : S.card ≤ 3 * n := by
      rw [card_erase_rucTriNhbd i]
      exact Nat.mul_le_mul_left 3 (Nat.sub_le n 3)
    exact_mod_cast hnat
  have hB2 : ∫ G, B G ^ 2 ∂erdosRenyi n p ≤ 15 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4) := by
    classical
    have hBsq : (fun G ↦ B G ^ 2) =
        fun G ↦ ∑ j₁ ∈ S, ∑ j₂ ∈ S, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G := by
      ext G; dsimp only [B]; rw [sq, Finset.sum_mul_sum]
    rw [hBsq, integral_finsetSum S fun _ _ ↦ Integrable.of_finite]
    have hrow : ∀ j₁ ∈ S,
        ∫ G, (∑ j₂ ∈ S, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G) ∂erdosRenyi n p ≤
          4 * p ^ 2 * (1 - p) + 3 * (n : ℝ) * p ^ 4 * (1 - p) := by
      intro j₁ hj₁
      rw [integral_finsetSum S fun _ _ ↦ Integrable.of_finite,
        ← Finset.sum_filter_add_sum_filter_not S
          (fun j₂ ↦ rucTripleOf j₂ \ rucTripleOf i = rucTripleOf j₁ \ rucTripleOf i)]
      let S_eq := S.filter fun j₂ ↦
        rucTripleOf j₂ \ rucTripleOf i = rucTripleOf j₁ \ rucTripleOf i
      let S_ne := S.filter fun j₂ ↦
        ¬ (rucTripleOf j₂ \ rucTripleOf i = rucTripleOf j₁ \ rucTripleOf i)
      have h1 : (∑ j₂ ∈ S_eq,
            ∫ G, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G ∂erdosRenyi n p) ≤
          4 * p ^ 2 * (1 - p) := by
        have hcard4 : (S_eq.card : ℝ) ≤ 4 := by
          exact_mod_cast card_filter_same_sdiff_le_four hj₁
        calc (∑ j₂ ∈ S_eq,
                ∫ G, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G ∂erdosRenyi n p)
            ≤ ∑ _j₂ ∈ S_eq, (p ^ 2 * (1 - p)) :=
              Finset.sum_le_sum fun j₂ hj₂ ↦
                (hpair_int j₁ hj₁ j₂ (Finset.mem_of_mem_filter j₂ hj₂)).2.1
          _ = (S_eq.card : ℝ) * (p ^ 2 * (1 - p)) := by simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 4 * (p ^ 2 * (1 - p)) :=
              mul_le_mul_of_nonneg_right hcard4 (mul_nonneg (sq_nonneg p) (by linarith))
          _ = 4 * p ^ 2 * (1 - p) := by ring
      have h2 : (∑ j₂ ∈ S_ne,
            ∫ G, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G ∂erdosRenyi n p) ≤
          3 * (n : ℝ) * p ^ 4 * (1 - p) := by
        have hcard_ne : (S_ne.card : ℝ) ≤ 3 * (n : ℝ) :=
          (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ S))).trans hS_le
        calc (∑ j₂ ∈ S_ne,
                ∫ G, rucSliceDiff i j₁ G * rucSliceDiff i j₂ G ∂erdosRenyi n p)
            ≤ ∑ _j₂ ∈ S_ne, (p ^ 4 * (1 - p)) :=
              Finset.sum_le_sum fun j₂ hj₂ ↦ by
                rcases Finset.mem_filter.mp hj₂ with ⟨hj₂S, hne⟩
                exact (hpair_int j₁ hj₁ j₂ hj₂S).2.2 (Ne.symm hne)
          _ = (S_ne.card : ℝ) * (p ^ 4 * (1 - p)) := by simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (3 * (n : ℝ)) * (p ^ 4 * (1 - p)) :=
              mul_le_mul_of_nonneg_right hcard_ne (mul_nonneg (pow_nonneg hp0 4) (by linarith))
          _ = 3 * (n : ℝ) * p ^ 4 * (1 - p) := by ring
      exact add_le_add h1 h2
    calc ∑ j₁ ∈ S, ∫ G, (∑ j₂ ∈ S,
            rucSliceDiff i j₁ G * rucSliceDiff i j₂ G) ∂erdosRenyi n p
        ≤ ∑ _j₁ ∈ S, (4 * p ^ 2 * (1 - p) + 3 * (n : ℝ) * p ^ 4 * (1 - p)) :=
          Finset.sum_le_sum hrow
      _ = (S.card : ℝ) * (4 * p ^ 2 * (1 - p) + 3 * (n : ℝ) * p ^ 4 * (1 - p)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 * (n : ℝ)) * (4 * p ^ 2 * (1 - p) + 3 * (n : ℝ) * p ^ 4 * (1 - p)) :=
          mul_le_mul_of_nonneg_right hS_le
            (add_nonneg (mul_nonneg (by positivity) (by linarith))
              (mul_nonneg (by positivity) (by linarith)))
      _ = (1 - p) * (12 * ((n : ℝ) * p ^ 2) + 9 * ((n : ℝ) ^ 2 * p ^ 4)) := by ring
      _ ≤ (1 - p) * (6 * (1 + (n : ℝ) ^ 2 * p ^ 4) + 9 * ((n : ℝ) ^ 2 * p ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          nlinarith [sq_nonneg (1 - (n : ℝ) * p ^ 2)]
      _ ≤ 15 * (1 - p) * (1 + (n : ℝ) ^ 2 * p ^ 4) := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - p) (show (0 : ℝ) ≤ 9 by norm_num)]
  have h1_nn : 0 ≤ (n : ℝ) ^ 2 * p ^ 4 := by positivity
  linarith [mul_nonneg (by linarith : 0 ≤ 1 - p) h1_nn]

end SteinMethod
