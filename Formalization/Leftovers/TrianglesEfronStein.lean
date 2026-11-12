/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Leftovers.MonotoneKolm
import Formalization.RandomGraph.Triangles

/-!
# Edge-Bit Coordinates & Efron–Stein Variance Bound for Triangle Counts
(`Formalization.Leftovers.TrianglesEfronStein`)

Provides the edge-bit representation of Erdős–Rényi triangle counts (`SteinIntro.tex:918-941`),
wedge-sum coordinate differences (`triCountBits_sub_update`), and the Efron–Stein variance bound
`variance_triTA₀_le` on the doubled Bernoulli product space.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Edge-Bit Coordinates, Wedge Sums, and Triangle Coordinate Differences -/

abbrev EdgeIdx (n : ℕ) := Fin (n.choose 2)
abbrev EdgeBits (n : ℕ) := BitVec (n.choose 2)
abbrev EdgePairs (n : ℕ) := EdgeBits n × EdgeBits n

private noncomputable def equivEdge (n : ℕ) : EdgeIdx n ≃ EdgePair n :=
  (Fintype.equivFinOfCardEq (card_edgePair n)).symm
private noncomputable def bitsToEdgeBits (n : ℕ) (x : EdgeBits n) : EdgePair n → Bool :=
  fun e ↦ x ((equivEdge n).symm e)
noncomputable def bitsToGraph (n : ℕ) (x : EdgeBits n) : SimpleGraph (Fin n) :=
  graphOfEdgeBits (bitsToEdgeBits n x)

lemma map_bitsToGraph_eq_erdosRenyi {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bitPi (n.choose 2) (bernoulliMeasure true false ⟨p, hp0, hp1⟩)).map (bitsToGraph n) =
      erdosRenyi n p := by
  set μ₀ := bernoulliMeasure true false ⟨p, hp0, hp1⟩
  have hmap1 : (bitPi (n.choose 2) μ₀).map (bitsToEdgeBits n) = Measure.pi fun _ ↦ μ₀ := by
    refine measure_eq_of_singleton fun ω ↦ ?_
    have hpre : bitsToEdgeBits n ⁻¹' {ω} = {fun k ↦ ω (equivEdge n k)} := by
      ext x; simp only [mem_preimage, mem_singleton_iff, funext_iff, bitsToEdgeBits]
      exact ⟨fun h k ↦ by simpa using h (equivEdge n k),
        fun h e ↦ by simpa using h ((equivEdge n).symm e)⟩
    rw [Measure.map_apply .of_discrete .of_discrete, hpre, pi_singleton_apply,
      pi_singleton_apply, ← (equivEdge n).prod_comp]
  have hcomp : bitsToGraph n = graphOfEdgeBits ∘ bitsToEdgeBits n := rfl
  unfold erdosRenyi
  rw [Set.projIcc_of_mem zero_le_one (Set.mem_Icc.mpr ⟨hp0, hp1⟩), hcomp,
    ← Measure.map_map measurable_graphOfEdgeBits .of_discrete, hmap1]

private noncomputable def mkEdgeIdx {n : ℕ} {u v : Fin n} (h : u ≠ v) : EdgeIdx n :=
  (equivEdge n).symm ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using h⟩
private lemma mkEdgeIdx_eq_iff {n : ℕ} {u v : Fin n} (h : u ≠ v) (k : EdgeIdx n) :
    mkEdgeIdx h = k ↔ s(u, v) = (equivEdge n k).1 := by
  simp only [mkEdgeIdx, Equiv.symm_apply_eq, Subtype.ext_iff]
private lemma equivEdge_mkEdgeIdx {n : ℕ} {u v : Fin n} (h : u ≠ v) :
    (equivEdge n (mkEdgeIdx h)).1 = s(u, v) := by simp [mkEdgeIdx]

private noncomputable def endFst (n : ℕ) (k : EdgeIdx n) : Fin n := (Quot.out (equivEdge n k).1).1
private noncomputable def endSnd (n : ℕ) (k : EdgeIdx n) : Fin n := (Quot.out (equivEdge n k).1).2
private lemma mk_endFst_endSnd (n : ℕ) (k : EdgeIdx n) :
    s(endFst n k, endSnd n k) = (equivEdge n k).1 := Quot.out_eq (equivEdge n k).1
private lemma endFst_ne_endSnd (n : ℕ) (k : EdgeIdx n) : endFst n k ≠ endSnd n k :=
  fun h ↦ (equivEdge n k).2 (by rw [← mk_endFst_endSnd, Sym2.mk_isDiag_iff]; exact h)
private lemma mkEdgeIdx_endFst_endSnd (n : ℕ) (k : EdgeIdx n) :
    mkEdgeIdx (endFst_ne_endSnd n k) = k := by rw [mkEdgeIdx_eq_iff, mk_endFst_endSnd]

private lemma bitsToGraph_adj_iff (n : ℕ) (x : EdgeBits n) {u v : Fin n} (h : u ≠ v) :
    (bitsToGraph n x).Adj u v ↔ x (mkEdgeIdx h) = true := by
  rw [← SimpleGraph.mem_edgeSet]
  exact mem_edgeSet_graphOfEdgeBits (bitsToEdgeBits n x) ⟨s(u, v), by simpa using h⟩

private noncomputable def adjBit (n : ℕ) (x : EdgeBits n) (u v : Fin n) : ℝ :=
  if h : u = v then 0 else bitVal (x (mkEdgeIdx h))
private lemma adjBit_of_ne {n : ℕ} (x : EdgeBits n) {u v : Fin n} (h : u ≠ v) :
    adjBit n x u v = bitVal (x (mkEdgeIdx h)) := by simp [adjBit, h]
private lemma adjBit_nonneg (n : ℕ) (x : EdgeBits n) (u v : Fin n) : 0 ≤ adjBit n x u v := by
  by_cases h : u = v <;> simp [adjBit, h, bitVal_nonneg]
private lemma adjBit_le_one (n : ℕ) (x : EdgeBits n) (u v : Fin n) : adjBit n x u v ≤ 1 := by
  by_cases h : u = v <;> simp [adjBit, h, bitVal_le_one]

private def otherVerts (n : ℕ) (u v : Fin n) : Finset (Fin n) := (Finset.univ.erase u).erase v
private lemma card_otherVerts {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    (otherVerts n u v).card = n - 2 := by
  rw [otherVerts, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩),
    Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin]; omega

noncomputable def wedgeSum (n : ℕ) (k : EdgeIdx n) (x : EdgeBits n) : ℝ :=
  ∑ w ∈ otherVerts n (endFst n k) (endSnd n k),
    adjBit n x (endFst n k) w * adjBit n x (endSnd n k) w

lemma wedgeSum_nonneg (n : ℕ) (k : EdgeIdx n) (x : EdgeBits n) : 0 ≤ wedgeSum n k x :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (adjBit_nonneg n x _ _) (adjBit_nonneg n x _ _)

lemma wedgeSum_le {n : ℕ} (hn : 3 ≤ n) (k : EdgeIdx n) (x : EdgeBits n) :
    wedgeSum n k x ≤ (n : ℝ) - 2 := by
  have h1 : wedgeSum n k x ≤ ∑ _w ∈ otherVerts n (endFst n k) (endSnd n k), (1 : ℝ) :=
    Finset.sum_le_sum fun w _ ↦ by
      nlinarith [adjBit_nonneg n x (endFst n k) w, adjBit_nonneg n x (endSnd n k) w,
        adjBit_le_one n x (endFst n k) w, adjBit_le_one n x (endSnd n k) w]
  rw [Finset.sum_const, card_otherVerts (endFst_ne_endSnd n k), nsmul_eq_mul, mul_one,
    Nat.cast_sub (by omega : 2 ≤ n)] at h1; simpa using h1

noncomputable def triCountBits (n : ℕ) (x : EdgeBits n) : ℝ :=
  (((bitsToGraph n x).cliqueSet 3).ncard : ℝ)

open scoped Classical in
private lemma ncard_cliqueSet_three_eq_powersetCard {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((G.cliqueSet 3).ncard : ℝ) = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 3,
      if G.IsNClique 3 s then (1 : ℝ) else 0 := by
  let S := ((Finset.univ : Finset (Fin n)).powersetCard 3).filter fun s ↦ G.IsNClique 3 s
  have hS : (S : Set (Finset (Fin n))) = G.cliqueSet 3 := by
    ext s; simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, SimpleGraph.mem_cliqueSet_iff]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.card_eq, h⟩⟩
  rw [← hS, Set.ncard_coe_finset]
  calc (S.card : ℝ) = ∑ _s ∈ S, (1 : ℝ) := by simp
    _ = _ := by simp [S]

lemma triCountBits_sub_update (n : ℕ) (k : EdgeIdx n) (x : EdgeBits n) (b : Bool) :
    triCountBits n x - triCountBits n (Function.update x k b) =
      (bitVal (x k) - bitVal b) * wedgeSum n k x := by
  classical
  rw [diff_update_eq_bitVal_sub_mul (triCountBits n) x k b]; congr 1
  set x₁ := Function.update x k true; set x₀ := Function.update x k false
  set G₁ := bitsToGraph n x₁; set G₀ := bitsToGraph n x₀
  set u := endFst n k; set v := endSnd n k
  have huv : u ≠ v := endFst_ne_endSnd n k
  rw [triCountBits, triCountBits, ncard_cliqueSet_three_eq_powersetCard G₁,
    ncard_cliqueSet_three_eq_powersetCard G₀, ← Finset.sum_sub_distrib]
  set P₃ := (Finset.univ : Finset (Fin n)).powersetCard 3
  have hfilter : (∑ s ∈ P₃, ((if G₁.IsNClique 3 s then (1 : ℝ) else 0) -
        if G₀.IsNClique 3 s then 1 else 0)) =
      ∑ s ∈ P₃.filter (fun s ↦ u ∈ s ∧ v ∈ s),
        ((if G₁.IsNClique 3 s then (1 : ℝ) else 0) - if G₀.IsNClique 3 s then 1 else 0) := by
    rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun s _ ↦ ?_
    by_cases huv_s : u ∈ s ∧ v ∈ s
    · simp [huv_s]
    · simp only [huv_s, ↓reduceIte]
      have hne : ∀ {a b : Fin n}, a ∈ s → b ∈ s → (hab : a ≠ b) → mkEdgeIdx hab ≠ k :=
        fun ha hb hab heq ↦ by
          rcases Sym2.eq_iff.mp (((mkEdgeIdx_eq_iff hab k).mp heq).trans
            (mk_endFst_endSnd n k).symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact huv_s ⟨ha, hb⟩
          · exact huv_s ⟨hb, ha⟩
      suffices hiff : G₁.IsNClique 3 s ↔ G₀.IsNClique 3 s by simp [hiff]
      simp only [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.Pairwise, Finset.mem_coe]
      refine and_congr ⟨fun h a ha b hb hab ↦ ?_, fun h a ha b hb hab ↦ ?_⟩ Iff.rfl <;>
        { have hadj := h ha hb hab; rw [bitsToGraph_adj_iff n _ hab] at hadj ⊢
          simpa [x₁, x₀, hne ha hb hab] using hadj }
  rw [hfilter, wedgeSum]
  refine (Finset.sum_bij (fun w _ ↦ ({u, v, w} : Finset (Fin n))) ?_ ?_ ?_ ?_).symm
  · intro w hw; rw [otherVerts, Finset.mem_erase, Finset.mem_erase] at hw
    simp [P₃, Finset.mem_powersetCard,
      Finset.card_triple_eq_three_iff.mpr ⟨huv, hw.2.1.symm, hw.1.symm⟩]
  · intro w₁ hw₁ w₂ _ heq; rw [otherVerts, Finset.mem_erase, Finset.mem_erase] at hw₁
    rcases by simpa using (heq ▸ by simp : w₁ ∈ ({u, v, w₂} : Finset (Fin n))) with h1 | h2 | h3
    · exact (hw₁.2.1 h1).elim
    · exact (hw₁.1 h2).elim
    · exact h3
  · intro s hs
    simp only [Finset.mem_filter, P₃, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
    obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp (show ((s.erase u).erase v).card = 1 by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hs.2.2⟩),
        Finset.card_erase_of_mem hs.2.1, hs.1])
    have hwm : w ∈ (s.erase u).erase v := hw_eq ▸ Finset.mem_singleton_self w
    have hwu := (Finset.mem_erase.mp (Finset.mem_erase.mp hwm).2).1
    have hwv := (Finset.mem_erase.mp hwm).1
    refine ⟨w, Finset.mem_erase.mpr ⟨hwv, Finset.mem_erase.mpr ⟨hwu, Finset.mem_univ w⟩⟩,
      Finset.eq_of_subset_of_card_le (fun z hz ↦ ?_)
        (by rw [hs.1, Finset.card_triple_eq_three_iff.mpr ⟨huv, hwu.symm, hwv.symm⟩])⟩
    rcases by simpa using hz with rfl | rfl | rfl
    · exact hs.2.1
    · exact hs.2.2
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hwm).2).2
  · intro w hw; rw [otherVerts, Finset.mem_erase, Finset.mem_erase] at hw
    obtain ⟨hwv, hwu, -⟩ := hw
    have hcard3 := Finset.card_triple_eq_three_iff.mpr ⟨huv, hwu.symm, hwv.symm⟩
    have hnot0 : ¬ G₀.IsNClique 3 {u, v, w} := fun h0 ↦ by
      have hadj : G₀.Adj u v := h0.1 (by simp) (by simp) huv
      rw [bitsToGraph_adj_iff n x₀ huv, mkEdgeIdx_endFst_endSnd] at hadj; simp [x₀] at hadj
    have hkuw : mkEdgeIdx hwu.symm ≠ k := fun heq ↦ hwv (Sym2.congr_right.mp
      (((mkEdgeIdx_eq_iff hwu.symm k).mp heq).trans (mk_endFst_endSnd n k).symm))
    have hkvw : mkEdgeIdx hwv.symm ≠ k := fun heq ↦ hwu (Sym2.congr_right.mp
      ((((mkEdgeIdx_eq_iff hwv.symm k).mp heq).trans (mk_endFst_endSnd n k).symm).trans
        Sym2.eq_swap))
    have h1_iff : G₁.IsNClique 3 {u, v, w} ↔
        x (mkEdgeIdx hwu.symm) = true ∧ x (mkEdgeIdx hwv.symm) = true := by
      rw [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]
      have hadj_uv : G₁.Adj u v := by
        rw [bitsToGraph_adj_iff n x₁ huv, mkEdgeIdx_endFst_endSnd]; simp [x₁]
      have hadj_uw : G₁.Adj u w ↔ x (mkEdgeIdx hwu.symm) = true := by
        rw [bitsToGraph_adj_iff n x₁ hwu.symm]; simp [x₁, hkuw]
      have hadj_vw : G₁.Adj v w ↔ x (mkEdgeIdx hwv.symm) = true := by
        rw [bitsToGraph_adj_iff n x₁ hwv.symm]; simp [x₁, hkvw]
      refine ⟨fun ⟨hcl, _⟩ ↦ ⟨hadj_uw.mp (hcl (by simp) (by simp) hwu.symm),
        hadj_vw.mp (hcl (by simp) (by simp) hwv.symm)⟩, fun ⟨huw, hvw⟩ ↦ ⟨?_, hcard3⟩⟩
      intro a ha b hb hab
      rcases by simpa using ha with rfl | rfl | rfl <;>
        rcases by simpa using hb with rfl | rfl | rfl
      · exact (hab rfl).elim
      · exact hadj_uv
      · exact hadj_uw.mpr huw
      · exact hadj_uv.symm
      · exact (hab rfl).elim
      · exact hadj_vw.mpr hvw
      · exact (hadj_uw.mpr huw).symm
      · exact (hadj_vw.mpr hvw).symm
      · exact (hab rfl).elim
    rw [ite_eq_right_iff.mpr fun h0 ↦ (hnot0 h0).elim, sub_zero,
      adjBit_of_ne x hwu.symm, adjBit_of_ne x hwv.symm]
    by_cases hG₁ : G₁.IsNClique 3 {u, v, w}
    · obtain ⟨h1, h2⟩ := h1_iff.mp hG₁; simp [hG₁, h1, h2, bitVal]
    · cases hx1 : x (mkEdgeIdx hwu.symm)
      · simp [hG₁, bitVal]
      · cases hx2 : x (mkEdgeIdx hwv.symm)
        · simp [hG₁, bitVal]
        · exact (hG₁ (h1_iff.mpr ⟨hx1, hx2⟩)).elim

/-! ### Section 2: Second-Moment & Efron–Stein Variance Bound on `triTA₀` -/

private lemma sq_sum_le_card_mul_sum_sq {α : Type*} (S : Finset α) (f : α → ℝ) :
    (∑ w ∈ S, f w) ^ 2 ≤ (S.card : ℝ) * ∑ w ∈ S, f w ^ 2 := by
  have h0 : 0 ≤ ∑ w₁ ∈ S, ∑ w₂ ∈ S, (f w₁ - f w₂) ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsub : ∀ w₁ : α, (∑ w₂ ∈ S, (f w₁ - f w₂) ^ 2) =
      (S.card : ℝ) * f w₁ ^ 2 - 2 * (f w₁ * ∑ w₂ ∈ S, f w₂) + ∑ w₂ ∈ S, f w₂ ^ 2 := fun w₁ ↦ by
    simp_rw [show ∀ w₂ : α, (f w₁ - f w₂) ^ 2 = f w₁ ^ 2 - 2 * (f w₁ * f w₂) + f w₂ ^ 2 from
      fun _ ↦ by ring, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
  have hexp : (∑ w₁ ∈ S, ∑ w₂ ∈ S, (f w₁ - f w₂) ^ 2) =
      2 * (S.card : ℝ) * (∑ w ∈ S, f w ^ 2) - 2 * (∑ w ∈ S, f w) ^ 2 := by
    simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, sq]; ring
  linarith

private lemma integral_wedgeSum_sq_le {n : ℕ} (hn : 3 ≤ n) (q : unitInterval) (k : EdgeIdx n) :
    ∫ x, (wedgeSum n k x) ^ 2 ∂bitPi (n.choose 2) (bernoulliMeasure true false q) ≤
      ((n : ℝ) - 2) ^ 2 * (q : ℝ) ^ 2 := by
  set μ₀ := bernoulliMeasure true false q; set ν := bitPi (n.choose 2) μ₀
  set u := endFst n k; set v := endSnd n k; set S := otherVerts n u v
  have huv : u ≠ v := endFst_ne_endSnd n k
  have hScard : (S.card : ℝ) = (n : ℝ) - 2 := by
    rw [card_otherVerts huv, Nat.cast_sub (by omega : 2 ≤ n)]; norm_num
  have hpt : ∀ x : EdgeBits n,
      (wedgeSum n k x) ^ 2 ≤ ((n : ℝ) - 2) * ∑ w ∈ S, adjBit n x u w * adjBit n x v w := fun x ↦ by
    refine (sq_sum_le_card_mul_sum_sq S _).trans_eq ?_
    rw [hScard]; congr 1; refine Finset.sum_congr rfl fun w hw ↦ ?_
    dsimp only [S, otherVerts] at hw; rw [Finset.mem_erase, Finset.mem_erase] at hw
    rw [adjBit_of_ne x hw.2.1.symm, adjBit_of_ne x hw.1.symm, mul_pow, bitVal_sq, bitVal_sq]
  refine (integral_mono (finite_discrete_integrable _) (finite_discrete_integrable _) hpt).trans ?_
  rw [integral_const_mul, integral_finsetSum S fun _ _ ↦ finite_discrete_integrable _]
  have hterm : ∀ w ∈ S, (∫ x, adjBit n x u w * adjBit n x v w ∂ν) = (q : ℝ) ^ 2 := fun w hw ↦ by
    dsimp only [S, otherVerts] at hw; rw [Finset.mem_erase, Finset.mem_erase] at hw
    set k₁ := mkEdgeIdx hw.2.1.symm; set k₂ := mkEdgeIdx hw.1.symm
    have hk12 : k₁ ≠ k₂ := fun heq ↦ huv (Sym2.congr_left.mp (by
      calc s(u, w) = (equivEdge n k₁).1 := (equivEdge_mkEdgeIdx hw.2.1.symm).symm
        _ = (equivEdge n k₂).1 := by rw [heq]
        _ = s(v, w) := equivEdge_mkEdgeIdx hw.1.symm))
    rw [show (fun x : EdgeBits n ↦ adjBit n x u w * adjBit n x v w) =
      fun x ↦ bitVal (x k₁) * bitVal (x k₂) from
        funext fun x ↦ by rw [adjBit_of_ne x hw.2.1.symm, adjBit_of_ne x hw.1.symm],
      integral_pi_mul_of_disjoint μ₀ {k₁} {k₂} (Finset.disjoint_singleton.mpr hk12)
        (fun _ _ h ↦ by rw [h k₁ (Finset.mem_singleton_self k₁)])
        (fun _ _ h ↦ by rw [h k₂ (Finset.mem_singleton_self k₂)]),
      integral_bernoulli_pi_eval q k₁ bitVal, integral_bernoulli_pi_eval q k₂ bitVal]
    simp [bitVal]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hScard]; exact le_of_eq (by ring)

private noncomputable def adjEdges (n : ℕ) (e : EdgeIdx n) : Finset (EdgeIdx n) :=
  let S := otherVerts n (endFst n e) (endSnd n e)
  (S.attach.image fun c ↦ mkEdgeIdx (Finset.mem_erase.mp (Finset.mem_erase.mp c.2).2).1.symm) ∪
    (S.attach.image fun c ↦ mkEdgeIdx (Finset.mem_erase.mp c.2).1.symm)

private lemma card_adjEdges_le (n : ℕ) (e : EdgeIdx n) : (adjEdges n e).card ≤ 2 * (n - 2) := by
  unfold adjEdges; refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := (otherVerts n (endFst n e) (endSnd n e)).attach)
    (f := fun c ↦ mkEdgeIdx (Finset.mem_erase.mp (Finset.mem_erase.mp c.2).2).1.symm)
  have h2 := Finset.card_image_le (s := (otherVerts n (endFst n e) (endSnd n e)).attach)
    (f := fun c ↦ mkEdgeIdx (Finset.mem_erase.mp c.2).1.symm)
  rw [Finset.card_attach, card_otherVerts (endFst_ne_endSnd n e)] at h1 h2; omega

private lemma notMem_adjEdges_self (n : ℕ) (e : EdgeIdx n) : e ∉ adjEdges n e := by
  intro hm; simp only [adjEdges, Finset.mem_union, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hm
  rcases hm with ⟨c, hc, heq⟩ | ⟨c, hc, heq⟩ <;>
    rw [otherVerts, Finset.mem_erase, Finset.mem_erase] at hc
  · exact hc.1 (Sym2.congr_right.mp
      (((mkEdgeIdx_eq_iff _ e).mp heq).trans (mk_endFst_endSnd n e).symm))
  · exact hc.2.1 (Sym2.congr_right.mp
      ((((mkEdgeIdx_eq_iff _ e).mp heq).trans (mk_endFst_endSnd n e).symm).trans Sym2.eq_swap))

private lemma wedgeSum_update_of_notMem {n : ℕ} {e k : EdgeIdx n}
    (hk : k ∉ adjEdges n e) (η : EdgeBits n) (β : Bool) :
    wedgeSum n k (Function.update η e β) = wedgeSum n k η := by
  have huv : endFst n k ≠ endSnd n k := endFst_ne_endSnd n k
  have hmemA : ∀ {c : Fin n} (hca : c ≠ endFst n e) (hcb : c ≠ endSnd n e),
      s(endFst n e, c) = (equivEdge n k).1 → False :=
    fun {c} hca hcb heq ↦ hk (Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨⟨c, Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, Finset.mem_univ c⟩⟩⟩,
        Finset.mem_attach _ _, (mkEdgeIdx_eq_iff hca.symm k).mpr heq⟩))
  have hmemB : ∀ {c : Fin n} (hca : c ≠ endFst n e) (hcb : c ≠ endSnd n e),
      s(endSnd n e, c) = (equivEdge n k).1 → False :=
    fun {c} hca hcb heq ↦ hk (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨⟨c, Finset.mem_erase.mpr ⟨hcb, Finset.mem_erase.mpr ⟨hca, Finset.mem_univ c⟩⟩⟩,
        Finset.mem_attach _ _, (mkEdgeIdx_eq_iff hcb.symm k).mpr heq⟩))
  refine Finset.sum_congr rfl fun w hw ↦ ?_
  rw [otherVerts, Finset.mem_erase, Finset.mem_erase] at hw
  have h1 : mkEdgeIdx hw.2.1.symm ≠ e := fun heq ↦ by
    rcases Sym2.eq_iff.mp (((mkEdgeIdx_eq_iff _ e).mp heq).trans (mk_endFst_endSnd n e).symm) with
      ⟨hu, hw'⟩ | ⟨hu, hw'⟩
    · exact hmemA (by rw [← hu]; exact huv.symm) (by rw [← hw']; exact hw.1.symm)
        (by rw [← hu]; exact mk_endFst_endSnd n k)
    · exact hmemB (by rw [← hw']; exact hw.1.symm) (by rw [← hu]; exact huv.symm)
        (by rw [← hu]; exact mk_endFst_endSnd n k)
  have h2 : mkEdgeIdx hw.1.symm ≠ e := fun heq ↦ by
    rcases Sym2.eq_iff.mp (((mkEdgeIdx_eq_iff _ e).mp heq).trans (mk_endFst_endSnd n e).symm) with
      ⟨hv, hw'⟩ | ⟨hv, hw'⟩
    · exact hmemA (by rw [← hv]; exact huv) (by rw [← hw']; exact hw.2.1.symm)
        (by rw [← hv, Sym2.eq_swap]; exact mk_endFst_endSnd n k)
    · exact hmemB (by rw [← hw']; exact hw.2.1.symm) (by rw [← hv]; exact huv)
        (by rw [← hv, Sym2.eq_swap]; exact mk_endFst_endSnd n k)
  simp [adjBit, hw.2.1.symm, hw.1.symm, h1, h2]

private lemma abs_wedgeSum_sub_le_of_endpoints {n : ℕ} {e k : EdgeIdx n} {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : (equivEdge n e).1 = s(a, b)) (hk : (equivEdge n k).1 = s(a, c)) :
    mkEdgeIdx hbc ≠ k ∧ ∀ η : EdgeBits n,
      |wedgeSum n k (Function.update η e true) - wedgeSum n k (Function.update η e false)| ≤
        bitVal (η (mkEdgeIdx hbc)) := by
  set k' := mkEdgeIdx hbc
  have hk'_ne_k : k' ≠ k := fun heq ↦
    hab.symm (Sym2.congr_left.mp (((mkEdgeIdx_eq_iff hbc k).mp heq).trans hk))
  have hk'_ne_e : k' ≠ e := fun heq ↦
    hac.symm (Sym2.congr_left.mp (Sym2.eq_swap.trans (((mkEdgeIdx_eq_iff hbc e).mp heq).trans he)))
  refine ⟨hk'_ne_k, fun η ↦ ?_⟩
  have huv_ac : s(endFst n k, endSnd n k) = s(a, c) := (mk_endFst_endSnd n k).trans hk
  have hb_u : b ≠ endFst n k := by
    rcases Sym2.eq_iff.mp huv_ac with ⟨hu, _⟩ | ⟨hu, _⟩
    · rw [hu]; exact hab.symm
    · rw [hu]; exact hbc
  have hb_v : b ≠ endSnd n k := by
    rcases Sym2.eq_iff.mp huv_ac with ⟨_, hv⟩ | ⟨_, hv⟩
    · rw [hv]; exact hbc
    · rw [hv]; exact hab.symm
  have hb_mem : b ∈ otherVerts n (endFst n k) (endSnd n k) :=
    Finset.mem_erase.mpr ⟨hb_v, Finset.mem_erase.mpr ⟨hb_u, Finset.mem_univ b⟩⟩
  rw [wedgeSum, wedgeSum, ← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ hb_mem]
  have herase : ∑ w ∈ (otherVerts n (endFst n k) (endSnd n k)).erase b,
      (adjBit n (Function.update η e true) (endFst n k) w *
          adjBit n (Function.update η e true) (endSnd n k) w -
        adjBit n (Function.update η e false) (endFst n k) w *
          adjBit n (Function.update η e false) (endSnd n k) w) = 0 :=
    Finset.sum_eq_zero fun w hw ↦ by
      rw [Finset.mem_erase, otherVerts, Finset.mem_erase, Finset.mem_erase] at hw
      obtain ⟨hwb, hwv, hwu, -⟩ := hw
      have h1 : mkEdgeIdx hwu.symm ≠ e := fun heq ↦ by
        rcases Sym2.eq_iff.mp (((mkEdgeIdx_eq_iff _ e).mp heq).trans he) with ⟨_, hw'⟩ | ⟨hu', _⟩
        · exact hwb hw'
        · exact hb_u hu'.symm
      have h2 : mkEdgeIdx hwv.symm ≠ e := fun heq ↦ by
        rcases Sym2.eq_iff.mp (((mkEdgeIdx_eq_iff _ e).mp heq).trans he) with ⟨_, hw'⟩ | ⟨hv', _⟩
        · exact hwb hw'
        · exact hb_v hv'.symm
      simp [adjBit, hwu.symm, hwv.symm, h1, h2]
  rw [herase, add_zero, adjBit_of_ne _ hb_u.symm, adjBit_of_ne _ hb_v.symm,
    adjBit_of_ne _ hb_u.symm, adjBit_of_ne _ hb_v.symm]
  rcases Sym2.eq_iff.mp huv_ac with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [(mkEdgeIdx_eq_iff _ e).mpr (by rw [hu, he]),
      (mkEdgeIdx_eq_iff _ k').mpr (by rw [hv, equivEdge_mkEdgeIdx, Sym2.eq_swap])]
    simp only [Function.update_self, Function.update_of_ne hk'_ne_e]
    cases η k' <;> norm_num [bitVal]
  · rw [(mkEdgeIdx_eq_iff _ k').mpr (by rw [hu, equivEdge_mkEdgeIdx, Sym2.eq_swap]),
      (mkEdgeIdx_eq_iff _ e).mpr (by rw [hv, he])]
    simp only [Function.update_self, Function.update_of_ne hk'_ne_e]
    cases η k' <;> norm_num [bitVal]

private lemma exists_thirdEdge_of_mem_adjEdges {n : ℕ} {e k : EdgeIdx n} (hk : k ∈ adjEdges n e) :
    ∃ k' : EdgeIdx n, k' ≠ k ∧ ∀ η : EdgeBits n,
      |wedgeSum n k (Function.update η e true) - wedgeSum n k (Function.update η e false)| ≤
        bitVal (η k') := by
  simp only [adjEdges, Finset.mem_union, Finset.mem_image, Finset.mem_attach,
    true_and, Subtype.exists] at hk
  have hab : endFst n e ≠ endSnd n e := endFst_ne_endSnd n e
  rcases hk with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
    rw [otherVerts, Finset.mem_erase, Finset.mem_erase] at hc
  · obtain ⟨hne, hbnd⟩ := abs_wedgeSum_sub_le_of_endpoints hab hc.2.1.symm hc.1.symm
      (mk_endFst_endSnd n e).symm (equivEdge_mkEdgeIdx hc.2.1.symm)
    exact ⟨mkEdgeIdx hc.1.symm, hne, hbnd⟩
  · obtain ⟨hne, hbnd⟩ := abs_wedgeSum_sub_le_of_endpoints hab.symm hc.1.symm hc.2.1.symm
      ((mk_endFst_endSnd n e).symm.trans Sym2.eq_swap) (equivEdge_mkEdgeIdx hc.1.symm)
    exact ⟨mkEdgeIdx hc.2.1.symm, hne, hbnd⟩

private lemma hybVec_update_fst {K : ℕ} (m : ℕ) (z : BitVec K × BitVec K) (e : Fin K) (b : Bool) :
    hybVec m (Function.update z.1 e b, z.2) =
      if e.1 < m then hybVec m z else Function.update (hybVec m z) e b := by
  split_ifs with hlt <;> ext i <;> by_cases hie : i = e <;>
    first | (subst hie; simp [hybVec, hlt]) | simp [hybVec, hie]

private lemma hybVec_update_snd {K : ℕ} (m : ℕ) (z : BitVec K × BitVec K) (e : Fin K) (b : Bool) :
    hybVec m (z.1, Function.update z.2 e b) =
      if e.1 < m then Function.update (hybVec m z) e b else hybVec m z := by
  split_ifs with hlt <;> ext i <;> by_cases hie : i = e <;>
    first | (subst hie; simp [hybVec, hlt]) | simp [hybVec, hie]

private lemma integral_B_eq {K : ℕ} (q : unitInterval) (k : Fin K) :
    (∫ z, (bitVal (z.1 k) - bitVal (z.2 k)) ^ 2
        ∂bitProd K (bernoulliMeasure true false q)) = 2 * (q : ℝ) * (1 - (q : ℝ)) := by
  set ν := bitPi K (bernoulliMeasure true false q)
  rw [bitProd, integral_prod _ (finite_discrete_integrable _)]
  let φ : Bool → ℝ := fun a ↦ ∫ y, (bitVal a - bitVal (y k)) ^ 2 ∂ν
  change ∫ x, φ (x k) ∂ν = _; rw [integral_bernoulli_pi_eval q k φ]
  have h1 : φ true = 1 - (q : ℝ) := by
    dsimp [φ, ν]; rw [integral_bernoulli_pi_eval q k (fun b ↦ (bitVal true - bitVal b) ^ 2)]
    simp [bitVal]
  have h0 : φ false = (q : ℝ) := by
    dsimp [φ, ν]; rw [integral_bernoulli_pi_eval q k (fun b ↦ (bitVal false - bitVal b) ^ 2)]
    simp [bitVal]
  rw [h1, h0]; ring

private lemma integral_hybBit_eq {K : ℕ} (q : unitInterval) (m : ℕ) (k' : Fin K) :
    (∫ z, bitVal (hybVec m z k') ∂bitProd K (bernoulliMeasure true false q)) = (q : ℝ) := by
  set μ₀ := bernoulliMeasure true false q
  have hm := integral_map (μ := bitProd K μ₀) (φ := hybVec m) Measurable.of_discrete.aemeasurable
    (f := fun x ↦ bitVal (x k')) Measurable.of_discrete.aestronglyMeasurable
  rw [hybVec_map_eq_pi μ₀ m, integral_bernoulli_pi_eval q k' bitVal] at hm
  simpa [bitVal] using hm.symm

private lemma integral_fstBit_eq {K : ℕ} (q : unitInterval) (k' : Fin K) :
    (∫ z, bitVal (z.1 k') ∂bitProd K (bernoulliMeasure true false q)) = (q : ℝ) := by
  simp_rw [show ∀ z : BitVec K × BitVec K, z.1 k' = hybVec 0 z k' from fun _ ↦ by simp [hybVec]]
  exact integral_hybBit_eq q 0 k'

private lemma sum_univ_eq_add_sum_of_support {α : Type*} [Fintype α]
    (e : α) (A : Finset α) (he : e ∉ A) (g : α → ℝ) (hz : ∀ k, k ≠ e → k ∉ A → g k = 0) :
    ∑ k : α, g k = g e + ∑ k ∈ A, g k := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e)]; congr 1
  have hsub : A ⊆ Finset.univ.erase e := fun k hk ↦
    Finset.mem_erase.mpr ⟨fun h ↦ he (h ▸ hk), Finset.mem_univ k⟩
  rw [← Finset.sum_sdiff hsub, Finset.sum_eq_zero fun k hk ↦ ?_, zero_add]
  rw [Finset.mem_sdiff, Finset.mem_erase] at hk; exact hz k hk.1.1 hk.2

noncomputable def triTA₀ (n : ℕ) (z : EdgePairs n) : ℝ :=
  ∑ k : EdgeIdx n,
    (bitVal (z.1 k) - bitVal (z.2 k)) ^ 2 * wedgeSum n k z.1 * wedgeSum n k (hybVec k.1 z)

/-- Efron–Stein variance bound for the unnormalized triangle-count auxiliary sum `triTA₀` on the
doubled Bernoulli product space (`SteinIntro.tex:935-941`). -/
theorem variance_triTA₀_le {n : ℕ} (hn : 3 ≤ n) (q : unitInterval) :
    variance (triTA₀ n) (bitProd (n.choose 2) (bernoulliMeasure true false q)) ≤
      (n.choose 2 : ℝ) * 2 * (q : ℝ) ^ 3 * (1 - (q : ℝ)) * ((n : ℝ) - 2) ^ 4 *
        (2 + 40 * (1 - (q : ℝ))) := by
  set μ₀ := bernoulliMeasure true false q; set P₂ := bitProd (n.choose 2) μ₀
  set N₂ : ℝ := (n : ℝ) - 2
  have hN₂_nn : 0 ≤ N₂ := by
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    dsimp [N₂]; linarith
  let B : EdgeIdx n → EdgePairs n → ℝ := fun k z ↦ (bitVal (z.1 k) - bitVal (z.2 k)) ^ 2
  have hB_sq : ∀ k z, (B k z) ^ 2 = B k z := fun k z ↦ by
    dsimp only [B]; cases z.1 k <;> cases z.2 k <;> norm_num [bitVal]
  have hB_nn : ∀ k z, 0 ≤ B k z := fun _ _ ↦ sq_nonneg _
  refine (prod_pi_bool_efron_stein q (triTA₀ n)).trans ?_
  have he_bound : ∀ e : EdgeIdx n,
      (∫ z, (triTA₀ n (Function.update z.1 e true, z.2) -
          triTA₀ n (Function.update z.1 e false, z.2)) ^ 2 ∂P₂) +
        (∫ z, (triTA₀ n (z.1, Function.update z.2 e true) -
          triTA₀ n (z.1, Function.update z.2 e false)) ^ 2 ∂P₂) ≤
      2 * N₂ ^ 4 * (q : ℝ) ^ 2 * (2 + 40 * (1 - (q : ℝ))) := fun e ↦ by
    classical
    set A := adjEdges n e
    have hA_card : (A.card : ℝ) ≤ 2 * N₂ := by
      have hcast : ((2 * (n - 2) : ℕ) : ℝ) = 2 * N₂ := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ n)]; norm_num [N₂]
      exact (Nat.cast_le.mpr (card_adjEdges_le n e)).trans_eq hcast
    have he_notA : e ∉ A := notMem_adjEdges_self n e
    let kStar : (k : EdgeIdx n) → k ∈ A → EdgeIdx n := fun _ hk ↦
      (exists_thirdEdge_of_mem_adjEdges hk).choose
    have hkStar_ne : ∀ k (hk : k ∈ A), kStar k hk ≠ k := fun _ hk ↦
      (exists_thirdEdge_of_mem_adjEdges hk).choose_spec.1
    have hkStar_bnd : ∀ k (hk : k ∈ A) η,
        |wedgeSum n k (Function.update η e true) - wedgeSum n k (Function.update η e false)| ≤
          bitVal (η (kStar k hk)) := fun _ hk ↦
      (exists_thirdEdge_of_mem_adjEdges hk).choose_spec.2
    let D₀ : EdgePairs n → ℝ := fun z ↦ wedgeSum n e z.1 * wedgeSum n e (hybVec e.1 z)
    let X₁ : (k : EdgeIdx n) → k ∈ A → EdgePairs n → ℝ :=
      fun k hk z ↦ N₂ * B k z * (bitVal (z.1 (kStar k hk)) + bitVal (hybVec k.1 z (kStar k hk)))
    let X₂ : (k : EdgeIdx n) → k ∈ A → EdgePairs n → ℝ :=
      fun k hk z ↦ N₂ * B k z * bitVal (hybVec k.1 z (kStar k hk))
    have hD₀_int : ∫ z, (D₀ z) ^ 2 ∂P₂ ≤ N₂ ^ 4 * (q : ℝ) ^ 2 := by
      have hpt : ∀ z, (D₀ z) ^ 2 ≤ N₂ ^ 2 * (wedgeSum n e z.1) ^ 2 := fun z ↦ by
        have hle : D₀ z ≤ N₂ * wedgeSum n e z.1 := by
          dsimp only [D₀]; nlinarith [wedgeSum_nonneg n e z.1, wedgeSum_le hn e (hybVec e.1 z)]
        nlinarith [mul_nonneg (wedgeSum_nonneg n e z.1) (wedgeSum_nonneg n e (hybVec e.1 z))]
      refine (integral_mono (finite_discrete_integrable _) (finite_discrete_integrable _)
        hpt).trans ?_
      rw [integral_const_mul]
      have hfst : P₂.map Prod.fst = bitPi (n.choose 2) μ₀ := Measure.fst_prod
      have hl := integral_map (μ := P₂) (φ := Prod.fst) measurable_fst.aemeasurable
        (f := fun x ↦ (wedgeSum n e x) ^ 2) Measurable.of_discrete.aestronglyMeasurable
      rw [hfst] at hl; rw [← hl]; nlinarith [integral_wedgeSum_sq_le hn q e, sq_nonneg N₂]
    have hpert : ∀ (z zt zf : EdgePairs n) (Y : (k : EdgeIdx n) → k ∈ A → ℝ),
        (∀ k ≠ e, B k zt = B k z ∧ B k zf = B k z) → |B e zt - B e zf| = 1 →
        (∀ k ∉ A, wedgeSum n k zt.1 = wedgeSum n k z.1 ∧ wedgeSum n k zf.1 = wedgeSum n k z.1 ∧
          wedgeSum n k (hybVec k.1 zt) = wedgeSum n k (hybVec k.1 z) ∧
          wedgeSum n k (hybVec k.1 zf) = wedgeSum n k (hybVec k.1 z)) →
        (∀ k (hk : k ∈ A), |wedgeSum n k zt.1 * wedgeSum n k (hybVec k.1 zt) -
          wedgeSum n k zf.1 * wedgeSum n k (hybVec k.1 zf)| ≤ N₂ * Y k hk) →
        (triTA₀ n zt - triTA₀ n zf) ^ 2 ≤
          2 * (D₀ z) ^ 2 + 2 * (A.card : ℝ) * ∑ k ∈ A.attach, (N₂ * B k.1 z * Y k.1 k.2) ^ 2 := by
      intro z zt zf Y hBk hBe hnoA hYA
      let g : EdgeIdx n → ℝ := fun k ↦ B k zt * wedgeSum n k zt.1 * wedgeSum n k (hybVec k.1 zt) -
        B k zf * wedgeSum n k zf.1 * wedgeSum n k (hybVec k.1 zf)
      have hsum : triTA₀ n zt - triTA₀ n zf = g e + ∑ k ∈ A, g k := by
        dsimp only [triTA₀]; rw [← Finset.sum_sub_distrib]
        refine sum_univ_eq_add_sum_of_support e A he_notA g fun k hke hkA ↦ ?_
        obtain ⟨hb1, hb2⟩ := hBk k hke; obtain ⟨hw1, hw2, hw3, hw4⟩ := hnoA k hkA
        dsimp only [g]; rw [hb1, hb2, hw1, hw2, hw3, hw4, sub_self]
      have hge : |g e| ≤ D₀ z := by
        obtain ⟨hw1, hw2, hw3, hw4⟩ := hnoA e he_notA
        rw [show g e = (B e zt - B e zf) * D₀ z by dsimp [g, D₀]; rw [hw1, hw2, hw3, hw4]; ring,
          abs_mul, hBe, one_mul,
          abs_of_nonneg (mul_nonneg (wedgeSum_nonneg n e _) (wedgeSum_nonneg n e _))]
      have hgA : ∀ k : {x // x ∈ A}, |g k.1| ≤ N₂ * B k.1 z * Y k.1 k.2 := fun ⟨k, hk⟩ ↦ by
        obtain ⟨hb1, hb2⟩ := hBk k (fun h ↦ he_notA (h ▸ hk))
        rw [show g k = B k z * (wedgeSum n k zt.1 * wedgeSum n k (hybVec k.1 zt) -
          wedgeSum n k zf.1 * wedgeSum n k (hybVec k.1 zf)) by dsimp [g]; rw [hb1, hb2]; ring,
          abs_mul, abs_of_nonneg (hB_nn k z)]
        exact (mul_le_mul_of_nonneg_left (hYA k hk) (hB_nn k z)).trans_eq (by ring)
      have habs : |triTA₀ n zt - triTA₀ n zf| ≤
          D₀ z + ∑ k ∈ A.attach, (N₂ * B k.1 z * Y k.1 k.2) := by
        rw [hsum, ← Finset.sum_attach A]
        exact (abs_add_le _ _).trans (add_le_add hge
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ hgA k)))
      have hsq : (triTA₀ n zt - triTA₀ n zf) ^ 2 ≤
          (D₀ z + ∑ k ∈ A.attach, (N₂ * B k.1 z * Y k.1 k.2)) ^ 2 := by
        rw [← sq_abs (triTA₀ n zt - triTA₀ n zf)]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      have hcs := sq_sum_le_card_mul_sum_sq A.attach (fun k ↦ N₂ * B k.1 z * Y k.1 k.2)
      rw [Finset.card_attach] at hcs
      nlinarith [sq_nonneg (D₀ z - ∑ k ∈ A.attach, (N₂ * B k.1 z * Y k.1 k.2))]
    have hhyb_noA₁ : ∀ z k, k ∉ A → ∀ b,
        wedgeSum n k (hybVec k.1 (Function.update z.1 e b, z.2)) = wedgeSum n k (hybVec k.1 z) :=
      fun z k hkA b ↦ by
        by_cases hlt : e.1 < k.1 <;> simp [hybVec_update_fst, hlt, wedgeSum_update_of_notMem hkA]
    have hhyb_noA₂ : ∀ z k, k ∉ A → ∀ b,
        wedgeSum n k (hybVec k.1 (z.1, Function.update z.2 e b)) = wedgeSum n k (hybVec k.1 z) :=
      fun z k hkA b ↦ by
        by_cases hlt : e.1 < k.1 <;> simp [hybVec_update_snd, hlt, wedgeSum_update_of_notMem hkA]
    have hpt₁ : ∀ z, (triTA₀ n (Function.update z.1 e true, z.2) -
          triTA₀ n (Function.update z.1 e false, z.2)) ^ 2 ≤
        2 * (D₀ z) ^ 2 + 2 * (A.card : ℝ) * ∑ k ∈ A.attach, (X₁ k.1 k.2 z) ^ 2 := fun z ↦ by
      refine hpert z _ _ (fun k hk ↦ bitVal (z.1 (kStar k hk)) + bitVal (hybVec k.1 z (kStar k hk)))
        (fun k hke ↦ ⟨by dsimp [B]; rw [Function.update_of_ne hke],
          by dsimp [B]; rw [Function.update_of_ne hke]⟩)
        (by dsimp [B]; rw [Function.update_self, Function.update_self]; cases z.2 e <;>
          norm_num [bitVal])
        (fun k hkA ↦ ⟨wedgeSum_update_of_notMem hkA z.1 true,
          wedgeSum_update_of_notMem hkA z.1 false, hhyb_noA₁ z k hkA true, hhyb_noA₁ z k hkA false⟩)
        (fun k hk ↦ ?_)
      set zt := (Function.update z.1 e true, z.2); set zf := (Function.update z.1 e false, z.2)
      have hd2 : |wedgeSum n k (hybVec k.1 zt) - wedgeSum n k (hybVec k.1 zf)| ≤
          bitVal (hybVec k.1 z (kStar k hk)) := by
        dsimp only [zt, zf]; by_cases hlt : e.1 < k.1 <;>
          simp [hybVec_update_fst, hlt, bitVal_nonneg, hkStar_bnd k hk]
      rw [show wedgeSum n k zt.1 * wedgeSum n k (hybVec k.1 zt) -
        wedgeSum n k zf.1 * wedgeSum n k (hybVec k.1 zf) =
        (wedgeSum n k zt.1 - wedgeSum n k zf.1) * wedgeSum n k (hybVec k.1 zt) +
          wedgeSum n k zf.1 * (wedgeSum n k (hybVec k.1 zt) - wedgeSum n k (hybVec k.1 zf)) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (wedgeSum_nonneg n k (hybVec k.1 zt)),
        abs_of_nonneg (wedgeSum_nonneg n k zf.1)]
      nlinarith [hkStar_bnd k hk z.1, wedgeSum_le hn k (hybVec k.1 zt), wedgeSum_le hn k zf.1,
        abs_nonneg (wedgeSum n k zt.1 - wedgeSum n k zf.1),
        abs_nonneg (wedgeSum n k (hybVec k.1 zt) - wedgeSum n k (hybVec k.1 zf))]
    have hpt₂ : ∀ z, (triTA₀ n (z.1, Function.update z.2 e true) -
          triTA₀ n (z.1, Function.update z.2 e false)) ^ 2 ≤
        2 * (D₀ z) ^ 2 + 2 * (A.card : ℝ) * ∑ k ∈ A.attach, (X₂ k.1 k.2 z) ^ 2 := fun z ↦ by
      refine hpert z _ _ (fun k hk ↦ bitVal (hybVec k.1 z (kStar k hk)))
        (fun k hke ↦ ⟨by dsimp [B]; rw [Function.update_of_ne hke],
          by dsimp [B]; rw [Function.update_of_ne hke]⟩)
        (by dsimp [B]; rw [Function.update_self, Function.update_self]; cases z.1 e <;>
          norm_num [bitVal])
        (fun k hkA ↦ ⟨rfl, rfl, hhyb_noA₂ z k hkA true, hhyb_noA₂ z k hkA false⟩)
        (fun k hk ↦ ?_)
      set zt := (z.1, Function.update z.2 e true); set zf := (z.1, Function.update z.2 e false)
      have hd2 : |wedgeSum n k (hybVec k.1 zt) - wedgeSum n k (hybVec k.1 zf)| ≤
          bitVal (hybVec k.1 z (kStar k hk)) := by
        dsimp only [zt, zf]; by_cases hlt : e.1 < k.1 <;>
          simp [hybVec_update_snd, hlt, bitVal_nonneg, hkStar_bnd k hk]
      rw [show wedgeSum n k zt.1 * wedgeSum n k (hybVec k.1 zt) -
        wedgeSum n k zf.1 * wedgeSum n k (hybVec k.1 zf) =
        wedgeSum n k z.1 * (wedgeSum n k (hybVec k.1 zt) - wedgeSum n k (hybVec k.1 zf)) by
          dsimp [zt, zf]; ring, abs_mul, abs_of_nonneg (wedgeSum_nonneg n k z.1)]
      nlinarith [wedgeSum_le hn k z.1,
        abs_nonneg (wedgeSum n k (hybVec k.1 zt) - wedgeSum n k (hybVec k.1 zf))]
    have hX₂_int : ∀ k : {x // x ∈ A},
        ∫ z, (X₂ k.1 k.2 z) ^ 2 ∂P₂ = 2 * N₂ ^ 2 * (q : ℝ) ^ 2 * (1 - (q : ℝ)) := fun ⟨k, hk⟩ ↦ by
      set k' := kStar k hk
      let ψ : Bool → Bool → ℝ := fun a b ↦ bitVal (if k'.1 < k.1 then b else a)
      have hsq : ∀ z, (X₂ k hk z) ^ 2 = N₂ ^ 2 * (B k z * ψ (z.1 k') (z.2 k')) := fun z ↦ by
        have hhyb : bitVal (hybVec k.1 z k') = ψ (z.1 k') (z.2 k') := by dsimp [hybVec, ψ]
        dsimp only [X₂, k']; rw [hhyb]
        calc (N₂ * B k z * ψ (z.1 k') (z.2 k')) ^ 2
            = N₂ ^ 2 * (B k z) ^ 2 * (ψ (z.1 k') (z.2 k')) ^ 2 := by ring
          _ = N₂ ^ 2 * (B k z * ψ (z.1 k') (z.2 k')) := by rw [hB_sq, bitVal_sq]; ring
      simp_rw [hsq, integral_const_mul]
      rw [integral_prod_pi_mul_of_ne μ₀ (hkStar_ne k hk).symm
        (fun a b ↦ (bitVal a - bitVal b) ^ 2) ψ, integral_B_eq q k,
        show (∫ z, ψ (z.1 k') (z.2 k') ∂P₂) = (q : ℝ) by
          simpa [hybVec, ψ] using integral_hybBit_eq q k.1 k']; ring
    have hX₁_int : ∀ k : {x // x ∈ A},
        ∫ z, (X₁ k.1 k.2 z) ^ 2 ∂P₂ ≤ 8 * N₂ ^ 2 * (q : ℝ) ^ 2 * (1 - (q : ℝ)) := fun ⟨k, hk⟩ ↦ by
      set k' := kStar k hk
      let ψ₁ : Bool → Bool → ℝ := fun a b ↦ bitVal a + bitVal (if k'.1 < k.1 then b else a)
      have hle : ∀ z, (X₁ k hk z) ^ 2 ≤ 2 * N₂ ^ 2 * (B k z * ψ₁ (z.1 k') (z.2 k')) := fun z ↦ by
        set u := bitVal (z.1 k'); set v := bitVal (hybVec k.1 z k')
        have huv_sq : (u + v) ^ 2 ≤ 2 * (u + v) := by
          nlinarith [bitVal_sq (z.1 k'), bitVal_sq (hybVec k.1 z k'), sq_nonneg (u - v)]
        have h1 : (X₁ k hk z) ^ 2 = (N₂ ^ 2 * B k z) * (u + v) ^ 2 := by
          dsimp only [X₁, k', u, v]
          calc (N₂ * B k z * (u + v)) ^ 2 = N₂ ^ 2 * (B k z) ^ 2 * (u + v) ^ 2 := by ring
            _ = (N₂ ^ 2 * B k z) * (u + v) ^ 2 := by rw [hB_sq]
        have hψ_eq : u + v = ψ₁ (z.1 k') (z.2 k') := by dsimp [u, v, hybVec, ψ₁]
        rw [h1, hψ_eq]
        exact (mul_le_mul_of_nonneg_left (hψ_eq ▸ huv_sq)
          (mul_nonneg (sq_nonneg N₂) (hB_nn k z))).trans_eq (by ring)
      refine (integral_mono (finite_discrete_integrable _) (finite_discrete_integrable _)
        hle).trans_eq ?_
      rw [integral_const_mul, integral_prod_pi_mul_of_ne μ₀ (hkStar_ne k hk).symm
        (fun a b ↦ (bitVal a - bitVal b) ^ 2) ψ₁, integral_B_eq q k,
        show (fun z : EdgePairs n ↦ ψ₁ (z.1 k') (z.2 k')) =
          fun z ↦ bitVal (z.1 k') + bitVal (hybVec k.1 z k') from funext fun _ ↦ rfl,
        integral_add (finite_discrete_integrable _) (finite_discrete_integrable _),
        integral_fstBit_eq q k', integral_hybBit_eq q k.1 k']; ring
    have hint : ∀ (F : EdgePairs n → ℝ) (X : (k : EdgeIdx n) → k ∈ A → EdgePairs n → ℝ),
        (∀ z, F z ≤ 2 * (D₀ z) ^ 2 + 2 * (A.card : ℝ) * ∑ k ∈ A.attach, (X k.1 k.2 z) ^ 2) →
        ∫ z, F z ∂P₂ ≤ 2 * (∫ z, (D₀ z) ^ 2 ∂P₂) +
          2 * (A.card : ℝ) * ∑ k ∈ A.attach, ∫ z, (X k.1 k.2 z) ^ 2 ∂P₂ := fun F X hpt ↦
      (integral_mono (finite_discrete_integrable _) (finite_discrete_integrable _) hpt).trans_eq (by
        rw [integral_add (finite_discrete_integrable _) (finite_discrete_integrable _),
          integral_const_mul, integral_const_mul,
          integral_finsetSum A.attach fun _ _ ↦ finite_discrete_integrable _])
    have hint₁ := hint _ X₁ hpt₁; have hint₂ := hint _ X₂ hpt₂
    have hsum₁ : ∑ k ∈ A.attach, ∫ z, (X₁ k.1 k.2 z) ^ 2 ∂P₂ ≤
        (A.card : ℝ) * (8 * N₂ ^ 2 * (q : ℝ) ^ 2 * (1 - (q : ℝ))) :=
      (Finset.sum_le_sum fun k _ ↦ hX₁_int k).trans
        (by rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul])
    have hsum₂ : ∑ k ∈ A.attach, ∫ z, (X₂ k.1 k.2 z) ^ 2 ∂P₂ =
        (A.card : ℝ) * (2 * N₂ ^ 2 * (q : ℝ) ^ 2 * (1 - (q : ℝ))) := by
      simp_rw [hX₂_int, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    have hA_sq : (A.card : ℝ) ^ 2 ≤ 4 * N₂ ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg N₂) (sq_nonneg (q : ℝ))) (sub_nonneg.mpr q.2.2)]
  have hsum_le : ∑ e : EdgeIdx n,
      ((∫ z, (triTA₀ n (Function.update z.1 e true, z.2) -
          triTA₀ n (Function.update z.1 e false, z.2)) ^ 2 ∂P₂) +
        (∫ z, (triTA₀ n (z.1, Function.update z.2 e true) -
          triTA₀ n (z.1, Function.update z.2 e false)) ^ 2 ∂P₂)) ≤
      (n.choose 2 : ℝ) * (2 * N₂ ^ 4 * (q : ℝ) ^ 2 * (2 + 40 * (1 - (q : ℝ)))) :=
    (Finset.sum_le_sum fun e _ ↦ he_bound e).trans (by simp [nsmul_eq_mul])
  exact (mul_le_mul_of_nonneg_left hsum_le
    (mul_nonneg q.2.1 (sub_nonneg.mpr q.2.2))).trans_eq (by ring)

end SteinMethod
