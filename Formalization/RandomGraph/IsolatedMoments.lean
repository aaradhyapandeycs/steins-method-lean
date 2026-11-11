/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.RandomGraph.ErdosRenyi
import Formalization.Statements.Sec3
import Mathlib.Probability.Moments.Variance

/-!
# Isolated-Vertex Moments and `ISSUE-3.9` Counterexamples

Implements the Erdős–Rényi $G(n, p)$ moment calculations for Example 3.9 (`\label{ex72}`,
`SteinIntro.tex:1354-1410`), the degree-one neighbor sum identity and variance upper bound used in
the proof of Theorem 3.17 (`SteinIntro.tex:1388-1420`), and machine-checked $n = 3, p = 1/2$
counterexamples to the two false printed formulas at `SteinIntro.tex:1395` and `SteinIntro.tex:1397`
(`ISSUE-3.9`).
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace SteinMethod

/-! ### General `erdosRenyi` integration, variance, and finite-sum square helpers -/

private lemma integrable_erdosRenyi {n : ℕ} {p : ℝ} (f : SimpleGraph (Fin n) → ℝ) :
    Integrable f (erdosRenyi n p) :=
  Integrable.of_finite

private lemma memLp_two_erdosRenyi {n : ℕ} {p : ℝ} (f : SimpleGraph (Fin n) → ℝ) :
    MemLp f 2 (erdosRenyi n p) :=
  (integrable_norm_rpow_iff (integrable_erdosRenyi f).aestronglyMeasurable
    two_ne_zero ENNReal.ofNat_ne_top).mp (integrable_erdosRenyi _)

private lemma variance_erdosRenyi_eq {n : ℕ} {p : ℝ} (X : SimpleGraph (Fin n) → ℝ) :
    ProbabilityTheory.variance X (erdosRenyi n p) =
      (∫ G, X G ^ 2 ∂erdosRenyi n p) - (∫ G, X G ∂erdosRenyi n p) ^ 2 := by
  simpa [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub (memLp_two_erdosRenyi X)

private lemma integral_indicator_one_er {n : ℕ} {p : ℝ} (S : Set (SimpleGraph (Fin n))) :
    ∫ G, S.indicator (1 : SimpleGraph (Fin n) → ℝ) G ∂erdosRenyi n p =
      (erdosRenyi n p).real S := by
  rw [MeasureTheory.integral_indicator MeasurableSet.of_discrete]
  simp

private lemma indicator_one_sq {α : Type*} (S : Set α) (x : α) :
    (S.indicator (1 : α → ℝ) x) ^ 2 = S.indicator (1 : α → ℝ) x := by
  by_cases hx : x ∈ S <;> simp [hx]

private lemma indicator_one_mul {α : Type*} (S T : Set α) (x : α) :
    S.indicator (1 : α → ℝ) x * T.indicator (1 : α → ℝ) x =
      (S ∩ T).indicator (1 : α → ℝ) x := by
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [hxS, hxT]

private lemma sq_sum_eq_diag_add_offDiag {α : Type*}
    (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, f i) ^ 2 =
      (∑ i ∈ s, f i ^ 2) + ∑ x ∈ s.offDiag, f x.1 * f x.2 := by
  classical
  calc (∑ i ∈ s, f i) ^ 2
      = (∑ i ∈ s, f i) * ∑ j ∈ s, f j := sq _
    _ = ∑ i ∈ s, ∑ j ∈ s, f i * f j := Finset.sum_mul_sum s s f f
    _ = ∑ x ∈ s ×ˢ s, f x.1 * f x.2 := (Finset.sum_product' s s (fun i j ↦ f i * f j)).symm
    _ = ∑ x ∈ s.diag ∪ s.offDiag, f x.1 * f x.2 := by rw [Finset.diag_union_offDiag]
    _ = (∑ x ∈ s.diag, f x.1 * f x.2) + ∑ x ∈ s.offDiag, f x.1 * f x.2 :=
          Finset.sum_union s.disjoint_diag_offDiag
    _ = (∑ i ∈ s, f i ^ 2) + ∑ x ∈ s.offDiag, f x.1 * f x.2 := by
          rw [Finset.diag, Finset.sum_map]
          simp only [Function.Embedding.coeFn_mk, Function.diag, sq]

private lemma pow_le_one_real {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ∀ k : ℕ, x ^ k ≤ 1
  | 0 => by simp
  | k + 1 => by
      rw [pow_add, pow_one]
      exact (mul_le_mul (pow_le_one_real hx0 hx1 k) hx1 hx0 zero_le_one).trans_eq (mul_one 1)

/-! ### Edge-pair and incidence-set combinatorics on `Fin n` -/

private lemma two_le_of_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) : 2 ≤ n := by
  have hval : i.1 ≠ j.1 := fun hv ↦ h (Fin.ext hv)
  omega

private lemma three_le_of_pairwise_ne {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : 3 ≤ n := by
  have h1 : i.1 ≠ j.1 := fun hv ↦ hij (Fin.ext hv)
  have h2 : i.1 ≠ k.1 := fun hv ↦ hik (Fin.ext hv)
  have h3 : j.1 ≠ k.1 := fun hv ↦ hjk (Fin.ext hv)
  omega

private def mkEdgePair {n : ℕ} (i j : Fin n) (h : i ≠ j) : EdgePair n :=
  ⟨s(i, j), by simpa [Sym2.mk_isDiag_iff] using h⟩

@[simp]
private lemma mkEdgePair_val {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    (mkEdgePair i j h).1 = s(i, j) := rfl

private lemma mkEdgePair_comm {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    mkEdgePair i j h = mkEdgePair j i h.symm :=
  Subtype.ext Sym2.eq_swap

private def incidentEdges {n : ℕ} (i : Fin n) : Finset (EdgePair n) :=
  (Finset.univ.erase i).attach.map
    ⟨fun ⟨j, hj⟩ ↦ mkEdgePair i j (Finset.ne_of_mem_erase hj).symm, by
      rintro ⟨j₁, _⟩ ⟨j₂, _⟩ h
      exact Subtype.ext (Sym2.congr_right.mp (congr_arg Subtype.val h))⟩

private lemma card_incidentEdges {n : ℕ} (i : Fin n) :
    (incidentEdges i).card = n - 1 := by
  rw [incidentEdges, Finset.card_map, Finset.card_attach,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

private lemma mem_incidentEdges_iff {n : ℕ} (i : Fin n) (e : EdgePair n) :
    e ∈ incidentEdges i ↔ i ∈ e.1 := by
  constructor
  · rintro he
    rcases Finset.mem_map.mp he with ⟨⟨j, _⟩, -, rfl⟩
    exact Sym2.mem_mk_left i j
  · intro hi
    obtain ⟨j, hj_eq⟩ := Sym2.mem_iff_exists.mp hi
    have hij : i ≠ j := fun h ↦ e.2 (by rw [hj_eq, Sym2.mk_isDiag_iff]; exact h)
    refine Finset.mem_map.mpr ⟨⟨j, Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩⟩,
      Finset.mem_attach _ _, Subtype.ext hj_eq.symm⟩

private lemma incidentEdges_inter_eq_singleton {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    incidentEdges i ∩ incidentEdges j = {mkEdgePair i j h} := by
  ext e
  simp only [Finset.mem_inter, mem_incidentEdges_iff, Finset.mem_singleton, Subtype.ext_iff,
    mkEdgePair_val]
  exact Sym2.mem_and_mem_iff h

private lemma card_incidentEdges_union {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    (incidentEdges i ∪ incidentEdges j).card = 2 * n - 3 := by
  have hn2 : 2 ≤ n := two_le_of_ne h
  have hcard := Finset.card_union_add_card_inter (incidentEdges i) (incidentEdges j)
  rw [incidentEdges_inter_eq_singleton h, Finset.card_singleton,
    card_incidentEdges i, card_incidentEdges j] at hcard
  omega

private def incidentOther {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Finset (EdgePair n) :=
  (incidentEdges j).erase (mkEdgePair i j hij)

private lemma mem_incidentOther_iff {n : ℕ} {i j : Fin n} (hij : i ≠ j) (e : EdgePair n) :
    e ∈ incidentOther i j hij ↔ j ∈ e.1 ∧ i ∉ e.1 := by
  rw [incidentOther, Finset.mem_erase, mem_incidentEdges_iff]
  refine ⟨fun ⟨hne, hj⟩ ↦ ⟨hj, fun hi ↦
      hne (Subtype.ext ((Sym2.mem_and_mem_iff hij).mp ⟨hi, hj⟩))⟩,
    fun ⟨hj, hi⟩ ↦ ⟨fun h ↦ hi (h ▸ Sym2.mem_mk_left i j), hj⟩⟩

private lemma card_incidentOther {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (incidentOther i j hij).card = n - 2 := by
  have hn2 : 2 ≤ n := two_le_of_ne hij
  have hmem : mkEdgePair i j hij ∈ incidentEdges j :=
    (mem_incidentEdges_iff j _).mpr (Sym2.mem_mk_right i j)
  rw [incidentOther, Finset.card_erase_of_mem hmem, card_incidentEdges]
  omega

/-! ### Isolated-vertex moments (`SteinIntro.tex:1370-1379`) -/

private noncomputable def isolatedInd {n : ℕ} (i : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator (1 : SimpleGraph (Fin n) → ℝ) G

private lemma isIsolated_iff_incidentEdges {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    G.IsIsolated i ↔ ∀ e ∈ incidentEdges i, e.1 ∉ G.edgeSet := by
  rw [SimpleGraph.isIsolated_iff_forall_edgeSet_notMem]
  refine ⟨fun h e he heG ↦ h e.1 heG ((mem_incidentEdges_iff i e).mp he), fun h z hz hi ↦ ?_⟩
  have hnd : ¬ z.IsDiag := G.not_isDiag_of_mem_edgeSet hz
  exact h ⟨z, hnd⟩ ((mem_incidentEdges_iff i ⟨z, hnd⟩).mpr hi) hz

private lemma isIsolated_set_eq_cylinder {n : ℕ} (i : Fin n) :
    {G : SimpleGraph (Fin n) | G.IsIsolated i} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ incidentEdges i, e.1 ∉ G.edgeSet)} := by
  ext G
  simp only [Set.mem_ofPred_eq, isIsolated_iff_incidentEdges]
  exact ⟨fun h ↦ ⟨fun _ he ↦ False.elim (Finset.notMem_empty _ he), h⟩, fun ⟨_, h⟩ ↦ h⟩

private lemma isIsolated_inter_eq_cylinder {n : ℕ} (i j : Fin n) :
    {G : SimpleGraph (Fin n) | G.IsIsolated i} ∩
        {G : SimpleGraph (Fin n) | G.IsIsolated j} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ incidentEdges i ∪ incidentEdges j, e.1 ∉ G.edgeSet)} := by
  ext G
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, isIsolated_iff_incidentEdges, Finset.mem_union]
  exact ⟨fun ⟨hi, hj⟩ ↦ ⟨fun _ he ↦ False.elim (Finset.notMem_empty _ he),
      fun e he ↦ he.elim (hi e) (hj e)⟩,
    fun ⟨_, h⟩ ↦ ⟨fun e he ↦ h e (Or.inl he), fun e he ↦ h e (Or.inr he)⟩⟩

private lemma isolatedInd_integral {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin n) :
    ∫ G, isolatedInd i G ∂erdosRenyi n p = (1 - p) ^ (n - 1) := by
  unfold isolatedInd
  rw [integral_indicator_one_er, isIsolated_set_eq_cylinder,
    erdosRenyi_real_cylinder hp0 hp1 ∅ (incidentEdges i) (by simp),
    Finset.card_empty, pow_zero, one_mul, card_incidentEdges]

private lemma isolatedInd_mul_integral {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {i j : Fin n} (hij : i ≠ j) :
    ∫ G, isolatedInd i G * isolatedInd j G ∂erdosRenyi n p = (1 - p) ^ (2 * n - 3) := by
  simp_rw [isolatedInd, indicator_one_mul]
  rw [integral_indicator_one_er, isIsolated_inter_eq_cylinder,
    erdosRenyi_real_cylinder hp0 hp1 ∅ (incidentEdges i ∪ incidentEdges j) (by simp),
    Finset.card_empty, pow_zero, one_mul, card_incidentEdges_union hij]

/-- Expectation of the number of isolated vertices in $G(n, p)$
(Example 3.9, `SteinIntro.tex:1370-1373`): $\mathbb{E}[X] = n(1 - p)^{n - 1}$. -/
theorem isolatedCount_integral {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ G, (∑ i : Fin n,
      {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator
        (1 : SimpleGraph (Fin n) → ℝ) G) ∂erdosRenyi n p =
      (n : ℝ) * (1 - p) ^ (n - 1) := by
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun _ _ ↦ integrable_erdosRenyi _)]
  change (∑ i ∈ (Finset.univ : Finset (Fin n)), ∫ G, isolatedInd i G ∂erdosRenyi n p) = _
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ∫ G, isolatedInd i G ∂erdosRenyi n p = (1 - p) ^ (n - 1) :=
    fun i _ ↦ isolatedInd_integral hp0 hp1 i
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- Variance of the number of isolated vertices in $G(n, p)$ for $n \ge 2$
(Example 3.9, eq. `\label{77}`, `SteinIntro.tex:1374-1379`):
$\operatorname{Var}(X) = n(1 - p)^{n - 1}[1 + (n p - 1)(1 - p)^{n - 2}]$. -/
theorem isolatedCount_variance {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 2 ≤ n) :
    ProbabilityTheory.variance
      (fun G : SimpleGraph (Fin n) ↦
        ∑ i : Fin n,
          {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator
            (1 : SimpleGraph (Fin n) → ℝ) G)
      (erdosRenyi n p) =
      (n : ℝ) * (1 - p) ^ (n - 1) * (1 + ((n : ℝ) * p - 1) * (1 - p) ^ (n - 2)) := by
  let X : SimpleGraph (Fin n) → ℝ := fun G ↦ ∑ i : Fin n, isolatedInd i G
  change ProbabilityTheory.variance X (erdosRenyi n p) = _
  rw [variance_erdosRenyi_eq]
  have hX_int : ∫ G, X G ∂erdosRenyi n p = (n : ℝ) * (1 - p) ^ (n - 1) :=
    isolatedCount_integral hp0 hp1
  have hsq : (fun G ↦ X G ^ 2) = fun G ↦
      X G + ∑ x ∈ (Finset.univ : Finset (Fin n)).offDiag,
        isolatedInd x.1 G * isolatedInd x.2 G := by
    ext G
    dsimp only [X]
    rw [sq_sum_eq_diag_add_offDiag]
    exact congr_arg₂ (· + ·) (Finset.sum_congr rfl fun _ _ ↦ indicator_one_sq _ G) rfl
  rw [hsq, MeasureTheory.integral_add (integrable_erdosRenyi _) (integrable_erdosRenyi _),
    hX_int, MeasureTheory.integral_finsetSum Finset.univ.offDiag
      (fun _ _ ↦ integrable_erdosRenyi _)]
  have hoff : ∀ x ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ∫ G, isolatedInd x.1 G * isolatedInd x.2 G ∂erdosRenyi n p = (1 - p) ^ (2 * n - 3) :=
    fun x hx ↦ isolatedInd_mul_integral hp0 hp1 (Finset.mem_offDiag.mp hx).2.2
  rw [Finset.sum_congr rfl hoff, Finset.sum_const, Finset.offDiag_card,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hcard : (m + 2) * (m + 2) - (m + 2) = (m + 2) * (m + 1) := by
    rw [show (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) by ring, Nat.add_sub_cancel]
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    show 2 * (m + 2) - 3 = m + m + 1 by omega, hcard,
    pow_add (1 - p) m 1, pow_add (1 - p) (m + m) 1, pow_add (1 - p) m m, pow_one]
  push_cast
  ring

/-! ### Degree-one neighbor events and second moment (`SteinIntro.tex:1406-1409`) -/

private noncomputable def degOneAdjInd {n : ℕ} (i j : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | H.Adj i j ∧ (H.neighborSet j).ncard = 1}.indicator
    (1 : SimpleGraph (Fin n) → ℝ) G

private noncomputable def degOneInd {n : ℕ} (j : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | (H.neighborSet j).ncard = 1}.indicator
    (1 : SimpleGraph (Fin n) → ℝ) G

private lemma degOneAdjInd_of_true {n : ℕ} {i j : Fin n} {G : SimpleGraph (Fin n)}
    (h : G.Adj i j ∧ (G.neighborSet j).ncard = 1) : degOneAdjInd i j G = 1 := by
  unfold degOneAdjInd; exact Set.indicator_of_mem h 1

private lemma degOneAdjInd_of_false {n : ℕ} {i j : Fin n} {G : SimpleGraph (Fin n)}
    (h : ¬ (G.Adj i j ∧ (G.neighborSet j).ncard = 1)) : degOneAdjInd i j G = 0 := by
  unfold degOneAdjInd; exact Set.indicator_of_notMem h 1

private lemma degOneInd_of_true {n : ℕ} {j : Fin n} {G : SimpleGraph (Fin n)}
    (h : (G.neighborSet j).ncard = 1) : degOneInd j G = 1 := by
  unfold degOneInd; exact Set.indicator_of_mem h 1

private lemma degOneInd_of_false {n : ℕ} {j : Fin n} {G : SimpleGraph (Fin n)}
    (h : ¬ (G.neighborSet j).ncard = 1) : degOneInd j G = 0 := by
  unfold degOneInd; exact Set.indicator_of_notMem h 1

private lemma adj_and_ncard_neighborSet_eq_one_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) :
    G.Adj i j ∧ (G.neighborSet j).ncard = 1 ↔ G.neighborSet j = {i} := by
  constructor
  · rintro ⟨hadj, hcard⟩
    obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp hcard
    have hi : i ∈ G.neighborSet j := (G.mem_neighborSet j i).mpr hadj.symm
    rw [hu, Set.mem_singleton_iff] at hi
    rw [hu, hi]
  · intro h
    have hi : i ∈ G.neighborSet j := h ▸ Set.mem_singleton i
    exact ⟨((G.mem_neighborSet j i).mp hi).symm, by rw [h, Set.ncard_singleton]⟩

private lemma neighborSet_eq_singleton_iff_cylinder {n : ℕ} {G : SimpleGraph (Fin n)}
    {i j : Fin n} (hij : i ≠ j) :
    G.neighborSet j = {i} ↔
      (mkEdgePair i j hij).1 ∈ G.edgeSet ∧ ∀ e ∈ incidentOther i j hij, e.1 ∉ G.edgeSet := by
  constructor
  · intro h
    have hadj_ji : G.Adj j i := (G.mem_neighborSet j i).mp (h ▸ Set.mem_singleton i)
    refine ⟨G.mem_edgeSet.mpr hadj_ji.symm, fun e he heG ↦ ?_⟩
    obtain ⟨hj_mem, hi_notMem⟩ := (mem_incidentOther_iff hij e).mp he
    obtain ⟨w, hw_eq⟩ := Sym2.mem_iff_exists.mp hj_mem
    have hjw : G.Adj j w := G.mem_edgeSet.mp (hw_eq ▸ heG)
    have hw_eq_i : w = i := Set.mem_singleton_iff.mp (h ▸ (G.mem_neighborSet j w).mpr hjw)
    exact hi_notMem (by rw [hw_eq, hw_eq_i]; exact Sym2.mem_mk_right j i)
  · rintro ⟨hpos, hneg⟩
    have hadj_ij : G.Adj i j := G.mem_edgeSet.mp hpos
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_singleton_iff]
    refine ⟨fun hjw ↦ ?_, fun hw ↦ hw ▸ hadj_ij.symm⟩
    by_contra hwi
    have hwj : w ≠ j := G.ne_of_adj hjw.symm
    have hi_not : i ∉ (mkEdgePair w j hwj).1 := by
      rw [mkEdgePair_val, Sym2.mem_iff]
      rintro (rfl | rfl) <;> [exact hwi rfl; exact hij rfl]
    exact hneg _ ((mem_incidentOther_iff hij _).mpr ⟨Sym2.mem_mk_right w j, hi_not⟩)
      (G.mem_edgeSet.mpr hjw.symm)

private lemma degOneAdj_set_eq_cylinder {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    {G : SimpleGraph (Fin n) | G.Adj i j ∧ (G.neighborSet j).ncard = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ ({mkEdgePair i j hij} : Finset (EdgePair n)), e.1 ∈ G.edgeSet) ∧
          (∀ e ∈ incidentOther i j hij, e.1 ∉ G.edgeSet)} := by
  ext G
  simp only [Set.mem_ofPred_eq, adj_and_ncard_neighborSet_eq_one_iff,
    neighborSet_eq_singleton_iff_cylinder hij, Finset.mem_singleton]
  exact ⟨fun ⟨hp, hn⟩ ↦ ⟨fun _ h ↦ h ▸ hp, hn⟩, fun ⟨hp, hn⟩ ↦ ⟨hp _ rfl, hn⟩⟩

private lemma degOneAdjInd_integral {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {i j : Fin n} (hij : i ≠ j) :
    ∫ G, degOneAdjInd i j G ∂erdosRenyi n p = p * (1 - p) ^ (n - 2) := by
  have hdisj : Disjoint ({mkEdgePair i j hij} : Finset (EdgePair n))
      (incidentOther i j hij) :=
    Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _)
  unfold degOneAdjInd
  rw [integral_indicator_one_er, degOneAdj_set_eq_cylinder hij,
    erdosRenyi_real_cylinder hp0 hp1 _ _ hdisj,
    Finset.card_singleton, pow_one, card_incidentOther hij]

private lemma incidentOther_inter_eq_singleton {n : ℕ} {j k u v : Fin n}
    (hjk : j ≠ k) (huj : u ≠ j) (huk : u ≠ k) (hvk : v ≠ k) (hvj : v ≠ j) :
    incidentOther u j huj ∩ incidentOther v k hvk = {mkEdgePair j k hjk} := by
  ext e
  simp only [Finset.mem_inter, mem_incidentOther_iff, Finset.mem_singleton, Subtype.ext_iff,
    mkEdgePair_val]
  refine ⟨fun ⟨⟨hj, _⟩, ⟨hk, _⟩⟩ ↦ (Sym2.mem_and_mem_iff hjk).mp ⟨hj, hk⟩, fun heq ↦ ?_⟩
  rw [heq]
  refine ⟨⟨Sym2.mem_mk_left j k, ?_⟩, ⟨Sym2.mem_mk_right j k, ?_⟩⟩ <;> rw [Sym2.mem_iff]
  · rintro (rfl | rfl) <;> [exact huj rfl; exact huk rfl]
  · rintro (rfl | rfl) <;> [exact hvj rfl; exact hvk rfl]

private lemma degOneAdjInd_mul_integral_of_ne {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {j k u v : Fin n} (hjk : j ≠ k) (huj : u ≠ j) (huk : u ≠ k) (hvk : v ≠ k) (hvj : v ≠ j) :
    ∫ G, degOneAdjInd u j G * degOneAdjInd v k G ∂erdosRenyi n p =
      p ^ 2 * (1 - p) ^ (2 * n - 5) := by
  have hn3 : 3 ≤ n := three_le_of_pairwise_ne huj huk hjk
  let e₁ : EdgePair n := mkEdgePair u j huj
  let e₂ : EdgePair n := mkEdgePair v k hvk
  let S_pos : Finset (EdgePair n) := {e₁, e₂}
  let S_neg : Finset (EdgePair n) := incidentOther u j huj ∪ incidentOther v k hvk
  have he12 : e₁ ≠ e₂ := by
    intro h
    rcases Sym2.mem_iff.mp (h ▸ Sym2.mem_mk_right u j : j ∈ e₂.1) with rfl | rfl
    · exact hvj rfl
    · exact hjk rfl
  have hdisj : Disjoint S_pos S_neg := by
    rw [Finset.disjoint_left]
    intro e he_pos he_neg
    rcases Finset.mem_insert.mp he_pos with rfl | he_pos'
    · rcases Finset.mem_union.mp he_neg with he_neg1 | he_neg2
      · exact ((mem_incidentOther_iff huj e₁).mp he_neg1).2 (Sym2.mem_mk_left u j)
      · rcases Sym2.mem_iff.mp ((mem_incidentOther_iff hvk e₁).mp he_neg2).1 with rfl | rfl
        · exact huk rfl
        · exact hjk rfl
    · rw [Finset.mem_singleton.mp he_pos'] at he_neg
      rcases Finset.mem_union.mp he_neg with he_neg1 | he_neg2
      · rcases Sym2.mem_iff.mp ((mem_incidentOther_iff huj e₂).mp he_neg1).1 with rfl | rfl
        · exact hvj rfl
        · exact hjk rfl
      · exact ((mem_incidentOther_iff hvk e₂).mp he_neg2).2 (Sym2.mem_mk_left v k)
  have hset : {G : SimpleGraph (Fin n) | G.Adj u j ∧ (G.neighborSet j).ncard = 1} ∩
        {G : SimpleGraph (Fin n) | G.Adj v k ∧ (G.neighborSet k).ncard = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ S_pos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ S_neg, e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, adj_and_ncard_neighborSet_eq_one_iff,
      neighborSet_eq_singleton_iff_cylinder huj, neighborSet_eq_singleton_iff_cylinder hvk,
      S_pos, S_neg, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    exact ⟨fun ⟨⟨h1, hn1⟩, ⟨h2, hn2⟩⟩ ↦
        ⟨fun e he ↦ he.elim (fun h ↦ h ▸ h1) (fun h ↦ h ▸ h2),
          fun e he ↦ he.elim (hn1 e) (hn2 e)⟩,
      fun ⟨hp_all, hn_all⟩ ↦
        ⟨⟨hp_all e₁ (Or.inl rfl), fun e he ↦ hn_all e (Or.inl he)⟩,
          ⟨hp_all e₂ (Or.inr rfl), fun e he ↦ hn_all e (Or.inr he)⟩⟩⟩
  have hcard_neg : S_neg.card = 2 * n - 5 := by
    have hcard := Finset.card_union_add_card_inter (incidentOther u j huj) (incidentOther v k hvk)
    rw [incidentOther_inter_eq_singleton hjk huj huk hvk hvj, Finset.card_singleton,
      card_incidentOther huj, card_incidentOther hvk] at hcard
    dsimp only [S_neg]
    omega
  simp_rw [degOneAdjInd, indicator_one_mul]
  rw [integral_indicator_one_er, hset, erdosRenyi_real_cylinder hp0 hp1 S_pos S_neg hdisj,
    Finset.card_pair he12, hcard_neg]

private lemma degOneNeighbor_eq_sum {n : ℕ} (i : Fin n) (G : SimpleGraph (Fin n)) :
    ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ) =
      ∑ j : Fin n, degOneAdjInd i j G := by
  classical
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun j ↦ G.Adj i j ∧ (G.neighborSet j).ncard = 1)
  have hs : (s : Set (Fin n)) = {j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1} := by
    ext j; simp [s]
  rw [← hs, Set.ncard_coe_finset]
  dsimp only [s]
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : G.Adj i j ∧ (G.neighborSet j).ncard = 1
  · rw [ite_eq_left h, degOneAdjInd_of_true h]
  · rw [ite_eq_right h, degOneAdjInd_of_false h]

private lemma degOneNeighbor_eq_sum_erase {n : ℕ} (i : Fin n) (G : SimpleGraph (Fin n)) :
    ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ) =
      ∑ j ∈ Finset.univ.erase i, degOneAdjInd i j G := by
  rw [degOneNeighbor_eq_sum]
  have hii : degOneAdjInd i i G = 0 := degOneAdjInd_of_false fun h ↦ G.ne_of_adj h.1 rfl
  exact (Finset.sum_erase Finset.univ (f := fun j ↦ degOneAdjInd i j G) hii).symm

/-- Second moment of $D_i$, the number of degree-one neighbors of vertex $i$ in $G(n, p)$, for
$n \ge 3$ (Example 3.9, `SteinIntro.tex:1406-1409`):
$\mathbb{E}[D_i^2] = (n - 1)p(1 - p)^{n - 2} + (n - 1)(n - 2)p^2(1 - p)^{2n - 5}$. -/
theorem degOneNeighbor_sq_integral {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 3 ≤ n) (i : Fin n) :
    ∫ G, (({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ)) ^ 2
      ∂erdosRenyi n p =
      ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) +
        ((n : ℝ) - 1) * ((n : ℝ) - 2) * p ^ 2 * (1 - p) ^ (2 * n - 5) := by
  let S : Finset (Fin n) := Finset.univ.erase i
  have hfun : (fun G : SimpleGraph (Fin n) ↦
        (({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ)) ^ 2) =
      fun G ↦ (∑ j ∈ S, degOneAdjInd i j G) +
        ∑ x ∈ S.offDiag, degOneAdjInd i x.1 G * degOneAdjInd i x.2 G := by
    ext G
    rw [degOneNeighbor_eq_sum_erase, sq_sum_eq_diag_add_offDiag]
    exact congr_arg₂ (· + ·) (Finset.sum_congr rfl fun _ _ ↦ indicator_one_sq _ G) rfl
  rw [hfun, MeasureTheory.integral_add (integrable_erdosRenyi _) (integrable_erdosRenyi _),
    MeasureTheory.integral_finsetSum S (fun _ _ ↦ integrable_erdosRenyi _),
    MeasureTheory.integral_finsetSum S.offDiag (fun _ _ ↦ integrable_erdosRenyi _)]
  have hdiag : ∀ j ∈ S,
      ∫ G, degOneAdjInd i j G ∂erdosRenyi n p = p * (1 - p) ^ (n - 2) :=
    fun j hj ↦ degOneAdjInd_integral hp0 hp1 (Finset.ne_of_mem_erase hj).symm
  have hoff : ∀ x ∈ S.offDiag,
      ∫ G, degOneAdjInd i x.1 G * degOneAdjInd i x.2 G ∂erdosRenyi n p =
        p ^ 2 * (1 - p) ^ (2 * n - 5) := by
    intro x hx
    rcases Finset.mem_offDiag.mp hx with ⟨hx1, hx2, hne⟩
    exact degOneAdjInd_mul_integral_of_ne hp0 hp1 hne
      (Finset.ne_of_mem_erase hx1).symm (Finset.ne_of_mem_erase hx2).symm
      (Finset.ne_of_mem_erase hx2).symm (Finset.ne_of_mem_erase hx1).symm
  have hScard : S.card = n - 1 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_congr rfl hdiag, Finset.sum_const, hScard, nsmul_eq_mul,
    Finset.sum_congr rfl hoff, Finset.sum_const, Finset.offDiag_card, hScard, nsmul_eq_mul]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hcard : (m + 2) * (m + 2) - (m + 2) = (m + 2) * (m + 1) := by
    rw [show (m + 2) * (m + 2) = (m + 2) * (m + 1) + (m + 2) by ring, Nat.add_sub_cancel]
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show 2 * (m + 3) - 5 = 2 * m + 1 by omega, hcard]
  push_cast
  ring

/-- Proof of all four verified moment identities in Example 3.9 (`Ex3_9_moments`,
`SteinIntro.tex:1370-1379, 1406-1409`). -/
theorem Ex3_9_moments_proof : Ex3_9_moments := by
  intro n p hp0 hp1
  exact ⟨isolatedCount_integral hp0 hp1,
    fun _ _ hij ↦ isolatedInd_mul_integral hp0 hp1 hij,
    fun hn ↦ isolatedCount_variance hp0 hp1 hn,
    fun hn i ↦ degOneNeighbor_sq_integral hp0 hp1 hn i⟩

/-! ### Degree-one sum identity, exact pair moment, and variance upper bound -/

private lemma degOneInd_eq_sum_erase {n : ℕ} (j : Fin n) (G : SimpleGraph (Fin n)) :
    degOneInd j G = ∑ u ∈ Finset.univ.erase j, degOneAdjInd u j G := by
  by_cases hdeg : (G.neighborSet j).ncard = 1
  · obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hdeg
    have hjw : G.Adj j w := (G.mem_neighborSet j w).mp (hw ▸ Set.mem_singleton w)
    have hw_erase : w ∈ Finset.univ.erase j :=
      Finset.mem_erase.mpr ⟨G.ne_of_adj hjw.symm, Finset.mem_univ w⟩
    rw [degOneInd_of_true hdeg]
    symm
    rw [Finset.sum_eq_single_of_mem w hw_erase]
    · exact degOneAdjInd_of_true ⟨hjw.symm, hdeg⟩
    · intro u _ huw
      refine degOneAdjInd_of_false ?_
      rw [adj_and_ncard_neighborSet_eq_one_iff, hw]
      exact fun hset ↦ huw (Set.mem_singleton_iff.mp (hset ▸ Set.mem_singleton u))
  · rw [degOneInd_of_false hdeg]
    symm
    exact Finset.sum_eq_zero fun u _ ↦ degOneAdjInd_of_false fun h ↦ hdeg h.2

/-- Summing $D_i$ (the number of degree-one neighbors of $i$) over all vertices $i$ equals the
total number of degree-one vertices $\sum_j Y_j$ (`SteinIntro.tex:1393-1395`). -/
theorem sum_degOneNeighbor_eq_sum_degOne (n : ℕ) (G : SimpleGraph (Fin n)) :
    (∑ i : Fin n, ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ)) =
      ∑ j : Fin n,
        {H : SimpleGraph (Fin n) | (H.neighborSet j).ncard = 1}.indicator
          (1 : SimpleGraph (Fin n) → ℝ) G := by
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ) =
        ∑ j : Fin n, degOneAdjInd i j G :=
    fun i _ ↦ degOneNeighbor_eq_sum i G
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hjj : degOneAdjInd j j G = 0 := degOneAdjInd_of_false fun h ↦ G.ne_of_adj h.1 rfl
  rw [← Finset.sum_erase Finset.univ (f := fun i ↦ degOneAdjInd i j G) hjj,
    ← degOneInd_eq_sum_erase]
  rfl

private lemma degOneInd_integral {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : Fin n) :
    ∫ G, degOneInd j G ∂erdosRenyi n p = ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) := by
  have h1 : 1 ≤ n := Nat.one_le_of_lt j.2
  simp_rw [degOneInd_eq_sum_erase j]
  rw [MeasureTheory.integral_finsetSum _ (fun _ _ ↦ integrable_erdosRenyi _)]
  have hterm : ∀ u ∈ (Finset.univ : Finset (Fin n)).erase j,
      ∫ G, degOneAdjInd u j G ∂erdosRenyi n p = p * (1 - p) ^ (n - 2) :=
    fun u hu ↦ degOneAdjInd_integral hp0 hp1 (Finset.ne_of_mem_erase hu)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub h1, Nat.cast_one, mul_assoc]

private lemma degOneAdjInd_mul_eq_zero_of_ne {n : ℕ} {j k v : Fin n}
    (hvj : v ≠ j) (G : SimpleGraph (Fin n)) :
    degOneAdjInd k j G * degOneAdjInd v k G = 0 := by
  by_cases h1 : G.Adj k j ∧ (G.neighborSet j).ncard = 1
  · by_cases h2 : G.Adj v k ∧ (G.neighborSet k).ncard = 1
    · exfalso
      have hset : G.neighborSet k = {v} := (adj_and_ncard_neighborSet_eq_one_iff G v k).mp h2
      have hj_mem : j ∈ G.neighborSet k := (G.mem_neighborSet k j).mpr h1.1
      exact hvj (Set.mem_singleton_iff.mp (hset ▸ hj_mem)).symm
    · rw [degOneAdjInd_of_false h2, mul_zero]
  · rw [degOneAdjInd_of_false h1, zero_mul]

private lemma degOneAdjInd_mul_integral_adj {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {j k : Fin n} (hjk : j ≠ k) :
    ∫ G, degOneAdjInd k j G * degOneAdjInd j k G ∂erdosRenyi n p =
      p * (1 - p) ^ (2 * n - 4) := by
  have hn2 : 2 ≤ n := two_le_of_ne hjk
  let e₀ : EdgePair n := mkEdgePair j k hjk
  let S_pos : Finset (EdgePair n) := {e₀}
  let S_neg : Finset (EdgePair n) := incidentOther k j hjk.symm ∪ incidentOther j k hjk
  have hdisj_neg : Disjoint (incidentOther k j hjk.symm) (incidentOther j k hjk) :=
    Finset.disjoint_left.mpr fun e he1 he2 ↦
      ((mem_incidentOther_iff hjk.symm e).mp he1).2 ((mem_incidentOther_iff hjk e).mp he2).1
  have hdisj : Disjoint S_pos S_neg := by
    rw [Finset.disjoint_singleton_left, Finset.mem_union]
    rintro (he1 | he2)
    · exact ((mem_incidentOther_iff hjk.symm e₀).mp he1).2 (Sym2.mem_mk_right j k)
    · exact ((mem_incidentOther_iff hjk e₀).mp he2).2 (Sym2.mem_mk_left j k)
  have hcomm : (mkEdgePair k j hjk.symm).1 = e₀.1 := congr_arg Subtype.val (mkEdgePair_comm k j _)
  have hset : {G : SimpleGraph (Fin n) | G.Adj k j ∧ (G.neighborSet j).ncard = 1} ∩
        {G : SimpleGraph (Fin n) | G.Adj j k ∧ (G.neighborSet k).ncard = 1} =
      {G : SimpleGraph (Fin n) |
        (∀ e ∈ S_pos, e.1 ∈ G.edgeSet) ∧ (∀ e ∈ S_neg, e.1 ∉ G.edgeSet)} := by
    ext G
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, adj_and_ncard_neighborSet_eq_one_iff,
      neighborSet_eq_singleton_iff_cylinder hjk.symm, neighborSet_eq_singleton_iff_cylinder hjk,
      S_pos, S_neg, Finset.mem_singleton, Finset.mem_union]
    exact ⟨fun ⟨⟨_, hn1⟩, ⟨hp2, hn2_neg⟩⟩ ↦
        ⟨fun _ h ↦ h ▸ hp2, fun e he ↦ he.elim (hn1 e) (hn2_neg e)⟩,
      fun ⟨hp, hn_all⟩ ↦
        ⟨⟨hcomm.symm ▸ hp e₀ rfl, fun e he ↦ hn_all e (Or.inl he)⟩,
          ⟨hp e₀ rfl, fun e he ↦ hn_all e (Or.inr he)⟩⟩⟩
  have hcard_neg : S_neg.card = 2 * n - 4 := by
    dsimp only [S_neg]
    rw [Finset.card_union_of_disjoint hdisj_neg, card_incidentOther hjk.symm,
      card_incidentOther hjk]
    omega
  simp_rw [degOneAdjInd, indicator_one_mul]
  rw [integral_indicator_one_er, hset, erdosRenyi_real_cylinder hp0 hp1 S_pos S_neg hdisj,
    Finset.card_singleton, pow_one, hcard_neg]

/-- Exact joint expectation $\mathbb{E}[Y_j Y_k]$ for distinct vertices $j \ne k$ ($n \ge 3$),
correcting the typo $(n - 1)^2$ in `SteinIntro.tex:1397` (`ISSUE-3.9`) to $(n - 2)^2$. -/
private lemma degOneInd_mul_integral {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 3 ≤ n) {j k : Fin n} (hjk : j ≠ k) :
    ∫ G, degOneInd j G * degOneInd k G ∂erdosRenyi n p =
      p * (1 - p) ^ (2 * n - 4) + ((n : ℝ) - 2) ^ 2 * p ^ 2 * (1 - p) ^ (2 * n - 5) := by
  let U : Finset (Fin n) := (Finset.univ.erase j).erase k
  let V : Finset (Fin n) := (Finset.univ.erase k).erase j
  have hk_mem : k ∈ (Finset.univ : Finset (Fin n)).erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_univ k⟩
  have hj_mem : j ∈ (Finset.univ : Finset (Fin n)).erase k :=
    Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩
  have hdecomp : (fun G ↦ degOneInd j G * degOneInd k G) =
      fun G ↦ degOneAdjInd k j G * degOneAdjInd j k G +
        ∑ u ∈ U, ∑ v ∈ V, degOneAdjInd u j G * degOneAdjInd v k G := by
    ext G
    rw [degOneInd_eq_sum_erase j G, degOneInd_eq_sum_erase k G,
      ← Finset.add_sum_erase _ _ hk_mem, ← Finset.add_sum_erase _ _ hj_mem]
    change (degOneAdjInd k j G + ∑ u ∈ U, degOneAdjInd u j G) *
        (degOneAdjInd j k G + ∑ v ∈ V, degOneAdjInd v k G) = _
    have hcross1 : degOneAdjInd k j G * ∑ v ∈ V, degOneAdjInd v k G = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun v hv ↦
        degOneAdjInd_mul_eq_zero_of_ne (Finset.ne_of_mem_erase hv) G
    have hcross2 : (∑ u ∈ U, degOneAdjInd u j G) * degOneAdjInd j k G = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun u hu ↦ ?_
      rw [mul_comm]
      exact degOneAdjInd_mul_eq_zero_of_ne (Finset.ne_of_mem_erase hu) G
    rw [add_mul, mul_add, mul_add, hcross1, hcross2, Finset.sum_mul_sum]
    ring
  rw [hdecomp, MeasureTheory.integral_add (integrable_erdosRenyi _) (integrable_erdosRenyi _),
    degOneAdjInd_mul_integral_adj hp0 hp1 hjk,
    MeasureTheory.integral_finsetSum U (fun _ _ ↦ integrable_erdosRenyi _)]
  have hinner : ∀ u ∈ U,
      ∫ G, (∑ v ∈ V, degOneAdjInd u j G * degOneAdjInd v k G) ∂erdosRenyi n p =
        ((n : ℝ) - 2) * (p ^ 2 * (1 - p) ^ (2 * n - 5)) := by
    intro u hu
    rw [MeasureTheory.integral_finsetSum V (fun _ _ ↦ integrable_erdosRenyi _)]
    have huk : u ≠ k := Finset.ne_of_mem_erase hu
    have huj : u ≠ j := Finset.ne_of_mem_erase (Finset.erase_subset k _ hu)
    have hv_term : ∀ v ∈ V,
        ∫ G, degOneAdjInd u j G * degOneAdjInd v k G ∂erdosRenyi n p =
          p ^ 2 * (1 - p) ^ (2 * n - 5) :=
      fun v hv ↦ degOneAdjInd_mul_integral_of_ne hp0 hp1 hjk huj huk
        (Finset.ne_of_mem_erase (Finset.erase_subset j _ hv)) (Finset.ne_of_mem_erase hv)
    have hVcard : V.card = n - 2 := by
      dsimp only [V]
      rw [Finset.card_erase_of_mem hj_mem, Finset.card_erase_of_mem (Finset.mem_univ k),
        Finset.card_univ, Fintype.card_fin]
      omega
    rw [Finset.sum_congr rfl hv_term, Finset.sum_const, hVcard, nsmul_eq_mul,
      Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  have hUcard : U.card = n - 2 := by
    dsimp only [U]
    rw [Finset.card_erase_of_mem hk_mem, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, hUcard, nsmul_eq_mul,
    Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_ofNat]
  ring

private lemma sum_degOne_variance {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 3 ≤ n) :
    ProbabilityTheory.variance
      (fun G : SimpleGraph (Fin n) ↦ ∑ j : Fin n, degOneInd j G)
      (erdosRenyi n p) =
      (n : ℝ) * ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) +
        (n : ℝ) * ((n : ℝ) - 1) *
          (p * (1 - p) ^ (2 * n - 4) + ((n : ℝ) - 2) ^ 2 * p ^ 2 * (1 - p) ^ (2 * n - 5)) -
        ((n : ℝ) * ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2)) ^ 2 := by
  let S_rv : SimpleGraph (Fin n) → ℝ := fun G ↦ ∑ j : Fin n, degOneInd j G
  change ProbabilityTheory.variance S_rv (erdosRenyi n p) = _
  rw [variance_erdosRenyi_eq]
  have hmean : ∫ G, S_rv G ∂erdosRenyi n p =
      (n : ℝ) * ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) := by
    dsimp only [S_rv]
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun _ _ ↦ integrable_erdosRenyi _)]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        ∫ G, degOneInd j G ∂erdosRenyi n p = ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) :=
      fun j _ ↦ degOneInd_integral hp0 hp1 j
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hsq : (fun G ↦ S_rv G ^ 2) = fun G ↦
      S_rv G + ∑ x ∈ (Finset.univ : Finset (Fin n)).offDiag,
        degOneInd x.1 G * degOneInd x.2 G := by
    ext G
    dsimp only [S_rv]
    rw [sq_sum_eq_diag_add_offDiag]
    exact congr_arg₂ (· + ·) (Finset.sum_congr rfl fun _ _ ↦ indicator_one_sq _ G) rfl
  rw [hsq, MeasureTheory.integral_add (integrable_erdosRenyi _) (integrable_erdosRenyi _),
    hmean, MeasureTheory.integral_finsetSum Finset.univ.offDiag
      (fun _ _ ↦ integrable_erdosRenyi _)]
  have hoff : ∀ x ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ∫ G, degOneInd x.1 G * degOneInd x.2 G ∂erdosRenyi n p =
        p * (1 - p) ^ (2 * n - 4) + ((n : ℝ) - 2) ^ 2 * p ^ 2 * (1 - p) ^ (2 * n - 5) :=
    fun x hx ↦ degOneInd_mul_integral hp0 hp1 hn (Finset.mem_offDiag.mp hx).2.2
  rw [Finset.sum_congr rfl hoff, Finset.sum_const, Finset.offDiag_card,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hcard : (m + 3) * (m + 3) - (m + 3) = (m + 3) * (m + 2) := by
    rw [show (m + 3) * (m + 3) = (m + 3) * (m + 2) + (m + 3) by ring, Nat.add_sub_cancel]
  rw [hcard]
  push_cast
  ring

/-- Polynomial variance upper bound $\operatorname{Var}(\sum_i D_i) \le 2 n^2 p + n^4 p^3$ for
$n \ge 3$ and $0 \le p \le 1$, replacing the false printed intermediate expression at
`SteinIntro.tex:1395` (`ISSUE-3.9`) in the proof of Theorem 3.17. -/
theorem sum_degOneNeighbor_variance_le {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hn : 3 ≤ n) :
    ProbabilityTheory.variance
      (fun G : SimpleGraph (Fin n) ↦
        ∑ i : Fin n, ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ))
      (erdosRenyi n p) ≤
      2 * (n : ℝ) ^ 2 * p + (n : ℝ) ^ 4 * p ^ 3 := by
  simp_rw [sum_degOneNeighbor_eq_sum_degOne n]
  change ProbabilityTheory.variance (fun G ↦ ∑ j : Fin n, degOneInd j G) (erdosRenyi n p) ≤ _
  rw [sum_degOne_variance hp0 hp1 hn]
  set N : ℝ := (n : ℝ)
  set u : ℝ := (1 - p) ^ (n - 2)
  set w : ℝ := (1 - p) ^ (2 * n - 4)
  set v : ℝ := (1 - p) ^ (2 * n - 5)
  have hN3 : (3 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hn
  have hN0 : 0 ≤ N := by linarith
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hu0 : 0 ≤ u := pow_nonneg hq0 _
  have hu1 : u ≤ 1 := pow_le_one_real hq0 hq1 _
  have hw0 : 0 ≤ w := pow_nonneg hq0 _
  have hw1 : w ≤ 1 := pow_le_one_real hq0 hq1 _
  have hv0 : 0 ≤ v := pow_nonneg hq0 _
  have hv1 : v ≤ 1 := pow_le_one_real hq0 hq1 _
  have hb1 : N * (N - 1) * p * u ≤ N ^ 2 * p := sub_nonneg.mp <| by
    rw [show N ^ 2 * p - N * (N - 1) * p * u = N ^ 2 * p * (1 - u) + N * p * u by ring]
    exact add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg N) hp0) (sub_nonneg.mpr hu1))
      (mul_nonneg (mul_nonneg hN0 hp0) hu0)
  have hb2 : N * (N - 1) * (p * w) ≤ N ^ 2 * p := sub_nonneg.mp <| by
    rw [show N ^ 2 * p - N * (N - 1) * (p * w) = N ^ 2 * p * (1 - w) + N * p * w by ring]
    exact add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg N) hp0) (sub_nonneg.mpr hw1))
      (mul_nonneg (mul_nonneg hN0 hp0) hw0)
  have hpow : u ^ 2 = v * (1 - p) := by
    dsimp only [u, v]
    rw [sq, ← pow_add, show (n - 2) + (n - 2) = (2 * n - 5) + 1 by omega, pow_add, pow_one]
  have hb3 : N * (N - 1) * ((N - 2) ^ 2 * p ^ 2 * v) - (N * (N - 1) * p * u) ^ 2 ≤
      N ^ 4 * p ^ 3 := by
    rw [show (N * (N - 1) * p * u) ^ 2 = N ^ 2 * (N - 1) ^ 2 * p ^ 2 * u ^ 2 by ring, hpow]
    refine sub_nonneg.mp ?_
    rw [show N ^ 4 * p ^ 3 - (N * (N - 1) * ((N - 2) ^ 2 * p ^ 2 * v) -
          N ^ 2 * (N - 1) ^ 2 * p ^ 2 * (v * (1 - p))) =
        N * (N - 1) * (3 * N - 4) * p ^ 2 * v + N ^ 4 * p ^ 3 * (1 - v) +
          N ^ 2 * (2 * N - 1) * p ^ 3 * v by ring]
    exact add_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hN0 (by linarith)) (by linarith))
        (sq_nonneg p)) hv0)
      (mul_nonneg (mul_nonneg (pow_nonneg hN0 4) (pow_nonneg hp0 3)) (sub_nonneg.mpr hv1)))
      (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg N) (by linarith)) (pow_nonneg hp0 3)) hv0)
  calc N * (N - 1) * p * u + N * (N - 1) * (p * w + (N - 2) ^ 2 * p ^ 2 * v) -
        (N * (N - 1) * p * u) ^ 2
      = (N * (N - 1) * p * u) + (N * (N - 1) * (p * w)) +
          (N * (N - 1) * ((N - 2) ^ 2 * p ^ 2 * v) - (N * (N - 1) * p * u) ^ 2) := by ring
    _ ≤ N ^ 2 * p + N ^ 2 * p + N ^ 4 * p ^ 3 := add_le_add (add_le_add hb1 hb2) hb3
    _ = 2 * N ^ 2 * p + N ^ 4 * p ^ 3 := by ring

/-! ### Machine-checked counterexamples at $n = 3, p = 1/2$ (`ISSUE-3.9`) -/

/-- Counterexample at $n = 3, p = 1/2$ to the false printed joint-degree-one expectation formula at
`SteinIntro.tex:1397` (`ISSUE-3.9`): the true value is $\mathbb{E}[Y_0 Y_1] = 1/4$, whereas the
printed expression evaluates to $5/8$. -/
theorem Ex3_9_L1397_counterexample :
    let Y : Fin 3 → SimpleGraph (Fin 3) → ℝ :=
      fun i G ↦ {H : SimpleGraph (Fin 3) | (H.neighborSet i).ncard = 1}.indicator 1 G
    ∫ G, Y 0 G * Y 1 G ∂erdosRenyi 3 (1 / 2) = 1 / 4 ∧
      (1 / 4 : ℝ) ≠
        (1 / 2) * (1 - 1 / 2) ^ (2 * 3 - 4) +
          ((3 : ℝ) - 1) ^ 2 * (1 / 2) ^ 2 * (1 - 1 / 2) ^ (2 * 3 - 5) := by
  have h01 : (0 : Fin 3) ≠ (1 : Fin 3) := fun h ↦ by have := congr_arg Fin.val h; omega
  refine ⟨?_, by norm_num⟩
  change ∫ G, degOneInd (0 : Fin 3) G * degOneInd (1 : Fin 3) G ∂erdosRenyi 3 (1 / 2) = 1 / 4
  rw [degOneInd_mul_integral (by norm_num) (by norm_num) (by omega) h01]
  norm_num

/-- Counterexample at $n = 3, p = 1/2$ to the false printed variance formula for $\sum_i D_i$ at
`SteinIntro.tex:1395` (`ISSUE-3.9`): the true variance is $3/4$, whereas the printed expression
evaluates to $3$. -/
theorem Ex3_9_L1395_counterexample :
    let D : Fin 3 → SimpleGraph (Fin 3) → ℝ :=
      fun i G ↦ ({j : Fin 3 | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ)
    ProbabilityTheory.variance (fun G ↦ ∑ i : Fin 3, D i G) (erdosRenyi 3 (1 / 2)) = 3 / 4 ∧
      (3 / 4 : ℝ) ≠
        (3 : ℝ) * (3 - 1) * (1 / 2) * (1 - 1 / 2) ^ (3 - 2) *
          (1 - (3 - 1) * (1 / 2) * (1 - 1 / 2) ^ (3 - 2) + (1 - 1 / 2) ^ (3 - 2) +
            (3 - 1) ^ 2 * (1 / 2) ^ 2 * (1 - 1 / 2) ^ (3 - 3)) := by
  refine ⟨?_, by norm_num⟩
  change ProbabilityTheory.variance
      (fun G : SimpleGraph (Fin 3) ↦
        ∑ i : Fin 3, ({j : Fin 3 | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ))
      (erdosRenyi 3 (1 / 2)) = 3 / 4
  simp_rw [sum_degOneNeighbor_eq_sum_degOne 3]
  change ProbabilityTheory.variance (fun G ↦ ∑ j : Fin 3, degOneInd j G)
      (erdosRenyi 3 (1 / 2)) = 3 / 4
  rw [sum_degOne_variance (by norm_num) (by norm_num) (by omega)]
  norm_num

end SteinMethod
