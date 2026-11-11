/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Dependency
import Formalization.PoissonDep.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Poisson Approximation under Local Dependence (`Formalization.PoissonDep.LocalDependence`)

Covers Section 4.2 of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`,
`SteinIntro.tex:1968-2004`):

* Shared Chen–Stein neighborhood decomposition `abs_integral_poissonSteinOp_sum_indicator_le`.
* **Theorem 4.7, corrected** (`\label{thm103}`, `SteinIntro.tex:1970-1977`; `ISSUE-4.7`):
  `tvDist_sum_dep_indicator_le`, adding `∀ i, i ∈ N i`.
* **Negation of printed Theorem 4.7** (`ISSUE-4.7`): `not_Thm4_7_printed`, machine-checking the
  counterexample $n = 1$, $X_1 \equiv 1$, $N_1 = \emptyset$.
* **Remark 4.1** (`SteinIntro.tex:1978-1981`): `tvDist_sum_indicator_condExp_le`, proving from
  scratch the Arratia–Goldstein–Gordon `[agg89, agg90]` $b_1 + b_2 + b_3$ total-variation bound.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Shared Chen–Stein neighborhood decomposition -/

private lemma aemeasurable_finset_sum_nat' {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) {X : ι → Ω → ℕ} (hX : ∀ i ∈ s, AEMeasurable (X i) P) :
    AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) P := by
  classical
  induction s using Finset.induction with
  | empty => exact aemeasurable_const
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hX a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hX i (Finset.mem_insert_of_mem hi))

private lemma integrable_indicator_mul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → ℕ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hX01 : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) (hY01 : ∀ᵐ ω ∂P, Y ω = 0 ∨ Y ω = 1) :
    Integrable (fun ω ↦ (X ω : ℝ) * (Y ω : ℝ)) P := by
  refine Integrable.of_mem_Icc 0 1
    (((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hX).mul
      ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hY)) ?_
  filter_upwards [hX01, hY01] with ω hx hy
  rcases hx with hx0 | hx1 <;> rcases hy with hy0 | hy1
  · simp [hx0, hy0]
  · simp [hx0, hy1]
  · simp [hx1, hy0]
  · simp [hx1, hy1]

private lemma sum_sdiff_eq_sum_subtype {n : ℕ} (s : Finset (Fin n)) (g : Fin n → ℕ) :
    ∑ j ∈ Finset.univ \ s, g j = ∑ j : {j : Fin n // j ∉ s}, g j.1 := by
  have hmem : ∀ j : Fin n, j ∈ Finset.univ \ s ↔ j ∉ s := by simp
  refine Finset.sum_bij (fun j hj ↦ ⟨j, (hmem j).mp hj⟩)
    (fun _ _ ↦ Finset.mem_univ _) (fun _ _ _ _ h ↦ congrArg Subtype.val h)
    (fun ⟨j, hj⟩ _ ↦ ⟨j, (hmem j).mpr hj, rfl⟩) (fun _ _ ↦ rfl)

/-- Core Chen–Stein local-dependence decomposition (`SteinIntro.tex:1983-2003`): for `{0, 1}`
indicators `X_i` with neighborhoods `N_i` containing `i`, `|𝔼[r f(W + 1) - W f(W)]|` is bounded by
`min(1, r⁻¹) * (b₁ + b₂)` plus the centered remainder sum against `f(V_i + 1)`, where
`V_i = ∑_{j ∉ N_i} X_j`. -/
theorem abs_integral_poissonSteinOp_sum_indicator_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℕ} {N : Fin n → Finset (Fin n)} {r : ℝ≥0}
    (hr : 0 < r)
    (hX : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hNi : ∀ i : Fin n, i ∈ N i)
    (hr_sum : (r : ℝ) = ∑ i : Fin n, P.real {ω | X i ω = 1})
    {f : ℕ → ℝ} (hf : f ∈ poissonSteinClass r) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let p₂ : Fin n → Fin n → ℝ := fun i j ↦ ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P
    let V : Fin n → Ω → ℕ := fun i ω ↦ ∑ j ∈ Finset.univ \ N i, X j ω
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    |∫ ω, poissonSteinOp r f (W ω) ∂P| ≤
      min 1 (r : ℝ)⁻¹ *
        ((∑ i : Fin n, ∑ j ∈ N i, p i * p j) +
          ∑ i : Fin n, ∑ j ∈ (N i).erase i, p₂ i j) +
      ∑ i : Fin n, |∫ ω, ((X i ω : ℝ) - p i) * f (V i ω + 1) ∂P| := by
  intro p p₂ V W
  let U : Fin n → Ω → ℕ := fun i ω ↦ ∑ j ∈ (N i).erase i, X j ω
  let C : ℝ := min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))
  let M : ℝ := min 1 (r : ℝ)⁻¹
  have hC_nn : 0 ≤ C := le_min zero_le_one (Real.rpow_nonneg r.coe_nonneg _)
  have hM_nn : 0 ≤ M := le_min zero_le_one (inv_nonneg.mpr r.coe_nonneg)
  have hf_bdd : ∀ k : ℕ, |f k| ≤ C := hf.1
  have hf_diff : ∀ k : ℕ, |fwdDiff 1 f k| ≤ M :=
    abs_fwdDiff_le_min_of_mem_poissonSteinClass hr hf
  have hW_meas : AEMeasurable W P :=
    aemeasurable_finset_sum_nat' Finset.univ fun i _ ↦ hX i
  have hV_meas : ∀ i : Fin n, AEMeasurable (V i) P :=
    fun i ↦ aemeasurable_finset_sum_nat' (Finset.univ \ N i) fun j _ ↦ hX j
  have hU_meas : ∀ i : Fin n, AEMeasurable (U i) P :=
    fun i ↦ aemeasurable_finset_sum_nat' ((N i).erase i) fun j _ ↦ hX j
  have hInt_Xi : ∀ i : Fin n, Integrable (fun ω ↦ (X i ω : ℝ)) P :=
    fun i ↦ integrable_natCast_of_ae_zero_or_one (hX i) (hX01 i)
  have hInt_Xij : ∀ i j : Fin n, Integrable (fun ω ↦ (X i ω : ℝ) * (X j ω : ℝ)) P :=
    fun i j ↦ integrable_indicator_mul (hX i) (hX j) (hX01 i) (hX01 j)
  have hInt_fW : Integrable (fun ω ↦ f (W ω + 1)) P :=
    Integrable.of_mem_Icc (-C) C
      ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable hW_meas)
      (Eventually.of_forall fun ω ↦ abs_le.mp (hf_bdd (W ω + 1)))
  have hInt_fV : ∀ i : Fin n, Integrable (fun ω ↦ f (V i ω + 1)) P := fun i ↦
    Integrable.of_mem_Icc (-C) C
      ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable (hV_meas i))
      (Eventually.of_forall fun ω ↦ abs_le.mp (hf_bdd (V i ω + 1)))
  have hInt_Xi_fVU : ∀ i : Fin n,
      Integrable (fun ω ↦ (X i ω : ℝ) * f (V i ω + U i ω + 1)) P := by
    intro i
    refine Integrable.of_mem_Icc (-C) C
      (((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable (hX i)).mul
        ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable
          ((hV_meas i).add (hU_meas i)))) ?_
    filter_upwards [hX01 i] with ω hω
    rw [Set.mem_Icc, ← abs_le]
    rcases hω with h0 | h1
    · simp [h0, hC_nn]
    · rw [h1, Nat.cast_one, one_mul]
      exact hf_bdd (V i ω + U i ω + 1)
  have hInt_Xi_fV : ∀ i : Fin n, Integrable (fun ω ↦ (X i ω : ℝ) * f (V i ω + 1)) P := by
    intro i
    refine Integrable.of_mem_Icc (-C) C
      (((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable (hX i)).mul
        ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable
          (hV_meas i))) ?_
    filter_upwards [hX01 i] with ω hω
    rw [Set.mem_Icc, ← abs_le]
    rcases hω with h0 | h1
    · simp [h0, hC_nn]
    · rw [h1, Nat.cast_one, one_mul]
      exact hf_bdd (V i ω + 1)
  have hW_split_N : ∀ i : Fin n, ∀ ω, W ω = (∑ j ∈ N i, X j ω) + V i ω := fun i ω ↦ by
    simpa [W, V, add_comm] using (Finset.sum_sdiff (Finset.subset_univ (N i)) (f := (X · ω))).symm
  have hN_split : ∀ i : Fin n, ∀ ω, ∑ j ∈ N i, X j ω = X i ω + U i ω := fun i ω ↦
    (Finset.add_sum_erase (N i) (fun j ↦ X j ω) (hNi i)).symm
  have h_op_ae : (fun ω ↦ poissonSteinOp r f (W ω)) =ᵐ[P]
      fun ω ↦ ∑ i : Fin n,
        (p i * (f (W ω + 1) - f (V i ω + 1)) -
          (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) -
          ((X i ω : ℝ) - p i) * f (V i ω + 1)) := by
    filter_upwards [ae_all_iff.mpr hX01] with ω hω
    have hsum_X : (W ω : ℝ) * f (W ω) =
        ∑ i : Fin n, (X i ω : ℝ) * f (V i ω + U i ω + 1) := by
      change ((∑ i : Fin n, X i ω : ℕ) : ℝ) * f (W ω) = _
      rw [Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rcases hω i with h0 | h1
      · simp [h0]
      · have hW1 : W ω = V i ω + U i ω + 1 := by
          rw [hW_split_N i ω, hN_split i ω, h1]
          omega
        rw [h1, hW1]
    simp only [poissonSteinOp, hr_sum, hsum_X, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  have hInt_t1 : ∀ i : Fin n, Integrable (fun ω ↦ p i * (f (W ω + 1) - f (V i ω + 1))) P :=
    fun i ↦ (hInt_fW.sub (hInt_fV i)).const_mul (p i)
  have hInt_t2 : ∀ i : Fin n,
      Integrable (fun ω ↦ (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1))) P := by
    intro i
    have heq : (fun ω ↦ (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1))) =
        fun ω ↦ (X i ω : ℝ) * f (V i ω + U i ω + 1) - (X i ω : ℝ) * f (V i ω + 1) := by
      ext ω; ring
    rw [heq]
    exact (hInt_Xi_fVU i).sub (hInt_Xi_fV i)
  have hInt_t3 : ∀ i : Fin n, Integrable (fun ω ↦ ((X i ω : ℝ) - p i) * f (V i ω + 1)) P := by
    intro i
    have heq : (fun ω ↦ ((X i ω : ℝ) - p i) * f (V i ω + 1)) =
        fun ω ↦ (X i ω : ℝ) * f (V i ω + 1) - p i * f (V i ω + 1) := by
      ext ω; ring
    rw [heq]
    exact (hInt_Xi_fV i).sub ((hInt_fV i).const_mul (p i))
  have hInt_summand : ∀ i : Fin n,
      Integrable (fun ω ↦
        p i * (f (W ω + 1) - f (V i ω + 1)) -
          (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) -
          ((X i ω : ℝ) - p i) * f (V i ω + 1)) P :=
    fun i ↦ ((hInt_t1 i).sub (hInt_t2 i)).sub (hInt_t3 i)
  rw [integral_congr_ae h_op_ae, integral_finsetSum Finset.univ fun i _ ↦ hInt_summand i]
  have hb1 : ∀ i : Fin n,
      |∫ ω, p i * (f (W ω + 1) - f (V i ω + 1)) ∂P| ≤ M * ∑ j ∈ N i, p i * p j := by
    intro i
    rw [integral_const_mul, abs_mul, abs_of_nonneg measureReal_nonneg]
    have hpt : ∀ ω, ‖f (W ω + 1) - f (V i ω + 1)‖ ≤ M * ∑ j ∈ N i, (X j ω : ℝ) := by
      intro ω
      rw [Real.norm_eq_abs]
      refine (abs_sub_le_of_abs_fwdDiff_le hM_nn hf_diff (V i ω + 1) (W ω + 1)).trans ?_
      have hdiff : ((W ω + 1 : ℕ) : ℝ) - ((V i ω + 1 : ℕ) : ℝ) = ∑ j ∈ N i, (X j ω : ℝ) := by
        rw [hW_split_N i ω]
        push_cast
        ring
      rw [hdiff, abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ Nat.cast_nonneg _)]
    have hint_diff : |∫ ω, (f (W ω + 1) - f (V i ω + 1)) ∂P| ≤ M * ∑ j ∈ N i, p j := by
      calc |∫ ω, (f (W ω + 1) - f (V i ω + 1)) ∂P|
        _ = ‖∫ ω, (f (W ω + 1) - f (V i ω + 1)) ∂P‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ ω, ‖f (W ω + 1) - f (V i ω + 1)‖ ∂P := norm_integral_le_integral_norm _
        _ ≤ ∫ ω, M * ∑ j ∈ N i, (X j ω : ℝ) ∂P :=
          integral_mono (hInt_fW.sub (hInt_fV i)).norm
            ((integrable_finsetSum _ fun j _ ↦ hInt_Xi j).const_mul M) hpt
        _ = M * ∑ j ∈ N i, p j := by
          rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hInt_Xi j]
          congr 1
          exact Finset.sum_congr rfl fun j _ ↦ integral_natCast_of_ae_zero_or_one (hX j) (hX01 j)
    calc p i * |∫ ω, (f (W ω + 1) - f (V i ω + 1)) ∂P|
      _ ≤ p i * (M * ∑ j ∈ N i, p j) := mul_le_mul_of_nonneg_left hint_diff measureReal_nonneg
      _ = M * ∑ j ∈ N i, p i * p j := by
        rw [← mul_assoc, mul_comm (p i) M, mul_assoc, Finset.mul_sum]
  have hb2 : ∀ i : Fin n,
      |∫ ω, (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) ∂P| ≤
        M * ∑ j ∈ (N i).erase i, p₂ i j := by
    intro i
    have hpt : ∀ ω, ‖(X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1))‖ ≤
        M * ∑ j ∈ (N i).erase i, (X i ω : ℝ) * (X j ω : ℝ) := by
      intro ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have h1 := abs_sub_le_of_abs_fwdDiff_le hM_nn hf_diff (V i ω + 1) (V i ω + U i ω + 1)
      have hdiff : |((V i ω + U i ω + 1 : ℕ) : ℝ) - ((V i ω + 1 : ℕ) : ℝ)| =
          ∑ j ∈ (N i).erase i, (X j ω : ℝ) := by
        have heq : ((V i ω + U i ω + 1 : ℕ) : ℝ) - ((V i ω + 1 : ℕ) : ℝ) =
            ∑ j ∈ (N i).erase i, (X j ω : ℝ) := by
          dsimp only [U]
          push_cast
          ring
        rw [heq, abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ Nat.cast_nonneg _)]
      rw [hdiff] at h1
      calc (X i ω : ℝ) * |f (V i ω + U i ω + 1) - f (V i ω + 1)|
        _ ≤ (X i ω : ℝ) * (M * ∑ j ∈ (N i).erase i, (X j ω : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = M * ∑ j ∈ (N i).erase i, (X i ω : ℝ) * (X j ω : ℝ) := by
          rw [← mul_assoc, mul_comm (X i ω : ℝ) M, mul_assoc, Finset.mul_sum]
    calc |∫ ω, (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) ∂P|
      _ = ‖∫ ω, (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) ∂P‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ ω, ‖(X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1))‖ ∂P :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, M * ∑ j ∈ (N i).erase i, (X i ω : ℝ) * (X j ω : ℝ) ∂P :=
        integral_mono (hInt_t2 i).norm
          ((integrable_finsetSum _ fun j _ ↦ hInt_Xij i j).const_mul M) hpt
      _ = M * ∑ j ∈ (N i).erase i, p₂ i j := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ hInt_Xij i j]
  calc |∑ i : Fin n, ∫ ω,
        (p i * (f (W ω + 1) - f (V i ω + 1)) -
          (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) -
          ((X i ω : ℝ) - p i) * f (V i ω + 1)) ∂P|
    _ ≤ ∑ i : Fin n, |∫ ω,
        (p i * (f (W ω + 1) - f (V i ω + 1)) -
          (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) -
          ((X i ω : ℝ) - p i) * f (V i ω + 1)) ∂P| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n,
        (M * (∑ j ∈ N i, p i * p j) + M * (∑ j ∈ (N i).erase i, p₂ i j) +
          |∫ ω, ((X i ω : ℝ) - p i) * f (V i ω + 1) ∂P|) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hInt_12 : Integrable
          (fun ω ↦ p i * (f (W ω + 1) - f (V i ω + 1)) -
            (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1))) P :=
        (hInt_t1 i).sub (hInt_t2 i)
      rw [integral_sub hInt_12 (hInt_t3 i), integral_sub (hInt_t1 i) (hInt_t2 i)]
      set I₁ := ∫ ω, p i * (f (W ω + 1) - f (V i ω + 1)) ∂P
      set I₂ := ∫ ω, (X i ω : ℝ) * (f (V i ω + U i ω + 1) - f (V i ω + 1)) ∂P
      set I₃ := ∫ ω, ((X i ω : ℝ) - p i) * f (V i ω + 1) ∂P
      have htri1 : |I₁ - I₂ - I₃| ≤ |I₁ - I₂| + |I₃| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (I₁ - I₂) 0 I₃
      have htri2 : |I₁ - I₂| ≤ |I₁| + |I₂| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le I₁ 0 I₂
      linarith [hb1 i, hb2 i]
    _ = M * ((∑ i : Fin n, ∑ j ∈ N i, p i * p j) +
          ∑ i : Fin n, ∑ j ∈ (N i).erase i, p₂ i j) +
        ∑ i : Fin n, |∫ ω, ((X i ω : ℝ) - p i) * f (V i ω + 1) ∂P| := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]

/-! ### Theorem 4.7 (corrected) and Counterexample to Printed Theorem 4.7 (`ISSUE-4.7`) -/

/-- **Theorem 4.7, corrected** (`\label{thm103}`, `SteinIntro.tex:1970-1977`; `ISSUE-4.7`):
Poisson local-dependence total-variation bound for a sum `W = ∑ i, X i` of `{0, 1}`-indicators with
dependency neighborhoods `N_i` satisfying `∀ i, i ∈ N i`. -/
theorem tvDist_sum_dep_indicator_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {N : Fin n → Finset (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hDep : HasDependencyNeighborhoods P (fun i ω ↦ (X i ω : ℝ)) N)
    (hNi : ∀ i : Fin n, i ∈ N i)
    (hr_sum : (r : ℝ) = ∑ i : Fin n, P.real {ω | X i ω = 1})
    (_hZ : AEMeasurable Z P')
    (hlaw : P'.map Z = poissonLaw r) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let p₂ : Fin n → Fin n → ℝ := fun i j ↦ ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          ((∑ i : Fin n, ∑ j ∈ N i, p i * p j) +
            ∑ i : Fin n, ∑ j ∈ (N i).erase i, p₂ i j)) := by
  intro p p₂ W
  rw [hlaw]
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with rfl | hr_pos
  · have hmap := map_sum_eq_poissonLaw_zero hX hX01 hr_sum.symm
    rw [show W = fun ω ↦ ∑ i : Fin n, X i ω from rfl, hmap, tvDist, ipm_self]
    exact zero_le
  · have hW_meas : AEMeasurable W P :=
      aemeasurable_finset_sum_nat' Finset.univ fun i _ ↦ hX i
    refine (tvDist_le_iSup_poissonSteinClass P hr_pos hW_meas).trans (iSup₂_le fun f hf ↦ ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    let V : Fin n → Ω → ℕ := fun i ω ↦ ∑ j ∈ Finset.univ \ N i, X j ω
    have hrem_zero : ∀ i : Fin n,
        |∫ ω, ((X i ω : ℝ) - p i) * f (V i ω + 1) ∂P| = 0 := by
      intro i
      let C : ℝ := min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))
      have hV_meas : AEMeasurable (V i) P :=
        aemeasurable_finset_sum_nat' (Finset.univ \ N i) fun j _ ↦ hX j
      have hInt_fV : Integrable (fun ω ↦ f (V i ω + 1)) P :=
        Integrable.of_mem_Icc (-C) C
          ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable hV_meas)
          (Eventually.of_forall fun ω ↦ abs_le.mp (hf.1 (V i ω + 1)))
      have htoNat_meas : Measurable (Nat.floor : ℝ → ℕ) := by
        intro s _
        have hsing : ∀ k : ℕ, MeasurableSet ((Nat.floor : ℝ → ℕ) ⁻¹' {k}) := by
          intro k
          cases k with
          | zero =>
            have heq : (Nat.floor : ℝ → ℕ) ⁻¹' {0} = Set.Iio 1 := by
              ext x; simp
            rw [heq]
            exact measurableSet_Iio
          | succ m =>
            have heq : (Nat.floor : ℝ → ℕ) ⁻¹' {m + 1} =
                Set.Ico ((m + 1 : ℕ) : ℝ) ((m + 2 : ℕ) : ℝ) := by
              ext x
              simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico]
              constructor
              · intro hx
                have hx0 : 0 ≤ x := by
                  by_contra hneg
                  have hz : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hneg)
                  omega
                have hiff := (Nat.floor_eq_iff hx0).mp hx
                refine ⟨hiff.1, ?_⟩
                have h2 := hiff.2
                push_cast at h2 ⊢
                linarith
              · intro hx
                have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx.1
                refine (Nat.floor_eq_iff hx0).mpr ⟨hx.1, ?_⟩
                have h2 := hx.2
                push_cast at h2 ⊢
                linarith
            rw [heq]
            exact measurableSet_Ico
        have hs_eq : (Nat.floor : ℝ → ℕ) ⁻¹' s = ⋃ k ∈ s, (Nat.floor : ℝ → ℕ) ⁻¹' {k} := by
          ext x; simp
        rw [hs_eq]
        exact MeasurableSet.biUnion s.to_countable fun k _ ↦ hsing k
      have hψ : Measurable fun u : ({j : Fin n // j ∉ N i} → ℝ) ↦
          f ((∑ j : {j : Fin n // j ∉ N i}, Nat.floor (u j)) + 1) :=
        (Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp
          (Finset.measurable_sum Finset.univ fun j _ ↦ htoNat_meas.comp (measurable_pi_apply j))
      have hind_fV : IndepFun (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ f (V i ω + 1)) P := by
        have hcomp := (hDep i).comp measurable_id hψ
        have heq_V : (fun ω ↦ f ((∑ j : {j : Fin n // j ∉ N i},
            Nat.floor (X j.1 ω : ℝ)) + 1)) = fun ω ↦ f (V i ω + 1) := by
          ext ω
          simp only [Nat.floor_natCast, V, sum_sdiff_eq_sum_subtype]
        simpa only [Function.comp_def, id_eq, heq_V] using hcomp
      have hInt_Xi := integrable_natCast_of_ae_zero_or_one (hX i) (hX01 i)
      have hind_sub : IndepFun (fun ω ↦ (X i ω : ℝ) - p i) (fun ω ↦ f (V i ω + 1)) P := by
        simpa only [Function.comp_def, id_eq] using
          hind_fV.comp (measurable_id.sub_const (p i)) measurable_id
      have hmul := hind_sub.integral_mul_eq_mul_integral
        (hInt_Xi.sub (integrable_const (p i))).aestronglyMeasurable
        hInt_fV.aestronglyMeasurable
      have hmean0 : ∫ ω, ((X i ω : ℝ) - p i) ∂P = 0 := by
        rw [integral_sub hInt_Xi (integrable_const (p i)),
          integral_natCast_of_ae_zero_or_one (hX i) (hX01 i),
          integral_const, probReal_univ, one_smul, sub_self]
      change |∫ ω, ((fun ω' ↦ (X i ω' : ℝ) - p i) * (fun ω' ↦ f (V i ω' + 1))) ω ∂P| = 0
      rw [hmul, hmean0, zero_mul, abs_zero]
    have hmain := abs_integral_poissonSteinOp_sum_indicator_le P hr_pos hX hX01 hNi hr_sum hf
    dsimp only at hmain
    have hrem_sum : (∑ i : Fin n,
        |∫ ω, ((X i ω : ℝ) - p i) * f ((∑ j ∈ Finset.univ \ N i, X j ω) + 1) ∂P|) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ hrem_zero i
    linarith [hmain, hrem_sum]

/-- Literal printed statement of Theorem 4.7 (`\label{thm103}`, `SteinIntro.tex:1970-1977`),
omitting `∀ i, i ∈ N i` (`ISSUE-4.7`). -/
def Thm4_7_printed : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {N : Fin n → Finset (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    HasDependencyNeighborhoods P (fun i ω ↦ (X i ω : ℝ)) N →
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let p₂ : Fin n → Fin n → ℝ := fun i j ↦ ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    (r : ℝ) = ∑ i : Fin n, p i →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          ((∑ i : Fin n, ∑ j ∈ N i, p i * p j) +
            ∑ i : Fin n, ∑ j ∈ (N i).erase i, p₂ i j))

/-- **Refutation of printed Theorem 4.7** (`ISSUE-4.7`, `SteinIntro.tex:1970-1977`):
with $n = 1$, $X_1 \equiv 1$ ($p_1 = \lambda = 1$), and $N_1 = \emptyset$, $X_1$ is constant and
hence independent of $\{X_j\}_{j \notin N_1} = \{X_1\}$, so the printed bound is `0`, whereas
`d_TV(δ_1, Po(1)) ≥ e^{-1} > 0`. -/
theorem not_Thm4_7_printed : ¬ Thm4_7_printed := by
  intro hprint
  let P : Measure PUnit := Measure.dirac PUnit.unit
  let P' : Measure (PUnit × ℕ) := (Measure.dirac PUnit.unit).prod (poissonLaw 1)
  let X : Fin 1 → PUnit → ℕ := fun _ _ ↦ 1
  let N : Fin 1 → Finset (Fin 1) := fun _ ↦ ∅
  have hX : ∀ i : Fin 1, AEMeasurable (X i) P := fun _ ↦ aemeasurable_const
  have hX01 : ∀ i : Fin 1, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1 :=
    fun _ ↦ Eventually.of_forall fun _ ↦ Or.inr rfl
  have hDep : HasDependencyNeighborhoods P (fun i ω ↦ (X i ω : ℝ)) N :=
    fun _ ↦ indepFun_const_left ((1 : ℕ) : ℝ) _
  have hr_sum : ((1 : ℝ≥0) : ℝ) = ∑ i : Fin 1, P.real {ω | X i ω = 1} := by
    simp [P, X, measureReal_def]
  have hlaw : P'.map Prod.snd = poissonLaw 1 := by
    simp [P', Measure.map_snd_prod]
  have hle := hprint P P' (X := X) (N := N) (r := 1) (Z := Prod.snd)
    hX hX01 hDep hr_sum measurable_snd.aemeasurable hlaw
  have hrhs : ENNReal.ofReal
      (min 1 ((1 : ℝ≥0) : ℝ)⁻¹ *
        ((∑ i : Fin 1, ∑ j ∈ N i, P.real {ω | X i ω = 1} * P.real {ω | X j ω = 1}) +
          ∑ i : Fin 1, ∑ j ∈ (N i).erase i, ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P)) = 0 := by
    simp [N]
  rw [hrhs, hlaw] at hle
  let W : PUnit → ℕ := fun ω ↦ ∑ i : Fin 1, X i ω
  have hmapW : P.map W = Measure.dirac 1 := by
    have hW1 : W = fun _ : PUnit ↦ (1 : ℕ) := by
      ext ω; simp [W, X]
    rw [hW1, Measure.map_const, measure_univ, one_smul]
  rw [hmapW] at hle
  have htv : ENNReal.ofReal |(Measure.dirac (1 : ℕ)).real {0} - (poissonLaw 1).real {0}| ≤
      tvDist (Measure.dirac 1) (poissonLaw 1) := by
    rw [tvDist_eq_iSup]
    exact le_iSup₂_of_le ({0} : Set ℕ) .of_discrete le_rfl
  have hdirac0 : (Measure.dirac (1 : ℕ)).real {0} = 0 := by
    simp [measureReal_def, Measure.dirac_apply' _ .of_discrete]
  have hpois0 : (poissonLaw 1).real {0} = Real.exp (-1) := by
    simpa using ProbabilityTheory.poissonMeasure_real_singleton 1 0
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal |(Measure.dirac (1 : ℕ)).real {0} -
      (poissonLaw 1).real {0}| := by
    rw [hdirac0, hpois0, zero_sub, abs_neg, abs_of_pos (Real.exp_pos (-1))]
    exact ENNReal.ofReal_pos.mpr (Real.exp_pos (-1))
  exact not_lt_of_ge (htv.trans hle) hpos

/-! ### Remark 4.1: Arratia–Goldstein–Gordon `b₁ + b₂ + b₃` Bound -/

/-- **Remark 4.1** (`SteinIntro.tex:1978-1981`, proving from scratch the Arratia–Goldstein–Gordon
`[agg89, agg90]` $b_1 + b_2 + b_3$ bound cited there): dropping the independence assumption on
$(X_j)_{j \notin N_i}$ for neighborhoods $N_i$ ($i \in N_i$) adds the conditional-expectation
dependence term $\min\{1, \lambda^{-1/2}\} \sum_{i=1}^n \mathbb{E}|\mathbb{E}[X_i - p_i \mid
(X_j)_{j \notin N_i}]|$.

*Reading note (`stmts-review-05C` C3)*: Ross's prose states that dropping the independence
assumption adds *"an additional error term that (roughly) measures the dependence between $X_i$ and
$(X_j)_{j \notin N_i}$"* (`SteinIntro.tex:1979-1981`), citing `[agg89, agg90]`. We formalize this
concretely via the standard Arratia–Goldstein–Gordon $b_3$ term
$\sum_{i=1}^n \mathbb{E}|\mathbb{E}[X_i - p_i \mid \sigma(X_j : j \notin N_i)]|$ weighted by the
Lemma 4.4 `(4.2)` uniform bound $\|f\| \le \min\{1, \lambda^{-1/2}\}$, with `Measurable (X i)` so
the comap $\sigma$-algebra in `P[· | m_i]` is a sub-$\sigma$-algebra (junk-zero rule). -/
theorem tvDist_sum_indicator_condExp_le
    {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {N : Fin n → Finset (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX : ∀ i : Fin n, Measurable (X i))
    (hX01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hNi : ∀ i : Fin n, i ∈ N i)
    (hr_sum : (r : ℝ) = ∑ i : Fin n, P.real {ω | X i ω = 1})
    (_hZ : AEMeasurable Z P')
    (hlaw : P'.map Z = poissonLaw r) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let p₂ : Fin n → Fin n → ℝ := fun i j ↦ ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P
    let b₁ : ℝ := ∑ i : Fin n, ∑ j ∈ N i, p i * p j
    let b₂ : ℝ := ∑ i : Fin n, ∑ j ∈ (N i).erase i, p₂ i j
    let b₃ : ℝ := ∑ i : Fin n,
      ∫ ω, |P[fun ω' ↦ (X i ω' : ℝ) - p i |
        MeasurableSpace.comap (fun ω' (j : {j : Fin n // j ∉ N i}) ↦ X j ω') inferInstance] ω| ∂P
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (min 1 (r : ℝ)⁻¹ * (b₁ + b₂) + min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) * b₃) := by
  intro p p₂ b₁ b₂ b₃ W
  rw [hlaw]
  have hX_ae : ∀ i : Fin n, AEMeasurable (X i) P := fun i ↦ (hX i).aemeasurable
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with rfl | hr_pos
  · have hmap := map_sum_eq_poissonLaw_zero hX_ae hX01 hr_sum.symm
    rw [show W = fun ω ↦ ∑ i : Fin n, X i ω from rfl, hmap, tvDist, ipm_self]
    exact zero_le
  · have hW_meas : AEMeasurable W P :=
      aemeasurable_finset_sum_nat' Finset.univ fun i _ ↦ hX_ae i
    refine (tvDist_le_iSup_poissonSteinClass P hr_pos hW_meas).trans (iSup₂_le fun f hf ↦ ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    let V : Fin n → Ω → ℕ := fun i ω ↦ ∑ j ∈ Finset.univ \ N i, X j ω
    let C : ℝ := min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))
    have hmain := abs_integral_poissonSteinOp_sum_indicator_le P hr_pos hX_ae hX01 hNi hr_sum hf
    refine hmain.trans (add_le_add le_rfl ?_)
    dsimp only [b₃]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    let tup : Ω → ({j : Fin n // j ∉ N i} → ℕ) := fun ω j ↦ X j.1 ω
    have htup_meas : Measurable tup := measurable_pi_iff.mpr fun j ↦ hX j.1
    have hm_i : MeasurableSpace.comap tup inferInstance ≤ mΩ := htup_meas.comap_le
    have : IsFiniteMeasure (P.trim hm_i) := isFiniteMeasure_trim hm_i
    let d : Ω → ℝ := fun ω ↦ (X i ω : ℝ) - p i
    let g : Ω → ℝ := fun ω ↦ f (V i ω + 1)
    let ψ : ({j : Fin n // j ∉ N i} → ℕ) → ℝ :=
      fun u ↦ f ((∑ j : {j : Fin n // j ∉ N i}, u j) + 1)
    have hψ : Measurable ψ :=
      (Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp
        (Finset.measurable_sum Finset.univ fun j _ ↦ measurable_pi_apply j)
    have hg_eq : g = ψ ∘ tup := by
      ext ω
      simp [g, ψ, tup, V, sum_sdiff_eq_sum_subtype]
    have hg_meas : Measurable g := by
      rw [hg_eq]
      exact hψ.comp htup_meas
    have hg_sm : StronglyMeasurable[MeasurableSpace.comap tup inferInstance] g := by
      rw [hg_eq]
      exact (hψ.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    have hd_int : Integrable d P :=
      (integrable_natCast_of_ae_zero_or_one (hX_ae i) (hX01 i)).sub (integrable_const (p i))
    have hdg_int : Integrable (d * g) P := by
      refine Integrable.of_mem_Icc (-(2 * C)) (2 * C)
        (hd_int.aemeasurable.mul hg_meas.aemeasurable) ?_
      filter_upwards [hX01 i] with ω hω
      rw [Pi.mul_apply, Set.mem_Icc, ← abs_le, abs_mul]
      have hp_le1 : p i ≤ 1 := by
        simpa only [probReal_univ] using
          (measureReal_mono (Set.subset_univ {ω' | X i ω' = 1}) : P.real {ω' | X i ω' = 1} ≤ _)
      have hp_nn : 0 ≤ p i := measureReal_nonneg
      have hd_le2 : |d ω| ≤ 2 := by
        dsimp only [d]
        rcases hω with h0 | h1
        · rw [h0, Nat.cast_zero, abs_le]; constructor <;> linarith
        · rw [h1, Nat.cast_one, abs_le]; constructor <;> linarith
      calc |d ω| * |g ω|
        _ ≤ 2 * C := mul_le_mul hd_le2 (hf.1 (V i ω + 1)) (abs_nonneg _) (by positivity)
    have hpull : P[d * g | MeasurableSpace.comap tup inferInstance] =ᵐ[P]
        P[d | MeasurableSpace.comap tup inferInstance] * g :=
      condExp_mul_of_stronglyMeasurable_right hg_sm hdg_int hd_int
    have hint_eq : ∫ ω, d ω * g ω ∂P =
        ∫ ω, P[d | MeasurableSpace.comap tup inferInstance] ω * g ω ∂P := by
      calc ∫ ω, d ω * g ω ∂P
        _ = ∫ ω, P[d * g | MeasurableSpace.comap tup inferInstance] ω ∂P :=
          (integral_condExp hm_i).symm
        _ = ∫ ω, P[d | MeasurableSpace.comap tup inferInstance] ω * g ω ∂P :=
          integral_congr_ae hpull
    have hcond_prod_int : Integrable
        (fun ω ↦ P[d | MeasurableSpace.comap tup inferInstance] ω * g ω) P :=
      integrable_condExp.congr hpull
    calc |∫ ω, d ω * g ω ∂P|
      _ = ‖∫ ω, P[d | MeasurableSpace.comap tup inferInstance] ω * g ω ∂P‖ := by
        rw [hint_eq, Real.norm_eq_abs]
      _ ≤ ∫ ω, ‖P[d | MeasurableSpace.comap tup inferInstance] ω * g ω‖ ∂P :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, C * |P[d | MeasurableSpace.comap tup inferInstance] ω| ∂P := by
        refine integral_mono hcond_prod_int.norm (integrable_condExp.abs.const_mul C) fun ω ↦ ?_
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hf.1 (V i ω + 1)) (abs_nonneg _)
      _ = C * ∫ ω, |P[d | MeasurableSpace.comap tup inferInstance] ω| ∂P :=
        integral_const_mul C _

end SteinMethod
