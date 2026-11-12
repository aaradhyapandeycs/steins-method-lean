/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Monotone.FKGCore
import Formalization.Poisson.SteinBounds
import Formalization.Poisson.SteinCore
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FinCases

/-!
# Theorem 4.17 and Reading (A) Refutation (`Formalization.PoissonSizeBias.Monotone.FKG`)

Re-exports `FKGCore` and proves Theorem 4.17 (`\label{thm124}`, `SteinIntro.tex:2382-2390`,
`thm4_17_corrected`) together with the library refutation `not_Thm4_17_printed`
(`not_thm4_17_printed`, `ISSUE-4.17`) of the individual-direction reading.
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-! ### Part 3: Theorem 4.17 (`\label{thm124}`, `SteinIntro.tex:2382-2390`) -/

private lemma tvDist_le_of_forall_measurableSet {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) {c : ℝ≥0∞}
    (hc : ∀ A : Set α, MeasurableSet A → ENNReal.ofReal |μ.real A - ν.real A| ≤ c) :
    tvDist μ ν ≤ c := by
  unfold tvDist ipm
  refine iSup₂_le fun h hh ↦ iSup_le fun _ ↦ ?_
  rcases hh with ⟨A, hA, rfl⟩
  rw [integral_indicator_one hA, integral_indicator_one hA]
  exact hc A hA

private lemma le_tvDist_of_measurableSet {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    ENNReal.ofReal |μ.real A - ν.real A| ≤ tvDist μ ν := by
  unfold tvDist ipm
  have hint : Integrable (A.indicator (1 : α → ℝ)) μ ∧
      Integrable (A.indicator (1 : α → ℝ)) ν :=
    ⟨(integrable_const (1 : ℝ)).indicator hA, (integrable_const (1 : ℝ)).indicator hA⟩
  have h_eq : ENNReal.ofReal |μ.real A - ν.real A| =
      ENNReal.ofReal |(∫ x, A.indicator (1 : α → ℝ) x ∂μ) -
        (∫ x, A.indicator (1 : α → ℝ) x ∂ν)| := by
    rw [integral_indicator_one hA, integral_indicator_one hA]
  rw [h_eq]
  exact le_iSup₂_of_le (A.indicator 1) ⟨A, hA, rfl⟩ (le_iSup_of_le hint le_rfl)

private lemma nat_cast_eq_sum_indicator_range {n k : ℕ} (hkn : k ≤ n) :
    (k : ℝ) = ∑ m ∈ Finset.range n, if m + 1 ≤ k then (1 : ℝ) else 0 := by
  have h_sub : (∑ m ∈ Finset.range n, if m + 1 ≤ k then (1 : ℝ) else 0) =
      ∑ m ∈ Finset.range k, (1 : ℝ) := by
    rw [← Finset.sum_subset (Finset.range_mono hkn)]
    · refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hlt : m < k := Finset.mem_range.mp hm
      simp [Nat.succ_le_of_lt hlt]
    · intro m _ hm
      have hnot : ¬ (m + 1 ≤ k) := by
        have := Finset.mem_range.not.mp hm
        omega
      simp [hnot]
  rw [h_sub]
  simp

private lemma fn_succ_eq_fn_one_add_sum_fwdDiff {n k : ℕ} (hkn : k ≤ n) (g : ℕ → ℝ) :
    g (k + 1) = g 1 + ∑ m ∈ Finset.range n,
      fwdDiff 1 g (m + 1) * (if m + 1 ≤ k then (1 : ℝ) else 0) := by
  have h_sub : (∑ m ∈ Finset.range n,
      fwdDiff 1 g (m + 1) * (if m + 1 ≤ k then (1 : ℝ) else 0)) =
      ∑ m ∈ Finset.range k, fwdDiff 1 g (m + 1) := by
    rw [← Finset.sum_subset (Finset.range_mono hkn)]
    · refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hlt : m < k := Finset.mem_range.mp hm
      simp [Nat.succ_le_of_lt hlt]
    · intro m _ hm
      have hnot : ¬ (m + 1 ≤ k) := by
        have := Finset.mem_range.not.mp hm
        omega
      simp [hnot]
  rw [h_sub]
  have h_tele : ∀ m : ℕ, g (m + 1) = g 1 + ∑ j ∈ Finset.range m, fwdDiff 1 g (j + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ← add_assoc, ← ih]
        simp only [fwdDiff]
        ring
  exact h_tele k

/-- **Theorem 4.17, corrected** (`\label{thm124}`, `SteinIntro.tex:2382-2390`; `ISSUE-4.17`):
if $\mathbf{Y} = (Y_j)_{j=1}^N$ are independent $\{0, 1\}$-indicators and
$f_1, \dots, f_n : \{0, 1\}^N \to \{0, 1\}$ are either all increasing (`MonotoneOn`) or all
decreasing (`AntitoneOn`) on $\{0, 1\}^N = \{y \mid \forall j,\, y_j \le 1\}$, then for
$X_i = f_i(\mathbf{Y})$, $p_i = \mathbb{P}(X_i = 1)$, $W = \sum_{i=1}^n X_i$,
$\lambda = \sum_{i=1}^n p_i$, and $Z \sim \mathrm{Po}(\lambda)$,
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\min\{1, \lambda^{-1}\}(\operatorname{Var}(W) - \lambda + 2 \sum_{i=1}^n p_i^2)$. -/
theorem thm4_17_corrected
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {N n : ℕ} {Y : Fin N → Ω → ℕ} {f : Fin n → (Fin N → ℕ) → ℕ}
    {r : ℝ≥0} {Z : Ω' → ℕ}
    (hY_meas : ∀ j : Fin N, AEMeasurable (Y j) P)
    (hY_01 : ∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (hY_indep : ProbabilityTheory.iIndepFun Y P)
    (hf_01 : ∀ i : Fin n, ∀ y : Fin N → ℕ,
      (∀ j : Fin N, y j ≤ 1) → f i y = 0 ∨ f i y = 1)
    (hf_mono :
      (∀ i : Fin n, MonotoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) ∨
      (∀ i : Fin n, AntitoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}))
    (hr_eq : (r : ℝ) = ∑ i : Fin n, P.real {ω | f i (fun j ↦ Y j ω) = 1})
    (_hZ_meas : AEMeasurable Z P')
    (hZ_law : P'.map Z = poissonLaw r) :
    let X : Fin n → Ω → ℕ := fun i ω ↦ f i (fun j ↦ Y j ω)
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
            2 * ∑ i : Fin n, p i ^ 2)) := by
  intro X p W
  rw [hZ_law]
  have hY_all01 : ∀ᵐ ω ∂P, ∀ j : Fin N, Y j ω ≤ 1 := by
    filter_upwards [Filter.eventually_all.mpr hY_01] with ω hω j
    rcases hω j with h0 | h1 <;> omega
  have hX_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1 := by
    intro i
    filter_upwards [hY_all01] with ω hω
    exact hf_01 i (fun j ↦ Y j ω) hω
  have hX_all01 : ∀ᵐ ω ∂P, ∀ i : Fin n, X i ω = 0 ∨ X i ω = 1 :=
    Filter.eventually_all.mpr hX_01
  have hY_vec_meas : AEMeasurable (fun ω (j : Fin N) ↦ Y j ω) P :=
    aemeasurable_pi_iff.mpr hY_meas
  have hX_meas : ∀ i : Fin n, AEMeasurable (X i) P :=
    fun i ↦ (Measurable.of_discrete (f := f i)).comp_aemeasurable hY_vec_meas
  have hW_meas : AEMeasurable W P :=
    (Measurable.of_discrete (f := fun y : Fin N → ℕ ↦ ∑ i : Fin n, f i y)).comp_aemeasurable
      hY_vec_meas
  have hint_comp : ∀ Φ : (Fin N → ℕ) → ℝ,
      Integrable (fun ω ↦ Φ (fun j ↦ Y j ω)) P :=
    fun Φ ↦ (integrable_and_integral_comp_zero_one_indep P hY_meas hY_01 hY_indep Φ).1
  have hX_mean : ∀ i : Fin n, ∫ ω, (X i ω : ℝ) ∂P = p i := by
    intro i
    let Y' : Fin N → Ω → ℕ := fun j ↦ (hY_meas j).mk (Y j)
    have hY'_meas : Measurable (fun ω j ↦ Y' j ω) :=
      measurable_pi_iff.mpr fun j ↦ (hY_meas j).measurable_mk
    have hY'_ae : ∀ᵐ ω ∂P, (fun j ↦ Y j ω) = (fun j ↦ Y' j ω) := by
      filter_upwards [Filter.eventually_all.mpr fun j ↦ (hY_meas j).ae_eq_mk] with ω hω
      funext j
      exact hω j
    have hX'_meas : Measurable (fun ω ↦ f i (fun j ↦ Y' j ω)) :=
      (Measurable.of_discrete (f := f i)).comp hY'_meas
    have h_ind_ae : (fun ω ↦ (X i ω : ℝ)) =ᵐ[P]
        {ω | f i (fun j ↦ Y' j ω) = 1}.indicator (1 : Ω → ℝ) := by
      filter_upwards [hX_01 i, hY'_ae] with ω h01 h_eq
      rcases h01 with h0 | h1
      · have h0' : f i (fun j ↦ Y' j ω) = 0 := by rw [← h_eq]; exact h0
        simp [X, h0, h0']
      · have h1' : f i (fun j ↦ Y' j ω) = 1 := by rw [← h_eq]; exact h1
        simp [X, h1, h1']
    have h_meas_set : MeasurableSet {ω | f i (fun j ↦ Y' j ω) = 1} :=
      hX'_meas (measurableSet_singleton 1)
    rw [integral_congr_ae h_ind_ae, integral_indicator_one h_meas_set]
    refine measureReal_congr ?_
    filter_upwards [hY'_ae] with ω h_eq
    simp [X, h_eq]
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) := by
    have h_sum : (fun ω ↦ (W ω : ℝ)) = fun ω ↦ ∑ i : Fin n, (X i ω : ℝ) := by
      funext ω
      simp [W]
    rw [h_sum, integral_finsetSum Finset.univ fun i _ ↦
      hint_comp (fun y ↦ (f i y : ℝ)), hr_eq]
    exact Finset.sum_congr rfl fun i _ ↦ hX_mean i
  -- Handle `r = 0` boundary case directly
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with hr0 | hr_pos
  · subst hr0
    have hW_zero : ∀ᵐ ω ∂P, W ω = 0 := by
      have h_int0 : ∫ ω, (W ω : ℝ) ∂P = 0 := by simpa using hW_mean
      have h_nn : 0 ≤ᵐ[P] fun ω ↦ (W ω : ℝ) :=
        Filter.Eventually.of_forall fun ω ↦ Nat.cast_nonneg _
      have h_ae0 := (integral_eq_zero_iff_of_nonneg_ae h_nn
        (hint_comp (fun y ↦ ((∑ i : Fin n, f i y : ℕ) : ℝ)))).mp h_int0
      filter_upwards [h_ae0] with ω hω
      exact Nat.cast_eq_zero.mp hω
    have hpo_0 : (poissonLaw 0).real {0} = 1 := by
      simpa [poissonLaw] using ProbabilityTheory.poissonMeasure_real_singleton 0 0
    refine tvDist_le_of_forall_measurableSet _ _ fun A hA ↦ ?_
    rw [map_measureReal_apply_of_aemeasurable hW_meas hA]
    have hP_A : P.real (W ⁻¹' A) = P.real {ω : Ω | (0 : ℕ) ∈ A} := by
      refine measureReal_congr ?_
      filter_upwards [hW_zero] with ω hω
      simp [hω]
    rw [hP_A]
    by_cases h0A : (0 : ℕ) ∈ A
    · have hP1 : P.real {ω : Ω | (0 : ℕ) ∈ A} = 1 := by simp [h0A]
      have hpo1 : (poissonLaw 0).real A = 1 :=
        le_antisymm measureReal_le_one
          (hpo_0 ▸ measureReal_mono (Set.singleton_subset_iff.mpr h0A))
      rw [hP1, hpo1]
      simp
    · have hP0 : P.real {ω : Ω | (0 : ℕ) ∈ A} = 0 := by simp [h0A]
      have hpo0 : (poissonLaw 0).real A = 0 := by
        refine le_antisymm ?_ measureReal_nonneg
        have hsub : A ⊆ ({0} : Set ℕ)ᶜ :=
          fun x hx hx0 ↦ h0A (Set.mem_singleton_iff.mp hx0 ▸ hx)
        calc (poissonLaw 0).real A
          _ ≤ (poissonLaw 0).real ({0} : Set ℕ)ᶜ := measureReal_mono hsub
          _ = 1 - (poissonLaw 0).real {0} := probReal_compl_eq_one_sub .of_discrete
          _ = 0 := by linarith
      rw [hP0, hpo0]
      simp
  · -- Main case `0 < r`
    refine tvDist_le_of_forall_measurableSet _ _ fun A hA ↦ ?_
    rw [map_measureReal_apply_of_aemeasurable hW_meas hA]
    change ENNReal.ofReal |P.real {ω | W ω ∈ A} - (poissonLaw r).real A| ≤ _
    rw [abs_measureReal_sub_poissonLaw_eq P hr_pos hW_meas A]
    refine ENNReal.ofReal_le_ofReal ?_
    set g : ℕ → ℝ := poissonSteinSol r A
    set C : ℝ := min 1 (r : ℝ)⁻¹
    have hC_nn : 0 ≤ C := le_min zero_le_one (inv_nonneg.mpr (NNReal.coe_nonneg r))
    have hg_diff : ∀ k : ℕ, |fwdDiff 1 g k| ≤ C := fun k ↦
      (abs_fwdDiff_poissonSteinSol_le hr_pos A k).trans (one_sub_exp_neg_div_le_min hr_pos)
    let W_i : Fin n → (Fin N → ℕ) → ℕ :=
      fun i y ↦ ∑ j ∈ Finset.univ.erase i, f j y
    let W_y : (Fin N → ℕ) → ℕ := fun y ↦ ∑ i : Fin n, f i y
    have h_decomp : (fun ω ↦ (r : ℝ) * g (W ω + 1) - (W ω : ℝ) * g (W ω)) =ᵐ[P]
        fun ω ↦ ∑ i : Fin n,
          (p i * (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) -
            ((X i ω : ℝ) - p i) * g (W_i i (fun j ↦ Y j ω) + 1)) := by
      filter_upwards [hX_all01] with ω hω
      have h_xg : ∀ i : Fin n,
          (X i ω : ℝ) * g (W ω) = (X i ω : ℝ) * g (W_i i (fun j ↦ Y j ω) + 1) := by
        intro i
        have h_add : W ω = W_i i (fun j ↦ Y j ω) + X i ω :=
          (Finset.sum_erase_add Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)).symm
        rcases hω i with h0 | h1
        · simp [h0]
        · rw [h_add, h1]
      have h_sum_xg : (W ω : ℝ) * g (W ω) =
          ∑ i : Fin n, (X i ω : ℝ) * g (W_i i (fun j ↦ Y j ω) + 1) := by
        have hW_cast : (W ω : ℝ) = ∑ i : Fin n, (X i ω : ℝ) := by simp [W]
        rw [hW_cast, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ h_xg i
      have h_r_sum : (r : ℝ) * g (W ω + 1) = ∑ i : Fin n, p i * g (W ω + 1) := by
        rw [hr_eq, Finset.sum_mul]
      rw [h_r_sum, h_sum_xg, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [integral_congr_ae h_decomp,
      integral_finsetSum Finset.univ fun i _ ↦
        hint_comp (fun y ↦ p i * (g (W_y y + 1) - g (W_i i y + 1)) -
          ((f i y : ℝ) - p i) * g (W_i i y + 1))]
    -- Bound each summand `i : Fin n`
    have h_term_bound : ∀ i : Fin n,
        |∫ ω, (p i * (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) -
            ((X i ω : ℝ) - p i) * g (W_i i (fun j ↦ Y j ω) + 1)) ∂P| ≤
          C * p i ^ 2 +
            C * ∫ ω, ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ) ∂P := by
      intro i
      have hp_nn : 0 ≤ p i := measureReal_nonneg
      have h_int1 := hint_comp (fun y ↦ p i * (g (W_y y + 1) - g (W_i i y + 1)))
      have h_int2 := hint_comp (fun y ↦ ((f i y : ℝ) - p i) * g (W_i i y + 1))
      rw [integral_sub h_int1 h_int2]
      -- Bound first integral by `C * p i ^ 2`
      have h_b1 : |∫ ω, p i * (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) ∂P| ≤
          C * p i ^ 2 := by
        rw [integral_const_mul, abs_mul, abs_of_nonneg hp_nn]
        have h_pw : ∀ᵐ ω ∂P,
            |g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)| ≤ C * (X i ω : ℝ) := by
          filter_upwards [hX_01 i] with ω h01
          have h_add : W ω = W_i i (fun j ↦ Y j ω) + X i ω :=
            (Finset.sum_erase_add Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)).symm
          rcases h01 with h0 | h1
          · rw [h_add, h0]
            simp
          · rw [h_add, h1]
            simpa [fwdDiff] using hg_diff (W_i i (fun j ↦ Y j ω) + 1)
        have h_abs_le : |∫ ω, (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) ∂P| ≤
            C * p i := by
          calc |∫ ω, (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) ∂P|
            _ ≤ ∫ ω, |g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)| ∂P :=
              abs_integral_le_integral_abs
            _ ≤ ∫ ω, C * (X i ω : ℝ) ∂P :=
              integral_mono_ae
                (hint_comp (fun y ↦ |g (W_y y + 1) - g (W_i i y + 1)|))
                (hint_comp (fun y ↦ C * (f i y : ℝ))) h_pw
            _ = C * p i := by rw [integral_const_mul, hX_mean i]
        calc p i * |∫ ω, (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) ∂P|
          _ ≤ p i * (C * p i) := mul_le_mul_of_nonneg_left h_abs_le hp_nn
          _ = C * p i ^ 2 := by ring
      -- Bound second integral via FKG and finite telescoping
      have hWi_le : ∀ᵐ ω ∂P, W_i i (fun j ↦ Y j ω) ≤ n := by
        filter_upwards [hX_all01] with ω hω
        calc W_i i (fun j ↦ Y j ω)
          _ = ∑ j ∈ Finset.univ.erase i, X j ω := rfl
          _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
            refine Finset.sum_le_sum fun j _ ↦ ?_
            rcases hω j with h0 | h1 <;> omega
          _ = (Finset.univ.erase i).card := by simp
          _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
          _ = n := Fintype.card_fin n
      let ind_m : ℕ → (Fin N → ℕ) → ℝ :=
        fun m y ↦ if m + 1 ≤ W_i i y then 1 else 0
      have h_tele_g : (fun ω ↦ ((X i ω : ℝ) - p i) * g (W_i i (fun j ↦ Y j ω) + 1)) =ᵐ[P]
          fun ω ↦ ((X i ω : ℝ) - p i) * g 1 +
            ∑ m ∈ Finset.range n,
              fwdDiff 1 g (m + 1) * (((X i ω : ℝ) - p i) * ind_m m (fun j ↦ Y j ω)) := by
        filter_upwards [hWi_le] with ω hle
        rw [fn_succ_eq_fn_one_add_sum_fwdDiff hle g, mul_add, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        ring
      have h_tele_W : (fun ω ↦ ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ)) =ᵐ[P]
          fun ω ↦ ∑ m ∈ Finset.range n,
            ((X i ω : ℝ) - p i) * ind_m m (fun j ↦ Y j ω) := by
        filter_upwards [hWi_le] with ω hle
        rw [nat_cast_eq_sum_indicator_range hle, Finset.mul_sum]
      have h_mean_zero : ∫ ω, ((X i ω : ℝ) - p i) * g 1 ∂P = 0 := by
        rw [integral_mul_const, integral_sub (hint_comp (fun y ↦ (f i y : ℝ)))
          (integrable_const (p i)), hX_mean i, integral_const, probReal_univ, one_smul,
          sub_self, zero_mul]
      have h_cov_nonneg : ∀ m : ℕ,
          0 ≤ ∫ ω, ((X i ω : ℝ) - p i) * ind_m m (fun j ↦ Y j ω) ∂P := by
        intro m
        have h_sub_eq : (fun ω ↦ ((X i ω : ℝ) - p i) * ind_m m (fun j ↦ Y j ω)) =
            fun ω ↦ (X i ω : ℝ) * ind_m m (fun j ↦ Y j ω) -
              p i * ind_m m (fun j ↦ Y j ω) := by
          funext ω
          ring
        rw [h_sub_eq, integral_sub (hint_comp (fun y ↦ (f i y : ℝ) * ind_m m y))
          (hint_comp (fun y ↦ p i * ind_m m y)), integral_const_mul, ← hX_mean i, sub_nonneg]
        exact fkg_independent_indicators_on P (g := fun y ↦ (f i y : ℝ)) (h := ind_m m)
          hY_meas hY_01 hY_indep (by
          rcases hf_mono with h_inc | h_dec
          · left
            refine ⟨fun a ha b hb hab ↦ Nat.cast_le.mpr (h_inc i ha hb hab),
              fun a ha b hb hab ↦ ?_⟩
            have h_sum_le : W_i i a ≤ W_i i b :=
              Finset.sum_le_sum fun j _ ↦ h_inc j ha hb hab
            by_cases h1 : m + 1 ≤ W_i i a <;> by_cases h2 : m + 1 ≤ W_i i b
            · simp only [ind_m, h1, h2, ↓reduceIte, le_rfl]
            · exact False.elim (h2 (le_trans h1 h_sum_le))
            · simp only [ind_m, h1, h2, ↓reduceIte, zero_le_one]
            · simp only [ind_m, h1, h2, ↓reduceIte, le_rfl]
          · right
            refine ⟨fun a ha b hb hab ↦ Nat.cast_le.mpr (h_dec i ha hb hab),
              fun a ha b hb hab ↦ ?_⟩
            have h_sum_le : W_i i b ≤ W_i i a :=
              Finset.sum_le_sum fun j _ ↦ h_dec j ha hb hab
            by_cases h1 : m + 1 ≤ W_i i b <;> by_cases h2 : m + 1 ≤ W_i i a
            · simp only [ind_m, h1, h2, ↓reduceIte, le_rfl]
            · exact False.elim (h2 (le_trans h1 h_sum_le))
            · simp only [ind_m, h1, h2, ↓reduceIte, zero_le_one]
            · simp only [ind_m, h1, h2, ↓reduceIte, le_rfl])
      have h_b2 : |∫ ω, ((X i ω : ℝ) - p i) * g (W_i i (fun j ↦ Y j ω) + 1) ∂P| ≤
          C * ∫ ω, ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ) ∂P := by
        rw [integral_congr_ae h_tele_g,
          integral_add (hint_comp (fun y ↦ ((f i y : ℝ) - p i) * g 1))
            (hint_comp (fun y ↦ ∑ m ∈ Finset.range n,
              fwdDiff 1 g (m + 1) * (((f i y : ℝ) - p i) * ind_m m y))),
          h_mean_zero, zero_add,
          integral_finsetSum (Finset.range n) fun m _ ↦
            hint_comp (fun y ↦ fwdDiff 1 g (m + 1) * (((f i y : ℝ) - p i) * ind_m m y)),
          integral_congr_ae h_tele_W,
          integral_finsetSum (Finset.range n) fun m _ ↦
            hint_comp (fun y ↦ ((f i y : ℝ) - p i) * ind_m m y),
          Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
        rw [integral_const_mul, abs_mul, abs_of_nonneg (h_cov_nonneg m)]
        exact mul_le_mul_of_nonneg_right (hg_diff (m + 1)) (h_cov_nonneg m)
      exact (abs_sub _ _).trans (add_le_add h_b1 h_b2)
    -- Sum `h_term_bound` over `i : Fin n` and identify variance
    have h_var_id :
        (∑ i : Fin n, ∫ ω, ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ) ∂P) =
          ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
            ∑ i : Fin n, p i ^ 2 := by
      rw [← integral_finsetSum Finset.univ fun i _ ↦
        hint_comp (fun y ↦ ((f i y : ℝ) - p i) * (W_i i y : ℝ))]
      have h_alg :
          (fun ω ↦ ∑ i : Fin n,
            ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ)) =ᵐ[P]
          fun ω ↦ ((W ω : ℝ) - (r : ℝ)) ^ 2 + ((W ω : ℝ) - (r : ℝ)) * (r : ℝ) -
            (W ω : ℝ) + ∑ i : Fin n, p i * (X i ω : ℝ) := by
        filter_upwards [hX_all01] with ω hω
        have hWi_sub : ∀ i : Fin n,
            (W_i i (fun j ↦ Y j ω) : ℝ) = (W ω : ℝ) - (X i ω : ℝ) := by
          intro i
          have h_add : W ω = W_i i (fun j ↦ Y j ω) + X i ω :=
            (Finset.sum_erase_add Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)).symm
          have h_cast : (W ω : ℝ) = (W_i i (fun j ↦ Y j ω) : ℝ) + (X i ω : ℝ) := by
            exact_mod_cast h_add
          linarith
        have hX_sq : ∀ i : Fin n, (X i ω : ℝ) ^ 2 = (X i ω : ℝ) := by
          intro i
          rcases hω i with h0 | h1
          · simp [h0]
          · simp [h1]
        have h_each : ∀ i : Fin n,
            ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ) =
              ((X i ω : ℝ) - p i) * (W ω : ℝ) - (X i ω : ℝ) + p i * (X i ω : ℝ) := by
          intro i
          rw [hWi_sub i]
          calc ((X i ω : ℝ) - p i) * ((W ω : ℝ) - (X i ω : ℝ))
            _ = ((X i ω : ℝ) - p i) * (W ω : ℝ) - (X i ω : ℝ) ^ 2 +
                p i * (X i ω : ℝ) := by ring
            _ = ((X i ω : ℝ) - p i) * (W ω : ℝ) - (X i ω : ℝ) + p i * (X i ω : ℝ) := by
              rw [hX_sq i]
        simp_rw [h_each]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          Finset.sum_sub_distrib, ← hr_eq]
        have hW_cast : (∑ x : Fin n, (X x ω : ℝ)) = (W ω : ℝ) := by simp [W]
        rw [hW_cast]
        ring
      have hW_memLp : MemLp (fun ω ↦ (W ω : ℝ)) 2 P := by
        have hW_aesm :=
          (hint_comp (fun y ↦ ((∑ i : Fin n, f i y : ℕ) : ℝ))).aestronglyMeasurable
        refine (memLp_top_of_bound hW_aesm n ?_).mono_exponent le_top
        filter_upwards [hX_all01] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        have hle : W ω ≤ n := by
          calc W ω = ∑ i : Fin n, X i ω := rfl
            _ ≤ ∑ _i : Fin n, 1 := by
              refine Finset.sum_le_sum fun i _ ↦ ?_
              rcases hω i with h0 | h1 <;> omega
            _ = n := by simp
        exact_mod_cast hle
      have h_var_eq : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
          ∫ ω, ((W ω : ℝ) - (r : ℝ)) ^ 2 ∂P := by
        rw [ProbabilityTheory.variance_eq_integral hW_memLp.aemeasurable, hW_mean]
      have h_lin_zero : ∫ ω, ((W ω : ℝ) - (r : ℝ)) * (r : ℝ) ∂P = 0 := by
        rw [integral_mul_const, integral_sub (hint_comp (fun y ↦ (W_y y : ℝ)))
          (integrable_const (r : ℝ)), hW_mean, integral_const, probReal_univ, one_smul,
          sub_self, zero_mul]
      have h_sum_pX :
          ∫ ω, (∑ i : Fin n, p i * (X i ω : ℝ)) ∂P = ∑ i : Fin n, p i ^ 2 := by
        rw [integral_finsetSum Finset.univ fun i _ ↦ hint_comp (fun y ↦ p i * (f i y : ℝ))]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [integral_const_mul, hX_mean i, sq]
      rw [integral_congr_ae h_alg,
        integral_add (hint_comp (fun y ↦ ((W_y y : ℝ) - (r : ℝ)) ^ 2 +
            ((W_y y : ℝ) - (r : ℝ)) * (r : ℝ) - (W_y y : ℝ)))
          (hint_comp (fun y ↦ ∑ i : Fin n, p i * (f i y : ℝ))),
        integral_sub (hint_comp (fun y ↦ ((W_y y : ℝ) - (r : ℝ)) ^ 2 +
            ((W_y y : ℝ) - (r : ℝ)) * (r : ℝ)))
          (hint_comp (fun y ↦ (W_y y : ℝ))),
        integral_add (hint_comp (fun y ↦ ((W_y y : ℝ) - (r : ℝ)) ^ 2))
          (hint_comp (fun y ↦ ((W_y y : ℝ) - (r : ℝ)) * (r : ℝ))),
        ← h_var_eq, h_lin_zero, add_zero, hW_mean, h_sum_pX]
    calc |∑ i : Fin n, ∫ ω,
          (p i * (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) -
            ((X i ω : ℝ) - p i) * g (W_i i (fun j ↦ Y j ω) + 1)) ∂P|
      _ ≤ ∑ i : Fin n, |∫ ω,
          (p i * (g (W ω + 1) - g (W_i i (fun j ↦ Y j ω) + 1)) -
            ((X i ω : ℝ) - p i) * g (W_i i (fun j ↦ Y j ω) + 1)) ∂P| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n,
          (C * p i ^ 2 +
            C * ∫ ω, ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ) ∂P) :=
        Finset.sum_le_sum fun i _ ↦ h_term_bound i
      _ = C * (∑ i : Fin n, p i ^ 2) +
          C * (∑ i : Fin n,
            ∫ ω, ((X i ω : ℝ) - p i) * (W_i i (fun j ↦ Y j ω) : ℝ) ∂P) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = C * (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
          2 * ∑ i : Fin n, p i ^ 2) := by
        rw [h_var_id]
        ring

/-- **Refutation of Reading (A) of Theorem 4.17** (`\label{thm124}`, `SteinIntro.tex:2382-2390`;
`ISSUE-4.17`): when $X_1 = Y_1$ (increasing) and $X_2 = 1 - Y_1$ (decreasing) for
$Y_1 \sim \mathrm{Ber}(1/2)$, $W = X_1 + X_2 \equiv 1$ has $\operatorname{Var}(W) = 0$,
$\lambda = 1$, and $p_1 = p_2 = 1/2$, so the printed upper bound is
$0 < d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1))$. -/
theorem not_thm4_17_printed :
    ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {N n : ℕ} {Y : Fin N → Ω → ℕ} {f : Fin n → (Fin N → ℕ) → ℕ}
        {r : ℝ≥0} {Z : Ω' → ℕ},
        (∀ j : Fin N, AEMeasurable (Y j) P) →
        (∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1) →
        ProbabilityTheory.iIndepFun Y P →
        (∀ i : Fin n, ∀ y : Fin N → ℕ,
          (∀ j : Fin N, y j ≤ 1) → f i y = 0 ∨ f i y = 1) →
        (∀ i : Fin n,
          MonotoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} ∨
          AntitoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) →
        let X : Fin n → Ω → ℕ := fun i ω ↦ f i (fun j ↦ Y j ω)
        let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
        let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
        (r : ℝ) = ∑ i : Fin n, p i →
        AEMeasurable Z P' →
        P'.map Z = poissonLaw r →
        tvDist (P.map W) (P'.map Z) ≤
          ENNReal.ofReal
            (min 1 (r : ℝ)⁻¹ *
              (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
                2 * ∑ i : Fin n, p i ^ 2))) := by
  intro h_printed
  let P : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
  let P' : Measure ℕ := poissonLaw 1
  let Y : Fin 1 → Bool → ℕ := fun _ b ↦ if b then 1 else 0
  let f : Fin 2 → (Fin 1 → ℕ) → ℕ :=
    ![fun y ↦ min (y 0) 1, fun y ↦ 1 - min (y 0) 1]
  have hY_meas : ∀ j : Fin 1, AEMeasurable (Y j) P :=
    fun _ ↦ Measurable.of_discrete.aemeasurable
  have hY_01 : ∀ j : Fin 1, ∀ᵐ b ∂P, Y j b = 0 ∨ Y j b = 1 :=
    fun _ ↦ Filter.Eventually.of_forall fun b ↦ by cases b <;> simp [Y]
  have hY_indep : ProbabilityTheory.iIndepFun Y P := by
    refine ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mpr fun S {sets} _ ↦ ?_
    have hS : S = ∅ ∨ S = {0} := by
      rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · exact Or.inl rfl
      · right
        have hx0 : x = 0 := Fin.eq_zero x
        subst hx0
        ext y
        rw [Fin.eq_zero y]
        simpa using hx
    rcases hS with rfl | rfl
    · have h_empty : (⋂ i ∈ (∅ : Finset (Fin 1)), Y i ⁻¹' sets i) = Set.univ := by
        ext b
        simp
      rw [h_empty, Finset.prod_empty, measure_univ]
    · simp
  have hf_01 : ∀ i : Fin 2, ∀ y : Fin 1 → ℕ,
      (∀ j : Fin 1, y j ≤ 1) → f i y = 0 ∨ f i y = 1 := by
    intro i y _
    have h01 : min (y 0) 1 = 0 ∨ min (y 0) 1 = 1 := by omega
    rcases h01 with h0 | h1
    · fin_cases i <;> simp [f, h0]
    · fin_cases i <;> simp [f, h1]
  have hf_mono : ∀ i : Fin 2,
      MonotoneOn (f i) {y : Fin 1 → ℕ | ∀ j : Fin 1, y j ≤ 1} ∨
      AntitoneOn (f i) {y : Fin 1 → ℕ | ∀ j : Fin 1, y j ≤ 1} := by
    intro i
    fin_cases i
    · left
      intro a _ b _ hab
      simpa [f] using min_le_min_right 1 (hab 0)
    · right
      intro a _ b _ hab
      simpa [f] using Nat.sub_le_sub_left (min_le_min_right 1 (hab 0)) 1
  let X : Fin 2 → Bool → ℕ := fun i b ↦ f i (fun j ↦ Y j b)
  let p : Fin 2 → ℝ := fun i ↦ P.real {b | X i b = 1}
  let W : Bool → ℕ := fun b ↦ ∑ i : Fin 2, X i b
  have hp0 : p 0 = 1 / 2 := by
    have hset : {b : Bool | X 0 b = 1} = {true} := by
      ext b
      cases b <;> simp [X, Y, f]
    simp only [p, hset, P, measureReal_def, PMF.toMeasure_apply_singleton _ _ .of_discrete,
      PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num
  have hp1 : p 1 = 1 / 2 := by
    have hset : {b : Bool | X 1 b = 1} = {false} := by
      ext b
      cases b <;> simp [X, Y, f]
    simp only [p, hset, P, measureReal_def, PMF.toMeasure_apply_singleton _ _ .of_discrete,
      PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num
  have hr_eq : ((1 : ℝ≥0) : ℝ) = ∑ i : Fin 2, p i := by
    rw [Fin.sum_univ_two, hp0, hp1]
    norm_num
  have hW_const : W = fun _ : Bool ↦ 1 := by
    funext b
    cases b <;> decide
  have h_map_id : P'.map (id : ℕ → ℕ) = poissonLaw 1 := Measure.map_id
  have h_ineq := h_printed P P' (r := 1) (Z := id) hY_meas hY_01 hY_indep hf_01 hf_mono hr_eq
    aemeasurable_id h_map_id
  dsimp only at h_ineq
  change tvDist (P.map W) (P'.map id) ≤
    ENNReal.ofReal
      (min 1 ((1 : ℝ≥0) : ℝ)⁻¹ *
        (ProbabilityTheory.variance (fun b ↦ (W b : ℝ)) P - ((1 : ℝ≥0) : ℝ) +
          2 * ∑ i : Fin 2, p i ^ 2)) at h_ineq
  have h_var0 : ProbabilityTheory.variance (fun b ↦ (W b : ℝ)) P = 0 := by
    rw [hW_const, ProbabilityTheory.variance_eq_integral aemeasurable_const]
    have h_int1 : ∫ _ : Bool, (1 : ℝ) ∂P = 1 := by
      rw [integral_const, probReal_univ, one_smul]
    simp [h_int1]
  have h_rhs0 : min 1 ((1 : ℝ≥0) : ℝ)⁻¹ *
      (ProbabilityTheory.variance (fun b ↦ (W b : ℝ)) P - ((1 : ℝ≥0) : ℝ) +
        2 * ∑ i : Fin 2, p i ^ 2) = 0 := by
    rw [h_var0, Fin.sum_univ_two, hp0, hp1]
    norm_num
  rw [h_rhs0, ENNReal.ofReal_zero, Measure.map_id] at h_ineq
  have : IsFiniteMeasure (P.map W) := by
    constructor
    rw [Measure.map_apply Measurable.of_discrete MeasurableSet.univ]
    exact measure_lt_top P _
  have h_lb : ENNReal.ofReal |(P.map W).real {0} - P'.real {0}| ≤ tvDist (P.map W) P' :=
    le_tvDist_of_measurableSet (P.map W) P' (measurableSet_singleton 0)
  have hW_zero : (P.map W).real {0} = 0 := by
    rw [map_measureReal_apply Measurable.of_discrete (measurableSet_singleton 0)]
    have hpre : W ⁻¹' {0} = ∅ := by
      ext b
      cases b <;> simp [W, X, Y, f]
    simp [hpre]
  have hP'_zero : P'.real {0} = Real.exp (-1) := by
    simpa [P', poissonLaw] using ProbabilityTheory.poissonMeasure_real_singleton 1 0
  rw [hW_zero, hP'_zero, zero_sub, abs_neg, abs_of_pos (Real.exp_pos (-1))] at h_lb
  have h_pos : (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-1)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos (-1))
  exact not_lt_of_ge (h_lb.trans h_ineq) h_pos


/-- Alias of `not_thm4_17_printed` matching the `Sec4` naming convention (`ISSUE-4.17`). -/
alias not_Thm4_17_printed := not_thm4_17_printed

end SteinMethod
