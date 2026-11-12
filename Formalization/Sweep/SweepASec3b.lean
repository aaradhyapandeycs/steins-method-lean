/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.DependencyCount
import Formalization.Normal.DependencyNeighborhoods
import Formalization.Normal.IndependentSums
import Formalization.Normal.WassersteinBound
import Mathlib.Probability.Independence.Basic

/-!
# Section 3.2 Gap Proofs (`SWEEP-A`: `A10`, `A11`)

Proves the Section 3.2 dependency-neighborhood claims in Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `sec3_2_indep_isDependencyGraph_proof` (`SteinIntro.tex:827-828`, `A10`): mutually independent
  random variables satisfy both `HasDependencyNeighborhoods` and `IsDependencyGraph` with
  singleton neighborhoods $N_i = \{i\}$ (and $D = 1$ when $n \ge 1$).
* `sec3_2_depNeighborhoods_intermediate_bound_proof` (`SteinIntro.tex:908-911`, `A11`): under
  Definition 3.1 (`HasDependencyNeighborhoods P X N`),
  $\sigma^2 = \mathbb{E}[\sum_i X_i \sum_{j \in N_i} X_j]$ and $d_{\mathrm{W}}(W, Z)$ is bounded
  by the sum of intermediate terms `(3.11)` and `(3.12)`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Independent Summands as Dependency Graph (`A10`) -/

/-- Library proof of `Sec3_2_indep_isDependencyGraph` (`SteinIntro.tex:827-828`). -/
theorem sec3_2_indep_isDependencyGraph_proof
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX_indep : ProbabilityTheory.iIndepFun X P) :
    HasDependencyNeighborhoods P X (fun i ↦ {i}) ∧
    IsDependencyGraph P X (fun i ↦ {i}) ∧
    (0 < n → (Finset.univ.sup fun i : Fin n ↦ ({i} : Finset (Fin n)).card) = 1) := by
  have hG : IsDependencyGraph P X (fun i ↦ {i}) := by
    refine ⟨fun i ↦ Finset.mem_singleton_self i, fun i j hij ↦ ?_, fun A B hAB ↦ ?_⟩
    · rw [Finset.mem_singleton.mp hij]
      exact Finset.mem_singleton_self i
    · have hdisj : Disjoint A B := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        have hnot := hAB a ha b hb
        rw [Finset.mem_singleton] at hnot
        exact Ne.symm hnot
      exact hX_indep.indepFun_finset₀ A B hdisj hX_meas
  have hN : HasDependencyNeighborhoods P X (fun i ↦ {i}) :=
    hG.hasDependencyNeighborhoods
  have hD (hn : 0 < n) : (Finset.univ.sup fun i : Fin n ↦ ({i} : Finset (Fin n)).card) = 1 := by
    have i0 : Fin n := ⟨0, hn⟩
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le fun i _ ↦ ?_
      rw [Finset.card_singleton]
    · have hmem : i0 ∈ Finset.univ := Finset.mem_univ i0
      have hcard : ({i0} : Finset (Fin n)).card = 1 := Finset.card_singleton i0
      rw [← hcard]
      exact Finset.le_sup (f := fun i ↦ ({i} : Finset (Fin n)).card) hmem
  exact ⟨hN, hG, hD⟩

/-! ### Section 2: Intermediate Dependency-Neighborhood Bound (`A11`) -/

private lemma hasDependencyNeighborhoods_indep_pair
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hN : HasDependencyNeighborhoods P X N)
    {i k : Fin n} (hk : k ∉ N i) :
    ProbabilityTheory.IndepFun (X i) (X k) P := by
  let π : ({j // j ∉ N i} → ℝ) → ℝ := fun g ↦ g ⟨k, hk⟩
  have hπ : Measurable π := measurable_pi_apply (⟨k, hk⟩ : {j // j ∉ N i})
  exact (hN i).comp measurable_id hπ

private lemma hasDependencyNeighborhoods_integral_quadSum_eq_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hN : HasDependencyNeighborhoods P X N) :
    (∫ ω, ∑ i : Fin n, X i ω * ∑ j ∈ N i, X j ω ∂P) =
      ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P := by
  have hsum_meas : AEMeasurable (fun ω ↦ ∑ i : Fin n, X i ω) P :=
    Finset.univ.aemeasurable_fun_sum fun i _ ↦ hX_meas i
  have hsum_int_zero : (∫ ω, ∑ i : Fin n, X i ω ∂P) = 0 := by
    rw [integral_finsetSum Finset.univ fun i _ ↦ depGraph_integrable_of_memLp_four (hX4 i)]
    simp [hX0]
  rw [ProbabilityTheory.variance_of_integral_eq_zero hsum_meas hsum_int_zero]
  have hsq_exp : (fun ω ↦ (∑ i : Fin n, X i ω) ^ 2) =
      fun ω ↦ ∑ i : Fin n, ∑ k : Fin n, X i ω * X k ω := by
    ext ω
    rw [sq, Fintype.sum_mul_sum]
  rw [hsq_exp]
  rw [integral_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  have heq_pt : (fun ω ↦ ∑ i : Fin n, X i ω * ∑ j ∈ N i, X j ω) =
      fun ω ↦ ∑ i : Fin n, ∑ j ∈ N i, X i ω * X j ω := by
    ext ω
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
  rw [heq_pt]
  rw [integral_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum (N i) fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum (N i) fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  rw [integral_finsetSum Finset.univ fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  refine Finset.sum_subset (s₁ := N i) (s₂ := Finset.univ)
    (f := fun k ↦ ∫ ω, X i ω * X k ω ∂P) (Finset.subset_univ (N i)) fun k _ hk ↦ ?_
  have hind := hasDependencyNeighborhoods_indep_pair hN hk
  rw [hind.integral_fun_mul_eq_mul_integral
    (hX_meas i).aestronglyMeasurable (hX_meas k).aestronglyMeasurable, hX0 i, zero_mul]

/-- Library proof of `Sec3_2_depNeighborhoods_intermediate_bound` (`SteinIntro.tex:908-911`). -/
theorem sec3_2_depNeighborhoods_intermediate_bound_proof
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hN : HasDependencyNeighborhoods P X N)
    (hVar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    let σ2 : ℝ := ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P
    let σ : ℝ := Real.sqrt σ2
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / σ
    σ2 = (∫ ω, ∑ i : Fin n, X i ω * ∑ j ∈ N i, X j ω ∂P) ∧
      wassersteinDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (1 / σ ^ 3 *
              (∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i,
                ∫ ω, |X i ω * X j ω * X k ω| ∂P) +
            Real.sqrt 2 / (Real.sqrt Real.pi * σ ^ 2) *
              Real.sqrt
                (ProbabilityTheory.variance
                  (fun ω ↦ ∑ i : Fin n, ∑ j ∈ N i, X i ω * X j ω) P)) := by
  intro σ2 σ W
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  have hσ_ne : σ ≠ 0 := hσ_pos.ne'
  have hσ_sq : σ ^ 2 = σ2 := Real.sq_sqrt hVar.le
  have hσ2_eq : σ2 = (∫ ω, ∑ i : Fin n, X i ω * ∑ j ∈ N i, X j ω ∂P) :=
    (hasDependencyNeighborhoods_integral_quadSum_eq_variance P hX_meas hX4 hX0 hN).symm
  refine ⟨hσ2_eq, ?_⟩
  let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ (N i)ᶜ, X j ω) / σ
  let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, ∑ k ∈ N i, X i ω * X k ω
  have hW_meas : AEMeasurable W P := depGraph_aemeasurable_W hX_meas
  have hWi_meas (i : Fin n) : AEMeasurable (W_i i) P :=
    ((N i)ᶜ.aemeasurable_fun_sum fun j _ ↦ hX_meas j).div_const σ
  have hW_sub (i : Fin n) (ω : Ω) : W ω - W_i i ω = (∑ j ∈ N i, X j ω) / σ := by
    dsimp only [W, W_i]
    rw [← Finset.sum_add_sum_compl (N i) (fun j ↦ X j ω)]
    ring
  have hS_memLp2 : MemLp S 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦
      memLp_finsetSum (N i) fun k _ ↦ memLp_two_mul_of_memLp_four (hX4 i) (hX4 k)
  have hWass := wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P' hW_meas hZ hZ_law
  refine hWass.trans ?_
  refine iSup₂_le fun f hf ↦ ENNReal.ofReal_le_ofReal ?_
  have ⟨hdf, hddf, hf_bound, hdf_bound, hdd_bound⟩ := hf
  have hf_meas : Measurable f := hdf.continuous.measurable
  have hdf_meas : Measurable (deriv f) := hddf.continuous.measurable
  let T_i : Fin n → Ω → ℝ := fun i ω ↦
    X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))
  let A : Ω → ℝ := fun ω ↦ (1 / σ) * ∑ i : Fin n, T_i i ω
  let B : Ω → ℝ := fun ω ↦
    deriv f (W ω) * (1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω))
  let C : Ω → ℝ := fun ω ↦ (1 / σ) * ∑ i : Fin n, X i ω * f (W_i i ω)
  have h_stein_pt (ω : Ω) : normalSteinOp f (W ω) = -A ω + B ω - C ω := by
    have h1 : (∑ i : Fin n, X i ω) * f (W ω) = ∑ i : Fin n, X i ω * f (W ω) :=
      Finset.sum_mul Finset.univ (fun i ↦ X i ω) (f (W ω))
    have h2 : deriv f (W ω) * (1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω)) =
        deriv f (W ω) - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
      have hm : deriv f (W ω) * ((1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω)) =
          (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
        calc deriv f (W ω) * ((1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω))
            = (1 / σ) * ((∑ i : Fin n, X i ω * (W ω - W_i i ω)) * deriv f (W ω)) := by ring
          _ = (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
              rw [Finset.sum_mul]
      calc deriv f (W ω) * (1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω))
          = deriv f (W ω) -
              deriv f (W ω) * ((1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω)) := by
            ring
        _ = deriv f (W ω) -
            (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
            rw [hm]
    have h3 : (∑ i : Fin n, T_i i ω) + (∑ i : Fin n, X i ω * f (W_i i ω)) +
        (∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) =
        ∑ i : Fin n, X i ω * f (W ω) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp only [T_i]
      ring
    have h4 : W ω * f (W ω) = (1 / σ) * ∑ i : Fin n, X i ω * f (W ω) := by
      have hw : W ω * f (W ω) = (1 / σ) * ((∑ i : Fin n, X i ω) * f (W ω)) := by
        change ((∑ i : Fin n, X i ω) / σ) * f (W ω) =
          (1 / σ) * ((∑ i : Fin n, X i ω) * f (W ω))
        ring
      rw [hw, h1]
    dsimp only [normalSteinOp, A, B, C]
    rw [h4, ← h3, h2]
    ring
  have hind_Wi (i : Fin n) : ProbabilityTheory.IndepFun (X i) (fun ω ↦ f (W_i i ω)) P := by
    let ψ : ({j // j ∉ N i} → ℝ) → ℝ := fun g ↦
      f ((∑ j : {j // j ∉ N i}, g j) / σ)
    have hψ : Measurable ψ :=
      hf_meas.comp
        ((Finset.univ.measurable_sum fun (j : {j // j ∉ N i}) _ ↦
          measurable_pi_apply j).div_const σ)
    have hc := (hN i).comp measurable_id hψ
    have heq : ψ ∘ (fun ω (j : {j // j ∉ N i}) ↦ X j ω) = fun ω ↦ f (W_i i ω) := by
      ext ω
      dsimp only [Function.comp_apply, ψ, W_i]
      rw [Finset.sum_subtype (N i)ᶜ (fun _ ↦ Finset.mem_compl) (fun j ↦ X j ω)]
    simpa only [Function.id_comp, heq] using hc
  have hfWi_meas (i : Fin n) : AEStronglyMeasurable (fun ω ↦ f (W_i i ω)) P :=
    (hf_meas.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
  have hint_Ci (i : Fin n) : Integrable (fun ω ↦ X i ω * f (W_i i ω)) P := by
    refine ((depGraph_integrable_of_memLp_four (hX4 i)).norm.mul_const 2).mono'
      ((hX_meas i).aestronglyMeasurable.mul (hfWi_meas i))
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf_bound (W_i i ω)) (abs_nonneg (X i ω))
  have hint_C : Integrable C P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ hint_Ci i).const_mul (1 / σ)
  have hC_zero : ∫ ω, C ω ∂P = 0 := by
    dsimp only [C]
    rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ hint_Ci i]
    have hz (i : Fin n) : ∫ ω, X i ω * f (W_i i ω) ∂P = 0 := by
      rw [(hind_Wi i).integral_fun_mul_eq_mul_integral
        (hX_meas i).aestronglyMeasurable (hfWi_meas i), hX0 i, zero_mul]
    simp [hz]
  have hTi_bound (i : Fin n) (ω : Ω) :
      |T_i i ω| ≤ (1 / σ ^ 2) * ∑ j ∈ N i, ∑ k ∈ N i, |X i ω * X j ω * X k ω| := by
    have htay := abs_sub_deriv_mul_le_half_sq hdf hddf hdd_bound (W ω) (W_i i ω)
    have hsq_sum : (∑ j ∈ N i, X j ω) ^ 2 ≤
        ∑ j ∈ N i, ∑ k ∈ N i, |X j ω * X k ω| := by
      have habs : |∑ j ∈ N i, X j ω| ≤ ∑ j ∈ N i, |X j ω| :=
        Finset.abs_sum_le_sum_abs (fun j ↦ X j ω) (N i)
      calc (∑ j ∈ N i, X j ω) ^ 2
          = |∑ j ∈ N i, X j ω| * |∑ j ∈ N i, X j ω| := by rw [← sq, sq_abs]
        _ ≤ (∑ j ∈ N i, |X j ω|) * (∑ k ∈ N i, |X k ω|) :=
            mul_le_mul habs habs (abs_nonneg _) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        _ = ∑ j ∈ N i, ∑ k ∈ N i, |X j ω| * |X k ω| :=
            Finset.sum_mul_sum (N i) (N i) (fun j ↦ |X j ω|) (fun k ↦ |X k ω|)
        _ = ∑ j ∈ N i, ∑ k ∈ N i, |X j ω * X k ω| := by
            simp_rw [abs_mul]
    calc |T_i i ω|
        = |X i ω| * |f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)| := abs_mul _ _
      _ ≤ |X i ω| * (W ω - W_i i ω) ^ 2 := by
          have ht2 : (2 / 2 : ℝ) * (W ω - W_i i ω) ^ 2 = (W ω - W_i i ω) ^ 2 := by ring
          rw [← ht2]
          exact mul_le_mul_of_nonneg_left htay (abs_nonneg (X i ω))
      _ = (1 / σ ^ 2) * (|X i ω| * (∑ j ∈ N i, X j ω) ^ 2) := by
          rw [hW_sub i ω, div_pow]
          ring
      _ ≤ (1 / σ ^ 2) * (|X i ω| * ∑ j ∈ N i, ∑ k ∈ N i, |X j ω * X k ω|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq_sum (abs_nonneg (X i ω))) (by positivity)
      _ = (1 / σ ^ 2) * ∑ j ∈ N i, ∑ k ∈ N i, |X i ω * X j ω * X k ω| := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          rw [abs_mul, abs_mul, abs_mul]
          ring
  have hTi_meas (i : Fin n) : AEStronglyMeasurable (T_i i) P := by
    have hm1 : AEMeasurable (fun ω ↦ f (W ω) - f (W_i i ω)) P :=
      (hf_meas.comp_aemeasurable hW_meas).fun_sub (hf_meas.comp_aemeasurable (hWi_meas i))
    have hm2 : AEMeasurable (fun ω ↦ (W ω - W_i i ω) * deriv f (W ω)) P :=
      (hW_meas.fun_sub (hWi_meas i)).fun_mul (hdf_meas.comp_aemeasurable hW_meas)
    exact ((hX_meas i).fun_mul (hm1.fun_sub hm2)).aestronglyMeasurable
  have hint_dom_i (i : Fin n) :
      Integrable (fun ω ↦ ∑ j ∈ N i, ∑ k ∈ N i, |X i ω * X j ω * X k ω|) P :=
    integrable_finsetSum (N i) fun j _ ↦
      integrable_finsetSum (N i) fun k _ ↦ by
        have heq : (fun ω ↦ |X i ω * X j ω * X k ω|) =
            fun ω ↦ |X i ω| * |X j ω| * |X k ω| := by
          ext ω
          rw [abs_mul, abs_mul]
        rw [heq]
        exact integrable_abs_mul_three (hX4 i) (hX4 j) (hX4 k)
  have hint_Ti (i : Fin n) : Integrable (T_i i) P := by
    refine ((hint_dom_i i).const_mul (1 / σ ^ 2)).mono' (hTi_meas i)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs] using hTi_bound i ω
  have hint_A : Integrable A P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ hint_Ti i).const_mul (1 / σ)
  have hB_inner (ω : Ω) :
      1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) = (σ ^ 2 - S ω) / σ ^ 2 := by
    have hsum : (∑ i : Fin n, X i ω * (W ω - W_i i ω)) = (1 / σ) * S ω := by
      dsimp only [S]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hW_sub i ω, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [hsum, sub_div, div_self (pow_ne_zero 2 hσ_ne)]
    congr 1
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  have h_diff_lp2 : MemLp (fun ω ↦ |σ ^ 2 - S ω|) 2 P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      ((memLp_const (σ ^ 2)).sub hS_memLp2).norm
  have h_diff_int : Integrable (fun ω ↦ |σ ^ 2 - S ω|) P :=
    h_diff_lp2.integrable one_le_two
  have hB_bound_pt (ω : Ω) :
      |B ω| ≤ (Real.sqrt (2 / Real.pi) / σ ^ 2) * |σ ^ 2 - S ω| := by
    have hb : B ω = deriv f (W ω) * ((σ ^ 2 - S ω) / σ ^ 2) := by
      dsimp only [B]
      rw [hB_inner ω]
    rw [hb, abs_mul, abs_div, abs_of_pos (pow_pos hσ_pos 2)]
    calc |deriv f (W ω)| * (|σ ^ 2 - S ω| / σ ^ 2)
        ≤ Real.sqrt (2 / Real.pi) * (|σ ^ 2 - S ω| / σ ^ 2) :=
          mul_le_mul_of_nonneg_right (hdf_bound (W ω))
            (div_nonneg (abs_nonneg _) (sq_nonneg σ))
      _ = (Real.sqrt (2 / Real.pi) / σ ^ 2) * |σ ^ 2 - S ω| := by ring
  have hint_B : Integrable B P := by
    have hB_meas : AEStronglyMeasurable B P := by
      have hm : AEMeasurable (fun ω ↦ deriv f (W ω) * ((σ ^ 2 - S ω) / σ ^ 2)) P :=
        (hdf_meas.comp_aemeasurable hW_meas).fun_mul
          ((hS_memLp2.aemeasurable.const_sub (σ ^ 2)).div_const (σ ^ 2))
      have heq : B = fun ω ↦ deriv f (W ω) * ((σ ^ 2 - S ω) / σ ^ 2) := by
        ext ω
        dsimp only [B]
        rw [hB_inner ω]
      rw [heq]
      exact hm.aestronglyMeasurable
    refine (h_diff_int.const_mul (Real.sqrt (2 / Real.pi) / σ ^ 2)).mono' hB_meas
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs] using hB_bound_pt ω
  have h_decomp : ∫ ω, normalSteinOp f (W ω) ∂P =
      -(∫ ω, A ω ∂P) + ∫ ω, B ω ∂P := by
    have hfn : (fun ω ↦ normalSteinOp f (W ω)) = fun ω ↦ (-A ω + B ω) - C ω := by
      ext ω
      exact h_stein_pt ω
    rw [hfn, integral_sub (hint_A.fun_neg.fun_add hint_B) hint_C,
      integral_add hint_A.fun_neg hint_B, integral_neg, hC_zero, sub_zero]
  have hA_le : |∫ ω, A ω ∂P| ≤
      (1 / σ ^ 3) * ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i,
        ∫ ω, |X i ω * X j ω * X k ω| ∂P := by
    let domA : Ω → ℝ := fun ω ↦
      (1 / σ ^ 3) * ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, |X i ω * X j ω * X k ω|
    have hint_domA : Integrable domA P :=
      (integrable_finsetSum Finset.univ fun i _ ↦ hint_dom_i i).const_mul (1 / σ ^ 3)
    have hA_pt (ω : Ω) : |A ω| ≤ domA ω := by
      dsimp only [A, domA]
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hσ_pos)]
      calc (1 / σ) * |∑ i : Fin n, T_i i ω|
          ≤ (1 / σ) * ∑ i : Fin n, |T_i i ω| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (1 / σ) * ∑ i : Fin n,
              ((1 / σ ^ 2) * ∑ j ∈ N i, ∑ k ∈ N i, |X i ω * X j ω * X k ω|) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun i _ ↦ hTi_bound i ω) (by positivity)
        _ = (1 / σ ^ 3) *
              ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, |X i ω * X j ω * X k ω| := by
            rw [← Finset.mul_sum]
            have h3 : (1 / σ) * (1 / σ ^ 2) = 1 / σ ^ 3 := by ring
            rw [← mul_assoc, h3]
    have h1 : |∫ ω, A ω ∂P| ≤ ∫ ω, domA ω ∂P :=
      abs_integral_le_integral_abs.trans (integral_mono hint_A.abs hint_domA hA_pt)
    have h2 : ∫ ω, domA ω ∂P =
        (1 / σ ^ 3) * ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i,
          ∫ ω, |X i ω * X j ω * X k ω| ∂P := by
      dsimp only [domA]
      rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ hint_dom_i i]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum (N i) fun j _ ↦
        integrable_finsetSum (N i) fun k _ ↦ by
          have heq : (fun ω ↦ |X i ω * X j ω * X k ω|) =
              fun ω ↦ |X i ω| * |X j ω| * |X k ω| := by
            ext ω
            rw [abs_mul, abs_mul]
          rw [heq]
          exact integrable_abs_mul_three (hX4 i) (hX4 j) (hX4 k)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      exact integral_finsetSum (N i) fun k _ ↦ by
        have heq : (fun ω ↦ |X i ω * X j ω * X k ω|) =
            fun ω ↦ |X i ω| * |X j ω| * |X k ω| := by
          ext ω
          rw [abs_mul, abs_mul]
        rw [heq]
        exact integrable_abs_mul_three (hX4 i) (hX4 j) (hX4 k)
    exact h1.trans_eq h2
  have hB_le : |∫ ω, B ω ∂P| ≤
      Real.sqrt 2 / (Real.sqrt Real.pi * σ ^ 2) *
        Real.sqrt
          (ProbabilityTheory.variance
            (fun ω ↦ ∑ i : Fin n, ∑ j ∈ N i, X i ω * X j ω) P) := by
    have h1 : |∫ ω, B ω ∂P| ≤
        (Real.sqrt (2 / Real.pi) / σ ^ 2) * ∫ ω, |σ ^ 2 - S ω| ∂P := by
      have hm := abs_integral_le_integral_abs.trans
        (integral_mono hint_B.abs
          (h_diff_int.const_mul (Real.sqrt (2 / Real.pi) / σ ^ 2)) hB_bound_pt)
      rwa [integral_const_mul] at hm
    have hS_mean : ∫ ω, S ω ∂P = σ ^ 2 := by
      have heq := hasDependencyNeighborhoods_integral_quadSum_eq_variance P hX_meas hX4 hX0 hN
      dsimp only [S]
      have hpt : (fun ω ↦ ∑ i : Fin n, ∑ k ∈ N i, X i ω * X k ω) =
          fun ω ↦ ∑ i : Fin n, X i ω * ∑ j ∈ N i, X j ω := by
        ext ω
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum]
      rw [hpt, heq, hσ_sq]
    have h_l1_var : ∫ ω, |σ ^ 2 - S ω| ∂P ≤
        Real.sqrt (ProbabilityTheory.variance S P) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hcs := sq_integral_le_integral_sq h_diff_lp2
      have hsq_eq : (fun ω ↦ |σ ^ 2 - S ω| ^ 2) =
          fun ω ↦ (S ω - ∫ ω', S ω' ∂P) ^ 2 := by
        ext ω
        rw [sq_abs, hS_mean]
        ring
      rwa [hsq_eq, ← ProbabilityTheory.variance_eq_integral hS_memLp2.aemeasurable] at hcs
    have h2pi : Real.sqrt (2 / Real.pi) / σ ^ 2 = Real.sqrt 2 / (Real.sqrt Real.pi * σ ^ 2) := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [h2pi] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h_l1_var (by positivity))
  calc |∫ ω, normalSteinOp f (W ω) ∂P|
      = |-(∫ ω, A ω ∂P) + ∫ ω, B ω ∂P| := by rw [h_decomp]
    _ ≤ |-(∫ ω, A ω ∂P)| + |∫ ω, B ω ∂P| := abs_add_le _ _
    _ = |∫ ω, A ω ∂P| + |∫ ω, B ω ∂P| := by rw [abs_neg]
    _ ≤ (1 / σ ^ 3 *
          (∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, ∫ ω, |X i ω * X j ω * X k ω| ∂P) +
        Real.sqrt 2 / (Real.sqrt Real.pi * σ ^ 2) *
          Real.sqrt
            (ProbabilityTheory.variance
              (fun ω ↦ ∑ i : Fin n, ∑ j ∈ N i, X i ω * X j ω) P)) :=
      add_le_add hA_le hB_le

end SteinMethod
