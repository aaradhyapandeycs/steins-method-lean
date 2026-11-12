/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonSizeBias
import Formalization.PoissonSizeBias.Core.Basic
import Formalization.PoissonSizeBias.Core.Exchangeable
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Variance

/-!
# Decreasing Size-Bias Couplings (`Formalization.PoissonSizeBias.Negative.Basic`)

Formalizes **Theorem 4.19** (`\label{thm125}`, `SteinIntro.tex:2455-2478`) from Section 4.3.4
(*Decreasing size-bias couplings*) of Nathan Ross, *"Fundamentals of Stein's method"*:

- `tvDist_poisson_le_of_decreasing_sizeBias`: **Theorem 4.19** (`\label{thm125}`), proving
  $$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
    \min\{1, \lambda\}\left(1 - \frac{\operatorname{Var}(W)}{\lambda}\right)$$
  when $W = \sum_{i=1}^n X_i$ is a sum of $\{0, 1\}$-indicators with positive mean $\lambda$ and a
  coordinatewise decreasing conditional coupling $X_j^{(i)} \le X_j$ ($j \ne i$).
- `tvDist_poisson_le_of_aux_decreasing_coupling`: adjoins the random index $I$
  (`ℙ(I = i) = p_i / λ`) on a product extension so downstream applications (`Ex4_13`, `Ex4_15`,
  `Ex4_16`, `Rem4_17`) only need to supply the conditional couplings $(X_j^{(i)})_{j \ne i}$ on
  `Ω × Aux`.
- `tvDist_poisson_le_of_fintype_couplings`: glues pairwise conditional couplings on a finite
  discrete state space `E`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Helper Lemmas on `{0, 1}`-Valued `ℕ` Random Variables -/

/-- Expectation of an a.e. `{0, 1}`-valued `ℕ` random variable equals `P.real {ω | X ω = 1}`. -/
theorem integral_nat_zero_one_eq_measureReal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℕ} (hX_meas : Measurable X) (hX_zo : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) :
    ∫ ω, (X ω : ℝ) ∂P = P.real {ω | X ω = 1} := by
  have hset : MeasurableSet {ω | X ω = 1} := hX_meas (measurableSet_singleton 1)
  have hae : (fun ω ↦ (X ω : ℝ)) =ᵐ[P] {ω | X ω = 1}.indicator (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hX_zo] with ω hω
    rcases hω with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [integral_congr_ae hae, integral_indicator hset, setIntegral_one_eq_measureReal]

/-- An a.e. `{0, 1}`-valued `ℕ` random variable is integrable after casting to `ℝ`. -/
theorem integrable_nat_zero_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℕ} (hX_meas : Measurable X) (hX_zo : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) :
    Integrable (fun ω ↦ (X ω : ℝ)) P := by
  have hmeas : Measurable (fun ω ↦ (X ω : ℝ)) :=
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp hX_meas
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards [hX_zo] with ω hω
  rcases hω with h0 | h1
  · simp [h0]
  · simp [h1]

/-- A finite sum of a.e. `{0, 1}`-valued `ℕ` random variables belongs to `MemLp _ 2 P`. -/
theorem memLp_two_sum_nat_zero_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    MemLp (fun ω ↦ ((∑ i : Fin n, X i ω : ℕ) : ℝ)) 2 P := by
  have hW_meas : Measurable (fun ω ↦ ((∑ i : Fin n, X i ω : ℕ) : ℝ)) :=
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp
      (Finset.measurable_sum Finset.univ fun i _ ↦ hX_meas i)
  refine (memLp_top_of_bound hW_meas.aestronglyMeasurable (n : ℝ) ?_).mono_exponent le_top
  filter_upwards [ae_all_iff.mpr hX_zo] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have hle : ∑ i : Fin n, X i ω ≤ n := by
    calc ∑ i : Fin n, X i ω
      _ ≤ ∑ _i : Fin n, 1 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rcases hω i with h0 | h1 <;> omega
      _ = n := by simp
  exact_mod_cast hle

/-! ### Theorem 4.19 (`\label{thm125}`, `SteinIntro.tex:2455-2478`) -/

/-- **Theorem 4.19** (`\label{thm125}`, `SteinIntro.tex:2455-2465`; proof `L2466-2478`):
for `{0, 1}`-indicators $X_1, \dots, X_n$ with $p_i = \mathbb{P}(X_i = 1)$,
$W = \sum_{i=1}^n X_i$, and $\lambda = \sum_{i=1}^n p_i > 0$, if $(X_j^{(i)})_{j \ne i}$ has the
conditional distribution of $(X_j)_{j \ne i}$ given $X_i = 1$, $I$ is independent of
$(X, X^{(\cdot)})$ with $\mathbb{P}(I = i) = p_i / \lambda$, and $X_j^{(i)} \le X_j$ almost surely
for all $i \ne j$, then for $Z \sim \mathrm{Po}(\lambda)$,
$$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  \min\{1, \lambda\}\left(1 - \frac{\operatorname{Var}(W)}{\lambda}\right).$$ -/
theorem tvDist_poisson_le_of_decreasing_sizeBias
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℕ)} {I : Ω → Fin n}
    {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ω ∂P, Y i ω j ≤ X j.1 ω) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ))) := by
  intro p W hr hlam hY_meas hY_law hI_meas hI_prob hI_indep hY_le _hZ_meas hZ_law
  have hr_pos : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hlam_pos : 0 < ∑ i : Fin n, p i := by
    rw [← hlam]
    exact hr_pos
  have hI_prob' : ∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / ∑ k : Fin n, p k := by
    intro i
    rw [← hlam]
    exact hI_prob i
  let Ws : Ω → ℕ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1
  have hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P (fun ω ↦ (Ws ω : ℝ)) :=
    sizeBias_sum_of_nat_zero_one_fintype P hX_meas hX_zo hlam_pos hY_meas hY_law
      hI_meas hI_prob' hI_indep
  have hW_meas : Measurable W := Finset.measurable_sum Finset.univ fun i _ ↦ hX_meas i
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) := by
    have hcast : (fun ω ↦ (W ω : ℝ)) = fun ω ↦ ∑ i : Fin n, (X i ω : ℝ) := by
      ext ω
      simp [W]
    rw [hcast, integral_finsetSum Finset.univ fun i _ ↦
      integrable_nat_zero_one P (hX_meas i) (hX_zo i)]
    have hsum : (∑ i : Fin n, ∫ ω, (X i ω : ℝ) ∂P) = ∑ i : Fin n, p i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact integral_nat_zero_one_eq_measureReal P (hX_meas i) (hX_zo i)
    rw [hsum, hlam]
  have hY_all : ∀ᵐ ω ∂P, ∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, Y i ω j ≤ X j.1 ω :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hY_le i)
  have hX_all : ∀ᵐ ω ∂P, ∀ i : Fin n, X i ω = 0 ∨ X i ω = 1 := ae_all_iff.mpr hX_zo
  have hWs_le_W_succ : ∀ᵐ ω ∂P, Ws ω ≤ W ω + 1 := by
    filter_upwards [hY_all] with ω hω
    have hsub : (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) ≤
        ∑ j : {j : Fin n // j ≠ I ω}, X j.1 ω :=
      Finset.sum_le_sum fun j _ ↦ hω (I ω) j
    have herase : (∑ j : {j : Fin n // j ≠ I ω}, X j.1 ω) =
        ∑ k ∈ Finset.univ.erase (I ω), X k ω :=
      (Finset.sum_subtype (Finset.univ.erase (I ω)) (by simp) (fun k ↦ X k ω)).symm
    have hle_W : (∑ k ∈ Finset.univ.erase (I ω), X k ω) ≤ W ω := by
      have hsplit : (∑ k ∈ Finset.univ.erase (I ω), X k ω) + X (I ω) ω = W ω :=
        Finset.sum_erase_add Finset.univ (fun k ↦ X k ω) (Finset.mem_univ (I ω))
      omega
    exact Nat.add_le_add_right (hsub.trans (herase.le.trans hle_W)) 1
  have hWs_int : Integrable (fun ω ↦ (Ws ω : ℝ)) P := by
    refine Integrable.of_bound hSB.2.2.1.aestronglyMeasurable ((n : ℝ) + 1) ?_
    filter_upwards [hWs_le_W_succ, hX_all] with ω hle hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hW_le : W ω ≤ n := by
      calc W ω = ∑ i : Fin n, X i ω := rfl
        _ ≤ ∑ _i : Fin n, 1 := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rcases hω i with h0 | h1 <;> omega
        _ = n := by simp
    have hWs_le : Ws ω ≤ n + 1 := by omega
    exact_mod_cast hWs_le
  have hW_memLp : MemLp (fun ω ↦ (W ω : ℝ)) 2 P :=
    memLp_two_sum_nat_zero_one P hX_meas hX_zo
  have hW2_int : Integrable (fun ω ↦ (W ω : ℝ) * (W ω : ℝ)) P := by
    simpa [sq] using hW_memLp.integrable_sq
  have hSB_moment : ∫ ω, (W ω : ℝ) * (W ω : ℝ) ∂P = (r : ℝ) * ∫ ω, (Ws ω : ℝ) ∂P := by
    have h := hSB.2.2.2 (fun x : ℝ ↦ x) measurable_id hW2_int
    rwa [hW_mean] at h
  have hvar : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      (r : ℝ) * (∫ ω, (Ws ω : ℝ) ∂P) - (r : ℝ) ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub hW_memLp]
    simp only [Pi.pow_apply, hW_mean]
    have hsq : (fun ω ↦ (W ω : ℝ) ^ 2) = fun ω ↦ (W ω : ℝ) * (W ω : ℝ) := by
      ext ω
      ring
    rw [hsq, hSB_moment]
  have habs_eq : ∫ ω, |(W ω : ℝ) + 1 - (Ws ω : ℝ)| ∂P =
      1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ) := by
    have hae_abs : (fun ω ↦ |(W ω : ℝ) + 1 - (Ws ω : ℝ)|) =ᵐ[P]
        fun ω ↦ (W ω : ℝ) + 1 - (Ws ω : ℝ) := by
      filter_upwards [hWs_le_W_succ] with ω hle
      have hcast : (Ws ω : ℝ) ≤ (W ω : ℝ) + 1 := by exact_mod_cast hle
      exact abs_of_nonneg (sub_nonneg.mpr hcast)
    have hW1_int : Integrable (fun ω ↦ (W ω : ℝ) + 1) P :=
      hSB.2.1.fun_add (integrable_const 1)
    rw [integral_congr_ae hae_abs,
      integral_sub hW1_int hWs_int,
      integral_add hSB.2.1 (integrable_const 1),
      hW_mean, integral_const, probReal_univ, one_smul, hvar]
    field_simp [hr_pos.ne']
    ring
  rw [hZ_law, ← habs_eq]
  exact tvDist_poissonLaw_le_of_isSizeBias_nat P hr hW_meas.aemeasurable hW_mean hSB hWs_int

/-- On a probability space, an index `I : Ω → Fin n` satisfying `P.real (I ⁻¹' {i}) = p i / r`
forces `0 < r`. -/
theorem pos_of_index_prob
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {I : Ω → Fin n} {p : Fin n → ℝ} {r : ℝ≥0}
    (hI_meas : Measurable I) (hI_prob : ∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) :
    0 < r := by
  by_contra hr0
  have hr_zero : (r : ℝ) = 0 := by exact_mod_cast le_antisymm (not_lt.mp hr0) zero_le
  have hprob0 : ∀ i : Fin n, P.real (I ⁻¹' {i}) = 0 := fun i ↦ by
    rw [hI_prob i, hr_zero, div_zero]
  have huniv : (Set.univ : Set Ω) = ⋃ i ∈ (Finset.univ : Finset (Fin n)), I ⁻¹' {i} := by
    ext ω
    simp
  have h1 : P.real Set.univ = 0 := by
    rw [huniv, measureReal_biUnion_finset]
    · simp [hprob0]
    · intro i _ j _ hij
      exact Disjoint.preimage I (Set.disjoint_singleton.mpr hij)
    · intro i _
      exact hI_meas (measurableSet_singleton i)
  linarith [probReal_univ (μ := P)]

/-- **Theorem 4.19** (`\label{thm125}`, `SteinIntro.tex:2455-2465`): full statement including
both `IsSizeBias P W P Ws` (`L2458-2459`) and the decreasing size-bias Poisson TV bound (`L2463`),
deducing `0 < r` automatically from the index distribution `ℙ(I = i) = p_i / r`. -/
theorem thm4_19
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℕ)} {I : Ω → Fin n}
    {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, (Y (I ω) ω j : ℝ)) + 1
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ω ∂P, Y i ω j ≤ X j.1 ω) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ) *
            (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ))) := by
  intro p W Ws hlam hY_meas hY_law hI_meas hI_prob hI_indep hY_le hZ_meas hZ_law
  have hr : 0 < r := pos_of_index_prob P hI_meas hI_prob
  have hlam_pos : 0 < ∑ i : Fin n, p i := by
    rw [← hlam]
    exact NNReal.coe_pos.mpr hr
  have hI_prob' : ∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / ∑ k : Fin n, p k := fun i ↦ by
    rw [← hlam]
    exact hI_prob i
  have hSB_nat := sizeBias_sum_of_nat_zero_one_fintype P hX_meas hX_zo hlam_pos hY_meas hY_law
    hI_meas hI_prob' hI_indep
  have hWs_eq :
      (fun ω ↦ (((∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1 : ℕ) : ℝ)) = Ws := by
    ext ω
    simp [Ws]
  rw [hWs_eq] at hSB_nat
  exact ⟨hSB_nat, tvDist_poisson_le_of_decreasing_sizeBias P P' hX_meas hX_zo hr hlam hY_meas
    hY_law hI_meas hI_prob hI_indep hY_le hZ_meas hZ_law⟩

/-! ### Auxiliary Product-Space Extension and Pushforward Invariance -/

/-- Conditional pushforward invariance under a measure-preserving map `P₂.map f = P`. -/
private lemma cond_preimage_map_comp
    {Ω₂ Ω α : Type*} [MeasurableSpace Ω₂] [MeasurableSpace Ω] [MeasurableSpace α]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω₂ → Ω} (hf : Measurable f) (hmap : P₂.map f = P)
    {A : Set Ω} (hA : MeasurableSet A) {g : Ω → α} (hg : Measurable g) :
    (ProbabilityTheory.cond P₂ (f ⁻¹' A)).map (g ∘ f) =
      (ProbabilityTheory.cond P A).map g := by
  refine Measure.ext fun E hE ↦ ?_
  rw [Measure.map_apply (hg.comp hf) hE, Measure.map_apply hg hE,
    ProbabilityTheory.cond_apply (hf hA), ProbabilityTheory.cond_apply hA]
  have h1 : P₂ (f ⁻¹' A) = P A := by
    rw [← hmap, Measure.map_apply hf hA]
  have h2 : P₂ (f ⁻¹' A ∩ (g ∘ f) ⁻¹' E) = P (A ∩ g ⁻¹' E) := by
    rw [Set.preimage_comp, ← Set.preimage_inter, ← hmap,
      Measure.map_apply hf (hA.inter (hg hE))]
  rw [h1, h2]

/-- Product-space extension of **Theorem 4.19**: given decreasing conditional couplings
`Y i : Ω × Aux → ({j : Fin n // j ≠ i} → ℕ)` on `P.prod Q`, automatically adjoins an independent
index `I : Fin n` (`ℙ(I = i) = p_i / r`) and applies `tvDist_poisson_le_of_decreasing_sizeBias`. -/
theorem tvDist_poisson_le_of_aux_decreasing_coupling
    {Ω Aux Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Aux] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Aux) [IsProbabilityMeasure Q]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ}
    {Y : (i : Fin n) → Ω × Aux → ({j : Fin n // j ≠ i} → ℕ)}
    {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ i : Fin n, Measurable (Y i)) →
    (∀ i : Fin n,
      0 < p i →
      (P.prod Q).map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω)) →
    (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ z ∂(P.prod Q), Y i z j ≤ X j.1 z.1) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ))) := by
  intro p W hr hlam hY_meas hY_law hY_le hZ_meas hZ_law
  have hr_pos : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  let q : Fin n → ℝ≥0∞ := fun i ↦ ENNReal.ofReal (p i / (r : ℝ))
  have hsum_q : HasSum q 1 := by
    suffices h : (∑ i : Fin n, q i) = 1 from h ▸ hasSum_fintype q
    calc ∑ i : Fin n, ENNReal.ofReal (p i / (r : ℝ))
      _ = ENNReal.ofReal (∑ i : Fin n, p i / (r : ℝ)) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ ↦ div_nonneg measureReal_nonneg hr_pos.le).symm
      _ = ENNReal.ofReal ((∑ i : Fin n, p i) / (r : ℝ)) := by rw [← Finset.sum_div]
      _ = ENNReal.ofReal ((r : ℝ) / (r : ℝ)) := by rw [← hlam]
      _ = 1 := by rw [div_self hr_pos.ne', ENNReal.ofReal_one]
  let pmfI : PMF (Fin n) := ⟨q, hsum_q⟩
  let μI : Measure (Fin n) := pmfI.toMeasure
  have : IsProbabilityMeasure μI := PMF.toMeasure.isProbabilityMeasure pmfI
  let P₁ : Measure (Ω × Aux) := P.prod Q
  let P₂ : Measure ((Ω × Aux) × Fin n) := P₁.prod μI
  let π₁ : Ω × Aux → Ω := Prod.fst
  let π₂ : (Ω × Aux) × Fin n → Ω × Aux := Prod.fst
  let π : (Ω × Aux) × Fin n → Ω := π₁ ∘ π₂
  have hπ_meas : Measurable π := measurable_fst.comp measurable_fst
  have hmap_π₁ : P₁.map π₁ = P := Measure.fst_prod
  have hmap_π₂ : P₂.map π₂ = P₁ := Measure.fst_prod
  have hmap_π : P₂.map π = P := by
    rw [← Measure.map_map measurable_fst measurable_fst, hmap_π₂, hmap_π₁]
  let X₂ : Fin n → (Ω × Aux) × Fin n → ℕ := fun i z ↦ X i (π z)
  let Y₂ : (i : Fin n) → (Ω × Aux) × Fin n → ({j : Fin n // j ≠ i} → ℕ) := fun i z ↦ Y i (π₂ z)
  let I₂ : (Ω × Aux) × Fin n → Fin n := Prod.snd
  have hX₂_meas : ∀ i : Fin n, Measurable (X₂ i) := fun i ↦ (hX_meas i).comp hπ_meas
  have hX₂_zo : ∀ i : Fin n, ∀ᵐ z ∂P₂, X₂ i z = 0 ∨ X₂ i z = 1 := by
    intro i
    have hset : MeasurableSet {ω : Ω | X i ω = 0 ∨ X i ω = 1} :=
      ((hX_meas i) (measurableSet_singleton 0)).union ((hX_meas i) (measurableSet_singleton 1))
    exact (ae_map_iff hπ_meas.aemeasurable hset).mp (hmap_π.symm ▸ hX_zo i)
  have hp₂_eq : ∀ i : Fin n, P₂.real {z | X₂ i z = 1} = p i := by
    intro i
    have hset : MeasurableSet {ω : Ω | X i ω = 1} := (hX_meas i) (measurableSet_singleton 1)
    change P₂.real (π ⁻¹' {ω : Ω | X i ω = 1}) = p i
    rw [← map_measureReal_apply hπ_meas hset, hmap_π]
  have hlam₂ : (r : ℝ) = ∑ i : Fin n, P₂.real {z | X₂ i z = 1} := by
    simp_rw [hp₂_eq]
    exact hlam
  have hY₂_meas : ∀ i : Fin n, AEMeasurable (Y₂ i) P₂ :=
    fun i ↦ ((hY_meas i).comp measurable_fst).aemeasurable
  have hY₂_law : ∀ i : Fin n,
      0 < P₂.real {z | X₂ i z = 1} →
      P₂.map (Y₂ i) =
        (ProbabilityTheory.cond P₂ {z | X₂ i z = 1}).map
          (fun z (j : {j : Fin n // j ≠ i}) ↦ X₂ j z) := by
    intro i hi_pos
    rw [hp₂_eq i] at hi_pos
    have hmapY : P₂.map (Y₂ i) = P₁.map (Y i) := by
      rw [← hmap_π₂, Measure.map_map (hY_meas i) measurable_fst]
      rfl
    have hproj : Measurable (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) :=
      Measurable.of_eval fun j ↦ hX_meas j.1
    have hcond := cond_preimage_map_comp P₂ P hπ_meas hmap_π
      ((hX_meas i) (measurableSet_singleton 1)) hproj
    rw [hmapY, hY_law i hi_pos]
    exact hcond.symm
  have hI₂_meas : Measurable I₂ := measurable_snd
  have hI₂_prob : ∀ i : Fin n,
      P₂.real (I₂ ⁻¹' {i}) = P₂.real {z | X₂ i z = 1} / (r : ℝ) := by
    intro i
    rw [hp₂_eq i]
    have hmap_snd : P₂.map I₂ = μI := Measure.snd_prod
    rw [← map_measureReal_apply measurable_snd (measurableSet_singleton i), hmap_snd,
      measureReal_def]
    change (pmfI.toMeasure {i}).toReal = p i / (r : ℝ)
    rw [PMF.toMeasure_apply_singleton pmfI i (measurableSet_singleton i)]
    exact ENNReal.toReal_ofReal (div_nonneg measureReal_nonneg hr_pos.le)
  have hI₂_indep :
      ProbabilityTheory.IndepFun I₂ (fun z ↦ (fun i ↦ X₂ i z, fun i ↦ Y₂ i z)) P₂ := by
    let φ : Ω × Aux → (Fin n → ℕ) × ((i : Fin n) → {j : Fin n // j ≠ i} → ℕ) :=
      fun z₁ ↦ (fun i ↦ X i z₁.1, fun i ↦ Y i z₁)
    have hφ_meas : Measurable φ :=
      (Measurable.of_eval fun i ↦ (hX_meas i).comp measurable_fst).prodMk
        (Measurable.of_eval fun i ↦ hY_meas i)
    exact (ProbabilityTheory.indepFun_prod (μ := P₁) (ν := μI) hφ_meas measurable_id).symm
  have hY₂_le : ∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ z ∂P₂, Y₂ i z j ≤ X₂ j.1 z := by
    intro i j
    have hset : MeasurableSet {z₁ : Ω × Aux | Y i z₁ j ≤ X j.1 z₁.1} := by
      have h1 : Measurable (fun z₁ : Ω × Aux ↦ Y i z₁ j) :=
        (measurable_pi_apply j).comp (hY_meas i)
      have h2 : Measurable (fun z₁ : Ω × Aux ↦ X j.1 z₁.1) := (hX_meas j.1).comp measurable_fst
      exact measurableSet_le h1 h2
    exact (ae_map_iff measurable_fst.aemeasurable hset).mp (hmap_π₂.symm ▸ hY_le i j)
  have hmain := tvDist_poisson_le_of_decreasing_sizeBias P₂ P' hX₂_meas hX₂_zo hr hlam₂
    hY₂_meas hY₂_law hI₂_meas hI₂_prob hI₂_indep hY₂_le hZ_meas hZ_law
  have hW_meas : Measurable W := Finset.measurable_sum Finset.univ fun i _ ↦ hX_meas i
  have hW₂_eq : (fun z : (Ω × Aux) × Fin n ↦ ∑ i : Fin n, X₂ i z) = W ∘ π := rfl
  have hmap_W : P₂.map (fun z ↦ ∑ i : Fin n, X₂ i z) = P.map W := by
    rw [hW₂_eq, ← Measure.map_map hW_meas hπ_meas, hmap_π]
  have hvar_W : ProbabilityTheory.variance
      (fun z : (Ω × Aux) × Fin n ↦ ((∑ i : Fin n, X₂ i z : ℕ) : ℝ)) P₂ =
      ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P := by
    have hWR_meas : Measurable (fun ω ↦ (W ω : ℝ)) :=
      (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp hW_meas
    have h := ProbabilityTheory.variance_map (μ := P₂)
      (X := fun ω ↦ (W ω : ℝ)) (Y := π) hWR_meas.aemeasurable hπ_meas.aemeasurable
    rw [hmap_π] at h
    exact h.symm
  rwa [hmap_W, hvar_W] at hmain

/-! ### Finite Discrete Gluing of Pairwise Conditional Couplings -/

/-- Two measures on a finite discrete measurable space that agree on all singletons are equal. -/
theorem measure_ext_of_singleton_fintype
    {α : Type*} [Finite α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    {μ ν : Measure α} (h : ∀ a : α, μ {a} = ν {a}) : μ = ν := by
  classical
  cases nonempty_fintype α
  refine Measure.ext fun E _ ↦ ?_
  have hE : E = ⋃ a ∈ E.toFinset, ({a} : Set α) := by
    ext a
    simp
  rw [hE, measure_biUnion_finset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun a _ ↦ h a
  · intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  · intro _ _
    exact .of_discrete
  · intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  · intro _ _
    exact .of_discrete

/-- Singleton mass of a pushforward measure on a finite discrete domain. -/
theorem measure_map_singleton_fintype
    {α β : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [DecidableEq β] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (μ : Measure α) (f : α → β) (b : β) :
    (μ.map f) {b} = ∑ a ∈ Finset.univ.filter (fun a ↦ f a = b), μ {a} := by
  classical
  rw [Measure.map_apply Measurable.of_discrete .of_discrete]
  have hpre : f ⁻¹' {b} = ⋃ a ∈ Finset.univ.filter (fun a ↦ f a = b), ({a} : Set α) := by
    ext a
    simp
  rw [hpre, measure_biUnion_finset]
  · intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  · intro _ _
    exact .of_discrete

/-- Total mass of a measure on a finite discrete space equals the sum of its singleton masses. -/
theorem sum_measure_singleton_fintype
    {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : Measure α) : (∑ a : α, μ {a}) = μ Set.univ := by
  classical
  have huniv : (Set.univ : Set α) = ⋃ a ∈ (Finset.univ : Finset α), ({a} : Set α) := by
    ext a
    simp
  rw [huniv, measure_biUnion_finset]
  · intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  · intro _ _
    exact .of_discrete

/-- **Finite-State Pairwise Coupling Glue for Theorem 4.19**:
on a finite discrete state space `E`, if `X : Fin n → E → ℕ` are `{0, 1}`-indicators and for each
`i : Fin n` with `0 < μ.real {b | X i b = 1}` there exists a coupling `ν_i` on `E × E` between
`μ` and `cond μ {b | X i b = 1}` such that `X j z.2 ≤ X j z.1` `ν_i`-almost everywhere for `j ≠ i`,
then all `n` couplings glue conditionally independently given `b : E` and **Theorem 4.19** yields
$$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
  \min\{1, \lambda\}\left(1 - \frac{\operatorname{Var}(W)}{\lambda}\right).$$ -/
theorem tvDist_poisson_le_of_fintype_couplings
    {E Ω' : Type*} [Finite E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    [MeasurableSpace Ω']
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → E → ℕ} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX_zo : ∀ i : Fin n, ∀ b : E, X i b = 0 ∨ X i b = 1) :
    let p : Fin n → ℝ := fun i ↦ μ.real {b | X i b = 1}
    let W : E → ℕ := fun b ↦ ∑ i : Fin n, X i b
    0 < r →
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ i : Fin n, 0 < p i →
      ∃ (ν : Measure (E × E)), IsProbabilityMeasure ν ∧
        ν.map Prod.fst = μ ∧
        ν.map Prod.snd = ProbabilityTheory.cond μ {b | X i b = 1} ∧
        (∀ᵐ z ∂ν, ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1)) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (μ.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun b ↦ (W b : ℝ)) μ / (r : ℝ))) := by
  classical
  cases nonempty_fintype E
  intro p W hr hlam hex hZ_meas hZ_law
  let ν : Fin n → Measure (E × E) := fun i ↦
    if hi : 0 < p i then (hex i hi).choose else μ.map (fun b ↦ (b, b))
  have hν_prob : ∀ i : Fin n, IsProbabilityMeasure (ν i) := by
    intro i
    by_cases hi : 0 < p i
    · simpa [ν, hi] using (hex i hi).choose_spec.1
    · simp only [ν, hi, ↓reduceDIte]
      exact (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr ‹_›
  have hν_fst : ∀ i : Fin n, (ν i).map Prod.fst = μ := by
    intro i
    by_cases hi : 0 < p i
    · simpa [ν, hi] using (hex i hi).choose_spec.2.1
    · simp only [ν, hi, ↓reduceDIte]
      rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
      exact Measure.map_id
  have hν_snd : ∀ i : Fin n, 0 < p i →
      (ν i).map Prod.snd = ProbabilityTheory.cond μ {b | X i b = 1} := by
    intro i hi
    simpa [ν, hi] using (hex i hi).choose_spec.2.2.1
  have hν_le : ∀ i : Fin n, ∀ᵐ z ∂(ν i), ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1 := by
    intro i
    by_cases hi : 0 < p i
    · simpa [ν, hi] using (hex i hi).choose_spec.2.2.2
    · simp only [ν, hi, ↓reduceDIte]
      have hset : MeasurableSet
          {z : E × E | ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1} := .of_discrete
      rw [ae_map_iff Measurable.of_discrete.aemeasurable hset]
      exact Eventually.of_forall fun b _ _ ↦ le_rfl
  have hν_row_sum : ∀ (i : Fin n) (b : E), (∑ b' : E, (ν i) {(b, b')}) = μ {b} := by
    intro i b
    have hmap := congrArg (fun m : Measure E ↦ m {b}) (hν_fst i)
    rw [measure_map_singleton_fintype (ν i) Prod.fst b] at hmap
    have hfilt : (Finset.univ.filter fun z : E × E ↦ z.1 = b) =
        Finset.univ.map ⟨fun b' : E ↦ (b, b'), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
      ext ⟨b₁, b₂⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨fun h ↦ ⟨b₂, Prod.ext h.symm rfl⟩, fun ⟨_, h⟩ ↦ (Prod.mk.inj h).1.symm⟩
    rw [hfilt, Finset.sum_map] at hmap
    exact hmap
  let w : E × (Fin n → E) → ℝ≥0∞ := fun z ↦
    if μ {z.1} = 0 then 0 else μ {z.1} * ∏ i : Fin n, ((ν i) {(z.1, z.2 i)} * (μ {z.1})⁻¹)
  have hrow_factor : ∀ (b : E) (h0 : μ {b} ≠ 0) (i : Fin n),
      (∑ b' : E, ((ν i) {(b, b')} * (μ {b})⁻¹)) = 1 := by
    intro b h0 i
    rw [← Finset.sum_mul, hν_row_sum i b]
    exact ENNReal.mul_inv_cancel h0 (measure_ne_top μ {b})
  have hsum_y_eq : ∀ b : E, (∑ y : Fin n → E, w (b, y)) = μ {b} := by
    intro b
    by_cases h0 : μ {b} = 0
    · simp [w, h0]
    · simp only [w, h0, ↓reduceIte]
      rw [← Finset.mul_sum,
        ← Fintype.prod_sum (fun (i : Fin n) (b' : E) ↦ (ν i) {(b, b')} * (μ {b})⁻¹)]
      simp_rw [hrow_factor b h0]
      simp
  have hsum_w : HasSum w 1 := by
    suffices h : (∑ z : E × (Fin n → E), w z) = 1 from h ▸ hasSum_fintype w
    rw [Fintype.sum_prod_type]
    simp_rw [hsum_y_eq]
    rw [sum_measure_singleton_fintype μ, measure_univ]
  let pmfJ : PMF (E × (Fin n → E)) := ⟨w, hsum_w⟩
  let P_J : Measure (E × (Fin n → E)) := pmfJ.toMeasure
  have : IsProbabilityMeasure P_J := PMF.toMeasure.isProbabilityMeasure pmfJ
  have hPJ_singleton : ∀ z : E × (Fin n → E), P_J {z} = w z :=
    fun z ↦ PMF.toMeasure_apply_singleton pmfJ z .of_discrete
  have hPJ_fst : P_J.map Prod.fst = μ := by
    refine measure_ext_of_singleton_fintype fun b ↦ ?_
    rw [measure_map_singleton_fintype P_J Prod.fst b]
    have hfilt : (Finset.univ.filter fun z : E × (Fin n → E) ↦ z.1 = b) =
        Finset.univ.map ⟨fun y : Fin n → E ↦ (b, y), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
      ext ⟨b₁, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨fun h ↦ ⟨y, Prod.ext h.symm rfl⟩, fun ⟨_, h⟩ ↦ (Prod.mk.inj h).1.symm⟩
    rw [hfilt, Finset.sum_map]
    simp_rw [hPJ_singleton]
    exact hsum_y_eq b
  have hPJ_pair : ∀ i : Fin n, P_J.map (fun z : E × (Fin n → E) ↦ (z.1, z.2 i)) = ν i := by
    intro i
    refine measure_ext_of_singleton_fintype fun ⟨b₀, b₁⟩ ↦ ?_
    rw [measure_map_singleton_fintype P_J (fun z : E × (Fin n → E) ↦ (z.1, z.2 i)) (b₀, b₁)]
    let emb : ({j : Fin n // j ≠ i} → E) ↪ E × (Fin n → E) :=
      ⟨fun g ↦ (b₀, fun k ↦ if hk : k = i then b₁ else g ⟨k, hk⟩), by
        intro g₁ g₂ h
        have hy := (Prod.mk.inj h).2
        funext j
        have hj := congrFun hy j.1
        simpa [j.2] using hj⟩
    have hfilt : (Finset.univ.filter fun z : E × (Fin n → E) ↦ (z.1, z.2 i) = (b₀, b₁)) =
        Finset.univ.map emb := by
      ext ⟨b, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, Finset.mem_map, emb]
      constructor
      · rintro ⟨rfl, rfl⟩
        refine ⟨fun j ↦ y j.1, Prod.ext rfl ?_⟩
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · rintro ⟨g, h⟩
        rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        simp
    rw [hfilt, Finset.sum_map]
    by_cases h0 : μ {b₀} = 0
    · have hle : (ν i) {(b₀, b₁)} ≤ μ {b₀} := by
        rw [← hν_row_sum i b₀]
        exact Finset.single_le_sum (f := fun b' ↦ (ν i) {(b₀, b')})
          (fun _ _ ↦ zero_le) (Finset.mem_univ b₁)
      have hν0 : (ν i) {(b₀, b₁)} = 0 := le_antisymm (hle.trans (le_of_eq h0)) zero_le
      rw [hν0]
      refine Finset.sum_eq_zero fun g _ ↦ ?_
      rw [hPJ_singleton]
      exact ite_eq_left h0
    · have hw_eval : ∀ g : {j : Fin n // j ≠ i} → E,
          P_J {emb g} =
            μ {b₀} * ∏ k : Fin n,
              ((ν k) {(b₀, if hk : k = i then b₁ else g ⟨k, hk⟩)} * (μ {b₀})⁻¹) := by
        intro g
        rw [hPJ_singleton]
        change (if μ {b₀} = 0 then 0 else
          μ {b₀} * ∏ k : Fin n,
            ((ν k) {(b₀, if hk : k = i then b₁ else g ⟨k, hk⟩)} * (μ {b₀})⁻¹)) = _
        rw [ite_eq_right h0]
      simp_rw [hw_eval]
      have hprod_split : ∀ g : {j : Fin n // j ≠ i} → E,
          (∏ k : Fin n, ((ν k) {(b₀, if hk : k = i then b₁ else g ⟨k, hk⟩)} * (μ {b₀})⁻¹)) =
            ((ν i) {(b₀, b₁)} * (μ {b₀})⁻¹) *
              ∏ j : {j : Fin n // j ≠ i}, ((ν j.1) {(b₀, g j)} * (μ {b₀})⁻¹) := by
        intro g
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        congr 1
        · simp
        · refine Finset.prod_bij (fun (x : Fin n) (hx : x ∈ Finset.univ.erase i) ↦
              (⟨x, Finset.ne_of_mem_erase hx⟩ : {j : Fin n // j ≠ i}))
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ by simpa using congrArg Subtype.val h)
            (fun j _ ↦ ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩, Subtype.ext rfl⟩)
            (fun x hx ↦ ?_)
          simp [Finset.ne_of_mem_erase hx]
      have hsum_prod :
          (∑ g : {j : Fin n // j ≠ i} → E,
            ∏ j : {j : Fin n // j ≠ i}, ((ν j.1) {(b₀, g j)} * (μ {b₀})⁻¹)) = 1 := by
        rw [← Fintype.prod_sum
          (fun (j : {j : Fin n // j ≠ i}) (b' : E) ↦ (ν j.1) {(b₀, b')} * (μ {b₀})⁻¹)]
        refine Finset.prod_eq_one fun j _ ↦ ?_
        exact hrow_factor b₀ h0 j.1
      simp_rw [hprod_split, ← mul_assoc]
      rw [← Finset.mul_sum, hsum_prod, mul_one]
      rw [mul_comm (μ {b₀}), mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top μ {b₀}), mul_one]
  -- Apply `tvDist_poisson_le_of_aux_decreasing_coupling` on `P_J` with `Aux = Unit`
  let XJ : Fin n → E × (Fin n → E) → ℕ := fun i z ↦ X i z.1
  let YJ : (i : Fin n) → (E × (Fin n → E)) × Unit → ({j : Fin n // j ≠ i} → ℕ) :=
    fun i z j ↦ X j.1 (z.1.2 i)
  have hXJ_meas : ∀ i : Fin n, Measurable (XJ i) := fun _ ↦ .of_discrete
  have hXJ_zo : ∀ i : Fin n, ∀ᵐ z ∂P_J, XJ i z = 0 ∨ XJ i z = 1 :=
    fun i ↦ Eventually.of_forall fun z ↦ hX_zo i z.1
  have hpJ_eq : ∀ i : Fin n, P_J.real {z | XJ i z = 1} = p i := by
    intro i
    change P_J.real (Prod.fst ⁻¹' {b : E | X i b = 1}) = p i
    rw [← map_measureReal_apply Measurable.of_discrete .of_discrete, hPJ_fst]
  have hlamJ : (r : ℝ) = ∑ i : Fin n, P_J.real {z | XJ i z = 1} := by
    simp_rw [hpJ_eq]
    exact hlam
  have hYJ_meas : ∀ i : Fin n, Measurable (YJ i) := fun _ ↦ .of_discrete
  let Q_unit : Measure Unit := Measure.dirac ()
  have hfst_unit : (P_J.prod Q_unit).map Prod.fst = P_J := Measure.fst_prod
  have hYJ_law : ∀ i : Fin n, 0 < P_J.real {z | XJ i z = 1} →
      (P_J.prod Q_unit).map (YJ i) =
        (ProbabilityTheory.cond P_J {z | XJ i z = 1}).map
          (fun z (j : {j : Fin n // j ≠ i}) ↦ XJ j z) := by
    intro i hi_pos
    rw [hpJ_eq i] at hi_pos
    have h1 : (P_J.prod Q_unit).map (YJ i) =
        P_J.map (fun z : E × (Fin n → E) ↦ fun j : {j : Fin n // j ≠ i} ↦ X j.1 (z.2 i)) := by
      change (P_J.prod Q_unit).map
        ((fun z : E × (Fin n → E) ↦ fun j : {j : Fin n // j ≠ i} ↦ X j.1 (z.2 i)) ∘ Prod.fst) = _
      rw [← Measure.map_map Measurable.of_discrete measurable_fst, hfst_unit]
    have h2 : P_J.map (fun z : E × (Fin n → E) ↦ z.2 i) =
        ProbabilityTheory.cond μ {b | X i b = 1} := by
      change P_J.map (Prod.snd ∘ fun z : E × (Fin n → E) ↦ (z.1, z.2 i)) = _
      rw [← Measure.map_map measurable_snd Measurable.of_discrete, hPJ_pair i, hν_snd i hi_pos]
    have h3 : P_J.map (fun z : E × (Fin n → E) ↦ fun j : {j : Fin n // j ≠ i} ↦ X j.1 (z.2 i)) =
        (ProbabilityTheory.cond μ {b | X i b = 1}).map
          (fun b (j : {j : Fin n // j ≠ i}) ↦ X j.1 b) := by
      rw [← h2, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
      rfl
    have h4 := cond_preimage_map_comp P_J μ (f := Prod.fst) Measurable.of_discrete hPJ_fst
      (A := {b : E | X i b = 1}) .of_discrete
      (g := fun b (j : {j : Fin n // j ≠ i}) ↦ X j.1 b) Measurable.of_discrete
    rw [h1, h3]
    exact h4.symm
  have hYJ_le : ∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i},
      ∀ᵐ z ∂(P_J.prod Q_unit), YJ i z j ≤ XJ j.1 z.1 := by
    intro i j
    have hpair_ae : ∀ᵐ z : E × (Fin n → E) ∂P_J, X j.1 (z.2 i) ≤ X j.1 z.1 := by
      have hset : MeasurableSet
          {u : E × E | ∀ k : Fin n, k ≠ i → X k u.2 ≤ X k u.1} := .of_discrete
      have hpulled := (ae_map_iff (f := fun z : E × (Fin n → E) ↦ (z.1, z.2 i))
        Measurable.of_discrete.aemeasurable hset).mp ((hPJ_pair i).symm ▸ hν_le i)
      filter_upwards [hpulled] with z hz
      exact hz j.1 j.2
    have hset₂ : MeasurableSet {z : E × (Fin n → E) | X j.1 (z.2 i) ≤ X j.1 z.1} := .of_discrete
    exact (ae_map_iff (f := Prod.fst) measurable_fst.aemeasurable hset₂).mp
      (hfst_unit.symm ▸ hpair_ae)
  have hmain := tvDist_poisson_le_of_aux_decreasing_coupling P_J Q_unit P'
    hXJ_meas hXJ_zo hr hlamJ hYJ_meas hYJ_law hYJ_le hZ_meas hZ_law
  have hmap_W : P_J.map (fun z : E × (Fin n → E) ↦ ∑ i : Fin n, XJ i z) = μ.map W := by
    change P_J.map (W ∘ Prod.fst) = μ.map W
    rw [← Measure.map_map Measurable.of_discrete Measurable.of_discrete, hPJ_fst]
  have hvar_W : ProbabilityTheory.variance
      (fun z : E × (Fin n → E) ↦ ((∑ i : Fin n, XJ i z : ℕ) : ℝ)) P_J =
      ProbabilityTheory.variance (fun b : E ↦ (W b : ℝ)) μ := by
    have h := ProbabilityTheory.variance_map (μ := P_J)
      (X := fun b : E ↦ (W b : ℝ)) (Y := Prod.fst)
      Measurable.of_discrete.aemeasurable measurable_fst.aemeasurable
    rw [hPJ_fst] at h
    exact h.symm
  rwa [hmap_W, hvar_W] at hmain

/-- **Pointwise Decreasing Coupling Space from Pairwise Couplings on a Finite State Space**:
glues pairwise conditional couplings `ν_i` on `E : Type` into a single discrete probability space
`(Ωc, Pc)` carrying `Xc` with the joint law of `X` under `μ` and conditional vectors `Yc i`
matching `(cond μ {X i = 1}).map (X_{≠ i})` and satisfying `Yc i ωc j ≤ Xc j.1 ωc` everywhere. -/
theorem exists_fintype_decreasing_coupling_space
    {E : Type} [Finite E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → E → ℕ}
    (hex : ∀ i : Fin n, 0 < μ.real {b | X i b = 1} →
      ∃ (ν : Measure (E × E)), IsProbabilityMeasure ν ∧
        ν.map Prod.fst = μ ∧
        ν.map Prod.snd = ProbabilityTheory.cond μ {b | X i b = 1} ∧
        (∀ᵐ z ∂ν, ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1)) :
    ∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = μ.map (fun b i ↦ X i b) ∧
      (∀ i : Fin n, 0 < μ.real {b | X i b = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond μ {b | X i b = 1}).map
            (fun b (j : {j : Fin n // j ≠ i}) ↦ X j.1 b)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc) := by
  classical
  cases nonempty_fintype E
  let p : Fin n → ℝ := fun i ↦ μ.real {b | X i b = 1}
  let ν : Fin n → Measure (E × E) := fun i ↦
    if hi : 0 < p i then (hex i hi).choose else μ.map (fun b ↦ (b, b))
  have hν_fst : ∀ i : Fin n, (ν i).map Prod.fst = μ := by
    intro i
    by_cases hi : 0 < p i
    · simpa [ν, hi] using (hex i hi).choose_spec.2.1
    · simp only [ν, hi, ↓reduceDIte]
      rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
      exact Measure.map_id
  have hν_snd : ∀ i : Fin n, 0 < p i →
      (ν i).map Prod.snd = ProbabilityTheory.cond μ {b | X i b = 1} := fun i hi ↦ by
    simpa [ν, hi] using (hex i hi).choose_spec.2.2.1
  have hν_le : ∀ i : Fin n, ∀ᵐ z ∂(ν i), ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1 := by
    intro i
    by_cases hi : 0 < p i
    · simpa [ν, hi] using (hex i hi).choose_spec.2.2.2
    · simp only [ν, hi, ↓reduceDIte]
      have hset : MeasurableSet
          {z : E × E | ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1} := .of_discrete
      rw [ae_map_iff Measurable.of_discrete.aemeasurable hset]
      exact Eventually.of_forall fun b _ _ ↦ le_rfl
  have hν_row_sum : ∀ (i : Fin n) (b : E), (∑ b' : E, (ν i) {(b, b')}) = μ {b} := by
    intro i b
    have hmap := congrArg (fun m : Measure E ↦ m {b}) (hν_fst i)
    rw [measure_map_singleton_fintype (ν i) Prod.fst b] at hmap
    have hfilt : (Finset.univ.filter fun z : E × E ↦ z.1 = b) =
        Finset.univ.map ⟨fun b' : E ↦ (b, b'), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
      ext ⟨b₁, b₂⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨fun h ↦ ⟨b₂, Prod.ext h.symm rfl⟩, fun ⟨_, h⟩ ↦ (Prod.mk.inj h).1.symm⟩
    rw [hfilt, Finset.sum_map] at hmap
    exact hmap
  let w : E × (Fin n → E) → ℝ≥0∞ := fun z ↦
    if μ {z.1} = 0 then 0 else μ {z.1} * ∏ i : Fin n, ((ν i) {(z.1, z.2 i)} * (μ {z.1})⁻¹)
  have hrow_factor : ∀ (b : E) (h0 : μ {b} ≠ 0) (i : Fin n),
      (∑ b' : E, ((ν i) {(b, b')} * (μ {b})⁻¹)) = 1 := by
    intro b h0 i
    rw [← Finset.sum_mul, hν_row_sum i b]
    exact ENNReal.mul_inv_cancel h0 (measure_ne_top μ {b})
  have hsum_y_eq : ∀ b : E, (∑ y : Fin n → E, w (b, y)) = μ {b} := by
    intro b
    by_cases h0 : μ {b} = 0
    · simp [w, h0]
    · simp only [w, h0, ↓reduceIte]
      rw [← Finset.mul_sum,
        ← Fintype.prod_sum (fun (i : Fin n) (b' : E) ↦ (ν i) {(b, b')} * (μ {b})⁻¹)]
      simp_rw [hrow_factor b h0]
      simp
  have hsum_w : HasSum w 1 := by
    suffices h : (∑ z : E × (Fin n → E), w z) = 1 from h ▸ hasSum_fintype w
    rw [Fintype.sum_prod_type]
    simp_rw [hsum_y_eq]
    rw [sum_measure_singleton_fintype μ, measure_univ]
  let pmfJ : PMF (E × (Fin n → E)) := ⟨w, hsum_w⟩
  let Pc : Measure (E × (Fin n → E)) := pmfJ.toMeasure
  have : IsProbabilityMeasure Pc := PMF.toMeasure.isProbabilityMeasure pmfJ
  have hPc_singleton : ∀ z : E × (Fin n → E), Pc {z} = w z :=
    fun z ↦ PMF.toMeasure_apply_singleton pmfJ z .of_discrete
  have hPc_fst : Pc.map Prod.fst = μ := by
    refine measure_ext_of_singleton_fintype fun b ↦ ?_
    rw [measure_map_singleton_fintype Pc Prod.fst b]
    have hfilt : (Finset.univ.filter fun z : E × (Fin n → E) ↦ z.1 = b) =
        Finset.univ.map ⟨fun y : Fin n → E ↦ (b, y), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
      ext ⟨b₁, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      exact ⟨fun h ↦ ⟨y, Prod.ext h.symm rfl⟩, fun ⟨_, h⟩ ↦ (Prod.mk.inj h).1.symm⟩
    rw [hfilt, Finset.sum_map]
    simp_rw [hPc_singleton]
    exact hsum_y_eq b
  have hPc_pair : ∀ i : Fin n, Pc.map (fun z : E × (Fin n → E) ↦ (z.1, z.2 i)) = ν i := by
    intro i
    refine measure_ext_of_singleton_fintype fun ⟨b₀, b₁⟩ ↦ ?_
    rw [measure_map_singleton_fintype Pc (fun z : E × (Fin n → E) ↦ (z.1, z.2 i)) (b₀, b₁)]
    let emb : ({j : Fin n // j ≠ i} → E) ↪ E × (Fin n → E) :=
      ⟨fun g ↦ (b₀, fun k ↦ if hk : k = i then b₁ else g ⟨k, hk⟩), by
        intro g₁ g₂ h
        have hy := (Prod.mk.inj h).2
        funext j
        have hj := congrFun hy j.1
        simpa [j.2] using hj⟩
    have hfilt : (Finset.univ.filter fun z : E × (Fin n → E) ↦ (z.1, z.2 i) = (b₀, b₁)) =
        Finset.univ.map emb := by
      ext ⟨b, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, Finset.mem_map, emb]
      constructor
      · rintro ⟨rfl, rfl⟩
        refine ⟨fun j ↦ y j.1, Prod.ext rfl ?_⟩
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · rintro ⟨g, h⟩
        rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        simp
    rw [hfilt, Finset.sum_map]
    by_cases h0 : μ {b₀} = 0
    · have hle : (ν i) {(b₀, b₁)} ≤ μ {b₀} := by
        rw [← hν_row_sum i b₀]
        exact Finset.single_le_sum (f := fun b' ↦ (ν i) {(b₀, b')})
          (fun _ _ ↦ zero_le) (Finset.mem_univ b₁)
      have hν0 : (ν i) {(b₀, b₁)} = 0 := le_antisymm (hle.trans (le_of_eq h0)) zero_le
      rw [hν0]
      refine Finset.sum_eq_zero fun g _ ↦ ?_
      rw [hPc_singleton]
      exact ite_eq_left h0
    · have hw_eval : ∀ g : {j : Fin n // j ≠ i} → E,
          Pc {emb g} =
            μ {b₀} * ∏ k : Fin n,
              ((ν k) {(b₀, if hk : k = i then b₁ else g ⟨k, hk⟩)} * (μ {b₀})⁻¹) := by
        intro g
        rw [hPc_singleton]
        change (if μ {b₀} = 0 then 0 else
          μ {b₀} * ∏ k : Fin n,
            ((ν k) {(b₀, if hk : k = i then b₁ else g ⟨k, hk⟩)} * (μ {b₀})⁻¹)) = _
        rw [ite_eq_right h0]
      simp_rw [hw_eval]
      have hprod_split : ∀ g : {j : Fin n // j ≠ i} → E,
          (∏ k : Fin n, ((ν k) {(b₀, if hk : k = i then b₁ else g ⟨k, hk⟩)} * (μ {b₀})⁻¹)) =
            ((ν i) {(b₀, b₁)} * (μ {b₀})⁻¹) *
              ∏ j : {j : Fin n // j ≠ i}, ((ν j.1) {(b₀, g j)} * (μ {b₀})⁻¹) := by
        intro g
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        congr 1
        · simp
        · refine Finset.prod_bij (fun (x : Fin n) (hx : x ∈ Finset.univ.erase i) ↦
              (⟨x, Finset.ne_of_mem_erase hx⟩ : {j : Fin n // j ≠ i}))
            (fun _ _ ↦ Finset.mem_univ _)
            (fun _ _ _ _ h ↦ by simpa using congrArg Subtype.val h)
            (fun j _ ↦ ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩, Subtype.ext rfl⟩)
            (fun x hx ↦ ?_)
          simp [Finset.ne_of_mem_erase hx]
      have hsum_prod :
          (∑ g : {j : Fin n // j ≠ i} → E,
            ∏ j : {j : Fin n // j ≠ i}, ((ν j.1) {(b₀, g j)} * (μ {b₀})⁻¹)) = 1 := by
        rw [← Fintype.prod_sum
          (fun (j : {j : Fin n // j ≠ i}) (b' : E) ↦ (ν j.1) {(b₀, b')} * (μ {b₀})⁻¹)]
        refine Finset.prod_eq_one fun j _ ↦ ?_
        exact hrow_factor b₀ h0 j.1
      simp_rw [hprod_split, ← mul_assoc]
      rw [← Finset.mul_sum, hsum_prod, mul_one]
      rw [mul_comm (μ {b₀}), mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top μ {b₀}), mul_one]
  let Xc : Fin n → E × (Fin n → E) → ℕ := fun i z ↦ X i z.1
  let Yc : (i : Fin n) → E × (Fin n → E) → ({j : Fin n // j ≠ i} → ℕ) :=
    fun i z j ↦ if ∀ k : Fin n, k ≠ i → X k (z.2 i) ≤ X k z.1 then X j.1 (z.2 i) else X j.1 z.1
  refine ⟨E × (Fin n → E), inferInstance, Pc, inferInstance, Xc, Yc,
    fun _ ↦ .of_discrete, fun _ ↦ .of_discrete, ?_, ?_, ?_⟩
  · change Pc.map ((fun b i ↦ X i b) ∘ Prod.fst) = μ.map (fun b i ↦ X i b)
    rw [← Measure.map_map Measurable.of_discrete measurable_fst, hPc_fst]
  · intro i hi_pos
    have hae : Yc i =ᵐ[Pc]
        fun z : E × (Fin n → E) ↦ fun j : {j : Fin n // j ≠ i} ↦ X j.1 (z.2 i) := by
      have hset : MeasurableSet {u : E × E | ∀ k : Fin n, k ≠ i → X k u.2 ≤ X k u.1} :=
        .of_discrete
      have hpulled := (ae_map_iff (f := fun z : E × (Fin n → E) ↦ (z.1, z.2 i))
        Measurable.of_discrete.aemeasurable hset).mp ((hPc_pair i).symm ▸ hν_le i)
      filter_upwards [hpulled] with z hz
      funext j
      exact ite_eq_left_iff.mpr fun h ↦ absurd hz h
    rw [Measure.map_congr hae]
    have h2 : Pc.map (fun z : E × (Fin n → E) ↦ z.2 i) =
        ProbabilityTheory.cond μ {b | X i b = 1} := by
      change Pc.map (Prod.snd ∘ fun z : E × (Fin n → E) ↦ (z.1, z.2 i)) = _
      rw [← Measure.map_map measurable_snd Measurable.of_discrete, hPc_pair i, hν_snd i hi_pos]
    rw [← h2, Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    rfl
  · intro i z j
    dsimp [Yc, Xc]
    split_ifs with h
    · exact h j.1 j.2
    · exact le_rfl

end SteinMethod
