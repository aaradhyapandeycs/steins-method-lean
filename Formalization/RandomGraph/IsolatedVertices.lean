/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Statements.Sec3
import Formalization.RandomGraph.ErdosRenyi
import Formalization.RandomGraph.IsolatedCoupling
import Formalization.RandomGraph.IsolatedMoments
import Formalization.SizeBias.Basic
import Formalization.Exchangeable.SteinPairBound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Asymptotic Normal Approximation for Isolated Vertices (`IsolatedVertices.lean`)

Implements Theorem 3.17 (`Thm3_17_proof`, `SteinIntro.tex:1413-1420`, nested inside Example 3.9
`\label{ex72}`) of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `Thm3_17_proof`: under $n^\alpha p_n \to c \in (0, \infty)$ with $1 \le \alpha < 2$, the
  standardized isolated-vertex count $W_n = (X_n - \mu_n) / \sigma_n$ in $G(n, p_n)$ satisfies
  $d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1)) \le C / \sigma_n$ eventually via
  Theorem 3.13 (`sizeBias_wassersteinDist_le`) and `Ex3_9_sizeBias_proof`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### Finite-Space $L^p$, Exponential, Variance, and Product Conditional-Expectation Helpers -/

section Helpers

private lemma memLp_of_finite {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (q : ℝ≥0∞) :
    MemLp f q μ := by
  have := Fintype.ofFinite α
  exact MemLp.of_bound (measurable_of_finite f).aestronglyMeasurable
    (∑ x : α, ‖f x‖) (Eventually.of_forall fun x ↦
      Finset.single_le_sum (fun y _ ↦ norm_nonneg (f y)) (Finset.mem_univ x))

private lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hexp_pos : 0 < Real.exp (2 * x) := Real.exp_pos (2 * x)
  have h1 : 1 ≤ Real.exp (2 * x) * (1 - x) := calc
    1 ≤ 1 + x * (1 - 2 * x) := by nlinarith
    _ = (2 * x + 1) * (1 - x) := by ring
    _ ≤ Real.exp (2 * x) * (1 - x) :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * x)) (by linarith)
  rw [show -2 * x = -(2 * x) by ring, Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀' hexp_pos).mpr h1

private lemma one_sub_pow_le_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∀ k : ℕ, 1 - (1 - x) ^ k ≤ (k : ℝ) * x
  | 0 => by simp
  | k + 1 => by
      have ih := one_sub_pow_le_mul hx0 hx1 k
      have hmul : (1 - (1 - x) ^ k) * (1 - x) ≤ (k : ℝ) * x * 1 := by
        have hpow_le : (1 - x) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
        nlinarith
      push_cast
      linarith [show 1 - (1 - x) ^ (k + 1) = (1 - (1 - x) ^ k) * (1 - x) + x by ring]

private lemma variance_fun_add_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {A B : α → ℝ} (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    ProbabilityTheory.variance (fun x ↦ A x + B x) μ ≤
      2 * ProbabilityTheory.variance A μ + 2 * ProbabilityTheory.variance B μ := by
  have hAi : Integrable A μ := hA.integrable one_le_two
  have hBi : Integrable B μ := hB.integrable one_le_two
  have hA2 : Integrable (fun x ↦ (A x - ∫ y, A y ∂μ) ^ 2) μ :=
    (hA.sub (memLp_const _)).integrable_sq
  have hB2 : Integrable (fun x ↦ (B x - ∫ y, B y ∂μ) ^ 2) μ :=
    (hB.sub (memLp_const _)).integrable_sq
  have hAB : MemLp (fun x ↦ A x + B x) 2 μ := hA.add hB
  rw [ProbabilityTheory.variance_eq_integral hAB.aemeasurable,
    ProbabilityTheory.variance_eq_integral hA.aemeasurable,
    ProbabilityTheory.variance_eq_integral hB.aemeasurable,
    integral_add hAi hBi, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hA2.const_mul 2) (hB2.const_mul 2)]
  refine integral_mono_ae ((hAB.sub (memLp_const _)).integrable_sq)
    ((hA2.const_mul 2).add (hB2.const_mul 2)) (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  nlinarith [sq_nonneg ((A x - ∫ y, A y ∂μ) - (B x - ∫ y, B y ∂μ))]

private lemma condExp_fst_prod_finite {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : α × β → ℝ) :
    (fun ω : α × β ↦ ∫ b, f (ω.1, b) ∂ν) =ᵐ[μ.prod ν]
      (μ.prod ν)[f | MeasurableSpace.comap Prod.fst inferInstance] := by
  let g₀ : α → ℝ := fun a ↦ ∫ b, f (a, b) ∂ν
  have hg_sm : StronglyMeasurable[MeasurableSpace.comap (Prod.fst : α × β → α) inferInstance]
      (g₀ ∘ Prod.fst) :=
    (measurable_of_finite g₀).stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
  have hf_int : Integrable f (μ.prod ν) := Integrable.of_finite
  have hg_int : Integrable (g₀ ∘ Prod.fst) (μ.prod ν) := Integrable.of_finite
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf_int
    (fun _ _ _ ↦ hg_int.integrableOn) (fun s hs _ ↦ ?_) hg_sm.aestronglyMeasurable
  rcases hs with ⟨A, hA, rfl⟩
  have hs_meas : MeasurableSet (Prod.fst ⁻¹' A : Set (α × β)) := measurable_fst hA
  change ∫ x in Prod.fst ⁻¹' A, (g₀ ∘ Prod.fst) x ∂(μ.prod ν) = _
  rw [← integral_indicator hs_meas, ← integral_indicator hs_meas,
    integral_prod _ (hg_int.indicator hs_meas), integral_prod _ (hf_int.indicator hs_meas)]
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  dsimp only
  by_cases ha : a ∈ A
  · have h1 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator (g₀ ∘ Prod.fst) (a, b)) =
        fun _ ↦ g₀ a :=
      funext fun _ ↦ Set.indicator_of_mem (s := Prod.fst ⁻¹' A) ha (g₀ ∘ Prod.fst)
    have h2 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator f (a, b)) = fun b ↦ f (a, b) :=
      funext fun _ ↦ Set.indicator_of_mem (s := Prod.fst ⁻¹' A) ha f
    rw [h1, h2, integral_const, probReal_univ, one_smul]
  · have h1 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator (g₀ ∘ Prod.fst) (a, b)) = 0 :=
      funext fun _ ↦ Set.indicator_of_notMem (s := Prod.fst ⁻¹' A) ha (g₀ ∘ Prod.fst)
    have h2 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator f (a, b)) = 0 :=
      funext fun _ ↦ Set.indicator_of_notMem (s := Prod.fst ⁻¹' A) ha f
    rw [h1, h2]

end Helpers

/-! ### Fixed-`(n, p)` Moment and Size-Bias Wasserstein Bounds -/

section FixedGraphBounds

private noncomputable def isoInd (n : ℕ) (i : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator 1 G

private noncomputable def isoCount (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ i : Fin n, isoInd n i G

private noncomputable def degOneNbr (n : ℕ) (i : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ)

private noncomputable def posDegInd (n : ℕ) (i : Fin n) (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | 0 < (H.neighborSet i).ncard}.indicator 1 G

private noncomputable def avgDelta (n : ℕ) (G : SimpleGraph (Fin n)) : ℝ :=
  (n : ℝ)⁻¹ * ((∑ i : Fin n, degOneNbr n i G) + ((n : ℝ) - isoCount n G))

private noncomputable def thm317Const (c : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * Real.sqrt ((8 + 8 * c ^ 2) / Real.exp (-8 * c)) +
    (4 + 4 * c) / Real.exp (-8 * c)

private lemma posDegInd_eq_one_sub_isoInd {n : ℕ} (i : Fin n) (H : SimpleGraph (Fin n)) :
    posDegInd n i H = 1 - isoInd n i H := by
  by_cases hiso : H.IsIsolated i
  · have hnot : ¬ 0 < (H.neighborSet i).ncard := by
      rwa [← not_isIsolated_iff_neighborSet_ncard_pos, not_not]
    have h1 : posDegInd n i H = 0 := Set.indicator_of_notMem hnot 1
    have h2 : isoInd n i H = 1 := Set.indicator_of_mem hiso 1
    linarith
  · have hpos : 0 < (H.neighborSet i).ncard :=
      (not_isIsolated_iff_neighborSet_ncard_pos H i).mp hiso
    have h1 : posDegInd n i H = 1 := Set.indicator_of_mem hpos 1
    have h2 : isoInd n i H = 0 := Set.indicator_of_notMem hiso 1
    linarith

private lemma posDegInd_sq {n : ℕ} (i : Fin n) (H : SimpleGraph (Fin n)) :
    posDegInd n i H ^ 2 = posDegInd n i H := by
  by_cases hpos : 0 < (H.neighborSet i).ncard
  · have h : posDegInd n i H = 1 := Set.indicator_of_mem hpos 1
    rw [h, one_pow]
  · have h : posDegInd n i H = 0 := Set.indicator_of_notMem hpos 1
    rw [h, sq, mul_zero]

private lemma isoCount_mean_bounds {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ (∫ G, isoCount n G ∂erdosRenyi n p) ∧
      (∫ G, isoCount n G ∂erdosRenyi n p) ≤ (n : ℝ) := by
  have hval : ∫ G, isoCount n G ∂erdosRenyi n p = (n : ℝ) * (1 - p) ^ (n - 1) :=
    isolatedCount_integral hp0 hp1
  rw [hval]
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpow_nn : 0 ≤ (1 - p) ^ (n - 1) := pow_nonneg (by linarith) _
  have hpow_le : (1 - p) ^ (n - 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  exact ⟨mul_nonneg hn0 hpow_nn, mul_le_of_le_one_right hn0 hpow_le⟩

private lemma isoCount_variance_bounds {n : ℕ} {p c : ℝ}
    (hn2 : 2 ≤ n) (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2) (hnp_lt : (n : ℝ) * p < 2 * c) :
    Real.exp (-8 * c) * (n : ℝ) ^ 2 * p ≤
        ProbabilityTheory.variance (isoCount n) (erdosRenyi n p) ∧
      ProbabilityTheory.variance (isoCount n) (erdosRenyi n p) ≤ 2 * (n : ℝ) ^ 2 * p := by
  have hp1 : p ≤ 1 := by linarith
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hv_val : ProbabilityTheory.variance (isoCount n) (erdosRenyi n p) =
      (n : ℝ) * (1 - p) ^ (n - 1) * (1 + ((n : ℝ) * p - 1) * (1 - p) ^ (n - 2)) :=
    isolatedCount_variance hp0 hp1 hn2
  rw [hv_val]
  set u₁ : ℝ := (1 - p) ^ (n - 1)
  set u₂ : ℝ := (1 - p) ^ (n - 2)
  have hu₁_nn : 0 ≤ u₁ := pow_nonneg (by linarith) _
  have hu₁_le : u₁ ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hu₂_nn : 0 ≤ u₂ := pow_nonneg (by linarith) _
  have hu₂_le : u₂ ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · have hB_lo : (n : ℝ) * p * u₂ ≤ 1 + ((n : ℝ) * p - 1) * u₂ := by linarith
    have hpow_add : u₁ * u₂ = (1 - p) ^ (2 * n - 3) := by
      rw [← pow_add, show (n - 1) + (n - 2) = 2 * n - 3 by omega]
    have hexp_le : Real.exp (-8 * c) ≤ (1 - p) ^ (2 * n - 3) := by
      have hk_le : ((2 * n - 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        exact_mod_cast Nat.sub_le (2 * n) 3
      calc
        Real.exp (-8 * c)
          ≤ Real.exp (((2 * n - 3 : ℕ) : ℝ) * (-2 * p)) := by
            rw [Real.exp_le_exp]
            nlinarith
        _ = Real.exp (-2 * p) ^ (2 * n - 3) := Real.exp_nat_mul (-2 * p) (2 * n - 3)
        _ ≤ (1 - p) ^ (2 * n - 3) :=
            pow_le_pow_left₀ (Real.exp_nonneg _) (exp_neg_two_mul_le_one_sub hp0 hp_half) _
    calc
      Real.exp (-8 * c) * (n : ℝ) ^ 2 * p
        = (n : ℝ) ^ 2 * p * Real.exp (-8 * c) := by ring
      _ ≤ (n : ℝ) ^ 2 * p * (1 - p) ^ (2 * n - 3) :=
          mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = (n : ℝ) * u₁ * ((n : ℝ) * p * u₂) := by rw [← hpow_add]; ring
      _ ≤ (n : ℝ) * u₁ * (1 + ((n : ℝ) * p - 1) * u₂) :=
          mul_le_mul_of_nonneg_left hB_lo (mul_nonneg hn_nn hu₁_nn)
  · have h1_le : 1 - u₂ ≤ (n : ℝ) * p :=
      (one_sub_pow_le_mul hp0 hp1 (n - 2)).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 2) hp0)
    have h2_le : (n : ℝ) * p * u₂ ≤ (n : ℝ) * p :=
      mul_le_of_le_one_right (mul_nonneg hn_nn hp0) hu₂_le
    have hB_hi : 1 + ((n : ℝ) * p - 1) * u₂ ≤ 2 * (n : ℝ) * p := by linarith
    have hB_nn : 0 ≤ 1 + ((n : ℝ) * p - 1) * u₂ := by
      have : 0 ≤ (n : ℝ) * p * u₂ := mul_nonneg (mul_nonneg hn_nn hp0) hu₂_nn
      linarith
    calc
      (n : ℝ) * u₁ * (1 + ((n : ℝ) * p - 1) * u₂)
        ≤ (n : ℝ) * (2 * (n : ℝ) * p) :=
          mul_le_mul (mul_le_of_le_one_right hn_nn hu₁_le) hB_hi hB_nn hn_nn
      _ = 2 * (n : ℝ) ^ 2 * p := by ring

private lemma avgDelta_variance_le {n : ℕ} {p c : ℝ}
    (hn3 : 3 ≤ n) (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2)
    (hnp_lt : (n : ℝ) * p < 2 * c) :
    ProbabilityTheory.variance (avgDelta n) (erdosRenyi n p) ≤ (8 + 8 * c ^ 2) * p := by
  have hp1 : p ≤ 1 := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  let μG := erdosRenyi n p
  let S_D : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, degOneNbr n i H
  let N_sub_X : SimpleGraph (Fin n) → ℝ := fun H ↦ (n : ℝ) - isoCount n H
  have hvar_SD : ProbabilityTheory.variance S_D μG ≤ (2 + 4 * c ^ 2) * (n : ℝ) ^ 2 * p := by
    have h1 := sum_degOneNeighbor_variance_le hp0 hp1 hn3
    have hnp2 : ((n : ℝ) * p) ^ 2 ≤ (2 * c) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnp_lt.le 2
    have h2 : (n : ℝ) ^ 4 * p ^ 3 ≤ 4 * c ^ 2 * (n : ℝ) ^ 2 * p := calc
      (n : ℝ) ^ 4 * p ^ 3 = ((n : ℝ) * p) ^ 2 * ((n : ℝ) ^ 2 * p) := by ring
      _ ≤ (2 * c) ^ 2 * ((n : ℝ) ^ 2 * p) := mul_le_mul_of_nonneg_right hnp2 (by positivity)
      _ = 4 * c ^ 2 * (n : ℝ) ^ 2 * p := by ring
    change ProbabilityTheory.variance S_D μG ≤ _ at h1
    linarith
  have hvar_NX : ProbabilityTheory.variance N_sub_X μG ≤ 2 * (n : ℝ) ^ 2 * p := by
    rw [ProbabilityTheory.variance_const_sub
      (measurable_of_finite (isoCount n)).aestronglyMeasurable]
    exact (isoCount_variance_bounds (by omega) hp0 hp_half hnp_lt).2
  have hadd_le := variance_fun_add_le μG (memLp_of_finite μG S_D 2)
    (memLp_of_finite μG N_sub_X 2)
  have hmul : ProbabilityTheory.variance (avgDelta n) μG =
      ((n : ℝ)⁻¹) ^ 2 * ProbabilityTheory.variance (fun H ↦ S_D H + N_sub_X H) μG :=
    ProbabilityTheory.variance_const_mul (n : ℝ)⁻¹ (fun H ↦ S_D H + N_sub_X H) μG
  rw [hmul]
  calc
    ((n : ℝ)⁻¹) ^ 2 * ProbabilityTheory.variance (fun H ↦ S_D H + N_sub_X H) μG
      ≤ ((n : ℝ)⁻¹) ^ 2 *
          (2 * ((2 + 4 * c ^ 2) * (n : ℝ) ^ 2 * p) + 2 * (2 * (n : ℝ) ^ 2 * p)) :=
        mul_le_mul_of_nonneg_left (hadd_le.trans (by linarith)) (sq_nonneg _)
    _ = (8 + 8 * c ^ 2) * p := by
        field_simp [hn_pos.ne']
        ring

private lemma delta_slice_sq_integral_le {n : ℕ} {p c : ℝ}
    (hn3 : 3 ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hnp_lt : (n : ℝ) * p < 2 * c) (i : Fin n) :
    ∫ H, (degOneNbr n i H + posDegInd n i H) ^ 2 ∂erdosRenyi n p ≤
      (4 + 4 * c) * (n : ℝ) * p := by
  let μG := erdosRenyi n p
  have hn2 : 2 ≤ n := by omega
  have hpt : ∀ H : SimpleGraph (Fin n),
      (degOneNbr n i H + posDegInd n i H) ^ 2 ≤
        2 * degOneNbr n i H ^ 2 + 2 * posDegInd n i H := fun H ↦ by
    nlinarith [sq_nonneg (degOneNbr n i H - posDegInd n i H), posDegInd_sq i H]
  have hDG2_le : ∫ H, degOneNbr n i H ^ 2 ∂μG ≤ (1 + 2 * c) * (n : ℝ) * p := by
    change ∫ H, ({j : Fin n | H.Adj i j ∧ (H.neighborSet j).ncard = 1}.ncard : ℝ) ^ 2 ∂μG ≤ _
    rw [degOneNeighbor_sq_integral hp0 hp1 hn3 i]
    have hpow1 : (1 - p) ^ (n - 2) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hpow2 : (1 - p) ^ (2 * n - 5) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hpow2_nn : 0 ≤ (1 - p) ^ (2 * n - 5) := pow_nonneg (by linarith) _
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hterm1 : ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) ≤ (n : ℝ) * p := calc
      ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2)
        ≤ ((n : ℝ) - 1) * p :=
          mul_le_of_le_one_right (mul_nonneg (by linarith) hp0) hpow1
      _ ≤ (n : ℝ) * p := mul_le_mul_of_nonneg_right (by linarith) hp0
    have hprod : ((n : ℝ) - 1) * ((n : ℝ) - 2) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hterm2 :
        ((n : ℝ) - 1) * ((n : ℝ) - 2) * p ^ 2 * (1 - p) ^ (2 * n - 5) ≤
          2 * c * (n : ℝ) * p := calc
      ((n : ℝ) - 1) * ((n : ℝ) - 2) * p ^ 2 * (1 - p) ^ (2 * n - 5)
        ≤ (n : ℝ) ^ 2 * p ^ 2 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hprod (sq_nonneg p))
            hpow2 hpow2_nn (by positivity)
      _ = ((n : ℝ) * p) * ((n : ℝ) * p) := by ring
      _ ≤ (2 * c) * ((n : ℝ) * p) :=
          mul_le_mul_of_nonneg_right hnp_lt.le (mul_nonneg (by linarith) hp0)
      _ = 2 * c * (n : ℝ) * p := by ring
    linarith
  have hind_int_le : ∫ H, posDegInd n i H ∂μG ≤ (n : ℝ) * p := by
    have hind_eq : (fun H ↦ posDegInd n i H) = fun H ↦ 1 - isoInd n i H :=
      funext (posDegInd_eq_one_sub_isoInd i)
    have hX_int_eq : ∫ H, isoInd n i H ∂μG = (1 - p) ^ (n - 1) := by
      unfold isoInd
      rw [integral_indicator_one MeasurableSet.of_discrete,
        erdosRenyi_real_isIsolated hp0 hp1 i]
    rw [hind_eq, integral_sub (integrable_const 1) Integrable.of_finite,
      integral_const, probReal_univ, one_smul, hX_int_eq]
    exact (one_sub_pow_le_mul hp0 hp1 (n - 1)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n 1) hp0)
  have hD2_int : Integrable (fun H ↦ degOneNbr n i H ^ 2) μG := Integrable.of_finite
  have hind_int : Integrable (posDegInd n i) μG := Integrable.of_finite
  calc
    ∫ H, (degOneNbr n i H + posDegInd n i H) ^ 2 ∂μG
      ≤ ∫ H, 2 * degOneNbr n i H ^ 2 + 2 * posDegInd n i H ∂μG :=
        integral_mono_ae Integrable.of_finite
          ((hD2_int.const_mul 2).add (hind_int.const_mul 2)) (Eventually.of_forall hpt)
    _ = 2 * (∫ H, degOneNbr n i H ^ 2 ∂μG) + 2 * ∫ H, posDegInd n i H ∂μG := by
        rw [integral_add (hD2_int.const_mul 2) (hind_int.const_mul 2),
          integral_const_mul, integral_const_mul]
    _ ≤ 2 * ((1 + 2 * c) * (n : ℝ) * p) + 2 * ((n : ℝ) * p) := by linarith
    _ = (4 + 4 * c) * (n : ℝ) * p := by ring

private lemma combine_stein_bounds {n p c μ v qQX mΔ2 : ℝ}
    (hn_pos : 0 < n) (hp_pos : 0 < p) (hc : 0 < c) (hμ_le : μ ≤ n)
    (hv_lo : Real.exp (-8 * c) * n ^ 2 * p ≤ v)
    (hq_le : qQX ≤ (8 + 8 * c ^ 2) * p)
    (hm_nn : 0 ≤ mΔ2) (hm_le : mΔ2 ≤ (4 + 4 * c) * n * p) :
    let σ := Real.sqrt v
    (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt qQX +
      (μ / σ ^ 3) * mΔ2 ≤ thm317Const c / σ := by
  intro σ
  set q₀ : ℝ := Real.exp (-8 * c)
  have hq₀_pos : 0 < q₀ := Real.exp_pos (-8 * c)
  have hv_pos : 0 < v := lt_of_lt_of_le (by positivity) hv_lo
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hv_pos
  have hσ_sq : σ ^ 2 = v := Real.sq_sqrt hv_pos.le
  rw [le_div_iff₀ hσ_pos]
  have hrew :
      ((μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt qQX + (μ / σ ^ 3) * mΔ2) * σ =
        Real.sqrt (2 / Real.pi) * (μ * (Real.sqrt qQX / σ)) + μ * mΔ2 / v := by
    rw [← hσ_sq]
    field_simp [hσ_pos.ne']
  rw [hrew]
  have hsqrt_div : Real.sqrt qQX / σ ≤ Real.sqrt ((8 + 8 * c ^ 2) / q₀) / n := by
    rw [div_le_iff₀ hσ_pos]
    have hsq : qQX ≤ ((8 + 8 * c ^ 2) / q₀) * (v / n ^ 2) := calc
      qQX ≤ (8 + 8 * c ^ 2) * p := hq_le
      _ = ((8 + 8 * c ^ 2) / q₀) * ((q₀ * n ^ 2 * p) / n ^ 2) := by
          field_simp [hq₀_pos.ne', hn_pos.ne']
      _ ≤ ((8 + 8 * c ^ 2) / q₀) * (v / n ^ 2) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hv_lo (sq_nonneg n)) (by positivity)
    calc
      Real.sqrt qQX
        ≤ Real.sqrt (((8 + 8 * c ^ 2) / q₀) * (v / n ^ 2)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt ((8 + 8 * c ^ 2) / q₀) * Real.sqrt (v / n ^ 2) :=
          Real.sqrt_mul (by positivity) _
      _ = Real.sqrt ((8 + 8 * c ^ 2) / q₀) / n * σ := by
          rw [Real.sqrt_div hv_pos.le, Real.sqrt_sq hn_pos.le]
          ring
  have hterm1 :
      Real.sqrt (2 / Real.pi) * (μ * (Real.sqrt qQX / σ)) ≤
        Real.sqrt (2 / Real.pi) * Real.sqrt ((8 + 8 * c ^ 2) / q₀) := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc
      μ * (Real.sqrt qQX / σ)
        ≤ n * (Real.sqrt ((8 + 8 * c ^ 2) / q₀) / n) :=
          mul_le_mul hμ_le hsqrt_div (div_nonneg (Real.sqrt_nonneg _) hσ_pos.le) hn_pos.le
      _ = Real.sqrt ((8 + 8 * c ^ 2) / q₀) := mul_div_cancel₀ _ hn_pos.ne'
  have hterm2 : μ * mΔ2 / v ≤ (4 + 4 * c) / q₀ := by
    rw [div_le_iff₀ hv_pos]
    calc
      μ * mΔ2
        ≤ n * ((4 + 4 * c) * n * p) := mul_le_mul hμ_le hm_le hm_nn hn_pos.le
      _ = ((4 + 4 * c) / q₀) * (q₀ * n ^ 2 * p) := by
          field_simp [hq₀_pos.ne']
      _ ≤ ((4 + 4 * c) / q₀) * v := mul_le_mul_of_nonneg_left hv_lo (by positivity)
  exact add_le_add hterm1 hterm2

private theorem isolatedVertices_wasserstein_le {n : ℕ} {p c : ℝ}
    (hn3 : 3 ≤ n) (hp_pos : 0 < p) (hp_half : p ≤ 1 / 2) (hc : 0 < c)
    (hnp_lt : (n : ℝ) * p < 2 * c) :
    let μ := ∫ G, isoCount n G ∂erdosRenyi n p
    let σ := Real.sqrt (ProbabilityTheory.variance (isoCount n) (erdosRenyi n p))
    let W := fun G : SimpleGraph (Fin n) ↦ (isoCount n G - μ) / σ
    wassersteinDist ((erdosRenyi n p).map W) stdNormalLaw ≤
      ENNReal.ofReal (thm317Const c / σ) := by
  intro μ σ W
  have hn0 : 0 < n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hp0 : 0 ≤ p := hp_pos.le
  have hp1_lt : p < 1 := by linarith
  have hp1_le : p ≤ 1 := hp1_lt.le
  obtain ⟨hμ_nn, hμ_le_n⟩ := isoCount_mean_bounds (n := n) hp0 hp1_le
  obtain ⟨hv_lo, _⟩ := isoCount_variance_bounds (by omega : 2 ≤ n) hp0 hp_half hnp_lt
  have hv_pos : 0 < ProbabilityTheory.variance (isoCount n) (erdosRenyi n p) :=
    lt_of_lt_of_le (by
      have := Real.exp_pos (-8 * c)
      positivity) hv_lo
  let μG : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
  let unif_pmf : PMF (Fin n) := @PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn0⟩⟩
  let unif : Measure (Fin n) := unif_pmf.toMeasure
  let P : Measure (SimpleGraph (Fin n) × Fin n) := μG.prod unif
  have hmap_fst : P.map Prod.fst = μG := (measurePreserving_fst (μ := μG) (ν := unif)).map_eq
  have hmap_snd : P.map Prod.snd = unif := (measurePreserving_snd (μ := μG) (ν := unif)).map_eq
  have hindep : ProbabilityTheory.IndepFun
      (Prod.snd : SimpleGraph (Fin n) × Fin n → Fin n) Prod.fst P :=
    (ProbabilityTheory.indepFun_prod (μ := μG) (ν := unif) measurable_id measurable_id).symm
  let X_Ω : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ isoCount n ω.1
  let Xs : SimpleGraph (Fin n) × Fin n → ℝ :=
    fun ω ↦ ∑ i : Fin n, isoInd n i (ω.1.deleteIncidenceSet ω.2)
  let Δ : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ Xs ω - X_Ω ω
  obtain ⟨hSB, hΔ_ident⟩ := Ex3_9_sizeBias_proof P hn0 hp0 hp1_lt
    measurable_fst hmap_fst measurable_snd hindep hmap_snd
  have hΔ_eq : ∀ ω : SimpleGraph (Fin n) × Fin n,
      Δ ω = degOneNbr n ω.2 ω.1 + posDegInd n ω.2 ω.1 := by
    intro ω
    have hstep : Δ ω = degOneNbr n ω.2 ω.1 +
        {ω' : SimpleGraph (Fin n) × Fin n |
          0 < (ω'.1.neighborSet ω'.2).ncard}.indicator
          (1 : SimpleGraph (Fin n) × Fin n → ℝ) ω := hΔ_ident ω
    have hind : {ω' : SimpleGraph (Fin n) × Fin n |
          0 < (ω'.1.neighborSet ω'.2).ncard}.indicator
          (1 : SimpleGraph (Fin n) × Fin n → ℝ) ω = posDegInd n ω.2 ω.1 := by
      by_cases hpos : 0 < (ω.1.neighborSet ω.2).ncard
      · exact (Set.indicator_of_mem hpos 1).trans (Set.indicator_of_mem hpos 1).symm
      · exact (Set.indicator_of_notMem hpos 1).trans (Set.indicator_of_notMem hpos 1).symm
    exact hstep.trans (congrArg (degOneNbr n ω.2 ω.1 + ·) hind)
  have hXΩ_meas : Measurable X_Ω := (measurable_of_finite (isoCount n)).comp measurable_fst
  have hXΩ_nn : 0 ≤ᵐ[P] X_Ω := Eventually.of_forall fun ω ↦
    Finset.sum_nonneg fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ω.1
  have hXΩ_Lp : MemLp X_Ω 2 P := memLp_of_finite P X_Ω 2
  have hμ_Ω : ∫ ω, X_Ω ω ∂P = μ := by
    change ∫ ω, isoCount n ω.1 ∂P = ∫ G, isoCount n G ∂μG
    rw [← hmap_fst]
    exact (integral_map measurable_fst.aemeasurable
      (measurable_of_finite (isoCount n)).aestronglyMeasurable).symm
  have hv_Ω : ProbabilityTheory.variance X_Ω P = ProbabilityTheory.variance (isoCount n) μG := by
    have h := ProbabilityTheory.variance_map (μ := P) (Y := Prod.fst) (X := isoCount n)
      (hmap_fst ▸ (measurable_of_finite (isoCount n)).aemeasurable) measurable_fst.aemeasurable
    rw [hmap_fst] at h
    exact h.symm
  have hσ_Ω : Real.sqrt (ProbabilityTheory.variance X_Ω P) = σ := congrArg Real.sqrt hv_Ω
  have hW_map : P.map (fun ω ↦ (X_Ω ω - ∫ ω', X_Ω ω' ∂P) /
      Real.sqrt (ProbabilityTheory.variance X_Ω P)) = μG.map W := by
    rw [hμ_Ω, hσ_Ω, ← hmap_fst, Measure.map_map (measurable_of_finite W) measurable_fst]
    rfl
  have hSB' : IsSizeBias P X_Ω P Xs := hSB
  have hWass := sizeBias_wassersteinDist_le P stdNormalLaw hXΩ_meas hXΩ_nn hXΩ_Lp
    (hv_Ω.symm ▸ hv_pos) hSB' measurable_id.aemeasurable Measure.map_id
  dsimp only at hWass
  rw [hW_map, Measure.map_id, hμ_Ω, hσ_Ω] at hWass
  let Q_X : SimpleGraph (Fin n) × Fin n → ℝ :=
    P[Δ | MeasurableSpace.comap X_Ω inferInstance]
  have hm_XG : MeasurableSpace.comap X_Ω inferInstance ≤
      MeasurableSpace.comap (Prod.fst : SimpleGraph (Fin n) × Fin n → SimpleGraph (Fin n))
        inferInstance := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨isoCount n ⁻¹' s, measurable_of_finite (isoCount n) hs, rfl⟩
  have hevar_mono : ProbabilityTheory.evariance Q_X P ≤
      ProbabilityTheory.evariance
        (P[Δ | MeasurableSpace.comap Prod.fst inferInstance]) P :=
    evariance_condExp_mono P hm_XG measurable_fst.comap_le Integrable.of_finite
  have hg_avg : ∀ H : SimpleGraph (Fin n), ∫ i, Δ (H, i) ∂unif = avgDelta n H := by
    intro H
    rw [PMF.integral_eq_sum]
    have hunif_toReal : ∀ i : Fin n, (unif_pmf i).toReal = (n : ℝ)⁻¹ := fun i ↦ by
      simp [unif_pmf, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
    have hsum_ind : (∑ i : Fin n, posDegInd n i H) = (n : ℝ) - isoCount n H := by
      simp_rw [posDegInd_eq_one_sub_isoInd]
      simp [Finset.sum_sub_distrib, isoCount]
    simp_rw [hunif_toReal, smul_eq_mul, ← Finset.mul_sum, hΔ_eq]
    rw [Finset.sum_add_distrib, hsum_ind]
    rfl
  have hcond_ae : (avgDelta n ∘ Prod.fst) =ᵐ[P]
      P[Δ | MeasurableSpace.comap Prod.fst inferInstance] := by
    refine (condExp_fst_prod_finite μG unif Δ).mp (Eventually.of_forall fun ω hω ↦ ?_)
    exact (hg_avg ω.1).symm.trans hω
  have hQ_Lp : MemLp Q_X 2 P := memLp_of_finite P Q_X 2
  have hvar_QX : ProbabilityTheory.variance Q_X P ≤ (8 + 8 * c ^ 2) * p := by
    have hg_map : ProbabilityTheory.variance (avgDelta n ∘ Prod.fst) P =
        ProbabilityTheory.variance (avgDelta n) μG := by
      have h := ProbabilityTheory.variance_map (μ := P) (Y := Prod.fst) (X := avgDelta n)
        (hmap_fst ▸ (measurable_of_finite (avgDelta n)).aemeasurable) measurable_fst.aemeasurable
      rw [hmap_fst] at h
      exact h.symm
    have hvar_gG := avgDelta_variance_le hn3 hp0 hp_half hnp_lt
    have hev_le : ProbabilityTheory.evariance Q_X P ≤
        ENNReal.ofReal ((8 + 8 * c ^ 2) * p) := calc
      ProbabilityTheory.evariance Q_X P
        ≤ ProbabilityTheory.evariance
            (P[Δ | MeasurableSpace.comap Prod.fst inferInstance]) P := hevar_mono
      _ = ProbabilityTheory.evariance (avgDelta n ∘ Prod.fst) P :=
          ProbabilityTheory.evariance_congr hcond_ae.symm
      _ = ENNReal.ofReal (ProbabilityTheory.variance (avgDelta n ∘ Prod.fst) P) :=
          (ProbabilityTheory.ofReal_variance (memLp_of_finite P (avgDelta n ∘ Prod.fst) 2)).symm
      _ ≤ ENNReal.ofReal ((8 + 8 * c ^ 2) * p) :=
          ENNReal.ofReal_le_ofReal (hg_map ▸ hvar_gG)
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ProbabilityTheory.ofReal_variance hQ_Lp]
    exact hev_le
  have hΔ2_int_le : ∫ ω, Δ ω ^ 2 ∂P ≤ (4 + 4 * c) * (n : ℝ) * p := by
    have hinner : ∀ i : Fin n, ∫ H, Δ (H, i) ^ 2 ∂μG ≤ (4 + 4 * c) * (n : ℝ) * p := by
      intro i
      simp_rw [hΔ_eq]
      exact delta_slice_sq_integral_le hn3 hp0 hp1_le hnp_lt i
    rw [integral_prod_symm _ (Integrable.of_finite : Integrable (fun ω ↦ Δ ω ^ 2) P)]
    calc
      ∫ i, (∫ H, Δ (H, i) ^ 2 ∂μG) ∂unif
        ≤ ∫ _, (4 + 4 * c) * (n : ℝ) * p ∂unif :=
          integral_mono_ae Integrable.of_finite (integrable_const _) (Eventually.of_forall hinner)
      _ = (4 + 4 * c) * (n : ℝ) * p := by simp [integral_const, probReal_univ]
  have hevar_rpow : ProbabilityTheory.evariance Q_X P ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q_X P)) := by
    rw [← ProbabilityTheory.ofReal_variance hQ_Lp,
      ENNReal.ofReal_rpow_of_nonneg (ProbabilityTheory.variance_nonneg Q_X P) (by positivity),
      ← Real.sqrt_eq_rpow]
  have hlintegral_Δ2 : (∫⁻ ω, ENNReal.ofReal (Δ ω ^ 2) ∂P) =
      ENNReal.ofReal (∫ ω, Δ ω ^ 2 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (Eventually.of_forall fun _ ↦ sq_nonneg _)).symm
  have hInt_nn : 0 ≤ ∫ ω, Δ ω ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  have hreal := combine_stein_bounds hn_pos hp_pos hc hμ_le_n hv_lo hvar_QX hInt_nn hΔ2_int_le
  have hC1_nn : 0 ≤ μ / σ ^ 2 * Real.sqrt (2 / Real.pi) := by positivity
  have hC2_nn : 0 ≤ μ / σ ^ 3 := by positivity
  calc
    wassersteinDist (μG.map W) stdNormalLaw
      ≤ ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) *
            ProbabilityTheory.evariance Q_X P ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (μ / σ ^ 3) * ∫⁻ ω, ENNReal.ofReal (Δ ω ^ 2) ∂P := hWass
    _ = ENNReal.ofReal
          ((μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Real.sqrt (ProbabilityTheory.variance Q_X P) +
            (μ / σ ^ 3) * (∫ ω, Δ ω ^ 2 ∂P)) := by
        rw [hevar_rpow, hlintegral_Δ2, ← ENNReal.ofReal_mul hC1_nn, ← ENNReal.ofReal_mul hC2_nn,
          ← ENNReal.ofReal_add (mul_nonneg hC1_nn (Real.sqrt_nonneg _)) (mul_nonneg hC2_nn hInt_nn)]
    _ ≤ ENNReal.ofReal (thm317Const c / σ) := ENNReal.ofReal_le_ofReal hreal

end FixedGraphBounds

/-! ### Proof of Theorem 3.17 (`Thm3_17_proof`) -/

/-- Theorem 3.17 (`SteinIntro.tex:1413-1420`, inside Example 3.9 `\label{ex72}`): if $X_n$ counts
isolated vertices in $G(n, p_n)$ ($0 \le p_n \le 1$), $W_n = (X_n - \mu_n)/\sigma_n$, and
$n^\alpha p_n \to c \in (0, \infty)$ with $1 \le \alpha < 2$, then
$d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1)) \le C / \sigma_n$ eventually. -/
theorem Thm3_17_proof : Thm3_17 := by
  intro p α c hp hα1 _hα2 hc htend
  refine ⟨thm317Const c, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * c)
  have hev_lo : ∀ᶠ n : ℕ in atTop, c / 2 < (n : ℝ) ^ α * p n :=
    htend.eventually (Ioi_mem_nhds (by linarith : c / 2 < c))
  have hev_hi : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ α * p n < 2 * c :=
    htend.eventually (Iio_mem_nhds (by linarith : c < 2 * c))
  filter_upwards [eventually_ge_atTop (max N 3), hev_lo, hev_hi] with n hn hp_lo hp_hi
  have hn3 : 3 ≤ n := (le_max_right N 3).trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hp0 : 0 ≤ p n := (hp n).1
  have hrpow : (n : ℝ) ≤ (n : ℝ) ^ α := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn_ge1 hα1
  have hnp_lt : (n : ℝ) * p n < 2 * c :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrpow hp0) hp_hi
  have h4c_lt : 4 * c < (n : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast (le_max_left N 3).trans hn)
  have hp_half : p n ≤ 1 / 2 := by
    have hmul : 4 * c * p n ≤ (n : ℝ) * p n := mul_le_mul_of_nonneg_right h4c_lt.le hp0
    nlinarith
  have hp_pos : 0 < p n := by
    by_contra! hle
    have hrpow_pos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hn_pos α
    have hnonpos : (n : ℝ) ^ α * p n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hrpow_pos.le hle
    linarith
  exact isolatedVertices_wasserstein_le hn3 hp_pos hp_half hc hnp_lt

end SteinMethod
