/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Size-Bias Coupling Recipes for Sums (`Formalization.SizeBias.Coupling`)

Formalizes Proposition 3.14 and Corollaries 3.15–3.16 of Nathan Ross,
*"Fundamentals of Stein's method"* (`SteinIntro.tex:1284-1332`):
* `sizeBias_sum_of_condDistrib_recipe`: general conditional-distribution coupling recipe for
  $X = \sum_{i=1}^n X_i$ (`Prop3_14`, `\label{prop71}`, `SteinIntro.tex:1284-1299`).
* `sizeBias_sum_of_iIndepFun`: replace-one coupling $X^s = X - X_I + X_I^s$ for independent
  nonnegative summands (`Cor3_15`, `\label{cor71}`, `SteinIntro.tex:1319-1325`).
* `sizeBias_sum_of_zero_one`: conditional coupling $X^s = \sum_{j \ne I} X_j^{(I)} + 1$ for
  zero-one summands (`Cor3_16`, `\label{cor72}`, `SteinIntro.tex:1326-1332`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SteinMethod

section Helpers

private lemma sum_subtype_ne_eq_erase {n : ℕ} (i : Fin n) (v : Fin n → ℝ) :
    (∑ j : {j : Fin n // j ≠ i}, v j.1) = ∑ j ∈ Finset.univ.erase i, v j :=
  (Finset.sum_subtype (Finset.univ.erase i) (by simp) v).symm

private lemma sum_fin_eq_sum_ne_add {n : ℕ} (i : Fin n) (v : Fin n → ℝ) :
    (∑ k : Fin n, v k) = (∑ j : {j : Fin n // j ≠ i}, v j.1) + v i := by
  rw [sum_subtype_ne_eq_erase, Finset.sum_erase_add _ _ (Finset.mem_univ i)]

/-- When $\mu_U = \mathbb{E}[U] > 0$, any size-biased version $U^s$ has law with density
$x \mapsto x / \mu_U$ with respect to the law of $U$ (`SteinIntro.tex:1224-1230`). -/
private lemma map_sizeBias_eq_withDensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {U Us : Ω → ℝ} (hU_meas : Measurable U) (hUs : IsSizeBias P U P Us)
    (hμU_pos : 0 < ∫ ω, U ω ∂P) :
    P.map Us =
      (P.map U).withDensity (fun x ↦ ENNReal.ofReal (x / ∫ ω, U ω ∂P)) := by
  rcases hUs with ⟨hU_nn, hU_int, hUs_meas, hUs_eq⟩
  set μU : ℝ := ∫ ω, U ω ∂P
  refine Measure.ext fun A hA ↦ ?_
  let indA : ℝ → ℝ := A.indicator (fun _ ↦ (1 : ℝ))
  have hindA_meas : Measurable indA := measurable_const.indicator hA
  have hU_ind_eq : (fun ω ↦ U ω * indA (U ω)) = (U ⁻¹' A).indicator U := by
    funext ω
    by_cases hω : U ω ∈ A <;> simp [indA, hω]
  have hU_ind_int : Integrable (fun ω ↦ U ω * indA (U ω)) P := by
    rw [hU_ind_eq]
    exact hU_int.indicator (hU_meas hA)
  have hUs_real : (P.map Us).real A = ∫ ω, indA (Us ω) ∂P := by
    rw [← integral_map hUs_meas hindA_meas.stronglyMeasurable.aestronglyMeasurable,
      integral_indicator hA, setIntegral_one_eq_measureReal]
  have hreal_eq : (P.map Us).real A = ∫ ω, μU⁻¹ * (U ω * indA (U ω)) ∂P := by
    have hsb := hUs_eq indA hindA_meas hU_ind_int
    rw [← hUs_real] at hsb
    rw [integral_const_mul]
    have hdiv : (P.map Us).real A = (∫ ω, U ω * indA (U ω) ∂P) / μU := by
      rw [hsb, mul_div_cancel_left₀ _ hμU_pos.ne']
    rw [hdiv]
    ring
  have hscaled_nn : 0 ≤ᵐ[P] fun ω ↦ μU⁻¹ * (U ω * indA (U ω)) := by
    filter_upwards [hU_nn] with ω hω
    have hind_nn : 0 ≤ indA (U ω) := by
      by_cases hx : U ω ∈ A <;> simp [indA, hx]
    exact mul_nonneg (inv_nonneg.mpr hμU_pos.le) (mul_nonneg hω hind_nn)
  have hscaled_int : Integrable (fun ω ↦ μU⁻¹ * (U ω * indA (U ω))) P :=
    hU_ind_int.const_mul μU⁻¹
  have hd_meas : Measurable (fun x : ℝ ↦ ENNReal.ofReal (x / μU)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.div_const μU)
  calc
    (P.map Us) A = ENNReal.ofReal ((P.map Us).real A) := (ofReal_measureReal).symm
    _ = ENNReal.ofReal (∫ ω, μU⁻¹ * (U ω * indA (U ω)) ∂P) := by rw [hreal_eq]
    _ = ∫⁻ ω, ENNReal.ofReal (μU⁻¹ * (U ω * indA (U ω))) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hscaled_int hscaled_nn
    _ = ∫⁻ ω, A.indicator (fun x ↦ ENNReal.ofReal (x / μU)) (U ω) ∂P := by
      refine lintegral_congr fun ω ↦ ?_
      by_cases hω : U ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have hind : indA (U ω) = 1 := Set.indicator_of_mem hω _
        rw [hind, mul_one]
        congr 1
        ring
      · rw [Set.indicator_of_notMem hω]
        have hind : indA (U ω) = 0 := Set.indicator_of_notMem hω _
        rw [hind, mul_zero, mul_zero, ENNReal.ofReal_zero]
    _ = ∫⁻ x, A.indicator (fun x ↦ ENNReal.ofReal (x / μU)) x ∂(P.map U) :=
      (lintegral_map (hd_meas.indicator hA) hU_meas).symm
    _ = ∫⁻ x in A, ENNReal.ofReal (x / μU) ∂(P.map U) := lintegral_indicator hA _
    _ = ((P.map U).withDensity (fun x ↦ ENNReal.ofReal (x / μU))) A :=
      (withDensity_apply _ hA).symm

/-- Kernel composition-product size-bias transfer when $\mathbb{E}[U] > 0$: if $(U, W)$ has law
$\mathcal{L}(U) \otimes \kappa$ and $(U^s, W^s)$ has law $\mathcal{L}(U^s) \otimes \kappa$ for a
Markov kernel $\kappa$, then integrability of $U\,\varphi(U, W)$ implies integrability of
$\varphi(U^s, W^s)$ and
$\mathbb{E}[U\,\varphi(U, W)] = \mathbb{E}[U]\,\mathbb{E}[\varphi(U^s, W^s)]$
(`SteinIntro.tex:1284-1318`). -/
private lemma sizeBias_compProd_integral
    {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {U Us : Ω → ℝ} {W Ws : Ω → γ} {κ : Kernel ℝ γ} [IsMarkovKernel κ]
    (hU_meas : Measurable U) (hW_meas : AEMeasurable W P) (hWs_meas : AEMeasurable Ws P)
    (hUs : IsSizeBias P U P Us)
    (hUW_law : P.map (fun ω ↦ (U ω, W ω)) = (P.map U) ⊗ₘ κ)
    (hUsWs_law : P.map (fun ω ↦ (Us ω, Ws ω)) = (P.map Us) ⊗ₘ κ)
    (hμU_pos : 0 < ∫ ω, U ω ∂P)
    {φ : ℝ × γ → ℝ} (hφ_meas : Measurable φ)
    (hUφ_int : Integrable (fun ω ↦ U ω * φ (U ω, W ω)) P) :
    Integrable (fun ω ↦ φ (Us ω, Ws ω)) P ∧
      ∫ ω, U ω * φ (U ω, W ω) ∂P =
        (∫ ω, U ω ∂P) * ∫ ω, φ (Us ω, Ws ω) ∂P := by
  have hdens := map_sizeBias_eq_withDensity P hU_meas hUs hμU_pos
  rcases hUs with ⟨_, _, hUs_meas, hUs_eq⟩
  set μU : ℝ := ∫ ω, U ω ∂P
  let ψ : ℝ × γ → ℝ := fun p ↦ p.1 * φ p
  have hψ_meas : Measurable ψ := measurable_fst.fun_mul hφ_meas
  have hUW_meas : AEMeasurable (fun ω ↦ (U ω, W ω)) P := hU_meas.aemeasurable.prodMk hW_meas
  have hUsWs_meas : AEMeasurable (fun ω ↦ (Us ω, Ws ω)) P := hUs_meas.prodMk hWs_meas
  have hψ_int_cp : Integrable ψ ((P.map U) ⊗ₘ κ) := by
    rw [← hUW_law]
    exact (integrable_map_measure hψ_meas.stronglyMeasurable.aestronglyMeasurable
      hUW_meas).mpr hUφ_int
  let nφ : ℝ × γ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal ‖φ p‖
  let nψ : ℝ × γ → ℝ≥0∞ := fun p ↦ ENNReal.ofReal ‖ψ p‖
  have hnφ_meas : Measurable nφ :=
    ENNReal.measurable_ofReal.comp (continuous_norm.measurable.comp hφ_meas)
  have hnψ_meas : Measurable nψ :=
    ENNReal.measurable_ofReal.comp (continuous_norm.measurable.comp hψ_meas)
  have hd_meas : Measurable (fun x : ℝ ↦ ENNReal.ofReal (x / μU)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.div_const μU)
  have hφ_int_cp : Integrable φ ((P.map Us) ⊗ₘ κ) := by
    refine ⟨hφ_meas.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hlt_ψ : ∫⁻ p, nψ p ∂((P.map U) ⊗ₘ κ) < ∞ :=
      (hasFiniteIntegral_iff_norm ψ).mp hψ_int_cp.hasFiniteIntegral
    have hle : ∫⁻ p, nφ p ∂((P.map Us) ⊗ₘ κ) ≤
        ENNReal.ofReal μU⁻¹ * ∫⁻ p, nψ p ∂((P.map U) ⊗ₘ κ) := calc
      ∫⁻ p, nφ p ∂((P.map Us) ⊗ₘ κ)
          = ∫⁻ x, ∫⁻ y, nφ (x, y) ∂(κ x) ∂(P.map Us) :=
            Measure.lintegral_compProd hnφ_meas
      _ = ∫⁻ x, ∫⁻ y, nφ (x, y) ∂(κ x) ∂((P.map U).withDensity
            (fun x ↦ ENNReal.ofReal (x / μU))) := by rw [hdens]
      _ = ∫⁻ x, ENNReal.ofReal (x / μU) * ∫⁻ y, nφ (x, y) ∂(κ x) ∂(P.map U) :=
            lintegral_withDensity_eq_lintegral_mul (P.map U) hd_meas
              hnφ_meas.lintegral_kernel_prod_right'
      _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (x / μU) * nφ (x, y) ∂(κ x) ∂(P.map U) := by
            refine lintegral_congr fun x ↦ ?_
            exact (lintegral_const_mul (ENNReal.ofReal (x / μU))
              (hnφ_meas.comp measurable_prodMk_left)).symm
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal μU⁻¹ * nψ (x, y) ∂(κ x) ∂(P.map U) := by
            refine lintegral_mono fun x ↦ lintegral_mono fun y ↦ ?_
            rcases le_or_gt 0 x with hx | hx
            · have hxdiv : x / μU = μU⁻¹ * x := by ring
              have hnorm : |ψ (x, y)| = x * |φ (x, y)| := by
                dsimp [ψ]
                rw [abs_mul, abs_of_nonneg hx]
              dsimp [nφ, nψ]
              rw [hxdiv, hnorm, ENNReal.ofReal_mul (inv_nonneg.mpr hμU_pos.le),
                ENNReal.ofReal_mul hx, mul_assoc]
            · dsimp [nφ]
              rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hx.le hμU_pos.le),
                zero_mul]
              exact bot_le
      _ = ∫⁻ p, ENNReal.ofReal μU⁻¹ * nψ p ∂((P.map U) ⊗ₘ κ) :=
            (Measure.lintegral_compProd (hnψ_meas.const_mul (ENNReal.ofReal μU⁻¹))).symm
      _ = ENNReal.ofReal μU⁻¹ * ∫⁻ p, nψ p ∂((P.map U) ⊗ₘ κ) :=
            lintegral_const_mul (ENNReal.ofReal μU⁻¹) hnψ_meas
    exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt_ψ)
  have hφ_int_P : Integrable (fun ω ↦ φ (Us ω, Ws ω)) P := by
    have hmap : Integrable φ (P.map (fun ω ↦ (Us ω, Ws ω))) := by rwa [hUsWs_law]
    exact (integrable_map_measure hφ_meas.stronglyMeasurable.aestronglyMeasurable
      hUsWs_meas).mp hmap
  refine ⟨hφ_int_P, ?_⟩
  let h : ℝ → ℝ := fun x ↦ ∫ y, φ (x, y) ∂(κ x)
  have hh_meas : Measurable h :=
    hφ_meas.stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hxh_eq : ∀ x : ℝ, x * h x = ∫ y, ψ (x, y) ∂(κ x) := fun x ↦
    (integral_const_mul x (fun y ↦ φ (x, y))).symm
  have hUh_int : Integrable (fun ω ↦ U ω * h (U ω)) P := by
    have hnorm_int : Integrable (fun x ↦ ∫ y, ‖ψ (x, y)‖ ∂(κ x)) (P.map U) :=
      ((Measure.integrable_compProd_iff
        hψ_meas.stronglyMeasurable.aestronglyMeasurable).mp hψ_int_cp).2
    have hxh_meas : Measurable (fun x : ℝ ↦ x * h x) := measurable_id.fun_mul hh_meas
    have hxh_int : Integrable (fun x : ℝ ↦ x * h x) (P.map U) := by
      refine hnorm_int.mono' hxh_meas.stronglyMeasurable.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun x ↦ ?_
      rw [hxh_eq x]
      exact norm_integral_le_integral_norm (fun y ↦ ψ (x, y))
    exact (integrable_map_measure hxh_meas.stronglyMeasurable.aestronglyMeasurable
      hU_meas.aemeasurable).mp hxh_int
  have hUs_h_eq : ∫ ω, φ (Us ω, Ws ω) ∂P = ∫ ω, h (Us ω) ∂P := calc
    ∫ ω, φ (Us ω, Ws ω) ∂P
        = ∫ p, φ p ∂(P.map (fun ω ↦ (Us ω, Ws ω))) :=
          (integral_map hUsWs_meas hφ_meas.stronglyMeasurable.aestronglyMeasurable).symm
    _ = ∫ p, φ p ∂((P.map Us) ⊗ₘ κ) := by rw [hUsWs_law]
    _ = ∫ x, h x ∂(P.map Us) := Measure.integral_compProd hφ_int_cp
    _ = ∫ ω, h (Us ω) ∂P :=
          integral_map hUs_meas hh_meas.stronglyMeasurable.aestronglyMeasurable
  calc
    ∫ ω, U ω * φ (U ω, W ω) ∂P
        = ∫ p, ψ p ∂(P.map (fun ω ↦ (U ω, W ω))) :=
          (integral_map hUW_meas hψ_meas.stronglyMeasurable.aestronglyMeasurable).symm
    _ = ∫ p, ψ p ∂((P.map U) ⊗ₘ κ) := by rw [hUW_law]
    _ = ∫ x, ∫ y, ψ (x, y) ∂(κ x) ∂(P.map U) := Measure.integral_compProd hψ_int_cp
    _ = ∫ x, x * h x ∂(P.map U) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x ↦ (hxh_eq x).symm)
    _ = ∫ ω, U ω * h (U ω) ∂P :=
          integral_map hU_meas.aemeasurable
            (measurable_id.fun_mul hh_meas).stronglyMeasurable.aestronglyMeasurable
    _ = μU * ∫ ω, h (Us ω) ∂P := hUs_eq h hh_meas hUh_int
    _ = μU * ∫ ω, φ (Us ω, Ws ω) ∂P := by rw [hUs_h_eq]

/-- Unified index-splitting master lemma for Proposition 3.14 and Corollaries 3.15–3.16:
splits $\mathbb{E}[f(g(I, V))]$ across the finite partition $\{I = i\}_{i \in \mathrm{Fin}\,n}$,
discarding zero-mean summands ($\mu_i = 0$) via $P(I = i) = 0$ and factoring positive-mean
summands ($\mu_i > 0$) via `IndepFun I V P` (`SteinIntro.tex:1301-1318`). -/
private lemma isSizeBias_sum_of_index_coupling
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {I : Ω → Fin n} {V : Ω → β} {g : Fin n → β → ℝ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_nn : ∀ i : Fin n, 0 ≤ᵐ[P] X i)
    (hX_int : ∀ i : Fin n, Integrable (X i) P)
    (hμ_pos : 0 < ∑ i : Fin n, ∫ ω, X i ω ∂P)
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P)
    (hV_meas : AEMeasurable V P)
    (hI_indep : ProbabilityTheory.IndepFun I V P)
    (hg_meas : ∀ i : Fin n, Measurable (g i))
    (h_fiber : ∀ (f : ℝ → ℝ), Measurable f → ∀ i : Fin n,
      0 < ∫ ω, X i ω ∂P →
      Integrable (fun ω ↦ X i ω * f (∑ k : Fin n, X k ω)) P →
      Integrable (fun ω ↦ f (g i (V ω))) P ∧
        ∫ ω, X i ω * f (∑ k : Fin n, X k ω) ∂P =
          (∫ ω, X i ω ∂P) * ∫ ω, f (g i (V ω)) ∂P) :
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P (fun ω ↦ g (I ω) (V ω)) := by
  let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
  let Xs_tot : Ω → ℝ := fun ω ↦ g (I ω) (V ω)
  have hS_meas : Measurable S := Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas i
  have hX_nn_all : ∀ᵐ ω ∂P, ∀ i : Fin n, 0 ≤ X i ω := eventually_countable_forall.mpr hX_nn
  have hS_nn : 0 ≤ᵐ[P] S :=
    hX_nn_all.mono fun ω hω ↦ Finset.sum_nonneg fun i _ ↦ hω i
  have hS_int : Integrable S P := integrable_finsetSum Finset.univ fun i _ ↦ hX_int i
  have hXs_tot_meas : AEMeasurable Xs_tot P := by
    have h_eq : Xs_tot =
        fun ω ↦ ∑ i : Fin n, (I ⁻¹' {i}).indicator (fun ω' ↦ g i (V ω')) ω := by
      funext ω
      symm
      rw [Finset.sum_eq_single (I ω)]
      · simp [Xs_tot]
      · intro i _ hi
        exact Set.indicator_of_notMem (by simpa using hi.symm) _
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    rw [h_eq]
    exact Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦
      ((hg_meas i).comp_aemeasurable hV_meas).indicator (hI_meas (measurableSet_singleton i))
  refine ⟨hS_nn, hS_int, hXs_tot_meas, ?_⟩
  intro f hf_meas hfS_int
  set μ : ℝ := ∑ i : Fin n, ∫ ω, X i ω ∂P
  have hS_mean : ∫ ω, S ω ∂P = μ := integral_finsetSum Finset.univ fun i _ ↦ hX_int i
  have hXi_fS_int : ∀ i : Fin n, Integrable (fun ω ↦ X i ω * f (S ω)) P := by
    intro i
    have hm : AEStronglyMeasurable (fun ω ↦ X i ω * f (S ω)) P :=
      ((hX_meas i).fun_mul (hf_meas.comp hS_meas)).stronglyMeasurable.aestronglyMeasurable
    refine hfS_int.mono hm ?_
    filter_upwards [hX_nn_all] with ω hω
    have hXi_le : X i ω ≤ S ω := Finset.single_le_sum (fun k _ ↦ hω k) (Finset.mem_univ i)
    have hSω_nn : 0 ≤ S ω := (hω i).trans hXi_le
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (hω i), Real.norm_of_nonneg hSω_nn]
    exact mul_le_mul_of_nonneg_right hXi_le (norm_nonneg _)
  let term : Fin n → Ω → ℝ := fun i ↦ (I ⁻¹' {i}).indicator (fun ω ↦ f (g i (V ω)))
  have hfXs_eq : (fun ω ↦ f (Xs_tot ω)) = fun ω ↦ ∑ i : Fin n, term i ω := by
    funext ω
    symm
    rw [Finset.sum_eq_single (I ω)]
    · simp [term, Xs_tot]
    · intro i _ hi
      exact Set.indicator_of_notMem (by simpa using hi.symm) _
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have hterm : ∀ i : Fin n,
      Integrable (term i) P ∧
        μ * ∫ ω, term i ω ∂P = ∫ ω, X i ω * f (S ω) ∂P := by
    intro i
    have hμi_nn : 0 ≤ ∫ ω, X i ω ∂P := integral_nonneg_of_ae (hX_nn i)
    rcases hμi_nn.eq_or_lt with hμi_zero | hμi_pos
    · have hμi0 : ∫ ω, X i ω ∂P = 0 := hμi_zero.symm
      have hXi_ae0 : X i =ᵐ[P] 0 :=
        (integral_eq_zero_iff_of_nonneg_ae (hX_nn i) (hX_int i)).mp hμi0
      have hLHS0 : ∫ ω, X i ω * f (S ω) ∂P = 0 :=
        integral_eq_zero_of_ae (hXi_ae0.mono fun ω hω ↦ by simp [hω])
      have hPI_real0 : P.real (I ⁻¹' {i}) = 0 := by rw [hI_prob i, hμi0, zero_div]
      have hPI0 : P (I ⁻¹' {i}) = 0 := (measureReal_eq_zero_iff).mp hPI_real0
      have hterm_ae0 : term i =ᵐ[P] 0 :=
        (measure_eq_zero_iff_ae_notMem.mp hPI0).mono fun ω hω ↦
          Set.indicator_of_notMem hω _
      refine ⟨(integrable_zero Ω ℝ P).congr hterm_ae0.symm, ?_⟩
      rw [integral_eq_zero_of_ae hterm_ae0, mul_zero, hLHS0]
    · obtain ⟨hfg_int, hfg_eq⟩ := h_fiber f hf_meas i hμi_pos (hXi_fS_int i)
      have hIi_meas : MeasurableSet (I ⁻¹' {i}) := hI_meas (measurableSet_singleton i)
      refine ⟨hfg_int.indicator hIi_meas, ?_⟩
      let fI : Fin n → ℝ := ({i} : Set (Fin n)).indicator (fun _ ↦ (1 : ℝ))
      let gV : β → ℝ := fun v ↦ f (g i v)
      have hfI_meas : Measurable fI := measurable_const.indicator (measurableSet_singleton i)
      have hgV_meas : Measurable gV := hf_meas.comp (hg_meas i)
      have hpt : term i = fun ω ↦ fI (I ω) * gV (V ω) := by
        funext ω
        by_cases hω : I ω = i <;> simp [term, fI, gV, hω]
      have hfI_comp : (fun ω ↦ fI (I ω)) = (I ⁻¹' {i}).indicator (fun _ ↦ (1 : ℝ)) := by
        funext ω
        by_cases hω : I ω = i <;> simp [fI, hω]
      have hint_term : ∫ ω, term i ω ∂P =
          ((∫ ω, X i ω ∂P) / μ) * ∫ ω, f (g i (V ω)) ∂P := by
        rw [hpt,
          hI_indep.integral_fun_comp_mul_comp hI_meas.aemeasurable hV_meas
            hfI_meas.stronglyMeasurable.aestronglyMeasurable
            hgV_meas.stronglyMeasurable.aestronglyMeasurable,
          hfI_comp, integral_indicator hIi_meas, setIntegral_one_eq_measureReal, hI_prob i]
      rw [hint_term, ← mul_assoc, mul_div_cancel₀ _ hμ_pos.ne', ← hfg_eq]
  have hSfS_eq : (fun ω ↦ S ω * f (S ω)) = fun ω ↦ ∑ i : Fin n, X i ω * f (S ω) := by
    funext ω
    exact Finset.sum_mul Finset.univ (fun i ↦ X i ω) (f (S ω))
  calc
    ∫ ω, S ω * f (S ω) ∂P
        = ∑ i : Fin n, ∫ ω, X i ω * f (S ω) ∂P := by
          rw [hSfS_eq]
          exact integral_finsetSum Finset.univ fun i _ ↦ hXi_fS_int i
    _ = ∑ i : Fin n, μ * ∫ ω, term i ω ∂P :=
          Finset.sum_congr rfl fun i _ ↦ (hterm i).2.symm
    _ = μ * ∑ i : Fin n, ∫ ω, term i ω ∂P := (Finset.mul_sum _ _ _).symm
    _ = (∫ ω, S ω ∂P) * ∫ ω, f (Xs_tot ω) ∂P := by
          rw [hS_mean, hfXs_eq, integral_finsetSum Finset.univ fun i _ ↦ (hterm i).1]

end Helpers

/-- Proposition 3.14 (`\label{prop71}`, `SteinIntro.tex:1284-1299`): size-bias coupling recipe for
a sum $X = \sum_{i=1}^n X_i$ of nonnegative integrable random variables with total mean
$\mu = \sum_i \mu_i > 0$. -/
theorem sizeBias_sum_of_condDistrib_recipe
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xs : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_nn : ∀ i : Fin n, 0 ≤ᵐ[P] X i)
    (hX_int : ∀ i : Fin n, Integrable (X i) P)
    (hμ_pos : 0 < ∑ i : Fin n, ∫ ω, X i ω ∂P)
    (hXs : ∀ i : Fin n, IsSizeBias P (X i) P (Xs i))
    (hY_meas : ∀ i : Fin n, AEMeasurable (Y i) P)
    (hXY_law : ∀ i : Fin n,
      P.map (fun ω ↦ (Xs i ω, Y i ω)) =
        (P.map (Xs i)) ⊗ₘ
          ProbabilityTheory.condDistrib (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) (X i) P)
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P)
    (hI_indep : ProbabilityTheory.IndepFun I
      (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω, fun i ↦ Y i ω)) P) :
    let Xs_total : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + Xs (I ω) ω
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P Xs_total := by
  intro Xs_total
  let V : Ω → (Fin n → ℝ) × (Fin n → ℝ) × ((i : Fin n) → ({j : Fin n // j ≠ i} → ℝ)) :=
    fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω, fun i ↦ Y i ω)
  let g : Fin n →
      (Fin n → ℝ) × (Fin n → ℝ) × ((i : Fin n) → ({j : Fin n // j ≠ i} → ℝ)) → ℝ :=
    fun i v ↦ (∑ j : {j : Fin n // j ≠ i}, v.2.2 i j) + v.2.1 i
  have hV_meas : AEMeasurable V P :=
    (Measurable.of_eval hX_meas).aemeasurable.prodMk
      ((AEMeasurable.of_eval fun i ↦ (hXs i).2.2.1).prodMk (AEMeasurable.of_eval hY_meas))
  have hg_meas : ∀ i : Fin n, Measurable (g i) := fun i ↦
    (Finset.measurable_fun_sum Finset.univ fun j _ ↦
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (measurable_snd.comp measurable_snd))).fun_add
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  refine isSizeBias_sum_of_index_coupling P hX_meas hX_nn hX_int hμ_pos hI_meas hI_prob
    hV_meas hI_indep hg_meas ?_
  intro f hf_meas i hμi_pos hXi_fS_int
  let rest : Ω → ({j : Fin n // j ≠ i} → ℝ) := fun ω j ↦ X j.1 ω
  have hrest_meas : Measurable rest := Measurable.of_eval fun j ↦ hX_meas j.1
  let φ : ℝ × ({j : Fin n // j ≠ i} → ℝ) → ℝ :=
    fun p ↦ f ((∑ j : {j : Fin n // j ≠ i}, p.2 j) + p.1)
  have hφ_meas : Measurable φ :=
    hf_meas.comp ((Finset.measurable_fun_sum Finset.univ fun j _ ↦
      (measurable_pi_apply j).comp measurable_snd).fun_add measurable_fst)
  have hUW_law : P.map (fun ω ↦ (X i ω, rest ω)) =
      (P.map (X i)) ⊗ₘ ProbabilityTheory.condDistrib rest (X i) P :=
    (ProbabilityTheory.compProd_map_condDistrib
      (hX_meas i).aemeasurable hrest_meas.aemeasurable).symm
  have hUφ_eq : (fun ω ↦ X i ω * φ (X i ω, rest ω)) =
      fun ω ↦ X i ω * f (∑ k : Fin n, X k ω) := by
    funext ω
    dsimp [φ, rest]
    rw [← sum_fin_eq_sum_ne_add i (fun k ↦ X k ω)]
  have hUφ_int : Integrable (fun ω ↦ X i ω * φ (X i ω, rest ω)) P := by
    rwa [hUφ_eq]
  have hres := sizeBias_compProd_integral P (hX_meas i) hrest_meas.aemeasurable (hY_meas i)
    (hXs i) hUW_law (hXY_law i) hμi_pos hφ_meas hUφ_int
  rwa [hUφ_eq] at hres

/-- Corollary 3.15 (`\label{cor71}`, `SteinIntro.tex:1319-1325`; `ISSUE-TYPO-3.15`): size-bias
coupling $X^s = X - X_I + X_I^s$ for a sum of independent nonnegative integrable random variables
$X_1, \dots, X_n$ with $\mu = \sum_i \mathbb{E}[X_i] > 0$. -/
theorem sizeBias_sum_of_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xs : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_nn : ∀ i : Fin n, 0 ≤ᵐ[P] X i)
    (hX_int : ∀ i : Fin n, Integrable (X i) P)
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (hXs : ∀ i : Fin n, IsSizeBias P (X i) P (Xs i))
    (hXs_indep : ∀ i : Fin n,
      ProbabilityTheory.IndepFun (Xs i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) P)
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω)) P)
    (hμ_pos : 0 < ∑ i : Fin n, ∫ ω, X i ω ∂P) :
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ i : Fin n, X i ω) - X (I ω) ω + Xs (I ω) ω) := by
  let V : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω)
  let g : Fin n → (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    fun i v ↦ (∑ k : Fin n, v.1 k) - v.1 i + v.2 i
  have hV_meas : AEMeasurable V P :=
    (Measurable.of_eval hX_meas).aemeasurable.prodMk
      (AEMeasurable.of_eval fun i ↦ (hXs i).2.2.1)
  have hg_meas : ∀ i : Fin n, Measurable (g i) := fun i ↦ by
    dsimp [g]
    fun_prop
  refine isSizeBias_sum_of_index_coupling P hX_meas hX_nn hX_int hμ_pos hI_meas hI_prob
    hV_meas hI_indep hg_meas ?_
  intro f hf_meas i hμi_pos hXi_fS_int
  let W : Ω → ℝ := fun ω ↦ ∑ j ∈ Finset.univ.erase i, X j ω
  have hW_meas : Measurable W := Finset.measurable_fun_sum _ fun j _ ↦ hX_meas j
  let κ : Kernel ℝ ℝ := Kernel.const ℝ (P.map W)
  have hXiW_indep : ProbabilityTheory.IndepFun (X i) W P := by
    have hsum := (hX_indep.indepFun_finsetSum_of_notMem hX_meas
      (Finset.notMem_erase i Finset.univ)).symm
    have hW_eq : (∑ j ∈ Finset.univ.erase i, X j) = W := by
      ext ω
      simp [W]
    rwa [hW_eq] at hsum
  have hXsiW_indep : ProbabilityTheory.IndepFun (Xs i) W P := by
    let sumSub : ({j : Fin n // j ≠ i} → ℝ) → ℝ := fun u ↦ ∑ j : {j : Fin n // j ≠ i}, u j
    have hsumSub_meas : Measurable sumSub :=
      Finset.measurable_fun_sum Finset.univ fun j _ ↦ measurable_pi_apply j
    have hcomp := (hXs_indep i).comp measurable_id hsumSub_meas
    have hcomp_eq : (sumSub ∘ fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) = W :=
      funext fun ω ↦ sum_subtype_ne_eq_erase i (fun k ↦ X k ω)
    simpa only [Function.id_comp, hcomp_eq] using hcomp
  have hUW_law : P.map (fun ω ↦ (X i ω, W ω)) = (P.map (X i)) ⊗ₘ κ := by
    rw [hXiW_indep.map_prod_eq_prod_map_map (hX_meas i).aemeasurable hW_meas.aemeasurable,
      Measure.compProd_const]
  have hUsWs_law : P.map (fun ω ↦ (Xs i ω, W ω)) = (P.map (Xs i)) ⊗ₘ κ := by
    rw [hXsiW_indep.map_prod_eq_prod_map_map (hXs i).2.2.1 hW_meas.aemeasurable,
      Measure.compProd_const]
  let φ : ℝ × ℝ → ℝ := fun p ↦ f (p.2 + p.1)
  have hφ_meas : Measurable φ := hf_meas.comp (measurable_snd.fun_add measurable_fst)
  have hUφ_eq : (fun ω ↦ X i ω * φ (X i ω, W ω)) =
      fun ω ↦ X i ω * f (∑ k : Fin n, X k ω) := by
    funext ω
    dsimp [φ, W]
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hUsφ_eq : (fun ω ↦ φ (Xs i ω, W ω)) = fun ω ↦ f (g i (V ω)) := by
    funext ω
    dsimp [φ, W, g, V]
    have hsum : (∑ k : Fin n, X k ω) = (∑ j ∈ Finset.univ.erase i, X j ω) + X i ω :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
    congr 1
    linarith
  have hUφ_int : Integrable (fun ω ↦ X i ω * φ (X i ω, W ω)) P := by rwa [hUφ_eq]
  have hres := sizeBias_compProd_integral P (hX_meas i) hW_meas.aemeasurable hW_meas.aemeasurable
    (hXs i) hUW_law hUsWs_law hμi_pos hφ_meas hUφ_int
  rwa [hUφ_eq, hUsφ_eq] at hres

/-- Corollary 3.16 (`\label{cor72}`, `SteinIntro.tex:1326-1332`): size-bias coupling
$X^s = \sum_{j \ne I} X_j^{(I)} + 1$ for a sum of zero-one random variables $X_1, \dots, X_n$ with
$p_i = \mathbb{P}(X_i = 1)$ and $\mu = \sum_i p_i > 0$. -/
theorem sizeBias_sum_of_zero_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : Fin n → ℝ := fun i ↦ P.real (X i ⁻¹' {1})
    let μ : ℝ := ∑ i : Fin n, p i
    0 < μ →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P (X i ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / μ) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1) := by
  intro p μ hμ_pos hY_meas hY_law hI_meas hI_prob hI_indep
  have hX_nn : ∀ i : Fin n, 0 ≤ᵐ[P] X i := fun i ↦
    (hX_zo i).mono fun ω hω ↦ by rcases hω with hω | hω <;> simp [hω]
  have hX_ae_ind : ∀ i : Fin n, X i =ᵐ[P] (X i ⁻¹' {1}).indicator (fun _ ↦ (1 : ℝ)) := by
    intro i
    refine (hX_zo i).mono fun ω hω ↦ ?_
    rcases hω with h0 | h1
    · have hnot : ω ∉ X i ⁻¹' {1} := by simp [h0]
      rw [h0, Set.indicator_of_notMem hnot]
    · have hmem : ω ∈ X i ⁻¹' {1} := by simp [h1]
      rw [h1, Set.indicator_of_mem hmem]
  have hX_int : ∀ i : Fin n, Integrable (X i) P := fun i ↦
    ((integrable_const (1 : ℝ)).indicator
      (hX_meas i (measurableSet_singleton 1))).congr (hX_ae_ind i).symm
  have hX_mean : ∀ i : Fin n, ∫ ω, X i ω ∂P = p i := by
    intro i
    rw [integral_congr_ae (hX_ae_ind i),
      integral_indicator (hX_meas i (measurableSet_singleton 1)), setIntegral_one_eq_measureReal]
  have hμ_eq : (∑ j : Fin n, ∫ ω, X j ω ∂P) = μ :=
    Finset.sum_congr rfl fun j _ ↦ hX_mean j
  have hμ_pos' : 0 < ∑ i : Fin n, ∫ ω, X i ω ∂P := by rwa [hμ_eq]
  have hI_prob' : ∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P := by
    intro i
    rw [hX_mean i, hμ_eq, hI_prob i]
  let V : Ω → (Fin n → ℝ) × ((i : Fin n) → ({j : Fin n // j ≠ i} → ℝ)) :=
    fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)
  let g : Fin n → (Fin n → ℝ) × ((i : Fin n) → ({j : Fin n // j ≠ i} → ℝ)) → ℝ :=
    fun i v ↦ (∑ j : {j : Fin n // j ≠ i}, v.2 i j) + 1
  have hV_meas : AEMeasurable V P :=
    (Measurable.of_eval hX_meas).aemeasurable.prodMk (AEMeasurable.of_eval hY_meas)
  have hg_meas : ∀ i : Fin n, Measurable (g i) := fun i ↦
    (Finset.measurable_fun_sum Finset.univ fun j _ ↦
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)).fun_add
      measurable_const
  refine isSizeBias_sum_of_index_coupling P hX_meas hX_nn hX_int hμ_pos' hI_meas hI_prob'
    hV_meas hI_indep hg_meas ?_
  intro f hf_meas i hμi_pos hXi_fS_int
  have hp_pos : 0 < p i := by rwa [← hX_mean i]
  let A : Set Ω := X i ⁻¹' {1}
  have hA_meas : MeasurableSet A := hX_meas i (measurableSet_singleton 1)
  have hPA_ne_zero : P A ≠ 0 := (measureReal_ne_zero_iff).mp hp_pos.ne'
  let rest : Ω → ({j : Fin n // j ≠ i} → ℝ) := fun ω j ↦ X j.1 ω
  have hrest_meas : Measurable rest := Measurable.of_eval fun j ↦ hX_meas j.1
  let ψ : ({j : Fin n // j ≠ i} → ℝ) → ℝ := fun u ↦ f ((∑ j : {j : Fin n // j ≠ i}, u j) + 1)
  have hψ_meas : Measurable ψ :=
    hf_meas.comp ((Finset.measurable_fun_sum Finset.univ fun j _ ↦
      measurable_pi_apply j).fun_add measurable_const)
  have h_ae_ind : (fun ω ↦ X i ω * f (∑ k : Fin n, X k ω)) =ᵐ[P] A.indicator (ψ ∘ rest) := by
    refine (hX_zo i).mono fun ω hω ↦ ?_
    rcases hω with h0 | h1
    · have hnot : ω ∉ A := by simp [A, h0]
      simp [h0, Set.indicator_of_notMem hnot]
    · have hmem : ω ∈ A := by simp [A, h1]
      rw [Set.indicator_of_mem hmem]
      dsimp [ψ, rest]
      rw [h1, one_mul, sum_fin_eq_sum_ne_add i (fun k ↦ X k ω), h1]
  have h_intOn : IntegrableOn (ψ ∘ rest) A P :=
    (integrable_indicator_iff hA_meas).mp (hXi_fS_int.congr h_ae_ind)
  have h_int_cond : Integrable (ψ ∘ rest) (ProbabilityTheory.cond P A) := by
    rw [ProbabilityTheory.cond]
    exact h_intOn.smul_measure (ENNReal.inv_ne_top.mpr hPA_ne_zero)
  have h_int_map : Integrable ψ (P.map (Y i)) := by
    rw [hY_law i hp_pos]
    exact (integrable_map_measure hψ_meas.stronglyMeasurable.aestronglyMeasurable
      hrest_meas.aemeasurable).mpr h_int_cond
  have hY_int : Integrable (fun ω ↦ f (g i (V ω))) P :=
    (integrable_map_measure hψ_meas.stronglyMeasurable.aestronglyMeasurable
      (hY_meas i)).mp h_int_map
  refine ⟨hY_int, ?_⟩
  have hY_integral : ∫ ω, f (g i (V ω)) ∂P =
      (p i)⁻¹ * ∫ ω, X i ω * f (∑ k : Fin n, X k ω) ∂P := calc
    ∫ ω, f (g i (V ω)) ∂P
        = ∫ u, ψ u ∂(P.map (Y i)) :=
          (integral_map (hY_meas i) hψ_meas.stronglyMeasurable.aestronglyMeasurable).symm
    _ = ∫ u, ψ u ∂((ProbabilityTheory.cond P A).map rest) := by rw [hY_law i hp_pos]
    _ = ∫ ω, ψ (rest ω) ∂(ProbabilityTheory.cond P A) :=
          integral_map hrest_meas.aemeasurable hψ_meas.stronglyMeasurable.aestronglyMeasurable
    _ = ((P A)⁻¹).toReal * ∫ ω in A, ψ (rest ω) ∂P := by
          rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
    _ = (p i)⁻¹ * ∫ ω, A.indicator (ψ ∘ rest) ω ∂P := by
          rw [ENNReal.toReal_inv, ← measureReal_def, integral_indicator hA_meas]
          rfl
    _ = (p i)⁻¹ * ∫ ω, X i ω * f (∑ k : Fin n, X k ω) ∂P := by
          rw [integral_congr_ae h_ae_ind.symm]
  rw [hX_mean i, hY_integral, mul_inv_cancel_left₀ hp_pos.ne']

end SteinMethod
