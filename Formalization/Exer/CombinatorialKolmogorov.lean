/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exer.PermSwapCoupling
import Formalization.Kolmogorov.ZeroBiasBound
import Formalization.ZeroBias.Basic
import Formalization.ZeroBias.Density

/-!
# Combinatorial CLT Kolmogorov Bound (`Formalization.Exer.CombinatorialKolmogorov`)

Proves the Kolmogorov distance bound for the combinatorial central limit theorem (`EXER-3`,
`Sec3_6_1_combinatorial_kolmogorov`, `SteinIntro.tex:1741-1743`, `%%XXXX Exercise 3`):
for an $n \times n$ real array $(a_{ij})_{i,j=1}^n$ with $|a_{ij}| \le C$, a uniform random
permutation $\pi \sim \mathrm{Unif}(S_n)$, $S = \sum_{i=1}^n a_{i, \pi(i)}$ with $\sigma^2 =
\operatorname{Var}(S) > 0$, and $W = (S - \mu)/\sigma$,
$$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{N}(0, 1)) \le
  \left(1 + \frac{1}{\sqrt{2\pi}} + \frac{\sqrt{2\pi}}{4}\right) \frac{8 C}{\sigma}.$$

The proof combines:
1. the two-swap coupling on $S_n \times \mathrm{TwoSwapQuad}\,n \times (0, 1)$ from
   `Formalization.Exer.PermSwapCoupling`, which constructs a zero-bias coupling $(W, W^z)$ with
   $|W^z - W| \le 8 C / \sigma$ almost surely for all $n \ge 2$ (including $n = 2$), and
2. Theorem 3.27 (`kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd`) from
   `Formalization.Kolmogorov.ZeroBiasBound`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace SteinMethod

/-! ### Section 1: Calculus & Exchangeable Regression Helpers for the Coupled Space -/

private lemma sq_sub_setIntegral_Ioo_deriv_eq_aux
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (w w' : ℝ) :
    (w' - w) ^ 2 * (∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * w + (1 - u) * w')) =
      (w' - w) * (F w' - F w) := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  let g : ℝ → ℝ := fun u ↦ F (w' + u * (w - w'))
  have hg_cd : ContDiff ℝ 1 g :=
    hF.comp (contDiff_const.add (contDiff_id.mul contDiff_const))
  have hg_deriv : ∀ u : ℝ, HasDerivAt g ((w - w') * deriv F (u * w + (1 - u) * w')) u := by
    intro u
    have hd_aff : HasDerivAt (fun s : ℝ ↦ w' + s * (w - w')) (w - w') u := by
      have hd1 : HasDerivAt (fun s : ℝ ↦ s * (w - w')) (1 * (w - w')) u :=
        (hasDerivAt_id' u).mul_const (w - w')
      rw [one_mul] at hd1
      have hd_add := (hasDerivAt_const u w').add hd1
      rw [zero_add] at hd_add
      exact hd_add
    have hd_F : HasDerivAt F (deriv F (w' + u * (w - w'))) (w' + u * (w - w')) :=
      (hF.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hcomp := hd_F.comp u hd_aff
    have hrew : w' + u * (w - w') = u * w + (1 - u) * w' := by ring
    rw [hrew, mul_comm] at hcomp
    exact hcomp
  have hg_deriv_eq : (fun u ↦ deriv g u) =
      fun u ↦ (w - w') * deriv F (u * w + (1 - u) * w') :=
    funext fun u ↦ (hg_deriv u).deriv
  have hg_ac : AbsolutelyContinuousOnInterval g 0 1 :=
    hg_cd.contDiffOn.absolutelyContinuousOnInterval
  have hFTC := hg_ac.integral_deriv_eq_sub
  have hg1 : g 1 = F w := by
    dsimp [g]
    exact congrArg F (by ring)
  have hg0 : g 0 = F w' := by
    dsimp [g]
    exact congrArg F (by ring)
  rw [hg1, hg0, hg_deriv_eq, intervalIntegral.integral_const_mul] at hFTC
  linear_combination (w - w') * hFTC

private lemma integral_sub_mul_sub_eq_two_mul_a_integral_mul_aux
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W')
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    {F : ℝ → ℝ} (hF_meas : Measurable F) (hF_sub : ∀ w : ℝ, |F w| ≤ |w|) :
    ∫ ω, (W' ω - W ω) * (F (W' ω) - F (W ω)) ∂P = 2 * a * ∫ ω, W ω * F (W ω) ∂P := by
  have hmW_le : MeasurableSpace.comap W inferInstance ≤ mΩ := hW_meas.comap_le
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'2 : MemLp W' 2 P := hId.memLp_snd hW2
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  have hW_sq_int : Integrable (fun ω ↦ W ω ^ 2) P := hW2.integrable_sq
  have hWW'_int : Integrable (W * W') P := hW2.integrable_mul hW'2
  have hFW_aestrong : AEStronglyMeasurable (fun ω ↦ F (W ω)) P :=
    (hF_meas.comp hW_meas).aestronglyMeasurable
  have hWF_int : Integrable (fun ω ↦ W ω * F (W ω)) P := by
    refine hW_sq_int.mono' (hW_meas.aestronglyMeasurable.mul hFW_aestrong)
      (ae_of_all P fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, ← sq_abs, sq]
    exact mul_le_mul_of_nonneg_left (hF_sub (W ω)) (abs_nonneg (W ω))
  have hW'F_int : Integrable (fun ω ↦ W' ω * F (W ω)) P := by
    refine hWW'_int.norm.mono'
      (hId.aemeasurable_snd.aestronglyMeasurable.mul hFW_aestrong)
      (ae_of_all P fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, Pi.mul_apply, abs_mul, mul_comm |W ω|]
    exact mul_le_mul_of_nonneg_left (hF_sub (W ω)) (abs_nonneg (W' ω))
  have hFW_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
      (fun ω ↦ F (W ω)) :=
    (hF_meas.comp (comap_measurable (m := inferInstance) W)).stronglyMeasurable
  have hF_mul_W'_int : Integrable ((fun ω ↦ F (W ω)) * W') P := by
    have heq : (fun ω ↦ F (W ω)) * W' = (fun ω ↦ W' ω * F (W ω)) := by
      ext ω; simp [mul_comm]
    rw [heq]
    exact hW'F_int
  have hCondMul :
      P[(fun ω ↦ F (W ω)) * W' | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        fun ω ↦ (1 - a) * (W ω * F (W ω)) := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hFW_sm hF_mul_W'_int hW'_int, hCond]
      with ω hω1 hω2
    rw [hω1, Pi.mul_apply, hω2]
    ring
  have hW'F_eq : ∫ ω, W' ω * F (W ω) ∂P = (1 - a) * ∫ ω, W ω * F (W ω) ∂P := calc
    ∫ ω, W' ω * F (W ω) ∂P = ∫ ω, ((fun ω ↦ F (W ω)) * W') ω ∂P := by
      congr 1; ext ω; simp only [Pi.mul_apply]; ring
    _ = ∫ ω, P[(fun ω ↦ F (W ω)) * W' | MeasurableSpace.comap W inferInstance] ω ∂P :=
      (integral_condExp (μ := P) (f := (fun ω ↦ F (W ω)) * W') hmW_le).symm
    _ = ∫ ω, (1 - a) * (W ω * F (W ω)) ∂P := integral_congr_ae hCondMul
    _ = (1 - a) * ∫ ω, W ω * F (W ω) ∂P := integral_const_mul (1 - a) _
  have hDiff_int : Integrable (fun ω ↦ (W ω - W' ω) * F (W ω)) P := by
    have heq : (fun ω ↦ (W ω - W' ω) * F (W ω)) =
        fun ω ↦ W ω * F (W ω) - W' ω * F (W ω) := by
      ext ω; ring
    rw [heq]
    exact hWF_int.sub hW'F_int
  have hDiff_eq : ∫ ω, (W ω - W' ω) * F (W ω) ∂P = a * ∫ ω, W ω * F (W ω) ∂P := by
    have heq : (fun ω ↦ (W ω - W' ω) * F (W ω)) =
        fun ω ↦ W ω * F (W ω) - W' ω * F (W ω) := by
      ext ω; ring
    rw [heq, integral_sub hWF_int hW'F_int, hW'F_eq]
    ring
  have hG_meas : Measurable (fun p : ℝ × ℝ ↦ (p.2 - p.1) * F p.2) :=
    (measurable_snd.sub measurable_fst).mul (hF_meas.comp measurable_snd)
  have hExch_comp := hExch.comp hG_meas
  have hSymm_int : ∫ ω, (W' ω - W ω) * F (W' ω) ∂P = ∫ ω, (W ω - W' ω) * F (W ω) ∂P :=
    hExch_comp.integral_eq
  have hSymm_integrable : Integrable (fun ω ↦ (W' ω - W ω) * F (W' ω)) P :=
    hExch_comp.symm.integrable_snd hDiff_int
  have hSum_eq : (fun ω ↦ (W' ω - W ω) * (F (W' ω) - F (W ω))) =
      fun ω ↦ (W' ω - W ω) * F (W' ω) + (W ω - W' ω) * F (W ω) := by
    ext ω; ring
  rw [hSum_eq, integral_add hSymm_integrable hDiff_int, hSymm_int, hDiff_eq]
  ring

/-! ### Section 2: Zero-Bias Property of the Two-Swap Coupling -/

/-- Unnormalized two-swap coupled random variable $W_u(\pi, q, u) = \mathrm{combStat}\,a\,\pi$. -/
noncomputable def twoSwapBaseRV {n : ℕ} (a : Fin n → Fin n → ℝ)
    (x : (Equiv.Perm (Fin n) × TwoSwapQuad n) × ℝ) : ℝ :=
  combStat a x.1.1

/-- Unnormalized two-swap zero-bias random variable
$W_u^z(\pi, q, u) = u\,\mathrm{combStat}\,a\,\pi^\dagger +
(1 - u)\,\mathrm{combStat}\,a\,\pi'^\dagger$. -/
noncomputable def twoSwapZeroBiasRV {n : ℕ} (a : Fin n → Fin n → ℝ)
    (x : (Equiv.Perm (Fin n) × TwoSwapQuad n) × ℝ) : ℝ :=
  x.2 * combStat a (twoSwapCoupledPair x.1).1 +
    (1 - x.2) * combStat a (twoSwapCoupledPair x.1).2

/-- On the coupled product space $(\mu_\sigma \otimes \mu_q) \otimes \mathrm{Unif}(0, 1)$,
`twoSwapZeroBiasRV a` has the zero-bias distribution of `twoSwapBaseRV a`. -/
lemma isZeroBias_twoSwapCoupling {n : ℕ} (hn : 2 ≤ n) (a : Fin n → Fin n → ℝ)
    (hVar : 0 < ProbabilityTheory.variance (combStat a)
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure) :
    let hQ_pos : 0 < ∑ q : TwoSwapQuad n, twoSwapWeight a q :=
      (sum_sq_combStat_swap_and_twoSwapWeight_pos hn a hVar).2
    let μσ : Measure (Equiv.Perm (Fin n)) :=
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
    let μq : Measure (TwoSwapQuad n) := (twoSwapQuadPMF a hQ_pos).toMeasure
    let μu : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
    let Pc : Measure ((Equiv.Perm (Fin n) × TwoSwapQuad n) × ℝ) := (μσ.prod μq).prod μu
    IsProbabilityMeasure Pc ∧
      IsZeroBias Pc (twoSwapBaseRV a) Pc (twoSwapZeroBiasRV a) := by
  intro hQ_pos μσ μq μu Pc
  have : DiscreteMeasurableSpace (TwoSwapQuad n) := inferInstance
  have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μq := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μu := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
  have hPc_prob : IsProbabilityMeasure Pc := inferInstance
  refine ⟨hPc_prob, ?_⟩
  have hWu_meas : Measurable (twoSwapBaseRV a) :=
    (Measurable.of_discrete (f := combStat a)).comp (measurable_fst.comp measurable_fst)
  have hWzu_meas : Measurable (twoSwapZeroBiasRV a) := by
    have hm1 : Measurable (fun y : Equiv.Perm (Fin n) × TwoSwapQuad n ↦
        combStat a (twoSwapCoupledPair y).1) := .of_discrete
    have hm2 : Measurable (fun y : Equiv.Perm (Fin n) × TwoSwapQuad n ↦
        combStat a (twoSwapCoupledPair y).2) := .of_discrete
    exact (measurable_snd.mul (hm1.comp measurable_fst)).add
      ((measurable_const.sub measurable_snd).mul (hm2.comp measurable_fst))
  have hmap_fst : Pc.map (Prod.fst ∘ Prod.fst) = μσ := by
    rw [← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.map_fst_prod, measure_univ, one_smul]
  have hId_Wu : IdentDistrib (twoSwapBaseRV a) (combStat a) Pc μσ :=
    ⟨hWu_meas.aemeasurable, (Measurable.of_discrete (f := combStat a)).aemeasurable,
      by
        change Pc.map (combStat a ∘ (Prod.fst ∘ Prod.fst)) = μσ.map (combStat a)
        rw [← Measure.map_map .of_discrete (measurable_fst.comp measurable_fst), hmap_fst]⟩
  have hWu_L2 : MemLp (twoSwapBaseRV a) 2 Pc := by
    let B : ℝ := ∑ ρ : Equiv.Perm (Fin n), |combStat a ρ|
    refine MemLp.of_bound hWu_meas.aestronglyMeasurable B (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun ρ _ ↦ abs_nonneg (combStat a ρ)) (Finset.mem_univ x.1.1)
  have hWu_mean : ∫ x, twoSwapBaseRV a x ∂Pc = 0 := by
    rw [hId_Wu.integral_eq, PMF.integral_eq_sum]
    have hn1 : 1 ≤ n := by omega
    simp_rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, ← Finset.mul_sum, sum_combStat_eq_zero hn1 a, mul_zero]
  have hWu_var_eq : ProbabilityTheory.variance (twoSwapBaseRV a) Pc =
      ProbabilityTheory.variance (combStat a) μσ := hId_Wu.variance_eq
  have hWu_var_pos : 0 < ProbabilityTheory.variance (twoSwapBaseRV a) Pc := by
    rwa [hWu_var_eq]
  refine (isZeroBias_and_map_eq_of_c1_sublinear Pc Pc hWu_L2 hWu_mean hWu_var_pos
    hWzu_meas.aemeasurable ?_).2
  intro F hF_cd hF_sub ⟨B, hB⟩
  have hF_meas : Measurable F := hF_cd.continuous.measurable
  have hF'_int : Integrable (fun x ↦ deriv F (twoSwapZeroBiasRV a x)) Pc :=
    Integrable.of_bound ((measurable_deriv F).comp hWzu_meas).aestronglyMeasurable B
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hB (twoSwapZeroBiasRV a x))
  let G : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) → ℝ :=
    fun p ↦ ∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * combStat a p.1 + (1 - u) * combStat a p.2)
  have hInt_Pc : ∫ x, deriv F (twoSwapZeroBiasRV a x) ∂Pc =
      ∫ y, G (twoSwapCoupledPair y) ∂(μσ.prod μq) := by
    rw [integral_prod _ hF'_int]
    rfl
  rw [hInt_Pc, integral_twoSwapCoupledPair_eq hn a hQ_pos G]
  have hNum_term : ∀ (ρ : Equiv.Perm (Fin n)) (τ : SwapType n),
      (combStat a (ρ * τ.1) - combStat a ρ) ^ 2 * G (ρ, ρ * τ.1) =
        (combStat a (ρ * τ.1) - combStat a ρ) *
          (F (combStat a (ρ * τ.1)) - F (combStat a ρ)) :=
    fun ρ τ ↦ sq_sub_setIntegral_Ioo_deriv_eq_aux hF_cd (combStat a ρ) (combStat a (ρ * τ.1))
  simp_rw [hNum_term]
  let hne : Nonempty (SwapType n) :=
    ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩
  let μτ : Measure (SwapType n) :=
    (@PMF.uniformOfFintype (SwapType n) inferInstance hne).toMeasure
  have : DiscreteMeasurableSpace (SwapType n) := inferInstance
  have : IsProbabilityMeasure μτ := PMF.toMeasure.isProbabilityMeasure _
  have h1 : (μσ.prod μτ).map Prod.fst = μσ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have h2 : (μσ.prod μτ).map Prod.snd = μτ := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hindep : ProbabilityTheory.IndepFun
      (Prod.fst : Equiv.Perm (Fin n) × SwapType n → Equiv.Perm (Fin n))
      (Prod.snd : Equiv.Perm (Fin n) × SwapType n → SwapType n) (μσ.prod μτ) :=
    ProbabilityTheory.indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  obtain ⟨hExch, hW0_meas, hW0_2, _, hCond_W0⟩ :=
    combinatorial_exchangeable_and_linear (μσ.prod μτ) hn a
      measurable_fst measurable_snd hindep h1 h2
  have hNum_int := integral_sub_mul_sub_eq_two_mul_a_integral_mul_aux (μσ.prod μτ)
    hExch hW0_meas hW0_2 hCond_W0 hF_meas hF_sub
  rw [integral_prod_uniform_perm_swapType hn] at hNum_int
  have hDen_int := (sum_sq_combStat_swap_and_twoSwapWeight_pos hn a hVar).1
  rw [integral_prod_uniform_perm_swapType hn] at hDen_int
  have hId_W0_Wu : IdentDistrib (fun p : Equiv.Perm (Fin n) × SwapType n ↦ combStat a p.1)
      (twoSwapBaseRV a) (μσ.prod μτ) Pc := by
    refine ⟨hW0_meas.aemeasurable, hWu_meas.aemeasurable, ?_⟩
    change (μσ.prod μτ).map (combStat a ∘ Prod.fst) = Pc.map (twoSwapBaseRV a)
    rw [← Measure.map_map .of_discrete measurable_fst, h1, ← hId_Wu.map_eq]
  have hWF_eq : ∫ p, combStat a p.1 * F (combStat a p.1) ∂(μσ.prod μτ) =
      ∫ x, twoSwapBaseRV a x * F (twoSwapBaseRV a x) ∂Pc :=
    (hId_W0_Wu.comp (measurable_id.mul hF_meas)).integral_eq
  rw [hWF_eq] at hNum_int
  rw [← hWu_var_eq] at hDen_int
  have hc1 : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc2 : (Fintype.card (SwapType n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ha_ne : 2 / ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact div_ne_zero two_ne_zero (by linarith)
  have hDen_sum_ne : (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
      (combStat a (ρ * τ.1) - combStat a ρ) ^ 2) ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at hDen_int
    exact (mul_ne_zero (mul_ne_zero two_ne_zero ha_ne) hWu_var_pos.ne') hDen_int.symm
  have hrel :
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
        ((Fintype.card (SwapType n) : ℝ)⁻¹ *
          (ProbabilityTheory.variance (twoSwapBaseRV a) Pc *
            (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
              (combStat a (ρ * τ.1) - combStat a ρ) *
                (F (combStat a (ρ * τ.1)) - F (combStat a ρ))) -
            (∫ x, twoSwapBaseRV a x * F (twoSwapBaseRV a x) ∂Pc) *
              (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
                (combStat a (ρ * τ.1) - combStat a ρ) ^ 2))) = 0 := by
    linear_combination
      ProbabilityTheory.variance (twoSwapBaseRV a) Pc * hNum_int -
        (∫ x, twoSwapBaseRV a x * F (twoSwapBaseRV a x) ∂Pc) * hDen_int
  have hsub0 :
      ProbabilityTheory.variance (twoSwapBaseRV a) Pc *
        (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
          (combStat a (ρ * τ.1) - combStat a ρ) *
            (F (combStat a (ρ * τ.1)) - F (combStat a ρ))) -
        (∫ x, twoSwapBaseRV a x * F (twoSwapBaseRV a x) ∂Pc) *
          (∑ ρ : Equiv.Perm (Fin n), ∑ τ : SwapType n,
            (combStat a (ρ * τ.1) - combStat a ρ) ^ 2) = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_left (inv_ne_zero hc1))).resolve_left
      (inv_ne_zero hc2)
  symm
  rw [mul_div_assoc', div_eq_iff hDen_sum_ne]
  exact sub_eq_zero.mp hsub0

/-! ### Section 3: Main Theorem (`Sec3_6_1_combinatorial_kolmogorov`) -/

/-- **Combinatorial CLT Kolmogorov bound** (`Sec3_6_1_combinatorial_kolmogorov`,
`SteinIntro.tex:1741-1743`, `%%XXXX Exercise 3`). -/
theorem sec3_6_1_combinatorial_kolmogorov
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {a : Fin n → Fin n → ℝ} {π : Ω → Equiv.Perm (Fin n)} {Z : Ω' → ℝ} {C : ℝ}
    (hC : ∀ i j : Fin n, |a i j| ≤ C)
    (hπ : AEMeasurable π P)
    (hπ_unif : P.map π = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
    (hvar_S : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, a i (π ω i)) P)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, a i (π ω i)
    let μ : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ (S ω - μ) / σ
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (8 * C / σ)) := by
  intro S μ σ W
  have hn2 : 2 ≤ n := two_le_of_pos_variance_perm P hvar_S
  have hn1 : 1 ≤ n := by omega
  let μσ : Measure (Equiv.Perm (Fin n)) :=
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  have hvar_eq : ProbabilityTheory.variance S P = ProbabilityTheory.variance (combStat a) μσ :=
    variance_combStat_eq_variance_sum P hn1 a hπ hπ_unif
  have hvar_comb : 0 < ProbabilityTheory.variance (combStat a) μσ := by
    rwa [← hvar_eq]
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hvar_S
  let hQ_pos : 0 < ∑ q : TwoSwapQuad n, twoSwapWeight a q :=
    (sum_sq_combStat_swap_and_twoSwapWeight_pos hn2 a hvar_comb).2
  let μq : Measure (TwoSwapQuad n) := (twoSwapQuadPMF a hQ_pos).toMeasure
  let μu : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let Pc : Measure ((Equiv.Perm (Fin n) × TwoSwapQuad n) × ℝ) := (μσ.prod μq).prod μu
  obtain ⟨hPc_prob, hZB_u⟩ := isZeroBias_twoSwapCoupling hn2 a hvar_comb
  let Wc : (Equiv.Perm (Fin n) × TwoSwapQuad n) × ℝ → ℝ := fun x ↦ σ⁻¹ * twoSwapBaseRV a x
  let Wzc : (Equiv.Perm (Fin n) × TwoSwapQuad n) × ℝ → ℝ := fun x ↦ σ⁻¹ * twoSwapZeroBiasRV a x
  have hZB_c : IsZeroBias Pc Wc Pc Wzc := hZB_u.const_mul σ⁻¹
  have : DiscreteMeasurableSpace (TwoSwapQuad n) := inferInstance
  have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μq := PMF.toMeasure.isProbabilityMeasure _
  have : IsProbabilityMeasure μu := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
  have hmap_fst : Pc.map (Prod.fst ∘ Prod.fst) = μσ := by
    rw [← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.map_fst_prod, measure_univ, one_smul]
  have hId_Wu : IdentDistrib (twoSwapBaseRV a) (combStat a) Pc μσ :=
    ⟨((Measurable.of_discrete (f := combStat a)).comp
        (measurable_fst.comp measurable_fst)).aemeasurable,
      (Measurable.of_discrete (f := combStat a)).aemeasurable,
      by
        change Pc.map (combStat a ∘ (Prod.fst ∘ Prod.fst)) = μσ.map (combStat a)
        rw [← Measure.map_map .of_discrete (measurable_fst.comp measurable_fst), hmap_fst]⟩
  have hvar_Wc : ProbabilityTheory.variance Wc Pc = 1 := by
    dsimp [Wc]
    rw [ProbabilityTheory.variance_const_mul, hId_Wu.variance_eq, ← hvar_eq, inv_pow,
      Real.sq_sqrt hvar_S.le, inv_mul_cancel₀ hvar_S.ne']
  have hδ : ∀ᵐ x ∂Pc, |Wzc x - Wc x| ≤ 8 * C / σ := by
    have hmap_snd : Pc.map Prod.snd = μu := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    have hmem_map : ∀ᵐ u ∂(Pc.map Prod.snd), u ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [hmap_snd]
      exact ae_restrict_mem measurableSet_Ioo
    have hu_ae : ∀ᵐ x ∂Pc, x.2 ∈ Set.Ioo (0 : ℝ) 1 :=
      (ae_map_iff measurable_snd.aemeasurable measurableSet_Ioo).mp hmem_map
    filter_upwards [hu_ae] with x hx
    have hsub : Wzc x - Wc x = σ⁻¹ * (twoSwapZeroBiasRV a x - twoSwapBaseRV a x) := by
      dsimp [Wzc, Wc]; ring
    rw [hsub, abs_mul, abs_of_pos (inv_pos.mpr hσ_pos), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_combStat_convex_permTwoSwap_sub_le hC hx.1.le hx.2.le
        x.1.2.1.1.1 x.1.2.1.1.2 x.1.2.1.2.1 x.1.2.1.2.2 x.1.1)
      (inv_nonneg.mpr hσ_pos.le)
  have hmap_Wc_eq : Pc.map Wc = P.map W := by
    let g : Equiv.Perm (Fin n) → ℝ := fun ρ ↦ σ⁻¹ * combStat a ρ
    have hg_meas : Measurable g := .of_discrete
    have hWc_comp : Wc = g ∘ (Prod.fst ∘ Prod.fst) := rfl
    have hW_comp : W = g ∘ π := by
      funext ω
      dsimp [W, S, μ, g, combStat]
      ring
    rw [hWc_comp, ← Measure.map_map hg_meas (measurable_fst.comp measurable_fst), hmap_fst,
      hW_comp, ← AEMeasurable.map_map_of_aemeasurable hg_meas.aemeasurable hπ, hπ_unif]
  rw [← hmap_Wc_eq]
  exact kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd Pc P' hvar_Wc hZB_c hδ hZ hZ_law

end SteinMethod
