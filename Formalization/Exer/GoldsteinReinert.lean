/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.ZeroBias
import Formalization.Exchangeable.Basic
import Formalization.ZeroBias.Basic
import Formalization.ZeroBias.Density
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Independence.Basic

/-!
# Zero-Bias from a Stein Pair & General Goldstein–Reinert Lemma
(`Formalization.Exer.GoldsteinReinert`)

Formalizes the canonical zero-bias construction from an exchangeable regression pair
(Goldstein & Reinert 1997 `\cite{gore97}` Lemma 2.1, proved from scratch; `%XXXX Exercise 3`,
`SteinIntro.tex:1527-1528`):

> construction.  Another canonical method of construction that is useful in practice can be
> derived from a Stein pair
> - see \cite{gore97}. %XXXX Exercise 3

## Main Results

- `SteinMethod.goldstein_reinert_zeroBias`: General Goldstein–Reinert construction for an
  arbitrary exchangeable pair $(W, W')$ with regression parameter $a > 0$ (no $a \le 1$ constraint)
  with respect to a sub-σ-algebra $\mathcal{F}$ containing $\sigma(W)$:
  the square-increment-biased measure
  $$dQ(\omega) := \frac{(W'(\omega) - W(\omega))^2}{2 a \sigma^2}\,dP(\omega)$$
  is a probability measure on $\Omega$, and the uniform interpolation
  $U W^\dagger + (1 - U) W'^\dagger$ has the zero-bias distribution of $W$ both canonically on
  $Q \otimes \mathrm{Unif}(0, 1)$ and universally for any realization.
- `SteinMethod.goldstein_reinert_zeroBias_of_comap`: Specialization to the canonical regression
  $\mathbb{E}[W' \mid W] = (1 - a) W$ a.s. with $a > 0$.
- `SteinMethod.Sec3_5_1_zeroBias_of_steinPair`: The approved `Prop` for `EXER-1`.
- `SteinMethod.Sec3_5_1_zeroBias_of_steinPair_holds`: Proof witness for `EXER-1`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Calculus and Fundamental Theorem of Calculus Helpers -/

/-- Pointwise identity for $C^1$ functions on the interval $[0, 1]$:
$(w' - w)^2 \int_0^1 F'(u w + (1 - u) w')\,du = (w' - w)(F(w') - F(w))$. -/
lemma sq_sub_integral_deriv_eq_sub_mul_sub
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (w w' : ℝ) :
    (w' - w) ^ 2 * (∫ u in (0 : ℝ)..1, deriv F (u * w + (1 - u) * w')) =
      (w' - w) * (F w' - F w) := by
  let g : ℝ → ℝ := fun u ↦ F (w' + u * (w - w'))
  have hg_cd : ContDiff ℝ 1 g := by
    have haff : ContDiff ℝ 1 (fun u : ℝ ↦ w' + u * (w - w')) :=
      contDiff_const.add (contDiff_id.mul contDiff_const)
    exact hF.comp haff
  have hg_deriv : ∀ u : ℝ, HasDerivAt g ((w - w') * deriv F (u * w + (1 - u) * w')) u := by
    intro u
    have hd_aff : HasDerivAt (fun s : ℝ ↦ w' + s * (w - w')) (w - w') u := by
      have hd1 : HasDerivAt (fun s : ℝ ↦ s * (w - w')) (1 * (w - w')) u :=
        (hasDerivAt_id' u).mul_const (w - w')
      rw [one_mul] at hd1
      have hd0 : HasDerivAt (fun _ : ℝ ↦ w') 0 u := hasDerivAt_const u w'
      have hd_add := hd0.add hd1
      rw [zero_add] at hd_add
      exact hd_add
    have hd_F : HasDerivAt F (deriv F (w' + u * (w - w'))) (w' + u * (w - w')) :=
      (hF.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hcomp := hd_F.comp u hd_aff
    have hrew : w' + u * (w - w') = u * w + (1 - u) * w' := by ring
    rw [hrew, mul_comm] at hcomp
    exact hcomp
  have hg_deriv_eq : ∀ u : ℝ, deriv g u = (w - w') * deriv F (u * w + (1 - u) * w') :=
    fun u ↦ (hg_deriv u).deriv
  have hg_ac : AbsolutelyContinuousOnInterval g 0 1 :=
    hg_cd.contDiffOn.absolutelyContinuousOnInterval
  have hFTC := hg_ac.integral_deriv_eq_sub
  have hg1 : g 1 = F w := by
    dsimp [g]
    have : w' + (1 : ℝ) * (w - w') = w := by ring
    rw [this]
  have hg0 : g 0 = F w' := by
    dsimp [g]
    have : w' + (0 : ℝ) * (w - w') = w' := by ring
    rw [this]
  rw [hg1, hg0] at hFTC
  have hstep : (∫ u in (0 : ℝ)..1, deriv g u) =
      (w - w') * (∫ u in (0 : ℝ)..1, deriv F (u * w + (1 - u) * w')) := by
    have hcongr : (fun u ↦ deriv g u) =
        fun u ↦ (w - w') * deriv F (u * w + (1 - u) * w') := funext hg_deriv_eq
    rw [hcongr, intervalIntegral.integral_const_mul]
  rw [hstep] at hFTC
  have hsq_eq : (w' - w) ^ 2 = (w - w') ^ 2 := by ring
  have hmul : (w' - w) ^ 2 * (∫ u in (0 : ℝ)..1, deriv F (u * w + (1 - u) * w')) =
      (w - w') * ((w - w') * (∫ u in (0 : ℝ)..1, deriv F (u * w + (1 - u) * w'))) := by
    rw [hsq_eq, sq, mul_assoc]
  rw [hmul, hFTC]
  ring

/-- Set integral over `Ioo 0 1` version of `sq_sub_integral_deriv_eq_sub_mul_sub`. -/
lemma sq_sub_setIntegral_Ioo_deriv_eq
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (w w' : ℝ) :
    (w' - w) ^ 2 * (∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * w + (1 - u) * w')) =
      (w' - w) * (F w' - F w) := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact sq_sub_integral_deriv_eq_sub_mul_sub hF w w'

/-! ### Section 2: Conditional Expectation & Regression from Sub-σ-Algebras -/

/-- Projection of linear regression from any sub-σ-algebra $\mathcal{F} \supseteq \sigma(W)$ down
to $\sigma(W)$: if $\mathbb{E}[W' - W \mid \mathcal{F}] = -a W$ a.s., then
$\mathbb{E}[W' \mid W] = (1 - a) W$ a.s. -/
lemma comap_regression_of_sub_algebra
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P) (hW'2 : MemLp W' 2 P)
    (F : MeasurableSpace Ω) (hF : F ≤ mΩ)
    (hWF : MeasurableSpace.comap W inferInstance ≤ F)
    (hreg : P[W' - W | F] =ᵐ[P] fun ω ↦ -a * W ω) :
    P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω := by
  let mW := MeasurableSpace.comap W inferInstance
  have hmW_le : mW ≤ mΩ := hW_meas.comap_le
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  have hDiff_int : Integrable (W' - W) P := hW'_int.sub hW_int
  have hW_sm : StronglyMeasurable[mW] W :=
    (comap_measurable (m := inferInstance) W).stronglyMeasurable
  have hTower : P[P[W' - W | F] | mW] =ᵐ[P] P[W' - W | mW] :=
    condExp_condExp_of_le (μ := P) (f := W' - W) hWF hF
  have hProj_LHS : P[P[W' - W | F] | mW] =ᵐ[P] fun ω ↦ -a * W ω := by
    refine (condExp_congr_ae (m := mW) hreg).trans ?_
    rw [condExp_of_stronglyMeasurable hmW_le (hW_sm.const_mul (-a)) (hW_int.const_mul (-a))]
  have hDiff_mW : P[W' - W | mW] =ᵐ[P] fun ω ↦ -a * W ω :=
    hTower.symm.trans hProj_LHS
  have hSplit : P[W' - W | mW] =ᵐ[P] fun ω ↦ P[W' | mW] ω - W ω := by
    have h1 := condExp_sub (m := mW) hW'_int hW_int
    have h2 := condExp_of_stronglyMeasurable hmW_le hW_sm hW_int
    filter_upwards [h1] with ω hω
    rw [hω, Pi.sub_apply, congr_fun h2 ω]
  filter_upwards [hDiff_mW, hSplit] with ω h1 h2
  rw [h2] at h1
  linarith

/-! ### Section 3: The Goldstein–Reinert Zero-Bias Identity for Test Functions -/

/-- Antisymmetry and regression identity for test functions:
$\int_\Omega (W' - W)(F(W') - F(W))\,dP = 2 a \int_\Omega W F(W)\,dP$. -/
lemma integral_sub_mul_sub_eq_two_mul_a_integral_mul
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W')
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    {F : ℝ → ℝ} (hF_meas : Measurable F) (hF_sub : ∀ w : ℝ, |F w| ≤ |w|) :
    ∫ ω, (W' ω - W ω) * (F (W' ω) - F (W ω)) ∂P =
      2 * a * ∫ ω, W ω * F (W ω) ∂P := by
  have hmW_le : MeasurableSpace.comap W inferInstance ≤ mΩ := hW_meas.comap_le
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'2 : MemLp W' 2 P := hId.memLp_snd hW2
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  have hW_sq_int : Integrable (fun ω ↦ W ω ^ 2) P := hW2.integrable_sq
  have hWW'_int : Integrable (W * W') P := hW2.integrable_mul hW'2
  have hW_aestrong : AEStronglyMeasurable W P := hW_meas.aestronglyMeasurable
  have hFW_aestrong : AEStronglyMeasurable (fun ω ↦ F (W ω)) P :=
    (hF_meas.comp hW_meas).aestronglyMeasurable
  have hWF_aestrong : AEStronglyMeasurable (fun ω ↦ W ω * F (W ω)) P :=
    hW_aestrong.mul hFW_aestrong
  have hWF_int : Integrable (fun ω ↦ W ω * F (W ω)) P := by
    refine hW_sq_int.mono' hWF_aestrong (ae_of_all P fun ω ↦ ?_)
    calc ‖W ω * F (W ω)‖ = |W ω * F (W ω)| := Real.norm_eq_abs _
      _ = |W ω| * |F (W ω)| := abs_mul _ _
      _ ≤ |W ω| * |W ω| := mul_le_mul_of_nonneg_left (hF_sub (W ω)) (abs_nonneg (W ω))
      _ = W ω ^ 2 := by rw [← sq, sq_abs]
  have hW'F_aestrong : AEStronglyMeasurable (fun ω ↦ W' ω * F (W ω)) P := by
    have hW'_aestrong : AEStronglyMeasurable W' P :=
      hId.aemeasurable_snd.aestronglyMeasurable
    exact hW'_aestrong.mul hFW_aestrong
  have hW'F_int : Integrable (fun ω ↦ W' ω * F (W ω)) P := by
    refine hWW'_int.norm.mono' hW'F_aestrong (ae_of_all P fun ω ↦ ?_)
    calc ‖W' ω * F (W ω)‖ = |W' ω * F (W ω)| := Real.norm_eq_abs _
      _ = |W' ω| * |F (W ω)| := abs_mul _ _
      _ ≤ |W' ω| * |W ω| := mul_le_mul_of_nonneg_left (hF_sub (W ω)) (abs_nonneg (W' ω))
      _ = |(W * W') ω| := by rw [Pi.mul_apply, mul_comm (W ω), abs_mul]
      _ = ‖(W * W') ω‖ := (Real.norm_eq_abs _).symm
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
        (fun ω ↦ W ω * F (W ω)) - (fun ω ↦ W' ω * F (W ω)) := by
      ext ω; simp only [Pi.sub_apply]; ring
    rw [heq]
    exact hWF_int.sub hW'F_int
  have hDiff_eq : ∫ ω, (W ω - W' ω) * F (W ω) ∂P = a * ∫ ω, W ω * F (W ω) ∂P := by
    have heq : (fun ω ↦ (W ω - W' ω) * F (W ω)) =
        (fun ω ↦ W ω * F (W ω)) - (fun ω ↦ W' ω * F (W ω)) := by
      ext ω; simp only [Pi.sub_apply]; ring
    rw [heq, integral_sub' hWF_int hW'F_int, hW'F_eq]
    ring
  have hG_meas : Measurable (fun p : ℝ × ℝ ↦ (p.2 - p.1) * F p.2) :=
    (measurable_snd.sub measurable_fst).mul (hF_meas.comp measurable_snd)
  have hExch_comp := hExch.comp hG_meas
  have hSymm_int :
      ∫ ω, (W' ω - W ω) * F (W' ω) ∂P = ∫ ω, (W ω - W' ω) * F (W ω) ∂P :=
    hExch_comp.integral_eq
  have hSymm_integrable : Integrable (fun ω ↦ (W' ω - W ω) * F (W' ω)) P :=
    hExch_comp.symm.integrable_snd hDiff_int
  have hSum_eq : (fun ω ↦ (W' ω - W ω) * (F (W' ω) - F (W ω))) =
      (fun ω ↦ (W' ω - W ω) * F (W' ω)) + (fun ω ↦ (W ω - W' ω) * F (W ω)) := by
    ext ω; simp only [Pi.add_apply]; ring
  rw [hSum_eq, integral_add' hSymm_integrable hDiff_int, hSymm_int, hDiff_eq]
  ring

/-- The square-increment-biased measure $dQ = \frac{(W' - W)^2}{2 a \sigma^2} dP$
is a probability measure. -/
lemma isProbabilityMeasure_withDensity_sq_sub
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hVar : 0 < ProbabilityTheory.variance W P) :
    IsProbabilityMeasure
      (P.withDensity fun ω ↦
        ENNReal.ofReal ((W' ω - W ω) ^ 2 / (2 * a * ProbabilityTheory.variance W P))) := by
  set c : ℝ := 2 * a * ProbabilityTheory.variance W P
  have hc : 0 < c := mul_pos (mul_pos two_pos ha) hVar
  have hc_ne : c ≠ 0 := hc.ne'
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'2 : MemLp W' 2 P := hId.memLp_snd hW2
  have hDiff : MemLp (fun ω ↦ W' ω - W ω) 2 P := hW'2.sub hW2
  have hsq_int : Integrable (fun ω ↦ (W' ω - W ω) ^ 2) P := hDiff.integrable_sq
  have hg_int : Integrable (fun ω ↦ (W' ω - W ω) ^ 2 / c) P := by
    have heq : (fun ω ↦ (W' ω - W ω) ^ 2 / c) = fun ω ↦ c⁻¹ * (W' ω - W ω) ^ 2 := by
      ext ω; ring
    rw [heq]
    exact hsq_int.const_mul c⁻¹
  have hg_nn : 0 ≤ᵐ[P] fun ω ↦ (W' ω - W ω) ^ 2 / c :=
    ae_of_all P fun ω ↦ div_nonneg (sq_nonneg _) hc.le
  have hsq_eq := (steinPair_integral_eq_zero_and_sq_sub_eq P hExch ha hW_meas hW2 hCond).2
  have h_int_g : ∫ ω, (W' ω - W ω) ^ 2 / c ∂P = 1 := calc
    ∫ ω, (W' ω - W ω) ^ 2 / c ∂P = ∫ ω, c⁻¹ * (W' ω - W ω) ^ 2 ∂P := by
      congr 1; ext ω; ring
    _ = c⁻¹ * ∫ ω, (W' ω - W ω) ^ 2 ∂P := integral_const_mul c⁻¹ _
    _ = c⁻¹ * c := by rw [hsq_eq]
    _ = 1 := inv_mul_cancel₀ hc_ne
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hg_int hg_nn, h_int_g, ENNReal.ofReal_one]

/-- Integration against the square-increment-biased measure $Q$ reduces via FTC
and regression to $\sigma^{-2} \mathbb{E}[W F(W)]$. -/
lemma integral_sq_sub_density_mul_setIntegral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hVar : 0 < ProbabilityTheory.variance W P)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hF_sub : ∀ w : ℝ, |F w| ≤ |w|) :
    let Q : Measure Ω :=
      P.withDensity fun ω ↦
        ENNReal.ofReal ((W' ω - W ω) ^ 2 / (2 * a * ProbabilityTheory.variance W P))
    ∫ ω, (∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * W ω + (1 - u) * W' ω)) ∂Q =
      (ProbabilityTheory.variance W P)⁻¹ * ∫ ω, W ω * F (W ω) ∂P := by
  intro Q
  set c : ℝ := 2 * a * ProbabilityTheory.variance W P
  have ha_pos : 0 < 2 * a := mul_pos two_pos ha
  have hc : 0 < c := mul_pos ha_pos hVar
  have hc_ne : c ≠ 0 := hc.ne'
  have h2a_ne : 2 * a ≠ 0 := ha_pos.ne'
  have hVar_ne : ProbabilityTheory.variance W P ≠ 0 := hVar.ne'
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'_aem : AEMeasurable W' P := hId.aemeasurable_snd
  have hDiff_aem : AEMeasurable (fun ω ↦ W' ω - W ω) P := hW'_aem.sub hW_meas.aemeasurable
  have hsq_div_aem : AEMeasurable (fun ω ↦ (W' ω - W ω) ^ 2 / c) P :=
    (hDiff_aem.pow_const 2).div_const c
  have hd_aem : AEMeasurable (fun ω ↦ ENNReal.ofReal ((W' ω - W ω) ^ 2 / c)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hsq_div_aem
  have hd_lt_top : ∀ᵐ ω ∂P, ENNReal.ofReal ((W' ω - W ω) ^ 2 / c) < ∞ :=
    ae_of_all P fun _ ↦ ENNReal.ofReal_lt_top
  let k : Ω → ℝ := fun ω ↦
    ∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * W ω + (1 - u) * W' ω)
  change ∫ ω, k ω ∂Q = _
  rw [show Q = P.withDensity (fun ω ↦ ENNReal.ofReal ((W' ω - W ω) ^ 2 / c)) from rfl,
    integral_withDensity_eq_integral_toReal_smul₀ hd_aem hd_lt_top k]
  have htoReal : ∀ ω, (ENNReal.ofReal ((W' ω - W ω) ^ 2 / c)).toReal =
      (W' ω - W ω) ^ 2 / c := fun ω ↦
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) hc.le)
  have hcongr : (fun ω ↦ (ENNReal.ofReal ((W' ω - W ω) ^ 2 / c)).toReal • k ω) =
      fun ω ↦ c⁻¹ * ((W' ω - W ω) * (F (W' ω) - F (W ω))) := by
    ext ω
    rw [smul_eq_mul, htoReal]
    dsimp [k]
    have hFTC := sq_sub_setIntegral_Ioo_deriv_eq hF (W ω) (W' ω)
    calc ((W' ω - W ω) ^ 2 / c) *
          (∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * W ω + (1 - u) * W' ω))
        = c⁻¹ * ((W' ω - W ω) ^ 2 *
            (∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * W ω + (1 - u) * W' ω))) := by ring
      _ = c⁻¹ * ((W' ω - W ω) * (F (W' ω) - F (W ω))) := by rw [hFTC]
  rw [hcongr, integral_const_mul]
  have hF_meas : Measurable F := hF.continuous.measurable
  have hreg := integral_sub_mul_sub_eq_two_mul_a_integral_mul
    P hExch hW_meas hW2 hCond hF_meas hF_sub
  rw [hreg]
  have hcan : c⁻¹ * (2 * a * ∫ ω, W ω * F (W ω) ∂P) =
      (ProbabilityTheory.variance W P)⁻¹ * ∫ ω, W ω * F (W ω) ∂P := by
    dsimp [c]
    rw [mul_inv_rev, mul_assoc, ← mul_assoc (2 * a)⁻¹,
      inv_mul_cancel₀ h2a_ne, one_mul]
  exact hcan

/-! ### Section 4: Uniform Distribution on (0, 1) -/

/-- For a uniform random variable $U \sim \mathrm{Unif}(0, 1)$, its law $P.\mathrm{map}(U)$
is $\mathrm{volume}.\mathrm{restrict}(0, 1)$. -/
lemma map_eq_restrict_Ioo_of_isUniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Ω → ℝ} (hU : MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P) :
    P.map U = volume.restrict (Set.Ioo (0 : ℝ) 1) := by
  rw [hU.map_eq, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
    inv_one, one_smul]

/-- Pushforward of a product measure under `Prod.map f id` for any a.e.-measurable `f`. -/
lemma map_prod_map_id_of_aemeasurable {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {f : α → γ} (hf : AEMeasurable f μ) :
    (μ.prod ν).map (Prod.map f id) = (μ.map f).prod ν := by
  have hf_mk_meas : Measurable (hf.mk f) := hf.measurable_mk
  have h_eq : (fun p : α × β ↦ Prod.map f id p) =ᵐ[μ.prod ν]
      fun p ↦ Prod.map (hf.mk f) id p := by
    have h1 : (fun p : α × β ↦ f p.1) =ᵐ[μ.prod ν] fun p ↦ hf.mk f p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp hf.ae_eq_mk
    filter_upwards [h1] with p hp
    dsimp [Prod.map]
    rw [hp]
  rw [Measure.map_congr h_eq,
    ← Measure.map_prod_map _ _ hf_mk_meas measurable_id,
    Measure.map_id, Measure.map_congr hf.ae_eq_mk.symm]

/-! ### Section 5: The Goldstein–Reinert Zero-Bias Theorems -/

/-- Canonical and universal zero-bias construction for an exchangeable pair $(W, W')$ with
regression $\mathbb{E}[W' \mid W] = (1 - a) W$ a.s. and $a > 0$ (Goldstein & Reinert 1997
`\cite{gore97}` Lemma 2.1, proved from scratch; `%XXXX Exercise 3`, `SteinIntro.tex:1527-1528`). -/
theorem goldstein_reinert_zeroBias_of_comap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hVar : 0 < ProbabilityTheory.variance W P) :
    let Q : Measure Ω :=
      P.withDensity fun ω ↦
        ENNReal.ofReal ((W' ω - W ω) ^ 2 / (2 * a * ProbabilityTheory.variance W P))
    (IsProbabilityMeasure Q ∧
      IsZeroBias P W (Q.prod (volume.restrict (Set.Ioo (0 : ℝ) 1)))
        (fun p ↦ p.2 * W p.1 + (1 - p.2) * W' p.1)) ∧
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      {Wd W'd U : Ω' → ℝ},
      AEMeasurable Wd P' →
      AEMeasurable W'd P' →
      AEMeasurable U P' →
      P'.map (fun ω' ↦ (Wd ω', W'd ω')) = Q.map (fun ω ↦ (W ω, W' ω)) →
      MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P' →
      ProbabilityTheory.IndepFun U (fun ω' ↦ (Wd ω', W'd ω')) P' →
      IsZeroBias P W P' (fun ω' ↦ U ω' * Wd ω' + (1 - U ω') * W'd ω') := by
  intro Q
  have hQ_prob : IsProbabilityMeasure Q :=
    isProbabilityMeasure_withDensity_sq_sub P hExch ha hW_meas hW2 hCond hVar
  have hMean : ∫ ω, W ω ∂P = 0 :=
    (steinPair_integral_eq_zero_and_sq_sub_eq P hExch ha hW_meas hW2 hCond).1
  have hVar_ne : ProbabilityTheory.variance W P ≠ 0 := hVar.ne'
  set μU : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  have hμU_prob : IsProbabilityMeasure μU := by
    constructor
    simp only [μU, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
  have : IsProbabilityMeasure Q := hQ_prob
  have : IsProbabilityMeasure μU := hμU_prob
  have hQ_prod_prob : IsProbabilityMeasure (Q.prod μU) := inferInstance
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'_aem_P : AEMeasurable W' P := hId.aemeasurable_snd
  have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
  have hW'_aem_Q : AEMeasurable W' Q := hW'_aem_P.mono_ac hQP
  have hW'_aem_prod : AEMeasurable (fun p : Ω × ℝ ↦ W' p.1) (Q.prod μU) :=
    hW'_aem_Q.comp_fst
  have hW_aem_prod : AEMeasurable (fun p : Ω × ℝ ↦ W p.1) (Q.prod μU) :=
    (hW_meas.comp measurable_fst).aemeasurable
  let Wz_canon : Ω × ℝ → ℝ := fun p ↦ p.2 * W p.1 + (1 - p.2) * W' p.1
  have hWz_canon_aem : AEMeasurable Wz_canon (Q.prod μU) := by
    dsimp [Wz_canon]
    refine (measurable_snd.aemeasurable.mul hW_aem_prod).add ?_
    exact (measurable_const.sub measurable_snd).aemeasurable.mul hW'_aem_prod
  have hC1_canon : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → (∀ w : ℝ, |F w| ≤ |w|) →
      (∃ B : ℝ, ∀ w : ℝ, |deriv F w| ≤ B) →
      ∫ ω, W ω * F (W ω) ∂P =
        ProbabilityTheory.variance W P * ∫ p, deriv F (Wz_canon p) ∂(Q.prod μU) := by
    intro F hF hF_sub ⟨B, hB⟩
    have hderiv_cont : Continuous (deriv F) := hF.continuous_deriv le_rfl
    have hderiv_meas : Measurable (deriv F) := hderiv_cont.measurable
    have hderiv_aem : AEMeasurable (fun p ↦ deriv F (Wz_canon p)) (Q.prod μU) :=
      hderiv_meas.comp_aemeasurable hWz_canon_aem
    have hderiv_int : Integrable (fun p ↦ deriv F (Wz_canon p)) (Q.prod μU) :=
      Integrable.of_bound hderiv_aem.aestronglyMeasurable B
        (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hB (Wz_canon p))
    have hFubini : ∫ p, deriv F (Wz_canon p) ∂(Q.prod μU) =
        ∫ ω, (∫ u in Set.Ioo (0 : ℝ) 1, deriv F (u * W ω + (1 - u) * W' ω)) ∂Q := by
      exact integral_prod (fun p ↦ deriv F (Wz_canon p)) hderiv_int
    have hFTC_Q :=
      integral_sq_sub_density_mul_setIntegral_eq P hExch ha hW_meas hW2 hCond hVar hF hF_sub
    change ∫ ω, (∫ u in Set.Ioo (0 : ℝ) 1,
      deriv F (u * W ω + (1 - u) * W' ω)) ∂Q = _ at hFTC_Q
    rw [hFubini, hFTC_Q]
    rw [← mul_assoc, mul_inv_cancel₀ hVar_ne, one_mul]
  have hZB_canon :=
    (isZeroBias_and_map_eq_of_c1_sublinear P (Q.prod μU) hW2 hMean hVar hWz_canon_aem hC1_canon).2
  refine ⟨⟨hQ_prob, hZB_canon⟩, ?_⟩
  intro Ω' mΩ' P' hP' Wd W'd U hWd hW'd hU hmap_pair hUnif hIndep
  let Wz_univ : Ω' → ℝ := fun ω' ↦ U ω' * Wd ω' + (1 - U ω') * W'd ω'
  have hWz_univ_aem : AEMeasurable Wz_univ P' := by
    dsimp [Wz_univ]
    refine (hU.mul hWd).add ?_
    exact (measurable_const.sub measurable_id).aemeasurable.comp_aemeasurable hU |>.mul hW'd
  have hU_map : P'.map U = μU := map_eq_restrict_Ioo_of_isUniform hUnif
  have hWd_pair_aem : AEMeasurable (fun ω' ↦ (Wd ω', W'd ω')) P' := hWd.prodMk hW'd
  have hIndep_symm : ProbabilityTheory.IndepFun (fun ω' ↦ (Wd ω', W'd ω')) U P' := hIndep.symm
  have hprod_P' : P'.map (fun ω' ↦ ((Wd ω', W'd ω'), U ω')) =
      (Q.map (fun ω ↦ (W ω, W' ω))).prod μU := by
    rw [hIndep_symm.map_prod_eq_prod_map_map hWd_pair_aem hU, hmap_pair, hU_map]
  have hW_pair_aem : AEMeasurable (fun ω ↦ (W ω, W' ω)) Q :=
    (hW_meas.aemeasurable.mono_ac hQP).prodMk hW'_aem_Q
  have hprod_canon : (Q.prod μU).map (fun p ↦ ((W p.1, W' p.1), p.2)) =
      (Q.map (fun ω ↦ (W ω, W' ω))).prod μU := by
    have hrew : (fun p : Ω × ℝ ↦ ((W p.1, W' p.1), p.2)) =
        Prod.map (fun ω ↦ (W ω, W' ω)) id := rfl
    rw [hrew, map_prod_map_id_of_aemeasurable Q μU hW_pair_aem]
  let ψ : (ℝ × ℝ) × ℝ → ℝ := fun q ↦ q.2 * q.1.1 + (1 - q.2) * q.1.2
  have hψ_cont : Continuous ψ := by fun_prop
  have hψ_meas : Measurable ψ := hψ_cont.measurable
  have huniv_comp : Wz_univ = ψ ∘ (fun ω' ↦ ((Wd ω', W'd ω'), U ω')) := rfl
  have hcanon_comp : Wz_canon = ψ ∘ (fun p ↦ ((W p.1, W' p.1), p.2)) := rfl
  have hV_aem : AEMeasurable (fun ω' ↦ ((Wd ω', W'd ω'), U ω')) P' :=
    hWd_pair_aem.prodMk hU
  have hP_aem : AEMeasurable (fun p : Ω × ℝ ↦ ((W p.1, W' p.1), p.2)) (Q.prod μU) :=
    (hW_pair_aem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      measurable_snd.aemeasurable
  have hmap_Wz : P'.map Wz_univ = (Q.prod μU).map Wz_canon := by
    rw [huniv_comp, hcanon_comp,
      ← AEMeasurable.map_map_of_aemeasurable hψ_meas.aemeasurable hV_aem,
      ← AEMeasurable.map_map_of_aemeasurable hψ_meas.aemeasurable hP_aem,
      hprod_P', hprod_canon]
  have hId_Wz : IdentDistrib Wz_canon Wz_univ (Q.prod μU) P' :=
    ⟨hWz_canon_aem, hWz_univ_aem, hmap_Wz.symm⟩
  exact IsZeroBias.congr_identDistrib hZB_canon (IdentDistrib.refl hW_meas.aemeasurable) hId_Wz

/-- General Goldstein–Reinert construction (`\cite{gore97}` Lemma 2.1, proved from scratch;
`SteinIntro.tex:1527-1528`, `%XXXX Exercise 3`): for an arbitrary exchangeable pair $(W, W')$ with
regression parameter $a > 0$ (no $a \le 1$ constraint) with respect to a sub-σ-algebra
$\mathcal{F}$ containing $\sigma(W)$ with $\mathbb{E}[W' - W \mid \mathcal{F}] = -a W$ a.s.,
the square-increment-biased measure $Q$ is a probability measure and the uniform linear
interpolation $U W^\dagger + (1 - U) W'^\dagger$ has the zero-bias distribution of $W$
both canonically and universally. -/
theorem goldstein_reinert_zeroBias
    {Ω : Type*} (F : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hF : F ≤ mΩ)
    (hWF : MeasurableSpace.comap W inferInstance ≤ F)
    (hreg : P[W' - W | F] =ᵐ[P] fun ω ↦ -a * W ω)
    (hVar : 0 < ProbabilityTheory.variance W P) :
    let Q : Measure Ω :=
      P.withDensity fun ω ↦
        ENNReal.ofReal ((W' ω - W ω) ^ 2 / (2 * a * ProbabilityTheory.variance W P))
    (IsProbabilityMeasure Q ∧
      IsZeroBias P W (Q.prod (volume.restrict (Set.Ioo (0 : ℝ) 1)))
        (fun p ↦ p.2 * W p.1 + (1 - p.2) * W' p.1)) ∧
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      {Wd W'd U : Ω' → ℝ},
      AEMeasurable Wd P' →
      AEMeasurable W'd P' →
      AEMeasurable U P' →
      P'.map (fun ω' ↦ (Wd ω', W'd ω')) = Q.map (fun ω ↦ (W ω, W' ω)) →
      MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P' →
      ProbabilityTheory.IndepFun U (fun ω' ↦ (Wd ω', W'd ω')) P' →
      IsZeroBias P W P' (fun ω' ↦ U ω' * Wd ω' + (1 - U ω') * W'd ω') := by
  intro Q
  have hW'2 : MemLp W' 2 P := hExch.fst_identDistrib_snd.memLp_snd hW2
  have hCond := comap_regression_of_sub_algebra hW_meas hW2 hW'2 F hF hWF hreg
  exact goldstein_reinert_zeroBias_of_comap P hExch ha hW_meas hW2 hCond hVar

end SteinMethod
