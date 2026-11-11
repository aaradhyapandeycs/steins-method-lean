/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Normal.WassersteinBound
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Size-Bias Couplings and Normal Approximation (`Formalization.SizeBias.Basic`)

Develops the core properties of size-bias distributions and size-bias Stein couplings from
Section 3.4 of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`,
`SteinIntro.tex:1220-1280`):

* `IsSizeBias.integrable_comp_of_pos_mean`: transfer of integrability from $X g(X)$ under $P$ to
  $g(X^s)$ under $P'$ when $\mathbb{E}[X] > 0$ via monotone truncation.
* `pos_integral_of_nonneg_of_variance_pos`: strict positivity $\mathbb{E}[X] > 0$ for an a.s.
  nonnegative integrable random variable with $\operatorname{Var}(X) > 0$.
* `sizeBias_stein_identity` (Section 3.4 eq. `(3.23)` `\label{71}`, `SteinIntro.tex:1232-1236`;
  `ISSUE-TYPO-3.4a`): standardized size-bias Stein identity.
* `sizeBias_law_characterization` (**Proposition 3.11**, restricted to $\mu > 0$,
  `SteinIntro.tex:1239-1245`; `ISSUE-3.11`, ruling `D8`): uniqueness and existence of the
  size-bias law $dF^s(x) = (x / \mu)\,dF(x)$.
* `sizeBias_nat_pmf` (**Corollary 3.12**, restricted to $\mu > 0$, `SteinIntro.tex:1246-1252`;
  `ISSUE-3.11`): discrete size-bias probability mass formula
  $\mathbb{P}(X^s = k) = k\,\mathbb{P}(X = k) / \mu$.
* `sizeBias_wassersteinDist_le` (**Theorem 3.13**, `\label{thm71}`, `SteinIntro.tex:1255-1261`):
  Wasserstein-1 normal approximation bound via size-bias coupling on a common probability space.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### Integrability transfer and positive-mean helpers -/

/-- If $X^s$ has the size-bias distribution of $X$ with $\mathbb{E}[X] > 0$ and $X g(X)$ is
integrable for measurable $g : \mathbb{R} \to \mathbb{R}$, then $g(X^s)$ is integrable
(Definition 3.7 `\label{sbc}`, `SteinIntro.tex:1224-1236`; ruling `D8`). -/
theorem IsSizeBias.integrable_comp_of_pos_mean
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsFiniteMeasure P']
    {X : Ω → ℝ} {Xs : Ω' → ℝ} {g : ℝ → ℝ}
    (hSB : IsSizeBias P X P' Xs) (hμ : 0 < ∫ ω, X ω ∂P)
    (hg : Measurable g) (hInt : Integrable (fun ω ↦ X ω * g (X ω)) P) :
    Integrable (fun ω' ↦ g (Xs ω')) P' := by
  rcases hSB with ⟨_, hX_int, hXs_meas, hSB_eq⟩
  let hM : ℕ → ℝ → ℝ := fun M x ↦ min |g x| (M : ℝ)
  have hM_meas : ∀ M : ℕ, Measurable (hM M) := fun M ↦
    continuous_min.measurable.comp ((continuous_abs.measurable.comp hg).prodMk measurable_const)
  have hM_nn : ∀ (M : ℕ) (x : ℝ), 0 ≤ hM M x :=
    fun M x ↦ le_min (abs_nonneg (g x)) (Nat.cast_nonneg M)
  have hM_le_abs : ∀ (M : ℕ) (x : ℝ), hM M x ≤ |g x| :=
    fun M x ↦ min_le_left |g x| (M : ℝ)
  have hM_le_const : ∀ (M : ℕ) (x : ℝ), hM M x ≤ (M : ℝ) :=
    fun M x ↦ min_le_right |g x| (M : ℝ)
  have hAbs_int : Integrable (fun ω ↦ |X ω * g (X ω)|) P := by
    simpa only [Real.norm_eq_abs] using hInt.norm
  have hXhM_abs_le : ∀ (M : ℕ) (ω : Ω), |X ω * hM M (X ω)| ≤ |X ω * g (X ω)| := fun M ω ↦ by
    rw [abs_mul, abs_mul, abs_of_nonneg (hM_nn M (X ω))]
    exact mul_le_mul_of_nonneg_left (hM_le_abs M (X ω)) (abs_nonneg (X ω))
  have hXhM_int : ∀ M : ℕ, Integrable (fun ω ↦ X ω * hM M (X ω)) P := fun M ↦
    hInt.norm.mono'
      (hX_int.aestronglyMeasurable.mul
        ((hM_meas M).comp_aemeasurable hX_int.aemeasurable).aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs] using hXhM_abs_le M ω)
  have hLIntM : ∀ M : ℕ,
      ∫⁻ ω', ENNReal.ofReal (hM M (Xs ω')) ∂P' ≤
        ENNReal.ofReal ((∫ ω, |X ω * g (X ω)| ∂P) / ∫ ω, X ω ∂P) := fun M ↦ by
    have hhMXs_asm : AEStronglyMeasurable (fun ω' ↦ hM M (Xs ω')) P' :=
      ((hM_meas M).comp_aemeasurable hXs_meas).aestronglyMeasurable
    have hhMXs_int : Integrable (fun ω' ↦ hM M (Xs ω')) P' :=
      (integrable_const (M : ℝ)).mono' hhMXs_asm
        (Eventually.of_forall fun ω' ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hM_nn M (Xs ω'))]
          exact hM_le_const M (Xs ω'))
    have hhMXs_nn : 0 ≤ᵐ[P'] fun ω' ↦ hM M (Xs ω') :=
      Eventually.of_forall fun ω' ↦ hM_nn M (Xs ω')
    have hIntLe : ∫ ω, X ω * hM M (X ω) ∂P ≤ ∫ ω, |X ω * g (X ω)| ∂P :=
      integral_mono (hXhM_int M) hAbs_int fun ω ↦ (le_abs_self _).trans (hXhM_abs_le M ω)
    have hRealLe : ∫ ω', hM M (Xs ω') ∂P' ≤
        (∫ ω, |X ω * g (X ω)| ∂P) / ∫ ω, X ω ∂P := by
      refine le_of_mul_le_mul_left ?_ hμ
      rw [mul_div_cancel₀ _ hμ.ne', ← hSB_eq (hM M) (hM_meas M) (hXhM_int M)]
      exact hIntLe
    rw [← ofReal_integral_eq_lintegral_ofReal hhMXs_int hhMXs_nn]
    exact ENNReal.ofReal_le_ofReal hRealLe
  have hSup : ∀ r : ℝ, (⨆ M : ℕ, ENNReal.ofReal (min r (M : ℝ))) = ENNReal.ofReal r := fun r ↦ by
    refine le_antisymm (iSup_le fun M ↦ ENNReal.ofReal_le_ofReal (min_le_left r (M : ℝ))) ?_
    obtain ⟨M, hM_gt⟩ := exists_nat_gt r
    exact le_trans (by rw [min_eq_left hM_gt.le])
      (le_iSup (fun k : ℕ ↦ ENNReal.ofReal (min r (k : ℝ))) M)
  have hLInt : ∫⁻ ω', ENNReal.ofReal ‖g (Xs ω')‖ ∂P' ≤
      ENNReal.ofReal ((∫ ω, |X ω * g (X ω)| ∂P) / ∫ ω, X ω ∂P) := calc
    ∫⁻ ω', ENNReal.ofReal ‖g (Xs ω')‖ ∂P'
      = ∫⁻ ω', (⨆ M : ℕ, ENNReal.ofReal (hM M (Xs ω'))) ∂P' := by
        refine lintegral_congr fun ω' ↦ ?_
        rw [Real.norm_eq_abs, ← hSup |g (Xs ω')|]
    _ = ⨆ M : ℕ, ∫⁻ ω', ENNReal.ofReal (hM M (Xs ω')) ∂P' :=
        lintegral_iSup'
          (fun M ↦ ((hM_meas M).comp_aemeasurable hXs_meas).ennreal_ofReal)
          (Eventually.of_forall fun _ _ _ h12 ↦
            ENNReal.ofReal_le_ofReal
              (le_min (min_le_left _ _) ((min_le_right _ _).trans (Nat.cast_le.mpr h12))))
    _ ≤ ENNReal.ofReal ((∫ ω, |X ω * g (X ω)| ∂P) / ∫ ω, X ω ∂P) := iSup_le hLIntM
  exact ⟨(hg.comp_aemeasurable hXs_meas).aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm _).mpr (hLInt.trans_lt ENNReal.ofReal_lt_top)⟩

/-- If $X \ge 0$ a.s. is integrable on a probability space with $\operatorname{Var}(X) > 0$, then
$\mathbb{E}[X] > 0$ (`SteinIntro.tex:1232-1261`). -/
theorem pos_integral_of_nonneg_of_variance_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX_nn : 0 ≤ᵐ[P] X) (hX_int : Integrable X P)
    (hVar : 0 < ProbabilityTheory.variance X P) :
    0 < ∫ ω, X ω ∂P := by
  have hge : 0 ≤ ∫ ω, X ω ∂P := integral_nonneg_of_ae hX_nn
  rcases hge.eq_or_lt with hzero | hpos
  · have hX0 : X =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hX_nn hX_int).mp hzero.symm
    have hVar0 : ProbabilityTheory.variance X P = 0 := by
      rw [ProbabilityTheory.variance_congr hX0, ProbabilityTheory.variance_zero]
    linarith
  · exact hpos

/-! ### Section 3.4 Stein identity, Proposition 3.11, and Corollary 3.12 -/

/-- **Section 3.4 size-bias Stein identity** (eq. `(3.23)` `\label{71}`,
`SteinIntro.tex:1232-1236`; `ISSUE-TYPO-3.4a`): for $X \ge 0$ a.s. in $L^2(P)$ with
$\sigma^2 = \operatorname{Var}(X) > 0$, $\mu = \mathbb{E}[X]$, $W = (X - \mu)/\sigma$, and
size-bias $X^s$ on the same probability space, if $X f(W)$ and $f(W)$ are integrable for measurable
$f$, then $f((X^s - \mu)/\sigma)$ is integrable and
$\mathbb{E}[W f(W)] = \frac{\mu}{\sigma}(\mathbb{E}[f((X^s - \mu)/\sigma)] - \mathbb{E}[f(W)])$. -/
theorem sizeBias_stein_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xs : Ω → ℝ} {f : ℝ → ℝ}
    (hX_nn : 0 ≤ᵐ[P] X) (hX2 : MemLp X 2 P)
    (hVar : 0 < ProbabilityTheory.variance X P)
    (hSB : IsSizeBias P X P Xs) (hf : Measurable f)
    (hXfW_int : Integrable (fun ω ↦
      X ω * f ((X ω - ∫ x, X x ∂P) / Real.sqrt (ProbabilityTheory.variance X P))) P)
    (hfW_int : Integrable (fun ω ↦
      f ((X ω - ∫ x, X x ∂P) / Real.sqrt (ProbabilityTheory.variance X P))) P) :
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    let W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
    Integrable (fun ω ↦ f ((Xs ω - μ) / σ)) P ∧
      ∫ ω, W ω * f (W ω) ∂P =
        μ / σ * ((∫ ω, f ((Xs ω - μ) / σ) ∂P) - ∫ ω, f (W ω) ∂P) := by
  dsimp only
  set μ : ℝ := ∫ ω, X ω ∂P
  set σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
  set W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
  have hX_int : Integrable X P := hX2.integrable one_le_two
  have hμ_pos : 0 < μ := pos_integral_of_nonneg_of_variance_pos P hX_nn hX_int hVar
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  let g : ℝ → ℝ := fun x ↦ f ((x - μ) / σ)
  have hg_meas : Measurable g :=
    hf.comp ((continuous_id.sub continuous_const).div₀ continuous_const
      (fun _ ↦ hσ_pos.ne')).measurable
  have hfXs_int : Integrable (fun ω ↦ f ((Xs ω - μ) / σ)) P :=
    hSB.integrable_comp_of_pos_mean hμ_pos hg_meas hXfW_int
  refine ⟨hfXs_int, ?_⟩
  have hXfW_int' : Integrable (fun ω ↦ X ω * f (W ω)) P := hXfW_int
  have hfW_int' : Integrable (fun ω ↦ f (W ω)) P := hfW_int
  have hSB_g : ∫ ω, X ω * f (W ω) ∂P = μ * ∫ ω, f ((Xs ω - μ) / σ) ∂P :=
    hSB.2.2.2 g hg_meas hXfW_int
  have hW_eq : (fun ω ↦ W ω * f (W ω)) =
      fun ω ↦ σ⁻¹ * (X ω * f (W ω) - μ * f (W ω)) := by
    ext ω
    dsimp only [W]
    rw [div_eq_mul_inv]
    ring
  rw [hW_eq, integral_const_mul σ⁻¹, integral_sub hXfW_int' (hfW_int'.const_mul μ),
    integral_const_mul μ, hSB_g, div_eq_mul_inv]
  ring

/-- **Proposition 3.11, restricted to $\mu > 0$** (`SteinIntro.tex:1239-1245`; `ISSUE-3.11`,
ruling `D8`): for $X \ge 0$ a.s. integrable with $\mu = \mathbb{E}[X] > 0$, every size-bias random
variable $X^s$ has law `(P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μ))`, and conversely
this weighted measure $\nu$ is a probability measure on $\mathbb{R}$ such that `id` under $\nu$
has the size-bias distribution with respect to $X$. -/
theorem sizeBias_law_characterization
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX_nn : 0 ≤ᵐ[P] X) (hX_int : Integrable X P) (hμ_pos : 0 < ∫ ω, X ω ∂P) :
    let μ : ℝ := ∫ ω, X ω ∂P
    (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {Xs : Ω' → ℝ},
        IsSizeBias P X P' Xs →
        P'.map Xs = (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μ))) ∧
      (let ν : Measure ℝ := (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μ))
       IsProbabilityMeasure ν ∧ IsSizeBias P X ν id) := by
  dsimp only
  set μ : ℝ := ∫ ω, X ω ∂P
  set d : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (x / μ)
  have hd_meas : Measurable d :=
    ENNReal.measurable_ofReal.comp
      (continuous_id.div₀ continuous_const (fun _ ↦ hμ_pos.ne')).measurable
  have hX_aem : AEMeasurable X P := hX_int.aemeasurable
  have hid_nn : ∀ᵐ x ∂(P.map X), 0 ≤ x :=
    (ae_map_iff (p := fun y : ℝ ↦ 0 ≤ y) hX_aem measurableSet_Ici).mpr hX_nn
  have hid_int : Integrable (fun x : ℝ ↦ x) (P.map X) :=
    (integrable_map_measure aestronglyMeasurable_id hX_aem).mpr hX_int
  have hdiv_int : Integrable (fun x : ℝ ↦ x / μ) (P.map X) := hid_int.div_const μ
  have hdiv_nn : 0 ≤ᵐ[P.map X] fun x : ℝ ↦ x / μ := by
    filter_upwards [hid_nn] with x hx
    exact div_nonneg hx hμ_pos.le
  refine ⟨?_, ?_⟩
  · intro P' _ Xs hSB
    refine Measure.ext fun A hA ↦ ?_
    let f : ℝ → ℝ := A.indicator 1
    have hf_meas : Measurable f := measurable_one.indicator hA
    have hf_bdd : ∀ x : ℝ, |f x| ≤ 1 := fun x ↦ by
      dsimp only [f]
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Pi.one_apply, abs_one]
      · rw [Set.indicator_of_notMem hx, abs_zero]
        exact zero_le_one
    have hXf_int : Integrable (fun ω ↦ X ω * f (X ω)) P :=
      (hX_int.norm.mul_const 1).mono'
        (hX_int.aestronglyMeasurable.mul (hf_meas.comp_aemeasurable hX_aem).aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ by
          simpa only [Real.norm_eq_abs, abs_mul] using
            mul_le_mul_of_nonneg_left (hf_bdd (X ω)) (abs_nonneg (X ω)))
    have hEq : ∫ ω, X ω * f (X ω) ∂P = μ * ∫ ω', f (Xs ω') ∂P' :=
      hSB.2.2.2 f hf_meas hXf_int
    have hRHS : ∫ ω', f (Xs ω') ∂P' = (P'.map Xs).real A := by
      rw [← integral_map hSB.2.2.1 hf_meas.aestronglyMeasurable, integral_indicator_one hA]
    have hmul_ind : (fun x : ℝ ↦ x * f x) = A.indicator id := funext fun x ↦ by
      dsimp only [f]
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.one_apply, mul_one, id_eq]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    have hLHS : ∫ ω, X ω * f (X ω) ∂P = ∫ x in A, x ∂(P.map X) := calc
      ∫ ω, X ω * f (X ω) ∂P = ∫ x, x * f x ∂(P.map X) :=
        (integral_map hX_aem (measurable_id.mul hf_meas).aestronglyMeasurable).symm
      _ = ∫ x, A.indicator id x ∂(P.map X) := by rw [hmul_ind]
      _ = ∫ x in A, x ∂(P.map X) := integral_indicator hA
    have hSetDiv : ∫ x in A, (x / μ) ∂(P.map X) = (P'.map Xs).real A := by
      rw [integral_div μ (fun x : ℝ ↦ x), ← hLHS, hEq, hRHS]
      exact (div_eq_iff hμ_pos.ne').mpr (mul_comm _ _)
    calc
      (P'.map Xs) A = ENNReal.ofReal ((P'.map Xs).real A) :=
        (ofReal_measureReal (measure_ne_top (P'.map Xs) A)).symm
      _ = ENNReal.ofReal (∫ x in A, (x / μ) ∂(P.map X)) := by rw [hSetDiv]
      _ = ∫⁻ x in A, d x ∂(P.map X) :=
        ofReal_integral_eq_lintegral_ofReal hdiv_int.integrableOn (ae_restrict_of_ae hdiv_nn)
      _ = (P.map X).withDensity d A := (withDensity_apply d hA).symm
  · set ν : Measure ℝ := (P.map X).withDensity d
    have hIntDivUniv : ∫ x, (x / μ) ∂(P.map X) = 1 := by
      rw [integral_div μ (fun x : ℝ ↦ x),
        integral_map hX_aem (measurable_id' : Measurable fun x : ℝ ↦ x).aestronglyMeasurable]
      exact div_self hμ_pos.ne'
    have hν_prob : IsProbabilityMeasure ν := by
      rw [isProbabilityMeasure_iff, withDensity_apply d MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hdiv_int hdiv_nn, hIntDivUniv, ENNReal.ofReal_one]
    refine ⟨hν_prob, hX_nn, hX_int, measurable_id.aemeasurable, fun f hf _ ↦ ?_⟩
    have hToReal_ae :
        (fun x : ℝ ↦ (d x).toReal • f x) =ᵐ[P.map X] fun x : ℝ ↦ μ⁻¹ * (x * f x) := by
      filter_upwards [hdiv_nn] with x hx
      dsimp only [d]
      rw [ENNReal.toReal_ofReal hx, smul_eq_mul, div_eq_mul_inv]
      ring
    have hν_int_eq : ∫ x, f x ∂ν = μ⁻¹ * ∫ ω, X ω * f (X ω) ∂P := calc
      ∫ x, f x ∂ν = ∫ x, (d x).toReal • f x ∂(P.map X) :=
        integral_withDensity_eq_integral_toReal_smul hd_meas
          (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) f
      _ = ∫ x, μ⁻¹ * (x * f x) ∂(P.map X) := integral_congr_ae hToReal_ae
      _ = μ⁻¹ * ∫ x, x * f x ∂(P.map X) := integral_const_mul μ⁻¹ (fun x ↦ x * f x)
      _ = μ⁻¹ * ∫ ω, X ω * f (X ω) ∂P := by
        rw [integral_map hX_aem (measurable_id'.fun_mul hf).aestronglyMeasurable]
    change ∫ ω, X ω * f (X ω) ∂P = μ * ∫ x, f x ∂ν
    rw [hν_int_eq, ← mul_assoc, mul_inv_cancel₀ hμ_pos.ne', one_mul]

/-- Point-mass relation for any size-bias random variable with positive mean:
$P'(X^s = c) = c\,P(X = c) / \mathbb{E}[X]$ for every $c \in \mathbb{R}$
(`SteinIntro.tex:1246-1252`). -/
theorem IsSizeBias.measureReal_eq_singleton
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P]
    {P' : Measure Ω'} [IsFiniteMeasure P']
    {X : Ω → ℝ} {Xs : Ω' → ℝ}
    (hSB : IsSizeBias P X P' Xs) (hμ_pos : 0 < ∫ ω, X ω ∂P) (c : ℝ) :
    P'.real {ω' | Xs ω' = c} = c * P.real {ω | X ω = c} / ∫ ω, X ω ∂P := by
  set S : Set ℝ := {c}
  have hS : MeasurableSet S := measurableSet_singleton c
  let f : ℝ → ℝ := S.indicator 1
  have hf_meas : Measurable f := measurable_one.indicator hS
  have hf_bdd : ∀ x : ℝ, |f x| ≤ 1 := fun x ↦ by
    dsimp only [f]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Pi.one_apply, abs_one]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact zero_le_one
  have hmul_c : (fun ω : Ω ↦ X ω * f (X ω)) = fun ω ↦ c * f (X ω) := funext fun ω ↦ by
    dsimp only [f]
    by_cases hx : X ω ∈ S
    · rw [Set.mem_singleton_iff.mp hx]
    · rw [Set.indicator_of_notMem hx, mul_zero, mul_zero]
  have hfX_int : Integrable (fun ω ↦ f (X ω)) P :=
    (integrable_const (1 : ℝ)).mono'
      (hf_meas.comp_aemeasurable hSB.2.1.aemeasurable).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]
        exact hf_bdd (X ω))
  have hXf_int : Integrable (fun ω ↦ X ω * f (X ω)) P := by
    rw [hmul_c]
    exact hfX_int.const_mul c
  have hEq := hSB.2.2.2 f hf_meas hXf_int
  have hpreX : X ⁻¹' S = {ω | X ω = c} := Set.ext fun _ ↦ Set.mem_singleton_iff
  have hpreXs : Xs ⁻¹' S = {ω' | Xs ω' = c} := Set.ext fun _ ↦ Set.mem_singleton_iff
  have hLHS : ∫ ω, X ω * f (X ω) ∂P = c * P.real {ω | X ω = c} := by
    rw [hmul_c, integral_const_mul c,
      ← integral_map hSB.2.1.aemeasurable hf_meas.aestronglyMeasurable,
      integral_indicator_one hS,
      map_measureReal_apply_of_aemeasurable hSB.2.1.aemeasurable hS, hpreX]
  have hRHS : ∫ ω', f (Xs ω') ∂P' = P'.real {ω' | Xs ω' = c} := by
    rw [← integral_map hSB.2.2.1 hf_meas.aestronglyMeasurable,
      integral_indicator_one hS,
      map_measureReal_apply_of_aemeasurable hSB.2.2.1 hS, hpreXs]
  rw [hLHS, hRHS] at hEq
  refine mul_right_cancel₀ hμ_pos.ne' ?_
  rw [div_mul_cancel₀ _ hμ_pos.ne', hEq, mul_comm]

/-- **Corollary 3.12, restricted to $\mu > 0$** (`SteinIntro.tex:1246-1252`; `ISSUE-3.11`):
for a nonnegative integer-valued integrable random variable $X$ with $\mu = \mathbb{E}[X] > 0$ and
size-bias random variable $X^s$, $\mathbb{P}(X^s = k) = k\,\mathbb{P}(X = k) / \mu$ for all
$k \in \mathbb{N}$. -/
theorem sizeBias_nat_pmf
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Xs : Ω' → ℝ}
    (_ : ∀ᵐ ω ∂P, X ω ∈ Set.range (Nat.cast : ℕ → ℝ))
    (_ : Integrable X P)
    (hμ_pos : 0 < ∫ ω, X ω ∂P)
    (hSB : IsSizeBias P X P' Xs) :
    let μ : ℝ := ∫ ω, X ω ∂P
    ∀ k : ℕ, P'.real {ω' | Xs ω' = k} = (k : ℝ) * P.real {ω | X ω = k} / μ :=
  fun k ↦ hSB.measureReal_eq_singleton hμ_pos (k : ℝ)

/-! ### Private calculus and $L^1$–$L^2$ helpers for Theorem 3.13 -/

private lemma normalWassersteinClass_taylor_bound
    {f : ℝ → ℝ} (hf : f ∈ normalWassersteinClass) :
    ∀ w w' : ℝ, |f w' - f w - (w' - w) * deriv f w| ≤ (w' - w) ^ 2 := by
  rcases hf with ⟨hf1, hf2, _, _, hf''_bdd⟩
  intro w w'
  let Φ : ℝ → ℝ := fun t ↦ f w' - f t - (w' - t) * deriv f t
  let Φ' : ℝ → ℝ := fun t ↦ -(w' - t) * deriv (deriv f) t
  let Ψ : ℝ → ℝ := fun t ↦ (w' - t) ^ 2
  let Ψ' : ℝ → ℝ := fun t ↦ -2 * (w' - t)
  have hΦ : ∀ t, HasDerivAt Φ (Φ' t) t := by
    intro t
    have hd_sub : HasDerivAt (fun s ↦ w' - s) (-1) t := (hasDerivAt_id' t).const_sub w'
    have hd0 : HasDerivAt (fun s ↦ f w' - f s) (-deriv f t) t :=
      (hf1 t).hasDerivAt.const_sub (f w')
    have hd1 :
        HasDerivAt (fun s ↦ (w' - s) * deriv f s)
          ((-1) * deriv f t + (w' - t) * deriv (deriv f) t) t :=
      hd_sub.fun_mul (hf2 t).hasDerivAt
    have hΦ'_eq :
        Φ' t = -deriv f t - ((-1) * deriv f t + (w' - t) * deriv (deriv f) t) := by
      dsimp only [Φ']
      ring
    rw [hΦ'_eq]
    exact hd0.fun_sub hd1
  have hΨ : ∀ t, HasDerivAt Ψ (Ψ' t) t := by
    intro t
    have hd_sub : HasDerivAt (fun s ↦ w' - s) (-1) t := (hasDerivAt_id' t).const_sub w'
    have hΨ'_eq : Ψ' t = ↑(2 : ℕ) * (w' - t) ^ (2 - 1) * (-1) := by
      dsimp only [Ψ']
      push_cast
      ring
    rw [hΨ'_eq]
    exact hd_sub.fun_pow 2
  have hΦ_cont : Continuous Φ := continuous_iff_continuousAt.mpr fun t ↦ (hΦ t).continuousAt
  have hΨ_cont : Continuous Ψ := continuous_iff_continuousAt.mpr fun t ↦ (hΨ t).continuousAt
  have hΦ_w' : Φ w' = 0 := by
    dsimp only [Φ]
    ring
  have hΨ_w' : Ψ w' = 0 := by
    dsimp only [Ψ]
    ring
  change |Φ w| ≤ (w' - w) ^ 2
  rcases lt_trichotomy w w' with hww' | hww' | hw'w
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hww' hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hc_ne : w' - c ≠ 0 := sub_ne_zero.mpr hc.2.ne'
    have hfac : (2 * Φ w - (w' - w) ^ 2 * deriv (deriv f) c) * (w' - c) = 0 := by
      have h0 : (Ψ w' - Ψ w) * Φ' c - (Φ w' - Φ w) * Ψ' c = 0 := sub_eq_zero.mpr hratio
      rw [hΦ_w', hΨ_w'] at h0
      dsimp only [Φ', Ψ', Ψ] at h0
      linarith [
        (by ring :
          (2 * Φ w - (w' - w) ^ 2 * deriv (deriv f) c) * (w' - c) =
            -((0 - (w' - w) ^ 2) * (-(w' - c) * deriv (deriv f) c) -
              (0 - Φ w) * (-2 * (w' - c))))]
    have hΦw : Φ w = (1 / 2) * (w' - w) ^ 2 * deriv (deriv f) c := by
      have hlin := (mul_eq_zero.mp hfac).resolve_right hc_ne
      linarith
    calc
      |Φ w| = (1 / 2) * (w' - w) ^ 2 * |deriv (deriv f) c| := by
        rw [hΦw, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
          abs_of_nonneg (sq_nonneg (w' - w))]
      _ ≤ (1 / 2) * (w' - w) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (hf''_bdd c) (by positivity)
      _ = (w' - w) ^ 2 := by ring
  · subst hww'
    rw [hΦ_w', sub_self, abs_zero]
    norm_num
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hw'w hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hc_ne : w' - c ≠ 0 := sub_ne_zero.mpr hc.1.ne
    have hfac : (2 * Φ w - (w' - w) ^ 2 * deriv (deriv f) c) * (w' - c) = 0 := by
      have h0 : (Ψ w - Ψ w') * Φ' c - (Φ w - Φ w') * Ψ' c = 0 := sub_eq_zero.mpr hratio
      rw [hΦ_w', hΨ_w'] at h0
      dsimp only [Φ', Ψ', Ψ] at h0
      linarith [
        (by ring :
          (2 * Φ w - (w' - w) ^ 2 * deriv (deriv f) c) * (w' - c) =
            ((w' - w) ^ 2 - 0) * (-(w' - c) * deriv (deriv f) c) -
              (Φ w - 0) * (-2 * (w' - c)))]
    have hΦw : Φ w = (1 / 2) * (w' - w) ^ 2 * deriv (deriv f) c := by
      have hlin := (mul_eq_zero.mp hfac).resolve_right hc_ne
      linarith
    calc
      |Φ w| = (1 / 2) * (w' - w) ^ 2 * |deriv (deriv f) c| := by
        rw [hΦw, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
          abs_of_nonneg (sq_nonneg (w' - w))]
      _ ≤ (1 / 2) * (w' - w) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (hf''_bdd c) (by positivity)
      _ = (w' - w) ^ 2 := by ring

private lemma integral_abs_sub_le_sqrt_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg2 : MemLp g 2 P) :
    ∫ ω, |g ω - ∫ x, g x ∂P| ∂P ≤ Real.sqrt (ProbabilityTheory.variance g P) := by
  set m : ℝ := ∫ x, g x ∂P
  set h : Ω → ℝ := fun ω ↦ |g ω - m|
  set c : ℝ := ∫ ω, h ω ∂P
  have hg_int : Integrable g P := hg2.integrable one_le_two
  have hh_int : Integrable h P := by
    dsimp only [h]
    simpa only [Real.norm_eq_abs] using (hg_int.sub' (integrable_const m)).norm
  have hsq_int : Integrable (fun ω ↦ (g ω - m) ^ 2) P :=
    (hg2.sub (memLp_const m)).integrable_sq
  have hnonneg : 0 ≤ ∫ ω, (h ω - c) ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg (h ω - c)
  have hexp : (fun ω ↦ (h ω - c) ^ 2) =
      fun ω ↦ ((g ω - m) ^ 2 - 2 * c * h ω) + c ^ 2 := by
    ext ω
    have habs : h ω ^ 2 = (g ω - m) ^ 2 := sq_abs (g ω - m)
    dsimp only [h] at habs ⊢
    linarith [
      (by ring :
        (|g ω - m| - c) ^ 2 - (((g ω - m) ^ 2 - 2 * c * |g ω - m|) + c ^ 2) =
          |g ω - m| ^ 2 - (g ω - m) ^ 2)]
  have hcalc : ∫ ω, (h ω - c) ^ 2 ∂P = ProbabilityTheory.variance g P - c ^ 2 := by
    rw [hexp, integral_add (hsq_int.sub' (hh_int.const_mul (2 * c))) (integrable_const (c ^ 2)),
      integral_sub hsq_int (hh_int.const_mul (2 * c)), integral_const_mul (2 * c) h,
      integral_const (c ^ 2), probReal_univ, one_smul]
    dsimp only [c, m]
    rw [← ProbabilityTheory.variance_eq_integral hg_int.aemeasurable]
    ring
  exact Real.le_sqrt_of_sq_le (by linarith [hnonneg, hcalc])

/-! ### Theorem 3.13: Wasserstein normal approximation via size-bias coupling -/

/-- **Theorem 3.13** (`\label{thm71}`, `SteinIntro.tex:1255-1261`): for measurable $X \ge 0$ a.s.
in $L^2(P)$ with $\sigma^2 = \operatorname{Var}(X) > 0$, $\mu = \mathbb{E}[X]$, standardized
$W = (X - \mu)/\sigma$, size-bias coupling $X^s$ on the same probability space, and standard normal
$Z \sim \mathcal{N}(0, 1)$,
$$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\mu}{\sigma^2}\sqrt{\frac{2}{\pi}}\sqrt{\operatorname{Var}(\mathbb{E}[X^s - X \mid X])} +
\frac{\mu}{\sigma^3}\mathbb{E}[(X^s - X)^2]$$
in `ℝ≥0∞` (`ProbabilityTheory.evariance`, `lintegral`). -/
theorem sizeBias_wassersteinDist_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X Xs : Ω → ℝ} {Z : Ω' → ℝ}
    (hX_meas : Measurable X) (hX_nn : 0 ≤ᵐ[P] X)
    (hX2 : MemLp X 2 P) (hVar : 0 < ProbabilityTheory.variance X P)
    (hSB : IsSizeBias P X P Xs)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    let W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) *
          ProbabilityTheory.evariance
            (P[fun ω ↦ Xs ω - X ω | MeasurableSpace.comap X inferInstance]) P ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (μ / σ ^ 3) * ∫⁻ ω, ENNReal.ofReal ((Xs ω - X ω) ^ 2) ∂P := by
  dsimp only
  set μ : ℝ := ∫ ω, X ω ∂P
  set σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
  set W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
  set D : Ω → ℝ := fun ω ↦ Xs ω - X ω
  set Q : Ω → ℝ := P[D | MeasurableSpace.comap X inferInstance]
  set V : ℝ≥0∞ := ProbabilityTheory.evariance Q P
  set M2 : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P
  have hX_int : Integrable X P := hX2.integrable one_le_two
  have hμ_pos : 0 < μ := pos_integral_of_nonneg_of_variance_pos P hX_nn hX_int hVar
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  have hσ_sq : σ ^ 2 = ProbabilityTheory.variance X P := by
    rw [sq, Real.mul_self_sqrt hVar.le]
  rcases eq_or_ne M2 ⊤ with hM2_top | hM2_ne_top
  · have hc_ne : ENNReal.ofReal (μ / σ ^ 3) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    rw [hM2_top, ENNReal.mul_top hc_ne, add_top]
    exact le_top
  have hXsq_eq : (fun ω ↦ X ω * id (X ω)) = fun ω ↦ X ω ^ 2 := funext fun ω ↦ by
    rw [id_eq, sq]
  have hXid_int : Integrable (fun ω ↦ X ω * id (X ω)) P := by
    rw [hXsq_eq]
    exact hX2.integrable_sq
  have hXs_int : Integrable Xs P :=
    hSB.integrable_comp_of_pos_mean hμ_pos measurable_id hXid_int
  have hSB_id : ∫ ω, X ω ^ 2 ∂P = μ * ∫ ω, Xs ω ∂P := by
    rw [← hXsq_eq]
    exact hSB.2.2.2 id measurable_id hXid_int
  have hVar_sub : σ ^ 2 = (∫ ω, X ω ^ 2 ∂P) - μ ^ 2 := by
    rw [hσ_sq, ProbabilityTheory.variance_eq_sub hX2]
    rfl
  have hD_int : Integrable D P := hXs_int.sub' hX_int
  have hD_mean : ∫ ω, D ω ∂P = σ ^ 2 / μ := by
    have hmul : μ * ∫ ω, D ω ∂P = μ * (σ ^ 2 / μ) := by
      dsimp only [D]
      rw [integral_sub hXs_int hX_int, mul_sub, ← hSB_id, ← sq, mul_div_cancel₀ _ hμ_pos.ne']
      linarith [hVar_sub]
    exact mul_left_cancel₀ hμ_pos.ne' hmul
  have hD2_nn : 0 ≤ᵐ[P] fun ω ↦ D ω ^ 2 := Eventually.of_forall fun _ ↦ sq_nonneg _
  have hD2_int : Integrable (fun ω ↦ D ω ^ 2) P :=
    ⟨(continuous_pow 2).comp_aestronglyMeasurable hD_int.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hD2_nn).mpr hM2_ne_top.lt_top⟩
  have hM2_eq : M2 = ENNReal.ofReal (∫ ω, D ω ^ 2 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hD2_int hD2_nn).symm
  have hD2 : MemLp D 2 P :=
    (memLp_two_iff_integrable_sq hD_int.aestronglyMeasurable).mpr hD2_int
  have hm := hX_meas.comap_le
  have hQ_int : Integrable Q P := integrable_condExp
  have hQ2 : MemLp Q 2 P :=
    (eLpNorm_condExp_le_eLpNorm (μ := P)
      (m := MeasurableSpace.comap X inferInstance) D one_le_two).trans_lt hD2.eLpNorm_lt_top
  have hQ_mean : ∫ ω, Q ω ∂P = σ ^ 2 / μ := by
    dsimp only [Q]
    rw [integral_condExp hm, hD_mean]
  have hV_eq : V ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q P)) := by
    dsimp only [V]
    rw [← ProbabilityTheory.ofReal_variance hQ2,
      ENNReal.ofReal_rpow_of_nonneg (ProbabilityTheory.variance_nonneg Q P) (by positivity),
      ← Real.sqrt_eq_rpow]
  have hAff_meas : Measurable (fun x : ℝ ↦ (x - μ) / σ) :=
    ((continuous_id.sub continuous_const).div₀ continuous_const
      (fun _ ↦ hσ_pos.ne')).measurable
  have hW_meas : Measurable W := hAff_meas.comp hX_meas
  refine (wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P'
    hW_meas.aemeasurable hZ hZ_law).trans ?_
  refine iSup₂_le fun f hf ↦ ?_
  have hTaylor := normalWassersteinClass_taylor_bound hf
  rcases hf with ⟨hf1, hf2, hf_bdd, hf'_bdd, _⟩
  let Ws : Ω → ℝ := fun ω ↦ (Xs ω - μ) / σ
  have hf_meas : Measurable f := hf1.continuous.measurable
  have hfW_asm : AEStronglyMeasurable (fun ω ↦ f (W ω)) P :=
    (hf_meas.comp hW_meas).aestronglyMeasurable
  have hfW_int : Integrable (fun ω ↦ f (W ω)) P :=
    (integrable_const (2 : ℝ)).mono' hfW_asm
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hf_bdd (W ω))
  have hXfW_int : Integrable (fun ω ↦ X ω * f (W ω)) P :=
    (hX_int.norm.mul_const 2).mono' (hX_int.aestronglyMeasurable.mul hfW_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg (X ω)))
  obtain ⟨hfWs_int0, hSB_W0⟩ :=
    sizeBias_stein_identity P hX_nn hX2 hVar hSB hf_meas hXfW_int hfW_int
  have hfWs_int : Integrable (fun ω ↦ f (Ws ω)) P := hfWs_int0
  have hSB_W : ∫ ω, W ω * f (W ω) ∂P =
      μ / σ * ((∫ ω, f (Ws ω) ∂P) - ∫ ω, f (W ω) ∂P) := hSB_W0
  have hWfW_eq : (fun ω ↦ W ω * f (W ω)) =
      fun ω ↦ σ⁻¹ * (X ω * f (W ω) - μ * f (W ω)) := funext fun ω ↦ by
    dsimp only [W]
    rw [div_eq_mul_inv]
    ring
  have hWfW_int : Integrable (fun ω ↦ W ω * f (W ω)) P := by
    rw [hWfW_eq]
    exact (hXfW_int.sub' (hfW_int.const_mul μ)).const_mul σ⁻¹
  set B₁ : ℝ := Real.sqrt (2 / Real.pi)
  have hf'W_sm :
      StronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω ↦ deriv f (W ω)) :=
    ((hf2.continuous.measurable.comp hAff_meas).comp
      (comap_measurable (m := inferInstance) X)).stronglyMeasurable
  have hf'W_asm : AEStronglyMeasurable (fun ω ↦ deriv f (W ω)) P :=
    (hf2.continuous.measurable.comp hW_meas).aestronglyMeasurable
  have hf'W_int : Integrable (fun ω ↦ deriv f (W ω)) P :=
    (integrable_const B₁).mono' hf'W_asm
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hf'_bdd (W ω))
  have hDf'W_int : Integrable (fun ω ↦ D ω * deriv f (W ω)) P :=
    (hD_int.norm.mul_const B₁).mono' (hD_int.aestronglyMeasurable.mul hf'W_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg (D ω)))
  have hQf'W_int : Integrable (fun ω ↦ Q ω * deriv f (W ω)) P :=
    (hQ_int.norm.mul_const B₁).mono' (hQ_int.aestronglyMeasurable.mul hf'W_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg (Q ω)))
  have hIntDf'W : ∫ ω, D ω * deriv f (W ω) ∂P = ∫ ω, Q ω * deriv f (W ω) ∂P := calc
    ∫ ω, D ω * deriv f (W ω) ∂P
      = ∫ ω, (D * fun ω ↦ deriv f (W ω)) ω ∂P := rfl
    _ = ∫ ω, P[D * (fun ω ↦ deriv f (W ω)) |
          MeasurableSpace.comap X inferInstance] ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, Q ω * deriv f (W ω) ∂P :=
        integral_congr_ae
          (condExp_mul_of_stronglyMeasurable_right hf'W_sm hDf'W_int hD_int)
  have hDiffW_eq : ∀ ω, Ws ω - W ω = D ω / σ := fun ω ↦ by
    dsimp only [Ws, W, D]
    ring
  have hLin_eq : (fun ω ↦ (Ws ω - W ω) * deriv f (W ω)) =
      fun ω ↦ σ⁻¹ * (D ω * deriv f (W ω)) := funext fun ω ↦ by
    rw [hDiffW_eq ω, div_eq_mul_inv]
    ring
  have hLin_int : Integrable (fun ω ↦ (Ws ω - W ω) * deriv f (W ω)) P := by
    rw [hLin_eq]
    exact hDf'W_int.const_mul σ⁻¹
  set R : Ω → ℝ := fun ω ↦ f (Ws ω) - f (W ω) - (Ws ω - W ω) * deriv f (W ω)
  have hR_int : Integrable R P := (hfWs_int.sub' hfW_int).sub' hLin_int
  have hDiffF_int :
      (∫ ω, f (Ws ω) ∂P) - ∫ ω, f (W ω) ∂P =
        σ⁻¹ * ∫ ω, Q ω * deriv f (W ω) ∂P + ∫ ω, R ω ∂P := by
    have hAdd : (fun ω ↦ f (Ws ω) - f (W ω)) =
        fun ω ↦ (Ws ω - W ω) * deriv f (W ω) + R ω := funext fun ω ↦ by
      dsimp only [R]
      ring
    rw [← integral_sub hfWs_int hfW_int, hAdd, integral_add hLin_int hR_int, hLin_eq,
      integral_const_mul σ⁻¹ (fun ω ↦ D ω * deriv f (W ω)), hIntDf'W]
  set S : Ω → ℝ := fun ω ↦ (σ ^ 2 / μ - Q ω) * deriv f (W ω)
  have hS_eq : S = fun ω ↦ (σ ^ 2 / μ) * deriv f (W ω) - Q ω * deriv f (W ω) :=
    funext fun _ ↦ by ring
  have hS_int : Integrable S P := by
    rw [hS_eq]
    exact (hf'W_int.const_mul (σ ^ 2 / μ)).sub' hQf'W_int
  have hStein_eq :
      ∫ ω, normalSteinOp f (W ω) ∂P =
        (μ / σ ^ 2) * ∫ ω, S ω ∂P - (μ / σ) * ∫ ω, R ω ∂P := by
    have hOp : ∫ ω, normalSteinOp f (W ω) ∂P =
        ∫ ω, deriv f (W ω) ∂P - ∫ ω, W ω * f (W ω) ∂P :=
      integral_sub hf'W_int hWfW_int
    have hIntS : ∫ ω, S ω ∂P =
        (σ ^ 2 / μ) * ∫ ω, deriv f (W ω) ∂P - ∫ ω, Q ω * deriv f (W ω) ∂P := by
      rw [hS_eq, integral_sub (hf'W_int.const_mul (σ ^ 2 / μ)) hQf'W_int,
        integral_const_mul (σ ^ 2 / μ) (fun ω ↦ deriv f (W ω))]
    have hCancel : (μ / σ ^ 2) * (σ ^ 2 / μ) = 1 := by
      rw [div_mul_div_comm, mul_comm μ (σ ^ 2),
        div_self (mul_ne_zero (pow_ne_zero 2 hσ_pos.ne') hμ_pos.ne')]
    have hDivSq : (μ / σ) * σ⁻¹ = μ / σ ^ 2 := by
      refine mul_right_cancel₀ (pow_ne_zero 2 hσ_pos.ne') ?_
      have hL : (μ / σ) * σ⁻¹ * σ ^ 2 = (μ / σ * σ) * (σ⁻¹ * σ) := by ring
      rw [hL, div_mul_cancel₀ μ hσ_pos.ne', inv_mul_cancel₀ hσ_pos.ne',
        div_mul_cancel₀ μ (pow_ne_zero 2 hσ_pos.ne'), mul_one]
    rw [hOp, hSB_W, hDiffF_int, hIntS]
    calc
      (∫ ω, deriv f (W ω) ∂P) -
          (μ / σ) * (σ⁻¹ * ∫ ω, Q ω * deriv f (W ω) ∂P + ∫ ω, R ω ∂P)
        = 1 * (∫ ω, deriv f (W ω) ∂P) -
            ((μ / σ) * σ⁻¹) * (∫ ω, Q ω * deriv f (W ω) ∂P) -
            (μ / σ) * ∫ ω, R ω ∂P := by ring
      _ = ((μ / σ ^ 2) * (σ ^ 2 / μ)) * (∫ ω, deriv f (W ω) ∂P) -
            (μ / σ ^ 2) * (∫ ω, Q ω * deriv f (W ω) ∂P) -
            (μ / σ) * ∫ ω, R ω ∂P := by rw [hCancel, hDivSq]
      _ = (μ / σ ^ 2) *
            ((σ ^ 2 / μ) * ∫ ω, deriv f (W ω) ∂P - ∫ ω, Q ω * deriv f (W ω) ∂P) -
            (μ / σ) * ∫ ω, R ω ∂P := by ring
  have hS_bound :
      |∫ ω, S ω ∂P| ≤ B₁ * Real.sqrt (ProbabilityTheory.variance Q P) := by
    have h1 : |∫ ω, S ω ∂P| ≤ ∫ ω, |S ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm S
    have hS_abs_int : Integrable (fun ω ↦ |S ω|) P := by
      simpa only [Real.norm_eq_abs] using hS_int.norm
    have hQsub_abs_int : Integrable (fun ω ↦ |Q ω - ∫ x, Q x ∂P|) P := by
      simpa only [Real.norm_eq_abs] using (hQ_int.sub' (integrable_const (∫ x, Q x ∂P))).norm
    have h2 : ∫ ω, |S ω| ∂P ≤ ∫ ω, B₁ * |Q ω - ∫ x, Q x ∂P| ∂P := by
      refine integral_mono hS_abs_int (hQsub_abs_int.const_mul B₁) fun ω ↦ ?_
      dsimp only [S]
      rw [abs_mul, ← hQ_mean, abs_sub_comm (∫ x, Q x ∂P) (Q ω), mul_comm B₁]
      exact mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg _)
    rw [integral_const_mul B₁ (fun ω ↦ |Q ω - ∫ x, Q x ∂P|)] at h2
    have h3 : B₁ * ∫ ω, |Q ω - ∫ x, Q x ∂P| ∂P ≤
        B₁ * Real.sqrt (ProbabilityTheory.variance Q P) :=
      mul_le_mul_of_nonneg_left (integral_abs_sub_le_sqrt_variance P hQ2) (Real.sqrt_nonneg _)
    exact h1.trans (h2.trans h3)
  have hR_bound : |∫ ω, R ω ∂P| ≤ (1 / σ ^ 2) * ∫ ω, D ω ^ 2 ∂P := by
    have h1 : |∫ ω, R ω ∂P| ≤ ∫ ω, |R ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    have hR_abs_int : Integrable (fun ω ↦ |R ω|) P := by
      simpa only [Real.norm_eq_abs] using hR_int.norm
    have h2 : ∫ ω, |R ω| ∂P ≤ ∫ ω, (1 / σ ^ 2) * D ω ^ 2 ∂P := by
      refine integral_mono hR_abs_int (hD2_int.const_mul (1 / σ ^ 2)) fun ω ↦ ?_
      have hT := hTaylor (W ω) (Ws ω)
      have hSq : (Ws ω - W ω) ^ 2 = (1 / σ ^ 2) * D ω ^ 2 := by
        rw [hDiffW_eq ω, div_eq_mul_inv]
        ring
      exact hT.trans_eq hSq
    rw [integral_const_mul (1 / σ ^ 2) (fun ω ↦ D ω ^ 2)] at h2
    exact h1.trans h2
  have hPow3 : (μ / σ) * (1 / σ ^ 2) = μ / σ ^ 3 := by
    have hσ3 : σ ^ 3 ≠ 0 := pow_ne_zero 3 hσ_pos.ne'
    refine mul_right_cancel₀ hσ3 ?_
    have hL : (μ / σ) * (1 / σ ^ 2) * σ ^ 3 = (μ / σ * σ) * (1 / σ ^ 2 * σ ^ 2) := by ring
    rw [hL, div_mul_cancel₀ μ hσ_pos.ne', div_mul_cancel₀ 1 (pow_ne_zero 2 hσ_pos.ne'),
      div_mul_cancel₀ μ hσ3, mul_one]
  have hReal :
      |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        (μ / σ ^ 2 * B₁) * Real.sqrt (ProbabilityTheory.variance Q P) +
          (μ / σ ^ 3) * ∫ ω, D ω ^ 2 ∂P := by
    have hTri :
        |(μ / σ ^ 2) * ∫ ω, S ω ∂P - (μ / σ) * ∫ ω, R ω ∂P| ≤
          (μ / σ ^ 2) * |∫ ω, S ω ∂P| + (μ / σ) * |∫ ω, R ω ∂P| := by
      have hSubLe :
          |(μ / σ ^ 2) * ∫ ω, S ω ∂P - (μ / σ) * ∫ ω, R ω ∂P| ≤
            |(μ / σ ^ 2) * ∫ ω, S ω ∂P| + |(μ / σ) * ∫ ω, R ω ∂P| :=
        abs_sub _ _
      rwa [abs_mul, abs_of_pos (by positivity : 0 < μ / σ ^ 2),
        abs_mul, abs_of_pos (by positivity : 0 < μ / σ)] at hSubLe
    have h1 : (μ / σ ^ 2) * |∫ ω, S ω ∂P| ≤
        (μ / σ ^ 2 * B₁) * Real.sqrt (ProbabilityTheory.variance Q P) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hS_bound (by positivity)
    have h2 : (μ / σ) * |∫ ω, R ω ∂P| ≤ (μ / σ ^ 3) * ∫ ω, D ω ^ 2 ∂P := by
      calc
        (μ / σ) * |∫ ω, R ω ∂P|
          ≤ (μ / σ) * ((1 / σ ^ 2) * ∫ ω, D ω ^ 2 ∂P) :=
            mul_le_mul_of_nonneg_left hR_bound (by positivity)
        _ = ((μ / σ) * (1 / σ ^ 2)) * ∫ ω, D ω ^ 2 ∂P := by ring
        _ = (μ / σ ^ 3) * ∫ ω, D ω ^ 2 ∂P := by rw [hPow3]
    rw [hStein_eq]
    exact hTri.trans (add_le_add h1 h2)
  have hC1_nn : 0 ≤ μ / σ ^ 2 * B₁ := by positivity
  have hSqrt_nn : 0 ≤ Real.sqrt (ProbabilityTheory.variance Q P) := Real.sqrt_nonneg _
  have hC2_nn : 0 ≤ μ / σ ^ 3 := by positivity
  have hIntD2_nn : 0 ≤ ∫ ω, D ω ^ 2 ∂P := integral_nonneg fun _ ↦ sq_nonneg _
  calc
    ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|
      ≤ ENNReal.ofReal
          ((μ / σ ^ 2 * B₁) * Real.sqrt (ProbabilityTheory.variance Q P) +
            (μ / σ ^ 3) * ∫ ω, D ω ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal hReal
    _ = ENNReal.ofReal ((μ / σ ^ 2 * B₁) * Real.sqrt (ProbabilityTheory.variance Q P)) +
          ENNReal.ofReal ((μ / σ ^ 3) * ∫ ω, D ω ^ 2 ∂P) :=
        ENNReal.ofReal_add (mul_nonneg hC1_nn hSqrt_nn) (mul_nonneg hC2_nn hIntD2_nn)
    _ = ENNReal.ofReal (μ / σ ^ 2 * B₁) * V ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (μ / σ ^ 3) * M2 := by
        rw [ENNReal.ofReal_mul hC1_nn, ENNReal.ofReal_mul hC2_nn, ← hV_eq, ← hM2_eq]

end SteinMethod
