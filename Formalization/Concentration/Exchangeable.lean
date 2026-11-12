/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.Basic
import Formalization.Exchangeable.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Exchangeable-Pair & Stein-Pair Concentration (`Formalization.Concentration.Exchangeable`)

Proves the core exchangeable-pair and Stein-pair concentration inequalities of Section 7
(`SteinIntro.tex:3476-3683`):

* `condVar_linear_bound_nonneg` (**Remark 7.3**, `SteinIntro.tex:3490-3495`).
* `exchangeable_antisymm_tail_bound` (**Theorem 7.5**, `\label{thm211b}`,
  `SteinIntro.tex:3658-3676`, including boundary conjuncts at $C = 0$).
* `steinPair_reduction_to_antisymm` (Section 7 prose reduction from Theorem 7.5 to Theorem 7.2,
  `SteinIntro.tex:3677-3681`).
* `steinPair_tail_bounds_of_pos` (general $a > 0$ library version of **Theorem 7.2**,
  `\label{thm211a}`, `SteinIntro.tex:3479-3489`; ruling `D7`) and `steinPair_tail_bounds`
  (**Theorem 7.2** for `IsSteinPair`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Remark 7.3 -/

/-- **Remark 7.3** (`SteinIntro.tex:3490-3495`): condition `(7.1)`
($\mathbb{E}[(W' - W)^2 \mid \mathcal{F}] / (2a) \le B W + C$ with $a > 0$) forces
$B W + C \ge 0$ a.s., hence $W \ge -C / B$ a.s. whenever $B > 0$. -/
theorem condVar_linear_bound_nonneg
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω)
    {a B C : ℝ} {W W' : Ω → ℝ} {m : MeasurableSpace Ω}
    (ha : 0 < a) (_hm : m ≤ m₀)
    (hCond : ∀ᵐ ω ∂P, P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a) ≤ B * W ω + C) :
    (∀ᵐ ω ∂P, 0 ≤ B * W ω + C) ∧ (0 < B → ∀ᵐ ω ∂P, -C / B ≤ W ω) := by
  have hnn : 0 ≤ᵐ[P] P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] :=
    condExp_nonneg (Eventually.of_forall fun ω' ↦ sq_nonneg (W' ω' - W ω'))
  have hBWC : ∀ᵐ ω ∂P, 0 ≤ B * W ω + C := by
    filter_upwards [hnn, hCond] with ω h1 h2
    exact (div_nonneg h1 (by positivity)).trans h2
  refine ⟨hBWC, fun hB ↦ ?_⟩
  filter_upwards [hBWC] with ω hω
  exact (div_le_iff₀ hB).mpr (by linarith)

/-! ### Section 2: Theorem 7.5 (Exchangeable Antisymmetric Concentration) -/

/-- Monotone exponential-truncation helper: if $U \ge 0$ is integrable and
$c \cdot \mathbb{E}[U \mid X] \le V$ a.s. with $V \ge 0$ a.s., $c > 0$, and $V e^{\theta f(X)}$
integrable, then $U e^{\theta f(X)}$ is integrable and
$c \int U e^{\theta f(X)} \le \int V e^{\theta f(X)}$. -/
private lemma integrable_and_integral_mul_exp_le_of_condExp_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → α} {f : α → ℝ} {U V : Ω → ℝ} {c θ : ℝ}
    (hX : Measurable X) (hf : Measurable f)
    (hc : 0 < c) (hU_int : Integrable U P) (hU_nn : ∀ ω, 0 ≤ U ω)
    (hVE_int : Integrable (fun ω ↦ V ω * Real.exp (θ * f (X ω))) P)
    (hV_nn : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hCond : ∀ᵐ ω ∂P, c * P[U | MeasurableSpace.comap X inferInstance] ω ≤ V ω) :
    Integrable (fun ω ↦ U ω * Real.exp (θ * f (X ω))) P ∧
      c * ∫ ω, U ω * Real.exp (θ * f (X ω)) ∂P ≤
        ∫ ω, V ω * Real.exp (θ * f (X ω)) ∂P := by
  let Y : Ω → ℝ := fun ω ↦ f (X ω)
  have hmX := hX.comap_le
  have hY_meas : Measurable Y := hf.comp hX
  let eM : ℕ → ℝ → ℝ := fun M y ↦ min (Real.exp (θ * y)) (M : ℝ)
  have heM_meas : ∀ M : ℕ, Measurable (eM M) := fun M ↦
    continuous_min.measurable.comp
      ((Real.continuous_exp.comp (continuous_id.const_mul θ)).measurable.prodMk measurable_const)
  have heM_nn : ∀ (M : ℕ) (y : ℝ), 0 ≤ eM M y :=
    fun M y ↦ le_min (Real.exp_pos _).le (Nat.cast_nonneg M)
  have hSup_min : ∀ r : ℝ, (⨆ M : ℕ, ENNReal.ofReal (min r (M : ℝ))) = ENNReal.ofReal r := by
    intro r
    refine le_antisymm (iSup_le fun M ↦ ENNReal.ofReal_le_ofReal (min_le_left r (M : ℝ))) ?_
    obtain ⟨M, hM_gt⟩ := exists_nat_gt r
    exact le_trans (by rw [min_eq_left hM_gt.le])
      (le_iSup (fun k : ℕ ↦ ENNReal.ofReal (min r (k : ℝ))) M)
  have hM_step : ∀ M : ℕ,
      Integrable (fun ω ↦ eM M (Y ω) * U ω) P ∧
        c * ∫ ω, eM M (Y ω) * U ω ∂P ≤ ∫ ω, V ω * Real.exp (θ * Y ω) ∂P := by
    intro M
    have heMY_sm : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω ↦ eM M (Y ω)) :=
      (((heM_meas M).comp hf).comp (comap_measurable X)).stronglyMeasurable
    have heMY_asm : AEStronglyMeasurable (fun ω ↦ eM M (Y ω)) P :=
      ((heM_meas M).comp hY_meas).aestronglyMeasurable
    have heMU_int : Integrable (fun ω ↦ eM M (Y ω) * U ω) P := by
      refine (hU_int.const_mul (M : ℝ)).mono' (heMY_asm.mul hU_int.aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (heM_nn M (Y ω)) (hU_nn ω))]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (hU_nn ω)
    have hpull : (fun ω ↦ eM M (Y ω) * P[U | MeasurableSpace.comap X inferInstance] ω) =ᵐ[P]
        P[fun ω' ↦ eM M (Y ω') * U ω' | MeasurableSpace.comap X inferInstance] :=
      (condExp_mul_of_stronglyMeasurable_left heMY_sm heMU_int hU_int).symm
    have heMCond_int : Integrable
        (fun ω ↦ eM M (Y ω) * (c * P[U | MeasurableSpace.comap X inferInstance] ω)) P := by
      have h1 : (fun ω ↦ eM M (Y ω) * (c * P[U | MeasurableSpace.comap X inferInstance] ω)) =
          fun ω ↦ c * (eM M (Y ω) * P[U | MeasurableSpace.comap X inferInstance] ω) := by
        ext ω; ring
      rw [h1]
      exact ((integrable_congr hpull.symm).mp integrable_condExp).const_mul c
    have hle : c * ∫ ω, eM M (Y ω) * U ω ∂P ≤ ∫ ω, V ω * Real.exp (θ * Y ω) ∂P := calc
      c * ∫ ω, eM M (Y ω) * U ω ∂P
          = c * ∫ ω, P[fun ω' ↦ eM M (Y ω') * U ω' |
              MeasurableSpace.comap X inferInstance] ω ∂P := by rw [integral_condExp hmX]
      _ = c * ∫ ω, eM M (Y ω) * P[U | MeasurableSpace.comap X inferInstance] ω ∂P := by
            rw [integral_congr_ae hpull.symm]
      _ = ∫ ω, eM M (Y ω) * (c * P[U | MeasurableSpace.comap X inferInstance] ω) ∂P := by
            rw [← integral_const_mul]
            exact integral_congr_ae (Eventually.of_forall fun _ ↦ by ring)
      _ ≤ ∫ ω, V ω * Real.exp (θ * Y ω) ∂P := by
            refine integral_mono_ae heMCond_int hVE_int ?_
            filter_upwards [hCond, hV_nn] with ω h1 h2
            calc eM M (Y ω) * (c * P[U | MeasurableSpace.comap X inferInstance] ω)
                ≤ eM M (Y ω) * V ω := mul_le_mul_of_nonneg_left h1 (heM_nn M (Y ω))
              _ ≤ Real.exp (θ * Y ω) * V ω := mul_le_mul_of_nonneg_right (min_le_left _ _) h2
              _ = V ω * Real.exp (θ * Y ω) := mul_comm _ _
    exact ⟨heMU_int, hle⟩
  have hLIntM : ∀ M : ℕ,
      ∫⁻ ω, ENNReal.ofReal (eM M (Y ω) * U ω) ∂P ≤
        ENNReal.ofReal (c⁻¹ * ∫ ω, V ω * Real.exp (θ * Y ω) ∂P) := by
    intro M
    rw [← ofReal_integral_eq_lintegral_ofReal (hM_step M).1
      (Eventually.of_forall fun ω ↦ mul_nonneg (heM_nn M (Y ω)) (hU_nn ω))]
    refine ENNReal.ofReal_le_ofReal ?_
    exact (le_inv_mul_iff₀ hc).mpr (hM_step M).2
  have hsup_pt : ∀ ω, ENNReal.ofReal ‖U ω * Real.exp (θ * Y ω)‖ =
      ⨆ M : ℕ, ENNReal.ofReal (eM M (Y ω) * U ω) := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hU_nn ω) (Real.exp_pos _).le)]
    by_cases hU0 : U ω = 0
    · simp [hU0]
    · rw [mul_comm (U ω), ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← hSup_min (Real.exp (θ * Y ω)), ENNReal.iSup_mul]
      exact iSup_congr fun M ↦ (ENNReal.ofReal_mul (heM_nn M (Y ω))).symm
  have hSup_eq : ∫⁻ ω, ENNReal.ofReal ‖U ω * Real.exp (θ * Y ω)‖ ∂P =
      ⨆ M : ℕ, ∫⁻ ω, ENNReal.ofReal (eM M (Y ω) * U ω) ∂P := by
    rw [lintegral_congr hsup_pt]
    exact lintegral_iSup'
      (fun M ↦ (((heM_meas M).comp hY_meas).aemeasurable.mul hU_int.aemeasurable).ennreal_ofReal)
      (Eventually.of_forall fun ω _ _ h12 ↦ ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right
          (le_min (min_le_left _ _) ((min_le_right _ _).trans (Nat.cast_le.mpr h12))) (hU_nn ω)))
  have hLInt_le : ∫⁻ ω, ENNReal.ofReal ‖U ω * Real.exp (θ * Y ω)‖ ∂P ≤
      ENNReal.ofReal (c⁻¹ * ∫ ω, V ω * Real.exp (θ * Y ω) ∂P) :=
    hSup_eq.trans_le (iSup_le hLIntM)
  have hExp_meas : Measurable (fun ω ↦ Real.exp (θ * Y ω)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul hY_meas)
  have hUE_int : Integrable (fun ω ↦ U ω * Real.exp (θ * Y ω)) P :=
    ⟨hU_int.aestronglyMeasurable.mul hExp_meas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_norm _).mpr (hLInt_le.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hUE_int, ?_⟩
  have hRHS_nn : 0 ≤ c⁻¹ * ∫ ω, V ω * Real.exp (θ * Y ω) ∂P :=
    mul_nonneg (inv_nonneg.mpr hc.le)
      (integral_nonneg_of_ae (hV_nn.mono fun _ hω ↦ mul_nonneg hω (Real.exp_pos _).le))
  have hofReal : ENNReal.ofReal (∫ ω, U ω * Real.exp (θ * Y ω) ∂P) ≤
      ENNReal.ofReal (c⁻¹ * ∫ ω, V ω * Real.exp (θ * Y ω) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hUE_int
      (Eventually.of_forall fun ω ↦ mul_nonneg (hU_nn ω) (Real.exp_pos _).le)]
    refine (lintegral_congr fun ω ↦ ?_).trans_le hLInt_le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hU_nn ω) (Real.exp_pos _).le)]
  exact (le_inv_mul_iff₀ hc).mp ((ENNReal.ofReal_le_ofReal_iff hRHS_nn).mp hofReal)

/-- General library version of **Theorem 7.5** (`\label{thm211b}`, `SteinIntro.tex:3658-3676`,
including boundary cases at $C = 0$): on any measurable space $\alpha$, if $(X, X')$ is an
exchangeable pair, $F : \alpha \times \alpha \to \mathbb{R}$ is measurable and antisymmetric,
$f(X) = \mathbb{E}[F(X, X') \mid X]$ a.s., $\mathbb{E}[e^{\theta f(X)}|F(X, X')|] < \infty$ for all
$\theta \in \mathbb{R}$, and
$\frac{1}{2}\mathbb{E}[|(f(X) - f(X')) F(X, X')| \mid X] \le B f(X) + C$ a.s. with $B, C \ge 0$,
then for every $t > 0$ both $\mathbb{P}(f(X) \ge t)$ and $\mathbb{P}(f(X) > t)$ are bounded by
$\exp(-t^2 / (2 C + 2 B t))$, $\mathbb{P}(f(X) \le -t)$ is bounded by $\exp(-t^2 / (2 C))$, and
when $C = 0$, $f(X) = 0$ a.s. so all three tail probabilities vanish (`F1`). -/
theorem exchangeable_antisymm_tail_bound
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X X' : Ω → α} {F : α × α → ℝ} {f : α → ℝ} {B C : ℝ}
    (hX : Measurable X)
    (hExch : IsExchangeablePair P X X')
    (hF : Measurable F)
    (hAnti : ∀ x x' : α, F (x, x') = -F (x', x))
    (hf : Measurable f)
    (hf_eq : (fun ω ↦ f (X ω)) =ᵐ[P]
      P[fun ω ↦ F (X ω, X' ω) | MeasurableSpace.comap X inferInstance])
    (hInt : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * f (X ω)) * |F (X ω, X' ω)|) P)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hCond : ∀ᵐ ω ∂P,
      (1 / 2 : ℝ) *
          P[fun ω' ↦ |(f (X ω') - f (X' ω')) * F (X ω', X' ω')| |
            MeasurableSpace.comap X inferInstance] ω ≤
        B * f (X ω) + C)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ f (X ω)} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) ∧
      P.real {ω | t < f (X ω)} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) ∧
      P.real {ω | f (X ω) ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * C)) ∧
      (C = 0 →
        P.real {ω | f (X ω) ≤ -t} = 0 ∧
          P.real {ω | t ≤ f (X ω)} = 0 ∧
          P.real {ω | t < f (X ω)} = 0) := by
  let Y : Ω → ℝ := fun ω ↦ f (X ω)
  let Y' : Ω → ℝ := fun ω ↦ f (X' ω)
  let G : Ω → ℝ := fun ω ↦ F (X ω, X' ω)
  let D : Ω → ℝ := fun ω ↦ |(Y ω - Y' ω) * G ω|
  have hmX := hX.comap_le
  have hY_meas : Measurable Y := hf.comp hX
  have hXX'_aem : AEMeasurable (fun ω ↦ (X ω, X' ω)) P := hExch.aemeasurable_fst
  have hX'_aem : AEMeasurable X' P := measurable_snd.comp_aemeasurable hXX'_aem
  have hY'_aem : AEMeasurable Y' P := hf.comp_aemeasurable hX'_aem
  have hG_aem : AEMeasurable G P := hF.comp_aemeasurable hXX'_aem
  -- Step 1: `G` and `|G|` are integrable (from `θ = 0`).
  have hAbsG_int : Integrable (fun ω ↦ |G ω|) P := by simpa [Y, G] using hInt 0
  have hG_int : Integrable G P :=
    (integrable_norm_iff hG_aem.aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using hAbsG_int)
  -- Step 2: `|Y| * exp(θ * Y)` and `exp(θ * Y)` are integrable for all `θ : ℝ`.
  have hf_abs : (fun ω ↦ |Y ω|) =ᵐ[P]
      fun ω ↦ |P[G | MeasurableSpace.comap X inferInstance] ω| := by
    filter_upwards [hf_eq] with ω hω
    exact congrArg abs hω
  have hAbsY_le_cond : (fun ω ↦ |Y ω|) ≤ᵐ[P]
      P[fun ω ↦ |G ω| | MeasurableSpace.comap X inferInstance] :=
    hf_abs.trans_le (abs_condExp_ae_le_condExp_abs G)
  have hAbsY_int : Integrable (fun ω ↦ |Y ω|) P := by
    have hnorm : Integrable (fun ω ↦ |P[G | MeasurableSpace.comap X inferInstance] ω|) P := by
      simpa only [Real.norm_eq_abs] using
        (integrable_condExp (μ := P) (m := MeasurableSpace.comap X inferInstance) (f := G)).norm
    exact (integrable_congr hf_abs.symm).mp hnorm
  have hY_sm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (fun ω ↦ |Y ω|) :=
    ((continuous_abs.measurable.comp hf).comp (comap_measurable X)).stronglyMeasurable
  have hCondAbsY : ∀ᵐ ω ∂P,
      (1 : ℝ) * P[fun ω' ↦ |Y ω'| | MeasurableSpace.comap X inferInstance] ω ≤
        P[fun ω' ↦ |G ω'| | MeasurableSpace.comap X inferInstance] ω := by
    have hself : P[fun ω' ↦ |Y ω'| | MeasurableSpace.comap X inferInstance] = fun ω' ↦ |Y ω'| :=
      condExp_of_stronglyMeasurable hmX hY_sm hAbsY_int
    filter_upwards [hAbsY_le_cond] with ω hω
    rwa [one_mul, hself]
  have hExpY_int : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * Y ω)) P := by
    intro θ
    have hexp_meas : Measurable (fun ω ↦ Real.exp (θ * Y ω)) :=
      Real.continuous_exp.measurable.comp (measurable_const.mul hY_meas)
    have hexp_sm : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
        (fun ω ↦ Real.exp (θ * Y ω)) :=
      ((Real.continuous_exp.measurable.comp (measurable_const.mul hf)).comp
        (comap_measurable X)).stronglyMeasurable
    have hGE_abs_int : Integrable (fun ω ↦ |G ω| * Real.exp (θ * Y ω)) P := by
      simpa only [Y, G, mul_comm] using hInt θ
    have hCondGE_int : Integrable
        (fun ω ↦ P[fun ω' ↦ |G ω'| | MeasurableSpace.comap X inferInstance] ω *
          Real.exp (θ * Y ω)) P := by
      have hpull :=
        condExp_mul_of_stronglyMeasurable_right (m := MeasurableSpace.comap X inferInstance)
          hexp_sm hGE_abs_int hAbsG_int
      exact (integrable_congr hpull).mp integrable_condExp
    have hYExp_int : Integrable (fun ω ↦ |Y ω| * Real.exp (θ * Y ω)) P :=
      (integrable_and_integral_mul_exp_le_of_condExp_le (X := X) (f := f) P hX hf zero_lt_one
        hAbsY_int (fun _ ↦ abs_nonneg _) hCondGE_int
        (condExp_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)) hCondAbsY).1
    refine ((integrable_const (Real.exp |θ|)).add hYExp_int).mono'
      hexp_meas.aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
    rcases le_or_gt |Y ω| 1 with hle1 | hgt1
    · have hθY : θ * Y ω ≤ |θ| := calc
        θ * Y ω ≤ |θ * Y ω| := le_abs_self _
        _ = |θ| * |Y ω| := abs_mul θ (Y ω)
        _ ≤ |θ| * 1 := mul_le_mul_of_nonneg_left hle1 (abs_nonneg _)
        _ = |θ| := mul_one _
      exact (Real.exp_le_exp.mpr hθY).trans
        (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
    · have h1 : Real.exp (θ * Y ω) ≤ |Y ω| * Real.exp (θ * Y ω) := by
        nlinarith [Real.exp_pos (θ * Y ω)]
      exact h1.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hIntUniv : interior (ProbabilityTheory.integrableExpSet Y P) = Set.univ := by
    rw [interior_eq_univ]; ext u; exact ⟨fun _ ↦ trivial, fun _ ↦ hExpY_int u⟩
  have hY2 : MemLp Y 2 P :=
    ProbabilityTheory.memLp_of_mem_interior_integrableExpSet (hIntUniv ▸ trivial) 2
  have hYmul_int : ∀ θ : ℝ, Integrable (fun ω ↦ Y ω * Real.exp (θ * Y ω)) P := fun θ ↦ by
    simpa [pow_one] using
      ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
        (hIntUniv ▸ trivial) 1
  -- Step 3: `D = |(Y - Y') * G|` is integrable (from `θ = ±1` + exchangeability).
  have hYG_int : Integrable (fun ω ↦ |Y ω * G ω|) P := by
    have hasm : AEStronglyMeasurable (fun ω ↦ |Y ω * G ω|) P := by
      simpa only [Real.norm_eq_abs, Pi.mul_apply] using
        (hY_meas.aestronglyMeasurable.mul hG_aem.aestronglyMeasurable).norm
    refine ((hInt 1).add (hInt (-1))).mono' hasm (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_abs, abs_mul, Pi.add_apply]
    have hy : |Y ω| ≤ Real.exp (1 * Y ω) + Real.exp ((-1) * Y ω) := by
      have h1 : |Y ω| ≤ Real.exp |Y ω| := (Real.add_one_le_exp |Y ω|).trans' (by linarith)
      rcases le_total 0 (Y ω) with h0 | h0
      · rw [abs_of_nonneg h0] at h1 ⊢
        have he1 : Real.exp (1 * Y ω) = Real.exp (Y ω) := by ring_nf
        linarith [Real.exp_pos ((-1) * Y ω), he1]
      · rw [abs_of_nonpos h0] at h1 ⊢
        have he2 : Real.exp ((-1) * Y ω) = Real.exp (-Y ω) := by ring_nf
        linarith [Real.exp_pos (1 * Y ω), he2]
    nlinarith [abs_nonneg (G ω)]
  have hY'G_int : Integrable (fun ω ↦ |Y' ω * G ω|) P := by
    let H₁ : α × α → ℝ := fun p ↦ |f p.1 * F p|
    have hH₁_meas : Measurable H₁ :=
      continuous_abs.measurable.comp ((hf.comp measurable_fst).mul hF)
    have hH₁_swap_int : Integrable (fun ω ↦ H₁ (X' ω, X ω)) P :=
      (hExch.comp hH₁_meas).integrable_snd hYG_int
    refine hH₁_swap_int.congr (Eventually.of_forall fun ω ↦ ?_)
    dsimp [H₁, Y', G]
    rw [hAnti (X ω) (X' ω), mul_neg, abs_neg]
  have hD_asm : AEStronglyMeasurable D P := by
    simpa only [D, Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply] using
      ((hY_meas.aestronglyMeasurable.sub hY'_aem.aestronglyMeasurable).mul
        hG_aem.aestronglyMeasurable).norm
  have hD_int : Integrable D P := by
    refine (hYG_int.add hY'G_int).mono' hD_asm (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _), Pi.add_apply]
    calc |(Y ω - Y' ω) * G ω|
        = |Y ω * G ω - Y' ω * G ω| := by ring_nf
      _ ≤ |Y ω * G ω| + |Y' ω * G ω| := abs_sub _ _
  -- Step 4: Nonnegativity `0 ≤ B * Y + C` a.s., `∫ Y = 0`, and `(1/2) ∫ D * exp(θ Y) ≤ ...`.
  have hBWC_nn : ∀ᵐ ω ∂P, 0 ≤ B * Y ω + C := by
    have hnn : 0 ≤ᵐ[P] P[D | MeasurableSpace.comap X inferInstance] :=
      condExp_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
    filter_upwards [hnn, hCond] with ω h1 h2
    exact (mul_nonneg (by norm_num) h1).trans h2
  have hMean0 : ∫ ω, Y ω ∂P = 0 := calc
    ∫ ω, Y ω ∂P
        = ∫ ω, P[G | MeasurableSpace.comap X inferInstance] ω ∂P := integral_congr_ae hf_eq
    _ = ∫ ω, G ω ∂P := integral_condExp hmX
    _ = 0 := hExch.integral_antisymm_eq_zero hF hAnti
  have hDExp_bound : ∀ θ : ℝ,
      Integrable (fun ω ↦ D ω * Real.exp (θ * Y ω)) P ∧
        (1 / 2 : ℝ) * ∫ ω, D ω * Real.exp (θ * Y ω) ∂P ≤
          ∫ ω, (B * Y ω + C) * Real.exp (θ * Y ω) ∂P := by
    intro θ
    have hRHS_int : Integrable (fun ω ↦ (B * Y ω + C) * Real.exp (θ * Y ω)) P := by
      have hpt : (fun ω ↦ (B * Y ω + C) * Real.exp (θ * Y ω)) =
          fun ω ↦ B * (Y ω * Real.exp (θ * Y ω)) + C * Real.exp (θ * Y ω) := by ext ω; ring
      rw [hpt]
      exact ((hYmul_int θ).const_mul B).add ((hExpY_int θ).const_mul C)
    exact integrable_and_integral_mul_exp_le_of_condExp_le (X := X) (f := f) P hX hf
      (by norm_num : (0 : ℝ) < 1 / 2) hD_int (fun _ ↦ abs_nonneg _) hRHS_int hBWC_nn hCond
  -- Step 5: Handle `C = 0` (`Y = 0` a.s.) vs `C > 0` (`mgf_tail_bounds_of_abs_deriv_le`).
  have hZeroCase : C = 0 → Y =ᵐ[P] 0 := by
    intro hC0
    have hYG_signed_int : Integrable (fun ω ↦ Y ω * G ω) P :=
      (integrable_norm_iff (hY_meas.aestronglyMeasurable.mul hG_aem.aestronglyMeasurable)).mp
        (by simpa only [Real.norm_eq_abs, Pi.mul_apply] using hYG_int)
    have hY'G_signed_int : Integrable (fun ω ↦ Y' ω * G ω) P :=
      (integrable_norm_iff (hY'_aem.aestronglyMeasurable.mul hG_aem.aestronglyMeasurable)).mp
        (by simpa only [Real.norm_eq_abs, Pi.mul_apply] using hY'G_int)
    have hYg_eq : ∫ ω, Y ω ^ 2 ∂P = (1 / 2 : ℝ) * ∫ ω, (Y ω - Y' ω) * G ω ∂P := by
      have hY_sm0 : StronglyMeasurable[MeasurableSpace.comap X inferInstance] Y :=
        (hf.comp (comap_measurable X)).stronglyMeasurable
      have h1 : ∫ ω, Y ω ^ 2 ∂P = ∫ ω, Y ω * G ω ∂P := by
        have hsq : (fun ω ↦ Y ω ^ 2) =ᵐ[P]
            fun ω ↦ Y ω * P[G | MeasurableSpace.comap X inferInstance] ω := by
          filter_upwards [hf_eq] with ω hω
          dsimp only [Y, G] at hω ⊢
          rw [hω, sq]
        calc ∫ ω, Y ω ^ 2 ∂P
            = ∫ ω, Y ω * P[G | MeasurableSpace.comap X inferInstance] ω ∂P :=
              integral_congr_ae hsq
          _ = ∫ ω, P[fun ω' ↦ Y ω' * G ω' | MeasurableSpace.comap X inferInstance] ω ∂P :=
              integral_congr_ae
                (condExp_mul_of_stronglyMeasurable_left hY_sm0 hYG_signed_int hG_int).symm
          _ = ∫ ω, Y ω * G ω ∂P := integral_condExp hmX
      have h2 : ∫ ω, Y ω * G ω ∂P = -∫ ω, Y' ω * G ω ∂P := by
        let H : α × α → ℝ := fun p ↦ f p.1 * F p
        have hH_meas : Measurable H := (hf.comp measurable_fst).mul hF
        have hId := (hExch.comp hH_meas).integral_eq
        have hswap : (fun ω ↦ H (X' ω, X ω)) = fun ω ↦ -(Y' ω * G ω) := by
          ext ω; dsimp [H, Y', G]; rw [hAnti (X ω) (X' ω)]; ring
        change ∫ ω, H (X ω, X' ω) ∂P = -∫ ω, Y' ω * G ω ∂P
        rw [hId, hswap, integral_neg]
      have hsub : (fun ω ↦ (Y ω - Y' ω) * G ω) = fun ω ↦ Y ω * G ω - Y' ω * G ω := by
        ext ω; ring
      rw [hsub, integral_sub hYG_signed_int hY'G_signed_int]
      linarith
    have hY2_le0 : ∫ ω, Y ω ^ 2 ∂P ≤ 0 := by
      have h0 := (hDExp_bound 0).2
      simp only [zero_mul, Real.exp_zero, mul_one, hC0, add_zero] at h0
      rw [integral_const_mul, hMean0, mul_zero] at h0
      have hDiffG_int : Integrable (fun ω ↦ (Y ω - Y' ω) * G ω) P := by
        have hsub : (fun ω ↦ (Y ω - Y' ω) * G ω) = fun ω ↦ Y ω * G ω - Y' ω * G ω := by
          ext ω; ring
        rw [hsub]
        exact hYG_signed_int.sub hY'G_signed_int
      have habs_le : ∫ ω, (Y ω - Y' ω) * G ω ∂P ≤ ∫ ω, D ω ∂P :=
        integral_mono hDiffG_int hD_int fun ω ↦ le_abs_self _
      linarith
    have hY2_eq0 : ∫ ω, Y ω ^ 2 ∂P = 0 :=
      le_antisymm hY2_le0 (integral_nonneg fun ω ↦ sq_nonneg _)
    have hsq0 : (fun ω ↦ Y ω ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω ↦ sq_nonneg _)
        hY2.integrable_sq).mp hY2_eq0
    filter_upwards [hsq0] with ω hω
    exact sq_eq_zero_iff.mp hω
  have hZeroTails : C = 0 →
      P.real {ω | Y ω ≤ -t} = 0 ∧ P.real {ω | t ≤ Y ω} = 0 ∧ P.real {ω | t < Y ω} = 0 := by
    intro hC0
    have hnull : P {ω | Y ω ≠ 0} = 0 := ae_iff.mp (hZeroCase hC0)
    have h1 : P.real {ω | Y ω ≤ -t} = 0 := by
      have hsub : {ω | Y ω ≤ -t} ⊆ {ω | Y ω ≠ 0} := fun ω hω h0 ↦ by
        change Y ω ≤ -t at hω; linarith
      rw [measureReal_def, measure_mono_null hsub hnull, ENNReal.toReal_zero]
    have h2 : P.real {ω | t ≤ Y ω} = 0 := by
      have hsub : {ω | t ≤ Y ω} ⊆ {ω | Y ω ≠ 0} := fun ω hω h0 ↦ by
        change t ≤ Y ω at hω; linarith
      rw [measureReal_def, measure_mono_null hsub hnull, ENNReal.toReal_zero]
    have h3 : P.real {ω | t < Y ω} = 0 := by
      have hsub : {ω | t < Y ω} ⊆ {ω | Y ω ≠ 0} := fun ω hω h0 ↦ by
        change t < Y ω at hω; linarith
      rw [measureReal_def, measure_mono_null hsub hnull, ENNReal.toReal_zero]
    exact ⟨h1, h2, h3⟩
  rcases hC.eq_or_lt with rfl | hC_pos
  · obtain ⟨hz1, hz2, hz3⟩ := hZeroTails rfl
    refine ⟨?_, ?_, ?_, fun _ ↦ ⟨hz1, hz2, hz3⟩⟩
    · rw [hz2]; positivity
    · rw [hz3]; positivity
    · rw [hz1]; positivity
  · -- Step 6: Prove `|m'(θ)| ≤ |θ| ∫ (B Y + C) exp(θ Y)` and invoke the MGF engine.
    have hDiff : ∀ θ : ℝ,
        |∫ ω, Y ω * Real.exp (θ * Y ω) ∂P| ≤
          |θ| * ∫ ω, (B * Y ω + C) * Real.exp (θ * Y ω) ∂P := by
      intro θ
      have hexp_meas : Measurable (fun ω ↦ Real.exp (θ * Y ω)) :=
        Real.continuous_exp.measurable.comp (measurable_const.mul hY_meas)
      have hexpY_sm : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
          (fun ω ↦ Real.exp (θ * Y ω)) :=
        ((Real.continuous_exp.measurable.comp (measurable_const.mul hf)).comp
          (comap_measurable X)).stronglyMeasurable
      have hGE_int : Integrable (fun ω ↦ G ω * Real.exp (θ * Y ω)) P :=
        (integrable_norm_iff
          (hG_aem.aestronglyMeasurable.mul hexp_meas.aestronglyMeasurable)).mp
          (by
            refine (hInt θ).congr (Eventually.of_forall fun ω ↦ ?_)
            dsimp only [G, Y]
            rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm])
      have hGE'_int : Integrable (fun ω ↦ G ω * Real.exp (θ * Y' ω)) P := by
        let H : α × α → ℝ := fun p ↦ F p * Real.exp (θ * f p.1)
        have hH_meas : Measurable H :=
          hF.mul (Real.continuous_exp.measurable.comp
            (measurable_const.mul (hf.comp measurable_fst)))
        have hswap_int : Integrable (fun ω ↦ H (X' ω, X ω)) P :=
          (hExch.comp hH_meas).integrable_snd hGE_int
        have heq_neg : (fun ω ↦ G ω * Real.exp (θ * Y' ω)) = fun ω ↦ -H (X' ω, X ω) := by
          ext ω; dsimp [H, G, Y']; rw [hAnti (X ω) (X' ω)]; ring
        rw [heq_neg]
        exact hswap_int.neg
      have hm'_eq_G : ∫ ω, Y ω * Real.exp (θ * Y ω) ∂P =
          ∫ ω, G ω * Real.exp (θ * Y ω) ∂P := by
        have h1 : (fun ω ↦ Y ω * Real.exp (θ * Y ω)) =ᵐ[P]
            fun ω ↦ P[G | MeasurableSpace.comap X inferInstance] ω * Real.exp (θ * Y ω) := by
          filter_upwards [hf_eq] with ω hω
          dsimp only [Y, G] at hω ⊢
          rw [hω]
        calc ∫ ω, Y ω * Real.exp (θ * Y ω) ∂P
            = ∫ ω, P[G | MeasurableSpace.comap X inferInstance] ω * Real.exp (θ * Y ω) ∂P :=
              integral_congr_ae h1
          _ = ∫ ω, P[fun ω' ↦ G ω' * Real.exp (θ * Y ω') |
                MeasurableSpace.comap X inferInstance] ω ∂P :=
              integral_congr_ae
                (condExp_mul_of_stronglyMeasurable_right hexpY_sm hGE_int hG_int).symm
          _ = ∫ ω, G ω * Real.exp (θ * Y ω) ∂P := integral_condExp hmX
      have hGE_swap : ∫ ω, G ω * Real.exp (θ * Y ω) ∂P =
          -∫ ω, G ω * Real.exp (θ * Y' ω) ∂P := by
        let H : α × α → ℝ := fun p ↦ F p * Real.exp (θ * f p.1)
        have hH_meas : Measurable H :=
          hF.mul (Real.continuous_exp.measurable.comp
            (measurable_const.mul (hf.comp measurable_fst)))
        have hId := (hExch.comp hH_meas).integral_eq
        have hswap : (fun ω ↦ H (X' ω, X ω)) = fun ω ↦ -(G ω * Real.exp (θ * Y' ω)) := by
          ext ω; dsimp [H, G, Y']; rw [hAnti (X ω) (X' ω)]; ring
        change ∫ ω, H (X ω, X' ω) ∂P = -∫ ω, G ω * Real.exp (θ * Y' ω) ∂P
        rw [hId, hswap, integral_neg]
      have hm'_half : ∫ ω, Y ω * Real.exp (θ * Y ω) ∂P =
          (1 / 2 : ℝ) * ∫ ω, G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω)) ∂P := by
        have hsub : (fun ω ↦ G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω))) =
            fun ω ↦ G ω * Real.exp (θ * Y ω) - G ω * Real.exp (θ * Y' ω) := by ext ω; ring
        rw [hsub, integral_sub hGE_int hGE'_int, hm'_eq_G]
        linarith
      have hDE_int : Integrable (fun ω ↦ D ω * Real.exp (θ * Y ω)) P := (hDExp_bound θ).1
      have hDE'_eq : Integrable (fun ω ↦ D ω * Real.exp (θ * Y' ω)) P ∧
          ∫ ω, D ω * Real.exp (θ * Y' ω) ∂P = ∫ ω, D ω * Real.exp (θ * Y ω) ∂P := by
        let KD : α × α → ℝ := fun p ↦ |(f p.1 - f p.2) * F p| * Real.exp (θ * f p.1)
        have hKD_meas : Measurable KD :=
          (continuous_abs.measurable.comp
            (((hf.comp measurable_fst).sub (hf.comp measurable_snd)).mul hF)).mul
            (Real.continuous_exp.measurable.comp (measurable_const.mul (hf.comp measurable_fst)))
        have hId := hExch.comp hKD_meas
        have hKD_swap : (fun ω ↦ KD (X' ω, X ω)) = fun ω ↦ D ω * Real.exp (θ * Y' ω) := by
          ext ω
          dsimp [KD, D, Y, Y', G]
          have hsym : (f (X' ω) - f (X ω)) * F (X' ω, X ω) =
              (f (X ω) - f (X' ω)) * F (X ω, X' ω) := by
            rw [hAnti (X' ω) (X ω)]; ring
          rw [hsym]
        refine ⟨hKD_swap ▸ hId.integrable_snd hDE_int, ?_⟩
        rw [← hKD_swap]
        exact hId.integral_eq.symm
      have hGdiff_int : Integrable
          (fun ω ↦ G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω))) P := by
        have hsub : (fun ω ↦ G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω))) =
            fun ω ↦ G ω * Real.exp (θ * Y ω) - G ω * Real.exp (θ * Y' ω) := by ext ω; ring
        rw [hsub]
        exact hGE_int.sub hGE'_int
      have hDom_int : Integrable
          (fun ω ↦ (|θ| / 2) * (D ω * Real.exp (θ * Y ω) + D ω * Real.exp (θ * Y' ω))) P :=
        (hDE_int.add hDE'_eq.1).const_mul (|θ| / 2)
      have hpt_bound : ∀ ω,
          |G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω))| ≤
            (|θ| / 2) * (D ω * Real.exp (θ * Y ω) + D ω * Real.exp (θ * Y' ω)) := by
        intro ω
        rw [abs_mul]
        have hchord := abs_exp_sub_exp_le (θ * Y ω) (θ * Y' ω)
        have hθsub : |θ * Y ω - θ * Y' ω| = |θ| * |Y ω - Y' ω| := by rw [← mul_sub, abs_mul]
        calc |G ω| * |Real.exp (θ * Y ω) - Real.exp (θ * Y' ω)|
            ≤ |G ω| * (|θ * Y ω - θ * Y' ω| *
                ((Real.exp (θ * Y ω) + Real.exp (θ * Y' ω)) / 2)) :=
              mul_le_mul_of_nonneg_left hchord (abs_nonneg _)
          _ = (|θ| / 2) * ((|Y ω - Y' ω| * |G ω|) * Real.exp (θ * Y ω) +
                (|Y ω - Y' ω| * |G ω|) * Real.exp (θ * Y' ω)) := by rw [hθsub]; ring
          _ = (|θ| / 2) * (D ω * Real.exp (θ * Y ω) + D ω * Real.exp (θ * Y' ω)) := by
              dsimp [D]; rw [abs_mul]
      have hnorm_le :
          |∫ ω, G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω)) ∂P| ≤
            ∫ ω, |G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω))| ∂P := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (f := fun ω ↦
            G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω))) (μ := P)
      calc |∫ ω, Y ω * Real.exp (θ * Y ω) ∂P|
          = (1 / 2 : ℝ) * |∫ ω, G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω)) ∂P| := by
            rw [hm'_half, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        _ ≤ (1 / 2 : ℝ) * ∫ ω, |G ω * (Real.exp (θ * Y ω) - Real.exp (θ * Y' ω))| ∂P :=
            mul_le_mul_of_nonneg_left hnorm_le (by norm_num)
        _ ≤ (1 / 2 : ℝ) *
              ∫ ω, (|θ| / 2) * (D ω * Real.exp (θ * Y ω) + D ω * Real.exp (θ * Y' ω)) ∂P :=
            mul_le_mul_of_nonneg_left
              (integral_mono (by simpa only [Real.norm_eq_abs] using hGdiff_int.norm)
                hDom_int hpt_bound)
              (by norm_num)
        _ = |θ| * ((1 / 2 : ℝ) * ∫ ω, D ω * Real.exp (θ * Y ω) ∂P) := by
            rw [integral_const_mul, integral_add hDE_int hDE'_eq.1, hDE'_eq.2]
            ring
        _ ≤ |θ| * ∫ ω, (B * Y ω + C) * Real.exp (θ * Y ω) ∂P :=
            mul_le_mul_of_nonneg_left (hDExp_bound θ).2 (abs_nonneg _)
    obtain ⟨hUp, hLow⟩ :=
      mgf_tail_bounds_of_abs_deriv_le P hExpY_int hMean0 hB hC_pos hDiff ht
    have hUp_strict : P.real {ω | t < Y ω} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) := by
      have hsub : {ω | t < Y ω} ⊆ {ω | t ≤ Y ω} := fun ω (hlt : t < Y ω) ↦ le_of_lt hlt
      have hmono : P.real {ω | t < Y ω} ≤ P.real {ω | t ≤ Y ω} := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
      exact hmono.trans hUp
    exact ⟨hUp, hUp_strict, hLow, fun hC0 ↦ absurd hC0 hC_pos.ne'⟩

/-! ### Section 3: Prose Reduction (`SteinIntro.tex:3677-3681`) & Theorem 7.2 -/

/-- General $a > 0$ reduction from an exchangeable linear-regression pair $(W, W')$ to the
antisymmetric kernel $F(w, w') = (w - w') / a$ of Theorem 7.5 (`SteinIntro.tex:3677-3681`;
ruling `D7`, `F4`). -/
theorem steinPair_reduction_of_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W) (hW_int : Integrable W P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω) :
    let F : ℝ × ℝ → ℝ := fun p ↦ (p.1 - p.2) / a
    (∀ w w' : ℝ, F (w, w') = -F (w', w)) ∧
      P[fun ω ↦ F (W ω, W' ω) | MeasurableSpace.comap W inferInstance] =ᵐ[P] W ∧
      (fun ω ↦
        (1 / 2 : ℝ) *
          P[fun ω' ↦ |(W ω' - W' ω') * F (W ω', W' ω')| |
            MeasurableSpace.comap W inferInstance] ω) =ᵐ[P]
        fun ω ↦
          P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
            MeasurableSpace.comap W inferInstance] ω / (2 * a) := by
  dsimp only
  set F : ℝ × ℝ → ℝ := fun p ↦ (p.1 - p.2) / a
  have hAnti : ∀ w w' : ℝ, F (w, w') = -F (w', w) := fun w w' ↦ by dsimp [F]; ring
  have hmW := hW_meas.comap_le
  have hW'_int : Integrable W' P := hExch.fst_identDistrib_snd.integrable_snd hW_int
  have hW_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] W :=
    (comap_measurable W).stronglyMeasurable
  have hPW : P[W | MeasurableSpace.comap W inferInstance] = W :=
    condExp_of_stronglyMeasurable hmW hW_sm hW_int
  have hReg : P[fun ω ↦ F (W ω, W' ω) | MeasurableSpace.comap W inferInstance] =ᵐ[P] W := by
    have hpt : (fun ω ↦ F (W ω, W' ω)) = a⁻¹ • (W - W') := by
      ext ω; dsimp [F]; ring
    rw [hpt]
    have h1 := condExp_smul a⁻¹ (W - W') (MeasurableSpace.comap W inferInstance) (μ := P)
    have h2 := condExp_sub hW_int hW'_int (MeasurableSpace.comap W inferInstance)
    filter_upwards [h1, h2, hCond] with ω hω1 hω2 hω3
    rw [hω1, Pi.smul_apply, smul_eq_mul, hω2, Pi.sub_apply, hPW, hω3]
    field_simp [ha.ne']
    ring
  have hQuad : (fun ω ↦
      (1 / 2 : ℝ) *
        P[fun ω' ↦ |(W ω' - W' ω') * F (W ω', W' ω')| |
          MeasurableSpace.comap W inferInstance] ω) =ᵐ[P]
      fun ω ↦
        P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
          MeasurableSpace.comap W inferInstance] ω / (2 * a) := by
    have hpt : (fun ω' ↦ |(W ω' - W' ω') * F (W ω', W' ω')|) =
        a⁻¹ • fun ω' ↦ (W' ω' - W ω') ^ 2 := by
      ext ω'
      dsimp [F]
      have hsq : (W ω' - W' ω') * ((W ω' - W' ω') / a) = a⁻¹ * (W' ω' - W ω') ^ 2 := by ring
      rw [hsq, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr ha.le) (sq_nonneg _))]
    rw [hpt]
    filter_upwards [condExp_smul a⁻¹ (fun ω' ↦ (W' ω' - W ω') ^ 2)
      (MeasurableSpace.comap W inferInstance) (μ := P)] with ω hω
    rw [hω, Pi.smul_apply, smul_eq_mul]
    field_simp [ha.ne']
  exact ⟨hAnti, hReg, hQuad⟩

/-- Section 7 prose reduction from Theorem 7.5 to Theorem 7.2 (`SteinIntro.tex:3677-3681`, `F4`):
if $(W, W')$ is an $a$-Stein pair, setting $F(w, w') = (w - w') / a$ gives an antisymmetric
kernel with $\mathbb{E}[F(W, W') \mid W] = W$ a.s. and reduces Theorem 7.5's condition to `(7.1)`
with $\mathcal{F} = \sigma(W)$. -/
theorem steinPair_reduction_to_antisymm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hSP : IsSteinPair P a W W') :
    let F : ℝ × ℝ → ℝ := fun p ↦ (p.1 - p.2) / a
    (∀ w w' : ℝ, F (w, w') = -F (w', w)) ∧
      P[fun ω ↦ F (W ω, W' ω) | MeasurableSpace.comap W inferInstance] =ᵐ[P] W ∧
      (fun ω ↦
        (1 / 2 : ℝ) *
          P[fun ω' ↦ |(W ω' - W' ω') * F (W ω', W' ω')| |
            MeasurableSpace.comap W inferInstance] ω) =ᵐ[P]
        fun ω ↦
          P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
            MeasurableSpace.comap W inferInstance] ω / (2 * a) := by
  rcases hSP with ⟨hExch, ha, _, hW_meas, hW_int, hCond⟩
  exact steinPair_reduction_of_pos P hExch ha hW_meas hW_int hCond

/-- General $a > 0$ library version of **Theorem 7.2** (`\label{thm211a}`, eq. `(7.1)`
`\label{122g}`, `SteinIntro.tex:3479-3489`; ruling `D7`, `F1`): concentration inequalities for an
exchangeable pair $(W, W')$ satisfying $\mathbb{E}[W' \mid W] = (1 - a) W$ with $a > 0$ (not
requiring $a \le 1$, so Proposition 7.3 at $n = 2$ where $a = 2$ is covered directly) and linear
conditional-variance bound $\mathbb{E}[(W' - W)^2 \mid \mathcal{F}] / (2a) \le B W + C$ for any
sub-$\sigma$-algebra $\mathcal{F} \supseteq \sigma(W)$, including the exact boundary values at
$C = 0$. -/
theorem steinPair_tail_bounds_of_pos
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a B C : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hInt : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * W ω) * |W' ω - W ω|) P)
    {m : MeasurableSpace Ω}
    (hWm : MeasurableSpace.comap W inferInstance ≤ m) (hm : m ≤ m₀)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hVarCond : ∀ᵐ ω ∂P, P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a) ≤ B * W ω + C)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ W ω} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) ∧
      P.real {ω | W ω ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * C)) ∧
      (C = 0 → P.real {ω | W ω ≤ -t} = 0) ∧
      (B = 0 → C = 0 → P.real {ω | t ≤ W ω} = 0) := by
  let mW : MeasurableSpace Ω := MeasurableSpace.comap W inferInstance
  have hW_int : Integrable W P := hW2.integrable one_le_two
  obtain ⟨hAnti, hReg, hQuad⟩ :=
    @steinPair_reduction_of_pos Ω m₀ P _ a W W' hExch ha hW_meas hW_int hCond
  let F : ℝ × ℝ → ℝ := fun p ↦ (p.1 - p.2) / a
  have hF_meas : Measurable F := (measurable_fst.sub measurable_snd).div_const a
  have hF_int : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * W ω) * |F (W ω, W' ω)|) P := by
    intro θ
    have hpt : (fun ω ↦ Real.exp (θ * W ω) * |F (W ω, W' ω)|) =
        fun ω ↦ a⁻¹ * (Real.exp (θ * W ω) * |W' ω - W ω|) := by
      ext ω
      dsimp [F]
      rw [abs_div, abs_of_pos ha, abs_sub_comm]
      ring
    rw [hpt]
    exact (hInt θ).const_mul a⁻¹
  have hBWC_int : Integrable (fun ω ↦ B * W ω + C) P :=
    (hW_int.const_mul B).add (integrable_const C)
  have hBWC_sm : StronglyMeasurable[mW] (fun ω ↦ B * W ω + C) :=
    (((comap_measurable (m := inferInstance) W).const_mul B).add
      measurable_const).stronglyMeasurable
  have hTower : ∀ᵐ ω ∂P,
      P[fun ω' ↦ (W' ω' - W ω') ^ 2 | mW] ω / (2 * a) ≤ B * W ω + C := by
    have hLHS_int : Integrable
        (fun ω ↦ P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a)) P :=
      integrable_condExp.div_const (2 * a)
    have hmono := condExp_mono (m := mW) hLHS_int hBWC_int hVarCond
    have hRHS_eq : P[fun ω ↦ B * W ω + C | mW] = fun ω ↦ B * W ω + C :=
      condExp_of_stronglyMeasurable (hWm.trans hm) hBWC_sm hBWC_int
    have hsmul : P[fun ω ↦ P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a) | mW] =ᵐ[P]
        fun ω ↦ P[P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] | mW] ω / (2 * a) := by
      have hpt : (fun ω ↦ P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a)) =
          (2 * a)⁻¹ • P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] := by
        ext ω; dsimp; ring
      rw [hpt]
      filter_upwards [condExp_smul (2 * a)⁻¹ (P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m]) mW (μ := P)]
        with ω hω
      rw [hω, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    have hcc := condExp_condExp_of_le (m₀ := m₀) (μ := P)
      (f := fun ω' ↦ (W' ω' - W ω') ^ 2) hWm hm
    filter_upwards [hmono, hsmul, hcc] with ω h1 h2 h3
    rw [hRHS_eq] at h1
    have h3div : P[P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] | mW] ω / (2 * a) =
        P[fun ω' ↦ (W' ω' - W ω') ^ 2 | mW] ω / (2 * a) := by rw [h3]
    linarith
  have hCond75 : ∀ᵐ ω ∂P,
      (1 / 2 : ℝ) *
          P[fun ω' ↦ |(W ω' - W' ω') * F (W ω', W' ω')| | mW] ω ≤
        B * W ω + C := by
    filter_upwards [hQuad, hTower] with ω h1 h2
    exact h1.le.trans h2
  obtain ⟨hUp, _, hLow, hZero⟩ :=
    @exchangeable_antisymm_tail_bound Ω ℝ m₀ inferInstance P _ W W' F id B C
      hW_meas hExch hF_meas hAnti measurable_id hReg.symm hF_int hB hC hCond75 t ht
  exact ⟨hUp, hLow, fun hC0 ↦ (hZero hC0).1, fun _ hC0 ↦ (hZero hC0).2.1⟩

/-- **Theorem 7.2** (`\label{thm211a}`, eq. `(7.1)` `\label{122g}`, `SteinIntro.tex:3479-3489`;
`D7`, `F1`): concentration inequalities for an $a$-Stein pair $(W, W')$ with finite variance under
$\mathbb{E}[(W' - W)^2 \mid \mathcal{F}] / (2a) \le B W + C$, including boundary conjuncts at
$C = 0$. -/
theorem steinPair_tail_bounds
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a B C : ℝ} {W W' : Ω → ℝ}
    (hSP : IsSteinPair P a W W') (hW2 : MemLp W 2 P)
    (hInt : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * W ω) * |W' ω - W ω|) P)
    {m : MeasurableSpace Ω}
    (hWm : MeasurableSpace.comap W inferInstance ≤ m) (hm : m ≤ m₀)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hVarCond : ∀ᵐ ω ∂P, P[fun ω' ↦ (W' ω' - W ω') ^ 2 | m] ω / (2 * a) ≤ B * W ω + C)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ W ω} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) ∧
      P.real {ω | W ω ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * C)) ∧
      (C = 0 → P.real {ω | W ω ≤ -t} = 0) ∧
      (B = 0 → C = 0 → P.real {ω | t ≤ W ω} = 0) := by
  rcases hSP with ⟨hExch, ha, _, hW_meas, _, hCond⟩
  exact @steinPair_tail_bounds_of_pos Ω m₀ P _ a B C W W' hExch ha hW_meas hW2 hCond hInt
    m hWm hm hB hC hVarCond t ht

end SteinMethod
