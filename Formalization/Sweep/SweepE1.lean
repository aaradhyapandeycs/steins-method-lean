/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Branching.Extinction
import Formalization.Exponential.Equilibrium

/-!
# Section 5 Prose-Claim Sweep (`Formalization.Sweep.SweepE1`)

Proves the two remaining approved items from `docs/reviews/stmts-review-SWEEP-E.md`
(`SE-1`–`SE-8`):
- `sec5_1_equilibrium_rhs_wellDefined` (`D-E3`, `SteinIntro.tex:2844-2845`; `ISSUE-5.5`):
  almost-sure differentiability and representative invariance of $\mathbb{E}[f'(W^e)]$ in `(5.3)`.
- `sec5_3_scaled_Yn_mean_gt_one_witness` (`D-E6` witness, `SteinIntro.tex:3023-3024`;
  `ISSUE-5.9-PROOF-MEAN`): witness critical Galton–Watson process with $\sigma^2 > 0$ and
  $\mathbb{E}|Z_1|^3 < \infty$ for which $\mathbb{E}[2 Y_n / (n\sigma^2)] > 1$ for every $n \ge 1$.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-- **Section 5.1 prose: well-definedness of $\mathbb{E}[f'(W^e)]$ in `(5.3)`**
(`\label{173}`, `SteinIntro.tex:2844-2845`; `ISSUE-5.5`, `D-E3`): for any non-negative integrable
$W$ with $\mu = \mathbb{E}[W] > 0$, any equilibrium variable $W^e$ (`IsEquilibrium P W P' We`),
and any $K$-Lipschitz function $f : \mathbb{R} \to \mathbb{R}$, $f$ is differentiable at
$W^e(\omega')$ for $P'$-almost-every $\omega'$, `deriv f ∘ We` is $P'$-integrable, and every
function $g : \mathbb{R} \to \mathbb{R}$ agreeing with `deriv f` where $f$ is differentiable is
$P'$-integrable along $W^e$ with $\int g(W^e)\,dP' = \int f'(W^e)\,dP'$. -/
theorem sec5_1_equilibrium_rhs_wellDefined
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {We : Ω' → ℝ} {f g : ℝ → ℝ} {K : ℝ≥0}
    (hW_nn : 0 ≤ᵐ[P] W)
    (hW_int : Integrable W P)
    (hμ_pos : 0 < ∫ ω, W ω ∂P)
    (hEq : IsEquilibrium P W P' We)
    (hLip : LipschitzWith K f)
    (hg : ∀ x : ℝ, DifferentiableAt ℝ f x → g x = deriv f x) :
    (∀ᵐ ω' ∂P', DifferentiableAt ℝ f (We ω')) ∧
      Integrable (fun ω' ↦ deriv f (We ω')) P' ∧
      Integrable (fun ω' ↦ g (We ω')) P' ∧
      (∫ ω', g (We ω') ∂P' = ∫ ω', deriv f (We ω') ∂P') := by
  have hac : Measure.AbsolutelyContinuous (P'.map We) volume :=
    ((sec5_1_equilibrium_ac P hW_nn hW_int hμ_pos).1 P' hEq).2
  have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
    fun a b ↦ hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hdiff_vol : ∀ᵐ x ∂volume, DifferentiableAt ℝ f x := by
    have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
        x ∈ uIcc (-(n : ℝ) - 1) ((n : ℝ) + 1) → DifferentiableAt ℝ f x :=
      ae_all_iff.mpr fun n ↦ (hf_ac (-(n : ℝ) - 1) ((n : ℝ) + 1)).ae_differentiableAt
    filter_upwards [hall] with x hx
    let n : ℕ := ⌈|x|⌉₊
    have hxn : |x| ≤ (n : ℝ) := Nat.le_ceil |x|
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmem : x ∈ uIcc (-(n : ℝ) - 1) ((n : ℝ) + 1) := by
      rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    exact hx n hmem
  let s : Set ℝ := {x : ℝ | ¬ DifferentiableAt ℝ f x}
  let E : Set ℝ := toMeasurable volume s
  have hvol_E : volume E = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hdiff_vol
  have hmap_E : (P'.map We) E = 0 := hac hvol_E
  have hpre_E : P' (We ⁻¹' E) = 0 := by
    rwa [← Measure.map_apply_of_aemeasurable hEq.2.2.1 (measurableSet_toMeasurable volume s)]
  have hdiff_P' : ∀ᵐ ω' ∂P', DifferentiableAt ℝ f (We ω') := by
    rw [ae_iff]
    refine measure_mono_null (fun ω' hω' ↦ ?_) hpre_E
    exact subset_toMeasurable volume s hω'
  have hderiv_int : Integrable (fun ω' ↦ deriv f (We ω')) P' := by
    refine Integrable.of_bound
      ((measurable_deriv f).comp_aemeasurable hEq.2.2.1).aestronglyMeasurable K
      (ae_of_all P' fun ω' ↦ ?_)
    exact norm_deriv_le_of_lipschitz hLip
  have hae_eq : (fun ω' ↦ deriv f (We ω')) =ᵐ[P'] fun ω' ↦ g (We ω') :=
    hdiff_P'.mono fun ω' hω' ↦ (hg (We ω') hω').symm
  exact ⟨hdiff_P', hderiv_int, hderiv_int.congr hae_eq, integral_congr_ae hae_eq.symm⟩

/-- **Non-unit-mean witness for `ISSUE-5.9-PROOF-MEAN`** (`SteinIntro.tex:3023-3024`; `SE-4`):
for the critical Galton–Watson process with offspring law
$\frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$ ($\mathbb{E}[Z_1] = 1$, $\sigma^2 = 1 > 0$,
$\mathbb{E}|Z_1|^3 = 4 < \infty$), the scaled non-extinct generation size $\frac{2 Y_n}{n\sigma^2}$
satisfies $\mathbb{E}\bigl[\frac{2 Y_n}{n\sigma^2}\bigr] > 1$ for every $n \ge 1$, so Theorem 5.4
(`\label{thm172}`, which requires $\mathbb{E}[W] = 1$) does not apply directly to
$\frac{2 Y_n}{n\sigma^2}$. -/
theorem sec5_3_scaled_Yn_mean_gt_one_witness :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (Z : ℕ → Ω → ℕ),
      IsGaltonWatson P Z ∧
        ∫ ω, (Z 1 ω : ℝ) ∂P = 1 ∧
        MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P ∧
        0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P ∧
        ∀ n : ℕ, 1 ≤ n →
          let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
          1 < ∫ ω, 2 * (Z n ω : ℝ) / ((n : ℝ) * σsq)
            ∂(ProbabilityTheory.cond P {ω | 0 < Z n ω}) := by
  let P : Measure (ℕ × ℕ → ℕ) := Measure.infinitePi (fun _ : ℕ × ℕ ↦ twoBernoulliMeasure)
  let ξ : ℕ × ℕ → (ℕ × ℕ → ℕ) → ℕ := fun p ω ↦ ω p
  let Z : ℕ → (ℕ × ℕ → ℕ) → ℕ := gwCanonical ξ
  have hGW : IsGaltonWatson P Z :=
    isGaltonWatson_infinitePi twoBernoulliMeasure (integrable_twoBernoulliMeasure _)
  have hξ_meas : ∀ p, Measurable (ξ p) := measurable_pi_apply
  have hZ_meas : ∀ n, Measurable (Z n) := measurable_gwCanonical hξ_meas
  have hZ1_eq : Z 1 = ξ (0, 0) := funext (gwCanonical_one ξ)
  have hmap : P.map (Z 1) = twoBernoulliMeasure := by
    rw [hZ1_eq]
    exact Measure.infinitePi_map_eval (fun _ : ℕ × ℕ ↦ twoBernoulliMeasure) (0, 0)
  have hcast_meas : Measurable (fun k : ℕ ↦ (k : ℝ)) := Measurable.of_discrete
  have hsq_meas : Measurable (fun k : ℕ ↦ ((k : ℝ) - 1) ^ 2) := Measurable.of_discrete
  have hZ1R_meas : Measurable (fun ω ↦ (Z 1 ω : ℝ)) := hcast_meas.comp (hZ_meas 1)
  have hmean : ∫ ω, (Z 1 ω : ℝ) ∂P = 1 := by
    have h1 := integral_map (μ := P) (hZ_meas 1).aemeasurable hcast_meas.aestronglyMeasurable
    rw [hmap, integral_twoBernoulliMeasure] at h1
    linarith [h1]
  have hvar : ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P = 1 := by
    rw [ProbabilityTheory.variance_eq_integral hZ1R_meas.aemeasurable, hmean]
    have h1 := integral_map (μ := P) (hZ_meas 1).aemeasurable hsq_meas.aestronglyMeasurable
    rw [hmap, integral_twoBernoulliMeasure] at h1
    linarith [h1]
  have hgt2_zero : P {ω | 2 < Z 1 ω} = 0 := by
    have hpre : {ω : ℕ × ℕ → ℕ | 2 < Z 1 ω} = (Z 1) ⁻¹' {k : ℕ | 2 < k} := rfl
    rw [hpre, ← Measure.map_apply (hZ_meas 1) MeasurableSet.of_discrete, hmap]
    simp [twoBernoulliMeasure]
  have hae_le2 : ∀ᵐ ω ∂P, Z 1 ω ≤ 2 := by
    rw [ae_iff]
    simpa only [not_le] using hgt2_zero
  have hZ1_le2 : ∀ᵐ ω ∂P, ‖(Z 1 ω : ℝ)‖ ≤ 2 := by
    refine hae_le2.mono fun ω hk ↦ ?_
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hk
  have hL3 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P :=
    (memLp_top_of_bound hZ1R_meas.aestronglyMeasurable 2 hZ1_le2).mono_exponent le_top
  let φ : ℝ → ℝ := fun t ↦ ∫ ω, t ^ (Z 1 ω) ∂P
  have hφ_eq : ∀ t : ℝ, φ t = (1 + t ^ 2) / 2 := fun t ↦ by
    have hpow_meas : Measurable (fun k : ℕ ↦ t ^ k) := Measurable.of_discrete
    have h1 := integral_map (μ := P) (hZ_meas 1).aemeasurable hpow_meas.aestronglyMeasurable
    rw [hmap, integral_twoBernoulliMeasure] at h1
    dsimp only [φ]
    linarith [h1]
  have hp_bound : ∀ n : ℕ,
      0 < 1 - φ^[n] 0 ∧ 1 - φ^[n] 0 ≤ 2 / ((n : ℝ) + 2) := by
    intro n
    induction n with
    | zero =>
      simp only [Function.iterate_zero, id_eq, sub_zero, Nat.cast_zero, zero_add]
      norm_num
    | succ m ih =>
      rcases ih with ⟨hm_pos, hm_le⟩
      set pm : ℝ := 1 - φ^[m] 0
      have hqm : φ^[m] 0 = 1 - pm := by ring
      have hnext : 1 - φ^[m + 1] 0 = pm * (1 - pm / 2) := by
        rw [Function.iterate_succ_apply', hφ_eq, hqm]
        ring
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have h2m_pos : (0 : ℝ) < (m : ℝ) + 2 := by linarith
      have h3m_pos : (0 : ℝ) < (m : ℝ) + 3 := by linarith
      have hpm_le1 : pm ≤ 1 := by
        have hle : 2 / ((m : ℝ) + 2) ≤ 1 := by
          rw [div_le_one h2m_pos]; linarith
        exact hm_le.trans hle
      refine ⟨?_, ?_⟩
      · rw [hnext]
        exact mul_pos hm_pos (by linarith)
      · rw [hnext, Nat.cast_add, Nat.cast_one, show (m : ℝ) + 1 + 2 = (m : ℝ) + 3 by ring]
        let u : ℝ := 2 / ((m : ℝ) + 2)
        have hmono : pm * (1 - pm / 2) ≤ u * (1 - u / 2) := by
          have hdiff : u * (1 - u / 2) - pm * (1 - pm / 2) =
              (u - pm) * (1 - (u + pm) / 2) := by ring
          have hu_le1 : u ≤ 1 := by
            dsimp only [u]; rw [div_le_one h2m_pos]; linarith
          have h1 : 0 ≤ u - pm := sub_nonneg.mpr hm_le
          have h2 : 0 ≤ 1 - (u + pm) / 2 := by linarith
          linarith [mul_nonneg h1 h2]
        have hu_step : u * (1 - u / 2) ≤ 2 / ((m : ℝ) + 3) := by
          dsimp only [u]
          have hsimp : (2 / ((m : ℝ) + 2)) * (1 - (2 / ((m : ℝ) + 2)) / 2) =
              (2 * ((m : ℝ) + 1)) / (((m : ℝ) + 2) ^ 2) := by
            field_simp [h2m_pos.ne']
            ring
          rw [hsimp, div_le_div_iff₀ (pow_pos h2m_pos 2) h3m_pos]
          nlinarith
        exact hmono.trans hu_step
  refine ⟨ℕ × ℕ → ℕ, inferInstance, P, inferInstance, Z, hGW, hmean, hL3,
    by rw [hvar]; exact zero_lt_one, fun n hn ↦ ?_⟩
  dsimp only
  rw [hvar, mul_one]
  set E : Set (ℕ × ℕ → ℕ) := {ω | 0 < Z n ω}
  have hE_meas : MeasurableSet E := (hZ_meas n) MeasurableSet.of_discrete
  have hEc_eq : Eᶜ = {ω | Z n ω = 0} := by
    ext ω; simp [E]
  have hpE_eq : P.real E = 1 - φ^[n] 0 := by
    have hcompl : P.real E = 1 - P.real {ω | Z n ω = 0} := by
      have h1 := probReal_compl_eq_one_sub (μ := P) hE_meas
      rw [hEc_eq] at h1
      linarith
    rw [hcompl, hGW.measureReal_Z_eq_zero n]
  obtain ⟨hpE_pos, hpE_le⟩ := hp_bound n
  have hpE_real_pos : 0 < P.real E := hpE_eq ▸ hpE_pos
  have hset_int : ∫ ω in E, (Z n ω : ℝ) ∂P = 1 := by
    rw [← integral_indicator hE_meas]
    have hind : E.indicator (fun ω ↦ (Z n ω : ℝ)) = fun ω ↦ (Z n ω : ℝ) := by
      ext ω
      by_cases hω : ω ∈ E
      · exact indicator_of_mem hω _
      · rw [indicator_of_notMem hω]
        have hz0 : Z n ω = 0 := by simpa [E] using hω
        simp [hz0]
    rw [hind]
    exact hGW.integral_Z_eq_one hmean n
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn))
  have hcond_int :
      ∫ ω, 2 * (Z n ω : ℝ) / (n : ℝ) ∂(ProbabilityTheory.cond P E) =
        2 / ((n : ℝ) * P.real E) := by
    rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
      ← measureReal_def]
    have hlin : (fun ω : ℕ × ℕ → ℕ ↦ 2 * (Z n ω : ℝ) / (n : ℝ)) =
        fun ω ↦ (2 / (n : ℝ)) * (Z n ω : ℝ) := by
      ext ω; ring
    rw [hlin, integral_const_mul, hset_int, mul_one]
    field_simp [hn_pos.ne', hpE_real_pos.ne']
  rw [hcond_int, one_lt_div (mul_pos hn_pos hpE_real_pos)]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hnp_le : (n : ℝ) * P.real E ≤ 2 * (n : ℝ) / ((n : ℝ) + 2) := by
    calc
      (n : ℝ) * P.real E ≤ (n : ℝ) * (2 / ((n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (hpE_eq ▸ hpE_le) hn_pos.le
      _ = 2 * (n : ℝ) / ((n : ℝ) + 2) := by ring
  have hlt2 : 2 * (n : ℝ) / ((n : ℝ) + 2) < 2 := by
    rw [div_lt_iff₀ hn2_pos]
    linarith
  exact hnp_le.trans_lt hlt2

end SteinMethod
