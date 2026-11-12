/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Exchangeable.Basic
import Formalization.Normal.WassersteinBound
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Function-Level Stein-Pair Inequality (3.18) and Wasserstein Corollary (`SweepBSteinPair`)

Proves the Section 3.3 intermediate function-level inequality (3.18) (`\label{511}`,
`SteinIntro.tex:1043-1046`) and its Wasserstein corollary (`SteinIntro.tex:1047-1048`):

* `sec3_3_eq3_18_proof` (`Sec3_3_eq3_18`): for an $a$-Stein pair $(W, W')$ and twice-differentiable
  $f$ with bounded $f, f', f''$,
  $$|\mathbb{E}[f'(W) - W f(W)]| \le
    \|f'\|\,\mathbb{E}\left|1 - \frac{\mathbb{E}[(W' - W)^2 \mid W]}{2a}\right| +
    \frac{\|f''\|}{6a}\,\mathbb{E}|W' - W|^3,$$
  formulated with `ℝ≥0∞` `lintegral`s on the right-hand side so non-$L^3$ increments evaluate to
  `⊤` rather than junk 0.
* `sec3_3_eq3_18_wasserstein_proof` (`Sec3_3_eq3_18_wasserstein`): taking the supremum over
  `normalWassersteinClass` ($B_1 = \sqrt{2/\pi}, B_2 = 2$) via Theorem 3.1 bounds
  $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))$ with cubic coefficient $2 / (6a) = 1 / (3a)$.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-- Taylor expansion bound with Lagrange remainder for $C^2$ function $f$ with bounded $f, f''$:
antiderivative $F(w) = \int_0^w f(t)\,dt$ satisfies $|F(w)| \le B_0 |w|$ and
$|F(w') - F(w) - (w' - w) f(w) - \frac{1}{2}(w' - w)^2 f'(w)| \le \frac{B_2}{6} |w' - w|^3$. -/
lemma taylor_antideriv_bound {f : ℝ → ℝ} {B₀ B₂ : ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf_bdd : ∀ w, |f w| ≤ B₀) (hf''_bdd : ∀ w, |deriv (deriv f) w| ≤ B₂) :
    ∃ F : ℝ → ℝ, (∀ t, HasDerivAt F (f t) t) ∧ (∀ w, |F w| ≤ B₀ * |w|) ∧
      ∀ w w',
        |F w' - F w - (w' - w) * f w - (1 / 2) * (w' - w) ^ 2 * deriv f w| ≤
          (B₂ / 6) * |w' - w| ^ 3 := by
  have hB0_nn : 0 ≤ B₀ := (abs_nonneg (f 0)).trans (hf_bdd 0)
  have hB2_nn : 0 ≤ B₂ := (abs_nonneg (deriv (deriv f) 0)).trans (hf''_bdd 0)
  let F : ℝ → ℝ := fun w ↦ ∫ t in (0 : ℝ)..w, f t
  have hcont : Continuous f := hf1.continuous
  have hF_deriv : ∀ t, HasDerivAt F (f t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hF_bdd : ∀ w, |F w| ≤ B₀ * |w| := by
    intro w
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := w)
      (C := B₀) (f := f) (fun x _ ↦ by simpa only [Real.norm_eq_abs] using hf_bdd x)
    simpa only [F, Real.norm_eq_abs, sub_zero] using hnorm
  refine ⟨F, hF_deriv, hF_bdd, fun w w' ↦ ?_⟩
  let Φ : ℝ → ℝ := fun t ↦ F w' - F t - (w' - t) * f t - (1 / 2) * (w' - t) ^ 2 * deriv f t
  let Φ' : ℝ → ℝ := fun t ↦ -(1 / 2) * (w' - t) ^ 2 * deriv (deriv f) t
  let Ψ : ℝ → ℝ := fun t ↦ (w' - t) ^ 3
  let Ψ' : ℝ → ℝ := fun t ↦ -3 * (w' - t) ^ 2
  have hΦ : ∀ t, HasDerivAt Φ (Φ' t) t := by
    intro t
    have hd_sub : HasDerivAt (fun s ↦ w' - s) (-1) t := (hasDerivAt_id' t).const_sub w'
    have hd0 : HasDerivAt (fun s ↦ F w' - F s) (-f t) t := (hF_deriv t).const_sub (F w')
    have hd1 : HasDerivAt (fun s ↦ (w' - s) * f s) ((-1) * f t + (w' - t) * deriv f t) t :=
      hd_sub.fun_mul (hf1 t).hasDerivAt
    have hd_sq : HasDerivAt (fun s ↦ (w' - s) ^ 2) (↑(2 : ℕ) * (w' - t) ^ (2 - 1) * (-1)) t :=
      hd_sub.fun_pow 2
    have hd2 :
        HasDerivAt (fun s ↦ (1 / 2) * (w' - s) ^ 2 * deriv f s)
          (((1 / 2) * (↑(2 : ℕ) * (w' - t) ^ (2 - 1) * (-1))) * deriv f t +
            ((1 / 2) * (w' - t) ^ 2) * deriv (deriv f) t) t :=
      (hd_sq.const_mul (1 / 2)).fun_mul (hf2 t).hasDerivAt
    have hΦ'_eq :
        Φ' t =
          -f t - ((-1) * f t + (w' - t) * deriv f t) -
            (((1 / 2) * (↑(2 : ℕ) * (w' - t) ^ (2 - 1) * (-1))) * deriv f t +
              ((1 / 2) * (w' - t) ^ 2) * deriv (deriv f) t) := by
      dsimp only [Φ']
      push_cast
      ring
    rw [hΦ'_eq]
    exact (hd0.fun_sub hd1).fun_sub hd2
  have hΨ : ∀ t, HasDerivAt Ψ (Ψ' t) t := by
    intro t
    have hd_sub : HasDerivAt (fun s ↦ w' - s) (-1) t := (hasDerivAt_id' t).const_sub w'
    have hΨ'_eq : Ψ' t = ↑(3 : ℕ) * (w' - t) ^ (3 - 1) * (-1) := by
      dsimp only [Ψ']
      push_cast
      ring
    rw [hΨ'_eq]
    exact hd_sub.fun_pow 3
  have hΦ_cont : Continuous Φ := continuous_iff_continuousAt.mpr fun t ↦ (hΦ t).continuousAt
  have hΨ_cont : Continuous Ψ := continuous_iff_continuousAt.mpr fun t ↦ (hΨ t).continuousAt
  have hΦ_w' : Φ w' = 0 := by
    dsimp only [Φ]
    ring
  have hΨ_w' : Ψ w' = 0 := by
    dsimp only [Ψ]
    ring
  change |Φ w| ≤ (B₂ / 6) * |w' - w| ^ 3
  rcases lt_trichotomy w w' with hww' | hww' | hw'w
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hww' hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hc_ne : (w' - c) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hc.2.ne')
    have hfac : (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 = 0 := by
      have h0 : (Ψ w' - Ψ w) * Φ' c - (Φ w' - Φ w) * Ψ' c = 0 := sub_eq_zero.mpr hratio
      rw [hΦ_w', hΨ_w'] at h0
      dsimp only [Φ', Ψ', Ψ] at h0
      linarith [
        (by ring :
          (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 =
            -((0 - (w' - w) ^ 3) * (-(1 / 2) * (w' - c) ^ 2 * deriv (deriv f) c) -
              (0 - Φ w) * (-3 * (w' - c) ^ 2)))]
    have hΦw : Φ w = (1 / 6) * (w' - w) ^ 3 * deriv (deriv f) c := by
      have hlin := (mul_eq_zero.mp hfac).resolve_right hc_ne
      linarith
    calc
      |Φ w| = (1 / 6) * |w' - w| ^ 3 * |deriv (deriv f) c| := by
        rw [hΦw, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6), abs_pow]
      _ ≤ (1 / 6) * |w' - w| ^ 3 * B₂ :=
        mul_le_mul_of_nonneg_left (hf''_bdd c) (by positivity)
      _ = (B₂ / 6) * |w' - w| ^ 3 := by ring
  · subst hww'
    rw [hΦ_w', sub_self, abs_zero]
    positivity
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hw'w hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hc_ne : (w' - c) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hc.1.ne)
    have hfac : (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 = 0 := by
      have h0 : (Ψ w - Ψ w') * Φ' c - (Φ w - Φ w') * Ψ' c = 0 := sub_eq_zero.mpr hratio
      rw [hΦ_w', hΨ_w'] at h0
      dsimp only [Φ', Ψ', Ψ] at h0
      linarith [
        (by ring :
          (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 =
            ((w' - w) ^ 3 - 0) * (-(1 / 2) * (w' - c) ^ 2 * deriv (deriv f) c) -
              (Φ w - 0) * (-3 * (w' - c) ^ 2))]
    have hΦw : Φ w = (1 / 6) * (w' - w) ^ 3 * deriv (deriv f) c := by
      have hlin := (mul_eq_zero.mp hfac).resolve_right hc_ne
      linarith
    calc
      |Φ w| = (1 / 6) * |w' - w| ^ 3 * |deriv (deriv f) c| := by
        rw [hΦw, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6), abs_pow]
      _ ≤ (1 / 6) * |w' - w| ^ 3 * B₂ :=
        mul_le_mul_of_nonneg_left (hf''_bdd c) (by positivity)
      _ = (B₂ / 6) * |w' - w| ^ 3 := by ring

/-- Proof of display (3.18) (`\label{511}`, `SteinIntro.tex:1043-1046`):
for an $a$-Stein pair $(W, W')$ and twice-differentiable $f$ with bounded $f, f', f''$,
$|\mathbb{E}[f'(W) - W f(W)]| \le B_1\,\mathbb{E}|1 - \mathbb{E}[(W' - W)^2 \mid W]/(2a)| +
(B_2 / (6a))\,\mathbb{E}|W' - W|^3$. -/
theorem sec3_3_eq3_18_proof
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a B₀ B₁ B₂ : ℝ} {W W' : Ω → ℝ} {f : ℝ → ℝ}
    (hSP : IsSteinPair P a W W')
    (hf1 : Differentiable ℝ f)
    (hf2 : Differentiable ℝ (deriv f))
    (hf_bdd : ∀ w : ℝ, |f w| ≤ B₀)
    (hf'_bdd : ∀ w : ℝ, |deriv f w| ≤ B₁)
    (hf''_bdd : ∀ w : ℝ, |deriv (deriv f) w| ≤ B₂) :
    ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P| ≤
      ENNReal.ofReal B₁ *
          (∫⁻ ω,
            ENNReal.ofReal
              |1 - (P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
                  MeasurableSpace.comap W inferInstance] ω) / (2 * a)| ∂P) +
        ENNReal.ofReal (B₂ / (6 * a)) *
          ∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P := by
  rcases hSP with ⟨hExch, ha, ha_le1, hW_meas, hW_int, hCond⟩
  have hB0_nn : 0 ≤ B₀ := (abs_nonneg (f 0)).trans (hf_bdd 0)
  have hB1_nn : 0 ≤ B₁ := (abs_nonneg (deriv f 0)).trans (hf'_bdd 0)
  have hB2_nn : 0 ≤ B₂ := (abs_nonneg (deriv (deriv f) 0)).trans (hf''_bdd 0)
  set D : Ω → ℝ := fun ω ↦ W' ω - W ω
  set Q : Ω → ℝ := P[fun ω ↦ D ω ^ 2 | MeasurableSpace.comap W inferInstance]
  set M3 : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (|D ω| ^ 3) ∂P
  set S1 : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal |1 - Q ω / (2 * a)| ∂P
  -- If M3 = ⊤, bound holds unless B₂ = 0
  by_cases hM3_top : M3 = ⊤
  · by_cases hB2_zero : B₂ = 0
    · -- B₂ = 0 implies deriv (deriv f) = 0 everywhere, so deriv f is constant
      have hf''0 : ∀ w, deriv (deriv f) w = 0 := fun w ↦ by
        have := hf''_bdd w
        rw [hB2_zero] at this
        exact abs_nonpos_iff.mp this
      have hf'const : ∀ x, deriv f x = deriv f 0 := fun x ↦
        is_const_of_deriv_eq_zero (fun u ↦ hf2 u)
          (fun u ↦ hf''0 u) x 0
      have hf'0 : ∀ w, deriv f w = 0 := by
        intro w
        by_contra hne
        have hpos : 0 < |deriv f 0| := by
          have h_eq : deriv f 0 = deriv f w := (hf'const w).symm
          rw [h_eq]
          exact abs_pos.mpr hne
        have hgrow : ∀ x : ℝ, 0 < x → x * |deriv f 0| ≤ 2 * B₀ := fun x hx ↦ by
          obtain ⟨c, hc, hc_eq⟩ := exists_deriv_eq_slope f hx hf1.continuous.continuousOn
            (fun t _ ↦ (hf1 t).differentiableWithinAt)
          rw [hf'const c] at hc_eq
          have hdiff : f x - f 0 = x * deriv f 0 := by
            have hsub : x - 0 ≠ 0 := by linarith
            calc
              f x - f 0 = (x - 0) * ((f x - f 0) / (x - 0)) :=
                (mul_div_cancel₀ (f x - f 0) hsub).symm
              _ = (x - 0) * deriv f 0 := by rw [hc_eq]
              _ = x * deriv f 0 := by rw [sub_zero]
          have hle : |f x - f 0| ≤ B₀ + B₀ :=
            (abs_sub (f x) (f 0)).trans (add_le_add (hf_bdd x) (hf_bdd 0))
          rw [hdiff, abs_mul, abs_of_pos hx] at hle
          linarith
        have hx_choice : 0 < (2 * B₀ + 1) / |deriv f 0| := by positivity
        have hlim := hgrow ((2 * B₀ + 1) / |deriv f 0|) hx_choice
        rw [div_mul_cancel₀ _ hpos.ne'] at hlim
        linarith
      have hf_const : ∀ x, f x = f 0 := fun x ↦
        is_const_of_deriv_eq_zero (fun u ↦ hf1 u)
          (fun u ↦ hf'0 u) x 0
      have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
      have hm := hW_meas.comap_le
      have hMeanEq : ∫ ω, W ω ∂P = (1 - a) * ∫ ω, W ω ∂P := calc
        ∫ ω, W ω ∂P = ∫ ω, W' ω ∂P := hId.integral_eq
        _ = ∫ ω, P[W' | MeasurableSpace.comap W inferInstance] ω ∂P :=
          (integral_condExp (μ := P) (f := W') hm).symm
        _ = ∫ ω, (1 - a) * W ω ∂P := integral_congr_ae hCond
        _ = (1 - a) * ∫ ω, W ω ∂P := integral_const_mul (1 - a) W
      have hMean : ∫ ω, W ω ∂P = 0 := by
        have : a * ∫ ω, W ω ∂P = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left ha.ne'
      have hOp0 : (fun ω ↦ normalSteinOp f (W ω)) = fun ω ↦ - f 0 * W ω := by
        ext ω
        dsimp only [normalSteinOp]
        rw [hf'0 (W ω), zero_sub, hf_const (W ω)]
        ring
      rw [hOp0, integral_const_mul (-f 0) W, hMean, mul_zero, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
    · have hB2_pos : 0 < B₂ := lt_of_le_of_ne hB2_nn (Ne.symm hB2_zero)
      have hpos : 0 < B₂ / (6 * a) := div_pos hB2_pos (mul_pos (by norm_num) ha)
      rw [hM3_top]
      have hne : ENNReal.ofReal (B₂ / (6 * a)) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
      have h_top : ENNReal.ofReal (B₂ / (6 * a)) * ⊤ = ⊤ :=
        ENNReal.mul_top hne
      rw [h_top, add_top]
      exact le_top
  obtain ⟨F, hF_deriv, hF_bdd, hTaylor⟩ := taylor_antideriv_bound hf1 hf2 hf_bdd hf''_bdd
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'_int : Integrable W' P := hId.integrable_snd hW_int
  have hD_int : Integrable D P := hW'_int.sub' hW_int
  have hD_abs_asm : AEStronglyMeasurable (fun ω ↦ |D ω|) P := by
    simpa only [Real.norm_eq_abs] using hD_int.norm.aestronglyMeasurable
  have hD3_nn : 0 ≤ᵐ[P] fun ω ↦ |D ω| ^ 3 := Eventually.of_forall fun _ ↦ by positivity
  have hD3_int : Integrable (fun ω ↦ |D ω| ^ 3) P :=
    ⟨(continuous_pow 3).comp_aestronglyMeasurable hD_abs_asm,
      (hasFiniteIntegral_iff_ofReal hD3_nn).mpr (lt_top_iff_ne_top.mpr hM3_top)⟩
  have hM3_eq : M3 = ENNReal.ofReal (∫ ω, |D ω| ^ 3 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hD3_int hD3_nn).symm
  have hD2_le : ∀ ω, D ω ^ 2 ≤ 1 + |D ω| ^ 3 := by
    intro ω
    by_cases h : |D ω| ≤ 1
    · have hsq : D ω ^ 2 ≤ 1 := by
        calc D ω ^ 2 = |D ω| ^ 2 := (sq_abs (D ω)).symm
        _ ≤ 1 ^ 2 := sq_le_sq.mpr (by rwa [abs_abs, abs_one])
        _ = 1 := by norm_num
      linarith [show 0 ≤ |D ω| ^ 3 by positivity]
    · have h1 : 1 ≤ |D ω| := le_of_not_ge h
      have hsq : D ω ^ 2 = |D ω| ^ 2 := (sq_abs (D ω)).symm
      rw [hsq]
      have : |D ω| ^ 2 ≤ |D ω| ^ 3 := by
        calc |D ω| ^ 2 = |D ω| ^ 2 * 1 := (mul_one _).symm
        _ ≤ |D ω| ^ 2 * |D ω| := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = |D ω| ^ 3 := by ring
      linarith
  have hD2_int : Integrable (fun ω ↦ D ω ^ 2) P :=
    (integrable_const (1 : ℝ) |>.add hD3_int).mono'
      ((continuous_pow 2).comp_aestronglyMeasurable hD_int.aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hD2_le ω)
  have hF_cont : Continuous F := continuous_iff_continuousAt.mpr fun t ↦ (hF_deriv t).continuousAt
  have hFW_int : Integrable (fun ω ↦ F (W ω)) P :=
    (hW_int.norm.const_mul B₀).mono' (hF_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hF_bdd (W ω))
  have hFW'_int : Integrable (fun ω ↦ F (W' ω)) P :=
    (hW'_int.norm.const_mul B₀).mono'
      (hF_cont.comp_aestronglyMeasurable hW'_int.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hF_bdd (W' ω))
  have hFW_diff_zero : ∫ ω, (F (W' ω) - F (W ω)) ∂P = 0 := by
    have hFW_eq : ∫ ω, F (W ω) ∂P = ∫ ω, F (W' ω) ∂P :=
      (hId.comp hF_cont.measurable).integral_eq
    rw [integral_sub hFW'_int hFW_int, hFW_eq, sub_self]
  have hm := hW_meas.comap_le
  have hW_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] W :=
    (comap_measurable (m := inferInstance) W).stronglyMeasurable
  have hCondD :
      P[D | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ -a * W ω := by
    filter_upwards [condExp_sub hW'_int hW_int (MeasurableSpace.comap W inferInstance), hCond]
      with ω h1 h2
    change P[W' - W | MeasurableSpace.comap W inferInstance] ω = -a * W ω
    rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable hm hW_sm hW_int]
    ring
  have hfW_sm :
      StronglyMeasurable[MeasurableSpace.comap W inferInstance] (fun ω ↦ f (W ω)) :=
    (hf1.continuous.measurable.comp (comap_measurable (m := inferInstance) W)).stronglyMeasurable
  have hfW_asm : AEStronglyMeasurable (fun ω ↦ f (W ω)) P :=
    (hf1.continuous.measurable.comp hW_meas).aestronglyMeasurable
  have hWfW_int : Integrable (fun ω ↦ W ω * f (W ω)) P :=
    (hW_int.norm.mul_const B₀).mono' (hW_int.aestronglyMeasurable.mul hfW_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg (W ω)))
  have hDfW_int : Integrable (fun ω ↦ D ω * f (W ω)) P :=
    (hD_int.norm.mul_const B₀).mono' (hD_int.aestronglyMeasurable.mul hfW_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg (D ω)))
  have hCondDfW :
      P[D * (fun ω ↦ f (W ω)) | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        fun ω ↦ -a * (W ω * f (W ω)) := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_right hfW_sm hDfW_int hD_int, hCondD]
      with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    ring
  have hIntDfW : ∫ ω, D ω * f (W ω) ∂P = -a * ∫ ω, W ω * f (W ω) ∂P := calc
    ∫ ω, D ω * f (W ω) ∂P = ∫ ω, (D * fun ω ↦ f (W ω)) ω ∂P := rfl
    _ = ∫ ω, P[D * (fun ω ↦ f (W ω)) | MeasurableSpace.comap W inferInstance] ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, -a * (W ω * f (W ω)) ∂P := integral_congr_ae hCondDfW
    _ = -a * ∫ ω, W ω * f (W ω) ∂P := integral_const_mul (-a) (fun ω ↦ W ω * f (W ω))
  have hf'W_sm :
      StronglyMeasurable[MeasurableSpace.comap W inferInstance] (fun ω ↦ deriv f (W ω)) :=
    (hf2.continuous.measurable.comp (comap_measurable (m := inferInstance) W)).stronglyMeasurable
  have hf'W_asm : AEStronglyMeasurable (fun ω ↦ deriv f (W ω)) P :=
    (hf2.continuous.measurable.comp hW_meas).aestronglyMeasurable
  have hf'W_int : Integrable (fun ω ↦ deriv f (W ω)) P :=
    (integrable_const B₁).mono' hf'W_asm
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hf'_bdd (W ω))
  have hD2f'W_int : Integrable (fun ω ↦ D ω ^ 2 * deriv f (W ω)) P :=
    (hD2_int.norm.mul_const B₁).mono' (hD2_int.aestronglyMeasurable.mul hf'W_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg (D ω ^ 2)))
  have hQ_int : Integrable Q P := integrable_condExp
  have hCondD2f'W :
      P[(fun ω ↦ D ω ^ 2) * (fun ω ↦ deriv f (W ω)) |
          MeasurableSpace.comap W inferInstance] =ᵐ[P]
        fun ω ↦ Q ω * deriv f (W ω) :=
    condExp_mul_of_stronglyMeasurable_right hf'W_sm hD2f'W_int hD2_int
  have hIntD2f'W : ∫ ω, D ω ^ 2 * deriv f (W ω) ∂P = ∫ ω, Q ω * deriv f (W ω) ∂P := calc
    ∫ ω, D ω ^ 2 * deriv f (W ω) ∂P
      = ∫ ω, ((fun ω ↦ D ω ^ 2) * (fun ω ↦ deriv f (W ω))) ω ∂P := rfl
    _ = ∫ ω, P[(fun ω ↦ D ω ^ 2) * (fun ω ↦ deriv f (W ω)) |
          MeasurableSpace.comap W inferInstance] ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, Q ω * deriv f (W ω) ∂P := integral_congr_ae hCondD2f'W
  have hHalfD2f'W_int : Integrable (fun ω ↦ (1 / 2) * D ω ^ 2 * deriv f (W ω)) P := by
    simpa only [mul_assoc] using hD2f'W_int.const_mul (1 / 2)
  set R : Ω → ℝ :=
    fun ω ↦ F (W' ω) - F (W ω) - D ω * f (W ω) - (1 / 2) * D ω ^ 2 * deriv f (W ω)
  have hR_int : Integrable R P :=
    ((hFW'_int.sub' hFW_int).sub' hDfW_int).sub' hHalfD2f'W_int
  have hIntR :
      ∫ ω, R ω ∂P =
        a * ∫ ω, W ω * f (W ω) ∂P - (1 / 2) * ∫ ω, Q ω * deriv f (W ω) ∂P := by
    have hHalfEq : (fun ω ↦ (1 / 2) * D ω ^ 2 * deriv f (W ω)) =
        fun ω ↦ (1 / 2) * (D ω ^ 2 * deriv f (W ω)) := funext fun _ ↦ by ring
    dsimp only [R]
    rw [integral_sub ((hFW'_int.sub' hFW_int).sub' hDfW_int) hHalfD2f'W_int,
      integral_sub (hFW'_int.sub' hFW_int) hDfW_int,
      hFW_diff_zero, hIntDfW, hHalfEq,
      integral_const_mul (1 / 2) (fun ω ↦ D ω ^ 2 * deriv f (W ω)), hIntD2f'W]
    ring
  have hQf'W_int : Integrable (fun ω ↦ Q ω * deriv f (W ω)) P :=
    (hQ_int.norm.mul_const B₁).mono' (hQ_int.aestronglyMeasurable.mul hf'W_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg (Q ω)))
  set S : Ω → ℝ := fun ω ↦ (2 * a - Q ω) * deriv f (W ω)
  have hS_eq : S = fun ω ↦ (2 * a) * deriv f (W ω) - Q ω * deriv f (W ω) :=
    funext fun _ ↦ by ring
  have hS_int : Integrable S P := by
    rw [hS_eq]
    exact (hf'W_int.const_mul (2 * a)).sub' hQf'W_int
  have hSteinId :
      a * ∫ ω, normalSteinOp f (W ω) ∂P = (1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P := by
    have hOp : ∫ ω, normalSteinOp f (W ω) ∂P =
        ∫ ω, deriv f (W ω) ∂P - ∫ ω, W ω * f (W ω) ∂P :=
      integral_sub hf'W_int hWfW_int
    have hIntS : ∫ ω, S ω ∂P =
        (2 * a) * ∫ ω, deriv f (W ω) ∂P - ∫ ω, Q ω * deriv f (W ω) ∂P := by
      rw [hS_eq, integral_sub (hf'W_int.const_mul (2 * a)) hQf'W_int,
        integral_const_mul (2 * a) (fun ω ↦ deriv f (W ω))]
    rw [hOp, hIntS, hIntR]
    ring
  have hR_bound : |∫ ω, R ω ∂P| ≤ (B₂ / 6) * ∫ ω, |D ω| ^ 3 ∂P := by
    have h1 : |∫ ω, R ω ∂P| ≤ ∫ ω, |R ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    have hR_abs_int : Integrable (fun ω ↦ |R ω|) P := by
      simpa only [Real.norm_eq_abs] using hR_int.norm
    have h2 : ∫ ω, |R ω| ∂P ≤ ∫ ω, (B₂ / 6) * |D ω| ^ 3 ∂P :=
      integral_mono hR_abs_int (hD3_int.const_mul (B₂ / 6)) fun ω ↦ hTaylor (W ω) (W' ω)
    rw [integral_const_mul (B₂ / 6) (fun ω ↦ |D ω| ^ 3)] at h2
    exact h1.trans h2
  have hS_bound :
      |∫ ω, S ω ∂P| ≤ (2 * a) * (B₁ * ∫ ω, |1 - Q ω / (2 * a)| ∂P) := by
    have h1 : |∫ ω, S ω ∂P| ≤ ∫ ω, |S ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm S
    have hS_abs_int : Integrable (fun ω ↦ |S ω|) P := by
      simpa only [Real.norm_eq_abs] using hS_int.norm
    have hQ_scaled_int : Integrable (fun ω ↦ |1 - Q ω / (2 * a)|) P := by
      have h1a : Integrable (fun ω ↦ (1 : ℝ) - Q ω / (2 * a)) P :=
        (integrable_const 1).sub' (hQ_int.div_const (2 * a))
      simpa only [Real.norm_eq_abs] using h1a.norm
    have h2 : ∫ ω, |S ω| ∂P ≤ ∫ ω, (2 * a) * (B₁ * |1 - Q ω / (2 * a)|) ∂P := by
      refine integral_mono hS_abs_int ((hQ_scaled_int.const_mul B₁).const_mul (2 * a)) fun ω ↦ ?_
      dsimp only [S]
      rw [abs_mul]
      have hrew : 2 * a - Q ω = (2 * a) * (1 - Q ω / (2 * a)) := by
        have : 2 * a ≠ 0 := by linarith
        field_simp
      rw [hrew, abs_mul, abs_of_pos (by linarith : 0 < 2 * a), mul_assoc]
      have h1 : |1 - Q ω / (2 * a)| * |deriv f (W ω)| ≤ |1 - Q ω / (2 * a)| * B₁ :=
        mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg _)
      have h2 : (2 * a) * (|1 - Q ω / (2 * a)| * |deriv f (W ω)|) ≤
          (2 * a) * (|1 - Q ω / (2 * a)| * B₁) :=
        mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2 * a)
      have h3 : (2 * a) * (|1 - Q ω / (2 * a)| * B₁) =
          (2 * a) * (B₁ * |1 - Q ω / (2 * a)|) := by ring
      exact h2.trans_eq h3
    rw [integral_const_mul (2 * a), integral_const_mul B₁] at h2
    exact h1.trans h2
  have hMulLe :
      a * |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        a * (B₁ * ∫ ω, |1 - Q ω / (2 * a)| ∂P) + (B₂ / 6) * ∫ ω, |D ω| ^ 3 ∂P := by
    have hAbsEq : a * |∫ ω, normalSteinOp f (W ω) ∂P| =
        |(1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P| := by
      rw [← hSteinId, abs_mul, abs_of_pos ha]
    have hTri :
        |(1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P| ≤
          (1 / 2) * |∫ ω, S ω ∂P| + |∫ ω, R ω ∂P| := by
      have hSubLe :
          |(1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P| ≤
            |(1 / 2) * ∫ ω, S ω ∂P| + |∫ ω, R ω ∂P| :=
        abs_le.mpr
          ⟨by linarith [neg_abs_le ((1 / 2) * ∫ ω, S ω ∂P), le_abs_self (∫ ω, R ω ∂P)],
            by linarith [le_abs_self ((1 / 2) * ∫ ω, S ω ∂P), neg_abs_le (∫ ω, R ω ∂P)]⟩
      rwa [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hSubLe
    linarith [hS_bound, hR_bound]
  have hDivA :
      |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        B₁ * (∫ ω, |1 - Q ω / (2 * a)| ∂P) + (B₂ / (6 * a)) * ∫ ω, |D ω| ^ 3 ∂P := by
    have h_equiv :
        a * (B₁ * (∫ ω, |1 - Q ω / (2 * a)| ∂P) + (B₂ / (6 * a)) * ∫ ω, |D ω| ^ 3 ∂P) =
          a * (B₁ * ∫ ω, |1 - Q ω / (2 * a)| ∂P) + (B₂ / 6) * ∫ ω, |D ω| ^ 3 ∂P := by
      have : a * ((B₂ / (6 * a)) * ∫ ω, |D ω| ^ 3 ∂P) = (B₂ / 6) * ∫ ω, |D ω| ^ 3 ∂P := by
        calc
          a * ((B₂ / (6 * a)) * ∫ ω, |D ω| ^ 3 ∂P)
            = (a * (B₂ / (6 * a))) * ∫ ω, |D ω| ^ 3 ∂P := by ring
          _ = (B₂ / 6) * ∫ ω, |D ω| ^ 3 ∂P := by
            congr 1
            have : 6 * a ≠ 0 := mul_ne_zero (by norm_num) ha.ne'
            field_simp
      linarith
    refine le_of_mul_le_mul_left ?_ ha
    rw [h_equiv]
    exact hMulLe
  have hQ_scaled_int : Integrable (fun ω ↦ |1 - Q ω / (2 * a)|) P := by
    have h1a : Integrable (fun ω ↦ (1 : ℝ) - Q ω / (2 * a)) P :=
      (integrable_const 1).sub' (hQ_int.div_const (2 * a))
    simpa only [Real.norm_eq_abs] using h1a.norm
  have hS1_eq : S1 = ENNReal.ofReal (∫ ω, |1 - Q ω / (2 * a)| ∂P) := by
    have hnn : 0 ≤ᵐ[P] fun ω ↦ |1 - Q ω / (2 * a)| := Eventually.of_forall fun _ ↦ abs_nonneg _
    exact (ofReal_integral_eq_lintegral_ofReal hQ_scaled_int hnn).symm
  have hOF := ENNReal.ofReal_le_ofReal hDivA
  have hterm1_nn : 0 ≤ B₁ * ∫ ω, |1 - Q ω / (2 * a)| ∂P :=
    mul_nonneg hB1_nn (integral_nonneg fun _ ↦ abs_nonneg _)
  have hterm2_nn : 0 ≤ (B₂ / (6 * a)) * ∫ ω, |D ω| ^ 3 ∂P :=
    mul_nonneg (by positivity) (integral_nonneg fun _ ↦ by positivity)
  rw [ENNReal.ofReal_add hterm1_nn hterm2_nn] at hOF
  rw [ENNReal.ofReal_mul hB1_nn, ← hS1_eq, ENNReal.ofReal_mul (by positivity), ← hM3_eq] at hOF
  exact hOF

/-- Wasserstein corollary of display (3.18) (`\label{511}`, `SteinIntro.tex:1043-1048`):
specializing `sec3_3_eq3_18_proof` over `normalWassersteinClass` ($B_1 = \sqrt{2/\pi}, B_2 = 2$)
yields the $d_{\mathrm{W}}$ bound with cubic coefficient $2 / (6a) = 1 / (3a)$. -/
theorem sec3_3_eq3_18_wasserstein_proof
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ}
    (hSP : IsSteinPair P a W W')
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi)) *
          (∫⁻ ω,
            ENNReal.ofReal
              |1 - (P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
                  MeasurableSpace.comap W inferInstance] ω) / (2 * a)| ∂P) +
        ENNReal.ofReal (1 / (3 * a)) *
          ∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P := by
  have hW_meas : Measurable W := hSP.2.2.2.1
  have hWass :=
    wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P' hW_meas.aemeasurable hZ hZ_law
  refine hWass.trans ?_
  refine iSup₂_le fun f hf ↦ ?_
  rcases hf with ⟨hf1, hf2, hf_bdd, hf'_bdd, hf''_bdd⟩
  have h_eq18 := sec3_3_eq3_18_proof P hSP hf1 hf2 hf_bdd hf'_bdd hf''_bdd
  have hcoeff : (2 : ℝ) / (6 * a) = 1 / (3 * a) := by ring
  rw [hcoeff] at h_eq18
  exact h_eq18

end SteinMethod
