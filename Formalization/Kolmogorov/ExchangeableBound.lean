/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.Basic
import Formalization.Kolmogorov.ZeroBiasBound
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Exchangeable-Pair Kolmogorov Bound (`Formalization.Kolmogorov.ExchangeableBound`)

Proves Section 3.6.2 of Nathan Ross, *"Fundamentals of Stein's method"* (`Probability Surveys` 8,
2011; `arXiv:1109.1880v1`, `SteinIntro.tex:1745-1812`):

* `steinPair_integral_sq_sub_mul_indicator_Ioc_le` &
  `IsSteinPair.integral_sq_sub_mul_indicator_Ioc_le` (**Lemma 3.29** `\label{lem92}`,
  `SteinIntro.tex:1793-1798`, proved for general $0 < a$ per ruling `D7`):
  $\mathbb{E}[(W' - W)^2 \mathbb{I}[x < W \le x + \delta]] \le 3 \delta a$.
* `steinPair_kolmogorovDist_map_stdNormal_le` &
  `IsSteinPair.kolmogorovDist_map_stdNormal_le` (**Theorem 3.28** `\label{thm92}`,
  `SteinIntro.tex:1750-1755`, proved for general $0 < a$ per ruling `D7`; `ISSUE-3.25` proof note):
  $$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  \frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])}}{2a} +
  \frac{\delta^3}{2a} + \frac{3\delta}{2}.$$
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Exchangeable-Pair Expectation Helpers -/

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
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- Exchangeable-pair identity $\mathbb{E}[(W' - W)(g(W') - g(W))] = 2a\,\mathbb{E}[W g(W)]$ for
any continuous bounded function $g : \mathbb{R} \to \mathbb{R}$ and general $0 < a$
(`SteinIntro.tex:1758-1760, 1802-1803`; ruling `D7`). -/
theorem steinPair_integral_sub_mul_sub_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a B : ℝ} {W W' : Ω → ℝ} {g : ℝ → ℝ}
    (hExch : IsExchangeablePair P W W') (_ha : 0 < a)
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hg_cont : Continuous g) (hg_bdd : ∀ u : ℝ, |g u| ≤ B) :
    ∫ ω, (W' ω - W ω) * (g (W' ω) - g (W ω)) ∂P = 2 * a * ∫ ω, W ω * g (W ω) ∂P := by
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'2 : MemLp W' 2 P := hId.memLp_snd hW2
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  set D : Ω → ℝ := fun ω ↦ W' ω - W ω
  have hD_int : Integrable D P := hW'_int.sub' hW_int
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
  have hgW_sm :
      StronglyMeasurable[MeasurableSpace.comap W inferInstance] (fun ω ↦ g (W ω)) :=
    (hg_cont.measurable.comp (comap_measurable (m := inferInstance) W)).stronglyMeasurable
  have hgW_asm : AEStronglyMeasurable (fun ω ↦ g (W ω)) P :=
    (hg_cont.measurable.comp hW_meas).aestronglyMeasurable
  have hgW'_asm : AEStronglyMeasurable (fun ω ↦ g (W' ω)) P :=
    hg_cont.comp_aestronglyMeasurable hW'_int.aestronglyMeasurable
  have hDgW_int : Integrable (fun ω ↦ D ω * g (W ω)) P :=
    (hD_int.norm.mul_const B).mono' (hD_int.aestronglyMeasurable.mul hgW_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hg_bdd (W ω)) (abs_nonneg (D ω)))
  have hDgW'_int : Integrable (fun ω ↦ D ω * g (W' ω)) P :=
    (hD_int.norm.mul_const B).mono' (hD_int.aestronglyMeasurable.mul hgW'_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hg_bdd (W' ω)) (abs_nonneg (D ω)))
  have hDg_sum_int : Integrable (fun ω ↦ D ω * (g (W' ω) + g (W ω))) P :=
    (hDgW'_int.add hDgW_int).congr (Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply]; ring)
  have hAnti_zero : ∫ ω, D ω * (g (W' ω) + g (W ω)) ∂P = 0 := by
    let F : ℝ × ℝ → ℝ := fun p ↦ (p.2 - p.1) * (g p.2 + g p.1)
    have hF_meas : Measurable F :=
      (measurable_snd.sub measurable_fst).mul
        ((hg_cont.measurable.comp measurable_snd).add (hg_cont.measurable.comp measurable_fst))
    exact hExch.integral_antisymm_eq_zero hF_meas (fun u v ↦ by dsimp only [F]; ring)
  have hCondDgW :
      P[D * (fun ω ↦ g (W ω)) | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        fun ω ↦ -a * (W ω * g (W ω)) := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_right hgW_sm hDgW_int hD_int, hCondD]
      with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    ring
  have hIntDgW : ∫ ω, D ω * g (W ω) ∂P = -a * ∫ ω, W ω * g (W ω) ∂P := calc
    ∫ ω, D ω * g (W ω) ∂P = ∫ ω, (D * fun ω ↦ g (W ω)) ω ∂P := rfl
    _ = ∫ ω, P[D * (fun ω ↦ g (W ω)) | MeasurableSpace.comap W inferInstance] ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, -a * (W ω * g (W ω)) ∂P := integral_congr_ae hCondDgW
    _ = -a * ∫ ω, W ω * g (W ω) ∂P := integral_const_mul (-a) (fun ω ↦ W ω * g (W ω))
  have hdecomp : (fun ω ↦ D ω * (g (W' ω) - g (W ω))) =
      fun ω ↦ D ω * (g (W' ω) + g (W ω)) - 2 * (D ω * g (W ω)) :=
    funext fun _ ↦ by ring
  change ∫ ω, D ω * (g (W' ω) - g (W ω)) ∂P = 2 * a * ∫ ω, W ω * g (W ω) ∂P
  rw [hdecomp, integral_sub hDg_sum_int (hDgW_int.const_mul 2), hAnti_zero,
    integral_const_mul 2 (fun ω ↦ D ω * g (W ω)), hIntDgW]
  ring

/-! ### Section 2: Lemma 3.29 (`Lem3_29`) -/

private noncomputable def kolmExchRamp (x δ w : ℝ) : ℝ :=
  max (x - δ) (min (x + 2 * δ) w) - (x + δ / 2)

private lemma continuous_kolmExchRamp (x δ : ℝ) : Continuous (kolmExchRamp x δ) := by
  unfold kolmExchRamp
  fun_prop

private lemma monotone_kolmExchRamp (x δ : ℝ) : Monotone (kolmExchRamp x δ) := by
  intro u v huv
  unfold kolmExchRamp
  exact sub_le_sub_right (max_le_max_left _ (min_le_min_left _ huv)) _

private lemma abs_kolmExchRamp_le (x : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (w : ℝ) :
    |kolmExchRamp x δ w| ≤ 3 * δ / 2 := by
  unfold kolmExchRamp
  have hlo : x - δ ≤ max (x - δ) (min (x + 2 * δ) w) := le_max_left _ _
  have hhi : max (x - δ) (min (x + 2 * δ) w) ≤ x + 2 * δ :=
    max_le (by linarith) (min_le_left _ _)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma sq_sub_mul_indicator_Ioc_le_kolmExchRamp (x : ℝ) {δ : ℝ} (_hδ : 0 ≤ δ)
    {w w' : ℝ} (hdiff : |w' - w| ≤ δ) :
    (w' - w) ^ 2 * (Ioc x (x + δ)).indicator 1 w ≤
      (w' - w) * (kolmExchRamp x δ w' - kolmExchRamp x δ w) := by
  by_cases hw : w ∈ Ioc x (x + δ)
  · rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one]
    obtain ⟨hw1, hw2⟩ := mem_Ioc.mp hw
    obtain ⟨hd1, hd2⟩ := abs_le.mp hdiff
    have hgw : kolmExchRamp x δ w = w - (x + δ / 2) := by
      unfold kolmExchRamp
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    have hgw' : kolmExchRamp x δ w' = w' - (x + δ / 2) := by
      unfold kolmExchRamp
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    rw [hgw, hgw']
    exact le_of_eq (by ring)
  · rw [Set.indicator_of_notMem hw, mul_zero]
    rcases le_total w w' with hle | hge
    · exact mul_nonneg (sub_nonneg.mpr hle)
        (sub_nonneg.mpr (monotone_kolmExchRamp x δ hle))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hge)
        (sub_nonpos.mpr (monotone_kolmExchRamp x δ hge))

/-- **Lemma 3.29** (general $0 < a$ library version, `\label{lem92}`, `SteinIntro.tex:1793-1798`;
ruling `D7`): if $(W, W')$ is an exchangeable pair with $0 < a$, measurable $W$,
$\mathbb{E}[W' \mid W] = (1 - a) W$ a.s., $\operatorname{Var}(W) = 1$, and $|W' - W| \le \delta$
almost surely, then $\mathbb{E}[(W' - W)^2 \mathbb{I}[x < W \le x + \delta]] \le 3 \delta a$ for
all $x \in \mathbb{R}$. -/
theorem steinPair_integral_sq_sub_mul_indicator_Ioc_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a δ : ℝ} {W W' : Ω → ℝ} (x : ℝ)
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hvar : ProbabilityTheory.variance W P = 1)
    (hδ : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ) :
    ∫ ω, (W' ω - W ω) ^ 2 * (Ioc x (x + δ)).indicator 1 (W ω) ∂P ≤ 3 * δ * a := by
  have : (ae P).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero P)
  obtain ⟨ω₀, hω₀⟩ := hδ.exists
  have hδ_nn : 0 ≤ δ := (abs_nonneg _).trans hω₀
  have hW2 : MemLp W 2 P :=
    ProbabilityTheory.memLp_two_of_variance_ne_zero hW_meas.aestronglyMeasurable
      (by rw [hvar]; exact one_ne_zero)
  obtain ⟨hMean, _⟩ := steinPair_integral_eq_zero_and_sq_sub_eq P hExch ha hW_meas hW2 hCond
  have hW'2 : MemLp W' 2 P := hExch.fst_identDistrib_snd.memLp_snd hW2
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  have hD_int : Integrable (fun ω ↦ W' ω - W ω) P := hW'_int.sub' hW_int
  have hD_sq_int : Integrable (fun ω ↦ (W' ω - W ω) ^ 2) P := (hW'2.sub hW2).integrable_sq
  set g : ℝ → ℝ := kolmExchRamp x δ
  have hg_cont : Continuous g := continuous_kolmExchRamp x δ
  have hg_bdd : ∀ u : ℝ, |g u| ≤ 3 * δ / 2 := abs_kolmExchRamp_le x hδ_nn
  have hlhs_int : Integrable (fun ω ↦ (W' ω - W ω) ^ 2 * (Ioc x (x + δ)).indicator 1 (W ω)) P := by
    have hind_meas : Measurable ((Ioc x (x + δ)).indicator (1 : ℝ → ℝ)) :=
      measurable_one.indicator measurableSet_Ioc
    refine hD_sq_int.norm.mono'
      (hD_sq_int.aestronglyMeasurable.mul (hind_meas.comp hW_meas).aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    by_cases hw : W ω ∈ Ioc x (x + δ) <;> simp [hw, sq_nonneg]
  have hrhs_int : Integrable (fun ω ↦ (W' ω - W ω) * (g (W' ω) - g (W ω))) P := by
    have hg_sub_asm : AEStronglyMeasurable (fun ω ↦ g (W' ω) - g (W ω)) P :=
      (hg_cont.comp_aestronglyMeasurable hW'_int.aestronglyMeasurable).sub
        (hg_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable)
    refine (hD_int.norm.mul_const (3 * δ)).mono'
      (hD_int.aestronglyMeasurable.mul hg_sub_asm) (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    have hgb : |g (W' ω) - g (W ω)| ≤ 3 * δ := by
      calc |g (W' ω) - g (W ω)| ≤ |g (W' ω)| + |g (W ω)| := abs_sub _ _
        _ ≤ 3 * δ / 2 + 3 * δ / 2 := add_le_add (hg_bdd (W' ω)) (hg_bdd (W ω))
        _ = 3 * δ := by ring
    exact mul_le_mul_of_nonneg_left hgb (abs_nonneg _)
  have hint_le : ∫ ω, (W' ω - W ω) ^ 2 * (Ioc x (x + δ)).indicator 1 (W ω) ∂P ≤
      ∫ ω, (W' ω - W ω) * (g (W' ω) - g (W ω)) ∂P := by
    refine integral_mono_ae hlhs_int hrhs_int ?_
    filter_upwards [hδ] with ω hω
    exact sq_sub_mul_indicator_Ioc_le_kolmExchRamp x hδ_nn hω
  have hexch_eq := steinPair_integral_sub_mul_sub_eq P hExch ha hW_meas hW2 hCond hg_cont hg_bdd
  have hWg_int : Integrable (fun ω ↦ W ω * g (W ω)) P :=
    (hW_int.norm.mul_const (3 * δ / 2)).mono'
      (hW_int.aestronglyMeasurable.mul
        (hg_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable))
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hg_bdd (W ω)) (abs_nonneg (W ω)))
  have hW_abs_int : Integrable (fun ω ↦ |W ω|) P := by
    simpa only [Real.norm_eq_abs] using hW_int.norm
  have hWg_le : ∫ ω, W ω * g (W ω) ∂P ≤ 3 * δ / 2 := by
    have h1 : ∫ ω, W ω * g (W ω) ∂P ≤ ∫ ω, |W ω| * (3 * δ / 2) ∂P := by
      refine integral_mono hWg_int (hW_abs_int.mul_const (3 * δ / 2)) fun ω ↦ ?_
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg_bdd (W ω)) (abs_nonneg (W ω))
    rw [integral_mul_const] at h1
    have hW1 := integral_abs_le_one_of_integral_eq_zero_of_variance_eq_one P hW2 hMean hvar
    have hmul := mul_le_mul_of_nonneg_right hW1 (by positivity : 0 ≤ 3 * δ / 2)
    linarith
  have h2a_le : 2 * a * ∫ ω, W ω * g (W ω) ∂P ≤ 3 * δ * a := by
    have h := mul_le_mul_of_nonneg_left hWg_le (by positivity : 0 ≤ 2 * a)
    linarith
  exact hint_le.trans (hexch_eq.trans_le h2a_le)

/-- **Lemma 3.29** (`\label{lem92}`, `SteinIntro.tex:1793-1798`): `IsSteinPair` specialization of
`steinPair_integral_sq_sub_mul_indicator_Ioc_le`. -/
theorem IsSteinPair.integral_sq_sub_mul_indicator_Ioc_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a δ : ℝ} {W W' : Ω → ℝ} (x : ℝ)
    (hSP : IsSteinPair P a W W')
    (hvar : ProbabilityTheory.variance W P = 1)
    (hδ : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ) :
    ∫ ω, (W' ω - W ω) ^ 2 * (Ioc x (x + δ)).indicator 1 (W ω) ∂P ≤ 3 * δ * a := by
  rcases hSP with ⟨hExch, ha, _, hW_meas, _, hCond⟩
  exact steinPair_integral_sq_sub_mul_indicator_Ioc_le P x hExch ha hW_meas hCond hvar hδ

/-! ### Section 3: Analytic Remainder Identities and Theorem 3.28 (`Thm3_28`) -/

private noncomputable def kolmMulAntideriv (x u : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..u, z * normalSteinSolKolm x z

private lemma hasDerivAt_kolmMulAntideriv (x u : ℝ) :
    HasDerivAt (kolmMulAntideriv x) (u * normalSteinSolKolm x u) u := by
  have hcont : Continuous (fun z : ℝ ↦ z * normalSteinSolKolm x z) :=
    continuous_id.mul (continuous_normalSteinSolKolm x)
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 u)
    (hcont.stronglyMeasurableAtFilter volume (𝓝 u)) hcont.continuousAt

private lemma continuous_kolmMulAntideriv (x : ℝ) : Continuous (kolmMulAntideriv x) :=
  continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_kolmMulAntideriv x u).continuousAt

private lemma hasDerivAt_min_of_ne (x : ℝ) {c : ℝ} (hc : c ≠ x) :
    HasDerivAt (fun u : ℝ ↦ min x u) ((Iic x).indicator 1 c) c := by
  rcases lt_or_gt_of_ne hc with hlt | hgt
  · have hcx : c ∈ Iic x := mem_Iic.mpr hlt.le
    rw [Set.indicator_of_mem hcx, Pi.one_apply]
    refine (hasDerivAt_id c).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hlt] with u hu
    exact min_eq_right (mem_Iio.mp hu).le
  · have hcx : c ∉ Iic x := fun h ↦ not_lt_of_ge (mem_Iic.mp h) hgt
    rw [Set.indicator_of_notMem hcx]
    refine (hasDerivAt_const c x).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hgt] with u hu
    exact min_eq_left (mem_Ioi.mp hu).le

private lemma normalSteinSolKolm_sub_eq (x w w' : ℝ) :
    normalSteinSolKolm x w' - normalSteinSolKolm x w =
      (kolmMulAntideriv x w' - kolmMulAntideriv x w) + (min x w' - min x w) -
        (w' - w) * stdNormalCDF x := by
  set K : ℝ → ℝ := fun u ↦
    normalSteinSolKolm x u - kolmMulAntideriv x u - min x u + u * stdNormalCDF x
  have hK_cont : Continuous K := by
    have h1 : Continuous (normalSteinSolKolm x) := continuous_normalSteinSolKolm x
    have h2 : Continuous (kolmMulAntideriv x) := continuous_kolmMulAntideriv x
    have h3 : Continuous (fun u : ℝ ↦ min x u) := continuous_const.min continuous_id
    have h4 : Continuous (fun u : ℝ ↦ u * stdNormalCDF x) := continuous_id.mul continuous_const
    exact ((h1.sub h2).sub h3).add h4
  have hK_deriv : ∀ c : ℝ, c ≠ x → HasDerivAt K 0 c := fun c hc ↦ by
    have hd1 := hasDerivAt_normalSteinSolKolm_of_ne x hc
    have hd2 := hasDerivAt_kolmMulAntideriv x c
    have hd3 := hasDerivAt_min_of_ne x hc
    have hd4 : HasDerivAt (fun u : ℝ ↦ u * stdNormalCDF x) (1 * stdNormalCDF x) c :=
      (hasDerivAt_id c).mul_const (stdNormalCDF x)
    convert ((hd1.sub hd2).sub hd3).add hd4 using 1
    ring
  have hno_x : ∀ a b : ℝ, a < b → (∀ c ∈ Ioo a b, c ≠ x) → K b = K a := by
    intro a b hab hne
    obtain ⟨c, _, hslope⟩ := exists_hasDerivAt_eq_slope K (fun _ ↦ 0) hab hK_cont.continuousOn
      fun c hc ↦ hK_deriv c (hne c hc)
    have hsub : K b - K a = 0 :=
      (div_eq_zero_iff.mp hslope.symm).resolve_right (sub_ne_zero.mpr hab.ne')
    linarith
  have hord : ∀ a b : ℝ, a ≤ b → K b = K a := by
    intro a b hab
    rcases hab.eq_or_lt with rfl | hlt
    · rfl
    · by_cases hbx : b ≤ x
      · exact hno_x a b hlt fun c hc ↦ (hc.2.trans_le hbx).ne
      · by_cases hxa : x ≤ a
        · exact hno_x a b hlt fun c hc ↦ (hxa.trans_lt hc.1).ne'
        · push Not at hbx hxa
          exact (hno_x x b hbx fun c hc ↦ hc.1.ne').trans (hno_x a x hxa fun c hc ↦ hc.2.ne)
  have hK_eq : K w' = K w := by
    rcases le_total w w' with hww' | hw'w
    · exact hord w w' hww'
    · exact (hord w' w hw'w).symm
  dsimp only [K] at hK_eq
  linarith

private lemma abs_kolmMulAntideriv_sub_le (x w w' : ℝ) :
    |(kolmMulAntideriv x w' - kolmMulAntideriv x w) -
        (w' - w) * (w * normalSteinSolKolm x w)| ≤
      (|w| + Real.sqrt (2 * Real.pi) / 4) * ((w' - w) ^ 2 / 2) := by
  set f := normalSteinSolKolm x
  set M : ℝ := |w| + Real.sqrt (2 * Real.pi) / 4
  set Φ : ℝ → ℝ := fun t ↦ (kolmMulAntideriv x t - kolmMulAntideriv x w) - (t - w) * (w * f w)
  set Φ' : ℝ → ℝ := fun t ↦ t * f t - w * f w
  set Ψ : ℝ → ℝ := fun t ↦ (t - w) ^ 2 / 2
  set Ψ' : ℝ → ℝ := fun t ↦ t - w
  have hΦ : ∀ t : ℝ, HasDerivAt Φ (Φ' t) t := fun t ↦ by
    have hd1 : HasDerivAt (fun u ↦ kolmMulAntideriv x u - kolmMulAntideriv x w) (t * f t) t :=
      (hasDerivAt_kolmMulAntideriv x t).sub_const _
    have hd2 : HasDerivAt (fun u ↦ (u - w) * (w * f w)) (1 * (w * f w)) t :=
      ((hasDerivAt_id t).sub_const w).mul_const (w * f w)
    have hΦ'_eq : Φ' t = t * f t - 1 * (w * f w) := by dsimp only [Φ']; ring
    rw [hΦ'_eq]
    exact hd1.fun_sub hd2
  have hΨ : ∀ t : ℝ, HasDerivAt Ψ (Ψ' t) t := fun t ↦ by
    have hd : HasDerivAt (fun u ↦ (u - w) ^ 2 / 2) ((2 * (t - w) ^ (2 - 1) * 1) / 2) t :=
      (((hasDerivAt_id t).sub_const w).pow 2).div_const 2
    convert hd using 1
    ring
  have hΦ_cont : Continuous Φ := continuous_iff_continuousAt.mpr fun t ↦ (hΦ t).continuousAt
  have hΨ_cont : Continuous Ψ := continuous_iff_continuousAt.mpr fun t ↦ (hΨ t).continuousAt
  have hΦ_w : Φ w = 0 := by simp [Φ]
  have hΨ_w : Ψ w = 0 := by simp [Ψ]
  have hΦ'_le : ∀ c : ℝ, |Φ' c| ≤ M * |Ψ' c| := fun c ↦ by
    have h := abs_mul_normalSteinSolKolm_sub_le x (c - w) 0 w
    have hsimp : (w + (c - w)) * f (w + (c - w)) - (w + 0) * f (w + 0) = Φ' c := by
      have hw : w + (c - w) = c := by ring
      rw [hw, add_zero]
    rw [hsimp, abs_zero, add_zero] at h
    exact h
  change |Φ w'| ≤ M * Ψ w'
  rcases lt_trichotomy w w' with hlt | rfl | hgt
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hlt hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hpos : 0 < |Ψ' c| := abs_pos.mpr (sub_ne_zero.mpr hc.1.ne')
    have habs_eq : |Φ w'| * |Ψ' c| = Ψ w' * |Φ' c| := by
      have h0 := congrArg abs hratio
      rw [hΦ_w, hΨ_w, sub_zero, sub_zero, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ Ψ w')] at h0
      exact h0.symm
    have hmul_le : |Φ w'| * |Ψ' c| ≤ (M * Ψ w') * |Ψ' c| := by
      calc |Φ w'| * |Ψ' c| = Ψ w' * |Φ' c| := habs_eq
        _ ≤ Ψ w' * (M * |Ψ' c|) := mul_le_mul_of_nonneg_left (hΦ'_le c) (by positivity)
        _ = (M * Ψ w') * |Ψ' c| := by ring
    exact le_of_mul_le_mul_right hmul_le hpos
  · simp [hΦ_w, hΨ_w]
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hgt hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hpos : 0 < |Ψ' c| := abs_pos.mpr (sub_ne_zero.mpr hc.2.ne)
    have habs_eq : |Φ w'| * |Ψ' c| = Ψ w' * |Φ' c| := by
      have h0 := congrArg abs hratio
      rw [hΦ_w, hΨ_w, zero_sub, zero_sub, abs_mul, abs_mul, abs_neg, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ Ψ w')] at h0
      exact h0.symm
    have hmul_le : |Φ w'| * |Ψ' c| ≤ (M * Ψ w') * |Ψ' c| := by
      calc |Φ w'| * |Ψ' c| = Ψ w' * |Φ' c| := habs_eq
        _ ≤ Ψ w' * (M * |Ψ' c|) := mul_le_mul_of_nonneg_left (hΦ'_le c) (by positivity)
        _ = (M * Ψ w') * |Ψ' c| := by ring
    exact le_of_mul_le_mul_right hmul_le hpos

private lemma indicator_min_remainder_bounds (x : ℝ) {δ : ℝ} {w w' : ℝ} (hdiff : |w' - w| ≤ δ) :
    -((w' - w) ^ 2 * (Ioc x (x + δ)).indicator 1 w) ≤
        (w' - w) * ((w' - w) * (Iic x).indicator 1 w - (min x w' - min x w)) ∧
      (w' - w) * ((w' - w) * (Iic x).indicator 1 w - (min x w' - min x w)) ≤
        (w' - w) ^ 2 * (Ioc (x - δ) x).indicator 1 w := by
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdiff
  have hnn_lo : 0 ≤ (w' - w) ^ 2 * (Ioc x (x + δ)).indicator 1 w := by
    by_cases hw : w ∈ Ioc x (x + δ) <;> simp [hw, sq_nonneg]
  have hnn_hi : 0 ≤ (w' - w) ^ 2 * (Ioc (x - δ) x).indicator 1 w := by
    by_cases hw : w ∈ Ioc (x - δ) x <;> simp [hw, sq_nonneg]
  by_cases hw : w ≤ x
  · have hwx : w ∈ Iic x := mem_Iic.mpr hw
    rw [Set.indicator_of_mem hwx, Pi.one_apply, mul_one, min_eq_right hw]
    by_cases hw' : w' ≤ x
    · rw [min_eq_right hw', sub_self, mul_zero]
      exact ⟨by linarith, hnn_hi⟩
    · push Not at hw'
      rw [min_eq_left hw'.le]
      have hmem : w ∈ Ioc (x - δ) x := mem_Ioc.mpr ⟨by linarith, hw⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      have hmid_nn : 0 ≤ (w' - w) * ((w' - w) - (x - w)) :=
        mul_nonneg (by linarith) (by linarith)
      have hmid_le : (w' - w) * ((w' - w) - (x - w)) ≤ (w' - w) ^ 2 := by nlinarith
      exact ⟨by linarith, hmid_le⟩
  · have hwx : w ∉ Iic x := hw
    push Not at hw
    rw [Set.indicator_of_notMem hwx, mul_zero, zero_sub, min_eq_left hw.le]
    by_cases hw' : w' ≤ x
    · rw [min_eq_right hw']
      have hmem : w ∈ Ioc x (x + δ) := mem_Ioc.mpr ⟨hw, by linarith⟩
      rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      have hmid_np : (w' - w) * -(w' - x) ≤ 0 := by nlinarith
      have hmid_ge : -(w' - w) ^ 2 ≤ (w' - w) * -(w' - x) := by nlinarith
      exact ⟨hmid_ge, hmid_np.trans hnn_hi⟩
    · push Not at hw'
      rw [min_eq_left hw'.le, sub_self, neg_zero, mul_zero]
      exact ⟨by linarith, hnn_hi⟩

/-- **Theorem 3.28** (general $0 < a$ library version, `\label{thm92}`, `SteinIntro.tex:1750-1755`;
ruling `D7`, `ISSUE-3.25` proof note): if $(W, W')$ is an exchangeable pair with $0 < a$,
measurable $W$, $\mathbb{E}[W' \mid W] = (1 - a) W$ a.s., $\operatorname{Var}(W) = 1$, and
$|W' - W| \le \delta$ almost surely, and $Z \sim \mathcal{N}(0, 1)$, then
$$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])}}{2a} +
\frac{\delta^3}{2a} + \frac{3\delta}{2}.$$

Proof note (`ISSUE-3.25`): obtaining denominator $2a$ (rather than $a$) in the first error term at
`SteinIntro.tex:1768` uses the sharp left-derivative bound $|D_- f_x(w)| \le 1$
(`abs_derivWithin_Iic_normalSteinSolKolm_le_one`, CGS 2011 Lemma 2.3) rather than the looser bound
$\|f_x'\| \le 2$ printed in Lemma 3.25; the theorem holds as printed. -/
theorem steinPair_kolmogorovDist_map_stdNormal_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a δ : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hvar : ProbabilityTheory.variance W P = 1)
    (hδ : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (2 * a) +
      ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2) := by
  set D : Ω → ℝ := fun ω ↦ W' ω - W ω
  set Q : Ω → ℝ := P[fun ω ↦ D ω ^ 2 | MeasurableSpace.comap W inferInstance]
  set V : ℝ≥0∞ := ProbabilityTheory.evariance Q P
  rcases eq_or_ne V ⊤ with hV_top | hV_ne_top
  · have hV_rpow : V ^ (1 / 2 : ℝ) = ⊤ :=
      (ENNReal.rpow_eq_top_iff_of_pos (by positivity)).mpr hV_top
    rw [hV_rpow, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, top_add]
    exact le_top
  have : (ae P).NeBot := ae_neBot.mpr (IsProbabilityMeasure.ne_zero P)
  obtain ⟨ω₀, hω₀⟩ := hδ.exists
  have hδ_nn : 0 ≤ δ := (abs_nonneg _).trans hω₀
  have hW2 : MemLp W 2 P :=
    ProbabilityTheory.memLp_two_of_variance_ne_zero hW_meas.aestronglyMeasurable
      (by rw [hvar]; exact one_ne_zero)
  obtain ⟨hMean, hSqDiff_var⟩ :=
    steinPair_integral_eq_zero_and_sq_sub_eq P hExch ha hW_meas hW2 hCond
  have hSqDiff : ∫ ω, D ω ^ 2 ∂P = 2 * a := by
    dsimp only [D]
    rw [hSqDiff_var, hvar, mul_one]
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'2 : MemLp W' 2 P := hId.memLp_snd hW2
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  have hD_int : Integrable D P := hW'_int.sub' hW_int
  have hD_sq_int : Integrable (fun ω ↦ D ω ^ 2) P := (hW'2.sub hW2).integrable_sq
  have hm := hW_meas.comap_le
  have hQ_int : Integrable Q P := integrable_condExp
  have hQ_mean : ∫ ω, Q ω ∂P = 2 * a := by
    dsimp only [Q]
    rw [integral_condExp hm, hSqDiff]
  have hQ2 : MemLp Q 2 P :=
    (ProbabilityTheory.evariance_lt_top_iff_memLp hQ_int.aestronglyMeasurable).mp hV_ne_top.lt_top
  have hV_eq : V ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q P)) := by
    dsimp only [V]
    rw [← ProbabilityTheory.ofReal_variance hQ2,
      ENNReal.ofReal_rpow_of_nonneg (ProbabilityTheory.variance_nonneg Q P) (by positivity),
      ← Real.sqrt_eq_rpow]
  rw [kolmogorovDist_map_stdNormal_eq_iSup_normalSteinOpLeft P P' hW_meas.aemeasurable hZ hZ_law]
  refine iSup_le fun x ↦ ?_
  set f := normalSteinSolKolm x
  set f'L : ℝ → ℝ := fun w ↦ derivWithin f (Iic w) w
  have hf_cont : Continuous f := continuous_normalSteinSolKolm x
  have hf_bdd : ∀ u : ℝ, |f u| ≤ Real.sqrt (Real.pi / 2) := abs_normalSteinSolKolm_le x
  have hf'L_eq : ∀ w : ℝ, f'L w = w * f w + (Iic x).indicator 1 w - stdNormalCDF x := fun w ↦ by
    have hd := (hasDerivWithinAt_Iic_normalSteinSolKolm x w).derivWithin (uniqueDiffWithinAt_Iic w)
    simpa only [f'L, f] using hd
  have hf'L_meas : Measurable f'L := by
    have heq : f'L = fun w ↦ w * f w + (Iic x).indicator 1 w - stdNormalCDF x := funext hf'L_eq
    rw [heq]
    exact ((measurable_id.mul hf_cont.measurable).add
      (measurable_one.indicator measurableSet_Iic)).sub measurable_const
  have hf'L_bdd : ∀ w : ℝ, |f'L w| ≤ 1 := abs_derivWithin_Iic_normalSteinSolKolm_le_one x
  have hf'LW_sm :
      StronglyMeasurable[MeasurableSpace.comap W inferInstance] (fun ω ↦ f'L (W ω)) :=
    (hf'L_meas.comp (comap_measurable (m := inferInstance) W)).stronglyMeasurable
  have hf'LW_asm : AEStronglyMeasurable (fun ω ↦ f'L (W ω)) P :=
    (hf'L_meas.comp hW_meas).aestronglyMeasurable
  have hf'LW_int : Integrable (fun ω ↦ f'L (W ω)) P :=
    (integrable_const 1).mono' hf'LW_asm
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hf'L_bdd (W ω))
  have hWfW_int : Integrable (fun ω ↦ W ω * f (W ω)) P :=
    (hW_int.norm.mul_const (Real.sqrt (Real.pi / 2))).mono'
      (hW_int.aestronglyMeasurable.mul
        (hf_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable))
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg (W ω)))
  have hD2f'L_int : Integrable (fun ω ↦ D ω ^ 2 * f'L (W ω)) P :=
    hD_sq_int.norm.mono' (hD_sq_int.aestronglyMeasurable.mul hf'LW_asm)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (hf'L_bdd (W ω)) (abs_nonneg _)).trans (by rw [mul_one]))
  have hQf'L_int : Integrable (fun ω ↦ Q ω * f'L (W ω)) P :=
    hQ_int.norm.mono' (hQ_int.aestronglyMeasurable.mul hf'LW_asm)
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (hf'L_bdd (W ω)) (abs_nonneg _)).trans (by rw [mul_one]))
  have hIntD2f'L : ∫ ω, D ω ^ 2 * f'L (W ω) ∂P = ∫ ω, Q ω * f'L (W ω) ∂P := calc
    ∫ ω, D ω ^ 2 * f'L (W ω) ∂P
      = ∫ ω, ((fun ω ↦ D ω ^ 2) * (fun ω ↦ f'L (W ω))) ω ∂P := rfl
    _ = ∫ ω, P[(fun ω ↦ D ω ^ 2) * (fun ω ↦ f'L (W ω)) |
          MeasurableSpace.comap W inferInstance] ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, Q ω * f'L (W ω) ∂P :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_right hf'LW_sm hD2f'L_int hD_sq_int)
  have hDf_int : Integrable (fun ω ↦ D ω * (f (W' ω) - f (W ω))) P := by
    have hf_sub_asm : AEStronglyMeasurable (fun ω ↦ f (W' ω) - f (W ω)) P :=
      (hf_cont.comp_aestronglyMeasurable hW'_int.aestronglyMeasurable).sub
        (hf_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable)
    refine (hD_int.norm.mul_const (2 * Real.sqrt (Real.pi / 2))).mono'
      (hD_int.aestronglyMeasurable.mul hf_sub_asm) (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    have hfb : |f (W' ω) - f (W ω)| ≤ 2 * Real.sqrt (Real.pi / 2) := by
      calc |f (W' ω) - f (W ω)| ≤ |f (W' ω)| + |f (W ω)| := abs_sub _ _
        _ ≤ Real.sqrt (Real.pi / 2) + Real.sqrt (Real.pi / 2) :=
            add_le_add (hf_bdd (W' ω)) (hf_bdd (W ω))
        _ = 2 * Real.sqrt (Real.pi / 2) := by ring
    exact mul_le_mul_of_nonneg_left hfb (abs_nonneg _)
  set S₀ : Ω → ℝ := fun ω ↦ (2 * a - Q ω) * f'L (W ω)
  set A₁ : Ω → ℝ := fun ω ↦
    -D ω * ((kolmMulAntideriv x (W' ω) - kolmMulAntideriv x (W ω)) - D ω * (W ω * f (W ω)))
  set A₂ : Ω → ℝ := fun ω ↦
    D ω * (D ω * (Iic x).indicator 1 (W ω) - (min x (W' ω) - min x (W ω)))
  have hW_abs_int : Integrable (fun ω ↦ |W ω|) P := by
    simpa only [Real.norm_eq_abs] using hW_int.norm
  have hA₁_dom_int : Integrable (fun ω ↦ (|W ω| + Real.sqrt (2 * Real.pi) / 4) * (δ ^ 3 / 2)) P :=
    (hW_abs_int.add (integrable_const _)).mul_const (δ ^ 3 / 2)
  have hA₁_ae_le : ∀ᵐ ω ∂P, |A₁ ω| ≤ (|W ω| + Real.sqrt (2 * Real.pi) / 4) * (δ ^ 3 / 2) := by
    filter_upwards [hδ] with ω hω
    dsimp only [A₁]
    rw [abs_mul, abs_neg]
    have hsub := abs_kolmMulAntideriv_sub_le x (W ω) (W' ω)
    have hD_sq_le : D ω ^ 2 / 2 ≤ δ ^ 2 / 2 := by
      have hsq : |D ω| ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hω 2
      rw [sq_abs] at hsq
      linarith
    calc |D ω| * |(kolmMulAntideriv x (W' ω) - kolmMulAntideriv x (W ω)) -
            D ω * (W ω * f (W ω))|
        ≤ δ * ((|W ω| + Real.sqrt (2 * Real.pi) / 4) * (D ω ^ 2 / 2)) :=
          mul_le_mul hω hsub (abs_nonneg _) hδ_nn
      _ ≤ δ * ((|W ω| + Real.sqrt (2 * Real.pi) / 4) * (δ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hD_sq_le (by positivity)) hδ_nn
      _ = (|W ω| + Real.sqrt (2 * Real.pi) / 4) * (δ ^ 3 / 2) := by ring
  have hA₁_asm : AEStronglyMeasurable A₁ P := by
    have hF1_cont := continuous_kolmMulAntideriv x
    have hF1_sub : AEStronglyMeasurable
        (fun ω ↦ kolmMulAntideriv x (W' ω) - kolmMulAntideriv x (W ω)) P :=
      (hF1_cont.comp_aestronglyMeasurable hW'_int.aestronglyMeasurable).sub
        (hF1_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable)
    exact hD_int.neg.aestronglyMeasurable.mul
      (hF1_sub.sub (hD_int.aestronglyMeasurable.mul hWfW_int.aestronglyMeasurable))
  have hA₁_int : Integrable A₁ P :=
    hA₁_dom_int.mono' hA₁_asm (by filter_upwards [hA₁_ae_le] with ω hω; rwa [Real.norm_eq_abs])
  have hA₂_asm : AEStronglyMeasurable A₂ P := by
    have hind_asm : AEStronglyMeasurable (fun ω ↦ (Iic x).indicator (1 : ℝ → ℝ) (W ω)) P :=
      ((measurable_one.indicator measurableSet_Iic).comp hW_meas).aestronglyMeasurable
    have hmin_cont : Continuous (fun u : ℝ ↦ min x u) := continuous_const.min continuous_id
    have hmin_sub : AEStronglyMeasurable (fun ω ↦ min x (W' ω) - min x (W ω)) P :=
      (hmin_cont.comp_aestronglyMeasurable hW'_int.aestronglyMeasurable).sub
        (hmin_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable)
    exact hD_int.aestronglyMeasurable.mul
      ((hD_int.aestronglyMeasurable.mul hind_asm).sub hmin_sub)
  have hpt_decomp : ∀ ω : Ω, D ω ^ 2 * f'L (W ω) - D ω * (f (W' ω) - f (W ω)) = A₁ ω + A₂ ω := by
    intro ω
    dsimp only [A₁, A₂, D]
    rw [hf'L_eq (W ω), normalSteinSolKolm_sub_eq x (W ω) (W' ω)]
    ring
  have hA₂_int : Integrable A₂ P := by
    refine ((hD2f'L_int.sub' hDf_int).sub' hA₁_int).congr (Eventually.of_forall fun ω ↦ ?_)
    change (D ω ^ 2 * f'L (W ω) - D ω * (f (W' ω) - f (W ω))) - A₁ ω = A₂ ω
    linarith [hpt_decomp ω]
  have hSteinId :
      2 * a * ∫ ω, normalSteinOpLeft f (W ω) ∂P =
        ∫ ω, S₀ ω ∂P + ∫ ω, A₁ ω ∂P + ∫ ω, A₂ ω ∂P := by
    have hOp : ∫ ω, normalSteinOpLeft f (W ω) ∂P =
        ∫ ω, f'L (W ω) ∂P - ∫ ω, W ω * f (W ω) ∂P :=
      integral_sub hf'LW_int hWfW_int
    have hexch_f := steinPair_integral_sub_mul_sub_eq P hExch ha hW_meas hW2 hCond hf_cont hf_bdd
    have hS₀_eq : S₀ = fun ω ↦ (2 * a) * f'L (W ω) - Q ω * f'L (W ω) := funext fun _ ↦ by ring
    have hIntS₀ : ∫ ω, S₀ ω ∂P =
        (2 * a) * ∫ ω, f'L (W ω) ∂P - ∫ ω, D ω ^ 2 * f'L (W ω) ∂P := by
      rw [hS₀_eq, integral_sub (hf'LW_int.const_mul (2 * a)) hQf'L_int,
        integral_const_mul (2 * a) (fun ω ↦ f'L (W ω)), hIntD2f'L]
    have hIntA : ∫ ω, A₁ ω ∂P + ∫ ω, A₂ ω ∂P =
        ∫ ω, D ω ^ 2 * f'L (W ω) ∂P - ∫ ω, D ω * (f (W' ω) - f (W ω)) ∂P := by
      rw [← integral_add hA₁_int hA₂_int, ← integral_sub hD2f'L_int hDf_int]
      exact integral_congr_ae (Eventually.of_forall fun ω ↦ (hpt_decomp ω).symm)
    have hDf_eq : ∫ ω, D ω * (f (W' ω) - f (W ω)) ∂P = 2 * a * ∫ ω, W ω * f (W ω) ∂P := hexch_f
    rw [hOp, hIntS₀, add_assoc, hIntA, hDf_eq]
    ring
  have hS₀_bound : |∫ ω, S₀ ω ∂P| ≤ Real.sqrt (ProbabilityTheory.variance Q P) := by
    have hS₀_int : Integrable S₀ P := by
      have hS₀_eq : S₀ = fun ω ↦ (2 * a) * f'L (W ω) - Q ω * f'L (W ω) := funext fun _ ↦ by ring
      rw [hS₀_eq]
      exact (hf'LW_int.const_mul (2 * a)).sub' hQf'L_int
    have h1 : |∫ ω, S₀ ω ∂P| ≤ ∫ ω, |S₀ ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm S₀
    have hS₀_abs_int : Integrable (fun ω ↦ |S₀ ω|) P := by
      simpa only [Real.norm_eq_abs] using hS₀_int.norm
    have hQsub_abs_int : Integrable (fun ω ↦ |Q ω - ∫ u, Q u ∂P|) P := by
      simpa only [Real.norm_eq_abs] using (hQ_int.sub' (integrable_const (∫ u, Q u ∂P))).norm
    have h2 : ∫ ω, |S₀ ω| ∂P ≤ ∫ ω, |Q ω - ∫ u, Q u ∂P| ∂P := by
      refine integral_mono hS₀_abs_int hQsub_abs_int fun ω ↦ ?_
      dsimp only [S₀]
      rw [abs_mul, ← hQ_mean, abs_sub_comm (∫ u, Q u ∂P) (Q ω)]
      exact (mul_le_mul_of_nonneg_left (hf'L_bdd (W ω)) (abs_nonneg _)).trans (by rw [mul_one])
    exact h1.trans (h2.trans (integral_abs_sub_le_sqrt_variance P hQ2))
  have hA₁_bound : |∫ ω, A₁ ω ∂P| ≤ δ ^ 3 := by
    have h1 : |∫ ω, A₁ ω ∂P| ≤ ∫ ω, (|W ω| + Real.sqrt (2 * Real.pi) / 4) * (δ ^ 3 / 2) ∂P := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le hA₁_dom_int
        (by filter_upwards [hA₁_ae_le] with ω hω; rwa [Real.norm_eq_abs])
    rw [integral_mul_const, integral_add hW_abs_int (integrable_const _), integral_const,
      probReal_univ, smul_eq_mul, one_mul] at h1
    have hW1 := integral_abs_le_one_of_integral_eq_zero_of_variance_eq_one P hW2 hMean hvar
    have hpi1 := sqrt_two_pi_div_four_le_one
    have hsum_le : (∫ ω, |W ω| ∂P + Real.sqrt (2 * Real.pi) / 4) * (δ ^ 3 / 2) ≤
        2 * (δ ^ 3 / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hA₂_bound : |∫ ω, A₂ ω ∂P| ≤ 3 * δ * a := by
    have hind_int : ∀ y : ℝ, Integrable (fun ω ↦ D ω ^ 2 * (Ioc y (y + δ)).indicator 1 (W ω)) P :=
      fun y ↦ by
        have hm_ind : Measurable ((Ioc y (y + δ)).indicator (1 : ℝ → ℝ)) :=
          measurable_one.indicator measurableSet_Ioc
        refine hD_sq_int.norm.mono'
          (hD_sq_int.aestronglyMeasurable.mul (hm_ind.comp hW_meas).aestronglyMeasurable)
          (Eventually.of_forall fun ω ↦ ?_)
        rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        by_cases hw : W ω ∈ Ioc y (y + δ) <;> simp [hw, sq_nonneg]
    have hlo : -(3 * δ * a) ≤ ∫ ω, A₂ ω ∂P := by
      have hlem := steinPair_integral_sq_sub_mul_indicator_Ioc_le P x hExch ha hW_meas hCond
        hvar hδ
      have hmono : ∫ ω, -(D ω ^ 2 * (Ioc x (x + δ)).indicator 1 (W ω)) ∂P ≤ ∫ ω, A₂ ω ∂P := by
        refine integral_mono_ae (hind_int x).neg hA₂_int ?_
        filter_upwards [hδ] with ω hω
        exact (indicator_min_remainder_bounds x hω).1
      rw [integral_neg] at hmono
      linarith
    have hhi : ∫ ω, A₂ ω ∂P ≤ 3 * δ * a := by
      have hlem := steinPair_integral_sq_sub_mul_indicator_Ioc_le P (x - δ) hExch ha hW_meas
        hCond hvar hδ
      have hset : Ioc (x - δ) ((x - δ) + δ) = Ioc (x - δ) x := by rw [sub_add_cancel]
      have hmono : ∫ ω, A₂ ω ∂P ≤
          ∫ ω, D ω ^ 2 * (Ioc (x - δ) ((x - δ) + δ)).indicator 1 (W ω) ∂P := by
        refine integral_mono_ae hA₂_int (hind_int (x - δ)) ?_
        filter_upwards [hδ] with ω hω
        rw [hset]
        exact (indicator_min_remainder_bounds x hω).2
      exact hmono.trans hlem
    exact abs_le.mpr ⟨hlo, hhi⟩
  have h2a_pos : 0 < 2 * a := by positivity
  have hMulLe : 2 * a * |∫ ω, normalSteinOpLeft f (W ω) ∂P| ≤
      Real.sqrt (ProbabilityTheory.variance Q P) + δ ^ 3 + 3 * δ * a := by
    have hAbsEq : 2 * a * |∫ ω, normalSteinOpLeft f (W ω) ∂P| =
        |∫ ω, S₀ ω ∂P + ∫ ω, A₁ ω ∂P + ∫ ω, A₂ ω ∂P| := by
      rw [← hSteinId, abs_mul, abs_of_pos h2a_pos]
    have hTri : |∫ ω, S₀ ω ∂P + ∫ ω, A₁ ω ∂P + ∫ ω, A₂ ω ∂P| ≤
        |∫ ω, S₀ ω ∂P| + |∫ ω, A₁ ω ∂P| + |∫ ω, A₂ ω ∂P| := by
      calc |(∫ ω, S₀ ω ∂P + ∫ ω, A₁ ω ∂P) + ∫ ω, A₂ ω ∂P|
          ≤ |∫ ω, S₀ ω ∂P + ∫ ω, A₁ ω ∂P| + |∫ ω, A₂ ω ∂P| := abs_add_le _ _
        _ ≤ |∫ ω, S₀ ω ∂P| + |∫ ω, A₁ ω ∂P| + |∫ ω, A₂ ω ∂P| := by
            gcongr; exact abs_add_le _ _
    linarith
  have hReal : |∫ ω, normalSteinOpLeft f (W ω) ∂P| ≤
      Real.sqrt (ProbabilityTheory.variance Q P) / (2 * a) + (δ ^ 3 / (2 * a) + 3 * δ / 2) := by
    refine le_of_mul_le_mul_left ?_ h2a_pos
    have hrhs : (2 * a) * (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * a) +
        (δ ^ 3 / (2 * a) + 3 * δ / 2)) =
        Real.sqrt (ProbabilityTheory.variance Q P) + δ ^ 3 + 3 * δ * a := by
      have hne : 2 * a ≠ 0 := h2a_pos.ne'
      field_simp [hne]
      ring
    linarith
  have hTerm₁_nn : 0 ≤ Real.sqrt (ProbabilityTheory.variance Q P) / (2 * a) :=
    div_nonneg (Real.sqrt_nonneg _) h2a_pos.le
  have hTerm₂_nn : 0 ≤ δ ^ 3 / (2 * a) + 3 * δ / 2 := by positivity
  calc ENNReal.ofReal |∫ ω, normalSteinOpLeft f (W ω) ∂P|
      ≤ ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * a) +
          (δ ^ 3 / (2 * a) + 3 * δ / 2)) := ENNReal.ofReal_le_ofReal hReal
    _ = ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * a)) +
          ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2) :=
        ENNReal.ofReal_add hTerm₁_nn hTerm₂_nn
    _ = V ^ (1 / 2 : ℝ) / ENNReal.ofReal (2 * a) +
          ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2) := by
        rw [ENNReal.ofReal_div_of_pos h2a_pos, ← hV_eq]

/-- **Theorem 3.28** (`\label{thm92}`, `SteinIntro.tex:1750-1755`; `ISSUE-3.25` proof note):
`IsSteinPair` specialization of `steinPair_kolmogorovDist_map_stdNormal_le`. -/
theorem IsSteinPair.kolmogorovDist_map_stdNormal_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a δ : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ}
    (hSP : IsSteinPair P a W W')
    (hvar : ProbabilityTheory.variance W P = 1)
    (hδ : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (2 * a) +
      ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2) := by
  rcases hSP with ⟨hExch, ha, _, hW_meas, _, hCond⟩
  exact steinPair_kolmogorovDist_map_stdNormal_le P P' hExch ha hW_meas hCond hvar hδ hZ hZ_law

end SteinMethod
