/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.ZeroBias.Density
import Mathlib.Probability.CDF
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Distributional Uniqueness from Compactly Supported C¹ Derivatives (`SweepBZeroBias`)

Proves Section 3.5 distributional uniqueness from derivatives of compactly supported $C^1$
functions (`SteinIntro.tex:1512-1513`, inside Proposition 3.19 proof):
if two real random variables $X$ and $Y$ satisfy $\mathbb{E}[f'(X)] = \mathbb{E}[f'(Y)]$ for all
$f \in C_c^1(\mathbb{R})$, then $X \stackrel{d}{=} Y$ (`ProbabilityTheory.IdentDistrib X Y P P'`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SteinMethod

/-- If $k : ℝ → ℝ$ is continuous, supported on $[-R, R]$, and has zero integral $\int_{-R}^R k = 0$,
then $\mathbb{E}[k(X)] = \mathbb{E}[k(Y)]$ because $f(t) = \int_{-R}^t k(s)\,ds$ is $C^1$ and
compactly supported with $f' = k$. -/
lemma integral_eq_of_compact_integral_zero
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hHyp : ∀ f : ℝ → ℝ,
        Differentiable ℝ f →
        Continuous (deriv f) →
        (∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → f x = 0) →
        ∫ ω, deriv f (X ω) ∂P = ∫ ω', deriv f (Y ω') ∂P')
    (k : ℝ → ℝ) (hk_cont : Continuous k) (R : ℝ) (hR : 0 < R)
    (hk_supp : ∀ x : ℝ, R ≤ |x| → k x = 0)
    (hk_int : ∫ s in (-R)..R, k s = 0) :
    ∫ ω, k (X ω) ∂P = ∫ ω', k (Y ω') ∂P' := by
  let f : ℝ → ℝ := fun t ↦ ∫ s in (-R)..t, k s
  have hf_deriv : ∀ t, HasDerivAt f (k t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hk_cont.intervalIntegrable (-R) t)
      hk_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hk_cont.continuousAt
  have hf_diff : Differentiable ℝ f := fun t ↦ (hf_deriv t).differentiableAt
  have hderiv_eq : deriv f = k := funext fun t ↦ (hf_deriv t).deriv
  have hf_cont_deriv : Continuous (deriv f) := by rw [hderiv_eq]; exact hk_cont
  have hf_supp : ∃ R' : ℝ, ∀ x : ℝ, R' ≤ |x| → f x = 0 := by
    refine ⟨R, fun x hx ↦ ?_⟩
    rcases le_total 0 x with hx0 | hx0
    · have hx_ge : R ≤ x := by rwa [abs_of_nonneg hx0] at hx
      have hsplit : (∫ s in (-R)..x, k s) = (∫ s in (-R)..R, k s) + (∫ s in R..x, k s) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hk_cont.intervalIntegrable (-R) R) (hk_cont.intervalIntegrable R x)).symm
      have hzero : ∫ s in R..x, k s = 0 := by
        refine intervalIntegral.integral_zero_ae (ae_of_all _ fun s hs ↦ ?_)
        have hs_ge : R ≤ s := by
          rw [uIoc_of_le hx_ge] at hs
          exact hs.1.le
        have : R ≤ |s| := by rwa [abs_of_nonneg (hR.le.trans hs_ge)]
        exact hk_supp s this
      dsimp [f]
      rw [hsplit, hk_int, hzero, add_zero]
    · have hx_le : x ≤ -R := by
        have : R ≤ -x := by rwa [abs_of_nonpos hx0] at hx
        linarith
      dsimp [f]
      refine intervalIntegral.integral_zero_ae (ae_of_all _ fun s hs ↦ ?_)
      rw [uIoc_of_ge hx_le] at hs
      have hs_le : s ≤ -R := hs.2
      have : R ≤ |s| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      exact hk_supp s this
  have h := hHyp f hf_diff hf_cont_deriv hf_supp
  rwa [hderiv_eq] at h

/-- For any continuous function $g : ℝ → ℝ$ with compact support and $0 ≤ g ≤ 1$,
$\mathbb{E}[g(X)] = \mathbb{E}[g(Y)]$. -/
lemma integral_eq_of_compact_nonneg_le_one
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P')
    (hHyp : ∀ f : ℝ → ℝ,
        Differentiable ℝ f →
        Continuous (deriv f) →
        (∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → f x = 0) →
        ∫ ω, deriv f (X ω) ∂P = ∫ ω', deriv f (Y ω') ∂P')
    (g : ℝ → ℝ) (hg_cont : Continuous g) (R : ℝ) (hR : 0 < R)
    (hg_supp : ∀ x : ℝ, R ≤ |x| → g x = 0)
    (hg_bdd : ∀ x : ℝ, 0 ≤ g x ∧ g x ≤ 1) :
    ∫ ω, g (X ω) ∂P = ∫ ω', g (Y ω') ∂P' := by
  have hShift : ∀ S : ℝ, 0 < S →
      (∫ ω, g (X ω) ∂P) - (∫ ω', g (Y ω') ∂P') =
      (∫ ω, g (X ω - S) ∂P) - (∫ ω', g (Y ω' - S) ∂P') := fun S hS ↦ by
    let k : ℝ → ℝ := fun t ↦ g t - g (t - S)
    have hk_cont : Continuous k := hg_cont.sub (hg_cont.comp (continuous_sub_right S))
    have hRS_pos : 0 < R + S := add_pos hR hS
    have hk_supp : ∀ x : ℝ, R + S ≤ |x| → k x = 0 := fun x hx ↦ by
      dsimp [k]
      rcases le_total 0 x with hx0 | hx0
      · have hx_ge : R + S ≤ x := by rwa [abs_of_nonneg hx0] at hx
        have h1 : g x = 0 := hg_supp x (by rw [abs_of_nonneg (by linarith)]; linarith)
        have h2 : g (x - S) = 0 := hg_supp (x - S) (by rw [abs_of_nonneg (by linarith)]; linarith)
        rw [h1, h2, sub_zero]
      · have hx_le : x ≤ -(R + S) := by
          have : R + S ≤ -x := by rwa [abs_of_nonpos hx0] at hx
          linarith
        have h1 : g x = 0 := hg_supp x (by rw [abs_of_nonpos (by linarith)]; linarith)
        have h2 : g (x - S) = 0 := hg_supp (x - S) (by rw [abs_of_nonpos (by linarith)]; linarith)
        rw [h1, h2, sub_zero]
    have hk_int : ∫ s in (-(R + S))..(R + S), k s = 0 := by
      have h1_int : IntervalIntegrable g volume (-(R + S)) (R + S) := hg_cont.intervalIntegrable _ _
      have h2_int : IntervalIntegrable (fun s ↦ g (s - S)) volume (-(R + S)) (R + S) :=
        (hg_cont.comp (continuous_sub_right S)).intervalIntegrable _ _
      have hsub_int : (∫ s in (-(R + S))..(R + S), k s) =
          (∫ s in (-(R + S))..(R + S), g s) - ∫ s in (-(R + S))..(R + S), g (s - S) :=
        intervalIntegral.integral_sub h1_int h2_int
      rw [hsub_int, intervalIntegral.integral_comp_sub_right g S]
      have h1 : (∫ s in (-(R + S))..(R + S), g s) = ∫ s in (-R)..R, g s := by
        have hs1 : (∫ s in (-(R + S))..(R + S), g s) =
            (∫ s in (-(R + S))..(-R), g s) + (∫ s in (-R)..R, g s) + (∫ s in R..(R + S), g s) := by
          have h_mid : (∫ s in (-(R + S))..(-R), g s) + (∫ s in (-R)..R, g s) =
              ∫ s in (-(R + S))..R, g s :=
            intervalIntegral.integral_add_adjacent_intervals (μ := volume)
              (hg_cont.intervalIntegrable (-(R + S)) (-R)) (hg_cont.intervalIntegrable (-R) R)
          have h_all : (∫ s in (-(R + S))..R, g s) + (∫ s in R..(R + S), g s) =
              ∫ s in (-(R + S))..(R + S), g s :=
            intervalIntegral.integral_add_adjacent_intervals (μ := volume)
              (hg_cont.intervalIntegrable (-(R + S)) R) (hg_cont.intervalIntegrable R (R + S))
          linarith
        have hz1 : ∫ s in (-(R + S))..(-R), g s = 0 := by
          refine intervalIntegral.integral_zero_ae (ae_of_all _ fun s hs ↦ ?_)
          rw [uIoc_of_le (by linarith : -(R + S) ≤ -R)] at hs
          have : R ≤ |s| := by
            rw [abs_of_nonpos (by linarith [hs.2, hR] : s ≤ 0)]
            linarith [hs.2]
          exact hg_supp s this
        have hz2 : ∫ s in R..(R + S), g s = 0 := by
          refine intervalIntegral.integral_zero_ae (ae_of_all _ fun s hs ↦ ?_)
          rw [uIoc_of_le (by linarith : R ≤ R + S)] at hs
          have : R ≤ |s| := by
            rw [abs_of_nonneg (by linarith [hs.1, hR] : 0 ≤ s)]
            linarith [hs.1]
          exact hg_supp s this
        rw [hs1, hz1, hz2, zero_add, add_zero]
      have h2 : (∫ s in (-(R + S) - S)..((R + S) - S), g s) = ∫ s in (-R)..R, g s := by
        have heq_b : (R + S) - S = R := by ring
        have heq_a : -(R + S) - S = -(R + 2 * S) := by ring
        rw [heq_b, heq_a]
        have hs2 : (∫ s in (-(R + 2 * S))..R, g s) =
            (∫ s in (-(R + 2 * S))..(-R), g s) + (∫ s in (-R)..R, g s) := by
          have := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
            (hg_cont.intervalIntegrable (-(R + 2 * S)) (-R)) (hg_cont.intervalIntegrable (-R) R)
          linarith
        have hz3 : ∫ s in (-(R + 2 * S))..(-R), g s = 0 := by
          refine intervalIntegral.integral_zero_ae (ae_of_all _ fun s hs ↦ ?_)
          rw [uIoc_of_le (by linarith : -(R + 2 * S) ≤ -R)] at hs
          have : R ≤ |s| := by
            rw [abs_of_nonpos (by linarith [hs.2, hR] : s ≤ 0)]
            linarith [hs.2]
          exact hg_supp s this
        rw [hs2, hz3, zero_add]
      rw [h1, h2, sub_self]
    have hEq :=
      integral_eq_of_compact_integral_zero P P' hHyp k hk_cont (R + S) hRS_pos hk_supp hk_int
    dsimp [k] at hEq
    have hgX_int : Integrable (fun ω ↦ g (X ω)) P :=
      Integrable.of_bound ((hg_cont.measurable.comp_aemeasurable hX).aestronglyMeasurable) 1
        (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [(hg_bdd (X ω)).1], (hg_bdd (X ω)).2⟩)
    have hgXS_int : Integrable (fun ω ↦ g (X ω - S)) P :=
      Integrable.of_bound
        (((hg_cont.comp (continuous_sub_right S)).measurable.comp_aemeasurable
          hX).aestronglyMeasurable) 1
        (ae_of_all _ fun ω ↦ by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [(hg_bdd (X ω - S)).1], (hg_bdd (X ω - S)).2⟩)
    have hgY_int : Integrable (fun ω' ↦ g (Y ω')) P' :=
      Integrable.of_bound ((hg_cont.measurable.comp_aemeasurable hY).aestronglyMeasurable) 1
        (ae_of_all _ fun ω' ↦ by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [(hg_bdd (Y ω')).1], (hg_bdd (Y ω')).2⟩)
    have hgYS_int : Integrable (fun ω' ↦ g (Y ω' - S)) P' :=
      Integrable.of_bound
        (((hg_cont.comp (continuous_sub_right S)).measurable.comp_aemeasurable
          hY).aestronglyMeasurable) 1
        (ae_of_all _ fun ω' ↦ by
          rw [Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [(hg_bdd (Y ω' - S)).1], (hg_bdd (Y ω' - S)).2⟩)
    rw [integral_sub hgX_int hgXS_int, integral_sub hgY_int hgYS_int] at hEq
    linarith
  set C : ℝ := (∫ ω, g (X ω) ∂P) - (∫ ω', g (Y ω') ∂P')
  have hC_eq : ∀ m : ℕ,
      (∫ ω, g (X ω - (m + 1 : ℝ)) ∂P) - (∫ ω', g (Y ω' - (m + 1 : ℝ)) ∂P') = C := fun m ↦ by
    have hpos : 0 < (m + 1 : ℝ) := Nat.cast_add_one_pos m
    exact (hShift (m + 1 : ℝ) hpos).symm
  have htendX : Tendsto (fun m : ℕ ↦ ∫ ω, g (X ω - (m + 1 : ℝ)) ∂P) atTop (𝓝 0) := by
    have hpoint : ∀ ω : Ω, Tendsto (fun m : ℕ ↦ g (X ω - (m + 1 : ℝ))) atTop (𝓝 0) := fun ω ↦ by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.Ici_mem_atTop ⌈X ω + R⌉₊] with m hm
      have hm_ge : X ω + R ≤ (m : ℝ) := (Nat.le_ceil (X ω + R)).trans (Nat.cast_le.mpr hm)
      have harg : R ≤ |X ω - (m + 1 : ℝ)| := by
        rw [abs_of_nonpos (by linarith : X ω - (m + 1 : ℝ) ≤ 0)]
        linarith
      exact (hg_supp _ harg).symm
    have hdom := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
      (fun m ↦ ((hg_cont.comp (continuous_sub_right (m + 1 : ℝ))).measurable.comp_aemeasurable
        hX).aestronglyMeasurable)
      (integrable_const 1)
      (fun m ↦ ae_of_all P fun ω ↦ by
        change ‖g (X ω - (m + 1 : ℝ))‖ ≤ 1
        rw [Real.norm_eq_abs]
        have := hg_bdd (X ω - (m + 1 : ℝ))
        exact abs_le.mpr ⟨by linarith, this.2⟩)
      (ae_of_all P hpoint)
    rw [integral_zero] at hdom
    exact hdom
  have htendY : Tendsto (fun m : ℕ ↦ ∫ ω', g (Y ω' - (m + 1 : ℝ)) ∂P') atTop (𝓝 0) := by
    have hpoint : ∀ ω' : Ω', Tendsto (fun m : ℕ ↦ g (Y ω' - (m + 1 : ℝ))) atTop (𝓝 0) := fun ω' ↦ by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.Ici_mem_atTop ⌈Y ω' + R⌉₊] with m hm
      have hm_ge : Y ω' + R ≤ (m : ℝ) := (Nat.le_ceil (Y ω' + R)).trans (Nat.cast_le.mpr hm)
      have harg : R ≤ |Y ω' - (m + 1 : ℝ)| := by
        rw [abs_of_nonpos (by linarith : Y ω' - (m + 1 : ℝ) ≤ 0)]
        linarith
      exact (hg_supp _ harg).symm
    have hdom := tendsto_integral_of_dominated_convergence (fun _ : Ω' ↦ (1 : ℝ))
      (fun m ↦ ((hg_cont.comp (continuous_sub_right (m + 1 : ℝ))).measurable.comp_aemeasurable
        hY).aestronglyMeasurable)
      (integrable_const 1)
      (fun m ↦ ae_of_all P' fun ω' ↦ by
        change ‖g (Y ω' - (m + 1 : ℝ))‖ ≤ 1
        rw [Real.norm_eq_abs]
        have := hg_bdd (Y ω' - (m + 1 : ℝ))
        exact abs_le.mpr ⟨by linarith, this.2⟩)
      (ae_of_all P' hpoint)
    rw [integral_zero] at hdom
    exact hdom
  have htendSub :
      Tendsto (fun m : ℕ ↦ (∫ ω, g (X ω - (m + 1 : ℝ)) ∂P) - (∫ ω', g (Y ω' - (m + 1 : ℝ)) ∂P'))
        atTop (𝓝 (0 - 0)) := htendX.sub htendY
  rw [sub_zero] at htendSub
  simp_rw [hC_eq] at htendSub
  have hC0 : C = 0 := tendsto_nhds_unique tendsto_const_nhds htendSub
  dsimp [C] at hC0
  linarith

/-- Helper: `zbRamp x n t = 0` when $t \ge x + 1$. -/
lemma zbRamp_of_ge {x : ℝ} {n : ℕ} {t : ℝ} (ht : x + 1 ≤ t) : zbRamp x n t = 0 := by
  dsimp [zbRamp]
  have htx : (1 : ℝ) ≤ t - x := by linarith
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg (α := ℝ) n)]
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) * (t - x) := by
    calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ ((n : ℝ) + 1) * (t - x) := mul_le_mul hn htx zero_le_one (by linarith)
  have hmin : min (1 : ℝ) (1 - ((n : ℝ) + 1) * (t - x)) ≤ 0 :=
    (min_le_right 1 _).trans (by linarith)
  exact max_eq_left hmin

/-- Helper: `zbRamp x n t = 1` when $t \le x$. -/
lemma zbRamp_of_le {x : ℝ} {n : ℕ} {t : ℝ} (ht : t ≤ x) : zbRamp x n t = 1 := by
  dsimp [zbRamp]
  have hmul : ((n : ℝ) + 1) * (t - x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hmin : min 1 (1 - ((n : ℝ) + 1) * (t - x)) = 1 := min_eq_left (by linarith)
  rw [hmin]
  exact max_eq_right zero_le_one

/-- Section 3.5 distributional uniqueness from derivatives of compactly supported $C^1$ functions
(`SteinIntro.tex:1512-1513`, inside the proof of Proposition 3.19): if two real-valued random
variables $X$ and $Y$ satisfy $\mathbb{E}[f'(X)] = \mathbb{E}[f'(Y)]$ for every continuously
differentiable function $f : \mathbb{R} \to \mathbb{R}$ with compact support, then
$X \stackrel{d}{=} Y$ (`ProbabilityTheory.IdentDistrib X Y P P'`). -/
theorem sec3_5_identDistrib_of_integral_deriv_compactSupport_proof
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P')
    (hHyp : ∀ f : ℝ → ℝ,
        Differentiable ℝ f →
        Continuous (deriv f) →
        (∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → f x = 0) →
        ∫ ω, deriv f (X ω) ∂P = ∫ ω', deriv f (Y ω') ∂P') :
    ProbabilityTheory.IdentDistrib X Y P P' := by
  have hP_map : IsProbabilityMeasure (P.map X) := (Measure.isProbabilityMeasure_map_iff hX).mpr ‹_›
  have hP'_map : IsProbabilityMeasure (P'.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY).mpr ‹_›
  have hmap_eq : P.map X = P'.map Y := by
    refine Measure.eq_of_cdf (P.map X) (P'.map Y) ?_
    ext x
    have heq_n : ∀ n : ℕ, ∫ t, zbRamp x n t ∂(P.map X) = ∫ t, zbRamp x n t ∂(P'.map Y) := fun n ↦ by
      let g_M : ℕ → ℝ → ℝ := fun M t ↦ zbRamp x n t * zbRamp (M : ℝ) 0 (-t)
      have hg_int : ∀ M : ℕ, ∫ ω, g_M M (X ω) ∂P = ∫ ω', g_M M (Y ω') ∂P' := fun M ↦ by
        have hg_cont : Continuous (g_M M) :=
          (continuous_zbRamp x n).mul ((continuous_zbRamp (M : ℝ) 0).comp continuous_neg)
        let R : ℝ := |x| + (M : ℝ) + 2
        have hR_pos : 0 < R := by
          have : 0 ≤ |x| := abs_nonneg x
          have : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith
        have hg_supp : ∀ t : ℝ, R ≤ |t| → g_M M t = 0 := fun t ht ↦ by
          dsimp [R] at ht
          dsimp [g_M]
          by_cases htx : x + 1 ≤ t
          · rw [zbRamp_of_ge htx, zero_mul]
          · have htx' : t < x + 1 := not_le.mp htx
            have ht_neg : t < 0 := by
              by_contra! hnonneg
              have ht_eq : |t| = t := abs_of_nonneg hnonneg
              have hle : t ≤ |x| + 1 := by linarith [le_abs_self x]
              have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
              linarith
            have ht_abs : |t| = -t := abs_of_nonpos ht_neg.le
            have hzero : zbRamp (M : ℝ) 0 (-t) = 0 := by
              have hM1 : (M : ℝ) + 1 ≤ -t := by
                have : 0 ≤ |x| := abs_nonneg x
                linarith
              exact zbRamp_of_ge hM1
            rw [hzero, mul_zero]
        have hg_bdd : ∀ t : ℝ, 0 ≤ g_M M t ∧ g_M M t ≤ 1 := fun t ↦ by
          dsimp [g_M]
          have h1 := abs_zbRamp_le_one x n t
          have h2 := abs_zbRamp_le_one (M : ℝ) 0 (-t)
          have h1_pos : 0 ≤ zbRamp x n t := le_max_left 0 _
          have h2_pos : 0 ≤ zbRamp (M : ℝ) 0 (-t) := le_max_left 0 _
          have h1_le : zbRamp x n t ≤ 1 := (abs_le.mp h1).2
          have h2_le : zbRamp (M : ℝ) 0 (-t) ≤ 1 := (abs_le.mp h2).2
          have hprod_pos : 0 ≤ zbRamp x n t * zbRamp (M : ℝ) 0 (-t) := mul_nonneg h1_pos h2_pos
          have hprod_le : zbRamp x n t * zbRamp (M : ℝ) 0 (-t) ≤ 1 := by
            calc zbRamp x n t * zbRamp (M : ℝ) 0 (-t) ≤ 1 * 1 :=
              mul_le_mul h1_le h2_le h2_pos zero_le_one
            _ = 1 := mul_one 1
          exact ⟨hprod_pos, hprod_le⟩
        exact integral_eq_of_compact_nonneg_le_one P P' hX hY hHyp
          (g_M M) hg_cont R hR_pos hg_supp hg_bdd
      have hpointX :
          ∀ ω : Ω, Tendsto (fun M : ℕ ↦ g_M M (X ω)) atTop (𝓝 (zbRamp x n (X ω))) := fun ω ↦ by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.Ici_mem_atTop ⌈-X ω⌉₊] with M hM
        have hM_ge : -X ω ≤ (M : ℝ) := (Nat.le_ceil (-X ω)).trans (Nat.cast_le.mpr hM)
        have h1 : zbRamp (M : ℝ) 0 (-X ω) = 1 := zbRamp_of_le hM_ge
        dsimp [g_M]
        rw [h1, mul_one]
      have hdomX := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
        (fun M ↦ (((continuous_zbRamp x n).mul
          ((continuous_zbRamp (M : ℝ) 0).comp continuous_neg)).measurable.comp_aemeasurable
            hX).aestronglyMeasurable)
        (integrable_const 1)
        (fun M ↦ ae_of_all P fun ω ↦ by
          change ‖g_M M (X ω)‖ ≤ 1
          rw [Real.norm_eq_abs]
          have h1 := abs_zbRamp_le_one x n (X ω)
          have h2 := abs_zbRamp_le_one (M : ℝ) 0 (-X ω)
          have h1_pos : 0 ≤ zbRamp x n (X ω) := le_max_left 0 _
          have h2_pos : 0 ≤ zbRamp (M : ℝ) 0 (-X ω) := le_max_left 0 _
          have h1_le : zbRamp x n (X ω) ≤ 1 := (abs_le.mp h1).2
          have h2_le : zbRamp (M : ℝ) 0 (-X ω) ≤ 1 := (abs_le.mp h2).2
          have hprod_pos : 0 ≤ g_M M (X ω) := mul_nonneg h1_pos h2_pos
          have hprod_le : g_M M (X ω) ≤ 1 := by
            calc g_M M (X ω) ≤ 1 * 1 := mul_le_mul h1_le h2_le h2_pos zero_le_one
            _ = 1 := mul_one 1
          exact abs_le.mpr ⟨by linarith, hprod_le⟩)
        (ae_of_all P hpointX)
      have hpointY :
          ∀ ω' : Ω', Tendsto (fun M : ℕ ↦ g_M M (Y ω')) atTop (𝓝 (zbRamp x n (Y ω'))) :=
        fun ω' ↦ by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.Ici_mem_atTop ⌈-Y ω'⌉₊] with M hM
        have hM_ge : -Y ω' ≤ (M : ℝ) := (Nat.le_ceil (-Y ω')).trans (Nat.cast_le.mpr hM)
        have h1 : zbRamp (M : ℝ) 0 (-Y ω') = 1 := zbRamp_of_le hM_ge
        dsimp [g_M]
        rw [h1, mul_one]
      have hdomY := tendsto_integral_of_dominated_convergence (fun _ : Ω' ↦ (1 : ℝ))
        (fun M ↦ (((continuous_zbRamp x n).mul
          ((continuous_zbRamp (M : ℝ) 0).comp continuous_neg)).measurable.comp_aemeasurable
            hY).aestronglyMeasurable)
        (integrable_const 1)
        (fun M ↦ ae_of_all P' fun ω' ↦ by
          change ‖g_M M (Y ω')‖ ≤ 1
          rw [Real.norm_eq_abs]
          have h1 := abs_zbRamp_le_one x n (Y ω')
          have h2 := abs_zbRamp_le_one (M : ℝ) 0 (-Y ω')
          have h1_pos : 0 ≤ zbRamp x n (Y ω') := le_max_left 0 _
          have h2_pos : 0 ≤ zbRamp (M : ℝ) 0 (-Y ω') := le_max_left 0 _
          have h1_le : zbRamp x n (Y ω') ≤ 1 := (abs_le.mp h1).2
          have h2_le : zbRamp (M : ℝ) 0 (-Y ω') ≤ 1 := (abs_le.mp h2).2
          have hprod_pos : 0 ≤ g_M M (Y ω') := mul_nonneg h1_pos h2_pos
          have hprod_le : g_M M (Y ω') ≤ 1 := by
            calc g_M M (Y ω') ≤ 1 * 1 := mul_le_mul h1_le h2_le h2_pos zero_le_one
            _ = 1 := mul_one 1
          exact abs_le.mpr ⟨by linarith, hprod_le⟩)
        (ae_of_all P' hpointY)
      have hlim_int :
          Tendsto (fun M : ℕ ↦ ∫ ω', g_M M (Y ω') ∂P') atTop (𝓝 (∫ ω, zbRamp x n (X ω) ∂P)) := by
        have : (fun M : ℕ ↦ ∫ ω', g_M M (Y ω') ∂P') = (fun M : ℕ ↦ ∫ ω, g_M M (X ω) ∂P) := by
          ext M; exact (hg_int M).symm
        rw [this]
        exact hdomX
      have h_int_eq : ∫ ω, zbRamp x n (X ω) ∂P = ∫ ω', zbRamp x n (Y ω') ∂P' :=
        tendsto_nhds_unique hlim_int hdomY
      have hmapX : (∫ ω, zbRamp x n (X ω) ∂P) = ∫ t, zbRamp x n t ∂(P.map X) :=
        (integral_map hX (continuous_zbRamp x n).aestronglyMeasurable).symm
      have hmapY : (∫ ω', zbRamp x n (Y ω') ∂P') = ∫ t, zbRamp x n t ∂(P'.map Y) :=
        (integral_map hY (continuous_zbRamp x n).aestronglyMeasurable).symm
      rw [hmapX, hmapY] at h_int_eq
      exact h_int_eq
    have hlim1 := tendsto_integral_zbRamp (P.map X) x
    have hlim2 := tendsto_integral_zbRamp (P'.map Y) x
    simp_rw [heq_n] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2
  exact ⟨hX, hY, hmap_eq⟩

end SteinMethod
