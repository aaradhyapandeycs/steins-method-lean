/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.KolmogorovSolution
import Formalization.Normal.MillRatio
import Mathlib.Probability.CDF
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Section 2 Gap Proofs (`SWEEP-A`: `A4`, `A5`)

Proves the Section 2 prose characterization and Gaussian tail display in Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `sec2_cor2_3_iff_stdNormal_proof` (`SteinIntro.tex:597-600`, `A4`): for any real-valued random
  variable $W$, the left-hand side $|\mathbb{P}(W \le x) - \Phi(x)|$ of `(2.2)` vanishes for all
  $x \in \mathbb{R}$ iff $W \sim \mathcal{N}(0, 1)$, and the right-hand side of `(2.2)` likewise
  vanishes for all $x \in \mathbb{R}$ iff $W \sim \mathcal{N}(0, 1)$ (both for `normalSteinOpLeft`
  and for the two-sided operator `normalSteinOp`).
* `sec2_stdNormalCDF_tail_le_proof` (`SteinIntro.tex:612-615`, `A5`): for all $w > 0$,
  $1 - \Phi(w) \le \min\{1/2, 1/(w\sqrt{2\pi})\} e^{-w^2/2}$.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SteinMethod

/-! ### Section 1: Standard Normal CDF vs `ProbabilityTheory.cdf` and Atomless Property -/

private lemma cdf_stdNormalLaw_eq (x : ℝ) :
    ProbabilityTheory.cdf stdNormalLaw x = stdNormalCDF x :=
  rfl

private lemma stdNormalLaw_singleton (x : ℝ) : stdNormalLaw {x} = 0 := by
  have hvol : (volume : Measure ℝ) {x} = 0 := by
    rw [← Icc_self x, Real.volume_Icc, sub_self, ENNReal.ofReal_zero]
  rw [stdNormalLaw, ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact withDensity_absolutelyContinuous volume _ hvol

private lemma abs_integral_normalSteinOp_kolm_of_singleton_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW : AEMeasurable W P) {x : ℝ} (hx : (P.map W) {x} = 0) :
    |∫ ω, normalSteinOp (normalSteinSolKolm x) (W ω) ∂P| =
      |P.real {ω | W ω ≤ x} - stdNormalCDF x| := by
  rw [abs_measureReal_Iic_sub_stdNormalCDF_eq P hW x]
  congr 1
  have hpre : P {ω | W ω = x} = 0 := by
    have hm := Measure.map_apply_of_aemeasurable hW (measurableSet_singleton x)
    simpa only [preimage, mem_singleton_iff] using hm.symm.trans hx
  have hae : ∀ᵐ ω ∂P, W ω ≠ x := by
    rw [ae_iff]
    simpa only [not_ne_iff] using hpre
  refine integral_congr_ae (hae.mono fun ω hω ↦ ?_)
  have hd := (hasDerivAt_normalSteinSolKolm_of_ne x hω).deriv
  dsimp only [normalSteinOp]
  rw [hd, normalSteinOpLeft_normalSteinSolKolm]
  ring

/-! ### Section 2: All-`x` Characterization of `stdNormalLaw` (`Sec2_cor2_3_iff_stdNormal`) -/

/-- Library proof of `Sec2_cor2_3_iff_stdNormal` (`SteinIntro.tex:597-600`). -/
theorem sec2_cor2_3_iff_stdNormal_proof
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW : AEMeasurable W P) :
    ((∀ x : ℝ, |P.real {ω | W ω ≤ x} - stdNormalCDF x| = 0) ↔ P.map W = stdNormalLaw) ∧
    ((∀ x : ℝ, |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P| = 0) ↔
      P.map W = stdNormalLaw) ∧
    ((∀ x : ℝ, |∫ ω, normalSteinOp (normalSteinSolKolm x) (W ω) ∂P| = 0) ↔
      P.map W = stdNormalLaw) := by
  let μ : Measure ℝ := P.map W
  have hμ_prob : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  have hcdf_W : ∀ x : ℝ, P.real {ω | W ω ≤ x} = ProbabilityTheory.cdf μ x := fun x ↦ by
    rw [ProbabilityTheory.cdf_eq_real]
    exact (map_measureReal_apply_of_aemeasurable hW measurableSet_Iic).symm
  have h1 : (∀ x : ℝ, |P.real {ω | W ω ≤ x} - stdNormalCDF x| = 0) ↔
      μ = stdNormalLaw := by
    constructor
    · intro hall
      refine Measure.eq_of_cdf μ stdNormalLaw (StieltjesFunction.ext fun x ↦ ?_)
      have hx := sub_eq_zero.mp (abs_eq_zero.mp (hall x))
      rwa [hcdf_W x, ← cdf_stdNormalLaw_eq x] at hx
    · intro hμ x
      rw [hcdf_W x, hμ, cdf_stdNormalLaw_eq x, sub_self, abs_zero]
  have h2 : (∀ x : ℝ, |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P| = 0) ↔
      μ = stdNormalLaw := by
    simp_rw [← abs_measureReal_Iic_sub_stdNormalCDF_eq P hW]
    exact h1
  refine ⟨h1, h2, ?_⟩
  constructor
  · intro hall
    let S : Set ℝ :=
      {x : ℝ | Function.leftLim (ProbabilityTheory.cdf μ) x ≠ ProbabilityTheory.cdf μ x}
    have hS_cnt : S.Countable := (ProbabilityTheory.cdf μ).countable_leftLim_ne
    have hS_dense : Dense Sᶜ := hS_cnt.dense_compl ℝ
    refine Measure.eq_of_cdf μ stdNormalLaw (StieltjesFunction.ext fun x ↦ ?_)
    have hlim : ∀ ε : ℝ, 0 < ε → ∃ y ∈ Ioo x (x + ε),
        ProbabilityTheory.cdf μ y = ProbabilityTheory.cdf stdNormalLaw y := by
      intro ε hε
      have hne : (Ioo x (x + ε)).Nonempty := ⟨x + ε / 2, by linarith, by linarith⟩
      obtain ⟨y, hy_open, hy_compl⟩ := hS_dense.inter_open_nonempty _ isOpen_Ioo hne
      have hy_left : Function.leftLim (ProbabilityTheory.cdf μ) y = ProbabilityTheory.cdf μ y :=
        not_ne_iff.mp hy_compl
      have hy0 : μ {y} = 0 := by
        rw [← ProbabilityTheory.measure_cdf μ, StieltjesFunction.measure_singleton, hy_left,
          sub_self, ENNReal.ofReal_zero]
      have heq := abs_integral_normalSteinOp_kolm_of_singleton_eq_zero P hW hy0
      rw [hall y] at heq
      have hsub := sub_eq_zero.mp (abs_eq_zero.mp heq.symm)
      rw [hcdf_W y, ← cdf_stdNormalLaw_eq y] at hsub
      exact ⟨y, hy_open, hsub⟩
    choose y hy_mem hy_eq using fun n : ℕ ↦ hlim (1 / ((n : ℝ) + 1)) (by positivity)
    have hy_tend : Tendsto y atTop (𝓝[≥] x) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (by simpa only [add_zero] using
            tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
          (fun n ↦ (hy_mem n).1.le) (fun n ↦ (hy_mem n).2.le)
      · exact mem_Ici.mpr (hy_mem n).1.le
    have ht1 : Tendsto (fun n ↦ ProbabilityTheory.cdf μ (y n)) atTop
        (𝓝 (ProbabilityTheory.cdf μ x)) :=
      ((ProbabilityTheory.cdf μ).right_continuous x).tendsto.comp hy_tend
    have ht2 : Tendsto (fun n ↦ ProbabilityTheory.cdf stdNormalLaw (y n)) atTop
        (𝓝 (ProbabilityTheory.cdf stdNormalLaw x)) :=
      ((ProbabilityTheory.cdf stdNormalLaw).right_continuous x).tendsto.comp hy_tend
    exact tendsto_nhds_unique ht1 (by simpa only [hy_eq] using ht2)
  · intro hμ x
    have hx0 : (P.map W) {x} = 0 := by
      rw [hμ]
      exact stdNormalLaw_singleton x
    rw [abs_integral_normalSteinOp_kolm_of_singleton_eq_zero P hW hx0]
    exact h1.mpr hμ x

/-! ### Section 3: Standard Normal Upper-Tail Bound (`Sec2_stdNormalCDF_tail_le`) -/

private lemma sqrt_four_eq_two : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private lemma one_sub_stdNormalCDF_le_half_exp (w : ℝ) (hw : 0 ≤ w) :
    1 - stdNormalCDF w ≤ (1 / 2) * Real.exp (-w ^ 2 / 2) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  by_cases hcase : Real.sqrt (2 / Real.pi) ≤ w
  · have hprod : 2 ≤ w * Real.sqrt (2 * Real.pi) := by
      calc
        (2 : ℝ) = Real.sqrt 4 := sqrt_four_eq_two.symm
        _ = Real.sqrt ((2 / Real.pi) * (2 * Real.pi)) := by
            congr 1
            field_simp [hpi_pos.ne']
            ring
        _ = Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) :=
            Real.sqrt_mul (by positivity) _
        _ ≤ w * Real.sqrt (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right hcase hsqrt_pos.le
    have hw_pos : 0 < w := lt_of_lt_of_le (Real.sqrt_pos.mpr (by positivity)) hcase
    have hmill := mul_one_sub_stdNormalCDF_le w hw
    have hdiv : 1 - stdNormalCDF w ≤ stdNormalPDF w / w :=
      (le_div_iff₀ hw_pos).mpr (by linarith)
    rw [stdNormalPDF_eq] at hdiv
    calc
      1 - stdNormalCDF w ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-w ^ 2 / 2) / w := hdiv
      _ = (1 / (w * Real.sqrt (2 * Real.pi))) * Real.exp (-w ^ 2 / 2) := by ring
      _ ≤ (1 / 2) * Real.exp (-w ^ 2 / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact one_div_le_one_div_of_le (by norm_num) hprod
  · have hlt : w < Real.sqrt (2 / Real.pi) := lt_of_not_ge hcase
    let g : ℝ → ℝ := fun t ↦ (1 / 2) * Real.exp (-t ^ 2 / 2) - (1 - stdNormalCDF t)
    have hg0 : g 0 = 0 := by
      simp only [g, stdNormalCDF_zero]
      norm_num
    have hg_deriv : ∀ t : ℝ,
        HasDerivAt g (Real.exp (-t ^ 2 / 2) * ((Real.sqrt (2 * Real.pi))⁻¹ - t / 2)) t := by
      intro t
      have hexp : HasDerivAt (fun u : ℝ ↦ -u ^ 2 / 2) (-t) t := by
        simpa using ((hasDerivAt_pow 2 t).neg.div_const (2 : ℝ)).congr_deriv (by ring)
      have h1 : HasDerivAt (fun u : ℝ ↦ (1 / 2 : ℝ) * Real.exp (-u ^ 2 / 2))
          ((1 / 2 : ℝ) * (Real.exp (-t ^ 2 / 2) * (-t))) t :=
        ((Real.hasDerivAt_exp _).comp t hexp).const_mul (1 / 2 : ℝ)
      have h2 : HasDerivAt (fun u : ℝ ↦ 1 - stdNormalCDF u) (-stdNormalPDF t) t := by
        simpa only [zero_sub] using
          (hasDerivAt_const t (1 : ℝ)).fun_sub (hasDerivAt_stdNormalCDF t)
      refine (h1.fun_sub h2).congr_deriv ?_
      rw [stdNormalPDF_eq]
      ring
    have hg_mono : MonotoneOn g (Icc 0 w) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 w)
        (fun t _ ↦ (hg_deriv t).continuousAt.continuousWithinAt)
        (fun t _ ↦ (hg_deriv t).differentiableAt.differentiableWithinAt)
        fun t ht ↦ ?_
      rw [interior_Icc] at ht
      rw [(hg_deriv t).deriv]
      refine mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr ?_)
      have ht_lt : t < Real.sqrt (2 / Real.pi) := ht.2.trans hlt
      have hmul_le : t * Real.sqrt (2 * Real.pi) ≤ 2 := by
        calc
          t * Real.sqrt (2 * Real.pi) ≤ Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi) :=
            mul_le_mul_of_nonneg_right ht_lt.le hsqrt_pos.le
          _ = Real.sqrt ((2 / Real.pi) * (2 * Real.pi)) :=
            (Real.sqrt_mul (by positivity) _).symm
          _ = Real.sqrt 4 := by
            congr 1
            field_simp [hpi_pos.ne']
            ring
          _ = 2 := sqrt_four_eq_two
      rw [inv_eq_one_div, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsqrt_pos]
      linarith
    have h0_le_gw : 0 ≤ g w := by
      rw [← hg0]
      exact hg_mono ⟨le_rfl, hw⟩ ⟨hw, le_rfl⟩ hw
    dsimp only [g] at h0_le_gw
    linarith

/-- Library proof of `Sec2_stdNormalCDF_tail_le` (`SteinIntro.tex:612-615`). -/
theorem sec2_stdNormalCDF_tail_le_proof (w : ℝ) (hw : 0 < w) :
    1 - stdNormalCDF w ≤
      min (1 / 2) (1 / (w * Real.sqrt (2 * Real.pi))) * Real.exp (-w ^ 2 / 2) := by
  rcases min_cases (1 / 2 : ℝ) (1 / (w * Real.sqrt (2 * Real.pi))) with
    ⟨hmin, _⟩ | ⟨hmin, _⟩
  · rw [hmin]
    exact one_sub_stdNormalCDF_le_half_exp w hw.le
  · rw [hmin]
    have hmill := mul_one_sub_stdNormalCDF_le w hw.le
    have hdiv : 1 - stdNormalCDF w ≤ stdNormalPDF w / w :=
      (le_div_iff₀ hw).mpr (by linarith)
    rw [stdNormalPDF_eq] at hdiv
    exact hdiv.trans_eq (by ring)

end SteinMethod
