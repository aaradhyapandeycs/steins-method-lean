/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Kolmogorov.BinomialOrder
import Formalization.Normal.IndependentSums
import Formalization.Normal.KolmogorovSolution
import Formalization.Normal.SolutionBounds
import Formalization.Normal.WassersteinBound
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi

/-!
# Section 3 Opening & Section 3.1 Gap Proofs (`SWEEP-A`: `A8a`, `A8b`, `A9`, `SA-8`)

Proves the Section 3 opening regularity contrast and Section 3.1 prose claims in Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `sec3_opening_steinSol_regularity_proof` (`SteinIntro.tex:711-716`, `A8a`) and
  `not_sec3_normalSteinSol_mem_wassersteinClass_strictReading_proof` (`A8b`);
* `sec3_1_iid_wasserstein_rate_proof` (`SteinIntro.tex:743-744`, `A9`);
* `sec3_1_indepSum_thirdMoment_proof` (`SteinIntro.tex:746-747`, `SA-8`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Stein-Solution Regularity (`A8a`, `A8b`, `SteinIntro.tex:711-716`) -/

private lemma lipschitzWith_two_of_ac_deriv_le_two {g : ℝ → ℝ}
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b)
    (h2 : ∀ u : ℝ, |deriv g u| ≤ 2) :
    LipschitzWith 2 g := by
  rw [lipschitzWith_iff_dist_le_mul]
  have hstep : ∀ a b : ℝ, a ≤ b → |g b - g a| ≤ 2 * (b - a) := by
    intro a b hab
    rw [← (hac a b).integral_deriv_eq_sub, intervalIntegral.integral_of_le hab,
      ← Real.norm_eq_abs]
    have hae : ∀ᵐ u : ℝ, ‖deriv g u‖ ≤ 2 :=
      Eventually.of_forall fun u ↦ by rw [Real.norm_eq_abs]; exact h2 u
    have hb := norm_setIntegral_le_of_norm_le_const_ae
      (s := Ioc a b) measure_Ioc_lt_top (ae_restrict_of_ae hae)
    simpa [Real.volume_real_Ioc_of_le hab, mul_comm] using hb
  intro x y
  rw [NNReal.coe_ofNat, Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm (g x), abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hstep x y hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hstep y x hyx

private lemma integrable_stdNormalLaw_of_lipschitzWith_one
    {h : ℝ → ℝ} (hh : LipschitzWith 1 h) :
    Integrable h stdNormalLaw := by
  have hid : Integrable id stdNormalLaw :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
  refine ((integrable_const |h 0|).add hid.norm).mono' hh.continuous.aestronglyMeasurable
    (Eventually.of_forall fun t ↦ ?_)
  have hd := hh.dist_le_mul t 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero, NNReal.coe_one, one_mul] at hd
  dsimp only [Pi.add_apply, id_eq]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (h t) (h 0)]

private lemma not_differentiable_abs : ¬ Differentiable ℝ (fun x : ℝ ↦ |x|) := by
  intro hd
  have hd0 : DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := hd 0
  have hpos : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).hasDerivWithinAt.congr (fun x hx ↦ abs_of_nonneg hx) (abs_zero)
  have hneg : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).neg.hasDerivWithinAt.congr (fun x hx ↦ abs_of_nonpos hx)
      (by simp)
  have heq1 : deriv (fun x : ℝ ↦ |x|) 0 = 1 :=
    (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd0.hasDerivAt.hasDerivWithinAt hpos
  have heq2 : deriv (fun x : ℝ ↦ |x|) 0 = -1 :=
    (uniqueDiffWithinAt_Iic (0 : ℝ)).eq_deriv _ hd0.hasDerivAt.hasDerivWithinAt hneg
  linarith

private lemma not_differentiable_deriv_normalSteinSolKolm (x : ℝ) :
    ¬ Differentiable ℝ (deriv (normalSteinSolKolm x)) := by
  intro hd
  have hcont : ContinuousAt (deriv (normalSteinSolKolm x)) x := (hd x).continuousAt
  let u : ℕ → ℝ := fun n ↦ x - 1 / ((n : ℝ) + 1)
  let v : ℕ → ℝ := fun n ↦ x + 1 / ((n : ℝ) + 1)
  have hstep : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hu_lim : Tendsto u atTop (𝓝 x) := by
    simpa only [u, sub_zero] using tendsto_const_nhds.sub hstep
  have hv_lim : Tendsto v atTop (𝓝 x) := by
    simpa only [v, add_zero] using tendsto_const_nhds.add hstep
  have hu_eq : ∀ n : ℕ, deriv (normalSteinSolKolm x) (u n) =
      u n * normalSteinSolKolm x (u n) + 1 - stdNormalCDF x := fun n ↦ by
    have hlt : u n < x := sub_lt_self x (by positivity)
    have hmem : u n ∈ Iic x := hlt.le
    rw [(hasDerivAt_normalSteinSolKolm_of_ne x hlt.ne).deriv,
      indicator_of_mem hmem, Pi.one_apply]
  have hv_eq : ∀ n : ℕ, deriv (normalSteinSolKolm x) (v n) =
      v n * normalSteinSolKolm x (v n) - stdNormalCDF x := fun n ↦ by
    have hgt : x < v n := lt_add_of_pos_right x (by positivity)
    have hnot : v n ∉ Iic x := not_le.mpr hgt
    rw [(hasDerivAt_normalSteinSolKolm_of_ne x hgt.ne').deriv,
      indicator_of_notMem hnot, add_zero]
  have hprod_u : Tendsto (fun n ↦ u n * normalSteinSolKolm x (u n)) atTop
      (𝓝 (x * normalSteinSolKolm x x)) :=
    hu_lim.mul ((continuous_normalSteinSolKolm x).continuousAt.tendsto.comp hu_lim)
  have hprod_v : Tendsto (fun n ↦ v n * normalSteinSolKolm x (v n)) atTop
      (𝓝 (x * normalSteinSolKolm x x)) :=
    hv_lim.mul ((continuous_normalSteinSolKolm x).continuousAt.tendsto.comp hv_lim)
  have hlim_u : Tendsto (fun n ↦ deriv (normalSteinSolKolm x) (u n)) atTop
      (𝓝 (x * normalSteinSolKolm x x + 1 - stdNormalCDF x)) := by
    simpa only [hu_eq] using (hprod_u.add tendsto_const_nhds).sub tendsto_const_nhds
  have hlim_v : Tendsto (fun n ↦ deriv (normalSteinSolKolm x) (v n)) atTop
      (𝓝 (x * normalSteinSolKolm x x - stdNormalCDF x)) := by
    simpa only [hv_eq] using hprod_v.sub tendsto_const_nhds
  have heq_u : deriv (normalSteinSolKolm x) x =
      x * normalSteinSolKolm x x + 1 - stdNormalCDF x :=
    tendsto_nhds_unique (hcont.tendsto.comp hu_lim) hlim_u
  have heq_v : deriv (normalSteinSolKolm x) x =
      x * normalSteinSolKolm x x - stdNormalCDF x :=
    tendsto_nhds_unique (hcont.tendsto.comp hv_lim) hlim_v
  linarith

/-- Library proof of `Sec3_opening_steinSol_regularity` (`SteinIntro.tex:711-716`). -/
theorem sec3_opening_steinSol_regularity_proof :
    (∀ h : ℝ → ℝ, LipschitzWith 1 h →
      Differentiable ℝ (normalSteinSol h) ∧
      (∀ w : ℝ, |normalSteinSol h w| ≤ 2) ∧
      (∀ w : ℝ, |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi)) ∧
      LipschitzWith 2 (deriv (normalSteinSol h)) ∧
      (normalSteinSol h ∈ normalWassersteinClass ↔ Differentiable ℝ h)) ∧
    (∀ x : ℝ,
      ¬ Differentiable ℝ (normalSteinSolKolm x) ∧
      ¬ Differentiable ℝ (deriv (normalSteinSolKolm x))) := by
  refine ⟨fun h hh ↦ ?_, fun x ↦ ⟨fun hd ↦
    not_differentiableAt_normalSteinSolKolm x (hd x),
    not_differentiable_deriv_normalSteinSolKolm x⟩⟩
  have hcont : Continuous h := hh.continuous
  have hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b :=
    fun a b ↦ hh.lipschitzOnWith.absolutelyContinuousOnInterval
  have hderiv_le : ∀ t : ℝ, |deriv h t| ≤ 1 := fun t ↦ by
    simpa only [Real.norm_eq_abs, NNReal.coe_one] using norm_deriv_le_of_lipschitz (x₀ := t) hh
  have hh_int : Integrable h stdNormalLaw := integrable_stdNormalLaw_of_lipschitzWith_one hh
  have hf_diff : Differentiable ℝ (normalSteinSol h) :=
    fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hh_int hcont w).differentiableAt
  have hderiv_eq : deriv (normalSteinSol h) =
      fun w ↦ w * normalSteinSol h w + h w - stdNormalExpect h :=
    funext fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hh_int hcont w).deriv
  have hb0 : ∀ w : ℝ, |normalSteinSol h w| ≤ 2 := fun w ↦ by
    simpa only [mul_one] using abs_normalSteinSol_le_of_lipschitzDeriv hac hderiv_le w
  have hb1 : ∀ w : ℝ, |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi) := fun w ↦ by
    simpa only [mul_one] using abs_deriv_normalSteinSol_le_of_lipschitzDeriv hac hderiv_le w
  have hb2 : ∀ w : ℝ, |deriv (deriv (normalSteinSol h)) w| ≤ 2 := fun w ↦ by
    simpa only [mul_one] using
      abs_iteratedDeriv_two_normalSteinSol_le_of_lipschitzDeriv hac hderiv_le w
  have hcd_wf : ContDiff ℝ 1 (fun w : ℝ ↦ w * normalSteinSol h w) := by
    have hcd_f : ContDiff ℝ 1 (normalSteinSol h) := by
      rw [contDiff_one_iff_deriv]
      refine ⟨hf_diff, ?_⟩
      rw [hderiv_eq]
      exact ((continuous_id.mul hf_diff.continuous).add hcont).sub continuous_const
    exact contDiff_id.mul hcd_f
  have hac_df : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (deriv (normalSteinSol h)) a b := by
    intro a b
    rw [hderiv_eq]
    exact ((hcd_wf.contDiffOn.absolutelyContinuousOnInterval.add (hac a b)).sub
      (LipschitzWith.const (stdNormalExpect h)).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hlip2 : LipschitzWith 2 (deriv (normalSteinSol h)) :=
    lipschitzWith_two_of_ac_deriv_le_two hac_df hb2
  refine ⟨hf_diff, hb0, hb1, hlip2, ?_⟩
  constructor
  · intro hf_mem
    have hdf_diff : Differentiable ℝ (deriv (normalSteinSol h)) := hf_mem.2.1
    have hh_eq : h = fun w ↦ deriv (normalSteinSol h) w - w * normalSteinSol h w +
        stdNormalExpect h := by
      ext w
      have hw := congr_fun hderiv_eq w
      linarith
    rw [hh_eq]
    exact (hdf_diff.fun_sub (differentiable_fun_id.fun_mul hf_diff)).add_const _
  · intro hh_diff
    refine ⟨hf_diff, ?_, hb0, hb1, hb2⟩
    rw [hderiv_eq]
    exact ((differentiable_fun_id.fun_mul hf_diff).fun_add hh_diff).sub_const _

/-- Library proof of `not_Sec3_normalSteinSol_mem_wassersteinClass_strictReading`
(`SteinIntro.tex:711-713`). -/
theorem not_sec3_normalSteinSol_mem_wassersteinClass_strictReading_proof :
    ∃ h : ℝ → ℝ, LipschitzWith 1 h ∧
      ¬ Differentiable ℝ (deriv (normalSteinSol h)) ∧
      normalSteinSol h ∉ normalWassersteinClass := by
  let h : ℝ → ℝ := fun x ↦ |x|
  have hh_lip : LipschitzWith 1 h :=
    LipschitzWith.mk_one fun x y ↦ by
      rw [Real.dist_eq, Real.dist_eq]
      exact abs_abs_sub_abs_le_abs_sub x y
  have hreg := sec3_opening_steinSol_regularity_proof.1 h hh_lip
  have hnot_mem : normalSteinSol h ∉ normalWassersteinClass :=
    fun hmem ↦ not_differentiable_abs (hreg.2.2.2.2.mp hmem)
  have hnot_diff : ¬ Differentiable ℝ (deriv (normalSteinSol h)) := by
    intro hdf
    apply hnot_mem
    have hh_int := integrable_stdNormalLaw_of_lipschitzWith_one hh_lip
    have hderiv_eq : deriv (normalSteinSol h) =
        fun w ↦ w * normalSteinSol h w + h w - stdNormalExpect h :=
      funext fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hh_int hh_lip.continuous w).deriv
    have hh_eq : h = fun w ↦ deriv (normalSteinSol h) w - w * normalSteinSol h w +
        stdNormalExpect h := by
      ext w
      have hw := congr_fun hderiv_eq w
      linarith
    have hh_diff : Differentiable ℝ h := by
      rw [hh_eq]
      exact (hdf.fun_sub (differentiable_fun_id.fun_mul hreg.1)).add_const _
    exact hreg.2.2.2.2.mpr hh_diff
  exact ⟨h, hh_lip, hnot_diff, hnot_mem⟩

/-! ### Section 2: i.i.d. Wasserstein Rate & Optimality (`A9`, `SteinIntro.tex:743-744`) -/

private lemma rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hx, Real.rpow_one]

/-- Library proof of `Sec3_1_iid_wasserstein_rate` (`SteinIntro.tex:743-744`). -/
theorem sec3_1_iid_wasserstein_rate_proof :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {X : ℕ → Ω → ℝ},
      (∀ i : ℕ, AEMeasurable (X i) P) →
      ProbabilityTheory.iIndepFun X P →
      (∀ i : ℕ, ProbabilityTheory.IdentDistrib (X i) (X 0) P P) →
      MemLp (X 0) 4 P →
      ∫ ω, X 0 ω ∂P = 0 →
      ∫ ω, X 0 ω ^ 2 ∂P = 1 →
      let C : ℝ := (∫ ω, |X 0 ω| ^ 3 ∂P) + Real.sqrt (2 / Real.pi * ∫ ω, X 0 ω ^ 4 ∂P)
      ∀ n : ℕ, 0 < n →
        let W_n : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / Real.sqrt n
        wassersteinDist (P.map W_n) stdNormalLaw ≤ ENNReal.ofReal (C / Real.sqrt n)) ∧
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (X : ℕ → Ω → ℝ) (c : ℝ),
      0 < c ∧
      (∀ i : ℕ, AEMeasurable (X i) P) ∧
      ProbabilityTheory.iIndepFun X P ∧
      (∀ i : ℕ, ProbabilityTheory.IdentDistrib (X i) (X 0) P P) ∧
      MemLp (X 0) 4 P ∧
      ∫ ω, X 0 ω ∂P = 0 ∧
      ∫ ω, X 0 ω ^ 2 ∂P = 1 ∧
      ∀ n : ℕ, 0 < n →
        let W_n : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / Real.sqrt n
        ENNReal.ofReal (c / Real.sqrt n) ≤ wassersteinDist (P.map W_n) stdNormalLaw) := by
  constructor
  · intro Ω _ P _ X hX_meas h_indep h_ident hX4 hX0 hX2 C n hn W_n
    let Y : Fin n → Ω → ℝ := fun i ↦ X i.1
    have hY_meas : ∀ i : Fin n, AEMeasurable (Y i) P := fun i ↦ hX_meas i.1
    have hY_indep : iIndepFun Y P := h_indep.precomp Fin.val_injective
    have hY4 : ∀ i : Fin n, MemLp (Y i) 4 P := fun i ↦ (h_ident i.1).symm.memLp_snd hX4
    have hY0 : ∀ i : Fin n, ∫ ω, Y i ω ∂P = 0 :=
      fun i ↦ (h_ident i.1).integral_eq.trans hX0
    have hY2 : ∀ i : Fin n, ∫ ω, Y i ω ^ 2 ∂P = 1 := fun i ↦
      ((h_ident i.1).comp (measurable_id.pow_const 2)).integral_eq.trans hX2
    have hY3_eq : ∀ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P = ∫ ω, |X 0 ω| ^ 3 ∂P := fun i ↦
      ((h_ident i.1).comp (continuous_abs.pow 3).measurable).integral_eq
    have hY4_eq : ∀ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P = ∫ ω, X 0 ω ^ 4 ∂P := fun i ↦
      ((h_ident i.1).comp (measurable_id.pow_const 4)).integral_eq
    have hW_eq : W_n = fun ω ↦ (∑ i : Fin n, Y i ω) / Real.sqrt n := by
      ext ω
      dsimp only [W_n, Y]
      rw [← Fin.sum_univ_eq_sum_range (fun k ↦ X k ω) n]
    have hstein := wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P stdNormalLaw
      (indepSum_aemeasurable_W hY_meas) aemeasurable_id Measure.map_id
    have hthm := indepSum_wasserstein_clt_of_stein_bound P stdNormalLaw hn
      hY_meas hY_indep hY4 hY0 hY2 hstein
    dsimp only at hthm
    rw [Measure.map_id, ← hW_eq] at hthm
    refine hthm.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    have hsum3 : (∑ i : Fin n, ∫ ω, |Y i ω| ^ 3 ∂P) =
        (n : ℝ) * ∫ ω, |X 0 ω| ^ 3 ∂P := by
      simp_rw [hY3_eq]
      simp
    have hsum4 : (∑ i : Fin n, ∫ ω, Y i ω ^ 4 ∂P) =
        (n : ℝ) * ∫ ω, X 0 ω ^ 4 ∂P := by
      simp_rw [hY4_eq]
      simp
    dsimp only [C]
    rw [hsum3, hsum4, rpow_three_halves_eq_mul_sqrt hn_pos,
      Real.sqrt_mul hn_pos.le, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / Real.pi),
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
    have hnsq : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn_pos.le).symm
    have hpi_sqrt_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    conv_lhs =>
      arg 2
      rw [hnsq]
    field_simp [hn_pos.ne', hsqrt_pos.ne', hpi_sqrt_ne]
    rw [Real.sqrt_sq hsqrt_pos.le]
    ring
  · let μ₀ : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
    let P : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ ↦ μ₀
    let rad : Bool → ℝ := fun b ↦ if b then 1 else -1
    let X : ℕ → (ℕ → Bool) → ℝ := fun i ω ↦ rad (ω i)
    let σ₀ : ℝ := Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2))
    let L : ℝ := 2 / (Real.pi * σ₀)
    let c : ℝ := stdNormalPDF L * L / (4 * Real.pi * σ₀)
    have hσ₀_pos : 0 < σ₀ := Real.sqrt_pos.mpr (by norm_num)
    have hL_pos : 0 < L := div_pos zero_lt_two (mul_pos Real.pi_pos hσ₀_pos)
    have hc_pos : 0 < c :=
      div_pos (mul_pos (stdNormalPDF_pos L) hL_pos) (by positivity)
    have hrad_meas : Measurable rad := Measurable.of_discrete
    have hX_meas_strong : ∀ i : ℕ, Measurable (X i) :=
      fun i ↦ hrad_meas.comp (measurable_pi_apply i)
    have h_indep : iIndepFun X P :=
      ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ₀) (X := fun _ ↦ rad)
        (fun _ ↦ hrad_meas)
    have hmap_i : ∀ i : ℕ, P.map (X i) = μ₀.map rad := fun i ↦ by
      have heval : P.map (fun ω : ℕ → Bool ↦ ω i) = μ₀ :=
        Measure.infinitePi_map_eval (fun _ : ℕ ↦ μ₀) i
      change P.map (rad ∘ fun ω : ℕ → Bool ↦ ω i) = μ₀.map rad
      rw [← Measure.map_map hrad_meas (measurable_pi_apply i), heval]
    have h_ident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P := fun i ↦
      ⟨(hX_meas_strong i).aemeasurable, (hX_meas_strong 0).aemeasurable,
        (hmap_i i).trans (hmap_i 0).symm⟩
    have hX0_lp4 : MemLp (X 0) 4 P :=
      MemLp.of_bound (hX_meas_strong 0).aestronglyMeasurable 1
        (Eventually.of_forall fun ω ↦ by
          dsimp only [X, rad]
          cases ω 0 <;> norm_num)
    have hμ₀_singleton : ∀ b : Bool, μ₀.real {b} = 1 / 2 := fun b ↦ by
      rw [Measure.real, PMF.toMeasure_uniformOfFintype_apply _ (MeasurableSet.singleton b)]
      simp
    have hX0_mean : ∫ ω, X 0 ω ∂P = 0 := by
      have hi : ∫ ω, X 0 ω ∂P = ∫ x, id x ∂(P.map (X 0)) :=
        (integral_map (hX_meas_strong 0).aemeasurable aestronglyMeasurable_id).symm
      rw [hi, hmap_i 0, integral_map hrad_meas.aemeasurable aestronglyMeasurable_id,
        integral_fintype Integrable.of_finite]
      simp [hμ₀_singleton, rad]
    have hX0_sq : ∫ ω, X 0 ω ^ 2 ∂P = 1 := by
      have hsq1 : (fun ω : ℕ → Bool ↦ X 0 ω ^ 2) = fun _ ↦ (1 : ℝ) := by
        ext ω
        dsimp only [X, rad]
        cases ω 0 <;> norm_num
      rw [hsq1, integral_const, probReal_univ, one_smul]
    refine ⟨ℕ → Bool, inferInstance, P, inferInstance, X, c, hc_pos,
      fun i ↦ (hX_meas_strong i).aemeasurable, h_indep, h_ident, hX0_lp4, hX0_mean, hX0_sq,
      fun n hn ↦ ?_⟩
    intro W_n
    let B : Fin n → (ℕ → Bool) → ℝ := fun i ω ↦ if ω i.1 then 1 else 0
    have hB_meas : ∀ i : Fin n, Measurable (B i) :=
      fun i ↦
        (Measurable.of_discrete :
          Measurable fun b : Bool ↦ if b then (1 : ℝ) else 0).comp
        (measurable_pi_apply i.1)
    have hB_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, B i ω = 0 ∨ B i ω = 1 :=
      fun i ↦ Eventually.of_forall fun ω ↦ by
        dsimp only [B]
        cases ω i.1 <;> simp
    have hlow := le_binomial_wassersteinDist (p := 1 / 2) (by norm_num) (by norm_num)
      P stdNormalLaw hn hB_meas hB_01 aemeasurable_id Measure.map_id
    dsimp only at hlow
    rw [Measure.map_id] at hlow
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsqrt_quarter : Real.sqrt ((n : ℝ) * (1 / 2) * (1 - 1 / 2)) = Real.sqrt n / 2 := by
      have hq : (n : ℝ) * (1 / 2) * (1 - 1 / 2) = (n : ℝ) / 4 := by ring
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hq, Real.sqrt_div hn_pos.le, h4]
    have hW_eq : (fun ω : ℕ → Bool ↦
        ((∑ i : Fin n, B i ω) - (n : ℝ) * (1 / 2)) /
          Real.sqrt ((n : ℝ) * (1 / 2) * (1 - 1 / 2))) = W_n := by
      ext ω
      rw [hsqrt_quarter]
      dsimp only [W_n, X, B, rad]
      have hrad_B : ∀ k : ℕ, (if ω k then (1 : ℝ) else -1) =
          2 * (if ω k then (1 : ℝ) else 0) - 1 := fun k ↦ by
        cases ω k <;> norm_num
      simp_rw [hrad_B]
      rw [← Fin.sum_univ_eq_sum_range (fun k ↦ 2 * (if ω k then (1 : ℝ) else 0) - 1) n,
        Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      have hsqrt_ne : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
      field_simp [hsqrt_ne]
    have hrpow : (n : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt n)⁻¹ := by
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hn_pos.le,
        ← Real.sqrt_eq_rpow]
    rw [hW_eq] at hlow
    convert hlow using 2
    dsimp only [c, L, σ₀]
    rw [hrpow, div_eq_mul_inv]

/-! ### Section 3: Third-Moment Modification of Theorem 3.2 (`SA-8`, `SteinIntro.tex:746-747`) -/

/-- Library proof of `Sec3_1_indepSum_thirdMoment` (`SteinIntro.tex:746-747`). -/
theorem sec3_1_indepSum_thirdMoment_proof
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX3 : ∀ i : Fin n, MemLp (X i) 3 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX2 : ∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (3 / (n : ℝ) ^ (3 / 2 : ℝ) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := by
  intro W
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hW_meas : AEMeasurable W P := indepSum_aemeasurable_W hX_meas
  refine (wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P' hW_meas hZ hZ_law).trans ?_
  refine iSup₂_le fun f hf ↦ ENNReal.ofReal_le_ofReal ?_
  rcases hf with ⟨hf1, hf2, hf0, hf1_le, hf2_le⟩
  let W_i : Fin n → Ω → ℝ := fun i ω ↦
    (∑ j ∈ Finset.univ.erase i, X j ω) / Real.sqrt n
  have hWi_meas : ∀ i : Fin n, AEMeasurable (W_i i) P := fun i ↦
    ((Finset.univ.erase i).aemeasurable_fun_sum fun j _ ↦ hX_meas j).div_const (Real.sqrt n)
  have hX1 : ∀ i : Fin n, Integrable (X i) P :=
    fun i ↦ memLp_one_iff_integrable.mp ((hX3 i).mono_exponent (by norm_num))
  have hX_sq : ∀ i : Fin n, Integrable (fun ω ↦ X i ω ^ 2) P :=
    fun i ↦ ((hX3 i).mono_exponent (by norm_num)).integrable_sq
  have hX_cube : ∀ i : Fin n, Integrable (fun ω ↦ |X i ω| ^ 3) P := fun i ↦ by
    simpa [Real.norm_eq_abs] using (hX3 i).integrable_norm_pow (by decide)
  have h_diff : ∀ (i : Fin n) (ω : Ω), W ω - W_i i ω = X i ω / Real.sqrt n := fun i ω ↦ by
    dsimp only [W, W_i]
    rw [← sub_div, ← Finset.add_sum_erase Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)]
    ring
  have hfW_asm : AEStronglyMeasurable (fun ω ↦ f (W ω)) P :=
    (hf1.continuous.measurable.comp_aemeasurable hW_meas).aestronglyMeasurable
  have hfWi_asm : ∀ i : Fin n, AEStronglyMeasurable (fun ω ↦ f (W_i i ω)) P := fun i ↦
    (hf1.continuous.measurable.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
  have hdfW_asm : AEStronglyMeasurable (fun ω ↦ deriv f (W ω)) P :=
    (hf2.continuous.measurable.comp_aemeasurable hW_meas).aestronglyMeasurable
  have hdfWi_asm : ∀ i : Fin n, AEStronglyMeasurable (fun ω ↦ deriv f (W_i i ω)) P :=
    fun i ↦ (hf2.continuous.measurable.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
  have hdfW_int : Integrable (fun ω ↦ deriv f (W ω)) P :=
    Integrable.of_bound hdfW_asm (Real.sqrt (2 / Real.pi))
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hf1_le (W ω))
  have hdfWi_int : ∀ i : Fin n, Integrable (fun ω ↦ deriv f (W_i i ω)) P := fun i ↦
    Integrable.of_bound (hdfWi_asm i) (Real.sqrt (2 / Real.pi))
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hf1_le (W_i i ω))
  have hind_Wi : ∀ i : Fin n, IndepFun (X i) (W_i i) P := fun i ↦ by
    have hsum := (h_indep.indepFun_finsetSum_of_notMem₀ hX_meas
      (Finset.notMem_erase i Finset.univ)).symm
    have hc := hsum.comp measurable_id (measurable_id.div_const (Real.sqrt n))
    have heq : ((fun x : ℝ ↦ id x / Real.sqrt n) ∘
        ∑ j ∈ Finset.univ.erase i, X j) = W_i i := by
      ext ω
      simp [W_i, Finset.sum_apply]
    simpa only [Function.id_comp, heq] using hc
  have hXfWi_zero : ∀ i : Fin n, ∫ ω, X i ω * f (W_i i ω) ∂P = 0 := fun i ↦ by
    have hind_f : IndepFun (X i) (f ∘ W_i i) P :=
      (hind_Wi i).comp measurable_id hf1.continuous.measurable
    change ∫ ω, X i ω * (f ∘ W_i i) ω ∂P = 0
    rw [hind_f.integral_fun_mul_eq_mul_integral (hX_meas i).aestronglyMeasurable (hfWi_asm i),
      hX0 i, zero_mul]
  have hX2dfWi : ∀ i : Fin n,
      ∫ ω, X i ω ^ 2 * deriv f (W_i i ω) ∂P = ∫ ω, deriv f (W_i i ω) ∂P := fun i ↦ by
    have hind_sq : IndepFun (fun ω ↦ X i ω ^ 2) (deriv f ∘ W_i i) P :=
      (hind_Wi i).comp (measurable_id.pow_const 2) hf2.continuous.measurable
    change ∫ ω, (fun ω ↦ X i ω ^ 2) ω * (deriv f ∘ W_i i) ω ∂P = _
    rw [hind_sq.integral_fun_mul_eq_mul_integral ((hX_meas i).pow_const 2).aestronglyMeasurable
      (hdfWi_asm i), hX2 i, one_mul]
    rfl
  let R : Fin n → Ω → ℝ := fun i ω ↦
    X i ω * (f (W ω) - f (W_i i ω) - (X i ω / Real.sqrt n) * deriv f (W_i i ω))
  have hR_int : ∀ i : Fin n, Integrable (R i) P := fun i ↦ by
    have heq : R i = fun ω ↦ X i ω * f (W ω) - X i ω * f (W_i i ω) -
        (X i ω ^ 2 / Real.sqrt n) * deriv f (W_i i ω) := by
      ext ω
      dsimp only [R]
      ring
    rw [heq]
    exact ((integrable_mul_of_bound (hX1 i) hfW_asm (fun ω ↦ hf0 (W ω))).sub
      (integrable_mul_of_bound (hX1 i) (hfWi_asm i) (fun ω ↦ hf0 (W_i i ω)))).sub
      (integrable_mul_of_bound ((hX_sq i).div_const _) (hdfWi_asm i) (fun ω ↦ hf1_le (W_i i ω)))
  have hWfW_eq : ∫ ω, W ω * f (W ω) ∂P =
      (1 / Real.sqrt n) * (∑ i : Fin n, ∫ ω, R i ω ∂P) +
        (1 / (n : ℝ)) * ∑ i : Fin n, ∫ ω, deriv f (W_i i ω) ∂P := by
    have hpt : (fun ω ↦ W ω * f (W ω)) = fun ω ↦
        (1 / Real.sqrt n) * ∑ i : Fin n, X i ω * f (W ω) := by
      ext ω
      have h1 : W ω * f (W ω) = (1 / Real.sqrt n) * ((∑ i : Fin n, X i ω) * f (W ω)) := by
        change ((∑ i : Fin n, X i ω) / Real.sqrt n) * f (W ω) = _
        ring
      rw [h1, Finset.sum_mul]
    rw [hpt, integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦
      integrable_mul_of_bound (hX1 i) hfW_asm fun ω ↦ hf0 (W ω)]
    have hi_split : ∀ i : Fin n, ∫ ω, X i ω * f (W ω) ∂P =
        (∫ ω, R i ω ∂P) + (1 / Real.sqrt n) * ∫ ω, deriv f (W_i i ω) ∂P := fun i ↦ by
      have hfn : (fun ω ↦ X i ω * f (W ω)) = fun ω ↦
          (R i ω + X i ω * f (W_i i ω)) +
            (1 / Real.sqrt n) * (X i ω ^ 2 * deriv f (W_i i ω)) := by
        ext ω
        dsimp only [R]
        ring
      rw [hfn, integral_add
        ((hR_int i).fun_add
          (integrable_mul_of_bound (hX1 i) (hfWi_asm i) fun ω ↦ hf0 (W_i i ω)))
        ((integrable_mul_of_bound (hX_sq i) (hdfWi_asm i)
          fun ω ↦ hf1_le (W_i i ω)).const_mul _),
        integral_add (hR_int i)
          (integrable_mul_of_bound (hX1 i) (hfWi_asm i) fun ω ↦ hf0 (W_i i ω)),
        hXfWi_zero i, add_zero, integral_const_mul, hX2dfWi i]
    simp_rw [hi_split]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, ← mul_assoc]
    have hsq_inv : (1 / Real.sqrt n) * (1 / Real.sqrt n) = 1 / (n : ℝ) := by
      rw [one_div_mul_one_div, Real.mul_self_sqrt hn_pos.le]
    rw [hsq_inv]
  have hdfW_avg : ∫ ω, deriv f (W ω) ∂P =
      (1 / (n : ℝ)) * ∑ _i : Fin n, ∫ ω, deriv f (W ω) ∂P := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      one_div_mul_cancel hn_pos.ne', one_mul]
  have hop_eq : ∫ ω, normalSteinOp f (W ω) ∂P =
      (1 / (n : ℝ)) * (∑ i : Fin n, ∫ ω, (deriv f (W ω) - deriv f (W_i i ω)) ∂P) -
        (1 / Real.sqrt n) * ∑ i : Fin n, ∫ ω, R i ω ∂P := by
    have hWfW_int : Integrable (fun ω ↦ W ω * f (W ω)) P := by
      have hpt : (fun ω ↦ W ω * f (W ω)) = fun ω ↦
          (1 / Real.sqrt n) * ∑ i : Fin n, X i ω * f (W ω) := by
        ext ω
        have h1 : W ω * f (W ω) = (1 / Real.sqrt n) * ((∑ i : Fin n, X i ω) * f (W ω)) := by
          change ((∑ i : Fin n, X i ω) / Real.sqrt n) * f (W ω) = _
          ring
        rw [h1, Finset.sum_mul]
      rw [hpt]
      exact (integrable_finsetSum Finset.univ fun i _ ↦
        integrable_mul_of_bound (hX1 i) hfW_asm fun ω ↦ hf0 (W ω)).const_mul _
    unfold normalSteinOp
    rw [integral_sub hdfW_int hWfW_int, hWfW_eq, hdfW_avg]
    have hsum_sub : (∑ _i : Fin n, ∫ ω, deriv f (W ω) ∂P) -
        (∑ i : Fin n, ∫ ω, deriv f (W_i i ω) ∂P) =
        ∑ i : Fin n, ∫ ω, (deriv f (W ω) - deriv f (W_i i ω)) ∂P := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ (integral_sub hdfW_int (hdfWi_int i)).symm
    rw [← hsum_sub]
    ring
  have h1_le_3 : ∀ i : Fin n, ∫ ω, |X i ω| ∂P ≤ ∫ ω, |X i ω| ^ 3 ∂P := fun i ↦ by
    have hpt : ∀ ω : Ω, |X i ω| ≤ |X i ω| ^ 3 - X i ω ^ 2 + 1 := fun ω ↦ by
      have hfac : (|X i ω| ^ 3 - X i ω ^ 2 + 1) - |X i ω| =
          (|X i ω| - 1) ^ 2 * (|X i ω| + 1) := by
        have hsq : X i ω ^ 2 = |X i ω| ^ 2 := (sq_abs (X i ω)).symm
        rw [hsq]
        ring
      have hnn : 0 ≤ (|X i ω| - 1) ^ 2 * (|X i ω| + 1) :=
        mul_nonneg (sq_nonneg _) (by positivity)
      linarith
    have hsub_int : Integrable (fun ω ↦ |X i ω| ^ 3 - X i ω ^ 2) P :=
      (hX_cube i).sub (hX_sq i)
    have hdom : Integrable (fun ω ↦ |X i ω| ^ 3 - X i ω ^ 2 + 1) P :=
      hsub_int.add (integrable_const 1)
    have hm := integral_mono (hX1 i).abs hdom hpt
    rw [integral_add hsub_int (integrable_const 1),
      integral_sub (hX_cube i) (hX_sq i), hX2 i, integral_const, probReal_univ, one_smul] at hm
    linarith
  have hterm1 : ∀ i : Fin n,
      |∫ ω, (deriv f (W ω) - deriv f (W_i i ω)) ∂P| ≤
        (2 / Real.sqrt n) * ∫ ω, |X i ω| ^ 3 ∂P := fun i ↦ by
    have hpt : ∀ ω : Ω, |deriv f (W ω) - deriv f (W_i i ω)| ≤
        (2 / Real.sqrt n) * |X i ω| := fun ω ↦ by
      have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le (C := 2) (f := deriv f)
        (fun x _ ↦ hf2 x)
        (fun x _ ↦ by simpa only [Real.norm_eq_abs] using hf2_le x)
        (mem_univ (W_i i ω)) (mem_univ (W ω))
      rw [Real.norm_eq_abs, Real.norm_eq_abs, h_diff i ω, abs_div, abs_of_pos hsqrt_pos] at hmvt
      exact hmvt.trans_eq (by ring)
    have hm := abs_integral_le_integral_abs.trans
      (integral_mono (hdfW_int.sub (hdfWi_int i)).abs ((hX1 i).abs.const_mul _) hpt)
    rw [integral_const_mul] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (h1_le_3 i) (by positivity))
  have hterm2 : ∀ i : Fin n,
      |∫ ω, R i ω ∂P| ≤ (1 / (n : ℝ)) * ∫ ω, |X i ω| ^ 3 ∂P := fun i ↦ by
    have hpt : ∀ ω : Ω, |R i ω| ≤ (1 / (n : ℝ)) * |X i ω| ^ 3 := fun ω ↦ by
      have htay := abs_sub_deriv_mul_le_half_sq hf1 hf2 hf2_le (W_i i ω) (W ω)
      have heq_rem : |f (W ω) - f (W_i i ω) - (X i ω / Real.sqrt n) * deriv f (W_i i ω)| =
          |f (W_i i ω) - f (W ω) - (W_i i ω - W ω) * deriv f (W_i i ω)| := by
        have hsub : f (W ω) - f (W_i i ω) - (X i ω / Real.sqrt n) * deriv f (W_i i ω) =
            -(f (W_i i ω) - f (W ω) - (W_i i ω - W ω) * deriv f (W_i i ω)) := by
          have hd := h_diff i ω
          have hd' : W_i i ω - W ω = -(X i ω / Real.sqrt n) := by linarith
          rw [hd']
          ring
        rw [hsub, abs_neg]
      have hsq_diff : (W_i i ω - W ω) ^ 2 = |X i ω| ^ 2 / (n : ℝ) := by
        have hd := h_diff i ω
        have hd' : W_i i ω - W ω = -(X i ω / Real.sqrt n) := by linarith
        rw [hd', neg_sq, div_pow, Real.sq_sqrt hn_pos.le, sq_abs]
      dsimp only [R]
      rw [abs_mul, heq_rem]
      calc
        |X i ω| * |f (W_i i ω) - f (W ω) - (W_i i ω - W ω) * deriv f (W_i i ω)|
          ≤ |X i ω| * ((2 / 2) * (W_i i ω - W ω) ^ 2) :=
            mul_le_mul_of_nonneg_left htay (abs_nonneg _)
        _ = (1 / (n : ℝ)) * |X i ω| ^ 3 := by
            rw [hsq_diff]
            ring
    have hm := abs_integral_le_integral_abs.trans
      (integral_mono (hR_int i).abs ((hX_cube i).const_mul _) hpt)
    rwa [integral_const_mul] at hm
  rw [hop_eq]
  have hsum1 : |∑ i : Fin n, ∫ ω, (deriv f (W ω) - deriv f (W_i i ω)) ∂P| ≤
      (2 / Real.sqrt n) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hterm1 i
  have hsum2 : |∑ i : Fin n, ∫ ω, R i ω ∂P| ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ hterm2 i
  have h1 :
      |(1 / (n : ℝ)) * (∑ i : Fin n, ∫ ω, (deriv f (W ω) - deriv f (W_i i ω)) ∂P)| ≤
        (2 / ((n : ℝ) * Real.sqrt n)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hn_pos)]
    exact (mul_le_mul_of_nonneg_left hsum1 (by positivity)).trans_eq (by ring)
  have h2 : |(1 / Real.sqrt n) * ∑ i : Fin n, ∫ ω, R i ω ∂P| ≤
      (1 / ((n : ℝ) * Real.sqrt n)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hsqrt_pos)]
    exact (mul_le_mul_of_nonneg_left hsum2 (by positivity)).trans_eq (by ring)
  rw [rpow_three_halves_eq_mul_sqrt hn_pos]
  calc
    |(1 / (n : ℝ)) * (∑ i : Fin n, ∫ ω, (deriv f (W ω) - deriv f (W_i i ω)) ∂P) -
        (1 / Real.sqrt n) * ∑ i : Fin n, ∫ ω, R i ω ∂P|
      ≤ |(1 / (n : ℝ)) * (∑ i : Fin n, ∫ ω, (deriv f (W ω) - deriv f (W_i i ω)) ∂P)| +
          |(1 / Real.sqrt n) * ∑ i : Fin n, ∫ ω, R i ω ∂P| := abs_sub _ _
    _ ≤ (2 / ((n : ℝ) * Real.sqrt n)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          (1 / ((n : ℝ) * Real.sqrt n)) *
            (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) := add_le_add h1 h2
    _ = 3 / ((n : ℝ) * Real.sqrt n) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by ring

end SteinMethod
