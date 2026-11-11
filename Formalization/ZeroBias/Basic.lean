/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.SteinLemma
import Formalization.Normal.WassersteinBound
import Formalization.ZeroBias.Density
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Zero-Bias Transform: Sanity Witnesses, Scaling, Wasserstein Bound & Fixed Points

Develops the remaining general results of Section 3.5 of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:1437-1523`), building on
`Formalization.ZeroBias.Density`:

* `isZeroBias_stdNormal` and `zeroBiasDensity_stdNormal`: non-vacuity sanity witnesses on
  `stdNormalLaw`.
* `IsZeroBias.const_mul` (**Proposition 3.20**, existence reading `Prop3_20`,
  `SteinIntro.tex:1519-1521`), `zeroBias_const_mul_restricted` (**Proposition 3.20, restricted**
  law-identity reading `Prop3_20_restricted`; `ISSUE-3.20`), and `not_Prop3_20_printed`.
* `zeroBias_wassersteinDist_le` (**Theorem 3.18**, `\label{thm81}`, `SteinIntro.tex:1454-1461`).
* `isZeroBias_self_iff_normalLaw` (`Sec3_5_zeroBias_fixedPoint`, `SteinIntro.tex:1450-1451`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Non-Vacuity Witnesses -/

/-- Sanity witness for `IsZeroBias` (Definition 3.10, `SteinIntro.tex:1442-1449`; `D9`):
the standard normal distribution `stdNormalLaw` has the zero-bias distribution with respect to
itself. -/
theorem isZeroBias_stdNormal : IsZeroBias stdNormalLaw id stdNormalLaw id := by
  refine ⟨memLp_id_gaussianReal 2, ?_, aemeasurable_id, ?_⟩
  · simp
  · intro f hf _ hf'
    have hvar : ProbabilityTheory.variance id stdNormalLaw = 1 := by
      simp [stdNormalLaw]
    rw [hvar, one_mul]
    exact (integrable_mul_and_integral_eq_deriv_stdNormal hf hf').2

/-- Sanity witness for `zeroBiasDensity` (Proposition 3.19(2) `\label{i82}`, eq. `\label{82}`,
`SteinIntro.tex:1479-1484`): the zero-bias density of `stdNormalLaw` equals `stdNormalPDF`. -/
theorem zeroBiasDensity_stdNormal (w : ℝ) :
    zeroBiasDensity stdNormalLaw id w = stdNormalPDF w := by
  have hvar : ProbabilityTheory.variance id stdNormalLaw = 1 := by simp [stdNormalLaw]
  have hint_id : Integrable (fun x : ℝ ↦ x * stdNormalPDF x) volume := by
    have hid : Integrable id stdNormalLaw :=
      memLp_one_iff_integrable.mp (memLp_id_gaussianReal 1)
    exact (integrable_stdNormalLaw_iff.mp hid).congr (ae_of_all _ fun x ↦ mul_comm _ _)
  have htend : Tendsto (fun x : ℝ ↦ -stdNormalPDF x) atTop (𝓝 0) := by
    have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have hsq : Tendsto (fun x : ℝ ↦ -(x ^ 2 / 2)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp
          ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by norm_num))
      exact hsq.congr fun x ↦ by ring
    have hpdf : Tendsto stdNormalPDF atTop (𝓝 0) := by
      have hfn : stdNormalPDF = fun x ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) :=
        funext stdNormalPDF_eq
      rw [hfn]
      simpa using hexp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
    simpa using hpdf.neg
  have hderiv : ∀ x ∈ Ici w, HasDerivAt (fun u ↦ -stdNormalPDF u) (x * stdNormalPDF x) x :=
    fun x _ ↦ by convert (hasDerivAt_stdNormalPDF x).neg using 1; ring
  have hIoi : ∫ x in Ioi w, x * stdNormalPDF x = stdNormalPDF w := by
    simpa using integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_id.integrableOn htend
  unfold zeroBiasDensity
  rw [hvar, inv_one, one_mul]
  dsimp only [id_eq]
  have heq : ∫ x, x * (Ioi w).indicator 1 x ∂stdNormalLaw = ∫ x in Ioi w, x * stdNormalPDF x := by
    change stdNormalExpect (fun x ↦ x * (Ioi w).indicator 1 x) = _
    rw [stdNormalExpect_eq_integral_mul_pdf, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : x ∈ Ioi w <;> simp [hx, mul_comm]
  rw [heq, hIoi]

/-! ### Section 2: Proposition 3.20 (`Prop3_20`, `Prop3_20_restricted`, and Refutation) -/

private lemma locallyAC_comp_mul_left {f : ℝ → ℝ}
    (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) {a : ℝ} (ha : a ≠ 0) (u v : ℝ) :
    AbsolutelyContinuousOnInterval (fun x ↦ f (a * x)) u v := by
  have hint : IntervalIntegrable (fun s ↦ a * deriv f (a * s)) volume u v := by
    have hdf : IntervalIntegrable (deriv f) volume (a * u) (a * v) :=
      (hf (a * u) (a * v)).intervalIntegrable_deriv
    have h1 := hdf.comp_mul_left.const_mul a
    rwa [show a * u / a = u by field_simp, show a * v / a = v by field_simp] at h1
  have heq : (fun x ↦ f (a * x)) =
      fun x ↦ f (a * u) + ∫ s in u..x, a * deriv f (a * s) := by
    ext x
    have hftc := (hf (a * u) (a * x)).integral_deriv_eq_sub
    have hchg := intervalIntegral.integral_comp_mul_left (fun s ↦ deriv f s) ha (a := u) (b := x)
    have hsmul : ∫ s in u..x, a * deriv f (a * s) = a * ∫ s in u..x, deriv f (a * s) :=
      intervalIntegral.integral_const_mul a _
    rw [hsmul, hchg, smul_eq_mul, hftc, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    ring
  rw [heq]
  exact ((LipschitzWith.const (f (a * u))).lipschitzOnWith.absolutelyContinuousOnInterval).add
    (hint.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc)

private lemma deriv_comp_mul_left_eq (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    deriv (fun t ↦ f (a * t)) x = a * deriv f (a * x) := by
  by_cases hdiff : DifferentiableAt ℝ f (a * x)
  · have hd : HasDerivAt (fun t ↦ f (a * t)) (deriv f (a * x) * a) x :=
      hdiff.hasDerivAt.comp x (by simpa using (hasDerivAt_id' x).const_mul a)
    rw [hd.deriv, mul_comm]
  · have hnd : ¬ DifferentiableAt ℝ (fun t ↦ f (a * t)) x := by
      intro hdg
      refine hdiff ?_
      let g : ℝ → ℝ := fun t ↦ f (a * t)
      have hdg' : DifferentiableAt ℝ g (a⁻¹ * (a * x)) := by
        simpa [g, inv_mul_cancel_left₀ ha] using hdg
      have hd_inv : DifferentiableAt ℝ (g ∘ fun y ↦ a⁻¹ * y) (a * x) :=
        DifferentiableAt.comp (g := g) (f := fun y ↦ a⁻¹ * y) (a * x) hdg'
          (differentiableAt_id.const_mul a⁻¹)
      refine hd_inv.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
      dsimp only [Function.comp_apply, g]
      rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hdiff, mul_zero]

/-- **Proposition 3.20** (existence reading `Prop3_20`, `SteinIntro.tex:1519-1521`): if `Wz` has
the zero-bias distribution of `W`, then for every `a : ℝ` (with no positivity condition on
`Var(W)` or `a`), `a * Wz` has the zero-bias distribution of `a * W`. -/
theorem IsZeroBias.const_mul
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : Ω → ℝ} {Wz : Ω' → ℝ}
    (hZB : IsZeroBias P W P' Wz) (a : ℝ) :
    IsZeroBias P (fun ω ↦ a * W ω) P' (fun ω' ↦ a * Wz ω') := by
  rcases hZB with ⟨hW_L2, hW_mean, hWz_meas, hZB_eq⟩
  refine ⟨hW_L2.const_mul a, ?_, hWz_meas.const_mul a, ?_⟩
  · rw [integral_const_mul, hW_mean, mul_zero]
  · intro f hf hIntW hIntWz
    by_cases ha : a = 0
    · subst ha
      have h0 : (fun ω : Ω ↦ (0 : ℝ) * W ω) = 0 := by ext; simp
      rw [h0, ProbabilityTheory.variance_zero]
      simp
    · let g : ℝ → ℝ := fun x ↦ f (a * x)
      have hg_ac : ∀ u v : ℝ, AbsolutelyContinuousOnInterval g u v :=
        locallyAC_comp_mul_left hf ha
      have hg_deriv : ∀ x : ℝ, deriv g x = a * deriv f (a * x) := deriv_comp_mul_left_eq f ha
      have hWg_int : Integrable (fun ω ↦ W ω * g (W ω)) P := by
        have heq : (fun ω ↦ W ω * g (W ω)) = fun ω ↦ a⁻¹ * ((a * W ω) * f (a * W ω)) := by
          ext ω; dsimp [g]; field_simp [ha]
        rw [heq]
        exact hIntW.const_mul a⁻¹
      have hWzg_int : Integrable (fun ω' ↦ deriv g (Wz ω')) P' := by
        simp_rw [hg_deriv]
        exact hIntWz.const_mul a
      have hstep := hZB_eq g hg_ac hWg_int hWzg_int
      simp_rw [hg_deriv] at hstep
      rw [integral_const_mul] at hstep
      have hLHS : ∫ ω, (a * W ω) * f (a * W ω) ∂P = a * ∫ ω, W ω * g (W ω) ∂P := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
        dsimp [g]; ring
      rw [hLHS, hstep, ProbabilityTheory.variance_const_mul a W P]
      ring

/-- **Proposition 3.20, restricted** (law-identity reading `Prop3_20_restricted`,
`SteinIntro.tex:1519-1521`; `ISSUE-3.20` as the $\operatorname{Var}(aW) = a^2 \sigma^2 = 0$
instance of `ISSUE-3.19`): when $\operatorname{Var}(W) > 0$ and $a \ne 0$, every zero-bias
realization $Y$ of $a W$ has the same law as $a W^z$. -/
theorem zeroBias_const_mul_restricted
    {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    {W : Ω → ℝ} {Wz : Ω' → ℝ} {Y : Ω'' → ℝ} {a : ℝ}
    (hVar : 0 < ProbabilityTheory.variance W P) (ha : a ≠ 0)
    (hZB : IsZeroBias P W P' Wz) :
    IsZeroBias P (fun ω ↦ a * W ω) P' (fun ω' ↦ a * Wz ω') ∧
      (IsZeroBias P (fun ω ↦ a * W ω) P'' Y →
        P''.map Y = P'.map (fun ω' ↦ a * Wz ω')) := by
  have haZB : IsZeroBias P (fun ω ↦ a * W ω) P' (fun ω' ↦ a * Wz ω') := hZB.const_mul a
  refine ⟨haZB, fun hY ↦ ?_⟩
  have haVar : 0 < ProbabilityTheory.variance (fun ω ↦ a * W ω) P := by
    rw [ProbabilityTheory.variance_const_mul]
    exact mul_pos (sq_pos_of_ne_zero ha) hVar
  have hchar := (zeroBias_law_characterization (Ω' := Ω') P haZB.1 haZB.2.1 haVar).2.1 P' haZB
  have hcharY := (zeroBias_law_characterization (Ω' := Ω'') P haZB.1 haZB.2.1 haVar).2.1 P'' hY
  exact hcharY.trans hchar.symm

/-- Machine-checked refutation of the unrestricted law-identity reading of Proposition 3.20 at
$a = 0$ (`ISSUE-3.20`, `SteinIntro.tex:1519-1521`): even when $\operatorname{Var}(W) = 1 > 0$
($W \sim \mathcal{N}(0, 1)$), at $a = 0$ we have $\operatorname{Var}(a W) = 0$ (`ISSUE-3.19`), so
$Y \equiv 1$ satisfies `IsZeroBias` with respect to $0 \cdot W$ while $0 \cdot W^z \equiv 0$. -/
theorem not_Prop3_20_printed :
    ¬ (∀ {Ω Ω' Ω'' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        {W : Ω → ℝ} {Wz : Ω' → ℝ} {Y : Ω'' → ℝ} {a : ℝ},
        0 < ProbabilityTheory.variance W P →
        IsZeroBias P W P' Wz →
        IsZeroBias P (fun ω ↦ a * W ω) P'' Y →
        P''.map Y = P'.map (fun ω' ↦ a * Wz ω')) := by
  intro hall
  have hvar : 0 < ProbabilityTheory.variance id stdNormalLaw := by
    simp [stdNormalLaw]
  have hY : IsZeroBias stdNormalLaw (fun ω : ℝ ↦ (0 : ℝ) * id ω) (Measure.dirac 1) id := by
    have h0 : (fun ω : ℝ ↦ (0 : ℝ) * id ω) = fun _ ↦ (0 : ℝ) := by ext; simp
    rw [h0]
    refine ⟨memLp_const (0 : ℝ), by simp, aemeasurable_id, fun f _ _ _ ↦ ?_⟩
    rw [show (fun _ : ℝ ↦ (0 : ℝ)) = (0 : ℝ → ℝ) from rfl, ProbabilityTheory.variance_zero]
    simp
  have heq := hall stdNormalLaw stdNormalLaw (Measure.dirac (1 : ℝ)) hvar isZeroBias_stdNormal hY
  have hLHS : (Measure.dirac (1 : ℝ)).map id = Measure.dirac 1 := Measure.map_id
  have hRHS : stdNormalLaw.map (fun ω' : ℝ ↦ (0 : ℝ) * id ω') = Measure.dirac 0 := by simp
  rw [hLHS, hRHS] at heq
  have h1 : (Measure.dirac (1 : ℝ)) {(1 : ℝ)} = (Measure.dirac (0 : ℝ)) {(1 : ℝ)} :=
    congrArg (fun μ : Measure ℝ ↦ μ {(1 : ℝ)}) heq
  simp at h1

/-! ### Section 3: Theorem 3.18 (`Thm3_18`, Wasserstein Bound via Zero-Bias Coupling) -/

/-- **Theorem 3.18** (`\label{thm81}`, `SteinIntro.tex:1454-1461`): for mean-zero unit-variance `W`
coupled on the same probability space with a zero-bias version `Wz`, and `Z ~ N(0, 1)`,
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le 2\,\mathbb{E}|W^z - W|$ (with `lintegral` on the
right-hand side per the junk-zero rule `D1`). -/
theorem zeroBias_wassersteinDist_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ}
    (hVar : ProbabilityTheory.variance W P = 1)
    (hZB : IsZeroBias P W P Wz)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    wassersteinDist (P.map W) (P'.map Z) ≤
      2 * ∫⁻ ω, ENNReal.ofReal |Wz ω - W ω| ∂P := by
  rcases hZB with ⟨hW_L2, _, hWz_meas, hZB_eq⟩
  have hW_aem : AEMeasurable W P := hW_L2.aemeasurable
  have hW_int : Integrable W P := hW_L2.integrable one_le_two
  refine (wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P' hW_aem hZ hZ_law).trans ?_
  refine iSup₂_le fun f hf ↦ ?_
  rcases hf with ⟨hf_diff, hdf_diff, hf_bdd, hdf_bdd, hddf_bdd⟩
  have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b := fun a b ↦ by
    have hcd : ContDiff ℝ 1 f := contDiff_one_iff_deriv.mpr ⟨hf_diff, hdf_diff.continuous⟩
    exact hcd.contDiffOn.absolutelyContinuousOnInterval
  have hWf_int : Integrable (fun ω ↦ W ω * f (W ω)) P := by
    refine (hW_int.norm.mul_const 2).mono'
      (hW_L2.aestronglyMeasurable.mul
        (hf_diff.continuous.measurable.comp_aemeasurable hW_aem).aestronglyMeasurable)
      (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg (W ω))
  have hdfW_int : Integrable (fun ω ↦ deriv f (W ω)) P :=
    Integrable.of_bound
      (hdf_diff.continuous.measurable.comp_aemeasurable hW_aem).aestronglyMeasurable
      (Real.sqrt (2 / Real.pi))
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd (W ω))
  have hdfWz_int : Integrable (fun ω ↦ deriv f (Wz ω)) P :=
    Integrable.of_bound
      (hdf_diff.continuous.measurable.comp_aemeasurable hWz_meas).aestronglyMeasurable
      (Real.sqrt (2 / Real.pi))
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd (Wz ω))
  have hstein : ∫ ω, normalSteinOp f (W ω) ∂P = ∫ ω, (deriv f (W ω) - deriv f (Wz ω)) ∂P := by
    unfold normalSteinOp
    rw [integral_sub hdfW_int hWf_int, hZB_eq f hf_ac hWf_int hdfWz_int, hVar, one_mul,
      integral_sub hdfW_int hdfWz_int]
  have hlip : ∀ x y : ℝ, |deriv f x - deriv f y| ≤ 2 * |y - x| := fun x y ↦ by
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
      (fun z _ ↦ hdf_diff z) (fun z _ ↦ by rw [Real.norm_eq_abs]; exact hddf_bdd z)
      convex_univ (mem_univ y) (mem_univ x)
    simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt
  have hdiff_int : Integrable (fun ω ↦ |deriv f (W ω) - deriv f (Wz ω)|) P :=
    (hdfW_int.sub hdfWz_int).abs
  calc
    ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|
      = ENNReal.ofReal |∫ ω, (deriv f (W ω) - deriv f (Wz ω)) ∂P| := by rw [hstein]
    _ ≤ ENNReal.ofReal (∫ ω, |deriv f (W ω) - deriv f (Wz ω)| ∂P) :=
        ENNReal.ofReal_le_ofReal abs_integral_le_integral_abs
    _ = ∫⁻ ω, ENNReal.ofReal |deriv f (W ω) - deriv f (Wz ω)| ∂P :=
        ofReal_integral_eq_lintegral_ofReal hdiff_int (ae_of_all _ fun _ ↦ abs_nonneg _)
    _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) * ENNReal.ofReal |Wz ω - W ω| ∂P := by
        refine lintegral_mono fun ω ↦ ?_
        calc
          ENNReal.ofReal |deriv f (W ω) - deriv f (Wz ω)|
            ≤ ENNReal.ofReal (2 * |Wz ω - W ω|) := ENNReal.ofReal_le_ofReal (hlip (W ω) (Wz ω))
          _ = (2 : ℝ≥0∞) * ENNReal.ofReal |Wz ω - W ω| := by
              rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    _ = 2 * ∫⁻ ω, ENNReal.ofReal |Wz ω - W ω| ∂P :=
        lintegral_const_mul'' 2
          ((continuous_abs.measurable.comp_aemeasurable (hWz_meas.sub hW_aem)).ennreal_ofReal)

/-! ### Section 4: Fixed-Point Characterization (`Sec3_5_zeroBias_fixedPoint`) -/

/-- **Section 3.5 Fixed-Point Characterization** (`SteinIntro.tex:1450-1451`): an a.e. measurable
random variable `W` satisfies `IsZeroBias P W P W` if and only if the law of `W` is a centered
normal distribution `normalLaw 0 v` (`gaussianReal 0 v`, for some `v : ℝ≥0`). -/
theorem isZeroBias_self_iff_normalLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (hW : AEMeasurable W P) :
    IsZeroBias P W P W ↔ ∃ v : ℝ≥0, P.map W = normalLaw 0 v := by
  constructor
  · intro hZB
    have hW2 : MemLp W 2 P := hZB.1
    have hMean : ∫ ω, W ω ∂P = 0 := hZB.2.1
    have hv_nn : 0 ≤ ProbabilityTheory.variance W P := ProbabilityTheory.variance_nonneg W P
    rcases hv_nn.eq_or_lt with hv0 | hv_pos
    · refine ⟨0, ?_⟩
      rw [normalLaw, gaussianReal_zero_var]
      have hW0 : W =ᵐ[P] fun _ ↦ (0 : ℝ) := by
        filter_upwards [ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hW2 hv0.symm] with ω hω
        simpa [hMean] using hω
      calc
        P.map W = P.map (fun _ : Ω ↦ (0 : ℝ)) := Measure.map_congr hW0
        _ = Measure.dirac 0 := by simp
    · set σ : ℝ := Real.sqrt (ProbabilityTheory.variance W P)
      have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hv_pos
      let W₁ : Ω → ℝ := fun ω ↦ σ⁻¹ * W ω
      have hW₁_aem : AEMeasurable W₁ P := hW.const_mul σ⁻¹
      have hZB₁ : IsZeroBias P W₁ P W₁ := hZB.const_mul σ⁻¹
      have hVar₁ : ProbabilityTheory.variance W₁ P = 1 := by
        dsimp [W₁]
        rw [ProbabilityTheory.variance_const_mul, inv_pow, Real.sq_sqrt hv_pos.le,
          inv_mul_cancel₀ hv_pos.ne']
      have hW₁_int : Integrable W₁ P := hZB₁.1.integrable one_le_two
      have hmap₁ : P.map W₁ = stdNormalLaw := by
        refine Measure.eq_of_cdf (P.map W₁) stdNormalLaw ?_
        ext x
        have heq_n : ∀ n : ℕ,
            ∫ t, zbRamp x n t ∂(P.map W₁) = ∫ z, zbRamp x n z ∂stdNormalLaw := fun n ↦ by
          let h : ℝ → ℝ := zbRamp x n
          have hh_cont : Continuous h := continuous_zbRamp x n
          have hh_meas : Measurable h := hh_cont.measurable
          have hh_int : Integrable h stdNormalLaw :=
            Integrable.of_bound hh_cont.aestronglyMeasurable 1
              (ae_of_all _ fun t ↦ by rw [Real.norm_eq_abs]; exact abs_zbRamp_le_one x n t)
          let M : ℝ := 1 + |stdNormalExpect h|
          have hM : ∀ t : ℝ, |h t - stdNormalExpect h| ≤ M := fun t ↦ by
            dsimp [M]; linarith [abs_sub (h t) (stdNormalExpect h), abs_zbRamp_le_one x n t]
          let f : ℝ → ℝ := normalSteinSol h
          have hf_deriv_eq : deriv f = fun w ↦ w * f w + h w - stdNormalExpect h :=
            funext fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hh_int hh_cont w).deriv
          have hf_diff : Differentiable ℝ f :=
            fun w ↦ (hasDerivAt_normalSteinSol_of_continuous hh_int hh_cont w).differentiableAt
          have hf_cont_df : Continuous (deriv f) := by
            rw [hf_deriv_eq]
            exact ((continuous_id.mul hf_diff.continuous).add hh_cont).sub continuous_const
          have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b := fun a b ↦
            (contDiff_one_iff_deriv.mpr ⟨hf_diff, hf_cont_df⟩).contDiffOn
              |>.absolutelyContinuousOnInterval
          have hWf_int : Integrable (fun ω ↦ W₁ ω * f (W₁ ω)) P := by
            refine (hW₁_int.norm.mul_const (Real.sqrt (Real.pi / 2) * M)).mono'
              (hZB₁.1.aestronglyMeasurable.mul
                (hf_diff.continuous.measurable.comp_aemeasurable hW₁_aem).aestronglyMeasurable)
              (ae_of_all _ fun ω ↦ ?_)
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left
              (abs_normalSteinSol_le_of_bounded hh_meas hM (W₁ ω)) (abs_nonneg (W₁ ω))
          have hdf_int : Integrable (fun ω ↦ deriv f (W₁ ω)) P :=
            Integrable.of_bound
              (hf_cont_df.measurable.comp_aemeasurable hW₁_aem).aestronglyMeasurable
              (2 * M) (ae_of_all _ fun ω ↦ by
                rw [Real.norm_eq_abs]
                exact abs_deriv_normalSteinSol_le_of_bounded hh_meas hM (W₁ ω))
          have hzb := hZB₁.2.2.2 f hf_ac hWf_int hdf_int
          rw [hVar₁, one_mul] at hzb
          have hop : ∀ w : ℝ, deriv f w - w * f w = h w - stdNormalExpect h := fun w ↦ by
            rw [congr_fun hf_deriv_eq w]; ring
          have h0 : ∫ ω, (h (W₁ ω) - stdNormalExpect h) ∂P = 0 := by
            simp_rw [← hop]
            rw [integral_sub hdf_int hWf_int, hzb, sub_self]
          have hhW₁_int : Integrable (fun ω ↦ h (W₁ ω)) P :=
            Integrable.of_bound (hh_meas.comp_aemeasurable hW₁_aem).aestronglyMeasurable 1
              (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_zbRamp_le_one x n (W₁ ω))
          rw [integral_sub hhW₁_int (integrable_const _), integral_const, probReal_univ,
            one_smul, sub_eq_zero] at h0
          rw [integral_map hW₁_aem hh_cont.aestronglyMeasurable]
          exact h0
        have hlim1 := tendsto_integral_zbRamp (P.map W₁) x
        have hlim2 := tendsto_integral_zbRamp stdNormalLaw x
        simp_rw [heq_n] at hlim1
        exact tendsto_nhds_unique hlim1 hlim2
      refine ⟨Real.toNNReal (ProbabilityTheory.variance W P), ?_⟩
      have hid₁ : IdentDistrib W₁ id P stdNormalLaw :=
        ⟨hW₁_aem, aemeasurable_id, by rw [hmap₁, Measure.map_id]⟩
      have hidW : IdentDistrib (fun ω ↦ σ * W₁ ω) (fun z ↦ σ * z) P stdNormalLaw :=
        hid₁.comp (measurable_const_mul σ)
      have hW_eq : W = fun ω ↦ σ * W₁ ω := by
        ext ω; dsimp [W₁]; rw [← mul_assoc, mul_inv_cancel₀ hσ_pos.ne', one_mul]
      calc
        P.map W = P.map (fun ω ↦ σ * W₁ ω) := by rw [hW_eq]
        _ = stdNormalLaw.map (fun z ↦ σ * z) := hidW.map_eq
        _ = normalLaw 0 (Real.toNNReal (ProbabilityTheory.variance W P)) := by
            rw [stdNormalLaw, gaussianReal_map_const_mul, mul_zero, mul_one, normalLaw]
            congr 1
            ext
            rw [Real.coe_toNNReal _ hv_pos.le]
            simp [σ, Real.sq_sqrt hv_pos.le]
  · rintro ⟨v, hv_law⟩
    let Z_scaled : ℝ → ℝ := fun z ↦ Real.sqrt (v : ℝ) * z
    have hZ_law : stdNormalLaw.map Z_scaled = normalLaw 0 v := by
      dsimp [Z_scaled, stdNormalLaw, normalLaw]
      rw [gaussianReal_map_const_mul, mul_zero, mul_one]
      congr 1
      ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
    have hZB_scaled : IsZeroBias stdNormalLaw Z_scaled stdNormalLaw Z_scaled :=
      isZeroBias_stdNormal.const_mul (Real.sqrt (v : ℝ))
    have hid : IdentDistrib Z_scaled W stdNormalLaw P :=
      ⟨(measurable_const_mul _).aemeasurable, hW, hZ_law.trans hv_law.symm⟩
    exact hZB_scaled.congr_identDistrib hid hid

end SteinMethod
