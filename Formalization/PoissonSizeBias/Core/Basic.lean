/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Metrics.Basic
import Formalization.Poisson.SteinLemma
import Formalization.SizeBias.Coupling

/-!
# Poisson Size-Bias Coupling Core (`Formalization.PoissonSizeBias.Core.Basic`)

Core theorems opening Section 4.3 (*Size-bias Coupling*, `SteinIntro.tex:2113-2159`), imported by
Tracks G2–G4:
- **Theorem 4.10** (`\label{thm121}`, `SteinIntro.tex:2120-2127`; proof display `L2130-2133`):
  `tvDist_poisson_le_of_isSizeBias` (and `tvDist_poissonLaw_le_of_isSizeBias`,
  `tvDist_poissonLaw_le_of_isSizeBias_integrable`, `tvDist_poissonLaw_le_of_isSizeBias_nat`, plus
  the sharper `1 - e^{-r}` variant `tvDist_poissonLaw_le_one_sub_exp_of_isSizeBias`).
- **Corollary 4.11** (`\label{cor121}`, `SteinIntro.tex:2142-2147`; `ISSUE-TYPO-4.11`):
  `sizeBias_sum_of_zero_one_fin` on `Fin n` and `sizeBias_sum_of_zero_one_fintype` /
  `sizeBias_sum_of_nat_zero_one_fintype` over arbitrary finite index types `[Fintype ι]`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Support and discrete telescoping lemmas for Theorem 4.10 -/

private lemma measurable_natFloor : Measurable (Nat.floor : ℝ → ℕ) := by
  intro s _
  have hsingle : ∀ k : ℕ, MeasurableSet ((Nat.floor : ℝ → ℕ) ⁻¹' {k}) := by
    intro k
    cases k with
    | zero =>
        have hpre : (Nat.floor : ℝ → ℕ) ⁻¹' {0} = Set.Iio 1 := by
          ext x
          simp
        rw [hpre]
        exact measurableSet_Iio
    | succ m =>
        have hpre : (Nat.floor : ℝ → ℕ) ⁻¹' {m + 1} =
            Set.Ico ((m + 1 : ℕ) : ℝ) (((m + 1 : ℕ) : ℝ) + 1) := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_Ico]
          constructor
          · intro hx
            have hx_nn : 0 ≤ x := by
              by_contra hneg
              have h0 : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge hneg)
              omega
            exact (Nat.floor_eq_iff hx_nn).mp hx
          · intro hx
            have hx_nn : 0 ≤ x := (Nat.cast_nonneg (m + 1)).trans hx.1
            exact (Nat.floor_eq_iff hx_nn).mpr hx
        rw [hpre]
        exact measurableSet_Ico
  have hunion : (Nat.floor : ℝ → ℕ) ⁻¹' s = ⋃ k ∈ s, (Nat.floor : ℝ → ℕ) ⁻¹' {k} := by
    ext x
    simp
  rw [hunion]
  exact MeasurableSet.biUnion (Set.to_countable s) fun k _ ↦ hsingle k

/-- If `W : Ω → ℕ` has positive mean under `P` and `Ws` has the size-bias distribution of `W`,
then `Ws` takes values in `Set.range (Nat.cast : ℕ → ℝ)` almost everywhere, so `(⌊Ws ω'⌋₊ : ℝ) =
Ws ω'` for `P'`-a.e. `ω'` (`SteinIntro.tex:2120-2135`). -/
theorem isSizeBias_ae_natFloor_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℕ} {Ws : Ω' → ℝ}
    (hμ : 0 < ∫ ω, (W ω : ℝ) ∂P)
    (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P' Ws) :
    ∀ᵐ ω' ∂P', ((⌊Ws ω'⌋₊ : ℕ) : ℝ) = Ws ω' := by
  let S : Set ℝ := Set.range (Nat.cast : ℕ → ℝ)
  have hS_meas : MeasurableSet S := (Set.countable_range (Nat.cast : ℕ → ℝ)).measurableSet
  let g : ℝ → ℝ := Sᶜ.indicator 1
  have hg_meas : Measurable g := measurable_one.indicator hS_meas.compl
  have hWg_zero : ∀ ω : Ω, (W ω : ℝ) * g (W ω : ℝ) = 0 := fun ω ↦ by
    have hmem : (W ω : ℝ) ∈ S := ⟨W ω, rfl⟩
    simp [g, hmem]
  have hWg_int : Integrable (fun ω : Ω ↦ (W ω : ℝ) * g (W ω : ℝ)) P := by
    simp_rw [hWg_zero]
    exact integrable_zero Ω ℝ P
  have hSB_eq := hSB.2.2.2 g hg_meas hWg_int
  simp only [hWg_zero, integral_zero] at hSB_eq
  have hgWs_int : Integrable (fun ω' ↦ g (Ws ω')) P' := by
    refine (integrable_const (1 : ℝ)).mono'
      (hg_meas.comp_aemeasurable hSB.2.2.1).aestronglyMeasurable
      (Eventually.of_forall fun ω' ↦ ?_)
    by_cases h : Ws ω' ∈ Sᶜ <;> simp [g, h]
  have hgWs_nn : 0 ≤ᵐ[P'] fun ω' ↦ g (Ws ω') :=
    Eventually.of_forall fun ω' ↦ by
      by_cases h : Ws ω' ∈ Sᶜ <;> simp [g, h]
  have hIntZero : ∫ ω', g (Ws ω') ∂P' = 0 := by
    rcases mul_eq_zero.mp hSB_eq.symm with h0 | h0
    · linarith
    · exact h0
  have hae_zero : (fun ω' ↦ g (Ws ω')) =ᵐ[P'] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hgWs_nn hgWs_int).mp hIntZero
  filter_upwards [hae_zero] with ω' hω'
  have hmem : Ws ω' ∈ S := by
    by_contra hnot
    have h1 : g (Ws ω') = 1 := Set.indicator_of_mem hnot 1
    linarith [show g (Ws ω') = 0 from hω']
  rcases hmem with ⟨k, hk⟩
  rw [← hk, Nat.floor_natCast]

/-- Discrete telescoping bound (`SteinIntro.tex:2131-2134`): if `|Δf(m)| ≤ C` for every `m : ℕ`,
then `|f j - f k| ≤ C * |(j : ℝ) - (k : ℝ)|` for all `j k : ℕ`. -/
theorem abs_sub_le_mul_abs_sub_of_fwdDiff_le
    {f : ℕ → ℝ} {C : ℝ} (hf : ∀ m : ℕ, |fwdDiff 1 f m| ≤ C) (j k : ℕ) :
    |f j - f k| ≤ C * |(j : ℝ) - (k : ℝ)| := by
  have aux : ∀ a d : ℕ, |f (a + d) - f a| ≤ C * (d : ℝ) := by
    intro a d
    induction d with
    | zero => simp
    | succ d ih =>
        have hsplit : f (a + (d + 1)) - f a = (f (a + d) - f a) + fwdDiff 1 f (a + d) := by
          rw [← add_assoc]
          simp only [fwdDiff]
          ring
        rw [hsplit, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
        exact (abs_add_le _ _).trans (add_le_add ih (hf (a + d)))
  rcases le_total k j with hkj | hjk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
    have hcast : |(k + d : ℕ) - (k : ℝ)| = (d : ℝ) := by
      rw [Nat.cast_add, add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg d)]
    simpa [hcast] using aux k d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
    have hcast : |(j : ℝ) - (j + d : ℕ)| = (d : ℝ) := by
      rw [Nat.cast_add, sub_add_cancel_left, abs_neg, abs_of_nonneg (Nat.cast_nonneg d)]
    rw [abs_sub_comm]
    simpa [hcast] using aux j d

/-! ### Stein operator bound and Theorem 4.10 -/

/-- Extended-real proof display of Theorem 4.10 (`SteinIntro.tex:2129-2134`): for bounded
`f : ℕ → ℝ` with `‖Δf‖ ≤ C`, size-bias coupling rewrites `𝔼[r f(W + 1) - W f(W)]` as
`r 𝔼[f(W + 1) - f(W^s)]` and bounds its absolute value by `r C 𝔼|W + 1 - W^s|` in `ℝ≥0∞`. -/
theorem ennreal_abs_integral_poissonSteinOp_le_of_isSizeBias
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hmean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ))
    {Ws : Ω → ℝ} (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws)
    {f : ℕ → ℝ} {B C : ℝ} (hf_bdd : ∀ k : ℕ, |f k| ≤ B)
    (hf_diff : ∀ k : ℕ, |fwdDiff 1 f k| ≤ C) :
    ENNReal.ofReal |∫ ω, poissonSteinOp r f (W ω) ∂P| ≤
      ENNReal.ofReal ((r : ℝ) * C) *
        ∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| ∂P := by
  have hC_nn : 0 ≤ C := (abs_nonneg _).trans (hf_diff 0)
  have hμ : 0 < ∫ ω, (W ω : ℝ) ∂P := by
    rw [hmean]
    exact NNReal.coe_pos.mpr hr
  let g : ℝ → ℝ := fun x ↦ f ⌊x⌋₊
  have hg_meas : Measurable g := (Measurable.of_discrete (f := f)).comp measurable_natFloor
  have hWf_eq : (fun ω ↦ (W ω : ℝ) * f (W ω)) = fun ω ↦ (W ω : ℝ) * g (W ω : ℝ) := by
    ext ω
    simp [g]
  have hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P := hSB.2.1
  have hWf_int : Integrable (fun ω ↦ (W ω : ℝ) * f (W ω)) P := by
    refine (hW_int.norm.mul_const B).mono'
      (hW_int.aestronglyMeasurable.mul
        ((Measurable.of_discrete (f := f)).comp_aemeasurable hW).aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg _)
  have hWg_int : Integrable (fun ω ↦ (W ω : ℝ) * g (W ω : ℝ)) P := hWf_eq ▸ hWf_int
  have hfW1_int : Integrable (fun ω ↦ f (W ω + 1)) P := by
    have hf1_asm : AEStronglyMeasurable (fun ω ↦ f (W ω + 1)) P :=
      ((Measurable.of_discrete (f := fun k ↦ f (k + 1))).comp_aemeasurable hW).aestronglyMeasurable
    refine (integrable_const B).mono' hf1_asm (Eventually.of_forall fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs] using hf_bdd (W ω + 1)
  have hgWs_int : Integrable (fun ω ↦ g (Ws ω)) P := by
    refine (integrable_const B).mono'
      (hg_meas.comp_aemeasurable hSB.2.2.1).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs, g] using hf_bdd ⌊Ws ω⌋₊
  have hSB_eq : ∫ ω, (W ω : ℝ) * f (W ω) ∂P = (r : ℝ) * ∫ ω, g (Ws ω) ∂P := by
    rw [hWf_eq, hSB.2.2.2 g hg_meas hWg_int, hmean]
  have hOp_eq : ∫ ω, poissonSteinOp r f (W ω) ∂P =
      (r : ℝ) * ∫ ω, (f (W ω + 1) - g (Ws ω)) ∂P := by
    have hsub : (fun ω ↦ poissonSteinOp r f (W ω)) =
        fun ω ↦ (r : ℝ) * f (W ω + 1) - (W ω : ℝ) * f (W ω) := rfl
    rw [hsub, integral_sub (hfW1_int.const_mul (r : ℝ)) hWf_int,
      integral_const_mul, hSB_eq, ← mul_sub, integral_sub hfW1_int hgWs_int]
  have hdiff_int : Integrable (fun ω ↦ |f (W ω + 1) - g (Ws ω)|) P :=
    (hfW1_int.sub hgWs_int).abs
  have hae_floor := isSizeBias_ae_natFloor_eq P P hμ hSB
  have hae_bound : ∀ᵐ ω ∂P,
      ENNReal.ofReal |f (W ω + 1) - g (Ws ω)| ≤
        ENNReal.ofReal C * ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| := by
    filter_upwards [hae_floor] with ω hω
    have hstep := abs_sub_le_mul_abs_sub_of_fwdDiff_le hf_diff (W ω + 1) ⌊Ws ω⌋₊
    rw [Nat.cast_add, Nat.cast_one, hω] at hstep
    rw [← ENNReal.ofReal_mul hC_nn]
    exact ENNReal.ofReal_le_ofReal hstep
  have hWr_aem : AEMeasurable (fun ω ↦ (W ω : ℝ)) P :=
    (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp_aemeasurable hW
  have hmeas_abs : AEMeasurable (fun ω ↦ |(W ω : ℝ) + 1 - Ws ω|) P :=
    continuous_abs.measurable.comp_aemeasurable ((hWr_aem.add_const (1 : ℝ)).sub hSB.2.2.1)
  calc
    ENNReal.ofReal |∫ ω, poissonSteinOp r f (W ω) ∂P|
      = ENNReal.ofReal ((r : ℝ) * |∫ ω, (f (W ω + 1) - g (Ws ω)) ∂P|) := by
        rw [hOp_eq, abs_mul, abs_of_nonneg (NNReal.coe_nonneg r)]
    _ ≤ ENNReal.ofReal ((r : ℝ) * ∫ ω, |f (W ω + 1) - g (Ws ω)| ∂P) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg r))
        exact abs_integral_le_integral_abs
    _ = ENNReal.ofReal (r : ℝ) * ENNReal.ofReal (∫ ω, |f (W ω + 1) - g (Ws ω)| ∂P) :=
        ENNReal.ofReal_mul (NNReal.coe_nonneg r)
    _ = ENNReal.ofReal (r : ℝ) * ∫⁻ ω, ENNReal.ofReal |f (W ω + 1) - g (Ws ω)| ∂P := by
        rw [ofReal_integral_eq_lintegral_ofReal hdiff_int
          (Eventually.of_forall fun _ ↦ abs_nonneg _)]
    _ ≤ ENNReal.ofReal (r : ℝ) *
          ∫⁻ ω, ENNReal.ofReal C * ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| ∂P :=
        mul_le_mul_of_nonneg_left (lintegral_mono_ae hae_bound) zero_le
    _ = ENNReal.ofReal ((r : ℝ) * C) *
          ∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| ∂P := by
        rw [lintegral_const_mul'' _ hmeas_abs.ennreal_ofReal, ← mul_assoc,
          ENNReal.ofReal_mul (NNReal.coe_nonneg r)]

/-- Sharper `1 - e^{-r}` Poisson total-variation bound via size-bias coupling
(`SteinIntro.tex:2120-2135` combined with Lemma 4.4's `|Δf_A| ≤ (1 - e^{-r}) / r`). -/
theorem tvDist_poissonLaw_le_one_sub_exp_of_isSizeBias
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hmean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ))
    {Ws : Ω → ℝ} (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws) :
    tvDist (P.map W) (poissonLaw r) ≤
      ENNReal.ofReal (1 - Real.exp (-(r : ℝ))) *
        ∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| ∂P := by
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  rw [tvDist_eq_iSup]
  refine iSup₂_le fun A hA ↦ ?_
  rw [map_measureReal_apply_of_aemeasurable hW hA]
  change ENNReal.ofReal |P.real {ω | W ω ∈ A} - (poissonLaw r).real A| ≤ _
  rw [abs_measureReal_sub_poissonLaw_eq P hr hW A]
  have hOp := ennreal_abs_integral_poissonSteinOp_le_of_isSizeBias P hr hW hmean hSB
    (abs_poissonSteinSol_le hr A) (abs_fwdDiff_poissonSteinSol_le hr A)
  have hr_ne : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr.ne'
  have hmul : (r : ℝ) * ((1 - Real.exp (-(r : ℝ))) / (r : ℝ)) = 1 - Real.exp (-(r : ℝ)) :=
    mul_div_cancel₀ _ hr_ne
  simpa only [poissonSteinOp, hmul] using hOp

/-- **Theorem 4.10** (`\label{thm121}`, `SteinIntro.tex:2120-2127`), `poissonLaw r` form:
for `W : Ω → ℕ` with `𝔼[W] = r > 0` and size-bias coupling `Ws` on `(Ω, P)`,
`d_TV(Law(W), Po(r)) ≤ min(1, r) 𝔼|W + 1 - Ws|` (stated in `ℝ≥0∞` via `lintegral`). -/
theorem tvDist_poissonLaw_le_of_isSizeBias
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hmean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ))
    {Ws : Ω → ℝ} (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws) :
    tvDist (P.map W) (poissonLaw r) ≤
      ENNReal.ofReal (min 1 (r : ℝ)) *
        ∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| ∂P := by
  refine (tvDist_poissonLaw_le_one_sub_exp_of_isSizeBias P hr hW hmean hSB).trans ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hle := one_sub_exp_neg_div_le_min hr
  have hr_pos : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hmul := mul_le_mul_of_nonneg_left hle hr_pos.le
  rw [mul_div_cancel₀ _ hr_pos.ne'] at hmul
  have hmin : (r : ℝ) * min 1 (r : ℝ)⁻¹ = min 1 (r : ℝ) := by
    rw [mul_min_of_nonneg _ _ hr_pos.le, mul_one, mul_inv_cancel₀ hr_pos.ne', min_comm]
  rwa [hmin] at hmul

/-- **Theorem 4.10** (`\label{thm121}`, `SteinIntro.tex:2120-2127`), two-space random-variable form
matching `SteinMethod.Thm4_10`. -/
theorem tvDist_poisson_le_of_isSizeBias
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {r : ℝ≥0} {W : Ω → ℕ} {Ws : Ω → ℝ} {Z : Ω' → ℕ}
    (hr : 0 < r) (hW : AEMeasurable W P)
    (hmean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ))
    (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws)
    (_hZ : AEMeasurable Z P') (hZ_law : P'.map Z = poissonLaw r) :
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (min 1 (r : ℝ)) *
        ∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| ∂P := by
  rw [hZ_law]
  exact tvDist_poissonLaw_le_of_isSizeBias P hr hW hmean hSB

/-- **Theorem 4.10** (`\label{thm121}`, `SteinIntro.tex:2120-2127`), Bochner-integral
specialization when `Ws` is `P`-integrable (the typical case in finite indicator sums). -/
theorem tvDist_poissonLaw_le_of_isSizeBias_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hmean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ))
    {Ws : Ω → ℝ} (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws)
    (hWs_int : Integrable Ws P) :
    tvDist (P.map W) (poissonLaw r) ≤
      ENNReal.ofReal (min 1 (r : ℝ) * ∫ ω, |(W ω : ℝ) + 1 - Ws ω| ∂P) := by
  have hdiff_int : Integrable (fun ω ↦ |(W ω : ℝ) + 1 - Ws ω|) P :=
    ((hSB.2.1.add (integrable_const 1)).sub hWs_int).abs
  have hmin_nn : 0 ≤ min 1 (r : ℝ) := le_min zero_le_one (NNReal.coe_nonneg r)
  rw [ENNReal.ofReal_mul hmin_nn,
    ofReal_integral_eq_lintegral_ofReal hdiff_int (Eventually.of_forall fun _ ↦ abs_nonneg _)]
  exact tvDist_poissonLaw_le_of_isSizeBias P hr hW hmean hSB

/-- **Theorem 4.10** (`\label{thm121}`, `SteinIntro.tex:2120-2127`), `ℕ`-valued `Ws`
specialization. -/
theorem tvDist_poissonLaw_le_of_isSizeBias_nat
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W Ws : Ω → ℕ} (hW : AEMeasurable W P)
    (hmean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ))
    (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P (fun ω ↦ (Ws ω : ℝ)))
    (hWs_int : Integrable (fun ω ↦ (Ws ω : ℝ)) P) :
    tvDist (P.map W) (poissonLaw r) ≤
      ENNReal.ofReal (min 1 (r : ℝ) * ∫ ω, |(W ω : ℝ) + 1 - (Ws ω : ℝ)| ∂P) :=
  tvDist_poissonLaw_le_of_isSizeBias_integrable P hr hW hmean hSB hWs_int

/-! ### Corollary 4.11: Size-bias coupling for sums of zero-one indicators -/

/-- **Corollary 4.11** (`\label{cor121}`, `SteinIntro.tex:2142-2147`; `ISSUE-TYPO-4.11`):
size-bias coupling $W^s = \sum_{j \ne I} X_j^{(I)} + 1$ for `Fin n`-indexed zero-one indicators. -/
theorem sizeBias_sum_of_zero_one_fin
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : Fin n → ℝ := fun i ↦ P.real (X i ⁻¹' {1})
    let lam : ℝ := ∑ i : Fin n, p i
    0 < lam →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P (X i ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / lam) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1) :=
  sizeBias_sum_of_zero_one P hX_meas hX_zo

theorem map_map_of_measurable_aemeasurable
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {g : β → γ} {f : α → β} (hg : Measurable g) (hf : AEMeasurable f μ) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  ext s hs
  rw [Measure.map_apply hg hs, Measure.map_apply_of_aemeasurable hf (hg hs),
    Measure.map_apply_of_aemeasurable (hg.comp_aemeasurable hf) hs, Set.preimage_comp]

/-- **Corollary 4.11** over an arbitrary finite index type `ι` (`[Fintype ι] [DecidableEq ι]`,
for subgraph and combinatorial indexings in Section 4.3): size-bias coupling
$W^s = \sum_{j \ne I} X_j^{(I)} + 1$ for zero-one random variables $(X_i)_{i \in \iota}$. -/
theorem sizeBias_sum_of_zero_one_fintype
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [DiscreteMeasurableSpace ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ}
    {Y : (i : ι) → Ω → ({j : ι // j ≠ i} → ℝ)} {I : Ω → ι}
    (hX_meas : ∀ i : ι, Measurable (X i))
    (hX_zo : ∀ i : ι, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : ι → ℝ := fun i ↦ P.real (X i ⁻¹' {1})
    let lam : ℝ := ∑ i : ι, p i
    0 < lam →
    (∀ i : ι, AEMeasurable (Y i) P) →
    (∀ i : ι,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P (X i ⁻¹' {1})).map
          (fun ω (j : {j : ι // j ≠ i}) ↦ X j.1 ω)) →
    Measurable I →
    (∀ i : ι, P.real (I ⁻¹' {i}) = p i / lam) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    IsSizeBias P (fun ω ↦ ∑ i : ι, X i ω) P
      (fun ω ↦ (∑ j : {j : ι // j ≠ I ω}, Y (I ω) ω j) + 1) := by
  intro p lam hlam_pos hY_meas hY_law hI_meas hI_prob hI_indep
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let m : ℕ := Fintype.card ι
  let subEquiv : ∀ k : Fin m, {j : Fin m // j ≠ k} ≃ {j : ι // j ≠ e.symm k} := fun k ↦
    { toFun := fun j ↦ ⟨e.symm j.1, fun h ↦ j.2 (by simpa using congrArg e h)⟩
      invFun := fun j ↦ ⟨e j.1, fun h ↦ j.2 (by simpa using congrArg e.symm h)⟩
      left_inv := fun j ↦ Subtype.ext (e.right_inv j.1)
      right_inv := fun j ↦ Subtype.ext (e.left_inv j.1) }
  let X' : Fin m → Ω → ℝ := fun k ω ↦ X (e.symm k) ω
  let Y' : (k : Fin m) → Ω → ({j : Fin m // j ≠ k} → ℝ) :=
    fun k ω j ↦ Y (e.symm k) ω (subEquiv k j)
  let I' : Ω → Fin m := fun ω ↦ e (I ω)
  have hX'_meas : ∀ k : Fin m, Measurable (X' k) := fun k ↦ hX_meas (e.symm k)
  have hX'_zo : ∀ k : Fin m, ∀ᵐ ω ∂P, X' k ω = 0 ∨ X' k ω = 1 := fun k ↦ hX_zo (e.symm k)
  have hlam'_eq : (∑ k : Fin m, P.real (X' k ⁻¹' {1})) = lam :=
    e.symm.sum_comp (fun i ↦ P.real (X i ⁻¹' {1}))
  have hlam'_pos : 0 < ∑ k : Fin m, P.real (X' k ⁻¹' {1}) := hlam'_eq ▸ hlam_pos
  have hY'_meas : ∀ k : Fin m, AEMeasurable (Y' k) P := fun k ↦ by
    have hpull : Measurable fun (u : {j : ι // j ≠ e.symm k} → ℝ) (j : {j : Fin m // j ≠ k}) ↦
        u (subEquiv k j) :=
      Measurable.of_eval fun j ↦ measurable_pi_apply (subEquiv k j)
    exact hpull.comp_aemeasurable (hY_meas (e.symm k))
  have hY'_law : ∀ k : Fin m, 0 < P.real (X' k ⁻¹' {1}) →
      P.map (Y' k) =
        (ProbabilityTheory.cond P (X' k ⁻¹' {1})).map
          (fun ω (j : {j : Fin m // j ≠ k}) ↦ X' j.1 ω) := by
    intro k hk_pos
    let pull : ({j : ι // j ≠ e.symm k} → ℝ) → ({j : Fin m // j ≠ k} → ℝ) :=
      fun u j ↦ u (subEquiv k j)
    have hpull_meas : Measurable pull :=
      Measurable.of_eval fun j ↦ measurable_pi_apply (subEquiv k j)
    have h1 : P.map (Y' k) = (P.map (Y (e.symm k))).map pull :=
      (map_map_of_measurable_aemeasurable hpull_meas (hY_meas (e.symm k))).symm
    have hproj_meas : Measurable (fun ω (j : {j : ι // j ≠ e.symm k}) ↦ X j.1 ω) :=
      Measurable.of_eval fun j ↦ hX_meas j.1
    have h2 : ((ProbabilityTheory.cond P (X (e.symm k) ⁻¹' {1})).map
          (fun ω (j : {j : ι // j ≠ e.symm k}) ↦ X j.1 ω)).map pull =
        (ProbabilityTheory.cond P (X' k ⁻¹' {1})).map
          (fun ω (j : {j : Fin m // j ≠ k}) ↦ X' j.1 ω) := by
      rw [Measure.map_map hpull_meas hproj_meas]
      rfl
    rw [h1, hY_law (e.symm k) hk_pos, h2]
  have hI'_meas : Measurable I' := (Measurable.of_discrete (f := e)).comp hI_meas
  have hI'_prob : ∀ k : Fin m,
      P.real (I' ⁻¹' {k}) = P.real (X' k ⁻¹' {1}) / ∑ r : Fin m, P.real (X' r ⁻¹' {1}) := by
    intro k
    have hpre : I' ⁻¹' {k} = I ⁻¹' {e.symm k} := by
      ext ω
      simp [I', Equiv.eq_symm_apply]
    rw [hpre, hlam'_eq, hI_prob (e.symm k)]
  have hI'_indep :
      ProbabilityTheory.IndepFun I' (fun ω ↦ (fun k ↦ X' k ω, fun k ↦ Y' k ω)) P := by
    let φ₁ : ι → Fin m := e
    let φ₂ : ((i : ι) → ℝ) × ((i : ι) → {j : ι // j ≠ i} → ℝ) →
        (Fin m → ℝ) × ((k : Fin m) → {j : Fin m // j ≠ k} → ℝ) :=
      fun uv ↦ (fun k ↦ uv.1 (e.symm k), fun k j ↦ uv.2 (e.symm k) (subEquiv k j))
    have hφ₁ : Measurable φ₁ := Measurable.of_discrete
    have hφ₂ : Measurable φ₂ :=
      (Measurable.of_eval fun k ↦ (measurable_pi_apply (e.symm k)).comp measurable_fst).prodMk
        (Measurable.of_eval fun k ↦
          Measurable.of_eval fun j ↦
            (measurable_pi_apply (subEquiv k j)).comp
              ((measurable_pi_apply (e.symm k)).comp measurable_snd))
    exact hI_indep.comp hφ₁ hφ₂
  have hres := sizeBias_sum_of_zero_one P hX'_meas hX'_zo hlam'_pos hY'_meas hY'_law
    hI'_meas hI'_prob hI'_indep
  have hsumX : (fun ω ↦ ∑ k : Fin m, X' k ω) = fun ω ↦ ∑ i : ι, X i ω :=
    funext fun ω ↦ e.symm.sum_comp (fun i ↦ X i ω)
  have hsumY : (fun ω ↦ (∑ j : {j : Fin m // j ≠ I' ω}, Y' (I' ω) ω j) + 1) =
      fun ω ↦ (∑ j : {j : ι // j ≠ I ω}, Y (I ω) ω j) + 1 := by
    ext ω
    congr 1
    have hsum1 : (∑ j : {j : Fin m // j ≠ I' ω}, Y' (I' ω) ω j) =
        ∑ j : {j : ι // j ≠ e.symm (I' ω)}, Y (e.symm (I' ω)) ω j :=
      (subEquiv (I' ω)).sum_comp (fun j ↦ Y (e.symm (I' ω)) ω j)
    rw [hsum1]
    have haux : ∀ a b : ι, a = b →
        (∑ j : {j : ι // j ≠ a}, Y a ω j) = ∑ j : {j : ι // j ≠ b}, Y b ω j := by
      rintro a _ rfl
      rfl
    exact haux (e.symm (I' ω)) (I ω) (e.left_inv (I ω))
  rwa [hsumX, hsumY] at hres

/-- `ℕ`-valued indicator specialization of `sizeBias_sum_of_zero_one_fintype` over `[Fintype ι]`. -/
theorem sizeBias_sum_of_nat_zero_one_fintype
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [DiscreteMeasurableSpace ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ι → Ω → ℕ}
    {Y : (i : ι) → Ω → ({j : ι // j ≠ i} → ℕ)} {I : Ω → ι}
    (hX_meas : ∀ i : ι, Measurable (X i))
    (hX_zo : ∀ i : ι, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) :
    let p : ι → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let lam : ℝ := ∑ i : ι, p i
    0 < lam →
    (∀ i : ι, AEMeasurable (Y i) P) →
    (∀ i : ι,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : ι // j ≠ i}) ↦ X j.1 ω)) →
    Measurable I →
    (∀ i : ι, P.real (I ⁻¹' {i}) = p i / lam) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    IsSizeBias P (fun ω ↦ ((∑ i : ι, X i ω : ℕ) : ℝ)) P
      (fun ω ↦ (((∑ j : {j : ι // j ≠ I ω}, Y (I ω) ω j) + 1 : ℕ) : ℝ)) := by
  intro p lam hlam_pos hY_meas hY_law hI_meas hI_prob hI_indep
  let Xr : ι → Ω → ℝ := fun i ω ↦ (X i ω : ℝ)
  let Yr : (i : ι) → Ω → ({j : ι // j ≠ i} → ℝ) := fun i ω j ↦ (Y i ω j : ℝ)
  have hcast_nat : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  have hXr_meas : ∀ i : ι, Measurable (Xr i) :=
    fun i ↦ hcast_nat.comp (hX_meas i)
  have hXr_zo : ∀ i : ι, ∀ᵐ ω ∂P, Xr i ω = 0 ∨ Xr i ω = 1 :=
    fun i ↦ (hX_zo i).mono fun ω hω ↦ by rcases hω with h | h <;> simp [Xr, h]
  have hpre : ∀ i : ι, Xr i ⁻¹' {(1 : ℝ)} = {ω | X i ω = 1} := by
    intro i
    ext ω
    simp [Xr]
  have hYr_meas : ∀ i : ι, AEMeasurable (Yr i) P := fun i ↦ by
    let castPi : ({j : ι // j ≠ i} → ℕ) → ({j : ι // j ≠ i} → ℝ) := fun u j ↦ (u j : ℝ)
    have hcast : Measurable castPi :=
      Measurable.of_eval fun j ↦ hcast_nat.comp (measurable_pi_apply j)
    exact hcast.comp_aemeasurable (hY_meas i)
  have hYr_law : ∀ i : ι, 0 < P.real (Xr i ⁻¹' {1}) →
      P.map (Yr i) =
        (ProbabilityTheory.cond P (Xr i ⁻¹' {1})).map
          (fun ω (j : {j : ι // j ≠ i}) ↦ Xr j.1 ω) := by
    intro i hi_pos
    rw [hpre i] at hi_pos ⊢
    let castPi : ({j : ι // j ≠ i} → ℕ) → ({j : ι // j ≠ i} → ℝ) := fun u j ↦ (u j : ℝ)
    have hcast : Measurable castPi :=
      Measurable.of_eval fun j ↦ hcast_nat.comp (measurable_pi_apply j)
    have hproj : Measurable (fun ω (j : {j : ι // j ≠ i}) ↦ X j.1 ω) :=
      Measurable.of_eval fun j ↦ hX_meas j.1
    have h1 : P.map (Yr i) = (P.map (Y i)).map castPi :=
      (map_map_of_measurable_aemeasurable hcast (hY_meas i)).symm
    rw [h1, hY_law i hi_pos, Measure.map_map hcast hproj]
    rfl
  have hlam_eq : (∑ i : ι, P.real (Xr i ⁻¹' {1})) = lam := by
    simp only [hpre]
    rfl
  have hI_prob' : ∀ i : ι,
      P.real (I ⁻¹' {i}) = P.real (Xr i ⁻¹' {1}) / ∑ k : ι, P.real (Xr k ⁻¹' {1}) := by
    intro i
    rw [hpre i, hlam_eq]
    exact hI_prob i
  have hI_indep' :
      ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ Xr i ω, fun i ↦ Yr i ω)) P := by
    let castAll : ((i : ι) → ℕ) × ((i : ι) → {j : ι // j ≠ i} → ℕ) →
        ((i : ι) → ℝ) × ((i : ι) → {j : ι // j ≠ i} → ℝ) :=
      fun uv ↦ (fun i ↦ (uv.1 i : ℝ), fun i j ↦ (uv.2 i j : ℝ))
    have hcast : Measurable castAll :=
      (Measurable.of_eval fun i ↦
        hcast_nat.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      (Measurable.of_eval fun i ↦
        Measurable.of_eval fun j ↦
          hcast_nat.comp ((measurable_pi_apply j).comp
            ((measurable_pi_apply i).comp measurable_snd)))
    exact hI_indep.comp measurable_id hcast
  have hres := sizeBias_sum_of_zero_one_fintype P hXr_meas hXr_zo (hlam_eq ▸ hlam_pos)
    hYr_meas hYr_law hI_meas hI_prob' hI_indep'
  simpa [Xr, Yr, Nat.cast_sum, Nat.cast_add, Nat.cast_one] using hres

end SteinMethod
