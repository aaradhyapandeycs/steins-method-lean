/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Couplings
import Formalization.Defs.OrnsteinUhlenbeck
import Formalization.Exchangeable.SteinPairBound
import Formalization.Normal.DependencyCount
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Ornstein–Uhlenbeck Transition Kernel and Remark 3.5 (`Formalization.Leftovers.OrnsteinUhlenbeck`)

Proves the mathematical claims of Remark 3.5 (`SteinIntro.tex:1009-1024`; `ISSUE-TYPO-3.5`) for
the concrete Ornstein–Uhlenbeck transition kernel `ouKernel`:
* `instIsMarkovKernelOuKernel`: `ouKernel a` is a Markov kernel for every `a : ℝ`.
* `ouKernel_drift_littleO` & `ouKernel_mean_littleO` (`SteinIntro.tex:1014`):
  $\mathbb{E}[D(t + a) - D(t) \mid D(t) = x] = -a x + o(a)$ as $a \to 0^+$.
* `ouKernel_sq_increment_littleO` (`SteinIntro.tex:1015`):
  $\mathbb{E}[(D(t + a) - D(t))^2 \mid D(t) = x] = 2a + o(a)$ as $a \to 0^+$.
* `ouKernel_tail_littleO` (`SteinIntro.tex:1016`):
  $\mathbb{P}(|D(t + a) - D(t)| > \varepsilon \mid D(t) = x) = o(a)$ as $a \to 0^+$.
* `ouKernel_reversible`, `ouKernel_stationary`, and `ouKernel_isSteinPair`
  (`SteinIntro.tex:1018-1022`): for every $a > 0$, `ouKernel a` is reversible with respect to
  `stdNormalLaw`, has stationary distribution `stdNormalLaw`, and realizes a $(1 - e^{-a})$-Stein
  pair under `stdNormalLaw ⊗ₘ ouKernel a`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Basic Kernel Evaluation and Markov Property -/

/-- For $a > 0$, `ouKernel a x` is the Gaussian law $\mathcal{N}(e^{-a} x, 1 - e^{-2a})$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem ouKernel_of_pos {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ouKernel a x =
      gaussianReal (Real.exp (-a) * x) (Real.toNNReal (1 - Real.exp (-2 * a))) := by
  simp only [ouKernel, ha, ↓reduceIte]
  rfl

/-- For $a \le 0$, `ouKernel a` is the identity kernel `Kernel.id`
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
theorem ouKernel_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    ouKernel a = Kernel.id := by
  simp only [ouKernel, not_lt.mpr ha, ↓reduceIte]

/-- Non-vacuity witness: `ouKernel a` is a Markov kernel for every $a \in \mathbb{R}$
(Remark 3.5, `SteinIntro.tex:1009-1024`). -/
instance instIsMarkovKernelOuKernel (a : ℝ) : IsMarkovKernel (ouKernel a) where
  isProbabilityMeasure x := by
    by_cases ha : 0 < a
    · rw [ouKernel_of_pos ha x]
      infer_instance
    · rw [ouKernel_of_nonpos (not_lt.mp ha)]
      infer_instance

private lemma one_sub_exp_neg_two_mul_pos {a : ℝ} (ha : 0 < a) :
    0 < 1 - Real.exp (-2 * a) := by
  have hexp : Real.exp (-2 * a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

private lemma ouVar_ne_zero {a : ℝ} (ha : 0 < a) :
    Real.toNNReal (1 - Real.exp (-2 * a)) ≠ 0 :=
  (Real.toNNReal_pos.mpr (one_sub_exp_neg_two_mul_pos ha)).ne'

private lemma coe_ouVar {a : ℝ} (ha : 0 < a) :
    ((Real.toNNReal (1 - Real.exp (-2 * a)) : ℝ≥0) : ℝ) = 1 - Real.exp (-2 * a) :=
  Real.coe_toNNReal _ (one_sub_exp_neg_two_mul_pos ha).le

/-! ### Section 2: Increment Distribution and Exact Conditional Moments -/

/-- For $a > 0$, the increment $y \mapsto y - x$ under `ouKernel a x` has Gaussian law
$\mathcal{N}((e^{-a} - 1) x, 1 - e^{-2a})$ (Remark 3.5, `SteinIntro.tex:1013-1017`). -/
theorem ouKernel_map_sub_const {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (ouKernel a x).map (· - x) =
      gaussianReal ((Real.exp (-a) - 1) * x) (Real.toNNReal (1 - Real.exp (-2 * a))) := by
  rw [ouKernel_of_pos ha x, gaussianReal_map_sub_const x]
  congr 1
  ring

/-- Conditional mean $\int y\,d(\mathrm{ouKernel}\,a\,x)(y) = e^{-a} x$ for $a > 0$
(Remark 3.5, `SteinIntro.tex:1014`). -/
theorem integral_id_ouKernel {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ y, y ∂ouKernel a x) = Real.exp (-a) * x := by
  rw [ouKernel_of_pos ha x]
  exact integral_id_gaussianReal

/-- Conditional mean increment $\int (y - x)\,d(\mathrm{ouKernel}\,a\,x)(y) = (e^{-a} - 1) x$
for $a > 0$ (Remark 3.5, `SteinIntro.tex:1014`). -/
theorem integral_sub_ouKernel {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ y, (y - x) ∂ouKernel a x) = (Real.exp (-a) - 1) * x := by
  rw [ouKernel_of_pos ha x]
  have hid : Integrable (fun y : ℝ ↦ y)
      (gaussianReal (Real.exp (-a) * x) (Real.toNNReal (1 - Real.exp (-2 * a)))) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  rw [integral_sub hid (integrable_const x), integral_id_gaussianReal, integral_const,
    probReal_univ, one_smul]
  ring

/-- Conditional second moment of the increment for $a > 0$:
$\int (y - x)^2\,d(\mathrm{ouKernel}\,a\,x)(y) = (1 - e^{-2a}) + (e^{-a} - 1)^2 x^2$
(Remark 3.5, `SteinIntro.tex:1015`). -/
theorem integral_sq_sub_ouKernel {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ y, (y - x) ^ 2 ∂ouKernel a x) =
      (1 - Real.exp (-2 * a)) + (Real.exp (-a) - 1) ^ 2 * x ^ 2 := by
  set μ : Measure ℝ :=
    gaussianReal ((Real.exp (-a) - 1) * x) (Real.toNNReal (1 - Real.exp (-2 * a)))
  have hmap : (∫ y, (y - x) ^ 2 ∂ouKernel a x) = ∫ z, z ^ 2 ∂μ := by
    have hm := integral_map (μ := ouKernel a x) (φ := fun y ↦ y - x) (f := fun z : ℝ ↦ z ^ 2)
      (measurable_id.sub measurable_const).aemeasurable
      (continuous_pow 2).aestronglyMeasurable
    rw [← hm, ouKernel_map_sub_const ha x]
  have hvar := variance_eq_sub (μ := μ) (X := id) (memLp_id_gaussianReal 2)
  simp only [μ, variance_id_gaussianReal, Pi.pow_def, id_eq, integral_id_gaussianReal,
    coe_ouVar ha] at hvar
  rw [hmap]
  linarith

private lemma ouKernel_map_sub_eq_affine_stdNormal {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (ouKernel a x).map (· - x) =
      stdNormalLaw.map
        (fun z ↦ (Real.exp (-a) - 1) * x + Real.sqrt (1 - Real.exp (-2 * a)) * z) := by
  set m : ℝ := (Real.exp (-a) - 1) * x
  set s : ℝ := Real.sqrt (1 - Real.exp (-2 * a))
  calc
    (ouKernel a x).map (· - x)
      = gaussianReal (s * 0 + m) (NNReal.mk (s ^ 2) (sq_nonneg s) * 1) := by
          rw [ouKernel_map_sub_const ha x]
          congr 1
          · ring
          · ext
            rw [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one, coe_ouVar ha,
              Real.sq_sqrt (one_sub_exp_neg_two_mul_pos ha).le]
    _ = ((gaussianReal 0 1).map (s * ·)).map (m + ·) := by
          rw [gaussianReal_map_const_mul, gaussianReal_map_const_add]
    _ = stdNormalLaw.map (fun z ↦ m + s * z) := by
          rw [stdNormalLaw, Measure.map_map (measurable_const_add m) (measurable_const_mul s)]
          rfl

private lemma add_pow_four_le_eight_mul (u w : ℝ) :
    (u + w) ^ 4 ≤ 8 * u ^ 4 + 8 * w ^ 4 := by
  have hid : 8 * u ^ 4 + 8 * w ^ 4 - (u + w) ^ 4 =
      (2 * (u ^ 2 + w ^ 2) + (u + w) ^ 2) * (u - w) ^ 2 + 4 * (u ^ 2 - w ^ 2) ^ 2 := by
    ring
  have hnn : 0 ≤ (2 * (u ^ 2 + w ^ 2) + (u + w) ^ 2) * (u - w) ^ 2 +
      4 * (u ^ 2 - w ^ 2) ^ 2 := by
    positivity
  linarith

private lemma integral_pow_four_sub_ouKernel_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Integrable (fun y : ℝ ↦ (y - x) ^ 4) (ouKernel a x) ∧
      (∫ y, (y - x) ^ 4 ∂ouKernel a x) ≤
        8 * ((Real.exp (-a) - 1) * x) ^ 4 +
          8 * (1 - Real.exp (-2 * a)) ^ 2 * (∫ z, z ^ 4 ∂stdNormalLaw) := by
  set m : ℝ := (Real.exp (-a) - 1) * x
  set s : ℝ := Real.sqrt (1 - Real.exp (-2 * a))
  have hLp4_map : MemLp (id : ℝ → ℝ) 4 ((ouKernel a x).map (· - x)) := by
    rw [ouKernel_map_sub_const ha x]
    simpa using memLp_id_gaussianReal 4
  have hInt_map : Integrable (fun w : ℝ ↦ w ^ 4) ((ouKernel a x).map (· - x)) :=
    integrable_pow_four hLp4_map
  have hInt_ou : Integrable (fun y : ℝ ↦ (y - x) ^ 4) (ouKernel a x) :=
    (integrable_map_measure (continuous_pow 4).aestronglyMeasurable
      (measurable_id.sub measurable_const).aemeasurable).mp hInt_map
  refine ⟨hInt_ou, ?_⟩
  have hZ4 : Integrable (fun z : ℝ ↦ z ^ 4) stdNormalLaw := by
    rw [stdNormalLaw]
    exact integrable_pow_four (memLp_id_gaussianReal 4)
  have hInt_aff : Integrable (fun z : ℝ ↦ (m + s * z) ^ 4) stdNormalLaw := by
    have hEq := ouKernel_map_sub_eq_affine_stdNormal ha x
    rw [hEq] at hInt_map
    exact (integrable_map_measure (continuous_pow 4).aestronglyMeasurable
      (measurable_const.add (measurable_const.mul measurable_id)).aemeasurable).mp hInt_map
  have hEq_int : (∫ y, (y - x) ^ 4 ∂ouKernel a x) = ∫ z, (m + s * z) ^ 4 ∂stdNormalLaw := by
    calc
      (∫ y, (y - x) ^ 4 ∂ouKernel a x)
        = ∫ w, w ^ 4 ∂((ouKernel a x).map (· - x)) :=
          (integral_map (measurable_id.sub measurable_const).aemeasurable
            (continuous_pow 4).aestronglyMeasurable).symm
      _ = ∫ w, w ^ 4 ∂(stdNormalLaw.map (fun z ↦ m + s * z)) := by
          rw [ouKernel_map_sub_eq_affine_stdNormal ha x]
      _ = ∫ z, (m + s * z) ^ 4 ∂stdNormalLaw :=
          integral_map (measurable_const.add (measurable_const.mul measurable_id)).aemeasurable
            (continuous_pow 4).aestronglyMeasurable
  have hs4 : s ^ 4 = (1 - Real.exp (-2 * a)) ^ 2 := by
    have hs2 : s ^ 2 = 1 - Real.exp (-2 * a) :=
      Real.sq_sqrt (one_sub_exp_neg_two_mul_pos ha).le
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - Real.exp (-2 * a)) ^ 2 := by rw [hs2]
  have hBound_int : Integrable
      (fun z : ℝ ↦ 8 * m ^ 4 + 8 * (1 - Real.exp (-2 * a)) ^ 2 * z ^ 4) stdNormalLaw :=
    (integrable_const (8 * m ^ 4)).add (hZ4.const_mul (8 * (1 - Real.exp (-2 * a)) ^ 2))
  rw [hEq_int]
  calc
    (∫ z, (m + s * z) ^ 4 ∂stdNormalLaw)
      ≤ ∫ z, (8 * m ^ 4 + 8 * (1 - Real.exp (-2 * a)) ^ 2 * z ^ 4) ∂stdNormalLaw := by
        refine integral_mono hInt_aff hBound_int fun z ↦ ?_
        calc (m + s * z) ^ 4 ≤ 8 * m ^ 4 + 8 * (s * z) ^ 4 := add_pow_four_le_eight_mul m (s * z)
          _ = 8 * m ^ 4 + 8 * (1 - Real.exp (-2 * a)) ^ 2 * z ^ 4 := by
              rw [mul_pow s z, hs4]
              ring
    _ = 8 * m ^ 4 + 8 * (1 - Real.exp (-2 * a)) ^ 2 * (∫ z, z ^ 4 ∂stdNormalLaw) := by
        rw [integral_add (integrable_const _) (hZ4.const_mul _), integral_const,
          probReal_univ, one_smul, integral_const_mul]

/-! ### Section 3: Infinitesimal Diffusion Properties (Remark 3.5, Items 1–3) -/

private lemma tendsto_exp_neg_sub_one_div :
    Tendsto (fun a : ℝ ↦ (Real.exp (-a) - 1) / a) (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
  have hderiv : HasDerivAt (fun a : ℝ ↦ Real.exp (-a)) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg.exp
  have hslope := hderiv.tendsto_slope_zero_right
  refine hslope.congr fun a ↦ ?_
  simp [smul_eq_mul, div_eq_inv_mul]

private lemma tendsto_one_sub_exp_neg_two_mul_div :
    Tendsto (fun a : ℝ ↦ (1 - Real.exp (-2 * a)) / a) (nhdsWithin 0 (Ioi 0)) (nhds 2) := by
  have h1 : HasDerivAt (fun a : ℝ ↦ -2 * a) (-2) 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).const_mul (-2 : ℝ)
    rwa [mul_one] at h
  have h2 : HasDerivAt (fun a : ℝ ↦ Real.exp (-2 * a)) (-2) 0 := by
    have h := h1.exp
    simpa only [mul_zero, Real.exp_zero, one_mul] using h
  have hderiv : HasDerivAt (fun a : ℝ ↦ 1 - Real.exp (-2 * a)) 2 0 := by
    have h := h2.const_sub (1 : ℝ)
    rwa [neg_neg] at h
  have hslope := hderiv.tendsto_slope_zero_right
  refine hslope.congr fun a ↦ ?_
  simp [smul_eq_mul, div_eq_inv_mul]

private lemma tendsto_exp_neg_sub_one :
    Tendsto (fun a : ℝ ↦ Real.exp (-a) - 1) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcont : Continuous (fun a : ℝ ↦ Real.exp (-a) - 1) := by fun_prop
  have ht : Tendsto (fun a : ℝ ↦ Real.exp (-a) - 1) (nhdsWithin 0 (Ioi 0))
      (nhds (Real.exp (-(0 : ℝ)) - 1)) := hcont.continuousWithinAt.tendsto
  simpa only [neg_zero, Real.exp_zero, sub_self] using ht

private lemma tendsto_one_sub_exp_neg_two_mul :
    Tendsto (fun a : ℝ ↦ 1 - Real.exp (-2 * a)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcont : Continuous (fun a : ℝ ↦ 1 - Real.exp (-2 * a)) := by fun_prop
  have ht : Tendsto (fun a : ℝ ↦ 1 - Real.exp (-2 * a)) (nhdsWithin 0 (Ioi 0))
      (nhds (1 - Real.exp (-2 * (0 : ℝ)))) := hcont.continuousWithinAt.tendsto
  simpa only [mul_zero, Real.exp_zero, sub_self] using ht

/-- Remark 3.5, Item 1 (`SteinIntro.tex:1014`): for every $x \in \mathbb{R}$,
$\mathbb{E}[D(t + a) - D(t) \mid D(t) = x] = -a x + o(a)$ as $a \to 0^+$. -/
theorem ouKernel_drift_littleO (x : ℝ) :
    Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂ouKernel a x) - (-a * x)) / a)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hlim : Tendsto (fun a : ℝ ↦ ((Real.exp (-a) - 1) / a + 1) * x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [neg_add_cancel, zero_mul] using
      (tendsto_exp_neg_sub_one_div.add (tendsto_const_nhds (x := (1 : ℝ)))).mul_const x
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  rw [integral_sub_ouKernel ha x]
  have ha_ne : a ≠ 0 := ha.ne'
  field_simp [ha_ne]
  ring

/-- Equivalent unshifted form of Remark 3.5, Item 1 (`SteinIntro.tex:1014`):
$(\int y\,d(\mathrm{ouKernel}\,a\,x)(y) - x - (-a x)) / a \to 0$ as $a \to 0^+$. -/
theorem ouKernel_mean_littleO (x : ℝ) :
    Tendsto (fun a : ℝ ↦ ((∫ y, y ∂ouKernel a x) - x - (-a * x)) / a)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  refine (ouKernel_drift_littleO x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  rw [integral_sub_ouKernel ha x, integral_id_ouKernel ha x]
  ring

/-- Remark 3.5, Item 2 (`SteinIntro.tex:1015`): for every $x \in \mathbb{R}$,
$\mathbb{E}[(D(t + a) - D(t))^2 \mid D(t) = x] = 2a + o(a)$ as $a \to 0^+$. -/
theorem ouKernel_sq_increment_littleO (x : ℝ) :
    Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂ouKernel a x) - 2 * a) / a)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h1 : Tendsto (fun a : ℝ ↦ (1 - Real.exp (-2 * a)) / a - 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [sub_self] using
      tendsto_one_sub_exp_neg_two_mul_div.sub (tendsto_const_nhds (x := (2 : ℝ)))
  have h2 : Tendsto (fun a : ℝ ↦ ((Real.exp (-a) - 1) / a) * (Real.exp (-a) - 1) * x ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (tendsto_exp_neg_sub_one_div.mul tendsto_exp_neg_sub_one).mul_const (x ^ 2)
  have hsum : Tendsto
      (fun a : ℝ ↦ ((1 - Real.exp (-2 * a)) / a - 2) +
        ((Real.exp (-a) - 1) / a) * (Real.exp (-a) - 1) * x ^ 2)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using h1.add h2
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  rw [integral_sq_sub_ouKernel ha x]
  have ha_ne : a ≠ 0 := ha.ne'
  field_simp [ha_ne]
  ring

/-- Remark 3.5, Item 3 (`SteinIntro.tex:1016`): for every $x \in \mathbb{R}$ and $\varepsilon > 0$,
$\mathbb{P}(|D(t + a) - D(t)| > \varepsilon \mid D(t) = x) = o(a)$ as $a \to 0^+$. -/
theorem ouKernel_tail_littleO (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun a : ℝ ↦ (ouKernel a x).real {y : ℝ | ε < |y - x|} / a)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  set M4 : ℝ := ∫ z, z ^ 4 ∂stdNormalLaw
  set upper : ℝ → ℝ := fun a ↦
    (8 * (((Real.exp (-a) - 1) / a) * (Real.exp (-a) - 1) ^ 3 * x ^ 4) +
      8 * (((1 - Real.exp (-2 * a)) / a) * (1 - Real.exp (-2 * a)) * M4)) / ε ^ 4
  have hpow3 : Tendsto (fun a : ℝ ↦ (Real.exp (-a) - 1) ^ 3)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using tendsto_exp_neg_sub_one.pow 3
  have ht1 : Tendsto
      (fun a : ℝ ↦ 8 * (((Real.exp (-a) - 1) / a) * (Real.exp (-a) - 1) ^ 3 * x ^ 4))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((tendsto_exp_neg_sub_one_div.mul hpow3).mul_const (x ^ 4)).const_mul 8
  have ht2 : Tendsto
      (fun a : ℝ ↦ 8 * (((1 - Real.exp (-2 * a)) / a) * (1 - Real.exp (-2 * a)) * M4))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using
      ((tendsto_one_sub_exp_neg_two_mul_div.mul tendsto_one_sub_exp_neg_two_mul).mul_const
        M4).const_mul 8
  have hupper : Tendsto upper (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    dsimp only [upper]
    simpa using (ht1.add ht2).div_const (ε ^ 4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    exact div_nonneg measureReal_nonneg ha.le
  · filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    obtain ⟨hInt4, hMom4⟩ := integral_pow_four_sub_ouKernel_le ha x
    have hMeasSet : MeasurableSet {y : ℝ | ε < |y - x|} :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet
    have hMarkov :
        ε ^ 4 * (ouKernel a x).real {y : ℝ | ε < |y - x|} ≤
          ∫ y, (y - x) ^ 4 ∂ouKernel a x := by
      have hInd : ε ^ 4 * (ouKernel a x).real {y : ℝ | ε < |y - x|} =
          ∫ y, {y' : ℝ | ε < |y' - x|}.indicator (fun _ ↦ ε ^ 4) y ∂ouKernel a x := by
        rw [integral_indicator_const _ hMeasSet, smul_eq_mul, mul_comm]
      rw [hInd]
      refine integral_mono ((integrable_const (ε ^ 4)).indicator hMeasSet) hInt4 fun y ↦ ?_
      by_cases hy : y ∈ {y' : ℝ | ε < |y' - x|}
      · rw [Set.indicator_of_mem hy]
        have hlt : ε ≤ |y - x| := le_of_lt hy
        have hp4 : ε ^ 4 ≤ |y - x| ^ 4 := pow_le_pow_left₀ hε.le hlt 4
        have habs4 : |y - x| ^ 4 = (y - x) ^ 4 := by
          have hsq : |y - x| ^ 2 = (y - x) ^ 2 := sq_abs (y - x)
          calc |y - x| ^ 4 = (|y - x| ^ 2) ^ 2 := by ring
            _ = ((y - x) ^ 2) ^ 2 := by rw [hsq]
            _ = (y - x) ^ 4 := by ring
        linarith
      · rw [Set.indicator_of_notMem hy]
        positivity
    have hε4_pos : 0 < ε ^ 4 := pow_pos hε 4
    have ha_ne : a ≠ 0 := ha.ne'
    have hε4_ne : ε ^ 4 ≠ 0 := hε4_pos.ne'
    calc
      (ouKernel a x).real {y : ℝ | ε < |y - x|} / a
        ≤ ((∫ y, (y - x) ^ 4 ∂ouKernel a x) / ε ^ 4) / a := by
          gcongr
          rwa [le_div_iff₀' hε4_pos]
      _ ≤ ((8 * ((Real.exp (-a) - 1) * x) ^ 4 +
            8 * (1 - Real.exp (-2 * a)) ^ 2 * M4) / ε ^ 4) / a := by
          gcongr
      _ = upper a := by
          dsimp only [upper]
          field_simp [ha_ne, hε4_ne]

/-! ### Section 4: Reversibility, Stationarity, Stein Pair Witness, and `rem3_5_proof` -/

private noncomputable def ouJointPDF (a : ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  gaussianPDF 0 1 p.1 *
    gaussianPDF (Real.exp (-a) * p.1) (Real.toNNReal (1 - Real.exp (-2 * a))) p.2

private lemma measurable_ouJointPDF (a : ℝ) : Measurable (ouJointPDF a) := by
  unfold ouJointPDF
  have h1 : Measurable (fun p : ℝ × ℝ ↦ gaussianPDF 0 1 p.1) :=
    (measurable_gaussianPDF 0 1).comp measurable_fst
  have h2 : Measurable (fun p : ℝ × ℝ ↦
      gaussianPDF (Real.exp (-a) * p.1) (Real.toNNReal (1 - Real.exp (-2 * a))) p.2) :=
    measurable_uncurry_gaussianPDF.comp
      ((measurable_const.mul measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
  exact h1.mul h2

private lemma ouJointPDF_swap {a : ℝ} (ha : 0 < a) (p : ℝ × ℝ) :
    ouJointPDF a (Prod.swap p) = ouJointPDF a p := by
  rcases p with ⟨x, y⟩
  set c : ℝ := Real.exp (-a)
  set v : ℝ≥0 := Real.toNNReal (1 - Real.exp (-2 * a))
  have hc2 : Real.exp (-2 * a) = c ^ 2 := by
    dsimp only [c]
    rw [← Real.exp_nat_mul]
    ring_nf
  have hv_coe : (v : ℝ) = 1 - c ^ 2 := by
    dsimp only [v]
    rw [coe_ouVar ha, hc2]
  have hv_pos : 0 < (v : ℝ) := by
    rw [hv_coe, ← hc2]
    exact one_sub_exp_neg_two_mul_pos ha
  have hv_ne : (v : ℝ) ≠ 0 := hv_pos.ne'
  unfold ouJointPDF
  simp only [Prod.swap_prod_mk, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 y),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one]
  rw [mul_mul_mul_comm, ← Real.exp_add, mul_mul_mul_comm, ← Real.exp_add]
  congr 2
  have hc_def : Real.exp (-a) = c := rfl
  have h1c_ne : 1 - c ^ 2 ≠ 0 := hv_coe ▸ hv_ne
  rw [hv_coe, hc_def]
  field_simp [h1c_ne]
  ring

private lemma stdNormalLaw_compProd_ouKernel_apply {a : ℝ} (ha : 0 < a)
    {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    (stdNormalLaw ⊗ₘ ouKernel a) s =
      ∫⁻ x, ∫⁻ y, s.indicator (ouJointPDF a) (x, y) ∂volume ∂volume := by
  set c : ℝ := Real.exp (-a)
  set v : ℝ≥0 := Real.toNNReal (1 - Real.exp (-2 * a))
  have hv_ne : v ≠ 0 := ouVar_ne_zero ha
  let g : ℝ × ℝ → ℝ≥0∞ := fun p ↦ s.indicator (fun q : ℝ × ℝ ↦ gaussianPDF (c * q.1) v q.2) p
  have hg_meas : Measurable g :=
    (measurable_uncurry_gaussianPDF.comp
      ((measurable_const.mul measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))).indicator hs
  have hslice : ∀ x : ℝ, ouKernel a x (Prod.mk x ⁻¹' s) = ∫⁻ y, g (x, y) ∂volume := by
    intro x
    rw [ouKernel_of_pos ha x, gaussianReal_apply _ hv_ne,
      ← lintegral_indicator (measurable_prodMk_left hs)]
    refine lintegral_congr fun y ↦ ?_
    by_cases hxy : (x, y) ∈ s
    · have hy : y ∈ Prod.mk x ⁻¹' s := hxy
      simp only [g, c, Set.indicator_of_mem hy, Set.indicator_of_mem hxy]
    · have hy : y ∉ Prod.mk x ⁻¹' s := hxy
      simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]
  rw [Measure.compProd_apply hs]
  simp_rw [hslice]
  rw [stdNormalLaw, gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul₀ (measurable_gaussianPDF 0 1).aemeasurable
      hg_meas.lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun x ↦ ?_
  dsimp only [Pi.mul_apply]
  have hgy : Measurable (fun y : ℝ ↦ g (x, y)) :=
    hg_meas.comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_const_mul _ hgy]
  refine lintegral_congr fun y ↦ ?_
  by_cases hxy : (x, y) ∈ s
  · simp only [g, c, v, ouJointPDF, Set.indicator_of_mem hxy]
  · simp only [g, Set.indicator_of_notMem hxy, mul_zero]

/-- Reversibility of `ouKernel a` with respect to `stdNormalLaw` for $a > 0$
(Remark 3.5, `SteinIntro.tex:1018-1019`). -/
theorem ouKernel_reversible {a : ℝ} (ha : 0 < a) :
    (stdNormalLaw ⊗ₘ ouKernel a).map Prod.swap = stdNormalLaw ⊗ₘ ouKernel a := by
  ext s hs
  rw [Measure.map_apply measurable_swap hs,
    stdNormalLaw_compProd_ouKernel_apply ha (measurable_swap hs),
    stdNormalLaw_compProd_ouKernel_apply ha hs]
  have hswap_ind : ∀ x y : ℝ,
      (Prod.swap ⁻¹' s).indicator (ouJointPDF a) (x, y) =
        s.indicator (ouJointPDF a) (y, x) := by
    intro x y
    by_cases hxy : (y, x) ∈ s
    · have hpre : (x, y) ∈ Prod.swap ⁻¹' s := hxy
      rw [Set.indicator_of_mem hpre, Set.indicator_of_mem hxy]
      exact (ouJointPDF_swap ha (x, y)).symm
    · have hpre : (x, y) ∉ Prod.swap ⁻¹' s := hxy
      rw [Set.indicator_of_notMem hpre, Set.indicator_of_notMem hxy]
  simp_rw [hswap_ind]
  exact lintegral_lintegral_swap
    (((measurable_ouJointPDF a).indicator hs).comp measurable_swap).aemeasurable

/-- Stationarity of `stdNormalLaw` under `ouKernel a` for $a > 0$
(Remark 3.5, `SteinIntro.tex:1018-1019`). -/
theorem ouKernel_stationary {a : ℝ} (ha : 0 < a) :
    stdNormalLaw.bind (ouKernel a) = stdNormalLaw := by
  calc
    stdNormalLaw.bind (ouKernel a)
      = (stdNormalLaw ⊗ₘ ouKernel a).snd := (Measure.snd_compProd stdNormalLaw (ouKernel a)).symm
    _ = ((stdNormalLaw ⊗ₘ ouKernel a).map Prod.swap).snd := by rw [ouKernel_reversible ha]
    _ = (stdNormalLaw ⊗ₘ ouKernel a).fst := by
        rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
        rfl
    _ = stdNormalLaw := Measure.fst_compProd stdNormalLaw (ouKernel a)

/-- Non-vacuity Stein-pair witness (Remark 3.5, `SteinIntro.tex:1021-1022`): for every $a > 0$,
under `P = stdNormalLaw ⊗ₘ ouKernel a`, `(Prod.fst, Prod.snd)` is a `(1 - e^{-a})`-Stein pair
with unit variance $\operatorname{Var}(W) = 1$. -/
theorem ouKernel_isSteinPair {a : ℝ} (ha : 0 < a) :
    IsSteinPair (stdNormalLaw ⊗ₘ ouKernel a) (1 - Real.exp (-a)) Prod.fst Prod.snd ∧
      variance Prod.fst (stdNormalLaw ⊗ₘ ouKernel a) = 1 := by
  set P : Measure (ℝ × ℝ) := stdNormalLaw ⊗ₘ ouKernel a
  have : IsProbabilityMeasure P := inferInstance
  have hExch : IsExchangeablePair P Prod.fst Prod.snd :=
    reversibleMarkov_isExchangeablePair stdNormalLaw (ouKernel a)
      (ouKernel_reversible ha) measurable_id
  have ha_par : 0 < 1 - Real.exp (-a) ∧ 1 - Real.exp (-a) ≤ 1 := by
    have hexp_lt : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hexp_pos : 0 < Real.exp (-a) := Real.exp_pos (-a)
    exact ⟨by linarith, by linarith⟩
  have hmap_fst : P.map Prod.fst = stdNormalLaw :=
    Measure.fst_compProd stdNormalLaw (ouKernel a)
  have hLp2_fst : MemLp Prod.fst 2 P := by
    have hid2 : MemLp (id : ℝ → ℝ) 2 (P.map Prod.fst) := by
      rw [hmap_fst, stdNormalLaw]
      exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff aestronglyMeasurable_id measurable_fst.aemeasurable).mp hid2
  have hInt_fst : Integrable Prod.fst P := hLp2_fst.integrable one_le_two
  have hInt_snd : Integrable Prod.snd P :=
    hExch.fst_identDistrib_snd.integrable_snd hInt_fst
  have hVar_fst : variance Prod.fst P = 1 := by
    have hv := variance_map (μ := P) (Y := Prod.fst) (X := id)
      (by rw [hmap_fst]; exact aemeasurable_id) measurable_fst.aemeasurable
    rw [hmap_fst, stdNormalLaw, variance_id_gaussianReal, NNReal.coe_one] at hv
    exact hv.symm
  refine ⟨⟨hExch, ha_par.1, ha_par.2, measurable_fst, hInt_fst, ?_⟩, hVar_fst⟩
  have hm_le :
      MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance ≤
        (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    measurable_fst.comap_le
  have hsm_rhs : StronglyMeasurable[MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ) inferInstance]
      (fun p : ℝ × ℝ ↦ (1 - (1 - Real.exp (-a))) * p.1) :=
    ((measurable_const.mul (comap_measurable (m := inferInstance) Prod.fst))).stronglyMeasurable
  have hInt_rhs : Integrable (fun p : ℝ × ℝ ↦ (1 - (1 - Real.exp (-a))) * p.1) P :=
    hInt_fst.const_mul _
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := P) hm_le hInt_snd
    (fun s _ _ ↦ hInt_rhs.integrableOn) ?_ hsm_rhs.aestronglyMeasurable).symm
  rintro s ⟨A, hA, rfl⟩ _
  have hpre : (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' A = A ×ˢ univ := by ext p; simp
  rw [hpre, Measure.setIntegral_compProd hA MeasurableSet.univ hInt_rhs.integrableOn,
    Measure.setIntegral_compProd hA MeasurableSet.univ hInt_snd.integrableOn]
  refine setIntegral_congr_fun hA fun x _ ↦ ?_
  simp only [Measure.restrict_univ, integral_const, probReal_univ, one_smul,
    integral_id_ouKernel ha x]
  ring

/-- Partial proof of Remark 3.5 (`SteinIntro.tex:1009-1024`; `ISSUE-TYPO-3.5`): verifies the
three infinitesimal properties (`L1014-1016`), reversibility and stationarity with respect to
`stdNormalLaw` (`L1018-1019`), and the $(1 - e^{-a})$-Stein pair property (`L1021-1022`) for
`ouKernel`. The martingale-problem uniqueness assertion at `L1018` ("These three properties
determine the O-U diffusion process") is not formalized. -/
theorem rem3_5_proof :
    (∀ x : ℝ,
      Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ∂ouKernel a x) - (-a * x)) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
    (∀ x : ℝ,
      Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂ouKernel a x) - 2 * a) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
    (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun a : ℝ ↦ (ouKernel a x).real {y : ℝ | ε < |y - x|} / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
    (∀ a : ℝ, 0 < a →
      IsMarkovKernel (ouKernel a) ∧
        (stdNormalLaw ⊗ₘ ouKernel a).map Prod.swap = stdNormalLaw ⊗ₘ ouKernel a ∧
        stdNormalLaw.bind (ouKernel a) = stdNormalLaw ∧
        IsSteinPair (stdNormalLaw ⊗ₘ ouKernel a) (1 - Real.exp (-a)) Prod.fst Prod.snd) :=
  ⟨ouKernel_drift_littleO,
    ouKernel_sq_increment_littleO,
    fun x _ hε ↦ ouKernel_tail_littleO x hε,
    fun _ ha ↦
      ⟨inferInstance, ouKernel_reversible ha, ouKernel_stationary ha,
        (ouKernel_isSteinPair ha).1⟩⟩

end SteinMethod
