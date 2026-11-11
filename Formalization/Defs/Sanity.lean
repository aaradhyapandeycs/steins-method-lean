/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Non-Vacuity Sanity Checks (`Formalization.Defs.Sanity`)

Concrete evaluations and witness constructions verifying non-vacuity of the core metrics, normal
Stein equation solution, size-bias relation, and linear-regression $a$-Stein pair definitions in
`Formalization.Defs` for Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`,
`SteinIntro.tex`; rulings `D1`–`D9` of `docs/AUTHOR_RULINGS.md`).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SteinMethod

private lemma le_ipm {α : Type*} [MeasurableSpace α] {H : Set (α → ℝ)} {μ ν : Measure α}
    {h : α → ℝ} (hh : h ∈ H) (hμ : Integrable h μ) (hν : Integrable h ν) :
    ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| ≤ ipm H μ ν :=
  le_iSup₂_of_le h hh (le_iSup_of_le ⟨hμ, hν⟩ le_rfl)

private lemma ipm_le {α : Type*} [MeasurableSpace α] {H : Set (α → ℝ)} {μ ν : Measure α}
    {c : ℝ≥0∞}
    (hc : ∀ h ∈ H, Integrable h μ → Integrable h ν →
      ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| ≤ c) :
    ipm H μ ν ≤ c :=
  iSup₂_le fun h hh ↦ iSup_le fun ⟨hμ, hν⟩ ↦ hc h hh hμ hν

private lemma indicator_one_bounds (A : Set ℝ) (x : ℝ) :
    0 ≤ A.indicator (1 : ℝ → ℝ) x ∧ A.indicator (1 : ℝ → ℝ) x ≤ 1 := by
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx 1, Pi.one_apply]
    exact ⟨zero_le_one, le_rfl⟩
  · rw [Set.indicator_of_notMem hx 1]
    exact ⟨le_rfl, zero_le_one⟩

private lemma indicator_one_dirac_sub_le (A : Set ℝ) :
    ENNReal.ofReal
      |(∫ x, A.indicator (1 : ℝ → ℝ) x ∂Measure.dirac 0) -
        (∫ x, A.indicator (1 : ℝ → ℝ) x ∂Measure.dirac 1)| ≤ 1 := by
  rw [integral_dirac, integral_dirac, ENNReal.ofReal_le_one]
  obtain ⟨h0a, h0b⟩ := indicator_one_bounds A 0
  obtain ⟨h1a, h1b⟩ := indicator_one_bounds A 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma one_le_ipm_indicator {H : Set (ℝ → ℝ)} {A : Set ℝ}
    (hA : A.indicator 1 ∈ H) (h0 : (0 : ℝ) ∈ A) (h1 : (1 : ℝ) ∉ A) :
    1 ≤ ipm H (Measure.dirac 0) (Measure.dirac 1) := by
  have hle := le_ipm (μ := Measure.dirac 0) (ν := Measure.dirac 1) hA
    (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top)
  rw [integral_dirac, integral_dirac, Set.indicator_of_mem h0 1,
    Set.indicator_of_notMem h1 1, Pi.one_apply, sub_zero, abs_one,
    ENNReal.ofReal_one] at hle
  exact hle

/-- Non-vacuity of `wassersteinDist`: $d_{\mathrm{W}}(\delta_0, \delta_1) = 1$
(Section 1.1.1 item 2 `\label{probmet}`, `SteinIntro.tex:516-519`; rulings `D1`–`D2`). -/
theorem wassersteinDist_dirac_zero_one :
    wassersteinDist (Measure.dirac 0) (Measure.dirac 1) = 1 := by
  rw [wassersteinDist]
  refine le_antisymm (ipm_le fun h hh _ _ ↦ ?_) ?_
  · rw [integral_dirac, integral_dirac, ENNReal.ofReal_le_one]
    have hd := LipschitzWith.dist_le_mul hh 0 1
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one] at hd
    have h01 : |(0 : ℝ) - 1| = 1 := by norm_num
    linarith
  · have hle := le_ipm (H := {h : ℝ → ℝ | LipschitzWith 1 h})
      (μ := Measure.dirac 0) (ν := Measure.dirac 1) LipschitzWith.id
      (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top)
    rw [integral_dirac, integral_dirac, id_eq, id_eq, zero_sub, abs_neg, abs_one,
      ENNReal.ofReal_one] at hle
    exact hle

/-- Non-vacuity of `tvDist`: $d_{\mathrm{TV}}(\delta_0, \delta_1) = 1$
(Section 1.1.1 item 3 `\label{probmet}`, `SteinIntro.tex:520-521`; Proposition 1.2(3)
`\label{prop22}`, `SteinIntro.tex:532-535`; rulings `D1`–`D3`). -/
theorem tvDist_dirac_zero_one :
    tvDist (Measure.dirac (0 : ℝ)) (Measure.dirac 1) = 1 := by
  rw [tvDist]
  refine le_antisymm (ipm_le fun h hh _ _ ↦ ?_) ?_
  · rcases hh with ⟨A, _, rfl⟩
    exact indicator_one_dirac_sub_le A
  · refine one_le_ipm_indicator ⟨{0}, measurableSet_singleton 0, rfl⟩
      (Set.mem_singleton 0) ?_
    rw [Set.mem_singleton_iff]
    norm_num

/-- Non-vacuity of `kolmogorovDist`: $d_{\mathrm{K}}(\delta_0, \delta_1) = 1$
(Section 1.1.1 item 1 `\label{probmet}`, `SteinIntro.tex:513-515`; rulings `D1`–`D2`). -/
theorem kolmogorovDist_dirac_zero_one :
    kolmogorovDist (Measure.dirac 0) (Measure.dirac 1) = 1 := by
  rw [kolmogorovDist]
  refine le_antisymm (ipm_le fun h hh _ _ ↦ ?_) ?_
  · rcases hh with ⟨x, rfl⟩
    exact indicator_one_dirac_sub_le (Set.Iic x)
  · refine one_le_ipm_indicator ⟨0, rfl⟩ (Set.mem_Iic.mpr le_rfl) ?_
    rw [Set.mem_Iic]
    norm_num

/-- Non-degeneracy of `wassersteinDist` on the diagonal: $d_{\mathrm{W}}(\mu, \mu) = 0$
(Section 1.1.1 item 2 `\label{probmet}`, `SteinIntro.tex:516-519`; rulings `D1`–`D2`). -/
theorem wassersteinDist_self (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    wassersteinDist μ μ = 0 := by
  rw [wassersteinDist]
  refine le_antisymm (ipm_le fun h _ _ _ ↦ ?_) zero_le
  rw [sub_self, abs_zero, ENNReal.ofReal_zero]

/-- Non-vacuity of `normalSteinSol`: $f_{\mathbb{I}[\cdot \le 0]}$ is not identically zero
(Lemma 2.2 `\label{lem2}`, eq. `(2.1)` `\label{1a}`, `SteinIntro.tex:578-588`; Lemma 2.5
`\label{lem31}`, eq. `(2.6)` `\label{33}`, `SteinIntro.tex:675-684`; ruling `D4`). -/
theorem normalSteinSol_indicator_Iic_zero_ne_zero :
    ∃ w : ℝ, normalSteinSol ((Set.Iic 0).indicator 1) w ≠ 0 := by
  refine ⟨0, ?_⟩
  rw [normalSteinSol]
  refine mul_ne_zero (Real.exp_ne_zero _) ?_
  have hcongr :
      (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-t ^ 2 / 2) *
          (stdNormalExpect ((Set.Iic 0).indicator 1) -
            (Set.Iic (0 : ℝ)).indicator (1 : ℝ → ℝ) t)) =
      ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-t ^ 2 / 2) * stdNormalExpect ((Set.Iic 0).indicator 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht0 : t ∉ Set.Iic (0 : ℝ) := not_le_of_gt (Set.mem_Ioi.mp ht)
    rw [Set.indicator_of_notMem ht0 1, sub_zero]
  rw [hcongr, integral_mul_const]
  refine mul_ne_zero ?_ ?_
  · have heq (t : ℝ) : -t ^ 2 / 2 = -(1 / 2 : ℝ) * t ^ 2 := by ring
    simp_rw [heq]
    rw [integral_gaussian_Ioi]
    exact (div_pos (Real.sqrt_pos_of_pos (div_pos Real.pi_pos (by norm_num))) two_pos).ne'
  · rw [stdNormalExpect, integral_indicator_one measurableSet_Iic,
      measureReal_ne_zero_iff (measure_ne_top _ _)]
    intro h0
    have hvol := ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
    rw [Real.volume_Iic] at hvol
    exact ENNReal.top_ne_zero hvol

/-- Symmetric $\mathrm{Bernoulli}(1/2)$ measure on `Bool` witnessing `IsSizeBias`
(Definition 3.7 `\label{sbc}`, `SteinIntro.tex:1224-1230`; ruling `D8`). -/
noncomputable def bernoulliHalfMeasure : Measure Bool :=
  (1 / 2 : ℝ≥0) • Measure.dirac true + (1 / 2 : ℝ≥0) • Measure.dirac false

instance : IsProbabilityMeasure bernoulliHalfMeasure where
  measure_univ := by
    rw [bernoulliHalfMeasure, Measure.coe_add, Pi.add_apply,
      Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply,
      measure_univ, measure_univ, mul_one, ← ENNReal.coe_add,
      ENNReal.coe_eq_one, ← NNReal.coe_eq_one, NNReal.coe_add, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
    norm_num

/-- Indicator random variable $X : \mathrm{Bool} \to \{0, 1\}$ witnessing `IsSizeBias`
(Definition 3.7 `\label{sbc}`, `SteinIntro.tex:1224-1230`; ruling `D8`). -/
def bernoulliHalfRV : Bool → ℝ
  | true => 1
  | false => 0

private lemma integral_bernoulliHalfMeasure (g : Bool → ℝ) :
    ∫ b, g b ∂bernoulliHalfMeasure = (1 / 2 : ℝ) * g true + (1 / 2 : ℝ) * g false := by
  have ht : Integrable g ((1 / 2 : ℝ≥0) • Measure.dirac true) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  have hf : Integrable g ((1 / 2 : ℝ≥0) • Measure.dirac false) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  rw [bernoulliHalfMeasure, integral_add_measure ht hf, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_dirac, integral_dirac, NNReal.smul_def,
    NNReal.smul_def, smul_eq_mul, smul_eq_mul, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]

private lemma integral_bernoulliHalfRV :
    ∫ b, bernoulliHalfRV b ∂bernoulliHalfMeasure = 1 / 2 := by
  rw [integral_bernoulliHalfMeasure]
  dsimp only [bernoulliHalfRV]
  norm_num

/-- Concrete satisfaction of `IsSizeBias` for $X \sim \mathrm{Bernoulli}(1/2)$ and $X^s \equiv 1$
(Definition 3.7 `\label{sbc}`, `SteinIntro.tex:1224-1230`; ruling `D8`). -/
theorem isSizeBias_bernoulliHalf :
    IsSizeBias bernoulliHalfMeasure bernoulliHalfRV bernoulliHalfMeasure (fun _ ↦ 1) := by
  refine ⟨ae_of_all _ ?_, ?_, measurable_const.aemeasurable, fun f _ _ ↦ ?_⟩
  · rintro (_ | _)
    · exact le_rfl
    · exact zero_le_one
  · exact ((integrable_dirac enorm_lt_top).smul_measure_nnreal).add_measure
      ((integrable_dirac enorm_lt_top).smul_measure_nnreal)
  · rw [integral_bernoulliHalfMeasure, integral_bernoulliHalfMeasure,
      integral_bernoulliHalfMeasure]
    dsimp only [bernoulliHalfRV]
    ring

/-- Non-vacuity of `IsSizeBias`: existence of a probability space and random variables with
$\mathbb{E}[X] = 1/2$ satisfying `IsSizeBias`
(Definition 3.7 `\label{sbc}`, `SteinIntro.tex:1224-1230`; ruling `D8`). -/
theorem exists_isSizeBias_bernoulli :
    ∃ (P : Measure Bool) (_ : IsProbabilityMeasure P) (X Xs : Bool → ℝ),
      ∫ b, X b ∂P = 1 / 2 ∧ IsSizeBias P X P Xs :=
  ⟨bernoulliHalfMeasure, inferInstance, bernoulliHalfRV, fun _ ↦ 1,
    integral_bernoulliHalfRV, isSizeBias_bernoulliHalf⟩

/-- Uniform probability measure on `Bool × Bool` witnessing `IsSteinPair`
(Definition 3.2, `SteinIntro.tex:952-960`; ruling `D7`). -/
noncomputable def rademacherPairMeasure : Measure (Bool × Bool) :=
  (1 / 4 : ℝ≥0) •
    (Measure.dirac (true, true) + Measure.dirac (true, false) +
      Measure.dirac (false, true) + Measure.dirac (false, false))

instance : IsProbabilityMeasure rademacherPairMeasure where
  measure_univ := by
    rw [rademacherPairMeasure, Measure.coe_nnreal_smul_apply, Measure.coe_add,
      Measure.coe_add, Measure.coe_add, Pi.add_apply, Pi.add_apply, Pi.add_apply,
      measure_univ, measure_univ, measure_univ, measure_univ, ← ENNReal.coe_one,
      ← ENNReal.coe_add, ← ENNReal.coe_add, ← ENNReal.coe_add, ← ENNReal.coe_mul,
      ENNReal.coe_inj, ← NNReal.coe_inj, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_add, NNReal.coe_add, NNReal.coe_add, NNReal.coe_one, NNReal.coe_ofNat]
    norm_num

/-- Rademacher sign map $\mathrm{Bool} \to \{\pm 1\}$
(Definition 3.2, `SteinIntro.tex:952-960`; ruling `D7`). -/
def rademacherVal : Bool → ℝ
  | true => 1
  | false => -1

/-- First independent symmetric Rademacher coordinate
$W : \mathrm{Bool} \times \mathrm{Bool} \to \mathbb{R}$
(Definition 3.2, `SteinIntro.tex:952-960`; ruling `D7`). -/
def rademacherFst (p : Bool × Bool) : ℝ :=
  rademacherVal p.1

/-- Second independent symmetric Rademacher coordinate
$W' : \mathrm{Bool} \times \mathrm{Bool} \to \mathbb{R}$
(Definition 3.2, `SteinIntro.tex:952-960`; ruling `D7`). -/
def rademacherSnd (p : Bool × Bool) : ℝ :=
  rademacherVal p.2

private lemma integrable_rademacherPairMeasure (f : Bool × Bool → ℝ) :
    Integrable f rademacherPairMeasure :=
  ((((integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)).add_measure
    (integrable_dirac enorm_lt_top)).add_measure
    (integrable_dirac enorm_lt_top)).smul_measure_nnreal

private lemma integral_rademacherPairMeasure (g : Bool × Bool → ℝ) :
    ∫ p, g p ∂rademacherPairMeasure =
      (1 / 4 : ℝ) *
        (g (true, true) + g (true, false) + g (false, true) + g (false, false)) := by
  have hd (p : Bool × Bool) : Integrable g (Measure.dirac p) := integrable_dirac enorm_lt_top
  rw [rademacherPairMeasure, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    integral_add_measure (((hd _).add_measure (hd _)).add_measure (hd _)) (hd _),
    integral_add_measure ((hd _).add_measure (hd _)) (hd _),
    integral_add_measure (hd _) (hd _),
    integral_dirac, integral_dirac, integral_dirac, integral_dirac]

private lemma integral_sq_rademacherFst :
    ∫ p, rademacherFst p ^ 2 ∂rademacherPairMeasure = 1 := by
  rw [integral_rademacherPairMeasure]
  dsimp only [rademacherFst, rademacherVal]
  norm_num

private lemma map_swap_rademacherPairMeasure :
    rademacherPairMeasure.map Prod.swap = rademacherPairMeasure := by
  rw [rademacherPairMeasure, Measure.map_smul _ measurable_swap.aemeasurable,
    Measure.map_add _ _ measurable_swap, Measure.map_add _ _ measurable_swap,
    Measure.map_add _ _ measurable_swap, Measure.map_dirac' measurable_swap,
    Measure.map_dirac' measurable_swap, Measure.map_dirac' measurable_swap,
    Measure.map_dirac' measurable_swap]
  dsimp only [Prod.swap]
  rw [add_right_comm (Measure.dirac (true, true)) (Measure.dirac (false, true))
    (Measure.dirac (true, false))]

/-- Concrete satisfaction of `IsSteinPair` for independent symmetric Rademacher variables with
$a = 1$ (Definition 3.2, `SteinIntro.tex:952-960`; ruling `D7`). -/
theorem isSteinPair_rademacher :
    IsSteinPair rademacherPairMeasure 1 rademacherFst rademacherSnd := by
  refine ⟨?_, zero_lt_one, le_rfl, Measurable.of_discrete,
    integrable_rademacherPairMeasure rademacherFst, ?_⟩
  · refine ⟨Measurable.of_discrete.aemeasurable, Measurable.of_discrete.aemeasurable, ?_⟩
    have hcomp :
        (fun p : Bool × Bool ↦ (rademacherSnd p, rademacherFst p)) =
          (fun p : Bool × Bool ↦ (rademacherFst p, rademacherSnd p)) ∘ Prod.swap :=
      funext fun ⟨_, _⟩ ↦ rfl
    rw [hcomp, ← Measure.map_map Measurable.of_discrete measurable_swap,
      map_swap_rademacherPairMeasure]
  · have hm : MeasurableSpace.comap rademacherFst inferInstance ≤
        (inferInstance : MeasurableSpace (Bool × Bool)) :=
      (Measurable.of_discrete : Measurable rademacherFst).comap_le
    have hce :
        (fun _ : Bool × Bool ↦ (0 : ℝ)) =ᵐ[rademacherPairMeasure]
          rademacherPairMeasure[rademacherSnd |
            MeasurableSpace.comap rademacherFst inferInstance] := by
      refine ae_eq_condExp_of_forall_setIntegral_eq hm
        (integrable_rademacherPairMeasure rademacherSnd)
        (fun _ _ _ ↦ integrableOn_zero) (fun s hs _ ↦ ?_) aestronglyMeasurable_const
      rcases hs with ⟨t, _, rfl⟩
      rw [integral_zero, ← integral_indicator MeasurableSet.of_discrete,
        integral_rademacherPairMeasure]
      have hpair (b : Bool) :
          (rademacherFst ⁻¹' t).indicator rademacherSnd (b, true) +
            (rademacherFst ⁻¹' t).indicator rademacherSnd (b, false) = 0 := by
        by_cases hb : rademacherVal b ∈ t
        · have hbt : (b, true) ∈ rademacherFst ⁻¹' t := hb
          have hbf : (b, false) ∈ rademacherFst ⁻¹' t := hb
          rw [Set.indicator_of_mem hbt rademacherSnd,
            Set.indicator_of_mem hbf rademacherSnd]
          dsimp only [rademacherSnd, rademacherVal]
          norm_num
        · have hbt : (b, true) ∉ rademacherFst ⁻¹' t := hb
          have hbf : (b, false) ∉ rademacherFst ⁻¹' t := hb
          rw [Set.indicator_of_notMem hbt rademacherSnd,
            Set.indicator_of_notMem hbf rademacherSnd, add_zero]
      rw [add_assoc
        ((rademacherFst ⁻¹' t).indicator rademacherSnd (true, true) +
          (rademacherFst ⁻¹' t).indicator rademacherSnd (true, false))
        ((rademacherFst ⁻¹' t).indicator rademacherSnd (false, true))
        ((rademacherFst ⁻¹' t).indicator rademacherSnd (false, false)),
        hpair true, hpair false, add_zero, mul_zero]
    have hzero : (fun ω : Bool × Bool ↦ (1 - (1 : ℝ)) * rademacherFst ω) =
        fun _ ↦ (0 : ℝ) :=
      funext fun _ ↦ by rw [sub_self, zero_mul]
    rw [hzero]
    exact hce.symm

/-- Non-vacuity of `IsSteinPair`: existence of a probability space and random variables with
$\mathbb{E}[W^2] = 1$ satisfying `IsSteinPair` at $a = 1$
(Definition 3.2, `SteinIntro.tex:952-960`; ruling `D7`). -/
theorem exists_isSteinPair_rademacher :
    ∃ (P : Measure (Bool × Bool)) (_ : IsProbabilityMeasure P) (W W' : Bool × Bool → ℝ),
      ∫ p, W p ^ 2 ∂P = 1 ∧ IsSteinPair P 1 W W' :=
  ⟨rademacherPairMeasure, inferInstance, rademacherFst, rademacherSnd,
    integral_sq_rademacherFst, isSteinPair_rademacher⟩

/-- Uniform probability measure on $[-1, 1]$ witnessing `IsZeroBias` for symmetric Rademacher $W$
(Definition 3.10, `SteinIntro.tex:1442-1449`; rulings `D5`, `D9`). -/
noncomputable def uniformIccNegOneOne : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1)

instance : IsProbabilityMeasure uniformIccNegOneOne where
  measure_univ := by
    rw [uniformIccNegOneOne, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    have htwo : ENNReal.ofReal ((1 : ℝ) - -1) = (2 : ℝ≥0∞) := by
      rw [show (1 : ℝ) - -1 = 2 by norm_num]
      simp only [ENNReal.ofReal_ofNat]
    rw [htwo]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

private lemma integrable_bernoulliHalfMeasure (g : Bool → ℝ) :
    Integrable g bernoulliHalfMeasure :=
  ((integrable_dirac enorm_lt_top).smul_measure_nnreal).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure_nnreal)

private lemma memLp_two_rademacherVal : MemLp rademacherVal 2 bernoulliHalfMeasure :=
  (memLp_two_iff_integrable_sq
    (Measurable.of_discrete : Measurable rademacherVal).aestronglyMeasurable).mpr
    (integrable_bernoulliHalfMeasure _)

private lemma integral_rademacherVal :
    ∫ b, rademacherVal b ∂bernoulliHalfMeasure = 0 := by
  rw [integral_bernoulliHalfMeasure]
  dsimp only [rademacherVal]
  norm_num

private lemma variance_rademacherVal :
    ProbabilityTheory.variance rademacherVal bernoulliHalfMeasure = 1 := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (Measurable.of_discrete : Measurable rademacherVal).aemeasurable integral_rademacherVal,
    integral_bernoulliHalfMeasure]
  dsimp only [rademacherVal]
  norm_num

/-- Concrete satisfaction of `IsZeroBias` for symmetric Rademacher $W \in \{\pm 1\}$ and
$W^z \sim \mathrm{Uniform}[-1, 1]$
(Definition 3.10, `SteinIntro.tex:1442-1449`; `ISSUE-3.10`, rulings `D5`, `D9`). -/
theorem isZeroBias_rademacher_uniform :
    IsZeroBias bernoulliHalfMeasure rademacherVal uniformIccNegOneOne id := by
  refine ⟨memLp_two_rademacherVal, integral_rademacherVal, measurable_id.aemeasurable,
    fun f hf _ _ ↦ ?_⟩
  rw [variance_rademacherVal, one_mul, integral_bernoulliHalfMeasure]
  dsimp only [rademacherVal, id_eq]
  rw [uniformIccNegOneOne, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_ofNat]
  rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (-1 : ℝ)) (b := 1)),
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    (hf (-1) 1).integral_deriv_eq_sub, inv_eq_one_div (2 : ℝ)]
  ring

/-- Non-vacuity of `IsZeroBias`: existence of probability spaces and random variables with
$\operatorname{Var}(W) = 1$ satisfying `IsZeroBias`
(Definition 3.10, `SteinIntro.tex:1442-1449`; `ISSUE-3.10`, rulings `D5`, `D9`). -/
theorem exists_isZeroBias_rademacher :
    ∃ (Ω Ω' : Type) (_ : MeasurableSpace Ω) (_ : MeasurableSpace Ω')
      (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (W : Ω → ℝ) (Wz : Ω' → ℝ),
      IsZeroBias P W P' Wz ∧ ProbabilityTheory.variance W P = 1 :=
  ⟨Bool, ℝ, inferInstance, inferInstance, bernoulliHalfMeasure, inferInstance,
    uniformIccNegOneOne, inferInstance, rademacherVal, id,
    isZeroBias_rademacher_uniform, variance_rademacherVal⟩

end SteinMethod
