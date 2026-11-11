/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Geometric
import Formalization.Metrics.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Geometric Stein Characterization, Stein Equation, and TV Bound (`Formalization.Geometric.Basic`)

Core theory of Section 6.1 (*Main theorem*, `SteinIntro.tex:3220-3277`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* Point-mass, probability-measure, moment, and tail formulas for `geomLaw` ($\mathrm{Ge}^0(p)$ on
  $\{0, 1, \dots\}$) and `posGeomLaw` ($\mathrm{Ge}(p)$ on $\{1, 2, \dots\}$).
* **Lemma 6.1(1)** (`\label{lem173}`, `SteinIntro.tex:3229-3236`):
  `integral_geomSteinOp_geomLaw` and `integral_geomSteinOp_eq_zero_of_map_eq`.
* **Lemma 6.1(2)** (`\label{lem173}`, `SteinIntro.tex:3229-3241`):
  `map_eq_geomLaw_of_integral_geomSteinOp_eq_zero`.
* **Lemma 6.2** (`\label{lem174}`, `SteinIntro.tex:3243-3249, 3264-3274`):
  `geomSteinSol_zero`, `fwdDiff_geomSteinSol`, `geomSteinSol_steinEq`,
  `eq_geomSteinSol_of_steinEq`, `fwdDiff_geomSteinSol_bounds`, and
  `geomSteinSol_mem_geomSteinClass`.
* **Theorem 6.3** (`\label{thm178}`, `SteinIntro.tex:3251-3258`): `tvDist_geomLaw_le`.
* Non-vacuity witness `isDiscreteEquilibrium_geomLaw_self` showing $\mathrm{Ge}^0(p)$ is its own
  discrete equilibrium distribution.
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-! ### Non-vacuity, point masses, moments, and tails of `geomLaw` and `posGeomLaw` -/

private lemma projIcc_geom_ne_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Set.projIcc 0 1 zero_le_one p ≠ 0 := by
  intro h
  have hval : ((Set.projIcc 0 1 zero_le_one p : unitInterval) : ℝ) = 0 := by rw [h]; rfl
  rw [Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩] at hval
  exact hp0.ne' hval

private lemma norm_one_sub_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ‖1 - p‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
  linarith

/-- `geomLaw p` is a probability measure on `ℕ` (Section 6.1, `SteinIntro.tex:3223-3225`). -/
instance instIsProbabilityMeasureGeomLaw (p : ℝ) : IsProbabilityMeasure (geomLaw p) := by
  unfold geomLaw
  infer_instance

/-- `posGeomLaw p` is a probability measure on `ℕ` (Section 6 opening,
`SteinIntro.tex:2884, 3194`). -/
instance instIsProbabilityMeasurePosGeomLaw (p : ℝ) : IsProbabilityMeasure (posGeomLaw p) := by
  unfold posGeomLaw
  exact (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance

/-- Singleton mass of `geomLaw p` ($\mathrm{Ge}^0(p)$): $\mathbb{P}(N = k) = (1 - p)^k p$ for
$0 < p \le 1$ (Section 6.1, `SteinIntro.tex:3223-3225`). -/
theorem geomLaw_singleton {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    geomLaw p {k} = ENNReal.ofReal ((1 - p) ^ k * p) := by
  rw [geomLaw, ProbabilityTheory.geometricMeasure_singleton (projIcc_geom_ne_zero hp0 hp1) k,
    Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩]

/-- Real singleton mass of `geomLaw p`: $(\mathrm{geomLaw}\,p).\mathrm{real}\,\{k\} = (1 - p)^k p$
for $0 < p \le 1$ (Section 6.1, `SteinIntro.tex:3223-3225`). -/
theorem geomLaw_real_singleton {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    (geomLaw p).real {k} = (1 - p) ^ k * p := by
  rw [geomLaw, ProbabilityTheory.geometricMeasure_real_singleton (projIcc_geom_ne_zero hp0 hp1) k,
    Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩]

/-- `posGeomLaw p` ($\mathrm{Ge}(p)$ on $\{1, 2, \dots\}$) puts zero mass at `0`
(`SteinIntro.tex:2884, 3194`). -/
@[simp]
theorem posGeomLaw_singleton_zero (p : ℝ) : posGeomLaw p {0} = 0 := by
  rw [posGeomLaw, Measure.map_apply .of_discrete .of_discrete]
  have hpre : (· + 1 : ℕ → ℕ) ⁻¹' {0} = ∅ := by
    ext k
    simp
  rw [hpre, measure_empty]

/-- Real mass of `posGeomLaw p` at `0` is zero (`SteinIntro.tex:2884, 3194`). -/
@[simp]
theorem posGeomLaw_real_singleton_zero (p : ℝ) : (posGeomLaw p).real {0} = 0 := by
  rw [measureReal_def, posGeomLaw_singleton_zero, ENNReal.toReal_zero]

/-- Singleton mass of `posGeomLaw p` ($\mathrm{Ge}(p)$): $\mathbb{P}(X = k) = (1 - p)^{k - 1} p$
for $0 < p \le 1$ and $k \ge 1$ (`SteinIntro.tex:2884, 3194`). -/
theorem posGeomLaw_singleton_of_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    posGeomLaw p {k} = ENNReal.ofReal ((1 - p) ^ (k - 1) * p) := by
  rw [posGeomLaw, Measure.map_apply .of_discrete .of_discrete]
  have hpre : (· + 1 : ℕ → ℕ) ⁻¹' {k} = {k - 1} := by
    ext j
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  rw [hpre, geomLaw_singleton hp0 hp1 (k - 1)]

/-- Real singleton mass of `posGeomLaw p`: $\mathbb{P}(X = k) = (1 - p)^{k - 1} p$ for
$0 < p \le 1$ and $k \ge 1$ (`SteinIntro.tex:2884, 3194`). -/
theorem posGeomLaw_real_singleton_of_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {k : ℕ}
    (hk : 1 ≤ k) :
    (posGeomLaw p).real {k} = (1 - p) ^ (k - 1) * p := by
  have hnn : 0 ≤ (1 - p) ^ (k - 1) * p :=
    mul_nonneg (pow_nonneg (sub_nonneg.mpr hp1) _) hp0.le
  rw [measureReal_def, posGeomLaw_singleton_of_pos hp0 hp1 hk, ENNReal.toReal_ofReal hnn]

/-- Every polynomial moment $k \mapsto k^m$ is integrable under `geomLaw p` for $0 < p \le 1$
(Section 6.1, `SteinIntro.tex:3223-3225`). -/
theorem integrable_pow_geomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (m : ℕ) :
    Integrable (fun k : ℕ ↦ (k : ℝ) ^ m) (geomLaw p) := by
  rw [geomLaw, ProbabilityTheory.integrable_geometricMeasure_iff (projIcc_geom_ne_zero hp0 hp1)]
  simp only [Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩]
  have hsum := (summable_pow_mul_geometric_of_norm_lt_one m
    (norm_one_sub_lt_one hp0 hp1)).mul_right p
  refine hsum.congr fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) m)]
  ring

/-- `k ↦ (k : ℝ)` is integrable under `geomLaw p` for $0 < p \le 1$
(`SteinIntro.tex:3223-3225`). -/
theorem integrable_natCast_geomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Integrable (fun k : ℕ ↦ (k : ℝ)) (geomLaw p) := by
  simpa only [pow_one] using integrable_pow_geomLaw hp0 hp1 1

/-- `k ↦ (k : ℝ)` belongs to $L^2(\mathrm{geomLaw}\,p)$ for $0 < p \le 1$
(`SteinIntro.tex:3313`). -/
theorem memLp_natCast_two_geomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    MemLp (fun k : ℕ ↦ (k : ℝ)) 2 (geomLaw p) :=
  (memLp_two_iff_integrable_sq Measurable.of_discrete.aestronglyMeasurable).mpr
    (integrable_pow_geomLaw hp0 hp1 2)

/-- Expected value of $\mathrm{Ge}^0(p)$: $\mathbb{E}[N] = (1 - p) / p$ for $0 < p \le 1$
(Section 6.1, `SteinIntro.tex:3223-3225, 3253`). -/
theorem integral_natCast_geomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫ k, (k : ℝ) ∂(geomLaw p) = (1 - p) / p := by
  rw [geomLaw, ProbabilityTheory.integral_geometricMeasure (projIcc_geom_ne_zero hp0 hp1)]
  simp only [Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩, smul_eq_mul]
  have hcongr : (fun n : ℕ ↦ (1 - p) ^ n * p * (n : ℝ)) =
      fun n : ℕ ↦ p * ((n : ℝ) * (1 - p) ^ n) := funext fun _ ↦ by ring
  rw [hcongr, tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one (norm_one_sub_lt_one hp0 hp1)]
  have hsub : 1 - (1 - p) = p := by ring
  rw [hsub, sq, ← mul_div_assoc]
  exact mul_div_mul_left (1 - p) p hp0.ne'

/-- `k ↦ (k : ℝ)` is integrable under `posGeomLaw p` for $0 < p \le 1$
(`SteinIntro.tex:2884, 3194`). -/
theorem integrable_natCast_posGeomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Integrable (fun k : ℕ ↦ (k : ℝ)) (posGeomLaw p) := by
  rw [posGeomLaw, integrable_map_measure Measurable.of_discrete.aestronglyMeasurable
    Measurable.of_discrete.aemeasurable]
  have heq : ((fun k : ℕ ↦ (k : ℝ)) ∘ (· + 1)) = fun k : ℕ ↦ (k : ℝ) + 1 := by
    ext k
    simp [Nat.cast_add]
  rw [heq]
  exact (integrable_natCast_geomLaw hp0 hp1).add (integrable_const 1)

/-- Expected value of $\mathrm{Ge}(p)$ on $\{1, 2, \dots\}$: $\mathbb{E}[X] = 1 / p$ for
$0 < p \le 1$ (`SteinIntro.tex:2884, 3194`). -/
theorem integral_natCast_posGeomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∫ k, (k : ℝ) ∂(posGeomLaw p) = 1 / p := by
  rw [posGeomLaw, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  simp_rw [Nat.cast_add, Nat.cast_one]
  rw [integral_add (integrable_natCast_geomLaw hp0 hp1) (integrable_const 1),
    integral_natCast_geomLaw hp0 hp1, integral_const, probReal_univ, one_smul]
  field_simp [hp0.ne']
  ring

/-- Tail probability of `geomLaw p`: $\mathbb{P}(N > k) = (1 - p)^{k + 1}$ for $0 < p \le 1$
(`SteinIntro.tex:3223-3225, 3304-3310`). -/
theorem measureReal_Ioi_geomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (k : ℕ) :
    (geomLaw p).real (Set.Ioi k) = (1 - p) ^ (k + 1) := by
  rw [← integral_indicator_one .of_discrete, geomLaw,
    ProbabilityTheory.integral_geometricMeasure (projIcc_geom_ne_zero hp0 hp1)]
  simp only [Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩, smul_eq_mul]
  let u : ℕ → ℝ := fun n ↦ (1 - p) ^ n * p * (Set.Ioi k).indicator 1 n
  have hu_shift : ∀ j : ℕ, u (k + 1 + j) = (1 - p) ^ (k + 1) * ((1 - p) ^ j * p) := fun j ↦ by
    have hmem : k + 1 + j ∈ Set.Ioi k := by
      simp only [Set.mem_Ioi]
      omega
    simp only [u, Set.indicator_of_mem hmem, Pi.one_apply, mul_one, pow_add]
    ring
  have hu_sum_shift : Summable (fun j : ℕ ↦ u (k + 1 + j)) := by
    simp_rw [hu_shift]
    exact ((summable_geometric_of_norm_lt_one (norm_one_sub_lt_one hp0 hp1)).mul_right p).mul_left
      ((1 - p) ^ (k + 1))
  have hu_sum : Summable u := (summable_nat_add_iff (k + 1)).mp
    (by simpa only [Nat.add_comm (k + 1)] using hu_sum_shift)
  have hsplit := hu_sum.sum_add_tsum_nat_add (k + 1)
  have hfin : ∑ i ∈ Finset.range (k + 1), u i = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hnot : i ∉ Set.Ioi k := by
      simp only [Finset.mem_range, Set.mem_Ioi] at hi ⊢
      omega
    simp [u, Set.indicator_of_notMem hnot]
  rw [← hsplit, hfin, zero_add]
  have hshift_eq : (fun i : ℕ ↦ u (i + (k + 1))) =
      fun j : ℕ ↦ (1 - p) ^ (k + 1) * ((1 - p) ^ j * p) := by
    ext j
    rw [Nat.add_comm j (k + 1), hu_shift j]
  rw [hshift_eq, tsum_mul_left, tsum_mul_right,
    tsum_geometric_of_norm_lt_one (norm_one_sub_lt_one hp0 hp1)]
  have hsub : 1 - (1 - p) = p := by ring
  rw [hsub, inv_mul_cancel₀ hp0.ne', mul_one]

/-! ### Lemma 6.1: Characterizing Operator of $\mathrm{Ge}^0(p)$ -/

private lemma geomSteinOp_eq (p : ℝ) (f : ℕ → ℝ) (k : ℕ) :
    geomSteinOp p f k = (1 - p) * f (k + 1) - f k + p * f 0 := by
  simp only [geomSteinOp, fwdDiff]
  ring

private lemma integral_geomLaw_shift_relation {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : Integrable f (geomLaw p))
    (hf_shift : Integrable (fun k : ℕ ↦ f (k + 1)) (geomLaw p)) :
    ∫ k, f k ∂(geomLaw p) = p * f 0 + (1 - p) * ∫ k, f (k + 1) ∂(geomLaw p) := by
  have hp_ne := projIcc_geom_ne_zero hp0 hp1
  have h1 := ProbabilityTheory.hasSum_integral_geometricMeasure hp_ne hf
  have h2 := ProbabilityTheory.hasSum_integral_geometricMeasure hp_ne hf_shift
  rw [geomLaw, Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩]
  simp only [Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩, smul_eq_mul] at h1 h2
  let g : ℕ → ℝ := fun n ↦ (1 - p) ^ n * p * f n
  have h1' : HasSum g (∫ n, f n ∂ProbabilityTheory.geometricMeasure ⟨p, hp0.le, hp1⟩) := h1
  have h2_mul := h2.mul_left (1 - p)
  have hsucc : (fun n : ℕ ↦ (1 - p) * ((1 - p) ^ n * p * f (n + 1))) =
      fun n : ℕ ↦ g (n + 1) := funext fun n ↦ by
    dsimp only [g]
    rw [pow_succ']
    ring
  rw [hsucc] at h2_mul
  have hzero := h2_mul.zero_add
  have hg0 : g 0 = p * f 0 := by simp [g]
  rw [hg0] at hzero
  exact h1'.unique hzero

/-- **Lemma 6.1(1)** (measure level, `\label{lem173}`, `SteinIntro.tex:3229-3236`): for
$0 < p \le 1$ and any bounded $f : \mathbb{N} \to \mathbb{R}$,
$\int \mathcal{A}f(k)\,\mathrm{d}(\mathrm{geomLaw}\,p) = 0$. -/
theorem integral_geomSteinOp_geomLaw {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : ∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) :
    ∫ k, geomSteinOp p f k ∂(geomLaw p) = 0 := by
  obtain ⟨C, hC⟩ := hf
  have hf_int : Integrable f (geomLaw p) :=
    ⟨.of_discrete, .of_bounded (Filter.Eventually.of_forall fun k ↦ by
      rw [Real.norm_eq_abs]; exact hC k)⟩
  have hf_shift : Integrable (fun k : ℕ ↦ f (k + 1)) (geomLaw p) :=
    ⟨.of_discrete, .of_bounded (Filter.Eventually.of_forall fun k ↦ by
      rw [Real.norm_eq_abs]; exact hC (k + 1))⟩
  simp_rw [geomSteinOp_eq]
  rw [integral_add ((hf_shift.const_mul (1 - p)).sub' hf_int) (integrable_const (p * f 0)),
    integral_sub (hf_shift.const_mul (1 - p)) hf_int, integral_const_mul, integral_const,
    probReal_univ, one_smul, integral_geomLaw_shift_relation hp0 hp1 hf_int hf_shift]
  ring

/-- **Lemma 6.1(1)** (random-variable level, `\label{lem173}`, `SteinIntro.tex:3229-3236`): if
$Z \sim \mathrm{Ge}^0(p)$ with $0 < p \le 1$, then $\mathbb{E}[\mathcal{A}f(Z)] = 0$ for every
bounded $f : \mathbb{N} \to \mathbb{R}$. -/
theorem integral_geomSteinOp_eq_zero_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {Z : Ω → ℕ} (hZ : AEMeasurable Z P)
    (hlaw : P.map Z = geomLaw p)
    {f : ℕ → ℝ} (hf : ∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) :
    ∫ ω, geomSteinOp p f (Z ω) ∂P = 0 := by
  rw [← integral_map hZ .of_discrete, hlaw]
  exact integral_geomSteinOp_geomLaw hp0 hp1 hf

/-- **Lemma 6.1(2)** (`\label{lem173}`, `SteinIntro.tex:3229-3241`; `ISSUE-6.1`): for
$0 < p \le 1$, if $W : \Omega \to \mathbb{N}$ satisfies $\mathbb{E}[\mathcal{A}f(W)] = 0$ for all
bounded $f : \mathbb{N} \to \mathbb{R}$, then $W \sim \mathrm{Ge}^0(p)$. -/
theorem map_eq_geomLaw_of_integral_geomSteinOp_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hStein : ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, geomSteinOp p f (W ω) ∂P = 0) :
    P.map W = geomLaw p := by
  have _ : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  have hbdd_ind : ∀ j : ℕ, ∃ C : ℝ, ∀ k : ℕ, |({j} : Set ℕ).indicator (1 : ℕ → ℝ) k| ≤ C := by
    intro j
    refine ⟨1, fun k ↦ ?_⟩
    by_cases hk : k ∈ ({j} : Set ℕ)
    · rw [Set.indicator_of_mem hk, Pi.one_apply, abs_one]
    · rw [Set.indicator_of_notMem hk, abs_zero]
      exact zero_le_one
  have hind_int : ∀ j : ℕ, Integrable (({j} : Set ℕ).indicator (1 : ℕ → ℝ)) (P.map W) := fun j ↦
    (integrable_const (1 : ℝ)).indicator .of_discrete
  have h_zero : (P.map W).real {0} = p := by
    have hint : ∫ k, geomSteinOp p (({0} : Set ℕ).indicator 1) k ∂(P.map W) = 0 := by
      rw [integral_map hW .of_discrete]
      exact hStein _ (hbdd_ind 0)
    have hop : (fun k : ℕ ↦ geomSteinOp p (({0} : Set ℕ).indicator 1) k) =
        fun k : ℕ ↦ p - ({0} : Set ℕ).indicator (1 : ℕ → ℝ) k := by
      ext k
      rw [geomSteinOp_eq]
      have h1 : (({0} : Set ℕ).indicator (1 : ℕ → ℝ) (k + 1)) = 0 :=
        Set.indicator_of_notMem (by simp) _
      have h0 : (({0} : Set ℕ).indicator (1 : ℕ → ℝ) 0) = 1 :=
        Set.indicator_of_mem (Set.mem_singleton 0) _
      rw [h1, h0]
      ring
    rw [hop, integral_sub (integrable_const p) (hind_int 0),
      integral_const, probReal_univ, one_smul, integral_indicator_one .of_discrete] at hint
    linarith
  have h_rec : ∀ j : ℕ, (P.map W).real {j + 1} = (1 - p) * (P.map W).real {j} := by
    intro j
    have hint : ∫ k, geomSteinOp p (({j + 1} : Set ℕ).indicator 1) k ∂(P.map W) = 0 := by
      rw [integral_map hW .of_discrete]
      exact hStein _ (hbdd_ind (j + 1))
    have hop : (fun k : ℕ ↦ geomSteinOp p (({j + 1} : Set ℕ).indicator 1) k) =
        fun k : ℕ ↦ (1 - p) * ({j} : Set ℕ).indicator (1 : ℕ → ℝ) k -
          ({j + 1} : Set ℕ).indicator (1 : ℕ → ℝ) k := by
      ext k
      rw [geomSteinOp_eq]
      have h0 : (({j + 1} : Set ℕ).indicator (1 : ℕ → ℝ) 0) = 0 :=
        Set.indicator_of_notMem (by simp) _
      have hshift : (({j + 1} : Set ℕ).indicator (1 : ℕ → ℝ) (k + 1)) =
          ({j} : Set ℕ).indicator (1 : ℕ → ℝ) k := by
        by_cases hk : k = j
        · subst hk
          simp
        · have hk1 : k + 1 ≠ j + 1 := fun h ↦ hk (Nat.add_right_cancel h)
          rw [Set.indicator_of_notMem (by simpa using hk1),
            Set.indicator_of_notMem (by simpa using hk)]
      rw [h0, hshift]
      ring
    rw [hop, integral_sub ((hind_int j).const_mul (1 - p)) (hind_int (j + 1)),
      integral_const_mul, integral_indicator_one .of_discrete,
      integral_indicator_one .of_discrete] at hint
    linarith
  refine Measure.ext_of_measureReal_singleton fun k ↦ ?_
  rw [geomLaw_real_singleton hp0 hp1 k]
  induction k with
  | zero =>
      rw [pow_zero, one_mul, h_zero]
  | succ k ih =>
      rw [h_rec k, ih, pow_succ']
      ring

/-! ### Lemma 6.2: Solution and Bounds for the Geometric Stein Equation -/

private noncomputable def geomTailSum (p : ℝ) (A : Set ℕ) (k : ℕ) : ℝ :=
  ∑' i : ℕ, (A ∩ Set.Ici k).indicator (fun i ↦ (1 - p) ^ (i - k)) i

private lemma geomSteinSol_eq_sub_geomTailSum (p : ℝ) (A : Set ℕ) (k : ℕ) :
    geomSteinSol p A k = geomTailSum p A 0 - geomTailSum p A k := by
  have hIci0 : A ∩ Set.Ici 0 = A := Set.inter_eq_left.mpr fun _ _ ↦ Nat.zero_le _
  simp only [geomSteinSol, geomTailSum, hIci0, Nat.sub_zero]

private lemma summable_geom_shift {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ) (k : ℕ) :
    Summable (fun j : ℕ ↦ {m : ℕ | k + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j) := by
  refine Summable.of_nonneg_of_le (fun j ↦ ?_) (fun j ↦ ?_)
    (summable_geometric_of_norm_lt_one (norm_one_sub_lt_one hp0 hp1))
  · exact Set.indicator_nonneg (fun _ _ ↦ pow_nonneg (sub_nonneg.mpr hp1) _) j
  · by_cases hj : j ∈ {m : ℕ | k + m ∈ A}
    · rw [Set.indicator_of_mem hj]
    · rw [Set.indicator_of_notMem hj]
      exact pow_nonneg (sub_nonneg.mpr hp1) j

private lemma geomTailSum_eq_shift_tsum {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (A : Set ℕ) (k : ℕ) :
    geomTailSum p A k =
      ∑' j : ℕ, {m : ℕ | k + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j := by
  let u : ℕ → ℝ := (A ∩ Set.Ici k).indicator (fun i ↦ (1 - p) ^ (i - k))
  have hu_add : (fun j : ℕ ↦ u (j + k)) =
      fun j : ℕ ↦ {m : ℕ | k + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j := by
    ext j
    have hmem : j + k ∈ A ∩ Set.Ici k ↔ k + j ∈ A := by
      simp only [Set.mem_inter_iff, Set.mem_Ici, Nat.add_comm j k]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, Nat.le_add_right k j⟩⟩
    by_cases hj : k + j ∈ A
    · have hj1 : j + k ∈ A ∩ Set.Ici k := hmem.mpr hj
      have hj2 : j ∈ {m : ℕ | k + m ∈ A} := hj
      dsimp only [u]
      rw [Set.indicator_of_mem hj1, Set.indicator_of_mem hj2, Nat.add_sub_cancel]
    · have hj1 : j + k ∉ A ∩ Set.Ici k := mt hmem.mp hj
      have hj2 : j ∉ {m : ℕ | k + m ∈ A} := hj
      dsimp only [u]
      rw [Set.indicator_of_notMem hj1, Set.indicator_of_notMem hj2]
  have hu_sum : Summable u :=
    (summable_nat_add_iff k).mp (hu_add.symm ▸ summable_geom_shift hp0 hp1 A k)
  have hsplit := hu_sum.sum_add_tsum_nat_add k
  have hfin : ∑ i ∈ Finset.range k, u i = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hnot : i ∉ A ∩ Set.Ici k := fun h ↦ by
      simp only [Finset.mem_range] at hi
      exact not_le_of_gt hi h.2
    exact Set.indicator_of_notMem hnot _
  rw [geomTailSum, ← hsplit, hfin, zero_add, hu_add]

private lemma geomTailSum_rec {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ) (k : ℕ) :
    geomTailSum p A k = A.indicator 1 k + (1 - p) * geomTailSum p A (k + 1) := by
  rw [geomTailSum_eq_shift_tsum hp0 hp1 A k, geomTailSum_eq_shift_tsum hp0 hp1 A (k + 1),
    (summable_geom_shift hp0 hp1 A k).tsum_eq_zero_add]
  have h0 : {m : ℕ | k + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) 0 = A.indicator 1 k := by
    by_cases hk : k ∈ A
    · have hk0 : (0 : ℕ) ∈ {m : ℕ | k + m ∈ A} := hk
      rw [Set.indicator_of_mem hk0, Set.indicator_of_mem hk, pow_zero, Pi.one_apply]
    · have hk0 : (0 : ℕ) ∉ {m : ℕ | k + m ∈ A} := hk
      rw [Set.indicator_of_notMem hk0, Set.indicator_of_notMem hk]
  rw [h0, ← tsum_mul_left]
  congr 2 with j
  have hmem : k + (j + 1) ∈ A ↔ (k + 1) + j ∈ A := by
    rw [show k + (j + 1) = (k + 1) + j by omega]
  by_cases hj : (k + 1) + j ∈ A
  · have hj1 : j + 1 ∈ {m : ℕ | k + m ∈ A} := hmem.mpr hj
    have hj2 : j ∈ {m : ℕ | (k + 1) + m ∈ A} := hj
    rw [Set.indicator_of_mem hj1, Set.indicator_of_mem hj2, pow_succ']
  · have hj1 : j + 1 ∉ {m : ℕ | k + m ∈ A} := mt hmem.mp hj
    have hj2 : j ∉ {m : ℕ | (k + 1) + m ∈ A} := hj
    rw [Set.indicator_of_notMem hj1, Set.indicator_of_notMem hj2, mul_zero]

private lemma mul_geomTailSum_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ) :
    p * geomTailSum p A 0 = (geomLaw p).real A := by
  rw [← integral_indicator_one .of_discrete, geomLaw,
    ProbabilityTheory.integral_geometricMeasure (projIcc_geom_ne_zero hp0 hp1)]
  simp only [Set.projIcc_of_mem zero_le_one ⟨hp0.le, hp1⟩, smul_eq_mul,
    geomTailSum_eq_shift_tsum hp0 hp1 A 0, zero_add]
  rw [← tsum_mul_left]
  congr 1 with i
  by_cases hi : i ∈ A
  · have hi' : i ∈ {m : ℕ | m ∈ A} := hi
    rw [Set.indicator_of_mem hi', Set.indicator_of_mem hi, Pi.one_apply, mul_one]
    ring
  · have hi' : i ∉ {m : ℕ | m ∈ A} := hi
    rw [Set.indicator_of_notMem hi', Set.indicator_of_notMem hi, mul_zero, mul_zero]

/-- **Lemma 6.2** (boundary condition, `\label{lem174}`, `SteinIntro.tex:3243-3249`):
`geomSteinSol p A 0 = 0`. -/
@[simp]
theorem geomSteinSol_zero (p : ℝ) (A : Set ℕ) : geomSteinSol p A 0 = 0 := by
  rw [geomSteinSol_eq_sub_geomTailSum, sub_self]

/-- **Lemma 6.2** (forward-difference formula, `\label{lem174}`, `SteinIntro.tex:3268-3270`):
$\Delta f_A(k) = \mathbb{I}[k \in A] - p \sum_{i \in A,\, i \ge k + 1} (1 - p)^{i - (k + 1)}$ for
$0 < p \le 1$. -/
theorem fwdDiff_geomSteinSol {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ) (k : ℕ) :
    fwdDiff 1 (geomSteinSol p A) k =
      A.indicator 1 k -
        p * ∑' i : ℕ, (A ∩ Set.Ici (k + 1)).indicator (fun i ↦ (1 - p) ^ (i - (k + 1))) i := by
  rw [fwdDiff, geomSteinSol_eq_sub_geomTailSum, geomSteinSol_eq_sub_geomTailSum]
  change (geomTailSum p A 0 - geomTailSum p A (k + 1)) -
      (geomTailSum p A 0 - geomTailSum p A k) =
    A.indicator 1 k - p * geomTailSum p A (k + 1)
  rw [geomTailSum_rec hp0 hp1 A k]
  ring

/-- **Lemma 6.2** (Stein equation, `\label{lem174}`, `SteinIntro.tex:3245-3247`): for
$0 < p \le 1$, $(1 - p)\Delta f_A(k) - p f_A(k) = \mathbb{I}[k \in A] - \mathrm{Ge}^0(p)(A)$. -/
theorem geomSteinSol_steinEq {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ) (k : ℕ) :
    (1 - p) * fwdDiff 1 (geomSteinSol p A) k - p * geomSteinSol p A k =
      A.indicator 1 k - (geomLaw p).real A := by
  rw [fwdDiff, geomSteinSol_eq_sub_geomTailSum, geomSteinSol_eq_sub_geomTailSum,
    ← mul_geomTailSum_zero hp0 hp1 A, geomTailSum_rec hp0 hp1 A k]
  ring

/-- **Lemma 6.2** (uniqueness, `\label{lem174}`, `SteinIntro.tex:3245-3247, 3264-3267`): for
$0 < p \le 1$, `geomSteinSol p A` is the unique function $g : \mathbb{N} \to \mathbb{R}$ with
$g(0) = 0$ solving $(1 - p)\Delta g(k) - p g(k) = \mathbb{I}[k \in A] - \mathrm{Ge}^0(p)(A)$. -/
theorem eq_geomSteinSol_of_steinEq {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ)
    {g : ℕ → ℝ} (hg0 : g 0 = 0)
    (hg : ∀ k : ℕ,
      (1 - p) * fwdDiff 1 g k - p * g k = A.indicator 1 k - (geomLaw p).real A) :
    g = geomSteinSol p A := by
  let d : ℕ → ℝ := fun k ↦ g k - geomSteinSol p A k
  have hd0 : d 0 = 0 := by simp [d, hg0]
  have hd_rec : ∀ k : ℕ, (1 - p) * d (k + 1) = d k := fun k ↦ by
    have hdiff := sub_eq_zero.mpr ((hg k).trans (geomSteinSol_steinEq hp0 hp1 A k).symm)
    simp only [fwdDiff] at hdiff
    dsimp only [d]
    linarith
  ext k
  suffices hdk : d k = 0 from sub_eq_zero.mp hdk
  rcases eq_or_lt_of_le hp1 with rfl | hp_lt
  · have h := hd_rec k
    simpa using h.symm
  · have hne : 1 - p ≠ 0 := sub_ne_zero.mpr hp_lt.ne'
    induction k with
    | zero => exact hd0
    | succ k ih =>
        have h := hd_rec k
        rw [ih] at h
        exact (mul_eq_zero.mp h).resolve_left hne

/-- **Lemma 6.2** (forward-difference bounds, `\label{lem174}`, `SteinIntro.tex:3248-3249,
3271-3274`; `ISSUE-TYPO-6.2`): $-1 \le \Delta f_A(k) \le 1$ for all $0 < p \le 1$ and
$k \in \mathbb{N}$. -/
theorem fwdDiff_geomSteinSol_bounds {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ) (k : ℕ) :
    -1 ≤ fwdDiff 1 (geomSteinSol p A) k ∧ fwdDiff 1 (geomSteinSol p A) k ≤ 1 := by
  rw [fwdDiff_geomSteinSol hp0 hp1 A k]
  change -1 ≤ A.indicator 1 k - p * geomTailSum p A (k + 1) ∧
    A.indicator 1 k - p * geomTailSum p A (k + 1) ≤ 1
  rw [geomTailSum_eq_shift_tsum hp0 hp1 A (k + 1)]
  have hsum_geom := summable_geometric_of_norm_lt_one (norm_one_sub_lt_one hp0 hp1)
  have hsum_ind := summable_geom_shift hp0 hp1 A (k + 1)
  have htsum_nn : 0 ≤ ∑' j : ℕ, {m : ℕ | (k + 1) + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j :=
    tsum_nonneg fun j ↦ Set.indicator_nonneg (fun _ _ ↦ pow_nonneg (sub_nonneg.mpr hp1) _) j
  have htsum_le : ∑' j : ℕ, {m : ℕ | (k + 1) + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j ≤
      p⁻¹ := by
    calc
      ∑' j : ℕ, {m : ℕ | (k + 1) + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j
        ≤ ∑' j : ℕ, (1 - p) ^ j := by
          refine hsum_ind.tsum_le_tsum (fun j ↦ ?_) hsum_geom
          by_cases hj : j ∈ {m : ℕ | (k + 1) + m ∈ A}
          · rw [Set.indicator_of_mem hj]
          · rw [Set.indicator_of_notMem hj]
            exact pow_nonneg (sub_nonneg.mpr hp1) j
      _ = (1 - (1 - p))⁻¹ := tsum_geometric_of_norm_lt_one (norm_one_sub_lt_one hp0 hp1)
      _ = p⁻¹ := by ring_nf
  have hmul_nn : 0 ≤ p * ∑' j : ℕ,
      {m : ℕ | (k + 1) + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j :=
    mul_nonneg hp0.le htsum_nn
  have hmul_le : p * ∑' j : ℕ,
      {m : ℕ | (k + 1) + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j ≤ 1 := by
    calc
      p * ∑' j : ℕ, {m : ℕ | (k + 1) + m ∈ A}.indicator (fun j ↦ (1 - p) ^ j) j
        ≤ p * p⁻¹ := mul_le_mul_of_nonneg_left htsum_le hp0.le
      _ = 1 := mul_inv_cancel₀ hp0.ne'
  have hind_nn : (0 : ℝ) ≤ A.indicator 1 k :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) k
  have hind_le : A.indicator (1 : ℕ → ℝ) k ≤ 1 := by
    by_cases hk : k ∈ A
    · rw [Set.indicator_of_mem hk, Pi.one_apply]
    · rw [Set.indicator_of_notMem hk]
      exact zero_le_one
  exact ⟨by linarith, by linarith⟩

/-- `geomSteinSol p A` belongs to `geomSteinClass` for $0 < p \le 1$
(Lemma 6.2 & Theorem 6.3, `SteinIntro.tex:3245-3255`). -/
theorem geomSteinSol_mem_geomSteinClass {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (A : Set ℕ) :
    geomSteinSol p A ∈ geomSteinClass :=
  ⟨geomSteinSol_zero p A, fun k ↦ abs_le.mpr (fwdDiff_geomSteinSol_bounds hp0 hp1 A k)⟩

/-! ### Theorem 6.3: Total Variation Bound via `geomSteinClass` -/

/-- **Theorem 6.3** (`\label{thm178}`, `SteinIntro.tex:3251-3258`): for $0 < p \le 1$, any
integer-valued random variable $W : \Omega \to \mathbb{N}$, and $N \sim \mathrm{Ge}^0(p)$,
$d_{\mathrm{TV}}(W, N) \le \sup_{f \in \mathcal{F}} |\mathbb{E}[(1 - p)\Delta f(W) - p f(W)]|$. -/
theorem tvDist_geomLaw_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {W : Ω → ℕ} (hW : AEMeasurable W P)
    {N : Ω' → ℕ} (hN : P'.map N = geomLaw p) :
    tvDist (P.map W) (P'.map N) ≤
      ⨆ f ∈ geomSteinClass,
        ENNReal.ofReal |∫ ω, ((1 - p) * fwdDiff 1 f (W ω) - p * f (W ω)) ∂P| := by
  have _ : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  rw [hN, tvDist_eq_iSup (P.map W) (geomLaw p)]
  refine iSup₂_le fun A _ ↦ ?_
  let f := geomSteinSol p A
  have hf_mem : f ∈ geomSteinClass := geomSteinSol_mem_geomSteinClass hp0 hp1 A
  have hpoint : (fun ω : Ω ↦ (1 - p) * fwdDiff 1 f (W ω) - p * f (W ω)) =
      fun ω : Ω ↦ A.indicator 1 (W ω) - (geomLaw p).real A :=
    funext fun ω ↦ geomSteinSol_steinEq hp0 hp1 A (W ω)
  have hint_ind : Integrable (fun ω : Ω ↦ A.indicator (1 : ℕ → ℝ) (W ω)) P :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable hW).mp
      ((integrable_const (1 : ℝ)).indicator .of_discrete)
  have hint_eq : ∫ ω, ((1 - p) * fwdDiff 1 f (W ω) - p * f (W ω)) ∂P =
      (P.map W).real A - (geomLaw p).real A := by
    rw [hpoint, integral_sub hint_ind (integrable_const ((geomLaw p).real A)),
      ← integral_map hW Measurable.of_discrete.aestronglyMeasurable,
      integral_indicator_one .of_discrete, integral_const, probReal_univ, one_smul]
  rw [← hint_eq]
  exact le_iSup₂_of_le f hf_mem le_rfl

/-! ### Non-vacuity witness for `IsDiscreteEquilibrium` -/

/-- Bounds on $|f(k)|$ for functions with bounded forward difference:
$|f(k)| \le |f(0)| + \max(C, 0) \cdot k$ (`SteinIntro.tex:3285`). -/
theorem abs_le_of_abs_fwdDiff_le {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k : ℕ, |fwdDiff 1 f k| ≤ C) (k : ℕ) :
    |f k| ≤ |f 0| + max C 0 * (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : f (k + 1) = f k + fwdDiff 1 f k := by
        rw [fwdDiff]
        ring
      calc
        |f (k + 1)| = |f k + fwdDiff 1 f k| := by rw [hstep]
        _ ≤ |f k| + |fwdDiff 1 f k| := abs_add_le _ _
        _ ≤ (|f 0| + max C 0 * (k : ℝ)) + max C 0 :=
          add_le_add ih ((hf k).trans (le_max_left C 0))
        _ = |f 0| + max C 0 * ((k + 1 : ℕ) : ℝ) := by
          push_cast
          ring

/-- Non-vacuity witness for `IsDiscreteEquilibrium`: for $0 < p \le 1$, $\mathrm{Ge}^0(p)$ is its
own discrete equilibrium distribution (`SteinIntro.tex:3283-3289, 3304-3310`). -/
theorem isDiscreteEquilibrium_geomLaw_self {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsDiscreteEquilibrium (geomLaw p) p id (geomLaw p) id := by
  refine ⟨hp0, hp1, measurable_id.aemeasurable, integrable_natCast_geomLaw hp0 hp1,
    integral_natCast_geomLaw hp0 hp1, measurable_id.aemeasurable, fun f ⟨C, hf⟩ ↦ ?_⟩
  have hf_int : Integrable f (geomLaw p) := by
    refine ((integrable_const |f 0|).add
        ((integrable_natCast_geomLaw hp0 hp1).const_mul (max C 0))).mono'
      Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun k ↦ ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_of_abs_fwdDiff_le hf k
  have hf_shift : Integrable (fun k : ℕ ↦ f (k + 1)) (geomLaw p) := by
    refine ((integrable_const (|f 0| + max C 0)).add
        ((integrable_natCast_geomLaw hp0 hp1).const_mul (max C 0))).mono'
      Measurable.of_discrete.aestronglyMeasurable (Filter.Eventually.of_forall fun k ↦ ?_)
    rw [Real.norm_eq_abs]
    calc
      |f (k + 1)| ≤ |f 0| + max C 0 * ((k + 1 : ℕ) : ℝ) := abs_le_of_abs_fwdDiff_le hf (k + 1)
      _ = (|f 0| + max C 0) + max C 0 * (k : ℝ) := by
        push_cast
        ring
  simp_rw [id_eq, fwdDiff]
  rw [integral_sub hf_shift hf_int, integral_geomLaw_shift_relation hp0 hp1 hf_int hf_shift]
  ring

end SteinMethod
