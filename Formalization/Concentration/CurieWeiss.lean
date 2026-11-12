/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.Exchangeable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Magnetization Concentration in the Curie–Weiss Model (`Formalization.Concentration.CurieWeiss`)

Proves **Proposition 7.4** (`\label{prop2112y}`, `SteinIntro.tex:3645-3801`) from Section 7 of
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `abs_tanh_sub_tanh_le`: 1-Lipschitz inequality $|\tanh(x) - \tanh(y)| \le |x - y|$
  (`SteinIntro.tex:3778-3780`).
* `curieWeiss_magnetization_concentration` (**Proposition 7.4**, `\label{prop2112y}`,
  `SteinIntro.tex:3645-3653`): for all $n \ge 1$, $\beta > 0$, $h \in \mathbb{R}$, and $t \ge 0$,
  under the Curie–Weiss Gibbs measure `(7.6)` (`\label{2199}`),
  $\mathbb{P}\bigl(|m - \tanh(\beta m + \beta h)| \ge \frac{\beta}{n} + \frac{t}{\sqrt{n}}\bigr)
  \le 2\exp\bigl(-\frac{t^2}{4(1 + \beta)}\bigr)$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SteinMethod

/-! ### Section 1: Hyperbolic Tangent Helpers -/

/-- Derivative of `Real.tanh` is `1 / Real.cosh x ^ 2` (`SteinIntro.tex:3652, 3778`). -/
private lemma hasDerivAt_tanh_real (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have heq : Real.tanh = fun z : ℝ ↦ Real.sinh z / Real.cosh z :=
    funext fun z ↦ Real.tanh_eq_sinh_div_cosh z
  rw [heq]
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne' using 1
  have hsq := Real.cosh_sq_sub_sinh_sq x
  rw [sq, sq] at hsq
  rw [hsq]

/-- 1-Lipschitz property $|\tanh(x) - \tanh(y)| \le |x - y|$ (`SteinIntro.tex:3778-3780`). -/
theorem abs_tanh_sub_tanh_le (x y : ℝ) :
    |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have hmono_tanh : Monotone Real.tanh :=
    monotone_of_hasDerivAt_nonneg hasDerivAt_tanh_real fun z ↦ by positivity
  have hmono_diff : Monotone (fun z : ℝ ↦ z - Real.tanh z) := by
    refine monotone_of_hasDerivAt_nonneg
      (fun z ↦ (hasDerivAt_id' z).fun_sub (hasDerivAt_tanh_real z)) fun z ↦ ?_
    change 0 ≤ 1 - 1 / Real.cosh z ^ 2
    have hc1 : 1 ≤ Real.cosh z := Real.one_le_cosh z
    have hcsq : 1 ≤ Real.cosh z ^ 2 := by nlinarith
    have hdiv : 1 / Real.cosh z ^ 2 ≤ 1 := div_le_one_of_le₀ hcsq (sq_nonneg _)
    linarith
  rcases le_total y x with hyx | hxy
  · have h1 : 0 ≤ Real.tanh x - Real.tanh y := sub_nonneg.mpr (hmono_tanh hyx)
    have h2 : Real.tanh x - Real.tanh y ≤ x - y := by linarith [hmono_diff hyx]
    rw [abs_of_nonneg h1, abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact h2
  · have h1 : 0 ≤ Real.tanh y - Real.tanh x := sub_nonneg.mpr (hmono_tanh hxy)
    have h2 : Real.tanh y - Real.tanh x ≤ y - x := by linarith [hmono_diff hxy]
    rw [abs_sub_comm, abs_of_nonneg h1, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h2

/-- Expresses $(e^u - e^{-u}) / (e^u + e^{-u})$ as `Real.tanh u` (`SteinIntro.tex:3652, 3740`). -/
private lemma exp_sub_div_exp_add_eq_tanh (u : ℝ) :
    (Real.exp u - Real.exp (-u)) / (Real.exp u + Real.exp (-u)) = Real.tanh u := by
  have h1 := Real.cosh_add_sinh u
  have h2 := Real.cosh_sub_sinh u
  have hnum : Real.exp u - Real.exp (-u) = 2 * Real.sinh u := by linarith
  have hden : Real.exp u + Real.exp (-u) = 2 * Real.cosh u := by linarith
  rw [hnum, hden, mul_div_mul_left _ _ two_ne_zero, ← Real.tanh_eq_sinh_div_cosh]

/-! ### Section 2: Gibbs Sampler Pair & Local Factorization -/

section GibbsSampler

private noncomputable def cwMag (n : ℕ) (x : Fin n → Bool) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, spin (x i)

private noncomputable def cwMagErase (n : ℕ) (x : Fin n → Bool) (i : Fin n) : ℝ :=
  (1 / (n : ℝ)) * ∑ j ∈ Finset.univ.erase i, spin (x j)

private noncomputable def cwLocalField (n : ℕ) (β h : ℝ) (x : Fin n → Bool) (i : Fin n) : ℝ :=
  β * cwMagErase n x i + β * h

private lemma spin_sq_eq_one (b : Bool) : spin b ^ 2 = 1 := by
  cases b <;> simp [spin]

/-- Pairwise interaction identity
$\sum_{j < k} \sigma_j \sigma_k = \frac{1}{2}((\sum_j \sigma_j)^2 - n)$ for $\pm 1$ spins
(`SteinIntro.tex:3634-3635`). -/
private lemma curieWeiss_pair_sum_eq (n : ℕ) (y : Fin n → Bool) :
    (∑ j : Fin n, ∑ k ∈ Finset.univ.filter (j < ·), spin (y j) * spin (y k)) =
      ((∑ j : Fin n, spin (y j)) ^ 2 - (n : ℝ)) / 2 := by
  have hlt_eq_gt :
      (∑ j : Fin n, ∑ k ∈ Finset.univ.filter (· < j), spin (y j) * spin (y k)) =
        ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (j < ·), spin (y j) * spin (y k) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by
      split_ifs <;> ring
  have hsq : (∑ j : Fin n, spin (y j)) ^ 2 =
      ∑ j : Fin n, ∑ k : Fin n, spin (y j) * spin (y k) := by
    rw [sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.mul_sum _ _ _
  have hsplit : ∀ j : Fin n,
      (∑ k : Fin n, spin (y j) * spin (y k)) =
        1 + ((∑ k ∈ Finset.univ.filter (j < ·), spin (y j) * spin (y k)) +
          ∑ k ∈ Finset.univ.filter (· < j), spin (y j) * spin (y k)) := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hdiag : spin (y j) * spin (y j) = 1 := by rw [← sq, spin_sq_eq_one]
    have hunion : Finset.univ.erase j =
        Finset.univ.filter (j < ·) ∪ Finset.univ.filter (· < j) := by
      ext k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
        true_and]
      exact ne_iff_lt_or_gt.trans or_comm
    have hdisj : Disjoint (Finset.univ.filter (j < ·)) (Finset.univ.filter (· < j)) := by
      rw [Finset.disjoint_filter]
      exact fun _ _ h1 h2 ↦ lt_asymm h1 h2
    rw [hdiag, hunion, Finset.sum_union hdisj]
  simp_rw [hsplit] at hsq
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsq
  linarith

/-- Local Boltzmann factorization of `curieWeissWeight n β h (Function.update x i b)`
(`SteinIntro.tex:3711-3736`). -/
private lemma curieWeissWeight_update_eq {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    let S : ℝ := ∑ j ∈ Finset.univ.erase i, spin (x j)
    let base : ℝ := β / (n : ℝ) * ((S ^ 2 + 1 - (n : ℝ)) / 2) + β * h * S
    curieWeissWeight n β h (Function.update x i b) =
      Real.exp base * Real.exp (spin b * cwLocalField n β h x i) := by
  intro S base
  have hrn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum : (∑ j : Fin n, spin (Function.update x i b j)) = spin b + S := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  unfold curieWeissWeight
  rw [curieWeiss_pair_sum_eq, hsum, ← Real.exp_add]
  congr 1
  dsimp [base, cwLocalField, cwMagErase, S]
  field_simp [hrn]
  have hsb : spin b = 1 ∨ spin b = -1 := by cases b <;> simp [spin]
  rcases hsb with hb | hb <;> rw [hb] <;> ring

/-- Conditional resampling probability of setting site `i` to `b` given `(x j)_{j ≠ i}`
(`SteinIntro.tex:3700-3736`). -/
private noncomputable def cwCondProb (n : ℕ) (β h : ℝ) (x : Fin n → Bool)
    (i : Fin n) (b : Bool) : ℝ :=
  curieWeissWeight n β h (Function.update x i b) /
    (curieWeissWeight n β h (Function.update x i true) +
      curieWeissWeight n β h (Function.update x i false))

private lemma cwCondProb_nonneg (n : ℕ) (β h : ℝ) (x : Fin n → Bool)
    (i : Fin n) (b : Bool) : 0 ≤ cwCondProb n β h x i b :=
  div_nonneg (curieWeissWeight_pos n β h _).le
    (add_pos (curieWeissWeight_pos n β h _) (curieWeissWeight_pos n β h _)).le

private lemma cwCondProb_sum_bool (n : ℕ) (β h : ℝ) (x : Fin n → Bool) (i : Fin n) :
    ∑ b : Bool, cwCondProb n β h x i b = 1 := by
  have hden : 0 < curieWeissWeight n β h (Function.update x i true) +
      curieWeissWeight n β h (Function.update x i false) :=
    add_pos (curieWeissWeight_pos n β h _) (curieWeissWeight_pos n β h _)
  rw [Fintype.sum_bool]
  dsimp [cwCondProb]
  rw [← add_div, div_self hden.ne']

private lemma cwCondProb_spin_expectation {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (x : Fin n → Bool) (i : Fin n) :
    (∑ b : Bool, cwCondProb n β h x i b * spin b) =
      Real.tanh (cwLocalField n β h x i) := by
  rw [Fintype.sum_bool]
  dsimp [cwCondProb]
  rw [curieWeissWeight_update_eq hn β h x i true, curieWeissWeight_update_eq hn β h x i false]
  set E := Real.exp
    (β / (n : ℝ) * (((∑ j ∈ Finset.univ.erase i, spin (x j)) ^ 2 + 1 - (n : ℝ)) / 2) +
      β * h * ∑ j ∈ Finset.univ.erase i, spin (x j))
  set u := cwLocalField n β h x i
  have hE : E ≠ 0 := (Real.exp_pos _).ne'
  have hden : Real.exp u + Real.exp (-u) ≠ 0 :=
    (add_pos (Real.exp_pos u) (Real.exp_pos (-u))).ne'
  have hst : spin true = 1 := rfl
  have hsf : spin false = -1 := rfl
  rw [hst, hsf, one_mul, neg_one_mul]
  calc E * Real.exp u / (E * Real.exp u + E * Real.exp (-u)) * 1 +
        E * Real.exp (-u) / (E * Real.exp u + E * Real.exp (-u)) * (-1)
      = (Real.exp u - Real.exp (-u)) / (Real.exp u + Real.exp (-u)) := by
        field_simp [hE, hden]; ring
    _ = Real.tanh u := exp_sub_div_exp_add_eq_tanh u

/-- Joint weight of transitioning from `x` via site `i` to `Function.update x i b` in the
Curie–Weiss Gibbs sampler (`SteinIntro.tex:3685-3706`). -/
private noncomputable def cwStepWeight (n : ℕ) (β h : ℝ)
    (q : (Fin n → Bool) × Fin n × Bool) : ℝ :=
  (1 / (n : ℝ)) * (curieWeissWeight n β h q.1 / curieWeissPartition n β h) *
    cwCondProb n β h q.1 q.2.1 q.2.2

private lemma cwStepWeight_nonneg (n : ℕ) (β h : ℝ)
    (q : (Fin n → Bool) × Fin n × Bool) : 0 ≤ cwStepWeight n β h q :=
  mul_nonneg
    (mul_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg n))
      (div_nonneg (curieWeissWeight_pos n β h q.1).le (curieWeissPartition_pos n β h).le))
    (cwCondProb_nonneg n β h q.1 q.2.1 q.2.2)

/-- Joint measure of one step $(\sigma, \sigma')$ of the Curie–Weiss Gibbs sampler on
`(Fin n → Bool) × (Fin n → Bool)` (`SteinIntro.tex:3685-3695`). -/
private noncomputable def cwJointMeasure (n : ℕ) (β h : ℝ) :
    Measure ((Fin n → Bool) × (Fin n → Bool)) :=
  Measure.sum fun q : (Fin n → Bool) × Fin n × Bool ↦
    ENNReal.ofReal (cwStepWeight n β h q) •
      Measure.dirac (q.1, Function.update q.1 q.2.1 q.2.2)

private lemma cwStepWeight_sum_step {n : ℕ} (hn : 0 < n) (β h : ℝ) (x : Fin n → Bool) :
    (∑ i : Fin n, ∑ b : Bool, cwStepWeight n β h (x, i, b)) =
      curieWeissWeight n β h x / curieWeissPartition n β h := by
  have hrn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  dsimp only [cwStepWeight]
  have hinner : ∀ i : Fin n,
      (∑ b : Bool, (1 / (n : ℝ)) * (curieWeissWeight n β h x / curieWeissPartition n β h) *
          cwCondProb n β h x i b) =
        (1 / (n : ℝ)) * (curieWeissWeight n β h x / curieWeissPartition n β h) := fun i ↦ by
    rw [← Finset.mul_sum, cwCondProb_sum_bool, mul_one]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hrn]

private lemma cwJointMeasure_isProb {n : ℕ} (hn : 0 < n) (β h : ℝ) :
    IsProbabilityMeasure (cwJointMeasure n β h) := by
  rw [isProbabilityMeasure_iff, cwJointMeasure, Measure.sum_apply _ MeasurableSet.univ,
    tsum_fintype]
  have hterm : ∀ q : (Fin n → Bool) × Fin n × Bool,
      (ENNReal.ofReal (cwStepWeight n β h q) •
        Measure.dirac (q.1, Function.update q.1 q.2.1 q.2.2)) Set.univ =
        ENNReal.ofReal (cwStepWeight n β h q) := fun q ↦ by
    rw [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
      Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, smul_eq_mul, mul_one]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun q _ ↦ cwStepWeight_nonneg n β h q,
    Fintype.sum_prod_type]
  have hinner : ∀ x : Fin n → Bool,
      (∑ p : Fin n × Bool, cwStepWeight n β h (x, p)) =
        curieWeissWeight n β h x / curieWeissPartition n β h := fun x ↦ by
    rw [Fintype.sum_prod_type, cwStepWeight_sum_step hn β h x]
  simp_rw [hinner, ← Finset.sum_div]
  change ENNReal.ofReal (curieWeissPartition n β h / curieWeissPartition n β h) = 1
  rw [div_self (curieWeissPartition_pos n β h).ne', ENNReal.ofReal_one]

private lemma cwJointMeasure_map_fst {n : ℕ} (hn : 0 < n) (β h : ℝ) :
    (cwJointMeasure n β h).map Prod.fst = curieWeissMeasure n β h := by
  ext s hs
  classical
  rw [Measure.map_apply measurable_fst hs, cwJointMeasure,
    Measure.sum_apply _ (measurable_fst hs), tsum_fintype,
    curieWeissMeasure, Measure.sum_apply _ hs, tsum_fintype]
  have h1 : ∀ q : (Fin n → Bool) × Fin n × Bool,
      (ENNReal.ofReal (cwStepWeight n β h q) •
        Measure.dirac (q.1, Function.update q.1 q.2.1 q.2.2)) (Prod.fst ⁻¹' s) =
        if q.1 ∈ s then ENNReal.ofReal (cwStepWeight n β h q) else 0 := fun q ↦ by
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurable_fst hs)]
    by_cases hq : q.1 ∈ s <;> simp [hq]
  have h2 : ∀ x : Fin n → Bool,
      (ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h) •
        Measure.dirac x) s =
        if x ∈ s then ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h)
        else 0 := fun x ↦ by
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    by_cases hx : x ∈ s <;> simp [hx]
  simp_rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : x ∈ s
  · simp only [hx, ↓reduceIte]
    simp_rw [← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ cwStepWeight_nonneg n β h (x, _, b)]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦
        Finset.sum_nonneg fun b _ ↦ cwStepWeight_nonneg n β h (x, i, b),
      cwStepWeight_sum_step hn β h x]
  · simp only [hx, ↓reduceIte, Finset.sum_const_zero]

/-- Reversibility (`IsExchangeablePair`) of one step of the Curie–Weiss Gibbs sampler
(`SteinIntro.tex:3687-3692`). -/
private lemma cwJointMeasure_exchangeable (n : ℕ) (β h : ℝ) :
    IsExchangeablePair (cwJointMeasure n β h) Prod.fst Prod.snd := by
  refine ⟨measurable_id.aemeasurable, measurable_swap.aemeasurable, ?_⟩
  change Measure.map id (cwJointMeasure n β h) = Measure.map Prod.swap (cwJointMeasure n β h)
  rw [Measure.map_id]
  symm
  ext s hs
  rw [Measure.map_apply measurable_swap hs, cwJointMeasure,
    Measure.sum_apply _ (measurable_swap hs), Measure.sum_apply _ hs, tsum_fintype, tsum_fintype]
  let invStep : ((Fin n → Bool) × Fin n × Bool) ≃ ((Fin n → Bool) × Fin n × Bool) :=
    { toFun := fun q ↦ (Function.update q.1 q.2.1 q.2.2, q.2.1, q.1 q.2.1)
      invFun := fun q ↦ (Function.update q.1 q.2.1 q.2.2, q.2.1, q.1 q.2.1)
      left_inv := fun ⟨x, i, b⟩ ↦ by simp
      right_inv := fun ⟨x, i, b⟩ ↦ by simp }
  rw [← Equiv.sum_comp invStep]
  refine Finset.sum_congr rfl fun ⟨x, i, b⟩ _ ↦ ?_
  have hinv : invStep (x, i, b) = (Function.update x i b, i, x i) := rfl
  rw [hinv]
  dsimp only
  have hup_self : Function.update (Function.update x i b) i (x i) = x := by simp
  have hwt : cwStepWeight n β h (Function.update x i b, i, x i) =
      cwStepWeight n β h (x, i, b) := by
    dsimp [cwStepWeight, cwCondProb]
    simp only [Function.update_idem, hup_self]
    ring
  rw [hwt, hup_self, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurable_swap hs), Measure.dirac_apply' _ hs]
  rfl

private lemma cwJointMeasure_integral {n : ℕ} (_hn : 0 < n) (β h : ℝ)
    (H : ((Fin n → Bool) × (Fin n → Bool)) → ℝ) :
    ∫ p, H p ∂(cwJointMeasure n β h) =
      ∑ x : Fin n → Bool, ∑ i : Fin n, ∑ b : Bool,
        cwStepWeight n β h (x, i, b) * H (x, Function.update x i b) := by
  have hInt : ∀ q : (Fin n → Bool) × Fin n × Bool,
      Integrable H (ENNReal.ofReal (cwStepWeight n β h q) •
        Measure.dirac (q.1, Function.update q.1 q.2.1 q.2.2)) := fun q ↦ by
    have : IsFiniteMeasure (ENNReal.ofReal (cwStepWeight n β h q) •
        Measure.dirac (q.1, Function.update q.1 q.2.1 q.2.2)) := by
      constructor
      rw [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ]
      simp [ENNReal.ofReal_lt_top]
    exact Integrable.of_finite
  have hsum_eq : cwJointMeasure n β h =
      ∑ q : (Fin n → Bool) × Fin n × Bool,
        ENNReal.ofReal (cwStepWeight n β h q) •
          Measure.dirac (q.1, Function.update q.1 q.2.1 q.2.2) := by
    ext s hs
    rw [cwJointMeasure, Measure.sum_apply _ hs, Measure.finsetSum_apply, tsum_fintype]
  rw [hsum_eq, integral_finsetSum_measure fun q _ ↦ hInt q]
  have hterm : ∀ q : (Fin n → Bool) × Fin n × Bool,
      ∫ p, H p ∂(ENNReal.ofReal (cwStepWeight n β h q) •
        Measure.dirac (q.1, Function.update q.1 q.2.1 q.2.2)) =
        cwStepWeight n β h q * H (q.1, Function.update q.1 q.2.1 q.2.2) := fun q ↦ by
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (cwStepWeight_nonneg n β h q), smul_eq_mul]
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun x _ ↦ Fintype.sum_prod_type _

/-- Conditional expectation given `Prod.fst` under `cwJointMeasure` (`SteinIntro.tex:3738-3747`). -/
private lemma cwJointMeasure_condExp_fst {n : ℕ} (hn : 0 < n) (β h : ℝ)
    (H : ((Fin n → Bool) × (Fin n → Bool)) → ℝ) :
    (fun p : (Fin n → Bool) × (Fin n → Bool) ↦
        (1 / (n : ℝ)) * ∑ i : Fin n, ∑ b : Bool,
          cwCondProb n β h p.1 i b * H (p.1, Function.update p.1 i b)) =ᵐ[cwJointMeasure n β h]
      (cwJointMeasure n β h)[H |
        MeasurableSpace.comap
          (Prod.fst : ((Fin n → Bool) × (Fin n → Bool)) → Fin n → Bool) inferInstance] := by
  have := cwJointMeasure_isProb hn β h
  let fstCW : ((Fin n → Bool) × (Fin n → Bool)) → Fin n → Bool := Prod.fst
  let g : (Fin n → Bool) → ℝ := fun x ↦
    (1 / (n : ℝ)) * ∑ i : Fin n, ∑ b : Bool,
      cwCondProb n β h x i b * H (x, Function.update x i b)
  have hg_sm : StronglyMeasurable[MeasurableSpace.comap fstCW inferInstance]
      (g ∘ fstCW) :=
    ((Measurable.of_discrete (f := g)).comp
      (comap_measurable (m := inferInstance) fstCW)).stronglyMeasurable
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le
    Integrable.of_finite (fun _ _ _ ↦ Integrable.of_finite) (fun s hs _ ↦ ?_)
    hg_sm.aestronglyMeasurable
  rcases hs with ⟨T, hT, rfl⟩
  rw [← integral_indicator (measurable_fst hT), ← integral_indicator (measurable_fst hT),
    cwJointMeasure_integral hn β h, cwJointMeasure_integral hn β h]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : x ∈ T
  · have hmem : ∀ i b, (x, Function.update x i b) ∈ Prod.fst ⁻¹' T := fun _ _ ↦ hx
    simp only [hmem, Set.indicator_of_mem]
    have h1 : (∑ i : Fin n, ∑ b : Bool, cwStepWeight n β h (x, i, b) * g x) =
        (curieWeissWeight n β h x / curieWeissPartition n β h) * g x := by
      simp_rw [← Finset.sum_mul, cwStepWeight_sum_step hn β h x]
    rw [h1]
    dsimp only [g, cwStepWeight]
    rw [← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  · have hnot : ∀ i b, (x, Function.update x i b) ∉ Prod.fst ⁻¹' T := fun _ _ ↦ hx
    simp [hnot]

end GibbsSampler

/-! ### Section 3: Proof of Proposition 7.4 -/

/-- **Proposition 7.4** (`\label{prop2112y}`, `SteinIntro.tex:3645-3653`): concentration of the
empirical magnetization $m(\sigma) = \frac{1}{n}\sum_{i=1}^n \sigma_i$ in the Curie–Weiss model
with Gibbs measure `(7.6)` (`\label{2199}`). -/
theorem curieWeiss_magnetization_concentration
    {n : ℕ} (hn : 0 < n) {β h t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    let P : Measure (Fin n → Bool) := curieWeissMeasure n β h
    let m : (Fin n → Bool) → ℝ := fun x ↦ (1 / (n : ℝ)) * ∑ i : Fin n, spin (x i)
    P.real {x | β / (n : ℝ) + t / Real.sqrt (n : ℝ) ≤ |m x - Real.tanh (β * m x + β * h)|} ≤
      2 * Real.exp (-t ^ 2 / (4 * (1 + β))) := by
  intro P m
  rcases ht.eq_or_lt with rfl | ht_pos
  · -- Boundary `t = 0`: `2 * exp 0 = 2 ≥ 1 ≥ P.real ...`.
    have hprob1 : P.real {x | β / (n : ℝ) + 0 / Real.sqrt (n : ℝ) ≤
        |m x - Real.tanh (β * m x + β * h)|} ≤ 1 := by
      have hmono : P.real {x | β / (n : ℝ) + 0 / Real.sqrt (n : ℝ) ≤
          |m x - Real.tanh (β * m x + β * h)|} ≤ P.real Set.univ := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (Set.subset_univ _))
      exact hmono.trans_eq probReal_univ
    have hrhs : 2 * Real.exp (-0 ^ 2 / (4 * (1 + β))) = 2 := by simp
    linarith
  · -- Main case `t > 0`: apply Theorem 7.5 (`exchangeable_antisymm_tail_bound`) to Gibbs step `Q`.
    have := cwJointMeasure_isProb hn β h
    let Q := cwJointMeasure n β h
    have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hrn_pos
    let F : ((Fin n → Bool) × (Fin n → Bool)) → ℝ :=
      fun p ↦ ∑ i : Fin n, (spin (p.1 i) - spin (p.2 i))
    let f : (Fin n → Bool) → ℝ :=
      fun x ↦ cwMag n x - (1 / (n : ℝ)) * ∑ i : Fin n, Real.tanh (cwLocalField n β h x i)
    have hAnti : ∀ x x' : Fin n → Bool, F (x, x') = -F (x', x) := fun x x' ↦ by
      dsimp [F]
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    -- 1. Check `f(X) = Q[F(X, X') | X]` a.s. (`SteinIntro.tex:3738-3759`).
    have hf_eq : (fun p : (Fin n → Bool) × (Fin n → Bool) ↦ f p.1) =ᵐ[Q]
        Q[fun p ↦ F (p.1, p.2) | MeasurableSpace.comap Prod.fst inferInstance] := by
      refine (EventuallyEq.of_eq ?_).trans (cwJointMeasure_condExp_fst hn β h F)
      funext p
      have hstepF : ∀ (x : Fin n → Bool) (i : Fin n) (b : Bool),
          F (x, Function.update x i b) = spin (x i) - spin b := fun x i b ↦ by
        dsimp [F]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
        have hrest : ∑ j ∈ Finset.univ.erase i,
            (spin (x j) - spin (Function.update x i b j)) = 0 :=
          Finset.sum_eq_zero fun j hj ↦ by
            rw [Function.update_of_ne (Finset.mem_erase.mp hj).1, sub_self]
        rw [hrest, add_zero]
      have hinner : ∀ (x : Fin n → Bool) (i : Fin n),
          (∑ b : Bool, cwCondProb n β h x i b * F (x, Function.update x i b)) =
            spin (x i) - Real.tanh (cwLocalField n β h x i) := fun x i ↦ by
        simp_rw [hstepF, mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, cwCondProb_sum_bool, one_mul,
          cwCondProb_spin_expectation hn β h x i]
      dsimp only [f, cwMag]
      simp_rw [hinner]
      rw [Finset.sum_sub_distrib]
      ring
    -- 2. Single-coordinate Lipschitz & step bounds (`SteinIntro.tex:3771-3787`).
    have hspin_diff : ∀ b₁ b₂ : Bool, |spin b₁ - spin b₂| ≤ 2 := by
      intro b₁ b₂; cases b₁ <;> cases b₂ <;> norm_num [spin]
    have hStepProd : ∀ (x : Fin n → Bool) (i : Fin n) (b : Bool),
        |(f x - f (Function.update x i b)) * F (x, Function.update x i b)| ≤
          4 * (1 + β) / (n : ℝ) := by
      intro x i b
      let y := Function.update x i b
      have hF_abs : |F (x, y)| ≤ 2 := by
        have hFeq : F (x, y) = spin (x i) - spin b := by
          dsimp [F, y]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
          have h0 : ∑ j ∈ Finset.univ.erase i,
              (spin (x j) - spin (Function.update x i b j)) = 0 :=
            Finset.sum_eq_zero fun j hj ↦ by
              rw [Function.update_of_ne (Finset.mem_erase.mp hj).1, sub_self]
          rw [h0, add_zero]
        rw [hFeq]
        exact hspin_diff (x i) b
      have hm_diff : |cwMag n x - cwMag n y| ≤ 2 / (n : ℝ) := by
        have hmeq : cwMag n x - cwMag n y = (spin (x i) - spin b) / (n : ℝ) := by
          dsimp [cwMag, y]
          rw [← mul_sub, ← Finset.sum_sub_distrib,
            ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
          have h0 : ∑ j ∈ Finset.univ.erase i,
              (spin (x j) - spin (Function.update x i b j)) = 0 :=
            Finset.sum_eq_zero fun j hj ↦ by
              rw [Function.update_of_ne (Finset.mem_erase.mp hj).1, sub_self]
          rw [h0, add_zero]; ring
        rw [hmeq, abs_div, abs_of_pos hrn_pos]
        exact div_le_div_of_nonneg_right (hspin_diff (x i) b) hrn_pos.le
      have hmi_diff : ∀ k : Fin n, |cwMagErase n x k - cwMagErase n y k| ≤ 2 / (n : ℝ) := by
        intro k
        dsimp [cwMagErase, y]
        rw [← mul_sub, ← Finset.sum_sub_distrib]
        by_cases hik : i = k
        · subst hik
          have h0 : ∑ j ∈ Finset.univ.erase i,
              (spin (x j) - spin (Function.update x i b j)) = 0 :=
            Finset.sum_eq_zero fun j hj ↦ by
              rw [Function.update_of_ne (Finset.mem_erase.mp hj).1, sub_self]
          rw [h0, mul_zero, abs_zero]
          positivity
        · rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩),
            Function.update_self]
          have h0 : ∑ j ∈ (Finset.univ.erase k).erase i,
              (spin (x j) - spin (Function.update x i b j)) = 0 :=
            Finset.sum_eq_zero fun j hj ↦ by
              rw [Function.update_of_ne (Finset.mem_erase.mp hj).1, sub_self]
          rw [h0, add_zero, one_div, inv_mul_eq_div, abs_div, abs_of_pos hrn_pos]
          exact div_le_div_of_nonneg_right (hspin_diff (x i) b) hrn_pos.le
      have hftanh : ∀ k : Fin n,
          |Real.tanh (cwLocalField n β h x k) - Real.tanh (cwLocalField n β h y k)| ≤
            2 * β / (n : ℝ) := fun k ↦ by
        refine (abs_tanh_sub_tanh_le _ _).trans ?_
        have hlin : cwLocalField n β h x k - cwLocalField n β h y k =
            β * (cwMagErase n x k - cwMagErase n y k) := by dsimp [cwLocalField]; ring
        rw [hlin, abs_mul, abs_of_pos hβ]
        calc β * |cwMagErase n x k - cwMagErase n y k|
            ≤ β * (2 / (n : ℝ)) := mul_le_mul_of_nonneg_left (hmi_diff k) hβ.le
          _ = 2 * β / (n : ℝ) := by ring
      have hf_diff : |f x - f y| ≤ 2 * (1 + β) / (n : ℝ) := by
        have hdecomp : f x - f y = (cwMag n x - cwMag n y) -
            (1 / (n : ℝ)) * ∑ k : Fin n,
              (Real.tanh (cwLocalField n β h x k) - Real.tanh (cwLocalField n β h y k)) := by
          dsimp [f]; rw [Finset.sum_sub_distrib]; ring
        rw [hdecomp]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hrn_pos)]
        have hsum_le : |∑ k : Fin n,
            (Real.tanh (cwLocalField n β h x k) - Real.tanh (cwLocalField n β h y k))| ≤
            (n : ℝ) * (2 * β / (n : ℝ)) :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            ((Finset.sum_le_sum fun k _ ↦ hftanh k).trans_eq (by simp))
        have hmul_le : (1 / (n : ℝ)) * |∑ k : Fin n,
            (Real.tanh (cwLocalField n β h x k) - Real.tanh (cwLocalField n β h y k))| ≤
            2 * β / (n : ℝ) := by
          calc (1 / (n : ℝ)) * |∑ k : Fin n,
              (Real.tanh (cwLocalField n β h x k) - Real.tanh (cwLocalField n β h y k))|
              ≤ (1 / (n : ℝ)) * ((n : ℝ) * (2 * β / (n : ℝ))) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = 2 * β / (n : ℝ) := by field_simp [hrn_pos.ne']
        calc |cwMag n x - cwMag n y| + (1 / (n : ℝ)) * |∑ k : Fin n,
              (Real.tanh (cwLocalField n β h x k) - Real.tanh (cwLocalField n β h y k))|
            ≤ 2 / (n : ℝ) + 2 * β / (n : ℝ) := add_le_add hm_diff hmul_le
          _ = 2 * (1 + β) / (n : ℝ) := by ring
      rw [abs_mul]
      calc |f x - f y| * |F (x, y)|
          ≤ (2 * (1 + β) / (n : ℝ)) * 2 :=
            mul_le_mul hf_diff hF_abs (abs_nonneg _) (by positivity)
        _ = 4 * (1 + β) / (n : ℝ) := by ring
    let C : ℝ := 2 * (1 + β) / (n : ℝ)
    have hC_pos : 0 < C := by dsimp [C]; positivity
    have hCond : ∀ᵐ p ∂Q,
        (1 / 2 : ℝ) *
            Q[fun p' ↦ |(f p'.1 - f p'.2) * F (p'.1, p'.2)| |
              MeasurableSpace.comap Prod.fst inferInstance] p ≤
          0 * f p.1 + C := by
      have hce := cwJointMeasure_condExp_fst hn β h
        (fun p' ↦ |(f p'.1 - f p'.2) * F (p'.1, p'.2)|)
      filter_upwards [hce.symm] with p hp
      rw [hp, zero_mul, zero_add]
      have hinner : ∀ i : Fin n,
          (∑ b : Bool, cwCondProb n β h p.1 i b *
              |(f p.1 - f (Function.update p.1 i b)) * F (p.1, Function.update p.1 i b)|) ≤
            4 * (1 + β) / (n : ℝ) := fun i ↦ by
        calc (∑ b : Bool, cwCondProb n β h p.1 i b *
              |(f p.1 - f (Function.update p.1 i b)) * F (p.1, Function.update p.1 i b)|)
            ≤ ∑ b : Bool, cwCondProb n β h p.1 i b * (4 * (1 + β) / (n : ℝ)) :=
              Finset.sum_le_sum fun b _ ↦
                mul_le_mul_of_nonneg_left (hStepProd p.1 i b) (cwCondProb_nonneg n β h p.1 i b)
          _ = 4 * (1 + β) / (n : ℝ) := by
              rw [← Finset.sum_mul, cwCondProb_sum_bool, one_mul]
      have hsum : (∑ i : Fin n, ∑ b : Bool, cwCondProb n β h p.1 i b *
            |(f p.1 - f (Function.update p.1 i b)) * F (p.1, Function.update p.1 i b)|) ≤
          (n : ℝ) * (4 * (1 + β) / (n : ℝ)) :=
        (Finset.sum_le_sum fun i _ ↦ hinner i).trans_eq (by simp)
      calc (1 / 2 : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, ∑ b : Bool, cwCondProb n β h p.1 i b *
              |(f p.1 - f (Function.update p.1 i b)) * F (p.1, Function.update p.1 i b)|)
          ≤ (1 / 2 : ℝ) * ((1 / (n : ℝ)) * ((n : ℝ) * (4 * (1 + β) / (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by norm_num)
        _ = C := by dsimp [C]; field_simp [hrn_pos.ne']; ring
    have hInt : ∀ θ : ℝ, Integrable (fun p ↦ Real.exp (θ * f p.1) * |F (p.1, p.2)|) Q :=
      fun _ ↦ Integrable.of_finite
    have ht_div : 0 < t / Real.sqrt (n : ℝ) := div_pos ht_pos hsqrtn_pos
    obtain ⟨hUp, _, hLow, _⟩ :=
      exchangeable_antisymm_tail_bound Q measurable_fst (cwJointMeasure_exchangeable n β h)
        .of_discrete hAnti .of_discrete hf_eq hInt le_rfl hC_pos.le hCond ht_div
    -- 3. Approximate `m - tanh(β m + β h)` by `f` within `β / n` (`SteinIntro.tex:3793-3800`).
    have hApprox : ∀ x : Fin n → Bool,
        |m x - Real.tanh (β * m x + β * h) - f x| ≤ β / (n : ℝ) := by
      intro x
      have hdiff : m x - Real.tanh (β * m x + β * h) - f x =
          (1 / (n : ℝ)) * ∑ i : Fin n,
            (Real.tanh (cwLocalField n β h x i) - Real.tanh (β * m x + β * h)) := by
        dsimp [f, m, cwMag]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp [hrn_pos.ne']
        ring
      have hmi : ∀ i : Fin n, |cwMagErase n x i - m x| = 1 / (n : ℝ) := fun i ↦ by
        have heq : cwMagErase n x i - m x = -(spin (x i) / (n : ℝ)) := by
          dsimp [cwMagErase, m]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
          ring
        have hspin_abs : |spin (x i)| = 1 := by cases x i <;> simp [spin]
        rw [heq, abs_neg, abs_div, hspin_abs, abs_of_pos hrn_pos]
      have hterm : ∀ i : Fin n,
          |Real.tanh (cwLocalField n β h x i) - Real.tanh (β * m x + β * h)| ≤ β / (n : ℝ) := by
        intro i
        refine (abs_tanh_sub_tanh_le _ _).trans ?_
        have hlin : cwLocalField n β h x i - (β * m x + β * h) = β * (cwMagErase n x i - m x) := by
          dsimp [cwLocalField]; ring
        rw [hlin, abs_mul, abs_of_pos hβ, hmi i]
        ring_nf; rfl
      rw [hdiff, abs_mul, abs_of_pos (one_div_pos.mpr hrn_pos)]
      have hsum : |∑ i : Fin n,
          (Real.tanh (cwLocalField n β h x i) - Real.tanh (β * m x + β * h))| ≤
          (n : ℝ) * (β / (n : ℝ)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          ((Finset.sum_le_sum fun i _ ↦ hterm i).trans_eq (by simp))
      calc (1 / (n : ℝ)) * |∑ i : Fin n,
            (Real.tanh (cwLocalField n β h x i) - Real.tanh (β * m x + β * h))|
          ≤ (1 / (n : ℝ)) * ((n : ℝ) * (β / (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = β / (n : ℝ) := by field_simp [hrn_pos.ne']
    have hSubEvent :
        {x : Fin n → Bool |
            β / (n : ℝ) + t / Real.sqrt (n : ℝ) ≤ |m x - Real.tanh (β * m x + β * h)|} ⊆
          {x | t / Real.sqrt (n : ℝ) ≤ |f x|} := by
      intro x hx
      change β / (n : ℝ) + t / Real.sqrt (n : ℝ) ≤ |m x - Real.tanh (β * m x + β * h)| at hx
      change t / Real.sqrt (n : ℝ) ≤ |f x|
      have htri : |m x - Real.tanh (β * m x + β * h)| ≤
          |m x - Real.tanh (β * m x + β * h) - f x| + |f x| := by
        simpa using abs_add_le (m x - Real.tanh (β * m x + β * h) - f x) (f x)
      linarith [hApprox x]
    have hMonoP :
        P.real {x | β / (n : ℝ) + t / Real.sqrt (n : ℝ) ≤
            |m x - Real.tanh (β * m x + β * h)|} ≤
          P.real {x | t / Real.sqrt (n : ℝ) ≤ |f x|} := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hSubEvent)
    have hMapFst : P.real {x | t / Real.sqrt (n : ℝ) ≤ |f x|} =
        Q.real {p | t / Real.sqrt (n : ℝ) ≤ |f p.1|} := by
      have hmap := cwJointMeasure_map_fst hn β h
      change (curieWeissMeasure n β h).real {x | t / Real.sqrt (n : ℝ) ≤ |f x|} = _
      rw [← hmap, measureReal_def, measureReal_def,
        Measure.map_apply measurable_fst (.of_discrete)]
      rfl
    have hUnion : Q.real {p | t / Real.sqrt (n : ℝ) ≤ |f p.1|} ≤
        Q.real {p | t / Real.sqrt (n : ℝ) ≤ f p.1} +
          Q.real {p | f p.1 ≤ -(t / Real.sqrt (n : ℝ))} := by
      have hsub : {p : (Fin n → Bool) × (Fin n → Bool) | t / Real.sqrt (n : ℝ) ≤ |f p.1|} ⊆
          {p | t / Real.sqrt (n : ℝ) ≤ f p.1} ∪ {p | f p.1 ≤ -(t / Real.sqrt (n : ℝ))} := by
        intro p hp
        change t / Real.sqrt (n : ℝ) ≤ |f p.1| at hp
        rcases le_abs.mp hp with h1 | h2
        · exact Or.inl (show t / Real.sqrt (n : ℝ) ≤ f p.1 from h1)
        · exact Or.inr (show f p.1 ≤ -(t / Real.sqrt (n : ℝ)) from by linarith)
      have hmono : Q.real {p | t / Real.sqrt (n : ℝ) ≤ |f p.1|} ≤
          Q.real ({p | t / Real.sqrt (n : ℝ) ≤ f p.1} ∪
            {p | f p.1 ≤ -(t / Real.sqrt (n : ℝ))}) := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono hsub)
      exact hmono.trans (measureReal_union_le _ _)
    have hExpEq : -(t / Real.sqrt (n : ℝ)) ^ 2 / (2 * C) = -t ^ 2 / (4 * (1 + β)) := by
      dsimp [C]
      rw [div_pow, Real.sq_sqrt hrn_pos.le]
      have h1b : (1 + β) ≠ 0 := by linarith
      field_simp [hrn_pos.ne', h1b]
      ring
    have hExpEq0 : -(t / Real.sqrt (n : ℝ)) ^ 2 / (2 * C + 2 * 0 * (t / Real.sqrt (n : ℝ))) =
        -t ^ 2 / (4 * (1 + β)) := by
      rw [mul_zero, zero_mul, add_zero]
      exact hExpEq
    rw [hExpEq0] at hUp
    rw [hExpEq] at hLow
    linarith [hMonoP, hMapFst, hUnion, hUp, hLow]

/-- Transfer of Proposition 7.4 (`\label{prop2112y}`, `SteinIntro.tex:3645-3653`) to any random
spin configuration `X : Ω → Fin n → Bool` with law `curieWeissMeasure n β h`. -/
theorem curieWeiss_concentration_of_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} {β h t : ℝ} {X : Ω → Fin n → Bool} (hn : 0 < n) (hβ : 0 < β) (ht : 0 ≤ t)
    (hX : AEMeasurable X P) (hlaw : P.map X = curieWeissMeasure n β h) :
    let m : Ω → ℝ := fun ω ↦ (∑ i : Fin n, spin (X ω i)) / (n : ℝ)
    P.real {ω | β / (n : ℝ) + t / Real.sqrt n ≤ |m ω - Real.tanh (β * m ω + β * h)|} ≤
      2 * Real.exp (-t ^ 2 / (4 * (1 + β))) := by
  intro m
  let m₀ : (Fin n → Bool) → ℝ := fun x ↦ (1 / (n : ℝ)) * ∑ i : Fin n, spin (x i)
  let E : Set (Fin n → Bool) :=
    {x | β / (n : ℝ) + t / Real.sqrt (n : ℝ) ≤ |m₀ x - Real.tanh (β * m₀ x + β * h)|}
  have hpre : {ω | β / (n : ℝ) + t / Real.sqrt n ≤ |m ω - Real.tanh (β * m ω + β * h)|} =
      X ⁻¹' E := by
    ext ω
    have hm : m ω = m₀ (X ω) := by dsimp [m, m₀]; ring
    change β / (n : ℝ) + t / Real.sqrt n ≤ |m ω - Real.tanh (β * m ω + β * h)| ↔
      β / (n : ℝ) + t / Real.sqrt n ≤ |m₀ (X ω) - Real.tanh (β * m₀ (X ω) + β * h)|
    rw [hm]
  rw [hpre, measureReal_def, ← Measure.map_apply_of_aemeasurable hX .of_discrete, hlaw,
    ← measureReal_def]
  exact curieWeiss_magnetization_concentration hn hβ ht

end SteinMethod
