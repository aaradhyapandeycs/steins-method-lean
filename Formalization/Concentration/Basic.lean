/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.Concentration
import Formalization.Normal.MillRatio
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Foundational MGF Concentration & Curie–Weiss Sanity (`Formalization.Concentration.Basic`)

Develops the foundational results of Section 7 (*Concentration Inequalities*,
`SteinIntro.tex:3389-3469, 3631-3644`) and non-vacuity sanity witnesses for
`Formalization.Defs.Concentration`:

* `curieWeissWeight_pos`, `curieWeissPartition_pos`, `instIsProbabilityMeasureCurieWeiss`,
  `curieWeissMeasure_real_singleton`, `curieWeiss_mode`: non-vacuity sanity witnesses and unique
  ground-state mode property (`SteinIntro.tex:3640-3641`) for the Curie–Weiss Gibbs measure `(7.6)`
  (`\label{2199}`, `SteinIntro.tex:3631-3637`).
* `abs_exp_sub_exp_le`: exponential chord inequality
  $|e^x - e^y| \le |x - y| \frac{e^x + e^y}{2}$ (eq. `(7.4)` `\label{211a}`,
  `SteinIntro.tex:3551, 3833`).
* `chernoff_tail_bounds` (**Proposition 7.1**, `\label{prop211}`, `SteinIntro.tex:3411-3417`).
* `mgf_integrable_mul_and_hasDerivAt` (Section 7 prose MGF derivative claim,
  `SteinIntro.tex:3464-3467`).
* `stdNormal_concentration` (**Example 7.1**, `\label{ex211}`, `SteinIntro.tex:3428-3445`).
* `poisson_concentration`, `poisson_bound_order_corrected`, `poisson_bound_order_restricted`,
  `not_poisson_bound_order_printed` (**Example 7.2**, `\label{ex212}`, `SteinIntro.tex:3447-3461`;
  `ISSUE-EX7.2`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Nat Topology

namespace SteinMethod

/-! ### Section 1: Non-Vacuity Sanity Witnesses & Ground States for `curieWeissMeasure` -/

/-- Strictly positive Boltzmann weight $w(\sigma) > 0$ in the Curie–Weiss model
(eq. `(7.6)` `\label{2199}`, `SteinIntro.tex:3631-3637`). -/
theorem curieWeissWeight_pos (n : ℕ) (β h : ℝ) (x : Fin n → Bool) :
    0 < curieWeissWeight n β h x :=
  Real.exp_pos _

/-- Strictly positive partition function $Z = \sum_\sigma w(\sigma) > 0$ in the Curie–Weiss model
(eq. `(7.6)` `\label{2199}`, `SteinIntro.tex:3631-3637`). -/
theorem curieWeissPartition_pos (n : ℕ) (β h : ℝ) :
    0 < curieWeissPartition n β h :=
  Finset.sum_pos (fun x _ ↦ curieWeissWeight_pos n β h x) Finset.univ_nonempty

/-- Singleton mass of `curieWeissMeasure` in `ℝ≥0∞`
(eq. `(7.6)` `\label{2199}`, `SteinIntro.tex:3631-3637`). -/
theorem curieWeissMeasure_singleton (n : ℕ) (β h : ℝ) (x : Fin n → Bool) :
    curieWeissMeasure n β h {x} =
      ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h) := by
  rw [curieWeissMeasure, Measure.sum_apply _ (measurableSet_singleton x), tsum_fintype]
  have hterm : ∀ y : Fin n → Bool,
      (ENNReal.ofReal (curieWeissWeight n β h y / curieWeissPartition n β h) •
        Measure.dirac y) {x} =
        if y = x then ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h)
        else 0 := by
    intro y
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' y (measurableSet_singleton x)]
    by_cases hyx : y = x
    · subst hyx; simp
    · have hnot : y ∉ ({x} : Set (Fin n → Bool)) := by simpa using hyx
      simp [hnot, hyx]
  simp_rw [hterm]
  simp

/-- Singleton probability mass `(curieWeissMeasure n β h).real {x} = Z⁻¹ w(x)`
(eq. `(7.6)` `\label{2199}`, `SteinIntro.tex:3631-3637`). -/
theorem curieWeissMeasure_real_singleton (n : ℕ) (β h : ℝ) (x : Fin n → Bool) :
    (curieWeissMeasure n β h).real {x} =
      (curieWeissPartition n β h)⁻¹ * curieWeissWeight n β h x := by
  have hnn : 0 ≤ curieWeissWeight n β h x / curieWeissPartition n β h :=
    div_nonneg (curieWeissWeight_pos n β h x).le (curieWeissPartition_pos n β h).le
  rw [measureReal_def, curieWeissMeasure_singleton, ENNReal.toReal_ofReal hnn, div_eq_inv_mul]

/-- Non-vacuity sanity witness: the Curie–Weiss Gibbs measure `(7.6)` (`\label{2199}`,
`SteinIntro.tex:3631-3637`) is a probability measure for all `n : ℕ` and `β, h : ℝ`. -/
instance instIsProbabilityMeasureCurieWeiss (n : ℕ) (β h : ℝ) :
    IsProbabilityMeasure (curieWeissMeasure n β h) := by
  rw [isProbabilityMeasure_iff, curieWeissMeasure, Measure.sum_apply _ MeasurableSet.univ,
    tsum_fintype]
  have hterm : ∀ x : Fin n → Bool,
      (ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h) •
        Measure.dirac x) Set.univ =
        ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h) := by
    intro x
    rw [Measure.smul_apply, Measure.dirac_apply' x MeasurableSet.univ,
      Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply, smul_eq_mul, mul_one]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦
    div_nonneg (curieWeissWeight_pos n β h x).le (curieWeissPartition_pos n β h).le]
  rw [← Finset.sum_div, ← curieWeissPartition,
    div_self (curieWeissPartition_pos n β h).ne', ENNReal.ofReal_one]

/-- Unique ground-state maximizers of the Curie–Weiss Gibbs weight and probability mass
(`SteinIntro.tex:3640-3641`): for $\beta > 0$, the all-$(+1)$ configuration uniquely maximizes
`(7.6)` when $h > 0$, and the all-$(-1)$ configuration uniquely maximizes `(7.6)` when $h < 0$. -/
theorem curieWeiss_mode {n : ℕ} {β h : ℝ} (hβ : 0 < β) :
    (0 < h →
        ∀ x : Fin n → Bool,
          x ≠ (fun _ ↦ true) →
          curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ true) ∧
            (curieWeissMeasure n β h).real {x} <
              (curieWeissMeasure n β h).real {fun _ ↦ true}) ∧
      (h < 0 →
        ∀ x : Fin n → Bool,
          x ≠ (fun _ ↦ false) →
          curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ false) ∧
            (curieWeissMeasure n β h).real {x} <
              (curieWeissMeasure n β h).real {fun _ ↦ false}) := by
  have hpair_le : ∀ (x : Fin n → Bool) (b : Bool),
      β / (n : ℝ) *
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin (x i) * spin (x j)) ≤
        β / (n : ℝ) *
          (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin b * spin b) := by
    intro x b
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_)
      (div_nonneg hβ.le (Nat.cast_nonneg n))
    cases hxi : x i <;> cases hxj : x j <;> cases b <;> simp [spin]
  have hZinv : 0 < (curieWeissPartition n β h)⁻¹ := inv_pos.mpr (curieWeissPartition_pos n β h)
  refine ⟨?_, ?_⟩
  · intro hh x hx
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    have hxi₀ : x i₀ = false := Bool.eq_false_iff.mpr hi₀
    have hsum_lt : (∑ i : Fin n, spin (x i)) < ∑ _i : Fin n, spin true := by
      refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
      · cases x i <;> simp [spin]
      · simp [hxi₀, spin]
    have hfield_lt : β * h * (∑ i : Fin n, spin (x i)) <
        β * h * ∑ _i : Fin n, spin true :=
      mul_lt_mul_of_pos_left hsum_lt (mul_pos hβ hh)
    have hw_lt : curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ true) := by
      unfold curieWeissWeight
      exact Real.exp_lt_exp.mpr (add_lt_add_of_le_of_lt (hpair_le x true) hfield_lt)
    refine ⟨hw_lt, ?_⟩
    rw [curieWeissMeasure_real_singleton, curieWeissMeasure_real_singleton]
    exact mul_lt_mul_of_pos_left hw_lt hZinv
  · intro hh x hx
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
    have hxi₀ : x i₀ = true := by cases h : x i₀ <;> simp_all
    have hsum_gt : (∑ _i : Fin n, spin false) < ∑ i : Fin n, spin (x i) := by
      refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
      · cases x i <;> simp [spin]
      · simp [hxi₀, spin]
    have hfield_lt : β * h * (∑ i : Fin n, spin (x i)) <
        β * h * ∑ _i : Fin n, spin false :=
      mul_lt_mul_of_neg_left hsum_gt (mul_neg_of_pos_of_neg hβ hh)
    have hw_lt : curieWeissWeight n β h x < curieWeissWeight n β h (fun _ ↦ false) := by
      unfold curieWeissWeight
      exact Real.exp_lt_exp.mpr (add_lt_add_of_le_of_lt (hpair_le x false) hfield_lt)
    refine ⟨hw_lt, ?_⟩
    rw [curieWeissMeasure_real_singleton, curieWeissMeasure_real_singleton]
    exact mul_lt_mul_of_pos_left hw_lt hZinv

/-! ### Section 2: Exponential Chord Inequality `(7.4)` -/

/-- Fundamental exponential chord inequality
$|e^x - e^y| \le |x - y| \frac{e^x + e^y}{2}$ used in the proofs of Theorem 7.2, Theorem 7.5, and
Theorem 7.6 (eq. `(7.4)` `\label{211a}`, `SteinIntro.tex:3551, 3833`). -/
theorem abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ |x - y| * ((Real.exp x + Real.exp y) / 2) := by
  have haux : ∀ a b : ℝ, b ≤ a →
      Real.exp a - Real.exp b ≤ (a - b) * ((Real.exp a + Real.exp b) / 2) := by
    intro a b hba
    let g : ℝ → ℝ := fun u ↦ u * (Real.exp u + Real.exp (-u)) - (Real.exp u - Real.exp (-u))
    have hg_deriv : ∀ u : ℝ, HasDerivAt g (u * (Real.exp u - Real.exp (-u))) u := by
      intro u
      have hneg : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-Real.exp (-u)) u := by
        simpa using (hasDerivAt_neg u).exp
      have hsum : HasDerivAt (fun t : ℝ ↦ Real.exp t + Real.exp (-t))
          (Real.exp u - Real.exp (-u)) u := by
        simpa [sub_eq_add_neg] using (Real.hasDerivAt_exp u).fun_add hneg
      have hdiff : HasDerivAt (fun t : ℝ ↦ Real.exp t - Real.exp (-t))
          (Real.exp u + Real.exp (-u)) u := by
        simpa [sub_eq_add_neg] using (Real.hasDerivAt_exp u).fun_sub hneg
      convert ((hasDerivAt_id' u).fun_mul hsum).fun_sub hdiff using 1; ring
    have hg_mono : Monotone g := by
      refine monotone_of_hasDerivAt_nonneg hg_deriv fun u ↦ ?_
      rcases le_total 0 u with hu | hu
      · have hexp : Real.exp (-u) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
        exact mul_nonneg hu (sub_nonneg.mpr hexp)
      · have hexp : Real.exp u ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
        exact mul_nonneg_of_nonpos_of_nonpos hu (sub_nonpos.mpr hexp)
    set u : ℝ := (a - b) / 2
    set m : ℝ := (a + b) / 2
    have hu : 0 ≤ u := by dsimp [u]; linarith
    have hg0 : 0 ≤ g u := by simpa [g] using hg_mono hu
    have ha : a = m + u := by dsimp [m, u]; ring
    have hb : b = m - u := by dsimp [m, u]; ring
    have hm_pos : 0 < Real.exp m := Real.exp_pos m
    have hmul : 0 ≤ Real.exp m * g u := mul_nonneg hm_pos.le hg0
    have hexpand : Real.exp m * g u =
        (a - b) * ((Real.exp a + Real.exp b) / 2) - (Real.exp a - Real.exp b) := by
      dsimp only [g]
      have h1 : Real.exp m * Real.exp u = Real.exp a := by rw [← Real.exp_add, ← ha]
      have h2 : Real.exp m * Real.exp (-u) = Real.exp b := by
        rw [← Real.exp_add, ← sub_eq_add_neg, ← hb]
      have h2u : 2 * u = a - b := by dsimp [u]; ring
      calc Real.exp m * (u * (Real.exp u + Real.exp (-u)) - (Real.exp u - Real.exp (-u)))
          = (2 * u) * ((Real.exp m * Real.exp u + Real.exp m * Real.exp (-u)) / 2) -
              (Real.exp m * Real.exp u - Real.exp m * Real.exp (-u)) := by ring
        _ = (a - b) * ((Real.exp a + Real.exp b) / 2) - (Real.exp a - Real.exp b) := by
            rw [h1, h2, h2u]
    linarith
  rcases le_total y x with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact haux x y hxy
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hyx)),
      abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hyx), add_comm (Real.exp x)]
    exact haux y x hyx

/-! ### Section 3: Proposition 7.1 & Prose MGF Derivative Claim -/

/-- **Proposition 7.1** (`\label{prop211}`, `SteinIntro.tex:3411-3417`): exponential Markov /
Chernoff upper and lower tail inequalities when $\mathbb{E}[e^{\theta W}] < \infty$ on
$(-\delta, \delta)$. -/
theorem chernoff_tail_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {δ : ℝ}
    (_hW : AEMeasurable W P) (_hδ : 0 < δ)
    (hint : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * W ω)) P)
    {t θ : ℝ} (_ht : 0 < t) (hθ0 : 0 < θ) (hθδ : θ < δ) :
    P.real {ω | t ≤ W ω} ≤ (∫ ω, Real.exp (θ * W ω) ∂P) / Real.exp (θ * t) ∧
      P.real {ω | W ω ≤ -t} ≤ (∫ ω, Real.exp (-θ * W ω) ∂P) / Real.exp (θ * t) := by
  have hpos_int : Integrable (fun ω ↦ Real.exp (θ * W ω)) P :=
    hint θ ⟨by linarith, hθδ⟩
  have hneg_int : Integrable (fun ω ↦ Real.exp (-θ * W ω)) P := by
    simpa [neg_mul] using hint (-θ) ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · have h1 := ProbabilityTheory.measure_ge_le_exp_mul_mgf t hθ0.le hpos_int
    simpa [ProbabilityTheory.mgf, neg_mul, Real.exp_neg, div_eq_mul_inv, mul_comm] using h1
  · have h2 := ProbabilityTheory.measure_le_le_exp_mul_mgf (-t) (neg_nonpos.mpr hθ0.le)
      (by simpa [neg_mul] using hneg_int)
    have hmul : -(-θ) * (-t) = -(θ * t) := by ring
    rw [hmul, Real.exp_neg] at h2
    simpa [ProbabilityTheory.mgf, neg_mul, div_eq_mul_inv, mul_comm] using h2

/-- **Section 7 prose MGF derivative identity** (`SteinIntro.tex:3464-3467`): if
$\mathbb{E}[e^{\theta W}] < \infty$ for all $\theta \in (-\delta, \delta)$ ($\delta > 0$), then
$W e^{\theta W}$ is integrable and $m'(\theta) = \mathbb{E}[W e^{\theta W}]$ for all
$\theta \in (-\delta, \delta)$. -/
theorem mgf_integrable_mul_and_hasDerivAt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {δ : ℝ}
    (_hW : AEMeasurable W P) (_hδ : 0 < δ)
    (hint : ∀ θ ∈ Set.Ioo (-δ) δ, Integrable (fun ω ↦ Real.exp (θ * W ω)) P)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (-δ) δ) :
    Integrable (fun ω ↦ W ω * Real.exp (θ * W ω)) P ∧
      HasDerivAt (fun u : ℝ ↦ ∫ ω, Real.exp (u * W ω) ∂P)
        (∫ ω, W ω * Real.exp (θ * W ω) ∂P) θ := by
  have hmem : θ ∈ interior (ProbabilityTheory.integrableExpSet W P) :=
    interior_maximal hint isOpen_Ioo hθ
  refine ⟨?_, ?_⟩
  · simpa [pow_one] using
      ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 1
  · exact ProbabilityTheory.hasDerivAt_mgf hmem

/-! ### Section 4: Example 7.1 (Normal Distribution) -/

/-- **Example 7.1** (`\label{ex211}`, `SteinIntro.tex:3428-3445`): for $Z \sim \mathcal{N}(0, 1)$,
the Mills ratio bound $\mathbb{P}(Z \ge t) \le \frac{e^{-t^2/2}}{t\sqrt{2\pi}}$, the MGF formula
$\mathbb{E}[e^{\theta Z}] = e^{\theta^2/2}$, and the Proposition 7.1 bounds
$\mathbb{P}(Z \ge t) \le e^{\theta^2/2 - \theta t}$ and $\mathbb{P}(Z \ge t) \le e^{-t^2/2}$. -/
theorem stdNormal_concentration
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ : AEMeasurable Z P) (hlaw : P.map Z = stdNormalLaw) :
    (∀ t : ℝ, 0 < t →
        P.real {ω | t ≤ Z ω} ≤ Real.exp (-t ^ 2 / 2) / (t * Real.sqrt (2 * Real.pi))) ∧
      (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * Z ω)) P ∧
        ∫ ω, Real.exp (θ * Z ω) ∂P = Real.exp (θ ^ 2 / 2)) ∧
      (∀ θ t : ℝ, 0 < θ → 0 < t →
        P.real {ω | t ≤ Z ω} ≤ Real.exp (θ ^ 2 / 2 - θ * t)) ∧
      (∀ t : ℝ, 0 < t → P.real {ω | t ≤ Z ω} ≤ Real.exp (-t ^ 2 / 2)) := by
  have hHasLaw : ProbabilityTheory.HasLaw Z (ProbabilityTheory.gaussianReal 0 1) P := ⟨hZ, hlaw⟩
  have hMgf : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * Z ω)) P ∧
      ∫ ω, Real.exp (θ * Z ω) ∂P = Real.exp (θ ^ 2 / 2) := by
    intro θ
    have hval := ProbabilityTheory.mgf_gaussianReal hHasLaw θ
    have hint : Integrable (fun ω ↦ Real.exp (θ * Z ω)) P :=
      ProbabilityTheory.mgf_pos_iff.mp (by rw [hval]; positivity)
    simp only [ProbabilityTheory.mgf, zero_mul, zero_add, NNReal.coe_one, one_mul] at hval
    exact ⟨hint, hval⟩
  have hChernoff : ∀ θ t : ℝ, 0 < θ → 0 < t →
      P.real {ω | t ≤ Z ω} ≤ Real.exp (θ ^ 2 / 2 - θ * t) := by
    intro θ t hθ _ht
    have h1 := ProbabilityTheory.measure_ge_le_exp_mul_mgf t hθ.le (hMgf θ).1
    rw [ProbabilityTheory.mgf, (hMgf θ).2, ← Real.exp_add] at h1
    exact h1.trans_eq (by ring_nf)
  refine ⟨?_, hMgf, hChernoff, ?_⟩
  · intro t ht
    have hpre : {ω | t ≤ Z ω} = Z ⁻¹' Set.Ici t := rfl
    have hreal : P.real {ω | t ≤ Z ω} = 1 - stdNormalCDF t := by
      rw [hpre, ← map_measureReal_apply_of_aemeasurable hZ measurableSet_Ici, hlaw]
      have h1 : ENNReal.ofReal (stdNormalLaw.real (Set.Ici t)) =
          ENNReal.ofReal (∫ x in Set.Ici t, stdNormalPDF x) := by
        rw [ofReal_measureReal (measure_ne_top _ _), stdNormalLaw,
          gaussianReal_apply_eq_integral 0 one_ne_zero (Set.Ici t)]
      have h2 : stdNormalLaw.real (Set.Ici t) = ∫ x in Set.Ici t, stdNormalPDF x :=
        (ENNReal.ofReal_eq_ofReal_iff measureReal_nonneg
          (integral_nonneg fun x ↦ stdNormalPDF_nonneg x)).mp h1
      rw [h2, ← setIntegral_congr_set Ioi_ae_eq_Ici, ← one_sub_stdNormalCDF_eq_integral_Ioi]
    rw [hreal]
    have hmill := mul_one_sub_stdNormalCDF_le t ht.le
    rw [stdNormalPDF_eq] at hmill
    rw [le_div_iff₀ (mul_pos ht (by positivity))]
    have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    calc (1 - stdNormalCDF t) * (t * Real.sqrt (2 * Real.pi))
        = (t * (1 - stdNormalCDF t)) * Real.sqrt (2 * Real.pi) := by ring
      _ ≤ ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) * Real.sqrt (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hmill (by positivity)
      _ = Real.exp (-t ^ 2 / 2) := by field_simp [hsqrt]
  · intro t ht
    exact (hChernoff t t ht ht).trans_eq (by ring_nf)

/-! ### Section 5: Example 7.2 (Poisson Distribution & `ISSUE-EX7.2`) -/

/-- **Example 7.2** (`\label{ex212}`, `SteinIntro.tex:3447-3461`; see `ISSUE-EX7.2`): MGF formula,
Chernoff upper tail bounds, and $o(e^{-c t})$ decay for $Z \sim \mathrm{Po}(\lambda)$
($\lambda > 0$). -/
theorem poisson_concentration
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {Z : Ω → ℕ}
    (hr : 0 < r) (hZ : AEMeasurable Z P) (hlaw : P.map Z = poissonLaw r) :
    let lam : ℝ := (r : ℝ)
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    (∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * (Z ω : ℝ))) P ∧
        ∫ ω, Real.exp (θ * (Z ω : ℝ)) ∂P = Real.exp (lam * (Real.exp θ - 1))) ∧
      (∀ θ t : ℝ, 0 < θ → 0 < t →
        P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤
          Real.exp (lam * (Real.exp θ - 1) - θ * (t + lam))) ∧
      (∀ t : ℝ, 0 < t → P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤ B t) ∧
      (∀ c : ℝ, 0 < c →
        Filter.Tendsto (fun t : ℝ ↦ B t / Real.exp (-c * t)) Filter.atTop (nhds 0)) := by
  dsimp only
  set lam : ℝ := (r : ℝ)
  have hlam : 0 < lam := NNReal.coe_pos.mpr hr
  have hMgf : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * (Z ω : ℝ))) P ∧
      ∫ ω, Real.exp (θ * (Z ω : ℝ)) ∂P = Real.exp (lam * (Real.exp θ - 1)) := by
    intro θ
    let f : ℕ → ℝ := fun n ↦ Real.exp (θ * (n : ℝ))
    have hf_meas : Measurable f := Measurable.of_discrete
    have hsum : HasSum (fun n : ℕ ↦ Real.exp (-lam) * lam ^ n / (n)! * f n)
        (Real.exp (lam * (Real.exp θ - 1))) := by
      have hterm : (fun n : ℕ ↦ Real.exp (-lam) * lam ^ n / (n)! * f n) =
          fun n : ℕ ↦ Real.exp (-lam) * ((lam * Real.exp θ) ^ n / (n)!) := by
        ext n
        dsimp only [f]
        rw [mul_comm θ (n : ℝ), Real.exp_nat_mul, mul_pow]
        ring
      have hval : Real.exp (-lam) * Real.exp (lam * Real.exp θ) =
          Real.exp (lam * (Real.exp θ - 1)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hterm, ← hval]
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (lam * Real.exp θ)).mul_left (Real.exp (-lam))
    have hint_po : Integrable f (ProbabilityTheory.poissonMeasure r) := by
      rw [ProbabilityTheory.integrable_poissonMeasure_iff]
      refine hsum.summable.congr fun n ↦ ?_
      dsimp only [f, lam]
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have hint : Integrable (fun ω ↦ f (Z ω)) P :=
      (integrable_map_measure hf_meas.aestronglyMeasurable hZ).mp (hlaw ▸ hint_po)
    have hint_eq : ∫ ω, f (Z ω) ∂P = Real.exp (lam * (Real.exp θ - 1)) := by
      rw [← integral_map hZ hf_meas.aestronglyMeasurable, hlaw, poissonLaw,
        ProbabilityTheory.integral_poissonMeasure r f]
      simpa only [lam, smul_eq_mul] using hsum.tsum_eq
    exact ⟨hint, hint_eq⟩
  have hTail : ∀ θ t : ℝ, 0 < θ → 0 < t →
      P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤
        Real.exp (lam * (Real.exp θ - 1) - θ * (t + lam)) := by
    intro θ t hθ _ht
    have hset : {ω | t ≤ (Z ω : ℝ) - lam} = {ω | t + lam ≤ (Z ω : ℝ)} := by
      ext ω; simp [le_sub_iff_add_le]
    rw [hset]
    have h1 := ProbabilityTheory.measure_ge_le_exp_mul_mgf (t + lam) hθ.le (hMgf θ).1
    rw [ProbabilityTheory.mgf, (hMgf θ).2, ← Real.exp_add] at h1
    exact h1.trans_eq (by ring_nf)
  have hOpt : ∀ t : ℝ, 0 < t →
      P.real {ω | t ≤ (Z ω : ℝ) - lam} ≤
        Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam)) := by
    intro t ht
    set θ : ℝ := Real.log (1 + t / lam)
    have h1lt : 1 < 1 + t / lam := by linarith [div_pos ht hlam]
    have hθ : 0 < θ := Real.log_pos h1lt
    have hexpθ : Real.exp θ = 1 + t / lam := Real.exp_log (by linarith)
    refine (hTail θ t hθ ht).trans_eq ?_
    congr 1
    rw [hexpθ]
    have hmul : lam * (1 + t / lam - 1) = t := by field_simp [hlam.ne']; ring
    linarith
  refine ⟨hMgf, hTail, hOpt, ?_⟩
  intro c hc
  let E : ℝ → ℝ := fun t ↦
    (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam)) - (-c * t)
  have heq : (fun t : ℝ ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam)) /
        Real.exp (-c * t)) = fun t ↦ Real.exp (E t) := by
    ext t; exact (Real.exp_sub _ _).symm
  rw [heq]
  refine Real.tendsto_exp_atBot.comp ?_
  have hlog_top : Tendsto (fun t : ℝ ↦ Real.log (1 + t / lam)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_const_nhds.add_atTop (tendsto_id.atTop_div_const hlam))
  refine tendsto_atBot_mono' atTop ?_ tendsto_neg_atTop_atBot
  filter_upwards [eventually_ge_atTop (0 : ℝ), hlog_top.eventually_ge_atTop (c + 2)] with t ht0 hlg
  have hlg_nn : 0 ≤ Real.log (1 + t / lam) := by linarith
  have h1 : t * (1 + c - Real.log (1 + t / lam)) ≤ -t := by nlinarith
  have h2 : E t ≤ t * (1 + c - Real.log (1 + t / lam)) := by
    dsimp [E]; nlinarith [mul_nonneg hlam.le hlg_nn]
  exact h2.trans h1

/-- **Example 7.2 lower-order comparison, corrected exponential-rate version** (`\label{ex212}`,
`SteinIntro.tex:3458`; `ISSUE-EX7.2`): for every $\lambda > 0$ and every $c > 1$,
$\lim_{t \to \infty} e^{-c t \log t} / B(\lambda, t) = 0$. -/
theorem poisson_bound_order_corrected {lam c : ℝ} (hlam : 0 < lam) (hc : 1 < c) :
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    Filter.Tendsto (fun t : ℝ ↦ Real.exp (-c * t * Real.log t) / B t) Filter.atTop (nhds 0) := by
  dsimp only
  let E : ℝ → ℝ := fun t ↦
    -c * t * Real.log t - (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
  have heq : (fun t : ℝ ↦
      Real.exp (-c * t * Real.log t) /
        Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))) =
      fun t ↦ Real.exp (E t) := by
    ext t; exact (Real.exp_sub _ _).symm
  rw [heq]
  refine Real.tendsto_exp_atBot.comp ?_
  set K₀ : ℝ := Real.log (1 + 1 / lam)
  have h1lam_pos : 0 < 1 + 1 / lam := by positivity
  have hlog_top : Tendsto (fun t : ℝ ↦ (c - 1) * Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by linarith)
  have hlin_bot : Tendsto (fun t : ℝ ↦ -2 * t + lam * K₀) atTop atBot :=
    (tendsto_id.const_mul_atTop_of_neg (by norm_num)).atBot_add tendsto_const_nhds
  refine tendsto_atBot_mono' atTop ?_ hlin_bot
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hlog_top.eventually_ge_atTop (K₀ + lam + 1)] with t ht1 hclg
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hpos_arg : 0 < 1 + t / lam := by positivity
  have harg_le : 1 + t / lam ≤ t * (1 + 1 / lam) := by
    have : 1 + t / lam ≤ t + t / lam := by linarith
    linarith [(by ring : t + t / lam = t * (1 + 1 / lam))]
  have hlog_le : Real.log (1 + t / lam) ≤ Real.log t + K₀ := by
    have h1 := Real.log_le_log hpos_arg harg_le
    rwa [Real.log_mul ht0.ne' h1lam_pos.ne'] at h1
  have hlog_t_le : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht0).trans (by linarith)
  have hE_eq : E t = -(c - 1) * Real.log t * t +
      t * (Real.log (1 + t / lam) - Real.log t - 1) + lam * Real.log (1 + t / lam) := by
    dsimp [E]; ring
  have h1 : t * (Real.log (1 + t / lam) - Real.log t - 1) ≤ t * (K₀ - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) ht0.le
  have h2 : lam * Real.log (1 + t / lam) ≤ lam * t + lam * K₀ := by
    nlinarith [mul_le_mul_of_nonneg_left hlog_le hlam.le,
      mul_le_mul_of_nonneg_left hlog_t_le hlam.le]
  have h3 : -(c - 1) * Real.log t * t ≤ -(K₀ + lam + 1) * t :=
    mul_le_mul_of_nonneg_right (by linarith) ht0.le
  rw [hE_eq]
  linarith

/-- **Example 7.2 lower-order comparison, restricted to $\lambda > e^{-1}$** (`\label{ex212}`,
`SteinIntro.tex:3458`; `ISSUE-EX7.2`): when $\lambda > e^{-1}$, the Poisson Chernoff bound
$B(\lambda, t)$ satisfies $\lim_{t \to \infty} e^{-t\log t} / B(\lambda, t) = 0$. -/
theorem poisson_bound_order_restricted {lam : ℝ} (hlam_gt : Real.exp (-1) < lam) :
    let B : ℝ → ℝ := fun t ↦
      Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
    Filter.Tendsto (fun t : ℝ ↦ Real.exp (-t * Real.log t) / B t) Filter.atTop (nhds 0) := by
  dsimp only
  have hlam : 0 < lam := (Real.exp_pos (-1)).trans hlam_gt
  have hlog_lam : -1 < Real.log lam := by
    have h := Real.log_lt_log (Real.exp_pos (-1)) hlam_gt
    rwa [Real.log_exp] at h
  set δ : ℝ := (1 + Real.log lam) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let E : ℝ → ℝ := fun t ↦
    -t * Real.log t - (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
  have heq : (fun t : ℝ ↦
      Real.exp (-t * Real.log t) /
        Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))) =
      fun t ↦ Real.exp (E t) := by
    ext t; exact (Real.exp_sub _ _).symm
  rw [heq]
  refine Real.tendsto_exp_atBot.comp ?_
  have hlim_ratio : Tendsto (fun t : ℝ ↦ Real.log (1 / t + 1 / lam) - 1) atTop
      (nhds (-2 * δ)) := by
    have h1 : Tendsto (fun t : ℝ ↦ 1 / t + 1 / lam) atTop (nhds (0 + 1 / lam)) :=
      (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
    rw [zero_add] at h1
    have h2 : Tendsto (fun t : ℝ ↦ Real.log (1 / t + 1 / lam) - 1) atTop
        (nhds (Real.log (1 / lam) - 1)) :=
      (h1.log (by positivity)).sub tendsto_const_nhds
    have hval : Real.log (1 / lam) - 1 = -2 * δ := by
      rw [one_div, Real.log_inv]; dsimp [δ]; ring
    rwa [hval] at h2
  have hev_ratio : ∀ᶠ t : ℝ in atTop, Real.log (1 / t + 1 / lam) - 1 < -δ :=
    hlim_ratio.eventually (gt_mem_nhds (by linarith))
  set a : ℝ := δ / 2
  have ha : 0 < a := by positivity
  set K : ℝ := lam * (a - 1 - Real.log a)
  have hlin_bot : Tendsto (fun t : ℝ ↦ -(δ / 2) * t + K) atTop atBot :=
    (tendsto_id.const_mul_atTop_of_neg (by linarith)).atBot_add tendsto_const_nhds
  refine tendsto_atBot_mono' atTop ?_ hlin_bot
  filter_upwards [eventually_gt_atTop (0 : ℝ), hev_ratio] with t ht hrat
  have hpos_arg : 0 < 1 + t / lam := by positivity
  have hdiv_eq : (1 + t / lam) / t = 1 / t + 1 / lam := by
    field_simp [ht.ne', hlam.ne']
  have hlog_sub : Real.log (1 + t / lam) - Real.log t - 1 =
      Real.log (1 / t + 1 / lam) - 1 := by
    rw [← Real.log_div hpos_arg.ne' ht.ne', hdiv_eq]
  have hlog_upper : Real.log (1 + t / lam) ≤ a * (1 + t / lam) - 1 - Real.log a := by
    have hmul_pos : 0 < a * (1 + t / lam) := mul_pos ha hpos_arg
    have hle := Real.log_le_sub_one_of_pos hmul_pos
    rw [Real.log_mul ha.ne' hpos_arg.ne'] at hle
    linarith
  have hlam_upper : lam * Real.log (1 + t / lam) ≤ (δ / 2) * t + K := by
    have h1 := mul_le_mul_of_nonneg_left hlog_upper hlam.le
    have h2 : lam * (a * (1 + t / lam) - 1 - Real.log a) = (δ / 2) * t + K := by
      dsimp [K, a]
      field_simp [hlam.ne']
      ring
    linarith
  have hE_eq : E t = t * (Real.log (1 + t / lam) - Real.log t - 1) +
      lam * Real.log (1 + t / lam) := by dsimp [E]; ring
  rw [hE_eq, hlog_sub]
  nlinarith [mul_lt_mul_of_pos_left hrat ht]

/-- Negation of the unrestricted Example 7.2 lower-order prose claim (`SteinIntro.tex:3458`;
`ISSUE-EX7.2`): it is **false** that $\lim_{t \to \infty} e^{-t\log t} / B(\lambda, t) = 0$ holds
for all $\lambda > 0$ (refuted at $\lambda = e^{-1}$). -/
theorem not_poisson_bound_order_printed :
    ¬ (∀ {lam : ℝ}, 0 < lam →
      let B : ℝ → ℝ := fun t ↦
        Real.exp (-t * (Real.log (1 + t / lam) - 1) - lam * Real.log (1 + t / lam))
      Filter.Tendsto (fun t : ℝ ↦ Real.exp (-t * Real.log t) / B t) Filter.atTop (nhds 0)) := by
  intro hall
  have hlam : 0 < Real.exp (-1) := Real.exp_pos (-1)
  have htend := hall hlam
  dsimp only at htend
  have hge1 : ∀ᶠ t : ℝ in atTop,
      1 ≤ Real.exp (-t * Real.log t) /
        Real.exp (-t * (Real.log (1 + t / Real.exp (-1)) - 1) -
          Real.exp (-1) * Real.log (1 + t / Real.exp (-1))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    rw [← Real.exp_sub, Real.one_le_exp_iff]
    have hle_arg : t / Real.exp (-1) ≤ 1 + t / Real.exp (-1) := by linarith
    have hlog_ge : Real.log t + 1 ≤ Real.log (1 + t / Real.exp (-1)) := by
      have h1 := Real.log_le_log (div_pos ht0 hlam) hle_arg
      rw [Real.log_div ht0.ne' hlam.ne', Real.log_exp] at h1
      linarith
    have hlog_nn : 0 ≤ Real.log (1 + t / Real.exp (-1)) := by
      have : 0 ≤ Real.log t := Real.log_nonneg ht
      linarith
    nlinarith [mul_nonneg hlam.le hlog_nn]
  have h1le0 : (1 : ℝ) ≤ 0 := ge_of_tendsto htend hge1
  linarith

/-! ### Section 6: Core MGF Differential-Inequality Concentration Engine -/

/-- If a centered random variable $Y$ has finite MGF on all of $\mathbb{R}$ and satisfies
$|\mathbb{E}[Y e^{\theta Y}]| \le |\theta|\,\mathbb{E}[(B Y + C) e^{\theta Y}]$ for all
$\theta \in \mathbb{R}$ with $B \ge 0$ and $C > 0$, then for every $t > 0$,
$\mathbb{P}(Y \ge t) \le \exp(-t^2 / (2 C + 2 B t))$ and
$\mathbb{P}(Y \le -t) \le \exp(-t^2 / (2 C))$ (`SteinIntro.tex:3539-3595, 3781-3806`). -/
theorem mgf_tail_bounds_of_abs_deriv_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {B C : ℝ}
    (hY_int : ∀ θ : ℝ, Integrable (fun ω ↦ Real.exp (θ * Y ω)) P)
    (hMean0 : ∫ ω, Y ω ∂P = 0)
    (hB : 0 ≤ B) (hC : 0 < C)
    (hDiff : ∀ θ : ℝ,
      |∫ ω, Y ω * Real.exp (θ * Y ω) ∂P| ≤
        |θ| * ∫ ω, (B * Y ω + C) * Real.exp (θ * Y ω) ∂P)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ Y ω} ≤ Real.exp (-t ^ 2 / (2 * C + 2 * B * t)) ∧
      P.real {ω | Y ω ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * C)) := by
  have hIntUniv : interior (ProbabilityTheory.integrableExpSet Y P) = Set.univ := by
    rw [interior_eq_univ]
    ext u
    exact ⟨fun _ ↦ trivial, fun _ ↦ hY_int u⟩
  have hmem : ∀ u : ℝ, u ∈ interior (ProbabilityTheory.integrableExpSet Y P) :=
    fun u ↦ hIntUniv ▸ trivial
  have hYmul_int : ∀ u : ℝ, Integrable (fun ω ↦ Y ω * Real.exp (u * Y ω)) P := fun u ↦ by
    simpa [pow_one] using
      ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet (hmem u) 1
  let m' : ℝ → ℝ := fun u ↦ ∫ ω, Y ω * Real.exp (u * Y ω) ∂P
  have hm'_deriv : ∀ u : ℝ, HasDerivAt m' (∫ ω, Y ω ^ 2 * Real.exp (u * Y ω) ∂P) u := fun u ↦ by
    simpa [m', pow_one] using ProbabilityTheory.hasDerivAt_integral_pow_mul_exp_real (hmem u) 1
  have hm'_mono : Monotone m' :=
    monotone_of_hasDerivAt_nonneg hm'_deriv fun u ↦
      integral_nonneg fun ω ↦ mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hm'0 : m' 0 = 0 := by simp [m', hMean0]
  have hLin_eq : ∀ u : ℝ,
      ∫ ω, (B * Y ω + C) * Real.exp (u * Y ω) ∂P =
        B * m' u + C * ProbabilityTheory.mgf Y P u := by
    intro u
    have hpt : (fun ω ↦ (B * Y ω + C) * Real.exp (u * Y ω)) =
        fun ω ↦ B * (Y ω * Real.exp (u * Y ω)) + C * Real.exp (u * Y ω) := by
      ext ω; ring
    rw [hpt, integral_add ((hYmul_int u).const_mul B) ((hY_int u).const_mul C),
      integral_const_mul, integral_const_mul]
    rfl
  have hL_deriv : ∀ u : ℝ,
      HasDerivAt (ProbabilityTheory.cgf Y P) (m' u / ProbabilityTheory.mgf Y P u) u := fun u ↦
    (ProbabilityTheory.hasDerivAt_mgf (hmem u)).log
      (ProbabilityTheory.mgf_pos (hY_int u)).ne'
  refine ⟨?_, ?_⟩
  · set θ : ℝ := t / (C + B * t)
    have hCB_pos : 0 < C + B * t := by nlinarith
    have hθ_pos : 0 < θ := div_pos ht hCB_pos
    have h1Bθ : 1 - B * θ = C / (C + B * t) := by
      dsimp [θ]; field_simp [hCB_pos.ne']; ring
    have h1Bθ_pos : 0 < 1 - B * θ := by rw [h1Bθ]; exact div_pos hC hCB_pos
    let G : ℝ → ℝ := fun u ↦ C * u ^ 2 / (2 * (1 - B * θ)) - ProbabilityTheory.cgf Y P u
    have hG_deriv : ∀ u : ℝ,
        HasDerivAt G (C * u / (1 - B * θ) - m' u / ProbabilityTheory.mgf Y P u) u := by
      intro u
      have hq : HasDerivAt (fun x : ℝ ↦ C * x ^ 2 / (2 * (1 - B * θ)))
          (C * u / (1 - B * θ)) u := by
        convert (((hasDerivAt_pow 2 u).const_mul C).div_const (2 * (1 - B * θ))) using 1
        field_simp [h1Bθ_pos.ne']; ring
      exact hq.fun_sub (hL_deriv u)
    have hG_mono : MonotoneOn G (Set.Icc 0 θ) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 θ)
        (fun u _ ↦ (hG_deriv u).continuousAt.continuousWithinAt)
        (fun u _ ↦ (hG_deriv u).hasDerivWithinAt) fun u hu ↦ ?_
      rw [interior_Icc] at hu
      have hu_pos : 0 < u := hu.1
      have hu_lt : u < θ := hu.2
      have hm'_nn : 0 ≤ m' u := hm'0 ▸ hm'_mono hu_pos.le
      have hmgf_pos : 0 < ProbabilityTheory.mgf Y P u := ProbabilityTheory.mgf_pos (hY_int u)
      have h1Bu_ge : 1 - B * θ ≤ 1 - B * u := by nlinarith
      have h1Bu_pos : 0 < 1 - B * u := h1Bθ_pos.trans_le h1Bu_ge
      have hd := hDiff u
      change |m' u| ≤ |u| * ∫ ω, (B * Y ω + C) * Real.exp (u * Y ω) ∂P at hd
      rw [abs_of_nonneg hm'_nn, abs_of_pos hu_pos, hLin_eq u] at hd
      have hstep1 : m' u / ProbabilityTheory.mgf Y P u ≤ C * u / (1 - B * u) :=
        (div_le_div_iff₀ hmgf_pos h1Bu_pos).mpr (by nlinarith)
      have hstep2 : C * u / (1 - B * u) ≤ C * u / (1 - B * θ) :=
        div_le_div_of_nonneg_left (mul_nonneg hC.le hu_pos.le) h1Bθ_pos h1Bu_ge
      linarith
    have hG0 : G 0 = 0 := by simp [G]
    have hle : G 0 ≤ G θ :=
      hG_mono (left_mem_Icc.mpr hθ_pos.le) (right_mem_Icc.mpr hθ_pos.le) hθ_pos.le
    rw [hG0] at hle
    have hcgf_le : ProbabilityTheory.cgf Y P θ ≤ C * θ ^ 2 / (2 * (1 - B * θ)) := by
      dsimp [G] at hle; linarith
    have hch := ProbabilityTheory.measure_ge_le_exp_cgf t hθ_pos.le (hY_int θ)
    have hexp_le : Real.exp (-θ * t + ProbabilityTheory.cgf Y P θ) ≤
        Real.exp (-θ * t + C * θ ^ 2 / (2 * (1 - B * θ))) :=
      Real.exp_le_exp.mpr (by linarith)
    refine hch.trans (hexp_le.trans_eq ?_)
    congr 1
    rw [h1Bθ]
    dsimp [θ]
    have h2CB : 2 * C + 2 * B * t ≠ 0 := by linarith
    field_simp [hCB_pos.ne', hC.ne', h2CB]
    ring
  · set θ : ℝ := -t / C
    have hθ_neg : θ < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hC
    let H : ℝ → ℝ := fun u ↦ ProbabilityTheory.cgf Y P u - C * u ^ 2 / 2
    have hH_deriv : ∀ u : ℝ,
        HasDerivAt H (m' u / ProbabilityTheory.mgf Y P u - C * u) u := by
      intro u
      have hq : HasDerivAt (fun x : ℝ ↦ C * x ^ 2 / 2) (C * u) u := by
        convert (((hasDerivAt_pow 2 u).const_mul C).div_const 2) using 1; ring
      exact (hL_deriv u).fun_sub hq
    have hH_mono : MonotoneOn H (Set.Icc θ 0) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc θ 0)
        (fun u _ ↦ (hH_deriv u).continuousAt.continuousWithinAt)
        (fun u _ ↦ (hH_deriv u).hasDerivWithinAt) fun u hu ↦ ?_
      rw [interior_Icc] at hu
      have hu_neg : u < 0 := hu.2
      have hm'_le : m' u ≤ 0 := hm'0 ▸ hm'_mono hu_neg.le
      have hmgf_pos : 0 < ProbabilityTheory.mgf Y P u := ProbabilityTheory.mgf_pos (hY_int u)
      have hd := hDiff u
      change |m' u| ≤ |u| * ∫ ω, (B * Y ω + C) * Real.exp (u * Y ω) ∂P at hd
      rw [abs_of_nonpos hm'_le, abs_of_neg hu_neg, hLin_eq u] at hd
      have hBm' : (-u) * (B * m' u) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hu_neg.le)
          (mul_nonpos_of_nonneg_of_nonpos hB hm'_le)
      have hCu : C * u * ProbabilityTheory.mgf Y P u ≤ m' u := by nlinarith
      have hdiv : C * u ≤ m' u / ProbabilityTheory.mgf Y P u :=
        (le_div_iff₀ hmgf_pos).mpr hCu
      linarith
    have hH0 : H 0 = 0 := by simp [H]
    have hle : H θ ≤ H 0 :=
      hH_mono (left_mem_Icc.mpr hθ_neg.le) (right_mem_Icc.mpr hθ_neg.le) hθ_neg.le
    rw [hH0] at hle
    have hcgf_le : ProbabilityTheory.cgf Y P θ ≤ C * θ ^ 2 / 2 := by
      dsimp [H] at hle; linarith
    have hch := ProbabilityTheory.measure_le_le_exp_cgf (-t) hθ_neg.le (hY_int θ)
    have hexp_le : Real.exp (-θ * -t + ProbabilityTheory.cgf Y P θ) ≤
        Real.exp (-θ * -t + C * θ ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    refine hch.trans (hexp_le.trans_eq ?_)
    congr 1
    dsimp [θ]
    field_simp [hC.ne']
    ring

end SteinMethod
