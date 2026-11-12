/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Monotone.BoolCoupling
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Covariance

/-!
# Lemma 4.18: Monotone Coupling Characterizations
(`Formalization.PoissonSizeBias.Monotone.Lemma4_18`)

Formalizes Lemma 4.18 (`\label{lem121}`, `SteinIntro.tex:2404-2423`): `lem4_18_cond` and the
auxiliary mixture-indicator characterization `monotone_coupling_mixture_iff`.
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-- Auxiliary mixture-indicator characterization of monotone coupling on $\{0, 1\}^n$: for random
vectors $X, Y \in \{0, 1\}^n$ and independent auxiliary indicators $I \sim \mathrm{Ber}(p)$,
$J = 1 - I$, the following are equivalent:
1. There exists a coupling $(X', Y')$ with $X' \stackrel{d}{=} X$, $Y' \stackrel{d}{=} Y$, and
   $X'_i \le Y'_i$ pointwise.
2. For every increasing function $f : \mathbb{R}^n \to \{0, 1\}$,
   $\mathbb{E}[f(X)] \le \mathbb{E}[f(Y)]$.
3. For every increasing function $f : \mathbb{R}^n \to \{0, 1\}$,
   $\mathrm{Cov}(f(X)I + f(Y)J, J) \ge 0$.
(For the conditional-distribution formulation of Lemma 4.18 `\label{lem121}` in
`SteinIntro.tex:2404-2423`, see `lem4_18_cond`.) -/
theorem monotone_coupling_mixture_iff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X Y : Fin n → Ω → ℝ) (I J : Ω → ℝ)
    (hX : ∀ i : Fin n, Measurable (X i))
    (hY : ∀ i : Fin n, Measurable (Y i))
    (hI : Measurable I) (hJ : Measurable J)
    (hX01 : ∀ (i : Fin n) (ω : Ω), X i ω = 0 ∨ X i ω = 1)
    (hY01 : ∀ (i : Fin n) (ω : Ω), Y i ω = 0 ∨ Y i ω = 1)
    (hI01 : ∀ ω : Ω, I ω = 0 ∨ I ω = 1)
    (hIJ : ∀ ω : Ω, J ω = 1 - I ω)
    (hI0 : 0 < ∫ ω, I ω ∂P) (hI1 : ∫ ω, I ω ∂P < 1)
    (hXI : IndepFun (fun ω i ↦ X i ω) I P)
    (hYJ : IndepFun (fun ω i ↦ Y i ω) J P) :
    let c1 : Prop :=
      ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : @Measure Ω' mΩ')
        (X' Y' : Fin n → Ω' → ℝ),
        @IsProbabilityMeasure Ω' mΩ' P' ∧
        (∀ i : Fin n, @Measurable Ω' ℝ mΩ' _ (X' i)) ∧
        (∀ i : Fin n, @Measurable Ω' ℝ mΩ' _ (Y' i)) ∧
        @Measure.map Ω' (Fin n → ℝ) mΩ' _ (fun ω' i ↦ X' i ω') P' =
          Measure.map (fun ω i ↦ X i ω) P ∧
        @Measure.map Ω' (Fin n → ℝ) mΩ' _ (fun ω' i ↦ Y' i ω') P' =
          Measure.map (fun ω i ↦ Y i ω) P ∧
        ∀ (i : Fin n) (ω' : Ω'), X' i ω' ≤ Y' i ω'
    let c2 : Prop :=
      ∀ f : (Fin n → ℝ) → ℝ, IsIncreasing f → Measurable f →
        (∀ x : Fin n → ℝ, f x = 0 ∨ f x = 1) →
        ∫ ω, f (fun i ↦ X i ω) ∂P ≤ ∫ ω, f (fun i ↦ Y i ω) ∂P
    let c3 : Prop :=
      ∀ f : (Fin n → ℝ) → ℝ, IsIncreasing f → Measurable f →
        (∀ x : Fin n → ℝ, f x = 0 ∨ f x = 1) →
        0 ≤ cov[fun ω ↦ f (fun i ↦ X i ω) * I ω + f (fun i ↦ Y i ω) * J ω, J; P]
    (c1 ↔ c2) ∧ (c2 ↔ c3) := by
  intro c1 c2 c3
  have hX_vec : Measurable (fun ω i ↦ X i ω) := measurable_pi_iff.mpr hX
  have hY_vec : Measurable (fun ω i ↦ Y i ω) := measurable_pi_iff.mpr hY
  constructor
  · -- `(c1 ↔ c2)`
    constructor
    · -- `c1 → c2`
      rintro ⟨Ω', mΩ', P', X', Y', hP', hX', hY', hmapX, hmapY, hle⟩ f hf_inc hf_meas hf01
      have hX'_vec : Measurable (fun ω' i ↦ X' i ω') := measurable_pi_iff.mpr hX'
      have hY'_vec : Measurable (fun ω' i ↦ Y' i ω') := measurable_pi_iff.mpr hY'
      have h_eqX : ∫ ω, f (fun i ↦ X i ω) ∂P = ∫ ω', f (fun i ↦ X' i ω') ∂P' := by
        rw [← integral_map hX_vec.aemeasurable hf_meas.aestronglyMeasurable, ← hmapX,
          integral_map hX'_vec.aemeasurable hf_meas.aestronglyMeasurable]
      have h_eqY : ∫ ω, f (fun i ↦ Y i ω) ∂P = ∫ ω', f (fun i ↦ Y' i ω') ∂P' := by
        rw [← integral_map hY_vec.aemeasurable hf_meas.aestronglyMeasurable, ← hmapY,
          integral_map hY'_vec.aemeasurable hf_meas.aestronglyMeasurable]
      rw [h_eqX, h_eqY]
      have hintX' : Integrable (fun ω' ↦ f (fun i ↦ X' i ω')) P' :=
        Integrable.of_bound (hf_meas.comp hX'_vec).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω' ↦
            norm_le_one_of_zero_or_one (hf01 (fun i ↦ X' i ω')))
      have hintY' : Integrable (fun ω' ↦ f (fun i ↦ Y' i ω')) P' :=
        Integrable.of_bound (hf_meas.comp hY'_vec).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω' ↦
            norm_le_one_of_zero_or_one (hf01 (fun i ↦ Y' i ω')))
      exact integral_mono hintX' hintY' fun ω' ↦ hf_inc _ _ (fun i ↦ hle i ω')
    · -- `c2 → c1`
      intro hc2
      let p : (Fin n → Bool) → ℝ :=
        fun x ↦ P.real {ω : Ω | (fun i ↦ X i ω) = ofBoolVec x}
      let q : (Fin n → Bool) → ℝ :=
        fun y ↦ P.real {ω : Ω | (fun i ↦ Y i ω) = ofBoolVec y}
      have hp_nonneg : ∀ x, 0 ≤ p x := fun _ ↦ measureReal_nonneg
      have hq_nonneg : ∀ y, 0 ≤ q y := fun _ ↦ measureReal_nonneg
      have hp_sum : ∑ x, p x = 1 := sum_probReal_eq_ofBoolVec P X hX hX01
      have hq_sum : ∑ y, q y = 1 := sum_probReal_eq_ofBoolVec P Y hY hY01
      have h_ind : ∀ g : (Fin n → Bool) → ℝ, Monotone g → (∀ x, g x = 0 ∨ g x = 1) →
          ∑ x, g x * p x ≤ ∑ y, g y * q y := by
        intro g hg hg01
        have h_ineq := hc2 (liftFromBool g) (isIncreasing_liftFromBool hg)
          (measurable_liftFromBool g) (fun z ↦ by rw [liftFromBool_eq]; exact hg01 _)
        rwa [integral_liftFromBool_eq P X hX hX01 g,
          integral_liftFromBool_eq P Y hY hY01 g] at h_ineq
      have h_mono : ∀ g : (Fin n → Bool) → ℝ, Monotone g →
          ∑ x, g x * p x ≤ ∑ y, g y * q y := fun g hg ↦
        sum_mul_le_of_monotone_bool p q hp_sum hq_sum h_ind (Finset.univ.image g).card g hg le_rfl
      obtain ⟨w, hw0, hw1, hwx, hwy⟩ :=
        exists_monotone_weights_bool p q hp_nonneg hp_sum hq_nonneg hq_sum h_mono
      let R := BoolOrderPairs n
      let P' : Measure R := ∑ r : R, ENNReal.ofReal (w r) • Measure.dirac r
      let X' : Fin n → R → ℝ := fun i r ↦ if r.1.1 i then 1 else 0
      let Y' : Fin n → R → ℝ := fun i r ↦ if r.1.2 i then 1 else 0
      have h_dirac_univ : ∀ r : R, (Measure.dirac r : Measure R) Set.univ = 1 :=
        fun r ↦ Measure.dirac_apply_of_mem (Set.mem_univ r)
      have h_dirac_apply : ∀ (r : R) (A : Set R),
          (Measure.dirac r : Measure R) A = A.indicator 1 r :=
        fun r _ ↦ Measure.dirac_apply' r trivial
      have hP' : IsProbabilityMeasure P' := by
        constructor
        simp only [P', Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
          h_dirac_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ ↦ hw0 r), hw1, ENNReal.ofReal_one]
      have hX'_meas : ∀ i : Fin n, Measurable (X' i) := fun _ _ _ ↦ trivial
      have hY'_meas : ∀ i : Fin n, Measurable (Y' i) := fun _ _ _ ↦ trivial
      refine ⟨R, inferInstance, P', X', Y', hP', hX'_meas, hY'_meas, ?_, ?_, ?_⟩
      · ext s hs
        have hX'_vec : Measurable (fun r : R ↦ (fun i ↦ X' i r)) := fun _ _ ↦ trivial
        rw [Measure.map_apply hX'_vec hs, measure_map_zero_one_apply P X hX hX01 hs]
        simp only [P', Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
          h_dirac_apply, Set.indicator_apply, Set.mem_preimage, Pi.one_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        have h_part : ∀ x : Fin n → Bool,
            (if ofBoolVec x ∈ s then ENNReal.ofReal (p x) else 0) =
              ∑ r : R, if r.1.1 = x then
                (if ofBoolVec r.1.1 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 := by
          intro x
          by_cases hmem : ofBoolVec x ∈ s
          · simp only [hmem, ↓reduceIte, ← hwx x]
            rw [ENNReal.ofReal_sum_of_nonneg]
            · refine Finset.sum_congr rfl fun r _ ↦ ?_
              by_cases hrx : r.1.1 = x
              · simp [hrx, hmem]
              · simp [hrx]
            · intro r _; split_ifs <;> simp [hw0 r]
          · simp only [hmem, ↓reduceIte]
            symm
            refine Finset.sum_eq_zero fun r _ ↦ ?_
            by_cases hrx : r.1.1 = x
            · simp [hrx, hmem]
            · simp [hrx]
        have h_rhs : (∑ x : Fin n → Bool,
            if ofBoolVec x ∈ s then
              ENNReal.ofReal (P.real {ω : Ω | (fun i ↦ X i ω) = ofBoolVec x})
            else 0) =
            ∑ x : Fin n → Bool,
              ∑ r : R, if r.1.1 = x then
                (if ofBoolVec r.1.1 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 :=
          Finset.sum_congr rfl fun x _ ↦ h_part x
        rw [h_rhs, Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [Finset.sum_ite_eq Finset.univ r.1.1]
        simp only [Finset.mem_univ, ↓reduceIte]
        rfl
      · ext s hs
        have hY'_vec : Measurable (fun r : R ↦ (fun i ↦ Y' i r)) := fun _ _ ↦ trivial
        rw [Measure.map_apply hY'_vec hs, measure_map_zero_one_apply P Y hY hY01 hs]
        simp only [P', Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
          h_dirac_apply, Set.indicator_apply, Set.mem_preimage, Pi.one_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        have h_part : ∀ y : Fin n → Bool,
            (if ofBoolVec y ∈ s then ENNReal.ofReal (q y) else 0) =
              ∑ r : R, if r.1.2 = y then
                (if ofBoolVec r.1.2 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 := by
          intro y
          by_cases hmem : ofBoolVec y ∈ s
          · simp only [hmem, ↓reduceIte, ← hwy y]
            rw [ENNReal.ofReal_sum_of_nonneg]
            · refine Finset.sum_congr rfl fun r _ ↦ ?_
              by_cases hry : r.1.2 = y
              · simp [hry, hmem]
              · simp [hry]
            · intro r _; split_ifs <;> simp [hw0 r]
          · simp only [hmem, ↓reduceIte]
            symm
            refine Finset.sum_eq_zero fun r _ ↦ ?_
            by_cases hry : r.1.2 = y
            · simp [hry, hmem]
            · simp [hry]
        have h_rhs : (∑ y : Fin n → Bool,
            if ofBoolVec y ∈ s then
              ENNReal.ofReal (P.real {ω : Ω | (fun i ↦ Y i ω) = ofBoolVec y})
            else 0) =
            ∑ y : Fin n → Bool,
              ∑ r : R, if r.1.2 = y then
                (if ofBoolVec r.1.2 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 :=
          Finset.sum_congr rfl fun y _ ↦ h_part y
        rw [h_rhs, Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [Finset.sum_ite_eq Finset.univ r.1.2]
        simp only [Finset.mem_univ, ↓reduceIte]
        rfl
      · intro i r
        have h_le : r.1.1 i ≤ r.1.2 i := r.2 i
        unfold X' Y'
        cases h1 : r.1.1 i <;> cases h2 : r.1.2 i
        · exact le_rfl
        · exact zero_le_one
        · rw [h1, h2] at h_le; exact False.elim (Bool.noConfusion (h_le rfl))
        · exact le_rfl
  · -- `(c2 ↔ c3)`
    have hJ01 : ∀ ω : Ω, J ω = 0 ∨ J ω = 1 := by
      intro ω
      rw [hIJ ω]
      rcases hI01 ω with h0 | h1
      · right; linarith
      · left; linarith
    have hintI : Integrable I P :=
      Integrable.of_bound hI.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω ↦ norm_le_one_of_zero_or_one (hI01 ω))
    have hintJ : Integrable J P :=
      Integrable.of_bound hJ.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω ↦ norm_le_one_of_zero_or_one (hJ01 ω))
    have hmemJ : MemLp J 2 P :=
      (memLp_top_of_bound hJ.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω ↦
          norm_le_one_of_zero_or_one (hJ01 ω))).mono_exponent le_top
    have h_int_J : ∫ ω, J ω ∂P = 1 - ∫ ω, I ω ∂P := by
      have h_eq : J = fun ω ↦ 1 - I ω := funext hIJ
      rw [h_eq, integral_sub (integrable_const 1) hintI, integral_const, probReal_univ,
        smul_eq_mul, mul_one]
    have hJ0 : 0 < ∫ ω, J ω ∂P := by linarith
    have h_cov_id : ∀ f : (Fin n → ℝ) → ℝ, Measurable f →
        (∀ x : Fin n → ℝ, f x = 0 ∨ f x = 1) →
        cov[fun ω ↦ f (fun i ↦ X i ω) * I ω + f (fun i ↦ Y i ω) * J ω, J; P] =
          (∫ ω, f (fun i ↦ Y i ω) ∂P - ∫ ω, f (fun i ↦ X i ω) ∂P) *
            (∫ ω, I ω ∂P) * (∫ ω, J ω ∂P) := by
      intro f hf_meas hf01
      let FX : Ω → ℝ := fun ω ↦ f (fun i ↦ X i ω)
      let FY : Ω → ℝ := fun ω ↦ f (fun i ↦ Y i ω)
      let Z : Ω → ℝ := fun ω ↦ FX ω * I ω + FY ω * J ω
      have hFX_meas : Measurable FX := hf_meas.comp hX_vec
      have hFY_meas : Measurable FY := hf_meas.comp hY_vec
      have hZ_meas : Measurable Z := (hFX_meas.mul hI).add (hFY_meas.mul hJ)
      have hZ_bound : ∀ ω : Ω, ‖Z ω‖ ≤ 2 := by
        intro ω
        unfold Z FX FY
        rw [hIJ ω]
        rcases hf01 (fun i ↦ X i ω) with hx | hx <;>
          rcases hf01 (fun i ↦ Y i ω) with hy | hy <;>
          rcases hI01 ω with hi | hi <;>
          simp [hx, hy, hi]
      have hmemZ : MemLp Z 2 P :=
        (memLp_top_of_bound hZ_meas.aestronglyMeasurable 2
          (Filter.Eventually.of_forall hZ_bound)).mono_exponent le_top
      rw [covariance_eq_sub hmemZ hmemJ]
      have hZJ : (fun ω ↦ Z ω * J ω) = (fun ω ↦ FY ω * J ω) := by
        funext ω
        unfold Z
        rw [hIJ ω]
        rcases hI01 ω with hi | hi
        · simp [hi]
        · simp [hi]
      have hintFXI : Integrable (fun ω ↦ FX ω * I ω) P :=
        Integrable.of_bound (hFX_meas.mul hI).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω ↦ by
            unfold FX
            rcases hf01 (fun i ↦ X i ω) with hx | hx <;>
              rcases hI01 ω with hi | hi <;> simp [hx, hi])
      have hintFYJ : Integrable (fun ω ↦ FY ω * J ω) P :=
        Integrable.of_bound (hFY_meas.mul hJ).aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω ↦ by
            unfold FY
            rcases hf01 (fun i ↦ Y i ω) with hy | hy <;>
              rcases hJ01 ω with hj | hj <;> simp [hy, hj])
      have h_ind_XI : ∫ ω, FX ω * I ω ∂P = (∫ ω, FX ω ∂P) * (∫ ω, I ω ∂P) :=
        (hXI.comp hf_meas measurable_id).integral_fun_mul_eq_mul_integral
          hFX_meas.aestronglyMeasurable hI.aestronglyMeasurable
      have h_ind_YJ : ∫ ω, FY ω * J ω ∂P = (∫ ω, FY ω ∂P) * (∫ ω, J ω ∂P) :=
        (hYJ.comp hf_meas measurable_id).integral_fun_mul_eq_mul_integral
          hFY_meas.aestronglyMeasurable hJ.aestronglyMeasurable
      have h_int_Z : ∫ ω, Z ω ∂P = (∫ ω, FX ω ∂P) * (∫ ω, I ω ∂P) +
          (∫ ω, FY ω ∂P) * (∫ ω, J ω ∂P) := by
        unfold Z
        rw [integral_add hintFXI hintFYJ, h_ind_XI, h_ind_YJ]
      change ∫ ω, Z ω * J ω ∂P - (∫ ω, Z ω ∂P) * (∫ ω, J ω ∂P) = _
      rw [hZJ, h_ind_YJ, h_int_Z, h_int_J]
      ring
    constructor
    · intro hc2 f hf_inc hf_meas hf01
      rw [h_cov_id f hf_meas hf01]
      have hle := hc2 f hf_inc hf_meas hf01
      exact mul_nonneg (mul_nonneg (by linarith) (le_of_lt hI0)) (le_of_lt hJ0)
    · intro hc3 f hf_inc hf_meas hf01
      have hnonneg := hc3 f hf_inc hf_meas hf01
      rw [h_cov_id f hf_meas hf01] at hnonneg
      have hpos : 0 < (∫ ω, I ω ∂P) * (∫ ω, J ω ∂P) := mul_pos hI0 hJ0
      have h_diff :
          0 ≤ ∫ ω, f (fun i ↦ Y i ω) ∂P - ∫ ω, f (fun i ↦ X i ω) ∂P := by
        nlinarith
      linarith

private def natOfBoolVec {n : ℕ} (x : Fin n → Bool) (j : Fin n) : ℕ :=
  if x j then 1 else 0

private lemma monotone_natOfBoolVec {n : ℕ} : Monotone (@natOfBoolVec n) := by
  intro a b hab j
  unfold natOfBoolVec
  cases h1 : a j <;> cases h2 : b j
  · exact le_rfl
  · exact zero_le_one
  · have h := hab j; rw [h1, h2] at h; exact False.elim (Bool.noConfusion (h rfl))
  · exact le_rfl

private lemma decide_one_le_natOfBoolVec {n : ℕ} (x : Fin n → Bool) :
    (fun j ↦ decide (1 ≤ natOfBoolVec x j)) = x := by
  funext j
  unfold natOfBoolVec
  cases x j <;> simp

private lemma eq_natOfBoolVec_decide {n : ℕ} {y : Fin n → ℕ}
    (hy : ∀ j : Fin n, y j = 0 ∨ y j = 1) :
    y = natOfBoolVec (fun j ↦ decide (1 ≤ y j)) := by
  funext j
  unfold natOfBoolVec
  rcases hy j with h0 | h1
  · simp [h0]
  · simp [h1]

private lemma integrable_and_integral_nat_zero_one {n : ℕ} {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    {V : Ω₀ → Fin n → ℕ} (hV : Measurable V)
    (hV01 : ∀ᵐ ω ∂P₀, ∀ j : Fin n, V ω j = 0 ∨ V ω j = 1)
    (φ : (Fin n → ℕ) → ℝ) :
    Integrable (fun ω ↦ φ (V ω)) P₀ ∧
      ∫ ω, φ (V ω) ∂P₀ =
        ∑ x : Fin n → Bool, φ (natOfBoolVec x) * P₀.real {ω | V ω = natOfBoolVec x} := by
  have h_ae : (fun ω ↦ φ (V ω)) =ᵐ[P₀]
      fun ω ↦ ∑ x : Fin n → Bool,
        φ (natOfBoolVec x) *
          {ω' | V ω' = natOfBoolVec x}.indicator (fun _ ↦ (1 : ℝ)) ω := by
    filter_upwards [hV01] with ω hω
    let x₀ : Fin n → Bool := fun j ↦ decide (1 ≤ V ω j)
    have hx₀ : V ω = natOfBoolVec x₀ := eq_natOfBoolVec_decide hω
    rw [Finset.sum_eq_single x₀]
    · simp [hx₀]
    · intro x _ hxne
      have hnot : ω ∉ {ω' | V ω' = natOfBoolVec x} := by
        intro hmem
        apply hxne
        have h_eq : natOfBoolVec x₀ = natOfBoolVec x := hx₀.symm.trans hmem
        have h_dec := congr_arg (fun y : Fin n → ℕ ↦ (fun j ↦ decide (1 ≤ y j))) h_eq
        rw [decide_one_le_natOfBoolVec, decide_one_le_natOfBoolVec] at h_dec
        exact h_dec.symm
      simp [Set.indicator_of_notMem hnot]
    · intro habs; exact False.elim (habs (Finset.mem_univ x₀))
  have h_meas_x : ∀ x : Fin n → Bool, MeasurableSet {ω' | V ω' = natOfBoolVec x} :=
    fun x ↦ hV (measurableSet_singleton (natOfBoolVec x))
  have h_sum_int : Integrable (fun ω ↦ ∑ x : Fin n → Bool,
      φ (natOfBoolVec x) *
        {ω' | V ω' = natOfBoolVec x}.indicator (fun _ ↦ (1 : ℝ)) ω) P₀ := by
    refine integrable_finsetSum Finset.univ fun x _ ↦ ?_
    exact ((integrable_const (1 : ℝ)).indicator (h_meas_x x)).const_mul _
  refine ⟨h_sum_int.congr h_ae.symm, ?_⟩
  rw [integral_congr_ae h_ae,
    integral_finsetSum Finset.univ fun x _ ↦
      ((integrable_const (1 : ℝ)).indicator (h_meas_x x)).const_mul _]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [integral_const_mul]
  change φ (natOfBoolVec x) *
      ∫ ω, {ω' | V ω' = natOfBoolVec x}.indicator 1 ω ∂P₀ = _
  rw [integral_indicator_one (h_meas_x x)]

private lemma measure_map_nat_zero_one_apply {n : ℕ} {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    {V : Ω₀ → Fin n → ℕ} (hV : Measurable V)
    (hV01 : ∀ᵐ ω ∂P₀, ∀ j : Fin n, V ω j = 0 ∨ V ω j = 1)
    (s : Set (Fin n → ℕ)) :
    (P₀.map V) s =
      ∑ x : Fin n → Bool,
        if natOfBoolVec x ∈ s then
          ENNReal.ofReal (P₀.real {ω | V ω = natOfBoolVec x})
        else 0 := by
  have : IsProbabilityMeasure (P₀.map V) := isProbabilityMeasure_map' hV.aemeasurable
  have h_int := (integrable_and_integral_nat_zero_one P₀ hV hV01
    (s.indicator (1 : (Fin n → ℕ) → ℝ))).2
  have h_lhs :
      ∫ ω, s.indicator (1 : (Fin n → ℕ) → ℝ) (V ω) ∂P₀ = (P₀.map V).real s := by
    change ∫ ω, (V ⁻¹' s).indicator (1 : Ω₀ → ℝ) ω ∂P₀ = (P₀.map V).real s
    rw [integral_indicator_one (hV .of_discrete), map_measureReal_apply hV .of_discrete]
  rw [h_lhs] at h_int
  have h_ofReal := congr_arg ENNReal.ofReal h_int
  rw [ofReal_measureReal] at h_ofReal
  rw [h_ofReal, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hxs : natOfBoolVec x ∈ s
    · simp [hxs]
    · simp [hxs]
  · intro x _
    by_cases hxs : natOfBoolVec x ∈ s
    · simp [hxs, measureReal_nonneg]
    · simp [hxs]

/-- **Lemma 4.18** (`\label{lem121}`, `SteinIntro.tex:2404-2423`): for $\{0, 1\}$-indicators
$\mathbf{X} = (X_1, \dots, X_n)$ and $\mathbf{X}^{(i)}$ having the conditional distribution of
$\mathbf{X}$ given $X_i = 1$ (assuming $\mathbb{P}(X_i = 1) > 0$), the following are equivalent:
(1) there exists a coupling $(\hat{\mathbf{X}}, \hat{\mathbf{X}}^{(i)})$ of $\mathbf{X}$ and
    $\mathbf{X}^{(i)}$ such that $\hat{X}_j \le \hat{X}_j^{(i)}$ almost surely for all $j$;
(2) for every increasing indicator function $\phi : \mathbb{N}^n \to \mathbb{R}$,
    $\mathbb{E}[\phi(\mathbf{X})] \le \mathbb{E}[\phi(\mathbf{X}^{(i)})]$;
(3) for every increasing indicator function $\phi : \mathbb{N}^n \to \mathbb{R}$,
    $0 \le \operatorname{Cov}(X_i, \phi(\mathbf{X}))$. -/
theorem lem4_18_cond
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {X_cond : Fin n → Ω' → ℕ} (i : Fin n)
    (hX : ∀ j : Fin n, Measurable (X j))
    (hX01 : ∀ j : Fin n, ∀ᵐ ω ∂P, X j ω = 0 ∨ X j ω = 1)
    (hX_cond : ∀ j : Fin n, Measurable (X_cond j))
    (hp_pos : 0 < P.real {ω | X i ω = 1})
    (h_law : P'.map (fun ω' j ↦ X_cond j ω') =
      (ProbabilityTheory.cond P {ω | X i ω = 1}).map (fun ω j ↦ X j ω)) :
    let c1 : Prop :=
      ∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
        (Xc Xc_cond : Ωc → Fin n → ℕ),
        Measurable Xc ∧ Measurable Xc_cond ∧
        Pc.map Xc = P.map (fun ω j ↦ X j ω) ∧
        Pc.map Xc_cond = P'.map (fun ω' j ↦ X_cond j ω') ∧
        ∀ j : Fin n, ∀ᵐ ωc ∂Pc, Xc ωc j ≤ Xc_cond ωc j
    let c2 : Prop :=
      ∀ φ : (Fin n → ℕ) → ℝ,
        Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
          ∫ ω, φ (fun j ↦ X j ω) ∂P ≤ ∫ ω', φ (fun j ↦ X_cond j ω') ∂P'
    let c3 : Prop :=
      ∀ φ : (Fin n → ℕ) → ℝ,
        Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
          0 ≤ ProbabilityTheory.covariance
            (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X j ω)) P
    (c1 ↔ c2) ∧ (c2 ↔ c3) := by
  intro c1 c2 c3
  have hX_vec : Measurable (fun ω j ↦ X j ω) := measurable_pi_iff.mpr hX
  have hX_cond_vec : Measurable (fun ω' j ↦ X_cond j ω') := measurable_pi_iff.mpr hX_cond
  have hX_all01 : ∀ᵐ ω ∂P, ∀ j : Fin n, X j ω = 0 ∨ X j ω = 1 :=
    Filter.eventually_all.mpr hX01
  have hX_cond_all01 : ∀ᵐ ω' ∂P', ∀ j : Fin n, X_cond j ω' = 0 ∨ X_cond j ω' = 1 := by
    let S01 : Set (Fin n → ℕ) := {y | ∀ j : Fin n, y j = 0 ∨ y j = 1}
    have hP0 : P ((fun ω j ↦ X j ω) ⁻¹' S01ᶜ) = 0 := hX_all01
    have hcond0 : (ProbabilityTheory.cond P {ω | X i ω = 1})
        ((fun ω j ↦ X j ω) ⁻¹' S01ᶜ) = 0 :=
      ProbabilityTheory.cond_absolutelyContinuous hP0
    have hmap_eq : P' ((fun ω' j ↦ X_cond j ω') ⁻¹' S01ᶜ) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}) ((fun ω j ↦ X j ω) ⁻¹' S01ᶜ) := by
      rw [← Measure.map_apply hX_cond_vec .of_discrete, h_law,
        Measure.map_apply hX_vec .of_discrete]
    exact hmap_eq.trans hcond0
  constructor
  · -- `c1 ↔ c2`
    constructor
    · rintro ⟨Ωc, mΩc, Pc, hPc, Xc, Xc_cond, hXc, hXc_cond, hmapX, hmapXc, hle⟩ φ hφ_mono _
      have h_eqX : ∫ ω, φ (fun j ↦ X j ω) ∂P = ∫ ωc, φ (Xc ωc) ∂Pc := by
        rw [← integral_map hX_vec.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
          ← hmapX, integral_map hXc.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
      have h_eqXc :
          ∫ ω', φ (fun j ↦ X_cond j ω') ∂P' = ∫ ωc, φ (Xc_cond ωc) ∂Pc := by
        rw [← integral_map hX_cond_vec.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
          ← hmapXc,
          integral_map hXc_cond.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
      rw [h_eqX, h_eqXc]
      have hXc_01 : ∀ᵐ ωc ∂Pc, ∀ j : Fin n, Xc ωc j = 0 ∨ Xc ωc j = 1 := by
        let S01 : Set (Fin n → ℕ) := {y | ∀ j : Fin n, y j = 0 ∨ y j = 1}
        change Pc (Xc ⁻¹' S01ᶜ) = 0
        rw [← Measure.map_apply hXc .of_discrete, hmapX, Measure.map_apply hX_vec .of_discrete]
        exact hX_all01
      have hXc_cond_01 :
          ∀ᵐ ωc ∂Pc, ∀ j : Fin n, Xc_cond ωc j = 0 ∨ Xc_cond ωc j = 1 := by
        let S01 : Set (Fin n → ℕ) := {y | ∀ j : Fin n, y j = 0 ∨ y j = 1}
        change Pc (Xc_cond ⁻¹' S01ᶜ) = 0
        rw [← Measure.map_apply hXc_cond .of_discrete, hmapXc,
          Measure.map_apply hX_cond_vec .of_discrete]
        exact hX_cond_all01
      refine integral_mono_ae
        (integrable_and_integral_nat_zero_one Pc hXc hXc_01 φ).1
        (integrable_and_integral_nat_zero_one Pc hXc_cond hXc_cond_01 φ).1 ?_
      filter_upwards [Filter.eventually_all.mpr hle] with ωc hωc
      exact hφ_mono hωc
    · intro hc2
      let p : (Fin n → Bool) → ℝ :=
        fun x ↦ P.real {ω : Ω | (fun j ↦ X j ω) = natOfBoolVec x}
      let q : (Fin n → Bool) → ℝ :=
        fun y ↦ P'.real {ω' : Ω' | (fun j ↦ X_cond j ω') = natOfBoolVec y}
      have hp_nonneg : ∀ x, 0 ≤ p x := fun _ ↦ measureReal_nonneg
      have hq_nonneg : ∀ y, 0 ≤ q y := fun _ ↦ measureReal_nonneg
      have hp_sum : ∑ x, p x = 1 := by
        have h := (integrable_and_integral_nat_zero_one P hX_vec hX_all01 (fun _ ↦ 1)).2
        simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
        exact h.symm
      have hq_sum : ∑ y, q y = 1 := by
        have h := (integrable_and_integral_nat_zero_one
          P' hX_cond_vec hX_cond_all01 (fun _ ↦ 1)).2
        simp only [one_mul, integral_const, probReal_univ, smul_eq_mul, mul_one] at h
        exact h.symm
      have h_ind : ∀ g : (Fin n → Bool) → ℝ, Monotone g → (∀ x, g x = 0 ∨ g x = 1) →
          ∑ x, g x * p x ≤ ∑ y, g y * q y := by
        intro g hg hg01
        let φ : (Fin n → ℕ) → ℝ := fun y ↦ g (fun j ↦ decide (1 ≤ y j))
        have hφ_mono : Monotone φ := by
          intro a b hab
          refine hg fun j ↦ ?_
          by_cases h1 : 1 ≤ a j
          · have h2 : 1 ≤ b j := le_trans h1 (hab j)
            simp [h1, h2]
          · simp [h1]
        have hφ_eq : ∀ x : Fin n → Bool, φ (natOfBoolVec x) = g x := by
          intro x
          unfold φ
          rw [decide_one_le_natOfBoolVec]
        have h_ineq := hc2 φ hφ_mono (fun y ↦ hg01 _)
        rw [(integrable_and_integral_nat_zero_one P hX_vec hX_all01 φ).2,
          (integrable_and_integral_nat_zero_one P' hX_cond_vec hX_cond_all01 φ).2] at h_ineq
        simpa [hφ_eq] using h_ineq
      have h_mono : ∀ g : (Fin n → Bool) → ℝ, Monotone g →
          ∑ x, g x * p x ≤ ∑ y, g y * q y := fun g hg ↦
        sum_mul_le_of_monotone_bool p q hp_sum hq_sum h_ind
          (Finset.univ.image g).card g hg le_rfl
      obtain ⟨w, hw0, hw1, hwx, hwy⟩ :=
        exists_monotone_weights_bool p q hp_nonneg hp_sum hq_nonneg hq_sum h_mono
      let R := BoolOrderPairs n
      let Pc : Measure R := ∑ r : R, ENNReal.ofReal (w r) • Measure.dirac r
      let Xc : R → Fin n → ℕ := fun r ↦ natOfBoolVec r.1.1
      let Xc_cond : R → Fin n → ℕ := fun r ↦ natOfBoolVec r.1.2
      have h_dirac_univ : ∀ r : R, (Measure.dirac r : Measure R) Set.univ = 1 :=
        fun r ↦ Measure.dirac_apply_of_mem (Set.mem_univ r)
      have h_dirac_apply : ∀ (r : R) (A : Set R),
          (Measure.dirac r : Measure R) A = A.indicator 1 r :=
        fun r _ ↦ Measure.dirac_apply' r trivial
      have hPc : IsProbabilityMeasure Pc := by
        constructor
        simp only [Pc, Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
          h_dirac_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ ↦ hw0 r), hw1, ENNReal.ofReal_one]
      have hXc_meas : Measurable Xc := fun _ _ ↦ trivial
      have hXc_cond_meas : Measurable Xc_cond := fun _ _ ↦ trivial
      refine ⟨R, inferInstance, Pc, hPc, Xc, Xc_cond, hXc_meas, hXc_cond_meas, ?_, ?_, ?_⟩
      · ext s hs
        rw [Measure.map_apply hXc_meas hs,
          measure_map_nat_zero_one_apply P hX_vec hX_all01 s]
        simp only [Pc, Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
          h_dirac_apply, Set.indicator_apply, Set.mem_preimage, Pi.one_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        have h_part : ∀ x : Fin n → Bool,
            (if natOfBoolVec x ∈ s then ENNReal.ofReal (p x) else 0) =
              ∑ r : R, if r.1.1 = x then
                (if natOfBoolVec r.1.1 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 := by
          intro x
          by_cases hmem : natOfBoolVec x ∈ s
          · simp only [hmem, ↓reduceIte, ← hwx x]
            rw [ENNReal.ofReal_sum_of_nonneg]
            · refine Finset.sum_congr rfl fun r _ ↦ ?_
              by_cases hrx : r.1.1 = x
              · simp [hrx, hmem]
              · simp [hrx]
            · intro r _; split_ifs <;> simp [hw0 r]
          · simp only [hmem, ↓reduceIte]
            symm
            refine Finset.sum_eq_zero fun r _ ↦ ?_
            by_cases hrx : r.1.1 = x
            · simp [hrx, hmem]
            · simp [hrx]
        have h_rhs : (∑ x : Fin n → Bool,
            if natOfBoolVec x ∈ s then
              ENNReal.ofReal (P.real {ω : Ω | (fun j ↦ X j ω) = natOfBoolVec x})
            else 0) =
            ∑ x : Fin n → Bool,
              ∑ r : R, if r.1.1 = x then
                (if natOfBoolVec r.1.1 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 :=
          Finset.sum_congr rfl fun x _ ↦ h_part x
        rw [h_rhs, Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [Finset.sum_ite_eq Finset.univ r.1.1]
        simp [Xc]
      · ext s hs
        rw [Measure.map_apply hXc_cond_meas hs,
          measure_map_nat_zero_one_apply P' hX_cond_vec hX_cond_all01 s]
        simp only [Pc, Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
          h_dirac_apply, Set.indicator_apply, Set.mem_preimage, Pi.one_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        have h_part : ∀ y : Fin n → Bool,
            (if natOfBoolVec y ∈ s then ENNReal.ofReal (q y) else 0) =
              ∑ r : R, if r.1.2 = y then
                (if natOfBoolVec r.1.2 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 := by
          intro y
          by_cases hmem : natOfBoolVec y ∈ s
          · simp only [hmem, ↓reduceIte, ← hwy y]
            rw [ENNReal.ofReal_sum_of_nonneg]
            · refine Finset.sum_congr rfl fun r _ ↦ ?_
              by_cases hry : r.1.2 = y
              · simp [hry, hmem]
              · simp [hry]
            · intro r _; split_ifs <;> simp [hw0 r]
          · simp only [hmem, ↓reduceIte]
            symm
            refine Finset.sum_eq_zero fun r _ ↦ ?_
            by_cases hry : r.1.2 = y
            · simp [hry, hmem]
            · simp [hry]
        have h_rhs : (∑ y : Fin n → Bool,
            if natOfBoolVec y ∈ s then
              ENNReal.ofReal (P'.real {ω' : Ω' | (fun j ↦ X_cond j ω') = natOfBoolVec y})
            else 0) =
            ∑ y : Fin n → Bool,
              ∑ r : R, if r.1.2 = y then
                (if natOfBoolVec r.1.2 ∈ s then ENNReal.ofReal (w r) else 0)
              else 0 :=
          Finset.sum_congr rfl fun y _ ↦ h_part y
        rw [h_rhs, Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        rw [Finset.sum_ite_eq Finset.univ r.1.2]
        simp [Xc_cond]
      · intro j
        exact Filter.Eventually.of_forall fun r ↦ monotone_natOfBoolVec r.2 j
  · -- `c2 ↔ c3`
    have h_cov_id : ∀ φ : (Fin n → ℕ) → ℝ,
        (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
        ProbabilityTheory.covariance
          (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X j ω)) P =
          P.real {ω | X i ω = 1} *
            (∫ ω', φ (fun j ↦ X_cond j ω') ∂P' - ∫ ω, φ (fun j ↦ X j ω) ∂P) := by
      intro φ hφ01
      have hXi_meas : Measurable (fun ω ↦ (X i ω : ℝ)) :=
        Measurable.of_discrete.comp (hX i)
      have hφ_meas : Measurable (fun ω ↦ φ (fun j ↦ X j ω)) :=
        Measurable.of_discrete.comp hX_vec
      have hXi_mem : MemLp (fun ω ↦ (X i ω : ℝ)) 2 P := by
        refine (memLp_top_of_bound hXi_meas.aestronglyMeasurable 1 ?_).mono_exponent le_top
        filter_upwards [hX01 i] with ω h01
        rcases h01 with h01 | h01
        · simp [h01]
        · simp [h01]
      have hφ_mem : MemLp (fun ω ↦ φ (fun j ↦ X j ω)) 2 P := by
        refine (memLp_top_of_bound hφ_meas.aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω ↦ ?_)).mono_exponent le_top
        rcases hφ01 (fun j ↦ X j ω) with h01 | h01
        · simp [h01]
        · simp [h01]
      rw [covariance_eq_sub hXi_mem hφ_mem]
      let A : Set Ω := {ω | X i ω = 1}
      have hA_meas : MeasurableSet A := hX i (measurableSet_singleton 1)
      have hXi_ind : (fun ω ↦ (X i ω : ℝ)) =ᵐ[P] A.indicator (1 : Ω → ℝ) := by
        filter_upwards [hX01 i] with ω h01
        rcases h01 with h01 | h01
        · simp [A, h01]
        · simp [A, h01]
      have hXi_mean : ∫ ω, (X i ω : ℝ) ∂P = P.real A := by
        rw [integral_congr_ae hXi_ind, integral_indicator_one hA_meas]
      have h_mul_ind : (fun ω ↦ (X i ω : ℝ) * φ (fun j ↦ X j ω)) =ᵐ[P]
          A.indicator (fun ω ↦ φ (fun j ↦ X j ω)) := by
        filter_upwards [hX01 i] with ω h01
        rcases h01 with h01 | h01
        · simp [A, h01]
        · simp [A, h01]
      have h_int_mul : ∫ ω, (X i ω : ℝ) * φ (fun j ↦ X j ω) ∂P =
          ∫ ω in A, φ (fun j ↦ X j ω) ∂P := by
        rw [integral_congr_ae h_mul_ind, integral_indicator hA_meas]
      have h_cond_int : ∫ ω', φ (fun j ↦ X_cond j ω') ∂P' =
          (P.real A)⁻¹ * ∫ ω in A, φ (fun j ↦ X j ω) ∂P := by
        rw [← integral_map hX_cond_vec.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
          h_law, integral_map hX_vec.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
          ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, ← Measure.real,
          smul_eq_mul]
      have hp_ne : P.real A ≠ 0 := ne_of_gt hp_pos
      have h_set_eq : ∫ ω in A, φ (fun j ↦ X j ω) ∂P =
          P.real A * ∫ ω', φ (fun j ↦ X_cond j ω') ∂P' := by
        rw [h_cond_int, ← mul_assoc, mul_inv_cancel₀ hp_ne, one_mul]
      change ∫ ω, (X i ω : ℝ) * φ (fun j ↦ X j ω) ∂P -
        (∫ ω, (X i ω : ℝ) ∂P) * (∫ ω, φ (fun j ↦ X j ω) ∂P) = _
      rw [h_int_mul, h_set_eq, hXi_mean]
      ring
    constructor
    · intro hc2 φ hφ_mono hφ01
      rw [h_cov_id φ hφ01]
      exact mul_nonneg (le_of_lt hp_pos) (sub_nonneg.mpr (hc2 φ hφ_mono hφ01))
    · intro hc3 φ hφ_mono hφ01
      have h := hc3 φ hφ_mono hφ01
      rw [h_cov_id φ hφ01] at h
      have h_sub :
          0 ≤ ∫ ω', φ (fun j ↦ X_cond j ω') ∂P' -
            ∫ ω, φ (fun j ↦ X j ω) ∂P := by
        nlinarith
      linarith

end SteinMethod
