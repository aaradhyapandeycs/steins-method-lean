/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.GeometricSums
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.Independence.Integration

/-!
# Auxiliary Coin & Geometric Lemmas for the Theorem 5.7 Counterexample
(`Formalization.Exponential.GeometricSumsCounterexampleAux`)

Provides the Rademacher coin space on `{0, ..., m - 1}`, fourth-moment lower bound
`36 < ∫ |Z_4001|`, exchangeability of coin coordinates on `{Z_4001 < 0}`, and the truncated
geometric distributions `ceMuL` (on `{1, ..., 4001}`) and `ceMuH` (on `{4002, ...}`) at
`(1 - p)^4001 = 1 / 2` used in `Formalization.Exponential.GeometricSumsCounterexample` to refute
the literal printed statement of Theorem 5.7 (`SteinIntro.tex:2915-2929`, `ISSUE-5.7`).
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod.Counterexample57

noncomputable def ceBern : Measure Bool :=
  (1 / 2 : ℝ≥0) • Measure.dirac true + (1 / 2 : ℝ≥0) • Measure.dirac false

lemma ceBern_singleton (b : Bool) : ceBern {b} = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [ceBern, Measure.coe_add, Pi.add_apply, Measure.coe_nnreal_smul_apply,
    Measure.coe_nnreal_smul_apply]
  cases b <;> simp

instance : IsProbabilityMeasure ceBern := by
  refine ⟨?_⟩
  have huniv : (univ : Set Bool) = {true} ∪ {false} := by ext b; cases b <;> simp
  rw [huniv, measure_union (by simp) (measurableSet_singleton false),
    ceBern_singleton true, ceBern_singleton false, ← ENNReal.coe_add]
  norm_num

def ceRad (b : Bool) : ℝ := if b then 1 else -1

lemma ce_abs_rad (b : Bool) : |ceRad b| = 1 := by cases b <;> norm_num [ceRad]

lemma ce_sq_rad (b : Bool) : ceRad b ^ 2 = 1 := by cases b <;> norm_num [ceRad]

lemma ce_cube_rad (b : Bool) : ceRad b ^ 3 = ceRad b := by cases b <;> norm_num [ceRad]

lemma ce_pow4_rad (b : Bool) : ceRad b ^ 4 = 1 := by cases b <;> norm_num [ceRad]

lemma ce_integral_rad : ∫ b, ceRad b ∂ceBern = 0 := by
  have ht : Integrable ceRad ((1 / 2 : ℝ≥0) • Measure.dirac true) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  have hf : Integrable ceRad ((1 / 2 : ℝ≥0) • Measure.dirac false) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  rw [ceBern, integral_add_measure ht hf, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_dirac, integral_dirac, NNReal.smul_def,
    NNReal.smul_def, smul_eq_mul, smul_eq_mul]
  norm_num [ceRad]

abbrev ceCoins (m : ℕ) : Type := Fin m → Bool

noncomputable def ceCoinMeas (m : ℕ) : Measure (ceCoins m) :=
  Measure.pi fun _ : Fin m ↦ ceBern

instance (m : ℕ) : IsProbabilityMeasure (ceCoinMeas m) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin m ↦ ceBern))

def ceR (m : ℕ) (r : Fin m) (b : ceCoins m) : ℝ := ceRad (b r)

lemma ce_iIndepFun_R (m : ℕ) : iIndepFun (ceR m) (ceCoinMeas m) :=
  iIndepFun_pi fun _ ↦ (Measurable.of_discrete : Measurable ceRad).aemeasurable

lemma ce_integral_R (m : ℕ) (r : Fin m) : ∫ b, ceR m r b ∂ceCoinMeas m = 0 := by
  have hmp := measurePreserving_eval (fun _ : Fin m ↦ ceBern) r
  have hm : AEStronglyMeasurable ceRad ((ceCoinMeas m).map (Function.eval r)) := by
    rw [ceCoinMeas, hmp.map_eq]
    exact Measurable.of_discrete.aestronglyMeasurable
  calc
    ∫ b, ceR m r b ∂ceCoinMeas m
        = ∫ x, ceRad x ∂(ceCoinMeas m).map (Function.eval r) :=
          (integral_map (measurable_pi_apply r).aemeasurable hm).symm
    _ = ∫ x, ceRad x ∂ceBern := by rw [ceCoinMeas, hmp.map_eq]
    _ = 0 := ce_integral_rad

lemma ce_map_invol {m : ℕ} {τ : ceCoins m → ceCoins m} (hτ : ∀ b, τ (τ b) = b) :
    (ceCoinMeas m).map τ = ceCoinMeas m := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  have hpre : τ ⁻¹' {b} = {τ b} := by
    ext b'
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h ↦ by rw [← h, hτ], fun h ↦ by rw [h, hτ]⟩
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton b), hpre,
    ceCoinMeas, Measure.pi_singleton, Measure.pi_singleton]
  refine Finset.prod_congr rfl fun r _ ↦ ?_
  rw [ceBern_singleton, ceBern_singleton]

def ceZ (m : ℕ) (b : ceCoins m) : ℝ := ∑ r : Fin m, ceR m r b

/-- Partial Rademacher sums have 2nd moment `k` and 4th moment `3 k^2 - 2 k`. -/
lemma ce_partial_moments {m : ℕ} :
    ∀ (k : ℕ) (hk : k ≤ m),
      (∫ b, (∑ r : Fin k, ceR m ⟨r.1, r.2.trans_le hk⟩ b) ^ 2 ∂ceCoinMeas m = (k : ℝ)) ∧
      (∫ b, (∑ r : Fin k, ceR m ⟨r.1, r.2.trans_le hk⟩ b) ^ 4 ∂ceCoinMeas m =
        3 * (k : ℝ) ^ 2 - 2 * (k : ℝ)) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    have hk_le : k ≤ m := Nat.le_of_succ_le hk
    obtain ⟨ih2, ih4⟩ := ih hk_le
    let A : ceCoins m → ℝ := fun b ↦ ∑ r : Fin k, ceR m ⟨r.1, r.2.trans_le hk_le⟩ b
    let rk : Fin m := ⟨k, hk⟩
    let E : ceCoins m → ℝ := ceR m rk
    have hsum_eq : ∀ b, (∑ r : Fin (k + 1), ceR m ⟨r.1, r.2.trans_le hk⟩ b) = A b + E b :=
      fun b ↦ by rw [Fin.sum_univ_castSucc]; rfl
    have hind_AE : IndepFun A E (ceCoinMeas m) := by
      let S : Finset (Fin m) := Finset.univ.filter (fun j : Fin m ↦ j.1 < k)
      let T : Finset (Fin m) := {rk}
      have hST : Disjoint S T := by
        refine Finset.disjoint_singleton_right.mpr ?_
        simp [S, rk]
      have hbase := iIndepFun.indepFun_finset S T hST (ce_iIndepFun_R m)
        (fun _ ↦ Measurable.of_discrete)
      let idx : Fin k → S := fun r ↦
        ⟨⟨r.1, r.2.trans_le hk_le⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.2⟩⟩
      let φ : (S → ℝ) → ℝ := fun u ↦ ∑ r : Fin k, u (idx r)
      let ψ : (T → ℝ) → ℝ := fun v ↦ v ⟨rk, Finset.mem_singleton_self rk⟩
      have hφ : Measurable φ := Finset.measurable_sum _ fun r _ ↦ measurable_pi_apply (idx r)
      have hψ : Measurable ψ := measurable_pi_apply _
      exact hbase.comp hφ hψ
    have hE_mean : ∫ b, E b ∂ceCoinMeas m = 0 := ce_integral_R m rk
    have hint_f : ∀ f : ceCoins m → ℝ, Integrable f (ceCoinMeas m) :=
      fun _ ↦ Integrable.of_finite
    have hmul_zero : ∀ {g : ℝ → ℝ}, Measurable g →
        ∫ b, g (A b) * E b ∂ceCoinMeas m = 0 := fun {g} hg ↦ by
      change ∫ b, (g ∘ A) b * (id ∘ E) b ∂ceCoinMeas m = 0
      rw [(hind_AE.comp hg measurable_id).integral_fun_mul_eq_mul_integral
        Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable]
      change (∫ b, g (A b) ∂ceCoinMeas m) * (∫ b, E b ∂ceCoinMeas m) = 0
      rw [hE_mean, mul_zero]
    constructor
    · have hpt2 : (fun b ↦ (∑ r : Fin (k + 1), ceR m ⟨r.1, r.2.trans_le hk⟩ b) ^ 2) =
          fun b ↦ (A b ^ 2 + 1) + (2 * A b) * E b := by
        ext b
        rw [hsum_eq b]
        have he2 : E b ^ 2 = 1 := ce_sq_rad (b rk)
        linear_combination he2
      rw [hpt2, integral_add (hint_f _) (hint_f _), integral_add (hint_f _) (hint_f _),
        ih2, integral_const, probReal_univ, one_smul,
        hmul_zero (g := fun x ↦ 2 * x) (measurable_const.mul measurable_id),
        add_zero, Nat.cast_add, Nat.cast_one]
    · have hpt4 : (fun b ↦ (∑ r : Fin (k + 1), ceR m ⟨r.1, r.2.trans_le hk⟩ b) ^ 4) =
          fun b ↦ ((A b ^ 4 + 6 * A b ^ 2) + 1) + (4 * A b ^ 3 + 4 * A b) * E b := by
        ext b
        rw [hsum_eq b]
        have he2 : E b ^ 2 = 1 := ce_sq_rad (b rk)
        have he3 : E b ^ 3 = E b := ce_cube_rad (b rk)
        have he4 : E b ^ 4 = 1 := ce_pow4_rad (b rk)
        linear_combination 6 * A b ^ 2 * he2 + 4 * A b * he3 + he4
      have hg_meas : Measurable (fun x : ℝ ↦ 4 * x ^ 3 + 4 * x) :=
        (measurable_const.mul ((continuous_pow 3).measurable)).add
          (measurable_const.mul measurable_id)
      rw [hpt4, integral_add (hint_f _) (hint_f _), integral_add (hint_f _) (hint_f _),
        integral_add (hint_f _) (hint_f _), integral_const_mul, ih4, ih2,
        integral_const, probReal_univ, one_smul, hmul_zero hg_meas, add_zero,
        Nat.cast_add, Nat.cast_one]
      ring

lemma ce_integrable {m : ℕ} (f : ceCoins m → ℝ) : Integrable f (ceCoinMeas m) :=
  Integrable.of_finite

/-- Lower bound `36 < 𝔼|Z_4001|` via the polynomial inequality `z^2 ≤ (220/3) z + z^4 / 36300`. -/
lemma ce_abs_Z_4001_gt : 36 < ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001 := by
  obtain ⟨hm2, hm4⟩ := ce_partial_moments (m := 4001) 4001 le_rfl
  have hZ_pt : ∀ b, (∑ r : Fin 4001, ceR 4001 ⟨r.1, r.2.trans_le le_rfl⟩ b) = ceZ 4001 b :=
    fun _ ↦ rfl
  simp_rw [hZ_pt] at hm2 hm4
  have hpoly : ∀ b : ceCoins 4001,
      ceZ 4001 b ^ 2 ≤ (220 / 3 : ℝ) * |ceZ 4001 b| + (1 / 36300 : ℝ) * ceZ 4001 b ^ 4 := by
    intro b
    set z : ℝ := |ceZ 4001 b|
    have hz_nn : 0 ≤ z := abs_nonneg _
    have hz2 : ceZ 4001 b ^ 2 = z ^ 2 := (sq_abs _).symm
    have hz4 : ceZ 4001 b ^ 4 = z ^ 4 := by
      calc
        ceZ 4001 b ^ 4 = (ceZ 4001 b ^ 2) ^ 2 := by ring
        _ = (z ^ 2) ^ 2 := by rw [hz2]
        _ = z ^ 4 := by ring
    rw [hz2, hz4]
    have hfac : 0 ≤ z * (z - 110) ^ 2 * (z + 220) / 36300 :=
      div_nonneg (mul_nonneg (mul_nonneg hz_nn (sq_nonneg _)) (by linarith)) (by norm_num)
    linarith [show (220 / 3 : ℝ) * z + (1 / 36300 : ℝ) * z ^ 4 - z ^ 2 =
      z * (z - 110) ^ 2 * (z + 220) / 36300 by ring]
  have hint := integral_mono (ce_integrable (fun b ↦ ceZ 4001 b ^ 2))
    (ce_integrable (fun b ↦
      (220 / 3 : ℝ) * |ceZ 4001 b| + (1 / 36300 : ℝ) * ceZ 4001 b ^ 4)) hpoly
  rw [integral_add (ce_integrable _) (ce_integrable _), integral_const_mul,
    integral_const_mul, hm2, hm4] at hint
  generalize ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001 = M at hint ⊢
  norm_num at hint
  linarith

/-- Since `4001` is odd, `ceZ 4001 b ≠ 0` for every coin configuration `b`. -/
lemma ceZ_4001_ne_zero (b : ceCoins 4001) : ceZ 4001 b ≠ 0 := by
  have hcast : ceZ 4001 b =
      ((2 * (∑ r : Fin 4001, if b r then (1 : ℤ) else 0) - 4001 : ℤ) : ℝ) := by
    dsimp only [ceZ, ceR, ceRad]
    have hterm : ∀ r : Fin 4001,
        (if b r then (1 : ℝ) else -1) = (2 * (if b r then (1 : ℝ) else 0) - 1) := fun r ↦ by
      cases b r <;> norm_num
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hcast]
  intro h0
  have hz : (2 : ℤ) * (∑ r : Fin 4001, if b r then (1 : ℤ) else 0) - 4001 = 0 :=
    Int.cast_eq_zero.mp h0
  omega

def ceFlip (b : ceCoins 4001) : ceCoins 4001 := fun r ↦ !b r

lemma ceFlip_invol (b : ceCoins 4001) : ceFlip (ceFlip b) = b := by
  ext r; simp [ceFlip]

lemma ceRad_not (x : Bool) : ceRad (!x) = - ceRad x := by
  cases x <;> norm_num [ceRad]

lemma ceZ_flip (b : ceCoins 4001) : ceZ 4001 (ceFlip b) = - ceZ 4001 b := by
  dsimp only [ceZ, ceR, ceFlip]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ ceRad_not (b r)

lemma ceCoinMeas_neg_eq_half :
    (ceCoinMeas 4001) {b | ceZ 4001 b < 0} = (1 / 2 : ℝ≥0∞) ∧
    (ceCoinMeas 4001) {b | ¬ ceZ 4001 b < 0} = (1 / 2 : ℝ≥0∞) := by
  have hmap := ce_map_invol ceFlip_invol
  have hpre : ceFlip ⁻¹' {b | ceZ 4001 b < 0} = {b | ¬ ceZ 4001 b < 0} := by
    ext b
    simp only [mem_preimage, mem_ofPred_eq, ceZ_flip]
    have hne := ceZ_4001_ne_zero b
    exact ⟨fun h hlt ↦ by linarith, fun h ↦ by
      rcases lt_trichotomy (ceZ 4001 b) 0 with hlt | h0 | hgt
      · exact (h hlt).elim
      · exact (hne h0).elim
      · linarith⟩
  have heq : (ceCoinMeas 4001) {b | ceZ 4001 b < 0} =
      (ceCoinMeas 4001) {b | ¬ ceZ 4001 b < 0} := by
    calc
      (ceCoinMeas 4001) {b | ceZ 4001 b < 0}
          = ((ceCoinMeas 4001).map ceFlip) {b | ceZ 4001 b < 0} := by rw [hmap]
      _ = (ceCoinMeas 4001) (ceFlip ⁻¹' {b | ceZ 4001 b < 0}) :=
            Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete
      _ = (ceCoinMeas 4001) {b | ¬ ceZ 4001 b < 0} := by rw [hpre]
  have hsum : (ceCoinMeas 4001) {b | ceZ 4001 b < 0} +
      (ceCoinMeas 4001) {b | ¬ ceZ 4001 b < 0} = 1 := by
    have h := measure_add_measure_compl
      (μ := ceCoinMeas 4001) (s := {b | ceZ 4001 b < 0}) MeasurableSet.of_discrete
    rwa [measure_univ] at h
  rw [← heq, ← two_mul] at hsum
  have h2 : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
    rw [one_div]; exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hval : (ceCoinMeas 4001) {b | ceZ 4001 b < 0} = 1 / 2 :=
    (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp (hsum.trans h2.symm)
  exact ⟨hval, heq.symm.trans hval⟩

lemma ce_integral_Z_indicators :
    (∫ b, {b' | ¬ ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂ceCoinMeas 4001 =
      (1 / 2 : ℝ) * ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001) ∧
    (∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂ceCoinMeas 4001 =
      - (1 / 2 : ℝ) * ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001) := by
  let Ipos := ∫ b, {b' | ¬ ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂ceCoinMeas 4001
  let Ineg := ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂ceCoinMeas 4001
  have hdiff : Ipos - Ineg = ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001 := by
    dsimp only [Ipos, Ineg]
    rw [ ← integral_sub (ce_integrable _) (ce_integrable _)]
    refine integral_congr_ae (Eventually.of_forall fun b ↦ ?_)
    dsimp only
    by_cases hb : ceZ 4001 b < 0
    · have hmem : b ∈ {b' | ceZ 4001 b' < 0} := hb
      have hnot : b ∉ {b' | ¬ ceZ 4001 b' < 0} := not_not.mpr hb
      rw [indicator_of_notMem hnot, indicator_of_mem hmem, zero_sub, abs_of_neg hb]
    · have hmem : b ∈ {b' | ¬ ceZ 4001 b' < 0} := hb
      have hnot : b ∉ {b' | ceZ 4001 b' < 0} := hb
      rw [indicator_of_mem hmem, indicator_of_notMem hnot, sub_zero, abs_of_nonneg (not_lt.mp hb)]
  have hanti : Ineg = - Ipos := by
    have hmap := ce_map_invol ceFlip_invol
    have hcomp : ({b' | ceZ 4001 b' < 0}.indicator (ceZ 4001)) ∘ ceFlip =
        fun b ↦ - ({b' | ¬ ceZ 4001 b' < 0}.indicator (ceZ 4001) b) := by
      ext b
      simp only [Function.comp_apply]
      have hne := ceZ_4001_ne_zero b
      by_cases hb : ceZ 4001 b < 0
      · have hnot1 : ceFlip b ∉ {b' | ceZ 4001 b' < 0} := by
          simp only [mem_ofPred_eq, ceZ_flip]; linarith
        have hnot2 : b ∉ {b' | ¬ ceZ 4001 b' < 0} := not_not.mpr hb
        rw [indicator_of_notMem hnot1, indicator_of_notMem hnot2, neg_zero]
      · have hpos : 0 < ceZ 4001 b := lt_of_le_of_ne (not_lt.mp hb) hne.symm
        have hmem1 : ceFlip b ∈ {b' | ceZ 4001 b' < 0} := by
          simp only [mem_ofPred_eq, ceZ_flip]; linarith
        have hmem2 : b ∈ {b' | ¬ ceZ 4001 b' < 0} := hb
        rw [indicator_of_mem hmem1, indicator_of_mem hmem2, ceZ_flip]
    dsimp only [Ineg, Ipos]
    calc
      ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂ceCoinMeas 4001
          = ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂(ceCoinMeas 4001).map ceFlip := by
            rw [hmap]
      _ = ∫ b, ({b' | ceZ 4001 b' < 0}.indicator (ceZ 4001) ∘ ceFlip) b ∂ceCoinMeas 4001 :=
            integral_map Measurable.of_discrete.aemeasurable
              Measurable.of_discrete.aestronglyMeasurable
      _ = - ∫ b, {b' | ¬ ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂ceCoinMeas 4001 := by
            rw [hcomp, integral_neg]
  exact ⟨by linarith, by linarith⟩

/-- Exchangeability on `{ceZ 4001 < 0}`: each coordinate has expectation
`- (1 / (2 * 4001)) * 𝔼|ceZ 4001|` on `{ceZ 4001 < 0}`. -/
lemma ce_integral_R_on_neg (r₀ : Fin 4001) :
    ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r₀) b ∂ceCoinMeas 4001 =
      - (1 / (2 * (4001 : ℝ))) * ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001 := by
  have hexch : ∀ r : Fin 4001,
      ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r) b ∂ceCoinMeas 4001 =
        ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r₀) b ∂ceCoinMeas 4001 := fun r ↦ by
    let τ : ceCoins 4001 → ceCoins 4001 := fun b j ↦ b (Equiv.swap r r₀ j)
    have hτ : ∀ b, τ (τ b) = b := fun b ↦ by ext j; simp [τ]
    have hmap := ce_map_invol hτ
    have hZ_τ : ∀ b, ceZ 4001 (τ b) = ceZ 4001 b := fun b ↦
      Equiv.sum_comp (Equiv.swap r r₀) (fun j ↦ ceR 4001 j b)
    have hcomp : ({b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r)) ∘ τ =
        {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r₀) := by
      ext b
      simp only [Function.comp_apply]
      by_cases hb : ceZ 4001 b < 0
      · have hmem1 : τ b ∈ {b' | ceZ 4001 b' < 0} := by
          simp only [mem_ofPred_eq, hZ_τ]; exact hb
        have hmem2 : b ∈ {b' | ceZ 4001 b' < 0} := hb
        rw [indicator_of_mem hmem1, indicator_of_mem hmem2]
        simp [ceR, τ]
      · have hnot1 : τ b ∉ {b' | ceZ 4001 b' < 0} := by
          simp only [mem_ofPred_eq, hZ_τ]; exact hb
        have hnot2 : b ∉ {b' | ceZ 4001 b' < 0} := hb
        rw [indicator_of_notMem hnot1, indicator_of_notMem hnot2]
    calc
      ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r) b ∂ceCoinMeas 4001
          = ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r) b ∂(ceCoinMeas 4001).map τ := by
            rw [hmap]
      _ = ∫ b, ({b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r) ∘ τ) b ∂ceCoinMeas 4001 :=
            integral_map Measurable.of_discrete.aemeasurable
              Measurable.of_discrete.aestronglyMeasurable
      _ = ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r₀) b ∂ceCoinMeas 4001 := by rw [hcomp]
  have hsum : (4001 : ℝ) *
      ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r₀) b ∂ceCoinMeas 4001 =
        ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceZ 4001) b ∂ceCoinMeas 4001 := by
    have hpt : (fun b ↦ {b' | ceZ 4001 b' < 0}.indicator (ceZ 4001) b) =
        fun b ↦ ∑ r : Fin 4001, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r) b := by
      ext b
      by_cases hb : b ∈ {b' | ceZ 4001 b' < 0}
      · rw [indicator_of_mem hb]
        simp_rw [indicator_of_mem hb]
        rfl
      · rw [indicator_of_notMem hb]
        simp_rw [indicator_of_notMem hb]
        simp
    rw [hpt, integral_finsetSum Finset.univ fun _ _ ↦ ce_integrable _]
    simp_rw [hexch, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat]
  rw [ce_integral_Z_indicators.2] at hsum
  generalize ∫ b, {b' | ceZ 4001 b' < 0}.indicator (ceR 4001 r₀) b ∂ceCoinMeas 4001 = A at hsum ⊢
  generalize ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001 = B at hsum ⊢
  linarith

/-! ### Conditional Geometric Laws at `(1 - ceP)^4001 = 1 / 2` -/

noncomputable def ceP : ℝ := 1 - (1 / 2 : ℝ) ^ (1 / (4001 : ℝ))

lemma ceP_props :
    0 < ceP ∧ ceP < 1 ∧ (1 - ceP) ^ 4001 = (1 / 2 : ℝ) := by
  have hpow_pos : 0 < (1 / 2 : ℝ) ^ (1 / (4001 : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpow_lt : (1 / 2 : ℝ) ^ (1 / (4001 : ℝ)) < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by dsimp only [ceP]; linarith, by dsimp only [ceP]; linarith, ?_⟩
  have h1m : 1 - ceP = (1 / 2 : ℝ) ^ (1 / (4001 : ℝ)) := by dsimp only [ceP]; ring
  rw [h1m, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

lemma shiftedGeomLaw_ceP_halves :
    (shiftedGeomLaw ceP) (Iic 4001) = (1 / 2 : ℝ≥0∞) ∧
    (shiftedGeomLaw ceP) (Ioi 4001) = (1 / 2 : ℝ≥0∞) := by
  obtain ⟨hp0, hp1, hpow⟩ := ceP_props
  have hIoi_eq : (Ioi 4001 : Set ℕ) = Ici 4002 := by ext k; simp; omega
  have hreal_Ici := shiftedGeomLaw_real_Ici hp0 hp1.le (by norm_num : 1 ≤ 4002)
  have hsub : 4002 - 1 = 4001 := rfl
  rw [hsub, hpow] at hreal_Ici
  have hIoi : (shiftedGeomLaw ceP) (Ioi 4001) = (1 / 2 : ℝ≥0∞) := by
    rw [hIoi_eq, ← ofReal_measureReal (measure_ne_top _ _), hreal_Ici, one_div,
      ENNReal.ofReal_inv_of_pos zero_lt_two, ENNReal.ofReal_ofNat, one_div]
  have hcompl : (Iic 4001 : Set ℕ)ᶜ = Ioi 4001 := compl_Iic
  have hsum := measure_add_measure_compl (μ := shiftedGeomLaw ceP)
    (s := Iic 4001) measurableSet_Iic
  rw [hcompl, hIoi, measure_univ] at hsum
  have hIic : (shiftedGeomLaw ceP) (Iic 4001) = (1 / 2 : ℝ≥0∞) := by
    have h1 : (1 : ℝ≥0∞) = 1 / 2 + 1 / 2 := by
      rw [← two_mul, one_div]
      exact (ENNReal.mul_inv_cancel (by norm_num) (by norm_num)).symm
    exact (ENNReal.add_left_inj (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤)).mp (hsum.trans h1)
  exact ⟨hIic, hIoi⟩

noncomputable def ceMuL : Measure ℕ :=
  (2 : ℝ≥0∞) • (shiftedGeomLaw ceP).restrict (Iic 4001)

noncomputable def ceMuH : Measure ℕ :=
  (2 : ℝ≥0∞) • (shiftedGeomLaw ceP).restrict (Ioi 4001)

instance : IsProbabilityMeasure ceMuL := by
  refine ⟨?_⟩
  rw [ceMuL, Measure.smul_apply, Measure.restrict_apply_univ, shiftedGeomLaw_ceP_halves.1,
    smul_eq_mul, one_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure ceMuH := by
  refine ⟨?_⟩
  rw [ceMuH, Measure.smul_apply, Measure.restrict_apply_univ, shiftedGeomLaw_ceP_halves.2,
    smul_eq_mul, one_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

lemma ceMuL_add_ceMuH (s : Set ℕ) :
    (1 / 2 : ℝ≥0∞) * ceMuL s + (1 / 2 : ℝ≥0∞) * ceMuH s = (shiftedGeomLaw ceP) s := by
  have hhalf : (1 / 2 : ℝ≥0∞) * 2 = 1 := by
    rw [one_div]; exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  rw [ceMuL, ceMuH, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.of_discrete,
    Measure.restrict_apply MeasurableSet.of_discrete,
    ← mul_assoc, ← mul_assoc, hhalf, one_mul, one_mul,
    ← measure_union
      (Set.disjoint_left.mpr fun k h1 h2 ↦ not_lt_of_ge (mem_Iic.mp h1.2) (mem_Ioi.mp h2.2))
      MeasurableSet.of_discrete]
  congr 1
  ext k; simp only [mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
  exact ⟨fun h ↦ h.elim And.left And.left,
    fun hk ↦ (le_or_gt k 4001).imp (fun h ↦ ⟨hk, h⟩) (fun h ↦ ⟨hk, h⟩)⟩

lemma ceMuL_support : ∀ᵐ l ∂ceMuL, 1 ≤ l ∧ l ≤ 4001 := by
  rw [ae_iff]
  have hsub : {l : ℕ | ¬ (1 ≤ l ∧ l ≤ 4001)} ⊆ {0} ∪ Ioi 4001 := by
    intro l hl
    simp only [mem_ofPred_eq, not_and_or, not_le] at hl
    simp only [mem_union, mem_singleton_iff, mem_Ioi]
    rcases hl with h0 | hgt
    · exact Or.inl (by omega)
    · exact Or.inr hgt
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [ceMuL, Measure.smul_apply, Measure.restrict_apply MeasurableSet.of_discrete,
      smul_eq_mul]
    have h0 : (shiftedGeomLaw ceP) ({0} ∩ Iic 4001) = 0 :=
      measure_mono_null inter_subset_left (shiftedGeomLaw_zero ceP)
    rw [h0, mul_zero]
  · rw [ceMuL, Measure.smul_apply, Measure.restrict_apply MeasurableSet.of_discrete,
      smul_eq_mul]
    have hemp : Ioi 4001 ∩ Iic 4001 = (∅ : Set ℕ) :=
      Set.eq_empty_iff_forall_notMem.mpr fun k ⟨(h1 : 4001 < k), (h2 : k ≤ 4001)⟩ ↦
        not_lt_of_ge h2 h1
    rw [hemp, measure_empty, mul_zero]

lemma ceMuH_support : ∀ᵐ h ∂ceMuH, 4001 < h := by
  rw [ae_iff]
  have heq : {h : ℕ | ¬ 4001 < h} = Iic 4001 := by ext h; simp
  rw [heq, ceMuH, Measure.smul_apply, Measure.restrict_apply MeasurableSet.of_discrete,
    smul_eq_mul]
  have hemp : Iic 4001 ∩ Ioi 4001 = (∅ : Set ℕ) :=
    Set.eq_empty_iff_forall_notMem.mpr fun k ⟨(h1 : k ≤ 4001), (h2 : 4001 < k)⟩ ↦
      not_lt_of_ge h1 h2
  rw [hemp, measure_empty, mul_zero]

/-- Since `ceMuL.real {k} = 2 * ceP * (1 - ceP)^(k - 1)` is antitone on `{1, ..., 4001}`,
pairing `k` with `4002 - k` gives `∫ l, (l : ℝ) ∂ceMuL ≤ 2001`. -/
lemma ceMuL_mean_le : ∫ l, (l : ℝ) ∂ceMuL ≤ 2001 := by
  obtain ⟨hp0, hp1, _⟩ := ceP_props
  have hsingle : ∀ k ∈ Finset.Icc 1 4001,
      ceMuL.real {k} = 2 * (ceP * (1 - ceP) ^ (k - 1)) := fun k hk ↦ by
    have hk_lu := Finset.mem_Icc.mp hk
    have h1 : ceMuL {k} = 2 * (shiftedGeomLaw ceP) {k} := by
      rw [ceMuL, Measure.smul_apply, Measure.restrict_apply MeasurableSet.of_discrete,
        smul_eq_mul]
      have hinter : ({k} : Set ℕ) ∩ Iic 4001 = {k} :=
        inter_eq_left.mpr fun x hx ↦ (mem_singleton_iff.mp hx) ▸ hk_lu.2
      rw [hinter]
    rw [measureReal_def, h1, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← measureReal_def,
      shiftedGeomLaw_real_singleton_of_pos hp0 hp1.le hk_lu.1]
    ring
  have hsum_prob : ∑ k ∈ Finset.Icc 1 4001, ceMuL.real {k} = 1 := by
    have hdisj : Set.PairwiseDisjoint (Finset.Icc 1 4001 : Set ℕ) (fun k : ℕ ↦ ({k} : Set ℕ)) :=
      fun i _ j _ hij ↦ Set.disjoint_singleton.mpr hij
    have hunion : (⋃ k ∈ Finset.Icc 1 4001, ({k} : Set ℕ)) = Icc 1 4001 := by
      ext x; simp [Finset.mem_Icc]
    have hm := measureReal_biUnion_finset hdisj (fun _ _ ↦ MeasurableSet.of_discrete) (μ := ceMuL)
    rw [hunion] at hm
    have hfull : ceMuL.real (Icc 1 4001) = 1 := by
      have hae : ∀ᵐ l ∂ceMuL, l ∈ Icc 1 4001 := ceMuL_support
      have h0 : ceMuL (Icc 1 4001)ᶜ = 0 := ae_iff.mp hae
      have h1 := measure_add_measure_compl (μ := ceMuL) (s := Icc 1 4001) MeasurableSet.of_discrete
      rw [h0, add_zero, measure_univ] at h1
      rw [measureReal_def, h1, ENNReal.toReal_one]
    exact hm.symm.trans hfull
  have hint_eq : ∫ l, (l : ℝ) ∂ceMuL =
      ∑ k ∈ Finset.Icc (1 : ℕ) 4001, (k : ℝ) * ceMuL.real {k} := by
    have hae_eq : (fun l : ℕ ↦ (l : ℝ)) =ᵐ[ceMuL]
        fun l ↦ ∑ k ∈ Finset.Icc (1 : ℕ) 4001, ({k} : Set ℕ).indicator (fun _ ↦ (k : ℝ)) l := by
      filter_upwards [ceMuL_support] with l hl
      rw [Finset.sum_eq_single l]
      · simp
      · intro k _ hkl; simp [hkl.symm]
      · intro hl_not
        exact (hl_not (Finset.mem_Icc.mpr hl)).elim
    rw [integral_congr_ae hae_eq,
      integral_finsetSum (Finset.Icc (1 : ℕ) 4001)
        (f := fun (k : ℕ) (l : ℕ) ↦ ({k} : Set ℕ).indicator (fun _ ↦ (k : ℝ)) l)
        fun k _ ↦ (integrable_const (k : ℝ)).indicator MeasurableSet.of_discrete]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [integral_indicator_const (k : ℝ) MeasurableSet.of_discrete, smul_eq_mul, mul_comm]
  rw [hint_eq]
  let S := Finset.Icc (1 : ℕ) 4001
  let d : ℕ → ℝ := fun k ↦ ((k : ℝ) - 2001) * ceMuL.real {k}
  have hrefl : ∑ k ∈ S, d k = ∑ k ∈ S, d (4002 - k) := by
    refine Finset.sum_bij (fun k _ ↦ 4002 - k)
      (fun k hk ↦ by simp only [S, Finset.mem_Icc] at hk ⊢; omega)
      (fun k₁ hk₁ k₂ hk₂ h ↦ by simp only [S, Finset.mem_Icc] at hk₁ hk₂; omega)
      (fun k hk ↦ ⟨4002 - k, by simp only [S, Finset.mem_Icc] at hk ⊢; omega,
        by simp only [S, Finset.mem_Icc] at hk; omega⟩)
      (fun k hk ↦ by simp only [S, Finset.mem_Icc] at hk; congr 1; omega)
  have hpair_nonpos : ∀ k ∈ S, d k + d (4002 - k) ≤ 0 := fun k hk ↦ by
    have hk_lu := Finset.mem_Icc.mp hk
    have hk'_mem : 4002 - k ∈ S := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hcast_sub : ((4002 - k : ℕ) : ℝ) - 2001 = - ((k : ℝ) - 2001) := by
      rw [Nat.cast_sub (by omega : k ≤ 4002)]; push_cast; ring
    have hsum_d : d k + d (4002 - k) =
        ((k : ℝ) - 2001) * (ceMuL.real {k} - ceMuL.real {4002 - k}) := by
      dsimp only [d]; rw [hcast_sub]; ring
    rw [hsum_d, hsingle k hk, hsingle (4002 - k) hk'_mem]
    have h1mp_nn : 0 ≤ 1 - ceP := sub_nonneg.mpr hp1.le
    have h1mp_le : 1 - ceP ≤ 1 := sub_le_self 1 hp0.le
    rcases le_or_gt k 2001 with hle | hgt
    · have hexp_le : k - 1 ≤ 4002 - k - 1 := by omega
      have hpow_ge : (1 - ceP) ^ (4002 - k - 1) ≤ (1 - ceP) ^ (k - 1) :=
        pow_le_pow_of_le_one h1mp_nn h1mp_le hexp_le
      have h1 : (k : ℝ) - 2001 ≤ 0 := by exact_mod_cast (by omega : (k : ℤ) - 2001 ≤ 0)
      have h2 : 0 ≤ 2 * (ceP * (1 - ceP) ^ (k - 1)) -
          2 * (ceP * (1 - ceP) ^ (4002 - k - 1)) := by
        rw [show 2 * (ceP * (1 - ceP) ^ (k - 1)) - 2 * (ceP * (1 - ceP) ^ (4002 - k - 1)) =
          (2 * ceP) * ((1 - ceP) ^ (k - 1) - (1 - ceP) ^ (4002 - k - 1)) by ring]
        exact mul_nonneg (mul_nonneg zero_le_two hp0.le) (sub_nonneg.mpr hpow_ge)
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
    · have hexp_ge : 4002 - k - 1 ≤ k - 1 := by omega
      have hpow_le : (1 - ceP) ^ (k - 1) ≤ (1 - ceP) ^ (4002 - k - 1) :=
        pow_le_pow_of_le_one h1mp_nn h1mp_le hexp_ge
      have h1 : 0 ≤ (k : ℝ) - 2001 := by exact_mod_cast (by omega : (0 : ℤ) ≤ (k : ℤ) - 2001)
      have h2 : 2 * (ceP * (1 - ceP) ^ (k - 1)) -
          2 * (ceP * (1 - ceP) ^ (4002 - k - 1)) ≤ 0 := by
        rw [show 2 * (ceP * (1 - ceP) ^ (k - 1)) - 2 * (ceP * (1 - ceP) ^ (4002 - k - 1)) =
          (2 * ceP) * ((1 - ceP) ^ (k - 1) - (1 - ceP) ^ (4002 - k - 1)) by ring]
        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg zero_le_two hp0.le)
          (sub_nonpos.mpr hpow_le)
      exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  have h2sum : 2 * ∑ k ∈ S, d k ≤ 0 := by
    calc
      2 * ∑ k ∈ S, d k = (∑ k ∈ S, d k) + ∑ k ∈ S, d (4002 - k) := by rw [← hrefl]; ring
      _ = ∑ k ∈ S, (d k + d (4002 - k)) := (Finset.sum_add_distrib).symm
      _ ≤ 0 := Finset.sum_nonpos hpair_nonpos
  have hexpand : ∑ k ∈ S, d k =
      (∑ k ∈ S, (k : ℝ) * ceMuL.real {k}) - 2001 * ∑ k ∈ S, ceMuL.real {k} := by
    dsimp only [d]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand, hsum_prob, mul_one] at h2sum
  generalize ∑ k ∈ S, (k : ℝ) * ceMuL.real {k} = M at h2sum ⊢
  linarith only [h2sum]

end SteinMethod.Counterexample57
