/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Monotone.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Ring

/-!
# Finite Boolean Hypercube Monotone Coupling (`Formalization.PoissonSizeBias.Monotone.BoolCoupling`)

Establishes coordinatewise threshold lifting `liftFromBool` and finite-hypercube Strassen / Farkas
monotone coupling weights (`exists_monotone_weights_bool`) used to prove Lemma 4.18
(`SteinIntro.tex:2404-2423`).
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-! ### Part 3: Lemma 4.18 (`\label{lem121}`, `SteinIntro.tex:2404-2423`) -/

instance instDecidableLeFinBool (n : ℕ) :
    DecidableRel (· ≤ · : (Fin n → Bool) → (Fin n → Bool) → Prop) :=
  fun _ _ ↦ Fintype.decidableForallFintype

abbrev BoolOrderPairs (n : ℕ) : Type :=
  {p : (Fin n → Bool) × (Fin n → Bool) // p.1 ≤ p.2}

instance instMeasurableSpaceBoolOrderPairs (n : ℕ) :
    MeasurableSpace (BoolOrderPairs n) := ⊤

noncomputable def ofBoolVec {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ :=
  fun i ↦ if x i then 1 else 0

private noncomputable def stepInd (b : Bool) (t : ℝ) : ℝ :=
  if b then (Set.Ici (1 : ℝ)).indicator (fun _ ↦ 1) t
  else (Set.Iio (1 : ℝ)).indicator (fun _ ↦ 1) t

private lemma measurable_stepInd (b : Bool) : Measurable (stepInd b) := by
  cases b
  · exact measurable_const.indicator measurableSet_Iio
  · exact measurable_const.indicator measurableSet_Ici

/-- Lift `g : (Fin n → Bool) → ℝ` on the Boolean hypercube to `(Fin n → ℝ) → ℝ`
via componentwise thresholding at `1`. -/
noncomputable def liftFromBool {n : ℕ} (g : (Fin n → Bool) → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ x : Fin n → Bool, g x * ∏ i : Fin n, stepInd (x i) (z i)

theorem measurable_liftFromBool {n : ℕ} (g : (Fin n → Bool) → ℝ) :
    Measurable (liftFromBool g) := by
  unfold liftFromBool
  refine Finset.measurable_sum Finset.univ fun x _ ↦ Measurable.const_mul ?_ (g x)
  exact Finset.measurable_prod Finset.univ fun i _ ↦
    (measurable_stepInd (x i)).comp (measurable_pi_apply i)

private lemma prod_stepInd_eq_ite {n : ℕ} (x : Fin n → Bool) (z : Fin n → ℝ) :
    (∏ i : Fin n, stepInd (x i) (z i)) =
      if x = (fun i ↦ decide (1 ≤ z i)) then 1 else 0 := by
  by_cases hx : x = (fun i ↦ decide (1 ≤ z i))
  · subst hx
    simp only [↓reduceIte]
    refine Finset.prod_eq_one fun i _ ↦ ?_
    unfold stepInd
    by_cases hle : 1 ≤ z i
    · simp [hle]
    · have hlt : z i < 1 := not_le.mp hle
      simp [hle, hlt]
  · simp only [hx, ↓reduceIte]
    have hex : ∃ i : Fin n, x i ≠ decide (1 ≤ z i) := by
      by_contra h_all
      push Not at h_all
      exact hx (funext h_all)
    rcases hex with ⟨i₀, hi₀⟩
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    unfold stepInd
    by_cases hle : 1 ≤ z i₀
    · have hxf : x i₀ = false := by
        cases h : x i₀
        · rfl
        · exfalso; apply hi₀; simp [h, hle]
      have hnot : z i₀ ∉ Set.Iio (1 : ℝ) := not_lt_of_ge hle
      simp only [hxf, Bool.false_eq_true, ↓reduceIte, Set.indicator_of_notMem hnot]
    · have hxt : x i₀ = true := by
        cases h : x i₀
        · exfalso; apply hi₀; simp [h, hle]
        · rfl
      have hnot : z i₀ ∉ Set.Ici (1 : ℝ) := hle
      simp only [hxt, ↓reduceIte, Set.indicator_of_notMem hnot]

theorem liftFromBool_eq {n : ℕ} (g : (Fin n → Bool) → ℝ) (z : Fin n → ℝ) :
    liftFromBool g z = g (fun i ↦ decide (1 ≤ z i)) := by
  unfold liftFromBool
  simp_rw [prod_stepInd_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem isIncreasing_liftFromBool {n : ℕ} {g : (Fin n → Bool) → ℝ} (hg : Monotone g) :
    IsIncreasing (liftFromBool g) := by
  intro z₁ z₂ hz
  rw [liftFromBool_eq, liftFromBool_eq]
  refine hg fun i ↦ ?_
  by_cases h1 : 1 ≤ z₁ i
  · have h2 : 1 ≤ z₂ i := le_trans h1 (hz i)
    simp [h1, h2]
  · simp [h1]

theorem isDecreasing_liftFromBool {n : ℕ} {g : (Fin n → Bool) → ℝ} (hg : Antitone g) :
    IsDecreasing (liftFromBool g) := by
  intro z₁ z₂ hz
  rw [liftFromBool_eq, liftFromBool_eq]
  refine hg fun i ↦ ?_
  by_cases h1 : 1 ≤ z₁ i
  · have h2 : 1 ≤ z₂ i := le_trans h1 (hz i)
    simp [h1, h2]
  · simp [h1]

private lemma decide_one_le_ofBoolVec {n : ℕ} (x : Fin n → Bool) :
    (fun i ↦ decide (1 ≤ ofBoolVec x i)) = x := by
  funext i
  unfold ofBoolVec
  cases x i <;> simp

private lemma ofBoolVec_injective {n : ℕ} : Function.Injective (@ofBoolVec n) := by
  intro x y hxy
  have h := congr_arg (fun z : Fin n → ℝ ↦ (fun i ↦ decide (1 ≤ z i))) hxy
  rwa [decide_one_le_ofBoolVec, decide_one_le_ofBoolVec] at h

private lemma eq_ofBoolVec_decide {n : ℕ} {z : Fin n → ℝ}
    (hz : ∀ i : Fin n, z i = 0 ∨ z i = 1) :
    z = ofBoolVec (fun i ↦ decide (1 ≤ z i)) := by
  funext i
  unfold ofBoolVec
  rcases hz i with h0 | h1
  · simp [h0]
  · simp [h1]

private lemma prod_stepInd_eq_indicator_of_zero_one {n : ℕ} {Ω : Type*}
    (V : Fin n → Ω → ℝ) (hV01 : ∀ (i : Fin n) (ω : Ω), V i ω = 0 ∨ V i ω = 1)
    (x : Fin n → Bool) (ω : Ω) :
    (∏ i : Fin n, stepInd (x i) (V i ω)) =
      {ω' : Ω | (fun i ↦ V i ω') = ofBoolVec x}.indicator (fun _ ↦ (1 : ℝ)) ω := by
  rw [prod_stepInd_eq_ite]
  by_cases hx : x = (fun i ↦ decide (1 ≤ V i ω))
  · have hmem : ω ∈ {ω' : Ω | (fun i ↦ V i ω') = ofBoolVec x} := by
      simp only [Set.mem_ofPred_eq, hx]
      exact eq_ofBoolVec_decide (fun i ↦ hV01 i ω)
    rw [Set.indicator_of_mem hmem]
    simp [hx]
  · have hnot : ω ∉ {ω' : Ω | (fun i ↦ V i ω') = ofBoolVec x} := by
      intro hmem
      apply hx
      have h_eq : (fun i ↦ V i ω) = ofBoolVec x := hmem
      have h_dec := congr_arg (fun z : Fin n → ℝ ↦ (fun i ↦ decide (1 ≤ z i))) h_eq
      rw [decide_one_le_ofBoolVec] at h_dec
      exact h_dec.symm
    rw [Set.indicator_of_notMem hnot]
    simp [hx]

private lemma measurableSet_eq_ofBoolVec {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (V : Fin n → Ω → ℝ) (hV : ∀ i : Fin n, Measurable (V i)) (x : Fin n → Bool) :
    MeasurableSet {ω : Ω | (fun i ↦ V i ω) = ofBoolVec x} := by
  have h_vec : Measurable (fun ω : Ω ↦ (fun i : Fin n ↦ V i ω)) :=
    measurable_pi_iff.mpr hV
  exact h_vec (measurableSet_singleton (ofBoolVec x))

lemma integral_liftFromBool_eq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin n → Ω → ℝ) (hV : ∀ i : Fin n, Measurable (V i))
    (hV01 : ∀ (i : Fin n) (ω : Ω), V i ω = 0 ∨ V i ω = 1)
    (g : (Fin n → Bool) → ℝ) :
    ∫ ω, liftFromBool g (fun i ↦ V i ω) ∂P =
      ∑ x : Fin n → Bool, g x * P.real {ω : Ω | (fun i ↦ V i ω) = ofBoolVec x} := by
  have h_pt : ∀ ω : Ω, liftFromBool g (fun i ↦ V i ω) =
      ∑ x : Fin n → Bool, g x *
        {ω' : Ω | (fun i ↦ V i ω') = ofBoolVec x}.indicator (fun _ ↦ (1 : ℝ)) ω := by
    intro ω
    unfold liftFromBool
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [prod_stepInd_eq_indicator_of_zero_one V hV01 x ω]
  simp_rw [h_pt]
  rw [integral_finsetSum Finset.univ (fun x _ ↦
    ((integrable_const (1 : ℝ)).indicator (measurableSet_eq_ofBoolVec V hV x)).const_mul (g x))]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [integral_const_mul]
  change g x * ∫ ω, {ω' : Ω | (fun i ↦ V i ω') = ofBoolVec x}.indicator 1 ω ∂P = _
  rw [integral_indicator_one (measurableSet_eq_ofBoolVec V hV x)]

lemma sum_probReal_eq_ofBoolVec {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin n → Ω → ℝ) (hV : ∀ i : Fin n, Measurable (V i))
    (hV01 : ∀ (i : Fin n) (ω : Ω), V i ω = 0 ∨ V i ω = 1) :
    ∑ x : Fin n → Bool, P.real {ω : Ω | (fun i ↦ V i ω) = ofBoolVec x} = 1 := by
  have h := integral_liftFromBool_eq P V hV hV01 (fun _ ↦ 1)
  simp only [one_mul] at h
  have h_lhs : ∫ ω, liftFromBool (fun _ ↦ 1) (fun i ↦ V i ω) ∂P = 1 := by
    simp_rw [liftFromBool_eq, integral_const, probReal_univ, smul_eq_mul, mul_one]
  linarith

/-- Layer-cake induction on `Fin n → Bool`: if $\sum_x g(x) p(x) \le \sum_y g(y) q(y)$ holds
for all
monotone $\{0, 1\}$-valued functions $g$, then it holds for all monotone real-valued functions
$g$. -/
lemma sum_mul_le_of_monotone_bool {n : ℕ}
    (p q : (Fin n → Bool) → ℝ)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ y, q y = 1)
    (h_ind : ∀ g : (Fin n → Bool) → ℝ, Monotone g → (∀ x, g x = 0 ∨ g x = 1) →
      ∑ x, g x * p x ≤ ∑ y, g y * q y) :
    ∀ (k : ℕ) (g : (Fin n → Bool) → ℝ), Monotone g →
      (Finset.univ.image g).card ≤ k →
      ∑ x, g x * p x ≤ ∑ y, g y * q y
  | 0, g, _, hcard => by
    have hne : (Finset.univ.image g).Nonempty := Finset.univ_nonempty.image g
    have hpos : 0 < (Finset.univ.image g).card := Finset.card_pos.mpr hne
    omega
  | k + 1, g, hg, hcard => by
    let S := Finset.univ.image g
    have hS_ne : S.Nonempty := Finset.univ_nonempty.image g
    by_cases hle1 : S.card ≤ 1
    · let m := S.min' hS_ne
      have hm_mem : m ∈ S := Finset.min'_mem S hS_ne
      have hg_eq : ∀ x : Fin n → Bool, g x = m := fun x ↦
        Finset.card_le_one_iff.mp hle1 (Finset.mem_image_of_mem g (Finset.mem_univ x)) hm_mem
      simp_rw [hg_eq, ← Finset.mul_sum, hp_sum, hq_sum]
      exact le_rfl
    · let m := S.min' hS_ne
      have hm_mem : m ∈ S := Finset.min'_mem S hS_ne
      let S' := S.erase m
      have hS'_card : S'.card = S.card - 1 := Finset.card_erase_of_mem hm_mem
      have hS'_ne : S'.Nonempty := Finset.card_pos.mp (by omega)
      let m₂ := S'.min' hS'_ne
      have hm₂_mem : m₂ ∈ S' := Finset.min'_mem S' hS'_ne
      have hm_lt_m₂ : m < m₂ := lt_of_le_of_ne
        (Finset.min'_le S m₂ (Finset.mem_of_mem_erase hm₂_mem))
        ( Ne.symm (Finset.ne_of_mem_erase hm₂_mem) )
      let g₁ : (Fin n → Bool) → ℝ := fun x ↦ max (g x) m₂
      let ind : (Fin n → Bool) → ℝ := fun x ↦ if m₂ ≤ g x then 1 else 0
      have hg₁_mono : Monotone g₁ := fun x y hxy ↦ max_le_max_right m₂ (hg hxy)
      have hind_mono : Monotone ind := by
        intro x y hxy
        unfold ind
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso; exact h2 (le_trans h1 (hg hxy))
        · exact zero_le_one
        · exact le_rfl
      have hind_01 : ∀ x, ind x = 0 ∨ ind x = 1 := by
        intro x; unfold ind; split_ifs <;> simp
      have hg_decomp : ∀ x : Fin n → Bool,
          g x = g₁ x - (m₂ - m) + (m₂ - m) * ind x := by
        intro x
        unfold g₁ ind
        by_cases h : m₂ ≤ g x
        · simp only [h, ↓reduceIte, max_eq_left h]
          ring
        · simp only [h, ↓reduceIte, max_eq_right (le_of_lt (not_le.mp h))]
          have hgx_eq_m : g x = m := by
            have hgx_S : g x ∈ S := Finset.mem_image_of_mem g (Finset.mem_univ x)
            by_contra hne
            have hgx_S' : g x ∈ S' := Finset.mem_erase.mpr ⟨hne, hgx_S⟩
            exact h (Finset.min'_le S' (g x) hgx_S')
          rw [hgx_eq_m]
          ring
      have hg₁_sub : Finset.univ.image g₁ ⊆ S' := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨x, _, rfl⟩
        unfold g₁
        by_cases h : m₂ ≤ g x
        · rw [max_eq_left h]
          refine Finset.mem_erase.mpr
            ⟨by linarith, Finset.mem_image_of_mem g (Finset.mem_univ x)⟩
        · rw [max_eq_right (le_of_lt (not_le.mp h))]
          exact hm₂_mem
      have hg₁_card : (Finset.univ.image g₁).card ≤ k := by
        have hle := Finset.card_le_card hg₁_sub
        change S.card ≤ k + 1 at hcard
        omega
      have h_ih := sum_mul_le_of_monotone_bool p q hp_sum hq_sum h_ind k g₁ hg₁_mono hg₁_card
      have h_ind_ineq := h_ind ind hind_mono hind_01
      have h_diff_nonneg : 0 ≤ m₂ - m := by linarith
      have h_mul_ind := mul_le_mul_of_nonneg_left h_ind_ineq h_diff_nonneg
      have h_sum_x : ∑ x, g x * p x =
          (∑ x, g₁ x * p x) - (m₂ - m) * (∑ x, p x) +
            (m₂ - m) * (∑ x, ind x * p x) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [hg_decomp x]
        ring
      have h_sum_y : ∑ y, g y * q y =
          (∑ y, g₁ y * q y) - (m₂ - m) * (∑ y, q y) +
            (m₂ - m) * (∑ y, ind y * q y) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [hg_decomp y]
        ring
      rw [h_sum_x, h_sum_y, hp_sum, hq_sum]
      linarith

/-- Finite-poset Strassen theorem on `Fin n → Bool` via geometric Hahn–Banach separation. -/
lemma exists_monotone_weights_bool {n : ℕ}
    (p q : (Fin n → Bool) → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x) (_hp_sum : ∑ x, p x = 1)
    (hq_nonneg : ∀ y, 0 ≤ q y) (hq_sum : ∑ y, q y = 1)
    (h_mono : ∀ g : (Fin n → Bool) → ℝ, Monotone g →
      ∑ x, g x * p x ≤ ∑ y, g y * q y) :
    ∃ w : BoolOrderPairs n → ℝ,
      (∀ r, 0 ≤ w r) ∧
      (∑ r, w r = 1) ∧
      (∀ x, ∑ r : BoolOrderPairs n, (if r.1.1 = x then w r else 0) = p x) ∧
      (∀ y, ∑ r : BoolOrderPairs n, (if r.1.2 = y then w r else 0) = q y) := by
  let R := BoolOrderPairs n
  let Q := Fin n → Bool
  let E := (Q → ℝ) × (Q → ℝ)
  let Δ : Set (R → ℝ) := {w : R → ℝ | (∀ r, 0 ≤ w r) ∧ ∑ r, w r = 1}
  let M : (R → ℝ) →ₗ[ℝ] E :=
    { toFun := fun w ↦
        (fun x ↦ ∑ r : R, if r.1.1 = x then w r else 0,
         fun y ↦ ∑ r : R, if r.1.2 = y then w r else 0)
      map_add' := fun w₁ w₂ ↦ by
        ext x
        · change (∑ r : R, if r.1.1 = x then w₁ r + w₂ r else 0) =
            (∑ r : R, if r.1.1 = x then w₁ r else 0) +
              (∑ r : R, if r.1.1 = x then w₂ r else 0)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          split_ifs <;> ring
        · change (∑ r : R, if r.1.2 = x then w₁ r + w₂ r else 0) =
            (∑ r : R, if r.1.2 = x then w₁ r else 0) +
              (∑ r : R, if r.1.2 = x then w₂ r else 0)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          split_ifs <;> ring
      map_smul' := fun c w ↦ by
        ext x
        · change (∑ r : R, if r.1.1 = x then c * w r else 0) =
            c * (∑ r : R, if r.1.1 = x then w r else 0)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          split_ifs <;> ring
        · change (∑ r : R, if r.1.2 = x then c * w r else 0) =
            c * (∑ r : R, if r.1.2 = x then w r else 0)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          split_ifs <;> ring }
  have hΔ_conv : Convex ℝ Δ := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    refine ⟨fun r ↦ add_nonneg (mul_nonneg ha (hw₁.1 r)) (mul_nonneg hb (hw₂.1 r)), ?_⟩
    simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hw₁.2, hw₂.2, mul_one, hab]
  have hΔ_eq : Δ = Set.pi Set.univ (fun _ : R ↦ Set.Icc (0 : ℝ) 1) ∩
      {w : R → ℝ | ∑ r, w r = 1} := by
    ext w
    simp only [Δ, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, Set.mem_Icc,
      forall_true_left]
    constructor
    · rintro ⟨hw0, hw1⟩
      refine ⟨fun r ↦ ⟨hw0 r, ?_⟩, hw1⟩
      rw [← hw1]
      exact Finset.single_le_sum (fun r' _ ↦ hw0 r') (Finset.mem_univ r)
    · rintro ⟨hwIcc, hw1⟩
      exact ⟨fun r ↦ (hwIcc r).1, hw1⟩
  have hΔ_comp : IsCompact Δ := by
    rw [hΔ_eq]
    exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).inter_right
      (isClosed_eq (continuous_finsetSum Finset.univ fun r _ ↦ continuous_apply r)
        continuous_const)
  have hM_cont : Continuous M := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun x ↦ continuous_finsetSum Finset.univ fun r _ ↦
        Continuous.if_const (r.1.1 = x) (continuous_apply r) continuous_const
    · exact continuous_pi fun y ↦ continuous_finsetSum Finset.univ fun r _ ↦
        Continuous.if_const (r.1.2 = y) (continuous_apply r) continuous_const
  let C : Set E := M '' Δ
  have hC_conv : Convex ℝ C := hΔ_conv.linear_image M
  have hC_closed : IsClosed C := (hΔ_comp.image hM_cont).isClosed
  by_contra h_not
  have h_not_mem : (p, q) ∉ C := by
    intro hmem
    rcases hmem with ⟨w, ⟨hw0, hw1⟩, hMw⟩
    have h1 := congr_arg Prod.fst hMw
    have h2 := congr_arg Prod.snd hMw
    exact h_not ⟨w, hw0, hw1, fun x ↦ congr_fun h1 x, fun y ↦ congr_fun h2 y⟩
  obtain ⟨L, u, hL_lt, hu_lt⟩ := geometric_hahn_banach_closed_point hC_conv hC_closed h_not_mem
  let α : Q → ℝ := fun x ↦ L (Pi.single x 1, 0)
  let β : Q → ℝ := fun y ↦ L (0, Pi.single y 1)
  have hL_apply : ∀ a b : Q → ℝ,
      L (a, b) = (∑ x : Q, α x * a x) + (∑ y : Q, β y * b y) := by
    intro a b
    have hab : (a, b) = (∑ x : Q, a x • (Pi.single x (1 : ℝ), (0 : Q → ℝ))) +
        (∑ y : Q, b y • ((0 : Q → ℝ), Pi.single y (1 : ℝ))) := by
      ext x'
      · change a x' = (∑ x : Q, a x • (Pi.single x (1 : ℝ), (0 : Q → ℝ))).1 x' +
            (∑ y : Q, b y • ((0 : Q → ℝ), Pi.single y (1 : ℝ))).1 x'
        rw [Prod.fst_sum, Prod.fst_sum]
        simp only [Prod.smul_fst, smul_zero, Finset.sum_const_zero, Pi.zero_apply, add_zero,
          Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero]
        rw [Finset.sum_eq_single x' (fun x _ hx ↦ by simp [hx.symm])
          (fun h ↦ False.elim (h (Finset.mem_univ x')))]
        simp
      · change b x' = (∑ x : Q, a x • (Pi.single x (1 : ℝ), (0 : Q → ℝ))).2 x' +
            (∑ y : Q, b y • ((0 : Q → ℝ), Pi.single y (1 : ℝ))).2 x'
        rw [Prod.snd_sum, Prod.snd_sum]
        simp only [Prod.smul_snd, smul_zero, Finset.sum_const_zero, Pi.zero_apply, zero_add,
          Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero]
        rw [Finset.sum_eq_single x' (fun y _ hy ↦ by simp [hy.symm])
          (fun h ↦ False.elim (h (Finset.mem_univ x')))]
        simp
    rw [hab, map_add, map_sum, map_sum]
    congr 1
    · refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    · refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [map_smul, smul_eq_mul, mul_comm]
  have h_order_le : ∀ x y : Q, x ≤ y → α x + β y ≤ u := by
    intro x y hxy
    let r : R := ⟨(x, y), hxy⟩
    let w₀ : R → ℝ := Pi.single r 1
    have hw₀ : w₀ ∈ Δ := by
      refine ⟨fun r' ↦ ?_, ?_⟩
      · simp only [w₀, Pi.single_apply]
        split_ifs <;> linarith
      · simp [w₀]
    have hMw₀ : M w₀ = (Pi.single x 1, Pi.single y 1) := by
      ext z
      · simp only [M, LinearMap.coe_mk, AddHom.coe_mk, w₀, Pi.single_apply]
        rw [Finset.sum_eq_single r]
        · simp [r, eq_comm]
        · intro r' _ hr'
          simp [hr']
        · intro hr; exfalso; exact hr (Finset.mem_univ r)
      · simp only [M, LinearMap.coe_mk, AddHom.coe_mk, w₀, Pi.single_apply]
        rw [Finset.sum_eq_single r]
        · simp [r, eq_comm]
        · intro r' _ hr'
          simp [hr']
        · intro hr; exfalso; exact hr (Finset.mem_univ r)
    have h_lt := hL_lt (M w₀) ⟨w₀, hw₀, rfl⟩
    rw [hMw₀, hL_apply] at h_lt
    have h1 : (∑ x' : Q, α x' * (Pi.single x (1 : ℝ) : Q → ℝ) x') = α x := by
      rw [Finset.sum_eq_single x (fun x' _ hx' ↦ by simp [hx'])
        (fun h ↦ False.elim (h (Finset.mem_univ x)))]
      simp
    have h2 : (∑ y' : Q, β y' * (Pi.single y (1 : ℝ) : Q → ℝ) y') = β y := by
      rw [Finset.sum_eq_single y (fun y' _ hy' ↦ by simp [hy'])
        (fun h ↦ False.elim (h (Finset.mem_univ y)))]
      simp
    linarith
  let g : Q → ℝ := fun x ↦
    (Finset.univ.filter (fun z : Q ↦ z ≤ x)).sup' ⟨x, by simp⟩ α
  have hg_mono : Monotone g := by
    intro x y hxy
    refine Finset.sup'_mono α ?_ ⟨x, by simp⟩
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact le_trans hz hxy
  have hα_le_g : ∀ x : Q, α x ≤ g x := fun x ↦
    Finset.le_sup' α (by simp : x ∈ Finset.univ.filter (fun z : Q ↦ z ≤ x))
  have hg_le_β : ∀ y : Q, g y ≤ u - β y := by
    intro y
    refine Finset.sup'_le ⟨y, by simp⟩ α fun z hz ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    linarith [h_order_le z y hz]
  have hL_pq := hL_apply p q
  have h_sum_α : ∑ x : Q, α x * p x ≤ ∑ x : Q, g x * p x :=
    Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right (hα_le_g x) (hp_nonneg x)
  have h_sum_β : ∑ y : Q, β y * q y ≤ ∑ y : Q, (u - g y) * q y :=
    Finset.sum_le_sum fun y _ ↦
      mul_le_mul_of_nonneg_right (by linarith [hg_le_β y]) (hq_nonneg y)
  have h_sub_sum : ∑ y : Q, (u - g y) * q y = u - ∑ y : Q, g y * q y := by
    have h1 : ∑ y : Q, (u - g y) * q y = (∑ y : Q, u * q y) - ∑ y : Q, g y * q y := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ ↦ by ring
    rw [h1, ← Finset.mul_sum, hq_sum, mul_one]
  have h_mono_g := h_mono g hg_mono
  linarith

lemma measure_map_zero_one_apply {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Fin n → Ω → ℝ) (hV : ∀ i : Fin n, Measurable (V i))
    (hV01 : ∀ (i : Fin n) (ω : Ω), V i ω = 0 ∨ V i ω = 1)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) :
    Measure.map (fun ω i ↦ V i ω) P s =
      ∑ x : Fin n → Bool,
        if ofBoolVec x ∈ s then
          ENNReal.ofReal (P.real {ω : Ω | (fun i ↦ V i ω) = ofBoolVec x})
        else 0 := by
  have hV_meas : Measurable (fun ω i ↦ V i ω) := measurable_pi_iff.mpr hV
  have h_prob := integral_liftFromBool_eq P V hV hV01
    (fun x ↦ if ofBoolVec x ∈ s then 1 else 0)
  have h_lhs : ∫ ω, liftFromBool (fun x ↦ if ofBoolVec x ∈ s then 1 else 0)
      (fun i ↦ V i ω) ∂P = (Measure.map (fun ω i ↦ V i ω) P).real s := by
    have h_pt : ∀ ω : Ω,
        liftFromBool (fun x ↦ if ofBoolVec x ∈ s then 1 else 0) (fun i ↦ V i ω) =
          ((fun ω' i ↦ V i ω') ⁻¹' s).indicator (1 : Ω → ℝ) ω := by
      intro ω
      rw [liftFromBool_eq]
      have h_eq := eq_ofBoolVec_decide (fun i ↦ hV01 i ω)
      by_cases hmem : (fun i ↦ V i ω) ∈ s
      · have hmem' : ofBoolVec (fun i ↦ decide (1 ≤ V i ω)) ∈ s := h_eq ▸ hmem
        simp [hmem, hmem']
      · have hmem' : ofBoolVec (fun i ↦ decide (1 ≤ V i ω)) ∉ s := h_eq ▸ hmem
        simp [hmem, hmem']
    simp_rw [h_pt]
    rw [integral_indicator_one (hV_meas hs), map_measureReal_apply hV_meas hs]
  rw [h_lhs] at h_prob
  have : IsProbabilityMeasure (Measure.map (fun ω i ↦ V i ω) P) :=
    isProbabilityMeasure_map' hV_meas.aemeasurable
  have h_ofReal := congr_arg ENNReal.ofReal h_prob
  rw [ofReal_measureReal] at h_ofReal
  rw [h_ofReal, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    split_ifs <;> simp
  · intro x _
    split_ifs <;> simp [measureReal_nonneg]

lemma norm_le_one_of_zero_or_one {x : ℝ} (h : x = 0 ∨ x = 1) : ‖x‖ ≤ 1 := by
  rcases h with rfl | rfl <;> simp


end SteinMethod
