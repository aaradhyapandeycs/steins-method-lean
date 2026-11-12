/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# FKG / Harris–Kleitman Inequality for Independent Indicators
(`Formalization.PoissonSizeBias.Monotone.FKGCore`)

Proves the FKG / Harris–Kleitman correlation inequality (`SteinIntro.tex:2395-2401`, cited from
`[lig05]` Chapter 2) from scratch on the Boolean hypercube (`bernoulliCubeExpect_mul_le`) and for
independent `{0, 1}`-indicators (`fkg_independent_indicators_on`, `fkg_independent_indicators`).
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-! ### Part 1: Algebraic Harris–Kleitman Inequality on the Boolean Hypercube -/

/-- Map a Boolean to `{0, 1} ⊆ ℕ` (`false ↦ 0`, `true ↦ 1`). -/
def boolToNat (b : Bool) : ℕ :=
  if b then 1 else 0

/-- Coordinatewise embedding of `Fin N → Bool` into `Fin N → ℕ`. -/
def vecBoolToNat {N : ℕ} (b : Fin N → Bool) (j : Fin N) : ℕ :=
  boolToNat (b j)

lemma monotone_boolToNat : Monotone boolToNat := by
  intro a b hab
  cases a <;> cases b <;> revert hab <;> decide

lemma monotone_vecBoolToNat {N : ℕ} : Monotone (vecBoolToNat (N := N)) := by
  intro a b hab j
  exact monotone_boolToNat (hab j)

/-- Product weight of a Boolean configuration `b : Fin N → Bool` under success probabilities
`p : Fin N → ℝ`. -/
def bernoulliCubeWeight {N : ℕ} (p : Fin N → ℝ) (b : Fin N → Bool) : ℝ :=
  ∏ j : Fin N, if b j then p j else 1 - p j

/-- Weighted expectation on `Fin N → Bool` under product Bernoulli weights `p`. -/
def bernoulliCubeExpect {N : ℕ} (p : Fin N → ℝ) (G : (Fin N → Bool) → ℝ) : ℝ :=
  ∑ b : Fin N → Bool, bernoulliCubeWeight p b * G b

private lemma bernoulliCubeWeight_nonneg {N : ℕ} {p : Fin N → ℝ}
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1) (b : Fin N → Bool) :
    0 ≤ bernoulliCubeWeight p b := by
  unfold bernoulliCubeWeight
  refine Finset.prod_nonneg fun j _ ↦ ?_
  cases b j
  · simp [hp1 j]
  · simp [hp0 j]

private lemma bernoulliCubeExpect_cons {N : ℕ} (p : Fin (N + 1) → ℝ)
    (G : (Fin (N + 1) → Bool) → ℝ) :
    bernoulliCubeExpect p G =
      p 0 * bernoulliCubeExpect (Fin.tail p) (fun t ↦ G (Fin.cons true t)) +
        (1 - p 0) * bernoulliCubeExpect (Fin.tail p) (fun t ↦ G (Fin.cons false t)) := by
  unfold bernoulliCubeExpect bernoulliCubeWeight
  have h_equiv := (Fin.consEquiv (fun _ : Fin (N + 1) ↦ Bool)).sum_comp
    (fun b : Fin (N + 1) → Bool ↦ (∏ j : Fin (N + 1), if b j then p j else 1 - p j) * G b)
  rw [← h_equiv, Fintype.sum_prod_type, Fintype.sum_bool]
  have h_true :
      (∑ t : Fin N → Bool,
        (∏ j : Fin (N + 1),
          if (Fin.consEquiv (fun _ : Fin (N + 1) ↦ Bool)) (true, t) j then p j else 1 - p j) *
          G ((Fin.consEquiv (fun _ : Fin (N + 1) ↦ Bool)) (true, t))) =
        p 0 * ∑ t : Fin N → Bool,
          (∏ j : Fin N, if t j then Fin.tail p j else 1 - Fin.tail p j) *
            G (Fin.cons true t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Fin.prod_univ_succ]
    change (p 0 * ∏ i : Fin N, if t i = true then Fin.tail p i else 1 - Fin.tail p i) *
      G (Fin.cons true t) = _
    ring
  have h_false :
      (∑ t : Fin N → Bool,
        (∏ j : Fin (N + 1),
          if (Fin.consEquiv (fun _ : Fin (N + 1) ↦ Bool)) (false, t) j then p j else 1 - p j) *
          G ((Fin.consEquiv (fun _ : Fin (N + 1) ↦ Bool)) (false, t))) =
        (1 - p 0) * ∑ t : Fin N → Bool,
          (∏ j : Fin N, if t j then Fin.tail p j else 1 - Fin.tail p j) *
            G (Fin.cons false t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [Fin.prod_univ_succ]
    change ((1 - p 0) * ∏ i : Fin N, if t i = true then Fin.tail p i else 1 - Fin.tail p i) *
      G (Fin.cons false t) = _
    ring
  rw [h_true, h_false]

private lemma bernoulliCubeExpect_mono {N : ℕ} {p : Fin N → ℝ}
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    {G H : (Fin N → Bool) → ℝ} (hGH : ∀ b, G b ≤ H b) :
    bernoulliCubeExpect p G ≤ bernoulliCubeExpect p H := by
  unfold bernoulliCubeExpect
  refine Finset.sum_le_sum fun b _ ↦ ?_
  exact mul_le_mul_of_nonneg_left (hGH b) (bernoulliCubeWeight_nonneg hp0 hp1 b)

/-- Algebraic Harris–Kleitman correlation inequality on `Fin N → Bool`: any two coordinatewise
monotone functions `G, H : (Fin N → Bool) → ℝ` are positively correlated under product
Bernoulli
weights (`SteinIntro.tex:2398-2401`). -/
theorem bernoulliCubeExpect_mul_le {N : ℕ} {p : Fin N → ℝ}
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∀ j, p j ≤ 1)
    {G H : (Fin N → Bool) → ℝ} (hG : Monotone G) (hH : Monotone H) :
    bernoulliCubeExpect p G * bernoulliCubeExpect p H ≤
      bernoulliCubeExpect p (fun b ↦ G b * H b) := by
  induction N with
  | zero =>
      unfold bernoulliCubeExpect bernoulliCubeWeight
      let b₀ : Fin 0 → Bool := fun _ ↦ false
      rw [Fintype.sum_subsingleton _ b₀,
        Fintype.sum_subsingleton _ b₀,
        Fintype.sum_subsingleton _ b₀]
      simp
  | succ N ih =>
      rw [bernoulliCubeExpect_cons p G, bernoulliCubeExpect_cons p H,
        bernoulliCubeExpect_cons p (fun b ↦ G b * H b)]
      have hp0' : ∀ j : Fin N, 0 ≤ Fin.tail p j := fun j ↦ hp0 j.succ
      have hp1' : ∀ j : Fin N, Fin.tail p j ≤ 1 := fun j ↦ hp1 j.succ
      have hGt : Monotone (fun t : Fin N → Bool ↦ G (Fin.cons true t)) := by
        intro a b hab
        exact hG (Fin.cons_le_cons.mpr ⟨le_rfl, hab⟩)
      have hGf : Monotone (fun t : Fin N → Bool ↦ G (Fin.cons false t)) := by
        intro a b hab
        exact hG (Fin.cons_le_cons.mpr ⟨le_rfl, hab⟩)
      have hHt : Monotone (fun t : Fin N → Bool ↦ H (Fin.cons true t)) := by
        intro a b hab
        exact hH (Fin.cons_le_cons.mpr ⟨le_rfl, hab⟩)
      have hHf : Monotone (fun t : Fin N → Bool ↦ H (Fin.cons false t)) := by
        intro a b hab
        exact hH (Fin.cons_le_cons.mpr ⟨le_rfl, hab⟩)
      have ih_t := ih hp0' hp1' hGt hHt
      have ih_f := ih hp0' hp1' hGf hHf
      have h_ft : ∀ t : Fin N → Bool,
          (Fin.cons false t : Fin (N + 1) → Bool) ≤ Fin.cons true t := by
        intro t
        exact Fin.cons_le_cons.mpr ⟨by decide, le_rfl⟩
      have hG_tf : bernoulliCubeExpect (Fin.tail p) (fun t ↦ G (Fin.cons false t)) ≤
          bernoulliCubeExpect (Fin.tail p) (fun t ↦ G (Fin.cons true t)) :=
        bernoulliCubeExpect_mono hp0' hp1' fun t ↦ hG (h_ft t)
      have hH_tf : bernoulliCubeExpect (Fin.tail p) (fun t ↦ H (Fin.cons false t)) ≤
          bernoulliCubeExpect (Fin.tail p) (fun t ↦ H (Fin.cons true t)) :=
        bernoulliCubeExpect_mono hp0' hp1' fun t ↦ hH (h_ft t)
      have hq0 : 0 ≤ p 0 := hp0 0
      have hq1 : 0 ≤ 1 - p 0 := sub_nonneg.mpr (hp1 0)
      set Gt := bernoulliCubeExpect (Fin.tail p) (fun t ↦ G (Fin.cons true t))
      set Gf := bernoulliCubeExpect (Fin.tail p) (fun t ↦ G (Fin.cons false t))
      set Ht := bernoulliCubeExpect (Fin.tail p) (fun t ↦ H (Fin.cons true t))
      set Hf := bernoulliCubeExpect (Fin.tail p) (fun t ↦ H (Fin.cons false t))
      set GHt := bernoulliCubeExpect (Fin.tail p)
        (fun t ↦ G (Fin.cons true t) * H (Fin.cons true t))
      set GHf := bernoulliCubeExpect (Fin.tail p)
        (fun t ↦ G (Fin.cons false t) * H (Fin.cons false t))
      have h1 : 0 ≤ p 0 * (GHt - Gt * Ht) := mul_nonneg hq0 (sub_nonneg.mpr ih_t)
      have h2 : 0 ≤ (1 - p 0) * (GHf - Gf * Hf) := mul_nonneg hq1 (sub_nonneg.mpr ih_f)
      have h3 : 0 ≤ p 0 * (1 - p 0) * ((Gt - Gf) * (Ht - Hf)) :=
        mul_nonneg (mul_nonneg hq0 hq1)
          (mul_nonneg (sub_nonneg.mpr hG_tf) (sub_nonneg.mpr hH_tf))
      have hid : (p 0 * GHt + (1 - p 0) * GHf) -
          (p 0 * Gt + (1 - p 0) * Gf) * (p 0 * Ht + (1 - p 0) * Hf) =
          p 0 * (GHt - Gt * Ht) + (1 - p 0) * (GHf - Gf * Hf) +
            p 0 * (1 - p 0) * ((Gt - Gf) * (Ht - Hf)) := by ring
      linarith

/-! ### Part 2: Measure-Theoretic Reduction for Independent `{0, 1}`-Indicators -/

/-- Cylinder event where `Y : Fin N → Ω → ℕ` matches a Boolean configuration
`b : Fin N → Bool`. -/
def indicatorCylEvent {Ω : Type*} {N : ℕ}
    (Y : Fin N → Ω → ℕ) (b : Fin N → Bool) : Set Ω :=
  ⋂ j ∈ (Finset.univ : Finset (Fin N)),
    Y j ⁻¹' (if b j then ({1} : Set ℕ) else {1}ᶜ)

private lemma measurableSet_indicatorCylEvent {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {Y : Fin N → Ω → ℕ} (hY : ∀ j, Measurable (Y j)) (b : Fin N → Bool) :
    MeasurableSet (indicatorCylEvent Y b) := by
  unfold indicatorCylEvent
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun j _ ↦ ?_
  exact hY j .of_discrete

private lemma measureReal_indicatorCylEvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} {Y : Fin N → Ω → ℕ}
    (hY : ∀ j, Measurable (Y j)) (h_indep : ProbabilityTheory.iIndepFun Y P)
    (b : Fin N → Bool) :
    P.real (indicatorCylEvent Y b) =
      bernoulliCubeWeight (fun j ↦ P.real {ω | Y j ω = 1}) b := by
  unfold indicatorCylEvent bernoulliCubeWeight
  have h_sets : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      MeasurableSet (if b j then ({1} : Set ℕ) else {1}ᶜ) := fun j _ ↦ .of_discrete
  have h_prod := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp h_indep)
    Finset.univ h_sets
  rw [measureReal_def, h_prod, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  change P.real (Y j ⁻¹' (if b j then ({1} : Set ℕ) else {1}ᶜ)) = _
  cases hbj : b j
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h_compl : Y j ⁻¹' ({1} : Set ℕ)ᶜ = (Y j ⁻¹' {1})ᶜ := rfl
    rw [h_compl, probReal_compl_eq_one_sub (hY j (measurableSet_singleton 1))]
    rfl
  · simp only [↓reduceIte]
    rfl

private lemma ae_eq_sum_indicatorCylEvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N : ℕ} {Y : Fin N → Ω → ℕ}
    (hY_01 : ∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (Φ : (Fin N → ℕ) → ℝ) :
    (fun ω ↦ Φ (fun j ↦ Y j ω)) =ᵐ[P]
      fun ω ↦ ∑ b : Fin N → Bool,
        (indicatorCylEvent Y b).indicator (fun _ ↦ Φ (vecBoolToNat b)) ω := by
  have h_all : ∀ᵐ ω ∂P, ∀ j : Fin N, Y j ω = 0 ∨ Y j ω = 1 :=
    Filter.eventually_all.mpr hY_01
  filter_upwards [h_all] with ω hω
  let b₀ : Fin N → Bool := fun j ↦ decide (Y j ω = 1)
  have h_mem₀ : ω ∈ indicatorCylEvent Y b₀ := by
    simp only [indicatorCylEvent, Set.mem_iInter, Finset.mem_univ, forall_true_left,
      Set.mem_preimage, b₀]
    intro j
    by_cases h1 : Y j ω = 1 <;> simp [h1]
  have h_not_mem : ∀ b : Fin N → Bool, b ≠ b₀ → ω ∉ indicatorCylEvent Y b := by
    intro b hb hmem
    apply hb
    funext j
    simp only [indicatorCylEvent, Set.mem_iInter, Finset.mem_univ, forall_true_left,
      Set.mem_preimage] at hmem
    have hj := hmem j
    by_cases h1 : Y j ω = 1
    · cases hbj : b j
      · simp [hbj, h1] at hj
      · simp [b₀, h1]
    · cases hbj : b j
      · simp [b₀, h1]
      · simp [hbj, h1] at hj
  rw [Finset.sum_eq_single b₀]
  · rw [Set.indicator_of_mem h_mem₀]
    congr 1
    funext j
    simp only [vecBoolToNat, boolToNat, b₀]
    rcases hω j with h0 | h1
    · simp [h0]
    · simp [h1]
  · intro b _ hb
    exact Set.indicator_of_notMem (h_not_mem b hb) _
  · intro h_abs
    exact False.elim (h_abs (Finset.mem_univ b₀))

/-- Any function of `N` almost-sure `{0, 1}`-valued random variables is Bochner integrable, and
under mutual independence its expectation equals `bernoulliCubeExpect`
(`SteinIntro.tex:2395-2401`). -/
theorem integrable_and_integral_comp_zero_one_indep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} {Y : Fin N → Ω → ℕ}
    (hY_meas : ∀ j : Fin N, AEMeasurable (Y j) P)
    (hY_01 : ∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (hY_indep : ProbabilityTheory.iIndepFun Y P)
    (Φ : (Fin N → ℕ) → ℝ) :
    Integrable (fun ω ↦ Φ (fun j ↦ Y j ω)) P ∧
      ∫ ω, Φ (fun j ↦ Y j ω) ∂P =
        bernoulliCubeExpect
          (fun j ↦ P.real {ω | Y j ω = 1}) (fun b ↦ Φ (vecBoolToNat b)) := by
  let Y' : Fin N → Ω → ℕ := fun j ↦ (hY_meas j).mk (Y j)
  have hY'_meas : ∀ j, Measurable (Y' j) := fun j ↦ (hY_meas j).measurable_mk
  have hY'_ae : ∀ j, Y j =ᵐ[P] Y' j := fun j ↦ (hY_meas j).ae_eq_mk
  have hY'_01 : ∀ j : Fin N, ∀ᵐ ω ∂P, Y' j ω = 0 ∨ Y' j ω = 1 := by
    intro j
    filter_upwards [hY_01 j, hY'_ae j] with ω h01 h_eq
    rwa [← h_eq]
  have hY'_indep : ProbabilityTheory.iIndepFun Y' P :=
    ProbabilityTheory.iIndepFun.congr hY'_ae hY_indep
  have hp_eq : (fun j : Fin N ↦ P.real {ω | Y' j ω = 1}) =
      fun j : Fin N ↦ P.real {ω | Y j ω = 1} := by
    funext j
    refine measureReal_congr ?_
    filter_upwards [hY'_ae j] with ω h_eq
    simp [h_eq]
  have h_fn_ae :
      (fun ω ↦ Φ (fun j ↦ Y j ω)) =ᵐ[P] (fun ω ↦ Φ (fun j ↦ Y' j ω)) := by
    have h_all : ∀ᵐ ω ∂P, ∀ j : Fin N, Y j ω = Y' j ω := Filter.eventually_all.mpr hY'_ae
    filter_upwards [h_all] with ω hω
    congr 1
    funext j
    exact hω j
  have h_sum_ae := h_fn_ae.trans (ae_eq_sum_indicatorCylEvent P hY'_01 Φ)
  have h_sum_int : Integrable (fun ω ↦ ∑ b : Fin N → Bool,
      (indicatorCylEvent Y' b).indicator (fun _ ↦ Φ (vecBoolToNat b)) ω) P := by
    refine integrable_finsetSum Finset.univ fun b _ ↦ ?_
    exact (integrable_const (Φ (vecBoolToNat b))).indicator
      (measurableSet_indicatorCylEvent hY'_meas b)
  refine ⟨h_sum_int.congr h_sum_ae.symm, ?_⟩
  rw [integral_congr_ae h_sum_ae,
    integral_finsetSum Finset.univ fun b _ ↦
      (integrable_const (Φ (vecBoolToNat b))).indicator
        (measurableSet_indicatorCylEvent hY'_meas b)]
  unfold bernoulliCubeExpect
  rw [← hp_eq]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [integral_indicator (measurableSet_indicatorCylEvent hY'_meas b),
    setIntegral_const, smul_eq_mul, measureReal_indicatorCylEvent P hY'_meas hY'_indep b]

private lemma vecBoolToNat_mem_cube {N : ℕ} (b : Fin N → Bool) :
    vecBoolToNat b ∈ {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} := by
  intro j
  simp only [vecBoolToNat, boolToNat]
  split_ifs <;> omega

/-- **FKG / Harris–Kleitman Inequality** (`SteinIntro.tex:2395-2401`, `[lig05]` Chapter 2
and proved from scratch): if $\mathbf{Y} = (Y_j)_{j=1}^N$ are independent $\{0, 1\}$-indicators and
$g, h : \mathbb{N}^N \to \mathbb{R}$ are both increasing (`MonotoneOn`) or both decreasing
(`AntitoneOn`) on $\{0, 1\}^N = \{y \mid \forall j,\, y_j \le 1\}$, then
$\mathbb{E}[g(\mathbf{Y})]\,\mathbb{E}[h(\mathbf{Y})] \le
\mathbb{E}[g(\mathbf{Y})\,h(\mathbf{Y})]$. -/
theorem fkg_independent_indicators_on {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} {Y : Fin N → Ω → ℕ} {g h : (Fin N → ℕ) → ℝ}
    (hY_meas : ∀ j : Fin N, AEMeasurable (Y j) P)
    (hY_01 : ∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (hY_indep : ProbabilityTheory.iIndepFun Y P)
    (h_mono :
      (MonotoneOn g {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} ∧
        MonotoneOn h {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) ∨
      (AntitoneOn g {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} ∧
        AntitoneOn h {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1})) :
    (∫ ω, g (fun j ↦ Y j ω) ∂P) * (∫ ω, h (fun j ↦ Y j ω) ∂P) ≤
      ∫ ω, g (fun j ↦ Y j ω) * h (fun j ↦ Y j ω) ∂P := by
  have hp0 : ∀ j : Fin N, 0 ≤ P.real {ω | Y j ω = 1} := fun _ ↦ measureReal_nonneg
  have hp1 : ∀ j : Fin N, P.real {ω | Y j ω = 1} ≤ 1 := fun _ ↦ measureReal_le_one
  rw [(integrable_and_integral_comp_zero_one_indep P hY_meas hY_01 hY_indep g).2,
    (integrable_and_integral_comp_zero_one_indep P hY_meas hY_01 hY_indep h).2,
    (integrable_and_integral_comp_zero_one_indep P hY_meas hY_01 hY_indep (fun y ↦ g y * h y)).2]
  rcases h_mono with ⟨hg, hh⟩ | ⟨hg, hh⟩
  · exact bernoulliCubeExpect_mul_le hp0 hp1
      (fun a b hab ↦
        hg (vecBoolToNat_mem_cube a) (vecBoolToNat_mem_cube b) (monotone_vecBoolToNat hab))
      (fun a b hab ↦
        hh (vecBoolToNat_mem_cube a) (vecBoolToNat_mem_cube b) (monotone_vecBoolToNat hab))
  · have hg' : Monotone (fun b : Fin N → Bool ↦ -g (vecBoolToNat b)) :=
      fun a b hab ↦ neg_le_neg
        (hg (vecBoolToNat_mem_cube a) (vecBoolToNat_mem_cube b) (monotone_vecBoolToNat hab))
    have hh' : Monotone (fun b : Fin N → Bool ↦ -h (vecBoolToNat b)) :=
      fun a b hab ↦ neg_le_neg
        (hh (vecBoolToNat_mem_cube a) (vecBoolToNat_mem_cube b) (monotone_vecBoolToNat hab))
    have h_neg := bernoulliCubeExpect_mul_le hp0 hp1 hg' hh'
    have h_neg_g : bernoulliCubeExpect (fun j ↦ P.real {ω | Y j ω = 1})
        (fun b ↦ -g (vecBoolToNat b)) =
        -bernoulliCubeExpect
          (fun j ↦ P.real {ω | Y j ω = 1}) (fun b ↦ g (vecBoolToNat b)) := by
      unfold bernoulliCubeExpect
      simp only [mul_neg, Finset.sum_neg_distrib]
    have h_neg_h : bernoulliCubeExpect (fun j ↦ P.real {ω | Y j ω = 1})
        (fun b ↦ -h (vecBoolToNat b)) =
        -bernoulliCubeExpect
          (fun j ↦ P.real {ω | Y j ω = 1}) (fun b ↦ h (vecBoolToNat b)) := by
      unfold bernoulliCubeExpect
      simp only [mul_neg, Finset.sum_neg_distrib]
    have h_neg_gh : (fun b : Fin N → Bool ↦ (-g (vecBoolToNat b)) * (-h (vecBoolToNat b))) =
        fun b : Fin N → Bool ↦ g (vecBoolToNat b) * h (vecBoolToNat b) := by
      funext b
      ring
    rw [h_neg_g, h_neg_h, neg_mul_neg, h_neg_gh] at h_neg
    exact h_neg

/-- **FKG / Harris–Kleitman Inequality** (`SteinIntro.tex:2395-2401`, `[lig05]` Chapter 2
and proved from scratch): if $\mathbf{Y} = (Y_j)_{j=1}^N$ are independent $\{0, 1\}$-indicators and
$g, h : \mathbb{N}^N \to \mathbb{R}$ are both increasing (`Monotone`) or both decreasing
(`Antitone`), then $\mathbb{E}[g(\mathbf{Y})]\,\mathbb{E}[h(\mathbf{Y})] \le
\mathbb{E}[g(\mathbf{Y})\,h(\mathbf{Y})]$. -/
theorem fkg_independent_indicators {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} {Y : Fin N → Ω → ℕ} {g h : (Fin N → ℕ) → ℝ}
    (hY_meas : ∀ j : Fin N, AEMeasurable (Y j) P)
    (hY_01 : ∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (hY_indep : ProbabilityTheory.iIndepFun Y P)
    (h_mono : (Monotone g ∧ Monotone h) ∨ (Antitone g ∧ Antitone h)) :
    (∫ ω, g (fun j ↦ Y j ω) ∂P) * (∫ ω, h (fun j ↦ Y j ω) ∂P) ≤
      ∫ ω, g (fun j ↦ Y j ω) * h (fun j ↦ Y j ω) ∂P := by
  refine fkg_independent_indicators_on P hY_meas hY_01 hY_indep ?_
  rcases h_mono with ⟨hg, hh⟩ | ⟨hg, hh⟩
  · exact Or.inl ⟨hg.monotoneOn _, hh.monotoneOn _⟩
  · exact Or.inr ⟨hg.antitoneOn _, hh.antitoneOn _⟩


end SteinMethod
