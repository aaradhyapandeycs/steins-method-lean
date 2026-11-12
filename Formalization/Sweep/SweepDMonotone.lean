/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Monotone.FKG
import Formalization.PoissonSizeBias.Monotone.Lemma4_18
import Formalization.PoissonSizeBias.Core.Basic

/-!
# SWEEP-D Section 4.3.3 Proof Claims (`Formalization.Sweep.SweepDMonotone`)

Proves the two Section 4.3.3 proof claims accepted in `docs/reviews/stmts-review-SWEEP-D.md`:
* `thm4_17_comp_monotone_corrected` (`Thm4_17_comp_monotone_corrected`, `SteinIntro.tex:2395-2396`;
  `D-D3` / `ISSUE-4.17`), together with the library refutation
  `not_thm4_17_comp_monotone_printed` of the mixed-direction reading.
* `thm4_17_implicit_coupling_corrected` (`Thm4_17_implicit_coupling_corrected`,
  `SteinIntro.tex:2392-2394` echoing `L2375-2376`; `D-D2` / `ISSUE-4.17`).
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-- Theorem 4.17 proof composition monotonicity step, corrected (`SteinIntro.tex:2395-2396`;
`docs/reviews/stmts-review-SWEEP-D.md` `D-D3`, `ISSUE-4.17`). -/
theorem thm4_17_comp_monotone_corrected
    {N n : ℕ} {f : Fin n → (Fin N → ℕ) → ℕ} {φ : (Fin n → ℕ) → ℝ}
    (hφ : Monotone φ) :
    let cube : Set (Fin N → ℕ) := {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}
    ((∀ i : Fin n, MonotoneOn (f i) cube) →
      MonotoneOn (fun y ↦ φ (fun i ↦ f i y)) cube) ∧
    ((∀ i : Fin n, AntitoneOn (f i) cube) →
      AntitoneOn (fun y ↦ φ (fun i ↦ f i y)) cube) := by
  dsimp only
  exact ⟨fun hf _ hy₁ _ hy₂ hle ↦ hφ fun i ↦ hf i hy₁ hy₂ hle,
    fun hf _ hy₁ _ hy₂ hle ↦ hφ fun i ↦ hf i hy₁ hy₂ hle⟩

/-- Library refutation of the mixed-direction reading of `SteinIntro.tex:2395-2396`
(`ISSUE-4.17` pinpoint note): for $N = 2, n = 2$, $f_0(y) = y_0$ (`MonotoneOn`),
$f_1(y) = 1 - y_1$ (`AntitoneOn`), and increasing indicator $\phi(x) = \mathbf{1}[x_0 \ge 1 \wedge
x_1 \ge 1]$, $\phi \circ (f_0, f_1)$ is neither `MonotoneOn` nor `AntitoneOn` on $\{0, 1\}^2$. -/
theorem not_thm4_17_comp_monotone_printed :
    ¬ (∀ (N n : ℕ) (f : Fin n → (Fin N → ℕ) → ℕ) (φ : (Fin n → ℕ) → ℝ),
      Monotone φ →
      (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
      (∀ i : Fin n, ∀ y : Fin N → ℕ, (∀ j : Fin N, y j ≤ 1) → f i y = 0 ∨ f i y = 1) →
      (∀ i : Fin n,
        MonotoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} ∨
          AntitoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) →
      MonotoneOn (fun y ↦ φ (fun i ↦ f i y)) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} ∨
        AntitoneOn (fun y ↦ φ (fun i ↦ f i y)) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) := by
  intro h_all
  let f : Fin 2 → (Fin 2 → ℕ) → ℕ := fun i y ↦ if i = 0 then y 0 else 1 - y 1
  let φ : (Fin 2 → ℕ) → ℝ := fun x ↦ if 1 ≤ x 0 ∧ 1 ≤ x 1 then 1 else 0
  have hφ_mono : Monotone φ := by
    intro a b hab
    dsimp [φ]
    split_ifs with ha hb hb
    · exact le_rfl
    · exact False.elim (hb ⟨ha.1.trans (hab 0), ha.2.trans (hab 1)⟩)
    · norm_num
    · exact le_rfl
  have hφ_01 : ∀ x : Fin 2 → ℕ, φ x = 0 ∨ φ x = 1 := fun x ↦ by
    dsimp [φ]; split_ifs <;> simp
  have hf_01 : ∀ i : Fin 2, ∀ y : Fin 2 → ℕ, (∀ j : Fin 2, y j ≤ 1) → f i y = 0 ∨ f i y = 1 := by
    intro i y hy
    fin_cases i
    · have h0 := hy 0; dsimp [f]; omega
    · have h1 := hy 1; dsimp [f]; omega
  have hf_dir : ∀ i : Fin 2,
      MonotoneOn (f i) {y : Fin 2 → ℕ | ∀ j : Fin 2, y j ≤ 1} ∨
        AntitoneOn (f i) {y : Fin 2 → ℕ | ∀ j : Fin 2, y j ≤ 1} := by
    intro i
    fin_cases i
    · exact Or.inl fun a _ b _ hab ↦ by simpa [f] using hab 0
    · exact Or.inr fun a _ b _ hab ↦ by dsimp [f]; exact Nat.sub_le_sub_left (hab 1) 1
  have h_res := h_all 2 2 f φ hφ_mono hφ_01 hf_01 hf_dir
  let y₀ : Fin 2 → ℕ := fun _ ↦ 0
  let y₁ : Fin 2 → ℕ := fun j ↦ if j = 0 then 1 else 0
  let y₂ : Fin 2 → ℕ := fun _ ↦ 1
  have hy₀ : y₀ ∈ {y : Fin 2 → ℕ | ∀ j : Fin 2, y j ≤ 1} := fun _ ↦ by simp [y₀]
  have hy₁ : y₁ ∈ {y : Fin 2 → ℕ | ∀ j : Fin 2, y j ≤ 1} := fun j ↦ by
    fin_cases j <;> simp [y₁]
  have hy₂ : y₂ ∈ {y : Fin 2 → ℕ | ∀ j : Fin 2, y j ≤ 1} := fun _ ↦ by simp [y₂]
  have h01 : y₀ ≤ y₁ := fun j ↦ by fin_cases j <;> simp [y₀, y₁]
  have h12 : y₁ ≤ y₂ := fun j ↦ by fin_cases j <;> simp [y₁, y₂]
  have hv₀ : φ (fun i ↦ f i y₀) = 0 := by simp [φ, f, y₀]
  have hv₁ : φ (fun i ↦ f i y₁) = 1 := by simp [φ, f, y₁]
  have hv₂ : φ (fun i ↦ f i y₂) = 0 := by simp [φ, f, y₂]
  rcases h_res with hmono | hanti
  · have h := hmono hy₁ hy₂ h12; linarith
  · have h := hanti hy₀ hy₁ h01; linarith

/-! ### Helpers for `thm4_17_implicit_coupling_corrected` -/

private lemma vecBoolToNat_injective {n : ℕ} :
    Function.Injective (vecBoolToNat (N := n)) := by
  intro a b h
  funext j
  have hj := congr_fun h j
  cases ha : a j <;> cases hb : b j <;> simp [vecBoolToNat, boolToNat, ha, hb] at hj ⊢

private lemma eq_vecBoolToNat_of_zero_or_one {n : ℕ} {v : Fin n → ℕ}
    (hv : ∀ j : Fin n, v j = 0 ∨ v j = 1) :
    v = vecBoolToNat (fun j ↦ decide (v j = 1)) := by
  funext j
  rcases hv j with h0 | h1
  · simp [vecBoolToNat, boolToNat, h0]
  · simp [vecBoolToNat, boolToNat, h1]

private lemma map_measureReal_eq_sum_vecBoolToNat {n : ℕ} {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (μ : Measure Ω₀) [IsProbabilityMeasure μ]
    {V : Ω₀ → Fin n → ℕ} (hV : Measurable V)
    (hV01 : ∀ᵐ ω ∂μ, ∀ j : Fin n, V ω j = 0 ∨ V ω j = 1)
    (s : Set (Fin n → ℕ)) :
    (μ.map V).real s =
      ∑ b : Fin n → Bool,
        if vecBoolToNat b ∈ s then μ.real {ω | V ω = vecBoolToNat b} else 0 := by
  have h_ae : (V ⁻¹' s).indicator (1 : Ω₀ → ℝ) =ᵐ[μ]
      fun ω ↦ ∑ b : Fin n → Bool,
        (if vecBoolToNat b ∈ s then (1 : ℝ) else 0) *
          {ω' | V ω' = vecBoolToNat b}.indicator (fun _ ↦ (1 : ℝ)) ω := by
    filter_upwards [hV01] with ω hω
    let b₀ : Fin n → Bool := fun j ↦ decide (V ω j = 1)
    have hb₀ : V ω = vecBoolToNat b₀ := eq_vecBoolToNat_of_zero_or_one hω
    rw [Finset.sum_eq_single b₀]
    · by_cases hmem : vecBoolToNat b₀ ∈ s
      · have hmem' : ω ∈ V ⁻¹' s := by simpa [hb₀] using hmem
        simp [hb₀, hmem, hmem']
      · have hmem' : ω ∉ V ⁻¹' s := by simpa [hb₀] using hmem
        simp [hb₀, hmem, hmem']
    · intro b _ hbne
      have hnot : ω ∉ {ω' | V ω' = vecBoolToNat b} := fun h_eq ↦
        hbne (vecBoolToNat_injective (h_eq.symm.trans hb₀))
      simp [Set.indicator_of_notMem hnot]
    · intro habs; exact False.elim (habs (Finset.mem_univ b₀))
  have h_meas_b : ∀ b : Fin n → Bool, MeasurableSet {ω' | V ω' = vecBoolToNat b} :=
    fun b ↦ hV (measurableSet_singleton _)
  rw [map_measureReal_apply hV .of_discrete, ← integral_indicator_one (hV .of_discrete),
    integral_congr_ae h_ae,
    integral_finsetSum Finset.univ fun b _ ↦
      ((integrable_const (1 : ℝ)).indicator (h_meas_b b)).const_mul _]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [integral_const_mul]
  change (if vecBoolToNat b ∈ s then (1 : ℝ) else 0) *
      (∫ ω, {ω' | V ω' = vecBoolToNat b}.indicator 1 ω ∂μ) = _
  rw [integral_indicator_one (h_meas_b b)]
  split_ifs <;> ring

private lemma measure_map_eq_of_forall_vecBoolToNat {n : ℕ}
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁]
    (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    {V₁ : Ω₁ → Fin n → ℕ} {V₂ : Ω₂ → Fin n → ℕ}
    (hV₁ : Measurable V₁) (hV₂ : Measurable V₂)
    (hV₁_01 : ∀ᵐ ω₁ ∂μ₁, ∀ j : Fin n, V₁ ω₁ j = 0 ∨ V₁ ω₁ j = 1)
    (hV₂_01 : ∀ᵐ ω₂ ∂μ₂, ∀ j : Fin n, V₂ ω₂ j = 0 ∨ V₂ ω₂ j = 1)
    (h_eq : ∀ b : Fin n → Bool,
      μ₁.real {ω₁ | V₁ ω₁ = vecBoolToNat b} = μ₂.real {ω₂ | V₂ ω₂ = vecBoolToNat b}) :
    μ₁.map V₁ = μ₂.map V₂ := by
  have : IsProbabilityMeasure (μ₁.map V₁) := isProbabilityMeasure_map' hV₁.aemeasurable
  have : IsProbabilityMeasure (μ₂.map V₂) := isProbabilityMeasure_map' hV₂.aemeasurable
  ext s _
  rw [← ofReal_measureReal (μ := μ₁.map V₁) (s := s),
    ← ofReal_measureReal (μ := μ₂.map V₂) (s := s),
    map_measureReal_eq_sum_vecBoolToNat μ₁ hV₁ hV₁_01 s,
    map_measureReal_eq_sum_vecBoolToNat μ₂ hV₂ hV₂_01 s]
  congr 1
  exact Finset.sum_congr rfl fun b _ ↦ by rw [h_eq b]

private lemma map_cond_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {V : α → β} (hV : Measurable V) {B : Set β} (hB : MeasurableSet B) :
    (ProbabilityTheory.cond μ (V ⁻¹' B)).map V = ProbabilityTheory.cond (μ.map V) B := by
  ext S hS
  rw [Measure.map_apply hV hS, ProbabilityTheory.cond_apply (hV hB) μ (V ⁻¹' S),
    ProbabilityTheory.cond_apply hB (μ.map V) S, Measure.map_apply hV hB,
    Measure.map_apply hV (hB.inter hS), Set.preimage_inter]

private lemma isSizeBias_of_identDistrib_left
    {Ω₁ Ω₂ Ω' : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω']
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P' : Measure Ω'}
    {U₁ : Ω₁ → ℝ} {U₂ : Ω₂ → ℝ} {Us : Ω' → ℝ}
    (hnn₁ : 0 ≤ᵐ[P₁] U₁)
    (hId : IdentDistrib U₁ U₂ P₁ P₂)
    (hSB : IsSizeBias P₂ U₂ P' Us) :
    IsSizeBias P₁ U₁ P' Us := by
  refine ⟨hnn₁, hId.integrable_iff.mpr hSB.2.1, hSB.2.2.1, fun g hg hInt₁ ↦ ?_⟩
  have hId_mul : IdentDistrib (fun ω ↦ U₁ ω * g (U₁ ω)) (fun ω ↦ U₂ ω * g (U₂ ω)) P₁ P₂ :=
    hId.comp (measurable_id.mul hg)
  rw [hId_mul.integral_eq, hId.integral_eq]
  exact hSB.2.2.2 g hg (hId_mul.integrable_iff.mp hInt₁)

private lemma sum_pi_prod_filter_coord {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (K : Fin n → α → ℝ) (hrow : ∀ i : Fin n, ∑ y : α, K i y = 1)
    (i₀ : Fin n) (y₀ : α) :
    (∑ ys : Fin n → α, if ys i₀ = y₀ then ∏ i : Fin n, K i (ys i) else 0) = K i₀ y₀ := by
  let g : Fin n → α → ℝ := fun i y ↦ if i = i₀ then (if y = y₀ then K i y else 0) else K i y
  have hterm : ∀ ys : Fin n → α,
      (if ys i₀ = y₀ then ∏ i : Fin n, K i (ys i) else 0) = ∏ i : Fin n, g i (ys i) := by
    intro ys
    by_cases hys : ys i₀ = y₀
    · simp only [hys, ↓reduceIte]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases hi : i = i₀
      · subst hi; simp [g, hys]
      · simp [g, hi]
    · simp only [hys, ↓reduceIte]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [g, hys])
  simp_rw [hterm]
  rw [← Fintype.prod_sum g]
  have hsum_g : ∀ i : Fin n, (∑ y : α, g i y) = if i = i₀ then K i₀ y₀ else 1 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; simp [g]
    · simp [g, hi, hrow i]
  simp_rw [hsum_g]
  simp

/-- Theorem 4.17 proof implicit coupling existence, corrected (`SteinIntro.tex:2392-2394`, echoing
`L2375-2376`; `docs/reviews/stmts-review-SWEEP-D.md` `D-D2`, `ISSUE-4.17`). -/
theorem thm4_17_implicit_coupling_corrected
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N n : ℕ} {Y : Fin N → Ω → ℕ} {f : Fin n → (Fin N → ℕ) → ℕ}
    {r : ℝ≥0}
    (hY_meas : ∀ j : Fin N, AEMeasurable (Y j) P)
    (hY_01 : ∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (hY_indep : ProbabilityTheory.iIndepFun Y P)
    (hf_01 : ∀ i : Fin n, ∀ y : Fin N → ℕ,
      (∀ j : Fin N, y j ≤ 1) → f i y = 0 ∨ f i y = 1)
    (hf_mono :
      (∀ i : Fin n, MonotoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) ∨
        (∀ i : Fin n, AntitoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1})) :
    let X : Fin n → Ω → ℕ := fun i ω ↦ f i (fun j ↦ Y j ω)
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ (i : Fin n) (φ : (Fin n → ℕ) → ℝ),
      Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
        0 ≤ ProbabilityTheory.covariance
          (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X j ω)) P) ∧
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ)
      (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ))
      (Ic : Ωc → Fin n),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, ∀ᵐ ωc ∂Pc, Xc i ωc = 0 ∨ Xc i ωc = 1) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      (∀ i : Fin n,
        0 < p i →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map
            (fun ωc (j : {j : Fin n // j ≠ i}) ↦ Xc j.1 ωc)) ∧
      Measurable Ic ∧
      (∀ i : Fin n, Pc.real (Ic ⁻¹' {i}) = p i / (r : ℝ)) ∧
      ProbabilityTheory.IndepFun Ic (fun ωc ↦ (fun i ↦ Xc i ωc, fun i ↦ Yc i ωc)) Pc ∧
      (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ωc ∂Pc, Xc j.1 ωc ≤ Yc i ωc j) ∧
      IsSizeBias P (fun ω ↦ (W ω : ℝ)) Pc
        (fun ωc ↦ ((∑ j : {j : Fin n // j ≠ Ic ωc}, Yc (Ic ωc) ωc j) + 1 : ℕ))) := by
  let X : Fin n → Ω → ℕ := fun i ω ↦ f i (fun j ↦ Y j ω)
  let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
  let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
  dsimp only
  intro hr hr_eq
  let cube : Set (Fin N → ℕ) := {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}
  -- Measurable version `Y'` and `X'`
  let Y' : Fin N → Ω → ℕ := fun j ↦ (hY_meas j).mk (Y j)
  have hY'_meas : ∀ j : Fin N, Measurable (Y' j) := fun j ↦ (hY_meas j).measurable_mk
  have hY'_ae_all : ∀ᵐ ω ∂P, (fun j ↦ Y j ω) = (fun j ↦ Y' j ω) := by
    filter_upwards [Filter.eventually_all.mpr fun j ↦ (hY_meas j).ae_eq_mk] with ω hω
    funext j; exact hω j
  let X' : Fin n → Ω → ℕ := fun i ω ↦ f i (fun j ↦ Y' j ω)
  have hX'_meas : ∀ i : Fin n, Measurable (X' i) := fun i ↦
    (Measurable.of_discrete (f := f i)).comp (measurable_pi_iff.mpr hY'_meas)
  have hX'_vec_meas : Measurable (fun ω i ↦ X' i ω) := measurable_pi_iff.mpr hX'_meas
  have hX_ae_X' : ∀ i : Fin n, X i =ᵐ[P] X' i := fun i ↦ by
    filter_upwards [hY'_ae_all] with ω hω
    simp [X, X', hω]
  have hX_vec_ae : (fun ω i ↦ X i ω) =ᵐ[P] (fun ω i ↦ X' i ω) := by
    filter_upwards [hY'_ae_all] with ω hω
    funext i; simp [X, X', hω]
  have hY'_cube : ∀ᵐ ω ∂P, (fun j ↦ Y' j ω) ∈ cube := by
    filter_upwards [Filter.eventually_all.mpr hY_01, hY'_ae_all] with ω h01 h_eq j
    dsimp only
    have hj : Y' j ω = 0 ∨ Y' j ω = 1 := by rw [← congr_fun h_eq j]; exact h01 j
    rcases hj with h | h <;> omega
  have hX'_01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X' i ω = 0 ∨ X' i ω = 1 := fun i ↦ by
    filter_upwards [hY'_cube] with ω hω
    exact hf_01 i _ hω
  have hX'_all01 : ∀ᵐ ω ∂P, ∀ i : Fin n, X' i ω = 0 ∨ X' i ω = 1 :=
    Filter.eventually_all.mpr hX'_01
  have hp'_eq : ∀ i : Fin n, P.real {ω | X' i ω = 1} = p i := fun i ↦ by
    refine measureReal_congr ?_
    filter_upwards [hX_ae_X' i] with ω hω
    simp [hω]
  -- Part 1: non-negative covariance with increasing indicators via FKG + `D-D3`
  have hcov : ∀ (i : Fin n) (φ : (Fin n → ℕ) → ℝ),
      Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
        0 ≤ ProbabilityTheory.covariance
          (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X j ω)) P := by
    intro i φ hφ_mono hφ_01
    have hXi'_meas : Measurable (fun ω ↦ (X' i ω : ℝ)) :=
      (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (hX'_meas i)
    have hφ'_meas : Measurable (fun ω ↦ φ (fun j ↦ X' j ω)) :=
      (Measurable.of_discrete (f := φ)).comp hX'_vec_meas
    have hXi_mem : MemLp (fun ω ↦ (X i ω : ℝ)) 2 P := by
      have h_mem' : MemLp (fun ω ↦ (X' i ω : ℝ)) 2 P := by
        refine (memLp_top_of_bound hXi'_meas.aestronglyMeasurable 1 ?_).mono_exponent le_top
        filter_upwards [hX'_01 i] with ω h01
        rcases h01 with h | h <;> simp [h]
      exact h_mem'.ae_eq ((hX_ae_X' i).symm.mono fun ω hω ↦ by simp [hω])
    have hφ_mem : MemLp (fun ω ↦ φ (fun j ↦ X j ω)) 2 P := by
      have h_mem' : MemLp (fun ω ↦ φ (fun j ↦ X' j ω)) 2 P := by
        refine (memLp_top_of_bound hφ'_meas.aestronglyMeasurable 1
          (Filter.Eventually.of_forall fun ω ↦ ?_)).mono_exponent le_top
        rcases hφ_01 (fun j ↦ X' j ω) with h | h <;> simp [h]
      exact h_mem'.ae_eq (hX_vec_ae.symm.mono fun ω hω ↦ by simp [hω])
    rw [covariance_eq_sub hXi_mem hφ_mem]
    let g_fn : (Fin N → ℕ) → ℝ := fun y ↦ (f i y : ℝ)
    let h_fn : (Fin N → ℕ) → ℝ := fun y ↦ φ (fun k ↦ f k y)
    have hcomp := thm4_17_comp_monotone_corrected (f := f) hφ_mono
    have hfkg := fkg_independent_indicators_on P hY_meas hY_01 hY_indep (g := g_fn) (h := h_fn) ?_
    · change 0 ≤ ∫ ω, g_fn (fun j ↦ Y j ω) * h_fn (fun j ↦ Y j ω) ∂P -
        (∫ ω, g_fn (fun j ↦ Y j ω) ∂P) * ∫ ω, h_fn (fun j ↦ Y j ω) ∂P
      linarith
    · rcases hf_mono with h_inc | h_dec
      · exact Or.inl ⟨fun a ha b hb hab ↦ Nat.cast_le.mpr (h_inc i ha hb hab), hcomp.1 h_inc⟩
      · exact Or.inr ⟨fun a ha b hb hab ↦ Nat.cast_le.mpr (h_dec i ha hb hab), hcomp.2 h_dec⟩
  refine ⟨hcov, ?_⟩
  -- Part 2: build monotone transition kernels via Lemma 4.18 (`lem4_18_cond`)
  let q₀ : (Fin n → Bool) → ℝ :=
    fun x ↦ P.real {ω | (fun j ↦ X' j ω) = vecBoolToNat x}
  have hq₀_nn : ∀ x : Fin n → Bool, 0 ≤ q₀ x := fun _ ↦ measureReal_nonneg
  have hq₀_sum : ∑ x : Fin n → Bool, q₀ x = 1 := by
    have h := map_measureReal_eq_sum_vecBoolToNat P hX'_vec_meas hX'_all01 Set.univ
    simpa [q₀, map_measureReal_apply hX'_vec_meas MeasurableSet.univ] using h.symm
  have hex_K : ∀ i : Fin n, ∃ Ki : (Fin n → Bool) → (Fin n → Bool) → ℝ,
      (∀ x y, 0 ≤ Ki x y) ∧
      (∀ x y, Ki x y ≠ 0 → x ≤ y) ∧
      (∀ x, ∑ y : Fin n → Bool, Ki x y = 1) ∧
      (0 < p i → ∀ y : Fin n → Bool,
        (∑ x : Fin n → Bool, q₀ x * Ki x y) =
          (ProbabilityTheory.cond P {ω | X' i ω = 1}).real
            {ω | (fun j ↦ X' j ω) = vecBoolToNat y}) := by
    intro i
    by_cases hpi : 0 < p i
    · have hpi' : 0 < P.real {ω | X' i ω = 1} := (hp'_eq i).symm ▸ hpi
      have hAi_ne : P {ω | X' i ω = 1} ≠ 0 := fun h0 ↦ by
        simp [Measure.real, h0] at hpi'
      let P_i : Measure Ω := ProbabilityTheory.cond P {ω | X' i ω = 1}
      have : IsProbabilityMeasure P_i := ProbabilityTheory.cond_isProbabilityMeasure hAi_ne
      have hc3' : ∀ φ : (Fin n → ℕ) → ℝ,
          Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
            0 ≤ ProbabilityTheory.covariance
              (fun ω ↦ (X' i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X' j ω)) P := by
        intro φ hφ_mono hφ_01
        have h_ae1 : (fun ω ↦ (X i ω : ℝ)) =ᵐ[P] fun ω ↦ (X' i ω : ℝ) :=
          (hX_ae_X' i).mono fun ω hω ↦ by simp [hω]
        have h_ae2 : (fun ω ↦ φ (fun j ↦ X j ω)) =ᵐ[P] fun ω ↦ φ (fun j ↦ X' j ω) :=
          hX_vec_ae.mono fun ω hω ↦ by simp [hω]
        have hcov_eq : ProbabilityTheory.covariance
            (fun ω ↦ (X' i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X' j ω)) P =
            ProbabilityTheory.covariance
              (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X j ω)) P := by
          unfold ProbabilityTheory.covariance
          have hm1 : ∫ x, (X' i x : ℝ) ∂P = ∫ x, (X i x : ℝ) ∂P :=
            integral_congr_ae h_ae1.symm
          have hm2 : ∫ y, φ (fun j ↦ X' j y) ∂P = ∫ y, φ (fun j ↦ X j y) ∂P :=
            integral_congr_ae h_ae2.symm
          refine integral_congr_ae ?_
          filter_upwards [h_ae1, h_ae2] with ω h1 h2
          rw [hm1, hm2, h1, h2]
        rw [hcov_eq]
        exact hcov i φ hφ_mono hφ_01
      have hlem := lem4_18_cond P P_i i hX'_meas hX'_01 hX'_meas hpi' rfl
      obtain ⟨Ω_i, m_i, P_ci, hP_ci, X_ci, X_ci_cond, hX_ci, hX_ci_cond, hmap1, hmap2, hle⟩ :=
        hlem.1.mpr (hlem.2.mpr hc3')
      have hX_ci_01 : ∀ᵐ ω ∂P_ci, ∀ j : Fin n, X_ci ω j = 0 ∨ X_ci ω j = 1 := by
        let S01 : Set (Fin n → ℕ) := {v | ∀ j : Fin n, v j = 0 ∨ v j = 1}
        change P_ci (X_ci ⁻¹' S01ᶜ) = 0
        rw [← Measure.map_apply hX_ci .of_discrete, hmap1,
          Measure.map_apply hX'_vec_meas .of_discrete]
        exact hX'_all01
      have hX_ci_cond_01 : ∀ᵐ ω ∂P_ci, ∀ j : Fin n, X_ci_cond ω j = 0 ∨ X_ci_cond ω j = 1 := by
        let S01 : Set (Fin n → ℕ) := {v | ∀ j : Fin n, v j = 0 ∨ v j = 1}
        change P_ci (X_ci_cond ⁻¹' S01ᶜ) = 0
        rw [← Measure.map_apply hX_ci_cond .of_discrete, hmap2,
          Measure.map_apply hX'_vec_meas .of_discrete]
        exact ProbabilityTheory.cond_absolutelyContinuous hX'_all01
      let w : (Fin n → Bool) → (Fin n → Bool) → ℝ := fun x y ↦
        P_ci.real {ω | X_ci ω = vecBoolToNat x ∧ X_ci_cond ω = vecBoolToNat y}
      have hw_nn : ∀ x y, 0 ≤ w x y := fun _ _ ↦ measureReal_nonneg
      have hw_mono : ∀ x y, w x y ≠ 0 → x ≤ y := by
        intro x y hw_ne j
        by_contra hnot
        have hx1 : x j = true := by cases hx : x j <;> cases hy : y j <;> simp_all
        have hy0 : y j = false := by cases hx : x j <;> cases hy : y j <;> simp_all
        have hsub : {ω | X_ci ω = vecBoolToNat x ∧ X_ci_cond ω = vecBoolToNat y} ⊆
            {ω | ¬ (X_ci ω j ≤ X_ci_cond ω j)} := by
          rintro ω ⟨h1, h2⟩
          change ¬ (X_ci ω j ≤ X_ci_cond ω j)
          rw [h1, h2]
          simp [vecBoolToNat, boolToNat, hx1, hy0]
        have h0 : P_ci {ω | X_ci ω = vecBoolToNat x ∧ X_ci_cond ω = vecBoolToNat y} = 0 :=
          measure_mono_null hsub (hle j)
        exact hw_ne (by simp [w, Measure.real, h0])
      have hw_row : ∀ x : Fin n → Bool, (∑ y : Fin n → Bool, w x y) = q₀ x := by
        intro x
        have h_ae : {ω | X_ci ω = vecBoolToNat x}.indicator (1 : Ω_i → ℝ) =ᵐ[P_ci]
            fun ω ↦ ∑ y : Fin n → Bool,
              {ω' | X_ci ω' = vecBoolToNat x ∧ X_ci_cond ω' = vecBoolToNat y}.indicator
                (fun _ ↦ (1 : ℝ)) ω := by
          filter_upwards [hX_ci_cond_01] with ω hω
          let y₀ : Fin n → Bool := fun j ↦ decide (X_ci_cond ω j = 1)
          have hy₀ : X_ci_cond ω = vecBoolToNat y₀ := eq_vecBoolToNat_of_zero_or_one hω
          rw [Finset.sum_eq_single y₀]
          · by_cases hx : X_ci ω = vecBoolToNat x <;> simp [hx, hy₀]
          · intro y _ hyne
            have hnot : ω ∉ {ω' | X_ci ω' = vecBoolToNat x ∧ X_ci_cond ω' = vecBoolToNat y} :=
              fun h ↦ hyne (vecBoolToNat_injective (h.2.symm.trans hy₀))
            simp [Set.indicator_of_notMem hnot]
          · intro habs; exact False.elim (habs (Finset.mem_univ y₀))
        have hm1 : MeasurableSet {ω | X_ci ω = vecBoolToNat x} :=
          hX_ci (measurableSet_singleton _)
        have hm2 : ∀ y : Fin n → Bool,
            MeasurableSet {ω | X_ci ω = vecBoolToNat x ∧ X_ci_cond ω = vecBoolToNat y} :=
          fun y ↦ hm1.inter (hX_ci_cond (measurableSet_singleton _))
        have hint := integral_congr_ae h_ae
        rw [integral_indicator_one hm1,
          integral_finsetSum Finset.univ fun y _ ↦ (integrable_const (1 : ℝ)).indicator (hm2 y)]
          at hint
        have hlhs : P_ci.real {ω | X_ci ω = vecBoolToNat x} = q₀ x := by
          have h1 := congr_arg (fun μ : Measure (Fin n → ℕ) ↦ μ.real {vecBoolToNat x}) hmap1
          dsimp only [q₀]
          rw [map_measureReal_apply hX_ci (measurableSet_singleton _),
            map_measureReal_apply hX'_vec_meas (measurableSet_singleton _)] at h1
          exact h1
        rw [← hlhs, hint]
        refine (Finset.sum_congr rfl fun y _ ↦ ?_).symm
        exact integral_indicator_one (hm2 y)
      have hw_col : ∀ y : Fin n → Bool,
          (∑ x : Fin n → Bool, w x y) = P_i.real {ω | (fun j ↦ X' j ω) = vecBoolToNat y} := by
        intro y
        have h_ae : {ω | X_ci_cond ω = vecBoolToNat y}.indicator (1 : Ω_i → ℝ) =ᵐ[P_ci]
            fun ω ↦ ∑ x : Fin n → Bool,
              {ω' | X_ci ω' = vecBoolToNat x ∧ X_ci_cond ω' = vecBoolToNat y}.indicator
                (fun _ ↦ (1 : ℝ)) ω := by
          filter_upwards [hX_ci_01] with ω hω
          let x₀ : Fin n → Bool := fun j ↦ decide (X_ci ω j = 1)
          have hx₀ : X_ci ω = vecBoolToNat x₀ := eq_vecBoolToNat_of_zero_or_one hω
          rw [Finset.sum_eq_single x₀]
          · by_cases hy : X_ci_cond ω = vecBoolToNat y <;> simp [hx₀, hy]
          · intro x _ hxne
            have hnot : ω ∉ {ω' | X_ci ω' = vecBoolToNat x ∧ X_ci_cond ω' = vecBoolToNat y} :=
              fun h ↦ hxne (vecBoolToNat_injective (h.1.symm.trans hx₀))
            simp [Set.indicator_of_notMem hnot]
          · intro habs; exact False.elim (habs (Finset.mem_univ x₀))
        have hm1 : MeasurableSet {ω | X_ci_cond ω = vecBoolToNat y} :=
          hX_ci_cond (measurableSet_singleton _)
        have hm2 : ∀ x : Fin n → Bool,
            MeasurableSet {ω | X_ci ω = vecBoolToNat x ∧ X_ci_cond ω = vecBoolToNat y} :=
          fun x ↦ (hX_ci (measurableSet_singleton _)).inter hm1
        have hint := integral_congr_ae h_ae
        rw [integral_indicator_one hm1,
          integral_finsetSum Finset.univ fun x _ ↦ (integrable_const (1 : ℝ)).indicator (hm2 x)]
          at hint
        have hlhs : P_ci.real {ω | X_ci_cond ω = vecBoolToNat y} =
            P_i.real {ω | (fun j ↦ X' j ω) = vecBoolToNat y} := by
          have h1 := congr_arg (fun μ : Measure (Fin n → ℕ) ↦ μ.real {vecBoolToNat y}) hmap2
          rw [map_measureReal_apply hX_ci_cond (measurableSet_singleton _),
            map_measureReal_apply hX'_vec_meas (measurableSet_singleton _)] at h1
          exact h1
        rw [← hlhs, hint]
        refine (Finset.sum_congr rfl fun x _ ↦ ?_).symm
        exact integral_indicator_one (hm2 x)
      let Ki : (Fin n → Bool) → (Fin n → Bool) → ℝ := fun x y ↦
        if 0 < q₀ x then w x y / q₀ x else (if y = x then 1 else 0)
      refine ⟨Ki, ?_, ?_, ?_, ?_⟩
      · intro x y
        dsimp [Ki]
        split_ifs with hqx hyx
        · exact div_nonneg (hw_nn x y) hqx.le
        · norm_num
        · norm_num
      · intro x y hne
        dsimp [Ki] at hne
        split_ifs at hne with hqx hyx
        · exact hw_mono x y fun hw0 ↦ hne (by simp [hw0])
        · exact hyx.symm.le
        · exact False.elim (hne rfl)
      · intro x
        by_cases hqx : 0 < q₀ x
        · simp only [Ki, hqx, ↓reduceIte, ← Finset.sum_div, hw_row x, div_self hqx.ne']
        · simp [Ki, hqx]
      · intro _ y
        rw [← hw_col y]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        by_cases hqx : 0 < q₀ x
        · simp only [Ki, hqx, ↓reduceIte]
          exact mul_div_cancel₀ _ hqx.ne'
        · have hqx0 : q₀ x = 0 := le_antisymm (le_of_not_gt hqx) (hq₀_nn x)
          have hwy_le : w x y ≤ q₀ x := by
            rw [← hw_row x]
            exact Finset.single_le_sum (fun y' _ ↦ hw_nn x y') (Finset.mem_univ y)
          have hwy0 : w x y = 0 := le_antisymm (hwy_le.trans_eq hqx0) (hw_nn x y)
          rw [hqx0, zero_mul, hwy0]
    · refine ⟨fun x y ↦ if y = x then 1 else 0,
        fun x y ↦ by dsimp only; split_ifs <;> norm_num,
        fun x y hne ↦ by
          dsimp only at hne
          split_ifs at hne with h
          · exact h.symm.le
          · exact False.elim (hne rfl),
        fun x ↦ by simp,
        fun hp_pos ↦ False.elim (hpi hp_pos)⟩
  choose K hK_nn hK_mono hK_row hK_col using hex_K
  -- Build finite product coupling space `Ωc := State × Fin n`
  let State := (Fin n → Bool) × (Fin n → Fin n → Bool)
  let pmfS : State → ℝ := fun s ↦ q₀ s.1 * ∏ i : Fin n, K i s.1 (s.2 i)
  have hpmfS_nn : ∀ s : State, 0 ≤ pmfS s := fun s ↦
    mul_nonneg (hq₀_nn s.1) (Finset.prod_nonneg fun i _ ↦ hK_nn i s.1 (s.2 i))
  have hpmfS_fst : ∀ x : Fin n → Bool, (∑ ys : Fin n → Fin n → Bool, pmfS (x, ys)) = q₀ x := by
    intro x
    dsimp [pmfS]
    rw [← Finset.mul_sum, ← Fintype.prod_sum (fun i y ↦ K i x y)]
    simp [hK_row]
  have hpmfS_sum : ∑ s : State, pmfS s = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hpmfS_fst]
    exact hq₀_sum
  let μS : Measure State := ∑ s : State, ENNReal.ofReal (pmfS s) • Measure.dirac s
  have hμS_prob : IsProbabilityMeasure μS := by
    constructor
    simp only [μS, Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ ↦ hpmfS_nn s), hpmfS_sum, ENNReal.ofReal_one]
  have hμS_real : ∀ A : Set State, μS.real A = ∑ s : State, if s ∈ A then pmfS s else 0 := by
    intro A
    have h_app : μS A = ENNReal.ofReal (∑ s : State, if s ∈ A then pmfS s else 0) := by
      simp only [μS, Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
        Measure.dirac_apply' _ MeasurableSet.of_discrete, Set.indicator_apply, Pi.one_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun s _ ↦ by split_ifs <;> simp
      · intro s _; split_ifs <;> simp [hpmfS_nn s]
    rw [Measure.real, h_app, ENNReal.toReal_ofReal]
    exact Finset.sum_nonneg fun s _ ↦ by split_ifs <;> simp [hpmfS_nn s]
  have hr_pos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hp_nn : ∀ i : Fin n, 0 ≤ p i := fun _ ↦ measureReal_nonneg
  let μI : Measure (Fin n) := ∑ i : Fin n, ENNReal.ofReal (p i / (r : ℝ)) • Measure.dirac i
  have hμI_prob : IsProbabilityMeasure μI := by
    constructor
    simp only [μI, Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    have hsum1 : (∑ i : Fin n, p i / (r : ℝ)) = 1 := by
      rw [← Finset.sum_div, ← hr_eq, div_self hr_pos.ne']
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (hp_nn i) hr_pos.le),
      hsum1, ENNReal.ofReal_one]
  have hμI_real_singleton : ∀ i : Fin n, μI.real {i} = p i / (r : ℝ) := by
    intro i
    have h_app : μI {i} = ENNReal.ofReal (p i / (r : ℝ)) := by
      simp only [μI, Measure.coe_finsetSum, Measure.smul_apply, Finset.sum_apply,
        Measure.dirac_apply' _ (measurableSet_singleton i), Set.indicator_apply,
        Set.mem_singleton_iff, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ i]
      simp
    rw [Measure.real, h_app, ENNReal.toReal_ofReal (div_nonneg (hp_nn i) hr_pos.le)]
  let Ωc : Type := State × Fin n
  let Pc : Measure Ωc := μS.prod μI
  have hPc_prob : IsProbabilityMeasure Pc := inferInstance
  let Xc : Fin n → Ωc → ℕ := fun i ωc ↦ vecBoolToNat ωc.1.1 i
  let Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ) :=
    fun i ωc j ↦ vecBoolToNat (ωc.1.2 i) j.1
  let Ic : Ωc → Fin n := Prod.snd
  have hXc_meas : ∀ i : Fin n, Measurable (Xc i) := fun _ ↦ Measurable.of_discrete
  have hYc_meas : ∀ i : Fin n, Measurable (Yc i) := fun _ ↦ Measurable.of_discrete
  have hIc_meas : Measurable Ic := measurable_snd
  have hXc_vec_meas : Measurable (fun ωc i ↦ Xc i ωc) := measurable_pi_iff.mpr hXc_meas
  have hXc_01 : ∀ i : Fin n, ∀ᵐ ωc ∂Pc, Xc i ωc = 0 ∨ Xc i ωc = 1 := fun i ↦
    Filter.Eventually.of_forall fun ωc ↦ by
      cases ωc.1.1 i <;> simp [Xc, vecBoolToNat, boolToNat]
  have hXc_all01 : ∀ᵐ ωc ∂Pc, ∀ i : Fin n, Xc i ωc = 0 ∨ Xc i ωc = 1 :=
    Filter.eventually_all.mpr hXc_01
  have hPc_fst : ∀ A : Set State, Pc.real (Prod.fst ⁻¹' A) = μS.real A := by
    intro A
    have hpre : (Prod.fst ⁻¹' A : Set Ωc) = A ×ˢ Set.univ := by
      ext ωc; exact ⟨fun h ↦ ⟨h, trivial⟩, fun h ↦ h.1⟩
    rw [hpre, Measure.real, Measure.prod_prod, measure_univ, mul_one, ← Measure.real]
  -- Marginal `Pc.map Xc = P.map X`
  have hmap_Xc_X' : Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X' i ω) := by
    refine measure_map_eq_of_forall_vecBoolToNat Pc P hXc_vec_meas hX'_vec_meas
      hXc_all01 hX'_all01 fun b ↦ ?_
    have hpre : {ωc : Ωc | (fun i ↦ Xc i ωc) = vecBoolToNat b} =
        Prod.fst ⁻¹' {s : State | s.1 = b} := by
      ext ωc
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Xc]
      exact ⟨fun h ↦ vecBoolToNat_injective h, fun h ↦ by rw [h]⟩
    rw [hpre, hPc_fst, hμS_real, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · simpa using hpmfS_fst b
    · intro x _ hxb
      exact Finset.sum_eq_zero fun ys _ ↦ by simp [hxb]
    · intro habs; exact False.elim (habs (Finset.mem_univ b))
  have hmap_Xc : Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) :=
    hmap_Xc_X'.trans (Measure.map_congr hX_vec_ae.symm)
  -- Conditional marginal `Pc.map (Yc i) = (cond Pc {Xc i = 1}).map ...`
  have hYc_law : ∀ i : Fin n,
      0 < p i →
      Pc.map (Yc i) =
        (ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map
          (fun ωc (j : {j : Fin n // j ≠ i}) ↦ Xc j.1 ωc) := by
    intro i hpi
    let Yc_full : Ωc → Fin n → ℕ := fun ωc ↦ vecBoolToNat (ωc.1.2 i)
    have hYc_full_meas : Measurable Yc_full := Measurable.of_discrete
    have hYc_full_01 : ∀ᵐ ωc ∂Pc, ∀ j : Fin n, Yc_full ωc j = 0 ∨ Yc_full ωc j = 1 :=
      Filter.Eventually.of_forall fun ωc j ↦ by
        cases ωc.1.2 i j <;> simp [Yc_full, vecBoolToNat, boolToNat]
    let P_i : Measure Ω := ProbabilityTheory.cond P {ω | X' i ω = 1}
    have hpi' : 0 < P.real {ω | X' i ω = 1} := (hp'_eq i).symm ▸ hpi
    have hAi_ne : P {ω | X' i ω = 1} ≠ 0 := fun h0 ↦ by simp [Measure.real, h0] at hpi'
    have : IsProbabilityMeasure P_i := ProbabilityTheory.cond_isProbabilityMeasure hAi_ne
    have hP_i_01 : ∀ᵐ ω ∂P_i, ∀ j : Fin n, X' j ω = 0 ∨ X' j ω = 1 :=
      ProbabilityTheory.cond_absolutelyContinuous hX'_all01
    have hmap_full : Pc.map Yc_full = P_i.map (fun ω j ↦ X' j ω) := by
      refine measure_map_eq_of_forall_vecBoolToNat Pc P_i hYc_full_meas hX'_vec_meas
        hYc_full_01 hP_i_01 fun b ↦ ?_
      have hpre : {ωc : Ωc | Yc_full ωc = vecBoolToNat b} =
          Prod.fst ⁻¹' {s : State | s.2 i = b} := by
        ext ωc
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Yc_full]
        exact ⟨fun h ↦ vecBoolToNat_injective h, fun h ↦ by rw [h]⟩
      rw [hpre, hPc_fst, hμS_real, Fintype.sum_prod_type]
      have hinner : ∀ x : Fin n → Bool,
          (∑ ys : Fin n → Fin n → Bool, if ys i = b then pmfS (x, ys) else 0) =
            q₀ x * K i x b := by
        intro x
        dsimp [pmfS]
        have hmul : ∀ ys : Fin n → Fin n → Bool,
            (if ys i = b then q₀ x * ∏ k : Fin n, K k x (ys k) else 0) =
              q₀ x * (if ys i = b then ∏ k : Fin n, K k x (ys k) else 0) :=
          fun ys ↦ by split_ifs <;> ring
        simp_rw [hmul, ← Finset.mul_sum]
        rw [sum_pi_prod_filter_coord (fun k y ↦ K k x y) (fun k ↦ hK_row k x) i b]
      have hmem : ∀ (x : Fin n → Bool) (ys : Fin n → Fin n → Bool),
          ((x, ys) ∈ {s : State | s.2 i = b}) ↔ ys i = b := fun _ _ ↦ Iff.rfl
      simp_rw [hmem, hinner]
      exact hK_col i hpi b
    have hcond_eq : P_i.map (fun ω j ↦ X' j ω) =
        (ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map (fun ωc j ↦ Xc j ωc) := by
      let B : Set (Fin n → ℕ) := {v | v i = 1}
      have hB : MeasurableSet B := .of_discrete
      have h1 : P_i.map (fun ω j ↦ X' j ω) =
          ProbabilityTheory.cond (P.map (fun ω j ↦ X' j ω)) B :=
        map_cond_preimage P hX'_vec_meas hB
      have h2 : (ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map (fun ωc j ↦ Xc j ωc) =
          ProbabilityTheory.cond (Pc.map (fun ωc j ↦ Xc j ωc)) B :=
        map_cond_preimage Pc hXc_vec_meas hB
      rw [h1, h2, hmap_Xc_X']
    let res : (Fin n → ℕ) → ({j : Fin n // j ≠ i} → ℕ) := fun v j ↦ v j.1
    have hres_meas : Measurable res := Measurable.of_discrete
    calc Pc.map (Yc i)
      _ = (Pc.map Yc_full).map res := (Measure.map_map hres_meas hYc_full_meas).symm
      _ = ((ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map (fun ωc j ↦ Xc j ωc)).map res := by
        rw [hmap_full, hcond_eq]
      _ = (ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map
            (fun ωc (j : {j : Fin n // j ≠ i}) ↦ Xc j.1 ωc) :=
        Measure.map_map hres_meas hXc_vec_meas
  -- Index probabilities & independence
  have hIc_prob : ∀ i : Fin n, Pc.real (Ic ⁻¹' {i}) = p i / (r : ℝ) := by
    intro i
    have hpre : (Ic ⁻¹' {i} : Set Ωc) = Set.univ ×ˢ {i} := by
      ext ωc; exact ⟨fun h ↦ ⟨trivial, h⟩, fun h ↦ h.2⟩
    rw [hpre, Measure.real, Measure.prod_prod, measure_univ, one_mul, ← Measure.real,
      hμI_real_singleton i]
  have hIc_indep :
      ProbabilityTheory.IndepFun Ic (fun ωc ↦ (fun i ↦ Xc i ωc, fun i ↦ Yc i ωc)) Pc := by
    let G : State → (Fin n → ℕ) × ((i : Fin n) → {j : Fin n // j ≠ i} → ℕ) :=
      fun s ↦ (fun i ↦ vecBoolToNat s.1 i, fun i j ↦ vecBoolToNat (s.2 i) j.1)
    have hG_meas : Measurable G := Measurable.of_discrete
    exact (ProbabilityTheory.indepFun_prod hG_meas measurable_id).symm
  -- Almost-sure coordinatewise monotonicity `Xc j.1 ≤ Yc i j`
  have hmono_ae : ∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ωc ∂Pc, Xc j.1 ωc ≤ Yc i ωc j := by
    intro i j
    let BadS : Set State := {s : State | ¬ (s.1 ≤ s.2 i)}
    have hμS_bad_real : μS.real BadS = 0 := by
      rw [hμS_real]
      refine Finset.sum_eq_zero fun s _ ↦ ?_
      split_ifs with hs
      · have hK0 : K i s.1 (s.2 i) = 0 := by
          by_contra hne
          exact hs (hK_mono i s.1 (s.2 i) hne)
        dsimp [pmfS]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hK0, mul_zero]
      · rfl
    have hμS_bad : μS BadS = 0 := (measureReal_eq_zero_iff).mp hμS_bad_real
    have hPc_bad : Pc (BadS ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hμS_bad, zero_mul]
    refine (measure_eq_zero_iff_ae_notMem.mp hPc_bad).mono fun ωc hωc ↦ ?_
    have hle : ωc.1.1 ≤ ωc.1.2 i := by
      by_contra hnot
      exact hωc ⟨hnot, trivial⟩
    exact monotone_vecBoolToNat hle j.1
  -- `IsSizeBias` via `sizeBias_sum_of_nat_zero_one_fintype` + `IdentDistrib`
  have hpc_eq : ∀ i : Fin n, Pc.real {ωc | Xc i ωc = 1} = p i := by
    intro i
    have h1 := congr_arg (fun μ : Measure (Fin n → ℕ) ↦ μ.real {v | v i = 1}) hmap_Xc_X'
    simpa [hp'_eq i, map_measureReal_apply hXc_vec_meas .of_discrete,
      map_measureReal_apply hX'_vec_meas .of_discrete] using h1
  have hlam_c : 0 < ∑ i : Fin n, Pc.real {ωc | Xc i ωc = 1} := by
    simp_rw [hpc_eq]
    dsimp only [p, X]
    rw [← hr_eq]
    exact hr_pos
  have hYc_law_c : ∀ i : Fin n,
      0 < Pc.real {ωc | Xc i ωc = 1} →
      Pc.map (Yc i) =
        (ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map
          (fun ωc (j : {j : Fin n // j ≠ i}) ↦ Xc j.1 ωc) :=
    fun i hi ↦ hYc_law i ((hpc_eq i) ▸ hi)
  have hIc_prob_c : ∀ i : Fin n,
      Pc.real (Ic ⁻¹' {i}) =
        Pc.real {ωc | Xc i ωc = 1} / ∑ k : Fin n, Pc.real {ωc | Xc k ωc = 1} := by
    intro i
    simp_rw [hpc_eq]
    dsimp only [p, X]
    rw [← hr_eq]
    exact hIc_prob i
  have hSB_c : IsSizeBias Pc (fun ωc ↦ ((∑ i : Fin n, Xc i ωc : ℕ) : ℝ)) Pc
      (fun ωc ↦ (((∑ j : {j : Fin n // j ≠ Ic ωc}, Yc (Ic ωc) ωc j) + 1 : ℕ) : ℝ)) :=
    sizeBias_sum_of_nat_zero_one_fintype Pc hXc_meas hXc_01 hlam_c
      (fun i ↦ (hYc_meas i).aemeasurable) hYc_law_c hIc_meas hIc_prob_c hIc_indep
  have hW_id : IdentDistrib (fun ω ↦ (W ω : ℝ)) (fun ωc ↦ ((∑ i : Fin n, Xc i ωc : ℕ) : ℝ))
      P Pc := by
    let sumR : (Fin n → ℕ) → ℝ := fun v ↦ ((∑ i : Fin n, v i : ℕ) : ℝ)
    have hsumR : Measurable sumR := Measurable.of_discrete
    have hX_vec_aem : AEMeasurable (fun ω i ↦ X i ω) P :=
      hX'_vec_meas.aemeasurable.congr hX_vec_ae.symm
    have hId_vec : IdentDistrib (fun ω i ↦ X i ω) (fun ωc i ↦ Xc i ωc) P Pc :=
      ⟨hX_vec_aem, hXc_vec_meas.aemeasurable, hmap_Xc.symm⟩
    exact hId_vec.comp hsumR
  have hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) Pc
      (fun ωc ↦ (((∑ j : {j : Fin n // j ≠ Ic ωc}, Yc (Ic ωc) ωc j) + 1 : ℕ) : ℝ)) :=
    isSizeBias_of_identDistrib_left
      (Filter.Eventually.of_forall fun _ ↦ Nat.cast_nonneg _) hW_id hSB_c
  exact ⟨Ωc, inferInstance, Pc, hPc_prob, Xc, Yc, Ic, hXc_meas, hXc_01, hmap_Xc, hYc_meas,
    hYc_law, hIc_meas, hIc_prob, hIc_indep, hmono_ae, hSB⟩

/-- PascalCase alias for `not_thm4_17_comp_monotone_printed` (`ISSUE-4.17`). -/
alias not_Thm4_17_comp_monotone_printed := not_thm4_17_comp_monotone_printed

end SteinMethod
