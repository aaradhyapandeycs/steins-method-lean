/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Couplings
import Formalization.Defs.PoissonSizeBias
import Formalization.PoissonSizeBias.Core.Basic

/-!
# Exchangeable Indicator Couplings (`Formalization.PoissonSizeBias.Core.Exchangeable`)

Proves the remaining general coupling results in Section 4.3 (`SteinIntro.tex:2148-2172`) together
with non-vacuity sanity witnesses for `SteinMethod.IsExchangeableTuple`:
- `isExchangeableTuple_const`, `isExchangeableTuple_fin_two_iff`, and
  `IsExchangeableTuple.identDistrib_apply` (sanity witnesses for `IsExchangeableTuple`).
- **Corollary 4.12** (`\label{cor122}`, `SteinIntro.tex:2148-2154`; `ISSUE-TYPO-4.12`):
  `sizeBias_sum_of_exchangeable_zero_one_fintype` and `sizeBias_sum_of_exchangeable_zero_one_fin`.
- **Example 4.4** (*Law of small numbers*, `SteinIntro.tex:2162-2172`):
  `lawOfSmallNumbers_sizeBias_and_tvDist`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Non-vacuity and basic properties of `IsExchangeableTuple` -/

/-- Non-vacuity witness: a constant family `(fun _ ω ↦ Z ω)` of a.e.-measurable random variables is
exchangeable under any measure `P`. -/
theorem isExchangeableTuple_const
    {Ω ι α : Type*} [Countable ι] [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) {Z : Ω → α} (hZ : AEMeasurable Z P) :
    IsExchangeableTuple P (fun _ : ι ↦ Z) := by
  intro _
  exact IdentDistrib.refl (AEMeasurable.of_eval fun _ ↦ hZ)

/-- Equivalence between `IsExchangeableTuple` on `Fin 2` and `IsExchangeablePair`
(`Formalization/Defs/Couplings.lean`). -/
theorem isExchangeableTuple_fin_two_iff
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (W W' : Ω → α) :
    IsExchangeableTuple P ![W, W'] ↔ IsExchangeablePair P W W' := by
  let toPair : (Fin 2 → α) → α × α := fun u ↦ (u 0, u 1)
  let ofPair : α × α → (Fin 2 → α) := fun p ↦ ![p.1, p.2]
  have htoPair : Measurable toPair :=
    (measurable_pi_apply (0 : Fin 2)).prodMk (measurable_pi_apply (1 : Fin 2))
  have hofPair : Measurable ofPair := by
    refine Measurable.of_eval fun i ↦ ?_
    fin_cases i
    · exact measurable_fst
    · exact measurable_snd
  constructor
  · intro hexch
    have hswap := (hexch (Equiv.swap (0 : Fin 2) 1)).comp htoPair
    simpa [IsExchangeablePair, toPair, Function.comp_def] using hswap.symm
  · intro hpair σ
    have hW_aem : AEMeasurable (fun ω i ↦ (![W, W'] : Fin 2 → Ω → α) i ω) P := by
      have h := hpair.aemeasurable_fst
      refine AEMeasurable.of_eval fun i ↦ ?_
      fin_cases i
      · exact h.fst
      · exact h.snd
    by_cases h0 : σ 0 = 0
    · have hσ : σ = Equiv.refl (Fin 2) := by
        apply Equiv.ext
        intro i
        fin_cases i
        · dsimp
          exact h0
        · dsimp
          have hne : (σ 1).val ≠ (σ 0).val := fun hv ↦
            σ.injective.ne (by decide : (1 : Fin 2) ≠ 0) (Fin.ext hv)
          have h0v : (σ 0).val = 0 := congrArg Fin.val h0
          have h1lt : (σ 1).val < 2 := (σ 1).isLt
          apply Fin.ext
          change (σ 1).val = 1
          omega
      subst hσ
      exact IdentDistrib.refl hW_aem
    · have h01 : σ 0 = 1 := by
        have h0ne : (σ 0).val ≠ 0 := fun hv ↦ h0 (Fin.ext hv)
        have h0lt : (σ 0).val < 2 := (σ 0).isLt
        apply Fin.ext
        change (σ 0).val = 1
        omega
      have h10 : σ 1 = 0 := by
        have hne : (σ 1).val ≠ (σ 0).val := fun hv ↦
          σ.injective.ne (by decide : (1 : Fin 2) ≠ 0) (Fin.ext hv)
        have h01v : (σ 0).val = 1 := congrArg Fin.val h01
        have h1lt : (σ 1).val < 2 := (σ 1).isLt
        apply Fin.ext
        change (σ 1).val = 0
        omega
      have hcomp := hpair.symm.comp hofPair
      have hlhs : (ofPair ∘ fun ω ↦ (W' ω, W ω)) =
          fun ω i ↦ (![W, W'] : Fin 2 → Ω → α) (σ i) ω := by
        ext ω i
        fin_cases i <;> simp [ofPair, h01, h10]
      have hrhs : (ofPair ∘ fun ω ↦ (W ω, W' ω)) = fun ω i ↦ (![W, W'] : Fin 2 → Ω → α) i ω := by
        ext ω i
        fin_cases i <;> simp [ofPair]
      rwa [hlhs, hrhs] at hcomp

/-- Under `IsExchangeableTuple`, any two coordinates `X i` and `X j` are identically distributed. -/
theorem IsExchangeableTuple.identDistrib_apply
    {Ω ι α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {X : ι → Ω → α} (hexch : IsExchangeableTuple P X) (i j : ι) :
    IdentDistrib (X i) (X j) P P := by
  classical
  have h := (hexch (Equiv.swap j i)).comp (measurable_pi_apply j)
  simpa [Function.comp_def, Equiv.swap_apply_left] using h

/-- Under `IsExchangeableTuple` on a `[Fintype ι]`, for every `i i₀ : ι`, the pair
`(X i, ∑ k, X k)` has the same joint distribution as `(X i₀, ∑ k, X k)`. -/
theorem IsExchangeableTuple.identDistrib_coord_and_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {X : ι → Ω → ℝ} (hexch : IsExchangeableTuple P X) (i₀ i : ι) :
    IdentDistrib
      (fun ω ↦ (X i ω, ∑ k : ι, X k ω))
      (fun ω ↦ (X i₀ ω, ∑ k : ι, X k ω)) P P := by
  classical
  let σ : Equiv.Perm ι := Equiv.swap i₀ i
  let Φ : (ι → ℝ) → ℝ × ℝ := fun u ↦ (u i₀, ∑ k : ι, u k)
  have hΦ : Measurable Φ :=
    (measurable_pi_apply i₀).prodMk
      (Finset.measurable_fun_sum Finset.univ fun k _ ↦ measurable_pi_apply k)
  have h := (hexch σ).comp hΦ
  have hlhs : (Φ ∘ fun ω k ↦ X (σ k) ω) = fun ω ↦ (X i ω, ∑ k : ι, X k ω) := by
    ext ω
    · simp [Φ, σ]
    · simp only [Function.comp_apply, Φ]
      exact Equiv.sum_comp σ (fun k ↦ X k ω)
  have hrhs : (Φ ∘ fun ω k ↦ X k ω) = fun ω ↦ (X i₀ ω, ∑ k : ι, X k ω) := rfl
  rwa [hlhs, hrhs] at h

/-! ### Helper lemmas for `{0, 1}`-valued random variables -/

private lemma ae_eq_indicator_of_zero_or_one
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Ω → ℝ}
    (hzo : ∀ᵐ ω ∂P, U ω = 0 ∨ U ω = 1) :
    U =ᵐ[P] (U ⁻¹' {1}).indicator 1 := by
  filter_upwards [hzo] with ω hω
  rcases hω with h0 | h1
  · have hnot : ω ∉ U ⁻¹' {1} := by simp [h0]
    rw [h0, Set.indicator_of_notMem hnot]
  · have hmem : ω ∈ U ⁻¹' {1} := by simp [h1]
    rw [h1, Set.indicator_of_mem hmem, Pi.one_apply]

private lemma integral_eq_prob_of_zero_or_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {U : Ω → ℝ}
    (hU_meas : Measurable U) (hzo : ∀ᵐ ω ∂P, U ω = 0 ∨ U ω = 1) :
    ∫ ω, U ω ∂P = P.real (U ⁻¹' {1}) := by
  rw [integral_congr_ae (ae_eq_indicator_of_zero_or_one hzo),
    integral_indicator_one (hU_meas (measurableSet_singleton 1))]

/-! ### Corollary 4.12: Size-bias coupling for exchangeable zero-one indicators -/

/-- **Corollary 4.12** over an arbitrary `[Fintype ι]` with distinguished index `i₀ : ι`
(`\label{cor122}`, `SteinIntro.tex:2148-2154`; `ISSUE-TYPO-4.12`): if `(X_i)_{i ∈ ι}` are
exchangeable `{0, 1}`-indicators under `P` and `Y` under `P'` has the conditional distribution of
`(X_j)_{j ≠ i₀}` given `X_{i₀} = 1` (whenever `ℙ(X_{i₀} = 1) > 0`), then
`W^s = (∑_{j ≠ i₀} Y_j) + 1` under `P'` has the size-bias distribution of `W = ∑_i X_i`. -/
theorem sizeBias_sum_of_exchangeable_zero_one_fintype
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (i₀ : ι) {X : ι → Ω → ℝ} {Y : Ω' → ({j : ι // j ≠ i₀} → ℝ)}
    (hX_meas : ∀ i : ι, Measurable (X i))
    (hX_zo : ∀ i : ι, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hexch : IsExchangeableTuple P X)
    (hY_meas : AEMeasurable Y P')
    (hY_law : 0 < P.real (X i₀ ⁻¹' {1}) →
      P'.map Y =
        (ProbabilityTheory.cond P (X i₀ ⁻¹' {1})).map
          (fun ω (j : {j : ι // j ≠ i₀}) ↦ X j.1 ω)) :
    IsSizeBias P (fun ω ↦ ∑ i : ι, X i ω) P'
      (fun ω' ↦ (∑ j : {j : ι // j ≠ i₀}, Y ω' j) + 1) := by
  let W : Ω → ℝ := fun ω ↦ ∑ i : ι, X i ω
  let sumSub : ({j : ι // j ≠ i₀} → ℝ) → ℝ := fun u ↦ (∑ j : {j : ι // j ≠ i₀}, u j) + 1
  have hsumSub_meas : Measurable sumSub :=
    (Finset.measurable_fun_sum Finset.univ fun j _ ↦ measurable_pi_apply j).fun_add measurable_const
  have hX_nn : ∀ i : ι, 0 ≤ᵐ[P] X i := fun i ↦
    (hX_zo i).mono fun ω hω ↦ by rcases hω with h | h <;> simp [h]
  have hW_nn : 0 ≤ᵐ[P] W := by
    have hall : ∀ᵐ ω ∂P, ∀ i : ι, 0 ≤ X i ω := ae_all_iff.mpr hX_nn
    filter_upwards [hall] with ω hω
    exact Finset.sum_nonneg fun i _ ↦ hω i
  have hX_bdd : ∀ i : ι, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ (1 : ℝ) := fun i ↦
    (hX_zo i).mono fun ω hω ↦ by rcases hω with h | h <;> simp [h]
  have hX_int : ∀ i : ι, Integrable (X i) P := fun i ↦
    (integrable_const (1 : ℝ)).mono' (hX_meas i).aestronglyMeasurable (hX_bdd i)
  have hW_int : Integrable W P := integrable_finsetSum _ fun i _ ↦ hX_int i
  have hWs_meas : AEMeasurable (fun ω' ↦ sumSub (Y ω')) P' :=
    hsumSub_meas.comp_aemeasurable hY_meas
  refine ⟨hW_nn, hW_int, hWs_meas, ?_⟩
  intro f hf_meas hWf_int
  have hW_meas : Measurable W := Finset.measurable_fun_sum _ fun i _ ↦ hX_meas i
  have hXifW_int : ∀ i : ι, Integrable (fun ω ↦ X i ω * f (W ω)) P := by
    intro i
    refine hWf_int.norm.mono'
      ((hX_meas i).fun_mul (hf_meas.comp hW_meas)).aestronglyMeasurable ?_
    have hall : ∀ᵐ ω ∂P, ∀ k : ι, 0 ≤ X k ω := ae_all_iff.mpr hX_nn
    filter_upwards [hall] with ω hω
    have hXi_le_W : X i ω ≤ W ω :=
      Finset.single_le_sum (fun k _ ↦ hω k) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (hω i), abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ hω k)]
    exact mul_le_mul_of_nonneg_right hXi_le_W (abs_nonneg _)
  have hcoord_mean : ∀ i : ι, ∫ ω, X i ω ∂P = ∫ ω, X i₀ ω ∂P := fun i ↦
    (hexch.identDistrib_apply i i₀).integral_eq
  have hW_mean : ∫ ω, W ω ∂P = (Fintype.card ι : ℝ) * ∫ ω, X i₀ ω ∂P := by
    rw [integral_finsetSum Finset.univ fun i _ ↦ hX_int i]
    simp_rw [hcoord_mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcoord_prod : ∀ i : ι,
      ∫ ω, X i ω * f (W ω) ∂P = ∫ ω, X i₀ ω * f (W ω) ∂P := by
    intro i
    let ψ : ℝ × ℝ → ℝ := fun p ↦ p.1 * f p.2
    have hψ : Measurable ψ := measurable_fst.fun_mul (hf_meas.comp measurable_snd)
    exact ((hexch.identDistrib_coord_and_sum i₀ i).comp hψ).integral_eq
  have hWf_sum : ∫ ω, W ω * f (W ω) ∂P =
      (Fintype.card ι : ℝ) * ∫ ω, X i₀ ω * f (W ω) ∂P := by
    have hfun : (fun ω ↦ W ω * f (W ω)) = fun ω ↦ ∑ i : ι, X i ω * f (W ω) := by
      ext ω
      exact Finset.sum_mul Finset.univ (fun i ↦ X i ω) (f (W ω))
    rw [hfun, integral_finsetSum Finset.univ fun i _ ↦ hXifW_int i]
    simp_rw [hcoord_prod, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  set p₀ : ℝ := P.real (X i₀ ⁻¹' {1})
  have hp₀_eq : ∫ ω, X i₀ ω ∂P = p₀ := integral_eq_prob_of_zero_or_one P (hX_meas i₀) (hX_zo i₀)
  have hp₀_nn : 0 ≤ p₀ := measureReal_nonneg
  rcases hp₀_nn.eq_or_lt with hp₀_zero | hp₀_pos
  · have hXi0_zero : X i₀ =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (hX_nn i₀) (hX_int i₀)).mp (hp₀_eq.trans hp₀_zero.symm)
    have hprod_zero : (fun ω ↦ X i₀ ω * f (W ω)) =ᵐ[P] (fun _ : Ω ↦ (0 : ℝ)) := by
      filter_upwards [hXi0_zero] with ω hω
      simp [hω]
    rw [hWf_sum, integral_congr_ae hprod_zero, integral_zero, mul_zero,
      hW_mean, hp₀_eq, ← hp₀_zero, mul_zero, zero_mul]
  · let A : Set Ω := X i₀ ⁻¹' {1}
    have hA_meas : MeasurableSet A := hX_meas i₀ (measurableSet_singleton 1)
    let proj : Ω → ({j : ι // j ≠ i₀} → ℝ) := fun ω j ↦ X j.1 ω
    have hproj_meas : Measurable proj :=
      Measurable.of_eval fun (j : {j : ι // j ≠ i₀}) ↦ hX_meas j.1
    have hae_ind : (fun ω ↦ X i₀ ω * f (W ω)) =ᵐ[P]
        A.indicator (fun ω ↦ f (sumSub (proj ω))) := by
      filter_upwards [hX_zo i₀] with ω hω
      rcases hω with h0 | h1
      · have hnot : ω ∉ A := by simp [A, h0]
        rw [h0, zero_mul, Set.indicator_of_notMem hnot]
      · have hmem : ω ∈ A := by simp [A, h1]
        rw [h1, one_mul, Set.indicator_of_mem hmem]
        congr 1
        have hsplit : (∑ i : ι, X i ω) = (∑ i ∈ Finset.univ.erase i₀, X i ω) + X i₀ ω :=
          (Finset.sum_erase_add Finset.univ (fun i ↦ X i ω) (Finset.mem_univ i₀)).symm
        have hsub : (∑ j : {j : ι // j ≠ i₀}, X j.1 ω) = ∑ i ∈ Finset.univ.erase i₀, X i ω :=
          (Finset.sum_subtype (Finset.univ.erase i₀) (p := fun i ↦ i ≠ i₀)
            (fun i ↦ by simp) (fun i ↦ X i ω)).symm
        dsimp [W, sumSub, proj]
        rw [hsplit, h1, hsub]
    have hcond_eq : ∫ ω in A, f (sumSub (proj ω)) ∂P =
        p₀ * ∫ ω, f (sumSub (proj ω)) ∂(ProbabilityTheory.cond P A) := by
      rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
        ← measureReal_def]
      exact (mul_inv_cancel_left₀ hp₀_pos.ne' _).symm
    have hmap_eq : ∫ ω, f (sumSub (proj ω)) ∂(ProbabilityTheory.cond P A) =
        ∫ ω', f (sumSub (Y ω')) ∂P' := by
      let g : ({j : ι // j ≠ i₀} → ℝ) → ℝ := fun u ↦ f (sumSub u)
      have hg_meas : Measurable g := hf_meas.comp hsumSub_meas
      calc
        ∫ ω, g (proj ω) ∂(ProbabilityTheory.cond P A)
            = ∫ u, g u ∂((ProbabilityTheory.cond P A).map proj) :=
          (integral_map hproj_meas.aemeasurable hg_meas.aestronglyMeasurable).symm
        _ = ∫ u, g u ∂(P'.map Y) := by rw [← hY_law hp₀_pos]
        _ = ∫ ω', g (Y ω') ∂P' :=
          integral_map hY_meas hg_meas.aestronglyMeasurable
    have hi0_eq : ∫ ω, X i₀ ω * f (W ω) ∂P = p₀ * ∫ ω', f (sumSub (Y ω')) ∂P' := by
      rw [integral_congr_ae hae_ind, integral_indicator hA_meas, hcond_eq, hmap_eq]
    change ∫ ω, W ω * f (W ω) ∂P = (∫ ω, W ω ∂P) * ∫ ω', f (sumSub (Y ω')) ∂P'
    rw [hWf_sum, hi0_eq, hW_mean, hp₀_eq, mul_assoc]

/-- **Corollary 4.12** (`\label{cor122}`, `SteinIntro.tex:2148-2154`; `ISSUE-TYPO-4.12`),
`Fin n` specialization at vertex `⟨0, hn⟩` matching `SteinMethod.Cor4_12`. -/
theorem sizeBias_sum_of_exchangeable_zero_one_fin
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {Y : Ω' → ({j : Fin n // j ≠ ⟨0, hn⟩} → ℝ)}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hexch : IsExchangeableTuple P X)
    (hY_meas : AEMeasurable Y P')
    (hY_law : 0 < P.real (X ⟨0, hn⟩ ⁻¹' {1}) →
      P'.map Y =
        (ProbabilityTheory.cond P (X ⟨0, hn⟩ ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ ⟨0, hn⟩}) ↦ X j.1 ω)) :
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P'
      (fun ω' ↦ (∑ j : {j : Fin n // j ≠ ⟨0, hn⟩}, Y ω' j) + 1) :=
  sizeBias_sum_of_exchangeable_zero_one_fintype P P' (⟨0, hn⟩ : Fin n) hX_meas hX_zo hexch
    hY_meas hY_law

/-! ### Example 4.4: Law of small numbers via size-bias coupling -/

private lemma cond_map_eq_map_of_indepFun
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (hindep : IndepFun U V P) {s : Set α} (hs : MeasurableSet s)
    (hpos : 0 < P.real (U ⁻¹' s)) :
    (ProbabilityTheory.cond P (U ⁻¹' s)).map V = P.map V := by
  have hPA0 : P (U ⁻¹' s) ≠ 0 := by
    intro h0
    have : P.real (U ⁻¹' s) = 0 := by simp [Measure.real, h0]
    linarith
  have hPA_top : P (U ⁻¹' s) ≠ ⊤ := measure_ne_top P _
  ext B hB
  rw [Measure.map_apply hV hB, Measure.map_apply hV hB,
    ProbabilityTheory.cond_apply (hU hs) P (V ⁻¹' B),
    hindep.measure_inter_preimage_eq_mul s B hs hB,
    ← mul_assoc, ENNReal.inv_mul_cancel hPA0 hPA_top, one_mul]

/-- **Example 4.4** (*Law of small numbers*, `SteinIntro.tex:2162-2172`): for independent
`{0, 1}`-indicators `X_1, ..., X_n` with `p_i = ℙ(X_i = 1)`, `W = ∑_i X_i`,
`r = ∑_i p_i > 0`, an independent index `I` with `ℙ(I = i) = p_i / r`, and `Z ~ Po(r)`,
`W^s = ∑_{j ≠ I} X_j + 1` is a size-bias coupling of `W` and
`d_TV(W, Z) ≤ min(1, r) 𝔼[X_I] = min(1, r) ∑_i (p_i / r) 𝔼[X_i] = min(1, r⁻¹) ∑_i p_i²`. -/
theorem lawOfSmallNumbers_sizeBias_and_tvDist
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {I : Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hX_indep : ProbabilityTheory.iIndepFun X P) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, (X j.1 ω : ℝ)) + 1
    0 < r →
    (∑ i : Fin n, p i = (r : ℝ)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω i ↦ X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal (min 1 (r : ℝ) * ∫ ω, (X (I ω) ω : ℝ) ∂P) ∧
      min 1 (r : ℝ) * ∫ ω, (X (I ω) ω : ℝ) ∂P =
        min 1 (r : ℝ) * ∑ i : Fin n, (p i / (r : ℝ)) * ∫ ω, (X i ω : ℝ) ∂P ∧
      min 1 (r : ℝ) * ∑ i : Fin n, (p i / (r : ℝ)) * ∫ ω, (X i ω : ℝ) ∂P =
        min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2 := by
  intro p W Ws hr hsum_p hI_meas hI_prob hI_indep hZ_meas hZ_law
  let Xr : Fin n → Ω → ℝ := fun i ω ↦ (X i ω : ℝ)
  let Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ) := fun i ω j ↦ Xr j.1 ω
  have hXr_meas : ∀ i : Fin n, Measurable (Xr i) :=
    fun i ↦ (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (hX_meas i)
  have hXr_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, Xr i ω = 0 ∨ Xr i ω = 1 :=
    fun i ↦ (hX_zo i).mono fun ω hω ↦ by rcases hω with h | h <;> simp [Xr, h]
  have hpre : ∀ i : Fin n, Xr i ⁻¹' {(1 : ℝ)} = {ω | X i ω = 1} := by
    intro i
    ext ω
    simp [Xr]
  have hlam_eq : (∑ i : Fin n, P.real (Xr i ⁻¹' {1})) = (r : ℝ) := by
    simp_rw [hpre]
    exact hsum_p
  have hr_pos : (0 : ℝ) < r := NNReal.coe_pos.mpr hr
  have hcast_nat : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  have hY_meas : ∀ i : Fin n, AEMeasurable (Y i) P :=
    fun i ↦ (Measurable.of_eval fun (j : {j : Fin n // j ≠ i}) ↦ hXr_meas j.1).aemeasurable
  have hXr_indep : ProbabilityTheory.iIndepFun Xr P :=
    hX_indep.comp (fun _ ↦ (Nat.cast : ℕ → ℝ)) fun _ ↦ hcast_nat
  have hY_law : ∀ i : Fin n, 0 < P.real (Xr i ⁻¹' {1}) →
      P.map (Y i) =
        (ProbabilityTheory.cond P (Xr i ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ Xr j.1 ω) := by
    intro i hi_pos
    have hind : IndepFun (Xr i) (Y i) P := by
      have hsub := hXr_indep.indepFun_finset ({i} : Finset (Fin n)) (Finset.univ.erase i)
        (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase i Finset.univ)) hXr_meas
      let f₁ : (({i} : Finset (Fin n)) → ℝ) → ℝ := fun u ↦ u ⟨i, Finset.mem_singleton_self i⟩
      let f₂ : ((Finset.univ.erase i) → ℝ) → ({j : Fin n // j ≠ i} → ℝ) :=
        fun u j ↦ u ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ j.1⟩⟩
      have hf₁ : Measurable f₁ := measurable_pi_apply _
      have hf₂ : Measurable f₂ := Measurable.of_eval fun _ ↦ measurable_pi_apply _
      exact hsub.comp hf₁ hf₂
    exact (cond_map_eq_map_of_indepFun P (hXr_meas i)
      (Measurable.of_eval fun (j : {j : Fin n // j ≠ i}) ↦ hXr_meas j.1) hind
      (measurableSet_singleton 1) hi_pos).symm
  have hI_prob' : ∀ i : Fin n,
      P.real (I ⁻¹' {i}) = P.real (Xr i ⁻¹' {1}) / ∑ k : Fin n, P.real (Xr k ⁻¹' {1}) := by
    intro i
    rw [hpre i, hlam_eq]
    exact hI_prob i
  have hI_indep' :
      ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ Xr i ω, fun i ↦ Y i ω)) P := by
    let det : (Fin n → ℕ) → (Fin n → ℝ) × ((i : Fin n) → {j : Fin n // j ≠ i} → ℝ) :=
      fun u ↦ (fun i ↦ (u i : ℝ), fun i j ↦ (u j.1 : ℝ))
    have hdet : Measurable det :=
      (Measurable.of_eval fun i ↦ hcast_nat.comp (measurable_pi_apply i)).prodMk
      (Measurable.of_eval fun i ↦
        Measurable.of_eval fun (j : {j : Fin n // j ≠ i}) ↦
          hcast_nat.comp (measurable_pi_apply j.1))
    exact hI_indep.comp measurable_id hdet
  have hSB_sum := sizeBias_sum_of_zero_one_fin P hXr_meas hXr_zo (hlam_eq ▸ hr_pos)
    hY_meas hY_law hI_meas hI_prob' hI_indep'
  have hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws := by
    simpa [W, Ws, Xr, Y, Nat.cast_sum] using hSB_sum
  have hmean_i : ∀ i : Fin n, ∫ ω, (X i ω : ℝ) ∂P = p i := by
    intro i
    dsimp only [p]
    rw [← hpre i]
    exact integral_eq_prob_of_zero_or_one P (hXr_meas i) (hXr_zo i)
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) := by
    have hXi_int : ∀ i : Fin n, Integrable (Xr i) P := fun i ↦
      (integrable_const (1 : ℝ)).mono' (hXr_meas i).aestronglyMeasurable
        ((hXr_zo i).mono fun ω hω ↦ by rcases hω with h | h <;> simp [h])
    have hfun : (fun ω ↦ (W ω : ℝ)) = fun ω ↦ ∑ i : Fin n, Xr i ω := by
      ext ω
      simp [W, Xr]
    rw [hfun, integral_finsetSum Finset.univ fun i _ ↦ hXi_int i]
    simp_rw [Xr, hmean_i]
    exact hsum_p
  have hWs_int : Integrable Ws P := by
    have hdom_int : Integrable (fun ω ↦ (∑ k : Fin n, Xr k ω) + 1) P :=
      (integrable_finsetSum (Finset.univ : Finset (Fin n)) fun k _ ↦
        (integrable_const (1 : ℝ)).mono' (hXr_meas k).aestronglyMeasurable
          ((hXr_zo k).mono fun ω hω ↦ by rcases hω with h | h <;> simp [h])).add
        (integrable_const 1)
    refine hdom_int.mono' hSB.2.2.1.aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
    have hsub_eq : (∑ j : {j : Fin n // j ≠ I ω}, (X j.1 ω : ℝ)) =
        ∑ i ∈ Finset.univ.erase (I ω), (X i ω : ℝ) :=
      (Finset.sum_subtype (Finset.univ.erase (I ω)) (p := fun i ↦ i ≠ I ω)
        (fun i ↦ by simp) (fun i ↦ (X i ω : ℝ))).symm
    have hsub_le : (∑ j : {j : Fin n // j ≠ I ω}, (X j.1 ω : ℝ)) ≤
        ∑ k : Fin n, (X k ω : ℝ) := by
      rw [hsub_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun _ _ _ ↦ Nat.cast_nonneg _
    have hnn : 0 ≤ Ws ω := by
      dsimp [Ws]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    dsimp [Ws, Xr]
    linarith
  have hinc_eq : ∀ ω : Ω, |(W ω : ℝ) + 1 - Ws ω| = (X (I ω) ω : ℝ) := by
    intro ω
    have hsplit : (W ω : ℝ) =
        (∑ j : {j : Fin n // j ≠ I ω}, (X j.1 ω : ℝ)) + (X (I ω) ω : ℝ) := by
      dsimp [W]
      rw [Nat.cast_sum, ← Finset.sum_erase_add Finset.univ (fun k ↦ (X k ω : ℝ))
        (Finset.mem_univ (I ω)),
        Finset.sum_subtype (Finset.univ.erase (I ω)) (p := fun k ↦ k ≠ I ω) (fun k ↦ by simp)]
    have hdiff : (W ω : ℝ) + 1 - Ws ω = (X (I ω) ω : ℝ) := by
      dsimp [Ws]
      linarith
    rw [hdiff, abs_of_nonneg (Nat.cast_nonneg _)]
  have htv : tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (min 1 (r : ℝ) * ∫ ω, (X (I ω) ω : ℝ) ∂P) := by
    rw [hZ_law]
    have hW_meas : AEMeasurable W P :=
      (Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas i).aemeasurable
    have h := tvDist_poissonLaw_le_of_isSizeBias_integrable P hr hW_meas hW_mean hSB hWs_int
    simpa only [hinc_eq] using h
  have hEXI : ∫ ω, (X (I ω) ω : ℝ) ∂P =
      ∑ i : Fin n, (p i / (r : ℝ)) * ∫ ω, (X i ω : ℝ) ∂P := by
    have hpart : (fun ω ↦ (X (I ω) ω : ℝ)) =
        fun ω ↦ ∑ i : Fin n, (I ⁻¹' {i}).indicator 1 ω * (X i ω : ℝ) := by
      ext ω
      rw [Finset.sum_eq_single (I ω)]
      · simp
      · intro b _ hb
        have hnot : ω ∉ I ⁻¹' {b} := by simp [hb.symm]
        simp [Set.indicator_of_notMem hnot]
      · intro hnot
        exact absurd (Finset.mem_univ (I ω)) hnot
    have hterm_int : ∀ i : Fin n,
        Integrable (fun ω ↦ (I ⁻¹' {i}).indicator (1 : Ω → ℝ) ω * (X i ω : ℝ)) P := by
      intro i
      have hXi_int : Integrable (Xr i) P :=
        (integrable_const (1 : ℝ)).mono' (hXr_meas i).aestronglyMeasurable
          ((hXr_zo i).mono fun ω hω ↦ by rcases hω with h | h <;> simp [h])
      refine hXi_int.norm.mono'
        (((measurable_one.indicator (hI_meas (measurableSet_singleton i))).fun_mul
          (hXr_meas i)).aestronglyMeasurable)
        (Eventually.of_forall fun ω ↦ ?_)
      by_cases h : ω ∈ I ⁻¹' {i} <;> simp [Xr, h]
    rw [hpart, integral_finsetSum Finset.univ fun i _ ↦ hterm_int i]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hind_i : IndepFun ((I ⁻¹' {i}).indicator (1 : Ω → ℝ)) (Xr i) P := by
      let g₁ : Fin n → ℝ := ({i} : Set (Fin n)).indicator 1
      let g₂ : (Fin n → ℕ) → ℝ := fun u ↦ (u i : ℝ)
      have hg₁ : Measurable g₁ := measurable_one.indicator .of_discrete
      have hg₂ : Measurable g₂ :=
        (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply i)
      exact hI_indep.comp hg₁ hg₂
    have hprod_int := hind_i.integral_fun_mul_eq_mul_integral
      (measurable_one.indicator (hI_meas (measurableSet_singleton i))).aestronglyMeasurable
      (hXr_meas i).aestronglyMeasurable
    rw [hprod_int, integral_indicator_one (hI_meas (measurableSet_singleton i)), hI_prob i]
  have halg1 : min 1 (r : ℝ) * ∫ ω, (X (I ω) ω : ℝ) ∂P =
      min 1 (r : ℝ) * ∑ i : Fin n, (p i / (r : ℝ)) * ∫ ω, (X i ω : ℝ) ∂P := by
    rw [hEXI]
  have halg2 : min 1 (r : ℝ) * ∑ i : Fin n, (p i / (r : ℝ)) * ∫ ω, (X i ω : ℝ) ∂P =
      min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2 := by
    simp_rw [hmean_i]
    have hsum_div : (∑ i : Fin n, p i / (r : ℝ) * p i) =
        (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hsum_div, ← mul_assoc]
    congr 1
    rw [min_mul_of_nonneg _ _ (inv_nonneg.mpr hr_pos.le), one_mul,
      mul_inv_cancel₀ hr_pos.ne', min_comm]
  exact ⟨hSB, htv, halg1, halg2⟩

end SteinMethod
