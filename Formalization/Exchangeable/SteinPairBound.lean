/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Exchangeable.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Real

/-!
# Stein-Pair Normal Approximation Bounds and Exchangeable-Pair Criteria

This module proves the core exchangeable-pair and Stein-pair results from Section 3.2 of
Nathan Ross, *"Fundamentals of Stein's method"* (`SteinIntro.tex:983-1051`, `1133-1152`):

* `reversibleMarkov_isExchangeablePair` (Remark 3.3, `SteinIntro.tex:990-999`).
* `evariance_condExp_mono` (Remark 3.4, `SteinIntro.tex:1000-1008`).
* `isExchangeablePair_of_identDistrib_int_abs_sub_le_one` (Lemma 3.9, `\label{lem51}`,
  `SteinIntro.tex:1133-1152`).
* `steinPair_iSup_normalWassersteinClass_le` (Theorem 3.7 general $a > 0$ Stein-operator supremum
  bound, `\label{thm51}`, `SteinIntro.tex:983-988`, `1026-1050`; ruling `D7`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-- Remark 3.3 (`SteinIntro.tex:990-999`): if a Markov kernel $\kappa$ is reversible with respect
to a probability measure $\mu$ (`(μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ`), then for any measurable
statistic $W$, $(W(X_0), W(X_1))$ is exchangeable under $\mu \otimes_{\mathrm{m}} \kappa$. -/
theorem reversibleMarkov_isExchangeablePair
    {𝒳 α : Type*} [MeasurableSpace 𝒳] [MeasurableSpace α]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel 𝒳 𝒳) [ProbabilityTheory.IsMarkovKernel κ]
    {W : 𝒳 → α}
    (hrev : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ)
    (hW : Measurable W) :
    IsExchangeablePair (μ ⊗ₘ κ) (fun p ↦ W p.1) (fun p ↦ W p.2) := by
  have h12 : Measurable (fun p : 𝒳 × 𝒳 ↦ (W p.1, W p.2)) :=
    (hW.comp measurable_fst).prodMk (hW.comp measurable_snd)
  have h21 : Measurable (fun p : 𝒳 × 𝒳 ↦ (W p.2, W p.1)) :=
    (hW.comp measurable_snd).prodMk (hW.comp measurable_fst)
  refine ⟨h12.aemeasurable, h21.aemeasurable, ?_⟩
  calc
    (μ ⊗ₘ κ).map (fun p ↦ (W p.1, W p.2))
      = ((μ ⊗ₘ κ).map Prod.swap).map (fun p ↦ (W p.1, W p.2)) :=
        congrArg (Measure.map (fun p ↦ (W p.1, W p.2))) hrev.symm
    _ = (μ ⊗ₘ κ).map ((fun p ↦ (W p.1, W p.2)) ∘ Prod.swap) :=
        Measure.map_map h12 measurable_swap
    _ = (μ ⊗ₘ κ).map (fun p ↦ (W p.2, W p.1)) := rfl

private lemma evariance_eq_eLpNorm_two_sq
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P] {g : Ω → ℝ}
    (hg : Integrable g P) :
    ProbabilityTheory.evariance g P = eLpNorm (fun ω ↦ g ω - ∫ x, g x ∂P) 2 P ^ 2 := by
  have hm : AEStronglyMeasurable (fun ω ↦ g ω - ∫ x, g x ∂P) P :=
    (hg.sub (integrable_const (∫ x, g x ∂P))).aestronglyMeasurable
  calc
    ProbabilityTheory.evariance g P
      = ∫⁻ ω, ‖g ω - ∫ x, g x ∂P‖ₑ ^ (2 : ℝ) ∂P := by
        simp only [ProbabilityTheory.evariance, ENNReal.rpow_two]
    _ = eLpNorm' (fun ω ↦ g ω - ∫ x, g x ∂P) 2 P ^ (2 : ℝ) :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' zero_lt_two
    _ = eLpNorm (fun ω ↦ g ω - ∫ x, g x ∂P) 2 P ^ 2 := by
        rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hm, ENNReal.toReal_ofNat,
          ENNReal.rpow_two]

/-- Remark 3.4 (`SteinIntro.tex:1000-1008`): for sub-$\sigma$-algebras $m_1 \le m_2$ of the ambient
$\sigma$-algebra $m_0$ and any integrable random variable $Y$,
$\operatorname{Var}(\mathbb{E}[Y \mid m_1]) \le \operatorname{Var}(\mathbb{E}[Y \mid m_2])$ in
`ℝ≥0∞` (`ProbabilityTheory.evariance`). -/
theorem evariance_condExp_mono
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {m₁ m₂ : MeasurableSpace Ω} {Y : Ω → ℝ}
    (hm₁₂ : m₁ ≤ m₂) (hm₂₀ : m₂ ≤ m₀) (hY : Integrable Y P) :
    ProbabilityTheory.evariance (P[Y | m₁]) P ≤
      ProbabilityTheory.evariance (P[Y | m₂]) P := by
  have hm₁₀ : m₁ ≤ m₀ := hm₁₂.trans hm₂₀
  have hInt₁ : ∫ x, P[Y | m₁] x ∂P = ∫ x, Y x ∂P := by
    simpa only [setIntegral_univ] using setIntegral_condExp hm₁₀ hY .univ
  have hInt₂ : ∫ x, P[Y | m₂] x ∂P = ∫ x, Y x ∂P := by
    simpa only [setIntegral_univ] using setIntegral_condExp hm₂₀ hY .univ
  have hAE :
      (fun ω ↦ P[Y | m₁] ω - ∫ x, P[Y | m₁] x ∂P) =ᵐ[P]
        P[fun ω ↦ P[Y | m₂] ω - ∫ x, P[Y | m₂] x ∂P | m₁] := by
    have hSub :
        P[P[Y | m₂] - (fun _ ↦ ∫ x, P[Y | m₂] x ∂P) | m₁] =ᵐ[P]
          P[P[Y | m₂] | m₁] - P[fun _ ↦ ∫ x, P[Y | m₂] x ∂P | m₁] :=
      condExp_sub (integrable_condExp (μ := P) (m := m₂) (f := Y))
        (integrable_const (∫ x, P[Y | m₂] x ∂P)) m₁
    filter_upwards [condExp_condExp_of_le (μ := P) (f := Y) hm₁₂ hm₂₀, hSub] with ω h1 h2
    change P[Y | m₁] ω - ∫ x, P[Y | m₁] x ∂P =
      P[P[Y | m₂] - (fun _ ↦ ∫ x, P[Y | m₂] x ∂P) | m₁] ω
    rw [h2, Pi.sub_apply, h1, condExp_const (μ := P) hm₁₀ (∫ x, P[Y | m₂] x ∂P), hInt₁, hInt₂]
  rw [evariance_eq_eLpNorm_two_sq P (integrable_condExp (μ := P) (m := m₁) (f := Y)),
    evariance_eq_eLpNorm_two_sq P (integrable_condExp (μ := P) (m := m₂) (f := Y)),
    eLpNorm_congr_ae hAE]
  exact pow_le_pow_left'
    (eLpNorm_condExp_le_eLpNorm (μ := P) (m := m₁)
      (fun ω ↦ P[Y | m₂] ω - ∫ x, P[Y | m₂] x ∂P) one_le_two) 2

private lemma isExchangeablePair_of_identDistrib_int_abs_sub_le_one_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℤ} (hW : Measurable W) (hW' : Measurable W')
    (hId : ProbabilityTheory.IdentDistrib W W' P P)
    (hStep : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ 1) :
    IsExchangeablePair P W W' := by
  have hAdj : ∀ k : ℤ,
      P.real {ω | W ω = k ∧ W' ω = k + 1} = P.real {ω | W' ω = k ∧ W ω = k + 1} := by
    intro k
    set AB : Set Ω := {ω | W ω < k ∨ (W ω = k ∧ W' ω ≤ k)}
    set C₁ : Set Ω := {ω | W' ω = k ∧ W ω = k + 1}
    set C₂ : Set Ω := {ω | W ω = k ∧ W' ω = k + 1}
    have hC₁_meas : MeasurableSet C₁ :=
      (hW' (measurableSet_singleton k)).inter (hW (measurableSet_singleton (k + 1)))
    have hC₂_meas : MeasurableSet C₂ :=
      (hW (measurableSet_singleton k)).inter (hW' (measurableSet_singleton (k + 1)))
    have hDisj₁ : Disjoint AB C₁ := by
      rw [Set.disjoint_left]
      rintro ω (hlt | ⟨heq, _⟩) ⟨_, hWk1⟩ <;> omega
    have hDisj₂ : Disjoint AB C₂ := by
      rw [Set.disjoint_left]
      rintro ω (hlt | ⟨_, hle⟩)
      · rintro ⟨hWk, _⟩
        omega
      · rintro ⟨_, hW'k1⟩
        omega
    have hEq₁ : {ω | W' ω ≤ k} =ᵐ[P] AB ∪ C₁ := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hStep] with ω hω
      simp only [AB, C₁, mem_union, mem_ofPred_eq]
      rw [abs_le] at hω
      omega
    have hEq₂ : {ω | W ω ≤ k} =ᵐ[P] AB ∪ C₂ := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hStep] with ω hω
      simp only [AB, C₂, mem_union, mem_ofPred_eq]
      rw [abs_le] at hω
      omega
    have hLeEq : P.real {ω | W ω ≤ k} = P.real {ω | W' ω ≤ k} := by
      simp only [measureReal_def]
      exact congrArg ENNReal.toReal (hId.measure_mem_eq (s := Iic k) measurableSet_Iic)
    have hU₁ : P.real {ω | W' ω ≤ k} = P.real AB + P.real C₁ := by
      rw [measureReal_congr hEq₁,
        measureReal_union hDisj₁ hC₁_meas (measure_ne_top P AB) (measure_ne_top P C₁)]
    have hU₂ : P.real {ω | W ω ≤ k} = P.real AB + P.real C₂ := by
      rw [measureReal_congr hEq₂,
        measureReal_union hDisj₂ hC₂_meas (measure_ne_top P AB) (measure_ne_top P C₂)]
    linarith
  have h12 : Measurable (fun ω ↦ (W ω, W' ω)) := hW.prodMk hW'
  have h21 : Measurable (fun ω ↦ (W' ω, W ω)) := hW'.prodMk hW
  refine ⟨h12.aemeasurable, h21.aemeasurable, Measure.ext_of_singleton fun ⟨j, l⟩ ↦ ?_⟩
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top (P.map (fun ω ↦ (W ω, W' ω))) {(j, l)})
    (measure_ne_top (P.map (fun ω ↦ (W' ω, W ω))) {(j, l)})).mp ?_
  rw [map_measureReal_apply h12 (measurableSet_singleton (j, l)),
    map_measureReal_apply h21 (measurableSet_singleton (j, l))]
  have hPre₁ : (fun ω ↦ (W ω, W' ω)) ⁻¹' {(j, l)} = {ω | W ω = j ∧ W' ω = l} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_ofPred_eq]
  have hPre₂ : (fun ω ↦ (W' ω, W ω)) ⁻¹' {(j, l)} = {ω | W' ω = j ∧ W ω = l} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_ofPred_eq]
  rw [hPre₁, hPre₂]
  by_cases hjl : j = l
  · subst hjl
    congr 1
    ext ω
    exact and_comm
  · by_cases h1 : l = j + 1
    · subst h1
      exact hAdj j
    · by_cases h2 : j = l + 1
      · subst h2
        simpa only [and_comm] using (hAdj l).symm
      · have hZero₁ : P.real {ω | W ω = j ∧ W' ω = l} = 0 := by
          have hEmp : {ω | W ω = j ∧ W' ω = l} =ᵐ[P] (∅ : Set Ω) := by
            rw [Filter.eventuallyEqSet_empty]
            filter_upwards [hStep] with ω hω ⟨hWj, hW'l⟩
            rw [abs_le] at hω
            omega
          rw [measureReal_congr hEmp, measureReal_empty]
        have hZero₂ : P.real {ω | W' ω = j ∧ W ω = l} = 0 := by
          have hEmp : {ω | W' ω = j ∧ W ω = l} =ᵐ[P] (∅ : Set Ω) := by
            rw [Filter.eventuallyEqSet_empty]
            filter_upwards [hStep] with ω hω ⟨hW'j, hWl⟩
            rw [abs_le] at hω
            omega
          rw [measureReal_congr hEmp, measureReal_empty]
        rw [hZero₁, hZero₂]

/-- Lemma 3.9 (`\label{lem51}`, `SteinIntro.tex:1133-1152`): if $W$ and $W'$ are identically
distributed integer-valued random variables defined on the same probability space such that
$\mathbb{P}(|W' - W| \le 1) = 1$, then $(W, W')$ is an exchangeable pair. -/
theorem isExchangeablePair_of_identDistrib_int_abs_sub_le_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℤ}
    (hId : ProbabilityTheory.IdentDistrib W W' P P)
    (hStep : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ 1) :
    IsExchangeablePair P W W' := by
  have hW_ae : AEMeasurable W P := hId.aemeasurable_fst
  have hW'_ae : AEMeasurable W' P := hId.aemeasurable_snd
  set W₀ : Ω → ℤ := hW_ae.mk W
  set W'₀ : Ω → ℤ := hW'_ae.mk W'
  have hId₀ : ProbabilityTheory.IdentDistrib W₀ W'₀ P P :=
    hW_ae.identDistrib_mk.symm.trans (hId.trans hW'_ae.identDistrib_mk)
  have hStep₀ : ∀ᵐ ω ∂P, |W'₀ ω - W₀ ω| ≤ 1 := by
    filter_upwards [hStep, hW_ae.ae_eq_mk, hW'_ae.ae_eq_mk] with ω hω hWω hW'ω
    dsimp only [W₀, W'₀]
    rwa [← hWω, ← hW'ω]
  have hExch₀ : IsExchangeablePair P W₀ W'₀ :=
    isExchangeablePair_of_identDistrib_int_abs_sub_le_one_measurable P
      hW_ae.measurable_mk hW'_ae.measurable_mk hId₀ hStep₀
  have hEq12 :
      ProbabilityTheory.IdentDistrib (fun ω ↦ (W ω, W' ω)) (fun ω ↦ (W₀ ω, W'₀ ω)) P P :=
    ProbabilityTheory.IdentDistrib.of_ae_eq (hW_ae.prodMk hW'_ae)
      ((hW_ae.ae_eq_mk.and hW'_ae.ae_eq_mk).mono fun _ ⟨h1, h2⟩ ↦ Prod.ext h1 h2)
  have hEq21 :
      ProbabilityTheory.IdentDistrib (fun ω ↦ (W'₀ ω, W₀ ω)) (fun ω ↦ (W' ω, W ω)) P P :=
    (ProbabilityTheory.IdentDistrib.of_ae_eq (hW'_ae.prodMk hW_ae)
      ((hW'_ae.ae_eq_mk.and hW_ae.ae_eq_mk).mono fun _ ⟨h1, h2⟩ ↦ Prod.ext h1 h2)).symm
  exact hEq12.trans (hExch₀.trans hEq21)

private lemma antideriv_taylor_bound
    {f : ℝ → ℝ} (hf : f ∈ normalWassersteinClass) :
    ∃ F : ℝ → ℝ, (∀ t, HasDerivAt F (f t) t) ∧ (∀ w, |F w| ≤ 2 * |w|) ∧
      ∀ w w',
        |F w' - F w - (w' - w) * f w - (1 / 2) * (w' - w) ^ 2 * deriv f w| ≤
          (1 / 3) * |w' - w| ^ 3 := by
  rcases hf with ⟨hf1, hf2, hf_bdd, _, hf''_bdd⟩
  let F : ℝ → ℝ := fun w ↦ ∫ t in (0 : ℝ)..w, f t
  have hcont : Continuous f := hf1.continuous
  have hF_deriv : ∀ t, HasDerivAt F (f t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hF_bdd : ∀ w, |F w| ≤ 2 * |w| := by
    intro w
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := w)
      (C := 2) (f := f) (fun x _ ↦ by simpa only [Real.norm_eq_abs] using hf_bdd x)
    simpa only [F, Real.norm_eq_abs, sub_zero] using hnorm
  refine ⟨F, hF_deriv, hF_bdd, fun w w' ↦ ?_⟩
  let Φ : ℝ → ℝ := fun t ↦ F w' - F t - (w' - t) * f t - (1 / 2) * (w' - t) ^ 2 * deriv f t
  let Φ' : ℝ → ℝ := fun t ↦ -(1 / 2) * (w' - t) ^ 2 * deriv (deriv f) t
  let Ψ : ℝ → ℝ := fun t ↦ (w' - t) ^ 3
  let Ψ' : ℝ → ℝ := fun t ↦ -3 * (w' - t) ^ 2
  have hΦ : ∀ t, HasDerivAt Φ (Φ' t) t := by
    intro t
    have hd_sub : HasDerivAt (fun s ↦ w' - s) (-1) t := (hasDerivAt_id' t).const_sub w'
    have hd0 : HasDerivAt (fun s ↦ F w' - F s) (-f t) t := (hF_deriv t).const_sub (F w')
    have hd1 : HasDerivAt (fun s ↦ (w' - s) * f s) ((-1) * f t + (w' - t) * deriv f t) t :=
      hd_sub.fun_mul (hf1 t).hasDerivAt
    have hd_sq : HasDerivAt (fun s ↦ (w' - s) ^ 2) (↑(2 : ℕ) * (w' - t) ^ (2 - 1) * (-1)) t :=
      hd_sub.fun_pow 2
    have hd2 :
        HasDerivAt (fun s ↦ (1 / 2) * (w' - s) ^ 2 * deriv f s)
          (((1 / 2) * (↑(2 : ℕ) * (w' - t) ^ (2 - 1) * (-1))) * deriv f t +
            ((1 / 2) * (w' - t) ^ 2) * deriv (deriv f) t) t :=
      (hd_sq.const_mul (1 / 2)).fun_mul (hf2 t).hasDerivAt
    have hΦ'_eq :
        Φ' t =
          -f t - ((-1) * f t + (w' - t) * deriv f t) -
            (((1 / 2) * (↑(2 : ℕ) * (w' - t) ^ (2 - 1) * (-1))) * deriv f t +
              ((1 / 2) * (w' - t) ^ 2) * deriv (deriv f) t) := by
      dsimp only [Φ']
      push_cast
      ring
    rw [hΦ'_eq]
    exact (hd0.fun_sub hd1).fun_sub hd2
  have hΨ : ∀ t, HasDerivAt Ψ (Ψ' t) t := by
    intro t
    have hd_sub : HasDerivAt (fun s ↦ w' - s) (-1) t := (hasDerivAt_id' t).const_sub w'
    have hΨ'_eq : Ψ' t = ↑(3 : ℕ) * (w' - t) ^ (3 - 1) * (-1) := by
      dsimp only [Ψ']
      push_cast
      ring
    rw [hΨ'_eq]
    exact hd_sub.fun_pow 3
  have hΦ_cont : Continuous Φ := continuous_iff_continuousAt.mpr fun t ↦ (hΦ t).continuousAt
  have hΨ_cont : Continuous Ψ := continuous_iff_continuousAt.mpr fun t ↦ (hΨ t).continuousAt
  have hΦ_w' : Φ w' = 0 := by
    dsimp only [Φ]
    ring
  have hΨ_w' : Ψ w' = 0 := by
    dsimp only [Ψ]
    ring
  change |Φ w| ≤ (1 / 3) * |w' - w| ^ 3
  rcases lt_trichotomy w w' with hww' | hww' | hw'w
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hww' hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hc_ne : (w' - c) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hc.2.ne')
    have hfac : (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 = 0 := by
      have h0 : (Ψ w' - Ψ w) * Φ' c - (Φ w' - Φ w) * Ψ' c = 0 := sub_eq_zero.mpr hratio
      rw [hΦ_w', hΨ_w'] at h0
      dsimp only [Φ', Ψ', Ψ] at h0
      linarith [
        (by ring :
          (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 =
            -((0 - (w' - w) ^ 3) * (-(1 / 2) * (w' - c) ^ 2 * deriv (deriv f) c) -
              (0 - Φ w) * (-3 * (w' - c) ^ 2)))]
    have hΦw : Φ w = (1 / 6) * (w' - w) ^ 3 * deriv (deriv f) c := by
      have hlin := (mul_eq_zero.mp hfac).resolve_right hc_ne
      linarith
    calc
      |Φ w| = (1 / 6) * |w' - w| ^ 3 * |deriv (deriv f) c| := by
        rw [hΦw, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6), abs_pow]
      _ ≤ (1 / 6) * |w' - w| ^ 3 * 2 :=
        mul_le_mul_of_nonneg_left (hf''_bdd c) (by positivity)
      _ = (1 / 3) * |w' - w| ^ 3 := by ring
  · subst hww'
    rw [hΦ_w', sub_self, abs_zero]
    norm_num
  · obtain ⟨c, hc, hratio⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope Φ Φ' hw'w hΦ_cont.continuousOn (fun t _ ↦ hΦ t)
        Ψ Ψ' hΨ_cont.continuousOn (fun t _ ↦ hΨ t)
    have hc_ne : (w' - c) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hc.1.ne)
    have hfac : (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 = 0 := by
      have h0 : (Ψ w - Ψ w') * Φ' c - (Φ w - Φ w') * Ψ' c = 0 := sub_eq_zero.mpr hratio
      rw [hΦ_w', hΨ_w'] at h0
      dsimp only [Φ', Ψ', Ψ] at h0
      linarith [
        (by ring :
          (3 * Φ w - (1 / 2) * (w' - w) ^ 3 * deriv (deriv f) c) * (w' - c) ^ 2 =
            ((w' - w) ^ 3 - 0) * (-(1 / 2) * (w' - c) ^ 2 * deriv (deriv f) c) -
              (Φ w - 0) * (-3 * (w' - c) ^ 2))]
    have hΦw : Φ w = (1 / 6) * (w' - w) ^ 3 * deriv (deriv f) c := by
      have hlin := (mul_eq_zero.mp hfac).resolve_right hc_ne
      linarith
    calc
      |Φ w| = (1 / 6) * |w' - w| ^ 3 * |deriv (deriv f) c| := by
        rw [hΦw, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6), abs_pow]
      _ ≤ (1 / 6) * |w' - w| ^ 3 * 2 :=
        mul_le_mul_of_nonneg_left (hf''_bdd c) (by positivity)
      _ = (1 / 3) * |w' - w| ^ 3 := by ring

private lemma integral_abs_sub_le_sqrt_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg2 : MemLp g 2 P) :
    ∫ ω, |g ω - ∫ x, g x ∂P| ∂P ≤ Real.sqrt (ProbabilityTheory.variance g P) := by
  set m : ℝ := ∫ x, g x ∂P
  set h : Ω → ℝ := fun ω ↦ |g ω - m|
  set c : ℝ := ∫ ω, h ω ∂P
  have hg_int : Integrable g P := hg2.integrable one_le_two
  have hh_int : Integrable h P := by
    dsimp only [h]
    simpa only [Real.norm_eq_abs] using (hg_int.sub' (integrable_const m)).norm
  have hsq_int : Integrable (fun ω ↦ (g ω - m) ^ 2) P :=
    (hg2.sub (memLp_const m)).integrable_sq
  have hnonneg : 0 ≤ ∫ ω, (h ω - c) ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg (h ω - c)
  have hexp : (fun ω ↦ (h ω - c) ^ 2) =
      fun ω ↦ ((g ω - m) ^ 2 - 2 * c * h ω) + c ^ 2 := by
    ext ω
    have habs : h ω ^ 2 = (g ω - m) ^ 2 := sq_abs (g ω - m)
    dsimp only [h] at habs ⊢
    linarith [
      (by ring :
        (|g ω - m| - c) ^ 2 - (((g ω - m) ^ 2 - 2 * c * |g ω - m|) + c ^ 2) =
          |g ω - m| ^ 2 - (g ω - m) ^ 2)]
  have hcalc : ∫ ω, (h ω - c) ^ 2 ∂P = ProbabilityTheory.variance g P - c ^ 2 := by
    rw [hexp, integral_add (hsq_int.sub' (hh_int.const_mul (2 * c))) (integrable_const (c ^ 2)),
      integral_sub hsq_int (hh_int.const_mul (2 * c)), integral_const_mul (2 * c) h,
      integral_const (c ^ 2), probReal_univ, one_smul]
    dsimp only [c, m]
    rw [← ProbabilityTheory.variance_eq_integral hg_int.aemeasurable]
    ring
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- Theorem 3.7, general $a > 0$ Stein-operator supremum bound (`\label{thm51}`,
`SteinIntro.tex:983-988`, proof `SteinIntro.tex:1026-1050`; ruling `D7`): if $(W, W')$ is an
exchangeable pair with $0 < a$, measurable $W$, $\mathbb{E}[W' \mid W] = (1 - a) W$ a.s., and
$\mathbb{E}[W^2] = 1$, then
$$\sup_{f \in \mathcal{F}} |\mathbb{E}[f'(W) - W f(W)]| \le
\frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])}}{\sqrt{2\pi}\,a} +
\frac{\mathbb{E}|W' - W|^3}{3a}$$
in `ℝ≥0∞` (`ProbabilityTheory.evariance`, `lintegral`). -/
theorem steinPair_iSup_normalWassersteinClass_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω)
    (hW2_eq : ∫ ω, W ω ^ 2 ∂P = 1) :
    (⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|) ≤
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (Real.sqrt (2 * Real.pi) * a) +
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * a) := by
  set D : Ω → ℝ := fun ω ↦ W' ω - W ω
  set Q : Ω → ℝ := P[fun ω ↦ D ω ^ 2 | MeasurableSpace.comap W inferInstance]
  set V : ℝ≥0∞ := ProbabilityTheory.evariance Q P
  set M3 : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (|D ω| ^ 3) ∂P
  rcases eq_or_ne M3 ⊤ with hM3_top | hM3_ne_top
  · rw [hM3_top, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, add_top]
    exact le_top
  rcases eq_or_ne V ⊤ with hV_top | hV_ne_top
  · have hV_rpow : V ^ (1 / 2 : ℝ) = ⊤ :=
      (ENNReal.rpow_eq_top_iff_of_pos (by positivity)).mpr hV_top
    rw [hV_rpow, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, top_add]
    exact le_top
  have hW_sq_int : Integrable (fun ω ↦ W ω ^ 2) P := integrable_of_integral_eq_one hW2_eq
  have hW2 : MemLp W 2 P :=
    (memLp_two_iff_integrable_sq hW_meas.aestronglyMeasurable).mpr hW_sq_int
  obtain ⟨hMean, hSqDiff_var⟩ :=
    steinPair_integral_eq_zero_and_sq_sub_eq P hExch ha hW_meas hW2 hCond
  have hVarW : ProbabilityTheory.variance W P = 1 := by
    rw [ProbabilityTheory.variance_of_integral_eq_zero hW_meas.aemeasurable hMean, hW2_eq]
  have hSqDiff : ∫ ω, D ω ^ 2 ∂P = 2 * a := by
    dsimp only [D]
    rw [hSqDiff_var, hVarW, mul_one]
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'2 : MemLp W' 2 P := hId.memLp_snd hW2
  have hW_int : Integrable W P := hW2.integrable one_le_two
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  have hD_int : Integrable D P := hW'_int.sub' hW_int
  have hD_sq_int : Integrable (fun ω ↦ D ω ^ 2) P := (hW'2.sub hW2).integrable_sq
  have hm := hW_meas.comap_le
  have hQ_int : Integrable Q P := integrable_condExp
  have hQ_mean : ∫ ω, Q ω ∂P = 2 * a := by
    dsimp only [Q]
    rw [integral_condExp hm, hSqDiff]
  have hQ2 : MemLp Q 2 P :=
    (ProbabilityTheory.evariance_lt_top_iff_memLp hQ_int.aestronglyMeasurable).mp hV_ne_top.lt_top
  have hV_eq : V ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q P)) := by
    dsimp only [V]
    rw [← ProbabilityTheory.ofReal_variance hQ2,
      ENNReal.ofReal_rpow_of_nonneg (ProbabilityTheory.variance_nonneg Q P) (by positivity),
      ← Real.sqrt_eq_rpow]
  have hD_abs_asm : AEStronglyMeasurable (fun ω ↦ |D ω|) P := by
    simpa only [Real.norm_eq_abs] using hD_int.norm.aestronglyMeasurable
  have hD3_nn : 0 ≤ᵐ[P] fun ω ↦ |D ω| ^ 3 := Eventually.of_forall fun _ ↦ by positivity
  have hD3_int : Integrable (fun ω ↦ |D ω| ^ 3) P :=
    ⟨(continuous_pow 3).comp_aestronglyMeasurable hD_abs_asm,
      (hasFiniteIntegral_iff_ofReal hD3_nn).mpr hM3_ne_top.lt_top⟩
  have hM3_eq : M3 = ENNReal.ofReal (∫ ω, |D ω| ^ 3 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hD3_int hD3_nn).symm
  have hW_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] W :=
    (comap_measurable (m := inferInstance) W).stronglyMeasurable
  have hCondD :
      P[D | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ -a * W ω := by
    filter_upwards [condExp_sub hW'_int hW_int (MeasurableSpace.comap W inferInstance), hCond]
      with ω h1 h2
    change P[W' - W | MeasurableSpace.comap W inferInstance] ω = -a * W ω
    rw [h1, Pi.sub_apply, h2, condExp_of_stronglyMeasurable hm hW_sm hW_int]
    ring
  refine iSup₂_le fun f hf ↦ ?_
  obtain ⟨F, hF_deriv, hF_bdd, hTaylor⟩ := antideriv_taylor_bound hf
  rcases hf with ⟨hf1, hf2, hf_bdd, hf'_bdd, _⟩
  have hF_cont : Continuous F := continuous_iff_continuousAt.mpr fun t ↦ (hF_deriv t).continuousAt
  have hFW_int : Integrable (fun ω ↦ F (W ω)) P :=
    (hW_int.norm.const_mul 2).mono' (hF_cont.comp_aestronglyMeasurable hW_int.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hF_bdd (W ω))
  have hFW'_int : Integrable (fun ω ↦ F (W' ω)) P :=
    (hW'_int.norm.const_mul 2).mono'
      (hF_cont.comp_aestronglyMeasurable hW'_int.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hF_bdd (W' ω))
  have hFW_diff_zero : ∫ ω, (F (W' ω) - F (W ω)) ∂P = 0 := by
    have hFW_eq : ∫ ω, F (W ω) ∂P = ∫ ω, F (W' ω) ∂P :=
      (hId.comp hF_cont.measurable).integral_eq
    rw [integral_sub hFW'_int hFW_int, hFW_eq, sub_self]
  have hfW_sm :
      StronglyMeasurable[MeasurableSpace.comap W inferInstance] (fun ω ↦ f (W ω)) :=
    (hf1.continuous.measurable.comp (comap_measurable (m := inferInstance) W)).stronglyMeasurable
  have hfW_asm : AEStronglyMeasurable (fun ω ↦ f (W ω)) P :=
    (hf1.continuous.measurable.comp hW_meas).aestronglyMeasurable
  have hWfW_int : Integrable (fun ω ↦ W ω * f (W ω)) P :=
    (hW_int.norm.mul_const 2).mono' (hW_int.aestronglyMeasurable.mul hfW_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg (W ω)))
  have hDfW_int : Integrable (fun ω ↦ D ω * f (W ω)) P :=
    (hD_int.norm.mul_const 2).mono' (hD_int.aestronglyMeasurable.mul hfW_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf_bdd (W ω)) (abs_nonneg (D ω)))
  have hCondDfW :
      P[D * (fun ω ↦ f (W ω)) | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        fun ω ↦ -a * (W ω * f (W ω)) := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_right hfW_sm hDfW_int hD_int, hCondD]
      with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    ring
  have hIntDfW : ∫ ω, D ω * f (W ω) ∂P = -a * ∫ ω, W ω * f (W ω) ∂P := calc
    ∫ ω, D ω * f (W ω) ∂P = ∫ ω, (D * fun ω ↦ f (W ω)) ω ∂P := rfl
    _ = ∫ ω, P[D * (fun ω ↦ f (W ω)) | MeasurableSpace.comap W inferInstance] ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, -a * (W ω * f (W ω)) ∂P := integral_congr_ae hCondDfW
    _ = -a * ∫ ω, W ω * f (W ω) ∂P := integral_const_mul (-a) (fun ω ↦ W ω * f (W ω))
  set B₁ : ℝ := Real.sqrt (2 / Real.pi)
  have hf'W_sm :
      StronglyMeasurable[MeasurableSpace.comap W inferInstance] (fun ω ↦ deriv f (W ω)) :=
    (hf2.continuous.measurable.comp (comap_measurable (m := inferInstance) W)).stronglyMeasurable
  have hf'W_asm : AEStronglyMeasurable (fun ω ↦ deriv f (W ω)) P :=
    (hf2.continuous.measurable.comp hW_meas).aestronglyMeasurable
  have hf'W_int : Integrable (fun ω ↦ deriv f (W ω)) P :=
    (integrable_const B₁).mono' hf'W_asm
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hf'_bdd (W ω))
  have hD2f'W_int : Integrable (fun ω ↦ D ω ^ 2 * deriv f (W ω)) P :=
    (hD_sq_int.norm.mul_const B₁).mono' (hD_sq_int.aestronglyMeasurable.mul hf'W_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg (D ω ^ 2)))
  have hCondD2f'W :
      P[(fun ω ↦ D ω ^ 2) * (fun ω ↦ deriv f (W ω)) |
          MeasurableSpace.comap W inferInstance] =ᵐ[P]
        fun ω ↦ Q ω * deriv f (W ω) :=
    condExp_mul_of_stronglyMeasurable_right hf'W_sm hD2f'W_int hD_sq_int
  have hIntD2f'W : ∫ ω, D ω ^ 2 * deriv f (W ω) ∂P = ∫ ω, Q ω * deriv f (W ω) ∂P := calc
    ∫ ω, D ω ^ 2 * deriv f (W ω) ∂P
      = ∫ ω, ((fun ω ↦ D ω ^ 2) * (fun ω ↦ deriv f (W ω))) ω ∂P := rfl
    _ = ∫ ω, P[(fun ω ↦ D ω ^ 2) * (fun ω ↦ deriv f (W ω)) |
          MeasurableSpace.comap W inferInstance] ω ∂P :=
        (integral_condExp hm).symm
    _ = ∫ ω, Q ω * deriv f (W ω) ∂P := integral_congr_ae hCondD2f'W
  have hHalfD2f'W_int : Integrable (fun ω ↦ (1 / 2) * D ω ^ 2 * deriv f (W ω)) P := by
    simpa only [mul_assoc] using hD2f'W_int.const_mul (1 / 2)
  set R : Ω → ℝ :=
    fun ω ↦ F (W' ω) - F (W ω) - D ω * f (W ω) - (1 / 2) * D ω ^ 2 * deriv f (W ω)
  have hR_int : Integrable R P :=
    ((hFW'_int.sub' hFW_int).sub' hDfW_int).sub' hHalfD2f'W_int
  have hIntR :
      ∫ ω, R ω ∂P =
        a * ∫ ω, W ω * f (W ω) ∂P - (1 / 2) * ∫ ω, Q ω * deriv f (W ω) ∂P := by
    have hHalfEq : (fun ω ↦ (1 / 2) * D ω ^ 2 * deriv f (W ω)) =
        fun ω ↦ (1 / 2) * (D ω ^ 2 * deriv f (W ω)) := funext fun _ ↦ by ring
    dsimp only [R]
    rw [integral_sub ((hFW'_int.sub' hFW_int).sub' hDfW_int) hHalfD2f'W_int,
      integral_sub (hFW'_int.sub' hFW_int) hDfW_int,
      hFW_diff_zero, hIntDfW, hHalfEq,
      integral_const_mul (1 / 2) (fun ω ↦ D ω ^ 2 * deriv f (W ω)), hIntD2f'W]
    ring
  have hQf'W_int : Integrable (fun ω ↦ Q ω * deriv f (W ω)) P :=
    (hQ_int.norm.mul_const B₁).mono' (hQ_int.aestronglyMeasurable.mul hf'W_asm)
      (Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs, abs_mul] using
          mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg (Q ω)))
  set S : Ω → ℝ := fun ω ↦ (2 * a - Q ω) * deriv f (W ω)
  have hS_eq : S = fun ω ↦ (2 * a) * deriv f (W ω) - Q ω * deriv f (W ω) :=
    funext fun _ ↦ by ring
  have hS_int : Integrable S P := by
    rw [hS_eq]
    exact (hf'W_int.const_mul (2 * a)).sub' hQf'W_int
  have hSteinId :
      a * ∫ ω, normalSteinOp f (W ω) ∂P = (1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P := by
    have hOp : ∫ ω, normalSteinOp f (W ω) ∂P =
        ∫ ω, deriv f (W ω) ∂P - ∫ ω, W ω * f (W ω) ∂P :=
      integral_sub hf'W_int hWfW_int
    have hIntS : ∫ ω, S ω ∂P =
        (2 * a) * ∫ ω, deriv f (W ω) ∂P - ∫ ω, Q ω * deriv f (W ω) ∂P := by
      rw [hS_eq, integral_sub (hf'W_int.const_mul (2 * a)) hQf'W_int,
        integral_const_mul (2 * a) (fun ω ↦ deriv f (W ω))]
    rw [hOp, hIntS, hIntR]
    ring
  have hR_bound : |∫ ω, R ω ∂P| ≤ (1 / 3) * ∫ ω, |D ω| ^ 3 ∂P := by
    have h1 : |∫ ω, R ω ∂P| ≤ ∫ ω, |R ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm R
    have hR_abs_int : Integrable (fun ω ↦ |R ω|) P := by
      simpa only [Real.norm_eq_abs] using hR_int.norm
    have h2 : ∫ ω, |R ω| ∂P ≤ ∫ ω, (1 / 3) * |D ω| ^ 3 ∂P :=
      integral_mono hR_abs_int (hD3_int.const_mul (1 / 3)) fun ω ↦ hTaylor (W ω) (W' ω)
    rw [integral_const_mul (1 / 3) (fun ω ↦ |D ω| ^ 3)] at h2
    exact h1.trans h2
  have hS_bound :
      |∫ ω, S ω ∂P| ≤ B₁ * Real.sqrt (ProbabilityTheory.variance Q P) := by
    have h1 : |∫ ω, S ω ∂P| ≤ ∫ ω, |S ω| ∂P := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm S
    have hS_abs_int : Integrable (fun ω ↦ |S ω|) P := by
      simpa only [Real.norm_eq_abs] using hS_int.norm
    have hQsub_abs_int : Integrable (fun ω ↦ |Q ω - ∫ x, Q x ∂P|) P := by
      simpa only [Real.norm_eq_abs] using (hQ_int.sub' (integrable_const (∫ x, Q x ∂P))).norm
    have h2 : ∫ ω, |S ω| ∂P ≤ ∫ ω, B₁ * |Q ω - ∫ x, Q x ∂P| ∂P := by
      refine integral_mono hS_abs_int (hQsub_abs_int.const_mul B₁) fun ω ↦ ?_
      dsimp only [S]
      rw [abs_mul, ← hQ_mean, abs_sub_comm (∫ x, Q x ∂P) (Q ω), mul_comm B₁]
      exact mul_le_mul_of_nonneg_left (hf'_bdd (W ω)) (abs_nonneg _)
    rw [integral_const_mul B₁ (fun ω ↦ |Q ω - ∫ x, Q x ∂P|)] at h2
    have h3 : B₁ * ∫ ω, |Q ω - ∫ x, Q x ∂P| ∂P ≤
        B₁ * Real.sqrt (ProbabilityTheory.variance Q P) :=
      mul_le_mul_of_nonneg_left (integral_abs_sub_le_sqrt_variance P hQ2) (Real.sqrt_nonneg _)
    exact h1.trans (h2.trans h3)
  have hMulLe :
      a * |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        (1 / 2) * (B₁ * Real.sqrt (ProbabilityTheory.variance Q P)) +
          (1 / 3) * ∫ ω, |D ω| ^ 3 ∂P := by
    have hAbsEq : a * |∫ ω, normalSteinOp f (W ω) ∂P| =
        |(1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P| := by
      rw [← hSteinId, abs_mul, abs_of_pos ha]
    have hTri :
        |(1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P| ≤
          (1 / 2) * |∫ ω, S ω ∂P| + |∫ ω, R ω ∂P| := by
      have hSubLe :
          |(1 / 2) * ∫ ω, S ω ∂P - ∫ ω, R ω ∂P| ≤
            |(1 / 2) * ∫ ω, S ω ∂P| + |∫ ω, R ω ∂P| :=
        abs_le.mpr
          ⟨by linarith [neg_abs_le ((1 / 2) * ∫ ω, S ω ∂P), le_abs_self (∫ ω, R ω ∂P)],
            by linarith [le_abs_self ((1 / 2) * ∫ ω, S ω ∂P), neg_abs_le (∫ ω, R ω ∂P)]⟩
      rwa [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hSubLe
    linarith
  have hConst₁ :
      (1 / 2) * (B₁ * Real.sqrt (ProbabilityTheory.variance Q P)) =
        a * (Real.sqrt (ProbabilityTheory.variance Q P) / (Real.sqrt (2 * Real.pi) * a)) := by
    set v : ℝ := Real.sqrt (ProbabilityTheory.variance Q P)
    dsimp only [B₁]
    rw [Real.sqrt_div zero_le_two Real.pi, Real.sqrt_mul zero_le_two Real.pi]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
    have hspi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hden : Real.sqrt 2 * Real.sqrt Real.pi * a ≠ 0 :=
      mul_ne_zero (mul_ne_zero hs2 hspi) ha.ne'
    refine mul_right_cancel₀ hden ?_
    have hL :
        (1 / 2) * (Real.sqrt 2 / Real.sqrt Real.pi * v) *
            (Real.sqrt 2 * Real.sqrt Real.pi * a) = a * v := by
      calc
        (1 / 2) * (Real.sqrt 2 / Real.sqrt Real.pi * v) *
            (Real.sqrt 2 * Real.sqrt Real.pi * a)
          = (1 / 2) * (Real.sqrt 2 * Real.sqrt 2) *
              ((Real.sqrt Real.pi)⁻¹ * Real.sqrt Real.pi) * v * a := by
              rw [div_eq_mul_inv]
              ring
        _ = (1 / 2) * 2 * 1 * v * a := by
              rw [Real.mul_self_sqrt zero_le_two, inv_mul_cancel₀ hspi]
        _ = a * v := by ring
    have hR :
        a * (v / (Real.sqrt 2 * Real.sqrt Real.pi * a)) *
            (Real.sqrt 2 * Real.sqrt Real.pi * a) = a * v := by
      rw [mul_assoc, div_mul_cancel₀ v hden]
    rw [hL, hR]
  have hConst₂ :
      (1 / 3) * ∫ ω, |D ω| ^ 3 ∂P = a * ((∫ ω, |D ω| ^ 3 ∂P) / (3 * a)) := by
    have hden : 3 * a ≠ 0 := mul_ne_zero (by norm_num) ha.ne'
    refine mul_right_cancel₀ hden ?_
    have hR : a * ((∫ ω, |D ω| ^ 3 ∂P) / (3 * a)) * (3 * a) = a * ∫ ω, |D ω| ^ 3 ∂P := by
      rw [mul_assoc, div_mul_cancel₀ _ hden]
    rw [hR]
    ring
  have hReal :
      |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        Real.sqrt (ProbabilityTheory.variance Q P) / (Real.sqrt (2 * Real.pi) * a) +
          (∫ ω, |D ω| ^ 3 ∂P) / (3 * a) := by
    refine le_of_mul_le_mul_left ?_ ha
    linarith [hMulLe, hConst₁, hConst₂]
  have hDen₁ : 0 < Real.sqrt (2 * Real.pi) * a :=
    mul_pos (Real.sqrt_pos.mpr (mul_pos zero_lt_two Real.pi_pos)) ha
  have hDen₂ : 0 < 3 * a := mul_pos (by positivity) ha
  have hTerm₁_nn :
      0 ≤ Real.sqrt (ProbabilityTheory.variance Q P) / (Real.sqrt (2 * Real.pi) * a) :=
    div_nonneg (Real.sqrt_nonneg _) hDen₁.le
  have hTerm₂_nn : 0 ≤ (∫ ω, |D ω| ^ 3 ∂P) / (3 * a) :=
    div_nonneg (integral_nonneg fun _ ↦ by positivity) hDen₂.le
  calc
    ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|
      ≤ ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) / (Real.sqrt (2 * Real.pi) * a) +
            (∫ ω, |D ω| ^ 3 ∂P) / (3 * a)) :=
        ENNReal.ofReal_le_ofReal hReal
    _ = ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) / (Real.sqrt (2 * Real.pi) * a)) +
        ENNReal.ofReal ((∫ ω, |D ω| ^ 3 ∂P) / (3 * a)) :=
        ENNReal.ofReal_add hTerm₁_nn hTerm₂_nn
    _ = V ^ (1 / 2 : ℝ) / ENNReal.ofReal (Real.sqrt (2 * Real.pi) * a) +
          M3 / ENNReal.ofReal (3 * a) := by
        rw [ENNReal.ofReal_div_of_pos hDen₁, ENNReal.ofReal_div_of_pos hDen₂, ← hV_eq, ← hM3_eq]

end SteinMethod
