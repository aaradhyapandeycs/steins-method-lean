/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Exchangeable.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Replace-One Stein Pair for Standardized Sums (`Formalization.Exchangeable.IndepSumPair`)

Formalizes the Stein-pair construction and unit second-moment identity of Example 3.6
(`SteinIntro.tex:1053-1069`), along with reusable independence set-integral helpers for the moment
and conditional-variance bounds in `Formalization.Exchangeable.IndepSumPairBounds`:
* `indepSum_replaceOne_isSteinPair`: for independent centered unit-variance random variables
  $X_1, \dots, X_n$ with $\mathbb{E}[X_i^4] < \infty$, an independent copy $(X_1', \dots, X_n')$,
  and an independent uniform random index $I \in \{1, \dots, n\}$, the standardized sum
  $W = n^{-1/2} \sum_{i=1}^n X_i$ and replace-one perturbation
  $W' = W - X_I / \sqrt{n} + X_I' / \sqrt{n}$ form a $(1/n)$-Stein pair
  (`Ex3_6_steinPair`, `SteinIntro.tex:1053-1069`).
* `indepSum_replaceOne_integral_W_sq`: $\mathbb{E}[W^2] = 1$ (`SteinIntro.tex:1054`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SteinMethod

section Helpers

/-- Swaps only the $k$-th coordinate between two $n$-tuples (`SteinIntro.tex:1056-1060`). -/
private def swapCoord {n : ℕ} (k : Fin n) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i ↦ if k = i then p.2 i else p.1 i, fun i ↦ if k = i then p.1 i else p.2 i)

/-- Coordinatewise swap bundled with the random index $k \in \{1, \dots, n\}$
(`SteinIntro.tex:1056-1060`). -/
private def swapPair {n : ℕ} (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) :
    Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (q.1, swapCoord q.1 q.2)

private lemma measurable_swapPair {n : ℕ} : Measurable (@swapPair n) := by
  refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
  · refine Measurable.of_eval fun i ↦ ?_
    have hset : {q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.1 = i} = Prod.fst ⁻¹' {i} := by
      ext q; simp
    refine Measurable.ite (hset ▸ measurable_fst (measurableSet_singleton i)) ?_ ?_
    · exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
    · exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  · refine Measurable.of_eval fun i ↦ ?_
    have hset : {q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.1 = i} = Prod.fst ⁻¹' {i} := by
      ext q; simp
    refine Measurable.ite (hset ▸ measurable_fst (measurableSet_singleton i)) ?_ ?_
    · exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
    · exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)

/-- Swapping the $k$-th coordinate preserves $(\bigotimes_i \mu_i) \otimes (\bigotimes_i \mu_i)$
even when $\mu_1, \dots, \mu_n$ are non-identical (`SteinIntro.tex:1056-1060`). -/
private lemma measurePreserving_swapCoord {n : ℕ} (k : Fin n) (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (swapCoord k)
      ((Measure.pi μ).prod (Measure.pi μ))
      ((Measure.pi μ).prod (Measure.pi μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have he : MeasurePreserving e
      (Measure.pi fun i ↦ (μ i).prod (μ i))
      ((Measure.pi μ).prod (Measure.pi μ)) :=
    measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) μ μ
  have hf : ∀ i : Fin n,
      MeasurePreserving (if k = i then Prod.swap else id)
        ((μ i).prod (μ i)) ((μ i).prod (μ i)) := by
    intro i
    by_cases hk : k = i
    · simp only [hk, ↓reduceIte]
      exact Measure.measurePreserving_swap (μ := μ i) (ν := μ i)
    · simp only [hk, ↓reduceIte]
      exact MeasurePreserving.id ((μ i).prod (μ i))
  have hPi : MeasurePreserving (fun a i ↦ (if k = i then Prod.swap else id) (a i))
      (Measure.pi fun i ↦ (μ i).prod (μ i))
      (Measure.pi fun i ↦ (μ i).prod (μ i)) :=
    measurePreserving_pi (fun i ↦ (μ i).prod (μ i)) (fun i ↦ (μ i).prod (μ i)) hf
  have hcomp :
      MeasurePreserving
        ((e ∘ fun a i ↦ (if k = i then Prod.swap else id) (a i)) ∘ e.symm)
        ((Measure.pi μ).prod (Measure.pi μ))
        ((Measure.pi μ).prod (Measure.pi μ)) :=
    he.comp (hPi.comp (MeasurePreserving.symm e he))
  have he_apply : (e : (Fin n → ℝ × ℝ) → (Fin n → ℝ) × (Fin n → ℝ)) =
      fun a ↦ (fun i ↦ (a i).1, fun i ↦ (a i).2) := rfl
  have he_symm : (e.symm : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ × ℝ) =
      fun p i ↦ (p.1 i, p.2 i) := rfl
  have heq :
      swapCoord k = (e ∘ fun a i ↦ (if k = i then Prod.swap else id) (a i)) ∘ e.symm := by
    rw [he_apply, he_symm]
    funext p
    apply Prod.ext <;> funext i <;> by_cases hk : k = i <;> simp [swapCoord, hk]
  rwa [← heq] at hcomp

/-- Fiberwise invariance of $\mu_I \otimes \nu$ under `swapPair` (`SteinIntro.tex:1056-1060`). -/
private lemma measurePreserving_swapPair {n : ℕ}
    (μI : Measure (Fin n)) [SigmaFinite μI]
    (ν : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [SigmaFinite ν]
    (hSwap : ∀ k : Fin n, MeasurePreserving (swapCoord k) ν ν) :
    MeasurePreserving swapPair (μI.prod ν) (μI.prod ν) where
  measurable := measurable_swapPair
  map_eq := by
    refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [Measure.map_apply measurable_swapPair (hs.prod ht),
      Measure.prod_apply (measurable_swapPair (hs.prod ht))]
    have hslice :
        (fun k : Fin n ↦ ν (Prod.mk k ⁻¹' (swapPair ⁻¹' (s ×ˢ t)))) =
          s.indicator (fun _ ↦ ν t) := by
      funext k
      by_cases hk : k ∈ s
      · have hpre : Prod.mk k ⁻¹' (swapPair ⁻¹' (s ×ˢ t)) = swapCoord k ⁻¹' t := by
          ext p; simp [swapPair, hk]
        rw [Set.indicator_of_mem hk, hpre, ← Measure.map_apply (hSwap k).measurable ht,
          (hSwap k).map_eq]
      · have hpre : Prod.mk k ⁻¹' (swapPair ⁻¹' (s ×ˢ t)) = ∅ := by
          ext p; simp [swapPair, hk]
        rw [Set.indicator_of_notMem hk, hpre, measure_empty]
    rw [hslice, lintegral_indicator_const hs (ν t), mul_comm]

/-- Deterministic map building $(W, W')$ from $(I, (X, X'))$ (`SteinIntro.tex:1054-1058`). -/
private noncomputable def pairStat {n : ℕ}
    (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) : ℝ × ℝ :=
  let w := (∑ i : Fin n, q.2.1 i) / Real.sqrt n
  (w, w - q.2.1 q.1 / Real.sqrt n + q.2.2 q.1 / Real.sqrt n)

private lemma measurable_pairStat {n : ℕ} : Measurable (@pairStat n) := by
  have hsum : Measurable (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦
      ∑ i : Fin n, q.2.1 i) :=
    Finset.measurable_sum Finset.univ fun i _ ↦
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hw : Measurable (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦
      (∑ i : Fin n, q.2.1 i) / Real.sqrt n) :=
    hsum.div_const (Real.sqrt n)
  have heval1 : Measurable (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦ q.2.1 q.1) := by
    have heq : (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦ q.2.1 q.1) =
        fun q ↦ ∑ i : Fin n, if q.1 = i then q.2.1 i else 0 := by
      funext q; simp
    rw [heq]
    refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
    have hset : {q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.1 = i} = Prod.fst ⁻¹' {i} := by
      ext q; simp
    exact Measurable.ite (hset ▸ measurable_fst (measurableSet_singleton i))
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurable_const
  have heval2 : Measurable (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦ q.2.2 q.1) := by
    have heq : (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦ q.2.2 q.1) =
        fun q ↦ ∑ i : Fin n, if q.1 = i then q.2.2 i else 0 := by
      funext q; simp
    rw [heq]
    refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
    have hset : {q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.1 = i} = Prod.fst ⁻¹' {i} := by
      ext q; simp
    exact Measurable.ite (hset ▸ measurable_fst (measurableSet_singleton i))
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) measurable_const
  exact hw.prodMk ((hw.sub (heval1.div_const (Real.sqrt n))).add
    (heval2.div_const (Real.sqrt n)))

private lemma pairStat_swapPair {n : ℕ} (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) :
    pairStat (swapPair q) = ((pairStat q).2, (pairStat q).1) := by
  have hsum : (∑ i : Fin n, (swapCoord q.1 q.2).1 i) =
      (∑ i : Fin n, q.2.1 i) + (q.2.2 q.1 - q.2.1 q.1) := by
    have hterm : ∀ i : Fin n,
        (swapCoord q.1 q.2).1 i = q.2.1 i + (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0) := by
      intro i
      by_cases h : q.1 = i
      · subst h; simp [swapCoord]
      · simp [swapCoord, h]
    calc
      (∑ i : Fin n, (swapCoord q.1 q.2).1 i)
          = ∑ i : Fin n, (q.2.1 i + (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0)) :=
            Finset.sum_congr rfl fun i _ ↦ hterm i
      _ = (∑ i : Fin n, q.2.1 i) +
            ∑ i : Fin n, (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0) :=
            Finset.sum_add_distrib
      _ = (∑ i : Fin n, q.2.1 i) + (q.2.2 q.1 - q.2.1 q.1) := by simp
  have hk1 : (swapCoord q.1 q.2).1 q.1 = q.2.2 q.1 := by simp [swapCoord]
  have hk2 : (swapCoord q.1 q.2).2 q.1 = q.2.1 q.1 := by simp [swapCoord]
  ext <;> dsimp [pairStat, swapPair] <;> rw [hsum]
  · ring
  · rw [hk1, hk2]; ring

/-- Pointwise uniform mass $P(I = k) = 1/n$ (`SteinIntro.tex:1056`). -/
private lemma measureReal_I_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn : 0 < n) {I : Ω → Fin n}
    (hI_meas : Measurable I)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (k : Fin n) :
    P.real {ω : Ω | I ω = k} = 1 / (n : ℝ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpre : {ω : Ω | I ω = k} = I ⁻¹' {k} := by ext ω; simp
  have hmeas : P {ω : Ω | I ω = k} = (n : ℝ≥0∞)⁻¹ := by
    rw [hpre, ← Measure.map_apply hI_meas (measurableSet_singleton k), hI_unif,
      PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [measureReal_def, hmeas, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- Independence factorization for an indicator $\mathbf{1}_{I = k}$ against a $(X, X')$-statistic
over an $X$-measurable event (Example 3.6, `SteinIntro.tex:1061-1082`). -/
lemma indepSum_setIntegral_indicator_I_vx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (k : Fin n) {T : Set (Fin n → ℝ)} (hT : MeasurableSet T)
    {H : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hH : Measurable H) :
    let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
    let VXX' : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)
    ∫ ω in VX ⁻¹' T, {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ H (VXX' ω')) ω ∂P =
      (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, H (VXX' ω) ∂P := by
  intro VX VXX'
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hVX'_meas : Measurable (fun ω i ↦ X' i ω) := .of_eval hX'_meas
  have hVXX'_meas : Measurable VXX' := hVX_meas.prodMk hVX'_meas
  let fI : Fin n → ℝ := ({k} : Set (Fin n)).indicator (fun _ ↦ (1 : ℝ))
  let gV : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := (Prod.fst ⁻¹' T).indicator H
  have hfI_meas : Measurable fI := measurable_const.indicator (measurableSet_singleton k)
  have hgV_meas : Measurable gV := hH.indicator (measurable_fst hT)
  have hIk_meas : MeasurableSet {ω : Ω | I ω = k} := by
    have hpre : {ω : Ω | I ω = k} = I ⁻¹' {k} := by ext ω; simp
    exact hpre ▸ hI_meas (measurableSet_singleton k)
  have hpt :
      (VX ⁻¹' T).indicator ({ω' : Ω | I ω' = k}.indicator (fun ω' ↦ H (VXX' ω'))) =
        fun ω ↦ fI (I ω) * gV (VXX' ω) := by
    funext ω
    by_cases hTω : VX ω ∈ T <;> by_cases hIω : I ω = k <;> simp [fI, gV, VXX', VX, hTω, hIω]
  have hfI_comp : (fun ω ↦ fI (I ω)) = {ω : Ω | I ω = k}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω; by_cases hIω : I ω = k <;> simp [fI, hIω]
  have hgV_comp : (fun ω ↦ gV (VXX' ω)) = (VX ⁻¹' T).indicator (fun ω ↦ H (VXX' ω)) := by
    funext ω; by_cases hTω : VX ω ∈ T <;> simp [gV, VXX', VX, hTω]
  rw [← integral_indicator (hVX_meas hT), hpt,
    hI_indep.integral_fun_comp_mul_comp hI_meas.aemeasurable hVXX'_meas.aemeasurable
      hfI_meas.stronglyMeasurable.aestronglyMeasurable
      hgV_meas.stronglyMeasurable.aestronglyMeasurable,
    hfI_comp, integral_indicator_const (1 : ℝ) hIk_meas, smul_eq_mul, mul_one,
    measureReal_I_eq P hn hI_meas hI_unif k, hgV_comp, integral_indicator (hVX_meas hT)]

/-- Independence factorization for $\varphi(X)\,\psi(X')$ over an $X$-measurable event
(Example 3.6, `SteinIntro.tex:1061-1082`). -/
lemma indepSum_setIntegral_vx_mul_vx'
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} {X X' : Fin n → Ω → ℝ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    {T : Set (Fin n → ℝ)} (hT : MeasurableSet T)
    {φ ψ : (Fin n → ℝ) → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
    let VX' : Ω → Fin n → ℝ := fun ω i ↦ X' i ω
    ∫ ω in VX ⁻¹' T, φ (VX ω) * ψ (VX' ω) ∂P =
      (∫ ω in VX ⁻¹' T, φ (VX ω) ∂P) * ∫ ω, ψ (VX' ω) ∂P := by
  intro VX VX'
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hVX'_meas : Measurable VX' := .of_eval hX'_meas
  let φT : (Fin n → ℝ) → ℝ := T.indicator φ
  have hφT_meas : Measurable φT := hφ.indicator hT
  have hpt :
      (VX ⁻¹' T).indicator (fun ω ↦ φ (VX ω) * ψ (VX' ω)) = fun ω ↦ φT (VX ω) * ψ (VX' ω) := by
    funext ω; by_cases hTω : VX ω ∈ T <;> simp [φT, hTω]
  have hφT_comp : (fun ω ↦ φT (VX ω)) = (VX ⁻¹' T).indicator (fun ω ↦ φ (VX ω)) := by
    funext ω; by_cases hTω : VX ω ∈ T <;> simp [φT, hTω]
  rw [← integral_indicator (hVX_meas hT), hpt,
    (hXX'_indep.symm).integral_fun_comp_mul_comp hVX_meas.aemeasurable hVX'_meas.aemeasurable
      hφT_meas.stronglyMeasurable.aestronglyMeasurable
      hψ.stronglyMeasurable.aestronglyMeasurable,
    hφT_comp, integral_indicator (hVX_meas hT)]

end Helpers

/-- Example 3.6, Stein-pair verification (`SteinIntro.tex:1053-1069`): for independent centered
unit-variance random variables $X_1, \dots, X_n$ with $\mathbb{E}[X_i^4] < \infty$, an independent
copy $(X_1', \dots, X_n')$, and an independent uniform random index $I \in \{1, \dots, n\}$,
$(W, W')$ with $W = n^{-1/2} \sum_{i=1}^n X_i$ and $W' = W - X_I / \sqrt{n} + X_I' / \sqrt{n}$ is a
$(1/n)$-Stein pair. -/
theorem indepSum_replaceOne_isSteinPair
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (_hX_var : ∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω / Real.sqrt n + X' (I ω) ω / Real.sqrt n
    IsSteinPair P (1 / (n : ℝ)) W W' := by
  intro W W'
  let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  let VX' : Ω → Fin n → ℝ := fun ω i ↦ X' i ω
  let VXX' : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω ↦ (VX ω, VX' ω)
  let J : Ω → Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) := fun ω ↦ (I ω, VXX' ω)
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hVX'_meas : Measurable VX' := .of_eval hX'_meas
  have hVXX'_meas : Measurable VXX' := hVX_meas.prodMk hVX'_meas
  have hJ_meas : Measurable J := hI_meas.prodMk hVXX'_meas
  -- 1. Exchangeability `(W, W') =_d (W', W)`.
  have hMapVX : P.map VX = Measure.pi (fun i ↦ P.map (X i)) :=
    ProbabilityTheory.iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX_meas i).aemeasurable) h_indep
  have hMapVXX' :
      P.map VXX' = (Measure.pi (fun i ↦ P.map (X i))).prod (Measure.pi (fun i ↦ P.map (X i))) := by
    rw [ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
      hVX_meas.aemeasurable hVX'_meas.aemeasurable hXX'_indep.symm, hId.map_eq, hMapVX]
  have hSwapVXX' : ∀ k : Fin n, MeasurePreserving (swapCoord k) (P.map VXX') (P.map VXX') := by
    intro k
    rw [hMapVXX']
    exact measurePreserving_swapCoord k (fun i ↦ P.map (X i))
  have hMP_swapPair : MeasurePreserving swapPair (P.map J) (P.map J) := by
    have hMapJ : P.map J = (P.map I).prod (P.map VXX') :=
      ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
        hI_meas.aemeasurable hVXX'_meas.aemeasurable hI_indep
    rw [hMapJ]
    exact measurePreserving_swapPair (P.map I) (P.map VXX') hSwapVXX'
  have hWW'_meas : Measurable (fun ω ↦ (W ω, W' ω)) := measurable_pairStat.comp hJ_meas
  have hW'W_meas : Measurable (fun ω ↦ (W' ω, W ω)) := measurable_swap.comp hWW'_meas
  have hExch : IsExchangeablePair P W W' := by
    refine ⟨hWW'_meas.aemeasurable, hW'W_meas.aemeasurable, ?_⟩
    calc
      P.map (fun ω ↦ (W ω, W' ω))
          = P.map (pairStat ∘ J) := rfl
      _ = (P.map J).map pairStat := (Measure.map_map measurable_pairStat hJ_meas).symm
      _ = ((P.map J).map swapPair).map pairStat := by rw [hMP_swapPair.map_eq]
      _ = (P.map (swapPair ∘ J)).map pairStat := by
            rw [Measure.map_map measurable_swapPair hJ_meas]
      _ = P.map (pairStat ∘ (swapPair ∘ J)) :=
            Measure.map_map measurable_pairStat (measurable_swapPair.comp hJ_meas)
      _ = P.map (fun ω ↦ (W' ω, W ω)) :=
            congrArg (fun f ↦ P.map f) (funext fun ω ↦ pairStat_swapPair (J ω))
  -- 2. Parameter range, measurability, and integrability.
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have ha_pos : 0 < 1 / (n : ℝ) := div_pos zero_lt_one hrn_pos
  have ha_le1 : 1 / (n : ℝ) ≤ 1 := div_le_one_of_le₀ hrn_ge1 hrn_pos.le
  have hW_meas : Measurable W :=
    (Finset.measurable_sum Finset.univ fun i _ ↦ hX_meas i).div_const (Real.sqrt n)
  have hX_int : ∀ i : Fin n, Integrable (X i) P :=
    fun i ↦ (hX4 i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hX'_int : ∀ i : Fin n, Integrable (X' i) P := by
    intro i
    have hId_i : IdentDistrib (X' i) (X i) P P := hId.comp (measurable_pi_apply i)
    exact (hId_i.memLp_iff.mpr (hX4 i)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hW_int : Integrable W P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ hX_int i).div_const (Real.sqrt n)
  have hW'_int : Integrable W' P := (hExch.fst_identDistrib_snd).integrable_snd hW_int
  -- 3. Linear conditional expectation `P[W' | comap W] =ᵐ[P] (1 - 1/n) * W`.
  have hmW := hW_meas.comap_le
  have hW_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] W :=
    Measurable.stronglyMeasurable (comap_measurable (m := inferInstance) W)
  have hIk_meas : ∀ k : Fin n, MeasurableSet {ω : Ω | I ω = k} := by
    intro k
    have hpre : {ω : Ω | I ω = k} = I ⁻¹' {k} := by ext ω; simp
    exact hpre ▸ hI_meas (measurableSet_singleton k)
  have hDiff_decomp :
      (fun ω ↦ W' ω - W ω) =
        fun ω ↦ ∑ k : Fin n,
          {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') / Real.sqrt n) ω := by
    funext ω
    have hsum :
        (∑ k : Fin n,
            {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') / Real.sqrt n) ω) =
          (X' (I ω) ω - X (I ω) ω) / Real.sqrt n := by
      have hterm : ∀ k : Fin n,
          {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') / Real.sqrt n) ω =
            if I ω = k then (X' k ω - X k ω) / Real.sqrt n else 0 := by
        intro k
        by_cases hk : I ω = k <;> simp [hk]
      simp_rw [hterm]
      simp
    rw [hsum]
    dsimp [W']
    ring
  have hCondDiff :
      (fun ω ↦ -(1 / (n : ℝ)) * W ω) =ᵐ[P]
        P[fun ω ↦ W' ω - W ω | MeasurableSpace.comap W inferInstance] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hmW (hW'_int.sub' hW_int)
      (fun s _ _ ↦ (hW_int.const_mul (-(1 / (n : ℝ)))).integrableOn)
      (fun s hs _ ↦ ?_)
      (hW_sm.const_mul (-(1 / (n : ℝ)))).aestronglyMeasurable
    rcases hs with ⟨B, hB, rfl⟩
    let sumScale : (Fin n → ℝ) → ℝ := fun v ↦ (∑ i : Fin n, v i) / Real.sqrt n
    have hsumScale_meas : Measurable sumScale :=
      (Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i).div_const (Real.sqrt n)
    let T : Set (Fin n → ℝ) := sumScale ⁻¹' B
    have hT : MeasurableSet T := hsumScale_meas hB
    have hpre : W ⁻¹' B = VX ⁻¹' T := rfl
    rw [hpre, hDiff_decomp,
      integral_finsetSum Finset.univ fun k _ ↦
        ((((hX'_int k).sub' (hX_int k)).div_const (Real.sqrt n)).indicator
          (hIk_meas k)).integrableOn]
    have hterm_eq : ∀ k : Fin n,
        ∫ ω in VX ⁻¹' T,
            {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') / Real.sqrt n) ω ∂P =
          -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, X k ω / Real.sqrt n ∂P := by
      intro k
      let Hk : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦ (p.2 k - p.1 k) / Real.sqrt n
      have hHk_meas : Measurable Hk := by
        have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 k) :=
          (measurable_pi_apply k).comp measurable_snd
        have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 k) :=
          (measurable_pi_apply k).comp measurable_fst
        exact (h1.sub h2).div_const (Real.sqrt n)
      have hStep1 :=
        indepSum_setIntegral_indicator_I_vx P hn hX_meas hX'_meas hI_meas hI_indep hI_unif k hT
          hHk_meas
      have hX'0 : ∫ ω, X' k ω ∂P = 0 :=
        (hId.comp (measurable_pi_apply k)).integral_eq.trans (hX0 k)
      have hIntX' : ∫ ω in VX ⁻¹' T, X' k ω ∂P = 0 := by
        have hmul :=
          indepSum_setIntegral_vx_mul_vx' P hX_meas hX'_meas hXX'_indep hT
            (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ (1 : ℝ)))
            (measurable_pi_apply k)
        simpa only [one_mul, hX'0, mul_zero] using hmul
      have hSub :
          ∫ ω in VX ⁻¹' T, Hk (VXX' ω) ∂P = -∫ ω in VX ⁻¹' T, X k ω / Real.sqrt n ∂P := by
        have hfn :
            (fun ω ↦ Hk (VXX' ω)) =
              fun ω ↦ X' k ω / Real.sqrt n - X k ω / Real.sqrt n := by
          funext ω; dsimp [Hk, VXX', VX, VX']; ring
        rw [hfn,
          integral_sub ((hX'_int k).div_const (Real.sqrt n)).integrableOn
            ((hX_int k).div_const (Real.sqrt n)).integrableOn,
          integral_div (Real.sqrt n) (X' k), hIntX', zero_div, zero_sub]
      calc
        ∫ ω in VX ⁻¹' T,
            {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') / Real.sqrt n) ω ∂P
            = (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, Hk (VXX' ω) ∂P := hStep1
        _ = -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, X k ω / Real.sqrt n ∂P := by
            rw [hSub]; ring
    have hW_split :
        (fun ω ↦ W ω) = fun ω ↦ ∑ k : Fin n, X k ω / Real.sqrt n := by
      funext ω; dsimp [W]; rw [Finset.sum_div]
    calc
      ∫ ω in VX ⁻¹' T, -(1 / (n : ℝ)) * W ω ∂P
          = -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, W ω ∂P :=
            integral_const_mul (-(1 / (n : ℝ))) W
      _ = -(1 / (n : ℝ)) * ∑ k : Fin n, ∫ ω in VX ⁻¹' T, X k ω / Real.sqrt n ∂P := by
            rw [hW_split,
              integral_finsetSum Finset.univ fun k _ ↦
                ((hX_int k).div_const (Real.sqrt n)).integrableOn]
      _ = ∑ k : Fin n, -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, X k ω / Real.sqrt n ∂P := by
            rw [Finset.mul_sum]
      _ = ∑ k : Fin n,
            ∫ ω in VX ⁻¹' T,
              {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') / Real.sqrt n) ω ∂P :=
            Finset.sum_congr rfl fun k _ ↦ (hterm_eq k).symm
  have hCondW : P[W | MeasurableSpace.comap W inferInstance] = W :=
    condExp_of_stronglyMeasurable hmW hW_sm hW_int
  have hSubAE :
      P[fun ω ↦ W' ω - W ω | MeasurableSpace.comap W inferInstance] =ᵐ[P]
        P[W' | MeasurableSpace.comap W inferInstance] -
          P[W | MeasurableSpace.comap W inferInstance] :=
    condExp_sub hW'_int hW_int (MeasurableSpace.comap W inferInstance)
  have hCond :
      P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - 1 / (n : ℝ)) * W ω := by
    filter_upwards [hCondDiff.symm, hSubAE] with ω hω1 hω2
    have hω : P[W' | MeasurableSpace.comap W inferInstance] ω - W ω = -(1 / (n : ℝ)) * W ω := by
      have hsub := hω2.symm.trans hω1
      rwa [Pi.sub_apply, hCondW] at hsub
    linarith
  exact ⟨hExch, ha_pos, ha_le1, hW_meas, hW_int, hCond⟩

/-- Example 3.6, unit second moment $\mathbb{E}[W^2] = 1$ (`SteinIntro.tex:1054`). -/
theorem indepSum_replaceOne_integral_W_sq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_var : ∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) :
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    ∫ ω, W ω ^ 2 ∂P = 1 := by
  intro W
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hX2 : ∀ i : Fin n, MemLp (X i) 2 P :=
    fun i ↦ (hX4 i).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)
  have hX_int : ∀ i : Fin n, Integrable (X i) P :=
    fun i ↦ (hX2 i).integrable one_le_two
  have hW_meas : Measurable W :=
    (Finset.measurable_sum Finset.univ fun i _ ↦ hX_meas i).div_const (Real.sqrt n)
  have hW0 : ∫ ω, W ω ∂P = 0 := by
    dsimp [W]
    rw [integral_div, integral_finsetSum Finset.univ fun i _ ↦ hX_int i]
    simp [hX0]
  have hVarSum : ProbabilityTheory.variance (∑ i : Fin n, X i) P = (n : ℝ) := by
    rw [ProbabilityTheory.IndepFun.variance_sum (fun i _ ↦ hX2 i)
      (fun i _ j _ hij ↦ h_indep.indepFun hij)]
    simp [hX_var]
  have hW_eq : W = fun ω ↦ (Real.sqrt n)⁻¹ * (∑ i : Fin n, X i) ω := by
    funext ω; simp [W, div_eq_mul_inv, mul_comm]
  calc
    ∫ ω, W ω ^ 2 ∂P = ProbabilityTheory.variance W P :=
      (ProbabilityTheory.variance_of_integral_eq_zero hW_meas.aemeasurable hW0).symm
    _ = ((Real.sqrt n)⁻¹) ^ 2 * ProbabilityTheory.variance (∑ i : Fin n, X i) P := by
      rw [hW_eq, ProbabilityTheory.variance_const_mul]
    _ = ((Real.sqrt n) ^ 2)⁻¹ * (n : ℝ) := by rw [inv_pow, hVarSum]
    _ = 1 := by rw [Real.sq_sqrt hrn_pos.le, inv_mul_cancel₀ hrn_pos.ne']

end SteinMethod
