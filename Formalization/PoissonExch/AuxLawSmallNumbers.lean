/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.PoissonExch.Thm420
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Example 4.20: Replace-One Bernoulli Coupling & Law of Small Numbers (`AuxLawSmallNumbers`)

Sorry-free formalization of Example 4.20 (`SteinIntro.tex:2663-2680`) and Critic item `H3`
(`docs/reviews/stmts-review-05H.md`):
* `bernoulli_replaceOne_coupling` (`Ex4_20_coupling`, `SteinIntro.tex:2664-2671`): for independent
  $\{0, 1\}$-valued indicators $X_1, \dots, X_n$ with $\mathbb{P}(X_i = 1) = p_i$, an independent
  copy $(X_1', \dots, X_n')$, and an independent uniform index $I \in \mathrm{Fin}\, n$ ($n > 0$),
  $(W, W')$ with $W = \sum_i X_i$ and $W' = W - X_I + X_I'$ is an exchangeable pair and satisfies
  $$\mathbb{P}(W' = W + 1 \mid (X_i)) = \frac{1}{n} \sum_{i=1}^n (1 - X_i) p_i, \qquad
    \mathbb{P}(W = W' + 1 \mid (X_i)) = \frac{1}{n} \sum_{i=1}^n X_i (1 - p_i)$$
  almost surely;
* `aux_tvDist_indep_bernoulli_sum_poissonLaw_le` (`Ex4_20`, `SteinIntro.tex:2663-2680`): constructs
  $(X', I)$ on `Fin n × (Ω × Ω)` and applies Theorem 4.20 with $c = n$ to obtain
  $$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
    2 \min\{1, \lambda^{-1/2}\} \sum_{i=1}^n p_i^2.$$
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SteinMethod

section Helpers

private abbrev PairVec (n : ℕ) := (Fin n → ℕ) × (Fin n → ℕ)
private abbrev IdxPairVec (n : ℕ) := Fin n × PairVec n

/-- Swaps the $k$-th coordinate between two `Fin n → ℕ` tuples (`SteinIntro.tex:2664-2667`). -/
private def swapCoordNat {n : ℕ} (k : Fin n) (uv : PairVec n) : PairVec n :=
  (fun i ↦ if k = i then uv.2 i else uv.1 i, fun i ↦ if k = i then uv.1 i else uv.2 i)

/-- Coordinatewise swap bundled with the random index $k \in \mathrm{Fin}\, n$. -/
private def swapPairNat {n : ℕ} (q : IdxPairVec n) : IdxPairVec n :=
  (q.1, swapCoordNat q.1 q.2)

private lemma measurable_swapPairNat {n : ℕ} : Measurable (@swapPairNat n) := by
  refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
  · refine Measurable.of_eval fun i ↦ ?_
    have hset : {q : IdxPairVec n | q.1 = i} = Prod.fst ⁻¹' {i} := by ext q; simp
    exact Measurable.ite (hset ▸ measurable_fst (measurableSet_singleton i))
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  · refine Measurable.of_eval fun i ↦ ?_
    have hset : {q : IdxPairVec n | q.1 = i} = Prod.fst ⁻¹' {i} := by ext q; simp
    exact Measurable.ite (hset ▸ measurable_fst (measurableSet_singleton i))
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))

private lemma measurePreserving_swapCoordNat {n : ℕ} (k : Fin n) (μ : Fin n → Measure ℕ)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (swapCoordNat k)
      ((Measure.pi μ).prod (Measure.pi μ))
      ((Measure.pi μ).prod (Measure.pi μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℕ ℕ (Fin n)
  have he : MeasurePreserving e
      (Measure.pi fun i ↦ (μ i).prod (μ i))
      ((Measure.pi μ).prod (Measure.pi μ)) :=
    measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin n) μ μ
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
  have he_apply : (e : (Fin n → ℕ × ℕ) → PairVec n) =
      fun a ↦ (fun i ↦ (a i).1, fun i ↦ (a i).2) := rfl
  have he_symm : (e.symm : PairVec n → Fin n → ℕ × ℕ) =
      fun p i ↦ (p.1 i, p.2 i) := rfl
  have heq :
      swapCoordNat k = (e ∘ fun a i ↦ (if k = i then Prod.swap else id) (a i)) ∘ e.symm := by
    rw [he_apply, he_symm]
    funext p
    apply Prod.ext <;> funext i <;> by_cases hk : k = i <;> simp [swapCoordNat, hk]
  rwa [← heq] at hcomp

private lemma measurePreserving_swapPairNat {n : ℕ}
    (μI : Measure (Fin n)) [SigmaFinite μI]
    (ν : Measure (PairVec n)) [SigmaFinite ν]
    (hSwap : ∀ k : Fin n, MeasurePreserving (swapCoordNat k) ν ν) :
    MeasurePreserving swapPairNat (μI.prod ν) (μI.prod ν) where
  measurable := measurable_swapPairNat
  map_eq := by
    refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [Measure.map_apply measurable_swapPairNat (hs.prod ht),
      Measure.prod_apply (measurable_swapPairNat (hs.prod ht))]
    have hslice :
        (fun k : Fin n ↦ ν (Prod.mk k ⁻¹' (swapPairNat ⁻¹' (s ×ˢ t)))) =
          s.indicator (fun _ ↦ ν t) := by
      funext k
      by_cases hk : k ∈ s
      · have hpre :
            Prod.mk k ⁻¹' (swapPairNat ⁻¹' (s ×ˢ t)) = swapCoordNat k ⁻¹' t := by
          ext p; simp [swapPairNat, hk]
        rw [Set.indicator_of_mem hk, hpre, ← Measure.map_apply (hSwap k).measurable ht,
          (hSwap k).map_eq]
      · have hpre : Prod.mk k ⁻¹' (swapPairNat ⁻¹' (s ×ˢ t)) = ∅ := by
          ext p; simp [swapPairNat, hk]
        rw [Set.indicator_of_notMem hk, hpre, measure_empty]
    rw [hslice, lintegral_indicator_const hs (ν t), mul_comm]

/-- Deterministic map building $(W, W')$ from $(I, (X, X'))$ on `ℕ`. -/
private def pairStatNat {n : ℕ} (q : IdxPairVec n) : ℕ × ℕ :=
  let w := ∑ i : Fin n, q.2.1 i
  (w, w - q.2.1 q.1 + q.2.2 q.1)

private lemma measurable_eval_idxNat {α : Type*} [MeasurableSpace α] {n : ℕ}
    {f : α → Fin n} {g : α → Fin n → ℕ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a ↦ g a (f a)) := by
  have heq : (fun a ↦ g a (f a)) = fun a ↦ ∑ i : Fin n, if f a = i then g a i else 0 := by
    funext a; simp
  rw [heq]
  refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
  have hset : {a : α | f a = i} = f ⁻¹' {i} := by ext a; simp
  exact Measurable.ite (hset ▸ hf (measurableSet_singleton i))
    ((measurable_pi_apply i).comp hg) measurable_const

private lemma measurable_pairStatNat {n : ℕ} : Measurable (@pairStatNat n) := by
  have hsum : Measurable (fun q : IdxPairVec n ↦ ∑ i : Fin n, q.2.1 i) :=
    Finset.measurable_sum Finset.univ fun i _ ↦
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have he1 :=
    measurable_eval_idxNat (α := IdxPairVec n) measurable_fst (measurable_fst.comp measurable_snd)
  have he2 :=
    measurable_eval_idxNat (α := IdxPairVec n) measurable_fst (measurable_snd.comp measurable_snd)
  exact hsum.prodMk ((hsum.sub he1).add he2)

private lemma pairStatNat_swapPairNat {n : ℕ} (q : IdxPairVec n) :
    pairStatNat (swapPairNat q) = ((pairStatNat q).2, (pairStatNat q).1) := by
  let k := q.1
  let u := q.2.1
  let v := q.2.2
  have hu_split : (∑ i : Fin n, u i) = (∑ i ∈ Finset.univ.erase k, u i) + u k :=
    (Finset.sum_erase_add Finset.univ u (Finset.mem_univ k)).symm
  have hswap_erase : ∀ i ∈ Finset.univ.erase k, (swapCoordNat k (u, v)).1 i = u i := by
    intro i hi
    have hne : k ≠ i := (Finset.ne_of_mem_erase hi).symm
    simp [swapCoordNat, hne]
  have hu'_split :
      (∑ i : Fin n, (swapCoordNat k (u, v)).1 i) =
        (∑ i ∈ Finset.univ.erase k, u i) + v k := by
    rw [← Finset.sum_erase_add Finset.univ (swapCoordNat k (u, v)).1 (Finset.mem_univ k),
      Finset.sum_congr rfl hswap_erase]
    simp [swapCoordNat]
  have hk1 : (swapCoordNat k (u, v)).1 k = v k := by simp [swapCoordNat]
  have hk2 : (swapCoordNat k (u, v)).2 k = u k := by simp [swapCoordNat]
  ext <;> dsimp [pairStatNat, swapPairNat]
  · change (∑ i : Fin n, (swapCoordNat k (u, v)).1 i) = (∑ i : Fin n, u i) - u k + v k
    rw [hu'_split, hu_split, Nat.add_sub_cancel]
  · change (∑ i : Fin n, (swapCoordNat k (u, v)).1 i) -
        (swapCoordNat k (u, v)).1 k + (swapCoordNat k (u, v)).2 k = ∑ i : Fin n, u i
    rw [hu'_split, hk1, hk2, Nat.add_sub_cancel, ← hu_split]

private lemma measureReal_I_eq_one_div
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn : 0 < n) {I : Ω → Fin n}
    (hI_meas : Measurable I)
    (hI_unif : P.map I =
      (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (k : Fin n) :
    P.real {ω : Ω | I ω = k} = 1 / (n : ℝ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpre : {ω : Ω | I ω = k} = I ⁻¹' {k} := by ext ω; simp
  have hmeas : P {ω : Ω | I ω = k} = (n : ℝ≥0∞)⁻¹ := by
    rw [hpre, ← Measure.map_apply hI_meas (measurableSet_singleton k), hI_unif,
      PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [measureReal_def, hmeas, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- Independence factorization for $\mathbf{1}_{I = k} H(X, X')$ over an $X$-measurable event. -/
private lemma setIntegral_indicator_I_vxNat
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℕ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (hI_meas : Measurable I)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I =
      (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (k : Fin n) {T : Set (Fin n → ℕ)} (hT : MeasurableSet T)
    {H : PairVec n → ℝ} (hH : Measurable H) :
    let VX : Ω → Fin n → ℕ := fun ω i ↦ X i ω
    let VXX' : Ω → PairVec n := fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)
    ∫ ω in VX ⁻¹' T, {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ H (VXX' ω')) ω ∂P =
      (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, H (VXX' ω) ∂P := by
  intro VX VXX'
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hVX'_meas : Measurable (fun ω i ↦ X' i ω) := .of_eval hX'_meas
  have hVXX'_meas : Measurable VXX' := hVX_meas.prodMk hVX'_meas
  let fI : Fin n → ℝ := ({k} : Set (Fin n)).indicator (fun _ ↦ (1 : ℝ))
  let gV : PairVec n → ℝ := (Prod.fst ⁻¹' T).indicator H
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
  have hfI_comp :
      (fun ω ↦ fI (I ω)) = {ω : Ω | I ω = k}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext ω; by_cases hIω : I ω = k <;> simp [fI, hIω]
  have hgV_comp : (fun ω ↦ gV (VXX' ω)) = (VX ⁻¹' T).indicator (fun ω ↦ H (VXX' ω)) := by
    funext ω; by_cases hTω : VX ω ∈ T <;> simp [gV, VXX', VX, hTω]
  rw [← integral_indicator (hVX_meas hT), hpt,
    hI_indep.integral_fun_comp_mul_comp hI_meas.aemeasurable hVXX'_meas.aemeasurable
      hfI_meas.stronglyMeasurable.aestronglyMeasurable
      hgV_meas.stronglyMeasurable.aestronglyMeasurable,
    hfI_comp, integral_indicator_const (1 : ℝ) hIk_meas, smul_eq_mul, mul_one,
    measureReal_I_eq_one_div P hn hI_meas hI_unif k, hgV_comp, integral_indicator (hVX_meas hT)]

/-- Independence factorization for $\varphi(X)\,\psi(X')$ over an $X$-measurable event. -/
private lemma setIntegral_vxNat_mul_vx'Nat
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {n : ℕ} {X X' : Fin n → Ω → ℕ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (hXX'_indep : IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    {T : Set (Fin n → ℕ)} (hT : MeasurableSet T)
    {φ ψ : (Fin n → ℕ) → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    let VX : Ω → Fin n → ℕ := fun ω i ↦ X i ω
    let VX' : Ω → Fin n → ℕ := fun ω i ↦ X' i ω
    ∫ ω in VX ⁻¹' T, φ (VX ω) * ψ (VX' ω) ∂P =
      (∫ ω in VX ⁻¹' T, φ (VX ω) ∂P) * ∫ ω, ψ (VX' ω) ∂P := by
  intro VX VX'
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hVX'_meas : Measurable VX' := .of_eval hX'_meas
  let φT : (Fin n → ℕ) → ℝ := T.indicator φ
  have hφT_meas : Measurable φT := hφ.indicator hT
  have hpt :
      (VX ⁻¹' T).indicator (fun ω ↦ φ (VX ω) * ψ (VX' ω)) =
        fun ω ↦ φT (VX ω) * ψ (VX' ω) := by
    funext ω; by_cases hTω : VX ω ∈ T <;> simp [φT, hTω]
  have hφT_comp : (fun ω ↦ φT (VX ω)) = (VX ⁻¹' T).indicator (fun ω ↦ φ (VX ω)) := by
    funext ω; by_cases hTω : VX ω ∈ T <;> simp [φT, hTω]
  rw [← integral_indicator (hVX_meas hT), hpt,
    (hXX'_indep.symm).integral_fun_comp_mul_comp hVX_meas.aemeasurable hVX'_meas.aemeasurable
      hφT_meas.stronglyMeasurable.aestronglyMeasurable
      hψ.stronglyMeasurable.aestronglyMeasurable,
    hφT_comp, integral_indicator (hVX_meas hT)]

private lemma integral_bernoulli_nat_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℕ}
    (hY_meas : Measurable Y) (hY_01 : ∀ ω, Y ω = 0 ∨ Y ω = 1) :
    Integrable (fun ω ↦ (Y ω : ℝ)) P ∧
      ∫ ω, (Y ω : ℝ) ∂P = P.real {ω | Y ω = 1} := by
  have hS : MeasurableSet {ω : Ω | Y ω = 1} := hY_meas (measurableSet_singleton 1)
  have heq : (fun ω : Ω ↦ (Y ω : ℝ)) = {ω : Ω | Y ω = 1}.indicator (1 : Ω → ℝ) := by
    funext ω
    rcases hY_01 ω with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [heq]
  exact ⟨(integrable_const (1 : ℝ)).indicator hS, integral_indicator_one hS⟩

private lemma sum_indicator_I_eq {Ω : Type*} {n : ℕ} (I : Ω → Fin n)
    (f : Fin n → Ω → ℝ) (ω : Ω) :
    (∑ k : Fin n, {ω' : Ω | I ω' = k}.indicator (f k) ω) = f (I ω) ω := by
  have hterm : ∀ k : Fin n,
      {ω' : Ω | I ω' = k}.indicator (f k) ω = if I ω = k then f k ω else 0 := by
    intro k; by_cases hk : I ω = k <;> simp [hk]
  simp_rw [hterm]
  simp

/-- Conditional expectation given $\sigma(X)$ of an event decomposing along $\{I = k\}$ into
products $\varphi_k(X_k)\,\psi_k(X_k')$ for $\{0, 1\}$-valued coordinates. -/
private lemma condExp_indicator_eq_of_sum_I
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℕ} {I : Ω → Fin n}
    (hval : ∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1)
    (hval' : ∀ᵐ ω ∂P, ∀ i : Fin n, X' i ω = 0 ∨ X' i ω = 1)
    (hm : ∀ i, Measurable (X i))
    (hm' : ∀ i, Measurable (X' i))
    (hXX'_indep : IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I =
      (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    {S : Set Ω} (hS : MeasurableSet S)
    (φ ψ : Fin n → ℕ → ℝ) (q : Fin n → ℝ)
    (hq : ∀ k, ∫ ω, ψ k (X' k ω) ∂P = q k)
    (hae : S.indicator (1 : Ω → ℝ) =ᵐ[P]
      fun ω ↦ ∑ k : Fin n,
        {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ φ k (X k ω') * ψ k (X' k ω')) ω) :
    P[S.indicator (1 : Ω → ℝ) |
        MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
      fun ω ↦ (1 / (n : ℝ)) * ∑ k : Fin n, φ k (X k ω) * q k := by
  let VX : Ω → Fin n → ℕ := fun ω i ↦ X i ω
  have hVX_meas : Measurable VX := .of_eval hm
  have hIk_meas : ∀ k : Fin n, MeasurableSet {ω : Ω | I ω = k} := by
    intro k
    have hpre : {ω : Ω | I ω = k} = I ⁻¹' {k} := by ext ω; simp
    exact hpre ▸ hI_meas (measurableSet_singleton k)
  have hφ_int : ∀ k : Fin n, Integrable (fun ω ↦ φ k (X k ω)) P := by
    intro k
    refine Integrable.of_bound
      ((Measurable.of_discrete (f := φ k)).comp (hm k)).aestronglyMeasurable
      (max |φ k 0| |φ k 1|) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    rcases hval k ω with h0 | h1
    · rw [h0]; exact le_max_left _ _
    · rw [h1]; exact le_max_right _ _
  have hprod_int : ∀ k : Fin n,
      Integrable (fun ω ↦ φ k (X k ω) * ψ k (X' k ω)) P := by
    intro k
    have hψ_top : MemLp (fun ω ↦ ψ k (X' k ω)) ⊤ P := by
      refine memLp_top_of_bound
        ((Measurable.of_discrete (f := ψ k)).comp (hm' k)).aestronglyMeasurable
        (max |ψ k 0| |ψ k 1|) (hval'.mono fun ω hω ↦ ?_)
      rw [Real.norm_eq_abs]
      rcases hω k with h0 | h1
      · rw [h0]; exact le_max_left _ _
      · rw [h1]; exact le_max_right _ _
    exact (hφ_int k).mul_of_top_left hψ_top
  let g : Ω → ℝ := fun ω ↦ (1 / (n : ℝ)) * ∑ k : Fin n, φ k (X k ω) * q k
  have hg_sm : StronglyMeasurable[MeasurableSpace.comap VX inferInstance] g := by
    let G : (Fin n → ℕ) → ℝ := fun v ↦ (1 / (n : ℝ)) * ∑ k : Fin n, φ k (v k) * q k
    have hG : Measurable G :=
      (Finset.measurable_sum Finset.univ fun k _ ↦
        ((Measurable.of_discrete (f := φ k)).comp (measurable_pi_apply k)).mul measurable_const)
        |>.const_mul (1 / (n : ℝ))
    exact (hG.comp (comap_measurable (m := inferInstance) VX)).stronglyMeasurable
  have hg_int : Integrable g P :=
    (integrable_finsetSum Finset.univ fun k _ ↦
      (hφ_int k).mul_const (q k)).const_mul (1 / (n : ℝ))
  refine (ae_eq_condExp_of_forall_setIntegral_eq hVX_meas.comap_le
    ((integrable_const (1 : ℝ)).indicator hS)
    (fun _ _ _ ↦ hg_int.integrableOn)
    (fun s hs _ ↦ ?_)
    hg_sm.aestronglyMeasurable).symm
  rcases hs with ⟨T, hT, rfl⟩
  have hterm : ∀ k : Fin n,
      ∫ ω in VX ⁻¹' T,
          {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ φ k (X k ω') * ψ k (X' k ω')) ω ∂P =
        (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, φ k (X k ω) * q k ∂P := by
    intro k
    let Hk : PairVec n → ℝ := fun uv ↦ φ k (uv.1 k) * ψ k (uv.2 k)
    have hHk : Measurable Hk :=
      ((Measurable.of_discrete (f := φ k)).comp ((measurable_pi_apply k).comp measurable_fst)).mul
        ((Measurable.of_discrete (f := ψ k)).comp ((measurable_pi_apply k).comp measurable_snd))
    rw [setIntegral_indicator_I_vxNat P hn hm hm' hI_meas hI_indep hI_unif k hT hHk]
    have hfac :
        ∫ ω in VX ⁻¹' T, φ k (X k ω) * ψ k (X' k ω) ∂P =
          (∫ ω in VX ⁻¹' T, φ k (X k ω) ∂P) * ∫ ω, ψ k (X' k ω) ∂P :=
      setIntegral_vxNat_mul_vx'Nat P hm hm' hXX'_indep hT
        (φ := fun v ↦ φ k (v k)) (ψ := fun v ↦ ψ k (v k))
        ((Measurable.of_discrete (f := φ k)).comp (measurable_pi_apply k))
        ((Measurable.of_discrete (f := ψ k)).comp (measurable_pi_apply k))
    rw [show (∫ ω in VX ⁻¹' T, Hk (VX ω, fun i ↦ X' i ω) ∂P) =
        ∫ ω in VX ⁻¹' T, φ k (X k ω) * ψ k (X' k ω) ∂P from rfl,
      hfac, hq k, ← integral_mul_const]
  calc
    ∫ ω in VX ⁻¹' T, g ω ∂P
        = (1 / (n : ℝ)) * ∑ k : Fin n, ∫ ω in VX ⁻¹' T, φ k (X k ω) * q k ∂P := by
          dsimp [g]
          rw [integral_const_mul,
            integral_finsetSum Finset.univ fun k _ ↦ ((hφ_int k).mul_const (q k)).integrableOn]
    _ = ∑ k : Fin n, (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, φ k (X k ω) * q k ∂P := by
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n,
          ∫ ω in VX ⁻¹' T,
            {ω' : Ω | I ω' = k}.indicator
              (fun ω' ↦ φ k (X k ω') * ψ k (X' k ω')) ω ∂P :=
          Finset.sum_congr rfl fun k _ ↦ (hterm k).symm
    _ = ∫ ω in VX ⁻¹' T, S.indicator (1 : Ω → ℝ) ω ∂P := by
          rw [← integral_finsetSum Finset.univ fun k _ ↦
            ((hprod_int k).indicator (hIk_meas k)).integrableOn]
          exact setIntegral_congr_ae (hVX_meas hT) (hae.symm.mono fun ω hω _ ↦ hω)

end Helpers

/-- **Example 4.20 coupling and conditional jump probabilities** (`Ex4_20_coupling`, `H3`,
`SteinIntro.tex:2664-2671`):
for independent $\{0, 1\}$-valued indicators $X_1, \dots, X_n$ with $\mathbb{P}(X_i = 1) = p_i$,
an independent copy $(X_1', \dots, X_n')$ with the same joint law, and an independent uniform
random index $I \in \mathrm{Fin}\, n$ ($n > 0$), if $W = \sum_{i=1}^n X_i$ and
$W' = W - X_I + X_I'$, then $(W, W')$ is an exchangeable pair and
$$\mathbb{P}(W' = W + 1 \mid (X_i)) = \frac{1}{n} \sum_{i=1}^n (1 - X_i) p_i, \qquad
  \mathbb{P}(W = W' + 1 \mid (X_i)) = \frac{1}{n} \sum_{i=1}^n X_i (1 - p_i)$$
almost surely. -/
theorem bernoulli_replaceOne_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    {X X' : Fin n → Ω → ℕ} {p : Fin n → ℝ} {I : Ω → Fin n}
    (hval : ∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1)
    (hm : ∀ i, Measurable (X i))
    (hm' : ∀ i, Measurable (X' i))
    (hp : ∀ i, P.real {ω | X i ω = 1} = p i)
    (hind : iIndepFun X P)
    (hId : IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I =
      (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let W' : Ω → ℕ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    IsExchangeablePair P W W' ∧
      P[{ω | W' ω = W ω + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
        (fun ω ↦ (1 / (n : ℝ)) * ∑ i : Fin n, (1 - (X i ω : ℝ)) * p i) ∧
      P[{ω | W ω = W' ω + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
        (fun ω ↦ (1 / (n : ℝ)) * ∑ i : Fin n, (X i ω : ℝ) * (1 - p i)) := by
  intro W W'
  let VX : Ω → Fin n → ℕ := fun ω i ↦ X i ω
  let VX' : Ω → Fin n → ℕ := fun ω i ↦ X' i ω
  let VXX' : Ω → PairVec n := fun ω ↦ (VX ω, VX' ω)
  let J : Ω → IdxPairVec n := fun ω ↦ (I ω, VXX' ω)
  have hVX_meas : Measurable VX := .of_eval hm
  have hVX'_meas : Measurable VX' := .of_eval hm'
  have hVXX'_meas : Measurable VXX' := hVX_meas.prodMk hVX'_meas
  have hJ_meas : Measurable J := hI_meas.prodMk hVXX'_meas
  -- 1. Exchangeability `(W, W') =_d (W', W)`.
  have hMapVX : P.map VX = Measure.pi (fun i ↦ P.map (X i)) :=
    iIndepFun.map_fun_eq_pi_map (fun i ↦ (hm i).aemeasurable) hind
  have hMapVXX' :
      P.map VXX' =
        (Measure.pi (fun i ↦ P.map (X i))).prod (Measure.pi (fun i ↦ P.map (X i))) := by
    rw [IndepFun.map_prod_eq_prod_map_map
      hVX_meas.aemeasurable hVX'_meas.aemeasurable hXX'_indep.symm, hId.map_eq, hMapVX]
  have hSwapVXX' : ∀ k : Fin n, MeasurePreserving (swapCoordNat k) (P.map VXX') (P.map VXX') := by
    intro k; rw [hMapVXX']; exact measurePreserving_swapCoordNat k (fun i ↦ P.map (X i))
  have hMP_swapPair : MeasurePreserving swapPairNat (P.map J) (P.map J) := by
    have hMapJ : P.map J = (P.map I).prod (P.map VXX') :=
      IndepFun.map_prod_eq_prod_map_map hI_meas.aemeasurable hVXX'_meas.aemeasurable hI_indep
    rw [hMapJ]; exact measurePreserving_swapPairNat (P.map I) (P.map VXX') hSwapVXX'
  have hWW'_meas : Measurable (fun ω ↦ (W ω, W' ω)) := measurable_pairStatNat.comp hJ_meas
  have hW'W_meas : Measurable (fun ω ↦ (W' ω, W ω)) := measurable_swap.comp hWW'_meas
  have hExch : IsExchangeablePair P W W' := by
    refine ⟨hWW'_meas.aemeasurable, hW'W_meas.aemeasurable, ?_⟩
    calc
      P.map (fun ω ↦ (W ω, W' ω))
          = P.map (pairStatNat ∘ J) := rfl
      _ = (P.map J).map pairStatNat := (Measure.map_map measurable_pairStatNat hJ_meas).symm
      _ = ((P.map J).map swapPairNat).map pairStatNat := by rw [hMP_swapPair.map_eq]
      _ = (P.map (swapPairNat ∘ J)).map pairStatNat := by
            rw [Measure.map_map measurable_swapPairNat hJ_meas]
      _ = P.map (pairStatNat ∘ (swapPairNat ∘ J)) :=
            Measure.map_map measurable_pairStatNat (measurable_swapPairNat.comp hJ_meas)
      _ = P.map (fun ω ↦ (W' ω, W ω)) :=
            congrArg (fun f ↦ P.map f) (funext fun ω ↦ pairStatNat_swapPairNat (J ω))
  -- 2. Almost-sure `{0, 1}` range of `X'` and conditional jump probabilities.
  have hval'_i : ∀ i : Fin n, ∀ᵐ ω ∂P, X' i ω = 0 ∨ X' i ω = 1 := by
    intro i
    have hId_i : IdentDistrib (X' i) (X i) P P := hId.comp (measurable_pi_apply i)
    let bad : Set ℕ := {k : ℕ | ¬ (k = 0 ∨ k = 1)}
    have hbad_meas : MeasurableSet bad := MeasurableSet.of_discrete
    have hX_empty : X i ⁻¹' bad = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun ω hω ↦ hω (hval i ω)
    have hP_zero : P (X' i ⁻¹' bad) = 0 := by
      rw [← Measure.map_apply (hm' i) hbad_meas, hId_i.map_eq,
        Measure.map_apply (hm i) hbad_meas, hX_empty, measure_empty]
    exact ae_iff.mpr hP_zero
  have hval' : ∀ᵐ ω ∂P, ∀ i : Fin n, X' i ω = 0 ∨ X' i ω = 1 := ae_all_iff.mpr hval'_i
  have hW_meas : Measurable W := Finset.measurable_sum Finset.univ fun i _ ↦ hm i
  have hW'_meas : Measurable W' := (measurable_snd.comp measurable_pairStatNat).comp hJ_meas
  let S_up : Set Ω := {ω | W' ω = W ω + 1}
  let S_down : Set Ω := {ω | W ω = W' ω + 1}
  have hSup_meas : MeasurableSet S_up :=
    (hW_meas.prodMk hW'_meas) (MeasurableSet.of_discrete (s := {ab : ℕ × ℕ | ab.2 = ab.1 + 1}))
  have hSdown_meas : MeasurableSet S_down :=
    (hW'_meas.prodMk hW_meas) (MeasurableSet.of_discrete (s := {ab : ℕ × ℕ | ab.2 = ab.1 + 1}))
  have hX'_int_eq : ∀ k : Fin n,
      Integrable (fun ω ↦ (X' k ω : ℝ)) P ∧ ∫ ω, (X' k ω : ℝ) ∂P = p k := by
    intro k
    obtain ⟨hint, heq⟩ := integral_bernoulli_nat_eq P (hm k) (hval k)
    have hId_k : IdentDistrib (fun ω ↦ (X' k ω : ℝ)) (fun ω ↦ (X k ω : ℝ)) P P :=
      (hId.comp (measurable_pi_apply k)).comp (Measurable.of_discrete (f := Nat.cast))
    exact ⟨hId_k.symm.integrable_snd hint, hId_k.integral_eq.trans (heq.trans (hp k))⟩
  have hW_split : ∀ ω, W ω = (∑ i ∈ Finset.univ.erase (I ω), X i ω) + X (I ω) ω :=
    fun ω ↦ (Finset.sum_erase_add Finset.univ (fun i ↦ X i ω) (Finset.mem_univ (I ω))).symm
  have hW'_split : ∀ ω, W' ω = (∑ i ∈ Finset.univ.erase (I ω), X i ω) + X' (I ω) ω := by
    intro ω; dsimp [W']; rw [hW_split ω, Nat.add_sub_cancel]
  have hup_ae :
      S_up.indicator (1 : Ω → ℝ) =ᵐ[P]
        fun ω ↦ ∑ k : Fin n,
          {ω' : Ω | I ω' = k}.indicator
            (fun ω' ↦ (1 - (X k ω' : ℝ)) * (X' k ω' : ℝ)) ω := by
    filter_upwards [hval'] with ω hω'
    rw [sum_indicator_I_eq I (fun k ω' ↦ (1 - (X k ω' : ℝ)) * (X' k ω' : ℝ)) ω]
    rcases hval (I ω) ω with hX0 | hX1 <;> rcases hω' (I ω) with hX'0 | hX'1
    · have hne : ω ∉ S_up := by simp [S_up, hW_split ω, hW'_split ω, hX0, hX'0]
      simp [Set.indicator_of_notMem hne, hX0, hX'0]
    · have hmem : ω ∈ S_up := by simp [S_up, hW_split ω, hW'_split ω, hX0, hX'1]
      simp [Set.indicator_of_mem hmem, hX0, hX'1]
    · have hne : ω ∉ S_up := by
        change ¬ (W' ω = W ω + 1); rw [hW_split ω, hW'_split ω, hX1, hX'0]; omega
      simp [Set.indicator_of_notMem hne, hX1, hX'0]
    · have hne : ω ∉ S_up := by
        change ¬ (W' ω = W ω + 1); rw [hW_split ω, hW'_split ω, hX1, hX'1]; omega
      simp [Set.indicator_of_notMem hne, hX1, hX'1]
  have hdown_ae :
      S_down.indicator (1 : Ω → ℝ) =ᵐ[P]
        fun ω ↦ ∑ k : Fin n,
          {ω' : Ω | I ω' = k}.indicator
            (fun ω' ↦ (X k ω' : ℝ) * (1 - (X' k ω' : ℝ))) ω := by
    filter_upwards [hval'] with ω hω'
    rw [sum_indicator_I_eq I (fun k ω' ↦ (X k ω' : ℝ) * (1 - (X' k ω' : ℝ))) ω]
    rcases hval (I ω) ω with hX0 | hX1 <;> rcases hω' (I ω) with hX'0 | hX'1
    · have hne : ω ∉ S_down := by simp [S_down, hW_split ω, hW'_split ω, hX0, hX'0]
      simp [Set.indicator_of_notMem hne, hX0, hX'0]
    · have hne : ω ∉ S_down := by
        change ¬ (W ω = W' ω + 1); rw [hW_split ω, hW'_split ω, hX0, hX'1]; omega
      simp [Set.indicator_of_notMem hne, hX0, hX'1]
    · have hmem : ω ∈ S_down := by simp [S_down, hW_split ω, hW'_split ω, hX1, hX'0]
      simp [Set.indicator_of_mem hmem, hX1, hX'0]
    · have hne : ω ∉ S_down := by
        change ¬ (W ω = W' ω + 1); rw [hW_split ω, hW'_split ω, hX1, hX'1]; omega
      simp [Set.indicator_of_notMem hne, hX1, hX'1]
  have hCond_up :=
    condExp_indicator_eq_of_sum_I P hn hval hval' hm hm' hXX'_indep hI_meas hI_indep hI_unif
      hSup_meas (fun _ a ↦ 1 - (a : ℝ)) (fun _ b ↦ (b : ℝ)) p
      (fun k ↦ (hX'_int_eq k).2) hup_ae
  have hCond_down :=
    condExp_indicator_eq_of_sum_I P hn hval hval' hm hm' hXX'_indep hI_meas hI_indep hI_unif
      hSdown_meas (fun _ a ↦ (a : ℝ)) (fun _ b ↦ 1 - (b : ℝ)) (fun k ↦ 1 - p k)
      (fun k ↦ by
        rw [integral_sub (integrable_const (1 : ℝ)) (hX'_int_eq k).1, integral_const,
          measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, (hX'_int_eq k).2])
      hdown_ae
  exact ⟨hExch, hCond_up, hCond_down⟩

/-- Variant of `bernoulli_replaceOne_coupling` taking coordinatewise `iIndepFun X' P` and
`∀ i, IdentDistrib (X' i) (X i) P P`. -/
theorem bernoulli_replaceOne_coupling_of_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    {X X' : Fin n → Ω → ℕ} {p : Fin n → ℝ} {I : Ω → Fin n}
    (hval : ∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1)
    (hm : ∀ i, Measurable (X i))
    (hm' : ∀ i, Measurable (X' i))
    (hp : ∀ i, P.real {ω | X i ω = 1} = p i)
    (hind : iIndepFun X P)
    (hind' : iIndepFun X' P)
    (hId_i : ∀ i, IdentDistrib (X' i) (X i) P P)
    (hXX'_indep : IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I =
      (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let W' : Ω → ℕ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    IsExchangeablePair P W W' ∧
      P[{ω | W' ω = W ω + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
        (fun ω ↦ (1 / (n : ℝ)) * ∑ i : Fin n, (1 - (X i ω : ℝ)) * p i) ∧
      P[{ω | W ω = W' ω + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
        (fun ω ↦ (1 / (n : ℝ)) * ∑ i : Fin n, (X i ω : ℝ) * (1 - p i)) := by
  have hId : IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P := by
    refine ⟨(Measurable.of_eval hm').aemeasurable, (Measurable.of_eval hm).aemeasurable, ?_⟩
    rw [iIndepFun.map_fun_eq_pi_map (fun i ↦ (hm' i).aemeasurable) hind',
      iIndepFun.map_fun_eq_pi_map (fun i ↦ (hm i).aemeasurable) hind]
    exact congrArg Measure.pi (funext fun i ↦ (hId_i i).map_eq)
  exact bernoulli_replaceOne_coupling P hn hval hm hm' hp hind hId hXX'_indep hI_meas hI_indep
    hI_unif

/-- **Example 4.20: Law of Small Numbers via Exchangeable Pairs** (`Ex4_20`,
`SteinIntro.tex:2663-2680`):
for independent $\{0, 1\}$-valued indicators $X_1, \dots, X_n$ with $\mathbb{P}(X_i = 1) = p_i$,
$W = \sum_{i=1}^n X_i$, and $\lambda = \sum_{i=1}^n p_i > 0$,
$$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
  2 \min\{1, \lambda^{-1/2}\} \sum_{i=1}^n p_i^2.$$ -/
theorem aux_tvDist_indep_bernoulli_sum_poissonLaw_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℕ} {p : Fin n → ℝ}
    (hval : ∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1)
    (hm : ∀ i, Measurable (X i))
    (hp : ∀ i, P.real {ω | X i ω = 1} = p i)
    (hpb : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hind : iIndepFun X P)
    {r : ℝ≥0} (hr : 0 < r) (hlam : (r : ℝ) = ∑ i : Fin n, p i) :
    tvDist (P.map (fun ω ↦ ∑ i : Fin n, X i ω)) (poissonLaw r) ≤
      ENNReal.ofReal (2 * min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) * ∑ i : Fin n, p i ^ 2) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Ωe := Fin n × (Ω × Ω)
  let μI : Measure (Fin n) := (PMF.uniformOfFintype (Fin n)).toMeasure
  let Q : Measure Ωe := μI.prod (P.prod P)
  let π₁ : Ωe → Ω := fun q ↦ q.2.1
  let π₂ : Ωe → Ω := fun q ↦ q.2.2
  let I_ext : Ωe → Fin n := Prod.fst
  let X_ext : Fin n → Ωe → ℕ := fun i q ↦ X i (π₁ q)
  let X'_ext : Fin n → Ωe → ℕ := fun i q ↦ X i (π₂ q)
  let VX : Ω → Fin n → ℕ := fun ω i ↦ X i ω
  let VX_ext : Ωe → Fin n → ℕ := fun q i ↦ X_ext i q
  let W_ext : Ωe → ℕ := fun q ↦ ∑ i : Fin n, X_ext i q
  let W'_ext : Ωe → ℕ := fun q ↦ W_ext q - X_ext (I_ext q) q + X'_ext (I_ext q) q
  have hVX_meas : Measurable VX := .of_eval hm
  have hmp_snd : MeasurePreserving (Prod.snd : Ωe → Ω × Ω) Q (P.prod P) :=
    MeasureTheory.measurePreserving_snd
  have hmp_I : MeasurePreserving I_ext Q μI := MeasureTheory.measurePreserving_fst
  have hmp₁ : MeasurePreserving π₁ Q P := MeasureTheory.measurePreserving_fst.comp hmp_snd
  have hmp₂ : MeasurePreserving π₂ Q P := MeasureTheory.measurePreserving_snd.comp hmp_snd
  have hm_ext : ∀ i : Fin n, Measurable (X_ext i) := fun i ↦ (hm i).comp hmp₁.measurable
  have hm'_ext : ∀ i : Fin n, Measurable (X'_ext i) := fun i ↦ (hm i).comp hmp₂.measurable
  have hval_ext : ∀ i, ∀ q, X_ext i q = 0 ∨ X_ext i q = 1 := fun i q ↦ hval i (π₁ q)
  have hp_ext : ∀ i, Q.real {q | X_ext i q = 1} = p i := by
    intro i
    have hpre : {q : Ωe | X_ext i q = 1} = π₁ ⁻¹' {ω : Ω | X i ω = 1} := rfl
    have hmeas : MeasurableSet {ω : Ω | X i ω = 1} := hm i (measurableSet_singleton 1)
    rw [hpre, measureReal_def, hmp₁.measure_preimage hmeas.nullMeasurableSet,
      ← measureReal_def, hp i]
  have hind_ext : iIndepFun X_ext Q := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hpre_inter :
        (⋂ i ∈ S, X_ext i ⁻¹' sets i) = π₁ ⁻¹' (⋂ i ∈ S, X i ⁻¹' sets i) := by
      ext q; simp [X_ext]
    have hmeas_inter : MeasurableSet (⋂ i ∈ S, X i ⁻¹' sets i) :=
      MeasurableSet.biInter S.countable_toSet fun i hi ↦ hm i (hsets i hi)
    rw [hpre_inter, hmp₁.measure_preimage hmeas_inter.nullMeasurableSet,
      (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hind) S hsets]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    exact (hmp₁.measure_preimage (hm i (hsets i hi)).nullMeasurableSet).symm
  have hVX_ext_map : Q.map VX_ext = P.map VX := by
    change Q.map (VX ∘ π₁) = P.map VX
    rw [← Measure.map_map hVX_meas hmp₁.measurable, hmp₁.map_eq]
  have hVX'_ext_map : Q.map (fun q i ↦ X'_ext i q) = P.map VX := by
    change Q.map (VX ∘ π₂) = P.map VX
    rw [← Measure.map_map hVX_meas hmp₂.measurable, hmp₂.map_eq]
  have hId_ext : IdentDistrib (fun q i ↦ X'_ext i q) VX_ext Q Q :=
    ⟨(Measurable.of_eval hm'_ext).aemeasurable, (Measurable.of_eval hm_ext).aemeasurable,
      hVX'_ext_map.trans hVX_ext_map.symm⟩
  have hXX'_indep_ext : IndepFun (fun q i ↦ X'_ext i q) VX_ext Q := by
    refine (indepFun_iff_map_prod_eq_prod_map_map
      (Measurable.of_eval hm'_ext).aemeasurable
      (Measurable.of_eval hm_ext).aemeasurable).mpr ?_
    have hcomp :
        (fun q : Ωe ↦ (fun i ↦ X'_ext i q, VX_ext q)) =
          (Prod.map VX VX) ∘ Prod.swap ∘ Prod.snd := rfl
    rw [hcomp, ← Measure.map_map (hVX_meas.prodMap hVX_meas)
      (measurable_swap.comp measurable_snd),
      ← Measure.map_map measurable_swap measurable_snd,
      hmp_snd.map_eq, Measure.prod_swap, ← Measure.map_prod_map P P hVX_meas hVX_meas]
    exact congrArg₂ Measure.prod hVX'_ext_map.symm hVX_ext_map.symm
  have hI_indep_ext :
      IndepFun I_ext (fun q ↦ (VX_ext q, fun i ↦ X'_ext i q)) Q := by
    have hpair_meas : Measurable (fun q : Ωe ↦ (VX_ext q, fun i ↦ X'_ext i q)) :=
      (Measurable.of_eval hm_ext).prodMk (Measurable.of_eval hm'_ext)
    refine (indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable hpair_meas.aemeasurable).mpr ?_
    have hVXX'_map :
        Q.map (fun q ↦ (VX_ext q, fun i ↦ X'_ext i q)) =
          (P.prod P).map (Prod.map VX VX) := by
      change Q.map ((Prod.map VX VX) ∘ Prod.snd) = (P.prod P).map (Prod.map VX VX)
      rw [← Measure.map_map (hVX_meas.prodMap hVX_meas) measurable_snd, hmp_snd.map_eq]
    have hcomp :
        (fun q : Ωe ↦ (I_ext q, (VX_ext q, fun i ↦ X'_ext i q))) =
          Prod.map id (Prod.map VX VX) := rfl
    rw [hcomp, ← Measure.map_prod_map μI (P.prod P) measurable_id (hVX_meas.prodMap hVX_meas),
      Measure.map_id, ← hmp_I.map_eq, ← hVXX'_map]
  obtain ⟨hExch, hCond_up, hCond_down⟩ :=
    bernoulli_replaceOne_coupling Q hn hval_ext hm_ext hm'_ext hp_ext hind_ext hId_ext
      hXX'_indep_ext measurable_fst hI_indep_ext hmp_I.map_eq
  -- Apply Theorem 4.20 on `(Ωe, Q)` with `F = comap VX_ext` and `c = n`.
  have hVX_ext_meas : Measurable VX_ext := .of_eval hm_ext
  have hFle := hVX_ext_meas.comap_le
  have hW_ext_meas : Measurable W_ext := Finset.measurable_sum Finset.univ fun i _ ↦ hm_ext i
  have hW'_ext_meas : Measurable W'_ext := by
    have hJ : Measurable (fun q : Ωe ↦ (I_ext q, (VX_ext q, fun i ↦ X'_ext i q))) :=
      measurable_fst.prodMk (hVX_ext_meas.prodMk (.of_eval hm'_ext))
    exact (measurable_snd.comp measurable_pairStatNat).comp hJ
  have hWF :
      MeasurableSpace.comap W_ext inferInstance ≤ MeasurableSpace.comap VX_ext inferInstance := by
    have hsum_meas : Measurable (fun v : Fin n → ℕ ↦ ∑ i : Fin n, v i) :=
      Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i
    have hcomp : W_ext = (fun v : Fin n → ℕ ↦ ∑ i : Fin n, v i) ∘ VX_ext := rfl
    rw [hcomp, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hsum_meas.comap_le
  have hW_map_eq : Q.map W_ext = P.map (fun ω ↦ ∑ i : Fin n, X i ω) := by
    have hW_orig_meas : Measurable (fun ω ↦ ∑ i : Fin n, X i ω) :=
      Finset.measurable_sum Finset.univ fun i _ ↦ hm i
    have hcomp : W_ext = (fun ω ↦ ∑ i : Fin n, X i ω) ∘ π₁ := rfl
    rw [hcomp, ← Measure.map_map hW_orig_meas hmp₁.measurable, hmp₁.map_eq]
  have hthm :=
    tvDist_poissonLaw_exchangeable_le Q hr hW_ext_meas hW'_ext_meas hExch hFle hWF (n : ℝ)
  rw [hW_map_eq] at hthm
  -- Evaluate both conditional expectation error terms with `c = n`.
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let S_pX : Ωe → ℝ := fun q ↦ ∑ i : Fin n, p i * (X_ext i q : ℝ)
  have hS_pX_nn : ∀ q, 0 ≤ S_pX q := fun q ↦
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hpb i).1 (Nat.cast_nonneg _)
  have hX_ext_int : ∀ i : Fin n,
      Integrable (fun q ↦ (X_ext i q : ℝ)) Q ∧ ∫ q, (X_ext i q : ℝ) ∂Q = p i := by
    intro i
    obtain ⟨hint, heq⟩ := integral_bernoulli_nat_eq Q (hm_ext i) (hval_ext i)
    exact ⟨hint, heq.trans (hp_ext i)⟩
  have hS_pX_int : Integrable S_pX Q :=
    integrable_finsetSum Finset.univ fun i _ ↦ ((hX_ext_int i).1).const_mul (p i)
  have hS_pX_integral : ∫ q, S_pX q ∂Q = ∑ i : Fin n, p i ^ 2 := by
    dsimp [S_pX]
    rw [integral_finsetSum Finset.univ fun i _ ↦ ((hX_ext_int i).1).const_mul (p i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, (hX_ext_int i).2, sq]
  have hS_pX_lintegral :
      (∫⁻ q, ENNReal.ofReal (S_pX q) ∂Q) = ENNReal.ofReal (∑ i : Fin n, p i ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hS_pX_int (ae_of_all _ hS_pX_nn), hS_pX_integral]
  let ind_up : Ωe → ℝ := {q' | W'_ext q' = W_ext q' + 1}.indicator (1 : Ωe → ℝ)
  let ind_dn : Ωe → ℝ := {q' | W_ext q' = W'_ext q' + 1}.indicator (1 : Ωe → ℝ)
  let cexp : (Ωe → ℝ) → Ωe → ℝ :=
    condExpAt (MeasurableSpace.comap VX_ext inferInstance) inferInstance Q
  have herr₁ :
      (∫⁻ q, ENNReal.ofReal |(r : ℝ) - (n : ℝ) * cexp ind_up q| ∂Q) =
        ENNReal.ofReal (∑ i : Fin n, p i ^ 2) := by
    have hae :
        (fun q ↦ ENNReal.ofReal |(r : ℝ) - (n : ℝ) * cexp ind_up q|) =ᵐ[Q]
          fun q ↦ ENNReal.ofReal (S_pX q) := by
      filter_upwards [hCond_up] with q hq
      change ENNReal.ofReal
          |(r : ℝ) - (n : ℝ) * Q[ind_up | MeasurableSpace.comap VX_ext inferInstance] q| =
        ENNReal.ofReal (S_pX q)
      rw [hq, hlam]
      have halg :
          (∑ i : Fin n, p i) -
              (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (1 - (X_ext i q : ℝ)) * p i) =
            S_pX q := by
        have hmul : (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (1 - (X_ext i q : ℝ)) * p i) =
            ∑ i : Fin n, (1 - (X_ext i q : ℝ)) * p i := by field_simp [hn_ne]
        rw [hmul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [halg, abs_of_nonneg (hS_pX_nn q)]
    rw [lintegral_congr_ae hae, hS_pX_lintegral]
  have herr₂ :
      (∫⁻ q, ENNReal.ofReal |(W_ext q : ℝ) - (n : ℝ) * cexp ind_dn q| ∂Q) =
        ENNReal.ofReal (∑ i : Fin n, p i ^ 2) := by
    have hae :
        (fun q ↦ ENNReal.ofReal |(W_ext q : ℝ) - (n : ℝ) * cexp ind_dn q|) =ᵐ[Q]
          fun q ↦ ENNReal.ofReal (S_pX q) := by
      filter_upwards [hCond_down] with q hq
      change ENNReal.ofReal
          |(W_ext q : ℝ) - (n : ℝ) * Q[ind_dn | MeasurableSpace.comap VX_ext inferInstance] q| =
        ENNReal.ofReal (S_pX q)
      rw [hq, show (W_ext q : ℝ) = ∑ i : Fin n, (X_ext i q : ℝ) from
        Nat.cast_sum Finset.univ fun i ↦ X_ext i q]
      have halg :
          (∑ i : Fin n, (X_ext i q : ℝ)) -
              (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (X_ext i q : ℝ) * (1 - p i)) =
            S_pX q := by
        have hmul : (n : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n, (X_ext i q : ℝ) * (1 - p i)) =
            ∑ i : Fin n, (X_ext i q : ℝ) * (1 - p i) := by field_simp [hn_ne]
        rw [hmul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [halg, abs_of_nonneg (hS_pX_nn q)]
    rw [lintegral_congr_ae hae, hS_pX_lintegral]
  -- Combine with `hthm`.
  have hsum_sq_nn : 0 ≤ ∑ i : Fin n, p i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg (p i)
  have hM_nn : 0 ≤ min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) :=
    le_min zero_le_one (Real.rpow_nonneg (by positivity) _)
  refine hthm.trans ?_
  change ENNReal.ofReal (min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))) *
      ((∫⁻ q, ENNReal.ofReal |(r : ℝ) - (n : ℝ) * cexp ind_up q| ∂Q) +
       (∫⁻ q, ENNReal.ofReal |(W_ext q : ℝ) - (n : ℝ) * cexp ind_dn q| ∂Q)) ≤ _
  rw [herr₁, herr₂, ← ENNReal.ofReal_add hsum_sq_nn hsum_sq_nn, ← ENNReal.ofReal_mul hM_nn]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith

end SteinMethod
