/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.Exchangeable
import Formalization.Exchangeable.IndepSumPair

/-!
# Unscaled Independent-Sum Stein Pair (`Formalization.Concentration.IndepSumPair`)

Develops the unscaled $(1/n)$-Stein pair and conditional squared-difference identity for
**Example 7.4** (`SteinIntro.tex:3497-3520`):

* `indepSum_unscaled_isSteinPair` (**Example 7.4** Stein-pair setup, `Ex7_4_steinPair`,
  `SteinIntro.tex:3497-3502`): for independent $X_1, \dots, X_n \in L^2(P)$ with means $\mu_i$, an
  independent copy $(X_1', \dots, X_n')$, and an independent uniform index $I \in \{1, \dots, n\}$,
  $W = \sum_{i=1}^n (X_i - \mu_i)$ and $W' = W - X_I + X_I'$ form a $(1/n)$-Stein pair.
* `indepSum_condExp_sq_diff`: conditional expectation identity
  $\mathbb{E}[(W' - W)^2 \mid (X_j)_j] =
  \frac{1}{n}\sum_{k=1}^n (\mathbb{E}[X_k^2] - 2\mu_k X_k + X_k^2)$.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

section Helpers

/-- Swaps only the $k$-th coordinate between two $n$-tuples (`SteinIntro.tex:3500-3501`). -/
private def swapCoord7 {n : ℕ} (k : Fin n) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i ↦ if k = i then p.2 i else p.1 i, fun i ↦ if k = i then p.1 i else p.2 i)

/-- Coordinatewise swap bundled with the random index $k \in \{1, \dots, n\}$
(`SteinIntro.tex:3500-3501`). -/
private def swapPair7 {n : ℕ} (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) :
    Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (q.1, swapCoord7 q.1 q.2)

private lemma measurable_swapPair7 {n : ℕ} : Measurable (@swapPair7 n) := by
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

private lemma measurePreserving_swapCoord7 {n : ℕ} (k : Fin n) (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (swapCoord7 k)
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
      swapCoord7 k = (e ∘ fun a i ↦ (if k = i then Prod.swap else id) (a i)) ∘ e.symm := by
    rw [he_apply, he_symm]
    funext p
    apply Prod.ext <;> funext i <;> by_cases hk : k = i <;> simp [swapCoord7, hk]
  rwa [← heq] at hcomp

private lemma measurePreserving_swapPair7 {n : ℕ}
    (μI : Measure (Fin n)) [SigmaFinite μI]
    (ν : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [SigmaFinite ν]
    (hSwap : ∀ k : Fin n, MeasurePreserving (swapCoord7 k) ν ν) :
    MeasurePreserving swapPair7 (μI.prod ν) (μI.prod ν) where
  measurable := measurable_swapPair7
  map_eq := by
    refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [Measure.map_apply measurable_swapPair7 (hs.prod ht),
      Measure.prod_apply (measurable_swapPair7 (hs.prod ht))]
    have hslice :
        (fun k : Fin n ↦ ν (Prod.mk k ⁻¹' (swapPair7 ⁻¹' (s ×ˢ t)))) =
          s.indicator (fun _ ↦ ν t) := by
      funext k
      by_cases hk : k ∈ s
      · have hpre : Prod.mk k ⁻¹' (swapPair7 ⁻¹' (s ×ˢ t)) = swapCoord7 k ⁻¹' t := by
          ext p; simp [swapPair7, hk]
        rw [Set.indicator_of_mem hk, hpre, ← Measure.map_apply (hSwap k).measurable ht,
          (hSwap k).map_eq]
      · have hpre : Prod.mk k ⁻¹' (swapPair7 ⁻¹' (s ×ˢ t)) = ∅ := by
          ext p; simp [swapPair7, hk]
        rw [Set.indicator_of_notMem hk, hpre, measure_empty]
    rw [hslice, lintegral_indicator_const hs (ν t), mul_comm]

/-- Deterministic map building unscaled $(W, W')$ from $(I, (X, X'))$
(`SteinIntro.tex:3499-3501`). -/
private def pairStatUnscaled {n : ℕ} (μ : Fin n → ℝ)
    (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) : ℝ × ℝ :=
  let w := ∑ i : Fin n, (q.2.1 i - μ i)
  (w, w - q.2.1 q.1 + q.2.2 q.1)

private lemma measurable_pairStatUnscaled {n : ℕ} (μ : Fin n → ℝ) :
    Measurable (pairStatUnscaled μ) := by
  have hw : Measurable (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦
      ∑ i : Fin n, (q.2.1 i - μ i)) :=
    Finset.measurable_sum Finset.univ fun i _ ↦
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).sub measurable_const
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
  exact hw.prodMk ((hw.sub heval1).add heval2)

private lemma pairStatUnscaled_swapPair7 {n : ℕ} (μ : Fin n → ℝ)
    (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) :
    pairStatUnscaled μ (swapPair7 q) =
      ((pairStatUnscaled μ q).2, (pairStatUnscaled μ q).1) := by
  have hsum : (∑ i : Fin n, ((swapCoord7 q.1 q.2).1 i - μ i)) =
      (∑ i : Fin n, (q.2.1 i - μ i)) + (q.2.2 q.1 - q.2.1 q.1) := by
    have hterm : ∀ i : Fin n,
        (swapCoord7 q.1 q.2).1 i - μ i =
          (q.2.1 i - μ i) + (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0) := by
      intro i
      by_cases h : q.1 = i
      · subst h; simp [swapCoord7]
      · simp [swapCoord7, h]
    calc
      (∑ i : Fin n, ((swapCoord7 q.1 q.2).1 i - μ i))
          = ∑ i : Fin n, ((q.2.1 i - μ i) + (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0)) :=
            Finset.sum_congr rfl fun i _ ↦ hterm i
      _ = (∑ i : Fin n, (q.2.1 i - μ i)) +
            ∑ i : Fin n, (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0) :=
            Finset.sum_add_distrib
      _ = (∑ i : Fin n, (q.2.1 i - μ i)) + (q.2.2 q.1 - q.2.1 q.1) := by simp
  have hk1 : (swapCoord7 q.1 q.2).1 q.1 = q.2.2 q.1 := by simp [swapCoord7]
  have hk2 : (swapCoord7 q.1 q.2).2 q.1 = q.2.1 q.1 := by simp [swapCoord7]
  ext <;> dsimp [pairStatUnscaled, swapPair7] <;> rw [hsum]
  · ring
  · rw [hk1, hk2]; ring

end Helpers

/-- **Example 7.4, Stein-pair setup** (`Ex7_4_steinPair`, `SteinIntro.tex:3497-3502`): for
independent $X_1, \dots, X_n \in L^2(P)$ with means $\mu_i = \mathbb{E}[X_i]$, an independent copy
$(X_1', \dots, X_n')$, and an independent uniform random index $I \in \{1, \dots, n\}$,
$W = \sum_{i=1}^n (X_i - \mu_i)$ and $W' = W - X_I + X_I'$ form a $(1/n)$-Stein pair. -/
theorem indepSum_unscaled_isSteinPair
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX2 : ∀ i : Fin n, MemLp (X i) 2 P)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω - ∫ ω', X i ω' ∂P)
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    IsSteinPair P (1 / (n : ℝ)) W W' := by
  intro W W'
  let μ : Fin n → ℝ := fun i ↦ ∫ ω', X i ω' ∂P
  let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  let VX' : Ω → Fin n → ℝ := fun ω i ↦ X' i ω
  let VXX' : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω ↦ (VX ω, VX' ω)
  let J : Ω → Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) := fun ω ↦ (I ω, VXX' ω)
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hVX'_meas : Measurable VX' := .of_eval hX'_meas
  have hVXX'_meas : Measurable VXX' := hVX_meas.prodMk hVX'_meas
  have hJ_meas : Measurable J := hI_meas.prodMk hVXX'_meas
  have hMapVX : P.map VX = Measure.pi (fun i ↦ P.map (X i)) :=
    ProbabilityTheory.iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX_meas i).aemeasurable) h_indep
  have hMapVXX' :
      P.map VXX' = (Measure.pi (fun i ↦ P.map (X i))).prod (Measure.pi (fun i ↦ P.map (X i))) := by
    rw [ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
      hVX_meas.aemeasurable hVX'_meas.aemeasurable hXX'_indep.symm, hId.map_eq, hMapVX]
  have hSwapVXX' : ∀ k : Fin n, MeasurePreserving (swapCoord7 k) (P.map VXX') (P.map VXX') := by
    intro k
    rw [hMapVXX']
    exact measurePreserving_swapCoord7 k (fun i ↦ P.map (X i))
  have hMP_swapPair : MeasurePreserving swapPair7 (P.map J) (P.map J) := by
    have hMapJ : P.map J = (P.map I).prod (P.map VXX') :=
      ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
        hI_meas.aemeasurable hVXX'_meas.aemeasurable hI_indep
    rw [hMapJ]
    exact measurePreserving_swapPair7 (P.map I) (P.map VXX') hSwapVXX'
  have hWW'_meas : Measurable (fun ω ↦ (W ω, W' ω)) :=
    (measurable_pairStatUnscaled μ).comp hJ_meas
  have hW'W_meas : Measurable (fun ω ↦ (W' ω, W ω)) := measurable_swap.comp hWW'_meas
  have hExch : IsExchangeablePair P W W' := by
    refine ⟨hWW'_meas.aemeasurable, hW'W_meas.aemeasurable, ?_⟩
    calc
      P.map (fun ω ↦ (W ω, W' ω))
          = P.map (pairStatUnscaled μ ∘ J) := rfl
      _ = (P.map J).map (pairStatUnscaled μ) :=
            (Measure.map_map (measurable_pairStatUnscaled μ) hJ_meas).symm
      _ = ((P.map J).map swapPair7).map (pairStatUnscaled μ) := by rw [hMP_swapPair.map_eq]
      _ = (P.map (swapPair7 ∘ J)).map (pairStatUnscaled μ) := by
            rw [Measure.map_map measurable_swapPair7 hJ_meas]
      _ = P.map (pairStatUnscaled μ ∘ (swapPair7 ∘ J)) :=
            Measure.map_map (measurable_pairStatUnscaled μ) (measurable_swapPair7.comp hJ_meas)
      _ = P.map (fun ω ↦ (W' ω, W ω)) :=
            congrArg (fun f ↦ P.map f) (funext fun ω ↦ pairStatUnscaled_swapPair7 μ (J ω))
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have ha_pos : 0 < 1 / (n : ℝ) := div_pos zero_lt_one hrn_pos
  have ha_le1 : 1 / (n : ℝ) ≤ 1 := div_le_one_of_le₀ hrn_ge1 hrn_pos.le
  have hW_meas : Measurable W :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hX_meas i).sub measurable_const
  have hX_int : ∀ i : Fin n, Integrable (X i) P :=
    fun i ↦ (hX2 i).integrable one_le_two
  have hX'_int : ∀ i : Fin n, Integrable (X' i) P := by
    intro i
    have hId_i : IdentDistrib (X' i) (X i) P P := hId.comp (measurable_pi_apply i)
    exact (hId_i.memLp_iff.mpr (hX2 i)).integrable one_le_two
  have hW_int : Integrable W P :=
    integrable_finsetSum Finset.univ fun i _ ↦ (hX_int i).sub (integrable_const (μ i))
  have hW'_int : Integrable W' P := (hExch.fst_identDistrib_snd).integrable_snd hW_int
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
          {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ X' k ω' - X k ω') ω := by
    funext ω
    have hsum :
        (∑ k : Fin n,
            {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ X' k ω' - X k ω') ω) =
          X' (I ω) ω - X (I ω) ω := by
      have hterm : ∀ k : Fin n,
          {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ X' k ω' - X k ω') ω =
            if I ω = k then X' k ω - X k ω else 0 := by
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
    let sumCtr : (Fin n → ℝ) → ℝ := fun v ↦ ∑ i : Fin n, (v i - μ i)
    have hsumCtr_meas : Measurable sumCtr :=
      Finset.measurable_sum Finset.univ fun i _ ↦ (measurable_pi_apply i).sub measurable_const
    let T : Set (Fin n → ℝ) := sumCtr ⁻¹' B
    have hT : MeasurableSet T := hsumCtr_meas hB
    have hpre : W ⁻¹' B = VX ⁻¹' T := rfl
    rw [hpre, hDiff_decomp,
      integral_finsetSum Finset.univ fun k _ ↦
        (((hX'_int k).sub' (hX_int k)).indicator (hIk_meas k)).integrableOn]
    have hterm_eq : ∀ k : Fin n,
        ∫ ω in VX ⁻¹' T,
            {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ X' k ω' - X k ω') ω ∂P =
          -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, (X k ω - μ k) ∂P := by
      intro k
      let Hk : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦ p.2 k - p.1 k
      have hHk_meas : Measurable Hk :=
        ((measurable_pi_apply k).comp measurable_snd).sub
          ((measurable_pi_apply k).comp measurable_fst)
      have hStep1 :=
        indepSum_setIntegral_indicator_I_vx P hn hX_meas hX'_meas hI_meas hI_indep hI_unif k hT
          hHk_meas
      have hX'_mean : ∫ ω, X' k ω ∂P = μ k :=
        (hId.comp (measurable_pi_apply k)).integral_eq
      have hIntX' : ∫ ω in VX ⁻¹' T, X' k ω ∂P = ∫ ω in VX ⁻¹' T, μ k ∂P := by
        have hmul :
            ∫ ω in VX ⁻¹' T, (1 : ℝ) * X' k ω ∂P =
              (∫ ω in VX ⁻¹' T, (1 : ℝ) ∂P) * ∫ ω, X' k ω ∂P :=
          indepSum_setIntegral_vx_mul_vx' P hX_meas hX'_meas hXX'_indep hT
            (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ (1 : ℝ)))
            (measurable_pi_apply k)
        simp only [one_mul, hX'_mean] at hmul
        rw [hmul, setIntegral_const, smul_eq_mul, mul_one, setIntegral_const, smul_eq_mul]
      have hSub :
          ∫ ω in VX ⁻¹' T, Hk (VXX' ω) ∂P = -∫ ω in VX ⁻¹' T, (X k ω - μ k) ∂P := by
        have hfn : (fun ω ↦ Hk (VXX' ω)) = fun ω ↦ X' k ω - X k ω := rfl
        rw [hfn, integral_sub (hX'_int k).integrableOn (hX_int k).integrableOn, hIntX',
          ← integral_sub (integrable_const (μ k)).integrableOn (hX_int k).integrableOn,
          ← integral_neg]
        refine setIntegral_congr_fun (hVX_meas hT) fun ω _ ↦ ?_
        ring
      calc
        ∫ ω in VX ⁻¹' T,
            {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ X' k ω' - X k ω') ω ∂P
            = (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, Hk (VXX' ω) ∂P := hStep1
        _ = -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, (X k ω - μ k) ∂P := by
            rw [hSub]; ring
    calc
      ∫ ω in VX ⁻¹' T, -(1 / (n : ℝ)) * W ω ∂P
          = -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, W ω ∂P :=
            integral_const_mul (-(1 / (n : ℝ))) W
      _ = -(1 / (n : ℝ)) * ∑ k : Fin n, ∫ ω in VX ⁻¹' T, (X k ω - μ k) ∂P := by
            have hW_eq : W = fun ω ↦ ∑ k : Fin n, (X k ω - μ k) := rfl
            have hterm_int : ∀ k : Fin n, IntegrableOn (fun ω ↦ X k ω - μ k) (VX ⁻¹' T) P :=
              fun k ↦ ((hX_int k).sub (integrable_const (μ k))).integrableOn
            rw [hW_eq, integral_finsetSum Finset.univ fun k _ ↦ hterm_int k]
      _ = ∑ k : Fin n, -(1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T, (X k ω - μ k) ∂P := by
            rw [Finset.mul_sum]
      _ = ∑ k : Fin n,
            ∫ ω in VX ⁻¹' T,
              {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ X' k ω' - X k ω') ω ∂P :=
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

/-- Conditional expectation identity $\mathbb{E}[(W' - W)^2 \mid (X_j)_j] =
\frac{1}{n}\sum_{k=1}^n (\mathbb{E}[X_k^2] - 2\mu_k X_k + X_k^2)$ used in both parts of Example 7.4
(`SteinIntro.tex:3506-3520`). -/
theorem indepSum_condExp_sq_diff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX'_meas : ∀ i : Fin n, Measurable (X' i))
    (hX2 : ∀ i : Fin n, MemLp (X i) 2 P)
    (hId : ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P)
    (hXX'_indep : ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P)
    (hI_unif : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω - ∫ ω', X i ω' ∂P)
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap VX inferInstance] =ᵐ[P]
      fun ω ↦ (1 / (n : ℝ)) * ∑ k : Fin n,
        ((∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * X k ω + X k ω ^ 2) := by
  intro VX W W'
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hmVX := hVX_meas.comap_le
  have hX_int : ∀ i : Fin n, Integrable (X i) P := fun i ↦ (hX2 i).integrable one_le_two
  have hX'_2 : ∀ i : Fin n, MemLp (X' i) 2 P := fun i ↦
    ((hId.comp (measurable_pi_apply i)).memLp_iff).mpr (hX2 i)
  have hX_sq_int : ∀ i : Fin n, Integrable (fun ω ↦ X i ω ^ 2) P :=
    fun i ↦ (hX2 i).integrable_sq
  have hX'_sq_int : ∀ i : Fin n, Integrable (fun ω ↦ X' i ω ^ 2) P :=
    fun i ↦ (hX'_2 i).integrable_sq
  have hXX'_mul_int : ∀ i : Fin n, Integrable (fun ω ↦ X i ω * X' i ω) P :=
    fun i ↦ (hX2 i).integrable_mul (hX'_2 i)
  have hSqDiff_int : ∀ k : Fin n, Integrable (fun ω ↦ (X' k ω - X k ω) ^ 2) P := by
    intro k
    have heq : (fun ω ↦ (X' k ω - X k ω) ^ 2) =
        fun ω ↦ X' k ω ^ 2 - 2 * (X k ω * X' k ω) + X k ω ^ 2 := by
      funext ω; ring
    rw [heq]
    exact ((hX'_sq_int k).sub ((hXX'_mul_int k).const_mul 2)).add (hX_sq_int k)
  have hIk_meas : ∀ k : Fin n, MeasurableSet {ω : Ω | I ω = k} := by
    intro k
    have hpre : {ω : Ω | I ω = k} = I ⁻¹' {k} := by ext ω; simp
    exact hpre ▸ hI_meas (measurableSet_singleton k)
  have hDecomp :
      (fun ω ↦ (W' ω - W ω) ^ 2) =
        fun ω ↦ ∑ k : Fin n,
          {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') ^ 2) ω := by
    funext ω
    have hterm : ∀ k : Fin n,
        {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') ^ 2) ω =
          if I ω = k then (X' k ω - X k ω) ^ 2 else 0 := by
      intro k
      by_cases hk : I ω = k <;> simp [hk]
    simp_rw [hterm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    dsimp [W']
    ring
  have hLHS_int : Integrable (fun ω ↦ (W' ω - W ω) ^ 2) P := by
    rw [hDecomp]
    exact integrable_finsetSum Finset.univ fun k _ ↦ (hSqDiff_int k).indicator (hIk_meas k)
  let G : (Fin n → ℝ) → ℝ := fun v ↦
    (1 / (n : ℝ)) * ∑ k : Fin n,
      ((∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * v k + v k ^ 2)
  have hG_meas : Measurable G := by
    refine measurable_const.mul (Finset.measurable_sum Finset.univ fun k _ ↦ ?_)
    exact (measurable_const.sub (measurable_const.mul (measurable_pi_apply k))).add
      ((measurable_pi_apply k).pow_const 2)
  have hRHS_sm : StronglyMeasurable[MeasurableSpace.comap VX inferInstance] (G ∘ VX) :=
    (hG_meas.comp (comap_measurable (m := inferInstance) VX)).stronglyMeasurable
  have hRHS_int : Integrable (G ∘ VX) P := by
    refine (integrable_finsetSum Finset.univ fun k _ ↦ ?_).const_mul (1 / (n : ℝ))
    exact ((integrable_const _).sub ((hX_int k).const_mul _)).add (hX_sq_int k)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmVX hLHS_int
    (fun s _ _ ↦ hRHS_int.integrableOn) (fun s hs _ ↦ ?_)
    hRHS_sm.aestronglyMeasurable).symm
  rcases hs with ⟨T, hT, rfl⟩
  rw [hDecomp,
    integral_finsetSum Finset.univ fun k _ ↦ ((hSqDiff_int k).indicator (hIk_meas k)).integrableOn]
  have hterm : ∀ k : Fin n,
      ∫ ω in VX ⁻¹' T,
          {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') ^ 2) ω ∂P =
        (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T,
          ((∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * X k ω + X k ω ^ 2) ∂P := by
    intro k
    let Hk : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦ (p.2 k - p.1 k) ^ 2
    have hHk_meas : Measurable Hk :=
      (((measurable_pi_apply k).comp measurable_snd).sub
        ((measurable_pi_apply k).comp measurable_fst)).pow_const 2
    have hStep1 :=
      indepSum_setIntegral_indicator_I_vx P hn hX_meas hX'_meas hI_meas hI_indep hI_unif k hT
        hHk_meas
    have hId_k : IdentDistrib (X' k) (X k) P P := hId.comp (measurable_pi_apply k)
    have hX'_m1 : ∫ ω, X' k ω ∂P = ∫ ω, X k ω ∂P := hId_k.integral_eq
    have hX'_m2 : ∫ ω, X' k ω ^ 2 ∂P = ∫ ω, X k ω ^ 2 ∂P :=
      (hId_k.comp (measurable_id.pow_const 2)).integral_eq
    have hInt1 :
        ∫ ω in VX ⁻¹' T, X' k ω ^ 2 ∂P = ∫ ω in VX ⁻¹' T, (∫ ω', X k ω' ^ 2 ∂P) ∂P := by
      have hmul :
          ∫ ω in VX ⁻¹' T, (1 : ℝ) * X' k ω ^ 2 ∂P =
            (∫ ω in VX ⁻¹' T, (1 : ℝ) ∂P) * ∫ ω, X' k ω ^ 2 ∂P :=
        indepSum_setIntegral_vx_mul_vx' P hX_meas hX'_meas hXX'_indep hT
          (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ (1 : ℝ)))
          ((measurable_pi_apply k).pow_const 2)
      simp only [one_mul, hX'_m2] at hmul
      rw [hmul, setIntegral_const, smul_eq_mul, mul_one, setIntegral_const, smul_eq_mul]
    have hInt2 :
        ∫ ω in VX ⁻¹' T, X k ω * X' k ω ∂P =
          ∫ ω in VX ⁻¹' T, (∫ ω', X k ω' ∂P) * X k ω ∂P := by
      have hmul :
          ∫ ω in VX ⁻¹' T, X k ω * X' k ω ∂P =
            (∫ ω in VX ⁻¹' T, X k ω ∂P) * ∫ ω, X' k ω ∂P :=
        indepSum_setIntegral_vx_mul_vx' P hX_meas hX'_meas hXX'_indep hT
          (measurable_pi_apply k) (measurable_pi_apply k)
      rw [hmul, hX'_m1, mul_comm, ← integral_const_mul]
    have hExpand :
        ∫ ω in VX ⁻¹' T, (X' k ω - X k ω) ^ 2 ∂P =
          ∫ ω in VX ⁻¹' T,
            ((∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * X k ω + X k ω ^ 2) ∂P := by
      let f1 : Ω → ℝ := fun ω ↦ X' k ω ^ 2
      let f2 : Ω → ℝ := fun ω ↦ 2 * (X k ω * X' k ω)
      let f3 : Ω → ℝ := fun ω ↦ X k ω ^ 2
      have hf1 : IntegrableOn f1 (VX ⁻¹' T) P := (hX'_sq_int k).integrableOn
      have hf2 : IntegrableOn f2 (VX ⁻¹' T) P := ((hXX'_mul_int k).const_mul 2).integrableOn
      have hf3 : IntegrableOn f3 (VX ⁻¹' T) P := (hX_sq_int k).integrableOn
      have hpt : (fun ω ↦ (X' k ω - X k ω) ^ 2) = fun ω ↦ (f1 - f2) ω + f3 ω := by
        funext ω; dsimp [f1, f2, f3]; ring
      let g1 : Ω → ℝ := fun _ ↦ ∫ ω', X k ω' ^ 2 ∂P
      let g2 : Ω → ℝ := fun ω ↦ 2 * ((∫ ω', X k ω' ∂P) * X k ω)
      have hg1 : IntegrableOn g1 (VX ⁻¹' T) P := (integrable_const _).integrableOn
      have hg2 : IntegrableOn g2 (VX ⁻¹' T) P :=
        (((hX_int k).const_mul (∫ ω', X k ω' ∂P)).const_mul 2).integrableOn
      have hpt2 :
          (fun ω ↦ (∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * X k ω + X k ω ^ 2) =
            fun ω ↦ (g1 - g2) ω + f3 ω := by
        funext ω; dsimp [g1, g2, f3]; ring
      have hsub1 : ∫ ω in VX ⁻¹' T, (f1 - f2) ω ∂P =
          (∫ ω in VX ⁻¹' T, f1 ω ∂P) - ∫ ω in VX ⁻¹' T, f2 ω ∂P := integral_sub hf1 hf2
      have hsub2 : ∫ ω in VX ⁻¹' T, (g1 - g2) ω ∂P =
          (∫ ω in VX ⁻¹' T, g1 ω ∂P) - ∫ ω in VX ⁻¹' T, g2 ω ∂P := integral_sub hg1 hg2
      rw [hpt, hpt2, integral_add (hf1.sub hf2) hf3, integral_add (hg1.sub hg2) hf3, hsub1, hsub2]
      dsimp only [f1, f2, g1, g2]
      rw [integral_const_mul, integral_const_mul 2, hInt1, hInt2]
    exact hStep1.trans (congrArg ((1 / (n : ℝ)) * ·) hExpand)
  calc
    ∫ ω in VX ⁻¹' T, (G ∘ VX) ω ∂P
        = (1 / (n : ℝ)) * ∑ k : Fin n,
            ∫ ω in VX ⁻¹' T,
              ((∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * X k ω + X k ω ^ 2) ∂P := by
          let termF : Fin n → Ω → ℝ := fun k ω ↦
            (∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * X k ω + X k ω ^ 2
          have hG_eq : G ∘ VX = fun ω ↦ (1 / (n : ℝ)) * ∑ k : Fin n, termF k ω := rfl
          have htermF_int : ∀ k : Fin n, IntegrableOn (termF k) (VX ⁻¹' T) P := fun k ↦
            (((integrable_const _).sub ((hX_int k).const_mul _)).add (hX_sq_int k)).integrableOn
          rw [hG_eq, integral_const_mul, integral_finsetSum Finset.univ fun k _ ↦ htermF_int k]
    _ = ∑ k : Fin n,
          (1 / (n : ℝ)) * ∫ ω in VX ⁻¹' T,
            ((∫ ω', X k ω' ^ 2 ∂P) - 2 * (∫ ω', X k ω' ∂P) * X k ω + X k ω ^ 2) ∂P := by
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n,
          ∫ ω in VX ⁻¹' T,
            {ω' : Ω | I ω' = k}.indicator (fun ω' ↦ (X' k ω' - X k ω') ^ 2) ω ∂P :=
          Finset.sum_congr rfl fun k _ ↦ (hterm k).symm

end SteinMethod
