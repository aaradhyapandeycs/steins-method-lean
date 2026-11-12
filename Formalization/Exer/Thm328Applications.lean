/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.IndepSumPair
import Formalization.Exchangeable.SteinPairBound
import Formalization.Kolmogorov.ExchangeableBound
import Mathlib.Probability.Moments.Variance

/-!
# Theorem 3.28 Applications & Conditional-Variance Helpers (`Formalization.Exer.Thm328Applications`)

Provides:
1. Shared real-valued conditional-Jensen variance monotonicity helpers
   (`variance_condExp_le_of_le`, `variance_condExp_comap_le`) and direct conversions of
   **Theorem 3.28** (`\label{thm92}`, `IsSteinPair.kolmogorovDist_map_stdNormal_le`) +
   **Remark 3.4** (`evariance_condExp_mono`) to single `ENNReal.ofReal` bounds when conditioning on
   a finer measurable variable $X$ (`IsSteinPair.kolmogorovDist_le_of_comap`,
   `IsSteinPair.kolmogorovDist_le_of_condExp_ae_eq`).
2. **Section 3.6.2 bounded independent-sum Kolmogorov bound** (`sec3_6_2_indepSum_kolmogorov`,
   `EXER-4`, `SteinIntro.tex:1810`): applies Theorem 3.28 and Remark 3.4 to Example 3.6's
   replace-one $(1/n)$-Stein pair for independent centered almost surely bounded summands with
   general total variance $\sigma^2 > 0$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SteinMethod

/-! ### Section 1: Shared Conditional-Variance & Theorem 3.28 Conversion Helpers -/

/-- Real-valued conditional-Jensen variance monotonicity (`SteinIntro.tex:1000-1008`, Remark 3.4):
for sub-$\sigma$-algebras $m_1 \le m_2 \le m_0$ and $Y \in L^2(P)$,
$\operatorname{Var}(\mathbb{E}[Y \mid m_1]) \le \operatorname{Var}(\mathbb{E}[Y \mid m_2])$. -/
theorem variance_condExp_le_of_le
    {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {m₁ m₂ : MeasurableSpace Ω} {Y : Ω → ℝ}
    (hm₁₂ : m₁ ≤ m₂) (hm₂₀ : m₂ ≤ m₀) (hY2 : MemLp Y 2 P) :
    ProbabilityTheory.variance (P[Y | m₁]) P ≤
      ProbabilityTheory.variance (P[Y | m₂]) P := by
  have h₁ : MemLp (P[Y | m₁]) 2 P := hY2.condExp one_le_two
  have h₂ : MemLp (P[Y | m₂]) 2 P := hY2.condExp one_le_two
  have hev := evariance_condExp_mono P hm₁₂ hm₂₀ (hY2.integrable one_le_two)
  rw [← ProbabilityTheory.ofReal_variance h₁, ← ProbabilityTheory.ofReal_variance h₂] at hev
  exact (ENNReal.ofReal_le_ofReal_iff (ProbabilityTheory.variance_nonneg _ P)).mp hev

/-- Comap specialization of `variance_condExp_le_of_le`: if $\sigma(W) \le \sigma(X)$ with $X$
measurable and $Y \in L^2(P)$, then
$\operatorname{Var}(\mathbb{E}[Y \mid \sigma(W)]) \le
\operatorname{Var}(\mathbb{E}[Y \mid \sigma(X)])$. -/
theorem variance_condExp_comap_le
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → α} {X : Ω → β} {Y : Ω → ℝ}
    (hmWX : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap X inferInstance)
    (hX : Measurable X) (hY2 : MemLp Y 2 P) :
    ProbabilityTheory.variance (P[Y | MeasurableSpace.comap W inferInstance]) P ≤
      ProbabilityTheory.variance (P[Y | MeasurableSpace.comap X inferInstance]) P :=
  variance_condExp_le_of_le P hmWX hX.comap_le hY2

/-- Conversion of **Theorem 3.28** (`\label{thm92}`) + **Remark 3.4** (`evariance_condExp_mono`)
to a single real-valued `ENNReal.ofReal` bound when conditioning on a finer measurable variable
$X$ ($\sigma(W) \le \sigma(X)$): for an $a$-Stein pair $(W, W')$ with $\operatorname{Var}(W) = 1$
and $|W' - W| \le \delta$ a.s.,
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid \sigma(X)])}}{2a} +
\frac{\delta^3}{2a} + \frac{3\delta}{2}$. -/
theorem IsSteinPair.kolmogorovDist_le_of_comap
    {Ω Ω' β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a δ : ℝ} {W W' : Ω → ℝ} {X : Ω → β} {Z : Ω' → ℝ}
    (hSP : IsSteinPair P a W W')
    (hvar : ProbabilityTheory.variance W P = 1)
    (hδ : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ)
    (hmWX : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap X inferInstance)
    (hX : Measurable X)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt
            (ProbabilityTheory.variance
              (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap X inferInstance]) P) /
            (2 * a) +
          δ ^ 3 / (2 * a) +
          3 * δ / 2) := by
  have ha : 0 < a := hSP.2.1
  have h2a_pos : 0 < 2 * a := by positivity
  have hδ_nn : 0 ≤ δ := by
    obtain ⟨ω₀, hω₀⟩ := hδ.exists
    exact (abs_nonneg _).trans hω₀
  have hW'_aem : AEMeasurable W' P := hSP.1.fst_identDistrib_snd.aemeasurable_snd
  set D2 : Ω → ℝ := fun ω ↦ (W' ω - W ω) ^ 2
  have hD2_asm : AEStronglyMeasurable D2 P :=
    ((hW'_aem.sub hSP.2.2.2.1.aemeasurable).pow_const 2).aestronglyMeasurable
  have hD2_L2 : MemLp D2 2 P := by
    refine MemLp.of_bound hD2_asm (δ ^ 2) ?_
    filter_upwards [hδ] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      D2 ω = |W' ω - W ω| ^ 2 := (sq_abs (W' ω - W ω)).symm
      _ ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hω 2
  set QW : Ω → ℝ := P[D2 | MeasurableSpace.comap W inferInstance]
  set QX : Ω → ℝ := P[D2 | MeasurableSpace.comap X inferInstance]
  have hQW_L2 : MemLp QW 2 P := hD2_L2.condExp one_le_two
  have hVarLe : ProbabilityTheory.variance QW P ≤ ProbabilityTheory.variance QX P :=
    variance_condExp_comap_le P hmWX hX hD2_L2
  have hSqrtLe :
      Real.sqrt (ProbabilityTheory.variance QW P) / (2 * a) ≤
        Real.sqrt (ProbabilityTheory.variance QX P) / (2 * a) :=
    div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hVarLe) h2a_pos.le
  have hEvarEq :
      ProbabilityTheory.evariance QW P ^ (1 / 2 : ℝ) / ENNReal.ofReal (2 * a) =
        ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance QW P) / (2 * a)) := by
    rw [← ProbabilityTheory.ofReal_variance hQW_L2,
      ENNReal.ofReal_rpow_of_nonneg (ProbabilityTheory.variance_nonneg QW P) (by positivity),
      ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_div_of_pos h2a_pos]
  have hT1_nn : 0 ≤ Real.sqrt (ProbabilityTheory.variance QW P) / (2 * a) :=
    div_nonneg (Real.sqrt_nonneg _) h2a_pos.le
  have hT2_nn : 0 ≤ δ ^ 3 / (2 * a) + 3 * δ / 2 := by positivity
  calc
    kolmogorovDist (P.map W) (P'.map Z)
      ≤ ProbabilityTheory.evariance QW P ^ (1 / 2 : ℝ) / ENNReal.ofReal (2 * a) +
          ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2) :=
        hSP.kolmogorovDist_map_stdNormal_le P' hvar hδ hZ hZ_law
    _ = ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance QW P) / (2 * a)) +
          ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2) := by rw [hEvarEq]
    _ = ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance QW P) / (2 * a) +
          (δ ^ 3 / (2 * a) + 3 * δ / 2)) :=
        (ENNReal.ofReal_add hT1_nn hT2_nn).symm
    _ ≤ ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance QX P) / (2 * a) +
          δ ^ 3 / (2 * a) + 3 * δ / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith

/-- Direct **Theorem 3.28** + **Remark 3.4** helper when
$\mathbb{E}[(W' - W)^2 \mid \sigma(X)] =^{\text{a.s.}} R$ (note `MemLp R 2 P` is derived
automatically from $|W' - W| \le \delta$ a.s.):
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(R)}}{2a} + \frac{\delta^3}{2a} + \frac{3\delta}{2}$. -/
theorem IsSteinPair.kolmogorovDist_le_of_condExp_ae_eq
    {Ω Ω' β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace β]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a δ : ℝ} {W W' R : Ω → ℝ} {X : Ω → β} {Z : Ω' → ℝ}
    (hSP : IsSteinPair P a W W')
    (hvar : ProbabilityTheory.variance W P = 1)
    (hδ : ∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ)
    (hmWX : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap X inferInstance)
    (hX : Measurable X)
    (hCondSq : P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap X inferInstance] =ᵐ[P] R)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (ProbabilityTheory.variance R P) / (2 * a) +
          δ ^ 3 / (2 * a) +
          3 * δ / 2) := by
  rw [← ProbabilityTheory.variance_congr hCondSq]
  exact hSP.kolmogorovDist_le_of_comap P' hvar hδ hmWX hX hZ hZ_law

/-! ### Section 2: General-Variance Replace-One Coupling Helpers (`EXER-4`) -/

private lemma measurePreserving_prod_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving Prod.fst (μ.prod ν) μ :=
  ⟨measurable_fst, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

private lemma measurePreserving_prod_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving Prod.snd (μ.prod ν) ν :=
  ⟨measurable_snd, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩

private lemma indepFun_prod_fst_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ProbabilityTheory.IndepFun (Prod.fst : α × β → α) Prod.snd (μ.prod ν) := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have h1 : (Prod.fst : α × β → α) ⁻¹' s = s ×ˢ Set.univ := by ext p; simp
  have h2 : (Prod.snd : α × β → β) ⁻¹' t = Set.univ ×ˢ t := by ext p; simp
  have h3 : (s ×ˢ (Set.univ : Set β)) ∩ (Set.univ ×ˢ t) = s ×ˢ t := by ext p; simp
  rw [h1, h2, h3, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul]

private def swapCoordGen {n : ℕ} (k : Fin n) (p : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i ↦ if k = i then p.2 i else p.1 i, fun i ↦ if k = i then p.1 i else p.2 i)

private def swapPairGen {n : ℕ} (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) :
    Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (q.1, swapCoordGen q.1 q.2)

private lemma measurable_swapPairGen {n : ℕ} : Measurable (@swapPairGen n) := by
  have hset : ∀ i : Fin n,
      MeasurableSet {q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.1 = i} := fun i ↦ by
    have hpre : {q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) | q.1 = i} = Prod.fst ⁻¹' {i} := rfl
    exact hpre ▸ measurable_fst (measurableSet_singleton i)
  refine measurable_fst.prodMk (Measurable.prodMk
    (Measurable.of_eval fun i ↦ Measurable.ite (hset i)
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)))
    (Measurable.of_eval fun i ↦ Measurable.ite (hset i)
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))

private lemma measurePreserving_swapCoordGen {n : ℕ} (k : Fin n) (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (swapCoordGen k)
      ((Measure.pi μ).prod (Measure.pi μ))
      ((Measure.pi μ).prod (Measure.pi μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)
  have he : MeasurePreserving e
      (Measure.pi fun i ↦ (μ i).prod (μ i))
      ((Measure.pi μ).prod (Measure.pi μ)) :=
    measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) μ μ
  have hf : ∀ i : Fin n,
      MeasurePreserving (if k = i then Prod.swap else id)
        ((μ i).prod (μ i)) ((μ i).prod (μ i)) := fun i ↦ by
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
      swapCoordGen k = (e ∘ fun a i ↦ (if k = i then Prod.swap else id) (a i)) ∘ e.symm := by
    rw [he_apply, he_symm]
    funext p
    apply Prod.ext <;> funext i <;> by_cases hk : k = i <;> simp [swapCoordGen, hk]
  rwa [← heq] at hcomp

private lemma measurePreserving_swapPairGen {n : ℕ}
    (μI : Measure (Fin n)) [SigmaFinite μI]
    (ν : Measure ((Fin n → ℝ) × (Fin n → ℝ))) [SigmaFinite ν]
    (hSwap : ∀ k : Fin n, MeasurePreserving (swapCoordGen k) ν ν) :
    MeasurePreserving swapPairGen (μI.prod ν) (μI.prod ν) where
  measurable := measurable_swapPairGen
  map_eq := by
    refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [Measure.map_apply measurable_swapPairGen (hs.prod ht),
      Measure.prod_apply (measurable_swapPairGen (hs.prod ht))]
    have hslice :
        (fun k : Fin n ↦ ν (Prod.mk k ⁻¹' (swapPairGen ⁻¹' (s ×ˢ t)))) =
          s.indicator (fun _ ↦ ν t) := by
      funext k
      by_cases hk : k ∈ s
      · have hpre : Prod.mk k ⁻¹' (swapPairGen ⁻¹' (s ×ˢ t)) = swapCoordGen k ⁻¹' t := by
          ext p; simp [swapPairGen, hk]
        rw [Set.indicator_of_mem hk, hpre, ← Measure.map_apply (hSwap k).measurable ht,
          (hSwap k).map_eq]
      · have hpre : Prod.mk k ⁻¹' (swapPairGen ⁻¹' (s ×ˢ t)) = ∅ := by
          ext p; simp [swapPairGen, hk]
        rw [Set.indicator_of_notMem hk, hpre, measure_empty]
    rw [hslice, lintegral_indicator_const hs (ν t), mul_comm]

private noncomputable def pairStatScale {n : ℕ} (σ : ℝ)
    (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) : ℝ × ℝ :=
  let w := (∑ i : Fin n, q.2.1 i) / σ
  (w, w - q.2.1 q.1 / σ + q.2.2 q.1 / σ)

private lemma measurable_eval_idx {n : ℕ} {α : Type*} [MeasurableSpace α]
    (f : α → Fin n → ℝ) (hf : Measurable f) :
    Measurable (fun q : Fin n × α ↦ f q.2 q.1) := by
  have heq : (fun q : Fin n × α ↦ f q.2 q.1) =
      fun q ↦ ∑ i : Fin n, if q.1 = i then f q.2 i else 0 := by
    funext q; simp
  rw [heq]
  refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
  have hpre : {q : Fin n × α | q.1 = i} = Prod.fst ⁻¹' {i} := rfl
  exact Measurable.ite (hpre ▸ measurable_fst (measurableSet_singleton i))
    ((measurable_pi_apply i).comp (hf.comp measurable_snd)) measurable_const

private lemma measurable_pairStatScale {n : ℕ} (σ : ℝ) : Measurable (@pairStatScale n σ) := by
  have hw : Measurable (fun q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) ↦
      (∑ i : Fin n, q.2.1 i) / σ) :=
    (Finset.measurable_sum Finset.univ fun i _ ↦
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).div_const σ
  have he1 := measurable_eval_idx (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ) measurable_fst
  have he2 := measurable_eval_idx (Prod.snd : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ) measurable_snd
  exact hw.prodMk ((hw.sub (he1.div_const σ)).add (he2.div_const σ))

private lemma pairStatScale_swapPairGen {n : ℕ} (σ : ℝ)
    (q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) :
    pairStatScale σ (swapPairGen q) = (pairStatScale σ q).swap := by
  have hsum : (∑ i : Fin n, (swapCoordGen q.1 q.2).1 i) =
      (∑ i : Fin n, q.2.1 i) + (q.2.2 q.1 - q.2.1 q.1) := by
    have hterm : ∀ i : Fin n,
        (swapCoordGen q.1 q.2).1 i =
          q.2.1 i + (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0) := fun i ↦ by
      by_cases h : q.1 = i
      · subst h; simp [swapCoordGen]
      · simp [swapCoordGen, h]
    calc
      (∑ i : Fin n, (swapCoordGen q.1 q.2).1 i)
        = ∑ i : Fin n, (q.2.1 i + (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0)) :=
            Finset.sum_congr rfl fun i _ ↦ hterm i
      _ = (∑ i : Fin n, q.2.1 i) +
            ∑ i : Fin n, (if q.1 = i then q.2.2 q.1 - q.2.1 q.1 else 0) :=
            Finset.sum_add_distrib
      _ = (∑ i : Fin n, q.2.1 i) + (q.2.2 q.1 - q.2.1 q.1) := by simp
  have hk1 : (swapCoordGen q.1 q.2).1 q.1 = q.2.2 q.1 := by simp [swapCoordGen]
  have hk2 : (swapCoordGen q.1 q.2).2 q.1 = q.2.1 q.1 := by simp [swapCoordGen]
  ext <;> dsimp [pairStatScale, swapPairGen] <;> rw [hsum]
  · ring
  · rw [hk1, hk2]; ring

/-! ### Section 3: Bounded Independent-Sum Kolmogorov Bound (`EXER-4`) -/

/-- **Section 3.6.2 bounded independent-sum Kolmogorov bound via exchangeable pairs**
(`SteinIntro.tex:1810`, `EXER-4`, applying Theorem 3.28 `\label{thm92}` and Remark 3.4 with
Example 3.6's replace-one $(1/n)$-Stein pair): if $X_1, \dots, X_n$ are independent mean-zero
random variables satisfying $|X_i| \le C$ almost surely with
$\sigma^2 = \operatorname{Var}(\sum_{i=1}^n X_i) > 0$, $W = (\sum_{i=1}^n X_i) / \sigma$, and
$Z \sim \mathcal{N}(0, 1)$, then
$$
  d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
    \frac{\sqrt{\sum_{i=1}^n \operatorname{Var}(X_i^2)}}{2 \sigma^2} +
    \frac{4 n C^3}{\sigma^3} +
    \frac{3 C}{\sigma}.
$$
Here conditional Jensen (Remark 3.4) bounds
$\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W]) \le
\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid X])$, and the right-hand side evaluates the latter. -/
theorem sec3_6_2_indepSum_kolmogorov
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ} {C : ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |X i ω| ≤ C)
    (hVar_pos : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (∑ i : Fin n, ProbabilityTheory.variance (fun ω ↦ X i ω ^ 2) P) /
            (2 * σ ^ 2) +
          4 * (n : ℝ) * C ^ 3 / σ ^ 3 +
          3 * C / σ) := by
  intro S σ W
  have hn : 0 < n := by
    by_contra hn0
    obtain rfl := Nat.eq_zero_of_not_pos hn0
    have hS0 : S = 0 := by ext ω; simp [S]
    change 0 < ProbabilityTheory.variance S P at hVar_pos
    rw [hS0, ProbabilityTheory.variance_zero] at hVar_pos
    exact lt_irrefl 0 hVar_pos
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hrn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar_pos
  have hσ_ne : σ ≠ 0 := hσ_pos.ne'
  have hσ_sq : σ ^ 2 = ProbabilityTheory.variance S P := Real.sq_sqrt hVar_pos.le
  -- Canonical product space `μI ⊗ ((⨂ᵢ μᵢ) ⊗ (⨂ᵢ μᵢ))` realizing `(I, X, X')`.
  let μ : Fin n → Measure ℝ := fun i ↦ P.map (X i)
  have : ∀ i : Fin n, IsProbabilityMeasure (μ i) :=
    fun i ↦ (Measure.isProbabilityMeasure_map_iff (hX_meas i)).mpr inferInstance
  have hμ0 : ∀ i : Fin n, ∫ x, x ∂(μ i) = 0 :=
    fun i ↦ (integral_map (hX_meas i) aestronglyMeasurable_id).trans (hX0 i)
  have hClosed : MeasurableSet {x : ℝ | |x| ≤ C} :=
    (isClosed_le continuous_abs continuous_const).measurableSet
  have hμ_bdd : ∀ i : Fin n, ∀ᵐ x ∂(μ i), |x| ≤ C := fun i ↦ by
    rw [ae_iff]
    change (P.map (X i)) {x : ℝ | |x| ≤ C}ᶜ = 0
    rw [Measure.map_apply_of_aemeasurable (hX_meas i) hClosed.compl]
    exact ae_iff.mp (hX_bdd i)
  let μI : Measure (Fin n) := (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure
  let ν : Measure ((Fin n → ℝ) × (Fin n → ℝ)) := (Measure.pi μ).prod (Measure.pi μ)
  let P₀ : Measure (Fin n × ((Fin n → ℝ) × (Fin n → ℝ))) := μI.prod ν
  have : IsProbabilityMeasure μI := inferInstance
  have : IsProbabilityMeasure P₀ := inferInstance
  let I₀ : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → Fin n := Prod.fst
  let VY : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → Fin n → ℝ := fun q ↦ q.2.1
  let VY' : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → Fin n → ℝ := fun q ↦ q.2.2
  let Y : Fin n → Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun i q ↦ q.2.1 i
  let Y' : Fin n → Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun i q ↦ q.2.2 i
  let S₀ : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun q ↦ ∑ i : Fin n, q.2.1 i
  let W₀ : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun q ↦ S₀ q / σ
  let W₀' : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun q ↦ W₀ q - q.2.1 q.1 / σ + q.2.2 q.1 / σ
  let R₀ : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun q ↦ (1 / ((n : ℝ) * σ ^ 2)) *
      ∑ i : Fin n, (Y i q ^ 2 + ProbabilityTheory.variance id (μ i))
  have hI₀_meas : Measurable I₀ := measurable_fst
  have hVY_meas : Measurable VY := measurable_fst.comp measurable_snd
  have hVY'_meas : Measurable VY' := measurable_snd.comp measurable_snd
  have hY_meas : ∀ i : Fin n, Measurable (Y i) := fun i ↦ (measurable_pi_apply i).comp hVY_meas
  have hY'_meas : ∀ i : Fin n, Measurable (Y' i) := fun i ↦ (measurable_pi_apply i).comp hVY'_meas
  have hsnd_MP : MeasurePreserving Prod.snd P₀ ν := measurePreserving_prod_snd μI ν
  have hπY : MeasurePreserving VY P₀ (Measure.pi μ) :=
    (measurePreserving_prod_fst (Measure.pi μ) (Measure.pi μ)).comp hsnd_MP
  have hπY' : MeasurePreserving VY' P₀ (Measure.pi μ) :=
    (measurePreserving_prod_snd (Measure.pi μ) (Measure.pi μ)).comp hsnd_MP
  have hMP_Y : ∀ i : Fin n, MeasurePreserving (Y i) P₀ (μ i) :=
    fun i ↦ (measurePreserving_eval μ i).comp hπY
  have hMP_Y' : ∀ i : Fin n, MeasurePreserving (Y' i) P₀ (μ i) :=
    fun i ↦ (measurePreserving_eval μ i).comp hπY'
  have hI₀_unif : P₀.map I₀ = μI := (measurePreserving_prod_fst μI ν).map_eq
  have hI₀_indep :
      ProbabilityTheory.IndepFun I₀ (fun q ↦ (fun i ↦ Y i q, fun i ↦ Y' i q)) P₀ :=
    indepFun_prod_fst_snd μI ν
  have hYY'_indep : ProbabilityTheory.IndepFun VY' VY P₀ := by
    have hbase := (indepFun_prod_fst_snd (Measure.pi μ) (Measure.pi μ)).symm
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at hbase ⊢
    intro s t hs ht
    change P₀ (Prod.snd ⁻¹' (Prod.snd ⁻¹' s ∩ Prod.fst ⁻¹' t)) =
      P₀ (Prod.snd ⁻¹' (Prod.snd ⁻¹' s)) * P₀ (Prod.snd ⁻¹' (Prod.fst ⁻¹' t))
    rw [hsnd_MP.measure_preimage
        ((hs.preimage measurable_snd).inter (ht.preimage measurable_fst)).nullMeasurableSet,
      hbase s t hs ht,
      hsnd_MP.measure_preimage (hs.preimage measurable_snd).nullMeasurableSet,
      hsnd_MP.measure_preimage (ht.preimage measurable_fst).nullMeasurableSet]
  -- Bounds, moments, and distributional matching between `(P, W)` and `(P₀, W₀)`.
  have hPull_bdd : ∀ {i : Fin n} {Z : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ},
      Measurable Z → MeasurePreserving Z P₀ (μ i) → ∀ᵐ q ∂P₀, |Z q| ≤ C := by
    intro i Z hZm hZmp
    rw [ae_iff]
    have hpre : {q | ¬|Z q| ≤ C} = Z ⁻¹' {x : ℝ | |x| ≤ C}ᶜ := rfl
    rw [hpre, ← Measure.map_apply hZm hClosed.compl, hZmp.map_eq]
    exact ae_iff.mp (hμ_bdd i)
  have hY_bdd : ∀ i : Fin n, ∀ᵐ q ∂P₀, |Y i q| ≤ C := fun i ↦ hPull_bdd (hY_meas i) (hMP_Y i)
  have hY'_bdd : ∀ i : Fin n, ∀ᵐ q ∂P₀, |Y' i q| ≤ C := fun i ↦ hPull_bdd (hY'_meas i) (hMP_Y' i)
  have hSq_L2 : ∀ {Z : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ},
      Measurable Z → (∀ᵐ q ∂P₀, |Z q| ≤ C) → MemLp (fun q ↦ Z q ^ 2) 2 P₀ := by
    intro Z hZm hZb
    refine MemLp.of_bound (hZm.pow_const 2).aestronglyMeasurable (C ^ 2) ?_
    filter_upwards [hZb] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (Z q)]
    exact pow_le_pow_left₀ (abs_nonneg _) hq 2
  have hY_int : ∀ i : Fin n, Integrable (Y i) P₀ := fun i ↦
    Integrable.of_bound (hY_meas i).aestronglyMeasurable C
      (by filter_upwards [hY_bdd i] with q hq; simpa [Real.norm_eq_abs] using hq)
  have hY'_int : ∀ i : Fin n, Integrable (Y' i) P₀ := fun i ↦
    Integrable.of_bound (hY'_meas i).aestronglyMeasurable C
      (by filter_upwards [hY'_bdd i] with q hq; simpa [Real.norm_eq_abs] using hq)
  have hYsq_L2 : ∀ i : Fin n, MemLp (fun q ↦ Y i q ^ 2) 2 P₀ :=
    fun i ↦ hSq_L2 (hY_meas i) (hY_bdd i)
  have hY'sq_L2 : ∀ i : Fin n, MemLp (fun q ↦ Y' i q ^ 2) 2 P₀ :=
    fun i ↦ hSq_L2 (hY'_meas i) (hY'_bdd i)
  have hY_sq_int : ∀ i : Fin n, Integrable (fun q ↦ Y i q ^ 2) P₀ :=
    fun i ↦ (hYsq_L2 i).integrable one_le_two
  have hY'_sq_int : ∀ i : Fin n, Integrable (fun q ↦ Y' i q ^ 2) P₀ :=
    fun i ↦ (hY'sq_L2 i).integrable one_le_two
  have hY'0 : ∀ i : Fin n, ∫ q, Y' i q ∂P₀ = 0 := fun i ↦
    (integral_map (hY'_meas i).aemeasurable aestronglyMeasurable_id).symm.trans
      ((congrArg (fun ν₀ ↦ ∫ x, x ∂ν₀) (hMP_Y' i).map_eq).trans (hμ0 i))
  let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  have hVX_aem : AEMeasurable VX P := .of_eval hX_meas
  have hMapVX : P.map VX = Measure.pi μ := h_indep.map_fun_eq_pi_map hX_meas
  let sumRaw : (Fin n → ℝ) → ℝ := fun v ↦ ∑ i : Fin n, v i
  let sumScale : (Fin n → ℝ) → ℝ := fun v ↦ (∑ i : Fin n, v i) / σ
  have hsumRaw_meas : Measurable sumRaw :=
    Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i
  have hsumScale_meas : Measurable sumScale := hsumRaw_meas.div_const σ
  have hMapW : P₀.map W₀ = P.map W :=
    (Measure.map_map hsumScale_meas hVY_meas).symm.trans
      ((congrArg (Measure.map sumScale) (hπY.map_eq.trans hMapVX.symm)).trans
        (AEMeasurable.map_map_of_aemeasurable hsumScale_meas.aemeasurable hVX_aem))
  have hMapS : P₀.map S₀ = P.map S :=
    (Measure.map_map hsumRaw_meas hVY_meas).symm.trans
      ((congrArg (Measure.map sumRaw) (hπY.map_eq.trans hMapVX.symm)).trans
        (AEMeasurable.map_map_of_aemeasurable hsumRaw_meas.aemeasurable hVX_aem))
  have hVarW₀ : ProbabilityTheory.variance W₀ P₀ = 1 := by
    have hS_aem : AEMeasurable S P := hsumRaw_meas.comp_aemeasurable hVX_aem
    have hS₀_meas : Measurable S₀ := hsumRaw_meas.comp hVY_meas
    have hVarS₀ : ProbabilityTheory.variance S₀ P₀ = ProbabilityTheory.variance S P := by
      rw [← ProbabilityTheory.variance_id_map hS₀_meas.aemeasurable, hMapS,
        ProbabilityTheory.variance_id_map hS_aem]
    have hW₀_eq : W₀ = fun q ↦ σ⁻¹ * S₀ q := by
      funext q; dsimp [W₀]; rw [div_eq_mul_inv, mul_comm]
    rw [hW₀_eq, ProbabilityTheory.variance_const_mul, inv_pow, hVarS₀, ← hσ_sq,
      inv_mul_cancel₀ (pow_ne_zero 2 hσ_ne)]
  have hδ : ∀ᵐ q ∂P₀, |W₀' q - W₀ q| ≤ 2 * C / σ := by
    filter_upwards [ae_all_iff.mpr fun i ↦ (hY_bdd i).and (hY'_bdd i)] with q hq
    have hdiff : W₀' q - W₀ q = (Y' q.1 q - Y q.1 q) / σ := by dsimp [W₀', Y, Y']; ring
    rw [hdiff, abs_div, abs_of_pos hσ_pos]
    refine div_le_div_of_nonneg_right ?_ hσ_pos.le
    linarith [(hq q.1).1, (hq q.1).2, abs_sub (Y' q.1 q) (Y q.1 q)]
  have hmW₀_VY :
      MeasurableSpace.comap W₀ inferInstance ≤ MeasurableSpace.comap VY inferInstance := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨sumScale ⁻¹' B, hsumScale_meas hB, rfl⟩
  have hIk_meas : ∀ k : Fin n, MeasurableSet {q | I₀ q = k} := fun k ↦ by
    have hpre : {q : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) | I₀ q = k} = I₀ ⁻¹' {k} := rfl
    exact hpre ▸ hI₀_meas (measurableSet_singleton k)
  -- Step 1: `(W₀, W₀')` is a `(1 / n)`-Stein pair on `P₀`.
  have hSP : IsSteinPair P₀ (1 / (n : ℝ)) W₀ W₀' := by
    have hMP_swap : MeasurePreserving swapPairGen P₀ P₀ :=
      measurePreserving_swapPairGen μI ν (fun k ↦ measurePreserving_swapCoordGen k μ)
    have hWW'_meas : Measurable (fun q ↦ (W₀ q, W₀' q)) := measurable_pairStatScale σ
    have hExch : IsExchangeablePair P₀ W₀ W₀' := by
      refine ⟨hWW'_meas.aemeasurable, (measurable_swap.comp hWW'_meas).aemeasurable, ?_⟩
      calc
        P₀.map (fun q ↦ (W₀ q, W₀' q)) = P₀.map (pairStatScale σ) := rfl
        _ = (P₀.map swapPairGen).map (pairStatScale σ) := by rw [hMP_swap.map_eq]
        _ = P₀.map (pairStatScale σ ∘ swapPairGen) :=
            Measure.map_map (measurable_pairStatScale σ) measurable_swapPairGen
        _ = P₀.map (fun q ↦ (W₀' q, W₀ q)) :=
            congrArg (fun f ↦ P₀.map f) (funext fun q ↦ pairStatScale_swapPairGen σ q)
    have hW₀_meas : Measurable W₀ := hsumScale_meas.comp hVY_meas
    have hW₀_int : Integrable W₀ P₀ :=
      (integrable_finsetSum Finset.univ fun i _ ↦ hY_int i).div_const σ
    have hW₀'_int : Integrable W₀' P₀ := hExch.fst_identDistrib_snd.integrable_snd hW₀_int
    have hmW₀ := hW₀_meas.comap_le
    have hW₀_sm : StronglyMeasurable[MeasurableSpace.comap W₀ inferInstance] W₀ :=
      Measurable.stronglyMeasurable (comap_measurable (m := inferInstance) W₀)
    have hDiff_decomp :
        (fun q ↦ W₀' q - W₀ q) =
          fun q ↦ ∑ k : Fin n,
            {q' | I₀ q' = k}.indicator (fun q' ↦ (Y' k q' - Y k q') / σ) q := by
      funext q
      have hterm : ∀ k : Fin n,
          {q' | I₀ q' = k}.indicator (fun q' ↦ (Y' k q' - Y k q') / σ) q =
            if I₀ q = k then (Y' k q - Y k q) / σ else 0 := fun k ↦ by
        by_cases hk : I₀ q = k <;> simp [hk]
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, W₀']
      ring
    have hCondDiff :
        (fun q ↦ -(1 / (n : ℝ)) * W₀ q) =ᵐ[P₀]
          P₀[fun q ↦ W₀' q - W₀ q | MeasurableSpace.comap W₀ inferInstance] := by
      refine ae_eq_condExp_of_forall_setIntegral_eq hmW₀ (hW₀'_int.sub' hW₀_int)
        (fun _ _ _ ↦ (hW₀_int.const_mul (-(1 / (n : ℝ)))).integrableOn)
        (fun s hs _ ↦ ?_)
        (hW₀_sm.const_mul (-(1 / (n : ℝ)))).aestronglyMeasurable
      rcases hs with ⟨B, hB, rfl⟩
      let T : Set (Fin n → ℝ) := sumScale ⁻¹' B
      have hT : MeasurableSet T := hsumScale_meas hB
      have hpre : W₀ ⁻¹' B = VY ⁻¹' T := rfl
      rw [hpre, hDiff_decomp,
        integral_finsetSum Finset.univ fun k _ ↦
          ((((hY'_int k).sub' (hY_int k)).div_const σ).indicator (hIk_meas k)).integrableOn]
      have hterm_eq : ∀ k : Fin n,
          ∫ q in VY ⁻¹' T,
              {q' | I₀ q' = k}.indicator (fun q' ↦ (Y' k q' - Y k q') / σ) q ∂P₀ =
            -(1 / (n : ℝ)) * ∫ q in VY ⁻¹' T, Y k q / σ ∂P₀ := fun k ↦ by
        let Hk : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦ (p.2 k - p.1 k) / σ
        have hHk_meas : Measurable Hk := by
          have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 k) :=
            (measurable_pi_apply k).comp measurable_snd
          have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 k) :=
            (measurable_pi_apply k).comp measurable_fst
          exact (h1.sub h2).div_const σ
        have hStep1 :=
          indepSum_setIntegral_indicator_I_vx P₀ hn hY_meas hY'_meas hI₀_meas hI₀_indep hI₀_unif
            k hT hHk_meas
        have hIntY' : ∫ q in VY ⁻¹' T, Y' k q ∂P₀ = 0 := by
          have hmul :=
            indepSum_setIntegral_vx_mul_vx' P₀ hY_meas hY'_meas hYY'_indep hT
              (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ (1 : ℝ)))
              (measurable_pi_apply k)
          simpa only [one_mul, hY'0 k, mul_zero] using hmul
        have hSub :
            ∫ q in VY ⁻¹' T, Hk (VY q, VY' q) ∂P₀ = -∫ q in VY ⁻¹' T, Y k q / σ ∂P₀ := by
          have hfn : (fun q ↦ Hk (VY q, VY' q)) = fun q ↦ Y' k q / σ - Y k q / σ := by
            funext q; dsimp [Hk, VY, VY', Y, Y']; ring
          rw [hfn,
            integral_sub ((hY'_int k).div_const σ).integrableOn
              ((hY_int k).div_const σ).integrableOn,
            integral_div σ (Y' k), hIntY', zero_div, zero_sub]
        rw [hStep1, hSub]
        ring
      have hW₀_split : W₀ = fun q ↦ ∑ k : Fin n, Y k q / σ := by
        funext q; dsimp [W₀, S₀, Y]; rw [Finset.sum_div]
      calc
        ∫ q in VY ⁻¹' T, -(1 / (n : ℝ)) * W₀ q ∂P₀
          = -(1 / (n : ℝ)) * ∫ q in VY ⁻¹' T, W₀ q ∂P₀ := integral_const_mul _ W₀
        _ = -(1 / (n : ℝ)) * ∑ k : Fin n, ∫ q in VY ⁻¹' T, Y k q / σ ∂P₀ := by
            rw [hW₀_split,
              integral_finsetSum Finset.univ fun k _ ↦ ((hY_int k).div_const σ).integrableOn]
        _ = ∑ k : Fin n, -(1 / (n : ℝ)) * ∫ q in VY ⁻¹' T, Y k q / σ ∂P₀ := by rw [Finset.mul_sum]
        _ = ∑ k : Fin n,
              ∫ q in VY ⁻¹' T,
                {q' | I₀ q' = k}.indicator (fun q' ↦ (Y' k q' - Y k q') / σ) q ∂P₀ :=
            Finset.sum_congr rfl fun k _ ↦ (hterm_eq k).symm
    have hCondW₀ : P₀[W₀ | MeasurableSpace.comap W₀ inferInstance] = W₀ :=
      condExp_of_stronglyMeasurable hmW₀ hW₀_sm hW₀_int
    have hSubAE := condExp_sub hW₀'_int hW₀_int (MeasurableSpace.comap W₀ inferInstance)
    have hCond :
        P₀[W₀' | MeasurableSpace.comap W₀ inferInstance] =ᵐ[P₀]
          fun q ↦ (1 - 1 / (n : ℝ)) * W₀ q := by
      filter_upwards [hCondDiff.symm, hSubAE] with q hq1 hq2
      have hq : P₀[W₀' | MeasurableSpace.comap W₀ inferInstance] q - W₀ q =
          -(1 / (n : ℝ)) * W₀ q := by
        have hsub := hq2.symm.trans hq1
        rwa [Pi.sub_apply, hCondW₀] at hsub
      linarith
    exact ⟨hExch, div_pos zero_lt_one hrn_pos, div_le_one_of_le₀ hrn_ge1 hrn_pos.le,
      hW₀_meas, hW₀_int, hCond⟩
  -- Step 2: Evaluate `P₀[(W₀' - W₀)^2 | comap VY]` as `R₀`.
  have hCondSq :
      P₀[fun q ↦ (W₀' q - W₀ q) ^ 2 | MeasurableSpace.comap VY inferInstance] =ᵐ[P₀] R₀ := by
    let D2 : Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ := fun q ↦ (W₀' q - W₀ q) ^ 2
    have hYY'_mul_int : ∀ i : Fin n, Integrable (fun q ↦ Y i q * Y' i q) P₀ := fun i ↦ by
      have hY_L2 := (memLp_two_iff_integrable_sq (hY_meas i).aestronglyMeasurable).mpr (hY_sq_int i)
      have hY'_L2 :=
        (memLp_two_iff_integrable_sq (hY'_meas i).aestronglyMeasurable).mpr (hY'_sq_int i)
      exact hY_L2.integrable_mul hY'_L2
    have hD2_decomp :
        D2 = fun q ↦ ∑ i : Fin n,
          {q' | I₀ q' = i}.indicator (fun q' ↦ (Y' i q' - Y i q') ^ 2 / σ ^ 2) q := by
      funext q
      have hterm : ∀ i : Fin n,
          {q' | I₀ q' = i}.indicator (fun q' ↦ (Y' i q' - Y i q') ^ 2 / σ ^ 2) q =
            if I₀ q = i then (Y' i q - Y i q) ^ 2 / σ ^ 2 else 0 := fun i ↦ by
        by_cases hi : I₀ q = i <;> simp [hi]
      simp_rw [hterm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, D2, W₀', Y, Y', I₀]
      have hsub : W₀ q - q.2.1 q.1 / σ + q.2.2 q.1 / σ - W₀ q = (q.2.2 q.1 - q.2.1 q.1) / σ := by
        ring
      rw [hsub, div_pow]
    have hTerm_int : ∀ i : Fin n, Integrable
        ({q' | I₀ q' = i}.indicator (fun q' ↦ (Y' i q' - Y i q') ^ 2 / σ ^ 2)) P₀ := fun i ↦ by
      have hexp : (fun q' ↦ (Y' i q' - Y i q') ^ 2 / σ ^ 2) =
          fun q' ↦ ((Y' i q' ^ 2 + Y i q' ^ 2) - 2 * (Y i q' * Y' i q')) / σ ^ 2 := by
        funext q'; ring
      rw [hexp]
      exact (((((hY'_sq_int i).fun_add (hY_sq_int i)).sub'
        ((hYY'_mul_int i).const_mul 2)).div_const (σ ^ 2))).indicator (hIk_meas i)
    have hD2_int : Integrable D2 P₀ :=
      hD2_decomp ▸ integrable_finsetSum Finset.univ fun i _ ↦ hTerm_int i
    have hR₀_int : Integrable R₀ P₀ :=
      (integrable_finsetSum Finset.univ fun i _ ↦
        (hY_sq_int i).fun_add (integrable_const _)).const_mul _
    have hR₀_sm : StronglyMeasurable[MeasurableSpace.comap VY inferInstance] R₀ := by
      let φ : (Fin n → ℝ) → ℝ := fun v ↦
        (1 / ((n : ℝ) * σ ^ 2)) * ∑ i : Fin n, (v i ^ 2 + ProbabilityTheory.variance id (μ i))
      have hφ_meas : Measurable φ :=
        measurable_const.mul (Finset.measurable_sum Finset.univ fun i _ ↦
          ((measurable_pi_apply i).pow_const 2).add measurable_const)
      exact (hφ_meas.comp (comap_measurable (m := inferInstance) VY)).stronglyMeasurable
    refine (ae_eq_condExp_of_forall_setIntegral_eq hVY_meas.comap_le hD2_int
      (fun _ _ _ ↦ hR₀_int.integrableOn) (fun s hs _ ↦ ?_) hR₀_sm.aestronglyMeasurable).symm
    rcases hs with ⟨T, hT, rfl⟩
    rw [hD2_decomp, integral_finsetSum Finset.univ fun i _ ↦ (hTerm_int i).integrableOn]
    have hterm_eq : ∀ i : Fin n,
        ∫ q in VY ⁻¹' T,
            {q' | I₀ q' = i}.indicator (fun q' ↦ (Y' i q' - Y i q') ^ 2 / σ ^ 2) q ∂P₀ =
          (1 / ((n : ℝ) * σ ^ 2)) *
            ∫ q in VY ⁻¹' T, (Y i q ^ 2 + ProbabilityTheory.variance id (μ i)) ∂P₀ := fun i ↦ by
      let Hi : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦ (p.2 i - p.1 i) ^ 2 / σ ^ 2
      have hHi_meas : Measurable Hi := by
        have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.2 i) :=
          (measurable_pi_apply i).comp measurable_snd
        have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) ↦ p.1 i) :=
          (measurable_pi_apply i).comp measurable_fst
        exact ((h1.sub h2).pow_const 2).div_const (σ ^ 2)
      have hStep :=
        indepSum_setIntegral_indicator_I_vx P₀ hn hY_meas hY'_meas hI₀_meas hI₀_indep hI₀_unif i
          hT hHi_meas
      have hY'_sq_eq : ∫ q, Y' i q ^ 2 ∂P₀ = ProbabilityTheory.variance id (μ i) := by
        calc
          ∫ q, Y' i q ^ 2 ∂P₀ = ∫ x, x ^ 2 ∂(P₀.map (Y' i)) :=
            (integral_map (hY'_meas i).aemeasurable
              (measurable_id.pow_const 2).aestronglyMeasurable).symm
          _ = ∫ x, x ^ 2 ∂(μ i) := by rw [(hMP_Y' i).map_eq]
          _ = ProbabilityTheory.variance id (μ i) :=
            (ProbabilityTheory.variance_of_integral_eq_zero aemeasurable_id (hμ0 i)).symm
      have hIntY'_sq :
          ∫ q in VY ⁻¹' T, Y' i q ^ 2 ∂P₀ =
            ∫ q in VY ⁻¹' T, ProbabilityTheory.variance id (μ i) ∂P₀ := by
        have hmul :=
          indepSum_setIntegral_vx_mul_vx' P₀ hY_meas hY'_meas hYY'_indep hT
            (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ (1 : ℝ)))
            ((measurable_pi_apply i).pow_const 2)
        calc
          ∫ q in VY ⁻¹' T, Y' i q ^ 2 ∂P₀
            = (∫ q in VY ⁻¹' T, (1 : ℝ) ∂P₀) * ∫ q, Y' i q ^ 2 ∂P₀ := by
              simpa only [one_mul] using hmul
          _ = ∫ q in VY ⁻¹' T, ProbabilityTheory.variance id (μ i) ∂P₀ := by
              rw [hY'_sq_eq, integral_const, integral_const, smul_eq_mul, smul_eq_mul, mul_one]
      have hIntCross : ∫ q in VY ⁻¹' T, Y i q * Y' i q ∂P₀ = 0 := by
        have hmul :=
          indepSum_setIntegral_vx_mul_vx' P₀ hY_meas hY'_meas hYY'_indep hT
            (measurable_pi_apply i) (measurable_pi_apply i)
        simpa only [hY'0 i, mul_zero] using hmul
      have hexp :
          (fun q ↦ Hi (VY q, VY' q)) =
            fun q ↦ ((Y' i q ^ 2 + Y i q ^ 2) - 2 * (Y i q * Y' i q)) / σ ^ 2 := by
        funext q; dsimp [Hi, VY, VY', Y, Y']; ring
      have hEvalHi :
          ∫ q in VY ⁻¹' T, Hi (VY q, VY' q) ∂P₀ =
            (1 / σ ^ 2) *
              ∫ q in VY ⁻¹' T, (Y i q ^ 2 + ProbabilityTheory.variance id (μ i)) ∂P₀ := by
        rw [hexp, integral_div,
          integral_sub ((hY'_sq_int i).fun_add (hY_sq_int i)).integrableOn
            ((hYY'_mul_int i).const_mul 2).integrableOn,
          integral_add (hY'_sq_int i).integrableOn (hY_sq_int i).integrableOn,
          integral_const_mul 2 (fun q ↦ Y i q * Y' i q), hIntY'_sq, hIntCross,
          integral_add (hY_sq_int i).integrableOn (integrable_const _).integrableOn]
        ring
      rw [hStep, hEvalHi]
      ring
    calc
      ∫ q in VY ⁻¹' T, R₀ q ∂P₀
        = (1 / ((n : ℝ) * σ ^ 2)) *
            ∫ q in VY ⁻¹' T,
              (∑ i : Fin n, (Y i q ^ 2 + ProbabilityTheory.variance id (μ i))) ∂P₀ :=
          integral_const_mul _ _
      _ = (1 / ((n : ℝ) * σ ^ 2)) *
            ∑ i : Fin n,
              ∫ q in VY ⁻¹' T, (Y i q ^ 2 + ProbabilityTheory.variance id (μ i)) ∂P₀ := by
          rw [integral_finsetSum Finset.univ fun i _ ↦
            ((hY_sq_int i).fun_add (integrable_const _)).integrableOn]
      _ = ∑ i : Fin n,
            (1 / ((n : ℝ) * σ ^ 2)) *
              ∫ q in VY ⁻¹' T, (Y i q ^ 2 + ProbabilityTheory.variance id (μ i)) ∂P₀ := by
          rw [Finset.mul_sum]
      _ = ∑ i : Fin n,
            ∫ q in VY ⁻¹' T,
              {q' | I₀ q' = i}.indicator (fun q' ↦ (Y' i q' - Y i q') ^ 2 / σ ^ 2) q ∂P₀ :=
          Finset.sum_congr rfl fun i _ ↦ (hterm_eq i).symm
  -- Step 3: Apply Theorem 3.28 + Remark 3.4 and evaluate `Var(R₀)`.
  have hMain :=
    hSP.kolmogorovDist_le_of_condExp_ae_eq P' hVarW₀ hδ hmW₀_VY hVY_meas hCondSq hZ hZ_law
  have hY_indep : ProbabilityTheory.iIndepFun Y P₀ := by
    refine (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i ↦ (hY_meas i).aemeasurable)).mpr ?_
    have heq : (fun i ↦ P₀.map (Y i)) = μ := funext fun i ↦ (hMP_Y i).map_eq
    rw [heq]
    exact hπY.map_eq
  let Zsq : Fin n → Fin n × ((Fin n → ℝ) × (Fin n → ℝ)) → ℝ :=
    fun i q ↦ Y i q ^ 2 + ProbabilityTheory.variance id (μ i)
  have hZsq_indep : ProbabilityTheory.iIndepFun Zsq P₀ :=
    hY_indep.comp (fun i x ↦ x ^ 2 + ProbabilityTheory.variance id (μ i))
      (fun _ ↦ (measurable_id.pow_const 2).add measurable_const)
  have hZsq_L2 : ∀ i : Fin n, MemLp (Zsq i) 2 P₀ :=
    fun i ↦ (hYsq_L2 i).add (memLp_const _)
  have hVarYsq : ∀ i : Fin n,
      ProbabilityTheory.variance (fun q ↦ Y i q ^ 2) P₀ =
        ProbabilityTheory.variance (fun ω ↦ X i ω ^ 2) P := fun i ↦ by
    have hsq_aem : AEMeasurable (fun x : ℝ ↦ x ^ 2) (P₀.map (Y i)) :=
      (measurable_id.pow_const 2).aemeasurable
    have hsq_aemX : AEMeasurable (fun x : ℝ ↦ x ^ 2) (P.map (X i)) :=
      (measurable_id.pow_const 2).aemeasurable
    calc
      ProbabilityTheory.variance (fun q ↦ Y i q ^ 2) P₀
        = ProbabilityTheory.variance (fun x : ℝ ↦ x ^ 2) (P₀.map (Y i)) :=
          (ProbabilityTheory.variance_map hsq_aem (hY_meas i).aemeasurable).symm
      _ = ProbabilityTheory.variance (fun x : ℝ ↦ x ^ 2) (P.map (X i)) := by
          rw [(hMP_Y i).map_eq]
      _ = ProbabilityTheory.variance (fun ω ↦ X i ω ^ 2) P :=
          ProbabilityTheory.variance_map hsq_aemX (hX_meas i)
  have hVarR₀ :
      ProbabilityTheory.variance R₀ P₀ =
        (1 / ((n : ℝ) * σ ^ 2)) ^ 2 *
          ∑ i : Fin n, ProbabilityTheory.variance (fun ω ↦ X i ω ^ 2) P := by
    have hR₀_eq : R₀ = fun q ↦ (1 / ((n : ℝ) * σ ^ 2)) * (∑ i : Fin n, Zsq i) q := by
      funext q; simp [R₀, Zsq]
    rw [hR₀_eq, ProbabilityTheory.variance_const_mul,
      ProbabilityTheory.IndepFun.variance_sum (fun i _ ↦ hZsq_L2 i)
        (fun i _ j _ hij ↦ hZsq_indep.indepFun hij)]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp [Zsq]
    rw [ProbabilityTheory.variance_add_const ((hY_meas i).pow_const 2).aestronglyMeasurable,
      hVarYsq i]
  set V4 : ℝ := ∑ i : Fin n, ProbabilityTheory.variance (fun ω ↦ X i ω ^ 2) P
  have hAlg :
      Real.sqrt (ProbabilityTheory.variance R₀ P₀) / (2 * (1 / (n : ℝ))) +
          (2 * C / σ) ^ 3 / (2 * (1 / (n : ℝ))) +
          3 * (2 * C / σ) / 2 =
        Real.sqrt V4 / (2 * σ ^ 2) +
          4 * (n : ℝ) * C ^ 3 / σ ^ 3 +
          3 * C / σ := by
    have hc_nn : 0 ≤ 1 / ((n : ℝ) * σ ^ 2) := by positivity
    have hsqrt :
        Real.sqrt (ProbabilityTheory.variance R₀ P₀) =
          (1 / ((n : ℝ) * σ ^ 2)) * Real.sqrt V4 := by
      rw [hVarR₀, Real.sqrt_mul (sq_nonneg _) V4, Real.sqrt_sq hc_nn]
    rw [hsqrt]
    have hrn_ne : (n : ℝ) ≠ 0 := hrn_pos.ne'
    field_simp [hrn_ne, hσ_ne]
    ring
  rwa [hMapW, hAlg] at hMain

end SteinMethod
