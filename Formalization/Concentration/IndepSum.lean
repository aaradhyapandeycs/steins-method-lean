/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.IndepSumPair

/-!
# Concentration for Sums of Independent Random Variables (`Formalization.Concentration.IndepSum`)

Formalizes **Example 7.4** (`SteinIntro.tex:3497-3537`) from Section 7 of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `indepSum_unscaled_isSteinPair` (re-exported from `Formalization.Concentration.IndepSumPair`):
  **Example 7.4** Stein-pair setup (`Ex7_4_steinPair`, `SteinIntro.tex:3497-3502`).
* `indepSum_hoeffding_tail_bound` (**Example 7.4(1)**, `Ex7_4_1`, `SteinIntro.tex:3503-3515`):
  Hoeffding-type bound $\mathbb{P}(|W - \mathbb{E}[W]| \ge t) \le
  2\exp(-t^2 / \sum_{i=1}^n (\sigma_i^2 + C_i^2))$ under $|X_i - \mu_i| \le C_i$ a.s., together
  with the $\sum_i (\sigma_i^2 + C_i^2) = 0$ boundary vanishing claim (`F1`).
* `indepSum_unitInterval_tail_bound` (**Example 7.4(2)** corrected, `Ex7_4_2_corrected`,
  `\label{21198}`, eq. `(7.2)`, `SteinIntro.tex:3516-3536`; `ISSUE-EX7.4`): concentration bounds
  for $S = \sum_{i=1}^n X_i$ when $0 \le X_i \le 1$ a.s.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-- **Example 7.4(1)** (`Ex7_4_1`, `SteinIntro.tex:3503-3515`): for independent $X_1, \dots, X_n$
with $|X_i - \mathbb{E}[X_i]| \le C_i$ a.s. ($C_i \ge 0$) and $W = \sum_{i=1}^n (X_i - \mu_i)$, for
all $t > 0$,
$\mathbb{P}(|W - \mathbb{E}[W]| \ge t) \le 2\exp(-t^2 / \sum_{i=1}^n (\sigma_i^2 + C_i^2))$, and
when $\sum_{i=1}^n (\sigma_i^2 + C_i^2) = 0$ the tail probability is $0$ (`F1`). -/
theorem indepSum_hoeffding_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {C : Fin n → ℝ}
    (hn : 0 < n)
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hC_nn : ∀ i : Fin n, 0 ≤ C i)
    (hX_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |X i ω - ∫ ω', X i ω' ∂P| ≤ C i) :
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω - ∫ ω', X i ω' ∂P)
    ∀ t : ℝ, 0 < t →
      P.real {ω | t ≤ |W ω - ∫ ω', W ω' ∂P|} ≤
        2 * Real.exp (-t ^ 2 / ∑ i : Fin n, (ProbabilityTheory.variance (X i) P + C i ^ 2)) ∧
      (∑ i : Fin n, (ProbabilityTheory.variance (X i) P + C i ^ 2) = 0 →
        P.real {ω | t ≤ |W ω - ∫ ω', W ω' ∂P|} = 0) := by
  intro W t ht
  let μ : Fin n → ℝ := fun i ↦ ∫ ω', X i ω' ∂P
  have hX2 : ∀ i : Fin n, MemLp (X i) 2 P := by
    intro i
    refine MemLp.of_bound (hX_meas i).aestronglyMeasurable (C i + |μ i|) ?_
    filter_upwards [hX_bdd i] with ω hω
    rw [Real.norm_eq_abs]
    calc
      |X i ω| = |(X i ω - μ i) + μ i| := by ring_nf
      _ ≤ |X i ω - μ i| + |μ i| := abs_add_le _ _
      _ ≤ C i + |μ i| := by linarith
  have hX_int : ∀ i : Fin n, Integrable (X i) P := fun i ↦ (hX2 i).integrable one_le_two
  have hW_mean : ∫ ω', W ω' ∂P = 0 := by
    have hsub_int : ∀ i : Fin n, Integrable (fun ω ↦ X i ω - ∫ ω', X i ω' ∂P) P :=
      fun i ↦ (hX_int i).sub (integrable_const _)
    dsimp only [W]
    rw [integral_finsetSum Finset.univ fun i _ ↦ hsub_int i]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_sub (hX_int i) (integrable_const _), integral_const, probReal_univ, one_smul]
    exact sub_self _
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  have hVX_meas : Measurable VX := .of_eval hX_meas
  let ν : Measure (Fin n → ℝ) := P.map VX
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hVX_meas.aemeasurable).mpr ‹_›
  let μI : Measure (Fin n) := (PMF.uniformOfFintype (Fin n)).toMeasure
  let Ω' := Fin n × ((Fin n → ℝ) × (Fin n → ℝ))
  let Q : Measure Ω' := μI.prod (ν.prod ν)
  let I' : Ω' → Fin n := Prod.fst
  let Y : Fin n → Ω' → ℝ := fun i q ↦ q.2.1 i
  let Y' : Fin n → Ω' → ℝ := fun i q ↦ q.2.2 i
  have hY_meas : ∀ i : Fin n, Measurable (Y i) :=
    fun i ↦ (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hY'_meas : ∀ i : Fin n, Measurable (Y' i) :=
    fun i ↦ (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hVY_meas : Measurable (fun q : Ω' ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hVY'_meas : Measurable (fun q : Ω' ↦ q.2.2) := measurable_snd.comp measurable_snd
  have hQ_snd : Q.map Prod.snd = ν.prod ν := by
    dsimp only [Q]; rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hQ_VY : Q.map (fun q : Ω' ↦ q.2.1) = ν := by
    calc
      Q.map (Prod.fst ∘ Prod.snd) = (Q.map Prod.snd).map Prod.fst :=
        (Measure.map_map measurable_fst measurable_snd).symm
      _ = (ν.prod ν).map Prod.fst := by rw [hQ_snd]
      _ = ν := by simp
  have hQ_VY' : Q.map (fun q : Ω' ↦ q.2.2) = ν := by
    calc
      Q.map (Prod.snd ∘ Prod.snd) = (Q.map Prod.snd).map Prod.snd :=
        (Measure.map_map measurable_snd measurable_snd).symm
      _ = (ν.prod ν).map Prod.snd := by rw [hQ_snd]
      _ = ν := by simp
  have hMapYi : ∀ i : Fin n, Q.map (Y i) = P.map (X i) := by
    intro i
    calc
      Q.map ((fun v : Fin n → ℝ ↦ v i) ∘ fun q : Ω' ↦ q.2.1)
          = (Q.map (fun q : Ω' ↦ q.2.1)).map (fun v ↦ v i) :=
            (Measure.map_map (measurable_pi_apply i) hVY_meas).symm
      _ = (P.map VX).map (fun v ↦ v i) := by rw [hQ_VY]
      _ = P.map (X i) := Measure.map_map (measurable_pi_apply i) hVX_meas
  have hMapVX_pi : ν = Measure.pi (fun i ↦ P.map (X i)) :=
    ProbabilityTheory.iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX_meas i).aemeasurable) h_indep
  have hY_indep : ProbabilityTheory.iIndepFun Y Q := by
    rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hY_meas i).aemeasurable)]
    change Q.map (fun q : Ω' ↦ q.2.1) = Measure.pi (fun i ↦ Q.map (Y i))
    rw [hQ_VY, hMapVX_pi]
    congr 1; funext i; exact (hMapYi i).symm
  have hId_YY' : ProbabilityTheory.IdentDistrib (fun q i ↦ Y' i q) (fun q i ↦ Y i q) Q Q :=
    ⟨hVY'_meas.aemeasurable, hVY_meas.aemeasurable, hQ_VY'.trans hQ_VY.symm⟩
  have hYY'_indep : ProbabilityTheory.IndepFun (fun q i ↦ Y' i q) (fun q i ↦ Y i q) Q := by
    rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hVY'_meas.aemeasurable hVY_meas.aemeasurable]
    calc
      Q.map (Prod.swap ∘ Prod.snd) = (Q.map Prod.snd).map Prod.swap :=
        (Measure.map_map measurable_swap measurable_snd).symm
      _ = (ν.prod ν).map Prod.swap := by rw [hQ_snd]
      _ = ν.prod ν := Measure.prod_swap
      _ = (Q.map (fun q : Ω' ↦ q.2.2)).prod (Q.map (fun q : Ω' ↦ q.2.1)) := by
        rw [hQ_VY', hQ_VY]
  have hI'_indep : ProbabilityTheory.IndepFun I' (fun q : Ω' ↦ (q.2.1, q.2.2)) Q :=
    ProbabilityTheory.indepFun_prod measurable_id measurable_id
  have hI'_unif : Q.map I' = μI := by
    dsimp only [Q, I']; rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hId_Xi : ∀ i : Fin n, IdentDistrib (Y i) (X i) Q P :=
    fun i ↦ ⟨(hY_meas i).aemeasurable, (hX_meas i).aemeasurable, hMapYi i⟩
  have hY2 : ∀ i : Fin n, MemLp (Y i) 2 Q :=
    fun i ↦ (hId_Xi i).memLp_iff.mpr (hX2 i)
  have hY_mean : ∀ i : Fin n, ∫ q, Y i q ∂Q = μ i :=
    fun i ↦ (hId_Xi i).integral_eq
  have hY_var : ∀ i : Fin n, ProbabilityTheory.variance (Y i) Q =
      ProbabilityTheory.variance (X i) P :=
    fun i ↦ (hId_Xi i).variance_eq
  have hY_bdd : ∀ i : Fin n, ∀ᵐ q ∂Q, |Y i q - μ i| ≤ C i := by
    intro i
    have hmeas : MeasurableSet {x : ℝ | |x - μ i| ≤ C i} :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable measurableSet_Iic
    have hP : (P.map (X i)) {x : ℝ | |x - μ i| ≤ C i}ᶜ = 0 := by
      rw [Measure.map_apply (hX_meas i) hmeas.compl]
      exact ae_iff.mp (hX_bdd i)
    rw [ae_iff]
    change Q ((Y i) ⁻¹' {x : ℝ | |x - μ i| ≤ C i}ᶜ) = 0
    rw [← Measure.map_apply (hY_meas i) hmeas.compl, hMapYi i]
    exact hP
  have hY'_bdd : ∀ i : Fin n, ∀ᵐ q ∂Q, |Y' i q - μ i| ≤ C i := by
    intro i
    have hId_i : IdentDistrib (Y' i) (Y i) Q Q := hId_YY'.comp (measurable_pi_apply i)
    have hmeas : MeasurableSet {x : ℝ | |x - μ i| ≤ C i} :=
      (continuous_abs.comp (continuous_id.sub continuous_const)).measurable measurableSet_Iic
    rw [ae_iff]
    change Q ((Y' i) ⁻¹' {x : ℝ | |x - μ i| ≤ C i}ᶜ) = 0
    rw [← Measure.map_apply (hY'_meas i) hmeas.compl, hId_i.map_eq,
      Measure.map_apply (hY_meas i) hmeas.compl]
    exact ae_iff.mp (hY_bdd i)
  let WQ : Ω' → ℝ := fun q ↦ ∑ i : Fin n, (Y i q - ∫ q', Y i q' ∂Q)
  let W'Q : Ω' → ℝ := fun q ↦ WQ q - Y (I' q) q + Y' (I' q) q
  have hSP : IsSteinPair Q (1 / (n : ℝ)) WQ W'Q :=
    indepSum_unscaled_isSteinPair Q hn hY_meas hY'_meas hY_indep hY2 hId_YY' hYY'_indep
      measurable_fst hI'_indep hI'_unif
  have hWQ_eq : WQ = fun q ↦ ∑ i : Fin n, (Y i q - μ i) := by
    funext q; simp only [WQ, hY_mean]
  have hWQ2 : MemLp WQ 2 Q := by
    rw [hWQ_eq]
    exact memLp_finsetSum Finset.univ fun i _ ↦ (hY2 i).sub (memLp_const (μ i))
  let M : ℝ := ∑ i : Fin n, C i
  have hM_nn : 0 ≤ M := Finset.sum_nonneg fun i _ ↦ hC_nn i
  have hWQ_bdd : ∀ᵐ q ∂Q, |WQ q| ≤ M := by
    have hall : ∀ᵐ q ∂Q, ∀ i : Fin n, |Y i q - μ i| ≤ C i :=
      ae_all_iff.mpr hY_bdd
    filter_upwards [hall] with q hq
    rw [hWQ_eq]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ hq i)
  have hDiff_bdd : ∀ᵐ q ∂Q, |W'Q q - WQ q| ≤ 2 * M := by
    have hallY : ∀ᵐ q ∂Q, ∀ i : Fin n, |Y i q - μ i| ≤ C i := ae_all_iff.mpr hY_bdd
    have hallY' : ∀ᵐ q ∂Q, ∀ i : Fin n, |Y' i q - μ i| ≤ C i := ae_all_iff.mpr hY'_bdd
    filter_upwards [hallY, hallY'] with q hqY hqY'
    have h1 : C (I' q) ≤ M :=
      Finset.single_le_sum (fun i _ ↦ hC_nn i) (Finset.mem_univ (I' q))
    calc
      |W'Q q - WQ q| = |(Y' (I' q) q - μ (I' q)) - (Y (I' q) q - μ (I' q))| := by
        dsimp [W'Q]; ring_nf
      _ ≤ |Y' (I' q) q - μ (I' q)| + |Y (I' q) q - μ (I' q)| := abs_sub _ _
      _ ≤ C (I' q) + C (I' q) := add_le_add (hqY' (I' q)) (hqY (I' q))
      _ ≤ 2 * M := by linarith
  have hWQ_meas : Measurable WQ :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hY_meas i).sub measurable_const
  have hW'Q_meas : Measurable W'Q := by
    have he1 : Measurable (fun q : Ω' ↦ Y (I' q) q) := by
      have heq : (fun q : Ω' ↦ Y (I' q) q) =
          fun q ↦ ∑ i : Fin n, if I' q = i then Y i q else 0 := by funext q; simp
      rw [heq]
      refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
      have hs : {q : Ω' | I' q = i} = Prod.fst ⁻¹' {i} := by ext q; simp [I']
      exact Measurable.ite (hs ▸ measurable_fst (measurableSet_singleton i))
        (hY_meas i) measurable_const
    have he2 : Measurable (fun q : Ω' ↦ Y' (I' q) q) := by
      have heq : (fun q : Ω' ↦ Y' (I' q) q) =
          fun q ↦ ∑ i : Fin n, if I' q = i then Y' i q else 0 := by funext q; simp
      rw [heq]
      refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
      have hs : {q : Ω' | I' q = i} = Prod.fst ⁻¹' {i} := by ext q; simp [I']
      exact Measurable.ite (hs ▸ measurable_fst (measurableSet_singleton i))
        (hY'_meas i) measurable_const
    exact (hWQ_meas.sub he1).add he2
  have hmgf : ∀ θ : ℝ, Integrable (fun q ↦ Real.exp (θ * WQ q) * |W'Q q - WQ q|) Q := by
    intro θ
    have hmeas : Measurable (fun q ↦ Real.exp (θ * WQ q) * |W'Q q - WQ q|) :=
      (Real.continuous_exp.measurable.comp (measurable_const.mul hWQ_meas)).mul
        (continuous_abs.measurable.comp (hW'Q_meas.sub hWQ_meas))
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp (|θ| * M) * (2 * M)) ?_
    filter_upwards [hWQ_bdd, hDiff_bdd] with q hqW hqD
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
    refine mul_le_mul ?_ hqD (abs_nonneg _) (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by rw [abs_mul]; gcongr))
  have hmW_le : MeasurableSpace.comap WQ inferInstance ≤
      MeasurableSpace.comap (fun q : Ω' ↦ q.2.1) inferInstance := by
    have hfactor : WQ = (fun v : Fin n → ℝ ↦ ∑ i : Fin n, (v i - μ i)) ∘ fun q : Ω' ↦ q.2.1 := by
      rw [hWQ_eq]; rfl
    rw [hfactor, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (Finset.measurable_sum Finset.univ fun i _ ↦
        (measurable_pi_apply i).sub measurable_const).comap_le
  let sumVarC : ℝ := ∑ i : Fin n, (ProbabilityTheory.variance (X i) P + C i ^ 2)
  have hsumVarC_nn : 0 ≤ sumVarC :=
    Finset.sum_nonneg fun i _ ↦ add_nonneg (ProbabilityTheory.variance_nonneg _ _) (sq_nonneg _)
  have hCondEq := indepSum_condExp_sq_diff Q hn hY_meas hY'_meas hY2 hId_YY' hYY'_indep
    measurable_fst hI'_indep hI'_unif
  have hCondBound :
      ∀ᵐ q ∂Q,
        Q[fun q' ↦ (W'Q q' - WQ q') ^ 2 |
            MeasurableSpace.comap (fun q : Ω' ↦ q.2.1) inferInstance] q / (2 * (1 / (n : ℝ))) ≤
          0 * WQ q + sumVarC / 2 := by
    have hallY : ∀ᵐ q ∂Q, ∀ i : Fin n, |Y i q - μ i| ≤ C i := ae_all_iff.mpr hY_bdd
    have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    filter_upwards [hCondEq, hallY] with q hqEq hqBdd
    rw [hqEq, zero_mul, zero_add]
    have hterm : ∀ k : Fin n,
        (∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2 ≤
          ProbabilityTheory.variance (X k) P + C k ^ 2 := by
      intro k
      have hvar_k : ProbabilityTheory.variance (Y k) Q =
          (∫ q', Y k q' ^ 2 ∂Q) - (μ k) ^ 2 := by
        rw [ProbabilityTheory.variance_eq_integral (hY_meas k).aemeasurable, hY_mean k]
        have hpt : (fun q' ↦ (Y k q' - μ k) ^ 2) =
            fun q' ↦ (Y k q' ^ 2 - 2 * μ k * Y k q') + (μ k) ^ 2 := by funext q'; ring
        have hpt2 : (fun q' ↦ Y k q' ^ 2 - 2 * μ k * Y k q') =
            fun q' ↦ Y k q' ^ 2 - (2 * μ k) * Y k q' := rfl
        have hint1 : Integrable (fun q' ↦ Y k q' ^ 2) Q := (hY2 k).integrable_sq
        have hint2 : Integrable (fun q' ↦ (2 * μ k) * Y k q') Q :=
          ((hY2 k).integrable one_le_two).const_mul (2 * μ k)
        have hint12 : Integrable (fun q' ↦ Y k q' ^ 2 - 2 * μ k * Y k q') Q := hint1.sub hint2
        rw [hpt, integral_add hint12 (integrable_const _), hpt2, integral_sub hint1 hint2,
          integral_const_mul, hY_mean k, integral_const, probReal_univ, one_smul]
        ring
      have hsq_k : (Y k q - μ k) ^ 2 ≤ C k ^ 2 :=
        sq_le_sq.mpr (by rw [abs_of_nonneg (hC_nn k)]; exact hqBdd k)
      rw [← hY_var k, hvar_k, hY_mean k]
      nlinarith [hsq_k]
    have hsum_le :
        ∑ k : Fin n, ((∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2) ≤
          sumVarC :=
      Finset.sum_le_sum fun k _ ↦ hterm k
    calc
      (1 / (n : ℝ)) *
          (∑ k : Fin n, ((∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2)) /
          (2 * (1 / (n : ℝ)))
          = (∑ k : Fin n,
              ((∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2)) / 2 := by
            field_simp [hrn_pos.ne']
      _ ≤ sumVarC / 2 := by linarith
  have hTails := steinPair_tail_bounds Q hSP hWQ2 hmgf hmW_le hVY_meas.comap_le le_rfl
    (div_nonneg hsumVarC_nn zero_le_two) hCondBound ht
  have hLawW : Q.map WQ = P.map W := by
    let sumCtr : (Fin n → ℝ) → ℝ := fun v ↦ ∑ i : Fin n, (v i - μ i)
    have hs_meas : Measurable sumCtr :=
      Finset.measurable_sum Finset.univ fun i _ ↦ (measurable_pi_apply i).sub measurable_const
    calc
      Q.map WQ = Q.map (sumCtr ∘ fun q : Ω' ↦ q.2.1) := by rw [hWQ_eq]; rfl
      _ = (Q.map (fun q : Ω' ↦ q.2.1)).map sumCtr :=
            (Measure.map_map hs_meas hVY_meas).symm
      _ = (P.map VX).map sumCtr := by rw [hQ_VY]
      _ = P.map W := Measure.map_map hs_meas hVX_meas
  have hW_meas_P : Measurable W :=
    Finset.measurable_sum Finset.univ fun i _ ↦ (hX_meas i).sub measurable_const
  have hEventEq : P.real {ω | t ≤ |W ω - ∫ ω', W ω' ∂P|} = Q.real {q | t ≤ |WQ q|} := by
    rw [hW_mean]
    have hset : MeasurableSet {x : ℝ | t ≤ |x|} :=
      continuous_abs.measurable measurableSet_Ici
    have hpreP : {ω | t ≤ |W ω - 0|} = W ⁻¹' {x : ℝ | t ≤ |x|} := by ext ω; simp
    have hpreQ : {q | t ≤ |WQ q|} = WQ ⁻¹' {x : ℝ | t ≤ |x|} := rfl
    rw [hpreP, hpreQ, measureReal_def, measureReal_def,
      ← Measure.map_apply hW_meas_P hset, ← hLawW, Measure.map_apply hWQ_meas hset]
  have hUnion : Q.real {q | t ≤ |WQ q|} ≤ Q.real {q | t ≤ WQ q} + Q.real {q | WQ q ≤ -t} := by
    have hsub : {q | t ≤ |WQ q|} ⊆ {q | t ≤ WQ q} ∪ {q | WQ q ≤ -t} := by
      intro q hq
      change t ≤ |WQ q| at hq
      rcases le_abs.mp hq with h1 | h2
      · exact Or.inl (show t ≤ WQ q from h1)
      · exact Or.inr (show WQ q ≤ -t from by linarith)
    have hmono : Q.real {q | t ≤ |WQ q|} ≤ Q.real ({q | t ≤ WQ q} ∪ {q | WQ q ≤ -t}) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono hsub)
    exact hmono.trans (measureReal_union_le _ _)
  rw [hEventEq]
  refine ⟨?_, ?_⟩
  · calc
      Q.real {q | t ≤ |WQ q|}
          ≤ Q.real {q | t ≤ WQ q} + Q.real {q | WQ q ≤ -t} := hUnion
      _ ≤ Real.exp (-t ^ 2 / (2 * (sumVarC / 2) + 2 * 0 * t)) +
            Real.exp (-t ^ 2 / (2 * (sumVarC / 2))) := add_le_add hTails.1 hTails.2.1
      _ = 2 * Real.exp (-t ^ 2 / sumVarC) := by ring_nf
  · intro hsum0
    have hC0 : sumVarC / 2 = 0 := by dsimp [sumVarC]; rw [hsum0]; ring
    have hU0 : Q.real {q | t ≤ WQ q} = 0 := hTails.2.2.2 rfl hC0
    have hL0 : Q.real {q | WQ q ≤ -t} = 0 := hTails.2.2.1 hC0
    exact le_antisymm (hUnion.trans_eq (by rw [hU0, hL0, add_zero])) measureReal_nonneg

/-- **Example 7.4(2), corrected** (`Ex7_4_2_corrected`, `\label{21198}`, eq. `(7.2)`,
`SteinIntro.tex:3516-3536`; `ISSUE-EX7.4`): for independent $X_1, \dots, X_n$ with
$0 \le X_i \le 1$ a.s., uncentered sum $S = \sum_{i=1}^n X_i$, and $\mu = \mathbb{E}[S]$,
$\mathbb{P}(|S - \mu| \ge t) \le 2\exp(-t^2 / (2\mu + t))$ for all $t > 0$, and when
$\sigma^2 = \operatorname{Var}(S) > 0$,
$\mathbb{P}(|S - \mu|/\sigma \ge t) \le 2\exp(-t^2 / (2\mu/\sigma^2 + t/\sigma))$. -/
theorem indepSum_unitInterval_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    (hn : 0 < n)
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (h_indep : ProbabilityTheory.iIndepFun X P)
    (hX_unit : ∀ i : Fin n, ∀ᵐ ω ∂P, 0 ≤ X i ω ∧ X i ω ≤ 1) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let μ : ℝ := ∫ ω, S ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    (∀ t : ℝ, 0 < t →
        P.real {ω | t ≤ |S ω - μ|} ≤ 2 * Real.exp (-t ^ 2 / (2 * μ + t))) ∧
      (0 < ProbabilityTheory.variance S P →
        ∀ t : ℝ, 0 < t →
          P.real {ω | t ≤ |S ω - μ| / σ} ≤
            2 * Real.exp (-t ^ 2 / (2 * (μ / σ ^ 2) + t / σ))) := by
  intro S μ σ
  let μi : Fin n → ℝ := fun i ↦ ∫ ω', X i ω' ∂P
  have hX2 : ∀ i : Fin n, MemLp (X i) 2 P := by
    intro i
    refine MemLp.of_bound (hX_meas i).aestronglyMeasurable 1 ?_
    filter_upwards [hX_unit i] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
    exact hω.2
  have hX_int : ∀ i : Fin n, Integrable (X i) P := fun i ↦ (hX2 i).integrable one_le_two
  have hμ_eq : μ = ∑ i : Fin n, μi i := by
    dsimp [μ, S]
    exact integral_finsetSum Finset.univ fun i _ ↦ hX_int i
  have hμi_nn : ∀ i : Fin n, 0 ≤ μi i :=
    fun i ↦ integral_nonneg_of_ae ((hX_unit i).mono fun _ h ↦ h.1)
  have hμ_nn : 0 ≤ μ := by
    rw [hμ_eq]
    exact Finset.sum_nonneg fun i _ ↦ hμi_nn i
  have hMain : ∀ t : ℝ, 0 < t →
      P.real {ω | t ≤ |S ω - μ|} ≤ 2 * Real.exp (-t ^ 2 / (2 * μ + t)) := by
    intro t ht
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
    have hVX_meas : Measurable VX := .of_eval hX_meas
    let ν : Measure (Fin n → ℝ) := P.map VX
    have : IsProbabilityMeasure ν :=
      (Measure.isProbabilityMeasure_map_iff hVX_meas.aemeasurable).mpr ‹_›
    let μI : Measure (Fin n) := (PMF.uniformOfFintype (Fin n)).toMeasure
    let Ω' := Fin n × ((Fin n → ℝ) × (Fin n → ℝ))
    let Q : Measure Ω' := μI.prod (ν.prod ν)
    let I' : Ω' → Fin n := Prod.fst
    let Y : Fin n → Ω' → ℝ := fun i q ↦ q.2.1 i
    let Y' : Fin n → Ω' → ℝ := fun i q ↦ q.2.2 i
    have hY_meas : ∀ i : Fin n, Measurable (Y i) :=
      fun i ↦ (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
    have hY'_meas : ∀ i : Fin n, Measurable (Y' i) :=
      fun i ↦ (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
    have hVY_meas : Measurable (fun q : Ω' ↦ q.2.1) := measurable_fst.comp measurable_snd
    have hVY'_meas : Measurable (fun q : Ω' ↦ q.2.2) := measurable_snd.comp measurable_snd
    have hQ_snd : Q.map Prod.snd = ν.prod ν := by
      dsimp only [Q]; rw [Measure.map_snd_prod, measure_univ, one_smul]
    have hQ_VY : Q.map (fun q : Ω' ↦ q.2.1) = ν := by
      calc
        Q.map (Prod.fst ∘ Prod.snd) = (Q.map Prod.snd).map Prod.fst :=
          (Measure.map_map measurable_fst measurable_snd).symm
        _ = (ν.prod ν).map Prod.fst := by rw [hQ_snd]
        _ = ν := by simp
    have hQ_VY' : Q.map (fun q : Ω' ↦ q.2.2) = ν := by
      calc
        Q.map (Prod.snd ∘ Prod.snd) = (Q.map Prod.snd).map Prod.snd :=
          (Measure.map_map measurable_snd measurable_snd).symm
        _ = (ν.prod ν).map Prod.snd := by rw [hQ_snd]
        _ = ν := by simp
    have hMapYi : ∀ i : Fin n, Q.map (Y i) = P.map (X i) := by
      intro i
      calc
        Q.map ((fun v : Fin n → ℝ ↦ v i) ∘ fun q : Ω' ↦ q.2.1)
            = (Q.map (fun q : Ω' ↦ q.2.1)).map (fun v ↦ v i) :=
              (Measure.map_map (measurable_pi_apply i) hVY_meas).symm
        _ = (P.map VX).map (fun v ↦ v i) := by rw [hQ_VY]
        _ = P.map (X i) := Measure.map_map (measurable_pi_apply i) hVX_meas
    have hMapVX_pi : ν = Measure.pi (fun i ↦ P.map (X i)) :=
      ProbabilityTheory.iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX_meas i).aemeasurable) h_indep
    have hY_indep : ProbabilityTheory.iIndepFun Y Q := by
      rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hY_meas i).aemeasurable)]
      change Q.map (fun q : Ω' ↦ q.2.1) = Measure.pi (fun i ↦ Q.map (Y i))
      rw [hQ_VY, hMapVX_pi]
      congr 1; funext i; exact (hMapYi i).symm
    have hId_YY' : ProbabilityTheory.IdentDistrib (fun q i ↦ Y' i q) (fun q i ↦ Y i q) Q Q :=
      ⟨hVY'_meas.aemeasurable, hVY_meas.aemeasurable, hQ_VY'.trans hQ_VY.symm⟩
    have hYY'_indep : ProbabilityTheory.IndepFun (fun q i ↦ Y' i q) (fun q i ↦ Y i q) Q := by
      rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
        hVY'_meas.aemeasurable hVY_meas.aemeasurable]
      calc
        Q.map (Prod.swap ∘ Prod.snd) = (Q.map Prod.snd).map Prod.swap :=
          (Measure.map_map measurable_swap measurable_snd).symm
        _ = (ν.prod ν).map Prod.swap := by rw [hQ_snd]
        _ = ν.prod ν := Measure.prod_swap
        _ = (Q.map (fun q : Ω' ↦ q.2.2)).prod (Q.map (fun q : Ω' ↦ q.2.1)) := by
          rw [hQ_VY', hQ_VY]
    have hI'_indep : ProbabilityTheory.IndepFun I' (fun q : Ω' ↦ (q.2.1, q.2.2)) Q :=
      ProbabilityTheory.indepFun_prod measurable_id measurable_id
    have hI'_unif : Q.map I' = μI := by
      dsimp only [Q, I']; rw [Measure.map_fst_prod, measure_univ, one_smul]
    have hId_Xi : ∀ i : Fin n, IdentDistrib (Y i) (X i) Q P :=
      fun i ↦ ⟨(hY_meas i).aemeasurable, (hX_meas i).aemeasurable, hMapYi i⟩
    have hY2 : ∀ i : Fin n, MemLp (Y i) 2 Q :=
      fun i ↦ (hId_Xi i).memLp_iff.mpr (hX2 i)
    have hY_mean : ∀ i : Fin n, ∫ q, Y i q ∂Q = μi i :=
      fun i ↦ (hId_Xi i).integral_eq
    have hY_unit : ∀ i : Fin n, ∀ᵐ q ∂Q, 0 ≤ Y i q ∧ Y i q ≤ 1 := by
      intro i
      have hmeas : MeasurableSet (Set.Icc (0 : ℝ) 1) := measurableSet_Icc
      rw [ae_iff]
      change Q ((Y i) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) = 0
      rw [← Measure.map_apply (hY_meas i) hmeas.compl, hMapYi i,
        Measure.map_apply (hX_meas i) hmeas.compl]
      exact ae_iff.mp (hX_unit i)
    have hY'_unit : ∀ i : Fin n, ∀ᵐ q ∂Q, 0 ≤ Y' i q ∧ Y' i q ≤ 1 := by
      intro i
      have hId_i : IdentDistrib (Y' i) (Y i) Q Q := hId_YY'.comp (measurable_pi_apply i)
      have hmeas : MeasurableSet (Set.Icc (0 : ℝ) 1) := measurableSet_Icc
      rw [ae_iff]
      change Q ((Y' i) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) = 0
      rw [← Measure.map_apply (hY'_meas i) hmeas.compl, hId_i.map_eq,
        Measure.map_apply (hY_meas i) hmeas.compl]
      exact ae_iff.mp (hY_unit i)
    let WQ : Ω' → ℝ := fun q ↦ ∑ i : Fin n, (Y i q - ∫ q', Y i q' ∂Q)
    let W'Q : Ω' → ℝ := fun q ↦ WQ q - Y (I' q) q + Y' (I' q) q
    have hSP : IsSteinPair Q (1 / (n : ℝ)) WQ W'Q :=
      indepSum_unscaled_isSteinPair Q hn hY_meas hY'_meas hY_indep hY2 hId_YY' hYY'_indep
        measurable_fst hI'_indep hI'_unif
    have hWQ_eq : WQ = fun q ↦ (∑ i : Fin n, Y i q) - μ := by
      funext q
      simp only [WQ, hY_mean, Finset.sum_sub_distrib, hμ_eq]
    have hWQ2 : MemLp WQ 2 Q := by
      rw [hWQ_eq]
      exact (memLp_finsetSum Finset.univ fun i _ ↦ hY2 i).sub (memLp_const μ)
    have hμi_le1 : ∀ i : Fin n, μi i ≤ 1 := by
      intro i
      calc
        μi i = ∫ ω', X i ω' ∂P := rfl
        _ ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
              integral_mono_ae (hX_int i) (integrable_const 1) ((hX_unit i).mono fun _ h ↦ h.2)
        _ = 1 := by rw [integral_const, probReal_univ, one_smul]
    have hWQ_bdd : ∀ᵐ q ∂Q, |WQ q| ≤ (n : ℝ) := by
      filter_upwards [ae_all_iff.mpr hY_unit] with q hq
      have hS_nn : 0 ≤ ∑ i : Fin n, Y i q := Finset.sum_nonneg fun i _ ↦ (hq i).1
      have hS_le : ∑ i : Fin n, Y i q ≤ (n : ℝ) := by
        calc
          ∑ i : Fin n, Y i q ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ (hq i).2
          _ = (n : ℝ) := by simp
      have hμ_le : μ ≤ (n : ℝ) := by
        rw [hμ_eq]
        calc
          ∑ i : Fin n, μi i ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hμi_le1 i
          _ = (n : ℝ) := by simp
      rw [hWQ_eq, abs_le]
      constructor <;> linarith
    have hDiff_bdd : ∀ᵐ q ∂Q, |W'Q q - WQ q| ≤ 1 := by
      filter_upwards [ae_all_iff.mpr hY_unit, ae_all_iff.mpr hY'_unit] with q hqY hqY'
      have h1 := hqY (I' q)
      have h2 := hqY' (I' q)
      have heq : W'Q q - WQ q = Y' (I' q) q - Y (I' q) q := by dsimp [W'Q]; ring
      rw [heq, abs_le]
      constructor <;> linarith
    have hWQ_meas : Measurable WQ :=
      Finset.measurable_sum Finset.univ fun i _ ↦ (hY_meas i).sub measurable_const
    have hW'Q_meas : Measurable W'Q := by
      have he1 : Measurable (fun q : Ω' ↦ Y (I' q) q) := by
        have heq : (fun q : Ω' ↦ Y (I' q) q) =
            fun q ↦ ∑ i : Fin n, if I' q = i then Y i q else 0 := by funext q; simp
        rw [heq]
        refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
        have hs : {q : Ω' | I' q = i} = Prod.fst ⁻¹' {i} := by ext q; simp [I']
        exact Measurable.ite (hs ▸ measurable_fst (measurableSet_singleton i))
          (hY_meas i) measurable_const
      have he2 : Measurable (fun q : Ω' ↦ Y' (I' q) q) := by
        have heq : (fun q : Ω' ↦ Y' (I' q) q) =
            fun q ↦ ∑ i : Fin n, if I' q = i then Y' i q else 0 := by funext q; simp
        rw [heq]
        refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
        have hs : {q : Ω' | I' q = i} = Prod.fst ⁻¹' {i} := by ext q; simp [I']
        exact Measurable.ite (hs ▸ measurable_fst (measurableSet_singleton i))
          (hY'_meas i) measurable_const
      exact (hWQ_meas.sub he1).add he2
    have hmgf : ∀ θ : ℝ, Integrable (fun q ↦ Real.exp (θ * WQ q) * |W'Q q - WQ q|) Q := by
      intro θ
      have hmeas : Measurable (fun q ↦ Real.exp (θ * WQ q) * |W'Q q - WQ q|) :=
        (Real.continuous_exp.measurable.comp (measurable_const.mul hWQ_meas)).mul
          (continuous_abs.measurable.comp (hW'Q_meas.sub hWQ_meas))
      refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp (|θ| * (n : ℝ)) * 1) ?_
      filter_upwards [hWQ_bdd, hDiff_bdd] with q hqW hqD
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_abs]
      refine mul_le_mul ?_ hqD (abs_nonneg _) (Real.exp_pos _).le
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by rw [abs_mul]; gcongr))
    have hmW_le : MeasurableSpace.comap WQ inferInstance ≤
        MeasurableSpace.comap (fun q : Ω' ↦ q.2.1) inferInstance := by
      have hfactor : WQ = (fun v : Fin n → ℝ ↦ (∑ i : Fin n, v i) - μ) ∘ fun q : Ω' ↦ q.2.1 := by
        rw [hWQ_eq]; rfl
      rw [hfactor, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono
        ((Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i).sub
          measurable_const).comap_le
    have hCondEq := indepSum_condExp_sq_diff Q hn hY_meas hY'_meas hY2 hId_YY' hYY'_indep
      measurable_fst hI'_indep hI'_unif
    have hCondBound :
        ∀ᵐ q ∂Q,
          Q[fun q' ↦ (W'Q q' - WQ q') ^ 2 |
              MeasurableSpace.comap (fun q : Ω' ↦ q.2.1) inferInstance] q / (2 * (1 / (n : ℝ))) ≤
            (1 / 2 : ℝ) * WQ q + μ := by
      have hrn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      filter_upwards [hCondEq, ae_all_iff.mpr hY_unit] with q hqEq hqUnit
      rw [hqEq]
      have hterm : ∀ k : Fin n,
          (∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2 ≤
            μi k + Y k q := by
        intro k
        have hYsq_le : ∫ q', Y k q' ^ 2 ∂Q ≤ μi k := by
          rw [← hY_mean k]
          refine integral_mono_ae (hY2 k).integrable_sq ((hY2 k).integrable one_le_two) ?_
          filter_upwards [hY_unit k] with q' hq'
          nlinarith [hq'.1, hq'.2]
        have hk := hqUnit k
        have hμk := hμi_nn k
        rw [hY_mean k]
        nlinarith [hYsq_le, hk.1, hk.2, mul_nonneg hμk hk.1]
      have hsum_le :
          ∑ k : Fin n, ((∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2) ≤
            ∑ k : Fin n, (μi k + Y k q) :=
        Finset.sum_le_sum fun k _ ↦ hterm k
      have hsum_rhs : ∑ k : Fin n, (μi k + Y k q) = 2 * μ + WQ q := by
        rw [Finset.sum_add_distrib, ← hμ_eq, hWQ_eq]
        ring
      calc
        (1 / (n : ℝ)) *
            (∑ k : Fin n, ((∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2)) /
            (2 * (1 / (n : ℝ)))
            = (∑ k : Fin n,
                ((∫ q', Y k q' ^ 2 ∂Q) - 2 * (∫ q', Y k q' ∂Q) * Y k q + Y k q ^ 2)) / 2 := by
              field_simp [hrn_pos.ne']
        _ ≤ (2 * μ + WQ q) / 2 := by linarith [hsum_le, hsum_rhs]
        _ = (1 / 2 : ℝ) * WQ q + μ := by ring
    have hTails := steinPair_tail_bounds Q hSP hWQ2 hmgf hmW_le hVY_meas.comap_le (by norm_num)
      hμ_nn hCondBound ht
    have hLawW : Q.map WQ = P.map (fun ω ↦ S ω - μ) := by
      let sumSub : (Fin n → ℝ) → ℝ := fun v ↦ (∑ i : Fin n, v i) - μ
      have hs_meas : Measurable sumSub :=
        (Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i).sub measurable_const
      calc
        Q.map WQ = Q.map (sumSub ∘ fun q : Ω' ↦ q.2.1) := by rw [hWQ_eq]; rfl
        _ = (Q.map (fun q : Ω' ↦ q.2.1)).map sumSub :=
              (Measure.map_map hs_meas hVY_meas).symm
        _ = (P.map VX).map sumSub := by rw [hQ_VY]
        _ = P.map (fun ω ↦ S ω - μ) := Measure.map_map hs_meas hVX_meas
    have hS_meas : Measurable (fun ω ↦ S ω - μ) :=
      (Finset.measurable_sum Finset.univ fun i _ ↦ hX_meas i).sub measurable_const
    have hEventEq : P.real {ω | t ≤ |S ω - μ|} = Q.real {q | t ≤ |WQ q|} := by
      have hset : MeasurableSet {x : ℝ | t ≤ |x|} :=
        continuous_abs.measurable measurableSet_Ici
      have hpreP : {ω | t ≤ |S ω - μ|} = (fun ω ↦ S ω - μ) ⁻¹' {x : ℝ | t ≤ |x|} := rfl
      have hpreQ : {q | t ≤ |WQ q|} = WQ ⁻¹' {x : ℝ | t ≤ |x|} := rfl
      rw [hpreP, hpreQ, measureReal_def, measureReal_def,
        ← Measure.map_apply hS_meas hset, ← hLawW, Measure.map_apply hWQ_meas hset]
    have hUnion : Q.real {q | t ≤ |WQ q|} ≤ Q.real {q | t ≤ WQ q} + Q.real {q | WQ q ≤ -t} := by
      have hsub : {q | t ≤ |WQ q|} ⊆ {q | t ≤ WQ q} ∪ {q | WQ q ≤ -t} := by
        intro q hq
        change t ≤ |WQ q| at hq
        rcases le_abs.mp hq with h1 | h2
        · exact Or.inl (show t ≤ WQ q from h1)
        · exact Or.inr (show WQ q ≤ -t from by linarith)
      have hmono : Q.real {q | t ≤ |WQ q|} ≤ Q.real ({q | t ≤ WQ q} ∪ {q | WQ q ≤ -t}) := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono hsub)
      exact hmono.trans (measureReal_union_le _ _)
    have hUpper : Q.real {q | t ≤ WQ q} ≤ Real.exp (-t ^ 2 / (2 * μ + t)) := by
      have h1 := hTails.1
      have heq : 2 * μ + 2 * (1 / 2 : ℝ) * t = 2 * μ + t := by ring
      rwa [heq] at h1
    have hLower : Q.real {q | WQ q ≤ -t} ≤ Real.exp (-t ^ 2 / (2 * μ + t)) := by
      rcases hμ_nn.eq_or_lt with hμ0 | hμ_pos
      · rw [hTails.2.2.1 hμ0.symm]
        exact (Real.exp_pos _).le
      · refine hTails.2.1.trans (Real.exp_le_exp.mpr ?_)
        rw [neg_div, neg_div]
        have h1 : t ^ 2 / (2 * μ + t) ≤ t ^ 2 / (2 * μ) :=
          div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith)
        linarith
    rw [hEventEq]
    linarith [hUnion, hUpper, hLower]
  refine ⟨hMain, fun hVar t ht ↦ ?_⟩
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  have hσ_sq : σ ^ 2 = ProbabilityTheory.variance S P := Real.sq_sqrt hVar.le
  have hEvent : {ω | t ≤ |S ω - μ| / σ} = {ω | σ * t ≤ |S ω - μ|} := by
    ext ω
    change t ≤ |S ω - μ| / σ ↔ σ * t ≤ |S ω - μ|
    rw [le_div_iff₀ hσ_pos, mul_comm]
  rw [hEvent]
  refine (hMain (σ * t) (mul_pos hσ_pos ht)).trans_eq ?_
  congr 2
  have hden1 : 2 * μ + σ * t ≠ 0 := by positivity
  have hden2 : 2 * (μ / σ ^ 2) + t / σ ≠ 0 := by positivity
  field_simp [hσ_pos.ne', hden1, hden2]

end SteinMethod
