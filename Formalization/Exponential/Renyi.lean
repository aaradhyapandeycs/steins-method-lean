/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.GeometricSums

/-!
# Section 5.2: Rényi's Theorem (`Formalization.Exponential.Renyi`)

Theorem 5.6 (Rényi's Theorem, unlabeled, `SteinIntro.tex:2905-2911`): for any non-negative
mean-$1$ law $\mathcal{L}(X_0)$ (requiring $L^1$ only, with no finite second-moment assumption),
$\lim_{p \to 0^+} d_{\mathrm{K}}(\mathcal{L}(p \sum_{i=1}^{N_p} X_{p, i}), \mathcal{L}(Z)) = 0$ for
$Z \sim \mathrm{Exp}(1)$ and $N_p \sim \mathrm{Ge}(p)$ independent of i.i.d. $(X_{p, i})_{i \ge 1}$.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

private lemma wassersteinDist_map_le_integral_abs_sub
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W T : Ω → ℝ} (hW_int : Integrable W P) (hT_int : Integrable T P) :
    wassersteinDist (P.map W) (P.map T) ≤ ENNReal.ofReal (∫ ω, |W ω - T ω| ∂P) := by
  refine ipm_le fun h hh _ _ ↦ ?_
  have hhW_int : Integrable (fun ω ↦ h (W ω)) P := integrable_comp_of_lipschitz hW_int hh
  have hhT_int : Integrable (fun ω ↦ h (T ω)) P := integrable_comp_of_lipschitz hT_int hh
  rw [integral_map hW_int.aemeasurable hh.continuous.measurable.aestronglyMeasurable,
    integral_map hT_int.aemeasurable hh.continuous.measurable.aestronglyMeasurable,
    ← integral_sub hhW_int hhT_int]
  refine ENNReal.ofReal_le_ofReal ?_
  calc
    |∫ ω, (h (W ω) - h (T ω)) ∂P|
        ≤ ∫ ω, |h (W ω) - h (T ω)| ∂P := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω ↦ h (W ω) - h (T ω))
    _ ≤ ∫ ω, |W ω - T ω| ∂P := by
          refine integral_mono (hhW_int.sub hhT_int).norm (hW_int.sub hT_int).norm fun ω ↦ ?_
          simpa [Real.dist_eq] using hh.dist_le_mul (W ω) (T ω)

private lemma wassersteinDist_triangle_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → ℝ} (hT_int : Integrable T P) (μ ν : Measure ℝ) :
    wassersteinDist μ ν ≤ wassersteinDist μ (P.map T) + wassersteinDist (P.map T) ν := by
  refine ipm_le fun h hh hμ hν ↦ ?_
  have hT_map_int : Integrable h (P.map T) :=
    (integrable_map_measure hh.continuous.measurable.aestronglyMeasurable hT_int.aemeasurable).mpr
      (integrable_comp_of_lipschitz hT_int hh)
  have htri : |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| ≤
      |(∫ x, h x ∂μ) - (∫ x, h x ∂(P.map T))| + |(∫ x, h x ∂(P.map T)) - (∫ x, h x ∂ν)| := by
    have : (∫ x, h x ∂μ) - (∫ x, h x ∂ν) =
        ((∫ x, h x ∂μ) - (∫ x, h x ∂(P.map T))) +
          ((∫ x, h x ∂(P.map T)) - (∫ x, h x ∂ν)) := by ring
    rw [this]
    exact abs_add_le _ _
  calc
    ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)|
        ≤ ENNReal.ofReal (|(∫ x, h x ∂μ) - (∫ x, h x ∂(P.map T))| +
            |(∫ x, h x ∂(P.map T)) - (∫ x, h x ∂ν)|) := ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂(P.map T))| +
          ENNReal.ofReal |(∫ x, h x ∂(P.map T)) - (∫ x, h x ∂ν)| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ wassersteinDist μ (P.map T) + wassersteinDist (P.map T) ν :=
          add_le_add (le_ipm hh hμ hT_map_int) (le_ipm hh hT_map_int hν)

/-- Quantitative bounded i.i.d. geometric-sum bound obtained from `thm5_7_corrected` by adjoining a
single equilibrium coordinate on `(Ω × ℝ, P.prod ν_e)` without constructing an infinite product
space. -/
private lemma wassersteinDist_iid_geom_sum_le
    {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Y₀ : Ω₀ → ℝ} {Y : ℕ → Ω → ℝ} {N : Ω → ℕ} {p B : ℝ}
    (hp₀ : 0 < p) (hp₁ : p ≤ 1) (_hB : 0 ≤ B)
    (hY₀_meas : Measurable Y₀)
    (hY₀_bdd : ∀ ω₀, 0 ≤ Y₀ ω₀ ∧ Y₀ ω₀ ≤ B)
    (hY₀_mean : ∫ ω₀, Y₀ ω₀ ∂P₀ = 1)
    (hY_meas : ∀ i : ℕ, 1 ≤ i → Measurable (Y i))
    (hY_id : ∀ i : ℕ, 1 ≤ i → IdentDistrib (Y i) Y₀ P P₀)
    (hY_indep : iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ Y i.1) P)
    (hN_meas : Measurable N)
    (hN_law : P.map N = shiftedGeomLaw p)
    (hN_indep : IndepFun N (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ Y i.1 ω) P) :
    wassersteinDist (P.map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), Y i ω)) stdExpLaw ≤
      ENNReal.ofReal (2 * p * (1 + B ^ 2 / 2)) := by
  let I₁ := {i : ℕ // 1 ≤ i}
  have hY₀_int : Integrable Y₀ P₀ :=
    Integrable.of_bound hY₀_meas.aestronglyMeasurable B
      (Eventually.of_forall fun ω₀ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hY₀_bdd ω₀).1]
        exact (hY₀_bdd ω₀).2)
  have hY₀_pos : 0 < ∫ ω₀, Y₀ ω₀ ∂P₀ := by rw [hY₀_mean]; exact zero_lt_one
  have hac := (sec5_1_equilibrium_ac (Ω' := ℝ) P₀ (Eventually.of_forall fun ω₀ ↦ (hY₀_bdd ω₀).1)
    hY₀_int hY₀_pos).2
  let ρ : ℝ → ℝ≥0∞ :=
    (Ioi (0 : ℝ)).indicator
      (fun x ↦ ENNReal.ofReal (P₀.real {ω₀ | x < Y₀ ω₀} / ∫ ω₀, Y₀ ω₀ ∂P₀))
  let νe : Measure ℝ := volume.withDensity ρ
  have hνe_prob : IsProbabilityMeasure νe := hac.1
  have hνe_eq : IsEquilibrium P₀ Y₀ νe id := hac.2.2
  let Q : Measure (Ω × ℝ) := P.prod νe
  let YQ : ℕ → Ω × ℝ → ℝ := fun i q ↦ Y i q.1
  let YeQ : ℕ → Ω × ℝ → ℝ := fun _ q ↦ q.2
  let NQ : Ω × ℝ → ℕ := fun q ↦ N q.1
  have hQ_fst : Q.map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hQ_snd : Q.map Prod.snd = νe := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hYQ_aem : ∀ i : ℕ, 1 ≤ i → AEMeasurable (YQ i) Q := fun i hi ↦
    ((hY_meas i hi).comp measurable_fst).aemeasurable
  have hYQ_id : ∀ i : ℕ, 1 ≤ i → IdentDistrib (YQ i) Y₀ Q P₀ := fun i hi ↦ by
    refine IdentDistrib.trans ?_ (hY_id i hi)
    exact ⟨hYQ_aem i hi, (hY_meas i hi).aemeasurable, by
      change Q.map (Y i ∘ Prod.fst) = P.map (Y i)
      rw [← Measure.map_map (hY_meas i hi) measurable_fst, hQ_fst]⟩
  have hYQ_nn : ∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[Q] YQ i := fun i hi ↦ by
    have hae : ∀ᵐ ω₀ ∂P₀, 0 ≤ Y₀ ω₀ := Eventually.of_forall fun ω₀ ↦ (hY₀_bdd ω₀).1
    have hmap := (hYQ_id i hi).map_eq
    have hae' : ∀ᵐ x ∂(Q.map (YQ i)), 0 ≤ x := by
      rw [hmap]
      exact (ae_map_iff hY₀_meas.aemeasurable measurableSet_Ici).mpr hae
    exact (ae_map_iff (hYQ_aem i hi) measurableSet_Ici).mp hae'
  have hY₀_L2 : MemLp Y₀ 2 P₀ :=
    memLp_top_of_bound hY₀_meas.aestronglyMeasurable B
      (Eventually.of_forall fun ω₀ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hY₀_bdd ω₀).1]
        exact (hY₀_bdd ω₀).2) |>.mono_exponent le_top
  have hYQ_L2 : ∀ i : ℕ, 1 ≤ i → MemLp (YQ i) 2 Q := fun i hi ↦
    (hYQ_id i hi).symm.memLp_snd hY₀_L2
  have hYQ_mean : ∀ i : ℕ, 1 ≤ i → ∫ q, YQ i q ∂Q = 1 := fun i hi ↦ by
    rw [(hYQ_id i hi).integral_eq, hY₀_mean]
  have hYQ_indep : iIndepFun (fun i : I₁ ↦ YQ i.1) Q := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets hsets
    have hpre_i : ∀ i : I₁, (YQ i.1 ⁻¹' sets i) = (Y i.1 ⁻¹' sets i) ×ˢ univ := fun i ↦ by
      ext q; simp [YQ]
    have hpre_inter : (⋂ i ∈ S, YQ i.1 ⁻¹' sets i) =
        (⋂ i ∈ S, Y i.1 ⁻¹' sets i) ×ˢ (univ : Set ℝ) := by
      ext q; simp [YQ]
    rw [hpre_inter, Measure.prod_prod, measure_univ, mul_one,
      hY_indep.measure_inter_preimage_eq_mul S hsets]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [hpre_i i, Measure.prod_prod, measure_univ, mul_one]
  have hNQ_meas : Measurable NQ := hN_meas.comp measurable_fst
  have hNQ_law : Q.map NQ = shiftedGeomLaw p := by
    change Q.map (N ∘ Prod.fst) = shiftedGeomLaw p
    rw [← Measure.map_map hN_meas measurable_fst, hQ_fst, hN_law]
  have hNQ_pos : ∀ᵐ q ∂Q, 1 ≤ NQ q := by
    have hae := ae_one_le_shiftedGeomLaw p
    rw [← hNQ_law] at hae
    exact (ae_map_iff hNQ_meas.aemeasurable measurableSet_Ici).mp hae
  have hNQ_pmf : ∀ m : ℕ, 1 ≤ m →
      Q.real {q | NQ q = m} = p * Q.real {q | m ≤ NQ q} := fun m hm ↦ by
    have h1 : Q.real {q | NQ q = m} = (shiftedGeomLaw p).real {m} := by
      rw [← hNQ_law, map_measureReal_apply hNQ_meas (measurableSet_singleton m)]; rfl
    have h2 : Q.real {q | m ≤ NQ q} = (shiftedGeomLaw p).real (Ici m) := by
      rw [← hNQ_law, map_measureReal_apply hNQ_meas measurableSet_Ici]; rfl
    rw [h1, h2, shiftedGeomLaw_real_singleton_of_pos hp₀ hp₁ hm,
      shiftedGeomLaw_real_Ici hp₀ hp₁ hm]
    ring
  have hNQ_int : Integrable (fun q ↦ (NQ q : ℝ)) Q := by
    have hm := integrable_cast_shiftedGeomLaw hp₀ hp₁
    rw [← hNQ_law] at hm
    exact (integrable_map_measure (by fun_prop) hNQ_meas.aemeasurable).mp hm
  have hNQ_mean : ∫ q, (NQ q : ℝ) ∂Q = 1 / p := by
    have hm := integral_cast_shiftedGeomLaw hp₀ hp₁
    rw [← hNQ_law, integral_map hNQ_meas.aemeasurable (by fun_prop)] at hm
    exact hm
  have hYeQ_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium Q (YQ i) Q (YeQ i) := fun i hi ↦
    hνe_eq.congr_identDistrib (hYQ_id i hi).symm
      ⟨aemeasurable_id, measurable_snd.aemeasurable, by rw [Measure.map_id, hQ_snd]⟩
  have hYeQ_indep : ∀ i : I₁,
      IndepFun (YeQ i.1)
        (fun q ↦ (NQ q, NQ q, fun j : {j : I₁ // j ≠ i} ↦ YQ j.1.1 q)) Q := fun i ↦ by
    have hfst_meas : Measurable (fun ω ↦ (N ω, N ω, fun j : {j : I₁ // j ≠ i} ↦ Y j.1.1 ω)) :=
      hN_meas.prodMk (hN_meas.prodMk (measurable_pi_iff.mpr fun j ↦ hY_meas j.1.1 j.1.2))
    exact (indepFun_prod hfst_meas measurable_id).symm
  have hNNQ_indep : IndepFun (fun q ↦ (NQ q, NQ q))
      (fun q (i : I₁) ↦ YQ i.1 q) Q := by
    have hYvec_meas : Measurable (fun ω (i : I₁) ↦ Y i.1 ω) :=
      measurable_pi_iff.mpr fun i ↦ hY_meas i.1 i.2
    have hbase := indepFun_fst_comp_prod_snd (ν := νe) hN_meas hYvec_meas hN_indep
    exact hbase.comp (measurable_id.prodMk measurable_id) measurable_fst
  have hZ_prob : IsProbabilityMeasure stdExpLaw := isProbabilityMeasure_stdExpLaw
  have hbnd := thm5_7_corrected_minimal Q stdExpLaw hp₀ hp₁ hYQ_aem hYQ_nn hYQ_L2 hYQ_mean hYQ_indep
    hNQ_meas.aemeasurable hNQ_meas.aemeasurable hNQ_pos hNQ_int hNQ_mean
    hNQ_pos hNQ_pmf hYeQ_eq hYeQ_indep hNNQ_indep aemeasurable_id Measure.map_id
  have hmap_W : Q.map (fun q ↦ p * ∑ i ∈ Finset.Icc 1 (NQ q), YQ i q) =
      P.map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), Y i ω) := by
    let W_P : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), Y i ω
    have hWP_meas : Measurable W_P := by
      dsimp only [W_P]
      exact measurable_const.mul
        (measurable_select_nat
          (f := fun n ω ↦ ∑ i ∈ Finset.Icc 1 n, Y i ω)
          (fun n ↦ Finset.measurable_sum _ fun i hi ↦ hY_meas i (Finset.mem_Icc.mp hi).1) hN_meas)
    change Q.map (W_P ∘ Prod.fst) = P.map W_P
    rw [← Measure.map_map hWP_meas measurable_fst, hQ_fst]
  have hY₀_sq_int : Integrable (fun ω₀ ↦ Y₀ ω₀ ^ 2) P₀ :=
    Integrable.of_bound ((continuous_pow 2).measurable.comp hY₀_meas).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun ω₀ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [(hY₀_bdd ω₀).1]) (hY₀_bdd ω₀).2)
  have hμ₂_le : (⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ q, YQ i q ^ 2 ∂Q)) ≤
      ENNReal.ofReal (B ^ 2) := by
    refine iSup₂_le fun i hi ↦ ENNReal.ofReal_le_ofReal ?_
    have hsq_id : ∫ q, YQ i q ^ 2 ∂Q = ∫ ω₀, Y₀ ω₀ ^ 2 ∂P₀ := by
      have hid2 := (hYQ_id i hi).comp (continuous_pow 2).measurable
      exact hid2.integral_eq
    rw [hsq_id]
    calc
      ∫ ω₀, Y₀ ω₀ ^ 2 ∂P₀ ≤ ∫ _ω₀, B ^ 2 ∂P₀ := by
        refine integral_mono hY₀_sq_int (integrable_const (B ^ 2)) fun ω₀ ↦ ?_
        exact sq_le_sq' (by linarith [(hY₀_bdd ω₀).1]) (hY₀_bdd ω₀).2
      _ = B ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  have herr_le := hbnd.1.trans hbnd.2
  rw [hmap_W, Measure.map_id] at herr_le
  simp only [sub_self, abs_zero, ENNReal.ofReal_zero, lintegral_zero, add_zero] at herr_le
  refine herr_le.trans ?_
  calc
    ENNReal.ofReal (2 * p) *
        (1 + (⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ q, YQ i q ^ 2 ∂Q)) / 2)
        ≤ ENNReal.ofReal (2 * p) * (1 + ENNReal.ofReal (B ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add le_rfl (ENNReal.div_le_div_right hμ₂_le 2)) zero_le
    _ = ENNReal.ofReal (2 * p * (1 + B ^ 2 / 2)) := by
          symm
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one (by positivity),
            ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat 2]

/-- **Theorem 5.6 (Rényi's Theorem)** (unlabeled, `SteinIntro.tex:2905-2911`): for any
non-negative mean-$1$ law $\mathcal{L}(X_0)$, if for each $p \in (0, 1]$, $(X_{p, i})_{i \ge 1}$
are i.i.d. distributed as $X_0$ and independent of $N_p \sim \mathrm{Ge}(p)$, then
$\lim_{p \to 0^+} d_{\mathrm{K}}(\mathcal{L}(p \sum_{i=1}^{N_p} X_{p, i}), \mathcal{L}(Z)) = 0$ for
$Z \sim \mathrm{Exp}(1)$. -/
theorem thm5_6
    {Ω₀ Ω' : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω']
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X₀ : Ω₀ → ℝ} {Z : Ω' → ℝ}
    {Ω : ℝ → Type*} [∀ p, MeasurableSpace (Ω p)]
    (P : ∀ p, Measure (Ω p))
    {X : ∀ p, ℕ → Ω p → ℝ} {N : ∀ p, Ω p → ℕ}
    (hX₀_nn : 0 ≤ᵐ[P₀] X₀)
    (hX₀_int : Integrable X₀ P₀)
    (hX₀_mean : ∫ ω₀, X₀ ω₀ ∂P₀ = 1)
    (_hZ_aem : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdExpLaw)
    (hFam : ∀ p ∈ Ioc (0 : ℝ) 1,
      IsProbabilityMeasure (P p) ∧
      iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X p i.1) (P p) ∧
      (∀ i : ℕ, 1 ≤ i → IdentDistrib (X p i) X₀ (P p) P₀) ∧
      AEMeasurable (N p) (P p) ∧
      (P p).map (N p) = shiftedGeomLaw p ∧
      IndepFun (N p) (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X p i.1 ω) (P p)) :
    Tendsto
      (fun p : ℝ ↦
        kolmogorovDist
          ((P p).map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω))
          (P'.map Z))
      (𝓝[>] 0)
      (𝓝 0) := by
  rw [hZ_law]
  suffices hW_tendsto :
      Tendsto
        (fun p : ℝ ↦
          wassersteinDist ((P p).map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω)) stdExpLaw)
        (𝓝[>] 0)
        (𝓝 0) by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (f := fun p : ℝ ↦
        kolmogorovDist ((P p).map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω)) stdExpLaw)
      (h := fun p : ℝ ↦
        (2 * wassersteinDist
          ((P p).map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω)) stdExpLaw) ^ (1 / 2 : ℝ))
      ?_ (Eventually.of_forall fun _ ↦ zero_le) ?_
    · have hmul : Tendsto
          (fun p : ℝ ↦
            2 * wassersteinDist
              ((P p).map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω)) stdExpLaw)
          (𝓝[>] 0) (𝓝 (2 * 0)) :=
        ENNReal.Tendsto.const_mul hW_tendsto (Or.inr ENNReal.ofNat_ne_top)
      rw [mul_zero] at hmul
      have hrpow := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hmul
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        using hrpow
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with p hp
      have : IsProbabilityMeasure (P p) := (hFam p ⟨hp.1, hp.2.le⟩).1
      have hWp_aem : AEMeasurable (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω) (P p) := by
        rcases hFam p ⟨hp.1, hp.2.le⟩ with ⟨_, _, hX_id, hN_aem, _, _⟩
        let N' := hN_aem.mk (N p)
        let X' : ℕ → Ω p → ℝ := fun i ↦
          if hi : 1 ≤ i then (hX_id i hi).aemeasurable_fst.mk (X p i) else 0
        have hX'_meas : ∀ i, Measurable (X' i) := fun i ↦ by
          dsimp only [X']; split_ifs with hi
          · exact (hX_id i hi).aemeasurable_fst.measurable_mk
          · exact measurable_const
        have hm : Measurable (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N' ω), X' i ω) :=
          measurable_const.mul
            (measurable_select_nat (fun n ↦ Finset.measurable_sum _ fun i _ ↦ hX'_meas i)
              hN_aem.measurable_mk)
        have hae_all : ∀ᵐ ω ∂(P p), ∀ i : {i : ℕ // 1 ≤ i}, X p i.1 ω = X' i.1 ω :=
          ae_all_iff.mpr fun i ↦ by
            filter_upwards [(hX_id i.1 i.2).aemeasurable_fst.ae_eq_mk] with ω hω
            dsimp only [X']
            simp only [i.2, ↓reduceDIte, hω]
        refine hm.aemeasurable.congr ?_
        filter_upwards [hN_aem.ae_eq_mk, hae_all] with ω hNω hXω
        dsimp only [N']
        rw [← hNω]
        congr 1
        exact Finset.sum_congr rfl fun i hi ↦ (hXω ⟨i, (Finset.mem_Icc.mp hi).1⟩).symm
      have : IsProbabilityMeasure
          ((P p).map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω)) :=
        (Measure.isProbabilityMeasure_map_iff hWp_aem).mpr ‹_›
      exact kolmogorovDist_le_sqrt_two_mul_wassersteinDist_stdExpLaw _
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ_le⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal (4 * δ) ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hε_top
    · exact ⟨1, zero_lt_one, le_top⟩
    · refine ⟨ε.toReal / 8, div_pos (ENNReal.toReal_pos hε.ne' hε_top) (by norm_num), ?_⟩
      calc
        ENNReal.ofReal (4 * (ε.toReal / 8))
            ≤ ENNReal.ofReal ε.toReal :=
              ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_pos hε.ne' hε_top])
        _ = ε := ENNReal.ofReal_toReal hε_top
  let X₀' : Ω₀ → ℝ := fun ω₀ ↦ max (hX₀_int.aemeasurable.mk X₀ ω₀) 0
  have hX₀'_meas : Measurable X₀' := hX₀_int.aemeasurable.measurable_mk.max measurable_const
  have hX₀'_ae : X₀ =ᵐ[P₀] X₀' := by
    filter_upwards [hX₀_int.aemeasurable.ae_eq_mk, hX₀_nn] with ω₀ h1 (h2 : 0 ≤ X₀ ω₀)
    dsimp only [X₀']
    rw [← h1, max_eq_left h2]
  have hX₀'_int : Integrable X₀' P₀ := hX₀_int.congr hX₀'_ae
  have hX₀'_mean : ∫ ω₀, X₀' ω₀ ∂P₀ = 1 := by
    rw [← integral_congr_ae hX₀'_ae, hX₀_mean]
  let trunc : ℕ → ℝ → ℝ := fun K x ↦ min (max x 0) (K : ℝ)
  have htrunc_tendsto : Tendsto (fun K : ℕ ↦ ∫ ω₀, trunc K (X₀' ω₀) ∂P₀) atTop (𝓝 1) := by
    rw [← hX₀'_mean]
    refine tendsto_integral_of_dominated_convergence X₀'
      (fun K ↦ (((continuous_id.max continuous_const).min continuous_const).measurable.comp
        hX₀'_meas).aestronglyMeasurable)
      hX₀'_int ?_ ?_
    · intro K
      refine Eventually.of_forall fun ω₀ ↦ ?_
      have hnn : 0 ≤ X₀' ω₀ := le_max_right _ 0
      dsimp only [trunc]
      rw [max_eq_left hnn, Real.norm_eq_abs, abs_of_nonneg (le_min hnn (Nat.cast_nonneg K))]
      exact min_le_left _ _
    · refine Eventually.of_forall fun ω₀ ↦
        tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (X₀' ω₀)) fun K hK ↦ ?_
      have hnn : 0 ≤ X₀' ω₀ := le_max_right _ 0
      dsimp only [trunc]
      rw [max_eq_left hnn, min_eq_left ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))]
  let η : ℝ := min δ (1 / 2)
  have hη_pos : 0 < η := lt_min hδ_pos (by norm_num)
  have hmem_atTop := htrunc_tendsto.eventually (Ioo_mem_nhds (by linarith : 1 - η < 1)
    (by linarith : (1 : ℝ) < 1 + η))
  obtain ⟨K, hK_mem⟩ := hmem_atTop.exists
  set μK : ℝ := ∫ ω₀, trunc K (X₀' ω₀) ∂P₀
  have hμK_gt : 1 - η < μK := hK_mem.1
  have hμK_pos : 0 < μK := by
    have : η ≤ 1 / 2 := min_le_right _ _
    linarith
  have hμK_le_one : μK ≤ 1 := by
    rw [← hX₀'_mean]
    refine integral_mono
      ((((continuous_id.max continuous_const).min continuous_const).measurable.comp
        hX₀'_meas).aestronglyMeasurable |> fun hm ↦
        hX₀'_int.mono' hm (Eventually.of_forall fun ω₀ ↦ by
          have hnn : 0 ≤ X₀' ω₀ := le_max_right _ 0
          dsimp only [trunc]
          rw [max_eq_left hnn, Real.norm_eq_abs, abs_of_nonneg (le_min hnn (Nat.cast_nonneg K))]
          exact min_le_left _ _))
      hX₀'_int fun ω₀ ↦ ?_
    have hnn : 0 ≤ X₀' ω₀ := le_max_right _ 0
    dsimp only [trunc]
    rw [max_eq_left hnn]
    exact min_le_left _ _
  have h1mμK_lt : 1 - μK < δ := by
    have : η ≤ δ := min_le_left _ _
    linarith
  let B : ℝ := (K : ℝ) / μK
  have hB_nn : 0 ≤ B := div_nonneg (Nat.cast_nonneg K) hμK_pos.le
  let p_max : ℝ := min 1 (δ / (1 + B ^ 2 / 2))
  have hp_max_pos : 0 < p_max := lt_min zero_lt_one (div_pos hδ_pos (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hp_max_pos] with p hp
  have hp₀ : 0 < p := hp.1
  have hp₁ : p ≤ 1 := hp.2.le.trans (min_le_left _ _)
  have hp_small : 2 * p * (1 + B ^ 2 / 2) ≤ 2 * δ := by
    have hp_lt : p < δ / (1 + B ^ 2 / 2) := hp.2.trans_le (min_le_right _ _)
    have hpos : 0 < 1 + B ^ 2 / 2 := by positivity
    have := (lt_div_iff₀ hpos).mp hp_lt
    linarith
  rcases hFam p ⟨hp₀, hp₁⟩ with ⟨hPp_prob, hXp_indep, hXp_id, hNp_aem, hNp_law, hNp_indep⟩
  have : IsProbabilityMeasure (P p) := hPp_prob
  let I₁ := {i : ℕ // 1 ≤ i}
  let N₁ : Ω p → ℕ := fun ω ↦ max (hNp_aem.mk (N p) ω) 1
  let X₁ : ℕ → Ω p → ℝ := fun i ω ↦
    if hi : 1 ≤ i then max ((hXp_id i hi).aemeasurable_fst.mk (X p i) ω) 0 else 0
  have hN₁_meas : Measurable N₁ := hNp_aem.measurable_mk.max measurable_const
  have hX₁_meas : ∀ i, Measurable (X₁ i) := fun i ↦ by
    dsimp only [X₁]; split_ifs with hi
    · exact (hXp_id i hi).aemeasurable_fst.measurable_mk.max measurable_const
    · exact measurable_const
  have hX₁_nn : ∀ i ω, 0 ≤ X₁ i ω := fun i ω ↦ by
    dsimp only [X₁]; split_ifs
    · exact le_max_right _ 0
    · exact le_rfl
  have hNp_pos : ∀ᵐ ω ∂(P p), 1 ≤ N p ω := by
    have hae := ae_one_le_shiftedGeomLaw p
    rw [← hNp_law] at hae
    exact (ae_map_iff hNp_aem measurableSet_Ici).mp hae
  have hN₁_ae : N p =ᵐ[P p] N₁ := by
    filter_upwards [hNp_aem.ae_eq_mk, hNp_pos] with ω h1 h2
    dsimp only [N₁]; rw [← h1, max_eq_left h2]
  have hX₁_ae : ∀ i : ℕ, 1 ≤ i → X p i =ᵐ[P p] X₁ i := fun i hi ↦ by
    have hnn_i : 0 ≤ᵐ[P p] X p i := by
      have hmap := (hXp_id i hi).map_eq
      have hae0 : ∀ᵐ x ∂((P p).map (X p i)), 0 ≤ x := by
        rw [hmap]
        exact (ae_map_iff hX₀_int.aemeasurable measurableSet_Ici).mpr hX₀_nn
      exact (ae_map_iff (hXp_id i hi).aemeasurable_fst measurableSet_Ici).mp hae0
    filter_upwards [(hXp_id i hi).aemeasurable_fst.ae_eq_mk, hnn_i] with ω h1 (h2 : 0 ≤ X p i ω)
    dsimp only [X₁]
    simp only [hi, ↓reduceDIte, ← h1, max_eq_left h2]
  have hall_X₁ : ∀ᵐ ω ∂(P p), ∀ i : I₁, X p i.1 ω = X₁ i.1 ω :=
    ae_all_iff.mpr fun i ↦ hX₁_ae i.1 i.2
  have hN₁_law : (P p).map N₁ = shiftedGeomLaw p := by
    rw [← Measure.map_congr hN₁_ae, hNp_law]
  have hX₁_id : ∀ i : ℕ, 1 ≤ i → IdentDistrib (X₁ i) X₀' (P p) P₀ := fun i hi ↦
    (IdentDistrib.of_ae_eq (hXp_id i hi).aemeasurable_fst (hX₁_ae i hi)).symm.trans
      ((hXp_id i hi).trans (IdentDistrib.of_ae_eq hX₀_int.aemeasurable hX₀'_ae))
  have hX₁_indep : iIndepFun (fun i : I₁ ↦ X₁ i.1) (P p) :=
    hXp_indep.congr fun i ↦ hX₁_ae i.1 i.2
  have hN₁_indep : IndepFun N₁ (fun ω (i : I₁) ↦ X₁ i.1 ω) (P p) :=
    hNp_indep.congr hN₁_ae (hall_X₁.mono fun ω hω ↦ funext fun i ↦ hω i)
  let φ_tr : ℝ → ℝ := fun x ↦ trunc K x / μK
  have hφ_tr_meas : Measurable φ_tr :=
    (((continuous_id.max continuous_const).min continuous_const).div_const μK).measurable
  let Y₀ : Ω₀ → ℝ := fun ω₀ ↦ φ_tr (X₀' ω₀)
  let Y : ℕ → Ω p → ℝ := fun i ω ↦ if 1 ≤ i then φ_tr (X₁ i ω) else 0
  have hY₀_meas : Measurable Y₀ := hφ_tr_meas.comp hX₀'_meas
  have hY₀_bdd : ∀ ω₀, 0 ≤ Y₀ ω₀ ∧ Y₀ ω₀ ≤ B := fun ω₀ ↦ by
    have hnn : 0 ≤ X₀' ω₀ := le_max_right _ 0
    dsimp only [Y₀, φ_tr, trunc, B]
    rw [max_eq_left hnn]
    exact ⟨div_nonneg (le_min hnn (Nat.cast_nonneg K)) hμK_pos.le,
      div_le_div_of_nonneg_right (min_le_right _ _) hμK_pos.le⟩
  have hY₀_mean : ∫ ω₀, Y₀ ω₀ ∂P₀ = 1 := by
    change ∫ ω₀, trunc K (X₀' ω₀) / μK ∂P₀ = 1
    rw [integral_div]
    exact div_self hμK_pos.ne'
  have hY_meas : ∀ i : ℕ, 1 ≤ i → Measurable (Y i) := fun i hi ↦ by
    have heq : Y i = φ_tr ∘ X₁ i := by ext ω; simp [Y, hi]
    rw [heq]; exact hφ_tr_meas.comp (hX₁_meas i)
  have hY_id : ∀ i : ℕ, 1 ≤ i → IdentDistrib (Y i) Y₀ (P p) P₀ := fun i hi ↦ by
    have heq : Y i = φ_tr ∘ X₁ i := by ext ω; simp [Y, hi]
    rw [heq]
    exact (hX₁_id i hi).comp hφ_tr_meas
  have hY_indep : iIndepFun (fun i : I₁ ↦ Y i.1) (P p) := by
    have heq : (fun i : I₁ ↦ Y i.1) = fun i : I₁ ↦ φ_tr ∘ X₁ i.1 := by
      ext i ω; simp [Y, i.2]
    rw [heq]
    exact hX₁_indep.comp (fun _ ↦ φ_tr) (fun _ ↦ hφ_tr_meas)
  have hNY_indep : IndepFun N₁ (fun ω (i : I₁) ↦ Y i.1 ω) (P p) := by
    let ΦY : (I₁ → ℝ) → (I₁ → ℝ) := fun z i ↦ φ_tr (z i)
    have hΦY : Measurable ΦY :=
      measurable_pi_iff.mpr fun i ↦ hφ_tr_meas.comp (measurable_pi_apply i)
    have heq : (fun ω (i : I₁) ↦ Y i.1 ω) = ΦY ∘ fun ω (i : I₁) ↦ X₁ i.1 ω := by
      ext ω i; simp [Y, i.2, ΦY]
    rw [heq]
    exact hN₁_indep.comp measurable_id hΦY
  let W₁ : Ω p → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω
  let T₁ : Ω p → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N₁ ω), Y i ω
  have hW_ae : (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω) =ᵐ[P p] W₁ := by
    filter_upwards [hN₁_ae, hall_X₁] with ω hNω hXω
    dsimp only [W₁]; rw [hNω]; congr 1
    exact Finset.sum_congr rfl fun i hi ↦ hXω ⟨i, (Finset.mem_Icc.mp hi).1⟩
  have hT₁_exp := wassersteinDist_iid_geom_sum_le P₀ (P p) hp₀ hp₁ hB_nn
    hY₀_meas hY₀_bdd hY₀_mean hY_meas hY_id hY_indep hN₁_meas hN₁_law hNY_indep
  have hdiff_i_le : ∀ i : ℕ, 1 ≤ i → ∫ ω, |X₁ i ω - Y i ω| ∂(P p) ≤ 2 * (1 - μK) :=
    fun i hi ↦ by
      have hid_diff : IdentDistrib (fun ω ↦ |X₁ i ω - Y i ω|)
          (fun ω₀ ↦ |X₀' ω₀ - Y₀ ω₀|) (P p) P₀ := by
        have hcomp : (fun ω ↦ |X₁ i ω - Y i ω|) = (fun x ↦ |x - φ_tr x|) ∘ X₁ i := by
          ext ω; simp [Y, hi]
        rw [hcomp]
        exact (hX₁_id i hi).comp
          (continuous_abs.measurable.comp (measurable_id.sub hφ_tr_meas))
      rw [hid_diff.integral_eq]
      have hY₀_int : Integrable Y₀ P₀ :=
        Integrable.of_bound hY₀_meas.aestronglyMeasurable B
          (Eventually.of_forall fun ω₀ ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (hY₀_bdd ω₀).1]; exact (hY₀_bdd ω₀).2)
      have hpt_le : ∀ ω₀, |X₀' ω₀ - Y₀ ω₀| ≤
          (X₀' ω₀ - trunc K (X₀' ω₀)) + trunc K (X₀' ω₀) * (1 / μK - 1) := fun ω₀ ↦ by
        have hnn : 0 ≤ X₀' ω₀ := le_max_right _ 0
        have htr_nn : 0 ≤ trunc K (X₀' ω₀) := by
          dsimp only [trunc]; rw [max_eq_left hnn]; exact le_min hnn (Nat.cast_nonneg K)
        have htr_le : trunc K (X₀' ω₀) ≤ X₀' ω₀ := by
          dsimp only [trunc]; rw [max_eq_left hnn]; exact min_le_left _ _
        have h1div : 0 ≤ 1 / μK - 1 := by
          rw [sub_nonneg, one_le_div hμK_pos]; exact hμK_le_one
        have hid_eq : X₀' ω₀ - Y₀ ω₀ =
            (X₀' ω₀ - trunc K (X₀' ω₀)) - trunc K (X₀' ω₀) * (1 / μK - 1) := by
          dsimp only [Y₀, φ_tr]; ring
        rw [hid_eq]
        calc
          |(X₀' ω₀ - trunc K (X₀' ω₀)) - trunc K (X₀' ω₀) * (1 / μK - 1)|
              ≤ |X₀' ω₀ - trunc K (X₀' ω₀)| + |trunc K (X₀' ω₀) * (1 / μK - 1)| := abs_sub _ _
          _ = (X₀' ω₀ - trunc K (X₀' ω₀)) + trunc K (X₀' ω₀) * (1 / μK - 1) := by
                rw [abs_of_nonneg (sub_nonneg.mpr htr_le),
                  abs_of_nonneg (mul_nonneg htr_nn h1div)]
      have htr_int : Integrable (fun ω₀ ↦ trunc K (X₀' ω₀)) P₀ := by
        have hm : AEStronglyMeasurable (fun ω₀ ↦ trunc K (X₀' ω₀)) P₀ :=
          (((continuous_id.max (continuous_const (y := (0 : ℝ)))).min
            (continuous_const (y := (K : ℝ)))).measurable.comp hX₀'_meas).aestronglyMeasurable
        exact hX₀'_int.mono' hm (Eventually.of_forall fun ω₀ ↦ by
          have hnn : 0 ≤ X₀' ω₀ := le_max_right _ 0
          dsimp only [trunc]; rw [max_eq_left hnn, Real.norm_eq_abs,
            abs_of_nonneg (le_min hnn (Nat.cast_nonneg K))]
          exact min_le_left _ _)
      have hsub_int : Integrable (fun ω₀ ↦ X₀' ω₀ - trunc K (X₀' ω₀)) P₀ := hX₀'_int.sub htr_int
      have hmul_int : Integrable (fun ω₀ ↦ trunc K (X₀' ω₀) * (1 / μK - 1)) P₀ :=
        htr_int.mul_const _
      calc
        ∫ ω₀, |X₀' ω₀ - Y₀ ω₀| ∂P₀
            ≤ ∫ ω₀, ((X₀' ω₀ - trunc K (X₀' ω₀)) +
                trunc K (X₀' ω₀) * (1 / μK - 1)) ∂P₀ :=
              integral_mono (hX₀'_int.sub hY₀_int).norm (hsub_int.add hmul_int) hpt_le
        _ = 2 * (1 - μK) := by
              rw [integral_add hsub_int hmul_int,
                integral_sub hX₀'_int htr_int, integral_mul_const, hX₀'_mean]
              change (1 - μK) + μK * (1 / μK - 1) = 2 * (1 - μK)
              field_simp [hμK_pos.ne']
              ring
  have hSum_lint_bound : ∀ (g : ℕ → Ω p → ℝ) (_hg_meas : ∀ i, Measurable (g i))
      (_hg_nn : ∀ i ω, 0 ≤ g i ω)
      (_hg_indep : ∀ k : ℕ, IndepFun N₁ (g (k + 1)) (P p))
      {C : ℝ} (_hC : 0 ≤ C) (_hg_lint : ∀ k : ℕ, ∫⁻ ω, ENNReal.ofReal (g (k + 1) ω) ∂(P p) ≤
        ENNReal.ofReal C),
      ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.Icc 1 (N₁ ω), g i ω) ∂(P p) ≤
        ENNReal.ofReal (C / p) := by
    intro g hg_meas hg_nn hg_indep C _hC hg_lint
    have hpt : ∀ ω, ENNReal.ofReal (∑ i ∈ Finset.Icc 1 (N₁ ω), g i ω) =
        ∑' k : ℕ, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (g (k + 1) ω) := fun ω ↦ by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hg_nn i ω),
        sum_Icc_one_eq_tsum_ite (fun i ↦ ENNReal.ofReal (g i ω))]
      congr 1; ext k
      by_cases hk : k + 1 ≤ N₁ ω
      · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
        rw [indicator_of_mem hmem, one_mul]; simp only [hk, ↓reduceIte]
      · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
        rw [indicator_of_notMem hnot, zero_mul]; simp only [hk, ↓reduceIte]
    simp_rw [hpt]
    have hm_term : ∀ k : ℕ, Measurable (fun ω ↦
        {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (g (k + 1) ω)) := fun k ↦
      (measurable_const.indicator (measurableSet_le measurable_const hN₁_meas)).mul
        (ENNReal.measurable_ofReal.comp (hg_meas (k + 1)))
    rw [lintegral_tsum fun k ↦ (hm_term k).aemeasurable]
    have hterm_le : ∀ k : ℕ,
        ∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (g (k + 1) ω) ∂(P p) ≤
        (∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂(P p)) *
          ENNReal.ofReal C := fun k ↦ by
      let ψ₁ : ℕ → ℝ≥0∞ := fun n ↦ if k + 1 ≤ n then 1 else 0
      have hψ₁ : Measurable ψ₁ := Measurable.of_discrete
      have hind := (hg_indep k).comp hψ₁ ENNReal.measurable_ofReal
      have hprod : (fun ω ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (g (k + 1) ω)) =
          fun ω ↦ (ψ₁ ∘ N₁) ω * (ENNReal.ofReal ∘ g (k + 1)) ω := by
        ext ω
        dsimp only [ψ₁, Function.comp_apply]
        by_cases hk : k + 1 ≤ N₁ ω
        · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]
        · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
      have hl1 : ∫⁻ ω, (ψ₁ ∘ N₁) ω ∂(P p) =
          ∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂(P p) := by
        refine lintegral_congr fun ω ↦ ?_
        dsimp only [ψ₁, Function.comp_apply]
        by_cases hk : k + 1 ≤ N₁ ω
        · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]
        · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
      change lintegral (P p) (fun ω ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (g (k + 1) ω)) ≤ _
      rw [hprod, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        (hψ₁.comp hN₁_meas).aemeasurable
        (ENNReal.measurable_ofReal.comp (hg_meas (k + 1))).aemeasurable hind, hl1]
      exact mul_le_mul_of_nonneg_left (hg_lint k) zero_le
    have hN₁R_int : Integrable (fun ω ↦ (N₁ ω : ℝ)) (P p) := by
      have hm := integrable_cast_shiftedGeomLaw hp₀ hp₁
      rw [← hN₁_law] at hm
      exact (integrable_map_measure (by fun_prop) hN₁_meas.aemeasurable).mp hm
    have hN₁R_mean : ∫ ω, (N₁ ω : ℝ) ∂(P p) = 1 / p := by
      have hm := integral_cast_shiftedGeomLaw hp₀ hp₁
      rw [← hN₁_law, integral_map hN₁_meas.aemeasurable (by fun_prop)] at hm
      exact hm
    calc
      (∑' k : ℕ, ∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (g (k + 1) ω) ∂(P p))
          ≤ ∑' k : ℕ, (∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂(P p)) *
              ENNReal.ofReal C := ENNReal.tsum_le_tsum hterm_le
      _ = (∫⁻ ω, ∑' k : ℕ, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂(P p)) *
            ENNReal.ofReal C := by
            rw [ENNReal.tsum_mul_right, lintegral_tsum fun k ↦
              (measurable_const.indicator
                (measurableSet_le measurable_const hN₁_meas)).aemeasurable]
      _ = ENNReal.ofReal (1 / p) * ENNReal.ofReal C := by
            congr 1
            have htsum_N : ∀ ω,
                (∑' k : ℕ, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω) =
                  ENNReal.ofReal (N₁ ω : ℝ) := fun ω ↦ by
              have hc : (fun k : ℕ ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω) =
                  fun k ↦ if k + 1 ≤ N₁ ω then (1 : ℝ≥0∞) else 0 := by
                ext k
                by_cases hk : k + 1 ≤ N₁ ω
                · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
                  rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]
                · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
                  rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
              rw [hc, tsum_ite_le_eq_natCast, ENNReal.ofReal_natCast]
            simp_rw [htsum_N]
            rw [← ofReal_integral_eq_lintegral_ofReal hN₁R_int
              (Eventually.of_forall fun ω ↦ Nat.cast_nonneg (N₁ ω)), hN₁R_mean]
      _ = ENNReal.ofReal (C / p) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
  have hN₁_indep_k : ∀ k : ℕ, IndepFun N₁ (X₁ (k + 1)) (P p) := fun k ↦ by
    simpa [Function.comp_def] using
      hN₁_indep.comp measurable_id
        (measurable_pi_apply (X := fun _ : I₁ ↦ ℝ) ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩)
  have hW₁_int : Integrable W₁ (P p) := by
    refine Integrable.const_mul ⟨(measurable_select_nat
      (fun n ↦ Finset.measurable_sum _ fun i _ ↦ hX₁_meas i) hN₁_meas).aestronglyMeasurable, ?_⟩ p
    rw [hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω ↦ Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω)]
    refine lt_of_le_of_lt
      (hSum_lint_bound X₁ hX₁_meas hX₁_nn hN₁_indep_k zero_le_one fun k ↦ ?_)
      ENNReal.ofReal_lt_top
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hX₁k_int : Integrable (X₁ (k + 1)) (P p) :=
      (hX₁_id (k + 1) hk1).symm.integrable_snd hX₀'_int
    rw [← ofReal_integral_eq_lintegral_ofReal hX₁k_int (Eventually.of_forall fun ω ↦ hX₁_nn _ ω),
      (hX₁_id (k + 1) hk1).integral_eq, hX₀'_mean]
  have hY_all_meas : ∀ i, Measurable (Y i) := fun i ↦ by
    by_cases hi : 1 ≤ i
    · exact hY_meas i hi
    · have heq : Y i = 0 := by ext ω; simp [Y, hi]
      rw [heq]; exact measurable_const
  have hY_all_nn : ∀ i ω, 0 ≤ Y i ω := fun i ω ↦ by
    dsimp only [Y]; split_ifs with hi
    · dsimp only [φ_tr, trunc]
      exact div_nonneg (le_min (le_max_right _ 0) (Nat.cast_nonneg K)) hμK_pos.le
    · exact le_rfl
  have hT₁_int : Integrable T₁ (P p) := by
    refine Integrable.const_mul ⟨(measurable_select_nat
      (fun n ↦ Finset.measurable_sum _ fun i _ ↦ hY_all_meas i) hN₁_meas).aestronglyMeasurable,
      ?_⟩ p
    rw [hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω ↦ Finset.sum_nonneg fun i _ ↦ hY_all_nn i ω)]
    refine lt_of_le_of_lt
      (hSum_lint_bound Y hY_all_meas hY_all_nn
        (fun k ↦ by
          have heq : Y (k + 1) = φ_tr ∘ X₁ (k + 1) := by ext ω; simp [Y]
          rw [heq]
          exact (hN₁_indep_k k).comp measurable_id hφ_tr_meas) zero_le_one fun k ↦ ?_)
      ENNReal.ofReal_lt_top
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hY₀_int : Integrable Y₀ P₀ :=
      Integrable.of_bound hY₀_meas.aestronglyMeasurable B
        (Eventually.of_forall fun ω₀ ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hY₀_bdd ω₀).1]; exact (hY₀_bdd ω₀).2)
    have hYk_int : Integrable (Y (k + 1)) (P p) := (hY_id (k + 1) hk1).symm.integrable_snd hY₀_int
    rw [← ofReal_integral_eq_lintegral_ofReal hYk_int (Eventually.of_forall fun ω ↦ hY_all_nn _ ω),
      (hY_id (k + 1) hk1).integral_eq, hY₀_mean]
  have hWT_diff_le : ∫ ω, |W₁ ω - T₁ ω| ∂(P p) ≤ 2 * (1 - μK) := by
    let D : ℕ → Ω p → ℝ := fun i ω ↦ |X₁ i ω - Y i ω|
    have hD_meas : ∀ i, Measurable (D i) := fun i ↦
      continuous_abs.measurable.comp ((hX₁_meas i).sub (hY_all_meas i))
    have hD_nn : ∀ i ω, 0 ≤ D i ω := fun _ _ ↦ abs_nonneg _
    have hD_indep : ∀ k : ℕ, IndepFun N₁ (D (k + 1)) (P p) := fun k ↦ by
      have heq : D (k + 1) = (fun x ↦ |x - φ_tr x|) ∘ X₁ (k + 1) := by
        ext ω; simp [D, Y]
      rw [heq]
      exact (hN₁_indep_k k).comp measurable_id
        (continuous_abs.measurable.comp (measurable_id.sub hφ_tr_meas))
    have hC_nn : 0 ≤ 2 * (1 - μK) := by linarith [hμK_le_one]
    have hD_lint : ∀ k : ℕ,
        ∫⁻ ω, ENNReal.ofReal (D (k + 1) ω) ∂(P p) ≤ ENNReal.ofReal (2 * (1 - μK)) := fun k ↦ by
      have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have hX₁k_int : Integrable (X₁ (k + 1)) (P p) :=
        (hX₁_id (k + 1) hk1).symm.integrable_snd hX₀'_int
      have hY₀_int : Integrable Y₀ P₀ :=
        Integrable.of_bound hY₀_meas.aestronglyMeasurable B
          (Eventually.of_forall fun ω₀ ↦ by
            rw [Real.norm_eq_abs, abs_of_nonneg (hY₀_bdd ω₀).1]; exact (hY₀_bdd ω₀).2)
      have hYk_int : Integrable (Y (k + 1)) (P p) :=
        (hY_id (k + 1) hk1).symm.integrable_snd hY₀_int
      have hDk_int : Integrable (D (k + 1)) (P p) := by
        refine (hX₁k_int.sub hYk_int).norm.congr (Eventually.of_forall fun ω ↦ ?_)
        simp [D, Real.norm_eq_abs]
      rw [← ofReal_integral_eq_lintegral_ofReal hDk_int (Eventually.of_forall fun _ ↦ abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hdiff_i_le (k + 1) hk1)
    have hSumD_lint := hSum_lint_bound D hD_meas hD_nn hD_indep hC_nn hD_lint
    have hSumD_int : Integrable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N₁ ω), D i ω) (P p) :=
      ⟨(measurable_select_nat
        (fun n ↦ Finset.measurable_sum _ fun i _ ↦ hD_meas i) hN₁_meas).aestronglyMeasurable, by
        rw [hasFiniteIntegral_iff_ofReal
          (Eventually.of_forall fun ω ↦ Finset.sum_nonneg fun i _ ↦ hD_nn i ω)]
        exact lt_of_le_of_lt hSumD_lint ENNReal.ofReal_lt_top⟩
    have hSumD_le : ∫ ω, (∑ i ∈ Finset.Icc 1 (N₁ ω), D i ω) ∂(P p) ≤ 2 * (1 - μK) / p := by
      rw [← ofReal_integral_eq_lintegral_ofReal hSumD_int
        (Eventually.of_forall fun ω ↦ Finset.sum_nonneg fun i _ ↦ hD_nn i ω)] at hSumD_lint
      exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg hC_nn hp₀.le)).mp hSumD_lint
    have hpt_WT : ∀ ω, |W₁ ω - T₁ ω| ≤ p * ∑ i ∈ Finset.Icc 1 (N₁ ω), D i ω := fun ω ↦ by
      dsimp only [W₁, T₁, D]
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos hp₀]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hp₀.le
    have hWT_abs_int : Integrable (fun ω ↦ |W₁ ω - T₁ ω|) (P p) := by
      refine (hW₁_int.sub hT₁_int).norm.congr (Eventually.of_forall fun ω ↦ ?_)
      simp [Real.norm_eq_abs]
    calc
      ∫ ω, |W₁ ω - T₁ ω| ∂(P p)
          ≤ ∫ ω, p * (∑ i ∈ Finset.Icc 1 (N₁ ω), D i ω) ∂(P p) :=
            integral_mono hWT_abs_int (hSumD_int.const_mul p) hpt_WT
      _ = p * ∫ ω, (∑ i ∈ Finset.Icc 1 (N₁ ω), D i ω) ∂(P p) := integral_const_mul _ _
      _ ≤ p * (2 * (1 - μK) / p) := mul_le_mul_of_nonneg_left hSumD_le hp₀.le
      _ = 2 * (1 - μK) := by field_simp [hp₀.ne']
  rw [Measure.map_congr hW_ae]
  have hstep1 : wassersteinDist ((P p).map W₁) stdExpLaw ≤
      ENNReal.ofReal (∫ ω, |W₁ ω - T₁ ω| ∂(P p)) +
        ENNReal.ofReal (2 * p * (1 + B ^ 2 / 2)) :=
    (wassersteinDist_triangle_integrable (P p) hT₁_int _ _).trans
      (add_le_add (wassersteinDist_map_le_integral_abs_sub (P p) hW₁_int hT₁_int) hT₁_exp)
  have hsum_lt : 2 * (1 - μK) + 2 * p * (1 + B ^ 2 / 2) < 4 * δ := by
    linarith [h1mμK_lt, hp_small]
  have hstep2 : ENNReal.ofReal (∫ ω, |W₁ ω - T₁ ω| ∂(P p)) +
      ENNReal.ofReal (2 * p * (1 + B ^ 2 / 2)) < ENNReal.ofReal (4 * δ) :=
    calc
      ENNReal.ofReal (∫ ω, |W₁ ω - T₁ ω| ∂(P p)) + ENNReal.ofReal (2 * p * (1 + B ^ 2 / 2))
          ≤ ENNReal.ofReal (2 * (1 - μK)) + ENNReal.ofReal (2 * p * (1 + B ^ 2 / 2)) :=
            add_le_add (ENNReal.ofReal_le_ofReal hWT_diff_le) le_rfl
      _ = ENNReal.ofReal (2 * (1 - μK) + 2 * p * (1 + B ^ 2 / 2)) := by
            rw [← ENNReal.ofReal_add (by linarith [hμK_le_one]) (by positivity)]
      _ < ENNReal.ofReal (4 * δ) :=
            ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hsum_lt
  exact le_of_lt (lt_of_le_of_lt hstep1 (lt_of_lt_of_le hstep2 hδ_le))

end SteinMethod
