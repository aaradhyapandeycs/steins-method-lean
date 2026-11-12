/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.GeometricSumsAux

/-!
# Auxiliary Lemmas for Stationarity of Delayed Renewal Processes
(`Formalization.Exponential.RenewalAux`)

Helper lemmas for **Remark 5.3** (`\label{rem171}`, `SteinIntro.tex:2875-2880`), proved in
`Formalization.Exponential.Renewal`:
- Piecewise-linear ramp test function `min (max (x - a) 0) (b - a)` and its derivative;
- Pre-$n$ / post-$n$ independence split `indepFun_past_future`;
- Laplace-transform tail bound `tendsto_measureReal_sum_le_zero`;
- Stationary renewal measure identity `delayed_renewal_measure_clean` on `(a, b]`.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

lemma lipschitzWith_one_ramp (a b : ℝ) :
    LipschitzWith 1 (fun x : ℝ ↦ min (max (x - a) 0) (b - a)) := by
  refine LipschitzWith.mk_one fun u v ↦ ?_
  rw [Real.dist_eq, Real.dist_eq]
  have hmax : |max (u - a) 0 - max (v - a) 0| ≤ |u - v| := by
    rcases le_total (u - a) 0 with hu | hu <;> rcases le_total (v - a) 0 with hv | hv
    · simp [max_eq_right hu, max_eq_right hv]
    · rw [max_eq_right hu, max_eq_left hv, zero_sub, abs_neg, abs_of_nonneg hv]
      exact (by linarith : v - a ≤ v - u).trans
        ((le_abs_self (v - u)).trans (by rw [abs_sub_comm]))
    · rw [max_eq_left hu, max_eq_right hv, sub_zero, abs_of_nonneg hu]
      exact (by linarith : u - a ≤ u - v).trans (le_abs_self (u - v))
    · rw [max_eq_left hu, max_eq_left hv]
      exact le_of_eq (by ring_nf)
  rcases le_total (max (u - a) 0) (b - a) with hu | hu <;>
    rcases le_total (max (v - a) 0) (b - a) with hv | hv
  · rw [min_eq_left hu, min_eq_left hv]; exact hmax
  · rw [min_eq_left hu, min_eq_right hv]
    have hle : (b - a) - max (u - a) 0 ≤ max (v - a) 0 - max (u - a) 0 := by linarith
    have hnn : 0 ≤ (b - a) - max (u - a) 0 := by linarith
    calc
      |max (u - a) 0 - (b - a)| = (b - a) - max (u - a) 0 := by
        rw [abs_sub_comm, abs_of_nonneg hnn]
      _ ≤ |max (u - a) 0 - max (v - a) 0| := by
        rw [abs_sub_comm]; exact hle.trans (le_abs_self _)
      _ ≤ |u - v| := hmax
  · rw [min_eq_right hu, min_eq_left hv]
    have hle : (b - a) - max (v - a) 0 ≤ max (u - a) 0 - max (v - a) 0 := by linarith
    have hnn : 0 ≤ (b - a) - max (v - a) 0 := by linarith
    calc
      |(b - a) - max (v - a) 0| = (b - a) - max (v - a) 0 := abs_of_nonneg hnn
      _ ≤ |max (u - a) 0 - max (v - a) 0| := hle.trans (le_abs_self _)
      _ ≤ |u - v| := hmax
  · simp [min_eq_right hu, min_eq_right hv]

lemma deriv_ramp_eq_indicator {a b x : ℝ} (hab : a ≤ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    deriv (fun u : ℝ ↦ min (max (u - a) 0) (b - a)) x =
      (Ioc a b).indicator (1 : ℝ → ℝ) x := by
  let g : ℝ → ℝ := fun u ↦ min (max (u - a) 0) (b - a)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  rcases lt_trichotomy x a with hlt_a | rfl | hgt_a
  · have h_ev : g =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hlt_a] with u (hu : u < a)
      dsimp only [g]
      rw [max_eq_right (by linarith), min_eq_left hba]
    have hd : HasDerivAt g 0 x := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h_ev
    have hnot : x ∉ Ioc a b := fun hx ↦ by linarith [hx.1]
    rw [hd.deriv, indicator_of_notMem hnot]
  · exact (hxa rfl).elim
  · rcases lt_trichotomy x b with hlt_b | rfl | hgt_b
    · have h_ev : g =ᶠ[𝓝 x] fun u ↦ u - a := by
        filter_upwards [Ioo_mem_nhds hgt_a hlt_b] with u ⟨hu1, hu2⟩
        dsimp only [g]
        rw [max_eq_left (by linarith), min_eq_left (by linarith)]
      have hd : HasDerivAt g 1 x :=
        ((hasDerivAt_id x).sub_const a).congr_of_eventuallyEq h_ev
      have hmem : x ∈ Ioc a b := ⟨hgt_a, hlt_b.le⟩
      rw [hd.deriv, indicator_of_mem hmem, Pi.one_apply]
    · exact (hxb rfl).elim
    · have h_ev : g =ᶠ[𝓝 x] fun _ ↦ b - a := by
        filter_upwards [Ioi_mem_nhds hgt_b] with u (hu : b < u)
        dsimp only [g]
        rw [max_eq_left (by linarith), min_eq_right (by linarith)]
      have hd : HasDerivAt g 0 x := (hasDerivAt_const x (b - a)).congr_of_eventuallyEq h_ev
      have hnot : x ∉ Ioc a b := fun hx ↦ by linarith [hx.2]
      rw [hd.deriv, indicator_of_notMem hnot]

/-- Independence between the pre-$n$ history `(Ye₁, (Yseq₁ r)_{r < n})` and the post-$n$ sequence
`(Yseq₁ (n + j))_{j : ℕ}`. -/
lemma indepFun_past_future {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ye₁ : Ω → ℝ} {Yseq₁ : ℕ → Ω → ℝ}
    (hYe₁_meas : Measurable Ye₁) (hYseq₁_meas : ∀ k, Measurable (Yseq₁ k))
    (hYseq₁_indep : iIndepFun Yseq₁ P)
    (hYe₁_indep : IndepFun Ye₁ (fun ω (k : ℕ) ↦ Yseq₁ k ω) P) (n : ℕ) :
    IndepFun (fun ω ↦ (Ye₁ ω, fun r : Fin n ↦ Yseq₁ r.1 ω))
      (fun ω (j : ℕ) ↦ Yseq₁ (n + j) ω) P := by
  let Yvec : Ω → (ℕ → ℝ) := fun ω k ↦ Yseq₁ k ω
  have hYvec_meas : Measurable Yvec := measurable_pi_iff.mpr hYseq₁_meas
  let A_seq : (ℕ → ℝ) → (ℕ → ℝ) := fun y j ↦ y (n + j)
  let B_seq : (ℕ → ℝ) → (Fin n → ℝ) := fun y r ↦ y r.1
  have hA_meas : Measurable A_seq := measurable_pi_iff.mpr fun j ↦ measurable_pi_apply (n + j)
  have hB_meas : Measurable B_seq := measurable_pi_iff.mpr fun r ↦ measurable_pi_apply r.1
  have hAB_P : IndepFun (A_seq ∘ Yvec) (B_seq ∘ Yvec) P := by
    rw [IndepFun_iff_Indep]
    have hdisj : Disjoint {k : ℕ | n ≤ k} {k : ℕ | k < n} :=
      Set.disjoint_left.mpr fun k h1 h2 ↦ by simp only [mem_ofPred_eq] at h1 h2; omega
    have hind := indep_iSup_of_disjoint (fun k ↦ (hYseq₁_meas k).comap_le)
      hYseq₁_indep.iIndep hdisj
    refine indep_of_indep_of_le hind ?_ ?_
    · change MeasurableSpace.comap (A_seq ∘ Yvec)
          (⨆ j : ℕ, MeasurableSpace.comap (Function.eval j) inferInstance) ≤ _
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun j ↦ ?_
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂_of_le (n + j) (Nat.le_add_right n j) le_rfl
    · change MeasurableSpace.comap (B_seq ∘ Yvec)
          (⨆ r : Fin n, MeasurableSpace.comap (Function.eval r) inferInstance) ≤ _
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun r ↦ ?_
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂_of_le r.1 r.2 le_rfl
  let Q_seq : Measure (ℕ → ℝ) := P.map Yvec
  let Q_e : Measure ℝ := P.map Ye₁
  have : IsProbabilityMeasure Q_seq :=
    (Measure.isProbabilityMeasure_map_iff hYvec_meas.aemeasurable).mpr ‹_›
  have : IsProbabilityMeasure Q_e :=
    (Measure.isProbabilityMeasure_map_iff hYe₁_meas.aemeasurable).mpr ‹_›
  have hAB_Q : IndepFun A_seq B_seq Q_seq := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s u hs hu
    rw [Measure.map_apply hYvec_meas ((hA_meas hs).inter (hB_meas hu)),
      Measure.map_apply hYvec_meas (hA_meas hs), Measure.map_apply hYvec_meas (hB_meas hu)]
    exact hAB_P.measure_inter_preimage_eq_mul s u hs hu
  have hprod_indep := indepFun_fst_comp_prod_snd (ν := Q_e) hA_meas hB_meas hAB_Q
  have hswap_indep : IndepFun (fun q : (ℕ → ℝ) × ℝ ↦ (q.2, B_seq q.1))
      (fun q : (ℕ → ℝ) × ℝ ↦ A_seq q.1) (Q_seq.prod Q_e) :=
    (hprod_indep.comp measurable_id measurable_swap).symm
  have hmap_prod : P.map (fun ω ↦ (Yvec ω, Ye₁ ω)) = Q_seq.prod Q_e :=
    hYe₁_indep.symm.map_prod_eq_prod_map_map hYvec_meas.aemeasurable hYe₁_meas.aemeasurable
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s u hs hu
  let Ψ : Ω → (ℕ → ℝ) × ℝ := fun ω ↦ (Yvec ω, Ye₁ ω)
  have hΨ_meas : Measurable Ψ := hYvec_meas.prodMk hYe₁_meas
  let G₁ : (ℕ → ℝ) × ℝ → ℝ × (Fin n → ℝ) := fun q ↦ (q.2, B_seq q.1)
  let G₂ : (ℕ → ℝ) × ℝ → (ℕ → ℝ) := fun q ↦ A_seq q.1
  have hG₁_meas : Measurable G₁ := measurable_snd.prodMk (hB_meas.comp measurable_fst)
  have hG₂_meas : Measurable G₂ := hA_meas.comp measurable_fst
  change P (Ψ ⁻¹' (G₁ ⁻¹' s ∩ G₂ ⁻¹' u)) = P (Ψ ⁻¹' (G₁ ⁻¹' s)) * P (Ψ ⁻¹' (G₂ ⁻¹' u))
  rw [← Measure.map_apply hΨ_meas ((hG₁_meas hs).inter (hG₂_meas hu)),
    ← Measure.map_apply hΨ_meas (hG₁_meas hs), ← Measure.map_apply hΨ_meas (hG₂_meas hu),
    hmap_prod]
  exact hswap_indep.measure_inter_preimage_eq_mul s u hs hu

/-- Laplace-transform tail bound for i.i.d. non-negative sums with positive mean:
`P.real {ω | ∑_{k < n} Yseq₁ k ω ≤ B} → 0` as `n → ∞`. -/
lemma tendsto_measureReal_sum_le_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y₁ : Ω → ℝ} {Yseq₁ : ℕ → Ω → ℝ}
    (hY₁_meas : Measurable Y₁) (hY₁_nn : ∀ ω, 0 ≤ Y₁ ω) (hY₁_int : Integrable Y₁ P)
    (hμ_pos : 0 < ∫ ω, Y₁ ω ∂P) (hYseq₁_meas : ∀ k, Measurable (Yseq₁ k))
    (hYseq₁_nn : ∀ k ω, 0 ≤ Yseq₁ k ω) (hYseq₁_indep : iIndepFun Yseq₁ P)
    (hYseq₁_id : ∀ k, IdentDistrib (Yseq₁ k) Y₁ P P) (B : ℝ) :
    Tendsto (fun n : ℕ ↦ P.real {ω | ∑ k ∈ Finset.range n, Yseq₁ k ω ≤ B}) atTop (𝓝 0) := by
  set μ : ℝ := ∫ ω, Y₁ ω ∂P
  set q : ℝ := ∫ ω, Real.exp (- Y₁ ω) ∂P
  have hexp_meas : Measurable fun x : ℝ ↦ Real.exp (- x) :=
    (Real.continuous_exp.comp continuous_neg).measurable
  have hexp_int : Integrable (fun ω ↦ Real.exp (- Y₁ ω)) P :=
    Integrable.of_bound (hexp_meas.comp hY₁_meas).aestronglyMeasurable 1
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hY₁_nn ω)))
  have hq_nn : 0 ≤ q := integral_nonneg fun ω ↦ (Real.exp_pos _).le
  have hq_lt_one : q < 1 := by
    let A : Set Ω := {ω | μ / 2 ≤ Y₁ ω}
    have hA_meas : MeasurableSet A := hY₁_meas measurableSet_Ici
    have hPA_pos : 0 < P.real A := by
      by_contra hle
      have hPA0 : P A = 0 := by
        have h0 : P.real A = 0 := le_antisymm (not_lt.mp hle) measureReal_nonneg
        rwa [measureReal_eq_zero_iff] at h0
      have hae_le : Y₁ ≤ᵐ[P] fun _ ↦ μ / 2 := by
        rw [EventuallyLE, eventually_iff_exists_mem]
        refine ⟨Aᶜ, mem_ae_iff.mpr (by simpa using hPA0), fun ω hω ↦ ?_⟩
        simp only [mem_compl_iff, mem_ofPred_eq, not_le, A] at hω
        exact hω.le
      have hint_le : μ ≤ μ / 2 := by
        have h := integral_mono_ae hY₁_int (integrable_const (μ / 2)) hae_le
        rwa [integral_const, probReal_univ, one_smul] at h
      linarith
    let c₀ : ℝ := 1 - Real.exp (- (μ / 2))
    have hc₀_pos : 0 < c₀ := by
      dsimp only [c₀]
      have : Real.exp (- (μ / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have h1mq : 1 - q = ∫ ω, (1 - Real.exp (- Y₁ ω)) ∂P := by
      have h1 := integral_sub (integrable_const (1 : ℝ)) hexp_int
      rw [integral_const, probReal_univ, one_smul] at h1
      exact h1.symm
    have hpt : ∀ ω, A.indicator (fun _ ↦ c₀) ω ≤ 1 - Real.exp (- Y₁ ω) := fun ω ↦ by
      by_cases hω : ω ∈ A
      · rw [indicator_of_mem hω]
        have hle_exp : Real.exp (- Y₁ ω) ≤ Real.exp (- (μ / 2)) :=
          Real.exp_le_exp.mpr (neg_le_neg hω)
        dsimp only [c₀]; linarith
      · rw [indicator_of_notMem hω]
        have : Real.exp (- Y₁ ω) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hY₁_nn ω))
        linarith
    have hint_ge : c₀ * P.real A ≤ 1 - q := by
      rw [h1mq]
      have h := integral_mono ((integrable_const c₀).indicator hA_meas)
        ((integrable_const (1 : ℝ)).sub hexp_int) hpt
      rwa [integral_indicator_const c₀ hA_meas, smul_eq_mul, mul_comm] at h
    linarith [mul_pos hc₀_pos hPA_pos]
  let T : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n, Yseq₁ k ω
  have hT_meas : ∀ n, Measurable (T n) := fun n ↦
    Finset.measurable_sum _ fun k _ ↦ hYseq₁_meas k
  have hT_nn : ∀ n ω, 0 ≤ T n ω := fun n ω ↦ Finset.sum_nonneg fun k _ ↦ hYseq₁_nn k ω
  have hexp_T : ∀ n : ℕ, ∫ ω, Real.exp (- T n ω) ∂P = q ^ n := by
    intro n
    induction n with
    | zero =>
      simp [T]
    | succ n ih =>
      have hind_n : IndepFun (T n) (Yseq₁ n) P := by
        have hc := iIndepFun_indepFun_compl hYseq₁_indep hYseq₁_meas n
        let idx : Fin n → {j : ℕ // j ≠ n} := fun r ↦ ⟨r.1, ne_of_lt r.2⟩
        let ψ : ({j : ℕ // j ≠ n} → ℝ) → ℝ := fun z ↦ ∑ r : Fin n, z (idx r)
        have hψ : Measurable ψ := Finset.measurable_sum _ fun r _ ↦ measurable_pi_apply (idx r)
        have hTn_eq : T n = ψ ∘ fun ω (j : {j : ℕ // j ≠ n}) ↦ Yseq₁ j.1 ω := by
          ext ω; dsimp only [T, ψ, Function.comp_apply, idx]
          rw [← Fin.sum_univ_eq_sum_range]
        rw [hTn_eq]
        exact (hc.comp measurable_id hψ).symm
      have hsplit : (fun ω ↦ Real.exp (- T (n + 1) ω)) =
          fun ω ↦ Real.exp (- T n ω) * Real.exp (- Yseq₁ n ω) := by
        ext ω
        dsimp only [T]
        rw [Finset.sum_range_succ, neg_add, Real.exp_add]
      have hid_n : ∫ ω, Real.exp (- Yseq₁ n ω) ∂P = q :=
        ((hYseq₁_id n).comp hexp_meas).integral_eq
      have hmul := (hind_n.comp hexp_meas hexp_meas).integral_mul_eq_mul_integral
        (hexp_meas.comp (hT_meas n)).aestronglyMeasurable
        (hexp_meas.comp (hYseq₁_meas n)).aestronglyMeasurable
      dsimp only [Pi.mul_apply, Function.comp_apply] at hmul
      rw [hsplit, hmul, ih, hid_n, pow_succ]
  have hmarkov : ∀ n : ℕ, P.real {ω | T n ω ≤ B} ≤ Real.exp B * q ^ n := fun n ↦ by
    have hT_int : Integrable (fun ω ↦ Real.exp (- T n ω)) P :=
      Integrable.of_bound (hexp_meas.comp (hT_meas n)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hT_nn n ω)))
    have hpt : ∀ ω, {ω' | T n ω' ≤ B}.indicator (fun _ ↦ Real.exp (- B)) ω ≤
        Real.exp (- T n ω) := fun ω ↦ by
      by_cases hω : ω ∈ {ω' | T n ω' ≤ B}
      · rw [indicator_of_mem hω]
        exact Real.exp_le_exp.mpr (neg_le_neg hω)
      · rw [indicator_of_notMem hω]
        exact (Real.exp_pos _).le
    have hint := integral_mono
      ((integrable_const (Real.exp (- B))).indicator (hT_meas n measurableSet_Iic)) hT_int hpt
    rw [integral_indicator_const _ (hT_meas n measurableSet_Iic), smul_eq_mul, hexp_T n] at hint
    calc
      P.real {ω | T n ω ≤ B}
          = Real.exp B * (P.real {ω | T n ω ≤ B} * Real.exp (- B)) := by
            rw [← mul_assoc, mul_comm (Real.exp B), mul_assoc, ← Real.exp_add, add_neg_cancel,
              Real.exp_zero, mul_one]
      _ ≤ Real.exp B * q ^ n := mul_le_mul_of_nonneg_left hint (Real.exp_pos B).le
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) hmarkov ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt_one).const_mul (Real.exp B)

/-- Renewal measure identity on `(a, b]` for measurable non-negative delayed renewal sequences. -/
lemma delayed_renewal_measure_clean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y₁ Ye₁ : Ω → ℝ} {Yseq₁ : ℕ → Ω → ℝ}
    (hY₁_meas : Measurable Y₁) (hY₁_nn : ∀ ω, 0 ≤ Y₁ ω) (hY₁_int : Integrable Y₁ P)
    (hμ_pos : 0 < ∫ ω, Y₁ ω ∂P) (hYe₁_meas : Measurable Ye₁)
    (hYe₁_ac : Measure.AbsolutelyContinuous (P.map Ye₁) volume)
    (hYe₁_eq : IsEquilibrium P Y₁ P Ye₁)
    (hYseq₁_meas : ∀ k, Measurable (Yseq₁ k)) (hYseq₁_nn : ∀ k ω, 0 ≤ Yseq₁ k ω)
    (hYseq₁_indep : iIndepFun Yseq₁ P) (hYseq₁_id : ∀ k, IdentDistrib (Yseq₁ k) Y₁ P P)
    (hYe₁_indep : IndepFun Ye₁ (fun ω (k : ℕ) ↦ Yseq₁ k ω) P)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑' n : ℕ, P {ω | Ye₁ ω + (∑ k ∈ Finset.range n, Yseq₁ k ω) ∈ Ioc a b} =
      ENNReal.ofReal ((b - a) / ∫ ω, Y₁ ω ∂P) := by
  set μ : ℝ := ∫ ω, Y₁ ω ∂P
  let T : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n, Yseq₁ k ω
  let S₁ : ℕ → Ω → ℝ := fun n ω ↦ Ye₁ ω + T n ω
  have hT_meas : ∀ n, Measurable (T n) := fun n ↦
    Finset.measurable_sum _ fun k _ ↦ hYseq₁_meas k
  have hS₁_meas : ∀ n, Measurable (S₁ n) := fun n ↦ hYe₁_meas.add (hT_meas n)
  let g : ℝ → ℝ := fun x ↦ min (max (x - a) 0) (b - a)
  have hg_lip : LipschitzWith 1 g := lipschitzWith_one_ramp a b
  have hg_meas : Measurable g := hg_lip.continuous.measurable
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hg0 : g 0 = 0 := by
    dsimp only [g]
    rw [max_eq_right (by linarith), min_eq_left hba]
  have hg_bdd : ∀ x : ℝ, 0 ≤ g x ∧ g x ≤ b - a := fun x ↦
    ⟨le_min (le_max_right _ 0) hba, min_le_right _ _⟩
  have hg_ge_b : ∀ x : ℝ, b ≤ x → g x = b - a := fun x hbx ↦ by
    dsimp only [g]
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  have hstep : ∀ k : ℕ,
      (∫ ω, g (T (k + 1) ω) ∂P) - (∫ ω, g (T k ω) ∂P) =
        μ * P.real {ω | S₁ k ω ∈ Ioc a b} := fun k ↦ by
    have hTk_Y_indep : IndepFun (T k) (Yseq₁ k) P := by
      have hpast_fut := indepFun_past_future hYe₁_meas hYseq₁_meas hYseq₁_indep hYe₁_indep k
      let φ₁ : ℝ × (Fin k → ℝ) → ℝ := fun q ↦ ∑ r : Fin k, q.2 r
      let φ₂ : (ℕ → ℝ) → ℝ := fun z ↦ z 0
      have hφ₁ : Measurable φ₁ :=
        Finset.measurable_sum _ fun r _ ↦ (measurable_pi_apply r).comp measurable_snd
      have hφ₂ : Measurable φ₂ := measurable_pi_apply 0
      have heq1 : T k = φ₁ ∘ fun ω ↦ (Ye₁ ω, fun r : Fin k ↦ Yseq₁ r.1 ω) := by
        ext ω; dsimp only [T, φ₁, Function.comp_apply]
        rw [← Fin.sum_univ_eq_sum_range]
      have heq2 : Yseq₁ k = φ₂ ∘ fun ω (j : ℕ) ↦ Yseq₁ (k + j) ω := by
        ext ω; simp [φ₂]
      rw [heq1, heq2]
      exact hpast_fut.comp hφ₁ hφ₂
    have hTk_Ye_indep : IndepFun (T k) Ye₁ P := by
      let ψ : (ℕ → ℝ) → ℝ := fun z ↦ ∑ j ∈ Finset.range k, z j
      have hψ : Measurable ψ := Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
      exact (hYe₁_indep.comp measurable_id hψ).symm
    have : IsProbabilityMeasure (P.map (T k)) :=
      (Measure.isProbabilityMeasure_map_iff (hT_meas k).aemeasurable).mpr ‹_›
    have : IsProbabilityMeasure (P.map (Yseq₁ k)) :=
      (Measure.isProbabilityMeasure_map_iff (hYseq₁_meas k).aemeasurable).mpr ‹_›
    have : IsProbabilityMeasure (P.map Ye₁) :=
      (Measure.isProbabilityMeasure_map_iff hYe₁_meas.aemeasurable).mpr ‹_›
    let Φ₁ : ℝ × ℝ → ℝ := fun q ↦ g (q.1 + q.2) - g q.1
    let Φ₂ : ℝ × ℝ → ℝ := fun q ↦ (Ioc a b).indicator 1 (q.1 + q.2)
    have hΦ₁_meas : Measurable Φ₁ :=
      (hg_meas.comp (measurable_fst.add measurable_snd)).sub (hg_meas.comp measurable_fst)
    have hΦ₂_meas : Measurable Φ₂ :=
      (measurable_const.indicator measurableSet_Ioc).comp (measurable_fst.add measurable_snd)
    have hΦ₁_int : Integrable Φ₁ ((P.map (T k)).prod (P.map (Yseq₁ k))) :=
      Integrable.of_bound hΦ₁_meas.aestronglyMeasurable (b - a)
        (Eventually.of_forall fun q ↦ by
          rw [Real.norm_eq_abs]
          have h1 := hg_bdd (q.1 + q.2)
          have h2 := hg_bdd q.1
          exact abs_le.mpr ⟨by linarith, by linarith⟩)
    have hΦ₂_int : Integrable Φ₂ ((P.map (T k)).prod (P.map Ye₁)) :=
      Integrable.of_bound hΦ₂_meas.aestronglyMeasurable 1
        (Eventually.of_forall fun q ↦ by
          dsimp only [Φ₂]
          by_cases hq : q.1 + q.2 ∈ Ioc a b
          · simp [hq]
          · simp [hq])
    have hgTk_int : ∀ m, Integrable (fun ω ↦ g (T m ω)) P := fun m ↦
      Integrable.of_bound (hg_meas.comp (hT_meas m)).aestronglyMeasurable (b - a)
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg_bdd _).1]; exact (hg_bdd _).2)
    have hlhs_fub : (∫ ω, g (T (k + 1) ω) ∂P) - (∫ ω, g (T k ω) ∂P) =
        ∫ s, (∫ ω, (g (s + Y₁ ω) - g s) ∂P) ∂(P.map (T k)) := by
      rw [← integral_sub (hgTk_int (k + 1)) (hgTk_int k)]
      have h1 : (fun ω ↦ g (T (k + 1) ω) - g (T k ω)) = fun ω ↦ Φ₁ (T k ω, Yseq₁ k ω) := by
        ext ω; dsimp only [Φ₁, T]; rw [Finset.sum_range_succ]
      rw [h1, ← integral_map ((hT_meas k).prodMk (hYseq₁_meas k)).aemeasurable
        hΦ₁_meas.aestronglyMeasurable,
        hTk_Y_indep.map_prod_eq_prod_map_map (hT_meas k).aemeasurable
          (hYseq₁_meas k).aemeasurable,
        integral_prod Φ₁ hΦ₁_int]
      refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
      let ψs : ℝ → ℝ := fun y ↦ g (s + y) - g s
      have hψs_meas : Measurable ψs :=
        (hg_meas.comp (measurable_const.add measurable_id)).sub measurable_const
      change ∫ y, ψs y ∂(P.map (Yseq₁ k)) = ∫ ω, ψs (Y₁ ω) ∂P
      rw [integral_map (hYseq₁_meas k).aemeasurable hψs_meas.aestronglyMeasurable]
      exact ((hYseq₁_id k).comp hψs_meas).integral_eq
    have hrhs_fub : P.real {ω | S₁ k ω ∈ Ioc a b} =
        ∫ s, (∫ ω, (Ioc a b).indicator (1 : ℝ → ℝ) (s + Ye₁ ω) ∂P) ∂(P.map (T k)) := by
      have hind_int : P.real {ω | S₁ k ω ∈ Ioc a b} =
          ∫ ω, Φ₂ (T k ω, Ye₁ ω) ∂P := by
        have hc : (fun ω ↦ Φ₂ (T k ω, Ye₁ ω)) = {ω | S₁ k ω ∈ Ioc a b}.indicator 1 := by
          ext ω; dsimp only [Φ₂, S₁]
          rw [add_comm (T k ω) (Ye₁ ω)]
          by_cases hω : Ye₁ ω + T k ω ∈ Ioc a b
          · have hω' : ω ∈ {ω' | Ye₁ ω' + T k ω' ∈ Ioc a b} := hω
            rw [indicator_of_mem hω, indicator_of_mem hω']; rfl
          · have hω' : ω ∉ {ω' | Ye₁ ω' + T k ω' ∈ Ioc a b} := hω
            rw [indicator_of_notMem hω, indicator_of_notMem hω']
        rw [hc]
        exact (integral_indicator_one (hS₁_meas k measurableSet_Ioc)).symm
      rw [hind_int, ← integral_map ((hT_meas k).prodMk hYe₁_meas).aemeasurable
        hΦ₂_meas.aestronglyMeasurable,
        hTk_Ye_indep.map_prod_eq_prod_map_map (hT_meas k).aemeasurable hYe₁_meas.aemeasurable,
        integral_prod Φ₂ hΦ₂_int]
      refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
      let ψs₂ : ℝ → ℝ := fun y ↦ (Ioc a b).indicator (1 : ℝ → ℝ) (s + y)
      have hψs₂_meas : Measurable ψs₂ :=
        (measurable_const.indicator measurableSet_Ioc).comp (measurable_const.add measurable_id)
      change ∫ y, ψs₂ y ∂(P.map Ye₁) = ∫ ω, ψs₂ (Ye₁ ω) ∂P
      exact integral_map hYe₁_meas.aemeasurable hψs₂_meas.aestronglyMeasurable
    have hslice : ∀ s : ℝ, ∫ ω, (g (s + Y₁ ω) - g s) ∂P =
        μ * ∫ ω, (Ioc a b).indicator (1 : ℝ → ℝ) (s + Ye₁ ω) ∂P := fun s ↦ by
      let gs : ℝ → ℝ := fun u ↦ g (s + u)
      have hgs_lip : LipschitzWith 1 gs := by
        refine LipschitzWith.mk_one fun u v ↦ ?_
        simpa [gs, Real.dist_eq] using hg_lip.dist_le_mul (s + u) (s + v)
      have hgs_int : Integrable (fun ω ↦ gs (Y₁ ω)) P :=
        integrable_comp_of_lipschitz hY₁_int hgs_lip
      have heq := hYe₁_eq.2.2.2 gs ⟨1, hgs_lip⟩
      have hgs0 : gs 0 = g s := by simp [gs]
      rw [hgs0] at heq
      rw [integral_sub hgs_int (integrable_const (g s)), integral_const, probReal_univ,
        one_smul, heq]
      congr 1
      have hne : ∀ c : ℝ, ∀ᵐ ω ∂P, Ye₁ ω ≠ c := fun c ↦ by
        rw [ae_iff]
        have h0 : (P.map Ye₁) ({c} : Set ℝ) = 0 := hYe₁_ac (by simp)
        rw [Measure.map_apply hYe₁_meas (measurableSet_singleton c)] at h0
        convert h0 using 2
        ext ω; simp
      refine integral_congr_ae (((hne (a - s)).and (hne (b - s))).mono fun ω ⟨h1, h2⟩ ↦ ?_)
      have hxa : s + Ye₁ ω ≠ a := fun h ↦ h1 (by linarith)
      have hxb : s + Ye₁ ω ≠ b := fun h ↦ h2 (by linarith)
      dsimp only [gs]
      rw [deriv_comp_const_add_eq g s (Ye₁ ω), deriv_ramp_eq_indicator hab hxa hxb]
    rw [hlhs_fub, hrhs_fub, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hslice)
  have hsum_K : ∀ K : ℕ,
      ∑ k ∈ Finset.range K, P.real {ω | S₁ k ω ∈ Ioc a b} =
        (∫ ω, g (T K ω) ∂P) / μ := fun K ↦ by
    have hmul : μ * ∑ k ∈ Finset.range K, P.real {ω | S₁ k ω ∈ Ioc a b} =
        ∫ ω, g (T K ω) ∂P := by
      rw [Finset.mul_sum]
      have hcongr : ∀ k : ℕ, μ * P.real {ω | S₁ k ω ∈ Ioc a b} =
          (∫ ω, g (T (k + 1) ω) ∂P) - ∫ ω, g (T k ω) ∂P := fun k ↦ (hstep k).symm
      simp_rw [hcongr]
      rw [Finset.sum_range_sub (fun k ↦ ∫ ω, g (T k ω) ∂P) K]
      have hT0 : (fun ω ↦ g (T 0 ω)) = fun _ ↦ (0 : ℝ) := by ext ω; simp [T, hg0]
      rw [hT0, integral_zero, sub_zero]
    rw [← hmul, mul_div_cancel_left₀ _ hμ_pos.ne']
  have hgTK_tendsto : Tendsto (fun K : ℕ ↦ ∫ ω, g (T K ω) ∂P) atTop (𝓝 (b - a)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have htail := tendsto_measureReal_sum_le_zero P hY₁_meas hY₁_nn hY₁_int hμ_pos
      hYseq₁_meas hYseq₁_nn hYseq₁_indep hYseq₁_id b
    have hprod : Tendsto (fun K : ℕ ↦ (b - a) * P.real {ω | T K ω ≤ b}) atTop (𝓝 0) := by
      simpa using htail.const_mul (b - a)
    rw [Metric.tendsto_atTop] at hprod
    obtain ⟨N₀, hN₀⟩ := hprod ε hε
    refine ⟨N₀, fun K hK ↦ ?_⟩
    have hgTK_int : Integrable (fun ω ↦ g (T K ω)) P :=
      Integrable.of_bound (hg_meas.comp (hT_meas K)).aestronglyMeasurable (b - a)
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg_bdd _).1]; exact (hg_bdd _).2)
    have hdiff_le : |(b - a) - ∫ ω, g (T K ω) ∂P| ≤ (b - a) * P.real {ω | T K ω ≤ b} := by
      have h1 : (b - a) - ∫ ω, g (T K ω) ∂P = ∫ ω, ((b - a) - g (T K ω)) ∂P := by
        rw [integral_sub (integrable_const (b - a)) hgTK_int, integral_const, probReal_univ,
          one_smul]
      have hnn_int : 0 ≤ ∫ ω, ((b - a) - g (T K ω)) ∂P :=
        integral_nonneg fun ω ↦ sub_nonneg.mpr (hg_bdd _).2
      rw [h1, abs_of_nonneg hnn_int]
      have hpt : ∀ ω, (b - a) - g (T K ω) ≤
          {ω' | T K ω' ≤ b}.indicator (fun _ ↦ b - a) ω := fun ω ↦ by
        by_cases hω : ω ∈ {ω' | T K ω' ≤ b}
        · rw [indicator_of_mem hω]; linarith [(hg_bdd (T K ω)).1]
        · rw [indicator_of_notMem hω, hg_ge_b (T K ω) (not_le.mp hω).le, sub_self]
      have hm := integral_mono ((integrable_const (b - a)).sub hgTK_int)
        ((integrable_const (b - a)).indicator (hT_meas K measurableSet_Iic)) hpt
      rwa [integral_indicator_const _ (hT_meas K measurableSet_Iic), smul_eq_mul,
        mul_comm] at hm
    rw [Real.dist_eq, abs_sub_comm]
    have hK_lt := hN₀ K hK
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hba measureReal_nonneg)] at hK_lt
    exact hdiff_le.trans_lt hK_lt
  have hsum_real_tendsto :
      Tendsto (fun K : ℕ ↦ ∑ k ∈ Finset.range K, P.real {ω | S₁ k ω ∈ Ioc a b})
        atTop (𝓝 ((b - a) / μ)) := by
    simp_rw [hsum_K]
    exact hgTK_tendsto.div_const μ
  have hsum_enn_tendsto :
      Tendsto (fun K : ℕ ↦ ∑ k ∈ Finset.range K, P {ω | S₁ k ω ∈ Ioc a b})
        atTop (𝓝 (ENNReal.ofReal ((b - a) / μ))) := by
    have hcongr : (fun K : ℕ ↦ ∑ k ∈ Finset.range K, P {ω | S₁ k ω ∈ Ioc a b}) =
        fun K ↦ ENNReal.ofReal (∑ k ∈ Finset.range K, P.real {ω | S₁ k ω ∈ Ioc a b}) := by
      ext K
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ measureReal_nonneg]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      exact (ofReal_measureReal (measure_ne_top P _)).symm
    rw [hcongr]
    exact (ENNReal.continuous_ofReal.tendsto _).comp hsum_real_tendsto
  exact tendsto_nhds_unique ENNReal.summable.hasSum.tendsto_sum_nat hsum_enn_tendsto

end SteinMethod
