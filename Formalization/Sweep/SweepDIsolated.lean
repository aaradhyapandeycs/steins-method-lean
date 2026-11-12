/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.RandomGraph.IsolatedCoupling
import Formalization.RandomGraph.IsolatedMoments
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# SWEEP-D Example 4.5 Footnote Comparison (`Formalization.Sweep.SweepDIsolated`)

Proves `ex4_5_footnote_comparison` (`Ex4_5_footnote_comparison`, `SteinIntro.tex:2181-2186`,
referencing Section 3.4 `SteinIntro.tex:1380-1388`; `docs/reviews/stmts-review-SWEEP-D.md`
`D-D1` / `SD-4`): under Section 3.4's proof-method conditioning on the graph $G \sim G(n, p)$,
1. for the randomized Corollary 4.11 coupling $W^s_{\mathrm{rand}}(G, I) = W^s_{(I)}(G)$
   ($I \sim \mathrm{Unif}(\mathrm{Fin}\,n)$ independent of $G$),
   $\operatorname{Var}(\mathbb{E}[W^s_{\mathrm{rand}} - W \mid G]) =
   \frac{1}{n^2}\operatorname{Var}(\sum_{i=1}^n (W^s_{(i)} - W))$;
2. in the sparse normal regime $p_n = c / n$ ($c > 0$), for the deterministic Corollary 4.12
   coupling $W^s_{\mathrm{fix}} = W^s_{(v_1)}$, the un-averaged Section 3.4 upper-bound term
   $\frac{\mu_n}{\sigma_n^2}\sqrt{\operatorname{Var}(W^s_{\mathrm{fix}} - W)}$ stays bounded away
   from $0$ as $n \to \infty$.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

private lemma condExp_fst_prod_finite_er {α β : Type*} [Finite α] [Finite β]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : α × β → ℝ) :
    (fun ω : α × β ↦ ∫ b, f (ω.1, b) ∂ν) =ᵐ[μ.prod ν]
      (μ.prod ν)[f | MeasurableSpace.comap Prod.fst inferInstance] := by
  let g₀ : α → ℝ := fun a ↦ ∫ b, f (a, b) ∂ν
  have hg_sm : StronglyMeasurable[MeasurableSpace.comap (Prod.fst : α × β → α) inferInstance]
      (g₀ ∘ Prod.fst) :=
    (measurable_of_finite g₀).stronglyMeasurable.comp_measurable (comap_measurable Prod.fst)
  have hf_int : Integrable f (μ.prod ν) := Integrable.of_finite
  have hg_int : Integrable (g₀ ∘ Prod.fst) (μ.prod ν) := Integrable.of_finite
  refine ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf_int
    (fun _ _ _ ↦ hg_int.integrableOn) (fun s hs _ ↦ ?_) hg_sm.aestronglyMeasurable
  rcases hs with ⟨A, hA, rfl⟩
  have hs_meas : MeasurableSet (Prod.fst ⁻¹' A : Set (α × β)) := measurable_fst hA
  change ∫ x in Prod.fst ⁻¹' A, (g₀ ∘ Prod.fst) x ∂(μ.prod ν) = _
  rw [← integral_indicator hs_meas, ← integral_indicator hs_meas,
    integral_prod _ (hg_int.indicator hs_meas), integral_prod _ (hf_int.indicator hs_meas)]
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  dsimp only
  by_cases ha : a ∈ A
  · have h1 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator (g₀ ∘ Prod.fst) (a, b)) =
        fun _ ↦ g₀ a :=
      funext fun _ ↦ Set.indicator_of_mem (s := Prod.fst ⁻¹' A) ha (g₀ ∘ Prod.fst)
    have h2 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator f (a, b)) = fun b ↦ f (a, b) :=
      funext fun _ ↦ Set.indicator_of_mem (s := Prod.fst ⁻¹' A) ha f
    rw [h1, h2, integral_const, probReal_univ, one_smul]
  · have h1 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator (g₀ ∘ Prod.fst) (a, b)) = 0 :=
      funext fun _ ↦ Set.indicator_of_notMem (s := Prod.fst ⁻¹' A) ha (g₀ ∘ Prod.fst)
    have h2 : (fun b : β ↦ (Prod.fst ⁻¹' A).indicator f (a, b)) = 0 :=
      funext fun _ ↦ Set.indicator_of_notMem (s := Prod.fst ⁻¹' A) ha f
    rw [h1, h2]

private lemma deleteIncidenceSet_eq_self_of_isIsolated {n : ℕ} {H : SimpleGraph (Fin n)}
    {i : Fin n} (hiso : H.IsIsolated i) :
    H.deleteIncidenceSet i = H := by
  ext u w
  rw [SimpleGraph.deleteIncidenceSet_adj]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_, ?_⟩⟩
  · rintro rfl; exact hiso w h
  · rintro rfl; exact hiso u (H.adj_symm h)

private lemma isIsolated_deleteIncidenceSet_of_isIsolated {n : ℕ} {H : SimpleGraph (Fin n)}
    (i j : Fin n) (hiso : H.IsIsolated j) :
    (H.deleteIncidenceSet i).IsIsolated j :=
  fun w hw ↦ hiso w (SimpleGraph.deleteIncidenceSet_adj.mp hw).1

private lemma exp_neg_two_mul_le_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    Real.exp (-2 * t) ≤ 1 - t := by
  have h1 : 1 ≤ (1 - t) * (1 + 2 * t) := by nlinarith
  have h2 : 1 + 2 * t ≤ Real.exp (2 * t) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * t)
  have h3 : 1 ≤ (1 - t) * Real.exp (2 * t) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
  have hexp_pos : 0 < Real.exp (2 * t) := Real.exp_pos _
  rw [show -2 * t = -(2 * t) by ring, Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀' hexp_pos).mpr (by simpa [mul_comm] using h3)

private lemma quarter_min_prob_le_variance_of_zero_one_sep {Ω : Type*} [Finite Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} {E : Set Ω}
    (hE0 : ∀ ω ∈ E, Z ω = 0) (hEc1 : ∀ ω ∉ E, 1 ≤ Z ω) :
    (1 / 4 : ℝ) * min (P.real E) (1 - P.real E) ≤ ProbabilityTheory.variance Z P := by
  have hZ_mem : MemLp Z 2 P :=
    (integrable_norm_rpow_iff (Integrable.of_finite : Integrable Z P).aestronglyMeasurable
      two_ne_zero ENNReal.ofNat_ne_top).mp Integrable.of_finite
  rw [ProbabilityTheory.variance_eq_integral hZ_mem.aemeasurable]
  set m : ℝ := ∫ ω, Z ω ∂P
  have hE_meas : MeasurableSet E := MeasurableSet.of_discrete
  have hcompl_prob : P.real Eᶜ = 1 - P.real E := probReal_compl_eq_one_sub hE_meas
  rcases le_or_gt m (1 / 2) with hm | hm
  · calc (1 / 4 : ℝ) * min (P.real E) (1 - P.real E)
      _ ≤ (1 / 4 : ℝ) * (1 - P.real E) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ = ∫ ω, (1 / 4 : ℝ) * Eᶜ.indicator 1 ω ∂P := by
        rw [integral_const_mul, integral_indicator_one hE_meas.compl, hcompl_prob]
      _ ≤ ∫ ω, (Z ω - m) ^ 2 ∂P := by
        refine integral_mono_ae Integrable.of_finite Integrable.of_finite
          (Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases hω : ω ∈ E
        · have hnot : ω ∉ Eᶜ := fun hc ↦ hc hω
          rw [Set.indicator_of_notMem hnot, mul_zero]
          exact sq_nonneg _
        · have hmem : ω ∈ Eᶜ := hω
          rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
          have hge := hEc1 ω hω
          nlinarith
  · calc (1 / 4 : ℝ) * min (P.real E) (1 - P.real E)
      _ ≤ (1 / 4 : ℝ) * P.real E :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ = ∫ ω, (1 / 4 : ℝ) * E.indicator 1 ω ∂P := by
        rw [integral_const_mul, integral_indicator_one hE_meas]
      _ ≤ ∫ ω, (Z ω - m) ^ 2 ∂P := by
        refine integral_mono_ae Integrable.of_finite Integrable.of_finite
          (Eventually.of_forall fun ω ↦ ?_)
        dsimp only
        by_cases hω : ω ∈ E
        · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one, hE0 ω hω]
          nlinarith
        · rw [Set.indicator_of_notMem hω, mul_zero]
          exact sq_nonneg _

/-- Example 4.5 footnote comparison under the Section 3.4 proof-method reading
(`SteinIntro.tex:2181-2186`, referencing `SteinIntro.tex:1380-1388`;
`docs/reviews/stmts-review-SWEEP-D.md` `D-D1` / `SD-4`). -/
theorem ex4_5_footnote_comparison :
    (∀ {n : ℕ} (hn : 0 < n) {p : ℝ},
      0 ≤ p →
      p ≤ 1 →
      let v0 : Fin n := ⟨0, hn⟩
      let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
      let μI : Measure (Fin n) :=
        (@PMF.uniformOfFintype (Fin n) inferInstance ⟨v0⟩).toMeasure
      let Q : Measure (SimpleGraph (Fin n) × Fin n) := P.prod μI
      let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
        fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
      let W : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, X_ind i H
      let Ws_at : Fin n → SimpleGraph (Fin n) → ℝ :=
        fun i H ↦ (∑ j : {j : Fin n // j ≠ i}, X_ind j.1 (H.deleteIncidenceSet i)) + 1
      let WQ : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ W ω.1
      let Ws_rand : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ Ws_at ω.2 ω.1
      ProbabilityTheory.variance
          (Q[fun ω ↦ Ws_rand ω - WQ ω |
            MeasurableSpace.comap Prod.fst inferInstance]) Q =
        (1 / (n : ℝ) ^ 2) *
          ProbabilityTheory.variance (fun H ↦ ∑ i : Fin n, (Ws_at i H - W H)) P) ∧
    (∀ {c : ℝ}, 0 < c →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (hn : 0 < n),
          let v0 : Fin n := ⟨0, hn⟩
          let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n (c / (n : ℝ))
          let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
            fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
          let W : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, X_ind i H
          let Ws_fix : SimpleGraph (Fin n) → ℝ :=
            fun H ↦ (∑ j : {j : Fin n // j ≠ v0}, X_ind j.1 (H.deleteIncidenceSet v0)) + 1
          let μ : ℝ := ∫ H, W H ∂P
          let σ2 : ℝ := ProbabilityTheory.variance W P
          δ ≤ (μ / σ2) * Real.sqrt (ProbabilityTheory.variance (fun H ↦ Ws_fix H - W H) P)) := by
  constructor
  · intro n hn p hp0 hp1
    let v0 : Fin n := ⟨0, hn⟩
    let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
    let unif_pmf : PMF (Fin n) := @PMF.uniformOfFintype (Fin n) inferInstance ⟨v0⟩
    let μI : Measure (Fin n) := unif_pmf.toMeasure
    let Q : Measure (SimpleGraph (Fin n) × Fin n) := P.prod μI
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let W : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, X_ind i H
    let Ws_at : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ (∑ j : {j : Fin n // j ≠ i}, X_ind j.1 (H.deleteIncidenceSet i)) + 1
    let WQ : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ W ω.1
    let Ws_rand : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ Ws_at ω.2 ω.1
    dsimp only
    let S_fn : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, (Ws_at i H - W H)
    let avg_fn : SimpleGraph (Fin n) → ℝ := fun H ↦ (n : ℝ)⁻¹ * S_fn H
    let Δ : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ Ws_rand ω - WQ ω
    have h_avg : ∀ H : SimpleGraph (Fin n), ∫ i, Δ (H, i) ∂μI = avg_fn H := by
      intro H
      change ∫ i, Δ (H, i) ∂unif_pmf.toMeasure = avg_fn H
      rw [PMF.integral_eq_sum]
      have hunif : ∀ i : Fin n, (unif_pmf i).toReal = (n : ℝ)⁻¹ := fun i ↦ by
        simp [unif_pmf, PMF.uniformOfFintype_apply, ENNReal.toReal_inv]
      simp_rw [hunif, smul_eq_mul, ← Finset.mul_sum]
      rfl
    have hcond_ae : Q[Δ | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[Q]
        avg_fn ∘ Prod.fst := by
      refine (condExp_fst_prod_finite_er P μI Δ).symm.trans (Eventually.of_forall fun ω ↦ h_avg ω.1)
    have hmap_fst : Q.map Prod.fst = P := by
      simp [Q, Measure.map_fst_prod]
    have hvar_map : ProbabilityTheory.variance (avg_fn ∘ Prod.fst) Q =
        ProbabilityTheory.variance avg_fn P := by
      have h := ProbabilityTheory.variance_map (μ := Q) (Y := Prod.fst) (X := avg_fn)
        (hmap_fst ▸ (measurable_of_finite avg_fn).aemeasurable) measurable_fst.aemeasurable
      rw [hmap_fst] at h
      exact h.symm
    rw [ProbabilityTheory.variance_congr hcond_ae, hvar_map]
    change ProbabilityTheory.variance (fun H ↦ (n : ℝ)⁻¹ * S_fn H) P = _
    rw [ProbabilityTheory.variance_const_mul, inv_pow, one_div]
  · intro c hc
    have hexp1_pos : 0 < Real.exp (-2 * c) := Real.exp_pos _
    have hexp2_lt : Real.exp (-c / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hmin_exp_pos : 0 < min (Real.exp (-2 * c)) (1 - Real.exp (-c / 2)) :=
      lt_min hexp1_pos (by linarith)
    let v_lb : ℝ := (1 / 4 : ℝ) * min (Real.exp (-2 * c)) (1 - Real.exp (-c / 2))
    have hv_lb_pos : 0 < v_lb := mul_pos (by norm_num) hmin_exp_pos
    have hmax_pos : 0 < max (1 : ℝ) c := lt_max_of_lt_left zero_lt_one
    let δ : ℝ := (1 / max 1 c) * Real.sqrt v_lb
    refine ⟨δ, mul_pos (one_div_pos.mpr hmax_pos) (Real.sqrt_pos.mpr hv_lb_pos), ?_⟩
    rw [Filter.eventually_atTop]
    refine ⟨Nat.ceil (2 * c) + 2, fun n hn_ge hn ↦ ?_⟩
    let v0 : Fin n := ⟨0, hn⟩
    let p : ℝ := c / (n : ℝ)
    let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let W : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, X_ind i H
    let Ws_fix : SimpleGraph (Fin n) → ℝ :=
      fun H ↦ (∑ j : {j : Fin n // j ≠ v0}, X_ind j.1 (H.deleteIncidenceSet v0)) + 1
    let μ : ℝ := ∫ H, W H ∂P
    let σ2 : ℝ := ProbabilityTheory.variance W P
    dsimp only
    have hn2 : 2 ≤ n := by omega
    have hn_pos_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    have h2c_le_n : 2 * c ≤ (n : ℝ) := by
      have hceil : 2 * c ≤ (Nat.ceil (2 * c) : ℝ) := Nat.le_ceil (2 * c)
      have hcast : (Nat.ceil (2 * c) + 2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      linarith
    have hp0 : 0 ≤ p := div_nonneg hc.le hn_pos_r.le
    have hp_half : p ≤ 1 / 2 := by
      dsimp [p]
      rw [div_le_iff₀ hn_pos_r]
      linarith
    have hp1 : p ≤ 1 := hp_half.trans (by norm_num)
    -- Bound `q_n := (1 - p)^(n - 1)` from below and above
    have hq_lb : Real.exp (-2 * c) ≤ (1 - p) ^ (n - 1) := by
      have hbase : Real.exp (-2 * p) ≤ 1 - p := exp_neg_two_mul_le_one_sub hp0 hp_half
      have hpow : (Real.exp (-2 * p)) ^ (n - 1) ≤ (1 - p) ^ (n - 1) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hbase (n - 1)
      rw [← Real.exp_nat_mul] at hpow
      have hexp_mono : Real.exp (-2 * c) ≤ Real.exp ((n - 1 : ℕ) * (-2 * p)) := by
        refine Real.exp_le_exp.mpr ?_
        have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
        have hmul_le : ((n - 1 : ℕ) : ℝ) * (2 * p) ≤ (n : ℝ) * (2 * p) :=
          mul_le_mul_of_nonneg_right hn1_le (by positivity)
        have hnp : (n : ℝ) * (2 * p) = 2 * c := by
          dsimp [p]; field_simp [hn_pos_r.ne']
        linarith
      exact hexp_mono.trans hpow
    have hq_ub : (1 - p) ^ (n - 1) ≤ Real.exp (-c / 2) := by
      have h1 : 1 - p ≤ Real.exp (-p) := by
        simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-p)
      have hpow : (1 - p) ^ (n - 1) ≤ (Real.exp (-p)) ^ (n - 1) :=
        pow_le_pow_left₀ (by linarith) h1 (n - 1)
      rw [← Real.exp_nat_mul] at hpow
      refine hpow.trans (Real.exp_le_exp.mpr ?_)
      have hn1_ge : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith
      have hmul_ge : ((n : ℝ) / 2) * p ≤ ((n - 1 : ℕ) : ℝ) * p :=
        mul_le_mul_of_nonneg_right hn1_ge hp0
      have hnp : ((n : ℝ) / 2) * p = c / 2 := by
        dsimp [p]; field_simp [hn_pos_r.ne']
      linarith
    -- Bound `μ / σ2 ≥ 1 / max 1 c`
    have hμ_eq : μ = (n : ℝ) * (1 - p) ^ (n - 1) := isolatedCount_integral hp0 hp1
    have hσ2_eq : σ2 = μ * (1 + ((n : ℝ) * p - 1) * (1 - p) ^ (n - 2)) := by
      rw [show σ2 = ProbabilityTheory.variance W (erdosRenyi n p) from rfl,
        isolatedCount_variance hp0 hp1 hn2, ← hμ_eq]
    have hμ_pos : 0 < μ := by
      rw [hμ_eq]
      exact mul_pos hn_pos_r (hexp1_pos.trans_le hq_lb)
    have hnp_eq : (n : ℝ) * p = c := by dsimp [p]; field_simp [hn_pos_r.ne']
    set u : ℝ := (1 - p) ^ (n - 2)
    have hu0 : 0 ≤ u := pow_nonneg (by linarith) _
    have hu1 : u ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hconv_pos : 0 < 1 + (c - 1) * u := by
      have hm1 : min 1 c ≤ 1 := min_le_left 1 c
      have hmc : min 1 c ≤ c := min_le_right 1 c
      have hmin_pos : 0 < min 1 c := lt_min zero_lt_one hc
      have hle : min 1 c ≤ (1 - u) * 1 + u * c := by nlinarith
      linarith
    have hconv_ub : 1 + (c - 1) * u ≤ max 1 c := by
      have hM1 : (1 : ℝ) ≤ max 1 c := le_max_left 1 c
      have hMc : c ≤ max 1 c := le_max_right 1 c
      nlinarith
    have hσ2_pos : 0 < σ2 := by
      rw [hσ2_eq, hnp_eq]
      exact mul_pos hμ_pos hconv_pos
    have hσ2_ub : σ2 ≤ μ * max 1 c := by
      rw [hσ2_eq, hnp_eq]
      exact mul_le_mul_of_nonneg_left hconv_ub hμ_pos.le
    have hratio_lb : 1 / max 1 c ≤ μ / σ2 := by
      rw [div_le_div_iff₀ hmax_pos hσ2_pos, one_mul]
      linarith
    -- Bound `Var(Ws_fix - W) ≥ v_lb`
    let E₀ : Set (SimpleGraph (Fin n)) := {H | H.IsIsolated v0}
    have hZ_zero : ∀ H ∈ E₀, Ws_fix H - W H = 0 := by
      intro H hH
      have hdel : H.deleteIncidenceSet v0 = H := deleteIncidenceSet_eq_self_of_isIsolated hH
      have hv0_one : X_ind v0 H = 1 := Set.indicator_of_mem hH 1
      have hW_split : W H = (∑ j : {j : Fin n // j ≠ v0}, X_ind j.1 H) + X_ind v0 H := by
        dsimp [W]
        rw [← Finset.sum_erase_add Finset.univ (fun i ↦ X_ind i H) (Finset.mem_univ v0)]
        congr 1
        exact Finset.sum_subtype (Finset.univ.erase v0) (p := fun j ↦ j ≠ v0)
          (by simp) (fun i ↦ X_ind i H)
      dsimp [Ws_fix]
      rw [hdel, hW_split, hv0_one, sub_self]
    have hZ_one : ∀ H ∉ E₀, 1 ≤ Ws_fix H - W H := by
      intro H hH
      have hv0_zero : X_ind v0 H = 0 := Set.indicator_of_notMem hH 1
      have hW_split : W H = ∑ j : {j : Fin n // j ≠ v0}, X_ind j.1 H := by
        dsimp [W]
        rw [← Finset.sum_erase_add Finset.univ (fun i ↦ X_ind i H) (Finset.mem_univ v0),
          hv0_zero, add_zero]
        exact Finset.sum_subtype (Finset.univ.erase v0) (p := fun j ↦ j ≠ v0)
          (by simp) (fun i ↦ X_ind i H)
      have hmono : ∑ j : {j : Fin n // j ≠ v0}, X_ind j.1 H ≤
          ∑ j : {j : Fin n // j ≠ v0}, X_ind j.1 (H.deleteIncidenceSet v0) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        by_cases hj : H.IsIsolated j.1
        · have hj' : (H.deleteIncidenceSet v0).IsIsolated j.1 :=
            isIsolated_deleteIncidenceSet_of_isIsolated v0 j.1 hj
          have hm1 : H ∈ {K : SimpleGraph (Fin n) | K.IsIsolated j.1} := hj
          have hm2 : H.deleteIncidenceSet v0 ∈ {K : SimpleGraph (Fin n) | K.IsIsolated j.1} := hj'
          simp [X_ind, hm1, hm2]
        · have hm1 : H ∉ {K : SimpleGraph (Fin n) | K.IsIsolated j.1} := hj
          rw [show X_ind j.1 H = 0 from Set.indicator_of_notMem hm1 1]
          by_cases hj' : (H.deleteIncidenceSet v0).IsIsolated j.1
          · have hm2 : H.deleteIncidenceSet v0 ∈ {K : SimpleGraph (Fin n) | K.IsIsolated j.1} := hj'
            simp [X_ind, hm2]
          · have hm2 : H.deleteIncidenceSet v0 ∉ {K : SimpleGraph (Fin n) | K.IsIsolated j.1} := hj'
            simp [X_ind, hm2]
      dsimp [Ws_fix]
      rw [hW_split]
      linarith
    have hvar_Z : v_lb ≤ ProbabilityTheory.variance (fun H ↦ Ws_fix H - W H) P := by
      have hstep := quarter_min_prob_le_variance_of_zero_one_sep P hZ_zero hZ_one
      have hprob_E₀ : P.real E₀ = (1 - p) ^ (n - 1) := erdosRenyi_real_isIsolated hp0 hp1 v0
      rw [hprob_E₀] at hstep
      have hmin_le : min (Real.exp (-2 * c)) (1 - Real.exp (-c / 2)) ≤
          min ((1 - p) ^ (n - 1)) (1 - (1 - p) ^ (n - 1)) :=
        min_le_min hq_lb (by linarith)
      exact (mul_le_mul_of_nonneg_left hmin_le (by norm_num)).trans hstep
    exact mul_le_mul hratio_lb (Real.sqrt_le_sqrt hvar_Z) (Real.sqrt_nonneg _)
      (div_nonneg hμ_pos.le hσ2_pos.le)

end SteinMethod
