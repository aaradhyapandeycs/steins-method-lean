/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Core.IsolatedVerticesCoupling

/-!
# Isolated Vertices in Erdős–Rényi Graphs (`Formalization.PoissonSizeBias.Core.IsolatedVertices`)

Proves Proposition 4.13 (`isolatedVertices_tvDist_poisson`, `SteinIntro.tex:2208-2214`) and the
Example 4.5 asymptotic rate (`isolatedVertices_asymptotics`, `SteinIntro.tex:2215-2217`), and
re-exports `Formalization.PoissonSizeBias.Core.IsolatedVerticesCoupling`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Proposition 4.13 (`SteinIntro.tex:2208-2214`) -/

private lemma ncard_isIsolated_eq_sum_indicator {n : ℕ} (H : SimpleGraph (Fin n)) :
    ({i : Fin n | H.IsIsolated i}.ncard : ℝ) =
      ∑ i : Fin n, {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator
        (1 : SimpleGraph (Fin n) → ℝ) H := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  have hfin : {i : Fin n | H.IsIsolated i}.toFinset =
      Finset.univ.filter (fun i ↦ H.IsIsolated i) := by
    ext i
    simp
  rw [hfin, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : H.IsIsolated i <;> simp [h]

private lemma poissonLaw_zero_eq_dirac : poissonLaw 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun k ↦ ?_
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top (poissonLaw 0) {k})
    (measure_ne_top (Measure.dirac 0) {k})).mp ?_
  rw [show poissonLaw 0 = ProbabilityTheory.poissonMeasure 0 from rfl,
    ProbabilityTheory.poissonMeasure_real_singleton]
  cases k with
  | zero => simp
  | succ m => simp

/-- **Proposition 4.13** (`SteinIntro.tex:2208-2214`): total-variation Poisson approximation bounds
for the isolated-vertex count `W` in $G(n, p)$. -/
theorem isolatedVertices_tvDist_poisson
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {p : ℝ} {r : ℝ≥0}
    {G : Ω → SimpleGraph (Fin n)} {Z : Ω' → ℕ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hG_meas : AEMeasurable G P) (hG_law : P.map G = erdosRenyi n p) :
    let W : Ω → ℕ := fun ω ↦ {i : Fin n | (G ω).IsIsolated i}.ncard
    ((r : ℝ) = ∫ ω, (W ω : ℝ) ∂P) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) * (((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) + (1 - p) ^ (n - 1))) ∧
    (p < 1 →
      min 1 (r : ℝ) * (((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) + (1 - p) ^ (n - 1)) ≤
        min (r : ℝ) ((r : ℝ) ^ 2) * (p / (1 - p) + 1 / (n : ℝ))) := by
  intro W hr_eq hZ_meas hZ_law
  let W_gr : SimpleGraph (Fin n) → ℕ := fun H ↦ {i : Fin n | H.IsIsolated i}.ncard
  have hW_gr_meas : Measurable W_gr := measurable_of_finite _
  have hmap_W : P.map W = (erdosRenyi n p).map W_gr := by
    have hcomp : W = W_gr ∘ G := rfl
    rw [hcomp, ← map_map_of_measurable_aemeasurable hW_gr_meas hG_meas, hG_law]
  have hr_formula : (r : ℝ) = (n : ℝ) * (1 - p) ^ (n - 1) := by
    rw [hr_eq]
    have hmap := integral_map hG_meas
      (measurable_of_finite fun H : SimpleGraph (Fin n) ↦ (W_gr H : ℝ)).aestronglyMeasurable
    rw [← hmap, hG_law]
    simp_rw [W_gr, ncard_isIsolated_eq_sum_indicator]
    exact isolatedCount_integral hp0 hp1
  constructor
  · rw [hmap_W, hZ_law]
    rcases (zero_le : (0 : ℝ≥0) ≤ r).eq_or_lt with hr0 | hr_pos
    · subst hr0
      have hmean0 : ∫ H, (W_gr H : ℝ) ∂erdosRenyi n p = 0 := by
        simp_rw [W_gr, ncard_isIsolated_eq_sum_indicator]
        rw [isolatedCount_integral hp0 hp1, ← hr_formula]
        simp
      have hW_ae0 : (fun H ↦ (W_gr H : ℝ)) =ᵐ[erdosRenyi n p] (fun _ ↦ (0 : ℝ)) :=
        (integral_eq_zero_iff_of_nonneg_ae
          (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _) Integrable.of_finite).mp hmean0
      have hmap_dirac : (erdosRenyi n p).map W_gr = Measure.dirac 0 := by
        refine Measure.ext_of_singleton fun k ↦ ?_
        rw [Measure.map_apply hW_gr_meas (measurableSet_singleton k)]
        rcases k with _ | m
        · have hae : (W_gr ⁻¹' {0} : Set (SimpleGraph (Fin n))) =ᵐ[erdosRenyi n p] Set.univ :=
            ae_eq_univ.mpr (by
              filter_upwards [hW_ae0] with H hH
              exact Nat.cast_eq_zero.mp hH)
          rw [measure_congr hae, measure_univ]
          simp
        · have hae : ∀ᵐ H ∂erdosRenyi n p, H ∉ W_gr ⁻¹' {m + 1} := by
            filter_upwards [hW_ae0] with H hH hmem
            have hk : W_gr H = 0 := Nat.cast_eq_zero.mp hH
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at hmem
            omega
          rw [measure_mono_null (fun _ h ↦ not_not.mpr h) (ae_iff.mp hae)]
          simp
      rw [hmap_dirac, poissonLaw_zero_eq_dirac, tvDist, ipm_self]
      exact zero_le
    · obtain ⟨_, hSB, _, _, h1, h2, h3⟩ :=
        isolatedVertices_coupling (erdosRenyi n p) hn hp0 hp1 measurable_id (Measure.map_id)
      let Ws_gr : SimpleGraph (Fin n) → ℝ := fun H ↦
        (∑ j : {j : Fin n // j ≠ ⟨0, hn⟩},
          {K : SimpleGraph (Fin n) | K.IsIsolated j.1}.indicator 1
            (H.deleteIncidenceSet ⟨0, hn⟩)) + 1
      have hSB' : IsSizeBias (erdosRenyi n p) (fun H ↦ (W_gr H : ℝ)) (erdosRenyi n p) Ws_gr := by
        simpa only [W_gr, Ws_gr, id_eq, ncard_isIsolated_eq_sum_indicator] using hSB
      have hmean_gr : ∫ H, (W_gr H : ℝ) ∂erdosRenyi n p = (r : ℝ) := by
        simp_rw [W_gr, ncard_isIsolated_eq_sum_indicator]
        rw [isolatedCount_integral hp0 hp1, ← hr_formula]
      have htv := tvDist_poissonLaw_le_of_isSizeBias_integrable (erdosRenyi n p) hr_pos
        hW_gr_meas.aemeasurable hmean_gr hSB' Integrable.of_finite
      have hinc0 : ∫ H, |(W_gr H : ℝ) + 1 - Ws_gr H| ∂erdosRenyi n p =
          (1 - p) ^ (n - 1) + ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) := by
        simpa only [W_gr, Ws_gr, id_eq, ncard_isIsolated_eq_sum_indicator] using
          h1.trans (h2.trans h3)
      have hinc : ∫ H, |(W_gr H : ℝ) + 1 - Ws_gr H| ∂erdosRenyi n p =
          ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) + (1 - p) ^ (n - 1) := by
        linarith [hinc0]
      rwa [hinc] at htv
  · intro hp_lt
    have h1mp_pos : 0 < 1 - p := sub_pos.mpr hp_lt
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hstep : ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) + (1 - p) ^ (n - 1) ≤
        (r : ℝ) * (p / (1 - p) + 1 / (n : ℝ)) := by
      rcases (Nat.succ_le_of_lt hn).eq_or_lt with hn1 | hn2
      · have hn_eq : n = 1 := hn1.symm
        subst hn_eq
        rw [hr_formula]
        simp only [Nat.cast_one, sub_self, zero_mul, Nat.sub_self, pow_zero, zero_add,
          one_mul, div_one]
        have hdiv_nn : 0 ≤ p / (1 - p) := div_nonneg hp0 h1mp_pos.le
        linarith
      · have hn_ge2 : 2 ≤ n := hn2
        have hpow_split : (1 - p) ^ (n - 1) = (1 - p) ^ (n - 2) * (1 - p) := by
          rw [← pow_succ, show n - 2 + 1 = n - 1 by omega]
        have hterm1 : ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) ≤
            (r : ℝ) * (p / (1 - p)) := by
          rw [hr_formula, hpow_split]
          have hsub_le : (n : ℝ) - 1 ≤ n := by linarith
          have hnn : 0 ≤ p * (1 - p) ^ (n - 2) :=
            mul_nonneg hp0 (pow_nonneg h1mp_pos.le _)
          calc ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2)
              = ((n : ℝ) - 1) * (p * (1 - p) ^ (n - 2)) := by ring
            _ ≤ (n : ℝ) * (p * (1 - p) ^ (n - 2)) :=
                mul_le_mul_of_nonneg_right hsub_le hnn
            _ = (n : ℝ) * ((1 - p) ^ (n - 2) * (1 - p)) * (p / (1 - p)) := by
                field_simp [h1mp_pos.ne']
        have hterm2 : (1 - p) ^ (n - 1) = (r : ℝ) * (1 / (n : ℝ)) := by
          rw [hr_formula]
          field_simp [hn_pos.ne']
        linarith
    have hmin_nn : 0 ≤ min 1 (r : ℝ) := le_min zero_le_one (NNReal.coe_nonneg r)
    have hmul := mul_le_mul_of_nonneg_left hstep hmin_nn
    have hmin_r : min 1 (r : ℝ) * (r : ℝ) = min (r : ℝ) ((r : ℝ) ^ 2) := by
      rw [min_mul_of_nonneg _ _ (NNReal.coe_nonneg r), one_mul, sq]
    rwa [← mul_assoc, hmin_r] at hmul

/-! ### Example 4.5 Asymptotics (`SteinIntro.tex:2215-2217`) -/

private lemma tendsto_log_div_natCast_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  have hsqrt_inv : Tendsto (fun n : ℕ ↦ 2 * ((Real.sqrt (n : ℝ))⁻¹)) atTop (nhds 0) := by
    simpa using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        |>.const_mul 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt_inv ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hlog_le : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
      have h1 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
        conv_lhs => rw [← Real.sq_sqrt hn_pos.le]
        rw [Real.log_pow, Nat.cast_ofNat]
      have hle := Real.log_le_sub_one_of_pos hsq_pos
      linarith
    calc Real.log (n : ℝ) / (n : ℝ)
        ≤ (2 * Real.sqrt (n : ℝ)) / (n : ℝ) :=
          div_le_div_of_nonneg_right hlog_le hn_pos.le
      _ = 2 * (Real.sqrt (n : ℝ))⁻¹ := by
          have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
            Real.mul_self_sqrt hn_pos.le
          field_simp [hn_pos.ne', hsq_pos.ne']
          nlinarith [hsq]

private lemma tendsto_inv_log_natCast_atTop :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma tendsto_natCast_div_sub_one_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) - 1)) atTop (nhds 1) := by
  have h : Tendsto (fun n : ℕ ↦ 1 + 1 / ((n : ℝ) - 1)) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop))
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [hn1]
  ring

/-- **Example 4.5 asymptotics** (`SteinIntro.tex:2215-2217`): if $\lambda_n = n(1 - p_n)^{n - 1}$
stays in $[c_1, c_2] \subset (0, \infty)$ eventually, then $p_n / (\log n / n) \to 1$, so both
$p_n$ and the Proposition 4.13 upper bound are of exact order $\log(n) / n$. -/
theorem isolatedVertices_asymptotics
    {p : ℕ → ℝ} {c₁ c₂ : ℝ}
    (hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1)
    (hc₁ : 0 < c₁)
    (hlam : ∀ᶠ n : ℕ in Filter.atTop,
      c₁ ≤ (n : ℝ) * (1 - p n) ^ (n - 1) ∧ (n : ℝ) * (1 - p n) ^ (n - 1) ≤ c₂) :
    let lam : ℕ → ℝ := fun n ↦ (n : ℝ) * (1 - p n) ^ (n - 1)
    let err : ℕ → ℝ := fun n ↦ min (lam n) (lam n ^ 2) * (p n / (1 - p n) + 1 / (n : ℝ))
    Filter.Tendsto (fun n : ℕ ↦ p n / (Real.log (n : ℝ) / (n : ℝ))) Filter.atTop (nhds 1) ∧
      (∃ A₁ A₂ : ℝ, 0 < A₁ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        A₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ p n ∧ p n ≤ A₂ * (Real.log (n : ℝ) / (n : ℝ))) ∧
      (∃ B₁ B₂ : ℝ, 0 < B₁ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        B₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n ∧ err n ≤ B₂ * (Real.log (n : ℝ) / (n : ℝ))) := by
  intro lam err
  have hc₂_pos : 0 < c₂ := by
    rcases hlam.exists with ⟨n, hn⟩
    linarith
  have hp_lt_one : ∀ᶠ n : ℕ in atTop, p n < 1 := by
    filter_upwards [hlam, eventually_ge_atTop 2] with n hn hn2
    by_contra hge
    have hp1 : p n = 1 := le_antisymm (hp n).2 (le_of_not_gt hge)
    have h0 : (n : ℝ) * (1 - p n) ^ (n - 1) = 0 := by
      rw [hp1, sub_self, zero_pow (by omega), mul_zero]
    linarith [hn.1]
  have hp_upper : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) - 1) * p n ≤ Real.log (n : ℝ) - Real.log c₁ := by
    filter_upwards [hlam, eventually_ge_atTop 2] with n hn hn2
    have hn_pos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have hexp_le : 1 - p n ≤ Real.exp (-p n) := by
      linarith [Real.add_one_le_exp (-p n)]
    have hpow_le : (1 - p n) ^ (n - 1) ≤ Real.exp (-(((n : ℝ) - 1) * p n)) := by
      calc (1 - p n) ^ (n - 1)
          ≤ (Real.exp (-p n)) ^ (n - 1) :=
            pow_le_pow_left₀ (sub_nonneg.mpr (hp n).2) hexp_le (n - 1)
        _ = Real.exp (-(((n : ℝ) - 1) * p n)) := by
            rw [← Real.exp_nat_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
            ring_nf
    have hmul : c₁ ≤ (n : ℝ) * Real.exp (-(((n : ℝ) - 1) * p n)) :=
      hn.1.trans (mul_le_mul_of_nonneg_left hpow_le hn_pos.le)
    have hexp_div : Real.exp (((n : ℝ) - 1) * p n) ≤ (n : ℝ) / c₁ := by
      rw [Real.exp_neg] at hmul
      have hexp_pos : 0 < Real.exp (((n : ℝ) - 1) * p n) := Real.exp_pos _
      rw [le_div_iff₀ hc₁]
      have hmul' := mul_le_mul_of_nonneg_right hmul hexp_pos.le
      rw [mul_assoc, inv_mul_cancel₀ hexp_pos.ne', mul_one, mul_comm] at hmul'
      exact hmul'
    have hlog := Real.log_le_log (Real.exp_pos _) hexp_div
    rwa [Real.log_exp, Real.log_div hn_pos.ne' hc₁.ne'] at hlog
  have hp_lower : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ) - Real.log c₂) * (1 - p n) ≤ ((n : ℝ) - 1) * p n := by
    filter_upwards [hlam, hp_lt_one, eventually_ge_atTop 2] with n hn hp_lt hn2
    have hn_pos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have h1mp_pos : 0 < 1 - p n := sub_pos.mpr hp_lt
    have hexp_ge : Real.exp (-(p n / (1 - p n))) ≤ 1 - p n := by
      have h1 : (1 - p n)⁻¹ ≤ Real.exp (p n / (1 - p n)) := by
        have h_eq : p n / (1 - p n) + 1 = (1 - p n)⁻¹ := by
          field_simp [h1mp_pos.ne']
          ring
        linarith [Real.add_one_le_exp (p n / (1 - p n)), h_eq]
      rw [Real.exp_neg]
      simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr h1mp_pos) h1
    have hpow_ge : Real.exp (-(((n : ℝ) - 1) * (p n / (1 - p n)))) ≤ (1 - p n) ^ (n - 1) := by
      calc Real.exp (-(((n : ℝ) - 1) * (p n / (1 - p n))))
          = (Real.exp (-(p n / (1 - p n)))) ^ (n - 1) := by
            rw [← Real.exp_nat_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
            ring_nf
        _ ≤ (1 - p n) ^ (n - 1) := pow_le_pow_left₀ (Real.exp_pos _).le hexp_ge (n - 1)
    have hmul : (n : ℝ) * Real.exp (-(((n : ℝ) - 1) * (p n / (1 - p n)))) ≤ c₂ :=
      (mul_le_mul_of_nonneg_left hpow_ge hn_pos.le).trans hn.2
    have hexp_div : (n : ℝ) / c₂ ≤ Real.exp (((n : ℝ) - 1) * (p n / (1 - p n))) := by
      rw [Real.exp_neg] at hmul
      have hexp_pos : 0 < Real.exp (((n : ℝ) - 1) * (p n / (1 - p n))) := Real.exp_pos _
      rw [div_le_iff₀ hc₂_pos]
      have hmul' := mul_le_mul_of_nonneg_right hmul hexp_pos.le
      rwa [mul_assoc, inv_mul_cancel₀ hexp_pos.ne', mul_one, mul_comm] at hmul'
    have hlog := Real.log_le_log (div_pos hn_pos hc₂_pos) hexp_div
    rw [Real.log_exp, Real.log_div hn_pos.ne' hc₂_pos.ne'] at hlog
    have hmul2 := mul_le_mul_of_nonneg_right hlog h1mp_pos.le
    rwa [mul_assoc, div_mul_cancel₀ _ h1mp_pos.ne'] at hmul2
  have hp_tendsto_zero : Tendsto p atTop (nhds 0) := by
    let up : ℕ → ℝ := fun n ↦
      ((n : ℝ) / ((n : ℝ) - 1)) * (Real.log (n : ℝ) / (n : ℝ) - Real.log c₁ / (n : ℝ))
    have hup_lim : Tendsto up atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ) - Real.log c₁ / (n : ℝ))
          atTop (nhds (0 - 0)) :=
        tendsto_log_div_natCast_atTop.sub
          (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
      simpa [up] using tendsto_natCast_div_sub_one_atTop.mul h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup_lim
      (Eventually.of_forall fun n ↦ (hp n).1) ?_
    filter_upwards [hp_upper, eventually_ge_atTop 2] with n hup hn2
    have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have hn_pos : (0 : ℝ) < n := by linarith
    have hdiv := div_le_div_of_nonneg_right hup hn1_pos.le
    rw [mul_div_cancel_left₀ _ hn1_pos.ne'] at hdiv
    refine hdiv.trans_eq ?_
    dsimp [up]
    field_simp [hn1_pos.ne', hn_pos.ne']
  have hratio : Tendsto (fun n : ℕ ↦ p n / (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 1) := by
    let lo : ℕ → ℝ := fun n ↦
      ((n : ℝ) / ((n : ℝ) - 1)) * (1 - Real.log c₂ * (Real.log (n : ℝ))⁻¹) * (1 - p n)
    let hi : ℕ → ℝ := fun n ↦
      ((n : ℝ) / ((n : ℝ) - 1)) * (1 - Real.log c₁ * (Real.log (n : ℝ))⁻¹)
    have hlo_lim : Tendsto lo atTop (nhds 1) := by
      have hmid : Tendsto (fun n : ℕ ↦ 1 - Real.log c₂ * (Real.log (n : ℝ))⁻¹)
          atTop (nhds (1 - Real.log c₂ * 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_log_natCast_atTop)
      have h1mp : Tendsto (fun n : ℕ ↦ 1 - p n) atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub hp_tendsto_zero
      simpa [lo] using (tendsto_natCast_div_sub_one_atTop.mul hmid).mul h1mp
    have hhi_lim : Tendsto hi atTop (nhds 1) := by
      have hmid : Tendsto (fun n : ℕ ↦ 1 - Real.log c₁ * (Real.log (n : ℝ))⁻¹)
          atTop (nhds (1 - Real.log c₁ * 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_log_natCast_atTop)
      simpa [hi] using tendsto_natCast_div_sub_one_atTop.mul hmid
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hhi_lim ?_ ?_
    · filter_upwards [hp_lower, eventually_ge_atTop 3] with n hlow hn3
      have hn_ge3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have hn_pos : (0 : ℝ) < n := by linarith
      have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have hmul_n := mul_le_mul_of_nonneg_left hlow hn_pos.le
      have hdiv := div_le_div_of_nonneg_right hmul_n (mul_pos hn1_pos hlog_pos).le
      refine (le_of_eq ?_).trans (hdiv.trans_eq ?_)
      · dsimp [lo]
        field_simp [hn1_pos.ne', hlog_pos.ne']
      · field_simp [hn1_pos.ne', hlog_pos.ne', hn_pos.ne']
    · filter_upwards [hp_upper, eventually_ge_atTop 3] with n hup hn3
      have hn_ge3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have hn_pos : (0 : ℝ) < n := by linarith
      have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
      have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have hmul_n := mul_le_mul_of_nonneg_left hup hn_pos.le
      have hdiv := div_le_div_of_nonneg_right hmul_n (mul_pos hn1_pos hlog_pos).le
      refine (le_of_eq ?_).trans (hdiv.trans_eq ?_)
      · field_simp [hn1_pos.ne', hlog_pos.ne', hn_pos.ne']
      · dsimp [hi]
        field_simp [hn1_pos.ne', hlog_pos.ne']
  have hp_bounds : ∃ A₁ A₂ : ℝ, 0 < A₁ ∧ ∀ᶠ n : ℕ in atTop,
      A₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ p n ∧ p n ≤ A₂ * (Real.log (n : ℝ) / (n : ℝ)) := by
    refine ⟨1 / 2, 3 / 2, by norm_num, ?_⟩
    have hIoo : ∀ᶠ n : ℕ in atTop,
        p n / (Real.log (n : ℝ) / (n : ℝ)) ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) :=
      hratio.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hIoo, eventually_ge_atTop 3] with n hnI hn3
    have hn_ge3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have hscale_pos : 0 < Real.log (n : ℝ) / (n : ℝ) :=
      div_pos (Real.log_pos (by linarith)) (by linarith)
    exact ⟨(le_div_iff₀ hscale_pos).mp hnI.1.le, (div_le_iff₀ hscale_pos).mp hnI.2.le⟩
  have herr_bounds : ∃ B₁ B₂ : ℝ, 0 < B₁ ∧ ∀ᶠ n : ℕ in atTop,
      B₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n ∧ err n ≤ B₂ * (Real.log (n : ℝ) / (n : ℝ)) := by
    let m₁ : ℝ := min c₁ (c₁ ^ 2)
    let m₂ : ℝ := min c₂ (c₂ ^ 2)
    have hm₁_pos : 0 < m₁ := lt_min hc₁ (sq_pos_of_pos hc₁)
    refine ⟨m₁ * (1 / 2), m₂ * 4 + 1, by positivity, ?_⟩
    have hIoo : ∀ᶠ n : ℕ in atTop,
        p n / (Real.log (n : ℝ) / (n : ℝ)) ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) :=
      hratio.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
    have hp_small : ∀ᶠ n : ℕ in atTop, p n < 1 / 2 :=
      hp_tendsto_zero.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hlam, hIoo, hp_small, eventually_ge_atTop 4] with n hln hnI hps hn4
    have hn_ge4 : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hn_pos : (0 : ℝ) < n := by linarith
    have hlog_ge1 : 1 ≤ Real.log (n : ℝ) := by
      have hexp1 : Real.exp 1 ≤ (n : ℝ) := by
        have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
          linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
        have hquarter : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
          calc (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
            _ ≤ (Real.exp (-(1 / 2 : ℝ))) ^ 2 := pow_le_pow_left₀ (by norm_num) hhalf 2
            _ = Real.exp (-1) := by rw [← Real.exp_nat_mul]; norm_num
        rw [Real.exp_neg] at hquarter
        have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
        have hmul := mul_le_mul_of_nonneg_right hquarter hexp_pos.le
        rw [inv_mul_cancel₀ hexp_pos.ne'] at hmul
        linarith
      have := Real.log_le_log (Real.exp_pos 1) hexp1
      rwa [Real.log_exp] at this
    have hscale_pos : 0 < Real.log (n : ℝ) / (n : ℝ) :=
      div_pos (by linarith) hn_pos
    have hp_lo : (1 / 2) * (Real.log (n : ℝ) / (n : ℝ)) ≤ p n :=
      (le_div_iff₀ hscale_pos).mp hnI.1.le
    have hp_hi : p n ≤ (3 / 2) * (Real.log (n : ℝ) / (n : ℝ)) :=
      (div_le_iff₀ hscale_pos).mp hnI.2.le
    have h1mp_pos : 0 < 1 - p n := by linarith
    have hmin_lo : m₁ ≤ min (lam n) (lam n ^ 2) :=
      min_le_min hln.1 (pow_le_pow_left₀ hc₁.le hln.1 2)
    have hmin_hi : min (lam n) (lam n ^ 2) ≤ m₂ :=
      min_le_min hln.2 (pow_le_pow_left₀ (hc₁.le.trans hln.1) hln.2 2)
    have hmin_nn : 0 ≤ min (lam n) (lam n ^ 2) := hm₁_pos.le.trans hmin_lo
    constructor
    · have hfrac_lo : p n ≤ p n / (1 - p n) + 1 / (n : ℝ) := by
        have hp_le_div : p n ≤ p n / (1 - p n) := by
          rw [le_div_iff₀ h1mp_pos]
          nlinarith [(hp n).1, (hp n).2]
        have h1n_nn : 0 ≤ 1 / (n : ℝ) := by positivity
        linarith
      calc m₁ * (1 / 2) * (Real.log (n : ℝ) / (n : ℝ))
          = m₁ * ((1 / 2) * (Real.log (n : ℝ) / (n : ℝ))) := by ring
        _ ≤ m₁ * p n := mul_le_mul_of_nonneg_left hp_lo hm₁_pos.le
        _ ≤ min (lam n) (lam n ^ 2) * (p n / (1 - p n) + 1 / (n : ℝ)) :=
            mul_le_mul hmin_lo hfrac_lo (hp n).1 hmin_nn
    · have hfrac_hi : p n / (1 - p n) + 1 / (n : ℝ) ≤
          4 * (Real.log (n : ℝ) / (n : ℝ)) := by
        have hdiv_le : p n / (1 - p n) ≤ 2 * p n := by
          rw [div_le_iff₀ h1mp_pos]
          nlinarith [(hp n).1, hps]
        have h1n_le : 1 / (n : ℝ) ≤ Real.log (n : ℝ) / (n : ℝ) :=
          div_le_div_of_nonneg_right hlog_ge1 hn_pos.le
        linarith
      have hm₂_nn : 0 ≤ m₂ := hmin_nn.trans hmin_hi
      have hfrac_nn : 0 ≤ p n / (1 - p n) + 1 / (n : ℝ) :=
        add_nonneg (div_nonneg (hp n).1 h1mp_pos.le) (div_nonneg zero_le_one hn_pos.le)
      calc min (lam n) (lam n ^ 2) * (p n / (1 - p n) + 1 / (n : ℝ))
          ≤ m₂ * (4 * (Real.log (n : ℝ) / (n : ℝ))) :=
            mul_le_mul hmin_hi hfrac_hi hfrac_nn hm₂_nn
        _ ≤ (m₂ * 4 + 1) * (Real.log (n : ℝ) / (n : ℝ)) := by
            nlinarith [hscale_pos]
  exact ⟨hratio, hp_bounds, herr_bounds⟩

end SteinMethod
