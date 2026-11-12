/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.Equilibrium

/-!
# Example 5.4: Geometric Equilibrium Coupling and Wasserstein Bound
(`Formalization.Exponential.GeometricExample`)

Formalizes Example 5.4 (`\label{ex171}`, `SteinIntro.tex:2883-2901`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):
* `sizeBias_cond_uniform_pmf`: general PMF identity for $V \mid N^s \sim \mathrm{Unif}\{1, \dots,
  N^s\}$ (`SteinIntro.tex:2889-2893, 2931-2938`; shared by `Ex5_4`(i) and `Rem5_5`(i)).
* `wassersteinDist_shiftedGeomLaw_le`: standalone law-level bound
  $d_{\mathrm{W}}(\mathcal{L}(p N), \mathrm{Exp}(1)) \le p$ for $N \sim \mathrm{Ge}(p)$
  ($0 < p \le 1$), exported for Section 6 opening (`stmts-review-05E.md` item `E4`).
* `ex5_4` (**Example 5.4**): size-bias conditional uniform invariance, $N - U$ equilibrium
  coupling, and $d_{\mathrm{W}}(p N, Z) \le p$ (which also implies $p N \xrightarrow{d}
  \mathrm{Exp}(1)$ as $p \to 0^+$ at `SteinIntro.tex:2885`).
-/

open Function Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-- Countable disjoint additivity for `Measure.real` on finite measure spaces. -/
theorem measureReal_iUnion_disjoint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {A : ℕ → Set Ω}
    (hdisj : Pairwise (Disjoint on A)) (hmeas : ∀ k, MeasurableSet (A k)) :
    Summable (fun k ↦ P.real (A k)) ∧ P.real (⋃ k, A k) = ∑' k, P.real (A k) := by
  have hsum : Summable (fun k ↦ P.real (A k)) :=
    summable_of_sum_le (fun _ ↦ measureReal_nonneg) fun s ↦
      sum_measureReal_le_measureReal_univ (fun k _ ↦ hmeas k) (hdisj.set_pairwise ↑s)
  refine ⟨hsum, ?_⟩
  rw [measureReal_def, measure_iUnion hdisj hmeas]
  have hof : (fun k ↦ P (A k)) = fun k ↦ ENNReal.ofReal (P.real (A k)) :=
    funext fun k ↦ (ofReal_measureReal (measure_ne_top P (A k))).symm
  rw [hof, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ measureReal_nonneg) hsum,
    ENNReal.toReal_ofReal (tsum_nonneg fun _ ↦ measureReal_nonneg)]

/-- General PMF identity for a random variable $V$ conditionally uniform on $\{1, \dots, N^s\}$,
where $N^s$ has the size-bias distribution of a non-negative integer-valued integrable variable $N$
with $\mu = \mathbb{E}[N] > 0$:
$\mathbb{P}(V = m) = \mathbb{P}(N \ge m) / \mu$ for $m \ge 1$ and $0$ for $m = 0$
(`SteinIntro.tex:2889-2893, 2931-2938`; used in `Ex5_4`(i) and `Rem5_5`(i)). -/
theorem sizeBias_cond_uniform_pmf
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {N : Ω → ℕ} {Ns V : Ω' → ℕ}
    (hN_aem : AEMeasurable N P)
    (_hN_int : Integrable (fun ω ↦ (N ω : ℝ)) P)
    (hμ_pos : 0 < ∫ ω, (N ω : ℝ) ∂P)
    (hV_aem : AEMeasurable V P')
    (hSB : IsSizeBias P (fun ω ↦ (N ω : ℝ)) P' (fun ω' ↦ (Ns ω' : ℝ)))
    (hUnif : ∀ k m : ℕ, P'.real {ω' | Ns ω' = k ∧ V ω' = m} =
      if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Ns ω' = k} / (k : ℝ) else 0) :
    ∀ m : ℕ, P'.real {ω' | V ω' = m} =
      if 1 ≤ m then P.real {ω | m ≤ N ω} / ∫ ω, (N ω : ℝ) ∂P else 0 := by
  set μ : ℝ := ∫ ω, (N ω : ℝ) ∂P
  let NsR : Ω' → ℝ := fun ω' ↦ (Ns ω' : ℝ)
  let NsR' : Ω' → ℝ := hSB.2.2.1.mk NsR
  let V' : Ω' → ℕ := hV_aem.mk V
  let N' : Ω → ℕ := hN_aem.mk N
  have hNsR_meas : Measurable NsR' := hSB.2.2.1.measurable_mk
  have hV'_meas : Measurable V' := hV_aem.measurable_mk
  have hN'_meas : Measurable N' := hN_aem.measurable_mk
  have hae_NsR : NsR =ᵐ[P'] NsR' := hSB.2.2.1.ae_eq_mk
  have hae_V : V =ᵐ[P'] V' := hV_aem.ae_eq_mk
  have hae_N : N =ᵐ[P] N' := hN_aem.ae_eq_mk
  intro m
  let A : ℕ → Set Ω' := fun k ↦ {ω' | NsR' ω' = (k : ℝ) ∧ V' ω' = m}
  have hA_meas : ∀ k, MeasurableSet (A k) := fun k ↦
    (hNsR_meas (measurableSet_singleton (k : ℝ))).inter (hV'_meas (measurableSet_singleton m))
  have hA_disj : Pairwise (Disjoint on A) := fun k₁ k₂ hne ↦
    Set.disjoint_left.mpr fun ω' h1 h2 ↦ hne (Nat.cast_inj.mp (h1.1.symm.trans h2.1))
  have hA_congr : ∀ k, P'.real (A k) = P'.real {ω' | Ns ω' = k ∧ V ω' = m} := fun k ↦ by
    refine measureReal_congr ?_
    filter_upwards [hae_NsR, hae_V] with ω' h1 h2
    refine propext ?_
    change (NsR' ω' = (k : ℝ) ∧ V' ω' = m) ↔ (Ns ω' = k ∧ V ω' = m)
    rw [← h1, ← h2]
    simp [NsR]
  have hU_congr : P'.real {ω' | V ω' = m} = P'.real (⋃ k, A k) := by
    refine measureReal_congr ?_
    filter_upwards [hae_NsR, hae_V] with ω' h1 h2
    refine propext ?_
    rw [h2, mem_iUnion]
    exact ⟨fun hm ↦ ⟨Ns ω', h1.symm, hm⟩, fun ⟨_, _, hm⟩ ↦ hm⟩
  rw [hU_congr, (measureReal_iUnion_disjoint P' hA_disj hA_meas).2]
  simp_rw [hA_congr, hUnif]
  split_ifs with hm
  · let B : ℕ → Set Ω := fun k ↦ if m ≤ k then {ω | N' ω = k} else ∅
    have hB_meas : ∀ k, MeasurableSet (B k) := fun k ↦ by
      dsimp only [B]
      split_ifs
      · exact hN'_meas (measurableSet_singleton k)
      · exact MeasurableSet.empty
    have hB_disj : Pairwise (Disjoint on B) := fun k₁ k₂ hne ↦ by
      dsimp only [Function.onFun, B]
      split_ifs with h1 h2
      · exact Set.disjoint_left.mpr fun ω ha hb ↦ hne (ha.symm.trans hb)
      · exact disjoint_bot_right
      · exact disjoint_bot_left
      · exact disjoint_bot_left
    have hterm : ∀ k : ℕ,
        (if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Ns ω' = k} / (k : ℝ) else 0) =
          P.real (B k) / μ := fun k ↦ by
      by_cases hmk : m ≤ k
      · have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (lt_of_lt_of_le hm hmk)
        have hsb := hSB.measureReal_eq_singleton hμ_pos (k : ℝ)
        have hset1 : {ω' | (Ns ω' : ℝ) = (k : ℝ)} = {ω' | Ns ω' = k} := by ext; simp
        have hset2 : {ω | (N ω : ℝ) = (k : ℝ)} = {ω | N ω = k} := by ext; simp
        have hN_congr : P.real {ω | N ω = k} = P.real {ω | N' ω = k} :=
          measureReal_congr (hae_N.mono fun ω hω ↦ propext (by
            change (N ω = k) ↔ (N' ω = k); rw [hω]))
        rw [hset1, hset2, hN_congr] at hsb
        change P'.real {ω' | Ns ω' = k} = (k : ℝ) * P.real {ω | N' ω = k} / μ at hsb
        simp only [hm, hmk, and_self, ↓reduceIte, B, hsb]
        field_simp [hk_pos.ne', hμ_pos.ne']
      · simp [hm, hmk, B]
    simp_rw [hterm, div_eq_mul_inv, tsum_mul_right]
    have hB_union : P.real {ω | m ≤ N ω} = P.real (⋃ k, B k) := by
      refine measureReal_congr ?_
      filter_upwards [hae_N] with ω hω
      refine propext ?_
      rw [hω]
      simp only [mem_iUnion, B]
      refine ⟨fun h ↦ ⟨N' ω, by simp [h]⟩, fun ⟨k, hk⟩ ↦ ?_⟩
      by_cases hmk : m ≤ k
      · simp only [hmk, ↓reduceIte, mem_ofPred_eq] at hk
        exact hk ▸ hmk
      · simp [hmk] at hk
    rw [← (measureReal_iUnion_disjoint P hB_disj hB_meas).2, ← hB_union]
  · simp [hm]

/-- Equilibrium identity for $N - U$ when $N \sim \mathrm{Ge}(p)$ ($0 < p \le 1$) and
$U \sim \mathrm{Unif}(0, 1)$ is independent of $N$ (`SteinIntro.tex:2895-2898`). -/
theorem isEquilibrium_shiftedGeom_sub_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) {N : Ω → ℕ} {U : Ω → ℝ}
    (hN_aem : AEMeasurable N P) (hN_law : P.map N = shiftedGeomLaw p)
    (hU : MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P)
    (hIndep : IndepFun U N P) :
    IsEquilibrium P (fun ω ↦ (N ω : ℝ)) P (fun ω ↦ (N ω : ℝ) - U ω) := by
  have hNR_aem : AEMeasurable (fun ω ↦ (N ω : ℝ)) P :=
    (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hN_aem
  have hNR_int : Integrable (fun ω ↦ (N ω : ℝ)) P := by
    have h := integrable_cast_shiftedGeomLaw hp₀ hp₁
    rw [← hN_law] at h
    exact (integrable_map_measure (by fun_prop) hN_aem).mp h
  have hNR_mean : ∫ ω, (N ω : ℝ) ∂P = 1 / p := by
    have h := integral_cast_shiftedGeomLaw hp₀ hp₁
    rw [← hN_law, integral_map hN_aem (by fun_prop)] at h
    exact h
  refine ⟨Eventually.of_forall fun ω ↦ Nat.cast_nonneg (N ω), hNR_int,
    hNR_aem.sub hU.aemeasurable, fun f ⟨K, hLip⟩ ↦ ?_⟩
  have hU_map : P.map U = volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [hU.map_eq, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
      inv_one, one_smul]
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [← hU_map]
    exact (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).mpr ‹_›
  have hprod_map : P.map (fun ω ↦ (U ω, N ω)) =
      (volume.restrict (Ioo (0 : ℝ) 1)).prod (shiftedGeomLaw p) := by
    rw [hIndep.map_prod_eq_prod_map_map hU.aemeasurable hN_aem, hU_map, hN_law]
  let ψ : ℝ × ℕ → ℝ := fun q ↦ deriv f ((q.2 : ℝ) - q.1)
  have hψ_meas : Measurable ψ :=
    (measurable_deriv f).comp (by fun_prop : Measurable fun q : ℝ × ℕ ↦ (q.2 : ℝ) - q.1)
  have hdf_bdd : ∀ y : ℝ, |deriv f y| ≤ K := fun y ↦ by
    simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := y) hLip
  have hψ_int : Integrable ψ ((volume.restrict (Ioo (0 : ℝ) 1)).prod (shiftedGeomLaw p)) :=
    Integrable.of_bound hψ_meas.aestronglyMeasurable K
      (Eventually.of_forall fun q ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd _)
  have h_int_eq : ∫ ω, deriv f ((N ω : ℝ) - U ω) ∂P =
      ∫ k : ℕ, (∫ u in Ioo (0 : ℝ) 1, deriv f ((k : ℝ) - u)) ∂shiftedGeomLaw p := by
    have h1 : (fun ω ↦ deriv f ((N ω : ℝ) - U ω)) = fun ω ↦ ψ (U ω, N ω) := rfl
    rw [h1, ← integral_map (hU.aemeasurable.prodMk hN_aem) hψ_meas.aestronglyMeasurable,
      hprod_map, integral_prod_symm ψ hψ_int]
  have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
    fun a b ↦ hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have h_slice : ∀ k : ℕ,
      ∫ u in Ioo (0 : ℝ) 1, deriv f ((k : ℝ) - u) = f (k : ℝ) - f ((k : ℝ) - 1) := fun k ↦ by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    have hsub : (fun u : ℝ ↦ deriv f ((k : ℝ) - u)) = fun u ↦ deriv f ((k : ℝ) - 1 * u) := by
      ext u; ring_nf
    rw [hsub, intervalIntegral.integral_comp_sub_mul (deriv f) one_ne_zero (k : ℝ)]
    simp [(hf_ac ((k : ℝ) - 1) (k : ℝ)).integral_deriv_eq_sub]
  simp_rw [h_slice] at h_int_eq
  have hq_coe : (Set.projIcc 0 1 zero_le_one p : ℝ) = p :=
    congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hp₀.le, hp₁⟩)
  have hq_ne : Set.projIcc 0 1 zero_le_one p ≠ 0 := fun h0 ↦ by
    have h0' : (Set.projIcc 0 1 zero_le_one p : ℝ) = 0 := congrArg Subtype.val h0
    linarith
  have hr_norm : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp₁)]; linarith
  have hsum_fn : Summable (fun n : ℕ ↦ (1 - p) ^ n * f (n : ℝ)) := by
    have h0 := (summable_norm_pow_mul_geometric_of_norm_lt_one 0 hr_norm).mul_left |f 0|
    have h1 := (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr_norm).mul_left (K : ℝ)
    refine (h0.add h1).of_norm_bounded fun n ↦ ?_
    have hr_nn : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
    have hd := hLip.dist_le_mul (n : ℝ) 0
    rw [Real.dist_eq, Real.dist_eq, sub_zero, Nat.abs_cast] at hd
    have hfn : |f (n : ℝ)| ≤ |f 0| + (K : ℝ) * (n : ℝ) := by
      linarith [abs_sub_abs_le_abs_sub (f (n : ℝ)) (f 0)]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr_nn, Nat.abs_cast,
      pow_zero, pow_one, one_mul]
    calc
      (1 - p) ^ n * |f (n : ℝ)|
          ≤ (1 - p) ^ n * (|f 0| + (K : ℝ) * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hfn (pow_nonneg hr_nn n)
      _ = |f 0| * (1 - p) ^ n + (K : ℝ) * ((n : ℝ) * (1 - p) ^ n) := by ring
  have hsum_fn1 : Summable (fun n : ℕ ↦ (1 - p) ^ n * f ((n + 1 : ℕ) : ℝ)) := by
    by_cases hp1 : p = 1
    · subst hp1
      refine summable_of_ne_finset_zero (s := {0}) fun n hn ↦ ?_
      rw [Finset.mem_singleton] at hn
      simp [zero_pow hn]
    · have h1mp_pos : 0 < 1 - p := sub_pos.mpr (lt_of_le_of_ne hp₁ hp1)
      have hshift := ((summable_nat_add_iff 1).mpr hsum_fn).mul_left (1 - p)⁻¹
      refine hshift.congr fun n ↦ ?_
      rw [pow_succ']
      field_simp [h1mp_pos.ne']
  have h_geom_eval : ∫ k : ℕ, (f (k : ℝ) - f ((k : ℝ) - 1)) ∂shiftedGeomLaw p =
      p * ((∫ ω, f (N ω : ℝ) ∂P) - f 0) := by
    rw [shiftedGeomLaw, integral_map (by fun_prop) Measurable.of_discrete.aestronglyMeasurable,
      integral_geometricMeasure hq_ne, hq_coe]
    have hterm :
        (fun n : ℕ ↦ ((1 - p) ^ n * p) •
          (f ((n + 1 : ℕ) : ℝ) - f (((n + 1 : ℕ) : ℝ) - 1))) =
        fun n : ℕ ↦ p * ((1 - p) ^ n * f ((n + 1 : ℕ) : ℝ) - (1 - p) ^ n * f (n : ℝ)) := by
      ext n
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      ring
    rw [hterm, tsum_mul_left, hsum_fn1.tsum_sub hsum_fn]
    have hsplit := (hsum_fn.sum_add_tsum_nat_add 1).symm
    rw [Finset.sum_range_one, pow_zero, Nat.cast_zero, one_mul] at hsplit
    have htail : (∑' n : ℕ, (1 - p) ^ (n + 1) * f ((n + 1 : ℕ) : ℝ)) =
        (1 - p) * ∑' n : ℕ, (1 - p) ^ n * f ((n + 1 : ℕ) : ℝ) := by
      have hc : (fun n : ℕ ↦ (1 - p) ^ (n + 1) * f ((n + 1 : ℕ) : ℝ)) =
          fun n : ℕ ↦ (1 - p) * ((1 - p) ^ n * f ((n + 1 : ℕ) : ℝ)) := by
        ext n; rw [pow_succ']; ring
      rw [hc, tsum_mul_left]
    rw [htail] at hsplit
    have hfN_eval : ∫ ω, f (N ω : ℝ) ∂P = p * ∑' n : ℕ, (1 - p) ^ n * f ((n + 1 : ℕ) : ℝ) := by
      have hmap : ∫ ω, f (N ω : ℝ) ∂P = ∫ k : ℕ, f (k : ℝ) ∂shiftedGeomLaw p := by
        rw [← hN_law]
        exact (integral_map hN_aem
          (Measurable.of_discrete (f := fun k : ℕ ↦ f (k : ℝ))).aestronglyMeasurable).symm
      rw [hmap, shiftedGeomLaw,
        integral_map (by fun_prop) Measurable.of_discrete.aestronglyMeasurable,
        integral_geometricMeasure hq_ne, hq_coe]
      have hc : (fun n : ℕ ↦ ((1 - p) ^ n * p) • f ((n + 1 : ℕ) : ℝ)) =
          fun n : ℕ ↦ p * ((1 - p) ^ n * f ((n + 1 : ℕ) : ℝ)) := by
        ext n; simp only [smul_eq_mul]; ring
      rw [hc, tsum_mul_left]
    rw [hsplit, hfN_eval]
    ring
  rw [hNR_mean, h_int_eq, h_geom_eval]
  field_simp [hp₀.ne']

/-- Standalone law-level bound from **Example 5.4** (`\label{ex171}`, `SteinIntro.tex:2894-2900`;
exported for Section 6 opening per `stmts-review-05E.md` item `E4`): for $0 < p \le 1$,
$d_{\mathrm{W}}(\mathcal{L}(p N), \mathrm{Exp}(1)) \le p$ where $N \sim \mathrm{Ge}(p)$ on
$\{1, 2, \dots\}$. -/
theorem wassersteinDist_shiftedGeomLaw_le {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    wassersteinDist ((shiftedGeomLaw p).map (fun n : ℕ ↦ p * (n : ℝ))) stdExpLaw ≤
      ENNReal.ofReal p := by
  let μU : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have hμU_prob : IsProbabilityMeasure μU := by
    rw [isProbabilityMeasure_iff, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_one]
  let P₀ : Measure (ℝ × ℕ) := μU.prod (shiftedGeomLaw p)
  let U : ℝ × ℕ → ℝ := Prod.fst
  let N : ℝ × ℕ → ℕ := Prod.snd
  have hU_map : P₀.map U = μU := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hN_map : P₀.map N = shiftedGeomLaw p := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hU_unif : MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P₀ :=
    ⟨measurable_fst.aemeasurable, by
      rw [hU_map, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
        inv_one, one_smul]⟩
  have hIndep : IndepFun U N P₀ := indepFun_prod measurable_id measurable_id
  let W : ℝ × ℕ → ℝ := fun ω ↦ p * (N ω : ℝ)
  let We : ℝ × ℕ → ℝ := fun ω ↦ W ω - p * U ω
  have hEqN := isEquilibrium_shiftedGeom_sub_uniform P₀ hp₀ hp₁ measurable_snd.aemeasurable
    hN_map hU_unif hIndep
  have hEqW : IsEquilibrium P₀ W P₀ We := by
    have hscale := hEqN.const_mul_pos hp₀
    refine hscale.congr_identDistrib (IdentDistrib.refl (by fun_prop)) ?_
    refine IdentDistrib.of_ae_eq (by fun_prop) (Eventually.of_forall fun ω ↦ ?_)
    dsimp only [We, W]
    ring
  have hW_nn : 0 ≤ᵐ[P₀] W := Eventually.of_forall fun ω ↦ by positivity
  have hW2 : MemLp W 2 P₀ := by
    have hN2 : MemLp (fun ω : ℝ × ℕ ↦ (N ω : ℝ)) 2 P₀ := by
      have hm := memLp_cast_two_shiftedGeomLaw hp₀ hp₁
      rw [← hN_map] at hm
      exact (memLp_map_measure_iff (by fun_prop) measurable_snd.aemeasurable).mp hm
    exact hN2.const_mul p
  have hW_mean : ∫ ω, W ω ∂P₀ = 1 := by
    change ∫ ω, p * (N ω : ℝ) ∂P₀ = 1
    rw [integral_const_mul, ← integral_map measurable_snd.aemeasurable (by fun_prop), hN_map,
      integral_cast_shiftedGeomLaw hp₀ hp₁]
    field_simp [hp₀.ne']
  have hZ_prob : IsProbabilityMeasure stdExpLaw := isProbabilityMeasure_stdExpLaw
  have hbnd := thm5_4 P₀ stdExpLaw hW_nn hW2 hW_mean hEqW aemeasurable_id Measure.map_id
  rw [Measure.map_id] at hbnd
  have hW_law : P₀.map W = (shiftedGeomLaw p).map (fun n : ℕ ↦ p * (n : ℝ)) := by
    rw [← hN_map, Measure.map_map (by fun_prop) measurable_snd]
    rfl
  have hdiff_eval : ∫ ω, |We ω - W ω| ∂P₀ = p / 2 := by
    have hcongr : (fun ω : ℝ × ℕ ↦ |We ω - W ω|) = fun ω ↦ p * |U ω| := by
      ext ω
      dsimp only [We]
      have : W ω - p * U ω - W ω = -(p * U ω) := by ring
      rw [this, abs_neg, abs_mul, abs_of_pos hp₀]
    rw [hcongr, integral_const_mul, ← integral_map measurable_fst.aemeasurable (by fun_prop),
      hU_map]
    have hae : EqOn (fun u : ℝ ↦ |u|) id (Ioo (0 : ℝ) 1) := fun u hu ↦ abs_of_pos hu.1
    rw [setIntegral_congr_fun measurableSet_Ioo hae, setIntegral_congr_set Ioo_ae_eq_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) (id t) t := fun t _ ↦ by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (continuous_id.intervalIntegrable 0 1)]
    ring
  rw [hW_law, hdiff_eval] at hbnd
  have hmul : (2 : ℝ) * (p / 2) = p := by ring
  rwa [hmul] at hbnd

/-- **Example 5.4** (`\label{ex171}`, `SteinIntro.tex:2883-2900`): for $0 < p \le 1$ and
$N \sim \mathrm{Ge}(p)$ on $\{1, 2, \dots\}$, (i) $V \mid N^s \sim \mathrm{Unif}\{1, \dots, N^s\}$
satisfies $V \stackrel{d}{=} N$; (ii) for $U \sim \mathrm{Unif}(0, 1)$ independent of $N$,
$N - U$ has the equilibrium distribution of $N$ and $W - p U$ has the equilibrium distribution of
$W = p N$; and (iii) $d_{\mathrm{W}}(\mathcal{L}(p N), \mathcal{L}(Z)) \le p$ for
$Z \sim \mathrm{Exp}(1)$ (whence $p N \xrightarrow{d} \mathrm{Exp}(1)$ as $p \to 0^+$ at
`SteinIntro.tex:2885`). -/
theorem ex5_4 {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {N : Ω → ℕ} {Ns V : Ω' → ℕ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      AEMeasurable V P' →
      IsSizeBias P (fun ω ↦ (N ω : ℝ)) P' (fun ω' ↦ (Ns ω' : ℝ)) →
      (∀ k m : ℕ, P'.real {ω' | Ns ω' = k ∧ V ω' = m} =
        if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Ns ω' = k} / (k : ℝ) else 0) →
      P'.map V = P.map N) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {N : Ω → ℕ} {U : Ω → ℝ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P →
      IndepFun U N P →
      let W : Ω → ℝ := fun ω ↦ p * (N ω : ℝ)
      IsEquilibrium P (fun ω ↦ (N ω : ℝ)) P (fun ω ↦ (N ω : ℝ) - U ω) ∧
        IsEquilibrium P W P (fun ω ↦ W ω - p * U ω)) ∧
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {N : Ω → ℕ} {Z : Ω' → ℝ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      AEMeasurable Z P' →
      P'.map Z = stdExpLaw →
      wassersteinDist (P.map (fun ω ↦ p * (N ω : ℝ))) (P'.map Z) ≤ ENNReal.ofReal p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω Ω' _ _ P _ P' _ N Ns V hN_aem hN_law hV_aem hSB hUnif
    have hNR_int : Integrable (fun ω ↦ (N ω : ℝ)) P := by
      have h := integrable_cast_shiftedGeomLaw hp₀ hp₁
      rw [← hN_law] at h
      exact (integrable_map_measure (by fun_prop) hN_aem).mp h
    have hNR_mean : ∫ ω, (N ω : ℝ) ∂P = 1 / p := by
      have h := integral_cast_shiftedGeomLaw hp₀ hp₁
      rw [← hN_law, integral_map hN_aem (by fun_prop)] at h
      exact h
    have hμ_pos : 0 < ∫ ω, (N ω : ℝ) ∂P := by rw [hNR_mean]; positivity
    have hpmf := sizeBias_cond_uniform_pmf P P' hN_aem hNR_int hμ_pos hV_aem hSB hUnif
    rw [hN_law]
    have : IsProbabilityMeasure (P'.map V) := (Measure.isProbabilityMeasure_map_iff hV_aem).mpr ‹_›
    ext s hs
    rw [← Measure.tsum_indicator_apply_singleton (P'.map V) s hs,
      ← Measure.tsum_indicator_apply_singleton (shiftedGeomLaw p) s hs]
    congr with m
    by_cases hms : m ∈ s
    · simp only [indicator_of_mem hms]
      rw [← ofReal_measureReal (measure_ne_top (P'.map V) {m}),
        ← ofReal_measureReal (measure_ne_top (shiftedGeomLaw p) {m})]
      congr 1
      have hV_m : (P'.map V).real {m} = P'.real {ω' | V ω' = m} := by
        rw [map_measureReal_apply_of_aemeasurable hV_aem (measurableSet_singleton m)]
        rfl
      rw [hV_m, hpmf m, hNR_mean]
      rcases m with _ | k
      · simp [measureReal_def, shiftedGeomLaw_zero]
      · have hm1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have htail : P.real {ω | k + 1 ≤ N ω} = (shiftedGeomLaw p).real (Ici (k + 1)) := by
          rw [← hN_law, map_measureReal_apply_of_aemeasurable hN_aem measurableSet_Ici]
          rfl
        simp only [hm1, ↓reduceIte]
        rw [htail, shiftedGeomLaw_real_Ici hp₀ hp₁ hm1,
          shiftedGeomLaw_real_singleton_of_pos hp₀ hp₁ hm1]
        field_simp [hp₀.ne']
    · simp [indicator_of_notMem hms]
  · intro Ω _ P _ N U hN_aem hN_law hU hIndep
    dsimp only
    have h1 := isEquilibrium_shiftedGeom_sub_uniform P hp₀ hp₁ hN_aem hN_law hU hIndep
    refine ⟨h1, ?_⟩
    have h2 := h1.const_mul_pos hp₀
    have hNaem : AEMeasurable (fun ω ↦ (N ω : ℝ)) P :=
      (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hN_aem
    refine h2.congr_identDistrib (IdentDistrib.refl (hNaem.const_mul p)) ?_
    refine IdentDistrib.of_ae_eq ((hNaem.sub hU.aemeasurable).const_mul p)
      (Eventually.of_forall fun ω ↦ ?_)
    ring
  · intro Ω Ω' _ _ P _ P' _ N Z hN_aem hN_law _hZ_aem hZ_law
    have hmap : P.map (fun ω ↦ p * (N ω : ℝ)) =
        (shiftedGeomLaw p).map (fun n : ℕ ↦ p * (n : ℝ)) := by
      change P.map ((fun n : ℕ ↦ p * (n : ℝ)) ∘ N) = _
      rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hN_aem, hN_law]
    rw [hmap, hZ_law]
    exact wassersteinDist_shiftedGeomLaw_le hp₀ hp₁

private lemma stdExpLaw_map_div_eq_expLaw {r : ℝ} (hr : 0 < r) :
    stdExpLaw.map (fun u ↦ u / r) = expLaw r := by
  have : IsProbabilityMeasure (expLaw r) := isProbabilityMeasure_expMeasure hr
  have hf : Measurable (fun u : ℝ ↦ u / r) := measurable_id.div_const r
  have : IsProbabilityMeasure (stdExpLaw.map (fun u ↦ u / r)) :=
    (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).mpr isProbabilityMeasure_stdExpLaw
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hf measurableSet_Iic]
  have hpre : (fun u : ℝ ↦ u / r) ⁻¹' Iic x = Iic (x * r) := by
    ext u
    simp [div_le_iff₀ hr]
  rw [hpre, stdExpLaw, expLaw_real_Iic zero_lt_one, expLaw_real_Iic hr]
  by_cases hx : 0 ≤ x
  · have hrx : ¬ r * x < 0 := not_lt.mpr (mul_nonneg hr.le hx)
    simp [hx, hrx, mul_comm]
  · have hxr : x * r < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hx) hr
    simp [hx, hxr]

/-- **Example 5.4, weak convergence prose claim** (`\label{ex171}`, `SteinIntro.tex:2885`; `M4`):
as $p \to 0^+$, for $N_p \sim \mathrm{Ge}(p)$ and $Z \sim \mathrm{Exp}(1)$, $p N_p$ converges to
$Z$ in Wasserstein distance, in Kolmogorov distance, and weakly ($\mathbb{E}[g(p N_p)] \to
\mathbb{E}[g(Z)]$ for every bounded continuous $g : \mathbb{R} \to \mathbb{R}$). -/
theorem ex5_4_weak_conv
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    {Ω : ℝ → Type*} [∀ p, MeasurableSpace (Ω p)] (P : ∀ p, Measure (Ω p))
    {N : ∀ p, Ω p → ℕ}
    (hZ_aem : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdExpLaw)
    (hFam : ∀ p ∈ Ioc (0 : ℝ) 1,
      IsProbabilityMeasure (P p) ∧ AEMeasurable (N p) (P p) ∧ (P p).map (N p) = shiftedGeomLaw p) :
    Tendsto
      (fun p : ℝ ↦ wassersteinDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) ∧
    Tendsto
      (fun p : ℝ ↦ kolmogorovDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) ∧
    (∀ g : ℝ → ℝ, Continuous g → (∃ M : ℝ, ∀ x : ℝ, |g x| ≤ M) →
      Tendsto
        (fun p : ℝ ↦ ∫ ω, g (p * (N p ω : ℝ)) ∂(P p))
        (nhdsWithin 0 (Ioi 0))
        (𝓝 (∫ z, g (Z z) ∂P'))) := by
  have hmem_Ioc : Ioc (0 : ℝ) 1 ∈ nhdsWithin 0 (Ioi 0) := Ioc_mem_nhdsGT zero_lt_one
  have hmem_Ioo : Ioo (0 : ℝ) 1 ∈ nhdsWithin 0 (Ioi 0) := Ioo_mem_nhdsGT zero_lt_one
  have hdW_le : ∀ p ∈ Ioc (0 : ℝ) 1,
      wassersteinDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z) ≤ ENNReal.ofReal p := by
    intro p hp
    obtain ⟨_, hN_aem, hN_law⟩ := hFam p hp
    have hmap : (P p).map (fun ω ↦ p * (N p ω : ℝ)) =
        (shiftedGeomLaw p).map (fun n : ℕ ↦ p * (n : ℝ)) := by
      change (P p).map ((fun n : ℕ ↦ p * (n : ℝ)) ∘ N p) = _
      rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hN_aem, hN_law]
    rw [hmap, hZ_law]
    exact wassersteinDist_shiftedGeomLaw_le hp.1 hp.2
  have hdW_lim : Tendsto
      (fun p : ℝ ↦ wassersteinDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have hof : Tendsto (fun p : ℝ ↦ ENNReal.ofReal p) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof
      (Eventually.of_forall fun _ ↦ bot_le) (Filter.eventually_of_mem hmem_Ioc hdW_le)
  have hdK_lim : Tendsto
      (fun p : ℝ ↦ kolmogorovDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have hmul : Tendsto
        (fun p : ℝ ↦ 2 * wassersteinDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z))
        (nhdsWithin 0 (Ioi 0)) (𝓝 (2 * 0)) :=
      ENNReal.Tendsto.const_mul hdW_lim (Or.inr ENNReal.ofNat_ne_top)
    rw [mul_zero] at hmul
    have hrpow := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hmul
    have hrpow0 : Tendsto
        (fun p : ℝ ↦
          (2 * wassersteinDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z)) ^ (1 / 2 : ℝ))
        (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        using hrpow
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrpow0
      (Eventually.of_forall fun _ ↦ bot_le) ?_
    filter_upwards [hmem_Ioc] with p hp
    obtain ⟨hP_prob, hN_aem, _⟩ := hFam p hp
    have hWp_aem : AEMeasurable (fun ω ↦ p * (N p ω : ℝ)) (P p) :=
      ((by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hN_aem).const_mul p
    have : IsProbabilityMeasure ((P p).map (fun ω ↦ p * (N p ω : ℝ))) :=
      (Measure.isProbabilityMeasure_map_iff hWp_aem).mpr hP_prob
    rw [hZ_law]
    exact kolmogorovDist_le_sqrt_two_mul_wassersteinDist_stdExpLaw _
  refine ⟨hdW_lim, hdK_lim, fun g hg_cont ⟨M, hg_bdd⟩ ↦ ?_⟩
  have hceil_meas : Measurable (Nat.ceil : ℝ → ℕ) :=
    Monotone.measurable fun _ _ hab ↦ Nat.ceil_mono hab
  let r : ℝ → ℝ := fun p ↦ -Real.log (1 - p)
  let Q : ℝ → ℝ → ℝ := fun p u ↦ p * (Nat.ceil (u / r p) : ℝ)
  have hr_pos : ∀ p ∈ Ioo (0 : ℝ) 1, 0 < r p ∧ 1 - Real.exp (-r p) = p := by
    intro p ⟨hp0, hp1⟩
    have h1p_pos : 0 < 1 - p := by linarith
    have h1p_lt : 1 - p < 1 := by linarith
    have hlog_neg : Real.log (1 - p) < 0 := Real.log_neg h1p_pos h1p_lt
    refine ⟨by dsimp only [r]; linarith, ?_⟩
    dsimp only [r]
    rw [neg_neg, Real.exp_log h1p_pos]
    ring
  have hSlope : Tendsto (fun p : ℝ ↦ p / r p) (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
    have hhd : HasDerivAt r 1 0 := by
      have h1 : HasDerivAt (fun p : ℝ ↦ 1 - p) (-1) 0 := by
        simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub (hasDerivAt_id (0 : ℝ))
      have h2 : HasDerivAt (fun p : ℝ ↦ Real.log (1 - p)) ((-1) / (1 - 0)) 0 :=
        h1.log (by norm_num)
      convert h2.neg using 1
      norm_num
    have hsl := (hasDerivAt_iff_tendsto_slope_zero.mp hhd).mono_left
      (nhdsWithin_mono (0 : ℝ) (fun p (hp : 0 < p) ↦ ne_of_gt hp))
    have hsl' : Tendsto (fun p : ℝ ↦ r p / p) (nhdsWithin 0 (Ioi 0)) (𝓝 1) := by
      refine hsl.congr fun p ↦ ?_
      have hr0 : r 0 = 0 := by simp [r]
      rw [zero_add, hr0, sub_zero, smul_eq_mul, inv_mul_eq_div]
    have hinv := hsl'.inv₀ one_ne_zero
    rw [inv_one] at hinv
    exact hinv.congr fun p ↦ inv_div (r p) p
  have hQ_lim : ∀ᵐ u ∂stdExpLaw, Tendsto (fun p : ℝ ↦ g (Q p u)) (nhdsWithin 0 (Ioi 0))
      (𝓝 (g u)) := by
    filter_upwards [ae_pos_expLaw 1] with u hu
    refine hg_cont.continuousAt.tendsto.comp ?_
    have hlow_lim : Tendsto (fun p : ℝ ↦ (p / r p) * u) (nhdsWithin 0 (Ioi 0)) (𝓝 u) := by
      simpa using hSlope.mul_const u
    have hupp_lim : Tendsto (fun p : ℝ ↦ (p / r p) * u + p) (nhdsWithin 0 (Ioi 0)) (𝓝 u) := by
      have hid_lim : Tendsto (id : ℝ → ℝ) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
        continuous_id.continuousAt.tendsto.mono_left inf_le_left
      simpa using hlow_lim.add hid_lim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hupp_lim ?_ ?_
    · filter_upwards [hmem_Ioo] with p hp
      obtain ⟨hrp, _⟩ := hr_pos p hp
      have hle : u / r p ≤ (Nat.ceil (u / r p) : ℝ) := Nat.le_ceil (u / r p)
      calc
        (p / r p) * u = p * (u / r p) := by ring
        _ ≤ p * (Nat.ceil (u / r p) : ℝ) := mul_le_mul_of_nonneg_left hle hp.1.le
    · filter_upwards [hmem_Ioo] with p hp
      obtain ⟨hrp, _⟩ := hr_pos p hp
      have hpos_div : 0 < u / r p := div_pos hu hrp
      have hlt : (Nat.ceil (u / r p) : ℝ) < u / r p + 1 := Nat.ceil_lt_add_one hpos_div.le
      calc
        p * (Nat.ceil (u / r p) : ℝ) ≤ p * (u / r p + 1) :=
          mul_le_mul_of_nonneg_left hlt.le hp.1.le
        _ = (p / r p) * u + p := by ring
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (l := nhdsWithin (0 : ℝ) (Ioi 0)) (μ := stdExpLaw)
    (F := fun p u ↦ g (Q p u)) (f := g) (fun _ ↦ M)
    (Filter.eventually_of_mem hmem_Ioo fun p _ ↦
      (hg_cont.measurable.comp
        (measurable_const.mul ((by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).comp
          (hceil_meas.comp (measurable_id.div_const (r p)))))).aestronglyMeasurable)
    (Eventually.of_forall fun p ↦ Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs]; exact hg_bdd _)
    (integrable_const M) hQ_lim
  have hZ_int : ∫ u, g u ∂stdExpLaw = ∫ z, g (Z z) ∂P' := by
    rw [← hZ_law, integral_map hZ_aem hg_cont.measurable.aestronglyMeasurable]
  rw [hZ_int] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [hmem_Ioo] with p hp
  obtain ⟨hP_prob, hN_aem, hN_law⟩ := hFam p ⟨hp.1, hp.2.le⟩
  obtain ⟨hrp, h1exp⟩ := hr_pos p hp
  have hceil_law : stdExpLaw.map (fun u ↦ Nat.ceil (u / r p)) = shiftedGeomLaw p := by
    have hc := ex5_4_ceil_corrected stdExpLaw hrp (measurable_id.div_const (r p)).aemeasurable
      (stdExpLaw_map_div_eq_expLaw hrp)
    rwa [h1exp] at hc
  have hQ_meas : Measurable (fun u : ℝ ↦ Nat.ceil (u / r p)) :=
    hceil_meas.comp (measurable_id.div_const (r p))
  have hg_scale_meas : Measurable (fun n : ℕ ↦ g (p * (n : ℝ))) :=
    hg_cont.measurable.comp (measurable_const.mul (by fun_prop))
  calc
    ∫ u, g (Q p u) ∂stdExpLaw
      = ∫ n, g (p * (n : ℝ)) ∂(stdExpLaw.map (fun u ↦ Nat.ceil (u / r p))) :=
          (integral_map hQ_meas.aemeasurable hg_scale_meas.aestronglyMeasurable).symm
    _ = ∫ n, g (p * (n : ℝ)) ∂(P p).map (N p) := by rw [hceil_law, hN_law]
    _ = ∫ ω, g (p * (N p ω : ℝ)) ∂(P p) :=
          integral_map hN_aem hg_scale_meas.aestronglyMeasurable

end SteinMethod
