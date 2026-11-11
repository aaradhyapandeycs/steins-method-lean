/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonDep.ErdosRenyiBounds
import Formalization.PoissonDep.HeadRunAsymptotics
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The Erdős–Rényi Law for Longest Quality Head Runs
(`Formalization.PoissonDep.ErdosRenyiLaw`)

Proves Theorem 4.9 (`[\ER\ Law]`, `SteinIntro.tex:2071-2078`; corrected rare-event regime
`0 < p < a ≤ 1`, `ISSUE-4.9`) of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`) from scratch via dyadic subsequence interpolation (`2 ^ m`), exact
Cramér–Chernoff and elementary binomial tail bounds (`Formalization.PoissonDep.ErdosRenyiBounds`),
and the first Borel–Cantelli lemma (`MeasureTheory.ae_eventually_notMem`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Geometric Borel–Cantelli Helper -/

private lemma geom_sum_le_inv_one_sub' {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    ∑ m ∈ Finset.range N, q ^ m ≤ 1 / (1 - q) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  rw [le_div_iff₀ h1q]
  have hid : (∑ m ∈ Finset.range N, q ^ m) * (1 - q) = 1 - q ^ N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring
  rw [hid]
  linarith [pow_nonneg hq0 N]

/-- If `P.real (s m) ≤ C * r ^ m` eventually with `0 ≤ r < 1` and `0 ≤ C`, then almost surely
`ω ∉ s m` eventually as `m → ∞`. -/
private lemma ae_eventually_notMem_of_probReal_geom
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {s : ℕ → Set Ω} {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ᶠ m : ℕ in atTop, P.real (s m) ≤ C * r ^ m) :
    ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, ω ∉ s m := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hbound
  refine ae_eventually_notMem ?_
  rw [ENNReal.tsum_eq_iSup_nat]
  have htop_bound : (⨆ N : ℕ, ∑ m ∈ Finset.range N, P (s m)) ≤
      (M₀ : ℝ≥0∞) + ENNReal.ofReal (C * (1 / (1 - r))) := by
    refine iSup_le fun N ↦ ?_
    have hterm : ∀ m ∈ Finset.range N,
        P (s m) ≤ (if m < M₀ then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal (C * r ^ m) := by
      intro m _
      by_cases hm : m < M₀
      · simp only [hm, ↓reduceIte]
        exact prob_le_one.trans le_self_add
      · simp only [hm, ↓reduceIte, zero_add]
        have hle := hM₀ m (Nat.le_of_not_lt hm)
        rw [← ENNReal.ofReal_toReal (measure_ne_top P (s m))]
        exact ENNReal.ofReal_le_ofReal hle
    calc ∑ m ∈ Finset.range N, P (s m)
      _ ≤ ∑ m ∈ Finset.range N,
            ((if m < M₀ then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal (C * r ^ m)) :=
        Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.range N, if m < M₀ then (1 : ℝ≥0∞) else 0) +
            ∑ m ∈ Finset.range N, ENNReal.ofReal (C * r ^ m) := Finset.sum_add_distrib
      _ ≤ (M₀ : ℝ≥0∞) + ENNReal.ofReal (C * (1 / (1 - r))) := by
        refine add_le_add ?_ ?_
        · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]
          have hsub : (Finset.range N).filter (· < M₀) ⊆ Finset.range M₀ := by
            intro m hm
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
          exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_range M₀).le
        · rw [← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ mul_nonneg hC (pow_nonneg hr0 m),
            ← Finset.mul_sum]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (geom_sum_le_inv_one_sub' hr0 hr1 N) hC)
  exact (htop_bound.trans_lt (ENNReal.add_lt_top.mpr
    ⟨ENNReal.natCast_lt_top M₀, ENNReal.ofReal_lt_top⟩)).ne

/-! ### Uniform Asymptotic Block Lower Bound (`0 < p < a ≤ 1`) -/

/-- For any `0 < p < a ≤ 1` and `η > 0`, there exists `K₀ ≥ 1` such that every contiguous block
of length `k ≥ K₀` has quality-`a` probability at least `exp(-k (H(a, p) + η))`. -/
private lemma probReal_block_quality_eventually_ge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a η : ℝ} {Y : ℕ → Ω → ℕ}
    (hp0 : 0 < p) (hpa : p < a) (ha1 : a ≤ 1) (hη : 0 < η)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    (hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hYp : ∀ i : ℕ, P.real {ω | Y i ω = 1} = p) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ k ≥ K₀, ∀ b : ℕ,
      Real.exp (-(k : ℝ) * (klDivBernoulli a p + η)) ≤
        P.real {ω | a * (k : ℝ) ≤ ∑ r ∈ Finset.Ico (b * k) (b * k + k), (Y r ω : ℝ)} := by
  let H : ℝ := klDivBernoulli a p
  rcases ha1.eq_or_lt with rfl | ha1_lt
  · refine ⟨1, le_rfl, fun k _ b ↦ ?_⟩
    let s : Finset ℕ := Finset.Ico (b * k) (b * k + k)
    have hs_card : s.card = k := by simp [s]
    let g : ℕ → ℕ → ℝ := fun _ u ↦ if u = 1 then 1 else 0
    let E : Set Ω := {ω | ∏ r ∈ s, g r (Y r ω) = 1}
    have hE_meas : MeasurableSet E := by
      have hm : Measurable fun ω ↦ ∏ r ∈ s, g r (Y r ω) :=
        Finset.measurable_prod s fun r _ ↦
          (Measurable.of_discrete : Measurable (g r)).comp (hY_meas r)
      exact hm (measurableSet_singleton 1)
    have hE_sub : E ⊆ {ω | (1 : ℝ) * (k : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} := by
      intro ω hω
      change ∏ r ∈ s, g r (Y r ω) = 1 at hω
      have hall1 : ∀ r ∈ s, Y r ω = 1 := by
        intro r hr
        by_contra hne1
        have hz : ∏ r' ∈ s, g r' (Y r' ω) = 0 :=
          Finset.prod_eq_zero hr (by simp [g, hne1])
        linarith
      change (1 : ℝ) * (k : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)
      have h1 : ∑ r ∈ s, (Y r ω : ℝ) = ∑ _r ∈ s, (1 : ℝ) :=
        Finset.sum_congr rfl fun r hr ↦ by simp [hall1 r hr]
      rw [h1, Finset.sum_const, hs_card, nsmul_eq_mul, mul_one, one_mul]
    have hprod01 : ∀ ω, ∏ r ∈ s, g r (Y r ω) = 0 ∨ ∏ r ∈ s, g r (Y r ω) = 1 := by
      intro ω
      by_cases h1 : ∀ r ∈ s, Y r ω = 1
      · exact Or.inr (Finset.prod_eq_one fun r hr ↦ by simp [g, h1 r hr])
      · push Not at h1
        obtain ⟨r₀, hr₀, hne⟩ := h1
        exact Or.inl (Finset.prod_eq_zero hr₀ (by simp [g, hne]))
    have hE_prob : P.real E = p ^ k := by
      have hind_eq : E.indicator (1 : Ω → ℝ) = fun ω ↦ ∏ r ∈ s, g r (Y r ω) := by
        ext ω
        rcases hprod01 ω with h0 | h1
        · have hnot : ω ∉ E := by change ¬(_ = 1); rw [h0]; norm_num
          simp [Set.indicator_of_notMem hnot, h0]
        · have hmem : ω ∈ E := h1
          simp [Set.indicator_of_mem hmem, h1]
      have hY_ae : ∀ i : ℕ, AEMeasurable (Y i) P := fun i ↦ (hY_meas i).aemeasurable
      rw [← integral_indicator_one hE_meas, hind_eq,
        integral_finset_prod_indep_nat hY_ae hY_indep s g]
      have hfac : ∀ r ∈ s, ∫ ω, g r (Y r ω) ∂P = p := by
        intro r _
        have hae_r : (fun ω ↦ g r (Y r ω)) =ᵐ[P] fun ω ↦ (Y r ω : ℝ) := by
          filter_upwards [hY01 r] with ω hω
          rcases hω with h | h <;> simp [g, h]
        rw [integral_congr_ae hae_r, integral_natCast_of_ae_zero_or_one (hY_ae r) (hY01 r), hYp r]
      rw [Finset.prod_congr rfl hfac, Finset.prod_const, hs_card]
    have hp_exp : p ^ k = Real.exp (-(k : ℝ) * H) := by
      have h1 : -(k : ℝ) * H = (k : ℝ) * Real.log p := by
        simp only [H, klDivBernoulli, ↓reduceIte, one_div, Real.log_inv]; ring
      rw [h1, Real.exp_nat_mul, Real.exp_log hp0]
    have hexp_le : Real.exp (-(k : ℝ) * (H + η)) ≤ Real.exp (-(k : ℝ) * H) := by
      refine Real.exp_le_exp.mpr ?_
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    exact hexp_le.trans (hp_exp ▸ hE_prob ▸ measureReal_mono hE_sub (measure_ne_top P _))
  · have ha0 : 0 < a := hp0.trans hpa
    have hp1 : p < 1 := hpa.trans ha1_lt
    have h1a : 0 < 1 - a := sub_pos.mpr ha1_lt
    have hcont := continuousAt_klDivBernoulli ha0 ha1_lt hp0 hp1
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ_x, hδ_x_pos, hδ_x⟩ := hcont (η / 2) (half_pos hη)
    have hlog_small : ∀ᶠ k : ℕ in atTop, Real.log ((k : ℝ) + 1) ≤ (η / 2) * (k : ℝ) := by
      have htend_succ : Tendsto (fun k : ℕ ↦ Real.log ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
          atTop (𝓝 0) :=
        tendsto_log_div_natCast_atTop.comp (tendsto_add_atTop_nat 1)
      have hev := (tendsto_order.mp htend_succ).2 (η / 4) (by linarith)
      filter_upwards [hev, eventually_ge_atTop 1] with k hk hk1
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hle1 : Real.log ((k + 1 : ℕ) : ℝ) < (η / 4) * ((k + 1 : ℕ) : ℝ) :=
        (div_lt_iff₀ hk1_pos).mp hk
      push_cast at hle1
      have hk_r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      nlinarith
    have hinv_small : ∀ᶠ k : ℕ in atTop, 1 / (k : ℝ) < min δ_x (1 - a) := by
      have hmin_pos : 0 < min δ_x (1 - a) := lt_min hδ_x_pos h1a
      have htend0 : Tendsto (fun k : ℕ ↦ 1 / (k : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      exact (tendsto_order.mp htend0).2 _ hmin_pos
    have hak_ge1 : ∀ᶠ k : ℕ in atTop, 1 ≤ a * (k : ℝ) := by
      have htend_ak : Tendsto (fun k : ℕ ↦ a * (k : ℝ)) atTop atTop :=
        Filter.Tendsto.const_mul_atTop ha0 tendsto_natCast_atTop_atTop
      exact htend_ak.eventually_ge_atTop 1
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
      ((eventually_ge_atTop 2).and (hlog_small.and (hinv_small.and hak_ge1)))
    refine ⟨max 1 K₀, le_max_left 1 K₀, fun k hk b ↦ ?_⟩
    obtain ⟨_hk2, hlog_k, hinv_k, hak1⟩ := hK₀ k ((le_max_right 1 K₀).trans hk)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    let m : ℕ := Nat.ceil (a * (k : ℝ))
    have hak_le_m : a * (k : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
    have hm_lt_ak1 : (m : ℝ) < a * (k : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hm1 : 1 ≤ m := by
      have : (1 : ℝ) ≤ (m : ℝ) := hak1.trans hak_le_m
      exact_mod_cast this
    have hinv_1a : 1 / (k : ℝ) < 1 - a := hinv_k.trans_le (min_le_right _ _)
    have h1_lt_1ak : 1 < (1 - a) * (k : ℝ) := (div_lt_iff₀ hk_pos).mp hinv_1a
    have hmk : m < k := by
      have hm_lt_k : (m : ℝ) < (k : ℝ) := by linarith
      exact_mod_cast hm_lt_k
    have hdist_x : dist ((m : ℝ) / (k : ℝ)) a < δ_x := by
      rw [Real.dist_eq]
      have hlo : a ≤ (m : ℝ) / (k : ℝ) := (le_div_iff₀ hk_pos).mpr hak_le_m
      have hhi : (m : ℝ) / (k : ℝ) - a < 1 / (k : ℝ) := by
        have h1 : (m : ℝ) / (k : ℝ) - a = ((m : ℝ) - a * (k : ℝ)) / (k : ℝ) := by field_simp
        rw [h1, div_lt_div_iff_of_pos_right hk_pos]
        linarith
      rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      exact hhi.trans (hinv_k.trans_le (min_le_left _ _))
    have hkl_le : klDivBernoulli ((m : ℝ) / (k : ℝ)) p ≤ H + η / 2 := by
      have hd := hδ_x hdist_x
      rw [Real.dist_eq] at hd
      have h2 := (abs_lt.mp hd).2
      dsimp only [H]
      linarith
    let s : Finset ℕ := Finset.Ico (b * k) (b * k + k)
    have hs_card : s.card = k := by simp [s]
    have hms : m < s.card := hs_card ▸ hmk
    have hbinom := probReal_sum_ge_ge_klDiv_nat P hp0 hp1 hY_meas hY_indep hY01 hYp s hm1 hms
    rw [hs_card] at hbinom
    have hsub_ev : {ω | (m : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} ⊆
        {ω | a * (k : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} :=
      fun _ hω ↦ hak_le_m.trans hω
    have hmono_ev := measureReal_mono hsub_ev (measure_ne_top P _)
    have hexp_inv : Real.exp (-(k : ℝ) * (η / 2)) ≤ 1 / ((k : ℝ) + 1) := by
      have hk1_pos : 0 < (k : ℝ) + 1 := by positivity
      have heq_inv : 1 / ((k : ℝ) + 1) = Real.exp (-Real.log ((k : ℝ) + 1)) := by
        rw [Real.exp_neg, Real.exp_log hk1_pos, one_div]
      rw [heq_inv]
      exact Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (-(k : ℝ) * (H + η))
      _ = Real.exp (-(k : ℝ) * (η / 2)) * Real.exp (-(k : ℝ) * (H + η / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ (1 / ((k : ℝ) + 1)) *
            Real.exp (-(k : ℝ) * klDivBernoulli ((m : ℝ) / (k : ℝ)) p) := by
        refine mul_le_mul hexp_inv ?_ (Real.exp_pos _).le (by positivity)
        exact Real.exp_le_exp.mpr (by nlinarith)
      _ ≤ P.real {ω | (m : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} := hbinom
      _ ≤ P.real {ω | a * (k : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} := hmono_ev

/-! ### Fixed-`δ` Upper and Lower Almost-Sure Bounds via Dyadic Interpolation -/

/-- Almost-sure upper bound along `n → ∞` for any `δ > 0`. -/
private lemma ae_eventually_longestQualityRun_div_log_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a δ : ℝ} {Y : ℕ → Ω → ℕ}
    (hp0 : 0 < p) (hpa : p < a) (ha1 : a ≤ 1) (hδ : 0 < δ)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    (hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hYp : ∀ i : ℕ, P.real {ω | Y i ω = 1} = p) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ) ≤
        1 / klDivBernoulli a p + δ := by
  let H : ℝ := klDivBernoulli a p
  have hH_pos : 0 < H := klDivBernoulli_pos hp0 hpa ha1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let ε : ℝ := (H / 2) * δ
  have hε_pos : 0 < ε := by positivity
  let N : ℕ → ℕ := fun m ↦ 2 ^ (m + 1)
  let k : ℕ → ℕ := fun m ↦ max 1 (Nat.ceil (((1 + ε) / H) * Real.log (N m : ℝ)))
  let s : ℕ → Set Ω := fun m ↦
    {ω | k m ≤ longestQualityRun a (fun i : Fin (N m) ↦ Y i.1 ω)}
  let r : ℝ := Real.exp (-ε * Real.log 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h1exp_pos : 0 < 1 - Real.exp (-H) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hH_pos))
  let C : ℝ := 2 / (1 - Real.exp (-H))
  have hC_nn : 0 ≤ C := by positivity
  have hprob_s : ∀ᶠ m : ℕ in atTop, P.real (s m) ≤ C * r ^ m := by
    refine Eventually.of_forall fun m ↦ ?_
    have hk1 : 1 ≤ k m := le_max_left 1 _
    have hub := probReal_longestQualityRun_ge_le P hp0 hpa ha1 hY_meas hY_indep hY01 hYp
      (N m) hk1
    have hlog_Nm : Real.log (N m : ℝ) = ((m + 1 : ℕ) : ℝ) * Real.log 2 := by
      dsimp only [N]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hk_ge : ((1 + ε) / H) * Real.log (N m : ℝ) ≤ (k m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
    have hkH_ge : (1 + ε) * Real.log (N m : ℝ) ≤ (k m : ℝ) * H := by
      have hm := mul_le_mul_of_nonneg_right hk_ge hH_pos.le
      have hsimp : ((1 + ε) / H) * Real.log (N m : ℝ) * H = (1 + ε) * Real.log (N m : ℝ) := by
        field_simp
      linarith
    have hexp_le : Real.exp (-(k m : ℝ) * H) ≤
        ((1 / 2 : ℝ) ^ (m + 1)) * r ^ (m + 1) := by
      have h1 : Real.exp (-(k m : ℝ) * H) ≤ Real.exp (-(1 + ε) * Real.log (N m : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-(1 + ε) * Real.log (N m : ℝ)) =
          ((1 / 2 : ℝ) ^ (m + 1)) * r ^ (m + 1) := by
        rw [hlog_Nm]
        have hhalf : (1 / 2 : ℝ) ^ (m + 1) = Real.exp (-(((m + 1 : ℕ) : ℝ) * Real.log 2)) := by
          have harg : -(((m + 1 : ℕ) : ℝ) * Real.log 2) =
              ((m + 1 : ℕ) : ℝ) * (-Real.log 2) := by ring
          rw [harg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num), one_div]
        have hr_pow : r ^ (m + 1) = Real.exp (((m + 1 : ℕ) : ℝ) * (-ε * Real.log 2)) := by
          dsimp only [r]
          rw [← Real.exp_nat_mul]
        rw [hhalf, hr_pow, ← Real.exp_add]
        congr 1; ring
      exact h2 ▸ h1
    have hNm1_le : ((N m + 1 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ (m + 1) := by
      have hpos_pow : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow (m + 1) 2 (by norm_num)
      have hnat : N m + 1 ≤ 2 * 2 ^ (m + 1) := by dsimp only [N]; omega
      exact_mod_cast hnat
    have hr_m1_le : r ^ (m + 1) ≤ r ^ m := by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hr0 m) hr1.le
    calc P.real (s m)
      _ ≤ (((N m + 1 : ℕ) : ℝ) / (1 - Real.exp (-H))) * Real.exp (-(k m : ℝ) * H) := hub
      _ ≤ ((2 * (2 : ℝ) ^ (m + 1)) / (1 - Real.exp (-H))) *
            (((1 / 2 : ℝ) ^ (m + 1)) * r ^ (m + 1)) := by
        refine mul_le_mul ?_ hexp_le (Real.exp_pos _).le (by positivity)
        exact div_le_div_of_nonneg_right hNm1_le h1exp_pos.le
      _ = C * r ^ (m + 1) := by
        dsimp only [C]
        have hcancel : (2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) ^ (m + 1) = 1 := by
          rw [← mul_pow]; norm_num
        calc ((2 * (2 : ℝ) ^ (m + 1)) / (1 - Real.exp (-H))) *
              (((1 / 2 : ℝ) ^ (m + 1)) * r ^ (m + 1))
          _ = (2 / (1 - Real.exp (-H))) *
                ((2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) ^ (m + 1)) * r ^ (m + 1) := by ring
          _ = (2 / (1 - Real.exp (-H))) * r ^ (m + 1) := by rw [hcancel, mul_one]
      _ ≤ C * r ^ m := mul_le_mul_of_nonneg_left hr_m1_le hC_nn
  have hae_bc := ae_eventually_notMem_of_probReal_geom P hC_nn hr0 hr1 hprob_s
  have hratio_ev : ∀ᶠ m : ℕ in atTop,
      (k m : ℝ) / ((m : ℝ) * Real.log 2) ≤ 1 / H + δ := by
    have h1εH : (1 + ε) / H = 1 / H + δ / 2 := by
      dsimp only [ε]; field_simp
    have htend_rhs : Tendsto
        (fun m : ℕ ↦ ((1 + ε) / H) * (((m : ℝ) + 1) / (m : ℝ)) + 1 / ((m : ℝ) * Real.log 2))
        atTop (𝓝 ((1 + ε) / H)) := by
      have ht1 : Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1) / (m : ℝ)) atTop (𝓝 1) := by
        have hcongr : (fun m : ℕ ↦ ((m : ℝ) + 1) / (m : ℝ)) =ᶠ[atTop]
            fun m : ℕ ↦ 1 + 1 / (m : ℝ) := by
          filter_upwards [eventually_ge_atTop 1] with m hm
          have hm_ne : (m : ℝ) ≠ 0 := by positivity
          field_simp
        refine Tendsto.congr' hcongr.symm ?_
        simpa only [add_zero] using
          (tendsto_const_nhds (x := (1 : ℝ))).add
            ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
      have ht2 : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) * Real.log 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (Filter.Tendsto.atTop_mul_const hlog2_pos tendsto_natCast_atTop_atTop)
      simpa only [mul_one, add_zero] using (ht1.const_mul ((1 + ε) / H)).add ht2
    rw [h1εH] at htend_rhs
    have hev_lt := (tendsto_order.mp htend_rhs).2 (1 / H + δ) (by linarith)
    filter_upwards [hev_lt, eventually_ge_atTop 1] with m hm_lt hm1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hlog_Nm : Real.log (N m : ℝ) = ((m : ℝ) + 1) * Real.log 2 := by
      dsimp only [N]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      push_cast; rfl
    have hk_le : (k m : ℝ) ≤ ((1 + ε) / H) * (((m : ℝ) + 1) * Real.log 2) + 1 := by
      have harg_nn : 0 ≤ ((1 + ε) / H) * Real.log (N m : ℝ) := by rw [hlog_Nm]; positivity
      have hceil_le : (Nat.ceil (((1 + ε) / H) * Real.log (N m : ℝ)) : ℝ) ≤
          ((1 + ε) / H) * (((m : ℝ) + 1) * Real.log 2) + 1 := by
        calc (Nat.ceil (((1 + ε) / H) * Real.log (N m : ℝ)) : ℝ)
          _ ≤ ((1 + ε) / H) * Real.log (N m : ℝ) + 1 := (Nat.ceil_lt_add_one harg_nn).le
          _ = ((1 + ε) / H) * (((m : ℝ) + 1) * Real.log 2) + 1 := by rw [hlog_Nm]
      have h1_le : (1 : ℝ) ≤ ((1 + ε) / H) * (((m : ℝ) + 1) * Real.log 2) + 1 := by
        have : 0 ≤ ((1 + ε) / H) * (((m : ℝ) + 1) * Real.log 2) := by positivity
        linarith
      have hmax_cast : (k m : ℝ) =
          max (1 : ℝ) (Nat.ceil (((1 + ε) / H) * Real.log (N m : ℝ)) : ℝ) := by
        dsimp only [k]; exact_mod_cast rfl
      rw [hmax_cast]
      exact max_le h1_le hceil_le
    calc (k m : ℝ) / ((m : ℝ) * Real.log 2)
      _ ≤ (((1 + ε) / H) * (((m : ℝ) + 1) * Real.log 2) + 1) / ((m : ℝ) * Real.log 2) :=
        div_le_div_of_nonneg_right hk_le (by positivity)
      _ = ((1 + ε) / H) * (((m : ℝ) + 1) / (m : ℝ)) + 1 / ((m : ℝ) * Real.log 2) := by
        field_simp
      _ ≤ 1 / H + δ := by rw [h1εH]; exact hm_lt.le
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp ((eventually_ge_atTop 1).and hratio_ev)
  filter_upwards [hae_bc] with ω hω
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hω
  let M : ℕ := max M₀ M₁
  rw [eventually_atTop]
  refine ⟨2 ^ M, fun n hn ↦ ?_⟩
  have hn_pos : 0 < n := (Nat.pos_of_ne_zero (by positivity : 2 ^ M ≠ 0)).trans_le hn
  have hn_ne0 : n ≠ 0 := hn_pos.ne'
  let m : ℕ := Nat.log 2 n
  have hM_le_m : M ≤ m := Nat.le_log_of_pow_le (by norm_num) hn
  have hm0 : M₀ ≤ m := (le_max_left M₀ M₁).trans hM_le_m
  have hm1_idx : M₁ ≤ m := (le_max_right M₀ M₁).trans hM_le_m
  have hm_ge1 : 1 ≤ m := ((hM₁ M₁ le_rfl).1).trans hm1_idx
  have hpow_le_n : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn_ne0
  have hn_lt_Nm : n < N m := (Nat.log_lt_iff_lt_pow (by norm_num) hn_ne0).mp (Nat.lt_succ_self m)
  have hRn_le_RNm : longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) ≤
      longestQualityRun a (fun i : Fin (N m) ↦ Y i.1 ω) :=
    longestQualityRun_mono_prefix hn_lt_Nm.le (fun i ↦ Y i ω)
  have hRNm_lt_k : longestQualityRun a (fun i : Fin (N m) ↦ Y i.1 ω) < k m :=
    Nat.lt_of_not_ge (hM₀ m hm0)
  have hRn_le_k : (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) ≤ (k m : ℝ) := by
    exact_mod_cast (hRn_le_RNm.trans hRNm_lt_k.le)
  have hlog_ge : (m : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have hle_cast : ((2 ^ m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow_le_n
    calc (m : ℝ) * Real.log 2
      _ = Real.log ((2 ^ m : ℕ) : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) hle_cast
  have hmlog2_pos : 0 < (m : ℝ) * Real.log 2 := by
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_ge1
    positivity
  calc (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ)
    _ ≤ (k m : ℝ) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_right hRn_le_k (hmlog2_pos.trans_le hlog_ge).le
    _ ≤ (k m : ℝ) / ((m : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hmlog2_pos hlog_ge
    _ ≤ 1 / H + δ := (hM₁ m hm1_idx).2

/-- Almost-sure lower bound along `n → ∞` for any `δ > 0`. -/
private lemma ae_eventually_longestQualityRun_div_log_ge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a δ : ℝ} {Y : ℕ → Ω → ℕ}
    (hp0 : 0 < p) (hpa : p < a) (ha1 : a ≤ 1) (hδ : 0 < δ)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    (hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hYp : ∀ i : ℕ, P.real {ω | Y i ω = 1} = p) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      1 / klDivBernoulli a p - δ ≤
        (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ) := by
  let H : ℝ := klDivBernoulli a p
  have hH_pos : 0 < H := klDivBernoulli_pos hp0 hpa ha1
  by_cases htriv : 1 / H - δ ≤ 0
  · refine Eventually.of_forall fun ω ↦ ?_
    filter_upwards [eventually_ge_atTop 2] with n hn2
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hnn : 0 ≤ (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hlog_pos.le
    exact htriv.trans hnn
  push Not at htriv
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c : ℝ := 1 / H - δ / 2
  have hc_pos : 0 < c := by dsimp only [c]; linarith
  have hcH_lt1 : c * H < 1 := by
    have h1 : (1 / H) * H = 1 := one_div_mul_cancel hH_pos.ne'
    dsimp only [c]; nlinarith
  let η₀ : ℝ := (1 - c * H) / 2
  have hη₀_pos : 0 < η₀ := by dsimp only [η₀]; linarith
  let η : ℝ := η₀ / c
  have hη_pos : 0 < η := div_pos hη₀_pos hc_pos
  have hcHη_eq : c * (H + η) = 1 - η₀ := by
    dsimp only [η, η₀]; field_simp; ring
  obtain ⟨K₀, _hK₀_ge1, hblock⟩ :=
    probReal_block_quality_eventually_ge P hp0 hpa ha1 hη_pos hY_meas hY_indep hY01 hYp
  let M_pow : ℕ → ℕ := fun m ↦ 2 ^ m
  let k : ℕ → ℕ := fun m ↦ max 1 (Nat.floor (c * Real.log (M_pow m : ℝ)))
  let B : ℕ → ℕ := fun m ↦ M_pow m / k m
  let s : ℕ → Set Ω := fun m ↦
    {ω | longestQualityRun a (fun i : Fin (M_pow m) ↦ Y i.1 ω) < k m}
  let r : ℝ := Real.exp (-1)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  let A_coef : ℝ := (η₀ / 3) ^ 3 * (Real.log 2) ^ 2 / c
  have hA_pos : 0 < A_coef := by positivity
  have hprob_s : ∀ᶠ m : ℕ in atTop, P.real (s m) ≤ 1 * r ^ m := by
    have hcmlog_big : ∀ᶠ m : ℕ in atTop,
        ((K₀ : ℝ) + 1) ≤ c * ((m : ℝ) * Real.log 2) := by
      have htend : Tendsto (fun m : ℕ ↦ c * ((m : ℝ) * Real.log 2)) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hc_pos
          (Filter.Tendsto.atTop_mul_const hlog2_pos tendsto_natCast_atTop_atTop)
      exact htend.eventually_ge_atTop _
    have hm_big_A : ∀ᶠ m : ℕ in atTop, 2 / A_coef ≤ (m : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually_ge_atTop _
    filter_upwards [eventually_ge_atTop 1, hcmlog_big, hm_big_A] with m hm1 hcmlog hmA
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    have hm_ge1_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hlog_Mm : Real.log (M_pow m : ℝ) = (m : ℝ) * Real.log 2 := by
      dsimp only [M_pow]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hfloor_ge_K₀ : K₀ ≤ Nat.floor (c * Real.log (M_pow m : ℝ)) := by
      rw [Nat.le_floor_iff (by rw [hlog_Mm]; positivity), hlog_Mm]
      linarith
    have hk_ge_K₀ : K₀ ≤ k m := le_trans hfloor_ge_K₀ (le_max_right 1 _)
    have hk1 : 1 ≤ k m := le_max_left 1 _
    have hk_pos_r : 0 < (k m : ℝ) := by positivity
    have hk_le_cmlog : (k m : ℝ) ≤ c * ((m : ℝ) * Real.log 2) := by
      have hfl : (Nat.floor (c * Real.log (M_pow m : ℝ)) : ℝ) ≤ c * ((m : ℝ) * Real.log 2) := by
        rw [← hlog_Mm]
        exact Nat.floor_le (by rw [hlog_Mm]; positivity)
      have h1_le : (1 : ℝ) ≤ c * ((m : ℝ) * Real.log 2) := by
        have hKnn : (0 : ℝ) ≤ (K₀ : ℝ) := Nat.cast_nonneg K₀
        linarith
      have hmax_cast : (k m : ℝ) =
          max (1 : ℝ) (Nat.floor (c * Real.log (M_pow m : ℝ)) : ℝ) := by
        dsimp only [k]; exact_mod_cast rfl
      rw [hmax_cast]
      exact max_le h1_le hfl
    let q : ℝ := Real.exp (-(k m : ℝ) * (H + η))
    have hq_le1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hq_ge : Real.exp (-(1 - η₀) * ((m : ℝ) * Real.log 2)) ≤ q := by
      dsimp only [q]
      refine Real.exp_le_exp.mpr ?_
      have hmul := mul_le_mul_of_nonneg_right hk_le_cmlog (by positivity : 0 ≤ H + η)
      calc -(1 - η₀) * ((m : ℝ) * Real.log 2)
        _ = -(c * ((m : ℝ) * Real.log 2) * (H + η)) := by rw [← hcHη_eq]; ring
        _ ≤ -(k m : ℝ) * (H + η) := by linarith
    have hB_ge : (2 : ℝ) ^ m / (k m : ℝ) - 1 ≤ (B m : ℝ) := by
      have hdiv_lt : M_pow m < (B m + 1) * k m := by
        dsimp only [B]
        have hk_pos_nat : 0 < k m := hk1
        have hmod := Nat.div_add_mod (M_pow m) (k m)
        have hlt := Nat.mod_lt (M_pow m) hk_pos_nat
        calc M_pow m
          _ = k m * (M_pow m / k m) + M_pow m % k m := hmod.symm
          _ < k m * (M_pow m / k m) + k m := by omega
          _ = (M_pow m / k m + 1) * k m := by ring
      have hdiv_r : (2 : ℝ) ^ m ≤ ((B m : ℝ) + 1) * (k m : ℝ) := by
        have hcast : ((M_pow m : ℕ) : ℝ) ≤ (((B m + 1) * k m : ℕ) : ℝ) := by
          exact_mod_cast hdiv_lt.le
        dsimp only [M_pow] at hcast
        push_cast at hcast
        exact hcast
      have hdiv2 : (2 : ℝ) ^ m / (k m : ℝ) ≤ (B m : ℝ) + 1 :=
        (div_le_iff₀ hk_pos_r).mpr hdiv_r
      linarith
    have h2m_q_ge : (m : ℝ) + 1 ≤ ((2 : ℝ) ^ m / (k m : ℝ)) * q := by
      have h2m_exp : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      let u : ℝ := (η₀ / 3) * ((m : ℝ) * Real.log 2)
      have hu_nn : 0 ≤ u := by positivity
      have hexp_cube : u ^ 3 ≤ Real.exp (η₀ * ((m : ℝ) * Real.log 2)) := by
        have hu_le : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
        have h3u : η₀ * ((m : ℝ) * Real.log 2) = ((3 : ℕ) : ℝ) * u := by
          dsimp only [u]; push_cast; ring
        rw [h3u, Real.exp_nat_mul]
        exact pow_le_pow_left₀ hu_nn hu_le 3
      have hprod_exp : Real.exp (η₀ * ((m : ℝ) * Real.log 2)) =
          (2 : ℝ) ^ m * Real.exp (-(1 - η₀) * ((m : ℝ) * Real.log 2)) := by
        rw [h2m_exp, ← Real.exp_add]
        congr 1; ring
      have hquot_ge : A_coef * (m : ℝ) ^ 2 ≤ ((2 : ℝ) ^ m / (k m : ℝ)) * q := by
        calc A_coef * (m : ℝ) ^ 2
          _ = u ^ 3 / (c * ((m : ℝ) * Real.log 2)) := by dsimp only [A_coef, u]; field_simp
          _ ≤ Real.exp (η₀ * ((m : ℝ) * Real.log 2)) / (c * ((m : ℝ) * Real.log 2)) :=
            div_le_div_of_nonneg_right hexp_cube (by positivity)
          _ ≤ Real.exp (η₀ * ((m : ℝ) * Real.log 2)) / (k m : ℝ) :=
            div_le_div_of_nonneg_left (Real.exp_pos _).le hk_pos_r hk_le_cmlog
          _ = ((2 : ℝ) ^ m / (k m : ℝ)) * Real.exp (-(1 - η₀) * ((m : ℝ) * Real.log 2)) := by
            rw [hprod_exp, div_mul_eq_mul_div, mul_div_assoc]
          _ ≤ ((2 : ℝ) ^ m / (k m : ℝ)) * q :=
            mul_le_mul_of_nonneg_left hq_ge (by positivity)
      have hAm_ge2 : 2 ≤ A_coef * (m : ℝ) := by
        have hm' := mul_le_mul_of_nonneg_left hmA hA_pos.le
        have hsimp : A_coef * (2 / A_coef) = 2 := mul_div_cancel₀ 2 hA_pos.ne'
        linarith
      have hAm2 : (m : ℝ) + 1 ≤ A_coef * (m : ℝ) ^ 2 := by
        calc (m : ℝ) + 1
          _ ≤ 2 * (m : ℝ) := by linarith
          _ ≤ (A_coef * (m : ℝ)) * (m : ℝ) := mul_le_mul_of_nonneg_right hAm_ge2 hm_pos.le
          _ = A_coef * (m : ℝ) ^ 2 := by ring
      exact hAm2.trans hquot_ge
    have hBq_ge_m : (m : ℝ) ≤ (B m : ℝ) * q := by
      have hq_nn : 0 ≤ q := by dsimp only [q]; positivity
      have hmul_B := mul_le_mul_of_nonneg_right hB_ge hq_nn
      rw [sub_mul, one_mul] at hmul_B
      linarith
    have hlt_le := probReal_longestQualityRun_lt_le P hY_meas hY_indep hk1
      (Nat.div_mul_le_self (M_pow m) (k m)) fun b _ ↦ hblock (k m) hk_ge_K₀ b
    have hexp_m : Real.exp (-(B m : ℝ) * q) ≤ 1 * r ^ m := by
      rw [one_mul]
      dsimp only [r]
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by linarith)
    exact hlt_le.trans hexp_m
  have hae_bc := ae_eventually_notMem_of_probReal_geom P zero_le_one hr0 hr1 hprob_s
  have hratio_ev : ∀ᶠ m : ℕ in atTop,
      1 / H - δ ≤ (k m : ℝ) / (((m : ℝ) + 1) * Real.log 2) := by
    have htend_lhs : Tendsto
        (fun m : ℕ ↦ c * ((m : ℝ) / ((m : ℝ) + 1)) - 1 / (((m : ℝ) + 1) * Real.log 2))
        atTop (𝓝 c) := by
      have ht1 : Tendsto (fun m : ℕ ↦ (m : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 1) := by
        have hcongr : (fun m : ℕ ↦ (m : ℝ) / ((m : ℝ) + 1)) =ᶠ[atTop]
            fun m : ℕ ↦ 1 - 1 / ((m : ℝ) + 1) := by
          refine Eventually.of_forall fun m ↦ ?_
          have hm1_ne : (m : ℝ) + 1 ≠ 0 := by positivity
          field_simp; ring
        refine Tendsto.congr' hcongr.symm ?_
        have ht_add : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        simpa only [sub_zero] using
          (tendsto_const_nhds (x := (1 : ℝ))).sub
            ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop ht_add)
      have ht2 : Tendsto (fun m : ℕ ↦ 1 / (((m : ℝ) + 1) * Real.log 2)) atTop (𝓝 0) := by
        have ht_add : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        exact tendsto_const_nhds.div_atTop
          (Filter.Tendsto.atTop_mul_const hlog2_pos ht_add)
      simpa only [mul_one, sub_zero] using (ht1.const_mul c).sub ht2
    have hc_gt : 1 / H - δ < c := by dsimp only [c]; linarith
    have hev_gt := (tendsto_order.mp htend_lhs).1 (1 / H - δ) hc_gt
    filter_upwards [hev_gt] with m hm_gt
    have hlog_Mm : Real.log (M_pow m : ℝ) = (m : ℝ) * Real.log 2 := by
      dsimp only [M_pow]
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hk_ge : c * ((m : ℝ) * Real.log 2) - 1 ≤ (k m : ℝ) := by
      calc c * ((m : ℝ) * Real.log 2) - 1
        _ = c * Real.log (M_pow m : ℝ) - 1 := by rw [hlog_Mm]
        _ ≤ (Nat.floor (c * Real.log (M_pow m : ℝ)) : ℝ) :=
          (Nat.sub_one_lt_floor (c * Real.log (M_pow m : ℝ))).le
        _ ≤ (k m : ℝ) := by dsimp only [k]; exact_mod_cast le_max_right 1 _
    calc 1 / H - δ
      _ ≤ c * ((m : ℝ) / ((m : ℝ) + 1)) - 1 / (((m : ℝ) + 1) * Real.log 2) := hm_gt.le
      _ = (c * ((m : ℝ) * Real.log 2) - 1) / (((m : ℝ) + 1) * Real.log 2) := by field_simp
      _ ≤ (k m : ℝ) / (((m : ℝ) + 1) * Real.log 2) :=
        div_le_div_of_nonneg_right hk_ge (by positivity)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp ((eventually_ge_atTop 1).and hratio_ev)
  filter_upwards [hae_bc] with ω hω
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hω
  let M : ℕ := max M₀ M₁
  rw [eventually_atTop]
  refine ⟨max 2 (2 ^ M), fun n hn ↦ ?_⟩
  have hn2 : 2 ≤ n := (le_max_left 2 (2 ^ M)).trans hn
  have hnM : 2 ^ M ≤ n := (le_max_right 2 (2 ^ M)).trans hn
  have hn_ne0 : n ≠ 0 := by omega
  let m : ℕ := Nat.log 2 n
  have hM_le_m : M ≤ m := Nat.le_log_of_pow_le (by norm_num) hnM
  have hm0 : M₀ ≤ m := (le_max_left M₀ M₁).trans hM_le_m
  have hm1_idx : M₁ ≤ m := (le_max_right M₀ M₁).trans hM_le_m
  have hpow_le_n : M_pow m ≤ n := Nat.pow_log_le_self 2 hn_ne0
  have hn_lt_next : n < 2 ^ (m + 1) :=
    (Nat.log_lt_iff_lt_pow (by norm_num) hn_ne0).mp (Nat.lt_succ_self m)
  have hRMm_ge_k : k m ≤ longestQualityRun a (fun i : Fin (M_pow m) ↦ Y i.1 ω) :=
    Nat.le_of_not_lt (hM₀ m hm0)
  have hRn_ge_RMm : longestQualityRun a (fun i : Fin (M_pow m) ↦ Y i.1 ω) ≤
      longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) :=
    longestQualityRun_mono_prefix hpow_le_n (fun i ↦ Y i ω)
  have hRn_ge_k : (k m : ℝ) ≤ (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) := by
    exact_mod_cast (hRMm_ge_k.trans hRn_ge_RMm)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hlog_le : Real.log (n : ℝ) ≤ ((m : ℝ) + 1) * Real.log 2 := by
    have hle_cast : (n : ℝ) ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hn_lt_next.le
    calc Real.log (n : ℝ)
      _ ≤ Real.log ((2 ^ (m + 1) : ℕ) : ℝ) := Real.log_le_log (by positivity) hle_cast
      _ = ((m : ℝ) + 1) * Real.log 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        push_cast; rfl
  calc 1 / H - δ
    _ ≤ (k m : ℝ) / (((m : ℝ) + 1) * Real.log 2) := (hM₁ m hm1_idx).2
    _ ≤ (k m : ℝ) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlog_pos hlog_le
    _ ≤ (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_right hRn_ge_k hlog_pos.le

/-! ### Theorem 4.9 (`[\ER\ Law]`, `SteinIntro.tex:2071-2078`) -/

/-- **Theorem 4.9** (*Erdős–Rényi Law*, `[\ER\ Law]`, `SteinIntro.tex:2071-2078`; corrected
rare-event regime `0 < p < a ≤ 1`, `ISSUE-4.9`): for i.i.d. `Bernoulli(p)` `{0, 1}` variables
`Y_0, Y_1, \dots` and quality threshold `a` with `0 < p < a ≤ 1`, almost surely
`R_n / \log(n) \to 1 / H(a, p)` as `n \to \infty`, where
`R_n = longestQualityRun a (Y_0, …, Y_{n-1})` and `H(a, p) = klDivBernoulli a p`. -/
theorem erdos_renyi_longestQualityRun_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a : ℝ} {Y : ℕ → Ω → ℕ}
    (hp0 : 0 < p) (hpa : p < a) (ha1 : a ≤ 1)
    (hY_ae : ∀ i : ℕ, AEMeasurable (Y i) P)
    (hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hY_indep : iIndepFun Y P)
    (hYp : ∀ i : ℕ, P.real {ω | Y i ω = 1} = p) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦
          (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ))
        atTop
        (𝓝 (1 / klDivBernoulli a p)) := by
  let Y' : ℕ → Ω → ℕ := fun i ↦ (hY_ae i).mk (Y i)
  have hY'_meas : ∀ i : ℕ, Measurable (Y' i) := fun i ↦ (hY_ae i).measurable_mk
  have hae_eq : ∀ i : ℕ, Y i =ᵐ[P] Y' i := fun i ↦ (hY_ae i).ae_eq_mk
  have hY'_indep : iIndepFun Y' P := (iIndepFun_congr hae_eq).mp hY_indep
  have hY'01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y' i ω = 0 ∨ Y' i ω = 1 := by
    intro i
    filter_upwards [hY01 i, hae_eq i] with ω h01 heq
    rwa [← heq]
  have hY'p : ∀ i : ℕ, P.real {ω | Y' i ω = 1} = p := by
    intro i
    have hcongr : ({ω | Y' i ω = 1} : Set Ω) =ᵐ[P] {ω | Y i ω = 1} := by
      filter_upwards [hae_eq i] with ω heq
      simp [heq]
    rw [measureReal_congr hcongr, hYp i]
  have hae_all : ∀ᵐ ω ∂P, ∀ q : ℕ,
      (∀ᶠ n : ℕ in atTop,
        (longestQualityRun a (fun i : Fin n ↦ Y' i.1 ω) : ℝ) / Real.log (n : ℝ) ≤
          1 / klDivBernoulli a p + 1 / ((q : ℝ) + 1)) ∧
      (∀ᶠ n : ℕ in atTop,
        1 / klDivBernoulli a p - 1 / ((q : ℝ) + 1) ≤
          (longestQualityRun a (fun i : Fin n ↦ Y' i.1 ω) : ℝ) / Real.log (n : ℝ)) := by
    rw [ae_all_iff]
    intro q
    have hδ_pos : 0 < 1 / ((q : ℝ) + 1) := by positivity
    exact (ae_eventually_longestQualityRun_div_log_le P hp0 hpa ha1 hδ_pos hY'_meas hY'_indep
      hY'01 hY'p).and
      (ae_eventually_longestQualityRun_div_log_ge P hp0 hpa ha1 hδ_pos hY'_meas hY'_indep
        hY'01 hY'p)
  filter_upwards [hae_all, ae_all_iff.mpr hae_eq] with ω hω hall_eq
  have hseq_eq : ∀ n : ℕ,
      longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) =
        longestQualityRun a (fun i : Fin n ↦ Y' i.1 ω) := by
    intro n; congr 1; funext i; exact hall_eq i.1
  simp_rw [hseq_eq]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
  obtain ⟨N_q, hN_q⟩ := eventually_atTop.mp ((hω q).1.and (hω q).2)
  refine ⟨N_q, fun n hn ↦ ?_⟩
  obtain ⟨hub, hlb⟩ := hN_q n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end SteinMethod
