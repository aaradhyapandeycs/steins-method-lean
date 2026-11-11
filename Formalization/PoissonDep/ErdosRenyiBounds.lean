/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonDep.ErdosRenyiCounterexample
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Moments.Basic

/-!
# Finite-Sample Large-Deviation Bounds for Longest Quality Runs
(`Formalization.PoissonDep.ErdosRenyiBounds`)

Establishes the finite-sample upper and lower tail inequalities for `longestQualityRun` on i.i.d.
`{0, 1}` sequences needed for the from-scratch proof of Theorem 4.9 (`Erdős–Rényi Law`,
`SteinIntro.tex:2071-2078`):
* `longestQualityRun_mono_prefix`, `continuousAt_klDivBernoulli`, `integral_finset_prod_indep_nat`.
* `probReal_sum_ge_le_exp_klDiv` and `probReal_longestQualityRun_ge_le` (upper tail).
* `probReal_sum_ge_ge_klDiv_nat` and `probReal_longestQualityRun_lt_le` (lower tail).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Prefix Monotonicity, Continuity of Binary KL Divergence, and Product Integrals -/

/-- Prefix monotonicity of `longestQualityRun`: extending a sequence from length `m` to `n ≥ m`
can only increase the longest run of quality at least `a`. -/
theorem longestQualityRun_mono_prefix {a : ℝ} {m n : ℕ} (hmn : m ≤ n) (y : ℕ → ℕ) :
    longestQualityRun a (fun i : Fin m ↦ y i.1) ≤
      longestQualityRun a (fun i : Fin n ↦ y i.1) := by
  classical
  dsimp only [longestQualityRun]
  exact Nat.findGreatest_mono (fun _ ⟨i, hij, hsum⟩ ↦ ⟨i, hij.trans hmn, hsum⟩) hmn

/-- For fixed `p ∈ (0, 1)`, `x ↦ klDivBernoulli x p` is continuous at every `a ∈ (0, 1)`. -/
theorem continuousAt_klDivBernoulli {a p : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousAt (fun x ↦ klDivBernoulli x p) a := by
  have h1a : 0 < 1 - a := sub_pos.mpr ha1
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hap_ne : a / p ≠ 0 := (div_pos ha0 hp0).ne'
  have h1ap_ne : (1 - a) / (1 - p) ≠ 0 := (div_pos h1a h1p).ne'
  have hc1 : ContinuousAt (fun x : ℝ ↦ x * Real.log (x / p)) a :=
    continuousAt_id.mul (ContinuousAt.comp (g := Real.log) (f := fun x : ℝ ↦ x / p)
      (Real.continuousAt_log hap_ne) (continuousAt_id.div_const p))
  have hc_sub : ContinuousAt (fun x : ℝ ↦ 1 - x) a := continuousAt_const.sub continuousAt_id
  have hc2 : ContinuousAt (fun x : ℝ ↦ (1 - x) * Real.log ((1 - x) / (1 - p))) a :=
    hc_sub.mul (ContinuousAt.comp (g := Real.log) (f := fun x : ℝ ↦ (1 - x) / (1 - p))
      (Real.continuousAt_log h1ap_ne) (hc_sub.div_const (1 - p)))
  refine (hc1.add hc2).congr ?_
  filter_upwards [isOpen_Iio.mem_nhds ha1] with x hx
  have hx1 : x ≠ 1 := ne_of_lt hx
  simp only [Pi.add_apply, klDivBernoulli, hx1, ↓reduceIte]

/-- Product of integrals of coordinate functions over a finite subset of an independent `ℕ`-indexed
family of `ℕ`-valued random variables. -/
theorem integral_finset_prod_indep_nat {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℕ} (hY : ∀ i : ℕ, AEMeasurable (Y i) P)
    (hIndep : ProbabilityTheory.iIndepFun Y P)
    (s : Finset ℕ) (g : ℕ → ℕ → ℝ) :
    ∫ ω, ∏ t ∈ s, g t (Y t ω) ∂P = ∏ t ∈ s, ∫ ω, g t (Y t ω) ∂P := by
  classical
  induction s using Finset.induction with
  | empty => simp [probReal_univ]
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    have hdisj : Disjoint ({a} : Finset ℕ) s := Finset.disjoint_singleton_left.mpr ha
    have hind_tup := hIndep.indepFun_finset₀ ({a} : Finset ℕ) s hdisj hY
    have hφ : Measurable fun u : ({a} : Finset ℕ) → ℕ ↦
        g a (u ⟨a, Finset.mem_singleton_self a⟩) :=
      (Measurable.of_discrete : Measurable (g a)).comp (measurable_pi_apply _)
    have hψ : Measurable fun v : s → ℕ ↦ ∏ b : s, g b.1 (v b) :=
      Finset.measurable_prod Finset.univ fun b _ ↦
        (Measurable.of_discrete : Measurable (g b.1)).comp (measurable_pi_apply b)
    have hind_fun : IndepFun (fun ω ↦ g a (Y a ω)) (fun ω ↦ ∏ t ∈ s, g t (Y t ω)) P := by
      have hcomp := hind_tup.comp hφ hψ
      have heq_s : (fun x ↦ ∏ b : s, g b.1 (Y b.1 x)) = fun ω ↦ ∏ t ∈ s, g t (Y t ω) := by
        ext x; exact Finset.prod_coe_sort s (fun t ↦ g t (Y t x))
      simpa only [Function.comp_def, heq_s] using hcomp
    have hsm_a : AEStronglyMeasurable (fun ω ↦ g a (Y a ω)) P :=
      ((Measurable.of_discrete : Measurable (g a)).comp_aemeasurable (hY a)).aestronglyMeasurable
    have hsm_s : AEStronglyMeasurable (fun ω ↦ ∏ t ∈ s, g t (Y t ω)) P := by
      have hae : AEMeasurable (fun ω ↦ ∏ t ∈ s, g t (Y t ω)) P := by
        clear hind_fun hψ hφ hind_tup hdisj ih ha
        induction s using Finset.induction with
        | empty => exact aemeasurable_const
        | insert b s' hb ih' =>
          simp_rw [Finset.prod_insert hb]
          exact ((Measurable.of_discrete : Measurable (g b)).comp_aemeasurable (hY b)).mul ih'
      exact hae.aestronglyMeasurable
    change ∫ ω, ((fun ω' ↦ g a (Y a ω')) * (fun ω' ↦ ∏ t ∈ s, g t (Y t ω'))) ω ∂P = _
    rw [hind_fun.integral_mul_eq_mul_integral hsm_a hsm_s, ih]

/-! ### Exact Cramér–Chernoff Upper Bound on Empirical Sums -/

/-- Exact Cramér–Chernoff upper tail bound for a finite sum of independent `Bernoulli(p)` `{0, 1}`
random variables (`0 < p < a ≤ 1`):
`ℙ(∑_{r ∈ s} Y_r ≥ |s| a) ≤ exp(-|s| H(a, p))`. -/
theorem probReal_sum_ge_le_exp_klDiv
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a : ℝ} {Y : ℕ → Ω → ℕ}
    (hp0 : 0 < p) (hpa : p < a) (ha1 : a ≤ 1)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    (hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hYp : ∀ i : ℕ, P.real {ω | Y i ω = 1} = p)
    (s : Finset ℕ) :
    P.real {ω | a * (s.card : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} ≤
      Real.exp (-(s.card : ℝ) * klDivBernoulli a p) := by
  by_cases hs : s = ∅
  · subst hs
    simp only [Finset.card_empty, Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
    simpa only [probReal_univ] using measureReal_mono (Set.subset_univ _) (measure_ne_top P _)
  rcases ha1.eq_or_lt with rfl | ha1_lt
  · let g : ℕ → ℕ → ℝ := fun _ u ↦ if u = 1 then 1 else 0
    have hae_s : ∀ᵐ ω ∂P, ∀ r ∈ s, Y r ω = 0 ∨ Y r ω = 1 :=
      (ae_ball_iff s.countable_toSet).mpr fun r _ ↦ hY01 r
    let E : Set Ω := {ω | ∏ r ∈ s, g r (Y r ω) = 1}
    have hE_meas : MeasurableSet E := by
      have hm : Measurable fun ω ↦ ∏ r ∈ s, g r (Y r ω) :=
        Finset.measurable_prod s fun r _ ↦
          (Measurable.of_discrete : Measurable (g r)).comp (hY_meas r)
      exact hm (measurableSet_singleton 1)
    have hsub_ae : {ω | (1 : ℝ) * (s.card : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} ≤ᵐ[P] E := by
      filter_upwards [hae_s] with ω hω hsum
      rw [one_mul] at hsum
      change ∏ r ∈ s, g r (Y r ω) = 1
      have hall1 : ∀ r ∈ s, Y r ω = 1 := by
        by_contra hnot
        push Not at hnot
        obtain ⟨r₀, hr₀, hne1⟩ := hnot
        have hr₀_0 : (Y r₀ ω : ℝ) = 0 := by
          rcases hω r₀ hr₀ with h0 | h1
          · simp [h0]
          · exact absurd h1 hne1
        have hle_r : ∀ r ∈ s, (Y r ω : ℝ) ≤ 1 := by
          intro r hr; rcases hω r hr with h | h <;> simp [h]
        have hlt_sum : ∑ r ∈ s, (Y r ω : ℝ) < ∑ _r ∈ s, (1 : ℝ) :=
          Finset.sum_lt_sum hle_r ⟨r₀, hr₀, by simp [hr₀_0]⟩
        rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt_sum
        linarith
      exact Finset.prod_eq_one fun r hr ↦ by simp [g, hall1 r hr]
    have hle_E : P.real {ω | (1 : ℝ) * (s.card : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} ≤ P.real E := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top P E) (measure_mono_ae hsub_ae)
    have hprod01 : ∀ᵐ ω ∂P, ∏ r ∈ s, g r (Y r ω) = 0 ∨ ∏ r ∈ s, g r (Y r ω) = 1 := by
      refine Eventually.of_forall fun ω ↦ ?_
      by_cases h1 : ∀ r ∈ s, Y r ω = 1
      · exact Or.inr (Finset.prod_eq_one fun r hr ↦ by simp [g, h1 r hr])
      · push Not at h1
        obtain ⟨r₀, hr₀, hne⟩ := h1
        exact Or.inl (Finset.prod_eq_zero hr₀ (by simp [g, hne]))
    have hE_int : P.real E = ∫ ω, ∏ r ∈ s, g r (Y r ω) ∂P := by
      have hae_ind : E.indicator (1 : Ω → ℝ) =ᵐ[P] fun ω ↦ ∏ r ∈ s, g r (Y r ω) := by
        filter_upwards [hprod01] with ω hω
        rcases hω with h0 | h1
        · have hnot : ω ∉ E := by change ¬(_ = 1); rw [h0]; norm_num
          simp [Set.indicator_of_notMem hnot, h0]
        · have hmem : ω ∈ E := h1
          simp [Set.indicator_of_mem hmem, h1]
      rw [← integral_indicator_one hE_meas, integral_congr_ae hae_ind]
    have hY_ae : ∀ i : ℕ, AEMeasurable (Y i) P := fun i ↦ (hY_meas i).aemeasurable
    rw [hE_int, integral_finset_prod_indep_nat hY_ae hY_indep s g] at hle_E
    have hfac : ∀ r ∈ s, ∫ ω, g r (Y r ω) ∂P = p := by
      intro r _
      have hae_r : (fun ω ↦ g r (Y r ω)) =ᵐ[P] fun ω ↦ (Y r ω : ℝ) := by
        filter_upwards [hY01 r] with ω hω
        rcases hω with h | h <;> simp [g, h]
      rw [integral_congr_ae hae_r, integral_natCast_of_ae_zero_or_one (hY_ae r) (hY01 r), hYp r]
    rw [Finset.prod_congr rfl hfac, Finset.prod_const] at hle_E
    have hexp1 : p ^ s.card = Real.exp (-(s.card : ℝ) * klDivBernoulli 1 p) := by
      have h1 : -(s.card : ℝ) * klDivBernoulli 1 p = (s.card : ℝ) * Real.log p := by
        simp only [klDivBernoulli, ↓reduceIte, one_div, Real.log_inv]; ring
      rw [h1, Real.exp_nat_mul, Real.exp_log hp0]
    rwa [← hexp1]
  · have ha0 : 0 < a := hp0.trans hpa
    have h1a : 0 < 1 - a := sub_pos.mpr ha1_lt
    have h1p : 0 < 1 - p := sub_pos.mpr (hpa.trans ha1_lt)
    let ratio : ℝ := (a * (1 - p)) / (p * (1 - a))
    have hratio_gt1 : 1 < ratio := by
      dsimp only [ratio]; rw [one_lt_div (mul_pos hp0 h1a)]; nlinarith
    let t : ℝ := Real.log ratio
    have ht_pos : 0 < t := Real.log_pos hratio_gt1
    have hexp_t : Real.exp t = ratio := Real.exp_log (zero_lt_one.trans hratio_gt1)
    let X : ℕ → Ω → ℝ := fun r ω ↦ (Y r ω : ℝ)
    have hcast_meas : Measurable (Nat.cast : ℕ → ℝ) := .of_discrete
    have hX_meas : ∀ r : ℕ, Measurable (X r) := fun r ↦ hcast_meas.comp (hY_meas r)
    have hX_indep : iIndepFun X P :=
      hY_indep.comp (fun _ ↦ Nat.cast) (fun _ ↦ hcast_meas)
    have hX_int_exp : ∀ r ∈ s, Integrable (fun ω ↦ Real.exp (t * X r ω)) P := by
      intro r _
      refine integrable_exp_mul_of_mem_Icc (a := 0) (b := 1) (hX_meas r).aemeasurable ?_
      filter_upwards [hY01 r] with ω hω
      rcases hω with h | h <;> simp [X, h]
    have hmgf_r : ∀ r : ℕ, mgf (X r) P t = (1 - p) / (1 - a) := by
      intro r
      have hae_lin : (fun ω ↦ Real.exp (t * X r ω)) =ᵐ[P]
          fun ω ↦ (1 : ℝ) + (Real.exp t - 1) * X r ω := by
        filter_upwards [hY01 r] with ω hω
        rcases hω with h | h <;> simp [X, h]
      have hXr_int : Integrable (X r) P :=
        integrable_natCast_of_ae_zero_or_one (hY_meas r).aemeasurable (hY01 r)
      have hXr_mean : ∫ ω, X r ω ∂P = p := by
        rw [integral_natCast_of_ae_zero_or_one (hY_meas r).aemeasurable (hY01 r), hYp r]
      have hint2 : Integrable (fun ω ↦ (Real.exp t - 1) * X r ω) P :=
        hXr_int.const_mul (Real.exp t - 1)
      rw [mgf, integral_congr_ae hae_lin, integral_add (integrable_const 1) hint2,
        integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul, hXr_mean, hexp_t]
      dsimp only [ratio]; field_simp; ring
    have hsum_int : Integrable (fun ω ↦ Real.exp (t * (∑ r ∈ s, X r) ω)) P :=
      hX_indep.integrable_exp_mul_sum hX_meas hX_int_exp
    have hchern := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ r ∈ s, X r)
      (a * (s.card : ℝ)) ht_pos.le hsum_int
    rw [hX_indep.mgf_sum hX_meas s] at hchern
    have hprod_mgf : (∏ r ∈ s, mgf (X r) P t) = ((1 - p) / (1 - a)) ^ s.card := by
      rw [Finset.prod_congr rfl fun r _ ↦ hmgf_r r, Finset.prod_const]
    rw [hprod_mgf] at hchern
    have hset_eq : {ω | a * (s.card : ℝ) ≤ (∑ r ∈ s, X r) ω} =
        {ω | a * (s.card : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} := by ext ω; simp [X]
    rw [hset_eq] at hchern
    refine hchern.trans (le_of_eq ?_)
    have h1pa_pos : 0 < (1 - p) / (1 - a) := div_pos h1p h1a
    have hpow_exp : ((1 - p) / (1 - a)) ^ s.card =
        Real.exp ((s.card : ℝ) * Real.log ((1 - p) / (1 - a))) := by
      rw [Real.exp_nat_mul, Real.exp_log h1pa_pos]
    rw [hpow_exp, ← Real.exp_add]
    congr 1
    have ht_decomp : t = Real.log (a / p) - Real.log ((1 - a) / (1 - p)) := by
      dsimp only [t, ratio]
      have hrew : (a * (1 - p)) / (p * (1 - a)) = (a / p) / ((1 - a) / (1 - p)) := by field_simp
      rw [hrew, Real.log_div (div_pos ha0 hp0).ne' (div_pos h1a h1p).ne']
    have hlog_inv : Real.log ((1 - p) / (1 - a)) = -Real.log ((1 - a) / (1 - p)) := by
      rw [← inv_div, Real.log_inv]
    have ha_ne1 : a ≠ 1 := ha1_lt.ne
    rw [ht_decomp, hlog_inv]
    simp only [klDivBernoulli, ha_ne1, ↓reduceIte]; ring

/-! ### Finite-Sample Union + Geometric Upper Bound on `longestQualityRun` -/

private lemma geom_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    ∑ d ∈ Finset.range M, q ^ d ≤ 1 / (1 - q) := by
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  rw [le_div_iff₀ h1q]
  have hid : (∑ d ∈ Finset.range M, q ^ d) * (1 - q) = 1 - q ^ M := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ, add_mul, ih, pow_succ]; ring
  rw [hid]
  linarith [pow_nonneg hq0 M]

/-- Union and geometric-series bound on the upper tail of `longestQualityRun` (`0 < p < a ≤ 1`,
`1 ≤ k`): `ℙ(R_n ≥ k) ≤ ((n + 1) / (1 - exp(-H(a, p)))) * exp(-k H(a, p))`. -/
theorem probReal_longestQualityRun_ge_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a : ℝ} {Y : ℕ → Ω → ℕ}
    (hp0 : 0 < p) (hpa : p < a) (ha1 : a ≤ 1)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    (hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hYp : ∀ i : ℕ, P.real {ω | Y i ω = 1} = p)
    (n : ℕ) {k : ℕ} (hk1 : 1 ≤ k) :
    P.real {ω | k ≤ longestQualityRun a (fun i : Fin n ↦ Y i.1 ω)} ≤
      (((n + 1 : ℕ) : ℝ) / (1 - Real.exp (-klDivBernoulli a p))) *
        Real.exp (-(k : ℝ) * klDivBernoulli a p) := by
  classical
  let H : ℝ := klDivBernoulli a p
  have hH_pos : 0 < H := klDivBernoulli_pos hp0 hpa ha1
  have hexp_lt1 : Real.exp (-H) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hH_pos)
  have h1exp_pos : 0 < 1 - Real.exp (-H) := sub_pos.mpr hexp_lt1
  by_cases hkn : k ≤ n
  · let E : ℕ → ℕ → Set Ω := fun j i ↦
      {ω | a * (j : ℝ) ≤ ∑ r ∈ Finset.Ico i (i + j), (Y r ω : ℝ)}
    have hsub : {ω | k ≤ longestQualityRun a (fun i : Fin n ↦ Y i.1 ω)} ⊆
        ⋃ j ∈ Finset.Icc k n, ⋃ i ∈ Finset.range (n + 1 - j), E j i := by
      intro ω hω
      change k ≤ longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) at hω
      set j := longestQualityRun a (fun i : Fin n ↦ Y i.1 ω)
      have hj_le : j ≤ n := Nat.findGreatest_le n
      have hj_ne0 : j ≠ 0 := by omega
      obtain ⟨i₀, hij, hsum⟩ : ∃ i : ℕ, ∃ _ : i + j ≤ n,
          a * (j : ℝ) ≤ ∑ r : Fin j, (Y (i + r.1) ω : ℝ) :=
        Nat.findGreatest_of_ne_zero (m := j) rfl hj_ne0
      have hi₀ : i₀ ∈ Finset.range (n + 1 - j) := Finset.mem_range.mpr (by omega)
      refine Set.mem_biUnion (Finset.mem_Icc.mpr ⟨hω, hj_le⟩) ?_
      refine Set.mem_biUnion hi₀ ?_
      change a * (j : ℝ) ≤ ∑ r ∈ Finset.Ico i₀ (i₀ + j), (Y r ω : ℝ)
      have hsum_eq : (∑ r : Fin j, (Y (i₀ + r.1) ω : ℝ)) =
          ∑ r ∈ Finset.Ico i₀ (i₀ + j), (Y r ω : ℝ) := by
        refine Finset.sum_bij (fun (r : Fin j) _ ↦ i₀ + r.1)
          (fun r _ ↦ Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          (fun _ _ _ _ h ↦ Fin.ext (by omega))
          (fun m hm ↦ ⟨⟨m - i₀, by rw [Finset.mem_Ico] at hm; omega⟩, Finset.mem_univ _,
            by rw [Finset.mem_Ico] at hm; dsimp; omega⟩)
          (fun _ _ ↦ rfl)
      rwa [← hsum_eq]
    have hmono : P.real {ω | k ≤ longestQualityRun a (fun i : Fin n ↦ Y i.1 ω)} ≤
        P.real (⋃ j ∈ Finset.Icc k n, ⋃ i ∈ Finset.range (n + 1 - j), E j i) :=
      measureReal_mono hsub (measure_ne_top P _)
    have hub1 : P.real (⋃ j ∈ Finset.Icc k n, ⋃ i ∈ Finset.range (n + 1 - j), E j i) ≤
        ∑ j ∈ Finset.Icc k n, ∑ i ∈ Finset.range (n + 1 - j), P.real (E j i) :=
      (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum fun j _ ↦ measureReal_biUnion_finset_le _ _)
    have hEj : ∀ j ∈ Finset.Icc k n,
        ∑ i ∈ Finset.range (n + 1 - j), P.real (E j i) ≤
          ((n + 1 : ℕ) : ℝ) * Real.exp (-(j : ℝ) * H) := by
      intro j _
      have hEi : ∀ i ∈ Finset.range (n + 1 - j), P.real (E j i) ≤ Real.exp (-(j : ℝ) * H) := by
        intro i _
        have hcard : (Finset.Ico i (i + j)).card = j := by simp
        have hb := probReal_sum_ge_le_exp_klDiv P hp0 hpa ha1 hY_meas hY_indep hY01 hYp
          (Finset.Ico i (i + j))
        rwa [hcard] at hb
      calc ∑ i ∈ Finset.range (n + 1 - j), P.real (E j i)
        _ ≤ ∑ _i ∈ Finset.range (n + 1 - j), Real.exp (-(j : ℝ) * H) := Finset.sum_le_sum hEi
        _ = ((n + 1 - j : ℕ) : ℝ) * Real.exp (-(j : ℝ) * H) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ((n + 1 : ℕ) : ℝ) * Real.exp (-(j : ℝ) * H) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact_mod_cast Nat.sub_le (n + 1) j
    have hsum_j : ∑ j ∈ Finset.Icc k n, ((n + 1 : ℕ) : ℝ) * Real.exp (-(j : ℝ) * H) ≤
        (((n + 1 : ℕ) : ℝ) / (1 - Real.exp (-H))) * Real.exp (-(k : ℝ) * H) := by
      rw [← Finset.mul_sum]
      have hreindex : ∑ j ∈ Finset.Icc k n, Real.exp (-(j : ℝ) * H) =
          Real.exp (-(k : ℝ) * H) *
            ∑ d ∈ Finset.range (n + 1 - k), (Real.exp (-H)) ^ d := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun j _ ↦ j - k)
          (fun j hj ↦ Finset.mem_range.mpr (by rw [Finset.mem_Icc] at hj; omega))
          (fun j₁ hj₁ j₂ hj₂ h ↦ by rw [Finset.mem_Icc] at hj₁ hj₂; omega)
          (fun d hd ↦ ⟨k + d, Finset.mem_Icc.mpr
            ⟨by omega, by rw [Finset.mem_range] at hd; omega⟩, by omega⟩) ?_
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        have hjk : (j : ℝ) = (k : ℝ) + ((j - k : ℕ) : ℝ) := by
          exact_mod_cast (Nat.add_sub_of_le hj.1).symm
        rw [hjk]; ring
      rw [hreindex]
      have hgeom := geom_sum_le_inv_one_sub (Real.exp_pos (-H)).le hexp_lt1 (n + 1 - k)
      calc ((n + 1 : ℕ) : ℝ) *
            (Real.exp (-(k : ℝ) * H) * ∑ d ∈ Finset.range (n + 1 - k), Real.exp (-H) ^ d)
        _ ≤ ((n + 1 : ℕ) : ℝ) * (Real.exp (-(k : ℝ) * H) * (1 / (1 - Real.exp (-H)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left hgeom (Real.exp_pos _).le
        _ = (((n + 1 : ℕ) : ℝ) / (1 - Real.exp (-H))) * Real.exp (-(k : ℝ) * H) := by ring
    exact hmono.trans (hub1.trans ((Finset.sum_le_sum hEj).trans hsum_j))
  · have hemp : {ω | k ≤ longestQualityRun a (fun i : Fin n ↦ Y i.1 ω)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact (Nat.findGreatest_le n).trans_lt (Nat.lt_of_not_ge hkn)
    rw [hemp, measureReal_empty]
    positivity

/-! ### Elementary `ℕ`-Binomial Lower Bound and Disjoint-Block Failure Bound -/

/-- Elementary `ℕ` binomial mode inequality (`1 ≤ m < k`):
`k ^ k ≤ (k + 1) * (m ^ m * (k - m) ^ (k - m) * k.choose m)`. -/
private lemma pow_self_le_succ_mul_choose_pow {k m : ℕ} (_hm1 : 1 ≤ m) (hmk : m < k) :
    k ^ k ≤ (k + 1) * (m ^ m * (k - m) ^ (k - m) * k.choose m) := by
  let G : ℕ → ℕ := fun r ↦ m ^ r * (k - m) ^ (k - r) * k.choose r
  have hadj : ∀ r < k, G r * ((k - r) * m) = G (r + 1) * ((r + 1) * (k - m)) := by
    intro r hr
    have hsub : k - r = (k - (r + 1)) + 1 := by omega
    have hch := Nat.choose_succ_right_eq k r
    dsimp only [G]
    calc (m ^ r * (k - m) ^ (k - r) * k.choose r) * ((k - r) * m)
      _ = (m ^ r * m) * (k - m) ^ (k - r) * (k.choose r * (k - r)) := by ring
      _ = m ^ (r + 1) * ((k - m) ^ (k - (r + 1)) * (k - m)) *
            (k.choose (r + 1) * (r + 1)) := by
        rw [← pow_succ m r, ← hch, hsub, pow_succ (k - m) (k - (r + 1))]
      _ = (m ^ (r + 1) * (k - m) ^ (k - (r + 1)) * k.choose (r + 1)) *
            ((r + 1) * (k - m)) := by ring
  have hle_left : ∀ d r : ℕ, r + d = m → G r ≤ G m := by
    intro d
    induction d with
    | zero => intro r hr; simp [← hr]
    | succ d ih =>
      intro r hr
      have hr_lt_k : r < k := by omega
      have hstep : G r ≤ G (r + 1) := by
        have hpos : 0 < (r + 1) * (k - m) :=
          Nat.mul_pos (Nat.succ_pos r) (Nat.sub_pos_of_lt hmk)
        refine Nat.le_of_mul_le_mul_right ?_ hpos
        have hcoef : (r + 1) * (k - m) ≤ (k - r) * m := by
          calc (r + 1) * (k - m)
            _ ≤ m * (k - m) := Nat.mul_le_mul_right _ (by omega)
            _ ≤ m * (k - r) := Nat.mul_le_mul_left _ (Nat.sub_le_sub_left (by omega) k)
            _ = (k - r) * m := Nat.mul_comm _ _
        calc G r * ((r + 1) * (k - m))
          _ ≤ G r * ((k - r) * m) := Nat.mul_le_mul_left _ hcoef
          _ = G (r + 1) * ((r + 1) * (k - m)) := hadj r hr_lt_k
      exact hstep.trans (ih (r + 1) (by omega))
  have hle_right : ∀ d : ℕ, m + d ≤ k → G (m + d) ≤ G m := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
      have hmd_lt_k : m + d < k := by omega
      have hstep : G (m + d + 1) ≤ G (m + d) := by
        have hpos : 0 < (m + d + 1) * (k - m) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt hmk)
        refine Nat.le_of_mul_le_mul_right ?_ hpos
        have hcoef : (k - (m + d)) * m ≤ (m + d + 1) * (k - m) := by
          calc (k - (m + d)) * m
            _ ≤ (k - m) * m := Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (by omega) k)
            _ ≤ (k - m) * (m + d + 1) := Nat.mul_le_mul_left _ (by omega)
            _ = (m + d + 1) * (k - m) := Nat.mul_comm _ _
        calc G (m + d + 1) * ((m + d + 1) * (k - m))
          _ = G (m + d) * ((k - (m + d)) * m) := (hadj (m + d) hmd_lt_k).symm
          _ ≤ G (m + d) * ((m + d + 1) * (k - m)) := Nat.mul_le_mul_left _ hcoef
      have heq_add : m + (d + 1) = m + d + 1 := by omega
      rw [heq_add]
      exact hstep.trans (ih (by omega))
  have hall_le : ∀ r ∈ Finset.range (k + 1), G r ≤ G m := by
    intro r hr
    rw [Finset.mem_range] at hr
    rcases le_or_gt r m with hrm | hmr
    · exact hle_left (m - r) r (by omega)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmr.le
      exact hle_right d (by omega)
  have hsum_eq : k ^ k = ∑ r ∈ Finset.range (k + 1), G r := by
    have hmk_add : m + (k - m) = k := Nat.add_sub_of_le hmk.le
    calc k ^ k
      _ = (m + (k - m)) ^ k := by rw [hmk_add]
      _ = ∑ r ∈ Finset.range (k + 1), G r := add_pow m (k - m) k
  calc k ^ k
    _ = ∑ r ∈ Finset.range (k + 1), G r := hsum_eq
    _ ≤ ∑ _r ∈ Finset.range (k + 1), G m := Finset.sum_le_sum hall_le
    _ = (k + 1) * G m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Lower tail bound for a finite sum of independent `Bernoulli(p)` `{0, 1}` variables at an
integer threshold `1 ≤ m < |s|` (`0 < p < 1`):
`ℙ(∑_{r ∈ s} Y_r ≥ m) ≥ (1 / (|s| + 1)) * exp(-|s| H(m / |s|, p))`. -/
theorem probReal_sum_ge_ge_klDiv_nat
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} {Y : ℕ → Ω → ℕ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    (hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hYp : ∀ i : ℕ, P.real {ω | Y i ω = 1} = p)
    (s : Finset ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hms : m < s.card) :
    (1 / ((s.card : ℝ) + 1)) *
        Real.exp (-(s.card : ℝ) * klDivBernoulli ((m : ℝ) / (s.card : ℝ)) p) ≤
      P.real {ω | (m : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} := by
  classical
  set k := s.card
  have hk_pos : 0 < k := by omega
  have h1p : 0 < 1 - p := sub_pos.mpr hp1
  have hY_ae : ∀ i : ℕ, AEMeasurable (Y i) P := fun i ↦ (hY_meas i).aemeasurable
  let C : Finset ℕ → Set Ω := fun t ↦
    {ω | (∀ r ∈ t, Y r ω = 1) ∧ (∀ r ∈ s \ t, Y r ω = 0)}
  have hC_meas : ∀ t ∈ s.powersetCard m, MeasurableSet (C t) := by
    intro t _
    have h1 : MeasurableSet {ω | ∀ r ∈ t, Y r ω = 1} := by
      have heq : {ω | ∀ r ∈ t, Y r ω = 1} = ⋂ r ∈ t, Y r ⁻¹' {1} := by ext ω; simp
      rw [heq]; exact MeasurableSet.biInter t.countable_toSet fun r _ ↦ (hY_meas r) .of_discrete
    have h2 : MeasurableSet {ω | ∀ r ∈ s \ t, Y r ω = 0} := by
      have heq : {ω | ∀ r ∈ s \ t, Y r ω = 0} = ⋂ r ∈ s \ t, Y r ⁻¹' {0} := by ext ω; simp
      rw [heq]
      exact MeasurableSet.biInter (s \ t).countable_toSet fun r _ ↦ (hY_meas r) .of_discrete
    exact h1.inter h2
  have hC_disj : Set.PairwiseDisjoint (↑(s.powersetCard m)) C := by
    intro t₁ ht₁ t₂ ht₂ hne
    rw [Finset.mem_coe, Finset.mem_powersetCard] at ht₁ ht₂
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω1 hω2
    apply hne
    ext r
    constructor <;> intro hr
    · by_contra hnot2
      have hrs : r ∈ s \ t₂ := Finset.mem_sdiff.mpr ⟨ht₁.1 hr, hnot2⟩
      have h1 := hω1.1 r hr; have h0 := hω2.2 r hrs; omega
    · by_contra hnot1
      have hrs : r ∈ s \ t₁ := Finset.mem_sdiff.mpr ⟨ht₂.1 hr, hnot1⟩
      have h1 := hω2.1 r hr; have h0 := hω1.2 r hrs; omega
  have hC_sub : (⋃ t ∈ s.powersetCard m, C t) ⊆ {ω | (m : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} := by
    intro ω hω
    obtain ⟨t, ht, hCt⟩ := Set.mem_iUnion₂.mp hω
    rw [Finset.mem_powersetCard] at ht
    change (m : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)
    rw [← Finset.sum_sdiff ht.1]
    have hsum_t : ∑ r ∈ t, (Y r ω : ℝ) = (m : ℝ) := by
      have h1 : ∑ r ∈ t, (Y r ω : ℝ) = ∑ _r ∈ t, (1 : ℝ) :=
        Finset.sum_congr rfl fun r hr ↦ by simp [hCt.1 r hr]
      rw [h1, Finset.sum_const, ht.2, nsmul_eq_mul, mul_one]
    have hsum_sd : ∑ r ∈ s \ t, (Y r ω : ℝ) = 0 :=
      Finset.sum_eq_zero fun r hr ↦ by simp [hCt.2 r hr]
    linarith
  have hC_prob : ∀ t ∈ s.powersetCard m, P.real (C t) = p ^ m * (1 - p) ^ (k - m) := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    let g : Finset ℕ → ℕ → ℕ → ℝ := fun u r v ↦
      if r ∈ u then (if v = 1 then 1 else 0) else (if v = 0 then 1 else 0)
    have hprod01 : ∀ ω, ∏ r ∈ s, g t r (Y r ω) = 0 ∨ ∏ r ∈ s, g t r (Y r ω) = 1 := by
      intro ω
      by_cases hmem : ω ∈ C t
      · refine Or.inr (Finset.prod_eq_one fun r hr ↦ ?_)
        by_cases hrt : r ∈ t
        · simp [g, hrt, hmem.1 r hrt]
        · simp [g, hrt, hmem.2 r (Finset.mem_sdiff.mpr ⟨hr, hrt⟩)]
      · refine Or.inl ?_
        change ¬((∀ r ∈ t, Y r ω = 1) ∧ (∀ r ∈ s \ t, Y r ω = 0)) at hmem
        push Not at hmem
        by_cases h1 : ∀ r ∈ t, Y r ω = 1
        · obtain ⟨r₀, hr₀, hne0⟩ := hmem h1
          have hr₀s : r₀ ∈ s := (Finset.mem_sdiff.mp hr₀).1
          have hr₀t : r₀ ∉ t := (Finset.mem_sdiff.mp hr₀).2
          exact Finset.prod_eq_zero hr₀s (by simp [g, hr₀t, hne0])
        · push Not at h1
          obtain ⟨r₀, hr₀t, hne1⟩ := h1
          exact Finset.prod_eq_zero (ht.1 hr₀t) (by simp [g, hr₀t, hne1])
    have hind_eq : (C t).indicator (1 : Ω → ℝ) = fun ω ↦ ∏ r ∈ s, g t r (Y r ω) := by
      ext ω
      by_cases hmem : ω ∈ C t
      · rw [Set.indicator_of_mem hmem, Pi.one_apply]
        refine (Finset.prod_eq_one fun r hr ↦ ?_).symm
        by_cases hrt : r ∈ t
        · simp [g, hrt, hmem.1 r hrt]
        · simp [g, hrt, hmem.2 r (Finset.mem_sdiff.mpr ⟨hr, hrt⟩)]
      · rw [Set.indicator_of_notMem hmem]
        rcases hprod01 ω with h0 | h1
        · exact h0.symm
        · exfalso; apply hmem
          refine ⟨fun r hrt ↦ ?_, fun r hrsd ↦ ?_⟩
          · by_contra hne1
            have hz : ∏ r' ∈ s, g t r' (Y r' ω) = 0 :=
              Finset.prod_eq_zero (ht.1 hrt) (by simp [g, hrt, hne1])
            linarith
          · by_contra hne0
            have hrs : r ∈ s := (Finset.mem_sdiff.mp hrsd).1
            have hrt : r ∉ t := (Finset.mem_sdiff.mp hrsd).2
            have hz : ∏ r' ∈ s, g t r' (Y r' ω) = 0 :=
              Finset.prod_eq_zero hrs (by simp [g, hrt, hne0])
            linarith
    rw [← integral_indicator_one (hC_meas t (Finset.mem_powersetCard.mpr ht)), hind_eq,
      integral_finset_prod_indep_nat hY_ae hY_indep s (g t), ← Finset.prod_sdiff ht.1]
    have hprod_t : ∏ r ∈ t, ∫ ω, g t r (Y r ω) ∂P = p ^ m := by
      have hfac : ∀ r ∈ t, ∫ ω, g t r (Y r ω) ∂P = p := by
        intro r hrt
        have hae_r : (fun ω ↦ g t r (Y r ω)) =ᵐ[P] fun ω ↦ (Y r ω : ℝ) := by
          filter_upwards [hY01 r] with ω hω
          rcases hω with h | h <;> simp [g, hrt, h]
        rw [integral_congr_ae hae_r, integral_natCast_of_ae_zero_or_one (hY_ae r) (hY01 r), hYp r]
      rw [Finset.prod_congr rfl hfac, Finset.prod_const, ht.2]
    have hprod_sd : ∏ r ∈ s \ t, ∫ ω, g t r (Y r ω) ∂P = (1 - p) ^ (k - m) := by
      have hfac : ∀ r ∈ s \ t, ∫ ω, g t r (Y r ω) ∂P = 1 - p := by
        intro r hrsd
        have hrt : r ∉ t := (Finset.mem_sdiff.mp hrsd).2
        have hae_r : (fun ω ↦ g t r (Y r ω)) =ᵐ[P] fun ω ↦ (1 : ℝ) - (Y r ω : ℝ) := by
          filter_upwards [hY01 r] with ω hω
          rcases hω with h | h <;> simp [g, hrt, h]
        have hYr_int : Integrable (fun ω ↦ (Y r ω : ℝ)) P :=
          integrable_natCast_of_ae_zero_or_one (hY_ae r) (hY01 r)
        rw [integral_congr_ae hae_r, integral_sub (integrable_const 1) hYr_int,
          integral_const, probReal_univ, smul_eq_mul, one_mul,
          integral_natCast_of_ae_zero_or_one (hY_ae r) (hY01 r), hYp r]
      rw [Finset.prod_congr rfl hfac, Finset.prod_const, Finset.card_sdiff_of_subset ht.1, ht.2]
    rw [hprod_t, hprod_sd, mul_comm]
  have hprob_binom :
      (k.choose m : ℝ) * p ^ m * (1 - p) ^ (k - m) ≤
        P.real {ω | (m : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} := by
    calc (k.choose m : ℝ) * p ^ m * (1 - p) ^ (k - m)
      _ = ((s.powersetCard m).card : ℝ) * (p ^ m * (1 - p) ^ (k - m)) := by
        rw [Finset.card_powersetCard]; ring
      _ = ∑ t ∈ s.powersetCard m, P.real (C t) := by
        rw [Finset.sum_congr rfl hC_prob, Finset.sum_const, nsmul_eq_mul]
      _ = P.real (⋃ t ∈ s.powersetCard m, C t) :=
        (measureReal_biUnion_finset hC_disj hC_meas).symm
      _ ≤ P.real {ω | (m : ℝ) ≤ ∑ r ∈ s, (Y r ω : ℝ)} :=
        measureReal_mono hC_sub (measure_ne_top P _)
  refine le_trans ?_ hprob_binom
  have hmode_real : ((k : ℝ) ^ k) ≤
      ((k : ℝ) + 1) * ((m : ℝ) ^ m * ((k - m : ℕ) : ℝ) ^ (k - m) * (k.choose m : ℝ)) := by
    exact_mod_cast pow_self_le_succ_mul_choose_pow hm1 hms
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm1
  have hkm_pos : (0 : ℝ) < ((k - m : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hms)
  have hk_r_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
  have hchoose_lo : (1 / ((k : ℝ) + 1)) *
      ((k : ℝ) ^ k / ((m : ℝ) ^ m * ((k - m : ℕ) : ℝ) ^ (k - m))) ≤ (k.choose m : ℝ) := by
    rw [one_div_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
    linarith
  let x : ℝ := (m : ℝ) / (k : ℝ)
  have hx_pos : 0 < x := div_pos hm_pos hk_r_pos
  have h1x_eq : 1 - x = ((k - m : ℕ) : ℝ) / (k : ℝ) := by
    dsimp only [x]
    have hkm_cast : ((k - m : ℕ) : ℝ) = (k : ℝ) - (m : ℝ) := Nat.cast_sub hms.le
    rw [hkm_cast]; field_simp
  have h1x_pos : 0 < 1 - x := h1x_eq ▸ div_pos hkm_pos hk_r_pos
  have hexp_kl : Real.exp (-(k : ℝ) * klDivBernoulli x p) =
      ((k : ℝ) ^ k / ((m : ℝ) ^ m * ((k - m : ℕ) : ℝ) ^ (k - m))) *
        p ^ m * (1 - p) ^ (k - m) := by
    have hlin : -(k : ℝ) * klDivBernoulli x p =
        (m : ℝ) * Real.log (p / x) + ((k - m : ℕ) : ℝ) * Real.log ((1 - p) / (1 - x)) := by
      have hx_ne1 : x ≠ 1 := by linarith [h1x_pos]
      simp only [klDivBernoulli, hx_ne1, ↓reduceIte]
      have hkx : (k : ℝ) * x = (m : ℝ) := by dsimp only [x]; field_simp
      have hk1x : (k : ℝ) * (1 - x) = ((k - m : ℕ) : ℝ) := by rw [h1x_eq]; field_simp
      have hl1 : Real.log (p / x) = -Real.log (x / p) := by rw [← inv_div, Real.log_inv]
      have hl2 : Real.log ((1 - p) / (1 - x)) = -Real.log ((1 - x) / (1 - p)) := by
        rw [← inv_div, Real.log_inv]
      rw [hl1, hl2]
      calc -(k : ℝ) * (x * Real.log (x / p) + (1 - x) * Real.log ((1 - x) / (1 - p)))
        _ = -((k : ℝ) * x) * Real.log (x / p) -
              ((k : ℝ) * (1 - x)) * Real.log ((1 - x) / (1 - p)) := by ring
        _ = (m : ℝ) * -Real.log (x / p) +
              ((k - m : ℕ) : ℝ) * -Real.log ((1 - x) / (1 - p)) := by rw [hkx, hk1x]; ring
    rw [hlin, Real.exp_add, Real.exp_nat_mul, Real.exp_log (div_pos hp0 hx_pos),
      Real.exp_nat_mul, Real.exp_log (div_pos h1p h1x_pos)]
    have hpx : p / x = p * (k : ℝ) / (m : ℝ) := by dsimp only [x]; field_simp
    have h1px : (1 - p) / (1 - x) = (1 - p) * (k : ℝ) / ((k - m : ℕ) : ℝ) := by
      rw [h1x_eq]; field_simp
    rw [hpx, h1px, div_pow, div_pow, mul_pow, mul_pow]
    have hk_pow : (k : ℝ) ^ m * (k : ℝ) ^ (k - m) = (k : ℝ) ^ k := by
      rw [← pow_add, Nat.add_sub_of_le hms.le]
    field_simp
    linarith [hk_pow]
  rw [hexp_kl]
  calc (1 / ((k : ℝ) + 1)) *
        (((k : ℝ) ^ k / ((m : ℝ) ^ m * ((k - m : ℕ) : ℝ) ^ (k - m))) *
          p ^ m * (1 - p) ^ (k - m))
    _ = ((1 / ((k : ℝ) + 1)) *
          ((k : ℝ) ^ k / ((m : ℝ) ^ m * ((k - m : ℕ) : ℝ) ^ (k - m)))) *
          (p ^ m * (1 - p) ^ (k - m)) := by ring
    _ ≤ (k.choose m : ℝ) * (p ^ m * (1 - p) ^ (k - m)) :=
      mul_le_mul_of_nonneg_right hchoose_lo (by positivity)
    _ = (k.choose m : ℝ) * p ^ m * (1 - p) ^ (k - m) := by ring

/-- Helper sub-σ-algebra of coordinate `r` (defined as a `private def`, never an instance). -/
@[instance_reducible]
private def coordMS {Ω : Type*} [MeasurableSpace Ω] (Y : ℕ → Ω → ℕ) (r : ℕ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (Y r) inferInstance

/-- Disjoint-block failure upper bound: if `B * k ≤ n`, `1 ≤ k`, and every disjoint block of length
`k` among the first `B` blocks has quality-`a` success probability at least `q`, then
`ℙ(R_n < k) ≤ exp(-B q)`. -/
theorem probReal_longestQualityRun_lt_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a q : ℝ} {Y : ℕ → Ω → ℕ}
    (hY_meas : ∀ i : ℕ, Measurable (Y i))
    (hY_indep : iIndepFun Y P)
    {n B k : ℕ} (hk1 : 1 ≤ k) (hBkn : B * k ≤ n)
    (hq_block : ∀ b < B,
      q ≤ P.real {ω | a * (k : ℝ) ≤ ∑ r ∈ Finset.Ico (b * k) (b * k + k), (Y r ω : ℝ)}) :
    P.real {ω | longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) < k} ≤
      Real.exp (-(B : ℝ) * q) := by
  let G : ℕ → Set Ω := fun b ↦
    {ω | a * (k : ℝ) ≤ ∑ r ∈ Finset.Ico (b * k) (b * k + k), (Y r ω : ℝ)}
  let F : ℕ → Set Ω := fun b ↦ (G b)ᶜ
  have hle_m : ∀ r : ℕ, coordMS Y r ≤ ‹MeasurableSpace Ω› :=
    fun r ↦ (hY_meas r).comap_le
  have hG_meas_sub : ∀ b : ℕ,
      MeasurableSet[⨆ r ∈ Set.Ico (b * k) (b * k + k), coordMS Y r] (G b) := by
    intro b
    have hsum_meas : @Measurable Ω ℝ (⨆ r ∈ Set.Ico (b * k) (b * k + k), coordMS Y r)
        inferInstance (fun ω ↦ ∑ r ∈ Finset.Ico (b * k) (b * k + k), (Y r ω : ℝ)) := by
      refine Finset.measurable_sum (Finset.Ico (b * k) (b * k + k)) fun r hr ↦ ?_
      have hr_set : r ∈ Set.Ico (b * k) (b * k + k) := Finset.mem_Ico.mp hr
      have hYr : @Measurable Ω ℕ (coordMS Y r) inferInstance (Y r) :=
        measurable_iff_comap_le.mpr le_rfl
      have hcast_meas : Measurable (Nat.cast : ℕ → ℝ) := .of_discrete
      exact hcast_meas.comp (hYr.mono (le_biSup (coordMS Y) hr_set) le_rfl)
    exact hsum_meas measurableSet_Ici
  have hF_meas_sub : ∀ b : ℕ,
      MeasurableSet[⨆ r ∈ Set.Ico (b * k) (b * k + k), coordMS Y r] (F b) :=
    fun b ↦ (hG_meas_sub b).compl
  have hG_meas : ∀ b : ℕ, MeasurableSet (G b) := by
    intro b
    have hle_sup : (⨆ r ∈ Set.Ico (b * k) (b * k + k), coordMS Y r) ≤ ‹MeasurableSpace Ω› :=
      iSup₂_le fun r _ ↦ hle_m r
    exact hle_sup _ (hG_meas_sub b)
  have hprod_inter : ∀ m : ℕ,
      (MeasurableSet[⨆ r ∈ Set.Ico 0 (m * k), coordMS Y r] (⋂ b ∈ Finset.range m, F b)) ∧
        P (⋂ b ∈ Finset.range m, F b) = ∏ b ∈ Finset.range m, P (F b) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, by simp⟩
      simp only [Finset.range_zero, Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
      exact MeasurableSet.univ
    | succ m ih =>
      have hinter_eq : (⋂ b ∈ Finset.range (m + 1), F b) =
          (⋂ b ∈ Finset.range m, F b) ∩ F m := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_range]
        constructor
        · intro h; exact ⟨fun b hb ↦ h b (by omega), h m (by omega)⟩
        · rintro ⟨h1, h2⟩ b hb
          rcases eq_or_lt_of_le (Nat.le_of_lt_succ hb) with rfl | hlt
          · exact h2
          · exact h1 b hlt
      rw [hinter_eq]
      have hle1 : (⨆ r ∈ Set.Ico 0 (m * k), coordMS Y r) ≤
          (⨆ r ∈ Set.Ico 0 ((m + 1) * k), coordMS Y r) :=
        biSup_mono fun r hr ↦ ⟨hr.1, hr.2.trans_le (by rw [Nat.succ_mul]; omega)⟩
      have hle2 : (⨆ r ∈ Set.Ico (m * k) (m * k + k), coordMS Y r) ≤
          (⨆ r ∈ Set.Ico 0 ((m + 1) * k), coordMS Y r) :=
        biSup_mono fun r hr ↦ ⟨Nat.zero_le r, by rw [Nat.succ_mul]; exact hr.2⟩
      have hm_next : MeasurableSet[⨆ r ∈ Set.Ico 0 ((m + 1) * k), coordMS Y r]
          ((⋂ b ∈ Finset.range m, F b) ∩ F m) :=
        (hle1 _ ih.1).inter (hle2 _ (hF_meas_sub m))
      have hdisj_ico : Disjoint (Set.Ico 0 (m * k)) (Set.Ico (m * k) (m * k + k)) := by
        rw [Set.disjoint_left]; intro r hr1 hr2; exact absurd hr2.1 (not_le.mpr hr1.2)
      have hind_blocks : Indep (⨆ r ∈ Set.Ico 0 (m * k), coordMS Y r)
          (⨆ r ∈ Set.Ico (m * k) (m * k + k), coordMS Y r) P :=
        indep_iSup_of_disjoint hle_m hY_indep hdisj_ico
      have hind_set := hind_blocks.indepSet_of_measurableSet ih.1 (hF_meas_sub m)
      refine ⟨hm_next, ?_⟩
      rw [hind_set.measure_inter_eq_mul, ih.2, Finset.prod_range_succ]
  have hsub : {ω | longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) < k} ⊆
      ⋂ b ∈ Finset.range B, F b := by
    intro ω hω
    simp only [Set.mem_iInter, Finset.mem_range]
    intro b hb hGb
    have hbkn : b * k + k ≤ n := by
      have : (b + 1) * k ≤ B * k := Nat.mul_le_mul_right k (by omega)
      rw [Nat.succ_mul] at this; omega
    have hk_le : k ≤ longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) := by
      classical
      refine Nat.le_findGreatest (by omega) ⟨b * k, hbkn, ?_⟩
      have hsum_eq : (∑ r : Fin k, (Y (b * k + r.1) ω : ℝ)) =
          ∑ r ∈ Finset.Ico (b * k) (b * k + k), (Y r ω : ℝ) := by
        refine Finset.sum_bij (fun (r : Fin k) _ ↦ b * k + r.1)
          (fun r _ ↦ Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
          (fun _ _ _ _ h ↦ Fin.ext (by omega))
          (fun m hm ↦ ⟨⟨m - b * k, by rw [Finset.mem_Ico] at hm; omega⟩, Finset.mem_univ _,
            by rw [Finset.mem_Ico] at hm; dsimp; omega⟩)
          (fun _ _ ↦ rfl)
      rw [hsum_eq]; exact hGb
    exact absurd hk_le (not_le.mpr hω)
  have hreal_prod : P.real (⋂ b ∈ Finset.range B, F b) =
      ∏ b ∈ Finset.range B, P.real (F b) := by
    rw [measureReal_def, (hprod_inter B).2]
    have haux : ∀ m : ℕ, (∏ b ∈ Finset.range m, P (F b)).toReal =
        ∏ b ∈ Finset.range m, P.real (F b) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_range_succ, Finset.prod_range_succ, ENNReal.toReal_mul, ih, measureReal_def]
    exact haux B
  have hFb_le : ∀ b ∈ Finset.range B, P.real (F b) ≤ Real.exp (-q) := by
    intro b hb
    rw [Finset.mem_range] at hb
    have hcompl : P.real (G b) + P.real (F b) = 1 := by
      simpa only [F, probReal_univ] using measureReal_add_measureReal_compl (μ := P) (hG_meas b)
    linarith [hq_block b hb, Real.add_one_le_exp (-q)]
  have hprod_le : ∀ m ≤ B, ∏ b ∈ Finset.range m, P.real (F b) ≤ (Real.exp (-q)) ^ m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, pow_succ]
      exact mul_le_mul (ih (by omega))
        (hFb_le m (Finset.mem_range.mpr (by omega))) measureReal_nonneg (by positivity)
  calc P.real {ω | longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) < k}
    _ ≤ P.real (⋂ b ∈ Finset.range B, F b) := measureReal_mono hsub (measure_ne_top P _)
    _ = ∏ b ∈ Finset.range B, P.real (F b) := hreal_prod
    _ ≤ (Real.exp (-q)) ^ B := hprod_le B le_rfl
    _ = Real.exp (-(B : ℝ) * q) := by rw [← Real.exp_nat_mul]; ring_nf

end SteinMethod
