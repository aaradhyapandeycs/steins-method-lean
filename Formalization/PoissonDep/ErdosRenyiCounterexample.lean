/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonDep.HeadRunAsymptotics
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw

/-!
# Refutation of Printed Theorem 4.9 (`ISSUE-4.9`)

In Section 4.2.1 (`SteinIntro.tex:2071-2078`), Nathan Ross states Theorem 4.9 (*Erdős–Rényi Law*)
under the hypotheses $a \in (0, 1]$ and $p \in [0, 1]$, omitting the rare-event regime hypothesis
$0 < p < a \le 1$ (from Erdős–Rényi 1970). When $0 < a \le p \le 1$, the full prefix of length $n$
has empirical average tending to $p > a$ almost surely (for $a < p$) by the strong law of large
numbers, so $R_n = n$ eventually almost surely and $R_n / \log(n) \to +\infty$, whereas the printed
right-hand side $1 / H(a, p)$ is finite (`klDivBernoulli (1/4) (1/2) > 0`).

This file defines the literal printed statement `Thm4_9_printed` and machine-checks
`not_Thm4_9_printed` via `Measure.infinitePi` and `ProbabilityTheory.strong_law_ae_real` at
$a = 1/4$, $p = 1/2$.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-- Literal printed statement of Theorem 4.9 (`[\ER\ Law]`, `SteinIntro.tex:2071-2078`;
`ISSUE-4.9`), quantified over $a \in (0, 1]$ and $p \in [0, 1]$ without $0 < p < a$. -/
def Thm4_9_printed : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a : ℝ} {Y : ℕ → Ω → ℕ},
    0 < a → a ≤ 1 →
    0 ≤ p → p ≤ 1 →
    (∀ i : ℕ, AEMeasurable (Y i) P) →
    iIndepFun Y P →
    (∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
    (∀ i : ℕ, P.real {ω | Y i ω = 1} = p) →
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦
          (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ))
        atTop
        (𝓝 (1 / klDivBernoulli a p))

/-- Fair coin probability measure on `Bool` assigning mass `1 / 2` to `true` and `false`. -/
private noncomputable def fairCoinBool : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

private instance isProbabilityMeasure_fairCoinBool : IsProbabilityMeasure fairCoinBool := by
  refine ⟨?_⟩
  simp only [fairCoinBool, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ .univ,
    Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

private lemma fairCoinBool_singleton_true : fairCoinBool {true} = 1 / 2 := by
  simp [fairCoinBool, Measure.dirac_apply' _ .of_discrete]

/-- **Refutation of printed Theorem 4.9** (`ISSUE-4.9`, `SteinIntro.tex:2071-2078`): at
$a = 1/4 \in (0, 1]$ and $p = 1/2 \in [0, 1]$ on an infinite product of fair coin tosses,
$R_n = n$ eventually almost surely by the strong law of large numbers, so $R_n / \log(n)$ diverges
rather than converging to $1 / H(1/4, 1/2) \in \mathbb{R}$. -/
theorem not_Thm4_9_printed : ¬ Thm4_9_printed := by
  intro hprint
  let μ : Measure (ℕ → Bool) := Measure.infinitePi fun _ : ℕ ↦ fairCoinBool
  let P : Measure (PUnit × (ℕ → Bool)) := (Measure.dirac PUnit.unit).prod μ
  let coord : ℕ → PUnit × (ℕ → Bool) → Bool := fun i ω ↦ ω.2 i
  let Y : ℕ → PUnit × (ℕ → Bool) → ℕ := fun i ω ↦ if coord i ω then 1 else 0
  have hcoord_meas : ∀ i : ℕ, Measurable (coord i) :=
    fun i ↦ (measurable_pi_apply i).comp measurable_snd
  have hY_meas : ∀ i : ℕ, Measurable (Y i) :=
    fun i ↦ (Measurable.of_discrete : Measurable fun b : Bool ↦ if b then (1 : ℕ) else 0).comp
      (hcoord_meas i)
  have hmap_coord : ∀ i : ℕ, P.map (coord i) = fairCoinBool := by
    intro i
    have heq : coord i = (fun x : ℕ → Bool ↦ x i) ∘ Prod.snd := rfl
    rw [heq, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul]
    exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ fairCoinBool) i
  have hcoord_indep : iIndepFun coord P := by
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _
    have hpre : (⋂ i ∈ S, coord i ⁻¹' sets i) =
        Set.univ ×ˢ Set.pi S sets := by
      ext ⟨u, x⟩
      simp [coord]
    rw [hpre, Measure.prod_prod, measure_univ, one_mul,
      Measure.infinitePi_pi _ fun i _ ↦ .of_discrete]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← Measure.map_apply (hcoord_meas i) .of_discrete, hmap_coord i]
  have hY_indep : iIndepFun Y P :=
    hcoord_indep.comp (fun _ b ↦ if b then (1 : ℕ) else 0) (fun _ ↦ .of_discrete)
  have hY01 : ∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1 := by
    intro i
    refine Eventually.of_forall fun ω ↦ ?_
    dsimp only [Y]
    cases coord i ω <;> simp
  have hY_prob : ∀ i : ℕ, P.real {ω | Y i ω = 1} = 1 / 2 := by
    intro i
    have hset : {ω : PUnit × (ℕ → Bool) | Y i ω = 1} = coord i ⁻¹' {true} := by
      ext ω
      dsimp only [Y]
      cases coord i ω <;> simp
    rw [hset, measureReal_def, ← Measure.map_apply (hcoord_meas i) .of_discrete,
      hmap_coord i, fairCoinBool_singleton_true]
    norm_num
  -- Apply printed Theorem 4.9 at `a = 1/4, p = 1/2`
  have ha0 : (0 : ℝ) < 1 / 4 := by norm_num
  have ha1 : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hp0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hae_print := hprint P ha0 ha1 hp0 hp1 (fun i ↦ (hY_meas i).aemeasurable)
    hY_indep hY01 hY_prob
  -- Apply the strong law of large numbers to `X i ω := (Y i ω : ℝ)`
  let X : ℕ → PUnit × (ℕ → Bool) → ℝ := fun i ω ↦ (Y i ω : ℝ)
  have hcast_meas : Measurable (Nat.cast : ℕ → ℝ) := .of_discrete
  have hX_meas : ∀ i : ℕ, Measurable (X i) := fun i ↦ hcast_meas.comp (hY_meas i)
  have hX_indep : iIndepFun X P := hY_indep.comp (fun _ ↦ Nat.cast) (fun _ ↦ hcast_meas)
  have hX_pair : Pairwise (Function.onFun (· ⟂ᵢ[P] ·) X) := by
    intro i j hij
    have h := hX_indep.indepFun_finsetProd_of_notMem hX_meas (s := {i}) (i := j)
      (by simp [hij.symm])
    simpa only [Finset.prod_singleton] using h
  have hX_ident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P := by
    intro i
    have hφ : Measurable (fun b : Bool ↦ ((if b then (1 : ℕ) else 0 : ℕ) : ℝ)) := .of_discrete
    refine
      { aemeasurable_fst := (hX_meas i).aemeasurable
        aemeasurable_snd := (hX_meas 0).aemeasurable
        map_eq := ?_ }
    have hXi : X i = (fun b : Bool ↦ ((if b then (1 : ℕ) else 0 : ℕ) : ℝ)) ∘ coord i := rfl
    have hX0 : X 0 = (fun b : Bool ↦ ((if b then (1 : ℕ) else 0 : ℕ) : ℝ)) ∘ coord 0 := rfl
    rw [hXi, hX0, ← Measure.map_map hφ (hcoord_meas i), ← Measure.map_map hφ (hcoord_meas 0),
      hmap_coord i, hmap_coord 0]
  have hX0_int : Integrable (X 0) P :=
    integrable_natCast_of_ae_zero_or_one (hY_meas 0).aemeasurable (hY01 0)
  have hX0_mean : ∫ ω, X 0 ω ∂P = 1 / 2 := by
    rw [integral_natCast_of_ae_zero_or_one (hY_meas 0).aemeasurable (hY01 0), hY_prob 0]
  have hae_slln := strong_law_ae_real X hX0_int hX_pair hX_ident
  rw [hX0_mean] at hae_slln
  -- Combine both full-measure events on the probability space `P`
  obtain ⟨ω, hω_print, hω_slln⟩ := (hae_print.and hae_slln).exists
  have hev_avg : ∀ᶠ n : ℕ in atTop,
      (1 / 4 : ℝ) < (∑ i ∈ Finset.range n, X i ω) / (n : ℝ) :=
    (tendsto_order.mp hω_slln).1 (1 / 4) (by norm_num)
  have hev_Rn : ∀ᶠ n : ℕ in atTop,
      longestQualityRun (1 / 4) (fun i : Fin n ↦ Y i.1 ω) = n := by
    filter_upwards [hev_avg, eventually_ge_atTop 1] with n hn_avg hn1
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
    have hsum : (1 / 4 : ℝ) * (n : ℝ) ≤ ∑ r : Fin n, (Y r.1 ω : ℝ) := by
      have hmul : (1 / 4 : ℝ) * (n : ℝ) < ∑ i ∈ Finset.range n, X i ω :=
        (lt_div_iff₀ hn_pos).mp hn_avg
      rw [Fin.sum_univ_eq_sum_range (fun k ↦ (Y k ω : ℝ)) n]
      exact hmul.le
    classical
    refine le_antisymm (Nat.findGreatest_le n) ?_
    refine Nat.le_findGreatest le_rfl ⟨0, by omega, ?_⟩
    simpa only [zero_add] using hsum
  have htend_div : Tendsto (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ)) atTop
      (𝓝 (1 / klDivBernoulli (1 / 4) (1 / 2))) := by
    refine hω_print.congr' ?_
    filter_upwards [hev_Rn] with n hn
    rw [hn]
  -- Yet `(log n / n) → 0`, so `(log n / n) * (n / log n) → 0`, contradicting `= 1` for `n ≥ 2`
  have hprod0 : Tendsto
      (fun n : ℕ ↦ (Real.log (n : ℝ) / (n : ℝ)) * ((n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 (0 * (1 / klDivBernoulli (1 / 4) (1 / 2)))) :=
    tendsto_log_div_natCast_atTop.mul htend_div
  rw [zero_mul] at hprod0
  have hprod1 : Tendsto
      (fun n : ℕ ↦ (Real.log (n : ℝ) / (n : ℝ)) * ((n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn2
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hlog_ne : Real.log (n : ℝ) ≠ 0 := hlog_pos.ne'
    field_simp
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hprod1 hprod0
  norm_num at h10

end SteinMethod
