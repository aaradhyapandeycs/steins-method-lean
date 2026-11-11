/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Exchangeable.AntiVoterGraph
import Formalization.Exchangeable.Basic
import Formalization.Exchangeable.SteinPairBound
import Formalization.Normal.WassersteinBound
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Anti-Voter Model Stein Pair and Normal Approximation (`Formalization.Exchangeable.AntiVoter`)

This module proves the probabilistic anti-voter model results from Section 3.3.1 of Nathan Ross,
*"Fundamentals of Stein's method"* (`SteinIntro.tex:1099-1219`):

* `antiVoter_stationary_mean_zero` (`SteinIntro.tex:1107-1113`, `1212-1219`): under any stationary
  distribution of the anti-voter chain on a nonempty $r$-regular graph ($r > 0$), the total spin
  has mean zero.
* `antiVoter_variance_bounds` (Lemma 3.10, `SteinIntro.tex:1208-1219`): under any stationary
  distribution on an $r$-regular graph ($r > 0$), the variance $\sigma^2$ of the total spin
  satisfies $2\kappa(G)/r \le \sigma^2 \le |V|$.
* `antiVoter_steinPair_and_wasserstein_bound` (Theorem 3.8, `\label{thm52}`,
  `SteinIntro.tex:1114-1207`): $(W, W')$ is a $(2/n)$-Stein pair and satisfies the Wasserstein
  normal approximation bound $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
  \frac{4n}{3\sigma^3} + \frac{\sqrt{\operatorname{Var}(Q)}}{r\sigma^2\sqrt{2\pi}}$.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### Finite-State Expectation and Stationarity Helpers -/

private lemma integrable_comp_of_fintype
    {α Ω : Type*} [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {Y : Ω → α} (hY : Measurable Y) (g : α → ℝ) :
    Integrable (fun ω ↦ g (Y ω)) P := by
  have := Fintype.ofFinite α
  exact Integrable.of_bound ((measurable_of_finite g).comp hY).aestronglyMeasurable
    (∑ y : α, |g y|)
    (ae_of_all P fun ω ↦ by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun y _ ↦ abs_nonneg (g y)) (Finset.mem_univ (Y ω)))

private lemma memLp_two_comp_of_fintype
    {α Ω : Type*} [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {Y : Ω → α} (hY : Measurable Y) (g : α → ℝ) :
    MemLp (fun ω ↦ g (Y ω)) 2 P :=
  (memLp_two_iff_integrable_sq ((measurable_of_finite g).comp hY).aestronglyMeasurable).mpr
    (integrable_comp_of_fintype P hY (fun x ↦ g x ^ 2))

private lemma integral_comp_eq_sum_map_real
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → α} (hY : Measurable Y) (g : α → ℝ) :
    ∫ ω, g (Y ω) ∂P = ∑ x : α, (P.map Y).real {x} * g x := by
  have : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr ‹_›
  have hg_int : Integrable g (P.map Y) := integrable_comp_of_fintype (P.map Y) measurable_id g
  calc
    ∫ ω, g (Y ω) ∂P = ∫ x, g x ∂(P.map Y) :=
      (integral_map hY.aemeasurable (measurable_of_finite g).aestronglyMeasurable).symm
    _ = ∑ x : α, (P.map Y).real {x} • g x := integral_fintype hg_int
    _ = ∑ x : α, (P.map Y).real {x} * g x := by simp only [smul_eq_mul]

private lemma sum_map_real_singleton_eq_one
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → α} (hY : Measurable Y) :
    ∑ x : α, (P.map Y).real {x} = 1 := by
  have : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr ‹_›
  rw [sum_measureReal_singleton (Finset.univ : Finset α), Finset.coe_univ, probReal_univ]

private lemma sum_antiVoterStep_toReal_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → Bool) :
    ∑ y : V → Bool, (antiVoterStep G x y).toReal = 1 := by
  have hsum : ∑ y : V → Bool, antiVoterStep G x y = 1 := by
    simpa using (antiVoterStep G x).tsum_coe
  rw [← ENNReal.toReal_sum (fun y _ ↦ (antiVoterStep G x).apply_ne_top y), hsum,
    ENNReal.toReal_one]

private lemma stationary_measureReal_eq
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ν : Measure (V → Bool)} [IsFiniteMeasure ν] (hStat : IsAntiVoterStationary G ν)
    (y : V → Bool) :
    ν.real {y} = ∑ x : V → Bool, ν.real {x} * (antiVoterStep G x y).toReal := by
  simp only [measureReal_def]
  rw [hStat y, ENNReal.toReal_sum (fun x _ ↦
    ENNReal.mul_ne_top (measure_ne_top ν {x}) ((antiVoterStep G x).apply_ne_top y))]
  exact Finset.sum_congr rfl fun x _ ↦ ENNReal.toReal_mul

private lemma stationary_sum_step_sub_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ν : Measure (V → Bool)} [IsFiniteMeasure ν] (hStat : IsAntiVoterStationary G ν)
    (g : (V → Bool) → ℝ) :
    ∑ x : V → Bool, ν.real {x} *
      (∑ y : V → Bool, (antiVoterStep G x y).toReal * (g y - g x)) = 0 := by
  have hexp : ∀ x : V → Bool,
      ν.real {x} * (∑ y : V → Bool, (antiVoterStep G x y).toReal * (g y - g x)) =
        (∑ y : V → Bool, ν.real {x} * (antiVoterStep G x y).toReal * g y) -
          ν.real {x} * g x := by
    intro x
    have h1 :
        ∑ y : V → Bool, (antiVoterStep G x y).toReal * (g y - g x) =
          (∑ y : V → Bool, (antiVoterStep G x y).toReal * g y) -
            (∑ y : V → Bool, (antiVoterStep G x y).toReal) * g x := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [h1, sum_antiVoterStep_toReal_eq_one G x, one_mul, mul_sub, Finset.mul_sum]
    simp_rw [← mul_assoc]
  simp_rw [hexp]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have hL :
      (∑ y : V → Bool, ∑ x : V → Bool, ν.real {x} * (antiVoterStep G x y).toReal * g y) =
        ∑ y : V → Bool, ν.real {y} * g y := by
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← Finset.sum_mul, ← stationary_measureReal_eq G hStat y]
  rw [hL, sub_self]

/-! ### Stationary Mean Zero and Lemma 3.10 Variance Bounds -/

/-- Under any stationary distribution of the anti-voter Markov chain on a nonempty $r$-regular
finite simple graph ($r > 0$), the total spin $S = \sum_{v \in V} \operatorname{spin}(X_v)$ has
mean zero (`SteinIntro.tex:1107-1113`, `1212-1219`). -/
theorem antiVoter_stationary_mean_zero
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → V → Bool}
    (hV : (Finset.univ : Finset V).Nonempty)
    (hReg : G.IsRegularOfDegree r) (hr : 0 < r) (hX : Measurable X)
    (hStat : IsAntiVoterStationary G (P.map X)) :
    ∫ ω, (∑ v : V, spin (X ω v)) ∂P = 0 := by
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr ‹_›
  have : Nonempty V := ⟨hV.choose⟩
  have hn_pos : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hc_ne : -(2 / (Fintype.card V : ℝ)) ≠ 0 :=
    neg_ne_zero.mpr (div_pos zero_lt_two hn_pos).ne'
  have hMulZero :
      -(2 / (Fintype.card V : ℝ)) *
        (∑ x : V → Bool, (P.map X).real {x} * totalSpin x) = 0 := by
    have h0 := stationary_sum_step_sub_eq_zero G hStat totalSpin
    simp_rw [sum_antiVoterStep_sub_totalSpin G hV hReg hr] at h0
    rw [Finset.mul_sum]
    refine Eq.trans ?_ h0
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  have hSumZero : ∑ x : V → Bool, (P.map X).real {x} * totalSpin x = 0 :=
    (mul_eq_zero.mp hMulZero).resolve_left hc_ne
  change ∫ ω, totalSpin (X ω) ∂P = 0
  rw [integral_comp_eq_sum_map_real P hX totalSpin, hSumZero]

/-- Lemma 3.10 (`SteinIntro.tex:1208-1219`): for any stationary distribution of the anti-voter
Markov chain on an $r$-regular finite simple graph $G$ ($r > 0$), the variance $\sigma^2$ of the
total spin $S = \sum_{v \in V} \operatorname{spin}(X_v)$ satisfies
$\frac{2 \kappa(G)}{r} \le \sigma^2 \le |V|$. -/
theorem antiVoter_variance_bounds
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → V → Bool}
    (hReg : G.IsRegularOfDegree r) (hr : 0 < r) (hX : Measurable X)
    (hStat : IsAntiVoterStationary G (P.map X)) :
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    2 * (kappa G : ℝ) / (r : ℝ) ≤ ProbabilityTheory.variance S P ∧
      ProbabilityTheory.variance S P ≤ (Fintype.card V : ℝ) := by
  set S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
  change 2 * (kappa G : ℝ) / (r : ℝ) ≤ ProbabilityTheory.variance S P ∧
    ProbabilityTheory.variance S P ≤ (Fintype.card V : ℝ)
  by_cases hV : (Finset.univ : Finset V).Nonempty
  · have : Nonempty V := ⟨hV.choose⟩
    have : IsProbabilityMeasure (P.map X) :=
      (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr ‹_›
    set n : ℝ := (Fintype.card V : ℝ)
    have hn_pos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
    have hr_pos : 0 < (r : ℝ) := Nat.cast_pos.mpr hr
    have hn_ne : n ≠ 0 := hn_pos.ne'
    have hr_ne : (r : ℝ) ≠ 0 := hr_pos.ne'
    have hnr_ne : n * (r : ℝ) ≠ 0 := mul_ne_zero hn_ne hr_ne
    have hS_eq : S = fun ω ↦ totalSpin (X ω) := rfl
    have hS_meas : Measurable S := (measurable_of_finite totalSpin).comp hX
    have hMean : ∫ ω, S ω ∂P = 0 := antiVoter_stationary_mean_zero G P hV hReg hr hX hStat
    have hVar :
        ProbabilityTheory.variance S P =
          ∑ x : V → Bool, (P.map X).real {x} * totalSpin x ^ 2 := by
      rw [ProbabilityTheory.variance_of_integral_eq_zero hS_meas.aemeasurable hMean, hS_eq]
      exact integral_comp_eq_sum_map_real P hX (fun x ↦ totalSpin x ^ 2)
    have hStepSq : ∀ x : V → Bool,
        (∑ y : V → Bool,
          (antiVoterStep G x y).toReal * (totalSpin y ^ 2 - totalSpin x ^ 2)) =
          (2 + 2 / (n * (r : ℝ)) * quadSpin G x) - (4 / n) * totalSpin x ^ 2 := by
      intro x
      have halg : ∀ y : V → Bool,
          (antiVoterStep G x y).toReal * (totalSpin y ^ 2 - totalSpin x ^ 2) =
            (antiVoterStep G x y).toReal * (totalSpin y - totalSpin x) ^ 2 +
              2 * totalSpin x * ((antiVoterStep G x y).toReal * (totalSpin y - totalSpin x)) :=
        fun y ↦ by ring
      simp_rw [halg]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        sum_antiVoterStep_sq_sub_totalSpin G hV hReg hr x,
        sum_antiVoterStep_sub_totalSpin G hV hReg hr x]
      dsimp only [n]
      ring
    have hScale : ∀ x : V → Bool,
        n * (r : ℝ) *
          ((2 + 2 / (n * (r : ℝ)) * quadSpin G x) - (4 / n) * totalSpin x ^ 2) =
          (2 * n * (r : ℝ) + 2 * quadSpin G x) - 4 * (r : ℝ) * totalSpin x ^ 2 := by
      intro x
      have h1 : n * (r : ℝ) * (2 / (n * (r : ℝ))) = 2 := mul_div_cancel₀ 2 hnr_ne
      have h2 : n * (4 / n) = 4 := mul_div_cancel₀ 4 hn_ne
      calc
        n * (r : ℝ) * ((2 + 2 / (n * (r : ℝ)) * quadSpin G x) - (4 / n) * totalSpin x ^ 2)
          = 2 * n * (r : ℝ) + (n * (r : ℝ) * (2 / (n * (r : ℝ)))) * quadSpin G x -
              (n * (4 / n)) * (r : ℝ) * totalSpin x ^ 2 := by ring
        _ = (2 * n * (r : ℝ) + 2 * quadSpin G x) - 4 * (r : ℝ) * totalSpin x ^ 2 := by
              rw [h1, h2]
    have hVarId :
        4 * (r : ℝ) * ProbabilityTheory.variance S P =
          ∑ x : V → Bool, (P.map X).real {x} * (2 * n * (r : ℝ) + 2 * quadSpin G x) := by
      have h0 := stationary_sum_step_sub_eq_zero G hStat (fun x ↦ totalSpin x ^ 2)
      simp_rw [hStepSq] at h0
      have hMul : n * (r : ℝ) *
          (∑ x : V → Bool, (P.map X).real {x} *
            ((2 + 2 / (n * (r : ℝ)) * quadSpin G x) - (4 / n) * totalSpin x ^ 2)) = 0 := by
        rw [h0, mul_zero]
      rw [Finset.mul_sum] at hMul
      have hDiff :
          (∑ x : V → Bool, (P.map X).real {x} * (2 * n * (r : ℝ) + 2 * quadSpin G x)) -
            4 * (r : ℝ) * ProbabilityTheory.variance S P = 0 := by
        rw [hVar, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Eq.trans ?_ hMul
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        calc
          (P.map X).real {x} * (2 * n * (r : ℝ) + 2 * quadSpin G x) -
              4 * (r : ℝ) * ((P.map X).real {x} * totalSpin x ^ 2)
            = (P.map X).real {x} * ((2 * n * (r : ℝ) + 2 * quadSpin G x) -
                4 * (r : ℝ) * totalSpin x ^ 2) := by ring
          _ = (P.map X).real {x} * (n * (r : ℝ) *
                ((2 + 2 / (n * (r : ℝ)) * quadSpin G x) - (4 / n) * totalSpin x ^ 2)) := by
                rw [← hScale x]
          _ = n * (r : ℝ) * ((P.map X).real {x} *
                ((2 + 2 / (n * (r : ℝ)) * quadSpin G x) - (4 / n) * totalSpin x ^ 2)) := by ring
      linarith [hDiff]
    have hSumOne : ∑ x : V → Bool, (P.map X).real {x} = 1 :=
      sum_map_real_singleton_eq_one P hX
    have hLoSum :
        8 * (kappa G : ℝ) ≤ 4 * (r : ℝ) * ProbabilityTheory.variance S P := by
      calc
        8 * (kappa G : ℝ)
          = (∑ x : V → Bool, (P.map X).real {x}) * (8 * (kappa G : ℝ)) := by
              rw [hSumOne, one_mul]
        _ = ∑ x : V → Bool, (P.map X).real {x} * (8 * (kappa G : ℝ)) := Finset.sum_mul _ _ _
        _ ≤ ∑ x : V → Bool, (P.map X).real {x} * (2 * n * (r : ℝ) + 2 * quadSpin G x) :=
            Finset.sum_le_sum fun x _ ↦
              mul_le_mul_of_nonneg_left
                (eight_mul_kappa_le_two_card_mul_deg_add_two_quadSpin G hReg x)
                measureReal_nonneg
        _ = 4 * (r : ℝ) * ProbabilityTheory.variance S P := hVarId.symm
    have hHiSum :
        4 * (r : ℝ) * ProbabilityTheory.variance S P ≤ 4 * n * (r : ℝ) := by
      calc
        4 * (r : ℝ) * ProbabilityTheory.variance S P
          = ∑ x : V → Bool, (P.map X).real {x} * (2 * n * (r : ℝ) + 2 * quadSpin G x) := hVarId
        _ ≤ ∑ x : V → Bool, (P.map X).real {x} * (4 * n * (r : ℝ)) :=
            Finset.sum_le_sum fun x _ ↦
              mul_le_mul_of_nonneg_left
                (two_card_mul_deg_add_two_quadSpin_le_four_card_mul_deg G hReg x)
                measureReal_nonneg
        _ = (∑ x : V → Bool, (P.map X).real {x}) * (4 * n * (r : ℝ)) :=
            (Finset.sum_mul _ _ _).symm
        _ = 4 * n * (r : ℝ) := by rw [hSumOne, one_mul]
    refine ⟨(div_le_iff₀ hr_pos).mpr (by linarith [hLoSum]), ?_⟩
    exact le_of_mul_le_mul_left (by linarith [hHiSum]) (mul_pos (by norm_num : (0 : ℝ) < 4) hr_pos)
  · have : IsEmpty V := ⟨fun v ↦ hV ⟨v, Finset.mem_univ v⟩⟩
    have hKappa : kappa G = 0 := by
      unfold kappa
      refine Finset.inf'_eq_of_forall Finset.univ_nonempty _ fun A _ ↦ ?_
      have hEmp : (G.edgeFinset.filter fun e ↦ e ∈ A.sym2 ∨ e ∈ Aᶜ.sym2) = ∅ := by
        ext e
        rcases e with ⟨v, _⟩
        exact isEmptyElim v
      rw [hEmp, Finset.card_empty]
    have hUniv : (Finset.univ : Finset V) = ∅ := by
      ext v
      exact isEmptyElim v
    have hS : S = 0 := by
      ext ω
      change ∑ v ∈ (Finset.univ : Finset V), spin (X ω v) = 0
      rw [hUniv, Finset.sum_empty]
    rw [hKappa, hS, ProbabilityTheory.variance_zero, Fintype.card_eq_zero]
    simp

/-! ### One-Step Coupling and Conditional Expectation Helpers -/

private lemma measureReal_step_eq
    {V Ω : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [MeasurableSpace Ω] (P : Measure Ω)
    {X X' : Ω → V → Bool}
    (hStep : ∀ x y : V → Bool,
      P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y)
    (x y : V → Bool) :
    P.real {ω | X ω = x ∧ X' ω = y} =
      P.real {ω | X ω = x} * (antiVoterStep G x y).toReal := by
  simp only [measureReal_def, hStep x y, ENNReal.toReal_mul]

private lemma map_snd_eq_map_fst
    {V Ω : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X X' : Ω → V → Bool} (hX : Measurable X) (hX' : Measurable X')
    (hStat : IsAntiVoterStationary G (P.map X))
    (hStep : ∀ x y : V → Bool,
      P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y) :
    P.map X' = P.map X := by
  have : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr ‹_›
  have : IsProbabilityMeasure (P.map X') :=
    (Measure.isProbabilityMeasure_map_iff hX'.aemeasurable).mpr ‹_›
  refine Measure.ext_of_singleton fun y ↦ ?_
  refine (measureReal_eq_measureReal_iff
    (measure_ne_top (P.map X') {y}) (measure_ne_top (P.map X) {y})).mp ?_
  rw [map_measureReal_apply hX' (measurableSet_singleton y),
    stationary_measureReal_eq G hStat y]
  have hUnion : X' ⁻¹' {y} = ⋃ x ∈ (Finset.univ : Finset (V → Bool)),
      {ω | X ω = x ∧ X' ω = y} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, Finset.mem_univ, mem_iUnion, mem_ofPred_eq]
    exact ⟨fun hy ↦ ⟨X ω, trivial, rfl, hy⟩, fun ⟨_, _, _, hy⟩ ↦ hy⟩
  have hDisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (V → Bool)))
      (fun x : V → Bool ↦ {ω | X ω = x ∧ X' ω = y}) := by
    intro x₁ _ x₂ _ hne
    change Disjoint _ _
    rw [Set.disjoint_left]
    rintro ω ⟨hx₁, _⟩ ⟨hx₂, _⟩
    exact hne (hx₁.symm.trans hx₂)
  have hMeas : ∀ x ∈ (Finset.univ : Finset (V → Bool)),
      MeasurableSet {ω | X ω = x ∧ X' ω = y} := fun x _ ↦
    (hX (measurableSet_singleton x)).inter (hX' (measurableSet_singleton y))
  rw [hUnion, measureReal_biUnion_finset hDisj hMeas (fun _ _ ↦ measure_ne_top P _)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hPre : X ⁻¹' {x} = {ω | X ω = x} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  rw [measureReal_step_eq G P hStep x y, map_measureReal_apply hX (measurableSet_singleton x),
    hPre]

private lemma ae_antiVoterStep_ne_zero
    {V Ω : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [MeasurableSpace Ω] (P : Measure Ω)
    {X X' : Ω → V → Bool}
    (hStep : ∀ x y : V → Bool,
      P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y) :
    ∀ᵐ ω ∂P, antiVoterStep G (X ω) (X' ω) ≠ 0 := by
  have hPair : ∀ q : (V → Bool) × (V → Bool),
      ∀ᵐ ω ∂P, X ω = q.1 ∧ X' ω = q.2 → antiVoterStep G q.1 q.2 ≠ 0 := by
    rintro ⟨x, y⟩
    by_cases hxy : antiVoterStep G x y = 0
    · rw [ae_iff]
      refine measure_mono_null (t := {ω | X ω = x ∧ X' ω = y})
        (fun ω hω ↦ (not_imp.mp hω).1) ?_
      rw [hStep x y, hxy, mul_zero]
    · exact ae_of_all P fun _ _ ↦ hxy
  filter_upwards [ae_all_iff.mpr hPair] with ω hω
  exact hω (X ω, X' ω) ⟨rfl, rfl⟩

private lemma setIntegral_fiber_step_eq
    {V Ω : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X X' : Ω → V → Bool} (hX : Measurable X) (hX' : Measurable X')
    (hStep : ∀ x y : V → Bool,
      P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y)
    (F : (V → Bool) → (V → Bool) → ℝ) (x : V → Bool) :
    ∫ ω in {ω | X ω = x},
      (∑ y : V → Bool, (antiVoterStep G (X ω) y).toReal * F (X ω) y) ∂P =
      ∫ ω in {ω | X ω = x}, F (X ω) (X' ω) ∂P := by
  set h : (V → Bool) → ℝ := fun z ↦ ∑ y : V → Bool, (antiVoterStep G z y).toReal * F z y
  have hf_int : Integrable (fun ω ↦ F (X ω) (X' ω)) P :=
    integrable_comp_of_fintype P (hX.prodMk hX') (fun q ↦ F q.1 q.2)
  have hx_meas : MeasurableSet {ω | X ω = x} := hX (measurableSet_singleton x)
  have hLHS :
      ∫ ω in {ω | X ω = x}, h (X ω) ∂P =
        ∑ y : V → Bool, P.real {ω | X ω = x} * (antiVoterStep G x y).toReal * F x y := by
    calc
      ∫ ω in {ω | X ω = x}, h (X ω) ∂P
        = ∫ _ in {ω | X ω = x}, h x ∂P :=
          setIntegral_congr_fun hx_meas fun _ hω ↦ congrArg h hω
      _ = P.real {ω | X ω = x} * h x := by rw [setIntegral_const, smul_eq_mul]
      _ = ∑ y : V → Bool, P.real {ω | X ω = x} * (antiVoterStep G x y).toReal * F x y := by
          dsimp only [h]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ ↦ (mul_assoc _ _ _).symm
  have hUnion : {ω | X ω = x} = ⋃ y : V → Bool, {ω | X ω = x ∧ X' ω = y} := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq]
    exact ⟨fun hx ↦ ⟨X' ω, hx, rfl⟩, fun ⟨_, hx, _⟩ ↦ hx⟩
  have hs_meas : ∀ y : V → Bool, MeasurableSet {ω | X ω = x ∧ X' ω = y} := fun y ↦
    (hX (measurableSet_singleton x)).inter (hX' (measurableSet_singleton y))
  have hs_disj :
      Pairwise (Function.onFun Disjoint fun y : V → Bool ↦ {ω | X ω = x ∧ X' ω = y}) := by
    intro y₁ y₂ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨_, hy₁⟩ ⟨_, hy₂⟩
    exact hne (hy₁.symm.trans hy₂)
  have hRHS :
      ∫ ω in {ω | X ω = x}, F (X ω) (X' ω) ∂P =
        ∑ y : V → Bool, P.real {ω | X ω = x} * (antiVoterStep G x y).toReal * F x y := by
    nth_rw 1 [hUnion]
    rw [integral_iUnion_fintype hs_meas hs_disj (fun _ ↦ hf_int.integrableOn)]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    calc
      ∫ ω in {ω | X ω = x ∧ X' ω = y}, F (X ω) (X' ω) ∂P
        = ∫ _ in {ω | X ω = x ∧ X' ω = y}, F x y ∂P :=
          setIntegral_congr_fun (hs_meas y) fun _ ⟨hx, hy⟩ ↦ by rw [hx, hy]
      _ = P.real {ω | X ω = x ∧ X' ω = y} * F x y := by rw [setIntegral_const, smul_eq_mul]
      _ = P.real {ω | X ω = x} * (antiVoterStep G x y).toReal * F x y := by
          rw [measureReal_step_eq G P hStep x y]
  exact hLHS.trans hRHS.symm

private lemma condExp_step_eq
    {V Ω : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X X' : Ω → V → Bool} (hX : Measurable X) (hX' : Measurable X')
    (hStep : ∀ x y : V → Bool,
      P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y)
    (F : (V → Bool) → (V → Bool) → ℝ) :
    P[fun ω ↦ F (X ω) (X' ω) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω ↦ ∑ y : V → Bool, (antiVoterStep G (X ω) y).toReal * F (X ω) y := by
  set h : (V → Bool) → ℝ := fun z ↦ ∑ y : V → Bool, (antiVoterStep G z y).toReal * F z y
  set g : Ω → ℝ := fun ω ↦ h (X ω)
  have hf_int : Integrable (fun ω ↦ F (X ω) (X' ω)) P :=
    integrable_comp_of_fintype P (hX.prodMk hX') (fun q ↦ F q.1 q.2)
  have hg_int : Integrable g P := integrable_comp_of_fintype P hX h
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] g P :=
    ((measurable_of_finite h).comp
      (comap_measurable (m := inferInstance) X)).stronglyMeasurable.aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hf_int
    (fun _ _ _ ↦ hg_int.integrableOn) (fun s hs _ ↦ ?_) hgm).symm
  rcases hs with ⟨B, _, rfl⟩
  classical
  set t : Finset (V → Bool) := Finset.univ.filter (· ∈ B)
  have hUnion : X ⁻¹' B = ⋃ x ∈ t, {ω | X ω = x} := by
    ext ω
    simp only [t, mem_preimage, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_ofPred_eq]
    exact ⟨fun hω ↦ ⟨X ω, hω, rfl⟩, fun ⟨x, hx, hEq⟩ ↦ hEq.symm ▸ hx⟩
  have ht_meas : ∀ x ∈ t, MeasurableSet {ω | X ω = x} :=
    fun x _ ↦ hX (measurableSet_singleton x)
  have ht_disj : Set.PairwiseDisjoint (↑t) (fun x : V → Bool ↦ {ω | X ω = x}) := by
    intro x₁ _ x₂ _ hne
    change Disjoint _ _
    rw [Set.disjoint_left]
    intro ω hx₁ hx₂
    exact hne (hx₁.symm.trans hx₂)
  rw [hUnion, integral_biUnion_finset t ht_meas ht_disj (fun _ _ ↦ hg_int.integrableOn),
    integral_biUnion_finset t ht_meas ht_disj (fun _ _ ↦ hf_int.integrableOn)]
  exact Finset.sum_congr rfl fun x _ ↦ setIntegral_fiber_step_eq G P hX hX' hStep F x

/-! ### Theorem 3.8: Anti-Voter Stein Pair and Wasserstein Bound -/

/-- Theorem 3.8 (`\label{thm52}`, `SteinIntro.tex:1114-1207`): for the anti-voter Markov chain
on an $r$-regular finite simple graph $G$ on $n = |V|$ vertices that is neither bipartite nor a
cycle, if $X$ has a stationary distribution and $X'$ is one step of the chain from $X$, then
$(W, W')$ is a $(2/n)$-Stein pair and
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \frac{4n}{3\sigma^3} +
\frac{\sqrt{\operatorname{Var}(Q)}}{r\sigma^2\sqrt{2\pi}}$. -/
theorem antiVoter_steinPair_and_wasserstein_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X X' : Ω → V → Bool} {Z : Ω' → ℝ}
    (hReg : G.IsRegularOfDegree r)
    (hBip : ¬ G.IsBipartite)
    (_hCyc : IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)))
    (hX : Measurable X) (hX' : Measurable X')
    (hStat : IsAntiVoterStationary G (P.map X))
    (hStep : ∀ x y : V → Bool,
      P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y)
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    let n : ℝ := Fintype.card V
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    let S' : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X' ω v)
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    let W' : Ω → ℝ := fun ω ↦ S' ω / σ
    let Q : Ω → ℝ := fun ω ↦ ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (X ω i) * spin (X ω j)
    IsSteinPair P (2 / n) W W' ∧
      wassersteinDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (4 * n / (3 * σ ^ 3) +
            Real.sqrt (ProbabilityTheory.variance Q P) /
              ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi))) := by
  set n : ℝ := (Fintype.card V : ℝ)
  set S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
  set S' : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X' ω v)
  set σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
  set W : Ω → ℝ := fun ω ↦ S ω / σ
  set W' : Ω → ℝ := fun ω ↦ S' ω / σ
  set Q : Ω → ℝ := fun ω ↦ ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (X ω i) * spin (X ω j)
  change IsSteinPair P (2 / n) W W' ∧
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (4 * n / (3 * σ ^ 3) +
          Real.sqrt (ProbabilityTheory.variance Q P) /
            ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi)))
  have hk_ge : 1 ≤ kappa G := one_le_kappa_of_not_isBipartite G hBip
  have hn_ge : 3 ≤ Fintype.card V := three_le_card_of_not_isBipartite G hBip
  have hr_ge : 1 ≤ r := one_le_degree_of_not_isBipartite G hReg hBip
  have hr_pos_nat : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one hr_ge
  have hn_pos_nat : 0 < Fintype.card V := by omega
  have : Nonempty V := Fintype.card_pos_iff.mp hn_pos_nat
  have hV : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hk_real : (1 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast hk_ge
  have hn_real : (3 : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast hn_ge
  have hr_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
  have hn_pos : 0 < n := by linarith [hn_real]
  have hr_pos : 0 < (r : ℝ) := by linarith [hr_real]
  have ha_pos : 0 < 2 / n := div_pos zero_lt_two hn_pos
  have ha_le_one : 2 / n ≤ 1 := (div_le_iff₀ hn_pos).mpr (by linarith [hn_real])
  obtain ⟨hVar_lo, _⟩ := antiVoter_variance_bounds G P hReg hr_pos_nat hX hStat
  have hVar_pos : 0 < ProbabilityTheory.variance S P :=
    lt_of_lt_of_le (div_pos (by linarith [hk_real]) hr_pos) hVar_lo
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar_pos
  have hσ_ne : σ ≠ 0 := hσ_pos.ne'
  have hσ_sq : σ ^ 2 = ProbabilityTheory.variance S P := Real.sq_sqrt hVar_pos.le
  have hW_meas : Measurable W := (measurable_of_finite (fun x ↦ totalSpin x / σ)).comp hX
  have hW_int : Integrable W P := integrable_comp_of_fintype P hX (fun x ↦ totalSpin x / σ)
  have hS_meas : Measurable S := (measurable_of_finite totalSpin).comp hX
  have hMeanS : ∫ ω, S ω ∂P = 0 :=
    antiVoter_stationary_mean_zero G P hV hReg hr_pos_nat hX hStat
  have hW2_eq : ∫ ω, W ω ^ 2 ∂P = 1 := by
    have hEq : (fun ω ↦ W ω ^ 2) = fun ω ↦ S ω ^ 2 / σ ^ 2 :=
      funext fun ω ↦ div_pow (S ω) σ 2
    rw [hEq, integral_div (σ ^ 2) (fun ω ↦ S ω ^ 2),
      ← ProbabilityTheory.variance_of_integral_eq_zero hS_meas.aemeasurable hMeanS,
      ← hσ_sq, div_self (pow_ne_zero 2 hσ_ne)]
  have hStepNe : ∀ᵐ ω ∂P, antiVoterStep G (X ω) (X' ω) ≠ 0 :=
    ae_antiVoterStep_ne_zero G P hStep
  have hIdX : IdentDistrib X X' P P :=
    ⟨hX.aemeasurable, hX'.aemeasurable, (map_snd_eq_map_fst G P hX hX' hStat hStep).symm⟩
  have hExchTC :
      IsExchangeablePair P (fun ω ↦ trueCount (X ω)) (fun ω ↦ trueCount (X' ω)) :=
    isExchangeablePair_of_identDistrib_int_abs_sub_le_one P
      (hIdX.comp (measurable_of_finite trueCount))
      (hStepNe.mono fun _ hω ↦ antiVoterStep_trueCount_abs_sub_le_one G hω)
  have hExchW : IsExchangeablePair P W W' := by
    let φ : ℤ → ℝ := fun k ↦ (2 * (k : ℝ) - n) / σ
    have hΦ : Measurable (fun p : ℤ × ℤ ↦ (φ p.1, φ p.2)) :=
      ((measurable_of_countable φ).comp measurable_fst).prodMk
        ((measurable_of_countable φ).comp measurable_snd)
    have hφ : ∀ x : V → Bool, φ (trueCount x) = totalSpin x / σ := fun x ↦
      congrArg (· / σ) (totalSpin_eq_two_trueCount_sub x).symm
    have hEq12 : (fun ω ↦ (φ (trueCount (X ω)), φ (trueCount (X' ω)))) =
        fun ω ↦ (W ω, W' ω) :=
      funext fun ω ↦ Prod.ext (hφ (X ω)) (hφ (X' ω))
    have hEq21 : (fun ω ↦ (φ (trueCount (X' ω)), φ (trueCount (X ω)))) =
        fun ω ↦ (W' ω, W ω) :=
      funext fun ω ↦ Prod.ext (hφ (X' ω)) (hφ (X ω))
    unfold IsExchangeablePair
    rw [← hEq12, ← hEq21]
    exact hExchTC.comp hΦ
  have hmWX : MeasurableSpace.comap W inferInstance ≤ MeasurableSpace.comap X inferInstance := by
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨(fun x : V → Bool ↦ totalSpin x / σ) ⁻¹' A,
      measurable_of_finite (fun x : V → Bool ↦ totalSpin x / σ) hA, rfl⟩
  have hCondW'_X :
      P[W' | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun ω ↦ (1 - 2 / n) * W ω := by
    have hBase := condExp_step_eq G P hX hX' hStep (fun _ y ↦ totalSpin y / σ)
    have hSumW' : ∀ x : V → Bool,
        (∑ y : V → Bool, (antiVoterStep G x y).toReal * (totalSpin y / σ)) =
          (1 - 2 / n) * (totalSpin x / σ) := by
      intro x
      have hSplit : ∀ y : V → Bool,
          (antiVoterStep G x y).toReal * (totalSpin y / σ) =
            ((antiVoterStep G x y).toReal * (totalSpin y - totalSpin x) +
              (antiVoterStep G x y).toReal * totalSpin x) * σ⁻¹ := by
        intro y
        rw [div_eq_mul_inv]
        ring
      simp_rw [hSplit]
      rw [← Finset.sum_mul, Finset.sum_add_distrib,
        sum_antiVoterStep_sub_totalSpin G hV hReg hr_pos_nat x,
        ← Finset.sum_mul, sum_antiVoterStep_toReal_eq_one G x]
      dsimp only [n]
      rw [div_eq_mul_inv (totalSpin x) σ]
      ring
    exact hBase.mono fun ω hω ↦ hω.trans (hSumW' (X ω))
  have hCondW'_W :
      P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - 2 / n) * W ω := by
    have hR_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance]
        (fun ω ↦ (1 - 2 / n) * W ω) :=
      ((continuous_const.mul continuous_id').measurable.comp
        (comap_measurable (m := inferInstance) W)).stronglyMeasurable
    have hTower :
        P[P[W' | MeasurableSpace.comap X inferInstance] |
          MeasurableSpace.comap W inferInstance] =ᵐ[P]
          P[W' | MeasurableSpace.comap W inferInstance] :=
      condExp_condExp_of_le (μ := P) (f := W') hmWX hX.comap_le
    refine hTower.symm.trans
      ((condExp_congr_ae (m := MeasurableSpace.comap W inferInstance) hCondW'_X).trans ?_)
    rw [condExp_of_stronglyMeasurable hW_meas.comap_le hR_sm (hW_int.const_mul (1 - 2 / n))]
  have hStein : IsSteinPair P (2 / n) W W' :=
    ⟨hExchW, ha_pos, ha_le_one, hW_meas, hW_int, hCondW'_W⟩
  set D2 : Ω → ℝ := fun ω ↦ (W' ω - W ω) ^ 2
  set c₁ : ℝ := 2 / σ ^ 2
  set c₂ : ℝ := 2 / (n * (r : ℝ) * σ ^ 2)
  have hD2_int : Integrable D2 P :=
    integrable_comp_of_fintype P (hX.prodMk hX')
      (fun q ↦ (totalSpin q.2 / σ - totalSpin q.1 / σ) ^ 2)
  have hCondD2_X :
      P[D2 | MeasurableSpace.comap X inferInstance] =ᵐ[P] fun ω ↦ c₁ + c₂ * Q ω := by
    have hBase := condExp_step_eq G P hX hX' hStep
      (fun x y ↦ (totalSpin y / σ - totalSpin x / σ) ^ 2)
    have hSumD2 : ∀ x : V → Bool,
        (∑ y : V → Bool,
          (antiVoterStep G x y).toReal * (totalSpin y / σ - totalSpin x / σ) ^ 2) =
          c₁ + c₂ * quadSpin G x := by
      intro x
      have hSplit : ∀ y : V → Bool,
          (antiVoterStep G x y).toReal * (totalSpin y / σ - totalSpin x / σ) ^ 2 =
            ((antiVoterStep G x y).toReal * (totalSpin y - totalSpin x) ^ 2) * (σ ^ 2)⁻¹ := by
        intro y
        rw [← sub_div, div_pow, div_eq_mul_inv, ← mul_assoc]
      simp_rw [hSplit]
      rw [← Finset.sum_mul, sum_antiVoterStep_sq_sub_totalSpin G hV hReg hr_pos_nat x]
      dsimp only [c₁, c₂, n]
      ring
    exact hBase.mono fun ω hω ↦ hω.trans (hSumD2 (X ω))
  have hAffQ2 : MemLp (fun ω ↦ c₁ + c₂ * Q ω) 2 P :=
    memLp_two_comp_of_fintype P hX (fun x ↦ c₁ + c₂ * quadSpin G x)
  have hc₂Q_asm : AEStronglyMeasurable (fun ω ↦ c₂ * Q ω) P :=
    ((measurable_of_finite (fun x ↦ c₂ * quadSpin G x)).comp hX).aestronglyMeasurable
  have hc₂_nn : 0 ≤ c₂ := by positivity
  have hDen₁ : 0 < Real.sqrt (2 * Real.pi) * (2 / n) :=
    mul_pos (Real.sqrt_pos.mpr (mul_pos zero_lt_two Real.pi_pos)) ha_pos
  have hc₂_mul : c₂ * ((r : ℝ) * σ ^ 2) = 2 / n := by
    dsimp only [c₂]
    have hden : n * (r : ℝ) * σ ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hn_pos.ne' hr_pos.ne') (pow_ne_zero 2 hσ_ne)
    refine mul_right_cancel₀ hn_pos.ne' ?_
    calc
      2 / (n * (r : ℝ) * σ ^ 2) * ((r : ℝ) * σ ^ 2) * n
        = 2 / (n * (r : ℝ) * σ ^ 2) * (n * (r : ℝ) * σ ^ 2) := by ring
      _ = 2 := div_mul_cancel₀ 2 hden
      _ = 2 / n * n := (div_mul_cancel₀ 2 hn_pos.ne').symm
  have hQuot₁ :
      c₂ * Real.sqrt (ProbabilityTheory.variance Q P) /
        (Real.sqrt (2 * Real.pi) * (2 / n)) =
        Real.sqrt (ProbabilityTheory.variance Q P) /
          ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi)) := by
    set sQ : ℝ := Real.sqrt (ProbabilityTheory.variance Q P)
    set sPi : ℝ := Real.sqrt (2 * Real.pi)
    have hsPi_pos : 0 < sPi := Real.sqrt_pos.mpr (mul_pos zero_lt_two Real.pi_pos)
    have hdenA : sPi * (2 / n) ≠ 0 := mul_ne_zero hsPi_pos.ne' ha_pos.ne'
    have hdenB : (r : ℝ) * σ ^ 2 * sPi ≠ 0 :=
      mul_ne_zero (mul_ne_zero hr_pos.ne' (pow_ne_zero 2 hσ_ne)) hsPi_pos.ne'
    refine mul_right_cancel₀ (mul_ne_zero hdenA hdenB) ?_
    have hA : c₂ * sQ / (sPi * (2 / n)) * (sPi * (2 / n)) = c₂ * sQ :=
      div_mul_cancel₀ (c₂ * sQ) hdenA
    have hB : sQ / ((r : ℝ) * σ ^ 2 * sPi) * ((r : ℝ) * σ ^ 2 * sPi) = sQ :=
      div_mul_cancel₀ sQ hdenB
    calc
      c₂ * sQ / (sPi * (2 / n)) * (sPi * (2 / n) * ((r : ℝ) * σ ^ 2 * sPi))
        = (c₂ * sQ / (sPi * (2 / n)) * (sPi * (2 / n))) * ((r : ℝ) * σ ^ 2 * sPi) := by ring
      _ = (c₂ * ((r : ℝ) * σ ^ 2)) * sQ * sPi := by rw [hA]; ring
      _ = (2 / n) * sQ * sPi := by rw [hc₂_mul]
      _ = (sQ / ((r : ℝ) * σ ^ 2 * sPi) * ((r : ℝ) * σ ^ 2 * sPi)) * (sPi * (2 / n)) := by
            rw [hB]; ring
      _ = sQ / ((r : ℝ) * σ ^ 2 * sPi) * (sPi * (2 / n) * ((r : ℝ) * σ ^ 2 * sPi)) := by ring
  have hTerm₁ :
      ProbabilityTheory.evariance
          (P[D2 | MeasurableSpace.comap W inferInstance]) P ^ (1 / 2 : ℝ) /
        ENNReal.ofReal (Real.sqrt (2 * Real.pi) * (2 / n)) ≤
        ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) /
            ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi))) := by
    have hEvarLe :
        ProbabilityTheory.evariance (P[D2 | MeasurableSpace.comap W inferInstance]) P ≤
          ENNReal.ofReal (c₂ ^ 2 * ProbabilityTheory.variance Q P) := by
      refine (evariance_condExp_mono P hmWX hX.comap_le hD2_int).trans_eq ?_
      rw [ProbabilityTheory.evariance_congr hCondD2_X,
        ← ProbabilityTheory.ofReal_variance hAffQ2,
        ProbabilityTheory.variance_const_add hc₂Q_asm c₁,
        ProbabilityTheory.variance_const_mul c₂ Q P]
    have hRpowLe :
        ProbabilityTheory.evariance
            (P[D2 | MeasurableSpace.comap W inferInstance]) P ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (c₂ * Real.sqrt (ProbabilityTheory.variance Q P)) := by
      refine (ENNReal.rpow_le_rpow hEvarLe (by positivity)).trans_eq ?_
      rw [ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (sq_nonneg c₂) (ProbabilityTheory.variance_nonneg Q P)) (by positivity),
        ← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg c₂) (ProbabilityTheory.variance Q P),
        Real.sqrt_sq hc₂_nn]
    refine (ENNReal.div_le_div_right hRpowLe _).trans_eq ?_
    rw [← ENNReal.ofReal_div_of_pos hDen₁, hQuot₁]
  have hCubeAE :
      ∀ᵐ ω ∂P, ENNReal.ofReal (|W' ω - W ω| ^ 3) ≤ ENNReal.ofReal ((2 / σ) ^ 3) := by
    filter_upwards [hStepNe] with ω hω
    have hSpinLe : |totalSpin (X' ω) - totalSpin (X ω)| ≤ 2 :=
      antiVoterStep_totalSpin_abs_sub_le_two G hω
    have hDiffLe : |W' ω - W ω| ≤ 2 / σ := by
      change |totalSpin (X' ω) / σ - totalSpin (X ω) / σ| ≤ 2 / σ
      rw [← sub_div, abs_div, abs_of_pos hσ_pos]
      exact div_le_div_of_nonneg_right hSpinLe hσ_pos.le
    have hSqLe : |W' ω - W ω| * |W' ω - W ω| ≤ (2 / σ) * (2 / σ) :=
      mul_le_mul hDiffLe hDiffLe (abs_nonneg _) (by positivity)
    have hCubeLe : |W' ω - W ω| ^ 3 ≤ (2 / σ) ^ 3 := by
      calc
        |W' ω - W ω| ^ 3 = (|W' ω - W ω| * |W' ω - W ω|) * |W' ω - W ω| := by ring
        _ ≤ ((2 / σ) * (2 / σ)) * (2 / σ) :=
          mul_le_mul hSqLe hDiffLe (abs_nonneg _) (by positivity)
        _ = (2 / σ) ^ 3 := by ring
    exact ENNReal.ofReal_le_ofReal hCubeLe
  have hDen₂ : 0 < 3 * (2 / n) := mul_pos (by norm_num) ha_pos
  have hQuot₂ : (2 / σ) ^ 3 / (3 * (2 / n)) = 4 * n / (3 * σ ^ 3) := by
    have hdenA : 3 * (2 / n) ≠ 0 := hDen₂.ne'
    have hdenB : 3 * σ ^ 3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 3 hσ_ne)
    refine mul_right_cancel₀ (mul_ne_zero hdenA hdenB) ?_
    have hA : (2 / σ) ^ 3 / (3 * (2 / n)) * (3 * (2 / n)) = (2 / σ) ^ 3 :=
      div_mul_cancel₀ ((2 / σ) ^ 3) hdenA
    have hB : 4 * n / (3 * σ ^ 3) * (3 * σ ^ 3) = 4 * n :=
      div_mul_cancel₀ (4 * n) hdenB
    have hPow : (2 / σ) ^ 3 * σ ^ 3 = 8 := by
      rw [← mul_pow, div_mul_cancel₀ 2 hσ_ne]
      norm_num
    have hn2 : 2 / n * n = 2 := div_mul_cancel₀ 2 hn_pos.ne'
    calc
      (2 / σ) ^ 3 / (3 * (2 / n)) * (3 * (2 / n) * (3 * σ ^ 3))
        = ((2 / σ) ^ 3 / (3 * (2 / n)) * (3 * (2 / n))) * (3 * σ ^ 3) := by ring
      _ = 3 * ((2 / σ) ^ 3 * σ ^ 3) := by rw [hA]; ring
      _ = 24 := by rw [hPow]; norm_num
      _ = 12 * (2 / n * n) := by rw [hn2]; norm_num
      _ = (4 * n / (3 * σ ^ 3) * (3 * σ ^ 3)) * (3 * (2 / n)) := by rw [hB]; ring
      _ = 4 * n / (3 * σ ^ 3) * (3 * (2 / n) * (3 * σ ^ 3)) := by ring
  have hTerm₂ :
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * (2 / n)) ≤
        ENNReal.ofReal (4 * n / (3 * σ ^ 3)) := by
    have hM3Le :
        (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) ≤ ENNReal.ofReal ((2 / σ) ^ 3) := by
      calc
        (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P)
          ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((2 / σ) ^ 3) ∂P := lintegral_mono_ae hCubeAE
        _ = ENNReal.ofReal ((2 / σ) ^ 3) * P Set.univ :=
            lintegral_const (ENNReal.ofReal ((2 / σ) ^ 3))
        _ = ENNReal.ofReal ((2 / σ) ^ 3) := by rw [measure_univ, mul_one]
    refine (ENNReal.div_le_div_right hM3Le _).trans_eq ?_
    rw [← ENNReal.ofReal_div_of_pos hDen₂, hQuot₂]
  have hT1_nn :
      0 ≤ Real.sqrt (ProbabilityTheory.variance Q P) /
        ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi)) :=
    div_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg hr_pos.le (sq_nonneg σ)) (Real.sqrt_nonneg _))
  have hT2_nn : 0 ≤ 4 * n / (3 * σ ^ 3) := div_nonneg (by positivity) (by positivity)
  refine ⟨hStein, ?_⟩
  calc
    wassersteinDist (P.map W) (P'.map Z)
      ≤ ⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P| :=
        wassersteinDist_map_stdNormal_le_iSup_normalSteinOp P P' hW_meas.aemeasurable hZ hZ_law
    _ ≤ ProbabilityTheory.evariance
            (P[D2 | MeasurableSpace.comap W inferInstance]) P ^ (1 / 2 : ℝ) /
          ENNReal.ofReal (Real.sqrt (2 * Real.pi) * (2 / n)) +
        (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * (2 / n)) :=
        steinPair_iSup_normalWassersteinClass_le P hExchW ha_pos hW_meas hCondW'_W hW2_eq
    _ ≤ ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) /
            ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi))) +
        ENNReal.ofReal (4 * n / (3 * σ ^ 3)) :=
        add_le_add hTerm₁ hTerm₂
    _ = ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) /
            ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi)) +
          4 * n / (3 * σ ^ 3)) :=
        (ENNReal.ofReal_add hT1_nn hT2_nn).symm
    _ = ENNReal.ofReal
          (4 * n / (3 * σ ^ 3) +
            Real.sqrt (ProbabilityTheory.variance Q P) /
              ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi))) := by
        rw [add_comm]

end SteinMethod
