/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonExch
import Formalization.Defs.PoissonStein
import Formalization.Defs.Couplings
import Formalization.Defs.Metrics

/-!
# Poisson Exchangeable Pairs — Basic Results (`Formalization.PoissonExch.Basic`)

Non-vacuity sanity witnesses for `Formalization.Defs.PoissonExch`, together with
Remark 4.19 (Poisson detailed balance and birth-death stationarity, `SteinIntro.tex:2633-2641`) and
Remark 4.18 (exchangeable jump probability equality, `SteinIntro.tex:2628-2632`)
from Section 4.4 of Nathan Ross, *"Fundamentals of Stein's method"*.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SteinMethod

/-! ### Non-vacuity sanity witnesses for `Formalization.Defs.PoissonExch` -/

/-- Non-vacuity witness for `condExpAt`: the conditional expectation of a constant function with
respect to any sub-σ-algebra `F ≤ mΩ` under a probability measure equals that constant. -/
theorem condExpAt_const {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {F : MeasurableSpace Ω} (hF : F ≤ mΩ) (c : ℝ) :
    condExpAt F mΩ P (fun _ ↦ c) = fun _ ↦ c :=
  condExp_const (m := F) (m₀ := mΩ) (μ := P) hF c

/-- Non-vacuity witness for `numFixedPoints`: the identity permutation on `Fin 3` has `3`
fixed points. -/
theorem numFixedPoints_one_fin3 : numFixedPoints (1 : Equiv.Perm (Fin 3)) = 3 := by
  decide

/-- Non-vacuity witness for `numFixedPoints`: the transposition `swap 0 1` on `Fin 3` has `1`
fixed point (`2`). -/
theorem numFixedPoints_swap_fin3 :
    numFixedPoints (Equiv.swap (0 : Fin 3) 1) = 1 := by
  decide

/-- Non-vacuity witness for `numTwoCycles`: the identity permutation on `Fin 3` has `0`
two-cycles. -/
theorem numTwoCycles_one_fin3 : numTwoCycles (1 : Equiv.Perm (Fin 3)) = 0 := by
  simp [numTwoCycles]

/-- Non-vacuity witness for `numTwoCycles`: the transposition `swap 0 1` on `Fin 3` has `1`
two-cycle. -/
theorem numTwoCycles_swap_fin3 :
    numTwoCycles (Equiv.swap (0 : Fin 3) 1) = 1 := by
  unfold numTwoCycles
  have hne : (0 : Fin 3) ≠ 1 := by decide
  rw [(Equiv.Perm.isCycle_swap hne).cycleFactorsFinset_eq_singleton, Finset.filter_singleton]
  have hsupp : (Equiv.swap (0 : Fin 3) 1).support.card = 2 :=
    Equiv.Perm.card_support_swap hne
  split_ifs
  exact Finset.card_singleton _

/-! ### Remark 4.19: Poisson detailed balance and birth-death stationarity -/

/-- The Poisson distribution satisfies the detailed balance equation
$\lambda \cdot \mathbb{P}(Z = k) = (k + 1) \cdot \mathbb{P}(Z = k + 1)$ for all $k \in \mathbb{N}$
(Remark 4.19, `SteinIntro.tex:2633-2641`). -/
theorem poisson_detailed_balance (r : ℝ≥0) (k : ℕ) :
    (r : ℝ) * (poissonLaw r).real {k} = (↑(k + 1)) * (poissonLaw r).real {k + 1} := by
  simp only [poissonLaw]
  rw [poissonMeasure_real_singleton r k, poissonMeasure_real_singleton r (k + 1),
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- Global balance (stationarity) for the birth-death process on $\mathbb{N}$ with birth rate
$\alpha(k) = \lambda$ and death rate $\beta(k) = k$ under $\pi = \mathrm{Po}(\lambda)$:
$\pi(0)\lambda = \pi(1)$ at $k = 0$ and
$\pi(k + 1)(\lambda + k + 1) = \lambda \pi(k) + (k + 2)\pi(k + 2)$ for all $k \in \mathbb{N}$
(Remark 4.19, `SteinIntro.tex:2635-2638`; `stmts-review-05H`). -/
theorem poisson_stationary_birth_death (r : ℝ≥0) :
    (poissonLaw r).real {0} * (r : ℝ) = (poissonLaw r).real {1} ∧
      ∀ k : ℕ,
        (poissonLaw r).real {k + 1} * ((r : ℝ) + ((k + 1 : ℕ) : ℝ)) =
          (r : ℝ) * (poissonLaw r).real {k} +
            ((k + 2 : ℕ) : ℝ) * (poissonLaw r).real {k + 2} := by
  refine ⟨?_, fun k ↦ ?_⟩
  · have h0 := poisson_detailed_balance r 0
    push_cast at h0
    linarith
  · have hk0 := poisson_detailed_balance r k
    have hk1 := poisson_detailed_balance r (k + 1)
    linarith

/-! ### Remark 4.18: Equal jump probabilities under exchangeability -/

/-- For an exchangeable pair $(W, W')$, $\mathbb{P}(W' = W + 1) = \mathbb{P}(W = W' + 1)$
(Remark 4.18, `SteinIntro.tex:2628-2632`). -/
theorem exchangeable_jump_prob_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℕ}
    (_hW : Measurable W) (_hW' : Measurable W')
    (hex : IsExchangeablePair P W W') :
    P.real {ω | W' ω = W ω + 1} = P.real {ω | W ω = W' ω + 1} := by
  have key := hex.measure_mem_eq (s := {p : ℕ × ℕ | p.2 = p.1 + 1})
    MeasurableSet.of_discrete
  simp only [Measure.real, Set.preimage, Set.mem_ofPred_eq] at key ⊢
  exact congr_arg ENNReal.toReal key

end SteinMethod
