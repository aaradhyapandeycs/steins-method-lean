/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonSizeBias
import Formalization.PoissonSizeBias.Core.Basic
import Formalization.PoissonSizeBias.Negative.Basic
import Formalization.PoissonSizeBias.Negative.Occupancy
import Formalization.PoissonSizeBias.Negative.CouponNonUniform

/-!
# Non-Uniform Coupon Collecting Size-Bias Coupling (`Ex416Coupling`)

Formalizes the non-uniform coupon collecting size-bias coupling from **Example 4.16**
(`SteinIntro_utf8.tex:2581-2587`):

> Corollary \ref{cor121} now states that in order
> to construct $W^s$, we empty box $I$ (forcing $X_I^s=1$) and then redistribute the balls
> that were removed into the remaining
> boxes independently and with chance of landing in box $j$ equal to $p_j/(1-p_I)$.  If we let
> $X_j^{(I)}$ be the indicator that box $j$ is empty
> after this procedure, then it is clear that $(X_j^{(I)})_{j\not=I}$ has the distribution of
> $(X_j)_{j\not=I}$ conditional on $X_I=1$
> so that we can take $W^s=\sum_{j\not=I}X_j^{(I)} +1$.

and the monotonicity relation (`SteinIntro_utf8.tex:2588`):

> Analogous to Example \ref{ex123}, $X_j^{(i)}\leq X_j$ for  $j\not=i$ so that we can apply
> Theorem \ref{thm125}.

## Main Results

- `SteinMethod.ex4_16_sizeBias_stmt`: formal `Prop` stating that the non-uniform redistribution
  procedure yields indicators $(X_j^{(i)})_{j \ne i}$ with the conditional distribution of
  $(X_j)_{j \ne i}$ given $X_i = 1$ whenever $p_i < 1$, satisfies pointwise monotonicity
  $X_j^{(i)} \le X_j$, and with $I \sim \pi_i / \lambda$ (where $\pi_i = (1 - p_i)^k$) gives a
  valid size-bias coupling $W^s = \sum_{j \ne I} X_j^{(I)} + 1$ of $W = \sum_{i=1}^n X_i$.
- `SteinMethod.ex4_16_sizeBias_holds`: proof witness for `ex4_16_sizeBias_stmt`, applying
  `ex4_16_sizeBias` from `Formalization.PoissonSizeBias.Negative.CouponNonUniform`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-- Example 4.16, non-uniform redistribution size-bias coupling (`[Coupon collecting continued]`,
`SteinIntro.tex:2581-2587`): for $k$ balls placed independently into $n$ boxes with probabilities
$(p_1, \dots, p_n)$ ($\sum_i p_i = 1$, $p_i \ge 0$), redirecting each ball in box $i$ ($p_i < 1$)
independently to box $j \ne i$ with probability $p_j / (1 - p_i)$ yields indicators
$(X_j^{(i)})_{j \ne i}$ with the conditional law of $(X_j)_{j \ne i}$ given $X_i = 1$, satisfies
$X_j^{(i)} \le X_j$ everywhere, and with independent index $I$
($\mathbb{P}(I = i) = (1 - p_i)^k / \lambda$) gives a size-bias coupling
$W^s = \sum_{j \ne I} X_j^{(I)} + 1$ of $W = \sum_{i=1}^n X_i$. -/
def ex4_16_sizeBias_stmt : Prop :=
  ∀ {n k : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n}
    {R : (i : Fin n) → Fin k → Ω → {j : Fin n // j ≠ i}}
    {I : Ω → Fin n} {r : ℝ≥0},
    (∀ i : Fin n, 0 ≤ p i) →
    ∑ i : Fin n, p i = 1 →
    (∀ t : Fin k, Measurable (B t)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
    (∀ (i : Fin n) (t : Fin k), Measurable (R i t)) →
    (∀ i : Fin n, p i < 1 → ProbabilityTheory.iIndepFun (R i) P) →
    (∀ i : Fin n, p i < 1 → ∀ t : Fin k, ∀ j : {j : Fin n // j ≠ i},
      P.real {ω | R i t ω = j} = p j.1 / (1 - p i)) →
    (∀ i : Fin n, p i < 1 →
      ProbabilityTheory.IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ R i t ω) P) →
    Measurable I →
    (r : ℝ) = ∑ i : Fin n, (1 - p i) ^ k →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = (1 - p i) ^ k / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun t ↦ B t ω, fun i t ↦ R i t ω)) P →
    let B' : (i : Fin n) → Fin k → Ω → Fin n :=
      fun i t ω ↦ if B t ω = i then (R i t ω).1 else B t ω
    let X : Fin n → Ω → ℕ := fun i ω ↦ if ∀ t : Fin k, B t ω ≠ i then 1 else 0
    let X' : (i : Fin n) → {j : Fin n // j ≠ i} → Ω → ℕ :=
      fun i j ω ↦ if ∀ t : Fin k, B' i t ω ≠ j.1 then 1 else 0
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω : ℝ)
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, (X' (I ω) j ω : ℝ)) + 1
    (∀ i : Fin n, p i < 1 →
      P.map (fun ω (j : {j : Fin n // j ≠ i}) ↦ X' i j ω) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i}, X' i j ω ≤ X j.1 ω) ∧
      IsSizeBias P W P Ws

/-- Proof witness for `SteinMethod.ex4_16_sizeBias_stmt` (`SteinIntro.tex:2581-2587`). -/
theorem ex4_16_sizeBias_holds : ex4_16_sizeBias_stmt := by
  intro n k Ω mΩ P hP p B R I r hp_nn hp_sum hB_meas hB_indep hB_prob hR_meas hR_indep hR_prob
    hBR_indep hI_meas hr_eq hI_prob hI_indep B' X X' W Ws
  exact ex4_16_sizeBias P hp_nn hp_sum hB_meas hB_indep hB_prob hR_meas hR_indep hR_prob
    hBR_indep hI_meas hr_eq hI_prob hI_indep

end SteinMethod
