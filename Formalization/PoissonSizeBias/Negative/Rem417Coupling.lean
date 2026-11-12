/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonSizeBias
import Formalization.PoissonSizeBias.Core.Basic
import Formalization.PoissonSizeBias.Negative.Basic
import Formalization.PoissonSizeBias.Negative.Hypergeometric
import Formalization.PoissonSizeBias.Negative.Occupancy

/-!
# Ball-in-Box Occupancy Couplings & Remark 4.17 (`Rem417Coupling`)

Formalizes the decreasing conditional couplings and Poisson approximation bounds for general
occupancy problems from **Remark 4.17** (`SteinIntro_utf8.tex:2593-2601`):

> \begin{remark}
> We could also consider the number of boxes with at most $m\geq 0$ balls; we just studied the
> case $m=0$.  The coupling is still
> decreasing because it can be constructed by first choosing a box randomly and if it has greater
> than $m$ balls in it, redistributing
> a random
> number of them among the other boxes.  Thus Theorem \ref{thm125} can be applied and an error in
> the Poisson approximation can
> be obtained in terms of the mean and the variance.  We again refer to Chapter 6 of \cite{bhj92}
> for the details.
>
> Finally, could also consider the number of boxes containing exactly $m\geq0$ balls and
> containing at least $m\geq1$ balls, Theorem \ref{thm122} applies to the latter problem.  See
> Chapter 6 of \cite{bhj92}.
> \end{remark}

## Source Issues & Clause Status

- `ISSUE-REM-4.17` (`SteinIntro_utf8.tex:2600`): The source asserts that Theorem 4.14
  (`\ref{thm122}`) applies to the number of boxes containing at least $m \ge 1$ balls. However,
  Theorem 4.14 requires an *increasing* coupling ($X_j^{(i)} \ge X_j$), whereas conditioning on
  box $i$ receiving at least $m \ge 1$ balls leaves fewer balls for the remaining boxes, making
  the indicators negatively related ($X_j^{(i)} \le X_j$). At $n = 2, k = 1, m = 1,
  p = (1/2, 1/2)$, the printed bound is $0 < e^{-1} \le d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1))$
  (and at $n = 3, k = 1, m = 1, p = (1/3, 1/3, 1/3)$ it evaluates to $-1/3 < 0$). The theorem that
  actually applies is **Theorem 4.19** (`\ref{thm125}`). Proved in `rem4_17_atLeast_corrected` and
  refuted in `not_rem4_17_atLeast_printed`.
- `ISSUE-TYPO-REM4.17` (`SteinIntro_utf8.tex:2600`): Line 2600 begins "Finally, could also
  consider" (missing "we").
- **Status of `"containing exactly m ≥ 0 balls"` (`SteinIntro_utf8.tex:2600`)**: For $m = 0$ this
  coincides with empty boxes (covered by `Rem4_17_atMost` at $m = 0$ and Examples 4.15–4.16). For
  $m \ge 1$, Ross makes no theorem or monotonicity assertion and refers to `[bhj92]` Chapter 6
  (conditioning on box $i$ containing *exactly* $m$ balls is neither increasing nor decreasing in
  general and is treated in `[bhj92]` §6.3 via general size-bias couplings / Corollary 4.10).

## Main Results

- `SteinMethod.rem4_17_atMost_stmt`: formal `Prop` asserting that for boxes with at most $m \ge 0$
  balls, a decreasing conditional coupling exists and Theorem 4.19 yields
  $d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
  \min\{1, \lambda\}(1 - \operatorname{Var}(W) / \lambda)$.
- `SteinMethod.rem4_17_atMost_holds`: proof witness for `rem4_17_atMost_stmt`, applying
  `rem4_17_atMost` from `Formalization.PoissonSizeBias.Negative.Occupancy`.
- `SteinMethod.rem4_17_atLeast_corrected_stmt`: formal `Prop` asserting that for boxes with at
  least $m \ge 1$ balls, a decreasing conditional coupling exists and Theorem 4.19 (`\ref{thm125}`)
  yields $d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
  \min\{1, \lambda\}(1 - \operatorname{Var}(W) / \lambda)$.
- `SteinMethod.rem4_17_atLeast_corrected_holds`: proof witness for
  `rem4_17_atLeast_corrected_stmt`, applying `rem4_17_atLeast_corrected` from
  `Formalization.PoissonSizeBias.Negative.Occupancy`.
- `SteinMethod.not_Rem4_17_atLeast_printed`: refutation theorem for the printed Theorem 4.14 claim.
- `SteinMethod.not_Ex4_13_var_printed`: alias for `not_ex4_13_var_printed` (`ISSUE-TYPO-4.13`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-- Remark 4.17, at-most-$m$-balls occupancy (`SteinIntro.tex:2594-2598`): when $k$ balls are
placed independently into $n$ boxes with probabilities $(p_1, \dots, p_n)$ ($\sum_i p_i = 1$,
$p_i \ge 0$), if $W$ is the number of boxes containing at most $m$ balls and
$\lambda = \mathbb{E}[W] > 0$, then a decreasing conditional coupling exists and Theorem 4.19
gives $d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
\min\{1, \lambda\}(1 - \operatorname{Var}(W) / \lambda)$. -/
def rem4_17_atMost_stmt : Prop :=
  ∀ {n k m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, 0 ≤ p i) →
    ∑ i : Fin n, p i = 1 →
    (∀ t : Fin k, Measurable (B t)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
    let X : Fin n → Ω → ℕ := fun i ω ↦
      if ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card ≤ m then 1 else 0
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond P {ω | X i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc)) ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ)))

/-- Proof witness for `SteinMethod.rem4_17_atMost_stmt` (`SteinIntro.tex:2594-2598`). -/
theorem rem4_17_atMost_holds : rem4_17_atMost_stmt := by
  intro n k m Ω Ω' mΩ mΩ' P hP P' hP' p B r Z hp_nn hp_sum hB_meas hB_indep hB_prob
    X W hr hmean hZ_meas hZ_law
  exact rem4_17_atMost P P' hp_nn hp_sum hB_meas hB_indep hB_prob hr hmean hZ_meas hZ_law

/-- Remark 4.17, corrected at-least-$m$-balls occupancy (`SteinIntro.tex:2600`; `ISSUE-REM-4.17`):
when $k$ balls are placed independently into $n$ boxes with probabilities $(p_1, \dots, p_n)$
($\sum_i p_i = 1$, $p_i \ge 0$), if $m \ge 1$, $W$ is the number of boxes containing at least $m$
balls, and $\lambda = \mathbb{E}[W] > 0$, then a decreasing conditional coupling exists and
Theorem 4.19 (`\ref{thm125}`, correcting the printed `\ref{thm122}` at `L2600`; see
`not_Rem4_17_atLeast_printed`) gives
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
\min\{1, \lambda\}(1 - \operatorname{Var}(W) / \lambda)$. -/
def rem4_17_atLeast_corrected_stmt : Prop :=
  ∀ {n k m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    1 ≤ m →
    (∀ i : Fin n, 0 ≤ p i) →
    ∑ i : Fin n, p i = 1 →
    (∀ t : Fin k, Measurable (B t)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
    let X : Fin n → Ω → ℕ := fun i ω ↦
      if m ≤ ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card then 1 else 0
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond P {ω | X i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc)) ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ)))

/-- Proof witness for `SteinMethod.rem4_17_atLeast_corrected_stmt` (`SteinIntro.tex:2600`). -/
theorem rem4_17_atLeast_corrected_holds : rem4_17_atLeast_corrected_stmt := by
  intro n k m Ω Ω' mΩ mΩ' P hP P' hP' p B r Z hm hp_nn hp_sum hB_meas hB_indep hB_prob
    X W hr hmean hZ_meas hZ_law
  exact rem4_17_atLeast_corrected P P' hm hp_nn hp_sum hB_meas hB_indep hB_prob hr hmean hZ_meas
    hZ_law

/-- Refutation of the printed Theorem 4.14 (`\ref{thm122}`) claim in Remark 4.17
(`SteinIntro.tex:2600`; `ISSUE-REM-4.17`): for the number $W$ of boxes containing at least
$m \ge 1$ balls, Theorem 4.14's bound
$\min\{1, \lambda^{-1}\}(\operatorname{Var}(W) - \lambda + 2 \sum_{i=1}^n q_i^2)$ fails (e.g. at
$n = 2, k = 1, m = 1, p = (1/2, 1/2)$, where the bound is $0 < e^{-1} \le
d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1))$). -/
theorem not_Rem4_17_atLeast_printed :
    ¬ (∀ {n k m : ℕ}
        {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
        1 ≤ m →
        (∀ i : Fin n, 0 ≤ p i) →
        ∑ i : Fin n, p i = 1 →
        (∀ t : Fin k, Measurable (B t)) →
        ProbabilityTheory.iIndepFun B P →
        (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
        let X : Fin n → Ω → ℕ := fun i ω ↦
          if m ≤ ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card then 1 else 0
        let q : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
        let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
        0 < r →
        (r : ℝ) = ∑ i : Fin n, q i →
        AEMeasurable Z P' →
        P'.map Z = poissonLaw r →
        tvDist (P.map W) (P'.map Z) ≤
          ENNReal.ofReal
            (min 1 (r : ℝ)⁻¹ *
              (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
                2 * ∑ i : Fin n, (q i) ^ 2))) :=
  not_rem4_17_atLeast_printed

/-- Alias for `not_Rem4_17_atLeast_printed`. -/
alias not_rem4_17_atLeast_printed_holds := not_Rem4_17_atLeast_printed

/-- PascalCase alias for `not_ex4_13_var_printed` (`SteinIntro.tex:2500`; `ISSUE-TYPO-4.13`). -/
alias not_Ex4_13_var_printed := not_ex4_13_var_printed

end SteinMethod
