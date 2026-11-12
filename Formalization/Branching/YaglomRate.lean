/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Branching.AuxSpine
import Formalization.Branching.SizeBiasTree
import Formalization.Exponential.MetricBounds
import Mathlib.Analysis.Normed.Group.Tannery
/-!
# Section 5.3: Yaglom's Theorem and Convergence Rate (`Formalization.Branching.YaglomRate`)

This file formalizes the spine coupling discrepancy bounds, Kolmogorov survival asymptotic, and
Yaglom's theorem (`Theorem 5.8` and `Theorem 5.9`) from Section 5.3 ("Application: Critical
branching process") of N. Ross, *Fundamentals of Stein's method*, `SteinIntro.tex` lines
`3007–3029` and `3140–3189`:

* `sec5_3_eq_3143_corrected : Sec5_3_eq_3143_corrected` (`SteinIntro.tex:3142-3145`,
  `ISSUE-TYPO-5.3c`): corrected coupling difference $Y_n - Y_n^e = U + \sum_{j=1}^n (R_{n,j}' -
  R_{n,j}) \mathbf{1}_{L_{n,j} > 0}$ and triangle inequality (re-exported from `AuxYaglomSteps`).
* `sec5_3_neg_corr_3158_and_3160_corrected : Sec5_3_neg_corr_3158_and_3160_corrected`
  (`SteinIntro.tex:3158-3164`, `ISSUE-5.9-proof`): negative correlation of $S_{n,j}$ and
  $\mathbf{1}_{L_{n,j} = 0}$ and corrected conditional expectation chain
  $\mathbb{E}[R_{n,j}'] = \mathbb{E}[R_{n,j} \mid L_{n,j} = 0] =
  \mathbb{E}[S_{n,j} \mid L_{n,j} = 0] \le \mathbb{E}[S_{n,j}] = \sigma^2$.
* `sec5_3_step_i : Sec5_3_step_i` (`SteinIntro.tex:3148, 3154-3164`):
  $\mathbb{E}[R_{n,j}' \mathbf{1}_{L_{n,j} > 0}] = \mathbb{E}[R_{n,j}'] \mathbb{P}(L_{n,j} > 0) \le
  \sigma^2 \mathbb{P}(L_{n,j} > 0)$.
* `sec5_3_step_ii : Sec5_3_step_ii` (`SteinIntro.tex:3149-3150, 3166-3177`):
  $\mathbb{E}[R_{n,j} \mathbf{1}_{L_{n,j} > 0}] \le \mathbb{E}[X_j \mathbf{1}_{L_{n,j} > 0}] \le
  \mathbb{E}[Z_1^3]\,\mathbb{P}(Z_{n-j} > 0)$ (re-exported from `AuxYaglomSteps`).
* `sec5_3_step_iii : Sec5_3_step_iii` (`SteinIntro.tex:3151, 3179-3187`):
  $\mathbb{P}(L_{n,j} > 0) \le \sigma^2 \mathbb{P}(Z_{n-j} > 0) \le C (n - j + 1)^{-1}$.
* `sec5_3_lpp_mean_diff_o_n : Sec5_3_lpp_mean_diff_o_n` (`SteinIntro.tex:3027`):
  $\lim_{n \to \infty} \mathbb{E}|Y_n - Y_n^e| / n = 0$ under $\operatorname{Var}(Z_1) < \infty$.
* `sec5_3_kolmogorov_survival_restricted : Sec5_3_kolmogorov_survival_restricted`
  (`SteinIntro.tex:3028, 3185-3186`, `ISSUE-5.8`):
  $\lim_{n \to \infty} n\,\mathbb{P}(Z_n > 0) = 2 / \sigma^2$ for $\sigma^2 > 0$.
* `sec5_3_lpp_mean_diff_log_restricted : Sec5_3_lpp_mean_diff_log_restricted`
  (`SteinIntro.tex:3022-3023, 3140-3145`, `ISSUE-5.9`):
  $\mathbb{E}|Y_n - Y_n^e| \le C \log(n)$ for $n \ge 2$ under $\mathbb{E}|Z_1|^3 < \infty$.
* `thm5_8_restricted : Thm5_8_restricted` and `thm5_9_restricted : Thm5_9_restricted`:
  Yaglom's theorem in Kolmogorov distance (`Theorem 5.8`) and $O(\log(n)/n)$ Wasserstein rate
  (`Theorem 5.9`).
* `not_Thm5_8_printed : ¬ Thm5_8` and `not_Thm5_9_printed : ¬ Thm5_9`: counterexamples refuting the
  literal printed statements when $\sigma^2 = 0$ or $n = 1$.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-!
### 1. Statement Definitions (`docs/tracks/I.md`)
-/

/-- Section 5.3 corrected coupling difference and triangle inequality (`I-6`,
`SteinIntro.tex:3142-3145`; `ISSUE-TYPO-5.3c`): with $Y_n = R_n^*$ and $Y_n^e = R_n - U$,
$Y_n - Y_n^e = U + \sum_{j=1}^n (R_{n,j}' - R_{n,j})\mathbf{1}_{L_{n,j} > 0}$ (not $1 - U + \dots$
as printed), and
$|Y_n - Y_n^e| \le |U| + \sum_{j=1}^n R_{n,j}' \mathbf{1}_{L_{n,j} > 0} +
\sum_{j=1}^n R_{n,j} \mathbf{1}_{L_{n,j} > 0}$. -/
def Sec5_3_eq_3143_corrected_stmt : Prop :=
  ∀ {Ω' : Type*} (n : ℕ) (L R R' : ℕ → Ω' → ℕ) (U : Ω' → ℝ) (ω' : Ω'),
    let Yn : ℝ :=
      1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
    let Yne : ℝ := (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
    Yn - Yne =
      U ω' + ∑ j ∈ Finset.Icc 1 n,
        ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∧
    |Yn - Yne| ≤
      |U ω'| +
        (∑ j ∈ Finset.Icc 1 n, (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') +
        (∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω')

/-- Section 5.3 negative correlation of $S_{n,j}$ and $\mathbf{1}_{L_{n,j} = 0}$ (`L3158`) and
corrected conditional expectation chain (`L3160-3163`; `ISSUE-5.9-proof`, `I-8`): for every
$j \in \{1, \dots, n\}$, $\mathbb{E}[S_{n,j} \mathbf{1}_{L_{n,j} = 0}] \le
\mathbb{E}[S_{n,j}]\,\mathbb{P}(L_{n,j} = 0)$, $\mathbb{E}[R_{n,j}'] =
\mathbb{E}[R_{n,j} \mid L_{n,j} = 0] = \mathbb{E}[S_{n,j} \mid L_{n,j} = 0] \le
\mathbb{E}[S_{n,j}] = \sigma^2$, and $\mathbb{E}[S_n] - 1 = n \sigma^2$. -/
def Sec5_3_neg_corr_3158_and_3160_corrected_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    IsSizeBiasSpineCoupling P Z P' n X L R R' U →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    let Snj : ℕ → Ω' → ℝ := fun j ω' ↦ (L j ω' : ℝ) + (R j ω' : ℝ)
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, Snj j ω'
    (∫ ω', Sn ω' ∂P') - 1 = (n : ℝ) * σsq ∧
    ∀ j ∈ Finset.Icc 1 n,
      ∫ ω', Snj j ω' * {ω'' : Ω' | L j ω'' = 0}.indicator 1 ω' ∂P' ≤
        (∫ ω', Snj j ω' ∂P') * P'.real {ω' | L j ω' = 0} ∧
      ∫ ω', (R' j ω' : ℝ) ∂P' =
        ∫ ω', (R j ω' : ℝ) ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) ∧
      ∫ ω', (R j ω' : ℝ) ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) =
        ∫ ω', Snj j ω' ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) ∧
      ∫ ω', Snj j ω' ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) ≤
        ∫ ω', Snj j ω' ∂P' ∧
      ∫ ω', Snj j ω' ∂P' = σsq

/-- Section 5.3 spine step bound (i) (`SteinIntro.tex:3148, 3154-3164`; `ISSUE-5.9-proof`): in a
critical Galton–Watson process with $\operatorname{Var}(Z_1) = \sigma^2 < \infty$, for every
$j \in \{1, \dots, n\}$,
$\mathbb{E}[R_{n,j}' \mathbf{1}_{L_{n,j} > 0}] = \mathbb{E}[R_{n,j}'] \mathbb{P}(L_{n,j} > 0) \le
\sigma^2 \mathbb{P}(L_{n,j} > 0)$. -/
def Sec5_3_step_i_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    IsSizeBiasSpineCoupling P Z P' n X L R R' U →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    ∀ j ∈ Finset.Icc 1 n,
      ∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' =
        (∫ ω', (R' j ω' : ℝ) ∂P') * P'.real {ω' | 0 < L j ω'} ∧
      ∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        σsq * P'.real {ω' | 0 < L j ω'}

/-- Section 5.3 spine step bound (ii) (`SteinIntro.tex:3149-3150, 3166-3177`; `I-9`): in a
critical Galton–Watson process with $\mathbb{E}[Z_1^3] < \infty$, for every
$j \in \{1, \dots, n\}$,
$\mathbb{E}[R_{n,j} \mathbf{1}_{L_{n,j} > 0}] \le \mathbb{E}[X_j \mathbf{1}_{L_{n,j} > 0}] \le
\mathbb{E}[Z_1^3]\,\mathbb{P}(Z_{n-j} > 0)$. -/
def Sec5_3_step_ii_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P →
    IsSizeBiasSpine P Z P' n X L R →
    ∀ j ∈ Finset.Icc 1 n,
      ∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        ∫ ω', (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ∧
      ∫ ω', (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        (∫ ω, (Z 1 ω : ℝ) ^ 3 ∂P) * P.real {ω | 0 < Z (n - j) ω}

/-- Section 5.3 spine step bound (iii) (`SteinIntro.tex:3151, 3179-3187`; `I-3`): in a critical
Galton–Watson process with $\operatorname{Var}(Z_1) = \sigma^2 < \infty$, there exists $C > 0$
(depending only on the process) such that for all $n \ge 1$ and $j \in \{1, \dots, n\}$,
$\mathbb{P}(L_{n,j} > 0) \le \sigma^2 \mathbb{P}(Z_{n-j} > 0) \le C (n - j + 1)^{-1}$. -/
def Sec5_3_step_iii_stmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    (∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      {n : ℕ} {X L R : ℕ → Ω' → ℕ},
      IsSizeBiasSpine P Z P' n X L R →
      ∀ j ∈ Finset.Icc 1 n,
        P'.real {ω' | 0 < L j ω'} ≤ σsq * P.real {ω | 0 < Z (n - j) ω}) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j ∈ Finset.Icc 1 n,
      σsq * P.real {ω | 0 < Z (n - j) ω} ≤ C * ((n - j + 1 : ℕ) : ℝ)⁻¹

/-- Section 5.3 Lyons–Pemantle–Peres $o(n)$ coupling discrepancy (`I-3`,
`SteinIntro.tex:3027`): for a critical Galton–Watson process with
$\operatorname{Var}(Z_1) < \infty$, the coupled variables $(Y_n, Y_n^e)$ satisfy
$\lim_{n \to \infty} \mathbb{E}|Y_n - Y_n^e| / n = 0$. -/
def Sec5_3_lpp_mean_diff_o_n_stmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ}
    {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (P' : ∀ n, Measure (Ω' n)) [∀ n, IsProbabilityMeasure (P' n)]
    {X L R R' : ∀ n, ℕ → Ω' n → ℕ} {U : ∀ n, Ω' n → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    (∀ n : ℕ, 1 ≤ n → IsSizeBiasSpineCoupling P Z (P' n) n (X n) (L n) (R n) (R' n) (U n)) →
    let Yn : ∀ n, Ω' n → ℝ := fun n ω' ↦
      1 + ∑ j ∈ Finset.Icc 1 n, (if L n j ω' = 0 then (R n j ω' : ℝ) else (R' n j ω' : ℝ))
    let Yne : ∀ n, Ω' n → ℝ := fun n ω' ↦
      (1 + ∑ j ∈ Finset.Icc 1 n, (R n j ω' : ℝ)) - U n ω'
    Filter.Tendsto (fun n : ℕ ↦ (∫ ω', |Yn n ω' - Yne n ω'| ∂P' n) / (n : ℝ))
      Filter.atTop (nhds 0)

/-- Section 5.3 Kolmogorov survival asymptotic, restricted to $\sigma^2 > 0$ (`I-5`,
`SteinIntro.tex:3028, 3185-3186`; `ISSUE-5.8`): for a critical Galton–Watson process with
$0 < \sigma^2 = \operatorname{Var}(Z_1) < \infty$,
$\lim_{n \to \infty} n\,\mathbb{P}(Z_n > 0) = 2 / \sigma^2$. -/
def Sec5_3_kolmogorov_survival_restricted_stmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * P.real {ω | 0 < Z n ω})
      Filter.atTop (nhds (2 / σsq))

/-- Section 5.3 logarithmic coupling discrepancy bound, restricted to $n \ge 2$ (`I-3`, `I-4`,
`SteinIntro.tex:3022-3023, 3140-3145`; `ISSUE-5.9`): for a critical Galton–Watson process with
$\mathbb{E}|Z_1|^3 < \infty$, there exists a constant $C$ such that for all $n \ge 2$, the coupled
variables $(Y_n, Y_n^e)$ satisfy $\mathbb{E}|Y_n - Y_n^e| \le C \log(n)$. -/
def Sec5_3_lpp_mean_diff_log_restricted_stmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P →
    ∃ C : ℝ, ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
      2 ≤ n →
      IsSizeBiasSpineCoupling P Z P' n X L R R' U →
      let Yn : Ω' → ℝ := fun ω' ↦
        1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
      let Yne : Ω' → ℝ := fun ω' ↦
        (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
      ∫ ω', |Yn ω' - Yne ω'| ∂P' ≤ C * Real.log (n : ℝ)

/-- Theorem 5.8 (Yaglom's Theorem), as printed without $\sigma^2 > 0$ (`SteinIntro.tex:3007-3013`;
`ISSUE-5.8`, `I-10`): ill-defined when $\sigma^2 = \operatorname{Var}(Z_1) = 0$ due to division by
$0$ in $2 Y_n / (n \sigma^2)$ (and refuted under Lean's `x / 0 = 0` convention by
`not_Thm5_8_printed`). See `Thm5_8_restricted` for the valid statement with $\sigma^2 > 0$. -/
def Thm5_8 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {Zexp : Ω' → ℝ}
    {ΩY : ℕ → Type*} [∀ n, MeasurableSpace (ΩY n)]
    (PY : ∀ n, Measure (ΩY n)) [∀ n, IsProbabilityMeasure (PY n)]
    {Y : ∀ n, ΩY n → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    (∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Y n) (PY n) ∧
      (PY n).map (Y n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n)) →
    AEMeasurable Zexp P' →
    P'.map Zexp = stdExpLaw →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    Filter.Tendsto
      (fun n : ℕ ↦
        kolmogorovDist
          ((PY n).map (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq)))
          (P'.map Zexp))
      Filter.atTop
      (nhds 0)

/-- Theorem 5.8 (Yaglom's Theorem), restricted to $\sigma^2 = \operatorname{Var}(Z_1) > 0$
(`SteinIntro.tex:3007-3013`; `ISSUE-5.8`): if $(Z_n)_{n \ge 0}$ is a Galton–Watson branching
process with $\mathbb{E}[Z_1] = 1$ and $0 < \sigma^2 = \operatorname{Var}(Z_1) < \infty$,
$Y_n \stackrel{d}{=} (Z_n \mid Z_n > 0)$, and $Z \sim \mathrm{Exp}(1)$, then
$\lim_{n \to \infty} d_{\mathrm{K}}(\mathcal{L}(2 Y_n / (n \sigma^2)), \mathcal{L}(Z)) = 0$. -/
def Thm5_8_restricted_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {Zexp : Ω' → ℝ}
    {ΩY : ℕ → Type*} [∀ n, MeasurableSpace (ΩY n)]
    (PY : ∀ n, Measure (ΩY n)) [∀ n, IsProbabilityMeasure (PY n)]
    {Y : ∀ n, ΩY n → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P →
    (∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Y n) (PY n) ∧
      (PY n).map (Y n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n)) →
    AEMeasurable Zexp P' →
    P'.map Zexp = stdExpLaw →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    Filter.Tendsto
      (fun n : ℕ ↦
        kolmogorovDist
          ((PY n).map (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq)))
          (P'.map Zexp))
      Filter.atTop
      (nhds 0)

/-- Theorem 5.9, as printed for $n \ge 1$ (`SteinIntro.tex:3015-3020`; `ISSUE-5.9`, `I-10`):
fails at $n = 1$ even when $\sigma^2 > 0$ because $\log(1) = 0$ makes the right-hand side
$C \log(1)/1 = 0$ while $d_{\mathrm{W}}(\mathcal{L}(2 Y_1 / \sigma^2), \mathrm{Exp}(1)) > 0$
(refuted by `not_Thm5_9_printed`). See `Thm5_9_restricted` for the valid statement with
$\sigma^2 > 0$ and $n \ge 2$. -/
def Thm5_9 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {Zexp : Ω' → ℝ}
    {ΩY : ℕ → Type*} [∀ n, MeasurableSpace (ΩY n)]
    (PY : ∀ n, Measure (ΩY n)) [∀ n, IsProbabilityMeasure (PY n)]
    {Y : ∀ n, ΩY n → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P →
    0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P →
    (∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Y n) (PY n) ∧
      (PY n).map (Y n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n)) →
    AEMeasurable Zexp P' →
    P'.map Zexp = stdExpLaw →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      wassersteinDist
        ((PY n).map (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq)))
        (P'.map Zexp) ≤
        ENNReal.ofReal (C * Real.log (n : ℝ) / (n : ℝ))

/-- Theorem 5.9, restricted to $\sigma^2 = \operatorname{Var}(Z_1) > 0$ and $n \ge 2$
(`SteinIntro.tex:3015-3020`; `ISSUE-5.9`): if $(Z_n)_{n \ge 0}$ is a Galton–Watson branching
process with $\mathbb{E}[Z_1] = 1$, $0 < \sigma^2 = \operatorname{Var}(Z_1) < \infty$, and
$\mathbb{E}|Z_1|^3 < \infty$, $Y_n \stackrel{d}{=} (Z_n \mid Z_n > 0)$, and
$Z \sim \mathrm{Exp}(1)$, then there exists a constant $C$ such that for all $n \ge 2$,
$d_{\mathrm{W}}(\mathcal{L}(2 Y_n / (n \sigma^2)), \mathcal{L}(Z)) \le C \log(n) / n$. -/
def Thm5_9_restricted_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {Zexp : Ω' → ℝ}
    {ΩY : ℕ → Type*} [∀ n, MeasurableSpace (ΩY n)]
    (PY : ∀ n, Measure (ΩY n)) [∀ n, IsProbabilityMeasure (PY n)]
    {Y : ∀ n, ΩY n → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P →
    0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P →
    (∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Y n) (PY n) ∧
      (PY n).map (Y n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n)) →
    AEMeasurable Zexp P' →
    P'.map Zexp = stdExpLaw →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      wassersteinDist
        ((PY n).map (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq)))
        (P'.map Zexp) ≤
        ENNReal.ofReal (C * Real.log (n : ℝ) / (n : ℝ))


theorem integrable_iff_summable_and_integral_eq_tsum {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg_nn : ∀ a, 0 ≤ g a) :
    (Integrable g μ ↔ Summable (fun a ↦ g a * μ.real {a})) ∧
      (Summable (fun a ↦ g a * μ.real {a}) →
        ∫ a, g a ∂μ = ∑' a, g a * μ.real {a}) := by
  have hg_meas : Measurable g := Measurable.of_discrete
  have hlint :
      ∫⁻ a, ENNReal.ofReal (g a) ∂μ = ∑' a, ENNReal.ofReal (g a * μ.real {a}) := by
    rw [lintegral_countable']
    exact tsum_congr fun a ↦ by
      rw [ENNReal.ofReal_mul (hg_nn a), ofReal_measureReal (measure_ne_top μ {a})]
  have hnorm_eq : (∫⁻ a, ‖g a‖ₑ ∂μ) = ∫⁻ a, ENNReal.ofReal (g a) ∂μ :=
    lintegral_congr fun a ↦ Real.enorm_eq_ofReal (hg_nn a)
  have hint_iff : Integrable g μ ↔ Summable (fun a ↦ g a * μ.real {a}) := by
    rw [Integrable, and_iff_right hg_meas.aestronglyMeasurable, HasFiniteIntegral, hnorm_eq, hlint]
    refine ⟨fun hlt ↦ ENNReal.summable_toReal hlt.ne |>.congr fun a ↦
      ENNReal.toReal_ofReal (mul_nonneg (hg_nn a) measureReal_nonneg), fun hsum ↦ ?_⟩
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun a ↦ mul_nonneg (hg_nn a) measureReal_nonneg) hsum]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint_iff, fun hsum ↦ ?_⟩
  have hof := ofReal_integral_eq_lintegral_ofReal (hint_iff.mpr hsum) (Eventually.of_forall hg_nn)
  rw [hlint, ← ENNReal.ofReal_tsum_of_nonneg
    (fun a ↦ mul_nonneg (hg_nn a) measureReal_nonneg) hsum] at hof
  have h := congrArg ENNReal.toReal hof
  rwa [ENNReal.toReal_ofReal (integral_nonneg hg_nn),
    ENNReal.toReal_ofReal (tsum_nonneg fun a ↦ mul_nonneg (hg_nn a) measureReal_nonneg)] at h

theorem integral_nat_func_eq_tsum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℕ} (hX : AEMeasurable X P)
    {g : ℕ → ℝ} (hg_nn : ∀ d, 0 ≤ g d) (hInt : Integrable (fun ω ↦ g (X ω)) P) :
    Summable (fun d : ℕ ↦ g d * P.real {ω | X ω = d}) ∧
      ∫ ω, g (X ω) ∂P = ∑' d : ℕ, g d * P.real {ω | X ω = d} := by
  set μX := P.map X
  have : IsProbabilityMeasure μX := (Measure.isProbabilityMeasure_map_iff hX).mpr ‹_›
  have hg_m : Measurable g := Measurable.of_discrete
  have hp_eq : ∀ d : ℕ, P.real {ω | X ω = d} = μX.real {d} := fun d ↦
    (map_measureReal_apply_of_aemeasurable hX (measurableSet_singleton d)).symm
  have hsum_μ := (integrable_iff_summable_and_integral_eq_tsum μX hg_nn).1.mp
    ((integrable_map_measure hg_m.aestronglyMeasurable hX).mpr hInt)
  have hsum : Summable (fun d : ℕ ↦ g d * P.real {ω | X ω = d}) :=
    hsum_μ.congr fun d ↦ by rw [hp_eq d]
  refine ⟨hsum, ?_⟩
  rw [← integral_map hX hg_m.aestronglyMeasurable,
    (integrable_iff_summable_and_integral_eq_tsum μX hg_nn).2 hsum_μ]
  exact tsum_congr fun d ↦ by rw [hp_eq d]

theorem probReal_le_one' {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (s : Set α) : P.real s ≤ 1 :=
  (measureReal_mono (subset_univ s) (measure_ne_top P univ)).trans_eq probReal_univ

theorem IsGaltonWatson.prob_pos_eq_one_sub {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (n : ℕ) :
    P.real {ω | 0 < Z n ω} = 1 - P.real {ω | Z n ω = 0} := by
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  have h0_ae : ({ω | Z n ω = 0} : Set Ω) =ᵐ[P] (gwCanonical ξ' n ⁻¹' {0}) :=
    Filter.eventuallyEqSet_iff.mpr ((hZ_ae n).mono fun _ hω ↦ by simp [mem_preimage, hω])
  have hc : ({ω | 0 < Z n ω} : Set Ω) = {ω | Z n ω = 0}ᶜ := by ext ω; simp; omega
  rw [hc, probReal_compl_eq_one_sub₀
    ((measurable_gwCanonical hξ'_meas n (measurableSet_singleton 0)).nullMeasurableSet.congr
      h0_ae.symm)]

lemma one_sub_pow_le_mul_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ m : ℕ, 0 ≤ (m : ℝ) * (1 - q) - (1 - q ^ m)
  | 0 => by simp
  | m + 1 => by
      have ih := one_sub_pow_le_mul_one_sub hq0 hq1 m
      have hid : ((m + 1 : ℕ) : ℝ) * (1 - q) - (1 - q ^ (m + 1)) =
          q * ((m : ℝ) * (1 - q) - (1 - q ^ m)) + (m : ℝ) * (1 - q) ^ 2 := by push_cast; ring
      rw [hid]; positivity

lemma avg_pow_bdd_and_one_sub_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (d : ℕ) :
    let v : ℝ := (∑ a ∈ Finset.range (d + 1), q ^ a) / ((d : ℝ) + 1)
    0 ≤ v ∧ v ≤ 1 ∧ 1 - v ≤ (d : ℝ) * (1 - q) := by
  intro v
  refine ⟨div_nonneg (Finset.sum_nonneg fun a _ ↦ pow_nonneg hq0 a) (by positivity),
    (div_le_one (by positivity)).mpr ((Finset.sum_le_sum fun a _ ↦ pow_le_one₀ hq0 hq1).trans_eq
      (by simp)), ?_⟩
  dsimp only [v]
  rw [sub_le_comm, le_div_iff₀ (by positivity)]
  have hsum : ∑ a ∈ Finset.range (d + 1), (1 - q ^ a) ≤
      ∑ _ ∈ Finset.range (d + 1), (d : ℝ) * (1 - q) :=
    Finset.sum_le_sum fun a ha ↦ by
      have h1 := one_sub_pow_le_mul_one_sub hq0 hq1 a
      have ha_le : (a : ℝ) ≤ (d : ℝ) :=
        Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))
      nlinarith [sub_nonneg.mpr hq1]
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  push_cast at hsum ⊢; linarith

/-- **Section 5.3 corrected coupling difference and triangle inequality** (`I-6`,
`SteinIntro.tex:3142-3145`; `ISSUE-TYPO-5.3c`). -/
theorem sec5_3_eq_3143_corrected {Ω' : Type*} (n : ℕ) (L R R' : ℕ → Ω' → ℕ)
    (U : Ω' → ℝ) (ω' : Ω') :
    let Yn : ℝ :=
      1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
    let Yne : ℝ := (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
    Yn - Yne =
      U ω' + ∑ j ∈ Finset.Icc 1 n,
        ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∧
    |Yn - Yne| ≤
      |U ω'| +
        (∑ j ∈ Finset.Icc 1 n, (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') +
        (∑ j ∈ Finset.Icc 1 n,
          (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') := by
  intro Yn Yne
  have hterm : ∀ j : ℕ,
      (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ)) - (R j ω' : ℝ) =
        ((R' j ω' : ℝ) - (R j ω' : ℝ)) *
          {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' := fun j ↦ by
    by_cases h0 : L j ω' = 0
    · simp [h0]
    · simp [h0, Nat.pos_of_ne_zero h0]
  have hdiff : Yn - Yne = U ω' + ∑ j ∈ Finset.Icc 1 n,
      ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' := by
    have hsum_eq : (∑ j ∈ Finset.Icc 1 n,
        (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))) -
        (∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) =
        ∑ j ∈ Finset.Icc 1 n,
          ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ ↦ hterm j
    dsimp only [Yn, Yne]; linarith
  refine ⟨hdiff, ?_⟩
  rw [hdiff]
  have h1 := abs_add_le (U ω') (∑ j ∈ Finset.Icc 1 n,
    ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω')
  have h2 := Finset.abs_sum_le_sum_abs
    (fun j ↦ ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω')
    (Finset.Icc 1 n)
  have h3 : ∑ j ∈ Finset.Icc 1 n,
      |((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω'| ≤
      (∑ j ∈ Finset.Icc 1 n, (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') +
        (∑ j ∈ Finset.Icc 1 n,
          (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have hind_nn : 0 ≤ ({ω'' : Ω' | 0 < L j ω''}.indicator (1 : Ω' → ℝ) ω') :=
      indicator_nonneg (fun _ _ ↦ zero_le_one) ω'
    rw [abs_mul, abs_of_nonneg hind_nn, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hind_nn
    have hsub := abs_sub (R' j ω' : ℝ) (R j ω' : ℝ)
    have hR' : |(R' j ω' : ℝ)| = (R' j ω' : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    have hR : |(R j ω' : ℝ)| = (R j ω' : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    linarith
  linarith

lemma chebyshev_tsum_prob {u v w : ℕ → ℝ}
    (hu_nn : ∀ k, 0 ≤ u k) (hu_mono : Monotone u)
    (hv_nn : ∀ k, 0 ≤ v k) (hv_bdd : ∀ k, v k ≤ 1) (hv_anti : Antitone v)
    (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : Summable w) (hw_one : ∑' k, w k = 1)
    (huw_sum : Summable (fun k ↦ u k * w k)) :
    ∑' k, u k * v k * w k ≤ (∑' k, u k * w k) * (∑' k, v k * w k) := by
  classical
  have hvw_sum : Summable (fun k ↦ v k * w k) :=
    Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hv_nn k) (hw_nn k))
      (fun k ↦ mul_le_of_le_one_left (hw_nn k) (hv_bdd k)) hw_sum
  have huvw_sum : Summable (fun k ↦ u k * v k * w k) :=
    Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (mul_nonneg (hu_nn k) (hv_nn k)) (hw_nn k))
      (fun k ↦ by
        calc u k * v k * w k = v k * (u k * w k) := by ring
          _ ≤ 1 * (u k * w k) :=
              mul_le_mul_of_nonneg_right (hv_bdd k) (mul_nonneg (hu_nn k) (hw_nn k))
          _ = u k * w k := one_mul _) huw_sum
  set V : ℝ := ∑' k, v k * w k
  have hex : ∃ d, v d ≤ V := by
    by_contra hall; push Not at hall
    obtain ⟨d₁, hd₁⟩ : ∃ d₁, 0 < w d₁ := by
      by_contra hw0; push Not at hw0
      have h0 : ∀ d, w d = 0 := fun d ↦ le_antisymm (hw0 d) (hw_nn d)
      simp [h0] at hw_one
    have hlt := (hw_sum.mul_left V).tsum_lt_tsum (i := d₁)
      (fun d ↦ mul_le_mul_of_nonneg_right (hall d).le (hw_nn d))
      (mul_lt_mul_of_pos_right (hall d₁) hd₁) hvw_sum
    rw [tsum_mul_left, hw_one, mul_one] at hlt; exact lt_irrefl V hlt
  let d₀ := Nat.find hex
  have hterm : ∀ d, u d * v d * w d + u d₀ * V * w d ≤
      V * (u d * w d) + u d₀ * (v d * w d) := fun d ↦ by
    have hp : (u d - u d₀) * (v d - V) ≤ 0 := by
      rcases lt_or_ge d d₀ with hlt | hge
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hu_mono hlt.le))
          (sub_nonneg.mpr (le_of_not_ge (Nat.find_min hex hlt)))
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hu_mono hge))
          (sub_nonpos.mpr ((hv_anti hge).trans (Nat.find_spec hex)))
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hp (hw_nn d)]
  have hsL := huvw_sum.add (hw_sum.mul_left (u d₀ * V))
  have hsR := (huw_sum.mul_left V).add (hvw_sum.mul_left (u d₀))
  have hle := hsL.tsum_le_tsum hterm hsR
  rw [huvw_sum.tsum_add (hw_sum.mul_left _), tsum_mul_left, hw_one, mul_one,
    (huw_sum.mul_left V).tsum_add (hvw_sum.mul_left _), tsum_mul_left, tsum_mul_left] at hle
  change ∑' k, u k * v k * w k + u d₀ * V ≤ V * (∑' k, u k * w k) + u d₀ * V at hle
  linarith

/-- Core level-$j$ spine formulas conditioned on $(X_j, A_j)$. -/
theorem spine_level_identities {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n j : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hGW : IsGaltonWatson P Z) (hmean : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hSpine : IsSizeBiasSpine P Z P' n X L R) (hj : j ∈ Finset.Icc 1 n) :
    let q : ℝ := P.real {ω | Z (n - j) ω = 0}
    let v : ℕ → ℝ := fun d ↦ (∑ a ∈ Finset.range (d + 1), q ^ a) / ((d : ℝ) + 1)
    let pX : ℕ → ℝ := fun d ↦ P'.real {ω' | X j ω' = d}
    AEMeasurable (L j) P' ∧ AEMeasurable (R j) P' ∧
    (∃ S₀ : Set Ω', MeasurableSet S₀ ∧ ({ω' | L j ω' = 0} : Set Ω') =ᵐ[P'] S₀) ∧
    (∃ S₁ : Set Ω', MeasurableSet S₁ ∧ ({ω' | 0 < L j ω'} : Set Ω') =ᵐ[P'] S₁) ∧
    0 < P'.real {ω' | L j ω' = 0} ∧
    (∀ d : ℕ, pX d = ((d + 1 : ℕ) : ℝ) * P.real {ω | Z 1 ω = d + 1}) ∧
    Summable pX ∧ (∑' d : ℕ, pX d = 1) ∧
    P'.real {ω' | L j ω' = 0} = ∑' d : ℕ, v d * pX d ∧
    P'.real {ω' | 0 < L j ω'} = ∑' d : ℕ, (1 - v d) * pX d ∧
    (MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
      Integrable (fun ω' ↦ (X j ω' : ℝ)) P' ∧
      Integrable (fun ω' ↦ (L j ω' : ℝ) + (R j ω' : ℝ)) P' ∧
      Summable (fun d : ℕ ↦ (d : ℝ) * pX d) ∧
      (∫ ω', (X j ω' : ℝ) ∂P' =
        ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P) ∧
      (∫ ω', ((L j ω' : ℝ) + (R j ω' : ℝ)) ∂P' =
        ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P) ∧
      (∫ ω', ((L j ω' : ℝ) + (R j ω' : ℝ)) *
          {ω'' | L j ω'' = 0}.indicator 1 ω' ∂P' ≤
        ∑' d : ℕ, (d : ℝ) * v d * pX d) ∧
      (∫ ω', (R j ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        ∫ ω', (X j ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω' ∂P') ∧
      (∫ ω', (X j ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω' ∂P' =
        ∑' d : ℕ, (d : ℝ) * (1 - v d) * pX d)) := by
  intro q v pX
  obtain ⟨X_w, A_w, L_w, R_w, ξ_w, _, hlvl⟩ := hSpine.exists_measurable_witness
  rcases hlvl j hj with ⟨hX₀_m, hA₀_m, hL₀_m, hR₀_m, hξ₀_m, hX_ae, hL_ae, hR_ae, hSB_X,
    hAX_le, hXA_pmf, hξ₀_ind, hξ₀_law, hXA₀_ind, hL₀_def, hR₀_def⟩
  set X₀ := X_w j; set A₀ := A_w j; set L₀ := L_w j; set R₀ := R_w j; set ξ₀ := ξ_w j
  have hpX₀_congr : ∀ d : ℕ, P'.real {ω' | X₀ ω' = d} = pX d := fun d ↦
    measureReal_congr (Filter.eventuallyEqSet_iff.mpr (hX_ae.symm.mono fun _ h ↦ by simp [h]))
  have hpX_eq : ∀ d : ℕ, pX d =
      ((d + 1 : ℕ) : ℝ) * P.real {ω | Z 1 ω = d + 1} := fun d ↦ by
    have h1 := hSB_X.measureReal_eq_singleton
      (by rw [hmean]; exact zero_lt_one) ((d + 1 : ℕ) : ℝ)
    rw [hmean, div_one] at h1
    have hs1 : {ω' : Ω' | (X₀ ω' : ℝ) + 1 = ((d + 1 : ℕ) : ℝ)} =
        {ω' | X₀ ω' = d} := by ext ω'; norm_cast; simp
    have hs2 : {ω : Ω | (Z 1 ω : ℝ) = ((d + 1 : ℕ) : ℝ)} = {ω | Z 1 ω = d + 1} := by
      ext ω; exact Nat.cast_inj
    rw [hs1, hs2, hpX₀_congr d] at h1; exact h1
  have htonelli : ∀ {F : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞}, Measurable F →
      ∫⁻ ω', F ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') ∂P' =
        ∑' d : ℕ, ∑ a ∈ Finset.range (d + 1),
          (∫⁻ ω', F ((d, a), fun r ↦ ξ₀ r ω') ∂P') *
            ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) := fun {F} hF ↦ by
    let tupξ : Ω' → ℕ → ℕ := fun ω' r ↦ ξ₀ r ω'
    have htup_m : Measurable tupξ := measurable_pi_iff.mpr hξ₀_m
    set μXA := P'.map (fun ω' ↦ (X₀ ω', A₀ ω'))
    set μξ := P'.map tupξ
    have : IsProbabilityMeasure μXA :=
      (Measure.isProbabilityMeasure_map_iff (hX₀_m.prodMk hA₀_m).aemeasurable).mpr ‹_›
    have : IsProbabilityMeasure μξ :=
      (Measure.isProbabilityMeasure_map_iff htup_m.aemeasurable).mpr ‹_›
    change ∫⁻ ω', F ((X₀ ω', A₀ ω'), tupξ ω') ∂P' = _
    rw [← lintegral_map hF ((hX₀_m.prodMk hA₀_m).prodMk htup_m),
      hXA₀_ind.map_prod_eq_prod_map_map (hX₀_m.prodMk hA₀_m).aemeasurable htup_m.aemeasurable,
      lintegral_prod F hF.aemeasurable, lintegral_countable', ENNReal.tsum_prod']
    refine tsum_congr fun d ↦ ?_
    have hμXA_eq : ∀ a : ℕ, μXA {(d, a)} =
        if a ≤ d then ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) else 0 := fun a ↦ by
      have hpre : ((fun ω' ↦ (X₀ ω', A₀ ω')) ⁻¹' {(d, a)} : Set Ω') =
          {ω' | X₀ ω' = d ∧ A₀ ω' = a} := by ext; simp
      rw [← ofReal_measureReal (measure_ne_top μXA {(d, a)}),
        map_measureReal_apply (hX₀_m.prodMk hA₀_m) (measurableSet_singleton (d, a)),
        hpre, hXA_pmf d a, hpX₀_congr d, hpX_eq d]
      split_ifs with had
      · congr 1
        have hne : (d : ℝ) + 1 ≠ 0 := by positivity
        push_cast; exact mul_div_cancel_left₀ _ hne
      · simp
    rw [tsum_eq_sum (s := Finset.range (d + 1)) fun a ha ↦ by
      rw [hμXA_eq a]; split_ifs with had
      · exfalso; simp only [Finset.mem_range, not_lt] at ha; omega
      · simp]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have had : a ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [hμXA_eq a, ite_eq_left_iff.mpr fun h ↦ absurd had h,
      lintegral_map (f := fun y ↦ F ((d, a), y))
        (hF.comp (measurable_const.prodMk measurable_id)) htup_m]
  have hL0_ae : ({ω' | L j ω' = 0} : Set Ω') =ᵐ[P'] (L₀ ⁻¹' {0}) :=
    Filter.eventuallyEqSet_iff.mpr (hL_ae.mono fun _ h ↦ by simp [mem_preimage, h])
  have hLpos_ae : ({ω' | 0 < L j ω'} : Set Ω') =ᵐ[P'] (L₀ ⁻¹' Ioi 0) :=
    Filter.eventuallyEqSet_iff.mpr (hL_ae.mono fun _ h ↦ by simp [mem_preimage, h])
  have hX_aem : AEMeasurable (X j) P' := hX₀_m.aemeasurable.congr hX_ae.symm
  obtain ⟨hpX_sum', htsum_pX'⟩ := integral_nat_func_eq_tsum hX_aem
    (fun _ : ℕ ↦ zero_le_one) (integrable_const (1 : ℝ))
  have hpX_sum : Summable pX := hpX_sum'.congr fun d ↦ one_mul _
  have htsum_pX : ∑' d : ℕ, pX d = 1 := by simpa [one_mul] using htsum_pX'.symm
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := probReal_le_one' P _
  have hv_bdd : ∀ d, 0 ≤ v d ∧ v d ≤ 1 := fun d ↦
    ⟨(avg_pow_bdd_and_one_sub_le hq0 hq1 d).1, (avg_pow_bdd_and_one_sub_le hq0 hq1 d).2.1⟩
  have hξ₀_lint_one : ∀ r, ∫⁻ ω', (ξ₀ r ω' : ℝ≥0∞) ∂P' = 1 := fun r ↦ by
    have hc := (IdentDistrib.mk (hξ₀_m r).aemeasurable (hGW.aemeasurable_Z (n - j))
      (hξ₀_law r)).comp (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ))
    have h1 := ofReal_integral_eq_lintegral_ofReal
      (hc.symm.integrable_snd (hGW.integrable_Z (n - j)))
      (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)
    rw [hc.integral_eq.trans (hGW.integral_Z_eq_one hmean (n - j)), ENNReal.ofReal_one] at h1
    exact (lintegral_congr fun _ ↦ (ENNReal.ofReal_natCast _).symm).trans h1.symm
  let prefSum : ℕ → Ω' → ℕ := fun a ω' ↦ ∑ r ∈ Finset.range a, ξ₀ r ω'
  have hpref_m : ∀ a, Measurable (prefSum a) :=
    fun a ↦ Finset.measurable_sum _ fun r _ ↦ hξ₀_m r
  have hprod_q : ∀ a : ℕ, P'.real (prefSum a ⁻¹' {0}) = q ^ a := fun a ↦ by
    have hind_eq : ((prefSum a ⁻¹' {0}).indicator (1 : Ω' → ℝ)) =
        fun ω' ↦ ∏ i : Finset.range a,
          (({0} : Set ℕ).indicator (1 : ℕ → ℝ)) (ξ₀ i.1 ω') := by
      ext ω'
      by_cases h0 : prefSum a ω' = 0
      · rw [indicator_of_mem (show ω' ∈ prefSum a ⁻¹' {0} from h0), Pi.one_apply,
          Finset.prod_eq_one fun i _ ↦ by
            rw [indicator_of_mem (mem_singleton_iff.mpr ((Finset.sum_eq_zero_iff.mp h0) i.1 i.2))]
            rfl]
      · obtain ⟨i₀, hi₀⟩ : ∃ i : Finset.range a, ξ₀ i.1 ω' ≠ 0 := by
          by_contra hall; push Not at hall
          exact h0 (Finset.sum_eq_zero fun r hr ↦ hall ⟨r, hr⟩)
        rw [indicator_of_notMem (show ω' ∉ prefSum a ⁻¹' {0} from h0),
          Finset.prod_eq_zero (Finset.mem_univ i₀)
            (indicator_of_notMem (mt mem_singleton_iff.mp hi₀) _)]
    rw [← integral_indicator_one (hpref_m a (measurableSet_singleton 0)), hind_eq,
      (hξ₀_ind.precomp Subtype.val_injective).integral_fun_prod_comp
        (fun i ↦ (hξ₀_m i.1).aemeasurable)
        (fun _ ↦ Measurable.of_discrete.aestronglyMeasurable)]
    have hfac : ∀ i : Finset.range a,
        ∫ ω', (({0} : Set ℕ).indicator (1 : ℕ → ℝ))
          (ξ₀ i.1 ω') ∂P' = q := fun i ↦ by
      have h1 := congrArg (fun μ : Measure ℕ ↦ μ.real {0}) (hξ₀_law i.1)
      rw [map_measureReal_apply (hξ₀_m i.1) (measurableSet_singleton 0),
        map_measureReal_apply_of_aemeasurable (hGW.aemeasurable_Z (n - j))
          (measurableSet_singleton 0)] at h1
      exact (integral_indicator_one (hξ₀_m i.1 (measurableSet_singleton 0))).trans h1
    rw [Finset.prod_congr rfl fun i _ ↦ hfac i]; simp
  let fLsum : (ℕ × ℕ) × (ℕ → ℕ) → ℕ := fun z ↦ ∑ r ∈ Finset.range z.1.2, z.2 r
  let fRsum : (ℕ × ℕ) × (ℕ → ℕ) → ℕ :=
    fun z ↦ ∑ r ∈ Finset.Ico z.1.2 z.1.1, z.2 r
  have hm_Lsum : Measurable fLsum :=
    measurable_sum_range_nat (measurable_snd.comp measurable_fst)
      fun r ↦ (measurable_pi_apply r).comp measurable_snd
  have hm_Rsum : Measurable fRsum :=
    measurable_sum_Ico_nat (measurable_snd.comp measurable_fst)
      (measurable_fst.comp measurable_fst) fun r ↦ (measurable_pi_apply r).comp measurable_snd
  have hmem_L : ∀ (S : Set ℕ) (ω' : Ω'),
      ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') ∈ fLsum ⁻¹' S ↔ ω' ∈ L₀ ⁻¹' S :=
    fun S ω' ↦ by simp [fLsum, mem_preimage, hL₀_def ω']
  have hX_bochner : ∀ (g : ℕ → ℝ) (S : Set ℕ), (∀ d, 0 ≤ g d) → MeasurableSet S →
      Summable (fun d : ℕ ↦ g d * pX d) → Integrable (fun ω' ↦ g (X₀ ω')) P' →
      ∫ ω', g (X₀ ω') * (L₀ ⁻¹' S).indicator 1 ω' ∂P' =
        ∑' d : ℕ, g d *
          ((∑ a ∈ Finset.range (d + 1), P'.real (prefSum a ⁻¹' S)) /
            ((d : ℝ) + 1)) * pX d := by
    intro g S hg_nn hS hgpX_sum hg_int
    let FX : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞ := fun z ↦
      (fLsum ⁻¹' S).indicator (fun z' ↦ ENNReal.ofReal (g z'.1.1)) z
    have htX := htonelli (((Measurable.of_discrete :
      Measurable fun d : ℕ ↦ ENNReal.ofReal (g d)).comp
        (measurable_fst.comp measurable_fst)).indicator (hm_Lsum hS))
    have hlX : ∫⁻ ω', FX ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') ∂P' =
        ∫⁻ ω', ENNReal.ofReal (g (X₀ ω') * (L₀ ⁻¹' S).indicator 1 ω') ∂P' :=
      lintegral_congr fun ω' ↦ by
        by_cases hm : ω' ∈ L₀ ⁻¹' S
        · rw [indicator_of_mem hm, Pi.one_apply, mul_one]; dsimp only [FX]
          exact indicator_of_mem ((hmem_L S ω').mpr hm) _
        · rw [indicator_of_notMem hm, mul_zero, ENNReal.ofReal_zero]; dsimp only [FX]
          exact indicator_of_notMem (mt (hmem_L S ω').mp hm) _
    have hdX : ∀ d : ℕ, ∑ a ∈ Finset.range (d + 1),
        (∫⁻ ω', FX ((d, a), fun r ↦ ξ₀ r ω') ∂P') *
          ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) =
        ENNReal.ofReal (g d *
          ((∑ a ∈ Finset.range (d + 1), P'.real (prefSum a ⁻¹' S)) /
            ((d : ℝ) + 1)) * pX d) := by
      intro d
      have hcell : ∀ a : ℕ, ∫⁻ ω', FX ((d, a), fun r ↦ ξ₀ r ω') ∂P' =
          ENNReal.ofReal (P'.real (prefSum a ⁻¹' S) * g d) := fun a ↦ by
        have hfX : (fun ω' ↦ FX ((d, a), fun r ↦ ξ₀ r ω')) =
            (prefSum a ⁻¹' S).indicator (fun _ ↦ ENNReal.ofReal (g d)) :=
          funext fun _ ↦ rfl
        rw [hfX, lintegral_indicator (hpref_m a hS), setLIntegral_const, mul_comm,
          ← ofReal_measureReal (measure_ne_top P' _), ENNReal.ofReal_mul measureReal_nonneg]
      simp_rw [hcell]
      have hmul : ∀ a ∈ Finset.range (d + 1),
          ENNReal.ofReal (P'.real (prefSum a ⁻¹' S) * g d) *
            ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) =
          ENNReal.ofReal (g d * P'.real (prefSum a ⁻¹' S) * P.real {ω | Z 1 ω = d + 1}) :=
        fun a _ ↦ by
          rw [← ENNReal.ofReal_mul (mul_nonneg measureReal_nonneg (hg_nn d))]; ring_nf
      rw [Finset.sum_congr rfl hmul,
        ← ENNReal.ofReal_sum_of_nonneg fun a _ ↦
          mul_nonneg (mul_nonneg (hg_nn d) measureReal_nonneg) measureReal_nonneg,
        ← Finset.sum_mul, ← Finset.mul_sum, hpX_eq d]
      congr 1
      have hne : (d : ℝ) + 1 ≠ 0 := by positivity
      push_cast; field_simp
    have hw_bdd : ∀ d : ℕ,
        0 ≤ (∑ a ∈ Finset.range (d + 1), P'.real (prefSum a ⁻¹' S)) / ((d : ℝ) + 1) ∧
          (∑ a ∈ Finset.range (d + 1), P'.real (prefSum a ⁻¹' S)) /
            ((d : ℝ) + 1) ≤ 1 := fun d ↦
      ⟨div_nonneg (Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg) (by positivity),
        (div_le_one (by positivity)).mpr
          ((Finset.sum_le_sum fun a _ ↦ probReal_le_one' P' _).trans_eq (by simp))⟩
    have hd_sum : Summable (fun d : ℕ ↦ g d *
        ((∑ a ∈ Finset.range (d + 1), P'.real (prefSum a ⁻¹' S)) /
          ((d : ℝ) + 1)) * pX d) :=
      Summable.of_nonneg_of_le
        (fun d ↦ mul_nonneg (mul_nonneg (hg_nn d) (hw_bdd d).1) measureReal_nonneg)
        (fun d ↦ by
          calc g d * _ * pX d = _ * (g d * pX d) := by ring
            _ ≤ 1 * (g d * pX d) := mul_le_mul_of_nonneg_right (hw_bdd d).2
                (mul_nonneg (hg_nn d) measureReal_nonneg)
            _ = g d * pX d := one_mul _) hgpX_sum
    have hint_ind : Integrable (fun ω' ↦ g (X₀ ω') * (L₀ ⁻¹' S).indicator 1 ω') P' :=
      hg_int.mono' (((Measurable.of_discrete : Measurable g).comp hX₀_m).mul
        (measurable_one.indicator (hL₀_m hS))).aestronglyMeasurable
        (Eventually.of_forall fun ω' ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg_nn _)
            (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _))]
          by_cases hm : ω' ∈ L₀ ⁻¹' S <;> simp [hm, hg_nn])
    have hof := (ofReal_integral_eq_lintegral_ofReal hint_ind
      (Eventually.of_forall fun _ ↦ mul_nonneg (hg_nn _)
        (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _))).trans
          (hlX.symm.trans (htX.trans (tsum_congr hdX)))
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun d ↦ mul_nonneg (mul_nonneg (hg_nn d) (hw_bdd d).1) measureReal_nonneg) hd_sum] at hof
    have h := congrArg ENNReal.toReal hof
    rwa [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ mul_nonneg (hg_nn _)
      (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _)),
      ENNReal.toReal_ofReal (tsum_nonneg fun d ↦
        mul_nonneg (mul_nonneg (hg_nn d) (hw_bdd d).1) measureReal_nonneg)] at h
  have hv_sum : Summable (fun d : ℕ ↦ v d * pX d) :=
    Summable.of_nonneg_of_le (fun d ↦ mul_nonneg (hv_bdd d).1 measureReal_nonneg)
      (fun d ↦ mul_le_of_le_one_left measureReal_nonneg (hv_bdd d).2) hpX_sum
  have hL0_prob : P'.real {ω' | L j ω' = 0} = ∑' d : ℕ, v d * pX d := by
    have h1 := hX_bochner (fun _ ↦ 1) {0} (fun _ ↦ zero_le_one) (measurableSet_singleton 0)
      (hpX_sum.congr fun d ↦ (one_mul _).symm) (integrable_const 1)
    simp_rw [one_mul, hprod_q] at h1
    rw [measureReal_congr hL0_ae,
      ← integral_indicator_one (hL₀_m (measurableSet_singleton 0)), h1]
  have hLpos_prob : P'.real {ω' | 0 < L j ω'} = ∑' d : ℕ, (1 - v d) * pX d := by
    have hcompl : ({ω' | 0 < L j ω'} : Set Ω') = {ω' | L j ω' = 0}ᶜ := by ext; simp; omega
    conv_lhs => rw [hcompl, probReal_compl_eq_one_sub₀
      ((hL₀_m (measurableSet_singleton 0)).nullMeasurableSet.congr hL0_ae.symm),
      hL0_prob, ← htsum_pX, ← hpX_sum.tsum_sub hv_sum]
    exact tsum_congr fun d ↦ by change pX d - v d * pX d = (1 - v d) * pX d; ring
  have hL0_pos : 0 < P'.real {ω' | L j ω' = 0} := by
    obtain ⟨d, hd⟩ : ∃ d, 0 < pX d := by
      by_contra hall; push Not at hall
      have h0 : ∀ d, pX d = 0 := fun d ↦ le_antisymm (hall d) measureReal_nonneg
      simp [h0] at htsum_pX
    have hvd_pos : 0 < v d := div_pos (by
      rw [Finset.sum_range_succ']
      exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun a _ ↦ pow_nonneg hq0 _) (by simp))
      (by positivity)
    rw [hL0_prob]
    exact lt_of_lt_of_le (mul_pos hvd_pos hd)
      (hv_sum.le_tsum d fun k _ ↦ mul_nonneg (hv_bdd k).1 measureReal_nonneg)
  refine ⟨hL₀_m.aemeasurable.congr hL_ae.symm, hR₀_m.aemeasurable.congr hR_ae.symm,
    ⟨L₀ ⁻¹' {0}, hL₀_m (measurableSet_singleton 0), hL0_ae⟩,
    ⟨L₀ ⁻¹' Ioi 0, hL₀_m measurableSet_Ioi, hLpos_ae⟩,
    hL0_pos, hpX_eq, hpX_sum, htsum_pX, hL0_prob, hLpos_prob, fun h2 ↦ ?_⟩
  classical
  set σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
  have hZ21 : Integrable (fun ω ↦ (Z 1 ω : ℝ) ^ 2) P :=
    (memLp_two_iff_integrable_sq hGW.1.aestronglyMeasurable).mp h2
  have hZ1_sq : ∫ ω, (Z 1 ω : ℝ) ^ 2 ∂P = 1 + σsq := by
    have hv := ProbabilityTheory.variance_eq_sub h2
    change σsq = (∫ ω, (Z 1 ω : ℝ) ^ 2 ∂P) - (∫ ω, (Z 1 ω : ℝ) ∂P) ^ 2 at hv
    rw [hmean, one_pow] at hv; linarith
  have hX₀_int : Integrable (fun ω' ↦ (X₀ ω' : ℝ)) P' := by
    have hInt1 : Integrable (fun ω' ↦ (X₀ ω' : ℝ) + 1) P' :=
      hSB_X.integrable_comp_of_pos_mean (by rw [hmean]; exact zero_lt_one) measurable_id
        (by simpa [sq] using hZ21)
    exact (hInt1.sub (integrable_const 1)).congr
      (Eventually.of_forall fun _ ↦ add_sub_cancel_right _ _)
  have hX_int : Integrable (fun ω' ↦ (X j ω' : ℝ)) P' :=
    hX₀_int.congr (hX_ae.symm.mono fun _ h ↦ congrArg Nat.cast h)
  have hX_mean : ∫ ω', (X j ω' : ℝ) ∂P' = σsq := by
    rw [integral_congr_ae (hX_ae.mono fun _ h ↦ congrArg Nat.cast h)]
    have hexp : (fun ω ↦ (Z 1 ω : ℝ) * ((Z 1 ω : ℝ) - 1)) =
        fun ω ↦ (Z 1 ω : ℝ) ^ 2 - (Z 1 ω : ℝ) := by ext; ring
    have h1 := hSB_X.2.2.2 (fun x ↦ x - 1) (measurable_id.sub measurable_const)
      (hexp ▸ hZ21.sub hGW.1)
    rw [hexp, integral_sub hZ21 hGW.1, hZ1_sq, hmean] at h1
    simp only [add_sub_cancel_right, one_mul] at h1; linarith [h1]
  obtain ⟨hdpX_sum, hdpX_tsum'⟩ := integral_nat_func_eq_tsum hX_aem Nat.cast_nonneg hX_int
  have hdpX_tsum : ∑' d : ℕ, (d : ℝ) * pX d = σsq := hdpX_tsum'.symm.trans hX_mean
  have hSnj_lint : ∫⁻ ω', ((L₀ ω' : ℝ≥0∞) + (R₀ ω' : ℝ≥0∞)) ∂P' = ENNReal.ofReal σsq := by
    have hLR_sum : ∀ ω', (L₀ ω' : ℝ≥0∞) + (R₀ ω' : ℝ≥0∞) =
        ∑ r ∈ Finset.range (X₀ ω'), (ξ₀ r ω' : ℝ≥0∞) := fun ω' ↦ by
      rw [← Nat.cast_add, hL₀_def ω', hR₀_def ω',
        Finset.sum_range_add_sum_Ico _ (hAX_le ω'), Nat.cast_sum]
    have h1 := htonelli
      (F := fun z : (ℕ × ℕ) × (ℕ → ℕ) ↦ ((∑ r ∈ Finset.range z.1.1, z.2 r : ℕ) : ℝ≥0∞))
      ((Measurable.of_discrete : Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp
        (measurable_sum_range_nat (measurable_fst.comp measurable_fst)
          fun r ↦ (measurable_pi_apply r).comp measurable_snd))
    have hd_eq : ∀ d : ℕ, ∑ a ∈ Finset.range (d + 1),
        (∫⁻ ω', ((∑ r ∈ Finset.range d, ξ₀ r ω' : ℕ) : ℝ≥0∞) ∂P') *
          ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) =
        ENNReal.ofReal ((d : ℝ) * pX d) := fun d ↦ by
      have ha_eq : ∫⁻ ω', ((∑ r ∈ Finset.range d, ξ₀ r ω' : ℕ) : ℝ≥0∞) ∂P' = d := by
        simp_rw [Nat.cast_sum]
        rw [lintegral_finsetSum (Finset.range d) (f := fun r ω' ↦ (ξ₀ r ω' : ℝ≥0∞)) fun r _ ↦
          ((Measurable.of_discrete : Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp (hξ₀_m r))]
        simp [hξ₀_lint_one]
      simp_rw [ha_eq, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast (d + 1), ← ENNReal.ofReal_natCast d,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hpX_eq d]
      congr 1; ring
    simp_rw [hLR_sum, ← Nat.cast_sum]; rw [h1]; simp_rw [hd_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun d ↦ mul_nonneg (Nat.cast_nonneg d) measureReal_nonneg) hdpX_sum, hdpX_tsum]
  have hcast_m : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  have hSnj_ae : (fun ω' ↦ (L₀ ω' : ℝ) + (R₀ ω' : ℝ)) =ᵐ[P']
      fun ω' ↦ (L j ω' : ℝ) + (R j ω' : ℝ) :=
    (hL_ae.symm.and hR_ae.symm).mono fun _ ⟨h1, h2⟩ ↦ by simp [h1, h2]
  have hSnj₀_int : Integrable (fun ω' ↦ (L₀ ω' : ℝ) + (R₀ ω' : ℝ)) P' :=
    ⟨((hcast_m.comp hL₀_m).add (hcast_m.comp hR₀_m)).aestronglyMeasurable, by
      rw [HasFiniteIntegral]
      have heq : (fun ω' ↦ ‖(L₀ ω' : ℝ) + (R₀ ω' : ℝ)‖ₑ) =
          fun ω' ↦ (L₀ ω' : ℝ≥0∞) + (R₀ ω' : ℝ≥0∞) := by
        ext ω'; rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_add (Nat.cast_nonneg _)
          (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
      rw [heq, hSnj_lint]; exact ENNReal.ofReal_lt_top⟩
  have hSnj_mean : ∫ ω', ((L j ω' : ℝ) + (R j ω' : ℝ)) ∂P' = σsq := by
    rw [← integral_congr_ae hSnj_ae]
    have h := congrArg ENNReal.toReal ((ofReal_integral_eq_lintegral_ofReal hSnj₀_int
      (Eventually.of_forall fun _ ↦ by positivity)).trans
      (by simpa [ENNReal.ofReal_add (Nat.cast_nonneg _) (Nat.cast_nonneg _)] using hSnj_lint))
    rwa [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ by positivity),
      ENNReal.toReal_ofReal (ProbabilityTheory.variance_nonneg _ P)] at h
  have hRX_bochner_le : ∀ (S : Set ℕ), MeasurableSet S →
      ∫ ω', (R₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω' ∂P' ≤
        ∫ ω', (X₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω' ∂P' := fun S hS ↦ by
    let FR : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞ :=
      (fLsum ⁻¹' S).indicator fun z ↦ (fRsum z : ℝ≥0∞)
    let FX : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞ :=
      (fLsum ⁻¹' S).indicator fun z ↦ (z.1.1 : ℝ≥0∞)
    have htR := htonelli (F := FR) (((Measurable.of_discrete :
      Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp hm_Rsum).indicator (hm_Lsum hS))
    have htX := htonelli (F := FX) (((Measurable.of_discrete :
      Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp
        (measurable_fst.comp measurable_fst)).indicator (hm_Lsum hS))
    have hlR :
        ∫⁻ ω', ENNReal.ofReal ((R₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω') ∂P' =
          ∫⁻ ω', FR ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') ∂P' := lintegral_congr fun ω' ↦ by
      dsimp only [FR]; by_cases hm : ω' ∈ L₀ ⁻¹' S
      · rw [indicator_of_mem hm, indicator_of_mem ((hmem_L S ω').mpr hm), Pi.one_apply, mul_one,
          ENNReal.ofReal_natCast, hR₀_def ω']
      · rw [indicator_of_notMem hm, indicator_of_notMem (mt (hmem_L S ω').mp hm), mul_zero,
          ENNReal.ofReal_zero]
    have hlX :
        ∫⁻ ω', ENNReal.ofReal ((X₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω') ∂P' =
          ∫⁻ ω', FX ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') ∂P' := lintegral_congr fun ω' ↦ by
      dsimp only [FX]; by_cases hm : ω' ∈ L₀ ⁻¹' S
      · rw [indicator_of_mem hm, indicator_of_mem ((hmem_L S ω').mpr hm), Pi.one_apply, mul_one,
          ENNReal.ofReal_natCast]
      · rw [indicator_of_notMem hm, indicator_of_notMem (mt (hmem_L S ω').mp hm), mul_zero,
          ENNReal.ofReal_zero]
    have hcell_le : ∀ d a : ℕ,
        ∫⁻ ω', FR ((d, a), fun r ↦ ξ₀ r ω') ∂P' ≤
          ∫⁻ ω', FX ((d, a), fun r ↦ ξ₀ r ω') ∂P' := by
      intro d a
      have hmS : MeasurableSet (prefSum a ⁻¹' S) := hpref_m a hS
      have hfR : (fun ω' ↦ FR ((d, a), fun r ↦ ξ₀ r ω')) = fun ω' ↦
          ((prefSum a ⁻¹' S).indicator (1 : Ω' → ℝ≥0∞) ω') *
            ∑ r ∈ Finset.Ico a d, (ξ₀ r ω' : ℝ≥0∞) := by
        ext ω'; dsimp only [FR, fRsum]
        by_cases hm : ω' ∈ prefSum a ⁻¹' S
        · rw [indicator_of_mem (show ((d, a), fun r ↦ ξ₀ r ω') ∈ fLsum ⁻¹' S from hm),
            indicator_of_mem hm, Pi.one_apply, one_mul, Nat.cast_sum]
        · rw [indicator_of_notMem (show ((d, a), fun r ↦ ξ₀ r ω') ∉ fLsum ⁻¹' S from hm),
            indicator_of_notMem hm, zero_mul]
      have hfX : (fun ω' ↦ FX ((d, a), fun r ↦ ξ₀ r ω')) =
          (prefSum a ⁻¹' S).indicator (fun _ ↦ (d : ℝ≥0∞)) := funext fun _ ↦ rfl
      rw [hfR, hfX, lintegral_indicator hmS, setLIntegral_const, mul_comm]
      simp_rw [Finset.mul_sum]
      rw [lintegral_finsetSum (Finset.Ico a d)
        (f := fun i ω' ↦ ((prefSum a ⁻¹' S).indicator (1 : Ω' → ℝ≥0∞) ω') * (ξ₀ i ω' : ℝ≥0∞))
        fun r _ ↦ ((measurable_const : Measurable (1 : Ω' → ℝ≥0∞)).indicator hmS).mul
          ((Measurable.of_discrete : Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp (hξ₀_m r))]
      have hr_eq : ∀ r ∈ Finset.Ico a d,
          ∫⁻ ω', ((prefSum a ⁻¹' S).indicator (1 : Ω' → ℝ≥0∞) ω') *
            (ξ₀ r ω' : ℝ≥0∞) ∂P' = P' (prefSum a ⁻¹' S) := fun r hr ↦ by
        have hdisj : Disjoint (Finset.range a) {r} :=
          Finset.disjoint_singleton_right.mpr fun hmem ↦
            not_lt_of_ge (Finset.mem_Ico.mp hr).1 (Finset.mem_range.mp hmem)
        have hc := (hξ₀_ind.indepFun_finset (Finset.range a) {r} hdisj hξ₀_m).comp
          (Measurable.of_discrete : Measurable fun w : Finset.range a → ℕ ↦
            if (∑ i : Finset.range a, w i) ∈ S then (1 : ℝ≥0∞) else 0)
          (Measurable.of_discrete : Measurable fun w : ({r} : Finset ℕ) → ℕ ↦
            (w ⟨r, Finset.mem_singleton_self r⟩ : ℝ≥0∞))
        have hind_r : ((prefSum a ⁻¹' S).indicator (1 : Ω' → ℝ≥0∞)) ⟂ᵢ[P']
            (fun ω' ↦ (ξ₀ r ω' : ℝ≥0∞)) :=
          hc.congr (Eventually.of_forall fun ω' ↦ by
            dsimp only [Function.comp_apply]
            rw [Finset.sum_coe_sort (Finset.range a) (fun i ↦ ξ₀ i ω')]
            by_cases hm : prefSum a ω' ∈ S
            · rw [indicator_of_mem (show ω' ∈ prefSum a ⁻¹' S from hm), Pi.one_apply]
              exact ite_eq_left_iff.mpr fun h ↦ absurd hm h
            · rw [indicator_of_notMem (show ω' ∉ prefSum a ⁻¹' S from hm)]
              exact ite_eq_right_iff.mpr fun h ↦ absurd h hm)
            (Eventually.of_forall fun _ ↦ rfl)
        rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
          (f := (prefSum a ⁻¹' S).indicator (1 : Ω' → ℝ≥0∞))
          (g := fun ω' ↦ (ξ₀ r ω' : ℝ≥0∞))
          ((measurable_const : Measurable (1 : Ω' → ℝ≥0∞)).indicator hmS).aemeasurable
          ((Measurable.of_discrete :
            Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp (hξ₀_m r)).aemeasurable
          hind_r, lintegral_indicator_one hmS, hξ₀_lint_one r, mul_one]
      rw [Finset.sum_congr rfl hr_eq, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le d a)) zero_le
    have hint_R : Integrable (fun ω' ↦ (R₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω') P' :=
      hSnj₀_int.mono' ((hcast_m.comp hR₀_m).mul
        (measurable_one.indicator (hL₀_m hS))).aestronglyMeasurable
        (Eventually.of_forall fun ω' ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _))]
          by_cases hm : ω' ∈ L₀ ⁻¹' S
          · simp only [indicator_of_mem hm, Pi.one_apply, mul_one]
            linarith [Nat.cast_nonneg (α := ℝ) (L₀ ω')]
          · simp only [indicator_of_notMem hm, mul_zero]; positivity)
    have hint_X : Integrable (fun ω' ↦ (X₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω') P' :=
      hX₀_int.mono' ((hcast_m.comp hX₀_m).mul
        (measurable_one.indicator (hL₀_m hS))).aestronglyMeasurable
        (Eventually.of_forall fun ω' ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
            (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _))]
          by_cases hm : ω' ∈ L₀ ⁻¹' S <;> simp [hm])
    have hlint :
        ∫⁻ ω', ENNReal.ofReal ((R₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω') ∂P' ≤
          ∫⁻ ω', ENNReal.ofReal ((X₀ ω' : ℝ) * (L₀ ⁻¹' S).indicator 1 ω') ∂P' := by
      rw [hlR, hlX, htR, htX]
      exact ENNReal.tsum_le_tsum fun d ↦ Finset.sum_le_sum fun a _ ↦
        mul_le_mul_of_nonneg_right (hcell_le d a) zero_le
    rw [← ofReal_integral_eq_lintegral_ofReal hint_R (Eventually.of_forall fun _ ↦
          mul_nonneg (Nat.cast_nonneg _)
            (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _)),
      ← ofReal_integral_eq_lintegral_ofReal hint_X (Eventually.of_forall fun _ ↦
          mul_nonneg (Nat.cast_nonneg _)
            (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _))] at hlint
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ mul_nonneg (Nat.cast_nonneg _)
      (indicator_nonneg (f := (1 : Ω' → ℝ)) (fun _ _ ↦ zero_le_one) _))).mp hlint
  have hSnj_L0_le : ∫ ω', ((L j ω' : ℝ) + (R j ω' : ℝ)) *
      {ω'' | L j ω'' = 0}.indicator 1 ω' ∂P' ≤ ∑' d : ℕ, (d : ℝ) * v d * pX d := by
    have hae_eq : (fun ω' ↦ ((L j ω' : ℝ) + (R j ω' : ℝ)) *
        {ω'' | L j ω'' = 0}.indicator 1 ω') =ᵐ[P']
        fun ω' ↦ (R₀ ω' : ℝ) * (L₀ ⁻¹' {0}).indicator 1 ω' := by
      filter_upwards [hL_ae, hR_ae] with ω' h1 h2
      by_cases h0 : L₀ ω' = 0
      · rw [indicator_of_mem (show ω' ∈ {ω'' | L j ω'' = 0} from h1.trans h0),
          indicator_of_mem (show ω' ∈ L₀ ⁻¹' {0} from h0), h1, h0, h2]; simp
      · rw [indicator_of_notMem
            (show ω' ∉ {ω'' | L j ω'' = 0} from fun hm ↦ h0 (h1.symm.trans hm)),
          indicator_of_notMem (show ω' ∉ L₀ ⁻¹' {0} from h0)]; simp
    have hX0 := hX_bochner (fun d ↦ (d : ℝ)) {0} Nat.cast_nonneg (measurableSet_singleton 0)
      hdpX_sum hX₀_int
    simp_rw [hprod_q] at hX0
    exact (integral_congr_ae hae_eq).trans_le
      ((hRX_bochner_le {0} (measurableSet_singleton 0)).trans_eq hX0)
  have hae_pos : ∀ {Y Y₀ : Ω' → ℕ}, Y =ᵐ[P'] Y₀ →
      (fun ω' ↦ (Y ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω') =ᵐ[P']
        fun ω' ↦ (Y₀ ω' : ℝ) * (L₀ ⁻¹' Ioi 0).indicator 1 ω' := fun hY ↦ by
    filter_upwards [hY, hL_ae] with ω' h1 h2
    by_cases hp : 0 < L₀ ω'
    · rw [indicator_of_mem (show ω' ∈ {ω'' | 0 < L j ω''} by change 0 < L j ω'; omega),
        indicator_of_mem (show ω' ∈ L₀ ⁻¹' Ioi 0 from hp), h1]
    · rw [indicator_of_notMem (show ω' ∉ {ω'' | 0 < L j ω''} by change ¬ 0 < L j ω'; omega),
        indicator_of_notMem (show ω' ∉ L₀ ⁻¹' Ioi 0 from hp)]; simp
  have hRX_le : ∫ ω', (R j ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
      ∫ ω', (X j ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω' ∂P' := by
    rw [integral_congr_ae (hae_pos hR_ae), integral_congr_ae (hae_pos hX_ae)]
    exact hRX_bochner_le (Ioi 0) measurableSet_Ioi
  have hXpos_eq : ∫ ω', (X j ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω' ∂P' =
      ∑' d : ℕ, (d : ℝ) * (1 - v d) * pX d := by
    rw [integral_congr_ae (hae_pos hX_ae),
      hX_bochner (fun d ↦ (d : ℝ)) (Ioi 0) Nat.cast_nonneg measurableSet_Ioi hdpX_sum hX₀_int]
    have hp_pos : ∀ a : ℕ, P'.real (prefSum a ⁻¹' Ioi 0) = 1 - q ^ a := fun a ↦ by
      have hc : (prefSum a ⁻¹' Ioi 0 : Set Ω') = (prefSum a ⁻¹' {0})ᶜ := by
        ext ω'; simp only [mem_preimage, mem_Ioi, mem_compl_iff, mem_singleton_iff]; omega
      rw [hc, probReal_compl_eq_one_sub (hpref_m a (measurableSet_singleton 0)), hprod_q a]
    refine tsum_congr fun d ↦ ?_
    simp_rw [hp_pos, Finset.sum_sub_distrib]
    rw [show ∑ _ ∈ Finset.range (d + 1), (1 : ℝ) = (d : ℝ) + 1 by simp]
    dsimp only [v]; field_simp
  exact ⟨hX_int, hSnj₀_int.congr hSnj_ae, hdpX_sum, hX_mean, hSnj_mean, hSnj_L0_le, hRX_le,
    hXpos_eq⟩

/-- First inequality of step (iii): $\mathbb{P}(L_{n,j} > 0) \le \sigma^2 \mathbb{P}(Z_{n-j} > 0)$
under finite variance (`SteinIntro.tex:3151, 3179-3185`). -/
theorem prob_L_pos_le_var_mul_prob_Z_pos {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hGW : IsGaltonWatson P Z) (hmean : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (h2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P) (hSpine : IsSizeBiasSpine P Z P' n X L R) :
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    ∀ j ∈ Finset.Icc 1 n,
      P'.real {ω' | 0 < L j ω'} ≤ σsq * P.real {ω | 0 < Z (n - j) ω} := by
  intro σsq j hj
  obtain ⟨_, _, _, _, _, _, hpX_sum, _, _, hLpos_prob, h2_part⟩ :=
    spine_level_identities hGW hmean hSpine hj
  obtain ⟨hX_int, _, hdpX_sum, hX_mean, _, _, _, _⟩ := h2_part h2
  set q : ℝ := P.real {ω | Z (n - j) ω = 0}
  set v : ℕ → ℝ := fun d ↦ (∑ a ∈ Finset.range (d + 1), q ^ a) / ((d : ℝ) + 1)
  set pX : ℕ → ℝ := fun d ↦ P'.real {ω' | X j ω' = d}
  have hq0 : 0 ≤ q := measureReal_nonneg; have hq1 : q ≤ 1 := probReal_le_one' P _
  rcases hSpine with ⟨_, _, _, hlev⟩
  have hdpX_tsum : ∑' d : ℕ, (d : ℝ) * pX d = σsq :=
    ((integral_nat_func_eq_tsum (hlev j hj).1 Nat.cast_nonneg hX_int).2).symm.trans hX_mean
  have hsum_lhs : Summable (fun d : ℕ ↦ (1 - v d) * pX d) :=
    Summable.of_nonneg_of_le
      (fun d ↦ mul_nonneg (sub_nonneg.mpr (avg_pow_bdd_and_one_sub_le hq0 hq1 d).2.1)
        measureReal_nonneg)
      (fun d ↦ mul_le_of_le_one_left measureReal_nonneg
        (by linarith [(avg_pow_bdd_and_one_sub_le hq0 hq1 d).1])) hpX_sum
  rw [hLpos_prob, hGW.prob_pos_eq_one_sub (n - j)]
  refine (hsum_lhs.tsum_le_tsum (fun d ↦ ?_) (hdpX_sum.mul_right (1 - q))).trans_eq
    (by rw [tsum_mul_right, hdpX_tsum])
  nlinarith [(avg_pow_bdd_and_one_sub_le hq0 hq1 d).2.2, (measureReal_nonneg : 0 ≤ pX d)]

/-- **Section 5.3 spine step bound (ii)** (`SteinIntro.tex:3149-3150, 3166-3177`; `I-9`). -/
theorem sec5_3_step_ii {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hGW : IsGaltonWatson P Z) (hmean : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (h3 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P)
    (hSpine : IsSizeBiasSpine P Z P' n X L R) :
    ∀ j ∈ Finset.Icc 1 n,
      ∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        ∫ ω', (X j ω' : ℝ) * {ω'' | 0 < L j ω''}.indicator 1 ω' ∂P' ∧
      ∫ ω', (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        (∫ ω, (Z 1 ω : ℝ) ^ 3 ∂P) * P.real {ω | 0 < Z (n - j) ω} := by
  intro j hj; have h2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P := h3.mono_exponent (by norm_num)
  obtain ⟨_, _, _, _, _, hpX_eq, _, _, _, _, h2_part⟩ := spine_level_identities hGW hmean hSpine hj
  obtain ⟨_, _, hdpX_sum, _, _, _, hRX_le, hXpos_eq⟩ := h2_part h2; refine ⟨hRX_le, ?_⟩
  set q : ℝ := P.real {ω | Z (n - j) ω = 0}
  set v : ℕ → ℝ := fun d ↦ (∑ a ∈ Finset.range (d + 1), q ^ a) / ((d : ℝ) + 1)
  set pX : ℕ → ℝ := fun d ↦ P'.real {ω' | X j ω' = d}
  have hq0 : 0 ≤ q := measureReal_nonneg; have hq1 : q ≤ 1 := probReal_le_one' P _
  have hZ3_int : Integrable (fun ω ↦ (Z 1 ω : ℝ) ^ 3) P :=
    (h3.integrable_norm_pow (by positivity : (3 : ℕ) ≠ 0)).congr
      (Eventually.of_forall fun ω ↦ by
        dsimp only; rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)])
  obtain ⟨hZ3_sum, hZ3_val⟩ := integral_nat_func_eq_tsum (hGW.aemeasurable_Z 1)
    (fun k : ℕ ↦ pow_nonneg (Nat.cast_nonneg k) 3) hZ3_int
  have hinj1 : Function.Injective (fun d : ℕ ↦ d + 1) := fun _ _ h ↦ Nat.succ.inj h
  have hd2_le_term : ∀ d : ℕ, (d : ℝ) ^ 2 * pX d ≤
      ((d + 1 : ℕ) : ℝ) ^ 3 * P.real {ω | Z 1 ω = d + 1} := fun d ↦ by
    rw [hpX_eq d, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ measureReal_nonneg
    push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hd2_sum : Summable (fun d : ℕ ↦ (d : ℝ) ^ 2 * pX d) :=
    Summable.of_nonneg_of_le (fun d ↦ mul_nonneg (sq_nonneg _) measureReal_nonneg)
      hd2_le_term (hZ3_sum.comp_injective hinj1)
  have hd2_le_Z3 : ∑' d : ℕ, (d : ℝ) ^ 2 * pX d ≤ ∫ ω, (Z 1 ω : ℝ) ^ 3 ∂P := by
    rw [hZ3_val, hZ3_sum.tsum_eq_zero_add,
      show ((0 : ℕ) : ℝ) ^ 3 * P.real {ω | Z 1 ω = 0} = 0 by simp, zero_add]
    exact hd2_sum.tsum_le_tsum hd2_le_term (hZ3_sum.comp_injective hinj1)
  have hsum_lhs : Summable (fun d : ℕ ↦ (d : ℝ) * (1 - v d) * pX d) :=
    Summable.of_nonneg_of_le (fun d ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg d)
      (sub_nonneg.mpr (avg_pow_bdd_and_one_sub_le hq0 hq1 d).2.1)) measureReal_nonneg)
      (fun d ↦ mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (Nat.cast_nonneg d)
          (by linarith [(avg_pow_bdd_and_one_sub_le hq0 hq1 d).1]))
        measureReal_nonneg) hdpX_sum
  rw [hXpos_eq, hGW.prob_pos_eq_one_sub (n - j)]
  refine (hsum_lhs.tsum_le_tsum (fun d ↦ ?_) (hd2_sum.mul_right (1 - q))).trans
    (tsum_mul_right.trans_le (mul_le_mul_of_nonneg_right hd2_le_Z3 (sub_nonneg.mpr hq1)))
  nlinarith [mul_le_mul_of_nonneg_left (avg_pow_bdd_and_one_sub_le hq0 hq1 d).2.2
    (Nat.cast_nonneg (α := ℝ) d), (measureReal_nonneg : 0 ≤ pX d)]

/-!
### 2. Negative Correlation and Spine Step Bounds (`sec5_3_step_i`)
-/

theorem sec5_3_neg_corr_3158_and_3160_corrected :
    Sec5_3_neg_corr_3158_and_3160_corrected_stmt := by
  intro Ω Ω' _ _ P _ P' _ Z n X L R R' U hGW hmean h2 hCoup σsq Snj Sn
  rcases hCoup with ⟨hSpine, hR'_law, _, _, _, _⟩
  refine ⟨?_, fun j hj ↦ ?_⟩
  · have hint_j : ∀ j ∈ Finset.Icc 1 n,
        Integrable (Snj j) P' ∧ ∫ ω', Snj j ω' ∂P' = σsq := fun j hj ↦ by
      have h := (spine_level_identities hGW hmean hSpine hj).2.2.2.2.2.2.2.2.2.2 h2
      exact ⟨h.2.1, h.2.2.2.2.1⟩
    have hsum_int : Integrable (fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, Snj j ω') P' :=
      integrable_finsetSum _ fun j hj ↦ (hint_j j hj).1
    have hadd := integral_add (integrable_const (1 : ℝ)) hsum_int
    simp only [integral_const, probReal_univ, one_smul] at hadd
    change (∫ ω', (1 + ∑ j ∈ Finset.Icc 1 n, Snj j ω') ∂P') - 1 = (n : ℝ) * σsq
    rw [hadd, add_sub_cancel_left, integral_finsetSum _ fun j hj ↦ (hint_j j hj).1,
      Finset.sum_congr rfl fun j hj ↦ (hint_j j hj).2,
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul]
  · obtain ⟨_, hR_aem, ⟨S₀, hS₀_m, hS₀_ae⟩, _, hL0_pos, _, hpX_sum, htsum_pX,
      hL0_prob, _, h2_part⟩ := spine_level_identities hGW hmean hSpine hj
    obtain ⟨_, _, hdpX_sum, hX_mean, hSnj_mean, hSnj_L0_le, _, _⟩ := h2_part h2
    set q : ℝ := P.real {ω | Z (n - j) ω = 0}
    set v : ℕ → ℝ := fun d ↦ (∑ a ∈ Finset.range (d + 1), q ^ a) / ((d : ℝ) + 1)
    set pX : ℕ → ℝ := fun d ↦ P'.real {ω' | X j ω' = d}
    have hq0 : 0 ≤ q := measureReal_nonneg
    have hq1 : q ≤ 1 := probReal_le_one' P _
    have hv_anti : Antitone v := antitone_nat_of_succ_le fun d ↦ by
      dsimp only [v]
      rw [div_le_div_iff₀ (by positivity) (by positivity), Finset.sum_range_succ]
      have hpow : ((d : ℝ) + 1) * q ^ (d + 1) ≤ ∑ a ∈ Finset.range (d + 1), q ^ a := by
        have h1 : ∑ _ ∈ Finset.range (d + 1), q ^ (d + 1) ≤
            ∑ a ∈ Finset.range (d + 1), q ^ a :=
          Finset.sum_le_sum fun a ha ↦
            pow_le_pow_of_le_one hq0 hq1 (Nat.le_of_lt (Finset.mem_range.mp ha))
        simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h1
      push_cast; linarith
    have hdpX_tsum : ∑' d : ℕ, (d : ℝ) * pX d = σsq := by
      have h := (integral_nat_func_eq_tsum (by
        rcases hSpine with ⟨_, _, _, hlev⟩; exact (hlev j hj).1)
        (fun d : ℕ ↦ Nat.cast_nonneg d) (h2_part h2).1).2
      exact h.symm.trans hX_mean
    have hcheb := chebyshev_tsum_prob (u := fun d : ℕ ↦ (d : ℝ)) (v := v) (w := pX)
      Nat.cast_nonneg (fun _ _ h ↦ Nat.cast_le.mpr h)
      (fun d ↦ (avg_pow_bdd_and_one_sub_le hq0 hq1 d).1)
      (fun d ↦ (avg_pow_bdd_and_one_sub_le hq0 hq1 d).2.1)
      hv_anti (fun _ ↦ measureReal_nonneg) hpX_sum htsum_pX hdpX_sum
    rw [hdpX_tsum, ← hL0_prob] at hcheb
    have hneg_corr : ∫ ω', Snj j ω' * {ω'' : Ω' | L j ω'' = 0}.indicator 1 ω' ∂P' ≤
        (∫ ω', Snj j ω' ∂P') * P'.real {ω' | L j ω' = 0} := by
      rw [hSnj_mean]; exact hSnj_L0_le.trans hcheb
    have hcond_eq :
        ProbabilityTheory.cond P' {ω' | L j ω' = 0} = ProbabilityTheory.cond P' S₀ := by
      rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr hS₀_ae,
        Measure.restrict_congr_set hS₀_ae]
    have hR'_eq_cond : ∫ ω', (R' j ω' : ℝ) ∂P' =
        ∫ ω', (R j ω' : ℝ) ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) := by
      have hcast_m : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
      rw [← integral_map (hR'_law j hj).1 hcast_m.aestronglyMeasurable, (hR'_law j hj).2,
        integral_map (hR_aem.mono_ac ProbabilityTheory.cond_absolutelyContinuous)
          hcast_m.aestronglyMeasurable]
    have hcond_RS : ∫ ω', (R j ω' : ℝ) ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) =
        ∫ ω', Snj j ω' ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) := by
      rw [hcond_eq, ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
        ← integral_indicator hS₀_m, ← integral_indicator hS₀_m]
      congr 1; refine integral_congr_ae ?_
      filter_upwards [Filter.eventuallyEqSet_iff.mp hS₀_ae] with ω' hmem
      by_cases h0 : L j ω' = 0
      · simp [hmem.mp h0, Snj, h0]
      · simp [show ω' ∉ S₀ from fun hm ↦ h0 (hmem.mpr hm)]
    have hcond_le : ∫ ω', Snj j ω' ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) ≤
        ∫ ω', Snj j ω' ∂P' := by
      rw [hcond_eq, ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul,
        ← integral_indicator hS₀_m, ENNReal.toReal_inv, ← Measure.real,
        ← measureReal_congr hS₀_ae]
      have hind_ae : S₀.indicator (Snj j) =ᵐ[P']
          fun ω' ↦ Snj j ω' * {ω'' : Ω' | L j ω'' = 0}.indicator 1 ω' := by
        filter_upwards [Filter.eventuallyEqSet_iff.mp hS₀_ae] with ω' hmem
        by_cases h0 : L j ω' = 0
        · rw [indicator_of_mem (hmem.mp h0),
            indicator_of_mem (show ω' ∈ {ω'' | L j ω'' = 0} from h0)]; simp
        · rw [indicator_of_notMem (show ω' ∉ S₀ from fun hm ↦ h0 (hmem.mpr hm)),
            indicator_of_notMem (show ω' ∉ {ω'' | L j ω'' = 0} from h0)]; simp
      rw [integral_congr_ae hind_ae]
      calc (P'.real {ω' | L j ω' = 0})⁻¹ *
            ∫ ω', Snj j ω' * {ω'' : Ω' | L j ω'' = 0}.indicator 1 ω' ∂P'
          ≤ (P'.real {ω' | L j ω' = 0})⁻¹ *
              ((∫ ω', Snj j ω' ∂P') * P'.real {ω' | L j ω' = 0}) :=
            mul_le_mul_of_nonneg_left hneg_corr (inv_nonneg.mpr hL0_pos.le)
        _ = ∫ ω', Snj j ω' ∂P' := by field_simp [hL0_pos.ne']
    exact ⟨hneg_corr, hR'_eq_cond, hcond_RS, hcond_le, hSnj_mean⟩

theorem sec5_3_step_i : Sec5_3_step_i_stmt := by
  intro Ω Ω' _ _ P _ P' _ Z n X L R R' U hGW hmean h2 hCoup σsq j hj
  have hchain := (sec5_3_neg_corr_3158_and_3160_corrected P P' hGW hmean h2 hCoup).2 j hj
  have hR'_le : ∫ ω', (R' j ω' : ℝ) ∂P' ≤ σsq := by
    linarith [hchain.2.1, hchain.2.2.1, hchain.2.2.2.1, hchain.2.2.2.2]
  rcases hCoup with ⟨hSpine, hR'_law, _, hind_R'_XLR, _, _⟩
  obtain ⟨hL_aem, _, _, ⟨S₁, hS₁_m, hS₁_ae⟩, _, _, _, _, _, _, _⟩ :=
    spine_level_identities hGW hmean hSpine hj
  have hcast_m : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  let φ : ℕ → ℝ := fun m ↦ if 0 < m then 1 else 0
  have hind_j : (fun ω' ↦ (R' j ω' : ℝ)) ⟂ᵢ[P'] (fun ω' ↦ φ (L j ω')) := by
    simpa [Function.comp_def] using hind_R'_XLR.comp
      (hcast_m.comp (measurable_pi_apply (⟨j, hj⟩ : Finset.Icc 1 n)))
      ((Measurable.of_discrete : Measurable fun t : ℕ × ℕ × ℕ ↦ φ t.2.1).comp
        (measurable_pi_apply (⟨j, hj⟩ : Finset.Icc 1 n)))
  have hφ_eq : (fun ω' ↦ φ (L j ω')) = {ω'' : Ω' | 0 < L j ω''}.indicator 1 := by
    ext ω'; by_cases hp : 0 < L j ω' <;> simp [φ, hp]
  have heq : ∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' =
      (∫ ω', (R' j ω' : ℝ) ∂P') * P'.real {ω' | 0 < L j ω'} := by
    have h1 := hind_j.integral_fun_mul_eq_mul_integral
      (hcast_m.comp_aemeasurable (hR'_law j hj).1).aestronglyMeasurable
      ((Measurable.of_discrete : Measurable φ).comp_aemeasurable hL_aem).aestronglyMeasurable
    have h2 : ∫ ω', φ (L j ω') ∂P' = P'.real {ω' | 0 < L j ω'} := by
      rw [hφ_eq]
      refine (integral_congr_ae (f := {ω'' : Ω' | 0 < L j ω''}.indicator 1)
        (g := S₁.indicator 1) ?_).trans
        ((integral_indicator_one hS₁_m).trans (measureReal_congr hS₁_ae.symm))
      filter_upwards [Filter.eventuallyEqSet_iff.mp hS₁_ae] with ω' hm
      by_cases hp : 0 < L j ω'
      · rw [indicator_of_mem (show ω' ∈ {ω'' | 0 < L j ω''} from hp),
          indicator_of_mem (hm.mp hp)]
      · rw [indicator_of_notMem (show ω' ∉ {ω'' | 0 < L j ω''} from hp),
          indicator_of_notMem (fun h ↦ hp (hm.mpr h))]
    have h3 : (fun ω' ↦ (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') =
        fun ω' ↦ (R' j ω' : ℝ) * φ (L j ω') := by
      ext ω'; rw [← hφ_eq]
    rw [h3, h1, h2]
  exact ⟨heq, heq.trans_le (mul_le_mul_of_nonneg_right hR'_le measureReal_nonneg)⟩

/-!
### 3. PGF Second-Order Expansion, Kolmogorov Survival Asymptotic, and `sec5_3_step_iii`
-/

private lemma mul_one_sub_sum_geom (s : ℝ) :
    ∀ k : ℕ, (1 - s) * (∑ b ∈ Finset.range k, s ^ b) = 1 - s ^ k
  | 0 => by simp
  | m + 1 => by
      rw [Finset.sum_range_succ, mul_add, mul_one_sub_sum_geom s m, pow_succ]
      ring

private lemma one_sub_pow_eq_sub_double_geom (s : ℝ) :
    ∀ k : ℕ,
      1 - s ^ k =
        (1 - s) * (k : ℝ) -
          (1 - s) ^ 2 * ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range a, s ^ b
  | 0 => by simp
  | k + 1 => by
      have ih := one_sub_pow_eq_sub_double_geom s k
      have hgeom := mul_one_sub_sum_geom s k
      rw [Finset.sum_range_succ, mul_add, pow_succ, Nat.cast_add, Nat.cast_one]
      linear_combination (1 : ℝ) * ih + (1 - s) * hgeom

private lemma double_sum_one_eq_half_sq_sub :
    ∀ k : ℕ,
      (∑ a ∈ Finset.range k, ∑ _b ∈ Finset.range a, (1 : ℝ)) =
        ((k : ℝ) ^ 2 - (k : ℝ)) / 2
  | 0 => by simp
  | k + 1 => by
      rw [Finset.sum_range_succ, double_sum_one_eq_half_sq_sub k,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        Nat.cast_add, Nat.cast_one]
      ring

private lemma double_sum_one_sub_pow_le_cube {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) :
    (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range a, (1 - s ^ b)) ≤
      (1 - s) * (k : ℝ) ^ 3 := by
  have h1 :
      (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range a, (1 - s ^ b)) ≤
        ∑ a ∈ Finset.range k, ∑ _b ∈ Finset.range a, (1 - s) * (k : ℝ) := by
    refine Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum fun b hb ↦ ?_
    have hbk : (b : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.mem_range.mp hb).le.trans (Finset.mem_range.mp ha).le
    have hbern : 1 - s ^ b ≤ (1 - s) * (b : ℝ) := by
      linarith [one_sub_pow_le_mul_one_sub hs0 hs1 b]
    exact hbern.trans (mul_le_mul_of_nonneg_left hbk (sub_nonneg.mpr hs1))
  refine h1.trans ?_
  have h2 :
      (∑ a ∈ Finset.range k, ∑ _b ∈ Finset.range a, (1 - s) * (k : ℝ)) ≤
        ∑ _a ∈ Finset.range k, ∑ _b ∈ Finset.range k, (1 - s) * (k : ℝ) := by
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
      nsmul_eq_mul, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Finset.mem_range.mp ha).le)
      (mul_nonneg (sub_nonneg.mpr hs1) (Nat.cast_nonneg k))
  refine h2.trans_eq ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

private lemma tendsto_cesaro_nat {d : ℕ → ℝ} {L : ℝ} (hd : Tendsto d atTop (nhds L)) :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range n, d k) / (n : ℝ)) atTop (nhds L) := by
  rw [Metric.tendsto_atTop] at hd ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hd (ε / 2) (half_pos hε)
  let M : ℝ := ∑ k ∈ Finset.range N, |d k - L|
  have hM_nn : 0 ≤ M := Finset.sum_nonneg fun k _ ↦ abs_nonneg _
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * M / ε)
  refine ⟨max (max N 1) K, fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := (le_max_right N 1).trans ((le_max_left _ _).trans hn)
  have hnK : K ≤ n := (le_max_right _ K).trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  rw [Real.dist_eq]
  have hdiff :
      (∑ k ∈ Finset.range n, d k) / (n : ℝ) - L =
        (∑ k ∈ Finset.range n, (d k - L)) / (n : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      sub_div, mul_div_cancel_left₀ L hn_pos.ne']
  rw [hdiff, abs_div, abs_of_pos hn_pos]
  have hfilt : (∑ k ∈ Finset.range n, if k ∈ Finset.range N then |d k - L| else 0) ≤ M := by
    rw [← Finset.sum_filter]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk ↦ (Finset.mem_filter.mp hk).2) (fun _ _ _ ↦ abs_nonneg _)
  have hsum_abs :
      |∑ k ∈ Finset.range n, (d k - L)| ≤ M + (n : ℝ) * (ε / 2) := by
    calc
      |∑ k ∈ Finset.range n, (d k - L)|
          ≤ ∑ k ∈ Finset.range n, |d k - L| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n,
            ((if k ∈ Finset.range N then |d k - L| else 0) + ε / 2) := by
          refine Finset.sum_le_sum fun k _ ↦ ?_
          by_cases hk : k ∈ Finset.range N
          · simp only [hk, ↓reduceIte]; linarith
          · simp only [hk, ↓reduceIte, zero_add]
            have hkN : N ≤ k := by simpa [Finset.mem_range] using hk
            exact (Real.dist_eq (d k) L ▸ hN k hkN).le
      _ = (∑ k ∈ Finset.range n, if k ∈ Finset.range N then |d k - L| else 0) +
            (n : ℝ) * (ε / 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ M + (n : ℝ) * (ε / 2) := by linarith
  have hdiv_le :
      |∑ k ∈ Finset.range n, (d k - L)| / (n : ℝ) ≤ M / (n : ℝ) + ε / 2 := by
    calc
      |∑ k ∈ Finset.range n, (d k - L)| / (n : ℝ)
          ≤ (M + (n : ℝ) * (ε / 2)) / (n : ℝ) := div_le_div_of_nonneg_right hsum_abs hn_pos.le
      _ = M / (n : ℝ) + ε / 2 := by
          rw [add_div, mul_div_cancel_left₀ _ hn_pos.ne']
  have hMn_lt : M / (n : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hn_pos]
    have hKn : (2 * M / ε) < (n : ℝ) := hK.trans_le (Nat.cast_le.mpr hnK)
    have hmul := (div_lt_iff₀ hε).mp hKn
    linarith
  linarith

private lemma measureReal_Z_pos_add_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) (m : ℕ) :
    P.real {ω | 0 < Z m ω} + P.real {ω | Z m ω = 0} = 1 := by
  rw [hGW.prob_pos_eq_one_sub m]
  ring

private lemma measureReal_Z1_eq_one_lt_one_of_pos_var
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z)
    (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P)
    (hσ_pos : 0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P) :
    P.real {ω | Z 1 ω = 1} < 1 := by
  by_contra hge
  push Not at hge
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  have hZ1'_meas : Measurable (gwCanonical ξ' 1) := measurable_gwCanonical hξ'_meas 1
  have h1 : P.real (gwCanonical ξ' 1 ⁻¹' {1}) = P.real {ω | Z 1 ω = 1} := by
    refine measureReal_congr ?_
    filter_upwards [hZ_ae 1] with ω hω; simp [mem_preimage, hω]
  have heq1 : P.real (gwCanonical ξ' 1 ⁻¹' {1}) = 1 :=
    le_antisymm (probReal_le_one' P _) (h1.symm ▸ hge)
  have hcompl0 : P ((gwCanonical ξ' 1 ⁻¹' {1})ᶜ) = 0 := by
    have hreal0 : P.real ((gwCanonical ξ' 1 ⁻¹' {1})ᶜ) = 0 := by
      rw [probReal_compl_eq_one_sub (hZ1'_meas (measurableSet_singleton 1)), heq1, sub_self]
    exact (measureReal_eq_zero_iff (s := (gwCanonical ξ' 1 ⁻¹' {1})ᶜ)).mp hreal0
  have hae_sq : (fun ω ↦ (Z 1 ω : ℝ) ^ 2) =ᵐ[P] fun _ ↦ (1 : ℝ) := by
    have hae' : ∀ᵐ ω ∂P, gwCanonical ξ' 1 ω = 1 := by
      rw [ae_iff]; exact hcompl0
    filter_upwards [hZ_ae 1, hae'] with ω hZ h1'
    simp [hZ, h1']
  have hsq1 : ∫ ω, (Z 1 ω : ℝ) ^ 2 ∂P = 1 := by
    rw [integral_congr_ae hae_sq, integral_const, probReal_univ, one_smul]
  have hvar := ProbabilityTheory.variance_eq_sub hL2
  change ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P =
    (∫ ω, (Z 1 ω : ℝ) ^ 2 ∂P) - (∫ ω, (Z 1 ω : ℝ) ∂P) ^ 2 at hvar
  rw [hsq1, hcrit, one_pow, sub_self] at hvar
  linarith

private lemma pgf_reciprocal_step_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z)
    (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P) :
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    let q : ℕ → ℝ := fun m ↦ P.real {ω | 0 < Z m ω}
    let s : ℕ → ℝ := fun m ↦ P.real {ω | Z m ω = 0}
    let H : ℝ → ℝ := fun t ↦
      ∫ ω, (∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, t ^ b) ∂P
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Integrable (fun ω ↦ ∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, t ^ b) P ∧
      0 ≤ H t ∧ H t ≤ σsq / 2) ∧
    H 1 = σsq / 2 ∧
    (∀ m : ℕ,
      0 < q m ∧ q m ≤ 1 ∧ 0 ≤ s m ∧ s m ≤ 1 ∧ q m + s m = 1 ∧
      q (m + 1) = q m * (1 - q m * H (s m)) ∧
      1 / q (m + 1) - 1 / q m = (q m / q (m + 1)) * H (s m) ∧
      1 / q (m + 1) - 1 / q m = H (s m) / (1 - q m * H (s m))) := by
  intro σsq q s H
  have hZ1_sq_int : Integrable (fun ω ↦ (Z 1 ω : ℝ) ^ 2) P :=
    (memLp_two_iff_integrable_sq hGW.1.aestronglyMeasurable).mp hL2
  have hdom_int : Integrable (fun ω ↦ ((Z 1 ω : ℝ) ^ 2 - (Z 1 ω : ℝ)) / 2) P :=
    (hZ1_sq_int.sub hGW.1).div_const 2
  have hvar := ProbabilityTheory.variance_eq_sub hL2
  change σsq = (∫ ω, (Z 1 ω : ℝ) ^ 2 ∂P) - (∫ ω, (Z 1 ω : ℝ) ∂P) ^ 2 at hvar
  rw [hcrit, one_pow] at hvar
  have hdom_val : ∫ ω, ((Z 1 ω : ℝ) ^ 2 - (Z 1 ω : ℝ)) / 2 ∂P = σsq / 2 := by
    rw [integral_div 2, integral_sub hZ1_sq_int hGW.1, hcrit]
    linarith
  have hH1 : H 1 = σsq / 2 := by
    dsimp only [H]
    simp_rw [one_pow, double_sum_one_eq_half_sq_sub]
    exact hdom_val
  have hH_props : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Integrable (fun ω ↦ ∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, t ^ b) P ∧
      0 ≤ H t ∧ H t ≤ σsq / 2 := by
    intro t ht0 ht1
    have hle_dom : ∀ ω : Ω,
        (∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, t ^ b) ≤
          ((Z 1 ω : ℝ) ^ 2 - (Z 1 ω : ℝ)) / 2 := fun ω ↦ by
      rw [← double_sum_one_eq_half_sq_sub (Z 1 ω)]
      exact Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ pow_le_one₀ ht0 ht1
    have hnn : ∀ ω : Ω,
        0 ≤ ∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, t ^ b :=
      fun ω ↦ Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦ pow_nonneg ht0 b
    have hint : Integrable (fun ω ↦ ∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, t ^ b) P :=
      hdom_int.mono'
        ((Measurable.of_discrete :
          Measurable (fun k : ℕ ↦ ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range a, t ^ b)
            ).comp_aemeasurable
          (hGW.aemeasurable_Z 1)).aestronglyMeasurable
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_of_nonneg (hnn ω)]
          exact hle_dom ω)
    refine ⟨hint, integral_nonneg hnn, ?_⟩
    rw [← hdom_val]
    exact integral_mono hint hdom_int hle_dom
  refine ⟨hH_props, hH1, fun m ↦ ?_⟩
  have hqm_pos : 0 < q m := hGW.measureReal_Z_pos hcrit m
  have hqm1_pos : 0 < q (m + 1) := hGW.measureReal_Z_pos hcrit (m + 1)
  have hqm_le : q m ≤ 1 := probReal_le_one' P _
  have hsm_nn : 0 ≤ s m := measureReal_nonneg
  have hsm_le : s m ≤ 1 := probReal_le_one' P _
  have hsum_m : q m + s m = 1 := measureReal_Z_pos_add_eq_zero P hGW m
  have hsum_m1 : q (m + 1) + s (m + 1) = 1 := measureReal_Z_pos_add_eq_zero P hGW (m + 1)
  have hqm_eq : q m = 1 - s m := by linarith
  have hsm_step : s (m + 1) = ∫ ω, (s m) ^ (Z 1 ω) ∂P := by
    dsimp only [s]
    rw [hGW.measureReal_Z_eq_zero (m + 1), Function.iterate_succ_apply',
      ← hGW.measureReal_Z_eq_zero m]
  have hqm1_eq : q (m + 1) = ∫ ω, (1 - (s m) ^ (Z 1 ω)) ∂P := by
    have hsub := integral_sub (integrable_const (1 : ℝ))
      (integrable_pow_nat (hGW.aemeasurable_Z 1) hsm_nn hsm_le)
    simp only [integral_const, probReal_univ, one_smul] at hsub
    linarith
  have hH_int := (hH_props (s m) hsm_nn hsm_le).1
  have hqm1_rec : q (m + 1) = q m * (1 - q m * H (s m)) := by
    rw [hqm1_eq]
    have hpt : (fun ω ↦ 1 - (s m) ^ (Z 1 ω)) =
        fun ω ↦ q m * (Z 1 ω : ℝ) -
          (q m) ^ 2 * ∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, (s m) ^ b := by
      ext ω
      rw [hqm_eq]
      exact one_sub_pow_eq_sub_double_geom (s m) (Z 1 ω)
    rw [hpt, integral_sub (hGW.1.const_mul (q m)) (hH_int.const_mul ((q m) ^ 2)),
      integral_const_mul, integral_const_mul, hcrit, mul_one]
    dsimp only [H]
    ring
  have hdiv_step1 : 1 / q (m + 1) - 1 / q m = (q m / q (m + 1)) * H (s m) := by
    have hdiff : q m - q (m + 1) = (q m) ^ 2 * H (s m) := by linarith [hqm1_rec]
    rw [div_sub_div 1 1 hqm1_pos.ne' hqm_pos.ne', one_mul, mul_one, hdiff]
    field_simp [hqm_pos.ne', hqm1_pos.ne']
  have h1_sub_pos : 1 - q m * H (s m) = q (m + 1) / q m := by
    rw [hqm1_rec, mul_div_cancel_left₀ _ hqm_pos.ne']
  have hdiv_step2 : 1 / q (m + 1) - 1 / q m = H (s m) / (1 - q m * H (s m)) := by
    rw [hdiv_step1, h1_sub_pos]
    field_simp [hqm_pos.ne', hqm1_pos.ne']
  exact ⟨hqm_pos, hqm_le, hsm_nn, hsm_le, hsum_m, hqm1_rec, hdiv_step1, hdiv_step2⟩

theorem sec5_3_kolmogorov_survival_restricted :
    Sec5_3_kolmogorov_survival_restricted_stmt := by
  intro Ω _ P _ Z hGW hcrit hL2 hσ_pos
  dsimp only
  set σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
  set q : ℕ → ℝ := fun m ↦ P.real {ω | 0 < Z m ω}
  set s : ℕ → ℝ := fun m ↦ P.real {ω | Z m ω = 0}
  set H : ℝ → ℝ := fun t ↦
    ∫ ω, (∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, t ^ b) ∂P
  obtain ⟨hH_props, hH1, hrec⟩ := pgf_reciprocal_step_identity P hGW hcrit hL2
  have hZ1_sq_int : Integrable (fun ω ↦ (Z 1 ω : ℝ) ^ 2) P :=
    (memLp_two_iff_integrable_sq hGW.1.aestronglyMeasurable).mp hL2
  have hnot_one : P.real {ω | Z 1 ω = 1} < 1 :=
    measureReal_Z1_eq_one_lt_one_of_pos_var P hGW hcrit hL2 hσ_pos
  have hq_tendsto0 : Tendsto q atTop (nhds 0) :=
    hGW.tendsto_measureReal_Z_pos_zero hcrit.le hnot_one
  have hs_tendsto1 : Tendsto s atTop (nhds 1) := by
    have h : s = fun m ↦ 1 - q m := funext fun m ↦ by linarith [(hrec m).2.2.2.2.1]
    rw [h]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hq_tendsto0
  have hH_tendsto : Tendsto (fun m ↦ H (s m)) atTop (nhds (σsq / 2)) := by
    rw [← hH1]
    refine tendsto_integral_of_dominated_convergence
      (fun ω ↦ ((Z 1 ω : ℝ) ^ 2 - (Z 1 ω : ℝ)) / 2)
      (fun m ↦ (hH_props (s m) (hrec m).2.2.1 (hrec m).2.2.2.1).1.1)
      ((hZ1_sq_int.sub hGW.1).div_const 2)
      (fun m ↦ Eventually.of_forall fun ω ↦ ?_)
      (Eventually.of_forall fun ω ↦ ?_)
    · have hnn : 0 ≤ ∑ a ∈ Finset.range (Z 1 ω), ∑ b ∈ Finset.range a, (s m) ^ b :=
        Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ pow_nonneg (hrec m).2.2.1 _
      rw [Real.norm_of_nonneg hnn, ← double_sum_one_eq_half_sq_sub (Z 1 ω)]
      exact Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦
        pow_le_one₀ (hrec m).2.2.1 (hrec m).2.2.2.1
    · refine tendsto_finsetSum _ fun a _ ↦ tendsto_finsetSum _ fun b _ ↦ ?_
      exact ((continuous_pow b).tendsto 1).comp hs_tendsto1
  let d : ℕ → ℝ := fun m ↦ 1 / q (m + 1) - 1 / q m
  have hd_tendsto : Tendsto d atTop (nhds (σsq / 2)) := by
    have hd_eq : d = fun m ↦ H (s m) / (1 - q m * H (s m)) :=
      funext fun m ↦ (hrec m).2.2.2.2.2.2.2
    rw [hd_eq, show σsq / 2 = (σsq / 2) / (1 - 0 * (σsq / 2)) by ring]
    exact hH_tendsto.div
      (tendsto_const_nhds.sub (hq_tendsto0.mul hH_tendsto))
      (by norm_num)
  have hcesaro := tendsto_cesaro_nat hd_tendsto
  have htel : ∀ n : ℕ, (∑ m ∈ Finset.range n, d m) = 1 / q n - 1 / q 0 := by
    intro n
    exact Finset.sum_range_sub (fun m ↦ 1 / q m) n
  have hinv_n_tendsto : Tendsto (fun n : ℕ ↦ (1 / q 0) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hqn_inv_tendsto : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) * q n)) atTop (nhds (σsq / 2)) := by
    have h1 := hcesaro.add hinv_n_tendsto
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [htel n, sub_div, sub_add_cancel, div_div, mul_comm (q n) (n : ℝ)]
  have hfinal := hqn_inv_tendsto.inv₀ (by positivity : σsq / 2 ≠ 0)
  have hlim_eq : (σsq / 2)⁻¹ = 2 / σsq := by ring
  rw [hlim_eq] at hfinal
  refine hfinal.congr' (Eventually.of_forall fun n ↦ ?_)
  rw [one_div, inv_inv]

theorem sec5_3_step_iii : Sec5_3_step_iii_stmt := by
  intro Ω _ P _ Z hGW hcrit hL2
  dsimp only
  set σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
  refine ⟨fun {Ω'} _ P' _ {n} {X L R} hSp j hj ↦
    prob_L_pos_le_var_mul_prob_Z_pos P P' hGW hcrit hL2 hSp j hj, ?_⟩
  have hσ_nn : 0 ≤ σsq := ProbabilityTheory.variance_nonneg _ P
  rcases hσ_nn.eq_or_lt with hσ0 | hσ_pos
  · refine ⟨1, zero_lt_one, fun n j _ ↦ ?_⟩
    rw [← hσ0, zero_mul, one_mul]
    positivity
  · have hkolm := sec5_3_kolmogorov_survival_restricted P hGW hcrit hL2 hσ_pos
    have hq_tendsto0 : Tendsto (fun m : ℕ ↦ P.real {ω | 0 < Z m ω}) atTop (nhds 0) :=
      hGW.tendsto_measureReal_Z_pos_zero hcrit.le
        (measureReal_Z1_eq_one_lt_one_of_pos_var P hGW hcrit hL2 hσ_pos)
    let a : ℕ → ℝ := fun m ↦ σsq * ((m + 1 : ℕ) : ℝ) * P.real {ω | 0 < Z m ω}
    have ha_tendsto : Tendsto a atTop (nhds 2) := by
      have h1 : a = fun m : ℕ ↦
          σsq * ((m : ℝ) * P.real {ω | 0 < Z m ω} + P.real {ω | 0 < Z m ω}) := by
        ext m; dsimp only [a]; push_cast; ring
      have hlim2 : (2 : ℝ) = σsq * (2 / σsq + 0) := by
        rw [add_zero]; exact (mul_div_cancel₀ 2 hσ_pos.ne').symm
      rw [h1, hlim2]
      exact tendsto_const_nhds.mul (hkolm.add hq_tendsto0)
    rw [Metric.tendsto_atTop] at ha_tendsto
    obtain ⟨N, hN⟩ := ha_tendsto 1 zero_lt_one
    let C : ℝ := max 3 (∑ m ∈ Finset.range N, |a m|)
    have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left 3 _)
    have ha_le_C : ∀ m : ℕ, a m ≤ C := by
      intro m
      by_cases hm : m < N
      · refine (le_abs_self (a m)).trans ?_
        exact (Finset.single_le_sum (fun i _ ↦ abs_nonneg (a i))
          (Finset.mem_range.mpr hm)).trans (le_max_right 3 _)
      · have hmN : N ≤ m := not_lt.mp hm
        have hd := (Real.dist_eq (a m) 2 ▸ hN m hmN).le
        have ham3 : a m ≤ 3 := by linarith [(le_abs_self (a m - 2)).trans hd]
        exact ham3.trans (le_max_left 3 _)
    refine ⟨C, hC_pos, fun n j _ ↦ ?_⟩
    have hm := ha_le_C (n - j)
    have hpos : (0 : ℝ) < ((n - j + 1 : ℕ) : ℝ) := by positivity
    have hdiv := div_le_div_of_nonneg_right hm hpos.le
    have heq : a (n - j) / ((n - j + 1 : ℕ) : ℝ) = σsq * P.real {ω | 0 < Z (n - j) ω} := by
      dsimp only [a]
      field_simp [hpos.ne']
    rwa [heq, div_eq_mul_inv] at hdiv

/-!
### 4. Coupling Discrepancy Bounds (`sec5_3_lpp_mean_diff_o_n`)
-/

private lemma harmonic_sum_le_one_add_log (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n, ((n - j + 1 : ℕ) : ℝ)⁻¹) ≤ 1 + Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp
  · have hbij :
        (∑ j ∈ Finset.Icc 1 n, ((n - j + 1 : ℕ) : ℝ)⁻¹) =
          ∑ m ∈ Finset.range n, ((m + 1 : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_bij (fun j _ ↦ n - j)
        (fun j hj ↦ by have := Finset.mem_Icc.mp hj; rw [Finset.mem_range]; omega)
        (fun j₁ hj₁ j₂ hj₂ h ↦ by
          have := Finset.mem_Icc.mp hj₁
          have := Finset.mem_Icc.mp hj₂
          omega)
        (fun m hm ↦ ⟨n - m, Finset.mem_Icc.mpr ⟨by
          have := Finset.mem_range.mp hm; omega, Nat.sub_le n m⟩, by
          have := Finset.mem_range.mp hm; omega⟩)
        (fun _ _ ↦ rfl)
    rw [hbij]
    have hrange_eq : Finset.range n = insert 0 (Finset.Ico 1 n) := by
      ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    have h0_notMem : (0 : ℕ) ∉ Finset.Ico 1 n := by simp
    rw [hrange_eq, Finset.sum_insert h0_notMem]
    simp only [Nat.zero_add, Nat.cast_one, inv_one]
    have hstep : ∀ m ∈ Finset.Ico 1 n,
        ((m + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
      have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hexp := Real.add_one_le_exp (- ((m + 1 : ℕ) : ℝ)⁻¹)
      have hdiv_eq : (m : ℝ) / ((m + 1 : ℕ) : ℝ) = - ((m + 1 : ℕ) : ℝ)⁻¹ + 1 := by
        push_cast; field_simp [hm1_pos.ne']; ring
      rw [← hdiv_eq] at hexp
      have hlog := Real.log_le_log (div_pos hm_pos hm1_pos) hexp
      rw [Real.log_exp, Real.log_div hm_pos.ne' hm1_pos.ne'] at hlog
      linarith
    have hsum_le := Finset.sum_le_sum hstep
    rw [Finset.sum_Ico_sub (fun m : ℕ ↦ Real.log (m : ℝ)) hn_pos,
      Nat.cast_one, Real.log_one, sub_zero] at hsum_le
    linarith

private lemma integral_abs_U_le_one
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {U : Ω' → ℝ} (hU : MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P') :
    Integrable (fun ω' ↦ |U ω'|) P' ∧ ∫ ω', |U ω'| ∂P' ≤ 1 := by
  have hU_map : P'.map U = volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [hU.map_eq, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
      inv_one, one_smul]
  have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
    rw [← hU_map]
    exact (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).mpr ‹_›
  have hae_mem : ∀ᵐ ω' ∂P', U ω' ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᵐ x ∂(P'.map U), x ∈ Ioo (0 : ℝ) 1 := by
      rw [hU_map]
      exact ae_restrict_mem measurableSet_Ioo
    exact (ae_map_iff hU.aemeasurable measurableSet_Ioo).mp h1
  have habs_le : ∀ᵐ ω' ∂P', |U ω'| ≤ 1 :=
    hae_mem.mono fun ω' hω' ↦ by rw [abs_of_pos hω'.1]; exact hω'.2.le
  have hint : Integrable (fun ω' ↦ |U ω'|) P' :=
    Integrable.of_bound
      (continuous_abs.measurable.comp_aemeasurable hU.aemeasurable).aestronglyMeasurable
      1 (habs_le.mono fun ω' hω' ↦ by rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hω')
  refine ⟨hint, ?_⟩
  calc
    ∫ ω', |U ω'| ∂P' ≤ ∫ _ : Ω', (1 : ℝ) ∂P' :=
      integral_mono_ae hint (integrable_const 1) habs_le
    _ = 1 := by simp

private lemma integrable_spine_coupling_level
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n j : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P)
    (hCoupl : IsSizeBiasSpineCoupling P Z P' n X L R R' U)
    (hj : j ∈ Finset.Icc 1 n) :
    Integrable (fun ω' ↦ (R j ω' : ℝ)) P' ∧
    Integrable (fun ω' ↦ (R' j ω' : ℝ)) P' ∧
    Integrable (fun ω' ↦ (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' ∧
    Integrable (fun ω' ↦ (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' ∧
    Integrable (fun ω' ↦ (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' := by
  obtain ⟨hL_aem, hR_aem, _, _, hL0_pos, _, _, _, _, _, h2_part⟩ :=
    spine_level_identities hGW hcrit hCoupl.1 hj
  obtain ⟨hX_int, hSnj_int, _, _, _, _, _, _⟩ := h2_part hL2
  have hX_aem : AEMeasurable (X j) P' := by
    rcases hCoupl.1 with ⟨_, _, _, hlev⟩; exact (hlev j hj).1
  have hcast_m : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  let φ_pos : ℕ → ℝ := fun k ↦ if 0 < k then 1 else 0
  have hφ_m : Measurable φ_pos := Measurable.of_discrete
  have hind_eq : ∀ ω' : Ω', ({ω'' : Ω' | 0 < L j ω''}.indicator (1 : Ω' → ℝ) ω') = φ_pos (L j ω') :=
    fun ω' ↦ by by_cases h : 0 < L j ω' <;> simp [φ_pos, h]
  have hR_int : Integrable (fun ω' ↦ (R j ω' : ℝ)) P' :=
    hSnj_int.mono' (hcast_m.comp_aemeasurable hR_aem).aestronglyMeasurable
      (Eventually.of_forall fun ω' ↦ by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
        linarith [Nat.cast_nonneg (α := ℝ) (L j ω')])
  have hL0_ne : P' {ω' | L j ω' = 0} ≠ 0 := by
    intro h0; simp [Measure.real, h0] at hL0_pos
  have hR_cond_int :
      Integrable (fun ω' ↦ (R j ω' : ℝ)) (ProbabilityTheory.cond P' {ω' | L j ω' = 0}) :=
    hR_int.restrict.smul_measure (ENNReal.inv_ne_top.mpr hL0_ne)
  have hR_cond_aem :
      AEMeasurable (R j) (ProbabilityTheory.cond P' {ω' | L j ω' = 0}) :=
    hR_aem.mono_ac ProbabilityTheory.cond_absolutelyContinuous
  have hmap_int : Integrable (fun k : ℕ ↦ (k : ℝ)) (P'.map (R' j)) := by
    rw [(hCoupl.2.1 j hj).2]
    exact (integrable_map_measure hcast_m.aestronglyMeasurable hR_cond_aem).mpr hR_cond_int
  have hR'_int : Integrable (fun ω' ↦ (R' j ω' : ℝ)) P' :=
    (integrable_map_measure hcast_m.aestronglyMeasurable (hCoupl.2.1 j hj).1).mp hmap_int
  have hR_ind_int :
      Integrable (fun ω' ↦ (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' :=
    hR_int.mono'
      (((hcast_m.comp_aemeasurable hR_aem).mul
        (hφ_m.comp_aemeasurable hL_aem)).aestronglyMeasurable.congr
        (Eventually.of_forall fun ω' ↦ by simp [hind_eq ω']))
      (Eventually.of_forall fun ω' ↦ by
        by_cases h : 0 < L j ω' <;> simp [h])
  have hR'_ind_int :
      Integrable (fun ω' ↦ (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' :=
    hR'_int.mono'
      (((hcast_m.comp_aemeasurable (hCoupl.2.1 j hj).1).mul
        (hφ_m.comp_aemeasurable hL_aem)).aestronglyMeasurable.congr
        (Eventually.of_forall fun ω' ↦ by simp [hind_eq ω']))
      (Eventually.of_forall fun ω' ↦ by
        by_cases h : 0 < L j ω' <;> simp [h])
  have hX_ind_int :
      Integrable (fun ω' ↦ (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' :=
    hX_int.mono'
      (((hcast_m.comp_aemeasurable hX_aem).mul
        (hφ_m.comp_aemeasurable hL_aem)).aestronglyMeasurable.congr
        (Eventually.of_forall fun ω' ↦ by simp [hind_eq ω']))
      (Eventually.of_forall fun ω' ↦ by
        by_cases h : 0 < L j ω' <;> simp [h])
  exact ⟨hR_int, hR'_int, hR_ind_int, hR'_ind_int, hX_ind_int⟩

private lemma integral_abs_Yn_sub_Yne_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P)
    (hCoupl : IsSizeBiasSpineCoupling P Z P' n X L R R' U) :
    let Yn : Ω' → ℝ := fun ω' ↦
      1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
    let Yne : Ω' → ℝ := fun ω' ↦ (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
    Integrable (fun ω' ↦ |Yn ω' - Yne ω'|) P' ∧
    ∫ ω', |Yn ω' - Yne ω'| ∂P' ≤
      1 + ∑ j ∈ Finset.Icc 1 n,
        ((∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P') +
          (∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P')) := by
  intro Yn Yne
  obtain ⟨hU_int, hU_le⟩ := integral_abs_U_le_one P' hCoupl.2.2.2.2.1
  have hlevel := fun (j : ℕ) (hj : j ∈ Finset.Icc 1 n) ↦
    integrable_spine_coupling_level P P' hGW hcrit hL2 hCoupl hj
  have hsum_R'_int : Integrable
      (fun ω' ↦ ∑ j ∈ Finset.Icc 1 n,
        (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' :=
    integrable_finsetSum _ fun j hj ↦ (hlevel j hj).2.2.2.1
  have hsum_R_int : Integrable
      (fun ω' ↦ ∑ j ∈ Finset.Icc 1 n,
        (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' :=
    integrable_finsetSum _ fun j hj ↦ (hlevel j hj).2.2.1
  have hdom_int : Integrable
      (fun ω' ↦ |U ω'| +
        (∑ j ∈ Finset.Icc 1 n, (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') +
        (∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω')) P' :=
    (hU_int.add hsum_R'_int).add hsum_R_int
  have hcast_m : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  let φ_pos : ℕ → ℝ := fun k ↦ if 0 < k then 1 else 0
  have hφ_m : Measurable φ_pos := Measurable.of_discrete
  have hdiff_aem : AEStronglyMeasurable (fun ω' ↦ |Yn ω' - Yne ω'|) P' := by
    have hsum_aem : AEStronglyMeasurable
        (fun ω' ↦ ∑ j ∈ Finset.Icc 1 n,
          ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') P' := by
      refine (Finset.aestronglyMeasurable_sum _ fun j hj ↦ ?_).congr
        (Eventually.of_forall fun ω' ↦ Finset.sum_apply ω' _ _)
      obtain ⟨hL_aem, hR_aem, _, _, _, _, _, _, _, _, _⟩ :=
        spine_level_identities hGW hcrit hCoupl.1 hj
      exact (((hcast_m.comp_aemeasurable (hCoupl.2.1 j hj).1).aestronglyMeasurable.sub
        (hcast_m.comp_aemeasurable hR_aem).aestronglyMeasurable).mul
        (hφ_m.comp_aemeasurable hL_aem).aestronglyMeasurable).congr
        (Eventually.of_forall fun ω' ↦ by
          by_cases h : 0 < L j ω' <;> simp [φ_pos, h])
    exact (hCoupl.2.2.2.2.1.aemeasurable.aestronglyMeasurable.add hsum_aem).norm.congr
      (Eventually.of_forall fun ω' ↦ by
        dsimp only [Pi.add_apply, Real.norm_eq_abs]
        exact congrArg abs (sec5_3_eq_3143_corrected n L R R' U ω').1.symm)
  have habs_int : Integrable (fun ω' ↦ |Yn ω' - Yne ω'|) P' :=
    hdom_int.mono' hdiff_aem (Eventually.of_forall fun ω' ↦ by
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      exact (sec5_3_eq_3143_corrected n L R R' U ω').2)
  refine ⟨habs_int, ?_⟩
  have hdom_eq :
      ∫ ω', (|U ω'| +
        (∑ j ∈ Finset.Icc 1 n, (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') +
        (∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω')) ∂P' =
      (∫ ω', |U ω'| ∂P') +
        ∑ j ∈ Finset.Icc 1 n,
          ((∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P') +
            (∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P')) := by
    have h1 := integral_add (hU_int.add hsum_R'_int) hsum_R_int
    have h2 := integral_add hU_int hsum_R'_int
    dsimp only [Pi.add_apply] at h1 h2
    rw [h1, h2, integral_finsetSum _ (fun j hj ↦ (hlevel j hj).2.2.2.1),
      integral_finsetSum _ (fun j hj ↦ (hlevel j hj).2.2.1),
      add_assoc, ← Finset.sum_add_distrib]
  have hle := integral_mono habs_int hdom_int
    fun ω' ↦ (sec5_3_eq_3143_corrected n L R R' U ω').2
  linarith

theorem sec5_3_lpp_mean_diff_log_restricted :
    Sec5_3_lpp_mean_diff_log_restricted_stmt := by
  intro Ω _ P _ Z hGW hcrit hL3
  have hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P :=
    hL3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  set σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
  set m3 : ℝ := ∫ ω, (Z 1 ω : ℝ) ^ 3 ∂P
  have hσ_nn : 0 ≤ σsq := ProbabilityTheory.variance_nonneg _ P
  have hm3_nn : 0 ≤ m3 := integral_nonneg fun ω ↦ pow_nonneg (Nat.cast_nonneg _) 3
  obtain ⟨hstep_iii_1, C₀, hC₀_pos, hstep_iii_2⟩ := sec5_3_step_iii P hGW hcrit hL2
  let K : ℝ := (σsq + m3 / σsq) * C₀
  have hK_nn : 0 ≤ K := by dsimp only [K]; positivity
  let C : ℝ := (1 / Real.log 2) + K * ((1 / Real.log 2) + 1)
  refine ⟨C, fun {Ω'} _ P' _ {n} {X L R R'} {U} hn2 hCoupl ↦ ?_⟩
  dsimp only
  set Yn : Ω' → ℝ := fun ω' ↦
    1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
  set Yne : Ω' → ℝ := fun ω' ↦ (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogn_ge : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log zero_lt_two (by exact_mod_cast hn2)
  have hlogn_pos : 0 < Real.log (n : ℝ) := hlog2_pos.trans_le hlogn_ge
  have hbase := (integral_abs_Yn_sub_Yne_le P P' hGW hcrit hL2 hCoupl).2
  have hj_le : ∀ j ∈ Finset.Icc 1 n,
      (∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P') +
        (∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P') ≤
        K * ((n - j + 1 : ℕ) : ℝ)⁻¹ := by
    intro j hj
    have hR'_le :
        ∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
          σsq * C₀ * ((n - j + 1 : ℕ) : ℝ)⁻¹ := by
      calc ∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P'
          ≤ σsq * P'.real {ω' | 0 < L j ω'} :=
            (sec5_3_step_i P P' hGW hcrit hL2 hCoupl j hj).2
        _ ≤ σsq * (σsq * P.real {ω | 0 < Z (n - j) ω}) :=
            mul_le_mul_of_nonneg_left (hstep_iii_1 P' hCoupl.1 j hj) hσ_nn
        _ ≤ σsq * (C₀ * ((n - j + 1 : ℕ) : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left (hstep_iii_2 n j hj) hσ_nn
        _ = σsq * C₀ * ((n - j + 1 : ℕ) : ℝ)⁻¹ := by ring
    have hR_le :
        ∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
          (m3 / σsq) * C₀ * ((n - j + 1 : ℕ) : ℝ)⁻¹ := by
      have hii := sec5_3_step_ii P P' hGW hcrit hL3 hCoupl.1 j hj
      rcases hσ_nn.eq_or_lt with hσ0 | hσ_pos
      · obtain ⟨_, _, _, _, _, _, _, _, _, _, h2_part⟩ :=
          spine_level_identities hGW hcrit hCoupl.1 hj
        obtain ⟨hX_int, _, _, hX_mean, _, _, _, _⟩ := h2_part hL2
        have hX_ind_int := (integrable_spine_coupling_level P P' hGW hcrit hL2 hCoupl hj).2.2.2.2
        have hX_ind_le :
            ∫ ω', (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
              ∫ ω', (X j ω' : ℝ) ∂P' := by
          refine integral_mono hX_ind_int hX_int fun ω' ↦ ?_
          by_cases h : 0 < L j ω' <;> simp [h]
        have hle0 : ∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤ 0 := by
          linarith [hii.1, hX_ind_le, hX_mean, hσ0]
        have hrhs_nn : 0 ≤ (m3 / σsq) * C₀ * ((n - j + 1 : ℕ) : ℝ)⁻¹ := by positivity
        linarith
      · calc ∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P'
            ≤ m3 * P.real {ω | 0 < Z (n - j) ω} := hii.1.trans hii.2
          _ = (m3 / σsq) * (σsq * P.real {ω | 0 < Z (n - j) ω}) := by
              field_simp [hσ_pos.ne']
          _ ≤ (m3 / σsq) * (C₀ * ((n - j + 1 : ℕ) : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left (hstep_iii_2 n j hj) (div_nonneg hm3_nn hσ_nn)
          _ = (m3 / σsq) * C₀ * ((n - j + 1 : ℕ) : ℝ)⁻¹ := by ring
    dsimp only [K]
    linarith
  have hsum_le :
      (∑ j ∈ Finset.Icc 1 n,
        ((∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P') +
          (∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P'))) ≤
        K * (1 + Real.log (n : ℝ)) := by
    calc _ ≤ ∑ j ∈ Finset.Icc 1 n, K * ((n - j + 1 : ℕ) : ℝ)⁻¹ := Finset.sum_le_sum hj_le
      _ = K * ∑ j ∈ Finset.Icc 1 n, ((n - j + 1 : ℕ) : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ K * (1 + Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (harmonic_sum_le_one_add_log n) hK_nn
  have h1_le : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (n : ℝ) := by
    rw [one_div, le_inv_mul_iff₀ hlog2_pos, mul_one]
    exact hlogn_ge
  have hK1_le : K * (1 + Real.log (n : ℝ)) ≤ K * ((1 / Real.log 2) + 1) * Real.log (n : ℝ) := by
    have h2 : 1 + Real.log (n : ℝ) ≤ ((1 / Real.log 2) + 1) * Real.log (n : ℝ) := by linarith
    calc K * (1 + Real.log (n : ℝ))
        ≤ K * (((1 / Real.log 2) + 1) * Real.log (n : ℝ)) := mul_le_mul_of_nonneg_left h2 hK_nn
      _ = K * ((1 / Real.log 2) + 1) * Real.log (n : ℝ) := by ring
  dsimp only [C]
  linarith

theorem sec5_3_lpp_mean_diff_o_n : Sec5_3_lpp_mean_diff_o_n_stmt := by
  intro Ω _ P _ Z Ω' _ P' _ X L R R' U hGW hcrit hL2 hCoupl
  dsimp only
  set Yn : ∀ n, Ω' n → ℝ := fun n ω' ↦
    1 + ∑ j ∈ Finset.Icc 1 n, (if L n j ω' = 0 then (R n j ω' : ℝ) else (R' n j ω' : ℝ))
  set Yne : ∀ n, Ω' n → ℝ := fun n ω' ↦
    (1 + ∑ j ∈ Finset.Icc 1 n, (R n j ω' : ℝ)) - U n ω'
  set σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
  set q : ℕ → ℝ := fun m ↦ P.real {ω | 0 < Z m ω}
  set s : ℕ → ℝ := fun m ↦ P.real {ω | Z m ω = 0}
  have hσ_nn : 0 ≤ σsq := ProbabilityTheory.variance_nonneg _ P
  let v : ℕ → ℕ → ℝ := fun m d ↦ (∑ a ∈ Finset.range (d + 1), (s m) ^ a) / ((d : ℝ) + 1)
  let w : ℕ → ℝ := fun d ↦ (d : ℝ) * (((d + 1 : ℕ) : ℝ) * P.real {ω | Z 1 ω = d + 1})
  have hw_nn : ∀ d : ℕ, 0 ≤ w d := fun d ↦ by dsimp only [w]; positivity
  have hw_sum : Summable w := by
    have h1 := spine_level_identities hGW hcrit (hCoupl 1 le_rfl).1
      (Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
    obtain ⟨_, _, hdpX_sum, _, _, _, _, _⟩ := h1.2.2.2.2.2.2.2.2.2.2 hL2
    exact hdpX_sum.congr fun d ↦ by rw [h1.2.2.2.2.2.1 d]
  let ψ : ℕ → ℝ := fun m ↦
    if σsq = 0 then 0 else σsq ^ 2 * q m + ∑' d : ℕ, (1 - v m d) * w d
  have hψ_nn : ∀ m : ℕ, 0 ≤ ψ m := by
    intro m
    dsimp only [ψ]
    split_ifs
    · exact le_rfl
    · refine add_nonneg (mul_nonneg (sq_nonneg _) measureReal_nonneg)
        (tsum_nonneg fun d ↦ mul_nonneg ?_ (hw_nn d))
      linarith [(avg_pow_bdd_and_one_sub_le
        (measureReal_nonneg : 0 ≤ s m) (probReal_le_one' P _) d).2.1]
  have hψ_tendsto : Tendsto ψ atTop (nhds 0) := by
    by_cases hσ0 : σsq = 0
    · have h0 : ψ = fun _ ↦ 0 := funext fun m ↦ by simp [ψ, hσ0]
      rw [h0]; exact tendsto_const_nhds
    · have hσ_pos : 0 < σsq := lt_of_le_of_ne hσ_nn (Ne.symm hσ0)
      have hq_tendsto0 : Tendsto q atTop (nhds 0) :=
        hGW.tendsto_measureReal_Z_pos_zero hcrit.le
          (measureReal_Z1_eq_one_lt_one_of_pos_var P hGW hcrit hL2 hσ_pos)
      have htsum_tendsto : Tendsto (fun m : ℕ ↦ ∑' d : ℕ, (1 - v m d) * w d) atTop (nhds 0) := by
        rw [show (0 : ℝ) = ∑' _d : ℕ, (0 : ℝ) by simp]
        refine tendsto_tsum_of_dominated_convergence hw_sum (fun d ↦ ?_)
          (Eventually.of_forall fun m d ↦ ?_)
        · refine squeeze_zero (fun m ↦ ?_) (fun m ↦ ?_)
            (by simpa using (hq_tendsto0.const_mul (d : ℝ)).mul_const (w d))
          · have hv :=
              avg_pow_bdd_and_one_sub_le (measureReal_nonneg : 0 ≤ s m) (probReal_le_one' P _) d
            exact mul_nonneg (by linarith [hv.2.1]) (hw_nn d)
          · have hv :=
              avg_pow_bdd_and_one_sub_le (measureReal_nonneg : 0 ≤ s m) (probReal_le_one' P _) d
            have h1 : 1 - s m = q m := by linarith [measureReal_Z_pos_add_eq_zero P hGW m]
            have hle : 1 - v m d ≤ (d : ℝ) * q m := by
              rw [← h1]
              exact hv.2.2
            exact mul_le_mul_of_nonneg_right hle (hw_nn d)
        · have hv :=
            avg_pow_bdd_and_one_sub_le (measureReal_nonneg : 0 ≤ s m) (probReal_le_one' P _) d
          have hnn : 0 ≤ (1 - v m d) * w d := mul_nonneg (by linarith [hv.2.1]) (hw_nn d)
          rw [Real.norm_of_nonneg hnn]
          nlinarith [hv.1, hw_nn d]
      have hψ_eq : ψ = fun m ↦ σsq ^ 2 * q m + ∑' d : ℕ, (1 - v m d) * w d :=
        funext fun m ↦ by simp [ψ, hσ0]
      rw [hψ_eq, show (0 : ℝ) = σsq ^ 2 * 0 + 0 by ring]
      exact (tendsto_const_nhds.mul hq_tendsto0).add htsum_tendsto
  have hcesaro := tendsto_cesaro_nat hψ_tendsto
  have hinv_n : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper_tendsto :
      Tendsto (fun n : ℕ ↦ (1 + ∑ m ∈ Finset.range n, ψ m) / (n : ℝ)) atTop (nhds 0) := by
    have h := hinv_n.add hcesaro
    rw [add_zero] at h
    exact h.congr fun n ↦ (add_div _ _ _).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_tendsto
    (Eventually.of_forall fun n ↦
      div_nonneg (integral_nonneg fun _ ↦ abs_nonneg _) (Nat.cast_nonneg n)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
  have hbase := (integral_abs_Yn_sub_Yne_le P (P' n) hGW hcrit hL2 (hCoupl n hn1)).2
  have hj_le : ∀ j ∈ Finset.Icc 1 n,
      (∫ ω', (R' n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n) +
        (∫ ω', (R n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n) ≤
        ψ (n - j) := by
    intro j hj
    obtain ⟨_, _, _, _, _, hpX_eq, _, _, _, _, h2_part⟩ :=
      spine_level_identities hGW hcrit (hCoupl n hn1).1 hj
    obtain ⟨hX_int, _, _, hX_mean, _, _, hRX_le, hXpos_eq⟩ := h2_part hL2
    have hR'_le :
        ∫ ω', (R' n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n ≤
          σsq ^ 2 * q (n - j) := by
      calc ∫ ω', (R' n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n
          ≤ σsq * (P' n).real {ω' | 0 < L n j ω'} :=
            (sec5_3_step_i P (P' n) hGW hcrit hL2 (hCoupl n hn1) j hj).2
        _ ≤ σsq * (σsq * q (n - j)) :=
            mul_le_mul_of_nonneg_left
              (prob_L_pos_le_var_mul_prob_Z_pos P (P' n) hGW hcrit hL2 (hCoupl n hn1).1 j hj) hσ_nn
        _ = σsq ^ 2 * q (n - j) := by ring
    by_cases hσ0 : σsq = 0
    · have hX_ind_int :=
        (integrable_spine_coupling_level P (P' n) hGW hcrit hL2 (hCoupl n hn1) hj).2.2.2.2
      have hX_ind_le :
          ∫ ω', (X n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n ≤
            ∫ ω', (X n j ω' : ℝ) ∂P' n := by
        refine integral_mono hX_ind_int hX_int fun ω' ↦ ?_
        by_cases h : 0 < L n j ω' <;> simp [h]
      have hR_0 :
          ∫ ω', (R n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n ≤ 0 := by
        linarith [hRX_le, hX_ind_le, hX_mean, hσ0]
      have hR'_0 :
          ∫ ω', (R' n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n ≤ 0 := by
        have : σsq ^ 2 * q (n - j) = 0 := by rw [hσ0]; ring
        linarith [hR'_le]
      have hψ0 : ψ (n - j) = 0 := by simp [ψ, hσ0]
      linarith
    · have hR_le :
          ∫ ω', (R n j ω' : ℝ) * {ω'' : Ω' n | 0 < L n j ω''}.indicator 1 ω' ∂P' n ≤
            ∑' d : ℕ, (1 - v (n - j) d) * w d := by
        refine hRX_le.trans_eq (hXpos_eq.trans ?_)
        refine tsum_congr fun d ↦ ?_
        have hpX_d : (P' n).real {ω' | X n j ω' = d} =
            ((d + 1 : ℕ) : ℝ) * P.real {ω | Z 1 ω = d + 1} := hpX_eq d
        dsimp only [w, v, s]
        rw [hpX_d]
        ring
      have hψ_val : ψ (n - j) =
          σsq ^ 2 * q (n - j) + ∑' d : ℕ, (1 - v (n - j) d) * w d := by
        simp [ψ, hσ0]
      linarith
  have hbij :
      (∑ j ∈ Finset.Icc 1 n, ψ (n - j)) = ∑ m ∈ Finset.range n, ψ m := by
    refine Finset.sum_bij (fun j _ ↦ n - j)
      (fun j hj ↦ by have := Finset.mem_Icc.mp hj; rw [Finset.mem_range]; omega)
      (fun j₁ hj₁ j₂ hj₂ h ↦ by
        have := Finset.mem_Icc.mp hj₁
        have := Finset.mem_Icc.mp hj₂
        omega)
      (fun m hm ↦ ⟨n - m, Finset.mem_Icc.mpr ⟨by
        have := Finset.mem_range.mp hm; omega, Nat.sub_le n m⟩, by
        have := Finset.mem_range.mp hm; omega⟩)
      (fun _ _ ↦ rfl)
  have hsum_le := (Finset.sum_le_sum hj_le).trans_eq hbij
  linarith


/-! ### 5. Theorems 5.8 & 5.9 (`thm5_8_restricted`, `thm5_9_restricted`) and Counterexamples -/

private lemma integral_R_eq_half_var
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n j : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P)
    (hSpine : IsSizeBiasSpine P Z P' n X L R) (hj : j ∈ Finset.Icc 1 n) :
    ∫ ω', (R j ω' : ℝ) ∂P' = ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P / 2 := by
  obtain ⟨hL_aem, hR_aem, _, _, _, hpX_eq, _, _, _, _, h2_part⟩ :=
    spine_level_identities hGW hcrit hSpine hj
  obtain ⟨_, hSnj_int, _, _, hSnj_mean, _, _, _⟩ := h2_part hL2
  have hcast_m : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  have hL_int : Integrable (fun ω' ↦ (L j ω' : ℝ)) P' :=
    hSnj_int.mono' (hcast_m.comp_aemeasurable hL_aem).aestronglyMeasurable
      (Eventually.of_forall fun ω' ↦ by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
        linarith [Nat.cast_nonneg (α := ℝ) (R j ω')])
  have hR_int : Integrable (fun ω' ↦ (R j ω' : ℝ)) P' :=
    hSnj_int.mono' (hcast_m.comp_aemeasurable hR_aem).aestronglyMeasurable
      (Eventually.of_forall fun ω' ↦ by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
        linarith [Nat.cast_nonneg (α := ℝ) (L j ω')])
  obtain ⟨X_w, A_w, L_w, R_w, ξ_w, _, hlvl⟩ := hSpine.exists_measurable_witness
  rcases hlvl j hj with ⟨hX₀_m, hA₀_m, hL₀_m, hR₀_m, hξ₀_m, hX_ae, hL_ae, hR_ae, _,
    _, hXA_pmf, _, hξ₀_law, hXA₀_ind, hL₀_def, hR₀_def⟩
  set X₀ := X_w j; set A₀ := A_w j; set L₀ := L_w j; set R₀ := R_w j; set ξ₀ := ξ_w j
  have hpX₀_congr : ∀ d : ℕ, P'.real {ω' | X₀ ω' = d} = P'.real {ω' | X j ω' = d} := fun d ↦
    measureReal_congr (Filter.eventuallyEqSet_iff.mpr (hX_ae.symm.mono fun _ h ↦ by simp [h]))
  have htonelli : ∀ {F : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞}, Measurable F →
      ∫⁻ ω', F ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') ∂P' =
        ∑' d : ℕ, ∑ a ∈ Finset.range (d + 1),
          (∫⁻ ω', F ((d, a), fun r ↦ ξ₀ r ω') ∂P') *
            ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) := fun {F} hF ↦ by
    let tupξ : Ω' → ℕ → ℕ := fun ω' r ↦ ξ₀ r ω'
    have htup_m : Measurable tupξ := measurable_pi_iff.mpr hξ₀_m
    set μXA := P'.map (fun ω' ↦ (X₀ ω', A₀ ω'))
    set μξ := P'.map tupξ
    have : IsProbabilityMeasure μXA :=
      (Measure.isProbabilityMeasure_map_iff (hX₀_m.prodMk hA₀_m).aemeasurable).mpr ‹_›
    have : IsProbabilityMeasure μξ :=
      (Measure.isProbabilityMeasure_map_iff htup_m.aemeasurable).mpr ‹_›
    change ∫⁻ ω', F ((X₀ ω', A₀ ω'), tupξ ω') ∂P' = _
    rw [← lintegral_map hF ((hX₀_m.prodMk hA₀_m).prodMk htup_m),
      hXA₀_ind.map_prod_eq_prod_map_map (hX₀_m.prodMk hA₀_m).aemeasurable htup_m.aemeasurable,
      lintegral_prod F hF.aemeasurable, lintegral_countable', ENNReal.tsum_prod']
    refine tsum_congr fun d ↦ ?_
    have hμXA_eq : ∀ a : ℕ, μXA {(d, a)} =
        if a ≤ d then ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) else 0 := fun a ↦ by
      have hpre : ((fun ω' ↦ (X₀ ω', A₀ ω')) ⁻¹' {(d, a)} : Set Ω') =
          {ω' | X₀ ω' = d ∧ A₀ ω' = a} := by ext; simp
      have hpX_d : P'.real {ω' | X j ω' = d} =
          ((d + 1 : ℕ) : ℝ) * P.real {ω | Z 1 ω = d + 1} := hpX_eq d
      rw [← ofReal_measureReal (measure_ne_top μXA {(d, a)}),
        map_measureReal_apply (hX₀_m.prodMk hA₀_m) (measurableSet_singleton (d, a)),
        hpre, hXA_pmf d a, hpX₀_congr d, hpX_d]
      split_ifs with had
      · congr 1
        have hne : (d : ℝ) + 1 ≠ 0 := by positivity
        push_cast; exact mul_div_cancel_left₀ _ hne
      · simp
    rw [tsum_eq_sum (s := Finset.range (d + 1)) fun a ha ↦ by
      rw [hμXA_eq a]; split_ifs with had
      · exfalso; simp only [Finset.mem_range, not_lt] at ha; omega
      · simp]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have had : a ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [hμXA_eq a, ite_eq_left_iff.mpr fun h ↦ absurd had h,
      lintegral_map (f := fun y ↦ F ((d, a), y))
        (hF.comp (measurable_const.prodMk measurable_id)) htup_m]
  have hξ₀_lint_one : ∀ r, ∫⁻ ω', (ξ₀ r ω' : ℝ≥0∞) ∂P' = 1 := fun r ↦ by
    have hc := (IdentDistrib.mk (hξ₀_m r).aemeasurable (hGW.aemeasurable_Z (n - j))
      (hξ₀_law r)).comp hcast_m
    have h1 := ofReal_integral_eq_lintegral_ofReal
      (hc.symm.integrable_snd (hGW.integrable_Z (n - j)))
      (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)
    rw [hc.integral_eq.trans (hGW.integral_Z_eq_one hcrit (n - j)), ENNReal.ofReal_one] at h1
    exact (lintegral_congr fun _ ↦ (ENNReal.ofReal_natCast _).symm).trans h1.symm
  let FL : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞ :=
    fun z ↦ ((∑ r ∈ Finset.range z.1.2, z.2 r : ℕ) : ℝ≥0∞)
  let FR : (ℕ × ℕ) × (ℕ → ℕ) → ℝ≥0∞ :=
    fun z ↦ ((∑ r ∈ Finset.Ico z.1.2 z.1.1, z.2 r : ℕ) : ℝ≥0∞)
  have hFL_m : Measurable FL :=
    (Measurable.of_discrete : Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp
      (measurable_sum_range_nat (measurable_snd.comp measurable_fst)
        fun r ↦ (measurable_pi_apply r).comp measurable_snd)
  have hFR_m : Measurable FR :=
    (Measurable.of_discrete : Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp
      (measurable_sum_Ico_nat (measurable_snd.comp measurable_fst)
        (measurable_fst.comp measurable_fst) fun r ↦ (measurable_pi_apply r).comp measurable_snd)
  have hξ₀_cast_m : ∀ r, Measurable (fun ω' ↦ (ξ₀ r ω' : ℝ≥0∞)) :=
    fun r ↦ (Measurable.of_discrete : Measurable fun m : ℕ ↦ (m : ℝ≥0∞)).comp (hξ₀_m r)
  have hL_lint : ∫⁻ ω', (L₀ ω' : ℝ≥0∞) ∂P' =
      ∑' d : ℕ, ∑ a ∈ Finset.range (d + 1),
        (a : ℝ≥0∞) * ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) := by
    have h1 : (fun ω' ↦ (L₀ ω' : ℝ≥0∞)) = fun ω' ↦ FL ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') :=
      funext fun ω' ↦ by simp [FL, hL₀_def ω']
    rw [h1, htonelli hFL_m]
    refine tsum_congr fun d ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    dsimp only [FL]
    simp_rw [Nat.cast_sum]
    rw [lintegral_finsetSum (Finset.range a) fun r _ ↦ hξ₀_cast_m r]
    simp [hξ₀_lint_one]
  have hR_lint : ∫⁻ ω', (R₀ ω' : ℝ≥0∞) ∂P' =
      ∑' d : ℕ, ∑ a ∈ Finset.range (d + 1),
        ((d - a : ℕ) : ℝ≥0∞) * ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1}) := by
    have h1 : (fun ω' ↦ (R₀ ω' : ℝ≥0∞)) = fun ω' ↦ FR ((X₀ ω', A₀ ω'), fun r ↦ ξ₀ r ω') :=
      funext fun ω' ↦ by simp [FR, hR₀_def ω']
    rw [h1, htonelli hFR_m]
    refine tsum_congr fun d ↦ Finset.sum_congr rfl fun a _ ↦ ?_
    congr 1
    dsimp only [FR]
    simp_rw [Nat.cast_sum]
    rw [lintegral_finsetSum (Finset.Ico a d) fun r _ ↦ hξ₀_cast_m r]
    simp [hξ₀_lint_one]
  have hLR_lint_eq : ∫⁻ ω', (L₀ ω' : ℝ≥0∞) ∂P' = ∫⁻ ω', (R₀ ω' : ℝ≥0∞) ∂P' := by
    rw [hL_lint, hR_lint]
    refine tsum_congr fun d ↦ ?_
    rw [← Finset.sum_range_reflect
      (fun a : ℕ ↦ (a : ℝ≥0∞) * ENNReal.ofReal (P.real {ω | Z 1 ω = d + 1})) (d + 1)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Nat.add_sub_cancel]
  have hLR_int_eq : ∫ ω', (L j ω' : ℝ) ∂P' = ∫ ω', (R j ω' : ℝ) ∂P' := by
    have hL_of : ENNReal.ofReal (∫ ω', (L j ω' : ℝ) ∂P') = ∫⁻ ω', (L₀ ω' : ℝ≥0∞) ∂P' := by
      rw [ofReal_integral_eq_lintegral_ofReal hL_int
        (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)]
      exact lintegral_congr_ae (hL_ae.mono fun _ h ↦ by
        dsimp only; rw [← h, ENNReal.ofReal_natCast])
    have hR_of : ENNReal.ofReal (∫ ω', (R j ω' : ℝ) ∂P') = ∫⁻ ω', (R₀ ω' : ℝ≥0∞) ∂P' := by
      rw [ofReal_integral_eq_lintegral_ofReal hR_int
        (Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)]
      exact lintegral_congr_ae (hR_ae.mono fun _ h ↦ by
        dsimp only; rw [← h, ENNReal.ofReal_natCast])
    have h := congrArg ENNReal.toReal (hL_of.trans (hLR_lint_eq.trans hR_of.symm))
    rwa [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Nat.cast_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Nat.cast_nonneg _)] at h
  rw [integral_add hL_int hR_int] at hSnj_mean
  linarith

private lemma integrable_comp_of_lipschitz' {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hW : Integrable W P) (hLip : LipschitzWith K f) :
    Integrable (fun ω ↦ f (W ω)) P := by
  have hdom : Integrable (fun ω ↦ |f 0| + (K : ℝ) * ‖W ω‖) P :=
    (integrable_const |f 0|).add (hW.norm.const_mul (K : ℝ))
  refine hdom.mono'
    (hLip.continuous.measurable.comp_aemeasurable hW.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hd := hLip.dist_le_mul (W ω) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero, ← Real.norm_eq_abs (W ω)] at hd
  rw [Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (f (W ω)) (f 0)]

private lemma wassersteinDist_le_two_mul_integral_equilibrium_add_abs_mean
    {Ω Ω_exp : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω_exp]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P_exp : Measure Ω_exp) [IsProbabilityMeasure P_exp]
    {W We : Ω → ℝ} {Z_exp : Ω_exp → ℝ}
    (hEq : IsEquilibrium P W P We)
    (hdiff_int : Integrable (fun ω ↦ |We ω - W ω|) P)
    (hZ_meas : AEMeasurable Z_exp P_exp) (hZ_law : P_exp.map Z_exp = stdExpLaw) :
    wassersteinDist (P.map W) (P_exp.map Z_exp) ≤
      ENNReal.ofReal (2 * ∫ ω, |We ω - W ω| ∂P + |1 - ∫ ω, W ω ∂P|) := by
  rcases hEq with ⟨hW_nn, hW_int, hWe_aem, hEq_id⟩
  refine (thm5_3_1 P P_exp hW_nn hW_int hZ_meas hZ_law).trans ?_
  refine iSup₂_le fun f hf ↦ ENNReal.ofReal_le_ofReal ?_
  rcases hf with ⟨hf_diff, hf'_diff, hf'_bdd, hf''_bdd, hf0⟩
  have hf_lip : LipschitzWith 1 f := by
    refine lipschitzWith_of_nnnorm_deriv_le hf_diff fun x ↦ ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
    exact hf'_bdd x
  have hdf_lip : LipschitzWith 2 (deriv f) := by
    refine lipschitzWith_of_nnnorm_deriv_le hf'_diff fun x ↦ ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
    exact hf''_bdd x
  have hEq_f := hEq_id f ⟨1, hf_lip⟩
  rw [hf0, sub_zero] at hEq_f
  have hdfW_int : Integrable (fun ω ↦ deriv f (W ω)) P :=
    Integrable.of_bound
      ((measurable_deriv f).comp_aemeasurable hW_int.aemeasurable).aestronglyMeasurable
      1 (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hf'_bdd (W ω))
  have hdfWe_int : Integrable (fun ω ↦ deriv f (We ω)) P :=
    Integrable.of_bound
      ((measurable_deriv f).comp_aemeasurable hWe_aem).aestronglyMeasurable
      1 (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hf'_bdd (We ω))
  have hfW_int : Integrable (fun ω ↦ f (W ω)) P := integrable_comp_of_lipschitz' hW_int hf_lip
  have hsub_eq : ∫ ω, (deriv f (W ω) - f (W ω)) ∂P =
      (∫ ω, (deriv f (W ω) - deriv f (We ω)) ∂P) +
        (1 - ∫ ω, W ω ∂P) * ∫ ω, deriv f (We ω) ∂P := by
    rw [integral_sub hdfW_int hfW_int, hEq_f, integral_sub hdfW_int hdfWe_int]
    ring
  have hle1 : |∫ ω, (deriv f (W ω) - deriv f (We ω)) ∂P| ≤ 2 * ∫ ω, |We ω - W ω| ∂P := by
    calc |∫ ω, (deriv f (W ω) - deriv f (We ω)) ∂P|
        ≤ ∫ ω, |deriv f (W ω) - deriv f (We ω)| ∂P := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun ω ↦ deriv f (W ω) - deriv f (We ω))
      _ ≤ ∫ ω, 2 * |We ω - W ω| ∂P := by
          refine integral_mono (hdfW_int.sub hdfWe_int).norm (hdiff_int.const_mul 2) fun ω ↦ ?_
          have hd := hdf_lip.dist_le_mul (W ω) (We ω)
          rwa [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat, abs_sub_comm (W ω) (We ω)] at hd
      _ = 2 * ∫ ω, |We ω - W ω| ∂P := integral_const_mul 2 _
  have hle2 : |(1 - ∫ ω, W ω ∂P) * ∫ ω, deriv f (We ω) ∂P| ≤ |1 - ∫ ω, W ω ∂P| := by
    rw [abs_mul]
    have hdfWe_le : |∫ ω, deriv f (We ω) ∂P| ≤ 1 := by
      have hb := norm_integral_le_of_norm_le_const (μ := P) (C := 1)
        (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hf'_bdd (We ω))
      simpa [Real.norm_eq_abs] using hb
    exact mul_le_of_le_one_right (abs_nonneg _) hdfWe_le
  rw [hsub_eq]
  linarith [abs_add_le (∫ ω, (deriv f (W ω) - deriv f (We ω)) ∂P)
    ((1 - ∫ ω, W ω ∂P) * ∫ ω, deriv f (We ω) ∂P)]

private lemma wassersteinDist_scaled_Y_le
    {Ω ΩY Ω_exp Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ω_exp] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (P_exp : Measure Ω_exp) [IsProbabilityMeasure P_exp]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {Y : ΩY → ℕ} {Zexp : Ω_exp → ℝ}
    {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P)
    (hσ_pos : 0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P)
    (hn1 : 1 ≤ n)
    (hY_meas : AEMeasurable Y PY)
    (hY_map : PY.map Y = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n))
    (hZexp_meas : AEMeasurable Zexp P_exp)
    (hZexp_law : P_exp.map Zexp = stdExpLaw)
    (hCoupl : IsSizeBiasSpineCoupling P Z P' n X L R R' U) :
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    let Yn : Ω' → ℝ := fun ω' ↦
      1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
    let Yne : Ω' → ℝ := fun ω' ↦ (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
    wassersteinDist
        (PY.map (fun ω ↦ 2 * (Y ω : ℝ) / ((n : ℝ) * σsq)))
        (P_exp.map Zexp) ≤
      ENNReal.ofReal
        ((6 / σsq) * ((∫ ω', |Yn ω' - Yne ω'| ∂P') / (n : ℝ)) +
          (2 / σsq) * (1 / (n : ℝ))) := by
  intro σsq Yn Yne
  let Rstar : ℕ → Ω' → ℕ := fun j ω' ↦ if L j ω' = 0 then R j ω' else R' j ω'
  let Yn_nat : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, Rstar j ω'
  let Rn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)
  have hYn_cast : (fun ω' ↦ (Yn_nat ω' : ℝ)) = Yn := by
    ext ω'
    dsimp only [Yn_nat, Yn, Rstar]
    push_cast
    refine congrArg (1 + ·) (Finset.sum_congr rfl fun j _ ↦ ?_)
    split_ifs <;> rfl
  obtain ⟨hYn_nat_map, hEq_Yn⟩ := sec5_3_spine_coupling P P' hGW hcrit hCoupl
  have hEq_Yn' : IsEquilibrium P' Yn P' Yne := by rwa [← hYn_cast]
  let c : ℝ := 2 / ((n : ℝ) * σsq)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hc_pos : 0 < c := by dsimp only [c]; positivity
  let W : Ω' → ℝ := fun ω' ↦ c * Yn ω'
  let We : Ω' → ℝ := fun ω' ↦ c * Yne ω'
  have hEq_W : IsEquilibrium P' W P' We := hEq_Yn'.const_mul_pos hc_pos
  have hYn_nat_aem : AEMeasurable Yn_nat P' := by
    refine aemeasurable_const.add
      ((Finset.aemeasurable_sum (Finset.Icc 1 n) fun j hj ↦ ?_).congr
        (Eventually.of_forall fun ω' ↦ Finset.sum_apply ω' _ _))
    obtain ⟨hL_aem, hR_aem, _, _, _, _, _, _, _, _, _⟩ :=
      spine_level_identities hGW hcrit hCoupl.1 hj
    let ψ : ℕ × ℕ × ℕ → ℕ := fun q ↦ if q.1 = 0 then q.2.1 else q.2.2
    have hψ_m : Measurable ψ := Measurable.of_discrete
    exact hψ_m.comp_aemeasurable (hL_aem.prodMk (hR_aem.prodMk (hCoupl.2.1 j hj).1))
  let φ_scale : ℕ → ℝ := fun k ↦ 2 * (k : ℝ) / ((n : ℝ) * σsq)
  have hφ_m : Measurable φ_scale := Measurable.of_discrete
  have hmap_W : PY.map (fun ω ↦ 2 * (Y ω : ℝ) / ((n : ℝ) * σsq)) = P'.map W := by
    have h1 : (fun ω ↦ 2 * (Y ω : ℝ) / ((n : ℝ) * σsq)) = φ_scale ∘ Y := rfl
    have h2 : W = φ_scale ∘ Yn_nat := by
      ext ω'; dsimp only [W, φ_scale, c, Function.comp_apply]; rw [← hYn_cast]; ring
    rw [h1, h2, ← AEMeasurable.map_map_of_aemeasurable hφ_m.aemeasurable hY_meas,
      ← AEMeasurable.map_map_of_aemeasurable hφ_m.aemeasurable hYn_nat_aem,
      hY_map, hYn_nat_map]
  obtain ⟨habs_int, _⟩ := integral_abs_Yn_sub_Yne_le P P' hGW hcrit hL2 hCoupl
  have hWeW_eq : (fun ω' ↦ |We ω' - W ω'|) = fun ω' ↦ c * |Yn ω' - Yne ω'| := by
    ext ω'; dsimp only [W, We]; rw [← mul_sub, abs_mul, abs_of_pos hc_pos, abs_sub_comm]
  have hdiff_W_int : Integrable (fun ω' ↦ |We ω' - W ω'|) P' := hWeW_eq ▸ habs_int.const_mul c
  have hU_map : P'.map U = volume.restrict (Ioo (0 : ℝ) 1) := by
    rw [hCoupl.2.2.2.2.1.map_eq, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_one, inv_one, one_smul]
  have hae_U : ∀ᵐ ω' ∂P', U ω' ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᵐ x ∂(P'.map U), x ∈ Ioo (0 : ℝ) 1 := by
      rw [hU_map]; exact ae_restrict_mem measurableSet_Ioo
    exact (ae_map_iff hCoupl.2.2.2.2.1.aemeasurable measurableSet_Ioo).mp h1
  obtain ⟨hU_abs_int, hU_abs_le⟩ := integral_abs_U_le_one P' hCoupl.2.2.2.2.1
  have hU_int : Integrable U P' :=
    hU_abs_int.mono' hCoupl.2.2.2.2.1.aemeasurable.aestronglyMeasurable
      (Eventually.of_forall fun _ ↦ le_rfl)
  have hU_int_nn : 0 ≤ ∫ ω', U ω' ∂P' :=
    integral_nonneg_of_ae (hae_U.mono fun _ h ↦ h.1.le)
  have hU_int_le : ∫ ω', U ω' ∂P' ≤ 1 := by
    have heq : ∫ ω', U ω' ∂P' = ∫ ω', |U ω'| ∂P' :=
      integral_congr_ae (hae_U.mono fun _ h ↦ (abs_of_pos h.1).symm)
    linarith
  have hRn_int : Integrable Rn P' :=
    (integrable_const 1).add (integrable_finsetSum _ fun j hj ↦
      (integrable_spine_coupling_level P P' hGW hcrit hL2 hCoupl hj).1)
  have hRn_mean : ∫ ω', Rn ω' ∂P' = 1 + (n : ℝ) * (σsq / 2) := by
    dsimp only [Rn]
    rw [integral_add (integrable_const 1) (integrable_finsetSum _ fun j hj ↦
        (integrable_spine_coupling_level P P' hGW hcrit hL2 hCoupl hj).1),
      integral_const, probReal_univ, one_smul,
      integral_finsetSum _ (fun j hj ↦
        (integrable_spine_coupling_level P P' hGW hcrit hL2 hCoupl hj).1),
      Finset.sum_congr rfl (fun j hj ↦ integral_R_eq_half_var P P' hGW hcrit hL2 hCoupl.1 hj),
      Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  have hYne_int : Integrable Yne P' := hRn_int.sub hU_int
  have hYn_int : Integrable Yn P' := hEq_Yn'.2.1
  have hYne_mean : ∫ ω', Yne ω' ∂P' = 1 + (n : ℝ) * (σsq / 2) - ∫ ω', U ω' ∂P' := by
    dsimp only [Yne]; rw [integral_sub hRn_int hU_int, hRn_mean]
  have hmean_diff : |(∫ ω', Yn ω' ∂P') - (n : ℝ) * (σsq / 2)| ≤
      (∫ ω', |Yn ω' - Yne ω'| ∂P') + 1 := by
    have h1 : (∫ ω', Yn ω' ∂P') - (n : ℝ) * (σsq / 2) =
        (∫ ω', (Yn ω' - Yne ω') ∂P') + (1 - ∫ ω', U ω' ∂P') := by
      rw [integral_sub hYn_int hYne_int, hYne_mean]; ring
    have h2 : |∫ ω', (Yn ω' - Yne ω') ∂P'| ≤ ∫ ω', |Yn ω' - Yne ω'| ∂P' := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω' ↦ Yn ω' - Yne ω')
    have h3 : |1 - ∫ ω', U ω' ∂P'| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [h1]
    linarith [abs_add_le (∫ ω', (Yn ω' - Yne ω') ∂P') (1 - ∫ ω', U ω' ∂P')]
  have hW_mean_diff : |1 - ∫ ω', W ω' ∂P'| ≤ c * ((∫ ω', |Yn ω' - Yne ω'| ∂P') + 1) := by
    have hW_int : ∫ ω', W ω' ∂P' = c * ∫ ω', Yn ω' ∂P' := integral_const_mul c Yn
    have hc_mul : c * ((n : ℝ) * (σsq / 2)) = 1 := by
      dsimp only [c]; field_simp [hn_pos.ne', hσ_pos.ne']; exact div_self hσ_pos.ne'
    have h1 : 1 - ∫ ω', W ω' ∂P' = - (c * ((∫ ω', Yn ω' ∂P') - (n : ℝ) * (σsq / 2))) := by
      rw [hW_int]; linear_combination -hc_mul
    rw [h1, abs_neg, abs_mul, abs_of_pos hc_pos]
    exact mul_le_mul_of_nonneg_left hmean_diff hc_pos.le
  rw [hmap_W]
  refine (wassersteinDist_le_two_mul_integral_equilibrium_add_abs_mean
    P' P_exp hEq_W hdiff_W_int hZexp_meas hZexp_law).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hWeW_eq, integral_const_mul]
  have halg : 2 * (c * ∫ ω', |Yn ω' - Yne ω'| ∂P') + c * ((∫ ω', |Yn ω' - Yne ω'| ∂P') + 1) =
      (6 / σsq) * ((∫ ω', |Yn ω' - Yne ω'| ∂P') / (n : ℝ)) + (2 / σsq) * (1 / (n : ℝ)) := by
    dsimp only [c]; ring
  linarith

theorem thm5_8_restricted : Thm5_8_restricted_stmt := by
  intro Ω Ω_exp _ _ P _ P_exp _ Z Zexp ΩY _ PY _ Y hGW hcrit hL2 hσ_pos hY hZexp_meas hZexp_law
  dsimp only
  set σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
  let Ch1 := fun n : ℕ ↦ (sec5_3_exists_isSizeBiasSpineCoupling P hGW hcrit hL2 n).choose_spec
  let Ω' : ℕ → Type :=
    fun n ↦ (sec5_3_exists_isSizeBiasSpineCoupling P hGW hcrit hL2 n).choose
  let instΩ' : ∀ n, MeasurableSpace (Ω' n) := fun n ↦ (Ch1 n).choose
  let P' : ∀ n, Measure (Ω' n) := fun n ↦ (Ch1 n).choose_spec.choose
  let instP' : ∀ n, IsProbabilityMeasure (P' n) :=
    fun n ↦ (Ch1 n).choose_spec.choose_spec.choose
  let Ch2 := fun n : ℕ ↦ (Ch1 n).choose_spec.choose_spec.choose_spec
  let X : ∀ n, ℕ → Ω' n → ℕ := fun n ↦ (Ch2 n).choose
  let L : ∀ n, ℕ → Ω' n → ℕ := fun n ↦ (Ch2 n).choose_spec.choose
  let R : ∀ n, ℕ → Ω' n → ℕ := fun n ↦ (Ch2 n).choose_spec.choose_spec.choose
  let Ch3 := fun n : ℕ ↦ (Ch2 n).choose_spec.choose_spec.choose_spec
  let R' : ∀ n, ℕ → Ω' n → ℕ := fun n ↦ (Ch3 n).choose
  let U : ∀ n, Ω' n → ℝ := fun n ↦ (Ch3 n).choose_spec.choose
  have hCoupl : ∀ n : ℕ, IsSizeBiasSpineCoupling P Z (P' n) n (X n) (L n) (R n) (R' n) (U n) :=
    fun n ↦ (Ch3 n).choose_spec.choose_spec.1
  let Yn : ∀ n, Ω' n → ℝ := fun n ω' ↦
    1 + ∑ j ∈ Finset.Icc 1 n, (if L n j ω' = 0 then (R n j ω' : ℝ) else (R' n j ω' : ℝ))
  let Yne : ∀ n, Ω' n → ℝ := fun n ω' ↦
    (1 + ∑ j ∈ Finset.Icc 1 n, (R n j ω' : ℝ)) - U n ω'
  have ho_n := sec5_3_lpp_mean_diff_o_n P P' hGW hcrit hL2 (fun n _ ↦ hCoupl n)
  have hinv_n : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  let b_real : ℕ → ℝ := fun n ↦
    (6 / σsq) * ((∫ ω', |Yn n ω' - Yne n ω'| ∂P' n) / (n : ℝ)) + (2 / σsq) * (1 / (n : ℝ))
  have hb_tendsto : Tendsto b_real atTop (nhds 0) := by
    rw [show (0 : ℝ) = (6 / σsq) * 0 + (2 / σsq) * 0 by ring]
    exact (tendsto_const_nhds.mul ho_n).add (tendsto_const_nhds.mul hinv_n)
  let μY : ℕ → Measure ℝ :=
    fun n ↦ (PY n).map (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq))
  have hW_tendsto :
      Tendsto (fun n : ℕ ↦ wassersteinDist (μY n) (P_exp.map Zexp)) atTop (nhds 0) := by
    have hof_tendsto : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (b_real n)) atTop (nhds 0) := by
      rw [← ENNReal.ofReal_zero]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hb_tendsto
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof_tendsto
      (Eventually.of_forall fun _ ↦ zero_le) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    exact wassersteinDist_scaled_Y_le P (PY n) P_exp (P' n) hGW hcrit hL2 hσ_pos hn1
      (hY n hn1).1 (hY n hn1).2 hZexp_meas hZexp_law (hCoupl n)
  have hK_upper :
      Tendsto (fun n : ℕ ↦ (2 * wassersteinDist (μY n) (P_exp.map Zexp)) ^ (1 / 2 : ℝ))
        atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ ↦ 2 * wassersteinDist (μY n) (P_exp.map Zexp)) atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hW_tendsto (Or.inr ENNReal.ofNat_ne_top)
    have h2 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h2
    exact h2.comp h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK_upper
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hY_scale_aem : AEMeasurable (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq)) (PY n) :=
    ((Measurable.of_discrete :
      Measurable fun k : ℕ ↦ 2 * (k : ℝ) / ((n : ℝ) * σsq)).comp_aemeasurable
      (hY n hn1).1)
  have : IsProbabilityMeasure (μY n) :=
    (Measure.isProbabilityMeasure_map_iff hY_scale_aem).mpr inferInstance
  rw [hZexp_law]
  exact kolmogorovDist_le_sqrt_two_mul_wassersteinDist_stdExpLaw (μY n)

theorem thm5_9_restricted : Thm5_9_restricted_stmt := by
  intro Ω Ω_exp _ _ P _ P_exp _ Z Zexp ΩY _ PY _ Y hGW hcrit hL3 hσ_pos hY hZexp_meas hZexp_law
  dsimp only
  have hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P :=
    hL3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)
  set σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
  obtain ⟨C₁, hC₁⟩ := sec5_3_lpp_mean_diff_log_restricted P hGW hcrit hL3
  let C₁' : ℝ := max C₁ 0
  let C : ℝ := (6 / σsq) * C₁' + (2 / σsq) * (1 / Real.log 2)
  refine ⟨C, fun n hn2 ↦ ?_⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨Ω', _, P', _, X, L, R, R', U, hCoupl, _⟩ :=
    sec5_3_exists_isSizeBiasSpineCoupling P hGW hcrit hL2 n
  let Yn : Ω' → ℝ := fun ω' ↦
    1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
  let Yne : Ω' → ℝ := fun ω' ↦ (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
  have hW_le := wassersteinDist_scaled_Y_le P (PY n) P_exp P' hGW hcrit hL2 hσ_pos hn1
    (hY n hn1).1 (hY n hn1).2 hZexp_meas hZexp_law hCoupl
  refine hW_le.trans (ENNReal.ofReal_le_ofReal ?_)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogn_ge : Real.log 2 ≤ Real.log (n : ℝ) :=
    Real.log_le_log zero_lt_two (by exact_mod_cast hn2)
  have hlogn_pos : 0 < Real.log (n : ℝ) := hlog2_pos.trans_le hlogn_ge
  have hdiff_le : ∫ ω', |Yn ω' - Yne ω'| ∂P' ≤ C₁' * Real.log (n : ℝ) :=
    (hC₁ P' hn2 hCoupl).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) hlogn_pos.le)
  have h1_le : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log (n : ℝ) := by
    rw [one_div, le_inv_mul_iff₀ hlog2_pos, mul_one]
    exact hlogn_ge
  have hterm1 :
      (6 / σsq) * ((∫ ω', |Yn ω' - Yne ω'| ∂P') / (n : ℝ)) ≤
        (6 / σsq) * C₁' * Real.log (n : ℝ) / (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hdiff_le (Nat.cast_nonneg n)
    have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 6 / σsq)
    linarith [show (6 / σsq) * (C₁' * Real.log (n : ℝ) / (n : ℝ)) =
      (6 / σsq) * C₁' * Real.log (n : ℝ) / (n : ℝ) by ring]
  have hterm2 :
      (2 / σsq) * (1 / (n : ℝ)) ≤
        (2 / σsq) * (1 / Real.log 2) * Real.log (n : ℝ) / (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right h1_le (Nat.cast_nonneg n)
    have hmul := mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2 / σsq)
    linarith [show (2 / σsq) * ((1 / Real.log 2) * Real.log (n : ℝ) / (n : ℝ)) =
      (2 / σsq) * (1 / Real.log 2) * Real.log (n : ℝ) / (n : ℝ) by ring]
  dsimp only [C]
  linarith [show ((6 / σsq) * C₁' + (2 / σsq) * (1 / Real.log 2)) * Real.log (n : ℝ) / (n : ℝ) =
    (6 / σsq) * C₁' * Real.log (n : ℝ) / (n : ℝ) +
      (2 / σsq) * (1 / Real.log 2) * Real.log (n : ℝ) / (n : ℝ) by ring]

private lemma eq_stdExpLaw_real_Iic_of_kolmogorovDist_eq_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : kolmogorovDist μ stdExpLaw = 0) (x : ℝ) :
    μ.real (Iic x) = stdExpLaw.real (Iic x) := by
  have hle : ENNReal.ofReal |μ.real (Iic x) - stdExpLaw.real (Iic x)| ≤ 0 := by
    rw [← h, kolmogorovDist_eq_iSup]
    exact le_iSup (fun y : ℝ ↦ ENNReal.ofReal |μ.real (Iic y) - stdExpLaw.real (Iic y)|) x
  have h0 : |μ.real (Iic x) - stdExpLaw.real (Iic x)| ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp (nonpos_iff_eq_zero.mp hle)
  linarith [(abs_le.mp h0).1, (abs_le.mp h0).2]

/-- Refutation of the Lean `x / 0 = 0` transcription `Thm5_8` at $\sigma^2 = 0$ (`Z ≡ 1`,
`ISSUE-5.8`, `I-10`). Note: the printed Theorem 5.8 (`SteinIntro.tex:3007-3013`) is
mathematically ill-defined at $\sigma^2 = 0$ (due to division by $0$ in $2 Y_n / (n \sigma^2)$),
not false when $\sigma^2 > 0$; this theorem refutes only the `x / 0 = 0` reading. -/
theorem not_Thm5_8_printed : ¬ Thm5_8.{0, 0, 0} := by
  intro hThm
  let P : Measure Unit := Measure.dirac ()
  let Z : ℕ → Unit → ℕ := fun _ _ ↦ 1
  have hGW : IsGaltonWatson P Z := isGaltonWatson_const_one P
  have hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1 := by simp [P, Z]
  have hL2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P := by
    simp [Z]
  have hY : ∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Z n) P ∧
        P.map (Z n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) := by
    intro n _
    refine ⟨aemeasurable_const, ?_⟩
    have huniv : {ω : Unit | 0 < Z n ω} = univ := by ext; simp [Z]
    rw [huniv, ProbabilityTheory.cond_univ]
  have hlim := hThm P stdExpLaw (fun _ ↦ P) hGW hcrit hL2 hY aemeasurable_id Measure.map_id
  dsimp only at hlim
  have hσ0 : ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P = 0 := by
    rw [ProbabilityTheory.variance_eq_sub hL2]
    simp [P, Z]
  have hmap_dirac : ∀ n : ℕ,
      P.map (fun ω ↦ 2 * (Z n ω : ℝ) /
        ((n : ℝ) * ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P)) =
        Measure.dirac (0 : ℝ) := by
    intro n
    have hfun : (fun ω : Unit ↦ 2 * (Z n ω : ℝ) /
        ((n : ℝ) * ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P)) = fun _ ↦ 0 := by
      ext; simp [hσ0]
    rw [hfun, Measure.map_const, measure_univ, one_smul]
  simp_rw [hmap_dirac, Measure.map_id] at hlim
  have hK0 : kolmogorovDist (Measure.dirac (0 : ℝ)) stdExpLaw = 0 :=
    tendsto_const_nhds_iff.mp hlim
  have hcdf0 := eq_stdExpLaw_real_Iic_of_kolmogorovDist_eq_zero hK0 0
  have hdirac0 : (Measure.dirac (0 : ℝ)).real (Iic 0) = 1 := by simp [Measure.real]
  have hexp0 : stdExpLaw.real (Iic 0) = 0 := by
    change (expLaw 1).real (Iic 0) = 0
    rw [expLaw_real_Iic zero_lt_one 0]
    simp
  linarith

/-- Refutation of the printed Theorem 5.9 (`Thm5_9`, `SteinIntro.tex:3015-3020`; `ISSUE-5.9`,
`I-10`) at the genuine boundary case $n = 1$ with $\sigma^2 = 1 > 0$
($Z_1 \sim \frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$), where $\log 1 = 0$ makes the right-hand
side $C \log(1) / 1 = 0$ for every $C \in \mathbb{R}$ while
$d_{\mathrm{W}}(\mathcal{L}(2 Y_1 / \sigma^2), \mathrm{Exp}(1)) > 0$. -/
theorem not_Thm5_9_printed : ¬ Thm5_9.{0, 0, 0} := by
  intro hThm
  obtain ⟨Ω, _, P, _, Z, hGW, hcrit, hvar, h3_int, _, _⟩ :=
    sec5_3_exists_isGaltonWatson_pos_var
  have hL3 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P := by
    refine (integrable_norm_rpow_iff hGW.1.aestronglyMeasurable
      (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)).mp ?_
    simpa [Real.norm_eq_abs, show (3 : ℝ≥0∞).toReal = (3 : ℕ) by norm_num, Real.rpow_natCast]
      using h3_int
  have hσ_pos : 0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P := by
    rw [hvar]; exact zero_lt_one
  let PY : ∀ n : ℕ, Measure Ω := fun n ↦ ProbabilityTheory.cond P {ω | 0 < Z n ω}
  have instPY : ∀ n : ℕ, IsProbabilityMeasure (PY n) :=
    fun n ↦ ProbabilityTheory.cond_isProbabilityMeasure (hGW.measure_Z_pos_ne_zero hcrit n)
  have hY : ∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Z n) (PY n) ∧
        (PY n).map (Z n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) :=
    fun n _ ↦ ⟨(hGW.aemeasurable_Z n).mono_ac ProbabilityTheory.cond_absolutelyContinuous, rfl⟩
  obtain ⟨C, hC⟩ := hThm P stdExpLaw PY hGW hcrit hL3 hσ_pos hY aemeasurable_id Measure.map_id
  have h1 := hC 1 le_rfl
  simp only [Nat.cast_one, Real.log_one, mul_zero, ENNReal.ofReal_zero,
    Measure.map_id, hvar, mul_one, div_one] at h1
  let W : Ω → ℝ := fun ω ↦ 2 * (Z 1 ω : ℝ)
  let μ₁ : Measure ℝ := (PY 1).map W
  have hW_aem : AEMeasurable W (PY 1) :=
    ((Measurable.of_discrete : Measurable fun k : ℕ ↦ 2 * (k : ℝ)).comp_aemeasurable
      (hY 1 le_rfl).1)
  have : IsProbabilityMeasure μ₁ := (Measure.isProbabilityMeasure_map_iff hW_aem).mpr inferInstance
  have hW0 : wassersteinDist μ₁ stdExpLaw = 0 := nonpos_iff_eq_zero.mp h1
  have hK0 : kolmogorovDist μ₁ stdExpLaw = 0 := by
    have hle := kolmogorovDist_le_sqrt_two_mul_wassersteinDist_stdExpLaw μ₁
    rw [hW0, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hle
    exact nonpos_iff_eq_zero.mp hle
  have hcdf0 := eq_stdExpLaw_real_Iic_of_kolmogorovDist_eq_zero hK0 0
  have hcdf1 := eq_stdExpLaw_real_Iic_of_kolmogorovDist_eq_zero hK0 1
  have hpre_eq : W ⁻¹' (Iic (0 : ℝ)) = W ⁻¹' (Iic (1 : ℝ)) := by
    ext ω
    simp only [W, mem_preimage, mem_Iic]
    rcases Z 1 ω with _ | k
    · norm_num
    · push_cast
      constructor <;> intro h <;> linarith [Nat.cast_nonneg (α := ℝ) k]
  have hμ01 : μ₁.real (Iic 0) = μ₁.real (Iic 1) := by
    rw [map_measureReal_apply_of_aemeasurable hW_aem measurableSet_Iic,
      map_measureReal_apply_of_aemeasurable hW_aem measurableSet_Iic, hpre_eq]
  have hexp0 : stdExpLaw.real (Iic 0) = 0 := by
    change (expLaw 1).real (Iic 0) = 0
    rw [expLaw_real_Iic zero_lt_one 0]; simp
  have hexp1 : 0 < stdExpLaw.real (Iic 1) := by
    change 0 < (expLaw 1).real (Iic 1)
    rw [expLaw_real_Iic zero_lt_one 1, ite_eq_left_iff.mpr fun h ↦ absurd zero_le_one h]
    have : Real.exp (-(1 * 1 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  linarith

end SteinMethod
