/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs

/-!
# Section 1 Statements (`Formalization.Statements.Sec1`)

Self-contained `Prop` statements for Section 1 of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`, `SteinIntro.tex`), covering Theorem 1.1 (`\label{thm1}`,
`SteinIntro.tex:351-357`) and Proposition 1.2 (`\label{prop22}`, `SteinIntro.tex:523-537`).
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-- Theorem 1.1 (`\label{thm1}`, citing Berry 1941 `[ber41]`, `SteinIntro.tex:351-357`): let
$X_1, X_2, \ldots$ be i.i.d. random variables with $\mathbb{E}|X_1|^3 < \infty$,
$\mathbb{E}[X_1] = 0$, and $\operatorname{Var}(X_1) = 1$. If $\Phi$ denotes the c.d.f. of a
standard normal distribution and $W_n = \sum_{i=1}^n X_i / \sqrt{n}$, then for all
$x \in \mathbb{R}$,
$|\mathbb{P}(W_n \le x) - \Phi(x)| \le 1.88 \, \frac{\mathbb{E}|X_1|^3}{\sqrt{n}}$. -/
def Thm1_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {n : ℕ} (x : ℝ),
    0 < n →
    (∀ i : ℕ, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : ℕ, ProbabilityTheory.IdentDistrib (X i) (X 0) P P) →
    MemLp (X 0) 3 P →
    ∫ ω, X 0 ω ∂P = 0 →
    ProbabilityTheory.variance (X 0) P = 1 →
    let W_n : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / Real.sqrt n
    |P.real {ω | W_n ω ≤ x} - stdNormalCDF x| ≤
      1.88 * (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt n

/-- Proposition 1.2(1) (`\label{prop22}`, `SteinIntro.tex:523-526`): for real-valued random
variables $W$ and $Z$, the Kolmogorov distance is bounded above by the total variation distance,
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z))$. -/
def Prop1_2_1 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    AEMeasurable W P → AEMeasurable Z P' →
    kolmogorovDist (P.map W) (P'.map Z) ≤ tvDist (P.map W) (P'.map Z)

/-- Proposition 1.2(2) (`\label{prop22}`, `SteinIntro.tex:527-531`): if $Z$ has Lebesgue density
bounded almost everywhere by $C$, then for any real-valued random variable $W$,
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sqrt{2 C \, d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))}$. -/
def Prop1_2_2 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ} {C : ℝ} (f : ℝ → ℝ≥0∞),
    AEMeasurable W P → AEMeasurable Z P' →
    P'.map Z = volume.withDensity f →
    (∀ᵐ x ∂volume, f x ≤ ENNReal.ofReal C) →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      (2 * ENNReal.ofReal C * wassersteinDist (P.map W) (P'.map Z)) ^ (1 / 2 : ℝ)

/-- Proposition 1.2(3) (`\label{prop22}`, `SteinIntro.tex:532-537`): if $W$ and $Z$ take values in
a countable measurable-singleton space $S$, then
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) =
\frac{1}{2} \sum_{s \in S} |\mathbb{P}(W = s) - \mathbb{P}(Z = s)|$. -/
def Prop1_2_3 : Prop :=
  ∀ {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → S} {Z : Ω' → S},
    AEMeasurable W P → AEMeasurable Z P' →
    tvDist (P.map W) (P'.map Z) =
      (1 / 2 : ℝ≥0∞) *
        ∑' s : S, ENNReal.ofReal |P.real {ω | W ω = s} - P'.real {ω' | Z ω' = s}|

end SteinMethod
