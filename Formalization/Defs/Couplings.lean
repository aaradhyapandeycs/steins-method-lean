/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Variance

/-!
# Distributional Couplings (`Formalization.Defs.Couplings`)

Exchangeable pairs, $a$-Stein pairs, size-bias distributions, and zero-bias distributions per
rulings `D7`–`D9` of `docs/AUTHOR_RULINGS.md` (`RULING-USER-2026-11-11`).
-/

open MeasureTheory

namespace SteinMethod

/-- Ordered pair $(W, W')$ of random variables with $(W, W') \stackrel{d}{=} (W', W)$
(Definition 3.2, `SteinIntro.tex:952-954`). -/
def IsExchangeablePair {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (W W' : Ω → α) : Prop :=
  ProbabilityTheory.IdentDistrib (fun ω ↦ (W ω, W' ω)) (fun ω ↦ (W' ω, W ω)) P P

/-- Linear-regression $a$-Stein pair: exchangeable $(W, W')$ with $0 < a \le 1$ and
$\mathbb{E}[W' \mid W] = (1 - a)W$ a.s.
(Definition 3.2, `SteinIntro.tex:952-960`; ruling `D7`). -/
def IsSteinPair {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a : ℝ) (W W' : Ω → ℝ) : Prop :=
  IsExchangeablePair P W W' ∧ 0 < a ∧ a ≤ 1 ∧ Measurable W ∧ Integrable W P ∧
    P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω

/-- Size-bias distributional relation $\mathbb{E}[X f(X)] = \mathbb{E}[X]\,\mathbb{E}[f(X^s)]$
for $X \ge 0$ a.s. with finite mean
(Definition 3.7 `\label{sbc}`, `SteinIntro.tex:1224-1230`; ruling `D8`). -/
def IsSizeBias {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → ℝ) (P' : Measure Ω') (Xs : Ω' → ℝ) : Prop :=
  (0 ≤ᵐ[P] X) ∧ Integrable X P ∧ AEMeasurable Xs P' ∧
    ∀ f : ℝ → ℝ, Measurable f → Integrable (fun ω ↦ X ω * f (X ω)) P →
      ∫ ω, X ω * f (X ω) ∂P = (∫ ω, X ω ∂P) * ∫ ω', f (Xs ω') ∂P'

/-- Zero-bias distributional relation $\mathbb{E}[W f(W)] = \mathrm{Var}(W)\,\mathbb{E}[f'(W^z)]$
for mean-zero $L^2$ random variable $W$, quantified over locally absolutely continuous $f$ for
which both sides are integrable
(Definition 3.10, `SteinIntro.tex:1442-1449`; `ISSUE-3.10`, ruling `D9`). -/
def IsZeroBias {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (W : Ω → ℝ) (P' : Measure Ω') (Wz : Ω' → ℝ) : Prop :=
  MemLp W 2 P ∧ ∫ ω, W ω ∂P = 0 ∧ AEMeasurable Wz P' ∧
    ∀ f : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
      Integrable (fun ω ↦ W ω * f (W ω)) P →
      Integrable (fun ω' ↦ deriv f (Wz ω')) P' →
      ∫ ω, W ω * f (W ω) ∂P =
        ProbabilityTheory.variance W P * ∫ ω', deriv f (Wz ω') ∂P'

end SteinMethod
