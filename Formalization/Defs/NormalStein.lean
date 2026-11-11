/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Laws
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Normal Stein Operator, Solutions, and Function Classes (`Formalization.Defs.NormalStein`)

Normal Stein operator, Stein-equation solutions, and the Wasserstein smooth test class per
rulings `D4`–`D6` of `docs/AUTHOR_RULINGS.md` (`RULING-USER-2026-11-11`).
-/

open MeasureTheory

namespace SteinMethod

/-- Expectation $\Phi(h) = \mathbb{E}[h(Z)]$ with respect to $Z \sim \mathcal{N}(0, 1)$
(Section 2, preceding Proposition 2.4 `\label{prop31}`, `SteinIntro.tex:663`; ruling `D4`). -/
noncomputable def stdNormalExpect (h : ℝ → ℝ) : ℝ :=
  ∫ x, h x ∂(ProbabilityTheory.gaussianReal 0 1)

/-- Standard normal Stein operator $\mathcal{A}f(w) = f'(w) - w f(w)$
(Lemma 2.1 `\label{lem1}`, `SteinIntro.tex:563-566`; ruling `D4`). -/
noncomputable def normalSteinOp (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  deriv f w - w * f w

/-- Solution $f_h(w) = e^{w^2/2} \int_w^\infty e^{-t^2/2}(\Phi(h) - h(t))\,dt$ of the normal Stein
equation $f_h'(w) - w f_h(w) = h(w) - \Phi(h)$
(Lemma 2.5 `\label{lem31}`, eq. `(2.6)` `\label{33}`, `SteinIntro.tex:675-684`; ruling `D4`). -/
noncomputable def normalSteinSol (h : ℝ → ℝ) (w : ℝ) : ℝ :=
  Real.exp (w ^ 2 / 2) *
    ∫ t in Set.Ioi w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)

/-- Kolmogorov Stein solution $f_x = f_{\mathbb{I}[\cdot \le x]}$ for the half-line indicator
(Lemma 2.2 `\label{lem2}`, eq. `(2.1)` `\label{1a}`, `SteinIntro.tex:578-588`; ruling `D4`). -/
noncomputable def normalSteinSolKolm (x : ℝ) : ℝ → ℝ :=
  normalSteinSol ((Set.Iic x).indicator 1)

/-- Left-derivative normal Stein operator $D_- f(w) - w f(w)$, used **only** in `_corrected`
statements where $f_x$ has a jump in $f_x'$ at $w = x$
(Lemma 2.2 `\label{lem2}`, `SteinIntro.tex:578-588`; `ISSUE-2.2`, ruling `D4`). -/
noncomputable def normalSteinOpLeft (f : ℝ → ℝ) (w : ℝ) : ℝ :=
  derivWithin f (Set.Iic w) w - w * f w

/-- Literal test-function class
$\mathcal{F} = \{f : \|f\|, \|f''\| \le 2,\ \|f'\| \le \sqrt{2/\pi}\}$ in Theorem 3.1
(`\label{thm31}`, eq. `(3.1)` `\label{35}`, `SteinIntro.tex:719-724`; ruling `D6`). -/
def normalWassersteinClass : Set (ℝ → ℝ) :=
  {f | Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧
    (∀ w, |f w| ≤ 2) ∧ (∀ w, |deriv f w| ≤ Real.sqrt (2 / Real.pi)) ∧
    (∀ w, |deriv (deriv f) w| ≤ 2)}

end SteinMethod
