/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.NormalStein

/-!
# Kolmogorov Stein Test-Function Class (`Formalization.Defs.Kolmogorov`)

Literal smooth test-function class $\mathcal{F}$ satisfying the bounds of Lemma 3.25
(`\label{lem91}`) used in Corollary 3.26 (`\label{cor91}`, `SteinIntro.tex:1688-1694`).
-/

namespace SteinMethod

/-- Literal test-function class $\mathcal{F}$ satisfying the bounds of Lemma 3.25 in Corollary 3.26
(`\label{cor91}`, `SteinIntro.tex:1688-1694`, referencing Lemma 3.25 `\label{lem91}`,
`SteinIntro.tex:1677-1686`; parallel to `normalWassersteinClass` under ruling `D6`). -/
def normalKolmogorovClass : Set (ℝ → ℝ) :=
  {f | Differentiable ℝ f ∧
    (∀ w : ℝ, |f w| ≤ Real.sqrt (Real.pi / 2)) ∧
    (∀ w : ℝ, |deriv f w| ≤ 2) ∧
    (∀ u v w : ℝ,
      |(w + u) * f (w + u) - (w + v) * f (w + v)| ≤
        (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|))}

end SteinMethod
