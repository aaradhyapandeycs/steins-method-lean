/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Laws
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Poisson Stein Operator and Solution (`Formalization.Defs.PoissonStein`)

Chen–Stein characterizing operator and canonical Stein-equation solution $f_A$ on $\mathbb{N}$.
Forward differences reuse Mathlib's `_root_.fwdDiff 1` (`SteinIntro.tex:1885`).
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-- Poisson Stein characterizing operator $\mathcal{A}f(k) = r f(k + 1) - k f(k)$
(Lemma 4.1 `\label{lem101}`, `SteinIntro.tex:1824-1827`). -/
def poissonSteinOp (r : ℝ≥0) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (r : ℝ) * f (k + 1) - (k : ℝ) * f k

/-- Canonical solution $f_A$ of the Chen–Stein equation
$r f_A(k + 1) - k f_A(k) = \mathbb{I}[k \in A] - \mathrm{Po}(r)(A)$ with $f_A(0) = 0$
(Lemma 4.2 `\label{lem102}`, eq. `(4.1)` `\label{101}`, `SteinIntro.tex:1837-1848`). -/
noncomputable def poissonSteinSol (r : ℝ≥0) (A : Set ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 =>
      ((r : ℝ) ^ (k + 1))⁻¹ * Real.exp (r : ℝ) * (Nat.factorial k : ℝ) *
        ((poissonLaw r).real (A ∩ Set.Iio (k + 1)) -
          (poissonLaw r).real A * (poissonLaw r).real (Set.Iio (k + 1)))

end SteinMethod
