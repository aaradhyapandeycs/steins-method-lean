/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Basic.Real.Basic

/-!
# Coordinatewise Monotone Function Definitions (`Formalization.Defs.PoissonSizeBiasMonotone`)

Pure definitions for Definition 4.9 (`SteinIntro.tex:2377-2381`) in Section 4.3.3
(*Implicit coupling*) of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `SteinMethod.IsIncreasing`: coordinatewise increasing functions $f : \mathbb{R}^n \to \mathbb{R}$.
* `SteinMethod.IsDecreasing`: coordinatewise decreasing functions $f : \mathbb{R}^n \to \mathbb{R}$.
-/

namespace SteinMethod

/-- Definition 4.9 (`SteinIntro.tex:2377-2381`): a function $f : \mathbb{R}^n \to \mathbb{R}$ is
increasing if $x_i \le y_i$ for all $i$ implies $f(x) \le f(y)$. -/
def IsIncreasing {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, (∀ i : Fin n, x i ≤ y i) → f x ≤ f y

/-- Definition 4.9 (`SteinIntro.tex:2377-2381`): a function $f : \mathbb{R}^n \to \mathbb{R}$ is
decreasing if $x_i \le y_i$ for all $i$ implies $f(y) \le f(x)$. -/
def IsDecreasing {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, (∀ i : Fin n, x i ≤ y i) → f y ≤ f x

end SteinMethod
