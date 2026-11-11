/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonStein
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Poisson Dependency and Head-Run Definitions (`Formalization.Defs.PoissonDep`)

Defines the Chen–Stein test-function class `poissonSteinClass` (Theorem 4.5 `\label{thm101}`,
`SteinIntro.tex:1911-1916`) together with the head-run indicators `headRunIndicator`, total run
count `headRunCount`, longest quality-$a$ run length `longestQualityRun`, and binary relative
entropy `klDivBernoulli` for Section 4.2.1 (`SteinIntro.tex:2010-2078`).
-/

open scoped NNReal

namespace SteinMethod

/-- Function class $\mathcal{F}$ satisfying eq. `(4.2)` (`\label{102}`, `SteinIntro.tex:1881-1884`,
used in Theorem 4.5 `\label{thm101}`, `SteinIntro.tex:1911-1916`):
$\|f\| \le \min\{1, r^{-1/2}\}$ and $\|\Delta f\| \le (1 - e^{-r}) / r$. -/
def poissonSteinClass (r : ℝ≥0) : Set (ℕ → ℝ) :=
  {f | (∀ k : ℕ, |f k| ≤ min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
    (∀ k : ℕ, |fwdDiff 1 f k| ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ))}

/-- De-clumped indicator $X_{i+1}$ (`0`-indexed $i \in \{0, \dots, n - k\}$ corresponding to
$1$-indexed $1, \dots, n - k + 1$) that a head run of length at least $k$ begins at position $i$ in
$n$ coin tosses (`SteinIntro.tex:2013-2021`). -/
def headRunIndicator {n : ℕ} (k : ℕ) (y : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i + k ≤ n then
    (match i with
      | 0 => 1
      | r + 1 => 1 - y ⟨r, by omega⟩) *
      ∏ j : Fin k, y ⟨i + j.1, by omega⟩
  else 0

/-- Total count $W = \sum_{i=1}^{n-k+1} X_i$ of head runs of length at least $k$ in $n$ coin tosses
(`SteinIntro.tex:2010-2021`, Theorem 4.8 `\label{thm104}`). -/
def headRunCount {n : ℕ} (k : ℕ) (y : Fin n → ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n - k + 1), headRunIndicator k y i

open Classical in
/-- Length $R_n$ of the longest quality-$a$ head run in $n$ coin tosses `y : Fin n → ℕ`, i.e., the
greatest $j \in \{0, \dots, n\}$ for which some contiguous block of length $j$ has sum at least
$a j$ (`SteinIntro.tex:2055, 2066-2067, 2072`). At $a = 1$ on $\{0, 1\}$-valued sequences, this is
the length of the longest run of ones. -/
noncomputable def longestQualityRun {n : ℕ} (a : ℝ) (y : Fin n → ℕ) : ℕ :=
  Nat.findGreatest
    (fun j ↦ ∃ i : ℕ, ∃ h : i + j ≤ n,
      a * (j : ℝ) ≤ ∑ r : Fin j, (y ⟨i + r.1, by omega⟩ : ℝ))
    n

open Classical in
/-- Binary relative entropy $H(a, p)$ in the Erdős–Rényi law for longest quality-$a$ head runs
(Theorem 4.9, `SteinIntro.tex:2071-2078`): $H(1, p) = \log(1 / p)$ and
$H(a, p) = a \log(a / p) + (1 - a) \log((1 - a) / (1 - p))$ for $0 < a < 1$. -/
noncomputable def klDivBernoulli (a p : ℝ) : ℝ :=
  if a = 1 then Real.log (1 / p)
  else a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p))

end SteinMethod
