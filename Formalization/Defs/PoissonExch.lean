/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Concentration
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Perm.Support
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Poisson Exchangeable-Pair Definitions (`Formalization.Defs.PoissonExch`)

Definitions for Section 4.4 (*Exchangeable Pairs* for Poisson approximation,
`SteinIntro.tex:2606-2711`):

* `condExpAt`: conditional expectation with explicit sub-σ-algebra `m` and ambient σ-algebra `m₀`,
  used when both `MeasurableSpace Ω` structures are simultaneously in scope (Theorem 4.20,
  `SteinIntro.tex:2618-2660`).
* `numFixedPoints`: number of fixed points of a permutation on `Fin n` (Example 4.21,
  `SteinIntro.tex:2683`).
* `numTwoCycles`: number of 2-cycles (transpositions) in a permutation's disjoint cycle
  decomposition (Example 4.21, `SteinIntro.tex:2684`).

Discrete measurable-space instances on `Equiv.Perm (Fin n)` and the `Fintype` instance on
transpositions `{π : Equiv.Perm (Fin n) // π.IsSwap}` are re-exported from
`Formalization.Defs.Concentration` so Sections 4.4 and 7.1 share a single canonical set of
instances.
-/

open MeasureTheory

namespace SteinMethod

/-- Conditional expectation with explicit sub-σ-algebra `m` and ambient σ-algebra `m₀`.
Avoids `MeasurableSpace` instance-resolution ambiguity when both `m` and `m₀` are in scope on `Ω`
(Theorem 4.20, `SteinIntro.tex:2618-2660`). -/
noncomputable abbrev condExpAt {Ω : Type*} (m m₀ : MeasurableSpace Ω)
    (P : @Measure Ω m₀) (f : Ω → ℝ) : Ω → ℝ :=
  @condExp Ω ℝ m m₀ _ _ P f

/-- Number of fixed points $|\{i \in \mathrm{Fin}\,n \mid \pi(i) = i\}|$ of a permutation
$\pi \in \mathrm{Sym}(n)$ (Example 4.21, `SteinIntro.tex:2683`). -/
def numFixedPoints {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i ↦ π i = i).card

/-- Number of 2-cycles (transpositions) in the disjoint cycle decomposition of a permutation
$\pi$. A 2-cycle is a cycle factor whose support has cardinality exactly 2
(Example 4.21, `SteinIntro.tex:2684`). -/
noncomputable def numTwoCycles {α : Type*} [Fintype α] [DecidableEq α]
    (π : Equiv.Perm α) : ℕ :=
  (π.cycleFactorsFinset.filter fun c ↦ c.support.card = 2).card

end SteinMethod
