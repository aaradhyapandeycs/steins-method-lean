/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Probability.Independence.Basic

/-!
# Dependency Neighborhoods and Dependency Graphs (`Formalization.Defs.Dependency`)

Formalizes Definition 3.1 (`SteinIntro.tex:805-809`) and the dependency-graph notion described at
`SteinIntro.tex:810-812` (used in `Thm3_5_corrected`, `ISSUE-3.5`).
-/

open MeasureTheory

namespace SteinMethod

/-- Definition 3.1 (`SteinIntro.tex:805-809`), literal: a collection $(X_1, \dots, X_n)$ has
dependency neighborhoods $N_i \subseteq \{1, \dots, n\}$ if $X_i$ is independent of
$\{X_j\}_{j \notin N_i}$ for each $i$. -/
def HasDependencyNeighborhoods {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (N : Fin n → Finset (Fin n)) : Prop :=
  ∀ i, ProbabilityTheory.IndepFun (X i) (fun ω (j : {j // j ∉ N i}) ↦ X j ω) P

/-- Dependency graph, the notion described in the prose at `SteinIntro.tex:810-812`
("dependency neighborhoods are frequently referred to as dependency graphs");
the hypothesis of `Thm3_5_corrected` (`ISSUE-3.5`). -/
def IsDependencyGraph {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Fin n → Ω → ℝ) (N : Fin n → Finset (Fin n)) : Prop :=
  (∀ i, i ∈ N i) ∧ (∀ i j, j ∈ N i → i ∈ N j) ∧
  ∀ A B : Finset (Fin n), (∀ a ∈ A, ∀ b ∈ B, b ∉ N a) →
    ProbabilityTheory.IndepFun (fun ω (a : A) ↦ X a ω) (fun ω (b : B) ↦ X b ω) P

end SteinMethod
