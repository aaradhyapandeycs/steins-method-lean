/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Probability.Distributions.Uniform

/-!
# Anti-Voter Model Definitions (`Formalization.Defs.AntiVoter`)

Core definitions for the anti-voter Markov chain on a finite simple graph $G = (V, E)$
(Section 3.3.1, `SteinIntro.tex:1099-1219`; `docs/DEFINITIONS.md` §4.5):
* `spin`: maps `Bool` labels to `±1 : ℝ` (`true ↦ 1`, `false ↦ -1`), with opposite label `!b`.
* `antiVoterStep`: one step of the anti-voter chain on `V → Bool`.
* `IsAntiVoterStationary`: stationarity of a measure on `V → Bool` under `antiVoterStep G`.
* `kappa`: minimum over cuts `A ⊆ V` of the number of edges of `G` with both endpoints in `A`
  or both endpoints in `Aᶜ` (`SteinIntro.tex:1209-1211`).
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-- Spin value in `{-1, 1} ⊂ ℝ` of a Boolean vertex label (`SteinIntro.tex:1102-1107`). -/
def spin (b : Bool) : ℝ :=
  if b then 1 else -1

/-- One transition step of the anti-voter Markov chain on `G` (`SteinIntro.tex:1103-1105`):
choose a vertex `v` uniformly from `V`, choose a neighbor `u` uniformly from `G.neighborFinset v`,
and update the label at `v` to `!(x u)`.

As a totality convention, if `V` is empty or `v` has no neighbor in `G`, the chain stays at `x`
(`PMF.pure x`). Under the hypotheses of Theorem 3.8 and Lemma 3.10 every vertex has `r ≥ 1`
neighbors, so the fallback branch is never taken (`docs/DEFINITIONS.md` §4.5). -/
noncomputable def antiVoterStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool) : PMF (V → Bool) :=
  if hV : (Finset.univ : Finset V).Nonempty then
    (PMF.uniformOfFinset Finset.univ hV).bind fun v ↦
      if hN : (G.neighborFinset v).Nonempty then
        (PMF.uniformOfFinset (G.neighborFinset v) hN).map fun u ↦ Function.update x v (!x u)
      else
        PMF.pure x
  else
    PMF.pure x

/-- Stationarity of a measure `ν` on `V → Bool` for the anti-voter chain on `G`
(`SteinIntro.tex:1110-1116`). -/
def IsAntiVoterStationary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) : Prop :=
  ∀ y : V → Bool, ν {y} = ∑ x : V → Bool, ν {x} * antiVoterStep G x y

/-- Minimum over vertex subsets `A : Finset V` of the number of edges of `G` (each counted once in
`G.edgeFinset`) with both endpoints in `A` or both endpoints in `Aᶜ` (`\kappa(G)`,
`SteinIntro.tex:1209-1211`). -/
def kappa {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun A : Finset V ↦
    (G.edgeFinset.filter fun e ↦ e ∈ A.sym2 ∨ e ∈ Aᶜ.sym2).card

end SteinMethod
