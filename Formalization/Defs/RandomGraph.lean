/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.SimpleGraph
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Topology.UnitInterval

/-!
# Erdős–Rényi Random Graph Definitions (`SteinIntro.tex:918-920, 1354-1358`)

Defines the Erdős–Rényi random graph measure $G(n, p)$ (`SteinMethod.erdosRenyi n p`) on
`SimpleGraph (Fin n)` together with the unordered distinct-vertex pair index type
`SteinMethod.EdgePair n`, the edge-bit graph constructor `SteinMethod.graphOfEdgeBits`, and the
undirected edge indicators `SteinMethod.edgeIndicator`.

See [`docs/DEFINITIONS.md`](../../docs/DEFINITIONS.md) §4.6 for the specification and representation
notes.
-/

open MeasureTheory

namespace SteinMethod

/-- Unordered pairs of distinct vertices of `Fin n`, indexing the $\binom{n}{2}$ potential edges of
a simple graph on `Fin n`. -/
abbrev EdgePair (n : ℕ) : Type :=
  {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- Construct a simple graph on `Fin n` from its boolean edge-presence vector on `EdgePair n`. -/
def graphOfEdgeBits {n : ℕ} (ω : EdgePair n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e : Sym2 (Fin n) | ∃ h : ¬ e.IsDiag, ω ⟨e, h⟩ = true}

/-- The Erdős–Rényi random graph law $G(n, p)$ on `SimpleGraph (Fin n)`
(`SteinIntro.tex:919, 1355`): pushforward under `graphOfEdgeBits` of the product of independent
`Bernoulli(p)` measures over all $\binom{n}{2}$ potential edges `EdgePair n`.

For $p \in [0, 1]$, `Set.projIcc 0 1 zero_le_one p` equals `⟨p, hp₀, hp₁⟩`; clamping outside
$[0, 1]$ is a totality convention so `erdosRenyi n p` takes `(n : ℕ) (p : ℝ)` without proof
arguments. -/
noncomputable def erdosRenyi (n : ℕ) (p : ℝ) : Measure (SimpleGraph (Fin n)) :=
  (Measure.pi fun _ : EdgePair n ↦
    ProbabilityTheory.bernoulliMeasure true false
      (Set.projIcc 0 1 zero_le_one p)).map graphOfEdgeBits

/-- Real `{0, 1}`-valued indicator that undirected edge `e : EdgePair n` is present in `G`. -/
noncomputable def edgeIndicator {n : ℕ} (e : EdgePair n) (G : SimpleGraph (Fin n)) : ℝ :=
  {H : SimpleGraph (Fin n) | e.1 ∈ H.edgeSet}.indicator 1 G

end SteinMethod
