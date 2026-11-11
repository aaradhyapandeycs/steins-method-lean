/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.UnitInterval

/-!
# Section 6 Geometric Approximation Definitions (`Formalization.Defs.Geometric`)

Core definitions for Section 6 (*Geometric approximation*, `SteinIntro.tex:3190-3388`) of
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `geomLaw`: geometric distribution $\mathrm{Ge}^0(p)$ on $\mathbb{N} = \{0, 1, 2, \dots\}$ with
  $\mathbb{P}(N = k) = (1 - p)^k p$, reusing `ProbabilityTheory.geometricMeasure`.
* `posGeomLaw`: positive-support geometric distribution $\mathrm{Ge}(p)$ on $\{1, 2, \dots\}$.
* `geomSteinOp`, `geomSteinSol`, `geomSteinClass`: geometric Stein operator, canonical solution
  $f_A$, and test class $\mathcal{F}$.
* `IsDiscreteEquilibrium`: discrete equilibrium distributional relation `(6.1)`.
* `uniformAttachment`, `digraphOfTargets`, `digraphInDegree`: uniform attachment random directed
  graph $G_n$ on `Digraph (Fin n)` and vertex in-degree.
-/

open MeasureTheory

namespace SteinMethod

/-- Geometric distribution $\mathrm{Ge}^0(p)$ on $\mathbb{N} = \{0, 1, 2, \dots\}$ with point
probabilities $\mathbb{P}(N = k) = (1 - p)^k p$ for $0 < p \le 1$
(Section 6.1, `SteinIntro.tex:3223-3225`), reusing `ProbabilityTheory.geometricMeasure` via
`Set.projIcc 0 1 zero_le_one p`. -/
noncomputable def geomLaw (p : ℝ) : Measure ℕ :=
  ProbabilityTheory.geometricMeasure (Set.projIcc 0 1 zero_le_one p)

/-- Positive-support geometric distribution $\mathrm{Ge}(p)$ on $\{1, 2, \dots\} \subset \mathbb{N}$
with point probabilities $\mathbb{P}(X = k) = (1 - p)^{k - 1} p$ for $k \ge 1$ and $0 < p \le 1$
(Example 5.4 `\label{ex171}`, `SteinIntro.tex:2884`; Section 6 opening,
`SteinIntro.tex:3194-3198`). -/
noncomputable def posGeomLaw (p : ℝ) : Measure ℕ :=
  (geomLaw p).map (· + 1)

/-- Geometric Stein characterizing operator
$\mathcal{A}f(k) = (1 - p)\Delta f(k) - p f(k) + p f(0)$ on $\mathbb{N}$
(Lemma 6.1 `\label{lem173}`, `SteinIntro.tex:3230-3233`). -/
def geomSteinOp (p : ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (1 - p) * fwdDiff 1 f k - p * f k + p * f 0

/-- Canonical solution
$f_A(k) = \sum_{i \in A} (1 - p)^i - \sum_{i \in A,\, i \ge k} (1 - p)^{i - k}$
of the geometric Stein equation
$(1 - p)\Delta f_A(k) - p f_A(k) = \mathbb{I}[k \in A] - \mathbb{P}(Z \in A)$ with $f_A(0) = 0$
(Lemma 6.2 `\label{lem174}`, `SteinIntro.tex:3243-3249, 3266-3268`). -/
noncomputable def geomSteinSol (p : ℝ) (A : Set ℕ) (k : ℕ) : ℝ :=
  (∑' i : ℕ, A.indicator (fun i ↦ (1 - p) ^ i) i) -
    ∑' i : ℕ, (A ∩ Set.Ici k).indicator (fun i ↦ (1 - p) ^ (i - k)) i

/-- Test function class $\mathcal{F} = \{f : \mathbb{N} \to \mathbb{R} \mid f(0) = 0 \text{ and }
\|\Delta f\| \le 1\}$ for total variation geometric approximation
(Theorem 6.3 `\label{thm178}`, `SteinIntro.tex:3252`). -/
def geomSteinClass : Set (ℕ → ℝ) :=
  {f | f 0 = 0 ∧ ∀ k : ℕ, |fwdDiff 1 f k| ≤ 1}

/-- Discrete equilibrium distributional relation
$p\,\mathbb{E}[f(W)] - p f(0) = (1 - p)\,\mathbb{E}[\Delta f(W^e)]$ for all
$f : \mathbb{N} \to \mathbb{R}$ with $\|\Delta f\| < \infty$, where $W \ge 0$ is integer-valued
with $\mathbb{E}[W] = (1 - p)/p$ and $0 < p \le 1$
(Definition 6.1, eq. `(6.1)` `\label {1717}`, `SteinIntro.tex:3283-3289`). -/
def IsDiscreteEquilibrium {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (p : ℝ) (W : Ω → ℕ) (P' : Measure Ω') (We : Ω' → ℕ) : Prop :=
  0 < p ∧ p ≤ 1 ∧ AEMeasurable W P ∧ Integrable (fun ω ↦ (W ω : ℝ)) P ∧
    ∫ ω, (W ω : ℝ) ∂P = (1 - p) / p ∧ AEMeasurable We P' ∧
    ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |fwdDiff 1 f k| ≤ C) →
      p * (∫ ω, f (W ω) ∂P) - p * f 0 = (1 - p) * ∫ ω', fwdDiff 1 f (We ω') ∂P'

/-- Pullback measurable space structure on `Digraph V` induced by `Digraph.Adj`
(Section 6.3, `SteinIntro.tex:3334-3341`). -/
instance instMeasurableSpaceDigraph {V : Type*} : MeasurableSpace (Digraph V) :=
  .comap Digraph.Adj inferInstance

/-- Directed graph on `Fin n` (allowing self-loops) constructed from the attachment target vector
`t : ∀ k : Fin n, Fin (k.val + 1)`, with a directed edge `u → v` iff `(t u).val = v.val`
(Section 6.3, `SteinIntro.tex:3334-3341`). -/
def digraphOfTargets {n : ℕ} (t : ∀ k : Fin n, Fin (k.val + 1)) : Digraph (Fin n) where
  Adj u v := (t u).val = v.val

/-- Uniform attachment random directed graph law $G_n$ on `Digraph (Fin n)`: node $0$ has a
self-loop (`Fin 1`), and each subsequent node $k \in \mathrm{Fin}\,n$ independently attaches one
outgoing directed edge to a target chosen uniformly from $\{0, \dots, k\}$ (`Fin (k.val + 1)`)
(Section 6.3, `SteinIntro.tex:3334-3341`). -/
noncomputable def uniformAttachment (n : ℕ) : Measure (Digraph (Fin n)) :=
  (Measure.pi fun k : Fin n ↦
    (@PMF.uniformOfFintype (Fin (k.val + 1)) inferInstance ⟨⟨0, Nat.succ_pos _⟩⟩).toMeasure).map
      digraphOfTargets

/-- In-degree of vertex `v` in a directed graph `G` (counting a self-loop `v → v` once toward the
in-degree of `v`, matching `SteinIntro.tex:3335-3336`). -/
noncomputable def digraphInDegree {V : Type*} (G : Digraph V) (v : V) : ℕ :=
  {u : V | G.Adj u v}.ncard

end SteinMethod
