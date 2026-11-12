/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.RandomGraph
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.IdentDistrib

/-!
# Poisson Size-Bias Coupling Definitions (`Formalization.Defs.PoissonSizeBias`)

Definitions introduced in Section 4.3 (*Size-bias Coupling*, `SteinIntro.tex:2113-2252`):
- `SteinMethod.IsExchangeableTuple`: exchangeability of an indexed family of random variables under
  all permutations of the index type (Corollary 4.12 `\label{cor122}`, `SteinIntro.tex:2148-2154`).
- `SteinMethod.degreeDCouplingPMF`: the random edge-deletion / edge-addition transition on
  `SimpleGraph (Fin n)` forcing vertex `v` to have degree `d` (Example 4.6,
  `SteinIntro.tex:2227-2234`).
-/

open MeasureTheory

namespace SteinMethod

/-- An indexed family $(X_i)_{i \in \iota}$ of random variables is exchangeable under `P` if its
joint distribution is invariant under every permutation $\sigma \in \mathrm{Perm}(\iota)$:
$(X_{\sigma(i)})_{i \in \iota} \stackrel{d}{=} (X_i)_{i \in \iota}$
(used in Corollary 4.12 `\label{cor122}`, `SteinIntro.tex:2148-2154`). -/
def IsExchangeableTuple {Ω ι α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (X : ι → Ω → α) : Prop :=
  ∀ σ : Equiv.Perm ι,
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X (σ i) ω) (fun ω i ↦ X i ω) P P

open Classical in
/-- Random graph transition in Example 4.6 (*Degree $d$ vertices*, `SteinIntro.tex:2227-2234`):
given a simple graph `G` on `Fin n`, vertex `v`, and target degree `d`:
- if `d₁ := (G.neighborFinset v).card ≥ d`, erase `d₁ - d` edges chosen uniformly at random from
  the `d₁` edges incident to `v`;
- if `d₁ < d` and `d < n` (so `d - d₁ ≤ n - 1 - d₁`), add edges from `v` to `d - d₁` vertices
  chosen uniformly at random from the `n - 1 - d₁` vertices distinct from `v` and non-adjacent to
  `v` (returning `PMF.pure G` outside the valid range `d < n` for totality without proof
  arguments). -/
noncomputable def degreeDCouplingPMF {n : ℕ} (d : ℕ) (v : Fin n)
    (G : SimpleGraph (Fin n)) : PMF (SimpleGraph (Fin n)) :=
  let N : Finset (Fin n) := G.neighborFinset v
  if d ≤ N.card then
    let choices := N.powersetCard (N.card - d)
    have hne : choices.Nonempty := Finset.powersetCard_nonempty.mpr (Nat.sub_le N.card d)
    (PMF.uniformOfFinset choices hne).map fun E ↦
      G.deleteEdges ((E.image fun u ↦ s(v, u)) : Set (Sym2 (Fin n)))
  else
    let nonNbrs : Finset (Fin n) := Finset.univ.erase v \ N
    let choices := nonNbrs.powersetCard (d - N.card)
    if hne : choices.Nonempty then
      (PMF.uniformOfFinset choices hne).map fun A ↦
        G ⊔ SimpleGraph.fromEdgeSet ((A : Set (Fin n)).image fun u ↦ s(v, u))
    else
      PMF.pure G

open Classical in
/-- `{0, 1}`-valued `ℕ` edge-presence indicator of `e : EdgePair n` in `G`
(`SteinIntro.tex:2424-2449`). -/
noncomputable def edgeIndNat {n : ℕ} (e : EdgePair n) (G : SimpleGraph (Fin n)) : ℕ :=
  if e.1 ∈ G.edgeSet then 1 else 0

/-- Reconstruct a simple graph on `Fin n` from a vector on `Fin (Fintype.card (EdgePair n)) → ℕ`
by thresholding each coordinate at `1` (`SteinIntro.tex:2424-2449`). -/
noncomputable def graphOfNatEdgeVec {n : ℕ}
    (y : Fin (Fintype.card (EdgePair n)) → ℕ) : SimpleGraph (Fin n) :=
  graphOfEdgeBits (fun e : EdgePair n ↦ decide (1 ≤ y (Fintype.equivFin (EdgePair n) e)))

open Classical in
/-- Edge-indicator representation of `subgraphCopyIndicator α`: `1` if `α` is a subgraph of
`graphOfNatEdgeVec y`, and `0` otherwise (`SteinIntro.tex:2424-2427`). -/
noncomputable def subgraphEdgeFn {n : ℕ} (α : SimpleGraph (Fin n))
    (y : Fin (Fintype.card (EdgePair n)) → ℕ) : ℕ :=
  if α ≤ graphOfNatEdgeVec y then 1 else 0

open Classical in
/-- Monotone edge-indicator representation of the large-degree indicator $\mathbb{I}[\deg(v) \ge d]$
(`SteinIntro.tex:2429-2430`). -/
noncomputable def largeDegEdgeFn {n : ℕ} (v : Fin n) (d : ℕ)
    (y : Fin (Fintype.card (EdgePair n)) → ℕ) : ℕ :=
  if d ≤ (graphOfNatEdgeVec y).degree v then 1 else 0

open Classical in
/-- Antitone edge-indicator representation of the small-degree indicator $\mathbb{I}[\deg(v) \le d]$
(`SteinIntro.tex:2441-2442`). -/
noncomputable def smallDegEdgeFn {n : ℕ} (v : Fin n) (d : ℕ)
    (y : Fin (Fintype.card (EdgePair n)) → ℕ) : ℕ :=
  if (graphOfNatEdgeVec y).degree v ≤ d then 1 else 0

end SteinMethod
