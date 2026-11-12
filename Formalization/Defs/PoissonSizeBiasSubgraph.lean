/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

/-!
# Subgraph Copy and Count Definitions (`Formalization.Defs.PoissonSizeBiasSubgraph`)

Pure definitions for Section 4.3.2 (*Application: Subgraph counts*, `SteinIntro.tex:2279-2369`)
of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `SteinMethod.embedGraph H f`: pushforward of a simple graph `H : SimpleGraph V` along a vertex
  embedding `f : V ↪ Fin n`, giving a copy of `H` in $K_n$.
* `SteinMethod.subgraphCopies H n`: the finite set $\Gamma$ of all copies of `H` in $K_n$
  (`SteinIntro.tex:2286`).
* `SteinMethod.subgraphCopyIndicator α G`: the `{0, 1}`-valued indicator
  $X_\alpha(G) = \mathbb{I}[\alpha \subseteq G]$ (`SteinIntro.tex:2286-2287`).
* `SteinMethod.subgraphCount H n G`: the total number
  $W = \sum_{\alpha \in \Gamma} X_\alpha(G)$ of copies of `H` in `G` (`SteinIntro.tex:2287`).
* `SteinMethod.subgraphCopiesWithDiffEdges H n α t`: the subset $\Gamma_\alpha^t \subseteq \Gamma$
  of copies of `H` in $K_n$ with exactly `t` edges not in `α` (`SteinIntro.tex:2315-2316`).
-/

namespace SteinMethod

/-- Pushforward of a simple graph `H` on `V` along a vertex embedding `f : V ↪ Fin n`, giving the
subgraph of $K_n$ on `Fin n` whose edges are the images of the edges of `H` under `f`
(`SteinIntro.tex:2280-2287`). -/
def embedGraph {V : Type*} {n : ℕ} (H : SimpleGraph V) (f : V ↪ Fin n) :
    SimpleGraph (Fin n) where
  Adj u v := ∃ x y : V, f x = u ∧ f y = v ∧ H.Adj x y
  symm := ⟨fun _ _ ⟨x, y, hxu, hyv, hxy⟩ ↦ ⟨y, x, hyv, hxu, hxy.symm⟩⟩
  loopless := ⟨fun _ ⟨x, _, hxu, hyu, hxy⟩ ↦
    H.loopless.irrefl x (f.injective (hxu.trans hyu.symm) ▸ hxy)⟩

/-- The finite set $\Gamma$ of all copies of $H$ in $K_n$, i.e., subgraphs of the complete graph on
`Fin n` isomorphic to $H$ on its non-isolated vertices (`SteinIntro.tex:2282-2287`). -/
noncomputable def subgraphCopies {V : Type*} (H : SimpleGraph V) (n : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  (Set.toFinite {α : SimpleGraph (Fin n) | ∃ f : V ↪ Fin n, α = embedGraph H f}).toFinset

/-- `{0, 1}`-valued indicator $X_\alpha(G) = \mathbb{I}[\alpha \subseteq G]$ that the subgraph
$\alpha$ appears in $G$ (`SteinIntro.tex:2286-2287`). -/
noncomputable def subgraphCopyIndicator {n : ℕ} (α G : SimpleGraph (Fin n)) : ℕ := by
  classical exact if α ≤ G then 1 else 0

/-- Total number $W(G) = \sum_{\alpha \in \Gamma} X_\alpha(G)$ of copies of $H$ in $G$
(`SteinIntro.tex:2286-2287`). -/
noncomputable def subgraphCount {V : Type*} (H : SimpleGraph V) (n : ℕ)
    (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ α ∈ subgraphCopies H n, subgraphCopyIndicator α G

/-- The subset $\Gamma_\alpha^t \subseteq \Gamma$ of copies $\beta \in \Gamma$ of $H$ in $K_n$
having exactly $t$ edges not in $\alpha$ (`SteinIntro.tex:2315-2316`). -/
noncomputable def subgraphCopiesWithDiffEdges {V : Type*} (H : SimpleGraph V) (n : ℕ)
    (α : SimpleGraph (Fin n)) (t : ℕ) : Finset (SimpleGraph (Fin n)) := by
  classical exact (subgraphCopies H n).filter fun β ↦ (β.edgeSet \ α.edgeSet).ncard = t

end SteinMethod
