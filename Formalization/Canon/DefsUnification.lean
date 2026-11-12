/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.AntiVoter
import Formalization.Defs.Exponential
import Formalization.Defs.Geometric
import Formalization.Defs.NormalStein
import Formalization.Defs.PoissonSizeBias
import Formalization.Defs.PoissonSizeBiasMonotone
import Formalization.Defs.PoissonSizeBiasSubgraph
import Formalization.Defs.PoissonStein
import Formalization.Defs.RandomGraph
import Formalization.Defs.Sanity
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Order.Monotone.Basic

/-!
# Canonical Definition Unification Bridges (`Formalization.Canon.DefsUnification`)

Unifies project-specific definitions across `Formalization/Defs/*.lean` with canonical
Mathlib notions and eliminates internal representations/duplicates:
* `isIncreasing_iff_monotone`: `IsIncreasing` (`Formalization/Defs/PoissonSizeBiasMonotone.lean:22`)
  is definitionally equal to Mathlib's `Monotone`.
* `isDecreasing_iff_antitone`: `IsDecreasing` (`Formalization/Defs/PoissonSizeBiasMonotone.lean:27`)
  is definitionally equal to Mathlib's `Antitone`.
* `edgeIndNat_cast_eq_edgeIndicator`: natural indicator `edgeIndNat`
  (`Formalization/Defs/PoissonSizeBias.lean:64`) agrees with real `edgeIndicator`.
* `subgraphEdgeFn_eq_subgraphCopyIndicator`: edge vector representation `subgraphEdgeFn`
  (`Formalization/Defs/PoissonSizeBias.lean:76`) agrees with `subgraphCopyIndicator`.
* `normalSteinOp_eq_normalSteinOpLeft_of_differentiableAt`: two-sided normal Stein operator
  `normalSteinOp` (`Formalization/Defs/NormalStein.lean:28`) matches left operator
  `normalSteinOpLeft` at points of differentiability.
* `fwdDiff_one_apply`: evaluation of Mathlib's `fwdDiff 1 f k`
  (`Mathlib/Algebra/Group/ForwardDiff.lean:45`).
* `poissonSteinOp_fwdDiff`: expresses `poissonSteinOp` (`Formalization/Defs/PoissonStein.lean:23`)
  in terms of Mathlib's forward difference `fwdDiff 1`.
* `geomSteinOp_fwdDiff`: definitional forward difference form of `geomSteinOp`
  (`Formalization/Defs/Geometric.lean:53`).
* `rademacherVal_eq_spin`: `rademacherVal` (`Formalization/Defs/Sanity.lean:228`) matches `spin`
  (`Formalization/Defs/AntiVoter.lean:28`).
* `rademacherFst_eq_spin_comp_fst` & `rademacherSnd_eq_spin_comp_snd`: coordinate projections.
* `shiftedGeomLaw_eq_posGeomLaw`: agreement of `shiftedGeomLaw`
  (`Formalization/Defs/Exponential.lean:84`) and `posGeomLaw`
  (`Formalization/Defs/Geometric.lean:47`).
-/

open scoped NNReal

namespace SteinMethod

/-! ### Monotonicity Bridges -/

/-- `IsIncreasing` on coordinate functions (`SteinIntro.tex:2196-2200`,
`Formalization/Defs/PoissonSizeBiasMonotone.lean:22`)
is definitionally equal to Mathlib's `Monotone` (`Mathlib/Order/Monotone/Basic.lean:42`). -/
theorem isIncreasing_iff_monotone {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    IsIncreasing f ↔ Monotone f :=
  Iff.rfl

/-- `IsDecreasing` on coordinate functions (`SteinIntro.tex:2196-2200`,
`Formalization/Defs/PoissonSizeBiasMonotone.lean:27`)
is definitionally equal to Mathlib's `Antitone` (`Mathlib/Order/Monotone/Basic.lean:48`). -/
theorem isDecreasing_iff_antitone {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    IsDecreasing f ↔ Antitone f :=
  Iff.rfl

/-! ### Discrete Geometric Law Representation -/

/-- Positive geometric distribution `shiftedGeomLaw` (`SteinIntro.tex:2881-2884`,
`Formalization/Defs/Exponential.lean:84`) is definitionally equal to `posGeomLaw`
(`SteinIntro.tex:3225-3228`, `Formalization/Defs/Geometric.lean:47`). -/
theorem shiftedGeomLaw_eq_posGeomLaw (p : ℝ) :
    shiftedGeomLaw p = posGeomLaw p :=
  rfl

/-! ### Rademacher Spin Representations -/

/-- Rademacher coordinate value `rademacherVal` (`SteinIntro.tex:952-960`,
`Formalization/Defs/Sanity.lean:228`) equals `spin` (`SteinIntro.tex:1620-1628`,
`Formalization/Defs/AntiVoter.lean:28`). -/
theorem rademacherVal_eq_spin : rademacherVal = spin := by
  ext b
  cases b <;> rfl

/-- First Rademacher coordinate `rademacherFst` (`Formalization/Defs/Sanity.lean:235`)
equals `spin ∘ Prod.fst`. -/
theorem rademacherFst_eq_spin_comp_fst : rademacherFst = spin ∘ Prod.fst := by
  ext ⟨b₁, b₂⟩
  cases b₁ <;> rfl

/-- Second Rademacher coordinate `rademacherSnd` (`Formalization/Defs/Sanity.lean:241`)
equals `spin ∘ Prod.snd`. -/
theorem rademacherSnd_eq_spin_comp_snd : rademacherSnd = spin ∘ Prod.snd := by
  ext ⟨b₁, b₂⟩
  cases b₂ <;> rfl

/-! ### Edge and Subgraph Indicator Bridges -/

/-- Natural edge indicator `edgeIndNat` (`Formalization/Defs/PoissonSizeBias.lean:64`,
`SteinIntro.tex:2424-2449`) cast to `ℝ` equals real indicator `edgeIndicator`
(`Formalization/Defs/RandomGraph.lean:55`). -/
theorem edgeIndNat_cast_eq_edgeIndicator {n : ℕ} (e : EdgePair n)
    (G : SimpleGraph (Fin n)) :
    ((edgeIndNat e G : ℕ) : ℝ) = edgeIndicator e G := by
  dsimp [edgeIndNat, edgeIndicator, Set.indicator]
  split_ifs <;> simp

/-- Subgraph edge function `subgraphEdgeFn` (`Formalization/Defs/PoissonSizeBias.lean:76`,
`SteinIntro.tex:2424-2427`) equals `subgraphCopyIndicator α (graphOfNatEdgeVec y)`. -/
theorem subgraphEdgeFn_eq_subgraphCopyIndicator {n : ℕ} (α : SimpleGraph (Fin n))
    (y : Fin (Fintype.card (EdgePair n)) → ℕ) :
    subgraphEdgeFn α y = subgraphCopyIndicator α (graphOfNatEdgeVec y) :=
  rfl

/-! ### Stein Operator Bridges -/

/-- Agreement of left-derivative normal Stein operator `normalSteinOpLeft`
(`Formalization/Defs/NormalStein.lean:46`) with two-sided operator `normalSteinOp`
(`SteinIntro.tex:563-566`, `Formalization/Defs/NormalStein.lean:28`) at points of
differentiability. -/
theorem normalSteinOp_eq_normalSteinOpLeft_of_differentiableAt
    (f : ℝ → ℝ) (w : ℝ) (hf : DifferentiableAt ℝ f w) :
    normalSteinOpLeft f w = normalSteinOp f w := by
  dsimp [normalSteinOpLeft, normalSteinOp]
  rw [hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Iic w w Set.self_mem_Iic)]

/-- Evaluation of forward difference `fwdDiff 1 f k` (`Mathlib/Algebra/Group/ForwardDiff.lean:45`)
on `ℕ → ℝ`. -/
theorem fwdDiff_one_apply (f : ℕ → ℝ) (k : ℕ) :
    fwdDiff 1 f k = f (k + 1) - f k :=
  rfl

/-- Poisson Stein operator `poissonSteinOp` (`SteinIntro.tex:1824-1827`,
`Formalization/Defs/PoissonStein.lean:23`) expressed via Mathlib's `fwdDiff 1`. -/
theorem poissonSteinOp_fwdDiff (r : ℝ≥0) (f : ℕ → ℝ) (k : ℕ) :
    poissonSteinOp r f k = (r : ℝ) * fwdDiff 1 f k + (r - (k : ℝ)) * f k := by
  dsimp [poissonSteinOp, fwdDiff]
  ring

/-- Geometric Stein operator `geomSteinOp` (`SteinIntro.tex:3230-3233`,
`Formalization/Defs/Geometric.lean:53`) expressed via Mathlib's `fwdDiff 1`. -/
theorem geomSteinOp_fwdDiff (p : ℝ) (f : ℕ → ℝ) (k : ℕ) :
    geomSteinOp p f k = (1 - p) * fwdDiff 1 f k - p * f k + p * f 0 :=
  rfl

end SteinMethod
