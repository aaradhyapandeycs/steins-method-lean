/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.AntiVoter
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Probability.Moments.Basic

/-!
# Concentration & Curie–Weiss Definitions (`Formalization.Defs.Concentration`)

Definitions for Section 7 (*Concentration Inequalities*, `SteinIntro.tex:3389-3887`), specifically
the Curie–Weiss Gibbs measure `(7.6)` (`\label{2199}`, `SteinIntro.tex:3631-3637`) on spin
configurations `Fin n → Bool` read into `{-1, 1} ⊂ ℝ` via `SteinMethod.spin`.
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-- Unnormalized Boltzmann weight
$\exp\bigl(\frac{\beta}{n}\sum_{i < j} \sigma_i \sigma_j + \beta h \sum_i \sigma_i\bigr)$
of a spin configuration `x : Fin n → Bool` in the Curie–Weiss model
(eq. `(7.6)` `\label{2199}`, `SteinIntro.tex:3631-3637`). -/
noncomputable def curieWeissWeight (n : ℕ) (β h : ℝ) (x : Fin n → Bool) : ℝ :=
  Real.exp
    (β / (n : ℝ) *
        (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), spin (x i) * spin (x j)) +
      β * h * ∑ i : Fin n, spin (x i))

/-- Partition function $Z = \sum_{\sigma \in \{-1, 1\}^n} w(\sigma) > 0$ of the Curie–Weiss model
(eq. `(7.6)` `\label{2199}`, `SteinIntro.tex:3631-3637`). -/
noncomputable def curieWeissPartition (n : ℕ) (β h : ℝ) : ℝ :=
  ∑ x : Fin n → Bool, curieWeissWeight n β h x

/-- Curie–Weiss Gibbs probability measure on `Fin n → Bool` assigning mass
$Z^{-1} \exp\bigl(\frac{\beta}{n}\sum_{i < j} \sigma_i \sigma_j + \beta h \sum_i \sigma_i\bigr)$
to each configuration `x` (eq. `(7.6)` `\label{2199}`, `SteinIntro.tex:3631-3637`). -/
noncomputable def curieWeissMeasure (n : ℕ) (β h : ℝ) : Measure (Fin n → Bool) :=
  Measure.sum fun x : Fin n → Bool ↦
    ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h) • Measure.dirac x

/-- Discrete measurable space on `Equiv.Perm (Fin n)` (`SteinIntro.tex:3599`). -/
instance instMeasurableSpacePermFin (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Discrete measurable singleton class on `Equiv.Perm (Fin n)` (`SteinIntro.tex:3599`). -/
instance instMeasurableSingletonClassPermFin (n : ℕ) :
    MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ ↦ trivial⟩

/-- Classical `Fintype` instance on transpositions `{π : Equiv.Perm (Fin n) // π.IsSwap}`
(`SteinIntro.tex:3604-3605`). -/
noncomputable instance instFintypeIsSwapPermFin (n : ℕ) :
    Fintype {π : Equiv.Perm (Fin n) // π.IsSwap} :=
  @Subtype.fintype _ _ (Classical.decPred _) inferInstance

end SteinMethod
