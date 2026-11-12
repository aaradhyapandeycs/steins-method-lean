/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Branching.Basic
import Formalization.Defs
import Formalization.Defs.AntiVoter
import Formalization.Defs.Sanity
import Formalization.Exponential.GeometricSumsCounterexampleAux
import Formalization.PoissonSizeBias.Monotone.FKGCore
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.Distributions.Uniform

/-!
# Canonical Library Duplicate Bridges (`Formalization.Canon.LibraryDuplicates`)

Unifies public project helpers across proof modules identified in `canon-audit.md` §2.2
(Clusters D2–D6), and documents private file-local duplicates:

### Cluster D2 (Rademacher Spin Mappings)
* Accessible helper `Counterexample57.ceRad`
  (`Formalization/Exponential/GeometricSumsCounterexampleAux.lean:41`) matches `spin`
  (`Formalization/Defs/AntiVoter.lean:28`) and `rademacherVal`
  (`Formalization/Defs/Sanity.lean:228`).

### Cluster D3 (Fair Coin Measures)
* Accessible helper `Counterexample57.ceBern`
  (`Formalization/Exponential/GeometricSumsCounterexampleAux.lean:26`) matches
  `bernoulliHalfMeasure` (`Formalization/Defs/Sanity.lean:150`).
* Private file-local duplicates intentionally not imported:
  - `ceNuBern` (`Formalization/Exponential/GeometricSumsCounterexample.lean:28`)
  - `fairCoinBool` (`Formalization/PoissonDep/ErdosRenyiCounterexample.lean:49`).

### Cluster D4 (Boolean Indicators and Vector Lifts)
* Accessible helper `boolToNat`
  (`Formalization/PoissonSizeBias/Monotone/FKGCore.lean:29`) matches core Lean `Bool.toNat`.
* Accessible vector lift `vecBoolToNat` evaluates via `Bool.toNat`.
* Private file-local duplicates intentionally not imported:
  - `boolVal` (`Formalization/Concentration/CircularRuns.lean:31`)
  - `bitToReal` (`Formalization/RandomGraph/ErdosRenyi.lean:148`)
  - `boolIndNat` (`Formalization/PoissonSizeBias/Negative/Hypergeometric.lean:52`)
  - `natOfBoolVec` (`Formalization/PoissonSizeBias/Monotone/Lemma4_18.lean:313`).

### Cluster D5 (Edge and Subgraph Indicators)
* All public indicators unified in `Formalization.Canon.GraphsAndPerms` and
  `Formalization.Canon.DefsUnification`.

### Cluster D6 (Uniform Lebesgue Measures on the Unit Interval)
* Accessible helper `unitIntervalIooMeasure`
  (`Formalization/Branching/Basic.lean:481`) equals continuous conditional Lebesgue measure
  `ProbabilityTheory.cond volume (Set.Ioo 0 1)` and witnesses Mathlib's `pdf.IsUniform`.
* Private file-local duplicate: `unitIooMeasure`
  (`Formalization/PoissonSizeBias/Monotone/Basic.lean:174`).
-/

open MeasureTheory ProbabilityTheory

namespace SteinMethod

/-! ### Cluster D2: Rademacher Spin Bridges -/

/-- Counterexample Rademacher spin map `Counterexample57.ceRad`
(`Formalization/Exponential/GeometricSumsCounterexampleAux.lean:41`) equals `spin`
(`SteinIntro.tex:1620-1628`, `Formalization/Defs/AntiVoter.lean:28`). -/
theorem ceRad_eq_spin : Counterexample57.ceRad = spin := by
  ext b
  cases b <;> rfl

/-- Counterexample Rademacher spin map `Counterexample57.ceRad` equals `rademacherVal`
(`SteinIntro.tex:952-960`, `Formalization/Defs/Sanity.lean:228`). -/
theorem ceRad_eq_rademacherVal : Counterexample57.ceRad = rademacherVal := by
  ext b
  cases b <;> rfl

/-! ### Cluster D3: Bernoulli(1/2) Measure Bridges -/

/-- Counterexample fair Bernoulli measure `Counterexample57.ceBern`
(`Formalization/Exponential/GeometricSumsCounterexampleAux.lean:26`) equals
`bernoulliHalfMeasure` (`Formalization/Defs/Sanity.lean:150`). -/
theorem ceBern_eq_bernoulliHalfMeasure :
    Counterexample57.ceBern = bernoulliHalfMeasure :=
  rfl

/-! ### Cluster D4: Boolean to Nat Indicator Bridges -/

/-- Harris–Kleitman Boolean-to-Nat map `boolToNat`
(`Formalization/PoissonSizeBias/Monotone/FKGCore.lean:29`) equals core Lean `Bool.toNat`. -/
theorem boolToNat_eq_toNat : boolToNat = Bool.toNat := by
  ext b
  cases b <;> rfl

/-- Vector Boolean-to-Nat coordinate projection `vecBoolToNat` evaluates to `(b j).toNat`. -/
theorem vecBoolToNat_apply {N : ℕ} (b : Fin N → Bool) (j : Fin N) :
    vecBoolToNat b j = (b j).toNat := by
  dsimp [vecBoolToNat, boolToNat]
  cases b j <;> rfl

/-! ### Cluster D6: Unit Interval Uniform Measures -/

/-- Branching spine uniform measure `unitIntervalIooMeasure`
(`Formalization/Branching/Basic.lean:481`) equals continuous conditional Lebesgue measure
`ProbabilityTheory.cond volume (Set.Ioo (0 : ℝ) 1)`. -/
theorem unitIntervalIooMeasure_eq_cond_volume :
    unitIntervalIooMeasure = ProbabilityTheory.cond volume (Set.Ioo (0 : ℝ) 1) :=
  rfl

/-- Branching spine uniform measure `unitIntervalIooMeasure`
(`Formalization/Branching/Basic.lean:481`) witnesses Mathlib's `MeasureTheory.pdf.IsUniform`. -/
theorem isUniform_id_unitIntervalIooMeasure :
    MeasureTheory.pdf.IsUniform id (Set.Ioo (0 : ℝ) 1) unitIntervalIooMeasure where
  aemeasurable := aemeasurable_id
  map_eq := by rw [Measure.map_id, unitIntervalIooMeasure]

/-- Branching spine uniform measure `unitIntervalIooMeasure` equals conditional Lebesgue measure
on the closed unit interval `Set.Icc 0 1` up to boundary null sets `{0, 1}`. -/
theorem unitIntervalIooMeasure_eq_cond_volume_Icc :
    unitIntervalIooMeasure = ProbabilityTheory.cond volume (Set.Icc (0 : ℝ) 1) := by
  dsimp [unitIntervalIooMeasure, ProbabilityTheory.cond]
  rw [Real.volume_Ioo, Real.volume_Icc]
  norm_num
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc

end SteinMethod
