/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.BerryEsseen.BerryEsseen
import Formalization.Metrics.Basic
import Formalization.Statements.Sec1
import Formalization.Sweep.SweepASec1

/-!
# Section 1 Proof Wrappers (`Formalization.Statements.Sec1Proofs`)

Connects every `: Prop` entry in `Formalization.Statements.Sec1` (`SteinIntro.tex:347-557`) to its
library theorem in `Formalization.BerryEsseen`, `Formalization.Metrics`, and
`Formalization.Sweep.SweepASec1` (`AGENTS.md` Rule 5).
-/

namespace SteinMethod

/-- Theorem 1.1 (`\label{thm1}`, `SteinIntro.tex:351-357`) holds. -/
theorem Thm1_1_holds : Thm1_1 := by
  intro _ _ P _ _ _ x hn hXm hindep hident hX3 hmean hvar
  exact BerryEsseen.berry_esseen_iid P x hn hXm hindep hident hX3 hmean hvar

/-- Section 1.1.1 probability-metric axioms (`\label{probmet}`, eq. `(1.1)` `\label{23}`,
`SteinIntro.tex:502-522`) hold. -/
theorem Sec1_1_1_metrics_axioms_holds : Sec1_1_1_metrics_axioms :=
  sec1_1_1_metrics_axioms_proof

/-- Section 1.1.1 Item 1 Kolmogorov CDF representation and weak-convergence implication
(`\label{probmet}`, unlabeled item 1, `SteinIntro.tex:502-515`, `SteinIntro.tex:708-709`) hold. -/
theorem Sec1_1_1_kolmogorov_cdf_and_weakConv_holds : Sec1_1_1_kolmogorov_cdf_and_weakConv :=
  sec1_1_1_kolmogorov_cdf_and_weakConv_proof

/-- Proposition 1.2(1) (`\label{prop22}`, unlabeled item 1, `SteinIntro.tex:523-526`) holds. -/
theorem Prop1_2_1_holds : Prop1_2_1 := by
  intro _ _ _ _ P _ P' _ W Z _ _
  exact kolmogorovDist_map_le_tvDist_map P P' W Z

/-- Proposition 1.2(2) (`\label{prop22}`, unlabeled item 2, `SteinIntro.tex:523-524`,
`SteinIntro.tex:527-531`) holds. -/
theorem Prop1_2_2_holds : Prop1_2_2 := by
  intro _ _ _ _ P _ P' _ _ _ _ f _ _ hZ_dens hf
  exact kolmogorovDist_map_le_rpow_wassersteinDist_map P P' f hZ_dens hf

/-- Proposition 1.2(3) (`\label{prop22}`, unlabeled item 3, `SteinIntro.tex:523-524`,
`SteinIntro.tex:532-537`) holds. -/
theorem Prop1_2_3_holds : Prop1_2_3 := by
  intro _ _ _ _ _ _ _ _ P _ P' _ _ _ hW hZ
  exact tvDist_map_eq_half_tsum P P' hW hZ

end SteinMethod
