/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.BerryEsseen.BerryEsseen
import Formalization.Metrics.Basic
import Formalization.Statements.Sec1

/-!
# Section 1 Proofs (`Formalization.Statements.Sec1Proofs`)

Proof wrappers establishing `Thm1_1_holds`, `Prop1_2_1_holds`, `Prop1_2_2_holds`, and
`Prop1_2_3_holds` for Section 1 (`SteinIntro.tex:351-537`).
-/

namespace SteinMethod

/-- Proof of Theorem 1.1 (`\label{thm1}`, `SteinIntro.tex:351-357`). -/
theorem Thm1_1_holds : Thm1_1 := by
  intro _ _ P _ _ _ x hn hXm hindep hident hX3 hmean hvar
  exact BerryEsseen.berry_esseen_iid P x hn hXm hindep hident hX3 hmean hvar

/-- Proof of Proposition 1.2(1) (`\label{prop22}`, `SteinIntro.tex:523-526`). -/
theorem Prop1_2_1_holds : Prop1_2_1 := by
  intro _ _ _ _ P _ P' _ W Z _ _
  exact kolmogorovDist_map_le_tvDist_map P P' W Z

/-- Proof of Proposition 1.2(2) (`\label{prop22}`, `SteinIntro.tex:527-531`). -/
theorem Prop1_2_2_holds : Prop1_2_2 := by
  intro _ _ _ _ P _ P' _ _ _ _ f _ _ hZ_dens hf
  exact kolmogorovDist_map_le_rpow_wassersteinDist_map P P' f hZ_dens hf

/-- Proof of Proposition 1.2(3) (`\label{prop22}`, `SteinIntro.tex:532-537`). -/
theorem Prop1_2_3_holds : Prop1_2_3 := by
  intro _ _ _ _ _ _ _ _ P _ P' _ _ _ hW hZ
  exact tvDist_map_eq_half_tsum P P' hW hZ

end SteinMethod
