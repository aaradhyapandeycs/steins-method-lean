/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Statements.Sec5
import Formalization.Exponential.Basic
import Formalization.Exponential.SteinEquation
import Formalization.Exponential.MetricBounds
import Formalization.Exponential.Equilibrium
import Formalization.Exponential.GeometricExample
import Formalization.Exponential.GeometricSums
import Formalization.Exponential.GeometricSumsCounterexample
import Formalization.Exponential.Renyi
import Formalization.Exponential.Renewal
import Formalization.Exponential.Sec5Extras
import Formalization.Branching.Basic
import Formalization.Branching.Extinction
import Formalization.Branching.SizeBiasTree
import Formalization.Branching.YaglomRate
import Formalization.Sweep.SweepE1

/-!
# Section 5 Proof Wrappers (`Formalization.Statements.Sec5Proofs`)

Applies the library theorems in `Formalization.Exponential.*` and
`Formalization.Branching.*` to discharge each `: Prop` entry in `Formalization.Statements.Sec5`.
-/

namespace SteinMethod

theorem Lem5_1_1_holds : Lem5_1_1 :=
  fun P _ _ _ ↦ lem5_1_1_integrable P

theorem Lem5_1_2_holds : Lem5_1_2 :=
  fun P _ _ ↦ lem5_1_2 P

theorem Lem5_2_formula_holds : Lem5_2_formula :=
  lem5_2_formula

theorem Lem5_2_ode_contAt_holds : Lem5_2_ode_contAt :=
  fun hLoc hInt _ hcont ↦ lem5_2_ode_contAt hLoc hInt hcont

theorem Lem5_2_ode_ae_holds : Lem5_2_ode_ae :=
  ⟨fun hLoc hInt ↦ lem5_2_ode_ae hLoc hInt, fun hMeas hLe ↦ lem5_2_ode_ae_bdd hMeas hLe⟩

theorem Lem5_2_1_holds : Lem5_2_1 :=
  fun hMeas hNonneg hLe ↦ lem5_2_1 hMeas hNonneg hLe

theorem Lem5_2_2_holds : Lem5_2_2 :=
  fun hh hderiv ↦ lem5_2_2 hh hderiv

theorem Thm5_3_1_holds : Thm5_3_1 :=
  fun P _ P' _ _ _ ↦ thm5_3_1 P P'

theorem Thm5_3_2_holds : Thm5_3_2 :=
  fun P _ P' _ _ _ ↦ thm5_3_2 P P'

theorem Sec5_1_equilibrium_ac_holds : Sec5_1_equilibrium_ac :=
  fun P _ _ ↦ sec5_1_equilibrium_ac P

theorem Sec5_1_equilibrium_rhs_wellDefined_holds : Sec5_1_equilibrium_rhs_wellDefined :=
  fun P _ P' _ _ _ _ _ _ ↦ sec5_1_equilibrium_rhs_wellDefined P P'

theorem Thm5_4_holds : Thm5_4 :=
  fun P _ P' _ _ _ _ ↦ thm5_4 P P'

theorem Prop5_5_holds : Prop5_5 :=
  fun P _ P' _ _ _ _ ↦ prop5_5 P P'

theorem Rem5_3_holds : Rem5_3 :=
  fun P _ _ _ _ ↦ rem5_3 P

theorem Ex5_4_weak_conv_holds : Ex5_4_weak_conv :=
  fun P' _ _ _ _ P _ ↦ ex5_4_weak_conv P' P

theorem Ex5_4_ceil_corrected_holds : Ex5_4_ceil_corrected :=
  fun P _ _ _ ↦ ex5_4_ceil_corrected P

theorem Sec5_1_equilibrium_scale_restricted_holds : Sec5_1_equilibrium_scale_restricted :=
  fun P _ P' _ _ _ _ ↦ sec5_1_equilibrium_scale_restricted P P'

theorem Ex5_4_holds : Ex5_4 :=
  fun hp₀ hp₁ ↦ ex5_4 hp₀ hp₁

theorem Thm5_6_holds : Thm5_6 :=
  fun P₀ _ P' _ _ _ _ _ P _ _ ↦ thm5_6 P₀ P' P

theorem Sec5_2_eq5_6_holds : Sec5_2_eq5_6 := by
  intro _ _ P _ _ _ _ _ _
  exact sec5_2_eq5_6 P

theorem Thm5_7_corrected_holds : Thm5_7_corrected :=
  fun P _ P' _ _ _ _ _ _ _ ↦ thm5_7_corrected_minimal P P'

theorem Rem5_5_holds : Rem5_5 :=
  fun hp₀ hp₁ ↦ rem5_5 hp₀ hp₁

theorem Sec5_3_exists_isGaltonWatson_pos_var_holds :
    Sec5_3_exists_isGaltonWatson_pos_var :=
  sec5_3_exists_isGaltonWatson_pos_var

theorem Sec5_3_exists_isSizeBiasSpineCoupling_holds :
    Sec5_3_exists_isSizeBiasSpineCoupling := by
  intro _ _ P _ _ hGW hcrit hL2 n
  obtain ⟨Ω', mΩ', P', hP', X, L, R, R', U, hC, _⟩ :=
    sec5_3_exists_isSizeBiasSpineCoupling P hGW hcrit hL2 n
  exact ⟨Ω', mΩ', P', hP', X, L, R, R', U, hC⟩

theorem Sec5_3_extinction_holds : Sec5_3_extinction :=
  sec5_3_extinction

theorem Thm5_8_restricted_holds : Thm5_8_restricted :=
  thm5_8_restricted

theorem Thm5_9_restricted_holds : Thm5_9_restricted :=
  thm5_9_restricted

theorem Sec5_3_eq_1710_holds : Sec5_3_eq_1710 :=
  sec5_3_eq_1710

theorem Sec5_3_eq_1711_holds : Sec5_3_eq_1711 :=
  sec5_3_eq_1711

theorem Sec5_3_gwProb_sum_genSize_holds : Sec5_3_gwProb_sum_genSize :=
  sec5_3_gwProb_sum_genSize

theorem Sec5_3_gwSizeBiasProbV_sum_spine_holds : Sec5_3_gwSizeBiasProbV_sum_spine :=
  sec5_3_gwSizeBiasProbV_sum_spine

theorem Sec5_3_item_1_holds : Sec5_3_item_1 :=
  sec5_3_item_1

theorem Sec5_3_sizeBias_cond_pos_holds : Sec5_3_sizeBias_cond_pos :=
  sec5_3_sizeBias_cond_pos

theorem Sec5_3_item_2_holds : Sec5_3_item_2 :=
  sec5_3_item_2

theorem Sec5_3_item_3_holds : Sec5_3_item_3 :=
  sec5_3_item_3

theorem Sec5_3_item_4_holds : Sec5_3_item_4 :=
  sec5_3_item_4

theorem Sec5_3_eq_1712_holds : Sec5_3_eq_1712 :=
  sec5_3_eq_1712

theorem Sec5_3_not_indep_L_R_holds : Sec5_3_not_indep_L_R :=
  sec5_3_not_indep_L_R

theorem Sec5_3_spine_coupling_holds : Sec5_3_spine_coupling :=
  sec5_3_spine_coupling

theorem Sec5_3_eq_3143_corrected_holds : Sec5_3_eq_3143_corrected :=
  sec5_3_eq_3143_corrected

theorem Sec5_3_neg_corr_3158_and_3160_corrected_holds :
    Sec5_3_neg_corr_3158_and_3160_corrected :=
  sec5_3_neg_corr_3158_and_3160_corrected

theorem Sec5_3_step_i_holds : Sec5_3_step_i :=
  sec5_3_step_i

theorem Sec5_3_step_ii_holds : Sec5_3_step_ii :=
  sec5_3_step_ii

theorem Sec5_3_step_iii_holds : Sec5_3_step_iii :=
  sec5_3_step_iii

theorem Sec5_3_lpp_mean_diff_o_n_holds : Sec5_3_lpp_mean_diff_o_n :=
  sec5_3_lpp_mean_diff_o_n

theorem Sec5_3_kolmogorov_survival_restricted_holds :
    Sec5_3_kolmogorov_survival_restricted :=
  sec5_3_kolmogorov_survival_restricted

theorem Sec5_3_lpp_mean_diff_log_restricted_holds :
    Sec5_3_lpp_mean_diff_log_restricted :=
  sec5_3_lpp_mean_diff_log_restricted

theorem Sec5_3_scaled_Yn_mean_gt_one_witness_holds : Sec5_3_scaled_Yn_mean_gt_one_witness :=
  sec5_3_scaled_Yn_mean_gt_one_witness

end SteinMethod
