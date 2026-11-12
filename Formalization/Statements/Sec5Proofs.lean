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
import Formalization.Exponential.Rem56General
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

Connects every `: Prop` entry in `Formalization.Statements.Sec5` (`\label{exp}`,
`SteinIntro.tex:2712-3189`) to its library theorem in `Formalization.Exponential.*` and
`Formalization.Branching.*` (`AGENTS.md` Rule 5).
-/

namespace SteinMethod

/-- Lemma 5.1(1) (`\label{lem171}`, `SteinIntro.tex:2726-2733`) holds. -/
theorem Lem5_1_1_holds : Lem5_1_1 :=
  fun P _ _ _ ↦ lem5_1_1_integrable P

/-- Lemma 5.1(2) (`\label{lem171}`, `SteinIntro.tex:2726-2738`) holds. -/
theorem Lem5_1_2_holds : Lem5_1_2 :=
  fun P _ _ ↦ lem5_1_2 P

/-- Lemma 5.2 formula, boundary value, and continuous-$h$ ODE uniqueness (`\label{lem172}`,
eqs. `(5.1)`–`(5.2)` `\label{171}`–`\label{172}`, `SteinIntro.tex:2740-2745`,
`SteinIntro.tex:2774-2779`) hold. -/
theorem Lem5_2_formula_holds : Lem5_2_formula :=
  lem5_2_formula

/-- Lemma 5.2 pointwise ODE at continuity points (`\label{lem172}`, eq. `(5.1)` `\label{171}`,
`SteinIntro.tex:2740-2745`, `SteinIntro.tex:2774-2779`; `ISSUE-5.2-ODE`) holds. -/
theorem Lem5_2_ode_contAt_holds : Lem5_2_ode_contAt :=
  fun hLoc hInt _ hcont ↦ lem5_2_ode_contAt hLoc hInt hcont

/-- Lemma 5.2 local absolute continuity, a.e. ODE, and a.e. uniqueness (`\label{lem172}`, eqs.
`(5.1)`–`(5.2)` `\label{171}`–`\label{172}`, `SteinIntro.tex:2740-2745`,
`SteinIntro.tex:2774-2779`; `ISSUE-5.2-ODE`) hold. -/
theorem Lem5_2_ode_ae_holds : Lem5_2_ode_ae :=
  ⟨fun hLoc hInt ↦ lem5_2_ode_ae hLoc hInt, fun hMeas hLe ↦ lem5_2_ode_ae_bdd hMeas hLe⟩

/-- Lemma 5.2(1) (`\label{lem172}` item 1 `\label{i171}`, `SteinIntro.tex:2747-2750`,
`SteinIntro.tex:2740`, `SteinIntro.tex:2781-2789`) holds. -/
theorem Lem5_2_1_holds : Lem5_2_1 :=
  fun hMeas hNonneg hLe ↦ lem5_2_1 hMeas hNonneg hLe

/-- Lemma 5.2(2) (`\label{lem172}` item 2 `\label{i172}`, `SteinIntro.tex:2751-2754`,
`SteinIntro.tex:2740`, `SteinIntro.tex:2790-2796`; `ISSUE-5.2-PROOF`) holds. -/
theorem Lem5_2_2_holds : Lem5_2_2 :=
  fun hh hderiv ↦ lem5_2_2 hh hderiv

/-- Theorem 5.3(1) (`\label{thm171}`, `SteinIntro.tex:2758-2766`) holds. -/
theorem Thm5_3_1_holds : Thm5_3_1 :=
  fun P _ P' _ _ _ ↦ thm5_3_1 P P'

/-- Theorem 5.3(2) (`\label{thm171}`, `SteinIntro.tex:2758-2760`, `SteinIntro.tex:2767-2773`)
holds. -/
theorem Thm5_3_2_holds : Thm5_3_2 :=
  fun P _ P' _ _ _ ↦ thm5_3_2 P P'

/-- Section 5.1 equilibrium uniqueness and Lebesgue absolute continuity (unlabeled prose,
`SteinIntro.tex:2844-2845`; `ISSUE-5.5`) hold. -/
theorem Sec5_1_equilibrium_ac_holds : Sec5_1_equilibrium_ac :=
  fun P _ _ ↦ sec5_1_equilibrium_ac P

/-- Section 5.1 well-definedness of $\mathbb{E}[f'(W^e)]$ in `(5.3)` (`\label{173}`,
`SteinIntro.tex:2844-2845`, `SteinIntro.tex:2840`; `ISSUE-5.5`) holds. -/
theorem Sec5_1_equilibrium_rhs_wellDefined_holds : Sec5_1_equilibrium_rhs_wellDefined :=
  fun P _ P' _ _ _ _ _ _ ↦ sec5_1_equilibrium_rhs_wellDefined P P'

/-- Theorem 5.4 (`\label{thm172}`, `SteinIntro.tex:2847-2853`) holds. -/
theorem Thm5_4_holds : Thm5_4 :=
  fun P _ P' _ _ _ _ ↦ thm5_4 P P'

/-- Proposition 5.5 (`\label{prop171}`, `SteinIntro.tex:2863-2867`) holds. -/
theorem Prop5_5_holds : Prop5_5 :=
  fun P _ P' _ _ _ _ ↦ prop5_5 P P'

/-- Remark 5.3 (`\label{rem171}`, `SteinIntro.tex:2875-2880`) holds. -/
theorem Rem5_3_holds : Rem5_3 :=
  fun P _ _ _ _ ↦ rem5_3 P

/-- Example 5.4 weak convergence prose claim (`\label{ex171}`, `SteinIntro.tex:2885`,
`SteinIntro.tex:2883`) holds. -/
theorem Ex5_4_weak_conv_holds : Ex5_4_weak_conv :=
  fun P' _ _ _ _ P _ ↦ ex5_4_weak_conv P' P

/-- Example 5.4 corrected ceiling prose claim (`\label{ex171}`, `SteinIntro.tex:2885-2886`,
`SteinIntro.tex:2883`; `ISSUE-TYPO-5.4`) holds. -/
theorem Ex5_4_ceil_corrected_holds : Ex5_4_ceil_corrected :=
  fun P _ _ _ ↦ ex5_4_ceil_corrected P

/-- Example 5.4 equilibrium scaling identity, restricted to $c > 0$ (`\label{ex171}`,
`SteinIntro.tex:2894`, `SteinIntro.tex:2883`; `ISSUE-5.4`) holds. -/
theorem Sec5_1_equilibrium_scale_restricted_holds : Sec5_1_equilibrium_scale_restricted :=
  fun P _ P' _ _ _ _ ↦ sec5_1_equilibrium_scale_restricted P P'

/-- Example 5.4 (`\label{ex171}`, `SteinIntro.tex:2883-2900`) holds. -/
theorem Ex5_4_holds : Ex5_4 :=
  fun hp₀ hp₁ ↦ ex5_4 hp₀ hp₁

/-- Theorem 5.6 (Rényi's Theorem, unlabeled `theorem`, `SteinIntro.tex:2905-2911`) holds. -/
theorem Thm5_6_holds : Thm5_6 :=
  fun P₀ _ P' _ _ _ _ _ P _ _ ↦ thm5_6 P₀ P' P

/-- Section 5.2 equation `(5.6)` equilibrium coupling (`\label{179}`,
`SteinIntro.tex:2953-2957`) holds. -/
theorem Sec5_2_eq5_6_holds : Sec5_2_eq5_6 := by
  intro _ _ P _ _ _ _ _ _
  exact sec5_2_eq5_6 P

/-- Theorem 5.7, corrected (`\label{thm1710}`, eqs. `(5.4)`–`(5.5)`
`\label{177}`–`\label{178}`, `SteinIntro.tex:2915-2929`; `ISSUE-5.7`) holds. -/
theorem Thm5_7_corrected_holds : Thm5_7_corrected :=
  fun P _ P' _ _ _ _ _ _ _ ↦ thm5_7_corrected_minimal P P'

/-- Remark 5.5 (unlabeled `remark`, `SteinIntro.tex:2931-2947`) holds. -/
theorem Rem5_5_holds : Rem5_5 :=
  fun hp₀ hp₁ ↦ rem5_5 hp₀ hp₁

/-- Remark 5.6, generalization (unlabeled `remark`, `SteinIntro.tex:2948-2951`) holds. -/
theorem Rem5_6_generalization_holds : Rem5_6_generalization :=
  ⟨fun P _ P' _ ↦ rem5_6_part1 P P',
    ⟨fun P _ ↦ rem5_6_part2a P, fun P _ ↦ rem5_6_part2b P,
      fun P _ P' _ ↦ rem5_6_part2c P P'⟩,
    rem5_6_part3⟩

/-- Section 5.3 existence of a non-degenerate critical Galton–Watson process with $\sigma^2 >
0$ (unlabeled prose, `SteinIntro.tex:2993-2997`, `SteinIntro.tex:3007-3020`) holds. -/
theorem Sec5_3_exists_isGaltonWatson_pos_var_holds :
    Sec5_3_exists_isGaltonWatson_pos_var :=
  sec5_3_exists_isGaltonWatson_pos_var

/-- Section 5.3 existence of the Lyons–Pemantle–Peres size-bias spine coupling (unlabeled
prose, `SteinIntro.tex:3030-3044`, `SteinIntro.tex:3065-3067`, `SteinIntro.tex:3117-3138`,
`SteinIntro.tex:3167-3168`) holds. -/
theorem Sec5_3_exists_isSizeBiasSpineCoupling_holds :
    Sec5_3_exists_isSizeBiasSpineCoupling := by
  intro _ _ P _ _ hGW hcrit hL2 n
  obtain ⟨Ω', mΩ', P', hP', X, L, R, R', U, hC, _⟩ :=
    sec5_3_exists_isSizeBiasSpineCoupling P hGW hcrit hL2 n
  exact ⟨Ω', mΩ', P', hP', X, L, R, R', U, hC⟩

/-- Section 5.3 Galton–Watson extinction dichotomy (unlabeled prose,
`SteinIntro.tex:3003-3004`; `ISSUE-TYPO-5.3a`) holds. -/
theorem Sec5_3_extinction_holds : Sec5_3_extinction :=
  sec5_3_extinction

/-- Theorem 5.8 (Yaglom's Theorem), restricted to $\sigma^2 > 0$ (unlabeled `theorem`,
`SteinIntro.tex:3007-3013`; `ISSUE-5.8`) holds. -/
theorem Thm5_8_restricted_holds : Thm5_8_restricted :=
  thm5_8_restricted

/-- Theorem 5.9, restricted to $\sigma^2 > 0$ and $n \ge 2$ (unlabeled `theorem`,
`SteinIntro.tex:3015-3020`; `ISSUE-5.8`, `ISSUE-5.9`) holds. -/
theorem Thm5_9_restricted_holds : Thm5_9_restricted :=
  thm5_9_restricted

/-- Section 5.3 Equation `(5.7)` (`\label{1710}`, `SteinIntro.tex:3054-3056`,
`SteinIntro.tex:3085-3098`; `ISSUE-TYPO-5.3b`) holds. -/
theorem Sec5_3_eq_1710_holds : Sec5_3_eq_1710 :=
  sec5_3_eq_1710

/-- Section 5.3 Equation `(5.8)` (`\label{1711}`, `SteinIntro.tex:3070-3072`) holds. -/
theorem Sec5_3_eq_1711_holds : Sec5_3_eq_1711 :=
  sec5_3_eq_1711

/-- Section 5.3 tree-probability link to the Galton–Watson generation-size law (unlabeled
prose, `SteinIntro.tex:3047-3048`, `SteinIntro.tex:3074-3076`) holds. -/
theorem Sec5_3_gwProb_sum_genSize_holds : Sec5_3_gwProb_sum_genSize :=
  sec5_3_gwProb_sum_genSize

/-- Section 5.3 size-bias tree-probability link to the spine joint law (unlabeled prose,
`SteinIntro.tex:3047-3056`, `SteinIntro.tex:3070-3079`, `SteinIntro.tex:3100-3101`) holds. -/
theorem Sec5_3_gwSizeBiasProbV_sum_spine_holds : Sec5_3_gwSizeBiasProbV_sum_spine :=
  sec5_3_gwSizeBiasProbV_sum_spine

/-- Section 5.3 Item (1) (`\label{i171a}`, `SteinIntro.tex:3061`, `SteinIntro.tex:3069-3076`)
holds. -/
theorem Sec5_3_item_1_holds : Sec5_3_item_1 :=
  sec5_3_item_1

/-- Section 5.3 positive-conditioning size-bias invariance (unlabeled prose,
`SteinIntro.tex:3076-3078`) holds. -/
theorem Sec5_3_sizeBias_cond_pos_holds : Sec5_3_sizeBias_cond_pos :=
  sec5_3_sizeBias_cond_pos

/-- Section 5.3 Item (2) (`\label{i172a}`, `SteinIntro.tex:3062-3063`,
`SteinIntro.tex:3076-3078`) holds. -/
theorem Sec5_3_item_2_holds : Sec5_3_item_2 :=
  sec5_3_item_2

/-- Section 5.3 Item (3) (`\label{i173}`, `SteinIntro.tex:3064`, `SteinIntro.tex:3078-3079`)
holds. -/
theorem Sec5_3_item_3_holds : Sec5_3_item_3 :=
  sec5_3_item_3

/-- Section 5.3 Item (4) (`\label{i174}`, `SteinIntro.tex:3065-3067`,
`SteinIntro.tex:3079-3082`) holds. -/
theorem Sec5_3_item_4_holds : Sec5_3_item_4 :=
  sec5_3_item_4

/-- Section 5.3 Equation `(5.9)` (`\label{1712}`, `SteinIntro.tex:3100-3113`) holds. -/
theorem Sec5_3_eq_1712_holds : Sec5_3_eq_1712 :=
  sec5_3_eq_1712

/-- Section 5.3 non-independence of $L_{n,j}$ and $R_{n,j}$ (unlabeled prose,
`SteinIntro.tex:3119-3126`) holds. -/
theorem Sec5_3_not_indep_L_R_holds : Sec5_3_not_indep_L_R :=
  sec5_3_not_indep_L_R

/-- Section 5.3 spine realization of $Y_n$ (unlabeled prose, `SteinIntro.tex:3128-3139`) holds. -/
theorem Sec5_3_spine_coupling_holds : Sec5_3_spine_coupling :=
  sec5_3_spine_coupling

/-- Section 5.3 corrected coupling difference and triangle inequality (unlabeled display,
`SteinIntro.tex:3142-3145`; `ISSUE-TYPO-5.3c`) hold. -/
theorem Sec5_3_eq_3143_corrected_holds : Sec5_3_eq_3143_corrected :=
  sec5_3_eq_3143_corrected

/-- Section 5.3 negative correlation and corrected conditional expectation chain (unlabeled
display, `SteinIntro.tex:3158-3164`; `ISSUE-5.9-PROOF`) hold. -/
theorem Sec5_3_neg_corr_3158_and_3160_corrected_holds :
    Sec5_3_neg_corr_3158_and_3160_corrected :=
  sec5_3_neg_corr_3158_and_3160_corrected

/-- Section 5.3 spine step bound `(i)` (unlabeled display, `SteinIntro.tex:3148`,
`SteinIntro.tex:3154-3164`; `ISSUE-5.9-PROOF`) holds. -/
theorem Sec5_3_step_i_holds : Sec5_3_step_i :=
  sec5_3_step_i

/-- Section 5.3 spine step bound `(ii)` (unlabeled display, `SteinIntro.tex:3149-3150`,
`SteinIntro.tex:3166-3177`; `ISSUE-5.9-PROOF`) holds. -/
theorem Sec5_3_step_ii_holds : Sec5_3_step_ii :=
  sec5_3_step_ii

/-- Section 5.3 spine step bound `(iii)` (unlabeled display, `SteinIntro.tex:3151`,
`SteinIntro.tex:3179-3187`) holds. -/
theorem Sec5_3_step_iii_holds : Sec5_3_step_iii :=
  sec5_3_step_iii

/-- Section 5.3 Lyons–Pemantle–Peres $o(n)$ coupling discrepancy (unlabeled prose,
`SteinIntro.tex:3027`) holds. -/
theorem Sec5_3_lpp_mean_diff_o_n_holds : Sec5_3_lpp_mean_diff_o_n :=
  sec5_3_lpp_mean_diff_o_n

/-- Section 5.3 Kolmogorov survival asymptotic, restricted to $\sigma^2 > 0$ (unlabeled prose,
`SteinIntro.tex:3028`, `SteinIntro.tex:3185-3186`; `ISSUE-5.8`) holds. -/
theorem Sec5_3_kolmogorov_survival_restricted_holds :
    Sec5_3_kolmogorov_survival_restricted :=
  sec5_3_kolmogorov_survival_restricted

/-- Section 5.3 logarithmic coupling discrepancy bound, restricted to $n \ge 2$ (unlabeled
prose, `SteinIntro.tex:3022-3023`, `SteinIntro.tex:3140-3145`; `ISSUE-5.9`) holds. -/
theorem Sec5_3_lpp_mean_diff_log_restricted_holds :
    Sec5_3_lpp_mean_diff_log_restricted :=
  sec5_3_lpp_mean_diff_log_restricted

/-- Section 5.3 proof opening non-unit-mean witness (unlabeled proof note,
`SteinIntro.tex:3023-3024`; `ISSUE-5.9-PROOF-MEAN`) holds. -/
theorem Sec5_3_scaled_Yn_mean_gt_one_witness_holds : Sec5_3_scaled_Yn_mean_gt_one_witness :=
  sec5_3_scaled_Yn_mean_gt_one_witness

end SteinMethod
