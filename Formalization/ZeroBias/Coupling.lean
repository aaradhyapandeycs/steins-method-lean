/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.ZeroBias.Density
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Zero-Bias Coupling Construction for Sums (`Formalization.ZeroBias.Coupling`)

Proves Proposition 3.21 (`\label{prop81}`, `SteinIntro.tex:1530-1551`; display typo
`ISSUE-TYPO-3.21` at `L1546-1547`): for independent mean-zero $L^2$ summands $X_1, \dots, X_n$ with
$\sum_{i=1}^n \operatorname{Var}(X_i) = 1$, replacing a variance-weighted random summand $X_I$ by a
zero-bias version $X_I^z$ independent of $(X_j)_{j \ne I}$ yields a zero-bias version
$W^z = \sum_{j \ne I} X_j + X_I^z$ of $W = \sum_{i=1}^n X_i$.

To respect the dual-integrability convention `D9` (`ISSUE-3.10`) without imposing per-summand
integrability of $X_i f(W)$ for arbitrary locally absolutely continuous $f$, we first verify the
zero-bias expectation identity on sublinear $C^1$ functions with bounded derivative and then
transfer to the full `D9` class via `isZeroBias_and_map_eq_of_c1_sublinear` (Proposition 3.19(3),
since $\operatorname{Var}(W) = \sum_i \sigma_i^2 = 1 > 0$).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

section Helpers

private lemma zeroBias_coord_c1_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S U Uz : Ω → ℝ} {F : ℝ → ℝ} {B : ℝ}
    (hS_meas : Measurable S) (hU_meas : Measurable U) (hUz_meas : Measurable Uz)
    (hS_L2 : MemLp S 2 P) (hU_L2 : MemLp U 2 P)
    (hSU_indep : IndepFun S U P) (hSUz_indep : IndepFun S Uz P)
    (hUz_zb : IsZeroBias P U P Uz)
    (hF_cd : ContDiff ℝ 1 F) (hF_sub : ∀ w : ℝ, |F w| ≤ |w|)
    (hB : ∀ w : ℝ, |deriv F w| ≤ B) :
    ∫ ω, U ω * F (S ω + U ω) ∂P =
      ProbabilityTheory.variance U P * ∫ ω, deriv F (S ω + Uz ω) ∂P := by
  have hF_diff : Differentiable ℝ F := (contDiff_one_iff_deriv.mp hF_cd).1
  have hdf_cont : Continuous (deriv F) := (contDiff_one_iff_deriv.mp hF_cd).2
  set μS : Measure ℝ := P.map S
  set μU : Measure ℝ := P.map U
  set μUz : Measure ℝ := P.map Uz
  have : IsProbabilityMeasure μS := inferInstanceAs (IsProbabilityMeasure (P.map S))
  have : IsProbabilityMeasure μU := inferInstanceAs (IsProbabilityMeasure (P.map U))
  have : IsProbabilityMeasure μUz := inferInstanceAs (IsProbabilityMeasure (P.map Uz))
  have hprod_U : P.map (fun ω ↦ (S ω, U ω)) = μS.prod μU :=
    hSU_indep.map_prod_eq_prod_map_map hS_meas.aemeasurable hU_meas.aemeasurable
  have hprod_Uz : P.map (fun ω ↦ (S ω, Uz ω)) = μS.prod μUz :=
    hSUz_indep.map_prod_eq_prod_map_map hS_meas.aemeasurable hUz_meas.aemeasurable
  let K₁ : ℝ × ℝ → ℝ := fun p ↦ p.2 * F (p.1 + p.2)
  have hK₁_cont : Continuous K₁ :=
    continuous_snd.mul (hF_cd.continuous.comp (continuous_fst.add continuous_snd))
  have hW_L2 : MemLp (fun ω ↦ S ω + U ω) 2 P := hS_L2.add hU_L2
  have hUF_int : Integrable (fun ω ↦ U ω * F (S ω + U ω)) P := by
    refine (hU_L2.integrable_sq.add hW_L2.integrable_sq).mono'
      (hU_meas.mul (hF_cd.continuous.measurable.comp (hS_meas.add hU_meas))).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |U ω| * |F (S ω + U ω)| ≤ |U ω| * |S ω + U ω| :=
      mul_le_mul_of_nonneg_left (hF_sub (S ω + U ω)) (abs_nonneg (U ω))
    have h2 : |U ω| * |S ω + U ω| ≤ U ω ^ 2 + (S ω + U ω) ^ 2 := by
      nlinarith [sq_nonneg (|U ω| - |S ω + U ω|), sq_abs (U ω), sq_abs (S ω + U ω)]
    exact h1.trans h2
  have hK₁_int : Integrable K₁ (μS.prod μU) := by
    rw [← hprod_U]
    exact (integrable_map_measure hK₁_cont.aestronglyMeasurable
      (hS_meas.prodMk hU_meas).aemeasurable).mpr hUF_int
  let K₂ : ℝ × ℝ → ℝ := fun p ↦ deriv F (p.1 + p.2)
  have hK₂_cont : Continuous K₂ := hdf_cont.comp (continuous_fst.add continuous_snd)
  have hK₂_int : Integrable K₂ (μS.prod μUz) :=
    Integrable.of_bound hK₂_cont.aestronglyMeasurable B
      (ae_of_all _ fun p ↦ by rw [Real.norm_eq_abs]; exact hB (p.1 + p.2))
  have hslice : ∀ s : ℝ,
      ∫ u, u * F (s + u) ∂μU =
        ProbabilityTheory.variance U P * ∫ z, deriv F (s + z) ∂μUz := fun s ↦ by
    let g : ℝ → ℝ := fun u ↦ F (s + u)
    have hg_hd : ∀ u : ℝ, HasDerivAt g (deriv F (s + u)) u := fun u ↦ by
      have hd : HasDerivAt g (deriv F (s + u) * 1) u :=
        HasDerivAt.comp u (hF_diff (s + u)).hasDerivAt ((hasDerivAt_id' u).const_add s)
      rwa [mul_one] at hd
    have hg_deriv : deriv g = fun u ↦ deriv F (s + u) := funext fun u ↦ (hg_hd u).deriv
    have hg_cd : ContDiff ℝ 1 g := contDiff_one_iff_deriv.mpr
      ⟨fun u ↦ (hg_hd u).differentiableAt,
        hg_deriv ▸ hdf_cont.comp (continuous_const.add continuous_id)⟩
    have hg_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b := fun a b ↦
      hg_cd.contDiffOn.absolutelyContinuousOnInterval
    have hU_int : Integrable U P := hU_L2.integrable one_le_two
    have hUg_int : Integrable (fun ω ↦ U ω * g (U ω)) P := by
      refine ((hU_int.norm.const_mul |s|).add hU_L2.integrable_sq).mono'
        (hU_meas.mul (hg_cd.continuous.measurable.comp hU_meas)).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      dsimp only [Pi.add_apply, g]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have hsub := (hF_sub (s + U ω)).trans (abs_add_le s (U ω))
      have hmul := mul_le_mul_of_nonneg_left hsub (abs_nonneg (U ω))
      nlinarith [sq_abs (U ω)]
    have hUzg_int : Integrable (fun ω ↦ deriv g (Uz ω)) P := by
      rw [hg_deriv]
      exact Integrable.of_bound
        (hdf_cont.measurable.comp (measurable_const.add hUz_meas)).aestronglyMeasurable B
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hB (s + Uz ω))
    have hzb := hUz_zb.2.2.2 g hg_ac hUg_int hUzg_int
    rw [hg_deriv] at hzb
    have h1 : ∫ u, u * F (s + u) ∂μU = ∫ ω, U ω * F (s + U ω) ∂P :=
      integral_map hU_meas.aemeasurable
        (measurable_id.mul (hg_cd.continuous.measurable)).aestronglyMeasurable
    have h2 : ∫ z, deriv F (s + z) ∂μUz = ∫ ω, deriv F (s + Uz ω) ∂P :=
      integral_map hUz_meas.aemeasurable
        (hdf_cont.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    rw [h1, h2]
    exact hzb
  calc
    ∫ ω, U ω * F (S ω + U ω) ∂P
      = ∫ p, K₁ p ∂(P.map (fun ω ↦ (S ω, U ω))) :=
        (integral_map (hS_meas.prodMk hU_meas).aemeasurable hK₁_cont.aestronglyMeasurable).symm
    _ = ∫ p, K₁ p ∂(μS.prod μU) := by rw [hprod_U]
    _ = ∫ s, (∫ u, u * F (s + u) ∂μU) ∂μS := integral_prod K₁ hK₁_int
    _ = ∫ s, (ProbabilityTheory.variance U P * ∫ z, deriv F (s + z) ∂μUz) ∂μS := by
        simp_rw [hslice]
    _ = ProbabilityTheory.variance U P * ∫ s, (∫ z, deriv F (s + z) ∂μUz) ∂μS :=
        integral_const_mul _ _
    _ = ProbabilityTheory.variance U P * ∫ p, K₂ p ∂(μS.prod μUz) := by
        rw [integral_prod K₂ hK₂_int]
    _ = ProbabilityTheory.variance U P * ∫ p, K₂ p ∂(P.map (fun ω ↦ (S ω, Uz ω))) := by
        rw [hprod_Uz]
    _ = ProbabilityTheory.variance U P * ∫ ω, deriv F (S ω + Uz ω) ∂P := by
        rw [integral_map (hS_meas.prodMk hUz_meas).aemeasurable hK₂_cont.aestronglyMeasurable]

end Helpers

/-- **Proposition 3.21** (`\label{prop81}`, `SteinIntro.tex:1530-1551`; display typo
`ISSUE-TYPO-3.21`): if $X_1, \dots, X_n$ are independent mean-zero $L^2$ random variables with
$\sum_{i=1}^n \operatorname{Var}(X_i) = 1$, each $X_i^z$ has the zero-bias distribution of $X_i$
and is independent of $(X_j)_{j \ne i}$ (assuming less than printed Item 1 at `L1533-1534`, which
also mentions independence from $(X_j^z)_{j \ne i}$), and $I$ satisfies
$\mathbb{P}(I = i) = \operatorname{Var}(X_i)$ independently of $((X_i)_i, (X_i^z)_i)$, then
$W^z = \sum_{j \ne I} X_j + X_I^z$ has the zero-bias distribution of $W = \sum_{i=1}^n X_i$. -/
theorem zeroBias_sum_of_iIndepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xz : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hXz_meas : ∀ i : Fin n, Measurable (Xz i))
    (hX_indep : ProbabilityTheory.iIndepFun X P)
    (hX_L2 : ∀ i : Fin n, MemLp (X i) 2 P)
    (hX_mean : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hVar_sum : (∑ i : Fin n, ProbabilityTheory.variance (X i) P) = 1)
    (hXz : ∀ i : Fin n, IsZeroBias P (X i) P (Xz i))
    (hXz_indep : ∀ i : Fin n,
      ProbabilityTheory.IndepFun (Xz i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) P)
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin n, P.real (I ⁻¹' {i}) = ProbabilityTheory.variance (X i) P)
    (hI_indep : ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xz i ω)) P) :
    IsZeroBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j ∈ Finset.univ.erase (I ω), X j ω) + Xz (I ω) ω) := by
  let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
  let S_not : Fin n → Ω → ℝ := fun i ω ↦ ∑ j ∈ Finset.univ.erase i, X j ω
  let Wz : Ω → ℝ := fun ω ↦ S_not (I ω) ω + Xz (I ω) ω
  have hW_L2 : MemLp W 2 P := memLp_finsetSum Finset.univ fun i _ ↦ hX_L2 i
  have hW_mean : ∫ ω, W ω ∂P = 0 := by
    dsimp [W]
    rw [integral_finsetSum Finset.univ fun i _ ↦ (hX_L2 i).integrable one_le_two]
    simp [hX_mean]
  have hW_var : ProbabilityTheory.variance W P = 1 := by
    have hW_fn : W = ∑ i ∈ Finset.univ, X i := by ext ω; simp [W]
    rw [hW_fn, IndepFun.variance_sum (fun i _ ↦ hX_L2 i)
      (fun i _ j _ hij ↦ hX_indep.indepFun hij), hVar_sum]
  have hS_meas : ∀ i : Fin n, Measurable (S_not i) := fun i ↦
    Finset.measurable_fun_sum _ fun j _ ↦ hX_meas j
  have hWz_meas : Measurable Wz := by
    have heq : Wz = fun ω ↦
        ∑ i : Fin n, (I ⁻¹' {i}).indicator (fun ω' ↦ S_not i ω' + Xz i ω') ω := by
      ext ω
      symm
      rw [Finset.sum_eq_single (I ω)]
      · simp [Wz]
      · intro i _ hi
        have hnot : ω ∉ I ⁻¹' {i} := fun h ↦ hi h.symm
        simp [hnot]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    rw [heq]
    exact Finset.measurable_fun_sum Finset.univ fun i _ ↦
      ((hS_meas i).add (hXz_meas i)).indicator (hI_meas (measurableSet_singleton i))
  refine (isZeroBias_and_map_eq_of_c1_sublinear P P hW_L2 hW_mean
    (by rw [hW_var]; exact zero_lt_one) hWz_meas.aemeasurable ?_).2
  intro F hF_cd hF_sub ⟨B, hB⟩
  have hdf_cont : Continuous (deriv F) := (contDiff_one_iff_deriv.mp hF_cd).2
  rw [hW_var, one_mul]
  have hcoord : ∀ i : Fin n,
      ∫ ω, X i ω * F (W ω) ∂P =
        ProbabilityTheory.variance (X i) P * ∫ ω, deriv F (S_not i ω + Xz i ω) ∂P ∧
        Integrable (fun ω ↦ X i ω * F (W ω)) P := fun i ↦ by
    have hW_split : W = fun ω ↦ S_not i ω + X i ω := by
      ext ω
      dsimp [W, S_not]
      exact (Finset.sum_erase_add Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)).symm
    have hS_L2 : MemLp (S_not i) 2 P :=
      memLp_finsetSum (Finset.univ.erase i) fun j _ ↦ hX_L2 j
    have hSU_indep : IndepFun (S_not i) (X i) P := by
      have hfn : S_not i = ∑ j ∈ Finset.univ.erase i, X j := by ext ω; simp [S_not]
      rw [hfn]
      exact hX_indep.indepFun_finsetSum_of_notMem hX_meas (Finset.notMem_erase i Finset.univ)
    have hSUz_indep : IndepFun (S_not i) (Xz i) P := by
      let φ : ({j : Fin n // j ≠ i} → ℝ) → ℝ := fun v ↦ ∑ j, v j
      have hφ_meas : Measurable φ :=
        Finset.measurable_fun_sum Finset.univ fun j _ ↦ measurable_pi_apply j
      have hcomp : S_not i = φ ∘ (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) := by
        ext ω
        dsimp [S_not, φ]
        exact Finset.sum_subtype (Finset.univ.erase i) (by simp) (fun j ↦ X j ω)
      rw [hcomp]
      exact ((hXz_indep i).comp measurable_id hφ_meas).symm
    have hUF_int : Integrable (fun ω ↦ X i ω * F (W ω)) P := by
      refine ((hX_L2 i).integrable_sq.add hW_L2.integrable_sq).mono'
        ((hX_meas i).mul (hF_cd.continuous.measurable.comp
          (Finset.measurable_fun_sum Finset.univ fun k _ ↦ hX_meas k))).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |X i ω| * |F (W ω)| ≤ |X i ω| * |W ω| :=
        mul_le_mul_of_nonneg_left (hF_sub (W ω)) (abs_nonneg (X i ω))
      have h2 : |X i ω| * |W ω| ≤ X i ω ^ 2 + W ω ^ 2 := by
        nlinarith [sq_nonneg (|X i ω| - |W ω|), sq_abs (X i ω), sq_abs (W ω)]
      exact h1.trans h2
    refine ⟨?_, hUF_int⟩
    rw [hW_split]
    exact zeroBias_coord_c1_expectation P (hS_meas i) (hX_meas i) (hXz_meas i) hS_L2 (hX_L2 i)
      hSU_indep hSUz_indep (hXz i) hF_cd hF_sub hB
  have hLHS : ∫ ω, W ω * F (W ω) ∂P =
      ∑ i : Fin n, ProbabilityTheory.variance (X i) P * ∫ ω, deriv F (S_not i ω + Xz i ω) ∂P := by
    have hsum_fn : (fun ω ↦ W ω * F (W ω)) =
        fun ω ↦ ∑ i : Fin n, X i ω * F (W ω) := by
      ext ω; dsimp [W]; rw [Finset.sum_mul]
    rw [hsum_fn, integral_finsetSum Finset.univ fun i _ ↦ (hcoord i).2]
    exact Finset.sum_congr rfl fun i _ ↦ (hcoord i).1
  have hRHS_term : ∀ i : Fin n,
      Integrable (fun ω ↦ (I ⁻¹' {i}).indicator 1 ω * deriv F (S_not i ω + Xz i ω)) P ∧
        ∫ ω, (I ⁻¹' {i}).indicator 1 ω * deriv F (S_not i ω + Xz i ω) ∂P =
          ProbabilityTheory.variance (X i) P * ∫ ω, deriv F (S_not i ω + Xz i ω) ∂P := fun i ↦ by
    let ind_i : Fin n → ℝ := ({i} : Set (Fin n)).indicator 1
    let ψ_i : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
      fun p ↦ deriv F ((∑ j ∈ Finset.univ.erase i, p.1 j) + p.2 i)
    have hind_meas : Measurable ind_i := measurable_one.indicator (measurableSet_singleton i)
    have hψ_meas : Measurable ψ_i :=
      hdf_cont.measurable.comp
        ((Finset.measurable_fun_sum _ fun j _ ↦
          (measurable_pi_apply j).comp measurable_fst).add
          ((measurable_pi_apply i).comp measurable_snd))
    have hindep_i : IndepFun (ind_i ∘ I)
        (ψ_i ∘ fun ω ↦ (fun j ↦ X j ω, fun j ↦ Xz j ω)) P :=
      hI_indep.comp hind_meas hψ_meas
    have heq_ind : ind_i ∘ I = (I ⁻¹' {i}).indicator (1 : Ω → ℝ) := by
      ext ω; by_cases hω : I ω = i <;> simp [ind_i, hω]
    have heq_ψ : (ψ_i ∘ fun ω ↦ (fun j ↦ X j ω, fun j ↦ Xz j ω)) =
        fun ω ↦ deriv F (S_not i ω + Xz i ω) := rfl
    rw [heq_ind, heq_ψ] at hindep_i
    have h1_int : Integrable ((I ⁻¹' {i}).indicator (1 : Ω → ℝ)) P :=
      (integrable_const (1 : ℝ)).indicator (hI_meas (measurableSet_singleton i))
    have h2_int : Integrable (fun ω ↦ deriv F (S_not i ω + Xz i ω)) P :=
      Integrable.of_bound
        (hdf_cont.measurable.comp ((hS_meas i).add (hXz_meas i))).aestronglyMeasurable B
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hB (S_not i ω + Xz i ω))
    have hprod_int : Integrable
        (fun ω ↦ (I ⁻¹' {i}).indicator 1 ω * deriv F (S_not i ω + Xz i ω)) P := by
      refine (integrable_const |B|).mono'
        (h1_int.aestronglyMeasurable.mul h2_int.aestronglyMeasurable)
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hω : ω ∈ I ⁻¹' {i}
      · rw [indicator_of_mem hω, Pi.one_apply, abs_one, one_mul]
        exact (hB _).trans (le_abs_self B)
      · rw [indicator_of_notMem hω, abs_zero, zero_mul]
        exact abs_nonneg B
    refine ⟨hprod_int, ?_⟩
    rw [hindep_i.integral_fun_mul_eq_mul_integral h1_int.aestronglyMeasurable
      h2_int.aestronglyMeasurable,
      integral_indicator_one (hI_meas (measurableSet_singleton i)), hI_prob i]
  have hWz_sum : (fun ω ↦ deriv F (Wz ω)) =
      fun ω ↦ ∑ i : Fin n, (I ⁻¹' {i}).indicator 1 ω * deriv F (S_not i ω + Xz i ω) := by
    ext ω
    symm
    rw [Finset.sum_eq_single (I ω)]
    · simp [Wz]
    · intro i _ hi
      have hnot : ω ∉ I ⁻¹' {i} := fun h ↦ hi h.symm
      simp [hnot]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  rw [hLHS, hWz_sum, integral_finsetSum Finset.univ fun i _ ↦ (hRHS_term i).1]
  exact Finset.sum_congr rfl fun i _ ↦ ((hRHS_term i).2).symm

end SteinMethod
