/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.SteinEquation
import Formalization.Exponential.GeometricSums
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Section 5 Additional Entries (`Formalization.Exponential.Sec5Extras`)

Provides items `M1` and `M2` from `docs/reviews/review-05D.md` (`SteinIntro_utf8.tex:2740-2745`,
`2774-2779`, `2953-2957`):
* `lem5_2_ode_ae`, `lem5_2_ode_ae_bdd`, and `lem5_2_ode_ae_bdd_hasDerivAt` (`Lem5_2_ode_ae`, `M1`):
  for locally integrable $h : \mathbb{R} \to \mathbb{R}$ integrable under $\mathrm{Exp}(1)$ (and in
  particular for every bounded measurable $h$), `expSteinSol h` is locally absolutely continuous on
  $\mathbb{R}$, satisfies `HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x` at
  Lebesgue-almost-every $x \in \mathbb{R}$, and is the unique locally absolutely continuous
  $g : \mathbb{R} \to \mathbb{R}$ with $g(0) = 0$ solving the exponential Stein ODE a.e.
* `sec5_2_eq5_6` and `sec5_2_eq5_6_strong` (`Sec5_2_eq5_6`, `M2`, eq. `(5.6)` `\label{179}`,
  `SteinIntro_utf8.tex:2953-2957`): wraps `integrable_and_isEquilibrium_geom_sum_clean` to show that
  $W = p \sum_{i=1}^N X_i$ is integrable with $\mathbb{E}[W] = 1$ and
  $W^e = p (\sum_{i=1}^{M-1} X_i + X_M^e)$ is an equilibrium coupling of $W$.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### 1. Item M1: Lemma 5.2 a.e. ODE and Locally AC Uniqueness (`Lem5_2_ode_ae`) -/

/-- **Lemma 5.2, almost-everywhere ODE and locally AC uniqueness** (`\label{lem172}`, eqs.
`(5.1)`–`(5.2)` `\label{171}`–`\label{172}`, `SteinIntro_utf8.tex:2740-2745, 2774-2779`;
`ISSUE-5.2-ODE`, `M1`): for locally integrable $h : \mathbb{R} \to \mathbb{R}$ integrable under
$\mathrm{Exp}(1)$, `expSteinSol h` is locally absolutely continuous on $\mathbb{R}$, satisfies
$f_h'(x) - f_h(x) = h(x) - \mathbb{E}[h(Z)]$ with a two-sided derivative at Lebesgue-almost-every
$x \in \mathbb{R}$, and is the unique locally absolutely continuous function
$g : \mathbb{R} \to \mathbb{R}$ with $g(0) = 0$ satisfying $g'(x) - g(x) = h(x) - \mathbb{E}[h(Z)]$
almost everywhere. -/
theorem lem5_2_ode_ae {h : ℝ → ℝ}
    (hLoc : LocallyIntegrable h volume) (hInt : Integrable h stdExpLaw) :
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (expSteinSol h) a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x) ∧
      ∀ g : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b) → g 0 = 0 →
        (∀ᵐ x ∂volume, deriv g x - g x = h x - stdExpExpect h) →
        g = expSteinSol h := by
  set φ : ℝ → ℝ := fun t ↦ (h t - stdExpExpect h) * Real.exp (-t)
  have hφ_loc : LocallyIntegrable φ volume :=
    (hLoc.sub (locallyIntegrable_const _)).mul_continuous (by fun_prop)
  have hφ_iint : ∀ c d : ℝ, IntervalIntegrable φ volume c d := fun c d ↦
    intervalIntegrable_iff.mpr
      ((hφ_loc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have heq_sol : expSteinSol h = fun x ↦ Real.exp x * ∫ t in (0 : ℝ)..x, φ t :=
    funext (expSteinSol_eq_exp_mul_intervalIntegral hLoc hInt)
  have hac_sol : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (expSteinSol h) a b := fun a b ↦ by
    let A : ℝ := min (min a b) 0
    let B : ℝ := max (max a b) 0
    have hAB : A ≤ B := (min_le_right _ 0).trans (le_max_right _ 0)
    have h0_mem : (0 : ℝ) ∈ uIcc A B := by
      rw [uIcc_of_le hAB]
      exact ⟨min_le_right _ 0, le_max_right _ 0⟩
    have huIcc : uIcc a b ⊆ uIcc A B := by
      rw [uIcc, uIcc_of_le hAB]
      exact Icc_subset_Icc (min_le_left _ 0) (le_max_left _ 0)
    have hac_int : AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in (0 : ℝ)..x, φ t) a b :=
      ((hφ_iint A B).absolutelyContinuousOnInterval_intervalIntegral h0_mem).mono huIcc
    have hac_exp : AbsolutelyContinuousOnInterval Real.exp a b :=
      (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ 1 Real.exp (uIcc a b))
        |>.absolutelyContinuousOnInterval
    rw [heq_sol]
    exact hac_exp.mul hac_int
  have hae_sol : ∀ᵐ x ∂volume,
      HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hφ_loc] with x hx
    have hF : HasDerivAt (fun u ↦ ∫ t in (0 : ℝ)..u, φ t) (φ x) x := hx 0
    rw [heq_sol]
    convert (Real.hasDerivAt_exp x).fun_mul hF using 1
    dsimp only [φ]
    have hexp : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      Real.exp x * (∫ t in (0 : ℝ)..x, φ t) + h x - stdExpExpect h
        = Real.exp x * (∫ t in (0 : ℝ)..x, φ t) +
            (h x - stdExpExpect h) * (Real.exp x * Real.exp (-x)) := by rw [hexp]; ring
      _ = Real.exp x * (∫ t in (0 : ℝ)..x, φ t) +
            Real.exp x * ((h x - stdExpExpect h) * Real.exp (-x)) := by ring
  refine ⟨hac_sol, hae_sol, fun g hg_ac hg0 hg_ode ↦ ?_⟩
  have hg_diff_ae : ∀ᵐ x ∂volume, DifferentiableAt ℝ g x := by
    have hn : ∀ n : ℕ,
        ∀ᵐ x ∂volume, x ∈ uIcc (-(n : ℝ) - 1) ((n : ℝ) + 1) → DifferentiableAt ℝ g x :=
      fun n ↦ (hg_ac (-(n : ℝ) - 1) ((n : ℝ) + 1)).ae_differentiableAt
    filter_upwards [ae_all_iff.mpr hn] with x hx
    let n : ℕ := Nat.ceil |x|
    have hle : |x| ≤ (n : ℝ) := Nat.le_ceil |x|
    have habs := abs_le.mp hle
    have hmem : x ∈ uIcc (-(n : ℝ) - 1) ((n : ℝ) + 1) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
    exact hx n hmem
  set d : ℝ → ℝ := fun x ↦ Real.exp (-x) * (g x - expSteinSol h x)
  have hd_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval d a b := fun a b ↦
    ((by fun_prop : ContDiff ℝ 1 fun x : ℝ ↦ Real.exp (-x)).contDiffOn
      |>.absolutelyContinuousOnInterval).mul ((hg_ac a b).sub (hac_sol a b))
  have hd_deriv_ae : ∀ᵐ x ∂volume, deriv d x = 0 := by
    filter_upwards [hae_sol, hg_diff_ae, hg_ode] with x hsol hgd hgo
    have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-x)) x := by
      simpa using (hasDerivAt_id x).neg.exp
    have hsub : HasDerivAt (fun u ↦ g u - expSteinSol h u)
        (deriv g x - (expSteinSol h x + h x - stdExpExpect h)) x :=
      hgd.hasDerivAt.fun_sub hsol
    have hd0 : HasDerivAt d 0 x := by
      convert hexp.fun_mul hsub using 1
      have hgx : deriv g x = g x + h x - stdExpExpect h := by linarith
      rw [hgx]
      ring
    exact hd0.deriv
  have hd0 : d 0 = 0 := by simp [d, hg0, expSteinSol_zero hInt]
  ext x
  have hint0 : ∫ t in (0 : ℝ)..x, deriv d t = 0 := by
    rw [intervalIntegral.integral_congr_ae (hd_deriv_ae.mono fun t ht _ ↦ ht),
      intervalIntegral.integral_zero]
  have hsub0 : d x - d 0 = 0 := by
    rw [← (hd_ac 0 x).integral_deriv_eq_sub, hint0]
  have hx : d x = 0 := by linarith
  simp only [d, mul_eq_zero, Real.exp_ne_zero, false_or, sub_eq_zero] at hx
  exact hx

/-- Bounded measurable specialization of `lem5_2_ode_ae` (`M1`): if $h : \mathbb{R} \to \mathbb{R}$
is measurable and $|h(x)| \le M$ for all $x \in \mathbb{R}$, then `expSteinSol h` is locally
absolutely continuous, satisfies
`HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x` almost everywhere, and is
the unique locally absolutely continuous $g$ with $g(0) = 0$ solving
`deriv g x - g x = h x - stdExpExpect h` a.e. -/
theorem lem5_2_ode_ae_bdd {h : ℝ → ℝ} {M : ℝ}
    (hMeas : Measurable h) (hLe : ∀ x : ℝ, |h x| ≤ M) :
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (expSteinSol h) a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x) ∧
      ∀ g : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b) → g 0 = 0 →
        (∀ᵐ x ∂volume, deriv g x - g x = h x - stdExpExpect h) →
        g = expSteinSol h := by
  have hLoc : LocallyIntegrable h volume := fun x ↦
    let ⟨s, hs, hint⟩ := locallyIntegrable_const (μ := volume) M x
    ⟨s, hs, hint.mono' hMeas.aestronglyMeasurable.restrict
      (ae_of_all _ fun t ↦ by rw [Real.norm_eq_abs]; exact hLe t)⟩
  have hInt : Integrable h stdExpLaw :=
    Integrable.of_bound hMeas.aestronglyMeasurable M
      (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hLe x)
  exact lem5_2_ode_ae hLoc hInt

/-- Bounded measurable specialization of `lem5_2_ode_ae` with `HasDerivAt` in the uniqueness
hypothesis (`M1`). -/
theorem lem5_2_ode_ae_bdd_hasDerivAt {h : ℝ → ℝ} {M : ℝ}
    (hMeas : Measurable h) (hLe : ∀ x : ℝ, |h x| ≤ M) :
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (expSteinSol h) a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x) ∧
      ∀ g : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b) → g 0 = 0 →
        (∀ᵐ x ∂volume, HasDerivAt g (g x + h x - stdExpExpect h) x) →
        g = expSteinSol h := by
  obtain ⟨hac, hae, huniq⟩ := lem5_2_ode_ae_bdd hMeas hLe
  refine ⟨hac, hae, fun g hg_ac hg0 hg_hd ↦ huniq g hg_ac hg0 ?_⟩
  filter_upwards [hg_hd] with x hx
  linarith [hx.deriv]

/-! ### 2. Item M2: Equation (5.6) Geometric-Sum Equilibrium Coupling (`Sec5_2_eq5_6`) -/

/-- **Equation (5.6)** (`\label{179}`, `SteinIntro_utf8.tex:2953-2957`; `M2`): for independent
non-negative mean-$1$ summands $(X_i)_{i \ge 1}$ (requiring $L^1$ only), integer-valued
$N, M \ge 1$ a.s. with $\mathbb{E}[N] = 1/p$ and $\mathbb{P}(M = m) = p\,\mathbb{P}(N \ge m)$
($m \ge 1$) jointly independent of $(X_i)_{i \ge 1}$, and equilibrium variables $X_i^e$ each
independent of $(N, M, (X_j)_{j \ne i})$, the sum $W = p \sum_{i=1}^N X_i$ is integrable with
$\mathbb{E}[W] = 1$ and $W^e = p (\sum_{i=1}^{M-1} X_i + X_M^e)$ has the equilibrium distribution
of $W$. Wraps `integrable_and_isEquilibrium_geom_sum_clean`. -/
theorem sec5_2_eq5_6
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} {X Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ}
    (hp₀ : 0 < p) (_hp₁ : p ≤ 1)
    (hX_aem : ∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P)
    (hX_nn : ∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i)
    (hX_int : ∀ i : ℕ, 1 ≤ i → Integrable (X i) P)
    (hX_mean : ∀ i : ℕ, 1 ≤ i → ∫ ω, X i ω ∂P = 1)
    (hX_indep : iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P)
    (hN_aem : AEMeasurable N P)
    (hM_aem : AEMeasurable M P)
    (hN_pos : ∀ᵐ ω ∂P, 1 ≤ N ω)
    (hN_int : Integrable (fun ω ↦ (N ω : ℝ)) P)
    (hN_mean : ∫ ω, (N ω : ℝ) ∂P = 1 / p)
    (hM_pos : ∀ᵐ ω ∂P, 1 ≤ M ω)
    (hM_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω})
    (hXe_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (Xe i))
    (hXe_indep : ∀ i : {i : ℕ // 1 ≤ i},
      IndepFun (Xe i.1)
        (fun ω ↦ (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P)
    (hNM_indep : IndepFun (fun ω ↦ (N ω, M ω))
      (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P) :
    let W : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
    let We : Ω → ℝ := fun ω ↦ p * ((∑ i ∈ Finset.Ico 1 (M ω), X i ω) + Xe (M ω) ω)
    Integrable W P ∧ (∫ ω, W ω ∂P = 1) ∧ IsEquilibrium P W P We := by
  dsimp only
  let I₁ := {i : ℕ // 1 ≤ i}
  let N₁ : Ω → ℕ := fun ω ↦ max (hN_aem.mk N ω) 1
  let M₁ : Ω → ℕ := fun ω ↦ max (hM_aem.mk M ω) 1
  let X₁ : ℕ → Ω → ℝ := fun i ω ↦
    if hi : 1 ≤ i then max ((hX_aem i hi).mk (X i) ω) 0 else 0
  let Xe₁ : ℕ → Ω → ℝ := fun i ω ↦
    if hi : 1 ≤ i then (hXe_eq i hi).2.2.1.mk (Xe i) ω else 0
  have hN₁_meas : Measurable N₁ := hN_aem.measurable_mk.max measurable_const
  have hM₁_meas : Measurable M₁ := hM_aem.measurable_mk.max measurable_const
  have hM₁_ge : ∀ ω, 1 ≤ M₁ ω := fun _ ↦ le_max_right _ 1
  have hX₁_meas : ∀ i, Measurable (X₁ i) := fun i ↦ by
    dsimp only [X₁]; split_ifs with hi
    · exact (hX_aem i hi).measurable_mk.max measurable_const
    · exact measurable_const
  have hXe₁_meas : ∀ i, Measurable (Xe₁ i) := fun i ↦ by
    dsimp only [Xe₁]; split_ifs with hi
    · exact (hXe_eq i hi).2.2.1.measurable_mk
    · exact measurable_const
  have hX₁_nn : ∀ i ω, 0 ≤ X₁ i ω := fun i ω ↦ by
    dsimp only [X₁]; split_ifs
    · exact le_max_right _ 0
    · exact le_rfl
  have hN_ae : N =ᵐ[P] N₁ := by
    filter_upwards [hN_aem.ae_eq_mk, hN_pos] with ω h1 h2
    dsimp only [N₁]; rw [← h1, max_eq_left h2]
  have hM_ae : M =ᵐ[P] M₁ := by
    filter_upwards [hM_aem.ae_eq_mk, hM_pos] with ω h1 h2
    dsimp only [M₁]; rw [← h1, max_eq_left h2]
  have hX_ae : ∀ i : ℕ, 1 ≤ i → X i =ᵐ[P] X₁ i := fun i hi ↦ by
    filter_upwards [(hX_aem i hi).ae_eq_mk, hX_nn i hi] with ω h1 (h2 : 0 ≤ X i ω)
    dsimp only [X₁]; simp only [hi, ↓reduceDIte, ← h1, max_eq_left h2]
  have hXe_ae : ∀ i : ℕ, 1 ≤ i → Xe i =ᵐ[P] Xe₁ i := fun i hi ↦ by
    filter_upwards [(hXe_eq i hi).2.2.1.ae_eq_mk] with ω h1
    dsimp only [Xe₁]; simp only [hi, ↓reduceDIte, ← h1]
  have hall_ae : ∀ᵐ ω ∂P, ∀ i : I₁, X i.1 ω = X₁ i.1 ω ∧ Xe i.1 ω = Xe₁ i.1 ω :=
    ae_all_iff.mpr fun i ↦ (hX_ae i.1 i.2).and (hXe_ae i.1 i.2)
  have hX₁_indep : iIndepFun (fun i : I₁ ↦ X₁ i.1) P :=
    hX_indep.congr fun i ↦ hX_ae i.1 i.2
  have hXe₁_indep : ∀ i : I₁,
      IndepFun (Xe₁ i.1)
        (fun ω ↦ (N₁ ω, M₁ ω, fun j : {j : I₁ // j ≠ i} ↦ X₁ j.1.1 ω)) P := fun i ↦
    (hXe_indep i).congr (hXe_ae i.1 i.2)
      (((hN_ae.and hM_ae).and hall_ae).mono fun ω ⟨⟨hNω, hMω⟩, hXω⟩ ↦
        Prod.ext hNω (Prod.ext hMω (funext fun j ↦ (hXω j.1).1)))
  have hNM₁_indep : IndepFun (fun ω ↦ (N₁ ω, M₁ ω))
      (fun ω (i : I₁) ↦ X₁ i.1 ω) P :=
    hNM_indep.congr
      ((hN_ae.and hM_ae).mono fun ω ⟨h1, h2⟩ ↦ Prod.ext h1 h2)
      (hall_ae.mono fun ω hω ↦ funext fun i ↦ (hω i).1)
  have hX₁_int : ∀ i : ℕ, 1 ≤ i → Integrable (X₁ i) P := fun i hi ↦
    (hX_int i hi).congr (hX_ae i hi)
  have hX₁_mean : ∀ i : ℕ, 1 ≤ i → ∫ ω, X₁ i ω ∂P = 1 := fun i hi ↦ by
    rw [← integral_congr_ae (hX_ae i hi), hX_mean i hi]
  have hXe₁_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X₁ i) P (Xe₁ i) := fun i hi ↦
    (hXe_eq i hi).congr_identDistrib
      (IdentDistrib.of_ae_eq (hX_aem i hi) (hX_ae i hi))
      (IdentDistrib.of_ae_eq (hXe_eq i hi).2.2.1 (hXe_ae i hi))
  have hM₁_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M₁ ω = m} = p * P.real {ω | m ≤ N₁ ω} :=
    fun m hm ↦ by
      have hc1 : P.real {ω | M₁ ω = m} = P.real {ω | M ω = m} :=
        measureReal_congr (hM_ae.mono fun ω hω ↦ propext (by simp [hω]))
      have hc2 : P.real {ω | m ≤ N₁ ω} = P.real {ω | m ≤ N ω} :=
        measureReal_congr (hN_ae.mono fun ω hω ↦ propext (by simp [hω]))
      rw [hc1, hc2, hM_pmf m hm]
  have hN₁R_int : Integrable (fun ω ↦ (N₁ ω : ℝ)) P :=
    hN_int.congr (hN_ae.mono fun ω hω ↦ congrArg Nat.cast hω)
  have hN₁R_mean : ∫ ω, (N₁ ω : ℝ) ∂P = 1 / p := by
    rw [← integral_congr_ae (hN_ae.mono fun ω hω ↦ congrArg Nat.cast hω), hN_mean]
  let W₁ : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω
  let We₁ : Ω → ℝ := fun ω ↦ p * ((∑ i ∈ Finset.Ico 1 (M₁ ω), X₁ i ω) + Xe₁ (M₁ ω) ω)
  obtain ⟨hW₁_int, hW₁_mean, hEqW₁⟩ :=
    integrable_and_isEquilibrium_geom_sum_clean P hp₀ hX₁_meas hXe₁_meas hX₁_nn hX₁_int
      hX₁_mean hX₁_indep hN₁_meas hM₁_meas hM₁_ge hN₁R_int hN₁R_mean hM₁_pmf hXe₁_eq
      hXe₁_indep hNM₁_indep
  have hW_ae : (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω) =ᵐ[P] W₁ := by
    filter_upwards [hN_ae, hall_ae] with ω hNω hXω
    dsimp only [W₁]; rw [hNω]; congr 1
    exact Finset.sum_congr rfl fun i hi ↦ (hXω ⟨i, (Finset.mem_Icc.mp hi).1⟩).1
  have hWe_ae :
      (fun ω ↦ p * ((∑ i ∈ Finset.Ico 1 (M ω), X i ω) + Xe (M ω) ω)) =ᵐ[P] We₁ := by
    filter_upwards [hM_ae, hall_ae] with ω hMω hXω
    dsimp only [We₁]; rw [hMω]; congr 1; congr 1
    · exact Finset.sum_congr rfl fun i hi ↦ (hXω ⟨i, (Finset.mem_Ico.mp hi).1⟩).1
    · exact (hXω ⟨M₁ ω, hM₁_ge ω⟩).2
  refine ⟨hW₁_int.congr hW_ae.symm, ?_,
    hEqW₁.congr_identDistrib
      (IdentDistrib.of_ae_eq hW₁_int.aemeasurable hW_ae.symm)
      (IdentDistrib.of_ae_eq hEqW₁.2.2.1 hWe_ae.symm)⟩
  rw [integral_congr_ae hW_ae, hW₁_mean]

end SteinMethod
