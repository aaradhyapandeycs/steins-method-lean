/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Normal.DependencyCount
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Normal Approximation via Dependency Neighborhoods and Dependency Graphs

Formalizes Definition 3.1 (`SteinIntro.tex:805-812`) and the Stein-operator supremum bound for
Theorem 3.5 (`\label{thm41}`, eq. `(3.8)` `\label{41}`, `SteinIntro.tex:815-907`; `ISSUE-3.5`).
-/

open MeasureTheory

namespace SteinMethod

/-- A dependency graph defines dependency neighborhoods in the sense of Definition 3.1
(`SteinIntro.tex:805-812`; `ISSUE-3.5`). -/
theorem IsDependencyGraph.hasDependencyNeighborhoods
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hG : IsDependencyGraph P X N) :
    HasDependencyNeighborhoods P X N := by
  intro i
  have hAB : ∀ a ∈ ({i} : Finset (Fin n)), ∀ b ∈ (N i)ᶜ, b ∉ N a := by
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha]
    exact Finset.mem_compl.mp hb
  have hψ : Measurable (fun (g : ((N i)ᶜ : Finset (Fin n)) → ℝ) (j : {j // j ∉ N i}) ↦
      g ⟨j.1, Finset.mem_compl.mpr j.2⟩) := by
    rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply (⟨j.1, Finset.mem_compl.mpr j.2⟩ : ((N i)ᶜ : Finset (Fin n)))
  exact (hG.2.2 {i} (N i)ᶜ hAB).comp
    (measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩) hψ

/-- Almost-everywhere measurability of $W = (\sum_{i=1}^n X_i)/\sigma$ in Theorem 3.5
(`\label{thm41}`, `SteinIntro.tex:815-822`). -/
theorem depGraph_aemeasurable_W
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → ℝ} {σ : ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P) :
    AEMeasurable (fun ω ↦ (∑ i : Fin n, X i ω) / σ) P :=
  (Finset.univ.aemeasurable_fun_sum fun i _ ↦ hX_meas i).div_const σ

/-- One-sided quadratic growth bound: if $Q(0) = 0$ and $Q'(s) \le 2 s$ for $s \ge 0$, then
$Q(s) \le s^2$ for $s \ge 0$ (`SteinIntro.tex:842-845`). -/
private lemma quad_bound_of_hasDerivAt_nonneg {Q Q' : ℝ → ℝ}
    (hQ0 : Q 0 = 0) (hQ : ∀ s, HasDerivAt Q (Q' s) s)
    (hQ' : ∀ s, 0 ≤ s → Q' s ≤ 2 * s) :
    ∀ s, 0 ≤ s → Q s ≤ s ^ 2 := by
  let G : ℝ → ℝ := fun s ↦ s ^ 2 - Q s
  have hG_deriv (s : ℝ) : HasDerivAt G (2 * s - Q' s) s := by
    have hpow := hasDerivAt_pow 2 s
    have hp : ((2 : ℕ) : ℝ) * s ^ (2 - 1) = 2 * s := by
      change ((2 : ℕ) : ℝ) * s ^ 1 = 2 * s
      rw [Nat.cast_ofNat, pow_one]
    rw [hp] at hpow
    exact hpow.fun_sub (hQ s)
  have hG_cont : ContinuousOn G (Set.Ici 0) :=
    (continuous_iff_continuousAt.mpr fun s ↦ (hG_deriv s).continuousAt).continuousOn
  have hmono : MonotoneOn G (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hG_cont
      (fun x _ ↦ (hG_deriv x).hasDerivWithinAt)
      (fun x hx ↦ sub_nonneg.mpr (hQ' x (Set.mem_Ici.mp (interior_subset hx))))
  intro s hs
  have hle : G 0 ≤ G s := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  dsimp only [G] at hle
  rw [zero_pow two_ne_zero, hQ0, sub_zero] at hle
  linarith

/-- Second-order Taylor remainder bound $|f(w) - f(u) - (w - u) f'(w)| \le (w - u)^2$ for
$f \in \mathcal{F}$ with $\|f''\| \le 2$ (`SteinIntro.tex:842-845`). -/
private lemma taylor_sq_bound {f : ℝ → ℝ} (hf : f ∈ normalWassersteinClass) (w u : ℝ) :
    |f w - f u - (w - u) * deriv f w| ≤ (w - u) ^ 2 := by
  rcases hf with ⟨hdf, hddf, _, _, hdd_bound⟩
  let R : ℝ → ℝ := fun t ↦ f t - f w - (t - w) * deriv f w
  let R' : ℝ → ℝ := fun t ↦ deriv f t - deriv f w
  have hR0 : R w = 0 := by
    dsimp only [R]
    ring
  have hR_deriv (t : ℝ) : HasDerivAt R (R' t) t := by
    have h1 : HasDerivAt (fun y ↦ f y - f w) (deriv f t) t :=
      (hdf t).hasDerivAt.sub_const (f w)
    have h2 : HasDerivAt (fun y ↦ (y - w) * deriv f w) (1 * deriv f w) t :=
      ((hasDerivAt_id' t).sub_const w).mul_const (deriv f w)
    have h12 := h1.fun_sub h2
    have heq : deriv f t - 1 * deriv f w = R' t := by
      dsimp only [R']
      ring
    rwa [heq] at h12
  have hR'_bound (t : ℝ) : |R' t| ≤ 2 * |t - w| := by
    have hmvt := convex_univ.norm_image_sub_le_of_norm_deriv_le (C := 2) (f := deriv f)
      (fun x _ ↦ hddf x)
      (fun x _ ↦ by simpa only [Real.norm_eq_abs] using hdd_bound x)
      (Set.mem_univ w) (Set.mem_univ t)
    simpa only [R', Real.norm_eq_abs] using hmvt
  have hpos (s : ℝ) (hs : 0 ≤ s) : |R (w + s)| ≤ s ^ 2 := by
    have hb (x : ℝ) (hx : 0 ≤ x) : |R' (w + x)| ≤ 2 * x := by
      have h := hR'_bound (w + x)
      have heq : w + x - w = x := by ring
      rwa [heq, abs_of_nonneg hx] at h
    have h_upper : R (w + s) ≤ s ^ 2 :=
      quad_bound_of_hasDerivAt_nonneg (by simp only [add_zero, hR0])
        (fun x ↦ HasDerivAt.comp_const_add w x (hR_deriv (w + x)))
        (fun x hx ↦ (abs_le.mp (hb x hx)).2) s hs
    have h_lower : -R (w + s) ≤ s ^ 2 :=
      quad_bound_of_hasDerivAt_nonneg (by simp only [add_zero, hR0, neg_zero])
        (fun x ↦ (HasDerivAt.comp_const_add w x (hR_deriv (w + x))).fun_neg)
        (fun x hx ↦ by linarith [(abs_le.mp (hb x hx)).1]) s hs
    exact abs_le.mpr ⟨by linarith, h_upper⟩
  have hneg (s : ℝ) (hs : 0 ≤ s) : |R (w - s)| ≤ s ^ 2 := by
    have hb (x : ℝ) (hx : 0 ≤ x) : |R' (w - x)| ≤ 2 * x := by
      have h := hR'_bound (w - x)
      have heq : w - x - w = -x := by ring
      rwa [heq, abs_neg, abs_of_nonneg hx] at h
    have h_upper : R (w - s) ≤ s ^ 2 :=
      quad_bound_of_hasDerivAt_nonneg (by simp only [sub_zero, hR0])
        (fun x ↦ HasDerivAt.comp_const_sub w x (hR_deriv (w - x)))
        (fun x hx ↦ by linarith [(abs_le.mp (hb x hx)).1]) s hs
    have h_lower : -R (w - s) ≤ s ^ 2 :=
      quad_bound_of_hasDerivAt_nonneg (by simp only [sub_zero, hR0, neg_zero])
        (fun x ↦ (HasDerivAt.comp_const_sub w x (hR_deriv (w - x))).fun_neg)
        (fun x hx ↦ by linarith [(abs_le.mp (hb x hx)).2]) s hs
    exact abs_le.mpr ⟨by linarith, h_upper⟩
  have htarget : f w - f u - (w - u) * deriv f w = -R u := by
    dsimp only [R]
    ring
  rw [htarget, abs_neg]
  rcases le_total w u with hwu | huw
  · have h := hpos (u - w) (sub_nonneg.mpr hwu)
    have h1 : w + (u - w) = u := add_sub_cancel w u
    have h2 : (u - w) ^ 2 = (w - u) ^ 2 := by ring
    rwa [h1, h2] at h
  · have h := hneg (w - u) (sub_nonneg.mpr huw)
    have h1 : w - (w - u) = u := sub_sub_cancel w u
    rwa [h1] at h

/-- Stein-operator supremum bound over `normalWassersteinClass` for Theorem 3.5, corrected
(`\label{thm41}`, eq. `(3.8)` `\label{41}`, `SteinIntro.tex:815-907`; `ISSUE-3.5`). -/
theorem depGraph_iSup_normalWassersteinClass_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hG : IsDependencyGraph P X N)
    (hVar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P) :
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / σ
    let D : ℝ := ((Finset.univ.sup fun i : Fin n ↦ (N i).card : ℕ) : ℝ)
    (⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|) ≤
      ENNReal.ofReal
        (D ^ 2 / σ ^ 3 * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P)) := by
  intro σ W D
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  have hσ_ne : σ ≠ 0 := hσ_pos.ne'
  have hσ_sq : σ ^ 2 = ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P :=
    Real.sq_sqrt hVar.le
  have hD_nonneg : 0 ≤ D := Nat.cast_nonneg _
  let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ (N i)ᶜ, X j ω) / σ
  let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, ∑ k ∈ N i, X i ω * X k ω
  have hW_meas : AEMeasurable W P := depGraph_aemeasurable_W hX_meas
  have hWi_meas (i : Fin n) : AEMeasurable (W_i i) P :=
    ((N i)ᶜ.aemeasurable_fun_sum fun j _ ↦ hX_meas j).div_const σ
  have hW_sub (i : Fin n) (ω : Ω) : W ω - W_i i ω = (∑ j ∈ N i, X j ω) / σ := by
    dsimp only [W, W_i]
    rw [← Finset.sum_add_sum_compl (N i) (fun j ↦ X j ω)]
    ring
  have hS_memLp2 : MemLp S 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦
      memLp_finsetSum (N i) fun k _ ↦ memLp_two_mul_of_memLp_four (hX4 i) (hX4 k)
  refine iSup₂_le fun f hf ↦ ENNReal.ofReal_le_ofReal ?_
  have ⟨hdf, hddf, hf_bound, hdf_bound, _⟩ := hf
  have hf_meas : Measurable f := hdf.continuous.measurable
  have hdf_meas : Measurable (deriv f) := hddf.continuous.measurable
  let T_i : Fin n → Ω → ℝ := fun i ω ↦
    X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω))
  let A : Ω → ℝ := fun ω ↦ (1 / σ) * ∑ i : Fin n, T_i i ω
  let B : Ω → ℝ := fun ω ↦ deriv f (W ω) * (1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω))
  let C : Ω → ℝ := fun ω ↦ (1 / σ) * ∑ i : Fin n, X i ω * f (W_i i ω)
  have h_stein_pt (ω : Ω) : normalSteinOp f (W ω) = -A ω + B ω - C ω := by
    have h1 : (∑ i : Fin n, X i ω) * f (W ω) = ∑ i : Fin n, X i ω * f (W ω) :=
      Finset.sum_mul Finset.univ (fun i ↦ X i ω) (f (W ω))
    have h2 : deriv f (W ω) * (1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω)) =
        deriv f (W ω) - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
      have hm : deriv f (W ω) * ((1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω)) =
          (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
        calc deriv f (W ω) * ((1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω))
            = (1 / σ) * ((∑ i : Fin n, X i ω * (W ω - W_i i ω)) * deriv f (W ω)) := by ring
          _ = (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
              rw [Finset.sum_mul]
      calc deriv f (W ω) * (1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω))
          = deriv f (W ω) - deriv f (W ω) * ((1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω)) := by
            ring
        _ = deriv f (W ω) - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω) := by
            rw [hm]
    have h3 : (∑ i : Fin n, T_i i ω) + (∑ i : Fin n, X i ω * f (W_i i ω)) +
        (∑ i : Fin n, X i ω * (W ω - W_i i ω) * deriv f (W ω)) =
        ∑ i : Fin n, X i ω * f (W ω) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp only [T_i]
      ring
    have h4 : W ω * f (W ω) = (1 / σ) * ∑ i : Fin n, X i ω * f (W ω) := by
      have hw : W ω * f (W ω) = (1 / σ) * ((∑ i : Fin n, X i ω) * f (W ω)) := by
        change ((∑ i : Fin n, X i ω) / σ) * f (W ω) = (1 / σ) * ((∑ i : Fin n, X i ω) * f (W ω))
        ring
      rw [hw, h1]
    dsimp only [normalSteinOp, A, B, C]
    rw [h4, ← h3, h2]
    ring
  have hind_Wi (i : Fin n) : ProbabilityTheory.IndepFun (X i) (fun ω ↦ f (W_i i ω)) P := by
    let ψ : ({j // j ∉ N i} → ℝ) → ℝ := fun g ↦ f ((∑ j : {j // j ∉ N i}, g j) / σ)
    have hψ : Measurable ψ :=
      hf_meas.comp
        ((Finset.univ.measurable_sum fun (j : {j // j ∉ N i}) _ ↦
          measurable_pi_apply j).div_const σ)
    have hc := (hG.hasDependencyNeighborhoods i).comp measurable_id hψ
    have heq : ψ ∘ (fun ω (j : {j // j ∉ N i}) ↦ X j ω) = fun ω ↦ f (W_i i ω) := by
      ext ω
      dsimp only [Function.comp_apply, ψ, W_i]
      rw [Finset.sum_subtype (N i)ᶜ (fun _ ↦ Finset.mem_compl) (fun j ↦ X j ω)]
    simpa only [Function.id_comp, heq] using hc
  have hfWi_meas (i : Fin n) : AEStronglyMeasurable (fun ω ↦ f (W_i i ω)) P :=
    (hf_meas.comp_aemeasurable (hWi_meas i)).aestronglyMeasurable
  have hint_Ci (i : Fin n) : Integrable (fun ω ↦ X i ω * f (W_i i ω)) P := by
    refine ((depGraph_integrable_of_memLp_four (hX4 i)).norm.mul_const 2).mono'
      ((hX_meas i).aestronglyMeasurable.mul (hfWi_meas i))
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf_bound (W_i i ω)) (abs_nonneg (X i ω))
  have hint_C : Integrable C P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ hint_Ci i).const_mul (1 / σ)
  have hC_zero : ∫ ω, C ω ∂P = 0 := by
    dsimp only [C]
    rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ hint_Ci i]
    have hz (i : Fin n) : ∫ ω, X i ω * f (W_i i ω) ∂P = 0 := by
      rw [(hind_Wi i).integral_fun_mul_eq_mul_integral
        (hX_meas i).aestronglyMeasurable (hfWi_meas i), hX0 i, zero_mul]
    simp [hz]
  have hTi_bound (i : Fin n) (ω : Ω) :
      |T_i i ω| ≤ (1 / σ ^ 2) * ∑ j ∈ N i, ∑ k ∈ N i, |X i ω| * |X j ω| * |X k ω| := by
    have htay := taylor_sq_bound hf (W ω) (W_i i ω)
    have hsq_sum : (∑ j ∈ N i, X j ω) ^ 2 ≤
        ∑ j ∈ N i, ∑ k ∈ N i, |X j ω| * |X k ω| := by
      have habs : |∑ j ∈ N i, X j ω| ≤ ∑ j ∈ N i, |X j ω| :=
        Finset.abs_sum_le_sum_abs (fun j ↦ X j ω) (N i)
      calc (∑ j ∈ N i, X j ω) ^ 2
          = |∑ j ∈ N i, X j ω| * |∑ j ∈ N i, X j ω| := by rw [← sq, sq_abs]
        _ ≤ (∑ j ∈ N i, |X j ω|) * (∑ k ∈ N i, |X k ω|) :=
            mul_le_mul habs habs (abs_nonneg _) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        _ = ∑ j ∈ N i, ∑ k ∈ N i, |X j ω| * |X k ω| :=
            Finset.sum_mul_sum (N i) (N i) (fun j ↦ |X j ω|) (fun k ↦ |X k ω|)
    calc |T_i i ω|
        = |X i ω| * |f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)| := abs_mul _ _
      _ ≤ |X i ω| * (W ω - W_i i ω) ^ 2 :=
          mul_le_mul_of_nonneg_left htay (abs_nonneg (X i ω))
      _ = (1 / σ ^ 2) * (|X i ω| * (∑ j ∈ N i, X j ω) ^ 2) := by
          rw [hW_sub i ω, div_pow]
          ring
      _ ≤ (1 / σ ^ 2) * (|X i ω| * ∑ j ∈ N i, ∑ k ∈ N i, |X j ω| * |X k ω|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsq_sum (abs_nonneg (X i ω))) (by positivity)
      _ = (1 / σ ^ 2) * ∑ j ∈ N i, ∑ k ∈ N i, |X i ω| * |X j ω| * |X k ω| := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          ring
  have hTi_meas (i : Fin n) : AEStronglyMeasurable (T_i i) P := by
    have hm1 : AEMeasurable (fun ω ↦ f (W ω) - f (W_i i ω)) P :=
      (hf_meas.comp_aemeasurable hW_meas).fun_sub (hf_meas.comp_aemeasurable (hWi_meas i))
    have hm2 : AEMeasurable (fun ω ↦ (W ω - W_i i ω) * deriv f (W ω)) P :=
      (hW_meas.fun_sub (hWi_meas i)).fun_mul (hdf_meas.comp_aemeasurable hW_meas)
    exact ((hX_meas i).fun_mul (hm1.fun_sub hm2)).aestronglyMeasurable
  have hint_dom_i (i : Fin n) :
      Integrable (fun ω ↦ ∑ j ∈ N i, ∑ k ∈ N i, |X i ω| * |X j ω| * |X k ω|) P :=
    integrable_finsetSum (N i) fun j _ ↦
      integrable_finsetSum (N i) fun k _ ↦ integrable_abs_mul_three (hX4 i) (hX4 j) (hX4 k)
  have hint_Ti (i : Fin n) : Integrable (T_i i) P := by
    refine ((hint_dom_i i).const_mul (1 / σ ^ 2)).mono' (hTi_meas i)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs] using hTi_bound i ω
  have hint_A : Integrable A P :=
    (integrable_finsetSum Finset.univ fun i _ ↦ hint_Ti i).const_mul (1 / σ)
  have hB_inner (ω : Ω) :
      1 - (1 / σ) * ∑ i : Fin n, X i ω * (W ω - W_i i ω) = (σ ^ 2 - S ω) / σ ^ 2 := by
    have hsum : (∑ i : Fin n, X i ω * (W ω - W_i i ω)) = (1 / σ) * S ω := by
      dsimp only [S]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hW_sub i ω, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [hsum, sub_div, div_self (pow_ne_zero 2 hσ_ne)]
    congr 1
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  have h_diff_lp2 : MemLp (fun ω ↦ |σ ^ 2 - S ω|) 2 P := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      ((memLp_const (σ ^ 2)).sub hS_memLp2).norm
  have h_diff_int : Integrable (fun ω ↦ |σ ^ 2 - S ω|) P :=
    h_diff_lp2.integrable one_le_two
  have hB_bound_pt (ω : Ω) :
      |B ω| ≤ (Real.sqrt (2 / Real.pi) / σ ^ 2) * |σ ^ 2 - S ω| := by
    have hb : B ω = deriv f (W ω) * ((σ ^ 2 - S ω) / σ ^ 2) := by
      dsimp only [B]
      rw [hB_inner ω]
    rw [hb, abs_mul, abs_div, abs_of_pos (pow_pos hσ_pos 2)]
    calc |deriv f (W ω)| * (|σ ^ 2 - S ω| / σ ^ 2)
        ≤ Real.sqrt (2 / Real.pi) * (|σ ^ 2 - S ω| / σ ^ 2) :=
          mul_le_mul_of_nonneg_right (hdf_bound (W ω))
            (div_nonneg (abs_nonneg _) (sq_nonneg σ))
      _ = (Real.sqrt (2 / Real.pi) / σ ^ 2) * |σ ^ 2 - S ω| := by ring
  have hint_B : Integrable B P := by
    have hB_meas : AEStronglyMeasurable B P := by
      have hm : AEMeasurable (fun ω ↦ deriv f (W ω) * ((σ ^ 2 - S ω) / σ ^ 2)) P :=
        (hdf_meas.comp_aemeasurable hW_meas).fun_mul
          ((hS_memLp2.aemeasurable.const_sub (σ ^ 2)).div_const (σ ^ 2))
      have heq : B = fun ω ↦ deriv f (W ω) * ((σ ^ 2 - S ω) / σ ^ 2) := by
        ext ω
        dsimp only [B]
        rw [hB_inner ω]
      rw [heq]
      exact hm.aestronglyMeasurable
    refine (h_diff_int.const_mul (Real.sqrt (2 / Real.pi) / σ ^ 2)).mono' hB_meas
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    simpa only [Real.norm_eq_abs] using hB_bound_pt ω
  have h_decomp : ∫ ω, normalSteinOp f (W ω) ∂P = -(∫ ω, A ω ∂P) + ∫ ω, B ω ∂P := by
    have hfn : (fun ω ↦ normalSteinOp f (W ω)) = fun ω ↦ (-A ω + B ω) - C ω := by
      ext ω
      exact h_stein_pt ω
    rw [hfn, integral_sub (hint_A.fun_neg.fun_add hint_B) hint_C,
      integral_add hint_A.fun_neg hint_B, integral_neg, hC_zero, sub_zero]
  have hA_le : |∫ ω, A ω ∂P| ≤ D ^ 2 / σ ^ 3 * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P := by
    let g3 : Fin n → ℝ := fun i ↦ ∫ ω, |X i ω| ^ 3 ∂P
    let domA : Ω → ℝ := fun ω ↦
      (1 / σ ^ 3) * ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, |X i ω| * |X j ω| * |X k ω|
    have hA_pt (ω : Ω) : |A ω| ≤ domA ω := by
      dsimp only [A, domA]
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hσ_pos)]
      calc (1 / σ) * |∑ i : Fin n, T_i i ω|
          ≤ (1 / σ) * ∑ i : Fin n, |T_i i ω| :=
            mul_le_mul_of_nonneg_left
              (Finset.abs_sum_le_sum_abs (fun i ↦ T_i i ω) Finset.univ) (by positivity)
        _ ≤ (1 / σ) * ∑ i : Fin n,
              (1 / σ ^ 2) * ∑ j ∈ N i, ∑ k ∈ N i, |X i ω| * |X j ω| * |X k ω| :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hTi_bound i ω) (by positivity)
        _ = (1 / σ ^ 3) *
              ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, |X i ω| * |X j ω| * |X k ω| := by
            rw [← Finset.mul_sum]
            simp only [one_div, ← inv_pow]
            ring
    have hint_domA : Integrable domA P :=
      (integrable_finsetSum Finset.univ fun i _ ↦ hint_dom_i i).const_mul (1 / σ ^ 3)
    have h1 : |∫ ω, A ω ∂P| ≤ ∫ ω, domA ω ∂P :=
      abs_integral_le_integral_abs.trans (integral_mono hint_A.abs hint_domA hA_pt)
    have h2 : ∫ ω, domA ω ∂P =
        (1 / σ ^ 3) * ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i,
          ∫ ω, |X i ω| * |X j ω| * |X k ω| ∂P := by
      dsimp only [domA]
      rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ ↦ hint_dom_i i]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum (N i) fun j _ ↦
        integrable_finsetSum (N i) fun k _ ↦ integrable_abs_mul_three (hX4 i) (hX4 j) (hX4 k)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      exact integral_finsetSum (N i) fun k _ ↦ integrable_abs_mul_three (hX4 i) (hX4 j) (hX4 k)
    have hijk (i j k : Fin n) :
        (∫ ω, |X i ω| * |X j ω| * |X k ω| ∂P) ≤ (g3 i + g3 j + g3 k) / 3 := by
      have hdom3 : Integrable (fun ω ↦ (|X i ω| ^ 3 + |X j ω| ^ 3 + |X k ω| ^ 3) / 3) P :=
        (((integrable_abs_pow_three (hX4 i)).fun_add (integrable_abs_pow_three (hX4 j))).fun_add
          (integrable_abs_pow_three (hX4 k))).div_const 3
      have hm := integral_mono (integrable_abs_mul_three (hX4 i) (hX4 j) (hX4 k)) hdom3
        fun ω ↦ abs_mul_three_le (X i ω) (X j ω) (X k ω)
      have hev : (∫ ω, (|X i ω| ^ 3 + |X j ω| ^ 3 + |X k ω| ^ 3) / 3 ∂P) =
          (g3 i + g3 j + g3 k) / 3 := by
        rw [integral_div, integral_add
          ((integrable_abs_pow_three (hX4 i)).fun_add (integrable_abs_pow_three (hX4 j)))
          (integrable_abs_pow_three (hX4 k)),
          integral_add (integrable_abs_pow_three (hX4 i)) (integrable_abs_pow_three (hX4 j))]
      exact hm.trans_eq hev
    have h3 : (∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, ∫ ω, |X i ω| * |X j ω| * |X k ω| ∂P) ≤
        D ^ 2 * ∑ i : Fin n, g3 i := by
      calc ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, ∫ ω, |X i ω| * |X j ω| * |X k ω| ∂P
          ≤ ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, (g3 i + g3 j + g3 k) / 3 :=
            Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
              Finset.sum_le_sum fun k _ ↦ hijk i j k
        _ ≤ D ^ 2 * ∑ i : Fin n, g3 i :=
            sum_triple_dep_amgm_le hG.2.1 fun i ↦ integral_nonneg fun ω ↦ by positivity
    calc |∫ ω, A ω ∂P|
        ≤ (1 / σ ^ 3) * ∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i,
            ∫ ω, |X i ω| * |X j ω| * |X k ω| ∂P := h1.trans_eq h2
      _ ≤ (1 / σ ^ 3) * (D ^ 2 * ∑ i : Fin n, g3 i) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = D ^ 2 / σ ^ 3 * ∑ i : Fin n, g3 i := by ring
  have hB_le : |∫ ω, B ω ∂P| ≤
      Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
        Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) := by
    let M4 : ℝ := ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P
    have h1 : |∫ ω, B ω ∂P| ≤
        (Real.sqrt (2 / Real.pi) / σ ^ 2) * ∫ ω, |σ ^ 2 - S ω| ∂P := by
      have hm := abs_integral_le_integral_abs.trans
        (integral_mono hint_B.abs
          (h_diff_int.const_mul (Real.sqrt (2 / Real.pi) / σ ^ 2)) hB_bound_pt)
      rwa [integral_const_mul] at hm
    have hS_mean : ∫ ω, S ω ∂P = σ ^ 2 :=
      (depGraph_integral_quadSum_eq_variance P hX_meas hX4 hX0 hG).trans hσ_sq.symm
    have h_l1_var : ∫ ω, |σ ^ 2 - S ω| ∂P ≤ Real.sqrt (ProbabilityTheory.variance S P) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hcs := sq_integral_le_integral_sq h_diff_lp2
      have hsq_eq : (fun ω ↦ |σ ^ 2 - S ω| ^ 2) = fun ω ↦ (S ω - ∫ ω', S ω' ∂P) ^ 2 := by
        ext ω
        rw [sq_abs, hS_mean]
        ring
      rwa [hsq_eq, ← ProbabilityTheory.variance_eq_integral hS_memLp2.aemeasurable] at hcs
    have h_var_le : Real.sqrt (ProbabilityTheory.variance S P) ≤
        Real.sqrt (13 * D ^ 3 * M4) :=
      Real.sqrt_le_sqrt (depGraph_variance_quadSum_le P hX_meas hX4 hG)
    have hsqrt_D3 : Real.sqrt (D ^ 3) = D ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul hD_nonneg 3 (1 / (2 : ℝ))]
      congr 1
      norm_num
    have hsqrt_26 : Real.sqrt 2 * Real.sqrt 13 = Real.sqrt 26 := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2) 13]
      norm_num
    have h13D3_nonneg : 0 ≤ 13 * D ^ 3 := by positivity
    calc |∫ ω, B ω ∂P|
        ≤ (Real.sqrt (2 / Real.pi) / σ ^ 2) * ∫ ω, |σ ^ 2 - S ω| ∂P := h1
      _ ≤ (Real.sqrt (2 / Real.pi) / σ ^ 2) * Real.sqrt (13 * D ^ 3 * M4) :=
          mul_le_mul_of_nonneg_left (h_l1_var.trans h_var_le) (by positivity)
      _ = (Real.sqrt 2 / Real.sqrt Real.pi / σ ^ 2) *
            ((Real.sqrt 13 * D ^ (3 / 2 : ℝ)) * Real.sqrt M4) := by
          rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2) Real.pi,
            Real.sqrt_mul h13D3_nonneg M4,
            Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 13) (D ^ 3), hsqrt_D3]
      _ = (Real.sqrt 2 * Real.sqrt 13) * D ^ (3 / 2 : ℝ) /
            (Real.sqrt Real.pi * σ ^ 2) * Real.sqrt M4 := by
          rw [div_div]
          ring
      _ = Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) * Real.sqrt M4 := by
          rw [hsqrt_26]
  calc |∫ ω, normalSteinOp f (W ω) ∂P|
      = |-(∫ ω, A ω ∂P) + ∫ ω, B ω ∂P| := by rw [h_decomp]
    _ ≤ |-(∫ ω, A ω ∂P)| + |∫ ω, B ω ∂P| := abs_add_le _ _
    _ = |∫ ω, A ω ∂P| + |∫ ω, B ω ∂P| := by rw [abs_neg]
    _ ≤ D ^ 2 / σ ^ 3 * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) := add_le_add hA_le hB_le

end SteinMethod
