/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Leftovers.OUUniqueness

/-!
# Ornstein–Uhlenbeck Semigroup Uniqueness Under Ross's Printed Probability Tail
(`Formalization.Leftovers.OUProbTail`)

Resolves open obligation `BL8-2` of Remark 3.5 (`SteinIntro.tex:1009-1024`):
proves that Ross's literally printed **probability tail** condition (Item 3, `L1016`)
$$\forall x \in \mathbb{R},\;\forall \varepsilon > 0,\quad
  \lim_{a \to 0^+} \frac{\mathbb{P}(|D(t + a) - D(t)| > \varepsilon \mid D(t) = x)}{a} = 0$$
already suffices — without assuming the stronger Lindeberg second-moment tail — to uniquely
determine the Ornstein–Uhlenbeck transition semigroup `ouKernel` among Chapman–Kolmogorov Markov
semigroups under Remark 3.5 Items 1–2 and small-time quadratic moment domination (`QuadDom`).

Main results:
* `eq_ouKernel_of_probTail`: `K t = ouKernel t` for all `t > 0` under Chapman–Kolmogorov,
  Markov property, printed Items 1–3, and `QuadDom`.
* `lindeberg_tail_of_probTail_semigroup`: automatic upgrade from the printed probability tail
  (Item 3) to the Lindeberg second-moment tail for Chapman–Kolmogorov Markov semigroups.
* `eq_stdNormalLaw_of_bind_probTail`: moment-free stationary-law uniqueness (`μ = stdNormalLaw`)
  under the printed Item 3 hypothesis.
* `rem3_5_uniqueness_probTail_proof`: complete Remark 3.5 uniqueness bundle with Part 3 upgraded
  to Ross's printed probability-tail condition.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

open OUUniquenessAux

/-! ### Section 1: Elementary Real & Right-Hand Slope Comparison Helpers -/

namespace OUProbTailAux

lemma nonneg_of_hasDerivAt_nonneg (g g' : ℝ → ℝ) (hg0 : g 0 = 0)
    (hg : ∀ v : ℝ, HasDerivAt g (g' v) v) (hnn : ∀ v : ℝ, 0 ≤ v → 0 ≤ g' v)
    {u : ℝ} (hu : 0 ≤ u) : 0 ≤ g u := by
  rcases eq_or_lt_of_le hu with rfl | hu_pos
  · simp [hg0]
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' hu_pos
      (fun v _ ↦ (hg v).continuousAt.continuousWithinAt)
      (fun v _ ↦ hg v)
    rw [hg0, sub_zero, sub_zero, eq_div_iff hu_pos.ne'] at hslope
    nlinarith [hnn c hc.1.le]

lemma monotone_of_hasDerivAt_nonneg_all {g g' : ℝ → ℝ}
    (hg : ∀ v : ℝ, HasDerivAt g (g' v) v) (hnn : ∀ v : ℝ, 0 ≤ g' v) : Monotone g := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · obtain ⟨c, -, hslope⟩ := exists_hasDerivAt_eq_slope g g' hlt
      (fun v _ ↦ (hg v).continuousAt.continuousWithinAt)
      (fun v _ ↦ hg v)
    have hpos : 0 < y - x := sub_pos.mpr hlt
    rw [eq_div_iff hpos.ne'] at hslope
    nlinarith [hnn c]

lemma one_add_add_half_sq_le_exp {u : ℝ} (hu : 0 ≤ u) :
    1 + u + u ^ 2 / 2 ≤ Real.exp u := by
  suffices h : 0 ≤ Real.exp u - (1 + u + u ^ 2 / 2) by linarith
  refine nonneg_of_hasDerivAt_nonneg (fun w ↦ Real.exp w - (1 + w + w ^ 2 / 2))
    (fun v ↦ Real.exp v - (1 + v)) (by simp) (fun v ↦ ?_)
    (fun v _ ↦ by linarith [Real.add_one_le_exp v]) hu
  have hsq : HasDerivAt (fun w : ℝ ↦ w ^ 2 / 2) v v := by
    simpa only [sub_zero] using ((hasDerivAt_sq_sub 0 v).div_const (2 : ℝ)).congr_deriv (by ring)
  have hpoly : HasDerivAt (fun w : ℝ ↦ 1 + w + w ^ 2 / 2) (1 + v) v :=
    (((hasDerivAt_id' v).const_add 1).add hsq).congr_deriv (by ring)
  exact (Real.hasDerivAt_exp v).sub hpoly

lemma exp_neg_sub_one_add_le_half_sq {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) - 1 + u ≤ u ^ 2 / 2 := by
  suffices h : 0 ≤ u ^ 2 / 2 - (Real.exp (-u) - 1 + u) by linarith
  refine nonneg_of_hasDerivAt_nonneg (fun w ↦ w ^ 2 / 2 - (Real.exp (-w) - 1 + w))
    (fun v ↦ v + Real.exp (-v) - 1) (by simp) (fun v ↦ ?_)
    (fun v _ ↦ by linarith [Real.add_one_le_exp (-v)]) hu
  have hsq : HasDerivAt (fun w : ℝ ↦ w ^ 2 / 2) v v := by
    simpa only [sub_zero] using ((hasDerivAt_sq_sub 0 v).div_const (2 : ℝ)).congr_deriv (by ring)
  have hneg : HasDerivAt (fun w : ℝ ↦ -w) (-1) v := (hasDerivAt_id' v).neg
  have hexp : HasDerivAt (fun w : ℝ ↦ Real.exp (-w) - 1 + w) (-Real.exp (-v) + 1) v :=
    (((hneg.exp).sub_const 1).add (hasDerivAt_id' v)).congr_deriv (by ring)
  exact (hsq.sub hexp).congr_deriv (by ring)

lemma mul_exp_neg_le_one {u : ℝ} (_hu : 0 ≤ u) : u * Real.exp (-u) ≤ 1 := by
  have h1 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  calc u * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-u)).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

lemma sq_mul_exp_neg_le_two {u : ℝ} (hu : 0 ≤ u) : u ^ 2 * Real.exp (-u) ≤ 2 := by
  have h1 : u ^ 2 ≤ 2 * Real.exp u := by linarith [one_add_add_half_sq_le_exp hu]
  calc u ^ 2 * Real.exp (-u) ≤ (2 * Real.exp u) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-u)).le
    _ = 2 := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

lemma abs_mul_exp_neg_sq_le_half (v : ℝ) : |v| * Real.exp (-(v ^ 2)) ≤ 1 / 2 := by
  have h1 : 2 * |v| ≤ 1 + v ^ 2 := by nlinarith [sq_nonneg (|v| - 1), sq_abs v]
  have h2 : 1 + v ^ 2 ≤ Real.exp (v ^ 2) := by
    linarith [Real.add_one_le_exp (v ^ 2)]
  calc |v| * Real.exp (-(v ^ 2))
    _ ≤ (Real.exp (v ^ 2) / 2) * Real.exp (-(v ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le; linarith
    _ = 1 / 2 := by
        rw [div_mul_eq_mul_div, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Elementary right-hand upper Dini slope comparison on `[0, t]`: if `F` is continuous on `[0, t]`
and at every `s ∈ [0, t)` its forward difference quotient `(F (s + a) - F s) / a` is bounded above
by a quantity tending to `0` as `a → 0⁺`, then `F t ≤ F 0`. -/
lemma le_of_eventually_slope_right_le_tendsto_zero {F : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hF_cont : ContinuousOn F (Icc 0 t))
    (hslope : ∀ s ∈ Ico 0 t, ∃ R : ℝ → ℝ, Tendsto R (𝓝[>] 0) (𝓝 0) ∧
      ∀ᶠ a in 𝓝[>] 0, (F (s + a) - F s) / a ≤ R a) :
    F t ≤ F 0 := by
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  set η : ℝ := ε / (t + 1)
  have hη : 0 < η := by positivity
  suffices hFt : F t ≤ F 0 + η * t by
    have hlt : η * t < ε := by
      rw [show η * t = ε * (t / (t + 1)) by dsimp [η]; ring]
      exact mul_lt_of_lt_one_right hε ((div_lt_one (by positivity)).mpr (by linarith))
    linarith
  set G : ℝ → ℝ := fun u ↦ F u - F 0 - η * u
  have hG_cont : ContinuousOn G (Icc 0 t) :=
    (hF_cont.sub continuousOn_const).sub (continuous_const.mul continuous_id).continuousOn
  have hG0 : G 0 = 0 := by simp [G]
  set S : Set ℝ := {s ∈ Icc 0 t | ∀ u ∈ Icc 0 s, G u ≤ 0}
  have h0S : (0 : ℝ) ∈ S :=
    ⟨⟨le_rfl, ht⟩, fun u hu ↦ by rw [le_antisymm hu.2 hu.1, hG0]⟩
  have hS_bdd : BddAbove S := ⟨t, fun s hs ↦ hs.1.2⟩
  set sStar : ℝ := sSup S
  have hsStar_ge : 0 ≤ sStar := le_csSup hS_bdd h0S
  have hsStar_le : sStar ≤ t := csSup_le ⟨0, h0S⟩ fun s hs ↦ hs.1.2
  have h_lt_mem : ∀ u : ℝ, 0 ≤ u → u < sStar → G u ≤ 0 := fun u hu0 hult ↦ by
    obtain ⟨s, hsS, hus⟩ := (lt_csSup_iff hS_bdd ⟨0, h0S⟩).mp hult
    exact hsS.2 u ⟨hu0, hus.le⟩
  have hsStar_G : G sStar ≤ 0 := by
    rcases eq_or_lt_of_le hsStar_ge with h0 | hs_pos
    · rw [← h0, hG0]
    · refine le_of_forall_pos_lt_add fun δ₀ hδ₀ ↦ ?_
      obtain ⟨δ, hδ_pos, hδ⟩ :=
        Metric.continuousOn_iff.mp hG_cont sStar ⟨hsStar_ge, hsStar_le⟩ δ₀ hδ₀
      set v : ℝ := max 0 (sStar - δ / 2)
      have hv_mem : v ∈ Icc 0 t :=
        ⟨le_max_left _ _, (max_le hsStar_ge (by linarith)).trans hsStar_le⟩
      have hv_lt : v < sStar := max_lt hs_pos (by linarith)
      have hv_dist : dist v sStar < δ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hv_lt)]
        linarith [le_max_right (0 : ℝ) (sStar - δ / 2)]
      have hGv : G v ≤ 0 := h_lt_mem v (le_max_left _ _) hv_lt
      have hc := hδ v hv_mem hv_dist
      rw [Real.dist_eq] at hc
      linarith [(abs_lt.mp hc).1]
  have hsStar_mem : sStar ∈ S := ⟨⟨hsStar_ge, hsStar_le⟩, fun u hu ↦ by
    rcases lt_or_eq_of_le hu.2 with hlt | rfl
    · exact h_lt_mem u hu.1 hlt
    · exact hsStar_G⟩
  have hsStar_eq : sStar = t := by
    by_contra hne
    have hlt_t : sStar < t := lt_of_le_of_ne hsStar_le hne
    obtain ⟨R, hR_lim, hR_ev⟩ := hslope sStar ⟨hsStar_ge, hlt_t⟩
    have hev : ∀ᶠ a in 𝓝[>] 0, (F (sStar + a) - F sStar) / a < η := by
      filter_upwards [hR_ev, (Metric.tendsto_nhds.mp hR_lim) (η / 2) (half_pos hη)] with a ha1 ha2
      rw [Real.dist_eq, sub_zero] at ha2
      linarith [(abs_lt.mp ha2).2]
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hev
    set step : ℝ := min (δ / 2) (t - sStar)
    have hstep_pos : 0 < step := lt_min (half_pos hδ_pos) (sub_pos.mpr hlt_t)
    have h_next : sStar + step ∈ S := by
      refine ⟨⟨by linarith, by linarith [min_le_right (δ / 2) (t - sStar)]⟩,
        fun u hu ↦ ?_⟩
      rcases le_or_gt u sStar with hle | hgt
      · exact hsStar_mem.2 u ⟨hu.1, hle⟩
      · set a : ℝ := u - sStar
        have ha_pos : 0 < a := sub_pos.mpr hgt
        have ha_lt_δ : a ∈ Metric.ball 0 δ := by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha_pos]
          have h1 : a ≤ step := by dsimp [a]; linarith [hu.2]
          linarith [min_le_left (δ / 2) (t - sStar)]
        have hquot : (F (sStar + a) - F sStar) / a < η := hδ ⟨ha_lt_δ, ha_pos⟩
        rw [div_lt_iff₀ ha_pos, show sStar + a = u by dsimp [a]; ring] at hquot
        have hGu : G u = G sStar + (F u - F sStar - η * (u - sStar)) := by dsimp [G]; ring
        linarith
    linarith [le_csSup hS_bdd h_next]
  rw [hsStar_eq] at hsStar_G
  dsimp [G] at hsStar_G
  linarith

/-! ### Section 2: Smooth Convex Tail-Excess Function & Bregman Divergence -/

/-- Bounded smooth truncation `M^2 (1 - exp(-y^2 / M^2))` of `y^2`. -/
noncomputable def truncSq (M y : ℝ) : ℝ :=
  M ^ 2 * (1 - Real.exp (-(y ^ 2 / M ^ 2)))

/-- Smooth convex tail excess `y^2 - M^2 (1 - exp(-y^2 / M^2))`. -/
noncomputable def tailExcess (M y : ℝ) : ℝ :=
  y ^ 2 - truncSq M y

/-- First derivative of `tailExcess M`. -/
noncomputable def tailExcessDeriv (M y : ℝ) : ℝ :=
  2 * y * (1 - Real.exp (-(y ^ 2 / M ^ 2)))

/-- Second derivative of `tailExcess M`. -/
noncomputable def tailExcessDeriv2 (M y : ℝ) : ℝ :=
  2 * (1 - (1 - 2 * (y ^ 2 / M ^ 2)) * Real.exp (-(y ^ 2 / M ^ 2)))

/-- Nonnegative Bregman divergence of the convex function `tailExcess M`. -/
noncomputable def bregmanExcess (M y z : ℝ) : ℝ :=
  tailExcess M z - tailExcess M y - tailExcessDeriv M y * (z - y)

/-- Drift-excess auxiliary `y * tailExcessDeriv M y = 2 y^2 (1 - exp(-y^2 / M^2))`. -/
noncomputable def driftExcess (M y : ℝ) : ℝ :=
  y * tailExcessDeriv M y

/-- First derivative of `driftExcess M`. -/
noncomputable def driftExcessDeriv (M y : ℝ) : ℝ :=
  tailExcessDeriv M y + y * tailExcessDeriv2 M y

/-- Second derivative of `driftExcess M`. -/
noncomputable def driftExcessDeriv2 (M y : ℝ) : ℝ :=
  4 + (-4 + 20 * (y ^ 2 / M ^ 2) - 8 * (y ^ 2 / M ^ 2) ^ 2) * Real.exp (-(y ^ 2 / M ^ 2))

lemma hasDerivAt_exp_neg_div_sq (M y : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-(v ^ 2 / M ^ 2)))
      (-(2 * y / M ^ 2) * Real.exp (-(y ^ 2 / M ^ 2))) y := by
  have hsq : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * y) y := by
    simpa only [sub_zero] using hasDerivAt_sq_sub 0 y
  have hn : HasDerivAt (fun v : ℝ ↦ -(v ^ 2 / M ^ 2)) (-(2 * y / M ^ 2)) y :=
    (hsq.div_const (M ^ 2)).neg
  exact hn.exp.congr_deriv (by ring)

lemma hasDerivAt_tailExcess {M : ℝ} (hM : 0 < M) (y : ℝ) :
    HasDerivAt (tailExcess M) (tailExcessDeriv M y) y := by
  have hsq : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * y) y := by
    simpa only [sub_zero] using hasDerivAt_sq_sub 0 y
  have htr : HasDerivAt (truncSq M) (2 * y * Real.exp (-(y ^ 2 / M ^ 2))) y := by
    unfold truncSq
    refine (((hasDerivAt_exp_neg_div_sq M y).const_sub 1).const_mul (M ^ 2)).congr_deriv ?_
    have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM.ne'
    field_simp [hM2]
  exact (hsq.sub htr).congr_deriv (by unfold tailExcessDeriv; ring)

lemma hasDerivAt_tailExcessDeriv (M y : ℝ) :
    HasDerivAt (tailExcessDeriv M) (tailExcessDeriv2 M y) y := by
  unfold tailExcessDeriv tailExcessDeriv2
  have h1 : HasDerivAt (fun v : ℝ ↦ 2 * v) 2 y := by
    simpa using (hasDerivAt_id' y).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun v : ℝ ↦ 1 - Real.exp (-(v ^ 2 / M ^ 2)))
      ((2 * y / M ^ 2) * Real.exp (-(y ^ 2 / M ^ 2))) y := by
    exact ((hasDerivAt_exp_neg_div_sq M y).const_sub 1).congr_deriv (by ring)
  exact (h1.fun_mul h2).congr_deriv (by ring)

lemma hasDerivAt_tailExcessDeriv2 {M : ℝ} (hM : 0 < M) (y : ℝ) :
    HasDerivAt (tailExcessDeriv2 M)
      ((4 * y / M ^ 2) * (3 - 2 * (y ^ 2 / M ^ 2)) * Real.exp (-(y ^ 2 / M ^ 2))) y := by
  unfold tailExcessDeriv2
  have hsq : HasDerivAt (fun v : ℝ ↦ v ^ 2 / M ^ 2) (2 * y / M ^ 2) y := by
    have h0 : HasDerivAt (fun v : ℝ ↦ v ^ 2) (2 * y) y := by
      simpa only [sub_zero] using hasDerivAt_sq_sub 0 y
    exact h0.div_const (M ^ 2)
  have hlin : HasDerivAt (fun v : ℝ ↦ 1 - 2 * (v ^ 2 / M ^ 2)) (-(4 * y / M ^ 2)) y :=
    ((hsq.const_mul 2).const_sub 1).congr_deriv (by ring)
  have hprod := hlin.fun_mul (hasDerivAt_exp_neg_div_sq M y)
  refine ((hprod.const_sub 1).const_mul 2).congr_deriv ?_
  have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM.ne'
  field_simp [hM2]; ring

lemma hasDerivAt_driftExcess (M y : ℝ) :
    HasDerivAt (driftExcess M) (driftExcessDeriv M y) y := by
  unfold driftExcess driftExcessDeriv
  exact ((hasDerivAt_id' y).fun_mul (hasDerivAt_tailExcessDeriv M y)).congr_deriv (by ring)

lemma hasDerivAt_driftExcessDeriv {M : ℝ} (hM : 0 < M) (y : ℝ) :
    HasDerivAt (driftExcessDeriv M) (driftExcessDeriv2 M y) y := by
  unfold driftExcessDeriv driftExcessDeriv2
  have h1 := hasDerivAt_tailExcessDeriv M y
  have h2 := (hasDerivAt_id' y).fun_mul (hasDerivAt_tailExcessDeriv2 hM y)
  refine (h1.add h2).congr_deriv ?_
  unfold tailExcessDeriv2
  have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM.ne'
  field_simp [hM2]; ring

lemma tailExcess_bounds {M : ℝ} (hM : 0 < M) (y : ℝ) :
    0 ≤ tailExcess M y ∧ tailExcess M y ≤ y ^ 2 ∧
      tailExcess M y ≤ y ^ 4 / (2 * M ^ 2) := by
  set u : ℝ := y ^ 2 / M ^ 2
  have hu : 0 ≤ u := by positivity
  have hEq : tailExcess M y = M ^ 2 * (Real.exp (-u) - 1 + u) := by
    unfold tailExcess truncSq; dsimp [u]
    have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM.ne'
    field_simp [hM2]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]
    exact mul_nonneg (sq_nonneg M) (by linarith [Real.add_one_le_exp (-u)])
  · unfold tailExcess truncSq
    have hexp_le : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have htr_nn : 0 ≤ M ^ 2 * (1 - Real.exp (-u)) := mul_nonneg (sq_nonneg M) (by linarith)
    dsimp [u] at htr_nn; linarith
  · rw [hEq]
    calc M ^ 2 * (Real.exp (-u) - 1 + u)
      _ ≤ M ^ 2 * (u ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (exp_neg_sub_one_add_le_half_sq hu) (sq_nonneg M)
      _ = y ^ 4 / (2 * M ^ 2) := by
          dsimp [u]; have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM.ne'; field_simp [hM2]

lemma abs_tailExcessDeriv_le (M y : ℝ) : |tailExcessDeriv M y| ≤ 2 * |y| := by
  unfold tailExcessDeriv
  have hu : 0 ≤ y ^ 2 / M ^ 2 := by positivity
  have h0 : 0 ≤ 1 - Real.exp (-(y ^ 2 / M ^ 2)) := by
    linarith [Real.exp_le_one_iff.mpr (by linarith : -(y ^ 2 / M ^ 2) ≤ 0)]
  have h1 : 1 - Real.exp (-(y ^ 2 / M ^ 2)) ≤ 1 := by linarith [Real.exp_pos (-(y ^ 2 / M ^ 2))]
  rw [abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg h0]
  nlinarith [abs_nonneg y]

lemma tailExcessDeriv2_bounds (M y : ℝ) :
    0 ≤ tailExcessDeriv2 M y ∧ tailExcessDeriv2 M y ≤ 6 := by
  unfold tailExcessDeriv2
  set u : ℝ := y ^ 2 / M ^ 2
  have hu : 0 ≤ u := by positivity
  have hexp_pos : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have hexp_le : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  constructor
  · rcases le_or_gt (1 / 2 : ℝ) u with hge | hlt
    · have hnp : (1 - 2 * u) * Real.exp (-u) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hexp_pos.le
      linarith
    · have hle1 : (1 - 2 * u) * Real.exp (-u) ≤ 1 :=
        (mul_le_of_le_one_right (by linarith) hexp_le).trans (by linarith)
      linarith
  · have hbound : -((1 - 2 * u) * Real.exp (-u)) ≤ 2 := by
      have h1 := mul_exp_neg_le_one hu
      nlinarith
    linarith

lemma bregmanExcess_nonneg_and_le {M : ℝ} (hM : 0 < M) (y z : ℝ) :
    0 ≤ bregmanExcess M y z ∧ bregmanExcess M y z ≤ 6 * (z - y) ^ 2 := by
  have hmono : Monotone (tailExcessDeriv M) :=
    monotone_of_hasDerivAt_nonneg_all (hasDerivAt_tailExcessDeriv M)
      (fun v ↦ (tailExcessDeriv2_bounds M v).1)
  have hβ_deriv : ∀ u : ℝ,
      HasDerivAt (fun w ↦ bregmanExcess M y w) (tailExcessDeriv M u - tailExcessDeriv M y) u :=
    fun u ↦ by
      unfold bregmanExcess
      have hlin : HasDerivAt (fun w ↦ tailExcessDeriv M y * (w - y)) (tailExcessDeriv M y) u :=
        (((hasDerivAt_id' u).sub_const y).const_mul (tailExcessDeriv M y)).congr_deriv (by ring)
      exact ((hasDerivAt_tailExcess hM u).sub_const (tailExcess M y)).sub hlin
  have hb0 : bregmanExcess M y y = 0 := by unfold bregmanExcess; ring
  have hnn_b : 0 ≤ bregmanExcess M y z := by
    rcases lt_trichotomy y z with hlt | rfl | hgt
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun w ↦ bregmanExcess M y w)
        (fun u ↦ tailExcessDeriv M u - tailExcessDeriv M y) hlt
        (fun u _ ↦ (hβ_deriv u).continuousAt.continuousWithinAt)
        (fun u _ ↦ hβ_deriv u)
      rw [hb0, sub_zero, eq_div_iff (sub_pos.mpr hlt).ne'] at hslope
      nlinarith [hmono hc.1.le]
    · simp [hb0]
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun w ↦ bregmanExcess M y w)
        (fun u ↦ tailExcessDeriv M u - tailExcessDeriv M y) hgt
        (fun u _ ↦ (hβ_deriv u).continuousAt.continuousWithinAt)
        (fun u _ ↦ hβ_deriv u)
      rw [hb0, zero_sub, eq_div_iff (sub_pos.mpr hgt).ne'] at hslope
      nlinarith [hmono hc.2.le]
  refine ⟨hnn_b, ?_⟩
  have hd_lip : ∀ u : ℝ, |u - y| ≤ |z - y| →
      |tailExcessDeriv M u - tailExcessDeriv M y| ≤ 6 * |z - y| := fun u hu ↦ by
    have h1 := norm_sub_le_of_hasDerivAt_ball (x := y) (y := u) (C := 6)
      (hasDerivAt_tailExcessDeriv M) fun w _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (tailExcessDeriv2_bounds M w).1]
        exact (tailExcessDeriv2_bounds M w).2
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hu (by norm_num))
  have h2 := norm_sub_le_of_hasDerivAt_ball (x := y) (y := z) (C := 6 * |z - y|) hβ_deriv
    fun u hu ↦ by simpa [Real.norm_eq_abs] using hd_lip u hu
  rw [hb0, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn_b] at h2
  exact h2.trans_eq (by rw [mul_assoc, ← sq, sq_abs])

lemma sq_sub_le_four_mul_bregmanExcess {M : ℝ} (hM : 0 < M) {y z : ℝ}
    (hfar : 2 * M ≤ |z - y|) :
    (z - y) ^ 2 ≤ 4 * bregmanExcess M y z := by
  have hrewrite : bregmanExcess M y z =
      (z - y) ^ 2 - (truncSq M z - truncSq M y) +
        (2 * y * Real.exp (-(y ^ 2 / M ^ 2))) * (z - y) := by
    unfold bregmanExcess tailExcess tailExcessDeriv; ring
  have htr_z : truncSq M z ≤ M ^ 2 := by
    unfold truncSq
    have hexp_pos : 0 < Real.exp (-(z ^ 2 / M ^ 2)) := Real.exp_pos _
    nlinarith [sq_nonneg M]
  have htr_y : 0 ≤ truncSq M y := by
    unfold truncSq
    have hexp_le : Real.exp (-(y ^ 2 / M ^ 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    exact mul_nonneg (sq_nonneg M) (by linarith)
  have hpsi_deriv : |2 * y * Real.exp (-(y ^ 2 / M ^ 2))| ≤ M := by
    have hv := abs_mul_exp_neg_sq_le_half (y / M)
    rw [abs_div, abs_of_pos hM, div_pow] at hv
    rw [abs_mul, abs_mul, abs_of_pos zero_lt_two, abs_of_pos (Real.exp_pos _)]
    have hmul := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * M)
    have hlhs : 2 * M * (|y| / M * Real.exp (-(y ^ 2 / M ^ 2))) =
        2 * |y| * Real.exp (-(y ^ 2 / M ^ 2)) := by field_simp [hM.ne']
    linarith
  have hprod : |(2 * y * Real.exp (-(y ^ 2 / M ^ 2))) * (z - y)| ≤
      (z - y) ^ 2 / 4 + M ^ 2 := by
    rw [abs_mul]
    have h1 : |2 * y * Real.exp (-(y ^ 2 / M ^ 2))| * |z - y| ≤ M * |z - y| :=
      mul_le_mul_of_nonneg_right hpsi_deriv (abs_nonneg _)
    nlinarith [sq_nonneg (|z - y| / 2 - M), sq_abs (z - y)]
  have hfar_sq : 4 * M ^ 2 ≤ (z - y) ^ 2 := by
    have h1 := pow_le_pow_left₀ (by positivity) hfar 2
    rw [sq_abs] at h1; linarith
  have hlow : (z - y) ^ 2 - M ^ 2 - ((z - y) ^ 2 / 4 + M ^ 2) ≤ bregmanExcess M y z := by
    rw [hrewrite]; linarith [neg_abs_le ((2 * y * Real.exp (-(y ^ 2 / M ^ 2))) * (z - y))]
  linarith

lemma driftExcess_bounds {M : ℝ} (_hM : 0 < M) (y : ℝ) :
    0 ≤ driftExcess M y ∧ driftExcess M y ≤ 2 * y ^ 2 ∧
      driftExcess M y ≤ 2 * y ^ 4 / M ^ 2 ∧
      |driftExcessDeriv M y| ≤ 8 * |y| := by
  have hform : driftExcess M y = 2 * y ^ 2 * (1 - Real.exp (-(y ^ 2 / M ^ 2))) := by
    unfold driftExcess tailExcessDeriv; ring
  have hexp_pos : 0 < Real.exp (-(y ^ 2 / M ^ 2)) := Real.exp_pos _
  have hexp_le : Real.exp (-(y ^ 2 / M ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  refine ⟨by rw [hform]; exact mul_nonneg (by positivity) (by linarith),
    by rw [hform]; nlinarith [sq_nonneg y], ?_, ?_⟩
  · rw [hform]
    have hsub : 1 - Real.exp (-(y ^ 2 / M ^ 2)) ≤ y ^ 2 / M ^ 2 := by
      linarith [Real.add_one_le_exp (-(y ^ 2 / M ^ 2))]
    calc 2 * y ^ 2 * (1 - Real.exp (-(y ^ 2 / M ^ 2)))
      _ ≤ 2 * y ^ 2 * (y ^ 2 / M ^ 2) := mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = 2 * y ^ 4 / M ^ 2 := by ring
  · unfold driftExcessDeriv
    have h1 := abs_tailExcessDeriv_le M y
    have h2_nn := (tailExcessDeriv2_bounds M y).1
    have h2_le := (tailExcessDeriv2_bounds M y).2
    have hy2 : |y * tailExcessDeriv2 M y| ≤ 6 * |y| := by
      rw [abs_mul, abs_of_nonneg h2_nn]; nlinarith [abs_nonneg y]
    linarith [abs_add_le (tailExcessDeriv M y) (y * tailExcessDeriv2 M y)]

lemma abs_driftExcessDeriv2_le (M y : ℝ) : |driftExcessDeriv2 M y| ≤ 44 := by
  unfold driftExcessDeriv2
  set u : ℝ := y ^ 2 / M ^ 2
  have hu : 0 ≤ u := by positivity
  have hexp_pos : 0 < Real.exp (-u) := Real.exp_pos (-u)
  have hexp_le : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h1 := mul_exp_neg_le_one hu
  have h2 := sq_mul_exp_neg_le_two hu
  rw [abs_le]
  constructor <;> nlinarith

lemma abs_driftExcess_taylor_le {M : ℝ} (hM : 0 < M) (y z : ℝ) :
    |driftExcess M z - driftExcess M y - driftExcessDeriv M y * (z - y)| ≤
      44 * (z - y) ^ 2 := by
  have hd_lip : ∀ u : ℝ, |u - y| ≤ |z - y| →
      |driftExcessDeriv M u - driftExcessDeriv M y| ≤ 44 * |z - y| := fun u hu ↦ by
    have h1 := norm_sub_le_of_hasDerivAt_ball (x := y) (y := u) (C := 44)
      (hasDerivAt_driftExcessDeriv hM) fun w _ ↦ by
        simpa [Real.norm_eq_abs] using abs_driftExcessDeriv2_le M w
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hu (by norm_num))
  set R : ℝ → ℝ := fun w ↦
    driftExcess M w - driftExcess M y - driftExcessDeriv M y * (w - y)
  have hR_deriv : ∀ u : ℝ, HasDerivAt R (driftExcessDeriv M u - driftExcessDeriv M y) u :=
    fun u ↦ by
      have hlin : HasDerivAt (fun w ↦ driftExcessDeriv M y * (w - y)) (driftExcessDeriv M y) u :=
        (((hasDerivAt_id' u).sub_const y).const_mul (driftExcessDeriv M y)).congr_deriv (by ring)
      exact ((hasDerivAt_driftExcess M u).sub_const (driftExcess M y)).sub hlin
  have h2 := norm_sub_le_of_hasDerivAt_ball (x := y) (y := z) (C := 44 * |z - y|) hR_deriv
    fun u hu ↦ by simpa [Real.norm_eq_abs] using hd_lip u hu
  have hR0 : R y = 0 := by simp [R]
  rw [hR0, sub_zero, Real.norm_eq_abs] at h2
  exact h2.trans_eq (by rw [mul_assoc, ← sq, sq_abs])

/-- Second-order Taylor remainder `e^{iu} - (1 + iu - u^2 / 2)` of the complex exponential. -/
noncomputable def cexpRem (u : ℝ) : ℂ :=
  Complex.exp ((u : ℂ) * Complex.I) - (1 + (u : ℂ) * Complex.I - ((u ^ 2 / 2 : ℝ) : ℂ))

/-- Three-region bound on `‖cexpRem (θ * (z - y))‖` splitting into small jumps
(`|z - y| ≤ ε`), medium jumps (`ε < |z - y| < 2 M`), and far jumps (`2 M ≤ |z - y|`,
controlled by `bregmanExcess`). -/
lemma norm_cexpRem_le_probTail_bregman {θ_max θ ε M : ℝ} (hθ_nn : 0 ≤ θ_max)
    (hθ : |θ| ≤ θ_max) (hε : 0 < ε) (hM : 0 < M) (y z : ℝ) :
    ‖cexpRem (θ * (z - y))‖ ≤
      θ_max ^ 3 * ε * (z - y) ^ 2 +
        8 * θ_max ^ 2 * M ^ 2 * ({w : ℝ | ε < |w - y|}.indicator (fun _ ↦ (1 : ℝ)) z) +
        8 * θ_max ^ 2 * bregmanExcess M y z := by
  have hθ2 : θ ^ 2 ≤ θ_max ^ 2 := by
    rw [← sq_abs θ]; exact pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  have hθ3 : |θ| ^ 3 ≤ θ_max ^ 3 := pow_le_pow_left₀ (abs_nonneg θ) hθ 3
  have ht1_nn : 0 ≤ θ_max ^ 3 * ε * (z - y) ^ 2 := by positivity
  have ht2_nn : 0 ≤
      8 * θ_max ^ 2 * M ^ 2 * ({w : ℝ | ε < |w - y|}.indicator (fun _ ↦ (1 : ℝ)) z) :=
    mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) z)
  have ht3_nn : 0 ≤ 8 * θ_max ^ 2 * bregmanExcess M y z :=
    mul_nonneg (by positivity) (bregmanExcess_nonneg_and_le hM y z).1
  by_cases hgt : ε < |z - y|
  · have hr2 : ‖cexpRem (θ * (z - y))‖ ≤ 2 * θ_max ^ 2 * (z - y) ^ 2 := by
      have h0 : ‖cexpRem (θ * (z - y))‖ ≤ 2 * (θ * (z - y)) ^ 2 :=
        (norm_cexp_taylor_two_le _).trans (min_le_left _ _)
      rw [mul_pow] at h0
      exact h0.trans ((mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hθ2 (sq_nonneg _)) zero_le_two).trans_eq (by ring))
    by_cases hfar : 2 * M ≤ |z - y|
    · have hb := sq_sub_le_four_mul_bregmanExcess hM hfar
      nlinarith
    · have hfar' : |z - y| < 2 * M := not_le.mp hfar
      have hmem : z ∈ {w : ℝ | ε < |w - y|} := hgt
      rw [Set.indicator_of_mem hmem, mul_one]
      have hsq_lt : (z - y) ^ 2 ≤ 4 * M ^ 2 := by
        have hp := pow_le_pow_left₀ (abs_nonneg (z - y)) hfar'.le 2
        rw [sq_abs] at hp; linarith
      nlinarith
  · have hle_ε : |z - y| ≤ ε := not_lt.mp hgt
    have hr3 : ‖cexpRem (θ * (z - y))‖ ≤ θ_max ^ 3 * ε * (z - y) ^ 2 := by
      have h0 : ‖cexpRem (θ * (z - y))‖ ≤ |θ * (z - y)| ^ 3 :=
        (norm_cexp_taylor_two_le _).trans (min_le_right _ _)
      rw [abs_mul, mul_pow] at h0
      have hsub3 : |z - y| ^ 3 ≤ ε * (z - y) ^ 2 := by
        rw [show |z - y| ^ 3 = |z - y| * (z - y) ^ 2 by rw [← sq_abs]; ring]
        exact mul_le_mul_of_nonneg_right hle_ε (sq_nonneg _)
      exact (h0.trans (mul_le_mul hθ3 hsub3 (by positivity) (by positivity))).trans_eq (by ring)
    linarith

/-! ### Section 3: Subquadratic Semigroup Trajectory & Kernel-Step Integrability Helpers -/

/-- Continuity and forward-difference decomposition along a semigroup trajectory `μs` for any
continuous subquadratic test function `φ` whose second-order Taylor remainder is controlled by
`(z - y)^2`. -/
lemma subquad_semigroup_info {K : ℝ → Kernel ℝ ℝ}
    (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
    {a₀ C : ℝ} (ha₀ : 0 < a₀) (hC : 0 ≤ C) (hDom : QuadDom K a₀ C)
    {t M₀ : ℝ} (hM₀_nn : 0 ≤ M₀)
    {μs : ℝ → Measure ℝ} (hμs_prob : ∀ s : ℝ, IsProbabilityMeasure (μs s))
    (hμs_bind : ∀ s a : ℝ, 0 ≤ s → 0 < a → (μs s).bind (K a) = μs (s + a))
    (hμs_sq : ∀ s ∈ Icc 0 t,
      Integrable (fun y : ℝ ↦ y ^ 2) (μs s) ∧ (∫ y, y ^ 2 ∂μs s) ≤ M₀)
    {φ φ' : ℝ → ℝ} (hφ_cont : Continuous φ)
    {A₀ A₁ A₂ : ℝ} (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hφ_le : ∀ y : ℝ, |φ y| ≤ A₀ * y ^ 2)
    (hφ'_le : ∀ y : ℝ, |φ' y| ≤ A₁ * |y|)
    (hφ_rem : ∀ y z : ℝ, |φ z - φ y - φ' y * (z - y)| ≤ A₂ * (z - y) ^ 2) :
    (∀ s ∈ Icc 0 t, Integrable φ (μs s)) ∧
      (∀ s a : ℝ, 0 ≤ s → a ∈ Ioo 0 a₀ → s + a ≤ t →
        ((∫ y, φ y ∂μs (s + a)) - ∫ y, φ y ∂μs s) / a =
          ∫ y, ((∫ z, (φ z - φ y) ∂K a y) / a) ∂μs s) ∧
      ContinuousOn (fun s ↦ ∫ y, φ y ∂μs s) (Icc 0 t) := by
  have hφ_int_μ : ∀ s ∈ Icc 0 t, Integrable φ (μs s) := fun s hs ↦
    ((hμs_sq s hs).1.const_mul A₀).mono' hφ_cont.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa [Real.norm_eq_abs] using hφ_le y)
  have hφ_int_K : ∀ a ∈ Ioo 0 a₀, ∀ y : ℝ, Integrable φ (K a y) := fun a ha y ↦ by
    have := hMarkov a ha.1
    have hInt2 := (hDom a ha y).1
    have hdom_z : Integrable (fun z : ℝ ↦ 2 * A₀ * y ^ 2 + 2 * A₀ * (z - y) ^ 2) (K a y) :=
      iAdd (integrable_const _) (hInt2.const_mul _)
    refine hdom_z.mono' hφ_cont.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    rw [Real.norm_eq_abs]
    have hz2 : z ^ 2 ≤ 2 * y ^ 2 + 2 * (z - y) ^ 2 := by nlinarith [sq_nonneg (2 * y - z)]
    exact (hφ_le z).trans (by nlinarith)
  have hstep_le : ∀ a ∈ Ioo 0 a₀, ∀ y : ℝ,
      |(∫ z, (φ z - φ y) ∂K a y) / a| ≤ (2 * A₁ + A₂) * C * (1 + y ^ 2) :=
    fun a ha y ↦ by
    have ha_pos := ha.1; have := hMarkov a ha_pos
    obtain ⟨hInt2, hD1, hD2⟩ := hDom a ha y
    have hInt1 := integrable_sub_of_integrable_sq hInt2
    set rem : ℝ → ℝ := fun z ↦ φ z - φ y - φ' y * (z - y)
    have hrem_cont : Continuous rem := by
      dsimp [rem]; exact (hφ_cont.sub continuous_const).sub
        (continuous_const.mul (continuous_id.sub continuous_const))
    have hrem_int : Integrable rem (K a y) :=
      (hInt2.const_mul A₂).mono' hrem_cont.aestronglyMeasurable
        (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using hφ_rem y z)
    have hdecomp_z : (fun z : ℝ ↦ φ z - φ y) = fun z ↦ φ' y * (z - y) + rem z := by
      ext z; dsimp [rem]; ring
    have hint_eq : ∫ z, (φ z - φ y) ∂K a y =
        φ' y * (∫ z, (z - y) ∂K a y) + ∫ z, rem z ∂K a y := by
      rw [hdecomp_z, integral_add (hInt1.const_mul _) hrem_int, integral_const_mul]
    have hrem_int_le : |∫ z, rem z ∂K a y| ≤ A₂ * ∫ z, (z - y) ^ 2 ∂K a y := by
      rw [← Real.norm_eq_abs]
      exact (norm_integral_le_of_norm_le (hInt2.const_mul A₂)
        (ae_of_all _ fun z ↦ by simpa [Real.norm_eq_abs] using hφ_rem y z)).trans_eq
        (integral_const_mul _ _)
    have hnum_le : |∫ z, (φ z - φ y) ∂K a y| ≤
        (2 * A₁ + A₂) * C * a * (1 + y ^ 2) := by
      rw [hint_eq]
      have h1 : |φ' y * ∫ z, (z - y) ∂K a y| ≤ A₁ * |y| * (C * a * (1 + |y|)) := by
        rw [abs_mul]
        exact (mul_le_mul (hφ'_le y) hD1 (abs_nonneg _)
          (mul_nonneg hA₁ (abs_nonneg y))).trans_eq (by ring)
      have hy_quad : |y| * (1 + |y|) ≤ 2 * (1 + y ^ 2) := by
        nlinarith [sq_abs y, sq_nonneg (|y| - 1), abs_nonneg y]
      have h1' : A₁ * |y| * (C * a * (1 + |y|)) ≤ 2 * A₁ * C * a * (1 + y ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hy_quad (by positivity : 0 ≤ A₁ * C * a)
        linarith
      have h2' : A₂ * ∫ z, (z - y) ^ 2 ∂K a y ≤ A₂ * C * a * (1 + y ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hD2 hA₂
        linarith
      linarith [abs_add_le (φ' y * ∫ z, (z - y) ∂K a y) (∫ z, rem z ∂K a y)]
    rw [abs_div, abs_of_pos ha_pos, div_le_iff₀ ha_pos]
    linarith
  set g : ℝ → ℝ := fun s ↦ ∫ y, φ y ∂μs s
  have hdiff_eq : ∀ s a : ℝ, 0 ≤ s → a ∈ Ioo 0 a₀ → s + a ≤ t →
      (g (s + a) - g s) / a = ∫ y, ((∫ z, (φ z - φ y) ∂K a y) / a) ∂μs s :=
    fun s a hs ha hsa ↦ by
      have ha_pos := ha.1; have := hμs_prob s; have := hMarkov a ha_pos
      have hs_mem : s ∈ Icc 0 t := ⟨hs, by linarith⟩
      have hsa_mem : s + a ∈ Icc 0 t := ⟨by linarith, hsa⟩
      have hφ_sa : Integrable φ ((μs s ⊗ₘ K a).map Prod.snd) := by
        rw [← Measure.snd, Measure.snd_compProd, hμs_bind s a hs ha_pos]
        exact hφ_int_μ (s + a) hsa_mem
      have hφ_prod : Integrable (fun p : ℝ × ℝ ↦ φ p.2) (μs s ⊗ₘ K a) :=
        (integrable_map_measure hφ_cont.aestronglyMeasurable measurable_snd.aemeasurable).mp hφ_sa
      have hbind_int : g (s + a) = ∫ y, (∫ z, φ z ∂K a y) ∂μs s := by
        dsimp only [g]
        rw [← hμs_bind s a hs ha_pos, ← Measure.snd_compProd, Measure.snd,
          integral_map measurable_snd.aemeasurable hφ_cont.aestronglyMeasurable,
          Measure.integral_compProd hφ_prod]
      have router_int : Integrable (fun y ↦ ∫ z, φ z ∂K a y) (μs s) := by
        have hi := hφ_prod.integral_compProd
        simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at hi
        exact hi
      rw [hbind_int, ← integral_sub router_int (hφ_int_μ s hs_mem), ← integral_div]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      dsimp only
      rw [integral_sub (hφ_int_K a ha y) (integrable_const (φ y)), integral_const, probReal_univ,
        one_smul]
  set L_g : ℝ := (2 * A₁ + A₂) * C * (1 + M₀)
  have hLg_nn : 0 ≤ L_g := by positivity
  have hg_cont : ContinuousOn g (Icc 0 t) := by
    rw [Metric.continuousOn_iff]; intro s₁ hs₁ ε hε
    refine ⟨min a₀ (ε / (L_g + 1)), lt_min ha₀ (by positivity), fun s₂ hs₂ hd ↦ ?_⟩
    rw [Real.dist_eq] at hd; rw [Real.dist_eq]
    have hp : ∀ u v : ℝ, u ∈ Icc 0 t → v ∈ Icc 0 t → u ≤ v →
        v - u < min a₀ (ε / (L_g + 1)) → |g v - g u| < ε :=
      fun u v hu hv huv hvu ↦ by
        rcases eq_or_lt_of_le huv with rfl | hlt
        · simpa using hε
        · set a : ℝ := v - u; have ha_pos : 0 < a := sub_pos.mpr hlt
          have ha : a ∈ Ioo 0 a₀ := ⟨ha_pos, lt_of_lt_of_le hvu (min_le_left _ _)⟩
          have hua : u + a ≤ t := by linarith [hv.2]
          have := hμs_prob u
          have hdom_u : Integrable (fun y : ℝ ↦ (2 * A₁ + A₂) * C * (1 + y ^ 2)) (μs u) :=
            (iAdd (integrable_const 1) (hμs_sq u hu).1).const_mul ((2 * A₁ + A₂) * C)
          have hb : |(g (u + a) - g u) / a| ≤ L_g := by
            rw [hdiff_eq u a hu.1 ha hua, ← Real.norm_eq_abs]
            refine (norm_integral_le_of_norm_le hdom_u (ae_of_all _ fun y ↦ ?_)).trans ?_
            · rw [Real.norm_eq_abs]; exact hstep_le a ha y
            · rw [integral_const_mul, integral_add (integrable_const 1) (hμs_sq u hu).1,
                integral_const, probReal_univ, one_smul]
              dsimp [L_g]
              exact mul_le_mul_of_nonneg_left (by linarith [(hμs_sq u hu).2]) (by positivity)
          rw [show u + a = v by ring, abs_div, abs_of_pos ha_pos, div_le_iff₀ ha_pos] at hb
          nlinarith [(lt_div_iff₀' (by positivity : 0 < L_g + 1)).mp
            (lt_of_lt_of_le hvu (min_le_right _ _))]
    rcases le_total s₁ s₂ with hle | hle
    · exact hp s₁ s₂ hs₁ hs₂ hle (by rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at hd)
    · rw [abs_sub_comm]
      exact hp s₂ s₁ hs₂ hs₁ hle
        (by rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at hd)
  exact ⟨hφ_int_μ, hdiff_eq, hg_cont⟩

/-- Integrability under any square-integrable probability measure `μ` of the one-step conditional
drift, conditional second moment, and conditional tail probability of `K a` (`a ∈ (0, a₀)`),
together with the Chebyshev domination of the tail probability. -/
lemma kernel_step_integrable_on_mu {K : ℝ → Kernel ℝ ℝ}
    (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
    {a₀ C : ℝ} (_ha₀ : 0 < a₀) (hC : 0 ≤ C) (hDom : QuadDom K a₀ C)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ_sq : Integrable (fun y : ℝ ↦ y ^ 2) μ)
    {a : ℝ} (ha : a ∈ Ioo 0 a₀) :
    Integrable (fun y ↦ (∫ z, (z - y) ∂K a y) / a) μ ∧
      Integrable (fun y ↦ (∫ z, (z - y) ^ 2 ∂K a y) / a) μ ∧
      ∀ ε : ℝ, 0 < ε →
        Integrable (fun y ↦ (K a y).real {z : ℝ | ε < |z - y|} / a) μ ∧
          ∀ y : ℝ,
            (K a y).real {z : ℝ | ε < |z - y|} / a ≤ (C / ε ^ 2) * (1 + y ^ 2) := by
  have ha_pos := ha.1; have := hMarkov a ha_pos
  have hbound_int : Integrable (fun y : ℝ ↦ C * a * (1 + y ^ 2)) μ :=
    (iAdd (integrable_const 1) hμ_sq).const_mul (C * a)
  have hf2_prod : Integrable (fun p : ℝ × ℝ ↦ (p.2 - p.1) ^ 2) (μ ⊗ₘ K a) := by
    have hm_sq : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ (p.2 - p.1) ^ 2) (μ ⊗ₘ K a) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ ↦ (p.2 - p.1) ^ 2).aestronglyMeasurable
    refine ⟨hm_sq, ?_⟩
    rw [HasFiniteIntegral]
    have henorm : (∫⁻ p : ℝ × ℝ, ‖(p.2 - p.1) ^ 2‖ₑ ∂(μ ⊗ₘ K a)) =
        ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((p.2 - p.1) ^ 2) ∂(μ ⊗ₘ K a) :=
      lintegral_congr fun p ↦ Real.enorm_eq_ofReal (sq_nonneg (p.2 - p.1))
    rw [henorm, Measure.lintegral_compProd (by fun_prop)]
    have hle : (∫⁻ y, (∫⁻ z, ENNReal.ofReal ((z - y) ^ 2) ∂K a y) ∂μ) ≤
        ∫⁻ y, ENNReal.ofReal (C * a * (1 + y ^ 2)) ∂μ := by
      refine lintegral_mono fun y ↦ ?_
      obtain ⟨hInt2, -, hD2⟩ := hDom a ha y
      rw [← ofReal_integral_eq_lintegral_ofReal hInt2 (ae_of_all _ fun _ ↦ sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hD2
    refine hle.trans_lt ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hbound_int
      (ae_of_all _ fun y ↦ by positivity)]
    exact ENNReal.ofReal_lt_top
  have hf1_prod : Integrable (fun p : ℝ × ℝ ↦ p.2 - p.1) (μ ⊗ₘ K a) :=
    (iAdd (integrable_const (1 : ℝ)) hf2_prod).mono'
      (continuous_snd.sub continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun p ↦ by
        rw [Real.norm_eq_abs]
        nlinarith [sq_abs (p.2 - p.1), abs_nonneg (p.2 - p.1)])
  have hi2 : Integrable (fun y ↦ ∫ z, (z - y) ^ 2 ∂K a y) μ := by
    have h := hf2_prod.integral_compProd
    simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at h; exact h
  have hi1 : Integrable (fun y ↦ ∫ z, (z - y) ∂K a y) μ := by
    have h := hf1_prod.integral_compProd
    simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at h; exact h
  refine ⟨hi1.div_const a, hi2.div_const a, fun ε hε ↦ ?_⟩
  have hms2 : MeasurableSet {p : ℝ × ℝ | ε < |p.2 - p.1|} :=
    (isOpen_lt continuous_const (continuous_snd.sub continuous_fst).abs).measurableSet
  have hind_prod : Integrable
      ({p : ℝ × ℝ | ε < |p.2 - p.1|}.indicator (fun _ ↦ (1 : ℝ))) (μ ⊗ₘ K a) :=
    (integrable_const (1 : ℝ)).indicator hms2
  have hind_y : Integrable (fun y ↦ (K a y).real {z : ℝ | ε < |z - y|}) μ := by
    have h := hind_prod.integral_compProd
    simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at h
    refine h.congr (ae_of_all _ fun y ↦ ?_)
    dsimp only
    have hms1 : MeasurableSet {z : ℝ | ε < |z - y|} :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet
    have heq :
        (fun z : ℝ ↦
          {p : ℝ × ℝ | ε < |p.2 - p.1|}.indicator (fun _ ↦ (1 : ℝ)) (y, z)) =
          {z : ℝ | ε < |z - y|}.indicator (fun _ ↦ (1 : ℝ)) := by
      ext z; by_cases hz : ε < |z - y| <;> simp [Set.indicator, hz]
    rw [heq, integral_indicator_const _ hms1, smul_eq_mul, mul_one]
  refine ⟨hind_y.div_const a, fun y ↦ ?_⟩
  obtain ⟨hInt2, -, hD2⟩ := hDom a ha y
  have hms1 : MeasurableSet {z : ℝ | ε < |z - y|} :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet
  have hcheb : ε ^ 2 * (K a y).real {z : ℝ | ε < |z - y|} ≤ ∫ z, (z - y) ^ 2 ∂K a y := by
    have hind_eq : ε ^ 2 * (K a y).real {z : ℝ | ε < |z - y|} =
        ∫ z, {z' : ℝ | ε < |z' - y|}.indicator (fun _ ↦ ε ^ 2) z ∂K a y := by
      rw [integral_indicator_const _ hms1, smul_eq_mul, mul_comm]
    rw [hind_eq]
    refine integral_mono ((integrable_const (ε ^ 2)).indicator hms1) hInt2 fun z ↦ ?_
    by_cases hz : z ∈ {z' : ℝ | ε < |z' - y|}
    · rw [Set.indicator_of_mem hz]
      have hlt : ε < |z - y| := hz
      have hp := pow_le_pow_left₀ hε.le hlt.le 2
      rwa [sq_abs] at hp
    · rw [Set.indicator_of_notMem hz]; exact sq_nonneg _
  rw [div_le_iff₀ ha_pos]
  have hmul : ε ^ 2 * (K a y).real {z : ℝ | ε < |z - y|} ≤ C * a * (1 + y ^ 2) :=
    hcheb.trans hD2
  have hdiv := (le_div_iff₀' (pow_pos hε 2)).mpr hmul
  exact hdiv.trans_eq (by field_simp [hε.ne'])

end OUProbTailAux

/-! ### Section 4: Semigroup Uniqueness Under Ross's Printed Probability Tail (`BL8-2`) -/

open OUProbTailAux

/-- **Transition semigroup uniqueness under Ross's printed probability tail**
(resolves open obligation `BL8-2`, Remark 3.5, `SteinIntro.tex:1009-1024`):
any Chapman–Kolmogorov Markov transition semigroup `(K t)_{t > 0}` satisfying Remark 3.5's
literally printed Items 1–3 (including the probability tail
`(K a x).real {y | ε < |y - x|} = o(a)` in place of the Lindeberg second-moment tail) and
small-time quadratic moment domination (`QuadDom`) equals `ouKernel` at every positive time
`t > 0`. -/
theorem eq_ouKernel_of_probTail {K : ℝ → Kernel ℝ ℝ}
    (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
    (hDrift : ∀ x : ℝ,
      Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a) (𝓝[>] 0) (𝓝 0))
    (hDiff : ∀ x : ℝ,
      Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a) (𝓝[>] 0) (𝓝 0))
    (hProbTail : ∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun a : ℝ ↦ (K a x).real {y : ℝ | ε < |y - x|} / a) (𝓝[>] 0) (𝓝 0))
    (hDom : ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ QuadDom K a₀ C)
    (hSemi : ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → K (s + t) = Kernel.comp (K t) (K s))
    {t : ℝ} (ht : 0 < t) : K t = ouKernel t := by
  obtain ⟨a₀, ha₀, C, hC, hDom'⟩ := hDom
  refine Kernel.ext fun x ↦ ?_; have := hMarkov t ht
  refine Measure.ext_of_charFun (funext fun ξ₀ ↦ ?_)
  obtain ⟨M, hM_nn, hM_sq⟩ := uniform_sq_bound_of_semigroup hMarkov ha₀ hC hDom' hSemi ht x
  set μs : ℝ → Measure ℝ := fun s ↦ if 0 < s then K s x else Measure.dirac x
  have hμs_prob : ∀ s : ℝ, IsProbabilityMeasure (μs s) := fun s ↦ by
    by_cases hs : 0 < s
    · simp only [μs, hs, ↓reduceIte]; exact (hMarkov s hs).isProbabilityMeasure x
    · simp only [μs, hs, ↓reduceIte]; infer_instance
  have hμs_bind : ∀ s a : ℝ, 0 ≤ s → 0 < a → (μs s).bind (K a) = μs (s + a) :=
    fun s a hs ha ↦ by
      rcases eq_or_lt_of_le hs with rfl | hs_pos
      · simp [μs, ha, Measure.dirac_bind (Kernel.measurable _)]
      · have hsa : 0 < s + a := add_pos hs_pos ha
        simp [μs, hs_pos, hsa, hSemi s hs_pos a ha, Kernel.comp_apply]
  set M₀ : ℝ := max (x ^ 2) M
  have hM₀_nn : 0 ≤ M₀ := le_max_of_le_right hM_nn
  have hμs_sq : ∀ s ∈ Icc 0 t,
      Integrable (fun y : ℝ ↦ y ^ 2) (μs s) ∧ (∫ y, y ^ 2 ∂μs s) ≤ M₀ :=
    fun s hs ↦ by
      rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
      · simp only [μs, lt_irrefl, ↓reduceIte, integral_dirac]
        exact ⟨integrable_dirac (by simp), le_max_left _ _⟩
      · simp only [μs, hs_pos, ↓reduceIte]
        obtain ⟨hI, hL⟩ := hM_sq s ⟨hs_pos, hs.2⟩
        exact ⟨hI, hL.trans (le_max_right _ _)⟩
  set ξ : ℝ → ℝ := fun s ↦ Real.exp (-(t - s)) * ξ₀
  have hd_ξ : ∀ s : ℝ, HasDerivAt ξ (ξ s) s := fun s ↦ by
    have h1 : HasDerivAt (fun u : ℝ ↦ -(t - u)) 1 s :=
      (((hasDerivAt_id' s).const_sub t).neg).congr_deriv (by ring)
    exact (h1.exp.mul_const ξ₀).congr_deriv (by dsimp only [ξ]; ring)
  have hξ_le : ∀ s : ℝ, s ≤ t → |ξ s| ≤ |ξ₀| := fun s hs ↦ by
    dsimp only [ξ]; rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg ξ₀) (Real.exp_le_one_iff.mpr (by linarith))
  have hξ_lip : ∀ s a : ℝ, 0 ≤ a → s + a ≤ t → |ξ (s + a) - ξ s| ≤ |ξ₀| * a :=
    fun s a ha_nn hsa ↦ by
      simpa [Real.norm_eq_abs, abs_of_nonneg ha_nn] using
        norm_sub_le_of_hasDerivAt_ball (x := s) (y := s + a) (C := |ξ₀|) hd_ξ fun u hu ↦ by
          rw [Real.norm_eq_abs]
          exact hξ_le u (by linarith [(abs_le.mp (by simpa [abs_of_nonneg ha_nn] using hu)).2])
  have hcexp_le : ∀ s a y : ℝ, 0 < a → s + a ≤ t →
      ‖(cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)‖ ≤ |ξ₀| * |y| :=
    fun s a y ha hsa ↦ by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_le_iff₀ ha]
      exact (norm_cexpI_sub_le _ _ _).trans
        ((mul_le_mul_of_nonneg_right (hξ_lip s a ha.le hsa) (abs_nonneg y)).trans_eq (by ring))
  -- One-step charFun decomposition and `QuadDom` bound (no Lindeberg needed)
  have hdecomp : ∀ a ∈ Ioo 0 a₀, ∀ θ y : ℝ,
      (charFun (K a y) θ - cexpI θ y) / (a : ℂ) =
      cexpI θ y * (Complex.I * ((θ * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ) -
        (((θ ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)) +
        cexpI θ y * ((∫ z, cexpRem (θ * (z - y)) ∂K a y) / (a : ℂ)) := by
    intro a ha θ y; have ha_pos := ha.1; have := hMarkov a ha_pos
    have hInt2 := (hDom' a ha y).1; have hInt1 := integrable_sub_of_integrable_sq hInt2
    have hr_int : Integrable (fun z : ℝ ↦ cexpRem (θ * (z - y))) (K a y) :=
      (hInt2.const_mul (2 * θ ^ 2)).mono' (by unfold cexpRem; fun_prop) (ae_of_all _ fun z ↦
        (norm_cexp_taylor_two_le (θ * (z - y))).trans ((min_le_left _ _).trans_eq (by ring)))
    have hp : (fun z : ℝ ↦ cexpI θ z - cexpI θ y) = fun z ↦ cexpI θ y *
        ((((θ * (z - y) : ℝ) : ℂ) * Complex.I - ((((θ ^ 2 / 2) * (z - y) ^ 2 : ℝ) : ℂ))) +
          cexpRem (θ * (z - y))) := funext fun z ↦ by
      have hexp_z : cexpI θ z =
          cexpI θ y * Complex.exp (((θ * (z - y) : ℝ) : ℂ) * Complex.I) := by
        simp only [cexpI, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub]
        congr 1; ring
      rw [hexp_z]; unfold cexpRem
      rw [show (θ * (z - y)) ^ 2 / 2 = (θ ^ 2 / 2) * (z - y) ^ 2 by ring]; ring
    have hw1_i : Integrable (fun z : ℝ ↦ ((θ * (z - y) : ℝ) : ℂ) * Complex.I) (K a y) :=
      (hInt1.const_mul θ).ofReal.mul_const Complex.I
    have hw2_i : Integrable (fun z : ℝ ↦ (((θ ^ 2 / 2) * (z - y) ^ 2 : ℝ) : ℂ)) (K a y) :=
      (hInt2.const_mul (θ ^ 2 / 2)).ofReal
    have hsub_one : charFun (K a y) θ - cexpI θ y =
        ∫ z, (cexpI θ z - cexpI θ y) ∂K a y := by
      rw [charFun_eq_integral_cexpI, integral_sub (integrable_cexpI (K a y) θ)
        (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [hsub_one, hp, integral_const_mul, integral_add (iSub hw1_i hw2_i) hr_int,
      integral_sub hw1_i hw2_i, integral_mul_const, integral_complex_ofReal, integral_const_mul,
      integral_complex_ofReal, integral_const_mul]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr ha_pos.ne']
  have hStep_bnd : ∀ θ : ℝ, |θ| ≤ |ξ₀| → ∀ a ∈ Ioo 0 a₀, ∀ y : ℝ,
      ‖(charFun (K a y) θ - cexpI θ y) / (a : ℂ)‖ ≤
        (|ξ₀| + 3 * |ξ₀| ^ 2) * C * (1 + |y| + y ^ 2) := fun θ hθ a ha y ↦ by
    have ha_pos := ha.1; have := hMarkov a ha_pos; obtain ⟨hInt2, hD1, hD2⟩ := hDom' a ha y
    have hθ2 : θ ^ 2 ≤ |ξ₀| ^ 2 := by
      rw [← sq_abs θ]; exact pow_le_pow_left₀ (abs_nonneg θ) hθ 2
    rw [hdecomp a ha θ y]
    have hb1 : |(∫ z, (z - y) ∂K a y) / a| ≤ C * (1 + |y|) := by
      rw [abs_div, abs_of_pos ha_pos, div_le_iff₀ ha_pos]; linarith
    have hb2 : (∫ z, (z - y) ^ 2 ∂K a y) / a ≤ C * (1 + y ^ 2) := by
      rw [div_le_iff₀ ha_pos]; linarith
    have hsq_nn : 0 ≤ (∫ z, (z - y) ^ 2 ∂K a y) / a :=
      div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) ha_pos.le
    have ht1 : ‖Complex.I * ((θ * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ)‖ ≤
        |ξ₀| * C * (1 + |y|) := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul hθ hb1 (abs_nonneg _) (abs_nonneg ξ₀)).trans_eq (by ring)
    have ht2 : ‖(((θ ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)‖ ≤
        (|ξ₀| ^ 2 / 2) * C * (1 + y ^ 2) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity),
        abs_of_nonneg hsq_nn]
      exact (mul_le_mul (div_le_div_of_nonneg_right hθ2 zero_le_two) hb2 hsq_nn
        (by positivity)).trans_eq (by ring)
    have ht3 : ‖(∫ z, cexpRem (θ * (z - y)) ∂K a y) / (a : ℂ)‖ ≤
        2 * |ξ₀| ^ 2 * C * (1 + y ^ 2) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha_pos]
      have hint_le : ‖∫ z, cexpRem (θ * (z - y)) ∂K a y‖ ≤
          2 * |ξ₀| ^ 2 * ∫ z, (z - y) ^ 2 ∂K a y := by
        refine (norm_integral_le_of_norm_le (hInt2.const_mul (2 * |ξ₀| ^ 2))
          (ae_of_all _ fun z ↦ ?_)).trans_eq (integral_const_mul _ _)
        refine (norm_cexp_taylor_two_le _).trans ((min_le_left _ _).trans ?_)
        rw [mul_pow]; exact (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hθ2 (sq_nonneg _)) zero_le_two).trans_eq (by ring)
      refine (div_le_div_of_nonneg_right hint_le ha_pos.le).trans ?_
      rw [mul_div_assoc]; exact (mul_le_mul_of_nonneg_left hb2 (by positivity)).trans_eq (by ring)
    have hnorm_sum :
        ‖cexpI θ y * (Complex.I * ((θ * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ) -
            (((θ ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)) +
          cexpI θ y * ((∫ z, cexpRem (θ * (z - y)) ∂K a y) / (a : ℂ))‖ ≤
        (|ξ₀| * C * (1 + |y|) + (|ξ₀| ^ 2 / 2) * C * (1 + y ^ 2)) +
          2 * |ξ₀| ^ 2 * C * (1 + y ^ 2) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_cexpI, one_mul, norm_mul, norm_cexpI, one_mul]
      exact add_le_add ((norm_sub_le _ _).trans (add_le_add ht1 ht2)) ht3
    exact hnorm_sum.trans (by
      nlinarith [abs_nonneg y, sq_nonneg y, mul_nonneg (abs_nonneg ξ₀) hC,
        mul_nonneg (sq_nonneg |ξ₀|) hC])
  set L₁ : ℝ := (|ξ₀| + 3 * |ξ₀| ^ 2) * C
  have hL₁_nn : 0 ≤ L₁ := by positivity
  set Φ : ℝ → ℂ := fun s ↦ charFun (μs s) (ξ s)
  have hchar_int : ∀ s a : ℝ, 0 ≤ s → 0 < a →
      Integrable (fun y ↦ charFun (K a y) (ξ (s + a))) (μs s) := fun s a _ ha ↦ by
    have := hμs_prob s; have := hMarkov a ha
    have hi : Integrable (fun p : ℝ × ℝ ↦ cexpI (ξ (s + a)) p.2) (μs s ⊗ₘ K a) :=
      Integrable.of_bound ((continuous_cexpI _).comp continuous_snd).aestronglyMeasurable
        1 (ae_of_all _ fun p ↦ (norm_cexpI _ p.2).le)
    have h2 := hi.integral_compProd
    simp only [Kernel.prodMkLeft_apply, Kernel.const_apply, ← charFun_eq_integral_cexpI] at h2
    exact h2
  have hΦ_decomp : ∀ s a : ℝ, 0 ≤ s → 0 < a → (Φ (s + a) - Φ s) / (a : ℂ) =
      ∫ y, ((charFun (K a y) (ξ (s + a)) - cexpI (ξ (s + a)) y) / (a : ℂ) +
        (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)) ∂μs s := fun s a hs ha ↦ by
    have := hμs_prob s; have := hMarkov a ha
    dsimp only [Φ]; rw [← hμs_bind s a hs ha, charFun_bind_eq (μs s) (K a) (ξ (s + a)),
      charFun_eq_integral_cexpI (μs s) (ξ s),
      ← integral_sub (hchar_int s a hs ha) (integrable_cexpI (μs s) (ξ s)), ← integral_div]
    exact integral_congr_ae (ae_of_all _ fun y ↦ by ring)
  set K_lip : ℝ := L₁ * (2 + 2 * M₀) + |ξ₀| * (1 + M₀)
  have hK_nn : 0 ≤ K_lip := by positivity
  have hdom_info : ∀ s ∈ Icc 0 t,
      Integrable (fun y : ℝ ↦ L₁ * (1 + |y| + y ^ 2) + |ξ₀| * |y|) (μs s) ∧
        (∫ y, (L₁ * (1 + |y| + y ^ 2) + |ξ₀| * |y|) ∂μs s) ≤ K_lip := fun s hs ↦ by
    have := hμs_prob s; obtain ⟨hInt_y2, hInt_y2_le⟩ := hμs_sq s hs
    have hInt_abs := integrable_abs_of_integrable_sq hInt_y2
    have h1 := (iAdd (iAdd (integrable_const 1) hInt_abs) hInt_y2).const_mul L₁
    refine ⟨iAdd h1 (hInt_abs.const_mul |ξ₀|), ?_⟩
    rw [integral_add h1 (hInt_abs.const_mul |ξ₀|), integral_const_mul, integral_const_mul,
      integral_add (iAdd (integrable_const 1) hInt_abs) hInt_y2,
      integral_add (integrable_const 1) hInt_abs, integral_const, probReal_univ, one_smul]
    have habs_le : (∫ y, |y| ∂μs s) ≤ 1 + M₀ := by
      have hm := integral_mono hInt_abs (iAdd (integrable_const 1) hInt_y2)
        fun y ↦ by dsimp only; nlinarith [sq_abs y, abs_nonneg y]
      rw [integral_add (integrable_const 1) hInt_y2, integral_const, probReal_univ,
        one_smul] at hm
      linarith
    dsimp only [K_lip]; nlinarith [abs_nonneg ξ₀]
  have hΦ_cont : ContinuousOn Φ (Icc 0 t) := by
    rw [Metric.continuousOn_iff]; intro s₁ hs₁ ε hε
    refine ⟨min a₀ (ε / (K_lip + 1)), lt_min ha₀ (by positivity), fun s₂ hs₂ hd ↦ ?_⟩
    rw [Real.dist_eq] at hd; rw [dist_eq_norm]
    have hp : ∀ u v : ℝ, u ∈ Icc 0 t → v ∈ Icc 0 t → u ≤ v →
        v - u < min a₀ (ε / (K_lip + 1)) → ‖Φ v - Φ u‖ < ε :=
      fun u v hu hv huv hvu ↦ by
        rcases eq_or_lt_of_le huv with rfl | hlt
        · simpa using hε
        · set a : ℝ := v - u; have ha_pos : 0 < a := sub_pos.mpr hlt
          have ha : a ∈ Ioo 0 a₀ := ⟨ha_pos, lt_of_lt_of_le hvu (min_le_left _ _)⟩
          have hsa : u + a ≤ t := by linarith [hv.2]
          have := hμs_prob u; obtain ⟨hdom_u, hdom_le⟩ := hdom_info u hu
          have hb : ‖(Φ (u + a) - Φ u) / (a : ℂ)‖ ≤ K_lip := by
            rw [hΦ_decomp u a hu.1 ha_pos]
            exact (norm_integral_le_of_norm_le hdom_u (ae_of_all _ fun y ↦
              (norm_add_le _ _).trans (add_le_add
                (hStep_bnd (ξ (u + a)) (hξ_le _ hsa) a ha y)
                (hcexp_le u a y ha_pos hsa)))).trans hdom_le
          rw [show u + a = v by ring, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ha_pos, div_le_iff₀ ha_pos] at hb
          nlinarith [(lt_div_iff₀' (by positivity : 0 < K_lip + 1)).mp
            (lt_of_lt_of_le hvu (min_le_right _ _))]
    rcases le_total s₁ s₂ with hle | hle
    · exact hp s₁ s₂ hs₁ hs₂ hle (by rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at hd)
    · rw [norm_sub_rev]
      exact hp s₂ s₁ hs₂ hs₁ hle
        (by rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at hd)
  set expFactor : ℝ → ℂ := fun s ↦ Complex.exp (((ξ s ^ 2 / 2 : ℝ) : ℂ))
  set Ψ : ℝ → ℂ := fun s ↦ expFactor s * Φ s
  have hΨ_cont : ContinuousOn Ψ (Icc 0 t) :=
    (by dsimp [expFactor, ξ]; fun_prop : Continuous expFactor).continuousOn.mul hΦ_cont
  set C₀ : ℝ := Real.exp (ξ₀ ^ 2 / 2)
  have hC₀_pos : 0 < C₀ := Real.exp_pos _
  have hexpFactor_le : ∀ u : ℝ, u ≤ t → ‖expFactor u‖ ≤ C₀ := fun u hu ↦ by
    dsimp [expFactor, C₀]
    rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hsq : ξ u ^ 2 ≤ ξ₀ ^ 2 := by
      rw [← sq_abs (ξ u), ← sq_abs ξ₀]
      exact pow_le_pow_left₀ (abs_nonneg _) (hξ_le u hu) 2
    exact Real.exp_le_exp.mpr (by linarith)
  -- Key claim: for every `w : ℂ` with `‖w‖ ≤ 1`, `Re (w * (Ψ t - Ψ 0)) ≤ 0`.
  have hRe_le_zero : ∀ w : ℂ, ‖w‖ ≤ 1 → (w * (Ψ t - Ψ 0)).re ≤ 0 := fun w hw ↦ by
    -- Bound `Re (w * (Ψ t - Ψ 0))` in terms of `H_M t`, `ε`, and `∫ u in 0..t, ρ_M u`
    have h_for_M_ε : ∀ M_param : ℝ, 0 < M_param → ∀ ε : ℝ, 0 < ε →
        (w * (Ψ t - Ψ 0)).re ≤
          8 * C₀ * ξ₀ ^ 2 * (∫ y, tailExcess M_param y ∂μs t) +
            2 * C₀ * |ξ₀| ^ 3 * t * ε +
            8 * C₀ * ξ₀ ^ 2 *
              ∫ u in (0 : ℝ)..t, (∫ y, driftExcess M_param y ∂μs (max 0 (min t u))) := by
      intro M_param hMp ε hε
      have hH_info := subquad_semigroup_info
        hMarkov ha₀ hC hDom' hM₀_nn hμs_prob hμs_bind hμs_sq
        (φ := tailExcess M_param) (φ' := tailExcessDeriv M_param)
        (by unfold tailExcess truncSq; fun_prop)
        zero_le_one zero_le_two (by norm_num : (0 : ℝ) ≤ 6)
        (fun y ↦ by
          rw [abs_of_nonneg (tailExcess_bounds hMp y).1, one_mul]
          exact (tailExcess_bounds hMp y).2.1)
        (abs_tailExcessDeriv_le M_param)
        (fun y z ↦ by
          change |bregmanExcess M_param y z| ≤ 6 * (z - y) ^ 2
          rw [abs_of_nonneg (bregmanExcess_nonneg_and_le hMp y z).1]
          exact (bregmanExcess_nonneg_and_le hMp y z).2)
      have hρ_info := subquad_semigroup_info
        hMarkov ha₀ hC hDom' hM₀_nn hμs_prob hμs_bind hμs_sq
        (φ := driftExcess M_param) (φ' := driftExcessDeriv M_param)
        (by unfold driftExcess tailExcessDeriv; fun_prop)
        zero_le_two (by norm_num : (0 : ℝ) ≤ 8) (by norm_num : (0 : ℝ) ≤ 44)
        (fun y ↦ by
          rw [abs_of_nonneg (driftExcess_bounds hMp y).1]
          exact (driftExcess_bounds hMp y).2.1)
        (fun y ↦ (driftExcess_bounds hMp y).2.2.2)
        (abs_driftExcess_taylor_le hMp)
      set H_fn : ℝ → ℝ := fun s ↦ ∫ y, tailExcess M_param y ∂μs s
      set ρ_ext : ℝ → ℝ := fun u ↦ ∫ y, driftExcess M_param y ∂μs (max 0 (min t u))
      have hclamp_mem : ∀ u : ℝ, max 0 (min t u) ∈ Icc 0 t := fun u ↦
        ⟨le_max_left _ _, max_le ht.le (min_le_left _ _)⟩
      have hρ_ext_cont : Continuous ρ_ext :=
        hρ_info.2.2.comp_continuous
          (continuous_const.max (continuous_const.min continuous_id)) hclamp_mem
      set q_fn : ℝ → ℝ := fun u ↦
        2 * C₀ * |ξ₀| ^ 3 * ε + 8 * C₀ * ξ₀ ^ 2 * ρ_ext u
      have hq_cont : Continuous q_fn := by dsimp [q_fn]; fun_prop
      set J_fn : ℝ → ℝ := fun s ↦ ∫ u in (0 : ℝ)..s, q_fn u
      have hJ_cont : Continuous J_fn := continuous_iff_continuousAt.mpr fun s ↦
        (hasDerivAt_primitive hq_cont s).continuousAt
      set F_fn : ℝ → ℝ := fun s ↦ (w * Ψ s).re - 8 * C₀ * ξ₀ ^ 2 * H_fn s - J_fn s
      have hF_cont : ContinuousOn F_fn (Icc 0 t) := by
        have hwΨ : ContinuousOn (fun s ↦ (w * Ψ s).re) (Icc 0 t) :=
          Complex.continuous_re.continuousOn.comp
            (continuousOn_const.mul hΨ_cont) (mapsTo_univ _ _)
        exact (hwΨ.sub (continuousOn_const.mul hH_info.2.2)).sub hJ_cont.continuousOn
      have hF_le : F_fn t ≤ F_fn 0 := by
        refine le_of_eventually_slope_right_le_tendsto_zero ht.le hF_cont fun s hs ↦ ?_
        have := hμs_prob s
        have hs_Icc : s ∈ Icc 0 t := ⟨hs.1, hs.2.le⟩
        obtain ⟨hInt_y2_s, -⟩ := hμs_sq s hs_Icc
        have hInt_abs_s := integrable_abs_of_integrable_sq hInt_y2_s
        -- Main untruncated term `G₀(a, y)` and its limit `-ξ(s)^2 * Φ(s)`
        set G₀ : ℝ → ℝ → ℂ := fun a y ↦
          cexpI (ξ (s + a)) y *
            (Complex.I * ((ξ (s + a) * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ) -
              (((ξ (s + a) ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)) +
            (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)
        set Q₀ : ℝ → ℂ := fun a ↦
          expFactor (s + a) * (∫ y, G₀ a y ∂μs s) +
            ((expFactor (s + a) - expFactor s) / (a : ℂ)) * Φ s
        have hξ_lim : Tendsto (fun a : ℝ ↦ ξ (s + a)) (𝓝[>] 0) (𝓝 (ξ s)) := by
          have hc : Continuous (fun a : ℝ ↦ ξ (s + a)) := by dsimp [ξ]; fun_prop
          simpa only [add_zero] using (hc.continuousWithinAt (x := 0) (s := Ioi 0)).tendsto
        have hG₀_lim : Tendsto (fun a : ℝ ↦ ∫ y, G₀ a y ∂μs s) (𝓝[>] 0)
            (𝓝 (-(((ξ s ^ 2 : ℝ) : ℂ) * Φ s))) := by
          set domG : ℝ → ℝ := fun y ↦
            (|ξ₀| * C * (1 + |y|) + (|ξ₀| ^ 2 / 2) * C * (1 + y ^ 2)) + |ξ₀| * |y|
          have hdomG_int : Integrable domG (μs s) :=
            iAdd (iAdd ((iAdd (integrable_const 1) hInt_abs_s).const_mul (|ξ₀| * C))
              ((iAdd (integrable_const 1) hInt_y2_s).const_mul ((|ξ₀| ^ 2 / 2) * C)))
              (hInt_abs_s.const_mul |ξ₀|)
          have hG₀_ev : ∀ᶠ a in 𝓝[>] 0,
              AEStronglyMeasurable (G₀ a) (μs s) ∧ ∀ y : ℝ, ‖G₀ a y‖ ≤ domG y := by
            filter_upwards [Ioo_mem_nhdsGT (lt_min ha₀ (sub_pos.mpr hs.2))] with a ha
            have ha_pos := ha.1
            have ha_Ioo : a ∈ Ioo 0 a₀ := ⟨ha_pos, lt_of_lt_of_le ha.2 (min_le_left _ _)⟩
            have hsa : s + a ≤ t := by linarith [lt_of_lt_of_le ha.2 (min_le_right _ _)]
            obtain ⟨hi1, hi2, -⟩ :=
              kernel_step_integrable_on_mu hMarkov ha₀ hC hDom' (μs s) hInt_y2_s ha_Ioo
            have hm1 : AEStronglyMeasurable
                (fun y ↦ cexpI (ξ (s + a)) y *
                  (Complex.I * ((ξ (s + a) * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ) -
                    (((ξ (s + a) ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)))
                (μs s) := by
              refine (continuous_cexpI _).aestronglyMeasurable.mul ?_
              exact (aestronglyMeasurable_const.mul
                (Complex.continuous_ofReal.comp_aestronglyMeasurable
                  (hi1.aestronglyMeasurable.const_mul _))).sub
                (Complex.continuous_ofReal.comp_aestronglyMeasurable
                  (hi2.aestronglyMeasurable.const_mul _))
            have hm2 : AEStronglyMeasurable
                (fun y ↦ (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)) (μs s) :=
              ((iSub (integrable_cexpI _ _) (integrable_cexpI _ _)).div_const
                _).aestronglyMeasurable
            refine ⟨hm1.add hm2, fun y ↦ ?_⟩
            obtain ⟨_, hD1, hD2⟩ := hDom' a ha_Ioo y
            have hb1 : |(∫ z, (z - y) ∂K a y) / a| ≤ C * (1 + |y|) := by
              rw [abs_div, abs_of_pos ha_pos, div_le_iff₀ ha_pos]; linarith
            have hb2 : (∫ z, (z - y) ^ 2 ∂K a y) / a ≤ C * (1 + y ^ 2) := by
              rw [div_le_iff₀ ha_pos]; linarith
            have hsq_nn : 0 ≤ (∫ z, (z - y) ^ 2 ∂K a y) / a :=
              div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) ha_pos.le
            have hθ := hξ_le (s + a) hsa
            have hθ2 : ξ (s + a) ^ 2 ≤ |ξ₀| ^ 2 := by
              rw [← sq_abs (ξ (s + a))]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
            dsimp only [G₀, domG]
            refine (norm_add_le _ _).trans (add_le_add ?_ (hcexp_le s a y ha_pos hsa))
            rw [norm_mul, norm_cexpI, one_mul]
            refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
              exact (mul_le_mul hθ hb1 (abs_nonneg _) (abs_nonneg ξ₀)).trans_eq (by ring)
            · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity),
                abs_of_nonneg hsq_nn]
              exact (mul_le_mul (div_le_div_of_nonneg_right hθ2 zero_le_two) hb2 hsq_nn
                (by positivity)).trans_eq (by ring)
          have hG₀_pw' : ∀ y : ℝ, Tendsto (fun a : ℝ ↦ G₀ a y) (𝓝[>] 0)
              (𝓝 (-(((ξ s ^ 2 : ℝ) : ℂ) * cexpI (ξ s) y))) := fun y ↦ by
            have hDr := tendsto_div_of_sub_littleO (c := -y) ((hDrift y).congr fun a ↦ by ring)
            have hDf := tendsto_div_of_sub_littleO (hDiff y)
            have hc1 : Tendsto (fun a : ℝ ↦ cexpI (ξ (s + a)) y)
                (𝓝[>] 0) (𝓝 (cexpI (ξ s) y)) :=
              ((hasDerivAt_cexpI_comp (hasDerivAt_id' (ξ s)) y).continuousAt.tendsto).comp hξ_lim
            have ht1 : Tendsto
                (fun a : ℝ ↦ ((ξ (s + a) * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ))
                (𝓝[>] 0) (𝓝 ((-ξ s * y : ℝ) : ℂ)) := by
              have hr1 := hξ_lim.mul hDr; rw [show ξ s * -y = -ξ s * y by ring] at hr1
              exact (Complex.continuous_ofReal.tendsto _).comp hr1
            have ht2 : Tendsto
                (fun a : ℝ ↦
                  ((((ξ (s + a) ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)))
                (𝓝[>] 0) (𝓝 ((ξ s ^ 2 : ℝ) : ℂ)) := by
              have hr2 := ((hξ_lim.pow 2).div_const 2).mul hDf
              rw [show (ξ s ^ 2 / 2) * 2 = ξ s ^ 2 by ring] at hr2
              exact (Complex.continuous_ofReal.tendsto _).comp hr2
            have hc2 : Tendsto
                (fun a : ℝ ↦ (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ))
                (𝓝[>] 0) (𝓝 (cexpI (ξ s) y * (Complex.I * ((ξ s * y : ℝ) : ℂ)))) :=
              (hasDerivAt_cexpI_comp (hd_ξ s) y).tendsto_slope_zero_right.congr
                fun a ↦ by simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
            convert (hc1.mul ((ht1.const_mul Complex.I).sub ht2)).add hc2 using 2
            simp only [Complex.ofReal_mul, Complex.ofReal_neg]; ring
          have hlim_G₀ := tendsto_integral_filter_of_dominated_convergence _
            (hG₀_ev.mono fun _ h ↦ h.1) (hG₀_ev.mono fun _ h ↦ ae_of_all _ h.2) hdomG_int
            (ae_of_all _ hG₀_pw')
          rw [integral_neg, integral_const_mul, ← charFun_eq_integral_cexpI] at hlim_G₀
          exact hlim_G₀
        have hQ₀_lim : Tendsto (fun a : ℝ ↦ ‖Q₀ a‖) (𝓝[>] 0) (𝓝 0) := by
          have hd_sq : HasDerivAt (fun u : ℝ ↦ ξ u ^ 2 / 2) (ξ s ^ 2) s := by
            have hm : HasDerivAt (fun u : ℝ ↦ (ξ u * ξ u) / 2) (ξ s ^ 2) s :=
              (((hd_ξ s).fun_mul (hd_ξ s)).div_const (2 : ℝ)).congr_deriv (by ring)
            exact (show (fun u : ℝ ↦ (ξ u * ξ u) / 2) = fun u ↦ ξ u ^ 2 / 2 from
              funext fun u ↦ by rw [sq]) ▸ hm
          have hd_ef : HasDerivAt expFactor (((ξ s ^ 2 : ℝ) : ℂ) * expFactor s) s := by
            dsimp [expFactor]; simpa only [mul_comm] using hd_sq.ofReal_comp.cexp
          have hef_cont :
              Tendsto (fun a : ℝ ↦ expFactor (s + a)) (𝓝[>] 0) (𝓝 (expFactor s)) := by
            have hc : Continuous (fun a : ℝ ↦ expFactor (s + a)) := by
              dsimp [expFactor, ξ]; fun_prop
            simpa only [add_zero] using (hc.continuousWithinAt (x := 0) (s := Ioi 0)).tendsto
          have hef_slope : Tendsto (fun a : ℝ ↦ (expFactor (s + a) - expFactor s) / (a : ℂ))
              (𝓝[>] 0) (𝓝 (((ξ s ^ 2 : ℝ) : ℂ) * expFactor s)) :=
            hd_ef.tendsto_slope_zero_right.congr fun a ↦ by
              simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]
          have hQ₀_c : Tendsto Q₀ (𝓝[>] 0) (𝓝 0) := by
            convert (hef_cont.mul hG₀_lim).add (hef_slope.mul_const (Φ s)) using 2
            ring
          simpa using hQ₀_c.norm
        -- Limits of the three real integrals in `R_{M, ε}(a, s)`
        have hSq_lim : Tendsto
            (fun a : ℝ ↦ ∫ y, ((∫ z, (z - y) ^ 2 ∂K a y) / a) ∂μs s)
            (𝓝[>] 0) (𝓝 2) := by
          have hev : ∀ᶠ a in 𝓝[>] 0,
              AEStronglyMeasurable (fun y ↦ (∫ z, (z - y) ^ 2 ∂K a y) / a) (μs s) ∧
                ∀ y : ℝ, ‖(∫ z, (z - y) ^ 2 ∂K a y) / a‖ ≤ C * (1 + y ^ 2) := by
            filter_upwards [Ioo_mem_nhdsGT ha₀] with a ha
            obtain ⟨-, hi2, -⟩ :=
              kernel_step_integrable_on_mu hMarkov ha₀ hC hDom' (μs s) hInt_y2_s ha
            refine ⟨hi2.aestronglyMeasurable, fun y ↦ ?_⟩
            rw [Real.norm_eq_abs, abs_of_nonneg
              (div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) ha.1.le), div_le_iff₀ ha.1]
            linarith [(hDom' a ha y).2.2]
          have hlim := tendsto_integral_filter_of_dominated_convergence _
            (hev.mono fun _ h ↦ h.1) (hev.mono fun _ h ↦ ae_of_all _ h.2)
            ((iAdd (integrable_const 1) hInt_y2_s).const_mul C)
            (ae_of_all _ fun y ↦ tendsto_div_of_sub_littleO (hDiff y))
          rwa [integral_const, probReal_univ, one_smul] at hlim
        have hProb_lim : Tendsto
            (fun a : ℝ ↦ ∫ y, ((K a y).real {z : ℝ | ε < |z - y|} / a) ∂μs s)
            (𝓝[>] 0) (𝓝 0) := by
          have hev : ∀ᶠ a in 𝓝[>] 0,
              AEStronglyMeasurable (fun y ↦ (K a y).real {z : ℝ | ε < |z - y|} / a) (μs s) ∧
                ∀ y : ℝ, ‖(K a y).real {z : ℝ | ε < |z - y|} / a‖ ≤
                  (C / ε ^ 2) * (1 + y ^ 2) := by
            filter_upwards [Ioo_mem_nhdsGT ha₀] with a ha
            obtain ⟨-, -, hprob_i⟩ :=
              kernel_step_integrable_on_mu hMarkov ha₀ hC hDom' (μs s) hInt_y2_s ha
            obtain ⟨hi3, hb3⟩ := hprob_i ε hε
            refine ⟨hi3.aestronglyMeasurable, fun y ↦ ?_⟩
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg measureReal_nonneg ha.1.le)]
            exact hb3 y
          have hlim := tendsto_integral_filter_of_dominated_convergence _
            (hev.mono fun _ h ↦ h.1) (hev.mono fun _ h ↦ ae_of_all _ h.2)
            ((iAdd (integrable_const 1) hInt_y2_s).const_mul (C / ε ^ 2))
            (ae_of_all _ fun y ↦ hProbTail y ε hε)
          rwa [integral_zero] at hlim
        have hDr_hM_lim : Tendsto
            (fun a : ℝ ↦ -∫ y, (tailExcessDeriv M_param y *
              ((∫ z, (z - y) ∂K a y) / a)) ∂μs s)
            (𝓝[>] 0) (𝓝 (ρ_ext s)) := by
          have hev : ∀ᶠ a in 𝓝[>] 0,
              AEStronglyMeasurable
                (fun y ↦ tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a)) (μs s) ∧
                ∀ y : ℝ, ‖tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a)‖ ≤
                  4 * C * (1 + y ^ 2) := by
            filter_upwards [Ioo_mem_nhdsGT ha₀] with a ha
            obtain ⟨hi1, -, -⟩ :=
              kernel_step_integrable_on_mu hMarkov ha₀ hC hDom' (μs s) hInt_y2_s ha
            have hm : AEStronglyMeasurable
                (fun y ↦ tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a)) (μs s) :=
              (by unfold tailExcessDeriv; fun_prop :
                Continuous (tailExcessDeriv M_param)).aestronglyMeasurable.mul
                hi1.aestronglyMeasurable
            refine ⟨hm, fun y ↦ ?_⟩
            rw [Real.norm_eq_abs, abs_mul]
            have hb1 : |(∫ z, (z - y) ∂K a y) / a| ≤ C * (1 + |y|) := by
              rw [abs_div, abs_of_pos ha.1, div_le_iff₀ ha.1]; linarith [(hDom' a ha y).2.1]
            have hm1 := mul_le_mul (abs_tailExcessDeriv_le M_param y) hb1 (abs_nonneg _)
              (by positivity)
            have hy_q : |y| * (1 + |y|) ≤ 2 * (1 + y ^ 2) := by
              nlinarith [sq_abs y, sq_nonneg (|y| - 1), abs_nonneg y]
            nlinarith [mul_le_mul_of_nonneg_left hy_q hC]
          have hpw : ∀ y : ℝ, Tendsto
              (fun a : ℝ ↦ tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a))
              (𝓝[>] 0) (𝓝 (-driftExcess M_param y)) := fun y ↦ by
            have hDr := tendsto_div_of_sub_littleO (c := -y) ((hDrift y).congr fun a ↦ by ring)
            convert hDr.const_mul (tailExcessDeriv M_param y) using 2
            unfold driftExcess; ring
          have hlim := tendsto_integral_filter_of_dominated_convergence _
            (hev.mono fun _ h ↦ h.1) (hev.mono fun _ h ↦ ae_of_all _ h.2)
            ((iAdd (integrable_const 1) hInt_y2_s).const_mul (4 * C))
            (ae_of_all _ hpw)
          rw [integral_neg] at hlim
          have hs_clamp : max 0 (min t s) = s := by
            rw [min_eq_right hs.2.le, max_eq_right hs.1]
          simpa [ρ_ext, hs_clamp] using hlim.neg
        have hJ_slope : Tendsto (fun a : ℝ ↦ (J_fn (s + a) - J_fn s) / a)
            (𝓝[>] 0) (𝓝 (q_fn s)) :=
          (hasDerivAt_primitive hq_cont s).tendsto_slope_zero_right.congr fun a ↦ by
            rw [smul_eq_mul, inv_mul_eq_div]
        -- Assemble `R_s(a)` and prove `R_s(a) → 0` and `(F_fn (s + a) - F_fn s) / a ≤ R_s a`
        set R_s : ℝ → ℝ := fun a ↦
          ‖Q₀ a‖ +
            C₀ * |ξ₀| ^ 3 * ε * (∫ y, ((∫ z, (z - y) ^ 2 ∂K a y) / a) ∂μs s) +
            8 * C₀ * ξ₀ ^ 2 * M_param ^ 2 *
              (∫ y, ((K a y).real {z : ℝ | ε < |z - y|} / a) ∂μs s) +
            8 * C₀ * ξ₀ ^ 2 *
              (-∫ y, (tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a)) ∂μs s) -
            (J_fn (s + a) - J_fn s) / a
        have hRs_lim : Tendsto R_s (𝓝[>] 0) (𝓝 0) := by
          have hc := (((hQ₀_lim.add (hSq_lim.const_mul (C₀ * |ξ₀| ^ 3 * ε))).add
            (hProb_lim.const_mul (8 * C₀ * ξ₀ ^ 2 * M_param ^ 2))).add
            (hDr_hM_lim.const_mul (8 * C₀ * ξ₀ ^ 2))).sub hJ_slope
          convert hc using 2
          dsimp [q_fn]; ring
        refine ⟨R_s, hRs_lim, ?_⟩
        filter_upwards [Ioo_mem_nhdsGT (lt_min ha₀ (sub_pos.mpr hs.2))] with a ha
        have ha_pos := ha.1
        have ha_Ioo : a ∈ Ioo 0 a₀ := ⟨ha_pos, lt_of_lt_of_le ha.2 (min_le_left _ _)⟩
        have hsa : s + a ≤ t := by linarith [lt_of_lt_of_le ha.2 (min_le_right _ _)]
        obtain ⟨hi1, hi2, hprob_i⟩ :=
          kernel_step_integrable_on_mu hMarkov ha₀ hC hDom' (μs s) hInt_y2_s ha_Ioo
        obtain ⟨hi3, -⟩ := hprob_i ε hε
        -- Relate `(Ψ (s + a) - Ψ s) / a` to `Q₀ a + expFactor (s + a) * ∫ rem_y ∂μs s`
        set rem_y : ℝ → ℂ := fun y ↦
          cexpI (ξ (s + a)) y *
            ((∫ z, cexpRem (ξ (s + a) * (z - y)) ∂K a y) / (a : ℂ))
        have hG₀_int : Integrable (G₀ a) (μs s) := by
          have hm1 : Integrable
              (fun y ↦ cexpI (ξ (s + a)) y *
                (Complex.I * ((ξ (s + a) * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ) -
                  (((ξ (s + a) ^ 2 / 2) * ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)))
              (μs s) := by
            have hsub_c : Integrable
                (fun y ↦
                  Complex.I * ((ξ (s + a) * ((∫ z, (z - y) ∂K a y) / a) : ℝ) : ℂ) -
                    (((ξ (s + a) ^ 2 / 2) *
                      ((∫ z, (z - y) ^ 2 ∂K a y) / a) : ℝ) : ℂ)) (μs s) :=
              iSub ((hi1.const_mul (ξ (s + a))).ofReal.const_mul Complex.I)
                ((hi2.const_mul (ξ (s + a) ^ 2 / 2)).ofReal)
            exact hsub_c.norm.mono'
              ((continuous_cexpI _).aestronglyMeasurable.mul hsub_c.aestronglyMeasurable)
              (ae_of_all _ fun y ↦ by rw [norm_mul, norm_cexpI, one_mul])
          exact iAdd hm1 ((iSub (integrable_cexpI _ _) (integrable_cexpI _ _)).div_const _)
        have htot_int : Integrable (fun y ↦
            (charFun (K a y) (ξ (s + a)) - cexpI (ξ (s + a)) y) / (a : ℂ) +
              (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)) (μs s) :=
          iAdd ((iSub (hchar_int s a hs.1 ha_pos) (integrable_cexpI _ _)).div_const _)
            ((iSub (integrable_cexpI _ _) (integrable_cexpI _ _)).div_const _)
        have htot_eq : (fun y ↦
            (charFun (K a y) (ξ (s + a)) - cexpI (ξ (s + a)) y) / (a : ℂ) +
              (cexpI (ξ (s + a)) y - cexpI (ξ s) y) / (a : ℂ)) =
            fun y ↦ G₀ a y + rem_y y := by
          ext y; rw [hdecomp a ha_Ioo (ξ (s + a)) y]; dsimp [G₀, rem_y]; ring
        have hrem_int : Integrable rem_y (μs s) := by
          have h := iSub htot_int hG₀_int
          exact h.congr (ae_of_all _ fun y ↦ by
            have hy := congr_fun htot_eq y; dsimp at hy ⊢; rw [hy]; ring)
        have hΨ_decomp : (Ψ (s + a) - Ψ s) / (a : ℂ) =
            Q₀ a + expFactor (s + a) * ∫ y, rem_y y ∂μs s := by
          have halg : (Ψ (s + a) - Ψ s) / (a : ℂ) =
              expFactor (s + a) * ((Φ (s + a) - Φ s) / (a : ℂ)) +
                ((expFactor (s + a) - expFactor s) / (a : ℂ)) * Φ s := by
            dsimp [Ψ]; field_simp [Complex.ofReal_ne_zero.mpr ha_pos.ne']; ring
          rw [halg, hΦ_decomp s a hs.1 ha_pos, htot_eq, integral_add hG₀_int hrem_int]
          dsimp [Q₀]; ring
        -- Pointwise bound on `‖rem_y y‖` via `norm_cexpRem_le_probTail_bregman`
        set bregStep : ℝ → ℝ := fun y ↦ (∫ z, bregmanExcess M_param y z ∂K a y) / a
        have hbreg_eq : ∀ y : ℝ, bregStep y =
            (∫ z, (tailExcess M_param z - tailExcess M_param y) ∂K a y) / a -
              tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a) := fun y ↦ by
          have := hMarkov a ha_pos
          have hInt2 := (hDom' a ha_Ioo y).1
          have hInt1 := integrable_sub_of_integrable_sq hInt2
          have hb_int : Integrable (fun z ↦ bregmanExcess M_param y z) (K a y) :=
            (hInt2.const_mul 6).mono' (by unfold bregmanExcess tailExcess truncSq; fun_prop)
              (ae_of_all _ fun z ↦ by
                rw [Real.norm_eq_abs, abs_of_nonneg (bregmanExcess_nonneg_and_le hMp y z).1]
                exact (bregmanExcess_nonneg_and_le hMp y z).2)
          have hexp_z : (fun z : ℝ ↦ tailExcess M_param z - tailExcess M_param y) =
              fun z ↦ tailExcessDeriv M_param y * (z - y) + bregmanExcess M_param y z := by
            ext z; unfold bregmanExcess; ring
          rw [hexp_z, integral_add (hInt1.const_mul _) hb_int, integral_const_mul]
          dsimp [bregStep]; field_simp [ha_pos.ne']; ring
        have hdiff_H_int : Integrable
            (fun y ↦
              (∫ z, (tailExcess M_param z - tailExcess M_param y) ∂K a y) / a) (μs s) := by
          have := hMarkov a ha_pos
          have hφ_sa : Integrable (tailExcess M_param) ((μs s ⊗ₘ K a).map Prod.snd) := by
            rw [← Measure.snd, Measure.snd_compProd, hμs_bind s a hs.1 ha_pos]
            exact hH_info.1 (s + a) ⟨by linarith [hs.1], hsa⟩
          have hφ_prod :
              Integrable (fun p : ℝ × ℝ ↦ tailExcess M_param p.2) (μs s ⊗ₘ K a) :=
            (integrable_map_measure (by unfold tailExcess truncSq; fun_prop :
              Continuous (tailExcess M_param)).aestronglyMeasurable measurable_snd.aemeasurable).mp
              hφ_sa
          have h_outer : Integrable (fun y ↦ ∫ z, tailExcess M_param z ∂K a y) (μs s) := by
            have hi := hφ_prod.integral_compProd
            simp only [Kernel.prodMkLeft_apply, Kernel.const_apply] at hi; exact hi
          refine ((iSub h_outer (hH_info.1 s hs_Icc)).div_const a).congr (ae_of_all _ fun y ↦ ?_)
          have hInt_K : Integrable (tailExcess M_param) (K a y) := by
            have hInt2 := (hDom' a ha_Ioo y).1
            refine (iAdd (integrable_const (2 * y ^ 2)) (hInt2.const_mul 2)).mono'
              (by unfold tailExcess truncSq; fun_prop) (ae_of_all _ fun z ↦ ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (tailExcess_bounds hMp z).1]
            nlinarith [(tailExcess_bounds hMp z).2.1, sq_nonneg (2 * y - z)]
          dsimp only
          rw [integral_sub hInt_K (integrable_const _), integral_const, probReal_univ, one_smul]
        have hDr_hM_int : Integrable
            (fun y ↦ tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a)) (μs s) := by
          refine ((iAdd (integrable_const 1) hInt_y2_s).const_mul (4 * C)).mono'
            ((by unfold tailExcessDeriv; fun_prop :
              Continuous (tailExcessDeriv M_param)).aestronglyMeasurable.mul
              hi1.aestronglyMeasurable)
            (ae_of_all _ fun y ↦ ?_)
          rw [Real.norm_eq_abs, abs_mul]
          have hb1 : |(∫ z, (z - y) ∂K a y) / a| ≤ C * (1 + |y|) := by
            rw [abs_div, abs_of_pos ha_pos, div_le_iff₀ ha_pos]; linarith [(hDom' a ha_Ioo y).2.1]
          have hm1 := mul_le_mul (abs_tailExcessDeriv_le M_param y) hb1 (abs_nonneg _)
            (by positivity)
          have hy_q : |y| * (1 + |y|) ≤ 2 * (1 + y ^ 2) := by
            nlinarith [sq_abs y, sq_nonneg (|y| - 1), abs_nonneg y]
          nlinarith [mul_le_mul_of_nonneg_left hy_q hC]
        have hbreg_int : Integrable bregStep (μs s) :=
          (iSub hdiff_H_int hDr_hM_int).congr (ae_of_all _ fun y ↦ (hbreg_eq y).symm)
        have hrem_y_le : ∀ y : ℝ, ‖rem_y y‖ ≤
            |ξ₀| ^ 3 * ε * ((∫ z, (z - y) ^ 2 ∂K a y) / a) +
              8 * ξ₀ ^ 2 * M_param ^ 2 * ((K a y).real {z : ℝ | ε < |z - y|} / a) +
              8 * ξ₀ ^ 2 * bregStep y := fun y ↦ by
          have := hMarkov a ha_pos
          have hInt2 := (hDom' a ha_Ioo y).1
          have hms1 : MeasurableSet {w : ℝ | ε < |w - y|} :=
            (isOpen_lt continuous_const (continuous_id.sub continuous_const).abs).measurableSet
          have hb_int_z : Integrable (fun z ↦ bregmanExcess M_param y z) (K a y) :=
            (hInt2.const_mul 6).mono' (by unfold bregmanExcess tailExcess truncSq; fun_prop)
              (ae_of_all _ fun z ↦ by
                rw [Real.norm_eq_abs, abs_of_nonneg (bregmanExcess_nonneg_and_le hMp y z).1]
                exact (bregmanExcess_nonneg_and_le hMp y z).2)
          have hrhs_z : Integrable (fun z : ℝ ↦
              |ξ₀| ^ 3 * ε * (z - y) ^ 2 +
                8 * ξ₀ ^ 2 * M_param ^ 2 *
                  ({w : ℝ | ε < |w - y|}.indicator (fun _ ↦ (1 : ℝ)) z) +
                8 * ξ₀ ^ 2 * bregmanExcess M_param y z) (K a y) :=
            iAdd (iAdd (hInt2.const_mul _)
              (((integrable_const (1 : ℝ)).indicator hms1).const_mul _))
              (hb_int_z.const_mul _)
          dsimp [rem_y]
          rw [norm_mul, norm_cexpI, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ha_pos]
          have hint_z : ‖∫ z, cexpRem (ξ (s + a) * (z - y)) ∂K a y‖ ≤
              |ξ₀| ^ 3 * ε * (∫ z, (z - y) ^ 2 ∂K a y) +
                8 * ξ₀ ^ 2 * M_param ^ 2 * (K a y).real {z : ℝ | ε < |z - y|} +
                8 * ξ₀ ^ 2 * ∫ z, bregmanExcess M_param y z ∂K a y := by
            refine (norm_integral_le_of_norm_le hrhs_z (ae_of_all _ fun z ↦ ?_)).trans_eq ?_
            · have h3 := norm_cexpRem_le_probTail_bregman (abs_nonneg ξ₀) (hξ_le (s + a) hsa)
                hε hMp y z
              rwa [sq_abs ξ₀] at h3
            · rw [integral_add (iAdd (hInt2.const_mul _)
                (((integrable_const (1 : ℝ)).indicator hms1).const_mul _))
                (hb_int_z.const_mul _),
                integral_add (hInt2.const_mul _)
                  (((integrable_const (1 : ℝ)).indicator hms1).const_mul _),
                integral_const_mul, integral_const_mul, integral_const_mul,
                integral_indicator_const _ hms1, smul_eq_mul, mul_one]
          exact (div_le_div_of_nonneg_right hint_z ha_pos.le).trans_eq (by
            dsimp [bregStep]; simp only [div_eq_mul_inv]; ring)
        have hrem_int_le : ‖∫ y, rem_y y ∂μs s‖ ≤
            |ξ₀| ^ 3 * ε * (∫ y, ((∫ z, (z - y) ^ 2 ∂K a y) / a) ∂μs s) +
              8 * ξ₀ ^ 2 * M_param ^ 2 *
                (∫ y, ((K a y).real {z : ℝ | ε < |z - y|} / a) ∂μs s) +
              8 * ξ₀ ^ 2 * ((H_fn (s + a) - H_fn s) / a -
                ∫ y, (tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a)) ∂μs s) := by
          have hrhs_y := iAdd (iAdd (hi2.const_mul (|ξ₀| ^ 3 * ε))
            (hi3.const_mul (8 * ξ₀ ^ 2 * M_param ^ 2))) (hbreg_int.const_mul (8 * ξ₀ ^ 2))
          refine (norm_integral_le_of_norm_le hrhs_y (ae_of_all _ hrem_y_le)).trans_eq ?_
          rw [integral_add (iAdd (hi2.const_mul _) (hi3.const_mul _)) (hbreg_int.const_mul _),
            integral_add (hi2.const_mul _) (hi3.const_mul _),
            integral_const_mul, integral_const_mul, integral_const_mul]
          have hb_int_eq : ∫ y, bregStep y ∂μs s =
              (H_fn (s + a) - H_fn s) / a -
                ∫ y, (tailExcessDeriv M_param y * ((∫ z, (z - y) ∂K a y) / a)) ∂μs s := by
            rw [integral_congr_ae (ae_of_all _ hbreg_eq),
              integral_sub hdiff_H_int hDr_hM_int, ← hH_info.2.1 s a hs.1 ha_Ioo hsa]
          rw [hb_int_eq]
        have hΨ_norm : ‖(Ψ (s + a) - Ψ s) / (a : ℂ)‖ ≤
            ‖Q₀ a‖ + C₀ * ‖∫ y, rem_y y ∂μs s‖ := by
          rw [hΨ_decomp]
          exact (norm_add_le _ _).trans (add_le_add le_rfl
            ((norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hexpFactor_le (s + a) hsa)
              (norm_nonneg _))))
        have hRe_quot : ((w * Ψ (s + a)).re - (w * Ψ s).re) / a ≤
            ‖(Ψ (s + a) - Ψ s) / (a : ℂ)‖ := by
          have hre_eq : ((w * Ψ (s + a)).re - (w * Ψ s).re) / a =
              (w * ((Ψ (s + a) - Ψ s) / (a : ℂ))).re := by
            have hdiv_c : (Ψ (s + a) - Ψ s) / (a : ℂ) =
                ((a⁻¹ : ℝ) : ℂ) * (Ψ (s + a) - Ψ s) := by
              simp [Complex.ofReal_inv, div_eq_inv_mul]
            rw [hdiv_c]
            simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
              Complex.ofReal_re, Complex.ofReal_im, div_eq_inv_mul]
            ring
          rw [hre_eq]
          exact (Complex.re_le_norm _).trans (by
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) hw)
        have hF_quot : (F_fn (s + a) - F_fn s) / a =
            ((w * Ψ (s + a)).re - (w * Ψ s).re) / a -
              8 * C₀ * ξ₀ ^ 2 * ((H_fn (s + a) - H_fn s) / a) -
              (J_fn (s + a) - J_fn s) / a := by
          dsimp [F_fn]; simp only [div_eq_mul_inv]; ring
        rw [hF_quot]
        have hmul_C₀ := mul_le_mul_of_nonneg_left hrem_int_le hC₀_pos.le
        dsimp [R_s]
        linarith
      -- Unpack `F_fn t ≤ F_fn 0`
      have hH0_nn : 0 ≤ H_fn 0 := integral_nonneg fun y ↦ (tailExcess_bounds hMp y).1
      have hJ0 : J_fn 0 = 0 := by simp [J_fn]
      have hJt : J_fn t = 2 * C₀ * |ξ₀| ^ 3 * t * ε +
          8 * C₀ * ξ₀ ^ 2 * ∫ u in (0 : ℝ)..t, ρ_ext u := by
        dsimp [J_fn, q_fn]
        rw [intervalIntegral.integral_add intervalIntegrable_const
          ((hρ_ext_cont.const_mul _).intervalIntegrable 0 t),
          intervalIntegral.integral_const, sub_zero, smul_eq_mul,
          intervalIntegral.integral_const_mul]
        ring
      have hRe_sub : (w * (Ψ t - Ψ 0)).re = (w * Ψ t).re - (w * Ψ 0).re := by
        rw [mul_sub, Complex.sub_re]
      change (w * Ψ t).re - 8 * C₀ * ξ₀ ^ 2 * H_fn t - J_fn t ≤
        (w * Ψ 0).re - 8 * C₀ * ξ₀ ^ 2 * H_fn 0 - J_fn 0 at hF_le
      rw [hJ0, hJt] at hF_le
      have hH0_prod : 0 ≤ 8 * C₀ * ξ₀ ^ 2 * H_fn 0 :=
        mul_nonneg (by positivity) hH0_nn
      linarith
    -- First let `ε → 0⁺` for fixed `M_param`
    have h_for_M : ∀ M_param : ℝ, 0 < M_param →
        (w * (Ψ t - Ψ 0)).re ≤
          8 * C₀ * ξ₀ ^ 2 * (∫ y, tailExcess M_param y ∂μs t) +
            8 * C₀ * ξ₀ ^ 2 *
              ∫ u in (0 : ℝ)..t, (∫ y, driftExcess M_param y ∂μs (max 0 (min t u))) := by
      intro M_param hMp
      refine le_of_forall_pos_lt_add fun δ hδ ↦ ?_
      set ε : ℝ := δ / (2 * C₀ * |ξ₀| ^ 3 * t + 1)
      have hε : 0 < ε := by positivity
      have h1 := h_for_M_ε M_param hMp ε hε
      have h2 : 2 * C₀ * |ξ₀| ^ 3 * t * ε < δ := by
        rw [show 2 * C₀ * |ξ₀| ^ 3 * t * ε =
            δ * ((2 * C₀ * |ξ₀| ^ 3 * t) / (2 * C₀ * |ξ₀| ^ 3 * t + 1)) by
          dsimp [ε]; simp only [div_eq_mul_inv]; ring]
        exact mul_lt_of_lt_one_right hδ ((div_lt_one (by positivity)).mpr (by linarith))
      linarith
    -- Next let `M_param = (n : ℝ) + 1 → ∞`
    set Mn : ℕ → ℝ := fun n ↦ (n : ℝ) + 1
    have hMn_pos : ∀ n : ℕ, 0 < Mn n := fun n ↦ by dsimp [Mn]; positivity
    have hMn_inv_sq : Tendsto (fun n : ℕ ↦ 1 / Mn n ^ 2) atTop (𝓝 0) := by
      have h1 : Tendsto Mn atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h2 : Tendsto (fun n : ℕ ↦ Mn n ^ 2) atTop atTop := by
        simpa [sq] using h1.atTop_mul_atTop₀ h1
      exact (tendsto_inv_atTop_zero.comp h2).congr fun n ↦ by simp [one_div]
    have hH_tendsto :
        Tendsto (fun n : ℕ ↦ ∫ y, tailExcess (Mn n) y ∂μs t) atTop (𝓝 0) := by
      have := hμs_prob t
      obtain ⟨hInt_t, -⟩ := hμs_sq t ⟨ht.le, le_rfl⟩
      have hlim := tendsto_integral_of_dominated_convergence (fun y : ℝ ↦ y ^ 2)
        (fun n ↦ (by unfold tailExcess truncSq; fun_prop :
          Continuous (tailExcess (Mn n))).aestronglyMeasurable)
        hInt_t
        (fun n ↦ ae_of_all _ fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (tailExcess_bounds (hMn_pos n) y).1]
          exact (tailExcess_bounds (hMn_pos n) y).2.1)
        (ae_of_all _ fun y ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds
          (by simpa [mul_zero] using (hMn_inv_sq.const_mul (y ^ 4 / 2)))
          (fun n ↦ (tailExcess_bounds (hMn_pos n) y).1)
          (fun n ↦ (tailExcess_bounds (hMn_pos n) y).2.2.trans_eq
            (by rw [← div_div, div_eq_mul_inv])))
      rwa [integral_zero] at hlim
    have hρ_int_tendsto : Tendsto
        (fun n : ℕ ↦ ∫ u in (0 : ℝ)..t,
          (∫ y, driftExcess (Mn n) y ∂μs (max 0 (min t u)))) atTop (𝓝 0) := by
      simp_rw [intervalIntegral.integral_of_le ht.le]
      have hclamp_mem : ∀ u : ℝ, max 0 (min t u) ∈ Icc 0 t := fun u ↦
        ⟨le_max_left _ _, max_le ht.le (min_le_left _ _)⟩
      have hρ_n_cont : ∀ n : ℕ,
          Continuous (fun u : ℝ ↦ ∫ y, driftExcess (Mn n) y ∂μs (max 0 (min t u))) :=
        fun n ↦ by
          have hinfo := subquad_semigroup_info
            hMarkov ha₀ hC hDom' hM₀_nn hμs_prob hμs_bind hμs_sq
            (φ := driftExcess (Mn n)) (φ' := driftExcessDeriv (Mn n))
            (by unfold driftExcess tailExcessDeriv; fun_prop)
            zero_le_two (by norm_num : (0 : ℝ) ≤ 8) (by norm_num : (0 : ℝ) ≤ 44)
            (fun y ↦ by
              rw [abs_of_nonneg (driftExcess_bounds (hMn_pos n) y).1]
              exact (driftExcess_bounds (hMn_pos n) y).2.1)
            (fun y ↦ (driftExcess_bounds (hMn_pos n) y).2.2.2)
            (abs_driftExcess_taylor_le (hMn_pos n))
          exact hinfo.2.2.comp_continuous
            (continuous_const.max (continuous_const.min continuous_id)) hclamp_mem
      have hpw_u : ∀ u : ℝ, Tendsto
          (fun n : ℕ ↦ ∫ y, driftExcess (Mn n) y ∂μs (max 0 (min t u))) atTop (𝓝 0) :=
        fun u ↦ by
          set s_u : ℝ := max 0 (min t u)
          have := hμs_prob s_u
          obtain ⟨hInt_su, -⟩ := hμs_sq s_u (hclamp_mem u)
          have hlim := tendsto_integral_of_dominated_convergence (fun y : ℝ ↦ 2 * y ^ 2)
            (fun n ↦ (by unfold driftExcess tailExcessDeriv; fun_prop :
              Continuous (driftExcess (Mn n))).aestronglyMeasurable)
            (hInt_su.const_mul 2)
            (fun n ↦ ae_of_all _ fun y ↦ by
              rw [Real.norm_eq_abs, abs_of_nonneg (driftExcess_bounds (hMn_pos n) y).1]
              exact (driftExcess_bounds (hMn_pos n) y).2.1)
            (ae_of_all _ fun y ↦ tendsto_of_tendsto_of_tendsto_of_le_of_le
              tendsto_const_nhds
              (by simpa [mul_zero] using (hMn_inv_sq.const_mul (2 * y ^ 4)))
              (fun n ↦ (driftExcess_bounds (hMn_pos n) y).1)
              (fun n ↦ (driftExcess_bounds (hMn_pos n) y).2.2.1.trans_eq
                (by rw [div_eq_mul_inv])))
          rwa [integral_zero] at hlim
      have hdom_const : Integrable (fun _ : ℝ ↦ 2 * M₀) (volume.restrict (Ioc 0 t)) :=
        integrableOn_const (hs := measure_Ioc_lt_top.ne)
      have hlim_outer := tendsto_integral_of_dominated_convergence (fun _ : ℝ ↦ 2 * M₀)
        (fun n ↦ (hρ_n_cont n).aestronglyMeasurable)
        hdom_const
        (fun n ↦ ae_of_all _ fun u ↦ by
          set s_u : ℝ := max 0 (min t u)
          have := hμs_prob s_u
          obtain ⟨hInt_su, hle_su⟩ := hμs_sq s_u (hclamp_mem u)
          have hnn : 0 ≤ ∫ y, driftExcess (Mn n) y ∂μs s_u :=
            integral_nonneg fun y ↦ (driftExcess_bounds (hMn_pos n) y).1
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          have hmono := integral_mono
            ((hInt_su.const_mul 2).mono'
              (by unfold driftExcess tailExcessDeriv; fun_prop)
              (ae_of_all _ fun y ↦ by
                rw [Real.norm_eq_abs, abs_of_nonneg (driftExcess_bounds (hMn_pos n) y).1]
                exact (driftExcess_bounds (hMn_pos n) y).2.1))
            (hInt_su.const_mul 2) fun y ↦ (driftExcess_bounds (hMn_pos n) y).2.1
          rw [integral_const_mul] at hmono
          linarith)
        (ae_of_all _ hpw_u)
      rwa [integral_zero] at hlim_outer
    have hrhs_tendsto : Tendsto
        (fun n : ℕ ↦ 8 * C₀ * ξ₀ ^ 2 * (∫ y, tailExcess (Mn n) y ∂μs t) +
          8 * C₀ * ξ₀ ^ 2 *
            ∫ u in (0 : ℝ)..t, (∫ y, driftExcess (Mn n) y ∂μs (max 0 (min t u))))
        atTop (𝓝 0) := by
      simpa using (hH_tendsto.const_mul (8 * C₀ * ξ₀ ^ 2)).add
        (hρ_int_tendsto.const_mul (8 * C₀ * ξ₀ ^ 2))
    exact ge_of_tendsto hrhs_tendsto (Eventually.of_forall fun n ↦ h_for_M (Mn n) (hMn_pos n))
  -- Deduce `Ψ t = Ψ 0` by testing `w = 1, -1, -I, I`
  have hΨ_sub_zero : Ψ t - Ψ 0 = 0 := by
    refine Complex.ext ?_ ?_
    · rw [Complex.zero_re]
      have h1 := hRe_le_zero 1 (by simp)
      have h2 := hRe_le_zero (-1) (by simp)
      simp only [one_mul, neg_mul, Complex.neg_re] at h1 h2
      linarith
    · rw [Complex.zero_im]
      have h1 := hRe_le_zero (-Complex.I) (by simp)
      have h2 := hRe_le_zero Complex.I (by simp)
      simp only [neg_mul, Complex.I_mul, Complex.neg_re] at h1 h2
      linarith
  have hΨ_eq : Ψ t = Ψ 0 := sub_eq_zero.mp hΨ_sub_zero
  -- Conclude `charFun (K t x) ξ₀ = charFun (ouKernel t x) ξ₀`
  have hΦ0 : Φ 0 = cexpI (Real.exp (-t) * ξ₀) x := by
    have hμ0 : μs 0 = Measure.dirac x := by simp [μs]
    dsimp only [Φ, ξ]
    rw [hμ0, sub_zero, charFun_eq_integral_cexpI, integral_dirac]
  have hΦt : Φ t = charFun (K t x) ξ₀ := by
    have hμt : μs t = K t x := by simp [μs, ht]
    dsimp only [Φ, ξ]
    rw [hμt, sub_self, neg_zero, Real.exp_zero, one_mul]
  rw [show Ψ t = Complex.exp (((ξ₀ ^ 2 / 2 : ℝ) : ℂ)) * charFun (K t x) ξ₀ by
        dsimp only [Ψ, expFactor]; rw [hΦt]; simp only [ξ, sub_self, neg_zero, Real.exp_zero,
          one_mul],
      show Ψ 0 = Complex.exp ((((Real.exp (-t) * ξ₀) ^ 2 / 2 : ℝ) : ℂ)) *
        cexpI (Real.exp (-t) * ξ₀) x by dsimp only [Ψ, expFactor]; rw [hΦ0]; simp only [ξ,
          sub_zero]]
    at hΨ_eq
  have hcancel : charFun (K t x) ξ₀ = Complex.exp (-(((ξ₀ ^ 2 / 2 : ℝ) : ℂ))) *
      (Complex.exp ((((Real.exp (-t) * ξ₀) ^ 2 / 2 : ℝ) : ℂ)) *
        cexpI (Real.exp (-t) * ξ₀) x) := by
    rw [← hΨ_eq, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rw [hcancel, cexpI_eq_ofReal_mul, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add,
    charFun_ouKernel ht x ξ₀]
  congr 1
  have hre : (1 - Real.exp (-2 * t)) * ξ₀ ^ 2 / 2 =
      ξ₀ ^ 2 / 2 - (Real.exp (-t) * ξ₀) ^ 2 / 2 := by
    have he2 : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by rw [sq, ← Real.exp_add]; congr 1; ring
    rw [mul_pow, he2]; ring
  have him : (Real.exp (-t) * ξ₀) * x = ξ₀ * (Real.exp (-t) * x) := by ring
  rw [him, hre, Complex.ofReal_sub]; ring

/-! ### Section 5: Automatic Lindeberg Upgrade, Stationary Uniqueness, and Upgraded Statement -/

/-- Automatic tail upgrade for Chapman–Kolmogorov Markov semigroups: under Remark 3.5's printed
Items 1–3 and small-time quadratic moment domination (`QuadDom`), the Lindeberg second-moment tail
holds automatically (`K a = ouKernel a` for all `a > 0`). -/
theorem lindeberg_tail_of_probTail_semigroup {K : ℝ → Kernel ℝ ℝ}
    (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
    (hDrift : ∀ x : ℝ,
      Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a) (𝓝[>] 0) (𝓝 0))
    (hDiff : ∀ x : ℝ,
      Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a) (𝓝[>] 0) (𝓝 0))
    (hProbTail : ∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun a : ℝ ↦ (K a x).real {y : ℝ | ε < |y - x|} / a) (𝓝[>] 0) (𝓝 0))
    (hDom : ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ QuadDom K a₀ C)
    (hSemi : ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → K (s + t) = Kernel.comp (K t) (K s))
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂K a x) / a)
      (𝓝[>] 0) (𝓝 0) := by
  refine (ouKernel_lindeberg_tail x hε).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  rw [eq_ouKernel_of_probTail hMarkov hDrift hDiff hProbTail hDom hSemi ha]

/-- Moment-free stationary-law uniqueness under Ross's printed Item 3 probability tail
(Remark 3.5, `SteinIntro.tex:1009-1024`; `BL8-2`). -/
theorem eq_stdNormalLaw_of_bind_probTail {K : ℝ → Kernel ℝ ℝ}
    (hMarkov : ∀ a : ℝ, 0 < a → IsMarkovKernel (K a))
    (hDrift : ∀ x : ℝ,
      Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a) (𝓝[>] 0) (𝓝 0))
    (hDiff : ∀ x : ℝ,
      Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a) (𝓝[>] 0) (𝓝 0))
    (hProbTail : ∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Tendsto (fun a : ℝ ↦ (K a x).real {y : ℝ | ε < |y - x|} / a) (𝓝[>] 0) (𝓝 0))
    (hDom : ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ QuadDom K a₀ C)
    (hSemi : ∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → K (s + t) = Kernel.comp (K t) (K s))
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hStat : μ.bind (K t₀) = μ) : μ = stdNormalLaw := by
  rw [eq_ouKernel_of_probTail hMarkov hDrift hDiff hProbTail hDom hSemi ht₀] at hStat
  exact eq_stdNormalLaw_of_bind_ouKernel μ ht₀ hStat

/-- Complete Remark 3.5 semigroup uniqueness bundle under Ross's literally printed Items 1–3
(`SteinIntro.tex:1009-1024`; upgrades Part 3 of `Rem3_5_uniqueness_restricted`, resolving
open obligation `BL8-2`):
1. (*Non-vacuity*): `ouKernel` is a Chapman–Kolmogorov Markov semigroup satisfying Items 1–3 and
   small-time quadratic moment domination;
2. (*Semigroup & stationary-law uniqueness*): every Chapman–Kolmogorov Markov semigroup
   `(K t)_{t > 0}` satisfying Ross's printed Items 1–3 and small-time quadratic moment domination
   satisfies `K t = ouKernel t` for all `t > 0`, and every probability measure `μ` with
   `μ.bind (K t₀) = μ` for some `t₀ > 0` equals `stdNormalLaw`. -/
theorem rem3_5_uniqueness_probTail_proof :
    ((∀ a : ℝ, 0 < a → IsMarkovKernel (ouKernel a)) ∧
      (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t →
        ouKernel (s + t) = Kernel.comp (ouKernel t) (ouKernel s)) ∧
      (∀ x : ℝ, Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂ouKernel a x) - (-a * x)) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∀ x : ℝ, Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂ouKernel a x) - 2 * a) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
        Tendsto (fun a : ℝ ↦ (ouKernel a x).real {y : ℝ | ε < |y - x|} / a)
          (nhdsWithin 0 (Ioi 0)) (nhds 0)) ∧
      (∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Ioo 0 a₀, ∀ x : ℝ,
        Integrable (fun y : ℝ ↦ (y - x) ^ 2) (ouKernel a x) ∧
          |∫ y, (y - x) ∂ouKernel a x| ≤ C * a * (1 + |x|) ∧
          (∫ y, (y - x) ^ 2 ∂ouKernel a x) ≤ C * a * (1 + x ^ 2))) ∧
    (∀ K : ℝ → Kernel ℝ ℝ,
      (∀ a : ℝ, 0 < a → IsMarkovKernel (K a)) →
      (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t → K (s + t) = Kernel.comp (K t) (K s)) →
      (∀ x : ℝ, Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) →
      (∀ x : ℝ, Tendsto (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0)) →
      (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
        Tendsto (fun a : ℝ ↦ (K a x).real {y : ℝ | ε < |y - x|} / a)
          (nhdsWithin 0 (Ioi 0)) (nhds 0)) →
      (∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Ioo 0 a₀, ∀ x : ℝ,
        Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x) ∧
          |∫ y, (y - x) ∂K a x| ≤ C * a * (1 + |x|) ∧
          (∫ y, (y - x) ^ 2 ∂K a x) ≤ C * a * (1 + x ^ 2)) →
      (∀ t : ℝ, 0 < t → K t = ouKernel t) ∧
        (∀ μ : Measure ℝ, IsProbabilityMeasure μ →
          (∃ t₀ : ℝ, 0 < t₀ ∧ μ.bind (K t₀) = μ) → μ = stdNormalLaw)) := by
  refine ⟨⟨fun a _ ↦ instIsMarkovKernelOuKernel a, fun _ hs _ ht ↦ ouKernel_comp hs ht,
    ouKernel_drift_littleO, ouKernel_sq_increment_littleO,
    fun x _ hε ↦ ouKernel_tail_littleO x hε,
    ⟨1, zero_lt_one, 2, zero_le_two, ouKernel_quadratic_domination⟩⟩, ?_⟩
  intro K hMarkov hSemi hDrift hDiff hProbTail hDom
  exact ⟨fun _ ht ↦ eq_ouKernel_of_probTail hMarkov hDrift hDiff hProbTail hDom hSemi ht,
    fun μ _ ⟨t₀, ht₀, hStat⟩ ↦
      eq_stdNormalLaw_of_bind_probTail hMarkov hDrift hDiff hProbTail hDom hSemi μ ht₀ hStat⟩

end SteinMethod
