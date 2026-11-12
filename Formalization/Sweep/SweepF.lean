/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs

/-!
# Section 7 Prose & Proof-Interior Sweep (`Formalization.Sweep.SweepF`)

Proves the approved library theorems for Track `SWEEP-F` (`F-D3`,
`docs/reviews/stmts-review-SWEEP-F.md` `SF-6`; `SteinIntro.tex:3862-3870`, `ISSUE-7.6-PROOF`):

* `sec7_3_eq7_12_minimizer_corrected`: for all $C, \mu, \sigma, t > 0$, on the rescaled MGF domain
  $[0, 2\sigma/C)$ of display `(7.12)` (`\label{2134b}`), the printed test point
  $\theta_{\mathrm{sub}} = t(C\mu/\sigma^2 + C t/(2\sigma))^{-1}$ lies in $(0, 2\sigma/C)$ and
  evaluates to Theorem 7.6(2)'s bound, while the unique minimizer of
  $R(\theta) = \exp\bigl(\frac{\mu C\theta^2}{\sigma^2(2 - C\theta/\sigma)} - \theta t\bigr)$ on
  $[0, 2\sigma/C)$ is $\theta_{\min} = \frac{2\sigma}{C}(1 - \sqrt{\mu/(\mu + \sigma t)}) <
  \theta_{\mathrm{sub}}$ with $R(\theta_{\min}) < R(\theta_{\mathrm{sub}})$.
* `not_sec7_3_eq7_12_minimizer_printed`: refutes the printed claim (`SteinIntro.tex:3867-3868`)
  that $\theta_{\mathrm{sub}}$ minimizes the right-hand side of `(7.12)`, even on the narrower
  interval $0 \le \theta < \min\{2/C, 2\sigma/C\}$ (witnessed at $C = \mu = \sigma = 1$, $t = 3$,
  where $\theta_{\mathrm{sub}} = 6/5$ gives $e^{-9/5} > e^{-2}$ at $\theta = 1$).
-/

namespace SteinMethod

private lemma hg_param_sub_eq {C μ σ t r u₀ : ℝ}
    (hC : C ≠ 0) (hu : u₀ ≠ 0) (hr : r ≠ 0)
    (hr_id : (μ + σ * t) * r ^ 2 = μ) :
    (2 * μ * (1 - u₀) ^ 2 / (C * u₀) - 2 * σ * t * (1 - u₀) / C) -
        (2 * μ * (1 - r) ^ 2 / (C * r) - 2 * σ * t * (1 - r) / C) =
      2 * (μ + σ * t) / (C * u₀) * (u₀ - r) ^ 2 := by
  rw [← sub_eq_zero]
  field_simp [hC, hu, hr]
  linear_combination 2 * (r - u₀) * hr_id.symm

/-- **Proof of Theorem 7.6(2), corrected optimization of `(7.12)`** (`\label{2134b}`,
`SteinIntro.tex:3862-3870`; `ISSUE-7.6-PROOF`, `F-D3`): for $C, \mu, \sigma, t > 0$ and
$R(\theta) = \exp\bigl(\frac{\mu C \theta^2}{\sigma^2(2 - C\theta/\sigma)} - \theta t\bigr)$ on
$[0, 2\sigma/C)$, the printed choice $\theta_{\mathrm{sub}} = t(C\mu/\sigma^2 + Ct/(2\sigma))^{-1}$
lies in $(0, 2\sigma/C)$ and evaluates to Theorem 7.6(2)'s bound, while the true minimizer of $R$
on $[0, 2\sigma/C)$ is $\theta_{\min} = \frac{2\sigma}{C}(1 - \sqrt{\mu/(\mu + \sigma t)}) <
\theta_{\mathrm{sub}}$ with $R(\theta_{\min}) < R(\theta_{\mathrm{sub}})$. -/
theorem sec7_3_eq7_12_minimizer_corrected
    {C μ σ t : ℝ} (hC : 0 < C) (hμ : 0 < μ) (hσ : 0 < σ) (ht : 0 < t) :
    let R : ℝ → ℝ := fun θ ↦
      Real.exp ((μ * C * θ ^ 2) / (σ ^ 2 * (2 - C * θ / σ)) - θ * t)
    let θ_sub : ℝ := t * (C * μ / σ ^ 2 + C * t / (2 * σ))⁻¹
    let θ_min : ℝ := (2 * σ / C) * (1 - Real.sqrt (μ / (μ + σ * t)))
    0 < θ_min ∧
      θ_min < θ_sub ∧
      θ_sub < 2 * σ / C ∧
      R θ_sub = Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2 + C / (2 * σ) * t))) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ < 2 * σ / C → R θ_min ≤ R θ) ∧
      R θ_min < R θ_sub := by
  intro R θ_sub θ_min
  have hμσt : 0 < μ + σ * t := by positivity
  have h2μσt : 0 < 2 * μ + σ * t := by positivity
  have hq_pos : 0 < μ / (μ + σ * t) := div_pos hμ hμσt
  have hq_lt1 : μ / (μ + σ * t) < 1 := (div_lt_one hμσt).mpr (by linarith [mul_pos hσ ht])
  set r : ℝ := Real.sqrt (μ / (μ + σ * t))
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hq_pos
  have hr_sq : r ^ 2 = μ / (μ + σ * t) := Real.sq_sqrt hq_pos.le
  have hr_lt1 : r < 1 := by nlinarith
  have hr_id : (μ + σ * t) * r ^ 2 = μ := by
    rw [hr_sq]
    exact mul_div_cancel₀ μ hμσt.ne'
  have h2σC_pos : 0 < 2 * σ / C := by positivity
  have hθ_min_pos : 0 < θ_min := mul_pos h2σC_pos (by linarith)
  have hD_eq : C * μ / σ ^ 2 + C * t / (2 * σ) = C * (2 * μ + σ * t) / (2 * σ ^ 2) := by
    field_simp [hσ.ne']
  have hθ_sub_eq : θ_sub = (2 * σ / C) * (σ * t / (2 * μ + σ * t)) := by
    dsimp [θ_sub]
    rw [hD_eq]
    field_simp [hC.ne', hσ.ne', h2μσt.ne']
  have hθ_min_lt_sub : θ_min < θ_sub := by
    have hsq_gt : (2 * μ) ^ 2 < (r * (2 * μ + σ * t)) ^ 2 := by
      have hprod :
          (μ + σ * t) * ((r * (2 * μ + σ * t)) ^ 2 - (2 * μ) ^ 2) = μ * (σ * t) ^ 2 := by
        linear_combination (2 * μ + σ * t) ^ 2 * hr_id
      have hpos : 0 < μ * (σ * t) ^ 2 := by positivity
      nlinarith
    have hlin : 2 * μ < r * (2 * μ + σ * t) := by
      have hposR : 0 < r * (2 * μ + σ * t) := by positivity
      nlinarith
    have hfrac : 1 - r < σ * t / (2 * μ + σ * t) :=
      (lt_div_iff₀ h2μσt).mpr (by linarith)
    change (2 * σ / C) * (1 - r) < θ_sub
    rw [hθ_sub_eq]
    exact mul_lt_mul_of_pos_left hfrac h2σC_pos
  have hθ_sub_lt : θ_sub < 2 * σ / C := by
    rw [hθ_sub_eq]
    have hfrac_lt1 : σ * t / (2 * μ + σ * t) < 1 := (div_lt_one h2μσt).mpr (by linarith)
    nlinarith
  have hR_sub : R θ_sub = Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2 + C / (2 * σ) * t))) := by
    dsimp [R]
    congr 1
    rw [hθ_sub_eq]
    have hden_sub : 2 - C * ((2 * σ / C) * (σ * t / (2 * μ + σ * t))) / σ =
        4 * μ / (2 * μ + σ * t) := by
      field_simp [hC.ne', hσ.ne', h2μσt.ne']
      ring
    have hD_alt : C * μ / σ ^ 2 + C / (2 * σ) * t = C * (2 * μ + σ * t) / (2 * σ ^ 2) := by
      field_simp [hσ.ne']
    rw [hden_sub, hD_alt]
    field_simp [hC.ne', hμ.ne', hσ.ne', h2μσt.ne']
    ring
  -- Exact completing-the-square identity for the exponent difference on `θ < 2 * σ / C`.
  let g : ℝ → ℝ := fun θ ↦ (μ * C * θ ^ 2) / (σ ^ 2 * (2 - C * θ / σ)) - θ * t
  have hg_param : ∀ u : ℝ, 0 < u →
      g ((2 * σ / C) * (1 - u)) =
        2 * μ * (1 - u) ^ 2 / (C * u) - 2 * σ * t * (1 - u) / C := by
    intro u hu
    dsimp [g]
    have hden : 2 - C * ((2 * σ / C) * (1 - u)) / σ = 2 * u := by
      field_simp [hC.ne', hσ.ne']
      ring
    rw [hden]
    field_simp [hC.ne', hσ.ne', hu.ne']
  have hg_diff : ∀ θ : ℝ, θ < 2 * σ / C →
      let u : ℝ := 1 - C * θ / (2 * σ)
      0 < u ∧ g θ - g θ_min = 2 * (μ + σ * t) / (C * u) * (u - r) ^ 2 := by
    intro θ hθ u
    have hCθ : C * θ < 2 * σ := by linarith [(lt_div_iff₀ hC).mp hθ]
    have hu_pos : 0 < u := by
      dsimp [u]
      have : C * θ / (2 * σ) < 1 := (div_lt_one (by positivity)).mpr hCθ
      linarith
    refine ⟨hu_pos, ?_⟩
    have hθ_u : θ = (2 * σ / C) * (1 - u) := by
      dsimp [u]
      field_simp [hC.ne', hσ.ne']
      ring
    have hθ_min_r : θ_min = (2 * σ / C) * (1 - r) := rfl
    rw [hθ_u, hθ_min_r, hg_param u hu_pos, hg_param r hr_pos]
    exact hg_param_sub_eq hC.ne' hu_pos.ne' hr_pos.ne' hr_id
  have hR_min_le : ∀ θ : ℝ, 0 ≤ θ → θ < 2 * σ / C → R θ_min ≤ R θ := by
    intro θ _hθ0 hθlt
    obtain ⟨hu_pos, hgd⟩ := hg_diff θ hθlt
    dsimp [R]
    apply Real.exp_le_exp.mpr
    have hnn : 0 ≤ 2 * (μ + σ * t) / (C * (1 - C * θ / (2 * σ))) *
        (1 - C * θ / (2 * σ) - r) ^ 2 := by positivity
    change g θ_min ≤ g θ
    linarith
  have hR_min_lt_sub : R θ_min < R θ_sub := by
    obtain ⟨hu_pos, hgd⟩ := hg_diff θ_sub hθ_sub_lt
    dsimp [R]
    apply Real.exp_lt_exp.mpr
    have hur_neg : (1 - C * θ_sub / (2 * σ)) - r < 0 := by
      have h1 : 1 - C * θ_min / (2 * σ) = r := by
        change 1 - C * ((2 * σ / C) * (1 - r)) / (2 * σ) = r
        field_simp [hC.ne', hσ.ne']
        ring
      have h2 : C * θ_min / (2 * σ) < C * θ_sub / (2 * σ) := by
        apply div_lt_div_of_pos_right _ (by positivity)
        exact mul_lt_mul_of_pos_left hθ_min_lt_sub hC
      linarith
    have hsq_pos : 0 < ((1 - C * θ_sub / (2 * σ)) - r) ^ 2 := sq_pos_of_ne_zero hur_neg.ne
    have hpos : 0 < 2 * (μ + σ * t) / (C * (1 - C * θ_sub / (2 * σ))) *
        ((1 - C * θ_sub / (2 * σ)) - r) ^ 2 := by positivity
    change g θ_min < g θ_sub
    linarith
  exact ⟨hθ_min_pos, hθ_min_lt_sub, hθ_sub_lt, hR_sub, hR_min_le, hR_min_lt_sub⟩

/-- **Refutation of the printed minimizer claim in the proof of Theorem 7.6(2)** (`\label{2134b}`,
`SteinIntro.tex:3867-3868`; `ISSUE-7.6-PROOF`, `F-D3`): $\theta_{\mathrm{sub}} =
t(C\mu/\sigma^2 + Ct/(2\sigma))^{-1}$ does not minimize the right-hand side of `(7.12)`, even on
the restricted interval $0 \le \theta < \min\{2/C, 2\sigma/C\}$ (witnessed at
$C = \mu = \sigma = 1$, $t = 3$, where $\theta_{\mathrm{sub}} = 6/5$ gives $e^{-9/5} > e^{-2}$ at
$\theta = 1$). -/
theorem not_sec7_3_eq7_12_minimizer_printed :
    ¬ (∀ {C μ σ t : ℝ},
        0 < C →
        0 < μ →
        0 < σ →
        0 < t →
        let R : ℝ → ℝ := fun θ ↦
          Real.exp ((μ * C * θ ^ 2) / (σ ^ 2 * (2 - C * θ / σ)) - θ * t)
        let θ_sub : ℝ := t * (C * μ / σ ^ 2 + C * t / (2 * σ))⁻¹
        ∀ θ : ℝ, 0 ≤ θ → θ < min (2 / C) (2 * σ / C) → R θ_sub ≤ R θ) := by
  intro hAll
  have h1 := hAll (C := 1) (μ := 1) (σ := 1) (t := 3)
    zero_lt_one zero_lt_one zero_lt_one (by norm_num) 1 zero_le_one (by norm_num)
  dsimp only at h1
  have hlt :
      Real.exp ((1 * 1 * (1 : ℝ) ^ 2) / (1 ^ 2 * (2 - 1 * 1 / 1)) - 1 * 3) <
        Real.exp
          ((1 * 1 * (3 * (1 * 1 / (1 : ℝ) ^ 2 + 1 * 3 / (2 * 1))⁻¹) ^ 2) /
              (1 ^ 2 * (2 - 1 * (3 * (1 * 1 / (1 : ℝ) ^ 2 + 1 * 3 / (2 * 1))⁻¹) / 1)) -
            (3 * (1 * 1 / (1 : ℝ) ^ 2 + 1 * 3 / (2 * 1))⁻¹) * 3) :=
    Real.exp_lt_exp.mpr (by norm_num)
  exact not_le_of_gt hlt h1

/-- PascalCase alias for `not_sec7_3_eq7_12_minimizer_printed` (`ISSUE-7.6-PROOF`). -/
alias not_Sec7_3_eq7_12_minimizer_printed := not_sec7_3_eq7_12_minimizer_printed

end SteinMethod
