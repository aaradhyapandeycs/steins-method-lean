/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.Basic
import Formalization.SizeBias.Basic

/-!
# Concentration via Size-Bias Couplings (`Formalization.Concentration.SizeBias`)

Proves **Theorem 7.6** (`\label{thm211c}`, `SteinIntro.tex:3814-3871`; `ISSUE-7.6`) from Section 7
of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`), together with a formal
refutation of the printed statement at negative $t$:

* `sizeBias_tail_bounds` (**Theorem 7.6, corrected**, `Thm7_6_corrected`, `\label{thm211c}`,
  `SteinIntro.tex:3814-3826`; `ISSUE-7.6`): lower and upper concentration bounds for $X \ge 0$ a.s.
  with $0 < \operatorname{Var}(X) < \infty$ and a bounded size-bias coupling $|X - X^s| \le C$ a.s.,
  under $t \ge 0$.
* `not_sizeBias_tail_bounds_printed` (`not_Thm7_6_printed`, `ISSUE-7.6`): refutes the printed
  statement (which omits $t \ge 0$) via a fair coin $X \sim \mathrm{Bernoulli}(1/2)$,
  $X^s \equiv 1$, $C = 1$, and $t = -3$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SteinMethod

/-- Strict positivity $C > 0$ under the hypotheses of Theorem 7.6 (`SteinIntro.tex:3815`): if
$|X - X^s| \le C \le 0$ a.s., then $X = X^s$ a.s., forcing $\mathbb{E}[X^2] = \mu^2$ and
contradicting $\operatorname{Var}(X) > 0$. -/
private lemma pos_bound_of_sizeBias_of_variance_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xs : Ω → ℝ} {C : ℝ}
    (hX2 : MemLp X 2 P)
    (hVar : 0 < ProbabilityTheory.variance X P)
    (hSB : IsSizeBias P X P Xs)
    (hDiff : ∀ᵐ ω ∂P, |X ω - Xs ω| ≤ C) :
    0 < C := by
  by_contra! hC_le
  have hEq : X =ᵐ[P] Xs := by
    filter_upwards [hDiff] with ω hω
    exact sub_eq_zero.mp (abs_nonpos_iff.mp (hω.trans hC_le))
  have hX_int : Integrable X P := hX2.integrable one_le_two
  have hXid_eq : (fun ω ↦ X ω * id (X ω)) = fun ω ↦ X ω ^ 2 := funext fun ω ↦ by rw [id_eq, sq]
  have hXid_int : Integrable (fun ω ↦ X ω * id (X ω)) P := by
    rw [hXid_eq]; exact hX2.integrable_sq
  have hSB_id : ∫ ω, X ω ^ 2 ∂P = (∫ ω, X ω ∂P) * ∫ ω, Xs ω ∂P := by
    rw [← hXid_eq]
    exact hSB.2.2.2 id measurable_id hXid_int
  have hXs_mean : ∫ ω, Xs ω ∂P = ∫ ω, X ω ∂P := integral_congr_ae hEq.symm
  have hVar0 : ProbabilityTheory.variance X P = 0 := by
    rw [ProbabilityTheory.variance_eq_sub hX2]
    change (∫ ω, X ω ^ 2 ∂P) - (∫ ω, X ω ∂P) ^ 2 = 0
    rw [hSB_id, hXs_mean, sq]
    ring
  linarith

/-- **Theorem 7.6, corrected** (`Thm7_6_corrected`, `\label{thm211c}`,
`SteinIntro.tex:3814-3871`; `ISSUE-7.6`): for $X \ge 0$ a.s. in $L^2(P)$ with
$0 < \sigma^2 = \operatorname{Var}(X) < \infty$, $\mu = \mathbb{E}[X]$, and a size-bias coupling
$X^s$ satisfying $|X - X^s| \le C$ a.s.:
1. if $X \le X^s$ a.s., then for all $t \ge 0$,
   $\mathbb{P}((X - \mu)/\sigma \le -t) \le \exp\bigl(-t^2 / (2 C \mu / \sigma^2)\bigr)$;
2. if $\mathbb{E}[e^{(2/C) X}] < \infty$, then for all $t \ge 0$,
   $\mathbb{P}((X - \mu)/\sigma \ge t) \le
   \exp\bigl(-t^2 / (2 (C \mu / \sigma^2 + \frac{C}{2\sigma} t))\bigr)$. -/
theorem sizeBias_tail_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xs : Ω → ℝ} {C : ℝ}
    (hX_nn : 0 ≤ᵐ[P] X)
    (hX2 : MemLp X 2 P)
    (hVar : 0 < ProbabilityTheory.variance X P)
    (hSB : IsSizeBias P X P Xs)
    (hDiff : ∀ᵐ ω ∂P, |X ω - Xs ω| ≤ C) :
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    ((X ≤ᵐ[P] Xs →
        ∀ t : ℝ, 0 ≤ t →
          P.real {ω | (X ω - μ) / σ ≤ -t} ≤
            Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2)))) ∧
      (Integrable (fun ω ↦ Real.exp ((2 / C) * X ω)) P →
        ∀ t : ℝ, 0 ≤ t →
          P.real {ω | t ≤ (X ω - μ) / σ} ≤
            Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2 + C / (2 * σ) * t))))) := by
  intro μ σ
  have hX_int : Integrable X P := hX2.integrable one_le_two
  have hX_aem : AEMeasurable X P := hX_int.aemeasurable
  have hμ_pos : 0 < μ := pos_integral_of_nonneg_of_variance_pos P hX_nn hX_int hVar
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  have hσ_sq : σ ^ 2 = ProbabilityTheory.variance X P := Real.sq_sqrt hVar.le
  have hC_pos : 0 < C := pos_bound_of_sizeBias_of_variance_pos P hX2 hVar hSB hDiff
  -- Integrability of `exp(u X)` on `(-∞, 0]`.
  have hExp_nonpos_int : ∀ {u : ℝ}, u ≤ 0 → Integrable (fun ω ↦ Real.exp (u * X ω)) P := by
    intro u hu
    have hasm : AEStronglyMeasurable (fun ω ↦ Real.exp (u * X ω)) P :=
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul measurable_id)).comp_aemeasurable hX_aem).aestronglyMeasurable
    refine (integrable_const (1 : ℝ)).mono' hasm ?_
    filter_upwards [hX_nn] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hu hω)
  refine ⟨?_, ?_⟩
  · -- Item 1 (`X ≤ᵐ Xs`, lower tail `(X - μ)/σ ≤ -t`).
    intro hMono t ht
    rcases ht.eq_or_lt with rfl | ht_pos
    · have hle1 : P.real {ω | (X ω - μ) / σ ≤ -(0 : ℝ)} ≤ P.real Set.univ := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (Set.subset_univ _))
      exact (hle1.trans_eq probReal_univ).trans_eq (by simp)
    · have hIio_mem : ∀ {u : ℝ}, u < 0 →
          u ∈ interior (ProbabilityTheory.integrableExpSet X P) := by
        intro u hu
        exact interior_maximal (fun v hv ↦ hExp_nonpos_int (le_of_lt hv)) isOpen_Iio hu
      let m' : ℝ → ℝ := fun u ↦ ∫ ω, X ω * Real.exp (u * X ω) ∂P
      have hXexp_int : ∀ {u : ℝ}, u < 0 → Integrable (fun ω ↦ X ω * Real.exp (u * X ω)) P := by
        intro u hu
        simpa [pow_one] using
          ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
            (hIio_mem hu) 1
      have hmgf_cont : ContinuousOn (ProbabilityTheory.mgf X P) (Set.Iic 0) := by
        intro u hu
        rcases (Set.mem_Iic.mp hu).lt_or_eq with hu_neg | rfl
        · exact (ProbabilityTheory.hasDerivAt_mgf (hIio_mem hu_neg)).continuousAt.continuousWithinAt
        · refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
            (Eventually.of_forall fun _ ↦
              ((Real.continuous_exp.measurable.comp
                (measurable_const.mul measurable_id)).comp_aemeasurable
                hX_aem).aestronglyMeasurable)
            ?_ (integrable_const (1 : ℝ)) ?_
          · filter_upwards [self_mem_nhdsWithin] with v hv
            filter_upwards [hX_nn] with ω hω
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (Set.mem_Iic.mp hv) hω)
          · filter_upwards with ω
            exact (Real.continuous_exp.comp
              (continuous_id.mul continuous_const)).continuousWithinAt
      have hcgf_cont : ContinuousOn (ProbabilityTheory.cgf X P) (Set.Iic 0) := by
        have hcexp : ProbabilityTheory.cgf X P = fun u ↦ Real.log (ProbabilityTheory.mgf X P u) :=
          rfl
        rw [hcexp]
        exact ContinuousOn.log hmgf_cont fun u hu ↦
          (ProbabilityTheory.mgf_pos (hExp_nonpos_int (Set.mem_Iic.mp hu))).ne'
      set θ : ℝ := -σ * t / (C * μ)
      have hθ_neg : θ < 0 :=
        div_neg_of_neg_of_pos (by nlinarith) (mul_pos hC_pos hμ_pos)
      let H : ℝ → ℝ := fun u ↦ ProbabilityTheory.cgf X P u - μ * u - μ * C * u ^ 2 / 2
      have hH_cont : ContinuousOn H (Set.Icc θ 0) := by
        have hsub : Set.Icc θ 0 ⊆ Set.Iic 0 := fun u hu ↦ hu.2
        exact ((hcgf_cont.mono hsub).sub
          (continuous_const.mul continuous_id).continuousOn).sub
          (((continuous_const.mul (continuous_pow 2)).div_const 2).continuousOn)
      have hH_deriv : ∀ {u : ℝ}, u < 0 →
          HasDerivAt H (m' u / ProbabilityTheory.mgf X P u - μ - μ * C * u) u := by
        intro u hu
        have h1 : HasDerivAt (ProbabilityTheory.cgf X P)
            (m' u / ProbabilityTheory.mgf X P u) u :=
          (ProbabilityTheory.hasDerivAt_mgf (hIio_mem hu)).log
            (ProbabilityTheory.mgf_pos (hExp_nonpos_int hu.le)).ne'
        have h2 : HasDerivAt (fun x : ℝ ↦ μ * x) μ u := by
          simpa using (hasDerivAt_id' u).const_mul μ
        have h3 : HasDerivAt (fun x : ℝ ↦ μ * C * x ^ 2 / 2) (μ * C * u) u := by
          convert (((hasDerivAt_pow 2 u).const_mul (μ * C)).div_const 2) using 1
          ring
        exact (h1.fun_sub h2).fun_sub h3
      have hH_mono : MonotoneOn H (Set.Icc θ 0) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc θ 0) hH_cont
          (fun u hu ↦ (hH_deriv (by rw [interior_Icc] at hu; exact hu.2)).hasDerivWithinAt)
          fun u hu ↦ ?_
        rw [interior_Icc] at hu
        have hu_neg : u < 0 := hu.2
        let g_exp : ℝ → ℝ := fun x ↦ Real.exp (u * x)
        have hg_meas : Measurable g_exp :=
          Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
        have hXs_int : Integrable (fun ω ↦ Real.exp (u * Xs ω)) P :=
          hSB.integrable_comp_of_pos_mean hμ_pos hg_meas (hXexp_int hu_neg)
        have hSB_eq : m' u = μ * ∫ ω, Real.exp (u * Xs ω) ∂P :=
          hSB.2.2.2 g_exp hg_meas (hXexp_int hu_neg)
        have hpt_le : ∀ᵐ ω ∂P,
            Real.exp (u * X ω) - Real.exp (u * Xs ω) ≤ (-C * u) * Real.exp (u * X ω) := by
          filter_upwards [hMono, hDiff] with ω hle hbd
          have hexp_le : Real.exp (u * Xs ω) ≤ Real.exp (u * X ω) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hle hu_neg.le)
          have hchord := abs_exp_sub_exp_le (u * X ω) (u * Xs ω)
          have habs_u : |u * X ω - u * Xs ω| ≤ (-u) * C := by
            have heq : u * X ω - u * Xs ω = u * (X ω - Xs ω) := by ring
            rw [heq, abs_mul, abs_of_neg hu_neg]
            exact mul_le_mul_of_nonneg_left hbd (neg_nonneg.mpr hu_neg.le)
          calc
            Real.exp (u * X ω) - Real.exp (u * Xs ω)
                ≤ |Real.exp (u * X ω) - Real.exp (u * Xs ω)| := le_abs_self _
            _ ≤ |u * X ω - u * Xs ω| * ((Real.exp (u * X ω) + Real.exp (u * Xs ω)) / 2) := hchord
            _ ≤ ((-u) * C) * ((Real.exp (u * X ω) + Real.exp (u * X ω)) / 2) := by
                refine mul_le_mul habs_u ?_ (by positivity)
                  (mul_nonneg (neg_nonneg.mpr hu_neg.le) hC_pos.le)
                linarith
            _ = (-C * u) * Real.exp (u * X ω) := by ring
        have hInt_le : ProbabilityTheory.mgf X P u - ∫ ω, Real.exp (u * Xs ω) ∂P ≤
            (-C * u) * ProbabilityTheory.mgf X P u := by
          unfold ProbabilityTheory.mgf
          rw [← integral_sub (hExp_nonpos_int hu_neg.le) hXs_int, ← integral_const_mul]
          exact integral_mono_ae ((hExp_nonpos_int hu_neg.le).sub hXs_int)
            ((hExp_nonpos_int hu_neg.le).const_mul _) hpt_le
        have hmgf_pos : 0 < ProbabilityTheory.mgf X P u :=
          ProbabilityTheory.mgf_pos (hExp_nonpos_int hu_neg.le)
        have hm'_ge : μ * (1 + C * u) * ProbabilityTheory.mgf X P u ≤ m' u := by
          rw [hSB_eq]; nlinarith
        have hdiv : μ * (1 + C * u) ≤ m' u / ProbabilityTheory.mgf X P u :=
          (le_div_iff₀ hmgf_pos).mpr hm'_ge
        linarith
      have hH0 : H 0 = 0 := by
        dsimp [H]
        have hm0 : ProbabilityTheory.mgf X P 0 = 1 := by simp [ProbabilityTheory.mgf]
        change Real.log (ProbabilityTheory.mgf X P 0) - μ * 0 - μ * C * 0 ^ 2 / 2 = 0
        rw [hm0, Real.log_one]
        ring
      have hHθ_le : H θ ≤ H 0 :=
        hH_mono (left_mem_Icc.mpr hθ_neg.le) (right_mem_Icc.mpr hθ_neg.le) hθ_neg.le
      rw [hH0] at hHθ_le
      have hcgf_le : ProbabilityTheory.cgf X P θ ≤ μ * θ + μ * C * θ ^ 2 / 2 := by
        dsimp [H] at hHθ_le; linarith
      have hEvent : {ω | (X ω - μ) / σ ≤ -t} = {ω | X ω ≤ μ - σ * t} := by
        ext ω
        change (X ω - μ) / σ ≤ -t ↔ X ω ≤ μ - σ * t
        rw [div_le_iff₀ hσ_pos]
        constructor <;> intro h <;> linarith
      rw [hEvent]
      have hch := ProbabilityTheory.measure_le_le_exp_cgf (μ - σ * t) hθ_neg.le
        (hExp_nonpos_int hθ_neg.le)
      have hexp_le : Real.exp (-θ * (μ - σ * t) + ProbabilityTheory.cgf X P θ) ≤
          Real.exp (-θ * (μ - σ * t) + (μ * θ + μ * C * θ ^ 2 / 2)) :=
        Real.exp_le_exp.mpr (by linarith)
      refine hch.trans (hexp_le.trans_eq ?_)
      congr 1
      dsimp [θ]
      field_simp [hC_pos.ne', hμ_pos.ne', hσ_pos.ne']
      ring
  · -- Item 2 (`Integrable (exp ((2/C) X)) P`, upper tail `t ≤ (X - μ)/σ`).
    intro hExp2C t ht
    rcases ht.eq_or_lt with rfl | ht_pos
    · have hle1 : P.real {ω | (0 : ℝ) ≤ (X ω - μ) / σ} ≤ P.real Set.univ := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (Set.subset_univ _))
      exact (hle1.trans_eq probReal_univ).trans_eq (by simp)
    · have hExp_lt_int : ∀ {u : ℝ}, u < 2 / C →
          Integrable (fun ω ↦ Real.exp (u * X ω)) P := by
        intro u hu
        have hasm : AEStronglyMeasurable (fun ω ↦ Real.exp (u * X ω)) P :=
          ((Real.continuous_exp.measurable.comp
            (measurable_const.mul measurable_id)).comp_aemeasurable hX_aem).aestronglyMeasurable
        refine ((integrable_const (1 : ℝ)).add hExp2C).mono' hasm ?_
        filter_upwards [hX_nn] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
        rcases le_or_gt u 0 with hu0 | hu0
        · have h1 : Real.exp (u * X ω) ≤ 1 :=
            Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hu0 hω)
          linarith [Real.exp_pos ((2 / C) * X ω)]
        · have h2 : Real.exp (u * X ω) ≤ Real.exp ((2 / C) * X ω) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hu.le hω)
          linarith
      have hIio_mem : ∀ {u : ℝ}, u < 2 / C →
          u ∈ interior (ProbabilityTheory.integrableExpSet X P) := by
        intro u hu
        exact interior_maximal (fun v hv ↦ hExp_lt_int hv) isOpen_Iio hu
      let m' : ℝ → ℝ := fun u ↦ ∫ ω, X ω * Real.exp (u * X ω) ∂P
      have hXexp_int : ∀ {u : ℝ}, u < 2 / C →
          Integrable (fun ω ↦ X ω * Real.exp (u * X ω)) P := by
        intro u hu
        simpa [pow_one] using
          ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
            (hIio_mem hu) 1
      set D_den : ℝ := C * μ + C * σ * t / 2
      have hD_pos : 0 < D_den := by dsimp [D_den]; positivity
      set u₁ : ℝ := σ * t / D_den
      have hu₁_pos : 0 < u₁ := div_pos (mul_pos hσ_pos ht_pos) hD_pos
      have h1Cu₁ : 1 - C * u₁ / 2 = C * μ / D_den := by
        dsimp [u₁, D_den]
        field_simp [hD_pos.ne']
        ring
      have h1Cu₁_pos : 0 < 1 - C * u₁ / 2 := by
        rw [h1Cu₁]; exact div_pos (mul_pos hC_pos hμ_pos) hD_pos
      have hu₁_lt : u₁ < 2 / C := by
        rw [lt_div_iff₀ hC_pos]
        linarith
      let G : ℝ → ℝ := fun u ↦
        C * μ * u ^ 2 / (2 * (1 - C * u₁ / 2)) - (ProbabilityTheory.cgf X P u - μ * u)
      have hG_deriv : ∀ {u : ℝ}, u < 2 / C →
          HasDerivAt G
            (C * μ * u / (1 - C * u₁ / 2) - (m' u / ProbabilityTheory.mgf X P u - μ)) u := by
        intro u hu
        have hq : HasDerivAt (fun x : ℝ ↦ C * μ * x ^ 2 / (2 * (1 - C * u₁ / 2)))
            (C * μ * u / (1 - C * u₁ / 2)) u := by
          convert (((hasDerivAt_pow 2 u).const_mul (C * μ)).div_const
            (2 * (1 - C * u₁ / 2))) using 1
          field_simp [h1Cu₁_pos.ne']
          ring
        have hcgf : HasDerivAt (ProbabilityTheory.cgf X P)
            (m' u / ProbabilityTheory.mgf X P u) u :=
          (ProbabilityTheory.hasDerivAt_mgf (hIio_mem hu)).log
            (ProbabilityTheory.mgf_pos (hExp_lt_int hu)).ne'
        have hlin : HasDerivAt (fun x : ℝ ↦ μ * x) μ u := by
          simpa using (hasDerivAt_id' u).const_mul μ
        exact hq.fun_sub (hcgf.fun_sub hlin)
      have hG_mono : MonotoneOn G (Set.Icc 0 u₁) := by
        refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u₁)
          (fun u hu ↦ (hG_deriv (hu.2.trans_lt hu₁_lt)).continuousAt.continuousWithinAt)
          (fun u hu ↦
            (hG_deriv ((interior_subset hu).2.trans_lt hu₁_lt)).hasDerivWithinAt)
          fun u hu ↦ ?_
        rw [interior_Icc] at hu
        have hu_pos : 0 < u := hu.1
        have hu_lt₁ : u < u₁ := hu.2
        have hu_lt2C : u < 2 / C := hu_lt₁.trans hu₁_lt
        let g_exp : ℝ → ℝ := fun x ↦ Real.exp (u * x)
        have hg_meas : Measurable g_exp :=
          Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
        have hXs_int : Integrable (fun ω ↦ Real.exp (u * Xs ω)) P :=
          hSB.integrable_comp_of_pos_mean hμ_pos hg_meas (hXexp_int hu_lt2C)
        have hSB_eq : m' u = μ * ∫ ω, Real.exp (u * Xs ω) ∂P :=
          hSB.2.2.2 g_exp hg_meas (hXexp_int hu_lt2C)
        have hpt_le : ∀ᵐ ω ∂P,
            Real.exp (u * Xs ω) - Real.exp (u * X ω) ≤
              (C * u / 2) * (Real.exp (u * Xs ω) + Real.exp (u * X ω)) := by
          filter_upwards [hDiff] with ω hbd
          have hchord := abs_exp_sub_exp_le (u * Xs ω) (u * X ω)
          have habs_u : |u * Xs ω - u * X ω| ≤ C * u := by
            have heq : u * Xs ω - u * X ω = -(u * (X ω - Xs ω)) := by ring
            rw [heq, abs_neg, abs_mul, abs_of_pos hu_pos, mul_comm]
            exact mul_le_mul_of_nonneg_right hbd hu_pos.le
          calc
            Real.exp (u * Xs ω) - Real.exp (u * X ω)
                ≤ |Real.exp (u * Xs ω) - Real.exp (u * X ω)| := le_abs_self _
            _ ≤ |u * Xs ω - u * X ω| * ((Real.exp (u * Xs ω) + Real.exp (u * X ω)) / 2) := hchord
            _ ≤ (C * u) * ((Real.exp (u * Xs ω) + Real.exp (u * X ω)) / 2) :=
                mul_le_mul_of_nonneg_right habs_u (by positivity)
            _ = (C * u / 2) * (Real.exp (u * Xs ω) + Real.exp (u * X ω)) := by ring
        have hInt_le :
            (∫ ω, Real.exp (u * Xs ω) ∂P) - ProbabilityTheory.mgf X P u ≤
              (C * u / 2) * ((∫ ω, Real.exp (u * Xs ω) ∂P) + ProbabilityTheory.mgf X P u) := by
          unfold ProbabilityTheory.mgf
          rw [← integral_sub hXs_int (hExp_lt_int hu_lt2C),
            ← integral_add hXs_int (hExp_lt_int hu_lt2C), ← integral_const_mul]
          exact integral_mono_ae (hXs_int.sub (hExp_lt_int hu_lt2C))
            ((hXs_int.add (hExp_lt_int hu_lt2C)).const_mul _) hpt_le
        have hmgf_pos : 0 < ProbabilityTheory.mgf X P u :=
          ProbabilityTheory.mgf_pos (hExp_lt_int hu_lt2C)
        have h1Cu_ge : 1 - C * u₁ / 2 ≤ 1 - C * u / 2 := by nlinarith
        have h1Cu_pos : 0 < 1 - C * u / 2 := h1Cu₁_pos.trans_le h1Cu_ge
        have hm'_rel : (1 - C * u / 2) * (m' u - μ * ProbabilityTheory.mgf X P u) ≤
            C * μ * u * ProbabilityTheory.mgf X P u := by
          have hmul_μ := mul_le_mul_of_nonneg_left hInt_le hμ_pos.le
          nlinarith [hSB_eq]
        have hstep1 : m' u / ProbabilityTheory.mgf X P u - μ ≤ C * μ * u / (1 - C * u / 2) := by
          have hsub_div : m' u / ProbabilityTheory.mgf X P u - μ =
              (m' u - μ * ProbabilityTheory.mgf X P u) / ProbabilityTheory.mgf X P u := by
            field_simp [hmgf_pos.ne']
          rw [hsub_div, div_le_div_iff₀ hmgf_pos h1Cu_pos]
          linarith
        have hstep2 : C * μ * u / (1 - C * u / 2) ≤ C * μ * u / (1 - C * u₁ / 2) :=
          div_le_div_of_nonneg_left (by positivity) h1Cu₁_pos h1Cu_ge
        linarith
      have hG0 : G 0 = 0 := by
        dsimp [G]
        have hm0 : ProbabilityTheory.mgf X P 0 = 1 := by simp [ProbabilityTheory.mgf]
        change C * μ * 0 ^ 2 / (2 * (1 - C * u₁ / 2)) -
          (Real.log (ProbabilityTheory.mgf X P 0) - μ * 0) = 0
        rw [hm0, Real.log_one]
        ring
      have hGu₁ : G 0 ≤ G u₁ :=
        hG_mono (left_mem_Icc.mpr hu₁_pos.le) (right_mem_Icc.mpr hu₁_pos.le) hu₁_pos.le
      rw [hG0] at hGu₁
      have hcgf_le : ProbabilityTheory.cgf X P u₁ ≤
          μ * u₁ + C * μ * u₁ ^ 2 / (2 * (1 - C * u₁ / 2)) := by
        dsimp [G] at hGu₁; linarith
      have hEvent : {ω | t ≤ (X ω - μ) / σ} = {ω | μ + σ * t ≤ X ω} := by
        ext ω
        change t ≤ (X ω - μ) / σ ↔ μ + σ * t ≤ X ω
        rw [le_div_iff₀ hσ_pos]
        constructor <;> intro h <;> linarith
      rw [hEvent]
      have hch := ProbabilityTheory.measure_ge_le_exp_cgf (μ + σ * t) hu₁_pos.le
        (hExp_lt_int hu₁_lt)
      have hexp_le : Real.exp (-u₁ * (μ + σ * t) + ProbabilityTheory.cgf X P u₁) ≤
          Real.exp (-u₁ * (μ + σ * t) + (μ * u₁ + C * μ * u₁ ^ 2 / (2 * (1 - C * u₁ / 2)))) :=
        Real.exp_le_exp.mpr (by linarith)
      refine hch.trans (hexp_le.trans_eq ?_)
      congr 1
      rw [h1Cu₁]
      dsimp [u₁, D_den]
      have hden2 : C * μ / σ ^ 2 + C / (2 * σ) * t ≠ 0 := by positivity
      field_simp [hC_pos.ne', hμ_pos.ne', hσ_pos.ne', hD_pos.ne', hden2]
      ring

/-- **Counterexample to the printed Theorem 7.6 at $t < 0$** (`not_Thm7_6_printed`,
`SteinIntro.tex:3814-3826`; `ISSUE-7.6`): without the omitted hypothesis $t \ge 0$, both displayed
bounds fail for a fair coin $X \sim \mathrm{Bernoulli}(1/2)$ coupled with $X^s \equiv 1$ ($C = 1$)
at $t = -3$. -/
theorem not_sizeBias_tail_bounds_printed :
    ¬ (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {X Xs : Ω → ℝ} {C : ℝ},
        0 ≤ᵐ[P] X →
        MemLp X 2 P →
        0 < ProbabilityTheory.variance X P →
        IsSizeBias P X P Xs →
        (∀ᵐ ω ∂P, |X ω - Xs ω| ≤ C) →
        let μ : ℝ := ∫ ω, X ω ∂P
        let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
        ((X ≤ᵐ[P] Xs →
            ∀ t : ℝ,
              P.real {ω | (X ω - μ) / σ ≤ -t} ≤
                Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2)))) ∧
          (Integrable (fun ω ↦ Real.exp ((2 / C) * X ω)) P →
            ∀ t : ℝ,
              P.real {ω | t ≤ (X ω - μ) / σ} ≤
                Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2 + C / (2 * σ) * t)))))) := by
  intro h
  let _ : MeasurableSpace (ULift Bool) := ⊤
  have _ : MeasurableSingletonClass (ULift Bool) := ⟨fun _ ↦ trivial⟩
  let P₁ : Measure (ULift Bool) := (1 / 2 : ℝ≥0∞) • Measure.dirac (ULift.up true)
  let P₀ : Measure (ULift Bool) := (1 / 2 : ℝ≥0∞) • Measure.dirac (ULift.up false)
  let P : Measure (ULift Bool) := P₁ + P₀
  have _ : IsProbabilityMeasure P := by
    rw [isProbabilityMeasure_iff]
    simp [P, P₁, P₀, ENNReal.inv_two_add_inv_two]
  let X : ULift Bool → ℝ := fun b ↦ if b.down then 1 else 0
  let Xs : ULift Bool → ℝ := fun _ ↦ 1
  have hX_nn : 0 ≤ᵐ[P] X :=
    Eventually.of_forall fun b ↦ by rcases b with ⟨_ | _⟩ <;> norm_num [X]
  have hX2 : MemLp X 2 P := by
    refine MemLp.of_bound (.of_discrete) 1 (Eventually.of_forall fun b ↦ ?_)
    rcases b with ⟨_ | _⟩ <;> norm_num [X]
  have hIntBool : ∀ g : ULift Bool → ℝ,
      ∫ b, g b ∂P = (g (ULift.up true) + g (ULift.up false)) / 2 := by
    intro g
    have hg_bdd : ∀ (μ : Measure (ULift Bool)) [IsFiniteMeasure μ], Integrable g μ := fun μ _ ↦ by
      refine (integrable_const (max |g (ULift.up true)| |g (ULift.up false)|)).mono'
        Measurable.of_discrete.aestronglyMeasurable (Eventually.of_forall fun b ↦ ?_)
      rcases b with ⟨_ | _⟩ <;> simp [Real.norm_eq_abs]
    have _ : IsFiniteMeasure P₁ := ⟨by simp [P₁]⟩
    have _ : IsFiniteMeasure P₀ := ⟨by simp [P₀]⟩
    rw [integral_add_measure (hg_bdd P₁) (hg_bdd P₀)]
    simp only [P₁, P₀, integral_smul_measure, integral_dirac, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
    ring
  have hμ : ∫ b, X b ∂P = 1 / 2 := by rw [hIntBool]; norm_num [X]
  have hVar : ProbabilityTheory.variance X P = 1 / 4 := by
    rw [ProbabilityTheory.variance_eq_sub hX2, hIntBool, hμ]
    norm_num [X]
  have hVar_pos : 0 < ProbabilityTheory.variance X P := by rw [hVar]; norm_num
  have hSB : IsSizeBias P X P Xs := by
    refine ⟨hX_nn, hX2.integrable one_le_two, Measurable.of_discrete.aemeasurable, ?_⟩
    intro f _ _
    rw [hIntBool, hμ, hIntBool]
    simp [X, Xs]
    ring
  have hDiff : ∀ᵐ b ∂P, |X b - Xs b| ≤ (1 : ℝ) :=
    Eventually.of_forall fun b ↦ by rcases b with ⟨_ | _⟩ <;> norm_num [X, Xs]
  have hMono : X ≤ᵐ[P] Xs :=
    Eventually.of_forall fun b ↦ by rcases b with ⟨_ | _⟩ <;> norm_num [X, Xs]
  have h1 := (h P hX_nn hX2 hVar_pos hSB hDiff).1 hMono (-3)
  have hσ : Real.sqrt (ProbabilityTheory.variance X P) = 1 / 2 := by
    rw [hVar]
    have hsq : (1 / 4 : ℝ) = (1 / 2) ^ 2 := by norm_num
    rw [hsq, Real.sqrt_sq (by norm_num)]
  have hUniv : {b : ULift Bool |
      (X b - ∫ b', X b' ∂P) / Real.sqrt (ProbabilityTheory.variance X P) ≤ -(-3 : ℝ)} =
      Set.univ := by
    ext b
    simp only [Set.mem_ofPred, Set.mem_univ, iff_true, hμ, hσ]
    rcases b with ⟨_ | _⟩ <;> norm_num [X]
  rw [hUniv, probReal_univ, hμ, hσ] at h1
  have hexp_lt : Real.exp (-(-3 : ℝ) ^ 2 / (2 * (1 * (1 / 2) / (1 / 2) ^ 2))) < 1 := by
    rw [Real.exp_lt_one_iff]
    norm_num
  linarith

end SteinMethod
