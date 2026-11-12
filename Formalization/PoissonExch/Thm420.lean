/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonExch
import Formalization.Defs.PoissonStein
import Formalization.Defs.Couplings
import Formalization.Defs.Metrics
import Formalization.Metrics.Basic
import Formalization.Poisson.SteinLemma
import Formalization.PoissonExch.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Theorem 4.20: Poisson Approximation by Exchangeable Pairs

Theorem 4.20 (`\label{thm161}`, `SteinIntro.tex:2618-2626`), the anti-symmetry sub-claim
(`SteinIntro.tex:2647-2650`), and key identity `(4.3)` (`\label{161}`, `SteinIntro.tex:2656-2660`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SteinMethod

/-! ### Anti-symmetry of the exchangeable-pair test function (`SteinIntro.tex:2647-2650`) -/

/-- For an exchangeable pair $(W, W')$, the integral of the anti-symmetric test function
$F(w, w') = \mathbb{I}[w' = w+1] f(w') - \mathbb{I}[w = w'+1] f(w)$ vanishes.
This is used in the proof of Theorem 4.20 (`SteinIntro.tex:2647-2650`). -/
theorem integral_poissonExchTestFn_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℕ} (_hW : Measurable W) (_hW' : Measurable W')
    (hex : IsExchangeablePair P W W')
    (f : ℕ → ℝ) :
    ∫ ω, ((if W' ω = W ω + 1 then f (W' ω) else 0) -
           (if W ω = W' ω + 1 then f (W ω) else 0)) ∂P = 0 := by
  set g : ℕ × ℕ → ℝ := fun p ↦
    (if p.2 = p.1 + 1 then f p.2 else 0) - (if p.1 = p.2 + 1 then f p.1 else 0)
  have hexid : IdentDistrib (fun ω ↦ (W ω, W' ω)) (fun ω ↦ (W' ω, W ω)) P P := hex
  have hgm : Measurable g := Measurable.of_discrete
  have hid : IdentDistrib (g ∘ fun ω ↦ (W ω, W' ω)) (g ∘ fun ω ↦ (W' ω, W ω)) P P :=
    hexid.comp hgm
  have step1 : ∫ ω, g (W ω, W' ω) ∂P = ∫ ω, g (W' ω, W ω) ∂P := hid.integral_eq
  have step2 : ∀ ω, g (W' ω, W ω) = -g (W ω, W' ω) := fun ω ↦ by
    simp only [g]; ring
  simp_rw [step2] at step1
  rw [integral_neg] at step1
  linarith

/-! ### Theorem 4.20: TV bound via exchangeable pairs -/

/-- Pull-out and tower property for `condExpAt F mΩ P (S.indicator 1) * (g ∘ W)` when
`σ(W) ≤ F ≤ mΩ` and `g` is bounded. -/
private lemma integral_condExpAt_indicator_mul_comp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℕ} (hW : Measurable W)
    {F : MeasurableSpace Ω} (hFle : F ≤ mΩ)
    (hWF : MeasurableSpace.comap W inferInstance ≤ F)
    {S : Set Ω} (hS : MeasurableSet[mΩ] S)
    (g : ℕ → ℝ) {C : ℝ} (hg : ∀ k : ℕ, |g k| ≤ C) :
    Integrable (fun ω ↦ condExpAt F mΩ P (S.indicator (1 : Ω → ℝ)) ω * g (W ω)) P ∧
      ∫ ω, condExpAt F mΩ P (S.indicator (1 : Ω → ℝ)) ω * g (W ω) ∂P =
        ∫ ω, S.indicator (1 : Ω → ℝ) ω * g (W ω) ∂P := by
  let _ : MeasurableSpace Ω := mΩ
  let u : Ω → ℝ := S.indicator (1 : Ω → ℝ)
  let v : Ω → ℝ := fun ω ↦ g (W ω)
  have hu_int : Integrable u P := (integrable_const (1 : ℝ)).indicator hS
  have hv_meas_W : Measurable[MeasurableSpace.comap W inferInstance] v :=
    (Measurable.of_discrete (f := g)).comp (comap_measurable (m := inferInstance) W)
  have hv_sm : StronglyMeasurable[F] v := (hv_meas_W.mono hWF le_rfl).stronglyMeasurable
  have hv_meas : Measurable[mΩ] v := (Measurable.of_discrete (f := g)).comp hW
  have hv_int : Integrable v P :=
    Integrable.of_mem_Icc (-C) C hv_meas.aemeasurable
      (Filter.Eventually.of_forall fun ω ↦ abs_le.mp (hg (W ω)))
  have huv_eq : u * v = S.indicator v := by
    ext ω; by_cases hω : ω ∈ S <;> simp [u, v, hω]
  have huv_int : Integrable (u * v) P := huv_eq ▸ hv_int.indicator hS
  have hpull : condExpAt F mΩ P (u * v) =ᵐ[P] fun ω ↦ condExpAt F mΩ P u ω * v ω :=
    condExp_mul_of_stronglyMeasurable_right (m := F) (mΩ := mΩ) (μ := P) hv_sm huv_int hu_int
  have hint_prod : Integrable (fun ω ↦ condExpAt F mΩ P u ω * v ω) P :=
    (integrable_congr hpull).mp integrable_condExp
  refine ⟨hint_prod, ?_⟩
  calc
    ∫ ω, condExpAt F mΩ P u ω * v ω ∂P
        = ∫ ω, condExpAt F mΩ P (u * v) ω ∂P := integral_congr_ae hpull.symm
    _ = ∫ ω, (u * v) ω ∂P := integral_condExp (m := F) (m₀ := mΩ) (μ := P) hFle
    _ = ∫ ω, u ω * v ω ∂P := rfl

/-- Key identity eq. `(4.3)` (`\label{161}`, `SteinIntro.tex:2656-2660`) in the proof of
Theorem 4.20: for an exchangeable pair $(W, W')$ with $\sigma(W) \subseteq \mathcal{F}$,
integrable $W$, and bounded $f : \mathbb{N} \to \mathbb{R}$,
$\mathbb{E}[\lambda f(W+1) - W f(W)] =
\mathbb{E}[(\lambda - c \mathbb{P}(W'=W+1|\mathcal{F})) f(W+1) -
(W - c \mathbb{P}(W=W'+1|\mathcal{F})) f(W)]$.
This is a proof sub-claim; `Integrable (fun ω ↦ (W ω : ℝ)) P` is needed so that
$\mathbb{E}[W f(W)]$ is well-defined (`stmts-review-05H` `H2`). -/
theorem integral_poissonSteinOp_exchangeable_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {W W' : Ω → ℕ}
    (_hr : 0 < r)
    (hW : Measurable W) (hW' : Measurable W')
    (hex : IsExchangeablePair P W W')
    (hIntW : Integrable (fun ω ↦ (W ω : ℝ)) P)
    {F : MeasurableSpace Ω} (hFle : F ≤ mΩ)
    (hWF : MeasurableSpace.comap W inferInstance ≤ F)
    (f : ℕ → ℝ) (hf : ∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C)
    (c : ℝ) :
    ∫ ω, poissonSteinOp r f (W ω) ∂P =
      ∫ ω, (((r : ℝ) - c *
            condExpAt F mΩ P
              ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω + 1) -
          ((W ω : ℝ) - c *
            condExpAt F mΩ P
              ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω)) ∂P := by
  let _ : MeasurableSpace Ω := mΩ
  rcases hf with ⟨C, hC⟩
  let S_up : Set Ω := {ω' | W' ω' = W ω' + 1}
  let S_down : Set Ω := {ω' | W ω' = W' ω' + 1}
  have hS_up : MeasurableSet[mΩ] S_up :=
    (hW.prodMk hW') (MeasurableSet.of_discrete (s := {p : ℕ × ℕ | p.2 = p.1 + 1}))
  have hS_down : MeasurableSet[mΩ] S_down :=
    (hW'.prodMk hW) (MeasurableSet.of_discrete (s := {p : ℕ × ℕ | p.2 = p.1 + 1}))
  obtain ⟨hInt_cond_up, hEq_up⟩ :=
    integral_condExpAt_indicator_mul_comp P hW hFle hWF hS_up (fun k ↦ f (k + 1))
      (fun k ↦ hC (k + 1))
  obtain ⟨hInt_cond_down, hEq_down⟩ :=
    integral_condExpAt_indicator_mul_comp P hW hFle hWF hS_down f hC
  have hInt_fW1 : Integrable (fun ω ↦ f (W ω + 1)) P :=
    Integrable.of_mem_Icc (-C) C
      (((Measurable.of_discrete (f := fun k : ℕ ↦ f (k + 1))).comp hW).aemeasurable)
      (Filter.Eventually.of_forall fun ω ↦ abs_le.mp (hC (W ω + 1)))
  have hInt_fW : Integrable (fun ω ↦ f (W ω)) P :=
    Integrable.of_mem_Icc (-C) C
      (((Measurable.of_discrete (f := f)).comp hW).aemeasurable)
      (Filter.Eventually.of_forall fun ω ↦ abs_le.mp (hC (W ω)))
  have hInt_ind_up : Integrable (fun ω ↦ S_up.indicator (1 : Ω → ℝ) ω * f (W ω + 1)) P := by
    have heq : (fun ω ↦ S_up.indicator (1 : Ω → ℝ) ω * f (W ω + 1)) =
        S_up.indicator (fun ω ↦ f (W ω + 1)) := by
      ext ω; by_cases hω : ω ∈ S_up <;> simp [hω]
    exact heq ▸ hInt_fW1.indicator hS_up
  have hInt_ind_down : Integrable (fun ω ↦ S_down.indicator (1 : Ω → ℝ) ω * f (W ω)) P := by
    have heq : (fun ω ↦ S_down.indicator (1 : Ω → ℝ) ω * f (W ω)) =
        S_down.indicator (fun ω ↦ f (W ω)) := by
      ext ω; by_cases hω : ω ∈ S_down <;> simp [hω]
    exact heq ▸ hInt_fW.indicator hS_down
  have h_antisym_ind :
      (∫ ω, S_up.indicator (1 : Ω → ℝ) ω * f (W ω + 1) ∂P) -
        (∫ ω, S_down.indicator (1 : Ω → ℝ) ω * f (W ω) ∂P) = 0 := by
    rw [← integral_sub hInt_ind_up hInt_ind_down]
    have hpt :
        (fun ω ↦ S_up.indicator (1 : Ω → ℝ) ω * f (W ω + 1) -
            S_down.indicator (1 : Ω → ℝ) ω * f (W ω)) =
          fun ω ↦ (if W' ω = W ω + 1 then f (W' ω) else 0) -
            (if W ω = W' ω + 1 then f (W ω) else 0) := by
      ext ω
      have h_up : S_up.indicator (1 : Ω → ℝ) ω * f (W ω + 1) =
          if W' ω = W ω + 1 then f (W' ω) else 0 := by
        by_cases h : W' ω = W ω + 1 <;> simp [S_up, h]
      have h_down : S_down.indicator (1 : Ω → ℝ) ω * f (W ω) =
          if W ω = W' ω + 1 then f (W ω) else 0 := by
        by_cases h : W ω = W' ω + 1 <;> simp [S_down, h]
      rw [h_up, h_down]
    rw [hpt]
    exact integral_poissonExchTestFn_eq_zero P hW hW' hex f
  have h_cond_eq :
      (∫ ω, condExpAt F mΩ P (S_up.indicator (1 : Ω → ℝ)) ω * f (W ω + 1) ∂P) -
        (∫ ω, condExpAt F mΩ P (S_down.indicator (1 : Ω → ℝ)) ω * f (W ω) ∂P) = 0 := by
    rw [hEq_up, hEq_down, h_antisym_ind]
  have hInt_WfW : Integrable (fun ω ↦ (W ω : ℝ) * f (W ω)) P := by
    refine Integrable.mono' (hIntW.norm.mul_const C)
      (((Measurable.of_discrete (f := fun k : ℕ ↦ (k : ℝ) * f k)).comp hW).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC (W ω)) (abs_nonneg _)
  have hInt_op : Integrable (fun ω ↦ poissonSteinOp r f (W ω)) P :=
    (hInt_fW1.const_mul (r : ℝ)).sub hInt_WfW
  have hInt_c_diff :
      Integrable (fun ω ↦
        c * (condExpAt F mΩ P (S_up.indicator (1 : Ω → ℝ)) ω * f (W ω + 1) -
          condExpAt F mΩ P (S_down.indicator (1 : Ω → ℝ)) ω * f (W ω))) P :=
    (hInt_cond_up.sub hInt_cond_down).const_mul c
  have hrew :
      (fun ω ↦
        (((r : ℝ) - c * condExpAt F mΩ P (S_up.indicator (1 : Ω → ℝ)) ω) * f (W ω + 1) -
          ((W ω : ℝ) - c * condExpAt F mΩ P (S_down.indicator (1 : Ω → ℝ)) ω) * f (W ω))) =
        fun ω ↦ poissonSteinOp r f (W ω) -
          c * (condExpAt F mΩ P (S_up.indicator (1 : Ω → ℝ)) ω * f (W ω + 1) -
            condExpAt F mΩ P (S_down.indicator (1 : Ω → ℝ)) ω * f (W ω)) := by
    ext ω; dsimp [poissonSteinOp]; ring
  rw [hrew, integral_sub hInt_op hInt_c_diff, integral_const_mul,
    integral_sub hInt_cond_up hInt_cond_down, h_cond_eq, mul_zero, sub_zero]

/-- Theorem 4.20 (`\label{thm161}`, `SteinIntro.tex:2618-2626`): Poisson TV bound via
exchangeable pairs. The expectations on the RHS use `lintegral` (`ℝ≥0∞`-valued) to avoid
junk-zero when $W$ may not be integrable (`stmts-review-05H` `H1`).

The sub-σ-algebra `F` satisfies `σ(W) ≤ F ≤ mΩ`. We use `condExpAt F mΩ P` to avoid
instance-resolution issues when two `MeasurableSpace Ω` values are in scope. -/
theorem tvDist_poissonLaw_exchangeable_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {W W' : Ω → ℕ}
    (hr : 0 < r)
    (hW : Measurable W) (hW' : Measurable W')
    (hex : IsExchangeablePair P W W')
    {F : MeasurableSpace Ω} (hFle : F ≤ mΩ)
    (hWF : MeasurableSpace.comap W inferInstance ≤ F)
    (c : ℝ) :
    @tvDist ℕ _ (@Measure.map Ω ℕ mΩ _ W P) (poissonLaw r) ≤
      ENNReal.ofReal (min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))) *
        (@lintegral Ω mΩ P (fun ω ↦ ENNReal.ofReal |(r : ℝ) - c *
            condExpAt F mΩ P
              ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω|) +
         @lintegral Ω mΩ P (fun ω ↦ ENNReal.ofReal |(W ω : ℝ) - c *
            condExpAt F mΩ P
              ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω|)) := by
  let _ : MeasurableSpace Ω := mΩ
  let S_up : Set Ω := {ω' | W' ω' = W ω' + 1}
  let S_down : Set Ω := {ω' | W ω' = W' ω' + 1}
  let u₁ : Ω → ℝ := condExpAt F mΩ P (S_up.indicator (1 : Ω → ℝ))
  let u₂ : Ω → ℝ := condExpAt F mΩ P (S_down.indicator (1 : Ω → ℝ))
  let g₁ : Ω → ℝ := fun ω ↦ (r : ℝ) - c * u₁ ω
  let g₂ : Ω → ℝ := fun ω ↦ (W ω : ℝ) - c * u₂ ω
  let M : ℝ := min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))
  have hM_pos : 0 < M := lt_min zero_lt_one (Real.rpow_pos_of_pos (by positivity) _)
  have hM_nn : 0 ≤ M := hM_pos.le
  have hM_ne : ENNReal.ofReal M ≠ 0 := (ENNReal.ofReal_pos.mpr hM_pos).ne'
  rcases eq_or_ne (∫⁻ ω, ENNReal.ofReal |g₂ ω| ∂P) ⊤ with hg₂_top | hg₂_fin
  · change @tvDist ℕ _ (@Measure.map Ω ℕ mΩ _ W P) (poissonLaw r) ≤
      ENNReal.ofReal M * ((∫⁻ ω, ENNReal.ofReal |g₁ ω| ∂P) + ∫⁻ ω, ENNReal.ofReal |g₂ ω| ∂P)
    rw [hg₂_top, add_top, ENNReal.mul_top hM_ne]
    exact le_top
  · have hu₁_int : Integrable u₁ P := integrable_condExp
    have hu₂_int : Integrable u₂ P := integrable_condExp
    have hg₁_int : Integrable g₁ P := (integrable_const (r : ℝ)).sub (hu₁_int.const_mul c)
    have hg₂_aesm : AEStronglyMeasurable g₂ P :=
      (((Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp hW).aestronglyMeasurable).sub
        (hu₂_int.const_mul c).aestronglyMeasurable
    have hg₂_hfi : HasFiniteIntegral g₂ P := by
      rw [hasFiniteIntegral_iff_norm]
      simpa only [Real.norm_eq_abs] using hg₂_fin.lt_top
    have hg₂_int : Integrable g₂ P := ⟨hg₂_aesm, hg₂_hfi⟩
    have hIntW : Integrable (fun ω ↦ (W ω : ℝ)) P := by
      have h_eq : (fun ω ↦ (W ω : ℝ)) = g₂ + (fun ω ↦ c * u₂ ω) := by
        ext ω; simp [g₂]
      rw [h_eq]
      exact hg₂_int.add (hu₂_int.const_mul c)
    have hlint₁ :
        (∫⁻ ω, ENNReal.ofReal |g₁ ω| ∂P) = ENNReal.ofReal (∫ ω, |g₁ ω| ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hg₁_int.norm
        (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _)).symm
    have hlint₂ :
        (∫⁻ ω, ENNReal.ofReal |g₂ ω| ∂P) = ENNReal.ofReal (∫ ω, |g₂ ω| ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hg₂_int.norm
        (Filter.Eventually.of_forall fun ω ↦ abs_nonneg _)).symm
    have hI₁_nn : 0 ≤ ∫ ω, |g₁ ω| ∂P := integral_nonneg fun ω ↦ abs_nonneg _
    have hI₂_nn : 0 ≤ ∫ ω, |g₂ ω| ∂P := integral_nonneg fun ω ↦ abs_nonneg _
    change @tvDist ℕ _ (@Measure.map Ω ℕ mΩ _ W P) (poissonLaw r) ≤
      ENNReal.ofReal M * ((∫⁻ ω, ENNReal.ofReal |g₁ ω| ∂P) + ∫⁻ ω, ENNReal.ofReal |g₂ ω| ∂P)
    rw [hlint₁, hlint₂, ← ENNReal.ofReal_add hI₁_nn hI₂_nn, ← ENNReal.ofReal_mul hM_nn]
    have : IsProbabilityMeasure (@Measure.map Ω ℕ mΩ _ W P) :=
      ⟨by rw [Measure.map_apply hW .univ, Set.preimage_univ, measure_univ]⟩
    rw [tvDist_eq_iSup]
    refine iSup₂_le fun A hA ↦ ENNReal.ofReal_le_ofReal ?_
    rw [map_measureReal_apply hW hA]
    have hcor := abs_measureReal_sub_poissonLaw_eq P hr hW.aemeasurable A
    let f : ℕ → ℝ := poissonSteinSol r A
    have hf_le : ∀ k : ℕ, |f k| ≤ M := abs_poissonSteinSol_le hr A
    have hid :=
      integral_poissonSteinOp_exchangeable_eq P hr hW hW' hex hIntW hFle hWF f ⟨M, hf_le⟩ c
    have h_op : (fun ω ↦ poissonSteinOp r f (W ω)) =
        fun ω ↦ (r : ℝ) * f (W ω + 1) - (W ω : ℝ) * f (W ω) := by
      ext ω; rfl
    have hcor_rw : |P.real {ω | W ω ∈ A} - (poissonLaw r).real A| =
        |∫ ω, poissonSteinOp r f (W ω) ∂P| := by
      rw [hcor, h_op]
    rw [show (W ⁻¹' A : Set Ω) = {ω | W ω ∈ A} from rfl]
    rw [hcor_rw, hid]
    have hInt_term1 : Integrable (fun ω ↦ g₁ ω * f (W ω + 1)) P := by
      have hf1_aesm : AEStronglyMeasurable (fun ω ↦ f (W ω + 1)) P :=
        ((Measurable.of_discrete (f := fun k : ℕ ↦ f (k + 1))).comp hW).aestronglyMeasurable
      refine Integrable.mono' (hg₁_int.norm.mul_const M)
        (hg₁_int.aestronglyMeasurable.mul hf1_aesm)
        (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf_le (W ω + 1)) (abs_nonneg _)
    have hInt_term2 : Integrable (fun ω ↦ g₂ ω * f (W ω)) P := by
      have hf_aesm : AEStronglyMeasurable (fun ω ↦ f (W ω)) P :=
        ((Measurable.of_discrete (f := f)).comp hW).aestronglyMeasurable
      refine Integrable.mono' (hg₂_int.norm.mul_const M)
        (hg₂_int.aestronglyMeasurable.mul hf_aesm)
        (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hf_le (W ω)) (abs_nonneg _)
    change |∫ ω, (g₁ ω * f (W ω + 1) - g₂ ω * f (W ω)) ∂P| ≤ _
    rw [integral_sub hInt_term1 hInt_term2]
    have hb1 : |∫ ω, g₁ ω * f (W ω + 1) ∂P| ≤ M * ∫ ω, |g₁ ω| ∂P := by
      calc
        |∫ ω, g₁ ω * f (W ω + 1) ∂P|
            ≤ ∫ ω, ‖g₁ ω * f (W ω + 1)‖ ∂P := by
              rw [← Real.norm_eq_abs]
              exact norm_integral_le_integral_norm _
        _ ≤ ∫ ω, M * |g₁ ω| ∂P := by
              refine integral_mono_ae hInt_term1.norm (hg₁_int.norm.const_mul M)
                (Filter.Eventually.of_forall fun ω ↦ ?_)
              dsimp only
              rw [Real.norm_eq_abs, abs_mul, mul_comm M]
              exact mul_le_mul_of_nonneg_left (hf_le (W ω + 1)) (abs_nonneg _)
        _ = M * ∫ ω, |g₁ ω| ∂P := integral_const_mul M _
    have hb2 : |∫ ω, g₂ ω * f (W ω) ∂P| ≤ M * ∫ ω, |g₂ ω| ∂P := by
      calc
        |∫ ω, g₂ ω * f (W ω) ∂P|
            ≤ ∫ ω, ‖g₂ ω * f (W ω)‖ ∂P := by
              rw [← Real.norm_eq_abs]
              exact norm_integral_le_integral_norm _
        _ ≤ ∫ ω, M * |g₂ ω| ∂P := by
              refine integral_mono_ae hInt_term2.norm (hg₂_int.norm.const_mul M)
                (Filter.Eventually.of_forall fun ω ↦ ?_)
              dsimp only
              rw [Real.norm_eq_abs, abs_mul, mul_comm M]
              exact mul_le_mul_of_nonneg_left (hf_le (W ω)) (abs_nonneg _)
        _ = M * ∫ ω, |g₂ ω| ∂P := integral_const_mul M _
    have htri := abs_sub (∫ ω, g₁ ω * f (W ω + 1) ∂P) (∫ ω, g₂ ω * f (W ω) ∂P)
    linarith

end SteinMethod
