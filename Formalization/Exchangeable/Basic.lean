/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Couplings
import Mathlib.Algebra.Ring.CharZero
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Basic Properties of Exchangeable Pairs (`Formalization.Exchangeable.Basic`)

General distributional symmetry helpers for `IsExchangeablePair` (Definition 3.2,
`SteinIntro.tex:952-954`) and Proposition 3.6(1) (`\label{prop51}`, `SteinIntro.tex:962-971`):
for any exchangeable pair $(W, W')$ and antisymmetric measurable function $F$,
$\mathbb{E}[F(W, W')] = 0$ without any integrability hypothesis.
-/

open MeasureTheory ProbabilityTheory

namespace SteinMethod

/-- Symmetry of `IsExchangeablePair` (Definition 3.2, `SteinIntro.tex:952-954`): if $(W, W')$ is
an exchangeable pair, then $(W', W)$ is also an exchangeable pair. -/
theorem IsExchangeablePair.symm
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {W W' : Ω → α}
    (hExch : IsExchangeablePair P W W') :
    IsExchangeablePair P W' W :=
  ProbabilityTheory.IdentDistrib.symm hExch

/-- Marginal equality in distribution for an exchangeable pair (Definition 3.2,
`SteinIntro.tex:952-954`): $W \stackrel{d}{=} W'$. -/
theorem IsExchangeablePair.fst_identDistrib_snd
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {W W' : Ω → α}
    (hExch : IsExchangeablePair P W W') :
    IdentDistrib W W' P P :=
  ProbabilityTheory.IdentDistrib.comp hExch measurable_fst

/-- Symmetric marginal equality in distribution for an exchangeable pair (Definition 3.2,
`SteinIntro.tex:952-954`): $W' \stackrel{d}{=} W$. -/
theorem IsExchangeablePair.snd_identDistrib_fst
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {W W' : Ω → α}
    (hExch : IsExchangeablePair P W W') :
    IdentDistrib W' W P P :=
  hExch.fst_identDistrib_snd.symm

/-- Applying a measurable function $F : \alpha \times \alpha \to \beta$ to an exchangeable pair
$(W, W')$ yields identically distributed random variables $F(W, W')$ and $F(W', W)$
(Definition 3.2, `SteinIntro.tex:952-954`). -/
theorem IsExchangeablePair.comp
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} {W W' : Ω → α}
    (hExch : IsExchangeablePair P W W')
    {F : α × α → β} (hF : Measurable F) :
    IdentDistrib (fun ω ↦ F (W ω, W' ω)) (fun ω ↦ F (W' ω, W ω)) P P :=
  ProbabilityTheory.IdentDistrib.comp hExch hF

/-- Proposition 3.6(1) (`\label{prop51}`, `SteinIntro.tex:962-971`) on an arbitrary measurable
space: if $(W, W')$ is an exchangeable pair and $F : \alpha \times \alpha \to \mathbb{R}$ is
measurable and antisymmetric ($F(x, y) = -F(y, x)$), then $\int F(W, W')\,dP = 0$.

No `Integrable` hypothesis is needed: if $F(W, W')$ is not Bochner-integrable, Mathlib's Bochner
integral evaluates both sides of $\int F(W, W')\,dP = \int F(W', W)\,dP$ to $0$; `Measurable F` is
only the measurable-function typing of $F$. -/
theorem IsExchangeablePair.integral_antisymm_eq_zero
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {W W' : Ω → α}
    (hExch : IsExchangeablePair P W W')
    {F : α × α → ℝ} (hF : Measurable F)
    (hAnti : ∀ x y : α, F (x, y) = -F (y, x)) :
    ∫ ω, F (W ω, W' ω) ∂P = 0 := by
  have hEq : ∫ ω, F (W ω, W' ω) ∂P = -∫ ω, F (W ω, W' ω) ∂P := calc
    ∫ ω, F (W ω, W' ω) ∂P = ∫ ω, F (W' ω, W ω) ∂P := (hExch.comp hF).integral_eq
    _ = ∫ ω, -F (W ω, W' ω) ∂P :=
      congrArg (fun g : Ω → ℝ ↦ ∫ ω, g ω ∂P) (funext fun ω ↦ hAnti (W' ω) (W ω))
    _ = -∫ ω, F (W ω, W' ω) ∂P := integral_neg (fun ω ↦ F (W ω, W' ω))
  exact CharZero.eq_neg_self_iff.mp hEq

/-- General $a > 0$ library version of Proposition 3.6(2) (`\label{prop51}`,
`SteinIntro.tex:967-971`, proof `SteinIntro.tex:977-981`; ruling `D7`): if $(W, W')$ is an
exchangeable pair with $0 < a$, measurable $W \in L^2(P)$, and
$\mathbb{E}[W' \mid W] = (1 - a) W$ a.s., then $\mathbb{E}[W] = 0$ and
$\mathbb{E}[(W' - W)^2] = 2 a \operatorname{Var}(W)$. -/
theorem steinPair_integral_eq_zero_and_sq_sub_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hExch : IsExchangeablePair P W W') (ha : 0 < a)
    (hW_meas : Measurable W) (hW2 : MemLp W 2 P)
    (hCond : P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω) :
    ∫ ω, W ω ∂P = 0 ∧
      ∫ ω, (W' ω - W ω) ^ 2 ∂P = 2 * a * ProbabilityTheory.variance W P := by
  have hId : IdentDistrib W W' P P := hExch.fst_identDistrib_snd
  have hW'2 : MemLp W' 2 P := hId.memLp_snd hW2
  have hW'_int : Integrable W' P := hW'2.integrable one_le_two
  have hm := hW_meas.comap_le
  have hMeanEq : ∫ ω, W ω ∂P = (1 - a) * ∫ ω, W ω ∂P := calc
    ∫ ω, W ω ∂P = ∫ ω, W' ω ∂P := hId.integral_eq
    _ = ∫ ω, P[W' | MeasurableSpace.comap W inferInstance] ω ∂P :=
      (integral_condExp (μ := P) (f := W') hm).symm
    _ = ∫ ω, (1 - a) * W ω ∂P := integral_congr_ae hCond
    _ = (1 - a) * ∫ ω, W ω ∂P := integral_const_mul (1 - a) W
  have haMean : a * ∫ ω, W ω ∂P = 0 := by linarith
  have hMean : ∫ ω, W ω ∂P = 0 := (mul_eq_zero.mp haMean).resolve_left ha.ne'
  refine ⟨hMean, ?_⟩
  have hWW'_int : Integrable (W * W') P := hW2.integrable_mul hW'2
  have hW_sm : StronglyMeasurable[MeasurableSpace.comap W inferInstance] W :=
    Measurable.stronglyMeasurable (comap_measurable (m := inferInstance) W)
  have hCondMul :
      P[W * W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω ^ 2 := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left hW_sm hWW'_int hW'_int, hCond]
      with ω hω1 hω2
    rw [hω1, Pi.mul_apply, hω2]
    ring
  have hProdEq : ∫ ω, W ω * W' ω ∂P = (1 - a) * ∫ ω, W ω ^ 2 ∂P := calc
    ∫ ω, W ω * W' ω ∂P = ∫ ω, (W * W') ω ∂P := rfl
    _ = ∫ ω, P[W * W' | MeasurableSpace.comap W inferInstance] ω ∂P :=
      (integral_condExp (μ := P) (f := W * W') hm).symm
    _ = ∫ ω, (1 - a) * W ω ^ 2 ∂P := integral_congr_ae hCondMul
    _ = (1 - a) * ∫ ω, W ω ^ 2 ∂P := integral_const_mul (1 - a) (fun ω ↦ W ω ^ 2)
  have hW_sq_int : Integrable (fun ω ↦ W ω ^ 2) P := hW2.integrable_sq
  have hW'_sq_int : Integrable (fun ω ↦ W' ω ^ 2) P := hW'2.integrable_sq
  have hTwoWW'_int : Integrable (fun ω ↦ 2 * (W ω * W' ω)) P := hWW'_int.const_mul 2
  have hexp : (fun ω ↦ (W' ω - W ω) ^ 2) = fun ω ↦ (W' ω ^ 2 + W ω ^ 2) - 2 * (W ω * W' ω) :=
    funext fun ω ↦ by ring
  rw [hexp, integral_sub (hW'_sq_int.fun_add hW_sq_int) hTwoWW'_int,
    integral_add hW'_sq_int hW_sq_int, integral_const_mul 2 (fun ω ↦ W ω * W' ω),
    ← hId.sq.integral_eq, hProdEq,
    ProbabilityTheory.variance_of_integral_eq_zero hW_meas.aemeasurable hMean]
  ring

/-- Proposition 3.6(2) (`\label{prop51}`, `SteinIntro.tex:967-971`,
proof `SteinIntro.tex:977-981`): if $(W, W')$ is an $a$-Stein pair with finite second moment
(`MemLp W 2 P`), then $\mathbb{E}[W] = 0$ and
$\mathbb{E}[(W' - W)^2] = 2 a \operatorname{Var}(W)$. -/
theorem IsSteinPair.integral_eq_zero_and_sq_sub_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ}
    (hSP : IsSteinPair P a W W') (hW2 : MemLp W 2 P) :
    ∫ ω, W ω ∂P = 0 ∧
      ∫ ω, (W' ω - W ω) ^ 2 ∂P = 2 * a * ProbabilityTheory.variance W P := by
  rcases hSP with ⟨hExch, ha, _, hW_meas, _, hCond⟩
  exact steinPair_integral_eq_zero_and_sq_sub_eq P hExch ha hW_meas hW2 hCond

end SteinMethod
