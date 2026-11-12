/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Branching.Basic
import Formalization.Canon.Distributions
import Formalization.Canon.GraphsAndPerms
import Formalization.Defs
import Formalization.Defs.Branching
import Formalization.Defs.Couplings
import Formalization.Defs.Laws
import Formalization.Defs.Metrics
import Formalization.Defs.PoissonSizeBias
import Formalization.Defs.PoissonSizeBiasSubgraph
import Formalization.Defs.RandomGraph
import Formalization.Defs.Sanity
import Formalization.PoissonSizeBias.Core.Exchangeable
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.IdentDistrib

/-!
# Canonical Follow-Up Bridges (`Formalization.Canon.Followups`)

Provides required follow-up bridges (batch-CANON-phase2b) connecting project definitions with
Mathlib:
* `poissonLaw_real_singleton_eq_poissonPMFReal`: point probability under `poissonLaw`
  matching Mathlib's `ProbabilityTheory.poissonPMFReal`;
* `gwTreeGenSize_eq_card_gwVertex`: generation-indexed tree size `gwTreeGenSize` matching
  Mathlib's `Fintype.card (GWVertex t)`;
* `subgraphCount_eq_card_filter_le`: subgraph count $W(G)$ matching Mathlib's `Finset.card`
  of filtered subgraph copies;
* `erdosRenyi_eq_binomialRandom_of_mem_Icc`: Erdős–Rényi random graph law matching
  Mathlib's `SimpleGraph.binomialRandom` on $[0, 1]$;
* `rademacherPairMeasure_eq_prod`: independent Rademacher pair measure matching Mathlib's
  product measure `Measure.prod bernoulliHalfMeasure bernoulliHalfMeasure`;
* `isExchangeablePair_iff_map_eq` & `isExchangeablePair_iff_map_swap`: exchangeable pair
  characterizations via Mathlib pushforward measures and `Prod.swap` invariance;
* `isExchangeableTuple_fin_two_iff_isExchangeablePair`: `Fin 2` exchangeable tuple equivalence
  with exchangeable pair;
* `wassersteinDist_eq_iSup_lipschitz_one`: Wasserstein-1 distance unconditioned supremum over
  1-Lipschitz test functions for probability measures with finite first moments;
* `isSizeBias_iff_map_eq_withDensity`: full `iff` Radon–Nikodym characterization of `IsSizeBias`
  via Mathlib's `MeasureTheory.Measure.withDensity`.
-/

open scoped NNReal ENNReal BigOperators
open MeasureTheory ProbabilityTheory

namespace SteinMethod

set_option linter.deprecated false in
/-- Point probability under `poissonLaw` (`Formalization/Defs/Laws.lean:45`,
`SteinIntro.tex:1823-1848`) matches Mathlib's `ProbabilityTheory.poissonPMFReal`
(`Mathlib/Probability/Distributions/Poisson/Basic.lean:210`). -/
theorem poissonLaw_real_singleton_eq_poissonPMFReal (r : ℝ≥0) (k : ℕ) :
    (poissonLaw r).real {k} = ProbabilityTheory.poissonPMFReal r k := by
  rw [poissonLaw_eq_poissonMeasure, ProbabilityTheory.poissonMeasure_real_singleton]
  rfl

/-- Equivalence between the generation-indexed total size `gwTreeGenSize`
(`Formalization/Defs/Branching.lean:56`, `SteinIntro.tex:2993-3001`) and Mathlib's
`Fintype.card (GWVertex t)` via `Formalization/Branching/Basic.lean:58`. -/
theorem gwTreeGenSize_eq_card_gwVertex {n : ℕ} (t : GWTree n) :
    gwTreeGenSize t = Fintype.card (GWVertex t) :=
  (card_gwVertex_eq_gwTreeGenSize t).symm

open Classical in
/-- Equivalence of the subgraph count $W(G)$ (`SteinIntro.tex:2286-2287`,
`Formalization/Defs/PoissonSizeBiasSubgraph.lean:53`) with the Mathlib `Finset.card` of the
filtered copy set `(subgraphCopies H n).filter (fun α ↦ α ≤ G)`. -/
theorem subgraphCount_eq_card_filter_le {V : Type*} (H : SimpleGraph V) (n : ℕ)
    (G : SimpleGraph (Fin n)) :
    subgraphCount H n G = ((subgraphCopies H n).filter (fun α ↦ α ≤ G)).card := by
  unfold subgraphCount subgraphCopyIndicator
  rw [Finset.sum_boole]
  rfl

/-- For $p \in [0, 1]$, the Erdős–Rényi random graph law `erdosRenyi n p`
(`SteinIntro.tex:919`, `SteinIntro.tex:1355`, `Formalization/Defs/RandomGraph.lean:45`) equals
Mathlib's `SimpleGraph.binomialRandom (Fin n) ⟨p, hp⟩`
(`Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean:46`). -/
theorem erdosRenyi_eq_binomialRandom_of_mem_Icc (n : ℕ) {p : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    erdosRenyi n p = SimpleGraph.binomialRandom (Fin n) ⟨p, hp⟩ := by
  rw [erdosRenyi_eq_binomialRandom, Set.projIcc_of_mem _ hp]

private lemma bernoulliHalfMeasure_singleton (b : Bool) :
    bernoulliHalfMeasure {b} = (1 / 2 : ℝ≥0∞) := by
  cases b
  · rw [bernoulliHalfMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply, Measure.dirac_apply]
    simp
  · rw [bernoulliHalfMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply, Measure.dirac_apply]
    simp

private lemma rademacherPairMeasure_singleton (x y : Bool) :
    rademacherPairMeasure {(x, y)} = (1 / 4 : ℝ≥0∞) := by
  cases x <;> cases y
  · rw [rademacherPairMeasure, Measure.smul_apply, Measure.add_apply, Measure.add_apply,
      Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply, Measure.dirac_apply,
      Measure.dirac_apply]
    simp
  · rw [rademacherPairMeasure, Measure.smul_apply, Measure.add_apply, Measure.add_apply,
      Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply, Measure.dirac_apply,
      Measure.dirac_apply]
    simp
  · rw [rademacherPairMeasure, Measure.smul_apply, Measure.add_apply, Measure.add_apply,
      Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply, Measure.dirac_apply,
      Measure.dirac_apply]
    simp
  · rw [rademacherPairMeasure, Measure.smul_apply, Measure.add_apply, Measure.add_apply,
      Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply, Measure.dirac_apply,
      Measure.dirac_apply]
    simp

/-- The joint distribution `rademacherPairMeasure` (`Formalization/Defs/Sanity.lean:211`,
`SteinIntro.tex:952-960`) of an independent pair of Rademacher/symmetric Bernoulli signs
equals Mathlib's product measure `Measure.prod bernoulliHalfMeasure bernoulliHalfMeasure`. -/
theorem rademacherPairMeasure_eq_prod :
    rademacherPairMeasure =
      Measure.prod (α := Bool) (β := Bool) bernoulliHalfMeasure bernoulliHalfMeasure := by
  refine Measure.ext_of_singleton fun ⟨b1, b2⟩ ↦ ?_
  have hprod : (Measure.prod (α := Bool) (β := Bool)
      bernoulliHalfMeasure bernoulliHalfMeasure) {(b1, b2)} =
        bernoulliHalfMeasure {b1} * bernoulliHalfMeasure {b2} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [hprod, bernoulliHalfMeasure_singleton, bernoulliHalfMeasure_singleton,
    rademacherPairMeasure_singleton]
  have h_half : (1 / 2 : ℝ≥0∞) = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, ← ENNReal.coe_ofNat, ← ENNReal.coe_div (by norm_num)]
  have h_fourth : (1 / 4 : ℝ≥0∞) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, ← ENNReal.coe_ofNat, ← ENNReal.coe_div (by norm_num)]
  rw [h_fourth, h_half, ← ENNReal.coe_mul]
  congr 1
  ext
  push_cast
  norm_num

/-- Characterization of exchangeable pairs (`SteinIntro.tex:952-954`,
`Formalization/Defs/Couplings.lean:24`) via equality of Mathlib pushforward measures
`MeasureTheory.Measure.map`: $(W, W')$ is an exchangeable pair if and only if
$P_*(W, W') = P_*(W', W)$. -/
theorem isExchangeablePair_iff_map_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) {W W' : Ω → α}
    (hW : Measurable W) (hW' : Measurable W') :
    IsExchangeablePair P W W' ↔
      P.map (fun ω ↦ (W ω, W' ω)) = P.map (fun ω ↦ (W' ω, W ω)) := by
  have h1 : Measurable (fun ω ↦ (W ω, W' ω)) := hW.prodMk hW'
  have h2 : Measurable (fun ω ↦ (W' ω, W ω)) := hW'.prodMk hW
  constructor
  · intro h
    exact h.map_eq
  · intro h
    exact ⟨h1.aemeasurable, h2.aemeasurable, h⟩

/-- Characterization of exchangeable pairs (`SteinIntro.tex:952-954`,
`Formalization/Defs/Couplings.lean:24`) via Mathlib `Prod.swap` pushforward invariance:
$(W, W')$ is an exchangeable pair if and only if the joint pushforward $P_*(W, W')$ is
invariant under `Prod.swap`. -/
theorem isExchangeablePair_iff_map_swap
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) {W W' : Ω → α}
    (hW : Measurable W) (hW' : Measurable W') :
    IsExchangeablePair P W W' ↔
      (P.map (fun ω ↦ (W ω, W' ω))).map Prod.swap = P.map (fun ω ↦ (W ω, W' ω)) := by
  have h1 : Measurable (fun ω ↦ (W ω, W' ω)) := hW.prodMk hW'
  rw [isExchangeablePair_iff_map_eq P hW hW']
  have hswap : (P.map (fun ω ↦ (W ω, W' ω))).map Prod.swap =
      P.map (fun ω ↦ (W' ω, W ω)) := by
    rw [Measure.map_map measurable_swap h1]
    rfl
  rw [hswap, eq_comm]

/-- Equivalence between `IsExchangeableTuple` on `Fin 2` (`SteinIntro.tex:2148-2154`,
`Formalization/Defs/PoissonSizeBias.lean:30`) and `IsExchangeablePair`
(`SteinIntro.tex:952-954`, `Formalization/Defs/Couplings.lean:24`) via Mathlib `Fin 2`
permutations. -/
theorem isExchangeableTuple_fin_two_iff_isExchangeablePair
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (X : Fin 2 → Ω → α) :
    IsExchangeableTuple P X ↔ IsExchangeablePair P (X 0) (X 1) := by
  have hX : X = ![X 0, X 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hX]
  exact isExchangeableTuple_fin_two_iff P (X 0) (X 1)

private theorem lipschitz_integrable_of_integrable_id (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {h : ℝ → ℝ} (hlip : LipschitzWith 1 h) :
    Integrable h μ := by
  have h_norm_le (x : ℝ) : ‖h x‖ ≤ ‖h 0‖ + ‖x‖ := by
    have hdist := hlip.dist_le_mul x 0
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, sub_zero] at hdist
    have htri : ‖h x‖ ≤ ‖h 0‖ + ‖h x - h 0‖ := by
      have : h x = h 0 + (h x - h 0) := by ring
      nth_rw 1 [this]
      exact norm_add_le (h 0) (h x - h 0)
    have hnorm_sub : ‖h x - h 0‖ ≤ ‖x‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hdist
    linarith
  have h_bd : Integrable (fun x ↦ ‖h 0‖ + ‖x‖) μ :=
    (integrable_const (‖h 0‖)).add hμ.norm
  exact Integrable.mono' h_bd hlip.continuous.aestronglyMeasurable
    (ae_of_all μ h_norm_le)

/-- For probability measures $\mu, \nu$ with finite first moments (`Integrable id μ`,
`Integrable id ν`), the Wasserstein-1 distance `wassersteinDist` (`SteinIntro.tex:516-519`,
`Formalization/Defs/Metrics.lean:37`) equals Mathlib's unconditioned supremum over
1-Lipschitz test functions `LipschitzWith 1 h` without auxiliary integrability assumptions. -/
theorem wassersteinDist_eq_iSup_lipschitz_one (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) :
    wassersteinDist μ ν =
      ⨆ (h : ℝ → ℝ) (_ : LipschitzWith 1 h),
        ENNReal.ofReal |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| := by
  change ipm {h | LipschitzWith 1 h} μ ν = _
  rw [ipm]
  refine iSup_congr fun h ↦ ?_
  refine iSup_congr fun (hlip : LipschitzWith 1 h) ↦ ?_
  have h_int_μ : Integrable h μ := lipschitz_integrable_of_integrable_id μ hμ hlip
  have h_int_ν : Integrable h ν := lipschitz_integrable_of_integrable_id ν hν hlip
  rw [iSup_pos ⟨h_int_μ, h_int_ν⟩]

/-- Full `iff` Radon–Nikodym characterization of `IsSizeBias` (`SteinIntro.tex:1224-1230`,
`Formalization/Defs/Couplings.lean:39`): for almost surely non-negative $X$ with positive mean,
$X^s$ is a size-bias distribution for $X$ under $P'$ if and only if $X^s$ is almost everywhere
measurable and its pushforward $P'_* X^s$ has density $x \mapsto x / \mathbb{E}[X]$ with
respect to $P_* X$ (`MeasureTheory.Measure.withDensity`). -/
theorem isSizeBias_iff_map_eq_withDensity
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Xs : Ω' → ℝ}
    (hX_meas : Measurable X) (hX_nn : 0 ≤ᵐ[P] X) (hX_int : Integrable X P)
    (hX_pos : 0 < ∫ ω, X ω ∂P) :
    IsSizeBias P X P' Xs ↔
      AEMeasurable Xs P' ∧
        P'.map Xs = (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / ∫ ω, X ω ∂P)) := by
  set μX : ℝ := ∫ ω, X ω ∂P
  constructor
  · intro hsb
    exact ⟨hsb.2.2.1, map_sizeBias_eq_withDensity P P' hX_meas hX_int hX_pos hsb⟩
  · rintro ⟨hXs_ae, hmap⟩
    refine ⟨hX_nn, hX_int, hXs_ae, fun f hf_meas hf_int ↦ ?_⟩
    set d : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (x / μX)
    have hd_meas : Measurable d := ENNReal.measurable_ofReal.comp (measurable_id.div_const μX)
    have hd_lt_top : ∀ᵐ x ∂(P.map X), d x < ∞ :=
      ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top
    have h_int_Xs : ∫ ω', f (Xs ω') ∂P' = ∫ x, f x ∂(P'.map Xs) := by
      rw [← integral_map hXs_ae hf_meas.stronglyMeasurable.aestronglyMeasurable]
    have h_int_dens : ∫ x, f x ∂(P'.map Xs) = ∫ x, (d x).toReal * f x ∂(P.map X) := by
      rw [hmap]
      exact integral_withDensity_eq_integral_toReal_smul (μ := P.map X) hd_meas hd_lt_top f
    have hX_nn_map : ∀ᵐ x ∂(P.map X), 0 ≤ x := by
      rw [ae_map_iff (hX_meas.aemeasurable (μ := P)) measurableSet_Ici]
      exact hX_nn
    have hd_ae : (fun x ↦ (d x).toReal * f x) =ᵐ[P.map X] fun x ↦ μX⁻¹ * (x * f x) := by
      filter_upwards [hX_nn_map] with x hx
      dsimp [d] at *
      have hdiv_nn : 0 ≤ x / μX := div_nonneg hx hX_pos.le
      rw [ENNReal.toReal_ofReal hdiv_nn]
      ring
    have h_int_cv : ∫ x, x * f x ∂(P.map X) = ∫ ω, X ω * f (X ω) ∂P :=
      integral_map (hX_meas.aemeasurable (μ := P))
        (measurable_id.mul hf_meas).stronglyMeasurable.aestronglyMeasurable
    rw [h_int_Xs, h_int_dens, integral_congr_ae hd_ae, integral_const_mul, h_int_cv]
    change _ = μX * (μX⁻¹ * _); rw [← mul_assoc, mul_inv_cancel₀ hX_pos.ne', one_mul]

end SteinMethod
