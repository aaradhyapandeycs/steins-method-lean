/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.Concentration
import Formalization.Defs.OrnsteinUhlenbeck
import Formalization.Defs.PoissonDep
import Formalization.Leftovers.OrnsteinUhlenbeck
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Canonical Markov Kernels and Information Measures (`Formalization.Canon.MarkovAndEntropy`)

Bridges project-specific Markov chains, diffusion kernels, entropy, and Gibbs measures to
Mathlib's `ProbabilityTheory.Kernel.Invariant`, `InformationTheory.klDiv`, and `PMF.ofFintype`:
* `antiVoterKernel` / `isAntiVoterStationary_iff_kernel_invariant`: Markov kernel representation
  and stationarity for the anti-voter model on finite graphs (`SteinIntro.tex:1103-1116`,
  `Formalization/Defs/AntiVoter.lean:38, 51`).
* `ouKernel_apply_eq_gaussianReal`: evaluation of `ouKernel a` as `gaussianReal`
  (`SteinIntro.tex:1009-1024`, `Formalization/Defs/OrnsteinUhlenbeck.lean:24`).
* `ouKernel_invariant_stdNormalLaw`: stationarity of `stdNormalLaw` under `ouKernel a`
  (`SteinIntro.tex:1018-1019`, `Mathlib/Probability/Kernel/Invariance.lean:39`).
* `curieWeissMeasure_eq_pmf_ofFintype`: Curie–Weiss Gibbs measure as a `PMF.toMeasure`
  (`SteinIntro.tex:3631-3637`, `Formalization/Defs/Concentration.lean:42`).
* `klDivBernoulli_eq_klDiv`: binary relative entropy `klDivBernoulli` matching Mathlib
  `InformationTheory.klDiv` on `bernoulliMeasure` (`SteinIntro.tex:2071-2078`).
-/

open MeasureTheory ProbabilityTheory

namespace SteinMethod

/-- Discrete measurable singleton class on `V → Bool` for any finite type `V`. -/
instance instMeasurableSingletonClassPiBool {V : Type*} [Finite V] :
    MeasurableSingletonClass (V → Bool) := by
  refine ⟨fun y ↦ ?_⟩
  have heq : ({y} : Set (V → Bool)) = (Set.univ : Set V).pi (fun i ↦ {y i}) := by
    ext f; simp [funext_iff]
  rw [heq]
  exact (measurableSet_pi (Set.toFinite _).countable).mpr
    (Or.inl fun i _ ↦ measurableSet_singleton (y i))

/-! ### Anti-Voter Model Markov Kernel -/

/-- Canonical Markov kernel for the anti-voter Markov chain on a finite graph $G = (V, E)$
(`SteinIntro.tex:1103-1105`, `Formalization/Defs/AntiVoter.lean:38`). -/
noncomputable def antiVoterKernel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ProbabilityTheory.Kernel (V → Bool) (V → Bool) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun x ↦ (antiVoterStep G x).toMeasure

instance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ProbabilityTheory.IsMarkovKernel (antiVoterKernel G) := by
  refine ⟨fun x ↦ ?_⟩
  dsimp [antiVoterKernel, Kernel.ofFunOfCountable]
  infer_instance

/-- Stationarity of a measure `ν` under `antiVoterStep G` (`IsAntiVoterStationary`,
`SteinIntro.tex:1110-1116`, `Formalization/Defs/AntiVoter.lean:51`) is equivalent to invariance
under the canonical Markov kernel `antiVoterKernel G` (`ProbabilityTheory.Kernel.Invariant`,
`Mathlib/Probability/Kernel/Invariance.lean:39`). -/
theorem isAntiVoterStationary_iff_kernel_invariant {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) :
    IsAntiVoterStationary G ν ↔ ProbabilityTheory.Kernel.Invariant (antiVoterKernel G) ν := by
  constructor
  · intro hstat
    rw [ProbabilityTheory.Kernel.Invariant, Measure.ext_iff_singleton]
    intro y
    rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _)]
    dsimp [antiVoterKernel, Kernel.ofFunOfCountable]
    have hpt : (fun x : V → Bool ↦ (antiVoterStep G x).toMeasure {y}) =
        fun x ↦ antiVoterStep G x y := by
      funext x
      exact (antiVoterStep G x).toMeasure_apply_singleton y (measurableSet_singleton y)
    rw [hpt, lintegral_fintype]
    have hcomm : (fun x : V → Bool ↦ antiVoterStep G x y * ν {x}) =
        fun x ↦ ν {x} * antiVoterStep G x y := by
      funext x; rw [mul_comm]
    rw [hcomm]
    exact (hstat y).symm
  · intro hinv y
    have hext : ν.bind (antiVoterKernel G) = ν := hinv
    have hy := congrArg (fun m : Measure (V → Bool) ↦ m {y}) hext
    rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _)] at hy
    dsimp [antiVoterKernel, Kernel.ofFunOfCountable] at hy
    have hpt : (fun x : V → Bool ↦ (antiVoterStep G x).toMeasure {y}) =
        fun x ↦ antiVoterStep G x y := by
      funext x
      exact (antiVoterStep G x).toMeasure_apply_singleton y (measurableSet_singleton y)
    rw [hpt, lintegral_fintype] at hy
    have hcomm : (fun x : V → Bool ↦ antiVoterStep G x y * ν {x}) =
        fun x ↦ ν {x} * antiVoterStep G x y := by
      funext x; rw [mul_comm]
    rw [hcomm] at hy
    exact hy.symm

/-! ### Ornstein–Uhlenbeck Diffusion Kernel -/

/-- Pointwise evaluation of the Ornstein–Uhlenbeck transition kernel `ouKernel a`
(`SteinIntro.tex:1009-1024`, `Formalization/Defs/OrnsteinUhlenbeck.lean:24`) for $a > 0$ as the
Gaussian law $\mathcal{N}(e^{-a} x, 1 - e^{-2a})$ (`ProbabilityTheory.gaussianReal`). -/
theorem ouKernel_apply_eq_gaussianReal (a : ℝ) (ha : 0 < a) (x : ℝ) :
    ouKernel a x =
      ProbabilityTheory.gaussianReal (Real.exp (-a) * x)
        (Real.toNNReal (1 - Real.exp (-2 * a))) := by
  simp only [ouKernel, ha, ↓reduceIte]
  rfl

/-- Invariance of the standard normal law `stdNormalLaw` (`SteinIntro.tex:1018-1019`,
`Formalization/Defs/Laws.lean:29`) under the Ornstein–Uhlenbeck transition kernel `ouKernel a`
(`ProbabilityTheory.Kernel.Invariant`, `Mathlib/Probability/Kernel/Invariance.lean:39`). -/
theorem ouKernel_invariant_stdNormalLaw {a : ℝ} (ha : 0 < a) :
    ProbabilityTheory.Kernel.Invariant (ouKernel a) stdNormalLaw :=
  ouKernel_stationary ha

/-! ### Curie–Weiss Model Gibbs Measure -/

/-- Gibbs measure of the Curie–Weiss model `curieWeissMeasure n β h` (`SteinIntro.tex:3631-3637`,
`Formalization/Defs/Concentration.lean:42`) expressed as the measure associated with a
`ProbabilityMassFunction` on the finite configuration space `Fin n → Bool`
via `PMF.ofFintype` (`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:204`). -/
theorem curieWeissMeasure_eq_pmf_ofFintype (n : ℕ) (β h : ℝ)
    (hZ_pos : 0 < curieWeissPartition n β h) :
    curieWeissMeasure n β h =
      (PMF.ofFintype
        (fun x ↦ ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h))
        (by
          rw [← ENNReal.ofReal_sum_of_nonneg]
          · rw [← Finset.sum_div]
            have hZ : (∑ x : Fin n → Bool, curieWeissWeight n β h x) =
                curieWeissPartition n β h := rfl
            rw [hZ, div_self hZ_pos.ne', ENNReal.ofReal_one]
          · intro x _
            exact div_nonneg (Real.exp_pos _).le hZ_pos.le)).toMeasure := by
  rw [Measure.ext_iff_singleton]
  intro y
  rw [curieWeissMeasure, Measure.sum_apply _ (measurableSet_singleton y)]
  rw [(PMF.ofFintype _ _).toMeasure_apply_singleton y (measurableSet_singleton y)]
  rw [PMF.ofFintype_apply]
  have htsum : (∑' x : Fin n → Bool,
      (ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h) •
        Measure.dirac x) {y}) =
      ENNReal.ofReal (curieWeissWeight n β h y / curieWeissPartition n β h) := by
    rw [tsum_fintype]
    have hsingle : (∑ x : Fin n → Bool,
        (ENNReal.ofReal (curieWeissWeight n β h x / curieWeissPartition n β h) •
          Measure.dirac x) {y}) =
        (ENNReal.ofReal (curieWeissWeight n β h y / curieWeissPartition n β h) •
          Measure.dirac y) {y} := by
      refine Finset.sum_eq_single y (fun x _ hxy ↦ ?_) (fun hy ↦ (hy (Finset.mem_univ y)).elim)
      simp [hxy]
    rw [hsingle]
    simp
  exact htsum

/-! ### Binary Relative Entropy -/

/-- Equivalence between Ross's binary relative entropy `klDivBernoulli a p`
(`SteinIntro.tex:2071-2078`, `Formalization/Defs/PoissonDep.lean:61`) and Mathlib's
Kullback–Leibler divergence `InformationTheory.klDiv`
(`Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57`)
evaluated on `ProbabilityTheory.bernoulliMeasure true false`. -/
theorem klDivBernoulli_eq_klDiv (a p : ℝ) (ha : a ∈ Set.Icc 0 1) (hp : p ∈ Set.Ioo 0 1) :
    ENNReal.ofReal (klDivBernoulli a p) =
      InformationTheory.klDiv
        (ProbabilityTheory.bernoulliMeasure true false ⟨a, ha⟩)
        (ProbabilityTheory.bernoulliMeasure true false ⟨p, hp.1.le, hp.2.le⟩) := by
  set μ := ProbabilityTheory.bernoulliMeasure true false ⟨a, ha⟩
  set ν := ProbabilityTheory.bernoulliMeasure true false ⟨p, hp.1.le, hp.2.le⟩
  have hp0 : 0 < p := hp.1
  have hp1 : p < 1 := hp.2
  have h1mp_pos : 0 < 1 - p := by linarith
  have hν_true : ν {true} = ENNReal.ofReal p := by
    change (bernoulliMeasure true false ⟨p, hp.1.le, hp.2.le⟩) {true} = ENNReal.ofReal p
    rw [bernoulliMeasure_apply _ (measurableSet_singleton true)]
    simp only [Set.mem_singleton_iff, Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  have hν_false : ν {false} = ENNReal.ofReal (1 - p) := by
    change (bernoulliMeasure true false ⟨p, hp.1.le, hp.2.le⟩) {false} = ENNReal.ofReal (1 - p)
    rw [bernoulliMeasure_apply _ (measurableSet_singleton false)]
    simp only [Set.mem_singleton_iff, Bool.true_eq_false, ↓reduceIte]
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  have hν_true_ne_zero : ν {true} ≠ 0 := by
    rw [hν_true]
    exact (ENNReal.ofReal_pos.mpr hp0).ne'
  have hν_false_ne_zero : ν {false} ≠ 0 := by
    rw [hν_false]
    exact (ENNReal.ofReal_pos.mpr h1mp_pos).ne'
  have h_ac : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
    by_cases ht : true ∈ s <;> by_cases hf : false ∈ s
    · have h_univ : s = Set.univ := by
        ext b; cases b <;> simp [ht, hf]
      subst h_univ
      rw [measure_univ] at hs0; norm_num at hs0
    · have hs_eq : s = {true} := by
        ext b; cases b <;> simp [ht, hf]
      subst hs_eq; exact (hν_true_ne_zero hs0).elim
    · have hs_eq : s = {false} := by
        ext b; cases b <;> simp [ht, hf]
      subst hs_eq; exact (hν_false_ne_zero hs0).elim
    · have hs_eq : s = ∅ := by
        ext b; cases b <;> simp [ht, hf]
      subst hs_eq; simp
  have h_int : Integrable (llr μ ν) μ := by
    refine ⟨(measurable_llr μ ν).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ ↦ ENNReal.mul_lt_top enorm_lt_top (measure_lt_top μ _)
  rw [InformationTheory.klDiv_of_ac_of_integrable h_ac h_int]
  have hμ_univ : μ.real Set.univ = 1 := probReal_univ
  have hν_univ : ν.real Set.univ = 1 := probReal_univ
  rw [hμ_univ, hν_univ, add_sub_cancel_right]
  have hspec : μ = ν.withDensity (μ.rnDeriv ν) := by
    have hdec := μ.haveLebesgueDecomposition_add ν
    have hsing : μ.singularPart ν = 0 := Measure.singularPart_eq_zero_of_ac h_ac
    rwa [hsing, zero_add] at hdec
  have hμ_true : μ {true} = ENNReal.ofReal a := by
    change (bernoulliMeasure true false ⟨a, ha⟩) {true} = ENNReal.ofReal a
    rw [bernoulliMeasure_apply _ (measurableSet_singleton true)]
    simp only [Set.mem_singleton_iff, Bool.false_eq_true, ↓reduceIte]
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  have hμ_false : μ {false} = ENNReal.ofReal (1 - a) := by
    change (bernoulliMeasure true false ⟨a, ha⟩) {false} = ENNReal.ofReal (1 - a)
    rw [bernoulliMeasure_apply _ (measurableSet_singleton false)]
    simp only [Set.mem_singleton_iff, Bool.true_eq_false, ↓reduceIte]
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  have heq_t : ENNReal.ofReal a = μ.rnDeriv ν true * ENNReal.ofReal p := by
    have h1 : μ {true} = (ν.withDensity (μ.rnDeriv ν)) {true} := by rw [← hspec]
    rw [withDensity_apply _ (measurableSet_singleton true), lintegral_singleton, hμ_true,
      hν_true] at h1
    exact h1
  have heq_f : ENNReal.ofReal (1 - a) = μ.rnDeriv ν false * ENNReal.ofReal (1 - p) := by
    have h1 : μ {false} = (ν.withDensity (μ.rnDeriv ν)) {false} := by rw [← hspec]
    rw [withDensity_apply _ (measurableSet_singleton false), lintegral_singleton, hμ_false,
      hν_false] at h1
    exact h1
  have hrn_t : μ.rnDeriv ν true = ENNReal.ofReal (a / p) := by
    have hdiv : ENNReal.ofReal a / ENNReal.ofReal p = μ.rnDeriv ν true := by
      rw [heq_t, ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr hp0).ne'
        ENNReal.ofReal_ne_top]
    rw [← hdiv, ENNReal.ofReal_div_of_pos hp0]
  have hrn_f : μ.rnDeriv ν false = ENNReal.ofReal ((1 - a) / (1 - p)) := by
    have hdiv : ENNReal.ofReal (1 - a) / ENNReal.ofReal (1 - p) = μ.rnDeriv ν false := by
      rw [heq_f, ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr h1mp_pos).ne'
        ENNReal.ofReal_ne_top]
    rw [← hdiv, ENNReal.ofReal_div_of_pos h1mp_pos]
  have hllr_t : llr μ ν true = Real.log (a / p) := by
    dsimp [llr]; rw [hrn_t, ENNReal.toReal_ofReal (div_nonneg ha.1 hp0.le)]
  have hllr_f : llr μ ν false = Real.log ((1 - a) / (1 - p)) := by
    dsimp [llr]; rw [hrn_f, ENNReal.toReal_ofReal (div_nonneg (by linarith [ha.2]) h1mp_pos.le)]
  rw [integral_fintype h_int]
  have hsum_bool : (∑ x : Bool, μ.real {x} • llr μ ν x) =
      μ.real {true} * llr μ ν true + μ.real {false} * llr μ ν false := by
    rw [Fintype.sum_bool]; rfl
  rw [hsum_bool]
  have hμr_t : μ.real {true} = a := by
    rw [measureReal_def, hμ_true, ENNReal.toReal_ofReal ha.1]
  have hμr_f : μ.real {false} = 1 - a := by
    rw [measureReal_def, hμ_false, ENNReal.toReal_ofReal (by linarith [ha.2])]
  rw [hμr_t, hμr_f, hllr_t, hllr_f]
  by_cases ha1 : a = 1
  · subst ha1
    simp only [klDivBernoulli, ↓reduceIte, sub_self, zero_mul, add_zero, one_mul]
  · simp only [klDivBernoulli, ha1, ↓reduceIte]

end SteinMethod
