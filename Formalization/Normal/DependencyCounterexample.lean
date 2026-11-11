/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Sanity
import Formalization.Metrics.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

/-!
# Counterexample to Printed Theorem 3.5 (`Formalization.Normal.DependencyCounterexample`)

Machine-checks the counterexample documented in `ISSUE-3.5` showing that the literal printed
statement of Theorem 3.5 (`\label{thm41}`, eq. `(3.8)` `\label{41}`, `SteinIntro.tex:815-822`) in
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`), is false when stated under
singleton-to-complement dependency neighborhoods (`HasDependencyNeighborhoods`, Definition 3.1,
`SteinIntro.tex:805-809`) instead of set-to-set dependency graphs (`IsDependencyGraph`, used in
`Thm3_5_corrected`).

For any $m > 0$ and $n = 2m$, let $A_0, \dots, A_{m-1}, S$ be independent symmetric Rademacher
random variables ($\pm 1$ with probability $1/2$ each), and define
$X_{2r} = A_r$, $X_{2r+1} = S A_r$ with blocks $N_{2r} = N_{2r+1} = \{2r, 2r+1\}$ of size $D = 2$.
Each $X_i$ has mean $0$, $|X_i| \equiv 1$, and is independent of $(X_j)_{j \notin N_i}$
(`HasDependencyNeighborhoods`), while $\operatorname{Var}(\sum_{i=1}^n X_i) = 2m$. However,
$\sum_{i=1}^n X_i = (1 + S) \sum_{r=0}^{m-1} A_r$ vanishes with probability $1/2$, forcing
$\mathbb{E}|W| \le 1/\sqrt{2}$ whereas $\mathbb{E}|Z| = \sqrt{2/\pi}$ for $Z \sim \mathcal{N}(0,1)$.
At $m = 10000$ ($n = 20000$, $D = 2$), the printed $O(D^2 / \sqrt{n} + D^{3/2} / \sqrt{n})$ right
hand side falls strictly below $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{N}(0,1))$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace SteinMethod

section Counterexample

private lemma dc_bernoulliHalfMeasure_singleton (b : Bool) :
    bernoulliHalfMeasure {b} = ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [bernoulliHalfMeasure, Measure.coe_add, Pi.add_apply,
    Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply]
  cases b <;> simp

private lemma dc_integral_rademacherVal :
    ∫ b, rademacherVal b ∂bernoulliHalfMeasure = 0 := by
  have ht : Integrable rademacherVal ((1 / 2 : ℝ≥0) • Measure.dirac true) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  have hf : Integrable rademacherVal ((1 / 2 : ℝ≥0) • Measure.dirac false) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  rw [bernoulliHalfMeasure, integral_add_measure ht hf, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_dirac, integral_dirac, NNReal.smul_def,
    NNReal.smul_def, smul_eq_mul, smul_eq_mul, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  dsimp only [rademacherVal]
  norm_num

private lemma dc_abs_rademacherVal (b : Bool) : |rademacherVal b| = 1 := by
  cases b <;> norm_num [rademacherVal]

private lemma dc_sq_rademacherVal (b : Bool) : rademacherVal b ^ 2 = 1 := by
  cases b <;> norm_num [rademacherVal]

private abbrev dcSpace (m : ℕ) : Type := Fin (m + 1) → Bool

private noncomputable def dcMeas (m : ℕ) : Measure (dcSpace m) :=
  Measure.pi fun _ ↦ bernoulliHalfMeasure

private instance (m : ℕ) : IsProbabilityMeasure (dcMeas m) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : Fin (m + 1) ↦ bernoulliHalfMeasure))

private def dcR (m : ℕ) (k : Fin (m + 1)) (ω : dcSpace m) : ℝ :=
  rademacherVal (ω k)

private lemma dc_measurable_R (m : ℕ) (k : Fin (m + 1)) : Measurable (dcR m k) :=
  (Measurable.of_discrete : Measurable rademacherVal).comp (measurable_pi_apply k)

private lemma dc_iIndepFun_R (m : ℕ) : iIndepFun (dcR m) (dcMeas m) := by
  unfold dcMeas dcR
  exact iIndepFun_pi fun _ ↦ (Measurable.of_discrete : Measurable rademacherVal).aemeasurable

private lemma dc_integral_R (m : ℕ) (k : Fin (m + 1)) :
    ∫ ω, dcR m k ω ∂dcMeas m = 0 := by
  have hmp := measurePreserving_eval (fun _ : Fin (m + 1) ↦ bernoulliHalfMeasure) k
  have hm : AEStronglyMeasurable rademacherVal ((dcMeas m).map (Function.eval k)) := by
    rw [dcMeas, hmp.map_eq]
    exact (Measurable.of_discrete : Measurable rademacherVal).aestronglyMeasurable
  calc
    ∫ ω, dcR m k ω ∂dcMeas m
      = ∫ b, rademacherVal b ∂(dcMeas m).map (Function.eval k) :=
        (integral_map (measurable_pi_apply k).aemeasurable hm).symm
    _ = ∫ b, rademacherVal b ∂bernoulliHalfMeasure := by rw [dcMeas, hmp.map_eq]
    _ = 0 := dc_integral_rademacherVal

private def dcA (m : ℕ) (r : Fin m) (ω : dcSpace m) : ℝ :=
  dcR m r.castSucc ω

private def dcS (m : ℕ) (ω : dcSpace m) : ℝ :=
  dcR m (Fin.last m) ω

private def dcBlock {m : ℕ} (i : Fin (2 * m)) : Fin m :=
  ⟨i.1 / 2, by omega⟩

private def dcX (m : ℕ) (i : Fin (2 * m)) (ω : dcSpace m) : ℝ :=
  if i.1 % 2 = 0 then dcA m (dcBlock i) ω else dcS m ω * dcA m (dcBlock i) ω

private def dcN (m : ℕ) (i : Fin (2 * m)) : Finset (Fin (2 * m)) :=
  {⟨2 * (dcBlock i).1, by omega⟩, ⟨2 * (dcBlock i).1 + 1, by omega⟩}

private lemma dc_mem_N_iff {m : ℕ} (i j : Fin (2 * m)) :
    j ∈ dcN m i ↔ dcBlock j = dcBlock i := by
  simp only [dcN, dcBlock, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

private lemma dc_self_mem_N {m : ℕ} (i : Fin (2 * m)) : i ∈ dcN m i :=
  (dc_mem_N_iff i i).mpr rfl

private lemma dc_card_N {m : ℕ} (i : Fin (2 * m)) : (dcN m i).card = 2 := by
  refine Finset.card_pair fun h ↦ ?_
  have hv := congrArg Fin.val h
  dsimp only at hv
  omega

private lemma dc_sup_card_N {m : ℕ} (hm : 0 < m) :
    (Finset.univ.sup fun i : Fin (2 * m) ↦ (dcN m i).card) = 2 := by
  have hne : (Finset.univ : Finset (Fin (2 * m))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  simp_rw [dc_card_N]
  exact Finset.sup_const hne 2

private lemma dc_measurable_X (m : ℕ) (i : Fin (2 * m)) : Measurable (dcX m i) := by
  unfold dcX dcA dcS
  split_ifs
  · exact dc_measurable_R m (dcBlock i).castSucc
  · exact (dc_measurable_R m (Fin.last m)).mul (dc_measurable_R m (dcBlock i).castSucc)

private lemma dc_abs_X (m : ℕ) (i : Fin (2 * m)) (ω : dcSpace m) : |dcX m i ω| = 1 := by
  unfold dcX dcA dcS dcR
  split_ifs
  · exact dc_abs_rademacherVal _
  · rw [abs_mul, dc_abs_rademacherVal, dc_abs_rademacherVal, one_mul]

private lemma dc_sq_X (m : ℕ) (i : Fin (2 * m)) (ω : dcSpace m) : dcX m i ω ^ 2 = 1 := by
  rw [← sq_abs, dc_abs_X, one_pow]

private lemma dc_pow_four_X (m : ℕ) (i : Fin (2 * m)) (ω : dcSpace m) : dcX m i ω ^ 4 = 1 := by
  calc
    dcX m i ω ^ 4 = (dcX m i ω ^ 2) ^ 2 := by ring
    _ = 1 := by rw [dc_sq_X, one_pow]

private lemma dc_memLp_X (m : ℕ) (i : Fin (2 * m)) (p : ℝ≥0∞) :
    MemLp (dcX m i) p (dcMeas m) := by
  refine MemLp.of_bound (dc_measurable_X m i).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_eq_abs, dc_abs_X]

private lemma dc_integral_X (m : ℕ) (i : Fin (2 * m)) :
    ∫ ω, dcX m i ω ∂dcMeas m = 0 := by
  unfold dcX dcA dcS
  split_ifs
  · exact dc_integral_R m (dcBlock i).castSucc
  · have hne : Fin.last m ≠ (dcBlock i).castSucc := (Fin.castSucc_ne_last (dcBlock i)).symm
    have hind : dcR m (Fin.last m) ⟂ᵢ[dcMeas m] dcR m (dcBlock i).castSucc :=
      (dc_iIndepFun_R m).indepFun hne
    rw [hind.integral_fun_mul_eq_mul_integral
      (dc_measurable_R m _).aestronglyMeasurable (dc_measurable_R m _).aestronglyMeasurable]
    change (∫ ω, dcR m (Fin.last m) ω ∂dcMeas m) *
      (∫ ω, dcR m (dcBlock i).castSucc ω ∂dcMeas m) = 0
    rw [dc_integral_R, zero_mul]

private lemma dc_sum_abs_cube (m : ℕ) :
    (∑ i : Fin (2 * m), ∫ ω, |dcX m i ω| ^ 3 ∂dcMeas m) = 2 * (m : ℝ) := by
  have h1 (i : Fin (2 * m)) : ∫ ω, |dcX m i ω| ^ 3 ∂dcMeas m = 1 := by
    simp_rw [dc_abs_X, one_pow, integral_const, probReal_univ, one_smul]
  simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_mul, Nat.cast_ofNat]

private lemma dc_sum_pow_four (m : ℕ) :
    (∑ i : Fin (2 * m), ∫ ω, dcX m i ω ^ 4 ∂dcMeas m) = 2 * (m : ℝ) := by
  have h1 (i : Fin (2 * m)) : ∫ ω, dcX m i ω ^ 4 ∂dcMeas m = 1 := by
    simp_rw [dc_pow_four_X, integral_const, probReal_univ, one_smul]
  simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_mul, Nat.cast_ofNat]

private def dcTau (m : ℕ) (r : Fin m) (ω : dcSpace m) : dcSpace m :=
  Function.update ω r.castSucc (if ω (Fin.last m) then ω r.castSucc else !ω r.castSucc)

private lemma dc_measurable_tau (m : ℕ) (r : Fin m) : Measurable (dcTau m r) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k = r.castSucc
  · subst hk
    have heq : (fun ω : dcSpace m ↦ dcTau m r ω r.castSucc) =
        (fun p : Bool × Bool ↦ if p.2 then p.1 else !p.1) ∘
          fun ω ↦ (ω r.castSucc, ω (Fin.last m)) := by
      ext ω
      simp only [dcTau, Function.comp_apply, Function.update_self]
    rw [heq]
    exact Measurable.of_discrete.comp
      ((measurable_pi_apply r.castSucc).prodMk (measurable_pi_apply (Fin.last m)))
  · have heq : (fun ω : dcSpace m ↦ dcTau m r ω k) = fun ω ↦ ω k := by
      ext ω
      simp only [dcTau, Function.update_of_ne hk]
    rw [heq]
    exact measurable_pi_apply k

private lemma dc_tau_involutive (m : ℕ) (r : Fin m) (ω : dcSpace m) :
    dcTau m r (dcTau m r ω) = ω := by
  ext k
  by_cases hk : k = r.castSucc
  · subst hk
    simp only [dcTau, Function.update_self, Function.update_of_ne (Fin.castSucc_ne_last r).symm]
    cases ω (Fin.last m) <;> cases ω r.castSucc <;> rfl
  · simp only [dcTau, Function.update_of_ne hk]

private lemma dc_map_tau (m : ℕ) (r : Fin m) :
    (dcMeas m).map (dcTau m r) = dcMeas m := by
  refine Measure.ext_of_singleton fun ω ↦ ?_
  have hpre : dcTau m r ⁻¹' {ω} = {dcTau m r ω} := by
    ext ω'
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ by rw [← h, dc_tau_involutive], fun h ↦ by rw [h, dc_tau_involutive]⟩
  rw [Measure.map_apply (dc_measurable_tau m r) (measurableSet_singleton ω), hpre,
    dcMeas, Measure.pi_singleton, Measure.pi_singleton]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [dc_bernoulliHalfMeasure_singleton, dc_bernoulliHalfMeasure_singleton]

private lemma dc_indepFun_of_comp_map_eq {Ω β β' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace β']
    {μ : Measure Ω} {τ : Ω → Ω} {f : Ω → β} {g : Ω → β'}
    (hτ : Measurable τ) (hmap : μ.map τ = μ) (hf : Measurable f) (hg : Measurable g)
    (hind : (f ∘ τ) ⟂ᵢ[μ] (g ∘ τ)) :
    f ⟂ᵢ[μ] g := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have h1 : μ (f ⁻¹' s) = μ ((f ∘ τ) ⁻¹' s) :=
    calc
      μ (f ⁻¹' s) = (μ.map τ) (f ⁻¹' s) := by rw [hmap]
      _ = μ ((f ∘ τ) ⁻¹' s) := Measure.map_apply hτ (hf hs)
  have h2 : μ (g ⁻¹' t) = μ ((g ∘ τ) ⁻¹' t) :=
    calc
      μ (g ⁻¹' t) = (μ.map τ) (g ⁻¹' t) := by rw [hmap]
      _ = μ ((g ∘ τ) ⁻¹' t) := Measure.map_apply hτ (hg ht)
  have h3 : μ (f ⁻¹' s ∩ g ⁻¹' t) = μ ((f ∘ τ) ⁻¹' s ∩ (g ∘ τ) ⁻¹' t) :=
    calc
      μ (f ⁻¹' s ∩ g ⁻¹' t) = (μ.map τ) (f ⁻¹' s ∩ g ⁻¹' t) := by rw [hmap]
      _ = μ (τ ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t)) := Measure.map_apply hτ ((hf hs).inter (hg ht))
      _ = μ ((f ∘ τ) ⁻¹' s ∩ (g ∘ τ) ⁻¹' t) := rfl
  rw [h3, h1, h2]
  exact hind.measure_inter_preimage_eq_mul s t hs ht

private lemma dc_indepFun_A_outside (m : ℕ) (i : Fin (2 * m)) :
    dcA m (dcBlock i) ⟂ᵢ[dcMeas m]
      (fun ω (j : {j : Fin (2 * m) // j ∉ dcN m i}) ↦ dcX m j.1 ω) := by
  let r : Fin m := dcBlock i
  let S : Finset (Fin (m + 1)) := {r.castSucc}
  let T : Finset (Fin (m + 1)) := Finset.univ.erase r.castSucc
  have hST : Disjoint S T := Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _)
  have hbase := iIndepFun.indepFun_finset S T hST (dc_iIndepFun_R m) (dc_measurable_R m)
  have hlast : Fin.last m ∈ T :=
    Finset.mem_erase.mpr ⟨(Fin.castSucc_ne_last r).symm, Finset.mem_univ _⟩
  have hj (j : {j : Fin (2 * m) // j ∉ dcN m i}) : (dcBlock j.1).castSucc ∈ T := by
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro heq
    exact j.2 ((dc_mem_N_iff i j.1).mpr (Fin.castSucc_injective m heq))
  let φ : (S → ℝ) → ℝ := fun u ↦ u ⟨r.castSucc, Finset.mem_singleton_self _⟩
  let ψ : (T → ℝ) → ({j : Fin (2 * m) // j ∉ dcN m i} → ℝ) := fun v j ↦
    if j.1.1 % 2 = 0 then v ⟨(dcBlock j.1).castSucc, hj j⟩
    else v ⟨Fin.last m, hlast⟩ * v ⟨(dcBlock j.1).castSucc, hj j⟩
  have hφ : Measurable φ := measurable_pi_apply _
  have hψ : Measurable ψ := by
    rw [measurable_pi_iff]
    intro j
    dsimp only [ψ]
    split_ifs
    · exact measurable_pi_apply _
    · exact (measurable_pi_apply _).mul (measurable_pi_apply _)
  exact hbase.comp hφ hψ

private lemma dc_hasDependencyNeighborhoods (m : ℕ) :
    HasDependencyNeighborhoods (dcMeas m) (dcX m) (dcN m) := by
  intro i
  by_cases hi : i.1 % 2 = 0
  · have hXi : dcX m i = dcA m (dcBlock i) := funext fun ω ↦ ite_eq_left hi
    rw [hXi]
    exact dc_indepFun_A_outside m i
  · let r : Fin m := dcBlock i
    let g : dcSpace m → ({j : Fin (2 * m) // j ∉ dcN m i} → ℝ) := fun ω j ↦ dcX m j.1 ω
    have hg : Measurable g := measurable_pi_iff.mpr fun j ↦ dc_measurable_X m j.1
    have hcomp_f : dcX m i ∘ dcTau m r = dcA m r := by
      ext ω
      simp only [r, Function.comp_apply, dcX, ite_eq_right hi, dcS, dcA, dcR, dcTau,
        Function.update_self, Function.update_of_ne (Fin.castSucc_ne_last (dcBlock i)).symm]
      cases ω (Fin.last m) <;> cases ω (dcBlock i).castSucc <;> norm_num [rademacherVal]
    have hcomp_g : g ∘ dcTau m r = g := by
      ext ω j
      have hne : (dcBlock j.1).castSucc ≠ (dcBlock i).castSucc := fun heq ↦
        j.2 ((dc_mem_N_iff i j.1).mpr (Fin.castSucc_injective m heq))
      simp only [g, r, Function.comp_apply, dcX, dcS, dcA, dcR, dcTau,
        Function.update_of_ne hne, Function.update_of_ne (Fin.castSucc_ne_last (dcBlock i)).symm]
    refine dc_indepFun_of_comp_map_eq (dc_measurable_tau m r) (dc_map_tau m r)
      (dc_measurable_X m i) hg ?_
    rw [hcomp_f, hcomp_g]
    exact dc_indepFun_A_outside m i

private lemma dc_variance_sum_X (m : ℕ) :
    variance (fun ω ↦ ∑ i : Fin (2 * m), dcX m i ω) (dcMeas m) = 2 * (m : ℝ) := by
  rw [variance_fun_sum fun i ↦ dc_memLp_X m i 2]
  have hrow (i : Fin (2 * m)) :
      (∑ j : Fin (2 * m), covariance (dcX m i) (dcX m j) (dcMeas m)) = 1 := by
    rw [Finset.sum_eq_single i]
    · rw [covariance_self (dc_measurable_X m i).aemeasurable,
        variance_of_integral_eq_zero (dc_measurable_X m i).aemeasurable (dc_integral_X m i)]
      simp_rw [dc_sq_X, integral_const, probReal_univ, one_smul]
    · intro j _ hji
      by_cases hjN : j ∈ dcN m i
      · have hblk : dcBlock j = dcBlock i := (dc_mem_N_iff i j).mp hjN
        have hpar : (i.1 % 2 = 0 ∧ j.1 % 2 ≠ 0) ∨ (i.1 % 2 ≠ 0 ∧ j.1 % 2 = 0) := by
          have hij_val : j.1 ≠ i.1 := fun h ↦ hji (Fin.ext h)
          have hdiv : j.1 / 2 = i.1 / 2 := congrArg Fin.val hblk
          omega
        have hmul : dcX m i * dcX m j = dcS m := by
          ext ω
          simp only [Pi.mul_apply, dcX, hblk]
          rcases hpar with ⟨hi0, hj0⟩ | ⟨hi0, hj0⟩
          · rw [ite_eq_left hi0, ite_eq_right hj0]
            calc
              dcA m (dcBlock i) ω * (dcS m ω * dcA m (dcBlock i) ω)
                = dcS m ω * (dcA m (dcBlock i) ω ^ 2) := by ring
              _ = dcS m ω := by rw [dcA, dcR, dc_sq_rademacherVal, mul_one]
          · rw [ite_eq_right hi0, ite_eq_left hj0]
            calc
              (dcS m ω * dcA m (dcBlock i) ω) * dcA m (dcBlock i) ω
                = dcS m ω * (dcA m (dcBlock i) ω ^ 2) := by ring
              _ = dcS m ω := by rw [dcA, dcR, dc_sq_rademacherVal, mul_one]
        rw [covariance_eq_sub (dc_memLp_X m i 2) (dc_memLp_X m j 2), hmul]
        change (∫ ω, dcR m (Fin.last m) ω ∂dcMeas m) -
          (∫ ω, dcX m i ω ∂dcMeas m) * (∫ ω, dcX m j ω ∂dcMeas m) = 0
        rw [dc_integral_R, dc_integral_X, dc_integral_X, mul_zero, sub_zero]
      · have hind : dcX m i ⟂ᵢ[dcMeas m] dcX m j :=
          (dc_hasDependencyNeighborhoods m i).comp measurable_id
            (measurable_pi_apply (⟨j, hjN⟩ : {k : Fin (2 * m) // k ∉ dcN m i}))
        exact hind.covariance_eq_zero (dc_memLp_X m i 2) (dc_memLp_X m j 2)
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Nat.cast_mul, Nat.cast_ofNat]

private def dcPairEquiv (m : ℕ) : Fin m × Bool ≃ Fin (2 * m) where
  toFun p := ⟨2 * p.1.1 + _root_.cond p.2 0 1, by
    rcases p with ⟨⟨r, hr⟩, _ | _⟩ <;> dsimp only [_root_.cond] <;> omega⟩
  invFun i := (⟨i.1 / 2, by omega⟩, decide (i.1 % 2 = 0))
  left_inv := by
    rintro ⟨⟨r, hr⟩, _ | _⟩ <;> ext <;> dsimp only [_root_.cond]
    · omega
    · exact decide_eq_false (by omega)
    · omega
    · exact decide_eq_true (by omega)
  right_inv := by
    rintro ⟨i, hi⟩
    ext
    dsimp only
    by_cases h : i % 2 = 0
    · rw [decide_eq_true h]; dsimp only [_root_.cond]; omega
    · rw [decide_eq_false h]; dsimp only [_root_.cond]; omega

private lemma dc_sum_X_eq (m : ℕ) (ω : dcSpace m) :
    (∑ i : Fin (2 * m), dcX m i ω) = (1 + dcS m ω) * ∑ r : Fin m, dcA m r ω := by
  rw [← (dcPairEquiv m).sum_comp (fun i ↦ dcX m i ω), Fintype.sum_prod_type]
  have hinner (r : Fin m) :
      (∑ b : Bool, dcX m (dcPairEquiv m (r, b)) ω) = (1 + dcS m ω) * dcA m r ω := by
    rw [Fintype.sum_bool]
    have ht : dcX m (dcPairEquiv m (r, true)) ω = dcA m r ω := by
      have hdiv : dcBlock (dcPairEquiv m (r, true)) = r := by
        ext; change (2 * r.1 + 0) / 2 = r.1; omega
      have hmod : (dcPairEquiv m (r, true)).1 % 2 = 0 := by
        change (2 * r.1 + 0) % 2 = 0; omega
      rw [dcX, ite_eq_left hmod, hdiv]
    have hf : dcX m (dcPairEquiv m (r, false)) ω = dcS m ω * dcA m r ω := by
      have hdiv : dcBlock (dcPairEquiv m (r, false)) = r := by
        ext; change (2 * r.1 + 1) / 2 = r.1; omega
      have hmod : (dcPairEquiv m (r, false)).1 % 2 ≠ 0 := by
        change (2 * r.1 + 1) % 2 ≠ 0; omega
      rw [dcX, ite_eq_right hmod, hdiv]
    rw [ht, hf]; ring
  simp_rw [hinner, ← Finset.mul_sum]

private lemma dc_nonneg_one_add_S (m : ℕ) (ω : dcSpace m) : 0 ≤ 1 + dcS m ω := by
  unfold dcS dcR
  cases ω (Fin.last m) <;> norm_num [rademacherVal]

private lemma dc_indepFun_S_sum_A (m : ℕ) :
    (fun ω ↦ 1 + dcS m ω) ⟂ᵢ[dcMeas m] (fun ω ↦ |∑ r : Fin m, dcA m r ω|) := by
  let S : Finset (Fin (m + 1)) := {Fin.last m}
  let T : Finset (Fin (m + 1)) := Finset.univ.erase (Fin.last m)
  have hST : Disjoint S T := Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _)
  have hbase := iIndepFun.indepFun_finset S T hST (dc_iIndepFun_R m) (dc_measurable_R m)
  have hr (r : Fin m) : r.castSucc ∈ T :=
    Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last r, Finset.mem_univ _⟩
  let φ : (S → ℝ) → ℝ := fun u ↦ 1 + u ⟨Fin.last m, Finset.mem_singleton_self _⟩
  let ψ : (T → ℝ) → ℝ := fun v ↦ |∑ r : Fin m, v ⟨r.castSucc, hr r⟩|
  have hφ : Measurable φ := measurable_const.add (measurable_pi_apply _)
  have hψ : Measurable ψ := by
    refine continuous_abs.measurable.comp ?_
    exact Finset.measurable_sum Finset.univ fun r _ ↦
      @measurable_pi_apply T (fun _ ↦ ℝ) _ ⟨r.castSucc, hr r⟩
  exact hbase.comp hφ hψ

private lemma dc_integral_abs_sum_A_le (m : ℕ) :
    (∫ ω, |∑ r : Fin m, dcA m r ω| ∂dcMeas m) ≤ √(m : ℝ) := by
  let Y : dcSpace m → ℝ := fun ω ↦ ∑ r : Fin m, dcA m r ω
  have hA_meas (r : Fin m) : Measurable (dcA m r) := dc_measurable_R m r.castSucc
  have hA_lp (r : Fin m) : MemLp (dcA m r) 2 (dcMeas m) := by
    refine MemLp.of_bound (hA_meas r).aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, dcA, dcR, dc_abs_rademacherVal]
  have hY_lp : MemLp Y 2 (dcMeas m) := memLp_finsetSum Finset.univ fun r _ ↦ hA_lp r
  have habs_lp : MemLp (fun ω ↦ |Y ω|) 2 (dcMeas m) := by
    simpa only [Real.norm_eq_abs] using hY_lp.norm
  have hY_mean : ∫ ω, Y ω ∂dcMeas m = 0 := by
    rw [integral_finsetSum Finset.univ fun r _ ↦ (hA_lp r).integrable one_le_two]
    exact Finset.sum_eq_zero fun r _ ↦ dc_integral_R m r.castSucc
  have hY_sq : ∫ ω, Y ω ^ 2 ∂dcMeas m = (m : ℝ) := by
    rw [← variance_of_integral_eq_zero hY_lp.aemeasurable hY_mean, variance_fun_sum hA_lp]
    have hrow (r : Fin m) :
        (∑ s : Fin m, covariance (dcA m r) (dcA m s) (dcMeas m)) = 1 := by
      rw [Finset.sum_eq_single r]
      · rw [covariance_self (hA_meas r).aemeasurable,
          variance_of_integral_eq_zero (hA_meas r).aemeasurable (dc_integral_R m r.castSucc)]
        simp_rw [dcA, dcR, dc_sq_rademacherVal, integral_const, probReal_univ, one_smul]
      · intro s _ hsr
        have hne : r.castSucc ≠ s.castSucc := fun h ↦ hsr (Fin.castSucc_injective m h).symm
        exact ((dc_iIndepFun_R m).indepFun hne).covariance_eq_zero (hA_lp r) (hA_lp s)
      · intro hr_mem
        exact False.elim (hr_mem (Finset.mem_univ r))
    simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hvar_nn : 0 ≤ variance (fun ω ↦ |Y ω|) (dcMeas m) := variance_nonneg _ _
  rw [variance_eq_sub habs_lp] at hvar_nn
  have habs_sq : (dcMeas m)[(fun ω ↦ |Y ω|) ^ 2] = (m : ℝ) := by
    change ∫ ω, |Y ω| ^ 2 ∂dcMeas m = (m : ℝ)
    simp_rw [sq_abs]
    exact hY_sq
  rw [habs_sq] at hvar_nn
  have hsq_le : (∫ ω, |Y ω| ∂dcMeas m) ^ 2 ≤ (m : ℝ) := by
    change (dcMeas m)[fun ω ↦ |Y ω|] ^ 2 ≤ (m : ℝ)
    linarith
  exact Real.le_sqrt_of_sq_le hsq_le

private lemma dc_integral_abs_sum_X_le (m : ℕ) :
    (∫ ω, |∑ i : Fin (2 * m), dcX m i ω| ∂dcMeas m) ≤ √(m : ℝ) := by
  have hcongr (ω : dcSpace m) :
      |∑ i : Fin (2 * m), dcX m i ω| =
        (1 + dcS m ω) * |∑ r : Fin m, dcA m r ω| := by
    rw [dc_sum_X_eq, abs_mul, abs_of_nonneg (dc_nonneg_one_add_S m ω)]
  simp_rw [hcongr]
  have hm1 : AEStronglyMeasurable (fun ω ↦ 1 + dcS m ω) (dcMeas m) :=
    (measurable_const.add (dc_measurable_R m (Fin.last m))).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun ω ↦ |∑ r : Fin m, dcA m r ω|) (dcMeas m) :=
    (continuous_abs.measurable.comp
      (Finset.measurable_sum Finset.univ fun r _ ↦
        dc_measurable_R m r.castSucc)).aestronglyMeasurable
  rw [(dc_indepFun_S_sum_A m).integral_fun_mul_eq_mul_integral hm1 hm2]
  have hS_int : Integrable (dcS m) (dcMeas m) := by
    refine (MemLp.of_bound (dc_measurable_R m (Fin.last m)).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ ?_)).integrable le_rfl
    rw [Real.norm_eq_abs, dcR, dc_abs_rademacherVal]
  have hmean1 : (dcMeas m)[fun ω ↦ 1 + dcS m ω] = 1 := by
    change ∫ ω, (1 + dcS m ω) ∂dcMeas m = 1
    rw [integral_add (integrable_const 1) hS_int, integral_const, probReal_univ, one_smul]
    dsimp only [dcS]
    rw [dc_integral_R, add_zero]
  rw [hmean1, one_mul]
  exact dc_integral_abs_sum_A_le m

private lemma dc_integral_abs_W_le {m : ℕ} (hm : 0 < m) :
    let σ : ℝ := √(variance (fun ω ↦ ∑ i : Fin (2 * m), dcX m i ω) (dcMeas m))
    (∫ ω, |(∑ i : Fin (2 * m), dcX m i ω) / σ| ∂dcMeas m) ≤ 1 / √(2 : ℝ) := by
  intro σ
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hσ_eq : σ = √(2 * (m : ℝ)) := by
    dsimp only [σ]
    rw [dc_variance_sum_X]
  have hσ_pos : 0 < σ := by
    rw [hσ_eq]
    exact Real.sqrt_pos.mpr (mul_pos zero_lt_two hm_pos)
  have hrew (ω : dcSpace m) :
      |(∑ i : Fin (2 * m), dcX m i ω) / σ| = |∑ i : Fin (2 * m), dcX m i ω| * σ⁻¹ := by
    rw [abs_div, abs_of_pos hσ_pos, div_eq_mul_inv]
  simp_rw [hrew, integral_mul_const]
  calc
    (∫ ω, |∑ i : Fin (2 * m), dcX m i ω| ∂dcMeas m) * σ⁻¹
      ≤ √(m : ℝ) * σ⁻¹ :=
        mul_le_mul_of_nonneg_right (dc_integral_abs_sum_X_le m) (inv_nonneg.mpr hσ_pos.le)
    _ = √(m : ℝ) / (√(m : ℝ) * √(2 : ℝ)) := by
        rw [hσ_eq, Real.sqrt_mul zero_le_two, mul_comm √(2 : ℝ), ← div_eq_mul_inv]
    _ = 1 / √(2 : ℝ) := by
        rw [div_mul_eq_div_div, div_self (Real.sqrt_pos.mpr hm_pos).ne']

private lemma dc_hasDerivAt_neg_pdf (w : ℝ) :
    HasDerivAt (fun x ↦ -gaussianPDFReal 0 1 x) (w * gaussianPDFReal 0 1 w) w := by
  have h_inner : HasDerivAt (fun x : ℝ ↦ -(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) (-w) w := by
    have h0 : (fun x : ℝ ↦ -(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) = fun x : ℝ ↦ -(x ^ 2) / 2 := by
      ext x
      simp only [sub_zero, NNReal.coe_one, mul_one]
    rw [h0]
    convert (((hasDerivAt_id' w).fun_pow 2).neg.div_const (2 : ℝ)) using 1
    ring
  have h_exp : HasDerivAt
      (fun x : ℝ ↦ Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0))))
      (Real.exp (-(w - 0) ^ 2 / (2 * (1 : ℝ≥0))) * (-w)) w :=
    h_inner.exp
  have h_pdf : HasDerivAt (gaussianPDFReal 0 1) (-w * gaussianPDFReal 0 1 w) w := by
    rw [gaussianPDFReal_def]
    convert h_exp.const_mul (√(2 * Real.pi * (1 : ℝ≥0)))⁻¹ using 1
    ring
  convert h_pdf.neg using 1
  ring

private lemma dc_tendsto_neg_pdf_of_sq {l : Filter ℝ}
    (hsq : Tendsto (fun x : ℝ ↦ x ^ 2) l atTop) :
    Tendsto (fun x ↦ -gaussianPDFReal 0 1 x) l (𝓝 0) := by
  have hdiv : Tendsto (fun x : ℝ ↦ x ^ 2 / 2) l atTop :=
    hsq.atTop_div_const (by norm_num)
  have hneg : Tendsto (fun x : ℝ ↦ -(x - 0) ^ 2 / (2 * (1 : ℝ≥0))) l atBot := by
    have h' : Tendsto (fun x : ℝ ↦ -(x ^ 2 / 2)) l atBot :=
      tendsto_neg_atTop_atBot.comp hdiv
    refine h'.congr fun x ↦ ?_
    simp only [sub_zero, NNReal.coe_one, mul_one, neg_div]
  have hexp : Tendsto (fun x : ℝ ↦ Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ≥0)))) l (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hpdf : Tendsto (gaussianPDFReal 0 1) l (𝓝 0) := by
    rw [gaussianPDFReal_def]
    simpa using hexp.const_mul (√(2 * Real.pi * (1 : ℝ≥0)))⁻¹
  simpa using hpdf.neg

private lemma dc_integrable_mul_pdf :
    Integrable (fun w ↦ w * gaussianPDFReal 0 1 w) volume := by
  have hid : Integrable (fun w : ℝ ↦ w) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := 1) 1)
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at hid
  simpa only [toReal_gaussianPDF] using hid

private lemma dc_integrable_abs_gaussian :
    Integrable (fun x : ℝ ↦ |x|) (gaussianReal 0 1) := by
  have hid : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.mp (memLp_id_gaussianReal (μ := 0) (v := 1) 1)
  simpa only [Real.norm_eq_abs] using hid.norm

private lemma dc_integral_abs_stdNormal :
    ∫ x, |x| ∂stdNormalLaw = √(2 / Real.pi) := by
  have habs_std : Integrable (fun x : ℝ ↦ |x|) (gaussianReal 0 1) := dc_integrable_abs_gaussian
  have habs_pdf : Integrable (fun x : ℝ ↦ |x| * gaussianPDFReal 0 1 x) volume := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)] at habs_std
    simpa only [toReal_gaussianPDF] using habs_std
  have hdens : ∫ x, |x| ∂stdNormalLaw = ∫ x, |x| * gaussianPDFReal 0 1 x := by
    rw [stdNormalLaw, integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp_rw [smul_eq_mul, mul_comm]
  have hIoi : ∫ w in Set.Ioi (0 : ℝ), w * gaussianPDFReal 0 1 w = gaussianPDFReal 0 1 0 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
      (fun w _ ↦ dc_hasDerivAt_neg_pdf w)
      dc_integrable_mul_pdf.integrableOn
      (dc_tendsto_neg_pdf_of_sq (tendsto_pow_atTop (by norm_num)))
    simpa using h
  have hIic : ∫ w in Set.Iic (0 : ℝ), w * gaussianPDFReal 0 1 w = -gaussianPDFReal 0 1 0 := by
    have hbot : Tendsto (fun x : ℝ ↦ x ^ 2) atBot atTop := by
      have h : Tendsto (fun x : ℝ ↦ (-x) ^ 2) atBot atTop :=
        (tendsto_pow_atTop (by norm_num)).comp tendsto_neg_atBot_atTop
      simpa using h
    have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
      (fun w _ ↦ dc_hasDerivAt_neg_pdf w)
      dc_integrable_mul_pdf.integrableOn
      (dc_tendsto_neg_pdf_of_sq hbot)
    simpa using h
  have hpos : ∫ x in Set.Ioi (0 : ℝ), |x| * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by rw [abs_of_pos hx], hIoi]
  have hneg : ∫ x in Set.Iic (0 : ℝ), |x| * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 0 := by
    rw [setIntegral_congr_fun measurableSet_Iic fun x hx ↦ by rw [abs_of_nonpos hx, neg_mul],
      integral_neg, hIic, neg_neg]
  have hpdf0 : gaussianPDFReal 0 1 0 = (√(2 * Real.pi))⁻¹ := by
    simp [gaussianPDFReal_def]
  rw [hdens, ← integral_add_compl measurableSet_Iic habs_pdf, Set.compl_Iic, hneg, hpos, hpdf0]
  calc
    (√(2 * Real.pi))⁻¹ + (√(2 * Real.pi))⁻¹
      = 2 / (√(2 : ℝ) * √Real.pi) := by
          rw [← two_mul, Real.sqrt_mul zero_le_two, ← div_eq_mul_inv]
    _ = (2 / √(2 : ℝ)) / √Real.pi := by rw [div_mul_eq_div_div]
    _ = √(2 : ℝ) / √Real.pi := by rw [Real.div_sqrt]
    _ = √(2 / Real.pi) := (Real.sqrt_div zero_le_two Real.pi).symm

private lemma dc_wasserstein_ge {m : ℕ} (hm : 0 < m) :
    let σ : ℝ := √(variance (fun ω ↦ ∑ i : Fin (2 * m), dcX m i ω) (dcMeas m))
    let W : dcSpace m → ℝ := fun ω ↦ (∑ i : Fin (2 * m), dcX m i ω) / σ
    ENNReal.ofReal (√(2 / Real.pi) - 1 / √(2 : ℝ)) ≤
      wassersteinDist ((dcMeas m).map W) (stdNormalLaw.map id) := by
  intro σ W
  have hlip : LipschitzWith 1 (fun x : ℝ ↦ |x|) :=
    LipschitzWith.of_le_add fun x y ↦ by
      rw [Real.dist_eq]
      rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
        rcases le_total 0 (x - y) with hxy | hxy <;>
        simp only [abs_of_nonneg, abs_of_nonpos, *] <;> linarith
  have hW_meas : Measurable W :=
    (Finset.measurable_sum Finset.univ fun i _ ↦ dc_measurable_X m i).div measurable_const
  have hSum_int : Integrable (fun ω ↦ ∑ i : Fin (2 * m), dcX m i ω) (dcMeas m) :=
    memLp_one_iff_integrable.mp (memLp_finsetSum Finset.univ fun i _ ↦ dc_memLp_X m i 1)
  have hW_abs_int : Integrable (fun ω ↦ |W ω|) (dcMeas m) := by
    simpa only [W, Real.norm_eq_abs, div_eq_mul_inv] using (hSum_int.mul_const σ⁻¹).norm
  have hIntW : Integrable (fun x : ℝ ↦ |x|) ((dcMeas m).map W) :=
    (integrable_map_measure continuous_abs.measurable.aestronglyMeasurable
      hW_meas.aemeasurable).mpr hW_abs_int
  have hIntZ : Integrable (fun x : ℝ ↦ |x|) stdNormalLaw := dc_integrable_abs_gaussian
  have hipm := le_ipm (H := {h : ℝ → ℝ | LipschitzWith 1 h}) hlip hIntW hIntZ
  have hmapW : ∫ x, |x| ∂(dcMeas m).map W = ∫ ω, |W ω| ∂dcMeas m :=
    integral_map hW_meas.aemeasurable continuous_abs.measurable.aestronglyMeasurable
  have hdiff : √(2 / Real.pi) - 1 / √(2 : ℝ) ≤
      |(∫ x, |x| ∂(dcMeas m).map W) - (∫ x, |x| ∂stdNormalLaw)| := by
    rw [hmapW, dc_integral_abs_stdNormal, abs_sub_comm]
    exact le_trans (sub_le_sub_left (dc_integral_abs_W_le hm) _) (le_abs_self _)
  rw [Measure.map_id]
  exact le_trans (ENNReal.ofReal_le_ofReal hdiff) hipm

private lemma dc_rhs_lower_bound :
    (88 / 1000 : ℝ) < √(2 / Real.pi) - 1 / √(2 : ℝ) := by
  have hs2_pos : (0 : ℝ) < √(2 : ℝ) := Real.sqrt_pos.mpr zero_lt_two
  have h_inv_s2 : 1 / √(2 : ℝ) < 708 / 1000 := by
    rw [div_lt_iff₀ hs2_pos]
    have hlt : (1000 / 708 : ℝ) < √(2 : ℝ) :=
      (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have hmul := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 708 / 1000)
    linarith
  have h_sqrt_pi : (796 / 1000 : ℝ) < √(2 / Real.pi) := by
    refine (Real.lt_sqrt (by norm_num)).mpr ((lt_div_iff₀ Real.pi_pos).mpr ?_)
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hmul := mul_lt_mul_of_pos_left hpi (by norm_num : (0 : ℝ) < (796 / 1000) ^ 2)
    linarith
  linarith

private lemma dc_numerical_ineq :
    (2 : ℝ) ^ 2 / (√(20000 : ℝ)) ^ 3 * (20000 : ℝ) +
      √(26 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) / (√Real.pi * (√(20000 : ℝ)) ^ 2) * √(20000 : ℝ) <
      √(2 / Real.pi) - 1 / √(2 : ℝ) := by
  have hs2_pos : (0 : ℝ) < √(2 : ℝ) := Real.sqrt_pos.mpr zero_lt_two
  have hs2_sq : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt zero_le_two
  have hsq20000 : (√(20000 : ℝ)) ^ 2 = 20000 := Real.sq_sqrt (by norm_num)
  have hsqrt20000 : √(20000 : ℝ) = 100 * √(2 : ℝ) := by
    have h20000 : (20000 : ℝ) = 100 ^ 2 * 2 := by norm_num
    rw [h20000, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 100 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)]
  have hrpow : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * √(2 : ℝ) := by
    have h32 : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [h32, Real.rpow_add zero_lt_two, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hT1 : (2 : ℝ) ^ 2 / (√(20000 : ℝ)) ^ 3 * (20000 : ℝ) = 1 / (25 * √(2 : ℝ)) := by
    have hcube : (√(20000 : ℝ)) ^ 3 = (20000 : ℝ) * (100 * √(2 : ℝ)) := by
      calc
        (√(20000 : ℝ)) ^ 3 = (√(20000 : ℝ)) ^ 2 * √(20000 : ℝ) := by ring
        _ = (20000 : ℝ) * (100 * √(2 : ℝ)) := by rw [hsq20000, hsqrt20000]
    have h4 : (2 : ℝ) ^ 2 = 4 * 1 := by norm_num
    have h100 : (100 : ℝ) * √(2 : ℝ) = 4 * (25 * √(2 : ℝ)) := by ring
    rw [hcube]
    calc
      (2 : ℝ) ^ 2 / ((20000 : ℝ) * (100 * √(2 : ℝ))) * (20000 : ℝ)
        = ((20000 : ℝ) * (2 : ℝ) ^ 2) / ((20000 : ℝ) * (100 * √(2 : ℝ))) := by ring
      _ = (2 : ℝ) ^ 2 / (100 * √(2 : ℝ)) :=
          mul_div_mul_left ((2 : ℝ) ^ 2) (100 * √(2 : ℝ)) (by norm_num)
      _ = (4 * 1) / (4 * (25 * √(2 : ℝ))) := by rw [h4, h100]
      _ = 1 / (25 * √(2 : ℝ)) := mul_div_mul_left 1 (25 * √(2 : ℝ)) (by norm_num)
  have hT2 :
      √(26 : ℝ) * (2 : ℝ) ^ (3 / 2 : ℝ) / (√Real.pi * (√(20000 : ℝ)) ^ 2) * √(20000 : ℝ) =
        √(26 / Real.pi) / 50 := by
    rw [hrpow, hsq20000, hsqrt20000, div_mul_eq_mul_div]
    have hnum : √(26 : ℝ) * (2 * √(2 : ℝ)) * (100 * √(2 : ℝ)) = 400 * √(26 : ℝ) := by
      calc
        √(26 : ℝ) * (2 * √(2 : ℝ)) * (100 * √(2 : ℝ))
          = 200 * (√(2 : ℝ)) ^ 2 * √(26 : ℝ) := by ring
        _ = 200 * 2 * √(26 : ℝ) := by rw [hs2_sq]
        _ = 400 * √(26 : ℝ) := by ring
    have hden : √Real.pi * (20000 : ℝ) = 400 * (50 * √Real.pi) := by ring
    rw [hnum, hden, mul_div_mul_left (√(26 : ℝ)) (50 * √Real.pi) (by norm_num),
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 26), mul_comm (50 : ℝ), ← div_div]
  have hT1_lt : 1 / (25 * √(2 : ℝ)) < 29 / 1000 := by
    rw [div_lt_iff₀ (mul_pos (by norm_num) hs2_pos)]
    have hlt : (40 / 29 : ℝ) < √(2 : ℝ) :=
      (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have hmul := mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 29 / 40)
    linarith
  have hT2_lt : √(26 / Real.pi) / 50 < 58 / 1000 := by
    have h29 : √(26 / Real.pi) < 29 / 10 := by
      refine (Real.sqrt_lt' (by norm_num)).mpr ((div_lt_iff₀ Real.pi_pos).mpr ?_)
      have hpi : 3.14 < Real.pi := Real.pi_gt_d2
      have hmul := mul_lt_mul_of_pos_left hpi (by norm_num : (0 : ℝ) < (29 / 10) ^ 2)
      linarith
    linarith
  rw [hT1, hT2]
  linarith [dc_rhs_lower_bound, hT1_lt, hT2_lt]

/-- Counterexample refuting the literal printed Theorem 3.5 (`\label{thm41}`, eq. `(3.8)`
`\label{41}`, `SteinIntro.tex:815-822`; `ISSUE-3.5`) when `HasDependencyNeighborhoods` is used in
place of `IsDependencyGraph`: at $n = 20000$ and $D = 2$, the printed Wasserstein upper bound is
strictly smaller than $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{N}(0, 1))$. -/
theorem Thm3_5_counterexample :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (n : ℕ) (X : Fin n → Ω → ℝ) (N : Fin n → Finset (Fin n)),
      n = 20000 ∧
      (∀ i : Fin n, AEMeasurable (X i) P) ∧
      (∀ i : Fin n, MemLp (X i) 4 P) ∧
      (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) ∧
      HasDependencyNeighborhoods P X N ∧
      (∀ i : Fin n, i ∈ N i) ∧
      (Finset.univ.sup fun i : Fin n ↦ (N i).card) = 2 ∧
      0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P ∧
      let σ : ℝ := Real.sqrt (ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
      let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / σ
      let D : ℝ := ((Finset.univ.sup fun i : Fin n ↦ (N i).card : ℕ) : ℝ)
      ENNReal.ofReal
        (D ^ 2 / σ ^ 3 * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P)) <
        wassersteinDist (P.map W) (stdNormalLaw.map id) := by
  have hm : 0 < 10000 := by norm_num
  refine ⟨dcSpace 10000, inferInstance, dcMeas 10000, inferInstance, 2 * 10000, dcX 10000,
    dcN 10000, rfl, fun i ↦ (dc_measurable_X 10000 i).aemeasurable,
    fun i ↦ dc_memLp_X 10000 i 4, dc_integral_X 10000, dc_hasDependencyNeighborhoods 10000,
    fun i ↦ dc_self_mem_N i, dc_sup_card_N hm, ?_, ?_⟩
  · rw [dc_variance_sum_X]
    norm_num
  · dsimp only
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance
      (fun ω ↦ ∑ i : Fin (2 * 10000), dcX 10000 i ω) (dcMeas 10000))
    let W : dcSpace 10000 → ℝ := fun ω ↦ (∑ i : Fin (2 * 10000), dcX 10000 i ω) / σ
    let D : ℝ := ((Finset.univ.sup fun i : Fin (2 * 10000) ↦ (dcN 10000 i).card : ℕ) : ℝ)
    have hD : D = 2 := by
      dsimp only [D]
      rw [dc_sup_card_N hm, Nat.cast_ofNat]
    have h20000 : 2 * ((10000 : ℕ) : ℝ) = 20000 := by norm_num
    have hσ : σ = √(20000 : ℝ) := by
      dsimp only [σ]
      rw [dc_variance_sum_X 10000, h20000]
    have hlt_real :
        D ^ 2 / σ ^ 3 * (∑ i : Fin (2 * 10000), ∫ ω, |dcX 10000 i ω| ^ 3 ∂dcMeas 10000) +
          Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
            Real.sqrt (∑ i : Fin (2 * 10000), ∫ ω, dcX 10000 i ω ^ 4 ∂dcMeas 10000) <
        √(2 / Real.pi) - 1 / √(2 : ℝ) := by
      rw [hD, hσ, dc_sum_abs_cube 10000, dc_sum_pow_four 10000, h20000]
      exact dc_numerical_ineq
    have hpos_rhs : 0 < √(2 / Real.pi) - 1 / √(2 : ℝ) := by linarith [dc_rhs_lower_bound]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hpos_rhs).mpr hlt_real)
      (dc_wasserstein_ge hm)

/-- Universal refutation of the literal printed Theorem 3.5 (`\label{thm41}`, eq. `(3.8)`
`\label{41}`, `SteinIntro.tex:815-822`; `ISSUE-3.5`) with `HasDependencyNeighborhoods` in place of
`IsDependencyGraph` (even under `∀ i, i ∈ N i`). -/
theorem not_Thm3_5_printed :
    ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)} {Z : Ω' → ℝ},
        (∀ i : Fin n, AEMeasurable (X i) P) →
        (∀ i : Fin n, MemLp (X i) 4 P) →
        (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
        HasDependencyNeighborhoods P X N →
        (∀ i : Fin n, i ∈ N i) →
        0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
        AEMeasurable Z P' →
        P'.map Z = stdNormalLaw →
        let σ : ℝ := Real.sqrt (ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
        let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / σ
        let D : ℝ := ((Finset.univ.sup fun i : Fin n ↦ (N i).card : ℕ) : ℝ)
        wassersteinDist (P.map W) (P'.map Z) ≤
          ENNReal.ofReal
            (D ^ 2 / σ ^ 3 * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
              Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
                Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P))) := by
  intro h
  obtain ⟨Ω, mΩ, P, hP, n, X, N, _, hmeas, hlp, hmean, hdep, hself, _, hvar, hlt⟩ :=
    Thm3_5_counterexample
  have hle := @h Ω ℝ mΩ inferInstance P hP stdNormalLaw inferInstance n X N id
    hmeas hlp hmean hdep hself hvar (measurable_id (α := ℝ)).aemeasurable Measure.map_id
  exact not_le_of_gt hlt hle

end Counterexample

end SteinMethod
