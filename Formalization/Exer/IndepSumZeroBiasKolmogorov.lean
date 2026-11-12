/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Kolmogorov.ZeroBiasBound
import Formalization.ZeroBias.Coupling
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Section 3.6.1 Exercise: Kolmogorov Bound for Bounded Independent Sums via Zero-Bias

Formalizes the first part of the Section 3.6.1 exercise (`SteinIntro.tex:1741-1742`,
`%%XXXX Exercise 3`; cross-reference note `ISSUE-TYPO-3.27`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `zeroBias_indepSum_kolmogorovDist_le_of_coupling`: quantitative Kolmogorov normal approximation
  bound for a standardized sum $W = S / \sigma$ of independent mean-zero almost surely bounded
  random variables $X_1, \dots, X_n$ given an independent zero-bias coupling $\tilde{X}_i^z$ of
  $\tilde{X}_i = X_i / \sigma$ and variance-weighted mixture index $I$, combining Proposition 3.21
  (`zeroBias_sum_of_iIndepFun`) and Theorem 3.27
  (`kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd`).
* `sec3_6_1_indepSum_kolmogorov_proof` (`Sec3_6_1_indepSum_kolmogorov`): self-contained Kolmogorov
  bound requiring only $X_1, \dots, X_n$ on $(\Omega, P)$ (`AEMeasurable (X i) P`, `iIndepFun X P`,
  `∫ ω, X i ω ∂P = 0`, `∀ᵐ ω ∂P, |X i ω| ≤ C`, `0 < variance (∑ X_i) P`), constructing the
  bounded zero-bias summand laws via `exists_bdd_zeroBias_of_pos_var_exists` and the
  variance-weighted random index internally on an enlarged product probability space.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### Section 1: Private Helpers for Bounded Zero-Bias Summands and Product Lift -/

private lemma memLp_two_of_aemeasurable_ae_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {M : ℝ} (hY_meas : AEMeasurable Y P) (hY_bdd : ∀ᵐ ω ∂P, |Y ω| ≤ M) :
    MemLp Y 2 P :=
  MemLp.of_bound hY_meas.aestronglyMeasurable M
    (hY_bdd.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])

private noncomputable def summandZeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) : Measure ℝ :=
  if 0 < ProbabilityTheory.variance Y P then
    volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P Y w))
  else
    Measure.dirac 0

private lemma isProbabilityMeasure_summandZeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_L2 : MemLp Y 2 P) (hY_mean : ∫ ω, Y ω ∂P = 0) :
    IsProbabilityMeasure (summandZeroBiasLaw P Y) := by
  unfold summandZeroBiasLaw
  split_ifs with hpos
  · exact (zeroBias_law_characterization (Ω' := ℝ) P hY_L2 hY_mean hpos).2.2.1
  · infer_instance

private lemma isZeroBias_summandZeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_L2 : MemLp Y 2 P) (hY_mean : ∫ ω, Y ω ∂P = 0) :
    IsZeroBias P Y (summandZeroBiasLaw P Y) id := by
  unfold summandZeroBiasLaw
  split_ifs with hpos
  · exact (zeroBias_law_characterization (Ω' := ℝ) P hY_L2 hY_mean hpos).2.2.2
  · have hvar0 : ProbabilityTheory.variance Y P = 0 :=
      le_antisymm (not_lt.mp hpos) (ProbabilityTheory.variance_nonneg Y P)
    have hY0 : Y =ᵐ[P] fun _ ↦ (0 : ℝ) := by
      filter_upwards [ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hY_L2 hvar0] with ω hω
      simpa [hY_mean] using hω
    refine ⟨hY_L2, hY_mean, aemeasurable_id, fun f _ _ _ ↦ ?_⟩
    rw [hvar0, zero_mul]
    refine integral_eq_zero_of_ae (hY0.mono fun ω hω ↦ ?_)
    dsimp only at hω ⊢
    simp [hω]

private lemma ae_abs_le_summandZeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {M : ℝ}
    (hY_L2 : MemLp Y 2 P) (hY_mean : ∫ ω, Y ω ∂P = 0) (hY_bdd : ∀ᵐ ω ∂P, |Y ω| ≤ M) :
    ∀ᵐ x : ℝ ∂summandZeroBiasLaw P Y, |x| ≤ M := by
  unfold summandZeroBiasLaw
  split_ifs with hpos
  · exact @ae_abs_le_of_isZeroBias_of_ae_abs_le _ _ _ _ P _ _
      (zeroBias_law_characterization (Ω' := ℝ) P hY_L2 hY_mean hpos).2.2.1 Y id M hpos
      (zeroBias_law_characterization (Ω' := ℝ) P hY_L2 hY_mean hpos).2.2.2 hY_bdd
  · exact (isZeroBias_dirac_zero_of_variance_eq_zero P hY_L2 hY_mean
      (le_antisymm (not_lt.mp hpos) (ProbabilityTheory.variance_nonneg Y P)) hY_bdd).2.2

private noncomputable def varIndexLaw {n : ℕ} (w : Fin n → ℝ) : Measure (Fin n) :=
  ∑ i : Fin n, ENNReal.ofReal (w i) • Measure.dirac i

private lemma isProbabilityMeasure_varIndexLaw
    {n : ℕ} {w : Fin n → ℝ} (hnn : ∀ i : Fin n, 0 ≤ w i) (hsum : (∑ i : Fin n, w i) = 1) :
    IsProbabilityMeasure (varIndexLaw w) := by
  constructor
  simp only [varIndexLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hnn i, hsum, ENNReal.ofReal_one]

private lemma varIndexLaw_real_singleton
    {n : ℕ} {w : Fin n → ℝ} (hnn : ∀ i : Fin n, 0 ≤ w i) (i : Fin n) :
    (varIndexLaw w).real {i} = w i := by
  have happly : varIndexLaw w {i} = ENNReal.ofReal (w i) := by
    simp only [varIndexLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton i), smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hnot : j ∉ ({i} : Set (Fin n)) := hji
      simp [hnot]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  rw [measureReal_def, happly, ENNReal.toReal_ofReal (hnn i)]

private lemma iIndepFun_comp_measurePreserving
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'}
    {X : ι → Ω → ℝ} {π : Ω' → Ω}
    (hπ : MeasurePreserving π Q P) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P) :
    iIndepFun (fun i ω' ↦ X i (π ω')) Q := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hX_indep ⊢
  intro S sets hsets
  have hpre : (⋂ i ∈ S, (fun ω' ↦ X i (π ω')) ⁻¹' sets i) =
      π ⁻¹' (⋂ i ∈ S, X i ⁻¹' sets i) := by
    ext ω'; simp
  have hmeas_inter : MeasurableSet (⋂ i ∈ S, X i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi ↦ (hsets i hi).preimage (hX_meas i)
  rw [hpre, hπ.measure_preimage hmeas_inter.nullMeasurableSet, hX_indep S hsets]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  symm
  exact hπ.measure_preimage ((hsets i hi).preimage (hX_meas i)).nullMeasurableSet

private lemma indepFun_comp_measurePreserving
    {Ω Ω' β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace γ]
    {P : Measure Ω} {Q : Measure Ω'}
    {f : Ω → β} {g : Ω → γ} {π : Ω' → Ω}
    (hπ : MeasurePreserving π Q P) (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g P) :
    IndepFun (f ∘ π) (g ∘ π) Q := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hfg ⊢
  intro s t hs ht
  have hpre : ((f ∘ π) ⁻¹' s ∩ (g ∘ π) ⁻¹' t) = π ⁻¹' (f ⁻¹' s ∩ g ⁻¹' t) := rfl
  rw [hpre, hπ.measure_preimage ((hs.preimage hf).inter (ht.preimage hg)).nullMeasurableSet,
    hfg s t hs ht,
    ← hπ.measure_preimage (hs.preimage hf).nullMeasurableSet,
    ← hπ.measure_preimage (ht.preimage hg).nullMeasurableSet]
  rfl

/-! ### Section 2: Fixed-Space Coupling Bound (`Prop3_21` + `Thm3_27`) -/

/-- Quantitative Kolmogorov normal approximation bound for a unit-variance sum $W = \sum_i Y_i$ of
independent mean-zero almost surely bounded random variables $Y_1, \dots, Y_n$ ($|Y_i| \le M$ a.s.)
coupled on the same probability space with zero-bias variables $Y_i^z$ ($|Y_i^z| \le M$ a.s.) and an
independent variance-weighted index $I$, combining Proposition 3.21 (`zeroBias_sum_of_iIndepFun`)
and Theorem 3.27 (`kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd`). -/
theorem zeroBias_indepSum_kolmogorovDist_le_of_coupling
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {Y Yz : Fin n → Ω → ℝ} {I : Ω → Fin n} {Z : Ω' → ℝ} {M : ℝ}
    (hY_meas : ∀ i : Fin n, Measurable (Y i))
    (hYz_meas : ∀ i : Fin n, Measurable (Yz i))
    (hY_indep : iIndepFun Y P)
    (hY_L2 : ∀ i : Fin n, MemLp (Y i) 2 P)
    (hY_mean : ∀ i : Fin n, ∫ ω, Y i ω ∂P = 0)
    (hVar_sum : (∑ i : Fin n, ProbabilityTheory.variance (Y i) P) = 1)
    (hYz_zb : ∀ i : Fin n, IsZeroBias P (Y i) P (Yz i))
    (hYz_indep : ∀ i : Fin n,
      IndepFun (Yz i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ Y j ω) P)
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin n, P.real (I ⁻¹' {i}) = ProbabilityTheory.variance (Y i) P)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ Y i ω, fun i ↦ Yz i ω)) P)
    (hY_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |Y i ω| ≤ M)
    (hYz_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |Yz i ω| ≤ M)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    kolmogorovDist (P.map (fun ω ↦ ∑ i : Fin n, Y i ω)) (P'.map Z) ≤
      ENNReal.ofReal
        ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 * M)) := by
  let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, Y i ω
  let Wz : Ω → ℝ := fun ω ↦ (∑ j ∈ Finset.univ.erase (I ω), Y j ω) + Yz (I ω) ω
  have hW_var : ProbabilityTheory.variance W P = 1 := by
    have hW_fn : W = ∑ i ∈ Finset.univ, Y i := by ext ω; simp [W]
    rw [hW_fn, IndepFun.variance_sum (fun i _ ↦ hY_L2 i)
      (fun i _ j _ hij ↦ hY_indep.indepFun hij), hVar_sum]
  have hWz_zb : IsZeroBias P W P Wz :=
    zeroBias_sum_of_iIndepFun P hY_meas hYz_meas hY_indep hY_L2 hY_mean hVar_sum hYz_zb hYz_indep
      hI_meas hI_prob hI_indep
  have hY_all : ∀ᵐ ω ∂P, ∀ i : Fin n, |Y i ω| ≤ M := eventually_countable_forall.mpr hY_bdd
  have hYz_all : ∀ᵐ ω ∂P, ∀ i : Fin n, |Yz i ω| ≤ M := eventually_countable_forall.mpr hYz_bdd
  have hδ : ∀ᵐ ω ∂P, |Wz ω - W ω| ≤ 2 * M := by
    filter_upwards [hY_all, hYz_all] with ω hYω hYzω
    have hW_split : W ω = (∑ j ∈ Finset.univ.erase (I ω), Y j ω) + Y (I ω) ω :=
      (Finset.sum_erase_add Finset.univ (fun j ↦ Y j ω) (Finset.mem_univ (I ω))).symm
    have hdiff : Wz ω - W ω = Yz (I ω) ω - Y (I ω) ω := by
      dsimp only [Wz]; rw [hW_split]; ring
    rw [hdiff]
    calc |Yz (I ω) ω - Y (I ω) ω|
        ≤ |Yz (I ω) ω| + |Y (I ω) ω| := abs_sub _ _
      _ ≤ M + M := add_le_add (hYzω (I ω)) (hYω (I ω))
      _ = 2 * M := by ring
  exact kolmogorovDist_map_stdNormal_le_of_isZeroBias_bdd P P' hW_var hWz_zb hδ hZ hZ_law

/-! ### Section 3: Self-Contained Bounded Independent-Sum Bound (`EXER-2`) -/

private lemma sec3_6_1_indepSum_kolmogorov_measurable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ} {C : ℝ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_indep : iIndepFun X P)
    (hX_mean : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |X i ω| ≤ C)
    (hVar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 * C / σ)) := by
  intro S σ W
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  let Y : Fin n → Ω → ℝ := fun i ω ↦ X i ω / σ
  let M : ℝ := C / σ
  have hY_meas : ∀ i : Fin n, Measurable (Y i) := fun i ↦ (hX_meas i).div_const σ
  have hY_indep : iIndepFun Y P :=
    hX_indep.comp (fun _ x ↦ x / σ) (fun _ ↦ measurable_id.div_const σ)
  have hY_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |Y i ω| ≤ M := fun i ↦ by
    filter_upwards [hX_bdd i] with ω hω
    dsimp [Y, M]
    rw [abs_div, abs_of_pos hσ_pos]
    exact div_le_div_of_nonneg_right hω hσ_pos.le
  have hY_L2 : ∀ i : Fin n, MemLp (Y i) 2 P :=
    fun i ↦ memLp_two_of_aemeasurable_ae_abs_le (hY_meas i).aemeasurable (hY_bdd i)
  have hY_mean : ∀ i : Fin n, ∫ ω, Y i ω ∂P = 0 := fun i ↦ by
    dsimp [Y]; rw [integral_div, hX_mean i, zero_div]
  have hW_eq_sumY : W = fun ω ↦ ∑ i : Fin n, Y i ω := by
    ext ω; dsimp [W, S, Y]; rw [Finset.sum_div]
  have hW_var : ProbabilityTheory.variance W P = 1 := by
    have hW_mul : W = fun ω ↦ σ⁻¹ * S ω := by ext ω; dsimp [W]; ring
    rw [hW_mul, ProbabilityTheory.variance_const_mul, inv_pow,
      Real.sq_sqrt (ProbabilityTheory.variance_nonneg S P), inv_mul_cancel₀ hVar.ne']
  have hVar_sum : (∑ i : Fin n, ProbabilityTheory.variance (Y i) P) = 1 := by
    have hfn : W = ∑ i ∈ Finset.univ, Y i := by ext ω; simp [hW_eq_sumY]
    rw [← hW_var, hfn, IndepFun.variance_sum (fun i _ ↦ hY_L2 i)
      (fun i _ j _ hij ↦ hY_indep.indepFun hij)]
  let Ω_ext : Type _ := (Ω × (Fin n → ℝ)) × Fin n
  let νz : Fin n → Measure ℝ := fun i ↦ summandZeroBiasLaw P (Y i)
  have hνz_prob : ∀ i : Fin n, IsProbabilityMeasure (νz i) :=
    fun i ↦ isProbabilityMeasure_summandZeroBiasLaw P (hY_L2 i) (hY_mean i)
  let μZ : Measure (Fin n → ℝ) := @Measure.pi (Fin n) (fun _ ↦ ℝ) _ _ νz
  have hμZ_prob : IsProbabilityMeasure μZ := by dsimp [μZ]; infer_instance
  let wI : Fin n → ℝ := fun i ↦ ProbabilityTheory.variance (Y i) P
  have hwI_nn : ∀ i : Fin n, 0 ≤ wI i := fun i ↦ ProbabilityTheory.variance_nonneg (Y i) P
  let μI : Measure (Fin n) := varIndexLaw wI
  have hμI_prob : IsProbabilityMeasure μI := isProbabilityMeasure_varIndexLaw hwI_nn hVar_sum
  let Q : Measure Ω_ext := (P.prod μZ).prod μI
  have hQ_prob : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  let Y_lift : Fin n → Ω_ext → ℝ := fun i p ↦ Y i p.1.1
  let Yz_lift : Fin n → Ω_ext → ℝ := fun i p ↦ p.1.2 i
  let I_lift : Ω_ext → Fin n := fun p ↦ p.2
  have hπ1 : MeasurePreserving (fun p : Ω_ext ↦ p.1) Q (P.prod μZ) := measurePreserving_fst
  have hπY : MeasurePreserving (fun p : Ω_ext ↦ p.1.1) Q P := measurePreserving_fst.comp hπ1
  have hπZ : MeasurePreserving (fun p : Ω_ext ↦ p.1.2) Q μZ := measurePreserving_snd.comp hπ1
  have hπI : MeasurePreserving I_lift Q μI := measurePreserving_snd
  have hid_Y : ∀ i : Fin n, IdentDistrib (Y_lift i) (Y i) Q P := fun i ↦
    ⟨((hY_meas i).comp hπY.measurable).aemeasurable, (hY_meas i).aemeasurable, by
      change Q.map (Y i ∘ fun p : Ω_ext ↦ p.1.1) = P.map (Y i)
      rw [← Measure.map_map (hY_meas i) hπY.measurable, hπY.map_eq]⟩
  have hid_Yz : ∀ i : Fin n, IdentDistrib (Yz_lift i) id Q (νz i) := fun i ↦ by
    have hcomp : MeasurePreserving (Yz_lift i) Q (νz i) :=
      (measurePreserving_eval (μ := νz) i).comp hπZ
    exact ⟨hcomp.measurable.aemeasurable, aemeasurable_id, by rw [hcomp.map_eq, Measure.map_id]⟩
  have hY_lift_meas : ∀ i : Fin n, Measurable (Y_lift i) :=
    fun i ↦ (hY_meas i).comp (measurable_fst.comp measurable_fst)
  have hYz_lift_meas : ∀ i : Fin n, Measurable (Yz_lift i) :=
    fun i ↦ (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hI_lift_meas : Measurable I_lift := measurable_snd
  have hY_lift_indep : iIndepFun Y_lift Q :=
    iIndepFun_comp_measurePreserving hπY hY_meas hY_indep
  have hY_lift_L2 : ∀ i : Fin n, MemLp (Y_lift i) 2 Q :=
    fun i ↦ (hid_Y i).symm.memLp_snd (hY_L2 i)
  have hY_lift_mean : ∀ i : Fin n, ∫ p, Y_lift i p ∂Q = 0 :=
    fun i ↦ (hid_Y i).integral_eq.trans (hY_mean i)
  have hVar_lift_sum : (∑ i : Fin n, ProbabilityTheory.variance (Y_lift i) Q) = 1 := by
    simp_rw [(hid_Y _).variance_eq]
    exact hVar_sum
  have hYz_lift_zb : ∀ i : Fin n, IsZeroBias Q (Y_lift i) Q (Yz_lift i) := fun i ↦
    (isZeroBias_summandZeroBiasLaw P (hY_L2 i) (hY_mean i)).congr_identDistrib
      (hid_Y i).symm (hid_Yz i).symm
  have hYz_lift_indep : ∀ i : Fin n,
      IndepFun (Yz_lift i) (fun p (j : {j : Fin n // j ≠ i}) ↦ Y_lift j p) Q := fun i ↦ by
    have hm1 : Measurable (fun ω : Ω ↦ fun j : {j : Fin n // j ≠ i} ↦ Y j.1 ω) :=
      Measurable.of_eval fun j ↦ hY_meas j.1
    have hm2 : Measurable (fun z : Fin n → ℝ ↦ z i) := measurable_pi_apply i
    have hbase := (indepFun_prod (μ := P) (ν := μZ) hm1 hm2).symm
    exact indepFun_comp_measurePreserving hπ1 (hm2.comp measurable_snd)
      (hm1.comp measurable_fst) hbase
  have hI_lift_prob : ∀ i : Fin n,
      Q.real (I_lift ⁻¹' {i}) = ProbabilityTheory.variance (Y_lift i) Q := fun i ↦ by
    have hpre : Q (I_lift ⁻¹' {i}) = μI {i} :=
      hπI.measure_preimage (measurableSet_singleton i).nullMeasurableSet
    rw [measureReal_def, hpre, ← measureReal_def, varIndexLaw_real_singleton hwI_nn i,
      (hid_Y i).variance_eq]
  have hI_lift_indep :
      IndepFun I_lift (fun p ↦ (fun i ↦ Y_lift i p, fun i ↦ Yz_lift i p)) Q := by
    have hm_pair : Measurable (fun q : Ω × (Fin n → ℝ) ↦ (fun i ↦ Y i q.1, fun i ↦ q.2 i)) :=
      (Measurable.of_eval fun i ↦ (hY_meas i).comp measurable_fst).prodMk
        (Measurable.of_eval fun i ↦ (measurable_pi_apply i).comp measurable_snd)
    exact (indepFun_prod (μ := P.prod μZ) (ν := μI) hm_pair measurable_id).symm
  have hBdd_set : MeasurableSet {x : ℝ | |x| ≤ M} :=
    measurableSet_Iic.preimage continuous_abs.measurable
  have hY_lift_bdd : ∀ i : Fin n, ∀ᵐ p ∂Q, |Y_lift i p| ≤ M := fun i ↦ by
    have hmap : ∀ᵐ x ∂(Q.map (Y_lift i)), |x| ≤ M := by
      rw [(hid_Y i).map_eq]
      exact (ae_map_iff (hY_meas i).aemeasurable hBdd_set).mpr (hY_bdd i)
    exact (ae_map_iff (hY_lift_meas i).aemeasurable hBdd_set).mp hmap
  have hYz_lift_bdd : ∀ i : Fin n, ∀ᵐ p ∂Q, |Yz_lift i p| ≤ M := fun i ↦ by
    have hmap : ∀ᵐ x ∂(Q.map (Yz_lift i)), |x| ≤ M := by
      rw [(hid_Yz i).map_eq, Measure.map_id]
      exact ae_abs_le_summandZeroBiasLaw P (hY_L2 i) (hY_mean i) (hY_bdd i)
    exact (ae_map_iff (hYz_lift_meas i).aemeasurable hBdd_set).mp hmap
  have hBound := zeroBias_indepSum_kolmogorovDist_le_of_coupling Q P' hY_lift_meas hYz_lift_meas
    hY_lift_indep hY_lift_L2 hY_lift_mean hVar_lift_sum hYz_lift_zb hYz_lift_indep hI_lift_meas
    hI_lift_prob hI_lift_indep hY_lift_bdd hYz_lift_bdd hZ hZ_law
  have hW_meas : Measurable W := by
    rw [hW_eq_sumY]
    exact Finset.measurable_fun_sum Finset.univ fun i _ ↦ hY_meas i
  have hW_comp : (fun p : Ω_ext ↦ ∑ i : Fin n, Y_lift i p) = W ∘ fun p : Ω_ext ↦ p.1.1 := by
    ext p; simp [Y_lift, W, S, Y, Finset.sum_div]
  have hW_map : Q.map (fun p : Ω_ext ↦ ∑ i : Fin n, Y_lift i p) = P.map W := by
    rw [hW_comp, ← Measure.map_map hW_meas hπY.measurable, hπY.map_eq]
  rw [hW_map] at hBound
  have h2M : 2 * M = 2 * C / σ := by dsimp [M]; ring
  rwa [h2M] at hBound

/-- **Section 3.6.1 Bounded Independent-Sum Kolmogorov Bound** (`Sec3_6_1_indepSum_kolmogorov`,
`SteinIntro.tex:1741-1742`, `%%XXXX Exercise 3`; cross-reference note `ISSUE-TYPO-3.27`): if
$X_1, \dots, X_n$ are independent mean-zero random variables satisfying $|X_i| \le C$ almost surely
with $\sigma^2 = \operatorname{Var}(\sum_{i=1}^n X_i) > 0$, $W = (\sum_{i=1}^n X_i) / \sigma$, and
$Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
(1 + 1/\sqrt{2\pi} + \sqrt{2\pi}/4)\,(2 C / \sigma)$. -/
theorem sec3_6_1_indepSum_kolmogorov_proof
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ} {C : ℝ}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX_indep : iIndepFun X P)
    (hX_mean : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hX_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |X i ω| ≤ C)
    (hVar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 * C / σ)) := by
  intro S σ W
  let Xm : Fin n → Ω → ℝ := fun i ↦ (hX_meas i).mk (X i)
  have hXm_meas : ∀ i : Fin n, Measurable (Xm i) := fun i ↦ (hX_meas i).measurable_mk
  have hXm_ae : ∀ i : Fin n, X i =ᵐ[P] Xm i := fun i ↦ (hX_meas i).ae_eq_mk
  have hXm_indep : iIndepFun Xm P := hX_indep.congr hXm_ae
  have hXm_mean : ∀ i : Fin n, ∫ ω, Xm i ω ∂P = 0 :=
    fun i ↦ (integral_congr_ae (hXm_ae i).symm).trans (hX_mean i)
  have hXm_bdd : ∀ i : Fin n, ∀ᵐ ω ∂P, |Xm i ω| ≤ C :=
    fun i ↦ (hX_bdd i).mp ((hXm_ae i).mono fun _ h1 h2 ↦ h1 ▸ h2)
  have hSum_ae : S =ᵐ[P] fun ω ↦ ∑ i : Fin n, Xm i ω :=
    (eventually_countable_forall.mpr hXm_ae).mono fun ω hω ↦ Finset.sum_congr rfl fun i _ ↦ hω i
  have hVar_m : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, Xm i ω) P := by
    rwa [← ProbabilityTheory.variance_congr hSum_ae]
  have hBound := sec3_6_1_indepSum_kolmogorov_measurable P P' hXm_meas hXm_indep hXm_mean hXm_bdd
    hVar_m hZ hZ_law
  dsimp only at hBound
  have hσ_m : Real.sqrt (ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, Xm i ω) P) = σ := by
    rw [ProbabilityTheory.variance_congr hSum_ae.symm]
  rw [hσ_m] at hBound
  have hW_map : P.map (fun ω ↦ (∑ i : Fin n, Xm i ω) / σ) = P.map W := by
    refine Measure.map_congr (hSum_ae.symm.mono fun ω hω ↦ ?_)
    dsimp only at hω
    change (∑ i : Fin n, Xm i ω) / σ = S ω / σ
    rw [hω]
  rwa [hW_map] at hBound

end SteinMethod
