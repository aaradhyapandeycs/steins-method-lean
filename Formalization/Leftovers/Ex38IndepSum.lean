/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.SteinPairBound
import Formalization.SizeBias.Basic
import Formalization.SizeBias.Coupling
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Example 3.8: Size-Bias Normal Approximation for Independent Sums

Formalizes Example 3.8 (`\label{ex71}`, `SteinIntro.tex:1349-1353`; Backlog item 9) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* `sizeBias_indepSum_wassersteinDist_le_of_coupling`: quantitative Wasserstein-1 normal
  approximation bound for a standardized sum $W = (S - \mu)/\sigma$ of independent nonnegative $L^3$
  random variables $X_1, \dots, X_n$ given an independent size-bias coupling $X_i^s$ and mixture
  index $I$, combining Corollary 3.15 (`sizeBias_sum_of_iIndepFun`), Theorem 3.13
  (`sizeBias_wassersteinDist_le`), and Remark 3.4 (`evariance_condExp_mono`).
* `sizeBias_indepSum_wassersteinDist_le` (`Ex3_8`): self-contained Wasserstein-1 bound requiring
  only $X_1, \dots, X_n$ on $(\Omega, P)$ (`0 ≤ᵐ[P] X i`, `MemLp (X i) 3 P`, `iIndepFun X P`,
  `0 < variance (∑ X_i) P`), constructing the independent size-bias summands and random index
  internally on an enlarged product probability space.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### Section 1: Private Helpers for Law Transfer and Enlarged Product Space -/

private lemma IsSizeBias.congr_identDistrib
    {Ω₁ Ω₂ Ω₁' Ω₂' : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₁'] [MeasurableSpace Ω₂']
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P₁' : Measure Ω₁'} {P₂' : Measure Ω₂'}
    {X₁ : Ω₁ → ℝ} {X₂ : Ω₂ → ℝ} {Xs₁ : Ω₁' → ℝ} {Xs₂ : Ω₂' → ℝ}
    (hSB : IsSizeBias P₁ X₁ P₁' Xs₁)
    (hX : IdentDistrib X₁ X₂ P₁ P₂) (hXs : IdentDistrib Xs₁ Xs₂ P₁' P₂') :
    IsSizeBias P₂ X₂ P₂' Xs₂ := by
  rcases hSB with ⟨hX₁_nn, hX₁_int, _, hSB_eq⟩
  have hmap_nn : ∀ᵐ y ∂(P₂.map X₂), 0 ≤ y := by
    rw [← hX.map_eq]
    exact (ae_map_iff (p := fun y : ℝ ↦ 0 ≤ y) hX.aemeasurable_fst measurableSet_Ici).mpr hX₁_nn
  have hX₂_nn : 0 ≤ᵐ[P₂] X₂ :=
    (ae_map_iff (p := fun y : ℝ ↦ 0 ≤ y) hX.aemeasurable_snd measurableSet_Ici).mp hmap_nn
  refine ⟨hX₂_nn, hX.integrable_snd hX₁_int, hXs.aemeasurable_snd, ?_⟩
  intro f hf hX₂f_int
  have hXf : IdentDistrib (fun ω ↦ X₁ ω * f (X₁ ω)) (fun ω ↦ X₂ ω * f (X₂ ω)) P₁ P₂ :=
    hX.comp (measurable_id.mul hf)
  have hfXs : IdentDistrib (fun ω' ↦ f (Xs₁ ω')) (fun ω' ↦ f (Xs₂ ω')) P₁' P₂' :=
    hXs.comp hf
  rw [← hXf.integral_eq, ← hX.integral_eq, ← hfXs.integral_eq]
  exact hSB_eq f hf (hXf.symm.integrable_snd hX₂f_int)

private lemma integrable_cube_of_nonneg_memLp_three
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → ℝ} (hY_nn : 0 ≤ᵐ[P] Y) (hY3 : MemLp Y 3 P) :
    Integrable (fun ω ↦ Y ω ^ 3) P := by
  have h3 : MemLp Y (3 : ℕ) P := hY3
  have hnorm : Integrable (fun ω ↦ ‖Y ω‖ ^ 3) P := h3.integrable_norm_pow'
  refine hnorm.congr (hY_nn.mono fun ω hω ↦ ?_)
  dsimp only
  rw [Real.norm_of_nonneg hω]

private noncomputable def summandSizeBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) : Measure ℝ :=
  if 0 < ∫ ω, Y ω ∂P then
    (P.map Y).withDensity (fun x ↦ ENNReal.ofReal (x / ∫ ω, Y ω ∂P))
  else
    Measure.dirac 0

private lemma isProbabilityMeasure_summandSizeBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_nn : 0 ≤ᵐ[P] Y) (hY_int : Integrable Y P) :
    IsProbabilityMeasure (summandSizeBiasLaw P Y) := by
  unfold summandSizeBiasLaw
  split_ifs with hpos
  · exact (sizeBias_law_characterization (Ω' := ℝ) P hY_nn hY_int hpos).2.1
  · infer_instance

private lemma isSizeBias_summandSizeBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_nn : 0 ≤ᵐ[P] Y) (hY_int : Integrable Y P) :
    IsSizeBias P Y (summandSizeBiasLaw P Y) id := by
  unfold summandSizeBiasLaw
  split_ifs with hpos
  · exact (sizeBias_law_characterization (Ω' := ℝ) P hY_nn hY_int hpos).2.2
  · have hμ0 : ∫ ω, Y ω ∂P = 0 := le_antisymm (not_lt.mp hpos) (integral_nonneg_of_ae hY_nn)
    have hY0 : Y =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hY_nn hY_int).mp hμ0
    refine ⟨hY_nn, hY_int, aemeasurable_id, fun f _ _ ↦ ?_⟩
    rw [hμ0, zero_mul]
    exact integral_eq_zero_of_ae (hY0.mono fun ω hω ↦ by simp [hω])

private lemma memLp_two_id_summandSizeBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_nn : 0 ≤ᵐ[P] Y) (hY3 : MemLp Y 3 P) :
    MemLp (id : ℝ → ℝ) 2 (summandSizeBiasLaw P Y) := by
  have hY_int : Integrable Y P := hY3.integrable (by norm_num)
  by_cases hpos : 0 < ∫ ω, Y ω ∂P
  · have hdef : summandSizeBiasLaw P Y =
        (P.map Y).withDensity (fun x ↦ ENNReal.ofReal (x / ∫ ω, Y ω ∂P)) := by
      simp [summandSizeBiasLaw, hpos]
    rw [hdef]
    obtain ⟨hprob, hSB⟩ := (sizeBias_law_characterization (Ω' := ℝ) P hY_nn hY_int hpos).2
    have := hprob
    have hcube : Integrable (fun ω ↦ Y ω * (fun x : ℝ ↦ x ^ 2) (Y ω)) P := by
      have heq : (fun ω ↦ Y ω * Y ω ^ 2) = fun ω ↦ Y ω ^ 3 := funext fun _ ↦ by ring
      dsimp only
      rw [heq]
      exact integrable_cube_of_nonneg_memLp_three hY_nn hY3
    have hsq_int := hSB.integrable_comp_of_pos_mean hpos (measurable_id.pow_const 2) hcube
    exact (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr hsq_int
  · have hdef : summandSizeBiasLaw P Y = Measure.dirac 0 := by
      simp [summandSizeBiasLaw, hpos]
    rw [hdef]
    refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr ?_
    have hae : (fun _ : ℝ ↦ (0 : ℝ)) =ᵐ[Measure.dirac (0 : ℝ)] fun x : ℝ ↦ x ^ 2 := by
      rw [Filter.EventuallyEq, ae_dirac_eq]
      norm_num
    exact (integrable_const (0 : ℝ)).congr hae

private noncomputable def meanIndexLaw {n : ℕ} (w : Fin n → ℝ) : Measure (Fin n) :=
  ∑ i : Fin n, ENNReal.ofReal (w i) • Measure.dirac i

private lemma isProbabilityMeasure_meanIndexLaw
    {n : ℕ} {w : Fin n → ℝ} (hnn : ∀ i : Fin n, 0 ≤ w i) (hsum : (∑ i : Fin n, w i) = 1) :
    IsProbabilityMeasure (meanIndexLaw w) := by
  constructor
  simp only [meanIndexLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hnn i, hsum, ENNReal.ofReal_one]

private lemma meanIndexLaw_real_singleton
    {n : ℕ} {w : Fin n → ℝ} (hnn : ∀ i : Fin n, 0 ≤ w i) (i : Fin n) :
    (meanIndexLaw w).real {i} = w i := by
  have happly : meanIndexLaw w {i} = ENNReal.ofReal (w i) := by
    simp only [meanIndexLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
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

/-! ### Section 2: Fixed-Space Coupling Bound (`Cor3_15` + `Thm3_13` + `Rem3_4`) -/

private lemma summand_mean_mul_sq_diff_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {U Us : Ω → ℝ}
    (hU_meas : Measurable U) (hUs_meas : Measurable Us)
    (hU_nn : 0 ≤ᵐ[P] U) (hU3 : MemLp U 3 P) (hUs2 : MemLp Us 2 P)
    (hSB : IsSizeBias P U P Us) (hIndep : IndepFun Us U P) :
    (∫ ω, U ω ∂P) * ∫ ω, (Us ω - U ω) ^ 2 ∂P =
      (∫ ω, U ω ^ 3 ∂P) - (∫ ω, U ω ∂P) * ∫ ω, U ω ^ 2 ∂P := by
  have hU2 : MemLp U 2 P := hU3.mono_exponent (by norm_num)
  have hU_int : Integrable U P := hU3.integrable (by norm_num)
  rcases (integral_nonneg_of_ae hU_nn).eq_or_lt with hμ0 | _
  · have hμ_zero : ∫ ω, U ω ∂P = 0 := hμ0.symm
    have hU_ae0 : U =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg_ae hU_nn hU_int).mp hμ_zero
    have hU3_zero : ∫ ω, U ω ^ 3 ∂P = 0 :=
      integral_eq_zero_of_ae (hU_ae0.mono fun ω hω ↦ by simp [hω])
    rw [hμ_zero, hU3_zero]
    ring
  · have hUs_sq_int : Integrable (fun ω ↦ Us ω ^ 2) P := hUs2.integrable_sq
    have hU_sq_int : Integrable (fun ω ↦ U ω ^ 2) P := hU2.integrable_sq
    have hMul_int : Integrable (fun ω ↦ Us ω * U ω) P := hUs2.integrable_mul hU2
    have hU_cube_int : Integrable (fun ω ↦ U ω ^ 3) P :=
      integrable_cube_of_nonneg_memLp_three hU_nn hU3
    have hSB1 : ∫ ω, U ω ^ 2 ∂P = (∫ ω, U ω ∂P) * ∫ ω, Us ω ∂P := by
      have heq : (fun ω ↦ U ω * id (U ω)) = fun ω ↦ U ω ^ 2 := funext fun _ ↦ by simp [sq]
      rw [← heq]
      exact hSB.2.2.2 id measurable_id (heq ▸ hU_sq_int)
    have hSB2 : ∫ ω, U ω ^ 3 ∂P = (∫ ω, U ω ∂P) * ∫ ω, Us ω ^ 2 ∂P := by
      have heq : (fun ω ↦ U ω * (fun x : ℝ ↦ x ^ 2) (U ω)) = fun ω ↦ U ω ^ 3 :=
        funext fun _ ↦ by dsimp only; ring
      rw [← heq]
      exact hSB.2.2.2 (fun x : ℝ ↦ x ^ 2) (measurable_id.pow_const 2) (heq ▸ hU_cube_int)
    have hCross : ∫ ω, Us ω * U ω ∂P = (∫ ω, Us ω ∂P) * ∫ ω, U ω ∂P :=
      hIndep.integral_fun_mul_eq_mul_integral
        hUs_meas.aestronglyMeasurable hU_meas.aestronglyMeasurable
    have hexp : (fun ω ↦ (Us ω - U ω) ^ 2) =
        fun ω ↦ (Us ω ^ 2 + U ω ^ 2) - 2 * (Us ω * U ω) := funext fun _ ↦ by ring
    rw [hexp, integral_sub (hUs_sq_int.fun_add hU_sq_int) (hMul_int.const_mul 2),
      integral_add hUs_sq_int hU_sq_int, integral_const_mul 2 (fun ω ↦ Us ω * U ω), hCross]
    calc
      (∫ ω, U ω ∂P) *
          ((∫ ω, Us ω ^ 2 ∂P + ∫ ω, U ω ^ 2 ∂P) - 2 * ((∫ ω, Us ω ∂P) * ∫ ω, U ω ∂P))
        = ((∫ ω, U ω ∂P) * ∫ ω, Us ω ^ 2 ∂P) + (∫ ω, U ω ∂P) * (∫ ω, U ω ^ 2 ∂P) -
            2 * ((∫ ω, U ω ∂P) * ∫ ω, Us ω ∂P) * (∫ ω, U ω ∂P) := by ring
      _ = (∫ ω, U ω ^ 3 ∂P) + (∫ ω, U ω ∂P) * (∫ ω, U ω ^ 2 ∂P) -
            2 * (∫ ω, U ω ^ 2 ∂P) * (∫ ω, U ω ∂P) := by rw [← hSB2, ← hSB1]
      _ = (∫ ω, U ω ^ 3 ∂P) - (∫ ω, U ω ∂P) * ∫ ω, U ω ^ 2 ∂P := by ring

private lemma condExp_diff_vx_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xs : Fin n → Ω → ℝ} {I : Ω → Fin n}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hXs_meas : ∀ i : Fin n, Measurable (Xs i))
    (hX_int : ∀ i : Fin n, Integrable (X i) P)
    (hXs_int : ∀ i : Fin n, Integrable (Xs i) P)
    (hXXs_indep : IndepFun (fun ω i ↦ Xs i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω)) P) :
    let μ : ℝ := ∑ j : Fin n, ∫ ω, X j ω ∂P
    let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
    P[fun ω ↦ Xs (I ω) ω - X (I ω) ω | MeasurableSpace.comap VX inferInstance] =ᵐ[P]
      fun ω ↦ ∑ i : Fin n, ((∫ x, X i x ∂P) / μ) * ((∫ x, Xs i x ∂P) - X i ω) := by
  intro μ VX
  let VXs : Ω → Fin n → ℝ := fun ω i ↦ Xs i ω
  let VXXs : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω ↦ (VX ω, VXs ω)
  let D : Ω → ℝ := fun ω ↦ Xs (I ω) ω - X (I ω) ω
  let g : Ω → ℝ :=
    fun ω ↦ ∑ i : Fin n, ((∫ x, X i x ∂P) / μ) * ((∫ x, Xs i x ∂P) - X i ω)
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hVXXs_meas : Measurable VXXs := hVX_meas.prodMk (.of_eval hXs_meas)
  have hD_decomp : D = fun ω ↦
      ∑ i : Fin n, (I ⁻¹' {i}).indicator (fun ω' ↦ Xs i ω' - X i ω') ω := by
    funext ω; symm
    rw [Finset.sum_eq_single (I ω)]
    · simp [D]
    · intro i _ hi; exact Set.indicator_of_notMem (by simpa using hi.symm) _
    · intro h; exact False.elim (h (Finset.mem_univ _))
  have hTerm_int : ∀ i : Fin n,
      Integrable ((I ⁻¹' {i}).indicator (fun ω' ↦ Xs i ω' - X i ω')) P :=
    fun i ↦ ((hXs_int i).sub (hX_int i)).indicator (hI_meas (measurableSet_singleton i))
  have hD_int : Integrable D P := hD_decomp ▸ integrable_finsetSum Finset.univ fun i _ ↦ hTerm_int i
  have hg_term_int : ∀ i : Fin n,
      Integrable (fun ω ↦ ((∫ x, X i x ∂P) / μ) * ((∫ x, Xs i x ∂P) - X i ω)) P :=
    fun i ↦ ((integrable_const (∫ x, Xs i x ∂P)).sub (hX_int i)).const_mul ((∫ x, X i x ∂P) / μ)
  have hg_int : Integrable g P := integrable_finsetSum Finset.univ fun i _ ↦ hg_term_int i
  have hg_sm : StronglyMeasurable[MeasurableSpace.comap VX inferInstance] g := by
    let g0 : (Fin n → ℝ) → ℝ :=
      fun v ↦ ∑ i : Fin n, ((∫ x, X i x ∂P) / μ) * ((∫ x, Xs i x ∂P) - v i)
    have hg0_meas : Measurable g0 :=
      Finset.measurable_fun_sum Finset.univ fun i _ ↦
        measurable_const.fun_mul (measurable_const.fun_sub (measurable_pi_apply i))
    exact (hg0_meas.comp (comap_measurable (m := inferInstance) VX)).stronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq hVX_meas.comap_le hD_int
    (fun s _ _ ↦ hg_int.integrableOn) (fun s hs _ ↦ ?_) hg_sm.aestronglyMeasurable).symm
  rcases hs with ⟨T, hT, rfl⟩
  rw [hD_decomp, integral_finsetSum Finset.univ fun i _ ↦ (hTerm_int i).integrableOn,
    integral_finsetSum Finset.univ fun i _ ↦ (hg_term_int i).integrableOn]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let fI : Fin n → ℝ := ({i} : Set (Fin n)).indicator 1
  let gV : (Fin n → ℝ) × (Fin n → ℝ) → ℝ :=
    (Prod.fst ⁻¹' T).indicator (fun p ↦ p.2 i - p.1 i)
  have hfI_meas : Measurable fI := measurable_one.indicator (measurableSet_singleton i)
  have hgV_meas : Measurable gV :=
    (((measurable_pi_apply i).comp measurable_snd).fun_sub
      ((measurable_pi_apply i).comp measurable_fst)).indicator (measurable_fst hT)
  have hpt : (VX ⁻¹' T).indicator ((I ⁻¹' {i}).indicator (fun ω' ↦ Xs i ω' - X i ω')) =
      fun ω ↦ fI (I ω) * gV (VXXs ω) := by
    funext ω
    by_cases hTω : VX ω ∈ T <;> by_cases hIω : I ω = i <;> simp [fI, gV, VXXs, VX, VXs, hTω, hIω]
  have hfI_comp : (fun ω ↦ fI (I ω)) = (I ⁻¹' {i}).indicator (1 : Ω → ℝ) := by
    funext ω; by_cases hIω : I ω = i <;> simp [fI, hIω]
  have hgV_comp : (fun ω ↦ gV (VXXs ω)) = (VX ⁻¹' T).indicator (fun ω ↦ Xs i ω - X i ω) := by
    funext ω; by_cases hTω : VX ω ∈ T <;> simp [gV, VXXs, VX, VXs, hTω]
  have hStepI :
      ∫ ω in VX ⁻¹' T, (I ⁻¹' {i}).indicator (fun ω' ↦ Xs i ω' - X i ω') ω ∂P =
        ((∫ x, X i x ∂P) / μ) * ∫ ω in VX ⁻¹' T, (Xs i ω - X i ω) ∂P := by
    rw [← integral_indicator (hVX_meas hT), hpt,
      hI_indep.integral_fun_comp_mul_comp hI_meas.aemeasurable hVXXs_meas.aemeasurable
        hfI_meas.stronglyMeasurable.aestronglyMeasurable
        hgV_meas.stronglyMeasurable.aestronglyMeasurable,
      hfI_comp, integral_indicator_one (hI_meas (measurableSet_singleton i)), hI_prob i,
      hgV_comp, integral_indicator (hVX_meas hT)]
  have hStepXs :
      ∫ ω in VX ⁻¹' T, Xs i ω ∂P = ∫ ω in VX ⁻¹' T, (∫ x, Xs i x ∂P) ∂P := by
    let indT : (Fin n → ℝ) → ℝ := T.indicator 1
    have hindT_meas : Measurable indT := measurable_one.indicator hT
    have hindep_i : IndepFun (Xs i) (indT ∘ VX) P :=
      hXXs_indep.comp (measurable_pi_apply i) hindT_meas
    have hmul_eq : (VX ⁻¹' T).indicator (Xs i) = fun ω ↦ Xs i ω * (indT ∘ VX) ω := by
      funext ω; by_cases hTω : VX ω ∈ T <;> simp [indT, hTω]
    have hconst_eq : (VX ⁻¹' T).indicator (fun _ : Ω ↦ ∫ x, Xs i x ∂P) =
        fun ω ↦ (∫ x, Xs i x ∂P) * (indT ∘ VX) ω := by
      funext ω; by_cases hTω : VX ω ∈ T <;> simp [indT, hTω]
    rw [← integral_indicator (hVX_meas hT), hmul_eq,
      hindep_i.integral_fun_mul_eq_mul_integral (hXs_meas i).aestronglyMeasurable
        (hindT_meas.comp hVX_meas).aestronglyMeasurable,
      ← integral_const_mul (∫ x, Xs i x ∂P) (indT ∘ VX), ← hconst_eq,
      integral_indicator (hVX_meas hT)]
  rw [hStepI, integral_const_mul ((∫ x, X i x ∂P) / μ),
    integral_sub (integrable_const (∫ x, Xs i x ∂P)).integrableOn (hX_int i).integrableOn,
    integral_sub (hXs_int i).integrableOn (hX_int i).integrableOn, hStepXs]

private lemma ennreal_thm313_rhs_combine
    {μ σ Vsum Msum D2 : ℝ} {Ehalf : ℝ≥0∞}
    (hμ : 0 < μ) (hσ : 0 < σ) (hD2_nn : 0 ≤ D2)
    (hTerm2 : μ * D2 = Msum)
    (hEhalf : Ehalf ≤ ENNReal.ofReal (Real.sqrt Vsum / μ)) :
    ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Ehalf +
        ENNReal.ofReal (μ / σ ^ 3) * ENNReal.ofReal D2 ≤
      ENNReal.ofReal (1 / σ ^ 2 * Real.sqrt (2 / Real.pi * Vsum) + 1 / σ ^ 3 * Msum) := by
  have hMsum_nn : 0 ≤ Msum := hTerm2 ▸ mul_nonneg hμ.le hD2_nn
  have hC1_nn : 0 ≤ μ / σ ^ 2 * Real.sqrt (2 / Real.pi) :=
    mul_nonneg (div_nonneg hμ.le (sq_nonneg σ)) (Real.sqrt_nonneg _)
  have hC2_nn : 0 ≤ μ / σ ^ 3 := div_nonneg hμ.le (pow_nonneg hσ.le 3)
  have hT1_nn : 0 ≤ 1 / σ ^ 2 * Real.sqrt (2 / Real.pi * Vsum) :=
    mul_nonneg (div_nonneg zero_le_one (sq_nonneg σ)) (Real.sqrt_nonneg _)
  have hT2_nn : 0 ≤ 1 / σ ^ 3 * Msum :=
    mul_nonneg (div_nonneg zero_le_one (pow_nonneg hσ.le 3)) hMsum_nn
  have hFirst :
      (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * (Real.sqrt Vsum / μ) =
        1 / σ ^ 2 * Real.sqrt (2 / Real.pi * Vsum) := by
    rw [Real.sqrt_mul (div_nonneg zero_le_two Real.pi_pos.le) Vsum]
    calc
      (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * (Real.sqrt Vsum / μ)
          = (μ / μ) * (1 / σ ^ 2 * (Real.sqrt (2 / Real.pi) * Real.sqrt Vsum)) := by ring
      _ = 1 / σ ^ 2 * (Real.sqrt (2 / Real.pi) * Real.sqrt Vsum) := by
          rw [div_self hμ.ne', one_mul]
  have hSecond : (μ / σ ^ 3) * D2 = 1 / σ ^ 3 * Msum := by
    rw [← hTerm2]; ring
  calc
    ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * Ehalf +
          ENNReal.ofReal (μ / σ ^ 3) * ENNReal.ofReal D2
      ≤ ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) *
            ENNReal.ofReal (Real.sqrt Vsum / μ) +
          ENNReal.ofReal (μ / σ ^ 3) * ENNReal.ofReal D2 := by
        gcongr
    _ = ENNReal.ofReal ((μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) * (Real.sqrt Vsum / μ)) +
          ENNReal.ofReal ((μ / σ ^ 3) * D2) := by
        rw [← ENNReal.ofReal_mul hC1_nn, ← ENNReal.ofReal_mul hC2_nn]
    _ = ENNReal.ofReal (1 / σ ^ 2 * Real.sqrt (2 / Real.pi * Vsum) + 1 / σ ^ 3 * Msum) := by
        rw [hFirst, hSecond, ← ENNReal.ofReal_add hT1_nn hT2_nn]

/-- **Example 3.8, fixed-space coupling form** (`\label{ex71}`, `SteinIntro.tex:1349-1353`):
for independent a.s. nonnegative $L^3$ random variables $X_1, \dots, X_n$ with positive sum
variance $\sigma^2 = \operatorname{Var}(\sum_i X_i) > 0$, $L^2$ size-bias summands $X_i^s$ jointly
independent of $(X_1, \dots, X_n)$, and an independent random index $I$ with
$\mathbb{P}(I = i) = \mu_i / \mu$, plugging Corollary 3.15 into Theorem 3.13 and Remark 3.4 yields
$$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{1}{\sigma^2}\sqrt{\frac{2}{\pi}\sum_{i=1}^n \mu_i^2 \operatorname{Var}(X_i)} +
\frac{1}{\sigma^3}\sum_{i=1}^n \bigl(\mathbb{E}[X_i^3] - \mu_i \mathbb{E}[X_i^2]\bigr).$$ -/
theorem sizeBias_indepSum_wassersteinDist_le_of_coupling
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X Xs : Fin n → Ω → ℝ} {I : Ω → Fin n} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hXs_meas : ∀ i : Fin n, Measurable (Xs i))
    (hX_nn : ∀ i : Fin n, 0 ≤ᵐ[P] X i)
    (hX3 : ∀ i : Fin n, MemLp (X i) 3 P)
    (hXs2 : ∀ i : Fin n, MemLp (Xs i) 2 P)
    (hX_indep : iIndepFun X P)
    (hXs : ∀ i : Fin n, IsSizeBias P (X i) P (Xs i))
    (hXXs_indep : IndepFun (fun ω i ↦ Xs i ω) (fun ω i ↦ X i ω) P)
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω)) P)
    (hVar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let μ : ℝ := ∫ ω, S ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ (S ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / σ ^ 2 *
            Real.sqrt
              (2 / Real.pi *
                ∑ i : Fin n, (∫ ω, X i ω ∂P) ^ 2 * ProbabilityTheory.variance (X i) P) +
          1 / σ ^ 3 *
            ∑ i : Fin n, ((∫ ω, X i ω ^ 3 ∂P) - (∫ ω, X i ω ∂P) * ∫ ω, X i ω ^ 2 ∂P)) := by
  intro S μ σ W
  have hX2 : ∀ i : Fin n, MemLp (X i) 2 P := fun i ↦ (hX3 i).mono_exponent (by norm_num)
  have hX_int : ∀ i : Fin n, Integrable (X i) P := fun i ↦ (hX3 i).integrable (by norm_num)
  have hXs_int : ∀ i : Fin n, Integrable (Xs i) P := fun i ↦ (hXs2 i).integrable one_le_two
  have hS_meas : Measurable S := Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas i
  have hS_nn : 0 ≤ᵐ[P] S :=
    (eventually_countable_forall.mpr hX_nn).mono fun ω hω ↦ Finset.sum_nonneg fun i _ ↦ hω i
  have hS2 : MemLp S 2 P := memLp_finsetSum Finset.univ fun i _ ↦ hX2 i
  have hS_int : Integrable S P := hS2.integrable one_le_two
  have hμ_pos : 0 < μ := pos_integral_of_nonneg_of_variance_pos P hS_nn hS_int hVar
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar
  have hμ_sum : (∑ j : Fin n, ∫ ω, X j ω ∂P) = μ :=
    (integral_finsetSum Finset.univ fun j _ ↦ hX_int j).symm
  have hXs_indep_rest : ∀ i : Fin n,
      IndepFun (Xs i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) P := fun i ↦ by
    have hcomp := hXXs_indep.comp (measurable_pi_apply i)
      (Measurable.of_eval fun j : {j : Fin n // j ≠ i} ↦ measurable_pi_apply j.1)
    simpa only [Function.comp_def] using hcomp
  let Ss : Ω → ℝ := fun ω ↦ S ω - X (I ω) ω + Xs (I ω) ω
  have hSB_S : IsSizeBias P S P Ss :=
    sizeBias_sum_of_iIndepFun P hX_meas hX_nn hX_int hX_indep hXs hXs_indep_rest hI_meas hI_prob
      hI_indep (hμ_sum.symm ▸ hμ_pos)
  have hThm313 := sizeBias_wassersteinDist_le P P' hS_meas hS_nn hS2 hVar hSB_S hZ hZ_law
  dsimp only at hThm313
  let D : Ω → ℝ := fun ω ↦ Ss ω - S ω
  have hD_eq : D = fun ω ↦ Xs (I ω) ω - X (I ω) ω := funext fun ω ↦ by dsimp [D, Ss]; ring
  have hD_decomp : D = fun ω ↦
      ∑ i : Fin n, (I ⁻¹' {i}).indicator (fun ω' ↦ Xs i ω' - X i ω') ω := by
    funext ω; rw [hD_eq]; symm
    rw [Finset.sum_eq_single (I ω)]
    · simp
    · intro i _ hi; exact Set.indicator_of_notMem (by simpa using hi.symm) _
    · intro h; exact False.elim (h (Finset.mem_univ _))
  have hD_int : Integrable D P :=
    hD_decomp ▸ integrable_finsetSum Finset.univ fun i _ ↦
      ((hXs_int i).sub (hX_int i)).indicator (hI_meas (measurableSet_singleton i))
  have hD2_decomp : (fun ω ↦ D ω ^ 2) = fun ω ↦
      ∑ i : Fin n, (I ⁻¹' {i}).indicator (fun ω' ↦ (Xs i ω' - X i ω') ^ 2) ω := by
    funext ω
    have hd : D ω ^ 2 = (Xs (I ω) ω - X (I ω) ω) ^ 2 := by rw [hD_eq]
    rw [hd]; symm
    rw [Finset.sum_eq_single (I ω)]
    · simp
    · intro i _ hi; exact Set.indicator_of_notMem (by simpa using hi.symm) _
    · intro h; exact False.elim (h (Finset.mem_univ _))
  have hD2_term_int : ∀ i : Fin n,
      Integrable ((I ⁻¹' {i}).indicator (fun ω' ↦ (Xs i ω' - X i ω') ^ 2)) P :=
    fun i ↦ (((hXs2 i).sub (hX2 i)).integrable_sq).indicator (hI_meas (measurableSet_singleton i))
  have hD2_int : Integrable (fun ω ↦ D ω ^ 2) P :=
    hD2_decomp ▸ integrable_finsetSum Finset.univ fun i _ ↦ hD2_term_int i
  have hLInt_D2 : (∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P) = ENNReal.ofReal (∫ ω, D ω ^ 2 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hD2_int (Eventually.of_forall fun _ ↦ sq_nonneg _)).symm
  let VXXs : Ω → (Fin n → ℝ) × (Fin n → ℝ) := fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω)
  have hVXXs_meas : Measurable VXXs :=
    (Measurable.of_eval hX_meas).prodMk (Measurable.of_eval hXs_meas)
  have hTerm2_eval :
      μ * ∫ ω, D ω ^ 2 ∂P =
        ∑ i : Fin n, ((∫ ω, X i ω ^ 3 ∂P) - (∫ ω, X i ω ∂P) * ∫ ω, X i ω ^ 2 ∂P) := by
    rw [hD2_decomp, integral_finsetSum Finset.univ fun i _ ↦ hD2_term_int i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    let fI : Fin n → ℝ := ({i} : Set (Fin n)).indicator 1
    let gV : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p ↦ (p.2 i - p.1 i) ^ 2
    have hfI_meas : Measurable fI := measurable_one.indicator (measurableSet_singleton i)
    have hgV_meas : Measurable gV :=
      (((measurable_pi_apply i).comp measurable_snd).fun_sub
        ((measurable_pi_apply i).comp measurable_fst)).pow_const 2
    have hpt : (I ⁻¹' {i}).indicator (fun ω' ↦ (Xs i ω' - X i ω') ^ 2) =
        fun ω ↦ fI (I ω) * gV (VXXs ω) := by
      funext ω; by_cases hIω : I ω = i <;> simp [fI, gV, VXXs, hIω]
    have hfI_comp : (fun ω ↦ fI (I ω)) = (I ⁻¹' {i}).indicator (1 : Ω → ℝ) := by
      funext ω; by_cases hIω : I ω = i <;> simp [fI, hIω]
    have hint_i :
        ∫ ω, (I ⁻¹' {i}).indicator (fun ω' ↦ (Xs i ω' - X i ω') ^ 2) ω ∂P =
          ((∫ ω, X i ω ∂P) / μ) * ∫ ω, (Xs i ω - X i ω) ^ 2 ∂P := by
      rw [hpt,
        hI_indep.integral_fun_comp_mul_comp hI_meas.aemeasurable hVXXs_meas.aemeasurable
          hfI_meas.stronglyMeasurable.aestronglyMeasurable
          hgV_meas.stronglyMeasurable.aestronglyMeasurable,
        hfI_comp, integral_indicator_one (hI_meas (measurableSet_singleton i)), hI_prob i, hμ_sum]
    rw [hint_i, ← mul_assoc, mul_div_cancel₀ _ hμ_pos.ne']
    exact summand_mean_mul_sq_diff_eq P (hX_meas i) (hXs_meas i) (hX_nn i) (hX3 i) (hXs2 i)
      (hXs i) (hXXs_indep.comp (measurable_pi_apply i) (measurable_pi_apply i))
  let VX : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  have hVX_meas : Measurable VX := .of_eval hX_meas
  have hmS_le_mVX :
      MeasurableSpace.comap S inferInstance ≤ MeasurableSpace.comap VX inferInstance := by
    intro s hs
    rcases hs with ⟨B, hB, rfl⟩
    let sumFn : (Fin n → ℝ) → ℝ := fun v ↦ ∑ i : Fin n, v i
    have hsumFn_meas : Measurable sumFn :=
      Finset.measurable_fun_sum Finset.univ fun i _ ↦ measurable_pi_apply i
    exact ⟨sumFn ⁻¹' B, hsumFn_meas hB, rfl⟩
  have hEvar_mono :
      ProbabilityTheory.evariance (P[D | MeasurableSpace.comap S inferInstance]) P ≤
        ProbabilityTheory.evariance (P[D | MeasurableSpace.comap VX inferInstance]) P :=
    evariance_condExp_mono P hmS_le_mVX hVX_meas.comap_le hD_int
  let Y : Fin n → Ω → ℝ :=
    fun i ω ↦ ((∫ x, X i x ∂P) / μ) * ((∫ x, Xs i x ∂P) - X i ω)
  let g : Ω → ℝ := fun ω ↦ ∑ i : Fin n, Y i ω
  have hCond_ae : P[D | MeasurableSpace.comap VX inferInstance] =ᵐ[P] g := by
    have h0 := condExp_diff_vx_ae_eq P hX_meas hXs_meas hX_int hXs_int hXXs_indep hI_meas hI_prob
      hI_indep
    dsimp only at h0
    rw [hμ_sum] at h0
    rwa [hD_eq]
  have hY2 : ∀ i : Fin n, MemLp (Y i) 2 P := fun i ↦
    ((memLp_const (∫ x, Xs i x ∂P)).sub (hX2 i)).const_mul ((∫ x, X i x ∂P) / μ)
  have hg2 : MemLp g 2 P := memLp_finsetSum Finset.univ fun i _ ↦ hY2 i
  have hY_indep : iIndepFun Y P :=
    hX_indep.comp (fun i t ↦ ((∫ x, X i x ∂P) / μ) * ((∫ x, Xs i x ∂P) - t))
      (fun i ↦ (measurable_const.fun_sub measurable_id).const_mul ((∫ x, X i x ∂P) / μ))
  have hVar_g :
      ProbabilityTheory.variance g P =
        (∑ i : Fin n, (∫ ω, X i ω ∂P) ^ 2 * ProbabilityTheory.variance (X i) P) / μ ^ 2 := by
    have hg_sum : g = ∑ i ∈ Finset.univ, Y i := by ext ω; simp [g]
    rw [hg_sum, ProbabilityTheory.IndepFun.variance_sum (fun i _ ↦ hY2 i)
      (fun i _ j _ hij ↦ hY_indep.indepFun hij), Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp [Y]
    rw [ProbabilityTheory.variance_const_mul,
      ProbabilityTheory.variance_const_sub (hX_meas i).aestronglyMeasurable,
      div_pow, div_mul_eq_mul_div]
  have hEvar_le :
      ProbabilityTheory.evariance (P[D | MeasurableSpace.comap S inferInstance]) P ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal
          (Real.sqrt (∑ i : Fin n, (∫ ω, X i ω ∂P) ^ 2 * ProbabilityTheory.variance (X i) P) /
            μ) := by
    have hEvar_VX :
        ProbabilityTheory.evariance (P[D | MeasurableSpace.comap VX inferInstance]) P =
          ENNReal.ofReal (ProbabilityTheory.variance g P) := by
      rw [ProbabilityTheory.evariance_congr hCond_ae, ← ProbabilityTheory.ofReal_variance hg2]
    have hpow := ENNReal.rpow_le_rpow hEvar_mono (by positivity : (0 : ℝ) ≤ 1 / 2)
    rw [hEvar_VX,
      ENNReal.ofReal_rpow_of_nonneg (ProbabilityTheory.variance_nonneg g P) (by positivity),
      ← Real.sqrt_eq_rpow, hVar_g, Real.sqrt_div (Finset.sum_nonneg fun i _ ↦
        mul_nonneg (sq_nonneg _) (ProbabilityTheory.variance_nonneg _ _)),
      Real.sqrt_sq hμ_pos.le] at hpow
    exact hpow
  refine hThm313.trans ?_
  change ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) *
        ProbabilityTheory.evariance (P[D | MeasurableSpace.comap S inferInstance]) P ^ (1 / 2 : ℝ) +
      ENNReal.ofReal (μ / σ ^ 3) * ∫⁻ ω, ENNReal.ofReal (D ω ^ 2) ∂P ≤ _
  rw [hLInt_D2]
  exact ennreal_thm313_rhs_combine hμ_pos hσ_pos (integral_nonneg fun _ ↦ sq_nonneg _)
    hTerm2_eval hEvar_le

/-! ### Section 3: Self-Contained Example 3.8 Bound (`Ex3_8`) -/

private lemma sizeBias_indepSum_wassersteinDist_le_measurable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hX_meas : ∀ i : Fin n, Measurable (X i))
    (hX_nn : ∀ i : Fin n, 0 ≤ᵐ[P] X i)
    (hX3 : ∀ i : Fin n, MemLp (X i) 3 P)
    (hX_indep : iIndepFun X P)
    (hVar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let μ : ℝ := ∫ ω, S ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ (S ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / σ ^ 2 *
            Real.sqrt
              (2 / Real.pi *
                ∑ i : Fin n, (∫ ω, X i ω ∂P) ^ 2 * ProbabilityTheory.variance (X i) P) +
          1 / σ ^ 3 *
            ∑ i : Fin n, ((∫ ω, X i ω ^ 3 ∂P) - (∫ ω, X i ω ∂P) * ∫ ω, X i ω ^ 2 ∂P)) := by
  intro S μ σ W
  have hX_int : ∀ i : Fin n, Integrable (X i) P := fun i ↦ (hX3 i).integrable (by norm_num)
  have hS_nn : 0 ≤ᵐ[P] S :=
    (eventually_countable_forall.mpr hX_nn).mono fun ω hω ↦ Finset.sum_nonneg fun i _ ↦ hω i
  have hS_int : Integrable S P := integrable_finsetSum Finset.univ fun i _ ↦ hX_int i
  have hμ_pos : 0 < μ := pos_integral_of_nonneg_of_variance_pos P hS_nn hS_int hVar
  have hμ_sum : (∑ i : Fin n, ∫ ω, X i ω ∂P) = μ :=
    (integral_finsetSum Finset.univ fun i _ ↦ hX_int i).symm
  let Ω_ext : Type _ := (Ω × (Fin n → ℝ)) × Fin n
  let νs : Fin n → Measure ℝ := fun i ↦ summandSizeBiasLaw P (X i)
  have hνs_prob : ∀ i : Fin n, IsProbabilityMeasure (νs i) :=
    fun i ↦ isProbabilityMeasure_summandSizeBiasLaw P (hX_nn i) (hX_int i)
  let μS : Measure (Fin n → ℝ) := @Measure.pi (Fin n) (fun _ ↦ ℝ) _ _ νs
  have hμS_prob : IsProbabilityMeasure μS := by dsimp [μS]; infer_instance
  let wI : Fin n → ℝ := fun i ↦ (∫ ω, X i ω ∂P) / μ
  have hwI_nn : ∀ i : Fin n, 0 ≤ wI i :=
    fun i ↦ div_nonneg (integral_nonneg_of_ae (hX_nn i)) hμ_pos.le
  have hwI_sum : (∑ i : Fin n, wI i) = 1 := by
    dsimp [wI]; rw [← Finset.sum_div, hμ_sum, div_self hμ_pos.ne']
  let μI : Measure (Fin n) := meanIndexLaw wI
  have hμI_prob : IsProbabilityMeasure μI := isProbabilityMeasure_meanIndexLaw hwI_nn hwI_sum
  let Q : Measure Ω_ext := (P.prod μS).prod μI
  have hQ_prob : IsProbabilityMeasure Q := by dsimp [Q]; infer_instance
  let X_lift : Fin n → Ω_ext → ℝ := fun i p ↦ X i p.1.1
  let Xs_lift : Fin n → Ω_ext → ℝ := fun i p ↦ p.1.2 i
  let I_lift : Ω_ext → Fin n := fun p ↦ p.2
  have hπ1 : MeasurePreserving (fun p : Ω_ext ↦ p.1) Q (P.prod μS) := measurePreserving_fst
  have hπX : MeasurePreserving (fun p : Ω_ext ↦ p.1.1) Q P := measurePreserving_fst.comp hπ1
  have hπS : MeasurePreserving (fun p : Ω_ext ↦ p.1.2) Q μS := measurePreserving_snd.comp hπ1
  have hπI : MeasurePreserving I_lift Q μI := measurePreserving_snd
  have hid_X : ∀ i : Fin n, IdentDistrib (X_lift i) (X i) Q P := fun i ↦
    ⟨((hX_meas i).comp hπX.measurable).aemeasurable, (hX_meas i).aemeasurable, by
      change Q.map (X i ∘ fun p : Ω_ext ↦ p.1.1) = P.map (X i)
      rw [← Measure.map_map (hX_meas i) hπX.measurable, hπX.map_eq]⟩
  have hid_Xs : ∀ i : Fin n, IdentDistrib (Xs_lift i) id Q (νs i) := fun i ↦ by
    have hcomp : MeasurePreserving (Xs_lift i) Q (νs i) :=
      (measurePreserving_eval (μ := νs) i).comp hπS
    exact ⟨hcomp.measurable.aemeasurable, aemeasurable_id, by rw [hcomp.map_eq, Measure.map_id]⟩
  have hS_meas : Measurable S := Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas i
  have hid_sum : IdentDistrib (fun p : Ω_ext ↦ ∑ i : Fin n, X_lift i p) S Q P :=
    ⟨(hS_meas.comp hπX.measurable).aemeasurable, hS_meas.aemeasurable, by
      change Q.map (S ∘ fun p : Ω_ext ↦ p.1.1) = P.map S
      rw [← Measure.map_map hS_meas hπX.measurable, hπX.map_eq]⟩
  have hX_lift_meas : ∀ i : Fin n, Measurable (X_lift i) :=
    fun i ↦ (hX_meas i).comp (measurable_fst.comp measurable_fst)
  have hXs_lift_meas : ∀ i : Fin n, Measurable (Xs_lift i) :=
    fun i ↦ (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hI_lift_meas : Measurable I_lift := measurable_snd
  have hX_lift_nn : ∀ i : Fin n, 0 ≤ᵐ[Q] X_lift i := fun i ↦ by
    have hmap : ∀ᵐ y ∂(Q.map (X_lift i)), 0 ≤ y := by
      rw [(hid_X i).map_eq]
      exact (ae_map_iff (p := fun y : ℝ ↦ 0 ≤ y) (hX_meas i).aemeasurable measurableSet_Ici).mpr
        (hX_nn i)
    exact (ae_map_iff (p := fun y : ℝ ↦ 0 ≤ y) (hX_lift_meas i).aemeasurable
      measurableSet_Ici).mp hmap
  have hX_lift_3 : ∀ i : Fin n, MemLp (X_lift i) 3 Q :=
    fun i ↦ (hid_X i).symm.memLp_snd (hX3 i)
  have hXs_lift_2 : ∀ i : Fin n, MemLp (Xs_lift i) 2 Q :=
    fun i ↦ (hid_Xs i).symm.memLp_snd (memLp_two_id_summandSizeBiasLaw P (hX_nn i) (hX3 i))
  have hX_lift_indep : iIndepFun X_lift Q :=
    iIndepFun_comp_measurePreserving hπX hX_meas hX_indep
  have hXs_lift_sb : ∀ i : Fin n, IsSizeBias Q (X_lift i) Q (Xs_lift i) := fun i ↦
    (isSizeBias_summandSizeBiasLaw P (hX_nn i) (hX_int i)).congr_identDistrib
      (hid_X i).symm (hid_Xs i).symm
  have hXXs_lift_indep :
      IndepFun (fun p : Ω_ext ↦ fun i : Fin n ↦ Xs_lift i p)
        (fun p : Ω_ext ↦ fun i : Fin n ↦ X_lift i p) Q := by
    have hmX : Measurable (fun ω : Ω ↦ fun i : Fin n ↦ X i ω) := .of_eval hX_meas
    have hbase := (indepFun_prod (μ := P) (ν := μS) hmX (measurable_id : Measurable id)).symm
    exact indepFun_comp_measurePreserving hπ1 measurable_snd (hmX.comp measurable_fst) hbase
  have hI_lift_prob : ∀ i : Fin n,
      Q.real (I_lift ⁻¹' {i}) = (∫ p, X_lift i p ∂Q) / ∑ j : Fin n, ∫ p, X_lift j p ∂Q := fun i ↦ by
    have hpre : Q (I_lift ⁻¹' {i}) = μI {i} :=
      hπI.measure_preimage (measurableSet_singleton i).nullMeasurableSet
    have hsum_eq : (∑ j : Fin n, ∫ p, X_lift j p ∂Q) = μ := by
      rw [← hμ_sum]
      exact Finset.sum_congr rfl fun j _ ↦ (hid_X j).integral_eq
    rw [measureReal_def, hpre, ← measureReal_def, meanIndexLaw_real_singleton hwI_nn i,
      (hid_X i).integral_eq, hsum_eq]
  have hI_lift_indep :
      IndepFun I_lift (fun p : Ω_ext ↦ (fun i ↦ X_lift i p, fun i ↦ Xs_lift i p)) Q := by
    have hm_pair : Measurable (fun q : Ω × (Fin n → ℝ) ↦ (fun i ↦ X i q.1, fun i ↦ q.2 i)) :=
      (Measurable.of_eval fun i ↦ (hX_meas i).comp measurable_fst).prodMk
        (Measurable.of_eval fun i ↦ (measurable_pi_apply i).comp measurable_snd)
    exact (indepFun_prod (μ := P.prod μS) (ν := μI) hm_pair measurable_id).symm
  have hVar_lift : 0 < ProbabilityTheory.variance (fun p : Ω_ext ↦ ∑ i : Fin n, X_lift i p) Q := by
    rwa [hid_sum.variance_eq]
  have hBound := sizeBias_indepSum_wassersteinDist_le_of_coupling Q P' hX_lift_meas hXs_lift_meas
    hX_lift_nn hX_lift_3 hXs_lift_2 hX_lift_indep hXs_lift_sb hXXs_lift_indep hI_lift_meas
    hI_lift_prob hI_lift_indep hVar_lift hZ hZ_law
  dsimp only at hBound
  have hμ_lift : (∫ p : Ω_ext, (∑ i : Fin n, X_lift i p) ∂Q) = μ := hid_sum.integral_eq
  have hσ_lift :
      Real.sqrt (ProbabilityTheory.variance (fun p : Ω_ext ↦ ∑ i : Fin n, X_lift i p) Q) = σ := by
    rw [hid_sum.variance_eq]
  rw [hμ_lift, hσ_lift] at hBound
  have hW_map :
      Q.map (fun p : Ω_ext ↦ ((∑ i : Fin n, X_lift i p) - μ) / σ) = P.map W := by
    have hW_meas : Measurable W := (hS_meas.fun_sub measurable_const).div_const σ
    change Q.map (W ∘ fun p : Ω_ext ↦ p.1.1) = P.map W
    rw [← Measure.map_map hW_meas hπX.measurable, hπX.map_eq]
  rw [hW_map] at hBound
  have hMean_eq : ∀ i : Fin n, ∫ p, X_lift i p ∂Q = ∫ ω, X i ω ∂P :=
    fun i ↦ (hid_X i).integral_eq
  have hVar_i_eq : ∀ i : Fin n,
      ProbabilityTheory.variance (X_lift i) Q = ProbabilityTheory.variance (X i) P :=
    fun i ↦ (hid_X i).variance_eq
  have hSq_eq : ∀ i : Fin n, ∫ p, X_lift i p ^ 2 ∂Q = ∫ ω, X i ω ^ 2 ∂P :=
    fun i ↦ ((hid_X i).comp (measurable_id.pow_const 2)).integral_eq
  have hCube_eq : ∀ i : Fin n, ∫ p, X_lift i p ^ 3 ∂Q = ∫ ω, X i ω ^ 3 ∂P :=
    fun i ↦ ((hid_X i).comp (measurable_id.pow_const 3)).integral_eq
  simpa only [hMean_eq, hVar_i_eq, hSq_eq, hCube_eq] using hBound

/-- **Example 3.8** (`\label{ex71}`, `SteinIntro.tex:1349-1353`; Backlog item 9): Ross prints no
formula in Example 3.8 and leaves the derivation as an exercise; this bound is the project's
solution of that exercise, combining Corollary 3.15 (`\label{cor71}`), Theorem 3.13
(`\label{thm71}`), and Remark 3.4 under the independent size-bias coupling. Reading notes:
(1) nonnegativity (`0 ≤ᵐ[P] X i`) comes from Corollary 3.15's setting (size-bias requires
$X_i \ge 0$), not from the exercise's wording; (2) no formula is printed in Example 3.8, so the
right-hand side is the project's explicit evaluation of the exercise; (3) positivity of the sum
variance `0 < variance (∑ X_i) P` ($\sigma^2 > 0$) is a typing/well-definedness condition for
normalizing $W = (S - \mu)/\sigma$. -/
theorem sizeBias_indepSum_wassersteinDist_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ}
    (hX_nn : ∀ i : Fin n, 0 ≤ᵐ[P] X i)
    (hX3 : ∀ i : Fin n, MemLp (X i) 3 P)
    (hX_indep : iIndepFun X P)
    (hVar : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw) :
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let μ : ℝ := ∫ ω, S ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ (S ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / σ ^ 2 *
            Real.sqrt
              (2 / Real.pi *
                ∑ i : Fin n, (∫ ω, X i ω ∂P) ^ 2 * ProbabilityTheory.variance (X i) P) +
          1 / σ ^ 3 *
            ∑ i : Fin n, ((∫ ω, X i ω ^ 3 ∂P) - (∫ ω, X i ω ∂P) * ∫ ω, X i ω ^ 2 ∂P)) := by
  intro S μ σ W
  let Xm : Fin n → Ω → ℝ := fun i ↦ (hX3 i).aestronglyMeasurable.mk (X i)
  have hXm_meas : ∀ i : Fin n, Measurable (Xm i) :=
    fun i ↦ (hX3 i).aestronglyMeasurable.measurable_mk
  have hXm_ae : ∀ i : Fin n, X i =ᵐ[P] Xm i := fun i ↦ (hX3 i).aestronglyMeasurable.ae_eq_mk
  have hXm_nn : ∀ i : Fin n, 0 ≤ᵐ[P] Xm i :=
    fun i ↦ (hX_nn i).mp ((hXm_ae i).mono fun _ h1 h2 ↦ h1 ▸ h2)
  have hXm_3 : ∀ i : Fin n, MemLp (Xm i) 3 P := fun i ↦ (hX3 i).ae_eq (hXm_ae i)
  have hXm_indep : iIndepFun Xm P := hX_indep.congr hXm_ae
  have hSum_ae : S =ᵐ[P] fun ω ↦ ∑ i : Fin n, Xm i ω :=
    (eventually_countable_forall.mpr hXm_ae).mono fun ω hω ↦ Finset.sum_congr rfl fun i _ ↦ hω i
  have hVar_m : 0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, Xm i ω) P := by
    rwa [← ProbabilityTheory.variance_congr hSum_ae]
  have hBound := sizeBias_indepSum_wassersteinDist_le_measurable P P' hXm_meas hXm_nn hXm_3
    hXm_indep hVar_m hZ hZ_law
  dsimp only at hBound
  have hμ_m : (∫ ω, (∑ i : Fin n, Xm i ω) ∂P) = μ := integral_congr_ae hSum_ae.symm
  have hσ_m : Real.sqrt (ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, Xm i ω) P) = σ := by
    rw [ProbabilityTheory.variance_congr hSum_ae.symm]
  rw [hμ_m, hσ_m] at hBound
  have hW_map : P.map (fun ω ↦ ((∑ i : Fin n, Xm i ω) - μ) / σ) = P.map W := by
    refine Measure.map_congr (hSum_ae.symm.mono fun ω hω ↦ ?_)
    dsimp only at hω
    change ((∑ i : Fin n, Xm i ω) - μ) / σ = (S ω - μ) / σ
    rw [hω]
  rw [hW_map] at hBound
  have hMean_i : ∀ i : Fin n, ∫ ω, Xm i ω ∂P = ∫ ω, X i ω ∂P :=
    fun i ↦ integral_congr_ae (hXm_ae i).symm
  have hVar_i : ∀ i : Fin n,
      ProbabilityTheory.variance (Xm i) P = ProbabilityTheory.variance (X i) P :=
    fun i ↦ ProbabilityTheory.variance_congr (hXm_ae i).symm
  have hSq_i : ∀ i : Fin n, ∫ ω, Xm i ω ^ 2 ∂P = ∫ ω, X i ω ^ 2 ∂P :=
    fun i ↦ integral_congr_ae ((hXm_ae i).symm.mono fun _ h ↦ congrArg (· ^ 2) h)
  have hCube_i : ∀ i : Fin n, ∫ ω, Xm i ω ^ 3 ∂P = ∫ ω, X i ω ^ 3 ∂P :=
    fun i ↦ integral_congr_ae ((hXm_ae i).symm.mono fun _ h ↦ congrArg (· ^ 3) h)
  simpa only [hMean_i, hVar_i, hSq_i, hCube_i] using hBound

end SteinMethod
