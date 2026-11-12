/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.GeometricSums

/-!
# Section 5.2, Remark 5.6: Heterogeneous-Mean & Dependent Random Sums
Proves `rem5_6_part1`–`rem5_6_part3` (`SteinIntro.tex:2948-2951`; cf. `\cite{rope10}`).
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

private lemma map_eq_restrict_Ioo_rem56 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Ω → ℝ} (hU : MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P) :
    P.map U = volume.restrict (Ioo (0 : ℝ) 1) := by
  rw [hU.map_eq, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, inv_one,
    one_smul]
private lemma Icc_one_eq_insert_Ico {m : ℕ} (hm : 1 ≤ m) :
    Finset.Icc 1 m = insert m (Finset.Ico 1 m) := by
  ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
private lemma indicator_ite_mul {Ω : Type*} (p : Ω → Prop) [DecidablePred p] (g : Ω → ℝ) (ω : Ω) :
    {ω' | p ω'}.indicator g ω = (if p ω then 1 else 0) * g ω := by
  by_cases h : p ω
  · rw [indicator_of_mem (show ω ∈ {ω' | p ω'} from h)]; simp [h]
  · rw [indicator_of_notMem (show ω ∉ {ω' | p ω'} from h)]; simp [h]
private lemma integral_ite_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {p : Ω → Prop} [DecidablePred p] (hp : MeasurableSet {ω | p ω}) :
    ∫ ω, (if p ω then (1 : ℝ) else 0) ∂P = P.real {ω | p ω} := by
  rw [show (fun ω ↦ if p ω then (1 : ℝ) else 0) = {ω | p ω}.indicator 1 from
    funext fun ω ↦ by simpa using (indicator_ite_mul p 1 ω).symm]
  exact integral_indicator_one hp
private lemma aemeasurable_sum_fn {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (s : Finset ℕ)
    {X : ℕ → Ω → ℝ} (hX : ∀ i ∈ s, AEMeasurable (X i) P) :
    AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) P :=
  (Finset.aemeasurable_sum s hX).congr (Eventually.of_forall fun ω ↦ Finset.sum_apply ω s X)
private lemma integral_indep_slice {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → α} {V : Ω → β}
    {G : α × β → ℝ} (hU : AEMeasurable U P) (hV : AEMeasurable V P) (hInd : IndepFun U V P)
    (hGm : Measurable G) (hGi : Integrable (fun ω ↦ G (U ω, V ω)) P) :
    ∫ ω, G (U ω, V ω) ∂P = ∫ u, (∫ ω, G (u, V ω) ∂P) ∂(P.map U) := by
  have : IsProbabilityMeasure (P.map U) := (Measure.isProbabilityMeasure_map_iff hU).mpr ‹_›
  have : IsProbabilityMeasure (P.map V) := (Measure.isProbabilityMeasure_map_iff hV).mpr ‹_›
  have hGp : Integrable G ((P.map U).prod (P.map V)) := hInd.map_prod_eq_prod_map_map hU hV ▸
    (integrable_map_measure hGm.aestronglyMeasurable (hU.prodMk hV)).mpr hGi
  rw [← integral_map (hU.prodMk hV) hGm.aestronglyMeasurable,
    hInd.map_prod_eq_prod_map_map hU hV, integral_prod G hGp]
  exact integral_congr_ae (Eventually.of_forall fun u ↦ integral_map hV
    (hGm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
private lemma exists_nat_ge_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → ℕ}
    (hN : AEMeasurable N P) (hpos : ∀ᵐ ω ∂P, 1 ≤ N ω) :
    ∃ N₁ : Ω → ℕ, Measurable N₁ ∧ (∀ ω, 1 ≤ N₁ ω) ∧ N =ᵐ[P] N₁ :=
  ⟨fun ω ↦ max (hN.mk N ω) 1, hN.measurable_mk.max measurable_const, fun _ ↦ le_max_right _ 1, by
    filter_upwards [hN.ae_eq_mk, hpos] with ω h1 h2; rw [← h1, max_eq_left h2]⟩
private lemma exists_seq_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, 1 ≤ i → AEMeasurable (Y i) P) :
    ∃ Y₁ : ℕ → Ω → ℝ, (∀ i, Measurable (Y₁ i)) ∧ ∀ i, 1 ≤ i → Y i =ᵐ[P] Y₁ i :=
  ⟨fun i ↦ if hi : 1 ≤ i then (hY i hi).mk (Y i) else 0, fun i ↦ by
    by_cases hi : 1 ≤ i <;> simp only [hi, ↓reduceDIte]
    exacts [(hY i hi).measurable_mk, measurable_const],
   fun i hi ↦ by simp only [hi, ↓reduceDIte]; exact (hY i hi).ae_eq_mk⟩
private lemma exists_seq_nonneg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, 1 ≤ i → AEMeasurable (X i) P) (hnn : ∀ i, 1 ≤ i → 0 ≤ᵐ[P] X i) :
    ∃ X₁ : ℕ → Ω → ℝ, (∀ i, Measurable (X₁ i)) ∧ (∀ i ω, 0 ≤ X₁ i ω) ∧
      ∀ i, 1 ≤ i → X i =ᵐ[P] X₁ i := by
  obtain ⟨Y₁, hY₁_m, hY₁_ae⟩ := exists_seq_real hX
  exact ⟨fun i ω ↦ max (Y₁ i ω) 0, fun i ↦ (hY₁_m i).max measurable_const,
    fun _ _ ↦ le_max_right _ 0, fun i hi ↦ by
      filter_upwards [hY₁_ae i hi, hnn i hi] with ω h1 (h2 : 0 ≤ X i ω)
      rw [← h1, max_eq_left h2]⟩
private lemma abs_dep_equilibrium_sum_sub_le {X : ℕ → ℝ} (hX : ∀ i, 0 ≤ X i) {s : ℝ} (hs : 0 ≤ s)
    (Spre_m Xe_m : ℝ) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    |s * (Spre_m + Xe_m) - s * ∑ i ∈ Finset.Icc 1 n, X i| ≤
      s * (|(∑ i ∈ Finset.Ico 1 m, X i) - Spre_m| + |X m - Xe_m| +
        ∑ i ∈ Finset.Ioc (min n m) (max n m), X i) := by
  let mid := s * ((∑ i ∈ Finset.Ico 1 m, X i) + Xe_m)
  have h1 : |s * (Spre_m + Xe_m) - mid| = s * |(∑ i ∈ Finset.Ico 1 m, X i) - Spre_m| := by
    rw [show s * (Spre_m + Xe_m) - mid = s * (Spre_m - ∑ i ∈ Finset.Ico 1 m, X i) by ring,
      abs_mul, abs_of_nonneg hs, abs_sub_comm]
  have htri := abs_add_le (s * (Spre_m + Xe_m) - mid) (mid - s * ∑ i ∈ Finset.Icc 1 n, X i)
  rw [sub_add_sub_cancel] at htri; linarith [abs_equilibrium_sum_sub_le hX hs Xe_m hn hm]
private lemma lintegral_sum_indep_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X₁ : ℕ → Ω → ℝ} {N₁ M₁ : Ω → ℕ} (F : ℕ × ℕ → Finset ℕ)
    (pred : ℕ → ℕ × ℕ → Prop) [∀ k, DecidablePred (pred k)]
    (hsum : ∀ (g : ℕ → ℝ≥0∞) (q : ℕ × ℕ),
      ∑ i ∈ F q, g i = ∑' k : ℕ, if pred k q then g (k + 1) else 0)
    (hX₁_meas : ∀ i, Measurable (X₁ i)) (hX₁_nn : ∀ i ω, 0 ≤ X₁ i ω)
    (hX₁_int : ∀ i : ℕ, 1 ≤ i → Integrable (X₁ i) P) (hN₁_meas : Measurable N₁)
    (hM₁_meas : Measurable M₁) (hNM₁_indep : IndepFun (fun ω ↦ (N₁ ω, M₁ ω))
      (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X₁ i.1 ω) P) :
    ∫⁻ ω, ENNReal.ofReal (∑ i ∈ F (N₁ ω, M₁ ω), X₁ i ω) ∂P =
      ∫⁻ ω, ENNReal.ofReal (∑ i ∈ F (N₁ ω, M₁ ω), ∫ ω', X₁ i ω' ∂P) ∂P := by
  let I₁ := {i : ℕ // 1 ≤ i}; have hNM_m := hN₁_meas.prodMk hM₁_meas
  have hXv_m : Measurable (fun ω (i : I₁) ↦ X₁ i.1 ω) := measurable_pi_iff.mpr fun i ↦ hX₁_meas i.1
  let φ₁ : ℕ → ℕ × ℕ → ℝ≥0∞ := fun k q ↦ if pred k q then 1 else 0
  have hφ₁ : ∀ k, Measurable (φ₁ k) := fun _ ↦ Measurable.of_discrete
  have hpt (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (q : ℕ × ℕ) : ENNReal.ofReal (∑ i ∈ F q, g i) =
      ∑' k : ℕ, φ₁ k q * ENNReal.ofReal (g (k + 1)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hg i, hsum]
    exact tsum_congr fun k ↦ by dsimp only [φ₁]; split_ifs <;> simp
  have hmL : ∀ k, AEMeasurable (fun ω ↦ φ₁ k (N₁ ω, M₁ ω) * ENNReal.ofReal (X₁ (k + 1) ω)) P :=
    fun k ↦ (((hφ₁ k).comp hNM_m).mul (ENNReal.measurable_ofReal.comp (hX₁_meas _))).aemeasurable
  have hmR : ∀ k, AEMeasurable
      (fun ω ↦ φ₁ k (N₁ ω, M₁ ω) * ENNReal.ofReal (∫ ω', X₁ (k + 1) ω' ∂P)) P :=
    fun k ↦ (((hφ₁ k).comp hNM_m).mul measurable_const).aemeasurable
  rw [lintegral_congr fun ω ↦ hpt (fun i ↦ X₁ i ω) (fun i ↦ hX₁_nn i ω) _,
    lintegral_congr fun ω ↦ hpt _ (fun i ↦ integral_nonneg fun ω' ↦ hX₁_nn i ω') _,
    lintegral_tsum hmL, lintegral_tsum hmR]
  refine tsum_congr fun k ↦ ?_; let ik : I₁ := ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
  let φ₂ : (I₁ → ℝ) → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (z ik)
  have hφ₂ : Measurable φ₂ := ENNReal.measurable_ofReal.comp (measurable_pi_apply ik)
  have hl2 : ∫⁻ ω, (φ₂ ∘ fun ω (i : I₁) ↦ X₁ i.1 ω) ω ∂P =
      ENNReal.ofReal (∫ ω', X₁ (k + 1) ω' ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hX₁_int (k + 1) ik.2)
      (Eventually.of_forall fun ω ↦ hX₁_nn (k + 1) ω)).symm
  change (∫⁻ ω, (φ₁ k ∘ fun ω ↦ (N₁ ω, M₁ ω)) ω * (φ₂ ∘ fun ω (i : I₁) ↦ X₁ i.1 ω) ω ∂P) =
    ∫⁻ ω, (φ₁ k ∘ fun ω ↦ (N₁ ω, M₁ ω)) ω * ENNReal.ofReal (∫ ω', X₁ (k + 1) ω' ∂P) ∂P
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' ((hφ₁ k).comp hNM_m).aemeasurable
    (hφ₂.comp hXv_m).aemeasurable (hNM₁_indep.comp (hφ₁ k) hφ₂), hl2,
    lintegral_mul_const _ ((hφ₁ k).comp hNM_m)]

/-- **Remark 5.6, Part 1** (`SteinIntro.tex:2948-2951`): prefix increment-equilibrium coupling
bound for random sums with non-identical means and dependent summands. -/
theorem rem5_6_part1 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {X Spre Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ} {Z : Ω' → ℝ}
    (hX_aem : ∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) (hX_nn : ∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i)
    (hX_int : ∀ i : ℕ, 1 ≤ i → Integrable (X i) P) (hN_aem : AEMeasurable N P)
    (hM_aem : AEMeasurable M P) (hN_pos : ∀ᵐ ω ∂P, 1 ≤ N ω) (hM_pos : ∀ᵐ ω ∂P, 1 ≤ M ω)
    (hMeanSum_int : Integrable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) P)
    (hS_pos : 0 < ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) ∂P)
    (hM_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} =
      ((∫ ω', X m ω' ∂P) / ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) ∂P) *
        P.real {ω | m ≤ N ω})
    (hNM_indep : IndepFun (fun ω ↦ (N ω, M ω)) (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P)
    (hSpre_aem : ∀ m : ℕ, 1 ≤ m → AEMeasurable (Spre m) P)
    (hXe_aem : ∀ m : ℕ, 1 ≤ m → AEMeasurable (Xe m) P)
    (hM_pair_indep : ∀ m : ℕ, 1 ≤ m → IndepFun M (fun ω ↦ (Spre m ω, Xe m ω)) P)
    (hInc : ∀ m : ℕ, 1 ≤ m → ∀ h : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K h) →
      ∫ ω, (h (∑ i ∈ Finset.Icc 1 m, X i ω) - h (∑ i ∈ Finset.Ico 1 m, X i ω)) ∂P =
        (∫ ω', X m ω' ∂P) * ∫ ω, deriv h (Spre m ω + Xe m ω) ∂P)
    (hZ_aem : AEMeasurable Z P') (hZ_law : P'.map Z = stdExpLaw) :
    let μ := fun i ↦ ∫ ω', X i ω' ∂P; let S := ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), μ i) ∂P
    let W := fun ω ↦ S⁻¹ * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
    let We := fun ω ↦ S⁻¹ * (Spre (M ω) ω + Xe (M ω) ω)
    let errDep := ∫⁻ ω, ENNReal.ofReal |(∑ i ∈ Finset.Ico 1 (M ω), X i ω) - Spre (M ω) ω| ∂P
    let errEq := ∫⁻ ω, ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| ∂P
    let errIdx :=
      ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N ω) (M ω)) (max (N ω) (M ω)), μ i) ∂P
    Integrable W P ∧ (∫ ω, W ω ∂P = 1) ∧ IsEquilibrium P W P We ∧
      wassersteinDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal (2 / S) * (errDep + errEq + errIdx) := by
  dsimp only; let I₁ := {i : ℕ // 1 ≤ i}
  obtain ⟨N₁, hN₁_meas, hN₁_ge, hN_ae⟩ := exists_nat_ge_one hN_aem hN_pos
  obtain ⟨M₁, hM₁_meas, hM₁_ge, hM_ae⟩ := exists_nat_ge_one hM_aem hM_pos
  obtain ⟨X₁, hX₁_meas, hX₁_nn, hX_ae⟩ := exists_seq_nonneg hX_aem hX_nn
  obtain ⟨Spre₁, hSpre₁_meas, hSpre_ae⟩ := exists_seq_real hSpre_aem
  obtain ⟨Xe₁, hXe₁_meas, hXe_ae⟩ := exists_seq_real hXe_aem
  have hall_ae : ∀ᵐ ω ∂P, ∀ i, 1 ≤ i → X i ω = X₁ i ω ∧ Spre i ω = Spre₁ i ω ∧ Xe i ω = Xe₁ i ω :=
    (ae_all_iff.mpr fun i : I₁ ↦ (hX_ae i.1 i.2).and ((hSpre_ae i.1 i.2).and
      (hXe_ae i.1 i.2))).mono fun _ hω i hi ↦ hω ⟨i, hi⟩
  have hX₁_int : ∀ i, 1 ≤ i → Integrable (X₁ i) P := fun i hi ↦ (hX_int i hi).congr (hX_ae i hi)
  have hμ_eq : ∀ i, 1 ≤ i → ∫ ω', X₁ i ω' ∂P = ∫ ω', X i ω' ∂P :=
    fun i hi ↦ integral_congr_ae (hX_ae i hi).symm
  set μ := fun i ↦ ∫ ω', X i ω' ∂P; set S := ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), μ i) ∂P
  have hSinv_pos : 0 < S⁻¹ := inv_pos.mpr hS_pos
  have hMeanSum_ae : (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N ω), μ i) =ᵐ[P]
      fun ω ↦ ∑ i ∈ Finset.Icc 1 (N₁ ω), ∫ ω', X₁ i ω' ∂P := by
    filter_upwards [hN_ae] with ω hNω; rw [hNω]
    exact Finset.sum_congr rfl fun i hi ↦ (hμ_eq i (Finset.mem_Icc.mp hi).1).symm
  have hM₁_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M₁ ω = m} = (μ m / S) * P.real {ω | m ≤ N₁ ω} :=
    fun m hm ↦ by
      rw [measureReal_congr (s := {ω | M₁ ω = m}) (t := {ω | M ω = m})
          (hM_ae.symm.mono fun _ h ↦ propext (by simp [h])),
        measureReal_congr (s := {ω | m ≤ N₁ ω}) (t := {ω | m ≤ N ω})
          (hN_ae.symm.mono fun _ h ↦ propext (by simp [h])), hM_pmf m hm]
  have hNM₁_indep : IndepFun (fun ω ↦ (N₁ ω, M₁ ω)) (fun ω (i : I₁) ↦ X₁ i.1 ω) P :=
    hNM_indep.congr ((hN_ae.and hM_ae).mono fun _ ⟨h1, h2⟩ ↦ Prod.ext h1 h2)
      (hall_ae.mono fun _ hω ↦ funext fun i ↦ (hω i.1 i.2).1)
  have hM₁_pair_indep : ∀ m : ℕ, 1 ≤ m → IndepFun M₁ (fun ω ↦ (Spre₁ m ω, Xe₁ m ω)) P :=
    fun m hm ↦ (hM_pair_indep m hm).congr hM_ae
      (((hSpre_ae m hm).and (hXe_ae m hm)).mono fun _ ⟨h1, h2⟩ ↦ Prod.ext h1 h2)
  have hInc₁ : ∀ m : ℕ, 1 ≤ m → ∀ h : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K h) →
      ∫ ω, (h (∑ i ∈ Finset.Icc 1 m, X₁ i ω) - h (∑ i ∈ Finset.Ico 1 m, X₁ i ω)) ∂P =
        μ m * ∫ ω, deriv h (Spre₁ m ω + Xe₁ m ω) ∂P := fun m hm h hh ↦ by
    have hlhs : (fun ω ↦ h (∑ i ∈ Finset.Icc 1 m, X₁ i ω) - h (∑ i ∈ Finset.Ico 1 m, X₁ i ω)) =ᵐ[P]
        fun ω ↦ h (∑ i ∈ Finset.Icc 1 m, X i ω) - h (∑ i ∈ Finset.Ico 1 m, X i ω) := by
      filter_upwards [hall_ae] with ω hω
      rw [Finset.sum_congr rfl fun i hi ↦ (hω i (Finset.mem_Icc.mp hi).1).1.symm,
        Finset.sum_congr rfl fun i hi ↦ (hω i (Finset.mem_Ico.mp hi).1).1.symm]
    have hrhs : (fun ω ↦ deriv h (Spre₁ m ω + Xe₁ m ω)) =ᵐ[P]
        fun ω ↦ deriv h (Spre m ω + Xe m ω) :=
      ((hSpre_ae m hm).and (hXe_ae m hm)).mono fun _ ⟨h1, h2⟩ ↦ by dsimp only; rw [h1, h2]
    rw [integral_congr_ae hlhs, integral_congr_ae hrhs]; exact hInc m hm h hh
  let W := fun ω ↦ S⁻¹ * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
  let We := fun ω ↦ S⁻¹ * (Spre (M ω) ω + Xe (M ω) ω)
  let W₁ := fun ω ↦ S⁻¹ * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω
  let We₁ := fun ω ↦ S⁻¹ * (Spre₁ (M₁ ω) ω + Xe₁ (M₁ ω) ω)
  have hSum_meas : Measurable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) :=
    measurable_select_nat (fun n ↦ Finset.measurable_sum _ fun i _ ↦ hX₁_meas i) hN₁_meas
  have hWe₁_meas : Measurable We₁ := measurable_select_nat
    (fun m ↦ measurable_const.mul ((hSpre₁_meas m).add (hXe₁_meas m))) hM₁_meas
  have hSum_lint : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) ∂P =
      ENNReal.ofReal S := by
    have hIcc := lintegral_sum_indep_eq P (fun q ↦ Finset.Icc 1 q.1) (fun k q ↦ k + 1 ≤ q.1)
      (fun g q ↦ sum_Icc_one_eq_tsum_ite g q.1) hX₁_meas hX₁_nn hX₁_int hN₁_meas hM₁_meas hNM₁_indep
    dsimp only at hIcc; rw [hIcc, ← ofReal_integral_eq_lintegral_ofReal
      (hMeanSum_int.congr hMeanSum_ae)
      (Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ hX₁_nn i ω),
      integral_congr_ae hMeanSum_ae.symm]
  have hSum_int : Integrable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) P :=
    ⟨hSum_meas.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦
        Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω), hSum_lint]; exact ENNReal.ofReal_lt_top⟩
  have hW₁_int : Integrable W₁ P := hSum_int.const_mul S⁻¹
  have hW₁_mean : ∫ ω, W₁ ω ∂P = 1 := by
    have h1 := congrArg ENNReal.toReal ((ofReal_integral_eq_lintegral_ofReal hSum_int
      (Eventually.of_forall fun ω ↦ Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω)).trans hSum_lint)
    rw [ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω),
      ENNReal.toReal_ofReal hS_pos.le] at h1
    change ∫ ω, S⁻¹ * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω ∂P = 1
    rw [integral_const_mul, h1, inv_mul_cancel₀ hS_pos.ne']
  have hEqW₁ : IsEquilibrium P W₁ P We₁ := by
    refine ⟨Eventually.of_forall fun ω ↦ mul_nonneg hSinv_pos.le
      (Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω), hW₁_int, hWe₁_meas.aemeasurable,
      fun f ⟨K, hLip⟩ ↦ ?_⟩
    rw [hW₁_mean, one_mul]; let Sk : ℕ → Ω → ℝ := fun k ω ↦ S⁻¹ * ∑ i ∈ Finset.Icc 1 k, X₁ i ω
    have hSk_meas : ∀ k, Measurable (Sk k) :=
      fun _ ↦ measurable_const.mul (Finset.measurable_sum _ fun i _ ↦ hX₁_meas i)
    have hSk_int : ∀ k, Integrable (Sk k) P :=
      fun _ ↦ (integrable_finsetSum _ fun i hi ↦ hX₁_int i (Finset.mem_Icc.mp hi).1).const_mul S⁻¹
    have hSk_mono : ∀ {a b : ℕ} (hab : a ≤ b) (ω : Ω), Sk a ω ≤ Sk b ω := fun hab ω ↦
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right hab) fun i _ _ ↦ hX₁_nn i ω) hSinv_pos.le
    have hdf_bdd : ∀ y : ℝ, |deriv f y| ≤ K := fun y ↦ by
      simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := y) hLip
    let h_sc : ℝ → ℝ := fun u ↦ f (S⁻¹ * u)
    have hh_sc_lip : LipschitzWith (Real.toNNReal S⁻¹ * K) h_sc :=
      LipschitzWith.of_dist_le_mul fun u v ↦ by
        rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mul, Real.coe_toNNReal S⁻¹ hSinv_pos.le]
        have hd := hLip.dist_le_mul (S⁻¹ * u) (S⁻¹ * v)
        rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hSinv_pos] at hd; linarith
    have hterm_eq : ∀ k : ℕ,
        ∫ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun ω' ↦ f (Sk (k + 1) ω') - f (Sk k ω')) ω ∂P =
        ∫ ω, {ω' | M₁ ω' = k + 1}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω ∂P := fun k ↦ by
      set m : ℕ := k + 1; have hm : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le k)
      have h_inner : ∫ ω, (f (Sk (k + 1) ω) - f (Sk k ω)) ∂P =
          (μ m / S) * ∫ ω, deriv f (S⁻¹ * (Spre₁ m ω + Xe₁ m ω)) ∂P := by
        have h1 := hInc₁ m hm h_sc ⟨Real.toNNReal S⁻¹ * K, hh_sc_lip⟩
        have hlhs : (fun ω ↦ h_sc (∑ i ∈ Finset.Icc 1 m, X₁ i ω) -
            h_sc (∑ i ∈ Finset.Ico 1 m, X₁ i ω)) = fun ω ↦ f (Sk (k + 1) ω) - f (Sk k ω) := by
          ext ω; dsimp only [h_sc, Sk, m]; rw [Ico_one_succ]
        have hrhs : (fun ω ↦ deriv h_sc (Spre₁ m ω + Xe₁ m ω)) =
            fun ω ↦ S⁻¹ * deriv f (S⁻¹ * (Spre₁ m ω + Xe₁ m ω)) :=
          funext fun ω ↦ (deriv_comp_mul_left S⁻¹ f (Spre₁ m ω + Xe₁ m ω)).trans (smul_eq_mul _ _)
        rw [hlhs, hrhs, integral_const_mul] at h1; rw [h1, div_eq_mul_inv, mul_assoc]
      let α₁ : ℕ × ℕ → ℝ := fun q ↦ if m ≤ q.1 then 1 else 0
      let α₂ : ℕ → ℝ := fun q ↦ if q = m then 1 else 0
      let sum_n : ℕ → (I₁ → ℝ) → ℝ := fun n z ↦
        S⁻¹ * ∑ r : Fin n, z ⟨r.1 + 1, Nat.succ_le_succ (Nat.zero_le r.1)⟩
      let β₁ : (I₁ → ℝ) → ℝ := fun z ↦ f (sum_n (k + 1) z) - f (sum_n k z)
      let β₂ : ℝ × ℝ → ℝ := fun q ↦ deriv f (S⁻¹ * (q.1 + q.2))
      have hsum_n_meas : ∀ n, Measurable (sum_n n) :=
        fun _ ↦ measurable_const.mul (Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _)
      have hβ₁_meas : Measurable β₁ := (hLip.continuous.measurable.comp (hsum_n_meas (k + 1))).sub
        (hLip.continuous.measurable.comp (hsum_n_meas k))
      have hβ₂_meas : Measurable β₂ :=
        (measurable_deriv f).comp (measurable_const.mul (measurable_fst.add measurable_snd))
      have hsum_n_eq : ∀ n ω, sum_n n (fun i : I₁ ↦ X₁ i.1 ω) = Sk n ω := fun n ω ↦ by
        dsimp only [sum_n, Sk]; rw [sum_Icc_one_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
      have hlhs_prod : (fun ω ↦ {ω' | m ≤ N₁ ω'}.indicator
          (fun ω' ↦ f (Sk (k + 1) ω') - f (Sk k ω')) ω) =
          fun ω ↦ α₁ (N₁ ω, M₁ ω) * β₁ (fun i : I₁ ↦ X₁ i.1 ω) := by
        ext ω; rw [indicator_ite_mul]; dsimp only [α₁, β₁]; rw [hsum_n_eq, hsum_n_eq]
      have hrhs_prod : (fun ω ↦ {ω' | M₁ ω' = m}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω) =
          fun ω ↦ α₂ (M₁ ω) * β₂ (Spre₁ m ω, Xe₁ m ω) := by
        ext ω; rw [indicator_ite_mul]; dsimp only [α₂, β₂, We₁]; split_ifs with hω <;> simp [hω]
      have hβ₁_eq : (fun ω ↦ β₁ (fun i : I₁ ↦ X₁ i.1 ω)) = fun ω ↦ f (Sk (k + 1) ω) - f (Sk k ω) :=
        funext fun ω ↦ by dsimp only [β₁]; rw [hsum_n_eq, hsum_n_eq]
      rw [hlhs_prod, hrhs_prod, hNM₁_indep.integral_fun_comp_mul_comp
        (hN₁_meas.prodMk hM₁_meas).aemeasurable
        (measurable_pi_iff.mpr fun (i : I₁) ↦ hX₁_meas i.1).aemeasurable
        Measurable.of_discrete.aestronglyMeasurable hβ₁_meas.aestronglyMeasurable,
        (hM₁_pair_indep m hm).integral_fun_comp_mul_comp hM₁_meas.aemeasurable
        ((hSpre₁_meas m).prodMk (hXe₁_meas m)).aemeasurable
        Measurable.of_discrete.aestronglyMeasurable hβ₂_meas.aestronglyMeasurable,
        show ∫ ω, α₁ (N₁ ω, M₁ ω) ∂P = P.real {ω | m ≤ N₁ ω} from
          integral_ite_one P (measurableSet_le measurable_const hN₁_meas),
        show ∫ ω, α₂ (M₁ ω) ∂P = P.real {ω | M₁ ω = m} from
          integral_ite_one P (measurableSet_eq_fun hM₁_meas measurable_const), hβ₁_eq]
      change P.real {ω | m ≤ N₁ ω} * ∫ ω, (f (Sk (k + 1) ω) - f (Sk k ω)) ∂P =
        P.real {ω | M₁ ω = m} * ∫ ω, deriv f (S⁻¹ * (Spre₁ m ω + Xe₁ m ω)) ∂P
      rw [h_inner, ← mul_assoc, mul_comm (P.real {ω | m ≤ N₁ ω}) (μ m / S), ← hM₁_pmf m hm]
    let L_seq : ℕ → Ω → ℝ := fun n ω ↦ f (Sk (min n (N₁ ω)) ω) - f 0
    let R_seq : ℕ → Ω → ℝ := fun n ω ↦ {ω' | M₁ ω' ≤ n}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω
    have hL_sum : ∀ n ω, L_seq n ω = ∑ k ∈ Finset.range n,
        {ω' | k + 1 ≤ N₁ ω'}.indicator (fun ω' ↦ f (Sk (k + 1) ω') - f (Sk k ω')) ω := fun n ω ↦ by
      induction n with
      | zero => simp [L_seq, Sk]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← ih, indicator_ite_mul]; dsimp only [L_seq]; split_ifs with hn
        · rw [Nat.min_eq_left hn, Nat.min_eq_left (Nat.le_of_succ_le hn)]; ring
        · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]; ring
    have hR_sum : ∀ n ω, R_seq n ω = ∑ k ∈ Finset.range n,
        {ω' | M₁ ω' = k + 1}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω := fun n ω ↦ by
      induction n with
      | zero =>
        have := hM₁_ge ω; rw [Finset.sum_range_zero]; dsimp only [R_seq]
        rw [indicator_ite_mul]; split_ifs <;> first | omega | simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ← ih]; dsimp only [R_seq]
        rw [indicator_ite_mul, indicator_ite_mul, indicator_ite_mul]
        split_ifs <;> first | omega | ring
    have hLR_int_eq : ∀ n : ℕ, ∫ ω, L_seq n ω ∂P = ∫ ω, R_seq n ω ∂P := fun n ↦ by
      have hLt : ∀ k, Integrable (fun ω ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator
          (fun ω' ↦ f (Sk (k + 1) ω') - f (Sk k ω')) ω) P := fun k ↦
        ((integrable_comp_of_lipschitz (hSk_int (k + 1)) hLip).sub
          (integrable_comp_of_lipschitz (hSk_int k) hLip)).indicator (hN₁_meas measurableSet_Ici)
      have hRt : ∀ k, Integrable (fun ω ↦ {ω' | M₁ ω' = k + 1}.indicator
          (fun ω' ↦ deriv f (We₁ ω')) ω) P := fun k ↦
        (Integrable.of_bound ((measurable_deriv f).comp hWe₁_meas).aestronglyMeasurable K
          (Eventually.of_forall fun _ ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd _)).indicator
          (hM₁_meas (measurableSet_singleton (k + 1)))
      simp_rw [hL_sum n, hR_sum n]
      rw [integral_finsetSum _ fun k _ ↦ hLt k, integral_finsetSum _ fun k _ ↦ hRt k]
      exact Finset.sum_congr rfl fun k _ ↦ hterm_eq k
    have hL_tendsto : Tendsto (fun n : ℕ ↦ ∫ ω, L_seq n ω ∂P) atTop
        (𝓝 (∫ ω, (f (W₁ ω) - f 0) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω ↦ (K : ℝ) * W₁ ω)
        (fun n ↦ ((hLip.continuous.measurable.comp (measurable_select_nat
          (f := fun r ω ↦ Sk (min n r) ω) (fun r ↦ hSk_meas (min n r)) hN₁_meas)).sub
          measurable_const).aestronglyMeasurable) (hW₁_int.const_mul (K : ℝ))
        (fun n ↦ Eventually.of_forall fun ω ↦ ?_)
        (Eventually.of_forall fun ω ↦ tendsto_atTop_of_eventually_const (i₀ := N₁ ω) fun n hn ↦ ?_)
      · rw [Real.norm_eq_abs]; have hd := hLip.dist_le_mul (Sk (min n (N₁ ω)) ω) 0
        have hSn_nn : 0 ≤ Sk (min n (N₁ ω)) ω := by
          simpa [Sk] using hSk_mono (Nat.zero_le (min n (N₁ ω))) ω
        rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hSn_nn] at hd
        exact hd.trans (mul_le_mul_of_nonneg_left (hSk_mono (Nat.min_le_right _ _) ω) K.coe_nonneg)
      · dsimp only [L_seq]; rw [Nat.min_eq_right hn]
    have hR_tendsto : Tendsto (fun n : ℕ ↦ ∫ ω, R_seq n ω ∂P) atTop
        (𝓝 (∫ ω, deriv f (We₁ ω) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ (K : ℝ))
        (fun n ↦ (((measurable_deriv f).comp hWe₁_meas).indicator
          (hM₁_meas measurableSet_Iic)).aestronglyMeasurable) (integrable_const (K : ℝ))
        (fun n ↦ Eventually.of_forall fun ω ↦ ?_)
        (Eventually.of_forall fun ω ↦ tendsto_atTop_of_eventually_const (i₀ := M₁ ω) fun n hn ↦ ?_)
      · dsimp only [R_seq]; by_cases hω : M₁ ω ≤ n
        · rw [indicator_of_mem (show ω ∈ {ω' | M₁ ω' ≤ n} from hω), Real.norm_eq_abs]
          exact hdf_bdd _
        · simp [hω]
      · dsimp only [R_seq]; simp [hn]
    simp_rw [hLR_int_eq] at hL_tendsto; have hlim := tendsto_nhds_unique hL_tendsto hR_tendsto
    rw [integral_sub (integrable_comp_of_lipschitz hW₁_int hLip) (integrable_const (f 0)),
      integral_const, probReal_univ, one_smul] at hlim; exact hlim
  have hW_ae : W =ᵐ[P] W₁ := by
    filter_upwards [hN_ae, hall_ae] with ω hNω hω; dsimp only [W, W₁]; rw [hNω]; congr 1
    exact Finset.sum_congr rfl fun i hi ↦ (hω i (Finset.mem_Icc.mp hi).1).1
  have hWe_ae : We =ᵐ[P] We₁ := by
    filter_upwards [hM_ae, hall_ae] with ω hMω hω
    have hp := hω (M₁ ω) (hM₁_ge ω); dsimp only [We, We₁]; rw [hMω, hp.2.1, hp.2.2]
  refine ⟨hW₁_int.congr hW_ae.symm, by rw [integral_congr_ae hW_ae, hW₁_mean],
    hEqW₁.congr_identDistrib (IdentDistrib.of_ae_eq hW₁_int.aemeasurable hW_ae.symm)
      (IdentDistrib.of_ae_eq hEqW₁.2.2.1 hWe_ae.symm), ?_⟩
  rw [Measure.map_congr hW_ae]
  refine (wassersteinDist_le_two_mul_lintegral_equilibrium P P' (Eventually.of_forall fun ω ↦
    mul_nonneg hSinv_pos.le (Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω)) hW₁_int hW₁_mean
    hEqW₁ hZ_aem hZ_law).trans ?_
  have hDep_ae : (fun ω ↦ ENNReal.ofReal |(∑ i ∈ Finset.Ico 1 (M ω), X i ω) - Spre (M ω) ω|) =ᵐ[P]
      fun ω ↦ ENNReal.ofReal |(∑ i ∈ Finset.Ico 1 (M₁ ω), X₁ i ω) - Spre₁ (M₁ ω) ω| := by
    filter_upwards [hM_ae, hall_ae] with ω hMω hω; rw [hMω, (hω (M₁ ω) (hM₁_ge ω)).2.1,
      Finset.sum_congr rfl fun i hi ↦ (hω i (Finset.mem_Ico.mp hi).1).1]
  have hEq_ae : (fun ω ↦ ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω|) =ᵐ[P]
      fun ω ↦ ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| := by
    filter_upwards [hM_ae, hall_ae] with ω hMω hω
    have hp := hω (M₁ ω) (hM₁_ge ω); rw [hMω, hp.1, hp.2.2]
  have hIdx_ae : (fun ω ↦ ENNReal.ofReal
      (∑ i ∈ Finset.Ioc (min (N ω) (M ω)) (max (N ω) (M ω)), μ i)) =ᵐ[P] fun ω ↦ ENNReal.ofReal
        (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)), ∫ ω', X₁ i ω' ∂P) := by
    filter_upwards [hN_ae, hM_ae] with ω hNω hMω; rw [hNω, hMω]; congr 1
    refine Finset.sum_congr rfl fun i hi ↦ (hμ_eq i ?_).symm
    have := hM₁_ge ω; have := hN₁_ge ω; simp only [Finset.mem_Ioc] at hi; omega
  have hIoc_eq := lintegral_sum_indep_eq P (fun q ↦ Finset.Ioc (min q.1 q.2) (max q.1 q.2))
    (fun k q ↦ k + 1 ∈ Finset.Ioc (min q.1 q.2) (max q.1 q.2))
    (fun g q ↦ sum_Ioc_eq_tsum_ite g (min q.1 q.2) (max q.1 q.2))
    hX₁_meas hX₁_nn hX₁_int hN₁_meas hM₁_meas hNM₁_indep
  dsimp only at hIoc_eq
  rw [lintegral_congr_ae hDep_ae, lintegral_congr_ae hEq_ae, lintegral_congr_ae hIdx_ae, ← hIoc_eq]
  let fDep := fun ω ↦ ENNReal.ofReal |(∑ i ∈ Finset.Ico 1 (M₁ ω), X₁ i ω) - Spre₁ (M₁ ω) ω|
  let fEq := fun ω ↦ ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω|
  let fIoc := fun ω ↦
    ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)), X₁ i ω)
  have hfDep : Measurable fDep := ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    ((measurable_select_nat (f := fun m ω ↦ ∑ i ∈ Finset.Ico 1 m, X₁ i ω)
      (fun m ↦ Finset.measurable_sum _ fun i _ ↦ hX₁_meas i) hM₁_meas).sub
      (measurable_select_nat hSpre₁_meas hM₁_meas)))
  have hfEq : Measurable fEq := ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    ((measurable_select_nat hX₁_meas hM₁_meas).sub (measurable_select_nat hXe₁_meas hM₁_meas)))
  have hfIoc : Measurable fIoc := ENNReal.measurable_ofReal.comp <| measurable_select_nat
    (f := fun n ω ↦ ∑ i ∈ Finset.Ioc (min n (M₁ ω)) (max n (M₁ ω)), X₁ i ω)
    (fun n ↦ measurable_select_nat (f := fun m ω ↦ ∑ i ∈ Finset.Ioc (min n m) (max n m), X₁ i ω)
      (fun _ ↦ Finset.measurable_sum _ fun i _ ↦ hX₁_meas i) hM₁_meas) hN₁_meas
  have hpt : ∀ ω, ENNReal.ofReal |We₁ ω - W₁ ω| ≤
      ENNReal.ofReal S⁻¹ * (fDep ω + fEq ω + fIoc ω) := fun ω ↦ by
    refine (ENNReal.ofReal_le_ofReal (abs_dep_equilibrium_sum_sub_le (fun i ↦ hX₁_nn i ω)
      hSinv_pos.le (Spre₁ (M₁ ω) ω) (Xe₁ (M₁ ω) ω) (hN₁_ge ω) (hM₁_ge ω))).trans_eq ?_
    rw [ENNReal.ofReal_mul hSinv_pos.le, ENNReal.ofReal_add
      (add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω),
      ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  refine (mul_le_mul_of_nonneg_left (lintegral_mono hpt) zero_le).trans_eq ?_
  rw [lintegral_const_mul _ (by fun_prop : Measurable fun a ↦ fDep a + fEq a + fIoc a),
    lintegral_add_left (by fun_prop : Measurable fun a ↦ fDep a + fEq a),
    lintegral_add_left hfDep, ← mul_assoc, ← ENNReal.ofReal_mul zero_le_two, div_eq_mul_inv]

/-- **Remark 5.6, Part 2a** (`SteinIntro.tex:2948-2951`): joint $X_m$-size-biasing paired with
independent $\mathrm{Unif}(0, 1)$ satisfies the prefix increment-equilibrium identity. -/
theorem rem5_6_part2a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {Spre Xs U : Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (_hX_int : ∀ i : ℕ, 1 ≤ i → Integrable (X i) P) (hXm_nn : 0 ≤ᵐ[P] X m)
    (hSpre : AEMeasurable Spre P) (hXs : AEMeasurable Xs P) (_hXs_nn : 0 ≤ᵐ[P] Xs)
    (hU : MeasureTheory.pdf.IsUniform U (Ioo (0 : ℝ) 1) P)
    (hIndep : IndepFun U (fun ω ↦ (Spre ω, Xs ω)) P)
    (hSB : ∀ Φ : ℝ × ℝ → ℝ, Measurable Φ → (∃ C : ℝ, ∀ q, |Φ q| ≤ C) →
      ∫ ω, X m ω * Φ (∑ i ∈ Finset.Ico 1 m, X i ω, X m ω) ∂P =
        (∫ ω', X m ω' ∂P) * ∫ ω, Φ (Spre ω, Xs ω) ∂P)
    (h : ℝ → ℝ) (hh : ∃ K : ℝ≥0, LipschitzWith K h) :
    ∫ ω, (h (∑ i ∈ Finset.Icc 1 m, X i ω) - h (∑ i ∈ Finset.Ico 1 m, X i ω)) ∂P =
      (∫ ω', X m ω' ∂P) * ∫ ω, deriv h (Spre ω + U ω * Xs ω) ∂P := by
  rcases hh with ⟨K, hLip⟩
  have hdh_bdd : ∀ y : ℝ, |deriv h y| ≤ K := fun y ↦ by
    simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := y) hLip
  have hU_map := map_eq_restrict_Ioo_rem56 hU; set μU : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have : IsProbabilityMeasure μU :=
    hU_map ▸ (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).mpr ‹_›
  let G : ℝ × (ℝ × ℝ) → ℝ := fun p ↦ deriv h (p.2.1 + p.1 * p.2.2)
  have hG_meas : Measurable G := (measurable_deriv h).comp ((measurable_fst.comp measurable_snd).add
    (measurable_fst.mul (measurable_snd.comp measurable_snd)))
  let Φ : ℝ × ℝ → ℝ := fun q ↦ ∫ u, G (u, q) ∂μU
  have hΦ_meas : Measurable Φ := (hG_meas.stronglyMeasurable.integral_prod_left').measurable
  have hΦ_bdd : ∀ q : ℝ × ℝ, |Φ q| ≤ K := fun q ↦ by
    simpa [Φ, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (f := fun u ↦ G (u, q))
      (μ := μU) (C := (K : ℝ)) (Eventually.of_forall fun _ ↦ by
        rw [Real.norm_eq_abs]; exact hdh_bdd _)
  have hftc : ∀ s x : ℝ, 0 ≤ x → h (s + x) - h s = x * Φ (s, x) := fun s x hx ↦ by
    rcases hx.eq_or_lt with rfl | hx_pos; · simp
    let gs : ℝ → ℝ := fun t ↦ h (s + t)
    have hgs_lip : LipschitzWith K gs := LipschitzWith.of_dist_le_mul fun u v ↦ by
      simpa [gs, Real.dist_eq] using hLip.dist_le_mul (s + u) (s + v)
    have hder : ∀ u : ℝ, G (u, (s, x)) = deriv gs (u * x) :=
      fun u ↦ (deriv_comp_const_add_eq h s (u * x)).symm
    dsimp only [Φ, μU]; simp_rw [hder]
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_mul_right (deriv gs) hx_pos.ne', zero_mul, one_mul,
      smul_eq_mul, hgs_lip.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
    simp only [gs, add_zero]; field_simp [hx_pos.ne']
  have hlhs_ae : (fun ω ↦ h (∑ i ∈ Finset.Icc 1 m, X i ω) - h (∑ i ∈ Finset.Ico 1 m, X i ω)) =ᵐ[P]
      fun ω ↦ X m ω * Φ (∑ i ∈ Finset.Ico 1 m, X i ω, X m ω) := by
    filter_upwards [hXm_nn] with ω (hω : 0 ≤ X m ω)
    rw [Icc_one_eq_insert_Ico hm, Finset.sum_insert (by simp), add_comm]
    exact hftc (∑ i ∈ Finset.Ico 1 m, X i ω) (X m ω) hω
  have hpair_aem := hSpre.prodMk hXs
  have : IsProbabilityMeasure (P.map (fun ω ↦ (Spre ω, Xs ω))) :=
    (Measure.isProbabilityMeasure_map_iff hpair_aem).mpr ‹_›
  have hrhs_fub : ∫ ω, deriv h (Spre ω + U ω * Xs ω) ∂P = ∫ ω, Φ (Spre ω, Xs ω) ∂P := by
    change ∫ ω, G (U ω, (Spre ω, Xs ω)) ∂P = _
    rw [← integral_map (hU.aemeasurable.prodMk hpair_aem) hG_meas.aestronglyMeasurable,
      hIndep.map_prod_eq_prod_map_map hU.aemeasurable hpair_aem, hU_map,
      integral_prod_symm G (Integrable.of_bound hG_meas.aestronglyMeasurable K
        (Eventually.of_forall fun _ ↦ by rw [Real.norm_eq_abs]; exact hdh_bdd _)),
      integral_map hpair_aem hΦ_meas.aestronglyMeasurable]
  rw [integral_congr_ae hlhs_ae, hSB Φ hΦ_meas ⟨K, hΦ_bdd⟩, hrhs_fub]

/-- **Remark 5.6, Part 2b** (`SteinIntro.tex:2948-2951`): under $d$-dependence, local
size-biasing lifts to $S_{\mathrm{pre}}$ and cancels discrepancy outside the $d$-neighborhood. -/
theorem rem5_6_part2b {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {Vs Xs : Ω → ℝ} {m d : ℕ} (hm : 1 ≤ m)
    (hX_aem : ∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) (hXm_int : Integrable (X m) P)
    (hVs_aem : AEMeasurable Vs P) (hXs_aem : AEMeasurable Xs P)
    (hIndep_orig : IndepFun (fun ω ↦ ∑ i ∈ Finset.Ico 1 (m - d), X i ω)
      (fun ω ↦ (∑ i ∈ Finset.Ico (max 1 (m - d)) m, X i ω, X m ω)) P)
    (hIndep_sb : IndepFun (fun ω ↦ ∑ i ∈ Finset.Ico 1 (m - d), X i ω) (fun ω ↦ (Vs ω, Xs ω)) P)
    (hSB_loc : ∀ ψ : ℝ × ℝ → ℝ, Measurable ψ → (∃ C : ℝ, ∀ q, |ψ q| ≤ C) →
      ∫ ω, X m ω * ψ (∑ i ∈ Finset.Ico (max 1 (m - d)) m, X i ω, X m ω) ∂P =
        (∫ ω', X m ω' ∂P) * ∫ ω, ψ (Vs ω, Xs ω) ∂P) :
    let Spre := fun ω ↦ (∑ i ∈ Finset.Ico 1 (m - d), X i ω) + Vs ω
    (∀ Φ : ℝ × ℝ → ℝ, Measurable Φ → (∃ C : ℝ, ∀ q, |Φ q| ≤ C) →
      ∫ ω, X m ω * Φ (∑ i ∈ Finset.Ico 1 m, X i ω, X m ω) ∂P =
        (∫ ω', X m ω' ∂P) * ∫ ω, Φ (Spre ω, Xs ω) ∂P) ∧
      (∀ ω : Ω, |(∑ i ∈ Finset.Ico 1 m, X i ω) - Spre ω| =
        |(∑ i ∈ Finset.Ico (max 1 (m - d)) m, X i ω) - Vs ω|) := by
  dsimp only
  have hIco_union : Finset.Ico 1 m = Finset.Ico 1 (m - d) ∪ Finset.Ico (max 1 (m - d)) m := by
    ext i; simp only [Finset.mem_Ico, Finset.mem_union]; omega
  have hIco_disj : Disjoint (Finset.Ico 1 (m - d)) (Finset.Ico (max 1 (m - d)) m) :=
    Finset.disjoint_left.mpr fun i h1 h2 ↦ by simp only [Finset.mem_Ico] at h1 h2; omega
  have hsplit_sum : ∀ ω : Ω, ∑ i ∈ Finset.Ico 1 m, X i ω =
      (∑ i ∈ Finset.Ico 1 (m - d), X i ω) + ∑ i ∈ Finset.Ico (max 1 (m - d)) m, X i ω :=
    fun ω ↦ by rw [hIco_union, Finset.sum_union hIco_disj]
  refine ⟨fun Φ hΦ_meas ⟨C, hΦ_bdd⟩ ↦ ?_, fun ω ↦ by rw [hsplit_sum ω]; ring_nf⟩
  let Ufar := fun ω ↦ ∑ i ∈ Finset.Ico 1 (m - d), X i ω
  let Vloc := fun ω ↦ ∑ i ∈ Finset.Ico (max 1 (m - d)) m, X i ω
  have hUfar_aem : AEMeasurable Ufar P :=
    aemeasurable_sum_fn _ fun i hi ↦ hX_aem i (Finset.mem_Ico.mp hi).1
  have hVloc_aem : AEMeasurable Vloc P := aemeasurable_sum_fn _ fun i hi ↦
    hX_aem i ((le_max_left 1 _).trans (Finset.mem_Ico.mp hi).1)
  have hOrig_aem := hVloc_aem.prodMk (hX_aem m hm); have hSB_aem := hVs_aem.prodMk hXs_aem
  let G₂ := fun p : ℝ × (ℝ × ℝ) ↦ Φ (p.1 + p.2.1, p.2.2); let G₁ := fun p ↦ p.2.2 * G₂ p
  have hG₂_meas : Measurable G₂ := hΦ_meas.comp ((measurable_fst.add
    (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  have hG₁_meas : Measurable G₁ := (measurable_snd.comp measurable_snd).mul hG₂_meas
  have hG₁_int : Integrable (fun ω ↦ G₁ (Ufar ω, (Vloc ω, X m ω))) P :=
    (hXm_int.norm.const_mul C).mono' (hG₁_meas.comp_aemeasurable
      (hUfar_aem.prodMk hOrig_aem)).aestronglyMeasurable (Eventually.of_forall fun ω ↦ by
        dsimp only [G₁, G₂]; rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hΦ_bdd _) (abs_nonneg _))
  have hG₂_int : Integrable (fun ω ↦ G₂ (Ufar ω, (Vs ω, Xs ω))) P :=
    Integrable.of_bound (hG₂_meas.comp_aemeasurable (hUfar_aem.prodMk hSB_aem)).aestronglyMeasurable
      C (Eventually.of_forall fun _ ↦ by rw [Real.norm_eq_abs]; exact hΦ_bdd _)
  simp_rw [hsplit_sum]; change ∫ ω, G₁ (Ufar ω, (Vloc ω, X m ω)) ∂P =
    (∫ ω', X m ω' ∂P) * ∫ ω, G₂ (Ufar ω, (Vs ω, Xs ω)) ∂P
  rw [integral_indep_slice hUfar_aem hOrig_aem hIndep_orig hG₁_meas hG₁_int,
    integral_indep_slice hUfar_aem hSB_aem hIndep_sb hG₂_meas hG₂_int, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u ↦ hSB_loc (fun q ↦ Φ (u + q.1, q.2))
    (hΦ_meas.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
    ⟨C, fun q ↦ hΦ_bdd (u + q.1, q.2)⟩)

/-- **Remark 5.6, Part 2c** (`SteinIntro.tex:2948-2951`): mutually independent $L^2$ summands
with positive means $\mu_i > 0$ satisfy the explicit heterogeneous-mean second-moment bound. -/
theorem rem5_6_part2c {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    {X Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ} {Z : Ω' → ℝ}
    (hX_aem : ∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) (hX_nn : ∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i)
    (hX_L2 : ∀ i : ℕ, 1 ≤ i → MemLp (X i) 2 P) (hX_pos : ∀ i : ℕ, 1 ≤ i → 0 < ∫ ω, X i ω ∂P)
    (hX_indep : iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P) (hN_aem : AEMeasurable N P)
    (hM_aem : AEMeasurable M P) (hN_pos : ∀ᵐ ω ∂P, 1 ≤ N ω) (hM_pos : ∀ᵐ ω ∂P, 1 ≤ M ω)
    (hMeanSum_int : Integrable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) P)
    (hS_pos : 0 < ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) ∂P)
    (hM_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} =
      ((∫ ω', X m ω' ∂P) / ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) ∂P) *
        P.real {ω | m ≤ N ω})
    (hXe_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (Xe i))
    (hXe_indep : ∀ i : {i : ℕ // 1 ≤ i}, IndepFun (Xe i.1)
      (fun ω ↦ (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P)
    (hNM_indep : IndepFun (fun ω ↦ (N ω, M ω)) (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P)
    (hZ_aem : AEMeasurable Z P') (hZ_law : P'.map Z = stdExpLaw) :
    let μ := fun i ↦ ∫ ω', X i ω' ∂P; let S := ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), μ i) ∂P
    let W := fun ω ↦ S⁻¹ * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
    let errIdx :=
      ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N ω) (M ω)) (max (N ω) (M ω)), μ i) ∂P
    let err₁ := ENNReal.ofReal (2 / S) *
      ((∫⁻ ω, ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| ∂P) + errIdx)
    let err₂ := ENNReal.ofReal (2 / S) * ((∑' k : ℕ, P {ω | M ω = k + 1} *
      ENNReal.ofReal (μ (k + 1) + (∫ ω, X (k + 1) ω ^ 2 ∂P) / (2 * μ (k + 1)))) + errIdx)
    wassersteinDist (P.map W) (P'.map Z) ≤ err₁ ∧ err₁ ≤ err₂ := by
  dsimp only; let I₁ := {i : ℕ // 1 ≤ i}
  have hX_int : ∀ i, 1 ≤ i → Integrable (X i) P := fun i hi ↦ (hX_L2 i hi).integrable one_le_two
  have hXe_aem : ∀ i, 1 ≤ i → AEMeasurable (Xe i) P := fun i hi ↦ (hXe_eq i hi).2.2.1
  obtain ⟨M₁, hM₁_meas, hM₁_ge, hM_ae⟩ := exists_nat_ge_one hM_aem hM_pos
  obtain ⟨X₁, hX₁_meas, hX₁_nn, hX_ae⟩ := exists_seq_nonneg hX_aem hX_nn
  obtain ⟨Xe₁, hXe₁_meas, hXe_ae⟩ := exists_seq_real hXe_aem
  have hall_ae : ∀ᵐ ω ∂P, ∀ i, 1 ≤ i → X i ω = X₁ i ω ∧ Xe i ω = Xe₁ i ω :=
    (ae_all_iff.mpr fun i : I₁ ↦ (hX_ae i.1 i.2).and (hXe_ae i.1 i.2)).mono fun _ hω i hi ↦
      hω ⟨i, hi⟩
  have hX₁_indep : iIndepFun (fun i : I₁ ↦ X₁ i.1) P := hX_indep.congr fun i ↦ hX_ae i.1 i.2
  have hXe₁_indep : ∀ i : I₁,
      IndepFun (Xe₁ i.1) (fun ω ↦ (N ω, M₁ ω, fun j : {j : I₁ // j ≠ i} ↦ X₁ j.1.1 ω)) P :=
    fun i ↦ (hXe_indep i).congr (hXe_ae i.1 i.2) ((hM_ae.and hall_ae).mono
      fun _ ⟨hMω, hXω⟩ ↦ Prod.ext rfl (Prod.ext hMω (funext fun j ↦ (hXω j.1.1 j.1.2).1)))
  have hNM₁_indep : IndepFun (fun ω ↦ (N ω, M₁ ω)) (fun ω (i : I₁) ↦ X₁ i.1 ω) P :=
    hNM_indep.congr (hM_ae.mono fun _ h2 ↦ Prod.ext rfl h2)
      (hall_ae.mono fun _ hω ↦ funext fun i ↦ (hω i.1 i.2).1)
  have hXe₁_eq : ∀ i, 1 ≤ i → IsEquilibrium P (X₁ i) P (Xe₁ i) := fun i hi ↦
    (hXe_eq i hi).congr_identDistrib (IdentDistrib.of_ae_eq (hX_aem i hi) (hX_ae i hi))
      (IdentDistrib.of_ae_eq (hXe_aem i hi) (hXe_ae i hi))
  let Spre : ℕ → Ω → ℝ := fun m ω ↦ ∑ i ∈ Finset.Ico 1 m, X i ω
  let Spre₁ : ℕ → Ω → ℝ := fun m ω ↦ ∑ i ∈ Finset.Ico 1 m, X₁ i ω
  have hSpre_aem : ∀ m, 1 ≤ m → AEMeasurable (Spre m) P :=
    fun _ _ ↦ aemeasurable_sum_fn _ fun i hi ↦ hX_aem i (Finset.mem_Ico.mp hi).1
  have hSpre_ae : ∀ m, Spre m =ᵐ[P] Spre₁ m := fun _ ↦
    hall_ae.mono fun _ hω ↦ Finset.sum_congr rfl fun i hi ↦ (hω i (Finset.mem_Ico.mp hi).1).1
  have hSpre₁_indep_aux : ∀ (m : ℕ), 1 ≤ m → IndepFun M₁ (fun ω ↦ (Spre₁ m ω, Xe₁ m ω)) P ∧
      IndepFun (Spre₁ m) (X₁ m) P ∧ IndepFun (Spre₁ m) (Xe₁ m) P := fun m hm ↦ by
    set k : ℕ := m - 1; let im : I₁ := ⟨m, hm⟩; have hmk : m = k + 1 := by omega
    let idx_lt : Fin k → {j : I₁ // j ≠ im} := fun r ↦
      ⟨⟨r.1 + 1, Nat.succ_le_succ (Nat.zero_le r.1)⟩, fun heq ↦ by
        have hv : r.1 + 1 = m := congrArg Subtype.val heq; omega⟩
    let ψS : ({j : I₁ // j ≠ im} → ℝ) → ℝ := fun z ↦ ∑ r : Fin k, z (idx_lt r)
    have hψS_meas : Measurable ψS := Finset.measurable_sum _ fun _ _ ↦ measurable_pi_apply _
    have hcomp : Spre₁ m = ψS ∘ (fun ω (j : {j : I₁ // j ≠ im}) ↦ X₁ j.1.1 ω) := by
      ext ω; dsimp only [Spre₁, ψS, Function.comp_apply, idx_lt]
      rw [hmk, Ico_one_succ, sum_Icc_one_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    have hM₁_S : IndepFun M₁ (Spre₁ m) P :=
      (show Spre₁ m = (ψS ∘ fun (z : I₁ → ℝ) (j : {j : I₁ // j ≠ im}) ↦ z j.1) ∘
        (fun ω (i : I₁) ↦ X₁ i.1 ω) from hcomp) ▸ hNM₁_indep.comp measurable_snd
          (hψS_meas.comp (measurable_pi_iff.mpr fun j ↦ measurable_pi_apply j.1))
    have hMS_Xe : IndepFun (fun ω ↦ (M₁ ω, Spre₁ m ω)) (Xe₁ m) P :=
      (show (fun ω ↦ (M₁ ω, Spre₁ m ω)) =
        (fun t : ℕ × ℕ × ({j : I₁ // j ≠ im} → ℝ) ↦ (t.2.1, ψS t.2.2)) ∘
          (fun ω ↦ (N ω, M₁ ω, fun j : {j : I₁ // j ≠ im} ↦ X₁ j.1.1 ω)) from
        funext fun ω ↦ by simp [hcomp]) ▸ (hXe₁_indep im).symm.comp
          ((measurable_fst.comp measurable_snd).prodMk
            (hψS_meas.comp (measurable_snd.comp measurable_snd))) measurable_id
    exact ⟨indepFun_left_pair_of_indepFun_pair_right hM₁_meas
      (Finset.measurable_sum _ fun i _ ↦ hX₁_meas i) (hXe₁_meas m) hM₁_S hMS_Xe,
      hcomp ▸ ((iIndepFun_indepFun_compl hX₁_indep (fun i : I₁ ↦ hX₁_meas i.1) im).comp
        measurable_id hψS_meas).symm, hMS_Xe.comp measurable_snd measurable_id⟩
  have hM_pair_indep : ∀ m, 1 ≤ m → IndepFun M (fun ω ↦ (Spre m ω, Xe m ω)) P :=
    fun m hm ↦ (hSpre₁_indep_aux m hm).1.congr hM_ae.symm
      (((hSpre_ae m).symm.and (hXe_ae m hm).symm).mono fun _ ⟨h1, h2⟩ ↦ Prod.ext h1 h2)
  have hInc : ∀ m, 1 ≤ m → ∀ h : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K h) →
      ∫ ω, (h (∑ i ∈ Finset.Icc 1 m, X i ω) - h (∑ i ∈ Finset.Ico 1 m, X i ω)) ∂P =
        (∫ ω', X m ω' ∂P) * ∫ ω, deriv h (Spre m ω + Xe m ω) ∂P := fun m hm h ⟨K, hLip⟩ ↦ by
    obtain ⟨_, hInd_SX, hInd_SXe⟩ := hSpre₁_indep_aux m hm
    have hSpre₁_m : Measurable (Spre₁ m) := Finset.measurable_sum _ fun i _ ↦ hX₁_meas i
    have hdh_bdd : ∀ y : ℝ, |deriv h y| ≤ K := fun y ↦ by
      simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := y) hLip
    have hX₁m_int : Integrable (X₁ m) P := (hX_int m hm).congr (hX_ae m hm)
    let Φ₁ := fun q : ℝ × ℝ ↦ h (q.1 + q.2) - h q.1; let Φ₂ := fun q : ℝ × ℝ ↦ deriv h (q.1 + q.2)
    have hΦ₁_m : Measurable Φ₁ := (hLip.continuous.comp (continuous_fst.add
      continuous_snd)).measurable.sub (hLip.continuous.comp continuous_fst).measurable
    have hΦ₂_m : Measurable Φ₂ := (measurable_deriv h).comp (measurable_fst.add measurable_snd)
    have hΦ₁_int : Integrable (fun ω ↦ Φ₁ (Spre₁ m ω, X₁ m ω)) P :=
      (hX₁m_int.norm.const_mul (K : ℝ)).mono'
        (hΦ₁_m.comp (hSpre₁_m.prodMk (hX₁_meas m))).aestronglyMeasurable
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs]
          simpa [Φ₁, Real.dist_eq] using hLip.dist_le_mul (Spre₁ m ω + X₁ m ω) (Spre₁ m ω))
    have hΦ₂_int : Integrable (fun ω ↦ Φ₂ (Spre₁ m ω, Xe₁ m ω)) P :=
      Integrable.of_bound (hΦ₂_m.comp (hSpre₁_m.prodMk (hXe₁_meas m))).aestronglyMeasurable K
        (Eventually.of_forall fun _ ↦ by rw [Real.norm_eq_abs]; exact hdh_bdd _)
    have hslice : ∀ s : ℝ, ∫ ω, Φ₁ (s, X₁ m ω) ∂P =
        (∫ ω', X₁ m ω' ∂P) * ∫ ω, Φ₂ (s, Xe₁ m ω) ∂P := fun s ↦ by
      let gs : ℝ → ℝ := fun u ↦ h (s + u)
      have hgs_lip : LipschitzWith K gs := LipschitzWith.of_dist_le_mul fun u v ↦ by
        simpa [gs, Real.dist_eq] using hLip.dist_le_mul (s + u) (s + v)
      have heq := (hXe₁_eq m hm).2.2.2 gs ⟨K, hgs_lip⟩
      rw [show gs 0 = h s from by simp [gs],
        show (fun ω ↦ deriv gs (Xe₁ m ω)) = fun ω ↦ deriv h (s + Xe₁ m ω) from
          funext fun ω ↦ deriv_comp_const_add_eq h s (Xe₁ m ω)] at heq
      dsimp only [Φ₁, Φ₂]; rw [integral_sub (integrable_comp_of_lipschitz hX₁m_int hgs_lip)
        (integrable_const (h s)), integral_const, probReal_univ, one_smul]; exact heq
    have hlhs_ae : (fun ω ↦ h (∑ i ∈ Finset.Icc 1 m, X i ω) - h (∑ i ∈ Finset.Ico 1 m, X i ω)) =ᵐ[P]
        fun ω ↦ Φ₁ (Spre₁ m ω, X₁ m ω) := by
      filter_upwards [hSpre_ae m, hX_ae m hm] with ω h1 h2
      rw [Icc_one_eq_insert_Ico hm, Finset.sum_insert (by simp), add_comm]
      change h (Spre m ω + X m ω) - h (Spre m ω) = _; dsimp only [Φ₁]; rw [h1, h2]
    have hrhs_ae : (fun ω ↦ deriv h (Spre m ω + Xe m ω)) =ᵐ[P]
        fun ω ↦ Φ₂ (Spre₁ m ω, Xe₁ m ω) :=
      ((hSpre_ae m).and (hXe_ae m hm)).mono fun _ ⟨h1, h2⟩ ↦ by dsimp only [Φ₂]; rw [h1, h2]
    rw [integral_congr_ae hlhs_ae, integral_congr_ae hrhs_ae, integral_congr_ae (hX_ae m hm),
      integral_indep_slice hSpre₁_m.aemeasurable (hX₁_meas m).aemeasurable hInd_SX hΦ₁_m hΦ₁_int,
      integral_indep_slice hSpre₁_m.aemeasurable (hXe₁_meas m).aemeasurable hInd_SXe hΦ₂_m hΦ₂_int,
      ← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall hslice)
  have h1 := (rem5_6_part1 P P' hX_aem hX_nn hX_int hN_aem hM_aem hN_pos hM_pos hMeanSum_int
    hS_pos hM_pmf hNM_indep hSpre_aem hXe_aem hM_pair_indep hInc hZ_aem hZ_law).2.2.2
  rw [show (∫⁻ ω, ENNReal.ofReal |(∑ i ∈ Finset.Ico 1 (M ω), X i ω) - Spre (M ω) ω| ∂P) = 0 by
    simp [Spre], zero_add] at h1
  refine ⟨h1, mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) zero_le⟩
  set μ := fun i ↦ ∫ ω', X i ω' ∂P
  rw [lintegral_congr_ae ((hM_ae.and hall_ae).mono fun ω ⟨hMω, hω⟩ ↦ by
    have hp := hω (M₁ ω) (hM₁_ge ω)
    change ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| = ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω|
    rw [hMω, hp.1, hp.2])]
  have hXe_props : ∀ k, (0 ≤ᵐ[P] Xe₁ (k + 1)) ∧ ∫⁻ ω, ENNReal.ofReal (Xe₁ (k + 1) ω) ∂P =
      ENNReal.ofReal ((∫ ω, X (k + 1) ω ^ 2 ∂P) / (2 * μ (k + 1))) := fun k ↦ by
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hμ_eq : ∫ ω, X₁ (k + 1) ω ∂P = μ (k + 1) := integral_congr_ae (hX_ae (k + 1) hk1).symm
    obtain ⟨hXe_nn, hXe_int, hXe_mean⟩ := integrable_and_integral_equilibrium_of_memLp_two P P
      (Eventually.of_forall fun ω ↦ hX₁_nn (k + 1) ω) ((hX_L2 (k + 1) hk1).ae_eq (hX_ae _ hk1))
      (by rw [hμ_eq]; exact hX_pos (k + 1) hk1) (hXe₁_eq (k + 1) hk1)
    have hsq_eq : ∫ ω, X₁ (k + 1) ω ^ 2 ∂P = ∫ ω, X (k + 1) ω ^ 2 ∂P :=
      integral_congr_ae ((hX_ae (k + 1) hk1).symm.mono fun ω hω ↦ by dsimp only; rw [hω])
    exact ⟨hXe_nn, by rw [← ofReal_integral_eq_lintegral_ofReal hXe_int hXe_nn, hXe_mean, hsq_eq,
      hμ_eq]⟩
  have hae_tri : ∀ᵐ ω ∂P, ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| ≤
      ENNReal.ofReal (X₁ (M₁ ω) ω) + ENNReal.ofReal (Xe₁ (M₁ ω) ω) := by
    filter_upwards [ae_all_iff.mpr fun k : ℕ ↦ (hXe_props k).1] with ω hω
    have hm1 := hM₁_ge ω; have hsub : M₁ ω - 1 + 1 = M₁ ω := by omega
    have h1 := hX₁_nn (M₁ ω) ω; have h2 : 0 ≤ Xe₁ (M₁ ω) ω := hsub ▸ hω (M₁ ω - 1)
    exact (ENNReal.ofReal_le_ofReal ((abs_sub _ _).trans_eq
      (by rw [abs_of_nonneg h1, abs_of_nonneg h2]))).trans_eq (ENNReal.ofReal_add h1 h2)
  have hMX_indep : ∀ k, IndepFun M₁ (X₁ (k + 1)) P := fun k ↦ hNM₁_indep.comp measurable_snd
    (measurable_pi_apply (X := fun _ : I₁ ↦ ℝ) ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩)
  have hMXe_indep : ∀ k, IndepFun M₁ (Xe₁ (k + 1)) P := fun k ↦
    (hXe₁_indep ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩).symm.comp
      (measurable_fst.comp measurable_snd) measurable_id
  have hMeasX : Measurable (fun ω ↦ ENNReal.ofReal (X₁ (M₁ ω) ω)) :=
    ENNReal.measurable_ofReal.comp (measurable_select_nat hX₁_meas hM₁_meas)
  refine (lintegral_mono_ae hae_tri).trans_eq ?_
  rw [lintegral_add_left hMeasX,
    lintegral_ofReal_select_nat_eq_tsum P hM₁_meas hM₁_ge hX₁_meas hMX_indep,
    lintegral_ofReal_select_nat_eq_tsum P hM₁_meas hM₁_ge hXe₁_meas hMXe_indep, ← ENNReal.tsum_add]
  refine tsum_congr fun k ↦ ?_; have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  rw [measure_congr (s := {ω | M₁ ω = k + 1}) (t := {ω | M ω = k + 1})
      (hM_ae.symm.mono fun _ h ↦ propext (by simp [h])),
    ← ofReal_integral_eq_lintegral_ofReal ((hX_int (k + 1) hk1).congr (hX_ae _ hk1))
      (Eventually.of_forall fun ω ↦ hX₁_nn (k + 1) ω),
    integral_congr_ae (hX_ae (k + 1) hk1).symm, (hXe_props k).2, ← mul_add, ← ENNReal.ofReal_add
      (hX_pos (k + 1) hk1).le (div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
        (mul_nonneg zero_le_two (hX_pos (k + 1) hk1).le))]

/-- **Remark 5.6, Part 3** (`SteinIntro.tex:2948-2951`): strict non-vacuity witness with
dependent $(X_1, X_2)$ and unequal means $\mathbb{E}[X_1] = 1 / 2 \ne 1 = \mathbb{E}[X_2]$. -/
theorem rem5_6_part3 :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X Spre Xe : ℕ → Ω → ℝ) (N M : Ω → ℕ),
      (∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) ∧ (∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i) ∧
      (∀ i : ℕ, 1 ≤ i → Integrable (X i) P) ∧ AEMeasurable N P ∧ AEMeasurable M P ∧
      (∀ᵐ ω ∂P, 1 ≤ N ω) ∧ (∀ᵐ ω ∂P, 1 ≤ M ω) ∧
      Integrable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) P ∧
      0 < ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) ∂P ∧
      (∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} =
        ((∫ ω', X m ω' ∂P) / ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) ∂P) *
          P.real {ω | m ≤ N ω}) ∧
      IndepFun (fun ω ↦ (N ω, M ω)) (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P ∧
      (∀ m : ℕ, 1 ≤ m → AEMeasurable (Spre m) P) ∧ (∀ m : ℕ, 1 ≤ m → AEMeasurable (Xe m) P) ∧
      (∀ m : ℕ, 1 ≤ m → IndepFun M (fun ω ↦ (Spre m ω, Xe m ω)) P) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ h : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K h) →
        ∫ ω, (h (∑ i ∈ Finset.Icc 1 m, X i ω) - h (∑ i ∈ Finset.Ico 1 m, X i ω)) ∂P =
          (∫ ω', X m ω' ∂P) * ∫ ω, deriv h (Spre m ω + Xe m ω) ∂P) ∧
      ∫ ω, X 1 ω ∂P ≠ ∫ ω, X 2 ω ∂P ∧ ¬ IndepFun (X 1) (X 2) P := by
  let P : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have hP_prob : IsProbabilityMeasure P := by
    rw [isProbabilityMeasure_iff, Measure.restrict_apply_univ, Real.volume_Ioo]; simp
  let A : Set ℝ := Iio (1 / 2 : ℝ); have hA_meas : MeasurableSet A := measurableSet_Iio
  have hPA_real : P.real A = 1 / 2 := by
    rw [measureReal_def, Measure.restrict_apply hA_meas, show A ∩ Ioo (0 : ℝ) 1 =
      Ioo (0 : ℝ) (1 / 2) from Set.ext fun x ↦ ⟨fun ⟨h1, h2, _⟩ ↦ ⟨h2, h1⟩,
        fun ⟨h1, h2⟩ ↦ ⟨h2, h1, by linarith⟩⟩, Real.volume_Ioo]; norm_num
  let B : ℝ → ℝ := A.indicator 1; have hB_m : Measurable B := measurable_const.indicator hA_meas
  let c : ℕ → ℝ := fun i ↦ if i = 1 then 1 else 2
  have hc_nn : ∀ i, 0 ≤ c i := fun i ↦ by dsimp only [c]; split_ifs <;> norm_num
  let X : ℕ → ℝ → ℝ := fun i ω ↦ c i * B ω
  have hX_meas : ∀ i, Measurable (X i) := fun _ ↦ measurable_const.mul hB_m
  have hX_int : ∀ i, Integrable (X i) P :=
    fun i ↦ ((integrable_const (1 : ℝ)).indicator hA_meas).const_mul (c i)
  have hX_nn : ∀ i ω, 0 ≤ X i ω :=
    fun i ω ↦ mul_nonneg (hc_nn i) (indicator_nonneg (fun _ _ ↦ zero_le_one) ω)
  have hX_mean : ∀ i, ∫ ω, X i ω ∂P = c i * (1 / 2) := fun i ↦ by
    change ∫ ω, c i * B ω ∂P = _; rw [integral_const_mul, integral_indicator_one hA_meas, hPA_real]
  have hU_unif : MeasureTheory.pdf.IsUniform (id : ℝ → ℝ) (Ioo (0 : ℝ) 1) P :=
    ⟨measurable_id.aemeasurable, by
      rw [Measure.map_id, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
        inv_one, one_smul]⟩
  let Spre : ℕ → ℝ → ℝ := fun m _ ↦ ∑ i ∈ Finset.Ico 1 m, c i
  let Xe : ℕ → ℝ → ℝ := fun m ω ↦ ω * c m; let N : ℝ → ℕ := fun _ ↦ 1; let M : ℝ → ℕ := fun _ ↦ 1
  have hS_val : ∫ ω, (∑ i ∈ Finset.Icc 1 (N ω), ∫ ω', X i ω' ∂P) ∂P = 1 / 2 := by
    simp [N, hX_mean 1, c]
  refine ⟨ℝ, inferInstance, P, hP_prob, X, Spre, Xe, N, M,
    fun i _ ↦ (hX_meas i).aemeasurable, fun i _ ↦ Eventually.of_forall (hX_nn i),
    fun i _ ↦ hX_int i, measurable_const.aemeasurable, measurable_const.aemeasurable,
    Eventually.of_forall fun _ ↦ le_rfl, Eventually.of_forall fun _ ↦ le_rfl, integrable_const _,
    by rw [hS_val]; norm_num, ?_, indepFun_const_left (1, 1) _,
    fun _ _ ↦ measurable_const.aemeasurable, (fun _ _ ↦ (measurable_id.mul
      measurable_const).aemeasurable), fun _ _ ↦ indepFun_const_left 1 _, ?_,
    by rw [hX_mean 1, hX_mean 2]; dsimp [c]; norm_num, ?_⟩
  · intro m _; rw [hS_val, hX_mean m]; by_cases hm1 : m = 1
    · subst hm1; rw [show {ω : ℝ | M ω = 1} = univ from Set.ext fun _ ↦ by simp [M],
        show {ω : ℝ | 1 ≤ N ω} = univ from Set.ext fun _ ↦ by simp [N], probReal_univ]
      dsimp only [c]; norm_num
    · rw [show {ω : ℝ | M ω = m} = ∅ from Set.ext fun _ ↦ by simp [M, Ne.symm hm1],
        show {ω : ℝ | m ≤ N ω} = ∅ from Set.ext fun _ ↦ by simp [N]; omega, measureReal_empty,
        mul_zero]
  · intro m hm h hh
    refine rem5_6_part2a P hm (fun i _ ↦ hX_int i) (Eventually.of_forall (hX_nn m))
      measurable_const.aemeasurable measurable_const.aemeasurable
      (Eventually.of_forall fun _ ↦ hc_nn m) hU_unif
      (indepFun_const_right id (∑ i ∈ Finset.Ico 1 m, c i, c m)) (fun Φ _ _ ↦ ?_) h hh
    have hpt : (fun ω ↦ X m ω * Φ (∑ i ∈ Finset.Ico 1 m, X i ω, X m ω)) =
        A.indicator (fun _ ↦ c m * Φ (∑ i ∈ Finset.Ico 1 m, c i, c m)) := by
      ext ω; by_cases hω : ω ∈ A
      · have hB1 : B ω = 1 := indicator_of_mem hω _
        rw [indicator_of_mem hω, show ∑ i ∈ Finset.Ico 1 m, X i ω = ∑ i ∈ Finset.Ico 1 m, c i from
          Finset.sum_congr rfl fun i _ ↦ by simp [X, hB1]]; simp [X, hB1]
      · have hB0 : B ω = 0 := indicator_of_notMem hω _; rw [indicator_of_notMem hω]; simp [X, hB0]
    rw [hpt, integral_indicator_const _ hA_meas, smul_eq_mul, hPA_real, hX_mean m, integral_const,
      probReal_univ, one_smul]; ring
  · intro hInd
    have hpre : ∀ j, (j = 1 ∨ j = 2) → X j ⁻¹' Iic (0 : ℝ) = Aᶜ := fun j hj ↦ by
      ext ω; simp only [mem_preimage, mem_Iic, mem_compl_iff]; by_cases hω : ω ∈ A
      · have hB1 : B ω = 1 := indicator_of_mem hω _
        rcases hj with rfl | rfl <;> simp [X, c, hB1, hω]
      · have hB0 : B ω = 0 := indicator_of_notMem hω _; simp [X, hB0, hω]
    have hmul := (indepFun_iff_measure_inter_preimage_eq_mul.mp hInd)
      (Iic 0) (Iic 0) measurableSet_Iic measurableSet_Iic
    rw [hpre 1 (Or.inl rfl), hpre 2 (Or.inr rfl), inter_self] at hmul
    have htr : (P Aᶜ).toReal = 1 / 2 := by
      have hc := probReal_compl_eq_one_sub (μ := P) hA_meas; rw [hPA_real, measureReal_def] at hc
      linarith
    rw [← ENNReal.ofReal_toReal (measure_ne_top P Aᶜ), htr,
      ← ENNReal.ofReal_mul (by norm_num)] at hmul
    have hreal := congrArg ENNReal.toReal hmul; norm_num at hreal

end SteinMethod
