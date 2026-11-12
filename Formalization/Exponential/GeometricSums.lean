/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.GeometricSumsAux

/-!
# Section 5.2: Geometric Sums (`Formalization.Exponential.GeometricSums`)

Section 5.2 results (`SteinIntro.tex:2912-2984`):
- `thm5_7_corrected_minimal` & `thm5_7_corrected` (`Thm5_7_corrected`, `\label{thm1710}`,
  eqs. `(5.4)`–`(5.6)`, `SteinIntro.tex:2915-2929, 2952-2984`; `ISSUE-5.7`, `DEFINITIONS.md` §5.3,
  `D5-1`): Wasserstein exponential approximation bound for geometric-like random sums
  $W = p \sum_{i=1}^N X_i$.
- `rem5_5` (`Rem5_5`, `SteinIntro.tex:2931-2947`): size-bias uniform characterization of $M$,
  $M = N$ for $N \sim \mathrm{Ge}(p)$, and exact $\mathrm{Exp}(1)$ law for exponential summands.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-- **Theorem 5.7, corrected (minimal independence hypotheses)** (`\label{thm1710}`, eqs.
`(5.4)`–`(5.6)`, `SteinIntro.tex:2915-2929, 2952-2984`; `ISSUE-5.7`, `DEFINITIONS.md` §5.3,
`D5-1`): Wasserstein exponential approximation bound for geometric-like random sums
$W = p \sum_{i=1}^N X_i$ under the printed joint independence of $X_i^e$ from
$(N, M, (X_j)_{j \ne i})$ plus $(N, M) \perp (X_i)_{i \ge 1}$. -/
theorem thm5_7_corrected_minimal
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {X Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ} {Z : Ω' → ℝ}
    (hp₀ : 0 < p) (_hp₁ : p ≤ 1)
    (hX_aem : ∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P)
    (hX_nn : ∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i)
    (hX_L2 : ∀ i : ℕ, 1 ≤ i → MemLp (X i) 2 P)
    (hX_mean : ∀ i : ℕ, 1 ≤ i → ∫ ω, X i ω ∂P = 1)
    (hX_indep : iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P)
    (hN_aem : AEMeasurable N P)
    (hM_aem : AEMeasurable M P)
    (hN_pos : ∀ᵐ ω ∂P, 1 ≤ N ω)
    (hN_int : Integrable (fun ω ↦ (N ω : ℝ)) P)
    (hN_mean : ∫ ω, (N ω : ℝ) ∂P = 1 / p)
    (hM_pos : ∀ᵐ ω ∂P, 1 ≤ M ω)
    (hM_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω})
    (hXe_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (Xe i))
    (hXe_indep : ∀ i : {i : ℕ // 1 ≤ i},
      IndepFun (Xe i.1)
        (fun ω ↦ (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P)
    (hNM_indep : IndepFun (fun ω ↦ (N ω, M ω))
      (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P)
    (hZ_aem : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdExpLaw) :
    let W : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
    let μ₂ : ℝ≥0∞ := ⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ ω, X i ω ^ 2 ∂P)
    let err₁ : ℝ≥0∞ :=
      ENNReal.ofReal (2 * p) *
        ((∫⁻ ω, ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| ∂P) +
          ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
    let err₂ : ℝ≥0∞ :=
      ENNReal.ofReal (2 * p) *
        (1 + μ₂ / 2 + ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
    wassersteinDist (P.map W) (P'.map Z) ≤ err₁ ∧ err₁ ≤ err₂ := by
  dsimp only
  let I₁ := {i : ℕ // 1 ≤ i}
  let N₁ : Ω → ℕ := fun ω ↦ max (hN_aem.mk N ω) 1
  let M₁ : Ω → ℕ := fun ω ↦ max (hM_aem.mk M ω) 1
  let X₁ : ℕ → Ω → ℝ := fun i ω ↦
    if hi : 1 ≤ i then max ((hX_aem i hi).mk (X i) ω) 0 else 0
  let Xe₁ : ℕ → Ω → ℝ := fun i ω ↦
    if hi : 1 ≤ i then (hXe_eq i hi).2.2.1.mk (Xe i) ω else 0
  have hN₁_meas : Measurable N₁ := hN_aem.measurable_mk.max measurable_const
  have hM₁_meas : Measurable M₁ := hM_aem.measurable_mk.max measurable_const
  have hN₁_ge : ∀ ω, 1 ≤ N₁ ω := fun _ ↦ le_max_right _ 1
  have hM₁_ge : ∀ ω, 1 ≤ M₁ ω := fun _ ↦ le_max_right _ 1
  have hX₁_meas : ∀ i, Measurable (X₁ i) := fun i ↦ by
    dsimp only [X₁]
    split_ifs with hi
    · exact (hX_aem i hi).measurable_mk.max measurable_const
    · exact measurable_const
  have hXe₁_meas : ∀ i, Measurable (Xe₁ i) := fun i ↦ by
    dsimp only [Xe₁]
    split_ifs with hi
    · exact (hXe_eq i hi).2.2.1.measurable_mk
    · exact measurable_const
  have hX₁_nn : ∀ i ω, 0 ≤ X₁ i ω := fun i ω ↦ by
    dsimp only [X₁]
    split_ifs
    · exact le_max_right _ 0
    · exact le_rfl
  have hN_ae : N =ᵐ[P] N₁ := by
    filter_upwards [hN_aem.ae_eq_mk, hN_pos] with ω h1 h2
    dsimp only [N₁]
    rw [← h1, max_eq_left h2]
  have hM_ae : M =ᵐ[P] M₁ := by
    filter_upwards [hM_aem.ae_eq_mk, hM_pos] with ω h1 h2
    dsimp only [M₁]
    rw [← h1, max_eq_left h2]
  have hX_ae : ∀ i : ℕ, 1 ≤ i → X i =ᵐ[P] X₁ i := fun i hi ↦ by
    filter_upwards [(hX_aem i hi).ae_eq_mk, hX_nn i hi] with ω h1 (h2 : 0 ≤ X i ω)
    dsimp only [X₁]
    simp only [hi, ↓reduceDIte, ← h1, max_eq_left h2]
  have hXe_ae : ∀ i : ℕ, 1 ≤ i → Xe i =ᵐ[P] Xe₁ i := fun i hi ↦ by
    filter_upwards [(hXe_eq i hi).2.2.1.ae_eq_mk] with ω h1
    dsimp only [Xe₁]
    simp only [hi, ↓reduceDIte, ← h1]
  have hall_ae : ∀ᵐ ω ∂P, ∀ i : I₁, X i.1 ω = X₁ i.1 ω ∧ Xe i.1 ω = Xe₁ i.1 ω :=
    ae_all_iff.mpr fun i ↦ (hX_ae i.1 i.2).and (hXe_ae i.1 i.2)
  have hX₁_indep : iIndepFun (fun i : I₁ ↦ X₁ i.1) P :=
    hX_indep.congr fun i ↦ hX_ae i.1 i.2
  have hXe₁_indep : ∀ i : I₁,
      IndepFun (Xe₁ i.1)
        (fun ω ↦ (N₁ ω, M₁ ω, fun j : {j : I₁ // j ≠ i} ↦ X₁ j.1.1 ω)) P := fun i ↦
    (hXe_indep i).congr (hXe_ae i.1 i.2)
      (((hN_ae.and hM_ae).and hall_ae).mono fun ω ⟨⟨hNω, hMω⟩, hXω⟩ ↦
        Prod.ext hNω (Prod.ext hMω (funext fun j ↦ (hXω j.1).1)))
  have hNM₁_indep : IndepFun (fun ω ↦ (N₁ ω, M₁ ω))
      (fun ω (i : I₁) ↦ X₁ i.1 ω) P :=
    hNM_indep.congr
      ((hN_ae.and hM_ae).mono fun ω ⟨h1, h2⟩ ↦ Prod.ext h1 h2)
      (hall_ae.mono fun ω hω ↦ funext fun i ↦ (hω i).1)
  have hX₁_int : ∀ i : ℕ, 1 ≤ i → Integrable (X₁ i) P := fun i hi ↦
    ((hX_L2 i hi).integrable one_le_two).congr (hX_ae i hi)
  have hX₁_mean : ∀ i : ℕ, 1 ≤ i → ∫ ω, X₁ i ω ∂P = 1 := fun i hi ↦ by
    rw [← integral_congr_ae (hX_ae i hi), hX_mean i hi]
  have hX₁_lint : ∀ i : ℕ, 1 ≤ i → ∫⁻ ω, ENNReal.ofReal (X₁ i ω) ∂P = 1 := fun i hi ↦ by
    rw [← ofReal_integral_eq_lintegral_ofReal (hX₁_int i hi)
      (Eventually.of_forall fun ω ↦ hX₁_nn i ω), hX₁_mean i hi, ENNReal.ofReal_one]
  have hXe₁_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X₁ i) P (Xe₁ i) := fun i hi ↦
    (hXe_eq i hi).congr_identDistrib
      (IdentDistrib.of_ae_eq (hX_aem i hi) (hX_ae i hi))
      (IdentDistrib.of_ae_eq (hXe_eq i hi).2.2.1 (hXe_ae i hi))
  have hM₁_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M₁ ω = m} = p * P.real {ω | m ≤ N₁ ω} :=
    fun m hm ↦ by
      have hc1 : P.real {ω | M₁ ω = m} = P.real {ω | M ω = m} :=
        measureReal_congr (hM_ae.mono fun ω hω ↦ propext (by simp [hω]))
      have hc2 : P.real {ω | m ≤ N₁ ω} = P.real {ω | m ≤ N ω} :=
        measureReal_congr (hN_ae.mono fun ω hω ↦ propext (by simp [hω]))
      rw [hc1, hc2, hM_pmf m hm]
  have hN₁R_int : Integrable (fun ω ↦ (N₁ ω : ℝ)) P :=
    hN_int.congr (hN_ae.mono fun ω hω ↦ congrArg Nat.cast hω)
  have hN₁R_mean : ∫ ω, (N₁ ω : ℝ) ∂P = 1 / p := by
    rw [← integral_congr_ae (hN_ae.mono fun ω hω ↦ congrArg Nat.cast hω), hN_mean]
  let W₁ : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω
  let We₁ : Ω → ℝ := fun ω ↦ p * ((∑ i ∈ Finset.Ico 1 (M₁ ω), X₁ i ω) + Xe₁ (M₁ ω) ω)
  have hW₁_nn : ∀ ω, 0 ≤ W₁ ω := fun ω ↦
    mul_nonneg hp₀.le (Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω)
  have hW_ae : (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω) =ᵐ[P] W₁ := by
    filter_upwards [hN_ae, hall_ae] with ω hNω hXω
    dsimp only [W₁]
    rw [hNω]
    congr 1
    exact Finset.sum_congr rfl fun i hi ↦ (hXω ⟨i, (Finset.mem_Icc.mp hi).1⟩).1
  obtain ⟨hW₁_int, hW₁_mean, hEqW₁⟩ :=
    integrable_and_isEquilibrium_geom_sum_clean P hp₀ hX₁_meas hXe₁_meas hX₁_nn hX₁_int
      hX₁_mean hX₁_indep hN₁_meas hM₁_meas hM₁_ge hN₁R_int hN₁R_mean hM₁_pmf hXe₁_eq
      hXe₁_indep hNM₁_indep
  have hNM_meas : Measurable (fun ω ↦ (N₁ ω, M₁ ω)) := hN₁_meas.prodMk hM₁_meas
  have hXvec_meas : Measurable (fun ω (i : I₁) ↦ X₁ i.1 ω) :=
    measurable_pi_iff.mpr fun i ↦ hX₁_meas i.1
  have hDiffXM_ae :
      (fun ω ↦ ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω|) =ᵐ[P]
        fun ω ↦ ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| := by
    filter_upwards [hM_ae, hall_ae] with ω hMω hXω
    have hm1 : 1 ≤ M₁ ω := hM₁_ge ω
    have hpair := hXω ⟨M₁ ω, hm1⟩
    simp [hMω, hpair.1, hpair.2]
  have hDiffNM_ae :
      (fun ω ↦ ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)|) =ᵐ[P]
        fun ω ↦ ENNReal.ofReal |(N₁ ω : ℝ) - (M₁ ω : ℝ)| := by
    filter_upwards [hN_ae, hM_ae] with ω hNω hMω
    simp [hNω, hMω]
  have hIoc_lint :
      ∫⁻ ω, ENNReal.ofReal
        (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)), X₁ i ω) ∂P =
      ∫⁻ ω, ENNReal.ofReal |(N₁ ω : ℝ) - (M₁ ω : ℝ)| ∂P := by
    have hpt : ∀ ω,
        ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)), X₁ i ω) =
        ∑' k : ℕ,
          {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) ω * ENNReal.ofReal (X₁ (k + 1) ω) := fun ω ↦ by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hX₁_nn i ω),
        sum_Ioc_eq_tsum_ite (fun i ↦ ENNReal.ofReal (X₁ i ω))]
      congr 1; ext k
      by_cases hk : k + 1 ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω))
      · have hmem : ω ∈ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} := hk
        rw [indicator_of_mem hmem, one_mul]; simp only [hk, ↓reduceIte]
      · have hnot : ω ∉ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} := hk
        rw [indicator_of_notMem hnot, zero_mul]; simp only [hk, ↓reduceIte]
    simp_rw [hpt]
    have hEv_meas : ∀ k : ℕ,
        MeasurableSet {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} :=
      fun k ↦ by
        change MeasurableSet
          ((fun ω' ↦ (N₁ ω', M₁ ω')) ⁻¹'
            {q : ℕ × ℕ | k + 1 ∈ Finset.Ioc (min q.1 q.2) (max q.1 q.2)})
        exact hNM_meas MeasurableSet.of_discrete
    have hm_term : ∀ k : ℕ, Measurable (fun ω ↦
        {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
          (fun _ ↦ (1 : ℝ≥0∞)) ω * ENNReal.ofReal (X₁ (k + 1) ω)) := fun k ↦
      (measurable_const.indicator (hEv_meas k)).mul
        (ENNReal.measurable_ofReal.comp (hX₁_meas (k + 1)))
    rw [lintegral_tsum fun k ↦ (hm_term k).aemeasurable]
    have hfactor : ∀ k : ℕ,
        ∫⁻ ω,
          {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) ω * ENNReal.ofReal (X₁ (k + 1) ω) ∂P =
        ∫⁻ ω,
          {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) ω ∂P := fun k ↦ by
      let ik : I₁ := ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
      let φ₁ : ℕ × ℕ → ℝ≥0∞ := fun q ↦
        if k + 1 ∈ Finset.Ioc (min q.1 q.2) (max q.1 q.2) then 1 else 0
      let φ₂ : (I₁ → ℝ) → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (z ik)
      have hφ₁ : Measurable φ₁ := Measurable.of_discrete
      have hφ₂ : Measurable φ₂ := ENNReal.measurable_ofReal.comp (measurable_pi_apply ik)
      have hind := hNM₁_indep.comp hφ₁ hφ₂
      have hprod : (fun ω ↦
          {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
            (fun _ ↦ (1 : ℝ≥0∞)) ω * ENNReal.ofReal (X₁ (k + 1) ω)) =
          fun ω ↦ (φ₁ ∘ fun ω ↦ (N₁ ω, M₁ ω)) ω *
            (φ₂ ∘ fun ω (i : I₁) ↦ X₁ i.1 ω) ω := by
        ext ω
        dsimp only [φ₁, φ₂, Function.comp_apply]
        by_cases hk : k + 1 ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω))
        · have hmem : ω ∈ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} :=
            hk
          rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]; rfl
        · have hnot : ω ∉ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} :=
            hk
          rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]; rfl
      have hl1 : ∫⁻ ω, (φ₁ ∘ fun ω ↦ (N₁ ω, M₁ ω)) ω ∂P =
          ∫⁻ ω,
            {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
              (fun _ ↦ (1 : ℝ≥0∞)) ω ∂P := by
        refine lintegral_congr fun ω ↦ ?_
        dsimp only [φ₁, Function.comp_apply]
        by_cases hk : k + 1 ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω))
        · have hmem : ω ∈ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} :=
            hk
          rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]
        · have hnot : ω ∉ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} :=
            hk
          rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
      have hl2 : ∫⁻ ω, (φ₂ ∘ fun ω (i : I₁) ↦ X₁ i.1 ω) ω ∂P = 1 :=
        hX₁_lint (k + 1) ik.2
      change lintegral P (fun ω ↦
        {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
          (fun _ ↦ (1 : ℝ≥0∞)) ω * ENNReal.ofReal (X₁ (k + 1) ω)) = _
      rw [hprod, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        (hφ₁.comp hNM_meas).aemeasurable (hφ₂.comp hXvec_meas).aemeasurable hind, hl1, hl2, mul_one]
    simp_rw [hfactor]
    rw [← lintegral_tsum fun k ↦ (measurable_const.indicator (hEv_meas k)).aemeasurable]
    refine lintegral_congr fun ω ↦ ?_
    have hc : (fun k : ℕ ↦
        {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))}.indicator
          (fun _ ↦ (1 : ℝ≥0∞)) ω) =
        fun k ↦
          if k + 1 ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)) then 1 else 0 := by
      ext k
      by_cases hk : k + 1 ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω))
      · have hmem : ω ∈ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} := hk
        rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]
      · have hnot : ω ∉ {ω' | k + 1 ∈ Finset.Ioc (min (N₁ ω') (M₁ ω')) (max (N₁ ω') (M₁ ω'))} := hk
        rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
    rw [hc, tsum_ite_mem_Ioc_eq_ofReal_abs_sub]
  have hBound1 : wassersteinDist (P.map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω))
      (P'.map Z) ≤
      ENNReal.ofReal (2 * p) *
        ((∫⁻ ω, ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| ∂P) +
          ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P) := by
    rw [Measure.map_congr hW_ae, lintegral_congr_ae hDiffXM_ae, lintegral_congr_ae hDiffNM_ae]
    refine (wassersteinDist_le_two_mul_lintegral_equilibrium P P'
      (Eventually.of_forall hW₁_nn) hW₁_int hW₁_mean hEqW₁ hZ_aem hZ_law).trans ?_
    have hXM_meas : Measurable (fun ω ↦ ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω|) :=
      ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp
          ((measurable_select_nat hX₁_meas hM₁_meas).sub
            (measurable_select_nat hXe₁_meas hM₁_meas)))
    have hIoc_meas : Measurable (fun ω ↦ ENNReal.ofReal
        (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)), X₁ i ω)) := by
      let g_pair : ℕ × ℕ → Ω → ℝ := fun q ω ↦
        ∑ i ∈ Finset.Ioc (min q.1 q.2) (max q.1 q.2), X₁ i ω
      have hg_pair : ∀ q : ℕ × ℕ, Measurable (g_pair q) := fun q ↦
        Finset.measurable_sum _ fun i _ ↦ hX₁_meas i
      have hsel : Measurable (fun ω ↦ g_pair (N₁ ω, M₁ ω) ω) := by
        intro s hs
        have hpre : (fun ω ↦ g_pair (N₁ ω, M₁ ω) ω) ⁻¹' s =
            ⋃ q : ℕ × ℕ, ((fun ω ↦ (N₁ ω, M₁ ω)) ⁻¹' {q}) ∩ (g_pair q ⁻¹' s) := by
          ext ω
          simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
          exact ⟨fun h ↦ ⟨(N₁ ω, M₁ ω), rfl, h⟩, fun ⟨q, hq, hfq⟩ ↦ hq.symm ▸ hfq⟩
        rw [hpre]
        exact MeasurableSet.iUnion fun q ↦
          (hNM_meas (measurableSet_singleton q)).inter (hg_pair q hs)
      exact ENNReal.measurable_ofReal.comp hsel
    have hpt_le : ∀ ω, ENNReal.ofReal |We₁ ω - W₁ ω| ≤
        ENNReal.ofReal p * (ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| +
          ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)),
            X₁ i ω)) := fun ω ↦ by
      have habs := abs_equilibrium_sum_sub_le (fun i ↦ hX₁_nn i ω) hp₀.le (Xe₁ (M₁ ω) ω)
        (hN₁_ge ω) (hM₁_ge ω)
      have hsum_nn : 0 ≤ ∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)), X₁ i ω :=
        Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω
      calc
        ENNReal.ofReal |We₁ ω - W₁ ω|
            ≤ ENNReal.ofReal (p * |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| +
                p * ∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)), X₁ i ω) :=
              ENNReal.ofReal_le_ofReal habs
        _ = ENNReal.ofReal p * (ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| +
              ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)),
                X₁ i ω)) := by
              rw [← mul_add, ENNReal.ofReal_mul hp₀.le,
                ENNReal.ofReal_add (abs_nonneg _) hsum_nn]
    have hAdd_meas : Measurable (fun ω ↦
        ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| +
          ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)),
            X₁ i ω)) := hXM_meas.add hIoc_meas
    calc
      ENNReal.ofReal 2 * ∫⁻ ω, ENNReal.ofReal |We₁ ω - W₁ ω| ∂P
          ≤ ENNReal.ofReal 2 * ∫⁻ ω, ENNReal.ofReal p *
              (ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| +
                ENNReal.ofReal (∑ i ∈ Finset.Ioc (min (N₁ ω) (M₁ ω)) (max (N₁ ω) (M₁ ω)),
                  X₁ i ω)) ∂P :=
            mul_le_mul_of_nonneg_left (lintegral_mono hpt_le) zero_le
      _ = ENNReal.ofReal (2 * p) *
            ((∫⁻ ω, ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| ∂P) +
              ∫⁻ ω, ENNReal.ofReal |(N₁ ω : ℝ) - (M₁ ω : ℝ)| ∂P) := by
            rw [lintegral_const_mul _ hAdd_meas, lintegral_add_left hXM_meas,
              hIoc_lint, ← mul_assoc, ← ENNReal.ofReal_mul zero_le_two]
  refine ⟨hBound1, ?_⟩
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) zero_le
  rw [lintegral_congr_ae hDiffXM_ae]
  set μ₂ : ℝ≥0∞ := ⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ ω, X i ω ^ 2 ∂P)
  have hXe_props : ∀ i : I₁,
      (0 ≤ᵐ[P] Xe₁ i.1) ∧ ∫⁻ ω, ENNReal.ofReal (Xe₁ i.1 ω) ∂P ≤ μ₂ / 2 := fun i ↦ by
    have hX₁_L2 : MemLp (X₁ i.1) 2 P := (hX_L2 i.1 i.2).ae_eq (hX_ae i.1 i.2)
    have hμ_pos : 0 < ∫ ω, X₁ i.1 ω ∂P := by rw [hX₁_mean i.1 i.2]; exact zero_lt_one
    obtain ⟨hXe_nn, hXe_int, hXe_mean⟩ :=
      integrable_and_integral_equilibrium_of_memLp_two P P
        (Eventually.of_forall fun ω ↦ hX₁_nn i.1 ω) hX₁_L2 hμ_pos (hXe₁_eq i.1 i.2)
    rw [hX₁_mean i.1 i.2, mul_one] at hXe_mean
    have hsq_congr : ∫ ω, X₁ i.1 ω ^ 2 ∂P = ∫ ω, X i.1 ω ^ 2 ∂P :=
      integral_congr_ae ((hX_ae i.1 i.2).symm.mono fun ω hω ↦ by simp [hω])
    refine ⟨hXe_nn, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hXe_int hXe_nn, hXe_mean, hsq_congr,
      ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_ofNat 2]
    exact ENNReal.div_le_div_right
      (le_iSup₂ (f := fun (j : ℕ) (_ : 1 ≤ j) ↦ ENNReal.ofReal (∫ ω, X j ω ^ 2 ∂P)) i.1 i.2) 2
  have hae_tri : ∀ᵐ ω ∂P, ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| ≤
      ENNReal.ofReal (X₁ (M₁ ω) ω) + ENNReal.ofReal (Xe₁ (M₁ ω) ω) := by
    filter_upwards [ae_all_iff.mpr fun i : I₁ ↦ (hXe_props i).1] with ω hω
    have h1 : 0 ≤ X₁ (M₁ ω) ω := hX₁_nn (M₁ ω) ω
    have h2 : 0 ≤ Xe₁ (M₁ ω) ω := hω ⟨M₁ ω, hM₁_ge ω⟩
    have habs : |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| ≤ X₁ (M₁ ω) ω + Xe₁ (M₁ ω) ω :=
      (abs_sub _ _).trans_eq (by rw [abs_of_nonneg h1, abs_of_nonneg h2])
    exact (ENNReal.ofReal_le_ofReal habs).trans_eq (ENNReal.ofReal_add h1 h2)
  have hMX_indep : ∀ k : ℕ, IndepFun M₁ (X₁ (k + 1)) P := fun k ↦ by
    let ik : I₁ := ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
    exact hNM₁_indep.comp measurable_snd (measurable_pi_apply (X := fun _ : I₁ ↦ ℝ) ik)
  have hMXe_indep : ∀ k : ℕ, IndepFun M₁ (Xe₁ (k + 1)) P := fun k ↦
    (hXe₁_indep ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩).symm.comp
      (measurable_fst.comp measurable_snd) measurable_id
  have hsum_prob : (∑' k : ℕ, P {ω' | M₁ ω' = k + 1}) = 1 := by
    have hdisj : Pairwise (Disjoint on fun k : ℕ ↦ {ω' | M₁ ω' = k + 1}) :=
      fun k₁ k₂ hne ↦ Set.disjoint_left.mpr fun ω h1 h2 ↦ hne (Nat.succ.inj (h1.symm.trans h2))
    have hunion : (⋃ k : ℕ, {ω' | M₁ ω' = k + 1}) = univ := by
      ext ω
      simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨M₁ ω - 1, by have := hM₁_ge ω; omega⟩
    rw [← measure_iUnion hdisj (fun k ↦ hM₁_meas (measurableSet_singleton (k + 1))),
      hunion, measure_univ]
  have hXM₁_meas : Measurable (fun ω ↦ ENNReal.ofReal (X₁ (M₁ ω) ω)) :=
    ENNReal.measurable_ofReal.comp (measurable_select_nat hX₁_meas hM₁_meas)
  calc
    ∫⁻ ω, ENNReal.ofReal |X₁ (M₁ ω) ω - Xe₁ (M₁ ω) ω| ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (X₁ (M₁ ω) ω) + ENNReal.ofReal (Xe₁ (M₁ ω) ω)) ∂P :=
          lintegral_mono_ae hae_tri
    _ = (∫⁻ ω, ENNReal.ofReal (X₁ (M₁ ω) ω) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (Xe₁ (M₁ ω) ω) ∂P :=
          lintegral_add_left hXM₁_meas _
    _ = (∑' k : ℕ, P {ω' | M₁ ω' = k + 1} * ∫⁻ ω, ENNReal.ofReal (X₁ (k + 1) ω) ∂P) +
          ∑' k : ℕ, P {ω' | M₁ ω' = k + 1} * ∫⁻ ω, ENNReal.ofReal (Xe₁ (k + 1) ω) ∂P := by
          rw [lintegral_ofReal_select_nat_eq_tsum P hM₁_meas hM₁_ge hX₁_meas hMX_indep,
            lintegral_ofReal_select_nat_eq_tsum P hM₁_meas hM₁_ge hXe₁_meas hMXe_indep]
    _ ≤ 1 + μ₂ / 2 := by
          refine add_le_add ?_ ?_
          · simp_rw [fun k : ℕ ↦ hX₁_lint (k + 1) (Nat.succ_le_succ (Nat.zero_le k)), mul_one]
            exact hsum_prob.le
          · calc
              (∑' k : ℕ, P {ω' | M₁ ω' = k + 1} * ∫⁻ ω, ENNReal.ofReal (Xe₁ (k + 1) ω) ∂P)
                  ≤ ∑' k : ℕ, P {ω' | M₁ ω' = k + 1} * (μ₂ / 2) :=
                    ENNReal.tsum_le_tsum fun k ↦ mul_le_mul_of_nonneg_left
                      (hXe_props ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩).2 zero_le
              _ = (∑' k : ℕ, P {ω' | M₁ ω' = k + 1}) * (μ₂ / 2) := ENNReal.tsum_mul_right
              _ = μ₂ / 2 := by rw [hsum_prob, one_mul]

/-- Compatibility wrapper deriving the earlier stronger-hypothesis signature of Theorem 5.7 from
`thm5_7_corrected_minimal` so committed `Sec5Proofs` remains compiling until switched over. -/
theorem thm5_7_corrected
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {X Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ} {Z : Ω' → ℝ}
    (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    (hX_aem : ∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P)
    (hX_nn : ∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i)
    (hX_L2 : ∀ i : ℕ, 1 ≤ i → MemLp (X i) 2 P)
    (hX_mean : ∀ i : ℕ, 1 ≤ i → ∫ ω, X i ω ∂P = 1)
    (hX_indep : iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P)
    (hN_aem : AEMeasurable N P)
    (hM_aem : AEMeasurable M P)
    (hN_pos : ∀ᵐ ω ∂P, 1 ≤ N ω)
    (hN_int : Integrable (fun ω ↦ (N ω : ℝ)) P)
    (hN_mean : ∫ ω, (N ω : ℝ) ∂P = 1 / p)
    (hM_pos : ∀ᵐ ω ∂P, 1 ≤ M ω)
    (hM_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω})
    (hXe_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (Xe i))
    (hXe_indep : ∀ i : {i : ℕ // 1 ≤ i},
      IndepFun (Xe i.1) (fun ω (j : {j : {k : ℕ // 1 ≤ k} // j ≠ i}) ↦ X j.1.1 ω) P)
    (hNM_indep : IndepFun (fun ω ↦ (N ω, M ω))
      (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ (X i.1 ω, Xe i.1 ω)) P)
    (hZ_aem : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdExpLaw) :
    let W : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
    let μ₂ : ℝ≥0∞ := ⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ ω, X i ω ^ 2 ∂P)
    let err₁ : ℝ≥0∞ :=
      ENNReal.ofReal (2 * p) *
        ((∫⁻ ω, ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| ∂P) +
          ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
    let err₂ : ℝ≥0∞ :=
      ENNReal.ofReal (2 * p) *
        (1 + μ₂ / 2 + ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
    wassersteinDist (P.map W) (P'.map Z) ≤ err₁ ∧ err₁ ≤ err₂ := by
  obtain ⟨Xmk, hXmk_meas, hXmk_ae⟩ : ∃ Xmk : {k : ℕ // 1 ≤ k} → Ω → ℝ,
      (∀ k, Measurable (Xmk k)) ∧ ∀ k, X k.1 =ᵐ[P] Xmk k :=
    ⟨fun k ↦ (hX_aem k.1 k.2).mk (X k.1), fun k ↦ (hX_aem k.1 k.2).measurable_mk,
      fun k ↦ (hX_aem k.1 k.2).ae_eq_mk⟩
  obtain ⟨Xemk, hXemk_meas, hXemk_ae⟩ : ∃ Xemk : {k : ℕ // 1 ≤ k} → Ω → ℝ,
      (∀ k, Measurable (Xemk k)) ∧ ∀ k, Xe k.1 =ᵐ[P] Xemk k :=
    ⟨fun k ↦ (hXe_eq k.1 k.2).2.2.1.mk (Xe k.1), fun k ↦ (hXe_eq k.1 k.2).2.2.1.measurable_mk,
      fun k ↦ (hXe_eq k.1 k.2).2.2.1.ae_eq_mk⟩
  obtain ⟨NMmk, hNMmk_meas, hNMmk_ae⟩ :
      ∃ NMmk : Ω → ℕ × ℕ, Measurable NMmk ∧ (fun ω ↦ (N ω, M ω)) =ᵐ[P] NMmk :=
    ⟨(hN_aem.prodMk hM_aem).mk _, (hN_aem.prodMk hM_aem).measurable_mk,
      (hN_aem.prodMk hM_aem).ae_eq_mk⟩
  have hall : ∀ᵐ ω ∂P, ∀ k : {k : ℕ // 1 ≤ k}, X k.1 ω = Xmk k ω ∧ Xe k.1 ω = Xemk k ω :=
    ae_all_iff.mpr fun k ↦ (hXmk_ae k).and (hXemk_ae k)
  have hNM_mk : IndepFun NMmk (fun ω (k : {k : ℕ // 1 ≤ k}) ↦ (Xmk k ω, Xemk k ω)) P :=
    hNM_indep.congr hNMmk_ae (hall.mono fun ω hω ↦ funext fun k ↦ Prod.ext (hω k).1 (hω k).2)
  have hXe_min : ∀ i : {i : ℕ // 1 ≤ i},
      IndepFun (Xe i.1)
        (fun ω ↦ (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P := fun i ↦ by
    have hind1 := (hXe_indep i).congr (hXemk_ae i)
      (hall.mono fun ω hω ↦ funext fun j ↦ (hω j.1).1)
    have hψ : Measurable (fun z : {k : ℕ // 1 ≤ k} → ℝ × ℝ ↦
        ((z i).2, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ (z j.1).1)) :=
      (measurable_snd.comp (measurable_pi_apply (X := fun _ : {k : ℕ // 1 ≤ k} ↦ ℝ × ℝ) i)).prodMk
        (measurable_pi_iff.mpr fun j ↦
          measurable_fst.comp (measurable_pi_apply (X := fun _ : {k : ℕ // 1 ≤ k} ↦ ℝ × ℝ) j.1))
    have hind2 := indepFun_left_pair_of_indepFun_pair_right (hXemk_meas i)
      (measurable_pi_iff.mpr fun (j : {j : {k : ℕ // 1 ≤ k} // j ≠ i}) ↦ hXmk_meas j.1)
      hNMmk_meas hind1 (hNM_mk.symm.comp hψ measurable_id)
    have hind3 := hind2.comp measurable_id
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_snd.comp measurable_snd).prodMk measurable_fst))
    exact hind3.congr (hXemk_ae i).symm
      ((hNMmk_ae.symm.and hall).mono fun ω ⟨hNMω, hXω⟩ ↦ by
        change ((NMmk ω).1, (NMmk ω).2, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ Xmk j.1 ω) =
          (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)
        rw [hNMω]
        exact Prod.ext rfl (Prod.ext rfl (funext fun j ↦ (hXω j.1).1.symm)))
  have hNM_min : IndepFun (fun ω ↦ (N ω, M ω)) (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P :=
    hNM_indep.comp measurable_id (measurable_pi_iff.mpr fun i ↦
      measurable_fst.comp (measurable_pi_apply (X := fun _ : {k : ℕ // 1 ≤ k} ↦ ℝ × ℝ) i))
  exact thm5_7_corrected_minimal P P' hp₀ hp₁ hX_aem hX_nn hX_L2 hX_mean hX_indep hN_aem hM_aem
    hN_pos hN_int hN_mean hM_pos hM_pmf hXe_eq hXe_min hNM_min hZ_aem hZ_law

private lemma shiftedGeomLaw_ae_pos_and_tail {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : Ω → ℕ}
    (hN_aem : AEMeasurable N P) (hN_law : P.map N = shiftedGeomLaw p) :
    (∀ᵐ ω ∂P, 1 ≤ N ω) ∧
      ∀ m : ℕ, 1 ≤ m → P.real {ω | N ω = m} = p * P.real {ω | m ≤ N ω} := by
  refine ⟨?_, fun m hm ↦ ?_⟩
  · have hae := ae_one_le_shiftedGeomLaw p
    rw [← hN_law] at hae
    exact (ae_map_iff hN_aem measurableSet_Ici).mp hae
  · have h1 : P.real {ω | N ω = m} = (shiftedGeomLaw p).real {m} := by
      rw [← hN_law, map_measureReal_apply_of_aemeasurable hN_aem (measurableSet_singleton m)]
      rfl
    have h2 : P.real {ω | m ≤ N ω} = (shiftedGeomLaw p).real (Ici m) := by
      rw [← hN_law, map_measureReal_apply_of_aemeasurable hN_aem measurableSet_Ici]
      rfl
    rw [h1, h2, shiftedGeomLaw_real_singleton_of_pos hp₀ hp₁ hm,
      shiftedGeomLaw_real_Ici hp₀ hp₁ hm, mul_comm]

/-- **Remark 5.5** (`SteinIntro.tex:2931-2947`): (i) in the setting of Theorem 5.7,
$M \stackrel{d}{=} V$ where $V \mid N^s \sim \mathrm{Unif}\{1, \dots, N^s\}$; (ii) for
$N \sim \mathrm{Ge}(p)$, $M = N$ satisfies $M \ge 1$ a.s. and
$\mathbb{P}(M = m) = p\,\mathbb{P}(N \ge m)$ for $m \ge 1$; and (iii) when
$X_i \sim \mathrm{Exp}(1)$ are i.i.d. and independent of $N \sim \mathrm{Ge}(p)$,
$d_{\mathrm{W}}(\mathcal{L}(p \sum_{i=1}^N X_i), \mathcal{L}(Z)) = 0$. -/
theorem rem5_5 {p : ℝ} (hp₀ : 0 < p) (hp₁ : p ≤ 1) :
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {N M : Ω → ℕ} {Ns V : Ω' → ℕ},
      AEMeasurable N P →
      AEMeasurable M P →
      (∀ᵐ ω ∂P, 1 ≤ N ω) →
      Integrable (fun ω ↦ (N ω : ℝ)) P →
      ∫ ω, (N ω : ℝ) ∂P = 1 / p →
      (∀ᵐ ω ∂P, 1 ≤ M ω) →
      (∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω}) →
      AEMeasurable V P' →
      IsSizeBias P (fun ω ↦ (N ω : ℝ)) P' (fun ω' ↦ (Ns ω' : ℝ)) →
      (∀ k m : ℕ, P'.real {ω' | Ns ω' = k ∧ V ω' = m} =
        if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Ns ω' = k} / (k : ℝ) else 0) →
      P.map M = P'.map V) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : Ω → ℕ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      (∀ᵐ ω ∂P, 1 ≤ N ω) ∧
        ∀ m : ℕ, 1 ≤ m → P.real {ω | N ω = m} = p * P.real {ω | m ≤ N ω}) ∧
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {X : ℕ → Ω → ℝ} {N : Ω → ℕ} {Z : Ω' → ℝ},
      (∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) →
      (∀ i : ℕ, 1 ≤ i → P.map (X i) = stdExpLaw) →
      iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P →
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      IndepFun N (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P →
      AEMeasurable Z P' →
      P'.map Z = stdExpLaw →
      wassersteinDist (P.map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω)) (P'.map Z) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ω Ω' _ _ P _ P' _ N M Ns V hN_aem hM_aem _hN_pos hN_int hN_mean hM_pos hM_pmf
      hV_aem hSB hUnif
    have hμ_pos : 0 < ∫ ω, (N ω : ℝ) ∂P := by rw [hN_mean]; positivity
    have hV_pmf := sizeBias_cond_uniform_pmf P P' hN_aem hN_int hμ_pos hV_aem hSB hUnif
    have : IsProbabilityMeasure (P.map M) := (Measure.isProbabilityMeasure_map_iff hM_aem).mpr ‹_›
    have : IsProbabilityMeasure (P'.map V) := (Measure.isProbabilityMeasure_map_iff hV_aem).mpr ‹_›
    ext s hs
    rw [← Measure.tsum_indicator_apply_singleton (P.map M) s hs,
      ← Measure.tsum_indicator_apply_singleton (P'.map V) s hs]
    congr with m
    by_cases hms : m ∈ s
    · simp only [indicator_of_mem hms]
      rw [← ofReal_measureReal (measure_ne_top (P.map M) {m}),
        ← ofReal_measureReal (measure_ne_top (P'.map V) {m})]
      congr 1
      have h1 : (P.map M).real {m} = P.real {ω | M ω = m} := by
        rw [map_measureReal_apply_of_aemeasurable hM_aem (measurableSet_singleton m)]; rfl
      have h2 : (P'.map V).real {m} = P'.real {ω' | V ω' = m} := by
        rw [map_measureReal_apply_of_aemeasurable hV_aem (measurableSet_singleton m)]; rfl
      rw [h1, h2, hV_pmf m, hN_mean]
      rcases m with _ | k
      · have hM0 : P {ω | M ω = 0} = 0 :=
          measure_mono_null (fun ω (hω : M ω = 0) ↦ show ¬ 1 ≤ M ω by omega) (ae_iff.mp hM_pos)
        simp [measureReal_def, hM0]
      · have hm1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        simp only [hm1, ↓reduceIte]
        rw [hM_pmf (k + 1) hm1]
        field_simp [hp₀.ne']
    · simp [indicator_of_notMem hms]
  · intro Ω _ P _ N hN_aem hN_law
    exact shiftedGeomLaw_ae_pos_and_tail hp₀ hp₁ P hN_aem hN_law
  · intro Ω Ω' _ _ P _ P' _ X N Z hX_aem hX_law hX_indep hN_aem hN_law hNX_indep hZ_aem hZ_law
    let I₁ := {i : ℕ // 1 ≤ i}
    have hN_props := shiftedGeomLaw_ae_pos_and_tail hp₀ hp₁ P hN_aem hN_law
    have hX_nn : ∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i := fun i hi ↦ by
      have hae : ∀ᵐ x ∂stdExpLaw, 0 ≤ x := ae_nonneg_expLaw 1
      rw [← hX_law i hi] at hae
      exact (ae_map_iff (hX_aem i hi) measurableSet_Ici).mp hae
    have hX_L2 : ∀ i : ℕ, 1 ≤ i → MemLp (X i) 2 P := fun i hi ↦ by
      have hm := memLp_id_two_stdExpLaw
      rw [← hX_law i hi] at hm
      exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable (hX_aem i hi)).mp hm
    have hX_mean : ∀ i : ℕ, 1 ≤ i → ∫ ω, X i ω ∂P = 1 := fun i hi ↦ by
      have hm := integral_id_stdExpLaw
      rw [← hX_law i hi,
        integral_map (f := fun x : ℝ ↦ x) (hX_aem i hi) aestronglyMeasurable_id] at hm
      exact hm
    have hN_int : Integrable (fun ω ↦ (N ω : ℝ)) P := by
      have hm := integrable_cast_shiftedGeomLaw hp₀ hp₁
      rw [← hN_law] at hm
      exact (integrable_map_measure (by fun_prop) hN_aem).mp hm
    have hN_mean : ∫ ω, (N ω : ℝ) ∂P = 1 / p := by
      have hm := integral_cast_shiftedGeomLaw hp₀ hp₁
      rw [← hN_law, integral_map hN_aem (by fun_prop)] at hm
      exact hm
    have hXe_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (X i) := fun i hi ↦ by
      have hid : IdentDistrib id (X i) stdExpLaw P :=
        ⟨aemeasurable_id, hX_aem i hi, by rw [Measure.map_id, hX_law i hi]⟩
      exact isEquilibrium_stdExpLaw.congr_identDistrib hid hid
    obtain ⟨Xmk, hXmk_meas, hXmk_ae⟩ :
        ∃ Xmk : {i : ℕ // 1 ≤ i} → Ω → ℝ,
          (∀ k, Measurable (Xmk k)) ∧ ∀ k, X k.1 =ᵐ[P] Xmk k :=
      ⟨fun k ↦ (hX_aem k.1 k.2).mk (X k.1),
        fun k ↦ (hX_aem k.1 k.2).measurable_mk,
        fun k ↦ (hX_aem k.1 k.2).ae_eq_mk⟩
    obtain ⟨Nmk, hNmk_meas, hNmk_ae⟩ :
        ∃ Nmk : Ω → ℕ, Measurable Nmk ∧ N =ᵐ[P] Nmk :=
      ⟨hN_aem.mk N, hN_aem.measurable_mk, hN_aem.ae_eq_mk⟩
    have hall_mk : ∀ᵐ ω ∂P, ∀ k : {i : ℕ // 1 ≤ i}, X k.1 ω = Xmk k ω :=
      ae_all_iff.mpr hXmk_ae
    have hNXmk_indep : IndepFun Nmk (fun ω (k : {i : ℕ // 1 ≤ i}) ↦ Xmk k ω) P :=
      hNX_indep.congr hNmk_ae (hall_mk.mono fun ω hω ↦ funext hω)
    have hXe_indep : ∀ i : {i : ℕ // 1 ≤ i},
        IndepFun (X i.1)
          (fun ω ↦ (N ω, N ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P := fun i ↦ by
      have hind_compl := iIndepFun_indepFun_compl (hX_indep.congr hXmk_ae) hXmk_meas i
      have hψ : Measurable (fun z : {k : ℕ // 1 ≤ k} → ℝ ↦
          (z i, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ z j.1)) :=
        (measurable_pi_apply (X := fun _ : {k : ℕ // 1 ≤ k} ↦ ℝ) i).prodMk
          (measurable_pi_iff.mpr fun j ↦
            measurable_pi_apply (X := fun _ : {k : ℕ // 1 ≤ k} ↦ ℝ) j.1)
      have hpair_Nmk :
          IndepFun (fun ω ↦ (Xmk i ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ Xmk j.1 ω))
            Nmk P :=
        hNXmk_indep.symm.comp hψ measurable_id
      have hind_triple0 :=
        indepFun_left_pair_of_indepFun_pair_right (hXmk_meas i)
          (measurable_pi_iff.mpr fun (j : {j : {k : ℕ // 1 ≤ k} // j ≠ i}) ↦ hXmk_meas j.1)
          hNmk_meas hind_compl hpair_Nmk
      have hind_triple :=
        hind_triple0.comp measurable_id
          (measurable_snd.prodMk (measurable_snd.prodMk measurable_fst))
      exact hind_triple.congr (hXmk_ae i).symm
        ((hNmk_ae.symm.and hall_mk).mono fun ω ⟨hNω, hXω⟩ ↦
          Prod.ext hNω (Prod.ext hNω (funext fun j ↦ (hXω j.1).symm)))
    have hNN_indep : IndepFun (fun ω ↦ (N ω, N ω))
        (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P :=
      hNX_indep.comp (measurable_id.prodMk measurable_id) measurable_id
    have hbnd := (thm5_7_corrected_minimal P P' hp₀ hp₁ hX_aem hX_nn hX_L2 hX_mean hX_indep
      hN_aem hN_aem hN_props.1 hN_int hN_mean hN_props.1 hN_props.2
      hXe_eq hXe_indep hNN_indep hZ_aem hZ_law).1
    simp only [sub_self, abs_zero, ENNReal.ofReal_zero, lintegral_zero, add_zero, mul_zero] at hbnd
    exact nonpos_iff_eq_zero.mp hbnd

end SteinMethod
