/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.ZeroBias.Lindeberg
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Lindeberg–Feller Sufficiency and Non-Necessity (`Formalization.ZeroBias.LindebergFeller`)

Completes Section 3.5.2 of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`,
`SteinIntro.tex:1553-1568`):

* `tendsto_stdNormalLaw_of_lindeberg` (`Sec3_5_2_lindeberg_sufficient`,
  `SteinIntro.tex:1560-1564`; `ISSUE-3.22` prose note): the classical Lindeberg condition `(3.34)`
  (`\label{85}`) suffices for $W_n = \sum_{i=1}^{n+1} X_{i,n} \xrightarrow{d} \mathcal{N}(0, 1)$,
  proved without assuming pre-existing zero-bias or random-index variables on `Ω` by constructing
  an enlarged row-wise product probability space via Proposition 3.19(3) and applying Theorems 3.22
  and 3.23.
* `lindeberg_not_necessary_for_clt` (`Sec3_5_2_lindeberg_not_necessary_corrected`,
  `SteinIntro.tex:1565-1566`; `ISSUE-3.5.2-PROSE`): the Lindeberg condition is not necessary for
  $W_n \xrightarrow{d} \mathcal{N}(0, 1)$ when $\max_i \sigma_{i,n}^2 \to 0$ is not assumed
  (witnessed by $X_{0,n} \sim \mathcal{N}(0, 1)$, $X_{i,n} = 0$ for $i \ge 1$).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Fixed-Space Theorems 3.22, 3.23 & `Sec3_5_2_zeroBias_imp_tendstoInMeasure` -/

private lemma tendstoInMeasure_zero_iff_tail_real
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : ℕ → Ω → ℝ} :
    TendstoInMeasure P Y atTop 0 ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ ↦ P.real {ω | ε ≤ |Y n ω|}) atTop (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs]

/-- **Theorem 3.22** (`\label{thm82}`, eq. `(3.34)` `\label{85}`, `SteinIntro.tex:1577-1607`;
`ISSUE-3.22`): for a triangular array of row-wise independent mean-zero $L^2$ random variables with
unit row variance sum, zero-bias variables $X_{i,n}^z$, and variance-weighted random indices $I_n$
independent of $((X_{i,n})_i, (X_{i,n}^z)_i)$, the Lindeberg condition `(3.34)` holds if and only
if $X_{I_n, n}^z \xrightarrow{\mathbb{P}} 0$. -/
theorem lindeberg_iff_tendstoInMeasure_zeroBias
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)}
    (hX_meas : ∀ n i, Measurable (X n i))
    (hXz_meas : ∀ n i, Measurable (Xz n i))
    (_hX_indep : ∀ n, iIndepFun (X n) P)
    (hX_L2 : ∀ n i, MemLp (X n i) 2 P)
    (_hX_mean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (_hVar : ∀ n, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1)
    (hXz : ∀ n i, IsZeroBias P (X n i) P (Xz n i))
    (hI_meas : ∀ n, Measurable (I n))
    (hI_prob : ∀ n i, P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P)
    (hI_indep : ∀ n, IndepFun (I n) (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ ∑ i : Fin (n + 1),
        ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
        atTop (𝓝 0)) ↔
    TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) atTop 0 := by
  rw [tendstoInMeasure_zero_iff_tail_real]
  exact lindeberg_iff_row_zeroBias_tail_tendsto (fun _ ↦ P) hX_meas hXz_meas hX_L2 hXz hI_meas
    hI_prob hI_indep

/-- **Section 3.5.2 Prose Implication** (`Sec3_5_2_zeroBias_imp_tendstoInMeasure`,
`SteinIntro.tex:1585-1586, 1625-1646`): if $X_{I_n, n}^z \xrightarrow{\mathbb{P}} 0$, then
$\max_i \sigma_{i,n}^2 \to 0$ and $X_{I_n, n} \xrightarrow{\mathbb{P}} 0$. -/
theorem tendstoInMeasure_and_max_variance_tendsto_of_zeroBias
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)}
    (hX_meas : ∀ n i, Measurable (X n i))
    (hXz_meas : ∀ n i, Measurable (Xz n i))
    (hX_indep : ∀ n, iIndepFun (X n) P)
    (hX_L2 : ∀ n i, MemLp (X n i) 2 P)
    (hX_mean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hVar : ∀ n, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1)
    (hXz : ∀ n i, IsZeroBias P (X n i) P (Xz n i))
    (hI_meas : ∀ n, Measurable (I n))
    (hI_prob : ∀ n i, P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P)
    (hI_indep : ∀ n, IndepFun (I n) (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P)
    (hConv : TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) atTop 0) :
    Tendsto (fun n : ℕ ↦ Finset.univ.sup' Finset.univ_nonempty
        fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) P)
      atTop (𝓝 0) ∧
    TendstoInMeasure P (fun n ω ↦ X n (I n ω) ω) atTop 0 := by
  have hVar_sum : ∀ n, (∑ i : Fin (n + 1), ProbabilityTheory.variance (X n i) P) = 1 := fun n ↦ by
    have hfn : (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) = ∑ i ∈ Finset.univ, X n i := by ext; simp
    rw [← hVar n, hfn, IndepFun.variance_sum (fun i _ ↦ hX_L2 n i)
      (fun i _ j _ hij ↦ (hX_indep n).indepFun hij)]
  rw [tendstoInMeasure_zero_iff_tail_real] at hConv ⊢
  exact row_max_variance_and_summand_tail_tendsto_of_zeroBias (fun _ ↦ P) hX_meas hXz_meas hX_L2
    hX_mean hVar_sum hXz hI_meas hI_prob hI_indep hConv

/-- **Theorem 3.23** (`\label{thm83}`, `SteinIntro.tex:1588-1590, 1608-1624`; `ISSUE-3.22`): under
the triangular-array zero-bias coupling hypotheses, if $X_{I_n, n}^z \xrightarrow{\mathbb{P}} 0$,
then $W_n = \sum_{i=1}^{n+1} X_{i,n} \xrightarrow{d} \mathcal{N}(0, 1)$. -/
theorem tendsto_stdNormalLaw_of_tendstoInMeasure_zeroBias
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)}
    (hX_meas : ∀ n i, Measurable (X n i))
    (hXz_meas : ∀ n i, Measurable (Xz n i))
    (hX_indep : ∀ n, iIndepFun (X n) P)
    (hX_L2 : ∀ n i, MemLp (X n i) 2 P)
    (hX_mean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hVar : ∀ n, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1)
    (hXz : ∀ n i, IsZeroBias P (X n i) P (Xz n i))
    (hXz_indep : ∀ n i,
      IndepFun (Xz n i) (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) P)
    (hI_meas : ∀ n, Measurable (I n))
    (hI_prob : ∀ n i, P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P)
    (hI_indep : ∀ n, IndepFun (I n) (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P)
    (hConv : TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) atTop 0) :
    Tendsto (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      atTop (𝓝 stdNormalLaw.toProbabilityMeasure) := by
  have hVar_sum : ∀ n, (∑ i : Fin (n + 1), ProbabilityTheory.variance (X n i) P) = 1 := fun n ↦ by
    have hfn : (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) = ∑ i ∈ Finset.univ, X n i := by ext; simp
    rw [← hVar n, hfn, IndepFun.variance_sum (fun i _ ↦ hX_L2 n i)
      (fun i _ j _ hij ↦ (hX_indep n).indepFun hij)]
  rw [tendstoInMeasure_zero_iff_tail_real] at hConv
  exact row_tendsto_stdNormalLaw_of_zeroBias_tail_tendsto (fun _ ↦ P) hX_meas hXz_meas hX_indep
    hX_L2 hX_mean hVar_sum hXz hXz_indep hI_meas hI_prob hI_indep hConv

/-! ### Section 2: Product-Space Zero-Bias Construction & Lindeberg Sufficiency -/

section Sufficiency

private noncomputable def rowZeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) : Measure ℝ :=
  if 0 < ProbabilityTheory.variance Y P then
    volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P Y w))
  else
    Measure.dirac 0

private lemma isProbabilityMeasure_rowZeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_L2 : MemLp Y 2 P) (hY_mean : ∫ ω, Y ω ∂P = 0) :
    IsProbabilityMeasure (rowZeroBiasLaw P Y) := by
  unfold rowZeroBiasLaw
  split_ifs with hpos
  · exact (zeroBias_law_characterization (Ω' := ℝ) P hY_L2 hY_mean hpos).2.2.1
  · infer_instance

private lemma isZeroBias_rowZeroBiasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_L2 : MemLp Y 2 P) (hY_mean : ∫ ω, Y ω ∂P = 0) :
    IsZeroBias P Y (rowZeroBiasLaw P Y) id := by
  unfold rowZeroBiasLaw
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

private noncomputable def rowIndexLaw
    {k : ℕ} (σ2 : Fin k → ℝ) : Measure (Fin k) :=
  ∑ i : Fin k, ENNReal.ofReal (σ2 i) • Measure.dirac i

private lemma isProbabilityMeasure_rowIndexLaw
    {k : ℕ} {σ2 : Fin k → ℝ} (hnn : ∀ i : Fin k, 0 ≤ σ2 i)
    (hsum : (∑ i : Fin k, σ2 i) = 1) :
    IsProbabilityMeasure (rowIndexLaw σ2) := by
  constructor
  simp only [rowIndexLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hnn i, hsum, ENNReal.ofReal_one]

private lemma rowIndexLaw_real_singleton
    {k : ℕ} {σ2 : Fin k → ℝ} (hnn : ∀ i : Fin k, 0 ≤ σ2 i) (i : Fin k) :
    (rowIndexLaw σ2).real {i} = σ2 i := by
  have happly : rowIndexLaw σ2 {i} = ENNReal.ofReal (σ2 i) := by
    simp only [rowIndexLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton i), smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hnot : j ∉ ({i} : Set (Fin k)) := hji
      simp [hnot]
    · intro h; exact False.elim (h (Finset.mem_univ _))
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

/-- **Section 3.5.2 Lindeberg Sufficiency** (`Sec3_5_2_lindeberg_sufficient`, eq. `(3.34)`
`\label{85}`, `SteinIntro.tex:1560-1564`; `ISSUE-3.22` prose note): for a triangular array of
row-wise independent mean-zero $L^2$ random variables $(X_{i,n})_{0 \le i \le n}$ with unit row
variance $\operatorname{Var}(\sum_{i=0}^n X_{i,n}) = 1$, the Lindeberg condition `(3.34)` implies
weak convergence $W_n = \sum_{i=0}^n X_{i,n} \xrightarrow{d} \mathcal{N}(0, 1)$, without assuming
pre-existing zero-bias or random-index variables on `Ω`. -/
theorem tendsto_stdNormalLaw_of_lindeberg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (n : ℕ) → Fin (n + 1) → Ω → ℝ}
    (hX_meas : ∀ n i, Measurable (X n i))
    (hX_indep : ∀ n, iIndepFun (X n) P)
    (hX_L2 : ∀ n i, MemLp (X n i) 2 P)
    (hX_mean : ∀ n i, ∫ ω, X n i ω ∂P = 0)
    (hVar : ∀ n, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1)
    (hLind : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ ∑ i : Fin (n + 1),
        ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
        atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      atTop (𝓝 stdNormalLaw.toProbabilityMeasure) := by
  have hVar_sum : ∀ n, (∑ i : Fin (n + 1), ProbabilityTheory.variance (X n i) P) = 1 := fun n ↦ by
    have hfn : (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) = ∑ i ∈ Finset.univ, X n i := by ext; simp
    rw [← hVar n, hfn, IndepFun.variance_sum (fun i _ ↦ hX_L2 n i)
      (fun i _ j _ hij ↦ (hX_indep n).indepFun hij)]
  let Ω_row : ℕ → Type _ := fun n ↦ (Ω × (Fin (n + 1) → ℝ)) × Fin (n + 1)
  let νz : ∀ n, Fin (n + 1) → Measure ℝ := fun n i ↦ rowZeroBiasLaw P (X n i)
  have hνz_prob : ∀ n i, IsProbabilityMeasure (νz n i) :=
    fun n i ↦ isProbabilityMeasure_rowZeroBiasLaw P (hX_L2 n i) (hX_mean n i)
  let μZ : ∀ n, Measure (Fin (n + 1) → ℝ) := fun n ↦
    @Measure.pi (Fin (n + 1)) (fun _ ↦ ℝ) _ _ (νz n)
  have hμZ_prob : ∀ n, IsProbabilityMeasure (μZ n) := fun n ↦ by
    have : ∀ i, IsProbabilityMeasure (νz n i) := hνz_prob n
    dsimp [μZ]; infer_instance
  let μI : ∀ n, Measure (Fin (n + 1)) := fun n ↦
    rowIndexLaw (fun i ↦ ProbabilityTheory.variance (X n i) P)
  have hμI_prob : ∀ n, IsProbabilityMeasure (μI n) := fun n ↦
    isProbabilityMeasure_rowIndexLaw (fun i ↦ ProbabilityTheory.variance_nonneg (X n i) P)
      (hVar_sum n)
  let Q : ∀ n, Measure (Ω_row n) := fun n ↦ (P.prod (μZ n)).prod (μI n)
  have hQ_prob : ∀ n, IsProbabilityMeasure (Q n) := fun n ↦ by
    have := hμZ_prob n
    have := hμI_prob n
    dsimp [Q]; infer_instance
  let X_lift : ∀ n, Fin (n + 1) → Ω_row n → ℝ := fun n i p ↦ X n i p.1.1
  let Xz_lift : ∀ n, Fin (n + 1) → Ω_row n → ℝ := fun n i p ↦ p.1.2 i
  let I_lift : ∀ n, Ω_row n → Fin (n + 1) := fun n p ↦ p.2
  have hπ1 : ∀ n, MeasurePreserving (fun p : Ω_row n ↦ p.1) (Q n) (P.prod (μZ n)) := fun n ↦ by
    have := hμZ_prob n
    have := hμI_prob n
    exact measurePreserving_fst
  have hπX : ∀ n, MeasurePreserving (fun p : Ω_row n ↦ p.1.1) (Q n) P := fun n ↦ by
    have := hμZ_prob n
    exact measurePreserving_fst.comp (hπ1 n)
  have hπZ : ∀ n, MeasurePreserving (fun p : Ω_row n ↦ p.1.2) (Q n) (μZ n) := fun n ↦ by
    have := hμZ_prob n
    exact measurePreserving_snd.comp (hπ1 n)
  have hπI : ∀ n, MeasurePreserving (I_lift n) (Q n) (μI n) := fun n ↦ by
    have := hμZ_prob n
    have := hμI_prob n
    exact measurePreserving_snd
  have hid_X : ∀ n i, IdentDistrib (X_lift n i) (X n i) (Q n) P := fun n i ↦
    ⟨((hX_meas n i).comp (hπX n).measurable).aemeasurable, (hX_meas n i).aemeasurable, by
      change (Q n).map (X n i ∘ fun p : Ω_row n ↦ p.1.1) = P.map (X n i)
      rw [← Measure.map_map (hX_meas n i) (hπX n).measurable, (hπX n).map_eq]⟩
  have hid_Xz : ∀ n i, IdentDistrib (Xz_lift n i) id (Q n) (νz n i) := fun n i ↦ by
    have : ∀ j, IsProbabilityMeasure (νz n j) := hνz_prob n
    have heval : MeasurePreserving (Function.eval i) (μZ n) (νz n i) :=
      measurePreserving_eval (μ := νz n) i
    have hcomp : MeasurePreserving (Xz_lift n i) (Q n) (νz n i) := heval.comp (hπZ n)
    exact ⟨hcomp.measurable.aemeasurable, aemeasurable_id, by rw [hcomp.map_eq, Measure.map_id]⟩
  have hX_lift_meas : ∀ n i, Measurable (X_lift n i) :=
    fun n i ↦ (hX_meas n i).comp (measurable_fst.comp measurable_fst)
  have hXz_lift_meas : ∀ n i, Measurable (Xz_lift n i) :=
    fun n i ↦ (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have hI_lift_meas : ∀ n, Measurable (I_lift n) := fun _ ↦ measurable_snd
  have hX_lift_indep : ∀ n, iIndepFun (X_lift n) (Q n) :=
    fun n ↦ iIndepFun_comp_measurePreserving (hπX n) (hX_meas n) (hX_indep n)
  have hX_lift_L2 : ∀ n i, MemLp (X_lift n i) 2 (Q n) :=
    fun n i ↦ (hid_X n i).symm.memLp_snd (hX_L2 n i)
  have hX_lift_mean : ∀ n i, ∫ p, X_lift n i p ∂(Q n) = 0 :=
    fun n i ↦ (hid_X n i).integral_eq.trans (hX_mean n i)
  have hVar_lift_sum :
      ∀ n, (∑ i : Fin (n + 1), ProbabilityTheory.variance (X_lift n i) (Q n)) = 1 := fun n ↦ by
    simp_rw [(hid_X n _).variance_eq]
    exact hVar_sum n
  have hXz_lift_zb : ∀ n i, IsZeroBias (Q n) (X_lift n i) (Q n) (Xz_lift n i) := fun n i ↦
    (isZeroBias_rowZeroBiasLaw P (hX_L2 n i) (hX_mean n i)).congr_identDistrib
      (hid_X n i).symm (hid_Xz n i).symm
  have hXz_lift_indep : ∀ n i,
      IndepFun (Xz_lift n i) (fun p (j : {j : Fin (n + 1) // j ≠ i}) ↦ X_lift n j p) (Q n) :=
    fun n i ↦ by
      have := hμZ_prob n
      have hm1 : Measurable (fun ω : Ω ↦ fun j : {j : Fin (n + 1) // j ≠ i} ↦ X n j.1 ω) :=
        Measurable.of_eval fun j ↦ hX_meas n j.1
      have hm2 : Measurable (fun z : Fin (n + 1) → ℝ ↦ z i) := measurable_pi_apply i
      have hbase := (indepFun_prod (μ := P) (ν := μZ n) hm1 hm2).symm
      exact indepFun_comp_measurePreserving (hπ1 n)
        (hm2.comp measurable_snd) (hm1.comp measurable_fst) hbase
  have hI_lift_prob : ∀ n i,
      (Q n).real (I_lift n ⁻¹' {i}) = ProbabilityTheory.variance (X_lift n i) (Q n) :=
    fun n i ↦ by
      have hpre : (Q n) (I_lift n ⁻¹' {i}) = μI n {i} :=
        (hπI n).measure_preimage (measurableSet_singleton i).nullMeasurableSet
      rw [measureReal_def, hpre, ← measureReal_def,
        rowIndexLaw_real_singleton (fun j ↦ ProbabilityTheory.variance_nonneg (X n j) P) i,
        (hid_X n i).variance_eq]
  have hI_lift_indep : ∀ n,
      IndepFun (I_lift n) (fun p ↦ (fun i ↦ X_lift n i p, fun i ↦ Xz_lift n i p)) (Q n) :=
    fun n ↦ by
      have := hμZ_prob n
      have := hμI_prob n
      have hm_pair : Measurable (fun q : Ω × (Fin (n + 1) → ℝ) ↦
          (fun i ↦ X n i q.1, fun i ↦ q.2 i)) :=
        (Measurable.of_eval fun i ↦ (hX_meas n i).comp measurable_fst).prodMk
          (Measurable.of_eval fun i ↦ (measurable_pi_apply i).comp measurable_snd)
      exact (indepFun_prod (μ := P.prod (μZ n)) (ν := μI n) hm_pair measurable_id).symm
  have hLind_lift : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ ∑ i : Fin (n + 1),
        ∫ p, (X_lift n i p) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X_lift n i p) ∂(Q n))
        atTop (𝓝 0) := fun ε hε ↦ by
    have heq : ∀ n, (∑ i : Fin (n + 1),
          ∫ p, (X_lift n i p) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X_lift n i p) ∂(Q n)) =
        ∑ i : Fin (n + 1),
          ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P := fun n ↦ by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hg_meas : Measurable (fun x : ℝ ↦ x ^ 2 * {t : ℝ | ε < |t|}.indicator 1 x) :=
        (measurable_id.pow_const 2).mul
          (measurable_one.indicator (measurableSet_lt measurable_const continuous_abs.measurable))
      exact ((hid_X n i).comp hg_meas).integral_eq
    simp_rw [heq]
    exact hLind ε hε
  have hTail_Xz := (lindeberg_iff_row_zeroBias_tail_tendsto Q hX_lift_meas hXz_lift_meas
    hX_lift_L2 hXz_lift_zb hI_lift_meas hI_lift_prob hI_lift_indep).mp hLind_lift
  have hWeak_lift := row_tendsto_stdNormalLaw_of_zeroBias_tail_tendsto Q hX_lift_meas
    hXz_lift_meas hX_lift_indep hX_lift_L2 hX_lift_mean hVar_lift_sum hXz_lift_zb
    hXz_lift_indep hI_lift_meas hI_lift_prob hI_lift_indep hTail_Xz
  have hmap_eq : ∀ n : ℕ,
      (Q n).map (fun p ↦ ∑ i : Fin (n + 1), X_lift n i p) =
        P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) := fun n ↦ by
    have hsum_meas : Measurable (fun ω : Ω ↦ ∑ i : Fin (n + 1), X n i ω) :=
      Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas n i
    change (Q n).map ((fun ω ↦ ∑ i : Fin (n + 1), X n i ω) ∘ fun p : Ω_row n ↦ p.1.1) = _
    rw [← Measure.map_map hsum_meas (hπX n).measurable, (hπX n).map_eq]
  refine hWeak_lift.congr fun n ↦ ?_
  ext1
  simp only [Measure.coe_toProbabilityMeasure, hmap_eq n]

end Sufficiency

/-! ### Section 2: Non-Necessity of Lindeberg Without Negligible Summands -/

/-- **Section 3.5.2 Non-Necessity of Lindeberg Without Feller Condition**
(`Sec3_5_2_lindeberg_not_necessary_corrected`, `SteinIntro.tex:1565-1566`; `ISSUE-3.5.2-PROSE`):
there exists a triangular array of row-wise independent mean-zero $L^2$ random variables with unit
row variance whose row sums converge in distribution to $\mathcal{N}(0, 1)$, yet the Lindeberg
condition `(3.34)` fails (because $\max_i \sigma_{i,n}^2 \equiv 1 \not\to 0$). -/
theorem lindeberg_not_necessary_for_clt :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : (n : ℕ) → Fin (n + 1) → Ω → ℝ),
      (∀ n i, Measurable (X n i)) ∧
      (∀ n, iIndepFun (X n) P) ∧
      (∀ n i, MemLp (X n i) 2 P) ∧
      (∀ n i, ∫ ω, X n i ω ∂P = 0) ∧
      (∀ n, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) ∧
      Tendsto (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
        atTop (𝓝 stdNormalLaw.toProbabilityMeasure) ∧
      ¬ (∀ ε : ℝ, 0 < ε →
          Tendsto (fun n : ℕ ↦ ∑ i : Fin (n + 1),
            ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
            atTop (𝓝 0)) := by
  let X : (n : ℕ) → Fin (n + 1) → ℝ → ℝ := fun _ i ω ↦ if i = 0 then ω else 0
  have hsum_id : ∀ (n : ℕ) (ω : ℝ), (∑ i : Fin (n + 1), X n i ω) = ω := fun n ω ↦ by
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp [X]
    · intro i _ hi
      simp [X, hi]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  refine ⟨ℝ, inferInstance, stdNormalLaw, inferInstance, X, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n i
    by_cases hi : i = 0
    · have hXi : X n i = id := by ext ω; simp [X, hi]
      rw [hXi]; exact measurable_id
    · have hXi : X n i = fun _ ↦ (0 : ℝ) := by ext ω; simp [X, hi]
      rw [hXi]; exact measurable_const
  · intro n
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _
    by_cases hex : ∃ j ∈ S, X n j ⁻¹' sets j = ∅
    · rcases hex with ⟨j, hjS, hj0⟩
      have hinter0 : (⋂ i ∈ S, X n i ⁻¹' sets i) = ∅ :=
        subset_empty_iff.mp ((biInter_subset_of_mem hjS).trans (le_of_eq hj0))
      rw [hinter0, measure_empty, eq_comm]
      exact Finset.prod_eq_zero hjS (by rw [hj0, measure_empty])
    · have hconst_univ : ∀ j ∈ S, j ≠ 0 → X n j ⁻¹' sets j = univ := fun j hjS hjne ↦ by
        have hne : (X n j ⁻¹' sets j).Nonempty :=
          Set.nonempty_iff_ne_empty.mpr fun h ↦ hex ⟨j, hjS, h⟩
        rcases hne with ⟨ω₀, hω₀⟩
        have h0mem : (0 : ℝ) ∈ sets j := by simpa [X, hjne] using hω₀
        ext ω
        simp [X, hjne, h0mem]
      by_cases h0S : (0 : Fin (n + 1)) ∈ S
      · have hinter : (⋂ i ∈ S, X n i ⁻¹' sets i) = X n 0 ⁻¹' sets 0 := by
          refine Subset.antisymm (biInter_subset_of_mem h0S) (subset_iInter₂ fun j hjS ↦ ?_)
          by_cases hj0 : j = 0
          · subst hj0; exact Subset.rfl
          · rw [hconst_univ j hjS hj0]; exact subset_univ _
        rw [hinter, ← Finset.mul_prod_erase S _ h0S]
        have hprod1 : (∏ j ∈ S.erase 0, stdNormalLaw (X n j ⁻¹' sets j)) = 1 :=
          Finset.prod_eq_one fun j hj ↦ by
            have hj0 : j ≠ 0 := Finset.ne_of_mem_erase hj
            rw [hconst_univ j (Finset.mem_of_mem_erase hj) hj0, measure_univ]
        rw [hprod1, mul_one]
      · have hinter : (⋂ i ∈ S, X n i ⁻¹' sets i) = univ :=
          univ_subset_iff.mp (subset_iInter₂ fun j hjS ↦ by
            have hj0 : j ≠ 0 := fun h ↦ h0S (h ▸ hjS)
            rw [hconst_univ j hjS hj0])
        rw [hinter, measure_univ, eq_comm]
        exact Finset.prod_eq_one fun j hjS ↦ by
          have hj0 : j ≠ 0 := fun h ↦ h0S (h ▸ hjS)
          rw [hconst_univ j hjS hj0, measure_univ]
  · intro n i
    by_cases hi : i = 0
    · have hXi : X n i = id := by ext ω; simp [X, hi]
      rw [hXi]; exact memLp_id_gaussianReal 2
    · have hXi : X n i = fun _ ↦ (0 : ℝ) := by ext ω; simp [X, hi]
      rw [hXi]; exact memLp_const 0
  · intro n i
    by_cases hi : i = 0
    · have hXi : X n i = id := by ext ω; simp [X, hi]
      rw [hXi, stdNormalLaw]; simp
    · have hXi : X n i = fun _ ↦ (0 : ℝ) := by ext ω; simp [X, hi]
      rw [hXi]; simp
  · intro n
    simp_rw [hsum_id]
    simp [stdNormalLaw]
  · have hmap : ∀ n : ℕ,
        (stdNormalLaw.map (fun ω : ℝ ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure =
          stdNormalLaw.toProbabilityMeasure := fun n ↦ by
      ext1
      simp_rw [hsum_id]
      simp only [Measure.coe_toProbabilityMeasure]
      rw [show (fun ω : ℝ ↦ ω) = id from rfl, Measure.map_id]
    simp_rw [hmap]
    exact tendsto_const_nhds
  · intro hLind
    have h1 := hLind 1 zero_lt_one
    let c : ℝ := ∫ ω, ω ^ 2 * {x : ℝ | 1 < |x|}.indicator 1 ω ∂stdNormalLaw
    have hconst : ∀ n : ℕ,
        (∑ i : Fin (n + 1),
          ∫ ω, (X n i ω) ^ 2 * {x : ℝ | 1 < |x|}.indicator 1 (X n i ω) ∂stdNormalLaw) = c :=
      fun n ↦ by
        rw [Finset.sum_eq_single (0 : Fin (n + 1))]
        · simp [X, c]
        · intro i _ hi
          simp [X, hi]
        · intro h; exact False.elim (h (Finset.mem_univ _))
    simp_rw [hconst] at h1
    have hc0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds h1
    have hc_int : Integrable (fun ω : ℝ ↦ ω ^ 2 * {x : ℝ | 1 < |x|}.indicator 1 ω)
        stdNormalLaw := by
      have hid2 : Integrable (fun ω : ℝ ↦ ω ^ 2) stdNormalLaw :=
        (memLp_id_gaussianReal 2 : MemLp id 2 stdNormalLaw).integrable_sq
      refine hid2.mono'
        ((measurable_id.pow_const 2).mul
          (measurable_one.indicator
            (measurableSet_lt measurable_const continuous_abs.measurable))).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      by_cases hω : 1 < |ω|
      · have hm : ω ∈ {x : ℝ | 1 < |x|} := hω
        rw [indicator_of_mem hm, Pi.one_apply, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _)]
      · have hn : ω ∉ {x : ℝ | 1 < |x|} := hω
        simp [hn, sq_nonneg]
    have hIoo_le : stdNormalLaw.real (Ioo (1 : ℝ) 2) ≤ c := by
      rw [← integral_indicator_one measurableSet_Ioo]
      refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Ioo)
        hc_int fun ω ↦ ?_
      by_cases hω : ω ∈ Ioo (1 : ℝ) 2
      · have hm : ω ∈ {x : ℝ | 1 < |x|} := by
          change 1 < |ω|; exact hω.1.trans_le (le_abs_self ω)
        rw [indicator_of_mem hω, indicator_of_mem hm, Pi.one_apply, mul_one]
        nlinarith [hω.1]
      · rw [indicator_of_notMem hω]
        exact mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    have hIoo_pos : 0 < stdNormalLaw.real (Ioo (1 : ℝ) 2) := by
      have hpdf_eq : stdNormalLaw.real (Ioo (1 : ℝ) 2) = ∫ t in Ioo (1 : ℝ) 2, stdNormalPDF t := by
        rw [← integral_indicator_one measurableSet_Ioo]
        change stdNormalExpect ((Ioo (1 : ℝ) 2).indicator 1) = _
        rw [stdNormalExpect_eq_integral_mul_pdf, ← integral_indicator measurableSet_Ioo]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        by_cases ht : t ∈ Ioo (1 : ℝ) 2 <;> simp [ht]
      rw [hpdf_eq]
      have hconst_int : IntegrableOn (fun _ : ℝ ↦ stdNormalPDF 2) (Ioo (1 : ℝ) 2) volume :=
        integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne)
      have hpdf_int : IntegrableOn stdNormalPDF (Ioo (1 : ℝ) 2) volume := by
        have h1 : Integrable (fun _ : ℝ ↦ (1 : ℝ)) stdNormalLaw := integrable_const 1
        have hp : Integrable stdNormalPDF volume := by
          simpa using integrable_stdNormalLaw_iff.mp h1
        exact hp.integrableOn
      have hconst_le : ∫ _ in Ioo (1 : ℝ) 2, stdNormalPDF 2 ≤
          ∫ t in Ioo (1 : ℝ) 2, stdNormalPDF t := by
        refine setIntegral_mono_on hconst_int hpdf_int measurableSet_Ioo fun t ht ↦ ?_
        rw [stdNormalPDF_eq, stdNormalPDF_eq]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        nlinarith [ht.1, ht.2]
      have hconst_pos : 0 < ∫ _ in Ioo (1 : ℝ) 2, stdNormalPDF 2 := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
        linarith [stdNormalPDF_pos 2]
      exact hconst_pos.trans_le hconst_le
    linarith

end SteinMethod
