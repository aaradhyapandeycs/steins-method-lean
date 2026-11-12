/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Branching.Extinction
import Formalization.Exponential.Equilibrium
import Mathlib.MeasureTheory.Measure.Count

/-!
# Size-Bias Galton–Watson Trees and Lyons–Pemantle–Peres Spine Coupling
(`Formalization.Branching.SizeBiasTree`)

Develops the Lyons–Pemantle–Peres size-bias tree construction and spine properties from
Section 5.3 of Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`,
`SteinIntro.tex:3030-3139`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-!
### 1. Discrete Measure Equality, Pullback Independence, and Discrete Size-Bias Characterization
-/

/-- Two finite measures on a countable discrete measurable space are equal if and only if they
assign the same real measure to every singleton. -/
theorem measure_eq_of_measureReal_singleton {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [Countable α]
    (μ₁ μ₂ : Measure α) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ x : α, μ₁.real {x} = μ₂.real {x}) :
    μ₁ = μ₂ := by
  ext B _
  rw [← ofReal_measureReal (measure_ne_top μ₁ B),
    ← ofReal_measureReal (measure_ne_top μ₂ B)]
  congr 1
  have h1 := (measureReal_inter_fiber_tsum μ₁ MeasurableSet.univ measurable_id
    (fun x : α ↦ x ∈ B)).1
  have h2 := (measureReal_inter_fiber_tsum μ₂ MeasurableSet.univ measurable_id
    (fun x : α ↦ x ∈ B)).1
  simp only [univ_inter, id_eq] at h1 h2
  change μ₁.real {x : α | x ∈ B} = μ₂.real {x : α | x ∈ B}
  rw [← h1, ← h2]
  congr 1
  ext x
  exact h x.1

/-- Pushforward measures of two `AEMeasurable` maps into a countable discrete measurable space are
equal whenever their point-mass `measureReal` values agree. -/
theorem map_eq_of_measureReal_eq {Ω₁ Ω₂ α : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [Countable α]
    {P₁ : Measure Ω₁} [IsFiniteMeasure P₁] {P₂ : Measure Ω₂} [IsFiniteMeasure P₂]
    {f : Ω₁ → α} {g : Ω₂ → α} (hf : AEMeasurable f P₁) (hg : AEMeasurable g P₂)
    (h : ∀ x : α, P₁.real {ω | f ω = x} = P₂.real {ω | g ω = x}) :
    P₁.map f = P₂.map g := by
  have : IsFiniteMeasure (P₁.map f) := Measure.isFiniteMeasure_map P₁ f
  have : IsFiniteMeasure (P₂.map g) := Measure.isFiniteMeasure_map P₂ g
  refine measure_eq_of_measureReal_singleton (P₁.map f) (P₂.map g) fun x ↦ ?_
  rw [map_measureReal_apply_of_aemeasurable hf (measurableSet_singleton x),
    map_measureReal_apply_of_aemeasurable hg (measurableSet_singleton x)]
  exact h x

/-- Pullback of `iIndepFun` along a measure-preserving measurable map
$g : \Omega_1 \to \Omega_2$. -/
theorem iIndepFun_comp_map {Ω₁ Ω₂ ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (f : ∀ i, Ω₂ → β i) (g : Ω₁ → Ω₂)
    (hf : ∀ i, Measurable (f i)) (hg : Measurable g) (hmap : P₁.map g = P₂)
    (hind : iIndepFun f P₂) :
    iIndepFun (fun i ω₁ ↦ f i (g ω₁)) P₁ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro S sets hsets
  have hpre : ∀ i ∈ S,
      P₁ ((fun ω₁ ↦ f i (g ω₁)) ⁻¹' sets i) = P₂ (f i ⁻¹' sets i) := by
    intro i hi
    have h1 : (fun ω₁ ↦ f i (g ω₁)) ⁻¹' sets i = g ⁻¹' (f i ⁻¹' sets i) := rfl
    rw [h1, ← Measure.map_apply hg (hf i (hsets i hi)), hmap]
  have hinter : (⋂ i ∈ S, (fun ω₁ ↦ f i (g ω₁)) ⁻¹' sets i) =
      g ⁻¹' (⋂ i ∈ S, f i ⁻¹' sets i) := by
    ext ω₁; simp
  have hmeas_inter : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) :=
    MeasurableSet.biInter S.countable_toSet fun i hi ↦ hf i (hsets i hi)
  rw [hinter, ← Measure.map_apply hg hmeas_inter, hmap, hind S hsets]
  exact Finset.prod_congr rfl fun i hi ↦ (hpre i hi).symm

/-- Pullback of `IndepFun` along a measure-preserving measurable map $g : \Omega_1 \to \Omega_2$. -/
theorem indepFun_comp_map {Ω₁ Ω₂ β₁ β₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace β₁] [MeasurableSpace β₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    (f₁ : Ω₂ → β₁) (f₂ : Ω₂ → β₂) (g : Ω₁ → Ω₂)
    (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (hg : Measurable g) (hmap : P₁.map g = P₂)
    (hind : IndepFun f₁ f₂ P₂) :
    IndepFun (fun ω₁ ↦ f₁ (g ω₁)) (fun ω₁ ↦ f₂ (g ω₁)) P₁ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro s₁ s₂ hs₁ hs₂
  have hpre₁ : (fun ω₁ ↦ f₁ (g ω₁)) ⁻¹' s₁ = g ⁻¹' (f₁ ⁻¹' s₁) := rfl
  have hpre₂ : (fun ω₁ ↦ f₂ (g ω₁)) ⁻¹' s₂ = g ⁻¹' (f₂ ⁻¹' s₂) := rfl
  have hinter : g ⁻¹' (f₁ ⁻¹' s₁) ∩ g ⁻¹' (f₂ ⁻¹' s₂) =
      g ⁻¹' (f₁ ⁻¹' s₁ ∩ f₂ ⁻¹' s₂) := rfl
  rw [hpre₁, hpre₂, hinter,
    ← Measure.map_apply hg ((hf₁ hs₁).inter (hf₂ hs₂)),
    ← Measure.map_apply hg (hf₁ hs₁),
    ← Measure.map_apply hg (hf₂ hs₂), hmap]
  exact hind s₁ s₂ hs₁ hs₂

/-- Functions of the first and second coordinates of a product of probability measures are
independent. -/
theorem indepFun_prod_fst_snd {Ω₁ Ω₂ β₁ β₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace β₁] [MeasurableSpace β₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁]
    (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    (f₁ : Ω₁ → β₁) (f₂ : Ω₂ → β₂) (_hf₁ : Measurable f₁) (_hf₂ : Measurable f₂) :
    IndepFun (fun p : Ω₁ × Ω₂ ↦ f₁ p.1) (fun p : Ω₁ × Ω₂ ↦ f₂ p.2) (μ₁.prod μ₂) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s₁ s₂ hs₁ hs₂
  have hpre₁ : (fun p : Ω₁ × Ω₂ ↦ f₁ p.1) ⁻¹' s₁ = (f₁ ⁻¹' s₁) ×ˢ univ := by
    ext p; simp
  have hpre₂ : (fun p : Ω₁ × Ω₂ ↦ f₂ p.2) ⁻¹' s₂ = univ ×ˢ (f₂ ⁻¹' s₂) := by
    ext p; simp
  have hinter : ((fun p : Ω₁ × Ω₂ ↦ f₁ p.1) ⁻¹' s₁) ∩ ((fun p : Ω₁ × Ω₂ ↦ f₂ p.2) ⁻¹' s₂) =
      (f₁ ⁻¹' s₁) ×ˢ (f₂ ⁻¹' s₂) := by
    ext p; simp
  rw [hinter, hpre₁, hpre₂, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    measure_univ, measure_univ, mul_one, one_mul]

/-- Conditioning and pushforward commute with a measure-preserving measurable map. -/
theorem cond_map_comp_eq {Ω₁ Ω₂ α : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace α]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {g : Ω₁ → Ω₂} {f : Ω₂ → α} {S : Set Ω₂}
    (hg : Measurable g) (hf : Measurable f) (hS : MeasurableSet S)
    (hmap : P₁.map g = P₂) :
    (ProbabilityTheory.cond P₁ (g ⁻¹' S)).map (f ∘ g) =
      (ProbabilityTheory.cond P₂ S).map f := by
  ext B hB
  rw [Measure.map_apply (hf.comp hg) hB, Measure.map_apply hf hB,
    ProbabilityTheory.cond_apply (hg hS), ProbabilityTheory.cond_apply hS]
  have hinter : g ⁻¹' S ∩ (f ∘ g) ⁻¹' B = g ⁻¹' (S ∩ f ⁻¹' B) := rfl
  rw [hinter, ← Measure.map_apply hg hS, ← Measure.map_apply hg (hS.inter (hf hB)), hmap]

/-- Converse to Corollary 3.12 (`sizeBias_nat_pmf`): if $X : \Omega \to \mathbb{N}$ is
a.e.-measurable and integrable with $\mu = \mathbb{E}[X] > 0$ and $S : \Omega' \to \mathbb{N}$ is
a.e.-measurable with $P'(S = k) = k\,P(X = k) / \mu$ for all $k \in \mathbb{N}$, then
$(S : \Omega' \to \mathbb{R})$ has the size-bias distribution of $(X : \Omega \to \mathbb{R})$. -/
theorem isSizeBias_of_nat_measureReal
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℕ} {S : Ω' → ℕ}
    (hX_aem : AEMeasurable X P)
    (hX_int : Integrable (fun ω ↦ (X ω : ℝ)) P)
    (hμ_pos : 0 < ∫ ω, (X ω : ℝ) ∂P)
    (hS_meas : AEMeasurable S P')
    (hpmf : ∀ k : ℕ, P'.real {ω' | S ω' = k} =
      (k : ℝ) * P.real {ω | X ω = k} / ∫ ω, (X ω : ℝ) ∂P) :
    IsSizeBias P (fun ω ↦ (X ω : ℝ)) P' (fun ω' ↦ (S ω' : ℝ)) := by
  set μ : ℝ := ∫ ω, (X ω : ℝ) ∂P
  have hcast_meas : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  set μX : Measure ℕ := P.map X
  have : IsProbabilityMeasure μX := (Measure.isProbabilityMeasure_map_iff hX_aem).mpr ‹_›
  let d : ℕ → ℝ≥0∞ := fun k ↦ ENNReal.ofReal ((k : ℝ) / μ)
  have hd_meas : Measurable d := Measurable.of_discrete
  set μS : Measure ℕ := μX.withDensity d
  have hdiv_int : Integrable (fun k : ℕ ↦ (k : ℝ) / μ) μX := by
    have hid_int : Integrable (fun k : ℕ ↦ (k : ℝ)) μX :=
      (integrable_map_measure hcast_meas.aestronglyMeasurable hX_aem).mpr hX_int
    exact hid_int.div_const μ
  have hdiv_nn : 0 ≤ᵐ[μX] fun k : ℕ ↦ (k : ℝ) / μ :=
    Eventually.of_forall fun k ↦ div_nonneg (Nat.cast_nonneg k) hμ_pos.le
  have hμS_univ : μS univ = 1 := by
    rw [withDensity_apply d MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hdiv_int hdiv_nn,
      integral_div μ (fun k : ℕ ↦ (k : ℝ)),
      integral_map hX_aem hcast_meas.aestronglyMeasurable,
      div_self hμ_pos.ne', ENNReal.ofReal_one]
  have : IsProbabilityMeasure μS := ⟨hμS_univ⟩
  have : IsProbabilityMeasure (P'.map S) :=
    (Measure.isProbabilityMeasure_map_iff hS_meas).mpr ‹_›
  have hmap_eq : P'.map S = μS := by
    refine measure_eq_of_measureReal_singleton (P'.map S) μS fun k ↦ ?_
    rw [map_measureReal_apply_of_aemeasurable hS_meas (measurableSet_singleton k)]
    change P'.real {ω' | S ω' = k} = (μS {k}).toReal
    have hμS_k : μS {k} = d k * μX {k} := by
      rw [withDensity_apply d (measurableSet_singleton k)]
      have hcongr : ∀ x ∈ ({k} : Set ℕ), d x = d k :=
        fun x hx ↦ congrArg d (mem_singleton_iff.mp hx)
      rw [setLIntegral_congr_fun (measurableSet_singleton k) hcongr, setLIntegral_const]
    rw [hμS_k, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg k) hμ_pos.le)]
    have hμX_k : (μX {k}).toReal = P.real {ω | X ω = k} :=
      map_measureReal_apply_of_aemeasurable hX_aem (measurableSet_singleton k)
    rw [hμX_k, hpmf k]
    ring
  refine ⟨Eventually.of_forall fun ω ↦ Nat.cast_nonneg (X ω), hX_int,
    hcast_meas.comp_aemeasurable hS_meas, fun f _ _ ↦ ?_⟩
  have h_rhs : ∫ ω', f (S ω') ∂P' = ∫ k : ℕ, f (k : ℝ) ∂μS := by
    have h1 := integral_map hS_meas
      (Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k : ℝ)).aestronglyMeasurable
    rw [hmap_eq] at h1
    exact h1.symm
  have h_wd : ∫ k : ℕ, f (k : ℝ) ∂μS =
      μ⁻¹ * ∫ ω, (X ω : ℝ) * f (X ω) ∂P := by
    rw [integral_withDensity_eq_integral_toReal_smul hd_meas
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    have hcongr : (fun k : ℕ ↦ (d k).toReal • f (k : ℝ)) =
        fun k : ℕ ↦ μ⁻¹ * ((k : ℝ) * f (k : ℝ)) := by
      ext k
      dsimp only [d]
      rw [ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg k) hμ_pos.le),
        smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hcongr, integral_const_mul]
    congr 1
    exact integral_map hX_aem
      (Measurable.of_discrete : Measurable fun k : ℕ ↦ (k : ℝ) * f (k : ℝ)).aestronglyMeasurable
  rw [h_rhs, h_wd, ← mul_assoc, mul_inv_cancel₀ hμ_pos.ne', one_mul]

/-- In any `IsSizeBiasSpine` for a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$), at each
level $j \in \{1, \dots, n\}$ and for all $k, m \in \mathbb{N}$,
$P'(X_j = k) = (k + 1) P(Z_1 = k + 1)$ and
$P'(X_j = k \wedge A_j = m) = \mathbf{1}_{m \le k} P(Z_1 = k + 1)$. -/
theorem IsSizeBiasSpine.measureReal_X_A
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {X : ℕ → Ω' → ℕ}
    (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    {A : ℕ → Ω' → ℕ} {j : ℕ}
    (hSB : IsSizeBias P (fun ω ↦ (Z 1 ω : ℝ)) P' (fun ω' ↦ (X j ω' : ℝ) + 1))
    (hXA : ∀ k m : ℕ, P'.real {ω' | X j ω' = k ∧ A j ω' = m} =
      if m ≤ k then P'.real {ω' | X j ω' = k} / ((k : ℝ) + 1) else 0)
    (k m : ℕ) :
    P'.real {ω' | X j ω' = k} = ((k : ℝ) + 1) * P.real {ω | Z 1 ω = k + 1} ∧
      P'.real {ω' | X j ω' = k ∧ A j ω' = m} =
        if m ≤ k then P.real {ω | Z 1 ω = k + 1} else 0 := by
  have hμ_pos : 0 < ∫ ω, (Z 1 ω : ℝ) ∂P := by rw [hcrit]; exact zero_lt_one
  have h1 := hSB.measureReal_eq_singleton hμ_pos ((k + 1 : ℕ) : ℝ)
  rw [hcrit, div_one] at h1
  have hset1 : {ω' : Ω' | (X j ω' : ℝ) + 1 = ((k + 1 : ℕ) : ℝ)} = {ω' | X j ω' = k} := by
    ext ω'
    change ((X j ω' : ℝ) + 1 = ((k + 1 : ℕ) : ℝ)) ↔ X j ω' = k
    exact_mod_cast Nat.succ_inj
  have hset2 : {ω : Ω | (Z 1 ω : ℝ) = ((k + 1 : ℕ) : ℝ)} = {ω | Z 1 ω = k + 1} := by
    ext ω
    change ((Z 1 ω : ℝ) = ((k + 1 : ℕ) : ℝ)) ↔ Z 1 ω = k + 1
    exact Nat.cast_inj
  rw [hset1, hset2, Nat.cast_add, Nat.cast_one] at h1
  refine ⟨h1, ?_⟩
  rw [hXA k m, h1]
  have hne : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hne]

/-!
### 2. Canonical Size-Bias Spine Coupling Construction (`Sec5_3_exists_isSizeBiasSpineCoupling`)
-/

instance : MeasurableSpace (Σ k : ℕ, Fin (k + 1)) := ⊤

instance : DiscreteMeasurableSpace (Σ k : ℕ, Fin (k + 1)) := ⟨fun _ ↦ trivial⟩

/-- Canonical state space `Σ k : ℕ, Fin (k + 1)` for a pair `(X_j, A_j)` with `0 ≤ A_j ≤ X_j`. -/
abbrev GWSpineXA : Type := Σ k : ℕ, Fin (k + 1)

/-- Canonical probability measure on `GWSpineXA` assigning mass $P(Z_1 = k + 1)$ to each
$\langle k, m \rangle$. -/
noncomputable def gwSpineXAMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℕ → Ω → ℕ) : Measure GWSpineXA :=
  Measure.count.withDensity (fun q : GWSpineXA ↦ P {ω | Z 1 ω = q.1 + 1})

theorem gwSpineXAMeasure_singleton {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℕ → Ω → ℕ) (q : GWSpineXA) :
    gwSpineXAMeasure P Z {q} = P {ω | Z 1 ω = q.1 + 1} := by
  rw [gwSpineXAMeasure, withDensity_apply _ (measurableSet_singleton q),
    Measure.restrict_singleton, Measure.count_singleton, one_smul,
    lintegral_dirac' _ (Measurable.of_discrete)]

theorem gwSpineXAMeasure_real_singleton {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Z : ℕ → Ω → ℕ) (q : GWSpineXA) :
    (gwSpineXAMeasure P Z).real {q} = P.real {ω | Z 1 ω = q.1 + 1} := by
  rw [measureReal_def, gwSpineXAMeasure_singleton, measureReal_def]

theorem isProbabilityMeasure_gwSpineXAMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) :
    IsProbabilityMeasure (gwSpineXAMeasure P Z) := by
  refine ⟨?_⟩
  rw [gwSpineXAMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count, ENNReal.tsum_sigma']
  have hinner : ∀ k : ℕ,
      (∑' _m : Fin (k + 1), P {ω | Z 1 ω = k + 1}) =
        ((k + 1 : ℕ) : ℝ≥0∞) * P {ω | Z 1 ω = k + 1} := by
    intro k
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  have hZ1_meas : Measurable (gwCanonical ξ' 1) := measurable_gwCanonical hξ'_meas 1
  have hP_congr : ∀ r : ℕ, P {ω | Z 1 ω = r} = P {ω | gwCanonical ξ' 1 ω = r} := by
    intro r
    refine measure_congr ?_
    filter_upwards [hZ_ae 1] with ω hω
    simp [hω]
  have hZ1_set_meas : ∀ r : ℕ, MeasurableSet {ω | gwCanonical ξ' 1 ω = r} :=
    fun r ↦ hZ1_meas (measurableSet_singleton r)
  let E : ℕ → Set Ω := fun k ↦
    if k = 0 then {ω | gwCanonical ξ' 1 ω = 0} ∪ {ω | gwCanonical ξ' 1 ω = 1}
    else {ω | gwCanonical ξ' 1 ω = k + 1}
  have hE_meas : ∀ k, MeasurableSet (E k) := by
    intro k
    by_cases hk : k = 0
    · simp only [E, hk, ↓reduceIte]
      exact (hZ1_set_meas 0).union (hZ1_set_meas 1)
    · simp only [E, hk, ↓reduceIte]
      exact hZ1_set_meas (k + 1)
  have hE_disj : Pairwise (fun j k ↦ Disjoint (E j) (E k)) := by
    intro j k hjk
    refine Set.disjoint_left.2 fun ω hj hk ↦ ?_
    by_cases hj0 : j = 0 <;> by_cases hk0 : k = 0
    · exact hjk (hj0.trans hk0.symm)
    · simp only [E, hj0, hk0, ↓reduceIte, mem_union, mem_ofPred_eq] at hj hk
      omega
    · simp only [E, hj0, hk0, ↓reduceIte, mem_union, mem_ofPred_eq] at hj hk
      omega
    · simp only [E, hj0, hk0, ↓reduceIte, mem_ofPred_eq] at hj hk
      omega
  have hE_union : (⋃ k : ℕ, E k) = univ := by
    ext ω
    simp only [mem_iUnion, mem_univ, iff_true]
    rcases r : gwCanonical ξ' 1 ω with _ | _ | k
    · exact ⟨0, Or.inl r⟩
    · exact ⟨0, Or.inr r⟩
    · refine ⟨k + 1, ?_⟩
      dsimp only [E]
      rw [ite_eq_right_iff.2 fun h ↦ False.elim (Nat.succ_ne_zero k h)]
      exact r
  have hlint_term : ∀ k : ℕ,
      (∑' _m : Fin (k + 1), P {ω | Z 1 ω = k + 1}) =
        ∫⁻ ω in E k, (gwCanonical ξ' 1 ω : ℝ≥0∞) ∂P := by
    intro k
    rw [hinner k, hP_congr (k + 1)]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [E, ↓reduceIte, Nat.zero_add, Nat.cast_one, one_mul]
      have hdisj01 : Disjoint {ω : Ω | gwCanonical ξ' 1 ω = 0}
          {ω : Ω | gwCanonical ξ' 1 ω = 1} := by
        refine Set.disjoint_left.2 fun ω (h0 : gwCanonical ξ' 1 ω = 0)
          (h1 : gwCanonical ξ' 1 ω = 1) ↦ by omega
      rw [lintegral_union (hZ1_set_meas 1) hdisj01]
      have h0 : (∫⁻ ω in {ω | gwCanonical ξ' 1 ω = 0},
          (gwCanonical ξ' 1 ω : ℝ≥0∞) ∂P) = 0 := by
        have hcongr0 : ∀ ω ∈ {ω : Ω | gwCanonical ξ' 1 ω = 0},
            (gwCanonical ξ' 1 ω : ℝ≥0∞) = 0 :=
          fun ω (hω : gwCanonical ξ' 1 ω = 0) ↦ by simp [hω]
        rw [setLIntegral_congr_fun (hZ1_set_meas 0) hcongr0,
          setLIntegral_const, zero_mul]
      have h1 : (∫⁻ ω in {ω | gwCanonical ξ' 1 ω = 1},
          (gwCanonical ξ' 1 ω : ℝ≥0∞) ∂P) = P {ω | gwCanonical ξ' 1 ω = 1} := by
        have hcongr1 : ∀ ω ∈ {ω : Ω | gwCanonical ξ' 1 ω = 1},
            (gwCanonical ξ' 1 ω : ℝ≥0∞) = 1 :=
          fun ω (hω : gwCanonical ξ' 1 ω = 1) ↦ by simp [hω]
        rw [setLIntegral_congr_fun (hZ1_set_meas 1) hcongr1,
          setLIntegral_const, one_mul]
      rw [h0, h1, zero_add]
    · simp only [E, hk0, ↓reduceIte]
      have hcongr : ∀ ω ∈ {ω : Ω | gwCanonical ξ' 1 ω = k + 1},
          (gwCanonical ξ' 1 ω : ℝ≥0∞) = ((k + 1 : ℕ) : ℝ≥0∞) :=
        fun ω hω ↦ congrArg Nat.cast hω
      rw [setLIntegral_congr_fun (hZ1_set_meas (k + 1)) hcongr,
        setLIntegral_const]
  have htsum_eq : (∑' k : ℕ, ∑' _m : Fin (k + 1), P {ω | Z 1 ω = k + 1}) =
      ∑' k : ℕ, ∫⁻ ω in E k, (gwCanonical ξ' 1 ω : ℝ≥0∞) ∂P :=
    tsum_congr hlint_term
  rw [htsum_eq, ← lintegral_iUnion hE_meas hE_disj, hE_union, Measure.restrict_univ]
  have hlint_ae : (fun ω ↦ (gwCanonical ξ' 1 ω : ℝ≥0∞)) =ᵐ[P]
      fun ω ↦ ENNReal.ofReal (Z 1 ω : ℝ) := by
    filter_upwards [hZ_ae 1] with ω hω
    rw [← hω, ENNReal.ofReal_natCast]
  rw [lintegral_congr_ae hlint_ae,
    ← ofReal_integral_eq_lintegral_ofReal hGW.1
      (Eventually.of_forall fun ω ↦ Nat.cast_nonneg (Z 1 ω)),
    hcrit, ENNReal.ofReal_one]

theorem gwSpineXAMeasure_real_fst {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) (k : ℕ) :
    (gwSpineXAMeasure P Z).real {q : GWSpineXA | q.1 = k} =
      ((k : ℝ) + 1) * P.real {ω | Z 1 ω = k + 1} := by
  have : IsProbabilityMeasure (gwSpineXAMeasure P Z) :=
    isProbabilityMeasure_gwSpineXAMeasure P hGW hcrit
  obtain ⟨htsum, _⟩ := measureReal_inter_fiber_tsum (gwSpineXAMeasure P Z)
    MeasurableSet.univ measurable_id (fun q : GWSpineXA ↦ q.1 = k)
  simp only [univ_inter, id_eq] at htsum
  change (gwSpineXAMeasure P Z).real {q : GWSpineXA | q.1 = k} =
    ((k : ℝ) + 1) * P.real {ω | Z 1 ω = k + 1}
  rw [← htsum]
  let e : Fin (k + 1) ≃ {q : GWSpineXA // q.1 = k} :=
    { toFun := fun m ↦ ⟨⟨k, m⟩, rfl⟩
      invFun := fun ⟨⟨k', m⟩, hk⟩ ↦ hk ▸ m
      left_inv := fun _ ↦ rfl
      right_inv := by rintro ⟨⟨k', m⟩, rfl⟩; rfl }
  rw [← e.tsum_eq]
  have hterm : ∀ m : Fin (k + 1),
      (gwSpineXAMeasure P Z).real {q | q = (e m).1} = P.real {ω | Z 1 ω = k + 1} := by
    intro m
    exact gwSpineXAMeasure_real_singleton P Z ⟨k, m⟩
  simp_rw [hterm]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]

theorem gwSpineXAMeasure_real_fst_snd {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (_hGW : IsGaltonWatson P Z) (_hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) (k m : ℕ) :
    (gwSpineXAMeasure P Z).real {q : GWSpineXA | q.1 = k ∧ q.2.1 = m} =
      if m ≤ k then P.real {ω | Z 1 ω = k + 1} else 0 := by
  by_cases hmk : m ≤ k
  · have hlt : m < k + 1 := Nat.lt_succ_of_le hmk
    have hset : {q : GWSpineXA | q.1 = k ∧ q.2.1 = m} = {(⟨k, ⟨m, hlt⟩⟩ : GWSpineXA)} := by
      ext ⟨k', ⟨m', hm'⟩⟩
      change (k' = k ∧ m' = m) ↔ (⟨k', ⟨m', hm'⟩⟩ : Σ r : ℕ, Fin (r + 1)) = ⟨k, ⟨m, hlt⟩⟩
      rw [Sigma.mk.inj_iff]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨rfl, heq_of_eq rfl⟩
      · rintro ⟨rfl, h⟩
        rw [heq_iff_eq, Fin.ext_iff] at h
        exact ⟨rfl, h⟩
    rw [hset, gwSpineXAMeasure_real_singleton, ite_eq_left_iff.2 fun h ↦ False.elim (h hmk)]
  · have hset : {q : GWSpineXA | q.1 = k ∧ q.2.1 = m} = ∅ := by
      ext ⟨k', ⟨m', hm'⟩⟩
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      rintro rfl rfl
      exact hmk (Nat.le_of_lt_succ hm')
    rw [hset, measureReal_empty, ite_eq_right_iff.2 fun h ↦ False.elim (hmk h)]

theorem isSizeBias_gwSpineXAMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) :
    letI : IsProbabilityMeasure (gwSpineXAMeasure P Z) :=
      isProbabilityMeasure_gwSpineXAMeasure P hGW hcrit
    IsSizeBias P (fun ω ↦ (Z 1 ω : ℝ)) (gwSpineXAMeasure P Z) (fun q ↦ (q.1 : ℝ) + 1) := by
  have : IsProbabilityMeasure (gwSpineXAMeasure P Z) :=
    isProbabilityMeasure_gwSpineXAMeasure P hGW hcrit
  have hμ_pos : 0 < ∫ ω, (Z 1 ω : ℝ) ∂P := by rw [hcrit]; exact zero_lt_one
  have hSB := isSizeBias_of_nat_measureReal P (gwSpineXAMeasure P Z)
    (X := Z 1) (S := fun q : GWSpineXA ↦ q.1 + 1) (hGW.aemeasurable_Z 1) hGW.1 hμ_pos
    (Measurable.of_discrete.aemeasurable) fun r ↦ by
      rw [hcrit, div_one]
      rcases r with _ | k
      · have hempty : {q : GWSpineXA | q.1 + 1 = 0} = ∅ := by ext; simp
        rw [hempty, measureReal_empty, Nat.cast_zero, zero_mul]
      · have hset : {q : GWSpineXA | q.1 + 1 = k + 1} = {q | q.1 = k} := by
          ext q; simp
        rw [hset, gwSpineXAMeasure_real_fst P hGW hcrit k, Nat.cast_add, Nat.cast_one]
  simpa [Nat.cast_add, Nat.cast_one] using hSB

/-- Section 5.3 existence of the Lyons–Pemantle–Peres size-bias spine coupling (`I-2`,
`SteinIntro.tex:3030-3044, 3128-3136`): for every critical Galton–Watson branching process with
finite variance and every generation $n \ge 0$, there exists a probability space $(\Omega', P')$
supporting $(X, L, R, R', U)$ satisfying `IsSizeBiasSpineCoupling` (and in particular the
generation-$n$ size $S_n = 1 + \sum_{j=1}^n (L_{n,j} + R_{n,j})$ satisfies $S_n \ge 1$ everywhere,
witnessing the infinite-spine claim at `SteinIntro.tex:3043-3044`). -/
def Sec5_3_exists_isSizeBiasSpineCoupling_stmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    ∀ n : ℕ,
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (X L R R' : ℕ → Ω' → ℕ) (U : Ω' → ℝ),
        IsSizeBiasSpineCoupling P Z P' n X L R R' U ∧
        ∀ ω' : Ω', 1 ≤ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')

theorem sec5_3_exists_isSizeBiasSpineCoupling : Sec5_3_exists_isSizeBiasSpineCoupling_stmt := by
  intro Ω _ P _ Z hGW hcrit _ n
  have : IsProbabilityMeasure (gwSpineXAMeasure P Z) :=
    isProbabilityMeasure_gwSpineXAMeasure P hGW hcrit
  let μZ : ℕ → Measure ℕ := fun m ↦ P.map (Z m)
  have hμZ_prob : ∀ m : ℕ, IsProbabilityMeasure (μZ m) :=
    fun m ↦ (Measure.isProbabilityMeasure_map_iff (hGW.aemeasurable_Z m)).mpr ‹_›
  let Ω_level : Type := GWSpineXA × (ℕ → ℕ)
  let μ_xi : ℕ → Measure (ℕ → ℕ) := fun j ↦ Measure.infinitePi (fun _ : ℕ ↦ μZ (n - j))
  let μ_level : ℕ → Measure Ω_level := fun j ↦ (gwSpineXAMeasure P Z).prod (μ_xi j)
  let Ω_sp : Type := ℕ → Ω_level
  let μ_sp : Measure Ω_sp := Measure.infinitePi μ_level
  let X₀ : ℕ → Ω_sp → ℕ := fun j ω ↦ (ω j).1.1
  let A₀ : ℕ → Ω_sp → ℕ := fun j ω ↦ (ω j).1.2.1
  let ξ₀ : ℕ → ℕ → Ω_sp → ℕ := fun j r ω ↦ (ω j).2 r
  let L₀ : ℕ → Ω_sp → ℕ := fun j ω ↦ ∑ r ∈ Finset.range (A₀ j ω), ξ₀ j r ω
  let R₀ : ℕ → Ω_sp → ℕ := fun j ω ↦ ∑ r ∈ Finset.Ico (A₀ j ω) (X₀ j ω), ξ₀ j r ω
  have hX₀_meas : ∀ j, Measurable (X₀ j) :=
    fun j ↦ (Measurable.of_discrete : Measurable fun q : GWSpineXA ↦ q.1).comp
      (measurable_fst.comp (measurable_pi_apply j))
  have hA₀_meas : ∀ j, Measurable (A₀ j) :=
    fun j ↦ (Measurable.of_discrete : Measurable fun q : GWSpineXA ↦ q.2.1).comp
      (measurable_fst.comp (measurable_pi_apply j))
  have hξ₀_meas : ∀ j r, Measurable (ξ₀ j r) :=
    fun j r ↦ (measurable_pi_apply r).comp (measurable_snd.comp (measurable_pi_apply j))
  have hL₀_meas : ∀ j, Measurable (L₀ j) :=
    fun j ↦ measurable_sum_range (hA₀_meas j) (fun r ↦ hξ₀_meas j r)
  have hR₀_meas : ∀ j, Measurable (R₀ j) := by
    intro j
    have heq : R₀ j = fun ω ↦
        (∑ r ∈ Finset.range (X₀ j ω), ξ₀ j r ω) - L₀ j ω := by
      ext ω
      dsimp only [R₀, L₀]
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt_succ (ω j).1.2.2),
        Nat.add_sub_cancel_left]
    rw [heq]
    exact (measurable_sum_range (hX₀_meas j) (fun r ↦ hξ₀_meas j r)).sub (hL₀_meas j)
  have hlevel_eval : ∀ j : ℕ, μ_sp.map (fun ω : Ω_sp ↦ ω j) = μ_level j :=
    fun j ↦ Measure.infinitePi_map_eval μ_level j
  have hXA_eval : ∀ j : ℕ, μ_sp.map (fun ω : Ω_sp ↦ (ω j).1) = gwSpineXAMeasure P Z := by
    intro j
    have h1 : (fun ω : Ω_sp ↦ (ω j).1) = Prod.fst ∘ (fun ω : Ω_sp ↦ ω j) := rfl
    rw [h1, ← Measure.map_map measurable_fst (measurable_pi_apply j), hlevel_eval j,
      Measure.map_fst_prod, measure_univ, one_smul]
  have hxi_eval : ∀ j : ℕ, μ_sp.map (fun ω : Ω_sp ↦ (ω j).2) = μ_xi j := by
    intro j
    have h1 : (fun ω : Ω_sp ↦ (ω j).2) = Prod.snd ∘ (fun ω : Ω_sp ↦ ω j) := rfl
    rw [h1, ← Measure.map_map measurable_snd (measurable_pi_apply j), hlevel_eval j,
      Measure.map_snd_prod, measure_univ, one_smul]
  have hL₀_pos : ∀ j : ℕ, μ_sp {ω | L₀ j ω = 0} ≠ 0 := by
    intro j
    have hsub : {ω : Ω_sp | A₀ j ω = 0} ⊆ {ω : Ω_sp | L₀ j ω = 0} := by
      intro ω (hω : A₀ j ω = 0)
      simp [L₀, hω]
    have hA0_ne : μ_sp {ω : Ω_sp | A₀ j ω = 0} ≠ 0 := by
      have hpos : 0 < P.real {ω | 0 < (Z 1 ω : ℝ)} :=
        measureReal_pos_of_pos_integral P
          (Eventually.of_forall fun ω ↦ Nat.cast_nonneg (Z 1 ω))
          (by rw [hcrit]; exact zero_lt_one)
      have hex : ∃ k : ℕ, 0 < P.real {ω | Z 1 ω = k + 1} := by
        by_contra! hall
        have hzero : P.real {ω | 0 < Z 1 ω} = 0 := by
          obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
          have hZ1_meas : Measurable (gwCanonical ξ' 1) := measurable_gwCanonical hξ'_meas 1
          have hcongr : P.real {ω | 0 < Z 1 ω} = P.real {ω | 0 < gwCanonical ξ' 1 ω} := by
            refine measureReal_congr ?_
            filter_upwards [hZ_ae 1] with ω hω
            simp [hω]
          rw [hcongr]
          obtain ⟨htsum, _⟩ := measureReal_inter_fiber_tsum P MeasurableSet.univ hZ1_meas
            (fun r : ℕ ↦ 0 < r)
          simp only [univ_inter] at htsum
          rw [← htsum]
          have hfun : (fun x : {r : ℕ // 0 < r} ↦
              P.real {ω | gwCanonical ξ' 1 ω = x.1}) = fun _ ↦ 0 := by
            ext ⟨r, hr⟩
            rcases r with _ | k
            · exact False.elim (Nat.lt_irrefl 0 hr)
            · have hZ1_k : P.real {ω | gwCanonical ξ' 1 ω = k + 1} =
                  P.real {ω | Z 1 ω = k + 1} := by
                refine measureReal_congr ?_
                filter_upwards [hZ_ae 1] with ω hω
                simp [hω]
              rw [hZ1_k]
              exact le_antisymm (hall k) measureReal_nonneg
          rw [hfun, tsum_zero]
        have hcast : {ω : Ω | 0 < (Z 1 ω : ℝ)} = {ω | 0 < Z 1 ω} := by
          ext ω; simp
        rw [hcast, hzero] at hpos
        exact lt_irrefl 0 hpos
      rcases hex with ⟨k, hk⟩
      have hsub_k : {ω : Ω_sp | (ω j).1 = ⟨k, ⟨0, Nat.zero_lt_succ k⟩⟩} ⊆
          {ω : Ω_sp | A₀ j ω = 0} := by
        intro ω hω
        change (ω j).1.2.1 = 0
        rw [hω]
      refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsub_k))
      have hmeas_fst_j : Measurable (fun ω : Ω_sp ↦ (ω j).1) :=
        measurable_fst.comp (measurable_pi_apply j)
      have hpre : {ω : Ω_sp | (ω j).1 = ⟨k, ⟨0, Nat.zero_lt_succ k⟩⟩} =
          (fun ω : Ω_sp ↦ (ω j).1) ⁻¹' {⟨k, ⟨0, Nat.zero_lt_succ k⟩⟩} := rfl
      rw [hpre, ← Measure.map_apply hmeas_fst_j (measurableSet_singleton _),
        hXA_eval j, gwSpineXAMeasure_singleton]
      exact pos_iff_ne_zero.2 fun h0 ↦ hk.ne' (by simp [Measure.real, h0])
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hA0_ne) (measure_mono hsub))
  let μ_R' : ℕ → Measure ℕ :=
    fun j ↦ (ProbabilityTheory.cond μ_sp {ω | L₀ j ω = 0}).map (R₀ j)
  have hμ_R'_prob : ∀ j : ℕ, IsProbabilityMeasure (μ_R' j) := by
    intro j
    have : IsProbabilityMeasure (ProbabilityTheory.cond μ_sp {ω | L₀ j ω = 0}) :=
      ProbabilityTheory.cond_isProbabilityMeasure (hL₀_pos j)
    exact (Measure.isProbabilityMeasure_map_iff (hR₀_meas j).aemeasurable).mpr ‹_›
  let Ω' : Type := (Ω_sp × (ℕ → ℕ)) × ℝ
  let P_sp_R' : Measure (Ω_sp × (ℕ → ℕ)) := μ_sp.prod (Measure.infinitePi μ_R')
  let P' : Measure Ω' := P_sp_R'.prod unitIntervalIooMeasure
  let π_sp : Ω' → Ω_sp := fun ω' ↦ ω'.1.1
  let π_R' : Ω' → (ℕ → ℕ) := fun ω' ↦ ω'.1.2
  let X : ℕ → Ω' → ℕ := fun j ω' ↦ X₀ j (π_sp ω')
  let A : ℕ → Ω' → ℕ := fun j ω' ↦ A₀ j (π_sp ω')
  let ξ : ℕ → ℕ → Ω' → ℕ := fun j r ω' ↦ ξ₀ j r (π_sp ω')
  let L : ℕ → Ω' → ℕ := fun j ω' ↦ L₀ j (π_sp ω')
  let R : ℕ → Ω' → ℕ := fun j ω' ↦ R₀ j (π_sp ω')
  let R' : ℕ → Ω' → ℕ := fun j ω' ↦ π_R' ω' j
  let U : Ω' → ℝ := fun ω' ↦ ω'.2
  have hπ_sp_meas : Measurable π_sp := measurable_fst.comp measurable_fst
  have hπ_R'_meas : Measurable π_R' := measurable_snd.comp measurable_fst
  have hπ_fst_map : P'.map Prod.fst = P_sp_R' := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hπ_sp : P'.map π_sp = μ_sp := by
    change P'.map (Prod.fst ∘ Prod.fst) = μ_sp
    rw [← Measure.map_map measurable_fst measurable_fst, hπ_fst_map,
      Measure.map_fst_prod, measure_univ, one_smul]
  have hπ_R' : P'.map π_R' = Measure.infinitePi μ_R' := by
    change P'.map (Prod.snd ∘ Prod.fst) = Measure.infinitePi μ_R'
    rw [← Measure.map_map measurable_snd measurable_fst, hπ_fst_map,
      Measure.map_snd_prod, measure_univ, one_smul]
  have hπ_U : P'.map U = unitIntervalIooMeasure := by
    change P'.map Prod.snd = unitIntervalIooMeasure
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hX_meas : ∀ j, Measurable (X j) := fun j ↦ (hX₀_meas j).comp hπ_sp_meas
  have hA_meas : ∀ j, Measurable (A j) := fun j ↦ (hA₀_meas j).comp hπ_sp_meas
  have hξ_meas : ∀ j r, Measurable (ξ j r) := fun j r ↦ (hξ₀_meas j r).comp hπ_sp_meas
  have hL_meas : ∀ j, Measurable (L j) := fun j ↦ (hL₀_meas j).comp hπ_sp_meas
  have hR_meas : ∀ j, Measurable (R j) := fun j ↦ (hR₀_meas j).comp hπ_sp_meas
  have hR'_meas : ∀ j, Measurable (R' j) := fun j ↦ (measurable_pi_apply j).comp hπ_R'_meas
  refine ⟨Ω', inferInstance, P', inferInstance, X, L, R, R', U, ?_, fun _ ↦ Nat.le_add_right 1 _⟩
  refine ⟨⟨A, ξ, ?_, fun j _ ↦ ?_⟩, fun j _ ↦ ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. iIndepFun across j ∈ Finset.Icc 1 n
    let φ : ∀ _ : ℕ, Ω_level → ℕ × ℕ × (ℕ → ℕ) :=
      fun _ p ↦ (p.1.1, p.1.2.1, p.2)
    have hφ_meas : ∀ j : ℕ, Measurable (φ j) := fun _ ↦
      ((Measurable.of_discrete : Measurable fun q : GWSpineXA ↦ q.1).comp measurable_fst).prodMk
        (((Measurable.of_discrete : Measurable fun q : GWSpineXA ↦ q.2.1).comp
          measurable_fst).prodMk measurable_snd)
    have hind_sp : iIndepFun (fun j : ℕ ↦ fun ω : Ω_sp ↦ φ j (ω j)) μ_sp :=
      iIndepFun_infinitePi (P := μ_level) (X := φ) hφ_meas
    have hind_P' : iIndepFun (fun j : ℕ ↦ fun ω' : Ω' ↦ φ j (π_sp ω' j)) P' :=
      iIndepFun_comp_map (fun j ω ↦ φ j (ω j)) π_sp
        (by intro j; exact (hφ_meas j).comp (measurable_pi_apply j)) hπ_sp_meas hπ_sp hind_sp
    exact hind_P'.precomp Subtype.val_injective
  · -- 2. Level j properties in IsSizeBiasSpine
    have hmeas_fst_sp : Measurable (fun ω : Ω_sp ↦ (ω j).1) :=
      measurable_fst.comp (measurable_pi_apply j)
    have hmeas_snd_sp : Measurable (fun ω : Ω_sp ↦ (ω j).2) :=
      measurable_snd.comp (measurable_pi_apply j)
    have hmeas_XA : Measurable (fun ω' : Ω' ↦ (π_sp ω' j).1) :=
      hmeas_fst_sp.comp hπ_sp_meas
    have hmeas_xi : Measurable (fun ω' : Ω' ↦ (π_sp ω' j).2) :=
      hmeas_snd_sp.comp hπ_sp_meas
    have hmeas_lvl : Measurable (fun ω' : Ω' ↦ π_sp ω' j) :=
      (measurable_pi_apply j).comp hπ_sp_meas
    have hπ_XA : P'.map (fun ω' : Ω' ↦ (π_sp ω' j).1) = gwSpineXAMeasure P Z := by
      change P'.map ((fun ω : Ω_sp ↦ (ω j).1) ∘ π_sp) = gwSpineXAMeasure P Z
      rw [← Measure.map_map hmeas_fst_sp hπ_sp_meas, hπ_sp, hXA_eval j]
    have hπ_xi : P'.map (fun ω' : Ω' ↦ (π_sp ω' j).2) = μ_xi j := by
      change P'.map ((fun ω : Ω_sp ↦ (ω j).2) ∘ π_sp) = μ_xi j
      rw [← Measure.map_map hmeas_snd_sp hπ_sp_meas, hπ_sp, hxi_eval j]
    have hπ_lvl : P'.map (fun ω' : Ω' ↦ π_sp ω' j) = μ_level j := by
      change P'.map ((fun ω : Ω_sp ↦ ω j) ∘ π_sp) = μ_level j
      rw [← Measure.map_map (measurable_pi_apply j) hπ_sp_meas, hπ_sp, hlevel_eval j]
    refine ⟨(hX_meas j).aemeasurable, (hA_meas j).aemeasurable,
      fun r ↦ (hξ_meas j r).aemeasurable, ?_,
      fun ω' ↦ Nat.le_of_lt_succ (π_sp ω' j).1.2.2,
      fun k m ↦ ?_, ?_, fun r ↦ ?_, ?_, fun _ ↦ rfl, fun _ ↦ rfl⟩
    · -- IsSizeBias P (Z 1) P' (X j + 1)
      have hμ_pos : 0 < ∫ ω, (Z 1 ω : ℝ) ∂P := by rw [hcrit]; exact zero_lt_one
      have hSB := isSizeBias_of_nat_measureReal P P'
        (X := Z 1) (S := fun ω' : Ω' ↦ X j ω' + 1) (hGW.aemeasurable_Z 1) hGW.1 hμ_pos
        ((hX_meas j).add measurable_const).aemeasurable fun r ↦ by
          rw [hcrit, div_one]
          rcases r with _ | k
          · have hempty : {ω' : Ω' | X j ω' + 1 = 0} = ∅ := by ext; simp
            rw [hempty, measureReal_empty, Nat.cast_zero, zero_mul]
          · have hpre : {ω' : Ω' | X j ω' + 1 = k + 1} =
                (fun ω' : Ω' ↦ (π_sp ω' j).1) ⁻¹' {q : GWSpineXA | q.1 = k} := by
              ext ω'; simp [X, X₀]
            rw [hpre, ← map_measureReal_apply hmeas_XA (MeasurableSet.of_discrete),
              hπ_XA, gwSpineXAMeasure_real_fst P hGW hcrit k, Nat.cast_add, Nat.cast_one]
      simpa [Nat.cast_add, Nat.cast_one] using hSB
    · -- Joint PMF of (X j, A j)
      have hpre1 : {ω' : Ω' | X j ω' = k ∧ A j ω' = m} =
          (fun ω' : Ω' ↦ (π_sp ω' j).1) ⁻¹' {q : GWSpineXA | q.1 = k ∧ q.2.1 = m} := rfl
      have hpre2 : {ω' : Ω' | X j ω' = k} =
          (fun ω' : Ω' ↦ (π_sp ω' j).1) ⁻¹' {q : GWSpineXA | q.1 = k} := rfl
      rw [hpre1, hpre2,
        ← map_measureReal_apply hmeas_XA (MeasurableSet.of_discrete),
        ← map_measureReal_apply hmeas_XA (MeasurableSet.of_discrete),
        hπ_XA, gwSpineXAMeasure_real_fst_snd P hGW hcrit k m,
        gwSpineXAMeasure_real_fst P hGW hcrit k]
      have hne : (k : ℝ) + 1 ≠ 0 := by positivity
      rw [mul_div_cancel_left₀ _ hne]
    · -- iIndepFun (ξ j) P'
      have hind_xi : iIndepFun (fun (r : ℕ) (η : ℕ → ℕ) ↦ η r) (μ_xi j) :=
        iIndepFun_infinitePi (P := fun _ : ℕ ↦ μZ (n - j)) (X := fun _ (k : ℕ) ↦ k)
          (fun _ ↦ measurable_id)
      exact iIndepFun_comp_map (fun (r : ℕ) (η : ℕ → ℕ) ↦ η r)
        (fun ω' : Ω' ↦ (π_sp ω' j).2)
        (fun r ↦ measurable_pi_apply r) hmeas_xi hπ_xi hind_xi
    · -- P'.map (ξ j r) = P.map (Z (n - j))
      change P'.map ((fun η : ℕ → ℕ ↦ η r) ∘ (fun ω' : Ω' ↦ (π_sp ω' j).2)) = μZ (n - j)
      rw [← Measure.map_map (measurable_pi_apply r) hmeas_xi,
        hπ_xi, Measure.infinitePi_map_eval]
    · -- IndepFun (X j, A j) (ξ j) P'
      have hind_prod : IndepFun
          (fun p : Ω_level ↦ (p.1.1, p.1.2.1))
          (fun p : Ω_level ↦ p.2)
          (μ_level j) :=
        indepFun_prod_fst_snd (gwSpineXAMeasure P Z) (μ_xi j)
          (fun q : GWSpineXA ↦ (q.1, q.2.1)) id (Measurable.of_discrete) measurable_id
      exact indepFun_comp_map
        (fun p : Ω_level ↦ (p.1.1, p.1.2.1))
        (fun p : Ω_level ↦ p.2)
        (fun ω' : Ω' ↦ π_sp ω' j)
        ((Measurable.of_discrete : Measurable fun q : GWSpineXA ↦ (q.1, q.2.1)).comp
          measurable_fst)
        measurable_snd hmeas_lvl hπ_lvl hind_prod
  · -- 3. R' j law
    refine ⟨(hR'_meas j).aemeasurable, ?_⟩
    change P'.map ((fun η : ℕ → ℕ ↦ η j) ∘ π_R') =
      (ProbabilityTheory.cond P' (π_sp ⁻¹' {ω : Ω_sp | L₀ j ω = 0})).map (R₀ j ∘ π_sp)
    rw [← Measure.map_map (measurable_pi_apply j) hπ_R'_meas, hπ_R',
      Measure.infinitePi_map_eval]
    exact (cond_map_comp_eq hπ_sp_meas (hR₀_meas j)
      (hL₀_meas j (measurableSet_singleton 0)) hπ_sp).symm
  · -- 4. iIndepFun R'
    have hind_R' : iIndepFun (fun (j : ℕ) (η : ℕ → ℕ) ↦ η j) (Measure.infinitePi μ_R') :=
      iIndepFun_infinitePi (P := μ_R') (X := fun _ (k : ℕ) ↦ k) (fun _ ↦ measurable_id)
    exact (iIndepFun_comp_map (fun (j : ℕ) (η : ℕ → ℕ) ↦ η j) π_R'
      (fun j ↦ measurable_pi_apply j) hπ_R'_meas hπ_R' hind_R').precomp Subtype.val_injective
  · -- 5. IndepFun R' (X, L, R)
    let fR' : (ℕ → ℕ) → (Finset.Icc 1 n → ℕ) := fun η j ↦ η j.1
    let fXLR : Ω_sp → (Finset.Icc 1 n → ℕ × ℕ × ℕ) :=
      fun ω j ↦ (X₀ j.1 ω, L₀ j.1 ω, R₀ j.1 ω)
    have hfR'_meas : Measurable fR' :=
      measurable_pi_iff.2 fun j ↦ measurable_pi_apply j.1
    have hfXLR_meas : Measurable fXLR :=
      measurable_pi_iff.2 fun j ↦
        (hX₀_meas j.1).prodMk ((hL₀_meas j.1).prodMk (hR₀_meas j.1))
    have hind_prod := (indepFun_prod_fst_snd μ_sp (Measure.infinitePi μ_R')
      fXLR fR' hfXLR_meas hfR'_meas).symm
    exact indepFun_comp_map
      (fun p : Ω_sp × (ℕ → ℕ) ↦ fR' p.2)
      (fun p : Ω_sp × (ℕ → ℕ) ↦ fXLR p.1)
      Prod.fst
      (hfR'_meas.comp measurable_snd)
      (hfXLR_meas.comp measurable_fst) measurable_fst hπ_fst_map hind_prod
  · -- 6. IsUniform U (Ioo 0 1) P'
    exact ⟨measurable_snd.aemeasurable, hπ_U⟩
  · -- 7. IndepFun U ((X, L, R), R')
    let fR' : (ℕ → ℕ) → (Finset.Icc 1 n → ℕ) := fun η j ↦ η j.1
    let fXLR : Ω_sp → (Finset.Icc 1 n → ℕ × ℕ × ℕ) :=
      fun ω j ↦ (X₀ j.1 ω, L₀ j.1 ω, R₀ j.1 ω)
    have hfR'_meas : Measurable fR' :=
      measurable_pi_iff.2 fun j ↦ measurable_pi_apply j.1
    have hfXLR_meas : Measurable fXLR :=
      measurable_pi_iff.2 fun j ↦
        (hX₀_meas j.1).prodMk ((hL₀_meas j.1).prodMk (hR₀_meas j.1))
    have hpair_meas : Measurable (fun p : Ω_sp × (ℕ → ℕ) ↦ (fXLR p.1, fR' p.2)) :=
      (hfXLR_meas.comp measurable_fst).prodMk (hfR'_meas.comp measurable_snd)
    exact (indepFun_prod_fst_snd P_sp_R' unitIntervalIooMeasure
      (fun p : Ω_sp × (ℕ → ℕ) ↦ (fXLR p.1, fR' p.2)) id hpair_meas measurable_id).symm

/-!
### 3. Joint Law of $(S_n, L_n)$ in `IsSizeBiasSpine` and Section 5.3 Items (1)–(4)
-/

private theorem cond_real_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s t : Set Ω) (hs : MeasurableSet s) :
    (ProbabilityTheory.cond μ s).real t = (μ.real s)⁻¹ * μ.real (s ∩ t) := by
  rw [Measure.real, Measure.real, Measure.real,
    ProbabilityTheory.cond_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]

private theorem ae_all_finset {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset α) {p : α → Ω → Prop} (h : ∀ a ∈ s, ∀ᵐ ω ∂μ, p a ω) :
    ∀ᵐ ω ∂μ, ∀ a ∈ s, p a ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Eventually.of_forall fun _ _ ha ↦ False.elim (Finset.notMem_empty _ ha)
  | @insert a s _ ih =>
    filter_upwards [h a (Finset.mem_insert_self a s),
      ih (fun b hb ↦ h b (Finset.mem_insert_of_mem hb))] with ω ha hs b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ha
    · exact hs b hb

private lemma integrable_comp_of_lipschitz {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hW : Integrable W P) (hLip : LipschitzWith K f) :
    Integrable (fun ω ↦ f (W ω)) P := by
  have hdom : Integrable (fun ω ↦ |f 0| + (K : ℝ) * ‖W ω‖) P :=
    (integrable_const |f 0|).add (hW.norm.const_mul (K : ℝ))
  refine hdom.mono'
    (hLip.continuous.measurable.comp_aemeasurable hW.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hd := hLip.dist_le_mul (W ω) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero, ← Real.norm_eq_abs (W ω)] at hd
  rw [Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (f (W ω)) (f 0)]

theorem measureReal_pi_eq_prod_of_iIndepFun {Ω' α : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSingletonClass α]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {ξ : ℕ → Ω' → α} (hξ_indep : iIndepFun ξ P')
    {d : ℕ} {σ : Fin d → ℕ} (hσ : Function.Injective σ) (c : Fin d → α) :
    P'.real {ω' | (fun i : Fin d ↦ ξ (σ i) ω') = c} =
      ∏ i : Fin d, P'.real {ω' | ξ (σ i) ω' = c i} := by
  have hset : {ω' : Ω' | (fun i : Fin d ↦ ξ (σ i) ω') = c} =
      ⋂ i ∈ (Finset.univ : Finset (Fin d)), (fun ω' ↦ ξ (σ i) ω') ⁻¹' {c i} := by
    ext ω'; simp [funext_iff]
  rw [hset, Measure.real,
    (hξ_indep.precomp hσ).measure_inter_preimage_eq_mul Finset.univ
      (fun i _ ↦ measurableSet_singleton (c i)),
    ENNReal.toReal_prod]
  rfl

theorem map_pi_eq_of_iIndepFun {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    {ξ₁ : ℕ → Ω₁ → ℕ} {ξ₂ : ℕ → Ω₂ → ℕ}
    (hξ₁_meas : ∀ r, Measurable (ξ₁ r)) (hξ₂_meas : ∀ r, Measurable (ξ₂ r))
    (hξ₁_indep : iIndepFun ξ₁ P₁) (hξ₂_indep : iIndepFun ξ₂ P₂)
    {d : ℕ} {σ₁ σ₂ : Fin d → ℕ} (hσ₁ : Function.Injective σ₁) (hσ₂ : Function.Injective σ₂)
    (hmap : ∀ i : Fin d, P₁.map (ξ₁ (σ₁ i)) = P₂.map (ξ₂ (σ₂ i))) :
    P₁.map (fun ω₁ (i : Fin d) ↦ ξ₁ (σ₁ i) ω₁) =
      P₂.map (fun ω₂ (i : Fin d) ↦ ξ₂ (σ₂ i) ω₂) := by
  refine map_eq_of_measureReal_eq
    (measurable_pi_iff.2 fun i ↦ hξ₁_meas (σ₁ i)).aemeasurable
    (measurable_pi_iff.2 fun i ↦ hξ₂_meas (σ₂ i)).aemeasurable fun c ↦ ?_
  rw [measureReal_pi_eq_prod_of_iIndepFun P₁ hξ₁_indep hσ₁ c,
    measureReal_pi_eq_prod_of_iIndepFun P₂ hξ₂_indep hσ₂ c]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h1 := map_measureReal_apply (hξ₁_meas (σ₁ i)) (measurableSet_singleton (c i)) (μ := P₁)
  have h2 := map_measureReal_apply (hξ₂_meas (σ₂ i)) (measurableSet_singleton (c i)) (μ := P₂)
  rw [hmap i] at h1
  exact h1.symm.trans h2

theorem sum_fin_range_interval_partition (g : ℕ → ℕ) :
    ∀ (m u : ℕ),
      (∑ a : Fin m,
        if (∑ r ∈ Finset.range a.1, g r) ≤ u ∧ u < ∑ r ∈ Finset.range (a.1 + 1), g r
        then (1 : ℝ) else 0) =
      if u < ∑ r ∈ Finset.range m, g r then 1 else 0
  | 0, _ => by simp
  | m + 1, u => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, sum_fin_range_interval_partition g m u,
        Finset.sum_range_succ g m]
      generalize ∑ r ∈ Finset.range m, g r = S
      split_ifs <;> first | omega | ring

theorem measureReal_sum_swap_last {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {m : ℕ}
    {ξj : ℕ → Ω' → ℕ} (hξ_meas : ∀ r, Measurable (ξj r))
    (hξ_indep : iIndepFun ξj P')
    (hξ_law : ∀ r : ℕ, P'.map (ξj r) = P.map (Z m))
    (d k u : ℕ) (a : Fin (d + 1)) :
    P'.real {ω' | (∑ r ∈ Finset.range (d + 1), ξj r ω') = k ∧
        (∑ r ∈ Finset.range a.1, ξj r ω') ≤ u ∧
        u < (∑ r ∈ Finset.range a.1, ξj r ω') + ξj d ω'} =
      P'.real {ω' | (∑ r ∈ Finset.range (d + 1), ξj r ω') = k ∧
        (∑ r ∈ Finset.range a.1, ξj r ω') ≤ u ∧
        u < ∑ r ∈ Finset.range (a.1 + 1), ξj r ω'} := by
  let d_fin : Fin (d + 1) := ⟨d, Nat.lt_succ_self d⟩
  let π : Fin (d + 1) ≃ Fin (d + 1) := Equiv.swap a d_fin
  let Φ₁ : Ω' → (Fin (d + 1) → ℕ) := fun ω' i ↦ ξj (π i).1 ω'
  let Φ₂ : Ω' → (Fin (d + 1) → ℕ) := fun ω' i ↦ ξj i.1 ω'
  have hΦ₁_meas : Measurable Φ₁ := measurable_pi_iff.2 fun i ↦ hξ_meas (π i).1
  have hΦ₂_meas : Measurable Φ₂ := measurable_pi_iff.2 fun i ↦ hξ_meas i.1
  have hmap : P'.map Φ₁ = P'.map Φ₂ :=
    map_pi_eq_of_iIndepFun P' P' hξ_meas hξ_meas hξ_indep hξ_indep
      (Fin.val_injective.comp π.injective) Fin.val_injective
      (fun i ↦ by rw [hξ_law (π i).1, hξ_law i.1])
  let B : Set (Fin (d + 1) → ℕ) :=
    {c | (∑ i : Fin (d + 1), c i) = k ∧
      (∑ i : Fin (d + 1), if i.1 < a.1 then c i else 0) ≤ u ∧
      u < (∑ i : Fin (d + 1), if i.1 < a.1 then c i else 0) + c a}
  have hsum₂ : ∀ ω', (∑ i : Fin (d + 1), Φ₂ ω' i) = ∑ r ∈ Finset.range (d + 1), ξj r ω' :=
    fun ω' ↦ Fin.sum_univ_eq_sum_range (fun r ↦ ξj r ω') (d + 1)
  have hsum₁ : ∀ ω', (∑ i : Fin (d + 1), Φ₁ ω' i) = ∑ r ∈ Finset.range (d + 1), ξj r ω' := by
    intro ω'
    change (∑ i : Fin (d + 1), Φ₂ ω' (π i)) = _
    rw [π.sum_comp, hsum₂ ω']
  have hpref₂ : ∀ ω', (∑ i : Fin (d + 1), if i.1 < a.1 then Φ₂ ω' i else 0) =
      ∑ r ∈ Finset.range a.1, ξj r ω' := by
    intro ω'
    rw [Fin.sum_univ_eq_sum_range (fun r ↦ if r < a.1 then ξj r ω' else 0) (d + 1),
      ← Finset.sum_filter]
    have hfilt : (Finset.range (d + 1)).filter (· < a.1) = Finset.range a.1 := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      have ha := a.2
      omega
    rw [hfilt]
  have hpref₁ : ∀ ω', (∑ i : Fin (d + 1), if i.1 < a.1 then Φ₁ ω' i else 0) =
      ∑ r ∈ Finset.range a.1, ξj r ω' := by
    intro ω'
    rw [← hpref₂ ω']
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : i.1 < a.1
    · have hia : i ≠ a := fun h ↦ by subst h; exact Nat.lt_irrefl _ hi
      have hid : i ≠ d_fin := fun h ↦ by
        have h1 : i.1 = d := congrArg Fin.val h
        have ha := a.2
        omega
      have hπi : π i = i := Equiv.swap_apply_of_ne_of_ne hia hid
      simp [Φ₁, Φ₂, hi, hπi]
    · simp [hi]
  have hpre₁ : Φ₁ ⁻¹' B = {ω' | (∑ r ∈ Finset.range (d + 1), ξj r ω') = k ∧
      (∑ r ∈ Finset.range a.1, ξj r ω') ≤ u ∧
      u < (∑ r ∈ Finset.range a.1, ξj r ω') + ξj d ω'} := by
    ext ω'
    simp only [B, mem_preimage, mem_ofPred_eq, hsum₁ ω', hpref₁ ω']
    have hπa : Φ₁ ω' a = ξj d ω' := by
      change ξj (Equiv.swap a d_fin a).1 ω' = ξj d ω'
      rw [Equiv.swap_apply_left]
    rw [hπa]
  have hpre₂ : Φ₂ ⁻¹' B = {ω' | (∑ r ∈ Finset.range (d + 1), ξj r ω') = k ∧
      (∑ r ∈ Finset.range a.1, ξj r ω') ≤ u ∧
      u < ∑ r ∈ Finset.range (a.1 + 1), ξj r ω'} := by
    ext ω'
    simp only [B, mem_preimage, mem_ofPred_eq, hsum₂ ω', hpref₂ ω']
    have hΦ₂a : (∑ r ∈ Finset.range a.1, ξj r ω') + Φ₂ ω' a =
        ∑ r ∈ Finset.range (a.1 + 1), ξj r ω' :=
      (Finset.sum_range_succ (fun r ↦ ξj r ω') a.1).symm
    rw [hΦ₂a]
  rw [← hpre₁, ← hpre₂,
    ← map_measureReal_apply hΦ₁_meas (MeasurableSet.of_discrete),
    ← map_measureReal_apply hΦ₂_meas (MeasurableSet.of_discrete),
    hmap]

theorem IsGaltonWatson.measureReal_Z_succ_eq_tsum_iid
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) {m : ℕ}
    {ξj : ℕ → Ω' → ℕ} (hξ_meas : ∀ r, Measurable (ξj r))
    (hξ_indep : iIndepFun ξj P')
    (hξ_law : ∀ r : ℕ, P'.map (ξj r) = P.map (Z m)) (k : ℕ) :
    Summable (fun d : ℕ ↦ P.real {ω | Z 1 ω = d} *
        P'.real {ω' | (∑ r ∈ Finset.range d, ξj r ω') = k}) ∧
      (∑' d : ℕ, P.real {ω | Z 1 ω = d} *
        P'.real {ω' | (∑ r ∈ Finset.range d, ξj r ω') = k}) =
        P.real {ω | Z (m + 1) ω = k} := by
  obtain ⟨ξ', hξ'_meas, hξ'_indep, hξ'_ident, hZ_ae⟩ := hGW.exists_measurable_array
  let p : ℕ → ℝ := fun d ↦ P.real {ω | Z 1 ω = d}
  have hTm_meas : Measurable (gwTreeOfArray ξ' m) := measurable_gwTreeOfArray hξ'_meas m
  have hTm1_meas : Measurable (gwTreeOfArray ξ' (m + 1)) :=
    measurable_gwTreeOfArray hξ'_meas (m + 1)
  let μ₁ : Measure ℕ := P.map (Z 1)
  have : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff (hGW.aemeasurable_Z 1)).mpr ‹_›
  let νm : Measure (GWTree m) := P.map (gwTreeOfArray ξ' m)
  have : IsProbabilityMeasure νm :=
    (Measure.isProbabilityMeasure_map_iff hTm_meas.aemeasurable).mpr ‹_›
  let μT : Measure (ℕ → GWTree m) := Measure.infinitePi (fun _ : ℕ ↦ νm)
  let μ_root : Measure (ℕ × (ℕ → GWTree m)) := μ₁.prod μT
  let rootCombine : ℕ × (ℕ → GWTree m) → GWTree (m + 1) :=
    fun q ↦ List.ofFn (fun i : Fin q.1 ↦ q.2 i.1)
  have hrc_meas : Measurable rootCombine := by
    intro s hs
    have hpre : rootCombine ⁻¹' s =
        ⋃ d : ℕ, Prod.fst ⁻¹' {d} ∩
          (fun q : ℕ × (ℕ → GWTree m) ↦
            List.ofFn (fun i : Fin d ↦ q.2 i.1)) ⁻¹' s := by
      ext ⟨d, τ⟩
      simp only [rootCombine, mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
      exact ⟨fun h ↦ ⟨d, rfl, h⟩, by rintro ⟨d', rfl, h⟩; exact h⟩
    rw [hpre]
    refine MeasurableSet.iUnion fun d ↦ (measurable_fst (measurableSet_singleton d)).inter ?_
    have hproj : Measurable (fun q : ℕ × (ℕ → GWTree m) ↦ fun i : Fin d ↦ q.2 i.1) :=
      measurable_pi_iff.2 fun i ↦ (measurable_pi_apply i.1).comp measurable_snd
    let ofFnTree : (Fin d → GWTree m) → GWTree (m + 1) := List.ofFn
    exact ((measurable_of_countable ofFnTree).comp hproj) hs
  have hind_τ : iIndepFun (fun (r : ℕ) (τ : ℕ → GWTree m) ↦ τ r) μT :=
    iIndepFun_infinitePi (P := fun _ : ℕ ↦ νm) (X := fun _ t ↦ t) (fun _ ↦ measurable_id)
  have hmap_rc : μ_root.map rootCombine = P.map (gwTreeOfArray ξ' (m + 1)) := by
    refine map_eq_of_measureReal_eq hrc_meas.aemeasurable hTm1_meas.aemeasurable fun ts ↦ ?_
    let d := ts.length
    have hset : {q : ℕ × (ℕ → GWTree m) | rootCombine q = ts} =
        ({d} : Set ℕ) ×ˢ
          {τ : ℕ → GWTree m | (fun i : Fin d ↦ τ i.1) = (fun i : Fin d ↦ ts.get i)} := by
      ext ⟨d', τ⟩
      simp only [rootCombine, mem_ofPred_eq, mem_prod, mem_singleton_iff]
      constructor
      · intro h
        have hd : d' = d := by
          have hlen := congrArg List.length h
          simpa using hlen
        subst hd
        refine ⟨rfl, List.ofFn_injective (h.trans (List.ofFn_get ts).symm)⟩
      · rintro ⟨rfl, hτ⟩
        have hcongr : (fun i : Fin ts.length ↦ τ i.1) = (fun i : Fin ts.length ↦ ts.get i) := hτ
        rw [hcongr]
        exact List.ofFn_get ts
    rw [hset, Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
    change μ₁.real {d} *
        μT.real {τ : ℕ → GWTree m | (fun i : Fin d ↦ τ i.1) = (fun i : Fin d ↦ ts.get i)} =
      P.real {ω | gwTreeOfArray ξ' (m + 1) ω = ts}
    have hμ₁_d : μ₁.real {d} = p d :=
      map_measureReal_apply_of_aemeasurable (hGW.aemeasurable_Z 1) (measurableSet_singleton d)
    rw [hμ₁_d, measureReal_pi_eq_prod_of_iIndepFun μT hind_τ Fin.val_injective]
    have hfactor : ∀ i : Fin d,
        μT.real {τ : ℕ → GWTree m | τ i.1 = ts.get i} = gwProb p (ts.get i) := by
      intro i
      have heval : μT.map (fun τ : ℕ → GWTree m ↦ τ i.1) = νm :=
        Measure.infinitePi_map_eval (fun _ : ℕ ↦ νm) i.1
      have h1 := map_measureReal_apply (measurable_pi_apply i.1)
        (measurableSet_singleton (ts.get i)) (μ := μT)
      rw [heval, map_measureReal_apply hTm_meas (measurableSet_singleton (ts.get i))] at h1
      exact h1.symm.trans
        (measureReal_gwTreeOfArray_eq_gwProb P Z hξ'_meas hξ'_indep hξ'_ident m (ts.get i))
    simp_rw [hfactor]
    rw [prod_fin_get_eq_map_prod (gwProb p) ts,
      measureReal_gwTreeOfArray_eq_gwProb P Z hξ'_meas hξ'_indep hξ'_ident (m + 1) ts]
    rfl
  have htotal : μ_root.real {q | gwTreeGenSize (rootCombine q) = k} =
      P.real {ω | Z (m + 1) ω = k} := by
    have h1 := map_measureReal_apply hrc_meas
      ((measurable_of_countable gwTreeGenSize) (measurableSet_singleton k)) (μ := μ_root)
    rw [hmap_rc, map_measureReal_apply hTm1_meas
      ((measurable_of_countable gwTreeGenSize) (measurableSet_singleton k))] at h1
    refine h1.symm.trans ?_
    change P.real {ω | gwTreeGenSize (gwTreeOfArray ξ' (m + 1) ω) = k} =
      P.real {ω | Z (m + 1) ω = k}
    simp_rw [gwTreeGenSize_gwTreeOfArray]
    refine measureReal_congr ?_
    filter_upwards [hZ_ae (m + 1)] with ω hω
    simp [hω]
  obtain ⟨htsum, hsum⟩ := measureReal_inter_fiber_tsum μ_root
    (E := {q | gwTreeGenSize (rootCombine q) = k})
    (hrc_meas ((measurable_of_countable gwTreeGenSize) (measurableSet_singleton k)))
    measurable_fst (fun _ : ℕ ↦ True)
  have huniv_inter : {q : ℕ × (ℕ → GWTree m) | gwTreeGenSize (rootCombine q) = k} ∩
      {q | True} = {q | gwTreeGenSize (rootCombine q) = k} := inter_univ _
  rw [huniv_inter, htotal] at htsum
  let e := Equiv.subtypeUnivEquiv (α := ℕ) (p := fun _ ↦ True) (fun _ ↦ trivial)
  have hterm : ∀ d : ℕ,
      μ_root.real ({q : ℕ × (ℕ → GWTree m) | gwTreeGenSize (rootCombine q) = k} ∩
        {q | q.1 = d}) =
        P.real {ω | Z 1 ω = d} * P'.real {ω' | (∑ r ∈ Finset.range d, ξj r ω') = k} := by
    intro d
    have hset_d : {q : ℕ × (ℕ → GWTree m) | gwTreeGenSize (rootCombine q) = k} ∩
        {q | q.1 = d} =
        ({d} : Set ℕ) ×ˢ
          {τ : ℕ → GWTree m | (∑ r ∈ Finset.range d, gwTreeGenSize (τ r)) = k} := by
      ext ⟨d', τ⟩
      simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_singleton_iff]
      constructor
      · rintro ⟨h1, rfl⟩
        refine ⟨rfl, ?_⟩
        change ((List.ofFn (fun i : Fin d' ↦ τ i.1)).map gwTreeGenSize).sum = k at h1
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
          Fin.sum_univ_eq_sum_range (fun r ↦ gwTreeGenSize (τ r)) d'] at h1
        exact h1
      · rintro ⟨rfl, h2⟩
        refine ⟨?_, rfl⟩
        change ((List.ofFn (fun i : Fin d' ↦ τ i.1)).map gwTreeGenSize).sum = k
        simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
          Fin.sum_univ_eq_sum_range (fun r ↦ gwTreeGenSize (τ r)) d']
        exact h2
    rw [hset_d, Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
    change μ₁.real {d} *
        μT.real {τ : ℕ → GWTree m | (∑ r ∈ Finset.range d, gwTreeGenSize (τ r)) = k} = _
    have hμ₁_d : μ₁.real {d} = P.real {ω | Z 1 ω = d} :=
      map_measureReal_apply_of_aemeasurable (hGW.aemeasurable_Z 1) (measurableSet_singleton d)
    rw [hμ₁_d]
    congr 1
    let η : ℕ → (ℕ → GWTree m) → ℕ := fun r τ ↦ gwTreeGenSize (τ r)
    have hη_meas : ∀ r, Measurable (η r) :=
      fun r ↦ (measurable_of_countable gwTreeGenSize).comp (measurable_pi_apply r)
    have hη_indep : iIndepFun η μT :=
      hind_τ.comp (fun _ ↦ gwTreeGenSize) (fun _ ↦ measurable_of_countable gwTreeGenSize)
    have hη_law : ∀ r : ℕ, μT.map (η r) = P'.map (ξj r) := by
      intro r
      rw [hξ_law r]
      have hproj_r : Measurable (fun τ : ℕ → GWTree m ↦ τ r) := measurable_pi_apply r
      change μT.map (gwTreeGenSize ∘ fun τ : ℕ → GWTree m ↦ τ r) = P.map (Z m)
      rw [← Measure.map_map (measurable_of_countable gwTreeGenSize) hproj_r,
        Measure.infinitePi_map_eval,
        Measure.map_map (measurable_of_countable gwTreeGenSize) hTm_meas]
      have hcongr_m : gwTreeGenSize ∘ gwTreeOfArray ξ' m =ᵐ[P] Z m := by
        filter_upwards [hZ_ae m] with ω hω
        change gwTreeGenSize (gwTreeOfArray ξ' m ω) = Z m ω
        rw [gwTreeGenSize_gwTreeOfArray, hω]
      exact Measure.map_congr hcongr_m
    have hpi_map := map_pi_eq_of_iIndepFun μT P' hη_meas hξ_meas hη_indep hξ_indep
      (d := d) Fin.val_injective Fin.val_injective (fun i ↦ hη_law i.1)
    let S_sum : Set (Fin d → ℕ) := {c | (∑ i : Fin d, c i) = k}
    have hpre_η : (fun (τ : ℕ → GWTree m) (i : Fin d) ↦ η i.1 τ) ⁻¹' S_sum =
        {τ : ℕ → GWTree m | (∑ r ∈ Finset.range d, gwTreeGenSize (τ r)) = k} := by
      ext τ
      simp only [S_sum, η, mem_preimage, mem_ofPred_eq,
        Fin.sum_univ_eq_sum_range (fun r ↦ gwTreeGenSize (τ r)) d]
    have hpre_ξ : (fun (ω' : Ω') (i : Fin d) ↦ ξj i.1 ω') ⁻¹' S_sum =
        {ω' : Ω' | (∑ r ∈ Finset.range d, ξj r ω') = k} := by
      ext ω'
      simp only [S_sum, mem_preimage, mem_ofPred_eq,
        Fin.sum_univ_eq_sum_range (fun r ↦ ξj r ω') d]
    have hΦη : Measurable (fun (τ : ℕ → GWTree m) (i : Fin d) ↦ η i.1 τ) :=
      measurable_pi_iff.2 fun i ↦ hη_meas i.1
    have hΦξ : Measurable (fun (ω' : Ω') (i : Fin d) ↦ ξj i.1 ω') :=
      measurable_pi_iff.2 fun i ↦ hξ_meas i.1
    rw [← hpre_η, ← hpre_ξ,
      ← map_measureReal_apply hΦη (MeasurableSet.of_discrete),
      ← map_measureReal_apply hΦξ (MeasurableSet.of_discrete),
      hpi_map]
  have hsum' : Summable (fun d : ℕ ↦ μ_root.real
      ({q : ℕ × (ℕ → GWTree m) | gwTreeGenSize (rootCombine q) = k} ∩ {q | q.1 = d})) :=
    (e.summable_iff (f := fun d : ℕ ↦ μ_root.real
      ({q : ℕ × (ℕ → GWTree m) | gwTreeGenSize (rootCombine q) = k} ∩ {q | q.1 = d}))).mp hsum
  have htsum' : (∑' d : ℕ, μ_root.real
      ({q : ℕ × (ℕ → GWTree m) | gwTreeGenSize (rootCombine q) = k} ∩ {q | q.1 = d})) =
      P.real {ω | Z (m + 1) ω = k} := by
    rw [← htsum]
    exact (e.tsum_eq (fun d : ℕ ↦ μ_root.real
      ({q : ℕ × (ℕ → GWTree m) | gwTreeGenSize (rootCombine q) = k} ∩ {q | q.1 = d}))).symm
  simp_rw [hterm] at hsum' htsum'
  exact ⟨hsum', htsum'⟩

theorem measureReal_biUnion_fintype {Ω' ι : Type*} [MeasurableSpace Ω'] [Fintype ι]
    (P' : Measure Ω') [IsFiniteMeasure P'] {A : ι → Set Ω'}
    (hdisj : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hmeas : ∀ i, MeasurableSet (A i)) :
    P'.real (⋃ i : ι, A i) = ∑ i : ι, P'.real (A i) := by
  have h1 : (⋃ i : ι, A i) = ⋃ i ∈ (Finset.univ : Finset ι), A i := by simp
  rw [h1, Measure.real, measure_biUnion_finset (fun i _ j _ hij ↦ hdisj hij)
    (fun i _ ↦ hmeas i), ENNReal.toReal_sum (fun i _ ↦ measure_ne_top P' (A i))]
  rfl

theorem spine_level_step
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) {m : ℕ}
    {S₀ L₀ Xj Aj : Ω' → ℕ} {ξj : ℕ → Ω' → ℕ}
    (hS₀_meas : Measurable S₀) (hL₀_meas : Measurable L₀)
    (hXj_meas : Measurable Xj) (hAj_meas : Measurable Aj)
    (hξj_meas : ∀ r, Measurable (ξj r))
    (hAX_le : ∀ ω', Aj ω' ≤ Xj ω')
    (hXA_pmf : ∀ d a : ℕ, P'.real {ω' | Xj ω' = d ∧ Aj ω' = a} =
      if a ≤ d then P.real {ω | Z 1 ω = d + 1} else 0)
    (hξ_indep : iIndepFun ξj P')
    (hξ_law : ∀ r : ℕ, P'.map (ξj r) = P.map (Z m))
    (hind_XA_xi : IndepFun (fun ω' ↦ (Xj ω', Aj ω')) (fun ω' r ↦ ξj r ω') P')
    (hind_prev : IndepFun (fun ω' ↦ (Xj ω', Aj ω', fun r ↦ ξj r ω'))
      (fun ω' ↦ (S₀ ω', L₀ ω')) P')
    (hSL₀ : ∀ k u : ℕ, P'.real {ω' | S₀ ω' = k ∧ L₀ ω' = u} =
      if u < k then P.real {ω | Z m ω = k} else 0)
    (k u : ℕ) :
    let S₁ : Ω' → ℕ := fun ω' ↦ (∑ r ∈ Finset.range (Xj ω'), ξj r ω') + S₀ ω'
    let L₁ : Ω' → ℕ := fun ω' ↦ (∑ r ∈ Finset.range (Aj ω'), ξj r ω') + L₀ ω'
    P'.real {ω' | S₁ ω' = k ∧ L₁ ω' = u} =
      if u < k then P.real {ω | Z (m + 1) ω = k} else 0 := by
  intro S₁ L₁
  let U : ℕ → Ω' → ℕ := fun d ω' ↦ ∑ r ∈ Finset.range d, ξj r ω'
  have hU_meas : ∀ d : ℕ, Measurable (U d) :=
    fun d ↦ Finset.measurable_sum (Finset.range d) fun r _ ↦ hξj_meas r
  have hS₁_meas : Measurable S₁ := (measurable_sum_range hXj_meas hξj_meas).add hS₀_meas
  have hL₁_meas : Measurable L₁ := (measurable_sum_range hAj_meas hξj_meas).add hL₀_meas
  have hSL₁_set_meas : MeasurableSet {ω' | S₁ ω' = k ∧ L₁ ω' = u} :=
    (hS₁_meas (measurableSet_singleton k)).inter (hL₁_meas (measurableSet_singleton u))
  have hfiber_da : ∀ (d : ℕ) (a : Fin (d + 1)),
      P'.real ({ω' | S₁ ω' = k ∧ L₁ ω' = u} ∩ {ω' | Xj ω' = d ∧ Aj ω' = a.1}) =
        P.real {ω | Z 1 ω = d + 1} *
          P'.real {ω' | U (d + 1) ω' = k ∧ U a.1 ω' ≤ u ∧ u < U (a.1 + 1) ω'} := by
    intro d a
    let E₁ : Set Ω' := {ω' | S₁ ω' = k ∧ L₁ ω' = u} ∩ {ω' | Xj ω' = d ∧ Aj ω' = a.1}
    let E₂ : Set Ω' := {ω' | U d ω' + ξj d ω' = k ∧ U a.1 ω' ≤ u ∧ u < U a.1 ω' + ξj d ω'}
    have hE₁_meas : MeasurableSet E₁ :=
      hSL₁_set_meas.inter
        ((hXj_meas (measurableSet_singleton d)).inter (hAj_meas (measurableSet_singleton a.1)))
    have hE₂_meas : MeasurableSet E₂ :=
      (((hU_meas d).add (hξj_meas d)) (measurableSet_singleton k)).inter
        ((measurableSet_le (hU_meas a.1) measurable_const).inter
          (measurableSet_lt measurable_const ((hU_meas a.1).add (hξj_meas d))))
    have hswap : P'.real E₂ =
        P'.real {ω' | U (d + 1) ω' = k ∧ U a.1 ω' ≤ u ∧ u < U (a.1 + 1) ω'} := by
      have hE₂_eq : E₂ = {ω' | (∑ r ∈ Finset.range (d + 1), ξj r ω') = k ∧
          (∑ r ∈ Finset.range a.1, ξj r ω') ≤ u ∧
          u < (∑ r ∈ Finset.range a.1, ξj r ω') + ξj d ω'} := by
        ext ω'
        simp only [E₂, U, mem_ofPred_eq, Finset.sum_range_succ _ d]
      rw [hE₂_eq]
      exact measureReal_sum_swap_last P P' hξj_meas hξ_indep hξ_law d k u a
    rw [← hswap]
    let g : Ω' → ℕ × ℕ := fun ω' ↦ (U d ω', U a.1 ω')
    have hg_meas : Measurable g := (hU_meas d).prodMk (hU_meas a.1)
    obtain ⟨htsum₁, _⟩ := measureReal_inter_fiber_tsum P' (E := E₁) hE₁_meas hg_meas
      (fun _ : ℕ × ℕ ↦ True)
    obtain ⟨htsum₂, _⟩ := measureReal_inter_fiber_tsum P' (E := E₂) hE₂_meas hg_meas
      (fun _ : ℕ × ℕ ↦ True)
    simp only [Set.ofPred_true, inter_univ] at htsum₁ htsum₂
    rw [← htsum₁, ← htsum₂, ← tsum_mul_left]
    refine tsum_congr fun ⟨⟨x, y⟩, _⟩ ↦ ?_
    have hE₁_xy : E₁ ∩ {ω' | g ω' = (x, y)} =
        (fun ω' ↦ (Xj ω', Aj ω', fun r ↦ ξj r ω')) ⁻¹'
          {q : ℕ × ℕ × (ℕ → ℕ) | (q.1 = d ∧ q.2.1 = a.1) ∧
            ((∑ r ∈ Finset.range d, q.2.2 r) = x ∧ (∑ r ∈ Finset.range a.1, q.2.2 r) = y)} ∩
        (fun ω' ↦ (S₀ ω', L₀ ω')) ⁻¹' {p : ℕ × ℕ | x + p.1 = k ∧ y + p.2 = u} := by
      ext ω'
      simp only [E₁, S₁, L₁, U, g, mem_inter_iff, mem_ofPred_eq, mem_preimage, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨hk_eq, hu_eq⟩, hd_eq, hA_eq⟩, hx_eq, hy_eq⟩
        rw [hd_eq, hx_eq] at hk_eq
        rw [hA_eq, hy_eq] at hu_eq
        exact ⟨⟨⟨hd_eq, hA_eq⟩, hx_eq, hy_eq⟩, hk_eq, hu_eq⟩
      · rintro ⟨⟨⟨hd_eq, hA_eq⟩, hx_eq, hy_eq⟩, hk_eq, hu_eq⟩
        rw [← hx_eq, ← hd_eq] at hk_eq
        rw [← hy_eq, ← hA_eq] at hu_eq
        exact ⟨⟨⟨hk_eq, hu_eq⟩, hd_eq, hA_eq⟩, hx_eq, hy_eq⟩
    have hmeas_q : MeasurableSet
        {q : ℕ × ℕ × (ℕ → ℕ) | (q.1 = d ∧ q.2.1 = a.1) ∧
          ((∑ r ∈ Finset.range d, q.2.2 r) = x ∧ (∑ r ∈ Finset.range a.1, q.2.2 r) = y)} := by
      refine ((measurable_fst (measurableSet_singleton d)).inter
        ((measurable_fst.comp measurable_snd) (measurableSet_singleton a.1))).inter ?_
      refine ((Finset.measurable_sum (Finset.range d) fun r _ ↦
        (measurable_pi_apply r).comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton x)).inter ?_
      exact (Finset.measurable_sum (Finset.range a.1) fun r _ ↦
        (measurable_pi_apply r).comp (measurable_snd.comp measurable_snd))
          (measurableSet_singleton y)
    have hE₁_prod1 : P'.real (E₁ ∩ {ω' | g ω' = (x, y)}) =
        P'.real ({ω' | Xj ω' = d ∧ Aj ω' = a.1} ∩ {ω' | g ω' = (x, y)}) *
          P'.real {ω' | x + S₀ ω' = k ∧ y + L₀ ω' = u} := by
      rw [hE₁_xy, Measure.real,
        hind_prev.measure_inter_preimage_eq_mul _ _ hmeas_q (MeasurableSet.of_discrete),
        ENNReal.toReal_mul]
      congr 1
      rw [Measure.real]; congr 2; ext ω'; simp [g, U]
    have hXAg_eq : {ω' | Xj ω' = d ∧ Aj ω' = a.1} ∩ {ω' | g ω' = (x, y)} =
        (fun ω' ↦ (Xj ω', Aj ω')) ⁻¹' {(d, a.1)} ∩
          (fun ω' r ↦ ξj r ω') ⁻¹'
            {η : ℕ → ℕ | (∑ r ∈ Finset.range d, η r) = x ∧
              (∑ r ∈ Finset.range a.1, η r) = y} := by
      ext ω'
      simp [g, U, Prod.mk.injEq]
    have hmeas_η : MeasurableSet
        {η : ℕ → ℕ | (∑ r ∈ Finset.range d, η r) = x ∧
          (∑ r ∈ Finset.range a.1, η r) = y} :=
      ((Finset.measurable_sum (Finset.range d) fun r _ ↦ measurable_pi_apply r)
        (measurableSet_singleton x)).inter
        ((Finset.measurable_sum (Finset.range a.1) fun r _ ↦ measurable_pi_apply r)
          (measurableSet_singleton y))
    have hXAg_prod : P'.real ({ω' | Xj ω' = d ∧ Aj ω' = a.1} ∩ {ω' | g ω' = (x, y)}) =
        P.real {ω | Z 1 ω = d + 1} * P'.real {ω' | g ω' = (x, y)} := by
      have h1 : P'.real ({ω' | Xj ω' = d ∧ Aj ω' = a.1} ∩ {ω' | g ω' = (x, y)}) =
          P'.real {ω' | Xj ω' = d ∧ Aj ω' = a.1} * P'.real {ω' | g ω' = (x, y)} := by
        rw [hXAg_eq, Measure.real,
          hind_XA_xi.measure_inter_preimage_eq_mul _ _
            (MeasurableSet.of_discrete) hmeas_η,
          ENNReal.toReal_mul]
        congr 1 <;> (rw [Measure.real]; congr 2; ext ω'; simp [g, U])
      rw [h1, hXA_pmf d a.1, ite_eq_left_iff.2 fun h ↦ False.elim (h (Nat.le_of_lt_succ a.2))]
    have hind_g_ξd : IndepFun g (ξj d) P' := by
      have hdisj : Disjoint (Finset.range d) ({d} : Finset ℕ) := by simp
      have hind := hξ_indep.indepFun_finset₀ (Finset.range d) {d} hdisj
        (fun r ↦ (hξj_meas r).aemeasurable)
      let φg : (Finset.range d → ℕ) → ℕ × ℕ :=
        fun c ↦ (∑ r : Finset.range d, c r,
          ∑ r : Finset.range d, if r.1 < a.1 then c r else 0)
      have hφg_meas : Measurable φg :=
        (Finset.measurable_sum Finset.univ fun r _ ↦ measurable_pi_apply r).prodMk
          (Finset.measurable_sum Finset.univ fun r _ ↦ by
            by_cases h : r.1 < a.1 <;> simp [h, measurable_pi_apply r, measurable_const])
      have hcomp := hind.comp hφg_meas
        (measurable_pi_apply (⟨d, Finset.mem_singleton_self d⟩ : ({d} : Finset ℕ)))
      have hg_comp : (φg ∘ fun ω' (i : Finset.range d) ↦ ξj i.1 ω') = g := by
        funext ω'
        dsimp only [g, U, φg, Function.comp_apply]
        refine Prod.ext ?_ ?_
        · exact Finset.sum_attach (Finset.range d) (fun r ↦ ξj r ω')
        · refine (Finset.sum_attach (Finset.range d)
            (fun r ↦ if r < a.1 then ξj r ω' else 0)).trans ?_
          rw [← Finset.sum_filter]
          have hfilt : (Finset.range d).filter (· < a.1) = Finset.range a.1 := by
            ext r
            simp only [Finset.mem_filter, Finset.mem_range]
            have ha := a.2
            omega
          rw [hfilt]
      have hξd_comp :
          ((fun f : ({d} : Finset ℕ) → ℕ ↦ f ⟨d, Finset.mem_singleton_self d⟩) ∘
            fun ω' (i : ({d} : Finset ℕ)) ↦ ξj i.1 ω') = ξj d := rfl
      rwa [hg_comp, hξd_comp] at hcomp
    have hE₂_xy : E₂ ∩ {ω' | g ω' = (x, y)} =
        g ⁻¹' {(x, y)} ∩
          ξj d ⁻¹' {s : ℕ | x + s = k ∧ y ≤ u ∧ u < y + s} := by
      ext ω'
      simp only [E₂, g, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hk_eq, hy_le, hu_lt⟩, rfl, rfl⟩
        exact ⟨⟨rfl, rfl⟩, hk_eq, hy_le, hu_lt⟩
      · rintro ⟨⟨rfl, rfl⟩, hk_eq, hy_le, hu_lt⟩
        exact ⟨⟨hk_eq, hy_le, hu_lt⟩, rfl, rfl⟩
    have hE₂_prod : P'.real (E₂ ∩ {ω' | g ω' = (x, y)}) =
        P'.real {ω' | g ω' = (x, y)} *
          P'.real {ω' | x + ξj d ω' = k ∧ y ≤ u ∧ u < y + ξj d ω'} := by
      rw [hE₂_xy, Measure.real,
        hind_g_ξd.measure_inter_preimage_eq_mul _ _
          (MeasurableSet.of_discrete) (MeasurableSet.of_discrete),
        ENNReal.toReal_mul]
      rfl
    have htail_eq : P'.real {ω' | x + S₀ ω' = k ∧ y + L₀ ω' = u} =
        P'.real {ω' | x + ξj d ω' = k ∧ y ≤ u ∧ u < y + ξj d ω'} := by
      by_cases hxy : x ≤ k ∧ y ≤ u ∧ u - y < k - x
      · rcases hxy with ⟨hxk, hyu, hlt⟩
        have hset1 : {ω' : Ω' | x + S₀ ω' = k ∧ y + L₀ ω' = u} =
            {ω' | S₀ ω' = k - x ∧ L₀ ω' = u - y} := by
          ext ω'; simp only [mem_ofPred_eq]; omega
        have hset2 : {ω' : Ω' | x + ξj d ω' = k ∧ y ≤ u ∧ u < y + ξj d ω'} =
            {ω' | ξj d ω' = k - x} := by
          ext ω'; simp only [mem_ofPred_eq]; omega
        rw [hset1, hset2, hSL₀ (k - x) (u - y),
          ite_eq_left_iff.2 fun h ↦ False.elim (h hlt)]
        have hlaw_d := map_measureReal_apply (hξj_meas d)
          (measurableSet_singleton (k - x)) (μ := P')
        rw [hξ_law d, map_measureReal_apply_of_aemeasurable
          (hGW.aemeasurable_Z m) (measurableSet_singleton (k - x))] at hlaw_d
        exact hlaw_d
      · by_cases hle : x ≤ k ∧ y ≤ u
        · rcases hle with ⟨hxk, hyu⟩
          have hnot_lt : ¬ (u - y < k - x) := fun h ↦ hxy ⟨hxk, hyu, h⟩
          have hset1 : {ω' : Ω' | x + S₀ ω' = k ∧ y + L₀ ω' = u} =
              {ω' | S₀ ω' = k - x ∧ L₀ ω' = u - y} := by
            ext ω'; simp only [mem_ofPred_eq]; omega
          have hset2 : {ω' : Ω' | x + ξj d ω' = k ∧ y ≤ u ∧ u < y + ξj d ω'} = ∅ := by
            ext ω'; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]; omega
          rw [hset1, hset2, hSL₀ (k - x) (u - y),
            ite_eq_right_iff.2 fun h ↦ False.elim (hnot_lt h), measureReal_empty]
        · have hset1 : {ω' : Ω' | x + S₀ ω' = k ∧ y + L₀ ω' = u} = ∅ := by
            ext ω'; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]; omega
          have hset2 : {ω' : Ω' | x + ξj d ω' = k ∧ y ≤ u ∧ u < y + ξj d ω'} = ∅ := by
            ext ω'; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]; omega
          rw [hset1, hset2]
    rw [hE₁_prod1, hXAg_prod, hE₂_prod, htail_eq, mul_assoc]
  have hfiber_d : ∀ d : ℕ,
      P'.real ({ω' | S₁ ω' = k ∧ L₁ ω' = u} ∩ {ω' | Xj ω' = d}) =
        if u < k then
          P.real {ω | Z 1 ω = d + 1} * P'.real {ω' | U (d + 1) ω' = k}
        else 0 := by
    intro d
    let A₁ : Fin (d + 1) → Set Ω' :=
      fun a ↦ {ω' | S₁ ω' = k ∧ L₁ ω' = u} ∩ {ω' | Xj ω' = d ∧ Aj ω' = a.1}
    have hA₁_disj : Pairwise (fun a₁ a₂ ↦ Disjoint (A₁ a₁) (A₁ a₂)) := by
      intro a₁ a₂ ha
      refine Set.disjoint_left.2 fun ω' h1 h2 ↦ ha (Fin.ext ?_)
      exact h1.2.2.symm.trans h2.2.2
    have hA₁_meas : ∀ a, MeasurableSet (A₁ a) := fun a ↦
      hSL₁_set_meas.inter
        ((hXj_meas (measurableSet_singleton d)).inter (hAj_meas (measurableSet_singleton a.1)))
    have hA₁_union : (⋃ a : Fin (d + 1), A₁ a) =
        {ω' | S₁ ω' = k ∧ L₁ ω' = u} ∩ {ω' | Xj ω' = d} := by
      ext ω'
      simp only [A₁, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨a, hSL, hX, _⟩
        exact ⟨hSL, hX⟩
      · rintro ⟨hSL, rfl⟩
        exact ⟨⟨Aj ω', Nat.lt_succ_of_le (hAX_le ω')⟩, hSL, rfl, rfl⟩
    rw [← hA₁_union, measureReal_biUnion_fintype P' hA₁_disj hA₁_meas]
    simp only [A₁, hfiber_da d, ← Finset.mul_sum]
    let A₂ : Fin (d + 1) → Set Ω' :=
      fun a ↦ {ω' | U (d + 1) ω' = k ∧ U a.1 ω' ≤ u ∧ u < U (a.1 + 1) ω'}
    have hA₂_disj : Pairwise (fun a₁ a₂ ↦ Disjoint (A₂ a₁) (A₂ a₂)) := by
      intro a₁ a₂ ha
      refine Set.disjoint_left.2 fun ω' h1 h2 ↦ ?_
      have hne : a₁.1 ≠ a₂.1 := fun h ↦ ha (Fin.ext h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : U (a₁.1 + 1) ω' ≤ U a₂.1 ω' :=
          Finset.sum_le_sum_of_subset (Finset.range_mono hlt)
        have h1' := h1.2.2
        have h2' := h2.2.1
        omega
      · have hle : U (a₂.1 + 1) ω' ≤ U a₁.1 ω' :=
          Finset.sum_le_sum_of_subset (Finset.range_mono hgt)
        have h1' := h1.2.1
        have h2' := h2.2.2
        omega
    have hA₂_meas : ∀ a, MeasurableSet (A₂ a) := fun a ↦
      ((hU_meas (d + 1)) (measurableSet_singleton k)).inter
        ((measurableSet_le (hU_meas a.1) measurable_const).inter
          (measurableSet_lt measurable_const (hU_meas (a.1 + 1))))
    have hsum_A₂ := (measureReal_biUnion_fintype P' hA₂_disj hA₂_meas).symm
    change P.real {ω | Z 1 ω = d + 1} * (∑ a : Fin (d + 1), P'.real (A₂ a)) = _
    rw [hsum_A₂]
    by_cases huk : u < k
    · have hunion_eq : (⋃ a : Fin (d + 1), A₂ a) = {ω' | U (d + 1) ω' = k} := by
        ext ω'
        simp only [A₂, mem_iUnion, mem_ofPred_eq]
        constructor
        · rintro ⟨_, hk_eq, _, _⟩; exact hk_eq
        · intro hk_eq
          have hpart := sum_fin_range_interval_partition (fun r ↦ ξj r ω') (d + 1) u
          change (∑ a : Fin (d + 1),
              if U a.1 ω' ≤ u ∧ u < U (a.1 + 1) ω' then (1 : ℝ) else 0) =
            if u < U (d + 1) ω' then 1 else 0 at hpart
          rw [hk_eq, ite_eq_left_iff.2 fun h ↦ False.elim (h huk)] at hpart
          have hne0 : (∑ a : Fin (d + 1),
              if U a.1 ω' ≤ u ∧ u < U (a.1 + 1) ω' then (1 : ℝ) else 0) ≠ 0 := by
            rw [hpart]; exact one_ne_zero
          obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
          refine ⟨a, hk_eq, ?_⟩
          by_contra hcontra
          exact ha (ite_eq_right_iff.2 fun h ↦ False.elim (hcontra h))
      rw [hunion_eq, ite_eq_left_iff.2 fun h ↦ False.elim (h huk)]
    · have hunion_empty : (⋃ a : Fin (d + 1), A₂ a) = ∅ := by
        ext ω'
        simp only [A₂, mem_iUnion, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
        rintro a ⟨hk_eq, _, hu_lt⟩
        have hle : U (a.1 + 1) ω' ≤ U (d + 1) ω' :=
          Finset.sum_le_sum_of_subset (Finset.range_mono a.2)
        omega
      rw [hunion_empty, measureReal_empty, mul_zero,
        ite_eq_right_iff.2 fun h ↦ False.elim (huk h)]
  obtain ⟨htsum_X, _⟩ := measureReal_inter_fiber_tsum P'
    (E := {ω' | S₁ ω' = k ∧ L₁ ω' = u}) hSL₁_set_meas hXj_meas (fun _ : ℕ ↦ True)
  simp only [Set.ofPred_true, inter_univ] at htsum_X
  let e := Equiv.subtypeUnivEquiv (α := ℕ) (p := fun _ ↦ True) (fun _ ↦ trivial)
  have htsum_X' : P'.real {ω' | S₁ ω' = k ∧ L₁ ω' = u} =
      ∑' d : ℕ, P'.real ({ω' | S₁ ω' = k ∧ L₁ ω' = u} ∩ {ω' | Xj ω' = d}) := by
    rw [← htsum_X]
    exact e.tsum_eq (fun d : ℕ ↦
      P'.real ({ω' | S₁ ω' = k ∧ L₁ ω' = u} ∩ {ω' | Xj ω' = d}))
  rw [htsum_X']
  simp_rw [hfiber_d]
  by_cases huk : u < k
  · simp only [ite_true, huk]
    obtain ⟨hsum_iid, htsum_iid⟩ :=
      hGW.measureReal_Z_succ_eq_tsum_iid hξj_meas hξ_indep hξ_law k
    change (∑' d : ℕ, P.real {ω | Z 1 ω = d + 1} * P'.real {ω' | U (d + 1) ω' = k}) =
      P.real {ω | Z (m + 1) ω = k}
    rw [← htsum_iid, hsum_iid.tsum_eq_zero_add]
    have h0 : P'.real {ω' | (∑ r ∈ Finset.range 0, ξj r ω') = k} = 0 := by
      have hempty : {ω' : Ω' | (∑ r ∈ Finset.range 0, ξj r ω') = k} = ∅ := by
        ext ω'
        simp only [Finset.range_zero, Finset.sum_empty, mem_ofPred_eq, mem_empty_iff_false,
          iff_false]
        omega
      rw [hempty, measureReal_empty]
    rw [h0, mul_zero, zero_add]
  · simp [huk]

theorem IsSizeBiasSpine.exists_measurable_modification
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hSp : IsSizeBiasSpine P Z P' n X L R) :
    ∃ (X' A' L' R' : ℕ → Ω' → ℕ) (ξ' : ℕ → ℕ → Ω' → ℕ),
      (∀ j, Measurable (X' j)) ∧
      (∀ j, Measurable (A' j)) ∧
      (∀ j, Measurable (L' j)) ∧
      (∀ j, Measurable (R' j)) ∧
      (∀ j r, Measurable (ξ' j r)) ∧
      (∀ j ω', A' j ω' ≤ X' j ω') ∧
      (∀ j ω', L' j ω' = ∑ r ∈ Finset.range (A' j ω'), ξ' j r ω') ∧
      (∀ j ω', R' j ω' = ∑ r ∈ Finset.Ico (A' j ω') (X' j ω'), ξ' j r ω') ∧
      (∀ j ω', L' j ω' + R' j ω' = ∑ r ∈ Finset.range (X' j ω'), ξ' j r ω') ∧
      iIndepFun
        (fun j : Finset.Icc 1 n ↦ fun ω' ↦ (X' j.1 ω', A' j.1 ω', fun r : ℕ ↦ ξ' j.1 r ω')) P' ∧
      ∀ j ∈ Finset.Icc 1 n,
        (X' j =ᵐ[P'] X j) ∧
        (L' j =ᵐ[P'] L j) ∧
        (R' j =ᵐ[P'] R j) ∧
        IsSizeBias P (fun ω ↦ (Z 1 ω : ℝ)) P' (fun ω' ↦ (X' j ω' : ℝ) + 1) ∧
        (∀ k m : ℕ, P'.real {ω' | X' j ω' = k ∧ A' j ω' = m} =
          if m ≤ k then P'.real {ω' | X' j ω' = k} / ((k : ℝ) + 1) else 0) ∧
        iIndepFun (ξ' j) P' ∧
        (∀ r : ℕ, P'.map (ξ' j r) = P.map (Z (n - j))) ∧
        IndepFun (fun ω' ↦ (X' j ω', A' j ω')) (fun ω' (r : ℕ) ↦ ξ' j r ω') P' := by
  obtain ⟨A, ξ, hind_lvl, hlvl⟩ := hSp
  let X' : ℕ → Ω' → ℕ :=
    fun j ω' ↦ if hj : j ∈ Finset.Icc 1 n then (hlvl j hj).1.mk (X j) ω' else 0
  let A_raw : ℕ → Ω' → ℕ :=
    fun j ω' ↦ if hj : j ∈ Finset.Icc 1 n then (hlvl j hj).2.1.mk (A j) ω' else 0
  let A' : ℕ → Ω' → ℕ := fun j ω' ↦ min (A_raw j ω') (X' j ω')
  let ξ' : ℕ → ℕ → Ω' → ℕ :=
    fun j r ω' ↦ if hj : j ∈ Finset.Icc 1 n then ((hlvl j hj).2.2.1 r).mk (ξ j r) ω' else 0
  let L' : ℕ → Ω' → ℕ := fun j ω' ↦ ∑ r ∈ Finset.range (A' j ω'), ξ' j r ω'
  let R' : ℕ → Ω' → ℕ := fun j ω' ↦ ∑ r ∈ Finset.Ico (A' j ω') (X' j ω'), ξ' j r ω'
  have hX'_meas : ∀ j, Measurable (X' j) := by
    intro j
    by_cases hj : j ∈ Finset.Icc 1 n
    · change Measurable (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then (hlvl j h).1.mk (X j) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact (hlvl j hj).1.measurable_mk
    · change Measurable (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then (hlvl j h).1.mk (X j) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact measurable_const
  have hAraw_meas : ∀ j, Measurable (A_raw j) := by
    intro j
    by_cases hj : j ∈ Finset.Icc 1 n
    · change Measurable (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then (hlvl j h).2.1.mk (A j) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact (hlvl j hj).2.1.measurable_mk
    · change Measurable (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then (hlvl j h).2.1.mk (A j) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact measurable_const
  have hA'_meas : ∀ j, Measurable (A' j) :=
    fun j ↦ (hAraw_meas j).min (hX'_meas j)
  have hξ'_meas : ∀ j r, Measurable (ξ' j r) := by
    intro j r
    by_cases hj : j ∈ Finset.Icc 1 n
    · change Measurable
        (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then ((hlvl j h).2.2.1 r).mk (ξ j r) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact ((hlvl j hj).2.2.1 r).measurable_mk
    · change Measurable
        (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then ((hlvl j h).2.2.1 r).mk (ξ j r) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact measurable_const
  have hAX'_le : ∀ j ω', A' j ω' ≤ X' j ω' := fun j ω' ↦ min_le_right _ _
  have hLR'_sum : ∀ j ω', L' j ω' + R' j ω' = ∑ r ∈ Finset.range (X' j ω'), ξ' j r ω' :=
    fun j ω' ↦ Finset.sum_range_add_sum_Ico _ (hAX'_le j ω')
  have hL'_meas : ∀ j, Measurable (L' j) :=
    fun j ↦ measurable_sum_range (hA'_meas j) (fun r ↦ hξ'_meas j r)
  have hR'_meas : ∀ j, Measurable (R' j) := by
    intro j
    have heq : R' j = fun ω' ↦
        (∑ r ∈ Finset.range (X' j ω'), ξ' j r ω') - L' j ω' := by
      ext ω'
      rw [← hLR'_sum j ω', Nat.add_sub_cancel_left]
    rw [heq]
    exact (measurable_sum_range (hX'_meas j) (fun r ↦ hξ'_meas j r)).sub (hL'_meas j)
  have hX'_ae : ∀ j ∈ Finset.Icc 1 n, X' j =ᵐ[P'] X j := by
    intro j hj
    filter_upwards [(hlvl j hj).1.ae_eq_mk] with ω' hω'
    dsimp only [X']
    simp only [hj, ↓reduceDIte, ← hω']
  have hA'_ae : ∀ j ∈ Finset.Icc 1 n, A' j =ᵐ[P'] A j := by
    intro j hj
    filter_upwards [(hlvl j hj).1.ae_eq_mk, (hlvl j hj).2.1.ae_eq_mk] with ω' hXω' hAω'
    dsimp only [A', A_raw, X']
    simp only [hj, ↓reduceDIte, ← hXω', ← hAω']
    exact min_eq_left ((hlvl j hj).2.2.2.2.1 ω')
  have hξ'_ae : ∀ j ∈ Finset.Icc 1 n, ∀ r : ℕ, ξ' j r =ᵐ[P'] ξ j r := by
    intro j hj r
    filter_upwards [((hlvl j hj).2.2.1 r).ae_eq_mk] with ω' hω'
    dsimp only [ξ']
    simp only [hj, ↓reduceDIte, ← hω']
  have hξ'_all_ae : ∀ j ∈ Finset.Icc 1 n, ∀ᵐ ω' ∂P', ∀ r : ℕ, ξ' j r ω' = ξ j r ω' :=
    fun j hj ↦ ae_all_iff.2 (hξ'_ae j hj)
  have hL'_ae : ∀ j ∈ Finset.Icc 1 n, L' j =ᵐ[P'] L j := by
    intro j hj
    filter_upwards [hA'_ae j hj, hξ'_all_ae j hj] with ω' hAω' hξω'
    rw [(hlvl j hj).2.2.2.2.2.2.2.2.2.1 ω']
    dsimp only [L']
    rw [hAω']
    exact Finset.sum_congr rfl fun r _ ↦ hξω' r
  have hR'_ae : ∀ j ∈ Finset.Icc 1 n, R' j =ᵐ[P'] R j := by
    intro j hj
    filter_upwards [hX'_ae j hj, hA'_ae j hj, hξ'_all_ae j hj] with ω' hXω' hAω' hξω'
    rw [(hlvl j hj).2.2.2.2.2.2.2.2.2.2 ω']
    dsimp only [R']
    rw [hAω', hXω']
    exact Finset.sum_congr rfl fun r _ ↦ hξω' r
  refine ⟨X', A', L', R', ξ', hX'_meas, hA'_meas, hL'_meas, hR'_meas, hξ'_meas,
    hAX'_le, fun _ _ ↦ rfl, fun _ _ ↦ rfl, hLR'_sum, ?_, fun j hj ↦ ?_⟩
  · refine hind_lvl.congr fun j ↦ ?_
    filter_upwards [hX'_ae j.1 j.2, hA'_ae j.1 j.2, hξ'_all_ae j.1 j.2] with ω' hXω' hAω' hξω'
    rw [hXω', hAω', funext hξω']
  · refine ⟨hX'_ae j hj, hL'_ae j hj, hR'_ae j hj, ?_, fun k m ↦ ?_, ?_, fun r ↦ ?_, ?_⟩
    · rcases (hlvl j hj).2.2.2.1 with ⟨hZ_nn, hZ_int, _, hSB_eq⟩
      refine ⟨hZ_nn, hZ_int,
        (((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp
          (hX'_meas j)).add measurable_const).aemeasurable, fun f hf hint ↦ ?_⟩
      rw [hSB_eq f hf hint]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hX'_ae j hj] with ω' hω'
      rw [hω']
    · have hXA_congr : P'.real {ω' | X' j ω' = k ∧ A' j ω' = m} =
          P'.real {ω' | X j ω' = k ∧ A j ω' = m} := by
        refine measureReal_congr ?_
        filter_upwards [hX'_ae j hj, hA'_ae j hj] with ω' hXω' hAω'
        simp [hXω', hAω']
      have hX_congr : P'.real {ω' | X' j ω' = k} = P'.real {ω' | X j ω' = k} := by
        refine measureReal_congr ?_
        filter_upwards [hX'_ae j hj] with ω' hXω'
        simp [hXω']
      rw [hXA_congr, hX_congr, (hlvl j hj).2.2.2.2.2.1 k m]
    · exact (hlvl j hj).2.2.2.2.2.2.1.congr fun r ↦ (hξ'_ae j hj r).symm
    · rw [Measure.map_congr (hξ'_ae j hj r), (hlvl j hj).2.2.2.2.2.2.2.1 r]
    · refine (hlvl j hj).2.2.2.2.2.2.2.2.1.congr ?_ ?_
      · filter_upwards [hX'_ae j hj, hA'_ae j hj] with ω' hXω' hAω'
        rw [hXω', hAω']
      · filter_upwards [hξ'_all_ae j hj] with ω' hξω'
        exact (funext hξω').symm

theorem IsSizeBiasSpine.measureReal_Sn_Ln_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hSp : IsSizeBiasSpine P Z P' n X L R) (k u : ℕ) :
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    P'.real {ω' | Sn ω' = k ∧ Ln ω' = u} =
      if u < k then P.real {ω | Z n ω = k} else 0 := by
  intro Ln Sn
  obtain ⟨X', A', L', R', ξ', hX'_meas, hA'_meas, hL'_meas, hR'_meas, hξ'_meas,
    hAX'_le, hL'_eq, _, hLR'_sum, hind'_lvl, hlvl'⟩ := hSp.exists_measurable_modification
  let Sm : ℕ → Ω' → ℕ :=
    fun m ω' ↦ 1 + ∑ j ∈ Finset.Icc (n + 1 - m) n, (L' j ω' + R' j ω')
  let Lm : ℕ → Ω' → ℕ :=
    fun m ω' ↦ ∑ j ∈ Finset.Icc (n + 1 - m) n, L' j ω'
  have hSm_meas : ∀ m, Measurable (Sm m) := fun m ↦
    measurable_const.add (Finset.measurable_sum _ fun j _ ↦ (hL'_meas j).add (hR'_meas j))
  have hLm_meas : ∀ m, Measurable (Lm m) := fun m ↦
    Finset.measurable_sum _ fun j _ ↦ hL'_meas j
  have hind_m : ∀ m : ℕ, m ≤ n → ∀ k' u' : ℕ,
      P'.real {ω' | Sm m ω' = k' ∧ Lm m ω' = u'} =
        if u' < k' then P.real {ω | Z m ω = k'} else 0 := by
    intro m
    induction m with
    | zero =>
      intro _ k' u'
      have hIcc0 : Finset.Icc (n + 1 - 0) n = ∅ := Finset.Icc_eq_empty (by omega)
      have hSm0 : ∀ ω', Sm 0 ω' = 1 := fun ω' ↦ by dsimp only [Sm]; rw [hIcc0]; simp
      have hLm0 : ∀ ω', Lm 0 ω' = 0 := fun ω' ↦ by dsimp only [Lm]; rw [hIcc0]; simp
      have hZ0 : P.real {ω | Z 0 ω = k'} = if k' = 1 then 1 else 0 := by
        have hcongr : P.real {ω | Z 0 ω = k'} = P.real {ω : Ω | (1 : ℕ) = k'} := by
          refine measureReal_congr ?_
          filter_upwards [hGW.2.choose_spec.2.2.2.1] with ω hω
          simp [hω]
        rw [hcongr]
        by_cases hk1 : k' = 1
        · subst hk1; simp [probReal_univ]
        · have hempty : {ω : Ω | (1 : ℕ) = k'} = ∅ := by ext; simp [Ne.symm hk1]
          rw [hempty, measureReal_empty, ite_eq_right_iff.2 fun h ↦ False.elim (hk1 h)]
      simp_rw [hSm0, hLm0, hZ0]
      by_cases hk1 : k' = 1
      · subst hk1
        by_cases hu0 : u' = 0
        · subst hu0; simp [probReal_univ]
        · have hempty : {ω' : Ω' | 1 = 1 ∧ 0 = u'} = ∅ := by ext; simp [Ne.symm hu0]
          have hnot : ¬ (u' < 1) := by omega
          rw [hempty, measureReal_empty]
          simp [hnot]
      · have hempty : {ω' : Ω' | 1 = k' ∧ 0 = u'} = ∅ := by ext; simp [Ne.symm hk1]
        rw [hempty, measureReal_empty]
        simp [hk1]
    | succ m ih =>
      intro hm1 k' u'
      let j₀ : ℕ := n - m
      have hj₀_mem : j₀ ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hsub1 : n + 1 - (m + 1) = j₀ := by omega
      have hsub0 : n + 1 - m = j₀ + 1 := by omega
      have hnj₀ : n - j₀ = m := by omega
      have hIcc_ins : Finset.Icc j₀ n = insert j₀ (Finset.Icc (j₀ + 1) n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hj₀_notMem : j₀ ∉ Finset.Icc (j₀ + 1) n := by simp
      have hSm_succ : Sm (m + 1) =
          fun ω' ↦ (∑ r ∈ Finset.range (X' j₀ ω'), ξ' j₀ r ω') + Sm m ω' := by
        ext ω'
        dsimp only [Sm]
        rw [hsub1, hsub0, hIcc_ins, Finset.sum_insert hj₀_notMem, hLR'_sum j₀ ω']
        omega
      have hLm_succ : Lm (m + 1) =
          fun ω' ↦ (∑ r ∈ Finset.range (A' j₀ ω'), ξ' j₀ r ω') + Lm m ω' := by
        ext ω'
        dsimp only [Lm]
        rw [hsub1, hsub0, hIcc_ins, Finset.sum_insert hj₀_notMem, ← hL'_eq j₀ ω']
      let S_left : Finset (Finset.Icc 1 n) := {⟨j₀, hj₀_mem⟩}
      let S_right : Finset (Finset.Icc 1 n) :=
        Finset.univ.filter (fun j : Finset.Icc 1 n ↦ j.1 ∈ Finset.Icc (j₀ + 1) n)
      have hdisj : Disjoint S_left S_right := by
        rw [Finset.disjoint_singleton_left, Finset.mem_filter]
        rintro ⟨_, hmem⟩
        simp only [Finset.mem_Icc] at hmem
        omega
      have hsum_S_right : ∀ g : ℕ → ℕ,
          (∑ j : S_right, g j.1.1) = ∑ r ∈ Finset.Icc (j₀ + 1) n, g r := by
        intro g
        refine Finset.sum_bij (fun (j : S_right) _ ↦ j.1.1)
          (fun j _ ↦ (Finset.mem_filter.mp j.2).2)
          (fun j₁ _ j₂ _ h ↦ Subtype.ext (Subtype.ext h))
          (fun r hr ↦ ⟨⟨⟨r, Finset.mem_Icc.2 ⟨by
            have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩⟩,
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hr⟩⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ ↦ rfl)
      have hind_finset := hind'_lvl.indepFun_finset₀ S_left S_right hdisj
        (fun j ↦ ((hX'_meas j.1).prodMk
          ((hA'_meas j.1).prodMk (measurable_pi_iff.2 fun r ↦ hξ'_meas j.1 r))).aemeasurable)
      let ψ_left : (S_left → ℕ × ℕ × (ℕ → ℕ)) → ℕ × ℕ × (ℕ → ℕ) :=
        fun c ↦ c ⟨⟨j₀, hj₀_mem⟩, Finset.mem_singleton_self _⟩
      let ψ_right : (S_right → ℕ × ℕ × (ℕ → ℕ)) → ℕ × ℕ :=
        fun c ↦
          (1 + ∑ j : S_right, ∑ r ∈ Finset.range (c j).1, (c j).2.2 r,
           ∑ j : S_right, ∑ r ∈ Finset.range (c j).2.1, (c j).2.2 r)
      have hψ_left_meas : Measurable ψ_left := measurable_pi_apply _
      have hψ_right_meas : Measurable ψ_right := by
        refine (measurable_const.add (Finset.measurable_sum Finset.univ fun j _ ↦ ?_)).prodMk
          (Finset.measurable_sum Finset.univ fun j _ ↦ ?_)
        · exact measurable_sum_range (measurable_fst.comp (measurable_pi_apply j))
            (fun r ↦ (measurable_pi_apply r).comp
              (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply j))))
        · exact measurable_sum_range
            (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply j)))
            (fun r ↦ (measurable_pi_apply r).comp
              (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply j))))
      have hleft_eq :
          (ψ_left ∘ fun a (i : S_left) ↦ (X' i.1.1 a, A' i.1.1 a, fun r ↦ ξ' i.1.1 r a)) =
            fun ω' ↦ (X' j₀ ω', A' j₀ ω', fun r ↦ ξ' j₀ r ω') := rfl
      have hright_eq :
          (ψ_right ∘ fun a (i : S_right) ↦ (X' i.1.1 a, A' i.1.1 a, fun r ↦ ξ' i.1.1 r a)) =
            fun ω' ↦ (Sm m ω', Lm m ω') := by
        ext ω' : 1
        refine Prod.ext ?_ ?_
        · dsimp only [ψ_right, Sm, Function.comp_apply]
          rw [hsub0]
          congr 1
          rw [hsum_S_right (fun r ↦ ∑ i ∈ Finset.range (X' r ω'), ξ' r i ω')]
          exact Finset.sum_congr rfl fun r _ ↦ (hLR'_sum r ω').symm
        · dsimp only [ψ_right, Lm, Function.comp_apply]
          rw [hsub0, hsum_S_right (fun r ↦ ∑ i ∈ Finset.range (A' r ω'), ξ' r i ω')]
          exact Finset.sum_congr rfl fun r _ ↦ (hL'_eq r ω').symm
      have hind_prev : IndepFun (fun ω' ↦ (X' j₀ ω', A' j₀ ω', fun r ↦ ξ' j₀ r ω'))
          (fun ω' ↦ (Sm m ω', Lm m ω')) P' := by
        rw [← hleft_eq, ← hright_eq]
        exact hind_finset.comp hψ_left_meas hψ_right_meas
      have hj₀_props := hlvl' j₀ hj₀_mem
      have hXA_pmf : ∀ d a : ℕ, P'.real {ω' | X' j₀ ω' = d ∧ A' j₀ ω' = a} =
          if a ≤ d then P.real {ω | Z 1 ω = d + 1} else 0 :=
        fun d a ↦ (IsSizeBiasSpine.measureReal_X_A hcrit hj₀_props.2.2.2.1
          hj₀_props.2.2.2.2.1 d a).2
      have hξ_law_m : ∀ r : ℕ, P'.map (ξ' j₀ r) = P.map (Z m) := by
        intro r
        rw [hj₀_props.2.2.2.2.2.2.1 r, hnj₀]
      rw [hSm_succ, hLm_succ]
      exact spine_level_step P P' hGW (hSm_meas m) (hLm_meas m) (hX'_meas j₀) (hA'_meas j₀)
        (hξ'_meas j₀) (hAX'_le j₀) hXA_pmf hj₀_props.2.2.2.2.2.1 hξ_law_m
        hj₀_props.2.2.2.2.2.2.2 hind_prev (ih (by omega)) k' u'
  have hSn_ae : Sm n =ᵐ[P'] Sn := by
    have hsubn : n + 1 - n = 1 := by omega
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' ∧ R' j ω' = R j ω' :=
      ae_all_finset (Finset.Icc 1 n) fun j hj ↦
        (hlvl' j hj).2.1.and (hlvl' j hj).2.2.1
    filter_upwards [hall] with ω' hω'
    dsimp only [Sm, Sn]
    rw [hsubn]
    congr 1
    exact Finset.sum_congr rfl fun j hj ↦ by rw [(hω' j hj).1, (hω' j hj).2]
  have hLn_ae : Lm n =ᵐ[P'] Ln := by
    have hsubn : n + 1 - n = 1 := by omega
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' :=
      ae_all_finset (Finset.Icc 1 n) fun j hj ↦ (hlvl' j hj).2.1
    filter_upwards [hall] with ω' hω'
    dsimp only [Lm, Ln]
    rw [hsubn]
    exact Finset.sum_congr rfl fun j hj ↦ hω' j hj
  have hcongr : P'.real {ω' | Sn ω' = k ∧ Ln ω' = u} =
      P'.real {ω' | Sm n ω' = k ∧ Lm n ω' = u} := by
    refine measureReal_congr ?_
    filter_upwards [hSn_ae, hLn_ae] with ω' hS hL
    simp [hS, hL]
  rw [hcongr, hind_m n le_rfl k u]

theorem IsSizeBiasSpine.aemeasurable_L_R
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hSp : IsSizeBiasSpine P Z P' n X L R) :
    (∀ j ∈ Finset.Icc 1 n, AEMeasurable (L j) P' ∧ AEMeasurable (R j) P') ∧
      AEMeasurable (fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω') P' ∧
      AEMeasurable (fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, R j ω') P' ∧
      AEMeasurable (fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')) P' := by
  obtain ⟨_, _, L', R', _, _, _, hL'_meas, hR'_meas, _, _, _, _, _, _, hlvl'⟩ :=
    hSp.exists_measurable_modification
  have hLR : ∀ j ∈ Finset.Icc 1 n, AEMeasurable (L j) P' ∧ AEMeasurable (R j) P' :=
    fun j hj ↦ ⟨(hL'_meas j).aemeasurable.congr (hlvl' j hj).2.1,
      (hR'_meas j).aemeasurable.congr (hlvl' j hj).2.2.1⟩
  have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' ∧ R' j ω' = R j ω' :=
    ae_all_finset (Finset.Icc 1 n) fun j hj ↦
      (hlvl' j hj).2.1.and (hlvl' j hj).2.2.1
  refine ⟨hLR, ?_, ?_, ?_⟩
  · refine (Finset.measurable_sum (Finset.Icc 1 n) fun j _ ↦ hL'_meas j).aemeasurable.congr ?_
    filter_upwards [hall] with ω' hω'
    exact Finset.sum_congr rfl fun j hj ↦ (hω' j hj).1
  · refine ((Finset.measurable_sum (Finset.Icc 1 n)
      fun j _ ↦ hR'_meas j).const_add 1).aemeasurable.congr ?_
    filter_upwards [hall] with ω' hω'
    exact congrArg (1 + ·) (Finset.sum_congr rfl fun j hj ↦ (hω' j hj).2)
  · refine ((Finset.measurable_sum (Finset.Icc 1 n)
      fun j _ ↦ (hL'_meas j).add (hR'_meas j)).const_add 1).aemeasurable.congr ?_
    filter_upwards [hall] with ω' hω'
    exact congrArg (1 + ·)
      (Finset.sum_congr rfl fun j hj ↦ by simp [(hω' j hj).1, (hω' j hj).2])

theorem IsSizeBiasSpine.measureReal_Sn_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1)
    (hSp : IsSizeBiasSpine P Z P' n X L R) (k : ℕ) :
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    P'.real {ω' | Sn ω' = k} = (k : ℝ) * P.real {ω | Z n ω = k} := by
  intro Sn
  obtain ⟨_, _, L', R', _, _, _, hL'_meas, hR'_meas, _, _, _, _, _, _, hlvl'⟩ :=
    hSp.exists_measurable_modification
  let Sn' : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L' j ω' + R' j ω')
  let Ln' : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L' j ω'
  have hSn'_meas : Measurable Sn' :=
    measurable_const.add (Finset.measurable_sum _ fun j _ ↦ (hL'_meas j).add (hR'_meas j))
  have hLn'_meas : Measurable Ln' :=
    Finset.measurable_sum _ fun j _ ↦ hL'_meas j
  have hSn_ae : Sn' =ᵐ[P'] Sn := by
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' ∧ R' j ω' = R j ω' :=
      ae_all_finset (Finset.Icc 1 n) fun j hj ↦
        (hlvl' j hj).2.1.and (hlvl' j hj).2.2.1
    filter_upwards [hall] with ω' hω'
    dsimp only [Sn', Sn]
    congr 1
    exact Finset.sum_congr rfl fun j hj ↦ by rw [(hω' j hj).1, (hω' j hj).2]
  have hLn_ae : Ln' =ᵐ[P'] fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω' := by
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' :=
      ae_all_finset (Finset.Icc 1 n) fun j hj ↦ (hlvl' j hj).2.1
    filter_upwards [hall] with ω' hω'
    exact Finset.sum_congr rfl fun j hj ↦ hω' j hj
  have hSn_congr : P'.real {ω' | Sn ω' = k} = P'.real {ω' | Sn' ω' = k} := by
    refine measureReal_congr ?_
    filter_upwards [hSn_ae] with ω' hω'
    simp [hω']
  rw [hSn_congr]
  obtain ⟨htsum, _⟩ := measureReal_inter_fiber_tsum P'
    (E := {ω' | Sn' ω' = k}) (hSn'_meas (measurableSet_singleton k)) hLn'_meas
    (fun _ : ℕ ↦ True)
  simp only [Set.ofPred_true, inter_univ] at htsum
  let e := Equiv.subtypeUnivEquiv (α := ℕ) (p := fun _ ↦ True) (fun _ ↦ trivial)
  have htsum' : P'.real {ω' | Sn' ω' = k} =
      ∑' u : ℕ, P'.real ({ω' | Sn' ω' = k} ∩ {ω' | Ln' ω' = u}) := by
    rw [← htsum]
    exact e.tsum_eq (fun u : ℕ ↦ P'.real ({ω' | Sn' ω' = k} ∩ {ω' | Ln' ω' = u}))
  have hterm : ∀ u : ℕ,
      P'.real ({ω' | Sn' ω' = k} ∩ {ω' | Ln' ω' = u}) =
        if u < k then P.real {ω | Z n ω = k} else 0 := by
    intro u
    rw [← hSp.measureReal_Sn_Ln_eq hGW hcrit k u]
    refine measureReal_congr ?_
    filter_upwards [hSn_ae, hLn_ae] with ω' hS hL
    change (Sn' ω' = k ∧ Ln' ω' = u) = (Sn ω' = k ∧ (∑ j ∈ Finset.Icc 1 n, L j ω') = u)
    rw [hS, hL]
  rw [htsum']
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range k) (fun u hu ↦ by
    rw [Finset.mem_range, not_lt] at hu
    exact ite_eq_right_iff.2 fun h ↦ False.elim (not_lt_of_ge hu h))]
  have hsum_range :
      (∑ u ∈ Finset.range k, if u < k then P.real {ω | Z n ω = k} else 0) =
        ∑ _u ∈ Finset.range k, P.real {ω | Z n ω = k} :=
    Finset.sum_congr rfl fun u hu ↦
      ite_eq_left_iff.2 fun h ↦ False.elim (h (Finset.mem_range.mp hu))
  rw [hsum_range, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Section 5.3 Item (1) (`\label{i171a}`, `SteinIntro.tex:3061, 3069-3076`): in the size-bias
Galton–Watson tree of a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$), the generation-$n$
size $S_n = 1 + \sum_{j=1}^n (L_{n,j} + R_{n,j})$ has the size-bias distribution of $Z_n$. -/
def Sec5_3_item_1_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpine P Z P' n X L R →
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
    IsSizeBias P (fun ω ↦ (Z n ω : ℝ)) P' Sn

theorem sec5_3_item_1 : Sec5_3_item_1_stmt := by
  intro Ω Ω' _ _ P _ P' _ Z n X L R hGW hcrit hSp
  dsimp only
  let Sn_nat : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
  have hZn_mean : ∫ ω, (Z n ω : ℝ) ∂P = 1 := hGW.integral_Z_eq_one hcrit n
  have hμ_pos : 0 < ∫ ω, (Z n ω : ℝ) ∂P := by rw [hZn_mean]; exact zero_lt_one
  have hSB := isSizeBias_of_nat_measureReal P P'
    (X := Z n) (S := Sn_nat) (hGW.aemeasurable_Z n) (hGW.integrable_Z n) hμ_pos
    hSp.aemeasurable_L_R.2.2.2 fun k ↦ by
      rw [hZn_mean, div_one]
      exact hSp.measureReal_Sn_eq hGW hcrit k
  have hcast : (fun ω' ↦ (Sn_nat ω' : ℝ)) =
      fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ)) := by
    ext ω'
    simp [Sn_nat, Nat.cast_add, Nat.cast_sum]
  rwa [hcast] at hSB

/-- Section 5.3 Item (2) (`\label{i172a}`, `SteinIntro.tex:3062-3063, 3077-3078`): in a critical
Galton–Watson process ($\mathbb{E}[Z_1] = 1$), if $Y_n \stackrel{d}{=} (Z_n \mid Z_n > 0)$ and
$Y_n^s$ has the size-bias distribution of $Y_n$, then $S_n \stackrel{d}{=} Y_n^s$. -/
def Sec5_3_item_2_stmt : Prop :=
  ∀ {Ω ΩY Ωs Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ωs] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (Ps : Measure Ωs) [IsProbabilityMeasure Ps]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {Y : ΩY → ℕ} {Ys : Ωs → ℝ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) →
    IsSizeBias PY (fun ω ↦ (Y ω : ℝ)) Ps Ys →
    IsSizeBiasSpine P Z P' n X L R →
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
    P'.map Sn = Ps.map Ys

theorem sec5_3_item_2 : Sec5_3_item_2_stmt := by
  intro Ω ΩY Ωs Ω' _ _ _ _ P _ PY _ Ps _ P' _ Z n Y Ys X L R hGW hcrit hY_meas hY_map hSB_Ys hSp
  dsimp only
  let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
  have hSB_Sn_Z : IsSizeBias P (fun ω ↦ (Z n ω : ℝ)) P' Sn :=
    sec5_3_item_1 P P' hGW hcrit hSp
  have hZn_nn : 0 ≤ᵐ[P] fun ω ↦ (Z n ω : ℝ) :=
    Eventually.of_forall fun ω ↦ Nat.cast_nonneg (Z n ω)
  have hZn_int : Integrable (fun ω ↦ (Z n ω : ℝ)) P := hGW.integrable_Z n
  have hZn_mean : ∫ ω, (Z n ω : ℝ) ∂P = 1 := hGW.integral_Z_eq_one hcrit n
  have hZn_pos : 0 < ∫ ω, (Z n ω : ℝ) ∂P := by rw [hZn_mean]; exact zero_lt_one
  have hcast_meas : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  have hY_real_meas : AEMeasurable (fun ω ↦ (Y ω : ℝ)) PY :=
    hcast_meas.comp_aemeasurable hY_meas
  have hZn_cond_meas : AEMeasurable (Z n) (ProbabilityTheory.cond P {ω | 0 < Z n ω}) :=
    (hGW.aemeasurable_Z n).mono_ac ProbabilityTheory.cond_absolutelyContinuous
  have hY_real_map : PY.map (fun ω ↦ (Y ω : ℝ)) =
      (ProbabilityTheory.cond P {ω | 0 < (Z n ω : ℝ)}).map (fun ω ↦ (Z n ω : ℝ)) := by
    have hset : {ω : Ω | 0 < (Z n ω : ℝ)} = {ω | 0 < Z n ω} := by ext; simp
    rw [hset]
    change PY.map ((Nat.cast : ℕ → ℝ) ∘ Y) =
      (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map ((Nat.cast : ℕ → ℝ) ∘ Z n)
    rw [← AEMeasurable.map_map_of_aemeasurable hcast_meas.aemeasurable hY_meas,
      ← AEMeasurable.map_map_of_aemeasurable hcast_meas.aemeasurable hZn_cond_meas, hY_map]
  have hSB_Sn_Y : IsSizeBias PY (fun ω ↦ (Y ω : ℝ)) P' Sn :=
    (sec5_3_sizeBias_cond_pos P PY P' hZn_nn hZn_int hZn_pos hY_real_meas hY_real_map).mp
      hSB_Sn_Z
  have hY_nn : 0 ≤ᵐ[PY] fun ω ↦ (Y ω : ℝ) := hSB_Sn_Y.1
  have hY_int : Integrable (fun ω ↦ (Y ω : ℝ)) PY := hSB_Sn_Y.2.1
  have hY_mean_pos : 0 < ∫ ω, (Y ω : ℝ) ∂PY := by
    have hid : IdentDistrib (fun ω ↦ (Y ω : ℝ)) (fun ω ↦ (Z n ω : ℝ))
        PY (ProbabilityTheory.cond P {ω | 0 < Z n ω}) := by
      refine ⟨hY_real_meas, hcast_meas.comp_aemeasurable hZn_cond_meas, ?_⟩
      have hset : {ω : Ω | 0 < (Z n ω : ℝ)} = {ω | 0 < Z n ω} := by ext; simp
      rwa [hset] at hY_real_map
    rw [hid.integral_eq]
    obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
    let S₀ : Set Ω := {ω | 0 < gwCanonical ξ' n ω}
    have hS₀_meas : MeasurableSet S₀ :=
      (measurable_gwCanonical hξ'_meas n) (MeasurableSet.of_discrete)
    have hSS₀ : ({ω : Ω | 0 < Z n ω} : Set Ω) =ᵐ[P] S₀ := by
      filter_upwards [hZ_ae n] with ω hω
      change (0 < Z n ω) = (0 < gwCanonical ξ' n ω)
      rw [hω]
    have hcond_eq : ProbabilityTheory.cond P {ω | 0 < Z n ω} =
        (P S₀)⁻¹ • P.restrict S₀ := by
      rw [ProbabilityTheory.cond, measure_congr hSS₀, Measure.restrict_congr_set hSS₀]
    have hPS₀_ne_zero : P S₀ ≠ 0 :=
      (measure_congr hSS₀) ▸ hGW.measure_Z_pos_ne_zero hcrit n
    have hPS₀_ne_top : P S₀ ≠ ⊤ := measure_ne_top P S₀
    have hc_pos : 0 < (P S₀)⁻¹.toReal :=
      ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hPS₀_ne_top)
        (ENNReal.inv_ne_top.mpr hPS₀_ne_zero)
    have hZ_ind : S₀.indicator (fun ω ↦ (Z n ω : ℝ)) =ᵐ[P] fun ω ↦ (Z n ω : ℝ) := by
      filter_upwards [hZ_ae n] with ω hω
      by_cases h : ω ∈ S₀
      · exact indicator_of_mem h _
      · rw [indicator_of_notMem h]
        have h0 : gwCanonical ξ' n ω = 0 := Nat.eq_zero_of_not_pos h
        simp [hω, h0]
    rw [hcond_eq, integral_smul_measure, smul_eq_mul, ← integral_indicator hS₀_meas,
      integral_congr_ae hZ_ind, hZn_mean, mul_one]
    exact hc_pos
  rw [(sizeBias_law_characterization PY hY_nn hY_int hY_mean_pos).1 P' hSB_Sn_Y,
    (sizeBias_law_characterization PY hY_nn hY_int hY_mean_pos).1 Ps hSB_Ys]

/-- Section 5.3 Item (3) (`\label{i173}`, `SteinIntro.tex:3064, 3078-3079`): given $S_n = k$, the
distinguished vertex $v_n$ is uniformly distributed among the $k$ individuals of generation $n$,
i.e. $\mathbb{P}(S_n = k \wedge L_n = m) = \mathbb{P}(S_n = k) / k$ for $0 \le m < k$ and
$\mathbb{P}(S_n = k \wedge R_n = m) = \mathbb{P}(S_n = k) / k$ for $1 \le m \le k$. -/
def Sec5_3_item_3_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpine P Z P' n X L R →
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
    let Rn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, R j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    (∀ k m : ℕ, P'.real {ω' | Sn ω' = k ∧ Ln ω' = m} =
      if m < k then P'.real {ω' | Sn ω' = k} / (k : ℝ) else 0) ∧
    (∀ k m : ℕ, P'.real {ω' | Sn ω' = k ∧ Rn ω' = m} =
      if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Sn ω' = k} / (k : ℝ) else 0)

theorem sec5_3_item_3 : Sec5_3_item_3_stmt := by
  intro Ω Ω' _ _ P _ P' _ Z n X L R hGW hcrit hSp
  dsimp only
  let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
  let Rn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, R j ω'
  let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
  have hSL_add : ∀ ω', Ln ω' + Rn ω' = Sn ω' := by
    intro ω'
    dsimp only [Ln, Rn, Sn]
    rw [Finset.sum_add_distrib]
    omega
  have h1 : ∀ k m : ℕ, P'.real {ω' | Sn ω' = k ∧ Ln ω' = m} =
      if m < k then P'.real {ω' | Sn ω' = k} / (k : ℝ) else 0 := by
    intro k m
    rw [hSp.measureReal_Sn_Ln_eq hGW hcrit k m, hSp.measureReal_Sn_eq hGW hcrit k]
    by_cases hmk : m < k
    · have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [ite_eq_left_iff.2 fun h ↦ False.elim (h hmk),
        ite_eq_left_iff.2 fun h ↦ False.elim (h hmk),
        mul_div_cancel_left₀ _ hk0]
    · simp [hmk]
  refine ⟨h1, fun k m ↦ ?_⟩
  by_cases hmk : 1 ≤ m ∧ m ≤ k
  · have hset : {ω' : Ω' | Sn ω' = k ∧ Rn ω' = m} = {ω' | Sn ω' = k ∧ Ln ω' = k - m} := by
      ext ω'
      simp only [mem_ofPred_eq]
      have hadd := hSL_add ω'
      omega
    rw [hset, h1 k (k - m), ite_eq_left_iff.2 fun h ↦ by omega,
      ite_eq_left_iff.2 fun h ↦ False.elim (h hmk)]
  · have hempty : {ω' : Ω' | Sn ω' = k ∧ Rn ω' = m} = ∅ := by
      ext ω'
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨rfl, rfl⟩
      have hadd := hSL_add ω'
      have hR1 : 1 ≤ Rn ω' := Nat.le_add_right 1 _
      omega
    rw [hempty, measureReal_empty, ite_eq_right_iff.2 fun h ↦ False.elim (hmk h)]

/-- Section 5.3 size-bias tree-probability link to the spine joint law and normalization
(`I-1(b,c)`, `SteinIntro.tex:3048-3052, 3074-3079`): for a critical Galton–Watson process with
offspring PMF $p(k) = \mathbb{P}(Z_1 = k)$ and spine $(X, L, R)$ at generation $n$, summing
`gwSizeBiasProbV p t v` over all $(t, v)$ with $t_n = k$ and $\mathrm{left}(t, v) = m$ yields
$\mathbb{P}(S_n = k \wedge L_n = m)$, summing `gwSizeBiasProb p t` over $t_n = k$ yields
$\mathbb{P}(S_n = k) = k\,\mathbb{P}(Z_n = k)$, and `gwSizeBiasProb p` sums to $1$ over all
depth-$n$ planar trees. -/
def Sec5_3_gwSizeBiasProbV_sum_spine_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpine P Z P' n X L R →
    let p : ℕ → ℝ := fun k ↦ P.real {ω | Z 1 ω = k}
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    (Summable (gwSizeBiasProb p : GWTree n → ℝ) ∧ (∑' t : GWTree n, gwSizeBiasProb p t) = 1) ∧
    (∀ k : ℕ,
      Summable (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwSizeBiasProb p t.1) ∧
      (∑' t : {t : GWTree n // gwTreeGenSize t = k}, gwSizeBiasProb p t.1) =
        P'.real {ω' | Sn ω' = k}) ∧
    ∀ k m : ℕ,
      Summable
        (fun tv : {tv : Σ t : GWTree n, GWVertex t //
            gwTreeGenSize tv.1 = k ∧ gwLeftCount tv.1 tv.2 = m} ↦
          gwSizeBiasProbV p tv.1.1 tv.1.2) ∧
      (∑' tv : {tv : Σ t : GWTree n, GWVertex t //
          gwTreeGenSize tv.1 = k ∧ gwLeftCount tv.1 tv.2 = m},
        gwSizeBiasProbV p tv.1.1 tv.1.2) =
        P'.real {ω' | Sn ω' = k ∧ Ln ω' = m}

theorem sec5_3_gwSizeBiasProbV_sum_spine : Sec5_3_gwSizeBiasProbV_sum_spine_stmt := by
  intro Ω Ω' _ _ P _ P' _ Z n X L R hGW hcrit hSp
  dsimp only
  let p : ℕ → ℝ := fun k ↦ P.real {ω | Z 1 ω = k}
  let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
  let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
  have htree := sec5_3_gwProb_sum_genSize P hGW n
  refine ⟨?_, fun k ↦ ?_, fun k m ↦ ?_⟩
  · obtain ⟨ξ', hξ'_meas, hξ'_indep, hξ'_ident, hZ_ae⟩ := hGW.exists_measurable_array
    have hTn_meas : Measurable (gwTreeOfArray ξ' n) := measurable_gwTreeOfArray hξ'_meas n
    let A : GWTree n → Set Ω := fun t ↦ {ω | gwTreeOfArray ξ' n ω = t}
    have hA_meas : ∀ t, MeasurableSet (A t) := fun t ↦ hTn_meas (measurableSet_singleton t)
    have hA_disj : Pairwise (fun t₁ t₂ ↦ Disjoint (A t₁) (A t₂)) := by
      intro t₁ t₂ ht
      exact Set.disjoint_left.2 fun ω (h1 : gwTreeOfArray ξ' n ω = t₁)
        (h2 : gwTreeOfArray ξ' n ω = t₂) ↦ ht (h1.symm.trans h2)
    have hA_union : (⋃ t : GWTree n, A t) = univ := by
      ext ω; simp [A]
    have hnn : ∀ t : GWTree n, 0 ≤ gwSizeBiasProb p t := by
      intro t
      rw [sec5_3_eq_1711 p t,
        ← measureReal_gwTreeOfArray_eq_gwProb P Z hξ'_meas hξ'_indep hξ'_ident n t]
      exact mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
    have hlint_t : ∀ t : GWTree n,
        ENNReal.ofReal (gwSizeBiasProb p t) =
          ∫⁻ ω in A t, (gwCanonical ξ' n ω : ℝ≥0∞) ∂P := by
      intro t
      rw [sec5_3_eq_1711 p t,
        ← measureReal_gwTreeOfArray_eq_gwProb P Z hξ'_meas hξ'_indep hξ'_ident n t,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ofReal_measureReal (measure_ne_top P (A t))]
      have hcongr : ∀ ω ∈ A t, (gwCanonical ξ' n ω : ℝ≥0∞) = (gwTreeGenSize t : ℝ≥0∞) := by
        intro ω (hω : gwTreeOfArray ξ' n ω = t)
        rw [← gwTreeGenSize_gwTreeOfArray, hω]
      rw [setLIntegral_congr_fun (hA_meas t) hcongr, setLIntegral_const]
    have hlint_Z : ∫⁻ ω, (Z n ω : ℝ≥0∞) ∂P = 1 := by
      have heq : (fun ω ↦ (Z n ω : ℝ≥0∞)) = fun ω ↦ ENNReal.ofReal (Z n ω : ℝ) := by
        ext ω; exact (ENNReal.ofReal_natCast (Z n ω)).symm
      rw [heq, ← ofReal_integral_eq_lintegral_ofReal (hGW.integrable_Z n)
        (Eventually.of_forall fun ω ↦ Nat.cast_nonneg (Z n ω)),
        hGW.integral_Z_eq_one hcrit n, ENNReal.ofReal_one]
    have htsum_ennreal : (∑' t : GWTree n, ENNReal.ofReal (gwSizeBiasProb p t)) = 1 := by
      simp_rw [hlint_t]
      rw [← lintegral_iUnion hA_meas hA_disj, hA_union, Measure.restrict_univ]
      have hcongr_Z : (fun ω ↦ (gwCanonical ξ' n ω : ℝ≥0∞)) =ᵐ[P] fun ω ↦ (Z n ω : ℝ≥0∞) := by
        filter_upwards [hZ_ae n] with ω hω
        rw [hω]
      rw [lintegral_congr_ae hcongr_Z, hlint_Z]
    have hsum_sb : Summable (gwSizeBiasProb p : GWTree n → ℝ) := by
      refine summable_of_sum_le hnn (c := 1) fun s ↦ ?_
      have hle : (∑ t ∈ s, ENNReal.ofReal (gwSizeBiasProb p t)) ≤ 1 := by
        rw [← htsum_ennreal]
        exact ENNReal.sum_le_tsum s
      rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ ↦ hnn t)] at hle
      have htoReal := ENNReal.toReal_mono ENNReal.one_ne_top hle
      rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun t _ ↦ hnn t), ENNReal.toReal_one]
        at htoReal
    refine ⟨hsum_sb, ?_⟩
    have hofReal := (ENNReal.ofReal_tsum_of_nonneg hnn hsum_sb).trans htsum_ennreal
    have htoReal := congrArg ENNReal.toReal hofReal
    rwa [ENNReal.toReal_ofReal (tsum_nonneg hnn), ENNReal.toReal_one] at htoReal
  · have hcongr : (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwSizeBiasProb p t.1) =
        fun t ↦ (k : ℝ) * gwProb p t.1 := by
      ext t
      rw [sec5_3_eq_1711 p t.1, t.2]
    rw [hcongr]
    refine ⟨(htree.2 k).1.mul_left (k : ℝ), ?_⟩
    rw [tsum_mul_left, (htree.2 k).2, hSp.measureReal_Sn_eq hGW hcrit k]
  · let T_km := {tv : Σ t : GWTree n, GWVertex t //
      gwTreeGenSize tv.1 = k ∧ gwLeftCount tv.1 tv.2 = m}
    have hcongr : (fun tv : T_km ↦ gwSizeBiasProbV p tv.1.1 tv.1.2) =
        fun tv : T_km ↦ gwProb p tv.1.1 := by
      ext tv
      exact sec5_3_eq_1710 p tv.1.1 tv.1.2
    rw [hcongr, hSp.measureReal_Sn_Ln_eq hGW hcrit k m]
    by_cases hmk : m < k
    · let vm : ∀ t : {t : GWTree n // gwTreeGenSize t = k}, GWVertex t.1 :=
        fun t ↦ (gwVertexEquivFin t.1).symm ⟨m, t.2.symm ▸ hmk⟩
      have hvm_left : ∀ t : {t : GWTree n // gwTreeGenSize t = k},
          gwLeftCount t.1 (vm t) = m := by
        intro t
        change ((gwVertexEquivFin t.1 (vm t) : Fin (gwTreeGenSize t.1)) : ℕ) = m
        simp [vm]
      let e_km : T_km ≃ {t : GWTree n // gwTreeGenSize t = k} :=
        { toFun := fun tv ↦ ⟨tv.1.1, tv.2.1⟩
          invFun := fun t ↦ ⟨⟨t.1, vm t⟩, t.2, hvm_left t⟩
          left_inv := fun ⟨⟨t, v⟩, ht, hv⟩ ↦ by
            refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
            exact gwLeftCount_injective t ((hvm_left ⟨t, ht⟩).trans hv.symm)
          right_inv := fun ⟨t, ht⟩ ↦ rfl }
      rw [ite_eq_left_iff.2 fun h ↦ False.elim (h hmk)]
      exact ⟨(e_km.summable_iff (f := fun t : {t : GWTree n // gwTreeGenSize t = k} ↦
        gwProb p t.1)).mpr (htree.2 k).1,
        (e_km.tsum_eq (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦
          gwProb p t.1)).trans (htree.2 k).2⟩
    · have : IsEmpty T_km := ⟨fun ⟨⟨t, v⟩, ht, hv⟩ ↦ by
        have hlt : gwLeftCount t v < gwTreeGenSize t := by
          rw [← gwVertexEquivFin_apply_coe t v]
          exact (gwVertexEquivFin t v).2
        rw [ht, hv] at hlt
        exact hmk hlt⟩
      rw [ite_eq_right_iff.2 fun h ↦ False.elim (hmk h)]
      exact ⟨summable_empty, tsum_empty⟩

/-- Section 5.3 Equation (5.9) (`\label{1712}`, `SteinIntro.tex:3100-3113`): in the size-bias
Galton–Watson tree of a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$),
$\mathbb{P}(L_n = 0) = \mathbb{P}(Z_n > 0)$ and $S_n \mid \{L_n = 0\} \stackrel{d}{=} Y_n$. -/
def Sec5_3_eq_1712_stmt : Prop :=
  ∀ {Ω ΩY Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {Y : ΩY → ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) →
    IsSizeBiasSpine P Z P' n X L R →
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    P' {ω' | Ln ω' = 0} = P {ω | 0 < Z n ω} ∧
      (ProbabilityTheory.cond P' {ω' | Ln ω' = 0}).map Sn = PY.map Y

theorem sec5_3_eq_1712 : Sec5_3_eq_1712_stmt := by
  intro Ω ΩY Ω' _ _ _ P _ PY _ P' _ Z n Y X L R hGW hcrit _ hY_map hSp
  dsimp only
  let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
  let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
  obtain ⟨_, _, L', R', _, _, _, hL'_meas, hR'_meas, _, _, _, _, _, _, hlvl'⟩ :=
    hSp.exists_measurable_modification
  let Ln' : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L' j ω'
  let Sn' : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L' j ω' + R' j ω')
  have hLn'_meas : Measurable Ln' := Finset.measurable_sum _ fun j _ ↦ hL'_meas j
  have hSn'_meas : Measurable Sn' :=
    measurable_const.add (Finset.measurable_sum _ fun j _ ↦ (hL'_meas j).add (hR'_meas j))
  have hLn_ae : Ln' =ᵐ[P'] Ln := by
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' :=
      ae_all_finset (Finset.Icc 1 n) fun j hj ↦ (hlvl' j hj).2.1
    filter_upwards [hall] with ω' hω'
    exact Finset.sum_congr rfl fun j hj ↦ hω' j hj
  have hSn_ae : Sn' =ᵐ[P'] Sn := by
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' ∧ R' j ω' = R j ω' :=
      ae_all_finset (Finset.Icc 1 n) fun j hj ↦
        (hlvl' j hj).2.1.and (hlvl' j hj).2.2.1
    filter_upwards [hall] with ω' hω'
    dsimp only [Sn', Sn]
    congr 1
    exact Finset.sum_congr rfl fun j hj ↦ by rw [(hω' j hj).1, (hω' j hj).2]
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  let Zn' : Ω → ℕ := gwCanonical ξ' n
  have hZn'_meas : Measurable Zn' := measurable_gwCanonical hξ'_meas n
  have hLn_set_ae : ({ω' : Ω' | Ln ω' = 0} : Set Ω') =ᵐ[P'] {ω' | Ln' ω' = 0} := by
    filter_upwards [hLn_ae] with ω' hω'
    simp [hω']
  have hZn_set_ae : ({ω : Ω | 0 < Z n ω} : Set Ω) =ᵐ[P] {ω | 0 < Zn' ω} := by
    filter_upwards [hZ_ae n] with ω hω
    simp [Zn', hω]
  have hterm_eq : ∀ k : ℕ,
      P'.real ({ω' | Ln' ω' = 0} ∩ {ω' | Sn' ω' = k}) =
        P.real ({ω | 0 < Zn' ω} ∩ {ω | Zn' ω = k}) := by
    intro k
    have h1 : P'.real ({ω' | Ln' ω' = 0} ∩ {ω' | Sn' ω' = k}) =
        P'.real {ω' | Sn ω' = k ∧ Ln ω' = 0} := by
      refine measureReal_congr ?_
      filter_upwards [hSn_ae, hLn_ae] with ω' hS hL
      simp [hS, hL, and_comm]
    rw [h1, hSp.measureReal_Sn_Ln_eq hGW hcrit k 0]
    by_cases hk : 0 < k
    · have h2 : ({ω : Ω | 0 < Zn' ω} ∩ {ω | Zn' ω = k}) = {ω | Zn' ω = k} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; omega
      rw [h2, ite_eq_left_iff.2 fun h ↦ False.elim (h hk)]
      refine measureReal_congr ?_
      filter_upwards [hZ_ae n] with ω hω
      simp [Zn', hω]
    · have h2 : ({ω : Ω | 0 < Zn' ω} ∩ {ω | Zn' ω = k}) = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hpos, rfl⟩
        exact hk hpos
      rw [h2, measureReal_empty, ite_eq_right_iff.2 fun h ↦ False.elim (hk h)]
  have hreal_eq : P'.real {ω' | Ln' ω' = 0} = P.real {ω | 0 < Zn' ω} := by
    obtain ⟨htsum₁, _⟩ := measureReal_inter_fiber_tsum P'
      (E := {ω' | Ln' ω' = 0}) (hLn'_meas (measurableSet_singleton 0)) hSn'_meas
      (fun _ : ℕ ↦ True)
    obtain ⟨htsum₂, _⟩ := measureReal_inter_fiber_tsum P
      (E := {ω | 0 < Zn' ω}) (hZn'_meas (MeasurableSet.of_discrete)) hZn'_meas
      (fun _ : ℕ ↦ True)
    simp only [Set.ofPred_true, inter_univ] at htsum₁ htsum₂
    rw [← htsum₁, ← htsum₂]
    exact tsum_congr fun k ↦ hterm_eq k.1
  have hmeas_eq : P' {ω' | Ln ω' = 0} = P {ω | 0 < Z n ω} := by
    rw [measure_congr hLn_set_ae, measure_congr hZn_set_ae,
      ← ofReal_measureReal (measure_ne_top P' _),
      ← ofReal_measureReal (measure_ne_top P _), hreal_eq]
  refine ⟨hmeas_eq, ?_⟩
  rw [hY_map]
  have hcond_P' : ProbabilityTheory.cond P' {ω' | Ln ω' = 0} =
      ProbabilityTheory.cond P' {ω' | Ln' ω' = 0} := by
    rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
      measure_congr hLn_set_ae, Measure.restrict_congr_set hLn_set_ae]
  have hcond_P : ProbabilityTheory.cond P {ω | 0 < Z n ω} =
      ProbabilityTheory.cond P {ω | 0 < Zn' ω} := by
    rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
      measure_congr hZn_set_ae, Measure.restrict_congr_set hZn_set_ae]
  rw [hcond_P', hcond_P]
  have hSn_cond_ae : Sn =ᵐ[ProbabilityTheory.cond P' {ω' | Ln' ω' = 0}] Sn' :=
    ProbabilityTheory.cond_absolutelyContinuous hSn_ae.symm
  have hZn_cond_ae : Z n =ᵐ[ProbabilityTheory.cond P {ω | 0 < Zn' ω}] Zn' :=
    ProbabilityTheory.cond_absolutelyContinuous (hZ_ae n)
  rw [Measure.map_congr hSn_cond_ae, Measure.map_congr hZn_cond_ae]
  have hLn'_ne : P' {ω' | Ln' ω' = 0} ≠ 0 := by
    rw [← measure_congr hLn_set_ae, hmeas_eq]
    exact hGW.measure_Z_pos_ne_zero hcrit n
  have hZn'_ne : P {ω | 0 < Zn' ω} ≠ 0 := by
    rw [← measure_congr hZn_set_ae]
    exact hGW.measure_Z_pos_ne_zero hcrit n
  have : IsProbabilityMeasure (ProbabilityTheory.cond P' {ω' | Ln' ω' = 0}) :=
    ProbabilityTheory.cond_isProbabilityMeasure hLn'_ne
  have : IsProbabilityMeasure (ProbabilityTheory.cond P {ω | 0 < Zn' ω}) :=
    ProbabilityTheory.cond_isProbabilityMeasure hZn'_ne
  refine map_eq_of_measureReal_eq hSn'_meas.aemeasurable hZn'_meas.aemeasurable fun k ↦ ?_
  rw [cond_real_apply P' {ω' | Ln' ω' = 0} _ (hLn'_meas (measurableSet_singleton 0)),
    cond_real_apply P {ω | 0 < Zn' ω} _ (hZn'_meas (MeasurableSet.of_discrete)),
    hreal_eq]
  congr 1
  exact hterm_eq k

/-- Section 5.3 non-independence of $L_{n,j}$ and $R_{n,j}$ (`SteinIntro.tex:3122-3126`):
$L_{n,n}$ and $R_{n,n}$ are the numbers of siblings of $v_n$ to the left and right
($L_{n,n} + R_{n,n} = X_n$ a.s.), and for fixed $j$, $L_{n,j}$ and $R_{n,j}$ are in general not
independent (witnessed by $Z_1 \sim \frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$ at $j = n$). -/
def Sec5_3_not_indep_L_R_stmt : Prop :=
  (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    1 ≤ n →
    IsGaltonWatson P Z →
    IsSizeBiasSpine P Z P' n X L R →
    ∀ᵐ ω' ∂P', L n ω' + R n ω' = X n ω') ∧
  ∃ (Ω Ω' : Type) (_ : MeasurableSpace Ω) (_ : MeasurableSpace Ω')
    (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (P' : Measure Ω') (_ : IsProbabilityMeasure P')
    (Z : ℕ → Ω → ℕ) (X L R : ℕ → Ω' → ℕ),
    IsGaltonWatson P Z ∧
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 ∧
    IsSizeBiasSpine P Z P' 1 X L R ∧
    ¬ IndepFun (L 1) (R 1) P'

theorem sec5_3_not_indep_L_R : Sec5_3_not_indep_L_R_stmt := by
  refine ⟨?_, ?_⟩
  · intro Ω Ω' _ _ P _ P' _ Z n X L R hn hGW hSp
    have hn_mem : n ∈ Finset.Icc 1 n := Finset.mem_Icc.2 ⟨hn, le_rfl⟩
    obtain ⟨X', _, L', R', ξ', _, _, _, _, hξ'_meas, _, _, _, hLR'_sum, _, hlvl'⟩ :=
      hSp.exists_measurable_modification
    have hn_props := hlvl' n hn_mem
    have hξ_one : ∀ r : ℕ, ξ' n r =ᵐ[P'] fun _ ↦ 1 := by
      intro r
      have hlaw := hn_props.2.2.2.2.2.2.1 r
      rw [Nat.sub_self] at hlaw
      have hprob1 : P'.real {ω' | ξ' n r ω' = 1} = 1 := by
        have h1 := map_measureReal_apply (hξ'_meas n r) (measurableSet_singleton 1) (μ := P')
        rw [hlaw, map_measureReal_apply_of_aemeasurable (hGW.aemeasurable_Z 0)
          (measurableSet_singleton 1)] at h1
        have hcongr : P.real {ω | Z 0 ω = 1} = 1 := by
          have h2 : P.real {ω | Z 0 ω = 1} = P.real (univ : Set _) := by
            refine measureReal_congr ?_
            filter_upwards [hGW.2.choose_spec.2.2.2.1] with ω hω
            simp [hω]
          rw [h2, probReal_univ]
        exact h1.symm.trans hcongr
      have hcompl0 : P' {ω' | ξ' n r ω' ≠ 1} = 0 := by
        have hcompl_real : P'.real ({ω' | ξ' n r ω' = 1}ᶜ) = 0 := by
          have hsub := probReal_compl_eq_one_sub (μ := P')
            (s := {ω' | ξ' n r ω' = 1}) (hξ'_meas n r (measurableSet_singleton 1))
          rw [hsub, hprob1, sub_self]
        have hofReal := ofReal_measureReal (measure_ne_top P' ({ω' | ξ' n r ω' = 1}ᶜ))
        rw [hcompl_real, ENNReal.ofReal_zero] at hofReal
        exact hofReal.symm
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hcompl0] with ω' hω'
      exact not_not.mp hω'
    have hξ_all : ∀ᵐ ω' ∂P', ∀ r : ℕ, ξ' n r ω' = 1 := ae_all_iff.2 hξ_one
    filter_upwards [hn_props.1, hn_props.2.1, hn_props.2.2.1, hξ_all] with ω' hX hL hR hξ
    rw [← hL, ← hR, ← hX, hLR'_sum n ω']
    have hsum1 : (∑ r ∈ Finset.range (X' n ω'), ξ' n r ω') =
        ∑ _r ∈ Finset.range (X' n ω'), 1 :=
      Finset.sum_congr rfl fun r _ ↦ hξ r
    rw [hsum1, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  · obtain ⟨Ω, mΩ, P, hP, Z, hGW, hcrit, _, hint3, _, hZ1_2⟩ :=
      sec5_3_exists_isGaltonWatson_pos_var
    have hZ1_sq_int : Integrable (fun ω ↦ (Z 1 ω : ℝ) ^ 2) P := by
      refine ((integrable_const 1).add hint3).mono'
        ((hGW.integrable_Z 1).aestronglyMeasurable.pow 2)
        (Eventually.of_forall fun ω ↦ ?_)
      have hx : 0 ≤ (Z 1 ω : ℝ) := Nat.cast_nonneg (Z 1 ω)
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hx]
      rcases le_or_gt (Z 1 ω : ℝ) 1 with hle | hgt
      · nlinarith [pow_nonneg hx 3]
      · nlinarith [sq_nonneg (Z 1 ω : ℝ)]
    have hZ1_L2 : MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P :=
      (memLp_two_iff_integrable_sq (hGW.integrable_Z 1).aestronglyMeasurable).mpr hZ1_sq_int
    obtain ⟨Ω', mΩ', P', hP', X, L, R, R', U, hCoup, _⟩ :=
      sec5_3_exists_isSizeBiasSpineCoupling P hGW hcrit hZ1_L2 1
    have hSp : IsSizeBiasSpine P Z P' 1 X L R := hCoup.1
    refine ⟨Ω, Ω', mΩ, mΩ', P, hP, P', hP', Z, X, L, R, hGW, hcrit, hSp, ?_⟩
    intro hind
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 1, L j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 1, (L j ω' + R j ω')
    have hLn_eq : ∀ ω', Ln ω' = L 1 ω' := fun ω' ↦ by simp [Ln]
    have hSn_eq : ∀ ω', Sn ω' = 1 + (L 1 ω' + R 1 ω') := fun ω' ↦ by simp [Sn]
    have hSn2 : P'.real {ω' | Sn ω' = 2} = 1 := by
      rw [hSp.measureReal_Sn_eq hGW hcrit 2, hZ1_2]
      norm_num
    have hL0R0_zero : P'.real ({ω' | L 1 ω' = 0} ∩ {ω' | R 1 ω' = 0}) = 0 := by
      have hsub : ({ω' : Ω' | L 1 ω' = 0} ∩ {ω' | R 1 ω' = 0}) ⊆ {ω' | Sn ω' = 1} := by
        rintro ω' ⟨hL : L 1 ω' = 0, hR : R 1 ω' = 0⟩
        change Sn ω' = 1
        rw [hSn_eq ω', hL, hR]
      have hSn1_zero : P'.real {ω' | Sn ω' = 1} = 0 := by
        obtain ⟨_, _, L', R', _, _, _, hL'_meas, hR'_meas, _, _, _, _, _, _, hlvl'⟩ :=
          hSp.exists_measurable_modification
        have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 1 := by simp
        have hSn_ae : (fun ω' ↦ 1 + (L' 1 ω' + R' 1 ω')) =ᵐ[P'] Sn := by
          filter_upwards [(hlvl' 1 h1_mem).2.1, (hlvl' 1 h1_mem).2.2.1] with ω' hL hR
          rw [hSn_eq ω', hL, hR]
        have hSn1_congr : P'.real {ω' | Sn ω' = 1} =
            P'.real {ω' | 1 + (L' 1 ω' + R' 1 ω') = 1} := by
          refine measureReal_congr ?_
          filter_upwards [hSn_ae] with ω' hω'
          simp [hω']
        have hSn2_congr : P'.real {ω' | Sn ω' = 2} =
            P'.real {ω' | 1 + (L' 1 ω' + R' 1 ω') = 2} := by
          refine measureReal_congr ?_
          filter_upwards [hSn_ae] with ω' hω'
          simp [hω']
        have hmeas1 : MeasurableSet {ω' | 1 + (L' 1 ω' + R' 1 ω') = 1} :=
          (measurable_const.add ((hL'_meas 1).add (hR'_meas 1))) (measurableSet_singleton 1)
        have hdisj' : Disjoint {ω' : Ω' | 1 + (L' 1 ω' + R' 1 ω') = 2}
            {ω' | 1 + (L' 1 ω' + R' 1 ω') = 1} :=
          Set.disjoint_left.2 fun ω' (h2 : 1 + (L' 1 ω' + R' 1 ω') = 2)
            (h1 : 1 + (L' 1 ω' + R' 1 ω') = 1) ↦ by omega
        have hunion_le : P'.real ({ω' | 1 + (L' 1 ω' + R' 1 ω') = 2} ∪
            {ω' | 1 + (L' 1 ω' + R' 1 ω') = 1}) ≤ 1 :=
          (measureReal_mono (Set.subset_univ _) (measure_ne_top P' _)).trans_eq probReal_univ
        rw [measureReal_union hdisj' hmeas1, ← hSn2_congr, ← hSn1_congr, hSn2] at hunion_le
        linarith [(measureReal_nonneg : 0 ≤ P'.real {ω' | Sn ω' = 1})]
      exact le_antisymm
        ((measureReal_mono hsub (measure_ne_top P' _)).trans_eq hSn1_zero) measureReal_nonneg
    have hL0_pos : 0 < P'.real {ω' | L 1 ω' = 0} := by
      have hsub : {ω' : Ω' | Sn ω' = 2 ∧ Ln ω' = 0} ⊆ {ω' | L 1 ω' = 0} := by
        rintro ω' ⟨_, hL : Ln ω' = 0⟩
        change L 1 ω' = 0
        rwa [← hLn_eq ω']
      have hpos : P'.real {ω' | Sn ω' = 2 ∧ Ln ω' = 0} = 1 / 2 := by
        rw [hSp.measureReal_Sn_Ln_eq hGW hcrit 2 0, hZ1_2]
        norm_num
      have hle := measureReal_mono hsub (measure_ne_top P' _)
      linarith
    have hR0_pos : 0 < P'.real {ω' | R 1 ω' = 0} := by
      have hsub : {ω' : Ω' | Sn ω' = 2 ∧ Ln ω' = 1} ⊆ {ω' | R 1 ω' = 0} := by
        rintro ω' ⟨hS : Sn ω' = 2, hL : Ln ω' = 1⟩
        change R 1 ω' = 0
        rw [hSn_eq ω'] at hS
        rw [hLn_eq ω'] at hL
        omega
      have hpos : P'.real {ω' | Sn ω' = 2 ∧ Ln ω' = 1} = 1 / 2 := by
        rw [hSp.measureReal_Sn_Ln_eq hGW hcrit 2 1, hZ1_2]
        norm_num
      have hle := measureReal_mono hsub (measure_ne_top P' _)
      linarith
    have hprod : P'.real ({ω' | L 1 ω' = 0} ∩ {ω' | R 1 ω' = 0}) =
        P'.real {ω' | L 1 ω' = 0} * P'.real {ω' | R 1 ω' = 0} := by
      have h1 := hind.measure_inter_preimage_eq_mul {0} {0}
        (measurableSet_singleton 0) (measurableSet_singleton 0)
      have h2 := congrArg ENNReal.toReal h1
      rw [ENNReal.toReal_mul] at h2
      exact h2
    have hpos_prod : 0 < P'.real {ω' | L 1 ω' = 0} * P'.real {ω' | R 1 ω' = 0} :=
      mul_pos hL0_pos hR0_pos
    linarith

/-- `IsEquilibrium` depends on $(P, X)$ only through the pushforward law `P.map X`. -/
theorem isEquilibrium_congr_map {Ω₁ Ω₂ Ω' : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω']
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P' : Measure Ω'}
    {X₁ : Ω₁ → ℝ} {X₂ : Ω₂ → ℝ} {Xe : Ω' → ℝ}
    (hX₁ : AEMeasurable X₁ P₁) (hX₂ : AEMeasurable X₂ P₂)
    (hmap : P₁.map X₁ = P₂.map X₂) :
    IsEquilibrium P₁ X₁ P' Xe ↔ IsEquilibrium P₂ X₂ P' Xe :=
  ⟨fun h ↦ h.congr_identDistrib ⟨hX₁, hX₂, hmap⟩ ⟨h.2.2.1, h.2.2.1, rfl⟩,
   fun h ↦ h.congr_identDistrib ⟨hX₂, hX₁, hmap.symm⟩ ⟨h.2.2.1, h.2.2.1, rfl⟩⟩

/-- Conditioning a non-negative random variable $Z$ on $\{Z > 0\}$ preserves `IsEquilibrium`. -/
theorem isEquilibrium_cond_pos_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : Ω → ℝ) (Ze : Ω' → ℝ)
    (hZ_meas : AEMeasurable Z P)
    (hZ_nn : 0 ≤ᵐ[P] Z)
    (hZ_pos : P {ω | 0 < Z ω} ≠ 0) :
    IsEquilibrium P Z P' Ze ↔
      IsEquilibrium (ProbabilityTheory.cond P {ω | 0 < Z ω}) Z P' Ze := by
  let Z₀ : Ω → ℝ := hZ_meas.mk Z
  let S : Set Ω := {ω | 0 < Z ω}
  let S₀ : Set Ω := {ω | 0 < Z₀ ω}
  have hS₀_meas : MeasurableSet S₀ :=
    measurableSet_lt measurable_const hZ_meas.measurable_mk
  have hZZ₀ : Z =ᵐ[P] Z₀ := hZ_meas.ae_eq_mk
  have hSS₀ : S =ᵐ[P] S₀ := by
    filter_upwards [hZZ₀] with ω hω
    change (0 < Z ω) = (0 < Z₀ ω)
    rw [hω]
  have hPS₀ : P S = P S₀ := measure_congr hSS₀
  have hrest : P.restrict S = P.restrict S₀ := Measure.restrict_congr_set hSS₀
  have hcond_eq : ProbabilityTheory.cond P S = (P S₀)⁻¹ • P.restrict S₀ := by
    rw [ProbabilityTheory.cond, hPS₀, hrest]
  have hPS₀_ne_zero : P S₀ ≠ 0 := hPS₀ ▸ hZ_pos
  have hPS₀_ne_top : P S₀ ≠ ⊤ := measure_ne_top P S₀
  have hinv_ne_zero : (P S₀)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hPS₀_ne_top
  have hinv_ne_top : (P S₀)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hPS₀_ne_zero
  have hc_pos : 0 < (P S₀)⁻¹.toReal :=
    ENNReal.toReal_pos hinv_ne_zero hinv_ne_top
  have hc_ne : (P S₀)⁻¹.toReal ≠ 0 := hc_pos.ne'
  have hZ_ind : S₀.indicator Z =ᵐ[P] Z := by
    filter_upwards [hZ_nn, hZZ₀] with ω (hnn : 0 ≤ Z ω) hω
    by_cases h : ω ∈ S₀
    · exact indicator_of_mem h Z
    · rw [indicator_of_notMem h]
      have hle : Z ω ≤ 0 := by rw [hω]; exact not_lt.mp h
      linarith
  have hZ_int_iff : Integrable Z (ProbabilityTheory.cond P S) ↔ Integrable Z P := by
    rw [hcond_eq, integrable_smul_measure hinv_ne_zero hinv_ne_top]
    exact (integrable_indicator_iff hS₀_meas).symm.trans (integrable_congr hZ_ind)
  have hZ_int_eq :
      ∫ ω, Z ω ∂ProbabilityTheory.cond P S = (P S₀)⁻¹.toReal * ∫ ω, Z ω ∂P := by
    rw [hcond_eq, integral_smul_measure, smul_eq_mul, ← integral_indicator hS₀_meas,
      integral_congr_ae hZ_ind]
  have hf_int_eq : ∀ f : ℝ → ℝ,
      ∫ ω, (f (Z ω) - f 0) ∂ProbabilityTheory.cond P S =
        (P S₀)⁻¹.toReal * ∫ ω, (f (Z ω) - f 0) ∂P := by
    intro f
    have hf_ind : S₀.indicator (fun ω ↦ f (Z ω) - f 0) =ᵐ[P] fun ω ↦ f (Z ω) - f 0 := by
      filter_upwards [hZ_nn, hZZ₀] with ω (hnn : 0 ≤ Z ω) hω
      by_cases h : ω ∈ S₀
      · exact indicator_of_mem h _
      · rw [indicator_of_notMem h]
        have hle : Z ω ≤ 0 := by rw [hω]; exact not_lt.mp h
        have h0 : Z ω = 0 := le_antisymm hle hnn
        simp [h0]
    rw [hcond_eq, integral_smul_measure, smul_eq_mul, ← integral_indicator hS₀_meas,
      integral_congr_ae hf_ind]
  have hsub_P : ∀ {f : ℝ → ℝ} {K : ℝ≥0}, Integrable Z P → LipschitzWith K f →
      (∫ ω, f (Z ω) ∂P) - f 0 = ∫ ω, (f (Z ω) - f 0) ∂P := by
    intro f K hZi hL
    rw [integral_sub (integrable_comp_of_lipschitz hZi hL) (integrable_const (f 0)),
      integral_const, probReal_univ, one_smul]
  have hsub_cond : ∀ {f : ℝ → ℝ} {K : ℝ≥0},
      Integrable Z (ProbabilityTheory.cond P S) → LipschitzWith K f →
      (∫ ω, f (Z ω) ∂ProbabilityTheory.cond P S) - f 0 =
        ∫ ω, (f (Z ω) - f 0) ∂ProbabilityTheory.cond P S := by
    intro f K hZi hL
    have : IsProbabilityMeasure (ProbabilityTheory.cond P S) :=
      ProbabilityTheory.cond_isProbabilityMeasure hZ_pos
    rw [integral_sub (integrable_comp_of_lipschitz hZi hL) (integrable_const (f 0)),
      integral_const, probReal_univ, one_smul]
  have hZ_nn_cond : 0 ≤ᵐ[ProbabilityTheory.cond P S] Z :=
    ProbabilityTheory.cond_absolutelyContinuous hZ_nn
  constructor
  · rintro ⟨_, hZ_int, hZe_meas, hEq⟩
    refine ⟨hZ_nn_cond, hZ_int_iff.mpr hZ_int, hZe_meas, fun f ⟨K, hL⟩ ↦ ?_⟩
    rw [hsub_cond (hZ_int_iff.mpr hZ_int) hL, hf_int_eq f, ← hsub_P hZ_int hL,
      hZ_int_eq, hEq f ⟨K, hL⟩, mul_assoc]
  · rintro ⟨_, hZ_int_cond, hZe_meas, hEq⟩
    refine ⟨hZ_nn, hZ_int_iff.mp hZ_int_cond, hZe_meas, fun f ⟨K, hL⟩ ↦ ?_⟩
    have h1 := hEq f ⟨K, hL⟩
    rw [hsub_cond hZ_int_cond hL, hf_int_eq f, ← hsub_P (hZ_int_iff.mp hZ_int_cond) hL,
      hZ_int_eq, mul_assoc] at h1
    exact mul_left_cancel₀ hc_ne h1

/-- Section 5.3 Item (4) and `L3080-3081` distributional identity (`\label{i174}`,
`SteinIntro.tex:3065-3067, 3079-3082`): if $R_n$ is the number of individuals to the right
(inclusive) of $v_n$ and $U$ is uniform on $(0, 1)$ independent of all else, then
$R_n - U \stackrel{d}{=} U S_n$ and $Y_n^e := R_n - U$ has the equilibrium distribution of
$Y_n$. -/
def Sec5_3_item_4_stmt : Prop :=
  ∀ {Ω ΩY Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {Y : ΩY → ℕ} {X L R : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) →
    IsSizeBiasSpine P Z P' n X L R →
    MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P' →
    IndepFun U (fun ω' (j : Finset.Icc 1 n) ↦ (X j.1 ω', L j.1 ω', R j.1 ω')) P' →
    let Rn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
    P'.map (fun ω' ↦ Rn ω' - U ω') = P'.map (fun ω' ↦ U ω' * Sn ω') ∧
      IsEquilibrium PY (fun ω ↦ (Y ω : ℝ)) P' (fun ω' ↦ Rn ω' - U ω')

theorem sec5_3_item_4 : Sec5_3_item_4_stmt := by
  intro Ω ΩY Ω' _ _ _ P _ PY _ P' _ Z n Y X L R U hGW hcrit hY_meas hY_map hSp hU hIndep_U
  dsimp only
  let Rn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)
  let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
  let Rn_nat : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, R j ω'
  let Sn_nat : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
  have hZn_nn : 0 ≤ᵐ[P] fun ω ↦ (Z n ω : ℝ) :=
    Eventually.of_forall fun ω ↦ Nat.cast_nonneg (Z n ω)
  have hZn_int : Integrable (fun ω ↦ (Z n ω : ℝ)) P := hGW.integrable_Z n
  have hZn_mean : ∫ ω, (Z n ω : ℝ) ∂P = 1 := hGW.integral_Z_eq_one hcrit n
  have hZn_pos : 0 < ∫ ω, (Z n ω : ℝ) ∂P := by rw [hZn_mean]; exact zero_lt_one
  have hSB_Sn : IsSizeBias P (fun ω ↦ (Z n ω : ℝ)) P' Sn :=
    sec5_3_item_1 P P' hGW hcrit hSp
  let φS : (Finset.Icc 1 n → ℕ × ℕ × ℕ) → ℝ :=
    fun c ↦ 1 + ∑ j : Finset.Icc 1 n, (((c j).2.1 : ℝ) + ((c j).2.2 : ℝ))
  have hφS_meas : Measurable φS :=
    measurable_const.add (Finset.measurable_sum Finset.univ fun j _ ↦
      ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp
        (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply j)))).add
      ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp
        (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply j)))))
  have hSn_comp : (φS ∘ fun ω' (j : Finset.Icc 1 n) ↦ (X j.1 ω', L j.1 ω', R j.1 ω')) = Sn := by
    ext ω'
    dsimp only [φS, Sn, Function.comp_apply]
    congr 1
    exact Finset.sum_attach (Finset.Icc 1 n)
      (fun j ↦ (L j ω' : ℝ) + (R j ω' : ℝ))
  have hIndep_USn : IndepFun U Sn P' := by
    rw [← hSn_comp]
    exact hIndep_U.comp measurable_id hφS_meas
  have hEq_USn : IsEquilibrium P (fun ω ↦ (Z n ω : ℝ)) P' (fun ω' ↦ U ω' * Sn ω') :=
    prop5_5 P P' hZn_nn hZn_int hSB_Sn hU hIndep_USn
  let φR : (Finset.Icc 1 n → ℕ × ℕ × ℕ) → ℕ :=
    fun c ↦ 1 + ∑ j : Finset.Icc 1 n, (c j).2.2
  have hφR_meas : Measurable φR :=
    measurable_const.add (Finset.measurable_sum Finset.univ fun j _ ↦
      measurable_snd.comp (measurable_snd.comp (measurable_pi_apply j)))
  have hRn_comp :
      (φR ∘ fun ω' (j : Finset.Icc 1 n) ↦ (X j.1 ω', L j.1 ω', R j.1 ω')) = Rn_nat := by
    ext ω'
    dsimp only [φR, Rn_nat, Function.comp_apply]
    congr 1
    exact Finset.sum_attach (Finset.Icc 1 n) (fun j ↦ R j ω')
  have hIndep_UR : IndepFun U Rn_nat P' := by
    rw [← hRn_comp]
    exact hIndep_U.comp measurable_id hφR_meas
  have hRn_cast : (fun ω' ↦ (Rn_nat ω' : ℝ)) = Rn := by
    ext ω'
    simp [Rn_nat, Rn, Nat.cast_add, Nat.cast_sum]
  have hRn_nat_aem : AEMeasurable Rn_nat P' := hSp.aemeasurable_L_R.2.2.1
  have hRn_aem : AEMeasurable Rn P' := by
    rw [← hRn_cast]
    exact (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hRn_nat_aem
  have hEq_RnU : IsEquilibrium P (fun ω ↦ (Z n ω : ℝ)) P' (fun ω' ↦ Rn ω' - U ω') := by
    refine ⟨hZn_nn, hZn_int, hRn_aem.sub hU.aemeasurable, fun f ⟨K, hLip⟩ ↦ ?_⟩
    rw [hZn_mean, one_mul]
    have hU_map : P'.map U = volume.restrict (Ioo (0 : ℝ) 1) := by
      rw [hU.map_eq, ProbabilityTheory.cond, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one,
        inv_one, one_smul]
    have : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
      rw [← hU_map]
      exact (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).mpr ‹_›
    set νR : Measure ℕ := P'.map Rn_nat
    have : IsProbabilityMeasure νR :=
      (Measure.isProbabilityMeasure_map_iff hRn_nat_aem).mpr ‹_›
    have hprod_map : P'.map (fun ω' ↦ (U ω', Rn_nat ω')) =
        (volume.restrict (Ioo (0 : ℝ) 1)).prod νR := by
      rw [hIndep_UR.map_prod_eq_prod_map_map hU.aemeasurable hRn_nat_aem, hU_map]
    let φ : ℝ × ℕ → ℝ := fun p ↦ deriv f ((p.2 : ℝ) - p.1)
    have hφ_meas : Measurable φ :=
      (measurable_deriv f).comp
        (((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp measurable_snd).sub
          measurable_fst)
    have hdf_bdd : ∀ y : ℝ, |deriv f y| ≤ K := fun y ↦ by
      simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := y) hLip
    have hφ_int : Integrable φ ((volume.restrict (Ioo (0 : ℝ) 1)).prod νR) :=
      Integrable.of_bound hφ_meas.aestronglyMeasurable K
        (Eventually.of_forall fun p ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd ((p.2 : ℝ) - p.1))
    have hprod_aem : AEMeasurable (fun ω' ↦ (U ω', Rn_nat ω')) P' :=
      hU.aemeasurable.prodMk hRn_nat_aem
    have h_fub : ∫ ω', deriv f (Rn ω' - U ω') ∂P' =
        ∫ r : ℕ, (∫ u in Ioo (0 : ℝ) 1, deriv f ((r : ℝ) - u)) ∂νR := by
      have h1 : (fun ω' ↦ deriv f (Rn ω' - U ω')) = fun ω' ↦ φ (U ω', Rn_nat ω') := by
        ext ω'
        simp [φ, ← hRn_cast]
      rw [h1, ← integral_map hprod_aem hφ_meas.aestronglyMeasurable, hprod_map,
        integral_prod_symm φ hφ_int]
    have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b :=
      fun a b ↦ hLip.lipschitzOnWith.absolutelyContinuousOnInterval
    let g : ℕ → ℝ := fun r ↦ f (r : ℝ) - f ((r : ℝ) - 1)
    have h_ftc_r : ∀ r : ℕ, ∫ u in Ioo (0 : ℝ) 1, deriv f ((r : ℝ) - u) = g r := by
      intro r
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_comp_sub_left (deriv f) (r : ℝ), sub_zero,
        (hf_ac ((r : ℝ) - 1) (r : ℝ)).integral_deriv_eq_sub]
    simp_rw [h_ftc_r] at h_fub
    rw [integral_map hRn_nat_aem (Measurable.of_discrete : Measurable g).aestronglyMeasurable]
      at h_fub
    rw [h_fub]
    obtain ⟨_, _, L', R', _, _, _, hL'_meas, hR'_meas, _, _, _, _, _, _, hlvl'⟩ :=
      hSp.exists_measurable_modification
    let Sn' : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L' j ω' + R' j ω')
    let Rn' : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, R' j ω'
    have hSn'_meas : Measurable Sn' :=
      measurable_const.add (Finset.measurable_sum _ fun j _ ↦ (hL'_meas j).add (hR'_meas j))
    have hRn'_meas : Measurable Rn' :=
      measurable_const.add (Finset.measurable_sum _ fun j _ ↦ hR'_meas j)
    have hSn_ae : Sn' =ᵐ[P'] Sn_nat := by
      have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' ∧ R' j ω' = R j ω' :=
        ae_all_finset (Finset.Icc 1 n) fun j hj ↦
          (hlvl' j hj).2.1.and (hlvl' j hj).2.2.1
      filter_upwards [hall] with ω' hω'
      dsimp only [Sn', Sn_nat]
      congr 1
      exact Finset.sum_congr rfl fun j hj ↦ by rw [(hω' j hj).1, (hω' j hj).2]
    have hRn_ae : Rn' =ᵐ[P'] Rn_nat := by
      have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, R' j ω' = R j ω' :=
        ae_all_finset (Finset.Icc 1 n) fun j hj ↦ (hlvl' j hj).2.2.1
      filter_upwards [hall] with ω' hω'
      dsimp only [Rn', Rn_nat]
      congr 1
      exact Finset.sum_congr rfl fun j hj ↦ hω' j hj
    have hg_bdd : ∀ r : ℕ, |g r| ≤ K := by
      intro r
      have hd := hLip.dist_le_mul (r : ℝ) ((r : ℝ) - 1)
      rw [Real.dist_eq, Real.dist_eq] at hd
      simpa using hd
    have hgRn'_int : Integrable (fun ω' ↦ g (Rn' ω')) P' :=
      Integrable.of_bound
        ((Measurable.of_discrete : Measurable g).comp hRn'_meas).aestronglyMeasurable
        K (Eventually.of_forall fun ω' ↦ by rw [Real.norm_eq_abs]; exact hg_bdd (Rn' ω'))
    have hgRn_congr : ∫ ω', g (Rn_nat ω') ∂P' = ∫ ω', g (Rn' ω') ∂P' := by
      refine integral_congr_ae ?_
      filter_upwards [hRn_ae] with ω' hω'
      rw [hω']
    rw [hgRn_congr]
    let A' : ℕ → Set Ω' := fun k ↦ {ω' | Sn' ω' = k}
    have hA'_meas : ∀ k, MeasurableSet (A' k) := fun k ↦ hSn'_meas (measurableSet_singleton k)
    have hA'_disj : Pairwise (fun k₁ k₂ ↦ Disjoint (A' k₁) (A' k₂)) := by
      intro k₁ k₂ hk
      exact Set.disjoint_left.2 fun ω' (h1 : Sn' ω' = k₁) (h2 : Sn' ω' = k₂) ↦
        hk (h1.symm.trans h2)
    have hA'_union : (⋃ k : ℕ, A' k) = univ := by ext ω'; simp [A']
    have hint_P' : ∫ ω', g (Rn' ω') ∂P' = ∑' k : ℕ, ∫ ω' in A' k, g (Rn' ω') ∂P' := by
      rw [← setIntegral_univ, ← hA'_union,
        integral_iUnion hA'_meas hA'_disj hgRn'_int.integrableOn]
    have hfiber_P' : ∀ k : ℕ,
        ∫ ω' in A' k, g (Rn' ω') ∂P' = (f (k : ℝ) - f 0) * P.real {ω | Z n ω = k} := by
      intro k
      let B : Fin k → Set Ω' := fun m ↦ {ω' | Sn' ω' = k ∧ Rn' ω' = m.1 + 1}
      have hB_meas : ∀ m : Fin k, MeasurableSet (B m) := fun m ↦
        (hSn'_meas (measurableSet_singleton k)).inter
          (hRn'_meas (measurableSet_singleton (m.1 + 1)))
      have hB_disj : Pairwise (fun m₁ m₂ : Fin k ↦ Disjoint (B m₁) (B m₂)) := by
        intro m₁ m₂ hm
        refine Set.disjoint_left.2 fun ω' h1 h2 ↦ hm (Fin.ext ?_)
        have heq := h1.2.symm.trans h2.2
        omega
      have hind_sum : (A' k).indicator (fun ω' ↦ g (Rn' ω')) =
          fun ω' ↦ ∑ m : Fin k, (B m).indicator (fun ω'' ↦ g (Rn' ω'')) ω' := by
        ext ω'
        by_cases hk_eq : Sn' ω' = k
        · have hmemA : ω' ∈ A' k := hk_eq
          have h1 : 1 ≤ Rn' ω' := Nat.le_add_right 1 _
          have hle : Rn' ω' ≤ k := by
            rw [← hk_eq]
            dsimp only [Rn', Sn']
            exact Nat.add_le_add_left
              (Finset.sum_le_sum fun j _ ↦ Nat.le_add_left _ _) 1
          let m₀ : Fin k := ⟨Rn' ω' - 1, by omega⟩
          have hm₀ : ω' ∈ B m₀ := ⟨hk_eq, by dsimp [m₀]; omega⟩
          rw [indicator_of_mem hmemA, Finset.sum_eq_single m₀
            (fun m _ hm ↦ indicator_of_notMem (Set.disjoint_left.mp (hB_disj hm.symm) hm₀) _)
            (fun h ↦ False.elim (h (Finset.mem_univ m₀))), indicator_of_mem hm₀]
        · have hnotMemA : ω' ∉ A' k := hk_eq
          rw [indicator_of_notMem hnotMemA, Finset.sum_eq_zero fun m _ ↦
            indicator_of_notMem (fun h ↦ hk_eq h.1) _]
      rw [← integral_indicator (hA'_meas k), hind_sum,
        integral_finsetSum Finset.univ (fun m _ ↦ hgRn'_int.indicator (hB_meas m))]
      simp_rw [integral_indicator (hB_meas _)]
      have hB_term : ∀ m : Fin k,
          ∫ ω' in B m, g (Rn' ω') ∂P' =
            P.real {ω | Z n ω = k} * (f ((m.1 : ℝ) + 1) - f (m.1 : ℝ)) := by
        intro m
        have hcongr : ∀ ω' ∈ B m, g (Rn' ω') = f ((m.1 : ℝ) + 1) - f (m.1 : ℝ) := by
          intro ω' hω'
          rw [hω'.2]
          dsimp only [g]
          push_cast
          ring_nf
        rw [setIntegral_congr_fun (hB_meas m) hcongr, setIntegral_const, smul_eq_mul]
        congr 1
        have hBm_congr : P'.real (B m) =
            P'.real {ω' | Sn_nat ω' = k ∧ Rn_nat ω' = m.1 + 1} := by
          refine measureReal_congr ?_
          filter_upwards [hSn_ae, hRn_ae] with ω' hS hR
          simp [B, hS, hR]
        have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := m.2; omega)
        rw [hBm_congr, (sec5_3_item_3 P P' hGW hcrit hSp).2 k (m.1 + 1),
          ite_eq_left_iff.2 fun h ↦ by have := m.2; omega,
          hSp.measureReal_Sn_eq hGW hcrit k, mul_div_cancel_left₀ _ hk0]
      simp_rw [hB_term, ← Finset.mul_sum,
        Fin.sum_univ_eq_sum_range (fun r : ℕ ↦ f ((r : ℝ) + 1) - f (r : ℝ)) k]
      have htel : (∑ r ∈ Finset.range k, (f ((r : ℝ) + 1) - f (r : ℝ))) =
          f (k : ℝ) - f 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using
          Finset.sum_range_sub (fun r : ℕ ↦ f (r : ℝ)) k
      rw [htel, mul_comm]
    obtain ⟨ξ'', hξ''_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
    let Zn' : Ω → ℕ := gwCanonical ξ'' n
    have hZn'_meas : Measurable Zn' := measurable_gwCanonical hξ''_meas n
    have hfZ_int0 : Integrable (fun ω ↦ f (Z n ω)) P :=
      integrable_comp_of_lipschitz hZn_int hLip
    have hfZ_int : Integrable (fun ω ↦ f (Z n ω) - f 0) P :=
      hfZ_int0.sub (integrable_const (f 0))
    have hfZn'_int : Integrable (fun ω ↦ f (Zn' ω) - f 0) P := by
      refine hfZ_int.congr ?_
      filter_upwards [hZ_ae n] with ω hω
      simp [Zn', hω]
    have hfZ_sub : (∫ ω, f (Z n ω) ∂P) - f 0 = ∫ ω, (f (Z n ω) - f 0) ∂P := by
      rw [integral_sub hfZ_int0 (integrable_const (f 0)), integral_const, probReal_univ, one_smul]
    have hfZ_congr : ∫ ω, (f (Z n ω) - f 0) ∂P = ∫ ω, (f (Zn' ω) - f 0) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hZ_ae n] with ω hω
      simp [Zn', hω]
    let C : ℕ → Set Ω := fun k ↦ {ω | Zn' ω = k}
    have hC_meas : ∀ k, MeasurableSet (C k) := fun k ↦ hZn'_meas (measurableSet_singleton k)
    have hC_disj : Pairwise (fun k₁ k₂ ↦ Disjoint (C k₁) (C k₂)) := by
      intro k₁ k₂ hk
      exact Set.disjoint_left.2 fun ω (h1 : Zn' ω = k₁) (h2 : Zn' ω = k₂) ↦
        hk (h1.symm.trans h2)
    have hC_union : (⋃ k : ℕ, C k) = univ := by ext ω; simp [C]
    have hint_P : ∫ ω, (f (Zn' ω) - f 0) ∂P =
        ∑' k : ℕ, ∫ ω in C k, (f (Zn' ω) - f 0) ∂P := by
      rw [← setIntegral_univ, ← hC_union,
        integral_iUnion hC_meas hC_disj hfZn'_int.integrableOn]
    have hfiber_P : ∀ k : ℕ,
        ∫ ω in C k, (f (Zn' ω) - f 0) ∂P = (f (k : ℝ) - f 0) * P.real {ω | Z n ω = k} := by
      intro k
      have hcongr : ∀ ω ∈ C k, f (Zn' ω) - f 0 = f (k : ℝ) - f 0 :=
        fun ω (hω : Zn' ω = k) ↦ by rw [hω]
      rw [setIntegral_congr_fun (hC_meas k) hcongr, setIntegral_const, smul_eq_mul, mul_comm]
      congr 1
      refine measureReal_congr ?_
      filter_upwards [hZ_ae n] with ω hω
      simp [C, Zn', hω]
    rw [hfZ_sub, hfZ_congr, hint_P, hint_P']
    simp_rw [hfiber_P, hfiber_P']
  have hchar := (sec5_1_equilibrium_ac (Ω' := Ω') P hZn_nn hZn_int hZn_pos).1
  refine ⟨(hchar P' hEq_RnU).1.trans (hchar P' hEq_USn).1.symm, ?_⟩
  have hcast_meas : Measurable (Nat.cast : ℕ → ℝ) := Measurable.of_discrete
  have hY_real_meas : AEMeasurable (fun ω ↦ (Y ω : ℝ)) PY :=
    hcast_meas.comp_aemeasurable hY_meas
  have hZn_cond_meas : AEMeasurable (Z n) (ProbabilityTheory.cond P {ω | 0 < Z n ω}) :=
    (hGW.aemeasurable_Z n).mono_ac ProbabilityTheory.cond_absolutelyContinuous
  have hY_real_map : PY.map (fun ω ↦ (Y ω : ℝ)) =
      (ProbabilityTheory.cond P {ω | 0 < (Z n ω : ℝ)}).map (fun ω ↦ (Z n ω : ℝ)) := by
    have hset : {ω : Ω | 0 < (Z n ω : ℝ)} = {ω | 0 < Z n ω} := by ext; simp
    rw [hset]
    change PY.map ((Nat.cast : ℕ → ℝ) ∘ Y) =
      (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map ((Nat.cast : ℕ → ℝ) ∘ Z n)
    rw [← AEMeasurable.map_map_of_aemeasurable hcast_meas.aemeasurable hY_meas,
      ← AEMeasurable.map_map_of_aemeasurable hcast_meas.aemeasurable hZn_cond_meas, hY_map]
  have hpos : P {ω | 0 < (Z n ω : ℝ)} ≠ 0 :=
    measure_pos_ne_zero_of_pos_integral P hZn_nn hZn_pos
  have hZn_cond_real_meas :
      AEMeasurable (fun ω ↦ (Z n ω : ℝ)) (ProbabilityTheory.cond P {ω | 0 < (Z n ω : ℝ)}) :=
    hZn_int.aemeasurable.mono_ac ProbabilityTheory.cond_absolutelyContinuous
  exact (isEquilibrium_congr_map hZn_cond_real_meas hY_real_meas hY_real_map.symm).mp
    ((isEquilibrium_cond_pos_iff P P' (fun ω ↦ (Z n ω : ℝ)) (fun ω' ↦ Rn ω' - U ω')
      hZn_int.aemeasurable hZn_nn hpos).mp hEq_RnU)

/-- Section 5.3 spine realization of $Y_n$ (`SteinIntro.tex:3128-3139`): in a full size-bias spine
coupling at generation $n$, $R_n^* := 1 + \sum_{j=1}^n (R_{n,j} \mathbf{1}_{L_{n,j} = 0} +
R_{n,j}' \mathbf{1}_{L_{n,j} > 0})$ has the distribution of $Y_n \stackrel{d}{=}
(Z_n \mid Z_n > 0)$, while $Y_n^e := R_n - U$ has the equilibrium distribution of $R_n^*$. -/
def Sec5_3_spine_coupling_stmt : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpineCoupling P Z P' n X L R R' U →
    let Rstar : ℕ → Ω' → ℕ := fun j ω' ↦ if L j ω' = 0 then R j ω' else R' j ω'
    let Yn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, Rstar j ω'
    let Rn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)
    P'.map Yn = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) ∧
      IsEquilibrium P' (fun ω' ↦ (Yn ω' : ℝ)) P' (fun ω' ↦ Rn ω' - U ω')

theorem sec5_3_spine_coupling : Sec5_3_spine_coupling_stmt := by
  intro Ω Ω' _ _ P _ P' _ Z n X L R R' U hGW hcrit hCoup
  dsimp only
  let Rstar : ℕ → Ω' → ℕ := fun j ω' ↦ if L j ω' = 0 then R j ω' else R' j ω'
  let Yn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, Rstar j ω'
  let Rn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)
  let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
  let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
  rcases hCoup with ⟨hSp, hR'_law, hR'_indep, hind_R'_XLR, hU, hind_U_all⟩
  obtain ⟨X', A', L', R_sp', ξ', hX'_meas, hA'_meas, hL'_meas, hRsp'_meas, hξ'_meas,
    _, hL'_eq, hRsp'_eq, _, hind'_lvl, hlvl'⟩ := hSp.exists_measurable_modification
  let R'' : ℕ → Ω' → ℕ :=
    fun j ω' ↦ if hj : j ∈ Finset.Icc 1 n then (hR'_law j hj).1.mk (R' j) ω' else 0
  have hR''_meas : ∀ j, Measurable (R'' j) := by
    intro j
    by_cases hj : j ∈ Finset.Icc 1 n
    · change Measurable
        (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then (hR'_law j h).1.mk (R' j) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact (hR'_law j hj).1.measurable_mk
    · change Measurable
        (fun ω' ↦ if h : j ∈ Finset.Icc 1 n then (hR'_law j h).1.mk (R' j) ω' else 0)
      simp only [hj, ↓reduceDIte]
      exact measurable_const
  have hR''_ae : ∀ j ∈ Finset.Icc 1 n, R'' j =ᵐ[P'] R' j := by
    intro j hj
    filter_upwards [(hR'_law j hj).1.ae_eq_mk] with ω' hω'
    dsimp only [R'']
    simp only [hj, ↓reduceDIte, hω']
  let Rstar' : ℕ → Ω' → ℕ := fun j ω' ↦ if L' j ω' = 0 then R_sp' j ω' else R'' j ω'
  have hRstar'_meas : ∀ j, Measurable (Rstar' j) := fun j ↦
    Measurable.ite (hL'_meas j (measurableSet_singleton 0)) (hRsp'_meas j) (hR''_meas j)
  have hRstar'_ae : ∀ j ∈ Finset.Icc 1 n, Rstar' j =ᵐ[P'] Rstar j := by
    intro j hj
    filter_upwards [(hlvl' j hj).2.1, (hlvl' j hj).2.2.1, hR''_ae j hj] with ω' hL hR hR'
    dsimp only [Rstar', Rstar]
    rw [hL, hR, hR']
  let Yn' : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, Rstar' j ω'
  have hYn'_meas : Measurable Yn' :=
    measurable_const.add (Finset.measurable_sum _ fun j _ ↦ hRstar'_meas j)
  have hYn'_ae : Yn' =ᵐ[P'] Yn := by
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, Rstar' j ω' = Rstar j ω' :=
      ae_all_finset (Finset.Icc 1 n) hRstar'_ae
    filter_upwards [hall] with ω' hω'
    dsimp only [Yn', Yn]
    congr 1
    exact Finset.sum_congr rfl fun j hj ↦ hω' j hj
  have hYn_aem : AEMeasurable Yn P' := hYn'_meas.aemeasurable.congr hYn'_ae
  let Ln' : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L' j ω'
  have hLn'_meas : Measurable Ln' := Finset.measurable_sum _ fun j _ ↦ hL'_meas j
  have hLn'_ae : Ln' =ᵐ[P'] Ln := by
    have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' :=
      ae_all_finset (Finset.Icc 1 n) fun j hj ↦ (hlvl' j hj).2.1
    filter_upwards [hall] with ω' hω'
    exact Finset.sum_congr rfl fun j hj ↦ hω' j hj
  let I := Finset.Icc 1 n
  have hLR'_indep : iIndepFun (fun j : I ↦ fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) P' := by
    let φ : ∀ _ : I, ℕ × ℕ × (ℕ → ℕ) → ℕ × ℕ :=
      fun _ q ↦ (∑ r ∈ Finset.range q.2.1, q.2.2 r, ∑ r ∈ Finset.Ico q.2.1 q.1, q.2.2 r)
    have hφ_meas : ∀ j : I, Measurable (φ j) := fun _ ↦ by
      have h1 : Measurable (fun q : ℕ × ℕ × (ℕ → ℕ) ↦ ∑ r ∈ Finset.range q.2.1, q.2.2 r) :=
        measurable_sum_range (measurable_fst.comp measurable_snd)
          (fun r ↦ (measurable_pi_apply r).comp (measurable_snd.comp measurable_snd))
      have h2 : Measurable (fun q : ℕ × ℕ × (ℕ → ℕ) ↦ ∑ r ∈ Finset.Ico q.2.1 q.1, q.2.2 r) := by
        intro s hs
        have hpre : (fun q : ℕ × ℕ × (ℕ → ℕ) ↦ ∑ r ∈ Finset.Ico q.2.1 q.1, q.2.2 r) ⁻¹' s =
            ⋃ p : ℕ × ℕ,
              (fun q : ℕ × ℕ × (ℕ → ℕ) ↦ (q.2.1, q.1)) ⁻¹' {p} ∩
                (fun q : ℕ × ℕ × (ℕ → ℕ) ↦ ∑ r ∈ Finset.Ico p.1 p.2, q.2.2 r) ⁻¹' s := by
          ext q; simp
        rw [hpre]
        exact MeasurableSet.iUnion fun p ↦
          (((measurable_fst.comp measurable_snd).prodMk measurable_fst)
            (measurableSet_singleton p)).inter
            ((Finset.measurable_sum (Finset.Ico p.1 p.2) fun r _ ↦
              (measurable_pi_apply r).comp (measurable_snd.comp measurable_snd)) hs)
      exact h1.prodMk h2
    have hcomp_eq : (fun j : I ↦ fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) =
        fun j : I ↦ φ j ∘ fun ω' ↦ (X' j.1 ω', A' j.1 ω', fun r ↦ ξ' j.1 r ω') := by
      ext j ω'
      · exact hL'_eq j.1 ω'
      · exact hRsp'_eq j.1 ω'
    rw [hcomp_eq]
    exact hind'_lvl.comp φ hφ_meas
  have hR''_indep : iIndepFun (fun j : I ↦ R'' j.1) P' :=
    hR'_indep.congr fun j ↦ (hR''_ae j.1 j.2).symm
  have hind_R''_LR : IndepFun (fun ω' (j : I) ↦ R'' j.1 ω')
      (fun ω' (j : I) ↦ (L' j.1 ω', R_sp' j.1 ω')) P' := by
    let ψ : (I → ℕ × ℕ × ℕ) → (I → ℕ × ℕ) := fun c j ↦ (c j).2
    have hψ_meas : Measurable ψ :=
      measurable_pi_iff.2 fun j ↦ measurable_snd.comp (measurable_pi_apply j)
    have hind1 := hind_R'_XLR.comp measurable_id hψ_meas
    refine hind1.congr ?_ ?_
    · have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, R' j ω' = R'' j ω' :=
        ae_all_finset (Finset.Icc 1 n) fun j hj ↦ (hR''_ae j hj).symm
      filter_upwards [hall] with ω' hω'
      funext j
      exact hω' j.1 j.2
    · have hall : ∀ᵐ ω' ∂P', ∀ j ∈ Finset.Icc 1 n, L j ω' = L' j ω' ∧ R j ω' = R_sp' j ω' :=
        ae_all_finset (Finset.Icc 1 n) fun j hj ↦
          (hlvl' j hj).2.1.symm.and (hlvl' j hj).2.2.1.symm
      filter_upwards [hall] with ω' hω'
      funext j
      exact Prod.ext (hω' j.1 j.2).1 (hω' j.1 j.2).2
  have hLn_set_ae : ({ω' : Ω' | Ln ω' = 0} : Set Ω') =ᵐ[P'] {ω' | Ln' ω' = 0} := by
    filter_upwards [hLn'_ae] with ω' hω'
    simp [hω']
  have : IsProbabilityMeasure (ProbabilityTheory.cond P {ω | 0 < Z n ω}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (hGW.measure_Z_pos_ne_zero hcrit n)
  have hLn'_pos : P' {ω' | Ln' ω' = 0} ≠ 0 := by
    rw [← measure_congr hLn_set_ae,
      (sec5_3_eq_1712 P (ProbabilityTheory.cond P {ω | 0 < Z n ω}) P'
        hGW hcrit ((hGW.aemeasurable_Z n).mono_ac ProbabilityTheory.cond_absolutelyContinuous)
        rfl hSp).1]
    exact hGW.measure_Z_pos_ne_zero hcrit n
  have hLj_pos : ∀ j : I, P' {ω' | L j.1 ω' = 0} ≠ 0 := by
    intro j
    have hsub : {ω' : Ω' | Ln ω' = 0} ⊆ {ω' | L j.1 ω' = 0} := by
      intro ω' (hω' : (∑ i ∈ Finset.Icc 1 n, L i ω') = 0)
      exact Finset.sum_eq_zero_iff.mp hω' j.1 j.2
    have hLn_pos : P' {ω' | Ln ω' = 0} ≠ 0 := by
      rwa [measure_congr hLn_set_ae]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hLn_pos) (measure_mono hsub))
  have : IsProbabilityMeasure (ProbabilityTheory.cond P' {ω' | Ln' ω' = 0}) :=
    ProbabilityTheory.cond_isProbabilityMeasure hLn'_pos
  have : IsProbabilityMeasure (ProbabilityTheory.cond P' {ω' | Ln ω' = 0}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rwa [measure_congr hLn_set_ae])
  have htuple_map : P'.map (fun (ω' : Ω') (j : I) ↦ Rstar' j.1 ω') =
      (ProbabilityTheory.cond P' {ω' | Ln' ω' = 0}).map
        (fun (ω' : Ω') (j : I) ↦ R_sp' j.1 ω') := by
    refine map_eq_of_measureReal_eq
      (measurable_pi_iff.2 fun (j : I) ↦ hRstar'_meas j.1).aemeasurable
      (measurable_pi_iff.2 fun (j : I) ↦ hRsp'_meas j.1).aemeasurable fun c ↦ ?_
    let q : I → ℝ :=
      fun j ↦ (ProbabilityTheory.cond P' {ω' | L j.1 ω' = 0}).real {ω' | R j.1 ω' = c j}
    have hcond_prod :
        (ProbabilityTheory.cond P' {ω' | Ln' ω' = 0}).real
          {ω' | (fun j : I ↦ R_sp' j.1 ω') = c} = ∏ j : I, q j := by
      rw [cond_real_apply P' {ω' | Ln' ω' = 0} _ (hLn'_meas (measurableSet_singleton 0))]
      have hLn'_inter : {ω' : Ω' | Ln' ω' = 0} =
          ⋂ j ∈ (Finset.univ : Finset I), (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹'
            ({0} ×ˢ univ) := by
        ext ω'
        simp [Ln', I, Finset.sum_eq_zero_iff]
      have hLn'_both : ({ω' : Ω' | Ln' ω' = 0} ∩ {ω' | (fun j : I ↦ R_sp' j.1 ω') = c}) =
          ⋂ j ∈ (Finset.univ : Finset I), (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹'
            {(0, c j)} := by
        ext ω'
        simp [Ln', I, Finset.sum_eq_zero_iff, funext_iff, forall_and]
      have hprod_den : P'.real {ω' | Ln' ω' = 0} =
          ∏ j : I, P'.real {ω' | L' j.1 ω' = 0} := by
        rw [hLn'_inter, Measure.real,
          hLR'_indep.measure_inter_preimage_eq_mul Finset.univ
            (fun _ _ ↦ MeasurableSet.of_discrete),
          ENNReal.toReal_prod]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Measure.real]
        congr 2
        ext ω'
        simp
      have hprod_num : P'.real ({ω' | Ln' ω' = 0} ∩ {ω' | (fun j : I ↦ R_sp' j.1 ω') = c}) =
          ∏ j : I, P'.real ({ω' | L' j.1 ω' = 0} ∩ {ω' | R_sp' j.1 ω' = c j}) := by
        rw [hLn'_both, Measure.real,
          hLR'_indep.measure_inter_preimage_eq_mul Finset.univ
            (fun _ _ ↦ MeasurableSet.of_discrete),
          ENNReal.toReal_prod]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [Measure.real]
        congr 2
        ext ω'
        simp [Prod.mk.injEq]
      rw [hprod_den, hprod_num, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hLj_congr : P'.real {ω' | L' j.1 ω' = 0} = P'.real {ω' | L j.1 ω' = 0} := by
        refine measureReal_congr ?_
        filter_upwards [(hlvl' j.1 j.2).2.1] with ω' hL
        simp [hL]
      have hcond_j : ProbabilityTheory.cond P' {ω' | L j.1 ω' = 0} =
          ProbabilityTheory.cond P' {ω' | L' j.1 ω' = 0} := by
        have hset_ae : ({ω' : Ω' | L j.1 ω' = 0} : Set Ω') =ᵐ[P'] {ω' | L' j.1 ω' = 0} := by
          filter_upwards [(hlvl' j.1 j.2).2.1] with ω' hL
          simp [hL]
        rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
          measure_congr hset_ae, Measure.restrict_congr_set hset_ae]
      dsimp only [q]
      rw [hcond_j,
        cond_real_apply P' {ω' | L' j.1 ω' = 0} _ (hL'_meas j.1 (measurableSet_singleton 0)),
        hLj_congr]
      congr 1
      refine measureReal_congr ?_
      filter_upwards [(hlvl' j.1 j.2).2.2.1] with ω' hR
      simp [hR]
    rw [hcond_prod]
    let A₀ : I → Set Ω' := fun j ↦ {ω' | L' j.1 ω' = 0 ∧ R_sp' j.1 ω' = c j}
    let A₁ : I → Set Ω' := fun j ↦ {ω' | L' j.1 ω' ≠ 0 ∧ R'' j.1 ω' = c j}
    let B : Finset I → Set Ω' :=
      fun S ↦ (⋂ j ∈ S, A₀ j) ∩ (⋂ j ∈ Sᶜ, A₁ j)
    have hB_meas : ∀ S : Finset I, MeasurableSet (B S) := fun S ↦
      (MeasurableSet.biInter S.countable_toSet fun j _ ↦
        (hL'_meas j.1 (measurableSet_singleton 0)).inter
          (hRsp'_meas j.1 (measurableSet_singleton (c j)))).inter
      (MeasurableSet.biInter Sᶜ.countable_toSet fun j _ ↦
        (hL'_meas j.1 (measurableSet_singleton 0)).compl.inter
          (hR''_meas j.1 (measurableSet_singleton (c j))))
    have hB_disj : Pairwise (fun S₁ S₂ : Finset I ↦ Disjoint (B S₁) (B S₂)) := by
      intro S₁ S₂ hne
      refine Set.disjoint_left.2 fun ω' h1 h2 ↦ hne ?_
      ext j
      constructor
      · intro hj₁
        by_contra hj₂
        have h0 : L' j.1 ω' = 0 := (mem_iInter₂.mp h1.1 j hj₁).1
        have hne0 : L' j.1 ω' ≠ 0 := (mem_iInter₂.mp h2.2 j (Finset.mem_compl.mpr hj₂)).1
        exact hne0 h0
      · intro hj₂
        by_contra hj₁
        have h0 : L' j.1 ω' = 0 := (mem_iInter₂.mp h2.1 j hj₂).1
        have hne0 : L' j.1 ω' ≠ 0 := (mem_iInter₂.mp h1.2 j (Finset.mem_compl.mpr hj₁)).1
        exact hne0 h0
    have hB_union : (⋃ S : Finset I, B S) = {ω' | (fun j : I ↦ Rstar' j.1 ω') = c} := by
      ext ω'
      simp only [B, A₀, A₁, Rstar', mem_iUnion, mem_inter_iff, mem_iInter, Finset.mem_compl,
        mem_ofPred_eq, funext_iff]
      constructor
      · rintro ⟨S, hS₀, hS₁⟩ j
        by_cases hj : j ∈ S
        · simp only [ (hS₀ j hj).1, ↓reduceIte]
          exact (hS₀ j hj).2
        · simp only [(hS₁ j hj).1, ↓reduceIte]
          exact (hS₁ j hj).2
      · intro hc
        refine ⟨Finset.univ.filter (fun j : I ↦ L' j.1 ω' = 0),
          fun j hj ↦ ?_, fun j hj ↦ ?_⟩
        · have h0 : L' j.1 ω' = 0 := (Finset.mem_filter.mp hj).2
          have hcj := hc j
          simp only [h0, ↓reduceIte] at hcj
          exact ⟨h0, hcj⟩
        · have hne0 : L' j.1 ω' ≠ 0 := fun h0 ↦
            hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h0⟩)
          have hcj := hc j
          simp only [hne0, ↓reduceIte] at hcj
          exact ⟨hne0, hcj⟩
    rw [← hB_union, measureReal_biUnion_fintype P' hB_disj hB_meas]
    have hB_val : ∀ S : Finset I,
        P'.real (B S) =
          (∏ j ∈ S, P'.real (A₀ j)) *
            (∏ j ∈ (Finset.univ : Finset I) \ S, P'.real (A₁ j)) := by
      intro S
      have hBS_split : B S =
          (fun ω' (j : I) ↦ R'' j.1 ω') ⁻¹'
            {r : I → ℕ | ∀ j ∈ Sᶜ, r j = c j} ∩
          (fun ω' (j : I) ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹'
            {p : I → ℕ × ℕ | (∀ j ∈ S, (p j).1 = 0 ∧ (p j).2 = c j) ∧
              ∀ j ∈ Sᶜ, (p j).1 ≠ 0} := by
        ext ω'
        simp only [B, A₀, A₁, mem_inter_iff, mem_iInter, mem_ofPred_eq, mem_preimage]
        constructor
        · rintro ⟨h0, h1⟩
          exact ⟨fun j hj ↦ (h1 j hj).2, ⟨h0, fun j hj ↦ (h1 j hj).1⟩⟩
        · rintro ⟨hr, hp0, hp1⟩
          exact ⟨hp0, fun j hj ↦ ⟨hp1 j hj, hr j hj⟩⟩
      have hBS_prod1 : P'.real (B S) =
          P'.real (⋂ j ∈ Sᶜ, (fun ω' ↦ R'' j.1 ω') ⁻¹' {c j}) *
            P'.real ((⋂ j ∈ S, (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹' {(0, c j)}) ∩
              (⋂ j ∈ Sᶜ, (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹' ({0}ᶜ ×ˢ univ))) := by
        rw [hBS_split, Measure.real,
          hind_R''_LR.measure_inter_preimage_eq_mul _ _
            (MeasurableSet.of_discrete) (MeasurableSet.of_discrete),
          ENNReal.toReal_mul]
        congr 1
        · rw [Measure.real]; congr 2; ext ω'; simp
        · rw [Measure.real]; congr 2; ext ω'; simp [Prod.mk.injEq]
      have hR''_prod : P'.real (⋂ j ∈ Sᶜ, (fun ω' ↦ R'' j.1 ω') ⁻¹' {c j}) =
          ∏ j ∈ Sᶜ, P'.real {ω' | R'' j.1 ω' = c j} := by
        rw [Measure.real,
          hR''_indep.measure_inter_preimage_eq_mul Sᶜ (fun _ _ ↦ MeasurableSet.of_discrete),
          ENNReal.toReal_prod]
        rfl
      let setLR : I → Set (ℕ × ℕ) :=
        fun j ↦ if j ∈ S then {(0, c j)} else {0}ᶜ ×ˢ univ
      have hLR_union :
          ((⋂ j ∈ S, (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹' {(0, c j)}) ∩
            (⋂ j ∈ Sᶜ, (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹' ({0}ᶜ ×ˢ univ))) =
          ⋂ j ∈ (Finset.univ : Finset I),
            (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹' setLR j := by
        ext ω'
        simp only [setLR, mem_inter_iff, mem_iInter, Finset.mem_univ, true_implies,
          Finset.mem_compl]
        constructor
        · rintro ⟨hS, hSc⟩ j
          by_cases hj : j ∈ S <;> simp [hj, hS j, hSc j]
        · intro hall
          refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
          · have h := hall j; simpa [hj] using h
          · have h := hall j; simpa [hj] using h
      have hLR_prod :
          P'.real ((⋂ j ∈ S, (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹' {(0, c j)}) ∩
            (⋂ j ∈ Sᶜ, (fun ω' ↦ (L' j.1 ω', R_sp' j.1 ω')) ⁻¹' ({0}ᶜ ×ˢ univ))) =
          (∏ j ∈ S, P'.real (A₀ j)) * (∏ j ∈ Sᶜ, P'.real {ω' | L' j.1 ω' ≠ 0}) := by
        rw [hLR_union, Measure.real,
          hLR'_indep.measure_inter_preimage_eq_mul Finset.univ
            (fun _ _ ↦ MeasurableSet.of_discrete),
          ENNReal.toReal_prod,
          ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
        have hfilt1 : (Finset.univ : Finset I).filter (· ∈ S) = S := by ext j; simp
        have hfilt2 : (Finset.univ : Finset I).filter (fun j ↦ ¬ j ∈ S) = Sᶜ := by ext j; simp
        rw [hfilt1, hfilt2]
        congr 1
        · refine Finset.prod_congr rfl fun j hj ↦ ?_
          dsimp only [setLR]
          simp only [hj, ↓reduceIte]
          rw [Measure.real]
          congr 2
          ext ω'
          simp [A₀]
        · refine Finset.prod_congr rfl fun j hj ↦ ?_
          dsimp only [setLR]
          simp only [Finset.mem_compl.mp hj, ↓reduceIte]
          rw [Measure.real]
          congr 2
          ext ω'
          simp
      have hA₁_eq : ∀ j : I, P'.real (A₁ j) =
          P'.real {ω' | L' j.1 ω' ≠ 0} * P'.real {ω' | R'' j.1 ω' = c j} := by
        intro j
        have hind_j : IndepFun (R'' j.1) (L' j.1) P' := by
          have h := hind_R''_LR.comp (measurable_pi_apply j)
            (measurable_fst.comp (measurable_pi_apply j))
          exact h
        have hset_j : A₁ j = L' j.1 ⁻¹' ({0}ᶜ) ∩ R'' j.1 ⁻¹' {c j} := rfl
        rw [hset_j, Measure.real,
          hind_j.symm.measure_inter_preimage_eq_mul ({0}ᶜ) {c j}
            (MeasurableSet.of_discrete) (MeasurableSet.of_discrete),
          ENNReal.toReal_mul]
        rfl
      have hsdiff : (Finset.univ : Finset I) \ S = Sᶜ := by ext j; simp
      rw [hsdiff, hBS_prod1, hR''_prod, hLR_prod]
      simp_rw [hA₁_eq, Finset.prod_mul_distrib]
      ring
    simp_rw [hB_val]
    have hpow : (∑ S : Finset I,
        (∏ j ∈ S, P'.real (A₀ j)) *
           (∏ j ∈ (Finset.univ : Finset I) \ S, P'.real (A₁ j))) =
        ∑ S ∈ (Finset.univ : Finset I).powerset,
          (∏ j ∈ S, P'.real (A₀ j)) *
            (∏ j ∈ (Finset.univ : Finset I) \ S, P'.real (A₁ j)) := by
      refine Finset.sum_congr ?_ fun _ _ ↦ rfl
      ext S
      simp only [Finset.mem_univ, Finset.mem_powerset, Finset.subset_univ]
    rw [hpow, ← Finset.prod_add]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    have hA₁_eq : P'.real (A₁ j) =
        P'.real {ω' | L' j.1 ω' ≠ 0} * P'.real {ω' | R'' j.1 ω' = c j} := by
      have hind_j : IndepFun (R'' j.1) (L' j.1) P' :=
        hind_R''_LR.comp (measurable_pi_apply j)
          (measurable_fst.comp (measurable_pi_apply j))
      have hset_j : A₁ j = L' j.1 ⁻¹' ({0}ᶜ) ∩ R'' j.1 ⁻¹' {c j} := rfl
      rw [hset_j, Measure.real,
        hind_j.symm.measure_inter_preimage_eq_mul ({0}ᶜ) {c j}
          (MeasurableSet.of_discrete) (MeasurableSet.of_discrete),
        ENNReal.toReal_mul]
      rfl
    have hR''_cj : P'.real {ω' | R'' j.1 ω' = c j} = q j := by
      have h1 := map_measureReal_apply (hR''_meas j.1) (measurableSet_singleton (c j)) (μ := P')
      have hmap_j : P'.map (R'' j.1) =
          (ProbabilityTheory.cond P' {ω' | L j.1 ω' = 0}).map (R j.1) := by
        rw [Measure.map_congr (hR''_ae j.1 j.2), (hR'_law j.1 j.2).2]
      have : IsProbabilityMeasure (ProbabilityTheory.cond P' {ω' | L j.1 ω' = 0}) :=
        ProbabilityTheory.cond_isProbabilityMeasure (hLj_pos j)
      have hR_cond_aem : AEMeasurable (R j.1) (ProbabilityTheory.cond P' {ω' | L j.1 ω' = 0}) :=
        (hSp.aemeasurable_L_R.1 j.1 j.2).2.mono_ac ProbabilityTheory.cond_absolutelyContinuous
      rw [hmap_j, map_measureReal_apply_of_aemeasurable hR_cond_aem
        (measurableSet_singleton (c j))] at h1
      exact h1.symm
    have hA₀_eq : P'.real (A₀ j) = P'.real {ω' | L' j.1 ω' = 0} * q j := by
      have hset_ae : ({ω' : Ω' | L j.1 ω' = 0} : Set Ω') =ᵐ[P'] {ω' | L' j.1 ω' = 0} := by
        filter_upwards [(hlvl' j.1 j.2).2.1] with ω' hL
        simp [hL]
      have hcond_j : ProbabilityTheory.cond P' {ω' | L j.1 ω' = 0} =
          ProbabilityTheory.cond P' {ω' | L' j.1 ω' = 0} := by
        rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
          measure_congr hset_ae, Measure.restrict_congr_set hset_ae]
      have hLR_congr : P'.real (A₀ j) =
          P'.real ({ω' | L' j.1 ω' = 0} ∩ {ω' | R j.1 ω' = c j}) := by
        refine measureReal_congr ?_
        filter_upwards [(hlvl' j.1 j.2).2.2.1] with ω' hR
        simp [A₀, hR]
      have hqj : q j =
          (P'.real {ω' | L' j.1 ω' = 0})⁻¹ * P'.real (A₀ j) := by
        dsimp only [q]
        rw [hcond_j,
          cond_real_apply P' {ω' | L' j.1 ω' = 0} _ (hL'_meas j.1 (measurableSet_singleton 0)),
          hLR_congr]
      have hpos_j : P'.real {ω' | L' j.1 ω' = 0} ≠ 0 := by
        rw [← measureReal_congr hset_ae]
        exact (ENNReal.toReal_pos (hLj_pos j) (measure_ne_top P' _)).ne'
      rw [hqj, mul_inv_cancel_left₀ hpos_j]
    have hcompl_j : P'.real {ω' | L' j.1 ω' ≠ 0} = 1 - P'.real {ω' | L' j.1 ω' = 0} :=
      probReal_compl_eq_one_sub (μ := P') (s := {ω' | L' j.1 ω' = 0})
        (hL'_meas j.1 (measurableSet_singleton 0))
    rw [hA₀_eq, hA₁_eq, hR''_cj, hcompl_j]
    ring
  let φ_sum : (I → ℕ) → ℕ := fun c ↦ 1 + ∑ j : I, c j
  have hφ_sum_meas : Measurable φ_sum :=
    measurable_const.add (Finset.measurable_sum Finset.univ fun j _ ↦ measurable_pi_apply j)
  have hmap_sum := congrArg (fun μ : Measure (I → ℕ) ↦ μ.map φ_sum) htuple_map
  rw [Measure.map_map hφ_sum_meas (measurable_pi_iff.2 fun (j : I) ↦ hRstar'_meas j.1),
    Measure.map_map hφ_sum_meas (measurable_pi_iff.2 fun (j : I) ↦ hRsp'_meas j.1)] at hmap_sum
  have hYn'_comp : φ_sum ∘ (fun (ω' : Ω') (j : I) ↦ Rstar' j.1 ω') = Yn' := by
    ext ω'
    dsimp only [φ_sum, Yn', Function.comp_apply, I]
    congr 1
    exact Finset.sum_attach (Finset.Icc 1 n) (fun j ↦ Rstar' j ω')
  have hSn_cond_ae : (φ_sum ∘ fun (ω' : Ω') (j : I) ↦ R_sp' j.1 ω') =ᵐ[
      ProbabilityTheory.cond P' {ω' | Ln' ω' = 0}] Sn := by
    have hLn'_zero_ae : ∀ᵐ ω' ∂ProbabilityTheory.cond P' {ω' | Ln' ω' = 0}, Ln' ω' = 0 := by
      rw [ae_iff, ProbabilityTheory.cond_apply (s := {ω' | Ln' ω' = 0})
        (hLn'_meas (measurableSet_singleton 0))]
      have hempty : {ω' : Ω' | Ln' ω' = 0} ∩ {ω' | ¬ Ln' ω' = 0} = ∅ := by ext; simp
      rw [hempty, measure_empty, mul_zero]
    have hall : ∀ᵐ ω' ∂ProbabilityTheory.cond P' {ω' | Ln' ω' = 0},
        ∀ j ∈ Finset.Icc 1 n, L' j ω' = L j ω' ∧ R_sp' j ω' = R j ω' :=
      ProbabilityTheory.cond_absolutelyContinuous
        (ae_all_finset (Finset.Icc 1 n) fun j hj ↦
          (hlvl' j hj).2.1.and (hlvl' j hj).2.2.1)
    filter_upwards [hLn'_zero_ae, hall] with ω' hL0 hLR
    dsimp only [φ_sum, Sn, Function.comp_apply, I]
    congr 1
    refine (Finset.sum_attach (Finset.Icc 1 n) (fun j ↦ R_sp' j ω')).trans ?_
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hLj0 : L' j ω' = 0 := Finset.sum_eq_zero_iff.mp hL0 j hj
    rw [← (hLR j hj).1, ← (hLR j hj).2, hLj0, zero_add]
  have hcond_Ln : ProbabilityTheory.cond P' {ω' | Ln' ω' = 0} =
      ProbabilityTheory.cond P' {ω' | Ln ω' = 0} := by
    rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
      measure_congr hLn_set_ae, Measure.restrict_congr_set hLn_set_ae]
  rw [hYn'_comp, Measure.map_congr hYn'_ae, Measure.map_congr hSn_cond_ae, hcond_Ln] at hmap_sum
  have h1712 := (sec5_3_eq_1712 P (ProbabilityTheory.cond P {ω | 0 < Z n ω}) P'
    hGW hcrit ((hGW.aemeasurable_Z n).mono_ac ProbabilityTheory.cond_absolutelyContinuous)
    rfl hSp).2
  have hYn_law : P'.map Yn = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) :=
    hmap_sum.trans h1712
  refine ⟨hYn_law, ?_⟩
  have hind_U_XLR : IndepFun U (fun ω' (j : Finset.Icc 1 n) ↦ (X j.1 ω', L j.1 ω', R j.1 ω')) P' :=
    hind_U_all.comp measurable_id measurable_fst
  exact (sec5_3_item_4 P P' P' hGW hcrit hYn_aem hYn_law hSp hU hind_U_XLR).2

end SteinMethod
