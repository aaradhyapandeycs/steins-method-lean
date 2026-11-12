/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Negative.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic

/-!
# Hypergeometric & Remark 4.14 (`Formalization.PoissonSizeBias.Negative.Hypergeometric`)

Formalization of Example 4.13 (`[Hypergeometric distribution]`, `SteinIntro.tex:2480-2505`) and
Remark 4.14 (`SteinIntro.tex:2506-2510`, citing Harper 1967 / Pitman 1997 `[pit97]`):
- `SteinMethod.ex4_13_sizeBias`: exchangeability of the red-ball indicators, conditional law under
  the uniform replacement coupling, everywhere monotonicity, and size-bias conclusion.
- `SteinMethod.ex4_13_moments_corrected`: exact mean $nm / N$ and corrected variance
  $\frac{nm(N - n)(N - m)}{N^2(N - 1)}$ for $2 \le N$ (`ISSUE-TYPO-4.13`).
- `SteinMethod.not_ex4_13_var_printed`: refutation of the printed $(n - m)$ variance factor at
  $N = 4, n = 1, m = 2$.
- `SteinMethod.ex4_13_restricted`: Poisson total-variation bound for $2 \le N$.
- `SteinMethod.rem4_14`: complete proof from scratch via Rolle's theorem and Leibniz's rule that
  $W$ has the distribution of a sum of $n$ independent Bernoulli indicators, together with recovery
  of the Example 4.13 bound via Theorem 4.19 applied to those independent indicators (`G4-2`).
-/

open MeasureTheory ProbabilityTheory Set Polynomial
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Section 1: Red-Ball Indicators and Moments on `hypergeomVecMeasure` -/

private theorem redCountSet_eq_sum {N n : ℕ} (hnN : n ≤ N) (A : Finset (Fin N)) :
    (A.filter fun j : Fin N ↦ j.1 < n).card =
      ∑ i : Fin n, if Fin.castLE hnN i ∈ A then 1 else 0 := by
  let emb : Fin n ↪ Fin N := ⟨Fin.castLE hnN, Fin.castLE_injective hnN⟩
  have hmap :
      A.filter (fun j : Fin N ↦ j.1 < n) =
        (Finset.univ.filter fun i : Fin n ↦ Fin.castLE hnN i ∈ A).map emb := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, emb,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hjA, hjn⟩
      exact ⟨⟨j.1, hjn⟩, by simpa using hjA, Fin.ext rfl⟩
    · rintro ⟨i, hiA, rfl⟩
      exact ⟨hiA, i.2⟩
  rw [hmap, Finset.card_map, Finset.card_filter]

private def boolIndNat {N : ℕ} (j : Fin N) (v : Fin N → Bool) : ℕ :=
  if v j = true then 1 else 0

private theorem boolIndNat_zero_one {N : ℕ} (j : Fin N) (v : Fin N → Bool) :
    boolIndNat j v = 0 ∨ boolIndNat j v = 1 := by
  by_cases h : v j = true <;> simp [boolIndNat, h]

private theorem sum_boolIndNat_eq_card {N : ℕ} (v : Fin N → Bool) :
    (∑ j : Fin N, boolIndNat j v) = (boolSupport v).card := by
  unfold boolIndNat boolSupport
  rw [Finset.card_filter]

private theorem ae_mem_hypergeomVecSet {N m : ℕ} (hmN : m ≤ N) :
    ∀ᵐ v ∂hypergeomVecMeasure hmN, v ∈ hypergeomVecSet N m := by
  have hunion : {v : Fin N → Bool | ¬ v ∈ hypergeomVecSet N m} =
      ⋃ v ∈ (Finset.univ.filter fun w ↦ w ∉ hypergeomVecSet N m), {v} := by
    ext v
    simp
  rw [ae_iff, hunion,
    measure_biUnion_finset (fun v _ w _ hvw ↦ Set.disjoint_singleton.mpr hvw)
      (fun _ _ ↦ .of_discrete)]
  refine Finset.sum_eq_zero fun v hv ↦ ?_
  have hv' : v ∉ hypergeomVecSet N m := (Finset.mem_filter.mp hv).2
  rw [hypergeomVecMeasure_singleton, ite_eq_right hv']

private theorem integral_boolIndNat {N m : ℕ} (hmN : m ≤ N) (j : Fin N) :
    ∫ v, (boolIndNat j v : ℝ) ∂hypergeomVecMeasure hmN = (m : ℝ) / (N : ℝ) := by
  let μ := hypergeomVecMeasure hmN
  have hint : ∀ k : Fin N, Integrable (fun v ↦ (boolIndNat k v : ℝ)) μ := fun k ↦
    integrable_nat_zero_one μ .of_discrete (Filter.Eventually.of_forall (boolIndNat_zero_one k))
  have hconst : ∀ k : Fin N,
      ∫ v, (boolIndNat k v : ℝ) ∂μ = ∫ v, (boolIndNat j v : ℝ) ∂μ := by
    intro k
    let σ : Equiv.Perm (Fin N) := Equiv.swap k j
    let g : (Fin N → Bool) → (Fin N → Bool) := fun v x ↦ v (σ x)
    have hmap : μ.map g = μ := hypergeomVecMeasure_perm_invariant hmN σ
    calc
      ∫ v, (boolIndNat k v : ℝ) ∂μ
          = ∫ v, (boolIndNat k v : ℝ) ∂(μ.map g) := by rw [hmap]
      _ = ∫ v, (boolIndNat k (g v) : ℝ) ∂μ :=
          integral_map Measurable.of_discrete.aemeasurable
            Measurable.of_discrete.aestronglyMeasurable
      _ = ∫ v, (boolIndNat j v : ℝ) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
          simp [boolIndNat, g, σ]
  have hsum_eq :
      (∑ k : Fin N, ∫ v, (boolIndNat k v : ℝ) ∂μ) = (m : ℝ) := by
    rw [← integral_finsetSum Finset.univ fun k _ ↦ hint k]
    have hae : ∀ᵐ v ∂μ, (∑ k : Fin N, (boolIndNat k v : ℝ)) = (m : ℝ) := by
      filter_upwards [ae_mem_hypergeomVecSet hmN] with v hv
      have hcard : (boolSupport v).card = m := mem_hypergeomVecSet.mp hv
      exact_mod_cast (sum_boolIndNat_eq_card v).trans hcard
    rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]
  have hsum_const :
      (∑ k : Fin N, ∫ v, (boolIndNat k v : ℝ) ∂μ) =
        (N : ℝ) * ∫ v, (boolIndNat j v : ℝ) ∂μ := by
    rw [Finset.sum_congr rfl fun k _ ↦ hconst k, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt j.2)
  rw [eq_div_iff hN_pos.ne', mul_comm]
  exact hsum_const.symm.trans hsum_eq

private theorem integral_boolIndNat_mul_of_ne {N m : ℕ} (hN2 : 2 ≤ N) (hmN : m ≤ N)
    {j k : Fin N} (hjk : j ≠ k) :
    ∫ v, (boolIndNat j v : ℝ) * (boolIndNat k v : ℝ) ∂hypergeomVecMeasure hmN =
      (m : ℝ) * ((m : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) := by
  let μ := hypergeomVecMeasure hmN
  have hint_pair : ∀ a b : Fin N,
      Integrable (fun v ↦ (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ)) μ := by
    intro a b
    have hzo : ∀ᵐ v ∂μ, boolIndNat a v * boolIndNat b v = 0 ∨
        boolIndNat a v * boolIndNat b v = 1 :=
      Filter.Eventually.of_forall fun v ↦ by
        rcases boolIndNat_zero_one a v with ha | ha <;>
          rcases boolIndNat_zero_one b v with hb | hb <;> simp [ha, hb]
    have h := integrable_nat_zero_one μ .of_discrete hzo
    simp only [Nat.cast_mul] at h
    exact h
  have hconst : ∀ (a b : Fin N), a ≠ b →
      ∫ v, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) ∂μ =
        ∫ v, (boolIndNat j v : ℝ) * (boolIndNat k v : ℝ) ∂μ := by
    intro a b hab
    let τ₁ : Equiv.Perm (Fin N) := Equiv.swap a j
    have hτ₁b_ne : τ₁ b ≠ j := by
      have : τ₁ b ≠ τ₁ a := τ₁.injective.ne hab.symm
      simpa [τ₁] using this
    let τ₂ : Equiv.Perm (Fin N) := Equiv.swap (τ₁ b) k
    let σ : Equiv.Perm (Fin N) := τ₂ * τ₁
    have hσa : σ a = j := by
      change τ₂ (τ₁ a) = j
      rw [Equiv.swap_apply_left]
      exact Equiv.swap_apply_of_ne_of_ne hτ₁b_ne.symm hjk
    have hσb : σ b = k := by
      change τ₂ (τ₁ b) = k
      exact Equiv.swap_apply_left (τ₁ b) k
    let g : (Fin N → Bool) → (Fin N → Bool) := fun v x ↦ v (σ x)
    have hmap : μ.map g = μ := hypergeomVecMeasure_perm_invariant hmN σ
    calc
      ∫ v, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) ∂μ
          = ∫ v, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) ∂(μ.map g) := by rw [hmap]
      _ = ∫ v, (boolIndNat a (g v) : ℝ) * (boolIndNat b (g v) : ℝ) ∂μ :=
          integral_map Measurable.of_discrete.aemeasurable
            Measurable.of_discrete.aestronglyMeasurable
      _ = ∫ v, (boolIndNat j v : ℝ) * (boolIndNat k v : ℝ) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
          simp [boolIndNat, g, hσa, hσb]
  have hsum_val :
      (∑ a : Fin N, ∑ b ∈ Finset.univ.erase a,
        ∫ v, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) ∂μ) =
        (m : ℝ) * ((m : ℝ) - 1) := by
    have h1 :
        (∑ a : Fin N, ∑ b ∈ Finset.univ.erase a,
          ∫ v, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) ∂μ) =
          ∫ v, (∑ a : Fin N, ∑ b ∈ Finset.univ.erase a,
            (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ)) ∂μ := by
      rw [integral_finsetSum Finset.univ fun a _ ↦
        integrable_finsetSum _ fun b _ ↦ hint_pair a b]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [integral_finsetSum _ fun b _ ↦ hint_pair a b]
    rw [h1]
    have hae : ∀ᵐ v ∂μ,
        (∑ a : Fin N, ∑ b ∈ Finset.univ.erase a,
          (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ)) =
          (m : ℝ) * ((m : ℝ) - 1) := by
      filter_upwards [ae_mem_hypergeomVecSet hmN] with v hv
      have hcard : (∑ a : Fin N, (boolIndNat a v : ℝ)) = (m : ℝ) := by
        exact_mod_cast (sum_boolIndNat_eq_card v).trans (mem_hypergeomVecSet.mp hv)
      have hsplit :
          (∑ a : Fin N, (boolIndNat a v : ℝ)) * (∑ b : Fin N, (boolIndNat b v : ℝ)) =
            (∑ a : Fin N, (boolIndNat a v : ℝ)) +
              ∑ a : Fin N, ∑ b ∈ Finset.univ.erase a,
                (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) := by
        rw [Finset.sum_mul]
        have hrow : ∀ a : Fin N,
            (boolIndNat a v : ℝ) * (∑ b : Fin N, (boolIndNat b v : ℝ)) =
              (boolIndNat a v : ℝ) +
                ∑ b ∈ Finset.univ.erase a, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) := by
          intro a
          rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
          congr 1
          rcases boolIndNat_zero_one a v with ha | ha <;> simp [ha]
        simp_rw [hrow]
        rw [Finset.sum_add_distrib]
      rw [hcard] at hsplit
      linarith
    rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]
  have hsum_const :
      (∑ a : Fin N, ∑ b ∈ Finset.univ.erase a,
        ∫ v, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) ∂μ) =
        ((N : ℝ) * ((N : ℝ) - 1)) *
          ∫ v, (boolIndNat j v : ℝ) * (boolIndNat k v : ℝ) ∂μ := by
    have hinner : ∀ a : Fin N,
        (∑ b ∈ Finset.univ.erase a, ∫ v, (boolIndNat a v : ℝ) * (boolIndNat b v : ℝ) ∂μ) =
          ((N : ℝ) - 1) * ∫ v, (boolIndNat j v : ℝ) * (boolIndNat k v : ℝ) ∂μ := by
      intro a
      rw [Finset.sum_congr rfl fun b hb ↦ hconst a b (Finset.mem_erase.mp hb).1.symm,
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  have hdenom_pos : (0 : ℝ) < (N : ℝ) * ((N : ℝ) - 1) := by
    have hN : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    nlinarith
  rw [eq_div_iff hdenom_pos.ne', mul_comm]
  exact hsum_const.symm.trans hsum_val

/-! ### Section 2: Replacement Coupling on `Finset (Fin N)` and `Fin N → Bool` -/

/-- Single-step hypergeometric replacement map: keep `A` if `b ∈ A`, and if `b ∉ A` with
`A.card = m`, replace the `u`-th element of `A` (in canonical order) by `b`. -/
private def hypergeomStepSet {N m : ℕ} (b : Fin N) (A : Finset (Fin N)) (u : Fin m) :
    Finset (Fin N) :=
  if b ∈ A then A
  else if hcard : A.card = m then
    insert b (A.erase (A.orderEmbOfFin hcard u))
  else A

private def hypergeomStepVec {N m : ℕ} (b : Fin N) (v : Fin N → Bool) (u : Fin m) :
    Fin N → Bool :=
  setToBoolVec (hypergeomStepSet b (boolSupport v) u)

private theorem setToBoolVec_hypergeomStepSet {N m : ℕ} (b : Fin N) (A : Finset (Fin N))
    (u : Fin m) :
    setToBoolVec (hypergeomStepSet b A u) = hypergeomStepVec b (setToBoolVec A) u := by
  simp [hypergeomStepVec]

private theorem hypergeomStepSet_subset_insert {N m : ℕ} (b : Fin N) (A : Finset (Fin N))
    (u : Fin m) :
    hypergeomStepSet b A u ⊆ insert b A := by
  dsimp [hypergeomStepSet]
  split_ifs with hb hcard
  · exact Finset.subset_insert b A
  · exact Finset.insert_subset_insert b (Finset.erase_subset _ A)
  · exact Finset.subset_insert b A

private theorem indicator_hypergeomStepSet_le {N m : ℕ} (b : Fin N) (A : Finset (Fin N))
    (u : Fin m) {c : Fin N} (hcb : c ≠ b) :
    (if c ∈ hypergeomStepSet b A u then (1 : ℕ) else 0) ≤ (if c ∈ A then 1 else 0) := by
  by_cases hc : c ∈ hypergeomStepSet b A u
  · have hc_ins := hypergeomStepSet_subset_insert b A u hc
    have hcA : c ∈ A := (Finset.mem_insert.mp hc_ins).resolve_left hcb
    simp [hc, hcA]
  · simp [hc]

private theorem measure_eq_of_const_on_finset {α : Type*} [Finite α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (μ₁ μ₂ : Measure α) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {T : Finset α} (hT : T.Nonempty)
    {c₁ c₂ : ℝ≥0∞}
    (h1_in : ∀ w ∈ T, μ₁ {w} = c₁) (h1_out : ∀ w ∉ T, μ₁ {w} = 0)
    (h2_in : ∀ w ∈ T, μ₂ {w} = c₂) (h2_out : ∀ w ∉ T, μ₂ {w} = 0) :
    μ₁ = μ₂ := by
  cases nonempty_fintype α
  obtain ⟨w₀, hw₀⟩ := hT
  have hsum : ∀ (μ : Measure α) [IsProbabilityMeasure μ],
      (∀ w ∈ T, μ {w} = μ {w₀}) → (∀ w ∉ T, μ {w} = 0) →
      (T.card : ℝ) * μ.real {w₀} = 1 := by
    intro μ _ hin hout
    have huniv : (∑ x : α, μ {x}) = 1 := by
      have h1 : (Set.univ : Set α) = ⋃ x ∈ (Finset.univ : Finset α), ({x} : Set α) := by
        ext x
        simp
      rw [← measure_univ (μ := μ), h1,
        measure_biUnion_finset (fun x _ y _ hxy ↦ Set.disjoint_singleton.mpr hxy)
          (fun _ _ ↦ .of_discrete)]
    have hsplit : (∑ x : α, μ {x}) = ∑ _x ∈ T, μ {w₀} := by
      rw [← Finset.sum_subset (Finset.subset_univ T) (fun x _ hxT ↦ hout x hxT)]
      exact Finset.sum_congr rfl fun x hx ↦ hin x hx
    have hreal : ((∑ x : α, μ {x})).toReal = 1 := by rw [huniv, ENNReal.toReal_one]
    rw [hsplit, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ← measureReal_def] at hreal
    exact hreal
  have h1_sum := hsum μ₁ (fun w hw ↦ (h1_in w hw).trans (h1_in w₀ hw₀).symm) h1_out
  have h2_sum := hsum μ₂ (fun w hw ↦ (h2_in w hw).trans (h2_in w₀ hw₀).symm) h2_out
  have hcard_pos : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨w₀, hw₀⟩
  have hreal_eq : μ₁.real {w₀} = μ₂.real {w₀} :=
    mul_left_cancel₀ hcard_pos.ne' (h1_sum.trans h2_sum.symm)
  have hc_eq : c₁ = c₂ := by
    rw [← h1_in w₀ hw₀, ← h2_in w₀ hw₀, ← ofReal_measureReal, ← ofReal_measureReal, hreal_eq]
  refine measure_ext_of_singleton_fintype fun w ↦ ?_
  by_cases hw : w ∈ T
  · rw [h1_in w hw, h2_in w hw, hc_eq]
  · rw [h1_out w hw, h2_out w hw]

private theorem map_hypergeomStepVec_eq_cond {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) (b : Fin N) :
    let μ := hypergeomVecMeasure hmN
    let νU : Measure (Fin m) := (@PMF.uniformOfFintype (Fin m) inferInstance ⟨⟨0, hm1⟩⟩).toMeasure
    (μ.prod νU).map (fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b p.1 p.2) =
      ProbabilityTheory.cond μ {v | v b = true} := by
  classical
  intro μ νU
  have : IsProbabilityMeasure νU := PMF.toMeasure.isProbabilityMeasure _
  let T : Finset (Fin N → Bool) := (hypergeomVecSet N m).filter fun w ↦ w b = true
  have hT_ne : T.Nonempty := by
    have hcard_er : (Finset.univ.erase b).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin]
    have hsub_le : m - 1 ≤ (Finset.univ.erase b).card := by omega
    obtain ⟨E, hE⟩ := Finset.powersetCard_nonempty.mpr hsub_le
    obtain ⟨hE_sub, hE_card⟩ := Finset.mem_powersetCard.mp hE
    have hbE : b ∉ E := fun hb ↦ (Finset.mem_erase.mp (hE_sub hb)).1 rfl
    refine ⟨setToBoolVec (insert b E), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · rw [mem_hypergeomVecSet, boolSupport_setToBoolVec, Finset.card_insert_of_notMem hbE, hE_card]
      omega
    · simp
  obtain ⟨w₀, hw₀⟩ := hT_ne
  have hμ_event_ne : μ {v | v b = true} ≠ 0 := by
    intro h0
    have hw₀_le : μ {w₀} ≤ μ {v | v b = true} :=
      measure_mono (Set.singleton_subset_iff.mpr (Finset.mem_filter.mp hw₀).2)
    have hw₀_zero : μ {w₀} = 0 := le_antisymm (hw₀_le.trans (le_of_eq h0)) zero_le
    rw [hypergeomVecMeasure_singleton, ite_eq_left (Finset.mem_filter.mp hw₀).1] at hw₀_zero
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _) hw₀_zero
  have : IsProbabilityMeasure (ProbabilityTheory.cond μ {v | v b = true}) :=
    ProbabilityTheory.cond_isProbabilityMeasure hμ_event_ne
  let μ₁ := (μ.prod νU).map (fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b p.1 p.2)
  have : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance
  let c₁ : ℝ≥0∞ := (N : ℝ≥0∞) * (((N.choose m : ℝ≥0∞))⁻¹ * ((m : ℝ≥0∞))⁻¹)
  let c₂ : ℝ≥0∞ := (μ {v | v b = true})⁻¹ * ((N.choose m : ℝ≥0∞))⁻¹
  have h2_in : ∀ w ∈ T, (ProbabilityTheory.cond μ {v | v b = true}) {w} = c₂ := by
    intro w hw
    rw [ProbabilityTheory.cond_apply .of_discrete]
    have hint : ({v : Fin N → Bool | v b = true} ∩ {w}) = {w} :=
      Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr (Finset.mem_filter.mp hw).2)
    rw [hint, hypergeomVecMeasure_singleton, ite_eq_left (Finset.mem_filter.mp hw).1]
  have h2_out : ∀ w ∉ T, (ProbabilityTheory.cond μ {v | v b = true}) {w} = 0 := by
    intro w hw
    rw [ProbabilityTheory.cond_apply .of_discrete]
    by_cases hwb : w b = true
    · have hw_not : w ∉ hypergeomVecSet N m := fun h ↦ hw (Finset.mem_filter.mpr ⟨h, hwb⟩)
      have hint : ({v : Fin N → Bool | v b = true} ∩ {w}) = {w} :=
        Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hwb)
      rw [hint, hypergeomVecMeasure_singleton, ite_eq_right hw_not, mul_zero]
    · have hint : ({v : Fin N → Bool | v b = true} ∩ {w}) = ∅ := by
        ext v
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        rintro hv rfl
        exact hwb hv
      rw [hint, measure_empty, mul_zero]
  have hprod_singleton : ∀ (v : Fin N → Bool) (u : Fin m),
      (μ.prod νU) {(v, u)} =
        if v ∈ hypergeomVecSet N m then ((N.choose m : ℝ≥0∞))⁻¹ * ((m : ℝ≥0∞))⁻¹ else 0 := by
    intro v u
    have hset : ({(v, u)} : Set ((Fin N → Bool) × Fin m)) = ({v} : Set _) ×ˢ ({u} : Set _) := by
      ext ⟨x, y⟩
      simp
    rw [hset, Measure.prod_prod, hypergeomVecMeasure_singleton]
    have hνU : νU {u} = ((m : ℝ≥0∞))⁻¹ := by
      rw [PMF.toMeasure_apply_singleton _ _ .of_discrete,
        @PMF.uniformOfFintype_apply (Fin m) inferInstance ⟨⟨0, hm1⟩⟩ u,
        Fintype.card_fin]
    rw [hνU]
    split_ifs <;> simp
  have hstep_mem_T : ∀ v ∈ hypergeomVecSet N m, ∀ u : Fin m, hypergeomStepVec b v u ∈ T := by
    intro v hv u
    have hcard : (boolSupport v).card = m := mem_hypergeomVecSet.mp hv
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_hypergeomVecSet]
      dsimp [hypergeomStepVec, hypergeomStepSet]
      by_cases hb : b ∈ boolSupport v
      · simp [hb, hcard]
      · simp only [hb, ↓reduceIte, hcard, ↓reduceDIte, boolSupport_setToBoolVec]
        set y := (boolSupport v).orderEmbOfFin hcard u
        have hy : y ∈ boolSupport v := Finset.orderEmbOfFin_mem (boolSupport v) hcard u
        have hb_er : b ∉ (boolSupport v).erase y := fun h ↦ hb (Finset.erase_subset y _ h)
        rw [Finset.card_insert_of_notMem hb_er, Finset.card_erase_of_mem hy]
        omega
    · dsimp [hypergeomStepVec, hypergeomStepSet]
      by_cases hb : b ∈ boolSupport v
      · simp [hb]
      · simp [hb, hcard]
  have h1_out : ∀ w ∉ T, μ₁ {w} = 0 := by
    intro w hw
    rw [measure_map_singleton_fintype (μ.prod νU)
      (fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b p.1 p.2) w]
    refine Finset.sum_eq_zero fun ⟨v, u⟩ hvu ↦ ?_
    rw [hprod_singleton]
    have hv_not : v ∉ hypergeomVecSet N m := by
      intro hv
      have hstep : hypergeomStepVec b v u = w := (Finset.mem_filter.mp hvu).2
      exact hw (hstep ▸ hstep_mem_T v hv u)
    exact ite_eq_right hv_not
  have h1_in : ∀ w ∈ T, μ₁ {w} = c₁ := by
    intro w hw
    rw [measure_map_singleton_fintype (μ.prod νU)
      (fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b p.1 p.2) w]
    let S_pre := (hypergeomVecSet N m ×ˢ (Finset.univ : Finset (Fin m))).filter
      fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b p.1 p.2 = w
    have hsum_eq :
        (∑ p ∈ Finset.univ.filter
          (fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b p.1 p.2 = w),
          (μ.prod νU) {p}) =
        ∑ p ∈ S_pre, (((N.choose m : ℝ≥0∞))⁻¹ * ((m : ℝ≥0∞))⁻¹) := by
      have hsub : S_pre ⊆ Finset.univ.filter
          (fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b p.1 p.2 = w) := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, (Finset.mem_filter.mp hp).2⟩
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun ⟨v, u⟩ hvu ↦ ?_
        have hv : v ∈ hypergeomVecSet N m :=
          (Finset.mem_product.mp (Finset.mem_filter.mp hvu).1).1
        rw [hprod_singleton, ite_eq_left hv]
      · intro ⟨v, u⟩ hvu hnot
        have hstep : hypergeomStepVec b v u = w := (Finset.mem_filter.mp hvu).2
        have hv_not : v ∉ hypergeomVecSet N m := fun hv ↦
          hnot (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, Finset.mem_univ u⟩, hstep⟩)
        rw [hprod_singleton, ite_eq_right hv_not]
    rw [hsum_eq, Finset.sum_const, nsmul_eq_mul]
    suffices hcard_pre : S_pre.card = N by
      rw [hcard_pre]
    let B := boolSupport w
    have hB_card : B.card = m := mem_hypergeomVecSet.mp (Finset.mem_filter.mp hw).1
    have hbB : b ∈ B := (mem_boolSupport w b).mpr (Finset.mem_filter.mp hw).2
    let S₁ : Finset ((Fin N → Bool) × Fin m) :=
      (Finset.univ : Finset (Fin m)).map ⟨fun u ↦ (w, u), fun u₁ u₂ h ↦ (Prod.mk.inj h).2⟩
    let compB : Finset (Fin N) := Finset.univ \ B
    have hAy_card : ∀ y ∈ compB, (insert y (B.erase b)).card = m := by
      intro y hy
      have hyB : y ∉ B := (Finset.mem_sdiff.mp hy).2
      have hy_er : y ∉ B.erase b := fun h ↦ hyB (Finset.erase_subset b B h)
      rw [Finset.card_insert_of_notMem hy_er, Finset.card_erase_of_mem hbB, hB_card]
      omega
    let mkPair : (y : {y : Fin N // y ∈ compB}) → (Fin N → Bool) × Fin m := fun y ↦
      let Ay := insert y.1 (B.erase b)
      let hcard := hAy_card y.1 y.2
      let u := (Ay.orderIsoOfFin hcard).symm ⟨y.1, Finset.mem_insert_self y.1 _⟩
      (setToBoolVec Ay, u)
    have hmk_inj : Function.Injective mkPair := by
      intro y₁ y₂ h
      have hset : insert y₁.1 (B.erase b) = insert y₂.1 (B.erase b) := by
        have hv := (Prod.mk.inj h).1
        simpa [mkPair] using congrArg boolSupport hv
      have hmem : y₁.1 ∈ insert y₂.1 (B.erase b) := hset ▸ Finset.mem_insert_self y₁.1 _
      rcases Finset.mem_insert.mp hmem with heq | her
      · exact Subtype.ext heq
      · exact False.elim ((Finset.mem_sdiff.mp y₁.2).2 (Finset.erase_subset b B her))
    let S₂ : Finset ((Fin N → Bool) × Fin m) :=
      (Finset.univ : Finset {y : Fin N // y ∈ compB}).map ⟨mkPair, hmk_inj⟩
    have hdisj : Disjoint S₁ S₂ := by
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ ↦ ?_
      rcases Finset.mem_map.mp hp₁ with ⟨u, _, rfl⟩
      rcases Finset.mem_map.mp hp₂ with ⟨y, _, hy_eq⟩
      have hw_eq : setToBoolVec (insert y.1 (B.erase b)) = w := (Prod.mk.inj hy_eq).1
      have hB_eq : insert y.1 (B.erase b) = B := by
        simpa [B] using congrArg boolSupport hw_eq
      exact (Finset.mem_sdiff.mp y.2).2 (hB_eq ▸ Finset.mem_insert_self y.1 _)
    have hunion : S_pre = S₁ ∪ S₂ := by
      ext ⟨v, u⟩
      simp only [Finset.mem_union]
      constructor
      · intro hp
        have hv : v ∈ hypergeomVecSet N m :=
          (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        have hstep : hypergeomStepVec b v u = w := (Finset.mem_filter.mp hp).2
        have hA_card : (boolSupport v).card = m := mem_hypergeomVecSet.mp hv
        have hstep_set : hypergeomStepSet b (boolSupport v) u = B := by
          have := congrArg boolSupport hstep
          simpa [hypergeomStepVec, B] using this
        by_cases hbw : b ∈ boolSupport v
        · left
          have hv_eq : v = w := by
            rw [← setToBoolVec_boolSupport v, ← setToBoolVec_boolSupport w]
            have : boolSupport v = B := by simpa [hypergeomStepSet, hbw] using hstep_set
            simp [this, B]
          subst hv_eq
          exact Finset.mem_map.mpr ⟨u, Finset.mem_univ u, rfl⟩
        · right
          simp only [hypergeomStepSet, hbw, ↓reduceIte, hA_card, ↓reduceDIte] at hstep_set
          set y := (boolSupport v).orderEmbOfFin hA_card u
          have hyA : y ∈ boolSupport v := Finset.orderEmbOfFin_mem (boolSupport v) hA_card u
          have hb_er : b ∉ (boolSupport v).erase y := fun h ↦ hbw (Finset.erase_subset y _ h)
          have her_eq : (boolSupport v).erase y = B.erase b := by
            have := congrArg (fun E ↦ E.erase b) hstep_set
            simpa [Finset.erase_insert hb_er] using this
          have hA_eq : boolSupport v = insert y (B.erase b) := by
            rw [← her_eq, Finset.insert_erase hyA]
          have hyB : y ∉ B := by
            intro hyB
            have hy_ne_b : y ≠ b := fun h ↦ hbw (h ▸ hyA)
            have hy_in_er : y ∈ B.erase b := Finset.mem_erase.mpr ⟨hy_ne_b, hyB⟩
            rw [← her_eq] at hy_in_er
            exact (Finset.mem_erase.mp hy_in_er).1 rfl
          have hy_comp : y ∈ compB := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyB⟩
          refine Finset.mem_map.mpr ⟨⟨y, hy_comp⟩, Finset.mem_univ _, ?_⟩
          have hv_eq : setToBoolVec (insert y (B.erase b)) = v := by
            rw [← hA_eq, setToBoolVec_boolSupport]
          refine Prod.ext hv_eq ?_
          dsimp [mkPair]
          set hcard' := hAy_card y hy_comp
          set u' := ((insert y (B.erase b)).orderIsoOfFin hcard').symm
            ⟨y, Finset.mem_insert_self y _⟩
          have hu'_val : (insert y (B.erase b)).orderEmbOfFin hcard' u' = y := by
            change (((insert y (B.erase b)).orderIsoOfFin hcard') u').1 = y
            simp [u']
          have hu_val : (insert y (B.erase b)).orderEmbOfFin hcard' u = y := by
            have : (boolSupport v).orderEmbOfFin hA_card =
                (insert y (B.erase b)).orderEmbOfFin hcard' := by
              congr 1
            exact this ▸ rfl
          exact ((insert y (B.erase b)).orderEmbOfFin hcard').injective (hu'_val.trans hu_val.symm)
      · rintro (hp₁ | hp₂)
        · rcases Finset.mem_map.mp hp₁ with ⟨u', _, h_eq⟩
          rcases Prod.mk.inj h_eq with ⟨rfl, rfl⟩
          refine Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hw).1, Finset.mem_univ u'⟩, ?_⟩
          dsimp [hypergeomStepVec, hypergeomStepSet]
          rw [ite_eq_left hbB, setToBoolVec_boolSupport]
        · rcases Finset.mem_map.mp hp₂ with ⟨⟨y, hy⟩, _, h_eq⟩
          rcases Prod.mk.inj h_eq with ⟨rfl, rfl⟩
          set Ay := insert y (B.erase b)
          set hcard' := hAy_card y hy
          have hv_mem : setToBoolVec Ay ∈ hypergeomVecSet N m := by
            rw [mem_hypergeomVecSet, boolSupport_setToBoolVec]
            exact hcard'
          refine Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hv_mem, Finset.mem_univ _⟩, ?_⟩
          have hyB : y ∉ B := (Finset.mem_sdiff.mp hy).2
          have hy_ne_b : y ≠ b := fun h ↦ hyB (h ▸ hbB)
          have hb_Ay : b ∉ Ay := by
            simp [Ay, hy_ne_b.symm]
          dsimp [hypergeomStepVec, hypergeomStepSet]
          have hb_not : b ∉ insert y (B.erase b) := hb_Ay
          rw [boolSupport_setToBoolVec, ite_eq_right hb_not]
          simp only [hcard', ↓reduceDIte]
          set u' := (Ay.orderIsoOfFin hcard').symm ⟨y, Finset.mem_insert_self y _⟩
          have hu'_val : (insert y (B.erase b)).orderEmbOfFin hcard' u' = y := by
            change ((Ay.orderIsoOfFin hcard') u').1 = y
            simp [u']
          rw [hu'_val]
          have hy_er : y ∉ B.erase b := fun h ↦ hyB (Finset.erase_subset b B h)
          rw [Finset.erase_insert hy_er, Finset.insert_erase hbB]
          exact setToBoolVec_boolSupport w
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    have hcard₁ : S₁.card = m := by
      rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hcard₂ : S₂.card = N - m := by
      rw [Finset.card_map, Finset.card_univ, Fintype.card_coe]
      simp [compB, Finset.card_sdiff, hB_card]
    rw [hcard₁, hcard₂]
    omega
  exact measure_eq_of_const_on_finset μ₁ (ProbabilityTheory.cond μ {v | v b = true}) ⟨w₀, hw₀⟩
    h1_in h1_out h2_in h2_out

/-! ### Section 3: Example 4.13 (`ex4_13_sizeBias`, `ex4_13_moments_corrected`,
`not_ex4_13_var_printed`, `ex4_13_restricted`) -/

/-- Exchangeability of the red-ball indicators in Example 4.13 (`SteinIntro.tex:2488`). -/
private theorem ex4_13_exchangeable
    {N n m : ℕ} (hnN : n ≤ N) (hmN : m ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)}
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) :
    IsExchangeableTuple P (fun (i : Fin n) ω ↦ if Fin.castLE hnN i ∈ S ω then (1 : ℕ) else 0) := by
  intro σ
  let V : Ω → Fin N → Bool := fun ω ↦ setToBoolVec (S ω)
  have hV_meas : Measurable V := measurable_comp_finset_of_levelSet hS setToBoolVec
  have hV_law : P.map V = hypergeomVecMeasure hmN :=
    map_setToBoolVec_eq_hypergeomVecMeasure hmN P hS hS_unif
  let σ_ext : Equiv.Perm (Fin N) :=
    { toFun := fun j ↦ if hj : j.1 < n then Fin.castLE hnN (σ ⟨j.1, hj⟩) else j
      invFun := fun j ↦ if hj : j.1 < n then Fin.castLE hnN (σ.symm ⟨j.1, hj⟩) else j
      left_inv := fun j ↦ by
        by_cases hj : j.1 < n
        · have hj' : (Fin.castLE hnN (σ ⟨j.1, hj⟩)).1 < n := (σ ⟨j.1, hj⟩).2
          simp only [hj, ↓reduceDIte, hj']
          ext
          simp
        · simp [hj]
      right_inv := fun j ↦ by
        by_cases hj : j.1 < n
        · have hj' : (Fin.castLE hnN (σ.symm ⟨j.1, hj⟩)).1 < n := (σ.symm ⟨j.1, hj⟩).2
          simp only [hj, ↓reduceDIte, hj']
          ext
          simp
        · simp [hj] }
  let proj : (Fin N → Bool) → (Fin n → ℕ) :=
    fun v i ↦ if v (Fin.castLE hnN i) = true then 1 else 0
  let permVec : (Fin N → Bool) → (Fin N → Bool) := fun v j ↦ v (σ_ext j)
  have h1 : (fun ω i ↦ if Fin.castLE hnN (σ i) ∈ S ω then (1 : ℕ) else 0) =
      (proj ∘ permVec) ∘ V := by
    funext ω i
    have hσ : σ_ext (Fin.castLE hnN i) = Fin.castLE hnN (σ i) := by
      simp [σ_ext, i.2]
    simp [proj, permVec, V, setToBoolVec, hσ]
  have h2 : (fun ω i ↦ if Fin.castLE hnN i ∈ S ω then (1 : ℕ) else 0) = proj ∘ V := by
    funext ω i
    simp [proj, V, setToBoolVec]
  refine ⟨(Measurable.of_eval fun i ↦
      measurable_comp_finset_of_levelSet hS (fun A ↦ if Fin.castLE hnN (σ i) ∈ A then 1 else 0)
    ).aemeasurable,
    (Measurable.of_eval fun i ↦
      measurable_comp_finset_of_levelSet hS (fun A ↦ if Fin.castLE hnN i ∈ A then 1 else 0)
    ).aemeasurable, ?_⟩
  rw [h1, h2, ← Measure.map_map (Measurable.of_discrete.comp Measurable.of_discrete) hV_meas,
    ← Measure.map_map Measurable.of_discrete hV_meas, hV_law,
    ← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    hypergeomVecMeasure_perm_invariant hmN σ_ext]

/-- Example 4.13, size-bias coupling, exchangeability, and monotonicity (`[Hypergeometric
distribution]`, `SteinIntro.tex:2487-2498`). -/
theorem ex4_13_sizeBias
    {N n m : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)} {U : Ω → Fin m}
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ))
    (hU_meas : Measurable U)
    (hSU_indep : ProbabilityTheory.IndepFun (fun ω (j : Fin N) ↦ decide (j ∈ S ω)) U P)
    (hU_unif : P.map U = (@PMF.uniformOfFintype (Fin m) inferInstance ⟨⟨0, hm1⟩⟩).toMeasure) :
    let b₀ : Fin N := ⟨0, lt_of_lt_of_le hn1 hnN⟩
    let S' : Ω → Finset (Fin N) := fun ω ↦
      if b₀ ∈ S ω then S ω
      else if hcard : (S ω).card = m then
        insert b₀ ((S ω).erase ((S ω).orderEmbOfFin hcard (U ω)))
      else S ω
    let X : Fin n → Finset (Fin N) → ℕ :=
      fun i A ↦ if Fin.castLE hnN i ∈ A then 1 else 0
    let i₀ : Fin n := ⟨0, hn1⟩
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i (S ω) : ℝ)
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ i₀}, (X j.1 (S' ω) : ℝ)) + 1
    IsExchangeableTuple P (fun i ω ↦ X i (S ω)) ∧
      P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S' ω)) =
        (ProbabilityTheory.cond P {ω | X i₀ (S ω) = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S ω)) ∧
      (∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i₀}, X j.1 (S' ω) ≤ X j.1 (S ω)) ∧
      IsSizeBias P W P Ws := by
  intro b₀ S' X i₀ W Ws
  have hexch : IsExchangeableTuple P (fun i ω ↦ X i (S ω)) :=
    ex4_13_exchangeable hnN hmN P hS hS_unif
  let V : Ω → Fin N → Bool := fun ω ↦ setToBoolVec (S ω)
  have hV_meas : Measurable V := measurable_comp_finset_of_levelSet hS setToBoolVec
  have hV_law : P.map V = hypergeomVecMeasure hmN :=
    map_setToBoolVec_eq_hypergeomVecMeasure hmN P hS hS_unif
  have hVU_indep : ProbabilityTheory.IndepFun V U P := hSU_indep
  let νU : Measure (Fin m) := (@PMF.uniformOfFintype (Fin m) inferInstance ⟨⟨0, hm1⟩⟩).toMeasure
  have hVU_map : P.map (fun ω ↦ (V ω, U ω)) = (hypergeomVecMeasure hmN).prod νU := by
    rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hV_meas.aemeasurable hU_meas.aemeasurable).mp hVU_indep, hV_law, hU_unif]
  let projRest : (Fin N → Bool) → ({j : Fin n // j ≠ i₀} → ℕ) :=
    fun v j ↦ if v (Fin.castLE hnN j.1) = true then 1 else 0
  have hS'_vec : (fun ω ↦ setToBoolVec (S' ω)) =
      (fun p : (Fin N → Bool) × Fin m ↦ hypergeomStepVec b₀ p.1 p.2) ∘ (fun ω ↦ (V ω, U ω)) := by
    funext ω
    exact setToBoolVec_hypergeomStepSet b₀ (S ω) (U ω)
  have hX_S' : (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S' ω)) =
      projRest ∘ (fun ω ↦ setToBoolVec (S' ω)) := by
    funext ω j
    simp [projRest, X, setToBoolVec]
  have hS'_meas : Measurable (fun ω ↦ setToBoolVec (S' ω)) := by
    rw [hS'_vec]
    exact Measurable.of_discrete.comp (hV_meas.prodMk hU_meas)
  have hmap_lhs :
      P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S' ω)) =
        (ProbabilityTheory.cond (hypergeomVecMeasure hmN) {v | v b₀ = true}).map projRest := by
    rw [hX_S', ← Measure.map_map Measurable.of_discrete hS'_meas, hS'_vec,
      ← Measure.map_map Measurable.of_discrete (hV_meas.prodMk hU_meas), hVU_map,
      map_hypergeomStepVec_eq_cond hm1 hmN b₀]
  have hevent_pre : {ω : Ω | X i₀ (S ω) = 1} = V ⁻¹' {v : Fin N → Bool | v b₀ = true} := by
    ext ω
    have hcast : Fin.castLE hnN i₀ = b₀ := rfl
    by_cases h : b₀ ∈ S ω <;> simp [X, hcast, V, setToBoolVec, h]
  have hcond_V :
      (ProbabilityTheory.cond P {ω | X i₀ (S ω) = 1}).map V =
        ProbabilityTheory.cond (hypergeomVecMeasure hmN) {v | v b₀ = true} := by
    ext E hE
    rw [hevent_pre, Measure.map_apply hV_meas hE,
      ProbabilityTheory.cond_apply (hV_meas .of_discrete),
      ProbabilityTheory.cond_apply .of_discrete, ← hV_law, Measure.map_apply hV_meas .of_discrete,
      Measure.map_apply hV_meas (MeasurableSet.of_discrete.inter hE), Set.preimage_inter]
  have hX_S : (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S ω)) = projRest ∘ V := by
    funext ω j
    simp [projRest, X, V, setToBoolVec]
  have hcond_law :
      P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S' ω)) =
        (ProbabilityTheory.cond P {ω | X i₀ (S ω) = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S ω)) := by
    rw [hmap_lhs, ← hcond_V, Measure.map_map Measurable.of_discrete hV_meas, ← hX_S]
  have hmono : ∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i₀}, X j.1 (S' ω) ≤ X j.1 (S ω) := by
    intro ω j
    have hne : Fin.castLE hnN j.1 ≠ b₀ := by
      intro h
      apply j.2
      exact Fin.castLE_injective hnN h
    exact indicator_hypergeomStepSet_le b₀ (S ω) (U ω) hne
  have hsb : IsSizeBias P W P Ws := by
    let Xr : Fin n → Ω → ℝ := fun i ω ↦ (X i (S ω) : ℝ)
    let Yr : Ω → ({j : Fin n // j ≠ i₀} → ℝ) := fun ω j ↦ (X j.1 (S' ω) : ℝ)
    have hX_meas : ∀ i : Fin n, Measurable (fun ω ↦ X i (S ω)) :=
      fun i ↦ measurable_comp_finset_of_levelSet hS (X i)
    have hX'_meas : ∀ j : {j : Fin n // j ≠ i₀}, Measurable (fun ω ↦ X j.1 (S' ω)) := fun j ↦ by
      have hYj : (fun ω ↦ X j.1 (S' ω)) = (fun f : {j : Fin n // j ≠ i₀} → ℕ ↦ f j) ∘
          projRest ∘ (fun ω ↦ setToBoolVec (S' ω)) := by
        funext ω
        simp [X, projRest, setToBoolVec]
      rw [hYj]
      exact Measurable.of_discrete.comp (Measurable.of_discrete.comp hS'_meas)
    have hXr_meas : ∀ i : Fin n, Measurable (Xr i) :=
      fun i ↦ (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (hX_meas i)
    have hXr_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, Xr i ω = 0 ∨ Xr i ω = 1 :=
      fun i ↦ Filter.Eventually.of_forall fun ω ↦ by
        by_cases h : Fin.castLE hnN i ∈ S ω <;> simp [Xr, X, h]
    have hexch_r : IsExchangeableTuple P Xr := fun σ ↦
      (hexch σ).comp (Measurable.of_eval fun i ↦
        (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply i))
    have hYr_meas : AEMeasurable Yr P :=
      (Measurable.of_eval fun j ↦
        (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (hX'_meas j)).aemeasurable
    have hYr_law : 0 < P.real (Xr i₀ ⁻¹' {1}) →
        P.map Yr =
          (ProbabilityTheory.cond P (Xr i₀ ⁻¹' {1})).map
            (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ Xr j.1 ω) := by
      intro _
      have hpre : Xr i₀ ⁻¹' {(1 : ℝ)} = {ω | X i₀ (S ω) = 1} := by
        ext ω
        simp [Xr]
      rw [hpre]
      let castPi : ({j : Fin n // j ≠ i₀} → ℕ) → ({j : Fin n // j ≠ i₀} → ℝ) :=
        fun u j ↦ (u j : ℝ)
      have hcast : Measurable castPi :=
        Measurable.of_eval fun j ↦
          (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply j)
      have h1 : P.map Yr =
          (P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S' ω))).map castPi :=
        (Measure.map_map hcast (Measurable.of_eval hX'_meas)).symm
      rw [h1, hcond_law, Measure.map_map hcast (Measurable.of_eval fun j ↦ hX_meas j.1)]
      rfl
    exact sizeBias_sum_of_exchangeable_zero_one_fintype P P i₀ hXr_meas hXr_zo hexch_r
      hYr_meas hYr_law
  exact ⟨hexch, hcond_law, hmono, hsb⟩

/-- Example 4.13, corrected moment formulas (`[Hypergeometric distribution]`,
`SteinIntro.tex:2499-2501`; `ISSUE-TYPO-4.13`). -/
theorem ex4_13_moments_corrected
    {N n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)}
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (_hm1 : 1 ≤ m) (hmN : m ≤ N)
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) :
    let W : Ω → ℝ := fun ω ↦ (((S ω).filter fun j : Fin N ↦ j.1 < n).card : ℝ)
    ∫ ω, W ω ∂P = (n : ℝ) * (m : ℝ) / (N : ℝ) ∧
      (2 ≤ N →
        ProbabilityTheory.variance W P =
          (n : ℝ) * (m : ℝ) * ((N : ℝ) - (n : ℝ)) * ((N : ℝ) - (m : ℝ)) /
            ((N : ℝ) ^ 2 * ((N : ℝ) - 1))) := by
  intro W
  let V : Ω → Fin N → Bool := fun ω ↦ setToBoolVec (S ω)
  have hV_meas : Measurable V := measurable_comp_finset_of_levelSet hS setToBoolVec
  let μ := hypergeomVecMeasure hmN
  have hV_law : P.map V = μ := map_setToBoolVec_eq_hypergeomVecMeasure hmN P hS hS_unif
  let W_vec : (Fin N → Bool) → ℝ := fun v ↦ ∑ i : Fin n, (boolIndNat (Fin.castLE hnN i) v : ℝ)
  have hW_eq : W = W_vec ∘ V := by
    funext ω
    change (((S ω).filter fun j : Fin N ↦ j.1 < n).card : ℝ) =
      ∑ i : Fin n, (boolIndNat (Fin.castLE hnN i) (V ω) : ℝ)
    rw [redCountSet_eq_sum hnN (S ω), Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : Fin.castLE hnN i ∈ S ω <;> simp [boolIndNat, V, h]
  have hint_ind : ∀ i : Fin n, Integrable (fun v ↦ (boolIndNat (Fin.castLE hnN i) v : ℝ)) μ :=
    fun i ↦ integrable_nat_zero_one μ .of_discrete
      (Filter.Eventually.of_forall (boolIndNat_zero_one (Fin.castLE hnN i)))
  have hmean_vec : ∫ v, W_vec v ∂μ = (n : ℝ) * (m : ℝ) / (N : ℝ) := by
    dsimp [W_vec]
    rw [integral_finsetSum Finset.univ fun i _ ↦ hint_ind i,
      Finset.sum_congr rfl fun i _ ↦ integral_boolIndNat hmN (Fin.castLE hnN i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc]
  have hmean : ∫ ω, W ω ∂P = (n : ℝ) * (m : ℝ) / (N : ℝ) := by
    have hW_app : ∀ ω, W ω = W_vec (V ω) := congrFun hW_eq
    simp_rw [hW_app]
    rw [← integral_map hV_meas.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable, hV_law, hmean_vec]
  refine ⟨hmean, fun hN2 ↦ ?_⟩
  have hvar_eq : ProbabilityTheory.variance W P = ProbabilityTheory.variance W_vec μ := by
    rw [hW_eq, ← hV_law,
      ProbabilityTheory.variance_map (X := W_vec) (Y := V)
        Measurable.of_discrete.aemeasurable hV_meas.aemeasurable]
  rw [hvar_eq]
  have hmem2 : MemLp W_vec 2 μ := by
    have hcast : W_vec = fun v ↦ ((∑ i : Fin n, boolIndNat (Fin.castLE hnN i) v : ℕ) : ℝ) := by
      funext v
      simp [W_vec]
    rw [hcast]
    exact memLp_two_sum_nat_zero_one (hypergeomVecMeasure hmN)
      (X := fun i v ↦ boolIndNat (Fin.castLE hnN i) v) (fun _ ↦ .of_discrete)
      (fun i ↦ Filter.Eventually.of_forall (boolIndNat_zero_one (Fin.castLE hnN i)))
  rw [ProbabilityTheory.variance_eq_sub hmem2]
  simp only [Pi.pow_apply]
  have hsq_expand : ∀ v : Fin N → Bool,
      W_vec v ^ 2 = W_vec v +
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          (boolIndNat (Fin.castLE hnN i) v : ℝ) * (boolIndNat (Fin.castLE hnN j) v : ℝ) := by
    intro v
    dsimp [W_vec]
    rw [sq, Finset.sum_mul]
    have hrow : ∀ i : Fin n,
        (boolIndNat (Fin.castLE hnN i) v : ℝ) *
            (∑ j : Fin n, (boolIndNat (Fin.castLE hnN j) v : ℝ)) =
          (boolIndNat (Fin.castLE hnN i) v : ℝ) +
            ∑ j ∈ Finset.univ.erase i,
              (boolIndNat (Fin.castLE hnN i) v : ℝ) * (boolIndNat (Fin.castLE hnN j) v : ℝ) := by
      intro i
      rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      rcases boolIndNat_zero_one (Fin.castLE hnN i) v with hi | hi <;> simp [hi]
    simp_rw [hrow]
    rw [Finset.sum_add_distrib]
  simp_rw [hsq_expand]
  have hint_pair : ∀ i j : Fin n,
      Integrable (fun v ↦ (boolIndNat (Fin.castLE hnN i) v : ℝ) *
        (boolIndNat (Fin.castLE hnN j) v : ℝ)) μ := by
    intro i j
    have hzo : ∀ᵐ v ∂μ,
        boolIndNat (Fin.castLE hnN i) v * boolIndNat (Fin.castLE hnN j) v = 0 ∨
          boolIndNat (Fin.castLE hnN i) v * boolIndNat (Fin.castLE hnN j) v = 1 :=
      Filter.Eventually.of_forall fun v ↦ by
        rcases boolIndNat_zero_one (Fin.castLE hnN i) v with hi | hi <;>
          rcases boolIndNat_zero_one (Fin.castLE hnN j) v with hj | hj <;> simp [hi, hj]
    have h := integrable_nat_zero_one μ .of_discrete hzo
    simp only [Nat.cast_mul] at h
    exact h
  rw [integral_add (hmem2.integrable one_le_two)
    (integrable_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hint_pair i j),
    hmean_vec,
    integral_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hint_pair i j]
  have hinner : ∀ i : Fin n,
      ∫ v, (∑ j ∈ Finset.univ.erase i,
        (boolIndNat (Fin.castLE hnN i) v : ℝ) * (boolIndNat (Fin.castLE hnN j) v : ℝ)) ∂μ =
      ((n : ℝ) - 1) * ((m : ℝ) * ((m : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1))) := by
    intro i
    rw [integral_finsetSum _ fun j _ ↦ hint_pair i j]
    have hterm : ∀ j ∈ Finset.univ.erase i,
        ∫ v, (boolIndNat (Fin.castLE hnN i) v : ℝ) * (boolIndNat (Fin.castLE hnN j) v : ℝ) ∂μ =
          (m : ℝ) * ((m : ℝ) - 1) / ((N : ℝ) * ((N : ℝ) - 1)) := by
      intro j hj
      have hj_ne : Fin.castLE hnN i ≠ Fin.castLE hnN j :=
        (Fin.castLE_injective hnN).ne (Finset.mem_erase.mp hj).1.symm
      exact integral_boolIndNat_mul_of_ne hN2 hmN hj_ne
    rw [Finset.sum_congr rfl hterm, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub hn1, Nat.cast_one]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hN1_pos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  field_simp [hN_pos.ne', hN1_pos.ne']
  ring

/-- Refutation of the printed variance formula in Example 4.13 (`SteinIntro.tex:2500`;
`ISSUE-TYPO-4.13`): at $N = 4, n = 1, m = 2$, $\operatorname{Var}(W) = 1/4 \ne -1/8$. -/
theorem not_ex4_13_var_printed :
    ¬ (∀ {N n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {S : Ω → Finset (Fin N)},
        2 ≤ N →
        1 ≤ n →
        n ≤ N →
        1 ≤ m →
        m ≤ N →
        (∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A}) →
        (∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
          P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) →
        let W : Ω → ℝ := fun ω ↦ (((S ω).filter fun j : Fin N ↦ j.1 < n).card : ℝ)
        ProbabilityTheory.variance W P =
          (n : ℝ) * (m : ℝ) * ((N : ℝ) - (n : ℝ)) * ((n : ℝ) - (m : ℝ)) /
            ((N : ℝ) ^ 2 * ((N : ℝ) - 1))) := by
  intro hbad
  let hmN : 2 ≤ 4 := by decide
  let μ₀ : Measure (Fin 4 → Bool) := hypergeomVecMeasure hmN
  let P : Measure (PUnit × (Fin 4 → Bool)) := (Measure.dirac PUnit.unit).prod μ₀
  let S : PUnit × (Fin 4 → Bool) → Finset (Fin 4) := fun ω ↦ boolSupport ω.2
  have hS_meas : ∀ A : Finset (Fin 4), MeasurableSet {ω | S ω = A} :=
    fun A ↦ measurable_snd (show MeasurableSet {v : Fin 4 → Bool | boolSupport v = A} from
      .of_discrete)
  have hP_snd : P.map Prod.snd = μ₀ := Measure.snd_prod
  have hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2,
      P.real {ω | S ω = A} = 1 / ((4 : ℕ).choose 2 : ℝ) := by
    intro A hA
    change P.real (Prod.snd ⁻¹' {v : Fin 4 → Bool | boolSupport v = A}) = _
    rw [← map_measureReal_apply measurable_snd .of_discrete, hP_snd]
    have hset : ({v : Fin 4 → Bool | boolSupport v = A}) = {setToBoolVec A} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      rw [eq_comm, ← setToBoolVec_eq_iff, eq_comm]
    have hv_mem : setToBoolVec A ∈ hypergeomVecSet 4 2 := by
      rw [mem_hypergeomVecSet, boolSupport_setToBoolVec]
      exact (Finset.mem_powersetCard.mp hA).2
    rw [hset, hypergeomVecMeasure_real_singleton hmN, ite_eq_left hv_mem]
  have htrue := (ex4_13_moments_corrected (N := 4) (n := 1) (m := 2) P (S := S)
    (by decide) (by decide) (by decide) hmN hS_meas hS_unif).2 (by decide)
  have hfalse := hbad (N := 4) (n := 1) (m := 2) P (S := S)
    (by decide) (by decide) (by decide) (by decide) hmN hS_meas hS_unif
  have h1 : ProbabilityTheory.variance
      (fun ω ↦ (((S ω).filter fun j : Fin 4 ↦ j.1 < 1).card : ℝ)) P =
      1 / 4 := by
    rw [htrue]
    norm_num
  have h2 : ProbabilityTheory.variance
      (fun ω ↦ (((S ω).filter fun j : Fin 4 ↦ j.1 < 1).card : ℝ)) P =
      -1 / 8 := by
    rw [hfalse]
    norm_num
  linarith

/-- Example 4.13, restricted to $2 \le N$ (`[Hypergeometric distribution]`,
`SteinIntro.tex:2480-2505`). Restricted from $N \ge 1$ because every term of the printed bound at
`SteinIntro.tex:2504` divides by $N - 1$ (`0 / 0` at $N = 1$). -/
theorem ex4_13_restricted
    {N n m : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {S : Ω → Finset (Fin N)} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hN2 : 2 ≤ N) (hn1 : 1 ≤ n) (hnN : n ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N)
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ))
    (hr : (r : ℝ) = (n : ℝ) * (m : ℝ) / (N : ℝ))
    (hZ_meas : AEMeasurable Z P')
    (hZ_law : P'.map Z = poissonLaw r) :
    let W : Ω → ℕ := fun ω ↦ ((S ω).filter fun j : Fin N ↦ j.1 < n).card
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 ((n : ℝ) * (m : ℝ) / (N : ℝ)) *
          ((n : ℝ) / ((N : ℝ) - 1) + (m : ℝ) / ((N : ℝ) - 1) -
            (n : ℝ) * (m : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) - 1 / ((N : ℝ) - 1))) := by
  intro W
  let X : Fin n → Ω → ℕ := fun i ω ↦ if Fin.castLE hnN i ∈ S ω then 1 else 0
  have hW_eq : W = fun ω ↦ ∑ i : Fin n, X i ω := by
    funext ω
    exact redCountSet_eq_sum hnN (S ω)
  have hX_meas : ∀ i : Fin n, Measurable (X i) := fun i ↦
    measurable_comp_finset_of_levelSet hS (fun A ↦ if Fin.castLE hnN i ∈ A then 1 else 0)
  have hX_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1 := fun i ↦
    Filter.Eventually.of_forall fun ω ↦ by by_cases h : Fin.castLE hnN i ∈ S ω <;> simp [X, h]
  let νU : Measure (Fin m) := (@PMF.uniformOfFintype (Fin m) inferInstance ⟨⟨0, hm1⟩⟩).toMeasure
  have : IsProbabilityMeasure νU := PMF.toMeasure.isProbabilityMeasure _
  let V : Ω → Fin N → Bool := fun ω ↦ setToBoolVec (S ω)
  have hV_meas : Measurable V := measurable_comp_finset_of_levelSet hS setToBoolVec
  have hV_law : P.map V = hypergeomVecMeasure hmN :=
    map_setToBoolVec_eq_hypergeomVecMeasure hmN P hS hS_unif
  let Y : (i : Fin n) → Ω × Fin m → {j : Fin n // j ≠ i} → ℕ :=
    fun i p j ↦ if Fin.castLE hnN j.1 ∈ hypergeomStepSet (Fin.castLE hnN i) (S p.1) p.2
      then 1 else 0
  have hY_meas : ∀ i : Fin n, Measurable (Y i) := by
    intro i
    refine Measurable.of_eval fun j ↦ ?_
    have hS_fst : Measurable (fun p : Ω × Fin m ↦ setToBoolVec (S p.1)) :=
      hV_meas.comp measurable_fst
    have hrewrite : (fun p : Ω × Fin m ↦ Y i p j) =
        (fun q : (Fin N → Bool) × Fin m ↦
          if (hypergeomStepVec (Fin.castLE hnN i) q.1 q.2) (Fin.castLE hnN j.1) = true
          then 1 else 0) ∘ (fun p : Ω × Fin m ↦ (V p.1, p.2)) := by
      funext p
      simp [Y, V, hypergeomStepVec]
    rw [hrewrite]
    exact Measurable.of_discrete.comp (hS_fst.prodMk measurable_snd)
  have hY_cond : ∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
      (P.prod νU).map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) := by
    intro i _
    let projRest : (Fin N → Bool) → ({j : Fin n // j ≠ i} → ℕ) :=
      fun v j ↦ if v (Fin.castLE hnN j.1) = true then 1 else 0
    have hYi_eq : Y i = projRest ∘
        (fun q : (Fin N → Bool) × Fin m ↦ hypergeomStepVec (Fin.castLE hnN i) q.1 q.2) ∘
        (fun p : Ω × Fin m ↦ (V p.1, p.2)) := by
      funext p j
      simp [Y, projRest, V, hypergeomStepVec]
    have hprod_map :
        (P.prod νU).map (fun p : Ω × Fin m ↦ (V p.1, p.2)) =
          (hypergeomVecMeasure hmN).prod νU := by
      change (P.prod νU).map (Prod.map V id) = _
      rw [← Measure.map_prod_map P νU hV_meas measurable_id, hV_law, Measure.map_id]
    have hfg_meas : Measurable (fun p : Ω × Fin m ↦ (V p.1, p.2)) :=
      (hV_meas.comp measurable_fst).prodMk measurable_snd
    have hstep_meas :
        Measurable
          (fun q : (Fin N → Bool) × Fin m ↦ hypergeomStepVec (Fin.castLE hnN i) q.1 q.2) :=
      .of_discrete
    have hmap_lhs :
        (P.prod νU).map (Y i) =
          (ProbabilityTheory.cond (hypergeomVecMeasure hmN)
            {v | v (Fin.castLE hnN i) = true}).map projRest := by
      rw [hYi_eq, ← Measure.map_map Measurable.of_discrete (hstep_meas.comp hfg_meas),
        ← Measure.map_map hstep_meas hfg_meas,
        hprod_map, map_hypergeomStepVec_eq_cond hm1 hmN (Fin.castLE hnN i)]
    have hevent_pre : {ω : Ω | X i ω = 1} =
        V ⁻¹' {v : Fin N → Bool | v (Fin.castLE hnN i) = true} := by
      ext ω
      by_cases h : Fin.castLE hnN i ∈ S ω <;> simp [X, V, setToBoolVec, h]
    have hcond_V :
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map V =
          ProbabilityTheory.cond (hypergeomVecMeasure hmN)
            {v | v (Fin.castLE hnN i) = true} := by
      ext E hE
      rw [hevent_pre, Measure.map_apply hV_meas hE,
        ProbabilityTheory.cond_apply (hV_meas .of_discrete),
        ProbabilityTheory.cond_apply .of_discrete, ← hV_law,
        Measure.map_apply hV_meas .of_discrete,
        Measure.map_apply hV_meas (MeasurableSet.of_discrete.inter hE), Set.preimage_inter]
    have hX_rest : (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω) = projRest ∘ V := by
      funext ω j
      simp [projRest, X, V, setToBoolVec]
    rw [hmap_lhs, ← hcond_V, Measure.map_map Measurable.of_discrete hV_meas, ← hX_rest]
  have hY_le : ∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i},
      ∀ᵐ p ∂(P.prod νU), Y i p j ≤ X j.1 p.1 := fun i j ↦
    Filter.Eventually.of_forall fun p ↦
      indicator_hypergeomStepSet_le (Fin.castLE hnN i) (S p.1) p.2
        ((Fin.castLE_injective hnN).ne j.2)
  have mom := ex4_13_moments_corrected P hn1 hnN hm1 hmN hS hS_unif
  have hr_pos : 0 < r := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le hm1 hmN)
    have : (0 : ℝ) < (r : ℝ) := by rw [hr]; positivity
    exact_mod_cast this
  have hlam : (r : ℝ) = ∑ i : Fin n, P.real {ω | X i ω = 1} := by
    have hsum_int :
        (∑ i : Fin n, P.real {ω | X i ω = 1}) = ∫ ω, (W ω : ℝ) ∂P := by
      have hcast_W : (fun ω ↦ (W ω : ℝ)) = fun ω ↦ ∑ i : Fin n, (X i ω : ℝ) := by
        funext ω
        simp [hW_eq]
      rw [hcast_W, integral_finsetSum Finset.univ fun i _ ↦
        integrable_nat_zero_one P (hX_meas i) (hX_zo i)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (integral_nat_zero_one_eq_measureReal P (hX_meas i) (hX_zo i)).symm
    rw [hsum_int, mom.1, hr]
  have htv := tvDist_poisson_le_of_aux_decreasing_coupling P νU P' hX_meas hX_zo hr_pos hlam
    hY_meas hY_cond hY_le hZ_meas hZ_law
  have hW_map : P.map (fun ω ↦ ∑ i : Fin n, X i ω) = P.map W := by rw [hW_eq]
  have hW_var : ProbabilityTheory.variance (fun ω ↦ ((∑ i : Fin n, X i ω : ℕ) : ℝ)) P =
      ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P := by
    congr 1
    funext ω
    rw [congrFun hW_eq ω]
  rw [hW_map, hW_var, mom.2 hN2, hr] at htv
  refine htv.trans (le_of_eq ?_)
  congr 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hN1_pos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  congr 1
  field_simp [hn_pos.ne', hm_pos.ne', hN_pos.ne', hN1_pos.ne']
  ring

/-! ### Section 4: Remark 4.14 (Harper–Pitman Representation and Theorem 4.19 Recovery) -/

/-- Rolle's theorem + Gauss–Lucas on `[-1, 0]`: if `f : ℝ[X]` splits over `ℝ` with all roots in
`[-1, 0]`, then `derivative f` also splits over `ℝ` with all roots in `[-1, 0]`. -/
private theorem splits_and_roots_mem_Icc_derivative {f : ℝ[X]}
    (hf : f.Splits) (hroots : ∀ z ∈ f.roots, z ∈ Set.Icc (-1 : ℝ) 0) :
    (derivative f).Splits ∧ ∀ z ∈ (derivative f).roots, z ∈ Set.Icc (-1 : ℝ) 0 := by
  have hsp : (derivative f).Splits := by
    by_cases hd : f.natDegree = 0
    · rw [derivative_eq_zero.mpr hd]
      exact Splits.zero
    · rw [splits_iff_card_roots]
      have h1 : f.natDegree = f.roots.card := hf.natDegree_eq_card_roots
      have h2 : f.roots.card ≤ (derivative f).roots.card + 1 := card_roots_le_derivative f
      have h3 : (derivative f).natDegree = f.natDegree - 1 := natDegree_derivative f
      have h4 : (derivative f).roots.card ≤ (derivative f).natDegree := card_roots' (derivative f)
      omega
  refine ⟨hsp, fun x hx ↦ ?_⟩
  have hdf_ne : derivative f ≠ 0 := fun h0 ↦ by simp [h0] at hx
  have hf_ne : f ≠ 0 := fun h0 ↦ hdf_ne (by simp [h0])
  have hx_eval : (derivative f).eval x = 0 := (mem_roots hdf_ne).mp hx
  by_cases hfx : f.eval x = 0
  · exact hroots x ((mem_roots hf_ne).mpr hfx)
  · have hsum_eq := hf.eval_derivative_eq_eval_mul_sum hfx
    rw [hx_eval] at hsum_eq
    have hsum_zero : (f.roots.map fun z ↦ 1 / (x - z)).sum = 0 :=
      (mul_eq_zero.mp hsum_eq.symm).resolve_left hfx
    have hdeg_pos : 0 < f.natDegree := Nat.pos_of_ne_zero (derivative_ne_zero.mp hdf_ne)
    have hcard_pos : 0 < f.roots.card := by
      have := hf.natDegree_eq_card_roots
      omega
    obtain ⟨z₀, hz₀⟩ := Multiset.card_pos_iff_exists_mem.mp hcard_pos
    have hms_nonpos : ∀ s : Multiset ℝ, (∀ y ∈ s, y ≤ 0) → s.sum ≤ 0 := by
      intro s
      refine Multiset.induction_on s (by simp) fun a t ih ht ↦ ?_
      rw [Multiset.sum_cons]
      exact add_nonpos (ht a (Multiset.mem_cons_self a t))
        (ih fun y hy ↦ ht y (Multiset.mem_cons_of_mem hy))
    have hms_nonneg : ∀ s : Multiset ℝ, (∀ y ∈ s, 0 ≤ y) → 0 ≤ s.sum := by
      intro s
      refine Multiset.induction_on s (by simp) fun a t ih ht ↦ ?_
      rw [Multiset.sum_cons]
      exact add_nonneg (ht a (Multiset.mem_cons_self a t))
        (ih fun y hy ↦ ht y (Multiset.mem_cons_of_mem hy))
    let s : Multiset ℝ := f.roots.map fun z ↦ 1 / (x - z)
    have hz₀_mem : 1 / (x - z₀) ∈ s := Multiset.mem_map_of_mem _ hz₀
    obtain ⟨m', hm'⟩ := Multiset.exists_cons_of_mem hz₀_mem
    constructor
    · by_contra hlt
      have hlt' : x < -1 := lt_of_not_ge hlt
      have hneg : ∀ y ∈ s, y < 0 := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
        have hz_lo : -1 ≤ z := (hroots z hz).1
        exact div_neg_of_pos_of_neg zero_lt_one (by linarith)
      have hm'_nonpos : m'.sum ≤ 0 := hms_nonpos m' fun y hy ↦
        le_of_lt (hneg y (hm' ▸ Multiset.mem_cons_of_mem hy))
      have hz₀_neg : 1 / (x - z₀) < 0 := hneg _ hz₀_mem
      have hlt_zero : s.sum < 0 := by
        rw [hm', Multiset.sum_cons]
        linarith
      change s.sum = 0 at hsum_zero
      linarith
    · by_contra hgt
      have hgt' : 0 < x := lt_of_not_ge hgt
      have hpos : ∀ y ∈ s, 0 < y := by
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
        have hz_hi : z ≤ 0 := (hroots z hz).2
        exact div_pos zero_lt_one (by linarith)
      have hm'_nonneg : 0 ≤ m'.sum := hms_nonneg m' fun y hy ↦
        le_of_lt (hpos y (hm' ▸ Multiset.mem_cons_of_mem hy))
      have hz₀_pos : 0 < 1 / (x - z₀) := hpos _ hz₀_mem
      have hgt_zero : 0 < s.sum := by
        rw [hm', Multiset.sum_cons]
        linarith
      change s.sum = 0 at hsum_zero
      linarith

private theorem splits_and_roots_mem_Icc_iterate_derivative (k : ℕ) {f : ℝ[X]}
    (hf : f.Splits) (hroots : ∀ z ∈ f.roots, z ∈ Set.Icc (-1 : ℝ) 0) :
    (derivative^[k] f).Splits ∧ ∀ z ∈ (derivative^[k] f).roots, z ∈ Set.Icc (-1 : ℝ) 0 := by
  induction k generalizing f with
  | zero => exact ⟨hf, hroots⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hf', hr'⟩ := splits_and_roots_mem_Icc_derivative hf hroots
    exact ih hf' hr'

private theorem natDegree_and_leadingCoeff_iterate_derivative (k : ℕ) {f : ℝ[X]}
    (hk : k ≤ f.natDegree) :
    (derivative^[k] f).natDegree = f.natDegree - k ∧
      (derivative^[k] f).leadingCoeff = f.leadingCoeff * (f.natDegree.descFactorial k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨hd, hl⟩ := ih (Nat.le_of_succ_le hk)
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · rw [natDegree_derivative, hd]
      omega
    · rw [leadingCoeff_derivative, hl, hd, Nat.descFactorial_succ]
      push_cast
      ring

/-- Vandermonde-style identity: the probability generating polynomial of the hypergeometric
red-ball count splits as a product of $m$ Bernoulli generating factors, hence (since its degree is
at most $n$) as a product of $n$ Bernoulli generating factors. -/
private theorem exists_bernoulli_pgf_eq_hypergeom_pgf
    {N n m : ℕ} (hnN : n ≤ N) (hmN : m ≤ N) :
    ∃ q : Fin n → ℝ,
      (∀ i : Fin n, 0 ≤ q i ∧ q i ≤ 1) ∧
      (∏ i : Fin n, (C (1 - q i) + C (q i) * X)) =
        ∑ k ∈ Finset.range (m + 1),
          C ((n.choose k * (N - n).choose (m - k) : ℝ) / (N.choose m : ℝ)) * X ^ k := by
  let P₀ : ℝ[X] := (X + C 1) ^ n * X ^ (N - n)
  have hP₀_monic : P₀.Monic := (monic_X_add_C 1 |>.pow n).mul (monic_X_pow (N - n))
  have hP₀_deg : P₀.natDegree = N := by
    rw [(monic_X_add_C 1 |>.pow n).natDegree_mul (monic_X_pow (N - n)),
      (monic_X_add_C 1).natDegree_pow, natDegree_X_add_C, mul_one, natDegree_X_pow]
    omega
  have hsplits_pow : ∀ (k : ℕ) {p : ℝ[X]}, p.Splits → (p ^ k).Splits := by
    intro k p hp
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact Splits.mul ih hp
  have hP₀_splits : P₀.Splits :=
    Splits.mul (hsplits_pow n (Splits.X_add_C 1))
      (hsplits_pow (N - n) (by simp))
  have hP₀_roots : ∀ z ∈ P₀.roots, z ∈ Set.Icc (-1 : ℝ) 0 := by
    intro z hz
    rw [roots_mul hP₀_monic.ne_zero, Multiset.mem_add] at hz
    rcases hz with hz1 | hz2
    · by_cases hn0 : n = 0
      · simp [hn0] at hz1
      · rw [roots_pow, Multiset.mem_nsmul] at hz1
        have hz' : z = -1 := by
          have h := (mem_roots (X_add_C_ne_zero (1 : ℝ))).mp hz1.2
          simp at h
          linarith
        subst hz'
        exact ⟨le_rfl, by norm_num⟩
    · by_cases hNn : N - n = 0
      · simp [hNn] at hz2
      · rw [roots_pow, Multiset.mem_nsmul] at hz2
        have hz' : z = 0 := by simpa using hz2.2
        subst hz'
        exact ⟨by norm_num, le_rfl⟩
  let Q : ℝ[X] := derivative^[N - m] P₀
  have hNm_le : N - m ≤ P₀.natDegree := by rw [hP₀_deg]; omega
  obtain ⟨hQ_splits, hQ_roots⟩ :=
    splits_and_roots_mem_Icc_iterate_derivative (N - m) hP₀_splits hP₀_roots
  obtain ⟨hQ_deg, hQ_lead⟩ := natDegree_and_leadingCoeff_iterate_derivative (N - m) hNm_le
  have hQ_deg_m : Q.natDegree = m := by
    dsimp [Q]
    rw [hQ_deg, hP₀_deg]
    omega
  have hQ_lead_val : Q.leadingCoeff = ((N - m).factorial : ℝ) * (N.choose m : ℝ) := by
    dsimp [Q]
    rw [hQ_lead, hP₀_monic.leadingCoeff, one_mul, hP₀_deg,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.choose_symm hmN]
    push_cast
    ring
  have hrcard : Q.roots.card = m := hQ_splits.natDegree_eq_card_roots.symm.trans hQ_deg_m
  let rList : List ℝ := Q.roots.toList
  have hrList_len : rList.length = m := by simp [rList, hrcard]
  let t : Fin m → ℝ := fun j ↦ -rList.get (j.cast hrList_len.symm)
  have ht_bounds : ∀ j : Fin m, 0 ≤ t j ∧ t j ≤ 1 := by
    intro j
    let idx : Fin rList.length := j.cast hrList_len.symm
    have hmem_roots : rList.get idx ∈ Q.roots := Multiset.mem_toList.mp (List.get_mem rList idx)
    obtain ⟨hlo, hhi⟩ := hQ_roots (rList.get idx) hmem_roots
    change 0 ≤ -rList.get idx ∧ -rList.get idx ≤ 1
    exact ⟨by linarith, by linarith⟩
  have hQ_prod : Q = C Q.leadingCoeff * ∏ j : Fin m, (X + C (t j)) := by
    conv_lhs => dsimp [Q]; rw [hQ_splits.eq_prod_roots]
    congr 1
    have hms : Q.roots = ↑rList := (Multiset.coe_toList Q.roots).symm
    have hms_prod : ∀ L : List ℝ,
        (((L : Multiset ℝ).map fun a : ℝ ↦ X - C a)).prod =
          ∏ j : Fin L.length, (X - C (L.get j)) := by
      intro L
      induction L with
      | nil => simp
      | cons a L ih =>
        rw [← Multiset.cons_coe, Multiset.map_cons, Multiset.prod_cons, ih]
        symm
        have hlen : ∏ j : Fin (a :: L).length, (X - C ((a :: L).get j)) =
            ∏ j : Fin (L.length + 1), (X - C ((a :: L).get j)) :=
          Fintype.prod_equiv (finCongr rfl)
            (fun j : Fin (a :: L).length ↦ X - C ((a :: L).get j))
            (fun j : Fin (L.length + 1) ↦ X - C ((a :: L).get j))
            (fun _ ↦ rfl)
        rw [hlen, Fin.prod_univ_succ]
        simp
    rw [hms, hms_prod rList]
    refine Fintype.prod_equiv (finCongr hrList_len) _ _ fun j ↦ ?_
    change X - C (rList.get j) = X + C (-rList.get ((finCongr hrList_len j).cast hrList_len.symm))
    have hidx : (finCongr hrList_len j).cast hrList_len.symm = j := Fin.ext rfl
    rw [hidx, C_neg, sub_eq_add_neg]
  have hQ_leibniz :
      Q = C ((N - m).factorial : ℝ) *
        ∑ k ∈ Finset.range (m + 1),
          C (n.choose k * (N - n).choose (m - k) : ℝ) * ((X + C 1) ^ k * X ^ (m - k)) := by
    dsimp [Q, P₀]
    rw [iterate_derivative_mul]
    have hsum_step :
        (∑ r ∈ Finset.range (N - m + 1),
          (N - m).choose r •
            (derivative^[N - m - r] ((X + C (1 : ℝ)) ^ n) *
              derivative^[r] (X ^ (N - n) : ℝ[X]))) =
        ∑ r ∈ Finset.range (N - m + 1),
          ((N - m).choose r * (n.descFactorial (N - m - r) * (N - n).descFactorial r)) •
            ((X + C (1 : ℝ)) ^ (n - (N - m - r)) * X ^ (N - n - r)) := by
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [iterate_derivative_X_add_pow, iterate_derivative_X_pow_eq_natCast_mul]
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [hsum_step]
    let validR := (Finset.range (N - m + 1)).filter fun r ↦ N - m - r ≤ n ∧ r ≤ N - n
    let validK := (Finset.range (m + 1)).filter fun k ↦ k ≤ n ∧ m - k ≤ N - n
    have htrimR :
        (∑ r ∈ Finset.range (N - m + 1),
          ((N - m).choose r * (n.descFactorial (N - m - r) * (N - n).descFactorial r)) •
            ((X + C (1 : ℝ)) ^ (n - (N - m - r)) * X ^ (N - n - r))) =
        ∑ r ∈ validR,
          ((N - m).choose r * (n.descFactorial (N - m - r) * (N - n).descFactorial r)) •
            ((X + C (1 : ℝ)) ^ (n - (N - m - r)) * X ^ (N - n - r)) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot ↦ ?_).symm
      rw [Finset.mem_filter] at hnot
      by_cases h1 : N - m - r ≤ n
      · have h2 : N - n < r := lt_of_not_ge fun h2' ↦ hnot ⟨hr, h1, h2'⟩
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr h2, mul_zero, mul_zero, zero_smul]
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge h1), zero_mul, mul_zero, zero_smul]
    have htrimK :
        (∑ k ∈ Finset.range (m + 1),
          C (n.choose k * (N - n).choose (m - k) : ℝ) * ((X + C 1) ^ k * X ^ (m - k))) =
        ∑ k ∈ validK,
          C (n.choose k * (N - n).choose (m - k) : ℝ) * ((X + C 1) ^ k * X ^ (m - k)) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun k hk hnot ↦ ?_).symm
      rw [Finset.mem_filter] at hnot
      by_cases h1 : k ≤ n
      · have h2 : N - n < m - k := lt_of_not_ge fun h2' ↦ hnot ⟨hk, h1, h2'⟩
        rw [Nat.choose_eq_zero_of_lt h2, Nat.cast_zero, mul_zero, C_0, zero_mul]
      · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge h1), Nat.cast_zero, zero_mul, C_0, zero_mul]
    rw [htrimR, htrimK, Finset.mul_sum]
    refine Finset.sum_bij (fun r _ ↦ n - (N - m - r)) ?_ ?_ ?_ ?_
    · intro r hr
      obtain ⟨hr_mem, h1, h2⟩ := Finset.mem_filter.mp hr
      have hr_le : r ≤ N - m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr_mem)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩
    · intro r₁ hr₁ r₂ hr₂ heq
      obtain ⟨hr₁_mem, h1₁, _⟩ := Finset.mem_filter.mp hr₁
      obtain ⟨hr₂_mem, h1₂, _⟩ := Finset.mem_filter.mp hr₂
      have hr₁_le : r₁ ≤ N - m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr₁_mem)
      have hr₂_le : r₂ ≤ N - m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr₂_mem)
      omega
    · intro k hk
      obtain ⟨hk_mem, hk1, hk2⟩ := Finset.mem_filter.mp hk
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
      refine ⟨(N - n) - (m - k), Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩, by omega⟩
    · intro r hr
      obtain ⟨hr_mem, h1, h2⟩ := Finset.mem_filter.mp hr
      have hr_le : r ≤ N - m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr_mem)
      set k := n - (N - m - r)
      have hexp : N - n - r = m - k := by omega
      have hkn : n - k = N - m - r := by omega
      have hcomb :
          (N - m).choose r * (n.descFactorial (N - m - r) * (N - n).descFactorial r) =
            (N - m).factorial * (n.choose k * (N - n).choose (m - k)) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
          ← hkn, Nat.choose_symm (by omega : k ≤ n), hkn,
          ← Nat.choose_symm h2, hexp]
        have hfact := Nat.choose_mul_factorial_mul_factorial hr_le
        calc
          (N - m).choose r * (((N - m - r).factorial * n.choose k) *
              (r.factorial * (N - n).choose (m - k)))
              = ((N - m).choose r * r.factorial * (N - m - r).factorial) *
                  (n.choose k * (N - n).choose (m - k)) := by ring
          _ = (N - m).factorial * (n.choose k * (N - n).choose (m - k)) := by rw [hfact]
      rw [hexp, hcomb, nsmul_eq_mul, ← C_eq_natCast]
      push_cast
      simp only [C_mul]
      ring
  let P_bern_m : ℝ[X] := ∏ j : Fin m, (C (1 - t j) + C (t j) * X)
  let P_hyp : ℝ[X] := ∑ k ∈ Finset.range (m + 1),
    C ((n.choose k * (N - n).choose (m - k) : ℝ) / (N.choose m : ℝ)) * X ^ k
  have hpoly_eq : P_bern_m = P_hyp := by
    refine eq_of_infinite_eval_eq P_bern_m P_hyp
      ((Set.Ioi_infinite (1 : ℝ)).mono fun x hx ↦ ?_)
    have hx1 : (0 : ℝ) < x - 1 := sub_pos.mpr hx
    let y : ℝ := (x - 1)⁻¹
    have hlead_pos : (0 : ℝ) < ((N - m).factorial : ℝ) * (N.choose m : ℝ) := by
      have hf : (0 : ℝ) < ((N - m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (N - m)
      have hc : (0 : ℝ) < (N.choose m : ℝ) := by exact_mod_cast Nat.choose_pos hmN
      positivity
    have hlhs :
        (x - 1) ^ m * Q.eval y =
          (((N - m).factorial : ℝ) * (N.choose m : ℝ)) * P_bern_m.eval x := by
      have hxm_prod : (x - 1) ^ m = ∏ _j : Fin m, (x - 1) := by simp
      conv_lhs => rw [hQ_prod, hQ_lead_val]
      rw [eval_mul, eval_C, eval_prod, mul_left_comm ((x - 1) ^ m),
        hxm_prod, ← Finset.prod_mul_distrib]
      congr 1
      dsimp [P_bern_m]
      rw [eval_prod]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp only [eval_add, eval_mul, eval_X, eval_C, y]
      field_simp [hx1.ne']
      ring
    exact mul_left_cancel₀ hlead_pos.ne' (hlhs.symm.trans (by
      conv_lhs => rw [hQ_leibniz]
      rw [eval_mul, eval_C, eval_finsetSum, mul_left_comm ((x - 1) ^ m), Finset.mul_sum,
        Finset.mul_sum]
      dsimp [P_hyp]
      rw [eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hpow_split : (x - 1) ^ m = (x - 1) ^ k * (x - 1) ^ (m - k) := by
        rw [← pow_add, Nat.add_sub_of_le hk_le]
      simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, y]
      have hy1 : (x - 1) * ((x - 1)⁻¹ + 1) = x := by
        field_simp [hx1.ne']
        ring
      have hy0 : (x - 1) * (x - 1)⁻¹ = 1 := mul_inv_cancel₀ hx1.ne'
      have hterm :
          (x - 1) ^ m * (((x - 1)⁻¹ + 1) ^ k * ((x - 1)⁻¹) ^ (m - k)) = x ^ k := by
        rw [hpow_split, ← mul_assoc, mul_right_comm ((x - 1) ^ k), ← mul_pow, hy1,
          mul_assoc, ← mul_pow, hy0, one_pow, mul_one]
      have hchoose_ne : (N.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmN).ne'
      calc
        ((N - m).factorial : ℝ) * ((x - 1) ^ m *
            ((n.choose k * (N - n).choose (m - k) : ℝ) *
              (((x - 1)⁻¹ + 1) ^ k * ((x - 1)⁻¹) ^ (m - k))))
            = ((N - m).factorial : ℝ) * ((n.choose k * (N - n).choose (m - k) : ℝ) *
                ((x - 1) ^ m * (((x - 1)⁻¹ + 1) ^ k * ((x - 1)⁻¹) ^ (m - k)))) := by ring
        _ = ((N - m).factorial : ℝ) *
              ((n.choose k * (N - n).choose (m - k) : ℝ) * x ^ k) := by rw [hterm]
        _ = (((N - m).factorial : ℝ) * (N.choose m : ℝ)) *
              (((n.choose k * (N - n).choose (m - k) : ℝ) / (N.choose m : ℝ)) * x ^ k) := by
            field_simp [hchoose_ne]))
  let posSet : Finset (Fin m) := Finset.univ.filter fun j : Fin m ↦ t j ≠ 0
  have hprod_posSet :
      P_bern_m = ∏ j ∈ posSet, (C (1 - t j) + C (t j) * X) := by
    dsimp [P_bern_m]
    refine (Finset.prod_subset (Finset.filter_subset _ _) fun j _ hj ↦ ?_).symm
    have htj : t j = 0 := by simpa [posSet] using hj
    simp [htj]
  have hfactor_deg : ∀ j ∈ posSet,
      (C (1 - t j) + C (t j) * X).natDegree = 1 ∧ (C (1 - t j) + C (t j) * X) ≠ 0 := by
    intro j hj
    have htj : t j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hdeg : (C (1 - t j) + C (t j) * X).natDegree = 1 := by
      rw [add_comm, natDegree_add_C, natDegree_C_mul htj, natDegree_X]
    refine ⟨hdeg, fun h0 ↦ by rw [h0, natDegree_zero] at hdeg; exact zero_ne_one hdeg⟩
  have hdeg_bern : P_bern_m.natDegree = posSet.card := by
    rw [hprod_posSet, natDegree_prod _ _ fun j hj ↦ (hfactor_deg j hj).2]
    simp_rw [Finset.sum_congr rfl fun j hj ↦ (hfactor_deg j hj).1]
    simp
  have hdeg_hyp : P_hyp.natDegree ≤ n := by
    dsimp [P_hyp]
    refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦ ?_
    by_cases hkn : k ≤ n
    · exact natDegree_C_mul_X_pow_le _ k |>.trans hkn
    · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hkn), Nat.cast_zero, zero_mul, zero_div, C_0,
        zero_mul, natDegree_zero]
      exact Nat.zero_le n
  have hcard_le_n : posSet.card ≤ n := by
    rw [← hdeg_bern, hpoly_eq]
    exact hdeg_hyp
  let ePos : Fin posSet.card ≃ {j : Fin m // j ∈ posSet} :=
    (finCongr (Fintype.card_coe posSet).symm).trans (Fintype.equivFin _).symm
  let q : Fin n → ℝ := fun i ↦ if hi : i.1 < posSet.card then t (ePos ⟨i.1, hi⟩).1 else 0
  refine ⟨q, fun i ↦ ?_, ?_⟩
  · dsimp [q]
    split_ifs with hi
    · exact ht_bounds _
    · exact ⟨le_rfl, zero_le_one⟩
  · change (∏ i : Fin n, (C (1 - q i) + C (q i) * X)) = P_hyp
    rw [← hpoly_eq, hprod_posSet]
    let activeN : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ i.1 < posSet.card
    have htrimN :
        (∏ i : Fin n, (C (1 - q i) + C (q i) * X)) =
          ∏ i ∈ activeN, (C (1 - q i) + C (q i) * X) := by
      refine (Finset.prod_subset (Finset.filter_subset _ _) fun i _ hi ↦ ?_).symm
      have hi' : ¬ i.1 < posSet.card := by simpa [activeN] using hi
      simp [q, hi']
    rw [htrimN]
    refine Finset.prod_bij (fun i hi ↦ (ePos ⟨i.1, (Finset.mem_filter.mp hi).2⟩).1) ?_ ?_ ?_ ?_
    · intro i hi
      exact (ePos ⟨i.1, (Finset.mem_filter.mp hi).2⟩).2
    · intro i₁ hi₁ i₂ hi₂ heq
      have hsub : ePos ⟨i₁.1, (Finset.mem_filter.mp hi₁).2⟩ =
          ePos ⟨i₂.1, (Finset.mem_filter.mp hi₂).2⟩ := Subtype.ext heq
      have hfin := ePos.injective hsub
      exact Fin.ext (Fin.mk.inj hfin)
    · intro j hj
      let k := ePos.symm ⟨j, hj⟩
      refine ⟨⟨k.1, lt_of_lt_of_le k.2 hcard_le_n⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.2⟩, ?_⟩
      simp [k]
    · intro i hi
      have hi' : i.1 < posSet.card := (Finset.mem_filter.mp hi).2
      simp [q, hi']

private theorem coeff_prod_bernoulli_pgf {n : ℕ} (q : Fin n → ℝ) (d : ℕ) :
    (∏ i : Fin n, (C (1 - q i) + C (q i) * X)).coeff d =
      ∑ u : Fin n → Bool,
        if (∑ i : Fin n, if u i = true then 1 else 0) = d then
          ∏ i : Fin n, (if u i = true then q i else 1 - q i)
        else 0 := by
  induction n generalizing d with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty]
    have huniq : (Finset.univ : Finset (Fin 0 → Bool)) = {fun i ↦ i.elim0} := by
      ext u
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [huniq, Finset.sum_singleton]
    cases d with
    | zero => simp
    | succ d' => simp [coeff_one]
  | succ n ih =>
    let q' : Fin n → ℝ := fun i ↦ q i.succ
    let P_tail : ℝ[X] := ∏ i : Fin n, (C (1 - q' i) + C (q' i) * X)
    rw [Fin.prod_univ_succ]
    change ((C (1 - q 0) + C (q 0) * X) * P_tail).coeff d = _
    let eqv : Bool × (Fin n → Bool) ≃ (Fin (n + 1) → Bool) :=
      { toFun := fun p ↦ Fin.cons p.1 p.2
        invFun := fun u ↦ (u 0, Fin.tail u)
        left_inv := fun p ↦ by
          ext
          · simp
          · simp
        right_inv := fun u ↦ Fin.cons_self_tail u }
    rw [← eqv.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    have hcons_sum : ∀ (b : Bool) (u' : Fin n → Bool),
        (∑ i : Fin (n + 1), if eqv (b, u') i = true then 1 else 0) =
          (if b = true then 1 else 0) + ∑ i : Fin n, if u' i = true then 1 else 0 := by
      intro b u'
      rw [Fin.sum_univ_succ]
      simp [eqv]
    have hcons_prod : ∀ (b : Bool) (u' : Fin n → Bool),
        (∏ i : Fin (n + 1), if eqv (b, u') i = true then q i else 1 - q i) =
          (if b = true then q 0 else 1 - q 0) *
            ∏ i : Fin n, (if u' i = true then q' i else 1 - q' i) := by
      intro b u'
      rw [Fin.prod_univ_succ]
      simp [eqv, q']
    simp_rw [hcons_sum, hcons_prod]
    simp only [↓reduceIte, Bool.false_eq_true, zero_add]
    rw [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_C_mul]
    cases d with
    | zero =>
      rw [coeff_X_mul_zero, mul_zero, add_zero, ih q' 0, Finset.mul_sum]
      have htrue_zero :
          (∑ x : Fin n → Bool,
            if 1 + (∑ i : Fin n, if x i = true then 1 else 0) = 0 then
              q 0 * ∏ i : Fin n, (if x i = true then q' i else 1 - q' i)
            else 0) = 0 := by
        refine Finset.sum_eq_zero fun x _ ↦ ?_
        have hne : 1 + (∑ i : Fin n, if x i = true then 1 else 0) ≠ 0 := by omega
        exact ite_eq_right hne
      rw [htrue_zero, zero_add]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [mul_ite, mul_zero]
    | succ d' =>
      rw [coeff_X_mul, ih q' (d' + 1), ih q' d', add_comm, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [mul_ite, mul_zero]
        split_ifs with h1 h2
        · rfl
        · omega
        · omega
        · rfl
      · refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [mul_ite, mul_zero]

private theorem card_hypergeomVecSet_redCount {N n m : ℕ} (hnN : n ≤ N) (d : ℕ) :
    ((hypergeomVecSet N m).filter
        fun v ↦ (∑ i : Fin n, if v (Fin.castLE hnN i) = true then 1 else 0) = d).card =
      if d ≤ m then n.choose d * (N - n).choose (m - d) else 0 := by
  classical
  by_cases hdm : d ≤ m
  · rw [ite_eq_left hdm]
    let redSet : Finset (Fin N) := Finset.univ.filter fun j : Fin N ↦ j.1 < n
    let blueSet : Finset (Fin N) := Finset.univ \ redSet
    have hred_card : redSet.card = n := by
      have hmap : redSet = (Finset.univ : Finset (Fin n)).map
          ⟨Fin.castLE hnN, Fin.castLE_injective hnN⟩ := by
        ext j
        simp only [redSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Function.Embedding.coeFn_mk]
        exact ⟨fun hj ↦ ⟨⟨j.1, hj⟩, Fin.ext rfl⟩, by rintro ⟨i, rfl⟩; exact i.2⟩
      rw [hmap, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hblue_card : blueSet.card = N - n := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ redSet),
        Finset.card_univ, Fintype.card_fin, hred_card]
    let lhsSet := (hypergeomVecSet N m).filter
      fun v ↦ (∑ i : Fin n, if v (Fin.castLE hnN i) = true then 1 else 0) = d
    let rhsSet := redSet.powersetCard d ×ˢ blueSet.powersetCard (m - d)
    have hcard_rhs : rhsSet.card = n.choose d * (N - n).choose (m - d) := by
      rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
        hred_card, hblue_card]
    rw [← hcard_rhs]
    refine Finset.card_bij
      (fun v _ ↦ (boolSupport v ∩ redSet, boolSupport v \ redSet)) ?_ ?_ ?_
    · intro v hv
      obtain ⟨hv_m, hv_d⟩ := Finset.mem_filter.mp hv
      have hA_card : (boolSupport v).card = m := mem_hypergeomVecSet.mp hv_m
      have hinter_eq : boolSupport v ∩ redSet =
          (boolSupport v).filter (fun j : Fin N ↦ j.1 < n) := by
        ext j
        simp [redSet]
      have hinter_card : (boolSupport v ∩ redSet).card = d := by
        rw [hinter_eq, redCountSet_eq_sum hnN]
        simpa [mem_boolSupport] using hv_d
      have hsdiff_sub : boolSupport v \ redSet ⊆ blueSet := by
        intro j hj
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
      have hsdiff_card : (boolSupport v \ redSet).card = m - d := by
        have hpart := Finset.card_inter_add_card_sdiff (boolSupport v) redSet
        omega
      exact Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hinter_card⟩,
          Finset.mem_powersetCard.mpr ⟨hsdiff_sub, hsdiff_card⟩⟩
    · intro v₁ _ v₂ _ heq
      rcases Prod.mk.inj heq with ⟨h1, h2⟩
      have hsup : boolSupport v₁ = boolSupport v₂ := by
        ext j
        have h1j := Finset.ext_iff.mp h1 j
        have h2j := Finset.ext_iff.mp h2 j
        by_cases hj : j ∈ redSet
        · simpa [hj] using h1j
        · simpa [hj] using h2j
      rw [← setToBoolVec_boolSupport v₁, ← setToBoolVec_boolSupport v₂, hsup]
    · intro ⟨R, B⟩ hRB
      obtain ⟨hR, hB⟩ := Finset.mem_product.mp hRB
      obtain ⟨hR_sub, hR_card⟩ := Finset.mem_powersetCard.mp hR
      obtain ⟨hB_sub, hB_card⟩ := Finset.mem_powersetCard.mp hB
      have hdisj : Disjoint R B := by
        refine Finset.disjoint_left.mpr fun j hjR hjB ↦ ?_
        exact (Finset.mem_sdiff.mp (hB_sub hjB)).2 (hR_sub hjR)
      let v := setToBoolVec (R ∪ B)
      have hv_sup : boolSupport v = R ∪ B := boolSupport_setToBoolVec (R ∪ B)
      have hRB_inter : (R ∪ B) ∩ redSet = R := by
        ext j
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hjR | hjB, hj_red⟩
          · exact hjR
          · exact False.elim ((Finset.mem_sdiff.mp (hB_sub hjB)).2 hj_red)
        · intro hjR
          exact ⟨Or.inl hjR, hR_sub hjR⟩
      have hRB_sdiff : (R ∪ B) \ redSet = B := by
        ext j
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hjR | hjB, hj_nred⟩
          · exact False.elim (hj_nred (hR_sub hjR))
          · exact hjB
        · intro hjB
          exact ⟨Or.inr hjB, (Finset.mem_sdiff.mp (hB_sub hjB)).2⟩
      refine ⟨v, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [mem_hypergeomVecSet, hv_sup, Finset.card_union_of_disjoint hdisj, hR_card, hB_card]
        omega
      · have hfilter_eq : (R ∪ B).filter (fun j : Fin N ↦ j.1 < n) = (R ∪ B) ∩ redSet := by
          ext j
          simp [redSet]
        have hsum_eq := (redCountSet_eq_sum hnN (R ∪ B)).symm
        simpa [v, setToBoolVec, hfilter_eq, hRB_inter, hR_card] using hsum_eq
      · rw [hv_sup, hRB_inter, hRB_sdiff]
  · rw [ite_eq_right hdm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv hd_eq
    have hA_card : (boolSupport v).card = m := mem_hypergeomVecSet.mp hv
    have hle : (∑ i : Fin n, if v (Fin.castLE hnN i) = true then 1 else 0) ≤ m := by
      have h1 : (∑ i : Fin n, if v (Fin.castLE hnN i) = true then 1 else 0) =
          ((boolSupport v).filter fun j : Fin N ↦ j.1 < n).card := by
        simpa [mem_boolSupport] using (redCountSet_eq_sum hnN (boolSupport v)).symm
      rw [h1, ← hA_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    exact hdm (hd_eq ▸ hle)

private theorem nat_measure_eq_of_real_singleton_eq (μ₁ μ₂ : Measure ℕ)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : ∀ d : ℕ, μ₁.real {d} = μ₂.real {d}) :
    μ₁ = μ₂ := by
  ext S _
  have hS : S = ⋃ d ∈ S, ({d} : Set ℕ) := by
    ext d
    simp
  have hdisj : S.PairwiseDisjoint (fun d : ℕ ↦ ({d} : Set ℕ)) := fun d₁ _ d₂ _ hne ↦
    Set.disjoint_singleton.mpr hne
  rw [hS, measure_biUnion (Set.to_countable S) hdisj (fun _ _ ↦ .of_discrete),
    measure_biUnion (Set.to_countable S) hdisj (fun _ _ ↦ .of_discrete)]
  refine tsum_congr fun d ↦ ?_
  rw [← ofReal_measureReal, ← ofReal_measureReal, h d.1]

/-- Remark 4.14 (`SteinIntro.tex:2506-2510`, proving from scratch the Harper–Pitman representation
cited from `[pit97]`, together with Theorem 4.19 recovery `G4-2`): for any $1 \le n \le N$ and
$1 \le m \le N$, the hypergeometric red-ball count $W$ has the same distribution as
$\sum_{i=1}^n B_i$ for independent $\{0, 1\}$-indicators $B_1, \dots, B_n$, and for $2 \le N$
applying Theorem 4.19 directly to $(B_1, \dots, B_n)$ recovers the Example 4.13 bound. -/
theorem rem4_14
    {N n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)}
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N)
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) :
    let W : Ω → ℕ := fun ω ↦ ((S ω).filter fun j : Fin N ↦ j.1 < n).card
    ∃ (Ωb : Type) (_ : MeasurableSpace Ωb) (Pb : Measure Ωb) (_ : IsProbabilityMeasure Pb)
      (B : Fin n → Ωb → ℕ),
      (∀ i : Fin n, Measurable (B i)) ∧
      (∀ i : Fin n, ∀ᵐ ωb ∂Pb, B i ωb = 0 ∨ B i ωb = 1) ∧
      ProbabilityTheory.iIndepFun B Pb ∧
      Pb.map (fun ωb ↦ ∑ i : Fin n, B i ωb) = P.map W ∧
      (∀ (r : ℝ≥0), 2 ≤ N → (r : ℝ) = (n : ℝ) * (m : ℝ) / (N : ℝ) →
        tvDist (Pb.map (fun ωb ↦ ∑ i : Fin n, B i ωb)) (poissonLaw r) ≤
          ENNReal.ofReal
            (min 1 ((n : ℝ) * (m : ℝ) / (N : ℝ)) *
              ((n : ℝ) / ((N : ℝ) - 1) + (m : ℝ) / ((N : ℝ) - 1) -
                (n : ℝ) * (m : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) - 1 / ((N : ℝ) - 1)))) := by
  classical
  intro W
  obtain ⟨q, hq_bounds, hpgf_eq⟩ := exists_bernoulli_pgf_eq_hypergeom_pgf hnN hmN
  let pmf_i : Fin n → PMF Bool := fun i ↦
    ⟨fun b ↦ ENNReal.ofReal (if b = true then q i else 1 - q i), by
      suffices (∑ b : Bool, ENNReal.ofReal (if b = true then q i else 1 - q i)) = 1 from
        this ▸ hasSum_fintype _
      rw [Fintype.sum_bool]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← ENNReal.ofReal_add (hq_bounds i).1 (by linarith [(hq_bounds i).2]),
        add_sub_cancel, ENNReal.ofReal_one]⟩
  let μ_i : Fin n → Measure Bool := fun i ↦ (pmf_i i).toMeasure
  let Pb : Measure (Fin n → Bool) := Measure.pi μ_i
  let B : Fin n → (Fin n → Bool) → ℕ := fun i u ↦ if u i = true then 1 else 0
  have hB_meas : ∀ i : Fin n, Measurable (B i) :=
    fun i ↦ (Measurable.of_discrete (f := fun b : Bool ↦ if b = true then 1 else 0)).comp
      (measurable_pi_apply i)
  have hB_zo : ∀ i : Fin n, ∀ᵐ u ∂Pb, B i u = 0 ∨ B i u = 1 := fun i ↦
    Filter.Eventually.of_forall fun u ↦ by by_cases h : u i = true <;> simp [B, h]
  have hcoord_indep :
      ProbabilityTheory.iIndepFun (fun (i : Fin n) (u : Fin n → Bool) ↦ u i) Pb := by
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro T sets _
    have hlhs :
        (⋂ i ∈ T, (fun u : Fin n → Bool ↦ u i) ⁻¹' sets i) =
          Set.univ.pi (fun i : Fin n ↦ if i ∈ T then sets i else Set.univ) := by
      ext u
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      refine ⟨fun h i ↦ ?_, fun h i hi ↦ by simpa [hi] using h i⟩
      by_cases hi : i ∈ T <;> simp [hi, h]
    rw [hlhs, Measure.pi_pi]
    have hsingle : ∀ i ∈ T,
        Pb ((fun u : Fin n → Bool ↦ u i) ⁻¹' sets i) = μ_i i (sets i) := by
      intro i _
      have hpre : (fun u : Fin n → Bool ↦ u i) ⁻¹' sets i =
          Set.univ.pi (fun j : Fin n ↦ if j = i then sets i else Set.univ) := by
        ext u
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
        refine ⟨fun h j ↦ ?_, fun h ↦ by simpa using h i⟩
        by_cases hj : j = i
        · subst hj; simpa using h
        · simp [hj]
      rw [hpre, Measure.pi_pi]
      have hprod :
          (∏ j : Fin n, μ_i j (if j = i then sets i else Set.univ)) =
            μ_i i (sets i) * ∏ j ∈ Finset.univ.erase i, (1 : ℝ≥0∞) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        congr 1
        · simp
        · refine Finset.prod_congr rfl fun j hj ↦ ?_
          have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
          rw [ite_eq_right hj_ne, measure_univ]
      rw [hprod, Finset.prod_const_one, mul_one]
    rw [Finset.prod_congr rfl hsingle]
    have hsplit :
        (∏ i : Fin n, μ_i i (if i ∈ T then sets i else Set.univ)) =
          (∏ i ∈ T, μ_i i (sets i)) * ∏ i ∈ Finset.univ \ T, (1 : ℝ≥0∞) := by
      rw [← Finset.prod_sdiff (Finset.subset_univ T), mul_comm]
      congr 1
      · refine Finset.prod_congr rfl fun i hi ↦ ?_
        simp [hi]
      · refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hi_not : i ∉ T := (Finset.mem_sdiff.mp hi).2
        rw [ite_eq_right hi_not, measure_univ]
    rw [hsplit, Finset.prod_const_one, mul_one]
  have hB_indep : ProbabilityTheory.iIndepFun B Pb :=
    hcoord_indep.comp (fun _ (b : Bool) ↦ if b = true then (1 : ℕ) else 0)
      (fun _ ↦ .of_discrete)
  have hPb_singleton : ∀ u : Fin n → Bool,
      Pb.real {u} = ∏ i : Fin n, (if u i = true then q i else 1 - q i) := by
    intro u
    have hset : ({u} : Set (Fin n → Bool)) = Set.univ.pi (fun i ↦ {u i}) := by
      ext v
      simp [funext_iff]
    rw [measureReal_def, hset, Measure.pi_pi, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    change (μ_i i).real {u i} = _
    rw [measureReal_def, PMF.toMeasure_apply_singleton (pmf_i i) (u i) .of_discrete]
    change (ENNReal.ofReal (if u i = true then q i else 1 - q i)).toReal = _
    exact ENNReal.toReal_ofReal (by split_ifs <;> linarith [(hq_bounds i).1, (hq_bounds i).2])
  have hW_meas : Measurable W :=
    measurable_comp_finset_of_levelSet hS
      (fun A : Finset (Fin N) ↦ (A.filter fun j : Fin N ↦ j.1 < n).card)
  have hBsum_meas : Measurable (fun u : Fin n → Bool ↦ ∑ i : Fin n, B i u) :=
    Finset.measurable_fun_sum Finset.univ fun i _ ↦ hB_meas i
  have hlaw_eq : Pb.map (fun u ↦ ∑ i : Fin n, B i u) = P.map W := by
    have : IsProbabilityMeasure (Pb.map (fun u ↦ ∑ i : Fin n, B i u)) :=
      (Measure.isProbabilityMeasure_map_iff hBsum_meas.aemeasurable).mpr inferInstance
    have : IsProbabilityMeasure (P.map W) :=
      (Measure.isProbabilityMeasure_map_iff hW_meas.aemeasurable).mpr inferInstance
    refine nat_measure_eq_of_real_singleton_eq _ _ fun d ↦ ?_
    have hlhs :
        (Pb.map (fun u ↦ ∑ i : Fin n, B i u)).real {d} =
          (∏ i : Fin n, (C (1 - q i) + C (q i) * X)).coeff d := by
      rw [measureReal_def,
        measure_map_singleton_fintype Pb (fun u ↦ ∑ i : Fin n, B i u) d,
        ENNReal.toReal_sum fun u _ ↦ measure_ne_top Pb {u},
        coeff_prod_bernoulli_pgf q d]
      have hfilter_sum :
          (∑ u ∈ Finset.univ.filter (fun u : Fin n → Bool ↦ (∑ i : Fin n, B i u) = d),
            Pb.real {u}) =
          ∑ u : Fin n → Bool,
            if (∑ i : Fin n, if u i = true then 1 else 0) = d then
              ∏ i : Fin n, (if u i = true then q i else 1 - q i)
            else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        by_cases hd : (∑ i : Fin n, if u i = true then 1 else 0) = d <;>
          simp [B, hd, hPb_singleton]
      exact hfilter_sum
    have hrhs :
        (P.map W).real {d} =
          (∑ k ∈ Finset.range (m + 1),
            C ((n.choose k * (N - n).choose (m - k) : ℝ) / (N.choose m : ℝ)) * X ^ k).coeff d := by
      let V : Ω → Fin N → Bool := fun ω ↦ setToBoolVec (S ω)
      have hV_meas : Measurable V := measurable_comp_finset_of_levelSet hS setToBoolVec
      have hV_law : P.map V = hypergeomVecMeasure hmN :=
        map_setToBoolVec_eq_hypergeomVecMeasure hmN P hS hS_unif
      let W_vec : (Fin N → Bool) → ℕ :=
        fun v ↦ ∑ i : Fin n, if v (Fin.castLE hnN i) = true then 1 else 0
      have hW_comp : W = W_vec ∘ V := by
        funext ω
        change ((S ω).filter fun j : Fin N ↦ j.1 < n).card = _
        rw [redCountSet_eq_sum hnN (S ω)]
        simp [W_vec, V, setToBoolVec]
      have hmap_W : P.map W = (hypergeomVecMeasure hmN).map W_vec := by
        rw [hW_comp, ← Measure.map_map Measurable.of_discrete hV_meas, hV_law]
      rw [hmap_W, measureReal_def,
        measure_map_singleton_fintype (hypergeomVecMeasure hmN) W_vec d,
        ENNReal.toReal_sum fun v _ ↦ measure_ne_top _ {v}]
      let filt := (hypergeomVecSet N m).filter fun v ↦ W_vec v = d
      have htrim :
          (∑ v ∈ Finset.univ.filter (fun v : Fin N → Bool ↦ W_vec v = d),
            (hypergeomVecMeasure hmN).real {v}) =
          ∑ v ∈ filt, (1 / (N.choose m : ℝ)) := by
        have hsub : filt ⊆ Finset.univ.filter (fun v : Fin N → Bool ↦ W_vec v = d) := by
          intro v hv
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun v hv ↦ ?_
          have hv_m : v ∈ hypergeomVecSet N m := (Finset.mem_filter.mp hv).1
          rw [hypergeomVecMeasure_real_singleton hmN, ite_eq_left hv_m]
        · intro v hv_all hnot
          have hv_d : W_vec v = d := (Finset.mem_filter.mp hv_all).2
          have hv_not : v ∉ hypergeomVecSet N m := fun hv_m ↦
            hnot (Finset.mem_filter.mpr ⟨hv_m, hv_d⟩)
          rw [hypergeomVecMeasure_real_singleton hmN, ite_eq_right hv_not]
      have hreal_sum :
          (∑ v ∈ Finset.univ.filter (fun v : Fin N → Bool ↦ W_vec v = d),
            ((hypergeomVecMeasure hmN) {v}).toReal) =
          (∑ v ∈ Finset.univ.filter (fun v : Fin N → Bool ↦ W_vec v = d),
            (hypergeomVecMeasure hmN).real {v}) := rfl
      rw [hreal_sum, htrim, Finset.sum_const, nsmul_eq_mul, mul_one_div]
      have hcard_filt : filt.card =
          if d ≤ m then n.choose d * (N - n).choose (m - d) else 0 :=
        card_hypergeomVecSet_redCount hnN d
      rw [hcard_filt, finsetSum_coeff]
      simp_rw [coeff_C_mul_X_pow]
      by_cases hdm : d ≤ m
      · have hd_mem : d ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hdm)
        rw [ite_eq_left hdm, Finset.sum_eq_single d]
        · simp
        · intro k _ hkd
          exact ite_eq_right hkd.symm
        · intro hd_not
          exact False.elim (hd_not hd_mem)
      · rw [ite_eq_right hdm, Nat.cast_zero, zero_div]
        refine (Finset.sum_eq_zero fun k hk ↦ ?_).symm
        have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hdk : d ≠ k := by omega
        exact ite_eq_right hdk
    rw [hlhs, hrhs, hpgf_eq]
  refine ⟨Fin n → Bool, inferInstance, Pb, inferInstance, B, hB_meas, hB_zo, hB_indep, hlaw_eq,
    fun r hN2 hr ↦ ?_⟩
  -- Apply Theorem 4.19 directly to the independent Bernoulli indicators `(B i)` (`G4-2`)
  let Q_unit : Measure Unit := Measure.dirac ()
  let Y : (i : Fin n) → (Fin n → Bool) × Unit → {j : Fin n // j ≠ i} → ℕ :=
    fun i p j ↦ B j.1 p.1
  have hY_meas : ∀ i : Fin n, Measurable (Y i) :=
    fun i ↦ Measurable.of_eval fun j ↦ (hB_meas j.1).comp measurable_fst
  have hY_le : ∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i},
      ∀ᵐ p ∂(Pb.prod Q_unit), Y i p j ≤ B j.1 p.1 :=
    fun _ _ ↦ Filter.Eventually.of_forall fun _ ↦ le_rfl
  have hY_cond : ∀ i : Fin n, 0 < Pb.real {u | B i u = 1} →
      (Pb.prod Q_unit).map (Y i) =
        (ProbabilityTheory.cond Pb {u | B i u = 1}).map
          (fun u (j : {j : Fin n // j ≠ i}) ↦ B j.1 u) := by
    intro i hi_pos
    have hPb_ne : Pb {u | B i u = 1} ≠ 0 := by
      intro h0
      rw [measureReal_def, h0, ENNReal.toReal_zero] at hi_pos
      exact lt_irrefl 0 hi_pos
    let projBool : (Fin n → Bool) → ({j : Fin n // j ≠ i} → Bool) := fun u j ↦ u j.1
    let toNat : ({j : Fin n // j ≠ i} → Bool) → ({j : Fin n // j ≠ i} → ℕ) :=
      fun g j ↦ if g j = true then 1 else 0
    have hproj_meas : Measurable projBool :=
      Measurable.of_eval fun j ↦ measurable_pi_apply j.1
    have htoNat_meas : Measurable toNat :=
      Measurable.of_eval fun j ↦
        (Measurable.of_discrete (f := fun b : Bool ↦ if b = true then 1 else 0)).comp
          (measurable_pi_apply j)
    have hbool_eq :
        Pb.map projBool = (ProbabilityTheory.cond Pb {u | B i u = 1}).map projBool := by
      refine measure_ext_of_singleton_fintype fun g ↦ ?_
      have hg_meas : MeasurableSet ({g} : Set ({j : Fin n // j ≠ i} → Bool)) := by
        have h1 : ({g} : Set ({j : Fin n // j ≠ i} → Bool)) =
            Set.univ.pi (fun j ↦ {g j}) := by
          ext g'
          simp [funext_iff]
        rw [h1]
        exact MeasurableSet.univ_pi fun _ ↦ .of_discrete
      have hBi_meas : MeasurableSet {u : Fin n → Bool | B i u = 1} :=
        hB_meas i (measurableSet_singleton 1)
      rw [Measure.map_apply hproj_meas hg_meas,
        Measure.map_apply hproj_meas hg_meas,
        ProbabilityTheory.cond_apply hBi_meas]
      let Ev_i : Set (Fin n → Bool) := {u | B i u = 1}
      let Ev_g : Set (Fin n → Bool) := projBool ⁻¹' {g}
      change Pb Ev_g = (Pb Ev_i)⁻¹ * Pb (Ev_i ∩ Ev_g)
      let sets : Fin n → Set Bool :=
        fun k ↦ if hk : k = i then {true} else {g ⟨k, hk⟩}
      have hinter_eq :
          Ev_i ∩ Ev_g = ⋂ k ∈ (Finset.univ : Finset (Fin n)), (fun u ↦ u k) ⁻¹' sets k := by
        ext u
        simp only [Ev_i, Ev_g, projBool, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
          Set.mem_singleton_iff, funext_iff, Set.mem_iInter, Finset.mem_univ, forall_const]
        constructor
        · rintro ⟨hi_u, hg_u⟩ k
          by_cases hk : k = i
          · subst hk
            have : u k = true := by
              by_cases h : u k = true <;> simp [B, h] at hi_u
              exact h
            simp [sets, this]
          · simpa [sets, hk] using hg_u ⟨k, hk⟩
        · intro h
          refine ⟨?_, fun j ↦ ?_⟩
          · have hi_u : u i = true := by simpa [sets] using h i
            simp [B, hi_u]
          · simpa [sets, j.2] using h j.1
      have hg_eq :
          Ev_g = ⋂ k ∈ Finset.univ.erase i, (fun u ↦ u k) ⁻¹' sets k := by
        ext u
        simp only [Ev_g, projBool, Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
          Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true]
        exact ⟨fun hg_u k hk ↦ by simpa [sets, hk] using hg_u ⟨k, hk⟩,
          fun h j ↦ by simpa [sets, j.2] using h j.1 j.2⟩
      have hi_eq : Ev_i = (fun u ↦ u i) ⁻¹' sets i := by
        ext u
        by_cases h : u i = true <;> simp [Ev_i, B, sets, h]
      have hind_all := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp
        hcoord_indep) Finset.univ (fun _ _ ↦ .of_discrete) (sets := sets)
      have hind_er := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp
        hcoord_indep) (Finset.univ.erase i) (fun _ _ ↦ .of_discrete) (sets := sets)
      rw [hinter_eq, hind_all, hg_eq, hind_er,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ← hi_eq,
        ← mul_assoc, ENNReal.inv_mul_cancel hPb_ne (measure_ne_top Pb Ev_i), one_mul]
    have hlhs_map : (Pb.prod Q_unit).map (Y i) = (Pb.map projBool).map toNat := by
      have hcomp : Y i = toNat ∘ projBool ∘ Prod.fst := rfl
      have hfst : (Pb.prod Q_unit).map Prod.fst = Pb := Measure.fst_prod
      rw [hcomp, ← Measure.map_map htoNat_meas (hproj_meas.comp measurable_fst),
        ← Measure.map_map hproj_meas measurable_fst, hfst]
    have hrhs_map :
        (ProbabilityTheory.cond Pb {u | B i u = 1}).map
          (fun u (j : {j : Fin n // j ≠ i}) ↦ B j.1 u) =
        ((ProbabilityTheory.cond Pb {u | B i u = 1}).map projBool).map toNat := by
      have hcomp : (fun u (j : {j : Fin n // j ≠ i}) ↦ B j.1 u) = toNat ∘ projBool := rfl
      rw [hcomp, Measure.map_map htoNat_meas hproj_meas]
    rw [hlhs_map, hrhs_map, hbool_eq]
  have mom := ex4_13_moments_corrected P hn1 hnN hm1 hmN hS hS_unif
  have hr_pos : 0 < r := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le hm1 hmN)
    have : (0 : ℝ) < (r : ℝ) := by rw [hr]; positivity
    exact_mod_cast this
  have hmean_B :
      (∑ i : Fin n, Pb.real {u | B i u = 1}) = ∫ ω, (W ω : ℝ) ∂P := by
    have hlhs_int :
        (∑ i : Fin n, Pb.real {u | B i u = 1}) =
          ∫ x : ℕ, (x : ℝ) ∂(Pb.map (fun u ↦ ∑ i : Fin n, B i u)) := by
      rw [integral_map hBsum_meas.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
      have hcast_sum : (fun u ↦ ((∑ i : Fin n, B i u : ℕ) : ℝ)) =
          fun u ↦ ∑ i : Fin n, (B i u : ℝ) := by
        funext u
        simp
      rw [hcast_sum, integral_finsetSum Finset.univ fun i _ ↦
        integrable_nat_zero_one Pb (hB_meas i) (hB_zo i)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact (integral_nat_zero_one_eq_measureReal Pb (hB_meas i) (hB_zo i)).symm
    rw [hlhs_int, hlaw_eq, integral_map hW_meas.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable]
  have hlam : (r : ℝ) = ∑ i : Fin n, Pb.real {u | B i u = 1} := by
    rw [hmean_B, mom.1, hr]
  have htv := tvDist_poisson_le_of_aux_decreasing_coupling Pb Q_unit (poissonLaw r)
    hB_meas hB_zo hr_pos hlam hY_meas hY_cond hY_le aemeasurable_id Measure.map_id
  rw [Measure.map_id] at htv
  have hvar_B :
      ProbabilityTheory.variance (fun u ↦ ((∑ i : Fin n, B i u : ℕ) : ℝ)) Pb =
        ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P := by
    have h1 :
        ProbabilityTheory.variance (fun x : ℕ ↦ (x : ℝ))
          (Pb.map (fun u ↦ ∑ i : Fin n, B i u)) =
        ProbabilityTheory.variance (fun u ↦ ((∑ i : Fin n, B i u : ℕ) : ℝ)) Pb :=
      ProbabilityTheory.variance_map (X := fun x : ℕ ↦ (x : ℝ))
        (Y := fun u ↦ ∑ i : Fin n, B i u)
        Measurable.of_discrete.aemeasurable hBsum_meas.aemeasurable
    have h2 :
        ProbabilityTheory.variance (fun x : ℕ ↦ (x : ℝ)) (P.map W) =
          ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P :=
      ProbabilityTheory.variance_map (X := fun x : ℕ ↦ (x : ℝ)) (Y := W)
        Measurable.of_discrete.aemeasurable hW_meas.aemeasurable
    rw [← h1, hlaw_eq, h2]
  rw [hvar_B, mom.2 hN2, hr] at htv
  refine htv.trans (le_of_eq ?_)
  congr 1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  have hN1_pos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith
  congr 1
  field_simp [hn_pos.ne', hm_pos.ne', hN_pos.ne', hN1_pos.ne']
  ring

end SteinMethod

