/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Negative.Basic

/-!
# Hypergeometric Vector Space (`Formalization.PoissonSizeBias.Negative.Defs`)

Canonical representation of uniform size-`m` subsets of `Fin N` as `{0, 1}`-boolean vectors
`Fin N → Bool` with support of cardinality `m`, together with permutation invariance, pushforward
bridges from arbitrary `S : Ω → Finset (Fin N)`, and concrete non-vacuity witnesses for Example
4.13 and Remark 4.14 (`SteinIntro.tex:2480-2510`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Boolean-Vector Encoding of `Finset (Fin N)` -/

/-- Support `{j : Fin N | v j = true}` of a boolean vector `v : Fin N → Bool`. -/
def boolSupport {N : ℕ} (v : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun j ↦ v j = true

/-- Indicator boolean vector `j ↦ decide (j ∈ A)` of a subset `A : Finset (Fin N)`. -/
def setToBoolVec {N : ℕ} (A : Finset (Fin N)) : Fin N → Bool :=
  fun j ↦ decide (j ∈ A)

@[simp]
theorem mem_boolSupport {N : ℕ} (v : Fin N → Bool) (j : Fin N) :
    j ∈ boolSupport v ↔ v j = true := by
  simp [boolSupport]

@[simp]
theorem setToBoolVec_apply {N : ℕ} (A : Finset (Fin N)) (j : Fin N) :
    setToBoolVec A j = decide (j ∈ A) :=
  rfl

@[simp]
theorem boolSupport_setToBoolVec {N : ℕ} (A : Finset (Fin N)) :
    boolSupport (setToBoolVec A) = A := by
  ext j
  simp [boolSupport, setToBoolVec]

@[simp]
theorem setToBoolVec_boolSupport {N : ℕ} (v : Fin N → Bool) :
    setToBoolVec (boolSupport v) = v := by
  funext j
  cases h : v j <;> simp [setToBoolVec, boolSupport, h]

theorem setToBoolVec_eq_iff {N : ℕ} (A : Finset (Fin N)) (v : Fin N → Bool) :
    setToBoolVec A = v ↔ A = boolSupport v := by
  constructor
  · rintro rfl
    exact (boolSupport_setToBoolVec A).symm
  · rintro rfl
    exact setToBoolVec_boolSupport v

/-- Equivalence between `Finset (Fin N)` and `Fin N → Bool`. -/
def finsetEquivBoolVec (N : ℕ) : Finset (Fin N) ≃ (Fin N → Bool) where
  toFun := setToBoolVec
  invFun := boolSupport
  left_inv := boolSupport_setToBoolVec
  right_inv := setToBoolVec_boolSupport

/-! ### Hypergeometric Support and Canonical Probability Measure -/

/-- The `Finset` of boolean vectors `v : Fin N → Bool` with exactly `m` `true` coordinates. -/
def hypergeomVecSet (N m : ℕ) : Finset (Fin N → Bool) :=
  Finset.univ.filter fun v ↦ (boolSupport v).card = m

@[simp]
theorem mem_hypergeomVecSet {N m : ℕ} {v : Fin N → Bool} :
    v ∈ hypergeomVecSet N m ↔ (boolSupport v).card = m := by
  simp [hypergeomVecSet]

theorem powersetCard_map_setToBoolVec (N m : ℕ) :
    ((Finset.univ : Finset (Fin N)).powersetCard m).map (finsetEquivBoolVec N).toEmbedding =
      hypergeomVecSet N m := by
  ext v
  simp only [Finset.mem_map, Finset.mem_powersetCard, Finset.subset_univ, true_and,
    Equiv.toEmbedding_apply, mem_hypergeomVecSet]
  constructor
  · rintro ⟨A, rfl, rfl⟩
    change (boolSupport (setToBoolVec A)).card = A.card
    rw [boolSupport_setToBoolVec]
  · intro hv
    exact ⟨boolSupport v, hv, setToBoolVec_boolSupport v⟩

theorem card_hypergeomVecSet (N m : ℕ) :
    (hypergeomVecSet N m).card = N.choose m := by
  rw [← powersetCard_map_setToBoolVec, Finset.card_map, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]

theorem hypergeomVecSet_nonempty {N m : ℕ} (hmN : m ≤ N) :
    (hypergeomVecSet N m).Nonempty := by
  rw [← Finset.card_pos, card_hypergeomVecSet]
  exact Nat.choose_pos hmN

/-- Uniform `PMF` on boolean vectors `v : Fin N → Bool` of Hamming weight `m` (`m ≤ N`). -/
noncomputable def hypergeomVecPMF {N m : ℕ} (hmN : m ≤ N) : PMF (Fin N → Bool) :=
  PMF.uniformOfFinset (hypergeomVecSet N m) (hypergeomVecSet_nonempty hmN)

/-- Canonical hypergeometric coordinate probability measure on `Fin N → Bool` (`m ≤ N`). -/
noncomputable def hypergeomVecMeasure {N m : ℕ} (hmN : m ≤ N) : Measure (Fin N → Bool) :=
  (hypergeomVecPMF hmN).toMeasure

instance isProbabilityMeasure_hypergeomVecMeasure {N m : ℕ} (hmN : m ≤ N) :
    IsProbabilityMeasure (hypergeomVecMeasure hmN) :=
  PMF.toMeasure.isProbabilityMeasure (hypergeomVecPMF hmN)

theorem hypergeomVecMeasure_singleton {N m : ℕ} (hmN : m ≤ N) (v : Fin N → Bool) :
    hypergeomVecMeasure hmN {v} =
      if v ∈ hypergeomVecSet N m then ((N.choose m : ℝ≥0∞))⁻¹ else 0 := by
  rw [hypergeomVecMeasure, PMF.toMeasure_apply_singleton _ _ .of_discrete,
    hypergeomVecPMF, PMF.uniformOfFinset_apply, card_hypergeomVecSet]
  split_ifs <;> rfl

theorem hypergeomVecMeasure_real_singleton {N m : ℕ} (hmN : m ≤ N) (v : Fin N → Bool) :
    (hypergeomVecMeasure hmN).real {v} =
      if v ∈ hypergeomVecSet N m then 1 / (N.choose m : ℝ) else 0 := by
  rw [measureReal_def, hypergeomVecMeasure_singleton]
  split_ifs with hv
  · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  · simp

/-- Coordinate permutation invariance of `hypergeomVecMeasure hmN`. -/
theorem hypergeomVecMeasure_perm_invariant {N m : ℕ} (hmN : m ≤ N) (σ : Equiv.Perm (Fin N)) :
    (hypergeomVecMeasure hmN).map (fun v j ↦ v (σ j)) = hypergeomVecMeasure hmN := by
  let permVec : (Fin N → Bool) ≃ (Fin N → Bool) :=
    { toFun := fun v j ↦ v (σ j)
      invFun := fun v j ↦ v (σ.symm j)
      left_inv := fun v ↦ by funext j; simp
      right_inv := fun v ↦ by funext j; simp }
  refine measure_ext_of_singleton_fintype fun v ↦ ?_
  change (Measure.map permVec (hypergeomVecMeasure hmN)) {v} = _
  rw [measure_map_singleton_fintype (hypergeomVecMeasure hmN) permVec v]
  have hfilt : (Finset.univ.filter fun u : Fin N → Bool ↦ permVec u = v) = {permVec.symm v} := by
    ext u
    simp [Equiv.eq_symm_apply]
  rw [hfilt, Finset.sum_singleton, hypergeomVecMeasure_singleton, hypergeomVecMeasure_singleton]
  have hcard : (boolSupport (permVec.symm v)).card = (boolSupport v).card := by
    have hmap : (boolSupport (permVec.symm v)).map σ.symm.toEmbedding = boolSupport v := by
      ext j
      simp [boolSupport, permVec]
    rw [← hmap, Finset.card_map]
  simp [mem_hypergeomVecSet, hcard]

/-! ### Measurability and Pushforward Bridge from `S : Ω → Finset (Fin N)` -/

/-- Any composition `g ∘ S` with `S : Ω → Finset (Fin N)` is measurable when all level sets
`{ω | S ω = A}` are measurable, without requiring a `MeasurableSpace` instance on
`Finset (Fin N)`. -/
theorem measurable_comp_finset_of_levelSet
    {N : ℕ} {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {S : Ω → Finset (Fin N)}
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (g : Finset (Fin N) → β) :
    Measurable (fun ω ↦ g (S ω)) := by
  classical
  intro E _
  have hpre : (fun ω ↦ g (S ω)) ⁻¹' E =
      ⋃ A ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun A ↦ g A ∈ E),
        {ω | S ω = A} := by
    ext ω
    simp
  rw [hpre]
  exact Finset.measurableSet_biUnion _ fun A _ ↦ hS A

/-- Under `[IsProbabilityMeasure P]`, if `P.real {ω | S ω = A} = 1 / N.choose m` for every
`m`-subset `A` of `Fin N`, then `P {ω | S ω = A} = 0` for every subset `A` with `A.card ≠ m`. -/
theorem measure_levelSet_eq_zero_of_card_ne
    {N m : ℕ} (hmN : m ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)}
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ))
    {A : Finset (Fin N)} (hcard : A.card ≠ m) :
    P {ω | S ω = A} = 0 := by
  classical
  let pm : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard m
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Finset (Fin N))))
      (fun B : Finset (Fin N) ↦ {ω : Ω | S ω = B}) := by
    intro B₁ _ B₂ _ hne
    exact Set.disjoint_left.mpr fun ω h1 h2 ↦ hne (h1.symm.trans h2)
  have hunion : (⋃ B ∈ (Finset.univ : Finset (Finset (Fin N))), {ω : Ω | S ω = B}) = Set.univ := by
    ext ω
    simp
  have htotal : (∑ B : Finset (Fin N), P.real {ω | S ω = B}) = 1 := by
    rw [← measureReal_biUnion_finset hdisj (fun B _ ↦ hS B), hunion, probReal_univ]
  have hchoose_pos : (0 : ℝ) < (N.choose m : ℝ) := by exact_mod_cast Nat.choose_pos hmN
  have hsum_pm : (∑ B ∈ pm, P.real {ω | S ω = B}) = 1 := by
    rw [Finset.sum_congr rfl fun B hB ↦ hS_unif B hB, Finset.sum_const,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div_cancel hchoose_pos.ne']
  have hsplit : (∑ B : Finset (Fin N), P.real {ω | S ω = B}) =
      (∑ B ∈ pm, P.real {ω | S ω = B}) + ∑ B ∈ Finset.univ \ pm, P.real {ω | S ω = B} := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 1
    ext B
    simp
  have hrest_zero : (∑ B ∈ Finset.univ \ pm, P.real {ω | S ω = B}) = 0 := by
    linarith [htotal, hsum_pm, hsplit]
  have hAmem : A ∈ (Finset.univ : Finset (Finset (Fin N))) \ pm := by
    simp [pm, hcard]
  have hA_real_zero : P.real {ω | S ω = A} = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun B _ ↦ measureReal_nonneg).mp hrest_zero A hAmem
  exact (measureReal_eq_zero_iff).mp hA_real_zero

/-- Under the hypotheses of Example 4.13, `(S ω).card = m` holds `P`-almost everywhere. -/
theorem ae_card_eq_of_uniform_powersetCard
    {N m : ℕ} (hmN : m ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)}
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) :
    ∀ᵐ ω ∂P, (S ω).card = m := by
  classical
  rw [ae_iff]
  have hset : {ω : Ω | ¬ (S ω).card = m} =
      ⋃ A ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun A ↦ A.card ≠ m),
        {ω | S ω = A} := by
    ext ω
    simp
  rw [hset]
  exact measure_biUnion_null_iff (Finset.countable_toSet _) |>.mpr fun A hA ↦
    measure_levelSet_eq_zero_of_card_ne hmN P hS hS_unif (Finset.mem_filter.mp hA).2

/-- Pushforward of `setToBoolVec ∘ S` under `P` equals `hypergeomVecMeasure hmN`. -/
theorem map_setToBoolVec_eq_hypergeomVecMeasure
    {N m : ℕ} (hmN : m ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)}
    (hS : ∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A})
    (hS_unif : ∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) :
    P.map (fun ω ↦ setToBoolVec (S ω)) = hypergeomVecMeasure hmN := by
  have hmeas : Measurable (fun ω ↦ setToBoolVec (S ω)) :=
    measurable_comp_finset_of_levelSet hS setToBoolVec
  refine measure_ext_of_singleton_fintype fun v ↦ ?_
  rw [Measure.map_apply hmeas .of_discrete]
  have hpre : (fun ω ↦ setToBoolVec (S ω)) ⁻¹' {v} = {ω | S ω = boolSupport v} := by
    ext ω
    simp [setToBoolVec_eq_iff]
  rw [hpre, hypergeomVecMeasure_singleton]
  by_cases hv : v ∈ hypergeomVecSet N m
  · rw [ite_eq_left hv, ← ofReal_measureReal]
    have hmem : boolSupport v ∈ (Finset.univ : Finset (Fin N)).powersetCard m := by
      simp [mem_hypergeomVecSet.mp hv]
    rw [hS_unif (boolSupport v) hmem, one_div,
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.choose_pos hmN), ENNReal.ofReal_natCast]
  · rw [ite_eq_right hv]
    exact measure_levelSet_eq_zero_of_card_ne hmN P hS hS_unif (mt mem_hypergeomVecSet.mpr hv)

/-! ### Non-Vacuity Witnesses -/

/-- Non-vacuity witness at `N = 4, m = 2`: `hypergeomVecSet 4 2` has cardinality `6` and
`hypergeomVecMeasure` assigns probability `1 / 6` to `{0, 1} ⊆ Fin 4`. -/
theorem hypergeomVecMeasure_witness_N4_m2 :
    (hypergeomVecSet 4 2).card = 6 ∧
      (hypergeomVecMeasure (by decide : 2 ≤ 4)).real
        {setToBoolVec ({(0 : Fin 4), (1 : Fin 4)} : Finset (Fin 4))} = 1 / 6 := by
  refine ⟨by rw [card_hypergeomVecSet]; decide, ?_⟩
  rw [hypergeomVecMeasure_real_singleton]
  have hmem :
      setToBoolVec ({(0 : Fin 4), (1 : Fin 4)} : Finset (Fin 4)) ∈ hypergeomVecSet 4 2 := by
    rw [mem_hypergeomVecSet, boolSupport_setToBoolVec]
    decide
  rw [ite_eq_left hmem]
  have h6 : Nat.choose 4 2 = 6 := by decide
  rw [h6]
  norm_num

end SteinMethod
