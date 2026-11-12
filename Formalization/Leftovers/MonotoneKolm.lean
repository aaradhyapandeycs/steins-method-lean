/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Kolmogorov.ExchangeableBound
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic

/-!
# Monotone Coordinate-Replacement Kolmogorov Bound (`Formalization.Leftovers.MonotoneKolm`)

Provides reusable finite Bernoulli-product coordinate-replacement infrastructure for normal
approximation in Kolmogorov distance (`SteinIntro.tex:935-941`, `1745-1812`):
* `prod_pi_bool_efron_stein`: Boolean discrete-derivative Efron–Stein variance inequality on the
  doubled product space `(Fin K → Bool) × (Fin K → Bool)`.
* `monotone_pi_kolmogorovDist_le`: Kolmogorov normal approximation bound for standardized functions
  on `Fin K → Bool` with bounded non-negative coordinate differences (`0 ≤ C k x ≤ δ`).
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Coordinate-Replacement & Efron–Stein on Finite Bernoulli Products -/

abbrev BitVec (K : ℕ) := Fin K → Bool
noncomputable abbrev bitPi (K : ℕ) (μ₀ : Measure Bool) : Measure (BitVec K) :=
  Measure.pi fun _ : Fin K ↦ μ₀
noncomputable abbrev bitProd (K : ℕ) (μ₀ : Measure Bool) : Measure (BitVec K × BitVec K) :=
  (bitPi K μ₀).prod (bitPi K μ₀)

noncomputable def bitVal : Bool → ℝ | true => 1 | false => 0
lemma bitVal_nonneg (b : Bool) : 0 ≤ bitVal b := by cases b <;> simp [bitVal]
lemma bitVal_le_one (b : Bool) : bitVal b ≤ 1 := by cases b <;> simp [bitVal]
lemma bitVal_sq (b : Bool) : bitVal b ^ 2 = bitVal b := by cases b <;> simp [bitVal]
lemma abs_bitVal_sub_le_one (a b : Bool) : |bitVal a - bitVal b| ≤ 1 := by
  cases a <;> cases b <;> norm_num [bitVal]

lemma diff_update_eq_bitVal_sub_mul {K : ℕ} (f : BitVec K → ℝ) (z : BitVec K)
    (k : Fin K) (b : Bool) : f z - f (Function.update z k b) =
      (bitVal (z k) - bitVal b) * (f (Function.update z k true) - f (Function.update z k false)) :=
  by
  have h0 : Function.update z k (z k) = z := Function.update_eq_self k z
  cases hzk : z k <;> cases b <;> { rw [hzk] at h0; rw [h0]; simp [bitVal] }

lemma finite_discrete_integrable {α : Type*} [Finite α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] (f : α → ℝ) : Integrable f μ :=
  (MemLp.of_discrete (p := 2) (μ := μ) (f := f)).integrable one_le_two

lemma measure_eq_of_singleton {α : Type*} [Finite α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] {μ₁ μ₂ : Measure α} (h : ∀ x, μ₁ {x} = μ₂ {x}) : μ₁ = μ₂ := by
  ext s _; classical
  let _ := Fintype.ofFinite α
  have hs : s = ⋃ x ∈ s.toFinset, ({x} : Set α) := by ext x; simp
  have hd : PairwiseDisjoint (s.toFinset : Set α) (fun x : α ↦ ({x} : Set α)) :=
    fun _ _ _ _ hne ↦ disjoint_singleton.mpr hne
  rw [hs, measure_biUnion_finset hd (fun _ _ ↦ .of_discrete),
    measure_biUnion_finset hd (fun _ _ ↦ .of_discrete)]
  exact Finset.sum_congr rfl fun x _ ↦ h x

lemma pi_singleton_apply {ι : Type*} [Fintype ι] (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (x : ι → Bool) : (Measure.pi fun _ : ι ↦ μ₀) {x} = ∏ i : ι, μ₀ {x i} := by
  rw [show ({x} : Set (ι → Bool)) = univ.pi (fun i : ι ↦ ({x i} : Set Bool)) by
    ext y; simp [funext_iff], Measure.pi_pi]

private lemma prod_pi_singleton_apply {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (z : BitVec K × BitVec K) : bitProd K μ₀ {z} = ∏ i : Fin K, (μ₀ {z.1 i} * μ₀ {z.2 i}) := by
  rw [show ({z} : Set (BitVec K × BitVec K)) = {z.1} ×ˢ {z.2} by ext w; simp [Prod.ext_iff],
    Measure.prod_prod, pi_singleton_apply, pi_singleton_apply, ← Finset.prod_mul_distrib]

private def coordMaskSwap {K : ℕ} (mask : Fin K → Bool) (z : BitVec K × BitVec K) :=
  (fun i ↦ if mask i then z.2 i else z.1 i, fun i ↦ if mask i then z.1 i else z.2 i)

private lemma coordMaskSwap_involutive {K : ℕ} (mask : Fin K → Bool) :
    Function.Involutive (coordMaskSwap mask) := by
  rintro ⟨x, y⟩; ext i <;> cases h : mask i <;> simp [coordMaskSwap, h]

private lemma map_coordMaskSwap {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (mask : Fin K → Bool) : (bitProd K μ₀).map (coordMaskSwap mask) = bitProd K μ₀ := by
  refine measure_eq_of_singleton fun z ↦ ?_
  have hpre : coordMaskSwap mask ⁻¹' {z} = {coordMaskSwap mask z} := by
    ext w; simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun h ↦ by rw [← h, coordMaskSwap_involutive mask w],
      fun h ↦ by rw [h, coordMaskSwap_involutive mask z]⟩
  rw [Measure.map_apply .of_discrete .of_discrete, hpre,
    prod_pi_singleton_apply, prod_pi_singleton_apply]
  exact Finset.prod_congr rfl fun i _ ↦ by cases h : mask i <;> simp [coordMaskSwap, h, mul_comm]

private lemma integral_coordMaskSwap {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (mask : Fin K → Bool) (H : BitVec K × BitVec K → ℝ) :
    (∫ z, H (coordMaskSwap mask z) ∂bitProd K μ₀) = ∫ z, H z ∂bitProd K μ₀ := by
  have hint := integral_map (μ := bitProd K μ₀) (φ := coordMaskSwap mask)
    Measurable.of_discrete.aemeasurable (f := H) Measurable.of_discrete.aestronglyMeasurable
  rwa [map_coordMaskSwap μ₀ mask, eq_comm] at hint

private def swapCoord {K : ℕ} (k : Fin K) := coordMaskSwap (K := K) (· == k)
private def prefixSwap {K : ℕ} (m : ℕ) := coordMaskSwap (K := K) (fun i ↦ decide (i.1 < m))
def hybVec {K : ℕ} (m : ℕ) (z : BitVec K × BitVec K) : BitVec K :=
  fun i ↦ if i.1 < m then z.2 i else z.1 i
private def updVec {K : ℕ} (k : Fin K) (z : BitVec K × BitVec K) : BitVec K :=
  Function.update z.1 k (z.2 k)

private lemma swapCoord_fst_eq_updVec {K : ℕ} (k : Fin K) (z : BitVec K × BitVec K) :
    (swapCoord k z).1 = updVec k z := by
  ext i; by_cases hik : i = k <;> simp [swapCoord, coordMaskSwap, updVec, hik]

private lemma hybVec_swapCoord_left {K : ℕ} (k : Fin K) (z : BitVec K × BitVec K) :
    hybVec k.1 (swapCoord k z) = hybVec (k.1 + 1) z := by
  ext i; by_cases hik : i = k
  · subst hik; simp [hybVec, swapCoord, coordMaskSwap]
  · have hval : i.1 ≠ k.1 := fun h ↦ hik (Fin.ext h)
    by_cases hlt : i.1 < k.1
    · simp [hybVec, swapCoord, coordMaskSwap, hik, hlt, Nat.lt_succ_of_lt hlt]
    · have hlt' : ¬ i.1 < k.1 + 1 := by omega
      simp [hybVec, swapCoord, coordMaskSwap, hik, hlt, hlt']

private lemma hybVec_swapCoord_right {K : ℕ} (k : Fin K) (z : BitVec K × BitVec K) :
    hybVec (k.1 + 1) (swapCoord k z) = hybVec k.1 z := by
  simpa [swapCoord, coordMaskSwap_involutive (· == k) z] using
    (hybVec_swapCoord_left k (swapCoord k z)).symm

private lemma updVec_prefixSwap {K : ℕ} (k : Fin K) (z : BitVec K × BitVec K) :
    updVec k (prefixSwap k.1 z) = hybVec (k.1 + 1) z := by
  ext i; by_cases hik : i = k
  · subst hik; simp [updVec, prefixSwap, coordMaskSwap, hybVec]
  · have hval : i.1 ≠ k.1 := fun h ↦ hik (Fin.ext h)
    rw [updVec, Function.update_of_ne hik]
    by_cases hlt : i.1 < k.1
    · simp only [prefixSwap, coordMaskSwap, hybVec, decide_eq_true_eq, hlt,
        Nat.lt_succ_of_lt hlt, ↓reduceIte]
    · have hlt' : ¬ i.1 < k.1 + 1 := by omega
      simp only [prefixSwap, coordMaskSwap, hybVec, decide_eq_true_eq, hlt, hlt', ↓reduceIte]

lemma hybVec_map_eq_pi {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] (m : ℕ) :
    (bitProd K μ₀).map (hybVec m) = bitPi K μ₀ := by
  have hcomp : (hybVec m : BitVec K × BitVec K → BitVec K) = Prod.fst ∘ prefixSwap m := by
    ext z i; simp [hybVec, prefixSwap, coordMaskSwap]
  rw [hcomp, ← Measure.map_map measurable_fst .of_discrete, prefixSwap, map_coordMaskSwap μ₀ _]
  exact Measure.fst_prod

private lemma pi_chatterjee_identity {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (W : BitVec K → ℝ) (hW0 : ∫ x, W x ∂bitPi K μ₀ = 0) (g : ℝ → ℝ) :
    (∫ x, W x * g (W x) ∂bitPi K μ₀) = (1 / 2 : ℝ) * ∑ k : Fin K,
      ∫ z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * (g (W z.1) - g (W (updVec k z)))
        ∂bitProd K μ₀ := by
  set ν := bitPi K μ₀; set P₂ := bitProd K μ₀
  have hfst : P₂.map Prod.fst = ν := Measure.fst_prod
  have htele : ∀ z : BitVec K × BitVec K,
      W z.1 - W z.2 = ∑ k : Fin K, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) := fun z ↦ by
    rw [Fin.sum_univ_eq_sum_range (fun m ↦ W (hybVec m z) - W (hybVec (m + 1) z)),
      Finset.sum_range_sub' (fun m ↦ W (hybVec m z)) K,
      show hybVec 0 z = z.1 by ext i; simp [hybVec],
      show hybVec K z = z.2 by ext i; simp [hybVec, i.2]]
  have hlhs1 : (∫ z, W z.1 * g (W z.1) ∂P₂) = ∫ x, W x * g (W x) ∂ν := by
    have hm := integral_map (μ := P₂) (φ := Prod.fst) measurable_fst.aemeasurable
      (f := fun x ↦ W x * g (W x)) Measurable.of_discrete.aestronglyMeasurable
    rwa [hfst, eq_comm] at hm
  have hlhs2 : (∫ z, W z.2 * g (W z.1) ∂P₂) = 0 := by
    rw [show (fun z : BitVec K × BitVec K ↦ W z.2 * g (W z.1)) = fun z ↦ g (W z.1) * W z.2 from
      funext fun _ ↦ mul_comm _ _, integral_prod_mul (μ := ν) (ν := ν) (fun x ↦ g (W x)) W,
      hW0, mul_zero]
  have hstep : ∀ k : Fin K,
      (∫ z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * g (W z.1) ∂P₂) =
        (1 / 2 : ℝ) * ∫ z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
          (g (W z.1) - g (W (updVec k z))) ∂P₂ := fun k ↦ by
    let H : BitVec K × BitVec K → ℝ := fun z ↦
      (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * g (W z.1)
    have hinv := integral_coordMaskSwap μ₀ (· == k) H
    have hH_swap : ∀ z : BitVec K × BitVec K, H (coordMaskSwap (· == k) z) =
        -(W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * g (W (updVec k z)) := fun z ↦ by
      change H (swapCoord k z) = _; dsimp only [H]
      rw [hybVec_swapCoord_left, hybVec_swapCoord_right, swapCoord_fst_eq_updVec]; ring
    simp_rw [hH_swap] at hinv
    have hadd : (∫ z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
          (g (W z.1) - g (W (updVec k z))) ∂P₂) = (∫ z, H z ∂P₂) +
        ∫ z, (-(W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * g (W (updVec k z))) ∂P₂ := by
      rw [← integral_add (finite_discrete_integrable _) (finite_discrete_integrable _)]
      exact integral_congr_ae (ae_of_all _ fun _ ↦ by dsimp only [H]; ring)
    change ∫ z, H z ∂P₂ = _
    change ∫ z, -(W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * g (W (updVec k z)) ∂P₂ =
      ∫ z, H z ∂P₂ at hinv
    linarith
  calc (∫ x, W x * g (W x) ∂ν)
      = (∫ z, W z.1 * g (W z.1) ∂P₂) - ∫ z, W z.2 * g (W z.1) ∂P₂ := by
          rw [hlhs1, hlhs2, sub_zero]
    _ = ∫ z, (W z.1 - W z.2) * g (W z.1) ∂P₂ := by
          rw [← integral_sub (finite_discrete_integrable _) (finite_discrete_integrable _)]
          exact integral_congr_ae (ae_of_all _ fun _ ↦ by ring)
    _ = ∫ z, (∑ k : Fin K, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * g (W z.1)) ∂P₂ :=
          integral_congr_ae (ae_of_all _ fun z ↦ by dsimp only; rw [htele z, Finset.sum_mul])
    _ = ∑ k : Fin K, ∫ z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * g (W z.1) ∂P₂ :=
          integral_finsetSum Finset.univ fun _ _ ↦ finite_discrete_integrable _
    _ = (1 / 2 : ℝ) * ∑ k : Fin K, ∫ z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
          (g (W z.1) - g (W (updVec k z))) ∂P₂ := by simp_rw [hstep, ← Finset.mul_sum]

lemma integral_pi_mul_of_disjoint {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    (A B : Finset (Fin K)) (hdisj : Disjoint A B) {f g : BitVec K → ℝ}
    (hf : ∀ x y : BitVec K, (∀ i ∈ A, x i = y i) → f x = f y)
    (hg : ∀ x y : BitVec K, (∀ i ∈ B, x i = y i) → g x = g y) :
    (∫ x, f x * g x ∂bitPi K μ₀) = (∫ x, f x ∂bitPi K μ₀) * (∫ x, g x ∂bitPi K μ₀) := by
  set ν := bitPi K μ₀
  classical
  let fA : (A → Bool) → ℝ := fun u ↦ f fun i ↦ if hi : i ∈ A then u ⟨i, hi⟩ else false
  let gB : (B → Bool) → ℝ := fun v ↦ g fun i ↦ if hi : i ∈ B then v ⟨i, hi⟩ else false
  let bitBack : ℝ → Bool := fun r ↦ if r = 1 then true else false
  have hb_inv : ∀ b, bitBack (bitVal b) = b := fun b ↦ by cases b <;> simp [bitBack, bitVal]
  have hf_eq : f = fun x : BitVec K ↦ fA (fun i : A ↦ bitBack (bitVal (x i.1))) := by
    simp_rw [hb_inv]; exact funext fun x ↦ hf x _ fun i hi ↦ by simp [hi]
  have hg_eq : g = fun x : BitVec K ↦ gB (fun i : B ↦ bitBack (bitVal (x i.1))) := by
    simp_rw [hb_inv]; exact funext fun x ↦ hg x _ fun i hi ↦ by simp [hi]
  have hbb : Measurable bitBack :=
    Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const
  have hmS : ∀ {S : Finset (Fin K)} (φ : (S → Bool) → ℝ),
      Measurable (fun u : S → ℝ ↦ φ (fun i ↦ bitBack (u i))) := fun φ ↦
    Measurable.of_discrete.comp (measurable_pi_iff.mpr fun i ↦ hbb.comp (measurable_pi_apply i))
  have hpi : iIndepFun (fun (i : Fin K) (x : BitVec K) ↦ bitVal (x i)) ν :=
    iIndepFun_pi fun _ ↦ Measurable.of_discrete.aemeasurable
  have hind : IndepFun f g ν := by
    rw [hf_eq, hg_eq]
    exact (iIndepFun.indepFun_finset A B hdisj hpi (fun _ ↦ .of_discrete)).comp (hmS fA) (hmS gB)
  exact hind.integral_fun_mul_eq_mul_integral
    Measurable.of_discrete.aestronglyMeasurable Measurable.of_discrete.aestronglyMeasurable

lemma integral_bernoulli_pi_eval {K : ℕ} (q : unitInterval) (i : Fin K) (φ : Bool → ℝ) :
    (∫ x, φ (x i) ∂bitPi K (bernoulliMeasure true false q)) =
      (q : ℝ) * φ true + (1 - (q : ℝ)) * φ false := by
  set μ₀ := bernoulliMeasure true false q
  have hm := integral_map (μ := bitPi K μ₀) (φ := Function.eval i)
    (measurable_pi_apply i).aemeasurable (f := φ) Measurable.of_discrete.aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : Fin K ↦ μ₀) i).map_eq,
    integral_bernoulliMeasure true false q φ] at hm
  simpa [smul_eq_mul] using hm.symm

private def split2K {K : ℕ} (w : BitVec (K + K)) : BitVec K × BitVec K :=
  (fun i ↦ w (finSumFinEquiv (Sum.inl i)), fun i ↦ w (finSumFinEquiv (Sum.inr i)))
private def merge2K {K : ℕ} (z : BitVec K × BitVec K) : BitVec (K + K) :=
  fun j ↦ Sum.elim z.1 z.2 (finSumFinEquiv.symm j)

private lemma map_split2K_eq_prod {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀] :
    (bitPi (K + K) μ₀).map split2K = bitProd K μ₀ := by
  refine measure_eq_of_singleton fun z ↦ ?_
  have hpre : split2K ⁻¹' {z} = {merge2K z} := by
    ext w; simp only [mem_preimage, mem_singleton_iff]; refine ⟨?_, ?_⟩
    · rintro rfl; ext j; obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
      cases s <;> simp only [merge2K, split2K, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    · rintro rfl; ext i <;>
        simp only [split2K, merge2K, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  rw [Measure.map_apply .of_discrete .of_discrete, hpre, pi_singleton_apply,
    prod_pi_singleton_apply, ← finSumFinEquiv.prod_comp]
  simp [merge2K, Finset.prod_mul_distrib]

lemma integral_prod_pi_mul_of_ne {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    {k k' : Fin K} (hne : k ≠ k') (φ ψ : Bool → Bool → ℝ) :
    (∫ z, φ (z.1 k) (z.2 k) * ψ (z.1 k') (z.2 k') ∂bitProd K μ₀) =
      (∫ z, φ (z.1 k) (z.2 k) ∂bitProd K μ₀) * (∫ z, ψ (z.1 k') (z.2 k') ∂bitProd K μ₀) := by
  set ν₂ := bitPi (K + K) μ₀
  have hpull : ∀ H : BitVec K × BitVec K → ℝ,
      (∫ z, H z ∂bitProd K μ₀) = ∫ w, H (split2K w) ∂ν₂ := fun H ↦ by
    rw [← map_split2K_eq_prod μ₀]; exact integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable
  rw [hpull, hpull, hpull]
  let A : Finset (Fin (K + K)) := {finSumFinEquiv (Sum.inl k), finSumFinEquiv (Sum.inr k)}
  let B : Finset (Fin (K + K)) := {finSumFinEquiv (Sum.inl k'), finSumFinEquiv (Sum.inr k')}
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]; intro x hxA hxB
    simp only [A, B, Finset.mem_insert, Finset.mem_singleton] at hxA hxB
    rcases hxA with rfl | rfl <;> rcases hxB with h | h <;>
      { have h' := finSumFinEquiv.injective h; simp [hne] at h' }
  exact integral_pi_mul_of_disjoint μ₀ A B hdisj
    (fun _ _ h ↦ by simp only [split2K]; rw [h _ (by simp [A]), h _ (by simp [A])])
    (fun _ _ h ↦ by simp only [split2K]; rw [h _ (by simp [B]), h _ (by simp [B])])

private lemma pi_bool_efron_stein {K : ℕ} (q : unitInterval) (G : BitVec K → ℝ) :
    let ν := bitPi K (bernoulliMeasure true false q)
    variance G ν ≤ (q : ℝ) * (1 - (q : ℝ)) * ∑ j : Fin K,
      ∫ w, (G (Function.update w j true) - G (Function.update w j false)) ^ 2 ∂ν := by
  intro ν; set μ₀ := bernoulliMeasure true false q; set P₂ := bitProd K μ₀
  let Gc : BitVec K → ℝ := fun x ↦ G x - ∫ u, G u ∂ν
  have hGc0 : ∫ x, Gc x ∂ν = 0 := by
    dsimp only [Gc]; rw [integral_sub (finite_discrete_integrable _) (integrable_const _),
      integral_const, probReal_univ, one_smul, sub_self]
  have hvar : variance G ν = ∫ x, Gc x * Gc x ∂ν :=
    (variance_eq_integral Measurable.of_discrete.aemeasurable).trans
      (integral_congr_ae (ae_of_all _ fun x ↦ sq (Gc x)))
  have hchat := pi_chatterjee_identity μ₀ Gc hGc0 id; simp only [id_eq] at hchat
  have hes : variance G ν ≤ (1 / 2 : ℝ) * ∑ j : Fin K, ∫ u, (G u.1 - G (updVec j u)) ^ 2 ∂P₂ := by
    rw [hvar, hchat]; exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ by
      have hd1 : ∀ z, Gc (hybVec j.1 z) - Gc (hybVec (j.1 + 1) z) =
          G (hybVec j.1 z) - G (hybVec (j.1 + 1) z) := fun _ ↦ by dsimp only [Gc]; ring
      have hd2 : ∀ z, Gc z.1 - Gc (updVec j z) = G z.1 - G (updVec j z) :=
        fun _ ↦ by dsimp only [Gc]; ring
      simp_rw [hd1, hd2]
      have hle := integral_mono (μ := P₂) (finite_discrete_integrable _)
        (finite_discrete_integrable _) fun z : BitVec K × BitVec K ↦ show
          (G (hybVec j.1 z) - G (hybVec (j.1 + 1) z)) * (G z.1 - G (updVec j z)) ≤
            (1 / 2 : ℝ) * (G (hybVec j.1 z) - G (hybVec (j.1 + 1) z)) ^ 2 +
              (1 / 2 : ℝ) * (G z.1 - G (updVec j z)) ^ 2 by
          nlinarith [sq_nonneg ((G (hybVec j.1 z) - G (hybVec (j.1 + 1) z)) -
            (G z.1 - G (updVec j z)))]
      rw [integral_add (finite_discrete_integrable _) (finite_discrete_integrable _),
        integral_const_mul, integral_const_mul] at hle
      have hinv := integral_coordMaskSwap μ₀ (fun i ↦ decide (i.1 < j.1))
        (fun z ↦ (G z.1 - G (updVec j z)) ^ 2)
      have hps : ∀ z : BitVec K × BitVec K,
          (G (coordMaskSwap (fun i ↦ decide (i.1 < j.1)) z).1 -
            G (updVec j (coordMaskSwap (fun i ↦ decide (i.1 < j.1)) z))) ^ 2 =
          (G (hybVec j.1 z) - G (hybVec (j.1 + 1) z)) ^ 2 := fun z ↦ by
        rw [show (coordMaskSwap (fun i : Fin K ↦ decide (i.1 < j.1)) z).1 = hybVec j.1 z by
          ext i; simp [coordMaskSwap, hybVec]]
        change (G (hybVec j.1 z) - G (updVec j (prefixSwap j.1 z))) ^ 2 = _; rw [updVec_prefixSwap]
      simp_rw [hps] at hinv
      change (∫ z, (G (hybVec j.1 z) - G (hybVec (j.1 + 1) z)) ^ 2 ∂P₂) =
        ∫ z, (G z.1 - G (updVec j z)) ^ 2 ∂P₂ at hinv
      linarith) (by norm_num)
  refine hes.trans (le_of_eq ?_)
  have hterm : ∀ j : Fin K, (∫ u, (G u.1 - G (updVec j u)) ^ 2 ∂P₂) =
      2 * (q : ℝ) * (1 - (q : ℝ)) *
        ∫ w, (G (Function.update w j true) - G (Function.update w j false)) ^ 2 ∂ν := fun j ↦ by
    let D : BitVec K → ℝ := fun w ↦
      (G (Function.update w j true) - G (Function.update w j false)) ^ 2
    have hpt : ∀ u : BitVec K × BitVec K,
        (G u.1 - G (updVec j u)) ^ 2 = (bitVal (u.1 j) - bitVal (u.2 j)) ^ 2 * D u.1 := fun u ↦ by
      dsimp only [updVec, D]; rw [diff_update_eq_bitVal_sub_mul G u.1 j (u.2 j)]; ring
    simp_rw [hpt]; rw [integral_prod _ (finite_discrete_integrable _)]; simp_rw [integral_mul_const]
    let φ : Bool → ℝ := fun a ↦ ∫ y, (bitVal a - bitVal (y j)) ^ 2 ∂ν
    change (∫ w, φ (w j) * D w ∂ν) = 2 * (q : ℝ) * (1 - (q : ℝ)) * ∫ w, D w ∂ν
    rw [integral_pi_mul_of_disjoint μ₀ {j} (Finset.univ.erase j) (by simp)
      (fun x y h ↦ by rw [h j (Finset.mem_singleton_self j)])
      (fun x y h ↦ by
        have hu : ∀ b, Function.update x j b = Function.update y j b := fun b ↦ by
          ext i; by_cases hij : i = j
          · subst hij; simp
          · simp [hij, h i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)]
        dsimp only [D]; rw [hu true, hu false]),
      integral_bernoulli_pi_eval q j φ]
    have hφt : φ true = 1 - (q : ℝ) := by
      dsimp [φ, ν]; rw [integral_bernoulli_pi_eval q j (fun b ↦ (bitVal true - bitVal b) ^ 2)]
      simp [bitVal]
    have hφf : φ false = (q : ℝ) := by
      dsimp [φ, ν]; rw [integral_bernoulli_pi_eval q j (fun b ↦ (bitVal false - bitVal b) ^ 2)]
      simp [bitVal]
    rw [hφt, hφf]; ring
  simp_rw [hterm, ← Finset.mul_sum]; ring

/-- Boolean discrete-derivative Efron–Stein variance inequality on `(Fin K → Bool) × (Fin K → Bool)`
under independent `Bernoulli(q)` coordinates (`SteinIntro.tex:935-941`). -/
theorem prod_pi_bool_efron_stein {K : ℕ} (q : unitInterval) (F : BitVec K × BitVec K → ℝ) :
    let P₂ := bitProd K (bernoulliMeasure true false q)
    variance F P₂ ≤ (q : ℝ) * (1 - (q : ℝ)) * ∑ e : Fin K,
      ((∫ z, (F (Function.update z.1 e true, z.2) -
          F (Function.update z.1 e false, z.2)) ^ 2 ∂P₂) +
        (∫ z, (F (z.1, Function.update z.2 e true) -
          F (z.1, Function.update z.2 e false)) ^ 2 ∂P₂)) := by
  intro P₂; set μ₀ := bernoulliMeasure true false q; set ν₂ := bitPi (K + K) μ₀
  have hmap : ν₂.map split2K = P₂ := map_split2K_eq_prod μ₀
  rw [show variance F P₂ = variance (F ∘ split2K) ν₂ by
    rw [← hmap, variance_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aemeasurable]]
  refine (pi_bool_efron_stein q (F ∘ split2K)).trans (le_of_eq ?_)
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  have hpull : ∀ H : BitVec K × BitVec K → ℝ, (∫ z, H z ∂P₂) = ∫ w, H (split2K w) ∂ν₂ :=
    fun H ↦ by
      rw [← hmap]; exact integral_map Measurable.of_discrete.aemeasurable
        Measurable.of_discrete.aestronglyMeasurable
  have hinl : ∀ (e : Fin K) (w : BitVec (K + K)) (b : Bool),
      split2K (Function.update w (finSumFinEquiv (Sum.inl e)) b) =
        (Function.update (split2K w).1 e b, (split2K w).2) := fun e w b ↦ by
    ext i
    · by_cases hie : i = e
      · subst hie; simp only [split2K, Function.update_self]
      · dsimp only [split2K]
        rw [Function.update_of_ne (finSumFinEquiv.injective.ne (by simp [hie])),
          Function.update_of_ne hie]
    · dsimp only [split2K]; rw [Function.update_of_ne (finSumFinEquiv.injective.ne (by simp))]
  have hinr : ∀ (e : Fin K) (w : BitVec (K + K)) (b : Bool),
      split2K (Function.update w (finSumFinEquiv (Sum.inr e)) b) =
        ((split2K w).1, Function.update (split2K w).2 e b) := fun e w b ↦ by
    ext i
    · dsimp only [split2K]; rw [Function.update_of_ne (finSumFinEquiv.injective.ne (by simp))]
    · by_cases hie : i = e
      · subst hie; simp only [split2K, Function.update_self]
      · dsimp only [split2K]
        rw [Function.update_of_ne (finSumFinEquiv.injective.ne (by simp [hie])),
          Function.update_of_ne hie]
  congr 1; refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [hpull, hpull]; dsimp only [Function.comp_apply, ν₂, μ₀]; simp_rw [hinl, hinr]

/-! ### Section 2: Monotone Coordinate-Replacement Kolmogorov Stein Bound -/

private lemma abs_normalSteinSolKolm_rem_le (x w w' : ℝ) :
    |(normalSteinSolKolm x w - normalSteinSolKolm x w') -
        (w - w') * (w * normalSteinSolKolm x w - stdNormalCDF x) - (min x w - min x w')| ≤
      (|w| + Real.sqrt (2 * Real.pi) / 4) * ((w - w') ^ 2 / 2) := by
  set f := normalSteinSolKolm x; set M : ℝ := |w| + Real.sqrt (2 * Real.pi) / 4
  let R : ℝ → ℝ := fun u ↦ (f u - f w) - (u - w) * (w * f w - stdNormalCDF x) - (min x u - min x w)
  have hR_w : R w = 0 := by simp [R]
  have hmin_deriv : ∀ c : ℝ, c ≠ x →
      HasDerivAt (fun u : ℝ ↦ min x u) ((Iic x).indicator 1 c) c := fun c hc ↦ by
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · rw [indicator_of_mem (mem_Iic.mpr hlt.le), Pi.one_apply]
      exact (hasDerivAt_id c).congr_of_eventuallyEq
        (by filter_upwards [Iio_mem_nhds hlt] with u hu; exact min_eq_right (mem_Iio.mp hu).le)
    · rw [indicator_of_notMem (fun h ↦ not_lt_of_ge (mem_Iic.mp h) hgt)]
      exact (hasDerivAt_const c x).congr_of_eventuallyEq
        (by filter_upwards [Ioi_mem_nhds hgt] with u hu; exact min_eq_left (mem_Ioi.mp hu).le)
  have hR_deriv : ∀ c : ℝ, c ≠ x → HasDerivAt R (c * f c - w * f w) c := fun c hc ↦
    (((hasDerivAt_normalSteinSolKolm_of_ne x hc).sub_const (f w)).sub
      (((hasDerivAt_id c).sub_const w).mul_const (w * f w - stdNormalCDF x)) |>.sub
      ((hmin_deriv c hc).sub_const (min x w))).congr_deriv (by ring)
  have hR'_le : ∀ c : ℝ, |c * f c - w * f w| ≤ M * |c - w| := fun c ↦ by
    have h := abs_mul_normalSteinSolKolm_sub_le x (c - w) 0 w
    rwa [show w + (c - w) = c by ring, add_zero, abs_zero, add_zero] at h
  have hquad : ∀ s : ℝ, |s| = 1 → ∀ u : ℝ, 0 ≤ M * ((u - w) ^ 2 / 2) + s * R u := fun s hs_abs ↦ by
    let G : ℝ → ℝ := fun u ↦ M * ((u - w) ^ 2 / 2) + s * R u
    have hG_cont : Continuous G := by
      have : Continuous f := continuous_normalSteinSolKolm x
      have : Continuous (fun u : ℝ ↦ min x u) := continuous_const.min continuous_id
      fun_prop
    have hG_w : G w = 0 := by simp [G, hR_w]
    have hG_deriv : ∀ c : ℝ, c ≠ x →
        HasDerivAt G (M * (c - w) + s * (c * f c - w * f w)) c := fun c hc ↦
      ((((((hasDerivAt_id c).sub_const w).pow 2).div_const 2).const_mul M).congr_deriv
        (by simp)).add ((hR_deriv c hc).const_mul s)
    have hno_x_right : ∀ a b : ℝ, w ≤ a → a < b → (∀ c ∈ Ioo a b, c ≠ x) → G a ≤ G b :=
      fun a b hwa hab hne ↦ by
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G _ hab hG_cont.continuousOn
          fun c hc ↦ hG_deriv c (hne c hc)
        have hbnd : |s * (c * f c - w * f w)| ≤ M * (c - w) := by
          rw [abs_mul, hs_abs, one_mul]
          simpa [abs_of_nonneg (by linarith [hc.1] : 0 ≤ c - w)] using hR'_le c
        rw [eq_div_iff (sub_pos.mpr hab).ne'] at hslope
        nlinarith [(abs_le.mp hbnd).1, sub_pos.mpr hab]
    have hno_x_left : ∀ a b : ℝ, a < b → b ≤ w → (∀ c ∈ Ioo a b, c ≠ x) → G b ≤ G a :=
      fun a b hab hbw hne ↦ by
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope G _ hab hG_cont.continuousOn
          fun c hc ↦ hG_deriv c (hne c hc)
        have hbnd : |s * (c * f c - w * f w)| ≤ M * (w - c) := by
          rw [abs_mul, hs_abs, one_mul]
          simpa [show |c - w| = w - c by rw [abs_of_nonpos (by linarith [hc.2])]; ring] using
            hR'_le c
        rw [eq_div_iff (sub_pos.mpr hab).ne'] at hslope
        nlinarith [(abs_le.mp hbnd).2, sub_pos.mpr hab]
    intro u; rw [← hG_w]; rcases lt_trichotomy w u with hwu | rfl | huw
    · by_cases hux : u ≤ x
      · exact hno_x_right w u le_rfl hwu fun c hc ↦ (hc.2.trans_le hux).ne
      · by_cases hxw : x ≤ w
        · exact hno_x_right w u le_rfl hwu fun c hc ↦ (hxw.trans_lt hc.1).ne'
        · push Not at hux hxw
          exact (hno_x_right w x le_rfl hxw fun _ hc ↦ hc.2.ne).trans
            (hno_x_right x u hxw.le hux fun _ hc ↦ hc.1.ne')
    · exact le_rfl
    · by_cases hwx : w ≤ x
      · exact hno_x_left u w huw le_rfl fun c hc ↦ (hc.2.trans_le hwx).ne
      · by_cases hxu : x ≤ u
        · exact hno_x_left u w huw le_rfl fun c hc ↦ (hxu.trans_lt hc.1).ne'
        · push Not at hwx hxu
          exact (hno_x_left x w hwx le_rfl fun _ hc ↦ hc.1.ne').trans
            (hno_x_left u x hxu hwx.le fun _ hc ↦ hc.2.ne)
  rw [show (f w - f w') - (w - w') * (w * f w - stdNormalCDF x) - (min x w - min x w') = -R w' by
    dsimp [R]; ring, abs_neg, show (w - w') ^ 2 = (w' - w) ^ 2 by ring]
  exact abs_le.mpr ⟨by linarith [hquad 1 (by norm_num) w'],
    by linarith [hquad (-1) (by norm_num) w']⟩

private noncomputable def monoRamp (y δ w : ℝ) : ℝ := max (y - δ) (min (y + 2 * δ) w) - (y + δ / 2)
private lemma monoRamp_monotone (y δ : ℝ) : Monotone (monoRamp y δ) :=
  fun _ _ huv ↦ sub_le_sub_right (max_le_max_left _ (min_le_min_left _ huv)) _
private lemma abs_monoRamp_le (y : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (w : ℝ) :
    |monoRamp y δ w| ≤ 3 * δ / 2 := by
  unfold monoRamp; exact abs_le.mpr ⟨by linarith [le_max_left (y - δ) (min (y + 2 * δ) w)],
    by linarith [max_le (by linarith : y - δ ≤ y + 2 * δ) (min_le_left (y + 2 * δ) w)]⟩

private lemma sameSign_indicator_Ioc_le_monoRamp (y : ℝ) {δ w w' d' : ℝ}
    (hdiff : |w - w'| ≤ δ) (hsign : 0 ≤ d' * (w - w')) :
    d' * (w - w') * (Ioc y (y + δ)).indicator 1 w ≤ d' * (monoRamp y δ w - monoRamp y δ w') := by
  by_cases hw : w ∈ Ioc y (y + δ)
  · rw [indicator_of_mem hw, Pi.one_apply, mul_one]
    obtain ⟨hw1, hw2⟩ := mem_Ioc.mp hw; obtain ⟨hd1, hd2⟩ := abs_le.mp hdiff
    have hgw : monoRamp y δ w = w - (y + δ / 2) := by
      unfold monoRamp; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    have hgw' : monoRamp y δ w' = w' - (y + δ / 2) := by
      unfold monoRamp; rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    rw [hgw, hgw']; exact le_of_eq (by ring)
  · rw [indicator_of_notMem hw, mul_zero]; rcases lt_trichotomy w' w with hlt | rfl | hgt
    · exact mul_nonneg (nonneg_of_mul_nonneg_left hsign (sub_pos.mpr hlt))
        (sub_nonneg.mpr (monoRamp_monotone y δ hlt.le))
    · simp
    · exact mul_nonneg_of_nonpos_of_nonpos (nonpos_of_mul_nonneg_left hsign (sub_neg.mpr hgt))
        (sub_nonpos.mpr (monoRamp_monotone y δ hgt.le))

private lemma sameSign_min_remainder_bounds (x : ℝ) {δ w w' d' : ℝ}
    (hdiff : |w - w'| ≤ δ) (hsign : 0 ≤ d' * (w - w')) :
    -(d' * (w - w') * (Ioc (x - δ) x).indicator 1 w) ≤
        d' * ((min x w - min x w') - (w - w') * (Iic x).indicator 1 w) ∧
      d' * ((min x w - min x w') - (w - w') * (Iic x).indicator 1 w) ≤
        d' * (w - w') * (Ioc x (x + δ)).indicator 1 w := by
  obtain ⟨hd1, hd2⟩ := abs_le.mp hdiff
  have hnn_lo : 0 ≤ d' * (w - w') * (Ioc (x - δ) x).indicator 1 w := by
    by_cases hw : w ∈ Ioc (x - δ) x <;> simp [hw, hsign]
  have hnn_hi : 0 ≤ d' * (w - w') * (Ioc x (x + δ)).indicator 1 w := by
    by_cases hw : w ∈ Ioc x (x + δ) <;> simp [hw, hsign]
  by_cases hw : w ≤ x
  · rw [indicator_of_mem (mem_Iic.mpr hw), Pi.one_apply, mul_one, min_eq_right hw]
    by_cases hw' : w' ≤ x
    · rw [min_eq_right hw', show d' * ((w - w') - (w - w')) = 0 by ring]
      exact ⟨by linarith, hnn_hi⟩
    · push Not at hw'
      rw [min_eq_left hw'.le, indicator_of_mem (mem_Ioc.mpr ⟨by linarith, hw⟩),
        indicator_of_notMem (fun h : w ∈ Ioc x (x + δ) ↦ not_lt_of_ge hw (mem_Ioc.mp h).1),
        Pi.one_apply, mul_one, mul_zero]
      have hd'_np : d' ≤ 0 := nonpos_of_mul_nonneg_left hsign (by linarith)
      exact ⟨by linarith [mul_nonneg_of_nonpos_of_nonpos hd'_np (by linarith : w - x ≤ 0)],
        mul_nonpos_of_nonpos_of_nonneg hd'_np (by linarith)⟩
  · have hwx : w ∉ Iic x := hw; push Not at hw
    rw [indicator_of_notMem hwx, mul_zero, sub_zero, min_eq_left hw.le]
    by_cases hw' : w' ≤ x
    · rw [min_eq_right hw', indicator_of_mem (mem_Ioc.mpr ⟨hw, by linarith⟩),
        indicator_of_notMem (fun h : w ∈ Ioc (x - δ) x ↦ not_lt_of_ge (mem_Ioc.mp h).2 hw),
        Pi.one_apply, mul_one, mul_zero]
      have hd'_nn : 0 ≤ d' := nonneg_of_mul_nonneg_left hsign (by linarith)
      exact ⟨by linarith [mul_nonneg hd'_nn (by linarith : 0 ≤ x - w')],
        by linarith [mul_nonneg hd'_nn (by linarith : 0 ≤ w - x)]⟩
    · push Not at hw'; rw [min_eq_left hw'.le, sub_self, mul_zero]; exact ⟨by linarith, hnn_hi⟩

/-- Monotone coordinate-replacement normal approximation bound in Kolmogorov distance on finite
Bernoulli product spaces (`SteinIntro.tex:935-941`, `1745-1812`). -/
theorem monotone_pi_kolmogorovDist_le {K : ℕ} (μ₀ : Measure Bool) [IsProbabilityMeasure μ₀]
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : Ω' → ℝ} (hZ : AEMeasurable Z P') (hZ_law : P'.map Z = stdNormalLaw)
    {W : BitVec K → ℝ} {C : Fin K → BitVec K → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hW0 : ∫ x, W x ∂bitPi K μ₀ = 0) (hWvar : variance W (bitPi K μ₀) = 1)
    (hdiff : ∀ (k : Fin K) (x : BitVec K) (b : Bool),
      W x - W (Function.update x k b) = (bitVal (x k) - bitVal b) * C k x)
    (hC_bdd : ∀ (k : Fin K) (x : BitVec K), 0 ≤ C k x ∧ C k x ≤ δ) :
    let TA : BitVec K × BitVec K → ℝ := fun z ↦
      (1 / 2 : ℝ) * ∑ k : Fin K,
        (bitVal (z.1 k) - bitVal (z.2 k)) ^ 2 * C k z.1 * C k (hybVec k.1 z)
    kolmogorovDist ((bitPi K μ₀).map W) (P'.map Z) ≤
      ENNReal.ofReal ((1 + δ) * Real.sqrt (variance TA (bitProd K μ₀)) + 5 * δ / 2) := by
  intro TA; set ν := bitPi K μ₀; set P₂ := bitProd K μ₀
  have hfst : P₂.map Prod.fst = ν := Measure.fst_prod
  have hDk : ∀ k z, W z.1 - W (updVec k z) = (bitVal (z.1 k) - bitVal (z.2 k)) * C k z.1 :=
    fun k z ↦ hdiff k z.1 (z.2 k)
  have hDk' : ∀ k z, W (hybVec k.1 z) - W (hybVec (k.1 + 1) z) =
      (bitVal (z.1 k) - bitVal (z.2 k)) * C k (hybVec k.1 z) := fun k z ↦ by
    have hupd : hybVec (k.1 + 1) z = Function.update (hybVec k.1 z) k (z.2 k) := by
      ext i; by_cases hik : i = k
      · subst hik; simp [hybVec]
      · have hval : i.1 ≠ k.1 := fun h ↦ hik (Fin.ext h)
        by_cases hlt : i.1 < k.1
        · simp [hybVec, hik, hlt, Nat.lt_succ_of_lt hlt]
        · have hlt' : ¬ i.1 < k.1 + 1 := by omega
          simp [hybVec, hik, hlt, hlt']
    rw [hupd, hdiff k (hybVec k.1 z) (z.2 k), show hybVec k.1 z k = z.1 k by simp [hybVec]]
  have hterm_eq : ∀ k z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * (W z.1 - W (updVec k z)) =
      (bitVal (z.1 k) - bitVal (z.2 k)) ^ 2 * C k z.1 * C k (hybVec k.1 z) :=
    fun k z ↦ by rw [hDk k z, hDk' k z]; ring
  have hsign : ∀ k z, 0 ≤ (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * (W z.1 - W (updVec k z)) :=
    fun k z ↦ by
      rw [hterm_eq k z]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (hC_bdd k _).1) (hC_bdd k _).1
  have habs_Dk : ∀ (k : Fin K) (z : BitVec K × BitVec K), |W z.1 - W (updVec k z)| ≤ δ := by
    intro k z; rw [hDk k z, abs_mul, abs_of_nonneg (hC_bdd k z.1).1]
    nlinarith [abs_bitVal_sub_le_one (z.1 k) (z.2 k), (hC_bdd k z.1).1, (hC_bdd k z.1).2]
  have hcubic_le : ∀ (k : Fin K) (z : BitVec K × BitVec K),
      |W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)| * (W z.1 - W (updVec k z)) ^ 2 ≤
        δ * ((bitVal (z.1 k) - bitVal (z.2 k)) ^ 2 * C k z.1 * C k (hybVec k.1 z)) := by
    intro k z; rw [hDk k z, hDk' k z]
    have hc1 := hC_bdd k z.1; have hc2 := hC_bdd k (hybVec k.1 z)
    cases z.1 k <;> cases z.2 k <;> simp [bitVal, abs_of_nonneg hc2.1] <;>
      nlinarith [mul_nonneg hc1.1 hc2.1]
  have hW_sq_int : ∫ x, W x ^ 2 ∂ν = 1 := by
    rw [← variance_of_integral_eq_zero Measurable.of_discrete.aemeasurable hW0, hWvar]
  have hTA_mean : ∫ z, TA z ∂P₂ = 1 := by
    dsimp only [TA]; simp_rw [← hterm_eq]
    rw [integral_const_mul, integral_finsetSum Finset.univ fun _ _ ↦ finite_discrete_integrable _]
    have hchat := pi_chatterjee_identity μ₀ W hW0 id; simp only [id_eq] at hchat
    rw [← hchat, show (fun x : BitVec K ↦ W x * W x) = fun x ↦ W x ^ 2 from
      funext fun x ↦ (sq (W x)).symm, hW_sq_int]
  have hW_abs_le : ∫ x, |W x| ∂ν ≤ 1 :=
    integral_abs_le_one_of_integral_eq_zero_of_variance_eq_one ν MemLp.of_discrete hW0 hWvar
  have hlift : ∀ ψ : BitVec K → ℝ, (∫ x, ψ x ∂ν) = ∫ z, ψ z.1 ∂P₂ := fun ψ ↦ by
    have hm := integral_map (μ := P₂) (φ := Prod.fst) measurable_fst.aemeasurable
      (f := ψ) Measurable.of_discrete.aestronglyMeasurable
    rwa [hfst] at hm
  have hramp_bound : ∀ y : ℝ,
      ∫ z, TA z * (Ioc y (y + δ)).indicator 1 (W z.1) ∂P₂ ≤ 3 * δ / 2 := fun y ↦ by
    have hpt : ∀ z : BitVec K × BitVec K, TA z * (Ioc y (y + δ)).indicator 1 (W z.1) ≤
        (1 / 2 : ℝ) * ∑ k : Fin K, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
          (monoRamp y δ (W z.1) - monoRamp y δ (W (updVec k z))) := fun z ↦ by
      dsimp only [TA]; simp_rw [← hterm_eq]; rw [mul_assoc, Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦
        sameSign_indicator_Ioc_le_monoRamp y (habs_Dk k z) (hsign k z)) (by positivity)
    have hle := integral_mono (μ := P₂) (finite_discrete_integrable _)
      (finite_discrete_integrable _) hpt
    rw [integral_const_mul, integral_finsetSum Finset.univ fun _ _ ↦ finite_discrete_integrable _,
      ← pi_chatterjee_identity μ₀ W hW0 (monoRamp y δ)] at hle
    have h1 : ∫ x, W x * monoRamp y δ (W x) ∂ν ≤ ∫ x, |W x| * (3 * δ / 2) ∂ν :=
      integral_mono (finite_discrete_integrable _) (finite_discrete_integrable _) fun x ↦
        (le_abs_self _).trans (by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_monoRamp_le y hδ (W x)) (abs_nonneg _))
    rw [integral_mul_const] at h1; exact hle.trans (by nlinarith)
  rw [kolmogorovDist_map_stdNormal_eq_iSup_normalSteinOpLeft ν P'
    Measurable.of_discrete.aemeasurable hZ hZ_law]
  refine iSup_le fun x ↦ ENNReal.ofReal_le_ofReal ?_
  set f := normalSteinSolKolm x; set sdTA : ℝ := Real.sqrt (variance TA P₂)
  have hstein_P₂ : (∫ u, normalSteinOpLeft f (W u) ∂ν) =
      (∫ z, derivWithin f (Iic (W z.1)) (W z.1) ∂P₂) - (1 / 2 : ℝ) * ∑ k : Fin K,
        ∫ z, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
          (f (W z.1) - f (W (updVec k z))) ∂P₂ := by
    unfold normalSteinOpLeft
    rw [integral_sub (finite_discrete_integrable _) (finite_discrete_integrable _),
      hlift (fun u ↦ derivWithin f (Iic (W u)) (W u)), pi_chatterjee_identity μ₀ W hW0 f]
  have hd_eq : ∀ w : ℝ, derivWithin f (Iic w) w =
      w * f w + (Iic x).indicator 1 w - stdNormalCDF x := fun w ↦
    (hasDerivWithinAt_Iic_normalSteinSolKolm x w).derivWithin (uniqueDiffWithinAt_Iic w)
  let RemS : BitVec K × BitVec K → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∑ k : Fin K, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
      ((f (W z.1) - f (W (updVec k z))) -
        (W z.1 - W (updVec k z)) * (W z.1 * f (W z.1) - stdNormalCDF x) -
        (min x (W z.1) - min x (W (updVec k z))))
  let RemI : BitVec K × BitVec K → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∑ k : Fin K, (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
      ((min x (W z.1) - min x (W (updVec k z))) -
        (W z.1 - W (updVec k z)) * (Iic x).indicator 1 (W z.1))
  have hsum_eq : (1 / 2 : ℝ) * (∑ k : Fin K, ∫ z,
        (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) * (f (W z.1) - f (W (updVec k z))) ∂P₂) =
      (∫ z, TA z * derivWithin f (Iic (W z.1)) (W z.1) ∂P₂) +
        (∫ z, RemS z ∂P₂) + (∫ z, RemI z ∂P₂) := by
    rw [← integral_finsetSum Finset.univ fun _ _ ↦ finite_discrete_integrable _,
      ← integral_const_mul,
      ← integral_add (finite_discrete_integrable _) (finite_discrete_integrable _),
      ← integral_add (finite_discrete_integrable _) (finite_discrete_integrable _)]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    dsimp only [TA, RemS, RemI]; simp_rw [← hterm_eq]
    rw [hd_eq (W z.1), mul_assoc, Finset.sum_mul, ← mul_add, ← mul_add,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact congrArg ((1 / 2 : ℝ) * ·) (Finset.sum_congr rfl fun _ _ ↦ by ring)
  have hvar_term : |∫ z, derivWithin f (Iic (W z.1)) (W z.1) * (1 - TA z) ∂P₂| ≤ sdTA := by
    have hpt : ∀ z : BitVec K × BitVec K,
        |derivWithin f (Iic (W z.1)) (W z.1) * (1 - TA z)| ≤ |TA z - ∫ w, TA w ∂P₂| := fun z ↦ by
      rw [abs_mul, hTA_mean, abs_sub_comm 1 (TA z)]
      nlinarith [abs_derivWithin_Iic_normalSteinSolKolm_le_one x (W z.1), abs_nonneg (TA z - 1)]
    set m := ∫ z, |TA z - ∫ w, TA w ∂P₂| ∂P₂
    refine (abs_integral_le_integral_abs.trans
      (integral_mono (finite_discrete_integrable _) (finite_discrete_integrable _) hpt)).trans
      (Real.le_sqrt_of_sq_le ?_)
    have hm_le := integral_mono (μ := P₂) (finite_discrete_integrable _)
      (finite_discrete_integrable _) fun z : BitVec K × BitVec K ↦ show
        2 * m * |TA z - ∫ w, TA w ∂P₂| - m ^ 2 ≤ (TA z - ∫ w, TA w ∂P₂) ^ 2 by
        nlinarith [sq_nonneg (|TA z - ∫ w, TA w ∂P₂| - m), sq_abs (TA z - ∫ w, TA w ∂P₂)]
    rw [integral_sub (finite_discrete_integrable _) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul,
      ← variance_eq_integral Measurable.of_discrete.aemeasurable] at hm_le
    linarith
  have hRemS_term : |∫ z, RemS z ∂P₂| ≤ δ * (1 + sdTA) := by
    have hpt : ∀ z : BitVec K × BitVec K, |RemS z| ≤ (δ / 2) * (|W z.1| + 1) * TA z := fun z ↦ by
      dsimp only [RemS]; rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have hterm : ∀ k : Fin K,
          |(W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
            ((f (W z.1) - f (W (updVec k z))) -
              (W z.1 - W (updVec k z)) * (W z.1 * f (W z.1) - stdNormalCDF x) -
              (min x (W z.1) - min x (W (updVec k z))))| ≤
            (|W z.1| + 1) * (δ / 2) *
              ((bitVal (z.1 k) - bitVal (z.2 k)) ^ 2 * C k z.1 * C k (hybVec k.1 z)) := fun k ↦ by
        rw [abs_mul]
        have hr := (abs_normalSteinSolKolm_rem_le x (W z.1) (W (updVec k z))).trans
          (mul_le_mul_of_nonneg_right (add_le_add_right sqrt_two_pi_div_four_le_one |W z.1|)
            (by positivity))
        nlinarith [mul_le_mul_of_nonneg_left hr
          (abs_nonneg (W (hybVec k.1 z) - W (hybVec (k.1 + 1) z))),
          mul_le_mul_of_nonneg_left (hcubic_le k z) (by positivity : 0 ≤ (|W z.1| + 1) / 2)]
      refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
      refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hterm k)
        (by positivity)).trans (le_of_eq ?_)
      dsimp only [TA]; rw [← Finset.mul_sum]; ring
    have h1 := abs_integral_le_integral_abs.trans
      (integral_mono (μ := P₂) (finite_discrete_integrable _) (finite_discrete_integrable _) hpt)
    rw [show (∫ z, (δ / 2) * (|W z.1| + 1) * TA z ∂P₂) =
        (δ / 2) * (∫ z, (|W z.1| + 1) ∂P₂) +
          (δ / 2) * (∫ z, (|W z.1| + 1) * (TA z - 1) ∂P₂) by
      rw [show (fun z : BitVec K × BitVec K ↦ (δ / 2) * (|W z.1| + 1) * TA z) =
        fun z ↦ (δ / 2) * (|W z.1| + 1) + (δ / 2) * ((|W z.1| + 1) * (TA z - 1)) from
          funext fun _ ↦ by ring,
        integral_add (finite_discrete_integrable _) (finite_discrete_integrable _),
        integral_const_mul, integral_const_mul]] at h1
    have hmean1 : ∫ z, (|W z.1| + 1) ∂P₂ ≤ 2 := by
      rw [← hlift (fun u ↦ |W u| + 1),
        integral_add (finite_discrete_integrable _) (integrable_const 1),
        integral_const, probReal_univ, one_smul]; linarith
    have hcs_prod : ∫ z, (|W z.1| + 1) * (TA z - 1) ∂P₂ ≤ 2 * sdTA := by
      set c := ∫ z, (|W z.1| + 1) * (TA z - 1) ∂P₂
      rcases le_or_gt c 0 with hc0 | hc_pos
      · exact hc0.trans (by positivity)
      · have hsq1 : ∫ z, (|W z.1| + 1) ^ 2 ∂P₂ ≤ 4 := by
          rw [← hlift (fun u ↦ (|W u| + 1) ^ 2),
            show (fun u : BitVec K ↦ (|W u| + 1) ^ 2) = fun u ↦ (W u ^ 2 + 2 * |W u|) + 1 from
              funext fun u ↦ by nlinarith [sq_abs (W u)],
            integral_add (finite_discrete_integrable _) (integrable_const 1),
            integral_add (finite_discrete_integrable _) (finite_discrete_integrable _),
            integral_const_mul, hW_sq_int, integral_const, probReal_univ, one_smul]; linarith
        have hsq2 : ∫ z, (TA z - 1) ^ 2 ∂P₂ = sdTA ^ 2 := by
          rw [Real.sq_sqrt (variance_nonneg _ _),
            variance_eq_integral Measurable.of_discrete.aemeasurable, hTA_mean]
        have hm := integral_mono (μ := P₂) (finite_discrete_integrable _)
          (finite_discrete_integrable _) fun z : BitVec K × BitVec K ↦ show
            (c / 2) * ((|W z.1| + 1) * (TA z - 1)) ≤
              (c ^ 2 / 16) * (|W z.1| + 1) ^ 2 + (TA z - 1) ^ 2 by
            nlinarith [sq_nonneg ((c / 4) * (|W z.1| + 1) - (TA z - 1))]
        rw [integral_const_mul, integral_add (finite_discrete_integrable _)
          (finite_discrete_integrable _), integral_const_mul, hsq2] at hm
        have hc_sq : (c / 2) ^ 2 ≤ sdTA ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hsq1 (by positivity : 0 ≤ c ^ 2 / 16)]
        have hc_half : c / 2 ≤ sdTA := by
          simpa [sdTA] using Real.le_sqrt_of_sq_le
            (hc_sq.trans_eq (Real.sq_sqrt (variance_nonneg _ _)))
        linarith
    nlinarith
  have hRemI_term : |∫ z, RemI z ∂P₂| ≤ 3 * δ / 2 := by
    have hlo_pt : ∀ z : BitVec K × BitVec K,
        -(TA z * (Ioc (x - δ) x).indicator 1 (W z.1)) ≤ RemI z := fun z ↦ by
      rw [show -(TA z * (Ioc (x - δ) x).indicator 1 (W z.1)) =
          (1 / 2 : ℝ) * ∑ k : Fin K, -((W (hybVec k.1 z) - W (hybVec (k.1 + 1) z)) *
            (W z.1 - W (updVec k z)) * (Ioc (x - δ) x).indicator 1 (W z.1)) by
        dsimp only [TA]; simp_rw [← hterm_eq]
        rw [mul_assoc, Finset.sum_mul, ← mul_neg, ← Finset.sum_neg_distrib]]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦
        (sameSign_min_remainder_bounds x (habs_Dk k z) (hsign k z)).1) (by positivity)
    have hhi_pt : ∀ z : BitVec K × BitVec K,
        RemI z ≤ TA z * (Ioc x (x + δ)).indicator 1 (W z.1) := fun z ↦ by
      dsimp only [TA, RemI]; simp_rw [← hterm_eq]; rw [mul_assoc, Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦
        (sameSign_min_remainder_bounds x (habs_Dk k z) (hsign k z)).2) (by positivity)
    have hlo := integral_mono (μ := P₂) (finite_discrete_integrable _)
      (finite_discrete_integrable _) hlo_pt
    have hhi := integral_mono (μ := P₂) (finite_discrete_integrable _)
      (finite_discrete_integrable _) hhi_pt
    rw [integral_neg] at hlo
    have hb1 := hramp_bound (x - δ); rw [sub_add_cancel] at hb1
    exact abs_le.mpr ⟨by linarith, hhi.trans (hramp_bound x)⟩
  have hcomb : (∫ u, normalSteinOpLeft f (W u) ∂ν) =
      (∫ z, derivWithin f (Iic (W z.1)) (W z.1) * (1 - TA z) ∂P₂) -
        (∫ z, RemS z ∂P₂) - (∫ z, RemI z ∂P₂) := by
    rw [hstein_P₂, hsum_eq]
    have h1 : (∫ z, derivWithin f (Iic (W z.1)) (W z.1) ∂P₂) -
        (∫ z, TA z * derivWithin f (Iic (W z.1)) (W z.1) ∂P₂) =
        ∫ z, derivWithin f (Iic (W z.1)) (W z.1) * (1 - TA z) ∂P₂ := by
      rw [← integral_sub (finite_discrete_integrable _) (finite_discrete_integrable _)]
      exact integral_congr_ae (ae_of_all _ fun _ ↦ by ring)
    linarith
  rw [hcomb]
  set I₁ := ∫ z, derivWithin f (Iic (W z.1)) (W z.1) * (1 - TA z) ∂P₂
  set I₂ := ∫ z, RemS z ∂P₂; set I₃ := ∫ z, RemI z ∂P₂
  linarith [abs_sub (I₁ - I₂) I₃, abs_sub I₁ I₂, hvar_term, hRemS_term, hRemI_term]

end SteinMethod
