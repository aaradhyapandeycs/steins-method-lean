/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Geometric.Equilibrium
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Uniform Attachment Random Digraphs and Geometric In-Degree

Develops Section 6.3 (*Uniform attachment*, `SteinIntro.tex:3331-3388`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* Measurability, injectivity, probability-measure, and cylinder-probability guards for
  `Digraph (Fin n)`, `digraphOfTargets`, `uniformAttachment`, and `digraphInDegree`.
* Discrete equilibrium coupling `We ω := {u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard` for the
  in-degree `W ω := digraphInDegree (G ω) (I ω)` of an independent uniformly chosen vertex `I` in
  `G ~ uniformAttachment n`, satisfying `IsDiscreteEquilibrium P (1 / 2) W P We` and
  `|(We ω : ℝ) - (W ω : ℝ)| = if (G ω).Adj (I ω) (I ω) then 1 else 0`.
* **Theorem 6.6** (`\label{thm1716}`, `SteinIntro.tex:3345-3350`; `ISSUE-TYPO-6.6`, `ISSUE-6.6`):
  both the sharp bound $d_{\mathrm{TV}}(W, \mathrm{Ge}^0(1/2)) \le \frac{\log(n) + 1}{n}$ and the
  printed bound $\frac{2(\log(n) + 1)}{n}$ for all $n \ge 1$.
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-! ### Non-vacuity, measurability, injectivity, and cylinder formulas for `uniformAttachment` -/

/-- `Digraph.Adj` is measurable with respect to the pullback measurable space
`instMeasurableSpaceDigraph` (`SteinIntro.tex:3334-3341`). -/
theorem measurable_digraph_adj {V : Type*} :
    Measurable (Digraph.Adj : Digraph V → V → V → Prop) :=
  comap_measurable _

/-- Every subset of `Digraph (Fin n)` is measurable (`SteinIntro.tex:3334-3341`). -/
instance instDiscreteMeasurableSpaceDigraphFin (n : ℕ) :
    DiscreteMeasurableSpace (Digraph (Fin n)) :=
  ⟨fun s ↦ ⟨Digraph.Adj '' s, .of_discrete, Set.preimage_image_eq s Digraph.adj_injective⟩⟩

private instance instDiscreteMeasurableSpaceFinProdDigraph (n : ℕ) :
    DiscreteMeasurableSpace (Fin n × Digraph (Fin n)) := ⟨fun s ↦ by
  have hs : s = ⋃ k : Fin n, ({k} : Set (Fin n)) ×ˢ {G : Digraph (Fin n) | (k, G) ∈ s} := by
    ext ⟨k, G⟩
    simp
  rw [hs]
  exact MeasurableSet.iUnion fun k ↦
    (MeasurableSet.of_discrete : MeasurableSet ({k} : Set (Fin n))).prod .of_discrete⟩

/-- `digraphOfTargets` is measurable (`SteinIntro.tex:3334-3341`). -/
theorem measurable_digraphOfTargets {n : ℕ} : Measurable (digraphOfTargets (n := n)) :=
  .of_discrete

/-- `digraphOfTargets` is injective: each vertex `u` has a unique outgoing edge pointing to `t u`
(`SteinIntro.tex:3334-3341`). -/
theorem digraphOfTargets_injective {n : ℕ} : Function.Injective (digraphOfTargets (n := n)) := by
  intro t₁ t₂ h
  funext u
  let v : Fin n := ⟨(t₁ u).val, Nat.lt_of_lt_of_le (t₁ u).isLt (Nat.succ_le_of_lt u.isLt)⟩
  have hadj₁ : (digraphOfTargets t₁).Adj u v := rfl
  have hadj₂ : (digraphOfTargets t₂).Adj u v := h ▸ hadj₁
  exact Fin.ext hadj₂.symm

private abbrev TargetVec (n : ℕ) : Type :=
  ∀ k : Fin n, Fin (k.val + 1)

private noncomputable def unifFinMeasure (m : ℕ) (hm : 0 < m) : Measure (Fin m) :=
  (@PMF.uniformOfFintype (Fin m) inferInstance ⟨⟨0, hm⟩⟩).toMeasure

private instance instIsProbabilityMeasureUnifFinMeasure (m : ℕ) (hm : 0 < m) :
    IsProbabilityMeasure (unifFinMeasure m hm) := by
  unfold unifFinMeasure
  infer_instance

private lemma unifFinMeasure_singleton {m : ℕ} (hm : 0 < m) (x : Fin m) :
    unifFinMeasure m hm {x} = 1 / (m : ℝ≥0∞) := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [unifFinMeasure, PMF.toMeasure_uniformOfFintype_apply _ .of_discrete]
  simp

private lemma unifFinMeasure_real_singleton {m : ℕ} (hm : 0 < m) (x : Fin m) :
    (unifFinMeasure m hm).real {x} = (m : ℝ)⁻¹ := by
  rw [measureReal_def, unifFinMeasure_singleton hm x, one_div, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

private noncomputable def targetMeasure (n : ℕ) : Measure (TargetVec n) :=
  Measure.pi fun k : Fin n ↦ unifFinMeasure (k.val + 1) (Nat.succ_pos _)

private instance instIsProbabilityMeasureTargetMeasure (n : ℕ) :
    IsProbabilityMeasure (targetMeasure n) := by
  unfold targetMeasure
  infer_instance

/-- `uniformAttachment n` is a probability measure on `Digraph (Fin n)` for every `n : ℕ`
(Section 6.3, `SteinIntro.tex:3334-3341`). -/
instance instIsProbabilityMeasureUniformAttachment (n : ℕ) :
    IsProbabilityMeasure (uniformAttachment n) := by
  change IsProbabilityMeasure ((targetMeasure n).map digraphOfTargets)
  exact (Measure.isProbabilityMeasure_map_iff measurable_digraphOfTargets.aemeasurable).mpr
    inferInstance

/-- Cylinder edge probability of `uniformAttachment n` in `ℝ≥0∞`:
$\mathbb{P}(u \to v) = \frac{1}{u + 1}$ if $v \le u$, and $0$ if $v > u$
(Section 6.3, `SteinIntro.tex:3334-3341`). -/
theorem uniformAttachment_adj {n : ℕ} (u v : Fin n) :
    uniformAttachment n {G : Digraph (Fin n) | G.Adj u v} =
      if v ≤ u then 1 / ((u.val : ℝ≥0∞) + 1) else 0 := by
  change (targetMeasure n).map digraphOfTargets {G : Digraph (Fin n) | G.Adj u v} = _
  rw [Measure.map_apply measurable_digraphOfTargets .of_discrete]
  have hpre : digraphOfTargets ⁻¹' {G : Digraph (Fin n) | G.Adj u v} =
      Function.eval u ⁻¹' {x : Fin (u.val + 1) | x.val = v.val} := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply u) .of_discrete]
  have heval : (targetMeasure n).map (Function.eval u) =
      unifFinMeasure (u.val + 1) (Nat.succ_pos _) :=
    (measurePreserving_eval (fun k : Fin n ↦ unifFinMeasure (k.val + 1) (Nat.succ_pos _)) u).map_eq
  rw [heval]
  by_cases hvu : v ≤ u
  · rw [ite_eq_left hvu]
    let x₀ : Fin (u.val + 1) := ⟨v.val, Nat.lt_succ_of_le (Fin.le_def.mp hvu)⟩
    have hset : {x : Fin (u.val + 1) | x.val = v.val} = {x₀} := by
      ext x
      exact ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩
    rw [hset, unifFinMeasure_singleton (Nat.succ_pos _) x₀, Nat.cast_succ]
  · rw [ite_eq_right hvu]
    have hlt : u.val < v.val := Nat.lt_of_not_ge (mt Fin.le_def.mpr hvu)
    have hset : {x : Fin (u.val + 1) | x.val = v.val} = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      change x.val ≠ v.val
      omega
    rw [hset, measure_empty]

/-- Real cylinder edge probability of `uniformAttachment n`:
$\mathbb{P}(u \to v) = \frac{1}{u + 1}$ if $v \le u$, and $0$ if $v > u$
(Section 6.3, `SteinIntro.tex:3334-3341`). -/
theorem uniformAttachment_real_adj {n : ℕ} (u v : Fin n) :
    (uniformAttachment n).real {G : Digraph (Fin n) | G.Adj u v} =
      if v ≤ u then 1 / ((u.val : ℝ) + 1) else 0 := by
  rw [measureReal_def, uniformAttachment_adj u v]
  split_ifs with hvu
  · rw [one_div, ENNReal.toReal_inv,
      ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one, one_div]
  · exact ENNReal.toReal_zero

/-! ### Uniformity of `targetMeasure` and Symmetry/Recurrence Identities -/

private lemma targetMeasure_real_singleton {n : ℕ} (t : TargetVec n) :
    (targetMeasure n).real {t} = (Fintype.card (TargetVec n) : ℝ)⁻¹ := by
  have hpi : ∀ s : TargetVec n,
      (targetMeasure n).real {s} = ∏ u : Fin n, (((u.val : ℝ) + 1)⁻¹) := fun s ↦ by
    have hset : ({s} : Set (TargetVec n)) = Set.univ.pi fun u ↦ {s u} := by
      ext s'
      simp [funext_iff]
    have henn : targetMeasure n {s} =
        ∏ u : Fin n, (1 / ((u.val : ℝ≥0∞) + 1)) := by
      rw [hset, targetMeasure, Measure.pi_pi]
      refine Finset.prod_congr rfl fun u _ ↦ ?_
      rw [unifFinMeasure_singleton (Nat.succ_pos _) (s u), Nat.cast_succ]
    rw [measureReal_def, henn, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun u _ ↦ ?_
    rw [one_div, ENNReal.toReal_inv,
      ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one]
  have hsum1 : ∑ s : TargetVec n, (targetMeasure n).real {s} = 1 := by
    have h := integral_fintype (integrable_const (μ := targetMeasure n) (1 : ℝ))
    rw [integral_const, probReal_univ, one_smul] at h
    simpa only [smul_eq_mul, mul_one] using h.symm
  simp_rw [hpi] at hsum1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum1
  rw [hpi t]
  have hcard_ne : (Fintype.card (TargetVec n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact eq_inv_of_mul_eq_one_right hsum1

private lemma integral_targetMeasure_equiv {n : ℕ} (e : TargetVec n ≃ TargetVec n)
    (g : TargetVec n → ℝ) :
    ∫ t, g (e t) ∂(targetMeasure n) = ∫ t, g t ∂(targetMeasure n) := by
  rw [integral_fintype (Integrable.of_finite), integral_fintype (Integrable.of_finite)]
  simp_rw [targetMeasure_real_singleton, smul_eq_mul]
  exact e.sum_comp (fun t ↦ (Fintype.card (TargetVec n) : ℝ)⁻¹ * g t)

private def zeroTailCount {n : ℕ} (m : ℕ) (t : TargetVec n) : ℕ :=
  (Finset.univ.filter fun u : Fin n ↦ m ≤ u.val ∧ (t u).val = 0).card

private lemma zeroTailCount_eq_zero {n : ℕ} (t : TargetVec n) :
    zeroTailCount n t = 0 := by
  simp only [zeroTailCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ,
    true_imp_iff, not_and]
  intro u hu
  exact absurd hu (not_le_of_gt u.isLt)

private lemma zeroTailCount_update_succ {n : ℕ} (k : Fin n) (t : TargetVec n)
    (y : Fin (k.val + 1)) :
    zeroTailCount (k.val + 1) (Function.update t k y) = zeroTailCount (k.val + 1) t := by
  simp only [zeroTailCount]
  congr 1
  refine Finset.filter_congr fun u _ ↦ ?_
  by_cases huk : u = k
  · subst huk
    have hnot : ¬ (u.val + 1 ≤ u.val) := by omega
    simp [hnot]
  · rw [Function.update_of_ne huk]

private lemma zeroTailCount_update_self {n : ℕ} (k : Fin n) (t : TargetVec n)
    (y : Fin (k.val + 1)) :
    zeroTailCount k.val (Function.update t k y) =
      zeroTailCount (k.val + 1) t + if y.val = 0 then 1 else 0 := by
  classical
  let s₁ := Finset.univ.filter fun u : Fin n ↦ k.val + 1 ≤ u.val ∧ (t u).val = 0
  have hnot_mem : k ∉ s₁ := by
    simp [s₁]
  by_cases hy : y.val = 0
  · rw [ite_eq_left hy]
    have hset : (Finset.univ.filter fun u : Fin n ↦
        k.val ≤ u.val ∧ (Function.update t k y u).val = 0) = insert k s₁ := by
      ext u
      simp only [s₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases huk : u = k
      · subst huk
        simp [hy]
      · rw [Function.update_of_ne huk]
        have hne_val : u.val ≠ k.val := fun h ↦ huk (Fin.ext h)
        constructor
        · rintro ⟨hle, h0⟩
          exact Or.inr ⟨by omega, h0⟩
        · rintro (rfl | ⟨hle, h0⟩)
          · exact absurd rfl huk
          · exact ⟨by omega, h0⟩
    change (Finset.univ.filter _).card = s₁.card + 1
    rw [hset, Finset.card_insert_of_notMem hnot_mem]
  · rw [ite_eq_right hy, add_zero]
    have hset : (Finset.univ.filter fun u : Fin n ↦
        k.val ≤ u.val ∧ (Function.update t k y u).val = 0) = s₁ := by
      ext u
      simp only [s₁, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases huk : u = k
      · subst huk
        simp [hy]
      · rw [Function.update_of_ne huk]
        have hne_val : u.val ≠ k.val := fun h ↦ huk (Fin.ext h)
        exact ⟨fun ⟨hle, h0⟩ ↦ ⟨by omega, h0⟩, fun ⟨hle, h0⟩ ↦ ⟨by omega, h0⟩⟩
    change (Finset.univ.filter _).card = s₁.card
    rw [hset]

private lemma integral_zeroTailCount_step {n : ℕ} (k : Fin n) (f : ℕ → ℝ) :
    ((k.val : ℝ) + 1) *
        ((∫ t, f (zeroTailCount k.val t) ∂(targetMeasure n)) -
          ∫ t, f (zeroTailCount (k.val + 1) t) ∂(targetMeasure n)) =
      ∫ t, fwdDiff 1 f (zeroTailCount (k.val + 1) t) ∂(targetMeasure n) := by
  classical
  let shiftEquiv (x : Fin (k.val + 1)) : TargetVec n ≃ TargetVec n :=
    { toFun := fun t ↦ Function.update t k (t k + x)
      invFun := fun t ↦ Function.update t k (t k - x)
      left_inv := fun t ↦ by
        ext u
        by_cases huk : u = k
        · subst huk; simp
        · simp [Function.update_of_ne huk]
      right_inv := fun t ↦ by
        ext u
        by_cases huk : u = k
        · subst huk; simp
        · simp [Function.update_of_ne huk] }
  have hsum_eq :
      ∑ x : Fin (k.val + 1), ∫ t, f (zeroTailCount k.val t) ∂(targetMeasure n) =
        ∫ t, (∑ x : Fin (k.val + 1),
          f (zeroTailCount k.val (Function.update t k (t k + x)))) ∂(targetMeasure n) := by
    calc
      ∑ x : Fin (k.val + 1), ∫ t, f (zeroTailCount k.val t) ∂(targetMeasure n)
        = ∑ x : Fin (k.val + 1),
            ∫ t, f (zeroTailCount k.val (shiftEquiv x t)) ∂(targetMeasure n) :=
          Finset.sum_congr rfl fun x _ ↦ (integral_targetMeasure_equiv (shiftEquiv x) _).symm
      _ = ∫ t, (∑ x : Fin (k.val + 1),
            f (zeroTailCount k.val (shiftEquiv x t))) ∂(targetMeasure n) :=
          (integral_finsetSum Finset.univ fun _ _ ↦ Integrable.of_finite).symm
  have hLHS :
      ∑ _x : Fin (k.val + 1), ∫ t, f (zeroTailCount k.val t) ∂(targetMeasure n) =
        ((k.val : ℝ) + 1) * ∫ t, f (zeroTailCount k.val t) ∂(targetMeasure n) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
  have hinner : ∀ t : TargetVec n,
      (∑ x : Fin (k.val + 1), f (zeroTailCount k.val (Function.update t k (t k + x)))) =
        ((k.val : ℝ) + 1) * f (zeroTailCount (k.val + 1) t) +
          fwdDiff 1 f (zeroTailCount (k.val + 1) t) := fun t ↦ by
    have hbij : (∑ x : Fin (k.val + 1),
        f (zeroTailCount k.val (Function.update t k (t k + x)))) =
        ∑ y : Fin (k.val + 1), f (zeroTailCount k.val (Function.update t k y)) :=
      Equiv.sum_comp (Equiv.addLeft (t k)) (fun y ↦ f (zeroTailCount k.val (Function.update t k y)))
    rw [hbij]
    simp_rw [zeroTailCount_update_self]
    let y₀ : Fin (k.val + 1) := ⟨0, Nat.succ_pos _⟩
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ y₀)]
    have hy₀ : y₀.val = 0 := rfl
    rw [ite_eq_left hy₀]
    have herase : ∑ y ∈ Finset.univ.erase y₀,
        f (zeroTailCount (k.val + 1) t + if y.val = 0 then 1 else 0) =
        (k.val : ℝ) * f (zeroTailCount (k.val + 1) t) := by
      have hcongr : ∑ y ∈ Finset.univ.erase y₀,
          f (zeroTailCount (k.val + 1) t + if y.val = 0 then 1 else 0) =
          ∑ _y ∈ Finset.univ.erase y₀, f (zeroTailCount (k.val + 1) t) := by
        refine Finset.sum_congr rfl fun y hy ↦ ?_
        have hne : y.val ≠ 0 := fun hv ↦
          (Finset.mem_erase.mp hy).1 (Fin.ext hv)
        rw [ite_eq_right hne, add_zero]
      rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ y₀),
        Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, nsmul_eq_mul]
    rw [herase, fwdDiff]
    ring
  rw [hLHS] at hsum_eq
  simp_rw [hinner] at hsum_eq
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_const_mul] at hsum_eq
  linarith

private noncomputable def swapTargetEquiv {n : ℕ} (k : Fin n) : TargetVec n ≃ TargetVec n where
  toFun t u :=
    if h : k.val ≤ u.val then
      Equiv.swap ⟨0, Nat.succ_pos _⟩ ⟨k.val, Nat.lt_succ_of_le h⟩ (t u)
    else
      t u
  invFun t u :=
    if h : k.val ≤ u.val then
      Equiv.swap ⟨0, Nat.succ_pos _⟩ ⟨k.val, Nat.lt_succ_of_le h⟩ (t u)
    else
      t u
  left_inv t := by
    ext u
    dsimp only
    split_ifs with h
    · simp
    · rfl
  right_inv t := by
    ext u
    dsimp only
    split_ifs with h
    · simp
    · rfl

private lemma adj_swapTargetEquiv_iff {n : ℕ} (k u : Fin n) (t : TargetVec n) :
    (digraphOfTargets (swapTargetEquiv k t)).Adj u k ↔ (k.val ≤ u.val ∧ (t u).val = 0) := by
  change ((swapTargetEquiv k t) u).val = k.val ↔ k.val ≤ u.val ∧ (t u).val = 0
  simp only [swapTargetEquiv, Equiv.coe_fn_mk]
  split_ifs with h
  · let z₀ : Fin (u.val + 1) := ⟨0, Nat.succ_pos _⟩
    let zₖ : Fin (u.val + 1) := ⟨k.val, Nat.lt_succ_of_le h⟩
    have hval_k : ∀ x : Fin (u.val + 1), x.val = k.val ↔ x = zₖ :=
      fun x ↦ ⟨fun hx ↦ Fin.ext hx, fun hx ↦ congrArg Fin.val hx⟩
    have hval_0 : ∀ x : Fin (u.val + 1), x.val = 0 ↔ x = z₀ :=
      fun x ↦ ⟨fun hx ↦ Fin.ext hx, fun hx ↦ congrArg Fin.val hx⟩
    rw [hval_k, hval_0, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact ⟨fun ht ↦ ⟨h, ht⟩, fun ⟨_, ht⟩ ↦ ht⟩
  · constructor
    · intro hval
      exact absurd (Nat.lt_of_lt_of_le (hval ▸ (t u).isLt) (by omega)) (lt_irrefl _)
    · rintro ⟨hle, -⟩
      exact absurd hle h

private lemma inDegree_swapTargetEquiv {n : ℕ} (k : Fin n) (t : TargetVec n) :
    digraphInDegree (digraphOfTargets (swapTargetEquiv k t)) k = zeroTailCount k.val t := by
  classical
  rw [digraphInDegree, zeroTailCount, ← Set.ncard_coe_finset]
  congr 1
  ext u
  simp [adj_swapTargetEquiv_iff]

private lemma strictInDegree_swapTargetEquiv {n : ℕ} (k : Fin n) (t : TargetVec n) :
    {u : Fin n | u ≠ k ∧ (digraphOfTargets (swapTargetEquiv k t)).Adj u k}.ncard =
      zeroTailCount (k.val + 1) t := by
  classical
  rw [zeroTailCount, ← Set.ncard_coe_finset]
  congr 1
  ext u
  change (u ≠ k ∧ (digraphOfTargets (swapTargetEquiv k t)).Adj u k) ↔
    u ∈ (Finset.univ.filter fun u : Fin n ↦ k.val + 1 ≤ u.val ∧ (t u).val = 0)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, adj_swapTargetEquiv_iff]
  constructor
  · rintro ⟨hne, hle, h0⟩
    have hne_val : u.val ≠ k.val := fun hv ↦ hne (Fin.ext hv)
    exact ⟨by omega, h0⟩
  · rintro ⟨hle, h0⟩
    refine ⟨fun heq ↦ ?_, by omega, h0⟩
    subst heq
    omega

private lemma sum_ByParts_fin {n : ℕ} (a : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, ((k : ℝ) + 1) * (a k - a (k + 1)) =
      (∑ k ∈ Finset.range n, a k) - (n : ℝ) * a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one]
      ring

/-! ### Discrete Equilibrium Identity and Harmonic Sum Bound -/

private noncomputable def strictInDegree {V : Type*} (G : Digraph V) (v : V) : ℕ :=
  {u : V | u ≠ v ∧ G.Adj u v}.ncard

private lemma digraphInDegree_eq_strictInDegree_add {n : ℕ} (G : Digraph (Fin n)) (v : Fin n) :
    (digraphInDegree G v : ℝ) =
      (strictInDegree G v : ℝ) + ({H : Digraph (Fin n) | H.Adj v v}.indicator 1 G) := by
  classical
  by_cases hloop : G.Adj v v
  · have hmem : G ∈ {H : Digraph (Fin n) | H.Adj v v} := hloop
    have hunion : {u : Fin n | G.Adj u v} = insert v {u : Fin n | u ≠ v ∧ G.Adj u v} := by
      ext u
      by_cases huv : u = v
      · subst huv
        simp [hloop]
      · simp [huv]
    have hnot : v ∉ {u : Fin n | u ≠ v ∧ G.Adj u v} := fun h ↦ h.1 rfl
    rw [digraphInDegree, strictInDegree, hunion,
      Set.ncard_insert_of_notMem hnot (Set.toFinite _), Set.indicator_of_mem hmem,
      Pi.one_apply, Nat.cast_add, Nat.cast_one]
  · have hnot : G ∉ {H : Digraph (Fin n) | H.Adj v v} := hloop
    have heq : {u : Fin n | G.Adj u v} = {u : Fin n | u ≠ v ∧ G.Adj u v} := by
      ext u
      by_cases huv : u = v
      · subst huv
        simp [hloop]
      · simp [huv]
    rw [digraphInDegree, strictInDegree, heq, Set.indicator_of_notMem hnot, add_zero]

private lemma harmonic_sum_le_log_add_one {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) ≤ Real.log (n : ℝ) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hstep : ∀ j : ℕ,
      1 / (((j + 1 : ℕ) : ℝ) + 1) ≤
        Real.log (((j + 1 : ℕ) : ℝ) + 1) - Real.log ((j : ℝ) + 1) := fun j ↦ by
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj2 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) + 1 := by positivity
    have hquot_pos : 0 < (((j + 1 : ℕ) : ℝ) + 1) / ((j : ℝ) + 1) := div_pos hj2 hj1
    have hlog := Real.one_sub_inv_le_log_of_pos hquot_pos
    rw [inv_div, Real.log_div hj2.ne' hj1.ne'] at hlog
    have hsub : 1 - ((j : ℝ) + 1) / (((j + 1 : ℕ) : ℝ) + 1) =
        1 / (((j + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      field_simp [hj2.ne']
      ring
    linarith
  have htel : ∀ k : ℕ,
      ∑ j ∈ Finset.range k,
        (Real.log (((j + 1 : ℕ) : ℝ) + 1) - Real.log ((j : ℝ) + 1)) =
        Real.log ((k : ℝ) + 1) := fun k ↦ by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [Finset.sum_range_succ', Nat.cast_zero, Nat.cast_succ]
  have h0 : (1 : ℝ) / (0 + 1) = 1 := by norm_num
  rw [h0]
  have hsum_le : ∑ j ∈ Finset.range m, 1 / (((j + 1 : ℕ) : ℝ) + 1) ≤
      Real.log ((m : ℝ) + 1) :=
    (Finset.sum_le_sum fun j _ ↦ hstep j).trans_eq (htel m)
  linarith

private lemma uniformAttachment_eq_map (n : ℕ) :
    uniformAttachment n = (targetMeasure n).map digraphOfTargets :=
  rfl

private lemma integral_prod_uniformAttachment {n : ℕ} (hn : 0 < n)
    (φ : Fin n × Digraph (Fin n) → ℝ) :
    ∫ p, φ p ∂((unifFinMeasure n hn).prod (uniformAttachment n)) =
      (n : ℝ)⁻¹ * ∑ k : Fin n, ∫ t, φ (k, digraphOfTargets t) ∂(targetMeasure n) := by
  rw [uniformAttachment_eq_map,
    ← Measure.map_id (μ := unifFinMeasure n hn),
    Measure.map_prod_map (unifFinMeasure n hn) (targetMeasure n)
      measurable_id measurable_digraphOfTargets,
    integral_map (measurable_id.prodMap measurable_digraphOfTargets).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable,
    integral_prod _ Integrable.of_finite, integral_fintype Integrable.of_finite]
  simp_rw [unifFinMeasure_real_singleton hn, smul_eq_mul, ← Finset.mul_sum, Prod.map_apply, id_eq]

private lemma integral_inDegree_prod_step {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) :
    (∫ p : Fin n × Digraph (Fin n), f (digraphInDegree p.2 p.1)
        ∂((unifFinMeasure n hn).prod (uniformAttachment n))) - f 0 =
      ∫ p : Fin n × Digraph (Fin n), fwdDiff 1 f (strictInDegree p.2 p.1)
        ∂((unifFinMeasure n hn).prod (uniformAttachment n)) := by
  have hLHS : ∫ p : Fin n × Digraph (Fin n), f (digraphInDegree p.2 p.1)
        ∂((unifFinMeasure n hn).prod (uniformAttachment n)) =
      (n : ℝ)⁻¹ * ∑ k : Fin n, ∫ t, f (zeroTailCount k.val t) ∂(targetMeasure n) := by
    rw [integral_prod_uniformAttachment hn]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← integral_targetMeasure_equiv (swapTargetEquiv k)]
    simp_rw [inDegree_swapTargetEquiv k]
  have hRHS : ∫ p : Fin n × Digraph (Fin n), fwdDiff 1 f (strictInDegree p.2 p.1)
        ∂((unifFinMeasure n hn).prod (uniformAttachment n)) =
      (n : ℝ)⁻¹ * ∑ k : Fin n,
        ∫ t, fwdDiff 1 f (zeroTailCount (k.val + 1) t) ∂(targetMeasure n) := by
    rw [integral_prod_uniformAttachment hn]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← integral_targetMeasure_equiv (swapTargetEquiv k)]
    congr 1 with t
    rw [strictInDegree, strictInDegree_swapTargetEquiv k t]
  let a : ℕ → ℝ := fun m ↦ ∫ t, f (zeroTailCount m t) ∂(targetMeasure n)
  have han : a n = f 0 := by
    dsimp only [a]
    simp_rw [zeroTailCount_eq_zero]
    rw [integral_const, probReal_univ, one_smul]
  have hsum_fin_LHS : (∑ k : Fin n, a k.val) = ∑ m ∈ Finset.range n, a m :=
    Fin.sum_univ_eq_sum_range a n
  have hsum_fin_RHS :
      (∑ k : Fin n, ∫ t, fwdDiff 1 f (zeroTailCount (k.val + 1) t) ∂(targetMeasure n)) =
        ∑ m ∈ Finset.range n, ((m : ℝ) + 1) * (a m - a (m + 1)) := by
    calc
      (∑ k : Fin n, ∫ t, fwdDiff 1 f (zeroTailCount (k.val + 1) t) ∂(targetMeasure n))
        = ∑ k : Fin n, ((k.val : ℝ) + 1) * (a k.val - a (k.val + 1)) :=
          Finset.sum_congr rfl fun k _ ↦ (integral_zeroTailCount_step k f).symm
      _ = ∑ m ∈ Finset.range n, ((m : ℝ) + 1) * (a m - a (m + 1)) :=
          Fin.sum_univ_eq_sum_range (fun m ↦ ((m : ℝ) + 1) * (a m - a (m + 1))) n
  rw [hLHS, hRHS]
  change (n : ℝ)⁻¹ * (∑ k : Fin n, a k.val) - f 0 = _
  rw [hsum_fin_LHS, hsum_fin_RHS, sum_ByParts_fin a, han]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn_ne]

private lemma digraphInDegree_le_card {n : ℕ} (G₀ : Digraph (Fin n)) (v : Fin n) :
    digraphInDegree G₀ v ≤ n := by
  calc
    {u : Fin n | G₀.Adj u v}.ncard
      ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    _ = n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

private lemma aemeasurable_inDegree_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hI : AEMeasurable I P) :
    AEMeasurable (fun ω ↦ digraphInDegree (G ω) (I ω)) P :=
  (Measurable.of_discrete : Measurable fun p : Fin n × Digraph (Fin n) ↦
    digraphInDegree p.2 p.1).comp_aemeasurable (hI.prodMk hG)

private lemma aemeasurable_strictInDegree_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hI : AEMeasurable I P) :
    AEMeasurable (fun ω ↦ {u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard) P :=
  (Measurable.of_discrete : Measurable fun p : Fin n × Digraph (Fin n) ↦
    strictInDegree p.2 p.1).comp_aemeasurable (hI.prodMk hG)

private lemma memLp_inDegree_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hI : AEMeasurable I P) :
    MemLp (fun ω ↦ (digraphInDegree (G ω) (I ω) : ℝ)) 2 P :=
  MemLp.of_bound
    (((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable
      (aemeasurable_inDegree_of_aemeasurable hG hI)).aestronglyMeasurable)
    (n : ℝ)
    (Filter.Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast digraphInDegree_le_card (G ω) (I ω))

private lemma integral_inDegree_step_of_indep
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (f : ℕ → ℝ) :
    (∫ ω, f (digraphInDegree (G ω) (I ω)) ∂P) - f 0 =
      ∫ ω, fwdDiff 1 f ({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard) ∂P := by
  let IG : Ω → Fin n × Digraph (Fin n) := fun ω ↦ (I ω, G ω)
  have hIG : AEMeasurable IG P := hI.prodMk hG
  have hIG_law : P.map IG = (unifFinMeasure n hn).prod (uniformAttachment n) := by
    rw [hIndep.map_prod_eq_prod_map_map hI hG, hI_law, hG_law]
    rfl
  let g₁ : Fin n × Digraph (Fin n) → ℝ := fun p ↦ f (digraphInDegree p.2 p.1)
  let g₂ : Fin n × Digraph (Fin n) → ℝ := fun p ↦ fwdDiff 1 f (strictInDegree p.2 p.1)
  have h1 : ∫ ω, f (digraphInDegree (G ω) (I ω)) ∂P =
      ∫ p, g₁ p ∂((unifFinMeasure n hn).prod (uniformAttachment n)) := by
    change ∫ ω, g₁ (IG ω) ∂P = _
    rw [← hIG_law]
    exact (integral_map hIG (f := g₁) Measurable.of_discrete.aestronglyMeasurable).symm
  have h2 : ∫ ω, fwdDiff 1 f ({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard) ∂P =
      ∫ p, g₂ p ∂((unifFinMeasure n hn).prod (uniformAttachment n)) := by
    change ∫ ω, g₂ (IG ω) ∂P = _
    rw [← hIG_law]
    exact (integral_map hIG (f := g₂) Measurable.of_discrete.aestronglyMeasurable).symm
  rw [h1, h2]
  exact integral_inDegree_prod_step hn f

private lemma isDiscreteEquilibrium_inDegree_of_indep
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    IsDiscreteEquilibrium P (1 / 2)
      (fun ω ↦ digraphInDegree (G ω) (I ω)) P
      (fun ω ↦ {u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard) := by
  have hW_int : Integrable (fun ω ↦ (digraphInDegree (G ω) (I ω) : ℝ)) P :=
    (memLp_inDegree_of_aemeasurable P hG hI).integrable one_le_two
  have hW_mean : ∫ ω, (digraphInDegree (G ω) (I ω) : ℝ) ∂P = (1 - (1 / 2 : ℝ)) / (1 / 2) := by
    have hid :=
      integral_inDegree_step_of_indep P hn hG hG_law hI hIndep hI_law (fun m : ℕ ↦ (m : ℝ))
    have hfwd1 : (fun ω : Ω ↦ fwdDiff 1 (fun k : ℕ ↦ (k : ℝ))
        ({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard)) = fun _ ↦ (1 : ℝ) :=
      funext fun ω ↦ by rw [fwdDiff, Nat.cast_add, Nat.cast_one]; ring
    rw [Nat.cast_zero, sub_zero, hfwd1, integral_const, probReal_univ, one_smul] at hid
    rw [hid]
    norm_num
  refine ⟨by norm_num, by norm_num, aemeasurable_inDegree_of_aemeasurable hG hI,
    hW_int, hW_mean, aemeasurable_strictInDegree_of_aemeasurable hG hI, fun f _ ↦ ?_⟩
  calc
    (1 / 2 : ℝ) * (∫ ω, f (digraphInDegree (G ω) (I ω)) ∂P) - (1 / 2) * f 0
      = (1 / 2 : ℝ) * ((∫ ω, f (digraphInDegree (G ω) (I ω)) ∂P) - f 0) := (mul_sub _ _ _).symm
    _ = (1 - 1 / 2 : ℝ) *
          ∫ ω, fwdDiff 1 f ({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard) ∂P := by
        rw [integral_inDegree_step_of_indep P hn hG hG_law hI hIndep hI_law f]
        norm_num

private lemma abs_strictInDegree_sub_inDegree
    {n : ℕ} (G : Digraph (Fin n)) (v : Fin n) :
    |(({u : Fin n | u ≠ v ∧ G.Adj u v}.ncard : ℕ) : ℝ) - (digraphInDegree G v : ℝ)| =
      ({H : Digraph (Fin n) | H.Adj v v}.indicator (1 : Digraph (Fin n) → ℝ) G) := by
  have h : (digraphInDegree G v : ℝ) =
      (({u : Fin n | u ≠ v ∧ G.Adj u v}.ncard : ℕ) : ℝ) +
        ({H : Digraph (Fin n) | H.Adj v v}.indicator 1 G) :=
    digraphInDegree_eq_strictInDegree_add G v
  rw [h, sub_add_cancel_left, abs_neg]
  exact abs_of_nonneg (Set.indicator_nonneg (f := 1) (fun _ _ ↦ zero_le_one) G)

private lemma integrable_abs_strictInDegree_sub_inDegree
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hI : AEMeasurable I P) :
    Integrable (fun ω ↦
      |(({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard : ℕ) : ℝ) -
        (digraphInDegree (G ω) (I ω) : ℝ)|) P := by
  have hWR_aesm : AEStronglyMeasurable (fun ω ↦ (digraphInDegree (G ω) (I ω) : ℝ)) P :=
    ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable
      (aemeasurable_inDegree_of_aemeasurable hG hI)).aestronglyMeasurable
  have hWeR_aesm : AEStronglyMeasurable
      (fun ω ↦ (({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard : ℕ) : ℝ)) P :=
    ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable
      (aemeasurable_strictInDegree_of_aemeasurable hG hI)).aestronglyMeasurable
  refine (integrable_const (1 : ℝ)).mono'
    (continuous_abs.comp_aestronglyMeasurable (hWeR_aesm.sub hWR_aesm))
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_abs, abs_strictInDegree_sub_inDegree (G ω) (I ω)]
  by_cases h : (G ω).Adj (I ω) (I ω)
  · have hm : G ω ∈ {H : Digraph (Fin n) | H.Adj (I ω) (I ω)} := h
    rw [Set.indicator_of_mem hm, Pi.one_apply]
  · have hm : G ω ∉ {H : Digraph (Fin n) | H.Adj (I ω) (I ω)} := h
    rw [Set.indicator_of_notMem hm]
    exact zero_le_one

private lemma integral_abs_strictInDegree_sub_inDegree
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    ∫ ω, |(({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard : ℕ) : ℝ) -
        (digraphInDegree (G ω) (I ω) : ℝ)| ∂P =
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
  let IG : Ω → Fin n × Digraph (Fin n) := fun ω ↦ (I ω, G ω)
  have hIG : AEMeasurable IG P := hI.prodMk hG
  have hIG_law : P.map IG = (unifFinMeasure n hn).prod (uniformAttachment n) := by
    rw [hIndep.map_prod_eq_prod_map_map hI hG, hI_law, hG_law]
    rfl
  let ψ : Fin n × Digraph (Fin n) → ℝ :=
    fun p ↦ {H : Digraph (Fin n) | H.Adj p.1 p.1}.indicator 1 p.2
  have hpt : (fun ω : Ω ↦
      |(({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard : ℕ) : ℝ) -
        (digraphInDegree (G ω) (I ω) : ℝ)|) = fun ω ↦ ψ (IG ω) :=
    funext fun ω ↦ abs_strictInDegree_sub_inDegree (G ω) (I ω)
  have h1 : ∫ ω, |(({u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard : ℕ) : ℝ) -
      (digraphInDegree (G ω) (I ω) : ℝ)| ∂P = ∫ p, ψ p ∂(P.map IG) := by
    rw [hpt]
    exact (integral_map hIG (f := ψ) Measurable.of_discrete.aestronglyMeasurable).symm
  rw [h1, hIG_law, integral_prod_uniformAttachment hn ψ]
  congr 1
  have hinner : ∀ k : Fin n,
      (∫ t, ψ (k, digraphOfTargets t) ∂(targetMeasure n)) = 1 / ((k.val : ℝ) + 1) := fun k ↦ by
    have hmap : ∫ t, ψ (k, digraphOfTargets t) ∂(targetMeasure n) =
        ∫ H, ψ (k, H) ∂(uniformAttachment n) := by
      rw [uniformAttachment_eq_map,
        integral_map measurable_digraphOfTargets.aemeasurable
          (f := fun H ↦ ψ (k, H)) Measurable.of_discrete.aestronglyMeasurable]
    rw [hmap]
    dsimp only [ψ]
    rw [integral_indicator_one .of_discrete, uniformAttachment_real_adj k k, ite_eq_left le_rfl]
  simp_rw [hinner]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) n

/-- Discrete equilibrium coupling for the in-degree of an independent uniformly chosen vertex in
`uniformAttachment n`: `We ω := {u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard` (excluding the
potential self-loop at `I ω`) satisfies `IsDiscreteEquilibrium P (1 / 2) W P We` and
`∫ ω, |(We ω : ℝ) - (W ω : ℝ)| ∂P = (1 / n) * ∑ k ∈ Finset.range n, 1 / (k + 1)`
(Proof of Theorem 6.6 `\label{thm1716}`, `SteinIntro.tex:3352-3386`; `ISSUE-TYPO-6.6`). -/
theorem uniformAttachment_inDegree_equilibrium_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℕ := fun ω ↦ digraphInDegree (G ω) (I ω)
    let We : Ω → ℕ := fun ω ↦ {u : Fin n | u ≠ I ω ∧ (G ω).Adj u (I ω)}.ncard
    MemLp (fun ω ↦ (W ω : ℝ)) 2 P ∧
      IsDiscreteEquilibrium P (1 / 2) W P We ∧
      Integrable (fun ω ↦ |(We ω : ℝ) - (W ω : ℝ)|) P ∧
      ∫ ω, |(We ω : ℝ) - (W ω : ℝ)| ∂P =
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) :=
  ⟨memLp_inDegree_of_aemeasurable P hG hI,
    isDiscreteEquilibrium_inDegree_of_indep P hn hG hG_law hI hIndep hI_law,
    integrable_abs_strictInDegree_sub_inDegree P hG hI,
    integral_abs_strictInDegree_sub_inDegree P hn hG hG_law hI hIndep hI_law⟩

/-! ### Theorem 6.6: Total Variation Geometric Approximation for Uniform Attachment In-Degree -/

/-- **Theorem 6.6** (sharp bound, `\label{thm1716}`, `SteinIntro.tex:3345-3350, 3384-3385`;
`ISSUE-6.6`): for $n \ge 1$, $G \sim \mathrm{uniformAttachment}\,n$, independent uniform vertex
$I \in \mathrm{Fin}\,n$, in-degree $W = \mathrm{digraphInDegree}\,(G\,I)$, and
$N \sim \mathrm{Ge}^0(1/2)$,
$d_{\mathrm{TV}}(W, N) \le \frac{\log(n) + 1}{n}$. -/
theorem tvDist_uniformAttachment_inDegree_le_sharp
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n} {N : Ω' → ℕ}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (hN_law : P'.map N = geomLaw (1 / 2)) :
    let W : Ω → ℕ := fun ω ↦ digraphInDegree (G ω) (I ω)
    tvDist (P.map W) (P'.map N) ≤
      ENNReal.ofReal ((Real.log (n : ℝ) + 1) / (n : ℝ)) := by
  intro W
  obtain ⟨hW2, hEq, hDiff_int, hDiff_mean⟩ :=
    uniformAttachment_inDegree_equilibrium_coupling P hn hG hG_law hI hIndep hI_law
  have hThm65 := tvDist_le_of_isDiscreteEquilibrium P P' hW2 hEq hN_law
  have h2half : (2 : ℝ) * (1 - 1 / 2) = 1 := by norm_num
  rw [h2half, ENNReal.ofReal_one, one_mul,
    ← ofReal_integral_eq_lintegral_ofReal hDiff_int
      (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _),
    hDiff_mean] at hThm65
  refine hThm65.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (harmonic_sum_le_log_add_one hn)
    (inv_nonneg.mpr (Nat.cast_nonneg n))

/-- **Theorem 6.6** (`\label{thm1716}`, `SteinIntro.tex:3345-3350`; `ISSUE-TYPO-6.6`, `ISSUE-6.6`):
for $n \ge 1$, $G \sim \mathrm{uniformAttachment}\,n$, independent uniform vertex
$I \in \mathrm{Fin}\,n$, in-degree $W = \mathrm{digraphInDegree}\,(G\,I)$, and
$N \sim \mathrm{Ge}^0(1/2)$,
$d_{\mathrm{TV}}(W, N) \le \frac{2(\log(n) + 1)}{n}$. -/
theorem tvDist_uniformAttachment_inDegree_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n} {N : Ω' → ℕ}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure)
    (_hN : AEMeasurable N P') (hN_law : P'.map N = geomLaw (1 / 2)) :
    let W : Ω → ℕ := fun ω ↦ digraphInDegree (G ω) (I ω)
    tvDist (P.map W) (P'.map N) ≤
      ENNReal.ofReal (2 * (Real.log (n : ℝ) + 1) / (n : ℝ)) := by
  intro W
  refine (tvDist_uniformAttachment_inDegree_le_sharp P P' hn hG hG_law hI hIndep hI_law
    hN_law).trans (ENNReal.ofReal_le_ofReal ?_)
  have hnn : 0 ≤ (Real.log (n : ℝ) + 1) / (n : ℝ) :=
    div_nonneg (by linarith [Real.log_natCast_nonneg n]) (Nat.cast_nonneg n)
  linarith [show 2 * (Real.log (n : ℝ) + 1) / (n : ℝ) =
    2 * ((Real.log (n : ℝ) + 1) / (n : ℝ)) by ring]

end SteinMethod
