/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Branching
import Formalization.SizeBias.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure

/-!
# Basic Properties of Planar GW Trees & Non-Vacuity Witnesses (`Formalization.Branching.Basic`)

Proves:
* Planar tree probability identities `(5.7)` (`sec5_3_eq_1710`, `\label{1710}`,
  `SteinIntro.tex:3054-3056`, proved via the recursion at `SteinIntro.tex:3085-3098`) and `(5.8)`
  (`sec5_3_eq_1711`, `\label{1711}`, `SteinIntro.tex:3070-3072`), together with generation-size /
  vertex-count identities (`card_gwVertex_eq_gwTreeGenSize`, `gwLeftCount_add_gwRightCount`,
  `one_le_gwRightCount`); note that `gwProb` and `gwSizeBiasProbV` are defined by formula and
  recursion (`SteinIntro.tex:3047-3052, 3091-3098`), so `(5.7)` and `(5.8)` are identities about
  those definitions and `L3085-3092` is definitional;
* Positive-conditioning invariance of size-biasing (`sec5_3_sizeBias_cond_pos`,
  `SteinIntro.tex:3077-3078`, supporting Item 2 `\label{i172a}` at `SteinIntro.tex:3062-3063`);
* Canonical Galton–Watson construction on `Measure.infinitePi` (`gwCanonical`,
  `isGaltonWatson_infinitePi`) and non-vacuity witnesses for `IsGaltonWatson` (both the
  degenerate $Z_n \equiv 1$ case `isGaltonWatson_const_one` and the non-degenerate critical
  offspring law $\frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$ with $\sigma^2 = 1 > 0$,
  `sec5_3_exists_isGaltonWatson_pos_var`), `GWTree`, `IsSizeBiasSpine`, and
  `IsSizeBiasSpineCoupling` (`isSizeBiasSpine_const_one`, `isSizeBiasSpineCoupling_const_one`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Section 1: Planar GW Tree Identities `(5.7)` and `(5.8)` -/

theorem prod_fin_get_eq_map_prod {α : Type*} (f : α → ℝ) :
    ∀ ts : List α, (∏ j : Fin ts.length, f (ts.get j)) = (ts.map f).prod
  | [] => by simp
  | a :: ts => by
      change (∏ j : Fin (ts.length + 1), f ((a :: ts).get j)) = (List.map f (a :: ts)).prod
      rw [Fin.prod_univ_succ, List.map_cons, List.prod_cons, ← prod_fin_get_eq_map_prod f ts]
      rfl

theorem sum_fin_get_eq_map_sum {α : Type*} (f : α → ℕ) :
    ∀ ts : List α, (∑ j : Fin ts.length, f (ts.get j)) = (ts.map f).sum
  | [] => by simp
  | a :: ts => by
      change (∑ j : Fin (ts.length + 1), f ((a :: ts).get j)) = (List.map f (a :: ts)).sum
      rw [Fin.sum_univ_succ, List.map_cons, List.sum_cons, ← sum_fin_get_eq_map_sum f ts]
      rfl

/-- The number of vertices in generation $n$ of a planar tree $t$ equals `gwTreeGenSize t`
(`SteinIntro.tex:3073-3074`). -/
theorem card_gwVertex_eq_gwTreeGenSize :
    ∀ {n : ℕ} (t : GWTree n), Fintype.card (GWVertex t) = gwTreeGenSize t
  | 0, () => rfl
  | _ + 1, ts => by
      let _ : ∀ i : Fin ts.length, Fintype (GWVertex (ts.get i)) :=
        fun i ↦ instFintypeGWVertex (ts.get i)
      change Fintype.card (Σ i : Fin ts.length, GWVertex (ts.get i)) =
        (ts.map gwTreeGenSize).sum
      rw [Fintype.card_sigma]
      have hcongr : ∀ i : Fin ts.length,
          Fintype.card (GWVertex (ts.get i)) = gwTreeGenSize (ts.get i) :=
        fun i ↦ card_gwVertex_eq_gwTreeGenSize (ts.get i)
      simp_rw [hcongr]
      exact sum_fin_get_eq_map_sum gwTreeGenSize ts

/-- **Equation `(5.7)` (`\label{1710}`)** (`SteinIntro.tex:3054-3056`, proved via the recursion at
`SteinIntro.tex:3085-3098`; `ISSUE-TYPO-5.3b`, `I-1`):
for every depth-$n$ planar tree $t$ and every vertex $v$ in generation $n$ of $t$,
$G_n^s(t, v) = G_n(t)$. -/
def Sec5_3_eq_1710_stmt : Prop :=
  ∀ (p : ℕ → ℝ) {n : ℕ} (t : GWTree n) (v : GWVertex t),
    gwSizeBiasProbV p t v = gwProb p t

theorem sec5_3_eq_1710 (p : ℕ → ℝ) :
    ∀ {n : ℕ} (t : GWTree n) (v : GWVertex t),
      gwSizeBiasProbV p t v = gwProb p t
  | 0, (), () => rfl
  | _ + 1, ts, ⟨i, u⟩ => by
      change gwSizeBiasProbV p (ts.get i) u *
          (∏ j ∈ Finset.univ.erase i, gwProb p (ts.get j)) *
          ((ts.length : ℝ) * p ts.length) * (1 / (ts.length : ℝ)) =
        p ts.length * (ts.map (gwProb p)).prod
      have hpos : 0 < ts.length := Nat.zero_lt_of_lt i.2
      have hne : (ts.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
      rw [sec5_3_eq_1710 p (ts.get i) u,
        Finset.mul_prod_erase Finset.univ (fun j : Fin ts.length ↦ gwProb p (ts.get j))
          (Finset.mem_univ i),
        prod_fin_get_eq_map_prod (gwProb p) ts]
      field_simp [hne]

/-- **Equation `(5.8)` (`\label{1711}`)** (`SteinIntro.tex:3070-3072`; `I-1`):
for every depth-$n$ planar tree $t$, $G_n^s(t) = t_n G_n(t)$. -/
def Sec5_3_eq_1711_stmt : Prop :=
  ∀ (p : ℕ → ℝ) {n : ℕ} (t : GWTree n),
    gwSizeBiasProb p t = (gwTreeGenSize t : ℝ) * gwProb p t

theorem sec5_3_eq_1711 (p : ℕ → ℝ) {n : ℕ} (t : GWTree n) :
    gwSizeBiasProb p t = (gwTreeGenSize t : ℝ) * gwProb p t := by
  unfold gwSizeBiasProb
  simp_rw [sec5_3_eq_1710 p t]
  rw [Finset.sum_const, Finset.card_univ, card_gwVertex_eq_gwTreeGenSize, nsmul_eq_mul]

private lemma sum_map_take_add_get_add_drop {α : Type*} (f : α → ℕ) :
    ∀ (ts : List α) (i : Fin ts.length),
      ((ts.take i.1).map f).sum + f (ts.get i) + ((ts.drop (i.1 + 1)).map f).sum =
        (ts.map f).sum
  | [], i => Fin.elim0 i
  | a :: ts, ⟨0, _⟩ => by
      simp
  | a :: ts, ⟨k + 1, hk⟩ => by
      have ih := sum_map_take_add_get_add_drop f ts ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.get_eq_getElem,
        List.getElem_cons_succ, List.drop_succ_cons] at ih ⊢
      omega

/-- Every generation-$n$ vertex $v$ splits generation $n$ of $t$ into `gwLeftCount t v`
vertices strictly to the left of $v$ and `gwRightCount t v` vertices to the right (inclusive) of $v$
(`SteinIntro.tex:3100-3101`). -/
theorem gwLeftCount_add_gwRightCount :
    ∀ {n : ℕ} (t : GWTree n) (v : GWVertex t),
      gwLeftCount t v + gwRightCount t v = gwTreeGenSize t
  | 0, (), () => rfl
  | _ + 1, ts, ⟨i, u⟩ => by
      change (((ts.take i.1).map gwTreeGenSize).sum + gwLeftCount (ts.get i) u) +
          (gwRightCount (ts.get i) u + ((ts.drop (i.1 + 1)).map gwTreeGenSize).sum) =
        (ts.map gwTreeGenSize).sum
      have ih := gwLeftCount_add_gwRightCount (ts.get i) u
      have hsplit := sum_map_take_add_get_add_drop gwTreeGenSize ts i
      omega

/-- Since `gwRightCount t v` includes $v$ itself, it is always at least $1$
(`SteinIntro.tex:3065, 3100-3101`). -/
theorem one_le_gwRightCount :
    ∀ {n : ℕ} (t : GWTree n) (v : GWVertex t), 1 ≤ gwRightCount t v
  | 0, (), () => le_rfl
  | _ + 1, ts, ⟨i, u⟩ => by
      change 1 ≤ gwRightCount (ts.get i) u + ((ts.drop (i.1 + 1)).map gwTreeGenSize).sum
      have ih := one_le_gwRightCount (ts.get i) u
      omega

private lemma sum_fin_interval_partition :
    ∀ (L : List ℕ) (m : ℕ),
      (∑ i : Fin L.length,
        if (L.take i.1).sum ≤ m ∧ m < (L.take i.1).sum + L.get i then (1 : ℝ) else 0) =
      if m < L.sum then 1 else 0
  | [], m => by simp
  | a :: L, m => by
      change (∑ i : Fin (L.length + 1),
        if ((a :: L).take i.1).sum ≤ m ∧ m < ((a :: L).take i.1).sum + (a :: L).get i
        then (1 : ℝ) else 0) = if m < (a :: L).sum then 1 else 0
      rw [Fin.sum_univ_succ, List.sum_cons]
      by_cases hm : m < a
      · have h0 : (if ((a :: L).take (0 : Fin (L.length + 1)).1).sum ≤ m ∧
            m < ((a :: L).take (0 : Fin (L.length + 1)).1).sum + (a :: L).get 0
            then (1 : ℝ) else 0) = 1 :=
          ite_eq_left_iff.2 fun h ↦ by
            simp only [Fin.val_zero, List.take_zero, List.sum_nil, List.get_eq_getElem,
              List.getElem_cons_zero] at h
            omega
        have hrest : (∑ i : Fin L.length,
            if ((a :: L).take i.succ.1).sum ≤ m ∧
              m < ((a :: L).take i.succ.1).sum + (a :: L).get i.succ
            then (1 : ℝ) else 0) = 0 := by
          refine Finset.sum_eq_zero fun i _ ↦ ite_eq_right_iff.2 fun h ↦ ?_
          simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons, List.get_eq_getElem,
            List.getElem_cons_succ] at h
          omega
        have hrhs : (if m < a + L.sum then (1 : ℝ) else 0) = 1 :=
          ite_eq_left_iff.2 fun h ↦ by omega
        rw [h0, hrest, hrhs, add_zero]
      · have h0 : (if ((a :: L).take (0 : Fin (L.length + 1)).1).sum ≤ m ∧
            m < ((a :: L).take (0 : Fin (L.length + 1)).1).sum + (a :: L).get 0
            then (1 : ℝ) else 0) = 0 :=
          ite_eq_right_iff.2 fun h ↦ by
            simp only [Fin.val_zero, List.take_zero, List.sum_nil, List.get_eq_getElem,
              List.getElem_cons_zero] at h
            omega
        have hshift : (∑ i : Fin L.length,
            if ((a :: L).take i.succ.1).sum ≤ m ∧
              m < ((a :: L).take i.succ.1).sum + (a :: L).get i.succ
            then (1 : ℝ) else 0) =
          ∑ i : Fin L.length,
            if (L.take i.1).sum ≤ m - a ∧ m - a < (L.take i.1).sum + L.get i
            then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          by_cases h : (L.take i.1).sum ≤ m - a ∧ m - a < (L.take i.1).sum + L.get i
          · rw [ite_eq_left_iff.2 fun h' ↦ ?_, ite_eq_left_iff.2 fun h' ↦ False.elim (h' h)]
            simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons, List.get_eq_getElem,
              List.getElem_cons_succ] at h'
            simp only [List.get_eq_getElem] at h
            omega
          · rw [ite_eq_right_iff.2 fun h' ↦ ?_, ite_eq_right_iff.2 fun h' ↦ False.elim (h h')]
            simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons, List.get_eq_getElem,
              List.getElem_cons_succ] at h'
            simp only [List.get_eq_getElem] at h
            omega
        rw [h0, zero_add, hshift, sum_fin_interval_partition L (m - a)]
        by_cases h : m - a < L.sum
        · rw [ite_eq_left_iff.2 fun h' ↦ False.elim (h' h),
            ite_eq_left_iff.2 fun h' ↦ by omega]
        · rw [ite_eq_right_iff.2 fun h' ↦ False.elim (h h'),
            ite_eq_right_iff.2 fun h' ↦ by omega]

/-- As $v$ ranges over the generation-$n$ vertices of a depth-$n$ planar tree $t$,
`gwLeftCount t v` takes each value $m \in \{0, \dots, t_n - 1\}$ exactly once (`I-1`,
`SteinIntro.tex:3064, 3078-3079, 3100-3101`). -/
theorem sum_gwVertex_gwLeftCount_eq :
    ∀ {n : ℕ} (t : GWTree n) (m : ℕ),
      (∑ v : GWVertex t, if gwLeftCount t v = m then (1 : ℝ) else 0) =
        if m < gwTreeGenSize t then 1 else 0
  | 0, (), m => by
      change (∑ v : Unit, if 0 = m then (1 : ℝ) else 0) = if m < 1 then 1 else 0
      rw [Finset.univ_unique, Finset.sum_singleton]
      by_cases hm : m = 0
      · subst hm; simp
      · rw [ite_eq_right_iff.2 fun h ↦ by omega, ite_eq_right_iff.2 fun h ↦ by omega]
  | n + 1, (ts : List (GWTree n)), m => by
      let _ : ∀ i : Fin ts.length, Fintype (GWVertex (ts.get i)) :=
        fun i ↦ instFintypeGWVertex (ts.get i)
      change (∑ v : Σ i : Fin ts.length, GWVertex (ts.get i),
        if ((ts.take v.1.1).map gwTreeGenSize).sum + gwLeftCount (ts.get v.1) v.2 = m
        then (1 : ℝ) else 0) = if m < (ts.map gwTreeGenSize).sum then 1 else 0
      rw [Fintype.sum_sigma]
      have hinner : ∀ i : Fin ts.length,
          (∑ u : GWVertex (ts.get i),
            if ((ts.take i.1).map gwTreeGenSize).sum + gwLeftCount (ts.get i) u = m
            then (1 : ℝ) else 0) =
          if ((ts.map gwTreeGenSize).take i.1).sum ≤ m ∧
              m < ((ts.map gwTreeGenSize).take i.1).sum + (ts.map gwTreeGenSize).get
                (i.cast (List.length_map gwTreeGenSize).symm)
          then (1 : ℝ) else 0 := by
        intro i
        rw [← List.map_take]
        set s := ((ts.take i.1).map gwTreeGenSize).sum
        by_cases hle : s ≤ m
        · have hrew : (∑ u : GWVertex (ts.get i),
              if s + gwLeftCount (ts.get i) u = m then (1 : ℝ) else 0) =
            ∑ u : GWVertex (ts.get i),
              if gwLeftCount (ts.get i) u = m - s then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl fun u _ ↦ ?_
            by_cases hu : gwLeftCount (ts.get i) u = m - s
            · rw [ite_eq_left_iff.2 fun h ↦ by omega,
                ite_eq_left_iff.2 fun h ↦ False.elim (h hu)]
            · rw [ite_eq_right_iff.2 fun h ↦ by omega,
                ite_eq_right_iff.2 fun h ↦ False.elim (hu h)]
          rw [hrew, sum_gwVertex_gwLeftCount_eq (ts.get i) (m - s)]
          simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
          by_cases hlt : m - s < gwTreeGenSize ts[i.1]
          · rw [ite_eq_left_iff.2 fun h ↦ False.elim (h hlt),
              ite_eq_left_iff.2 fun h ↦ by omega]
          · rw [ite_eq_right_iff.2 fun h ↦ False.elim (hlt h),
              ite_eq_right_iff.2 fun h ↦ by omega]
        · have hzero : (∑ u : GWVertex (ts.get i),
              if s + gwLeftCount (ts.get i) u = m then (1 : ℝ) else 0) = 0 := by
            refine Finset.sum_eq_zero fun u _ ↦ ?_
            exact ite_eq_right_iff.2 fun h ↦ by omega
          rw [hzero, eq_comm]
          exact ite_eq_right_iff.2 fun h ↦ by omega
      simp_rw [hinner]
      have hpart := sum_fin_interval_partition (ts.map gwTreeGenSize) m
      rw [← hpart]
      refine Fintype.sum_equiv (Fin.castOrderIso (List.length_map gwTreeGenSize).symm).toEquiv
        _ _ fun i ↦ ?_
      rfl

/-! ### Section 2: Positive-Conditioning Invariance of Size-Biasing (`SteinIntro.tex:3077-3078`) -/

/-- If a non-negative random variable $X$ has strictly positive integral, then
$P(X > 0) \ne 0$. -/
theorem measure_pos_ne_zero_of_pos_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hX_nn : 0 ≤ᵐ[P] X) (hμ_pos : 0 < ∫ ω, X ω ∂P) :
    P {ω | 0 < X ω} ≠ 0 := by
  intro h0
  have hX0 : X =ᵐ[P] 0 := by
    filter_upwards [hX_nn, measure_eq_zero_iff_ae_notMem.mp h0] with ω hnn hnot
    exact le_antisymm (not_lt.mp hnot) hnn
  have hint0 : ∫ ω, X ω ∂P = 0 := integral_eq_zero_of_ae hX0
  linarith

/-- If a non-negative random variable $X$ on a finite measure space has strictly positive integral,
then $P_{\mathrm{real}}(X > 0) > 0$. -/
theorem measureReal_pos_of_pos_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX_nn : 0 ≤ᵐ[P] X) (hμ_pos : 0 < ∫ ω, X ω ∂P) :
    0 < P.real {ω | 0 < X ω} :=
  ENNReal.toReal_pos (measure_pos_ne_zero_of_pos_integral P hX_nn hμ_pos) (measure_ne_top P _)

/-- `IsSizeBias` depends on $(P, X)$ only through the pushforward law `P.map X`. -/
theorem isSizeBias_congr_map {Ω₁ Ω₂ Ω' : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω']
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {P' : Measure Ω'}
    {X₁ : Ω₁ → ℝ} {X₂ : Ω₂ → ℝ} {Xs : Ω' → ℝ}
    (hX₁ : AEMeasurable X₁ P₁) (hX₂ : AEMeasurable X₂ P₂)
    (hmap : P₁.map X₁ = P₂.map X₂) :
    IsSizeBias P₁ X₁ P' Xs ↔ IsSizeBias P₂ X₂ P' Xs := by
  have hid : IdentDistrib X₁ X₂ P₁ P₂ := ⟨hX₁, hX₂, hmap⟩
  have hnn : (0 ≤ᵐ[P₁] X₁) ↔ (0 ≤ᵐ[P₂] X₂) := by
    change (∀ᵐ x ∂P₁, (0 : ℝ) ≤ X₁ x) ↔ (∀ᵐ x ∂P₂, (0 : ℝ) ≤ X₂ x)
    exact (ae_map_iff (p := fun x : ℝ ↦ 0 ≤ x) hX₁ measurableSet_Ici).symm.trans
      (by rw [hmap]; exact ae_map_iff (p := fun x : ℝ ↦ 0 ≤ x) hX₂ measurableSet_Ici)
  have hf_id : ∀ {f : ℝ → ℝ}, Measurable f →
      IdentDistrib (fun ω ↦ X₁ ω * f (X₁ ω)) (fun ω ↦ X₂ ω * f (X₂ ω)) P₁ P₂ :=
    fun hf ↦ hid.comp (measurable_id.mul hf)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨hnn.mp h1, hid.integrable_iff.mp h2, h3, fun f hf hint2 ↦ ?_⟩
    rw [← (hf_id hf).integral_eq, ← hid.integral_eq]
    exact h4 f hf ((hf_id hf).integrable_iff.mpr hint2)
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨hnn.mpr h1, hid.integrable_iff.mpr h2, h3, fun f hf hint1 ↦ ?_⟩
    rw [(hf_id hf).integral_eq, hid.integral_eq]
    exact h4 f hf ((hf_id hf).integrable_iff.mp hint1)

/-- Conditioning a non-negative random variable $Z$ on $\{Z > 0\}$ preserves `IsSizeBias`
(`SteinIntro.tex:3077-3078`). -/
theorem isSizeBias_cond_pos_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : Ω → ℝ) (Zs : Ω' → ℝ)
    (hZ_meas : AEMeasurable Z P)
    (hZ_nn : 0 ≤ᵐ[P] Z)
    (hZ_pos : P {ω | 0 < Z ω} ≠ 0) :
    IsSizeBias P Z P' Zs ↔
      IsSizeBias (ProbabilityTheory.cond P {ω | 0 < Z ω}) Z P' Zs := by
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
      have hle : Z ω ≤ 0 := by
        rw [hω]
        exact not_lt.mp h
      linarith
  have hZ_int_iff : Integrable Z (ProbabilityTheory.cond P S) ↔ Integrable Z P := by
    rw [hcond_eq, integrable_smul_measure hinv_ne_zero hinv_ne_top]
    exact (integrable_indicator_iff hS₀_meas).symm.trans (integrable_congr hZ_ind)
  have hZ_int_eq :
      ∫ ω, Z ω ∂ProbabilityTheory.cond P S = (P S₀)⁻¹.toReal * ∫ ω, Z ω ∂P := by
    rw [hcond_eq, integral_smul_measure, smul_eq_mul, ← integral_indicator hS₀_meas,
      integral_congr_ae hZ_ind]
  have hZf_int_eq : ∀ f : ℝ → ℝ,
      ∫ ω, Z ω * f (Z ω) ∂ProbabilityTheory.cond P S =
        (P S₀)⁻¹.toReal * ∫ ω, Z ω * f (Z ω) ∂P := by
    intro f
    have hZf_ind : S₀.indicator (fun ω ↦ Z ω * f (Z ω)) =ᵐ[P] fun ω ↦ Z ω * f (Z ω) := by
      filter_upwards [hZ_nn, hZZ₀] with ω (hnn : 0 ≤ Z ω) hω
      by_cases h : ω ∈ S₀
      · exact indicator_of_mem h _
      · rw [indicator_of_notMem h]
        have hle : Z ω ≤ 0 := by
          rw [hω]
          exact not_lt.mp h
        have h0 : Z ω = 0 := le_antisymm hle hnn
        simp [h0]
    rw [hcond_eq, integral_smul_measure, smul_eq_mul, ← integral_indicator hS₀_meas,
      integral_congr_ae hZf_ind]
  have hZ_nn_cond : 0 ≤ᵐ[ProbabilityTheory.cond P S] Z :=
    ProbabilityTheory.cond_absolutelyContinuous hZ_nn
  constructor
  · rintro ⟨_, hZ_int, hZs_meas, hEq⟩
    refine ⟨hZ_nn_cond, hZ_int_iff.mpr hZ_int, hZs_meas, fun f hf hZf_cond ↦ ?_⟩
    have hZf_P : Integrable (fun ω ↦ Z ω * f (Z ω)) P := by
      have hZf_ind : S₀.indicator (fun ω ↦ Z ω * f (Z ω)) =ᵐ[P] fun ω ↦ Z ω * f (Z ω) := by
        filter_upwards [hZ_nn, hZZ₀] with ω (hnn : 0 ≤ Z ω) hω
        by_cases h : ω ∈ S₀
        · exact indicator_of_mem h _
        · rw [indicator_of_notMem h]
          have hle : Z ω ≤ 0 := by rw [hω]; exact not_lt.mp h
          have h0 : Z ω = 0 := le_antisymm hle hnn
          simp [h0]
      rw [hcond_eq, integrable_smul_measure hinv_ne_zero hinv_ne_top] at hZf_cond
      exact (integrable_congr hZf_ind).mp ((integrable_indicator_iff hS₀_meas).mpr hZf_cond)
    rw [hZf_int_eq f, hZ_int_eq, hEq f hf hZf_P, mul_assoc]
  · rintro ⟨_, hZ_int_cond, hZs_meas, hEq⟩
    refine ⟨hZ_nn, hZ_int_iff.mp hZ_int_cond, hZs_meas, fun f hf hZf_P ↦ ?_⟩
    have hZf_cond : Integrable (fun ω ↦ Z ω * f (Z ω)) (ProbabilityTheory.cond P S) := by
      rw [hcond_eq]
      exact hZf_P.restrict.smul_measure hinv_ne_top
    have h1 := hEq f hf hZf_cond
    rw [hZf_int_eq f, hZ_int_eq, mul_assoc] at h1
    exact mul_left_cancel₀ hc_ne h1

/-- Section 5.3 positive-conditioning size-bias invariance (`SteinIntro.tex:3077-3078`):
conditioning a non-negative integrable random variable $X$ with $\mathbb{E}[X] > 0$ to be strictly
positive does not change its size-bias distribution. -/
def Sec5_3_sizeBias_cond_pos_stmt : Prop :=
  ∀ {Ω ΩY Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : ΩY → ℝ} {Xs : Ω' → ℝ},
    0 ≤ᵐ[P] X →
    Integrable X P →
    0 < ∫ ω, X ω ∂P →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < X ω}).map X →
    (IsSizeBias P X P' Xs ↔ IsSizeBias PY Y P' Xs)

theorem sec5_3_sizeBias_cond_pos : Sec5_3_sizeBias_cond_pos_stmt := by
  intro Ω ΩY Ω' _ _ _ P _ PY _ P' _ X Y Xs hX_nn hX_int hμ_pos hY_meas hmap
  have hpos : P {ω | 0 < X ω} ≠ 0 := measure_pos_ne_zero_of_pos_integral P hX_nn hμ_pos
  have hX_cond_meas : AEMeasurable X (ProbabilityTheory.cond P {ω | 0 < X ω}) :=
    hX_int.aemeasurable.mono_ac ProbabilityTheory.cond_absolutelyContinuous
  exact (isSizeBias_cond_pos_iff P P' X Xs hX_int.aemeasurable hX_nn hpos).trans
    (isSizeBias_congr_map hX_cond_meas hY_meas hmap.symm)

/-! ### Section 3: Non-Vacuity Witnesses (`IsGaltonWatson`, `IsSizeBiasSpine`) -/

private lemma iIndepFun_const_general {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (c : ∀ i, β i) :
    iIndepFun (fun i (_ : Ω) ↦ c i) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  by_cases hall : ∀ i ∈ S, c i ∈ sets i
  · have hinter : (⋂ i ∈ S, (fun _ : Ω ↦ c i) ⁻¹' sets i) = univ := by
      ext ω
      simp only [mem_iInter, mem_preimage, mem_univ, iff_true]
      exact hall
    have hprod : (∏ i ∈ S, P ((fun _ : Ω ↦ c i) ⁻¹' sets i)) = 1 := by
      refine Finset.prod_eq_one fun i hi ↦ ?_
      have hpre : ((fun _ : Ω ↦ c i) ⁻¹' sets i : Set Ω) = univ := by
        ext ω; simp [hall i hi]
      rw [hpre, measure_univ]
    rw [hinter, measure_univ, hprod]
  · push Not at hall
    rcases hall with ⟨i₀, hi₀, hnot⟩
    have hinter : (⋂ i ∈ S, (fun _ : Ω ↦ c i) ⁻¹' sets i : Set Ω) = ∅ := by
      ext ω
      simp only [mem_iInter, mem_preimage, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨i₀, hi₀, hnot⟩
    have hprod : (∏ i ∈ S, P ((fun _ : Ω ↦ c i) ⁻¹' sets i)) = 0 := by
      refine Finset.prod_eq_zero hi₀ ?_
      have hpre : ((fun _ : Ω ↦ c i₀) ⁻¹' sets i₀ : Set Ω) = ∅ := by
        ext ω; simp [hnot]
      rw [hpre, measure_empty]
    rw [hinter, measure_empty, hprod]

/-- **Non-vacuity witness for `IsGaltonWatson`**: the deterministic critical branching process
$Z_n \equiv 1$ on any probability space $(\Omega, P)$ satisfies `IsGaltonWatson P Z`
(`SteinIntro.tex:2993-2997`). -/
theorem isGaltonWatson_const_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    IsGaltonWatson P (fun _ _ ↦ 1) := by
  refine ⟨by simp, fun _ _ ↦ 1,
    fun _ ↦ measurable_const.aemeasurable,
    iIndepFun_const_general P (fun _ ↦ 1),
    fun _ ↦ IdentDistrib.refl measurable_const.aemeasurable,
    ae_of_all _ fun _ ↦ rfl, fun _ ↦ ae_of_all _ fun _ ↦ ?_⟩
  simp

/-- Uniform probability measure on `Ioo (0 : ℝ) 1` used to witness `IsSizeBiasSpineCoupling`. -/
noncomputable def unitIntervalIooMeasure : Measure ℝ :=
  ProbabilityTheory.cond volume (Ioo (0 : ℝ) 1)

instance isProbabilityMeasure_unitIntervalIooMeasure :
    IsProbabilityMeasure unitIntervalIooMeasure where
  measure_univ := by
    rw [unitIntervalIooMeasure, ProbabilityTheory.cond, Measure.smul_apply,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
    norm_num

/-- **Non-vacuity witness for `IsSizeBiasSpine`**: the deterministic critical branching process
$Z_n \equiv 1$ has spine decomposition $X_j = L_{n,j} = R_{n,j} = 0$. -/
theorem isSizeBiasSpine_const_one {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P'] (n : ℕ) :
    IsSizeBiasSpine P (fun _ _ ↦ 1) P' n (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun _ _ ↦ 0) := by
  refine ⟨fun _ _ ↦ 0, fun _ _ _ ↦ 1,
    iIndepFun_const_general P' (fun _ ↦ (0, 0, fun _ ↦ 1)),
    fun j _ ↦ ⟨measurable_const.aemeasurable, measurable_const.aemeasurable,
      fun _ ↦ measurable_const.aemeasurable, ?_, fun _ ↦ le_rfl, fun k m ↦ ?_,
      iIndepFun_const_general P' (fun _ ↦ 1), fun _ ↦ ?_,
      indepFun_const_left (0, 0) _, fun _ ↦ by simp, fun _ ↦ by simp⟩⟩
  · refine ⟨ae_of_all _ fun _ ↦ by simp, by simp,
      measurable_const.aemeasurable, fun f _ _ ↦ ?_⟩
    simp
  · rcases k with _ | k
    · rcases m with _ | m
      · simp
      · simp
    · have hempty : {ω' : Ω' | (0 : ℕ) = k + 1} = ∅ := by ext; simp
      have hempty2 : {ω' : Ω' | (0 : ℕ) = k + 1 ∧ 0 = m} = ∅ := by ext; simp
      rw [hempty, hempty2, measureReal_empty]
      split_ifs <;> ring
  · rw [Measure.map_const, Measure.map_const, measure_univ, measure_univ]

/-- **Non-vacuity witness for `IsSizeBiasSpineCoupling`**: the deterministic critical branching
process $Z_n \equiv 1$ on `Measure.dirac ()` and `unitIntervalIooMeasure` satisfies
`IsSizeBiasSpineCoupling` for every $n \ge 0$. -/
theorem isSizeBiasSpineCoupling_const_one (n : ℕ) :
    IsSizeBiasSpineCoupling (Measure.dirac ()) (fun _ _ ↦ 1)
      unitIntervalIooMeasure n
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun _ _ ↦ 0) (fun _ _ ↦ 0) id := by
  refine ⟨isSizeBiasSpine_const_one (Measure.dirac ()) unitIntervalIooMeasure n,
    fun j _ ↦ ⟨measurable_const.aemeasurable, ?_⟩,
    iIndepFun_const_general unitIntervalIooMeasure (fun _ ↦ 0),
    indepFun_const_left _ _, ?_, indepFun_const_right _ _⟩
  · have huniv : {ω' : ℝ | (0 : ℕ) = 0} = univ := by ext; simp
    rw [huniv, ProbabilityTheory.cond_univ]
  · exact MeasureTheory.pdf.IsUniform.cond

/-- Canonical Galton–Watson generation sizes built recursively from an offspring array
$\xi : \mathbb{N} \times \mathbb{N} \to \Omega \to \mathbb{N}$ (`SteinIntro.tex:2993-2997`). -/
def gwCanonical {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) : ℕ → Ω → ℕ
  | 0, _ => 1
  | n + 1, ω => ∑ i ∈ Finset.range (gwCanonical ξ n ω), ξ (n, i) ω

@[simp]
theorem gwCanonical_zero {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) (ω : Ω) :
    gwCanonical ξ 0 ω = 1 :=
  rfl

@[simp]
theorem gwCanonical_one {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) (ω : Ω) :
    gwCanonical ξ 1 ω = ξ (0, 0) ω := by
  change (∑ i ∈ Finset.range 1, ξ (0, i) ω) = ξ (0, 0) ω
  exact Finset.sum_range_one _

theorem gwCanonical_succ {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) (n : ℕ) (ω : Ω) :
    gwCanonical ξ (n + 1) ω = ∑ i ∈ Finset.range (gwCanonical ξ n ω), ξ (n, i) ω :=
  rfl

/-- Canonical Galton–Watson process on the infinite product space $\mathbb{N} \times \mathbb{N} \to
\mathbb{N}$ equipped with `Measure.infinitePi (fun _ ↦ μ₁)` for any offspring probability law
`μ₁ : Measure ℕ` with finite mean (`SteinIntro.tex:2993-2997`). -/
theorem isGaltonWatson_infinitePi (μ₁ : Measure ℕ) [IsProbabilityMeasure μ₁]
    (h_int : Integrable (fun k : ℕ ↦ (k : ℝ)) μ₁) :
    IsGaltonWatson (Measure.infinitePi (fun _ : ℕ × ℕ ↦ μ₁))
      (gwCanonical (fun p (ω : ℕ × ℕ → ℕ) ↦ ω p)) := by
  let P : Measure (ℕ × ℕ → ℕ) := Measure.infinitePi (fun _ : ℕ × ℕ ↦ μ₁)
  let ξ : ℕ × ℕ → (ℕ × ℕ → ℕ) → ℕ := fun p ω ↦ ω p
  have hmap : ∀ p : ℕ × ℕ, P.map (ξ p) = μ₁ := fun p ↦
    Measure.infinitePi_map_eval (fun _ : ℕ × ℕ ↦ μ₁) p
  have hZ1_eq : gwCanonical ξ 1 = ξ (0, 0) := funext (gwCanonical_one ξ)
  have hcast_meas : Measurable (fun k : ℕ ↦ (k : ℝ)) := Measurable.of_discrete
  have hZ1_int : Integrable (fun ω ↦ (gwCanonical ξ 1 ω : ℝ)) P := by
    rw [hZ1_eq]
    have h1 : Integrable (fun k : ℕ ↦ (k : ℝ)) (P.map (ξ (0, 0))) := by
      rwa [hmap (0, 0)]
    exact (integrable_map_measure hcast_meas.aestronglyMeasurable
      (measurable_pi_apply (0, 0)).aemeasurable).mp h1
  refine ⟨hZ1_int, ξ, fun p ↦ (measurable_pi_apply p).aemeasurable,
    iIndepFun_infinitePi (P := fun _ : ℕ × ℕ ↦ μ₁) (X := fun _ (k : ℕ) ↦ k)
      (fun _ ↦ measurable_id),
    fun p ↦ ?_, ae_of_all _ fun _ ↦ rfl, fun n ↦ ae_of_all _ fun _ ↦ rfl⟩
  rw [hZ1_eq]
  exact ⟨(measurable_pi_apply p).aemeasurable, (measurable_pi_apply (0, 0)).aemeasurable,
    by rw [hmap p, hmap (0, 0)]⟩

/-- Critical offspring distribution $\frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$ on $\mathbb{N}$
with mean $1$ and variance $\sigma^2 = 1 > 0$. -/
noncomputable def twoBernoulliMeasure : Measure ℕ :=
  (1 / 2 : ℝ≥0) • Measure.dirac 0 + (1 / 2 : ℝ≥0) • Measure.dirac 2

instance isProbabilityMeasure_twoBernoulliMeasure :
    IsProbabilityMeasure twoBernoulliMeasure where
  measure_univ := by
    rw [twoBernoulliMeasure, Measure.coe_add, Pi.add_apply,
      Measure.coe_nnreal_smul_apply, Measure.coe_nnreal_smul_apply,
      measure_univ, measure_univ, mul_one, ← ENNReal.coe_add,
      ENNReal.coe_eq_one, ← NNReal.coe_eq_one, NNReal.coe_add, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
    norm_num

theorem integrable_twoBernoulliMeasure (g : ℕ → ℝ) :
    Integrable g twoBernoulliMeasure :=
  ((integrable_dirac enorm_lt_top).smul_measure_nnreal).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure_nnreal)

theorem integral_twoBernoulliMeasure (g : ℕ → ℝ) :
    ∫ k, g k ∂twoBernoulliMeasure = (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * g 2 := by
  have h0 : Integrable g ((1 / 2 : ℝ≥0) • Measure.dirac (0 : ℕ)) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  have h2 : Integrable g ((1 / 2 : ℝ≥0) • Measure.dirac (2 : ℕ)) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  rw [twoBernoulliMeasure, integral_add_measure h0 h2, integral_smul_nnreal_measure,
    integral_smul_nnreal_measure, integral_dirac, integral_dirac, NNReal.smul_def,
    NNReal.smul_def, smul_eq_mul, smul_eq_mul, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]

theorem twoBernoulliMeasure_real_zero :
    twoBernoulliMeasure.real {0} = 1 / 2 := by
  rw [← integral_indicator_one (measurableSet_singleton 0), integral_twoBernoulliMeasure]
  norm_num

theorem twoBernoulliMeasure_real_two :
    twoBernoulliMeasure.real {2} = 1 / 2 := by
  rw [← integral_indicator_one (measurableSet_singleton 2), integral_twoBernoulliMeasure]
  norm_num

/-- **Non-vacuity witness for `IsGaltonWatson` with $\sigma^2 > 0$** (`I-2`,
`SteinIntro.tex:2993-2997, 3007-3020`): there exists a probability space $(\Omega, P)$ and a
critical Galton–Watson process $Z$ with offspring law $\frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$
satisfying $\mathbb{E}[Z_1] = 1$, $\operatorname{Var}(Z_1) = 1 > 0$, and
$\mathbb{E}|Z_1|^3 = 4 < \infty$. -/
def Sec5_3_exists_isGaltonWatson_pos_var_stmt : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (Z : ℕ → Ω → ℕ),
    IsGaltonWatson P Z ∧
    (∫ ω, (Z 1 ω : ℝ) ∂P = 1) ∧
    ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P = 1 ∧
    Integrable (fun ω ↦ |(Z 1 ω : ℝ)| ^ 3) P ∧
    P.real {ω | Z 1 ω = 0} = 1 / 2 ∧
    P.real {ω | Z 1 ω = 2} = 1 / 2

theorem sec5_3_exists_isGaltonWatson_pos_var : Sec5_3_exists_isGaltonWatson_pos_var_stmt := by
  let P : Measure (ℕ × ℕ → ℕ) := Measure.infinitePi (fun _ : ℕ × ℕ ↦ twoBernoulliMeasure)
  let ξ : ℕ × ℕ → (ℕ × ℕ → ℕ) → ℕ := fun p ω ↦ ω p
  let Z : ℕ → (ℕ × ℕ → ℕ) → ℕ := gwCanonical ξ
  have hZ1_eq : Z 1 = ξ (0, 0) := funext (gwCanonical_one ξ)
  have hmap : P.map (Z 1) = twoBernoulliMeasure := by
    rw [hZ1_eq]
    exact Measure.infinitePi_map_eval (fun _ : ℕ × ℕ ↦ twoBernoulliMeasure) (0, 0)
  have hZ1_meas : Measurable (Z 1) := hZ1_eq ▸ measurable_pi_apply (0, 0)
  have hcast_meas : Measurable (fun k : ℕ ↦ (k : ℝ)) := Measurable.of_discrete
  have hsq_meas : Measurable (fun k : ℕ ↦ ((k : ℝ) - 1) ^ 2) := Measurable.of_discrete
  have hcube_meas : Measurable (fun k : ℕ ↦ |(k : ℝ)| ^ 3) := Measurable.of_discrete
  have hmean : ∫ ω, (Z 1 ω : ℝ) ∂P = 1 := by
    have h1 := integral_map (μ := P) hZ1_meas.aemeasurable hcast_meas.aestronglyMeasurable
    rw [hmap, integral_twoBernoulliMeasure] at h1
    linarith [h1]
  have hZ1R_meas : Measurable (fun ω ↦ (Z 1 ω : ℝ)) := hcast_meas.comp hZ1_meas
  have hvar : ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P = 1 := by
    rw [ProbabilityTheory.variance_eq_integral hZ1R_meas.aemeasurable, hmean]
    have h1 := integral_map (μ := P) hZ1_meas.aemeasurable hsq_meas.aestronglyMeasurable
    rw [hmap, integral_twoBernoulliMeasure] at h1
    linarith [h1]
  have h3 : Integrable (fun ω ↦ |(Z 1 ω : ℝ)| ^ 3) P := by
    have h1 : Integrable (fun k : ℕ ↦ |(k : ℝ)| ^ 3) (P.map (Z 1)) := by
      rw [hmap]
      exact integrable_twoBernoulliMeasure _
    exact (integrable_map_measure hcube_meas.aestronglyMeasurable hZ1_meas.aemeasurable).mp h1
  have hp0 : P.real {ω | Z 1 ω = 0} = 1 / 2 := by
    have : {ω : ℕ × ℕ → ℕ | Z 1 ω = 0} = (Z 1) ⁻¹' ({0} : Set ℕ) := rfl
    rw [this, ← map_measureReal_apply hZ1_meas (measurableSet_singleton 0), hmap,
      twoBernoulliMeasure_real_zero]
  have hp2 : P.real {ω | Z 1 ω = 2} = 1 / 2 := by
    have : {ω : ℕ × ℕ → ℕ | Z 1 ω = 2} = (Z 1) ⁻¹' ({2} : Set ℕ) := rfl
    rw [this, ← map_measureReal_apply hZ1_meas (measurableSet_singleton 2), hmap,
      twoBernoulliMeasure_real_two]
  exact ⟨ℕ × ℕ → ℕ, inferInstance, P, inferInstance, Z,
    isGaltonWatson_infinitePi twoBernoulliMeasure (integrable_twoBernoulliMeasure _),
    hmean, hvar, h3, hp0, hp2⟩

end SteinMethod
