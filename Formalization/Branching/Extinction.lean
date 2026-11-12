/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Branching.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Section 5.3: Extinction Dichotomy and Planar Tree Laws (`Formalization.Branching.Extinction`)

This file formalizes the planar tree distribution summation identities (`Sec5_3_gwProb_sum_genSize`,
`I-1(a,c)` from `docs/reviews/stmts-review-05I.md`) and the Galton–Watson extinction dichotomy
(`Sec5_3_extinction`, `SteinIntro.tex:2999-3004`; `ISSUE-TYPO-5.3a`).

It also establishes core structural lemmas for Galton–Watson processes used downstream in
`Formalization.Branching.SizeBiasTree` and `Formalization.Branching.YaglomRate`:
* Bijectivity of `gwLeftCount` onto `Fin (gwTreeGenSize t)`.
* Leaf-extension equivalence
  `gwTreeEquivSigma : (Σ t : GWTree n, (GWVertex t → ℕ)) ≃ GWTree (n + 1)`.
* Row independence of the offspring array and measurability/integrability of $Z_n$.
* Expectation identity $\mathbb{E}[Z_n] = (\mathbb{E}[Z_1])^n$ and PGF iteration
  $\mathbb{E}[s^{Z_n}] = f^{[n]}(s)$ for $s \in [0, 1]$.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace SteinMethod

/-!
### 1. Bijectivity of `gwLeftCount` on `GWVertex t`
-/

/-- For any vertex $v$ at generation $n$ of a depth-$n$ planar tree $t$,
$\mathrm{left}(t, v) < t_n$. -/
theorem gwLeftCount_lt_gwTreeGenSize {n : ℕ} (t : GWTree n) (v : GWVertex t) :
    gwLeftCount t v < gwTreeGenSize t := by
  have h1 := gwLeftCount_add_gwRightCount t v
  have h2 := one_le_gwRightCount t v
  omega

/-- Left-count as an element of `Fin (gwTreeGenSize t)`. -/
def gwLeftFin {n : ℕ} (t : GWTree n) (v : GWVertex t) : Fin (gwTreeGenSize t) :=
  ⟨gwLeftCount t v, gwLeftCount_lt_gwTreeGenSize t v⟩

/-- `gwLeftFin t` is a bijection from `GWVertex t` onto `Fin (gwTreeGenSize t)`. -/
theorem bijective_gwLeftFin {n : ℕ} (t : GWTree n) :
    Function.Bijective (gwLeftFin t) := by
  let _ : Fintype (GWVertex t) := instFintypeGWVertex t
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨fun i ↦ ?_, by rw [card_gwVertex_eq_gwTreeGenSize, Fintype.card_fin]⟩
  have hsum := sum_gwVertex_gwLeftCount_eq t i.1
  rw [ite_eq_left_iff.2 fun h ↦ False.elim (h i.2)] at hsum
  have hne : ∑ v : GWVertex t, (if gwLeftCount t v = i.1 then (1 : ℝ) else 0) ≠ 0 := by
    rw [hsum]; exact one_ne_zero
  obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨v, Fin.ext ?_⟩
  by_contra hcontra
  exact hv (ite_eq_right_iff.2 fun h ↦ False.elim (hcontra h))

/-- Equivalence `GWVertex t ≃ Fin (gwTreeGenSize t)` given by `gwLeftFin t`. -/
noncomputable def gwVertexEquivFin {n : ℕ} (t : GWTree n) :
    GWVertex t ≃ Fin (gwTreeGenSize t) :=
  Equiv.ofBijective (gwLeftFin t) (bijective_gwLeftFin t)

@[simp]
theorem gwVertexEquivFin_apply_coe {n : ℕ} (t : GWTree n) (v : GWVertex t) :
    ((gwVertexEquivFin t v : Fin (gwTreeGenSize t)) : ℕ) = gwLeftCount t v := rfl

/-- `gwLeftCount t` is injective on `GWVertex t`. -/
theorem gwLeftCount_injective {n : ℕ} (t : GWTree n) :
    Function.Injective (gwLeftCount t) := by
  intro u v huv
  exact (bijective_gwLeftFin t).1 (Fin.ext huv)

/-- Summing a function of `gwLeftCount t v` over `v : GWVertex t` equals summing over
`Finset.range (gwTreeGenSize t)`. -/
theorem sum_gwVertex_gwLeftCount {n : ℕ} {β : Type*} [AddCommMonoid β]
    (t : GWTree n) (g : ℕ → β) :
    (∑ v : GWVertex t, g (gwLeftCount t v)) = ∑ i ∈ Finset.range (gwTreeGenSize t), g i := by
  let _ : Fintype (GWVertex t) := instFintypeGWVertex t
  rw [← Fin.sum_univ_eq_sum_range]
  exact (gwVertexEquivFin t).sum_comp (fun i : Fin (gwTreeGenSize t) ↦ g i.1)

/-- Multiplying a function of `gwLeftCount t v` over `v : GWVertex t` equals multiplying over
`Finset.range (gwTreeGenSize t)`. -/
theorem prod_gwVertex_gwLeftCount {n : ℕ} {β : Type*} [CommMonoid β]
    (t : GWTree n) (g : ℕ → β) :
    (∏ v : GWVertex t, g (gwLeftCount t v)) = ∏ i ∈ Finset.range (gwTreeGenSize t), g i := by
  let _ : Fintype (GWVertex t) := instFintypeGWVertex t
  rw [← Fin.prod_univ_eq_prod_range]
  exact (gwVertexEquivFin t).prod_comp (fun i : Fin (gwTreeGenSize t) ↦ g i.1)

/-!
### 2. Leaf-Extension Equivalence for Planar Trees
-/

/-- Extend a depth-$n$ planar tree $t$ to depth $n + 1$ by attaching $c(v)$ children to each
generation-$n$ vertex $v \in \mathrm{GWVertex}(t)$. -/
def gwTreeExtend : ∀ {n : ℕ} (t : GWTree n), (GWVertex t → ℕ) → GWTree (n + 1)
  | 0, (), c => List.replicate (c ()) ()
  | _ + 1, ts, c =>
      List.ofFn fun i : Fin ts.length ↦
        gwTreeExtend (ts.get i) (fun u ↦ c ⟨i, u⟩)

@[simp]
theorem gwTreeExtend_nil {n : ℕ} (c : @GWVertex (n + 1) [] → ℕ) :
    @gwTreeExtend (n + 1) [] c = [] := rfl

theorem gwTreeExtend_cons {n : ℕ} (t : GWTree n) (ts : List (GWTree n))
    (c : @GWVertex (n + 1) (t :: ts) → ℕ) :
    @gwTreeExtend (n + 1) (t :: ts) c =
      gwTreeExtend t (fun u ↦ c ⟨0, u⟩) ::
        @gwTreeExtend (n + 1) ts (fun v ↦ c ⟨v.1.succ, v.2⟩) :=
  List.ofFn_succ

/-- The generation-$(n+1)$ size of `gwTreeExtend t c` is the sum of $c(v)$ over all
generation-$n$ vertices $v$ of $t$. -/
theorem gwTreeGenSize_gwTreeExtend :
    ∀ {n : ℕ} (t : GWTree n) (c : GWVertex t → ℕ),
      gwTreeGenSize (gwTreeExtend t c) = ∑ v : GWVertex t, c v
  | 0, (), c => by
      let c' : Unit → ℕ := c
      change ((List.replicate (c' ()) ()).map (fun _ : Unit ↦ 1)).sum = ∑ v : Unit, c' v
      rw [Finset.univ_unique, Finset.sum_singleton]
      simp
  | n + 1, (ts : List (GWTree n)), c => by
      let _ : ∀ i : Fin ts.length, Fintype (GWVertex (ts.get i)) :=
        fun i ↦ instFintypeGWVertex (ts.get i)
      let c' : (Σ i : Fin ts.length, GWVertex (ts.get i)) → ℕ := c
      change ((List.ofFn fun i : Fin ts.length ↦
        gwTreeExtend (ts.get i) (fun u ↦ c' ⟨i, u⟩)).map gwTreeGenSize).sum =
        ∑ v : Σ i : Fin ts.length, GWVertex (ts.get i), c' v
      rw [List.map_ofFn, List.sum_ofFn, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact gwTreeGenSize_gwTreeExtend (ts.get i) (fun u ↦ c' ⟨i, u⟩)

/-- The Galton–Watson tree probability of `gwTreeExtend t c` factors as the tree probability of $t$
times the product of offspring probabilities $\prod_{v \in \mathrm{GWVertex}(t)} p(c(v))$. -/
theorem gwProb_gwTreeExtend (p : ℕ → ℝ) :
    ∀ {n : ℕ} (t : GWTree n) (c : GWVertex t → ℕ),
      gwProb p (gwTreeExtend t c) =
        gwProb p t * ∏ v : GWVertex t, p (c v)
  | 0, (), c => by
      change p (List.replicate (c ()) ()).length *
        ((List.replicate (c ()) ()).map (fun _ : Unit ↦ (1 : ℝ))).prod =
        1 * ∏ v : Unit, p (c v)
      rw [Finset.univ_unique, Finset.prod_singleton]
      simp
  | n + 1, ts, c => by
      let _ : ∀ i : Fin ts.length, Fintype (GWVertex (ts.get i)) :=
        fun i ↦ instFintypeGWVertex (ts.get i)
      let _ : Fintype (GWVertex ts) := instFintypeGWVertex ts
      set L : List (GWTree (n + 1)) :=
        List.ofFn fun i : Fin ts.length ↦ gwTreeExtend (ts.get i) (fun u ↦ c ⟨i, u⟩)
      have hlen : L.length = ts.length := List.length_ofFn
      change p L.length * (L.map (gwProb p)).prod =
        (p ts.length * (List.map (gwProb p) ts).prod) *
          ∏ v : Σ i : Fin ts.length, GWVertex (ts.get i), p (c v)
      have hLprod : (L.map (gwProb p)).prod =
          ∏ i : Fin ts.length, gwProb p (gwTreeExtend (ts.get i) (fun u ↦ c ⟨i, u⟩)) := by
        dsimp only [L]
        rw [List.map_ofFn, List.prod_ofFn]
        rfl
      rw [hlen, hLprod, ← prod_fin_get_eq_map_prod (gwProb p) ts]
      simp_rw [gwProb_gwTreeExtend p (ts.get _) (fun u ↦ c ⟨_, u⟩)]
      rw [Finset.prod_mul_distrib, Fintype.prod_sigma, mul_assoc]

private theorem gwTreeExtend_list_inj {n : ℕ}
    (ih : Function.Injective (fun p : Σ t : GWTree n, (GWVertex t → ℕ) ↦ gwTreeExtend p.1 p.2)) :
    ∀ (ts₁ ts₂ : List (GWTree n)) (c₁ : @GWVertex (n + 1) ts₁ → ℕ)
      (c₂ : @GWVertex (n + 1) ts₂ → ℕ),
      @gwTreeExtend (n + 1) ts₁ c₁ = @gwTreeExtend (n + 1) ts₂ c₂ →
      (⟨ts₁, c₁⟩ : Σ ts : List (GWTree n), (@GWVertex (n + 1) ts → ℕ)) = ⟨ts₂, c₂⟩
  | [], [], c₁, c₂, _ => by
      congr
      ext ⟨i, _⟩
      exact Fin.elim0 i
  | [], t₂ :: ts₂, c₁, c₂, h => by
      have hlen := congrArg List.length h
      simp [gwTreeExtend] at hlen
  | t₁ :: ts₁, [], c₁, c₂, h => by
      have hlen := congrArg List.length h
      simp [gwTreeExtend] at hlen
  | t₁ :: ts₁, t₂ :: ts₂, c₁, c₂, h => by
      have hcons :
          gwTreeExtend t₁ (fun u ↦ c₁ ⟨0, u⟩) ::
            @gwTreeExtend (n + 1) ts₁ (fun v ↦ c₁ ⟨v.1.succ, v.2⟩) =
          gwTreeExtend t₂ (fun u ↦ c₂ ⟨0, u⟩) ::
            @gwTreeExtend (n + 1) ts₂ (fun v ↦ c₂ ⟨v.1.succ, v.2⟩) :=
        (gwTreeExtend_cons t₁ ts₁ c₁).symm.trans (h.trans (gwTreeExtend_cons t₂ ts₂ c₂))
      have hhead := @ih ⟨t₁, fun u ↦ c₁ ⟨0, u⟩⟩ ⟨t₂, fun u ↦ c₂ ⟨0, u⟩⟩ (List.cons.inj hcons).1
      have htail := gwTreeExtend_list_inj ih ts₁ ts₂
        (fun v ↦ c₁ ⟨v.1.succ, v.2⟩) (fun v ↦ c₂ ⟨v.1.succ, v.2⟩) (List.cons.inj hcons).2
      have ht : t₁ = t₂ := congrArg Sigma.fst hhead
      have hts : ts₁ = ts₂ := congrArg Sigma.fst htail
      subst ht; subst hts
      have hc0 : (fun u ↦ c₁ ⟨0, u⟩) = (fun u ↦ c₂ ⟨0, u⟩) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hhead).2
      have hcs : (fun v : @GWVertex (n + 1) ts₁ ↦ c₁ ⟨v.1.succ, v.2⟩) =
          (fun v ↦ c₂ ⟨v.1.succ, v.2⟩) :=
        eq_of_heq (Sigma.mk.inj_iff.mp htail).2
      congr
      ext ⟨i, u⟩
      revert u
      refine Fin.cases ?_ ?_ i
      · exact congrFun hc0
      · intro j u
        exact congrFun hcs ⟨j, u⟩

/-- `gwTreeExtend` is injective on `Σ t : GWTree n, (GWVertex t → ℕ)`. -/
theorem gwTreeExtend_injective :
    ∀ (n : ℕ), Function.Injective
      (fun p : Σ t : GWTree n, (GWVertex t → ℕ) ↦ gwTreeExtend p.1 p.2)
  | 0, ⟨(), c₁⟩, ⟨(), c₂⟩, h => by
      have hlen : (List.replicate (c₁ ()) ()).length = (List.replicate (c₂ ()) ()).length :=
        congrArg List.length h
      simp only [List.length_replicate] at hlen
      congr
      ext ⟨⟩
      exact hlen
  | n + 1, ⟨ts₁, c₁⟩, ⟨ts₂, c₂⟩, h =>
      gwTreeExtend_list_inj (gwTreeExtend_injective n) ts₁ ts₂ c₁ c₂ h

private theorem gwTreeExtend_list_surj {n : ℕ}
    (ih : Function.Surjective (fun p : Σ t : GWTree n, (GWVertex t → ℕ) ↦ gwTreeExtend p.1 p.2)) :
    ∀ (ss : List (GWTree (n + 1))),
      ∃ p : Σ ts : List (GWTree n), (@GWVertex (n + 1) ts → ℕ),
        @gwTreeExtend (n + 1) p.1 p.2 = ss
  | [] => ⟨⟨[], fun v ↦ Fin.elim0 v.1⟩, rfl⟩
  | s :: ss => by
      obtain ⟨⟨t, c₀⟩, hs⟩ := ih s
      obtain ⟨⟨ts, c'⟩, hss⟩ := gwTreeExtend_list_surj ih ss
      let c : @GWVertex (n + 1) (t :: ts) → ℕ :=
        fun ⟨i, u⟩ ↦
          Fin.cases (motive := fun i : Fin (ts.length + 1) ↦
            GWVertex ((t :: ts).get i) → ℕ)
            c₀ (fun j u' ↦ c' ⟨j, u'⟩) i u
      have hsucc : (fun v : @GWVertex (n + 1) ts ↦ c ⟨v.1.succ, v.2⟩) = c' := by
        ext ⟨j, u⟩; rfl
      refine ⟨⟨t :: ts, c⟩, ?_⟩
      exact (gwTreeExtend_cons t ts c).trans
        (congrArg₂ List.cons hs (hsucc.symm ▸ hss))

/-- `gwTreeExtend` is surjective onto `GWTree (n + 1)`. -/
theorem gwTreeExtend_surjective :
    ∀ (n : ℕ), Function.Surjective
      (fun p : Σ t : GWTree n, (GWVertex t → ℕ) ↦ gwTreeExtend p.1 p.2)
  | 0, (s : List Unit) => by
      refine ⟨⟨(), fun _ ↦ s.length⟩, ?_⟩
      change List.replicate s.length () = s
      exact (List.eq_replicate_iff.2 ⟨rfl, fun x _ ↦ Subsingleton.elim x ()⟩).symm
  | n + 1, (ss : List (GWTree (n + 1))) =>
      gwTreeExtend_list_surj (gwTreeExtend_surjective n) ss

/-- Leaf-extension equivalence `(Σ t : GWTree n, (GWVertex t → ℕ)) ≃ GWTree (n + 1)`. -/
noncomputable def gwTreeEquivSigma (n : ℕ) :
    (Σ t : GWTree n, (GWVertex t → ℕ)) ≃ GWTree (n + 1) :=
  Equiv.ofBijective (fun p ↦ gwTreeExtend p.1 p.2)
    ⟨gwTreeExtend_injective n, gwTreeExtend_surjective n⟩

@[simp]
theorem gwTreeEquivSigma_apply (n : ℕ) (p : Σ t : GWTree n, (GWVertex t → ℕ)) :
    gwTreeEquivSigma n p = gwTreeExtend p.1 p.2 := rfl

/-!
### 3. Canonical Random Tree, Row Independence, and `Sec5_3_gwProb_sum_genSize`
-/

/-- Measurability of a random finite sum `∑ i ∈ Finset.range (f ω), g i ω`. -/
theorem measurable_sum_range {α : Type*} [MeasurableSpace α] {f : α → ℕ} {g : ℕ → α → ℕ}
    (hf : Measurable f) (hg : ∀ i, Measurable (g i)) :
    Measurable (fun ω ↦ ∑ i ∈ Finset.range (f ω), g i ω) := by
  intro s hs
  have hpre : (fun ω ↦ ∑ i ∈ Finset.range (f ω), g i ω) ⁻¹' s =
      ⋃ m : ℕ, f ⁻¹' {m} ∩ (fun ω ↦ ∑ i ∈ Finset.range m, g i ω) ⁻¹' s := by
    ext ω; simp
  rw [hpre]
  exact MeasurableSet.iUnion fun m ↦
    (hf (measurableSet_singleton m)).inter
      ((Finset.measurable_sum (Finset.range m) fun i _ ↦ hg i) hs)

/-- `gwCanonical ξ n` is measurable whenever every `ξ p` is measurable. -/
theorem measurable_gwCanonical {α : Type*} [MeasurableSpace α] {ξ : ℕ × ℕ → α → ℕ}
    (hξ : ∀ p, Measurable (ξ p)) : ∀ n : ℕ, Measurable (gwCanonical ξ n)
  | 0 => measurable_const
  | n + 1 => measurable_sum_range (measurable_gwCanonical hξ n) (fun i ↦ hξ (n, i))

/-- `GWTree n` is countable for every $n$. -/
instance instCountableGWTree : ∀ n : ℕ, Countable (GWTree n)
  | 0 => inferInstanceAs (Countable Unit)
  | n + 1 =>
      letI : Countable (GWTree n) := instCountableGWTree n
      inferInstanceAs (Countable (List (GWTree n)))

/-- Discrete measurable space on `GWTree n`. -/
instance instMeasurableSpaceGWTree (n : ℕ) : MeasurableSpace (GWTree n) := ⊤

instance instMeasurableSingletonClassGWTree (n : ℕ) :
    MeasurableSingletonClass (GWTree n) := ⟨fun _ ↦ trivial⟩

/-- Canonical random planar tree of depth $n$ built from an offspring array $\xi$. -/
def gwTreeOfArray {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) : ∀ n : ℕ, Ω → GWTree n
  | 0, _ => ()
  | n + 1, ω =>
      gwTreeExtend (gwTreeOfArray ξ n ω)
        (fun v ↦ ξ (n, gwLeftCount (gwTreeOfArray ξ n ω) v) ω)

/-- The generation-$n$ size of `gwTreeOfArray ξ n ω` equals `gwCanonical ξ n ω` pointwise. -/
theorem gwTreeGenSize_gwTreeOfArray {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) :
    ∀ (n : ℕ) (ω : Ω), gwTreeGenSize (gwTreeOfArray ξ n ω) = gwCanonical ξ n ω
  | 0, _ => rfl
  | n + 1, ω => by
      simp only [gwTreeOfArray, gwTreeGenSize_gwTreeExtend,
        sum_gwVertex_gwLeftCount (gwTreeOfArray ξ n ω) (fun i ↦ ξ (n, i) ω),
        gwTreeGenSize_gwTreeOfArray ξ n ω, gwCanonical]

/-- Canonical tree of depth $n$ viewed as a function of the first $n$ rows
`Finset.range n → (ℕ → ℕ)` of the offspring array. -/
def gwTreeOfFinRows : ∀ n : ℕ, (Finset.range n → (ℕ → ℕ)) → GWTree n
  | 0, _ => ()
  | n + 1, r =>
      let t := gwTreeOfFinRows n (fun j : Finset.range n ↦
        r ⟨j.1, Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 j.2))⟩)
      gwTreeExtend t
        (fun v ↦ r ⟨n, Finset.mem_range.2 (Nat.lt_succ_self n)⟩ (gwLeftCount t v))

theorem gwTreeOfFinRows_eq_gwTreeOfArray {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) :
    ∀ (n : ℕ) (ω : Ω),
      gwTreeOfFinRows n (fun (j : Finset.range n) (i : ℕ) ↦ ξ (j.1, i) ω) =
        gwTreeOfArray ξ n ω
  | 0, _ => rfl
  | n + 1, ω => by
      dsimp only [gwTreeOfFinRows, gwTreeOfArray]
      rw [gwTreeOfFinRows_eq_gwTreeOfArray ξ n ω]

/-- Measurability of `gwTreeOfFinRows n`. -/
theorem measurable_gwTreeOfFinRows :
    ∀ n : ℕ, Measurable (gwTreeOfFinRows n)
  | 0 => measurable_const
  | n + 1 => by
      have ih := measurable_gwTreeOfFinRows n
      have hproj : Measurable (fun (r : Finset.range (n + 1) → (ℕ → ℕ)) (j : Finset.range n) ↦
          r ⟨j.1, Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 j.2))⟩) :=
        measurable_pi_iff.2 fun j ↦ measurable_pi_apply _
      have ht : Measurable (fun r : Finset.range (n + 1) → (ℕ → ℕ) ↦
          gwTreeOfFinRows n (fun j : Finset.range n ↦
            r ⟨j.1, Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 j.2))⟩)) :=
        ih.comp hproj
      intro s _
      let hn : n ∈ Finset.range (n + 1) := Finset.mem_range.2 (Nat.lt_succ_self n)
      have hpre : gwTreeOfFinRows (n + 1) ⁻¹' s =
          ⋃ t : GWTree n,
            {r | gwTreeOfFinRows n (fun j : Finset.range n ↦
              r ⟨j.1, Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 j.2))⟩) = t} ∩
            {r | gwTreeExtend t (fun v ↦ r ⟨n, hn⟩ (gwLeftCount t v)) ∈ s} := by
        ext r
        simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred]
        exact ⟨fun h ↦ ⟨_, rfl, h⟩, by rintro ⟨t, rfl, h⟩; exact h⟩
      rw [hpre]
      refine MeasurableSet.iUnion fun t ↦ (ht (measurableSet_singleton t)).inter ?_
      let _ : Fintype (GWVertex t) := instFintypeGWVertex t
      have hc : Measurable (fun (r : Finset.range (n + 1) → (ℕ → ℕ)) (v : GWVertex t) ↦
          r ⟨n, hn⟩ (gwLeftCount t v)) :=
        measurable_pi_iff.2 fun v ↦
          (measurable_pi_apply (gwLeftCount t v)).comp (measurable_pi_apply _)
      exact (measurable_of_countable (gwTreeExtend t)).comp hc trivial

/-- `gwTreeOfArray ξ n` is measurable whenever every `ξ p` is measurable. -/
theorem measurable_gwTreeOfArray {Ω : Type*} [MeasurableSpace Ω] {ξ : ℕ × ℕ → Ω → ℕ}
    (hξ : ∀ p, Measurable (ξ p)) (n : ℕ) :
    Measurable (gwTreeOfArray ξ n) := by
  have heq : gwTreeOfArray ξ n =
      gwTreeOfFinRows n ∘ (fun ω (j : Finset.range n) (i : ℕ) ↦ ξ (j.1, i) ω) := by
    ext ω; exact (gwTreeOfFinRows_eq_gwTreeOfArray ξ n ω).symm
  rw [heq]
  refine (measurable_gwTreeOfFinRows n).comp ?_
  exact measurable_pi_iff.2 fun j ↦ measurable_pi_iff.2 fun i ↦ hξ (j.1, i)

/-- If `ξ : ℕ × ℕ → Ω → ℕ` is an independent array, its rows `R n ω i := ξ (n, i) ω` are
mutually independent. -/
theorem iIndepFun_row_of_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ × ℕ → Ω → ℕ}
    (hξ_meas : ∀ p, Measurable (ξ p)) (hξ_indep : iIndepFun ξ P) :
    iIndepFun (fun (n : ℕ) (ω : Ω) (i : ℕ) ↦ ξ (n, i) ω) P := by
  have hrow_meas : ∀ n : ℕ, Measurable (fun (ω : Ω) (i : ℕ) ↦ ξ (n, i) ω) :=
    fun n ↦ measurable_pi_iff.2 fun i ↦ hξ_meas (n, i)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hrow_meas]
  have hcurry : (fun (ω : Ω) (n : ℕ) (i : ℕ) ↦ ξ (n, i) ω) =
      (MeasurableEquiv.curry ℕ ℕ ℕ) ∘ (fun (ω : Ω) (p : ℕ × ℕ) ↦ ξ p ω) := rfl
  rw [hcurry, ← Measure.map_map (MeasurableEquiv.curry ℕ ℕ ℕ).measurable
      (measurable_pi_iff.2 hξ_meas),
    hξ_indep.map_fun_eq_infinitePi_map hξ_meas,
    Measure.infinitePi_map_curry (fun n i ↦ P.map (ξ (n, i)))]
  congr 1
  funext n
  have hn_indep : iIndepFun (fun i ω ↦ ξ (n, i) ω) P :=
    hξ_indep.precomp (Prod.mk_right_injective n)
  exact (hn_indep.map_fun_eq_infinitePi_map (fun i ↦ hξ_meas (n, i))).symm

/-- `gwTreeOfArray ξ n` is independent of row $n$ of $\xi$. -/
theorem indepFun_gwTreeOfArray_row {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ × ℕ → Ω → ℕ}
    (hξ_meas : ∀ p, Measurable (ξ p)) (hξ_indep : iIndepFun ξ P) (n : ℕ) :
    IndepFun (gwTreeOfArray ξ n) (fun ω (i : ℕ) ↦ ξ (n, i) ω) P := by
  let R : ℕ → Ω → (ℕ → ℕ) := fun m ω i ↦ ξ (m, i) ω
  have hR_meas : ∀ m, AEMeasurable (R m) P :=
    fun m ↦ (measurable_pi_iff.2 fun i ↦ hξ_meas (m, i)).aemeasurable
  have hR_indep : iIndepFun R P := iIndepFun_row_of_iIndepFun hξ_meas hξ_indep
  have hdisj : Disjoint (Finset.range n) ({n} : Finset ℕ) := by simp
  have hind := hR_indep.indepFun_finset₀ (Finset.range n) {n} hdisj hR_meas
  have hcomp := hind.comp (measurable_gwTreeOfFinRows n)
    (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ)))
  convert hcomp using 1
  · ext ω
    exact (gwTreeOfFinRows_eq_gwTreeOfArray ξ n ω).symm
  · rfl

/-- `gwCanonical ξ n` is independent of row $n$ of $\xi$. -/
theorem indepFun_gwCanonical_row {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ × ℕ → Ω → ℕ}
    (hξ_meas : ∀ p, Measurable (ξ p)) (hξ_indep : iIndepFun ξ P) (n : ℕ) :
    IndepFun (gwCanonical ξ n) (fun ω (i : ℕ) ↦ ξ (n, i) ω) P := by
  have heq : gwCanonical ξ n = gwTreeGenSize ∘ gwTreeOfArray ξ n := by
    ext ω; exact (gwTreeGenSize_gwTreeOfArray ξ n ω).symm
  rw [heq]
  exact (indepFun_gwTreeOfArray_row hξ_meas hξ_indep n).comp
    (measurable_of_countable gwTreeGenSize) measurable_id

/-- Countable fiber decomposition of `P.real` for a measurable map into a countable
discrete type. -/
theorem measureReal_inter_fiber_tsum {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α] (P : Measure Ω) [IsFiniteMeasure P]
    {E : Set Ω} (hE : MeasurableSet E) {f : Ω → α} (hf : Measurable f) (Q : α → Prop) :
    (∑' a : {a : α // Q a}, P.real (E ∩ {ω | f ω = a.1})) =
      P.real (E ∩ {ω | Q (f ω)}) ∧
    Summable (fun a : {a : α // Q a} ↦ P.real (E ∩ {ω | f ω = a.1})) := by
  let A : {a : α // Q a} → Set Ω := fun a ↦ E ∩ {ω | f ω = a.1}
  have hA_meas : ∀ a, MeasurableSet (A a) :=
    fun a ↦ hE.inter (hf (measurableSet_singleton a.1))
  have hA_disj : Pairwise (fun a b ↦ Disjoint (A a) (A b)) := by
    intro a b hab
    refine Set.disjoint_left.2 fun ω hωa hωb ↦ hab (Subtype.ext ?_)
    have ha : f ω = a.1 := hωa.2
    have hb : f ω = b.1 := hωb.2
    exact ha.symm.trans hb
  have hA_union : (⋃ a : {a : α // Q a}, A a) = E ∩ {ω | Q (f ω)} := by
    ext ω
    simp only [A, mem_iUnion, mem_inter_iff, mem_ofPred, Subtype.exists]
    exact ⟨fun ⟨a, ha, hEω, hfω⟩ ↦ ⟨hEω, hfω ▸ ha⟩, fun ⟨hEω, hQ⟩ ↦ ⟨f ω, hQ, hEω, rfl⟩⟩
  have hmeas_eq : P (E ∩ {ω | Q (f ω)}) = ∑' a : {a : α // Q a}, P (A a) := by
    rw [← hA_union, measure_iUnion hA_disj hA_meas]
  have hne_top : (∑' a : {a : α // Q a}, P (A a)) ≠ ⊤ := by
    rw [← hmeas_eq]; exact measure_ne_top P _
  refine ⟨?_, ENNReal.summable_toReal hne_top⟩
  simp only [Measure.real, hmeas_eq]
  exact (ENNReal.tsum_toReal_eq (fun a ↦ measure_ne_top P (A a))).symm

/-- For an i.i.d. offspring array $\xi'$ with the law of $Z_1$, the probability that
`gwTreeOfArray ξ' n` equals a depth-$n$ planar tree $t$ is
`gwProb (fun k ↦ P.real {ω | Z 1 ω = k}) t`. -/
theorem measureReal_gwTreeOfArray_eq_gwProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → ℕ)
    {ξ : ℕ × ℕ → Ω → ℕ} (hξ_meas : ∀ p, Measurable (ξ p))
    (hξ_indep : iIndepFun ξ P) (hξ_ident : ∀ p, IdentDistrib (ξ p) (Z 1) P P) :
    ∀ (n : ℕ) (t : GWTree n),
      P.real {ω | gwTreeOfArray ξ n ω = t} = gwProb (fun k ↦ P.real {ω | Z 1 ω = k}) t
  | 0, () => by
      have huniv : {ω : Ω | gwTreeOfArray ξ 0 ω = ()} = univ := by
        ext; exact ⟨fun _ ↦ trivial, fun _ ↦ rfl⟩
      rw [huniv, probReal_univ, gwProb]
  | n + 1, s => by
      obtain ⟨⟨t, c⟩, rfl⟩ := gwTreeExtend_surjective n s
      let _ : Fintype (GWVertex t) := instFintypeGWVertex t
      have hevent : {ω : Ω | gwTreeOfArray ξ (n + 1) ω = gwTreeExtend t c} =
          {ω | gwTreeOfArray ξ n ω = t} ∩
          {ω | (fun v : GWVertex t ↦ ξ (n, gwLeftCount t v) ω) = c} := by
        ext ω
        simp only [gwTreeOfArray, mem_ofPred, mem_inter_iff]
        constructor
        · intro h
          have hinj := @gwTreeExtend_injective n
            ⟨gwTreeOfArray ξ n ω, fun v ↦ ξ (n, gwLeftCount (gwTreeOfArray ξ n ω) v) ω⟩
            ⟨t, c⟩ h
          have ht : gwTreeOfArray ξ n ω = t := congrArg Sigma.fst hinj
          subst ht
          exact ⟨rfl, eq_of_heq (Sigma.mk.inj_iff.mp hinj).2⟩
        · rintro ⟨rfl, hc⟩
          rw [hc]
      have hind_tree_row := indepFun_gwTreeOfArray_row hξ_meas hξ_indep n
      have hproj_meas : Measurable (fun (r : ℕ → ℕ) (v : GWVertex t) ↦ r (gwLeftCount t v)) :=
        measurable_pi_iff.2 fun v ↦ measurable_pi_apply (gwLeftCount t v)
      have hind_tree_tuple :
          IndepFun (gwTreeOfArray ξ n) (fun ω (v : GWVertex t) ↦ ξ (n, gwLeftCount t v) ω) P :=
        hind_tree_row.comp measurable_id hproj_meas
      have hinter : P.real ({ω | gwTreeOfArray ξ n ω = t} ∩
          {ω | (fun v : GWVertex t ↦ ξ (n, gwLeftCount t v) ω) = c}) =
          P.real {ω | gwTreeOfArray ξ n ω = t} *
            P.real {ω | (fun v : GWVertex t ↦ ξ (n, gwLeftCount t v) ω) = c} := by
        change P.real (gwTreeOfArray ξ n ⁻¹' {t} ∩
          (fun ω (v : GWVertex t) ↦ ξ (n, gwLeftCount t v) ω) ⁻¹' {c}) = _
        simp only [Measure.real]
        rw [hind_tree_tuple.measure_inter_preimage_eq_mul {t} {c} (measurableSet_singleton t)
          (measurableSet_singleton c), ENNReal.toReal_mul]
        rfl
      have htuple_indep : iIndepFun (fun (v : GWVertex t) ω ↦ ξ (n, gwLeftCount t v) ω) P := by
        refine hξ_indep.precomp ?_
        intro u v huv
        injection huv with _ h2
        exact gwLeftCount_injective t h2
      have htuple_prob : P.real {ω | (fun v : GWVertex t ↦ ξ (n, gwLeftCount t v) ω) = c} =
          ∏ v : GWVertex t, P.real {ω | Z 1 ω = c v} := by
        have hset : {ω : Ω | (fun v : GWVertex t ↦ ξ (n, gwLeftCount t v) ω) = c} =
            ⋂ v ∈ (Finset.univ : Finset (GWVertex t)),
              (fun ω ↦ ξ (n, gwLeftCount t v) ω) ⁻¹' {c v} := by
          ext ω; simp [funext_iff]
        rw [hset, Measure.real,
          htuple_indep.measure_inter_preimage_eq_mul Finset.univ
            (fun v _ ↦ measurableSet_singleton (c v)),
          ENNReal.toReal_prod]
        refine Finset.prod_congr rfl fun v _ ↦ ?_
        have hid := (hξ_ident (n, gwLeftCount t v)).measure_mem_eq (measurableSet_singleton (c v))
        exact congrArg ENNReal.toReal hid
      rw [hevent, hinter, measureReal_gwTreeOfArray_eq_gwProb P Z hξ_meas hξ_indep hξ_ident n t,
        htuple_prob, gwProb_gwTreeExtend]

/-- Measurable modification of the offspring array of a Galton–Watson process. -/
theorem IsGaltonWatson.exists_measurable_array {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) :
    ∃ ξ' : ℕ × ℕ → Ω → ℕ,
      (∀ p, Measurable (ξ' p)) ∧
      iIndepFun ξ' P ∧
      (∀ p, IdentDistrib (ξ' p) (Z 1) P P) ∧
      (∀ n, Z n =ᵐ[P] gwCanonical ξ' n) := by
  rcases hGW with ⟨_, ξ, hξ_meas, hξ_indep, hξ_ident, hZ0, hZn⟩
  let ξ' : ℕ × ℕ → Ω → ℕ := fun p ↦ (hξ_meas p).mk (ξ p)
  have hξ_ae : ∀ p, ξ p =ᵐ[P] ξ' p := fun p ↦ (hξ_meas p).ae_eq_mk
  refine ⟨ξ', fun p ↦ (hξ_meas p).measurable_mk, hξ_indep.congr hξ_ae,
    fun p ↦ (IdentDistrib.of_ae_eq (hξ_meas p).measurable_mk.aemeasurable
      (hξ_ae p).symm).trans (hξ_ident p), ?_⟩
  intro n
  induction n with
  | zero => exact hZ0
  | succ n ih =>
      have hrow_ae : ∀ᵐ ω ∂P, ∀ i : ℕ, ξ (n, i) ω = ξ' (n, i) ω :=
        ae_all_iff.2 fun i ↦ hξ_ae (n, i)
      filter_upwards [hZn n, ih, hrow_ae] with ω h1 h2 h3
      rw [h1, h2, gwCanonical]
      exact Finset.sum_congr rfl fun i _ ↦ h3 i

/-- Every generation $Z_n$ of a Galton–Watson process is almost everywhere measurable. -/
theorem IsGaltonWatson.aemeasurable_Z {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (n : ℕ) :
    AEMeasurable (Z n) P := by
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  exact (measurable_gwCanonical hξ'_meas n).aemeasurable.congr (hZ_ae n).symm

/-- Section 5.3 tree-probability link to the Galton–Watson generation-size law and normalization
(`I-1(a,c)`, `SteinIntro.tex:3047-3048, 3074-3076`): for a Galton–Watson process with offspring
PMF $p(k) = \mathbb{P}(Z_1 = k)$, summing `gwProb p t` over all depth-$n$ planar trees with
$t_n = k$ yields $\mathbb{P}(Z_n = k)$, and summing `gwProb p t` over all depth-$n$ planar trees
yields $1$. -/
def Sec5_3_gwProb_sum_genSize_stmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    let p : ℕ → ℝ := fun k ↦ P.real {ω | Z 1 ω = k}
    ∀ n : ℕ,
      (Summable (gwProb p : GWTree n → ℝ) ∧ (∑' t : GWTree n, gwProb p t) = 1) ∧
      ∀ k : ℕ,
        Summable (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwProb p t.1) ∧
        (∑' t : {t : GWTree n // gwTreeGenSize t = k}, gwProb p t.1) =
          P.real {ω | Z n ω = k}

theorem sec5_3_gwProb_sum_genSize : Sec5_3_gwProb_sum_genSize_stmt := by
  intro Ω _ P _ Z hGW p n
  obtain ⟨ξ', hξ'_meas, hξ'_indep, hξ'_ident, hZ_ae⟩ := hGW.exists_measurable_array
  have hT_meas : Measurable (gwTreeOfArray ξ' n) := measurable_gwTreeOfArray hξ'_meas n
  have hprob : ∀ t : GWTree n, gwProb p t = P.real {ω | gwTreeOfArray ξ' n ω = t} :=
    fun t ↦ (measureReal_gwTreeOfArray_eq_gwProb P Z hξ'_meas hξ'_indep hξ'_ident n t).symm
  constructor
  · change Summable (fun t : GWTree n ↦ gwProb p t) ∧ (∑' t : GWTree n, gwProb p t) = 1
    simp_rw [hprob]
    obtain ⟨htsum, hsum⟩ := measureReal_inter_fiber_tsum P MeasurableSet.univ hT_meas
      (fun _ : GWTree n ↦ True)
    simp only [univ_inter] at htsum hsum
    rw [Set.ofPred_true, probReal_univ] at htsum
    let e := Equiv.subtypeUnivEquiv (α := GWTree n) (p := fun _ ↦ True) (fun _ ↦ trivial)
    refine ⟨(e.summable_iff (f := fun t : GWTree n ↦
      P.real {ω | gwTreeOfArray ξ' n ω = t})).mp hsum, ?_⟩
    rw [← htsum]
    exact (e.tsum_eq (fun t : GWTree n ↦ P.real {ω | gwTreeOfArray ξ' n ω = t})).symm
  · intro k
    simp_rw [hprob]
    obtain ⟨htsum, hsum⟩ := measureReal_inter_fiber_tsum P MeasurableSet.univ hT_meas
      (fun t : GWTree n ↦ gwTreeGenSize t = k)
    simp only [univ_inter] at htsum hsum
    refine ⟨hsum, ?_⟩
    rw [htsum]
    simp_rw [gwTreeGenSize_gwTreeOfArray]
    refine measureReal_congr ?_
    filter_upwards [hZ_ae n] with ω hω
    simp [hω]

/-!
### 4. Moments, PGF Iteration, and Extinction Dichotomy
-/

/-- The Lebesgue integral of $Z_n$ equals $(\int^- Z_1\,dP)^n$. -/
theorem IsGaltonWatson.lintegral_Z {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (n : ℕ) :
    (∫⁻ ω, (Z n ω : ℝ≥0∞) ∂P) = (∫⁻ ω, (Z 1 ω : ℝ≥0∞) ∂P) ^ n := by
  obtain ⟨ξ', hξ'_meas, hξ'_indep, hξ'_ident, hZ_ae⟩ := hGW.exists_measurable_array
  set μ₁ : ℝ≥0∞ := ∫⁻ ω, (Z 1 ω : ℝ≥0∞) ∂P
  have hξ'_lint : ∀ p, (∫⁻ ω, (ξ' p ω : ℝ≥0∞) ∂P) = μ₁ := by
    intro p
    have h := (hξ'_ident p).comp (measurable_of_countable (fun k : ℕ ↦ (k : ℝ≥0∞)))
    exact h.lintegral_eq
  have hcanon : ∀ m : ℕ, (∫⁻ ω, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) = μ₁ ^ m := by
    intro m
    induction m with
    | zero => simp [gwCanonical]
    | succ m ih =>
        have hZ'_meas : Measurable (gwCanonical ξ' m) := measurable_gwCanonical hξ'_meas m
        let E : ℕ → Set Ω := fun k ↦ {ω | gwCanonical ξ' m ω = k}
        have hE_meas : ∀ k, MeasurableSet (E k) := fun k ↦ hZ'_meas (measurableSet_singleton k)
        have hE_disj : Pairwise (fun j k ↦ Disjoint (E j) (E k)) := by
          intro j k hjk
          refine Set.disjoint_left.2 fun ω (hj : gwCanonical ξ' m ω = j)
            (hk : gwCanonical ξ' m ω = k) ↦ hjk (hj.symm.trans hk)
        have hE_union : (⋃ k : ℕ, E k) = univ := by ext ω; simp [E]
        have hstep : ∀ k : ℕ,
            (∫⁻ ω in E k, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) ∂P) =
              (∫⁻ ω in E k, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) * μ₁ := by
          intro k
          have hcongr1 : ∀ ω ∈ E k, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) =
              ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞) := by
            intro ω hω
            have hω' : gwCanonical ξ' m ω = k := hω
            simp [gwCanonical, hω']
          have hcongr2 : ∀ ω ∈ E k, (gwCanonical ξ' m ω : ℝ≥0∞) = (k : ℝ≥0∞) :=
            fun ω hω ↦ congrArg Nat.cast hω
          rw [setLIntegral_congr_fun (hE_meas k) hcongr1,
            setLIntegral_congr_fun (hE_meas k) hcongr2,
            setLIntegral_const, ← lintegral_indicator (hE_meas k)]
          have hind_row := indepFun_gwCanonical_row hξ'_meas hξ'_indep m
          have hsum_meas : Measurable (fun r : ℕ → ℕ ↦ ∑ i ∈ Finset.range k, (r i : ℝ≥0∞)) :=
            Finset.measurable_sum (Finset.range k) fun i _ ↦
              (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp (measurable_pi_apply i)
          have hsum_meas_ω : Measurable (fun ω ↦ ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞)) :=
            hsum_meas.comp (measurable_pi_iff.2 fun i ↦ hξ'_meas (m, i))
          have hind_ind : IndepFun
              ((E k).indicator (fun _ ↦ (1 : ℝ≥0∞)))
              (fun ω ↦ ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞)) P := by
            have h1 : (E k).indicator (fun _ ↦ (1 : ℝ≥0∞)) =
                (Set.indicator {k} (fun _ ↦ (1 : ℝ≥0∞))) ∘ gwCanonical ξ' m := by
              ext ω; by_cases h : gwCanonical ξ' m ω = k <;> simp [E, h]
            rw [h1]
            exact hind_row.comp (measurable_of_countable _) hsum_meas
          have hrew : (E k).indicator (fun ω ↦ ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞)) =
              (fun ω ↦ (E k).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
                ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞)) := by
            ext ω; by_cases hω : ω ∈ E k <;> simp [hω]
          have hterm_meas : ∀ i : ℕ, Measurable (fun ω ↦ (ξ' (m, i) ω : ℝ≥0∞)) :=
            fun i ↦ (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp (hξ'_meas (m, i))
          rw [hrew, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
            (measurable_const.indicator (hE_meas k)).aemeasurable
            hsum_meas_ω.aemeasurable hind_ind,
            lintegral_indicator (hE_meas k), setLIntegral_const, one_mul,
            lintegral_finsetSum (Finset.range k) (fun i _ ↦ hterm_meas i)]
          simp_rw [hξ'_lint (m, _)]
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
        calc (∫⁻ ω, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) ∂P)
          _ = ∫⁻ ω in ⋃ k : ℕ, E k, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) ∂P := by
              rw [hE_union, Measure.restrict_univ]
          _ = ∑' k : ℕ, ∫⁻ ω in E k, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) ∂P :=
              lintegral_iUnion hE_meas hE_disj _
          _ = ∑' k : ℕ, (∫⁻ ω in E k, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) * μ₁ := by
              simp_rw [hstep]
          _ = (∑' k : ℕ, ∫⁻ ω in E k, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) * μ₁ :=
              ENNReal.tsum_mul_right
          _ = (∫⁻ ω in ⋃ k : ℕ, E k, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) * μ₁ := by
              rw [← lintegral_iUnion hE_meas hE_disj]
          _ = μ₁ ^ (m + 1) := by
              rw [hE_union, Measure.restrict_univ, ih, pow_succ]
  rw [lintegral_congr_ae (hZ_ae n |>.mono fun ω hω ↦ congrArg Nat.cast hω)]
  exact hcanon n

/-- Every generation $Z_n$ of a Galton–Watson process is integrable. -/
theorem IsGaltonWatson.integrable_Z {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (n : ℕ) :
    Integrable (fun ω ↦ (Z n ω : ℝ)) P := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ (Z n ω : ℝ)) P :=
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp_aemeasurable
      (hGW.aemeasurable_Z n)).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  have h1 := hGW.1.2
  simp only [HasFiniteIntegral, Real.enorm_natCast] at h1 ⊢
  rw [hGW.lintegral_Z n]
  exact ENNReal.pow_lt_top h1

/-- For any Galton–Watson process, $\mathbb{E}[Z_n] = (\mathbb{E}[Z_1])^n$. -/
theorem IsGaltonWatson.integral_Z {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (n : ℕ) :
    (∫ ω, (Z n ω : ℝ) ∂P) = (∫ ω, (Z 1 ω : ℝ) ∂P) ^ n := by
  have h_eq : ∀ m : ℕ, (∫ ω, (Z m ω : ℝ) ∂P) = (∫⁻ ω, (Z m ω : ℝ≥0∞) ∂P).toReal := by
    intro m
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ Nat.cast_nonneg (Z m ω))
      (hGW.integrable_Z m).1]
    congr with ω
    exact ENNReal.ofReal_natCast (Z m ω)
  rw [h_eq n, h_eq 1, hGW.lintegral_Z n, ENNReal.toReal_pow]

/-- In a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$),
$\mathbb{E}[Z_n] = 1$ for all $n$. -/
theorem IsGaltonWatson.integral_Z_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) (n : ℕ) :
    ∫ ω, (Z n ω : ℝ) ∂P = 1 := by
  rw [hGW.integral_Z n, hcrit, one_pow]

/-- In a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$),
$\mathbb{P}(Z_n > 0) > 0$ for all $n$. -/
theorem IsGaltonWatson.measureReal_Z_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) (n : ℕ) :
    0 < P.real {ω | 0 < Z n ω} := by
  have hset : {ω : Ω | 0 < Z n ω} = {ω : Ω | 0 < (Z n ω : ℝ)} := by
    ext ω; exact (Nat.cast_pos (α := ℝ)).symm
  rw [hset]
  exact measureReal_pos_of_pos_integral P
    (ae_of_all _ fun ω ↦ Nat.cast_nonneg (Z n ω))
    (by rw [hGW.integral_Z_eq_one hcrit n]; exact zero_lt_one)

/-- In a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$),
$P(Z_n > 0) \ne 0$ for all $n$. -/
theorem IsGaltonWatson.measure_Z_pos_ne_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) (n : ℕ) :
    P {ω | 0 < Z n ω} ≠ 0 := by
  have hset : {ω : Ω | 0 < Z n ω} = {ω : Ω | 0 < (Z n ω : ℝ)} := by
    ext ω; exact (Nat.cast_pos (α := ℝ)).symm
  rw [hset]
  exact measure_pos_ne_zero_of_pos_integral P
    (ae_of_all _ fun ω ↦ Nat.cast_nonneg (Z n ω))
    (by rw [hGW.integral_Z_eq_one hcrit n]; exact zero_lt_one)

/-- For $s \in [0, 1]$, `fun ω ↦ s ^ (Y ω)` is integrable for any a.e.-measurable
$Y : \Omega \to \mathbb{N}$. -/
theorem integrable_pow_nat {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℕ} (hY : AEMeasurable Y P) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Integrable (fun ω ↦ s ^ (Y ω)) P := by
  refine Integrable.of_mem_Icc 0 1 ?_ (ae_of_all _ fun ω ↦ ⟨pow_nonneg hs0 _, pow_le_one₀ hs0 hs1⟩)
  exact (measurable_of_countable (fun k : ℕ ↦ s ^ k)).comp_aemeasurable hY

/-- PGF iteration identity: for any $s \in [0, 1]$ and $n \ge 0$,
$\mathbb{E}[s^{Z_n}] = f^{[n]}(s)$ where $f(t) = \mathbb{E}[t^{Z_1}]$. -/
theorem IsGaltonWatson.integral_pow_Z {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ ω, s ^ (Z n ω) ∂P) = (fun t : ℝ ↦ ∫ ω, t ^ (Z 1 ω) ∂P)^[n] s := by
  obtain ⟨ξ', hξ'_meas, hξ'_indep, hξ'_ident, hZ_ae⟩ := hGW.exists_measurable_array
  set f : ℝ → ℝ := fun t ↦ ∫ ω, t ^ (Z 1 ω) ∂P
  have hf_mem : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → 0 ≤ f t ∧ f t ≤ 1 := by
    intro t ht0 ht1
    refine ⟨integral_nonneg fun ω ↦ pow_nonneg ht0 _, ?_⟩
    calc f t ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_mono (integrable_pow_nat (hGW.aemeasurable_Z 1) ht0 ht1)
            (integrable_const 1) (fun ω ↦ pow_le_one₀ ht0 ht1)
      _ = 1 := by simp
  have hξ'_pgf : ∀ (p : ℕ × ℕ) {t : ℝ}, (∫ ω, t ^ (ξ' p ω) ∂P) = f t := by
    intro p t
    exact ((hξ'_ident p).comp (measurable_of_countable (fun k : ℕ ↦ t ^ k))).integral_eq
  have hrow_pow : ∀ (m k : ℕ) {t : ℝ}, 0 ≤ t → t ≤ 1 →
      (∫ ω, t ^ (∑ i ∈ Finset.range k, ξ' (m, i) ω) ∂P) = (f t) ^ k := by
    intro m k t ht0 ht1
    induction k with
    | zero => simp
    | succ k ihk =>
        have hrow_indep : iIndepFun (fun i ω ↦ ξ' (m, i) ω) P :=
          hξ'_indep.precomp (Prod.mk_right_injective m)
        have hsum_fn : (∑ j ∈ Finset.range k, fun ω ↦ ξ' (m, j) ω) =
            fun ω ↦ ∑ i ∈ Finset.range k, ξ' (m, i) ω := by
          ext ω; simp [Finset.sum_apply]
        have hind_sum : IndepFun (fun ω ↦ ∑ i ∈ Finset.range k, ξ' (m, i) ω) (ξ' (m, k)) P := by
          rw [← hsum_fn]
          exact hrow_indep.indepFun_sum_range_succ (fun i ↦ hξ'_meas (m, i)) k
        have hind_pow : IndepFun
            (fun ω ↦ t ^ (∑ i ∈ Finset.range k, ξ' (m, i) ω))
            (fun ω ↦ t ^ (ξ' (m, k) ω)) P :=
          hind_sum.comp (measurable_of_countable _) (measurable_of_countable _)
        have hprod_eq : (fun ω ↦ t ^ (∑ i ∈ Finset.range (k + 1), ξ' (m, i) ω)) =
            fun ω ↦ t ^ (∑ i ∈ Finset.range k, ξ' (m, i) ω) * t ^ (ξ' (m, k) ω) := by
          ext ω; rw [Finset.sum_range_succ, pow_add]
        rw [hprod_eq, hind_pow.integral_fun_mul_eq_mul_integral
          ((measurable_of_countable _).comp
            (Finset.measurable_sum (Finset.range k) fun i _ ↦ hξ'_meas (m, i))).aestronglyMeasurable
          ((measurable_of_countable _).comp (hξ'_meas (m, k))).aestronglyMeasurable,
          ihk, hξ'_pgf (m, k), pow_succ]
  induction n generalizing s with
  | zero =>
      have h0 : (fun ω ↦ s ^ (Z 0 ω)) =ᵐ[P] fun _ ↦ s := by
        filter_upwards [hZ_ae 0] with ω hω
        simp [hω, gwCanonical]
      rw [integral_congr_ae h0]
      simp
  | succ n ihn =>
      have hfs := hf_mem hs0 hs1
      rw [Function.iterate_succ_apply, ← ihn hfs.1 hfs.2]
      have hZ_congr1 : (fun ω ↦ s ^ (Z (n + 1) ω)) =ᵐ[P] fun ω ↦ s ^ (gwCanonical ξ' (n + 1) ω) :=
        (hZ_ae (n + 1)).mono fun ω hω ↦ congrArg (s ^ ·) hω
      have hZ_congr2 : (fun ω ↦ (f s) ^ (Z n ω)) =ᵐ[P] fun ω ↦ (f s) ^ (gwCanonical ξ' n ω) :=
        (hZ_ae n).mono fun ω hω ↦ congrArg ((f s) ^ ·) hω
      rw [integral_congr_ae hZ_congr1, integral_congr_ae hZ_congr2]
      have hZ'_meas : Measurable (gwCanonical ξ' n) := measurable_gwCanonical hξ'_meas n
      let E : ℕ → Set Ω := fun k ↦ {ω | gwCanonical ξ' n ω = k}
      have hE_meas : ∀ k, MeasurableSet (E k) := fun k ↦ hZ'_meas (measurableSet_singleton k)
      have hE_disj : Pairwise (fun j k ↦ Disjoint (E j) (E k)) := by
        intro j k hjk
        refine Set.disjoint_left.2 fun ω (hj : gwCanonical ξ' n ω = j)
          (hk : gwCanonical ξ' n ω = k) ↦ hjk (hj.symm.trans hk)
      have hE_union : (⋃ k : ℕ, E k) = univ := by ext ω; simp [E]
      have hstep : ∀ k : ℕ,
          (∫ ω in E k, s ^ (gwCanonical ξ' (n + 1) ω) ∂P) =
            ∫ ω in E k, (f s) ^ (gwCanonical ξ' n ω) ∂P := by
        intro k
        have hc1 : ∀ ω ∈ E k, s ^ (gwCanonical ξ' (n + 1) ω) =
            s ^ (∑ i ∈ Finset.range k, ξ' (n, i) ω) := by
          intro ω hω
          have hω' : gwCanonical ξ' n ω = k := hω
          simp [gwCanonical, hω']
        have hc2 : ∀ ω ∈ E k, (f s) ^ (gwCanonical ξ' n ω) = (f s) ^ k :=
          fun ω hω ↦ congrArg ((f s) ^ ·) hω
        rw [setIntegral_congr_fun (hE_meas k) hc1, setIntegral_congr_fun (hE_meas k) hc2,
          setIntegral_const, smul_eq_mul, ← integral_indicator (hE_meas k)]
        have hind_row := indepFun_gwCanonical_row hξ'_meas hξ'_indep n
        have hsum_meas : Measurable (fun r : ℕ → ℕ ↦ s ^ (∑ i ∈ Finset.range k, r i)) :=
          (measurable_of_countable _).comp
            (Finset.measurable_sum (Finset.range k) fun i _ ↦ measurable_pi_apply i)
        have hind_ind : IndepFun
            ((E k).indicator (1 : Ω → ℝ))
            (fun ω ↦ s ^ (∑ i ∈ Finset.range k, ξ' (n, i) ω)) P := by
          have h1 : (E k).indicator (1 : Ω → ℝ) =
              (Set.indicator {k} (fun _ ↦ (1 : ℝ))) ∘ gwCanonical ξ' n := by
            ext ω; by_cases h : gwCanonical ξ' n ω = k <;> simp [E, h]
          rw [h1]
          exact hind_row.comp (measurable_of_countable _) hsum_meas
        have hrew : (E k).indicator (fun ω ↦ s ^ (∑ i ∈ Finset.range k, ξ' (n, i) ω)) =
            fun ω ↦ (E k).indicator (1 : Ω → ℝ) ω *
              s ^ (∑ i ∈ Finset.range k, ξ' (n, i) ω) := by
          ext ω; by_cases hω : ω ∈ E k <;> simp [hω]
        have hpow_meas : Measurable (fun ω ↦ s ^ (∑ i ∈ Finset.range k, ξ' (n, i) ω)) :=
          (measurable_of_countable _).comp
            (Finset.measurable_sum (Finset.range k) fun i _ ↦ hξ'_meas (n, i))
        rw [hrew, hind_ind.integral_fun_mul_eq_mul_integral
          (measurable_const.indicator (hE_meas k)).aestronglyMeasurable
          hpow_meas.aestronglyMeasurable,
          integral_indicator_one (hE_meas k), hrow_pow n k hs0 hs1]
      have hint1 : IntegrableOn (fun ω ↦ s ^ (gwCanonical ξ' (n + 1) ω)) (⋃ k, E k) P := by
        rw [hE_union, integrableOn_univ]
        exact integrable_pow_nat (measurable_gwCanonical hξ'_meas (n + 1)).aemeasurable hs0 hs1
      have hint2 : IntegrableOn (fun ω ↦ (f s) ^ (gwCanonical ξ' n ω)) (⋃ k, E k) P := by
        rw [hE_union, integrableOn_univ]
        exact integrable_pow_nat (measurable_gwCanonical hξ'_meas n).aemeasurable hfs.1 hfs.2
      calc (∫ ω, s ^ (gwCanonical ξ' (n + 1) ω) ∂P)
        _ = ∫ ω in ⋃ k, E k, s ^ (gwCanonical ξ' (n + 1) ω) ∂P := by
            rw [hE_union, Measure.restrict_univ]
        _ = ∑' k, ∫ ω in E k, s ^ (gwCanonical ξ' (n + 1) ω) ∂P :=
            integral_iUnion hE_meas hE_disj hint1
        _ = ∑' k, ∫ ω in E k, (f s) ^ (gwCanonical ξ' n ω) ∂P := by
            simp_rw [hstep]
        _ = ∫ ω in ⋃ k, E k, (f s) ^ (gwCanonical ξ' n ω) ∂P :=
            (integral_iUnion hE_meas hE_disj hint2).symm
        _ = ∫ ω, (f s) ^ (gwCanonical ξ' n ω) ∂P := by
            rw [hE_union, Measure.restrict_univ]

/-- At $s = 0$, $\mathbb{P}(Z_n = 0) = \mathbb{E}[0^{Z_n}] = f^{[n]}(0)$. -/
theorem IsGaltonWatson.measureReal_Z_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z) (n : ℕ) :
    P.real {ω | Z n ω = 0} = (fun t : ℝ ↦ ∫ ω, t ^ (Z 1 ω) ∂P)^[n] 0 := by
  rw [← hGW.integral_pow_Z n le_rfl zero_le_one]
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  have hZ'_meas : MeasurableSet {ω | gwCanonical ξ' n ω = 0} :=
    (measurable_gwCanonical hξ'_meas n) (measurableSet_singleton 0)
  have h1 : P.real {ω | Z n ω = 0} = P.real {ω | gwCanonical ξ' n ω = 0} := by
    refine measureReal_congr ?_
    filter_upwards [hZ_ae n] with ω hω
    simp [hω]
  have h2 : (fun ω ↦ (0 : ℝ) ^ (Z n ω)) =ᵐ[P]
      {ω | gwCanonical ξ' n ω = 0}.indicator 1 := by
    filter_upwards [hZ_ae n] with ω hω
    rw [hω]
    by_cases h0 : gwCanonical ξ' n ω = 0
    · have hmem : ω ∈ {ω | gwCanonical ξ' n ω = 0} := h0
      rw [indicator_of_mem hmem, Pi.one_apply, h0, pow_zero]
    · have hnot : ω ∉ {ω | gwCanonical ξ' n ω = 0} := h0
      rw [indicator_of_notMem hnot, zero_pow h0]
  rw [h1, integral_congr_ae h2, integral_indicator_one hZ'_meas]

/-- Pointwise quadratic lower bound for $(s^k - 1) - k(s - 1)$ on $[0, 1]$. -/
theorem pow_sub_one_sub_mul_ge {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ k : ℕ,
      (1 - s) ^ 2 * ((k : ℝ) - if k = 1 then 1 else 0) ≤
        2 * ((s ^ k - 1) - (k : ℝ) * (s - 1))
  | 0 => by simp
  | 1 => by simp
  | 2 => by
      have h2 : (2 : ℕ) ≠ 1 := by decide
      simp only [h2, ↓reduceIte, Nat.cast_ofNat]
      ring_nf
      linarith
  | m + 3 => by
      have ihm := pow_sub_one_sub_mul_ge hs0 hs1 (m + 2)
      have hm2 : m + 2 ≠ 1 := by omega
      have hm3 : m + 3 ≠ 1 := by omega
      simp only [hm2, hm3, ↓reduceIte, sub_zero] at ihm ⊢
      have hpow : s ^ (m + 2) ≤ s := by
        rw [pow_succ]
        exact mul_le_of_le_one_left hs0 (pow_le_one₀ hs0 hs1)
      have hmul : (1 - s) * s ^ (m + 2) ≤ (1 - s) * s :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
      have hsq : 0 ≤ (1 - s) ^ 2 := sq_nonneg (1 - s)
      have hcast2 : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
      have hcast3 : ((m + 3 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
      have hpow_succ : s ^ (m + 3) = s ^ (m + 2) * s := pow_succ s (m + 2)
      rw [hcast2] at ihm
      rw [hcast3, hpow_succ]
      nlinarith

/-- Telescoping geometric sum identity `(1 - t) * ∑ j ∈ Finset.range k, t ^ j = 1 - t ^ k`. -/
private theorem one_sub_mul_geom_sum (t : ℝ) :
    ∀ k : ℕ, (1 - t) * (∑ j ∈ Finset.range k, t ^ j) = 1 - t ^ k
  | 0 => by simp
  | k + 1 => by
      rw [Finset.sum_range_succ, mul_add, one_sub_mul_geom_sum t k, pow_succ]
      ring

/-- Upper bound `∑ j ∈ Finset.range k, t ^ j ≤ k` for `t ∈ [0, 1]`. -/
private theorem geom_sum_le_nat {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : ℕ) :
    (∑ j ∈ Finset.range k, t ^ j) ≤ (k : ℝ) := by
  calc (∑ j ∈ Finset.range k, t ^ j)
    _ ≤ ∑ _ ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ pow_le_one₀ ht0 ht1
    _ = (k : ℝ) := by simp

/-- Bernoulli inequality `1 - s ^ k ≤ k * (1 - s)` for `s ∈ [0, 1]`. -/
private theorem one_sub_pow_le_mul_one_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (k : ℕ) :
    1 - s ^ k ≤ (k : ℝ) * (1 - s) := by
  rw [← one_sub_mul_geom_sum s k, mul_comm]
  exact mul_le_mul_of_nonneg_right (geom_sum_le_nat hs0 hs1 k) (sub_nonneg.2 hs1)

/-- In a critical or subcritical Galton–Watson process with $\mathbb{E}[Z_1] \le 1$ and
$\mathbb{P}(Z_1 = 1) < 1$, $\lim_{n \to \infty} \mathbb{P}(Z_n > 0) = 0$. -/
theorem IsGaltonWatson.tendsto_measureReal_Z_pos_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ}
    (hGW : IsGaltonWatson P Z)
    (hm : ∫ ω, (Z 1 ω : ℝ) ∂P ≤ 1)
    (hnot_one : P.real {ω | Z 1 ω = 1} < 1) :
    Tendsto (fun n : ℕ ↦ P.real {ω | 0 < Z n ω}) atTop (nhds 0) := by
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  set f : ℝ → ℝ := fun t ↦ ∫ ω, t ^ (Z 1 ω) ∂P
  let q : ℕ → ℝ := fun n ↦ f^[n] 0
  have hf_mono : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ 1 → f s ≤ f t := by
    intro s t hs0 hst ht1
    exact integral_mono (integrable_pow_nat (hGW.aemeasurable_Z 1) hs0 (hst.trans ht1))
      (integrable_pow_nat (hGW.aemeasurable_Z 1) (hs0.trans hst) ht1)
      (fun ω ↦ pow_le_pow_left₀ hs0 hst (Z 1 ω))
  have hf_bounds : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → 0 ≤ f t ∧ f t ≤ 1 := by
    intro t ht0 ht1
    refine ⟨integral_nonneg fun ω ↦ pow_nonneg ht0 _, ?_⟩
    calc f t ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_mono (integrable_pow_nat (hGW.aemeasurable_Z 1) ht0 ht1)
            (integrable_const 1) (fun ω ↦ pow_le_one₀ ht0 ht1)
      _ = 1 := by simp
  have hq_mem : ∀ n : ℕ, 0 ≤ q n ∧ q n ≤ 1 := by
    intro n
    induction n with
    | zero => simp [q]
    | succ n ih =>
        dsimp only [q]
        rw [Function.iterate_succ_apply']
        exact hf_bounds ih.1 ih.2
  have hq_step : ∀ n : ℕ, q n ≤ q (n + 1) := by
    intro n
    induction n with
    | zero => exact (hq_mem 1).1
    | succ n ih =>
        dsimp only [q]
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact hf_mono (hq_mem n).1 ih (hq_mem (n + 1)).2
  have hq_mono : Monotone q := monotone_nat_of_le_succ hq_step
  have hq_bdd : BddAbove (range q) := ⟨1, by rintro _ ⟨n, rfl⟩; exact (hq_mem n).2⟩
  set qstar : ℝ := ⨆ n : ℕ, q n
  have hq_tendsto : Tendsto q atTop (nhds qstar) := tendsto_atTop_ciSup hq_mono hq_bdd
  have hqstar_0 : 0 ≤ qstar := le_ciSup_of_le hq_bdd 0 (by simp [q])
  have hqstar_1 : qstar ≤ 1 := ciSup_le fun n ↦ (hq_mem n).2
  have hfq_tendsto : Tendsto (fun n ↦ f (q n)) atTop (nhds (f qstar)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) ?_
      (integrable_const 1) ?_ ?_
    · exact fun n ↦ (integrable_pow_nat (hGW.aemeasurable_Z 1) (hq_mem n).1 (hq_mem n).2).1
    · intro n
      refine ae_of_all _ fun ω ↦ ?_
      rw [Real.norm_of_nonneg (pow_nonneg (hq_mem n).1 _)]
      exact pow_le_one₀ (hq_mem n).1 (hq_mem n).2
    · refine ae_of_all _ fun ω ↦ ?_
      exact (continuous_pow (Z 1 ω)).tendsto qstar |>.comp hq_tendsto
  have hfq_eq_succ : (fun n ↦ f (q n)) = fun n ↦ q (n + 1) := by
    ext n; exact (Function.iterate_succ_apply' f n 0).symm
  have hq_succ_tendsto : Tendsto (fun n ↦ q (n + 1)) atTop (nhds qstar) :=
    (tendsto_add_atTop_iff_nat 1).2 hq_tendsto
  have hfixed : f qstar = qstar :=
    tendsto_nhds_unique hfq_tendsto (hfq_eq_succ ▸ hq_succ_tendsto)
  have hqstar_eq_one : qstar = 1 := by
    rcases hm.lt_or_eq with hlt | hcrit
    · have h_lhs : Integrable (fun ω ↦ 1 - qstar ^ (Z 1 ω)) P :=
        (integrable_const 1).sub (integrable_pow_nat (hGW.aemeasurable_Z 1) hqstar_0 hqstar_1)
      have h_rhs : Integrable (fun ω ↦ (Z 1 ω : ℝ) * (1 - qstar)) P :=
        hGW.1.mul_const (1 - qstar)
      have hineq := integral_mono h_lhs h_rhs
        (fun ω ↦ one_sub_pow_le_mul_one_sub hqstar_0 hqstar_1 (Z 1 ω))
      rw [integral_sub (integrable_const 1)
          (integrable_pow_nat (hGW.aemeasurable_Z 1) hqstar_0 hqstar_1),
        integral_const, probReal_univ, one_smul, integral_mul_const] at hineq
      change 1 - f qstar ≤ (∫ ω, (Z 1 ω : ℝ) ∂P) * (1 - qstar) at hineq
      rw [hfixed] at hineq
      nlinarith
    · have hZ1_meas : MeasurableSet {ω | gwCanonical ξ' 1 ω = 1} :=
        (measurable_gwCanonical hξ'_meas 1) (measurableSet_singleton 1)
      have hZ1_ind_ae : (fun ω ↦ if Z 1 ω = 1 then (1 : ℝ) else 0) =ᵐ[P]
          {ω | gwCanonical ξ' 1 ω = 1}.indicator 1 := by
        filter_upwards [hZ_ae 1] with ω hω
        rw [hω]
        by_cases h : gwCanonical ξ' 1 ω = 1
        · have hmem : ω ∈ {ω | gwCanonical ξ' 1 ω = 1} := h
          rw [ite_eq_left_iff.2 fun h' ↦ False.elim (h' h), indicator_of_mem hmem, Pi.one_apply]
        · have hnot : ω ∉ {ω | gwCanonical ξ' 1 ω = 1} := h
          rw [ite_eq_right_iff.2 fun h' ↦ False.elim (h h'), indicator_of_notMem hnot]
      have hZ1_ind_int : Integrable (fun ω ↦ if Z 1 ω = 1 then (1 : ℝ) else 0) P :=
        ((integrable_const (1 : ℝ)).indicator hZ1_meas).congr hZ1_ind_ae.symm
      have hZ1_ind_integral : (∫ ω, (if Z 1 ω = 1 then (1 : ℝ) else 0) ∂P) =
          P.real {ω | Z 1 ω = 1} := by
        rw [integral_congr_ae hZ1_ind_ae, integral_indicator_one hZ1_meas]
        refine measureReal_congr ?_
        filter_upwards [hZ_ae 1] with ω hω
        simp [hω]
      have h_lhs_int : Integrable
          (fun ω ↦ (1 - qstar) ^ 2 * ((Z 1 ω : ℝ) - if Z 1 ω = 1 then 1 else 0)) P :=
        (hGW.1.sub hZ1_ind_int).const_mul ((1 - qstar) ^ 2)
      have h_sub1 : Integrable (fun ω ↦ qstar ^ (Z 1 ω) - 1) P :=
        (integrable_pow_nat (hGW.aemeasurable_Z 1) hqstar_0 hqstar_1).sub (integrable_const 1)
      have h_rhs_int : Integrable
          (fun ω ↦ 2 * ((qstar ^ (Z 1 ω) - 1) - (Z 1 ω : ℝ) * (qstar - 1))) P :=
        (h_sub1.sub (hGW.1.mul_const (qstar - 1))).const_mul 2
      have hineq := integral_mono h_lhs_int h_rhs_int
        (fun ω ↦ pow_sub_one_sub_mul_ge hqstar_0 hqstar_1 (Z 1 ω))
      have hlhs_val :
          (∫ ω, (1 - qstar) ^ 2 * ((Z 1 ω : ℝ) - if Z 1 ω = 1 then 1 else 0) ∂P) =
          (1 - qstar) ^ 2 * (1 - P.real {ω | Z 1 ω = 1}) := by
        rw [integral_const_mul, integral_sub hGW.1 hZ1_ind_int, hcrit, hZ1_ind_integral]
      have hrhs_val : (∫ ω, 2 * ((qstar ^ (Z 1 ω) - 1) - (Z 1 ω : ℝ) * (qstar - 1)) ∂P) =
          2 * (f qstar - qstar) := by
        rw [integral_const_mul, integral_sub h_sub1 (hGW.1.mul_const (qstar - 1)),
          integral_sub (integrable_pow_nat (hGW.aemeasurable_Z 1) hqstar_0 hqstar_1)
            (integrable_const 1),
          integral_mul_const, integral_const, probReal_univ, one_smul, hcrit]
        change 2 * (f qstar - 1 - 1 * (qstar - 1)) = 2 * (f qstar - qstar)
        ring
      rw [hlhs_val, hrhs_val, hfixed, sub_self, mul_zero] at hineq
      have hpos : 0 < 1 - P.real {ω | Z 1 ω = 1} := sub_pos.2 hnot_one
      have hsq_nonneg : 0 ≤ (1 - qstar) ^ 2 := sq_nonneg (1 - qstar)
      have hsq_zero : (1 - qstar) ^ 2 = 0 := by nlinarith
      nlinarith [sq_eq_zero_iff.mp hsq_zero]
  have hsurv_eq : (fun n : ℕ ↦ P.real {ω | 0 < Z n ω}) = fun n : ℕ ↦ 1 - q n := by
    ext n
    have hZ'_meas : MeasurableSet {ω | gwCanonical ξ' n ω = 0} :=
      (measurable_gwCanonical hξ'_meas n) (measurableSet_singleton 0)
    have hpos_congr : P.real {ω | 0 < Z n ω} = P.real ({ω | gwCanonical ξ' n ω = 0}ᶜ) := by
      refine measureReal_congr ?_
      filter_upwards [hZ_ae n] with ω hω
      change (0 < Z n ω) = ¬ (gwCanonical ξ' n ω = 0)
      rw [hω]
      exact propext Nat.pos_iff_ne_zero
    have hzero_congr : P.real {ω | Z n ω = 0} = P.real {ω | gwCanonical ξ' n ω = 0} := by
      refine measureReal_congr ?_
      filter_upwards [hZ_ae n] with ω hω
      simp [hω]
    rw [hpos_congr, measureReal_compl hZ'_meas, probReal_univ, ← hzero_congr,
      hGW.measureReal_Z_eq_zero n]
  rw [hsurv_eq]
  have hlim : (0 : ℝ) = 1 - qstar := by linarith
  rw [hlim]
  exact tendsto_const_nhds.sub hq_tendsto

/-- Section 5.3 Galton–Watson extinction dichotomy (`SteinIntro.tex:3003-3004`;
`ISSUE-TYPO-5.3a`): for a Galton–Watson branching process $(Z_n)_{n \ge 0}$, (i) if
$\mathbb{E}[Z_1] \le 1$ and $\mathbb{P}(Z_1 = 1) < 1$ (printed `\IP(Z_1=1<1)` by typo), then the
population almost surely dies out ($\mathbb{P}(\exists n, Z_n = 0) = 1$), whereas (ii) if
$\mathbb{E}[Z_1] > 1$, the probability that the population lives forever is strictly positive
($\mathbb{P}(\forall n, Z_n > 0) > 0$). -/
def Sec5_3_extinction_stmt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ((∫ ω, (Z 1 ω : ℝ) ∂P ≤ 1 → P.real {ω | Z 1 ω = 1} < 1 →
        P {ω | ∃ n : ℕ, Z n ω = 0} = 1) ∧
      (1 < ∫ ω, (Z 1 ω : ℝ) ∂P →
        0 < P {ω | ∀ n : ℕ, 0 < Z n ω}))

theorem sec5_3_extinction : Sec5_3_extinction_stmt := by
  intro Ω _ P _ Z hGW
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array
  have hZ_all : ∀ᵐ ω ∂P, ∀ n : ℕ, Z n ω = gwCanonical ξ' n ω := ae_all_iff.2 hZ_ae
  let E : ℕ → Set Ω := fun n ↦ {ω | gwCanonical ξ' n ω = 0}
  have hE_meas : ∀ n : ℕ, MeasurableSet (E n) :=
    fun n ↦ (measurable_gwCanonical hξ'_meas n) (measurableSet_singleton 0)
  have hE_mono : Monotone E := by
    refine monotone_nat_of_le_succ fun n ω (hω : gwCanonical ξ' n ω = 0) ↦ ?_
    change gwCanonical ξ' (n + 1) ω = 0
    simp [gwCanonical, hω]
  have h_extinct_ae : {ω : Ω | ∃ n : ℕ, Z n ω = 0} =ᵐ[P] ⋃ n : ℕ, E n := by
    filter_upwards [hZ_all] with ω hω
    rw [mem_iUnion]
    exact propext (exists_congr fun n ↦ by
      change (Z n ω = 0) ↔ (gwCanonical ξ' n ω = 0)
      rw [hω n])
  have h_surv_ae : {ω : Ω | ∀ n : ℕ, 0 < Z n ω} =ᵐ[P] (⋃ n : ℕ, E n)ᶜ := by
    filter_upwards [hZ_all] with ω hω
    rw [mem_compl_iff, mem_iUnion, not_exists]
    exact propext (forall_congr' fun n ↦ by
      change (0 < Z n ω) ↔ ¬ (gwCanonical ξ' n ω = 0)
      rw [hω n]
      exact Nat.pos_iff_ne_zero)
  set f : ℝ → ℝ := fun t ↦ ∫ ω, t ^ (Z 1 ω) ∂P
  let q : ℕ → ℝ := fun n ↦ f^[n] 0
  have hPE_eq_q : ∀ n : ℕ, P.real (E n) = q n := by
    intro n
    have hcongr : P.real (E n) = P.real {ω | Z n ω = 0} := by
      refine measureReal_congr ?_
      filter_upwards [hZ_ae n] with ω hω
      simp [E, hω]
    rw [hcongr, hGW.measureReal_Z_eq_zero n]
  have hPE_tendsto : Tendsto (fun n : ℕ ↦ P.real (E n)) atTop (nhds (P.real (⋃ n : ℕ, E n))) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := P) hE_mono
    exact (ENNReal.continuousAt_toReal (measure_ne_top P _)).tendsto.comp h1
  constructor
  · intro hm hnot_one
    have hsurv_zero := hGW.tendsto_measureReal_Z_pos_zero hm hnot_one
    have hq_one : Tendsto q atTop (nhds 1) := by
      have heq : q = fun n : ℕ ↦ 1 - P.real {ω | 0 < Z n ω} := by
        ext n
        have hpos_congr : P.real {ω | 0 < Z n ω} = P.real (E n)ᶜ := by
          refine measureReal_congr ?_
          filter_upwards [hZ_ae n] with ω hω
          change (0 < Z n ω) = ¬ (gwCanonical ξ' n ω = 0)
          rw [hω]
          exact propext Nat.pos_iff_ne_zero
        rw [hpos_congr, measureReal_compl (hE_meas n), probReal_univ, hPE_eq_q n]
        ring
      rw [heq]
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsurv_zero
    have hP_union_real : P.real (⋃ n : ℕ, E n) = 1 :=
      tendsto_nhds_unique hPE_tendsto (by simpa only [hPE_eq_q] using hq_one)
    have hP_union : P (⋃ n : ℕ, E n) = 1 := by
      have hle : P (⋃ n : ℕ, E n) ≤ 1 := prob_le_one
      exact (ENNReal.toReal_eq_one_iff (P (⋃ n : ℕ, E n))).mp hP_union_real
    rw [measure_congr h_extinct_ae, hP_union]
  · intro hm
    let tSeq : ℕ → ℝ := fun N ↦ 1 - 1 / ((N : ℝ) + 2)
    have ht_0 : ∀ N : ℕ, 0 ≤ tSeq N := by
      intro N
      dsimp only [tSeq]
      have hN : (1 : ℝ) ≤ (N : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
      linarith [div_le_one_of_le₀ hN (by positivity)]
    have ht_lt1 : ∀ N : ℕ, tSeq N < 1 := by
      intro N
      dsimp only [tSeq]
      have hpos : 0 < 1 / ((N : ℝ) + 2) := by positivity
      linarith
    have ht_1 : ∀ N : ℕ, tSeq N ≤ 1 := fun N ↦ (ht_lt1 N).le
    have ht_tendsto : Tendsto tSeq atTop (nhds 1) := by
      dsimp only [tSeq]
      have hinv : Tendsto (fun N : ℕ ↦ 1 / ((N : ℝ) + 2)) atTop (nhds 0) := by
        simpa only [one_div, Function.comp_def] using
          tendsto_inv_atTop_zero.comp
            (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    let g : ℝ → ℕ → ℝ := fun t k ↦ ∑ j ∈ Finset.range k, t ^ j
    have hg_meas : ∀ N : ℕ, AEStronglyMeasurable (fun ω ↦ g (tSeq N) (Z 1 ω)) P :=
      fun N ↦ ((measurable_of_countable (g (tSeq N))).comp_aemeasurable
        (hGW.aemeasurable_Z 1)).aestronglyMeasurable
    have hg_tendsto :
        Tendsto (fun N : ℕ ↦ ∫ ω, g (tSeq N) (Z 1 ω) ∂P) atTop
          (nhds (∫ ω, (Z 1 ω : ℝ) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun ω ↦ (Z 1 ω : ℝ))
        hg_meas hGW.1 ?_ ?_
      · intro N
        refine ae_of_all _ fun ω ↦ ?_
        have hnn : 0 ≤ g (tSeq N) (Z 1 ω) :=
          Finset.sum_nonneg fun j _ ↦ pow_nonneg (ht_0 N) j
        rw [Real.norm_of_nonneg hnn]
        exact geom_sum_le_nat (ht_0 N) (ht_1 N) (Z 1 ω)
      · refine ae_of_all _ fun ω ↦ ?_
        have h1 : ((Z 1 ω : ℕ) : ℝ) = ∑ j ∈ Finset.range (Z 1 ω), (1 : ℝ) ^ j := by simp
        rw [h1]
        exact tendsto_finsetSum (Finset.range (Z 1 ω)) fun j _ ↦
          ((continuous_pow j).tendsto 1).comp ht_tendsto
    have h_ev : ∀ᶠ N : ℕ in atTop, 1 < ∫ ω, g (tSeq N) (Z 1 ω) ∂P :=
      (tendsto_order.1 hg_tendsto).1 1 hm
    obtain ⟨N, hN⟩ := h_ev.exists
    set t₀ := tSeq N
    have ht₀_0 : 0 ≤ t₀ := ht_0 N
    have ht₀_lt1 : t₀ < 1 := ht_lt1 N
    have ht₀_1 : t₀ ≤ 1 := ht_1 N
    have hg_int : Integrable (fun ω ↦ g t₀ (Z 1 ω)) P := by
      refine hGW.1.mono' (hg_meas N) (ae_of_all _ fun ω ↦ ?_)
      have hnn : 0 ≤ g t₀ (Z 1 ω) := Finset.sum_nonneg fun j _ ↦ pow_nonneg ht₀_0 j
      rw [Real.norm_of_nonneg hnn]
      exact geom_sum_le_nat ht₀_0 ht₀_1 (Z 1 ω)
    have h_ident : (fun ω ↦ (1 - t₀) * g t₀ (Z 1 ω)) = fun ω ↦ 1 - t₀ ^ (Z 1 ω) := by
      ext ω
      exact one_sub_mul_geom_sum t₀ (Z 1 ω)
    have h_int_eq : (1 - t₀) * (∫ ω, g t₀ (Z 1 ω) ∂P) = 1 - f t₀ := by
      rw [← integral_const_mul, h_ident,
        integral_sub (integrable_const 1) (integrable_pow_nat (hGW.aemeasurable_Z 1) ht₀_0 ht₀_1),
        integral_const, probReal_univ, one_smul]
    have hft₀_le : f t₀ ≤ t₀ := by
      have hmul : 1 - t₀ < (1 - t₀) * ∫ ω, g t₀ (Z 1 ω) ∂P :=
        lt_mul_of_one_lt_right (sub_pos.2 ht₀_lt1) hN
      linarith
    have hf_mono : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ 1 → f s ≤ f t := by
      intro s t hs0 hst ht1
      exact integral_mono (integrable_pow_nat (hGW.aemeasurable_Z 1) hs0 (hst.trans ht1))
        (integrable_pow_nat (hGW.aemeasurable_Z 1) (hs0.trans hst) ht1)
        (fun ω ↦ pow_le_pow_left₀ hs0 hst (Z 1 ω))
    have hq_le_t₀ : ∀ n : ℕ, q n ≤ t₀ := by
      intro n
      induction n with
      | zero => simp [q, ht₀_0]
      | succ n ih =>
          dsimp only [q]
          rw [Function.iterate_succ_apply']
          have hq_nn : 0 ≤ q n := by
            rw [← hPE_eq_q n]
            exact measureReal_nonneg
          exact (hf_mono hq_nn ih ht₀_1).trans hft₀_le
    have hP_union_le : P.real (⋃ n : ℕ, E n) ≤ t₀ :=
      le_of_tendsto hPE_tendsto
        (Eventually.of_forall fun n ↦ by rw [hPE_eq_q n]; exact hq_le_t₀ n)
    have h_surv_real_pos : 0 < P.real {ω | ∀ n : ℕ, 0 < Z n ω} := by
      rw [measureReal_congr h_surv_ae, measureReal_compl (MeasurableSet.iUnion hE_meas),
        probReal_univ]
      linarith
    by_contra hle
    have hzero : P {ω | ∀ n : ℕ, 0 < Z n ω} = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hle)
    simp [Measure.real, hzero] at h_surv_real_pos

end SteinMethod
