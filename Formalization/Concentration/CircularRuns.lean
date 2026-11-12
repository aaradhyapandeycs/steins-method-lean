/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.SizeBias
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Circular Head Runs Size-Bias Concentration (`Formalization.Concentration.CircularRuns`)

Proves **Example 7.6** (`SteinIntro.tex:3878-3884`; `ISSUE-EX7.6`, `ISSUE-7.6`, restructured per
`stmts-review-05F` `F3`) from Section 7.3 of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`), together with a formal refutation of the printed variance formula:

* `circularRuns_sizeBias_concentration` (**Example 7.6, corrected**, `Ex7_6_corrected`,
  `SteinIntro.tex:3878-3884`; `ISSUE-EX7.6`, `ISSUE-7.6`): size-bias coupling, monotonicity,
  bounded increment $|X^s - X| \le 2k - 1$, mean ($k \le n$), corrected variance ($2k - 1 \le n$),
  and two-sided concentration bound ($t \ge 0$) for cyclic $k$-runs of $n$ i.i.d. $\mathrm{Ber}(p)$.
* `Ex7_6_variance_counterexample` (`SteinIntro.tex:3883`; `ISSUE-EX7.6`): at $n = 4$, $k = 2$,
  $p = 1/2$, $\mu = 1$ and $\operatorname{Var}(X) = 5/4$, whereas the printed formula gives $1$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SteinMethod

/-! ### Section 1: Combinatorial Cyclic Runs on Boolean Vectors -/

private def boolVal (b : Bool) : ℝ := if b then 1 else 0

private def bernVecWeight {n : ℕ} (p : ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ j : Fin n, if x j then p else 1 - p

private def cycPerm {n : ℕ} (hn : 1 ≤ n) (i : Fin n) : Fin n ≃ Fin n where
  toFun j := ⟨(i.1 + j.1) % n, Nat.mod_lt _ hn⟩
  invFun j := ⟨(j.1 + (n - i.1)) % n, Nat.mod_lt _ hn⟩
  left_inv j := Fin.ext <| by
    dsimp only; rw [Nat.mod_add_mod, show i.1 + j.1 + (n - i.1) = j.1 + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
  right_inv j := Fin.ext <| by
    dsimp only; rw [Nat.add_mod_mod, show i.1 + (j.1 + (n - i.1)) = j.1 + n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt j.2]

private def cycShift {n : ℕ} (hn : 1 ≤ n) (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun x j := x (cycPerm hn i j)
  invFun x j := x ((cycPerm hn i).symm j)
  left_inv x := funext fun j ↦ by simp
  right_inv x := funext fun j ↦ by simp

private lemma bernVecWeight_cycShift {n : ℕ} (hn : 1 ≤ n) (p : ℝ) (i : Fin n) (x : Fin n → Bool) :
    bernVecWeight p (cycShift hn i x) = bernVecWeight p x :=
  Equiv.prod_comp (cycPerm hn i) (fun j ↦ if x j then p else 1 - p)

private def cycIdx {n : ℕ} (hn : 1 ≤ n) (i : Fin n) (d : ℕ) : Fin n :=
  ⟨(i.1 + d) % n, Nat.mod_lt _ hn⟩

private def cycRunBool {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool) (i : Fin n) : ℝ :=
  ∏ r : Fin k, boolVal (x (cycIdx hn i r.1))

private def cycSumBool {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool) : ℝ :=
  ∑ i : Fin n, cycRunBool hn k x i

private def forceOn {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) (j : Fin n) : Bool :=
  if j ∈ S then true else x j

private def forceBool {n : ℕ} (k : ℕ) (x : Fin n → Bool) (j : Fin n) : Bool :=
  if j.1 < k then true else x j

private lemma cycRunBool_eq_one_or_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool)
    (i : Fin n) :
    cycRunBool hn k x i = if ∀ r : Fin k, x (cycIdx hn i r.1) = true then 1 else 0 := by
  unfold cycRunBool; split_ifs with hall
  · exact Finset.prod_eq_one fun r _ ↦ by simp [boolVal, hall r]
  · push Not at hall; obtain ⟨r₀, hr₀⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ r₀) (by simp [boolVal, hr₀])

private lemma cycRunBool_nonneg {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool) (i : Fin n) :
    0 ≤ cycRunBool hn k x i := by rw [cycRunBool_eq_one_or_zero]; split_ifs <;> norm_num

private lemma cycRunBool_le_one {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool) (i : Fin n) :
    cycRunBool hn k x i ≤ 1 := by rw [cycRunBool_eq_one_or_zero]; split_ifs <;> norm_num

private lemma cycRunBool_cycShift {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (i m : Fin n) (x : Fin n → Bool) :
    cycRunBool hn k (cycShift hn i x) m = cycRunBool hn k x (cycPerm hn i m) := by
  unfold cycRunBool; refine Finset.prod_congr rfl fun r _ ↦ ?_
  have hidx : cycPerm hn i (cycIdx hn m r.1) = cycIdx hn (cycPerm hn i m) r.1 := Fin.ext <| by
    simp only [cycPerm, cycIdx, Equiv.coe_fn_mk]
    rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  change boolVal (x (cycPerm hn i (cycIdx hn m r.1))) = _; rw [hidx]

private lemma cycRunBool_cycShift_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (i : Fin n)
    (x : Fin n → Bool) :
    cycRunBool hn k (cycShift hn i x) ⟨0, hn⟩ = cycRunBool hn k x i := by
  rw [cycRunBool_cycShift, show cycPerm hn i ⟨0, hn⟩ = i from
    Fin.ext (by dsimp [cycPerm]; exact Nat.mod_eq_of_lt i.2)]

private lemma cycSumBool_cycShift {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (i : Fin n) (x : Fin n → Bool) :
    cycSumBool hn k (cycShift hn i x) = cycSumBool hn k x := by
  unfold cycSumBool; simp_rw [cycRunBool_cycShift]
  exact Equiv.sum_comp (cycPerm hn i) (cycRunBool hn k x)

private def winSet {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.image fun r : Fin k ↦ cycIdx hn i r.1

private lemma mem_winSet_zero_iff {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (j : Fin n) :
    j ∈ winSet hn k ⟨0, hn⟩ ↔ j.1 < k := by
  simp only [winSet, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨?_, fun hj ↦ ⟨⟨j.1, hj⟩, Fin.ext ?_⟩⟩
  · rintro ⟨r, rfl⟩
    dsimp [cycIdx]; rw [Nat.zero_add]; exact (Nat.mod_le r.1 n).trans_lt r.2
  · dsimp [cycIdx]; rw [Nat.zero_add]; exact Nat.mod_eq_of_lt j.2

private lemma winSet_zero_eq_filter {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    winSet hn k ⟨0, hn⟩ = Finset.univ.filter fun j : Fin n ↦ j.1 < k := by
  ext j; simp [mem_winSet_zero_iff hn k j]

private lemma forceOn_winSet_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool) :
    forceOn (winSet hn k ⟨0, hn⟩) x = forceBool k x := by
  ext j; simp [forceOn, forceBool, mem_winSet_zero_iff hn k j]

private lemma prod_boolVal_eq_one_or_zero {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    (∏ j ∈ S, boolVal (x j)) = if ∀ j ∈ S, x j = true then 1 else 0 := by
  split_ifs with hall
  · exact Finset.prod_eq_one fun j hj ↦ by simp [boolVal, hall j hj]
  · push Not at hall; obtain ⟨j₀, hj₀, hxj₀⟩ := hall
    exact Finset.prod_eq_zero hj₀ (by simp [boolVal, hxj₀])

private lemma cycRunBool_eq_prod_winSet {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool)
    (i : Fin n) :
    cycRunBool hn k x i = ∏ j ∈ winSet hn k i, boolVal (x j) := by
  rw [cycRunBool_eq_one_or_zero, prod_boolVal_eq_one_or_zero]
  have hiff : (∀ r : Fin k, x (cycIdx hn i r.1) = true) ↔ (∀ j ∈ winSet hn k i, x j = true) := by
    simp [winSet]
  simp [hiff]

private lemma cycRunBool_mul_eq_prod_union {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool)
    (i d : Fin n) :
    cycRunBool hn k x i * cycRunBool hn k x d =
      ∏ j ∈ winSet hn k i ∪ winSet hn k d, boolVal (x j) := by
  have hite : ∀ (A B : Prop) [Decidable A] [Decidable B],
      (if A then (1 : ℝ) else 0) * (if B then 1 else 0) = if A ∧ B then 1 else 0 := by
    intro A B _ _; by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]
  rw [cycRunBool_eq_prod_winSet, cycRunBool_eq_prod_winSet,
    prod_boolVal_eq_one_or_zero, prod_boolVal_eq_one_or_zero, prod_boolVal_eq_one_or_zero, hite]
  have hiff : (∀ j ∈ winSet hn k i ∪ winSet hn k d, x j = true) ↔
      (∀ j ∈ winSet hn k i, x j = true) ∧ (∀ j ∈ winSet hn k d, x j = true) :=
    ⟨fun h ↦ ⟨fun j hj ↦ h j (Finset.mem_union_left _ hj),
        fun j hj ↦ h j (Finset.mem_union_right _ hj)⟩,
      fun ⟨h1, h2⟩ j hj ↦ (Finset.mem_union.mp hj).elim (h1 j) (h2 j)⟩
  simp only [hiff]

private lemma card_filter_lt {n m : ℕ} (hmn : m ≤ n) :
    (Finset.univ.filter fun j : Fin n ↦ j.1 < m).card = m := by
  let g : Fin m → Fin n := fun r ↦ ⟨r.1, by omega⟩
  have hinj : Function.Injective g := fun a b hab ↦ Fin.ext (congr_arg (Fin.val : Fin n → ℕ) hab)
  have himg : Finset.univ.image g = Finset.univ.filter (fun j : Fin n ↦ j.1 < m) := by
    ext j; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, g]
    exact ⟨fun ⟨r, hr⟩ ↦ hr ▸ r.2, fun hj ↦ ⟨⟨j.1, hj⟩, Fin.ext rfl⟩⟩
  rw [← himg, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-! ### Section 2: Monotonicity and Bounded Increment `|Xs - X| ≤ 2k - 1` -/

private lemma cycRunBool_mono_force {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool) (i : Fin n) :
    cycRunBool hn k x i ≤ cycRunBool hn k (forceBool k x) i := by
  rw [cycRunBool_eq_one_or_zero, cycRunBool_eq_one_or_zero]
  split_ifs with h1 h2
  · exact le_rfl
  · exact False.elim (h2 fun r ↦ by dsimp [forceBool]; split_ifs; exacts [rfl, h1 r])
  · norm_num
  · exact le_rfl

private lemma cycSumBool_mono_force {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (x : Fin n → Bool) :
    cycSumBool hn k x ≤ cycSumBool hn k (forceBool k x) :=
  Finset.sum_le_sum fun i _ ↦ cycRunBool_mono_force hn k x i

private lemma cycSumBool_force_sub_le {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (x : Fin n → Bool) :
    cycSumBool hn k (forceBool k x) - cycSumBool hn k x ≤ 2 * (k : ℝ) - 1 := by
  by_cases hsmall : n < 2 * k
  · have hsum_nn : 0 ≤ cycSumBool hn k x :=
      Finset.sum_nonneg fun i _ ↦ cycRunBool_nonneg hn k x i
    have hsum_le : cycSumBool hn k (forceBool k x) ≤ (n : ℝ) :=
      (Finset.sum_le_sum fun i _ ↦ cycRunBool_le_one hn k (forceBool k x) i).trans_eq (by simp)
    have hn_le : (n : ℝ) ≤ 2 * (k : ℝ) - 1 := by
      exact_mod_cast (by omega : (n : ℤ) ≤ 2 * (k : ℤ) - 1)
    linarith
  · have hn2k : 2 * k ≤ n := Nat.le_of_not_lt hsmall
    let S₁ : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ i.1 < k
    let S₂ : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ n < i.1 + k
    have hzero_outside : ∀ i ∉ S₁ ∪ S₂,
        cycRunBool hn k (forceBool k x) i - cycRunBool hn k x i = 0 := by
      intro i hi
      simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_lt] at hi
      refine sub_eq_zero.mpr (Finset.prod_congr rfl fun r _ ↦ ?_)
      have hge_k : ¬ ((cycIdx hn i r.1).1 < k) := by
        dsimp [cycIdx]; rw [Nat.mod_eq_of_lt (by omega : i.1 + r.1 < n)]; omega
      simp [forceBool, hge_k]
    have hcard₁ : S₁.card = k := card_filter_lt (by omega)
    have hcard₂ : S₂.card ≤ k - 1 := by
      let f : Fin n → ℕ := fun i ↦ i.1 + k - (n + 1)
      have hinj : ∀ a ∈ S₂, ∀ b ∈ S₂, f a = f b → a = b := fun a ha b hb hfab ↦ by
        have ha' := (Finset.mem_filter.mp ha).2; have hb' := (Finset.mem_filter.mp hb).2
        dsimp [f] at hfab; exact Fin.ext (by omega)
      have himg : S₂.image f ⊆ Finset.range (k - 1) := fun m hm ↦ by
        rcases Finset.mem_image.mp hm with ⟨i, hi, rfl⟩
        have hi' := (Finset.mem_filter.mp hi).2
        exact Finset.mem_range.mpr (by dsimp [f]; omega)
      calc S₂.card = (S₂.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range (k - 1)).card := Finset.card_le_card himg
        _ = k - 1 := Finset.card_range (k - 1)
    have hcard_u : (S₁ ∪ S₂).card ≤ 2 * k - 1 := by
      have hle := Finset.card_union_le S₁ S₂; omega
    have hdiff_eq : cycSumBool hn k (forceBool k x) - cycSumBool hn k x =
        ∑ i ∈ S₁ ∪ S₂, (cycRunBool hn k (forceBool k x) i - cycRunBool hn k x i) := by
      unfold cycSumBool; rw [← Finset.sum_sub_distrib]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ hzero_outside i hi).symm
    have hterm_le : ∀ i ∈ S₁ ∪ S₂,
        cycRunBool hn k (forceBool k x) i - cycRunBool hn k x i ≤ 1 := fun i _ ↦ by
      linarith [cycRunBool_le_one hn k (forceBool k x) i, cycRunBool_nonneg hn k x i]
    calc cycSumBool hn k (forceBool k x) - cycSumBool hn k x
        = ∑ i ∈ S₁ ∪ S₂, (cycRunBool hn k (forceBool k x) i - cycRunBool hn k x i) := hdiff_eq
      _ ≤ ∑ _i ∈ S₁ ∪ S₂, (1 : ℝ) := Finset.sum_le_sum hterm_le
      _ = ((S₁ ∪ S₂).card : ℝ) := by simp
      _ ≤ ((2 * k - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard_u
      _ = 2 * (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_mul]; norm_num

/-! ### Section 3: Product-Weight Summation Identities on `Fin n → Bool` -/

private lemma sum_bernVecWeight_single {n : ℕ} (p : ℝ) (a : Fin n) (h : (Fin n → Bool) → ℝ) :
    (∑ x : Fin n → Bool, bernVecWeight p x * boolVal (x a) * h x) =
      p * ∑ x : Fin n → Bool, bernVecWeight p x * h (Function.update x a true) := by
  let e := (Equiv.funSplitAt a Bool).symm
  have hwt : ∀ (b : Bool) (y : {j : Fin n // j ≠ a} → Bool),
      bernVecWeight p (e (b, y)) =
        (if b then p else 1 - p) * ∏ j : {j : Fin n // j ≠ a}, if y j then p else 1 - p := by
    intro b y; unfold bernVecWeight
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ a, show e (b, y) a = b by simp [e]]
    exact congrArg _ (Fintype.prod_congr _ _ fun j ↦ by simp [e, j.2])
  have hupd : ∀ (b : Bool) (y : {j : Fin n // j ≠ a} → Bool),
      Function.update (e (b, y)) a true = e (true, y) := fun b y ↦ by
    ext j; by_cases hja : j = a
    · subst hja; simp [e]
    · simp [e, hja]
  rw [← e.sum_comp, ← e.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_bool]
  have he_true : ∀ y, e (true, y) a = true := fun y ↦ by simp [e]
  have he_false : ∀ y, e (false, y) a = false := fun y ↦ by simp [e]
  simp_rw [he_true, he_false, hupd, hwt]
  have hb1 : boolVal true = 1 := rfl
  have hb0 : boolVal false = 0 := rfl
  simp_rw [hb1, hb0, mul_one, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simp only [↓reduceIte, Bool.false_eq_true]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ ↦ by ring

private lemma sum_bernVecWeight_prod_boolVal {n : ℕ} (p : ℝ) (S : Finset (Fin n))
    (g : (Fin n → Bool) → ℝ) :
    (∑ x : Fin n → Bool, bernVecWeight p x * (∏ j ∈ S, boolVal (x j)) * g x) =
      p ^ S.card * ∑ x : Fin n → Bool, bernVecWeight p x * g (forceOn S x) := by
  induction S using Finset.induction generalizing g with
  | empty =>
    have hf0 : ∀ x : Fin n → Bool, forceOn ∅ x = x := fun x ↦ by ext j; simp [forceOn]
    simp [hf0]
  | insert a S ha ih =>
    simp_rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hassoc : ∀ x : Fin n → Bool,
        bernVecWeight p x * (boolVal (x a) * ∏ j ∈ S, boolVal (x j)) * g x =
          bernVecWeight p x * boolVal (x a) * ((∏ j ∈ S, boolVal (x j)) * g x) := fun _ ↦ by ring
    simp_rw [hassoc]; rw [sum_bernVecWeight_single p a]
    have hprod_upd : ∀ x : Fin n → Bool,
        (∏ j ∈ S, boolVal (Function.update x a true j)) = ∏ j ∈ S, boolVal (x j) :=
      fun x ↦ Finset.prod_congr rfl fun j hj ↦ by simp [show j ≠ a from fun h ↦ ha (h ▸ hj)]
    have hforce_upd : ∀ x : Fin n → Bool,
        Function.update (forceOn S x) a true = forceOn (insert a S) x := fun x ↦ by
      ext j; by_cases hja : j = a
      · subst hja; simp [forceOn]
      · simp [forceOn, hja]
    have hinner : (∑ x : Fin n → Bool, bernVecWeight p x *
          ((∏ j ∈ S, boolVal (Function.update x a true j)) * g (Function.update x a true))) =
        ∑ x : Fin n → Bool,
          bernVecWeight p x * (∏ j ∈ S, boolVal (x j)) * g (Function.update x a true) :=
      Finset.sum_congr rfl fun x _ ↦ by rw [hprod_upd x]; ring
    rw [hinner, ih (fun x ↦ g (Function.update x a true))]
    simp_rw [hforce_upd]; rw [pow_succ']; ring

private lemma sum_bernVecWeight_eq_one {n : ℕ} (p : ℝ) :
    (∑ x : Fin n → Bool, bernVecWeight p x) = 1 := by
  have huniv : (Finset.univ : Finset (Fin n → Bool)) =
      Fintype.piFinset fun _ : Fin n ↦ (Finset.univ : Finset Bool) := by ext; simp
  unfold bernVecWeight
  rw [huniv, ← Finset.sum_pow' Finset.univ (fun b : Bool ↦ if b then p else 1 - p) n,
    Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]; ring

private lemma sum_bernVecWeight_prod_boolVal_const {n : ℕ} (p : ℝ) (S : Finset (Fin n)) :
    (∑ x : Fin n → Bool, bernVecWeight p x * ∏ j ∈ S, boolVal (x j)) = p ^ S.card := by
  have h := sum_bernVecWeight_prod_boolVal p S (fun _ ↦ 1)
  simp only [mul_one, sum_bernVecWeight_eq_one] at h; exact h

private lemma sum_cycSumBool_mul_comp {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (p : ℝ) (f : ℝ → ℝ) :
    (∑ x : Fin n → Bool, bernVecWeight p x * (cycSumBool hn k x * f (cycSumBool hn k x))) =
      ((n : ℝ) * p ^ (winSet hn k ⟨0, hn⟩).card) *
        ∑ x : Fin n → Bool, bernVecWeight p x * f (cycSumBool hn k (forceBool k x)) := by
  have hexpand : ∀ x : Fin n → Bool,
      bernVecWeight p x * (cycSumBool hn k x * f (cycSumBool hn k x)) =
        ∑ i : Fin n, bernVecWeight p x * cycRunBool hn k x i * f (cycSumBool hn k x) := fun x ↦ by
    unfold cycSumBool; rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp_rw [hexpand]; rw [Finset.sum_comm]
  have hshift : ∀ i : Fin n,
      (∑ x : Fin n → Bool, bernVecWeight p x * cycRunBool hn k x i * f (cycSumBool hn k x)) =
        ∑ x : Fin n → Bool,
          bernVecWeight p x * cycRunBool hn k x ⟨0, hn⟩ * f (cycSumBool hn k x) := fun i ↦ by
    symm; rw [← (cycShift hn i).sum_comp]
    exact Finset.sum_congr rfl fun x _ ↦ by
      rw [bernVecWeight_cycShift, cycRunBool_cycShift_zero, cycSumBool_cycShift]
  simp_rw [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    cycRunBool_eq_prod_winSet hn k _ ⟨0, hn⟩]
  rw [sum_bernVecWeight_prod_boolVal p (winSet hn k ⟨0, hn⟩) (fun x ↦ f (cycSumBool hn k x))]
  simp_rw [forceOn_winSet_zero hn k]; ring

private lemma sum_cycSumBool_mean {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (p : ℝ) :
    (∑ x : Fin n → Bool, bernVecWeight p x * cycSumBool hn k x) =
      (n : ℝ) * p ^ (winSet hn k ⟨0, hn⟩).card := by
  have h := sum_cycSumBool_mul_comp hn k p (fun _ ↦ 1)
  simp only [mul_one, sum_bernVecWeight_eq_one] at h; exact h

/-! ### Section 4: Window Cardinalities & Exact Second Moment (`2k - 1 ≤ n`) -/

private lemma card_winSet {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n) (d : Fin n) :
    (winSet hn k d).card = k := by
  unfold winSet
  have hinj : Function.Injective (fun r : Fin k ↦ cycIdx hn d r.1) := by
    intro a b hab
    have hp : cycPerm hn d ⟨a.1, by omega⟩ = cycPerm hn d ⟨b.1, by omega⟩ := hab
    have heq : (⟨a.1, by omega⟩ : Fin n) = ⟨b.1, by omega⟩ := (cycPerm hn d).injective hp
    exact Fin.ext (congr_arg (Fin.val : Fin n → ℕ) heq)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

private lemma card_union_winSet_lag {n k : ℕ} (hn : 1 ≤ n) (hnk : 2 * k - 1 ≤ n)
    {d : Fin n} (hd1 : 1 ≤ d.1) (hdk : d.1 < k) :
    (winSet hn k ⟨0, hn⟩ ∪ winSet hn k d).card = d.1 + k := by
  have hunion : winSet hn k ⟨0, hn⟩ ∪ winSet hn k d =
      Finset.univ.filter fun m : Fin n ↦ m.1 < d.1 + k := by
    ext m
    rw [Finset.mem_union, mem_winSet_zero_iff hn k m]
    simp only [winSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    refine ⟨?_, fun hlt ↦ ?_⟩
    · rintro (hm0 | ⟨r, rfl⟩)
      · omega
      · have := r.2; dsimp [cycIdx]; exact (Nat.mod_le _ _).trans_lt (by omega)
    · by_cases hmk : m.1 < k
      · exact Or.inl hmk
      · refine Or.inr ⟨⟨m.1 - d.1, by omega⟩, Fin.ext ?_⟩
        dsimp [cycIdx]; rw [show d.1 + (m.1 - d.1) = m.1 by omega, Nat.mod_eq_of_lt m.2]
  rw [hunion, card_filter_lt (by omega)]

private lemma card_union_winSet_disjoint {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n)
    {d : Fin n} (hdk : k ≤ d.1) (hdn : d.1 + k ≤ n) :
    (winSet hn k ⟨0, hn⟩ ∪ winSet hn k d).card = 2 * k := by
  have hdisj : Disjoint (winSet hn k ⟨0, hn⟩) (winSet hn k d) := by
    rw [Finset.disjoint_left]; intro m hm0 hmd
    have hm_lt : m.1 < k := (mem_winSet_zero_iff hn k m).mp hm0
    rcases Finset.mem_image.mp hmd with ⟨r, -, rfl⟩
    dsimp [cycIdx] at hm_lt; rw [Nat.mod_eq_of_lt (by omega : d.1 + r.1 < n)] at hm_lt; omega
  rw [Finset.card_union_of_disjoint hdisj, winSet_zero_eq_filter, card_filter_lt hkn,
    card_winSet hn hkn d]; omega

private lemma sum_cycSumBool_sq_sub {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hnk : 2 * k - 1 ≤ n)
    (p : ℝ) :
    let μ : ℝ := (n : ℝ) * p ^ k
    (∑ x : Fin n → Bool, bernVecWeight p x * cycSumBool hn k x ^ 2) - μ ^ 2 =
      μ * (1 - p ^ k + 2 * ∑ r ∈ Finset.Ico 1 k, (p ^ r - p ^ k)) := by
  intro μ
  have hkn : k ≤ n := by omega
  let c : Fin n → ℝ := fun d ↦
    (∑ x : Fin n → Bool, bernVecWeight p x * (cycRunBool hn k x ⟨0, hn⟩ * cycRunBool hn k x d)) -
      p ^ (2 * k)
  have hc_eval : ∀ d : Fin n,
      ∑ x : Fin n → Bool, bernVecWeight p x * (cycRunBool hn k x ⟨0, hn⟩ * cycRunBool hn k x d) =
        p ^ (winSet hn k ⟨0, hn⟩ ∪ winSet hn k d).card := fun d ↦ by
    simp_rw [cycRunBool_mul_eq_prod_union hn k _ ⟨0, hn⟩ d]
    exact sum_bernVecWeight_prod_boolVal_const p _
  have hsq_sum : (∑ x : Fin n → Bool, bernVecWeight p x * cycSumBool hn k x ^ 2) =
      (n : ℝ) * ∑ d : Fin n, ∑ x : Fin n → Bool,
        bernVecWeight p x * (cycRunBool hn k x ⟨0, hn⟩ * cycRunBool hn k x d) := by
    have hpt : ∀ x : Fin n → Bool, bernVecWeight p x * cycSumBool hn k x ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          bernVecWeight p x * (cycRunBool hn k x i * cycRunBool hn k x j) := fun x ↦ by
      unfold cycSumBool; rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.mul_sum _ _ _
    simp_rw [hpt]; rw [Finset.sum_comm]
    have hrow : ∀ i : Fin n, (∑ x : Fin n → Bool, ∑ j : Fin n,
          bernVecWeight p x * (cycRunBool hn k x i * cycRunBool hn k x j)) =
        ∑ d : Fin n, ∑ x : Fin n → Bool,
          bernVecWeight p x * (cycRunBool hn k x ⟨0, hn⟩ * cycRunBool hn k x d) := fun i ↦ by
      rw [Finset.sum_comm, ← (cycPerm hn i).sum_comp]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      symm; rw [← (cycShift hn i).sum_comp]
      exact Finset.sum_congr rfl fun x _ ↦ by
        rw [bernVecWeight_cycShift, cycRunBool_cycShift_zero, cycRunBool_cycShift]
    simp_rw [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hvar_eq : (∑ x : Fin n → Bool, bernVecWeight p x * cycSumBool hn k x ^ 2) - μ ^ 2 =
      (n : ℝ) * ∑ d : Fin n, c d := by
    rw [hsq_sum]; dsimp [c, μ]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, pow_mul p 2 k]; ring
  rw [hvar_eq]
  have hc0 : c ⟨0, hn⟩ = p ^ k * (1 - p ^ k) := by
    dsimp [c]; rw [hc_eval, Finset.union_idempotent, winSet_zero_eq_filter, card_filter_lt hkn,
      pow_mul']; ring
  have hc_pos : ∀ (r : ℕ) (hr1 : 1 ≤ r) (hrk : r < k),
      c ⟨r, by omega⟩ = p ^ k * (p ^ r - p ^ k) := fun r hr1 hrk ↦ by
    dsimp [c]; rw [hc_eval, card_union_winSet_lag hn hnk hr1 hrk, pow_add, pow_mul']; ring
  have hc_mid : ∀ d : Fin n, k ≤ d.1 → d.1 + k ≤ n → c d = 0 := fun d hdk hdn ↦ by
    dsimp [c]; rw [hc_eval, card_union_winSet_disjoint hn hkn hdk hdn, sub_self]
  have hc_neg : ∀ (r : ℕ) (hr1 : 1 ≤ r) (hrk : r < k),
      c ⟨n - r, by omega⟩ = c ⟨r, by omega⟩ := fun r hr1 hrk ↦ by
    dsimp [c]; congr 1
    let d : Fin n := ⟨n - r, by omega⟩
    let r' : Fin n := ⟨r, by omega⟩
    have hdr' : cycPerm hn d r' = ⟨0, hn⟩ := Fin.ext <| by
      dsimp [cycPerm, d, r']; rw [show n - r + r = n by omega, Nat.mod_self]
    symm; rw [← (cycShift hn d).sum_comp]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [bernVecWeight_cycShift, cycRunBool_cycShift_zero, cycRunBool_cycShift, hdr']; ring
  let A₀ : Finset (Fin n) := {⟨0, hn⟩}
  let A₁ : Finset (Fin n) := (Finset.Ico 1 k).attach.image fun r ↦
    ⟨r.1, by have := Finset.mem_Ico.mp r.2; omega⟩
  let A₂ : Finset (Fin n) := (Finset.Ico 1 k).attach.image fun r ↦
    ⟨n - r.1, by have := Finset.mem_Ico.mp r.2; omega⟩
  have hdisj₀₁ : Disjoint A₀ A₁ := by
    rw [Finset.disjoint_singleton_left]
    simp only [A₁, Finset.mem_image, Finset.mem_attach, true_and, not_exists]
    intro r hr
    have := (Finset.mem_Ico.mp r.2).1; have hv : r.1 = 0 := congr_arg Fin.val hr; omega
  have hdisj₀₂ : Disjoint A₀ A₂ := by
    rw [Finset.disjoint_singleton_left]
    simp only [A₂, Finset.mem_image, Finset.mem_attach, true_and, not_exists]
    intro r hr
    have := (Finset.mem_Ico.mp r.2).2; have hv : n - r.1 = 0 := congr_arg Fin.val hr; omega
  have hdisj₁₂ : Disjoint A₁ A₂ := by
    rw [Finset.disjoint_left]; intro d hd₁ hd₂
    rcases Finset.mem_image.mp hd₁ with ⟨r₁, -, hr₁⟩
    rcases Finset.mem_image.mp hd₂ with ⟨r₂, -, hr₂⟩
    have := (Finset.mem_Ico.mp r₁.2).2; have := (Finset.mem_Ico.mp r₂.2).2
    have hv : r₁.1 = n - r₂.1 := congr_arg Fin.val (hr₁.trans hr₂.symm); omega
  have houtside : ∀ d ∉ (A₀ ∪ A₁) ∪ A₂, c d = 0 := by
    intro d hd; simp only [Finset.mem_union, not_or] at hd
    rcases hd with ⟨⟨hd₀, hd₁⟩, hd₂⟩
    have hne0 : d.1 ≠ 0 := fun h0 ↦ hd₀ (Finset.mem_singleton.mpr (Fin.ext h0))
    have hgek : k ≤ d.1 := by
      by_contra hlt
      exact hd₁ (Finset.mem_image.mpr
        ⟨⟨d.1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩, Finset.mem_attach _ _, Fin.ext rfl⟩)
    have hlen : d.1 + k ≤ n := by
      by_contra hgt
      exact hd₂ (Finset.mem_image.mpr
        ⟨⟨n - d.1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩, Finset.mem_attach _ _,
          Fin.ext (by dsimp only; omega)⟩)
    exact hc_mid d hgek hlen
  have hsum_A₁ : ∑ d ∈ A₁, c d = ∑ r ∈ Finset.Ico 1 k, p ^ k * (p ^ r - p ^ k) := by
    dsimp [A₁]; rw [Finset.sum_image]
    · rw [← Finset.sum_attach (Finset.Ico 1 k)]
      exact Finset.sum_congr rfl fun r _ ↦
        hc_pos r.1 (Finset.mem_Ico.mp r.2).1 (Finset.mem_Ico.mp r.2).2
    · exact fun _ _ _ _ hab ↦ Subtype.ext (congr_arg Fin.val hab)
  have hsum_A₂ : ∑ d ∈ A₂, c d = ∑ r ∈ Finset.Ico 1 k, p ^ k * (p ^ r - p ^ k) := by
    dsimp [A₂]; rw [Finset.sum_image]
    · rw [← Finset.sum_attach (Finset.Ico 1 k)]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [hc_neg r.1 (Finset.mem_Ico.mp r.2).1 (Finset.mem_Ico.mp r.2).2]
      exact hc_pos r.1 (Finset.mem_Ico.mp r.2).1 (Finset.mem_Ico.mp r.2).2
    · intro a _ b _ hab
      have := (Finset.mem_Ico.mp a.2).2; have := (Finset.mem_Ico.mp b.2).2
      have hv := congr_arg Fin.val hab; dsimp only at hv; exact Subtype.ext (by omega)
  have hsum_all : ∑ d : Fin n, c d = c ⟨0, hn⟩ + ∑ d ∈ A₁, c d + ∑ d ∈ A₂, c d := by
    rw [← Finset.sum_subset (Finset.subset_univ ((A₀ ∪ A₁) ∪ A₂)) fun d _ hd ↦ houtside d hd,
      Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdisj₀₂, hdisj₁₂⟩),
      Finset.sum_union hdisj₀₁, Finset.sum_singleton]
  rw [hsum_all, hc0, hsum_A₁, hsum_A₂, ← Finset.mul_sum]; dsimp [μ]; ring

/-! ### Section 5: Measure-Theoretic Bridge for I.I.D. Bernoulli Coordinates -/

private noncomputable def isOneBool (r : ℝ) : Bool := if r ∈ ({1} : Set ℝ) then true else false

private lemma measurable_isOneBool : Measurable isOneBool :=
  Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const

private lemma boolVal_isOneBool_of_zero_or_one {r : ℝ} (hr : r = 0 ∨ r = 1) :
    boolVal (isOneBool r) = r := by rcases hr with rfl | rfl <;> simp [isOneBool, boolVal]

private lemma map_isOneBool_singleton_real
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {p : ℝ} {Y : Fin n → Ω → ℝ} (hY_meas : ∀ i : Fin n, Measurable (Y i))
    (hIndep : ProbabilityTheory.iIndepFun Y P) (hProb : ∀ i : Fin n, P.real {ω | Y i ω = 1} = p)
    (x : Fin n → Bool) :
    (P.map (fun ω (j : Fin n) ↦ isOneBool (Y j ω))).real {x} = bernVecWeight p x := by
  let B : Ω → Fin n → Bool := fun ω j ↦ isOneBool (Y j ω)
  have hB_meas : Measurable B :=
    measurable_pi_iff.mpr fun j ↦ measurable_isOneBool.comp (hY_meas j)
  let sets : Fin n → Set ℝ := fun j ↦ if x j then {1} else {1}ᶜ
  have hsets : ∀ j ∈ (Finset.univ : Finset (Fin n)), MeasurableSet (sets j) := fun j _ ↦ by
    dsimp [sets]; split_ifs; exacts [measurableSet_singleton 1, (measurableSet_singleton 1).compl]
  have hpre : B ⁻¹' {x} = ⋂ j ∈ (Finset.univ : Finset (Fin n)), Y j ⁻¹' sets j := by
    ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_iInter,
      Finset.mem_univ, forall_true_left, B, isOneBool, sets]
    exact forall_congr' fun j ↦ by cases x j <;> simp
  have hind := hIndep.measure_inter_preimage_eq_mul Finset.univ hsets
  rw [map_measureReal_apply_of_aemeasurable hB_meas.aemeasurable (measurableSet_singleton x),
    hpre, measureReal_def, hind, ENNReal.toReal_prod]
  unfold bernVecWeight; refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← measureReal_def]; dsimp [sets]
  cases hxj : x j
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hcompl : Y j ⁻¹' ({1} : Set ℝ)ᶜ = (Y j ⁻¹' ({1} : Set ℝ))ᶜ := rfl
    rw [hcompl, probReal_compl_eq_one_sub (hY_meas j (measurableSet_singleton 1))]
    congr 1; exact hProb j
  · simp only [↓reduceIte]; exact hProb j

private lemma integral_comp_isOneBool
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {p : ℝ} {Y : Fin n → Ω → ℝ} (hY_meas : ∀ i : Fin n, Measurable (Y i))
    (hIndep : ProbabilityTheory.iIndepFun Y P) (hProb : ∀ i : Fin n, P.real {ω | Y i ω = 1} = p)
    (G : (Fin n → Bool) → ℝ) :
    ∫ ω, G (fun j ↦ isOneBool (Y j ω)) ∂P =
      ∑ x : Fin n → Bool, bernVecWeight p x * G x := by
  let B : Ω → Fin n → Bool := fun ω j ↦ isOneBool (Y j ω)
  have hB_meas : Measurable B :=
    measurable_pi_iff.mpr fun j ↦ measurable_isOneBool.comp (hY_meas j)
  have _ : IsProbabilityMeasure (P.map B) :=
    ⟨by rw [Measure.map_apply hB_meas .univ, Set.preimage_univ, measure_univ]⟩
  rw [← integral_map hB_meas.aemeasurable Measurable.of_discrete.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [smul_eq_mul, map_isOneBool_singleton_real P hY_meas hIndep hProb x]

/-! ### Section 6: Example 7.6 (Corrected) & Variance Counterexample -/

/-- **Example 7.6, corrected** (`Ex7_6_corrected`, `SteinIntro.tex:3878-3884`; `ISSUE-EX7.6`,
`ISSUE-7.6`, `stmts-review-05F` `F3`): size-bias coupling, monotonicity, bounded increment
$|X^s - X| \le 2k - 1$, mean ($k \le n$), corrected variance ($2k - 1 \le n$), and two-sided
concentration ($t \ge 0$) for cyclic $k$-runs of $n$ i.i.d. $\mathrm{Bernoulli}(p)$ variables. -/
theorem circularRuns_sizeBias_concentration
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) {p : ℝ} {Y : Fin n → Ω → ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hY_meas : ∀ i : Fin n, Measurable (Y i))
    (hIndep : ProbabilityTheory.iIndepFun Y P)
    (hY01 : ∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hProb : ∀ i : Fin n, P.real {ω | Y i ω = 1} = p) :
    let Yf : Fin n → Ω → ℝ := fun j ω ↦ if j.1 < k then 1 else Y j ω
    let X_run : (Fin n → Ω → ℝ) → Fin n → Ω → ℝ :=
      fun Z i ω ↦ ∏ r : Fin k, Z ⟨(i.1 + r.1) % n, Nat.mod_lt _ hn⟩ ω
    let X : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_run Y i ω
    let Xs : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_run Yf i ω
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    IsSizeBias P X P Xs ∧
      (X ≤ᵐ[P] Xs) ∧
      (∀ᵐ ω ∂P, |Xs ω - X ω| ≤ (2 * (k : ℝ) - 1)) ∧
      (k ≤ n → μ = (n : ℝ) * p ^ k) ∧
      (2 * k - 1 ≤ n →
        ProbabilityTheory.variance X P =
          μ * (1 - p ^ k + 2 * ∑ r ∈ Finset.Ico 1 k, (p ^ r - p ^ k))) ∧
      ∀ t : ℝ, 0 ≤ t →
        P.real {ω | t ≤ |(X ω - μ) / σ|} ≤
          2 * Real.exp (-t ^ 2 / (2 * (2 * (k : ℝ) - 1) * (μ / σ ^ 2 + t / (2 * σ)))) := by
  intro Yf X_run X Xs μ σ
  let B : Ω → Fin n → Bool := fun ω j ↦ isOneBool (Y j ω)
  have hYf_meas : ∀ j : Fin n, Measurable (Yf j) := fun j ↦ by
    dsimp [Yf]; split_ifs; exacts [measurable_const, hY_meas j]
  have hX_meas : Measurable X :=
    Finset.measurable_sum Finset.univ fun _ _ ↦ Finset.measurable_prod Finset.univ fun _ _ ↦
      hY_meas _
  have hXs_meas : Measurable Xs :=
    Finset.measurable_sum Finset.univ fun _ _ ↦ Finset.measurable_prod Finset.univ fun _ _ ↦
      hYf_meas _
  have hae_all : ∀ᵐ ω ∂P, ∀ j : Fin n, Y j ω = 0 ∨ Y j ω = 1 := ae_all_iff.mpr hY01
  have hX_ae : X =ᵐ[P] fun ω ↦ cycSumBool hn k (B ω) := by
    filter_upwards [hae_all] with ω hω; dsimp [X, X_run, cycSumBool, cycRunBool, cycIdx, B]
    exact Finset.sum_congr rfl fun _ _ ↦
      Finset.prod_congr rfl fun _ _ ↦ (boolVal_isOneBool_of_zero_or_one (hω _)).symm
  have hXs_ae : Xs =ᵐ[P] fun ω ↦ cycSumBool hn k (forceBool k (B ω)) := by
    filter_upwards [hae_all] with ω hω
    dsimp [Xs, X_run, Yf, cycSumBool, cycRunBool, cycIdx, forceBool, B]
    refine Finset.sum_congr rfl fun _ _ ↦ Finset.prod_congr rfl fun _ _ ↦ ?_
    split_ifs; exacts [by simp [boolVal], (boolVal_isOneBool_of_zero_or_one (hω _)).symm]
  have hX_nn : 0 ≤ᵐ[P] X := hX_ae.mono fun ω hω ↦ by
    rw [hω]; exact Finset.sum_nonneg fun i _ ↦ cycRunBool_nonneg hn k (B ω) i
  have hX_le_n : ∀ᵐ ω ∂P, |X ω| ≤ (n : ℝ) := hX_ae.mono fun ω hω ↦ by
    dsimp only at hω
    have hnn : 0 ≤ cycSumBool hn k (B ω) :=
      Finset.sum_nonneg fun i _ ↦ cycRunBool_nonneg hn k (B ω) i
    rw [hω, abs_of_nonneg hnn]
    exact (Finset.sum_le_sum fun i _ ↦ cycRunBool_le_one hn k (B ω) i).trans_eq (by simp)
  have hX2 : MemLp X 2 P := MemLp.of_bound hX_meas.aestronglyMeasurable (n : ℝ) hX_le_n
  have hX_int : Integrable X P := hX2.integrable one_le_two
  have hMono : X ≤ᵐ[P] Xs := by
    filter_upwards [hX_ae, hXs_ae] with ω h1 h2; rw [h1, h2]; exact cycSumBool_mono_force hn k (B ω)
  have hDiff : ∀ᵐ ω ∂P, |Xs ω - X ω| ≤ 2 * (k : ℝ) - 1 := by
    filter_upwards [hX_ae, hXs_ae] with ω h1 h2
    rw [h1, h2, abs_of_nonneg (sub_nonneg.mpr (cycSumBool_mono_force hn k (B ω)))]
    exact cycSumBool_force_sub_le hn hk (B ω)
  have hμ_gen : μ = (n : ℝ) * p ^ (winSet hn k ⟨0, hn⟩).card := by
    dsimp [μ]; rw [integral_congr_ae hX_ae,
      integral_comp_isOneBool P hY_meas hIndep hProb (cycSumBool hn k), sum_cycSumBool_mean hn k p]
  have hμ_pos : 0 < μ := by
    rw [hμ_gen]; have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn; positivity
  have hSB : IsSizeBias P X P Xs := by
    refine ⟨hX_nn, hX_int, hXs_meas.aemeasurable, fun f _ _ ↦ ?_⟩
    have hLHS_ae : (fun ω ↦ X ω * f (X ω)) =ᵐ[P]
        fun ω ↦ cycSumBool hn k (B ω) * f (cycSumBool hn k (B ω)) :=
      hX_ae.mono fun _ hω ↦ by dsimp only at hω ⊢; rw [hω]
    have hRHS_ae : (fun ω ↦ f (Xs ω)) =ᵐ[P]
        fun ω ↦ f (cycSumBool hn k (forceBool k (B ω))) :=
      hXs_ae.mono fun _ hω ↦ by dsimp only at hω ⊢; rw [hω]
    rw [integral_congr_ae hLHS_ae, integral_congr_ae hRHS_ae,
      integral_comp_isOneBool P hY_meas hIndep hProb
        (fun x ↦ cycSumBool hn k x * f (cycSumBool hn k x)),
      integral_comp_isOneBool P hY_meas hIndep hProb
        (fun x ↦ f (cycSumBool hn k (forceBool k x))),
      sum_cycSumBool_mul_comp hn k p f, ← hμ_gen]
  have hMean_eq : k ≤ n → μ = (n : ℝ) * p ^ k := fun hkn ↦ by
    rw [hμ_gen, winSet_zero_eq_filter, card_filter_lt hkn]
  have hVar_eq : 2 * k - 1 ≤ n →
      ProbabilityTheory.variance X P =
        μ * (1 - p ^ k + 2 * ∑ r ∈ Finset.Ico 1 k, (p ^ r - p ^ k)) := fun hnk ↦ by
    have hX2_ae : (fun ω ↦ X ω ^ 2) =ᵐ[P] fun ω ↦ cycSumBool hn k (B ω) ^ 2 :=
      hX_ae.mono fun _ hω ↦ by dsimp only at hω ⊢; rw [hω]
    rw [ProbabilityTheory.variance_eq_sub hX2]; change (∫ ω, X ω ^ 2 ∂P) - μ ^ 2 = _
    rw [integral_congr_ae hX2_ae,
      integral_comp_isOneBool P hY_meas hIndep hProb (fun x ↦ cycSumBool hn k x ^ 2),
      hMean_eq (by omega)]
    exact sum_cycSumBool_sq_sub hn hk hnk p
  have hVar_pos : 0 < ProbabilityTheory.variance X P := by
    rw [ProbabilityTheory.variance_eq_integral hX_meas.aemeasurable]
    have hsub_ae : (fun ω ↦ (X ω - μ) ^ 2) =ᵐ[P] fun ω ↦ (cycSumBool hn k (B ω) - μ) ^ 2 :=
      hX_ae.mono fun _ hω ↦ by dsimp only at hω ⊢; rw [hω]
    change 0 < ∫ ω, (X ω - μ) ^ 2 ∂P
    rw [integral_congr_ae hsub_ae,
      integral_comp_isOneBool P hY_meas hIndep hProb (fun x ↦ (cycSumBool hn k x - μ) ^ 2)]
    let x₁ : Fin n → Bool := fun _ ↦ true
    let x₀ : Fin n → Bool := fun _ ↦ false
    have hx₀₁_ne : x₀ ≠ x₁ := fun h ↦ by have := congr_fun h ⟨0, hn⟩; simp [x₀, x₁] at this
    have hw_nn : ∀ x : Fin n → Bool, 0 ≤ bernVecWeight p x * (cycSumBool hn k x - μ) ^ 2 :=
      fun x ↦ mul_nonneg (Finset.prod_nonneg fun j _ ↦ by
        cases x j <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith) (sq_nonneg _)
    have hw₁_pos : 0 < bernVecWeight p x₁ := Finset.prod_pos fun _ _ ↦ by simp [x₁, hp0]
    have hw₀_pos : 0 < bernVecWeight p x₀ := Finset.prod_pos fun _ _ ↦ by simp [x₀]; linarith
    have hval₁ : cycSumBool hn k x₁ = (n : ℝ) := by unfold cycSumBool cycRunBool; simp [x₁, boolVal]
    have hval₀ : cycSumBool hn k x₀ = 0 :=
      Finset.sum_eq_zero fun _ _ ↦ Finset.prod_eq_zero (Finset.mem_univ ⟨0, hk⟩)
        (by simp [x₀, boolVal])
    have hpair_pos : 0 < bernVecWeight p x₀ * (cycSumBool hn k x₀ - μ) ^ 2 +
        bernVecWeight p x₁ * (cycSumBool hn k x₁ - μ) ^ 2 := by
      rw [hval₀, hval₁]
      have h0_pos : (0 - μ) ^ 2 > 0 := sq_pos_of_ne_zero (sub_ne_zero.mpr hμ_pos.ne)
      have h2_nn : 0 ≤ bernVecWeight p x₁ * ((n : ℝ) - μ) ^ 2 :=
        mul_nonneg hw₁_pos.le (sq_nonneg _)
      nlinarith [mul_pos hw₀_pos h0_pos]
    calc 0 < bernVecWeight p x₀ * (cycSumBool hn k x₀ - μ) ^ 2 +
            bernVecWeight p x₁ * (cycSumBool hn k x₁ - μ) ^ 2 := hpair_pos
      _ = ∑ x ∈ ({x₀, x₁} : Finset (Fin n → Bool)),
            bernVecWeight p x * (cycSumBool hn k x - μ) ^ 2 := by
          rw [Finset.sum_pair hx₀₁_ne]
      _ ≤ ∑ x : Fin n → Bool, bernVecWeight p x * (cycSumBool hn k x - μ) ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg hw_nn
  refine ⟨hSB, hMono, hDiff, hMean_eq, hVar_eq, fun t ht ↦ ?_⟩
  set C : ℝ := 2 * (k : ℝ) - 1
  have hC_pos : 0 < C := by
    have hk_cast : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
    dsimp [C]; linarith
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar_pos
  have hDiff_symm : ∀ᵐ ω ∂P, |X ω - Xs ω| ≤ C := hDiff.mono fun _ hω ↦ by rwa [abs_sub_comm]
  have hExp_int : Integrable (fun ω ↦ Real.exp ((2 / C) * X ω)) P := by
    refine (integrable_const (Real.exp ((2 / C) * (n : ℝ)))).mono'
      (Real.continuous_exp.measurable.comp (measurable_const.mul hX_meas)).aestronglyMeasurable ?_
    filter_upwards [hX_le_n] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hω) (by positivity))
  obtain ⟨hLow, hHigh⟩ := sizeBias_tail_bounds P hX_nn hX2 hVar_pos hSB hDiff_symm
  have h1 := hLow hMono t ht
  have h2 := hHigh hExp_int t ht
  have hUnion : {ω | t ≤ |(X ω - μ) / σ|} =
      {ω | t ≤ (X ω - μ) / σ} ∪ {ω | (X ω - μ) / σ ≤ -t} := by
    ext ω; simp only [Set.mem_ofPred, Set.mem_union, le_abs]
    exact or_congr_right ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
  have hSubadd : P.real {ω | t ≤ |(X ω - μ) / σ|} ≤
      P.real {ω | t ≤ (X ω - μ) / σ} + P.real {ω | (X ω - μ) / σ ≤ -t} := by
    rw [hUnion]; exact measureReal_union_le _ _
  have hDen1 : 0 < 2 * (C * μ / σ ^ 2) := by positivity
  have hDen2_le : 2 * (C * μ / σ ^ 2) ≤ 2 * C * (μ / σ ^ 2 + t / (2 * σ)) := by
    have : 0 ≤ C * t / σ := by positivity
    linarith [(by ring : 2 * C * (μ / σ ^ 2 + t / (2 * σ)) - 2 * (C * μ / σ ^ 2) = C * t / σ)]
  have hExp1_le : Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2))) ≤
      Real.exp (-t ^ 2 / (2 * C * (μ / σ ^ 2 + t / (2 * σ)))) := by
    refine Real.exp_le_exp.mpr ?_
    have hdiv_le := div_le_div_of_nonneg_left (sq_nonneg t) hDen1 hDen2_le
    linarith [
      (by ring : -t ^ 2 / (2 * (C * μ / σ ^ 2)) = -(t ^ 2 / (2 * (C * μ / σ ^ 2)))),
      (by ring : -t ^ 2 / (2 * C * (μ / σ ^ 2 + t / (2 * σ))) =
        -(t ^ 2 / (2 * C * (μ / σ ^ 2 + t / (2 * σ)))))]
  have hExp2_eq : Real.exp (-t ^ 2 / (2 * (C * μ / σ ^ 2 + C / (2 * σ) * t))) =
      Real.exp (-t ^ 2 / (2 * C * (μ / σ ^ 2 + t / (2 * σ)))) := by congr 2; ring
  rw [hExp2_eq] at h2
  linarith [hSubadd, h1.trans hExp1_le, h2]

/-- **Machine-checked counterexample to the printed variance formula in Example 7.6**
(`SteinIntro.tex:3883`; `ISSUE-EX7.6`): for $n = 4$ fair coin tosses ($p = 1/2$) and cyclic runs of
length $k = 2$ ($2k - 1 = 3 \le 4$), $\mu = \mathbb{E}[X] = 1$ and $\operatorname{Var}(X) = 5/4$,
whereas the printed formula evaluates to $1 \ne 5/4$. -/
theorem Ex7_6_variance_counterexample :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y : Fin 4 → Ω → ℝ),
      (∀ i : Fin 4, Measurable (Y i)) ∧ ProbabilityTheory.iIndepFun Y P ∧
      (∀ i : Fin 4, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) ∧
      (∀ i : Fin 4, P.real {ω | Y i ω = 1} = 1 / 2) ∧
      let X : Ω → ℝ := fun ω ↦ ∑ i : Fin 4, ∏ r : Fin 2,
        Y ⟨(i.1 + r.1) % 4, Nat.mod_lt _ (by omega)⟩ ω
      let μ : ℝ := ∫ ω, X ω ∂P
      μ = 1 ∧ ProbabilityTheory.variance X P = 5 / 4 ∧
        μ * (1 - (1 / 2 : ℝ) ^ 2 + ∑ r ∈ Finset.Ico 1 2, ((1 / 2 : ℝ) ^ r - (1 / 2 : ℝ) ^ 2)) =
          1 ∧
        ProbabilityTheory.variance X P ≠
          μ * (1 - (1 / 2 : ℝ) ^ 2 +
            ∑ r ∈ Finset.Ico 1 2, ((1 / 2 : ℝ) ^ r - (1 / 2 : ℝ) ^ 2)) := by
  let μ₀ : Measure Bool :=
    (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false
  have _ : IsProbabilityMeasure μ₀ := by
    rw [isProbabilityMeasure_iff]; simp [μ₀, ENNReal.inv_two_add_inv_two]
  let P : Measure (Fin 4 → Bool) := Measure.pi fun _ : Fin 4 ↦ μ₀
  let Y : Fin 4 → (Fin 4 → Bool) → ℝ := fun i ω ↦ boolVal (ω i)
  have hY_meas : ∀ i : Fin 4, Measurable (Y i) := fun i ↦
    (Measurable.of_discrete : Measurable boolVal).comp (measurable_pi_apply i)
  have hIndep : ProbabilityTheory.iIndepFun Y P :=
    ProbabilityTheory.iIndepFun_pi fun _ ↦
      (Measurable.of_discrete : Measurable boolVal).aemeasurable
  have hY01 : ∀ i : Fin 4, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1 :=
    fun i ↦ Eventually.of_forall fun ω ↦ by cases ω i <;> simp [Y, boolVal]
  have hProb : ∀ i : Fin 4, P.real {ω | Y i ω = 1} = 1 / 2 := fun i ↦ by
    have hset : {ω : Fin 4 → Bool | Y i ω = 1} =
        Set.pi Set.univ (Function.update (fun _ : Fin 4 ↦ (Set.univ : Set Bool)) i {true}) := by
      ext ω; simp only [Set.mem_ofPred, Set.mem_univ_pi]
      refine ⟨fun h1 j ↦ ?_, fun hall ↦ ?_⟩
      · by_cases hji : j = i
        · subst hji; rw [Function.update_self, Set.mem_singleton_iff]
          cases hω : ω j <;> simp [Y, boolVal, hω] at h1 ⊢
        · rw [Function.update_of_ne hji]; trivial
      · have hi := hall i
        rw [Function.update_self, Set.mem_singleton_iff] at hi; simp [Y, boolVal, hi]
    rw [measureReal_def, hset, Measure.pi_pi, Fintype.prod_eq_single i fun j hji ↦ by
      rw [Function.update_of_ne hji, measure_univ], Function.update_self]
    simp [μ₀]
  obtain ⟨_, _, _, hMean, hVar, _⟩ :=
    circularRuns_sizeBias_concentration P (by omega : 1 ≤ 4) (by omega : 1 ≤ 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hY_meas hIndep hY01 hProb
  refine ⟨Fin 4 → Bool, inferInstance, P, inferInstance, Y, hY_meas, hIndep, hY01, hProb, ?_⟩
  dsimp only
  have hIco : Finset.Ico 1 2 = ({1} : Finset ℕ) := by decide
  have hμ_val : (∫ ω, (∑ i : Fin 4, ∏ r : Fin 2,
      Y ⟨(i.1 + r.1) % 4, Nat.mod_lt _ (by omega)⟩ ω) ∂P) = 1 := by
    rw [hMean (by omega)]; norm_num
  have hVar_val : ProbabilityTheory.variance
      (fun ω ↦ ∑ i : Fin 4, ∏ r : Fin 2, Y ⟨(i.1 + r.1) % 4, Nat.mod_lt _ (by omega)⟩ ω) P =
      5 / 4 := by
    rw [hVar (by omega), hμ_val, hIco, Finset.sum_singleton]; norm_num
  refine ⟨hμ_val, hVar_val, ?_, ?_⟩
  · rw [hμ_val, hIco, Finset.sum_singleton]; norm_num
  · rw [hVar_val, hμ_val, hIco, Finset.sum_singleton]; norm_num

end SteinMethod
