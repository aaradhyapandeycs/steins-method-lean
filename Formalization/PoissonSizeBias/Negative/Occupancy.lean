/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Negative.Basic

/-!
# Ball-in-Box Couplings & Remark 4.17 (`Formalization.PoissonSizeBias.Negative.Occupancy`)

Formalizes the canonical multinomial ball-in-box model, empty-box moments, and **Remark 4.17**
(`SteinIntro.tex:2593-2601`, including `ISSUE-REM-4.17`):

- `ballBoxPMF`, `ballBoxMeasure`, `map_pi_eq_ballBoxMeasure`: canonical law on `Fin k → Fin n` for
  $k$ independent ball tosses with box probabilities $(p_1, \dots, p_n)$, plus pushforward from any
  realization `(Ω, P)`.
- `exists_ballBox_atMost_coupling`, `rem4_17_atMost`: inductive decreasing conditional coupling and
  Theorem 4.19 bound for the number of boxes containing **at most** $m \ge 0$ balls
  (`SteinIntro.tex:2594-2598`).
- `exists_ballBox_atLeast_coupling`, `rem4_17_atLeast_corrected`: inductive decreasing conditional
  coupling and Theorem 4.19 (`\ref{thm125}`) bound for the number of boxes containing **at least**
  $m \ge 1$ balls (`SteinIntro.tex:2600`; `ISSUE-REM-4.17`).
- `not_rem4_17_atLeast_printed`: refutation of the printed Theorem 4.14 (`\ref{thm122}`) bound for
  boxes containing at least $m \ge 1$ balls via $n = 2, k = 1, m = 1, p = (1/2, 1/2)$.
- `ballBox_empty_mean`, `ballBox_empty_variance`: exact mean and variance of the empty-box count
  ($m = 0$) for arbitrary $(p_1, \dots, p_n)$, reused in Examples 4.15 and 4.16.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Part 1: Canonical Multinomial Ball-in-Box Measure -/

/-- Probability weight $\prod_{t=0}^{k-1} p_{b(t)}$ of a ball-placement configuration
`b : Fin k → Fin n`. -/
noncomputable def ballBoxWeight {n : ℕ} (p : Fin n → ℝ) (k : ℕ) (b : Fin k → Fin n) : ℝ≥0∞ :=
  ∏ t : Fin k, ENNReal.ofReal (p (b t))

/-- Real probability weight $\prod_{t=0}^{k-1} p_{b(t)}$ of `b : Fin k → Fin n`. -/
def ballBoxRealWeight {n : ℕ} (p : Fin n → ℝ) (k : ℕ) (b : Fin k → Fin n) : ℝ :=
  ∏ t : Fin k, p (b t)

lemma ballBoxRealWeight_nonneg {n k : ℕ} {p : Fin n → ℝ} (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (b : Fin k → Fin n) : 0 ≤ ballBoxRealWeight p k b :=
  Finset.prod_nonneg fun t _ ↦ hp_nn (b t)

lemma ballBoxWeight_eq_ofReal {n : ℕ} {p : Fin n → ℝ} (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (k : ℕ) (b : Fin k → Fin n) :
    ballBoxWeight p k b = ENNReal.ofReal (ballBoxRealWeight p k b) := by
  unfold ballBoxWeight ballBoxRealWeight
  exact (ENNReal.ofReal_prod_of_nonneg fun t _ ↦ hp_nn (b t)).symm

lemma sum_ballBoxRealWeight {n : ℕ} {p : Fin n → ℝ} (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ) :
    (∑ b : Fin k → Fin n, ballBoxRealWeight p k b) = 1 := by
  unfold ballBoxRealWeight
  rw [← Fintype.prod_sum]
  simp [hp_sum]

lemma hasSum_ballBoxWeight {n : ℕ} (p : Fin n → ℝ) (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ) :
    HasSum (ballBoxWeight p k) 1 := by
  suffices h : (∑ b : Fin k → Fin n, ballBoxWeight p k b) = 1 from
    h ▸ hasSum_fintype (ballBoxWeight p k)
  simp_rw [ballBoxWeight_eq_ofReal hp_nn k]
  rw [← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ ballBoxRealWeight_nonneg hp_nn b,
    sum_ballBoxRealWeight hp_sum k, ENNReal.ofReal_one]

/-- Canonical `PMF` on `Fin k → Fin n` for $k$ independent ball placements with box probabilities
`p : Fin n → ℝ`. -/
noncomputable def ballBoxPMF {n : ℕ} (p : Fin n → ℝ) (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ) : PMF (Fin k → Fin n) :=
  ⟨ballBoxWeight p k, hasSum_ballBoxWeight p hp_nn hp_sum k⟩

/-- Canonical probability measure on `Fin k → Fin n` for $k$ independent ball placements with box
probabilities `p : Fin n → ℝ`. -/
noncomputable def ballBoxMeasure {n : ℕ} (p : Fin n → ℝ) (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ) : Measure (Fin k → Fin n) :=
  (ballBoxPMF p hp_nn hp_sum k).toMeasure

instance instIsProbabilityMeasureBallBoxMeasure {n : ℕ} (p : Fin n → ℝ)
    (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ) :
    IsProbabilityMeasure (ballBoxMeasure p hp_nn hp_sum k) :=
  PMF.toMeasure.isProbabilityMeasure _

@[simp]
lemma ballBoxMeasure_singleton {n : ℕ} (p : Fin n → ℝ) (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ) (b : Fin k → Fin n) :
    ballBoxMeasure p hp_nn hp_sum k {b} = ballBoxWeight p k b :=
  PMF.toMeasure_apply_singleton _ b .of_discrete

@[simp]
lemma ballBoxMeasure_real_singleton {n : ℕ} (p : Fin n → ℝ) (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ) (b : Fin k → Fin n) :
    (ballBoxMeasure p hp_nn hp_sum k).real {b} = ballBoxRealWeight p k b := by
  rw [measureReal_def, ballBoxMeasure_singleton, ballBoxWeight_eq_ofReal hp_nn,
    ENNReal.toReal_ofReal (ballBoxRealWeight_nonneg hp_nn b)]

lemma ballBoxMeasure_real_setOf {n : ℕ} (p : Fin n → ℝ) (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1) (k : ℕ)
    (P_pred : (Fin k → Fin n) → Prop) [DecidablePred P_pred] :
    (ballBoxMeasure p hp_nn hp_sum k).real {b | P_pred b} =
      ∑ b ∈ Finset.univ.filter P_pred, ballBoxRealWeight p k b := by
  have hunion : ({b : Fin k → Fin n | P_pred b}) =
      ⋃ b ∈ Finset.univ.filter P_pred, ({b} : Set (Fin k → Fin n)) := by
    ext b
    simp
  rw [measureReal_def, hunion, measure_biUnion_finset]
  · simp_rw [ballBoxMeasure_singleton, ballBoxWeight_eq_ofReal hp_nn]
    rw [← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ ballBoxRealWeight_nonneg hp_nn b,
      ENNReal.toReal_ofReal (Finset.sum_nonneg fun b _ ↦ ballBoxRealWeight_nonneg hp_nn b)]
  · intro x _ y _ hxy
    exact Set.disjoint_singleton.mpr hxy
  · intro _ _
    exact .of_discrete

/-- Pushforward of any independent family `B : Fin k → Ω → Fin n` with marginals `p i` equals
`ballBoxMeasure p hp_nn hp_sum k`. -/
theorem map_pi_eq_ballBoxMeasure
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Fin n → ℝ} (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1)
    {B : Fin k → Ω → Fin n} (hB_meas : ∀ t : Fin k, Measurable (B t))
    (hB_indep : ProbabilityTheory.iIndepFun B P)
    (hB_prob : ∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) :
    P.map (fun ω t ↦ B t ω) = ballBoxMeasure p hp_nn hp_sum k := by
  refine measure_ext_of_singleton_fintype fun b ↦ ?_
  have hBM : Measurable (fun ω t ↦ B t ω) := Measurable.of_eval hB_meas
  rw [Measure.map_apply hBM .of_discrete, ballBoxMeasure_singleton]
  have hpre : (fun ω t ↦ B t ω) ⁻¹' {b} = ⋂ t ∈ (Finset.univ : Finset (Fin k)), B t ⁻¹' {b t} := by
    ext ω
    simp [funext_iff]
  rw [hpre, (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hB_indep)
    Finset.univ (fun _ _ ↦ .of_discrete)]
  refine Finset.prod_congr rfl fun t _ ↦ ?_
  rw [← ofReal_measureReal]
  congr 1
  exact hB_prob t (b t)

/-! ### Part 2: Box Occupancy Counts & Recursive Decomposition -/

/-- Number of balls landing in box `i` under configuration `b : Fin k → Fin n`. -/
def boxCount {n k : ℕ} (i : Fin n) (b : Fin k → Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin k)).filter fun t ↦ b t = i).card

lemma boxCount_eq_sum {n k : ℕ} (i : Fin n) (b : Fin k → Fin n) :
    boxCount i b = ∑ t : Fin k, if b t = i then 1 else 0 := by
  unfold boxCount
  rw [Finset.card_filter]

lemma boxCount_cons {n k : ℕ} (i x : Fin n) (b' : Fin k → Fin n) :
    boxCount i (Fin.cons x b') = (if x = i then 1 else 0) + boxCount i b' := by
  rw [boxCount_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, ← boxCount_eq_sum]
  rfl

lemma ballBoxRealWeight_cons {n k : ℕ} (p : Fin n → ℝ) (x : Fin n) (b' : Fin k → Fin n) :
    ballBoxRealWeight p (k + 1) (Fin.cons x b') = p x * ballBoxRealWeight p k b' := by
  unfold ballBoxRealWeight
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  rfl

lemma ballBoxWeight_cons {n k : ℕ} (p : Fin n → ℝ) (x : Fin n) (b' : Fin k → Fin n) :
    ballBoxWeight p (k + 1) (Fin.cons x b') =
      ENNReal.ofReal (p x) * ballBoxWeight p k b' := by
  unfold ballBoxWeight
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  rfl

/-- Bijection between `Fin n × (Fin k → Fin n)` and `Fin (k + 1) → Fin n` via head and tail. -/
def headTailEquiv (n k : ℕ) : Fin n × (Fin k → Fin n) ≃ (Fin (k + 1) → Fin n) where
  toFun xb := Fin.cons xb.1 xb.2
  invFun b := (b 0, Fin.tail b)
  left_inv xb := by
    ext <;> simp [Fin.tail]
  right_inv b := Fin.cons_self_tail b

private lemma sum_erase_prob {n : ℕ} {p : Fin n → ℝ} (hp_sum : ∑ j : Fin n, p j = 1) (i : Fin n) :
    (∑ j ∈ Finset.univ.erase i, p j) = 1 - p i := by
  have h := Finset.sum_erase_add Finset.univ p (Finset.mem_univ i)
  linarith

private lemma hp_le_one {n : ℕ} {p : Fin n → ℝ} (hp_nn : ∀ j : Fin n, 0 ≤ p j)
    (hp_sum : ∑ j : Fin n, p j = 1) (i : Fin n) : p i ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ ↦ hp_nn j) (Finset.mem_univ i)
  linarith

private lemma sum_filter_fst_eq {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M]
    (f : α × α → M) (a : α) [DecidablePred fun z : α × α ↦ z.1 = a] :
    (∑ z ∈ Finset.univ.filter (fun z : α × α ↦ z.1 = a), f z) = ∑ b : α, f (a, b) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hxa
    exact Finset.sum_eq_zero fun y _ ↦ by simp [hxa]
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

private lemma sum_filter_snd_eq {α : Type*} [Fintype α] {M : Type*} [AddCommMonoid M]
    (f : α × α → M) (b : α) [DecidablePred fun z : α × α ↦ z.2 = b] :
    (∑ z ∈ Finset.univ.filter (fun z : α × α ↦ z.2 = b), f z) = ∑ a : α, f (a, b) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single b]
  · simp
  · intro y _ hyb
    simp [hyb]
  · intro hb
    exact False.elim (hb (Finset.mem_univ b))

/-! ### Part 3: Inductive Decreasing Conditional Coupling for At-Most-$m$ Balls -/

private lemma measureReal_atMost_succ {n k : ℕ} {p : Fin n → ℝ}
    (hp_nn : ∀ j : Fin n, 0 ≤ p j) (hp_sum : ∑ j : Fin n, p j = 1) (i : Fin n) (m : ℕ) :
    (ballBoxMeasure p hp_nn hp_sum (k + 1)).real {b | boxCount i b ≤ m} =
      p i *
          (if m = 0 then 0
           else (ballBoxMeasure p hp_nn hp_sum k).real {b' | boxCount i b' ≤ m - 1}) +
        (1 - p i) * (ballBoxMeasure p hp_nn hp_sum k).real {b' | boxCount i b' ≤ m} := by
  classical
  rw [ballBoxMeasure_real_setOf]
  have hsum_all :
      (∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) → Fin n ↦ boxCount i b ≤ m),
        ballBoxRealWeight p (k + 1) b) =
      ∑ x : Fin n, ∑ b' : Fin k → Fin n,
        if boxCount i (Fin.cons x b') ≤ m then
          ballBoxRealWeight p (k + 1) (Fin.cons x b')
        else 0 := by
    rw [Finset.sum_filter, ← (headTailEquiv n k).sum_comp
      (fun b ↦ if boxCount i b ≤ m then ballBoxRealWeight p (k + 1) b else 0),
      Fintype.sum_prod_type]
    rfl
  rw [hsum_all, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp only [boxCount_cons, ↓reduceIte, ballBoxRealWeight_cons]
    cases m with
    | zero =>
        simp
    | succ m' =>
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        have hiff : ∀ b' : Fin k → Fin n, (1 + boxCount i b' ≤ m' + 1) ↔ boxCount i b' ≤ m' :=
          fun _ ↦ by omega
        simp_rw [hiff, ← Finset.sum_filter, ← Finset.mul_sum]
        congr 1
        exact (ballBoxMeasure_real_setOf p hp_nn hp_sum k (fun b' ↦ boxCount i b' ≤ m')).symm
  · have hrest : ∀ j ∈ Finset.univ.erase i,
        (∑ b' : Fin k → Fin n,
          if boxCount i (Fin.cons j b') ≤ m then
            ballBoxRealWeight p (k + 1) (Fin.cons j b')
          else 0) =
          p j * (ballBoxMeasure p hp_nn hp_sum k).real {b' | boxCount i b' ≤ m} := by
      intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      simp_rw [boxCount_cons, ite_eq_right hj_ne, zero_add, ballBoxRealWeight_cons,
        ← Finset.sum_filter, ← Finset.mul_sum]
      congr 1
      exact (ballBoxMeasure_real_setOf p hp_nn hp_sum k (fun b' ↦ boxCount i b' ≤ m)).symm
    rw [Finset.sum_congr rfl hrest, ← Finset.sum_mul, sum_erase_prob hp_sum i]

/-- Inductive coupling on `Fin k → Fin n` between `ballBoxMeasure` and `ballBoxMeasure` conditioned
on `boxCount i b ≤ m`, increasing ball counts in boxes `j ≠ i` (`SteinIntro.tex:2595-2597`). -/
theorem exists_ballBox_atMost_coupling
    {n : ℕ} {p : Fin n → ℝ} (hp_nn : ∀ j : Fin n, 0 ≤ p j) (hp_sum : ∑ j : Fin n, p j = 1)
    (i : Fin n) :
    ∀ (k m : ℕ),
      0 < (ballBoxMeasure p hp_nn hp_sum k).real {b | boxCount i b ≤ m} →
      ∃ ν : Measure ((Fin k → Fin n) × (Fin k → Fin n)),
        IsProbabilityMeasure ν ∧
        ν.map Prod.fst = ballBoxMeasure p hp_nn hp_sum k ∧
        ν.map Prod.snd =
          ProbabilityTheory.cond (ballBoxMeasure p hp_nn hp_sum k) {b | boxCount i b ≤ m} ∧
        (∀ᵐ z ∂ν, ∀ j : Fin n, j ≠ i → boxCount j z.1 ≤ boxCount j z.2) := by
  classical
  intro k
  induction k with
  | zero =>
      intro m hpos
      let μ₀ := ballBoxMeasure p hp_nn hp_sum 0
      let ν := μ₀.map fun b ↦ (b, b)
      have hν_prob : IsProbabilityMeasure ν :=
        (Measure.isProbabilityMeasure_map_iff
          Measurable.of_discrete.aemeasurable).mpr inferInstance
      refine ⟨ν, hν_prob, ?_, ?_, ?_⟩
      · rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
        exact Measure.map_id
      · have hA_univ : ({b : Fin 0 → Fin n | boxCount i b ≤ m}) = Set.univ := by
          ext b
          simp [boxCount]
        rw [hA_univ, ProbabilityTheory.cond_univ,
          Measure.map_map Measurable.of_discrete Measurable.of_discrete]
        exact Measure.map_id
      · have hset : MeasurableSet
            {z : (Fin 0 → Fin n) × (Fin 0 → Fin n) |
              ∀ j : Fin n, j ≠ i → boxCount j z.1 ≤ boxCount j z.2} := .of_discrete
        rw [ae_map_iff Measurable.of_discrete.aemeasurable hset]
        exact Eventually.of_forall fun _ _ _ ↦ le_rfl
  | succ k ih =>
      intro m hZ_pos
      let μ := ballBoxMeasure p hp_nn hp_sum k
      let μ_s := ballBoxMeasure p hp_nn hp_sum (k + 1)
      set Z : ℝ := μ_s.real {b | boxCount i b ≤ m}
      set α₁ : ℝ := if m = 0 then 0 else μ.real {b' | boxCount i b' ≤ m - 1}
      set α₀ : ℝ := μ.real {b' | boxCount i b' ≤ m}
      have hZ_eq : Z = p i * α₁ + (1 - p i) * α₀ :=
        measureReal_atMost_succ hp_nn hp_sum i m
      have hα₁_nn : 0 ≤ α₁ := by
        by_cases hm : m = 0 <;> simp [α₁, hm, measureReal_nonneg]
      have hα₀_nn : 0 ≤ α₀ := measureReal_nonneg
      have hα_le : α₁ ≤ α₀ := by
        by_cases hm : m = 0
        · simp [α₁, hm, hα₀_nn]
        · simp only [α₁, hm, ↓reduceIte, α₀]
          refine measureReal_mono (fun b' hb' ↦ ?_) (measure_ne_top μ _)
          change boxCount i b' ≤ m - 1 at hb'
          change boxCount i b' ≤ m
          omega
      have hp_i_le : p i ≤ 1 := hp_le_one hp_nn hp_sum i
      let diag : Measure ((Fin k → Fin n) × (Fin k → Fin n)) := μ.map fun b' ↦ (b', b')
      have hdiag_prob : IsProbabilityMeasure diag :=
        (Measure.isProbabilityMeasure_map_iff
          Measurable.of_discrete.aemeasurable).mpr inferInstance
      have hdiag_fst : diag.map Prod.fst = μ := by
        rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
        exact Measure.map_id
      have hdiag_mono : ∀ᵐ z ∂diag, ∀ j : Fin n, j ≠ i → boxCount j z.1 ≤ boxCount j z.2 := by
        have hset : MeasurableSet
            {z : (Fin k → Fin n) × (Fin k → Fin n) |
              ∀ j : Fin n, j ≠ i → boxCount j z.1 ≤ boxCount j z.2} := .of_discrete
        rw [ae_map_iff Measurable.of_discrete.aemeasurable hset]
        exact Eventually.of_forall fun _ _ _ ↦ le_rfl
      let ν₀ : Measure ((Fin k → Fin n) × (Fin k → Fin n)) :=
        if h₀ : 0 < α₀ then (ih m h₀).choose else diag
      let ν₁ : Measure ((Fin k → Fin n) × (Fin k → Fin n)) :=
        if hm : m = 0 then diag
        else if h₁ : 0 < μ.real {b' | boxCount i b' ≤ m - 1} then (ih (m - 1) h₁).choose
        else diag
      have hν₀_fst : ν₀.map Prod.fst = μ := by
        by_cases h₀ : 0 < α₀
        · simpa [ν₀, h₀] using (ih m h₀).choose_spec.2.1
        · simp [ν₀, h₀, hdiag_fst]
      have hν₁_fst : ν₁.map Prod.fst = μ := by
        by_cases hm : m = 0
        · simp [ν₁, hm, hdiag_fst]
        · by_cases h₁ : 0 < μ.real {b' | boxCount i b' ≤ m - 1}
          · simpa [ν₁, hm, h₁] using (ih (m - 1) h₁).choose_spec.2.1
          · simp [ν₁, hm, h₁, hdiag_fst]
      have hν₀_mono : ∀ᵐ z ∂ν₀, ∀ j : Fin n, j ≠ i → boxCount j z.1 ≤ boxCount j z.2 := by
        by_cases h₀ : 0 < α₀
        · simpa [ν₀, h₀] using (ih m h₀).choose_spec.2.2.2
        · simp [ν₀, h₀, hdiag_mono]
      have hν₁_mono : ∀ᵐ z ∂ν₁, ∀ j : Fin n, j ≠ i → boxCount j z.1 ≤ boxCount j z.2 := by
        by_cases hm : m = 0
        · simp [ν₁, hm, hdiag_mono]
        · by_cases h₁ : 0 < μ.real {b' | boxCount i b' ≤ m - 1}
          · simpa [ν₁, hm, h₁] using (ih (m - 1) h₁).choose_spec.2.2.2
          · simp [ν₁, hm, h₁, hdiag_mono]
      let H : Fin n → Fin n → ℝ := fun x y ↦
        if x = i then
          if y = i then p i * α₁ / Z else p i * p y * (α₀ - α₁) / Z
        else
          if y = x then p x else 0
      have hH_nn : ∀ x y : Fin n, 0 ≤ H x y := by
        intro x y
        by_cases hx : x = i
        · by_cases hy : y = i
          · simp only [H, hx, hy, ↓reduceIte]
            exact div_nonneg (mul_nonneg (hp_nn i) hα₁_nn) hZ_pos.le
          · simp only [H, hx, hy, ↓reduceIte]
            exact div_nonneg
              (mul_nonneg (mul_nonneg (hp_nn i) (hp_nn y)) (sub_nonneg.mpr hα_le)) hZ_pos.le
        · by_cases hy : y = x <;> simp [H, hx, hy, hp_nn]
      have hH_row : ∀ x : Fin n, (∑ y : Fin n, H x y) = p x := by
        intro x
        by_cases hx : x = i
        · subst hx
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x)]
          have hrest : ∀ y ∈ Finset.univ.erase x, H x y = p x * p y * (α₀ - α₁) / Z := by
            intro y hy
            have hy_ne : y ≠ x := (Finset.mem_erase.mp hy).1
            simp [H, hy_ne]
          rw [Finset.sum_congr rfl hrest]
          simp only [H, ↓reduceIte]
          have hsum_y : (∑ y ∈ Finset.univ.erase x, p x * p y * (α₀ - α₁) / Z) =
              p x * (1 - p x) * (α₀ - α₁) / Z := by
            simp_rw [div_eq_mul_inv, mul_comm (p x), mul_assoc]
            rw [← Finset.sum_mul, sum_erase_prob hp_sum x]
          rw [hsum_y]
          have hnum : p x * α₁ + p x * (1 - p x) * (α₀ - α₁) = p x * Z := by
            rw [hZ_eq]
            ring
          calc p x * α₁ / Z + p x * (1 - p x) * (α₀ - α₁) / Z
            _ = (p x * α₁ + p x * (1 - p x) * (α₀ - α₁)) / Z := (add_div _ _ _).symm
            _ = p x * Z / Z := by rw [hnum]
            _ = p x := mul_div_cancel_right₀ (p x) hZ_pos.ne'
        · rw [Finset.sum_eq_single x]
          · simp [H, hx]
          · intro y _ hy
            simp [H, hx, hy]
          · intro habs
            exact False.elim (habs (Finset.mem_univ x))
      have hH_col_i : (∑ x : Fin n, H x i) = p i * α₁ / Z := by
        rw [Finset.sum_eq_single i]
        · simp [H]
        · intro x _ hx
          simp [H, hx, hx.symm]
        · intro habs
          exact False.elim (habs (Finset.mem_univ i))
      have hH_col_ne : ∀ j : Fin n, j ≠ i → (∑ x : Fin n, H x j) = p j * α₀ / Z := by
        intro j hj
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
        have herase : (∑ x ∈ Finset.univ.erase i, H x j) = p j := by
          rw [Finset.sum_eq_single j]
          · simp [H, hj]
          · intro x hx hxj
            have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
            simp [H, hxi, hxj.symm]
          · intro habs
            exact False.elim (habs (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
        rw [herase]
        simp only [H, ↓reduceIte, hj]
        field_simp [hZ_pos.ne']
        rw [hZ_eq]
        ring
      have hrow_tail : ∀ (ν_t : Measure ((Fin k → Fin n) × (Fin k → Fin n))),
          ν_t.map Prod.fst = μ →
          ∀ b₁' : Fin k → Fin n, (∑ b₂' : Fin k → Fin n, ν_t {(b₁', b₂')}) = μ {b₁'} := by
        intro ν_t hfst b₁'
        have hm1 := congrArg (fun m : Measure (Fin k → Fin n) ↦ m {b₁'}) hfst
        rw [measure_map_singleton_fintype ν_t Prod.fst b₁', sum_filter_fst_eq] at hm1
        exact hm1
      have hcol_tail : ∀ (ν_t : Measure ((Fin k → Fin n) × (Fin k → Fin n)))
          (μ_snd : Measure (Fin k → Fin n)),
          ν_t.map Prod.snd = μ_snd →
          ∀ b₂' : Fin k → Fin n, (∑ b₁' : Fin k → Fin n, ν_t {(b₁', b₂')}) = μ_snd {b₂'} := by
        intro ν_t μ_snd hsnd b₂'
        have hm2 := congrArg (fun m : Measure (Fin k → Fin n) ↦ m {b₂'}) hsnd
        rw [measure_map_singleton_fintype ν_t Prod.snd b₂', sum_filter_snd_eq] at hm2
        exact hm2
      let w : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n) → ℝ≥0∞ := fun ⟨b₁, b₂⟩ ↦
        ENNReal.ofReal (H (b₁ 0) (b₂ 0)) *
          (if b₂ 0 = i then ν₁ {(Fin.tail b₁, Fin.tail b₂)}
           else ν₀ {(Fin.tail b₁, Fin.tail b₂)})
      have hsum_b₂ : ∀ b₁ : Fin (k + 1) → Fin n,
          (∑ b₂ : Fin (k + 1) → Fin n, w (b₁, b₂)) = μ_s {b₁} := by
        intro b₁
        rw [← (headTailEquiv n k).sum_comp (fun b₂ ↦ w (b₁, b₂)), Fintype.sum_prod_type]
        have hinner : ∀ y : Fin n,
            (∑ b₂' : Fin k → Fin n, w (b₁, headTailEquiv n k (y, b₂'))) =
              ENNReal.ofReal (H (b₁ 0) y) * μ {Fin.tail b₁} := by
          intro y
          have hw_eq : ∀ b₂' : Fin k → Fin n,
              w (b₁, headTailEquiv n k (y, b₂')) =
                ENNReal.ofReal (H (b₁ 0) y) *
                  (if y = i then ν₁ {(Fin.tail b₁, b₂')} else ν₀ {(Fin.tail b₁, b₂')}) := by
            intro b₂'
            simp [w, headTailEquiv]
          simp_rw [hw_eq, ← Finset.mul_sum]
          by_cases hy : y = i
          · simp [hy, hrow_tail ν₁ hν₁_fst]
          · simp [hy, hrow_tail ν₀ hν₀_fst]
        simp_rw [hinner, ← Finset.sum_mul,
          ← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ hH_nn (b₁ 0) y, hH_row (b₁ 0)]
        rw [ballBoxMeasure_singleton, ballBoxMeasure_singleton,
          ← Fin.cons_self_tail b₁, ballBoxWeight_cons, Fin.cons_zero, Fin.tail_cons]
      have hsum_w : HasSum w 1 := by
        suffices h : (∑ z : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n), w z) = 1 from
          h ▸ hasSum_fintype w
        rw [Fintype.sum_prod_type]
        simp_rw [hsum_b₂]
        rw [sum_measure_singleton_fintype μ_s, measure_univ]
      let pmf_s : PMF ((Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n)) := ⟨w, hsum_w⟩
      let ν_s : Measure ((Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n)) := pmf_s.toMeasure
      have : IsProbabilityMeasure ν_s := PMF.toMeasure.isProbabilityMeasure pmf_s
      have hν_s_sing : ∀ z, ν_s {z} = w z :=
        fun z ↦ PMF.toMeasure_apply_singleton pmf_s z .of_discrete
      refine ⟨ν_s, inferInstance, ?_, ?_, ?_⟩
      · refine measure_ext_of_singleton_fintype fun b₁ ↦ ?_
        rw [measure_map_singleton_fintype ν_s Prod.fst b₁, sum_filter_fst_eq]
        simp_rw [hν_s_sing]
        exact hsum_b₂ b₁
      · refine measure_ext_of_singleton_fintype fun b₂ ↦ ?_
        rw [measure_map_singleton_fintype ν_s Prod.snd b₂, sum_filter_snd_eq]
        simp_rw [hν_s_sing]
        rw [← (headTailEquiv n k).sum_comp (fun b₁ ↦ w (b₁, b₂)), Fintype.sum_prod_type]
        have hZ_ne0 : μ_s {b | boxCount i b ≤ m} ≠ 0 := by
          intro h0
          have : Z = 0 := by simp [Z, measureReal_def, h0]
          linarith
        have hcond_s : ProbabilityTheory.cond μ_s {b | boxCount i b ≤ m} {b₂} =
            if boxCount i b₂ ≤ m then ENNReal.ofReal (μ_s.real {b₂} / Z) else 0 := by
          rw [ProbabilityTheory.cond_apply .of_discrete]
          by_cases hb₂ : boxCount i b₂ ≤ m
          · have hinter : ({b | boxCount i b ≤ m} ∩ {b₂}) = {b₂} := by
              ext b
              simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
              exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hb₂, h⟩⟩
            rw [ite_eq_left hb₂, hinter, ENNReal.ofReal_div_of_pos hZ_pos,
              ofReal_measureReal, ofReal_measureReal, div_eq_mul_inv, mul_comm]
          · have hinter : ({b | boxCount i b ≤ m} ∩ {b₂}) = ∅ := by
              ext b
              simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
                Set.mem_empty_iff_false, iff_false, not_and]
              intro h1 h2
              exact hb₂ (h2 ▸ h1)
            rw [ite_eq_right hb₂, hinter, measure_empty, mul_zero]
        rw [hcond_s]
        by_cases hy : b₂ 0 = i
        · have hw_i : ∀ (x : Fin n) (b₁' : Fin k → Fin n),
              w (headTailEquiv n k (x, b₁'), b₂) =
                ENNReal.ofReal (H x i) * ν₁ {(b₁', Fin.tail b₂)} := by
            intro x b₁'
            simp [w, headTailEquiv, hy]
          simp_rw [hw_i, ← Finset.mul_sum, ← Finset.sum_mul,
            ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hH_nn x i, hH_col_i]
          by_cases hm : m = 0
          · have hb₂_not : ¬ (boxCount i b₂ ≤ m) := by
              rw [← Fin.cons_self_tail b₂, boxCount_cons, hy, ite_eq_left rfl, hm]
              omega
            rw [ite_eq_right hb₂_not]
            simp [α₁, hm]
          · by_cases h₁ : 0 < μ.real {b' | boxCount i b' ≤ m - 1}
            · have hν₁_snd : ν₁.map Prod.snd =
                  ProbabilityTheory.cond μ {b' | boxCount i b' ≤ m - 1} := by
                simpa [ν₁, hm, h₁] using (ih (m - 1) h₁).choose_spec.2.2.1
              rw [hcol_tail ν₁ _ hν₁_snd (Fin.tail b₂),
                ProbabilityTheory.cond_apply .of_discrete]
              have hα₁_eq : α₁ = μ.real {b' | boxCount i b' ≤ m - 1} := by simp [α₁, hm]
              have hiff : (boxCount i b₂ ≤ m) ↔ boxCount i (Fin.tail b₂) ≤ m - 1 := by
                conv_lhs => rw [← Fin.cons_self_tail b₂, boxCount_cons, hy, ite_eq_left rfl]
                omega
              by_cases htail : boxCount i (Fin.tail b₂) ≤ m - 1
              · have hinter : ({b' | boxCount i b' ≤ m - 1} ∩ {Fin.tail b₂}) = {Fin.tail b₂} := by
                  ext b'
                  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
                  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ htail, h⟩⟩
                rw [ite_eq_left (hiff.mpr htail), hinter,
                  ← ofReal_measureReal (μ := μ) (s := {Fin.tail b₂}),
                  ← ofReal_measureReal (μ := μ) (s := {b' | boxCount i b' ≤ m - 1}),
                  ← hα₁_eq, ← ENNReal.ofReal_inv_of_pos (hα₁_eq ▸ h₁),
                  ← ENNReal.ofReal_mul (inv_nonneg.mpr (hα₁_eq ▸ h₁.le)),
                  ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (hp_nn i) hα₁_nn) hZ_pos.le)]
                congr 1
                have hμs_b₂ : μ_s.real {b₂} = p i * μ.real {Fin.tail b₂} := by
                  conv_lhs => rw [← Fin.cons_self_tail b₂]
                  rw [ballBoxMeasure_real_singleton, ballBoxRealWeight_cons, hy,
                    ballBoxMeasure_real_singleton]
                rw [hμs_b₂]
                have hα₁_ne : α₁ ≠ 0 := (hα₁_eq ▸ h₁).ne'
                field_simp [hα₁_ne, hZ_pos.ne']
              · have hinter : ({b' | boxCount i b' ≤ m - 1} ∩ {Fin.tail b₂}) = ∅ := by
                  ext b'
                  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
                    Set.mem_empty_iff_false, iff_false, not_and]
                  intro h1 h2
                  exact htail (h2 ▸ h1)
                rw [ite_eq_right (mt hiff.mp htail), hinter, measure_empty, mul_zero, mul_zero]
            · have hα₁_zero : α₁ = 0 := by
                have hle0 : μ.real {b' | boxCount i b' ≤ m - 1} ≤ 0 := not_lt.mp h₁
                have h0 : μ.real {b' | boxCount i b' ≤ m - 1} = 0 :=
                  le_antisymm hle0 measureReal_nonneg
                simp [α₁, hm, h0]
              rw [hα₁_zero, mul_zero, zero_div, ENNReal.ofReal_zero, zero_mul]
              by_cases hb₂ : boxCount i b₂ ≤ m
              · have htail : boxCount i (Fin.tail b₂) ≤ m - 1 := by
                  have hb₂' := hb₂
                  rw [← Fin.cons_self_tail b₂, boxCount_cons, hy, ite_eq_left rfl] at hb₂'
                  omega
                have hle_t : μ.real {Fin.tail b₂} ≤ μ.real {b' | boxCount i b' ≤ m - 1} :=
                  measureReal_mono (Set.singleton_subset_iff.mpr htail) (measure_ne_top μ _)
                have ht0 : μ.real {Fin.tail b₂} = 0 :=
                  le_antisymm (hle_t.trans (not_lt.mp h₁)) measureReal_nonneg
                have hμs0 : μ_s.real {b₂} = 0 := by
                  conv_lhs => rw [← Fin.cons_self_tail b₂]
                  rw [ballBoxMeasure_real_singleton, ballBoxRealWeight_cons, hy,
                    ← ballBoxMeasure_real_singleton p hp_nn hp_sum k, ht0, mul_zero]
                rw [ite_eq_left hb₂, hμs0, zero_div, ENNReal.ofReal_zero]
              · rw [ite_eq_right hb₂]
        · have hb₂0 : b₂ 0 ≠ i := hy
          set j := b₂ 0
          have hj : j ≠ i := hy
          have hw_j : ∀ (x : Fin n) (b₁' : Fin k → Fin n),
              w (headTailEquiv n k (x, b₁'), b₂) =
                ENNReal.ofReal (H x j) * ν₀ {(b₁', Fin.tail b₂)} := by
            intro x b₁'
            simp [w, headTailEquiv, hb₂0, j]
          simp_rw [hw_j, ← Finset.mul_sum, ← Finset.sum_mul,
            ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hH_nn x j, hH_col_ne j hj]
          have hiff : (boxCount i b₂ ≤ m) ↔ boxCount i (Fin.tail b₂) ≤ m := by
            conv_lhs => rw [← Fin.cons_self_tail b₂, boxCount_cons, ite_eq_right hj, zero_add]
          by_cases h₀ : 0 < α₀
          · have hν₀_snd : ν₀.map Prod.snd =
                ProbabilityTheory.cond μ {b' | boxCount i b' ≤ m} := by
              simpa [ν₀, h₀] using (ih m h₀).choose_spec.2.2.1
            rw [hcol_tail ν₀ _ hν₀_snd (Fin.tail b₂),
              ProbabilityTheory.cond_apply .of_discrete]
            by_cases htail : boxCount i (Fin.tail b₂) ≤ m
            · have hinter : ({b' | boxCount i b' ≤ m} ∩ {Fin.tail b₂}) = {Fin.tail b₂} := by
                ext b'
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
                exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ htail, h⟩⟩
              rw [ite_eq_left (hiff.mpr htail), hinter,
                ← ofReal_measureReal (μ := μ) (s := {Fin.tail b₂}),
                ← ofReal_measureReal (μ := μ) (s := {b' | boxCount i b' ≤ m}),
                ← ENNReal.ofReal_inv_of_pos h₀,
                ← ENNReal.ofReal_mul (inv_nonneg.mpr h₀.le),
                ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (hp_nn j) hα₀_nn) hZ_pos.le)]
              congr 1
              have hμs_b₂ : μ_s.real {b₂} = p j * μ.real {Fin.tail b₂} := by
                conv_lhs => rw [← Fin.cons_self_tail b₂]
                rw [ballBoxMeasure_real_singleton, ballBoxRealWeight_cons,
                  ballBoxMeasure_real_singleton]
              rw [hμs_b₂]
              field_simp [h₀.ne', hZ_pos.ne']
            · have hinter : ({b' | boxCount i b' ≤ m} ∩ {Fin.tail b₂}) = ∅ := by
                ext b'
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
                  Set.mem_empty_iff_false, iff_false, not_and]
                intro h1 h2
                exact htail (h2 ▸ h1)
              rw [ite_eq_right (mt hiff.mp htail), hinter, measure_empty, mul_zero, mul_zero]
          · have hα₀_zero : α₀ = 0 := le_antisymm (not_lt.mp h₀) hα₀_nn
            rw [hα₀_zero, mul_zero, zero_div, ENNReal.ofReal_zero, zero_mul]
            by_cases hb₂ : boxCount i b₂ ≤ m
            · have htail : boxCount i (Fin.tail b₂) ≤ m := hiff.mp hb₂
              have hle_t : μ.real {Fin.tail b₂} ≤ α₀ :=
                measureReal_mono (Set.singleton_subset_iff.mpr htail) (measure_ne_top μ _)
              have ht0 : μ.real {Fin.tail b₂} = 0 :=
                le_antisymm (hle_t.trans (le_of_eq hα₀_zero)) measureReal_nonneg
              have hμs0 : μ_s.real {b₂} = 0 := by
                conv_lhs => rw [← Fin.cons_self_tail b₂]
                rw [ballBoxMeasure_real_singleton, ballBoxRealWeight_cons,
                  ← ballBoxMeasure_real_singleton p hp_nn hp_sum k, ht0, mul_zero]
              rw [ite_eq_left hb₂, hμs0, zero_div, ENNReal.ofReal_zero]
            · rw [ite_eq_right hb₂]
      · rw [eventually_iff, MeasureTheory.mem_ae_iff]
        have hbad_sub :
            {z : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n) |
              ¬ ∀ j : Fin n, j ≠ i → boxCount j z.1 ≤ boxCount j z.2} ⊆
            {z | ν_s {z} = 0} := by
          intro ⟨b₁, b₂⟩ hnot
          by_contra hne0
          rw [Set.mem_ofPred_eq, hν_s_sing] at hne0
          have hH_ne0 : ENNReal.ofReal (H (b₁ 0) (b₂ 0)) ≠ 0 := left_ne_zero_of_mul hne0
          have htail_ne0 :
              (if b₂ 0 = i then ν₁ {(Fin.tail b₁, Fin.tail b₂)}
               else ν₀ {(Fin.tail b₁, Fin.tail b₂)}) ≠ 0 := right_ne_zero_of_mul hne0
          have hhead_le : ∀ j : Fin n, j ≠ i →
              (if b₁ 0 = j then 1 else 0) ≤ (if b₂ 0 = j then 1 else 0) := by
            intro j hj
            by_cases hb₁j : b₁ 0 = j
            · have hb₁_ne_i : b₁ 0 ≠ i := hb₁j ▸ hj
              have hb₂_eq : b₂ 0 = b₁ 0 := by
                by_contra hneq
                have hH0 : H (b₁ 0) (b₂ 0) = 0 := by simp [H, hb₁_ne_i, hneq]
                exact hH_ne0 (by simp [hH0])
              simp [hb₁j, hb₂_eq]
            · simp [hb₁j]
          have htail_le : ∀ j : Fin n, j ≠ i →
              boxCount j (Fin.tail b₁) ≤ boxCount j (Fin.tail b₂) := by
            by_cases hb₂i : b₂ 0 = i
            · simp only [hb₂i, ↓reduceIte] at htail_ne0
              by_contra hnot_t
              have hnull : ν₁ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.1 ≤ boxCount j u.2} = 0 :=
                MeasureTheory.mem_ae_iff.mp hν₁_mono
              have hle_null : ν₁ {(Fin.tail b₁, Fin.tail b₂)} ≤
                  ν₁ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.1 ≤ boxCount j u.2} :=
                measure_mono (Set.singleton_subset_iff.mpr hnot_t)
              exact htail_ne0 (le_antisymm (hle_null.trans (le_of_eq hnull)) zero_le)
            · simp only [hb₂i, ↓reduceIte] at htail_ne0
              by_contra hnot_t
              have hnull : ν₀ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.1 ≤ boxCount j u.2} = 0 :=
                MeasureTheory.mem_ae_iff.mp hν₀_mono
              have hle_null : ν₀ {(Fin.tail b₁, Fin.tail b₂)} ≤
                  ν₀ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.1 ≤ boxCount j u.2} :=
                measure_mono (Set.singleton_subset_iff.mpr hnot_t)
              exact htail_ne0 (le_antisymm (hle_null.trans (le_of_eq hnull)) zero_le)
          apply hnot
          intro j hj
          have hc1 : boxCount j b₁ = (if b₁ 0 = j then 1 else 0) + boxCount j (Fin.tail b₁) := by
            conv_lhs => rw [← Fin.cons_self_tail b₁, boxCount_cons]
          have hc2 : boxCount j b₂ = (if b₂ 0 = j then 1 else 0) + boxCount j (Fin.tail b₂) := by
            conv_lhs => rw [← Fin.cons_self_tail b₂, boxCount_cons]
          rw [hc1, hc2]
          exact Nat.add_le_add (hhead_le j hj) (htail_le j hj)
        have hzero_set : ν_s {z | ν_s {z} = 0} = 0 := by
          have hunion : ({z : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n) | ν_s {z} = 0}) =
              ⋃ z ∈ Finset.univ.filter (fun z ↦ ν_s {z} = 0), {z} := by
            ext z
            simp
          rw [hunion, measure_biUnion_finset]
          · refine Finset.sum_eq_zero fun z hz ↦ ?_
            exact (Finset.mem_filter.mp hz).2
          · intro x _ y _ hxy
            exact Set.disjoint_singleton.mpr hxy
          · intro _ _
            exact .of_discrete
        exact le_antisymm ((measure_mono hbad_sub).trans (le_of_eq hzero_set)) zero_le

/-! ### Part 4: Inductive Decreasing Conditional Coupling for At-Least-$m$ Balls -/

private lemma measureReal_atLeast_succ {n k : ℕ} {p : Fin n → ℝ}
    (hp_nn : ∀ j : Fin n, 0 ≤ p j) (hp_sum : ∑ j : Fin n, p j = 1) (i : Fin n)
    {m : ℕ} (hm : 1 ≤ m) :
    (ballBoxMeasure p hp_nn hp_sum (k + 1)).real {b | m ≤ boxCount i b} =
      p i * (ballBoxMeasure p hp_nn hp_sum k).real {b' | m - 1 ≤ boxCount i b'} +
        (1 - p i) * (ballBoxMeasure p hp_nn hp_sum k).real {b' | m ≤ boxCount i b'} := by
  classical
  rw [ballBoxMeasure_real_setOf]
  have hsum_all :
      (∑ b ∈ Finset.univ.filter (fun b : Fin (k + 1) → Fin n ↦ m ≤ boxCount i b),
        ballBoxRealWeight p (k + 1) b) =
      ∑ x : Fin n, ∑ b' : Fin k → Fin n,
        if m ≤ boxCount i (Fin.cons x b') then
          ballBoxRealWeight p (k + 1) (Fin.cons x b')
        else 0 := by
    rw [Finset.sum_filter, ← (headTailEquiv n k).sum_comp
      (fun b ↦ if m ≤ boxCount i b then ballBoxRealWeight p (k + 1) b else 0),
      Fintype.sum_prod_type]
    rfl
  rw [hsum_all, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp only [boxCount_cons, ↓reduceIte, ballBoxRealWeight_cons]
    have hiff : ∀ b' : Fin k → Fin n, (m ≤ 1 + boxCount i b') ↔ m - 1 ≤ boxCount i b' :=
      fun _ ↦ by omega
    simp_rw [hiff, ← Finset.sum_filter, ← Finset.mul_sum]
    congr 1
    exact (ballBoxMeasure_real_setOf p hp_nn hp_sum k (fun b' ↦ m - 1 ≤ boxCount i b')).symm
  · have hrest : ∀ j ∈ Finset.univ.erase i,
        (∑ b' : Fin k → Fin n,
          if m ≤ boxCount i (Fin.cons j b') then
            ballBoxRealWeight p (k + 1) (Fin.cons j b')
          else 0) =
          p j * (ballBoxMeasure p hp_nn hp_sum k).real {b' | m ≤ boxCount i b'} := by
      intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      simp_rw [boxCount_cons, ite_eq_right hj_ne, zero_add, ballBoxRealWeight_cons,
        ← Finset.sum_filter, ← Finset.mul_sum]
      congr 1
      exact (ballBoxMeasure_real_setOf p hp_nn hp_sum k (fun b' ↦ m ≤ boxCount i b')).symm
    rw [Finset.sum_congr rfl hrest, ← Finset.sum_mul, sum_erase_prob hp_sum i]

/-- Inductive coupling on `Fin k → Fin n` between `ballBoxMeasure` and `ballBoxMeasure` conditioned
on `m ≤ boxCount i b`, **decreasing** the ball counts in all boxes `j ≠ i`
(`SteinIntro.tex:2600`; `ISSUE-REM-4.17`). -/
theorem exists_ballBox_atLeast_coupling
    {n : ℕ} {p : Fin n → ℝ} (hp_nn : ∀ j : Fin n, 0 ≤ p j) (hp_sum : ∑ j : Fin n, p j = 1)
    (i : Fin n) :
    ∀ (k m : ℕ),
      0 < (ballBoxMeasure p hp_nn hp_sum k).real {b | m ≤ boxCount i b} →
      ∃ ν : Measure ((Fin k → Fin n) × (Fin k → Fin n)),
        IsProbabilityMeasure ν ∧
        ν.map Prod.fst = ballBoxMeasure p hp_nn hp_sum k ∧
        ν.map Prod.snd =
          ProbabilityTheory.cond (ballBoxMeasure p hp_nn hp_sum k) {b | m ≤ boxCount i b} ∧
        (∀ᵐ z ∂ν, ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1) := by
  classical
  intro k
  induction k with
  | zero =>
      intro m hpos
      have hm0 : m = 0 := by
        by_contra hne
        have hempty : ({b : Fin 0 → Fin n | m ≤ boxCount i b}) = ∅ := by
          ext b
          simp only [Set.mem_ofPred_eq, boxCount, Finset.univ_eq_empty, Finset.filter_empty,
            Finset.card_empty, Set.mem_empty_iff_false, iff_false]
          omega
        rw [hempty, measureReal_empty] at hpos
        exact lt_irrefl 0 hpos
      subst hm0
      let μ₀ := ballBoxMeasure p hp_nn hp_sum 0
      let ν := μ₀.map fun b ↦ (b, b)
      have hν_prob : IsProbabilityMeasure ν :=
        (Measure.isProbabilityMeasure_map_iff
          Measurable.of_discrete.aemeasurable).mpr inferInstance
      refine ⟨ν, hν_prob, ?_, ?_, ?_⟩
      · rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
        exact Measure.map_id
      · have hA_univ : ({b : Fin 0 → Fin n | 0 ≤ boxCount i b}) = Set.univ := by
          ext b
          simp
        rw [hA_univ, ProbabilityTheory.cond_univ,
          Measure.map_map Measurable.of_discrete Measurable.of_discrete]
        exact Measure.map_id
      · have hset : MeasurableSet
            {z : (Fin 0 → Fin n) × (Fin 0 → Fin n) |
              ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1} := .of_discrete
        rw [ae_map_iff Measurable.of_discrete.aemeasurable hset]
        exact Eventually.of_forall fun _ _ _ ↦ le_rfl
  | succ k ih =>
      intro m hZ_pos
      let μ := ballBoxMeasure p hp_nn hp_sum k
      let μ_s := ballBoxMeasure p hp_nn hp_sum (k + 1)
      by_cases hm0 : m = 0
      · subst hm0
        let ν := μ_s.map fun b ↦ (b, b)
        have hν_prob : IsProbabilityMeasure ν :=
          (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr
            inferInstance
        refine ⟨ν, hν_prob, ?_, ?_, ?_⟩
        · rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
          exact Measure.map_id
        · have hA_univ : ({b : Fin (k + 1) → Fin n | 0 ≤ boxCount i b}) = Set.univ := by
            ext b
            simp
          rw [hA_univ, ProbabilityTheory.cond_univ,
            Measure.map_map Measurable.of_discrete Measurable.of_discrete]
          exact Measure.map_id
        · have hset : MeasurableSet
              {z : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n) |
                ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1} := .of_discrete
          rw [ae_map_iff Measurable.of_discrete.aemeasurable hset]
          exact Eventually.of_forall fun _ _ _ ↦ le_rfl
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        set Z : ℝ := μ_s.real {b | m ≤ boxCount i b}
        set β₁ : ℝ := μ.real {b' | m - 1 ≤ boxCount i b'}
        set β₀ : ℝ := μ.real {b' | m ≤ boxCount i b'}
        have hZ_eq : Z = p i * β₁ + (1 - p i) * β₀ :=
          measureReal_atLeast_succ hp_nn hp_sum i hm1
        have hβ₁_nn : 0 ≤ β₁ := measureReal_nonneg
        have hβ₀_nn : 0 ≤ β₀ := measureReal_nonneg
        have hβ_le : β₀ ≤ β₁ := by
          refine measureReal_mono (fun b' hb' ↦ ?_) (measure_ne_top μ _)
          simp only [Set.mem_ofPred_eq] at hb' ⊢
          omega
        have hp_i_le : p i ≤ 1 := hp_le_one hp_nn hp_sum i
        have hβ₁_pos : 0 < β₁ := by
          by_contra hnot
          have hβ₁_0 : β₁ = 0 := le_antisymm (not_lt.mp hnot) hβ₁_nn
          have hβ₀_0 : β₀ = 0 := le_antisymm (hβ_le.trans (le_of_eq hβ₁_0)) hβ₀_nn
          have hZ_0 : Z = 0 := by rw [hZ_eq, hβ₁_0, hβ₀_0]; ring
          linarith
        let diag : Measure ((Fin k → Fin n) × (Fin k → Fin n)) := μ.map fun b' ↦ (b', b')
        have hdiag_fst : diag.map Prod.fst = μ := by
          rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
          exact Measure.map_id
        have hdiag_mono : ∀ᵐ z ∂diag, ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1 := by
          have hset : MeasurableSet
              {z : (Fin k → Fin n) × (Fin k → Fin n) |
                ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1} := .of_discrete
          rw [ae_map_iff Measurable.of_discrete.aemeasurable hset]
          exact Eventually.of_forall fun _ _ _ ↦ le_rfl
        let ν₁ : Measure ((Fin k → Fin n) × (Fin k → Fin n)) := (ih (m - 1) hβ₁_pos).choose
        let ν₀ : Measure ((Fin k → Fin n) × (Fin k → Fin n)) :=
          if h₀ : 0 < β₀ then (ih m h₀).choose else diag
        have hν₁_fst : ν₁.map Prod.fst = μ := (ih (m - 1) hβ₁_pos).choose_spec.2.1
        have hν₁_snd : ν₁.map Prod.snd = ProbabilityTheory.cond μ {b' | m - 1 ≤ boxCount i b'} :=
          (ih (m - 1) hβ₁_pos).choose_spec.2.2.1
        have hν₁_mono : ∀ᵐ z ∂ν₁, ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1 :=
          (ih (m - 1) hβ₁_pos).choose_spec.2.2.2
        have hν₀_fst : ν₀.map Prod.fst = μ := by
          by_cases h₀ : 0 < β₀
          · simpa [ν₀, h₀] using (ih m h₀).choose_spec.2.1
          · simp [ν₀, h₀, hdiag_fst]
        have hν₀_mono : ∀ᵐ z ∂ν₀, ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1 := by
          by_cases h₀ : 0 < β₀
          · simpa [ν₀, h₀] using (ih m h₀).choose_spec.2.2.2
          · simp [ν₀, h₀, hdiag_mono]
        let H : Fin n → Fin n → ℝ := fun x y ↦
          if x = i then
            if y = i then p i else 0
          else
            if y = i then p x * p i * (β₁ - β₀) / Z
            else if y = x then p x * β₀ / Z
            else 0
        have hH_nn : ∀ x y : Fin n, 0 ≤ H x y := by
          intro x y
          by_cases hx : x = i
          · by_cases hy : y = i <;> simp [H, hx, hy, hp_nn]
          · by_cases hy : y = i
            · simp only [H, hx, hy, ↓reduceIte]
              exact div_nonneg
                (mul_nonneg (mul_nonneg (hp_nn x) (hp_nn i)) (sub_nonneg.mpr hβ_le)) hZ_pos.le
            · by_cases hyx : y = x
              · simp only [H, hx, hyx, ↓reduceIte]
                exact div_nonneg (mul_nonneg (hp_nn x) hβ₀_nn) hZ_pos.le
              · simp [H, hx, hy, hyx]
        have hH_row : ∀ x : Fin n, (∑ y : Fin n, H x y) = p x := by
          intro x
          by_cases hx : x = i
          · rw [Finset.sum_eq_single i]
            · simp [H, hx]
            · intro y _ hy
              simp [H, hx, hy]
            · intro habs
              exact False.elim (habs (Finset.mem_univ i))
          · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
            have herase : (∑ y ∈ Finset.univ.erase i, H x y) = p x * β₀ / Z := by
              rw [Finset.sum_eq_single x]
              · simp [H, hx]
              · intro y hy hyx
                have hyi : y ≠ i := (Finset.mem_erase.mp hy).1
                simp [H, hx, hyi, hyx]
              · intro habs
                exact False.elim (habs (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩))
            rw [herase]
            simp only [H, hx, ↓reduceIte]
            field_simp [hZ_pos.ne']
            rw [hZ_eq]
            ring
        have hH_col_i : (∑ x : Fin n, H x i) = p i * β₁ / Z := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
          have hrest : ∀ x ∈ Finset.univ.erase i, H x i = p x * p i * (β₁ - β₀) / Z := by
            intro x hx
            have hxi : x ≠ i := (Finset.mem_erase.mp hx).1
            simp [H, hxi]
          rw [Finset.sum_congr rfl hrest]
          simp only [H, ↓reduceIte]
          have hsum_x : (∑ x ∈ Finset.univ.erase i, p x * p i * (β₁ - β₀) / Z) =
              (1 - p i) * p i * (β₁ - β₀) / Z := by
            simp_rw [div_eq_mul_inv, mul_assoc]
            rw [← Finset.sum_mul, sum_erase_prob hp_sum i]
          rw [hsum_x]
          field_simp [hZ_pos.ne']
          rw [hZ_eq]
          ring
        have hH_col_ne : ∀ j : Fin n, j ≠ i → (∑ x : Fin n, H x j) = p j * β₀ / Z := by
          intro j hj
          rw [Finset.sum_eq_single j]
          · simp [H, hj]
          · intro x _ hxj
            by_cases hxi : x = i
            · simp [H, hxi, hj]
            · simp [H, hxi, hj, hxj.symm]
          · intro habs
            exact False.elim (habs (Finset.mem_univ j))
        have hrow_tail : ∀ (ν_t : Measure ((Fin k → Fin n) × (Fin k → Fin n))),
            ν_t.map Prod.fst = μ →
            ∀ b₁' : Fin k → Fin n, (∑ b₂' : Fin k → Fin n, ν_t {(b₁', b₂')}) = μ {b₁'} := by
          intro ν_t hfst b₁'
          have hm_eq := congrArg (fun m : Measure (Fin k → Fin n) ↦ m {b₁'}) hfst
          rw [measure_map_singleton_fintype ν_t Prod.fst b₁', sum_filter_fst_eq] at hm_eq
          exact hm_eq
        have hcol_tail : ∀ (ν_t : Measure ((Fin k → Fin n) × (Fin k → Fin n)))
            (μ_snd : Measure (Fin k → Fin n)),
            ν_t.map Prod.snd = μ_snd →
            ∀ b₂' : Fin k → Fin n, (∑ b₁' : Fin k → Fin n, ν_t {(b₁', b₂')}) = μ_snd {b₂'} := by
          intro ν_t μ_snd hsnd b₂'
          have hm_eq := congrArg (fun m : Measure (Fin k → Fin n) ↦ m {b₂'}) hsnd
          rw [measure_map_singleton_fintype ν_t Prod.snd b₂', sum_filter_snd_eq] at hm_eq
          exact hm_eq
        let w : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n) → ℝ≥0∞ := fun ⟨b₁, b₂⟩ ↦
          ENNReal.ofReal (H (b₁ 0) (b₂ 0)) *
            (if b₂ 0 = i then ν₁ {(Fin.tail b₁, Fin.tail b₂)}
             else ν₀ {(Fin.tail b₁, Fin.tail b₂)})
        have hsum_b₂ : ∀ b₁ : Fin (k + 1) → Fin n,
            (∑ b₂ : Fin (k + 1) → Fin n, w (b₁, b₂)) = μ_s {b₁} := by
          intro b₁
          rw [← (headTailEquiv n k).sum_comp (fun b₂ ↦ w (b₁, b₂)), Fintype.sum_prod_type]
          have hinner : ∀ y : Fin n,
              (∑ b₂' : Fin k → Fin n, w (b₁, headTailEquiv n k (y, b₂'))) =
                ENNReal.ofReal (H (b₁ 0) y) * μ {Fin.tail b₁} := by
            intro y
            have hw_eq : ∀ b₂' : Fin k → Fin n,
                w (b₁, headTailEquiv n k (y, b₂')) =
                  ENNReal.ofReal (H (b₁ 0) y) *
                    (if y = i then ν₁ {(Fin.tail b₁, b₂')} else ν₀ {(Fin.tail b₁, b₂')}) := by
              intro b₂'
              simp [w, headTailEquiv]
            simp_rw [hw_eq, ← Finset.mul_sum]
            by_cases hy : y = i
            · simp [hy, hrow_tail ν₁ hν₁_fst]
            · simp [hy, hrow_tail ν₀ hν₀_fst]
          simp_rw [hinner, ← Finset.sum_mul,
            ← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ hH_nn (b₁ 0) y, hH_row (b₁ 0)]
          rw [ballBoxMeasure_singleton, ballBoxMeasure_singleton,
            ← Fin.cons_self_tail b₁, ballBoxWeight_cons, Fin.cons_zero, Fin.tail_cons]
        have hsum_w : HasSum w 1 := by
          suffices h : (∑ z : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n), w z) = 1 from
            h ▸ hasSum_fintype w
          rw [Fintype.sum_prod_type]
          simp_rw [hsum_b₂]
          rw [sum_measure_singleton_fintype μ_s, measure_univ]
        let pmf_s : PMF ((Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n)) := ⟨w, hsum_w⟩
        let ν_s : Measure ((Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n)) := pmf_s.toMeasure
        have : IsProbabilityMeasure ν_s := PMF.toMeasure.isProbabilityMeasure pmf_s
        have hν_s_sing : ∀ z, ν_s {z} = w z :=
          fun z ↦ PMF.toMeasure_apply_singleton pmf_s z .of_discrete
        refine ⟨ν_s, inferInstance, ?_, ?_, ?_⟩
        · refine measure_ext_of_singleton_fintype fun b₁ ↦ ?_
          rw [measure_map_singleton_fintype ν_s Prod.fst b₁, sum_filter_fst_eq]
          simp_rw [hν_s_sing]
          exact hsum_b₂ b₁
        · refine measure_ext_of_singleton_fintype fun b₂ ↦ ?_
          rw [measure_map_singleton_fintype ν_s Prod.snd b₂, sum_filter_snd_eq]
          simp_rw [hν_s_sing]
          rw [← (headTailEquiv n k).sum_comp (fun b₁ ↦ w (b₁, b₂)), Fintype.sum_prod_type]
          have hcond_s : ProbabilityTheory.cond μ_s {b | m ≤ boxCount i b} {b₂} =
              if m ≤ boxCount i b₂ then ENNReal.ofReal (μ_s.real {b₂} / Z) else 0 := by
            rw [ProbabilityTheory.cond_apply .of_discrete]
            by_cases hb₂ : m ≤ boxCount i b₂
            · have hinter : ({b | m ≤ boxCount i b} ∩ {b₂}) = {b₂} := by
                ext b
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
                exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hb₂, h⟩⟩
              rw [ite_eq_left hb₂, hinter, ENNReal.ofReal_div_of_pos hZ_pos,
                ofReal_measureReal, ofReal_measureReal, div_eq_mul_inv, mul_comm]
            · have hinter : ({b | m ≤ boxCount i b} ∩ {b₂}) = ∅ := by
                ext b
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
                  Set.mem_empty_iff_false, iff_false, not_and]
                intro h1 h2
                exact hb₂ (h2 ▸ h1)
              rw [ite_eq_right hb₂, hinter, measure_empty, mul_zero]
          rw [hcond_s]
          by_cases hy : b₂ 0 = i
          · have hw_i : ∀ (x : Fin n) (b₁' : Fin k → Fin n),
                w (headTailEquiv n k (x, b₁'), b₂) =
                  ENNReal.ofReal (H x i) * ν₁ {(b₁', Fin.tail b₂)} := by
              intro x b₁'
              simp [w, headTailEquiv, hy]
            simp_rw [hw_i, ← Finset.mul_sum, ← Finset.sum_mul,
              ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hH_nn x i, hH_col_i]
            rw [hcol_tail ν₁ _ hν₁_snd (Fin.tail b₂),
              ProbabilityTheory.cond_apply .of_discrete]
            have hiff : (m ≤ boxCount i b₂) ↔ m - 1 ≤ boxCount i (Fin.tail b₂) := by
              conv_lhs => rw [← Fin.cons_self_tail b₂, boxCount_cons, hy, ite_eq_left rfl]
              omega
            by_cases htail : m - 1 ≤ boxCount i (Fin.tail b₂)
            · have hinter : ({b' | m - 1 ≤ boxCount i b'} ∩ {Fin.tail b₂}) = {Fin.tail b₂} := by
                ext b'
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
                exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ htail, h⟩⟩
              rw [ite_eq_left (hiff.mpr htail), hinter,
                ← ofReal_measureReal (μ := μ) (s := {Fin.tail b₂}),
                ← ofReal_measureReal (μ := μ) (s := {b' | m - 1 ≤ boxCount i b'}),
                ← ENNReal.ofReal_inv_of_pos hβ₁_pos,
                ← ENNReal.ofReal_mul (inv_nonneg.mpr hβ₁_pos.le),
                ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (hp_nn i) hβ₁_nn) hZ_pos.le)]
              congr 1
              have hμs_b₂ : μ_s.real {b₂} = p i * μ.real {Fin.tail b₂} := by
                conv_lhs => rw [← Fin.cons_self_tail b₂]
                rw [ballBoxMeasure_real_singleton, ballBoxRealWeight_cons, hy,
                  ballBoxMeasure_real_singleton]
              rw [hμs_b₂]
              field_simp [hβ₁_pos.ne', hZ_pos.ne']
            · have hinter : ({b' | m - 1 ≤ boxCount i b'} ∩ {Fin.tail b₂}) = ∅ := by
                ext b'
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
                  Set.mem_empty_iff_false, iff_false, not_and]
                intro h1 h2
                exact htail (h2 ▸ h1)
              rw [ite_eq_right (mt hiff.mp htail), hinter, measure_empty, mul_zero, mul_zero]
          · have hb₂0 : b₂ 0 ≠ i := hy
            set j := b₂ 0
            have hj : j ≠ i := hy
            have hw_j : ∀ (x : Fin n) (b₁' : Fin k → Fin n),
                w (headTailEquiv n k (x, b₁'), b₂) =
                  ENNReal.ofReal (H x j) * ν₀ {(b₁', Fin.tail b₂)} := by
              intro x b₁'
              simp [w, headTailEquiv, hb₂0, j]
            simp_rw [hw_j, ← Finset.mul_sum, ← Finset.sum_mul,
              ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hH_nn x j, hH_col_ne j hj]
            have hiff : (m ≤ boxCount i b₂) ↔ m ≤ boxCount i (Fin.tail b₂) := by
              conv_lhs => rw [← Fin.cons_self_tail b₂, boxCount_cons, ite_eq_right hj, zero_add]
            by_cases h₀ : 0 < β₀
            · have hν₀_snd : ν₀.map Prod.snd =
                  ProbabilityTheory.cond μ {b' | m ≤ boxCount i b'} := by
                simpa [ν₀, h₀] using (ih m h₀).choose_spec.2.2.1
              rw [hcol_tail ν₀ _ hν₀_snd (Fin.tail b₂),
                ProbabilityTheory.cond_apply .of_discrete]
              by_cases htail : m ≤ boxCount i (Fin.tail b₂)
              · have hinter : ({b' | m ≤ boxCount i b'} ∩ {Fin.tail b₂}) = {Fin.tail b₂} := by
                  ext b'
                  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
                  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ htail, h⟩⟩
                rw [ite_eq_left (hiff.mpr htail), hinter,
                  ← ofReal_measureReal (μ := μ) (s := {Fin.tail b₂}),
                  ← ofReal_measureReal (μ := μ) (s := {b' | m ≤ boxCount i b'}),
                  ← ENNReal.ofReal_inv_of_pos h₀,
                  ← ENNReal.ofReal_mul (inv_nonneg.mpr h₀.le),
                  ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (hp_nn j) hβ₀_nn) hZ_pos.le)]
                congr 1
                have hμs_b₂ : μ_s.real {b₂} = p j * μ.real {Fin.tail b₂} := by
                  conv_lhs => rw [← Fin.cons_self_tail b₂]
                  rw [ballBoxMeasure_real_singleton, ballBoxRealWeight_cons,
                    ballBoxMeasure_real_singleton]
                rw [hμs_b₂]
                field_simp [h₀.ne', hZ_pos.ne']
              · have hinter : ({b' | m ≤ boxCount i b'} ∩ {Fin.tail b₂}) = ∅ := by
                  ext b'
                  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
                    Set.mem_empty_iff_false, iff_false, not_and]
                  intro h1 h2
                  exact htail (h2 ▸ h1)
                rw [ite_eq_right (mt hiff.mp htail), hinter, measure_empty, mul_zero, mul_zero]
            · have hβ₀_zero : β₀ = 0 := le_antisymm (not_lt.mp h₀) hβ₀_nn
              rw [hβ₀_zero, mul_zero, zero_div, ENNReal.ofReal_zero, zero_mul]
              by_cases hb₂ : m ≤ boxCount i b₂
              · have htail : m ≤ boxCount i (Fin.tail b₂) := hiff.mp hb₂
                have hle_t : μ.real {Fin.tail b₂} ≤ β₀ :=
                  measureReal_mono (Set.singleton_subset_iff.mpr htail) (measure_ne_top μ _)
                have ht0 : μ.real {Fin.tail b₂} = 0 :=
                  le_antisymm (hle_t.trans (le_of_eq hβ₀_zero)) measureReal_nonneg
                have hμs0 : μ_s.real {b₂} = 0 := by
                  conv_lhs => rw [← Fin.cons_self_tail b₂]
                  rw [ballBoxMeasure_real_singleton, ballBoxRealWeight_cons,
                    ← ballBoxMeasure_real_singleton p hp_nn hp_sum k, ht0, mul_zero]
                rw [ite_eq_left hb₂, hμs0, zero_div, ENNReal.ofReal_zero]
              · rw [ite_eq_right hb₂]
        · rw [eventually_iff, MeasureTheory.mem_ae_iff]
          have hbad_sub :
              {z : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n) |
                ¬ ∀ j : Fin n, j ≠ i → boxCount j z.2 ≤ boxCount j z.1} ⊆
              {z | ν_s {z} = 0} := by
            intro ⟨b₁, b₂⟩ hnot
            by_contra hne0
            rw [Set.mem_ofPred_eq, hν_s_sing] at hne0
            have hH_ne0 : ENNReal.ofReal (H (b₁ 0) (b₂ 0)) ≠ 0 := left_ne_zero_of_mul hne0
            have htail_ne0 :
                (if b₂ 0 = i then ν₁ {(Fin.tail b₁, Fin.tail b₂)}
                 else ν₀ {(Fin.tail b₁, Fin.tail b₂)}) ≠ 0 := right_ne_zero_of_mul hne0
            have hhead_le : ∀ j : Fin n, j ≠ i →
                (if b₂ 0 = j then 1 else 0) ≤ (if b₁ 0 = j then 1 else 0) := by
              intro j hj
              by_cases hb₂j : b₂ 0 = j
              · have hb₂_ne_i : b₂ 0 ≠ i := hb₂j ▸ hj
                have hb₁_eq : b₁ 0 = b₂ 0 := by
                  by_contra hneq
                  have hH0 : H (b₁ 0) (b₂ 0) = 0 := by
                    by_cases hb₁i : b₁ 0 = i
                    · simp [H, hb₁i, hb₂_ne_i]
                    · simp [H, hb₁i, hb₂_ne_i, Ne.symm hneq]
                  exact hH_ne0 (by simp [hH0])
                simp [hb₂j, hb₁_eq]
              · simp [hb₂j]
            have htail_le : ∀ j : Fin n, j ≠ i →
                boxCount j (Fin.tail b₂) ≤ boxCount j (Fin.tail b₁) := by
              by_cases hb₂i : b₂ 0 = i
              · simp only [hb₂i, ↓reduceIte] at htail_ne0
                by_contra hnot_t
                have hnull : ν₁ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.2 ≤ boxCount j u.1} = 0 :=
                  MeasureTheory.mem_ae_iff.mp hν₁_mono
                have hle_null : ν₁ {(Fin.tail b₁, Fin.tail b₂)} ≤
                    ν₁ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.2 ≤ boxCount j u.1} :=
                  measure_mono (Set.singleton_subset_iff.mpr hnot_t)
                exact htail_ne0 (le_antisymm (hle_null.trans (le_of_eq hnull)) zero_le)
              · simp only [hb₂i, ↓reduceIte] at htail_ne0
                by_contra hnot_t
                have hnull : ν₀ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.2 ≤ boxCount j u.1} = 0 :=
                  MeasureTheory.mem_ae_iff.mp hν₀_mono
                have hle_null : ν₀ {(Fin.tail b₁, Fin.tail b₂)} ≤
                    ν₀ {u | ¬ ∀ j : Fin n, j ≠ i → boxCount j u.2 ≤ boxCount j u.1} :=
                  measure_mono (Set.singleton_subset_iff.mpr hnot_t)
                exact htail_ne0 (le_antisymm (hle_null.trans (le_of_eq hnull)) zero_le)
            apply hnot
            intro j hj
            have hc1 : boxCount j b₁ = (if b₁ 0 = j then 1 else 0) + boxCount j (Fin.tail b₁) := by
              conv_lhs => rw [← Fin.cons_self_tail b₁, boxCount_cons]
            have hc2 : boxCount j b₂ = (if b₂ 0 = j then 1 else 0) + boxCount j (Fin.tail b₂) := by
              conv_lhs => rw [← Fin.cons_self_tail b₂, boxCount_cons]
            rw [hc1, hc2]
            exact Nat.add_le_add (hhead_le j hj) (htail_le j hj)
          have hzero_set : ν_s {z | ν_s {z} = 0} = 0 := by
            have hunion : ({z : (Fin (k + 1) → Fin n) × (Fin (k + 1) → Fin n) | ν_s {z} = 0}) =
                ⋃ z ∈ Finset.univ.filter (fun z ↦ ν_s {z} = 0), {z} := by
              ext z
              simp
            rw [hunion, measure_biUnion_finset]
            · refine Finset.sum_eq_zero fun z hz ↦ ?_
              exact (Finset.mem_filter.mp hz).2
            · intro x _ y _ hxy
              exact Set.disjoint_singleton.mpr hxy
            · intro _ _
              exact .of_discrete
          exact le_antisymm ((measure_mono hbad_sub).trans (le_of_eq hzero_set)) zero_le

/-! ### Part 5: Remark 4.17 Theorems & Printed Claim Refutation -/

/-- **Remark 4.17 (at-most-$m$ balls)** (`SteinIntro.tex:2594-2598`): for $k$ balls placed
independently into $n$ boxes with probabilities $(p_1, \dots, p_n)$, if $W$ counts boxes containing
at most $m$ balls and $\lambda = \mathbb{E}[W] > 0$, then Theorem 4.19 yields
$$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
  \min\{1, \lambda\}\left(1 - \frac{\operatorname{Var}(W)}{\lambda}\right).$$ -/
private lemma transfer_ballBox_coupling_space
    {n k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {μ : Measure (Fin k → Fin n)} [IsProbabilityMeasure μ]
    {B : Fin k → Ω → Fin n} (hBM : Measurable (fun ω t ↦ B t ω))
    (hmap_B : P.map (fun ω t ↦ B t ω) = μ)
    {X_μ : Fin n → (Fin k → Fin n) → ℕ}
    (hex : ∀ i : Fin n, 0 < μ.real {b | X_μ i b = 1} →
      ∃ ν : Measure ((Fin k → Fin n) × (Fin k → Fin n)), IsProbabilityMeasure ν ∧
        ν.map Prod.fst = μ ∧
        ν.map Prod.snd = ProbabilityTheory.cond μ {b | X_μ i b = 1} ∧
        (∀ᵐ z ∂ν, ∀ j : Fin n, j ≠ i → X_μ j z.2 ≤ X_μ j z.1)) :
    let X_P : Fin n → Ω → ℕ := fun i ω ↦ X_μ i (fun t ↦ B t ω)
    ∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X_P i ω) ∧
      (∀ i : Fin n, 0 < P.real {ω | X_P i ω = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond P {ω | X_P i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X_P j.1 ω)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc) := by
  intro X_P
  obtain ⟨Ωc, mΩc, Pc, hPc, Xc, Yc, hXc_m, hYc_m, hlaw_X, hlaw_Y, hle⟩ :=
    exists_fintype_decreasing_coupling_space μ hex
  refine ⟨Ωc, mΩc, Pc, hPc, Xc, Yc, hXc_m, hYc_m, ?_, ?_, hle⟩
  · have hcomp : (fun ω i ↦ X_P i ω) = (fun b i ↦ X_μ i b) ∘ (fun ω t ↦ B t ω) := rfl
    rw [hcomp, ← Measure.map_map Measurable.of_discrete hBM, hmap_B, hlaw_X]
  · intro i hi_pos
    have hp_eq : P.real {ω | X_P i ω = 1} = μ.real {b | X_μ i b = 1} := by
      change P.real ((fun ω t ↦ B t ω) ⁻¹' {b | X_μ i b = 1}) = μ.real {b | X_μ i b = 1}
      rw [← map_measureReal_apply hBM .of_discrete, hmap_B]
    rw [hp_eq] at hi_pos
    rw [hlaw_Y i hi_pos]
    refine Measure.ext fun E hE ↦ ?_
    let g : (Fin k → Fin n) → ({j : Fin n // j ≠ i} → ℕ) := fun b j ↦ X_μ j.1 b
    have hg : Measurable g := .of_discrete
    change (Measure.map g (ProbabilityTheory.cond μ {b | X_μ i b = 1})) E =
      (Measure.map (g ∘ fun ω t ↦ B t ω) (ProbabilityTheory.cond P {ω | X_P i ω = 1})) E
    have hXP_meas : MeasurableSet {ω | X_P i ω = 1} :=
      hBM (show MeasurableSet {b | X_μ i b = 1} from .of_discrete)
    rw [Measure.map_apply hg hE, Measure.map_apply (hg.comp hBM) hE,
      ProbabilityTheory.cond_apply .of_discrete,
      ProbabilityTheory.cond_apply hXP_meas]
    have hm1 : P {ω | X_P i ω = 1} = μ {b | X_μ i b = 1} := by
      change P ((fun ω t ↦ B t ω) ⁻¹' {b | X_μ i b = 1}) = μ {b | X_μ i b = 1}
      rw [← hmap_B, Measure.map_apply hBM .of_discrete]
    have hm2 : P ({ω | X_P i ω = 1} ∩ (g ∘ fun ω t ↦ B t ω) ⁻¹' E) =
        μ ({b | X_μ i b = 1} ∩ g ⁻¹' E) := by
      change P ((fun ω t ↦ B t ω) ⁻¹' {b | X_μ i b = 1} ∩
        ((fun ω t ↦ B t ω) ⁻¹' (g ⁻¹' E))) = _
      rw [← Set.preimage_inter, ← hmap_B, Measure.map_apply hBM .of_discrete]
    rw [hm1, hm2]

theorem rem4_17_atMost
    {n k m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1)
    (hB_meas : ∀ t : Fin k, Measurable (B t))
    (hB_indep : ProbabilityTheory.iIndepFun B P)
    (hB_prob : ∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) :
    let X : Fin n → Ω → ℕ := fun i ω ↦
      if ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card ≤ m then 1 else 0
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond P {ω | X i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc)) ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ))) := by
  intro X_P W hr hmean hZ_meas hZ_law
  let μ := ballBoxMeasure p hp_nn hp_sum k
  have hmap_B : P.map (fun ω t ↦ B t ω) = μ :=
    map_pi_eq_ballBoxMeasure P hp_nn hp_sum hB_meas hB_indep hB_prob
  have hBM : Measurable (fun ω t ↦ B t ω) := Measurable.of_eval hB_meas
  let X : Fin n → (Fin k → Fin n) → ℕ := fun i b ↦ if boxCount i b ≤ m then 1 else 0
  let W_μ : (Fin k → Fin n) → ℕ := fun b ↦ ∑ i : Fin n, X i b
  have hW_comp : W = W_μ ∘ (fun ω t ↦ B t ω) := rfl
  have hmap_W : P.map W = μ.map W_μ := by
    rw [hW_comp, ← Measure.map_map Measurable.of_discrete hBM, hmap_B]
  have hvar_W : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      ProbabilityTheory.variance (fun b ↦ (W_μ b : ℝ)) μ := by
    have h := ProbabilityTheory.variance_map (μ := P)
      (X := fun b : Fin k → Fin n ↦ (W_μ b : ℝ)) (Y := fun ω t ↦ B t ω)
      Measurable.of_discrete.aemeasurable hBM.aemeasurable
    rw [hmap_B] at h
    exact h.symm
  have hX_zo : ∀ i : Fin n, ∀ b : Fin k → Fin n, X i b = 0 ∨ X i b = 1 := by
    intro i b
    by_cases h : boxCount i b ≤ m <;> simp [X, h]
  have hlam : (r : ℝ) = ∑ i : Fin n, μ.real {b | X i b = 1} := by
    have hint_eq : ∫ ω, (W ω : ℝ) ∂P = ∫ b, (W_μ b : ℝ) ∂μ := by
      rw [← hmap_B, integral_map hBM.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
      rfl
    rw [hmean, hint_eq]
    have hcast : (fun b : Fin k → Fin n ↦ (W_μ b : ℝ)) = fun b ↦ ∑ i : Fin n, (X i b : ℝ) := by
      ext b
      simp [W_μ]
    rw [hcast, integral_finsetSum Finset.univ fun i _ ↦
      integrable_nat_zero_one μ .of_discrete (Eventually.of_forall (hX_zo i))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact integral_nat_zero_one_eq_measureReal μ .of_discrete (Eventually.of_forall (hX_zo i))
  have hex : ∀ i : Fin n, 0 < μ.real {b | X i b = 1} →
      ∃ ν : Measure ((Fin k → Fin n) × (Fin k → Fin n)), IsProbabilityMeasure ν ∧
        ν.map Prod.fst = μ ∧
        ν.map Prod.snd = ProbabilityTheory.cond μ {b | X i b = 1} ∧
        (∀ᵐ z ∂ν, ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1) := by
    intro i hi_pos
    have hset : ({b : Fin k → Fin n | X i b = 1}) = {b | boxCount i b ≤ m} := by
      ext b
      by_cases h : boxCount i b ≤ m <;> simp [X, h]
    rw [hset] at hi_pos ⊢
    obtain ⟨ν, hprob, hfst, hsnd, hmono⟩ :=
      exists_ballBox_atMost_coupling hp_nn hp_sum i k m hi_pos
    refine ⟨ν, hprob, hfst, hsnd, ?_⟩
    filter_upwards [hmono] with z hz j hj
    have hle := hz j hj
    dsimp [X]
    split_ifs with h2 h1
    · exact le_rfl
    · exact False.elim (h1 (hle.trans h2))
    · exact Nat.zero_le _
    · exact le_rfl
  refine ⟨transfer_ballBox_coupling_space P hBM hmap_B hex, ?_⟩
  rw [hmap_W, hvar_W]
  exact tvDist_poisson_le_of_fintype_couplings μ P' hX_zo hr hlam hex hZ_meas hZ_law

/-- **Remark 4.17, corrected (at-least-$m$ balls)** (`SteinIntro.tex:2600`; `ISSUE-REM-4.17`):
for $k$ balls placed independently into $n$ boxes with probabilities $(p_1, \dots, p_n)$, if
$m \ge 1$, $W$ counts boxes containing at least $m$ balls, and $\lambda = \mathbb{E}[W] > 0$, then
a decreasing conditional coupling exists and **Theorem 4.19** (`\ref{thm125}`, correcting the
printed `\ref{thm122}`) yields
$$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le
  \min\{1, \lambda\}\left(1 - \frac{\operatorname{Var}(W)}{\lambda}\right).$$ -/
theorem rem4_17_atLeast_corrected
    {n k m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ}
    (_hm : 1 ≤ m)
    (hp_nn : ∀ i : Fin n, 0 ≤ p i)
    (hp_sum : ∑ i : Fin n, p i = 1)
    (hB_meas : ∀ t : Fin k, Measurable (B t))
    (hB_indep : ProbabilityTheory.iIndepFun B P)
    (hB_prob : ∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) :
    let X : Fin n → Ω → ℕ := fun i ω ↦
      if m ≤ ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card then 1 else 0
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond P {ω | X i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc)) ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ))) := by
  intro X_P W hr hmean hZ_meas hZ_law
  let μ := ballBoxMeasure p hp_nn hp_sum k
  have hmap_B : P.map (fun ω t ↦ B t ω) = μ :=
    map_pi_eq_ballBoxMeasure P hp_nn hp_sum hB_meas hB_indep hB_prob
  have hBM : Measurable (fun ω t ↦ B t ω) := Measurable.of_eval hB_meas
  let X : Fin n → (Fin k → Fin n) → ℕ := fun i b ↦ if m ≤ boxCount i b then 1 else 0
  let W_μ : (Fin k → Fin n) → ℕ := fun b ↦ ∑ i : Fin n, X i b
  have hW_comp : W = W_μ ∘ (fun ω t ↦ B t ω) := rfl
  have hmap_W : P.map W = μ.map W_μ := by
    rw [hW_comp, ← Measure.map_map Measurable.of_discrete hBM, hmap_B]
  have hvar_W : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      ProbabilityTheory.variance (fun b ↦ (W_μ b : ℝ)) μ := by
    have h := ProbabilityTheory.variance_map (μ := P)
      (X := fun b : Fin k → Fin n ↦ (W_μ b : ℝ)) (Y := fun ω t ↦ B t ω)
      Measurable.of_discrete.aemeasurable hBM.aemeasurable
    rw [hmap_B] at h
    exact h.symm
  have hX_zo : ∀ i : Fin n, ∀ b : Fin k → Fin n, X i b = 0 ∨ X i b = 1 := by
    intro i b
    by_cases h : m ≤ boxCount i b <;> simp [X, h]
  have hlam : (r : ℝ) = ∑ i : Fin n, μ.real {b | X i b = 1} := by
    have hint_eq : ∫ ω, (W ω : ℝ) ∂P = ∫ b, (W_μ b : ℝ) ∂μ := by
      rw [← hmap_B, integral_map hBM.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
      rfl
    rw [hmean, hint_eq]
    have hcast : (fun b : Fin k → Fin n ↦ (W_μ b : ℝ)) = fun b ↦ ∑ i : Fin n, (X i b : ℝ) := by
      ext b
      simp [W_μ]
    rw [hcast, integral_finsetSum Finset.univ fun i _ ↦
      integrable_nat_zero_one μ .of_discrete (Eventually.of_forall (hX_zo i))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact integral_nat_zero_one_eq_measureReal μ .of_discrete (Eventually.of_forall (hX_zo i))
  have hex : ∀ i : Fin n, 0 < μ.real {b | X i b = 1} →
      ∃ ν : Measure ((Fin k → Fin n) × (Fin k → Fin n)), IsProbabilityMeasure ν ∧
        ν.map Prod.fst = μ ∧
        ν.map Prod.snd = ProbabilityTheory.cond μ {b | X i b = 1} ∧
        (∀ᵐ z ∂ν, ∀ j : Fin n, j ≠ i → X j z.2 ≤ X j z.1) := by
    intro i hi_pos
    have hset : ({b : Fin k → Fin n | X i b = 1}) = {b | m ≤ boxCount i b} := by
      ext b
      by_cases h : m ≤ boxCount i b <;> simp [X, h]
    rw [hset] at hi_pos ⊢
    obtain ⟨ν, hprob, hfst, hsnd, hmono⟩ :=
      exists_ballBox_atLeast_coupling hp_nn hp_sum i k m hi_pos
    refine ⟨ν, hprob, hfst, hsnd, ?_⟩
    filter_upwards [hmono] with z hz j hj
    have hle := hz j hj
    dsimp [X]
    split_ifs with h2 h1
    · exact le_rfl
    · exact False.elim (h1 (h2.trans hle))
    · exact Nat.zero_le _
    · exact le_rfl
  refine ⟨transfer_ballBox_coupling_space P hBM hmap_B hex, ?_⟩
  rw [hmap_W, hvar_W]
  exact tvDist_poisson_le_of_fintype_couplings μ P' hX_zo hr hlam hex hZ_meas hZ_law

/-- **Refutation of the printed Theorem 4.14 (`\ref{thm122}`) claim in Remark 4.17**
(`SteinIntro.tex:2600`; `ISSUE-REM-4.17`): at $n = 2, k = 1, m = 1, p = (1/2, 1/2)$, $W \equiv 1$
has $\lambda = 1$, $\operatorname{Var}(W) = 0$, and $q_1 = q_2 = 1/2$, so Theorem 4.14's bound
evaluates to $0 < e^{-1} \le d_{\mathrm{TV}}(\delta_1, \mathrm{Po}(1))$ (and at $n = 3, k = 1,
m = 1, p = (1/3, 1/3, 1/3)$ it evaluates to $-1/3 < 0$). -/
theorem not_rem4_17_atLeast_printed :
    ¬ (∀ {n k m : ℕ}
        {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
        1 ≤ m →
        (∀ i : Fin n, 0 ≤ p i) →
        ∑ i : Fin n, p i = 1 →
        (∀ t : Fin k, Measurable (B t)) →
        ProbabilityTheory.iIndepFun B P →
        (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
        let X : Fin n → Ω → ℕ := fun i ω ↦
          if m ≤ ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card then 1 else 0
        let q : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
        let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
        0 < r →
        (r : ℝ) = ∑ i : Fin n, q i →
        AEMeasurable Z P' →
        P'.map Z = poissonLaw r →
        tvDist (P.map W) (P'.map Z) ≤
          ENNReal.ofReal
            (min 1 (r : ℝ)⁻¹ *
              (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
                2 * ∑ i : Fin n, q i ^ 2))) := by
  intro h_printed
  let p : Fin 2 → ℝ := fun _ ↦ 1 / 2
  have hp_nn : ∀ i : Fin 2, 0 ≤ p i := fun _ ↦ by norm_num [p]
  have hp_sum : ∑ i : Fin 2, p i = 1 := by
    rw [Fin.sum_univ_two]
    norm_num [p]
  let μ₀ : Measure (Fin 2) := (@PMF.uniformOfFintype (Fin 2) inferInstance ⟨0⟩).toMeasure
  let P : Measure (PUnit × Fin 2) := (Measure.dirac PUnit.unit).prod μ₀
  let P' : Measure (PUnit × ℕ) := (Measure.dirac PUnit.unit).prod (poissonLaw 1)
  let B : Fin 1 → PUnit × Fin 2 → Fin 2 := fun _ ω ↦ ω.2
  have hB_meas : ∀ t : Fin 1, Measurable (B t) := fun _ ↦ measurable_snd
  have hB_indep : ProbabilityTheory.iIndepFun B P := by
    rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S hS _
    rcases Finset.eq_empty_or_nonempty S with rfl | ⟨t₀, ht₀⟩
    · simp
    · have hS_eq : S = {0} := by
        ext t
        rw [Subsingleton.elim t 0]
        rw [Subsingleton.elim t₀ 0] at ht₀
        simp [ht₀]
      subst hS_eq
      simp
  have hP_snd : P.map Prod.snd = μ₀ := Measure.snd_prod
  have hB_prob : ∀ t : Fin 1, ∀ i : Fin 2, P.real {ω | B t ω = i} = p i := by
    intro t i
    change P.real (Prod.snd ⁻¹' {i}) = p i
    rw [← map_measureReal_apply measurable_snd .of_discrete, hP_snd]
    simp only [μ₀, measureReal_def, PMF.toMeasure_apply_singleton _ _ .of_discrete,
      PMF.uniformOfFintype_apply, Fintype.card_fin, p]
    norm_num
  let X : Fin 2 → PUnit × Fin 2 → ℕ := fun i ω ↦
    if 1 ≤ ((Finset.univ : Finset (Fin 1)).filter fun t ↦ B t ω = i).card then 1 else 0
  let q : Fin 2 → ℝ := fun i ↦ P.real {ω | X i ω = 1}
  let W : PUnit × Fin 2 → ℕ := fun ω ↦ ∑ i : Fin 2, X i ω
  have hq : ∀ i : Fin 2, q i = 1 / 2 := by
    intro i
    have hset : {ω : PUnit × Fin 2 | X i ω = 1} = Prod.snd ⁻¹' {i} := by
      ext ⟨_, b⟩
      by_cases hb : b = i <;> simp [X, B, hb]
    dsimp only [q]
    rw [hset, ← map_measureReal_apply measurable_snd .of_discrete, hP_snd]
    simp only [μ₀, measureReal_def, PMF.toMeasure_apply_singleton _ _ .of_discrete,
      PMF.uniformOfFintype_apply, Fintype.card_fin]
    norm_num
  have hr_eq : ((1 : ℝ≥0) : ℝ) = ∑ i : Fin 2, q i := by
    rw [Fin.sum_univ_two, hq 0, hq 1]
    norm_num
  have hW_const : W = fun _ : PUnit × Fin 2 ↦ 1 := by
    funext ⟨_, b⟩
    dsimp only [W]
    rw [Fin.sum_univ_two]
    fin_cases b <;> simp [X, B]
  have hP'_snd : P'.map Prod.snd = poissonLaw 1 := Measure.snd_prod
  have h_ineq := h_printed (n := 2) (k := 1) (m := 1) P P'
    (p := p) (B := B) (r := 1) (Z := Prod.snd) le_rfl hp_nn hp_sum hB_meas hB_indep hB_prob
    zero_lt_one hr_eq measurable_snd.aemeasurable hP'_snd
  change tvDist (P.map W) (P'.map Prod.snd) ≤
    ENNReal.ofReal
      (min 1 ((1 : ℝ≥0) : ℝ)⁻¹ *
        (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - ((1 : ℝ≥0) : ℝ) +
          2 * ∑ i : Fin 2, q i ^ 2)) at h_ineq
  have hvar0 : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P = 0 := by
    have hW_real : (fun ω ↦ (W ω : ℝ)) = fun _ ↦ (1 : ℝ) := by
      funext ω
      simp [hW_const]
    rw [hW_real, ProbabilityTheory.variance_eq_sub (memLp_const (1 : ℝ))]
    simp
  have hrhs0 : min 1 ((1 : ℝ≥0) : ℝ)⁻¹ *
      (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - ((1 : ℝ≥0) : ℝ) +
        2 * ∑ i : Fin 2, q i ^ 2) = 0 := by
    rw [hvar0, Fin.sum_univ_two, hq 0, hq 1]
    norm_num
  rw [hrhs0, ENNReal.ofReal_zero, hP'_snd] at h_ineq
  have : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff (by rw [hW_const]; exact aemeasurable_const)).mpr
      inferInstance
  have h_lb : ENNReal.ofReal |(P.map W).real {0} - (poissonLaw 1).real {0}| ≤
      tvDist (P.map W) (poissonLaw 1) := by
    rw [tvDist_eq_iSup]
    exact le_iSup₂
      (f := fun (A : Set ℕ) (_ : MeasurableSet A) ↦
        ENNReal.ofReal |(P.map W).real A - (poissonLaw 1).real A|)
      ({0} : Set ℕ) (measurableSet_singleton 0)
  have hW_zero : (P.map W).real {0} = 0 := by
    rw [hW_const, map_measureReal_apply measurable_const (measurableSet_singleton 0)]
    simp
  have hP'_zero : (poissonLaw 1).real {0} = Real.exp (-1) := by
    simpa [poissonLaw] using ProbabilityTheory.poissonMeasure_real_singleton 1 0
  rw [hW_zero, hP'_zero, zero_sub, abs_neg, abs_of_pos (Real.exp_pos (-1))] at h_lb
  exact not_lt_of_ge (h_lb.trans h_ineq) (ENNReal.ofReal_pos.mpr (Real.exp_pos (-1)))

/-! ### Part 6: Empty-Box Mean, Variance, and TV Bound (`m = 0`) -/

/-- Number of empty boxes (`boxCount i b = 0`, i.e. `∀ t, b t ≠ i`) under `b : Fin k → Fin n`. -/
def emptyBoxCount {n k : ℕ} (b : Fin k → Fin n) : ℕ :=
  ∑ i : Fin n, if ∀ t : Fin k, b t ≠ i then 1 else 0

lemma emptyBoxCount_eq_atMost_zero {n k : ℕ} (b : Fin k → Fin n) :
    emptyBoxCount b = ∑ i : Fin n, if boxCount i b ≤ 0 then 1 else 0 := by
  unfold emptyBoxCount boxCount
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hiff : (∀ t : Fin k, b t ≠ i) ↔
      ((Finset.univ : Finset (Fin k)).filter fun t ↦ b t = i).card ≤ 0 := by
    simp [Finset.filter_eq_empty_iff]
  by_cases h : ∀ t : Fin k, b t ≠ i
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]

lemma ballBox_prob_avoid_one {n k : ℕ} {p : Fin n → ℝ}
    (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1) (i : Fin n) :
    (ballBoxMeasure p hp_nn hp_sum k).real {b | ∀ t : Fin k, b t ≠ i} = (1 - p i) ^ k := by
  classical
  rw [ballBoxMeasure_real_setOf, Finset.sum_filter]
  have hprod :
      (∑ b : Fin k → Fin n,
        if ∀ t : Fin k, b t ≠ i then ballBoxRealWeight p k b else 0) =
      ∏ _t : Fin k, ∑ x : Fin n, if x ≠ i then p x else 0 := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    by_cases hb : ∀ t : Fin k, b t ≠ i
    · rw [ite_eq_left hb]
      unfold ballBoxRealWeight
      refine Finset.prod_congr rfl fun t _ ↦ ?_
      rw [ite_eq_left (hb t)]
    · rw [ite_eq_right hb]
      rcases not_forall.mp hb with ⟨t₀, ht₀⟩
      rw [not_ne_iff] at ht₀
      refine (Finset.prod_eq_zero (Finset.mem_univ t₀) ?_).symm
      simp [ht₀]
  rw [hprod]
  have hsum_one : (∑ x : Fin n, if x ≠ i then p x else 0) = 1 - p i := by
    rw [← Finset.sum_filter]
    have hfilt : (Finset.univ.filter fun x : Fin n ↦ x ≠ i) = Finset.univ.erase i := by
      ext x
      simp
    rw [hfilt, sum_erase_prob hp_sum i]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hsum_one]

lemma ballBox_prob_avoid_two {n k : ℕ} {p : Fin n → ℝ}
    (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1)
    {i j : Fin n} (hij : j ≠ i) :
    (ballBoxMeasure p hp_nn hp_sum k).real {b | (∀ t : Fin k, b t ≠ i) ∧ (∀ t : Fin k, b t ≠ j)} =
      (1 - p i - p j) ^ k := by
  classical
  rw [ballBoxMeasure_real_setOf, Finset.sum_filter]
  have hprod :
      (∑ b : Fin k → Fin n,
        if (∀ t : Fin k, b t ≠ i) ∧ (∀ t : Fin k, b t ≠ j) then ballBoxRealWeight p k b else 0) =
      ∏ _t : Fin k, ∑ x : Fin n, if x ≠ i ∧ x ≠ j then p x else 0 := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    by_cases hb : (∀ t : Fin k, b t ≠ i) ∧ (∀ t : Fin k, b t ≠ j)
    · rw [ite_eq_left hb]
      unfold ballBoxRealWeight
      refine Finset.prod_congr rfl fun t _ ↦ ?_
      rw [ite_eq_left ⟨hb.1 t, hb.2 t⟩]
    · rw [ite_eq_right hb]
      have hex : ∃ t₀ : Fin k, ¬ (b t₀ ≠ i ∧ b t₀ ≠ j) := by
        by_contra hall
        exact hb ⟨fun t ↦ (not_exists.mp hall t |> not_not.mp).1,
          fun t ↦ (not_exists.mp hall t |> not_not.mp).2⟩
      rcases hex with ⟨t₀, ht₀⟩
      refine (Finset.prod_eq_zero (Finset.mem_univ t₀) ?_).symm
      exact ite_eq_right ht₀
  rw [hprod]
  have hsum_two : (∑ x : Fin n, if x ≠ i ∧ x ≠ j then p x else 0) = 1 - p i - p j := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩
    rw [← Finset.add_sum_erase (Finset.univ.erase i) _ hj_mem]
    have h1 : (if i ≠ i ∧ i ≠ j then p i else 0) = 0 := by simp
    have h2 : (if j ≠ i ∧ j ≠ j then p j else 0) = 0 := by simp
    have hrest : ∀ x ∈ (Finset.univ.erase i).erase j,
        (if x ≠ i ∧ x ≠ j then p x else 0) = p x := by
      intro x hx
      have hxj : x ≠ j := (Finset.mem_erase.mp hx).1
      have hxi : x ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      simp [hxi, hxj]
    rw [h1, h2, zero_add, zero_add, Finset.sum_congr rfl hrest]
    have hs1 := Finset.sum_erase_add (Finset.univ.erase i) p hj_mem
    have hs2 := sum_erase_prob hp_sum i
    linarith
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hsum_two]

/-- Exact mean $\sum_{i=1}^n (1 - p_i)^k$ of the empty-box count under `ballBoxMeasure`. -/
theorem ballBox_empty_mean {n k : ℕ} {p : Fin n → ℝ}
    (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1) :
    ∫ b, (emptyBoxCount b : ℝ) ∂(ballBoxMeasure p hp_nn hp_sum k) =
      ∑ i : Fin n, (1 - p i) ^ k := by
  let μ := ballBoxMeasure p hp_nn hp_sum k
  let X : Fin n → (Fin k → Fin n) → ℕ := fun i b ↦ if ∀ t : Fin k, b t ≠ i then 1 else 0
  have hX_zo : ∀ i b, X i b = 0 ∨ X i b = 1 := by
    intro i b
    by_cases h : ∀ t : Fin k, b t ≠ i <;> simp [X, h]
  have hcast : (fun b ↦ (emptyBoxCount b : ℝ)) = fun b ↦ ∑ i : Fin n, (X i b : ℝ) := by
    ext b
    simp [emptyBoxCount, X]
  rw [hcast, integral_finsetSum Finset.univ fun i _ ↦
    integrable_nat_zero_one μ .of_discrete (Eventually.of_forall (hX_zo i))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_nat_zero_one_eq_measureReal μ .of_discrete (Eventually.of_forall (hX_zo i))]
  have hset : ({b : Fin k → Fin n | X i b = 1}) = {b | ∀ t : Fin k, b t ≠ i} := by
    ext b
    by_cases h : ∀ t : Fin k, b t ≠ i <;> simp [X, h]
  rw [hset, ballBox_prob_avoid_one hp_nn hp_sum i]

/-- Exact variance identity for the empty-box count under `ballBoxMeasure`:
$\operatorname{Var}(W) = \sum_i ((1 - p_i)^k - (1 - p_i)^{2k}) +
  \sum_i \sum_{j \ne i} ((1 - p_i - p_j)^k - (1 - p_i)^k (1 - p_j)^k)$. -/
theorem ballBox_empty_variance {n k : ℕ} {p : Fin n → ℝ}
    (hp_nn : ∀ i : Fin n, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1) :
    ProbabilityTheory.variance (fun b ↦ (emptyBoxCount b : ℝ))
        (ballBoxMeasure p hp_nn hp_sum k) =
      (∑ i : Fin n, ((1 - p i) ^ k - (1 - p i) ^ (2 * k))) +
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ((1 - p i - p j) ^ k - (1 - p i) ^ k * (1 - p j) ^ k) := by
  classical
  let μ := ballBoxMeasure p hp_nn hp_sum k
  let X : Fin n → (Fin k → Fin n) → ℕ := fun i b ↦ if ∀ t : Fin k, b t ≠ i then 1 else 0
  have hX_zo : ∀ i : Fin n, ∀ᵐ b ∂μ, X i b = 0 ∨ X i b = 1 :=
    fun i ↦ Eventually.of_forall fun b ↦ by by_cases h : ∀ t : Fin k, b t ≠ i <;> simp [X, h]
  have hmem : MemLp (fun b ↦ (emptyBoxCount b : ℝ)) 2 μ :=
    memLp_two_sum_nat_zero_one μ (fun _ ↦ .of_discrete) hX_zo
  rw [ProbabilityTheory.variance_eq_sub hmem]
  simp only [Pi.pow_apply]
  rw [ballBox_empty_mean hp_nn hp_sum]
  have hsq_expand : ∀ b : Fin k → Fin n,
      (emptyBoxCount b : ℝ) ^ 2 =
        (emptyBoxCount b : ℝ) +
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (X i b : ℝ) * (X j b : ℝ) := by
    intro b
    have hcast : (emptyBoxCount b : ℝ) = ∑ i : Fin n, (X i b : ℝ) := by
      simp [emptyBoxCount, X]
    rw [hcast, sq, Finset.sum_mul]
    have hsplit : ∀ i : Fin n,
        (X i b : ℝ) * (∑ j : Fin n, (X j b : ℝ)) =
          (X i b : ℝ) + ∑ j ∈ Finset.univ.erase i, (X i b : ℝ) * (X j b : ℝ) := by
      intro i
      rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      by_cases h : ∀ t : Fin k, b t ≠ i <;> simp [X, h]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
  simp_rw [hsq_expand]
  have hint_W : Integrable (fun b ↦ (emptyBoxCount b : ℝ)) μ := hmem.integrable one_le_two
  have hint_pair : ∀ (i j : Fin n), Integrable (fun b ↦ (X i b : ℝ) * (X j b : ℝ)) μ := by
    intro i j
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1
      (Eventually.of_forall fun b ↦ ?_)
    by_cases hi : ∀ t : Fin k, b t ≠ i <;> by_cases hj : ∀ t : Fin k, b t ≠ j <;>
      simp [X, hi, hj]
  rw [integral_add hint_W (integrable_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hint_pair i j),
    ballBox_empty_mean hp_nn hp_sum,
    integral_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hint_pair i j]
  have hpair_int : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
      ∫ b, (X i b : ℝ) * (X j b : ℝ) ∂μ = (1 - p i - p j) ^ k := by
    intro i j hj
    have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
    let Pij : (Fin k → Fin n) → ℕ := fun b ↦ X i b * X j b
    have hPij_zo : ∀ᵐ b ∂μ, Pij b = 0 ∨ Pij b = 1 :=
      Eventually.of_forall fun b ↦ by
        by_cases hi : ∀ t : Fin k, b t ≠ i <;> by_cases hj' : ∀ t : Fin k, b t ≠ j <;>
          simp [Pij, X, hi, hj']
    have hcast_p : (fun b ↦ (X i b : ℝ) * (X j b : ℝ)) = fun b ↦ (Pij b : ℝ) := by
      ext b
      simp [Pij]
    rw [hcast_p, integral_nat_zero_one_eq_measureReal μ .of_discrete hPij_zo]
    have hset : ({b : Fin k → Fin n | Pij b = 1}) =
        {b | (∀ t : Fin k, b t ≠ i) ∧ (∀ t : Fin k, b t ≠ j)} := by
      ext b
      by_cases hi : ∀ t : Fin k, b t ≠ i <;> by_cases hj' : ∀ t : Fin k, b t ≠ j <;>
        simp [Pij, X, hi, hj']
    rw [hset, ballBox_prob_avoid_two hp_nn hp_sum hj_ne]
  have hsum_pairs :
      (∑ i : Fin n, ∫ b, (∑ j ∈ Finset.univ.erase i, (X i b : ℝ) * (X j b : ℝ)) ∂μ) =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (1 - p i - p j) ^ k := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ hint_pair i j]
    exact Finset.sum_congr rfl (hpair_int i)
  rw [hsum_pairs]
  have hsq_sum :
      (∑ i : Fin n, (1 - p i) ^ k) ^ 2 =
        (∑ i : Fin n, (1 - p i) ^ (2 * k)) +
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (1 - p i) ^ k * (1 - p j) ^ k := by
    rw [sq, Finset.sum_mul]
    have hsplit : ∀ i : Fin n,
        (1 - p i) ^ k * (∑ j : Fin n, (1 - p j) ^ k) =
          (1 - p i) ^ (2 * k) + ∑ j ∈ Finset.univ.erase i, (1 - p i) ^ k * (1 - p j) ^ k := by
      intro i
      rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i),
        two_mul, pow_add]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
  rw [hsq_sum, Finset.sum_sub_distrib]
  have hsub2 :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          ((1 - p i - p j) ^ k - (1 - p i) ^ k * (1 - p j) ^ k)) =
        (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (1 - p i - p j) ^ k) -
          ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (1 - p i) ^ k * (1 - p j) ^ k := by
    simp_rw [Finset.sum_sub_distrib]
  rw [hsub2]
  ring

end SteinMethod
