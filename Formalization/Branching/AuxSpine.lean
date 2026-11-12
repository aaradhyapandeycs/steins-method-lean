/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Branching.Basic
import Formalization.SizeBias.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Auxiliary Spine Convolution Semigroup & Tree Sums (`Formalization.Branching.AuxSpine`)

Self-contained Section 5.3 core engine (`SteinIntro.tex:3030-3114`; Critic `I-1`) importing only
`Formalization.Branching.Basic` and `Formalization.SizeBias.Basic`:
* `ℝ≥0∞` discrete convolution semigroup `iidSumProbENN`, associativity of `branchComp`, and the
  combinatorial interval-splitting identity `sum_iidSumProbENN_split`;
* Galton–Watson generation-size recurrence `IsGaltonWatson.measure_Z_succ_eq`, moments
  `𝔼[Z_n] = 1`, positivity `ℙ(Z_n > 0) ≠ 0`, and planar tree probability sum
  `gwProb_sum_genSize_aux`;
* Measurable modification, levelwise `(L, R)` independence, and shift invariance of
  `IsSizeBiasSpine`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Section 1: `ℝ≥0∞` Discrete Convolution Semigroup & Interval-Splitting Identity -/

/-- `ℝ≥0∞`-valued $d$-fold discrete convolution of $q : \mathbb{N} \to \mathbb{R}_{\ge 0}^\infty$.
-/
noncomputable def iidSumProbENN (q : ℕ → ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | d + 1, s => ∑ i ∈ Finset.range (s + 1), q i * iidSumProbENN q d (s - i)

@[simp] theorem iidSumProbENN_zero_zero (q : ℕ → ℝ≥0∞) : iidSumProbENN q 0 0 = 1 := rfl
@[simp] theorem iidSumProbENN_zero_succ (q : ℕ → ℝ≥0∞) (s : ℕ) :
    iidSumProbENN q 0 (s + 1) = 0 := rfl

theorem iidSumProbENN_zero (q : ℕ → ℝ≥0∞) (s : ℕ) :
    iidSumProbENN q 0 s = if s = 0 then 1 else 0 := by cases s <;> rfl

theorem iidSumProbENN_succ (q : ℕ → ℝ≥0∞) (d s : ℕ) :
    iidSumProbENN q (d + 1) s = ∑ i ∈ Finset.range (s + 1), q i * iidSumProbENN q d (s - i) := rfl

private lemma sum_range_triangle_swap {α : Type*} [AddCommMonoid α] (m : ℕ) (F : ℕ → ℕ → α) :
    (∑ m₁ ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (m₁ + 1), F m₁ i) =
      ∑ i ∈ Finset.range (m + 1), ∑ m' ∈ Finset.range (m - i + 1), F (i + m') i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ ↦ ⟨x.2, x.1 - x.2⟩)
    (fun ⟨m₁, i⟩ hx ↦ by simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢; omega)
    (fun ⟨m₁, i₁⟩ hx₁ ⟨m₂, i₂⟩ hx₂ h ↦ ?_) (fun ⟨i, m'⟩ hy ↦ ?_) (fun ⟨m₁, i⟩ hx ↦ ?_)
  · simp only [Finset.mem_sigma, Finset.mem_range] at hx₁ hx₂
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; rcases h with ⟨rfl, _⟩
    have hm : m₁ = m₂ := by omega
    subst hm; rfl
  · simp only [Finset.mem_sigma, Finset.mem_range] at hy
    exact ⟨⟨i + m', i⟩, by simp only [Finset.mem_sigma, Finset.mem_range]; omega,
      by simp only [Sigma.mk.inj_iff, heq_eq_eq]; exact ⟨trivial, by omega⟩⟩
  · simp only [Finset.mem_sigma, Finset.mem_range] at hx; rw [show i + (m₁ - i) = m₁ by omega]

/-- Combinatorial interval-splitting identity in `ℝ≥0∞`: decomposing a $d$-tuple of total sum
$m + r + 1$ at the unique index $a < d$ whose partial sum crosses $m$ yields
`iidSumProbENN q d (m + r + 1)`. -/
theorem sum_iidSumProbENN_split (q : ℕ → ℝ≥0∞) : ∀ (d m r : ℕ),
    (∑ a ∈ Finset.range d, ∑ m₁ ∈ Finset.range (m + 1), ∑ r₁ ∈ Finset.range (r + 1),
      iidSumProbENN q a m₁ * q (m - m₁ + (r - r₁) + 1) * iidSumProbENN q (d - 1 - a) r₁) =
    iidSumProbENN q d (m + r + 1)
  | 0, _, _ => by simp
  | d + 1, m, r => by
      rw [Finset.sum_range_succ']
      have ha0 : (∑ m₁ ∈ Finset.range (m + 1), ∑ r₁ ∈ Finset.range (r + 1),
            iidSumProbENN q 0 m₁ * q (m - m₁ + (r - r₁) + 1) *
              iidSumProbENN q (d + 1 - 1 - 0) r₁) =
          ∑ i ∈ Finset.Ico (m + 1) (m + r + 2), q i * iidSumProbENN q d (m + r + 1 - i) := by
        rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun _ _ ↦ by simp), zero_add]
        simp only [iidSumProbENN_zero_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel]
        refine Finset.sum_bij (fun r₁ _ ↦ m + (r - r₁) + 1)
          (fun r₁ hr₁ ↦ by rw [Finset.mem_range] at hr₁; rw [Finset.mem_Ico]; omega)
          (fun r₁ hr₁ r₂ hr₂ h ↦ by rw [Finset.mem_range] at hr₁ hr₂; omega)
          (fun i hi ↦ by
            rw [Finset.mem_Ico] at hi
            exact ⟨m + r + 1 - i, Finset.mem_range.mpr (by omega), by omega⟩)
          (fun r₁ hr₁ ↦ by
            rw [Finset.mem_range] at hr₁; rw [show m + r + 1 - (m + (r - r₁) + 1) = r₁ by omega])
      have hrest : (∑ a ∈ Finset.range d, ∑ m₁ ∈ Finset.range (m + 1), ∑ r₁ ∈ Finset.range (r + 1),
            iidSumProbENN q (a + 1) m₁ * q (m - m₁ + (r - r₁) + 1) *
              iidSumProbENN q (d + 1 - 1 - (a + 1)) r₁) =
          ∑ i ∈ Finset.range (m + 1), q i * iidSumProbENN q d (m + r + 1 - i) := by
        have hswap : ∀ a ∈ Finset.range d,
            (∑ m₁ ∈ Finset.range (m + 1), ∑ r₁ ∈ Finset.range (r + 1),
              iidSumProbENN q (a + 1) m₁ * q (m - m₁ + (r - r₁) + 1) *
                iidSumProbENN q (d + 1 - 1 - (a + 1)) r₁) =
            ∑ i ∈ Finset.range (m + 1), q i * ∑ m' ∈ Finset.range (m - i + 1),
              ∑ r₁ ∈ Finset.range (r + 1),
                iidSumProbENN q a m' * q (m - i - m' + (r - r₁) + 1) *
                  iidSumProbENN q (d - 1 - a) r₁ := fun a _ ↦ by
          have hsub_d : d + 1 - 1 - (a + 1) = d - 1 - a := by omega
          have hinner_m : ∀ m₁ : ℕ,
              (∑ r₁ ∈ Finset.range (r + 1),
                iidSumProbENN q (a + 1) m₁ * q (m - m₁ + (r - r₁) + 1) *
                  iidSumProbENN q (d + 1 - 1 - (a + 1)) r₁) =
              ∑ i ∈ Finset.range (m₁ + 1), q i * ∑ r₁ ∈ Finset.range (r + 1),
                iidSumProbENN q a (m₁ - i) * q (m - m₁ + (r - r₁) + 1) *
                  iidSumProbENN q (d - 1 - a) r₁ := fun m₁ ↦ by
            simp_rw [hsub_d, iidSumProbENN_succ q a m₁, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
          simp_rw [hinner_m]; rw [sum_range_triangle_swap m]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [← Finset.mul_sum]; congr 1
          refine Finset.sum_congr rfl fun m' _ ↦ Finset.sum_congr rfl fun _ _ ↦ ?_
          rw [show i + m' - i = m' by omega, show m - (i + m') = m - i - m' by omega]
        rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [← Finset.mul_sum, sum_iidSumProbENN_split q d (m - i) r]
        rw [Finset.mem_range] at hi; rw [show m - i + r + 1 = m + r + 1 - i by omega]
      rw [hrest, ha0, Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ m + r + 2),
        iidSumProbENN_succ]

theorem iidSumProbENN_add (q : ℕ → ℝ≥0∞) : ∀ (m₁ m₂ K : ℕ), iidSumProbENN q (m₁ + m₂) K =
    ∑ i ∈ Finset.range (K + 1), iidSumProbENN q m₁ i * iidSumProbENN q m₂ (K - i)
  | 0, _, _ => by
      rw [zero_add, Finset.sum_range_succ', Finset.sum_eq_zero (fun _ _ ↦ by simp), zero_add]; simp
  | m₁ + 1, m₂, K => by
      rw [Nat.succ_add, iidSumProbENN_succ]
      simp_rw [iidSumProbENN_add q m₁ m₂, Finset.mul_sum, Finset.sum_sigma']
      conv_rhs => arg 2; ext i; rw [iidSumProbENN_succ, Finset.sum_mul]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun x _ ↦ ⟨x.1 + x.2, x.1⟩)
        (fun ⟨a, b⟩ hx ↦ by simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢; omega)
        (fun ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h ↦ ?_) (fun ⟨i, a⟩ hy ↦ ?_) (fun ⟨a, b⟩ hx ↦ ?_)
      · simp only [Sigma.mk.inj_iff, heq_eq_eq] at h; rcases h with ⟨_, rfl⟩
        have hb : b₁ = b₂ := by omega
        subst hb; rfl
      · simp only [Finset.mem_sigma, Finset.mem_range] at hy
        exact ⟨⟨a, i - a⟩, by simp only [Finset.mem_sigma, Finset.mem_range]; omega,
          by simp only [Sigma.mk.inj_iff, heq_eq_eq]; exact ⟨by omega, trivial⟩⟩
      · simp only [Finset.mem_sigma, Finset.mem_range] at hx
        rw [show a + b - a = b by omega, show K - (a + b) = K - a - b by omega, mul_assoc]

/-- Branching composition $(b \circ c)(s) = \sum_{m=0}^\infty b(m)\,c^{*m}(s)$ in `ℝ≥0∞`. -/
noncomputable def branchComp (b c : ℕ → ℝ≥0∞) (s : ℕ) : ℝ≥0∞ :=
  ∑' m : ℕ, b m * iidSumProbENN c m s

/-- Antidiagonal equivalence `(Σ m : ℕ, Fin (m + 1)) ≃ ℕ × ℕ` sending `⟨m, j⟩ ↦ (j, m - j)`. -/
def antiDiagEquiv : (Σ m : ℕ, Fin (m + 1)) ≃ ℕ × ℕ where
  toFun x := (x.2.1, x.1 - x.2.1)
  invFun p := ⟨p.1 + p.2, ⟨p.1, by omega⟩⟩
  left_inv := fun ⟨m, ⟨m₁, hm₁⟩⟩ ↦ by
    dsimp
    have h1 : ∀ (a b : ℕ) (_ : a = b) (i : ℕ) (ha : i < a + 1) (hb : i < b + 1),
        (⟨a, ⟨i, ha⟩⟩ : Σ m : ℕ, Fin (m + 1)) = ⟨b, ⟨i, hb⟩⟩ := by rintro a _ rfl _ _ _; rfl
    exact h1 (m₁ + (m - m₁)) m (by omega) m₁ _ hm₁
  right_inv := fun ⟨_, _⟩ ↦ Prod.ext (by dsimp) (by dsimp; omega)

theorem tsum_iidSumProbENN_comp (b c : ℕ → ℝ≥0∞) :
    ∀ (d K : ℕ), (∑' m : ℕ, iidSumProbENN b d m * iidSumProbENN c m K) =
      iidSumProbENN (branchComp b c) d K
  | 0, K => by
      rw [tsum_eq_single 0]; · simp [iidSumProbENN_zero]
      · intro m hm; cases m with | zero => exact False.elim (hm rfl) | succ _ => simp
  | d + 1, K => by
      have hlhs : (∑' m : ℕ, iidSumProbENN b (d + 1) m * iidSumProbENN c m K) =
          ∑' p : ℕ × ℕ, b p.1 * iidSumProbENN b d p.2 * iidSumProbENN c (p.1 + p.2) K := by
        have hstep : ∀ m : ℕ, iidSumProbENN b (d + 1) m * iidSumProbENN c m K =
            ∑' j : Fin (m + 1), b j.1 * iidSumProbENN b d (m - j.1) * iidSumProbENN c m K :=
          fun m ↦ by
            rw [tsum_fintype, iidSumProbENN_succ, Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
        simp_rw [hstep]; rw [← ENNReal.tsum_sigma, ← antiDiagEquiv.tsum_eq]
        refine tsum_congr fun ⟨m, ⟨j, hj⟩⟩ ↦ ?_
        dsimp [antiDiagEquiv]; rw [show j + (m - j) = m by omega]
      rw [hlhs, ENNReal.tsum_prod']
      have hinner : ∀ m₁ : ℕ,
          (∑' m₂ : ℕ, b m₁ * iidSumProbENN b d m₂ * iidSumProbENN c (m₁ + m₂) K) =
          ∑ i ∈ Finset.range (K + 1),
            (b m₁ * iidSumProbENN c m₁ i) * iidSumProbENN (branchComp b c) d (K - i) := fun m₁ ↦ by
        simp_rw [iidSumProbENN_add c m₁ _ K, Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have rearrange : ∀ m₂ : ℕ,
            b m₁ * iidSumProbENN b d m₂ * (iidSumProbENN c m₁ i * iidSumProbENN c m₂ (K - i)) =
              (b m₁ * iidSumProbENN c m₁ i) *
                (iidSumProbENN b d m₂ * iidSumProbENN c m₂ (K - i)) := fun _ ↦ by ring
        simp_rw [rearrange]; rw [ENNReal.tsum_mul_left, tsum_iidSumProbENN_comp b c d (K - i)]
      simp_rw [hinner]
      rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable), iidSumProbENN_succ]
      exact Finset.sum_congr rfl fun _ _ ↦ by rw [ENNReal.tsum_mul_right, branchComp]

theorem branchComp_assoc (a b c : ℕ → ℝ≥0∞) :
    branchComp (branchComp a b) c = branchComp a (branchComp b c) := by
  ext K; unfold branchComp; simp_rw [← ENNReal.tsum_mul_right]; rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left, tsum_iidSumProbENN_comp]; rfl

/-- $n$-fold branching iteration starting from the Dirac mass at $1$. -/
noncomputable def branchIter (p : ℕ → ℝ≥0∞) : ℕ → ℕ → ℝ≥0∞
  | 0, s => if s = 1 then 1 else 0
  | n + 1, s => branchComp (branchIter p n) p s

theorem iidSumProbENN_one (p : ℕ → ℝ≥0∞) (K : ℕ) : iidSumProbENN p 1 K = p K := by
  rw [iidSumProbENN_succ, Finset.sum_range_succ]
  have h0 : ∑ x ∈ Finset.range K, p x * iidSumProbENN p 0 (K - x) = 0 :=
    Finset.sum_eq_zero fun x hx ↦ by
      rw [Finset.mem_range] at hx
      rw [show K - x = (K - x - 1) + 1 by omega, iidSumProbENN_zero_succ, mul_zero]
  rw [h0, zero_add, Nat.sub_self, iidSumProbENN_zero_zero, mul_one]

theorem branchIter_succ_eq_branchComp_left (p : ℕ → ℝ≥0∞) :
    ∀ n : ℕ, branchIter p (n + 1) = branchComp p (branchIter p n)
  | 0 => by
      ext K; simp only [branchIter, branchComp]
      have hlhs : (∑' m : ℕ, (if m = 1 then (1 : ℝ≥0∞) else 0) * iidSumProbENN p m K) = p K := by
        rw [tsum_eq_single 1]; · simp [iidSumProbENN_one]
        · intro m hm; simp [hm]
      have hid_one : ∀ d s : ℕ, iidSumProbENN (fun t ↦ if t = 1 then (1 : ℝ≥0∞) else 0) d s =
          if s = d then 1 else 0 := fun d ↦ by
        induction d with
        | zero => exact iidSumProbENN_zero _
        | succ d ih =>
            intro s; rw [iidSumProbENN_succ]; simp_rw [ih]; rcases s with _ | s; · simp
            · rw [Finset.sum_range_succ', Finset.sum_range_succ',
                Finset.sum_eq_zero (s := Finset.range s) (fun _ _ ↦ by simp), zero_add]; simp
      simp_rw [hid_one]; rw [hlhs, tsum_eq_single K]; · simp
      · intro d hd; simp [hd.symm]
  | n + 1 => by
      change branchComp (branchIter p (n + 1)) p = branchComp p (branchComp (branchIter p n) p)
      rw [branchIter_succ_eq_branchComp_left p n, branchComp_assoc]

/-! ### Section 2: Galton–Watson Generation Laws, Moments, and Planar Tree Sums -/

theorem ae_ball_finset {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) {p : ι → Ω → Prop} (h : ∀ i ∈ s, ∀ᵐ ω ∂μ, p i ω) :
    ∀ᵐ ω ∂μ, ∀ i ∈ s, p i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ae_of_all _ fun _ _ hi ↦ absurd hi (Finset.notMem_empty _)
  | insert a s _ ih =>
      filter_upwards [h a (Finset.mem_insert_self a s),
        ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))] with ω hωa hωs i hi
      rcases Finset.mem_insert.mp hi with rfl | his; · exact hωa
      · exact hωs i his

theorem measurable_sum_range_nat {α : Type*} [MeasurableSpace α] {f : α → ℕ} {g : ℕ → α → ℕ}
    (hf : Measurable f) (hg : ∀ i, Measurable (g i)) :
    Measurable (fun ω ↦ ∑ i ∈ Finset.range (f ω), g i ω) := fun s hs ↦ by
  have hpre : (fun ω ↦ ∑ i ∈ Finset.range (f ω), g i ω) ⁻¹' s =
      ⋃ m : ℕ, f ⁻¹' {m} ∩ (fun ω ↦ ∑ i ∈ Finset.range m, g i ω) ⁻¹' s := by ext; simp
  rw [hpre]
  exact MeasurableSet.iUnion fun m ↦ (hf (measurableSet_singleton m)).inter
    ((Finset.measurable_sum (Finset.range m) fun i _ ↦ hg i) hs)

theorem measurable_sum_Ico_nat {α : Type*} [MeasurableSpace α] {a b : α → ℕ} {g : ℕ → α → ℕ}
    (ha : Measurable a) (hb : Measurable b) (hg : ∀ i, Measurable (g i)) :
    Measurable (fun ω ↦ ∑ i ∈ Finset.Ico (a ω) (b ω), g i ω) := fun s hs ↦ by
  have hpre : (fun ω ↦ ∑ i ∈ Finset.Ico (a ω) (b ω), g i ω) ⁻¹' s =
      ⋃ p : ℕ × ℕ, (a ⁻¹' {p.1} ∩ b ⁻¹' {p.2}) ∩
        (fun ω ↦ ∑ i ∈ Finset.Ico p.1 p.2, g i ω) ⁻¹' s := by
    ext ω; simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, Prod.exists]
    exact ⟨fun h ↦ ⟨a ω, b ω, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨haω, hbω⟩, h⟩ ↦ by simpa [haω, hbω]⟩
  rw [hpre]
  exact MeasurableSet.iUnion fun p ↦
    ((ha (measurableSet_singleton p.1)).inter (hb (measurableSet_singleton p.2))).inter
      ((Finset.measurable_sum (Finset.Ico p.1 p.2) fun i _ ↦ hg i) hs)

theorem measurable_gwCanonical_nat {α : Type*} [MeasurableSpace α] {ξ : ℕ × ℕ → α → ℕ}
    (hξ : ∀ p, Measurable (ξ p)) : ∀ n : ℕ, Measurable (gwCanonical ξ n)
  | 0 => measurable_const
  | n + 1 => measurable_sum_range_nat (measurable_gwCanonical_nat hξ n) (fun i ↦ hξ (n, i))

theorem measure_sum_range_iid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {η : ℕ → Ω → ℕ} {q : ℕ → ℝ≥0∞} (hη_meas : ∀ r, Measurable (η r))
    (hη_indep : iIndepFun η P) (hη_pmf : ∀ r s, P {ω | η r ω = s} = q s) :
    ∀ (d s : ℕ), P {ω | (∑ r ∈ Finset.range d, η r ω) = s} = iidSumProbENN q d s
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | d + 1, s => by
      have hind : IndepFun (η d) (fun ω ↦ ∑ r ∈ Finset.range d, η r ω) P := by
        convert (hη_indep.indepFun_sum_range_succ hη_meas d).symm using 1; ext; simp
      have hsum_meas : Measurable (fun ω ↦ ∑ r ∈ Finset.range d, η r ω) :=
        Finset.measurable_sum (Finset.range d) fun r _ ↦ hη_meas r
      have hpart : {ω : Ω | (∑ r ∈ Finset.range (d + 1), η r ω) = s} =
          ⋃ i ∈ Finset.range (s + 1),
            {ω | η d ω = i} ∩ {ω | (∑ r ∈ Finset.range d, η r ω) = s - i} := by
        ext ω
        simp only [Finset.sum_range_succ, mem_ofPred, mem_iUnion, Finset.mem_range, mem_inter_iff]
        exact ⟨fun h ↦ ⟨η d ω, by omega, rfl, by omega⟩, fun ⟨_, _, _, _⟩ ↦ by omega⟩
      have hdisj : Set.PairwiseDisjoint (↑(Finset.range (s + 1)) : Set ℕ)
          (fun i ↦ {ω : Ω | η d ω = i} ∩ {ω | (∑ r ∈ Finset.range d, η r ω) = s - i}) :=
        fun _ _ _ _ hij ↦ Set.disjoint_left.2 fun _ hωi hωj ↦ hij (hωi.1.symm.trans hωj.1)
      rw [hpart, measure_biUnion_finset hdisj (fun i _ ↦
        (hη_meas d (measurableSet_singleton i)).inter (hsum_meas (measurableSet_singleton _))),
        iidSumProbENN_succ]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change P (η d ⁻¹' {i} ∩ (fun ω ↦ ∑ r ∈ Finset.range d, η r ω) ⁻¹' {s - i}) = _
      rw [hind.measure_inter_preimage_eq_mul {i} {s - i} (measurableSet_singleton i)
        (measurableSet_singleton (s - i))]
      change P {ω | η d ω = i} * P {ω | (∑ r ∈ Finset.range d, η r ω) = s - i} = _
      rw [hη_pmf d i, measure_sum_range_iid P hη_meas hη_indep hη_pmf d (s - i)]

theorem IsGaltonWatson.exists_measurable_array_aux {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) :
    ∃ ξ' : ℕ × ℕ → Ω → ℕ, (∀ p, Measurable (ξ' p)) ∧ iIndepFun ξ' P ∧
      (∀ p, IdentDistrib (ξ' p) (Z 1) P P) ∧ (∀ n, Z n =ᵐ[P] gwCanonical ξ' n) := by
  rcases hGW with ⟨_, ξ, hξ_meas, hξ_indep, hξ_ident, hZ0, hZn⟩
  let ξ' : ℕ × ℕ → Ω → ℕ := fun p ↦ (hξ_meas p).mk (ξ p)
  have hξ_ae : ∀ p, ξ p =ᵐ[P] ξ' p := fun p ↦ (hξ_meas p).ae_eq_mk
  refine ⟨ξ', fun p ↦ (hξ_meas p).measurable_mk, hξ_indep.congr hξ_ae,
    fun p ↦ (IdentDistrib.of_ae_eq (hξ_meas p) (hξ_ae p)).symm.trans (hξ_ident p), fun n ↦ ?_⟩
  induction n with
  | zero => exact hZ0
  | succ n ih =>
      filter_upwards [hZn n, ih, ae_all_iff.2 fun i ↦ hξ_ae (n, i)] with ω h1 h2 h3
      rw [h1, h2, gwCanonical]; exact Finset.sum_congr rfl fun i _ ↦ h3 i

theorem IsGaltonWatson.aemeasurable_Z_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) (n : ℕ) :
    AEMeasurable (Z n) P := by
  obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array_aux
  exact (measurable_gwCanonical_nat hξ'_meas n).aemeasurable.congr (hZ_ae n).symm

private lemma iIndepFun_row_of_iIndepFun_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ × ℕ → Ω → ℕ}
    (hξ_meas : ∀ p, Measurable (ξ p)) (hξ_indep : iIndepFun ξ P) :
    iIndepFun (fun (n : ℕ) (ω : Ω) (i : ℕ) ↦ ξ (n, i) ω) P := by
  have hrow_meas : ∀ n : ℕ, Measurable (fun (ω : Ω) (i : ℕ) ↦ ξ (n, i) ω) :=
    fun n ↦ measurable_pi_iff.2 fun i ↦ hξ_meas (n, i)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hrow_meas]
  have hcurry : (fun (ω : Ω) (n : ℕ) (i : ℕ) ↦ ξ (n, i) ω) =
      (MeasurableEquiv.curry ℕ ℕ ℕ) ∘ (fun (ω : Ω) (p : ℕ × ℕ) ↦ ξ p ω) := rfl
  rw [hcurry, ← Measure.map_map (MeasurableEquiv.curry ℕ ℕ ℕ).measurable
      (measurable_pi_iff.2 hξ_meas), hξ_indep.map_fun_eq_infinitePi_map hξ_meas,
    Measure.infinitePi_map_curry (fun n i ↦ P.map (ξ (n, i)))]
  congr 1; ext n : 1
  exact ((hξ_indep.precomp (Prod.mk_right_injective n)).map_fun_eq_infinitePi_map
    (fun i ↦ hξ_meas (n, i))).symm

private def gwCanonicalOfFinRows : ∀ n : ℕ, (Finset.range n → (ℕ → ℕ)) → ℕ
  | 0, _ => 1
  | n + 1, r =>
      let z := gwCanonicalOfFinRows n (fun j : Finset.range n ↦
        r ⟨j.1, Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 j.2))⟩)
      ∑ i ∈ Finset.range z, r ⟨n, Finset.self_mem_range_succ n⟩ i

private lemma gwCanonicalOfFinRows_eq {Ω : Type*} (ξ : ℕ × ℕ → Ω → ℕ) : ∀ (n : ℕ) (ω : Ω),
    gwCanonicalOfFinRows n (fun (j : Finset.range n) (i : ℕ) ↦ ξ (j.1, i) ω) = gwCanonical ξ n ω
  | 0, _ => rfl
  | n + 1, _ => by dsimp only [gwCanonicalOfFinRows, gwCanonical]; rw [gwCanonicalOfFinRows_eq]

private lemma measurable_gwCanonicalOfFinRows : ∀ n : ℕ, Measurable (gwCanonicalOfFinRows n)
  | 0 => measurable_const
  | n + 1 =>
      measurable_sum_range_nat ((measurable_gwCanonicalOfFinRows n).comp
        (measurable_pi_iff.2 fun _ ↦ measurable_pi_apply _))
        (fun i ↦ (measurable_pi_apply i).comp (measurable_pi_apply _))

private lemma indepFun_gwCanonical_row_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ℕ × ℕ → Ω → ℕ}
    (hξ_meas : ∀ p, Measurable (ξ p)) (hξ_indep : iIndepFun ξ P) (n : ℕ) :
    IndepFun (gwCanonical ξ n) (fun ω (i : ℕ) ↦ ξ (n, i) ω) P := by
  let R : ℕ → Ω → (ℕ → ℕ) := fun m ω i ↦ ξ (m, i) ω
  have hR_meas : ∀ m, AEMeasurable (R m) P :=
    fun m ↦ (measurable_pi_iff.2 fun i ↦ hξ_meas (m, i)).aemeasurable
  have hind := (iIndepFun_row_of_iIndepFun_aux hξ_meas hξ_indep).indepFun_finset₀
    (Finset.range n) {n} (by simp) hR_meas
  have hcomp := hind.comp (measurable_gwCanonicalOfFinRows n)
    (measurable_pi_apply ⟨n, Finset.mem_singleton_self n⟩)
  have heq1 : gwCanonical ξ n =
      gwCanonicalOfFinRows n ∘ fun a (i : Finset.range n) ↦ R i.1 a :=
    funext fun ω ↦ (gwCanonicalOfFinRows_eq ξ n ω).symm
  have heq2 : (fun ω (i : ℕ) ↦ ξ (n, i) ω) =
      (fun f : ({n} : Finset ℕ) → (ℕ → ℕ) ↦ f ⟨n, Finset.mem_singleton_self n⟩) ∘
        fun a (i : ({n} : Finset ℕ)) ↦ R i.1 a := rfl
  rw [heq1, heq2]; exact hcomp

/-- Exact generation-$n$ point-mass formula `P {Z_n = K} = branchIter (d ↦ P {Z_1 = d}) n K`. -/
theorem IsGaltonWatson.measure_Z_eq_branchIter {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) :
    ∀ (n K : ℕ), P {ω | Z n ω = K} = branchIter (fun d ↦ P {ω | Z 1 ω = d}) n K := by
  obtain ⟨ξ', hξ'_meas, hξ'_indep, hξ'_ident, hZ_ae⟩ := hGW.exists_measurable_array_aux
  intro n; induction n with
  | zero =>
      intro K
      have hae : {ω | Z 0 ω = K} =ᵐ[P] {ω | (1 : ℕ) = K} :=
        (hZ_ae 0).mono fun _ hω ↦ by simp [hω]
      rw [measure_congr hae, branchIter]
      split_ifs with hK; · subst hK; simp
      · rw [show {ω : Ω | (1 : ℕ) = K} = ∅ by ext; simp [Ne.symm hK], measure_empty]
  | succ n ih =>
      intro K
      have hae : {ω | Z (n + 1) ω = K} =ᵐ[P] {ω | gwCanonical ξ' (n + 1) ω = K} :=
        (hZ_ae (n + 1)).mono fun _ hω ↦ by simp [hω]
      rw [measure_congr hae, branchIter, branchComp]
      have hZn_meas := measurable_gwCanonical_nat hξ'_meas n
      have hZn1_meas := measurable_gwCanonical_nat hξ'_meas (n + 1)
      let E : ℕ → Set Ω := fun m ↦
        {ω | gwCanonical ξ' n ω = m} ∩ {ω | gwCanonical ξ' (n + 1) ω = K}
      have hE_meas : ∀ m, MeasurableSet (E m) := fun m ↦
        (hZn_meas (measurableSet_singleton m)).inter (hZn1_meas (measurableSet_singleton K))
      have hE_disj : Pairwise fun m₁ m₂ ↦ Disjoint (E m₁) (E m₂) := fun _ _ hm ↦
        Set.disjoint_left.2 fun _ h₁ h₂ ↦ hm (h₁.1.symm.trans h₂.1)
      have hE_union : (⋃ m : ℕ, E m) = {ω | gwCanonical ξ' (n + 1) ω = K} := by ext; simp [E]
      rw [← hE_union, measure_iUnion hE_disj hE_meas]
      refine tsum_congr fun m ↦ ?_
      have hev : E m = {ω | gwCanonical ξ' n ω = m} ∩
          {ω | (∑ i ∈ Finset.range m, ξ' (n, i) ω) = K} := by
        ext ω; simp only [E, mem_inter_iff, mem_ofPred, gwCanonical]
        exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h1 ▸ h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h1.symm ▸ h2⟩⟩
      have hind_m := (indepFun_gwCanonical_row_aux hξ'_meas hξ'_indep n).comp measurable_id
        (Finset.measurable_sum (Finset.range m) fun i _ ↦ measurable_pi_apply i)
      have hm_prod := hind_m.measure_inter_preimage_eq_mul {m} {K} (measurableSet_singleton m)
        (measurableSet_singleton K)
      dsimp only [Function.comp_def, id_eq] at hm_prod
      have hrow_indep : iIndepFun (fun i ω ↦ ξ' (n, i) ω) P :=
        hξ'_indep.precomp (Prod.mk_right_injective n)
      have hrow_pmf : ∀ i s, P {ω | ξ' (n, i) ω = s} = P {ω | Z 1 ω = s} := fun i s ↦
        (hξ'_ident (n, i)).measure_mem_eq (measurableSet_singleton s)
      have hZn_m : P {ω | gwCanonical ξ' n ω = m} = P {ω | Z n ω = m} :=
        measure_congr ((hZ_ae n).symm.mono fun _ hω ↦ by simp [hω])
      rw [hev]
      change P (gwCanonical ξ' n ⁻¹' {m} ∩
        (fun ω ↦ ∑ i ∈ Finset.range m, ξ' (n, i) ω) ⁻¹' {K}) = _
      rw [hm_prod]
      change P {ω | gwCanonical ξ' n ω = m} * P {ω | (∑ i ∈ Finset.range m, ξ' (n, i) ω) = K} = _
      rw [hZn_m, ih m, measure_sum_range_iid P (fun i ↦ hξ'_meas (n, i)) hrow_indep hrow_pmf m K]

/-- Root-first Galton–Watson generation-size distribution recurrence in `ℝ≥0∞`. -/
theorem IsGaltonWatson.measure_Z_succ_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) (n K : ℕ) :
    P {ω | Z (n + 1) ω = K} =
      ∑' d : ℕ, P {ω | Z 1 ω = d} * iidSumProbENN (fun s ↦ P {ω | Z n ω = s}) d K := by
  rw [hGW.measure_Z_eq_branchIter (n + 1) K, branchIter_succ_eq_branchComp_left, branchComp]
  refine tsum_congr fun d ↦ ?_; congr 2; ext s; exact (hGW.measure_Z_eq_branchIter n s).symm

/-- Moments and positivity of $Z_n$ for critical Galton–Watson processes. -/
theorem IsGaltonWatson.lintegral_Z_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) (n : ℕ) :
    (∫⁻ ω, (Z n ω : ℝ≥0∞) ∂P) = (∫⁻ ω, (Z 1 ω : ℝ≥0∞) ∂P) ^ n := by
  obtain ⟨ξ', hξ'_meas, hξ'_indep, hξ'_ident, hZ_ae⟩ := hGW.exists_measurable_array_aux
  set μ₁ : ℝ≥0∞ := ∫⁻ ω, (Z 1 ω : ℝ≥0∞) ∂P
  have hξ'_lint : ∀ p, (∫⁻ ω, (ξ' p ω : ℝ≥0∞) ∂P) = μ₁ := fun p ↦
    ((hξ'_ident p).comp (Measurable.of_discrete (f := fun k : ℕ ↦ (k : ℝ≥0∞)))).lintegral_eq
  have hcanon : ∀ m : ℕ, (∫⁻ ω, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) = μ₁ ^ m := fun m ↦ by
    induction m with
    | zero => simp [gwCanonical]
    | succ m ih =>
        have hZ'_meas := measurable_gwCanonical_nat hξ'_meas m
        let E : ℕ → Set Ω := fun k ↦ {ω | gwCanonical ξ' m ω = k}
        have hE_meas : ∀ k, MeasurableSet (E k) := fun k ↦ hZ'_meas (measurableSet_singleton k)
        have hE_disj : Pairwise fun j k ↦ Disjoint (E j) (E k) :=
          fun _ _ hjk ↦ Set.disjoint_left.2 fun _ hj hk ↦ hjk (hj.symm.trans hk)
        have hE_union : (⋃ k : ℕ, E k) = univ := by ext; simp [E]
        have hstep : ∀ k : ℕ, (∫⁻ ω in E k, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) ∂P) =
            (∫⁻ ω in E k, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) * μ₁ := fun k ↦ by
          have hc1 : ∀ ω ∈ E k, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) =
              ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞) := fun ω hω ↦ by
            have hω' : gwCanonical ξ' m ω = k := hω; simp [gwCanonical, hω']
          have hc2 : ∀ ω ∈ E k, (gwCanonical ξ' m ω : ℝ≥0∞) = (k : ℝ≥0∞) :=
            fun _ hω ↦ congrArg Nat.cast hω
          rw [setLIntegral_congr_fun (hE_meas k) hc1, setLIntegral_congr_fun (hE_meas k) hc2,
            setLIntegral_const, ← lintegral_indicator (hE_meas k)]
          have hind_row := indepFun_gwCanonical_row_aux hξ'_meas hξ'_indep m
          have hsum_meas : Measurable (fun r : ℕ → ℕ ↦ ∑ i ∈ Finset.range k, (r i : ℝ≥0∞)) :=
            Finset.measurable_sum (Finset.range k) fun i _ ↦
              (Measurable.of_discrete (f := Nat.cast)).comp (measurable_pi_apply i)
          have hind_ind : IndepFun ((E k).indicator (fun _ ↦ (1 : ℝ≥0∞)))
              (fun ω ↦ ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞)) P := by
            have h1 : (E k).indicator (fun _ ↦ (1 : ℝ≥0∞)) =
                (Set.indicator {k} (fun _ ↦ (1 : ℝ≥0∞))) ∘ gwCanonical ξ' m := by
              ext ω; by_cases h : gwCanonical ξ' m ω = k <;> simp [E, h]
            rw [h1]; exact hind_row.comp Measurable.of_discrete hsum_meas
          have hξ_cast_m : ∀ i, Measurable (fun ω ↦ (ξ' (m, i) ω : ℝ≥0∞)) :=
            fun i ↦ (Measurable.of_discrete (f := Nat.cast)).comp (hξ'_meas (m, i))
          have hrew : (E k).indicator (fun ω ↦ ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞)) =
              fun ω ↦ (E k).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
                ∑ i ∈ Finset.range k, (ξ' (m, i) ω : ℝ≥0∞) := by
            ext ω; by_cases hω : ω ∈ E k <;> simp [hω]
          rw [hrew, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
              (measurable_const.indicator (hE_meas k)).aemeasurable
              (Finset.measurable_sum (Finset.range k) fun i _ ↦ hξ_cast_m i).aemeasurable hind_ind,
            lintegral_indicator (hE_meas k), setLIntegral_const, one_mul,
            lintegral_finsetSum (Finset.range k) (fun i _ ↦ hξ_cast_m i)]
          simp_rw [hξ'_lint (m, _)]; rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        calc (∫⁻ ω, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) ∂P)
          _ = ∑' k : ℕ, ∫⁻ ω in E k, (gwCanonical ξ' (m + 1) ω : ℝ≥0∞) ∂P := by
              rw [← lintegral_iUnion hE_meas hE_disj, hE_union, Measure.restrict_univ]
          _ = (∑' k : ℕ, ∫⁻ ω in E k, (gwCanonical ξ' m ω : ℝ≥0∞) ∂P) * μ₁ := by
              simp_rw [hstep]; exact ENNReal.tsum_mul_right
          _ = μ₁ ^ (m + 1) := by
              rw [← lintegral_iUnion hE_meas hE_disj, hE_union, Measure.restrict_univ, ih, pow_succ]
  rw [lintegral_congr_ae ((hZ_ae n).mono fun _ hω ↦ congrArg Nat.cast hω), hcanon n]

theorem IsGaltonWatson.integrable_Z_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) (n : ℕ) :
    Integrable (fun ω ↦ (Z n ω : ℝ)) P := by
  refine ⟨((Measurable.of_discrete (f := fun k : ℕ ↦ (k : ℝ))).comp_aemeasurable
    (hGW.aemeasurable_Z_aux n)).aestronglyMeasurable, ?_⟩
  have h1 := hGW.1.2; simp only [HasFiniteIntegral, Real.enorm_natCast] at h1 ⊢
  rw [hGW.lintegral_Z_aux n]; exact ENNReal.pow_lt_top h1

theorem IsGaltonWatson.integral_Z_eq_one_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z)
    (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) (n : ℕ) : ∫ ω, (Z n ω : ℝ) ∂P = 1 := by
  have h_eq : ∀ m : ℕ, (∫ ω, (Z m ω : ℝ) ∂P) = (∫⁻ ω, (Z m ω : ℝ≥0∞) ∂P).toReal := fun m ↦ by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ Nat.cast_nonneg (Z m ω))
      (hGW.integrable_Z_aux m).1]
    congr with ω; exact ENNReal.ofReal_natCast (Z m ω)
  rw [h_eq n, hGW.lintegral_Z_aux n, ENNReal.toReal_pow, ← h_eq 1, hcrit, one_pow]

theorem IsGaltonWatson.measure_Z_pos_ne_zero_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z)
    (hcrit : ∫ ω, (Z 1 ω : ℝ) ∂P = 1) (n : ℕ) : P {ω | 0 < Z n ω} ≠ 0 := by
  have hpos : 0 < ∫ ω, (Z n ω : ℝ) ∂P := by
    rw [hGW.integral_Z_eq_one_aux hcrit n]; exact zero_lt_one
  have hne := measure_pos_ne_zero_of_pos_integral P
    (ae_of_all _ fun ω ↦ Nat.cast_nonneg (Z n ω)) hpos
  rwa [show {ω : Ω | 0 < (Z n ω : ℝ)} = {ω | 0 < Z n ω} by ext; exact_mod_cast Iff.rfl] at hne

/-- `ℝ≥0∞` planar tree probability matching `gwProb`. -/
noncomputable def gwProbENN (p : ℕ → ℝ≥0∞) : ∀ {n : ℕ}, GWTree n → ℝ≥0∞
  | 0, () => 1
  | _ + 1, ts => p ts.length * (ts.map (gwProbENN p)).prod

theorem gwProbENN_toReal {p : ℕ → ℝ≥0∞} (hp : ∀ d, p d ≠ ⊤) : ∀ {n : ℕ} (t : GWTree n),
    gwProbENN p t ≠ ⊤ ∧ (gwProbENN p t).toReal = gwProb (fun d ↦ (p d).toReal) t
  | 0, () => ⟨ENNReal.one_ne_top, by simp [gwProbENN, gwProb]⟩
  | n + 1, ts => by
      have hlist : ∀ s : List (GWTree n), (s.map (gwProbENN p)).prod ≠ ⊤ ∧
          ((s.map (gwProbENN p)).prod).toReal =
            (s.map (gwProb (fun d ↦ (p d).toReal))).prod := fun s ↦ by
        induction s with
        | nil => exact ⟨ENNReal.one_ne_top, by simp⟩
        | cons a s ih =>
            have ha := gwProbENN_toReal hp a; simp only [List.map_cons, List.prod_cons]
            exact ⟨ENNReal.mul_ne_top ha.1 ih.1, by rw [ENNReal.toReal_mul, ha.2, ih.2]⟩
      exact ⟨ENNReal.mul_ne_top (hp ts.length) (hlist ts).1,
        by simp only [gwProbENN, gwProb]; rw [ENNReal.toReal_mul, (hlist ts).2]⟩

private abbrev TreeList (n d K : ℕ) :=
  {ts : List (GWTree n) // ts.length = d ∧ (ts.map gwTreeGenSize).sum = K}

private def treeListSuccEquiv (n d K : ℕ) : TreeList n (d + 1) K ≃
    Σ i : Fin (K + 1), {t : GWTree n // gwTreeGenSize t = i.1} × TreeList n d (K - i.1) where
  toFun
    | ⟨t :: ts, hlen, hsum⟩ =>
        ⟨⟨gwTreeGenSize t, by simp only [List.map_cons, List.sum_cons] at hsum; omega⟩,
          ⟨⟨t, rfl⟩, ⟨ts, Nat.succ.inj hlen,
            by simp only [List.map_cons, List.sum_cons] at hsum ⊢; omega⟩⟩⟩
  invFun x := ⟨x.2.1.1 :: x.2.2.1, by simp [x.2.2.2.1],
    by have := x.1.2; simp only [List.map_cons, List.sum_cons, x.2.1.2, x.2.2.2.2]; omega⟩
  left_inv | ⟨_ :: _, _, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, ⟨⟨_, rfl⟩, ⟨_, _, _⟩⟩⟩ ↦ rfl

private lemma tsum_treeList_prod (p : ℕ → ℝ≥0∞) (n : ℕ) :
    ∀ (d K : ℕ), (∑' ts : TreeList n d K, (ts.1.map (gwProbENN p)).prod) =
      iidSumProbENN (fun s ↦ ∑' t : {t : GWTree n // gwTreeGenSize t = s}, gwProbENN p t.1) d K
  | 0, 0 => by
      let _ : Unique (TreeList n 0 0) :=
        { default := ⟨[], rfl, rfl⟩
          uniq := fun ⟨ts, hlen, _⟩ ↦ Subtype.ext (List.eq_nil_of_length_eq_zero hlen) }
      rw [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]; rfl
  | 0, s + 1 => by
      have : IsEmpty (TreeList n 0 (s + 1)) :=
        ⟨fun ⟨ts, hlen, hsum⟩ ↦ by rw [List.eq_nil_of_length_eq_zero hlen] at hsum; simp at hsum⟩
      simp
  | d + 1, K => by
      rw [← (treeListSuccEquiv n d K).symm.tsum_eq, ENNReal.tsum_sigma', tsum_fintype,
        iidSumProbENN_succ, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ENNReal.tsum_prod']
      have hfactor : ∀ t : {t : GWTree n // gwTreeGenSize t = i.1},
          (∑' ts : TreeList n d (K - i.1),
            (((treeListSuccEquiv n d K).symm ⟨i, (t, ts)⟩).1.map (gwProbENN p)).prod) =
          gwProbENN p t.1 * ∑' ts : TreeList n d (K - i.1), (ts.1.map (gwProbENN p)).prod :=
        fun _ ↦ by
          simp only [treeListSuccEquiv, Equiv.coe_fn_symm_mk, List.map_cons, List.prod_cons]
          exact ENNReal.tsum_mul_left
      simp_rw [hfactor]; rw [ENNReal.tsum_mul_right, tsum_treeList_prod p n d (K - i.1)]

theorem tsum_gwProbENN_eq_branchIter (p : ℕ → ℝ≥0∞) : ∀ (n K : ℕ),
    (∑' t : {t : GWTree n // gwTreeGenSize t = K}, gwProbENN p t.1) = branchIter p n K
  | 0, K => by
      by_cases hK : K = 1
      · subst hK
        let _ : Unique {t : GWTree 0 // gwTreeGenSize t = 1} :=
          { default := ⟨(), rfl⟩, uniq := fun ⟨(), _⟩ ↦ rfl }
        rw [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]; rfl
      · have : IsEmpty {t : GWTree 0 // gwTreeGenSize t = K} := ⟨fun ⟨(), h⟩ ↦ hK h.symm⟩
        simp [branchIter, hK]
  | n + 1, K => by
      let e : {t : GWTree (n + 1) // gwTreeGenSize t = K} ≃ Σ d : ℕ, TreeList n d K :=
        { toFun := fun ⟨ts, hsum⟩ ↦ ⟨ts.length, ⟨ts, rfl, hsum⟩⟩
          invFun := fun ⟨_, ⟨ts, _, hsum⟩⟩ ↦ ⟨ts, hsum⟩
          left_inv := fun ⟨_, _⟩ ↦ rfl
          right_inv := fun ⟨_, ⟨_, rfl, _⟩⟩ ↦ rfl }
      rw [← e.symm.tsum_eq, ENNReal.tsum_sigma', branchIter_succ_eq_branchComp_left, branchComp]
      refine tsum_congr fun d ↦ ?_
      have hcongr : ∀ ts : TreeList n d K,
          gwProbENN p (e.symm ⟨d, ts⟩).1 = p d * (ts.1.map (gwProbENN p)).prod :=
        fun ⟨ts, h, _⟩ ↦ by
          dsimp only [e, Equiv.coe_fn_symm_mk]
          change p ts.length * (ts.map (gwProbENN p)).prod = p d * (ts.map (gwProbENN p)).prod
          rw [h]
      simp_rw [hcongr]; rw [ENNReal.tsum_mul_left, tsum_treeList_prod]
      congr 2; ext s; exact tsum_gwProbENN_eq_branchIter p n s

/-- Self-contained planar tree probability summation identity (`I-1(a,c)`). -/
theorem gwProb_sum_genSize_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : ℕ → Ω → ℕ} (hGW : IsGaltonWatson P Z) (n : ℕ) :
    let p : ℕ → ℝ := fun k ↦ P.real {ω | Z 1 ω = k}
    (Summable (gwProb p : GWTree n → ℝ) ∧ (∑' t : GWTree n, gwProb p t) = 1) ∧
    ∀ k : ℕ, Summable (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwProb p t.1) ∧
      (∑' t : {t : GWTree n // gwTreeGenSize t = k}, gwProb p t.1) = P.real {ω | Z n ω = k} := by
  dsimp only
  let pENN : ℕ → ℝ≥0∞ := fun k ↦ P {ω | Z 1 ω = k}
  let p : ℕ → ℝ := fun k ↦ P.real {ω | Z 1 ω = k}
  have hp_tr : ∀ t : GWTree n, (gwProbENN pENN t).toReal = gwProb p t :=
    fun t ↦ (gwProbENN_toReal (fun _ ↦ measure_ne_top P _) t).2
  have hp_ne : ∀ t : GWTree n, gwProbENN pENN t ≠ ⊤ :=
    fun t ↦ (gwProbENN_toReal (fun _ ↦ measure_ne_top P _) t).1
  have hfiber_ENN : ∀ k : ℕ,
      (∑' t : {t : GWTree n // gwTreeGenSize t = k}, gwProbENN pENN t.1) = P {ω | Z n ω = k} :=
    fun k ↦ by rw [tsum_gwProbENN_eq_branchIter, hGW.measure_Z_eq_branchIter]
  have htotal_ENN : (∑' t : GWTree n, gwProbENN pENN t) = 1 := by
    let efib : GWTree n ≃ Σ k : ℕ, {t : GWTree n // gwTreeGenSize t = k} :=
      { toFun := fun t ↦ ⟨gwTreeGenSize t, ⟨t, rfl⟩⟩, invFun := fun ⟨_, ⟨t, _⟩⟩ ↦ t,
        left_inv := fun _ ↦ rfl, right_inv := fun ⟨_, ⟨_, rfl⟩⟩ ↦ rfl }
    rw [← efib.symm.tsum_eq, ENNReal.tsum_sigma']
    have hfib' : ∀ k : ℕ, (∑' b : {t : GWTree n // gwTreeGenSize t = k},
        gwProbENN pENN (efib.symm ⟨k, b⟩)) = P {ω | Z n ω = k} := hfiber_ENN
    simp_rw [hfib']
    obtain ⟨ξ', hξ'_meas, _, _, hZ_ae⟩ := hGW.exists_measurable_array_aux
    have hZn_meas := measurable_gwCanonical_nat hξ'_meas n
    have hcongr : ∀ k : ℕ, P {ω | Z n ω = k} = P {ω | gwCanonical ξ' n ω = k} := fun k ↦
      measure_congr ((hZ_ae n).mono fun _ hω ↦ by simp [hω])
    simp_rw [hcongr]
    have hdisj : Pairwise fun j k : ℕ ↦
        Disjoint {ω : Ω | gwCanonical ξ' n ω = j} {ω | gwCanonical ξ' n ω = k} :=
      fun _ _ hjk ↦ Set.disjoint_left.2 fun _ hj hk ↦ hjk (hj.symm.trans hk)
    rw [← measure_iUnion hdisj (fun k ↦ hZn_meas (measurableSet_singleton k)),
      show (⋃ k : ℕ, {ω : Ω | gwCanonical ξ' n ω = k}) = univ by ext; simp, measure_univ]
  refine ⟨⟨(ENNReal.summable_toReal (by rw [htotal_ENN]; exact ENNReal.one_ne_top)).congr hp_tr,
    ?_⟩, fun k ↦ ⟨(ENNReal.summable_toReal (by rw [hfiber_ENN k]; exact measure_ne_top P _)).congr
      fun t ↦ hp_tr t.1, ?_⟩⟩
  · rw [show (gwProb p : GWTree n → ℝ) = fun t ↦ (gwProbENN pENN t).toReal from
      funext fun t ↦ (hp_tr t).symm, ← ENNReal.tsum_toReal_eq hp_ne, htotal_ENN, ENNReal.toReal_one]
  · have htsum_tr := ENNReal.tsum_toReal_eq
      (f := fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwProbENN pENN t.1) (fun t ↦ hp_ne t.1)
    rw [show (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwProb p t.1) =
      fun t ↦ (gwProbENN pENN t.1).toReal from funext fun t ↦ (hp_tr t.1).symm,
      ← htsum_tr, hfiber_ENN k, Measure.real]

/-! ### Section 3: Measurable Witness, `(L, R)` Independence, and Shift Lemma -/

/-- Measurable modification of `IsSizeBiasSpine` preserving `A₀ j ω' ≤ X₀ j ω'` everywhere. -/
theorem IsSizeBiasSpine.exists_measurable_witness {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Z : ℕ → Ω → ℕ} {P' : Measure Ω'} {n : ℕ}
    {X L R : ℕ → Ω' → ℕ} (hSp : IsSizeBiasSpine P Z P' n X L R) :
    ∃ (X₀ A₀ L₀ R₀ : ℕ → Ω' → ℕ) (ξ₀ : ℕ → ℕ → Ω' → ℕ),
      iIndepFun
        (fun j : Finset.Icc 1 n ↦ fun ω' ↦ (X₀ j.1 ω', A₀ j.1 ω', fun r : ℕ ↦ ξ₀ j.1 r ω')) P' ∧
      ∀ j ∈ Finset.Icc 1 n,
        Measurable (X₀ j) ∧ Measurable (A₀ j) ∧ Measurable (L₀ j) ∧ Measurable (R₀ j) ∧
        (∀ r : ℕ, Measurable (ξ₀ j r)) ∧ X j =ᵐ[P'] X₀ j ∧ L j =ᵐ[P'] L₀ j ∧ R j =ᵐ[P'] R₀ j ∧
        IsSizeBias P (fun ω ↦ (Z 1 ω : ℝ)) P' (fun ω' ↦ (X₀ j ω' : ℝ) + 1) ∧
        (∀ ω' : Ω', A₀ j ω' ≤ X₀ j ω') ∧
        (∀ k m : ℕ, P'.real {ω' | X₀ j ω' = k ∧ A₀ j ω' = m} =
          if m ≤ k then P'.real {ω' | X₀ j ω' = k} / ((k : ℝ) + 1) else 0) ∧
        iIndepFun (ξ₀ j) P' ∧ (∀ r : ℕ, P'.map (ξ₀ j r) = P.map (Z (n - j))) ∧
        IndepFun (fun ω' ↦ (X₀ j ω', A₀ j ω')) (fun ω' (r : ℕ) ↦ ξ₀ j r ω') P' ∧
        (∀ ω' : Ω', L₀ j ω' = ∑ r ∈ Finset.range (A₀ j ω'), ξ₀ j r ω') ∧
        (∀ ω' : Ω', R₀ j ω' = ∑ r ∈ Finset.Ico (A₀ j ω') (X₀ j ω'), ξ₀ j r ω') := by
  rcases hSp with ⟨A, ξ, h_iindep, h_lvl⟩
  let X₀ : ℕ → Ω' → ℕ := fun j ↦
    if hj : j ∈ Finset.Icc 1 n then (h_lvl j hj).1.mk (X j) else fun _ ↦ 0
  let A₀ : ℕ → Ω' → ℕ := fun j ω' ↦
    if hj : j ∈ Finset.Icc 1 n then min ((h_lvl j hj).2.1.mk (A j) ω') (X₀ j ω') else 0
  let ξ₀ : ℕ → ℕ → Ω' → ℕ := fun j r ↦
    if hj : j ∈ Finset.Icc 1 n then ((h_lvl j hj).2.2.1 r).mk (ξ j r) else fun _ ↦ 0
  let L₀ : ℕ → Ω' → ℕ := fun j ω' ↦ ∑ r ∈ Finset.range (A₀ j ω'), ξ₀ j r ω'
  let R₀ : ℕ → Ω' → ℕ := fun j ω' ↦ ∑ r ∈ Finset.Ico (A₀ j ω') (X₀ j ω'), ξ₀ j r ω'
  have hX₀_eq : ∀ j (hj : j ∈ Finset.Icc 1 n), X₀ j = (h_lvl j hj).1.mk (X j) :=
    fun _ hj ↦ by simp only [X₀, hj, ↓reduceDIte]
  have hA₀_eq : ∀ j (hj : j ∈ Finset.Icc 1 n),
      A₀ j = fun ω' ↦ min ((h_lvl j hj).2.1.mk (A j) ω') (X₀ j ω') :=
    fun _ hj ↦ funext fun _ ↦ by simp only [A₀, hj, ↓reduceDIte]
  have hξ₀_eq : ∀ j (hj : j ∈ Finset.Icc 1 n) (r : ℕ), ξ₀ j r = ((h_lvl j hj).2.2.1 r).mk (ξ j r) :=
    fun _ hj _ ↦ by simp only [ξ₀, hj, ↓reduceDIte]
  have hX_ae : ∀ j (hj : j ∈ Finset.Icc 1 n), X j =ᵐ[P'] X₀ j := fun j hj ↦ by
    rw [hX₀_eq j hj]; exact (h_lvl j hj).1.ae_eq_mk
  have hA_ae : ∀ j (hj : j ∈ Finset.Icc 1 n), A j =ᵐ[P'] A₀ j := fun j hj ↦ by
    rw [hA₀_eq j hj]
    filter_upwards [(h_lvl j hj).2.1.ae_eq_mk, hX_ae j hj] with ω' h1 h2
    simp only [← h1, ← h2]; exact (min_eq_left ((h_lvl j hj).2.2.2.2.1 ω')).symm
  have hξ_ae : ∀ j (hj : j ∈ Finset.Icc 1 n) (r : ℕ), ξ j r =ᵐ[P'] ξ₀ j r := fun j hj r ↦ by
    rw [hξ₀_eq j hj r]; exact ((h_lvl j hj).2.2.1 r).ae_eq_mk
  have h_tuple_ae : ∀ j : Finset.Icc 1 n,
      (fun ω' ↦ (X j.1 ω', A j.1 ω', fun r : ℕ ↦ ξ j.1 r ω')) =ᵐ[P']
        (fun ω' ↦ (X₀ j.1 ω', A₀ j.1 ω', fun r : ℕ ↦ ξ₀ j.1 r ω')) := fun ⟨j, hj⟩ ↦ by
    filter_upwards [hX_ae j hj, hA_ae j hj, ae_all_iff.2 fun r ↦ hξ_ae j hj r] with _ h1 h2 h3
    ext1; · exact h1
    ext1; · exact h2
    exact funext h3
  refine ⟨X₀, A₀, L₀, R₀, ξ₀, h_iindep.congr h_tuple_ae, fun j hj ↦ ?_⟩
  have hX_meas : Measurable (X₀ j) := by rw [hX₀_eq j hj]; exact (h_lvl j hj).1.measurable_mk
  have hA_meas : Measurable (A₀ j) := by
    rw [hA₀_eq j hj]
    exact (Measurable.of_discrete (f := fun p : ℕ × ℕ ↦ min p.1 p.2)).comp
      ((h_lvl j hj).2.1.measurable_mk.prodMk hX_meas)
  have hξ_meas : ∀ r : ℕ, Measurable (ξ₀ j r) := fun r ↦ by
    rw [hξ₀_eq j hj r]; exact ((h_lvl j hj).2.2.1 r).measurable_mk
  have hξ_all : ∀ᵐ ω' ∂P', ∀ r : ℕ, ξ j r ω' = ξ₀ j r ω' := ae_all_iff.2 fun r ↦ hξ_ae j hj r
  have hL_ae : L j =ᵐ[P'] L₀ j := by
    filter_upwards [hA_ae j hj, hξ_all] with ω' hAω hξω
    rw [(h_lvl j hj).2.2.2.2.2.2.2.2.2.1 ω', hAω]; exact Finset.sum_congr rfl fun r _ ↦ hξω r
  have hR_ae : R j =ᵐ[P'] R₀ j := by
    filter_upwards [hX_ae j hj, hA_ae j hj, hξ_all] with ω' hXω hAω hξω
    rw [(h_lvl j hj).2.2.2.2.2.2.2.2.2.2 ω', hAω, hXω]; exact Finset.sum_congr rfl fun r _ ↦ hξω r
  have hSB : IsSizeBias P (fun ω ↦ (Z 1 ω : ℝ)) P' (fun ω' ↦ (X₀ j ω' : ℝ) + 1) := by
    rcases (h_lvl j hj).2.2.2.1 with ⟨hnn, hint, hmeas, heq⟩
    have hcast_ae : (fun ω' ↦ (X j ω' : ℝ) + 1) =ᵐ[P'] (fun ω' ↦ (X₀ j ω' : ℝ) + 1) :=
      (hX_ae j hj).mono fun _ hω ↦ by simp [hω]
    refine ⟨hnn, hint, hmeas.congr hcast_ae, fun f hf hInt ↦ ?_⟩
    rw [← integral_congr_ae (hcast_ae.mono fun _ hω ↦ congrArg f hω)]; exact heq f hf hInt
  have hXA_pmf : ∀ k m : ℕ, P'.real {ω' | X₀ j ω' = k ∧ A₀ j ω' = m} =
      if m ≤ k then P'.real {ω' | X₀ j ω' = k} / ((k : ℝ) + 1) else 0 := fun k m ↦ by
    have hc1 : {ω' | X₀ j ω' = k ∧ A₀ j ω' = m} =ᵐ[P'] {ω' | X j ω' = k ∧ A j ω' = m} := by
      filter_upwards [hX_ae j hj, hA_ae j hj] with _ h1 h2; simp [h1, h2]
    have hc2 : {ω' | X₀ j ω' = k} =ᵐ[P'] {ω' | X j ω' = k} :=
      (hX_ae j hj).symm.mono fun _ h1 ↦ by simp [h1]
    rw [measureReal_congr hc1, measureReal_congr hc2, (h_lvl j hj).2.2.2.2.2.1 k m]
  have hXA_indep : IndepFun (fun ω' ↦ (X₀ j ω', A₀ j ω')) (fun ω' (r : ℕ) ↦ ξ₀ j r ω') P' := by
    refine (h_lvl j hj).2.2.2.2.2.2.2.2.1.congr ?_ ?_
    · filter_upwards [hX_ae j hj, hA_ae j hj] with _ h1 h2; simp [h1, h2]
    · filter_upwards [hξ_all] with _ h3; exact funext h3
  exact ⟨hX_meas, hA_meas, measurable_sum_range_nat hA_meas hξ_meas,
    measurable_sum_Ico_nat hA_meas hX_meas hξ_meas, hξ_meas, hX_ae j hj, hL_ae, hR_ae,
    hSB, fun ω' ↦ by rw [congrFun (hA₀_eq j hj) ω']; exact min_le_right _ _,
    hXA_pmf, (h_lvl j hj).2.2.2.2.2.2.1.congr (hξ_ae j hj),
    fun r ↦ by rw [← Measure.map_congr (hξ_ae j hj r), (h_lvl j hj).2.2.2.2.2.2.2.1 r],
    hXA_indep, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Mutual independence of the spine pairs `(L j, R j)` across `j : Finset.Icc 1 n`. -/
theorem IsSizeBiasSpine.iIndepFun_LR {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Z : ℕ → Ω → ℕ} {P' : Measure Ω'} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hSp : IsSizeBiasSpine P Z P' n X L R) :
    iIndepFun (fun j : Finset.Icc 1 n ↦ fun ω' ↦ (L j.1 ω', R j.1 ω')) P' := by
  obtain ⟨X₀, A₀, L₀, R₀, ξ₀, h_iindep, hlvl⟩ := hSp.exists_measurable_witness
  let ψ : ℕ × ℕ × (ℕ → ℕ) → ℕ × ℕ := fun t ↦
    (∑ r ∈ Finset.range t.2.1, t.2.2 r, ∑ r ∈ Finset.Ico t.2.1 t.1, t.2.2 r)
  have hψ : Measurable ψ :=
    (measurable_sum_range_nat (measurable_fst.comp measurable_snd)
      fun r ↦ (measurable_pi_apply r).comp (measurable_snd.comp measurable_snd)).prodMk
    (measurable_sum_Ico_nat (measurable_fst.comp measurable_snd) measurable_fst
      fun r ↦ (measurable_pi_apply r).comp (measurable_snd.comp measurable_snd))
  have hind0 : iIndepFun (fun j : Finset.Icc 1 n ↦ fun ω' ↦ (L₀ j.1 ω', R₀ j.1 ω')) P' := by
    have heq : (fun j : Finset.Icc 1 n ↦ fun ω' ↦ (L₀ j.1 ω', R₀ j.1 ω')) =
        fun j : Finset.Icc 1 n ↦ ψ ∘ fun ω' ↦ (X₀ j.1 ω', A₀ j.1 ω', fun r ↦ ξ₀ j.1 r ω') :=
      funext fun j ↦ funext fun ω' ↦ Prod.ext
        ((hlvl j.1 j.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ω')
        ((hlvl j.1 j.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ω')
    rw [heq]; exact h_iindep.comp (fun _ ↦ ψ) (fun _ ↦ hψ)
  refine hind0.congr fun ⟨j, hj⟩ ↦ ?_
  filter_upwards [(hlvl j hj).2.2.2.2.2.2.1, (hlvl j hj).2.2.2.2.2.2.2.1] with _ h1 h2
  simp [h1, h2]

theorem IsSizeBiasSpine.aemeasurable_LR {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Z : ℕ → Ω → ℕ} {P' : Measure Ω'} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hSp : IsSizeBiasSpine P Z P' n X L R) {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    AEMeasurable (L j) P' ∧ AEMeasurable (R j) P' := by
  obtain ⟨_, _, L₀, R₀, _, _, hlvl⟩ := hSp.exists_measurable_witness
  rcases hlvl j hj with ⟨_, _, hLm, hRm, _, _, hLae, hRae, _⟩
  exact ⟨hLm.aemeasurable.congr hLae.symm, hRm.aemeasurable.congr hRae.symm⟩

/-- Shifting a spine of length $n + 1$ by $+1$ yields a spine of length $n$. -/
theorem IsSizeBiasSpine.shift {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Z : ℕ → Ω → ℕ} {P' : Measure Ω'} {n : ℕ} {X L R : ℕ → Ω' → ℕ}
    (hSp : IsSizeBiasSpine P Z P' (n + 1) X L R) :
    IsSizeBiasSpine P Z P' n (fun j ↦ X (j + 1)) (fun j ↦ L (j + 1)) (fun j ↦ R (j + 1)) := by
  rcases hSp with ⟨A, ξ, h_iindep, h_lvl⟩
  refine ⟨fun j ↦ A (j + 1), fun j ↦ ξ (j + 1), ?_, fun j hj ↦ ?_⟩
  · let emb : Finset.Icc 1 n → Finset.Icc 1 (n + 1) := fun j ↦
      ⟨j.1 + 1, Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp j.2).1; omega,
        by have := (Finset.mem_Icc.mp j.2).2; omega⟩⟩
    have hinj : Function.Injective emb :=
      fun _ _ h ↦ Subtype.ext (Nat.succ.inj (congrArg Subtype.val h))
    exact h_iindep.precomp hinj
  · have hj1 : j + 1 ∈ Finset.Icc 1 (n + 1) := by rw [Finset.mem_Icc] at hj ⊢; omega
    simpa only [Nat.succ_sub_succ_eq_sub n j] using h_lvl (j + 1) hj1

end SteinMethod
