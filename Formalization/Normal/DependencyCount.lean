/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

/-!
# Combinatorial and Fourth-Moment Bounds for Dependency Graphs

Auxiliary AM-GM inequalities, `L^4` moment integrability helpers, degree-counting bounds for
triple sums, and the fourth-moment variance bound `(3.12)`–`(3.16)` (`SteinIntro.tex:849-906`)
for Theorem 3.5 (`\label{thm41}`, `Thm3_5_corrected`, `ISSUE-3.5`).
-/

open MeasureTheory

namespace SteinMethod

/-! ### Elementary AM-GM inequalities -/

/-- Two-variable AM-GM inequality $|ab| \le (a^2 + b^2)/2$ (`SteinIntro.tex:875, 897`). -/
lemma abs_mul_le_half_add_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  have hid : a ^ 2 + b ^ 2 - 2 * (|a| * |b|) =
      (|a| - |b|) ^ 2 + (a ^ 2 - |a| ^ 2) + (b ^ 2 - |b| ^ 2) := by ring
  have h1 : 0 ≤ (|a| - |b|) ^ 2 := sq_nonneg (|a| - |b|)
  have h2 : |a| ^ 2 = a ^ 2 := sq_abs a
  have h3 : |b| ^ 2 = b ^ 2 := sq_abs b
  linarith

/-- Square AM-GM inequality $a^2 b^2 \le (a^4 + b^4)/2$ (`SteinIntro.tex:875, 899`). -/
lemma mul_sq_le_half_add_pow_four (a b : ℝ) : a ^ 2 * b ^ 2 ≤ (a ^ 4 + b ^ 4) / 2 := by
  have hid : a ^ 4 + b ^ 4 - 2 * (a ^ 2 * b ^ 2) = (a ^ 2 - b ^ 2) ^ 2 := by ring
  have hnn : 0 ≤ (a ^ 2 - b ^ 2) ^ 2 := sq_nonneg (a ^ 2 - b ^ 2)
  linarith

/-- Three-variable AM-GM inequality $abc \le (a^3 + b^3 + c^3)/3$ for $a, b, c \ge 0$
(`SteinIntro.tex:850-852`). -/
lemma amgm_three_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ (a ^ 3 + b ^ 3 + c ^ 3) / 3 := by
  have hid : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) =
      (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2 := by ring
  have hnn : 0 ≤ (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2 := by positivity
  linarith

/-- Three-variable absolute AM-GM inequality $|a||b||c| \le (|a|^3 + |b|^3 + |c|^3)/3$
(`SteinIntro.tex:850-852`). -/
lemma abs_mul_three_le (a b c : ℝ) : |a| * |b| * |c| ≤ (|a| ^ 3 + |b| ^ 3 + |c| ^ 3) / 3 :=
  amgm_three_nonneg (abs_nonneg a) (abs_nonneg b) (abs_nonneg c)

/-- Four-variable AM-GM inequality $abcd \le (a^4 + b^4 + c^4 + d^4)/4$
(`SteinIntro.tex:879, 887`). -/
lemma mul_four_le (a b c d : ℝ) : a * b * c * d ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have hid : a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 - 4 * (a * b * c * d) =
      (a ^ 2 - b ^ 2) ^ 2 + (c ^ 2 - d ^ 2) ^ 2 + 2 * (a * b - c * d) ^ 2 := by ring
  have hnn : 0 ≤ (a ^ 2 - b ^ 2) ^ 2 + (c ^ 2 - d ^ 2) ^ 2 + 2 * (a * b - c * d) ^ 2 := by
    positivity
  linarith

/-- Four-variable absolute AM-GM inequality $|abcd| \le (a^4 + b^4 + c^4 + d^4)/4$
(`SteinIntro.tex:879, 887`). -/
lemma abs_mul_four_le (a b c d : ℝ) :
    |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  rw [abs_le]
  refine ⟨?_, mul_four_le a b c d⟩
  have hneg := mul_four_le (-a) b c d
  have hpow : (-a) ^ 4 = a ^ 4 := by ring
  linarith

/-! ### Moment and integrability helpers under `MemLp · 4 P` -/

/-- Under a probability measure, `MemLp Y 4 P` implies `Integrable Y P`
(`SteinIntro.tex:816`). -/
lemma depGraph_integrable_of_memLp_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY4 : MemLp Y 4 P) :
    Integrable Y P :=
  hY4.integrable (by norm_num)

/-- Under a probability measure, `MemLp Y 4 P` implies integrability of $|Y|^3$
(`SteinIntro.tex:816, 820`). -/
lemma integrable_abs_pow_three {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY4 : MemLp Y 4 P) :
    Integrable (fun ω ↦ |Y ω| ^ 3) P := by
  have hY3 : MemLp Y (3 : ℕ) P := hY4.mono_exponent (by norm_num)
  have hi : Integrable (fun ω ↦ ‖Y ω‖ ^ 3) P := hY3.integrable_norm_pow'
  simpa only [Real.norm_eq_abs] using hi

/-- Under a probability measure, `MemLp Y 4 P` implies integrability of $Y^4$
(`SteinIntro.tex:816, 820`). -/
lemma integrable_pow_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY4 : MemLp Y 4 P) :
    Integrable (fun ω ↦ Y ω ^ 4) P := by
  have hY4' : MemLp Y (4 : ℕ) P := hY4.mono_exponent (by norm_num)
  have hi : Integrable (fun ω ↦ ‖Y ω‖ ^ 4) P := hY4'.integrable_norm_pow'
  have hnorm : (fun ω ↦ ‖Y ω‖ ^ 4) = fun ω ↦ Y ω ^ 4 := by
    ext ω
    rw [Real.norm_eq_abs]
    have hsq : |Y ω| ^ 2 = Y ω ^ 2 := sq_abs (Y ω)
    calc |Y ω| ^ 4 = (|Y ω| ^ 2) ^ 2 := by ring
      _ = (Y ω ^ 2) ^ 2 := by rw [hsq]
      _ = Y ω ^ 4 := by ring
  rwa [hnorm] at hi

/-- Under a probability measure, if $Y, Z \in L^4(P)$, then $Y Z$ is integrable
(`SteinIntro.tex:860-866`). -/
lemma integrable_mul_of_memLp_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y Z : Ω → ℝ} (hY4 : MemLp Y 4 P) (hZ4 : MemLp Z 4 P) :
    Integrable (fun ω ↦ Y ω * Z ω) P := by
  have hY2 : Integrable (fun ω ↦ Y ω ^ 2) P := (hY4.mono_exponent (by norm_num)).integrable_sq
  have hZ2 : Integrable (fun ω ↦ Z ω ^ 2) P := (hZ4.mono_exponent (by norm_num)).integrable_sq
  refine ((hY2.fun_add hZ2).div_const 2).mono'
    (hY4.aestronglyMeasurable.mul hZ4.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  simpa only [Real.norm_eq_abs] using abs_mul_le_half_add_sq (Y ω) (Z ω)

/-- Under a probability measure, if $Y, Z \in L^4(P)$, then $Y Z \in L^2(P)$
(`SteinIntro.tex:860-871`). -/
lemma memLp_two_mul_of_memLp_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y Z : Ω → ℝ} (hY4 : MemLp Y 4 P) (hZ4 : MemLp Z 4 P) :
    MemLp (fun ω ↦ Y ω * Z ω) 2 P := by
  have hmeas : AEStronglyMeasurable (fun ω ↦ Y ω * Z ω) P :=
    hY4.aestronglyMeasurable.mul hZ4.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hmeas_sq : AEStronglyMeasurable (fun ω ↦ (Y ω * Z ω) ^ 2) P := by
    have heq : (fun ω ↦ (Y ω * Z ω) ^ 2) = fun ω ↦ (Y ω * Z ω) * (Y ω * Z ω) := by
      ext ω
      exact sq (Y ω * Z ω)
    rw [heq]
    exact hmeas.mul hmeas
  refine (((integrable_pow_four hY4).fun_add (integrable_pow_four hZ4)).div_const 2).mono' hmeas_sq
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
  exact mul_sq_le_half_add_pow_four (Y ω) (Z ω)

/-- Under a probability measure, if $U, V, W \in L^4(P)$, then $|U||V||W|$ is integrable
(`SteinIntro.tex:847-852`). -/
lemma integrable_abs_mul_three {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U V W : Ω → ℝ}
    (hU4 : MemLp U 4 P) (hV4 : MemLp V 4 P) (hW4 : MemLp W 4 P) :
    Integrable (fun ω ↦ |U ω| * |V ω| * |W ω|) P := by
  have hdom : Integrable (fun ω ↦ (|U ω| ^ 3 + |V ω| ^ 3 + |W ω| ^ 3) / 3) P :=
    (((integrable_abs_pow_three hU4).fun_add (integrable_abs_pow_three hV4)).fun_add
      (integrable_abs_pow_three hW4)).div_const 3
  have hU : AEStronglyMeasurable (fun ω ↦ |U ω|) P := by
    simpa only [Real.norm_eq_abs] using hU4.aestronglyMeasurable.norm
  have hV : AEStronglyMeasurable (fun ω ↦ |V ω|) P := by
    simpa only [Real.norm_eq_abs] using hV4.aestronglyMeasurable.norm
  have hW : AEStronglyMeasurable (fun ω ↦ |W ω|) P := by
    simpa only [Real.norm_eq_abs] using hW4.aestronglyMeasurable.norm
  have hmeas : AEStronglyMeasurable (fun ω ↦ |U ω| * |V ω| * |W ω|) P :=
    (hU.mul hV).mul hW
  refine hdom.mono' hmeas (Filter.Eventually.of_forall fun ω ↦ ?_)
  have hnn : 0 ≤ |U ω| * |V ω| * |W ω| := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact abs_mul_three_le (U ω) (V ω) (W ω)

/-- Under a probability measure, if $U_1, U_2, U_3, U_4 \in L^4(P)$, then $U_1 U_2 U_3 U_4$ is
integrable (`SteinIntro.tex:870-883`). -/
lemma integrable_mul_four {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U₁ U₂ U₃ U₄ : Ω → ℝ}
    (h1 : MemLp U₁ 4 P) (h2 : MemLp U₂ 4 P) (h3 : MemLp U₃ 4 P) (h4 : MemLp U₄ 4 P) :
    Integrable (fun ω ↦ U₁ ω * U₂ ω * U₃ ω * U₄ ω) P := by
  have hdom : Integrable (fun ω ↦ (U₁ ω ^ 4 + U₂ ω ^ 4 + U₃ ω ^ 4 + U₄ ω ^ 4) / 4) P :=
    ((((integrable_pow_four h1).fun_add (integrable_pow_four h2)).fun_add
      (integrable_pow_four h3)).fun_add (integrable_pow_four h4)).div_const 4
  have hmeas : AEStronglyMeasurable (fun ω ↦ U₁ ω * U₂ ω * U₃ ω * U₄ ω) P :=
    ((h1.aestronglyMeasurable.mul h2.aestronglyMeasurable).mul
      h3.aestronglyMeasurable).mul h4.aestronglyMeasurable
  refine hdom.mono' hmeas (Filter.Eventually.of_forall fun ω ↦ ?_)
  simpa only [Real.norm_eq_abs] using abs_mul_four_le (U₁ ω) (U₂ ω) (U₃ ω) (U₄ ω)

/-- Cauchy–Schwarz / Jensen inequality $(\mathbb{E}[Y])^2 \le \mathbb{E}[Y^2]$ on a probability
space (`SteinIntro.tex:860, 898`). -/
lemma sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P) :
    (∫ ω, Y ω ∂P) ^ 2 ≤ ∫ ω, Y ω ^ 2 ∂P := by
  have hnn : 0 ≤ ProbabilityTheory.variance Y P := ProbabilityTheory.variance_nonneg Y P
  have hsub : ProbabilityTheory.variance Y P = (∫ ω, Y ω ^ 2 ∂P) - (∫ ω, Y ω ∂P) ^ 2 := by
    simpa only [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hY
  linarith

/-! ### Combinatorial degree bounds for triple and quadruple neighborhood sums -/

/-- Swapping sums over $i$ and $j \in N_i$ when $j \in N_i \leftrightarrow i \in N_j$
(`SteinIntro.tex:854-856`). -/
lemma sum_dep_comm {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ i j, j ∈ N i → i ∈ N j) (F : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j ∈ N i, F i j) = ∑ j : Fin n, ∑ i ∈ N j, F i j := by
  have h1 (i : Fin n) : (∑ j ∈ N i, F i j) = ∑ j : Fin n, if j ∈ N i then F i j else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 (j : Fin n) : (∑ i ∈ N j, F i j) = ∑ i : Fin n, if i ∈ N j then F i j else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have hij : (j ∈ N i) ↔ (i ∈ N j) := ⟨hSymm i j, hSymm j i⟩
  simp only [hij]

/-- Triple neighborhood sum bound
$\sum_{i=1}^n \sum_{j,k \in N_i} (g(i) + g(j) + g(k))/3 \le D^2 \sum_{i=1}^n g(i)$
for symmetric neighborhoods of maximum size $D$ (`SteinIntro.tex:849-856`). -/
lemma sum_triple_dep_amgm_le {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ i j, j ∈ N i → i ∈ N j) {g : Fin n → ℝ} (hg : ∀ i, 0 ≤ g i) :
    let D : ℝ := ((Finset.univ.sup fun i : Fin n ↦ (N i).card : ℕ) : ℝ)
    (∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, (g i + g j + g k) / 3) ≤
      D ^ 2 * ∑ i : Fin n, g i := by
  intro D
  have hD_nonneg : 0 ≤ D := Nat.cast_nonneg _
  have hcard (i : Fin n) : ((N i).card : ℝ) ≤ D :=
    Nat.cast_le.mpr (Finset.le_sup (f := fun k : Fin n ↦ (N k).card) (Finset.mem_univ i))
  have h_first : (∑ i : Fin n, ∑ _j ∈ N i, ∑ _k ∈ N i, g i) ≤ D ^ 2 * ∑ i : Fin n, g i := by
    calc ∑ i : Fin n, ∑ _j ∈ N i, ∑ _k ∈ N i, g i
        = ∑ i : Fin n, ((N i).card : ℝ) * (((N i).card : ℝ) * g i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i : Fin n, D * (D * g i) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have h1 : ((N i).card : ℝ) * g i ≤ D * g i :=
            mul_le_mul_of_nonneg_right (hcard i) (hg i)
          have h2 : ((N i).card : ℝ) * (((N i).card : ℝ) * g i) ≤ ((N i).card : ℝ) * (D * g i) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
          exact h2.trans (mul_le_mul_of_nonneg_right (hcard i) (mul_nonneg hD_nonneg (hg i)))
      _ = D ^ 2 * ∑ i : Fin n, g i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
  have h_second : (∑ i : Fin n, ∑ j ∈ N i, ∑ _k ∈ N i, g j) ≤ D ^ 2 * ∑ j : Fin n, g j := by
    calc ∑ i : Fin n, ∑ j ∈ N i, ∑ _k ∈ N i, g j
        = ∑ i : Fin n, ∑ j ∈ N i, ((N i).card : ℝ) * g j := by
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i : Fin n, ∑ j ∈ N i, D * g j := by
          refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
          exact mul_le_mul_of_nonneg_right (hcard i) (hg j)
      _ = ∑ j : Fin n, ∑ _i ∈ N j, D * g j := sum_dep_comm hSymm (fun _ j ↦ D * g j)
      _ = ∑ j : Fin n, ((N j).card : ℝ) * (D * g j) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n, D * (D * g j) := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          exact mul_le_mul_of_nonneg_right (hcard j) (mul_nonneg hD_nonneg (hg j))
      _ = D ^ 2 * ∑ j : Fin n, g j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          ring
  have h_third : (∑ i : Fin n, ∑ _j ∈ N i, ∑ k ∈ N i, g k) ≤ D ^ 2 * ∑ k : Fin n, g k := by
    have hswap : (∑ i : Fin n, ∑ _j ∈ N i, ∑ k ∈ N i, g k) =
        ∑ i : Fin n, ∑ k ∈ N i, ∑ _j ∈ N i, g k :=
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    rw [hswap]
    exact h_second
  have hsplit : (∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, (g i + g j + g k) / 3) =
      ((∑ i : Fin n, ∑ _j ∈ N i, ∑ _k ∈ N i, g i) +
        (∑ i : Fin n, ∑ j ∈ N i, ∑ _k ∈ N i, g j) +
        (∑ i : Fin n, ∑ _j ∈ N i, ∑ k ∈ N i, g k)) / 3 := by
    simp_rw [← Finset.sum_div]
    congr 1
    simp_rw [Finset.sum_add_distrib]
  rw [hsplit]
  linarith

/-- Type of 4-tuples $(i, k, j, l) \in \{1, \dots, n\}^4$ indexing expanded quadratic sums
(`SteinIntro.tex:870-900`). -/
private abbrev Tuple4 (n : ℕ) : Type := Fin n × Fin n × Fin n × Fin n

/-- All 4-tuples $(i, k, j, l)$ with $k \in N_i$ and $l \in N_j$ (`SteinIntro.tex:870-883`). -/
private def allEdgeTuples {n : ℕ} (N : Fin n → Finset (Fin n)) : Finset (Tuple4 n) :=
  Finset.univ.filter fun t ↦ t.2.1 ∈ N t.1 ∧ t.2.2.2 ∈ N t.2.2.1

/-- Connected / dependent 4-tuples $(i, k, j, l)$ with $k \in N_i$, $l \in N_j$, and at least one
cross-neighborhood edge between $\{i, k\}$ and $\{j, l\}$ (`SteinIntro.tex:883-894`). -/
private def badTuples {n : ℕ} (N : Fin n → Finset (Fin n)) : Finset (Tuple4 n) :=
  Finset.univ.filter fun t ↦
    t.2.1 ∈ N t.1 ∧ t.2.2.2 ∈ N t.2.2.1 ∧
      (t.2.2.1 ∈ N t.1 ∨ t.2.2.2 ∈ N t.1 ∨ t.2.2.1 ∈ N t.2.1 ∨ t.2.2.2 ∈ N t.2.1)

private lemma badTuples_subset_allEdgeTuples {n : ℕ} (N : Fin n → Finset (Fin n)) :
    badTuples N ⊆ allEdgeTuples N := by
  intro t ht
  simp only [badTuples, allEdgeTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  exact ⟨ht.1, ht.2.1⟩

private lemma mul_dep_sum_eq_sum_allEdgeTuples {n : ℕ} (N : Fin n → Finset (Fin n))
    (g₁ g₂ : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ k ∈ N i, g₁ i k) * (∑ j : Fin n, ∑ l ∈ N j, g₂ j l) =
      ∑ t ∈ allEdgeTuples N, g₁ t.1 t.2.1 * g₂ t.2.2.1 t.2.2.2 := by
  have h1 (i : Fin n) : (∑ k ∈ N i, g₁ i k) = ∑ k : Fin n, if k ∈ N i then g₁ i k else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h2 (j : Fin n) : (∑ l ∈ N j, g₂ j l) = ∑ l : Fin n, if l ∈ N j then g₂ j l else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [h1, h2]
  rw [Fintype.sum_mul_sum]
  simp_rw [Fintype.sum_mul_sum]
  have hcomm :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          (if k ∈ N i then g₁ i k else 0) * (if l ∈ N j then g₂ j l else 0)) =
        ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          (if k ∈ N i then g₁ i k else 0) * (if l ∈ N j then g₂ j l else 0) :=
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  rw [hcomm, allEdgeTuples, Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦
    Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  by_cases hk : k ∈ N i <;> by_cases hl : l ∈ N j <;> simp [hk, hl]

private lemma card_triple_biUnion_image_le {n : ℕ}
    (A : Finset (Fin n)) (B : Fin n → Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (f : Fin n → Fin n → Fin n → Tuple4 n) (D : ℕ)
    (hA : A.card ≤ D) (hB : ∀ x, (B x).card ≤ D) (hC : ∀ y, (C y).card ≤ D) :
    (A.biUnion fun x ↦ (B x).biUnion fun y ↦ (C y).image fun z ↦ f x y z).card ≤ D ^ 3 := by
  have h_inner (x : Fin n) :
      ((B x).biUnion fun y ↦ (C y).image fun z ↦ f x y z).card ≤ D * D := by
    calc ((B x).biUnion fun y ↦ (C y).image fun z ↦ f x y z).card
        ≤ ∑ y ∈ B x, ((C y).image fun z ↦ f x y z).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ B x, D := Finset.sum_le_sum fun y _ ↦ Finset.card_image_le.trans (hC y)
      _ = (B x).card * D := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
      _ ≤ D * D := Nat.mul_le_mul_right D (hB x)
  calc (A.biUnion fun x ↦ (B x).biUnion fun y ↦ (C y).image fun z ↦ f x y z).card
      ≤ ∑ x ∈ A, ((B x).biUnion fun y ↦ (C y).image fun z ↦ f x y z).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ A, D * D := Finset.sum_le_sum fun x _ ↦ h_inner x
    _ = A.card * (D * D) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ D * (D * D) := Nat.mul_le_mul_right (D * D) hA
    _ = D ^ 3 := by ring

private lemma card_badTuples_coord1_le {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ x y, y ∈ N x → x ∈ N y) (v : Fin n) :
    let D_nat : ℕ := Finset.univ.sup fun x : Fin n ↦ (N x).card
    ((badTuples N).filter fun t ↦ t.1 = v).card ≤ 4 * D_nat ^ 3 := by
  intro D_nat
  have hcard (x : Fin n) : (N x).card ≤ D_nat :=
    Finset.le_sup (f := fun z : Fin n ↦ (N z).card) (Finset.mem_univ x)
  let S₁ : Finset (Tuple4 n) :=
    (N v).biUnion fun k ↦ (N v).biUnion fun j ↦ (N j).image fun l ↦ (v, k, j, l)
  let S₂ : Finset (Tuple4 n) :=
    (N v).biUnion fun k ↦ (N k).biUnion fun j ↦ (N j).image fun l ↦ (v, k, j, l)
  let S₃ : Finset (Tuple4 n) :=
    (N v).biUnion fun k ↦ (N v).biUnion fun l ↦ (N l).image fun j ↦ (v, k, j, l)
  let S₄ : Finset (Tuple4 n) :=
    (N v).biUnion fun k ↦ (N k).biUnion fun l ↦ (N l).image fun j ↦ (v, k, j, l)
  have hsub : ((badTuples N).filter fun t ↦ t.1 = v) ⊆ (S₁ ∪ S₂) ∪ (S₃ ∪ S₄) := by
    rintro ⟨i, k, j, l⟩ ht
    simp only [badTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rcases ht with ⟨⟨hk, hl, hconn⟩, rfl⟩
    simp only [S₁, S₂, S₃, S₄, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
    rcases hconn with hjv | hlv | hjk | hlk
    · exact Or.inl (Or.inl ⟨k, hk, j, hjv, l, hl, rfl⟩)
    · exact Or.inr (Or.inl ⟨k, hk, l, hlv, j, hSymm j l hl, rfl⟩)
    · exact Or.inl (Or.inr ⟨k, hk, j, hjk, l, hl, rfl⟩)
    · exact Or.inr (Or.inr ⟨k, hk, l, hlk, j, hSymm j l hl, rfl⟩)
  have hS₁ : S₁.card ≤ D_nat ^ 3 :=
    card_triple_biUnion_image_le (N v) (fun _ ↦ N v) N (fun k j l ↦ (v, k, j, l)) D_nat
      (hcard v) (fun _ ↦ hcard v) hcard
  have hS₂ : S₂.card ≤ D_nat ^ 3 :=
    card_triple_biUnion_image_le (N v) N N (fun k j l ↦ (v, k, j, l)) D_nat
      (hcard v) hcard hcard
  have hS₃ : S₃.card ≤ D_nat ^ 3 :=
    card_triple_biUnion_image_le (N v) (fun _ ↦ N v) N (fun k l j ↦ (v, k, j, l)) D_nat
      (hcard v) (fun _ ↦ hcard v) hcard
  have hS₄ : S₄.card ≤ D_nat ^ 3 :=
    card_triple_biUnion_image_le (N v) N N (fun k l j ↦ (v, k, j, l)) D_nat
      (hcard v) hcard hcard
  have hu : ((S₁ ∪ S₂) ∪ (S₃ ∪ S₄)).card ≤ (S₁.card + S₂.card) + (S₃.card + S₄.card) :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _))
  have hle : ((badTuples N).filter fun t ↦ t.1 = v).card ≤
      ((S₁ ∪ S₂) ∪ (S₃ ∪ S₄)).card := Finset.card_le_card hsub
  omega

private lemma mem_badTuples_swap12_imp {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ x y, y ∈ N x → x ∈ N y) {i k j l : Fin n}
    (h : (i, k, j, l) ∈ badTuples N) : (k, i, j, l) ∈ badTuples N := by
  simp only [badTuples, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  rcases h with ⟨hik, hlj, h1 | h2 | h3 | h4⟩
  · exact ⟨hSymm i k hik, hlj, Or.inr (Or.inr (Or.inl h1))⟩
  · exact ⟨hSymm i k hik, hlj, Or.inr (Or.inr (Or.inr h2))⟩
  · exact ⟨hSymm i k hik, hlj, Or.inl h3⟩
  · exact ⟨hSymm i k hik, hlj, Or.inr (Or.inl h4)⟩

private lemma mem_badTuples_swap12 {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ x y, y ∈ N x → x ∈ N y) (t : Tuple4 n) :
    t ∈ badTuples N ↔ (t.2.1, t.1, t.2.2.1, t.2.2.2) ∈ badTuples N := by
  rcases t with ⟨i, k, j, l⟩
  exact ⟨mem_badTuples_swap12_imp hSymm, mem_badTuples_swap12_imp hSymm⟩

private lemma mem_badTuples_swapPairs_imp {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ x y, y ∈ N x → x ∈ N y) {i k j l : Fin n}
    (h : (i, k, j, l) ∈ badTuples N) : (j, l, i, k) ∈ badTuples N := by
  simp only [badTuples, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  rcases h with ⟨hik, hlj, h1 | h2 | h3 | h4⟩
  · exact ⟨hlj, hik, Or.inl (hSymm i j h1)⟩
  · exact ⟨hlj, hik, Or.inr (Or.inr (Or.inl (hSymm i l h2)))⟩
  · exact ⟨hlj, hik, Or.inr (Or.inl (hSymm k j h3))⟩
  · exact ⟨hlj, hik, Or.inr (Or.inr (Or.inr (hSymm k l h4)))⟩

private lemma mem_badTuples_swapPairs {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ x y, y ∈ N x → x ∈ N y) (t : Tuple4 n) :
    t ∈ badTuples N ↔ (t.2.2.1, t.2.2.2, t.1, t.2.1) ∈ badTuples N := by
  rcases t with ⟨i, k, j, l⟩
  exact ⟨mem_badTuples_swapPairs_imp hSymm, mem_badTuples_swapPairs_imp hSymm⟩

private lemma mem_badTuples_swapBoth {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ x y, y ∈ N x → x ∈ N y) (t : Tuple4 n) :
    t ∈ badTuples N ↔ (t.2.2.2, t.2.2.1, t.2.1, t.1) ∈ badTuples N := by
  rcases t with ⟨i, k, j, l⟩
  exact (mem_badTuples_swap12 hSymm (i, k, j, l)).trans
    ((mem_badTuples_swapPairs hSymm (k, i, j, l)).trans
      (mem_badTuples_swap12 hSymm (j, l, k, i)))

private lemma card_badTuples_coords_le {n : ℕ} {N : Fin n → Finset (Fin n)}
    (hSymm : ∀ x y, y ∈ N x → x ∈ N y) (v : Fin n) :
    let D_nat : ℕ := Finset.univ.sup fun x : Fin n ↦ (N x).card
    ((badTuples N).filter fun t ↦ t.1 = v).card ≤ 4 * D_nat ^ 3 ∧
      ((badTuples N).filter fun t ↦ t.2.1 = v).card ≤ 4 * D_nat ^ 3 ∧
      ((badTuples N).filter fun t ↦ t.2.2.1 = v).card ≤ 4 * D_nat ^ 3 ∧
      ((badTuples N).filter fun t ↦ t.2.2.2 = v).card ≤ 4 * D_nat ^ 3 := by
  intro D_nat
  have h1 : ((badTuples N).filter fun t ↦ t.1 = v).card ≤ 4 * D_nat ^ 3 :=
    card_badTuples_coord1_le hSymm v
  have h2_eq : ((badTuples N).filter fun t ↦ t.2.1 = v).card =
      ((badTuples N).filter fun t ↦ t.1 = v).card := by
    refine Finset.card_bijective (fun t : Tuple4 n ↦ (t.2.1, t.1, t.2.2.1, t.2.2.2)) ?_ ?_
    · exact Function.Involutive.bijective fun ⟨_, _, _, _⟩ ↦ rfl
    · intro t
      simp only [Finset.mem_filter]
      exact and_congr_left fun _ ↦ mem_badTuples_swap12 hSymm t
  have h3_eq : ((badTuples N).filter fun t ↦ t.2.2.1 = v).card =
      ((badTuples N).filter fun t ↦ t.1 = v).card := by
    refine Finset.card_bijective (fun t : Tuple4 n ↦ (t.2.2.1, t.2.2.2, t.1, t.2.1)) ?_ ?_
    · exact Function.Involutive.bijective fun ⟨_, _, _, _⟩ ↦ rfl
    · intro t
      simp only [Finset.mem_filter]
      exact and_congr_left fun _ ↦ mem_badTuples_swapPairs hSymm t
  have h4_eq : ((badTuples N).filter fun t ↦ t.2.2.2 = v).card =
      ((badTuples N).filter fun t ↦ t.1 = v).card := by
    refine Finset.card_bijective (fun t : Tuple4 n ↦ (t.2.2.2, t.2.2.1, t.2.1, t.1)) ?_ ?_
    · exact Function.Involutive.bijective fun ⟨_, _, _, _⟩ ↦ rfl
    · intro t
      simp only [Finset.mem_filter]
      exact and_congr_left fun _ ↦ mem_badTuples_swapBoth hSymm t
  exact ⟨h1, h2_eq.trans_le h1, h3_eq.trans_le h1, h4_eq.trans_le h1⟩

/-! ### Expectation and variance of $\sum_{i=1}^n \sum_{k \in N_i} X_i X_k$ -/

/-- Pairwise independence of $X_i$ and $X_k$ when $k \notin N_i$ under `IsDependencyGraph P X N`
(`SteinIntro.tex:810-812, 864-866`). -/
lemma IsDependencyGraph.indepFun_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hG : IsDependencyGraph P X N) {i k : Fin n} (hik : k ∉ N i) :
    ProbabilityTheory.IndepFun (X i) (X k) P := by
  have hAB : ∀ a ∈ ({i} : Finset (Fin n)), ∀ b ∈ ({k} : Finset (Fin n)), b ∉ N a := by
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha, Finset.mem_singleton.mp hb]
    exact hik
  exact (hG.2.2 {i} {k} hAB).comp
    (measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩)
    (measurable_pi_apply ⟨k, Finset.mem_singleton_self k⟩)

/-- Independence of $X_i X_k$ and $X_j X_l$ when $\{i, k\}$ and $\{j, l\}$ have no cross-edges
(`SteinIntro.tex:883-886`). -/
lemma IsDependencyGraph.indepFun_mul_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hG : IsDependencyGraph P X N) {i k j l : Fin n}
    (hdisj : ∀ a ∈ ({i, k} : Finset (Fin n)), ∀ b ∈ ({j, l} : Finset (Fin n)), b ∉ N a) :
    ProbabilityTheory.IndepFun (fun ω ↦ X i ω * X k ω) (fun ω ↦ X j ω * X l ω) P := by
  have hind := hG.2.2 {i, k} {j, l} hdisj
  have hi : i ∈ ({i, k} : Finset (Fin n)) := Finset.mem_insert_self i {k}
  have hk : k ∈ ({i, k} : Finset (Fin n)) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
  have hj : j ∈ ({j, l} : Finset (Fin n)) := Finset.mem_insert_self j {l}
  have hl : l ∈ ({j, l} : Finset (Fin n)) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self l)
  exact hind.comp
    ((measurable_pi_apply ⟨i, hi⟩).mul (measurable_pi_apply ⟨k, hk⟩))
    ((measurable_pi_apply ⟨j, hj⟩).mul (measurable_pi_apply ⟨l, hl⟩))

/-- Variance identity $\operatorname{Var}(\sum_i X_i) = \mathbb{E}[\sum_i \sum_{k \in N_i} X_i X_k]$
(`SteinIntro.tex:864-866`). -/
lemma depGraph_integral_quadSum_eq_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hX0 : ∀ i : Fin n, ∫ ω, X i ω ∂P = 0)
    (hG : IsDependencyGraph P X N) :
    (∫ ω, ∑ i : Fin n, ∑ k ∈ N i, X i ω * X k ω ∂P) =
      ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P := by
  have hsum_meas : AEMeasurable (fun ω ↦ ∑ i : Fin n, X i ω) P :=
    Finset.univ.aemeasurable_fun_sum fun i _ ↦ hX_meas i
  have hsum_int_zero : (∫ ω, ∑ i : Fin n, X i ω ∂P) = 0 := by
    rw [integral_finsetSum Finset.univ fun i _ ↦ depGraph_integrable_of_memLp_four (hX4 i)]
    simp [hX0]
  rw [ProbabilityTheory.variance_of_integral_eq_zero hsum_meas hsum_int_zero]
  have hsq_exp : (fun ω ↦ (∑ i : Fin n, X i ω) ^ 2) =
      fun ω ↦ ∑ i : Fin n, ∑ k : Fin n, X i ω * X k ω := by
    ext ω
    rw [sq, Fintype.sum_mul_sum]
  rw [hsq_exp]
  rw [integral_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  rw [integral_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum (N i) fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum (N i) fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  rw [integral_finsetSum Finset.univ fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
  refine Finset.sum_subset (Finset.subset_univ (N i)) fun k _ hk ↦ ?_
  rw [(hG.indepFun_pair hk).integral_fun_mul_eq_mul_integral
    (hX_meas i).aestronglyMeasurable (hX_meas k).aestronglyMeasurable]
  simp [hX0 i]

/-- Fourth-moment variance bound
$\operatorname{Var}(\sum_i \sum_{k \in N_i} X_i X_k) \le 13 D^3 \sum_{i=1}^n \mathbb{E}[X_i^4]$
(`SteinIntro.tex:868-906`, eqs. `(3.12)`–`(3.16)`). -/
theorem depGraph_variance_quadSum_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)}
    (hX_meas : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX4 : ∀ i : Fin n, MemLp (X i) 4 P)
    (hG : IsDependencyGraph P X N) :
    let D : ℝ := ((Finset.univ.sup fun i : Fin n ↦ (N i).card : ℕ) : ℝ)
    ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, ∑ k ∈ N i, X i ω * X k ω) P ≤
      13 * D ^ 3 * ∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P := by
  intro D
  let D_nat : ℕ := Finset.univ.sup fun i : Fin n ↦ (N i).card
  let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, ∑ k ∈ N i, X i ω * X k ω
  let m4 : Fin n → ℝ := fun v ↦ ∫ ω, X v ω ^ 4 ∂P
  have hm4_nonneg (v : Fin n) : 0 ≤ m4 v := integral_nonneg fun ω ↦ by positivity
  have hS_memLp2 : MemLp S 2 P :=
    memLp_finsetSum Finset.univ fun i _ ↦
      memLp_finsetSum (N i) fun k _ ↦ memLp_two_mul_of_memLp_four (hX4 i) (hX4 k)
  have hvar_sub : ProbabilityTheory.variance S P = (∫ ω, S ω ^ 2 ∂P) - (∫ ω, S ω ∂P) ^ 2 := by
    simpa only [Pi.pow_apply] using ProbabilityTheory.variance_eq_sub hS_memLp2
  have hS_sq_eq : (fun ω ↦ S ω ^ 2) =
      fun ω ↦ ∑ t ∈ allEdgeTuples N, X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω := by
    ext ω
    rw [sq, mul_dep_sum_eq_sum_allEdgeTuples]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    ring
  have hint_S_sq : (∫ ω, S ω ^ 2 ∂P) =
      ∑ t ∈ allEdgeTuples N, ∫ ω, X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω ∂P := by
    rw [hS_sq_eq]
    exact integral_finsetSum (allEdgeTuples N) fun t _ ↦
      integrable_mul_four (hX4 t.1) (hX4 t.2.1) (hX4 t.2.2.1) (hX4 t.2.2.2)
  have hint_S_eq : (∫ ω, S ω ∂P) = ∑ i : Fin n, ∑ k ∈ N i, ∫ ω, X i ω * X k ω ∂P := by
    dsimp only [S]
    rw [integral_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum (N i) fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact integral_finsetSum (N i) fun k _ ↦ integrable_mul_of_memLp_four (hX4 i) (hX4 k)
  have hmean_sq : (∫ ω, S ω ∂P) ^ 2 =
      ∑ t ∈ allEdgeTuples N,
        (∫ ω, X t.1 ω * X t.2.1 ω ∂P) * (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P) := by
    rw [sq, hint_S_eq, mul_dep_sum_eq_sum_allEdgeTuples]
  have hvar_all : ProbabilityTheory.variance S P =
      ∑ t ∈ allEdgeTuples N,
        ((∫ ω, X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω ∂P) -
          (∫ ω, X t.1 ω * X t.2.1 ω ∂P) * (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P)) := by
    rw [hvar_sub, hint_S_sq, hmean_sq, ← Finset.sum_sub_distrib]
  have hvar_bad : ProbabilityTheory.variance S P =
      ∑ t ∈ badTuples N,
        ((∫ ω, X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω ∂P) -
          (∫ ω, X t.1 ω * X t.2.1 ω ∂P) * (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P)) := by
    rw [hvar_all]
    refine (Finset.sum_subset (badTuples_subset_allEdgeTuples N) fun t ht hnot ↦ ?_).symm
    simp only [allEdgeTuples, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [badTuples, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    have hdisj : ∀ a ∈ ({t.1, t.2.1} : Finset (Fin n)),
        ∀ b ∈ ({t.2.2.1, t.2.2.2} : Finset (Fin n)), b ∉ N a := by
      intro a ha b hb hmem
      apply hnot
      refine ⟨ht.1, ht.2, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Or.inl hmem
      · exact Or.inr (Or.inl hmem)
      · exact Or.inr (Or.inr (Or.inl hmem))
      · exact Or.inr (Or.inr (Or.inr hmem))
    have hind := hG.indepFun_mul_pair hdisj
    have hmul_assoc : (fun ω ↦ X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω) =
        fun ω ↦ (X t.1 ω * X t.2.1 ω) * (X t.2.2.1 ω * X t.2.2.2 ω) := by
      ext ω
      ring
    rw [hmul_assoc, hind.integral_fun_mul_eq_mul_integral
      ((hX_meas t.1).aestronglyMeasurable.mul (hX_meas t.2.1).aestronglyMeasurable)
      ((hX_meas t.2.2.1).aestronglyMeasurable.mul (hX_meas t.2.2.2).aestronglyMeasurable)]
    ring
  have hterm_le (t : Tuple4 n) :
      (∫ ω, X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω ∂P) -
        (∫ ω, X t.1 ω * X t.2.1 ω ∂P) * (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P) ≤
        (m4 t.1 + m4 t.2.1 + m4 t.2.2.1 + m4 t.2.2.2) / 2 := by
    have hpart1 : (∫ ω, X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω ∂P) ≤
        (m4 t.1 + m4 t.2.1 + m4 t.2.2.1 + m4 t.2.2.2) / 4 := by
      have hdom : Integrable
          (fun ω ↦ (X t.1 ω ^ 4 + X t.2.1 ω ^ 4 + X t.2.2.1 ω ^ 4 + X t.2.2.2 ω ^ 4) / 4) P :=
        ((((integrable_pow_four (hX4 t.1)).fun_add (integrable_pow_four (hX4 t.2.1))).fun_add
          (integrable_pow_four (hX4 t.2.2.1))).fun_add
          (integrable_pow_four (hX4 t.2.2.2))).div_const 4
      have hle : (∫ ω, X t.1 ω * X t.2.1 ω * X t.2.2.1 ω * X t.2.2.2 ω ∂P) ≤
          ∫ ω, (X t.1 ω ^ 4 + X t.2.1 ω ^ 4 + X t.2.2.1 ω ^ 4 + X t.2.2.2 ω ^ 4) / 4 ∂P :=
        integral_mono (integrable_mul_four (hX4 t.1) (hX4 t.2.1) (hX4 t.2.2.1) (hX4 t.2.2.2))
          hdom fun ω ↦ mul_four_le (X t.1 ω) (X t.2.1 ω) (X t.2.2.1 ω) (X t.2.2.2 ω)
      have heval : (∫ ω, (X t.1 ω ^ 4 + X t.2.1 ω ^ 4 + X t.2.2.1 ω ^ 4 + X t.2.2.2 ω ^ 4) / 4 ∂P) =
          (m4 t.1 + m4 t.2.1 + m4 t.2.2.1 + m4 t.2.2.2) / 4 := by
        rw [integral_div, integral_add
          (((integrable_pow_four (hX4 t.1)).fun_add (integrable_pow_four (hX4 t.2.1))).fun_add
            (integrable_pow_four (hX4 t.2.2.1)))
          (integrable_pow_four (hX4 t.2.2.2)),
          integral_add
            ((integrable_pow_four (hX4 t.1)).fun_add (integrable_pow_four (hX4 t.2.1)))
            (integrable_pow_four (hX4 t.2.2.1)),
          integral_add (integrable_pow_four (hX4 t.1)) (integrable_pow_four (hX4 t.2.1))]
      exact hle.trans_eq heval
    have hpair_sq (a b : Fin n) : (∫ ω, X a ω * X b ω ∂P) ^ 2 ≤ (m4 a + m4 b) / 2 := by
      have hcs : (∫ ω, X a ω * X b ω ∂P) ^ 2 ≤ ∫ ω, (X a ω * X b ω) ^ 2 ∂P :=
        sq_integral_le_integral_sq (memLp_two_mul_of_memLp_four (hX4 a) (hX4 b))
      have hle2 : (∫ ω, (X a ω * X b ω) ^ 2 ∂P) ≤ ∫ ω, (X a ω ^ 4 + X b ω ^ 4) / 2 ∂P :=
        integral_mono (memLp_two_mul_of_memLp_four (hX4 a) (hX4 b)).integrable_sq
          (((integrable_pow_four (hX4 a)).fun_add (integrable_pow_four (hX4 b))).div_const 2)
          fun ω ↦ by
            rw [mul_pow]
            exact mul_sq_le_half_add_pow_four (X a ω) (X b ω)
      have heval2 : (∫ ω, (X a ω ^ 4 + X b ω ^ 4) / 2 ∂P) = (m4 a + m4 b) / 2 := by
        rw [integral_div, integral_add (integrable_pow_four (hX4 a)) (integrable_pow_four (hX4 b))]
      exact hcs.trans (hle2.trans_eq heval2)
    have hA := hpair_sq t.1 t.2.1
    have hB := hpair_sq t.2.2.1 t.2.2.2
    have hsq_ab : 0 ≤ ((∫ ω, X t.1 ω * X t.2.1 ω ∂P) + (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P)) ^ 2 :=
      sq_nonneg _
    have hid_ab :
        ((∫ ω, X t.1 ω * X t.2.1 ω ∂P) + (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P)) ^ 2 =
          (∫ ω, X t.1 ω * X t.2.1 ω ∂P) ^ 2 +
            2 * ((∫ ω, X t.1 ω * X t.2.1 ω ∂P) * (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P)) +
            (∫ ω, X t.2.2.1 ω * X t.2.2.2 ω ∂P) ^ 2 := by ring
    linarith
  have hproj_le (π : Tuple4 n → Fin n)
      (hcard_π : ∀ v : Fin n, ((badTuples N).filter fun t ↦ π t = v).card ≤ 4 * D_nat ^ 3) :
      (∑ t ∈ badTuples N, m4 (π t)) ≤ 4 * D ^ 3 * ∑ v : Fin n, m4 v := by
    rw [← Finset.sum_fiberwise' (badTuples N) π m4]
    calc ∑ v : Fin n, ∑ _t ∈ (badTuples N).filter (fun t ↦ π t = v), m4 v
        = ∑ v : Fin n, (((badTuples N).filter fun t ↦ π t = v).card : ℝ) * m4 v := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v : Fin n, (4 * D ^ 3) * m4 v := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          have hc : (((badTuples N).filter fun t ↦ π t = v).card : ℝ) ≤ 4 * D ^ 3 := by
            have hnat : (((badTuples N).filter fun t ↦ π t = v).card : ℝ) ≤
                ((4 * D_nat ^ 3 : ℕ) : ℝ) := Nat.cast_le.mpr (hcard_π v)
            simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hnat
          exact mul_le_mul_of_nonneg_right hc (hm4_nonneg v)
      _ = 4 * D ^ 3 * ∑ v : Fin n, m4 v := by rw [← Finset.mul_sum]
  have hc1 := hproj_le (fun t ↦ t.1) fun v ↦ (card_badTuples_coords_le hG.2.1 v).1
  have hc2 := hproj_le (fun t ↦ t.2.1) fun v ↦ (card_badTuples_coords_le hG.2.1 v).2.1
  have hc3 := hproj_le (fun t ↦ t.2.2.1) fun v ↦ (card_badTuples_coords_le hG.2.1 v).2.2.1
  have hc4 := hproj_le (fun t ↦ t.2.2.2) fun v ↦ (card_badTuples_coords_le hG.2.1 v).2.2.2
  have hsum_bad : ProbabilityTheory.variance S P ≤
      ∑ t ∈ badTuples N, (m4 t.1 + m4 t.2.1 + m4 t.2.2.1 + m4 t.2.2.2) / 2 := by
    rw [hvar_bad]
    exact Finset.sum_le_sum fun t _ ↦ hterm_le t
  have hsplit_bad :
      (∑ t ∈ badTuples N, (m4 t.1 + m4 t.2.1 + m4 t.2.2.1 + m4 t.2.2.2) / 2) =
        ((∑ t ∈ badTuples N, m4 t.1) + (∑ t ∈ badTuples N, m4 t.2.1) +
          (∑ t ∈ badTuples N, m4 t.2.2.1) + (∑ t ∈ badTuples N, m4 t.2.2.2)) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    simp_rw [Finset.sum_add_distrib]
  have hD3_nonneg : 0 ≤ D ^ 3 := pow_nonneg (Nat.cast_nonneg _) 3
  have hm4_sum_nonneg : 0 ≤ ∑ v : Fin n, m4 v := Finset.sum_nonneg fun v _ ↦ hm4_nonneg v
  have h8_le_13 : 8 * D ^ 3 * (∑ v : Fin n, m4 v) ≤ 13 * D ^ 3 * (∑ v : Fin n, m4 v) := by
    nlinarith
  linarith

end SteinMethod
