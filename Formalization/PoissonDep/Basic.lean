/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.PoissonDep
import Formalization.Metrics.Basic
import Formalization.Poisson.SteinBounds
import Formalization.Poisson.SteinCore
import Mathlib.Probability.Independence.Integration

/-!
# Poisson Chen–Stein Class, Sanity Witnesses, and Law of Small Numbers
(`Formalization.PoissonDep.Basic`)

Covers the opening of Section 4 after Lemma 4.4 and Section 4.1 of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:1887-1966`):

* Non-vacuity sanity witnesses for all definitions in `Formalization.Defs.PoissonDep`
  (`poissonSteinClass`, `headRunIndicator`, `headRunCount`, `longestQualityRun`,
  `klDivBernoulli`).
* Reusable `{0, 1}`-indicator, `poissonLaw 0`, and telescoping `fwdDiff 1` helper lemmas.
* **Theorem 4.5** (`\label{thm101}`, eq. `(4.4)` `\label{1019}`, `SteinIntro.tex:1911-1916`):
  `tvDist_le_iSup_poissonSteinClass` and `tvDist_map_le_iSup_poissonSteinClass`.
* **Theorem 4.6** (`\label{thm102}`, `SteinIntro.tex:1942-1949`; `ISSUE-TYPO-4.6`):
  `tvDist_sum_indep_indicator_le`.
* **Section 4.1 binomial limit** (`SteinIntro.tex:1938-1939`):
  `tendsto_tvDist_binomial_poissonLaw`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Non-vacuity witnesses for `Formalization.Defs.PoissonDep` -/

/-- Canonical Chen–Stein solutions belong to `poissonSteinClass r` for `r > 0`
(Lemma 4.4 `\label{lem103}`, `SteinIntro.tex:1879-1886`; non-vacuity witness for
`poissonSteinClass`). -/
theorem poissonSteinSol_mem_poissonSteinClass {r : ℝ≥0} (hr : 0 < r) (A : Set ℕ) :
    poissonSteinSol r A ∈ poissonSteinClass r :=
  ⟨abs_poissonSteinSol_le hr A, abs_fwdDiff_poissonSteinSol_le hr A⟩

/-- Non-vacuity witness for `headRunIndicator` (`SteinIntro.tex:2013-2021`): on `![1, 1, 0, 1]`
with threshold `k = 2`, a run of length at least `2` starts at index `0` and not at index `1`. -/
theorem headRunIndicator_nonvacuous :
    headRunIndicator 2 (![1, 1, 0, 1] : Fin 4 → ℕ) 0 = 1 ∧
      headRunIndicator 2 (![1, 1, 0, 1] : Fin 4 → ℕ) 1 = 0 := by
  constructor <;> decide

/-- Non-vacuity witness for `headRunCount` (`SteinIntro.tex:2010-2021`): `![1, 1, 0, 1, 1]` has
`2` de-clumped runs of ones of length at least `2`. -/
theorem headRunCount_nonvacuous :
    headRunCount 2 (![1, 1, 0, 1, 1] : Fin 5 → ℕ) = 2 := by
  decide

/-- Non-vacuity witness for `longestQualityRun` (`SteinIntro.tex:2055, 2066-2072`): the longest
run of ones (`a = 1`) in `![1, 1, 0, 1]` has length `2`. -/
theorem longestQualityRun_nonvacuous :
    longestQualityRun 1 (![1, 1, 0, 1] : Fin 4 → ℕ) = 2 := by
  unfold longestQualityRun
  classical
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, ?_, ?_⟩
  · intro _
    refine ⟨0, by omega, ?_⟩
    simp only [Fin.sum_univ_two]
    norm_num
  · rintro j hlt hle ⟨i, hij, hsum⟩
    have hj34 : j = 3 ∨ j = 4 := by omega
    rcases hj34 with rfl | rfl
    · have hi01 : i = 0 ∨ i = 1 := by omega
      rcases hi01 with rfl | rfl
      · simp only [Fin.sum_univ_three] at hsum
        norm_num at hsum
      · simp only [Fin.sum_univ_three] at hsum
        norm_num at hsum
    · have hi0 : i = 0 := by omega
      subst hi0
      simp only [Fin.sum_univ_four] at hsum
      norm_num at hsum

/-- Strict positivity of the binary relative entropy `klDivBernoulli a p` for `0 < p < a ≤ 1`
(Theorem 4.9, `SteinIntro.tex:2071-2078`; non-vacuity witness for `klDivBernoulli`). -/
theorem klDivBernoulli_pos {a p : ℝ} (hp : 0 < p) (hpa : p < a) (ha : a ≤ 1) :
    0 < klDivBernoulli a p := by
  have ha_pos : 0 < a := hp.trans hpa
  unfold klDivBernoulli
  split_ifs with ha1
  · subst ha1
    exact Real.log_pos (one_lt_one_div hp hpa)
  · have ha_lt : a < 1 := lt_of_le_of_ne ha ha1
    have h1a : 0 < 1 - a := sub_pos.mpr ha_lt
    have h1p : 0 < 1 - p := sub_pos.mpr (hpa.trans ha_lt)
    have hlog1 : Real.log (p / a) < p / a - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos hp ha_pos) (div_ne_one_of_ne hpa.ne)
    have hlog2 : Real.log ((1 - p) / (1 - a)) < (1 - p) / (1 - a) - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos h1p h1a) (div_ne_one_of_ne (by linarith))
    have hinv1 : Real.log (a / p) = -Real.log (p / a) := by
      rw [← inv_div, Real.log_inv]
    have hinv2 : Real.log ((1 - a) / (1 - p)) = -Real.log ((1 - p) / (1 - a)) := by
      rw [← inv_div, Real.log_inv]
    have ht1 : a - p < a * Real.log (a / p) := by
      rw [hinv1]
      have hm := mul_lt_mul_of_pos_left hlog1 ha_pos
      have hsimp : a * (p / a - 1) = p - a := by field_simp
      linarith
    have ht2 : p - a < (1 - a) * Real.log ((1 - a) / (1 - p)) := by
      rw [hinv2]
      have hm := mul_lt_mul_of_pos_left hlog2 h1a
      have hsimp : (1 - a) * ((1 - p) / (1 - a) - 1) = a - p := by field_simp; ring
      linarith
    linarith

/-! ### Reusable `fwdDiff`, `poissonLaw 0`, and `{0, 1}`-indicator helpers -/

/-- For `r > 0`, every `f ∈ poissonSteinClass r` satisfies the outer forward-difference bound
`|Δ f(k)| ≤ min(1, r⁻¹)` (`SteinIntro.tex:1881-1884`). -/
theorem abs_fwdDiff_le_min_of_mem_poissonSteinClass {r : ℝ≥0} (hr : 0 < r) {f : ℕ → ℝ}
    (hf : f ∈ poissonSteinClass r) (k : ℕ) :
    |fwdDiff 1 f k| ≤ min 1 (r : ℝ)⁻¹ :=
  (hf.2 k).trans (one_sub_exp_neg_div_le_min hr)

/-- Telescoping bound on `|f b - f a|` from a uniform first-difference bound `|fwdDiff 1 f k| ≤ M`
(`SteinIntro.tex:1999`). -/
theorem abs_sub_le_of_abs_fwdDiff_le {f : ℕ → ℝ} {M : ℝ} (_hM : 0 ≤ M)
    (hf : ∀ k : ℕ, |fwdDiff 1 f k| ≤ M) (a b : ℕ) :
    |f b - f a| ≤ M * |(b : ℝ) - (a : ℝ)| := by
  have aux : ∀ m d : ℕ, |f (m + d) - f m| ≤ M * (d : ℝ) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have hsplit : f (m + (d + 1)) - f m = (f (m + d) - f m) + fwdDiff 1 f (m + d) := by
        simp only [fwdDiff]
        ring_nf
      calc |f (m + (d + 1)) - f m|
        _ = |(f (m + d) - f m) + fwdDiff 1 f (m + d)| := by rw [hsplit]
        _ ≤ |f (m + d) - f m| + |fwdDiff 1 f (m + d)| := abs_add_le _ _
        _ ≤ M * (d : ℝ) + M := add_le_add ih (hf (m + d))
        _ = M * ((d + 1 : ℕ) : ℝ) := by push_cast; ring
  rcases le_total a b with hab | hba
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    have hdiff : |(↑(a + d) : ℝ) - (a : ℝ)| = (d : ℝ) := by
      have heq : ((a + d : ℕ) : ℝ) - (a : ℝ) = (d : ℝ) := by push_cast; ring
      rw [heq, abs_of_nonneg (Nat.cast_nonneg d)]
    rw [hdiff]
    exact aux a d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
    have hdiff : |(b : ℝ) - (↑(b + d) : ℝ)| = (d : ℝ) := by
      have heq : (b : ℝ) - ((b + d : ℕ) : ℝ) = -(d : ℝ) := by push_cast; ring
      rw [heq, abs_neg, abs_of_nonneg (Nat.cast_nonneg d)]
    rw [abs_sub_comm, hdiff]
    exact aux b d

/-- Degenerate Poisson law `Po(0)` equals the point mass `Measure.dirac 0` at `0`. -/
theorem poissonLaw_zero_eq_dirac : poissonLaw 0 = Measure.dirac 0 := by
  refine Measure.ext_of_measureReal_singleton fun k ↦ ?_
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  cases k with
  | zero => simp [measureReal_def]
  | succ m => simp [pow_succ, measureReal_def, Measure.dirac_apply' _ .of_discrete]

/-- A `{0, 1}`-valued `AEMeasurable` random variable is integrable after casting to `ℝ`. -/
theorem integrable_natCast_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℕ}
    (hX : AEMeasurable X P) (hX01 : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) :
    Integrable (fun ω ↦ (X ω : ℝ)) P := by
  refine Integrable.of_mem_Icc 0 1
    ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hX) ?_
  filter_upwards [hX01] with ω hω
  rcases hω with h | h <;> simp [h]

/-- Expectation of a `{0, 1}`-valued `AEMeasurable` random variable equals
`P.real {ω | X ω = 1}`. -/
theorem integral_natCast_of_ae_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℕ}
    (hX : AEMeasurable X P) (hX01 : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1) :
    ∫ ω, (X ω : ℝ) ∂P = P.real {ω | X ω = 1} := by
  let ind1 : ℕ → ℝ := ({1} : Set ℕ).indicator 1
  have hae : (fun ω ↦ (X ω : ℝ)) =ᵐ[P] fun ω ↦ ind1 (X ω) := by
    filter_upwards [hX01] with ω hω
    rcases hω with h | h <;> simp [ind1, h]
  calc ∫ ω, (X ω : ℝ) ∂P
    _ = ∫ ω, ind1 (X ω) ∂P := integral_congr_ae hae
    _ = ∫ k, ind1 k ∂(P.map X) := (integral_map hX .of_discrete).symm
    _ = (P.map X).real {1} := integral_indicator_one .of_discrete
    _ = P.real {ω | X ω = 1} := map_measureReal_apply_of_aemeasurable hX .of_discrete

/-- If a `{0, 1}`-indicator has `P.real {ω | X ω = 1} = 0`, then `X = 0` almost surely. -/
theorem ae_eq_zero_of_ae_zero_or_one_of_probReal_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℕ}
    (hX : AEMeasurable X P) (hX01 : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1)
    (hp0 : P.real {ω | X ω = 1} = 0) :
    ∀ᵐ ω ∂P, X ω = 0 := by
  have hmap0 : (P.map X).real {1} = 0 := by
    rw [map_measureReal_apply_of_aemeasurable hX .of_discrete]
    exact hp0
  have : IsProbabilityMeasure (P.map X) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hX .univ, Set.preimage_univ, measure_univ]⟩
  have hm0 : (P.map X) {1} = 0 :=
    (measureReal_eq_zero_iff (h := measure_ne_top _ _)).mp hmap0
  have hpre0 : P (X ⁻¹' {1}) = 0 := by
    rwa [Measure.map_apply_of_aemeasurable hX .of_discrete] at hm0
  have hne1 : ∀ᵐ ω ∂P, X ω ≠ 1 := by
    rw [ae_iff]
    have hset : {a : Ω | ¬X a ≠ 1} = X ⁻¹' {1} := by
      ext a
      simp
    rw [hset]
    exact hpre0
  filter_upwards [hX01, hne1] with ω hω h1
  rcases hω with h0 | h1'
  · exact h0
  · exact absurd h1' h1

/-- If `W = ∑ i, X i` is a finite sum of `{0, 1}`-indicators with total success probability `0`,
then `P.map W = poissonLaw 0`. -/
theorem map_sum_eq_poissonLaw_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {X : Fin n → Ω → ℕ}
    (hX : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hsum0 : (∑ i : Fin n, P.real {ω | X i ω = 1}) = 0) :
    P.map (fun ω ↦ ∑ i : Fin n, X i ω) = poissonLaw 0 := by
  have hp0 : ∀ i : Fin n, P.real {ω | X i ω = 1} = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ measureReal_nonneg).mp hsum0
    exact fun i ↦ hall i (Finset.mem_univ i)
  have hXi0 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 :=
    fun i ↦ ae_eq_zero_of_ae_zero_or_one_of_probReal_eq_zero (hX i) (hX01 i) (hp0 i)
  have hW0 : (fun ω ↦ ∑ i : Fin n, X i ω) =ᵐ[P] fun _ ↦ 0 := by
    filter_upwards [ae_all_iff.mpr hXi0] with ω hω
    simp [hω]
  rw [Measure.map_congr hW0, Measure.map_const, measure_univ, one_smul, poissonLaw_zero_eq_dirac]

/-! ### Theorem 4.5: Total-Variation Bound via `poissonSteinClass` -/

/-- **Theorem 4.5** (`\label{thm101}`, eq. `(4.4)` `\label{1019}`, `SteinIntro.tex:1911-1916`,
without moment hypothesis): for `0 < r` and any `AEMeasurable` `W : Ω → ℕ`,
`tvDist (P.map W) (poissonLaw r)` is bounded by the supremum of `|𝔼[r f(W + 1) - W f(W)]|` over
`f ∈ poissonSteinClass r`.

*Reading note (`stmts-review-05C` C3)*: `poissonSteinClass r` uses the sharp Lemma 4.4 `(4.2)`
bound `(1 - e^{-r}) / r` on `|Δ f|` (which is a subset of the outer `min(1, r⁻¹)` class, giving a
stronger upper bound in `(4.4)`), and `0 < r` is typing because `(4.2)` divides by `r`. -/
theorem tvDist_le_iSup_poissonSteinClass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} (hr : 0 < r) {W : Ω → ℕ} (hW : AEMeasurable W P) :
    tvDist (P.map W) (poissonLaw r) ≤
      ⨆ f ∈ poissonSteinClass r, ENNReal.ofReal |∫ ω, poissonSteinOp r f (W ω) ∂P| := by
  have : IsProbabilityMeasure (P.map W) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hW .univ, Set.preimage_univ, measure_univ]⟩
  rw [tvDist_eq_iSup]
  refine iSup₂_le fun A hA ↦ ?_
  rw [map_measureReal_apply_of_aemeasurable hW hA]
  have hid := abs_measureReal_sub_poissonLaw_eq P hr hW A
  change ENNReal.ofReal |P.real {ω | W ω ∈ A} - (poissonLaw r).real A| ≤ _
  rw [hid]
  exact le_iSup₂_of_le (poissonSteinSol r A) (poissonSteinSol_mem_poissonSteinClass hr A) le_rfl

/-- **Theorem 4.5** (`\label{thm101}`, eq. `(4.4)` `\label{1019}`, `SteinIntro.tex:1911-1916`):
random-variable-level statement with `Z` having law `poissonLaw r` (`r > 0`). -/
theorem tvDist_map_le_iSup_poissonSteinClass
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {r : ℝ≥0} {W : Ω → ℕ} {Z : Ω' → ℕ}
    (hr : 0 < r) (hW : AEMeasurable W P)
    (_hInt : Integrable (fun ω ↦ (W ω : ℝ)) P)
    (_hMean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ))
    (_hZ : AEMeasurable Z P') (hlaw : P'.map Z = poissonLaw r) :
    tvDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ poissonSteinClass r, ENNReal.ofReal |∫ ω, poissonSteinOp r f (W ω) ∂P| := by
  rw [hlaw]
  exact tvDist_le_iSup_poissonSteinClass P hr hW

/-! ### Theorem 4.6 & Section 4.1: Law of Small Numbers -/

private lemma aemeasurable_finset_sum_nat {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ι) {X : ι → Ω → ℕ} (hX : ∀ i ∈ s, AEMeasurable (X i) P) :
    AEMeasurable (fun ω ↦ ∑ i ∈ s, X i ω) P := by
  classical
  induction s using Finset.induction with
  | empty => exact aemeasurable_const
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hX a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hX i (Finset.mem_insert_of_mem hi))

private lemma min_one_inv_mul_le_min_one (r : ℝ≥0) :
    min 1 (r : ℝ)⁻¹ * (r : ℝ) ≤ min 1 (r : ℝ) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with rfl | hr
  · simp
  · have hr' : (0 : ℝ) < r := by positivity
    rcases le_total (r : ℝ) 1 with hr1 | h1r
    · have hinv : 1 ≤ (r : ℝ)⁻¹ := one_le_inv₀ hr' |>.mpr hr1
      rw [min_eq_left hinv, one_mul, min_eq_right hr1]
    · have hinv : (r : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1r
      rw [min_eq_right hinv, inv_mul_cancel₀ hr'.ne', min_eq_left h1r]

/-- **Theorem 4.6** (`\label{thm102}`, `SteinIntro.tex:1942-1949`; `ISSUE-TYPO-4.6`):
total-variation Poisson approximation bound for a sum of independent `{0, 1}`-indicators. -/
theorem tvDist_sum_indep_indicator_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℕ} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hX : ∀ i : Fin n, AEMeasurable (X i) P)
    (hX01 : ∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hr_sum : (r : ℝ) = ∑ i : Fin n, P.real {ω | X i ω = 1})
    (_hZ : AEMeasurable Z P')
    (hlaw : P'.map Z = poissonLaw r) :
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal (min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2) ∧
      min 1 (r : ℝ)⁻¹ * (∑ i : Fin n, p i ^ 2) ≤
        min 1 (r : ℝ) * Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ p := by
  intro p W
  have halg : min 1 (r : ℝ)⁻¹ * (∑ i : Fin n, p i ^ 2) ≤
      min 1 (r : ℝ) * Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ p := by
    set M := Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ p
    have hM_nonneg : 0 ≤ M :=
      le_trans (measureReal_nonneg : 0 ≤ p ⟨0, hn⟩)
        (Finset.le_sup' p (Finset.mem_univ ⟨0, hn⟩))
    have hsum_sq : ∑ i : Fin n, p i ^ 2 ≤ (r : ℝ) * M := by
      rw [hr_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' p hi) measureReal_nonneg
    have hmin_nn : 0 ≤ min 1 (r : ℝ)⁻¹ := le_min zero_le_one (inv_nonneg.mpr r.coe_nonneg)
    calc min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2
      _ ≤ min 1 (r : ℝ)⁻¹ * ((r : ℝ) * M) := mul_le_mul_of_nonneg_left hsum_sq hmin_nn
      _ = (min 1 (r : ℝ)⁻¹ * (r : ℝ)) * M := by ring
      _ ≤ min 1 (r : ℝ) * M := mul_le_mul_of_nonneg_right (min_one_inv_mul_le_min_one r) hM_nonneg
  refine ⟨?_, halg⟩
  rw [hlaw]
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with rfl | hr_pos
  · have hmap := map_sum_eq_poissonLaw_zero hX hX01 hr_sum.symm
    rw [show W = fun ω ↦ ∑ i : Fin n, X i ω from rfl, hmap, tvDist, ipm_self]
    exact zero_le
  · have hW_meas : AEMeasurable W P :=
      aemeasurable_finset_sum_nat Finset.univ fun i _ ↦ hX i
    refine (tvDist_le_iSup_poissonSteinClass P hr_pos hW_meas).trans (iSup₂_le fun f hf ↦ ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    let Wi : Fin n → Ω → ℕ := fun i ω ↦ ∑ j ∈ Finset.univ.erase i, X j ω
    have hWi_meas : ∀ i : Fin n, AEMeasurable (Wi i) P :=
      fun i ↦ aemeasurable_finset_sum_nat (Finset.univ.erase i) fun j _ ↦ hX j
    have hf_bdd : ∀ k : ℕ, |f k| ≤ min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) := hf.1
    have hf_diff : ∀ k : ℕ, |fwdDiff 1 f k| ≤ min 1 (r : ℝ)⁻¹ :=
      abs_fwdDiff_le_min_of_mem_poissonSteinClass hr_pos hf
    let C := min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))
    have hC_nn : 0 ≤ C := le_min zero_le_one (Real.rpow_nonneg r.coe_nonneg _)
    have hInt_fW : Integrable (fun ω ↦ f (W ω + 1)) P :=
      Integrable.of_mem_Icc (-C) C
        ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable hW_meas)
        (Eventually.of_forall fun ω ↦ abs_le.mp (hf_bdd (W ω + 1)))
    have hInt_fWi : ∀ i : Fin n, Integrable (fun ω ↦ f (Wi i ω + 1)) P := fun i ↦
      Integrable.of_mem_Icc (-C) C
        ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable (hWi_meas i))
        (Eventually.of_forall fun ω ↦ abs_le.mp (hf_bdd (Wi i ω + 1)))
    have hInt_XifWi : ∀ i : Fin n, Integrable (fun ω ↦ (X i ω : ℝ) * f (Wi i ω + 1)) P := by
      intro i
      refine Integrable.of_mem_Icc (-C) C
        (((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable (hX i)).mul
          ((Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp_aemeasurable
            (hWi_meas i))) ?_
      filter_upwards [hX01 i] with ω hω
      rw [Set.mem_Icc, ← abs_le]
      rcases hω with h0 | h1
      · simp [h0, hC_nn]
      · rw [h1, Nat.cast_one, one_mul]
        exact hf_bdd (Wi i ω + 1)
    have hW_split : ∀ i : Fin n, ∀ ω, W ω = X i ω + Wi i ω := fun i ω ↦
      (Finset.add_sum_erase Finset.univ (fun j ↦ X j ω) (Finset.mem_univ i)).symm
    have h_op_ae : (fun ω ↦ poissonSteinOp r f (W ω)) =ᵐ[P]
        fun ω ↦ ∑ i : Fin n, (p i * f (W ω + 1) - (X i ω : ℝ) * f (Wi i ω + 1)) := by
      filter_upwards [ae_all_iff.mpr hX01] with ω hω
      simp only [poissonSteinOp, hr_sum, Finset.sum_mul, Finset.sum_sub_distrib]
      congr 1
      change ((∑ i : Fin n, X i ω : ℕ) : ℝ) * f (W ω) = _
      rw [Nat.cast_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rcases hω i with h0 | h1
      · simp [h0]
      · rw [hW_split i ω, h1, add_comm 1 (Wi i ω)]
    have hInt_summand : ∀ i : Fin n,
        Integrable (fun ω ↦ p i * f (W ω + 1) - (X i ω : ℝ) * f (Wi i ω + 1)) P :=
      fun i ↦ (hInt_fW.const_mul (p i)).sub (hInt_XifWi i)
    rw [integral_congr_ae h_op_ae, integral_finsetSum Finset.univ fun i _ ↦ hInt_summand i]
    have h_term : ∀ i : Fin n,
        ∫ ω, (p i * f (W ω + 1) - (X i ω : ℝ) * f (Wi i ω + 1)) ∂P =
          p i * ∫ ω, (f (W ω + 1) - f (Wi i ω + 1)) ∂P := by
      intro i
      rw [integral_sub (hInt_fW.const_mul (p i)) (hInt_XifWi i), integral_const_mul]
      have hdisj : Disjoint ({i} : Finset (Fin n)) (Finset.univ.erase i) :=
        Finset.disjoint_singleton_left.mpr (Finset.notMem_erase i Finset.univ)
      have hind_tup := hIndep.indepFun_finset₀ ({i} : Finset (Fin n)) (Finset.univ.erase i)
        hdisj hX
      have hφ : Measurable fun u : ({i} : Finset (Fin n)) → ℕ ↦
          (u ⟨i, Finset.mem_singleton_self i⟩ : ℝ) :=
        (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp (measurable_pi_apply _)
      have hψ : Measurable fun v : (Finset.univ.erase i) → ℕ ↦
          f ((∑ b : Finset.univ.erase i, v b) + 1) :=
        (Measurable.of_discrete : Measurable fun k : ℕ ↦ f (k + 1)).comp
          (Finset.measurable_sum Finset.univ fun b _ ↦ measurable_pi_apply b)
      have hind_fun : IndepFun (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ f (Wi i ω + 1)) P := by
        have hcomp := hind_tup.comp hφ hψ
        have heq_Wi : (fun x ↦ f ((∑ b : Finset.univ.erase i, X b.1 x) + 1)) =
            fun ω ↦ f (Wi i ω + 1) := by
          ext x
          rw [Finset.sum_coe_sort (Finset.univ.erase i) (fun j ↦ X j x)]
        simpa only [Function.comp_def, heq_Wi] using hcomp
      have hmul : ∫ ω, (X i ω : ℝ) * f (Wi i ω + 1) ∂P =
          (∫ ω, (X i ω : ℝ) ∂P) * ∫ ω, f (Wi i ω + 1) ∂P :=
        hind_fun.integral_mul_eq_mul_integral
          ((integrable_natCast_of_ae_zero_or_one (hX i) (hX01 i)).aestronglyMeasurable)
          (hInt_fWi i).aestronglyMeasurable
      rw [hmul, integral_natCast_of_ae_zero_or_one (hX i) (hX01 i), ← mul_sub,
        ← integral_sub hInt_fW (hInt_fWi i)]
    calc |∑ i : Fin n, ∫ ω, (p i * f (W ω + 1) - (X i ω : ℝ) * f (Wi i ω + 1)) ∂P|
      _ ≤ ∑ i : Fin n, |∫ ω, (p i * f (W ω + 1) - (X i ω : ℝ) * f (Wi i ω + 1)) ∂P| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, p i * (min 1 (r : ℝ)⁻¹ * p i) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [h_term i, abs_mul, abs_of_nonneg measureReal_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
        have hae_diff : ∀ᵐ ω ∂P, ‖f (W ω + 1) - f (Wi i ω + 1)‖ ≤
            min 1 (r : ℝ)⁻¹ * (X i ω : ℝ) := by
          filter_upwards [hX01 i] with ω hω
          rw [Real.norm_eq_abs]
          rcases hω with h0 | h1
          · rw [hW_split i ω, h0, zero_add, sub_self, abs_zero, Nat.cast_zero, mul_zero]
          · rw [hW_split i ω, h1, Nat.cast_one, mul_one]
            have heq : 1 + Wi i ω + 1 = (Wi i ω + 1) + 1 := by omega
            rw [heq]
            exact hf_diff (Wi i ω + 1)
        calc |∫ ω, (f (W ω + 1) - f (Wi i ω + 1)) ∂P|
          _ = ‖∫ ω, (f (W ω + 1) - f (Wi i ω + 1)) ∂P‖ := (Real.norm_eq_abs _).symm
          _ ≤ ∫ ω, ‖f (W ω + 1) - f (Wi i ω + 1)‖ ∂P := norm_integral_le_integral_norm _
          _ ≤ ∫ ω, min 1 (r : ℝ)⁻¹ * (X i ω : ℝ) ∂P :=
            integral_mono_ae (hInt_fW.sub (hInt_fWi i)).norm
              ((integrable_natCast_of_ae_zero_or_one (hX i) (hX01 i)).const_mul _) hae_diff
          _ = min 1 (r : ℝ)⁻¹ * p i := by
            rw [integral_const_mul, integral_natCast_of_ae_zero_or_one (hX i) (hX01 i)]
      _ = min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring

/-- **Section 4.1 binomial limit** (`SteinIntro.tex:1938-1939`): for `W_n ~ Bi(n, r / n)`,
`tvDist ((P n).map (W_n)) (poissonLaw r) ≤ min(1, r) * (r / n)` for `n ≥ max(1, r)`, and hence
`tvDist ((P n).map (W_n)) (poissonLaw r) → 0` as `n → ∞`. -/
theorem tendsto_tvDist_binomial_poissonLaw
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {r : ℝ≥0} {X : ∀ n, Fin n → Ω n → ℕ}
    (hX : ∀ n : ℕ, 0 < n → (r : ℝ) ≤ (n : ℝ) →
      (∀ i : Fin n, AEMeasurable (X n i) (P n)) ∧
      (∀ i : Fin n, ∀ᵐ ω ∂P n, X n i ω = 0 ∨ X n i ω = 1) ∧
      ProbabilityTheory.iIndepFun (X n) (P n) ∧
      (∀ i : Fin n, (P n).real {ω | X n i ω = 1} = (r : ℝ) / (n : ℝ))) :
    let W : ∀ n, Ω n → ℕ := fun n ω ↦ ∑ i : Fin n, X n i ω
    (∀ n : ℕ, 0 < n → (r : ℝ) ≤ (n : ℝ) →
      tvDist ((P n).map (W n)) (poissonLaw r) ≤
        ENNReal.ofReal (min 1 (r : ℝ) * ((r : ℝ) / (n : ℝ)))) ∧
    Filter.Tendsto (fun n : ℕ ↦ tvDist ((P n).map (W n)) (poissonLaw r))
      Filter.atTop (nhds 0) := by
  intro W
  have hbound : ∀ n : ℕ, 0 < n → (r : ℝ) ≤ (n : ℝ) →
      tvDist ((P n).map (W n)) (poissonLaw r) ≤
        ENNReal.ofReal (min 1 (r : ℝ) * ((r : ℝ) / (n : ℝ))) := by
    intro n hn hrn
    obtain ⟨hmeas, h01, hind, hp⟩ := hX n hn hrn
    have hr_sum : (r : ℝ) = ∑ i : Fin n, (P n).real {ω | X n i ω = 1} := by
      have hcongr : ∑ i : Fin n, (P n).real {ω | X n i ω = 1} =
          ∑ _i : Fin n, (r : ℝ) / (n : ℝ) := Finset.sum_congr rfl fun i _ ↦ hp i
      rw [hcongr, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ (by positivity)]
    have hthm := tvDist_sum_indep_indicator_le (P n) (poissonLaw r) hn hmeas h01 hind hr_sum
      aemeasurable_id Measure.map_id
    have hsup : Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
        (fun i : Fin n ↦ (P n).real {ω | X n i ω = 1}) = (r : ℝ) / (n : ℝ) := by
      apply le_antisymm
      · exact Finset.sup'_le _ _ fun i _ ↦ (hp i).le
      · exact (hp ⟨0, hn⟩).symm.trans_le
          (Finset.le_sup' (fun i : Fin n ↦ (P n).real {ω | X n i ω = 1})
            (Finset.mem_univ ⟨0, hn⟩))
    rw [Measure.map_id] at hthm
    exact hthm.1.trans (ENNReal.ofReal_le_ofReal (hsup ▸ hthm.2))
  refine ⟨hbound, ?_⟩
  have hreal_lim : Filter.Tendsto (fun n : ℕ ↦ min 1 (r : ℝ) * ((r : ℝ) / (n : ℝ)))
      Filter.atTop (nhds 0) := by
    have hdiv : Filter.Tendsto (fun n : ℕ ↦ (r : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using hdiv.const_mul (min 1 (r : ℝ))
  have henn_lim : Filter.Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (min 1 (r : ℝ) * ((r : ℝ) / (n : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal_lim)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henn_lim
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (r : ℝ) + 1)] with n hn
  have hn_pos : 0 < n := by omega
  have hrn : (r : ℝ) ≤ (n : ℝ) :=
    (Nat.le_ceil (r : ℝ)).trans (by exact_mod_cast (by omega : Nat.ceil (r : ℝ) ≤ n))
  exact hbound n hn_pos hrn

end SteinMethod
