/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonDep.LocalDependence

/-!
# Head Runs in Coin Tossing and DNA Sequence Matching (`Formalization.PoissonDep.HeadRuns`)

Covers Section 4.2.1 (`SteinIntro.tex:2006-2061, 2079-2110`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`): `C2` index sanity checks,
`{W = 0} ↔ {R_n < k}`, **Theorem 4.8** (`tvDist_headRunCount_le`), and **Remark 4.3**
(`dna_match_iIndepFun_and_prob`, `dna_match_map_eq_pi`).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### C2: Longest-run-of-ones characterization & index sanity checks -/

open Classical in
/-- For a `{0, 1}`-valued sequence `y : Fin n → ℕ`, `longestQualityRun 1 y` equals the greatest
`j ≤ n` for which `y` contains `j` consecutive ones (`SteinIntro.tex:2055, 2066-2072`;
`stmts-review-05C` C2). -/
theorem longestQualityRun_one_eq_findGreatest_ones {n : ℕ} {y : Fin n → ℕ}
    (hy : ∀ i : Fin n, y i = 0 ∨ y i = 1) :
    longestQualityRun 1 y =
      Nat.findGreatest
        (fun j ↦ ∃ i : ℕ, ∃ h : i + j ≤ n, ∀ r : Fin j, y ⟨i + r.1, by omega⟩ = 1) n := by
  unfold longestQualityRun
  classical
  have hiff : ∀ j : ℕ,
      (∃ i : ℕ, ∃ h : i + j ≤ n,
        (1 : ℝ) * (j : ℝ) ≤ ∑ r : Fin j, (y ⟨i + r.1, by omega⟩ : ℝ)) ↔
      (∃ i : ℕ, ∃ h : i + j ≤ n, ∀ r : Fin j, y ⟨i + r.1, by omega⟩ = 1) := by
    intro j
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hij, hsum⟩
      refine ⟨i, hij, fun r₀ ↦ ?_⟩
      by_contra hr₀
      have hy0 : y ⟨i + r₀.1, by omega⟩ = 0 := by
        rcases hy ⟨i + r₀.1, by omega⟩ with h0 | h1
        · exact h0
        · exact absurd h1 hr₀
      have hle1 : ∀ r : Fin j, (y ⟨i + r.1, by omega⟩ : ℝ) ≤ 1 := by
        intro r
        rcases hy ⟨i + r.1, by omega⟩ with h | h <;> simp [h]
      have hlt : ∑ r : Fin j, (y ⟨i + r.1, by omega⟩ : ℝ) < ∑ _r : Fin j, (1 : ℝ) :=
        Finset.sum_lt_sum (fun r _ ↦ hle1 r)
          ⟨r₀, Finset.mem_univ r₀, by simp [hy0]⟩
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at hlt
      linarith
    · rintro ⟨i, hij, hall⟩
      refine ⟨i, hij, ?_⟩
      simp only [hall, Nat.cast_one, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one,
        one_mul, le_rfl]
  exact le_antisymm
    (Nat.findGreatest_mono_left (fun j hj ↦ (hiff j).mp hj) n)
    (Nat.findGreatest_mono_left (fun j hj ↦ (hiff j).mpr hj) n)

/-- Index sanity checks on `y = 0110111` (`n = 7`) for `headRunCount` (`stmts-review-05C` C2):
`headRunCount 2 y = 2`, `headRunCount 3 y = 1`, `headRunCount 4 y = 0`. -/
theorem headRunCount_sanity_0110111 :
    let y : Fin 7 → ℕ := ![0, 1, 1, 0, 1, 1, 1]
    headRunCount 2 y = 2 ∧ headRunCount 3 y = 1 ∧ headRunCount 4 y = 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Index sanity checks on `y = 0110111` (`n = 7`) for `longestQualityRun`
(`stmts-review-05C` C2): `longestQualityRun 1 y = 3` and `longestQualityRun (1 / 2) y = 7`. -/
theorem longestQualityRun_sanity_0110111 :
    let y : Fin 7 → ℕ := ![0, 1, 1, 0, 1, 1, 1]
    longestQualityRun 1 y = 3 ∧ longestQualityRun (1 / 2) y = 7 := by
  let y : Fin 7 → ℕ := ![0, 1, 1, 0, 1, 1, 1]
  have hy01 : ∀ i : Fin 7, y i = 0 ∨ y i = 1 := by decide
  classical
  refine ⟨?_, ?_⟩
  · rw [longestQualityRun_one_eq_findGreatest_ones hy01]
    set P : ℕ → Prop :=
      fun j ↦ ∃ i : ℕ, ∃ h : i + j ≤ 7, ∀ r : Fin j, y ⟨i + r.1, by omega⟩ = 1
    have hge : 3 ≤ Nat.findGreatest P 7 := by
      refine Nat.le_findGreatest (by omega) ⟨4, by omega, ?_⟩
      intro r
      fin_cases r <;> decide
    have hle : Nat.findGreatest P 7 ≤ 3 := by
      by_contra hnotle
      set j := Nat.findGreatest P 7 with hj_def
      have hj_le : j ≤ 7 := hj_def ▸ Nat.findGreatest_le 7
      have hj_ge : 4 ≤ j := by omega
      obtain ⟨i, hij, hall⟩ := Nat.findGreatest_of_ne_zero hj_def.symm (by omega)
      have h3 := hall ⟨3 - i, by omega⟩
      have hidx : (⟨i + (3 - i), by omega⟩ : Fin 7) = 3 := by ext; dsimp; omega
      rw [hidx] at h3
      have hy3 : y 3 = 0 := by decide
      omega
    exact le_antisymm hle hge
  · unfold longestQualityRun
    refine Nat.findGreatest_eq (P := fun j ↦ ∃ i : ℕ, ∃ h : i + j ≤ 7,
      (1 / 2 : ℝ) * (j : ℝ) ≤ ∑ r : Fin j, (y ⟨i + r.1, by omega⟩ : ℝ)) ⟨0, by omega, ?_⟩
    simp only [Fin.sum_univ_seven, y]; norm_num

private lemma headRunIndicator_zero {n k : ℕ} (hk : k ≤ n) (y : Fin n → ℕ) :
    headRunIndicator k y 0 = ∏ r : Fin k, y ⟨r.1, by omega⟩ := by simp [headRunIndicator, hk]

private lemma headRunIndicator_succ {n k : ℕ} (d : ℕ) (hdk : d + 1 + k ≤ n) (y : Fin n → ℕ) :
    headRunIndicator k y (d + 1) =
      (1 - y ⟨d, by omega⟩) * ∏ r : Fin k, y ⟨d + 1 + r.1, by omega⟩ := by
  simp [headRunIndicator, hdk]

/-- For `1 ≤ k ≤ n` and any `{0, 1}`-sequence `y : Fin n → ℕ`, `headRunCount k y = 0` if and only
if `longestQualityRun 1 y < k` (`SteinIntro.tex:2054-2056`). -/
theorem headRunCount_eq_zero_iff_longestQualityRun_lt {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n)
    {y : Fin n → ℕ} (hy : ∀ i : Fin n, y i = 0 ∨ y i = 1) :
    headRunCount k y = 0 ↔ longestQualityRun 1 y < k := by
  classical
  rw [longestQualityRun_one_eq_findGreatest_ones hy]
  set P : ℕ → Prop :=
    fun j ↦ ∃ i : ℕ, ∃ h : i + j ≤ n, ∀ r : Fin j, y ⟨i + r.1, by omega⟩ = 1
  constructor
  · intro hW0
    by_contra hnotlt
    have hk_le : k ≤ Nat.findGreatest P n := Nat.le_of_not_lt hnotlt
    set j := Nat.findGreatest P n with hj_def
    have hj_le : j ≤ n := hj_def ▸ Nat.findGreatest_le n
    obtain ⟨i₀, hi₀j, hallj⟩ := Nat.findGreatest_of_ne_zero hj_def.symm (by omega)
    have hi₀k : i₀ + k ≤ n := by omega
    have hallk : ∀ r : Fin k, y ⟨i₀ + r.1, by omega⟩ = 1 := fun r ↦ hallj ⟨r.1, by omega⟩
    have hex_ind : ∀ i : ℕ, (hi : i + k ≤ n) → (∀ r : Fin k, y ⟨i + r.1, by omega⟩ = 1) →
        ∃ m ≤ i, headRunIndicator k y m = 1 := by
      intro i
      induction i with
      | zero =>
        intro hi hall
        refine ⟨0, le_rfl, ?_⟩
        rw [headRunIndicator_zero (by omega)]
        exact Finset.prod_eq_one fun r _ ↦ by simpa only [zero_add] using hall r
      | succ d ih =>
        intro hi hall
        rcases hy ⟨d, by omega⟩ with hd0 | hd1
        · refine ⟨d + 1, le_rfl, ?_⟩
          rw [headRunIndicator_succ d hi, hd0, Finset.prod_eq_one fun r _ ↦ hall r]
          rfl
        · have hall_d : ∀ r : Fin k, y ⟨d + r.1, by omega⟩ = 1 := by
            intro r
            rcases eq_or_lt_of_le (Nat.zero_le r.1) with hr0 | hrpos
            · have heq : (⟨d + r.1, by omega⟩ : Fin n) = ⟨d, by omega⟩ := by ext; dsimp; omega
              rw [heq, hd1]
            · have hsub := hall ⟨r.1 - 1, by omega⟩
              have heq : (⟨d + r.1, by omega⟩ : Fin n) = ⟨d + 1 + (r.1 - 1), by omega⟩ := by
                ext; dsimp; omega
              rw [heq, hsub]
          obtain ⟨m, hmd, hm1⟩ := ih (by omega) hall_d
          exact ⟨m, by omega, hm1⟩
    obtain ⟨m, hmi₀, hm1⟩ := hex_ind i₀ hi₀k hallk
    have hmem : m ∈ Finset.range (n - k + 1) := Finset.mem_range.mpr (by omega)
    have hzero_all := (Finset.sum_eq_zero_iff.mp hW0) m hmem
    omega
  · intro hlt
    rw [headRunCount, Finset.sum_eq_zero_iff]
    intro i hi
    have hik : i + k ≤ n := by rw [Finset.mem_range] at hi; omega
    by_contra hne0
    have hprod_ne : (∏ r : Fin k, y ⟨i + r.1, by omega⟩) ≠ 0 := by
      intro hp0; apply hne0
      rcases i with _ | d
      · have hp0' : (∏ r : Fin k, y ⟨r.1, by omega⟩) = 0 := by simpa only [zero_add] using hp0
        rw [headRunIndicator_zero hkn, hp0']
      · rw [headRunIndicator_succ d hik, hp0, mul_zero]
    have hall1 : ∀ r : Fin k, y ⟨i + r.1, by omega⟩ = 1 := by
      intro r
      have hfac_ne : y ⟨i + r.1, by omega⟩ ≠ 0 := fun hz ↦
        hprod_ne (Finset.prod_eq_zero (Finset.mem_univ r) hz)
      rcases hy ⟨i + r.1, by omega⟩ with h0 | h1
      · exact absurd h0 hfac_ne
      · exact h1
    have hkle : k ≤ Nat.findGreatest P n := Nat.le_findGreatest hkn ⟨i, hik, hall1⟩
    exact absurd (hkle.trans_lt hlt) (lt_irrefl k)

/-- **Section 4.2.1 longest-run probability identity** (`SteinIntro.tex:2054-2056`):
`ℙ(W = 0) = ℙ(R_n < k)` for `{0, 1}`-valued coin tosses with `1 ≤ k ≤ n`. -/
theorem probReal_headRunCount_eq_zero_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n k : ℕ} {Y : Fin n → Ω → ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (_hY : ∀ i : Fin n, AEMeasurable (Y i) P)
    (hY01 : ∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) :
    P.real {ω | headRunCount k (fun i ↦ Y i ω) = 0} =
      P.real {ω | longestQualityRun 1 (fun i ↦ Y i ω) < k} := by
  refine measureReal_congr ?_
  filter_upwards [ae_all_iff.mpr hY01] with ω hω
  exact propext (headRunCount_eq_zero_iff_longestQualityRun_lt hk1 hkn hω)

/-! ### Theorem 4.8: Total-Variation Poisson Approximation for Head Runs -/

private lemma integral_finset_prod_indep {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ}
    {Y : Fin n → Ω → ℕ} (hY : ∀ i : Fin n, AEMeasurable (Y i) P)
    (hIndep : ProbabilityTheory.iIndepFun Y P)
    (s : Finset (Fin n)) (g : Fin n → ℕ → ℝ) (hg_bdd : ∀ t ∈ s, ∀ u : ℕ, |g t u| ≤ 1) :
    ∫ ω, ∏ t ∈ s, g t (Y t ω) ∂P = ∏ t ∈ s, ∫ ω, g t (Y t ω) ∂P := by
  classical
  induction s using Finset.induction with
  | empty => simp [probReal_univ]
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    have hdisj : Disjoint ({a} : Finset (Fin n)) s := Finset.disjoint_singleton_left.mpr ha
    have hind_tup := hIndep.indepFun_finset₀ ({a} : Finset (Fin n)) s hdisj hY
    have hφ : Measurable fun u : ({a} : Finset (Fin n)) → ℕ ↦
        g a (u ⟨a, Finset.mem_singleton_self a⟩) :=
      (Measurable.of_discrete : Measurable (g a)).comp (measurable_pi_apply _)
    have hψ : Measurable fun v : s → ℕ ↦ ∏ b : s, g b.1 (v b) :=
      Finset.measurable_prod Finset.univ fun b _ ↦
        (Measurable.of_discrete : Measurable (g b.1)).comp (measurable_pi_apply b)
    have hind_fun : IndepFun (fun ω ↦ g a (Y a ω)) (fun ω ↦ ∏ t ∈ s, g t (Y t ω)) P := by
      have hcomp := hind_tup.comp hφ hψ
      have heq_s : (fun x ↦ ∏ b : s, g b.1 (Y b.1 x)) = fun ω ↦ ∏ t ∈ s, g t (Y t ω) := by
        ext x
        exact Finset.prod_coe_sort s (fun t ↦ g t (Y t x))
      simpa only [Function.comp_def, heq_s] using hcomp
    have hsm_a : AEStronglyMeasurable (fun ω ↦ g a (Y a ω)) P :=
      ((Measurable.of_discrete : Measurable (g a)).comp_aemeasurable (hY a)).aestronglyMeasurable
    have hsm_s : AEStronglyMeasurable (fun ω ↦ ∏ t ∈ s, g t (Y t ω)) P := by
      have hae : AEMeasurable (fun ω ↦ ∏ t ∈ s, g t (Y t ω)) P := by
        clear hind_fun hψ hφ hind_tup hdisj ih hg_bdd ha
        induction s using Finset.induction with
        | empty => exact aemeasurable_const
        | insert b s' hb ih' =>
          simp_rw [Finset.prod_insert hb]
          exact ((Measurable.of_discrete : Measurable (g b)).comp_aemeasurable (hY b)).mul ih'
      exact hae.aestronglyMeasurable
    change ∫ ω, ((fun ω' ↦ g a (Y a ω')) * (fun ω' ↦ ∏ t ∈ s, g t (Y t ω'))) ω ∂P = _
    rw [hind_fun.integral_mul_eq_mul_integral hsm_a hsm_s,
      ih (fun t ht ↦ hg_bdd t (Finset.mem_insert_of_mem ht))]

private def headRunSupport {n : ℕ} (k : ℕ) (i : Fin (n - k + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun t : Fin n ↦ i.1 ≤ t.1 + 1 ∧ t.1 < i.1 + k

private def headRunEval {n k : ℕ} (hkn : k ≤ n) (i : Fin (n - k + 1))
    (u : headRunSupport k i → ℕ) : ℕ :=
  if h0 : i.1 = 0 then
    ∏ r : Fin k, u ⟨⟨r.1, by omega⟩, by simp [headRunSupport, h0]⟩
  else
    (1 - u ⟨⟨i.1 - 1, by omega⟩, by simp [headRunSupport]; omega⟩) *
      ∏ r : Fin k, u ⟨⟨i.1 + r.1, by omega⟩, by simp [headRunSupport]; omega⟩

private lemma measurable_headRunEval {n k : ℕ} (hkn : k ≤ n) (i : Fin (n - k + 1)) :
    Measurable (headRunEval hkn i) := by
  unfold headRunEval
  split_ifs with h0
  · exact Finset.measurable_prod Finset.univ fun r _ ↦ measurable_pi_apply _
  · let idx₀ : headRunSupport k i := ⟨⟨i.1 - 1, by omega⟩, by simp [headRunSupport]; omega⟩
    let idx₁ : Fin k → headRunSupport k i :=
      fun r ↦ ⟨⟨i.1 + r.1, by omega⟩, by simp [headRunSupport]; omega⟩
    have hsub : Measurable fun u : headRunSupport k i → ℕ ↦ 1 - u idx₀ :=
      (Measurable.of_discrete : Measurable fun x : ℕ ↦ 1 - x).comp (measurable_pi_apply idx₀)
    have hprod : Measurable fun u : headRunSupport k i → ℕ ↦ ∏ r : Fin k, u (idx₁ r) :=
      Finset.measurable_prod Finset.univ fun r _ ↦ measurable_pi_apply (idx₁ r)
    exact (Measurable.of_discrete : Measurable fun p : ℕ × ℕ ↦ p.1 * p.2).comp
      (hsub.prodMk hprod)

private lemma headRunEval_apply {n k : ℕ} (hkn : k ≤ n) (y : Fin n → ℕ) (i : Fin (n - k + 1)) :
    headRunEval hkn i (fun t ↦ y t.1) = headRunIndicator k y i.1 := by
  unfold headRunEval
  split_ifs with h0
  · rw [h0, headRunIndicator_zero hkn]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hdk : d + 1 + k ≤ n := by omega
    have h1 : (⟨i.1 - 1, by omega⟩ : Fin n) = ⟨d, by omega⟩ := by ext; dsimp; omega
    have h2 : ∀ r : Fin k, (⟨i.1 + r.1, by omega⟩ : Fin n) = ⟨d + 1 + r.1, by omega⟩ := by
      intro r; ext; dsimp; omega
    simp_rw [h1, h2]
    rw [hd, headRunIndicator_succ d hdk]

/-- **Theorem 4.8** (`\label{thm104}`, eq. `(4.8)` `\label{1011}`, `SteinIntro.tex:2024-2030`):
for `1 ≤ k ≤ n` and `0 ≤ p ≤ 1`, let `W = headRunCount k Y` be the number of head runs of length
at least `k` in `n` independent coin tosses with head probability `p`. Then
`𝔼[W] = p^k ((n - k)(1 - p) + 1)`, and for `Z ~ Po(λ)`,
`d_TV(ℒ(W), ℒ(Z)) ≤ λ² (2k + 1) / (n - k + 1) + 2 λ p^k`. -/
theorem tvDist_headRunCount_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n k : ℕ} {p : ℝ} {Y : Fin n → Ω → ℕ} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hY : ∀ i : Fin n, AEMeasurable (Y i) P)
    (hY01 : ∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hIndep : ProbabilityTheory.iIndepFun Y P)
    (hYp : ∀ i : Fin n, P.real {ω | Y i ω = 1} = p)
    (hr_eq : (r : ℝ) = p ^ k * (((n : ℝ) - (k : ℝ)) * (1 - p) + 1))
    (hZ : AEMeasurable Z P')
    (hlaw : P'.map Z = poissonLaw r) :
    let W : Ω → ℕ := fun ω ↦ headRunCount k (fun i ↦ Y i ω)
    ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          ((r : ℝ) ^ 2 * ((2 * (k : ℝ) + 1) / ((n : ℝ) - (k : ℝ) + 1)) +
            2 * (r : ℝ) * p ^ k) := by
  intro W
  set m : ℕ := n - k + 1
  have hm_pos : 0 < m := by omega
  let X : Fin m → Ω → ℕ := fun i ω ↦ headRunIndicator k (fun t ↦ Y t ω) i.1
  have hW_eq : W = fun ω ↦ ∑ i : Fin m, X i ω := by
    ext ω
    dsimp only [W, headRunCount, X]
    exact (Fin.sum_univ_eq_sum_range (fun i ↦ headRunIndicator k (fun t ↦ Y t ω) i) m).symm
  have hX_ae : ∀ i : Fin m, AEMeasurable (X i) P := by
    intro i
    have heq : X i = (headRunEval hkn i) ∘ (fun ω (t : headRunSupport k i) ↦ Y t.1 ω) := by
      ext ω
      exact (headRunEval_apply hkn (fun t ↦ Y t ω) i).symm
    rw [heq]
    exact (measurable_headRunEval hkn i).comp_aemeasurable (.of_eval fun t ↦ hY t.1)
  have hX01 : ∀ i : Fin m, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1 := by
    intro i
    filter_upwards [ae_all_iff.mpr hY01] with ω hω
    have hprod01 : ∀ (s : ℕ) (hs : s + k ≤ n),
        (∏ r : Fin k, Y ⟨s + r.1, by omega⟩ ω) = 0 ∨
          (∏ r : Fin k, Y ⟨s + r.1, by omega⟩ ω) = 1 := by
      intro s hs
      by_cases hall : ∀ r : Fin k, Y ⟨s + r.1, by omega⟩ ω = 1
      · exact Or.inr (Finset.prod_eq_one fun r _ ↦ hall r)
      · rw [not_forall] at hall
        obtain ⟨r, hr1⟩ := hall
        have hr0 : Y ⟨s + r.1, by omega⟩ ω = 0 := by
          rcases hω ⟨s + r.1, by omega⟩ with h0 | h1
          · exact h0
          · exact absurd h1 hr1
        exact Or.inl (Finset.prod_eq_zero (Finset.mem_univ r) hr0)
    dsimp only [X]
    rcases eq_or_ne i.1 0 with h0 | hne0
    · rw [h0, headRunIndicator_zero hkn]
      simpa only [zero_add] using hprod01 0 (by omega)
    · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hne0
      have hdk : d + 1 + k ≤ n := by omega
      rw [hd, headRunIndicator_succ d hdk]
      rcases hω ⟨d, by omega⟩ with hd0 | hd1 <;> rcases hprod01 (d + 1) hdk with hp0' | hp1'
      · simp [hd0, hp0']
      · simp [hd0, hp1']
      · simp [hd1, hp0']
      · simp [hd1, hp1']
  have hpX_zero : P.real {ω | X ⟨0, hm_pos⟩ ω = 1} = p ^ k := by
    rw [← integral_natCast_of_ae_zero_or_one (hX_ae ⟨0, hm_pos⟩) (hX01 ⟨0, hm_pos⟩)]
    let s₀ : Finset (Fin n) := Finset.univ.filter fun t : Fin n ↦ t.1 < k
    let g : Fin n → ℕ → ℝ := fun _ u ↦ if u = 1 then 1 else 0
    have hae_eq : (fun ω ↦ (X ⟨0, hm_pos⟩ ω : ℝ)) =ᵐ[P]
        fun ω ↦ ∏ t ∈ s₀, g t (Y t ω) := by
      filter_upwards [ae_all_iff.mpr hY01] with ω hω
      dsimp only [X]
      rw [headRunIndicator_zero hkn, Nat.cast_prod]
      refine Finset.prod_bij (fun (r : Fin k) _ ↦ (⟨r.1, by omega⟩ : Fin n))
        (fun r _ ↦ by simp [s₀, r.2])
        (fun _ _ _ _ h ↦ Fin.ext (Fin.mk.inj h))
        (fun t ht ↦ ⟨⟨t.1, by simp [s₀] at ht; omega⟩, Finset.mem_univ _, by ext; rfl⟩) ?_
      intro r _
      rcases hω ⟨r.1, by omega⟩ with h | h <;> simp [g, h]
    have hs₀_card : s₀.card = k := by
      refine Finset.card_bij (fun (t : Fin n) _ ↦ t.1)
        (fun t ht ↦ Finset.mem_range.mpr
          (by simp only [s₀, Finset.mem_filter, Finset.mem_univ, true_and] at ht; exact ht))
        (fun _ _ _ _ h ↦ Fin.ext h)
        (fun r hr ↦ ⟨⟨r, by rw [Finset.mem_range] at hr; omega⟩,
          by
            simp only [s₀, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Finset.mem_range.mp hr,
          rfl⟩)
        |>.trans (Finset.card_range k)
    rw [integral_congr_ae hae_eq,
      integral_finset_prod_indep hY hIndep s₀ g
        (fun _ _ u ↦ by dsimp only [g]; split_ifs <;> norm_num)]
    have hfac : ∀ t ∈ s₀, ∫ ω, g t (Y t ω) ∂P = p := by
      intro t _
      have hae_t : (fun ω ↦ g t (Y t ω)) =ᵐ[P] fun ω ↦ (Y t ω : ℝ) := by
        filter_upwards [hY01 t] with ω hω
        rcases hω with h | h <;> simp [g, h]
      rw [integral_congr_ae hae_t, integral_natCast_of_ae_zero_or_one (hY t) (hY01 t), hYp t]
    rw [Finset.prod_congr rfl hfac, Finset.prod_const, hs₀_card]
  have hpX_succ : ∀ (i : Fin m), i ≠ ⟨0, hm_pos⟩ →
      P.real {ω | X i ω = 1} = (1 - p) * p ^ k := by
    intro i hi0
    have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero fun h0 ↦ hi0 (Fin.ext h0)
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi_pos)
    have hdk : d + 1 + k ≤ n := by omega
    rw [← integral_natCast_of_ae_zero_or_one (hX_ae i) (hX01 i)]
    let t₀ : Fin n := ⟨d, by omega⟩
    let s₁ : Finset (Fin n) := Finset.univ.filter fun t : Fin n ↦ d + 1 ≤ t.1 ∧ t.1 < d + 1 + k
    have ht₀_not : t₀ ∉ s₁ := by simp [t₀, s₁]
    let g : Fin n → ℕ → ℝ := fun t u ↦
      if t = t₀ then (if u = 0 then 1 else 0) else (if u = 1 then 1 else 0)
    have hae_eq : (fun ω ↦ (X i ω : ℝ)) =ᵐ[P]
        fun ω ↦ ∏ t ∈ insert t₀ s₁, g t (Y t ω) := by
      filter_upwards [ae_all_iff.mpr hY01] with ω hω
      rw [Finset.prod_insert ht₀_not]
      dsimp only [X]
      rw [hd, headRunIndicator_succ d hdk, Nat.cast_mul, Nat.cast_prod]
      congr 1
      · rcases hω t₀ with h | h <;> simp [g, t₀, h]
      · refine Finset.prod_bij (fun (r : Fin k) _ ↦ (⟨d + 1 + r.1, by omega⟩ : Fin n))
          (fun r _ ↦ by simp [s₁]; omega)
          (fun _ _ _ _ h ↦ Fin.ext (by have := Fin.mk.inj h; omega))
          (fun t ht ↦ ⟨⟨t.1 - (d + 1), by simp [s₁] at ht; omega⟩, Finset.mem_univ _,
            by simp [s₁] at ht; ext; dsimp; omega⟩) ?_
        intro r _
        have hne_t₀ : (⟨d + 1 + r.1, by omega⟩ : Fin n) ≠ t₀ := by
          intro heq; have := congrArg Fin.val heq; dsimp [t₀] at this; omega
        rcases hω ⟨d + 1 + r.1, by omega⟩ with h | h <;> simp [g, hne_t₀, h]
    have hs₁_card : s₁.card = k := by
      refine Finset.card_bij (fun (t : Fin n) _ ↦ t.1 - (d + 1))
        (fun t ht ↦ Finset.mem_range.mpr (by simp [s₁] at ht; omega))
        (fun t₁ ht₁ t₂ ht₂ h ↦ Fin.ext (by simp [s₁] at ht₁ ht₂; omega))
        (fun r hr ↦ ⟨⟨d + 1 + r, by rw [Finset.mem_range] at hr; omega⟩,
          by simp [s₁]; rw [Finset.mem_range] at hr; omega, by dsimp; omega⟩)
        |>.trans (Finset.card_range k)
    rw [integral_congr_ae hae_eq,
      integral_finset_prod_indep hY hIndep (insert t₀ s₁) g
        (fun _ _ u ↦ by dsimp only [g]; split_ifs <;> norm_num),
      Finset.prod_insert ht₀_not]
    have hgt₀ : ∫ ω, g t₀ (Y t₀ ω) ∂P = 1 - p := by
      have hae0 : (fun ω ↦ g t₀ (Y t₀ ω)) =ᵐ[P] fun ω ↦ 1 - (Y t₀ ω : ℝ) := by
        filter_upwards [hY01 t₀] with ω hω
        rcases hω with h | h <;> simp [g, h]
      rw [integral_congr_ae hae0,
        integral_sub (integrable_const 1)
          (integrable_natCast_of_ae_zero_or_one (hY t₀) (hY01 t₀)),
        integral_const, probReal_univ, one_smul,
        integral_natCast_of_ae_zero_or_one (hY t₀) (hY01 t₀), hYp t₀]
    have hgs₁ : ∀ t ∈ s₁, ∫ ω, g t (Y t ω) ∂P = p := by
      intro t ht
      have hne : t ≠ t₀ := fun heq ↦ ht₀_not (heq ▸ ht)
      have hae_t : (fun ω ↦ g t (Y t ω)) =ᵐ[P] fun ω ↦ (Y t ω : ℝ) := by
        filter_upwards [hY01 t] with ω hω
        rcases hω with h | h <;> simp [g, hne, h]
      rw [integral_congr_ae hae_t, integral_natCast_of_ae_zero_or_one (hY t) (hY01 t), hYp t]
    rw [hgt₀, Finset.prod_congr rfl hgs₁, Finset.prod_const, hs₁_card]
  have hr_sum : (r : ℝ) = ∑ i : Fin m, P.real {ω | X i ω = 1} := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ⟨0, hm_pos⟩), hpX_zero]
    have herase : ∑ i ∈ Finset.univ.erase ⟨0, hm_pos⟩, P.real {ω | X i ω = 1} =
        ∑ _i ∈ Finset.univ.erase (⟨0, hm_pos⟩ : Fin m), (1 - p) * p ^ k :=
      Finset.sum_congr rfl fun i hi ↦ hpX_succ i (Finset.ne_of_mem_erase hi)
    rw [herase, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin,
      nsmul_eq_mul]
    have hm1 : ((m - 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      have hmk : m - 1 = n - k := by omega
      rw [hmk, Nat.cast_sub hkn]
    rw [hm1, hr_eq]
    ring
  have hmean : ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) := by
    rw [hW_eq]
    simp_rw [Nat.cast_sum]
    rw [integral_finsetSum Finset.univ fun i _ ↦
      integrable_natCast_of_ae_zero_or_one (hX_ae i) (hX01 i)]
    have hcongr : ∑ i : Fin m, ∫ ω, (X i ω : ℝ) ∂P =
        ∑ i : Fin m, P.real {ω | X i ω = 1} :=
      Finset.sum_congr rfl fun i _ ↦ integral_natCast_of_ae_zero_or_one (hX_ae i) (hX01 i)
    rw [hcongr, ← hr_sum]
  refine ⟨hmean, ?_⟩
  let N : Fin m → Finset (Fin m) :=
    fun i ↦ Finset.univ.filter fun j : Fin m ↦ i.1 ≤ j.1 + k ∧ j.1 ≤ i.1 + k
  have hNi : ∀ i : Fin m, i ∈ N i := fun i ↦ by simp [N]
  have hDep : HasDependencyNeighborhoods P (fun i ω ↦ (X i ω : ℝ)) N := by
    intro i
    let T : Finset (Fin n) :=
      (Finset.univ.filter fun j : Fin m ↦ j ∉ N i).biUnion (headRunSupport k)
    have hdisj : Disjoint (headRunSupport k i) T := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      rw [Finset.mem_filter] at hj
      refine Finset.disjoint_left.mpr fun t hti htj ↦ hj.2 ?_
      simp only [headRunSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hti htj
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hind_tup := hIndep.indepFun_finset₀ (headRunSupport k i) T hdisj hY
    have hφ : Measurable fun u : headRunSupport k i → ℕ ↦ (headRunEval hkn i u : ℝ) :=
      (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp (measurable_headRunEval hkn i)
    have hsub_T : ∀ j : {j : Fin m // j ∉ N i}, headRunSupport k j.1 ⊆ T :=
      fun j ↦ Finset.subset_biUnion_of_mem (headRunSupport k) (by simp [j.2])
    have hψ : Measurable fun v : T → ℕ ↦
        fun (j : {j : Fin m // j ∉ N i}) ↦
          (headRunEval hkn j.1 (fun a ↦ v ⟨a.1, hsub_T j a.2⟩) : ℝ) := by
      refine measurable_pi_iff.mpr fun j ↦ ?_
      refine ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp
        (measurable_headRunEval hkn j.1)).comp ?_
      exact measurable_pi_iff.mpr fun a ↦ measurable_pi_apply _
    have hcomp := hind_tup.comp hφ hψ
    have hlhs : (fun ω ↦ (headRunEval hkn i (fun t ↦ Y t.1 ω) : ℝ)) =
        fun ω ↦ (X i ω : ℝ) := by
      ext ω
      rw [headRunEval_apply hkn (fun t ↦ Y t ω) i]
    have hrhs : (fun ω (j : {j : Fin m // j ∉ N i}) ↦
        (headRunEval hkn j.1 (fun a ↦ Y a.1 ω) : ℝ)) =
        fun ω (j : {j : Fin m // j ∉ N i}) ↦ (X j.1 ω : ℝ) := by
      ext ω j
      rw [headRunEval_apply hkn (fun t ↦ Y t ω) j.1]
    simpa only [Function.comp_def, hlhs, hrhs] using hcomp
  have hp2_zero : ∀ i : Fin m, ∀ j ∈ (N i).erase i,
      ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P = 0 := by
    intro i j hj
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    have hmemN : j ∈ N i := Finset.mem_of_mem_erase hj
    dsimp only [N] at hmemN
    rw [Finset.mem_filter] at hmemN
    have hae0 : (fun ω ↦ (X i ω : ℝ) * (X j ω : ℝ)) =ᵐ[P] fun _ ↦ (0 : ℝ) := by
      filter_upwards [ae_all_iff.mpr hY01] with ω hω
      have aux : ∀ a b : Fin m, a.1 < b.1 → b.1 ≤ a.1 + k → X a ω * X b ω = 0 := by
        intro a b hab hbak
        obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b.1 ≠ 0)
        have hak : a.1 + k ≤ n := by omega
        have hdk_n : d + 1 + k ≤ n := by omega
        have hda : a.1 ≤ d := by omega
        have hdk : d - a.1 < k := by omega
        rcases hω ⟨d, by omega⟩ with hd0 | hd1
        · have hXa0 : X a ω = 0 := by
            dsimp only [X]
            have hp0' : (∏ r : Fin k, Y ⟨a.1 + r.1, by omega⟩ ω) = 0 := by
              refine Finset.prod_eq_zero (Finset.mem_univ ⟨d - a.1, hdk⟩) ?_
              have heq : (⟨a.1 + (d - a.1), by omega⟩ : Fin n) = ⟨d, by omega⟩ := by
                ext; dsimp; omega
              rw [heq, hd0]
            rcases eq_or_ne a.1 0 with ha0 | hane0
            · rw [ha0, headRunIndicator_zero hkn]
              simpa only [ha0, zero_add] using hp0'
            · obtain ⟨da, hda_eq⟩ := Nat.exists_eq_succ_of_ne_zero hane0
              rw [hda_eq, headRunIndicator_succ da (by omega)]
              have hp0'' : (∏ r : Fin k, Y ⟨da + 1 + r.1, by omega⟩ ω) = 0 := by
                simpa only [hda_eq] using hp0'
              rw [hp0'', mul_zero]
          rw [hXa0, zero_mul]
        · have hXb0 : X b ω = 0 := by
            dsimp only [X]
            rw [hd, headRunIndicator_succ d hdk_n, hd1, Nat.sub_self, zero_mul]
          rw [hXb0, mul_zero]
      have hprod0 : X i ω * X j ω = 0 := by
        rcases lt_trichotomy i.1 j.1 with hij | hij | hji
        · exact aux i j hij hmemN.2.2
        · exact absurd (Fin.ext hij) hne.symm
        · rw [mul_comm]; exact aux j i hji hmemN.2.1
      exact_mod_cast hprod0
    rw [integral_congr_ae hae0, integral_const, smul_zero]
  have hthm47 := tvDist_sum_dep_indicator_le P P' hX_ae hX01 hDep hNi hr_sum hZ hlaw
  rw [← hW_eq] at hthm47
  refine hthm47.trans (ENNReal.ofReal_le_ofReal ?_)
  have hb2_sum : (∑ i : Fin m, ∑ j ∈ (N i).erase i, ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j hj ↦ hp2_zero i j hj
  rw [hb2_sum, add_zero]
  set pX : Fin m → ℝ := fun i ↦ P.real {ω | X i ω = 1}
  have hb1_nn : 0 ≤ ∑ i : Fin m, ∑ j ∈ N i, pX i * pX j :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg measureReal_nonneg measureReal_nonneg
  have hmin_le1 : min 1 (r : ℝ)⁻¹ * ∑ i : Fin m, ∑ j ∈ N i, pX i * pX j ≤
      ∑ i : Fin m, ∑ j ∈ N i, pX i * pX j :=
    mul_le_of_le_one_left hb1_nn (min_le_left 1 _)
  refine hmin_le1.trans ?_
  set a : ℝ := (1 - p) * p ^ k
  set b : ℝ := p ^ (k + 1)
  have ha_nn : 0 ≤ a := mul_nonneg (sub_nonneg.mpr hp1) (pow_nonneg hp0 k)
  have hb_nn : 0 ≤ b := pow_nonneg hp0 (k + 1)
  let i0 : Fin m := ⟨0, hm_pos⟩
  have hpX_form : ∀ i : Fin m, pX i = a + (if i = i0 then b else 0) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [ite_true]
      dsimp only [pX, i0, a, b]
      rw [hpX_zero, pow_succ]
      ring
    · simp only [hi, ite_false, add_zero]
      exact hpX_succ i hi
  have hr_ab : (r : ℝ) = (m : ℝ) * a + b := by
    have hm_real : (m : ℝ) = (n : ℝ) - (k : ℝ) + 1 := by
      have hm_eq : m = (n - k) + 1 := rfl
      rw [hm_eq, Nat.cast_add, Nat.cast_sub hkn, Nat.cast_one]
    rw [hr_eq, hm_real]
    dsimp only [a, b]
    rw [pow_succ]
    ring
  have hcard_Ni : ∀ i : Fin m, ((N i).card : ℝ) ≤ 2 * (k : ℝ) + 1 := by
    intro i
    have hle_nat : (N i).card ≤ 2 * k + 1 := by
      have hinj : (N i).card ≤ (Finset.Icc (i.1 - k) (i.1 + k)).card := by
        refine Finset.card_le_card_of_injOn Fin.val (fun j hj ↦ ?_)
          (fun _ _ _ _ h ↦ Fin.ext h)
        rw [Finset.mem_coe, Finset.mem_filter] at hj
        rw [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨by omega, hj.2.2⟩
      rw [Nat.card_Icc] at hinj
      omega
    exact_mod_cast hle_nat
  have hcard_N0_m : ((N i0).card : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Finset.card_le_univ (N i0)).trans_eq (Fintype.card_fin m)
  have hsymm_N0 : (Finset.univ.filter fun i : Fin m ↦ i0 ∈ N i) = N i0 := by
    ext i
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hexpand : (∑ i : Fin m, ∑ j ∈ N i, pX i * pX j) =
      a ^ 2 * (∑ i : Fin m, ((N i).card : ℝ)) +
        a * b * ((N i0).card : ℝ) +
        a * b * ((Finset.univ.filter fun i : Fin m ↦ i0 ∈ N i).card : ℝ) +
        b ^ 2 := by
    simp_rw [hpX_form]
    have hinner : ∀ i : Fin m,
        (∑ j ∈ N i, (a + if i = i0 then b else 0) * (a + if j = i0 then b else 0)) =
          a ^ 2 * ((N i).card : ℝ) +
            (if i = i0 then a * b * ((N i).card : ℝ) else 0) +
            (if i0 ∈ N i then a * b else 0) +
            (if i = i0 then b ^ 2 else 0) := by
      intro i
      have hsum_j0 : (∑ j ∈ N i, if j = i0 then (1 : ℝ) else 0) =
          if i0 ∈ N i then 1 else 0 := by
        simp [Finset.sum_ite_eq']
      by_cases hi : i = i0
      · subst hi
        have hi0_mem : i0 ∈ N i0 := hNi i0
        simp only [ite_true, hi0_mem]
        have hlin : ∀ j : Fin m, (a + b) * (a + if j = i0 then b else 0) =
            (a ^ 2 + a * b) + (a * b + b ^ 2) * (if j = i0 then 1 else 0) := by
          intro j; split_ifs <;> ring
        simp_rw [hlin]
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hsum_j0]
        simp only [hi0_mem, ite_true]
        ring
      · simp only [hi, ite_false, add_zero]
        have hlin : ∀ j : Fin m, a * (a + if j = i0 then b else 0) =
            a ^ 2 + (a * b) * (if j = i0 then 1 else 0) := by
          intro j; split_ifs <;> ring
        simp_rw [hlin]
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hsum_j0]
        split_ifs <;> ring
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hsum_in : (∑ i : Fin m, if i0 ∈ N i then a * b else 0) =
        a * b * ((Finset.univ.filter fun i : Fin m ↦ i0 ∈ N i).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
    rw [hsum_in]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hexpand, hsymm_N0]
  have hm_pos_r : (0 : ℝ) < (m : ℝ) := by positivity
  have hm_denom : (m : ℝ) = (n : ℝ) - (k : ℝ) + 1 := by
    have hm_eq : m = (n - k) + 1 := rfl
    rw [hm_eq, Nat.cast_add, Nat.cast_sub hkn, Nat.cast_one]
  have hpart1 : a ^ 2 * (∑ i : Fin m, ((N i).card : ℝ)) ≤
      (r : ℝ) ^ 2 * ((2 * (k : ℝ) + 1) / ((n : ℝ) - (k : ℝ) + 1)) := by
    have hsum_card : (∑ i : Fin m, ((N i).card : ℝ)) ≤ (m : ℝ) * (2 * (k : ℝ) + 1) := by
      calc ∑ i : Fin m, ((N i).card : ℝ)
        _ ≤ ∑ _i : Fin m, (2 * (k : ℝ) + 1) := Finset.sum_le_sum fun i _ ↦ hcard_Ni i
        _ = (m : ℝ) * (2 * (k : ℝ) + 1) := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    calc a ^ 2 * (∑ i : Fin m, ((N i).card : ℝ))
      _ ≤ a ^ 2 * ((m : ℝ) * (2 * (k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hsum_card (sq_nonneg a)
      _ = ((m : ℝ) * a) ^ 2 * ((2 * (k : ℝ) + 1) / (m : ℝ)) := by field_simp
      _ ≤ ((m : ℝ) * a + b) ^ 2 * ((2 * (k : ℝ) + 1) / (m : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith [mul_nonneg hm_pos_r.le ha_nn, hb_nn]
      _ = (r : ℝ) ^ 2 * ((2 * (k : ℝ) + 1) / ((n : ℝ) - (k : ℝ) + 1)) := by
        rw [← hr_ab, ← hm_denom]
  have hpart2 : a * b * ((N i0).card : ℝ) + a * b * ((N i0).card : ℝ) + b ^ 2 ≤
      2 * (r : ℝ) * p ^ k := by
    have hpk_ab : p ^ k = a + b := by
      dsimp only [a, b]; rw [pow_succ]; ring
    rw [hr_ab, hpk_ab]
    have hab_m : a * b * ((N i0).card : ℝ) ≤ a * b * (m : ℝ) :=
      mul_le_mul_of_nonneg_left hcard_N0_m (mul_nonneg ha_nn hb_nn)
    have hdiff_nn : 0 ≤ 2 * (m : ℝ) * a ^ 2 + 2 * a * b + b ^ 2 := by positivity
    linarith
  linarith

/-! ### Remark 4.3: DNA Sequence Comparison Indicator Model -/

/-- **Remark 4.3** (`SteinIntro.tex:2079-2110`, DNA sequence comparison model): if two independent
sequences `A` and `B` of length `n` are i.i.d. draws from a `4`-letter alphabet (`Fin 4`) with
letter probabilities `q`, then the coordinate-wise match indicators
`Y i ω = if A i ω = B i ω then 1 else 0` are i.i.d. with
`ℙ(Y i = 1) = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2`. -/
theorem dna_match_iIndepFun_and_prob
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {A B : Fin n → Ω → Fin 4} {q : Fin 4 → ℝ}
    (hA : ∀ i : Fin n, AEMeasurable (A i) P)
    (hB : ∀ i : Fin n, AEMeasurable (B i) P)
    (hIndepA : ProbabilityTheory.iIndepFun A P)
    (hIndepB : ProbabilityTheory.iIndepFun B P)
    (hIndepAB : ProbabilityTheory.IndepFun (fun ω i ↦ A i ω) (fun ω i ↦ B i ω) P)
    (hAq : ∀ (i : Fin n) (c : Fin 4), P.real {ω | A i ω = c} = q c)
    (hBq : ∀ (i : Fin n) (c : Fin 4), P.real {ω | B i ω = c} = q c) :
    let Y : Fin n → Ω → ℕ := fun i ω ↦ if A i ω = B i ω then 1 else 0
    ProbabilityTheory.iIndepFun Y P ∧
      ∀ i : Fin n, P.real {ω | Y i ω = 1} = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
  intro Y
  let Z : Fin n → Ω → Fin 4 × Fin 4 := fun i ω ↦ (A i ω, B i ω)
  have hZ_ae : ∀ i : Fin n, AEMeasurable (Z i) P := fun i ↦ (hA i).prodMk (hB i)
  have htupA_ae : AEMeasurable (fun ω i ↦ A i ω) P := .of_eval hA
  have htupB_ae : AEMeasurable (fun ω i ↦ B i ω) P := .of_eval hB
  have hAi_Bi_indep : ∀ i : Fin n, IndepFun (A i) (B i) P := fun i ↦
    hIndepAB.comp (measurable_pi_apply i) (measurable_pi_apply i)
  have hZ_map_i : ∀ i : Fin n, P.map (Z i) = (P.map (A i)).prod (P.map (B i)) :=
    fun i ↦ (hAi_Bi_indep i).map_prod_eq_prod_map_map (hA i) (hB i)
  have hZ_indep : ProbabilityTheory.iIndepFun Z P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map hZ_ae]
    let zipFn : (Fin n → Fin 4) × (Fin n → Fin 4) → (Fin n → Fin 4 × Fin 4) :=
      fun uv i ↦ (uv.1 i, uv.2 i)
    have hzip_meas : Measurable zipFn :=
      measurable_pi_iff.mpr fun i ↦
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)
    have hmap_comp : P.map (fun ω i ↦ Z i ω) =
        (P.map (fun ω ↦ (fun i ↦ A i ω, fun i ↦ B i ω))).map zipFn :=
      (AEMeasurable.map_map_of_aemeasurable hzip_meas.aemeasurable (htupA_ae.prodMk htupB_ae)).symm
    rw [hmap_comp, hIndepAB.map_prod_eq_prod_map_map htupA_ae htupB_ae,
      hIndepA.map_fun_eq_pi_map hA, hIndepB.map_fun_eq_pi_map hB]
    have : ∀ i : Fin n, IsProbabilityMeasure (P.map (A i)) := fun i ↦
      ⟨by rw [Measure.map_apply_of_aemeasurable (hA i) .univ, Set.preimage_univ, measure_univ]⟩
    have : ∀ i : Fin n, IsProbabilityMeasure (P.map (B i)) := fun i ↦
      ⟨by rw [Measure.map_apply_of_aemeasurable (hB i) .univ, Set.preimage_univ, measure_univ]⟩
    have : ∀ i : Fin n, IsProbabilityMeasure (P.map (Z i)) := fun i ↦
      ⟨by rw [Measure.map_apply_of_aemeasurable (hZ_ae i) .univ, Set.preimage_univ, measure_univ]⟩
    refine Measure.ext_of_singleton fun w ↦ ?_
    rw [Measure.map_apply hzip_meas .of_discrete]
    have hpre : zipFn ⁻¹' {w} =
        ({fun i ↦ (w i).1} : Set (Fin n → Fin 4)) ×ˢ ({fun i ↦ (w i).2} : Set (Fin n → Fin 4)) := by
      ext ⟨u, v⟩
      simp only [zipFn, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, funext_iff,
        Prod.ext_iff]
      exact forall_and
    have hsing_pi : ∀ {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
        (μ : Fin n → Measure α) [∀ i, SigmaFinite (μ i)] (u : Fin n → α),
        (Measure.pi μ) {u} = ∏ i : Fin n, μ i {u i} := by
      intro α _ _ μ _ u
      have hu : ({u} : Set (Fin n → α)) = Set.univ.pi fun i ↦ {u i} := by
        ext x; simp [funext_iff]
      rw [hu, Measure.pi_pi]
    rw [hpre, Measure.prod_prod, hsing_pi, hsing_pi, hsing_pi, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [hZ_map_i i]
    have hw_prod : ({w i} : Set (Fin 4 × Fin 4)) = {(w i).1} ×ˢ {(w i).2} := by
      ext ⟨x, y⟩; simp [Prod.ext_iff]
    rw [hw_prod, Measure.prod_prod]
  let matchFn : Fin 4 × Fin 4 → ℕ := fun cd ↦ if cd.1 = cd.2 then 1 else 0
  have hY_comp : Y = fun i ↦ matchFn ∘ Z i := by
    ext i ω; rfl
  refine ⟨?_, ?_⟩
  · rw [hY_comp]
    exact hZ_indep.comp (fun _ ↦ matchFn) (fun _ ↦ .of_discrete)
  · intro i
    let diagSet : Set (Fin 4 × Fin 4) := {cd | cd.1 = cd.2}
    have hpre_diag : {ω : Ω | Y i ω = 1} = Z i ⁻¹' diagSet := by
      ext ω
      simp [Y, Z, diagSet]
    rw [hpre_diag, ← map_measureReal_apply_of_aemeasurable (hZ_ae i) .of_discrete, hZ_map_i i]
    have : IsProbabilityMeasure (P.map (A i)) :=
      ⟨by rw [Measure.map_apply_of_aemeasurable (hA i) .univ, Set.preimage_univ, measure_univ]⟩
    have : IsProbabilityMeasure (P.map (B i)) :=
      ⟨by rw [Measure.map_apply_of_aemeasurable (hB i) .univ, Set.preimage_univ, measure_univ]⟩
    have hdiag_fin : diagSet = ↑(Finset.univ.image fun c : Fin 4 ↦ (c, c)) := by
      ext ⟨c₁, c₂⟩
      simp [diagSet, eq_comm]
    rw [hdiag_fin, ← sum_measureReal_singleton,
      Finset.sum_image (fun c₁ _ c₂ _ h ↦ (Prod.ext_iff.mp h).1)]
    have hterm : ∀ c : Fin 4,
        ((P.map (A i)).prod (P.map (B i))).real {(c, c)} = q c ^ 2 := by
      intro c
      have hprod_sing : ({(c, c)} : Set (Fin 4 × Fin 4)) = {c} ×ˢ {c} := by
        ext ⟨x, y⟩; simp [Prod.ext_iff]
      rw [measureReal_def, hprod_sing, Measure.prod_prod, ENNReal.toReal_mul,
        ← measureReal_def, ← measureReal_def,
        map_measureReal_apply_of_aemeasurable (hA i) .of_discrete,
        map_measureReal_apply_of_aemeasurable (hB i) .of_discrete]
      change P.real {ω | A i ω = c} * P.real {ω | B i ω = c} = q c ^ 2
      rw [hAq i c, hBq i c, sq]
    simp only [Fin.sum_univ_four, hterm]

/-- Joint-law corollary for **Remark 4.3** (`SteinIntro.tex:2079-2110`; `stmts-review-05C`
optional strengthening): the vector `(Y 0 ω, ..., Y (n - 1) ω)` of DNA match indicators has the
product distribution `Measure.pi (fun i ↦ P.map (Y i))`, where each marginal `P.map (Y i)` is
supported on `{0, 1}` with `(P.map (Y i)).real {1} = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2`. -/
theorem dna_match_map_eq_pi
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {A B : Fin n → Ω → Fin 4} {q : Fin 4 → ℝ}
    (hA : ∀ i : Fin n, AEMeasurable (A i) P)
    (hB : ∀ i : Fin n, AEMeasurable (B i) P)
    (hIndepA : ProbabilityTheory.iIndepFun A P)
    (hIndepB : ProbabilityTheory.iIndepFun B P)
    (hIndepAB : ProbabilityTheory.IndepFun (fun ω i ↦ A i ω) (fun ω i ↦ B i ω) P)
    (hAq : ∀ (i : Fin n) (c : Fin 4), P.real {ω | A i ω = c} = q c)
    (hBq : ∀ (i : Fin n) (c : Fin 4), P.real {ω | B i ω = c} = q c) :
    let Y : Fin n → Ω → ℕ := fun i ω ↦ if A i ω = B i ω then 1 else 0
    P.map (fun ω i ↦ Y i ω) = Measure.pi (fun i ↦ P.map (Y i)) ∧
      ∀ i : Fin n, (P.map (Y i)).real {1} = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
  intro Y
  have hmain := dna_match_iIndepFun_and_prob P hA hB hIndepA hIndepB hIndepAB hAq hBq
  have hY_ae : ∀ i : Fin n, AEMeasurable (Y i) P := fun i ↦
    ((Measurable.of_discrete : Measurable fun cd : Fin 4 × Fin 4 ↦
      if cd.1 = cd.2 then (1 : ℕ) else 0).comp_aemeasurable ((hA i).prodMk (hB i)))
  refine ⟨hmain.1.map_fun_eq_pi_map hY_ae, fun i ↦ ?_⟩
  rw [map_measureReal_apply_of_aemeasurable (hY_ae i) .of_discrete]
  exact hmain.2 i

end SteinMethod
