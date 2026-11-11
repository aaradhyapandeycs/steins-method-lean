/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Geometric.Basic
import Formalization.SizeBias.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Discrete Equilibrium Couplings and Geometric Approximation (`Formalization.Geometric.Equilibrium`)

Develops Section 6.2 (*Discrete equilibrium*, `SteinIntro.tex:3278-3330`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* **Remark 6.2 & discrete equilibrium existence/uniqueness** (`\label{rem175}`,
  `SteinIntro.tex:3290-3291, 3304-3310`; `ISSUE-6.4`): `isDiscreteEquilibrium_iff_tail`
  (stationary-excess tail formula $\mathbb{P}(W^e = k) = \frac{p}{1 - p}\mathbb{P}(W > k)$ for
  $0 < p < 1$), `existsUnique_isDiscreteEquilibrium_measure` (existence and uniqueness of the
  discrete equilibrium law for $0 < p < 1$, formalizing `SteinIntro.tex:3290-3291`), and
  `not_unique_isDiscreteEquilibrium_one` (failure of uniqueness at the boundary $p = 1$).
* **Proposition 6.4** (`\label{prop172}`, `SteinIntro.tex:3292-3296`; `ISSUE-6.4`):
  `isDiscreteEquilibrium_of_isSizeBias_uniform`.
* **Theorem 6.5** (`\label{thm177}`, `SteinIntro.tex:3312-3319`):
  `integrable_sub_of_isDiscreteEquilibrium` and `tvDist_le_of_isDiscreteEquilibrium`.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace SteinMethod

/-! ### Finite-difference, discrete-measure, and integrability helpers -/

private lemma sum_range_fwdDiff (f : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, fwdDiff 1 f k = f m - f 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, fwdDiff]
      ring

private lemma abs_fwdDiff_sub_le_two_mul_abs {f : ℕ → ℝ}
    (hf : ∀ k : ℕ, |fwdDiff 1 f k| ≤ 1) (a b : ℕ) :
    |fwdDiff 1 f a - fwdDiff 1 f b| ≤ 2 * |(b : ℝ) - (a : ℝ)| := by
  by_cases hab : a = b
  · subst hab
    simp
  · have hge1 : (1 : ℝ) ≤ |(b : ℝ) - (a : ℝ)| := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hle : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have hle : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
    calc
      |fwdDiff 1 f a - fwdDiff 1 f b|
        ≤ |fwdDiff 1 f a| + |fwdDiff 1 f b| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hf a) (hf b)
      _ = 2 * 1 := by ring
      _ ≤ 2 * |(b : ℝ) - (a : ℝ)| := by linarith

private lemma integrable_comp_of_abs_fwdDiff_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {W : Ω → ℕ} (hW : AEMeasurable W P) (hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P)
    {f : ℕ → ℝ} (hf : ∃ C : ℝ, ∀ k : ℕ, |fwdDiff 1 f k| ≤ C) :
    Integrable (fun ω ↦ f (W ω)) P := by
  obtain ⟨C, hC⟩ := hf
  refine ((integrable_const |f 0|).add (hW_int.const_mul (max C 0))).mono'
    ((Measurable.of_discrete : Measurable f).comp_aemeasurable hW).aestronglyMeasurable
    (Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs]
  exact abs_le_of_abs_fwdDiff_le hC (W ω)

private lemma integrable_fwdDiff_comp
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsFiniteMeasure P']
    {We : Ω' → ℕ} (hWe : AEMeasurable We P')
    {f : ℕ → ℝ} (hf : ∃ C : ℝ, ∀ k : ℕ, |fwdDiff 1 f k| ≤ C) :
    Integrable (fun ω' ↦ fwdDiff 1 f (We ω')) P' := by
  obtain ⟨C, hC⟩ := hf
  refine (integrable_const (max C 0)).mono'
    ((Measurable.of_discrete : Measurable (fwdDiff 1 f)).comp_aemeasurable hWe).aestronglyMeasurable
    (Eventually.of_forall fun ω' ↦ ?_)
  rw [Real.norm_eq_abs]
  exact (hC (We ω')).trans (le_max_left C 0)

private lemma measureReal_Ioi_eq_tsum (μ : Measure ℕ) [IsFiniteMeasure μ] (k : ℕ) :
    μ.real (Set.Ioi k) = ∑' m : ℕ, (Set.Ioi k).indicator (fun m ↦ μ.real {m}) m := by
  have hind : Integrable ((Set.Ioi k).indicator (1 : ℕ → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator .of_discrete
  have hcnt := integral_countable hind
  rw [integral_indicator_one .of_discrete] at hcnt
  rw [hcnt]
  congr 1 with m
  by_cases hm : m ∈ Set.Ioi k
  · simp [hm]
  · simp [hm]

private lemma hasSum_integral_nat {μ : Measure ℕ} {g : ℕ → ℝ} (hg : Integrable g μ) :
    HasSum (fun m : ℕ ↦ μ.real {m} * g m) (∫ m, g m ∂μ) := by
  have hg' : Integrable g (Measure.sum fun m : ℕ ↦ μ {m} • Measure.dirac m) := by
    rwa [Measure.sum_smul_dirac μ]
  have h := hasSum_integral_measure hg'
  rw [Measure.sum_smul_dirac μ] at h
  convert h using 1
  ext m
  rw [integral_smul_measure, integral_dirac, measureReal_def, smul_eq_mul]

/-! ### Remark 6.2 & Existence/Uniqueness of the Discrete Equilibrium Distribution (`0 < p < 1`) -/

/-- **Remark 6.2** (stationary-excess characterization, restricted to $0 < p < 1$,
`\label{rem175}`, `SteinIntro.tex:3304-3310`; `ISSUE-6.4`): for $0 < p < 1$ and an integer-valued
random variable $W \ge 0$ with $\mathbb{E}[W] = (1 - p)/p$, a random variable $W^e$ satisfies
`IsDiscreteEquilibrium P p W P' We` if and only if it has the renewal-theory stationary-excess
point probabilities $\mathbb{P}(W^e = k) = \frac{p}{1 - p}\mathbb{P}(W > k)$
($= \mathbb{P}(W > k) / \mathbb{E}[W]$) for all $k \in \mathbb{N}$.

Reading note: Remark 6.2's *"the same as that from renewal theory"* is formalized as this
stationary-excess formula $\mathbb{P}(W^e = k) = \mathbb{P}(W > k) / \mathbb{E}[W]$ (stationarity
of the delayed renewal process $Y^e + Y_1 + \cdots$ is Remark 5.3 in §5). Existence and uniqueness
of this law on $\mathbb{N}$ (`existsUnique_isDiscreteEquilibrium_measure`) formalizes the prose at
`SteinIntro.tex:3290-3291`. -/
theorem isDiscreteEquilibrium_iff_tail
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} (hp0 : 0 < p) (hp_lt : p < 1)
    {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P)
    (hW_mean : ∫ ω, (W ω : ℝ) ∂P = (1 - p) / p)
    {We : Ω' → ℕ} (hWe : AEMeasurable We P') :
    IsDiscreteEquilibrium P p W P' We ↔
      ∀ k : ℕ, P'.real {ω' | We ω' = k} = p / (1 - p) * P.real {ω | k < W ω} := by
  have h1p_pos : 0 < 1 - p := sub_pos.mpr hp_lt
  have _ : IsProbabilityMeasure (P.map W) :=
    (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  have _ : IsProbabilityMeasure (P'.map We) :=
    (Measure.isProbabilityMeasure_map_iff hWe).mpr ‹_›
  constructor
  · intro hEq k
    let f : ℕ → ℝ := (Set.Ici (k + 1)).indicator 1
    have hf0 : f 0 = 0 := Set.indicator_of_notMem (by simp) 1
    have hfwd : ∀ j : ℕ, fwdDiff 1 f j = ({k} : Set ℕ).indicator 1 j := fun j ↦ by
      rw [fwdDiff]
      by_cases hj : j < k
      · have h1 : j + 1 ∉ Set.Ici (k + 1) := by simp only [Set.mem_Ici]; omega
        have h2 : j ∉ Set.Ici (k + 1) := by simp only [Set.mem_Ici]; omega
        have h3 : j ∉ ({k} : Set ℕ) := by simp only [Set.mem_singleton_iff]; omega
        simp [f, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
          Set.indicator_of_notMem h3]
      · by_cases hjeq : j = k
        · subst hjeq
          have h1 : j + 1 ∈ Set.Ici (j + 1) := Set.mem_Ici.mpr le_rfl
          have h2 : j ∉ Set.Ici (j + 1) := by simp only [Set.mem_Ici]; omega
          dsimp only [f]
          rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2]
          simp
        · have hgt : k + 1 ≤ j := by omega
          have h1 : j + 1 ∈ Set.Ici (k + 1) := by simp only [Set.mem_Ici]; omega
          have h2 : j ∈ Set.Ici (k + 1) := hgt
          have h3 : j ∉ ({k} : Set ℕ) := hjeq
          simp [f, Set.indicator_of_mem h1, Set.indicator_of_mem h2,
            Set.indicator_of_notMem h3]
    have hf_bdd : ∃ C : ℝ, ∀ j : ℕ, |fwdDiff 1 f j| ≤ C := by
      refine ⟨1, fun j ↦ ?_⟩
      rw [hfwd j]
      by_cases hj : j = k
      · simp [hj]
      · simp [hj]
    have hId := hEq.2.2.2.2.2.2 f hf_bdd
    rw [hf0, mul_zero, sub_zero] at hId
    have hLHS : ∫ ω, f (W ω) ∂P = P.real {ω | k < W ω} := by
      rw [← integral_map hW Measurable.of_discrete.aestronglyMeasurable,
        integral_indicator_one .of_discrete, map_measureReal_apply_of_aemeasurable hW .of_discrete]
      exact congrArg P.real (Set.ext fun ω ↦ Nat.succ_le_iff)
    have hRHS : ∫ ω', fwdDiff 1 f (We ω') ∂P' = P'.real {ω' | We ω' = k} := by
      simp_rw [hfwd]
      rw [← integral_map hWe Measurable.of_discrete.aestronglyMeasurable,
        integral_indicator_one .of_discrete, map_measureReal_apply_of_aemeasurable hWe .of_discrete]
      rfl
    rw [hLHS, hRHS] at hId
    exact (eq_div_iff h1p_pos.ne').mpr (by linarith) |>.trans (div_mul_eq_mul_div p (1 - p) _).symm
  · intro hTail
    refine ⟨hp0, hp_lt.le, hW, hW_int, hW_mean, hWe, fun f hf ↦ ?_⟩
    obtain ⟨C, hC⟩ := hf
    let μW := P.map W
    let μWe := P'.map We
    have hid_int : Integrable (fun m : ℕ ↦ (m : ℝ)) μW :=
      (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable hW).mpr hW_int
    have hf_sub_int : Integrable (fun m : ℕ ↦ f m - f 0) μW := by
      have hfW := integrable_comp_of_abs_fwdDiff_le hW hW_int ⟨C, hC⟩
      have hf_μW : Integrable f μW :=
        (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable hW).mpr hfW
      exact hf_μW.sub' (integrable_const (f 0))
    have hfwd_int : Integrable (fwdDiff 1 f) μWe :=
      (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable hWe).mpr
        (integrable_fwdDiff_comp hWe ⟨C, hC⟩)
    let F : ℕ → ℕ → ℝ := fun m k ↦
      (Set.Iio m).indicator (fun k ↦ μW.real {m} * fwdDiff 1 f k) k
    have hF_norm_row : ∀ m : ℕ, Summable (fun k : ℕ ↦ ‖F m k‖) := fun m ↦
      summable_of_ne_finset_zero (s := Finset.range m) fun k hk ↦ by
        have hnot : k ∉ Set.Iio m := by simpa [Finset.mem_range] using hk
        simp [F, Set.indicator_of_notMem hnot]
    have hF_row_bound : ∀ m : ℕ, (∑' k : ℕ, ‖F m k‖) ≤ μW.real {m} * (max C 0 * (m : ℝ)) :=
      fun m ↦ by
        rw [tsum_eq_sum (s := Finset.range m) fun k hk ↦ by
          have hnot : k ∉ Set.Iio m := by simpa [Finset.mem_range] using hk
          simp [F, Set.indicator_of_notMem hnot]]
        calc
          ∑ k ∈ Finset.range m, ‖F m k‖
            = ∑ k ∈ Finset.range m, μW.real {m} * |fwdDiff 1 f k| := by
              refine Finset.sum_congr rfl fun k hk ↦ ?_
              have hmem : k ∈ Set.Iio m := Finset.mem_range.mp hk
              simp [F, Set.indicator_of_mem hmem, abs_of_nonneg measureReal_nonneg]
          _ ≤ ∑ _k ∈ Finset.range m, μW.real {m} * max C 0 := by
              refine Finset.sum_le_sum fun k _ ↦
                mul_le_mul_of_nonneg_left ((hC k).trans (le_max_left C 0)) measureReal_nonneg
          _ = μW.real {m} * (max C 0 * (m : ℝ)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
    have h_m_sum : Summable (fun m : ℕ ↦ μW.real {m} * (max C 0 * (m : ℝ))) := by
      have hid_cnt := hasSum_integral_nat hid_int
      have hmul := hid_cnt.mul_left (max C 0)
      refine hmul.summable.congr fun m ↦ ?_
      ring
    have hF_uncurry_norm : Summable (Function.uncurry fun m k ↦ ‖F m k‖) :=
      (summable_prod_of_nonneg fun _ ↦ norm_nonneg _).mpr
        ⟨hF_norm_row, Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _)
          hF_row_bound h_m_sum⟩
    have hF_comm := (Summable.of_norm hF_uncurry_norm).tsum_comm'
      (fun m ↦ Summable.of_norm (hF_norm_row m))
      (fun k ↦ Summable.of_norm <| by
        have hcnt : Summable (fun m : ℕ ↦ μW.real {m}) :=
          ((hasSum_integral_nat (integrable_const (μ := μW) (1 : ℝ))).summable).congr
            fun m ↦ mul_one _
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
          (fun m ↦ ?_) (hcnt.mul_right |fwdDiff 1 f k|)
        by_cases hm : k ∈ Set.Iio m
        · simp [F, Set.indicator_of_mem hm, abs_of_nonneg measureReal_nonneg]
        · dsimp only [F]
          rw [Set.indicator_of_notMem hm, norm_zero]
          positivity)
    have hLHS_row : ∀ m : ℕ, (∑' k : ℕ, F m k) = μW.real {m} * (f m - f 0) := fun m ↦ by
      rw [tsum_eq_sum (s := Finset.range m) fun k hk ↦ by
        have hnot : k ∉ Set.Iio m := by simpa [Finset.mem_range] using hk
        simp [F, Set.indicator_of_notMem hnot]]
      have hcongr : ∑ k ∈ Finset.range m, F m k =
          ∑ k ∈ Finset.range m, μW.real {m} * fwdDiff 1 f k := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        dsimp only [F]
        exact Set.indicator_of_mem (show k ∈ Set.Iio m from Finset.mem_range.mp hk) _
      rw [hcongr, ← Finset.mul_sum, sum_range_fwdDiff]
    have hRHS_col : ∀ k : ℕ, (∑' m : ℕ, F m k) = μW.real (Set.Ioi k) * fwdDiff 1 f k := fun k ↦ by
      rw [measureReal_Ioi_eq_tsum μW k, ← tsum_mul_right]
      congr 1 with m
      by_cases hm : k < m
      · have h1 : k ∈ Set.Iio m := hm
        have h2 : m ∈ Set.Ioi k := hm
        simp [F, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      · have h1 : k ∉ Set.Iio m := hm
        have h2 : m ∉ Set.Ioi k := hm
        simp [F, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    simp_rw [hLHS_row, hRHS_col] at hF_comm
    have hIntW : (∫ ω, f (W ω) ∂P) - f 0 = ∑' m : ℕ, μW.real {m} * (f m - f 0) := by
      have hfW := integrable_comp_of_abs_fwdDiff_le hW hW_int ⟨C, hC⟩
      have h1 : (∫ ω, f (W ω) ∂P) - f 0 = ∫ ω, (fun m ↦ f m - f 0) (W ω) ∂P := by
        change (∫ ω, f (W ω) ∂P) - f 0 = ∫ ω, (f (W ω) - f 0) ∂P
        rw [integral_sub hfW (integrable_const (f 0)), integral_const, probReal_univ, one_smul]
      rw [h1,
        ← integral_map hW
          (Measurable.of_discrete : Measurable fun m ↦ f m - f 0).aestronglyMeasurable,
        integral_countable hf_sub_int]
      simp [smul_eq_mul]
    have hIntWe : ∫ ω', fwdDiff 1 f (We ω') ∂P' =
        ∑' k : ℕ, μWe.real {k} * fwdDiff 1 f k := by
      rw [← integral_map hWe Measurable.of_discrete.aestronglyMeasurable,
        integral_countable hfwd_int]
      simp [smul_eq_mul]
    have hTail_map : ∀ k : ℕ, μWe.real {k} = p / (1 - p) * μW.real (Set.Ioi k) := fun k ↦ by
      dsimp only [μWe, μW]
      rw [map_measureReal_apply_of_aemeasurable hWe .of_discrete,
        map_measureReal_apply_of_aemeasurable hW .of_discrete]
      exact hTail k
    calc
      p * (∫ ω, f (W ω) ∂P) - p * f 0
        = p * ((∫ ω, f (W ω) ∂P) - f 0) := by ring
      _ = p * ∑' m : ℕ, μW.real {m} * (f m - f 0) := by rw [hIntW]
      _ = p * ∑' k : ℕ, μW.real (Set.Ioi k) * fwdDiff 1 f k := by rw [hF_comm]
      _ = ∑' k : ℕ, p * (μW.real (Set.Ioi k) * fwdDiff 1 f k) := tsum_mul_left.symm
      _ = ∑' k : ℕ, (1 - p) * (μWe.real {k} * fwdDiff 1 f k) := by
          congr 1 with k
          rw [hTail_map k]
          field_simp [h1p_pos.ne']
      _ = (1 - p) * ∑' k : ℕ, μWe.real {k} * fwdDiff 1 f k := tsum_mul_left
      _ = (1 - p) * ∫ ω', fwdDiff 1 f (We ω') ∂P' := by rw [hIntWe]

/-- **Existence and uniqueness of the discrete equilibrium distribution**
(`SteinIntro.tex:3290-3291, 3304-3310`; `ISSUE-6.4`): for $0 < p < 1$ and an integer-valued random
variable $W \ge 0$ with $\mathbb{E}[W] = (1 - p)/p$, there exists a unique probability measure
$\nu$ on $\mathbb{N}$ such that `id` under $\nu$ has the discrete equilibrium distribution with
respect to $W$. -/
theorem existsUnique_isDiscreteEquilibrium_measure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp0 : 0 < p) (hp_lt : p < 1)
    {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P)
    (hW_mean : ∫ ω, (W ω : ℝ) ∂P = (1 - p) / p) :
    ∃! ν : Measure ℕ, ∃ _ : IsProbabilityMeasure ν, IsDiscreteEquilibrium P p W ν id := by
  have h1p_pos : 0 < 1 - p := sub_pos.mpr hp_lt
  let μW := P.map W
  have _ : IsProbabilityMeasure μW :=
    (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
  have hid_int : Integrable (fun m : ℕ ↦ (m : ℝ)) μW :=
    (integrable_map_measure Measurable.of_discrete.aestronglyMeasurable hW).mpr hW_int
  let w : ℕ → ℝ := fun k ↦ p / (1 - p) * P.real {ω | k < W ω}
  have hw_nn : ∀ k : ℕ, 0 ≤ w k := fun k ↦
    mul_nonneg (div_nonneg hp0.le h1p_pos.le) measureReal_nonneg
  have h_sum_tail : HasSum w 1 := by
    let F : ℕ → ℕ → ℝ := fun m k ↦ (Set.Iio m).indicator (fun _ ↦ μW.real {m}) k
    have hF_row : ∀ m : ℕ, HasSum (fun k : ℕ ↦ F m k) (μW.real {m} * (m : ℝ)) := fun m ↦ by
      have hzero : ∀ k ∉ Finset.range m, F m k = 0 := fun k hk ↦ by
        have hnot : k ∉ Set.Iio m := by simpa [Finset.mem_range] using hk
        exact Set.indicator_of_notMem hnot _
      have hsum_fn : Summable (fun k : ℕ ↦ F m k) := summable_of_ne_finset_zero hzero
      have htsum : (∑' k : ℕ, F m k) = μW.real {m} * (m : ℝ) := by
        rw [tsum_eq_sum hzero]
        calc
          ∑ k ∈ Finset.range m, F m k = ∑ _k ∈ Finset.range m, μW.real {m} := by
            refine Finset.sum_congr rfl fun k hk ↦ ?_
            dsimp only [F]
            exact Set.indicator_of_mem (show k ∈ Set.Iio m from Finset.mem_range.mp hk) _
          _ = μW.real {m} * (m : ℝ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      exact htsum ▸ hsum_fn.hasSum
    have hm_hasSum : HasSum (fun m : ℕ ↦ μW.real {m} * (m : ℝ)) ((1 - p) / p) := by
      have hcnt := hasSum_integral_nat hid_int
      rwa [integral_map hW Measurable.of_discrete.aestronglyMeasurable, hW_mean] at hcnt
    have hF_nn : ∀ x : ℕ × ℕ, 0 ≤ Function.uncurry F x := fun ⟨m, k⟩ ↦
      Set.indicator_nonneg (fun _ _ ↦ measureReal_nonneg) k
    have hF_uncurry : Summable (Function.uncurry F) :=
      (summable_prod_of_nonneg hF_nn).mpr
        ⟨fun m ↦ (hF_row m).summable,
          (hm_hasSum.summable.congr fun m ↦ ((hF_row m).tsum_eq).symm)⟩
    have hcol : ∀ k : ℕ, (∑' m : ℕ, F m k) = P.real {ω | k < W ω} := fun k ↦ by
      have hmap : P.real {ω | k < W ω} = μW.real (Set.Ioi k) := by
        dsimp only [μW]
        rw [map_measureReal_apply_of_aemeasurable hW .of_discrete]
        rfl
      rw [hmap, measureReal_Ioi_eq_tsum μW k]
      refine tsum_congr fun m ↦ ?_
      by_cases hm : k < m
      · have h1 : k ∈ Set.Iio m := hm
        have h2 : m ∈ Set.Ioi k := hm
        simp [F, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      · have h1 : k ∉ Set.Iio m := hm
        have h2 : m ∉ Set.Ioi k := hm
        simp [F, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have hcomm := hF_uncurry.tsum_comm' (fun m ↦ (hF_row m).summable)
      (fun k ↦ by
        have hcnt : Summable (fun m : ℕ ↦ μW.real {m}) :=
          ((hasSum_integral_nat (integrable_const (μ := μW) (1 : ℝ))).summable).congr
            fun m ↦ mul_one _
        refine Summable.of_nonneg_of_le (fun m ↦ hF_nn (m, k)) (fun m ↦ ?_) hcnt
        by_cases hm : k < m
        · have h1 : k ∈ Set.Iio m := hm
          simp [F, Set.indicator_of_mem h1]
        · have h1 : k ∉ Set.Iio m := hm
          simp [F, Set.indicator_of_notMem h1, measureReal_nonneg])
    simp_rw [fun m ↦ (hF_row m).tsum_eq, hcol] at hcomm
    have htail_sum : Summable (fun k : ℕ ↦ P.real {ω | k < W ω}) := by
      have h := hF_uncurry.prod_symm
      exact ((summable_prod_of_nonneg fun ⟨k, m⟩ ↦ hF_nn (m, k)).mp h).2.congr hcol
    have htsum_eq : ∑' k : ℕ, P.real {ω | k < W ω} = (1 - p) / p := by
      linarith [hcomm, hm_hasSum.tsum_eq]
    have hw_hasSum := (htail_sum.hasSum.mul_left (p / (1 - p)))
    rw [htsum_eq] at hw_hasSum
    have hcancel : p / (1 - p) * ((1 - p) / p) = 1 := by field_simp [hp0.ne', h1p_pos.ne']
    rwa [hcancel] at hw_hasSum
  let ν : Measure ℕ := Measure.sum fun k : ℕ ↦ ENNReal.ofReal (w k) • Measure.dirac k
  have hν_prob : IsProbabilityMeasure ν := h_sum_tail.isProbabilityMeasure_sum_dirac hw_nn
  have hν_real : ∀ k : ℕ, ν.real {k} = w k := fun k ↦ by
    rw [measureReal_def, Measure.sum_smul_dirac_singleton, ENNReal.toReal_ofReal (hw_nn k)]
  refine ⟨ν, ⟨hν_prob, ?_⟩, ?_⟩
  · exact (isDiscreteEquilibrium_iff_tail P ν hp0 hp_lt hW hW_int hW_mean
      measurable_id.aemeasurable).mpr fun k ↦ hν_real k
  · rintro ν' ⟨hν'_prob, hEq'⟩
    have htail' := (isDiscreteEquilibrium_iff_tail P ν' hp0 hp_lt hW hW_int hW_mean
      measurable_id.aemeasurable).mp hEq'
    exact Measure.ext_of_measureReal_singleton fun k ↦ (htail' k).trans (hν_real k).symm

/-- Non-uniqueness witness at $p = 1$ (`ISSUE-6.4`, `SteinIntro.tex:3290-3291, 3304-3310`): for
$W \equiv 0$ under $\delta_0 = \mathrm{Ge}^0(1)$, both $\delta_0$ and $\delta_1$ satisfy
`IsDiscreteEquilibrium`, so `(6.1)` does not determine a unique probability law at $p = 1$. -/
theorem not_unique_isDiscreteEquilibrium_one :
    IsDiscreteEquilibrium (Measure.dirac (0 : ℕ)) 1 id (Measure.dirac (0 : ℕ)) id ∧
      IsDiscreteEquilibrium (Measure.dirac (0 : ℕ)) 1 id (Measure.dirac (1 : ℕ)) id ∧
      (Measure.dirac (0 : ℕ) : Measure ℕ) ≠ Measure.dirac 1 := by
  have hint : Integrable (fun k : ℕ ↦ (k : ℝ)) (Measure.dirac (0 : ℕ)) :=
    integrable_dirac (by simp)
  have hmean : ∫ k : ℕ, (k : ℝ) ∂Measure.dirac (0 : ℕ) = (1 - (1 : ℝ)) / 1 := by
    rw [integral_dirac]
    norm_num
  have h0 : IsDiscreteEquilibrium (Measure.dirac (0 : ℕ)) 1 id (Measure.dirac (0 : ℕ)) id := by
    refine ⟨zero_lt_one, le_rfl, measurable_id.aemeasurable, hint, hmean,
      measurable_id.aemeasurable, fun f _ ↦ ?_⟩
    rw [integral_dirac]
    simp
  have h1 : IsDiscreteEquilibrium (Measure.dirac (0 : ℕ)) 1 id (Measure.dirac (1 : ℕ)) id := by
    refine ⟨zero_lt_one, le_rfl, measurable_id.aemeasurable, hint, hmean,
      measurable_id.aemeasurable, fun f _ ↦ ?_⟩
    rw [integral_dirac]
    simp
  refine ⟨h0, h1, fun heq ↦ ?_⟩
  have h := congrArg (fun μ : Measure ℕ ↦ μ {0}) heq
  simp at h

/-! ### Proposition 6.4: Constructive Size-Bias / Uniform Characterization -/

/-- **Proposition 6.4** (`\label{prop172}`, `SteinIntro.tex:3292-3296`; `ISSUE-6.4`): if
$0 < p \le 1$, $W \ge 0$ is integer-valued with $\mathbb{E}[W] = (1 - p)/p$, $W^s$ has the
size-bias distribution of $W$, and conditional on $W^s$, $W^e$ is uniform on
$\{0, 1, \dots, W^s - 1\}$, then $W^e$ has the discrete equilibrium distribution with respect to
$W$. -/
theorem isDiscreteEquilibrium_of_isSizeBias_uniform
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {W : Ω → ℕ} (hW : AEMeasurable W P)
    (hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P)
    (hW_mean : ∫ ω, (W ω : ℝ) ∂P = (1 - p) / p)
    {Ws We : Ω' → ℕ}
    (hSB : IsSizeBias P (fun ω ↦ (W ω : ℝ)) P' (fun ω' ↦ (Ws ω' : ℝ)))
    (hWe : AEMeasurable We P')
    (hUnif : ∀ m j : ℕ,
      P'.real {ω' | Ws ω' = m ∧ We ω' = j} =
        if j < m then P'.real {ω' | Ws ω' = m} / (m : ℝ) else 0) :
    IsDiscreteEquilibrium P p W P' We := by
  rcases eq_or_lt_of_le hp1 with rfl | hp_lt
  · refine ⟨hp0, le_rfl, hW, hW_int, hW_mean, hWe, fun f _ ↦ ?_⟩
    have hmean0 : ∫ ω, (W ω : ℝ) ∂P = 0 := by simpa using hW_mean
    have hW0_ae : (fun ω ↦ (W ω : ℝ)) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω ↦ Nat.cast_nonneg (W ω)) hW_int).mp hmean0
    have hfW_ae : (fun ω ↦ f (W ω)) =ᵐ[P] fun _ ↦ f 0 := by
      filter_upwards [hW0_ae] with ω hω
      have hWn : W ω = 0 := Nat.cast_eq_zero.mp hω
      rw [hWn]
    rw [integral_congr_ae hfW_ae, integral_const, probReal_univ, one_smul]
    ring
  · refine (isDiscreteEquilibrium_iff_tail P P' hp0 hp_lt hW hW_int hW_mean hWe).mpr fun j ↦ ?_
    have h1p_pos : 0 < 1 - p := sub_pos.mpr hp_lt
    have hμ_pos : 0 < ∫ ω, (W ω : ℝ) ∂P := by
      rw [hW_mean]
      exact div_pos h1p_pos hp0
    let E : ℕ → Set Ω' := fun m ↦ {ω' | Ws ω' = m ∧ We ω' = j}
    have hE_nm : ∀ m : ℕ, NullMeasurableSet (E m) P' := fun m ↦ by
      have h1 : {ω' : Ω' | Ws ω' = m} = (fun ω' ↦ (Ws ω' : ℝ)) ⁻¹' {(m : ℝ)} := by
        ext ω'
        simp [Nat.cast_inj]
      have h2 : {ω' : Ω' | We ω' = j} = We ⁻¹' {j} := rfl
      change NullMeasurableSet ({ω' | Ws ω' = m} ∩ {ω' | We ω' = j}) P'
      rw [h1, h2]
      exact (hSB.2.2.1.nullMeasurableSet_preimage (measurableSet_singleton (m : ℝ))).inter
        (hWe.nullMeasurableSet_preimage .of_discrete)
    have hE_disj : Pairwise fun m₁ m₂ ↦ Disjoint (E m₁) (E m₂) := fun m₁ m₂ hne ↦
      Set.disjoint_left.mpr fun _ h1 h2 ↦ hne (h1.1.symm.trans h2.1)
    have hE_union : (⋃ m : ℕ, E m) = {ω' | We ω' = j} := by
      ext ω'
      simp [E]
    have hENN : P' {ω' | We ω' = j} = ∑' m : ℕ, P' (E m) := by
      rw [← hE_union]
      exact measure_iUnion₀ (hE_disj.mono fun _ _ h ↦ h.aedisjoint) hE_nm
    have hSum_real : P'.real {ω' | We ω' = j} = ∑' m : ℕ, P'.real (E m) := by
      have hne_top : ∀ m : ℕ, P' (E m) ≠ ⊤ := fun m ↦ measure_ne_top P' (E m)
      have hsum_enn : Summable (fun m : ℕ ↦ P' (E m)) := ENNReal.summable
      have hlt_top : (∑' m : ℕ, P' (E m)) ≠ ⊤ := by
        rw [← hENN]
        exact measure_ne_top P' _
      rw [measureReal_def, hENN, ENNReal.tsum_toReal_eq hne_top]
      rfl
    have hSB_pmf : ∀ m : ℕ,
        P'.real {ω' | Ws ω' = m} = (m : ℝ) * P.real {ω | W ω = m} / ((1 - p) / p) := fun m ↦ by
      have h := hSB.measureReal_eq_singleton hμ_pos (m : ℝ)
      rw [hW_mean] at h
      have hsetWs : {ω' : Ω' | (Ws ω' : ℝ) = (m : ℝ)} = {ω' | Ws ω' = m} := by
        ext ω'; simp [Nat.cast_inj]
      have hsetW : {ω : Ω | (W ω : ℝ) = (m : ℝ)} = {ω | W ω = m} := by
        ext ω; simp [Nat.cast_inj]
      rwa [hsetWs, hsetW] at h
    let μW := P.map W
    have _ : IsProbabilityMeasure μW :=
      (Measure.isProbabilityMeasure_map_iff hW).mpr ‹_›
    have hterm : ∀ m : ℕ, P'.real (E m) =
        p / (1 - p) * (Set.Ioi j).indicator (fun m ↦ μW.real {m}) m := fun m ↦ by
      dsimp only [E]
      rw [hUnif m j]
      by_cases hjm : j < m
      · have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hjm)
        have hm_mem : m ∈ Set.Ioi j := hjm
        rw [ite_eq_left hjm, hSB_pmf m, Set.indicator_of_mem hm_mem]
        have hμW_m : μW.real {m} = P.real {ω | W ω = m} :=
          map_measureReal_apply_of_aemeasurable hW .of_discrete
        rw [hμW_m]
        field_simp [hm_pos.ne', hp0.ne', h1p_pos.ne']
      · have hm_not : m ∉ Set.Ioi j := hjm
        rw [ite_eq_right hjm, Set.indicator_of_notMem hm_not, mul_zero]
    rw [hSum_real]
    simp_rw [hterm]
    rw [tsum_mul_left, ← measureReal_Ioi_eq_tsum μW j]
    congr 1
    exact map_measureReal_apply_of_aemeasurable hW .of_discrete

/-! ### Theorem 6.5: Total Variation Bound via Discrete Equilibrium Coupling -/

/-- If $0 < p < 1$, $W \in L^2(P)$, and $W^e$ satisfies `IsDiscreteEquilibrium P p W P We`, then
$|(W^e : \mathbb{R}) - (W : \mathbb{R})|$ is integrable (`SteinIntro.tex:3312-3319`). -/
theorem integrable_sub_of_isDiscreteEquilibrium
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp_lt : p < 1) {W We : Ω → ℕ}
    (hW2 : MemLp (fun ω ↦ (W ω : ℝ)) 2 P)
    (hEq : IsDiscreteEquilibrium P p W P We) :
    Integrable (fun ω ↦ |(We ω : ℝ) - (W ω : ℝ)|) P := by
  rcases hEq with ⟨hp0, _, hW, hW_int, hW_mean, hWe, hStein⟩
  have h1p_pos : 0 < 1 - p := sub_pos.mpr hp_lt
  have hWsq_int : Integrable (fun ω ↦ (W ω : ℝ) ^ 2) P := hW2.integrable_sq
  let fM : ℕ → ℕ → ℝ := fun M k ↦ ∑ j ∈ Finset.range k, min (j : ℝ) (M : ℝ)
  have hfM_zero : ∀ M : ℕ, fM M 0 = 0 := fun _ ↦ rfl
  have hfM_fwd : ∀ M k : ℕ, fwdDiff 1 (fM M) k = min (k : ℝ) (M : ℝ) := fun M k ↦ by
    dsimp only [fM]
    rw [fwdDiff, Finset.sum_range_succ, add_sub_cancel_left]
  have hfM_le_sq : ∀ M k : ℕ, fM M k ≤ (k : ℝ) ^ 2 := fun M k ↦ by
    calc
      fM M k ≤ ∑ _j ∈ Finset.range k, (k : ℝ) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        exact (min_le_left _ _).trans (Nat.cast_le.mpr (Finset.mem_range.mp hj).le)
      _ = (k : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq]
  have hBoundM : ∀ M : ℕ,
      ∫⁻ ω, ENNReal.ofReal (min (We ω : ℝ) (M : ℝ)) ∂P ≤
        ENNReal.ofReal (p / (1 - p) * ∫ ω, (W ω : ℝ) ^ 2 ∂P) := fun M ↦ by
    have hf_bdd : ∃ C : ℝ, ∀ k : ℕ, |fwdDiff 1 (fM M) k| ≤ C := ⟨M, fun k ↦ by
      rw [hfM_fwd, abs_of_nonneg (le_min (Nat.cast_nonneg k) (Nat.cast_nonneg M))]
      exact min_le_right _ _⟩
    have hId := hStein (fM M) hf_bdd
    rw [hfM_zero M, mul_zero, sub_zero] at hId
    simp_rw [hfM_fwd] at hId
    have hfW_int : Integrable (fun ω ↦ fM M (W ω)) P :=
      integrable_comp_of_abs_fwdDiff_le hW hW_int hf_bdd
    have hmin_int : Integrable (fun ω ↦ min (We ω : ℝ) (M : ℝ)) P := by
      simpa only [hfM_fwd] using integrable_fwdDiff_comp hWe hf_bdd
    have hmin_nn : 0 ≤ᵐ[P] fun ω ↦ min (We ω : ℝ) (M : ℝ) :=
      Eventually.of_forall fun ω ↦ le_min (Nat.cast_nonneg (We ω)) (Nat.cast_nonneg M)
    have hIntLe : ∫ ω, fM M (W ω) ∂P ≤ ∫ ω, (W ω : ℝ) ^ 2 ∂P :=
      integral_mono hfW_int hWsq_int fun ω ↦ hfM_le_sq M (W ω)
    have hRealLe : ∫ ω, min (We ω : ℝ) (M : ℝ) ∂P ≤
        p / (1 - p) * ∫ ω, (W ω : ℝ) ^ 2 ∂P := by
      have hEqDiv : ∫ ω, min (We ω : ℝ) (M : ℝ) ∂P =
          p / (1 - p) * ∫ ω, fM M (W ω) ∂P := by
        rw [div_mul_eq_mul_div, eq_div_iff h1p_pos.ne']
        linarith
      rw [hEqDiv]
      exact mul_le_mul_of_nonneg_left hIntLe (div_nonneg hp0.le h1p_pos.le)
    rw [← ofReal_integral_eq_lintegral_ofReal hmin_int hmin_nn]
    exact ENNReal.ofReal_le_ofReal hRealLe
  have hSup : ∀ n : ℕ, (⨆ M : ℕ, ENNReal.ofReal (min (n : ℝ) (M : ℝ))) = ENNReal.ofReal (n : ℝ) :=
    fun n ↦ le_antisymm
      (iSup_le fun M ↦ ENNReal.ofReal_le_ofReal (min_le_left _ _))
      (le_trans (by rw [min_self])
        (le_iSup (fun M : ℕ ↦ ENNReal.ofReal (min (n : ℝ) (M : ℝ))) n))
  have hWe_lint : ∫⁻ ω, ENNReal.ofReal ‖(We ω : ℝ)‖ ∂P < ⊤ := by
    have hle : ∫⁻ ω, ENNReal.ofReal ‖(We ω : ℝ)‖ ∂P ≤
        ENNReal.ofReal (p / (1 - p) * ∫ ω, (W ω : ℝ) ^ 2 ∂P) := calc
      ∫⁻ ω, ENNReal.ofReal ‖(We ω : ℝ)‖ ∂P
        = ∫⁻ ω, (⨆ M : ℕ, ENNReal.ofReal (min (We ω : ℝ) (M : ℝ))) ∂P := by
          refine lintegral_congr fun ω ↦ ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (We ω)), ← hSup (We ω)]
      _ = ⨆ M : ℕ, ∫⁻ ω, ENNReal.ofReal (min (We ω : ℝ) (M : ℝ)) ∂P :=
          lintegral_iSup'
            (fun M ↦ ((Measurable.of_discrete :
              Measurable fun n : ℕ ↦ min (n : ℝ) (M : ℝ)).comp_aemeasurable hWe).ennreal_ofReal)
            (Eventually.of_forall fun _ _ _ h12 ↦
              ENNReal.ofReal_le_ofReal
                (le_min (min_le_left _ _) ((min_le_right _ _).trans (Nat.cast_le.mpr h12))))
      _ ≤ ENNReal.ofReal (p / (1 - p) * ∫ ω, (W ω : ℝ) ^ 2 ∂P) := iSup_le hBoundM
    exact hle.trans_lt ENNReal.ofReal_lt_top
  have hWe_int : Integrable (fun ω ↦ (We ω : ℝ)) P :=
    ⟨((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable
        hWe).aestronglyMeasurable,
      (hasFiniteIntegral_iff_norm _).mpr hWe_lint⟩
  simpa only [Real.norm_eq_abs] using (hWe_int.sub' hW_int).norm

/-- **Theorem 6.5** (`\label{thm177}`, `SteinIntro.tex:3312-3319`): for $0 < p \le 1$,
$N \sim \mathrm{Ge}^0(p)$, and an integer-valued random variable $W \ge 0$ with
$\mathbb{E}[W] = (1 - p)/p$ and $\mathbb{E}[W^2] < \infty$, if $W^e$ has the discrete equilibrium
distribution with respect to $W$ on the same probability space, then
$d_{\mathrm{TV}}(W, N) \le 2(1 - p)\mathbb{E}|W^e - W|$. -/
theorem tvDist_le_of_isDiscreteEquilibrium
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {W We : Ω → ℕ} {N : Ω' → ℕ}
    (_hW2 : MemLp (fun ω ↦ (W ω : ℝ)) 2 P)
    (hEq : IsDiscreteEquilibrium P p W P We)
    (hN_law : P'.map N = geomLaw p) :
    tvDist (P.map W) (P'.map N) ≤
      ENNReal.ofReal (2 * (1 - p)) * ∫⁻ ω, ENNReal.ofReal |(We ω : ℝ) - (W ω : ℝ)| ∂P := by
  rcases hEq with ⟨hp0, hp1, hW, hW_int, hW_mean, hWe, hStein⟩
  rcases eq_or_lt_of_le hp1 with rfl | hp_lt
  · have hmean0 : ∫ ω, (W ω : ℝ) ∂P = 0 := by simpa using hW_mean
    have hW0_ae : (fun ω ↦ (W ω : ℝ)) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω ↦ Nat.cast_nonneg (W ω)) hW_int).mp hmean0
    refine (tvDist_geomLaw_le P P' hp0 le_rfl hW hN_law).trans ?_
    refine iSup₂_le fun f ⟨hf0, _⟩ ↦ ?_
    have hzero_ae : (fun ω : Ω ↦ (1 - (1 : ℝ)) * fwdDiff 1 f (W ω) - 1 * f (W ω)) =ᵐ[P]
        fun _ ↦ (0 : ℝ) := by
      filter_upwards [hW0_ae] with ω hω
      have hWn : W ω = 0 := Nat.cast_eq_zero.mp hω
      simp [hWn, hf0]
    rw [integral_congr_ae hzero_ae, integral_const, smul_zero, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  · set M : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal |(We ω : ℝ) - (W ω : ℝ)| ∂P
    have h2_pos : 0 < 2 * (1 - p) := by linarith
    rcases eq_or_ne M ⊤ with hM_top | hM_ne_top
    · rw [hM_top, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h2_pos).ne']
      exact le_top
    have hD_nn : 0 ≤ᵐ[P] fun ω ↦ |(We ω : ℝ) - (W ω : ℝ)| :=
      Eventually.of_forall fun _ ↦ abs_nonneg _
    have hD_asm : AEStronglyMeasurable (fun ω ↦ |(We ω : ℝ) - (W ω : ℝ)|) P := by
      have hWe_asm : AEStronglyMeasurable (fun ω ↦ (We ω : ℝ)) P :=
        ((Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable
          hWe).aestronglyMeasurable
      exact (hWe_asm.sub hW_int.aestronglyMeasurable).norm
    have hD_int : Integrable (fun ω ↦ |(We ω : ℝ) - (W ω : ℝ)|) P :=
      ⟨hD_asm, (hasFiniteIntegral_iff_ofReal hD_nn).mpr hM_ne_top.lt_top⟩
    have hM_eq : M = ENNReal.ofReal (∫ ω, |(We ω : ℝ) - (W ω : ℝ)| ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hD_int hD_nn).symm
    refine (tvDist_geomLaw_le P P' hp0 hp_lt.le hW hN_law).trans ?_
    refine iSup₂_le fun f ⟨hf0, hf_bdd⟩ ↦ ?_
    have hfW_int : Integrable (fun ω ↦ f (W ω)) P :=
      integrable_comp_of_abs_fwdDiff_le hW hW_int ⟨1, hf_bdd⟩
    have hfwdW_int : Integrable (fun ω ↦ fwdDiff 1 f (W ω)) P :=
      integrable_fwdDiff_comp hW ⟨1, hf_bdd⟩
    have hfwdWe_int : Integrable (fun ω ↦ fwdDiff 1 f (We ω)) P :=
      integrable_fwdDiff_comp hWe ⟨1, hf_bdd⟩
    have hId := hStein f ⟨1, hf_bdd⟩
    rw [hf0, mul_zero, sub_zero] at hId
    have hRewrite : ∫ ω, ((1 - p) * fwdDiff 1 f (W ω) - p * f (W ω)) ∂P =
        (1 - p) * ∫ ω, (fwdDiff 1 f (W ω) - fwdDiff 1 f (We ω)) ∂P := by
      rw [integral_sub (hfwdW_int.const_mul (1 - p)) (hfW_int.const_mul p),
        integral_const_mul, integral_const_mul, hId, ← mul_sub,
        integral_sub hfwdW_int hfwdWe_int]
    have hDiff_abs_int : Integrable (fun ω ↦ |fwdDiff 1 f (W ω) - fwdDiff 1 f (We ω)|) P := by
      simpa only [Real.norm_eq_abs] using (hfwdW_int.sub' hfwdWe_int).norm
    have hRealBound : |∫ ω, ((1 - p) * fwdDiff 1 f (W ω) - p * f (W ω)) ∂P| ≤
        (2 * (1 - p)) * ∫ ω, |(We ω : ℝ) - (W ω : ℝ)| ∂P := by
      rw [hRewrite, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp_lt.le)]
      have h1 : |∫ ω, (fwdDiff 1 f (W ω) - fwdDiff 1 f (We ω)) ∂P| ≤
          ∫ ω, |fwdDiff 1 f (W ω) - fwdDiff 1 f (We ω)| ∂P := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun ω ↦ fwdDiff 1 f (W ω) - fwdDiff 1 f (We ω))
      have h2 : ∫ ω, |fwdDiff 1 f (W ω) - fwdDiff 1 f (We ω)| ∂P ≤
          ∫ ω, 2 * |(We ω : ℝ) - (W ω : ℝ)| ∂P :=
        integral_mono hDiff_abs_int (hD_int.const_mul 2) fun ω ↦
          abs_fwdDiff_sub_le_two_mul_abs hf_bdd (W ω) (We ω)
      rw [integral_const_mul] at h2
      have hmul := mul_le_mul_of_nonneg_left (h1.trans h2) (sub_nonneg.mpr hp_lt.le)
      linarith
    rw [hM_eq, ← ENNReal.ofReal_mul h2_pos.le]
    exact ENNReal.ofReal_le_ofReal hRealBound

end SteinMethod
