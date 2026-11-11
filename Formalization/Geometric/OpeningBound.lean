/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Geometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Section 6 Opening Bounds: Wasserstein Reduction, Counterexample, and Support Mismatch

Formalizes the opening motivation of Section 6 (`SteinIntro.tex:3193-3200`) of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`):

* **Support-mismatch total variation formula and limit** (`Sec6_supportMismatch`,
  `SteinIntro.tex:3199-3200`): for $X \sim \mathrm{Ge}(p)$ on $\{1, 2, \dots\}$ (`posGeomLaw p`,
  $0 < p \le 1$) and integer $k \ge 1$, if $W =^d kX$, then
  $$d_{\mathrm{TV}}(W, X) = 1 - \frac{p(1 - p)^{k - 1}}{1 - (1 - p)^k}
    \xrightarrow{p \to 0^+} \frac{k - 1}{k}$$
  (`tvDist_mul_posGeomLaw` and `tendsto_supportMismatch`).
* **Opening Wasserstein triangle-inequality display** (`SteinIntro.tex:3193-3198`; `ISSUE-6.0`):
  - `opening_wasserstein_of_ex5_4`: proves $|d_{\mathrm{W}}(pW, Z) - p\,d_{\mathrm{W}}(X, W)| \le p$
    (and finiteness of both Wasserstein distances) from Example 5.4's bound
    $d_{\mathrm{W}}(pX, Z) \le p$ via homogeneity
    $d_{\mathrm{W}}(pX, pW) = p\,d_{\mathrm{W}}(X, W)$ and the Wasserstein-1 triangle inequality.
  - `not_opening_wasserstein_printed`: machine-checked refutation of the printed unscaled inequality
    $|d_{\mathrm{W}}(pW, Z) - d_{\mathrm{W}}(X, W)| \le p$ using $p = 1/4$ and $W \equiv 4$.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SteinMethod

/-! ### Support Mismatch (`SteinIntro.tex:3199-3200`) -/

private lemma one_sub_pow_eq_mul_sum (x : ℝ) (k : ℕ) :
    1 - x ^ k = (1 - x) * ∑ i ∈ Finset.range k, x ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        1 - x ^ (k + 1) = (1 - x ^ k) + x ^ k * (1 - x) := by
          rw [pow_succ]
          ring
        _ = (1 - x) * ∑ i ∈ Finset.range (k + 1), x ^ i := by
          rw [ih, Finset.sum_range_succ]
          ring

/-- Exact total variation distance between $W =^d kX$ and $X \sim \mathrm{Ge}(p)$ on
$\{1, 2, \dots\}$ for $0 < p \le 1$ and $k \ge 1$ (`SteinIntro.tex:3199-3200`):
$$d_{\mathrm{TV}}(W, X) = 1 - \frac{p(1 - p)^{k - 1}}{1 - (1 - p)^k}.$$ -/
theorem tvDist_mul_posGeomLaw
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    {k : ℕ} (hk : 1 ≤ k)
    {W : Ω → ℕ} {X : Ω' → ℕ}
    (hX : AEMeasurable X P') (hX_law : P'.map X = posGeomLaw p)
    (hW_law : P.map W = P'.map (fun ω' ↦ k * X ω')) :
    tvDist (P.map W) (P'.map X) =
      ENNReal.ofReal (1 - p * (1 - p) ^ (k - 1) / (1 - (1 - p) ^ k)) := by
  have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  let μ₁ : Measure ℕ := (posGeomLaw p).map (fun m : ℕ ↦ k * m)
  let μ₂ : Measure ℕ := posGeomLaw p
  have _ : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance
  have hmapW : P.map W = μ₁ := by
    dsimp only [μ₁]
    rw [hW_law, ← hX_law]
    exact ((Measurable.of_discrete :
      Measurable fun m : ℕ ↦ k * m).aemeasurable.map_map_of_aemeasurable hX).symm
  rw [hmapW, hX_law]
  let g : ℕ → ℕ := fun j ↦ k * (j + 1)
  let A : Set ℕ := Set.range g
  have hg_inj : Function.Injective g := fun j₁ j₂ h ↦
    Nat.add_right_cancel (Nat.mul_left_cancel hk_pos h)
  have hμ₁_g : ∀ j : ℕ, μ₁ {g j} = ENNReal.ofReal ((1 - p) ^ j * p) := fun j ↦ by
    dsimp only [μ₁]
    rw [Measure.map_apply .of_discrete .of_discrete]
    have hpre : (fun m : ℕ ↦ k * m) ⁻¹' {g j} = {j + 1} := by
      ext m
      simp only [Set.mem_preimage, Set.mem_singleton_iff, g]
      exact ⟨fun h ↦ Nat.mul_left_cancel hk_pos h, fun h ↦ congrArg (k * ·) h⟩
    rw [hpre, posGeomLaw_singleton_of_pos hp0 hp1 (Nat.succ_le_succ (Nat.zero_le j))]
    simp
  have hμ₁_Ac : μ₁ Aᶜ = 0 := by
    dsimp only [μ₁]
    rw [Measure.map_apply .of_discrete .of_discrete]
    refine measure_mono_null (fun m hm ↦ ?_) (posGeomLaw_singleton_zero p)
    by_contra hm0
    have hm_ne : m ≠ 0 := hm0
    exact hm ⟨m - 1, by dsimp only [g]; rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm_ne)]⟩
  have hμ₂_le_μ₁_A : ∀ m ∈ A, μ₂ {m} ≤ μ₁ {m} := by
    rintro _ ⟨j, rfl⟩
    have hgj_ge : 1 ≤ g j := Nat.mul_pos hk_pos (Nat.succ_pos j)
    rw [hμ₁_g j, posGeomLaw_singleton_of_pos hp0 hp1 hgj_ge]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hp0.le)
    have hj_le : j ≤ g j - 1 := by
      have hmul : 1 * (j + 1) ≤ k * (j + 1) := Nat.mul_le_mul_right (j + 1) hk
      dsimp only [g]
      omega
    exact pow_le_pow_of_le_one (sub_nonneg.mpr hp1) (by linarith) hj_le
  have hS_le : ∀ S : Set ℕ, S ⊆ A → μ₂.real S ≤ μ₁.real S := fun S hSA ↦ by
    have henn : μ₂ S ≤ μ₁ S := by
      rw [← Measure.tsum_indicator_apply_singleton μ₂ S .of_discrete,
        ← Measure.tsum_indicator_apply_singleton μ₁ S .of_discrete]
      refine ENNReal.tsum_le_tsum fun m ↦ ?_
      by_cases hm : m ∈ S
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm]
        exact hμ₂_le_μ₁_A m (hSA hm)
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
    exact ENNReal.toReal_mono (measure_ne_top μ₁ S) henn
  have hsplit_real : ∀ (μ : Measure ℕ) [IsFiniteMeasure μ] (S T : Set ℕ),
      μ.real (S ∩ T) + μ.real (S \ T) = μ.real S := fun μ _ S T ↦ by
    have h := measure_inter_add_sdiff S (.of_discrete : MeasurableSet T) (μ := μ)
    rw [measureReal_def, measureReal_def, measureReal_def, ← h,
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  have hcompl_real : ∀ (μ : Measure ℕ) [IsProbabilityMeasure μ] (B : Set ℕ),
      μ.real B + μ.real Bᶜ = 1 := fun μ _ B ↦ by
    have h := measure_add_measure_compl (.of_discrete : MeasurableSet B) (μ := μ)
    rw [measure_univ] at h
    rw [measureReal_def, measureReal_def,
      ← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), h, ENNReal.toReal_one]
  have hμ₁_inter : ∀ B : Set ℕ, μ₁.real B = μ₁.real (A ∩ B) := fun B ↦ by
    have hdiff0 : μ₁.real (B \ A) = 0 := by
      have h0 : μ₁ (B \ A) = 0 := measure_mono_null (fun _ hx ↦ hx.2) hμ₁_Ac
      rw [measureReal_def, h0, ENNReal.toReal_zero]
    have hsp := hsplit_real μ₁ B A
    rw [hdiff0, add_zero, Set.inter_comm] at hsp
    exact hsp.symm
  have hμ₁_A : μ₁.real A = 1 := by
    have hu := hμ₁_inter Set.univ
    rw [probReal_univ, Set.inter_univ] at hu
    exact hu.symm
  have hone_side : ∀ B : Set ℕ, μ₁.real B - μ₂.real B ≤ 1 - μ₂.real A := fun B ↦ by
    have h1 := hsplit_real μ₁ A B
    have h2 := hsplit_real μ₂ A B
    have hle1 : μ₂.real (A ∩ B) ≤ μ₂.real B :=
      ENNReal.toReal_mono (measure_ne_top μ₂ B) (measure_mono Set.inter_subset_right)
    have hle2 : μ₂.real (A \ B) ≤ μ₁.real (A \ B) := hS_le (A \ B) (fun _ hx ↦ hx.1)
    linarith [hμ₁_inter B, hμ₁_A]
  have habs_le : ∀ B : Set ℕ, |μ₁.real B - μ₂.real B| ≤ 1 - μ₂.real A := fun B ↦ by
    refine abs_sub_le_iff.mpr ⟨hone_side B, ?_⟩
    have hc1 := hcompl_real μ₁ B
    have hc2 := hcompl_real μ₂ B
    linarith [hone_side Bᶜ]
  have htv_A : tvDist μ₁ μ₂ = ENNReal.ofReal (1 - μ₂.real A) := by
    rw [tvDist_eq_iSup]
    refine le_antisymm (iSup₂_le fun B _ ↦ ENNReal.ofReal_le_ofReal (habs_le B)) ?_
    have hleA : μ₂.real A ≤ 1 := by
      have h := hS_le A subset_rfl
      rwa [hμ₁_A] at h
    have hA_eq : 1 - μ₂.real A = |μ₁.real A - μ₂.real A| := by
      rw [hμ₁_A, abs_of_nonneg (sub_nonneg.mpr hleA)]
    rw [hA_eq]
    exact le_iSup₂_of_le A .of_discrete le_rfl
  have hμ₂_A : μ₂.real A = p * (1 - p) ^ (k - 1) / (1 - (1 - p) ^ k) := by
    have hunion : A = ⋃ j : ℕ, ({g j} : Set ℕ) := by
      ext m
      simp [A]
    have hdisj : Pairwise fun j₁ j₂ : ℕ ↦ Disjoint ({g j₁} : Set ℕ) {g j₂} :=
      fun j₁ j₂ hne ↦ Set.disjoint_singleton.mpr (hg_inj.ne hne)
    have henn : μ₂ A = ∑' j : ℕ, μ₂ {g j} := by
      rw [hunion, measure_iUnion hdisj fun _ ↦ .of_discrete]
    have hreal : μ₂.real A = ∑' j : ℕ, μ₂.real {g j} := by
      rw [measureReal_def, henn, ENNReal.tsum_toReal_eq fun j ↦ measure_ne_top μ₂ {g j}]
      rfl
    have hterm : ∀ j : ℕ,
        μ₂.real {g j} = (p * (1 - p) ^ (k - 1)) * ((1 - p) ^ k) ^ j := fun j ↦ by
      have hgj_ge : 1 ≤ g j := Nat.mul_pos hk_pos (Nat.succ_pos j)
      rw [posGeomLaw_real_singleton_of_pos hp0 hp1 hgj_ge]
      have hexp : g j - 1 = (k - 1) + k * j := by
        dsimp only [g]
        rw [Nat.mul_succ]
        omega
      rw [hexp, pow_add, pow_mul]
      ring
    have hnorm : ‖(1 - p) ^ k‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hp1) k)]
      exact pow_lt_one₀ (sub_nonneg.mpr hp1) (by linarith) hk_pos.ne'
    rw [hreal]
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm, div_eq_mul_inv]
  rw [htv_A, hμ₂_A]

/-- As $p \to 0^+$ ($\mathbb{E}[X] = 1/p \to \infty$), the support-mismatch total variation distance
$1 - \frac{p(1 - p)^{k - 1}}{1 - (1 - p)^k}$ converges to $\frac{k - 1}{k}$ for every integer
$k \ge 1$ (`SteinIntro.tex:3199-3200`). -/
theorem tendsto_supportMismatch {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun p : ℝ ↦ 1 - p * (1 - p) ^ (k - 1) / (1 - (1 - p) ^ k))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (((k : ℝ) - 1) / (k : ℝ))) := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hk).ne'
  let g : ℝ → ℝ := fun p ↦ 1 - (1 - p) ^ (k - 1) / ∑ i ∈ Finset.range k, (1 - p) ^ i
  have hg_cont : ContinuousAt g 0 := by
    have hnum : ContinuousAt (fun p : ℝ ↦ (1 - p) ^ (k - 1)) 0 :=
      ((continuous_const.sub continuous_id).pow (k - 1)).continuousAt
    have hden : ContinuousAt (fun p : ℝ ↦ ∑ i ∈ Finset.range k, (1 - p) ^ i) 0 :=
      (continuous_finsetSum _ fun i _ ↦ (continuous_const.sub continuous_id).pow i).continuousAt
    have hden0 : (∑ i ∈ Finset.range k, (1 - (0 : ℝ)) ^ i) ≠ 0 := by
      simpa using hk_ne
    exact continuousAt_const.sub (hnum.div hden hden0)
  have hg0 : g 0 = ((k : ℝ) - 1) / (k : ℝ) := by
    dsimp only [g]
    simp only [sub_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    field_simp [hk_ne]
  have hlim : Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (((k : ℝ) - 1) / (k : ℝ))) :=
    hg0 ▸ tendsto_nhdsWithin_of_tendsto_nhds hg_cont.tendsto
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p (hp : 0 < p)
  dsimp only [g]
  rw [one_sub_pow_eq_mul_sum (1 - p) k, show 1 - (1 - p) = p by ring,
    mul_div_mul_left _ _ hp.ne']

/-! ### Exponential Moment, Wasserstein-1 Helpers, Reduction, and Counterexample (`ISSUE-6.0`) -/

private lemma abs_sub_le_of_lipschitzWith_one {h : ℝ → ℝ} (hh : LipschitzWith 1 h)
    (x y : ℝ) : |h x - h y| ≤ |x - y| := by
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hh.dist_le_mul x y

private lemma wassersteinDist_symm (μ ν : Measure ℝ) :
    wassersteinDist μ ν = wassersteinDist ν μ :=
  ipm_symm _ μ ν

private lemma integrable_of_lipschitzWith_one {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hid : Integrable (fun x : ℝ ↦ x) μ) {h : ℝ → ℝ} (hh : LipschitzWith 1 h) :
    Integrable h μ := by
  refine (hid.abs.add (integrable_const |h 0|)).mono' hh.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  calc
    |h x| = |(h x - h 0) + h 0| := by ring_nf
    _ ≤ |h x - h 0| + |h 0| := abs_add_le _ _
    _ ≤ |x - 0| + |h 0| := add_le_add (abs_sub_le_of_lipschitzWith_one hh x 0) le_rfl
    _ = |x| + |h 0| := by simp

private lemma wassersteinDist_lt_top_of_integrable {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun x : ℝ ↦ x) μ) (hν : Integrable (fun x : ℝ ↦ x) ν) :
    wassersteinDist μ ν < ⊤ := by
  have hle : wassersteinDist μ ν ≤
      ENNReal.ofReal ((∫ x, |x| ∂μ) + ∫ x, |x| ∂ν) := by
    refine ipm_le fun h hh hμ_h hν_h ↦ ENNReal.ofReal_le_ofReal ?_
    have hshift : (∫ x, h x ∂μ) - (∫ x, h x ∂ν) =
        (∫ x, (h x - h 0) ∂μ) - ∫ x, (h x - h 0) ∂ν := by
      rw [integral_sub hμ_h (integrable_const (h 0)),
        integral_sub hν_h (integrable_const (h 0)), integral_const, integral_const,
        probReal_univ, probReal_univ, one_smul]
      ring
    have hb_μ : |∫ x, (h x - h 0) ∂μ| ≤ ∫ x, |x| ∂μ := by
      calc
        |∫ x, (h x - h 0) ∂μ| ≤ ∫ x, |h x - h 0| ∂μ := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun x : ℝ ↦ h x - h 0)
        _ ≤ ∫ x, |x| ∂μ :=
          integral_mono (hμ_h.sub (integrable_const (h 0))).abs hμ.abs fun x ↦ by
            simpa using abs_sub_le_of_lipschitzWith_one hh x 0
    have hb_ν : |∫ x, (h x - h 0) ∂ν| ≤ ∫ x, |x| ∂ν := by
      calc
        |∫ x, (h x - h 0) ∂ν| ≤ ∫ x, |h x - h 0| ∂ν := by
          simpa only [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (fun x : ℝ ↦ h x - h 0)
        _ ≤ ∫ x, |x| ∂ν :=
          integral_mono (hν_h.sub (integrable_const (h 0))).abs hν.abs fun x ↦ by
            simpa using abs_sub_le_of_lipschitzWith_one hh x 0
    rw [hshift]
    exact (abs_sub _ _).trans (add_le_add hb_μ hb_ν)
  exact hle.trans_lt ENNReal.ofReal_lt_top

private lemma wassersteinDist_triangle {μ ν ρ : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : ℝ ↦ x) ν) :
    wassersteinDist μ ρ ≤ wassersteinDist μ ν + wassersteinDist ν ρ := by
  refine ipm_le fun h hh hμ hρ ↦ ?_
  have hν_h : Integrable h ν := integrable_of_lipschitzWith_one hν hh
  have htri : |(∫ x, h x ∂μ) - (∫ x, h x ∂ρ)| ≤
      |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| + |(∫ x, h x ∂ν) - (∫ x, h x ∂ρ)| := by
    calc
      |(∫ x, h x ∂μ) - (∫ x, h x ∂ρ)|
        = |((∫ x, h x ∂μ) - (∫ x, h x ∂ν)) + ((∫ x, h x ∂ν) - (∫ x, h x ∂ρ))| := by ring_nf
      _ ≤ |(∫ x, h x ∂μ) - (∫ x, h x ∂ν)| + |(∫ x, h x ∂ν) - (∫ x, h x ∂ρ)| := abs_add_le _ _
  refine (ENNReal.ofReal_le_ofReal htri).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact add_le_add (le_ipm hh hμ hν_h) (le_ipm hh hν_h hρ)

private lemma wassersteinDist_map_const_mul_le {μ ν : Measure ℝ} {c : ℝ} (hc : 0 < c) :
    wassersteinDist (μ.map (fun x : ℝ ↦ c * x)) (ν.map (fun x : ℝ ↦ c * x)) ≤
      ENNReal.ofReal c * wassersteinDist μ ν := by
  refine ipm_le fun h hh hμ hν ↦ ?_
  let g : ℝ → ℝ := fun x ↦ c⁻¹ * h (c * x)
  have hg_lip : LipschitzWith 1 g :=
    LipschitzWith.mk_one fun x y ↦ by
      dsimp only [g]
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hc)]
      calc
        c⁻¹ * |h (c * x) - h (c * y)|
          ≤ c⁻¹ * |c * x - c * y| :=
            mul_le_mul_of_nonneg_left (abs_sub_le_of_lipschitzWith_one hh _ _)
              (inv_nonneg.mpr hc.le)
        _ = |x - y| := by
            rw [← mul_sub, abs_mul, abs_of_pos hc, inv_mul_cancel_left₀ hc.ne']
  have hg_μ : Integrable g μ :=
    ((integrable_map_measure hh.continuous.aestronglyMeasurable
      (measurable_const_mul c).aemeasurable).mp hμ).const_mul c⁻¹
  have hg_ν : Integrable g ν :=
    ((integrable_map_measure hh.continuous.aestronglyMeasurable
      (measurable_const_mul c).aemeasurable).mp hν).const_mul c⁻¹
  have hint_μ : ∫ y, h y ∂(μ.map (fun x : ℝ ↦ c * x)) = c * ∫ x, g x ∂μ := by
    rw [integral_map (measurable_const_mul c).aemeasurable hh.continuous.aestronglyMeasurable,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only [g]
    rw [mul_inv_cancel_left₀ hc.ne']
  have hint_ν : ∫ y, h y ∂(ν.map (fun x : ℝ ↦ c * x)) = c * ∫ x, g x ∂ν := by
    rw [integral_map (measurable_const_mul c).aemeasurable hh.continuous.aestronglyMeasurable,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    dsimp only [g]
    rw [mul_inv_cancel_left₀ hc.ne']
  rw [hint_μ, hint_ν, ← mul_sub, abs_mul, abs_of_pos hc, ENNReal.ofReal_mul hc.le]
  exact mul_le_mul_of_nonneg_left (le_ipm hg_lip hg_μ hg_ν) zero_le

private lemma wassersteinDist_map_const_mul {μ ν : Measure ℝ} {p : ℝ} (hp : 0 < p) :
    wassersteinDist (μ.map (fun x : ℝ ↦ p * x)) (ν.map (fun x : ℝ ↦ p * x)) =
      ENNReal.ofReal p * wassersteinDist μ ν := by
  refine le_antisymm (wassersteinDist_map_const_mul_le hp) ?_
  have hinv := wassersteinDist_map_const_mul_le (μ := μ.map (fun x : ℝ ↦ p * x))
    (ν := ν.map (fun x : ℝ ↦ p * x)) (inv_pos.mpr hp)
  have hmap : ∀ ρ : Measure ℝ,
      (ρ.map (fun x : ℝ ↦ p * x)).map (fun x : ℝ ↦ p⁻¹ * x) = ρ := fun ρ ↦ by
    rw [Measure.map_map (measurable_const_mul p⁻¹) (measurable_const_mul p)]
    have hcomp : ((fun x : ℝ ↦ p⁻¹ * x) ∘ fun x : ℝ ↦ p * x) = id :=
      funext fun x ↦ inv_mul_cancel_left₀ hp.ne' x
    rw [hcomp, Measure.map_id]
  rw [hmap μ, hmap ν] at hinv
  calc
    ENNReal.ofReal p * wassersteinDist μ ν
      ≤ ENNReal.ofReal p *
          (ENNReal.ofReal p⁻¹ *
            wassersteinDist (μ.map (fun x : ℝ ↦ p * x)) (ν.map (fun x : ℝ ↦ p * x))) :=
        mul_le_mul_of_nonneg_left hinv zero_le
    _ = wassersteinDist (μ.map (fun x : ℝ ↦ p * x)) (ν.map (fun x : ℝ ↦ p * x)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one,
          one_mul]

private lemma lintegral_abs_expMeasure_one :
    ∫⁻ x : ℝ, ENNReal.ofReal |x| ∂ProbabilityTheory.expMeasure 1 = 1 := by
  change ∫⁻ x : ℝ, ENNReal.ofReal |x| ∂volume.withDensity (ProbabilityTheory.gammaPDF 1 1) = 1
  have hmeas_pdf : Measurable (ProbabilityTheory.gammaPDF 1 1) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul volume hmeas_pdf
    continuous_abs.measurable.ennreal_ofReal]
  have hcongr : (ProbabilityTheory.gammaPDF 1 1 * fun x : ℝ ↦ ENNReal.ofReal |x|) =
      ProbabilityTheory.gammaPDF 2 1 := by
    ext x
    simp only [Pi.mul_apply, ProbabilityTheory.gammaPDF_eq]
    by_cases hx : 0 ≤ x
    · have hG2 : Real.Gamma 2 = 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
          one_mul]
      simp only [ite_eq_left hx, abs_of_nonneg hx, Real.one_rpow, Real.Gamma_one, div_one,
        sub_self, Real.rpow_zero, mul_one, hG2, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
        one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]
    · simp only [ite_eq_right hx, ENNReal.ofReal_zero, zero_mul]
  rw [hcongr]
  exact ProbabilityTheory.lintegral_gammaPDF_eq_one zero_lt_two zero_lt_one

private lemma integrable_id_expMeasure_one :
    Integrable (fun x : ℝ ↦ x) (ProbabilityTheory.expMeasure 1) := by
  refine ⟨measurable_id.aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
  simpa only [Real.norm_eq_abs, lintegral_abs_expMeasure_one] using ENNReal.one_lt_top

private lemma integral_abs_expMeasure_one :
    ∫ x : ℝ, |x| ∂ProbabilityTheory.expMeasure 1 = 1 := by
  have _ : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
  have hnn : 0 ≤ᵐ[ProbabilityTheory.expMeasure 1] fun x : ℝ ↦ |x| :=
    Eventually.of_forall abs_nonneg
  have h := ofReal_integral_eq_lintegral_ofReal integrable_id_expMeasure_one.abs hnn
  rw [lintegral_abs_expMeasure_one, ← ENNReal.ofReal_one] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg abs_nonneg) zero_le_one).mp h

/-- **Section 6 opening Wasserstein triangle-inequality reduction** (`SteinIntro.tex:3193-3198`;
`ISSUE-6.0`): given Example 5.4's bound $d_{\mathrm{W}}(pX, Z) \le p$ for $X \sim \mathrm{Ge}(p)$ on
$\{1, 2, \dots\}$ and $Z \sim \mathrm{Exp}(1)$, any integrable $W : \Omega \to \mathbb{N}$
satisfies $d_{\mathrm{W}}(pW, Z) < \infty$, $d_{\mathrm{W}}(X, W) < \infty$, and
$|d_{\mathrm{W}}(pW, Z) - p\,d_{\mathrm{W}}(X, W)| \le p$. -/
theorem opening_wasserstein_of_ex5_4
    {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    {p : ℝ} {W : Ω → ℕ} {X : Ω' → ℕ} {Z : Ω'' → ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hW : AEMeasurable W P) (_hW_pos : ∀ᵐ ω ∂P, 0 < W ω)
    (hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P)
    (_hW_mean : ∫ ω, (W ω : ℝ) ∂P = 1 / p)
    (hX : AEMeasurable X P') (hX_law : P'.map X = posGeomLaw p)
    (_hZ : AEMeasurable Z P'') (hZ_law : P''.map Z = ProbabilityTheory.expMeasure 1)
    (hEx5_4 : wassersteinDist ((posGeomLaw p).map (fun k : ℕ ↦ p * (k : ℝ)))
      (ProbabilityTheory.expMeasure 1) ≤ ENNReal.ofReal p) :
    wassersteinDist (P.map (fun ω ↦ p * (W ω : ℝ))) (P''.map Z) < ⊤ ∧
      wassersteinDist (P'.map (fun ω' ↦ (X ω' : ℝ))) (P.map (fun ω ↦ (W ω : ℝ))) < ⊤ ∧
      |(wassersteinDist (P.map (fun ω ↦ p * (W ω : ℝ))) (P''.map Z)).toReal -
          p * (wassersteinDist (P'.map (fun ω' ↦ (X ω' : ℝ)))
            (P.map (fun ω ↦ (W ω : ℝ)))).toReal| ≤ p := by
  let μW : Measure ℝ := P.map (fun ω ↦ (W ω : ℝ))
  let μX : Measure ℝ := P'.map (fun ω' ↦ (X ω' : ℝ))
  let μpW : Measure ℝ := P.map (fun ω ↦ p * (W ω : ℝ))
  let μpX : Measure ℝ := (posGeomLaw p).map (fun k : ℕ ↦ p * (k : ℝ))
  let μZ : Measure ℝ := ProbabilityTheory.expMeasure 1
  have hWR : AEMeasurable (fun ω ↦ (W ω : ℝ)) P :=
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hW
  have hXR : AEMeasurable (fun ω' ↦ (X ω' : ℝ)) P' :=
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hX
  have _ : IsProbabilityMeasure μW := (Measure.isProbabilityMeasure_map_iff hWR).mpr inferInstance
  have _ : IsProbabilityMeasure μX := (Measure.isProbabilityMeasure_map_iff hXR).mpr inferInstance
  have _ : IsProbabilityMeasure μpW :=
    (Measure.isProbabilityMeasure_map_iff ((measurable_const_mul p).comp_aemeasurable hWR)).mpr
      inferInstance
  have _ : IsProbabilityMeasure μpX :=
    (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance
  have _ : IsProbabilityMeasure μZ := ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
  have hμX_eq : μX = (posGeomLaw p).map (Nat.cast : ℕ → ℝ) := by
    dsimp only [μX]
    rw [← hX_law]
    exact ((Measurable.of_discrete :
      Measurable (Nat.cast : ℕ → ℝ)).aemeasurable.map_map_of_aemeasurable hX).symm
  have hμpW_eq : μpW = μW.map (fun x : ℝ ↦ p * x) := by
    dsimp only [μpW, μW]
    exact ((measurable_const_mul p).aemeasurable.map_map_of_aemeasurable hWR).symm
  have hμpX_eq : μpX = μX.map (fun x : ℝ ↦ p * x) := by
    rw [hμX_eq, Measure.map_map (measurable_const_mul p) .of_discrete]
    rfl
  have hid_μW : Integrable (fun x : ℝ ↦ x) μW :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hWR).mpr hW_int
  have hid_μX : Integrable (fun x : ℝ ↦ x) μX := by
    rw [hμX_eq]
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      Measurable.of_discrete.aemeasurable).mpr (integrable_natCast_posGeomLaw hp0 hp1)
  have hid_μpW : Integrable (fun x : ℝ ↦ x) μpW :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      ((measurable_const_mul p).comp_aemeasurable hWR)).mpr (hW_int.const_mul p)
  have hid_μpX : Integrable (fun x : ℝ ↦ x) μpX :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      Measurable.of_discrete.aemeasurable).mpr ((integrable_natCast_posGeomLaw hp0 hp1).const_mul p)
  have hd₁_lt : wassersteinDist μpW μZ < ⊤ :=
    wassersteinDist_lt_top_of_integrable hid_μpW integrable_id_expMeasure_one
  have hd₂_lt : wassersteinDist μX μW < ⊤ :=
    wassersteinDist_lt_top_of_integrable hid_μX hid_μW
  have hscale : wassersteinDist μpX μpW = ENNReal.ofReal p * wassersteinDist μX μW := by
    rw [hμpX_eq, hμpW_eq, wassersteinDist_map_const_mul hp0]
  have htri1 : wassersteinDist μpW μZ ≤
      ENNReal.ofReal p * wassersteinDist μX μW + ENNReal.ofReal p := by
    calc
      wassersteinDist μpW μZ
        ≤ wassersteinDist μpW μpX + wassersteinDist μpX μZ := wassersteinDist_triangle hid_μpX
      _ = ENNReal.ofReal p * wassersteinDist μX μW + wassersteinDist μpX μZ := by
          rw [wassersteinDist_symm μpW μpX, hscale]
      _ ≤ ENNReal.ofReal p * wassersteinDist μX μW + ENNReal.ofReal p :=
          add_le_add le_rfl hEx5_4
  have htri2 : ENNReal.ofReal p * wassersteinDist μX μW ≤
      wassersteinDist μpW μZ + ENNReal.ofReal p := by
    calc
      ENNReal.ofReal p * wassersteinDist μX μW
        = wassersteinDist μpX μpW := hscale.symm
      _ ≤ wassersteinDist μpX μZ + wassersteinDist μZ μpW :=
          wassersteinDist_triangle integrable_id_expMeasure_one
      _ = wassersteinDist μpW μZ + wassersteinDist μpX μZ := by
          rw [wassersteinDist_symm μZ μpW, add_comm]
      _ ≤ wassersteinDist μpW μZ + ENNReal.ofReal p := add_le_add le_rfl hEx5_4
  have hp_mul_ne_top : ENNReal.ofReal p * wassersteinDist μX μW ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd₂_lt.ne
  have hreal1 : (wassersteinDist μpW μZ).toReal ≤
      p * (wassersteinDist μX μW).toReal + p := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hp_mul_ne_top, ENNReal.ofReal_ne_top⟩)
      htri1
    rwa [ENNReal.toReal_add hp_mul_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hp0.le] at h
  have hreal2 : p * (wassersteinDist μX μW).toReal ≤
      (wassersteinDist μpW μZ).toReal + p := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hd₁_lt.ne, ENNReal.ofReal_ne_top⟩)
      htri2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_add hd₁_lt.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le] at h
  rw [hZ_law]
  exact ⟨hd₁_lt, hd₂_lt, abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- **Refutation of the printed Section 6 opening Wasserstein display** (`SteinIntro.tex:3193-3198`;
`ISSUE-6.0`): the printed inequality $|d_{\mathrm{W}}(pW, Z) - d_{\mathrm{W}}(X, W)| \le p$ fails at
$p = 1/4$ and $W \equiv 4$ (where $d_{\mathrm{W}}(pW, Z) \le 2$ while
$d_{\mathrm{W}}(X, W) \ge \frac{81}{32}$, so
$|d_{\mathrm{W}}(pW, Z) - d_{\mathrm{W}}(X, W)| \ge \frac{17}{32} > \frac{1}{4}$). -/
theorem not_opening_wasserstein_printed :
    ¬ (∀ {Ω Ω' Ω'' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      (P'' : Measure Ω'') [IsProbabilityMeasure P'']
      {p : ℝ} {W : Ω → ℕ} {X : Ω' → ℕ} {Z : Ω'' → ℝ},
      0 < p →
      p ≤ 1 →
      AEMeasurable W P →
      (∀ᵐ ω ∂P, 0 < W ω) →
      Integrable (fun ω ↦ (W ω : ℝ)) P →
      ∫ ω, (W ω : ℝ) ∂P = 1 / p →
      AEMeasurable X P' →
      P'.map X = posGeomLaw p →
      AEMeasurable Z P'' →
      P''.map Z = ProbabilityTheory.expMeasure 1 →
      |(wassersteinDist (P.map (fun ω ↦ p * (W ω : ℝ))) (P''.map Z)).toReal -
          (wassersteinDist (P'.map (fun ω' ↦ (X ω' : ℝ)))
            (P.map (fun ω ↦ (W ω : ℝ)))).toReal| ≤ p) := by
  intro H
  let P : Measure Unit := Measure.dirac ()
  let P' : Measure ℕ := posGeomLaw (1 / 4)
  let P'' : Measure ℝ := ProbabilityTheory.expMeasure 1
  have _ : IsProbabilityMeasure P'' := ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one
  let W : Unit → ℕ := fun _ ↦ 4
  have hp0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hp1 : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hW_pos : ∀ᵐ ω ∂P, 0 < W ω := Eventually.of_forall fun _ ↦ by decide
  have hW_int : Integrable (fun ω ↦ (W ω : ℝ)) P := integrable_const (4 : ℝ)
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = 1 / (1 / 4 : ℝ) := by
    dsimp only [P, W]
    rw [integral_dirac]
    norm_num
  have hbound := H P P' P'' (W := W) (X := id) (Z := id) hp0 hp1
    Measurable.of_discrete.aemeasurable hW_pos hW_int hW_mean
    measurable_id.aemeasurable Measure.map_id measurable_id.aemeasurable Measure.map_id
  have hmap_pW : P.map (fun ω ↦ (1 / 4 : ℝ) * (W ω : ℝ)) = Measure.dirac (1 : ℝ) := by
    dsimp only [P, W]
    rw [Measure.map_dirac' measurable_const ()]
    norm_num
  have hmap_W : P.map (fun ω ↦ (W ω : ℝ)) = Measure.dirac (4 : ℝ) := by
    dsimp only [P, W]
    exact Measure.map_dirac' (f := fun _ : Unit ↦ (4 : ℝ)) measurable_const ()
  rw [hmap_pW, hmap_W, Measure.map_id] at hbound
  -- Upper bound: `d_W(δ_1, Exp(1)) ≤ 2`
  have hd₁_le : wassersteinDist (Measure.dirac (1 : ℝ)) P'' ≤ ENNReal.ofReal 2 := by
    refine ipm_le fun h hh _ hP''_h ↦ ENNReal.ofReal_le_ofReal ?_
    rw [integral_dirac]
    have hdiff : h 1 - ∫ x, h x ∂P'' = ∫ x, (h 1 - h x) ∂P'' := by
      rw [integral_sub (integrable_const (h 1)) hP''_h, integral_const, probReal_univ, one_smul]
    rw [hdiff]
    calc
      |∫ x, (h 1 - h x) ∂P''| ≤ ∫ x, |h 1 - h x| ∂P'' := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x : ℝ ↦ h 1 - h x)
      _ ≤ ∫ x, (|x| + 1) ∂P'' := by
        refine integral_mono ((integrable_const (h 1)).sub hP''_h).abs
          (integrable_id_expMeasure_one.abs.add (integrable_const 1)) fun x ↦ ?_
        calc
          |h 1 - h x| ≤ |1 - x| := abs_sub_le_of_lipschitzWith_one hh 1 x
          _ = |x - 1| := abs_sub_comm 1 x
          _ = |x + (-1)| := by ring_nf
          _ ≤ |x| + |-1| := abs_add_le x (-1)
          _ = |x| + 1 := by norm_num
      _ = 2 := by
        rw [integral_add integrable_id_expMeasure_one.abs (integrable_const 1),
          integral_abs_expMeasure_one, integral_const, probReal_univ, one_smul]
        norm_num
  have hd₁_real : (wassersteinDist (Measure.dirac (1 : ℝ)) P'').toReal ≤ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd₁_le
    rwa [ENNReal.toReal_ofReal zero_le_two] at h
  -- Lower bound: `d_W(Ge(1/4), δ_4) ≥ 81/32` via `h₄(x) = |x - 4|`
  let μX : Measure ℝ := P'.map (fun k : ℕ ↦ (k : ℝ))
  have _ : IsProbabilityMeasure μX :=
    (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance
  have hid_μX : Integrable (fun x : ℝ ↦ x) μX :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      Measurable.of_discrete.aemeasurable).mpr (integrable_natCast_posGeomLaw hp0 hp1)
  have hd₂_lt : wassersteinDist μX (Measure.dirac (4 : ℝ)) < ⊤ :=
    wassersteinDist_lt_top_of_integrable hid_μX (integrable_dirac (by simp))
  let h₄ : ℝ → ℝ := fun x ↦ dist x 4
  have hh₄_lip : LipschitzWith 1 h₄ := LipschitzWith.dist_left 4
  have hh₄_int_μX : Integrable h₄ μX := integrable_of_lipschitzWith_one hid_μX hh₄_lip
  have hh₄_int_dir : Integrable h₄ (Measure.dirac (4 : ℝ)) :=
    integrable_of_lipschitzWith_one (integrable_dirac (by simp)) hh₄_lip
  have hint_h₄ : ∫ x, h₄ x ∂μX = 81 / 32 := by
    rw [integral_map Measurable.of_discrete.aemeasurable hh₄_lip.continuous.aestronglyMeasurable]
    have hdecomp : (fun k : ℕ ↦ h₄ (k : ℝ)) =
        fun k : ℕ ↦ ((k : ℝ) - 4) + 2 * max 0 (4 - (k : ℝ)) := by
      ext k
      dsimp only [h₄]
      rw [Real.dist_eq]
      rcases le_total (k : ℝ) 4 with hle | hge
      · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
        ring
      · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
        ring
    let r : ℕ → ℝ := fun k ↦ max 0 (4 - (k : ℝ))
    have hr_bdd : Integrable r P' := by
      refine (integrable_const (4 : ℝ)).mono' Measurable.of_discrete.aestronglyMeasurable
        (Eventually.of_forall fun k ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
      exact max_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hr_int : ∫ k, r k ∂P' = 81 / 64 := by
      rw [integral_countable hr_bdd, tsum_eq_sum (s := Finset.range 4) fun k hk ↦ by
        have hge4 : 4 ≤ k := by simpa [Finset.mem_range] using hk
        have hle0 : 4 - (k : ℝ) ≤ 0 := by
          have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge4
          linarith
        simp [r, max_eq_left hle0]]
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        smul_eq_mul, r]
      have h0 : P'.real {0} = 0 := posGeomLaw_real_singleton_zero (1 / 4)
      have h1 : P'.real {1} = (1 - (1 / 4 : ℝ)) ^ 0 * (1 / 4) :=
        posGeomLaw_real_singleton_of_pos hp0 hp1 (by decide)
      have h2 : P'.real {2} = (1 - (1 / 4 : ℝ)) ^ 1 * (1 / 4) :=
        posGeomLaw_real_singleton_of_pos hp0 hp1 (by decide)
      have h3 : P'.real {3} = (1 - (1 / 4 : ℝ)) ^ 2 * (1 / 4) :=
        posGeomLaw_real_singleton_of_pos hp0 hp1 (by decide)
      rw [h0, h1, h2, h3]
      norm_num
    rw [hdecomp, integral_add ((integrable_natCast_posGeomLaw hp0 hp1).sub' (integrable_const 4))
      (hr_bdd.const_mul 2),
      integral_sub (integrable_natCast_posGeomLaw hp0 hp1) (integrable_const 4),
      integral_natCast_posGeomLaw hp0 hp1, integral_const, probReal_univ, one_smul,
      integral_const_mul, hr_int]
    norm_num
  have hd₂_ge : ENNReal.ofReal (81 / 32) ≤ wassersteinDist μX (Measure.dirac (4 : ℝ)) := by
    have h := le_ipm (H := {h : ℝ → ℝ | LipschitzWith 1 h}) hh₄_lip hh₄_int_μX hh₄_int_dir
    have hh₄_4 : h₄ 4 = 0 := dist_self 4
    rw [hint_h₄, integral_dirac, hh₄_4, sub_zero,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 81 / 32)] at h
    exact h
  have hd₂_real : (81 / 32 : ℝ) ≤ (wassersteinDist μX (Measure.dirac (4 : ℝ))).toReal := by
    have h := ENNReal.toReal_mono hd₂_lt.ne hd₂_ge
    rwa [ENNReal.toReal_ofReal (by norm_num)] at h
  have hdiff_ge :
      (wassersteinDist μX (Measure.dirac (4 : ℝ))).toReal -
        (wassersteinDist (Measure.dirac (1 : ℝ)) P'').toReal ≤ 1 / 4 :=
    (abs_sub_le_iff.mp hbound).2
  linarith

end SteinMethod
