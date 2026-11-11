/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.MillRatio
import Formalization.RandomGraph.TrianglesRucinskiMoments

/-!
# Necessity Direction for Ruciński's Triangle CLT Criterion (`TrianglesRucinskiNecessity`)

Proves from scratch that pointwise CDF convergence of the standardized triangle count
$W_n = (T_n - \mu_n)/\sigma_n$ in $G(n, p_n)$ ($0 \le p_n \le 1$) to $\Phi = \text{stdNormalCDF}$
implies $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$ (`SteinIntro.tex:943-944`,
`\cite{ruc88}`):

1. `tendsto_sigma_atTop_of_tendsto_triangles_cdf`: bounded $\sigma_n$ along a subsequence forces a
   lattice gap of width $1 / \sigma_n$, preventing two adjacent intervals $(0, \delta]$ and
   $(\delta, 2\delta]$ from both having positive mass.
2. `tendsto_mul_p_atTop_of_tendsto_triangles_cdf`: $\sigma_n^2 \le (n p_n)^3 + 3 (n p_n)^5$, so
   $\sigma_n \to \infty$ forces $n p_n \to \infty$.
3. `tendsto_sq_mul_one_sub_p_atTop_of_tendsto_triangles_cdf`: $T_n(G) \le \binom{n}{3}$ forces the
   almost-sure upper cap $W_n(G) \le \sqrt{128 n^2 (1 - p_n)}$ whenever $p_n \ge 1/2$, incompatible
   with $\Phi(K) < 1$ if $n^2 (1 - p_n)$ does not tend to $\infty$.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace SteinMethod

/-! ### 1. Boundary Mean and Variance on $[0, 1]$ -/

lemma cliqueSet_three_ncard_le_choose {n : ℕ} (G : SimpleGraph (Fin n)) :
    ((G.cliqueSet 3).ncard : ℝ) ≤ (n.choose 3 : ℝ) := by
  rw [ncard_cliqueSet_three_eq_sum_rucTriInd]
  calc ∑ i : Fin (n.choose 3), rucTriInd i G
      ≤ ∑ _i : Fin (n.choose 3), (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ by
        by_cases h : G.IsNClique 3 (rucTripleOf i)
        · simp [rucTriInd_of_isNClique h]
        · simp [rucTriInd_of_not_isNClique h]
    _ = (n.choose 3 : ℝ) := by simp

lemma erdosRenyi_triangles_mean_closed {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫ G, ((G.cliqueSet 3).ncard : ℝ) ∂erdosRenyi n p = (n.choose 3 : ℝ) * p ^ 3 := by
  simp_rw [ncard_cliqueSet_three_eq_sum_rucTriInd]
  rw [integral_finsetSum Finset.univ fun _ _ ↦ Integrable.of_finite]
  have hterm : ∀ i : Fin (n.choose 3), ∫ G, rucTriInd i G ∂erdosRenyi n p = p ^ 3 := by
    intro i
    dsimp only [rucTriInd]
    rw [integral_indicator MeasurableSet.of_discrete]
    simp [erdosRenyi_real_isNClique_ruc hp0 hp1 i]
  simp [hterm]

lemma erdosRenyi_triangles_variance_closed {n : ℕ} {p : ℝ}
    (hn : 3 ≤ n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    ProbabilityTheory.variance T (erdosRenyi n p) =
      (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) := by
  intro T
  rcases eq_or_lt_of_le hp0 with rfl | hp0_pos
  · have hmean0 : ∫ G, T G ∂erdosRenyi n 0 = 0 := by
      rw [erdosRenyi_triangles_mean_closed le_rfl zero_le_one]
      ring
    have hae0 : T =ᵐ[erdosRenyi n 0] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ ↦ Nat.cast_nonneg _) Integrable.of_finite).mp hmean0
    rw [ProbabilityTheory.variance_congr hae0, ProbabilityTheory.variance_zero]
    ring
  · rcases eq_or_lt_of_le hp1 with rfl | hp1_lt
    · let D : SimpleGraph (Fin n) → ℝ := fun G ↦ (n.choose 3 : ℝ) - T G
      have hD_nn : ∀ G, 0 ≤ D G := fun G ↦ sub_nonneg.mpr (cliqueSet_three_ncard_le_choose G)
      have hD_int0 : ∫ G, D G ∂erdosRenyi n 1 = 0 := by
        dsimp only [D]
        rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const, probReal_univ,
          one_smul, erdosRenyi_triangles_mean_closed zero_le_one le_rfl]
        ring
      have hD_ae0 : D =ᵐ[erdosRenyi n 1] 0 :=
        (integral_eq_zero_iff_of_nonneg hD_nn Integrable.of_finite).mp hD_int0
      have hT_eq : T = fun G ↦ -D G + (n.choose 3 : ℝ) := by
        ext G; dsimp only [D]; ring
      have hneg0 : (fun G ↦ -D G) =ᵐ[erdosRenyi n 1] 0 :=
        hD_ae0.mono fun G hG ↦ by simp [hG]
      rw [hT_eq, ProbabilityTheory.variance_add_const Measurable.of_discrete.aestronglyMeasurable,
        ProbabilityTheory.variance_congr hneg0, ProbabilityTheory.variance_zero]
      ring
    · exact (erdosRenyi_triangles_mean_and_variance hn hp0_pos hp1_lt).2

/-! ### 2. Lattice Gap Lemma ($\sigma_n \to \infty$) -/

lemma tendsto_sigma_atTop_of_tendsto_triangles_cdf {p : ℕ → ℝ}
    (_hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1)
    (hCDF :
      let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
      let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
      let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
      let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
      ∀ x : ℝ,
        Tendsto (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
          atTop (𝓝 (stdNormalCDF x))) :
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    Tendsto σ atTop atTop := by
  intro T σ
  let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
  let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
  by_contra hnot
  rw [Filter.tendsto_atTop_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨B, hfreq⟩
  let B' := max B 1
  have hB'_pos : 0 < B' := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  let δ := (4 * B')⁻¹
  have hδ_pos : 0 < δ := by positivity
  let ν : ℕ → Measure ℝ := fun n ↦ (erdosRenyi n (p n)).map (W n)
  have hIoc_eq : ∀ (n : ℕ) {a b : ℝ}, a ≤ b →
      (ν n).real (Set.Ioc a b) = (ν n).real (Set.Iic b) - (ν n).real (Set.Iic a) := by
    intro n a b hab
    have : IsProbabilityMeasure (ν n) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_of_finite (W n)).aemeasurable).mpr
        inferInstance
    have hunion : Set.Iic a ∪ Set.Ioc a b = Set.Iic b := Iic_union_Ioc_eq_Iic hab
    have hdisj : Disjoint (Set.Iic a) (Set.Ioc a b) :=
      disjoint_left.mpr fun _ h1 h2 ↦ not_lt_of_ge h1 h2.1
    have hadd := measureReal_union hdisj measurableSet_Ioc (μ := ν n)
    rw [hunion] at hadd
    linarith
  have htend1 : Tendsto (fun n ↦ (ν n).real (Set.Ioc 0 δ)) atTop
      (𝓝 (stdNormalCDF δ - stdNormalCDF 0)) := by
    simp_rw [hIoc_eq _ hδ_pos.le]
    exact (hCDF δ).sub (hCDF 0)
  have htend2 : Tendsto (fun n ↦ (ν n).real (Set.Ioc δ (2 * δ))) atTop
      (𝓝 (stdNormalCDF (2 * δ) - stdNormalCDF δ)) := by
    simp_rw [hIoc_eq _ (by linarith : δ ≤ 2 * δ)]
    exact (hCDF (2 * δ)).sub (hCDF δ)
  have hlim1_pos : 0 < stdNormalCDF δ - stdNormalCDF 0 :=
    sub_pos.mpr (strictMono_stdNormalCDF hδ_pos)
  have hlim2_pos : 0 < stdNormalCDF (2 * δ) - stdNormalCDF δ :=
    sub_pos.mpr (strictMono_stdNormalCDF (by linarith))
  have hev : ∀ᶠ n : ℕ in atTop,
      0 < (ν n).real (Set.Ioc 0 δ) ∧ 0 < (ν n).real (Set.Ioc δ (2 * δ)) :=
    (htend1.eventually (Ioi_mem_nhds hlim1_pos)).and
      (htend2.eventually (Ioi_mem_nhds hlim2_pos))
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  obtain ⟨n, hnN, hσB⟩ := hfreq N
  have hσB' : σ n ≤ B' := hσB.le.trans (le_max_left B 1)
  obtain ⟨hpos1, hpos2⟩ := hN n hnN
  rw [map_measureReal_apply (measurable_of_finite (W n)) measurableSet_Ioc] at hpos1 hpos2
  have hne1 : (W n ⁻¹' Set.Ioc 0 δ).Nonempty :=
    nonempty_iff_ne_empty.mpr fun he ↦ by simp [he] at hpos1
  have hne2 : (W n ⁻¹' Set.Ioc δ (2 * δ)).Nonempty :=
    nonempty_iff_ne_empty.mpr fun he ↦ by simp [he] at hpos2
  rcases hne1 with ⟨G₁, hG₁_lo, hG₁_hi⟩
  rcases hne2 with ⟨G₂, hG₂_lo, hG₂_hi⟩
  change 0 < W n G₁ at hG₁_lo
  change W n G₁ ≤ δ at hG₁_hi
  change δ < W n G₂ at hG₂_lo
  change W n G₂ ≤ 2 * δ at hG₂_hi
  have hσ_pos : 0 < σ n := by
    have hσ_nn : 0 ≤ σ n := Real.sqrt_nonneg _
    rcases eq_or_lt_of_le hσ_nn with h0 | hpos
    · exfalso
      have hW0 : W n G₁ = 0 := by simp [W, ← h0]
      linarith
    · exact hpos
  have hW_lt : W n G₁ < W n G₂ := hG₁_hi.trans_lt hG₂_lo
  have hT_lt : T n G₁ < T n G₂ := by
    have hmul := mul_lt_mul_of_pos_right hW_lt hσ_pos
    dsimp only [W] at hmul
    rw [div_mul_cancel₀ _ hσ_pos.ne', div_mul_cancel₀ _ hσ_pos.ne'] at hmul
    linarith
  have hnat_lt : (G₁.cliqueSet 3).ncard < (G₂.cliqueSet 3).ncard := by
    dsimp only [T] at hT_lt
    exact_mod_cast hT_lt
  have hT_gap : 1 ≤ T n G₂ - T n G₁ := by
    have h1 : (G₁.cliqueSet 3).ncard + 1 ≤ (G₂.cliqueSet 3).ncard := hnat_lt
    have h1r : ((G₁.cliqueSet 3).ncard : ℝ) + 1 ≤ ((G₂.cliqueSet 3).ncard : ℝ) := by
      exact_mod_cast h1
    dsimp only [T]
    linarith
  have hW_gap : 4 * δ ≤ W n G₂ - W n G₁ := by
    have hdiv1 : 1 / B' ≤ 1 / σ n := one_div_le_one_div_of_le hσ_pos hσB'
    have hdiv2 : 1 / σ n ≤ (T n G₂ - T n G₁) / σ n :=
      div_le_div_of_nonneg_right hT_gap hσ_pos.le
    have hW_sub : W n G₂ - W n G₁ = (T n G₂ - T n G₁) / σ n := by
      dsimp only [W]; ring
    have h4δ : 4 * δ = 1 / B' := by
      dsimp only [δ]
      field_simp [hB'_pos.ne']
    linarith
  linarith

/-! ### 3. Necessity of $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$ -/

/-- Necessity of $n p_n \to \infty$ (`SteinIntro.tex:943-944`, `\cite{ruc88}`). -/
theorem tendsto_mul_p_atTop_of_tendsto_triangles_cdf {p : ℕ → ℝ}
    (hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1)
    (hCDF :
      let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
      let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
      let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
      let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
      ∀ x : ℝ,
        Tendsto (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
          atTop (𝓝 (stdNormalCDF x))) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop := by
  have hσ_top := tendsto_sigma_atTop_of_tendsto_triangles_cdf hp hCDF
  dsimp only at hσ_top
  let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
  let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
  by_contra hnot
  rw [Filter.tendsto_atTop_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨M, hfreq⟩
  let M' := max M 1
  have hM'_pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  let B := Real.sqrt (M' ^ 3 + 3 * M' ^ 5) + 1
  have hev := hσ_top.eventually (eventually_ge_atTop B)
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨N, hN⟩
  obtain ⟨n, hn_max, hnp_lt⟩ := hfreq (max N 4)
  have hnN : N ≤ n := (le_max_left N 4).trans hn_max
  have hn4 : 4 ≤ n := (le_max_right N 4).trans hn_max
  have hσ_ge : B ≤ σ n := hN n hnN
  obtain ⟨hp0, hp1⟩ := hp n
  have hnp_nn : 0 ≤ (n : ℝ) * p n := mul_nonneg (Nat.cast_nonneg n) hp0
  have hnp_le : (n : ℝ) * p n ≤ M' := hnp_lt.le.trans (le_max_left M 1)
  have hv_le : ProbabilityTheory.variance (T n) (erdosRenyi n (p n)) ≤ M' ^ 3 + 3 * M' ^ 5 := by
    rw [erdosRenyi_triangles_variance_closed (by omega : 3 ≤ n) hp0 hp1]
    obtain ⟨_, hch_hi⟩ := choose_three_bounds hn4
    have hch_le : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
      linarith
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hbrack : 1 - p n ^ 3 + 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n) ≤
        1 + 3 * (n : ℝ) ^ 2 * p n ^ 2 := by
      have h1p3 : 1 - p n ^ 3 ≤ 1 := by linarith [pow_nonneg hp0 3]
      have h1p : 1 - p n ≤ 1 := by linarith
      have hn3_le : (n : ℝ) - 3 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 1)]
      have hterm_le : 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n) ≤
          3 * (n : ℝ) ^ 2 * p n ^ 2 * 1 := by
        by_cases hsign : 0 ≤ (n : ℝ) - 3
        · exact mul_le_mul
            (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (p n)))
            h1p (by linarith) (by positivity)
        · have : 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg (p n))) (by linarith)
          exact this.trans (by positivity)
      linarith
    have hbrack_nn : 0 ≤ 1 - p n ^ 3 + 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n) := by
      have h1p3_nn : 0 ≤ 1 - p n ^ 3 := by
        have : 1 - p n ^ 3 = (1 - p n) * (1 + p n + p n ^ 2) := by ring
        rw [this]
        exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg (p n)])
      have hn3_nn : 0 ≤ (n : ℝ) - 3 := by
        have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
        linarith
      exact add_nonneg h1p3_nn
        (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg (p n))) (by linarith))
    calc (n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3 + 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n))
        ≤ (n : ℝ) ^ 3 * p n ^ 3 * (1 + 3 * (n : ℝ) ^ 2 * p n ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hch_le (pow_nonneg hp0 3)) hbrack
            hbrack_nn (by positivity)
      _ = ((n : ℝ) * p n) ^ 3 + 3 * ((n : ℝ) * p n) ^ 5 := by ring
      _ ≤ M' ^ 3 + 3 * M' ^ 5 :=
          add_le_add (pow_le_pow_left₀ hnp_nn hnp_le 3)
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnp_nn hnp_le 5) (by norm_num))
  have hσ_le : σ n ≤ Real.sqrt (M' ^ 3 + 3 * M' ^ 5) := Real.sqrt_le_sqrt hv_le
  linarith [show B = Real.sqrt (M' ^ 3 + 3 * M' ^ 5) + 1 from rfl]

/-- Necessity of $n^2 (1 - p_n) \to \infty$ (`SteinIntro.tex:943-944`, `\cite{ruc88}`). -/
theorem tendsto_sq_mul_one_sub_p_atTop_of_tendsto_triangles_cdf {p : ℕ → ℝ}
    (hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1)
    (hCDF :
      let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
      let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
      let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
      let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
      ∀ x : ℝ,
        Tendsto (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
          atTop (𝓝 (stdNormalCDF x))) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop := by
  have hσ_top := tendsto_sigma_atTop_of_tendsto_triangles_cdf hp hCDF
  dsimp only at hσ_top
  let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
  let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
  let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
  let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
  by_contra hnot
  rw [Filter.tendsto_atTop_atTop] at hnot
  push Not at hnot
  rcases hnot with ⟨M, hfreq⟩
  let M' := max M 1
  have hM'_pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  let K := Real.sqrt (200 * M')
  have hK_nn : 0 ≤ K := Real.sqrt_nonneg _
  have hΦ_lt : stdNormalCDF K < 1 := stdNormalCDF_lt_one K
  let c := (1 + stdNormalCDF K) / 2
  have hc_lt1 : c < 1 := by dsimp only [c]; linarith
  have hev_cdf := (hCDF K).eventually
    (Iio_mem_nhds (by dsimp only [c]; linarith : stdNormalCDF K < c))
  have hev_σ := hσ_top.eventually (eventually_ge_atTop 1)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (Real.sqrt (2 * M'))
  have hev_all := hev_cdf.and (hev_σ.and (eventually_ge_atTop (max N₃ 6)))
  rw [Filter.eventually_atTop] at hev_all
  rcases hev_all with ⟨N, hN⟩
  obtain ⟨n, hnN, hn2q_lt⟩ := hfreq N
  obtain ⟨hcdf_lt, hσ_ge1, hn_max⟩ := hN n hnN
  have hn_gt_sqrt : Real.sqrt (2 * M') < (n : ℝ) :=
    hN₃.trans_le (by exact_mod_cast (le_max_left N₃ 6).trans hn_max)
  have hn6 : 6 ≤ n := (le_max_right N₃ 6).trans hn_max
  obtain ⟨hp0, hp1⟩ := hp n
  have hn2q_le : (n : ℝ) ^ 2 * (1 - p n) ≤ M' := hn2q_lt.le.trans (le_max_left M 1)
  have hσ_pos : 0 < σ n := lt_of_lt_of_le zero_lt_one hσ_ge1
  have hp_pos : 0 < p n := by
    rcases eq_or_lt_of_le hp0 with hpz | hpos
    · exfalso
      have hv0 := erdosRenyi_triangles_variance_closed (by omega : 3 ≤ n) hp0 hp1
      dsimp only at hv0
      have h0 : ProbabilityTheory.variance (T n) (erdosRenyi n (p n)) = 0 := by
        dsimp only [T]; rw [hv0, ← hpz]; ring
      have : σ n = 0 := by simp [σ, h0]
      linarith
    · exact hpos
  have hp_lt1 : p n < 1 := by
    rcases eq_or_lt_of_le hp1 with hpone | hlt
    · exfalso
      have hv0 := erdosRenyi_triangles_variance_closed (by omega : 3 ≤ n) hp0 hp1
      dsimp only at hv0
      have h0 : ProbabilityTheory.variance (T n) (erdosRenyi n (p n)) = 0 := by
        dsimp only [T]; rw [hv0, hpone]; ring
      have : σ n = 0 := by simp [σ, h0]
      linarith
    · exact hlt
  have hq_pos : 0 < 1 - p n := by linarith
  have hp_half : 1 / 2 ≤ p n := by
    have hn2_gt : 2 * M' < (n : ℝ) ^ 2 := by
      have hsq := pow_lt_pow_left₀ hn_gt_sqrt (Real.sqrt_nonneg _) two_ne_zero
      rwa [Real.sq_sqrt (by positivity)] at hsq
    have hmul : (2 * M') * (1 - p n) < (n : ℝ) ^ 2 * (1 - p n) :=
      mul_lt_mul_of_pos_right hn2_gt hq_pos
    have hlt_M : M' * (2 * (1 - p n)) < M' * 1 := by linarith
    have h2q : 2 * (1 - p n) < 1 := lt_of_mul_lt_mul_left hlt_M hM'_pos.le
    linarith
  have hW_cap : ∀ G : SimpleGraph (Fin n), W n G ≤ K := by
    intro G
    by_cases hnum : T n G - μ n ≤ 0
    · exact (div_nonpos_of_nonpos_of_nonneg hnum hσ_pos.le).trans hK_nn
    · push Not at hnum
      obtain ⟨_, hch_hi⟩ := choose_three_bounds (by omega : 4 ≤ n)
      have hμ_eq := erdosRenyi_triangles_mean_closed hp0 hp1 (n := n)
      have hnum_le : T n G - μ n ≤ (n : ℝ) ^ 3 * (1 - p n) / 2 := by
        have hT_le := cliqueSet_three_ncard_le_choose G
        have h1p3 : 1 - p n ^ 3 ≤ 3 * (1 - p n) := by
          have hfac : 3 * (1 - p n) - (1 - p n ^ 3) =
              (1 - p n) * ((1 - p n) + (1 - p n ^ 2)) := by ring
          have hp2_le1 : p n ^ 2 ≤ 1 := pow_le_one₀ hp0 hp1
          have hnn : 0 ≤ (1 - p n) * ((1 - p n) + (1 - p n ^ 2)) :=
            mul_nonneg (by linarith) (by linarith)
          linarith
        calc T n G - μ n
            ≤ (n.choose 3 : ℝ) - (n.choose 3 : ℝ) * p n ^ 3 := by
              dsimp only [T, μ]
              linarith
          _ = (n.choose 3 : ℝ) * (1 - p n ^ 3) := by ring
          _ ≤ ((n : ℝ) ^ 3 / 6) * (3 * (1 - p n)) :=
              mul_le_mul hch_hi h1p3
                (by linarith [pow_le_one₀ hp0 hp1 (n := 3)]) (by positivity)
          _ = (n : ℝ) ^ 3 * (1 - p n) / 2 := by ring
      obtain ⟨_, hv_lo2⟩ := erdosRenyi_triangles_variance_lower_bounds hn6 hp_pos hp_lt1
      have hv_lo : (n : ℝ) ^ 4 * (1 - p n) / 512 ≤ σ n ^ 2 := by
        rw [Real.sq_sqrt (ProbabilityTheory.variance_nonneg _ _)]
        have hp5 : (1 / 32 : ℝ) ≤ p n ^ 5 := by
          have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / 2) hp_half 5
          norm_num at this
          exact this
        calc (n : ℝ) ^ 4 * (1 - p n) / 512
            = (n : ℝ) ^ 4 * (1 / 32 : ℝ) * (1 - p n) / 16 := by ring
          _ ≤ (n : ℝ) ^ 4 * p n ^ 5 * (1 - p n) / 16 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hp5 (by positivity)) hq_pos.le)
                (by norm_num)
          _ ≤ ProbabilityTheory.variance (T n) (erdosRenyi n (p n)) := hv_lo2
      have hsq : (W n G) ^ 2 ≤ K ^ 2 := by
        have hK2 : K ^ 2 = 200 * M' := Real.sq_sqrt (by positivity)
        rw [hK2]
        dsimp only [W]
        rw [div_pow]
        calc (T n G - μ n) ^ 2 / σ n ^ 2
            ≤ ((n : ℝ) ^ 3 * (1 - p n) / 2) ^ 2 / σ n ^ 2 :=
              div_le_div_of_nonneg_right (pow_le_pow_left₀ hnum.le hnum_le 2) (sq_nonneg _)
          _ ≤ ((n : ℝ) ^ 3 * (1 - p n) / 2) ^ 2 / ((n : ℝ) ^ 4 * (1 - p n) / 512) :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hv_lo
          _ = 128 * ((n : ℝ) ^ 2 * (1 - p n)) := by
              field_simp [hq_pos.ne', (show (n : ℝ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0))]
              ring
          _ ≤ 200 * M' := by linarith [mul_nonneg (sq_nonneg (n : ℝ)) hq_pos.le]
      have hsqrt := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (div_pos hnum hσ_pos).le, Real.sqrt_sq hK_nn] at hsqrt
  have hpre_univ : W n ⁻¹' Set.Iic K = Set.univ :=
    Set.eq_univ_of_forall fun G ↦ hW_cap G
  have hprob1 : ((erdosRenyi n (p n)).map (W n)).real (Set.Iic K) = 1 := by
    rw [map_measureReal_apply (measurable_of_finite (W n)) measurableSet_Iic, hpre_univ,
      probReal_univ]
  linarith

end SteinMethod
