/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Metrics.Basic
import Formalization.Normal.WassersteinBound
import Formalization.RandomGraph.TrianglesRucinskiNecessity
import Formalization.RandomGraph.TrianglesRucinskiSufficiency
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Ruciński's Triangle CLT Criterion (`TrianglesRucinskiCLT`)

Combines the Theorem 3.13 size-bias Wasserstein sufficiency bound (`TrianglesRucinskiSufficiency`),
the elementary lattice-gap / upper-support necessity proof (`TrianglesRucinskiNecessity`), and
distributional convergence bridges (`kolmogorovDist`, `wassersteinDist`, pointwise CDF, and
`ProbabilityMeasure ℝ` weak convergence via Portmanteau) to prove from scratch Ruciński's (1988,
*Probab. Theory Related Fields* 78, 1–10, Theorem 2 specialized to $H = K_3$ with
$m(K_3) = e(K_3)/v(K_3) = 1$) triangle-count CLT criterion (`SteinIntro.tex:943-944`,
`\cite{ruc88}`):

* `Sec3_2_1_triangles_rucinski_proof`: $W_n \xrightarrow{d} \mathcal{N}(0, 1)$ (in pointwise CDF,
  $d_{\mathrm{K}}$, or $d_{\mathrm{W}}$) iff $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$.
* `Sec3_2_1_triangles_rucinski_power_regime_proof`: for $0 \le p_n \le 1$ with
  $n^\alpha p_n \to c > 0$ ($0 \le \alpha$, $\alpha = 0 \to c < 1$), normal convergence
  ($d_{\mathrm{W}} \to 0$, $d_{\mathrm{K}} \to 0$, and pointwise CDF) holds for all
  $0 \le \alpha < 1$ (strictly containing $0 \le \alpha < 2/9$), and fails for $\alpha \ge 1$.
* `triangles_tendsto_probabilityMeasure_stdNormalLaw_iff`: equivalent characterization in
  `ProbabilityMeasure ℝ` (`Measure.toProbabilityMeasure`).
* `triangles_rucinski_at_inv_sqrt`: explicit witness $p_n = n^{-1/2}$ ($\alpha = 1/2 \ge 2/9$).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### 1. Convergence Mode Bridges -/

lemma tendsto_kolmogorovDist_stdNormalLaw_zero_of_wassersteinDist {ν : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (ν n)]
    (hW : Tendsto (fun n ↦ wassersteinDist (ν n) stdNormalLaw) atTop (𝓝 0)) :
    Tendsto (fun n ↦ kolmogorovDist (ν n) stdNormalLaw) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ))
  have hle : ∀ n : ℕ,
      kolmogorovDist (ν n) stdNormalLaw ≤ C * wassersteinDist (ν n) stdNormalLaw ^ (1 / 2 : ℝ) := by
    intro n
    have h := kolmogorovDist_map_le_stdNormal_rpow_wassersteinDist_map (ν n) stdNormalLaw
      measurable_id.aemeasurable measurable_id.aemeasurable Measure.map_id
    simpa [Measure.map_id, C] using h
  have hrpow : Tendsto (fun n ↦ wassersteinDist (ν n) stdNormalLaw ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    have hcont := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hcont
    exact hcont.comp hW
  have hmul : Tendsto (fun n ↦ C * wassersteinDist (ν n) stdNormalLaw ^ (1 / 2 : ℝ))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hrpow (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul
    (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall hle)

lemma tendsto_cdf_stdNormalCDF_of_kolmogorovDist {ν : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (ν n)]
    (hK : Tendsto (fun n ↦ kolmogorovDist (ν n) stdNormalLaw) atTop (𝓝 0)) :
    ∀ x : ℝ, Tendsto (fun n ↦ (ν n).real (Set.Iic x)) atTop (𝓝 (stdNormalCDF x)) := by
  intro x
  have htoReal : Tendsto (fun n ↦ (kolmogorovDist (ν n) stdNormalLaw).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hK
  have hev_lt : ∀ᶠ n : ℕ in atTop, kolmogorovDist (ν n) stdNormalLaw < ⊤ :=
    hK.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ htoReal
  filter_upwards [hev_lt] with n hlt
  rw [Real.norm_eq_abs, stdNormalCDF, ProbabilityTheory.cdf_eq_real]
  have hle_enn : ENNReal.ofReal |(ν n).real (Set.Iic x) - stdNormalLaw.real (Set.Iic x)| ≤
      kolmogorovDist (ν n) stdNormalLaw := by
    rw [kolmogorovDist_eq_iSup (ν n) stdNormalLaw]
    exact le_iSup (fun y : ℝ ↦ ENNReal.ofReal |(ν n).real (Set.Iic y) -
      stdNormalLaw.real (Set.Iic y)|) x
  exact (ENNReal.ofReal_le_iff_le_toReal hlt.ne).mp hle_enn

lemma tendsto_probabilityMeasure_stdNormalLaw_of_wassersteinDist {ν : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (ν n)]
    (hW : Tendsto (fun n ↦ wassersteinDist (ν n) stdNormalLaw) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (ν n).toProbabilityMeasure) atTop
      (𝓝 stdNormalLaw.toProbabilityMeasure) := by
  rw [MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  have hf_cont : Continuous f := hL.continuous
  let M : ℝ := ‖f 0‖ + max C 0
  have hf_bdd : ∀ x : ℝ, ‖f x‖ ≤ M := fun x ↦ by
    have hd : ‖f x - f 0‖ ≤ C := by simpa [dist_eq_norm] using hC x 0
    have htri : ‖f x‖ - ‖f 0‖ ≤ ‖f x - f 0‖ := norm_sub_norm_le (f x) (f 0)
    have hmax : C ≤ max C 0 := le_max_left C 0
    dsimp only [M]
    linarith
  have hf_int : ∀ μ : Measure ℝ, [IsFiniteMeasure μ] → Integrable f μ := fun μ _ ↦
    Integrable.of_bound hf_cont.aestronglyMeasurable M (Eventually.of_forall hf_bdd)
  let K : ℝ := max (L : ℝ) 1
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right (L : ℝ) 1)
  let g : ℝ → ℝ := fun x ↦ K⁻¹ * f x
  have hg_lip : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    have hfy := hL.dist_le_mul x y
    have hLK : (L : ℝ) ≤ K := le_max_left (L : ℝ) 1
    calc dist (g x) (g y)
        = K⁻¹ * dist (f x) (f y) := by
          simp only [g, Real.dist_eq]
          rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hK_pos)]
      _ ≤ K⁻¹ * ((L : ℝ) * dist x y) :=
          mul_le_mul_of_nonneg_left hfy (inv_nonneg.mpr hK_pos.le)
      _ ≤ K⁻¹ * (K * dist x y) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hLK dist_nonneg) (inv_nonneg.mpr hK_pos.le)
      _ = 1 * dist x y := by field_simp [hK_pos.ne']
  have htoReal : Tendsto (fun n ↦ (wassersteinDist (ν n) stdNormalLaw).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW
  have hev_lt : ∀ᶠ n : ℕ in atTop, wassersteinDist (ν n) stdNormalLaw < ⊤ :=
    hW.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  have hg_tend : Tendsto (fun n ↦ ∫ x, g x ∂ν n) atTop (𝓝 (∫ x, g x ∂stdNormalLaw)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ htoReal
    filter_upwards [hev_lt] with n hlt
    rw [Real.norm_eq_abs]
    have hle_enn : ENNReal.ofReal |(∫ x, g x ∂ν n) - (∫ x, g x ∂stdNormalLaw)| ≤
        wassersteinDist (ν n) stdNormalLaw :=
      le_ipm hg_lip ((hf_int (ν n)).const_mul K⁻¹) ((hf_int stdNormalLaw).const_mul K⁻¹)
    exact (ENNReal.ofReal_le_iff_le_toReal hlt.ne).mp hle_enn
  have hfg : ∀ μ : Measure ℝ, ∫ x, f x ∂μ = K * ∫ x, g x ∂μ := fun μ ↦ by
    dsimp only [g]
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hK_pos.ne', one_mul]
  simp_rw [Measure.coe_toProbabilityMeasure, hfg]
  exact hg_tend.const_mul K

lemma tendsto_cdf_stdNormalCDF_of_probabilityMeasure {ν : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (ν n)]
    (hP : Tendsto (fun n ↦ (ν n).toProbabilityMeasure) atTop
      (𝓝 stdNormalLaw.toProbabilityMeasure)) :
    ∀ x : ℝ, Tendsto (fun n ↦ (ν n).real (Set.Iic x)) atTop (𝓝 (stdNormalCDF x)) := by
  intro x
  have hfront_null :
      (stdNormalLaw.toProbabilityMeasure : Measure ℝ) (frontier (Set.Iic x)) = 0 := by
    rw [Measure.coe_toProbabilityMeasure, frontier_Iic, stdNormalLaw,
      gaussianReal_of_var_ne_zero 0 one_ne_zero,
      withDensity_apply _ (measurableSet_singleton x),
      Measure.restrict_eq_zero.mpr Real.volume_singleton, lintegral_zero_measure]
  have htend_enn :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hP hfront_null
  simp_rw [Measure.coe_toProbabilityMeasure] at htend_enn
  have htend_real :=
    (ENNReal.tendsto_toReal (measure_ne_top stdNormalLaw (Set.Iic x))).comp htend_enn
  simpa only [Function.comp_def, measureReal_def, stdNormalCDF,
    ProbabilityTheory.cdf_eq_real] using htend_real

/-! ### 2. Ruciński's Triangle CLT Criterion (`Sec3_2_1_triangles_rucinski_proof`) -/

/-- **Ruciński's (1988) triangle CLT criterion** (`SteinIntro.tex:943-944`, citing Ruciński 1988
`\cite{ruc88}`, Theorem 2 specialized to $H = K_3$ with $m(K_3) = e(K_3)/v(K_3) = 1$, proved from
scratch): for $G \sim G(n, p_n)$ with $0 \le p_n \le 1$, the standardized triangle count
$W_n = (T_n - \mathbb{E}[T_n])/\sigma_n$ converges in distribution to $\mathcal{N}(0, 1)$ (in
pointwise CDF, Kolmogorov distance $d_{\mathrm{K}}$, or Wasserstein distance $d_{\mathrm{W}}$) iff
$n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$.

Convention note: when $\sigma_n = 0$ (e.g. $p_n \in \{0, 1\}$ or $n < 3$), Lean's real division
evaluates $W_n = 0$; the full domain $0 \le p_n \le 1$ is sound without $0 < p_n < 1$ because if
$p_n \in \{0, 1\}$ infinitely often then $W_n \equiv 0$ along that subsequence (so normal
convergence fails) while $n p_n = 0$ or $n^2 (1 - p_n) = 0$ along that subsequence (so the
criterion also fails), whereas $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$ force
$0 < p_n < 1$ and $\sigma_n > 0$ eventually. -/
theorem Sec3_2_1_triangles_rucinski_proof :
    ∀ {p : ℕ → ℝ},
      (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
      let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
      let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
      let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
      let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
      ((∀ x : ℝ,
          Tendsto
            (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
            atTop (𝓝 (stdNormalCDF x))) ↔
        Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop ∧
          Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop) ∧
      (Tendsto
          (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          atTop (𝓝 0) ↔
        Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop ∧
          Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop) ∧
      (Tendsto
          (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          atTop (𝓝 0) ↔
        Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop ∧
          Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop) := by
  intro p hp T μ σ W
  let ν : ℕ → Measure ℝ := fun n ↦ (erdosRenyi n (p n)).map (W n)
  have : ∀ n : ℕ, IsProbabilityMeasure (ν n) := fun n ↦
    (Measure.isProbabilityMeasure_map_iff (measurable_of_finite (W n)).aemeasurable).mpr
      inferInstance
  have hRuc_to_W :
      Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop ∧
        Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop →
        Tendsto (fun n : ℕ ↦ wassersteinDist (ν n) stdNormalLaw) atTop (𝓝 0) :=
    fun ⟨hnp, hn2q⟩ ↦ tendsto_triangles_wassersteinDist_zero_of_rucinski hp hnp hn2q
  have hW_to_K :
      Tendsto (fun n : ℕ ↦ wassersteinDist (ν n) stdNormalLaw) atTop (𝓝 0) →
        Tendsto (fun n : ℕ ↦ kolmogorovDist (ν n) stdNormalLaw) atTop (𝓝 0) :=
    tendsto_kolmogorovDist_stdNormalLaw_zero_of_wassersteinDist
  have hK_to_CDF :
      Tendsto (fun n : ℕ ↦ kolmogorovDist (ν n) stdNormalLaw) atTop (𝓝 0) →
        ∀ x : ℝ, Tendsto (fun n : ℕ ↦ (ν n).real (Set.Iic x)) atTop (𝓝 (stdNormalCDF x)) :=
    tendsto_cdf_stdNormalCDF_of_kolmogorovDist
  have hCDF_to_Ruc :
      (∀ x : ℝ, Tendsto (fun n : ℕ ↦ (ν n).real (Set.Iic x)) atTop (𝓝 (stdNormalCDF x))) →
        Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop ∧
          Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop :=
    fun hcdf ↦ ⟨tendsto_mul_p_atTop_of_tendsto_triangles_cdf hp hcdf,
      tendsto_sq_mul_one_sub_p_atTop_of_tendsto_triangles_cdf hp hcdf⟩
  exact ⟨⟨hCDF_to_Ruc, fun h ↦ hK_to_CDF (hW_to_K (hRuc_to_W h))⟩,
    ⟨fun h ↦ hCDF_to_Ruc (hK_to_CDF h), fun h ↦ hW_to_K (hRuc_to_W h)⟩,
    ⟨fun h ↦ hCDF_to_Ruc (hK_to_CDF (hW_to_K h)), hRuc_to_W⟩⟩

/-- **Power-law normal-convergence regime for triangles** (`SteinIntro.tex:942-944`, citing
Ruciński 1988 `\cite{ruc88}`, Theorem 2 with $m(K_3) = 1$, proved from scratch): if
$0 \le p_n \le 1$ satisfies $\lim_{n \to \infty} n^\alpha p_n = c > 0$ for some $\alpha \ge 0$,
with $c < 1$ when $\alpha = 0$ (`ISSUE-3.2.1`), then:
1. for every $0 \le \alpha < 1$ (strictly containing the dependency-neighborhood regime
   $0 \le \alpha < 2/9$), $W_n$ converges to $\mathcal{N}(0, 1)$ in $d_{\mathrm{W}}$,
   $d_{\mathrm{K}}$, and pointwise CDF;
2. conversely, for $\alpha \ge 1$, normal convergence fails in pointwise CDF, $d_{\mathrm{K}}$, and
   $d_{\mathrm{W}}$. -/
theorem Sec3_2_1_triangles_rucinski_power_regime_proof :
    ∀ {p : ℕ → ℝ} {α c : ℝ},
      (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
      0 ≤ α →
      0 < c →
      (α = 0 → c < 1) →
      Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) atTop (𝓝 c) →
      let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
      let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
      let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
      let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
      (α < 1 →
        Tendsto
          (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          atTop (𝓝 0) ∧
        (∀ x : ℝ,
          Tendsto
            (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
            atTop (𝓝 (stdNormalCDF x)))) ∧
      (1 ≤ α →
        ¬ (∀ x : ℝ,
            Tendsto
              (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
              atTop (𝓝 (stdNormalCDF x))) ∧
        ¬ Tendsto
            (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
            atTop (𝓝 0) ∧
        ¬ Tendsto
            (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
            atTop (𝓝 0)) := by
  intro p α c hp hα0 hc hc0 htend T μ σ W
  obtain ⟨hcdf_iff, hk_iff, hw_iff⟩ := Sec3_2_1_triangles_rucinski_proof hp
  refine ⟨fun hα1 ↦ ?_, fun hα_ge1 ↦ ?_⟩
  · have hnp : Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop := by
      have hev_lo : ∀ᶠ n : ℕ in atTop, c / 2 < (n : ℝ) ^ α * p n :=
        htend.eventually (Ioi_mem_nhds (by linarith))
      have hrpow_top : Tendsto (fun n : ℕ ↦ (c / 2) * (n : ℝ) ^ (1 - α)) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity)
          ((tendsto_rpow_atTop (by linarith : 0 < 1 - α)).comp tendsto_natCast_atTop_atTop)
      refine tendsto_atTop_mono' atTop ?_ hrpow_top
      filter_upwards [eventually_ge_atTop 1, hev_lo] with n hn1 hlo
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hrpow_pos : 0 < (n : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hn_pos (1 - α)
      calc (c / 2) * (n : ℝ) ^ (1 - α)
          ≤ ((n : ℝ) ^ α * p n) * (n : ℝ) ^ (1 - α) :=
            mul_le_mul_of_nonneg_right hlo.le hrpow_pos.le
        _ = ((n : ℝ) ^ α * (n : ℝ) ^ (1 - α)) * p n := by ring
        _ = (n : ℝ) * p n := by
            rw [← Real.rpow_add hn_pos, show α + (1 - α) = 1 by ring, Real.rpow_one]
    have hn2q : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop := by
      let q : ℝ := if α = 0 then (1 + c) / 2 else 1 / 2
      have hq_pos : 0 < q := by dsimp only [q]; split_ifs <;> linarith
      have h1q_pos : 0 < 1 - q := by
        dsimp only [q]
        split_ifs with h0
        · linarith [hc0 h0]
        · norm_num
      have hev_pq : ∀ᶠ n : ℕ in atTop, p n < q := by
        rcases eq_or_lt_of_le hα0 with rfl | hα_pos
        · have hp_c : Tendsto p atTop (𝓝 c) := by simpa using htend
          exact hp_c.eventually
            (Iio_mem_nhds (by simp only [q, ↓reduceIte]; linarith [hc0 rfl]))
        · have hrpow_neg : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-α)) atTop (𝓝 0) := by
            simpa only [Function.comp_def, neg_neg] using
              (tendsto_rpow_neg_atTop (neg_pos.mpr (by linarith : -α < 0))).comp
                tendsto_natCast_atTop_atTop
          have hp_zero : Tendsto p atTop (𝓝 0) := by
            have hm := htend.mul hrpow_neg
            rw [mul_zero] at hm
            refine hm.congr' ?_
            filter_upwards [eventually_ge_atTop 1] with n hn1
            have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
            calc ((n : ℝ) ^ α * p n) * (n : ℝ) ^ (-α)
                = p n * ((n : ℝ) ^ α * (n : ℝ) ^ (-α)) := by ring
              _ = p n := by rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero, mul_one]
          exact hp_zero.eventually (Iio_mem_nhds hq_pos)
      have hn2_top : Tendsto (fun n : ℕ ↦ (1 - q) * (n : ℝ) ^ 2) atTop atTop :=
        Tendsto.const_mul_atTop h1q_pos
          ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
      refine tendsto_atTop_mono' atTop ?_ hn2_top
      filter_upwards [hev_pq] with n hpq
      calc (1 - q) * (n : ℝ) ^ 2
          ≤ (1 - p n) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
        _ = (n : ℝ) ^ 2 * (1 - p n) := by ring
    exact ⟨hw_iff.mpr ⟨hnp, hn2q⟩, hk_iff.mpr ⟨hnp, hn2q⟩, hcdf_iff.mpr ⟨hnp, hn2q⟩⟩
  · have hnot_np : ¬ Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop := by
      intro hnp
      have hev_hi : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ α * p n < c + 1 :=
        htend.eventually (Iio_mem_nhds (by linarith))
      have hev_lo : ∀ᶠ n : ℕ in atTop, c + 1 ≤ (n : ℝ) * p n :=
        hnp.eventually (eventually_ge_atTop (c + 1))
      rcases ((eventually_ge_atTop 1).and (hev_hi.and hev_lo)).exists with ⟨n, hn1, hhi, hlo⟩
      have hn1_r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hrpow_le : (n : ℝ) ≤ (n : ℝ) ^ α := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1_r hα_ge1
      have hmul_le : (n : ℝ) * p n ≤ (n : ℝ) ^ α * p n :=
        mul_le_mul_of_nonneg_right hrpow_le (hp n).1
      linarith
    exact ⟨fun h ↦ hnot_np (hcdf_iff.mp h).1,
      fun h ↦ hnot_np (hk_iff.mp h).1,
      fun h ↦ hnot_np (hw_iff.mp h).1⟩

/-- Equivalent weak-convergence formulation in `ProbabilityMeasure ℝ` (`SteinIntro.tex:943-944`,
`\cite{ruc88}`). -/
theorem triangles_tendsto_probabilityMeasure_stdNormalLaw_iff {p : ℕ → ℝ}
    (hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) :
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    haveI : ∀ n : ℕ, IsProbabilityMeasure ((erdosRenyi n (p n)).map (W n)) := fun n ↦
      (Measure.isProbabilityMeasure_map_iff (measurable_of_finite (W n)).aemeasurable).mpr
        inferInstance
    Tendsto (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).toProbabilityMeasure) atTop
        (𝓝 stdNormalLaw.toProbabilityMeasure) ↔
      Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop ∧
        Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop := by
  intro T μ σ W
  have : ∀ n : ℕ, IsProbabilityMeasure ((erdosRenyi n (p n)).map (W n)) := fun n ↦
    (Measure.isProbabilityMeasure_map_iff (measurable_of_finite (W n)).aemeasurable).mpr
      inferInstance
  obtain ⟨hcdf_iff, _, hw_iff⟩ := Sec3_2_1_triangles_rucinski_proof hp
  exact ⟨fun hP ↦ hcdf_iff.mp (tendsto_cdf_stdNormalCDF_of_probabilityMeasure hP),
    fun hRuc ↦ tendsto_probabilityMeasure_stdNormalLaw_of_wassersteinDist (hw_iff.mpr hRuc)⟩

/-- Strict-subset witness (`SteinIntro.tex:943-944`): at $p_n = n^{-1/2}$ ($\alpha = 1/2 \notin
[0, 2/9)$), standardized triangle counts satisfy normal convergence in $d_{\mathrm{W}}$,
$d_{\mathrm{K}}$, and pointwise CDF. -/
theorem triangles_rucinski_at_inv_sqrt :
    let p : ℕ → ℝ := fun n ↦ if n = 0 then 0 else (Real.sqrt (n : ℝ))⁻¹
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) ∧
      Tendsto (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        atTop (𝓝 0) := by
  intro p T μ σ W
  have hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1 := by
    intro n
    by_cases hn0 : n = 0
    · simp [p, hn0]
    · simp only [p, hn0, ↓reduceIte]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hn1
      exact ⟨by positivity, inv_le_one_of_one_le₀ hsqrt1⟩
  have hnp : Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop atTop := by
    have hsqrt_top : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    refine hsqrt_top.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : n ≠ 0 := by omega
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    simp only [p, hn0, ↓reduceIte]
    rw [← div_eq_mul_inv, Real.div_sqrt]
  have hn2q : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) atTop atTop := by
    have hhalf_top : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 / 2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num)
        ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
    refine tendsto_atTop_mono' atTop ?_ hhalf_top
    filter_upwards [eventually_ge_atTop 4] with n hn4
    have hn0 : n ≠ 0 := by omega
    have hsqrt2 : 2 ≤ Real.sqrt (n : ℝ) := by
      have hn4r : (2 : ℝ) ^ 2 ≤ (n : ℝ) := by
        norm_num
        exact_mod_cast hn4
      have h := Real.sqrt_le_sqrt hn4r
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hp_half : p n ≤ 1 / 2 := by
      simp only [p, hn0, ↓reduceIte, one_div]
      exact inv_anti₀ zero_lt_two hsqrt2
    have hq_half : 1 / 2 ≤ 1 - p n := by linarith
    calc (n : ℝ) ^ 2 / 2 = (n : ℝ) ^ 2 * (1 / 2 : ℝ) := by ring
      _ ≤ (n : ℝ) ^ 2 * (1 - p n) := mul_le_mul_of_nonneg_left hq_half (sq_nonneg _)
  obtain ⟨_, hk_iff, hw_iff⟩ := Sec3_2_1_triangles_rucinski_proof hp
  exact ⟨hp, hw_iff.mpr ⟨hnp, hn2q⟩, hk_iff.mpr ⟨hnp, hn2q⟩⟩

end SteinMethod
