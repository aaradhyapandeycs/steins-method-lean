/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.WassersteinBound
import Formalization.ZeroBias.Coupling
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Lindeberg Condition and Zero-Bias Convergence (`Formalization.ZeroBias.Lindeberg`)

Proves the zero-bias Lindeberg–Feller equivalence and weak convergence theorems of Section 3.5.2 of
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:1553-1648`):

* `lindeberg_iff_tendstoInMeasure_zeroBias` (**Theorem 3.22**, `\label{thm82}`,
  `SteinIntro.tex:1577-1584`): the Lindeberg condition `(3.34)` (`\label{85}`) holds if and only if
  $X_{I_n, n}^z \xrightarrow{\mathbb{P}} 0$.
* `tendstoInMeasure_and_max_variance_tendsto_of_zeroBias` (`Sec3_5_2_zeroBias_imp_tendstoInMeasure`,
  `SteinIntro.tex:1585-1586, 1625-1646`): if $X_{I_n, n}^z \xrightarrow{\mathbb{P}} 0$, then
  $\max_i \sigma_{i,n}^2 \to 0$ and $X_{I_n, n} \xrightarrow{\mathbb{P}} 0$.
* `tendsto_stdNormalLaw_of_tendstoInMeasure_zeroBias` (**Theorem 3.23**, `\label{thm83}`,
  `SteinIntro.tex:1588-1590, 1608-1624`): if $X_{I_n, n}^z \xrightarrow{\mathbb{P}} 0$, then
  $W_n \xrightarrow{d} \mathcal{N}(0, 1)$.

Core row-level bounds are proved for arbitrary row-indexed probability spaces `(Ω n, Q n)` so that
`Formalization.ZeroBias.LindebergFeller` can apply them directly to an enlarged product space
without assuming pre-existing zero-bias or random-index variables on the base space.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Zero-Bias Tail Identity (`SteinIntro.tex:1591-1607`) -/

section TailSandwich

/-- Piecewise-linear antiderivative $f_\varepsilon(x) = \max(0, x - \varepsilon) +
\min(0, x + \varepsilon)$ of $\mathbf{1}_{|x| \ge \varepsilon}$ (`SteinIntro.tex:1591-1595`). -/
def zbTailFn (ε x : ℝ) : ℝ :=
  max 0 (x - ε) + min 0 (x + ε)

private lemma lipschitzWith_zbTailFn (ε : ℝ) : LipschitzWith 2 (zbTailFn ε) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [NNReal.coe_ofNat, Real.dist_eq, Real.dist_eq]
  have hmax : |max 0 (x - ε) - max 0 (y - ε)| ≤ |x - y| := by
    rcases le_total 0 (x - ε) with hx | hx <;> rcases le_total 0 (y - ε) with hy | hy
    · rw [max_eq_right hx, max_eq_right hy]; exact le_of_eq (by ring_nf)
    · rw [max_eq_right hx, max_eq_left hy, sub_zero, abs_of_nonneg hx]
      linarith [le_abs_self (x - y)]
    · rw [max_eq_left hx, max_eq_right hy, zero_sub, abs_neg, abs_of_nonneg hy]
      linarith [neg_le_abs (x - y)]
    · rw [max_eq_left hx, max_eq_left hy, sub_self, abs_zero]; exact abs_nonneg _
  have hmin : |min 0 (x + ε) - min 0 (y + ε)| ≤ |x - y| := by
    rcases le_total 0 (x + ε) with hx | hx <;> rcases le_total 0 (y + ε) with hy | hy
    · rw [min_eq_left hx, min_eq_left hy, sub_self, abs_zero]; exact abs_nonneg _
    · rw [min_eq_left hx, min_eq_right hy, zero_sub, abs_neg, abs_of_nonpos hy]
      linarith [le_abs_self (x - y)]
    · rw [min_eq_right hx, min_eq_left hy, sub_zero, abs_of_nonpos hx]
      linarith [neg_le_abs (x - y)]
    · rw [min_eq_right hx, min_eq_right hy]; exact le_of_eq (by ring_nf)
  have hsplit : zbTailFn ε x - zbTailFn ε y =
      (max 0 (x - ε) - max 0 (y - ε)) + (min 0 (x + ε) - min 0 (y + ε)) := by
    dsimp [zbTailFn]; ring
  rw [hsplit]
  linarith [abs_add_le (max 0 (x - ε) - max 0 (y - ε)) (min 0 (x + ε) - min 0 (y + ε))]

private lemma abs_zbTailFn_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : |zbTailFn ε x| ≤ 2 * |x| := by
  have h0 : zbTailFn ε 0 = 0 := by
    dsimp [zbTailFn]
    rw [max_eq_left (by linarith), min_eq_left (by linarith), add_zero]
  have hd := (lipschitzWith_zbTailFn ε).dist_le_mul x 0
  simpa [Real.dist_eq, h0] using hd

private lemma mul_zbTailFn_eq {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    x * zbTailFn ε x = (x ^ 2 - ε * |x|) * {t : ℝ | ε ≤ |t|}.indicator 1 x := by
  rcases le_or_gt ε x with hx | hx
  · have hm : x ∈ {t : ℝ | ε ≤ |t|} := hx.trans (le_abs_self x)
    dsimp [zbTailFn]
    rw [max_eq_right (by linarith), min_eq_left (by linarith), indicator_of_mem hm, Pi.one_apply,
      abs_of_pos (hε.trans_le hx)]
    ring
  · rcases le_or_gt x (-ε) with hx2 | hx2
    · have hm : x ∈ {t : ℝ | ε ≤ |t|} := by
        change ε ≤ |x|; rw [abs_of_neg (by linarith)]; linarith
      dsimp [zbTailFn]
      rw [max_eq_left (by linarith), min_eq_right (by linarith), indicator_of_mem hm, Pi.one_apply,
        abs_of_neg (by linarith)]
      ring
    · have hn : x ∉ {t : ℝ | ε ≤ |t|} := by
        change ¬ ε ≤ |x|; rw [not_le]; exact abs_lt.mpr ⟨hx2, hx⟩
      dsimp [zbTailFn]
      rw [max_eq_left (by linarith), min_eq_left (by linarith), indicator_of_notMem hn]
      ring

private lemma deriv_zbTailFn_of_ne {ε x : ℝ} (hε : 0 < ε) (h1 : x ≠ ε) (h2 : x ≠ -ε) :
    deriv (zbTailFn ε) x = {t : ℝ | ε ≤ |t|}.indicator 1 x := by
  rcases lt_trichotomy x ε with hxlt | rfl | hxgt
  · rcases lt_trichotomy x (-ε) with hxlt2 | rfl | hxgt2
    · have heq : zbTailFn ε =ᶠ[𝓝 x] fun t ↦ t + ε :=
        Filter.eventually_of_mem (Iio_mem_nhds hxlt2) fun t (ht : t < -ε) ↦ by
          dsimp [zbTailFn]
          rw [max_eq_left (by linarith), min_eq_right (by linarith), zero_add]
      have hd : HasDerivAt (zbTailFn ε) 1 x :=
        ((hasDerivAt_id' x).add_const ε).congr_of_eventuallyEq heq
      have hm : x ∈ {t : ℝ | ε ≤ |t|} := by
        change ε ≤ |x|; rw [abs_of_neg (by linarith)]; linarith
      rw [hd.deriv, indicator_of_mem hm, Pi.one_apply]
    · exact False.elim (h2 rfl)
    · have heq : zbTailFn ε =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
        Filter.eventually_of_mem (Ioo_mem_nhds hxgt2 hxlt) fun t ht ↦ by
          dsimp [zbTailFn]
          rw [max_eq_left (by linarith [ht.2]), min_eq_left (by linarith [ht.1]), add_zero]
      have hd : HasDerivAt (zbTailFn ε) 0 x := (hasDerivAt_const x 0).congr_of_eventuallyEq heq
      have hn : x ∉ {t : ℝ | ε ≤ |t|} := by
        change ¬ ε ≤ |x|; rw [not_le]; exact abs_lt.mpr ⟨hxgt2, hxlt⟩
      rw [hd.deriv, indicator_of_notMem hn]
  · exact False.elim (h1 rfl)
  · have heq : zbTailFn ε =ᶠ[𝓝 x] fun t ↦ t - ε :=
      Filter.eventually_of_mem (Ioi_mem_nhds hxgt) fun t (ht : ε < t) ↦ by
        dsimp [zbTailFn]
        rw [max_eq_right (by linarith), min_eq_left (by linarith), add_zero]
    have hd : HasDerivAt (zbTailFn ε) 1 x :=
      ((hasDerivAt_id' x).sub_const ε).congr_of_eventuallyEq heq
    have hm : x ∈ {t : ℝ | ε ≤ |t|} := hxgt.le.trans (le_abs_self x)
    rw [hd.deriv, indicator_of_mem hm, Pi.one_apply]

/-- Single-summand zero-bias tail identity (`SteinIntro.tex:1592-1595`):
$\mathbb{E}[(X^2 - \varepsilon |X|)\mathbf{1}_{|X| \ge \varepsilon}] =
\operatorname{Var}(X)\,\mathbb{P}(|X^z| \ge \varepsilon)$. -/
theorem zeroBias_tail_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : Ω → ℝ} (hXz_meas : Measurable Xz) (hZB : IsZeroBias P X P Xz)
    {ε : ℝ} (hε : 0 < ε) :
    ∫ ω, ((X ω) ^ 2 - ε * |X ω|) * {t : ℝ | ε ≤ |t|}.indicator 1 (X ω) ∂P =
      ProbabilityTheory.variance X P * P.real {ω | ε ≤ |Xz ω|} := by
  rcases (ProbabilityTheory.variance_nonneg X P).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    have hX0 : X =ᵐ[P] fun _ ↦ (0 : ℝ) := by
      filter_upwards [ProbabilityTheory.ae_eq_integral_of_variance_eq_zero hZB.1 h0.symm] with ω hω
      simpa [hZB.2.1] using hω
    refine integral_eq_zero_of_ae (hX0.mono fun ω hω ↦ ?_)
    dsimp only at hω ⊢
    simp [hω]
  · have hmap := (zeroBias_law_characterization (Ω' := Ω) P hZB.1 hZB.2.1 hpos).2.1 P hZB
    have hac : P.map Xz ≪ volume := by
      rw [hmap]; exact withDensity_absolutelyContinuous _ _
    have hpair_meas : MeasurableSet ({-ε, ε} : Set ℝ) :=
      (measurableSet_singleton (-ε)).union (measurableSet_singleton ε)
    have hvol0 : volume ({-ε, ε} : Set ℝ) = 0 :=
      measure_union_null Real.volume_singleton Real.volume_singleton
    have hP0 : P (Xz ⁻¹' ({-ε, ε} : Set ℝ)) = 0 := by
      rw [← Measure.map_apply hXz_meas hpair_meas]
      exact hac hvol0
    have hae_ne : ∀ᵐ ω ∂P, Xz ω ≠ ε ∧ Xz ω ≠ -ε := by
      rw [ae_iff]
      refine measure_mono_null (fun ω hω ↦ ?_) hP0
      by_cases h1 : Xz ω = ε
      · exact Or.inr h1
      · by_cases h2 : Xz ω = -ε
        · exact Or.inl h2
        · exact False.elim (hω ⟨h1, h2⟩)
    have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval (zbTailFn ε) a b := fun a b ↦
      (lipschitzWith_zbTailFn ε).lipschitzOnWith.absolutelyContinuousOnInterval
    have hXf_int : Integrable (fun ω ↦ X ω * zbTailFn ε (X ω)) P := by
      refine (hZB.1.integrable_sq.const_mul 2).mono'
        (hZB.1.aestronglyMeasurable.mul
          ((lipschitzWith_zbTailFn ε).continuous.measurable.comp_aemeasurable
            hZB.1.aemeasurable).aestronglyMeasurable)
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := mul_le_mul_of_nonneg_left (abs_zbTailFn_le hε (X ω)) (abs_nonneg (X ω))
      nlinarith [sq_abs (X ω)]
    have hs_meas : MeasurableSet {t : ℝ | ε ≤ |t|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have hset_meas : MeasurableSet {ω : Ω | ε ≤ |Xz ω|} := hs_meas.preimage hXz_meas
    have hind_int : Integrable (fun ω ↦ {t : ℝ | ε ≤ |t|}.indicator (1 : ℝ → ℝ) (Xz ω)) P := by
      have heq : (fun ω ↦ {t : ℝ | ε ≤ |t|}.indicator (1 : ℝ → ℝ) (Xz ω)) =
          {ω : Ω | ε ≤ |Xz ω|}.indicator 1 := by
        ext ω; by_cases hω : ε ≤ |Xz ω| <;> simp [hω]
      rw [heq]
      exact (integrable_const (1 : ℝ)).indicator hset_meas
    have hae_deriv : (fun ω ↦ deriv (zbTailFn ε) (Xz ω)) =ᵐ[P]
        fun ω ↦ {t : ℝ | ε ≤ |t|}.indicator 1 (Xz ω) :=
      hae_ne.mono fun ω hω ↦ deriv_zbTailFn_of_ne hε hω.1 hω.2
    have hdf_int : Integrable (fun ω ↦ deriv (zbTailFn ε) (Xz ω)) P :=
      hind_int.congr hae_deriv.symm
    have hzb := hZB.2.2.2 (zbTailFn ε) hf_ac hXf_int hdf_int
    simp_rw [mul_zbTailFn_eq hε] at hzb
    rw [hzb, integral_congr_ae hae_deriv]
    congr 1
    have heq : (fun ω ↦ {t : ℝ | ε ≤ |t|}.indicator (1 : ℝ → ℝ) (Xz ω)) =
        {ω : Ω | ε ≤ |Xz ω|}.indicator 1 := by
      ext ω; by_cases hω : ε ≤ |Xz ω| <;> simp [hω]
    rw [heq, integral_indicator_one hset_meas]

/-- Random-index tail decomposition: when $I$ is independent of $(Y_i)_i$ with
$\mathbb{P}(I = i) = \sigma_i^2$, $\mathbb{P}(Y_I \in s) = \sum_i \sigma_i^2 \mathbb{P}(Y_i \in s)$
(`SteinIntro.tex:1597-1599`). -/
private lemma measureReal_randomIndex_eq_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} {Y : Fin k → Ω → ℝ} {I : Ω → Fin k} {σ2 : Fin k → ℝ}
    (hY_meas : ∀ i : Fin k, Measurable (Y i))
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin k, P.real (I ⁻¹' {i}) = σ2 i)
    (hI_indep : IndepFun I (fun ω i ↦ Y i ω) P)
    {s : Set ℝ} (hs : MeasurableSet s) :
    P.real {ω | Y (I ω) ω ∈ s} = ∑ i : Fin k, σ2 i * P.real {ω | Y i ω ∈ s} := by
  let A : Set Ω := {ω | Y (I ω) ω ∈ s}
  have hA_eq : A = ⋃ i : Fin k, (I ⁻¹' {i}) ∩ (Y i ⁻¹' s) := by
    ext ω; simp [A]
  have hA_meas : MeasurableSet A := by
    rw [hA_eq]
    exact MeasurableSet.iUnion fun i ↦
      (hI_meas (measurableSet_singleton i)).inter (hs.preimage (hY_meas i))
  have hind_sum : A.indicator (1 : Ω → ℝ) =
      fun ω ↦ ∑ i : Fin k, (I ⁻¹' {i}).indicator 1 ω * (Y i ⁻¹' s).indicator 1 ω := by
    ext ω
    symm
    rw [Finset.sum_eq_single (I ω)]
    · by_cases hω : Y (I ω) ω ∈ s
      · have hmA : ω ∈ A := hω
        have hmY : ω ∈ Y (I ω) ⁻¹' s := hω
        simp [hmA, hmY]
      · have hnA : ω ∉ A := hω
        have hnY : ω ∉ Y (I ω) ⁻¹' s := hω
        simp [hnA, hnY]
    · intro i _ hi
      have hnot : ω ∉ I ⁻¹' {i} := fun h ↦ hi h.symm
      simp [hnot]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  have hterm : ∀ i : Fin k,
      Integrable (fun ω ↦ (I ⁻¹' {i}).indicator (1 : Ω → ℝ) ω * (Y i ⁻¹' s).indicator 1 ω) P ∧
        ∫ ω, (I ⁻¹' {i}).indicator (1 : Ω → ℝ) ω * (Y i ⁻¹' s).indicator 1 ω ∂P =
          σ2 i * P.real {ω | Y i ω ∈ s} := fun i ↦ by
    let f1 : Fin k → ℝ := ({i} : Set (Fin k)).indicator 1
    let f2 : (Fin k → ℝ) → ℝ := fun v ↦ s.indicator 1 (v i)
    have hf1 : Measurable f1 := measurable_one.indicator (measurableSet_singleton i)
    have hf2 : Measurable f2 := (measurable_one.indicator hs).comp (measurable_pi_apply i)
    have hindep_i : IndepFun (f1 ∘ I) (f2 ∘ fun ω j ↦ Y j ω) P := hI_indep.comp hf1 hf2
    have he1 : f1 ∘ I = (I ⁻¹' {i}).indicator (1 : Ω → ℝ) := by
      ext ω; by_cases hω : I ω = i <;> simp [f1, hω]
    have he2 : (f2 ∘ fun ω j ↦ Y j ω) = (Y i ⁻¹' s).indicator (1 : Ω → ℝ) := by
      ext ω; by_cases hω : Y i ω ∈ s <;> simp [f2, hω]
    rw [he1, he2] at hindep_i
    have h1_int : Integrable ((I ⁻¹' {i}).indicator (1 : Ω → ℝ)) P :=
      (integrable_const (1 : ℝ)).indicator (hI_meas (measurableSet_singleton i))
    have h2_int : Integrable ((Y i ⁻¹' s).indicator (1 : Ω → ℝ)) P :=
      (integrable_const (1 : ℝ)).indicator (hs.preimage (hY_meas i))
    have hprod_int : Integrable
        (fun ω ↦ (I ⁻¹' {i}).indicator (1 : Ω → ℝ) ω * (Y i ⁻¹' s).indicator 1 ω) P := by
      refine (integrable_const (1 : ℝ)).mono'
        (h1_int.aestronglyMeasurable.mul h2_int.aestronglyMeasurable)
        (ae_of_all _ fun ω ↦ ?_)
      by_cases h1 : ω ∈ I ⁻¹' {i} <;> by_cases h2 : ω ∈ Y i ⁻¹' s <;> simp [h1, h2]
    refine ⟨hprod_int, ?_⟩
    rw [hindep_i.integral_fun_mul_eq_mul_integral h1_int.aestronglyMeasurable
      h2_int.aestronglyMeasurable,
      integral_indicator_one (hI_meas (measurableSet_singleton i)),
      integral_indicator_one (hs.preimage (hY_meas i)), hI_prob i]
    rfl
  rw [← integral_indicator_one hA_meas, hind_sum,
    integral_finsetSum Finset.univ fun i _ ↦ (hterm i).1]
  exact Finset.sum_congr rfl fun i _ ↦ (hterm i).2

/-- Two-sided Lindeberg sandwich for $\mathbb{P}(|X_I^z| \ge \varepsilon)$
(`SteinIntro.tex:1597-1607`):
- $\mathbb{P}(|X_I^z| \ge \varepsilon) \le L(\varepsilon / 2)$, and
- $L(2\varepsilon) \le 2\,\mathbb{P}(|X_I^z| \ge \varepsilon)$,
where $L(\delta) = \sum_i \mathbb{E}[X_i^2 \mathbf{1}_{|X_i| > \delta}]$ (`(3.34)` `\label{85}`). -/
theorem zeroBias_randomIndex_tail_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} {X Xz : Fin k → Ω → ℝ} {I : Ω → Fin k}
    (hX_meas : ∀ i : Fin k, Measurable (X i))
    (hXz_meas : ∀ i : Fin k, Measurable (Xz i))
    (hX_L2 : ∀ i : Fin k, MemLp (X i) 2 P)
    (hXz : ∀ i : Fin k, IsZeroBias P (X i) P (Xz i))
    (hI_meas : Measurable I)
    (hI_prob : ∀ i : Fin k, P.real (I ⁻¹' {i}) = ProbabilityTheory.variance (X i) P)
    (hI_indep : IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xz i ω)) P)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |Xz (I ω) ω|} ≤
        ∑ i : Fin k, ∫ ω, (X i ω) ^ 2 * {x : ℝ | ε / 2 < |x|}.indicator 1 (X i ω) ∂P ∧
      (∑ i : Fin k, ∫ ω, (X i ω) ^ 2 * {x : ℝ | 2 * ε < |x|}.indicator 1 (X i ω) ∂P) ≤
        2 * P.real {ω | ε ≤ |Xz (I ω) ω|} := by
  have hI_Xz : IndepFun I (fun ω i ↦ Xz i ω) P := hI_indep.comp measurable_id measurable_snd
  have hs_ge : MeasurableSet {x : ℝ | ε ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hprob_eq : P.real {ω | ε ≤ |Xz (I ω) ω|} =
      ∑ i : Fin k,
        ∫ ω, ((X i ω) ^ 2 - ε * |X i ω|) * {x : ℝ | ε ≤ |x|}.indicator 1 (X i ω) ∂P :=
    (measureReal_randomIndex_eq_sum P hXz_meas hI_meas hI_prob hI_Xz hs_ge).trans
      (Finset.sum_congr rfl fun i _ ↦ (zeroBias_tail_identity P (hXz_meas i) (hXz i) hε).symm)
  have hsub_int : ∀ i : Fin k,
      Integrable (fun ω ↦ ((X i ω) ^ 2 - ε * |X i ω|) * {x : ℝ | ε ≤ |x|}.indicator 1 (X i ω)) P :=
    fun i ↦ by
      refine (hX_L2 i).integrable_sq.mono'
        ((((hX_meas i).pow_const 2).sub
          (continuous_abs.measurable.comp (hX_meas i) |>.const_mul ε)).mul
          ((measurable_one.indicator hs_ge).comp (hX_meas i))).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      by_cases hx : ε ≤ |X i ω|
      · have hm : X i ω ∈ {x : ℝ | ε ≤ |x|} := hx
        have hnn : 0 ≤ (X i ω) ^ 2 - ε * |X i ω| := by
          have := mul_le_mul_of_nonneg_right hx (abs_nonneg (X i ω))
          nlinarith [sq_abs (X i ω)]
        rw [indicator_of_mem hm, Pi.one_apply, mul_one, Real.norm_eq_abs, abs_of_nonneg hnn]
        nlinarith [abs_nonneg (X i ω)]
      · have hn : X i ω ∉ {x : ℝ | ε ≤ |x|} := hx
        simp [hn, sq_nonneg]
  have hlind_int : ∀ (δ : ℝ) (i : Fin k),
      Integrable (fun ω ↦ (X i ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X i ω)) P := fun δ i ↦ by
    have hs_gt : MeasurableSet {x : ℝ | δ < |x|} :=
      measurableSet_lt measurable_const continuous_abs.measurable
    refine (hX_L2 i).integrable_sq.mono'
      (((hX_meas i).pow_const 2).mul
        ((measurable_one.indicator hs_gt).comp (hX_meas i))).aestronglyMeasurable
      (ae_of_all _ fun ω ↦ ?_)
    by_cases hx : δ < |X i ω|
    · have hm : X i ω ∈ {x : ℝ | δ < |x|} := hx
      rw [indicator_of_mem hm, Pi.one_apply, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
    · have hn : X i ω ∉ {x : ℝ | δ < |x|} := hx
      simp [hn, sq_nonneg]
  rw [hprob_eq]
  refine ⟨Finset.sum_le_sum fun i _ ↦ integral_mono (hsub_int i) (hlind_int (ε / 2) i) fun ω ↦ ?_,
    ?_⟩
  · by_cases hx : ε ≤ |X i ω|
    · have hm1 : X i ω ∈ {x : ℝ | ε ≤ |x|} := hx
      have hm2 : X i ω ∈ {x : ℝ | ε / 2 < |x|} := by change ε / 2 < |X i ω|; linarith
      rw [indicator_of_mem hm1, indicator_of_mem hm2, Pi.one_apply, mul_one, mul_one]
      nlinarith [abs_nonneg (X i ω)]
    · have hn1 : X i ω ∉ {x : ℝ | ε ≤ |x|} := hx
      rw [indicator_of_notMem hn1, mul_zero]
      exact mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [← integral_const_mul]
    refine integral_mono (hlind_int (2 * ε) i) ((hsub_int i).const_mul 2) fun ω ↦ ?_
    dsimp only
    by_cases hx : 2 * ε < |X i ω|
    · have hm2 : X i ω ∈ {x : ℝ | 2 * ε < |x|} := hx
      have hm1 : X i ω ∈ {x : ℝ | ε ≤ |x|} := by change ε ≤ |X i ω|; linarith
      rw [indicator_of_mem hm2, indicator_of_mem hm1, Pi.one_apply, mul_one, mul_one]
      have hmul := mul_le_mul_of_nonneg_right hx.le (abs_nonneg (X i ω))
      nlinarith [sq_abs (X i ω)]
    · have hn2 : X i ω ∉ {x : ℝ | 2 * ε < |x|} := hx
      rw [indicator_of_notMem hn2, mul_zero]
      by_cases hx1 : ε ≤ |X i ω|
      · have hm1 : X i ω ∈ {x : ℝ | ε ≤ |x|} := hx1
        rw [indicator_of_mem hm1, Pi.one_apply, mul_one]
        have hmul := mul_le_mul_of_nonneg_right hx1 (abs_nonneg (X i ω))
        nlinarith [sq_abs (X i ω)]
      · have hn1 : X i ω ∉ {x : ℝ | ε ≤ |x|} := hx1
        simp [hn1]

end TailSandwich

/-! ### Section 2: Row-Indexed Lindeberg Equivalence and Weak Convergence -/

section RowIndexed

/-- Row-indexed equivalence between the Lindeberg condition `(3.34)` and convergence in probability
of $X_{I_n, n}^z$ to $0$ (`SteinIntro.tex:1577-1607`). -/
theorem lindeberg_iff_row_zeroBias_tail_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Q n)]
    {X Xz : ∀ n, Fin (n + 1) → Ω n → ℝ} {I : ∀ n, Ω n → Fin (n + 1)}
    (hX_meas : ∀ n i, Measurable (X n i))
    (hXz_meas : ∀ n i, Measurable (Xz n i))
    (hX_L2 : ∀ n i, MemLp (X n i) 2 (Q n))
    (hXz : ∀ n i, IsZeroBias (Q n) (X n i) (Q n) (Xz n i))
    (hI_meas : ∀ n, Measurable (I n))
    (hI_prob : ∀ n i, (Q n).real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) (Q n))
    (hI_indep : ∀ n, IndepFun (I n) (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) (Q n)) :
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ ∑ i : Fin (n + 1),
        ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂(Q n))
        atTop (𝓝 0)) ↔
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ (Q n).real {ω | ε ≤ |Xz n (I n ω) ω|}) atTop (𝓝 0)) := by
  constructor
  · intro hLind ε hε
    refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) (hLind (ε / 2) (half_pos hε))
    exact (zeroBias_randomIndex_tail_sandwich (Q n) (hX_meas n) (hXz_meas n) (hX_L2 n) (hXz n)
      (hI_meas n) (hI_prob n) (hI_indep n) hε).1
  · intro hTail ε hε
    have hnn : ∀ n : ℕ, 0 ≤ ∑ i : Fin (n + 1),
        ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂(Q n) := fun n ↦
      Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦
        mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    have h2 : Tendsto (fun n : ℕ ↦ 2 * (Q n).real {ω | ε / 2 ≤ |Xz n (I n ω) ω|}) atTop (𝓝 0) := by
      simpa using (hTail (ε / 2) (half_pos hε)).const_mul 2
    refine squeeze_zero hnn (fun n ↦ ?_) h2
    have hsand := (zeroBias_randomIndex_tail_sandwich (Q n) (hX_meas n) (hXz_meas n) (hX_L2 n)
      (hXz n) (hI_meas n) (hI_prob n) (hI_indep n) (half_pos hε)).2
    have h2ε : 2 * (ε / 2) = ε := by ring
    rwa [h2ε] at hsand

/-- Row-indexed derivation of $\max_i \sigma_{i,n}^2 \to 0$ and $\mathbb{P}(|X_{I_n, n}| \ge
\varepsilon) \to 0$ from $\mathbb{P}(|X_{I_n, n}^z| \ge \varepsilon) \to 0$
(`SteinIntro.tex:1585-1586, 1625-1646`). -/
theorem row_max_variance_and_summand_tail_tendsto_of_zeroBias
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Q n)]
    {X Xz : ∀ n, Fin (n + 1) → Ω n → ℝ} {I : ∀ n, Ω n → Fin (n + 1)}
    (hX_meas : ∀ n i, Measurable (X n i))
    (hXz_meas : ∀ n i, Measurable (Xz n i))
    (hX_L2 : ∀ n i, MemLp (X n i) 2 (Q n))
    (hX_mean : ∀ n i, ∫ ω, X n i ω ∂(Q n) = 0)
    (hVar_sum : ∀ n, (∑ i : Fin (n + 1), ProbabilityTheory.variance (X n i) (Q n)) = 1)
    (hXz : ∀ n i, IsZeroBias (Q n) (X n i) (Q n) (Xz n i))
    (hI_meas : ∀ n, Measurable (I n))
    (hI_prob : ∀ n i, (Q n).real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) (Q n))
    (hI_indep : ∀ n, IndepFun (I n) (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) (Q n))
    (hTail_Xz : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ (Q n).real {ω | ε ≤ |Xz n (I n ω) ω|}) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ Finset.univ.sup' Finset.univ_nonempty
        fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) (Q n))
      atTop (𝓝 0) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ (Q n).real {ω | ε ≤ |X n (I n ω) ω|}) atTop (𝓝 0)) := by
  have hLind := (lindeberg_iff_row_zeroBias_tail_tendsto Q hX_meas hXz_meas hX_L2 hXz hI_meas
    hI_prob hI_indep).mpr hTail_Xz
  have hmax_tend : Tendsto (fun n : ℕ ↦ Finset.univ.sup' Finset.univ_nonempty
      fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) (Q n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    let δ : ℝ := Real.sqrt (η / 2)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (half_pos hη)
    have hδ_sq : δ ^ 2 = η / 2 := Real.sq_sqrt (half_pos hη).le
    have hev := (Metric.tendsto_nhds.mp (hLind δ hδ)) (η / 2) (half_pos hη)
    filter_upwards [hev] with n hn
    have hsup_nn : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) (Q n) :=
      le_trans (ProbabilityTheory.variance_nonneg (X n 0) (Q n))
        (Finset.le_sup' (fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) (Q n))
          (Finset.mem_univ 0))
    have hsup_le : Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) (Q n)) ≤
        δ ^ 2 + ∑ j : Fin (n + 1),
          ∫ ω, (X n j ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n j ω) ∂(Q n) := by
      refine Finset.sup'_le Finset.univ_nonempty _ fun i _ ↦ ?_
      have hvar_eq : ProbabilityTheory.variance (X n i) (Q n) = ∫ ω, (X n i ω) ^ 2 ∂(Q n) :=
        ProbabilityTheory.variance_of_integral_eq_zero (hX_meas n i).aemeasurable (hX_mean n i)
      have hs_gt : MeasurableSet {x : ℝ | δ < |x|} :=
        measurableSet_lt measurable_const continuous_abs.measurable
      have hl_int : Integrable (fun ω ↦ (X n i ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n i ω))
          (Q n) := by
        refine (hX_L2 n i).integrable_sq.mono'
          (((hX_meas n i).pow_const 2).mul
            ((measurable_one.indicator hs_gt).comp (hX_meas n i))).aestronglyMeasurable
          (ae_of_all _ fun ω ↦ ?_)
        by_cases hx : δ < |X n i ω|
        · have hm : X n i ω ∈ {x : ℝ | δ < |x|} := hx
          rw [indicator_of_mem hm, Pi.one_apply, mul_one, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg _)]
        · have hn' : X n i ω ∉ {x : ℝ | δ < |x|} := hx
          simp [hn', sq_nonneg]
      have hi_le : ProbabilityTheory.variance (X n i) (Q n) ≤
          δ ^ 2 + ∫ ω, (X n i ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n i ω) ∂(Q n) := by
        rw [hvar_eq]
        have hpt : ∀ ω : Ω n, (X n i ω) ^ 2 ≤
            δ ^ 2 + (X n i ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n i ω) := fun ω ↦ by
          by_cases hx : δ < |X n i ω|
          · have hm : X n i ω ∈ {x : ℝ | δ < |x|} := hx
            rw [indicator_of_mem hm, Pi.one_apply, mul_one]
            linarith [sq_nonneg δ]
          · have hn' : X n i ω ∉ {x : ℝ | δ < |x|} := hx
            rw [indicator_of_notMem hn', mul_zero, add_zero]
            have hle : |X n i ω| ≤ δ := not_lt.mp hx
            exact sq_le_sq.mpr (by rwa [abs_of_pos hδ])
        calc
          ∫ ω, (X n i ω) ^ 2 ∂(Q n)
            ≤ ∫ ω, (δ ^ 2 + (X n i ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n i ω)) ∂(Q n) :=
              integral_mono (hX_L2 n i).integrable_sq ((integrable_const _).add hl_int) hpt
          _ = δ ^ 2 + ∫ ω, (X n i ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n i ω) ∂(Q n) := by
              rw [integral_add (integrable_const _) hl_int, integral_const, probReal_univ, one_smul]
      have hsingle : ∫ ω, (X n i ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n i ω) ∂(Q n) ≤
          ∑ j : Fin (n + 1),
            ∫ ω, (X n j ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n j ω) ∂(Q n) :=
        Finset.single_le_sum
          (f := fun j : Fin (n + 1) ↦
            ∫ ω, (X n j ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n j ω) ∂(Q n))
          (fun j _ ↦ integral_nonneg fun ω ↦
            mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _))
          (Finset.mem_univ i)
      exact hi_le.trans (add_le_add (le_refl (δ ^ 2)) hsingle)
    rw [Real.dist_eq, sub_zero] at hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsup_nn]
    linarith [le_abs_self (∑ j : Fin (n + 1),
      ∫ ω, (X n j ω) ^ 2 * {x : ℝ | δ < |x|}.indicator 1 (X n j ω) ∂(Q n))]
  refine ⟨hmax_tend, fun ε hε ↦ ?_⟩
  have hscaled : Tendsto (fun n : ℕ ↦ (ε ^ 2)⁻¹ * Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) (Q n))) atTop (𝓝 0) := by
    simpa using hmax_tend.const_mul (ε ^ 2)⁻¹
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun n ↦ ?_) hscaled
  have hI_X : IndepFun (I n) (fun ω i ↦ X n i ω) (Q n) :=
    (hI_indep n).comp measurable_id measurable_fst
  have hs_ge : MeasurableSet {x : ℝ | ε ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  change (Q n).real {ω | X n (I n ω) ω ∈ {x : ℝ | ε ≤ |x|}} ≤ _
  rw [measureReal_randomIndex_eq_sum (Q n) (hX_meas n) (hI_meas n) (hI_prob n) hI_X hs_ge]
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) (Q n))
  have hcheb : ∀ i : Fin (n + 1),
      (Q n).real {ω | ε ≤ |X n i ω|} ≤
        (ε ^ 2)⁻¹ * ProbabilityTheory.variance (X n i) (Q n) := fun i ↦ by
    have hset_meas : MeasurableSet {ω : Ω n | ε ≤ |X n i ω|} := hs_ge.preimage (hX_meas n i)
    have hvar_eq : ProbabilityTheory.variance (X n i) (Q n) = ∫ ω, (X n i ω) ^ 2 ∂(Q n) :=
      ProbabilityTheory.variance_of_integral_eq_zero (hX_meas n i).aemeasurable (hX_mean n i)
    have hle : ε ^ 2 * (Q n).real {ω | ε ≤ |X n i ω|} ≤
        ProbabilityTheory.variance (X n i) (Q n) := by
      rw [hvar_eq, ← integral_indicator_one hset_meas, ← integral_const_mul]
      refine integral_mono (((integrable_const (1 : ℝ)).indicator hset_meas).const_mul (ε ^ 2))
        (hX_L2 n i).integrable_sq fun ω ↦ ?_
      dsimp only
      by_cases hω : ε ≤ |X n i ω|
      · have hm : ω ∈ {ω' : Ω n | ε ≤ |X n i ω'|} := hω
        rw [indicator_of_mem hm, Pi.one_apply, mul_one]
        nlinarith [sq_abs (X n i ω)]
      · have hn' : ω ∉ {ω' : Ω n | ε ≤ |X n i ω'|} := hω
        rw [indicator_of_notMem hn', mul_zero]
        exact sq_nonneg _
    calc
      (Q n).real {ω | ε ≤ |X n i ω|}
        = (ε ^ 2)⁻¹ * (ε ^ 2 * (Q n).real {ω | ε ≤ |X n i ω|}) := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hε.ne'), one_mul]
      _ ≤ (ε ^ 2)⁻¹ * ProbabilityTheory.variance (X n i) (Q n) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (sq_nonneg _))
  calc
    (∑ i : Fin (n + 1),
        ProbabilityTheory.variance (X n i) (Q n) * (Q n).real {ω | ε ≤ |X n i ω|})
      ≤ ∑ i : Fin (n + 1), M * (Q n).real {ω | ε ≤ |X n i ω|} :=
        Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right
          (Finset.le_sup' (fun j : Fin (n + 1) ↦ ProbabilityTheory.variance (X n j) (Q n))
            (Finset.mem_univ i))
          measureReal_nonneg
    _ = M * ∑ i : Fin (n + 1), (Q n).real {ω | ε ≤ |X n i ω|} := (Finset.mul_sum _ _ _).symm
    _ ≤ M * ∑ i : Fin (n + 1), (ε ^ 2)⁻¹ * ProbabilityTheory.variance (X n i) (Q n) := by
        have hM_nn : 0 ≤ M := le_trans (ProbabilityTheory.variance_nonneg (X n 0) (Q n))
          (Finset.le_sup' (fun j : Fin (n + 1) ↦ ProbabilityTheory.variance (X n j) (Q n))
            (Finset.mem_univ 0))
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hcheb i) hM_nn
    _ = (ε ^ 2)⁻¹ * M := by
        rw [← Finset.mul_sum, hVar_sum n, mul_one, mul_comm]

/-- Row-indexed weak convergence $W_n \xrightarrow{d} \mathcal{N}(0, 1)$ from
$\mathbb{P}(|X_{I_n, n}^z| \ge \varepsilon) \to 0$ (`SteinIntro.tex:1588-1590, 1608-1624`). -/
theorem row_tendsto_stdNormalLaw_of_zeroBias_tail_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Q n)]
    {X Xz : ∀ n, Fin (n + 1) → Ω n → ℝ} {I : ∀ n, Ω n → Fin (n + 1)}
    (hX_meas : ∀ n i, Measurable (X n i))
    (hXz_meas : ∀ n i, Measurable (Xz n i))
    (hX_indep : ∀ n, iIndepFun (X n) (Q n))
    (hX_L2 : ∀ n i, MemLp (X n i) 2 (Q n))
    (hX_mean : ∀ n i, ∫ ω, X n i ω ∂(Q n) = 0)
    (hVar_sum : ∀ n, (∑ i : Fin (n + 1), ProbabilityTheory.variance (X n i) (Q n)) = 1)
    (hXz : ∀ n i, IsZeroBias (Q n) (X n i) (Q n) (Xz n i))
    (hXz_indep : ∀ n i,
      IndepFun (Xz n i) (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) (Q n))
    (hI_meas : ∀ n, Measurable (I n))
    (hI_prob : ∀ n i, (Q n).real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) (Q n))
    (hI_indep : ∀ n, IndepFun (I n) (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) (Q n))
    (hTail_Xz : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ ↦ (Q n).real {ω | ε ≤ |Xz n (I n ω) ω|}) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((Q n).map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      atTop (𝓝 stdNormalLaw.toProbabilityMeasure) := by
  have hTail_X := (row_max_variance_and_summand_tail_tendsto_of_zeroBias Q hX_meas hXz_meas hX_L2
    hX_mean hVar_sum hXz hI_meas hI_prob hI_indep hTail_Xz).2
  let W : ∀ n, Ω n → ℝ := fun n ω ↦ ∑ i : Fin (n + 1), X n i ω
  let Wz : ∀ n, Ω n → ℝ :=
    fun n ω ↦ (∑ j ∈ Finset.univ.erase (I n ω), X n j ω) + Xz n (I n ω) ω
  have hW_meas : ∀ n, Measurable (W n) := fun n ↦
    Finset.measurable_fun_sum Finset.univ fun i _ ↦ hX_meas n i
  have hZB_W : ∀ n, IsZeroBias (Q n) (W n) (Q n) (Wz n) := fun n ↦
    zeroBias_sum_of_iIndepFun (Q n) (hX_meas n) (hXz_meas n) (hX_indep n) (hX_L2 n) (hX_mean n)
      (hVar_sum n) (hXz n) (hXz_indep n) (hI_meas n) (hI_prob n) (hI_indep n)
  have hVar_W : ∀ n, ProbabilityTheory.variance (W n) (Q n) = 1 := fun n ↦ by
    have hfn : W n = ∑ i ∈ Finset.univ, X n i := by ext ω; simp [W]
    rw [hfn, IndepFun.variance_sum (fun i _ ↦ hX_L2 n i)
      (fun i _ j _ hij ↦ (hX_indep n).indepFun hij), hVar_sum n]
  have hdW_bound : ∀ (n : ℕ) {η : ℝ}, 0 < η →
      wassersteinDist ((Q n).map (W n)) stdNormalLaw ≤
        ENNReal.ofReal (2 * η + 2 * Real.sqrt (2 / Real.pi) *
          ((Q n).real {ω | η / 2 ≤ |Xz n (I n ω) ω|} +
            (Q n).real {ω | η / 2 ≤ |X n (I n ω) ω|})) := by
    intro n η hη
    have h1 := wassersteinDist_map_stdNormal_le_iSup_normalSteinOp (Q n) stdNormalLaw
      (hW_meas n).aemeasurable aemeasurable_id Measure.map_id
    rw [Measure.map_id] at h1
    refine h1.trans (iSup₂_le fun f hf ↦ ?_)
    rcases hf with ⟨hf_diff, hdf_diff, hf_bdd, hdf_bdd, hddf_bdd⟩
    have hf_ac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b := fun a b ↦
      (contDiff_one_iff_deriv.mpr ⟨hf_diff, hdf_diff.continuous⟩).contDiffOn
        |>.absolutelyContinuousOnInterval
    have hW_int : Integrable (W n) (Q n) := (hZB_W n).1.integrable one_le_two
    have hWf_int : Integrable (fun ω ↦ W n ω * f (W n ω)) (Q n) := by
      refine (hW_int.norm.mul_const 2).mono'
        ((hW_meas n).mul (hf_diff.continuous.measurable.comp (hW_meas n))).aestronglyMeasurable
        (ae_of_all _ fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hf_bdd (W n ω)) (abs_nonneg (W n ω))
    have hdfW_int : Integrable (fun ω ↦ deriv f (W n ω)) (Q n) :=
      Integrable.of_bound
        (hdf_diff.continuous.measurable.comp (hW_meas n)).aestronglyMeasurable
        (Real.sqrt (2 / Real.pi))
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd (W n ω))
    have hdfWz_int : Integrable (fun ω ↦ deriv f (Wz n ω)) (Q n) :=
      Integrable.of_bound
        (hdf_diff.continuous.measurable.comp_aemeasurable (hZB_W n).2.2.1).aestronglyMeasurable
        (Real.sqrt (2 / Real.pi))
        (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd (Wz n ω))
    have hstein : ∫ ω, normalSteinOp f (W n ω) ∂(Q n) =
        ∫ ω, (deriv f (W n ω) - deriv f (Wz n ω)) ∂(Q n) := by
      unfold normalSteinOp
      rw [integral_sub hdfW_int hWf_int, (hZB_W n).2.2.2 f hf_ac hWf_int hdfWz_int,
        hVar_W n, one_mul, integral_sub hdfW_int hdfWz_int]
    have hlip : ∀ x y : ℝ, |deriv f x - deriv f y| ≤ 2 * |y - x| := fun x y ↦ by
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
        (fun z _ ↦ hdf_diff z) (fun z _ ↦ by rw [Real.norm_eq_abs]; exact hddf_bdd z)
        convex_univ (mem_univ y) (mem_univ x)
      simpa [Real.norm_eq_abs, abs_sub_comm] using hmvt
    have hdiff_eq : ∀ ω : Ω n, Wz n ω - W n ω = Xz n (I n ω) ω - X n (I n ω) ω := fun ω ↦ by
      dsimp [Wz, W]
      have herase := Finset.sum_erase_add Finset.univ (fun j ↦ X n j ω) (Finset.mem_univ (I n ω))
      linarith
    let U : Set (Ω n) := {ω | η / 2 ≤ |Xz n (I n ω) ω|} ∪ {ω | η / 2 ≤ |X n (I n ω) ω|}
    have hY_meas : ∀ Y : Fin (n + 1) → Ω n → ℝ, (∀ i, Measurable (Y i)) →
        Measurable (fun ω ↦ Y (I n ω) ω) := fun Y hY ↦ by
      have heq : (fun ω ↦ Y (I n ω) ω) =
          fun ω ↦ ∑ i : Fin (n + 1), (I n ⁻¹' {i}).indicator (Y i) ω := by
        ext ω; symm; rw [Finset.sum_eq_single (I n ω)]
        · simp
        · intro i _ hi; simp [show ω ∉ I n ⁻¹' {i} from fun h ↦ hi h.symm]
        · intro h; exact False.elim (h (Finset.mem_univ _))
      rw [heq]
      exact Finset.measurable_fun_sum Finset.univ fun i _ ↦
        (hY i).indicator (hI_meas n (measurableSet_singleton i))
    have hU_meas : MeasurableSet U :=
      ((measurableSet_le measurable_const continuous_abs.measurable).preimage
        (hY_meas (Xz n) (hXz_meas n))).union
      ((measurableSet_le measurable_const continuous_abs.measurable).preimage
        (hY_meas (X n) (hX_meas n)))
    let C : ℝ := 2 * Real.sqrt (2 / Real.pi)
    have hC_nn : 0 ≤ C := by positivity
    have hdom_int : Integrable (fun ω ↦ 2 * η + C * U.indicator 1 ω) (Q n) :=
      (integrable_const (2 * η)).add (((integrable_const (1 : ℝ)).indicator hU_meas).const_mul C)
    have hpt : ∀ ω : Ω n,
        |deriv f (W n ω) - deriv f (Wz n ω)| ≤ 2 * η + C * U.indicator 1 ω := fun ω ↦ by
      by_cases hω : ω ∈ U
      · rw [indicator_of_mem hω, Pi.one_apply, mul_one]
        have h1 := hdf_bdd (W n ω)
        have h2 := hdf_bdd (Wz n ω)
        have habs := abs_sub (deriv f (W n ω)) (deriv f (Wz n ω))
        dsimp [C]; linarith
      · rw [indicator_of_notMem hω, mul_zero, add_zero]
        have hnot1 : |Xz n (I n ω) ω| < η / 2 := not_le.mp (fun h ↦ hω (Or.inl h))
        have hnot2 : |X n (I n ω) ω| < η / 2 := not_le.mp (fun h ↦ hω (Or.inr h))
        have hdiff_lt : |Wz n ω - W n ω| ≤ η := by
          rw [hdiff_eq ω]
          linarith [abs_sub (Xz n (I n ω) ω) (X n (I n ω) ω)]
        exact (hlip (W n ω) (Wz n ω)).trans (by linarith)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hstein]
    calc
      |∫ ω, (deriv f (W n ω) - deriv f (Wz n ω)) ∂(Q n)|
        ≤ ∫ ω, |deriv f (W n ω) - deriv f (Wz n ω)| ∂(Q n) := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (2 * η + C * U.indicator 1 ω) ∂(Q n) :=
          integral_mono (hdfW_int.sub hdfWz_int).abs hdom_int hpt
      _ = 2 * η + C * (Q n).real U := by
          have hCU : Integrable (fun ω ↦ C * U.indicator (1 : Ω n → ℝ) ω) (Q n) :=
            ((integrable_const (1 : ℝ)).indicator hU_meas).const_mul C
          rw [integral_add (integrable_const (2 * η)) hCU,
            integral_const, probReal_univ, one_smul, integral_const_mul,
            integral_indicator_one hU_meas]
      _ ≤ 2 * η + C * ((Q n).real {ω | η / 2 ≤ |Xz n (I n ω) ω|} +
            (Q n).real {ω | η / 2 ≤ |X n (I n ω) ω|}) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (measureReal_union_le _ _) hC_nn)
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro h ⟨B, hB⟩ ⟨L, hLip⟩
  simp only [Measure.coe_toProbabilityMeasure]
  by_cases hL0 : (L : ℝ) = 0
  · have hconst : ∀ x : ℝ, h x = h 0 := fun x ↦ by
      have hd := hLip.dist_le_mul x 0
      rw [hL0, zero_mul, dist_le_zero] at hd
      exact hd
    simp_rw [hconst, integral_const, probReal_univ, one_smul]
    exact tendsto_const_nhds
  · have hL_pos : 0 < (L : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg L) (Ne.symm hL0)
    let h₁ : ℝ → ℝ := fun x ↦ (L : ℝ)⁻¹ * (h x - h 0)
    have hh₁_lip : LipschitzWith 1 h₁ := by
      refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
      rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
      have hd := hLip.dist_le_mul x y
      rw [Real.dist_eq, Real.dist_eq] at hd
      have hsub : h₁ x - h₁ y = (L : ℝ)⁻¹ * (h x - h y) := by dsimp [h₁]; ring
      rw [hsub, abs_mul, abs_of_pos (inv_pos.mpr hL_pos)]
      calc
        (L : ℝ)⁻¹ * |h x - h y| ≤ (L : ℝ)⁻¹ * ((L : ℝ) * |x - y|) :=
          mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hL_pos.le)
        _ = |x - y| := inv_mul_cancel_left₀ hL_pos.ne' _
    let M₁ : ℝ := (L : ℝ)⁻¹ * max B 0
    have hh₁_bdd : ∀ x : ℝ, |h₁ x| ≤ M₁ := fun x ↦ by
      dsimp [h₁, M₁]
      rw [abs_mul, abs_of_pos (inv_pos.mpr hL_pos)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hL_pos.le)
      have := hB x 0
      rw [Real.dist_eq] at this
      exact this.trans (le_max_left B 0)
    have hh₁_int : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable h₁ μ := fun μ _ ↦
      Integrable.of_bound hh₁_lip.continuous.aestronglyMeasurable M₁
        (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hh₁_bdd x)
    have hh₁_tend : Tendsto (fun n : ℕ ↦ ∫ x, h₁ x ∂((Q n).map (W n))) atTop
        (𝓝 (∫ x, h₁ x ∂stdNormalLaw)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      let η : ℝ := ε / 4
      have hη : 0 < η := by positivity
      let C : ℝ := 2 * Real.sqrt (2 / Real.pi)
      have hC_pos : 0 < C := by positivity
      have hsum_tend : Tendsto (fun n : ℕ ↦
          C * ((Q n).real {ω | η / 2 ≤ |Xz n (I n ω) ω|} +
            (Q n).real {ω | η / 2 ≤ |X n (I n ω) ω|})) atTop (𝓝 0) := by
        simpa using ((hTail_Xz (η / 2) (half_pos hη)).add
          (hTail_X (η / 2) (half_pos hη))).const_mul C
      have hev := (Metric.tendsto_nhds.mp hsum_tend) (ε / 2) (half_pos hε)
      filter_upwards [hev] with n hn
      have hw_le : ENNReal.ofReal
          |(∫ x, h₁ x ∂((Q n).map (W n))) - (∫ x, h₁ x ∂stdNormalLaw)| ≤
          wassersteinDist ((Q n).map (W n)) stdNormalLaw := by
        unfold wassersteinDist ipm
        exact le_iSup₂_of_le h₁ hh₁_lip
          (le_iSup_of_le ⟨hh₁_int _, hh₁_int _⟩ le_rfl)
      have hbound_enn := hw_le.trans (hdW_bound n hη)
      have hRHS_nn : 0 ≤ 2 * η + C * ((Q n).real {ω | η / 2 ≤ |Xz n (I n ω) ω|} +
          (Q n).real {ω | η / 2 ≤ |X n (I n ω) ω|}) :=
        add_nonneg (by positivity)
          (mul_nonneg hC_pos.le (add_nonneg measureReal_nonneg measureReal_nonneg))
      have hreal_le : |(∫ x, h₁ x ∂((Q n).map (W n))) - (∫ x, h₁ x ∂stdNormalLaw)| ≤
          2 * η + C * ((Q n).real {ω | η / 2 ≤ |Xz n (I n ω) ω|} +
            (Q n).real {ω | η / 2 ≤ |X n (I n ω) ω|}) :=
        (ENNReal.ofReal_le_ofReal_iff hRHS_nn).mp hbound_enn
      rw [Real.dist_eq, sub_zero] at hn
      rw [Real.dist_eq]
      have h2η : 2 * η = ε / 2 := by dsimp [η]; ring
      linarith [le_abs_self (C * ((Q n).real {ω | η / 2 ≤ |Xz n (I n ω) ω|} +
        (Q n).real {ω | η / 2 ≤ |X n (I n ω) ω|}))]
    have hh_decomp : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
        ∫ x, h x ∂μ = (L : ℝ) * (∫ x, h₁ x ∂μ) + h 0 := fun μ _ ↦ by
      have hfn : h = fun x ↦ (L : ℝ) * h₁ x + h 0 := by
        ext x; dsimp [h₁]; rw [← mul_assoc, mul_inv_cancel₀ hL_pos.ne', one_mul, sub_add_cancel]
      conv_lhs => rw [hfn]
      rw [integral_add ((hh₁_int μ).const_mul (L : ℝ)) (integrable_const (h 0)),
        integral_const_mul, integral_const, probReal_univ, one_smul]
    simp_rw [hh_decomp]
    exact (hh₁_tend.const_mul (L : ℝ)).add_const (h 0)

end RowIndexed

end SteinMethod
