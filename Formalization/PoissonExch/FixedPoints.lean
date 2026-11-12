/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonExch.FixedPointsMoments
import Formalization.PoissonExch.Thm420
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Example 4.21: Transposition Coupling & Fixed-Point TV Bound (`FixedPoints`)

Transposition-coupling conditional jump probabilities and the $4/n$ total-variation bound for the
number of fixed points $W = \mathrm{numFixedPoints}(\pi)$ of a uniform random permutation on
`Fin n`, from Example 4.21 (`SteinIntro.tex:2681-2709`) of Nathan Ross,
*"Fundamentals of Stein's method"*:

* `fixedPoints_transposition_coupling`: exchangeability of $(W, W')$ and conditional jump
  probabilities given $\sigma$ for $\pi' = \pi \tau$ with uniform transposition $\tau$
  (`SteinIntro.tex:2682-2688`, `stmts-review-05H` `H3`).
* `tvDist_fixedPoints_poissonLaw_le`: $d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(1)) \le 4/n$
  for $n \ge 2$ (`SteinIntro.tex:2694-2699`).
-/

open MeasureTheory ProbabilityTheory Finset PMF
open scoped NNReal ENNReal

namespace SteinMethod

/-! ### Transposition counting and conditional expectation given `σ` -/

private abbrev PermSwapType (n : ℕ) : Type :=
  {π : Equiv.Perm (Fin n) // π.IsSwap}

private lemma permSwapType_mul_self {n : ℕ} (τ : PermSwapType n) : τ.1 * τ.1 = 1 := by
  rcases τ with ⟨_, x, y, _, rfl⟩
  exact Equiv.swap_mul_self x y

private noncomputable def permSwapEquivLt (n : ℕ) :
    {p : Fin n × Fin n // p.1 < p.2} ≃ PermSwapType n :=
  Equiv.ofBijective
    (fun p ↦ ⟨Equiv.swap p.1.1 p.1.2, ⟨p.1.1, p.1.2, p.2.ne, rfl⟩⟩)
    ⟨by
      rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨i', j'⟩, hij'⟩ h
      have hswap : Equiv.swap i j = Equiv.swap i' j' := Subtype.ext_iff.mp h
      have hsupp : ({i, j} : Finset (Fin n)) = {i', j'} := by
        have h1 := Equiv.Perm.support_swap hij.ne
        have h2 := Equiv.Perm.support_swap hij'.ne
        rw [← h1, ← h2, hswap]
      have hi_mem : i ∈ ({i', j'} : Finset (Fin n)) := by
        rw [← hsupp]; exact Finset.mem_insert_self i {j}
      have hj_mem : j ∈ ({i', j'} : Finset (Fin n)) := by
        rw [← hsupp]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem hj_mem
      ext <;> dsimp
      · rcases hi_mem with rfl | rfl
        · rfl
        · rcases hj_mem with rfl | rfl
          · exact False.elim (lt_asymm hij hij')
          · exact False.elim (hij.ne rfl)
      · rcases hj_mem with rfl | rfl
        · rcases hi_mem with rfl | rfl
          · exact False.elim (hij.ne rfl)
          · exact False.elim (lt_asymm hij hij')
        · rfl,
     by
      rintro ⟨π, x, y, hxy, rfl⟩
      rcases lt_trichotomy x y with hlt | rfl | hgt
      · exact ⟨⟨(x, y), hlt⟩, rfl⟩
      · exact absurd rfl hxy
      · refine ⟨⟨(y, x), hgt⟩, ?_⟩
        ext z
        simp [Equiv.swap_comm]⟩

private lemma permSwapEquivLt_apply_coe (n : ℕ) (q : {p : Fin n × Fin n // p.1 < p.2}) :
    (permSwapEquivLt n q).1 = Equiv.swap q.1.1 q.1.2 :=
  congrArg Subtype.val (Equiv.ofBijective_apply _ _ q)

private lemma two_mul_sum_permSwapType {n : ℕ} (g : Equiv.Perm (Fin n) → ℝ) :
    2 * (∑ τ : PermSwapType n, g τ.1) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, g (Equiv.swap i j) := by
  have hlt_sum :
      (∑ τ : PermSwapType n, g τ.1) =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), g (Equiv.swap i j) := by
    rw [← Equiv.sum_comp (permSwapEquivLt n) (fun τ ↦ g τ.1)]
    simp_rw [permSwapEquivLt_apply_coe]
    have hbij :
        (∑ q : {p : Fin n × Fin n // p.1 < p.2}, g (Equiv.swap q.1.1 q.1.2)) =
          ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n ↦ p.1 < p.2),
            g (Equiv.swap p.1 p.2) :=
      Finset.sum_bij (fun q _ ↦ q.1)
        (fun q _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩)
        (fun _ _ _ _ h ↦ Subtype.ext h)
        (fun p hp ↦ ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ ↦ rfl)
    rw [hbij, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_filter]
  have hgt_sum :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (· < i), g (Equiv.swap i j)) =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (i < ·), g (Equiv.swap i j) := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Equiv.swap_comm]
  have hsplit : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.erase i, g (Equiv.swap i j) =
        (∑ j ∈ Finset.univ.filter (i < ·), g (Equiv.swap i j)) +
          ∑ j ∈ Finset.univ.filter (· < i), g (Equiv.swap i j) := by
    intro i
    have hunion :
        Finset.univ.erase i =
          Finset.univ.filter (i < ·) ∪ Finset.univ.filter (· < i) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
        true_and]
      exact ne_iff_lt_or_gt.trans or_comm
    have hdisj :
        Disjoint (Finset.univ.filter (i < ·)) (Finset.univ.filter (· < i)) := by
      rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact lt_asymm h1 h2
    rw [hunion, Finset.sum_union hdisj]
  simp_rw [hsplit, Finset.sum_add_distrib, hgt_sum, ← hlt_sum]
  ring

private lemma two_mul_card_permSwapType {n : ℕ} (hn : 1 ≤ n) :
    2 * (Fintype.card (PermSwapType n) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  have h1 := two_mul_sum_permSwapType (n := n) (fun _ ↦ (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ _)] at h1
  rw [h1, Nat.cast_sub hn, Nat.cast_one]

private lemma choose_two_cast_real {n : ℕ} (hn : 1 ≤ n) :
    (Nat.choose n 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 1 m]
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, ih (by omega)]
    push_cast
    ring

private lemma avg_permSwapType_eq_choose {n : ℕ} (hn : 2 ≤ n) (g : Equiv.Perm (Fin n) → ℝ) :
    (Fintype.card (PermSwapType n) : ℝ)⁻¹ * (∑ τ : PermSwapType n, g τ.1) =
      (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, g (Equiv.swap i j)) /
        (2 * (Nat.choose n 2 : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hrn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrn1_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcard := two_mul_card_permSwapType hn1
  have hc_pos : (0 : ℝ) < Fintype.card (PermSwapType n) := by
    nlinarith [mul_pos hrn_pos hrn1_pos]
  have hsum := two_mul_sum_permSwapType g
  have hch : (Nat.choose n 2 : ℝ) = Fintype.card (PermSwapType n) := by
    rw [choose_two_cast_real hn1]
    linarith [hcard]
  rw [hch, ← hsum]
  have hc : (Fintype.card (PermSwapType n) : ℝ) ≠ 0 := hc_pos.ne'
  field_simp

/-- For $n \ge 2$, the type `{π : Equiv.Perm (Fin n) // π.IsSwap}` of transpositions is
nonempty. -/
lemma nonempty_isSwapPermFin {n : ℕ} (hn : 2 ≤ n) :
    Nonempty {π : Equiv.Perm (Fin n) // π.IsSwap} :=
  ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne Nat.zero_ne_one, rfl⟩⟩⟩

private lemma perm_condExp_given_sigma
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → PermSwapType n}
    (hσ_meas : Measurable σ) (hτ_meas : Measurable τ)
    (h_indep : ProbabilityTheory.IndepFun σ τ P)
    (hτ_unif : P.map τ =
      (@PMF.uniformOfFintype (PermSwapType n) inferInstance
        (nonempty_isSwapPermFin hn)).toMeasure)
    (H : Equiv.Perm (Fin n) × PermSwapType n → ℝ) :
    P[fun ω ↦ H (σ ω, τ ω) | MeasurableSpace.comap σ inferInstance] =ᵐ[P]
      fun ω ↦ (Fintype.card (PermSwapType n) : ℝ)⁻¹ * ∑ t₀ : PermSwapType n, H (σ ω, t₀) := by
  have hne : Nonempty (PermSwapType n) := nonempty_isSwapPermFin hn
  have : DiscreteMeasurableSpace (PermSwapType n) := inferInstance
  have hmσ := hσ_meas.comap_le
  let g : Equiv.Perm (Fin n) → ℝ :=
    fun π ↦ (Fintype.card (PermSwapType n) : ℝ)⁻¹ * ∑ t₀ : PermSwapType n, H (π, t₀)
  have hg_meas : Measurable g := .of_discrete
  have hRHS_sm : StronglyMeasurable[MeasurableSpace.comap σ inferInstance] (g ∘ σ) :=
    (hg_meas.comp (comap_measurable (m := inferInstance) σ)).stronglyMeasurable
  let M : ℝ := ∑ p : Equiv.Perm (Fin n) × PermSwapType n, |H p|
  have hH_meas : Measurable (fun ω ↦ H (σ ω, τ ω)) :=
    (Measurable.of_discrete (f := H)).comp (hσ_meas.prodMk hτ_meas)
  have hLHS_int : Integrable (fun ω ↦ H (σ ω, τ ω)) P := by
    refine Integrable.of_bound hH_meas.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (H p)) (Finset.mem_univ (σ ω, τ ω))
  have hRHS_int : Integrable (g ∘ σ) P := by
    refine Integrable.of_bound (hg_meas.comp hσ_meas).aestronglyMeasurable
      ((Fintype.card (PermSwapType n) : ℝ)⁻¹ * M) (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    dsimp [g]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    gcongr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      ∑ t₀ : PermSwapType n, |H (σ ω, t₀)|
          ≤ ∑ p : Equiv.Perm (Fin n) × PermSwapType n, |H p| := by
            rw [Fintype.sum_prod_type]
            exact Finset.single_le_sum
              (fun π _ ↦ Finset.sum_nonneg fun t₀ _ ↦ abs_nonneg (H (π, t₀)))
              (Finset.mem_univ (σ ω))
      _ = M := rfl
  have hτ_prob : ∀ t₀ : PermSwapType n,
      P.real {ω | τ ω = t₀} = (Fintype.card (PermSwapType n) : ℝ)⁻¹ := by
    intro t₀
    have hpre : {ω | τ ω = t₀} = τ ⁻¹' {t₀} := rfl
    have hm : P {ω | τ ω = t₀} = (Fintype.card (PermSwapType n) : ℝ≥0∞)⁻¹ := by
      rw [hpre, ← Measure.map_apply hτ_meas (measurableSet_singleton t₀), hτ_unif,
        PMF.toMeasure_apply_singleton _ t₀ (measurableSet_singleton t₀),
        PMF.uniformOfFintype_apply]
    rw [measureReal_def, hm, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmσ hLHS_int
    (fun s _ _ ↦ hRHS_int.integrableOn) (fun s hs _ ↦ ?_)
    hRHS_sm.aestronglyMeasurable).symm
  rcases hs with ⟨T, hT, rfl⟩
  have hDecomp :
      (σ ⁻¹' T).indicator (fun ω ↦ H (σ ω, τ ω)) =
        fun ω ↦ ∑ t₀ : PermSwapType n,
          (T.indicator (fun π ↦ H (π, t₀)) (σ ω)) *
            (({t₀} : Set (PermSwapType n)).indicator 1 (τ ω)) := by
    funext ω
    by_cases hω : σ ω ∈ T
    · simp only [Set.mem_preimage, hω, Set.indicator_of_mem]
      have hterm : ∀ t₀ : PermSwapType n,
          H (σ ω, t₀) *
              ({t₀} : Set (PermSwapType n)).indicator (1 : PermSwapType n → ℝ) (τ ω) =
            if τ ω = t₀ then H (σ ω, t₀) else 0 := by
        intro t₀
        by_cases ht : τ ω = t₀ <;> simp [ht]
      simp_rw [hterm]
      simp
    · simp [hω]
  have hIntTerm : ∀ t₀ : PermSwapType n,
      Integrable (fun ω ↦
        (T.indicator (fun π ↦ H (π, t₀)) (σ ω)) *
          (({t₀} : Set (PermSwapType n)).indicator 1 (τ ω))) P := by
    intro t₀
    have hm1 : Measurable (fun ω ↦ T.indicator (fun π ↦ H (π, t₀)) (σ ω)) :=
      (Measurable.of_discrete (f := T.indicator (fun π ↦ H (π, t₀)))).comp hσ_meas
    have hm2 :
        Measurable (fun ω ↦
          ({t₀} : Set (PermSwapType n)).indicator (1 : PermSwapType n → ℝ) (τ ω)) :=
      (Measurable.of_discrete (f := ({t₀} : Set (PermSwapType n)).indicator 1)).comp hτ_meas
    have hM : 0 ≤ M := Finset.sum_nonneg fun p _ ↦ abs_nonneg (H p)
    refine Integrable.of_bound (hm1.mul hm2).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    by_cases hω : σ ω ∈ T <;> by_cases ht : τ ω = t₀
    · simp only [hω, Set.indicator_of_mem, Set.mem_singleton_iff, ht, Pi.one_apply, mul_one]
      exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (H p)) (Finset.mem_univ (σ ω, t₀))
    · simp [hω, ht, hM]
    · simp [hω, ht, hM]
    · simp [hω, ht, hM]
  symm
  rw [← integral_indicator (hσ_meas hT), hDecomp,
    integral_finsetSum Finset.univ fun t₀ _ ↦ hIntTerm t₀]
  have hFactor : ∀ t₀ : PermSwapType n,
      ∫ ω, (T.indicator (fun π ↦ H (π, t₀)) (σ ω)) *
          (({t₀} : Set (PermSwapType n)).indicator 1 (τ ω)) ∂P =
        (Fintype.card (PermSwapType n) : ℝ)⁻¹ * ∫ ω in σ ⁻¹' T, H (σ ω, t₀) ∂P := by
    intro t₀
    have hf1 : Measurable (T.indicator (fun π ↦ H (π, t₀))) := .of_discrete
    have hf2 : Measurable (({t₀} : Set (PermSwapType n)).indicator (1 : PermSwapType n → ℝ)) :=
      .of_discrete
    rw [h_indep.integral_fun_comp_mul_comp hσ_meas.aemeasurable hτ_meas.aemeasurable
      hf1.stronglyMeasurable.aestronglyMeasurable hf2.stronglyMeasurable.aestronglyMeasurable]
    have h2 : ∫ ω, ({t₀} : Set (PermSwapType n)).indicator (1 : PermSwapType n → ℝ) (τ ω) ∂P =
        (Fintype.card (PermSwapType n) : ℝ)⁻¹ := by
      have heq :
          (fun ω ↦ ({t₀} : Set (PermSwapType n)).indicator (1 : PermSwapType n → ℝ) (τ ω)) =
            {ω | τ ω = t₀}.indicator (fun _ ↦ (1 : ℝ)) := by
        funext ω; by_cases ht : τ ω = t₀ <;> simp [ht]
      have hms : MeasurableSet {ω | τ ω = t₀} := hτ_meas (measurableSet_singleton t₀)
      rw [heq, integral_indicator_const (1 : ℝ) hms, smul_eq_mul, mul_one, hτ_prob t₀]
    have h1 : ∫ ω, T.indicator (fun π ↦ H (π, t₀)) (σ ω) ∂P =
        ∫ ω in σ ⁻¹' T, H (σ ω, t₀) ∂P := by
      have heq : (fun ω ↦ T.indicator (fun π ↦ H (π, t₀)) (σ ω)) =
          (σ ⁻¹' T).indicator (fun ω ↦ H (σ ω, t₀)) := by
        funext ω; by_cases hω : σ ω ∈ T <;> simp [hω]
      rw [heq, integral_indicator (hσ_meas hT)]
    rw [h1, h2, mul_comm]
  simp_rw [hFactor, ← Finset.mul_sum]
  have hIntHt : ∀ t₀ : PermSwapType n, Integrable (fun ω ↦ H (σ ω, t₀)) P := by
    intro t₀
    refine Integrable.of_bound ((Measurable.of_discrete (f := fun π ↦ H (π, t₀))).comp
      hσ_meas).aestronglyMeasurable M (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (H p)) (Finset.mem_univ (σ ω, t₀))
  symm
  have hg_comp : g ∘ σ =
      fun ω ↦ (Fintype.card (PermSwapType n) : ℝ)⁻¹ * ∑ t₀ : PermSwapType n, H (σ ω, t₀) := rfl
  rw [hg_comp, integral_const_mul,
    integral_finsetSum Finset.univ fun t₀ _ ↦ (hIntHt t₀).integrableOn]

/-! ### Transposition coupling (`Ex4_21_coupling`) -/

/-- Example 4.21 coupling (`SteinIntro.tex:2682-2688`, `stmts-review-05H` `H3`): for $n \ge 2$, a
uniform random permutation $\sigma$ of `Fin n`, and an independent uniform transposition $\tau$,
with $W = \mathrm{numFixedPoints}(\sigma)$, $W' = \mathrm{numFixedPoints}(\sigma \tau)$, and
$W_2 = \mathrm{numTwoCycles}(\sigma)$, $(W, W')$ is an exchangeable pair and
$\mathbb{P}(W' = W + 1 \mid \sigma) = \frac{n - W - 2 W_2}{\binom{n}{2}}$,
$\mathbb{P}(W = W' + 1 \mid \sigma) = \frac{W (n - W)}{\binom{n}{2}}$. -/
theorem fixedPoints_transposition_coupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → {π : Equiv.Perm (Fin n) // π.IsSwap}}
    (hσ_meas : Measurable σ) (hτ_meas : Measurable τ)
    (h_indep : ProbabilityTheory.IndepFun σ τ P)
    (hσ_unif : P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure)
    (hτ_unif : P.map τ =
      (@PMF.uniformOfFintype {π : Equiv.Perm (Fin n) // π.IsSwap} inferInstance
        (nonempty_isSwapPermFin hn)).toMeasure) :
    let W : Ω → ℕ := fun ω ↦ numFixedPoints (σ ω)
    let W' : Ω → ℕ := fun ω ↦ numFixedPoints (σ ω * (τ ω).1)
    let W2 : Ω → ℕ := fun ω ↦ numTwoCycles (σ ω)
    IsExchangeablePair P W W' ∧
      P[{ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        (fun ω ↦ ((n : ℝ) - (W ω : ℝ) - 2 * (W2 ω : ℝ)) / (Nat.choose n 2 : ℝ)) ∧
      P[{ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        (fun ω ↦ (W ω : ℝ) * ((n : ℝ) - (W ω : ℝ)) / (Nat.choose n 2 : ℝ)) := by
  intro W W' W2
  have hne : Nonempty (PermSwapType n) := nonempty_isSwapPermFin hn
  have : DiscreteMeasurableSpace (PermSwapType n) := inferInstance
  let μσ := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  let μτ := (@PMF.uniformOfFintype (PermSwapType n) inferInstance hne).toMeasure
  let stepInv : Equiv.Perm (Fin n) × PermSwapType n ≃ Equiv.Perm (Fin n) × PermSwapType n :=
    { toFun := fun p ↦ (p.1 * p.2.1, p.2)
      invFun := fun p ↦ (p.1 * p.2.1, p.2)
      left_inv := fun p ↦ by simp [mul_assoc, permSwapType_mul_self]
      right_inv := fun p ↦ by simp [mul_assoc, permSwapType_mul_self] }
  have hMapPair : P.map (fun ω ↦ (σ ω, τ ω)) = μσ.prod μτ := by
    rw [ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
      hσ_meas.aemeasurable hτ_meas.aemeasurable h_indep, hσ_unif, hτ_unif]
  have hMP_step : MeasurePreserving stepInv (μσ.prod μτ) (μσ.prod μτ) := by
    refine ⟨.of_discrete, ?_⟩
    ext s hs
    rw [Measure.map_apply .of_discrete hs]
    have hsingleton : ∀ p : Equiv.Perm (Fin n) × PermSwapType n,
        (μσ.prod μτ) {p} =
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ *
            (Fintype.card (PermSwapType n) : ℝ≥0∞)⁻¹ := by
      intro p
      have hp : ({p} : Set (Equiv.Perm (Fin n) × PermSwapType n)) = {p.1} ×ˢ {p.2} := by
        ext q; simp [Prod.ext_iff]
      rw [hp, Measure.prod_prod,
        PMF.toMeasure_apply_singleton _ p.1 (measurableSet_singleton p.1),
        PMF.toMeasure_apply_singleton _ p.2 (measurableSet_singleton p.2),
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
    classical
    let fs : Finset (Equiv.Perm (Fin n) × PermSwapType n) := s.toFinite.toFinset
    let fpre : Finset (Equiv.Perm (Fin n) × PermSwapType n) :=
      (stepInv ⁻¹' s).toFinite.toFinset
    have hcard_eq : fpre.card = fs.card := by
      refine Finset.card_bij (fun p _ ↦ stepInv p) ?_ ?_ ?_
      · intro p hp
        simpa [fs, fpre] using hp
      · intro p₁ _ p₂ _ h
        exact stepInv.injective h
      · intro q hq
        refine ⟨stepInv.symm q, ?_, stepInv.apply_symm_apply q⟩
        simpa [fs, fpre] using hq
    have hmeas_eq : ∀ ft : Finset (Equiv.Perm (Fin n) × PermSwapType n),
        (μσ.prod μτ) (↑ft : Set _) =
          ft.card • ((Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ *
            (Fintype.card (PermSwapType n) : ℝ≥0∞)⁻¹) := by
      intro ft
      induction ft using Finset.induction_on with
      | empty => simp
      | insert p ft hp ih =>
        rw [Finset.coe_insert, Set.insert_eq,
          measure_union (Set.disjoint_singleton_left.mpr (by simpa using hp)) .of_discrete,
          ih, Finset.card_insert_of_notMem hp, add_nsmul, one_nsmul, hsingleton p, add_comm]
    have h1 : (μσ.prod μτ) (stepInv ⁻¹' s) = (μσ.prod μτ) ↑fpre := by
      dsimp only [fpre]; rw [Set.Finite.coe_toFinset]
    have h2 : (μσ.prod μτ) s = (μσ.prod μτ) ↑fs := by
      dsimp only [fs]; rw [Set.Finite.coe_toFinset]
    rw [h1, h2, hmeas_eq fpre, hmeas_eq fs, hcard_eq]
  let pairVal : Equiv.Perm (Fin n) × PermSwapType n → ℕ × ℕ :=
    fun p ↦ (numFixedPoints p.1, numFixedPoints (p.1 * p.2.1))
  have hpairVal_meas : Measurable pairVal := .of_discrete
  have hJ_meas : Measurable (fun ω ↦ (σ ω, τ ω)) := hσ_meas.prodMk hτ_meas
  have hWW'_meas : Measurable (fun ω ↦ (W ω, W' ω)) := hpairVal_meas.comp hJ_meas
  have hExch : IsExchangeablePair P W W' := by
    refine ⟨hWW'_meas.aemeasurable, (measurable_swap.comp hWW'_meas).aemeasurable, ?_⟩
    have hpt : pairVal ∘ stepInv = Prod.swap ∘ pairVal := by
      funext p
      dsimp [pairVal, stepInv]
      rw [mul_assoc, permSwapType_mul_self, mul_one]
    calc
      P.map (fun ω ↦ (W ω, W' ω))
          = (P.map (fun ω ↦ (σ ω, τ ω))).map pairVal :=
            (Measure.map_map hpairVal_meas hJ_meas).symm
      _ = (μσ.prod μτ).map pairVal := by rw [hMapPair]
      _ = ((μσ.prod μτ).map stepInv).map pairVal := by rw [hMP_step.map_eq]
      _ = (μσ.prod μτ).map (pairVal ∘ stepInv) :=
            Measure.map_map hpairVal_meas .of_discrete
      _ = (μσ.prod μτ).map (Prod.swap ∘ pairVal) := by rw [hpt]
      _ = (P.map (fun ω ↦ (σ ω, τ ω))).map (Prod.swap ∘ pairVal) := by rw [← hMapPair]
      _ = P.map (fun ω ↦ (W' ω, W ω)) :=
            Measure.map_map (measurable_swap.comp hpairVal_meas) hJ_meas
  let g_up : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → ℝ :=
    fun π τπ ↦ if numFixedPoints (π * τπ) = numFixedPoints π + 1 then 1 else 0
  let H_up : Equiv.Perm (Fin n) × PermSwapType n → ℝ := fun p ↦ g_up p.1 p.2.1
  have h_ind_up :
      {ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ) = fun ω ↦ H_up (σ ω, τ ω) := by
    funext ω; by_cases h : W' ω = W ω + 1 <;> simp [H_up, g_up, W, W', h]
  have hCond_up :
      P[{ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        fun ω ↦ ((n : ℝ) - (W ω : ℝ) - 2 * (W2 ω : ℝ)) / (Nat.choose n 2 : ℝ) := by
    rw [h_ind_up]
    filter_upwards [perm_condExp_given_sigma P hn hσ_meas hτ_meas h_indep hτ_unif H_up] with ω hω
    rw [hω]
    change (Fintype.card (PermSwapType n) : ℝ)⁻¹ * (∑ t₀ : PermSwapType n, g_up (σ ω) t₀.1) = _
    rw [avg_permSwapType_eq_choose hn (g_up (σ ω))]
    dsimp [g_up]
    rw [sum_up_jump_eq (σ ω)]
    dsimp [W, W2]
    exact mul_div_mul_left _ _ two_ne_zero
  let g_down : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → ℝ :=
    fun π τπ ↦ if numFixedPoints π = numFixedPoints (π * τπ) + 1 then 1 else 0
  let H_down : Equiv.Perm (Fin n) × PermSwapType n → ℝ := fun p ↦ g_down p.1 p.2.1
  have h_ind_down :
      {ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ) = fun ω ↦ H_down (σ ω, τ ω) := by
    funext ω; by_cases h : W ω = W' ω + 1 <;> simp [H_down, g_down, W, W', h]
  have hCond_down :
      P[{ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        fun ω ↦ (W ω : ℝ) * ((n : ℝ) - (W ω : ℝ)) / (Nat.choose n 2 : ℝ) := by
    rw [h_ind_down]
    filter_upwards [perm_condExp_given_sigma P hn hσ_meas hτ_meas h_indep hτ_unif H_down] with ω hω
    rw [hω]
    change (Fintype.card (PermSwapType n) : ℝ)⁻¹ * (∑ t₀ : PermSwapType n, g_down (σ ω) t₀.1) = _
    rw [avg_permSwapType_eq_choose hn (g_down (σ ω))]
    dsimp [g_down]
    rw [sum_down_jump_eq (σ ω)]
    dsimp [W]
    exact mul_div_mul_left _ _ two_ne_zero
  exact ⟨hExch, hCond_up, hCond_down⟩

/-! ### Main bound: `d_TV(W, Po(1)) ≤ 4/n` -/

private lemma integrable_perm_real {n : ℕ} (g : Equiv.Perm (Fin n) → ℝ) :
    Integrable g (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure := by
  refine Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable
    (∑ π : Equiv.Perm (Fin n), |g π|) (Filter.Eventually.of_forall fun π ↦ ?_)
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun p _ ↦ abs_nonneg (g p)) (Finset.mem_univ π)

private lemma lintegral_ofReal_comp_fst_eq {n : ℕ} (hne : Nonempty (PermSwapType n))
    (g : Equiv.Perm (Fin n) → ℝ) (hg : ∀ π, 0 ≤ g π) :
    let μσ := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
    let μτ := (@PMF.uniformOfFintype (PermSwapType n) inferInstance hne).toMeasure
    (∫⁻ ω : Equiv.Perm (Fin n) × PermSwapType n, ENNReal.ofReal (g ω.1) ∂(μσ.prod μτ)) =
      ENNReal.ofReal (∫ π, g π ∂μσ) := by
  intro μσ μτ
  have : DiscreteMeasurableSpace (PermSwapType n) := inferInstance
  let f : Equiv.Perm (Fin n) → ℝ≥0∞ := fun π ↦ ENNReal.ofReal (g π)
  have hf_meas : Measurable f := .of_discrete
  have hmap : (μσ.prod μτ).map Prod.fst = μσ := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  calc
    (∫⁻ ω : Equiv.Perm (Fin n) × PermSwapType n, f ω.1 ∂(μσ.prod μτ))
        = ∫⁻ π, f π ∂((μσ.prod μτ).map Prod.fst) :=
          (lintegral_map hf_meas measurable_fst).symm
    _ = ∫⁻ π, ENNReal.ofReal (g π) ∂μσ := by rw [hmap]
    _ = ENNReal.ofReal (∫ π, g π ∂μσ) :=
          (ofReal_integral_eq_lintegral_ofReal (integrable_perm_real g)
            (Filter.Eventually.of_forall hg)).symm

/-- Example 4.21 main bound (`SteinIntro.tex:2694-2699`):
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(1)) \le 4/n$ where $W = \mathrm{numFixedPoints}$ on
a uniform random permutation of `Fin n` ($n \ge 2$). -/
theorem tvDist_fixedPoints_poissonLaw_le {n : ℕ} (hn : 2 ≤ n) :
    tvDist ((uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.map numFixedPoints)
      (poissonLaw 1) ≤ ENNReal.ofReal (4 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hrn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrn1_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hne : Nonempty (PermSwapType n) := nonempty_isSwapPermFin hn
  have : DiscreteMeasurableSpace (PermSwapType n) := inferInstance
  let μσ := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
  let μτ := (@PMF.uniformOfFintype (PermSwapType n) inferInstance hne).toMeasure
  let Ω := Equiv.Perm (Fin n) × PermSwapType n
  let P : Measure Ω := μσ.prod μτ
  let σ : Ω → Equiv.Perm (Fin n) := Prod.fst
  let τ : Ω → PermSwapType n := Prod.snd
  let W : Ω → ℕ := fun ω ↦ numFixedPoints (σ ω)
  let W' : Ω → ℕ := fun ω ↦ numFixedPoints (σ ω * (τ ω).1)
  let W2 : Ω → ℕ := fun ω ↦ numTwoCycles (σ ω)
  have hσ_unif : P.map σ = μσ := by
    dsimp only [P, σ]
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hτ_unif : P.map τ = μτ := by
    dsimp only [P, τ]
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have h_indep : ProbabilityTheory.IndepFun σ τ P :=
    ProbabilityTheory.indepFun_prod measurable_id measurable_id
  obtain ⟨hExch, hCond_up, hCond_down⟩ :=
    fixedPoints_transposition_coupling P hn measurable_fst measurable_snd h_indep hσ_unif hτ_unif
  have hmapW : P.map W = μσ.map numFixedPoints := by
    rw [← hσ_unif, Measure.map_map (Measurable.of_discrete (f := numFixedPoints)) measurable_fst]
    rfl
  let mΩ : MeasurableSpace Ω := inferInstance
  let F : MeasurableSpace Ω := MeasurableSpace.comap σ inferInstance
  let _ : MeasurableSpace Ω := mΩ
  have hFle : F ≤ mΩ := measurable_fst.comap_le
  have hWF : MeasurableSpace.comap W inferInstance ≤ F := by
    change MeasurableSpace.comap (numFixedPoints ∘ σ) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (Measurable.of_discrete (f := numFixedPoints)).comap_le
  let c : ℝ := ((n : ℝ) - 1) / 2
  have hthm := tvDist_poissonLaw_exchangeable_le P (r := 1) zero_lt_one
    (Measurable.of_discrete (f := W)) (Measurable.of_discrete (f := W'))
    hExch hFle hWF c
  rw [← hmapW]
  have hmin1 : ENNReal.ofReal (min 1 (((1 : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)))) = 1 := by
    simp
  rw [hmin1, one_mul] at hthm
  refine hthm.trans ?_
  let g₁ : Equiv.Perm (Fin n) → ℝ :=
    fun π ↦ ((numFixedPoints π : ℝ) + 2 * (numTwoCycles π : ℝ)) / (n : ℝ)
  let g₂ : Equiv.Perm (Fin n) → ℝ :=
    fun π ↦ (numFixedPoints π : ℝ) ^ 2 / (n : ℝ)
  have hg₁_nn : ∀ π, 0 ≤ g₁ π := fun π ↦ div_nonneg (by positivity) hrn_pos.le
  have hg₂_nn : ∀ π, 0 ≤ g₂ π := fun π ↦ div_nonneg (by positivity) hrn_pos.le
  have hae₁ :
      (fun ω : Ω ↦ ENNReal.ofReal |((1 : ℝ≥0) : ℝ) - c *
          condExpAt F mΩ P ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω|) =ᵐ[P]
        fun ω : Ω ↦ ENNReal.ofReal (g₁ ω.1) := by
    filter_upwards [hCond_up] with ω hω
    change ENNReal.ofReal |(1 : ℝ) - c *
        (condExpAt F mΩ P ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω)| =
      ENNReal.ofReal (g₁ (σ ω))
    dsimp only [condExpAt, F, mΩ, W, W', σ, τ]
    rw [hω, choose_two_cast_real hn1]
    have halg :
        (1 : ℝ) -
            c * (((n : ℝ) - (W ω : ℝ) - 2 * (W2 ω : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1) / 2)) =
          g₁ (σ ω) := by
      dsimp [c, g₁, W, W2]
      field_simp [hrn_pos.ne', hrn1_pos.ne']
      ring
    dsimp only [W, W2, σ] at halg
    rw [halg, abs_of_nonneg (hg₁_nn ω.1)]
  have hae₂ :
      (fun ω : Ω ↦ ENNReal.ofReal |(W ω : ℝ) - c *
          condExpAt F mΩ P ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω|) =ᵐ[P]
        fun ω : Ω ↦ ENNReal.ofReal (g₂ ω.1) := by
    filter_upwards [hCond_down] with ω hω
    change ENNReal.ofReal |(W ω : ℝ) - c *
        (condExpAt F mΩ P ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω)| =
      ENNReal.ofReal (g₂ (σ ω))
    dsimp only [condExpAt, F, mΩ, W, W', σ, τ]
    rw [hω, choose_two_cast_real hn1]
    have halg :
        (W ω : ℝ) -
            c * ((W ω : ℝ) * ((n : ℝ) - (W ω : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1) / 2)) =
          g₂ (σ ω) := by
      dsimp [c, g₂, W]
      field_simp [hrn_pos.ne', hrn1_pos.ne']
      ring
    dsimp only [W, σ] at halg
    rw [halg, abs_of_nonneg (hg₂_nn ω.1)]
  have hI₁ : ∫ π, g₁ π ∂μσ = 2 / (n : ℝ) := by
    have hrew :
        g₁ = fun π ↦
          (1 / (n : ℝ)) * ((numFixedPoints π : ℝ) + 2 * (numTwoCycles π : ℝ)) := by
      ext π; dsimp [g₁]; ring
    rw [hrew, integral_const_mul,
      integral_add (integrable_perm_real _) ((integrable_perm_real _).const_mul 2),
      integral_const_mul, expected_fixed_points hn1, expected_two_cycles hn]
    ring
  have hI₂ : ∫ π, g₂ π ∂μσ = 2 / (n : ℝ) := by
    have hrew : g₂ = fun π ↦ (1 / (n : ℝ)) * (numFixedPoints π : ℝ) ^ 2 := by
      ext π; dsimp [g₂]; ring
    rw [hrew, integral_const_mul, expected_fixed_points_sq hn]
    ring
  rw [lintegral_congr_ae hae₁, lintegral_congr_ae hae₂,
    lintegral_ofReal_comp_fst_eq hne g₁ hg₁_nn,
    lintegral_ofReal_comp_fst_eq hne g₂ hg₂_nn,
    hI₁, hI₂, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hadd : (2 : ℝ) / (n : ℝ) + 2 / (n : ℝ) = 4 / (n : ℝ) := by ring
  rw [hadd]

end SteinMethod
