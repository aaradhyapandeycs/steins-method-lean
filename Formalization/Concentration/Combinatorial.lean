/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Concentration.CombinatorialPair

/-!
# Hoeffding's Combinatorial Concentration (`Formalization.Concentration.Combinatorial`)

Formalizes **Proposition 7.3** (`SteinIntro.tex:3612-3627`; `ISSUE-TYPO-7.5`, `ISSUE-7.5`,
ruling `D7`) from Section 7 of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`):

* `combinatorial_isSteinPair_restricted`, `not_combinatorial_isSteinPair_n2`: re-exported from
  `Formalization.Concentration.CombinatorialPair`.
* `combinatorial_concentration` (**Proposition 7.3**, `Prop7_3`, `SteinIntro.tex:3612-3617`):
  concentration bound $\mathbb{P}(|W| \ge t) \le
  2\exp\bigl(-t^2 / (\frac{4}{n}\sum_{i, j} a_{ij} + 2t)\bigr)$ for all $n \in \mathbb{N}$ via the
  general $a > 0$ library theorem `steinPair_tail_bounds_of_pos` (`D7`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-- **Proposition 7.3** (`Prop7_3`, `SteinIntro.tex:3612-3617`, `ISSUE-TYPO-7.5`, `ISSUE-7.5`,
ruling `D7`): for any $n \in \mathbb{N}$, any array $(a_{ij})_{1 \le i,j \le n}$ with
$0 \le a_{ij} \le 1$, and a uniform random permutation $\sigma$ of `Fin n`,
$W = \sum_{i=1}^n a_{i, \sigma(i)} - \frac{1}{n}\sum_{i,j} a_{ij}$ satisfies
$\mathbb{P}(|W| \ge t) \le 2\exp\bigl(-t^2 / (\frac{4}{n}\sum_{i,j} a_{ij} + 2t)\bigr)$ for all
$t > 0$. -/
theorem combinatorial_concentration
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {a : Fin n → Fin n → ℝ} {σ : Ω → Equiv.Perm (Fin n)}
    (ha_unit : ∀ i j : Fin n, 0 ≤ a i j ∧ a i j ≤ 1)
    (hσ_meas : AEMeasurable σ P)
    (hσ_unif : P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure) :
    let W : Ω → ℝ :=
      fun ω ↦ (∑ i : Fin n, a i (σ ω i)) - (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    ∀ t : ℝ, 0 < t →
      P.real {ω | t ≤ |W ω|} ≤
        2 * Real.exp (-t ^ 2 / ((4 / (n : ℝ)) * (∑ i : Fin n, ∑ j : Fin n, a i j) + 2 * t)) := by
  intro W t ht
  by_cases hn2 : 2 ≤ n
  · have hne : Nonempty (SwapType n) :=
      ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne (by norm_num), rfl⟩⟩⟩
    have : DiscreteMeasurableSpace (SwapType n) := inferInstance
    let μσ := (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure
    let μτ := (@PMF.uniformOfFintype (SwapType n) inferInstance hne).toMeasure
    have : IsProbabilityMeasure μσ := PMF.toMeasure.isProbabilityMeasure _
    have : IsProbabilityMeasure μτ := PMF.toMeasure.isProbabilityMeasure _
    let Ω' := Equiv.Perm (Fin n) × SwapType n
    let Q : Measure Ω' := μσ.prod μτ
    have : IsProbabilityMeasure Q := inferInstance
    let σ' : Ω' → Equiv.Perm (Fin n) := Prod.fst
    let τ' : Ω' → SwapType n := Prod.snd
    have hσ'_unif : Q.map σ' = μσ := by
      dsimp only [Q, σ']
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    have hτ'_unif : Q.map τ' = μτ := by
      dsimp only [Q, τ']
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    have h_indep' : ProbabilityTheory.IndepFun σ' τ' Q :=
      ProbabilityTheory.indepFun_prod measurable_id measurable_id
    obtain ⟨hExch, hWQ_meas, hWQ2, _, hCond_W⟩ :=
      combinatorial_exchangeable_and_linear Q hn2 a measurable_fst measurable_snd h_indep'
        hσ'_unif hτ'_unif
    let WQ : Ω' → ℝ := fun q ↦ combStat a (σ' q)
    let W'Q : Ω' → ℝ := fun q ↦ combStat a (σ' q * (τ' q).1)
    have hrn_pos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hrn1_pos : 0 < (n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    let a_param : ℝ := 2 / ((n : ℝ) - 1)
    have ha_pos : 0 < a_param := div_pos zero_lt_two hrn1_pos
    let S_all : ℝ := ∑ i : Fin n, ∑ j : Fin n, a i j
    have hS_nn : 0 ≤ S_all :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ (ha_unit i j).1
    let C_param : ℝ := (2 / (n : ℝ)) * S_all
    have hC_nn : 0 ≤ C_param := mul_nonneg (div_nonneg zero_le_two hrn_pos.le) hS_nn
    have hmgf : ∀ θ : ℝ, Integrable (fun q ↦ Real.exp (θ * WQ q) * |W'Q q - WQ q|) Q :=
      fun _ ↦ Integrable.of_finite
    have hmW_le : MeasurableSpace.comap WQ inferInstance ≤
        MeasurableSpace.comap σ' inferInstance := by
      change MeasurableSpace.comap (combStat a ∘ σ') inferInstance ≤ _
      rw [← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (Measurable.of_discrete (f := combStat a)).comap_le
    have hCondSq := combinatorial_condExp_given_sigma Q hn2 measurable_fst measurable_snd h_indep'
      hτ'_unif (fun p ↦ (combStat a (p.1 * p.2.1) - combStat a p.1) ^ 2)
    have hCondBound :
        ∀ᵐ q ∂Q,
          Q[fun q' ↦ (W'Q q' - WQ q') ^ 2 |
              MeasurableSpace.comap σ' inferInstance] q / (2 * a_param) ≤
            1 * WQ q + C_param := by
      filter_upwards [hCondSq] with q hq
      change Q[fun q' ↦ (combStat a (σ' q' * (τ' q').1) - combStat a (σ' q')) ^ 2 |
          MeasurableSpace.comap σ' inferInstance] q /
        (2 * a_param) ≤ 1 * combStat a (σ' q) + C_param
      rw [hq, avg_swapType_eq hn2 (fun τπ ↦ (combStat a (σ' q * τπ) - combStat a (σ' q)) ^ 2)]
      let π := σ' q
      have hterm_le : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
          (combStat a (π * Equiv.swap i j) - combStat a π) ^ 2 ≤
            2 * (a i (π j) + a j (π i) + a i (π i) + a j (π j)) := by
        intro i j hj
        rw [combStat_mul_swap_sub a π (Finset.mem_erase.mp hj).1]
        have h1 := ha_unit i (π j)
        have h2 := ha_unit j (π i)
        have h3 := ha_unit i (π i)
        have h4 := ha_unit j (π j)
        set u := a i (π j) + a j (π i)
        set v := a i (π i) + a j (π j)
        have hu0 : 0 ≤ u := by linarith
        have hu2 : u ≤ 2 := by linarith
        have hv0 : 0 ≤ v := by linarith
        have hv2 : v ≤ 2 := by linarith
        have heq : a i (π j) + a j (π i) - a i (π i) - a j (π j) = u - v := by ring
        have hsum : a i (π j) + a j (π i) + a i (π i) + a j (π j) = u + v := by ring
        rw [heq, hsum]
        rcases le_total u v with huv | hvu
        · have hd : 0 ≤ v - u := sub_nonneg.mpr huv
          have hd2 : v - u ≤ 2 := by linarith
          calc
            (u - v) ^ 2 = (v - u) * (v - u) := by ring
            _ ≤ 2 * (v - u) := mul_le_mul_of_nonneg_right hd2 hd
            _ ≤ 2 * (u + v) := by linarith
        · have hd : 0 ≤ u - v := sub_nonneg.mpr hvu
          have hd2 : u - v ≤ 2 := by linarith
          calc
            (u - v) ^ 2 = (u - v) * (u - v) := by ring
            _ ≤ 2 * (u - v) := mul_le_mul_of_nonneg_right hd2 hd
            _ ≤ 2 * (u + v) := by linarith
      have hsum_sq_le :
          (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
              (combStat a (π * Equiv.swap i j) - combStat a π) ^ 2) ≤
            4 * (n : ℝ) * combStat a π + 8 * S_all := by
        have hstep1 :
            (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
                (combStat a (π * Equiv.swap i j) - combStat a π) ^ 2) ≤
              ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
                2 * (a i (π j) + a j (π i) + a i (π i) + a j (π j)) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ hterm_le i j hj
        have hstep2 :
            (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
                2 * (a i (π j) + a j (π i) + a i (π i) + a j (π j))) =
              4 * S_all + 4 * ((n : ℝ) - 2) * ∑ i : Fin n, a i (π i) := by
          simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
          have hs1 := sum_erase_perm_apply a π
          have hs2 := sum_erase_perm_apply_symm a π
          have hs3 : (∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, a i (π i)) =
              ((n : ℝ) - 1) * ∑ i : Fin n, a i (π i) := by
            have hn1 : 1 ≤ n := by omega
            simp [Finset.card_erase_of_mem (Finset.mem_univ _), Nat.cast_sub hn1, Finset.mul_sum]
          have hs4 : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, a j (π j)) =
              ((n : ℝ) - 1) * ∑ i : Fin n, a i (π i) := by
            simp_rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_sub_distrib,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
          rw [hs1, hs2, hs3, hs4]
          dsimp [S_all]
          ring
        have hdiag_nn : 0 ≤ ∑ i : Fin n, a i (π i) :=
          Finset.sum_nonneg fun i _ ↦ (ha_unit i (π i)).1
        have hstep3 :
            4 * S_all + 4 * ((n : ℝ) - 2) * (∑ i : Fin n, a i (π i)) ≤
              4 * (n : ℝ) * combStat a π + 8 * S_all := by
          have hId : 4 * (n : ℝ) * combStat a π + 8 * S_all =
              4 * S_all + 4 * (n : ℝ) * (∑ i : Fin n, a i (π i)) := by
            unfold combStat
            dsimp [S_all]
            field_simp [hrn_pos.ne']
            ring
          rw [hId]
          nlinarith
        exact hstep1.trans (hstep2.le.trans hstep3)
      calc
        1 / ((n : ℝ) * ((n : ℝ) - 1)) *
            (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
              (combStat a (π * Equiv.swap i j) - combStat a π) ^ 2) /
            (2 * a_param)
            ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) *
                (4 * (n : ℝ) * combStat a π + 8 * S_all) / (2 * a_param) := by
              gcongr
        _ = 1 * combStat a π + C_param := by
              dsimp [a_param, C_param]
              field_simp [hrn_pos.ne', hrn1_pos.ne']
              ring
    have hTails := steinPair_tail_bounds_of_pos Q hExch ha_pos hWQ_meas hWQ2 hCond_W hmgf
      hmW_le measurable_fst.comap_le zero_le_one hC_nn hCondBound ht
    have hEventEq : P.real {ω | t ≤ |W ω|} = Q.real {q | t ≤ |WQ q|} := by
      have hset : MeasurableSet {x : ℝ | t ≤ |x|} :=
        continuous_abs.measurable measurableSet_Ici
      have hcs_meas : Measurable (combStat a) := .of_discrete
      have hLaw : P.map W = Q.map WQ := by
        calc
          P.map (combStat a ∘ σ) = (P.map σ).map (combStat a) :=
            (AEMeasurable.map_map_of_aemeasurable hcs_meas.aemeasurable hσ_meas).symm
          _ = (Q.map σ').map (combStat a) := by rw [hσ_unif, hσ'_unif]
          _ = Q.map WQ := Measure.map_map hcs_meas measurable_fst
      have hW_aem : AEMeasurable W P := hcs_meas.comp_aemeasurable hσ_meas
      have hpreP : {ω | t ≤ |W ω|} = W ⁻¹' {x : ℝ | t ≤ |x|} := rfl
      have hpreQ : {q | t ≤ |WQ q|} = WQ ⁻¹' {x : ℝ | t ≤ |x|} := rfl
      rw [hpreP, hpreQ, measureReal_def, measureReal_def,
        ← Measure.map_apply_of_aemeasurable hW_aem hset,
        hLaw, Measure.map_apply hWQ_meas hset]
    have hUnion : Q.real {q | t ≤ |WQ q|} ≤ Q.real {q | t ≤ WQ q} + Q.real {q | WQ q ≤ -t} := by
      have hsub : {q | t ≤ |WQ q|} ⊆ {q | t ≤ WQ q} ∪ {q | WQ q ≤ -t} := by
        intro q hq
        change t ≤ |WQ q| at hq
        rcases le_abs.mp hq with h1 | h2
        · exact Or.inl (show t ≤ WQ q from h1)
        · exact Or.inr (show WQ q ≤ -t from by linarith)
      have hmono : Q.real {q | t ≤ |WQ q|} ≤ Q.real ({q | t ≤ WQ q} ∪ {q | WQ q ≤ -t}) := by
        rw [measureReal_def, measureReal_def]
        exact ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono hsub)
      exact hmono.trans (measureReal_union_le _ _)
    have hDenEq : 2 * C_param + 2 * 1 * t = (4 / (n : ℝ)) * S_all + 2 * t := by
      dsimp [C_param]; ring
    have hUpper : Q.real {q | t ≤ WQ q} ≤
        Real.exp (-t ^ 2 / ((4 / (n : ℝ)) * S_all + 2 * t)) := by
      simpa only [hDenEq] using hTails.1
    have hLower : Q.real {q | WQ q ≤ -t} ≤
        Real.exp (-t ^ 2 / ((4 / (n : ℝ)) * S_all + 2 * t)) := by
      rcases hC_nn.eq_or_lt with hC0 | hC_pos
      · rw [hTails.2.2.1 hC0.symm]
        exact (Real.exp_pos _).le
      · refine hTails.2.1.trans (Real.exp_le_exp.mpr ?_)
        rw [← hDenEq, neg_div, neg_div]
        have h1 : t ^ 2 / (2 * C_param + 2 * 1 * t) ≤ t ^ 2 / (2 * C_param) :=
          div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith)
        linarith
    rw [hEventEq]
    linarith [hUnion, hUpper, hLower]
  · have hW0 : ∀ ω : Ω, W ω = 0 := by
      intro ω
      interval_cases n
      · simp [W]
      · dsimp [W]
        rw [Fin.sum_univ_one]
        simp [Fin.eq_zero (σ ω 0)]
    have hEmpty : {ω | t ≤ |W ω|} = ∅ := by
      ext ω
      change t ≤ |W ω| ↔ ω ∈ (∅ : Set Ω)
      rw [hW0 ω, abs_zero]
      simp [not_le.mpr ht]
    rw [hEmpty, measureReal_empty]
    positivity

end SteinMethod
