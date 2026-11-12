/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Negative.Occupancy

/-!
# Uniform Coupon Collecting (`Formalization.PoissonSizeBias.Negative.CouponUniform`)

Formalizes **Example 4.15** (`[Coupon collecting]`, `\label{ex123}`, eq. `(4.13)` `\label{129}`,
`SteinIntro.tex:2512-2565`):

- `ex4_15_allTypes_iff`: $W = 0 \iff$ every box receives at least one ball
  (`Function.Surjective b`).
- `ex4_15_sizeBias`: explicit ball-redistribution size-bias coupling, exchangeability, and
  coordinatewise monotonicity for $2 \le n$ (`SteinIntro.tex:2529-2539`).
- `ex4_15_restricted`: exact avoidance probabilities, mean, variance, eq. `(4.13)` TV bound, and
  full-collection probability error bound for $2 \le n$ (`SteinIntro.tex:2526-2551`).
- `ex4_15_eq413_identity`, `ex4_15_asymptotic_bounds`: exact `(4.13)` algebraic identity and first
  upper bound for $2 \le n$, together with logarithmic bounds for $3 \le n$
  (`SteinIntro.tex:2554-2560`; `review-05G4` item 2).
- `ex4_15_rate`: asymptotic Poisson limit $\lambda_n \to e^c$ and $O(\log(n)/n)$ convergence rate
  in the critical window $k_n = n \log n - c n + O(1)$ (`SteinIntro.tex:2553-2564`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Part 1: Full-Collection Event Equivalence (`SteinIntro.tex:2522-2525`) -/

/-- **Example 4.15, full-collection event equivalence** (`\label{ex123}`,
`SteinIntro.tex:2522-2525`): the empty-box count equals `0` iff `b : Fin k → Fin n` is
surjective. -/
theorem ex4_15_allTypes_iff {n k : ℕ} (b : Fin k → Fin n) :
    (∑ i : Fin n, (if ∀ r : Fin k, b r ≠ i then (1 : ℕ) else 0)) = 0 ↔ Function.Surjective b := by
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    have hi := h i (Finset.mem_univ i)
    by_contra hno
    push Not at hno
    have h1 : (if ∀ r : Fin k, b r ≠ i then (1 : ℕ) else 0) = 1 :=
      ite_eq_left fun r hr ↦ hno r hr
    omega
  · intro hsurj i _
    obtain ⟨r, hr⟩ := hsurj i
    exact ite_eq_right fun hall ↦ hall r hr

/-! ### Part 2: Uniform Redistribution Size-Bias Coupling (`SteinIntro.tex:2529-2539`) -/

private lemma unifProb_nn (n : ℕ) : ∀ _ : Fin n, 0 ≤ (1 : ℝ) / (n : ℝ) :=
  fun _ ↦ by positivity

private lemma unifProb_sum {n : ℕ} (hn : 0 < n) :
    (∑ _ : Fin n, (1 : ℝ) / (n : ℝ)) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [div_eq_mul_inv, hn0]

/-- **Example 4.15, redistribution size-bias coupling** (`\label{ex123}`,
`SteinIntro.tex:2529-2539`): redirecting every ball in box `0` uniformly among `{1, …, n - 1}`
($2 \le n$) yields the conditional distribution of $(X_j)_{j \ne 0}$ given $X_0 = 1$, satisfies
$X_j' \le X_j$ pointwise for $j \ne 0$, and gives a size-bias representation of $W$. -/
theorem ex4_15_sizeBias
    {n k : ℕ} (hn : 2 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B : Fin k → Ω → Fin n}
    {R : Fin k → Ω → {j : Fin n // j ≠ ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩}}
    (hB_meas : ∀ r : Fin k, Measurable (B r))
    (hB_indep : ProbabilityTheory.iIndepFun B P)
    (hB_prob : ∀ r : Fin k, ∀ i : Fin n, P.real {ω | B r ω = i} = 1 / (n : ℝ))
    (hR_meas : ∀ r : Fin k, Measurable (R r))
    (hR_indep : ProbabilityTheory.iIndepFun R P)
    (hR_prob : ∀ r : Fin k, ∀ j : {j : Fin n // j ≠ ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩},
      P.real {ω | R r ω = j} = 1 / ((n : ℝ) - 1))
    (hBR_indep : ProbabilityTheory.IndepFun (fun ω r ↦ B r ω) (fun ω r ↦ R r ω) P) :
    let i₀ : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩
    let B' : Fin k → Ω → Fin n := fun r ω ↦ if B r ω = i₀ then (R r ω).1 else B r ω
    let X : Fin n → Ω → ℕ := fun i ω ↦ if ∀ r : Fin k, B r ω ≠ i then 1 else 0
    let X' : Fin n → Ω → ℕ := fun i ω ↦ if ∀ r : Fin k, B' r ω ≠ i then 1 else 0
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω : ℝ)
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ i₀}, (X' j.1 ω : ℝ)) + 1
    IsExchangeableTuple P X ∧
      P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) =
        (ProbabilityTheory.cond P {ω | X i₀ ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 ω) ∧
      (∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i₀}, X' j.1 ω ≤ X j.1 ω) ∧
      IsSizeBias P W P Ws := by
  classical
  intro i₀ B' X X' W Ws
  have hn_pos : 0 < n := by omega
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn1_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let Bvec : Ω → (Fin k → Fin n) := fun ω r ↦ B r ω
  let Rvec : Ω → (Fin k → {j : Fin n // j ≠ i₀}) := fun ω r ↦ R r ω
  let B'vec : Ω → (Fin k → Fin n) := fun ω r ↦ B' r ω
  have hBv_meas : Measurable Bvec := Measurable.of_eval hB_meas
  have hRv_meas : Measurable Rvec := Measurable.of_eval hR_meas
  let μB := ballBoxMeasure (fun _ : Fin n ↦ 1 / (n : ℝ)) (unifProb_nn n) (unifProb_sum hn_pos) k
  have hmap_B : P.map Bvec = μB :=
    map_pi_eq_ballBoxMeasure P (unifProb_nn n) (unifProb_sum hn_pos) hB_meas hB_indep hB_prob
  -- Singleton probability of `Rvec`
  have hR_sing : ∀ u : Fin k → {j : Fin n // j ≠ i₀},
      P {ω | Rvec ω = u} = ENNReal.ofReal ((1 / ((n : ℝ) - 1)) ^ k) := by
    intro u
    have hpre : {ω | Rvec ω = u} = ⋂ r ∈ (Finset.univ : Finset (Fin k)), R r ⁻¹' {u r} := by
      ext ω
      simp [Rvec, funext_iff]
    rw [hpre, (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hR_indep)
      Finset.univ (fun _ _ ↦ .of_discrete)]
    have hprod : (∏ r : Fin k, P (R r ⁻¹' {u r})) =
        ∏ _r : Fin k, ENNReal.ofReal (1 / ((n : ℝ) - 1)) := by
      refine Finset.prod_congr rfl fun r _ ↦ ?_
      rw [← ofReal_measureReal]
      congr 1
      exact hR_prob r (u r)
    rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow (by positivity)]
  have hB_sing : ∀ b : Fin k → Fin n,
      P {ω | Bvec ω = b} = ENNReal.ofReal ((1 / (n : ℝ)) ^ k) := by
    intro b
    have hm : P {ω | Bvec ω = b} = μB {b} := by
      rw [← hmap_B, Measure.map_apply hBv_meas .of_discrete]
      rfl
    rw [hm, ballBoxMeasure_singleton, ballBoxWeight_eq_ofReal (unifProb_nn n)]
    unfold ballBoxRealWeight
    simp
  -- Joint pushforward `P.map (fun ω ↦ (Bvec ω, Rvec ω))`
  let Jvec : Ω → (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i₀}) := fun ω ↦ (Bvec ω, Rvec ω)
  have hJv_meas : Measurable Jvec := hBv_meas.prodMk hRv_meas
  have hJ_sing : ∀ bu : (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i₀}),
      (P.map Jvec) {bu} =
        ENNReal.ofReal ((1 / (n : ℝ)) ^ k * (1 / ((n : ℝ) - 1)) ^ k) := by
    rintro ⟨b, u⟩
    rw [Measure.map_apply hJv_meas .of_discrete]
    have hpre : Jvec ⁻¹' {(b, u)} = Bvec ⁻¹' {b} ∩ Rvec ⁻¹' {u} := by
      ext ω
      simp [Jvec]
    rw [hpre, hBR_indep.measure_inter_preimage_eq_mul {b} {u} .of_discrete .of_discrete]
    change P {ω | Bvec ω = b} * P {ω | Rvec ω = u} = _
    rw [hB_sing b, hR_sing u, ← ENNReal.ofReal_mul (by positivity)]
  -- Pushforward `P.map B'vec` equals `(cond μB {b | ∀ r, b r ≠ i₀})`
  let redir : (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i₀}) → (Fin k → Fin n) :=
    fun bu r ↦ if bu.1 r = i₀ then (bu.2 r).1 else bu.1 r
  have hB'_eq_comp : B'vec = redir ∘ Jvec := rfl
  have hp₀_eq : μB.real {b | ∀ r : Fin k, b r ≠ i₀} = (1 - 1 / (n : ℝ)) ^ k :=
    ballBox_prob_avoid_one (unifProb_nn n) (unifProb_sum hn_pos) i₀
  have hp₀_pos : 0 < μB.real {b | ∀ r : Fin k, b r ≠ i₀} := by
    rw [hp₀_eq]
    have : 1 / (n : ℝ) < 1 := by
      rw [div_lt_one hnR_pos]
      exact_mod_cast hn
    exact pow_pos (by linarith) k
  have hmap_B'vec : P.map B'vec = ProbabilityTheory.cond μB {b | ∀ r : Fin k, b r ≠ i₀} := by
    have hcomp : P.map B'vec = (P.map Jvec).map redir := by
      rw [hB'_eq_comp, Measure.map_map Measurable.of_discrete hJv_meas]
    rw [hcomp]
    refine measure_ext_of_singleton_fintype fun b₀ ↦ ?_
    rw [measure_map_singleton_fintype (P.map Jvec) redir b₀,
      ProbabilityTheory.cond_apply .of_discrete]
    by_cases hb₀ : ∀ r : Fin k, b₀ r ≠ i₀
    · have hinter : ({b | ∀ r : Fin k, b r ≠ i₀} ∩ {b₀}) = {b₀} := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hb₀, h⟩⟩
      rw [hinter]
      -- Count `(b, u)` with `redir (b, u) = b₀`: for each `r`, either `b r = b₀ r` (`n - 1`
      -- choices of `u r`) or `b r = i₀` and `u r = ⟨b₀ r, hb₀ r⟩` (`1` choice), giving `n^k`.
      have hcard : (Finset.univ.filter
          fun bu : (Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i₀}) ↦ redir bu = b₀).card =
          n ^ k := by
        let stepChoices : (r : Fin k) → Finset (Fin n × {j : Fin n // j ≠ i₀}) := fun r ↦
          Finset.univ.filter fun xu ↦ (if xu.1 = i₀ then xu.2.1 else xu.1) = b₀ r
        have hstep_card : ∀ r : Fin k, (stepChoices r).card = n := by
          intro r
          have hpart : stepChoices r =
              (Finset.univ.map ⟨fun u : {j : Fin n // j ≠ i₀} ↦ (b₀ r, u),
                  fun _ _ h ↦ (Prod.mk.inj h).2⟩) ∪
                {(i₀, ⟨b₀ r, hb₀ r⟩)} := by
            ext ⟨x, u⟩
            simp only [stepChoices, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_union, Finset.mem_map, Finset.mem_singleton]
            by_cases hx : x = i₀
            · subst hx
              simp only [↓reduceIte, Prod.mk.injEq, true_and]
              refine ⟨fun hu ↦ Or.inr (Subtype.ext hu), ?_⟩
              rintro (⟨u', h1⟩ | rfl)
              · exact False.elim (hb₀ r (Prod.mk.inj h1).1)
              · rfl
            · simp only [hx, ↓reduceIte, Prod.mk.injEq, false_and, or_false]
              exact ⟨fun h ↦ ⟨u, Prod.ext h.symm rfl⟩,
                fun ⟨u', h1⟩ ↦ (Prod.mk.inj h1).1.symm⟩
          have hdisj : Disjoint
              (Finset.univ.map ⟨fun u : {j : Fin n // j ≠ i₀} ↦ (b₀ r, u),
                fun _ _ h ↦ (Prod.mk.inj h).2⟩)
              {(i₀, ⟨b₀ r, hb₀ r⟩)} := by
            rw [Finset.disjoint_singleton_right, Finset.mem_map]
            rintro ⟨u, _, hu⟩
            exact hb₀ r (Prod.mk.inj hu).1
          have hcard_sub : Fintype.card {j : Fin n // j ≠ i₀} = n - 1 := by
            rw [Fintype.card_subtype_compl, Fintype.card_fin]
            simp
          rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_univ,
            hcard_sub, Finset.card_singleton]
          omega
        -- Biject the filter with `Fintype.piFinset stepChoices`
        let pairEquiv : ((Fin k → Fin n) × (Fin k → {j : Fin n // j ≠ i₀})) ≃
            (Fin k → Fin n × {j : Fin n // j ≠ i₀}) :=
          { toFun := fun bu r ↦ (bu.1 r, bu.2 r)
            invFun := fun f ↦ (fun r ↦ (f r).1, fun r ↦ (f r).2)
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
        have hmap_filt :
            (Finset.univ.filter fun bu ↦ redir bu = b₀).map pairEquiv.toEmbedding =
              Fintype.piFinset stepChoices := by
          ext f
          simp [pairEquiv, redir, stepChoices, Fintype.mem_piFinset, funext_iff]
        rw [← Finset.card_map pairEquiv.toEmbedding, hmap_filt, Fintype.card_piFinset]
        simp [hstep_card]
      simp_rw [hJ_sing]
      rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_pow,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg n),
        ← ENNReal.ofReal_mul (by positivity)]
      rw [← ofReal_measureReal (μ := μB) (s := {b₀}),
        ← ofReal_measureReal (μ := μB) (s := {b | ∀ r : Fin k, b r ≠ i₀}),
        hp₀_eq, ballBoxMeasure_real_singleton]
      have hb₀_wt : ballBoxRealWeight (fun _ : Fin n ↦ 1 / (n : ℝ)) k b₀ = (1 / (n : ℝ)) ^ k := by
        unfold ballBoxRealWeight
        simp
      rw [hb₀_wt, ← ENNReal.ofReal_inv_of_pos (hp₀_eq ▸ hp₀_pos),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (hp₀_eq ▸ hp₀_pos.le))]
      congr 1
      have h1 : (n : ℝ) ^ k * ((1 / (n : ℝ)) ^ k * (1 / ((n : ℝ) - 1)) ^ k) =
          (1 / ((n : ℝ) - 1)) ^ k := by
        rw [← mul_assoc, ← mul_pow, mul_one_div_cancel hnR_pos.ne', one_pow, one_mul]
      have h2 : ((1 - 1 / (n : ℝ)) ^ k)⁻¹ * (1 / (n : ℝ)) ^ k = (1 / ((n : ℝ) - 1)) ^ k := by
        have hbase : (1 - 1 / (n : ℝ))⁻¹ * (1 / (n : ℝ)) = 1 / ((n : ℝ) - 1) := by
          field_simp [hnR_pos.ne', hn1_pos.ne']
        rw [← inv_pow, ← mul_pow, hbase]
      rw [h1, h2]
    · have hinter : ({b | ∀ r : Fin k, b r ≠ i₀} ∩ {b₀}) = ∅ := by
        ext b
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        exact hb₀ (h2 ▸ h1)
      rw [hinter, measure_empty, mul_zero]
      have hempty_filt : (Finset.univ.filter fun bu ↦ redir bu = b₀) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro bu _ hbu
        push Not at hb₀
        rcases hb₀ with ⟨r, hr⟩
        have hbr := congrFun hbu r
        rw [hr] at hbr
        dsimp [redir] at hbr
        by_cases h1 : bu.1 r = i₀
        · rw [ite_eq_left h1] at hbr
          exact (bu.2 r).2 hbr
        · rw [ite_eq_right h1] at hbr
          exact h1 hbr
      rw [hempty_filt, Finset.sum_empty]
  -- Conjunct 1: conditional law of `(X' j)_{j ≠ i₀}`
  let indRest : (Fin k → Fin n) → ({j : Fin n // j ≠ i₀} → ℕ) :=
    fun b j ↦ if ∀ r : Fin k, b r ≠ j.1 then 1 else 0
  have hB'v_meas : Measurable B'vec := by
    rw [hB'_eq_comp]
    exact Measurable.of_discrete.comp hJv_meas
  have hcond_law :
      P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) =
        (ProbabilityTheory.cond P {ω | X i₀ ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 ω) := by
    have hlhs : P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) =
        (P.map B'vec).map indRest := by
      have hcomp : (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) = indRest ∘ B'vec := rfl
      rw [hcomp, Measure.map_map Measurable.of_discrete hB'v_meas]
    have hset_pre :
        ({ω : Ω | X i₀ ω = 1}) = Bvec ⁻¹' {b : Fin k → Fin n | ∀ r : Fin k, b r ≠ i₀} := by
      ext ω
      by_cases h : ∀ r : Fin k, B r ω ≠ i₀ <;> simp [X, Bvec, h]
    have hrhs_cond :
        (ProbabilityTheory.cond P {ω | X i₀ ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 ω) =
        (ProbabilityTheory.cond μB {b | ∀ r : Fin k, b r ≠ i₀}).map indRest := by
      rw [hset_pre]
      refine Measure.ext fun E hE ↦ ?_
      have hind_meas : Measurable indRest := .of_discrete
      have hX_comp : (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 ω) = indRest ∘ Bvec := rfl
      rw [hX_comp, Measure.map_apply (hind_meas.comp hBv_meas) hE,
        Measure.map_apply hind_meas hE,
        ProbabilityTheory.cond_apply (hBv_meas .of_discrete),
        ProbabilityTheory.cond_apply .of_discrete]
      have hm1 : P (Bvec ⁻¹' {b | ∀ r : Fin k, b r ≠ i₀}) = μB {b | ∀ r : Fin k, b r ≠ i₀} := by
        rw [← hmap_B, Measure.map_apply hBv_meas .of_discrete]
      have hm2 : P (Bvec ⁻¹' {b | ∀ r : Fin k, b r ≠ i₀} ∩ (indRest ∘ Bvec) ⁻¹' E) =
          μB ({b | ∀ r : Fin k, b r ≠ i₀} ∩ indRest ⁻¹' E) := by
        rw [Set.preimage_comp, ← Set.preimage_inter, ← hmap_B,
          Measure.map_apply hBv_meas .of_discrete]
      rw [hm1, hm2]
    rw [hlhs, hmap_B'vec, hrhs_cond]
  -- Conjunct 2: pointwise monotonicity
  have hmono : ∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i₀}, X' j.1 ω ≤ X j.1 ω := by
    intro ω j
    dsimp [X', X]
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      push Not at h2
      rcases h2 with ⟨r, hr⟩
      have hb' : B' r ω = j.1 := by
        dsimp [B']
        rw [hr, ite_eq_right j.2]
      exact h1 r hb'
    · exact Nat.zero_le _
    · exact le_rfl
  -- Conjuncts 1 & 4: `IsExchangeableTuple P X` and `IsSizeBias P W P Ws` via `Cor4_12`
  have hX_meas : ∀ i : Fin n, Measurable (X i) := fun i ↦ by
    have hcomp :
        X i = (fun b : Fin k → Fin n ↦ if ∀ r : Fin k, b r ≠ i then 1 else 0) ∘ Bvec := rfl
    rw [hcomp]
    exact Measurable.of_discrete.comp hBv_meas
  have hexch_nat : IsExchangeableTuple P X := by
    intro σ
    let Φn : (Fin k → Fin n) → (Fin n → ℕ) :=
      fun b i ↦ if ∀ r : Fin k, b r ≠ i then 1 else 0
    let permCfg : (Fin k → Fin n) ≃ (Fin k → Fin n) :=
      { toFun := fun b r ↦ σ.symm (b r)
        invFun := fun b r ↦ σ (b r)
        left_inv := fun b ↦ by ext r; simp
        right_inv := fun b ↦ by ext r; simp }
    have hμB_perm : μB.map permCfg = μB := by
      refine measure_ext_of_singleton_fintype fun b ↦ ?_
      rw [measure_map_singleton_fintype μB permCfg b]
      have hfilt : (Finset.univ.filter fun a : Fin k → Fin n ↦ permCfg a = b) =
          {permCfg.symm b} := by
        ext a
        simp [Equiv.eq_symm_apply]
      rw [hfilt, Finset.sum_singleton, ballBoxMeasure_singleton, ballBoxMeasure_singleton]
      unfold ballBoxWeight
      rfl
    have hmap1 : P.map (fun ω i ↦ X (σ i) ω) = μB.map Φn := by
      have hcomp : (fun ω i ↦ X (σ i) ω) = Φn ∘ permCfg ∘ Bvec := by
        ext ω i
        have hiff : (∀ r : Fin k, B r ω ≠ σ i) ↔ ∀ r : Fin k, σ.symm (B r ω) ≠ i := by
          refine ⟨fun h r hr ↦ h r (by simpa using congrArg σ hr),
            fun h r hr ↦ h r (by simpa using congrArg σ.symm hr)⟩
        by_cases h : ∀ r : Fin k, B r ω ≠ σ i
        · simp [X, Φn, permCfg, Bvec, h, hiff.mp h]
        · simp [X, Φn, permCfg, Bvec, h, mt hiff.mpr h]
      rw [hcomp, ← Measure.map_map Measurable.of_discrete (Measurable.of_discrete.comp hBv_meas),
        ← Measure.map_map Measurable.of_discrete hBv_meas, hmap_B, hμB_perm]
    have hmap2 : P.map (fun ω i ↦ X i ω) = μB.map Φn := by
      have hcomp : (fun ω i ↦ X i ω) = Φn ∘ Bvec := rfl
      rw [hcomp, ← Measure.map_map Measurable.of_discrete hBv_meas, hmap_B]
    exact { aemeasurable_fst := (Measurable.of_eval fun i ↦ hX_meas (σ i)).aemeasurable
            aemeasurable_snd := (Measurable.of_eval hX_meas).aemeasurable
            map_eq := hmap1.trans hmap2.symm }
  have hSB : IsSizeBias P W P Ws := by
    let Xr : Fin n → Ω → ℝ := fun i ω ↦ (X i ω : ℝ)
    let Yr : Ω → ({j : Fin n // j ≠ i₀} → ℝ) := fun ω j ↦ (X' j.1 ω : ℝ)
    let castPi : ({j : Fin n // j ≠ i₀} → ℕ) → ({j : Fin n // j ≠ i₀} → ℝ) :=
      fun u j ↦ (u j : ℝ)
    have hcast : Measurable castPi :=
      Measurable.of_eval fun j ↦
        (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply j)
    have hXr_meas : ∀ i : Fin n, Measurable (Xr i) :=
      fun i ↦ (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (hX_meas i)
    have hXr_zo : ∀ i : Fin n, ∀ᵐ ω ∂P, Xr i ω = 0 ∨ Xr i ω = 1 :=
      fun i ↦ Eventually.of_forall fun ω ↦ by
        by_cases h : ∀ r : Fin k, B r ω ≠ i <;> simp [Xr, X, h]
    have hexch : IsExchangeableTuple P Xr := fun σ ↦
      (hexch_nat σ).comp (Measurable.of_eval fun i ↦
        (Measurable.of_discrete (f := (Nat.cast : ℕ → ℝ))).comp (measurable_pi_apply i))
    have hY_nat_comp : (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) = indRest ∘ B'vec := rfl
    have hY_nat_meas : Measurable (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) := by
      rw [hY_nat_comp]
      exact Measurable.of_discrete.comp hB'v_meas
    have hYr_comp : Yr = castPi ∘ (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) := rfl
    have hYr_meas : AEMeasurable Yr P := by
      rw [hYr_comp]
      exact (hcast.comp hY_nat_meas).aemeasurable
    have hYr_law : 0 < P.real (Xr i₀ ⁻¹' {1}) →
        P.map Yr =
          (ProbabilityTheory.cond P (Xr i₀ ⁻¹' {1})).map
            (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ Xr j.1 ω) := by
      intro _
      have hpre : Xr i₀ ⁻¹' {(1 : ℝ)} = {ω | X i₀ ω = 1} := by
        ext ω
        simp [Xr]
      rw [hpre]
      have h1 : P.map Yr =
          (P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω)).map castPi := by
        rw [hYr_comp, Measure.map_map hcast hY_nat_meas]
      have hX_rest_meas : Measurable (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 ω) := by
        have hcomp : (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 ω) = indRest ∘ Bvec := rfl
        rw [hcomp]
        exact Measurable.of_discrete.comp hBv_meas
      rw [h1, hcond_law, Measure.map_map hcast hX_rest_meas]
      rfl
    exact sizeBias_sum_of_exchangeable_zero_one_fintype P P i₀ hXr_meas hXr_zo hexch
      hYr_meas hYr_law
  exact ⟨hexch_nat, hcond_law, hmono, hSB⟩

/-! ### Part 3: Example 4.15 Restricted Bound (`2 ≤ n`, `SteinIntro.tex:2540-2551`) -/

/-- **Example 4.15, restricted to $2 \le n$** (`\label{ex123}`, eq. `(4.13)` `\label{129}`,
`SteinIntro.tex:2526-2551`): exact avoidance probabilities, mean, variance, eq. `(4.13)` Poisson
total-variation bound, and full-collection error bound for $2 \le n$ boxes. -/
theorem ex4_15_restricted
    {n k : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ}
    (hn : 2 ≤ n)
    (hB_meas : ∀ r : Fin k, Measurable (B r))
    (hB_indep : ProbabilityTheory.iIndepFun B P)
    (hB_prob : ∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = 1 / (n : ℝ)) :
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, if ∀ t : Fin k, B t ω ≠ i then 1 else 0
    let lam : ℝ := (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k
    let err : ℝ := min 1 lam *
      ((1 - 1 / (n : ℝ)) ^ k +
        ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k))
    (r : ℝ) = lam →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    0 < r ∧
      (∀ i : Fin n, P.real {ω | ∀ t : Fin k, B t ω ≠ i} = (((n : ℝ) - 1) / (n : ℝ)) ^ k) ∧
      (∀ i j : Fin n, j ≠ i →
        P.real {ω | (∀ t : Fin k, B t ω ≠ i) ∧ (∀ t : Fin k, B t ω ≠ j)} =
          (((n : ℝ) - 2) / (n : ℝ)) ^ k) ∧
      ∫ ω, (W ω : ℝ) ∂P = lam ∧
      ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
        lam * (1 - (1 - 1 / (n : ℝ)) ^ k) +
          (n : ℝ) * ((n : ℝ) - 1) *
            ((1 - 2 / (n : ℝ)) ^ k - (1 - 1 / (n : ℝ)) ^ (2 * k)) ∧
      tvDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal err ∧
      |P.real {ω | W ω = 0} - Real.exp (-lam)| ≤ err := by
  intro W lam err hr_eq hZ_meas hZ_law
  have hn_pos : 0 < n := by omega
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn1_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbase_pos : 0 < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < 1 := (div_lt_one hnR_pos).mpr (by exact_mod_cast hn)
    linarith
  have hlam_pos : 0 < lam := mul_pos hnR_pos (pow_pos hbase_pos k)
  have hr_pos : 0 < r := NNReal.coe_pos.mp (hr_eq ▸ hlam_pos)
  let p : Fin n → ℝ := fun _ ↦ 1 / (n : ℝ)
  let μ := ballBoxMeasure p (unifProb_nn n) (unifProb_sum hn_pos) k
  have hBM : Measurable (fun ω t ↦ B t ω) := Measurable.of_eval hB_meas
  have hmap_B : P.map (fun ω t ↦ B t ω) = μ :=
    map_pi_eq_ballBoxMeasure P (unifProb_nn n) (unifProb_sum hn_pos) hB_meas hB_indep hB_prob
  have hmean : ∫ ω, (W ω : ℝ) ∂P = lam := by
    let f_emp : (Fin k → Fin n) → ℝ := fun b ↦ (emptyBoxCount b : ℝ)
    have hcomp : ∀ ω, (W ω : ℝ) = f_emp (fun t ↦ B t ω) := fun _ ↦ rfl
    simp_rw [hcomp]
    rw [(integral_map hBM.aemeasurable
      (Measurable.of_discrete (f := f_emp)).aestronglyMeasurable).symm, hmap_B]
    dsimp [f_emp]
    rw [ballBox_empty_mean]
    simp [p, lam]
  have hvar : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      lam * (1 - (1 - 1 / (n : ℝ)) ^ k) +
        (n : ℝ) * ((n : ℝ) - 1) *
          ((1 - 2 / (n : ℝ)) ^ k - (1 - 1 / (n : ℝ)) ^ (2 * k)) := by
    have hv := ProbabilityTheory.variance_map (μ := P)
      (X := fun b : Fin k → Fin n ↦ (emptyBoxCount b : ℝ)) (Y := fun ω t ↦ B t ω)
      Measurable.of_discrete.aemeasurable hBM.aemeasurable
    rw [hmap_B] at hv
    change ProbabilityTheory.variance ((fun b ↦ (emptyBoxCount b : ℝ)) ∘ (fun ω t ↦ B t ω)) P = _
    rw [← hv, ballBox_empty_variance]
    have h1 : (∑ _i : Fin n, ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / (n : ℝ)) ^ (2 * k))) =
        lam * (1 - (1 - 1 / (n : ℝ)) ^ k) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, lam]
      rw [two_mul, pow_add]
      ring
    have h2 : (∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i,
          ((1 - 1 / (n : ℝ) - 1 / (n : ℝ)) ^ k -
            (1 - 1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ k)) =
        (n : ℝ) * ((n : ℝ) - 1) *
          ((1 - 2 / (n : ℝ)) ^ k - (1 - 1 / (n : ℝ)) ^ (2 * k)) := by
      have hcard_er : ∀ i : Fin n, ((Finset.univ.erase i).card : ℝ) = (n : ℝ) - 1 := by
        intro i
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
          Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      have hinner : ∀ i : Fin n,
          (∑ _j ∈ Finset.univ.erase i,
            ((1 - 1 / (n : ℝ) - 1 / (n : ℝ)) ^ k -
              (1 - 1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ k)) =
          ((n : ℝ) - 1) * ((1 - 2 / (n : ℝ)) ^ k - (1 - 1 / (n : ℝ)) ^ (2 * k)) := by
        intro i
        rw [Finset.sum_const, nsmul_eq_mul, hcard_er i]
        congr 1
        have hsub2 : 1 - 1 / (n : ℝ) - 1 / (n : ℝ) = 1 - 2 / (n : ℝ) := by ring
        rw [hsub2, two_mul, pow_add]
      simp_rw [hinner]
      simp [mul_assoc]
    simpa only [p] using congrArg₂ (· + ·) h1 h2
  have hprob1 : ∀ i : Fin n,
      P.real {ω | ∀ t : Fin k, B t ω ≠ i} = (((n : ℝ) - 1) / (n : ℝ)) ^ k := by
    intro i
    change P.real ((fun ω t ↦ B t ω) ⁻¹' {b | ∀ t : Fin k, b t ≠ i}) = _
    rw [← map_measureReal_apply hBM .of_discrete, hmap_B, ballBox_prob_avoid_one]
    congr 1
    dsimp [p]
    field_simp [hnR_pos.ne']
  have hprob2 : ∀ i j : Fin n, j ≠ i →
      P.real {ω | (∀ t : Fin k, B t ω ≠ i) ∧ (∀ t : Fin k, B t ω ≠ j)} =
        (((n : ℝ) - 2) / (n : ℝ)) ^ k := by
    intro i j hij
    change P.real ((fun ω t ↦ B t ω) ⁻¹' {b | (∀ t : Fin k, b t ≠ i) ∧ (∀ t : Fin k, b t ≠ j)}) = _
    rw [← map_measureReal_apply hBM .of_discrete, hmap_B, ballBox_prob_avoid_two _ _ hij]
    congr 1
    dsimp [p]
    field_simp [hnR_pos.ne']
    ring
  have htv : tvDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal err := by
    let W0 : Ω → ℕ := fun ω ↦
      ∑ i : Fin n, if ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card ≤ 0
        then 1 else 0
    have hW_eq_W0 : W = W0 := by
      funext ω
      exact emptyBoxCount_eq_atMost_zero (fun t ↦ B t ω)
    rw [hW_eq_W0]
    have hmean0 : (r : ℝ) = ∫ ω, (W0 ω : ℝ) ∂P := by rw [← hW_eq_W0, hmean, hr_eq]
    have hbound := (rem4_17_atMost P P' (m := 0) (unifProb_nn n) (unifProb_sum hn_pos)
      hB_meas hB_indep hB_prob hr_pos hmean0 hZ_meas hZ_law).2
    change tvDist (P.map W0) (P'.map Z) ≤ ENNReal.ofReal
      (min 1 (r : ℝ) * (1 - ProbabilityTheory.variance (fun ω ↦ (W0 ω : ℝ)) P / (r : ℝ)))
      at hbound
    rw [← hW_eq_W0] at hbound ⊢
    -- Identify `1 - variance / lam` algebraically with eq. `(4.13)`
    have hprod_pow : (1 - 2 / (n : ℝ)) ^ k =
        (1 - 1 / (n : ℝ)) ^ k * (1 - 1 / ((n : ℝ) - 1)) ^ k := by
      rw [← mul_pow]
      congr 1
      field_simp [hnR_pos.ne', hn1_pos.ne']
      ring
    have halg : 1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ) =
        (1 - 1 / (n : ℝ)) ^ k +
          ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k) := by
      rw [hr_eq, hvar, hprod_pow]
      have hpow_ne : (1 - 1 / (n : ℝ)) ^ k ≠ 0 := (pow_pos hbase_pos k).ne'
      have h2k : (1 - 1 / (n : ℝ)) ^ (2 * k) = (1 - 1 / (n : ℝ)) ^ k * (1 - 1 / (n : ℝ)) ^ k := by
        rw [two_mul, pow_add]
      rw [h2k]
      dsimp only [lam]
      field_simp [hnR_pos.ne', hpow_ne]
      ring
    rwa [halg, hr_eq] at hbound
  have hzero_err : |P.real {ω | W ω = 0} - Real.exp (-lam)| ≤ err := by
    have hW_meas : Measurable W := by
      have hcomp : W = emptyBoxCount ∘ (fun ω t ↦ B t ω) := rfl
      rw [hcomp]
      exact Measurable.of_discrete.comp hBM
    have : IsProbabilityMeasure (P.map W) :=
      (Measure.isProbabilityMeasure_map_iff hW_meas.aemeasurable).mpr ‹_›
    have : IsProbabilityMeasure (P'.map Z) :=
      (Measure.isProbabilityMeasure_map_iff hZ_meas).mpr ‹_›
    have hlb : ENNReal.ofReal |(P.map W).real {0} - (P'.map Z).real {0}| ≤
        tvDist (P.map W) (P'.map Z) := by
      rw [tvDist_eq_iSup]
      exact le_iSup₂
        (f := fun (A : Set ℕ) (_ : MeasurableSet A) ↦
          ENNReal.ofReal |(P.map W).real A - (P'.map Z).real A|)
        ({0} : Set ℕ) (measurableSet_singleton 0)
    have hW0 : (P.map W).real {0} = P.real {ω | W ω = 0} :=
      map_measureReal_apply hW_meas (measurableSet_singleton 0)
    have hZ0 : (P'.map Z).real {0} = Real.exp (-lam) := by
      rw [hZ_law, ← hr_eq]
      simpa [poissonLaw] using ProbabilityTheory.poissonMeasure_real_singleton r 0
    have herr_nn : 0 ≤ err := by
      have hratio : 1 - 1 / ((n : ℝ) - 1) ≤ 1 - 1 / (n : ℝ) := by
        have : 1 / (n : ℝ) ≤ 1 / ((n : ℝ) - 1) :=
          one_div_le_one_div_of_le hn1_pos (by linarith)
        linarith
      have hpow_le : (1 - 1 / ((n : ℝ) - 1)) ^ k ≤ (1 - 1 / (n : ℝ)) ^ k := by
        by_cases hn2_eq : n = 2
        · subst hn2_eq
          rcases k with _ | k' <;> norm_num
        · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
          have hnn : 0 ≤ 1 - 1 / ((n : ℝ) - 1) := by
            have : 1 / ((n : ℝ) - 1) ≤ 1 := (div_le_one hn1_pos).mpr (by linarith)
            linarith
          exact pow_le_pow_left₀ hnn hratio k
      have hbr_nn : 0 ≤ (1 - 1 / (n : ℝ)) ^ k +
          ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k) :=
        add_nonneg (pow_nonneg hbase_pos.le k) (mul_nonneg hn1_pos.le (sub_nonneg.mpr hpow_le))
      exact mul_nonneg (le_min zero_le_one hlam_pos.le) hbr_nn
    rw [hW0, hZ0] at hlb
    exact (ENNReal.ofReal_le_ofReal_iff herr_nn).mp (hlb.trans htv)
  exact ⟨hr_pos, hprob1, hprob2, hmean, hvar, htv, hzero_err⟩

/-! ### Part 4: Asymptotic Inequalities & Rate (`SteinIntro.tex:2553-2564`) -/

/-- **Example 4.15, eq. `(4.13)` algebraic identity and linear upper bound for $2 \le n$**
(`\label{ex123}`, `SteinIntro.tex:2554-2560`; `review-05G4` item 2): for all $2 \le n$ and
$k \in \mathbb{N}$, setting $a = \frac{n(n - 2)}{(n - 1)^2}$ and $\lambda = n(1 - 1/n)^k$,
eq. `(4.13)` equals $\min\{1, \lambda\}(\frac{\lambda}{n} + \frac{n - 1}{n}\lambda(1 - a^k))$ and
is at most $\frac{\lambda}{n} + \lambda(1 - a^k)$. -/
theorem ex4_15_eq413_identity {n k : ℕ} (hn : 2 ≤ n) :
    let a : ℝ := (n : ℝ) * ((n : ℝ) - 2) / ((n : ℝ) - 1) ^ 2
    let lam : ℝ := (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k
    min 1 lam *
        ((1 - 1 / (n : ℝ)) ^ k +
          ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) =
      min 1 lam * (lam / (n : ℝ) + (((n : ℝ) - 1) / (n : ℝ)) * lam * (1 - a ^ k)) ∧
    min 1 lam *
        ((1 - 1 / (n : ℝ)) ^ k +
          ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) ≤
      lam / (n : ℝ) + lam * (1 - a ^ k) := by
  intro a lam
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have ha_nn : 0 ≤ a :=
    div_nonneg (mul_nonneg hn_pos.le (by linarith)) (sq_nonneg ((n : ℝ) - 1))
  have ha_le_one : a ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hn1_pos)]
    nlinarith
  have hratio : 1 - 1 / ((n : ℝ) - 1) = (1 - 1 / (n : ℝ)) * a := by
    dsimp [a]
    field_simp [hn_pos.ne', hn1_pos.ne']
    ring
  have hpow_eq : (1 - 1 / ((n : ℝ) - 1)) ^ k = (1 - 1 / (n : ℝ)) ^ k * a ^ k := by
    rw [hratio, mul_pow]
  have hexact : min 1 lam *
      ((1 - 1 / (n : ℝ)) ^ k +
        ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) =
      min 1 lam * (lam / (n : ℝ) + (((n : ℝ) - 1) / (n : ℝ)) * lam * (1 - a ^ k)) := by
    congr 1
    rw [hpow_eq]
    dsimp [lam]
    field_simp [hn_pos.ne']
  have hineq3 :
      min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) ≤
        lam / (n : ℝ) + lam * (1 - a ^ k) := by
    have hak_le : a ^ k ≤ 1 := pow_le_one₀ ha_nn ha_le_one
    have hbase_nn : 0 ≤ 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) ≤ 1 := (div_le_one hn_pos).mpr (by linarith)
      linarith
    have hpk_nn : 0 ≤ (1 - 1 / (n : ℝ)) ^ k := pow_nonneg hbase_nn k
    have hdiff_nn : 0 ≤ (1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k := by
      rw [hpow_eq]
      nlinarith
    have hbr_nn : 0 ≤ (1 - 1 / (n : ℝ)) ^ k +
        ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k) :=
      add_nonneg hpk_nn (mul_nonneg hn1_pos.le hdiff_nn)
    calc min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k))
      _ ≤ 1 * ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) :=
        mul_le_mul_of_nonneg_right (min_le_left 1 lam) hbr_nn
      _ = lam / (n : ℝ) + (((n : ℝ) - 1) / (n : ℝ)) * (lam * (1 - a ^ k)) := by
        rw [one_mul, hpow_eq]
        dsimp [lam]
        field_simp [hn_pos.ne']
      _ ≤ lam / (n : ℝ) + 1 * (lam * (1 - a ^ k)) := by
        refine add_le_add le_rfl ?_
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (mul_nonneg hn_pos.le hpk_nn) (by linarith))
        rw [div_le_one hn_pos]
        linarith
      _ = lam / (n : ℝ) + lam * (1 - a ^ k) := by ring
  exact ⟨hexact, hineq3⟩

/-- **Example 4.15, intermediate analytic identity and logarithmic bounds** (`\label{ex123}`,
`SteinIntro.tex:2554-2560`; `review-05G4` item 2): for $a = \frac{n(n - 2)}{(n - 1)^2}$ and
$\lambda = n(1 - 1/n)^k$, eq. `(4.13)` equals
$\min\{1, \lambda\}(\frac{\lambda}{n} + \frac{n - 1}{n}\lambda(1 - a^k))$ and is at most
$\frac{\lambda}{n} + \lambda(1 - a^k)$ for all $2 \le n$, and for $3 \le n$ satisfies
$1 - a^k \le k \log(\frac{(n - 1)^2}{n(n - 2)}) \le \frac{k}{n(n - 2)}$. -/
theorem ex4_15_asymptotic_bounds {n k : ℕ} :
    let a : ℝ := (n : ℝ) * ((n : ℝ) - 2) / ((n : ℝ) - 1) ^ 2
    let lam : ℝ := (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k
    (2 ≤ n →
      min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) =
        min 1 lam * (lam / (n : ℝ) + (((n : ℝ) - 1) / (n : ℝ)) * lam * (1 - a ^ k)) ∧
      min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) ≤
        lam / (n : ℝ) + lam * (1 - a ^ k)) ∧
    (3 ≤ n →
      1 - a ^ k ≤ (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) ∧
      (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) ≤
        (k : ℝ) / ((n : ℝ) * ((n : ℝ) - 2))) := by
  intro a lam
  refine ⟨fun hn2 ↦ ex4_15_eq413_identity hn2, fun hn3 ↦ ?_⟩
  have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn_pos : (0 : ℝ) < n := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn2_pos : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  have hprod_pos : 0 < (n : ℝ) * ((n : ℝ) - 2) := mul_pos hn_pos hn2_pos
  have ha_pos : 0 < a := div_pos hprod_pos (sq_pos_of_pos hn1_pos)
  have hineq1 : 1 - a ^ k ≤
      (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) := by
    have hinv : ((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2)) = a⁻¹ := by
      dsimp [a]
      rw [inv_div]
    rw [hinv, Real.log_inv, mul_neg]
    have hexp : a ^ k = Real.exp ((k : ℝ) * Real.log a) := by
      rw [← Real.exp_log ha_pos, ← Real.exp_nat_mul, Real.log_exp]
    have h1 := Real.add_one_le_exp ((k : ℝ) * Real.log a)
    linarith
  have hineq2 :
      (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) ≤
        (k : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) := by
    have h1 : ((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2)) =
        1 + 1 / ((n : ℝ) * ((n : ℝ) - 2)) := by
      field_simp [hprod_pos.ne']
      ring
    have harg_pos : 0 < 1 + 1 / ((n : ℝ) * ((n : ℝ) - 2)) := by positivity
    have hlog := Real.log_le_sub_one_of_pos harg_pos
    rw [h1]
    have hlog' : Real.log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 2))) ≤
        1 / ((n : ℝ) * ((n : ℝ) - 2)) := by linarith
    calc (k : ℝ) * Real.log (1 + 1 / ((n : ℝ) * ((n : ℝ) - 2)))
      _ ≤ (k : ℝ) * (1 / ((n : ℝ) * ((n : ℝ) - 2))) :=
        mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg k)
      _ = (k : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) := mul_one_div _ _
  exact ⟨hineq1, hineq2⟩

/-- Compatibility corollary for `ex4_15_asymptotic_bounds` on $3 \le n$
(`SteinIntro.tex:2554-2560`; see `ex4_15_eq413_identity` and `ex4_15_asymptotic_bounds` for the
$2 \le n$ `(4.13)` identity). -/
theorem ex4_15_asymptotic_ineq {n k : ℕ} (hn : 3 ≤ n) :
    let a : ℝ := (n : ℝ) * ((n : ℝ) - 2) / ((n : ℝ) - 1) ^ 2
    let lam : ℝ := (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k
    0 < (n : ℝ) * ((n : ℝ) - 2) ∧
      min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) =
        min 1 lam * (lam / (n : ℝ) + (((n : ℝ) - 1) / (n : ℝ)) * lam * (1 - a ^ k)) ∧
      1 - a ^ k ≤ (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) ∧
      (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) ≤
        (k : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)) ∧
      min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) ≤
        lam / (n : ℝ) + lam * (1 - a ^ k) := by
  intro a lam
  have hb := ex4_15_asymptotic_bounds (n := n) (k := k)
  have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨mul_pos (by linarith) (by linarith), (hb.1 (by omega)).1, (hb.2 hn).1, (hb.2 hn).2,
    (hb.1 (by omega)).2⟩

private lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← hsq, Real.log_pow]
    norm_num
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Example 4.15, asymptotic coupon-collecting rate** (`\label{ex123}`,
`SteinIntro.tex:2553-2564`): when $|k_n - (n \log n - c n)| \le 1$ eventually,
$\lambda_n = n(1 - 1/n)^{k_n} \to e^c$ and $d_{\mathrm{TV}}(W_n, \mathrm{Po}(\lambda_n)) \le
C \log(n)/n$ eventually. -/
theorem ex4_15_rate {c : ℝ} {k : ℕ → ℕ}
    (hk : ∀ᶠ n : ℕ in Filter.atTop,
      |(k n : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - c * (n : ℝ))| ≤ 1) :
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k n)
        Filter.atTop (nhds (Real.exp c)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          {B : Fin (k n) → Ω → Fin n} {r : ℝ≥0},
          (∀ t : Fin (k n), Measurable (B t)) →
          ProbabilityTheory.iIndepFun B P →
          (∀ t : Fin (k n), ∀ i : Fin n, P.real {ω | B t ω = i} = 1 / (n : ℝ)) →
          (r : ℝ) = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k n →
          let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, if ∀ t : Fin (k n), B t ω ≠ i then 1 else 0
          tvDist (P.map W) (poissonLaw r) ≤ ENNReal.ofReal (C * Real.log (n : ℝ) / (n : ℝ)) := by
  -- Part 1: show `log(n * (1 - 1/n)^(k n)) → c`, hence `lam_n → exp c`
  let L : ℕ → ℝ := fun n ↦ Real.log (n : ℝ) + (k n : ℝ) * Real.log (1 - 1 / (n : ℝ))
  have hL_tendsto : Filter.Tendsto L Filter.atTop (nhds c) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hk
    -- Choose `N` large enough that `1/n + 8/√n + 4(|c| + 1)/n < ε`
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (max 4 ((32 / ε) ^ 2 + (16 * (|c| + 1) / ε) + 1))
    use max N₀ N₁
    intro n hn_ge
    have hn0 : N₀ ≤ n := (le_max_left N₀ N₁).trans hn_ge
    have hn1 : N₁ ≤ n := (le_max_right N₀ N₁).trans hn_ge
    have hgt := hN₁.trans_le (by exact_mod_cast hn1 : (N₁ : ℝ) ≤ n)
    have hn4 : (4 : ℝ) < n := (le_max_left _ _).trans_lt hgt
    have hn_pos : (0 : ℝ) < n := by linarith
    have hn_sub1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have h1mn_pos : 0 < 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr (by linarith)
      linarith
    -- Bound `|log(1 - 1/n) + 1/n| ≤ 1 / (n * (n - 1))`
    have hlog_ub : Real.log (1 - 1 / (n : ℝ)) ≤ -(1 / (n : ℝ)) := by
      have h := Real.log_le_sub_one_of_pos h1mn_pos
      linarith
    have hlog_lb : -(1 / ((n : ℝ) - 1)) ≤ Real.log (1 - 1 / (n : ℝ)) := by
      have hinv : (1 - 1 / (n : ℝ))⁻¹ = 1 + 1 / ((n : ℝ) - 1) := by
        field_simp [hn_pos.ne', hn_sub1_pos.ne']
        ring
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / ((n : ℝ) - 1))
      rw [← hinv, Real.log_inv] at h
      linarith
    have herr_log :
        |Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)| ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [abs_le]
      constructor
      · have hdiff : 1 / (n : ℝ) - 1 / ((n : ℝ) - 1) =
            -(1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
          field_simp [hn_pos.ne', hn_sub1_pos.ne']
          ring
        linarith
      · have : 0 ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by positivity
        linarith
    -- Bound `k n`
    have hk_bd := hN₀ n hn0
    have hk_le : (k n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) + |c| * (n : ℝ) + 1 := by
      have h1 := (abs_le.mp hk_bd).2
      have h2 : -c * (n : ℝ) ≤ |c| * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (neg_le_abs c) hn_pos.le
      linarith
    -- Decompose `L n - c`
    have hdecomp : L n - c =
        (((n : ℝ) * Real.log (n : ℝ) - c * (n : ℝ) - (k n : ℝ)) / (n : ℝ)) +
          (k n : ℝ) * (Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)) := by
      dsimp [L]
      field_simp [hn_pos.ne']
      ring
    rw [Real.dist_eq, hdecomp]
    have ht1 : |((n : ℝ) * Real.log (n : ℝ) - c * (n : ℝ) - (k n : ℝ)) / (n : ℝ)| ≤
        1 / (n : ℝ) := by
      rw [abs_div, abs_of_pos hn_pos, abs_sub_comm]
      exact div_le_div_of_nonneg_right hk_bd hn_pos.le
    have ht2 : |(k n : ℝ) * (Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))| ≤
        ((n : ℝ) * Real.log (n : ℝ) + (|c| + 1) * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      have hk_le' : (k n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) + (|c| + 1) * (n : ℝ) := by linarith
      calc (k n : ℝ) * |Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ)|
        _ ≤ ((n : ℝ) * Real.log (n : ℝ) + (|c| + 1) * (n : ℝ)) *
              (1 / ((n : ℝ) * ((n : ℝ) - 1))) :=
          mul_le_mul hk_le' herr_log (abs_nonneg _) (by positivity)
        _ = ((n : ℝ) * Real.log (n : ℝ) + (|c| + 1) * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) :=
          mul_one_div _ _
    have hn_half : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
    have ht2' : ((n : ℝ) * Real.log (n : ℝ) + (|c| + 1) * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
        4 / Real.sqrt (n : ℝ) + 2 * (|c| + 1) / (n : ℝ) := by
      have hdiv1 : ((n : ℝ) * Real.log (n : ℝ) + (|c| + 1) * (n : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)) =
          (Real.log (n : ℝ) + (|c| + 1)) / ((n : ℝ) - 1) := by
        field_simp [hn_pos.ne', hn_sub1_pos.ne']
      rw [hdiv1]
      have hlog_n := log_le_two_sqrt hn_pos
      have hnum_nn : 0 ≤ Real.log (n : ℝ) + (|c| + 1) :=
        add_nonneg (Real.log_nonneg (by linarith)) (by positivity)
      calc (Real.log (n : ℝ) + (|c| + 1)) / ((n : ℝ) - 1)
        _ ≤ (Real.log (n : ℝ) + (|c| + 1)) / ((n : ℝ) / 2) :=
          div_le_div_of_nonneg_left hnum_nn (by positivity) hn_half
        _ ≤ (2 * Real.sqrt (n : ℝ) + (|c| + 1)) / ((n : ℝ) / 2) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ = 4 * Real.sqrt (n : ℝ) / (n : ℝ) + 2 * (|c| + 1) / (n : ℝ) := by ring
        _ = 4 / Real.sqrt (n : ℝ) + 2 * (|c| + 1) / (n : ℝ) := by
          congr 1
          have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
            Real.mul_self_sqrt hn_pos.le
          have hsq_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
          field_simp [hn_pos.ne', hsq_pos.ne']
          linarith
    -- Combine with `n > (32 / ε)^2 + 16(|c| + 1) / ε + 1`
    have hgt2 : (32 / ε) ^ 2 + (16 * (|c| + 1) / ε) + 1 < (n : ℝ) :=
      (le_max_right _ _).trans_lt hgt
    have hsqrt_gt : 32 / ε < Real.sqrt (n : ℝ) := by
      have h1 : (32 / ε) ^ 2 < (n : ℝ) := by
        have : 0 ≤ 16 * (|c| + 1) / ε := by positivity
        linarith
      exact (Real.lt_sqrt (by positivity)).mpr h1
    have h4_sqrt : 4 / Real.sqrt (n : ℝ) < ε / 8 := by
      rw [div_lt_iff₀ (Real.sqrt_pos.mpr hn_pos)]
      have h1 : 32 < Real.sqrt (n : ℝ) * ε := (div_lt_iff₀ hε).mp hsqrt_gt
      linarith
    have hn_gt_c : 16 * (|c| + 1) / ε < (n : ℝ) := by
      have : 0 ≤ (32 / ε) ^ 2 := sq_nonneg _
      linarith
    have hc_part : 1 / (n : ℝ) + 2 * (|c| + 1) / (n : ℝ) < ε / 2 := by
      have h1 : 16 * (|c| + 1) < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn_gt_c
      have h2 : 1 + 2 * (|c| + 1) ≤ 3 * (|c| + 1) := by
        have : 0 ≤ |c| := abs_nonneg c
        linarith
      rw [← add_div, div_lt_iff₀ hn_pos]
      have : 0 ≤ |c| := abs_nonneg c
      linarith
    calc |((n : ℝ) * Real.log (n : ℝ) - c * (n : ℝ) - (k n : ℝ)) / (n : ℝ) +
          (k n : ℝ) * (Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))|
      _ ≤ |((n : ℝ) * Real.log (n : ℝ) - c * (n : ℝ) - (k n : ℝ)) / (n : ℝ)| +
          |(k n : ℝ) * (Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ))| := abs_add_le _ _
      _ ≤ 1 / (n : ℝ) + (4 / Real.sqrt (n : ℝ) + 2 * (|c| + 1) / (n : ℝ)) :=
        add_le_add ht1 (ht2.trans ht2')
      _ < ε := by linarith
  have hlam_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k n)
        Filter.atTop (nhds (Real.exp c)) := by
    have hexp_L : Filter.Tendsto (fun n : ℕ ↦ Real.exp (L n))
        Filter.atTop (nhds (Real.exp c)) :=
      (Real.continuous_exp.tendsto c).comp hL_tendsto
    refine hexp_L.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn2
    have hn_pos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    have h1mn_pos : 0 < 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) < 1 := (div_lt_one hn_pos).mpr (by exact_mod_cast hn2)
      linarith
    dsimp [L]
    rw [Real.exp_add, Real.exp_log hn_pos, Real.exp_nat_mul, Real.exp_log h1mn_pos]
  -- Part 2: `O(log n / n)` TV rate eventually
  refine ⟨hlam_tendsto, ?_⟩
  let C : ℝ := 2 * Real.exp c * (1 + 2 * (2 + |c|))
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, ?_⟩
  have hlam_lt : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k n < 2 * Real.exp c :=
    (tendsto_order.mp hlam_tendsto).2 (2 * Real.exp c) (by linarith [Real.exp_pos c])
  filter_upwards [hk, hlam_lt, Filter.eventually_ge_atTop 4] with n hkn hlam_ub hn4
    Ω _ P _ B r hB_meas hB_indep hB_prob hr_eq
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn_pos : (0 : ℝ) < n := by linarith
  -- Apply `ex4_15_restricted` with `P' = poissonLaw r, Z = id` and `ex4_15_asymptotic_ineq`
  have hrest := (ex4_15_restricted P (poissonLaw r) (Z := id) hn2 hB_meas hB_indep hB_prob
    hr_eq aemeasurable_id Measure.map_id).2.2.2.2.2.1
  rw [Measure.map_id] at hrest
  have hasymp := ex4_15_asymptotic_ineq (k := k n) hn3
  set lam : ℝ := (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k n
  set a : ℝ := (n : ℝ) * ((n : ℝ) - 2) / ((n : ℝ) - 1) ^ 2
  have hbase_nn : 0 ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := (div_le_one hn_pos).mpr (by linarith)
    linarith
  have hlam_nn : 0 ≤ lam := mul_nonneg hn_pos.le (pow_nonneg hbase_nn _)
  have h1 : min 1 lam *
      ((1 - 1 / (n : ℝ)) ^ k n +
        ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k n - (1 - 1 / ((n : ℝ) - 1)) ^ k n)) ≤
      lam / (n : ℝ) + lam * ((k n : ℝ) / ((n : ℝ) * ((n : ℝ) - 2))) := by
    calc min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k n +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k n - (1 - 1 / ((n : ℝ) - 1)) ^ k n))
      _ ≤ lam / (n : ℝ) + lam * (1 - a ^ k n) := hasymp.2.2.2.2
      _ ≤ lam / (n : ℝ) + lam * ((k n : ℝ) / ((n : ℝ) * ((n : ℝ) - 2))) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (hasymp.2.2.1.trans hasymp.2.2.2.1) hlam_nn)
  -- Note `log n ≥ log 4 ≥ 1` for `n ≥ 4` (since `4 > exp 1` from `1/2 ≤ exp(-1/2)`)
  have hlog_ge1 : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hn_pos]
    have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
      have h := Real.add_one_le_exp (-1 / 2 : ℝ)
      linarith
    have hquarter : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
      have hsq := pow_le_pow_left₀ (by norm_num) hhalf 2
      rw [← Real.exp_nat_mul] at hsq
      norm_num at hsq
      exact hsq
    have hexp1_le4 : Real.exp 1 ≤ 4 := by
      have hprod : Real.exp 1 * Real.exp (-1) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have hmul := mul_le_mul_of_nonneg_left hquarter (Real.exp_pos 1).le
      linarith
    linarith
  have hkn_le : (k n : ℝ) ≤ (2 + |c|) * (n : ℝ) * Real.log (n : ℝ) := by
    have h1' := (abs_le.mp hkn).2
    have h2' : -c * (n : ℝ) ≤ |c| * (n : ℝ) * Real.log (n : ℝ) := by
      calc -c * (n : ℝ)
        _ ≤ |c| * (n : ℝ) * 1 := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (neg_le_abs c) hn_pos.le
        _ ≤ |c| * (n : ℝ) * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
    have h3' : (1 : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by nlinarith
    linarith
  have hn_sub2_ge : (n : ℝ) / 2 ≤ (n : ℝ) - 2 := by linarith
  have h2 : lam / (n : ℝ) + lam * ((k n : ℝ) / ((n : ℝ) * ((n : ℝ) - 2))) ≤
      C * Real.log (n : ℝ) / (n : ℝ) := by
    have ht_a : lam / (n : ℝ) ≤ 2 * Real.exp c * Real.log (n : ℝ) / (n : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ hn_pos.le
      calc lam = lam * 1 := (mul_one lam).symm
        _ ≤ (2 * Real.exp c) * Real.log (n : ℝ) :=
          mul_le_mul hlam_ub.le hlog_ge1 zero_le_one (by positivity)
    have ht_b : lam * ((k n : ℝ) / ((n : ℝ) * ((n : ℝ) - 2))) ≤
        2 * Real.exp c * (2 * (2 + |c|)) * Real.log (n : ℝ) / (n : ℝ) := by
      have hden_le : (n : ℝ) * ((n : ℝ) / 2) ≤ (n : ℝ) * ((n : ℝ) - 2) :=
        mul_le_mul_of_nonneg_left hn_sub2_ge hn_pos.le
      calc lam * ((k n : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)))
        _ ≤ (2 * Real.exp c) *
              (((2 + |c|) * (n : ℝ) * Real.log (n : ℝ)) / ((n : ℝ) * ((n : ℝ) / 2))) := by
          refine mul_le_mul hlam_ub.le ?_
            (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hn_pos.le (by linarith))) (by positivity)
          calc (k n : ℝ) / ((n : ℝ) * ((n : ℝ) - 2))
            _ ≤ (k n : ℝ) / ((n : ℝ) * ((n : ℝ) / 2)) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hden_le
            _ ≤ ((2 + |c|) * (n : ℝ) * Real.log (n : ℝ)) / ((n : ℝ) * ((n : ℝ) / 2)) :=
              div_le_div_of_nonneg_right hkn_le (by positivity)
        _ = 2 * Real.exp c * (2 * (2 + |c|)) * Real.log (n : ℝ) / (n : ℝ) := by
          field_simp [hn_pos.ne']
    calc lam / (n : ℝ) + lam * ((k n : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)))
      _ ≤ 2 * Real.exp c * Real.log (n : ℝ) / (n : ℝ) +
            2 * Real.exp c * (2 * (2 + |c|)) * Real.log (n : ℝ) / (n : ℝ) :=
        add_le_add ht_a ht_b
      _ = C * Real.log (n : ℝ) / (n : ℝ) := by
        dsimp [C]
        ring
  exact hrest.trans (ENNReal.ofReal_le_ofReal (h1.trans h2))

end SteinMethod
