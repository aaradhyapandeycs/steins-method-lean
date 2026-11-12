/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.PoissonSizeBias.Monotone.Basic
import Formalization.PoissonSizeBias.Monotone.Lemma4_18
import Formalization.PoissonSizeBias.Monotone.FKG
import Formalization.PoissonSizeBias.Monotone.SubgraphMonotone
import Formalization.PoissonSizeBias.Monotone.DegreeCovariance

/-!
# Monotone Coupling Applications to Erdős–Rényi Random Graphs
(`Formalization.PoissonSizeBias.Monotone.Examples`)

Re-exports all Section 4.3.3 (`Monotone.*`) modules and proves Example 4.11
(`[Large degree vertices]`, `SteinIntro.tex:2428-2439`, `ex4_11`) and Example 4.12
(`[Small degree vertices]`, `SteinIntro.tex:2440-2449`, `ex4_12`).
-/

open MeasureTheory ProbabilityTheory
set_option linter.style.openClassical false
set_option linter.unusedFintypeInType false
open scoped ENNReal NNReal Classical

namespace SteinMethod

/-! ### Part 6: Example 4.11 (`[Large degree vertices]`, `SteinIntro.tex:2428-2439`) and
Example 4.12 (`[Small degree vertices]`, `SteinIntro.tex:2440-2449`) -/

/-- **Example 4.11** (`[Large degree vertices]`, `SteinIntro.tex:2428-2439`, `[bhj92]` §5.2):
for $G \sim G(n, p)$ with $2 \le n$, $d < n$, and $0 < p \le 1$, let
$W = \sum_{v=1}^n \mathbb{I}[\deg(v) \ge d]$,
$q_1 = \sum_{k=d}^{n-1} \binom{n-1}{k} p^k (1 - p)^{n-1-k}$, and $Z_1 \sim \mathrm{Po}(n q_1)$.
(The conditions $2 \le n$, $d < n$, and $0 < p$ are required because the printed denominator
$(n - 1) p q_1$ vanishes at $n = 1$, $d \ge n$, or $p = 0$.)
Then each indicator $\mathbb{I}[\deg(v) \ge d]$ is an increasing function of the edge indicators,
$(n - 1) p q_1 > 0$, $\mathbb{E}[W] = n q_1$, and
$$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z_1)) \le
\frac{d^2 (1 - p) [\binom{n-1}{d} p^d (1 - p)^{n-1-d}]^2}{(n - 1) p q_1} + q_1.$$ -/
theorem ex4_11
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n d : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z₁ : Ω' → ℕ}
    (hn : 2 ≤ n) (hdn : d < n)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hG_meas : AEMeasurable G P)
    (hG_law : P.map G = erdosRenyi n p)
    (hr_eq : (r : ℝ) = (n : ℝ) *
      ∑ k ∈ Finset.Ico d n, ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k))
    (hZ_meas : AEMeasurable Z₁ P')
    (hZ_law : P'.map Z₁ = poissonLaw r) :
    let q₁ : ℝ :=
      ∑ k ∈ Finset.Ico d n, ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k)
    let W : Ω → ℕ := fun ω ↦ ∑ v : Fin n, if d ≤ (G ω).degree v then 1 else 0
    (∀ v : Fin n,
      Monotone (largeDegEdgeFn v d) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        largeDegEdgeFn v d (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) =
          if d ≤ G₀.degree v then 1 else 0) ∧
    0 < ((n : ℝ) - 1) * p * q₁ ∧
    ∫ ω, (W ω : ℝ) ∂P = (n : ℝ) * q₁ ∧
    tvDist (P.map W) (P'.map Z₁) ≤
      ENNReal.ofReal
        (((d : ℝ) ^ 2 * (1 - p) *
            (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
          (((n : ℝ) - 1) * p * q₁) + q₁) := by
  intro q₁ W
  have hr_q : (r : ℝ) = (n : ℝ) * q₁ := hr_eq
  have h1 : ∀ v : Fin n,
      Monotone (largeDegEdgeFn v d) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        largeDegEdgeFn v d (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) =
          if d ≤ G₀.degree v then 1 else 0 :=
    fun v ↦ ⟨monotone_largeDegEdgeFn v d, largeDegEdgeFn_edgeIndNat v d⟩
  let f : Fin n → (Fin (Fintype.card (EdgePair n)) → ℕ) → ℕ :=
    fun v ↦ largeDegEdgeFn v d
  let X_R : Fin n → SimpleGraph (Fin n) → ℝ :=
    fun v G₀ ↦ if d ≤ G₀.degree v then 1 else 0
  have h_prob_v : ∀ v : Fin n,
      (erdosRenyi n p).real {G₀ |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) = 1} =
        q₁ := by
    intro v
    have h_set : {G₀ : SimpleGraph (Fin n) |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) = 1} =
        {G₀ : SimpleGraph (Fin n) | d ≤ G₀.degree v} := by
      ext G₀
      simp only [Set.mem_ofPred_eq, f, largeDegEdgeFn_edgeIndNat]
      by_cases h : d ≤ G₀.degree v <;> simp [h]
    rw [h_set, erdosRenyi_real_degree_ge hp0.le hp1 v d]
  have h_prob_P : ∀ v : Fin n,
      P.real {ω |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1} = q₁ := by
    intro v
    change P.real (G ⁻¹' {G₀ |
      f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) = 1}) = q₁
    rw [← map_measureReal_apply_of_aemeasurable hG_meas .of_discrete, hG_law]
    exact h_prob_v v
  have hr_sum : (r : ℝ) = ∑ v : Fin n,
      P.real {ω |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1} := by
    rw [hr_q]
    simp_rw [h_prob_P, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hf_01 : ∀ v : Fin n, ∀ y : Fin (Fintype.card (EdgePair n)) → ℕ,
      (∀ j, y j ≤ 1) → f v y = 0 ∨ f v y = 1 := by
    intro v y _
    unfold f largeDegEdgeFn
    split_ifs <;> simp
  have hf_mono : (∀ v : Fin n, MonotoneOn (f v) {y | ∀ j, y j ≤ 1}) ∨
      (∀ v : Fin n, AntitoneOn (f v) {y | ∀ j, y j ≤ 1}) :=
    Or.inl fun v ↦ (monotone_largeDegEdgeFn v d).monotoneOn _
  have h_thm :=
    thm4_17_erdosRenyi P P' hp0.le hp1 hG_meas hG_law hf_01 hf_mono hr_sum hZ_meas hZ_law
  dsimp only at h_thm
  have hW_pt : ∀ ω,
      (∑ v : Fin n,
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω))) = W ω := by
    intro ω
    simp [f, W]
  simp_rw [hW_pt] at h_thm
  -- Compute pairwise covariance `cov[X_R v₁, X_R v₂; erdosRenyi n p]` for `v₁ ≠ v₂`
  let c : ℝ :=
    ((d : ℝ) ^ 2 * (1 - p) * (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
      (((n : ℝ) - 1) ^ 2 * p)
  have h_cov : ∀ v₁ v₂ : Fin n, v₁ ≠ v₂ →
      cov[X_R v₁, X_R v₂; erdosRenyi n p] = c := by
    intro v₁ v₂ h12
    rcases Nat.eq_zero_or_pos d with rfl | hd1
    · have hX_const : X_R v₁ = fun _ ↦ 1 := by
        funext G₀
        simp [X_R]
      rw [hX_const, covariance_const_left]
      unfold c
      simp
    · let φ_A : ℕ → ℝ := fun k ↦ if d ≤ k then 1 else 0
      let φ_B : ℕ → ℝ := fun k ↦ if k = d - 1 then 1 else 0
      let φ_K : Bool → ℝ := fun b ↦ if b = true then 1 else 0
      have hK01 : ∀ b : Bool, φ_K b = 0 ∨ φ_K b = 1 := fun b ↦ by cases b <;> simp [φ_K]
      have hX₁ : ∀ G₀, X_R v₁ G₀ = φ_A (reducedDeg v₁ v₂ G₀) +
          φ_K (edgeBitsOfGraph G₀ (pairEdge h12)) * φ_B (reducedDeg v₁ v₂ G₀) := by
        intro G₀
        unfold X_R φ_A φ_B φ_K
        rw [degree_eq_reducedDeg_add_ite h12 G₀]
        cases hbit : edgeBitsOfGraph G₀ (pairEdge h12)
        · simp
        · simp only [↓reduceIte, one_mul]
          by_cases hle : d ≤ reducedDeg v₁ v₂ G₀
          · have h1 : d ≤ reducedDeg v₁ v₂ G₀ + 1 := by omega
            have h2 : ¬ (reducedDeg v₁ v₂ G₀ = d - 1) := by omega
            simp [hle, h1, h2]
          · by_cases heq : reducedDeg v₁ v₂ G₀ = d - 1
            · have h1 : d ≤ reducedDeg v₁ v₂ G₀ + 1 := by omega
              simp only [h1, hle, ↓reduceIte]
              simp [heq]
            · have h1 : ¬ (d ≤ reducedDeg v₁ v₂ G₀ + 1) := by omega
              simp [hle, heq, h1]
      have hX₂ : ∀ G₀, X_R v₂ G₀ = φ_A (reducedDeg v₂ v₁ G₀) +
          φ_K (edgeBitsOfGraph G₀ (pairEdge h12)) * φ_B (reducedDeg v₂ v₁ G₀) := by
        intro G₀
        unfold X_R φ_A φ_B φ_K
        rw [degree_right_eq_reducedDeg_add_ite h12 G₀]
        cases hbit : edgeBitsOfGraph G₀ (pairEdge h12)
        · simp
        · simp only [↓reduceIte, one_mul]
          by_cases hle : d ≤ reducedDeg v₂ v₁ G₀
          · have h1 : d ≤ reducedDeg v₂ v₁ G₀ + 1 := by omega
            have h2 : ¬ (reducedDeg v₂ v₁ G₀ = d - 1) := by omega
            simp [hle, h1, h2]
          · by_cases heq : reducedDeg v₂ v₁ G₀ = d - 1
            · have h1 : d ≤ reducedDeg v₂ v₁ G₀ + 1 := by omega
              simp only [h1, hle, ↓reduceIte]
              simp [heq]
            · have h1 : ¬ (d ≤ reducedDeg v₂ v₁ G₀ + 1) := by omega
              simp [hle, heq, h1]
      rw [cov_degree_bilinear h12 φ_A φ_B φ_K hK01 (X_R v₁) (X_R v₂) hX₁ hX₂,
        integral_pairEdge_indicator hp0.le hp1 h12,
        integral_reducedDeg_eq hp0.le hp1 hn h12 (d - 1),
        integral_reducedDeg_eq hp0.le hp1 hn h12.symm (d - 1)]
      have h_sub_exp : n - 2 - (d - 1) = n - 1 - d := by omega
      rw [h_sub_exp]
      have h_binom_nat : (n - 1) * (n - 2).choose (d - 1) = (n - 1).choose d * d := by
        have h1 : n - 2 + 1 = n - 1 := by omega
        have h2 : d - 1 + 1 = d := by omega
        have h := Nat.add_one_mul_choose_eq (n - 2) (d - 1)
        rwa [h1, h2] at h
      have h_binom_real : ((n : ℝ) - 1) * ((n - 2).choose (d - 1) : ℝ) =
          ((n - 1).choose d : ℝ) * (d : ℝ) := by
        have h_cast : (((n - 1) * (n - 2).choose (d - 1) : ℕ) : ℝ) =
            (((n - 1).choose d * d : ℕ) : ℝ) := by rw [h_binom_nat]
        have hn1 : 1 ≤ n := by omega
        push_cast [Nat.cast_sub hn1] at h_cast
        exact h_cast
      have hp_pow : p ^ d = p ^ (d - 1) * p := by
        have hd_eq : d = (d - 1) + 1 := by omega
        conv_lhs => rw [hd_eq, pow_succ]
      have h_denom_ne : ((n : ℝ) - 1) ^ 2 * p ≠ 0 := by
        have hn_gt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (ne_of_gt hp0)
      unfold c
      rw [eq_div_iff h_denom_ne]
      calc p * (1 - p) * (((n - 2).choose (d - 1) : ℝ) * p ^ (d - 1) * (1 - p) ^ (n - 1 - d)) *
            (((n - 2).choose (d - 1) : ℝ) * p ^ (d - 1) * (1 - p) ^ (n - 1 - d)) *
            (((n : ℝ) - 1) ^ 2 * p)
        _ = (1 - p) *
            ((((n : ℝ) - 1) * ((n - 2).choose (d - 1) : ℝ)) *
              (p ^ (d - 1) * p) * (1 - p) ^ (n - 1 - d)) ^ 2 := by ring
        _ = (d : ℝ) ^ 2 * (1 - p) *
            (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2 := by
          rw [h_binom_real, ← hp_pow]
          ring
  have hX_mean : ∀ v : Fin n, ∫ G₀, X_R v G₀ ∂(erdosRenyi n p) = q₁ := by
    intro v
    have h_ind : X_R v =
        {G₀ : SimpleGraph (Fin n) | d ≤ G₀.degree v}.indicator 1 := by
      funext G₀
      by_cases h : d ≤ G₀.degree v <;> simp [X_R, h]
    rw [h_ind, integral_indicator_one .of_discrete, erdosRenyi_real_degree_ge hp0.le hp1 v d]
  have hW_mean : ∫ ω, (W ω : ℝ) ∂P = (n : ℝ) * q₁ := by
    have h_map := integral_map hG_meas
      (f := fun G₀ : SimpleGraph (Fin n) ↦ ∑ v : Fin n, X_R v G₀)
      Measurable.of_discrete.aestronglyMeasurable
    have h_comp : (∫ ω, (W ω : ℝ) ∂P) =
        ∫ ω, (fun G₀ : SimpleGraph (Fin n) ↦ ∑ v : Fin n, X_R v G₀) (G ω) ∂P := by
      congr 1; funext ω; simp [W, X_R]
    rw [h_comp, ← h_map, hG_law,
      integral_finsetSum Finset.univ (fun _ _ ↦ Integrable.of_finite)]
    simp_rw [hX_mean, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have h_var_P : ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
      ProbabilityTheory.variance (fun G₀ ↦ ∑ v : Fin n, X_R v G₀) (erdosRenyi n p) := by
    have h_comp : (fun ω ↦ (W ω : ℝ)) = (fun G₀ ↦ ∑ v : Fin n, X_R v G₀) ∘ G := by
      funext ω
      simp [W, X_R]
    rw [h_comp, ← ProbabilityTheory.variance_map Measurable.of_discrete.aemeasurable hG_meas,
      hG_law]
  have h_sum_q : 2 * (∑ v : Fin n,
      (P.real {ω |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1}) ^ 2) =
      2 * (n : ℝ) * q₁ ^ 2 := by
    simp_rw [h_prob_P, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  have h_var_comb := variance_sum_const_diag_offDiag (erdosRenyi n p) X_R q₁ c
    (fun v G₀ ↦ by by_cases h : d ≤ G₀.degree v <;> simp [X_R, h])
    hX_mean h_cov
  have hq₁_pos : 0 < q₁ := by
    unfold q₁
    have h_nonneg : ∀ k ∈ Finset.Ico d n,
        0 ≤ ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k) := by
      intro k _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0.le _))
        (pow_nonneg (by linarith) _)
    have h_mem_n1 : n - 1 ∈ Finset.Ico d n := by
      simp only [Finset.mem_Ico]
      omega
    have h_pos_n1 : 0 < ((n - 1).choose (n - 1) : ℝ) * p ^ (n - 1) *
        (1 - p) ^ (n - 1 - (n - 1)) := by
      simp [pow_pos hp0]
    exact lt_of_lt_of_le h_pos_n1 (Finset.single_le_sum h_nonneg h_mem_n1)
  have h_denom_pos : 0 < ((n : ℝ) - 1) * p * q₁ := by
    have hn_gt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact mul_pos (mul_pos (by linarith) hp0) hq₁_pos
  refine ⟨h1, h_denom_pos, hW_mean, h_thm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [h_var_P, h_sum_q, hr_q, h_var_comb]
  have h_rhs_nonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * c + (n : ℝ) * q₁ ^ 2 := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1_nn : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have hc_nn : 0 ≤ c := by
      unfold c
      exact div_nonneg
        (mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) hp0.le)
    exact add_nonneg (mul_nonneg (mul_nonneg hn_nn hn1_nn) hc_nn)
      (mul_nonneg hn_nn (sq_nonneg _))
  have h_eq_final :
      ((n : ℝ) * q₁)⁻¹ * ((n : ℝ) * ((n : ℝ) - 1) * c + (n : ℝ) * q₁ ^ 2) =
      (((d : ℝ) ^ 2 * (1 - p) *
          (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
        (((n : ℝ) - 1) * p * q₁) + q₁) := by
    unfold c
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1_ne : (n : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    have hp_ne : p ≠ 0 := ne_of_gt hp0
    have hq_ne : q₁ ≠ 0 := ne_of_gt hq₁_pos
    field_simp
  exact (mul_le_mul_of_nonneg_right (min_le_right 1 _) h_rhs_nonneg).trans_eq h_eq_final

/-- **Example 4.12** (`[Small degree vertices]`, `SteinIntro.tex:2440-2449`, `[bhj92]` §5.2):
for $G \sim G(n, p)$ with $2 \le n$, $d \in \mathbb{N}$, and $0 \le p < 1$, let
$W' = \sum_{v=1}^n \mathbb{I}[\deg(v) \le d]$,
$q_2 = \sum_{k=0}^d \binom{n-1}{k} p^k (1 - p)^{n-1-k}$, and $Z_2 \sim \mathrm{Po}(n q_2)$.
Then each indicator $\mathbb{I}[\deg(v) \le d]$ is a decreasing function of the edge indicators, and
$$d_{\mathrm{TV}}(\mathcal{L}(W'), \mathcal{L}(Z_2)) \le
\frac{(n - d - 1)^2 p [\binom{n-1}{d} p^d (1 - p)^{n-1-d}]^2}{(n - 1) (1 - p) q_2} + q_2.$$ -/
theorem ex4_12
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n d : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z₂ : Ω' → ℕ}
    (hn : 2 ≤ n) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hG_meas : AEMeasurable G P)
    (hG_law : P.map G = erdosRenyi n p)
    (hr_eq : (r : ℝ) = (n : ℝ) *
      ∑ k ∈ Finset.range (d + 1), ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k))
    (hZ_meas : AEMeasurable Z₂ P')
    (hZ_law : P'.map Z₂ = poissonLaw r) :
    let q₂ : ℝ :=
      ∑ k ∈ Finset.range (d + 1), ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k)
    let W' : Ω → ℕ := fun ω ↦ ∑ v : Fin n, if (G ω).degree v ≤ d then 1 else 0
    (∀ v : Fin n,
      Antitone (smallDegEdgeFn v d) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        smallDegEdgeFn v d (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) =
          if G₀.degree v ≤ d then 1 else 0) ∧
    0 < ((n : ℝ) - 1) * (1 - p) * q₂ ∧
    ∫ ω, (W' ω : ℝ) ∂P = (n : ℝ) * q₂ ∧
    tvDist (P.map W') (P'.map Z₂) ≤
      ENNReal.ofReal
        ((((n : ℝ) - (d : ℝ) - 1) ^ 2 * p *
            (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
          (((n : ℝ) - 1) * (1 - p) * q₂) + q₂) := by
  intro q₂ W'
  have hr_q : (r : ℝ) = (n : ℝ) * q₂ := hr_eq
  have h1 : ∀ v : Fin n,
      Antitone (smallDegEdgeFn v d) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        smallDegEdgeFn v d (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) =
          if G₀.degree v ≤ d then 1 else 0 :=
    fun v ↦ ⟨antitone_smallDegEdgeFn v d, smallDegEdgeFn_edgeIndNat v d⟩
  let f : Fin n → (Fin (Fintype.card (EdgePair n)) → ℕ) → ℕ :=
    fun v ↦ smallDegEdgeFn v d
  let X_R : Fin n → SimpleGraph (Fin n) → ℝ :=
    fun v G₀ ↦ if G₀.degree v ≤ d then 1 else 0
  have h_prob_v : ∀ v : Fin n,
      (erdosRenyi n p).real {G₀ |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) = 1} =
        q₂ := by
    intro v
    have h_set : {G₀ : SimpleGraph (Fin n) |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) = 1} =
        {G₀ : SimpleGraph (Fin n) | G₀.degree v ≤ d} := by
      ext G₀
      simp only [Set.mem_ofPred_eq, f, smallDegEdgeFn_edgeIndNat]
      by_cases h : G₀.degree v ≤ d <;> simp [h]
    rw [h_set, erdosRenyi_real_degree_le hp0 hp1.le v d]
  have h_prob_P : ∀ v : Fin n,
      P.real {ω |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1} = q₂ := by
    intro v
    change P.real (G ⁻¹' {G₀ |
      f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) = 1}) = q₂
    rw [← map_measureReal_apply_of_aemeasurable hG_meas .of_discrete, hG_law]
    exact h_prob_v v
  have hr_sum : (r : ℝ) = ∑ v : Fin n,
      P.real {ω |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1} := by
    rw [hr_q]
    simp_rw [h_prob_P, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hf_01 : ∀ v : Fin n, ∀ y : Fin (Fintype.card (EdgePair n)) → ℕ,
      (∀ j, y j ≤ 1) → f v y = 0 ∨ f v y = 1 := by
    intro v y _
    unfold f smallDegEdgeFn
    split_ifs <;> simp
  have hf_mono : (∀ v : Fin n, MonotoneOn (f v) {y | ∀ j, y j ≤ 1}) ∨
      (∀ v : Fin n, AntitoneOn (f v) {y | ∀ j, y j ≤ 1}) :=
    Or.inr fun v ↦ (antitone_smallDegEdgeFn v d).antitoneOn _
  have h_thm :=
    thm4_17_erdosRenyi P P' hp0 hp1.le hG_meas hG_law hf_01 hf_mono hr_sum hZ_meas hZ_law
  dsimp only at h_thm
  have hW_pt : ∀ ω,
      (∑ v : Fin n,
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω))) = W' ω := by
    intro ω
    simp [f, W']
  simp_rw [hW_pt] at h_thm
  -- Compute pairwise covariance `cov[X_R v₁, X_R v₂; erdosRenyi n p]` for `v₁ ≠ v₂`
  let c : ℝ :=
    ((((n : ℝ) - (d : ℝ) - 1) ^ 2 * p *
        (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
      (((n : ℝ) - 1) ^ 2 * (1 - p)))
  have h_cov : ∀ v₁ v₂ : Fin n, v₁ ≠ v₂ →
      cov[X_R v₁, X_R v₂; erdosRenyi n p] = c := by
    intro v₁ v₂ h12
    let φ_A : ℕ → ℝ := fun k ↦ if k + 1 ≤ d then 1 else 0
    let φ_B : ℕ → ℝ := fun k ↦ if k = d then 1 else 0
    let φ_K : Bool → ℝ := fun b ↦ if b = true then 0 else 1
    have hK01 : ∀ b : Bool, φ_K b = 0 ∨ φ_K b = 1 := fun b ↦ by cases b <;> simp [φ_K]
    have hX₁ : ∀ G₀, X_R v₁ G₀ = φ_A (reducedDeg v₁ v₂ G₀) +
        φ_K (edgeBitsOfGraph G₀ (pairEdge h12)) * φ_B (reducedDeg v₁ v₂ G₀) := by
      intro G₀
      unfold X_R φ_A φ_B φ_K
      rw [degree_eq_reducedDeg_add_ite h12 G₀]
      cases hbit : edgeBitsOfGraph G₀ (pairEdge h12)
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, one_mul]
        by_cases hlt : reducedDeg v₁ v₂ G₀ + 1 ≤ d
        · have hle : reducedDeg v₁ v₂ G₀ ≤ d := by omega
          have hne : ¬ (reducedDeg v₁ v₂ G₀ = d) := by omega
          simp [hlt, hle, hne]
        · by_cases heq : reducedDeg v₁ v₂ G₀ = d
          · simp [heq]
          · have hnot : ¬ (reducedDeg v₁ v₂ G₀ ≤ d) := by omega
            simp [hlt, heq, hnot]
      · simp
    have hX₂ : ∀ G₀, X_R v₂ G₀ = φ_A (reducedDeg v₂ v₁ G₀) +
        φ_K (edgeBitsOfGraph G₀ (pairEdge h12)) * φ_B (reducedDeg v₂ v₁ G₀) := by
      intro G₀
      unfold X_R φ_A φ_B φ_K
      rw [degree_right_eq_reducedDeg_add_ite h12 G₀]
      cases hbit : edgeBitsOfGraph G₀ (pairEdge h12)
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, one_mul]
        by_cases hlt : reducedDeg v₂ v₁ G₀ + 1 ≤ d
        · have hle : reducedDeg v₂ v₁ G₀ ≤ d := by omega
          have hne : ¬ (reducedDeg v₂ v₁ G₀ = d) := by omega
          simp [hlt, hle, hne]
        · by_cases heq : reducedDeg v₂ v₁ G₀ = d
          · simp [heq]
          · have hnot : ¬ (reducedDeg v₂ v₁ G₀ ≤ d) := by omega
            simp [hlt, heq, hnot]
      · simp
    have h_int_K :
        ∫ G₀, φ_K (edgeBitsOfGraph G₀ (pairEdge h12)) ∂(erdosRenyi n p) = 1 - p := by
      have h_eq : (fun G₀ ↦ φ_K (edgeBitsOfGraph G₀ (pairEdge h12))) =
          fun G₀ ↦
            1 - (if edgeBitsOfGraph G₀ (pairEdge h12) = true then (1 : ℝ) else 0) := by
        funext G₀
        cases edgeBitsOfGraph G₀ (pairEdge h12) <;> simp [φ_K]
      rw [h_eq, integral_sub (integrable_const 1) Integrable.of_finite,
        integral_const, probReal_univ, smul_eq_mul, mul_one,
        integral_pairEdge_indicator hp0 hp1.le h12]
    rw [cov_degree_bilinear h12 φ_A φ_B φ_K hK01 (X_R v₁) (X_R v₂) hX₁ hX₂,
      h_int_K,
      integral_reducedDeg_eq hp0 hp1.le hn h12 d,
      integral_reducedDeg_eq hp0 hp1.le hn h12.symm d]
    by_cases hdn2 : d ≤ n - 2
    · have h_binom_nat : (n - 1) * (n - 2).choose d = (n - 1).choose d * (n - 1 - d) := by
        have h1 : (n - 2).choose d = (n - 2).choose (n - 2 - d) :=
          (Nat.choose_symm hdn2).symm
        have h2 : (n - 1).choose d = (n - 1).choose (n - 1 - d) :=
          (Nat.choose_symm (by omega : d ≤ n - 1)).symm
        have h3 : n - 2 + 1 = n - 1 := by omega
        have h4 : n - 2 - d + 1 = n - 1 - d := by omega
        have h := Nat.add_one_mul_choose_eq (n - 2) (n - 2 - d)
        rw [h3, h4, ← h1, ← h2] at h
        exact h
      have h_binom_real : ((n : ℝ) - 1) * ((n - 2).choose d : ℝ) =
          ((n - 1).choose d : ℝ) * ((n : ℝ) - (d : ℝ) - 1) := by
        have h_cast : (((n - 1) * (n - 2).choose d : ℕ) : ℝ) =
            (((n - 1).choose d * (n - 1 - d) : ℕ) : ℝ) := by rw [h_binom_nat]
        have hn1 : 1 ≤ n := by omega
        have hdn1 : d ≤ n - 1 := by omega
        push_cast [Nat.cast_sub hn1, Nat.cast_sub hdn1] at h_cast
        linarith
      have hq_pow : (1 - p) ^ (n - 1 - d) = (1 - p) ^ (n - 2 - d) * (1 - p) := by
        have h_exp : n - 1 - d = (n - 2 - d) + 1 := by omega
        conv_lhs => rw [h_exp, pow_succ]
      have h_denom_ne : ((n : ℝ) - 1) ^ 2 * (1 - p) ≠ 0 := by
        have hn_gt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (by linarith)
      unfold c
      rw [eq_div_iff h_denom_ne]
      calc (1 - p) * (1 - (1 - p)) *
            (((n - 2).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 2 - d)) *
            (((n - 2).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 2 - d)) *
            (((n : ℝ) - 1) ^ 2 * (1 - p))
        _ = p *
            ((((n : ℝ) - 1) * ((n - 2).choose d : ℝ)) *
              p ^ d * ((1 - p) ^ (n - 2 - d) * (1 - p))) ^ 2 := by ring
        _ = ((n : ℝ) - (d : ℝ) - 1) ^ 2 * p *
            (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2 := by
          rw [h_binom_real, ← hq_pow]
          ring
    · -- `d > n - 2`, i.e., `d = n - 1` or `d ≥ n`
      have h_choose_zero : (n - 2).choose d = 0 := Nat.choose_eq_zero_of_lt (by omega)
      unfold c
      rw [h_choose_zero, Nat.cast_zero, zero_mul, zero_mul, mul_zero]
      by_cases h_eq_n1 : d = n - 1
      · have h_sub_zero : (n : ℝ) - (d : ℝ) - 1 = 0 := by
          have hn1 : 1 ≤ n := by omega
          rw [h_eq_n1, Nat.cast_sub hn1]
          ring
        rw [h_sub_zero]
        ring
      · have h_gt_n1 : n - 1 < d := by omega
        rw [Nat.choose_eq_zero_of_lt h_gt_n1, Nat.cast_zero]
        ring
  have hX_mean : ∀ v : Fin n, ∫ G₀, X_R v G₀ ∂(erdosRenyi n p) = q₂ := by
    intro v
    have h_ind : X_R v =
        {G₀ : SimpleGraph (Fin n) | G₀.degree v ≤ d}.indicator 1 := by
      funext G₀
      by_cases h : G₀.degree v ≤ d <;> simp [X_R, h]
    rw [h_ind, integral_indicator_one .of_discrete, erdosRenyi_real_degree_le hp0 hp1.le v d]
  have hW_mean : ∫ ω, (W' ω : ℝ) ∂P = (n : ℝ) * q₂ := by
    have h_map := integral_map hG_meas
      (f := fun G₀ : SimpleGraph (Fin n) ↦ ∑ v : Fin n, X_R v G₀)
      Measurable.of_discrete.aestronglyMeasurable
    have h_comp : (∫ ω, (W' ω : ℝ) ∂P) =
        ∫ ω, (fun G₀ : SimpleGraph (Fin n) ↦ ∑ v : Fin n, X_R v G₀) (G ω) ∂P := by
      congr 1; funext ω; simp [W', X_R]
    rw [h_comp, ← h_map, hG_law,
      integral_finsetSum Finset.univ (fun _ _ ↦ Integrable.of_finite)]
    simp_rw [hX_mean, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have h_var_P : ProbabilityTheory.variance (fun ω ↦ (W' ω : ℝ)) P =
      ProbabilityTheory.variance (fun G₀ ↦ ∑ v : Fin n, X_R v G₀) (erdosRenyi n p) := by
    have h_comp : (fun ω ↦ (W' ω : ℝ)) = (fun G₀ ↦ ∑ v : Fin n, X_R v G₀) ∘ G := by
      funext ω
      simp [W', X_R]
    rw [h_comp, ← ProbabilityTheory.variance_map Measurable.of_discrete.aemeasurable hG_meas,
      hG_law]
  have h_sum_q : 2 * (∑ v : Fin n,
      (P.real {ω |
        f v (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) (G ω)) = 1}) ^ 2) =
      2 * (n : ℝ) * q₂ ^ 2 := by
    simp_rw [h_prob_P, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  have h_var_comb := variance_sum_const_diag_offDiag (erdosRenyi n p) X_R q₂ c
    (fun v G₀ ↦ by by_cases h : G₀.degree v ≤ d <;> simp [X_R, h])
    hX_mean h_cov
  have hq₂_pos : 0 < q₂ := by
    unfold q₂
    have h_nonneg : ∀ k ∈ Finset.range (d + 1),
        0 ≤ ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k) := by
      intro k _
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
        (pow_nonneg (by linarith) _)
    have h_mem_0 : 0 ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.succ_pos d)
    have h_pos_0 : 0 < ((n - 1).choose 0 : ℝ) * p ^ 0 * (1 - p) ^ (n - 1 - 0) := by
      simp [pow_pos (by linarith : 0 < 1 - p)]
    exact lt_of_lt_of_le h_pos_0 (Finset.single_le_sum h_nonneg h_mem_0)
  have h_denom_pos : 0 < ((n : ℝ) - 1) * (1 - p) * q₂ := by
    have hn_gt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact mul_pos (mul_pos (by linarith) (by linarith)) hq₂_pos
  refine ⟨h1, h_denom_pos, hW_mean, h_thm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [h_var_P, h_sum_q, hr_q, h_var_comb]
  have h_rhs_nonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) * c + (n : ℝ) * q₂ ^ 2 := by
    have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn1_nn : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have hc_nn : 0 ≤ c := by
      unfold c
      exact div_nonneg
        (mul_nonneg (mul_nonneg (sq_nonneg _) hp0) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (by linarith))
    exact add_nonneg (mul_nonneg (mul_nonneg hn_nn hn1_nn) hc_nn)
      (mul_nonneg hn_nn (sq_nonneg _))
  have h_eq_final :
      ((n : ℝ) * q₂)⁻¹ * ((n : ℝ) * ((n : ℝ) - 1) * c + (n : ℝ) * q₂ ^ 2) =
      ((((n : ℝ) - (d : ℝ) - 1) ^ 2 * p *
          (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
        (((n : ℝ) - 1) * (1 - p) * q₂) + q₂) := by
    unfold c
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1_ne : (n : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      linarith
    have h1p_ne : 1 - p ≠ 0 := by linarith
    have hq_ne : q₂ ≠ 0 := ne_of_gt hq₂_pos
    field_simp
  exact (mul_le_mul_of_nonneg_right (min_le_right 1 _) h_rhs_nonneg).trans_eq h_eq_final


end SteinMethod
