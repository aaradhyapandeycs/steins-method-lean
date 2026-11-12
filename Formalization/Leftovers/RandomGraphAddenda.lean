/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Normal.WassersteinBound
import Formalization.RandomGraph.IsolatedCoupling
import Formalization.RandomGraph.Triangles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Section 3 Random-Graph Addenda (`Formalization.Leftovers.RandomGraphAddenda`)

Resolves the two random-graph addenda from `docs/reviews/review-04.md` (`P2`, `P3`) and
`docs/reviews/stmts-review-05K.md` (`K2`):
* `Ex3_9_sizeBias_le_one_proof`: extends Example 3.9 (`\label{ex72}`,
  `SteinIntro.tex:1354-1367, 1380-1383`) from $0 \le p < 1$ to $0 \le p \le 1$, covering both
  $n = 1$ (no potential edges) and $p = 1, n \ge 2$ ($X = 0$ a.s. under ruling `D8`).
* `Sec3_2_1_triangles_clt_regime_restricted_proof` (`SteinIntro.tex:941-945`; `ISSUE-TYPO-3.2.1`,
  `ISSUE-3.2.1`): for $0 \le p_n \le 1$ with $n^\alpha p_n \to c > 0$ ($0 \le \alpha$,
  $\alpha = 0 \to c < 1$), proves $\operatorname{Var}(T_n) \to \infty$ for all $0 \le \alpha < 1$,
  and proves that for $0 \le \alpha < 2/9$ the Section 3.2.1 Stein upper bound tends to $0$ and
  $W_n \to \mathcal{N}(0, 1)$ in both Wasserstein and Kolmogorov distance.
* `triangles_bound_tendsto_at_two_ninths` & `triangles_clt_counterexample_p_eq_one`: machine-checks
  that at the threshold $p_n = n^{-2/9}$ the Section 3.2.1 upper bound converges to $3\sqrt{2} > 0$,
  and at $p_n \equiv 1$ ($\alpha = 0, c = 1$) $\operatorname{Var}(T_n) = 0$.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-! ### Section 1: Example 3.9 Size-Bias Extension to $0 \le p \le 1$ (`P2`) -/

private instance instIsEmptyEdgePairOne : IsEmpty (EdgePair 1) :=
  ⟨fun ⟨e, he⟩ ↦
    Sym2.ind (fun u v h ↦ h (Sym2.mk_isDiag_iff.mpr (Subsingleton.elim u v))) e he⟩

private lemma erdosRenyi_one_eq (p q : ℝ) : erdosRenyi 1 p = erdosRenyi 1 q := by
  unfold erdosRenyi
  congr 2
  funext e
  exact isEmptyElim e

/-- Example 3.9, size-bias realization and increment identity extended to $0 \le p \le 1$
(`\label{ex72}`, `SteinIntro.tex:1354-1367, 1380-1383`; `review-04.md` `P2`). -/
theorem Ex3_9_sizeBias_le_one_proof
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {I : Ω → Fin n}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hG_meas : Measurable G) (hG_law : P.map G = erdosRenyi n p)
    (hI_meas : Measurable I) (hIG_indep : IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let X : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i (G ω)
    let Xs : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i ((G ω).deleteIncidenceSet (I ω))
    let d : Fin n → Ω → ℕ := fun i ω ↦ ((G ω).neighborSet i).ncard
    let D : Fin n → Ω → ℝ :=
      fun i ω ↦ ({j : Fin n | (G ω).Adj i j ∧ ((G ω).neighborSet j).ncard = 1}.ncard : ℝ)
    IsSizeBias P X P Xs ∧
      ∀ ω : Ω, Xs ω - X ω = D (I ω) ω + {ω' : Ω | 0 < d (I ω') ω'}.indicator 1 ω := by
  rcases lt_or_eq_of_le hp1 with hp_lt | rfl
  · exact Ex3_9_sizeBias_proof P hn hp0 hp_lt hG_meas hG_law hI_meas hIG_indep hI_law
  · intro X_ind X Xs d D
    have hDet : ∀ ω : Ω, Xs ω - X ω = D (I ω) ω + {ω' : Ω | 0 < d (I ω') ω'}.indicator 1 ω := by
      let μG : Measure (SimpleGraph (Fin n)) := erdosRenyi n 0
      let unif_pmf : PMF (Fin n) := @PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩
      let unif : Measure (Fin n) := unif_pmf.toMeasure
      let P₀ : Measure (SimpleGraph (Fin n) × Fin n) := μG.prod unif
      have hmap_fst : P₀.map Prod.fst = μG := (measurePreserving_fst (μ := μG) (ν := unif)).map_eq
      have hmap_snd : P₀.map Prod.snd = unif :=
        (measurePreserving_snd (μ := μG) (ν := unif)).map_eq
      have hindep : IndepFun (Prod.snd : SimpleGraph (Fin n) × Fin n → Fin n) Prod.fst P₀ :=
        (indepFun_prod (μ := μG) (ν := unif) measurable_id measurable_id).symm
      obtain ⟨_, hIdent₀⟩ := Ex3_9_sizeBias_proof P₀ hn le_rfl zero_lt_one
        measurable_fst hmap_fst measurable_snd hindep hmap_snd
      intro ω
      refine (hIdent₀ (G ω, I ω)).trans (congrArg (D (I ω) ω + ·) ?_)
      by_cases hpos : 0 < d (I ω) ω
      · exact (Set.indicator_of_mem hpos 1).trans (Set.indicator_of_mem hpos 1).symm
      · exact (Set.indicator_of_notMem hpos 1).trans (Set.indicator_of_notMem hpos 1).symm
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn) with hn1 | hn2
    · subst hn1
      have hG_zero : P.map G = erdosRenyi 1 0 := hG_law.trans (erdosRenyi_one_eq 1 0)
      exact ⟨(Ex3_9_sizeBias_proof P hn le_rfl zero_lt_one
        hG_meas hG_zero hI_meas hIG_indep hI_law).1, hDet⟩
    · refine ⟨?_, hDet⟩
      have hXi_zero : ∀ i : Fin n, ∀ᵐ ω ∂P, X_ind i (G ω) = 0 := by
        intro i
        have hreal0 : (P.map G).real {H : SimpleGraph (Fin n) | H.IsIsolated i} = 0 := by
          rw [hG_law, erdosRenyi_real_isIsolated zero_le_one le_rfl i, sub_self,
            zero_pow (by omega : n - 1 ≠ 0)]
        have hmeas0 : (P.map G) {H : SimpleGraph (Fin n) | H.IsIsolated i} = 0 := by
          rw [measureReal_def, ENNReal.toReal_eq_zero_iff] at hreal0
          exact hreal0.resolve_right (measure_ne_top _ _)
        rw [Measure.map_apply hG_meas MeasurableSet.of_discrete] at hmeas0
        rw [ae_iff]
        refine measure_mono_null (fun ω hω ↦ ?_) hmeas0
        change X_ind i (G ω) ≠ 0 at hω
        by_contra hiso
        exact hω (Set.indicator_of_notMem hiso 1)
      have hX_zero : X =ᵐ[P] 0 :=
        (ae_all_iff.mpr hXi_zero).mono fun ω hω ↦ Finset.sum_eq_zero fun i _ ↦ hω i
      have hX_nn : 0 ≤ᵐ[P] X := Eventually.of_forall fun ω ↦
        Finset.sum_nonneg fun _ _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) (G ω)
      have hX_int : Integrable X P := (integrable_zero Ω ℝ P).congr hX_zero.symm
      have hdel_meas : Measurable (fun ω : Ω ↦ (G ω).deleteIncidenceSet (I ω)) :=
        (measurable_of_finite
          (fun q : SimpleGraph (Fin n) × Fin n ↦ q.1.deleteIncidenceSet q.2)).comp
          (hG_meas.prodMk hI_meas)
      have hXs_meas : Measurable Xs :=
        Finset.univ.measurable_sum fun i _ ↦ (measurable_of_finite (X_ind i)).comp hdel_meas
      refine ⟨hX_nn, hX_int, hXs_meas.aemeasurable, fun f _ _ ↦ ?_⟩
      have hXf_zero : (fun ω ↦ X ω * f (X ω)) =ᵐ[P] 0 :=
        hX_zero.mono fun ω hω ↦ by simp [hω]
      rw [integral_eq_zero_of_ae hXf_zero, integral_eq_zero_of_ae hX_zero, zero_mul]

/-! ### Section 2: Combinatorial and Asymptotic Helpers for Triangle Counts (`P3`, `K2`) -/

private lemma two_mul_choose_two : ∀ k : ℕ, 2 * (k + 1).choose 2 = (k + 1) * k
  | 0 => rfl
  | k + 1 => by
    rw [Nat.choose_succ_succ (k + 1) 1, Nat.choose_one_right]
    linarith [two_mul_choose_two k]

private lemma six_mul_choose_three :
    ∀ m : ℕ, 6 * (m + 2).choose 3 = (m + 2) * (m + 1) * m
  | 0 => rfl
  | m + 1 => by
    rw [Nat.choose_succ_succ (m + 2) 2]
    nlinarith [two_mul_choose_two (m + 1), six_mul_choose_three m]

private lemma six_mul_choose_three_cast {n : ℕ} (hn : 3 ≤ n) :
    6 * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ n)
  have hnm : n = m + 2 := by omega
  subst hnm
  have hnat : (6 * (m + 2).choose 3 : ℕ) = (m + 2) * (m + 1) * m := six_mul_choose_three m
  have hcast : ((6 * (m + 2).choose 3 : ℕ) : ℝ) = (((m + 2) * (m + 1) * m : ℕ) : ℝ) :=
    congrArg Nat.cast hnat
  push_cast at hcast ⊢
  linarith [show ((m : ℝ) + 2) * ((m : ℝ) + 2 - 1) * ((m : ℝ) + 2 - 2) =
      ((m : ℝ) + 2) * ((m : ℝ) + 1) * (m : ℝ) by ring]

private lemma choose_three_bounds {n : ℕ} (hn : 6 ≤ n) :
    (n : ℝ) ^ 3 / 24 ≤ (n.choose 3 : ℝ) ∧ (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 := by
  have hid := six_mul_choose_three_cast (by omega : 3 ≤ n)
  have hn6 : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlo : (n : ℝ) * ((n : ℝ) / 2) * ((n : ℝ) / 2) ≤
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      (by linarith) (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hhi : (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) ≤ (n : ℝ) ^ 3 := by
    have hdiff : (n : ℝ) ^ 3 - (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) =
        (n : ℝ) * (3 * (n : ℝ) - 2) := by ring
    have hnn : 0 ≤ (n : ℝ) * (3 * (n : ℝ) - 2) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hchoose_nn : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
  constructor <;>
    linarith [show (n : ℝ) * ((n : ℝ) / 2) * ((n : ℝ) / 2) = (n : ℝ) ^ 3 / 4 by ring]

private lemma tendsto_choose_three_div_cube :
    Tendsto (fun n : ℕ ↦ (n.choose 3 : ℝ) / (n : ℝ) ^ 3) atTop (nhds (1 / 6)) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hf1 : Tendsto (fun n : ℕ ↦ 1 - 1 * ((n : ℝ))⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hinv.const_mul 1)
  have hf2 : Tendsto (fun n : ℕ ↦ 1 - 2 * ((n : ℝ))⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub (hinv.const_mul 2)
  have hlim : Tendsto
      (fun n : ℕ ↦ (1 - 1 * ((n : ℝ))⁻¹) * (1 - 2 * ((n : ℝ))⁻¹) / 6)
      atTop (nhds (1 / 6)) := by
    simpa using (hf1.mul hf2).div_const 6
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn_ne : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega)).ne'
  have hch : (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
    linarith [six_mul_choose_three_cast hn]
  rw [hch]
  field_simp [hn_ne]

private lemma tendsto_nat_rpow_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ β) atTop atTop :=
  (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop

private lemma tendsto_nat_rpow_zero_of_neg {β : ℝ} (hβ : β < 0) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ β) atTop (nhds 0) := by
  simpa only [Function.comp_def, neg_neg] using
    (tendsto_rpow_neg_atTop (neg_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop

private lemma rpow_nat_pow_eq {x a : ℝ} (hx : 0 < x) (k : ℕ) :
    (x ^ a) ^ k = x ^ ((k : ℝ) * a) := by
  rw [← Real.rpow_natCast (x ^ a) k, ← Real.rpow_mul hx.le, mul_comm]

private lemma eventually_triangle_scaling_bounds
    {p : ℕ → ℝ} {α c : ℝ}
    (hα0 : 0 ≤ α) (hc : 0 < c) (hc0 : α = 0 → c < 1)
    (htend : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) atTop (nhds c)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∀ᶠ n : ℕ in atTop,
        6 ≤ n ∧ 0 < p n ∧ p n < q ∧
          (c / 2) * (n : ℝ) ^ (-α) ≤ p n ∧ p n ≤ (2 * c) * (n : ℝ) ^ (-α) := by
  let q : ℝ := if α = 0 then (1 + c) / 2 else 1 / 2
  have hq0 : 0 < q := by dsimp only [q]; split_ifs <;> linarith [hc]
  have hq1 : q < 1 := by
    dsimp only [q]; split_ifs with hα_eq; · linarith [hc0 hα_eq]
    · norm_num
  have hev_p_lt_q : ∀ᶠ n : ℕ in atTop, p n < q := by
    rcases eq_or_lt_of_le hα0 with rfl | hα_pos
    · have hp_c : Tendsto p atTop (nhds c) := by simpa using htend
      exact hp_c.eventually (Iio_mem_nhds (by simp only [q, ↓reduceIte]; linarith [hc0 rfl]))
    · have hp_zero : Tendsto p atTop (nhds 0) := by
        have hmul : Tendsto (fun n : ℕ ↦ ((n : ℝ) ^ α * p n) * (n : ℝ) ^ (-α))
            atTop (nhds (c * 0)) :=
          htend.mul (tendsto_nat_rpow_zero_of_neg (by linarith))
        rw [mul_zero] at hmul
        refine hmul.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        calc ((n : ℝ) ^ α * p n) * (n : ℝ) ^ (-α)
          _ = p n * ((n : ℝ) ^ α * (n : ℝ) ^ (-α)) := by ring
          _ = p n := by rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero, mul_one]
      exact hp_zero.eventually (Iio_mem_nhds hq0)
  have hev_lo := htend.eventually (Ioi_mem_nhds (by linarith : c / 2 < c))
  have hev_hi := htend.eventually (Iio_mem_nhds (by linarith : c < 2 * c))
  refine ⟨q, hq0, hq1, ?_⟩
  filter_upwards [eventually_ge_atTop 6, hev_p_lt_q, hev_lo, hev_hi] with n hn6 hpq hlo hhi
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hrpow_neg_pos : 0 < (n : ℝ) ^ (-α) := Real.rpow_pos_of_pos hn_pos (-α)
  have hcancel : (n : ℝ) ^ α * (n : ℝ) ^ (-α) = 1 := by
    rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
  have hp_lo : (c / 2) * (n : ℝ) ^ (-α) ≤ p n := by
    calc (c / 2) * (n : ℝ) ^ (-α) ≤ ((n : ℝ) ^ α * p n) * (n : ℝ) ^ (-α) :=
          mul_le_mul_of_nonneg_right hlo.le hrpow_neg_pos.le
      _ = p n * ((n : ℝ) ^ α * (n : ℝ) ^ (-α)) := by ring
      _ = p n := by rw [hcancel, mul_one]
  have hp_hi : p n ≤ (2 * c) * (n : ℝ) ^ (-α) := by
    calc p n = p n * ((n : ℝ) ^ α * (n : ℝ) ^ (-α)) := by rw [hcancel, mul_one]
      _ = ((n : ℝ) ^ α * p n) * (n : ℝ) ^ (-α) := by ring
      _ ≤ (2 * c) * (n : ℝ) ^ (-α) := mul_le_mul_of_nonneg_right hhi.le hrpow_neg_pos.le
  exact ⟨hn6, lt_of_lt_of_le (by positivity) hp_lo, hpq, hp_lo, hp_hi⟩

private lemma choose_mul_poly_le {n : ℕ} {p α c B : ℝ}
    (hn6 : 6 ≤ n) (hp_pos : 0 < p) (hp1_lt : p < 1) (hc : 0 < c)
    (hp_hi : p ≤ (2 * c) * (n : ℝ) ^ (-α)) (hB : B ≤ 2) (hB0 : 0 ≤ B) :
    (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * B ≤ 2 * (2 * c) ^ 3 * (n : ℝ) ^ (3 - 3 * α) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨_, hch_hi⟩ := choose_three_bounds hn6
  have hp3_hi : p ^ 3 ≤ (2 * c) ^ 3 * (n : ℝ) ^ (-3 * α) := by
    calc p ^ 3 ≤ ((2 * c) * (n : ℝ) ^ (-α)) ^ 3 := pow_le_pow_left₀ hp_pos.le hp_hi 3
      _ = (2 * c) ^ 3 * (n : ℝ) ^ (-3 * α) := by rw [mul_pow, rpow_nat_pow_eq hn_pos 3]; ring_nf
  have h1p3_nn : 0 ≤ 1 - p ^ 3 := by
    have hp3_le1 : p ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hp_pos.le hp1_lt.le 3
    linarith
  have hm1 := mul_le_mul hch_hi hp3_hi (by positivity) (by positivity)
  have hm2 : (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) ≤
      (n : ℝ) ^ 3 * ((2 * c) ^ 3 * (n : ℝ) ^ (-3 * α)) * 1 :=
    mul_le_mul hm1 (sub_le_self 1 (by positivity)) h1p3_nn (by positivity)
  calc
    (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * B
      ≤ ((n : ℝ) ^ 3 * ((2 * c) ^ 3 * (n : ℝ) ^ (-3 * α)) * 1) * 2 :=
        mul_le_mul hm2 hB hB0 (by positivity)
    _ = 2 * (2 * c) ^ 3 * ((n : ℝ) ^ (3 : ℝ) * (n : ℝ) ^ (-3 * α)) := by
        have hc3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by norm_cast
        rw [hc3]; ring
    _ = 2 * (2 * c) ^ 3 * (n : ℝ) ^ (3 - 3 * α) := by
        rw [← Real.rpow_add hn_pos]; ring_nf

private lemma eventually_triangle_rhs_bounds
    {p : ℕ → ℝ} {α c : ℝ}
    (hα0 : 0 ≤ α) (hc : 0 < c) (hc0 : α = 0 → c < 1)
    (htend : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) atTop (nhds c)) :
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    let rhs₁ : ℕ → ℝ := fun n ↦
      (3 * (n : ℝ) - 8) ^ 2 / σ n ^ 3 *
        ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 2 + p n ^ 6))
    let rhs₂ : ℕ → ℝ := fun n ↦
      Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
        (Real.sqrt Real.pi * σ n ^ 2) *
        Real.sqrt ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 3 + p n ^ 9))
    ∃ C₁ C₂ : ℝ, ∀ᶠ n : ℕ in atTop,
      (0 ≤ rhs₁ n ∧ rhs₁ n ≤ C₁ * (n : ℝ) ^ (9 * α / 2 - 1)) ∧
      (0 ≤ rhs₂ n ∧ rhs₂ n ≤ C₂ * (n : ℝ) ^ (7 * α / 2 - 1)) ∧
      wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw ≤
        ENNReal.ofReal (rhs₁ n + rhs₂ n) := by
  intro T μ σ W rhs₁ rhs₂
  obtain ⟨q, _, hq1, hev⟩ := eventually_triangle_scaling_bounds hα0 hc hc0 htend
  set K₀ : ℝ := (c / 2) ^ 5 * (1 - q) / 16
  have h1q_pos : 0 < 1 - q := by linarith
  have hK₀_pos : 0 < K₀ := by positivity
  set C₁ : ℝ := 18 * (2 * c) ^ 3 / (K₀ * Real.sqrt K₀)
  set C₂ : ℝ := Real.sqrt 26 * 3 ^ ((3 : ℝ) / 2) * Real.sqrt (2 * (2 * c) ^ 3) /
    (Real.sqrt Real.pi * K₀)
  refine ⟨C₁, C₂, ?_⟩
  filter_upwards [hev] with n ⟨hn6, hp_pos, hpq, hp_lo, hp_hi⟩
  have hp1_lt : p n < 1 := hpq.trans hq1
  obtain ⟨_, hVar, hWass_raw⟩ := Sec3_2_1_triangles_restricted_proof stdNormalLaw
    (n := n) (p := p n) (Z := id) (by omega : 3 ≤ n) hp_pos hp1_lt
    measurable_id.aemeasurable Measure.map_id
  rw [Measure.map_id] at hWass_raw
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn6_r : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
  obtain ⟨hch_lo, _⟩ := choose_three_bounds hn6
  have hp5_lo : (c / 2) ^ 5 * (n : ℝ) ^ (-5 * α) ≤ p n ^ 5 := by
    calc (c / 2) ^ 5 * (n : ℝ) ^ (-5 * α) = ((c / 2) * (n : ℝ) ^ (-α)) ^ 5 := by
          rw [mul_pow, rpow_nat_pow_eq hn_pos 5]; ring_nf
      _ ≤ p n ^ 5 := pow_le_pow_left₀ (by positivity) hp_lo 5
  have h1p3_nn : 0 ≤ 1 - p n ^ 3 := by
    have hp3_le1 : p n ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hp_pos.le hp1_lt.le 3
    linarith
  have hVar_lo : K₀ * (n : ℝ) ^ (4 - 5 * α) ≤ variance (T n) (erdosRenyi n (p n)) := by
    rw [hVar]
    have hch_n3 : (n : ℝ) ^ 4 / 16 ≤ 3 * (n.choose 3 : ℝ) * ((n : ℝ) - 3) := by
      have hm := mul_le_mul hch_lo (by linarith : (n : ℝ) / 2 ≤ (n : ℝ) - 3)
        (by positivity) (Nat.cast_nonneg _)
      linarith [show 3 * (((n : ℝ) ^ 3 / 24) * ((n : ℝ) / 2)) = (n : ℝ) ^ 4 / 16 by ring]
    have hm2 : ((n : ℝ) ^ 4 / 16) * ((c / 2) ^ 5 * (n : ℝ) ^ (-5 * α)) * (1 - q) ≤
        (3 * (n.choose 3 : ℝ) * ((n : ℝ) - 3)) * p n ^ 5 * (1 - p n) :=
      mul_le_mul
        (mul_le_mul hch_n3 hp5_lo (by positivity)
          (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith)))
        (by linarith : 1 - q ≤ 1 - p n) h1q_pos.le
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by linarith))
          (by positivity))
    have hdrop : (3 * (n.choose 3 : ℝ) * ((n : ℝ) - 3)) * p n ^ 5 * (1 - p n) ≤
        (n.choose 3 : ℝ) * p n ^ 3 *
          (1 - p n ^ 3 + 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n)) := by
      have hnn : 0 ≤ (n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) := by positivity
      linarith [show (n.choose 3 : ℝ) * p n ^ 3 *
          (1 - p n ^ 3 + 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n)) -
        (3 * (n.choose 3 : ℝ) * ((n : ℝ) - 3)) * p n ^ 5 * (1 - p n) =
        (n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) by ring]
    calc
      K₀ * (n : ℝ) ^ (4 - 5 * α)
        = ((n : ℝ) ^ 4 / 16) * ((c / 2) ^ 5 * (n : ℝ) ^ (-5 * α)) * (1 - q) := by
          dsimp only [K₀]
          have hc4 : (n : ℝ) ^ (4 : ℝ) = (n : ℝ) ^ 4 := by norm_cast
          rw [show (n : ℝ) ^ (4 - 5 * α) = (n : ℝ) ^ (4 : ℝ) * (n : ℝ) ^ (-5 * α) by
            rw [← Real.rpow_add hn_pos]; ring_nf, hc4]
          ring
      _ ≤ _ := hm2.trans hdrop
  have hVar_pos : 0 < variance (T n) (erdosRenyi n (p n)) :=
    lt_of_lt_of_le (mul_pos hK₀_pos (Real.rpow_pos_of_pos hn_pos _)) hVar_lo
  have hσ2 : σ n ^ 2 = variance (T n) (erdosRenyi n (p n)) := Real.sq_sqrt hVar_pos.le
  have hσ_lo : Real.sqrt K₀ * (n : ℝ) ^ (2 - 5 * α / 2) ≤ σ n := by
    have hsq_eq : Real.sqrt (K₀ * (n : ℝ) ^ (4 - 5 * α)) =
        Real.sqrt K₀ * (n : ℝ) ^ (2 - 5 * α / 2) := by
      rw [Real.sqrt_mul hK₀_pos.le, Real.sqrt_eq_rpow ((n : ℝ) ^ (4 - 5 * α)),
        ← Real.rpow_mul hn_pos.le]
      congr 2; ring
    exact hsq_eq ▸ Real.sqrt_le_sqrt hVar_lo
  have hσ3_lo : K₀ * Real.sqrt K₀ * (n : ℝ) ^ (6 - 15 * α / 2) ≤ σ n ^ 3 := by
    calc K₀ * Real.sqrt K₀ * (n : ℝ) ^ (6 - 15 * α / 2)
        = (Real.sqrt K₀ * (n : ℝ) ^ (2 - 5 * α / 2)) ^ 3 := by
          rw [mul_pow, rpow_nat_pow_eq hn_pos 3]
          have hsqK : Real.sqrt K₀ ^ 3 = K₀ * Real.sqrt K₀ := by
            calc Real.sqrt K₀ ^ 3 = Real.sqrt K₀ ^ 2 * Real.sqrt K₀ := by ring
              _ = K₀ * Real.sqrt K₀ := by rw [Real.sq_sqrt hK₀_pos.le]
          rw [hsqK]; ring_nf
      _ ≤ σ n ^ 3 := pow_le_pow_left₀ (by positivity) hσ_lo 3
  have h3n8_nn : 0 ≤ 3 * (n : ℝ) - 8 := by linarith
  have h3n8_hi : 3 * (n : ℝ) - 8 ≤ 3 * (n : ℝ) := by linarith
  have hpoly6 : (1 - p n ^ 3) ^ 2 + p n ^ 6 ≤ 2 := by
    linarith [pow_le_pow_left₀ h1p3_nn (sub_le_self 1 (by positivity)) 2,
      pow_le_pow_left₀ hp_pos.le hp1_lt.le 6]
  have hpoly9 : (1 - p n ^ 3) ^ 3 + p n ^ 9 ≤ 2 := by
    linarith [pow_le_pow_left₀ h1p3_nn (sub_le_self 1 (by positivity)) 3,
      pow_le_pow_left₀ hp_pos.le hp1_lt.le 9]
  have hnum3_hi := choose_mul_poly_le hn6 hp_pos hp1_lt hc hp_hi hpoly6 (by positivity)
  have hnum4_hi := choose_mul_poly_le hn6 hp_pos hp1_lt hc hp_hi hpoly9 (by positivity)
  have hrhs1_le :
      (3 * (n : ℝ) - 8) ^ 2 / σ n ^ 3 *
          ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 2 + p n ^ 6)) ≤
        C₁ * (n : ℝ) ^ (9 * α / 2 - 1) := by
    have hsq_hi : (3 * (n : ℝ) - 8) ^ 2 ≤ (3 * (n : ℝ)) ^ 2 :=
      pow_le_pow_left₀ h3n8_nn h3n8_hi 2
    have hdiv : (3 * (n : ℝ) - 8) ^ 2 / σ n ^ 3 ≤
        (3 * (n : ℝ)) ^ 2 / (K₀ * Real.sqrt K₀ * (n : ℝ) ^ (6 - 15 * α / 2)) := by gcongr
    calc
      _ ≤ ((3 * (n : ℝ)) ^ 2 / (K₀ * Real.sqrt K₀ * (n : ℝ) ^ (6 - 15 * α / 2))) *
            (2 * (2 * c) ^ 3 * (n : ℝ) ^ (3 - 3 * α)) :=
          mul_le_mul hdiv hnum3_hi (by positivity) (by positivity)
      _ = C₁ * ((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (3 - 3 * α) /
            (n : ℝ) ^ (6 - 15 * α / 2)) := by
          dsimp only [C₁]
          have hc2 : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := by norm_cast
          rw [hc2]; ring_nf
      _ = C₁ * (n : ℝ) ^ (9 * α / 2 - 1) := by
          rw [← Real.rpow_add hn_pos, ← Real.rpow_sub hn_pos]; congr 2; ring
  have hrhs2_le :
      Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
          (Real.sqrt Real.pi * σ n ^ 2) *
          Real.sqrt
            ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 3 + p n ^ 9)) ≤
        C₂ * (n : ℝ) ^ (7 * α / 2 - 1) := by
    have hrpow_hi : (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) ≤
        3 ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) :=
      (Real.rpow_le_rpow h3n8_nn h3n8_hi (by positivity)).trans_eq
        (Real.mul_rpow (by positivity) hn_pos.le)
    have hsqrt_hi :
        Real.sqrt
            ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 3 + p n ^ 9)) ≤
          Real.sqrt (2 * (2 * c) ^ 3) * (n : ℝ) ^ ((3 - 3 * α) / 2) := by
      calc
        _ ≤ Real.sqrt (2 * (2 * c) ^ 3 * (n : ℝ) ^ (3 - 3 * α)) := Real.sqrt_le_sqrt hnum4_hi
        _ = Real.sqrt (2 * (2 * c) ^ 3) * Real.sqrt ((n : ℝ) ^ (3 - 3 * α)) :=
            Real.sqrt_mul (by positivity) _
        _ = Real.sqrt (2 * (2 * c) ^ 3) * (n : ℝ) ^ ((3 - 3 * α) / 2) := by
            rw [Real.sqrt_eq_rpow ((n : ℝ) ^ (3 - 3 * α)), ← Real.rpow_mul hn_pos.le]; ring_nf
    have hden_lo :
        Real.sqrt Real.pi * (K₀ * (n : ℝ) ^ (4 - 5 * α)) ≤ Real.sqrt Real.pi * σ n ^ 2 := by
      rw [hσ2]; exact mul_le_mul_of_nonneg_left hVar_lo (Real.sqrt_nonneg _)
    have hdiv :
        Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) / (Real.sqrt Real.pi * σ n ^ 2) ≤
          Real.sqrt 26 * (3 ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)) /
            (Real.sqrt Real.pi * (K₀ * (n : ℝ) ^ (4 - 5 * α))) := by gcongr
    calc
      _ ≤ (Real.sqrt 26 * (3 ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)) /
            (Real.sqrt Real.pi * (K₀ * (n : ℝ) ^ (4 - 5 * α)))) *
            (Real.sqrt (2 * (2 * c) ^ 3) * (n : ℝ) ^ ((3 - 3 * α) / 2)) :=
          mul_le_mul hdiv hsqrt_hi (Real.sqrt_nonneg _) (by positivity)
      _ = C₂ * ((n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 - 3 * α) / 2) /
            (n : ℝ) ^ (4 - 5 * α)) := by dsimp only [C₂]; ring_nf
      _ = C₂ * (n : ℝ) ^ (7 * α / 2 - 1) := by
          rw [← Real.rpow_add hn_pos, ← Real.rpow_sub hn_pos]; congr 2; ring
  exact ⟨⟨by positivity, hrhs1_le⟩, ⟨by positivity, hrhs2_le⟩, hWass_raw⟩

/-! ### Section 3: Proof of Section 3.2.1 CLT Regime (`P3` + `K2`) -/

/-- Section 3.2.1 triangle-count variance divergence ($0 \le \alpha < 1$) and normal approximation
CLT regime ($0 \le \alpha < 2/9$), restricted (`SteinIntro.tex:941-945`; `ISSUE-TYPO-3.2.1`,
`ISSUE-3.2.1`, `review-04.md` `P3`, `stmts-review-05K.md` `K2`). -/
theorem Sec3_2_1_triangles_clt_regime_restricted_proof
    {p : ℕ → ℝ} {α c : ℝ}
    (_hp : ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1)
    (hα0 : 0 ≤ α) (hc : 0 < c) (hc0 : α = 0 → c < 1)
    (htend : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) atTop (nhds c)) :
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    let rhs : ℕ → ℝ := fun n ↦
      (3 * (n : ℝ) - 8) ^ 2 / σ n ^ 3 *
          ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 2 + p n ^ 6)) +
        Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
          (Real.sqrt Real.pi * σ n ^ 2) *
          Real.sqrt
            ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 3 + p n ^ 9))
    (α < 1 →
      Tendsto (fun n : ℕ ↦ variance (T n) (erdosRenyi n (p n))) atTop atTop) ∧
    (α < 2 / 9 →
      Tendsto rhs atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        atTop (nhds 0)) := by
  intro T μ σ W rhs
  obtain ⟨q, hq0, hq1, hev⟩ := eventually_triangle_scaling_bounds hα0 hc hc0 htend
  constructor
  · intro hα1
    have hq3_pos : 0 < 1 - q ^ 3 := by
      rw [show 1 - q ^ 3 = (1 - q) * ((q + 1 / 2) ^ 2 + 3 / 4) by ring]
      exact mul_pos (by linarith) (by positivity)
    set K₁ : ℝ := (c / 2) ^ 3 * (1 - q ^ 3) / 24
    have hK₁_pos : 0 < K₁ := by positivity
    refine tendsto_atTop_mono' atTop ?_
      (Tendsto.const_mul_atTop hK₁_pos (tendsto_nat_rpow_atTop (by linarith : 0 < 3 - 3 * α)))
    filter_upwards [hev] with n ⟨hn6, hp_pos, hpq, hp_lo, _⟩
    have hp1_lt : p n < 1 := hpq.trans hq1
    obtain ⟨_, hVar, _⟩ := Sec3_2_1_triangles_restricted_proof stdNormalLaw (n := n) (p := p n)
      (Z := id) (by omega : 3 ≤ n) hp_pos hp1_lt measurable_id.aemeasurable Measure.map_id
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn6_r : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn6
    obtain ⟨hch_lo, _⟩ := choose_three_bounds hn6
    have hp3_lo : (c / 2) ^ 3 * (n : ℝ) ^ (-3 * α) ≤ p n ^ 3 := by
      calc (c / 2) ^ 3 * (n : ℝ) ^ (-3 * α) = ((c / 2) * (n : ℝ) ^ (-α)) ^ 3 := by
            rw [mul_pow, rpow_nat_pow_eq hn_pos 3]; ring_nf
        _ ≤ p n ^ 3 := pow_le_pow_left₀ (by positivity) hp_lo 3
    have h1p3_lo : 1 - q ^ 3 ≤ 1 - p n ^ 3 := by
      linarith [pow_le_pow_left₀ hp_pos.le hpq.le 3]
    have hextra_nn : 0 ≤ 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg _)) (by linarith)
    rw [hVar]
    calc
      K₁ * (n : ℝ) ^ (3 - 3 * α)
        = ((n : ℝ) ^ 3 / 24) * ((c / 2) ^ 3 * (n : ℝ) ^ (-3 * α)) * (1 - q ^ 3) := by
          dsimp only [K₁]
          have hc3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by norm_cast
          rw [show (n : ℝ) ^ (3 - 3 * α) = (n : ℝ) ^ (3 : ℝ) * (n : ℝ) ^ (-3 * α) by
            rw [← Real.rpow_add hn_pos]; ring_nf, hc3]
          ring
      _ ≤ (n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) :=
          mul_le_mul (mul_le_mul hch_lo hp3_lo (by positivity) (Nat.cast_nonneg _))
            h1p3_lo hq3_pos.le (by positivity)
      _ ≤ _ :=
          mul_le_mul_of_nonneg_left
            (by linarith :
              1 - p n ^ 3 ≤ 1 - p n ^ 3 + 3 * ((n : ℝ) - 3) * p n ^ 2 * (1 - p n))
            (by positivity)
  · intro hα29
    obtain ⟨C₁, C₂, hev_rhs⟩ := eventually_triangle_rhs_bounds hα0 hc hc0 htend
    have ht1 : Tendsto (fun n : ℕ ↦ C₁ * (n : ℝ) ^ (9 * α / 2 - 1)) atTop (nhds 0) := by
      simpa using (tendsto_nat_rpow_zero_of_neg (by linarith)).const_mul C₁
    have ht2 : Tendsto (fun n : ℕ ↦ C₂ * (n : ℝ) ^ (7 * α / 2 - 1)) atTop (nhds 0) := by
      simpa using (tendsto_nat_rpow_zero_of_neg (by linarith)).const_mul C₂
    have hupper_zero : Tendsto
        (fun n : ℕ ↦ C₁ * (n : ℝ) ^ (9 * α / 2 - 1) + C₂ * (n : ℝ) ^ (7 * α / 2 - 1))
        atTop (nhds 0) := by simpa using ht1.add ht2
    have hrhs_zero : Tendsto rhs atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_zero
        (hev_rhs.mono fun _ h ↦ add_nonneg h.1.1 h.2.1.1)
        (hev_rhs.mono fun _ h ↦ add_le_add h.1.2 h.2.1.2)
    have hofReal_rhs : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (rhs n)) atTop (nhds 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal hrhs_zero
    have hwass_zero :
        Tendsto (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hofReal_rhs
        (Eventually.of_forall fun _ ↦ zero_le)
        (hev_rhs.mono fun _ h ↦ h.2.2)
    have hkolm_zero :
        Tendsto (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          atTop (nhds 0) := by
      have hreal_kolm : Tendsto
          (fun n : ℕ ↦ (2 / Real.pi) ^ (1 / 4 : ℝ) * (rhs n) ^ (1 / 2 : ℝ))
          atTop (nhds 0) := by
        have hrpow : Tendsto (fun n : ℕ ↦ (rhs n) ^ (1 / 2 : ℝ)) atTop (nhds 0) := by
          have hc_rpow :=
            ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0).comp hrhs_zero
          rw [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hc_rpow
          exact hc_rpow
        have hmul := hrpow.const_mul ((2 / Real.pi) ^ (1 / 4 : ℝ))
        rwa [mul_zero] at hmul
      have hofReal_kolm : Tendsto
          (fun n : ℕ ↦ ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ) * (rhs n) ^ (1 / 2 : ℝ)))
          atTop (nhds 0) := by
        rw [← ENNReal.ofReal_zero]
        exact ENNReal.tendsto_ofReal hreal_kolm
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hofReal_kolm
        (Eventually.of_forall fun _ ↦ zero_le) ?_
      filter_upwards [hev_rhs] with n ⟨⟨hr1_nn, _⟩, ⟨hr2_nn, _⟩, hwass_le⟩
      have hrhs_nn : 0 ≤ rhs n := add_nonneg hr1_nn hr2_nn
      have hdK := kolmogorovDist_map_le_stdNormal_rpow_wassersteinDist_map
        (erdosRenyi n (p n)) stdNormalLaw (W := W n) (Z := id)
        Measurable.of_discrete.aemeasurable measurable_id.aemeasurable Measure.map_id
      rw [Measure.map_id] at hdK
      calc
        kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw
          ≤ ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ)) *
              wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw ^ (1 / 2 : ℝ) := hdK
        _ ≤ ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ)) *
              ENNReal.ofReal (rhs n) ^ (1 / 2 : ℝ) := by gcongr
        _ = ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ) * (rhs n) ^ (1 / 2 : ℝ)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hrhs_nn (by norm_num : (0 : ℝ) ≤ 1 / 2),
              ← ENNReal.ofReal_mul (by positivity)]
    exact ⟨hrhs_zero, hwass_zero, hkolm_zero⟩

/-! ### Section 4: Threshold Sharpness at $\alpha = 2/9$ and Degeneracy at $p \equiv 1$ -/

/-- At the boundary exponent $\alpha = 2/9$ with $p_n = n^{-2/9}$, the Section 3.2.1 Stein upper
bound (`SteinIntro.tex:937-938`) converges to $3\sqrt{2} > 0$, verifying that $\alpha < 2/9$ is
the sharp threshold of that bound (`review-04.md` `P3`). -/
theorem triangles_bound_tendsto_at_two_ninths :
    let p : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-(2 / 9 : ℝ))
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (variance (T n) (erdosRenyi n (p n)))
    let rhs : ℕ → ℝ := fun n ↦
      (3 * (n : ℝ) - 8) ^ 2 / σ n ^ 3 *
          ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 2 + p n ^ 6)) +
        Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
          (Real.sqrt Real.pi * σ n ^ 2) *
          Real.sqrt
            ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 3 + p n ^ 9))
    Tendsto rhs atTop (nhds (3 * Real.sqrt 2)) := by
  intro p T σ rhs
  let rhs₁ : ℕ → ℝ := fun n ↦
    (3 * (n : ℝ) - 8) ^ 2 / σ n ^ 3 *
      ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 2 + p n ^ 6))
  let rhs₂ : ℕ → ℝ := fun n ↦
    Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
      (Real.sqrt Real.pi * σ n ^ 2) *
      Real.sqrt ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 3 + p n ^ 9))
  have hp_zero : Tendsto p atTop (nhds 0) :=
    tendsto_nat_rpow_zero_of_neg (by norm_num : -(2 / 9 : ℝ) < 0)
  have hinv_n : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hvar_scaled :
      Tendsto (fun n : ℕ ↦ variance (T n) (erdosRenyi n (p n)) / (n : ℝ) ^ (26 / 9 : ℝ))
        atTop (nhds (1 / 2)) := by
    have hp3 : Tendsto (fun n : ℕ ↦ 1 - p n ^ 3) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub (hp_zero.pow 3)
    have htA : Tendsto (fun n : ℕ ↦ (1 - p n ^ 3) * (n : ℝ) ^ (-(5 / 9 : ℝ)))
        atTop (nhds 0) := by
      simpa using hp3.mul (tendsto_nat_rpow_zero_of_neg (by norm_num))
    have htB : Tendsto (fun n : ℕ ↦ 3 * (1 - 3 * ((n : ℝ))⁻¹) * (1 - p n))
        atTop (nhds 3) := by
      have h1 : Tendsto (fun n : ℕ ↦ 1 - 3 * ((n : ℝ))⁻¹) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub (hinv_n.const_mul 3)
      have h2 : Tendsto (fun n : ℕ ↦ 1 - p n) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub hp_zero
      simpa using (h1.const_mul 3).mul h2
    have hprod : Tendsto
        (fun n : ℕ ↦ ((n.choose 3 : ℝ) / (n : ℝ) ^ 3) *
          ((1 - p n ^ 3) * (n : ℝ) ^ (-(5 / 9 : ℝ)) +
            3 * (1 - 3 * ((n : ℝ))⁻¹) * (1 - p n)))
        atTop (nhds (1 / 2)) := by
      rw [show (1 / 2 : ℝ) = (1 / 6) * (0 + 3) by norm_num]
      exact tendsto_choose_three_div_cube.mul (htA.add htB)
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with n hn3
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hp_pos : 0 < p n := Real.rpow_pos_of_pos hn_pos _
    have hp1_lt : p n < 1 :=
      (Real.rpow_lt_rpow_of_exponent_lt hn_gt1 (by norm_num)).trans_eq (Real.rpow_zero _)
    obtain ⟨_, hVar, _⟩ := Sec3_2_1_triangles_restricted_proof stdNormalLaw
      (n := n) (p := p n) (Z := id) hn3 hp_pos hp1_lt measurable_id.aemeasurable Measure.map_id
    rw [hVar]
    have hp3_eq : p n ^ 3 = (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
      dsimp only [p]; rw [rpow_nat_pow_eq hn_pos 3]; ring_nf
    have hp2_eq : p n ^ 2 = (n : ℝ) ^ (-(4 / 9 : ℝ)) := by
      dsimp only [p]; rw [rpow_nat_pow_eq hn_pos 2]; ring_nf
    have hr1 : (n : ℝ) ^ (26 / 9 : ℝ) =
        (n : ℝ) ^ 3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (5 / 9 : ℝ) := by
      have hc3 : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 : ℝ) := by norm_cast
      rw [hc3, ← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]; congr 1; ring
    have hr2 : (n : ℝ) ^ (-(5 / 9 : ℝ)) = ((n : ℝ) ^ (5 / 9 : ℝ))⁻¹ :=
      Real.rpow_neg hn_pos.le (5 / 9)
    have hr3 : ((n : ℝ) - 3) * (n : ℝ) ^ (-(4 / 9 : ℝ)) / (n : ℝ) ^ (5 / 9 : ℝ) =
        1 - 3 * ((n : ℝ))⁻¹ := by
      have h59 : (n : ℝ) ^ (-(4 / 9 : ℝ)) / (n : ℝ) ^ (5 / 9 : ℝ) = ((n : ℝ))⁻¹ := by
        rw [← Real.rpow_sub hn_pos, show -(4 / 9 : ℝ) - 5 / 9 = -1 by ring, Real.rpow_neg_one]
      have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
      rw [mul_div_assoc, h59]; field_simp [hn_ne]
    have hpos59 : (n : ℝ) ^ (5 / 9 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
    have hpos23 : (n : ℝ) ^ (-(2 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
    have hn3_ne : (n : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hn_pos.ne'
    rw [hp3_eq, hp2_eq, hr1, hr2]
    have hsplit :
        (n.choose 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) *
            (1 - (n : ℝ) ^ (-(2 / 3 : ℝ)) +
              3 * ((n : ℝ) - 3) * (n : ℝ) ^ (-(4 / 9 : ℝ)) * (1 - p n)) /
          ((n : ℝ) ^ 3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) * (n : ℝ) ^ (5 / 9 : ℝ)) =
        ((n.choose 3 : ℝ) / (n : ℝ) ^ 3) *
          ((1 - (n : ℝ) ^ (-(2 / 3 : ℝ))) * ((n : ℝ) ^ (5 / 9 : ℝ))⁻¹ +
            3 * (((n : ℝ) - 3) * (n : ℝ) ^ (-(4 / 9 : ℝ)) / (n : ℝ) ^ (5 / 9 : ℝ)) *
              (1 - p n)) := by field_simp [hn3_ne, hpos23, hpos59]
    rw [hsplit, hr3]
  have hσ_scaled :
      Tendsto (fun n : ℕ ↦ (σ n / (n : ℝ) ^ (13 / 9 : ℝ)) ^ 3)
        atTop (nhds ((Real.sqrt (1 / 2)) ^ 3)) := by
    refine (((Real.continuous_sqrt.tendsto (1 / 2)).comp hvar_scaled).congr' ?_).pow 3
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    dsimp only [Function.comp_apply, σ]
    rw [Real.sqrt_div (variance_nonneg _ _),
      Real.sqrt_eq_rpow ((n : ℝ) ^ (26 / 9 : ℝ)), ← Real.rpow_mul hn_pos.le]
    ring_nf
  have hrhs₁_lim : Tendsto rhs₁ atTop (nhds (3 * Real.sqrt 2)) := by
    have h38 : Tendsto (fun n : ℕ ↦ (3 - 8 * ((n : ℝ))⁻¹) ^ 2) atTop (nhds 9) := by
      simpa [show (3 : ℝ) ^ 2 = 9 by norm_num] using
        (tendsto_const_nhds.sub (hinv_n.const_mul 8) :
          Tendsto (fun n : ℕ ↦ 3 - 8 * ((n : ℝ))⁻¹) atTop (nhds (3 - 8 * 0))).pow 2
    have hp3 : Tendsto (fun n : ℕ ↦ 1 - p n ^ 3) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub (hp_zero.pow 3)
    have hp6 : Tendsto (fun n : ℕ ↦ (1 - p n ^ 3) ^ 2 + p n ^ 6) atTop (nhds 1) := by
      simpa using (hp3.pow 2).add (hp_zero.pow 6)
    have hnum : Tendsto
        (fun n : ℕ ↦ (3 - 8 * ((n : ℝ))⁻¹) ^ 2 * ((n.choose 3 : ℝ) / (n : ℝ) ^ 3) *
          (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 2 + p n ^ 6))
        atTop (nhds (3 / 2)) := by
      rw [show (3 / 2 : ℝ) = ((9 * (1 / 6)) * 1) * 1 by norm_num]
      exact ((h38.mul tendsto_choose_three_div_cube).mul hp3).mul hp6
    have hquot := hnum.div hσ_scaled (by positivity : (Real.sqrt (1 / 2)) ^ 3 ≠ 0)
    have hval : (3 / 2 : ℝ) / (Real.sqrt (1 / 2)) ^ 3 = 3 * Real.sqrt 2 := by
      rw [one_div, Real.sqrt_inv, inv_pow, div_inv_eq_mul,
        show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring,
        Real.sq_sqrt (by positivity)]; ring
    rw [hval] at hquot
    refine hquot.congr' ?_
    filter_upwards [eventually_ge_atTop 3] with n hn3
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos.ne'
    have hp3_eq : p n ^ 3 = (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
      dsimp only [p]; rw [rpow_nat_pow_eq hn_pos 3]; ring_nf
    have hrpow_cube : ((n : ℝ) ^ (13 / 9 : ℝ)) ^ 3 =
        (n : ℝ) ^ 2 * (n : ℝ) ^ 3 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
      rw [rpow_nat_pow_eq hn_pos 3]
      have hc2 : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by norm_cast
      have hc3 : (n : ℝ) ^ 3 = (n : ℝ) ^ (3 : ℝ) := by norm_cast
      rw [hc2, hc3, ← Real.rpow_add hn_pos, ← Real.rpow_add hn_pos]; congr 1; ring
    dsimp only [Pi.div_apply, rhs₁]
    rw [div_pow, show 3 - 8 * ((n : ℝ))⁻¹ = (3 * (n : ℝ) - 8) / (n : ℝ) by field_simp [hn_ne],
      div_pow, div_div_eq_mul_div, hrpow_cube]
    conv_rhs =>
      rw [show (n.choose 3 : ℝ) * p n ^ 3 = (n.choose 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) by
        rw [hp3_eq]]
    have hpos23 : (n : ℝ) ^ (-(2 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hn_pos _).ne'
    have hn2_ne : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hn_ne
    have hn3_ne : (n : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hn_ne
    by_cases hσ0 : σ n = 0
    · simp [hσ0]
    · field_simp [hn2_ne, hn3_ne, hpos23, pow_ne_zero 3 hσ0]
  have hrhs₂_lim : Tendsto rhs₂ atTop (nhds 0) := by
    have htend_c : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (2 / 9 : ℝ) * p n) atTop (nhds 1) := by
      refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn1
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      dsimp only [p]; rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
    obtain ⟨_, C₂, hev_rhs⟩ := eventually_triangle_rhs_bounds
      (by norm_num : (0 : ℝ) ≤ 2 / 9) zero_lt_one (by norm_num) htend_c
    have hup : Tendsto (fun n : ℕ ↦ C₂ * (n : ℝ) ^ (7 * (2 / 9 : ℝ) / 2 - 1))
        atTop (nhds 0) := by
      simpa using (tendsto_nat_rpow_zero_of_neg (by norm_num)).const_mul C₂
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (hev_rhs.mono fun _ h ↦ h.2.1.1) (hev_rhs.mono fun _ h ↦ h.2.1.2)
  rw [show (3 * Real.sqrt 2 : ℝ) = 3 * Real.sqrt 2 + 0 by ring]
  exact hrhs₁_lim.add hrhs₂_lim

/-- Counterexample at the $\alpha = 0, c = 1$ boundary (`ISSUE-3.2.1` addendum,
`SteinIntro.tex:942-944`): for $p_n \equiv 1$, $n^0 p_n \to 1$, yet $\operatorname{Var}(T_n) = 0$
for every $n \in \mathbb{N}$ so $\operatorname{Var}(T_n) \not\to \infty$. -/
theorem triangles_clt_counterexample_p_eq_one :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) * (1 : ℝ)) atTop (nhds 1) ∧
    (∀ n : ℕ,
      variance (fun G : SimpleGraph (Fin n) ↦ ((G.cliqueSet 3).ncard : ℝ))
        (erdosRenyi n 1) = 0) ∧
    ¬ Tendsto
      (fun n : ℕ ↦
        variance (fun G : SimpleGraph (Fin n) ↦ ((G.cliqueSet 3).ncard : ℝ))
          (erdosRenyi n 1))
      atTop atTop := by
  have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ) * (1 : ℝ)) atTop (nhds 1) := by simp
  have hvar0 : ∀ n : ℕ,
      variance (fun G : SimpleGraph (Fin n) ↦ ((G.cliqueSet 3).ncard : ℝ))
        (erdosRenyi n 1) = 0 := by
    intro n
    by_cases hn2 : n ≤ 2
    · have hzero : (fun G : SimpleGraph (Fin n) ↦ ((G.cliqueSet 3).ncard : ℝ)) = 0 := by
        funext G
        have hemp : G.cliqueSet 3 = ∅ := by
          ext s; simp only [SimpleGraph.mem_cliqueSet_iff, Set.mem_empty_iff_false, iff_false]
          intro hs; have hle := s.card_le_univ; rw [Fintype.card_fin, hs.2] at hle; omega
        simp [hemp]
      rw [hzero, variance_zero]
    · have htop : (erdosRenyi n 1).real {(⊤ : SimpleGraph (Fin n))} = 1 := by
        have hset : ({(⊤ : SimpleGraph (Fin n))} : Set (SimpleGraph (Fin n))) =
            {G : SimpleGraph (Fin n) |
              (∀ e ∈ (Finset.univ : Finset (EdgePair n)), e.1 ∈ G.edgeSet) ∧
                (∀ e ∈ (∅ : Finset (EdgePair n)), e.1 ∉ G.edgeSet)} := by
          ext G
          simp only [Set.mem_singleton_iff, Finset.mem_univ, forall_true_left,
            Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true]
          refine ⟨by rintro rfl e; simp [SimpleGraph.edgeSet_top, e.2], fun h ↦ ?_⟩
          rw [← SimpleGraph.edgeSet_inj]
          ext e
          by_cases hd : e.IsDiag
          · simp [G.not_mem_edgeSet_of_isDiag hd, SimpleGraph.edgeSet_top, hd]
          · simpa [SimpleGraph.edgeSet_top, hd] using h ⟨e, hd⟩
        rw [hset, erdosRenyi_real_cylinder zero_le_one le_rfl Finset.univ ∅
          (Finset.disjoint_empty_right _)]
        simp
      have hmeas1 : erdosRenyi n 1 {(⊤ : SimpleGraph (Fin n))} = 1 := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        change ENNReal.ofReal ((erdosRenyi n 1).real {(⊤ : SimpleGraph (Fin n))}) = 1
        rw [htop, ENNReal.ofReal_one]
      have hcompl : (erdosRenyi n 1) ({(⊤ : SimpleGraph (Fin n))}ᶜ) = 0 := by
        rw [measure_compl MeasurableSet.of_discrete (measure_ne_top _ _), measure_univ,
          hmeas1, tsub_self]
      have hae_const :
          (fun G : SimpleGraph (Fin n) ↦ ((G.cliqueSet 3).ncard : ℝ)) =ᵐ[erdosRenyi n 1]
            fun _ ↦ ((((⊤ : SimpleGraph (Fin n)).cliqueSet 3).ncard : ℝ)) := by
        rw [Filter.EventuallyEq, ae_iff]
        refine measure_mono_null (fun G hG ↦ ?_) hcompl
        change ¬ ((G.cliqueSet 3).ncard : ℝ) =
            ((((⊤ : SimpleGraph (Fin n)).cliqueSet 3).ncard : ℝ)) at hG
        change G ≠ ⊤
        rintro rfl
        exact hG rfl
      have hev : evariance (fun G : SimpleGraph (Fin n) ↦ ((G.cliqueSet 3).ncard : ℝ))
          (erdosRenyi n 1) = 0 := by rw [evariance_congr hae_const]; simp [evariance]
      simp [variance, hev]
  refine ⟨h1, hvar0, ?_⟩
  simp_rw [hvar0]
  exact not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds

end SteinMethod
