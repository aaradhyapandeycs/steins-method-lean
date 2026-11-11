/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.AntiVoterIrreducible
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Aperiodicity, Unique Stationary Law, and Disconnected Counterexample for Anti-Voter

Completes Backlog Item 5 (`SteinIntro.tex:1101-1111`, citing Aldous–Fill `[af10]`; `ISSUE-3.8`):

* `antiVoter_ergodic_and_unique_stationary`: on any connected finite simple graph `G` that is
  neither bipartite nor isomorphic to `SimpleGraph.cycleGraph (Fintype.card V)` (dropping
  `r`-regularity to strengthen the result), the anti-voter Markov chain is irreducible and
  aperiodic on the set of non-constant labelings $\mathcal{N}(V)$, and admits a unique stationary
  probability distribution on `V → Bool` (whose support is $\mathcal{N}(V)$).
* `antiVoter_disconnected_counterexample`: machine-checked refutation on `Fin 7` ($G = K_3 \sqcup
  C_4$, which is $2$-regular, not bipartite, and not isomorphic to `cycleGraph 7`) showing that
  without `G.Connected`, both irreducibility on $\mathcal{N}(V)$ and (when a bipartite component is
  present) uniqueness of the stationary probability distribution on `V → Bool` fail.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SteinMethod

/-! ### Multi-step anti-voter transitions, self-loops, and simultaneous positivity -/

private noncomputable abbrev avStepBind {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : PMF (V → Bool)) : PMF (V → Bool) :=
  p.bind (antiVoterStep G)

private lemma avStepBind_iterate_eq_bind {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (t : ℕ) (p : PMF (V → Bool)),
      (avStepBind G)^[t] p = p.bind (fun x ↦ (avStepBind G)^[t] (PMF.pure x))
  | 0, p => by simp
  | t + 1, p => by
      rw [Function.iterate_succ_apply', avStepBind_iterate_eq_bind G t p, avStepBind,
        PMF.bind_bind]
      congr 1; ext x; rw [Function.iterate_succ_apply']

private lemma avStepBind_iterate_succ_pure_pos {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ} {x y z : V → Bool}
    (hxy : 0 < ((avStepBind G)^[t] (PMF.pure x)) y)
    (hyz : 0 < antiVoterStep G y z) :
    0 < ((avStepBind G)^[t + 1] (PMF.pure x)) z := by
  rw [Function.iterate_succ_apply', pos_iff_ne_zero, ← PMF.mem_support_iff, avStepBind,
    PMF.mem_support_bind_iff]
  exact ⟨y, (PMF.mem_support_iff _ _).mpr hxy.ne', (PMF.mem_support_iff _ _).mpr hyz.ne'⟩

private lemma univ_and_neighbors_nonempty {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hConn : G.Connected) (hBip : ¬ G.IsBipartite) :
    (Finset.univ : Finset V).Nonempty ∧ ∀ v : V, (G.neighborFinset v).Nonempty := by
  classical
  have hcard : 3 ≤ Fintype.card V := three_le_card_of_not_isBipartite G hBip
  obtain ⟨v₀⟩ := hConn.nonempty
  refine ⟨⟨v₀, Finset.mem_univ v₀⟩, fun v ↦ ?_⟩
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  obtain ⟨u, hu⟩ := (hConn.preconnected v w).nonempty_neighborSet_left hw.symm
  exact ⟨u, (G.mem_neighborFinset v u).mpr hu⟩

/-- Every non-constant configuration on a connected graph has a positive 1-step self-loop
probability under `antiVoterStep G` (`SteinIntro.tex:1103-1111`). -/
theorem antiVoterStep_self_pos_of_nonconst {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hConn : G.Connected)
    {y : V → Bool} (hy : IsNonConstLabeling y) :
    0 < antiVoterStep G y y := by
  rcases hy with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hab : a ≠ b := fun h ↦ Bool.noConfusion (ha.symm.trans (h ▸ hb))
  have hV : (Finset.univ : Finset V).Nonempty := ⟨a, Finset.mem_univ a⟩
  have hN : ∀ v : V, (G.neighborFinset v).Nonempty := by
    intro v
    by_cases hva : v = a
    · subst hva
      obtain ⟨u, hu⟩ := (hConn.preconnected v b).nonempty_neighborSet_left hab
      exact ⟨u, (G.mem_neighborFinset v u).mpr hu⟩
    · obtain ⟨u, hu⟩ := (hConn.preconnected v a).nonempty_neighborSet_left hva
      exact ⟨u, (G.mem_neighborFinset v u).mpr hu⟩
  let T : Finset V := Finset.univ.filter fun z : V ↦ y z = true
  have hT_ne : T.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨v, hvT, u, huT, hvu⟩ :=
    exists_adj_mem_notMem_of_connected hConn hT_ne ⟨b, by simp [T, hb]⟩
  have hyv : y v = true := (Finset.mem_filter.mp hvT).2
  have hyu : y u = false := by
    have hnot : y u ≠ true := fun h ↦ huT (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
    cases hyu' : y u <;> simp_all
  rw [pos_iff_ne_zero, antiVoterStep_ne_zero_iff G hV hN]
  refine ⟨v, u, hvu, ?_⟩
  rw [hyu, Bool.not_false, ← hyv, Function.update_eq_self]

private lemma exists_pos_iterate_of_reach {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : (Finset.univ : Finset V).Nonempty)
    (hN : ∀ v : V, (G.neighborFinset v).Nonempty)
    {x y : V → Bool} (hreach : AntiVoterReach G x y) :
    ∃ t : ℕ, 0 < ((avStepBind G)^[t] (PMF.pure x)) y := by
  induction hreach with
  | refl => exact ⟨0, by simp⟩
  | @tail z w _ hs ih =>
    rcases ih with ⟨t, ht⟩
    exact ⟨t + 1, avStepBind_iterate_succ_pure_pos G ht
      (pos_iff_ne_zero.mpr ((antiVoterStep_ne_zero_iff G hV hN z w).mpr hs))⟩

private lemma pos_iterate_of_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hConn : G.Connected)
    {x y : V → Bool} (hy : IsNonConstLabeling y) {N : ℕ}
    (hN : 0 < ((avStepBind G)^[N] (PMF.pure x)) y) :
    ∀ t : ℕ, N ≤ t → 0 < ((avStepBind G)^[t] (PMF.pure x)) y := by
  have hloop : 0 < antiVoterStep G y y := antiVoterStep_self_pos_of_nonconst G hConn hy
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero => simpa using hN
  | succ d ih => rw [← add_assoc]; exact avStepBind_iterate_succ_pure_pos G ih hloop

private lemma exists_uniform_pos_time {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hConn : G.Connected) (hBip : ¬ G.IsBipartite)
    (hNotCycle : IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V))) :
    ∃ T : ℕ, 1 ≤ T ∧
      ∀ (x y : V → Bool), IsNonConstLabeling y →
        0 < ((avStepBind G)^[T] (PMF.pure x)) y := by
  classical
  obtain ⟨hV, hN⟩ := univ_and_neighbors_nonempty hConn hBip
  have hex : ∀ (x : V → Bool) (y : {y : V → Bool // IsNonConstLabeling y}),
      ∃ n : ℕ, 0 < ((avStepBind G)^[n] (PMF.pure x)) y.1 :=
    fun x y ↦ exists_pos_iterate_of_reach G hV hN
      (antiVoter_irreducible_on_nonconst G hConn hBip hNotCycle y.2)
  let T : ℕ := 1 + Finset.univ.sup
    (fun p : (V → Bool) × {y : V → Bool // IsNonConstLabeling y} ↦
      Classical.choose (hex p.1 p.2))
  refine ⟨T, by omega, fun x y hy ↦ ?_⟩
  let p : (V → Bool) × {y : V → Bool // IsNonConstLabeling y} := (x, ⟨y, hy⟩)
  have hsup : Classical.choose (hex p.1 p.2) ≤
      Finset.univ.sup (fun q : (V → Bool) × {y : V → Bool // IsNonConstLabeling y} ↦
        Classical.choose (hex q.1 q.2)) :=
    Finset.le_sup (f := fun q : (V → Bool) × {y : V → Bool // IsNonConstLabeling y} ↦
      Classical.choose (hex q.1 q.2)) (Finset.mem_univ p)
  exact pos_iterate_of_ge G hConn hy (Classical.choose_spec (hex p.1 p.2)) T (by omega)

/-! ### Stationarity equivalence with `PMF` and Doeblin `ℓ¹` contraction -/

private lemma isAntiVoterStationary_iff_avStepBind {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : Measure (V → Bool)) [IsProbabilityMeasure μ] :
    IsAntiVoterStationary G μ ↔ avStepBind G μ.toPMF = μ.toPMF := by
  refine ⟨fun hstat ↦ ?_, fun hfix y ↦ ?_⟩
  · ext y; rw [avStepBind, PMF.bind_apply, tsum_fintype, Measure.toPMF_apply, hstat y]; rfl
  · have hy := congrArg (fun p : PMF (V → Bool) ↦ p y) hfix
    rw [avStepBind, PMF.bind_apply, tsum_fintype] at hy
    exact hy.symm

private lemma exists_unique_fixed_avStepBind_iterate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hConn : G.Connected) (hBip : ¬ G.IsBipartite) {T : ℕ}
    (hpos : ∀ (x y : V → Bool), IsNonConstLabeling y →
      0 < ((avStepBind G)^[T] (PMF.pure x)) y) :
    ∃ p_star : PMF (V → Bool),
      (avStepBind G)^[T] p_star = p_star ∧
      ∀ p : PMF (V → Bool), (avStepBind G)^[T] p = p → p = p_star := by
  have : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  let E := PiLp 1 (fun _ : V → Bool ↦ ℝ)
  let S : Set E := {w : E | (∀ x : V → Bool, 0 ≤ w x) ∧ ∑ x : V → Bool, w x = 1}
  have hS_closed : IsClosed S := by
    have h1 : IsClosed {w : E | ∀ x : V → Bool, 0 ≤ w x} := by
      have heq : {w : E | ∀ x : V → Bool, 0 ≤ w x} =
          ⋂ x : V → Bool, (fun w : E ↦ w x) ⁻¹' Set.Ici (0 : ℝ) := by ext w; simp
      rw [heq]
      exact isClosed_iInter fun x ↦
        isClosed_Ici.preimage (PiLp.continuous_apply 1 (fun _ : V → Bool ↦ ℝ) x)
    have h2 : IsClosed {w : E | ∑ x : V → Bool, w x = 1} :=
      isClosed_eq
        (continuous_finsetSum Finset.univ fun x _ ↦
          PiLp.continuous_apply 1 (fun _ : V → Bool ↦ ℝ) x)
        continuous_const
    exact h1.inter h2
  let P_T : (V → Bool) → (V → Bool) → ℝ :=
    fun x y ↦ (((avStepBind G)^[T] (PMF.pure x)) y).toReal
  have hP_nonneg : ∀ x y : V → Bool, 0 ≤ P_T x y := fun _ _ ↦ ENNReal.toReal_nonneg
  have hP_sum : ∀ x : V → Bool, ∑ y : V → Bool, P_T x y = 1 := by
    intro x
    have htsum : ∑ y : V → Bool, ((avStepBind G)^[T] (PMF.pure x)) y = 1 := by
      simpa using ((avStepBind G)^[T] (PMF.pure x)).tsum_coe
    rw [← ENNReal.toReal_sum (fun y _ ↦ ((avStepBind G)^[T] (PMF.pure x)).apply_ne_top y),
      htsum, ENNReal.toReal_one]
  let Φ : E → E := fun w ↦ WithLp.toLp 1 (fun y ↦ ∑ x : V → Bool, w x * P_T x y)
  have hMaps : MapsTo Φ S S := by
    rintro w ⟨hw_nn, hw_sum⟩
    refine ⟨fun y ↦ Finset.sum_nonneg fun x _ ↦ mul_nonneg (hw_nn x) (hP_nonneg x y), ?_⟩
    simp only [Φ]
    rw [Finset.sum_comm]
    calc
      ∑ x : V → Bool, ∑ y : V → Bool, w x * P_T x y =
          ∑ x : V → Bool, w x * (∑ y : V → Bool, P_T x y) :=
        Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum _ _ _).symm
      _ = ∑ x : V → Bool, w x := by simp_rw [hP_sum, mul_one]
      _ = 1 := hw_sum
  have hcard : 3 ≤ Fintype.card V := three_le_card_of_not_isBipartite G hBip
  obtain ⟨v₀⟩ := hConn.nonempty
  obtain ⟨v₁, hv₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v₀
  let y₀ : V → Bool := fun w ↦ decide (w = v₀)
  have hy₀ : IsNonConstLabeling y₀ := ⟨⟨v₀, by simp [y₀]⟩, ⟨v₁, by simp [y₀, hv₁]⟩⟩
  have hP_y₀_pos : ∀ x : V → Bool, 0 < P_T x y₀ := fun x ↦
    ENNReal.toReal_pos (hpos x y₀ hy₀).ne' (((avStepBind G)^[T] (PMF.pure x)).apply_ne_top y₀)
  let m₀ : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun x : V → Bool ↦ P_T x y₀)
  have hm₀_pos : 0 < m₀ := (Finset.lt_inf'_iff _).mpr fun x _ ↦ hP_y₀_pos x
  let ε : ℝ := min (1 / 2) m₀
  have hε_pos : 0 < ε := lt_min (by norm_num) hm₀_pos
  have hε_half : ε ≤ 1 / 2 := min_le_left _ _
  have hε_le : ∀ x : V → Bool, ε ≤ P_T x y₀ := fun x ↦
    (min_le_right (1 / 2) m₀).trans (Finset.inf'_le _ (Finset.mem_univ x))
  have hcont_ineq : ∀ u v : E, u ∈ S → v ∈ S →
      dist (Φ u) (Φ v) ≤ (1 - ε) * dist u v := by
    intro u v hu hv
    have hd_sum : ∑ x : V → Bool, (u x - v x) = 0 := by
      rw [Finset.sum_sub_distrib, hu.2, hv.2, sub_self]
    have hdist_uv : dist u v = ∑ x : V → Bool, |u x - v x| := by
      rw [PiLp.dist_eq_of_L1]; exact Finset.sum_congr rfl fun x _ ↦ Real.dist_eq (u x) (v x)
    have hdist_Φ : dist (Φ u) (Φ v) =
        ∑ y : V → Bool, |∑ x : V → Bool, (u x - v x) * P_T x y| := by
      rw [PiLp.dist_eq_of_L1]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Real.dist_eq]; simp only [Φ, ← Finset.sum_sub_distrib, sub_mul]
    rw [hdist_Φ, hdist_uv, ← Finset.add_sum_erase _ _ (Finset.mem_univ y₀)]
    have hy₀_term :
        |∑ x : V → Bool, (u x - v x) * P_T x y₀| ≤
          ∑ x : V → Bool, |u x - v x| * (P_T x y₀ - ε) := by
      have hshift :
          (∑ x : V → Bool, (u x - v x) * P_T x y₀) =
            ∑ x : V → Bool, (u x - v x) * (P_T x y₀ - ε) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd_sum, zero_mul, sub_zero]
      rw [hshift]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ ↦ ?_)
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hε_le x))]
    have hrest_terms :
        (∑ y ∈ Finset.univ.erase y₀, |∑ x : V → Bool, (u x - v x) * P_T x y|) ≤
          ∑ y ∈ Finset.univ.erase y₀, ∑ x : V → Bool, |u x - v x| * P_T x y :=
      Finset.sum_le_sum fun y _ ↦ (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum fun x _ ↦ by rw [abs_mul, abs_of_nonneg (hP_nonneg x y)]
    have htotal :
        (∑ x : V → Bool, |u x - v x| * (P_T x y₀ - ε)) +
            (∑ y ∈ Finset.univ.erase y₀, ∑ x : V → Bool, |u x - v x| * P_T x y) =
          (1 - ε) * ∑ x : V → Bool, |u x - v x| := by
      have hsplit :
          (∑ x : V → Bool, |u x - v x| * (P_T x y₀ - ε)) =
            (∑ x : V → Bool, |u x - v x| * P_T x y₀) -
              ε * ∑ x : V → Bool, |u x - v x| := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        congr 1; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
      have hfull :
          (∑ x : V → Bool, |u x - v x| * P_T x y₀) +
              (∑ y ∈ Finset.univ.erase y₀, ∑ x : V → Bool, |u x - v x| * P_T x y) =
            ∑ x : V → Bool, |u x - v x| := by
        rw [Finset.add_sum_erase _ (fun y ↦ ∑ x : V → Bool, |u x - v x| * P_T x y)
          (Finset.mem_univ y₀), Finset.sum_comm]
        calc
          ∑ x : V → Bool, ∑ y : V → Bool, |u x - v x| * P_T x y =
              ∑ x : V → Bool, |u x - v x| * (∑ y : V → Bool, P_T x y) :=
            Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum _ _ _).symm
          _ = ∑ x : V → Bool, |u x - v x| := by simp_rw [hP_sum, mul_one]
      linarith
    linarith [add_le_add hy₀_term hrest_terms]
  let K : ℝ≥0 := ⟨1 - ε, by linarith⟩
  have hContract : ContractingWith K (hMaps.restrict Φ S S) :=
    ⟨NNReal.coe_lt_one.mp (show (1 - ε : ℝ) < 1 by linarith),
     LipschitzWith.of_dist_le_mul fun u v ↦ hcont_ineq u.1 v.1 u.2 v.2⟩
  let w₀ : E := WithLp.toLp 1 (fun x ↦ if x = y₀ then (1 : ℝ) else 0)
  have hw₀S : w₀ ∈ S := ⟨fun x ↦ by simp only [w₀]; split_ifs <;> norm_num, by simp [w₀]⟩
  obtain ⟨w_star, hw_star_S, hw_star_fix, _, _⟩ :=
    hContract.exists_fixedPoint' hS_closed.isComplete hMaps hw₀S (edist_ne_top w₀ (Φ w₀))
  have hw_unique : ∀ w ∈ S, Φ w = w → w = w_star := by
    intro w hw hfix
    have hd := hcont_ineq w w_star hw hw_star_S
    rw [hfix, hw_star_fix.eq] at hd
    have hd_nn : 0 ≤ dist w w_star := dist_nonneg
    exact dist_eq_zero.mp (by nlinarith)
  have hhasSum : HasSum (fun x : V → Bool ↦ ENNReal.ofReal (w_star x)) 1 := by
    have hsum1 : (∑ x : V → Bool, ENNReal.ofReal (w_star x)) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ hw_star_S.1 x), hw_star_S.2, ENNReal.ofReal_one]
    simpa only [hsum1] using hasSum_fintype (fun x : V → Bool ↦ ENNReal.ofReal (w_star x))
  let p_star : PMF (V → Bool) := ⟨fun x ↦ ENNReal.ofReal (w_star x), hhasSum⟩
  let toVec : PMF (V → Bool) → E := fun p ↦ WithLp.toLp 1 (fun x ↦ (p x).toReal)
  have htoVec_mem : ∀ p : PMF (V → Bool), toVec p ∈ S := by
    intro p
    refine ⟨fun x ↦ ENNReal.toReal_nonneg, ?_⟩
    simp only [toVec]
    have htsum : ∑ x : V → Bool, p x = 1 := by simpa using p.tsum_coe
    rw [← ENNReal.toReal_sum (fun x _ ↦ p.apply_ne_top x), htsum, ENNReal.toReal_one]
  have htoVec_inj : Function.Injective toVec := fun p q hpq ↦ PMF.ext fun x ↦
    (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top x) (q.apply_ne_top x)).mp
      (congrArg (fun w : E ↦ w x) hpq)
  have htoVec_iter : ∀ p : PMF (V → Bool), toVec ((avStepBind G)^[T] p) = Φ (toVec p) := by
    intro p; ext y
    simp only [toVec, Φ, P_T]
    rw [avStepBind_iterate_eq_bind G T p, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun x _ ↦
        ENNReal.mul_ne_top (p.apply_ne_top x)
          (((avStepBind G)^[T] (PMF.pure x)).apply_ne_top y))]
    exact Finset.sum_congr rfl fun x _ ↦ ENNReal.toReal_mul
  have htoVec_p_star : toVec p_star = w_star := by
    ext x; exact ENNReal.toReal_ofReal (hw_star_S.1 x)
  refine ⟨p_star, htoVec_inj (by rw [htoVec_iter p_star, htoVec_p_star, hw_star_fix.eq]),
    fun p hp ↦ htoVec_inj ?_⟩
  rw [htoVec_p_star]
  exact hw_unique (toVec p) (htoVec_mem p) (by rw [← htoVec_iter p, hp])

/-- **Ergodicity and unique stationary distribution of the anti-voter Markov chain**
(`SteinIntro.tex:1110-1111`, citing Aldous–Fill `[af10]`; `ISSUE-3.8`): if `G` is a connected
finite simple graph that is neither bipartite nor isomorphic to `cycleGraph |V|`, then:
1. On non-constant labelings $\mathcal{N}(V)$, `antiVoterStep G` is irreducible and aperiodic;
2. `antiVoterStep G` admits a unique stationary probability measure on `V → Bool`, whose support
   is $\mathcal{N}(V)$.

Compared with the printed claim at `SteinIntro.tex:1110-1111` (`ISSUE-3.8`):
(a) irreducibility/aperiodicity is stated on $\mathcal{N}(V)$ rather than $\{-1, 1\}^V$;
(b) `G.Connected` is added (omitted in the printed text; refuted without connectedness by
`antiVoter_disconnected_counterexample`);
(c) `r`-regularity is dropped here, strengthening the result. -/
theorem antiVoter_ergodic_and_unique_stationary {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hConn : G.Connected) (hBip : ¬ G.IsBipartite)
    (hNotCycle : IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V))) :
    (∀ ⦃x y : V → Bool⦄,
      ((∃ a : V, x a = true) ∧ (∃ b : V, x b = false)) →
      ((∃ a : V, y a = true) ∧ (∃ b : V, y b = false)) →
      ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
        0 < ((fun p : PMF (V → Bool) ↦ p.bind (antiVoterStep G))^[t] (PMF.pure x)) y) ∧
    (∃ ν : Measure (V → Bool),
      IsProbabilityMeasure ν ∧
      IsAntiVoterStationary G ν ∧
      (∀ x : V → Bool,
        ν {x} ≠ 0 ↔ (∃ a : V, x a = true) ∧ (∃ b : V, x b = false)) ∧
      ∀ μ : Measure (V → Bool),
        IsProbabilityMeasure μ → IsAntiVoterStationary G μ → μ = ν) := by
  obtain ⟨hV, hN⟩ := univ_and_neighbors_nonempty hConn hBip
  refine ⟨fun x y _ hy ↦ ?_, ?_⟩
  · obtain ⟨N, hN_pos⟩ := exists_pos_iterate_of_reach G hV hN
      (antiVoter_irreducible_on_nonconst G hConn hBip hNotCycle hy)
    exact ⟨N, pos_iterate_of_ge G hConn hy hN_pos⟩
  · obtain ⟨T, _, hposT⟩ := exists_uniform_pos_time G hConn hBip hNotCycle
    obtain ⟨p_star, hpT, hp_uniq⟩ :=
      exists_unique_fixed_avStepBind_iterate G hConn hBip hposT
    have hp1 : avStepBind G p_star = p_star := by
      apply hp_uniq (avStepBind G p_star)
      rw [(Function.Commute.refl (avStepBind G)).iterate_left T p_star, hpT]
    let ν : Measure (V → Bool) := p_star.toMeasure
    have hν_stat : IsAntiVoterStationary G ν := by
      rw [isAntiVoterStationary_iff_avStepBind G ν, PMF.toMeasure_toPMF]; exact hp1
    refine ⟨ν, inferInstance, hν_stat, fun y ↦ ?_, fun μ hμ_prob hμ_stat ↦ ?_⟩
    · rw [p_star.toMeasure_apply_singleton y (measurableSet_singleton y)]
      refine ⟨fun hne ↦ ?_, fun hy_nc ↦ ?_⟩
      · rw [← hp1, avStepBind, PMF.bind_apply, tsum_fintype] at hne
        obtain ⟨x, _, hx_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
        exact antiVoterStep_support_nonconst G hV hN (right_ne_zero_of_mul hx_ne)
      · obtain ⟨x₀, hx₀⟩ := p_star.support_nonempty
        rw [PMF.mem_support_iff] at hx₀
        rw [← hpT, avStepBind_iterate_eq_bind G T p_star, PMF.bind_apply, tsum_fintype]
        have hterm : p_star x₀ * ((avStepBind G)^[T] (PMF.pure x₀)) y ≠ 0 :=
          mul_ne_zero hx₀ (hposT x₀ y hy_nc).ne'
        exact fun hsum0 ↦ hterm ((Finset.sum_eq_zero_iff.mp hsum0) x₀ (Finset.mem_univ x₀))
    · have hμ1 : avStepBind G μ.toPMF = μ.toPMF :=
        (isAntiVoterStationary_iff_avStepBind G μ).mp hμ_stat
      have hμT : ∀ n : ℕ, (avStepBind G)^[n] μ.toPMF = μ.toPMF := by
        intro n; induction n with
        | zero => rfl
        | succ n ih => rw [Function.iterate_succ_apply', ih, hμ1]
      exact (PMF.toPMF_eq_iff_toMeasure_eq p_star μ).mp (hp_uniq μ.toPMF (hμT T))

/-! ### Disconnected `2`-regular counterexample `K_3 ⊔ C_4` on `Fin 7` (`ISSUE-3.8`) -/

private def disconnAdjBool (i j : Fin 7) : Bool :=
  (decide (i.1 < 3) && decide (j.1 < 3) && decide (i ≠ j)) ||
  (decide (i.1 = 3) && (decide (j.1 = 4) || decide (j.1 = 6))) ||
  (decide (i.1 = 4) && (decide (j.1 = 3) || decide (j.1 = 5))) ||
  (decide (i.1 = 5) && (decide (j.1 = 4) || decide (j.1 = 6))) ||
  (decide (i.1 = 6) && (decide (j.1 = 3) || decide (j.1 = 5)))

/-- Disconnected `2`-regular graph $G = K_3 \sqcup C_4$ on `Fin 7`: `{0, 1, 2}` is a triangle and
`{3, 4, 5, 6}` is the 4-cycle `3 ~ 4 ~ 5 ~ 6 ~ 3`. -/
def disconnAntiVoterGraph : SimpleGraph (Fin 7) where
  Adj i j := disconnAdjBool i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel disconnAntiVoterGraph.Adj :=
  fun i j ↦ inferInstanceAs (Decidable (disconnAdjBool i j = true))

private lemma disconn_regular : disconnAntiVoterGraph.IsRegularOfDegree 2 := by
  intro v; fin_cases v <;> decide

private lemma disconn_not_bipartite : ¬ disconnAntiVoterGraph.IsBipartite := by
  rintro ⟨col⟩
  have h01 : (col 0).1 ≠ (col 1).1 := Fin.val_ne_of_ne (col.valid (by decide))
  have h12 : (col 1).1 ≠ (col 2).1 := Fin.val_ne_of_ne (col.valid (by decide))
  have h02 : (col 0).1 ≠ (col 2).1 := Fin.val_ne_of_ne (col.valid (by decide))
  have := (col 0).2; have := (col 1).2; have := (col 2).2
  omega

private lemma disconn_not_cycle :
    IsEmpty (disconnAntiVoterGraph ≃g SimpleGraph.cycleGraph (Fintype.card (Fin 7))) := by
  refine ⟨fun φ ↦ ?_⟩
  have hcard : Fintype.card (Fin 7) = 7 := Fintype.card_fin 7
  let ψ : disconnAntiVoterGraph ≃g SimpleGraph.cycleGraph 7 :=
    φ.trans (hcard ▸ SimpleGraph.Iso.refl)
  have htri : ∀ a b c : Fin 7,
      ¬ ((SimpleGraph.cycleGraph 7).Adj a b ∧
         (SimpleGraph.cycleGraph 7).Adj b c ∧
         (SimpleGraph.cycleGraph 7).Adj a c) := by decide
  exact htri (ψ 0) (ψ 1) (ψ 2)
    ⟨ψ.map_rel_iff.mpr (by decide), ψ.map_rel_iff.mpr (by decide), ψ.map_rel_iff.mpr (by decide)⟩

private def embedK3 (b : Bool) (x₀ : Fin 3 → Bool) : Fin 7 → Bool :=
  fun i ↦ if hi : i.1 < 3 then x₀ ⟨i.1, hi⟩ else if i.1 = 3 ∨ i.1 = 5 then b else !b

private lemma embedK3_injective (b : Bool) : Function.Injective (embedK3 b) := by
  intro x₁ x₂ h; ext a
  simpa [embedK3, a.2] using congrFun h ⟨a.1, by omega⟩

private def nonConstK3Finset : Finset (Fin 3 → Bool) :=
  Finset.univ.filter fun x : Fin 3 → Bool ↦ ¬ (x 0 = x 1 ∧ x 1 = x 2)

private lemma nonConstK3Finset_card : nonConstK3Finset.card = 6 := by decide

private def disconnSector (b : Bool) : Finset (Fin 7 → Bool) :=
  nonConstK3Finset.map ⟨embedK3 b, embedK3_injective b⟩

private lemma disconnSector_nonempty (b : Bool) : (disconnSector b).Nonempty :=
  Finset.card_pos.mp (by simp [disconnSector, nonConstK3Finset_card])

private lemma antiVoterStep_toReal_eq_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    (hV : (Finset.univ : Finset V).Nonempty)
    (hReg : G.IsRegularOfDegree r) (hr : 0 < r) (x y : V → Bool) :
    (antiVoterStep G x y).toReal =
      ((Fintype.card V : ℝ) * (r : ℝ))⁻¹ *
        (((Finset.univ ×ˢ Finset.univ).filter fun p : V × V ↦
          G.Adj p.1 p.2 ∧ Function.update x p.1 (!x p.2) = y).card : ℝ) := by
  have h := sum_antiVoterStep_toReal_mul G hV hReg hr x (fun z ↦ if z = y then (1 : ℝ) else 0)
  have hlhs : (∑ z : V → Bool, (antiVoterStep G x z).toReal * (if z = y then (1 : ℝ) else 0)) =
      (antiVoterStep G x y).toReal := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hzy; simp [hzy]
    · intro hm; exact (hm (Finset.mem_univ y)).elim
  rw [hlhs] at h; rw [h]; congr 1
  rw [Finset.natCast_card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  trans ∑ u ∈ G.neighborFinset v,
      (if G.Adj v u ∧ Function.update x v (!x u) = y then (1 : ℝ) else 0)
  · refine Finset.sum_congr rfl fun u hu ↦ ?_
    simp [(G.mem_neighborFinset v u).mp hu]
  · refine Finset.sum_subset (Finset.subset_univ (G.neighborFinset v)) fun u _ hu ↦ ?_
    have hna : ¬ G.Adj v u := fun ha ↦ hu ((G.mem_neighborFinset v u).mpr ha)
    simp [hna]

private lemma disconn_sector_step_c4 :
    ∀ (b : Bool) (x₀ : Fin 3 → Bool) (v u : Fin 7),
      disconnAntiVoterGraph.Adj v u →
      let w := Function.update (embedK3 b x₀) v (!(embedK3 b x₀ u))
      w 3 = b ∧ w 4 = !b ∧ w 5 = b ∧ w 6 = !b := by
  decide

private lemma disconn_preimage_count_embed :
    ∀ (b : Bool) (y₀ : Fin 3 → Bool),
      (∑ x₀ ∈ nonConstK3Finset,
        ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin 7 × Fin 7 ↦
          disconnAntiVoterGraph.Adj p.1 p.2 ∧
          Function.update (embedK3 b x₀) p.1 (!(embedK3 b x₀ p.2)) = embedK3 b y₀).card) =
      if y₀ ∈ nonConstK3Finset then 14 else 0 := by
  decide

private lemma disconnSector_preimage_sum (b : Bool) (y : Fin 7 → Bool) :
    (∑ x ∈ disconnSector b,
      ((Finset.univ ×ˢ Finset.univ).filter fun p : Fin 7 × Fin 7 ↦
        disconnAntiVoterGraph.Adj p.1 p.2 ∧
        Function.update x p.1 (!x p.2) = y).card) =
    if y ∈ disconnSector b then 14 else 0 := by
  rw [disconnSector, Finset.sum_map, Function.Embedding.coeFn_mk]
  by_cases hc4 : y 3 = b ∧ y 4 = !b ∧ y 5 = b ∧ y 6 = !b
  · let y₀ : Fin 3 → Bool := fun a ↦ y ⟨a.1, by omega⟩
    have hy_eq : y = embedK3 b y₀ := by
      ext i; fin_cases i <;> simp [embedK3, y₀, hc4.1, hc4.2.1, hc4.2.2.1, hc4.2.2.2]
    have hmem : embedK3 b y₀ ∈ nonConstK3Finset.map ⟨embedK3 b, embedK3_injective b⟩ ↔
        y₀ ∈ nonConstK3Finset :=
      ⟨fun h ↦ by obtain ⟨z, hz, heq⟩ := Finset.mem_map.mp h; exact embedK3_injective b heq ▸ hz,
       fun h ↦ Finset.mem_map.mpr ⟨y₀, h, rfl⟩⟩
    rw [hy_eq, disconn_preimage_count_embed b y₀]
    simp only [hmem]
  · have hnot : y ∉ nonConstK3Finset.map ⟨embedK3 b, embedK3_injective b⟩ := by
      intro hm
      obtain ⟨y₀, _, rfl⟩ := Finset.mem_map.mp hm
      exact hc4 ⟨rfl, rfl, rfl, rfl⟩
    simp only [hnot, ↓reduceIte]
    refine Finset.sum_eq_zero fun x₀ _ ↦ ?_
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨v, u⟩ hp ⟨hadj, rfl⟩
    exact hc4 (disconn_sector_step_c4 b x₀ v u hadj)

private lemma disconnSector_stationary (b : Bool) :
    IsAntiVoterStationary disconnAntiVoterGraph
      (PMF.uniformOfFinset (disconnSector b) (disconnSector_nonempty b)).toMeasure := by
  let p := PMF.uniformOfFinset (disconnSector b) (disconnSector_nonempty b)
  rw [isAntiVoterStationary_iff_avStepBind, PMF.toMeasure_toPMF]
  ext y
  have hV : (Finset.univ : Finset (Fin 7)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hcardS : (disconnSector b).card = 6 := by simp [disconnSector, nonConstK3Finset_card]
  have hreal : ((avStepBind disconnAntiVoterGraph p) y).toReal = (p y).toReal := by
    rw [avStepBind, PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun x _ ↦
        ENNReal.mul_ne_top (p.apply_ne_top x) ((antiVoterStep _ x).apply_ne_top y))]
    simp_rw [ENNReal.toReal_mul,
      antiVoterStep_toReal_eq_count disconnAntiVoterGraph hV disconn_regular (by omega),
      Fintype.card_fin]
    have hsum_restrict :
        (∑ x : Fin 7 → Bool,
          (p x).toReal * ((((7 : ℕ) : ℝ) * ((2 : ℕ) : ℝ))⁻¹ *
            (((Finset.univ ×ˢ Finset.univ).filter fun q : Fin 7 × Fin 7 ↦
              disconnAntiVoterGraph.Adj q.1 q.2 ∧
              Function.update x q.1 (!x q.2) = y).card : ℝ))) =
        ∑ x ∈ disconnSector b,
          (6 : ℝ)⁻¹ * ((((7 : ℕ) : ℝ) * ((2 : ℕ) : ℝ))⁻¹ *
            (((Finset.univ ×ˢ Finset.univ).filter fun q : Fin 7 × Fin 7 ↦
              disconnAntiVoterGraph.Adj q.1 q.2 ∧
              Function.update x q.1 (!x q.2) = y).card : ℝ)) := by
      rw [← Finset.sum_subset (Finset.subset_univ (disconnSector b))]
      · refine Finset.sum_congr rfl fun x hx ↦ ?_
        rw [PMF.uniformOfFinset_apply_of_mem _ hx, hcardS, ENNReal.toReal_inv,
          ENNReal.toReal_natCast]; norm_num
      · intro x _ hx
        rw [PMF.uniformOfFinset_apply_of_notMem _ hx, ENNReal.toReal_zero, zero_mul]
    rw [hsum_restrict]
    simp_rw [← mul_assoc]
    rw [← Finset.mul_sum, ← Nat.cast_sum, disconnSector_preimage_sum b y]
    by_cases hy : y ∈ disconnSector b
    · simp only [hy, ↓reduceIte]
      rw [PMF.uniformOfFinset_apply_of_mem _ hy, hcardS, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      norm_num
    · simp only [hy, ↓reduceIte]
      rw [show p y = 0 from PMF.uniformOfFinset_apply_of_notMem _ hy, ENNReal.toReal_zero]
      norm_num
  exact (ENNReal.toReal_eq_toReal_iff'
    ((avStepBind disconnAntiVoterGraph p).apply_ne_top y) (p.apply_ne_top y)).mp hreal

/-- **Disconnected `2`-regular counterexample (`ISSUE-3.8`)**: on `Fin 7`, the disjoint union
$G = K_3 \sqcup C_4$ (`disconnAntiVoterGraph`) is `2`-regular, not bipartite, and not isomorphic
to `cycleGraph 7`, yet it admits two distinct stationary probability distributions (refuting the
printed uniqueness claim at `SteinIntro.tex:1110-1111` when `G.Connected` is omitted) and has
pairs of non-constant configurations with zero `t`-step transition probability for all `t : ℕ`. -/
theorem antiVoter_disconnected_counterexample :
    ∃ (G : SimpleGraph (Fin 7)) (_ : DecidableRel G.Adj)
      (ν₁ ν₂ : Measure (Fin 7 → Bool)),
      G.IsRegularOfDegree 2 ∧
      ¬ G.IsBipartite ∧
      IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card (Fin 7))) ∧
      IsProbabilityMeasure ν₁ ∧ IsProbabilityMeasure ν₂ ∧
      IsAntiVoterStationary G ν₁ ∧ IsAntiVoterStationary G ν₂ ∧
      ν₁ ≠ ν₂ ∧
      ∃ x y : Fin 7 → Bool,
        ((∃ a, x a = true) ∧ (∃ b, x b = false)) ∧
        ((∃ a, y a = true) ∧ (∃ b, y b = false)) ∧
        ∀ t : ℕ,
          ((fun p : PMF (Fin 7 → Bool) ↦ p.bind (antiVoterStep G))^[t] (PMF.pure x)) y = 0 := by
  let p₁ := PMF.uniformOfFinset (disconnSector true) (disconnSector_nonempty true)
  let p₂ := PMF.uniformOfFinset (disconnSector false) (disconnSector_nonempty false)
  let x₀ : Fin 3 → Bool := ![true, false, false]
  have hx₀ : x₀ ∈ nonConstK3Finset := by decide
  let x : Fin 7 → Bool := embedK3 true x₀
  let y : Fin 7 → Bool := embedK3 false x₀
  have hx_mem : x ∈ disconnSector true := Finset.mem_map.mpr ⟨x₀, hx₀, rfl⟩
  have hx_not2 : x ∉ disconnSector false := by
    intro hm
    obtain ⟨z₀, _, hz⟩ := Finset.mem_map.mp hm
    have h3 := congrFun hz 3
    simp [x, embedK3] at h3
  have hne_meas : p₁.toMeasure ≠ p₂.toMeasure := by
    intro heq
    have h1 := p₁.toMeasure_apply_singleton x (measurableSet_singleton x)
    have h2 := p₂.toMeasure_apply_singleton x (measurableSet_singleton x)
    rw [heq, h2, PMF.uniformOfFinset_apply_of_mem _ hx_mem,
      PMF.uniformOfFinset_apply_of_notMem _ hx_not2] at h1
    have hcard : (disconnSector true).card = 6 := by simp [disconnSector, nonConstK3Finset_card]
    rw [hcard] at h1
    exact (ENNReal.inv_ne_zero.mpr (by norm_num)) h1.symm
  refine ⟨disconnAntiVoterGraph, inferInstance, p₁.toMeasure, p₂.toMeasure,
    disconn_regular, disconn_not_bipartite, disconn_not_cycle,
    inferInstance, inferInstance,
    disconnSector_stationary true, disconnSector_stationary false,
    hne_meas, x, y,
    ⟨⟨0, by simp [x, embedK3, x₀]⟩, ⟨1, by simp [x, embedK3, x₀]⟩⟩,
    ⟨⟨0, by simp [y, embedK3, x₀]⟩, ⟨1, by simp [y, embedK3, x₀]⟩⟩, ?_⟩
  have hinv : ∀ (z w : Fin 7 → Bool),
      z 3 = true → z 4 = false → z 5 = true → z 6 = false →
      antiVoterStep disconnAntiVoterGraph z w ≠ 0 →
      w 3 = true ∧ w 4 = false ∧ w 5 = true ∧ w 6 = false := by
    intro z w hz3 hz4 hz5 hz6 hstep
    have hV : (Finset.univ : Finset (Fin 7)).Nonempty := ⟨0, Finset.mem_univ 0⟩
    have hN : ∀ v : Fin 7, (disconnAntiVoterGraph.neighborFinset v).Nonempty := fun v ↦ by
      rw [← Finset.card_pos, disconnAntiVoterGraph.card_neighborFinset_eq_degree,
        disconn_regular v]
      omega
    obtain ⟨v, u, hadj, rfl⟩ :=
      (antiVoterStep_ne_zero_iff disconnAntiVoterGraph hV hN z w).mp hstep
    fin_cases v <;> fin_cases u <;> simp_all [disconnAntiVoterGraph, disconnAdjBool]
  have hall : ∀ (t : ℕ) (w : Fin 7 → Bool),
      ((avStepBind disconnAntiVoterGraph)^[t] (PMF.pure x)) w ≠ 0 →
      w 3 = true ∧ w 4 = false ∧ w 5 = true ∧ w 6 = false := by
    intro t
    induction t with
    | zero =>
      intro w hw
      simp only [Function.iterate_zero, id_eq, PMF.pure_apply] at hw
      have hwx : w = x := by by_contra hne; simp [hne] at hw
      subst hwx; simp [x, embedK3]
    | succ t ih =>
      intro w hw
      rw [Function.iterate_succ_apply', ← PMF.mem_support_iff, avStepBind,
        PMF.mem_support_bind_iff] at hw
      rcases hw with ⟨z, hz, hzw⟩
      rw [PMF.mem_support_iff] at hz hzw
      obtain ⟨h3, h4, h5, h6⟩ := ih z hz
      exact hinv z w h3 h4 h5 h6 hzw
  intro t
  by_contra hne
  have hy3 : y 3 = true := (hall t y hne).1
  simp [y, embedK3] at hy3

end SteinMethod
