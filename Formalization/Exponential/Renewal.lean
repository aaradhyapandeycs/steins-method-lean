/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.RenewalAux
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Section 5.1: Remark 5.3 — Stationarity of Delayed Renewal Processes
(`Formalization.Exponential.Renewal`)

Formalizes **Remark 5.3** (`\label{rem171}`, `SteinIntro.tex:2875-2880`): if $Y \ge 0$ a.s. is
integrable with $\mu = \mathbb{E}[Y] > 0$, $Y^e$ has the equilibrium distribution of $Y$, and
$Y_0, Y_1, \dots$ are i.i.d. copies of $Y$ independent of $Y^e$, then the delayed renewal sequence
$S_n = Y^e + \sum_{k=0}^{n-1} Y_k$ ($n \ge 0$) is stationary:
1. Its renewal measure on $(a, b]$ equals $(b - a)/\mu$ for all $0 \le a \le b$;
2. For every $t \ge 0$, the post-$t$ renewal epoch process $(S_{N_t + k} - t)_{k \ge 0}$ (with
   $N_t = \inf\{n \in \mathbb{N} \mid t < S_n\}$) has the same joint law on
   $\mathbb{N} \to \mathbb{R}$ as $(S_k)_{k \ge 0}$.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

/-- Post-`t` epoch stationarity for everywhere-measurable non-negative renewal variables. -/
private lemma post_t_stationarity_clean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Y₁ Ye₁ : Ω → ℝ} {Yseq₁ : ℕ → Ω → ℝ}
    (hY₁_meas : Measurable Y₁)
    (hY₁_nn : ∀ ω, 0 ≤ Y₁ ω)
    (hY₁_int : Integrable Y₁ P)
    (hμ₁_pos : 0 < ∫ ω, Y₁ ω ∂P)
    (hYe₁_meas : Measurable Ye₁)
    (hYe₁_nn : ∀ ω, 0 ≤ Ye₁ ω)
    (hYe₁_pos : ∀ᵐ ω ∂P, 0 < Ye₁ ω)
    (hYe₁_ac : Measure.AbsolutelyContinuous (P.map Ye₁) volume)
    (hYe₁_eq : IsEquilibrium P Y₁ P Ye₁)
    (hYseq₁_meas : ∀ k, Measurable (Yseq₁ k))
    (hYseq₁_nn : ∀ k ω, 0 ≤ Yseq₁ k ω)
    (hYseq₁_indep : iIndepFun Yseq₁ P)
    (hYseq₁_id : ∀ k, IdentDistrib (Yseq₁ k) Y₁ P P)
    (hYe₁_indep : IndepFun Ye₁ (fun ω (k : ℕ) ↦ Yseq₁ k ω) P)
    {t : ℝ} (ht : 0 ≤ t) :
    let S₁ : ℕ → Ω → ℝ := fun n ω ↦ Ye₁ ω + ∑ k ∈ Finset.range n, Yseq₁ k ω
    let Nt₁ : Ω → ℕ := fun ω ↦ sInf {n : ℕ | t < S₁ n ω}
    (Measurable fun ω (k : ℕ) ↦ S₁ (Nt₁ ω + k) ω - t) ∧
    (Measurable fun ω (k : ℕ) ↦ S₁ k ω) ∧
    P.map (fun ω (k : ℕ) ↦ S₁ (Nt₁ ω + k) ω - t) = P.map (fun ω (k : ℕ) ↦ S₁ k ω) := by
  dsimp only
  let μ : ℝ := ∫ ω, Y₁ ω ∂P
  let ρ₁ : ℝ → ℝ≥0∞ :=
    (Ioi (0 : ℝ)).indicator (fun x ↦ ENNReal.ofReal (P.real {ω | x < Y₁ ω} / μ))
  have hYe₁_law : P.map Ye₁ = volume.withDensity ρ₁ :=
    ((sec5_1_equilibrium_ac (Ω' := Ω) P (Eventually.of_forall hY₁_nn) hY₁_int hμ₁_pos).1
      P hYe₁_eq).1
  let T : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n, Yseq₁ k ω
  let S₁ : ℕ → Ω → ℝ := fun n ω ↦ Ye₁ ω + T n ω
  have hT_meas : ∀ n, Measurable (T n) := fun n ↦
    Finset.measurable_sum _ fun k _ ↦ hYseq₁_meas k
  have hS₁_meas : ∀ n, Measurable (S₁ n) := fun n ↦ hYe₁_meas.add (hT_meas n)
  have hS₁_mono : ∀ {m₁ m₂ : ℕ}, m₁ ≤ m₂ → ∀ ω, S₁ m₁ ω ≤ S₁ m₂ ω := fun hab ω ↦ by
    dsimp only [S₁, T]
    refine add_le_add_right ?_ (Ye₁ ω)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
      fun k _ _ ↦ hYseq₁_nn k ω
  have hS₁_succ : ∀ m ω, S₁ (m + 1) ω = S₁ m ω + Yseq₁ m ω := fun m ω ↦ by
    dsimp only [S₁, T]
    rw [Finset.sum_range_succ, add_assoc]
  have hRenewal_S₁ : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∑' n : ℕ, P {ω | S₁ n ω ∈ Ioc a b} = ENNReal.ofReal ((b - a) / μ) := fun a b ha hab ↦
    delayed_renewal_measure_clean P hY₁_meas hY₁_nn hY₁_int hμ₁_pos
      hYe₁_meas hYe₁_ac hYe₁_eq hYseq₁_meas hYseq₁_nn hYseq₁_indep hYseq₁_id hYe₁_indep ha hab
  let Nt₁ : Ω → ℕ := fun ω ↦ sInf {n : ℕ | t < S₁ n ω}
  let E : ℕ → Set Ω := fun n ↦ {ω | t < S₁ n ω ∧ ∀ m < n, S₁ m ω ≤ t}
  have hE_meas : ∀ n : ℕ, MeasurableSet (E n) := fun n ↦ by
    have hcap : {ω | ∀ m < n, S₁ m ω ≤ t} =
        ⋂ m ∈ Finset.range n, {ω | S₁ m ω ≤ t} := by
      ext ω; simp [Finset.mem_range]
    refine (measurableSet_lt measurable_const (hS₁_meas n)).inter ?_
    change MeasurableSet {ω | ∀ m < n, S₁ m ω ≤ t}
    rw [hcap]
    exact MeasurableSet.biInter (Finset.countable_toSet _)
      fun m _ ↦ measurableSet_le (hS₁_meas m) measurable_const
  have hE_disj : Pairwise (Disjoint on E) := fun n₁ n₂ hne ↦ by
    refine Set.disjoint_left.mpr fun ω h1 h2 ↦ ?_
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [h1.1, h2.2 n₁ hlt]
    · linarith [h2.1, h1.2 n₂ hgt]
  have hE_Nt₁ : ∀ n : ℕ, ∀ ω ∈ E n, Nt₁ ω = n := fun n ω hω ↦ by
    have hne : ({k : ℕ | t < S₁ k ω}).Nonempty := ⟨n, hω.1⟩
    have hle : Nt₁ ω ≤ n := Nat.sInf_le hω.1
    have hmem : t < S₁ (Nt₁ ω) ω := Nat.sInf_mem hne
    by_contra hneq
    have hlt : Nt₁ ω < n := lt_of_le_of_ne hle hneq
    linarith [hω.2 (Nt₁ ω) hlt]
  have hUnion_eq : (⋃ n : ℕ, E n) = {ω | ∃ n : ℕ, t < S₁ n ω} := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨fun ⟨n, hn⟩ ↦ ⟨n, hn.1⟩, fun hne ↦ ⟨Nt₁ ω, Nat.sInf_mem hne, fun m hm ↦ ?_⟩⟩
    by_contra hlt_m
    have hm_mem : m ∈ {n : ℕ | t < S₁ n ω} := not_le.mp hlt_m
    exact absurd (Nat.sInf_le hm_mem) (not_le_of_gt hm)
  have hE_compl_zero : P ((⋃ n : ℕ, E n)ᶜ) = 0 := by
    rw [← measureReal_eq_zero_iff]
    refine le_antisymm ?_ measureReal_nonneg
    have htail := tendsto_measureReal_sum_le_zero P hY₁_meas hY₁_nn hY₁_int
      hμ₁_pos hYseq₁_meas hYseq₁_nn hYseq₁_indep hYseq₁_id t
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds htail fun n ↦ ?_
    refine measureReal_mono fun ω hω ↦ ?_
    rw [hUnion_eq, mem_compl_iff, mem_ofPred_eq, not_exists] at hω
    simp only [mem_ofPred_eq]
    have hle : S₁ n ω ≤ t := not_lt.mp (hω n)
    dsimp only [S₁, T] at hle
    linarith [hYe₁_nn ω]
  have hNt₁_meas : Measurable Nt₁ := by
    have hsingle : ∀ n : ℕ, MeasurableSet (Nt₁ ⁻¹' {n}) := fun n ↦ by
      rcases n with _ | m
      · have heq0 : Nt₁ ⁻¹' {0} = E 0 ∪ (⋃ k : ℕ, E k)ᶜ := by
          ext ω
          simp only [mem_preimage, mem_singleton_iff, mem_union]
          by_cases hω : ω ∈ ⋃ k : ℕ, E k
          · obtain ⟨k, hk⟩ := mem_iUnion.mp hω
            have hval := hE_Nt₁ k ω hk
            refine ⟨fun h0 ↦ Or.inl (by rw [hval] at h0; exact h0 ▸ hk),
              fun h ↦ h.elim (fun hk0 ↦ hE_Nt₁ 0 ω hk0) (fun hc ↦ (hc hω).elim)⟩
          · refine ⟨fun _ ↦ Or.inr hω, fun h ↦ h.elim (fun hk0 ↦ ?_) (fun _ ↦ ?_)⟩
            · exact (hω (mem_iUnion.mpr ⟨0, hk0⟩)).elim
            · have hω' : ω ∈ (⋃ k : ℕ, E k)ᶜ := hω
              rw [hUnion_eq, mem_compl_iff, mem_ofPred_eq, not_exists] at hω'
              have hempty : {k : ℕ | t < S₁ k ω} = ∅ :=
                Set.eq_empty_iff_forall_notMem.mpr fun k (hk : t < S₁ k ω) ↦
                  not_lt_of_ge (not_lt.mp (hω' k)) hk
              dsimp only [Nt₁]; rw [hempty, Nat.sInf_empty]
        rw [heq0]
        exact (hE_meas 0).union (MeasurableSet.iUnion hE_meas).compl
      · have heqm : Nt₁ ⁻¹' {m + 1} = E (m + 1) := by
          ext ω
          simp only [mem_preimage, mem_singleton_iff]
          refine ⟨fun hval ↦ ?_, fun hm1 ↦ hE_Nt₁ (m + 1) ω hm1⟩
          by_cases hω : ω ∈ ⋃ k : ℕ, E k
          · obtain ⟨k, hk⟩ := mem_iUnion.mp hω
            have hk_eq : k = m + 1 := (hE_Nt₁ k ω hk).symm.trans hval
            exact hk_eq ▸ hk
          · have hω' : ω ∈ (⋃ k : ℕ, E k)ᶜ := hω
            rw [hUnion_eq, mem_compl_iff, mem_ofPred_eq, not_exists] at hω'
            have hempty : {k : ℕ | t < S₁ k ω} = ∅ :=
              Set.eq_empty_iff_forall_notMem.mpr fun k (hk : t < S₁ k ω) ↦
                not_lt_of_ge (not_lt.mp (hω' k)) hk
            dsimp only [Nt₁] at hval; rw [hempty, Nat.sInf_empty] at hval
            omega
        rw [heqm]
        exact hE_meas (m + 1)
    intro s _hs
    have hpre : Nt₁ ⁻¹' s = ⋃ n ∈ s, Nt₁ ⁻¹' {n} := by ext ω; simp
    rw [hpre]
    exact MeasurableSet.biUnion (Set.to_countable s) fun n _ ↦ hsingle n
  let R_t : Ω → ℝ := fun ω ↦ S₁ (Nt₁ ω) ω - t
  let Z_t : Ω → (ℕ → ℝ) := fun ω j ↦ Yseq₁ (Nt₁ ω + j) ω
  let Yvec₁ : Ω → (ℕ → ℝ) := fun ω j ↦ Yseq₁ j ω
  have hRt_meas : Measurable R_t :=
    (measurable_select_nat hS₁_meas hNt₁_meas).sub measurable_const
  have hZt_meas : Measurable Z_t :=
    measurable_pi_iff.mpr fun j ↦
      measurable_select_nat (f := fun n ω ↦ Yseq₁ (n + j) ω)
        (fun n ↦ hYseq₁_meas (n + j)) hNt₁_meas
  have hYvec₁_meas : Measurable Yvec₁ := measurable_pi_iff.mpr hYseq₁_meas
  have hmeasure_sum_E : ∀ (D : Set Ω), MeasurableSet D →
      P D = ∑' n : ℕ, P (E n ∩ D) := fun D hD ↦ by
    have hdiff_zero : P (D ∩ (⋃ n : ℕ, E n)ᶜ) = 0 :=
      measure_mono_null inter_subset_right hE_compl_zero
    have hunion_D : D = (D ∩ ⋃ n : ℕ, E n) ∪ (D ∩ (⋃ n : ℕ, E n)ᶜ) :=
      (inter_union_compl D _).symm
    have hdisj_compl : Disjoint (D ∩ ⋃ n : ℕ, E n) (D ∩ (⋃ n : ℕ, E n)ᶜ) :=
      Disjoint.mono inter_subset_right inter_subset_right disjoint_compl_right
    conv_lhs => rw [hunion_D]
    rw [measure_union hdisj_compl (hD.inter (MeasurableSet.iUnion hE_meas).compl),
      hdiff_zero, add_zero, inter_iUnion,
      measure_iUnion (fun i j hij ↦ (hE_disj hij).mono inter_subset_right inter_subset_right)
        (fun n ↦ hD.inter (hE_meas n))]
    exact tsum_congr fun n ↦ by rw [inter_comm]
  have hProd_char : ∀ (A : Set ℝ) (C : Set (ℕ → ℝ)), MeasurableSet A → MeasurableSet C →
      P (R_t ⁻¹' A ∩ Z_t ⁻¹' C) = P (R_t ⁻¹' A) * (P.map Yvec₁) C := by
    intro A C hA hC
    let μ₁ : Measure (ℕ → ℝ) := (P.restrict (R_t ⁻¹' A)).map Z_t
    let μ₂ : Measure (ℕ → ℝ) := P (R_t ⁻¹' A) • P.map Yvec₁
    have : IsProbabilityMeasure (P.map Yvec₁) :=
      (Measure.isProbabilityMeasure_map_iff hYvec₁_meas.aemeasurable).mpr ‹_›
    have : IsFiniteMeasure μ₁ := inferInstance
    have hμ_eq : μ₁ = μ₂ := by
      refine ext_of_generate_finite
        (squareCylinders fun _ : ℕ ↦ {s : Set ℝ | MeasurableSet s})
        generateFrom_squareCylinders.symm
        (isPiSystem_squareCylinders (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet)
          (fun _ ↦ by simp))
        (fun S hS ↦ ?_) ?_
      · rcases hS with ⟨F, B, hB_pi, rfl⟩
        have hB_meas : ∀ j : ℕ, MeasurableSet (B j) := fun j ↦ hB_pi j (mem_univ j)
        have hcyl_meas : MeasurableSet ((F : Set ℕ).pi B) :=
          MeasurableSet.pi (Finset.countable_toSet F) fun j _ ↦ hB_meas j
        dsimp only [μ₁, μ₂]
        rw [Measure.map_apply hZt_meas hcyl_meas, Measure.restrict_apply (hZt_meas hcyl_meas),
          inter_comm, Measure.smul_apply, smul_eq_mul,
          hmeasure_sum_E _ ((hRt_meas hA).inter (hZt_meas hcyl_meas)),
          hmeasure_sum_E _ (hRt_meas hA), ← ENNReal.tsum_mul_right]
        refine tsum_congr fun n ↦ ?_
        let past : Ω → ℝ × (Fin n → ℝ) := fun ω ↦ (Ye₁ ω, fun r : Fin n ↦ Yseq₁ r.1 ω)
        let fut : Ω → (ℕ → ℝ) := fun ω j ↦ Yseq₁ (n + j) ω
        have hpast_fut := indepFun_past_future hYe₁_meas hYseq₁_meas hYseq₁_indep hYe₁_indep n
        let S_past : Fin (n + 1) → ℝ × (Fin n → ℝ) → ℝ := fun m q ↦
          q.1 + ∑ r : Fin n, if r.1 < m.1 then q.2 r else 0
        have hS_past_meas : ∀ m : Fin (n + 1), Measurable (S_past m) := fun m ↦
          measurable_fst.add
            (Finset.measurable_sum _ fun r _ ↦ by
              by_cases hrm : r.1 < m.1
              · simp only [hrm, ↓reduceIte]
                exact (measurable_pi_apply r).comp measurable_snd
              · simp only [hrm, ↓reduceIte]; exact measurable_const)
        have hS_past_eq : ∀ (m : Fin (n + 1)) (ω : Ω),
            S_past m (past ω) = S₁ m.1 ω := fun m ω ↦ by
          dsimp only [S_past, past, S₁, T]
          congr 1
          rw [Fin.sum_univ_eq_sum_range (fun k ↦ if k < m.1 then Yseq₁ k ω else 0) n]
          have hsub : Finset.range m.1 ⊆ Finset.range n :=
            Finset.range_mono (Nat.lt_succ_iff.mp m.2)
          have hzero : ∀ k ∈ Finset.range n, k ∉ Finset.range m.1 →
              (if k < m.1 then Yseq₁ k ω else 0) = 0 :=
            fun k _ hk ↦ ite_eq_right_iff.mpr fun hlt ↦ (hk (Finset.mem_range.mpr hlt)).elim
          rw [← Finset.sum_subset hsub hzero]
          exact Finset.sum_congr rfl fun k hk ↦
            ite_eq_left_iff.mpr fun hnot ↦ (hnot (Finset.mem_range.mp hk)).elim
        let D_past : Set (ℝ × (Fin n → ℝ)) :=
          {q | t < S_past (Fin.last n) q} ∩
            (⋂ m : Fin n, {q | S_past m.castSucc q ≤ t}) ∩
            ((fun q ↦ S_past (Fin.last n) q - t) ⁻¹' A)
        have hD_past_meas : MeasurableSet D_past := by
          dsimp only [D_past]
          refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
          · exact measurableSet_lt measurable_const (hS_past_meas (Fin.last n))
          · exact MeasurableSet.iInter fun m ↦
              measurableSet_le (hS_past_meas m.castSucc) measurable_const
          · exact ((hS_past_meas (Fin.last n)).sub measurable_const) hA
        have hEn_A_eq : E n ∩ R_t ⁻¹' A = past ⁻¹' D_past := by
          ext ω
          simp only [mem_inter_iff, mem_preimage, D_past, mem_iInter, mem_ofPred_eq]
          have hlast := hS_past_eq (Fin.last n) ω
          simp only [Fin.val_last] at hlast
          constructor
          · rintro ⟨hEn, hAω⟩
            have hNt_n := hE_Nt₁ n ω hEn
            refine ⟨⟨?_, fun m ↦ ?_⟩, ?_⟩
            · rw [hlast]; exact hEn.1
            · rw [hS_past_eq m.castSucc ω]; exact hEn.2 m.1 m.2
            · rw [hlast]; dsimp only [R_t] at hAω; rwa [hNt_n] at hAω
          · rintro ⟨⟨h1, h2⟩, h3⟩
            have hEn : ω ∈ E n := ⟨by rwa [← hlast], fun m hm ↦ by
              have := h2 ⟨m, hm⟩
              simpa only [Fin.val_castSucc, hS_past_eq] using this⟩
            refine ⟨hEn, ?_⟩
            dsimp only [R_t]
            rw [hE_Nt₁ n ω hEn, ← hlast]
            exact h3
        have hEn_AC_eq : E n ∩ (R_t ⁻¹' A ∩ Z_t ⁻¹' ((F : Set ℕ).pi B)) =
            (past ⁻¹' D_past) ∩ (fut ⁻¹' ((F : Set ℕ).pi B)) := by
          rw [← inter_assoc, hEn_A_eq]
          ext ω
          simp only [mem_inter_iff]
          refine and_congr_right fun hω_past ↦ ?_
          have hEn : ω ∈ E n := (hEn_A_eq.symm.subset hω_past).1
          have hNt_n := hE_Nt₁ n ω hEn
          simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, Z_t, fut, hNt_n]
        have hfut_cyl : P (fut ⁻¹' ((F : Set ℕ).pi B)) = (P.map Yvec₁) ((F : Set ℕ).pi B) := by
          rw [Measure.map_apply hYvec₁_meas hcyl_meas]
          have hpre1 : fut ⁻¹' ((F : Set ℕ).pi B) =
              ⋂ j ∈ F, Yseq₁ (n + j) ⁻¹' B j := by ext ω; simp [fut, Set.mem_pi]
          have hpre2 : Yvec₁ ⁻¹' ((F : Set ℕ).pi B) =
              ⋂ j ∈ F, Yseq₁ j ⁻¹' B j := by ext ω; simp [Yvec₁, Set.mem_pi]
          have hinj : Function.Injective (fun j : ℕ ↦ n + j) := add_right_injective n
          have hshift_indep : iIndepFun (fun j : ℕ ↦ Yseq₁ (n + j)) P :=
            hYseq₁_indep.precomp hinj
          rw [hpre1, hpre2, hshift_indep.measure_inter_preimage_eq_mul F (fun j _ ↦ hB_meas j),
            hYseq₁_indep.measure_inter_preimage_eq_mul F (fun j _ ↦ hB_meas j)]
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          have hid1 := (hYseq₁_id (n + j)).map_eq
          have hid2 := (hYseq₁_id j).map_eq
          rw [← Measure.map_apply (hYseq₁_meas (n + j)) (hB_meas j),
            ← Measure.map_apply (hYseq₁_meas j) (hB_meas j), hid1, hid2]
        rw [hEn_AC_eq,
          hpast_fut.measure_inter_preimage_eq_mul D_past ((F : Set ℕ).pi B) hD_past_meas
            hcyl_meas,
          ← hEn_A_eq, hfut_cyl]
      · dsimp only [μ₁, μ₂]
        rw [Measure.map_apply hZt_meas MeasurableSet.univ, preimage_univ,
          Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.smul_apply,
          Measure.map_apply hYvec₁_meas MeasurableSet.univ, preimage_univ, measure_univ,
          smul_eq_mul, mul_one]
    have happ := congrArg (fun m : Measure (ℕ → ℝ) ↦ m C) hμ_eq
    dsimp only [μ₁, μ₂] at happ
    rwa [Measure.map_apply hZt_meas hC, Measure.restrict_apply (hZt_meas hC), inter_comm,
      Measure.smul_apply, smul_eq_mul] at happ
  have hZt_law : P.map Z_t = P.map Yvec₁ := by
    ext C hC
    rw [Measure.map_apply hZt_meas hC]
    have h := hProd_char univ C MeasurableSet.univ hC
    rwa [preimage_univ, univ_inter, measure_univ, one_mul] at h
  have hRt_Zt_indep : IndepFun R_t Z_t P := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro A C hA hC
    rw [hProd_char A C hA hC, ← hZt_law, Measure.map_apply hZt_meas hC]
  have hRt_law : P.map R_t = P.map Ye₁ := by
    have : IsProbabilityMeasure (P.map R_t) :=
      (Measure.isProbabilityMeasure_map_iff hRt_meas.aemeasurable).mpr ‹_›
    have : IsProbabilityMeasure (P.map Ye₁) :=
      (Measure.isProbabilityMeasure_map_iff hYe₁_meas.aemeasurable).mpr ‹_›
    let U_ren : Measure ℝ := Measure.sum (fun m : ℕ ↦ P.map (S₁ m))
    have hU_Iic_zero : U_ren (Iic 0) = 0 := by
      dsimp only [U_ren]
      rw [Measure.sum_apply _ measurableSet_Iic]
      refine (tsum_congr fun m ↦ ?_).trans tsum_zero
      rw [Measure.map_apply (hS₁_meas m) measurableSet_Iic]
      refine measure_mono_null (fun ω (hω : S₁ m ω ≤ 0) ↦ ?_) (ae_iff.mp hYe₁_pos)
      simp only [mem_ofPred_eq, not_lt]
      have h0m := hS₁_mono (Nat.zero_le m) ω
      dsimp only [S₁, T] at h0m
      simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h0m
      linarith
    have hU_Ioc : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
        U_ren (Ioc a b) = ENNReal.ofReal ((b - a) / μ) := fun a b ha hab ↦ by
      dsimp only [U_ren]
      rw [Measure.sum_apply _ measurableSet_Ioc]
      have hcongr : (fun m : ℕ ↦ (P.map (S₁ m)) (Ioc a b)) =
          fun m ↦ P {ω | S₁ m ω ∈ Ioc a b} := by
        ext m; rw [Measure.map_apply (hS₁_meas m) measurableSet_Ioc]; rfl
      rw [hcongr, hRenewal_S₁ a b ha hab]
    have hU_Iic_pos : ∀ r : ℝ, 0 ≤ r → U_ren (Iic r) = ENNReal.ofReal (r / μ) := fun r hr ↦ by
      have hunion : Iic r = Iic 0 ∪ Ioc 0 r := by
        ext x; simp only [mem_Iic, mem_union, mem_Ioc]; constructor
        · intro hxr
          rcases le_or_gt x 0 with hx0 | hx0
          · exact Or.inl hx0
          · exact Or.inr ⟨hx0, hxr⟩
        · rintro (hx0 | ⟨_, hxr⟩) <;> linarith
      have hdisj : Disjoint (Iic (0 : ℝ)) (Ioc 0 r) :=
        Set.disjoint_left.mpr fun x (hx1 : x ≤ 0) hx2 ↦ by linarith [hx2.1]
      rw [hunion, measure_union hdisj measurableSet_Ioc, hU_Iic_zero, zero_add,
        hU_Ioc 0 r le_rfl hr, sub_zero]
    have hU_restrict : U_ren.restrict (Iic t) =
        ENNReal.ofReal (1 / μ) • volume.restrict (Ioc 0 t) := by
      have hfin : IsFiniteMeasure (U_ren.restrict (Iic t)) :=
        ⟨by rw [Measure.restrict_apply_univ, hU_Iic_pos t ht]; exact ENNReal.ofReal_lt_top⟩
      refine Measure.ext_of_Iic _ _ fun x ↦ ?_
      rw [Measure.restrict_apply measurableSet_Iic, Measure.smul_apply,
        Measure.restrict_apply measurableSet_Iic, smul_eq_mul]
      rcases le_or_gt x 0 with hx0 | hx0
      · have hsub : Iic x ∩ Iic t ⊆ Iic 0 := fun y hy ↦ hy.1.trans hx0
        have hempty : Iic x ∩ Ioc 0 t = ∅ := by
          ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
          intro ⟨h1, h2, _⟩; linarith
        rw [measure_mono_null hsub hU_Iic_zero, hempty, measure_empty, mul_zero]
      · set r : ℝ := min x t
        have hr0 : 0 ≤ r := le_min hx0.le ht
        have h1 : Iic x ∩ Iic t = Iic r := by ext y; simp [r]
        have h2 : Iic x ∩ Ioc 0 t = Ioc 0 r := by
          ext y; simp only [mem_inter_iff, mem_Iic, mem_Ioc, r, le_min_iff]
          tauto
        rw [h1, h2, hU_Iic_pos r hr0, Real.volume_Ioc, sub_zero,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    have hIoi_eq : ∀ u : ℝ, (P.map R_t) (Ioi u) = (P.map Ye₁) (Ioi u) := fun u ↦ by
      rcases lt_or_ge u 0 with hu_neg | hu_nn
      · have hRt_one : (P.map R_t) (Ioi u) = 1 := by
          rw [Measure.map_apply hRt_meas measurableSet_Ioi]
          refine le_antisymm prob_le_one ?_
          have hU_one : P (⋃ n : ℕ, E n) = 1 := by
            have h1 := measure_add_measure_compl (μ := P) (s := ⋃ n : ℕ, E n)
              (MeasurableSet.iUnion hE_meas)
            rwa [hE_compl_zero, add_zero, measure_univ] at h1
          rw [← hU_one]
          refine measure_mono fun ω hω ↦ ?_
          obtain ⟨n, hn⟩ := mem_iUnion.mp hω
          simp only [mem_preimage, mem_Ioi, R_t, hE_Nt₁ n ω hn]
          linarith [hn.1]
        have hYe_one : (P.map Ye₁) (Ioi u) = 1 := by
          rw [Measure.map_apply hYe₁_meas measurableSet_Ioi]
          refine le_antisymm prob_le_one ?_
          have hpos_one : P {ω | 0 < Ye₁ ω} = 1 := by
            have h0 : P {ω | 0 < Ye₁ ω}ᶜ = 0 := ae_iff.mp hYe₁_pos
            have h1 := measure_add_measure_compl (μ := P) (s := {ω | 0 < Ye₁ ω})
              (measurableSet_lt measurable_const hYe₁_meas)
            rwa [h0, add_zero, measure_univ] at h1
          rw [← hpos_one]
          exact measure_mono fun ω (hω : 0 < Ye₁ ω) ↦ by
            simp only [mem_preimage, mem_Ioi]; linarith
        rw [hRt_one, hYe_one]
      · rw [Measure.map_apply hRt_meas measurableSet_Ioi,
          hmeasure_sum_E _ (hRt_meas measurableSet_Ioi), tsum_eq_zero_add' ENNReal.summable]
        have h0_eq : P (E 0 ∩ R_t ⁻¹' Ioi u) = (P.map Ye₁) (Ioi (t + u)) := by
          rw [Measure.map_apply hYe₁_meas measurableSet_Ioi]
          congr 1
          ext ω
          simp only [mem_inter_iff, mem_preimage, mem_Ioi]
          constructor
          · rintro ⟨hE0, hR⟩
            have hNt0 := hE_Nt₁ 0 ω hE0
            dsimp only [R_t, S₁, T] at hR
            rw [hNt0, Finset.range_zero, Finset.sum_empty, add_zero] at hR
            linarith
          · intro hYe_gt
            have hE0 : ω ∈ E 0 := by
              refine ⟨?_, fun m hm ↦ (Nat.not_lt_zero m hm).elim⟩
              dsimp only [S₁, T]
              rw [Finset.range_zero, Finset.sum_empty, add_zero]
              linarith
            refine ⟨hE0, ?_⟩
            dsimp only [R_t, S₁, T]
            rw [hE_Nt₁ 0 ω hE0, Finset.range_zero, Finset.sum_empty, add_zero]
            linarith
        have hm_eq : ∀ m : ℕ, P (E (m + 1) ∩ R_t ⁻¹' Ioi u) =
            ∫⁻ s in Iic t, P {ω | t + u - s < Y₁ ω} ∂(P.map (S₁ m)) := fun m ↦ by
          have hset_eq : E (m + 1) ∩ R_t ⁻¹' Ioi u =
              {ω | S₁ m ω ≤ t ∧ t + u < S₁ m ω + Yseq₁ m ω} := by
            ext ω
            simp only [mem_inter_iff, mem_preimage, mem_Ioi, mem_ofPred_eq]
            constructor
            · rintro ⟨hEm1, hR⟩
              have hNtm1 := hE_Nt₁ (m + 1) ω hEm1
              dsimp only [R_t] at hR
              rw [hNtm1, hS₁_succ m ω] at hR
              exact ⟨hEm1.2 m (Nat.lt_succ_self m), by linarith⟩
            · rintro ⟨hle, hgt⟩
              have hEm1 : ω ∈ E (m + 1) := by
                refine ⟨by rw [hS₁_succ m ω]; linarith, fun j hj ↦ ?_⟩
                exact (hS₁_mono (Nat.lt_succ_iff.mp hj) ω).trans hle
              refine ⟨hEm1, ?_⟩
              dsimp only [R_t]
              rw [hE_Nt₁ (m + 1) ω hEm1, hS₁_succ m ω]
              linarith
          have hSm_Ym_indep : IndepFun (S₁ m) (Yseq₁ m) P := by
            have hpast_fut := indepFun_past_future hYe₁_meas hYseq₁_meas hYseq₁_indep
              hYe₁_indep m
            let φ₁ : ℝ × (Fin m → ℝ) → ℝ := fun q ↦ q.1 + ∑ r : Fin m, q.2 r
            let φ₂ : (ℕ → ℝ) → ℝ := fun z ↦ z 0
            have hφ₁ : Measurable φ₁ :=
              measurable_fst.add
                (Finset.measurable_sum _ fun r _ ↦ (measurable_pi_apply r).comp measurable_snd)
            have hφ₂ : Measurable φ₂ := measurable_pi_apply 0
            have heq1 : S₁ m = φ₁ ∘ fun ω ↦ (Ye₁ ω, fun r : Fin m ↦ Yseq₁ r.1 ω) := by
              ext ω; dsimp only [S₁, T, φ₁, Function.comp_apply]
              rw [← Fin.sum_univ_eq_sum_range]
            have heq2 : Yseq₁ m = φ₂ ∘ fun ω (j : ℕ) ↦ Yseq₁ (m + j) ω := by
              ext ω; simp [φ₂]
            rw [heq1, heq2]
            exact hpast_fut.comp hφ₁ hφ₂
          have : IsProbabilityMeasure (P.map (S₁ m)) :=
            (Measure.isProbabilityMeasure_map_iff (hS₁_meas m).aemeasurable).mpr ‹_›
          have : IsProbabilityMeasure (P.map (Yseq₁ m)) :=
            (Measure.isProbabilityMeasure_map_iff (hYseq₁_meas m).aemeasurable).mpr ‹_›
          let U_prod : Set (ℝ × ℝ) := {q | q.1 ≤ t ∧ t + u < q.1 + q.2}
          have hU_meas : MeasurableSet U_prod :=
            (measurableSet_le measurable_fst measurable_const).inter
              (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))
          have hpre_prod : {ω | S₁ m ω ≤ t ∧ t + u < S₁ m ω + Yseq₁ m ω} =
              (fun ω ↦ (S₁ m ω, Yseq₁ m ω)) ⁻¹' U_prod := rfl
          rw [hset_eq, hpre_prod,
            ← Measure.map_apply ((hS₁_meas m).prodMk (hYseq₁_meas m)) hU_meas,
            hSm_Ym_indep.map_prod_eq_prod_map_map (hS₁_meas m).aemeasurable
              (hYseq₁_meas m).aemeasurable,
            Measure.prod_apply hU_meas, ← lintegral_indicator measurableSet_Iic]
          refine lintegral_congr fun s ↦ ?_
          by_cases hs : s ∈ Iic t
          · rw [indicator_of_mem hs]
            have hslice_eq : Prod.mk s ⁻¹' U_prod = Ioi (t + u - s) := by
              ext y; simp only [mem_preimage, mem_Ioi, U_prod, mem_ofPred_eq]
              exact ⟨fun h ↦ by linarith [h.2], fun h ↦ ⟨hs, by linarith⟩⟩
            rw [hslice_eq, (hYseq₁_id m).map_eq,
              Measure.map_apply hY₁_meas measurableSet_Ioi]
            rfl
          · rw [indicator_of_notMem hs]
            have hslice_empty : Prod.mk s ⁻¹' U_prod = ∅ := by
              ext y; simp only [mem_preimage, U_prod, mem_ofPred_eq, mem_empty_iff_false,
                iff_false]
              exact fun h ↦ hs h.1
            rw [hslice_empty, measure_empty]
        simp_rw [hm_eq]
        have htail_enn_meas : Measurable fun s : ℝ ↦ P {ω | t + u - s < Y₁ ω} := by
          have hmono : Monotone fun s : ℝ ↦ P {ω | t + u - s < Y₁ ω} := fun s₁ s₂ hs ↦
            measure_mono fun ω (hω : t + u - s₁ < Y₁ ω) ↦ by
              simp only [mem_ofPred_eq]; linarith
          exact hmono.measurable
        have hsum_U :
            (∑' m : ℕ, ∫⁻ s in Iic t, P {ω | t + u - s < Y₁ ω} ∂(P.map (S₁ m))) =
              ∫⁻ s in Iic t, P {ω | t + u - s < Y₁ ω} ∂U_ren := by
          have hrestrict_sum : U_ren.restrict (Iic t) =
              Measure.sum (fun m : ℕ ↦ (P.map (S₁ m)).restrict (Iic t)) :=
            Measure.restrict_sum _ measurableSet_Iic
          rw [hrestrict_sum, lintegral_sum_measure]
        rw [hsum_U, hU_restrict, lintegral_smul_measure, smul_eq_mul,
          ← lintegral_const_mul _ htail_enn_meas]
        let F : ℝ → ℝ≥0∞ :=
          (Ico u (t + u)).indicator (fun x ↦ ENNReal.ofReal (P.real {ω | x < Y₁ ω} / μ))
        have hcov1 : ∫⁻ s in Ioc 0 t, ENNReal.ofReal (1 / μ) * P {ω | t + u - s < Y₁ ω} =
            ∫⁻ s, F (t + u - s) := by
          rw [← lintegral_indicator measurableSet_Ioc]
          refine lintegral_congr fun s ↦ ?_
          by_cases hs : s ∈ Ioc 0 t
          · have hx_mem : t + u - s ∈ Ico u (t + u) :=
              ⟨by linarith [hs.2], by linarith [hs.1]⟩
            rw [indicator_of_mem hs]
            dsimp only [F]
            rw [indicator_of_mem hx_mem, ← ofReal_measureReal (measure_ne_top P _),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; ring
          · have hx_not : t + u - s ∉ Ico u (t + u) := fun hx ↦
              hs ⟨by linarith [hx.2], by linarith [hx.1]⟩
            rw [indicator_of_notMem hs]; dsimp only [F]; rw [indicator_of_notMem hx_not]
        have hIco_Ioc : ∫⁻ x, F x = (P.map Ye₁) (Ioc u (t + u)) := by
          rw [hYe₁_law, withDensity_apply _ measurableSet_Ioc]
          dsimp only [F]
          rw [lintegral_indicator measurableSet_Ico]
          have h_ae_set : (Ico u (t + u) : Set ℝ) =ᵐ[volume] Ioc u (t + u) := by
            change ∀ᵐ x ∂volume, (x ∈ Ico u (t + u)) = (x ∈ Ioc u (t + u))
            rw [ae_iff]
            have hsub : {x : ℝ | ¬ ((x ∈ Ico u (t + u)) = (x ∈ Ioc u (t + u)))} ⊆
                ({u} ∪ {t + u} : Set ℝ) := by
              intro x hx
              simp only [mem_ofPred_eq, eq_iff_iff, mem_Ico, mem_Ioc] at hx
              simp only [mem_union, mem_singleton_iff]
              by_contra hne
              rcases not_or.mp hne with ⟨hne1, hne2⟩
              exact hx ⟨fun ⟨h1, h2⟩ ↦ ⟨lt_of_le_of_ne h1 (Ne.symm hne1), h2.le⟩,
                fun ⟨h1, h2⟩ ↦ ⟨h1.le, lt_of_le_of_ne h2 hne2⟩⟩
            exact measure_mono_null hsub (measure_union_null (by simp) (by simp))
          rw [setLIntegral_congr h_ae_set, ← lintegral_indicator measurableSet_Ioc,
            ← lintegral_indicator measurableSet_Ioc]
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : x ∈ Ioc u (t + u)
          · rw [indicator_of_mem hx, indicator_of_mem hx]
            dsimp only [ρ₁]
            have hx_pos : x ∈ Ioi (0 : ℝ) := lt_of_le_of_lt hu_nn hx.1
            rw [indicator_of_mem hx_pos]
          · rw [indicator_of_notMem hx, indicator_of_notMem hx]
        rw [hcov1, lintegral_sub_left_eq_self F (t + u), hIco_Ioc, h0_eq]
        have hunion_Ioi : Ioi (t + u) ∪ Ioc u (t + u) = Ioi u := by
          ext x; simp only [mem_union, mem_Ioi, mem_Ioc]
          constructor
          · rintro (h | ⟨h, _⟩) <;> linarith
          · intro h
            rcases lt_or_ge (t + u) x with hgt | hle
            · exact Or.inl hgt
            · exact Or.inr ⟨h, hle⟩
        have hdisj_Ioi : Disjoint (Ioi (t + u)) (Ioc u (t + u)) :=
          Set.disjoint_left.mpr fun x hx1 hx2 ↦ by linarith [mem_Ioi.mp hx1, hx2.2]
        rw [← measure_union hdisj_Ioi measurableSet_Ioc, hunion_Ioi]
    refine Measure.ext_of_Iic _ _ fun u ↦ ?_
    have h1 : (P.map R_t) (Iic u) + (P.map R_t) (Ioi u) = 1 := by
      rw [← measure_union
        (Set.disjoint_left.mpr fun x (hx1 : x ∈ Iic u) (hx2 : x ∈ Ioi u) ↦
          not_lt_of_ge (mem_Iic.mp hx1) (mem_Ioi.mp hx2))
        measurableSet_Ioi, Iic_union_Ioi, measure_univ]
    have h2 : (P.map Ye₁) (Iic u) + (P.map Ye₁) (Ioi u) = 1 := by
      rw [← measure_union
        (Set.disjoint_left.mpr fun x (hx1 : x ∈ Iic u) (hx2 : x ∈ Ioi u) ↦
          not_lt_of_ge (mem_Iic.mp hx1) (mem_Ioi.mp hx2))
        measurableSet_Ioi, Iic_union_Ioi, measure_univ]
    rw [hIoi_eq u] at h1
    exact (ENNReal.add_left_inj (measure_ne_top (P.map Ye₁) (Ioi u))).mp (h1.trans h2.symm)
  let Φ : ℝ × (ℕ → ℝ) → (ℕ → ℝ) := fun q k ↦ q.1 + ∑ j ∈ Finset.range k, q.2 j
  have hΦ_meas : Measurable Φ :=
    measurable_pi_iff.mpr fun k ↦
      measurable_fst.add
        (Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).comp measurable_snd)
  have hJoint_eq : P.map (fun ω ↦ (R_t ω, Z_t ω)) = P.map (fun ω ↦ (Ye₁ ω, Yvec₁ ω)) := by
    rw [hRt_Zt_indep.map_prod_eq_prod_map_map hRt_meas.aemeasurable hZt_meas.aemeasurable,
      hYe₁_indep.map_prod_eq_prod_map_map hYe₁_meas.aemeasurable hYvec₁_meas.aemeasurable,
      hRt_law, hZt_law]
  let proc₁_shift : Ω → (ℕ → ℝ) := fun ω k ↦ S₁ (Nt₁ ω + k) ω - t
  let proc₁_base : Ω → (ℕ → ℝ) := fun ω k ↦ S₁ k ω
  have hshift_comp : proc₁_shift = Φ ∘ fun ω ↦ (R_t ω, Z_t ω) := by
    ext ω k
    dsimp only [proc₁_shift, Φ, Function.comp_apply, R_t, Z_t, S₁, T]
    rw [Finset.sum_range_add]
    ring
  have hbase_comp : proc₁_base = Φ ∘ fun ω ↦ (Ye₁ ω, Yvec₁ ω) := rfl
  have hmap_proc₁ : P.map proc₁_shift = P.map proc₁_base := by
    rw [hshift_comp, hbase_comp, ← Measure.map_map hΦ_meas (hRt_meas.prodMk hZt_meas),
      ← Measure.map_map hΦ_meas (hYe₁_meas.prodMk hYvec₁_meas), hJoint_eq]
  have hshift_meas : Measurable proc₁_shift :=
    hshift_comp ▸ hΦ_meas.comp (hRt_meas.prodMk hZt_meas)
  have hbase_meas : Measurable proc₁_base :=
    hbase_comp ▸ hΦ_meas.comp (hYe₁_meas.prodMk hYvec₁_meas)
  exact ⟨hshift_meas, hbase_meas, hmap_proc₁⟩

/-- **Remark 5.3** (`\label{rem171}`, `SteinIntro.tex:2875-2880`): for $Y \ge 0$ a.s. integrable
with $\mu = \mathbb{E}[Y] > 0$, if $Y^e$ has the equilibrium distribution of $Y$ and is independent
of an i.i.d. sequence $Y_0, Y_1, \dots$ distributed as $Y$, then the delayed renewal sequence
$S_n = Y^e + \sum_{k=0}^{n-1} Y_k$ ($n \ge 0$) is stationary: (i) its renewal measure on $(a, b]$
equals $(b - a)/\mu$ for all $0 \le a \le b$, and (ii) for every $t \ge 0$, the post-$t$ epoch
process $(S_{N_t + k} - t)_{k \ge 0}$ (with $N_t = \inf\{n \in \mathbb{N} \mid t < S_n\}$) has the
same joint law on $\mathbb{N} \to \mathbb{R}$ as $(S_k)_{k \ge 0}$. -/
theorem rem5_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y Ye : Ω → ℝ} {Yseq : ℕ → Ω → ℝ}
    (hY_nn : 0 ≤ᵐ[P] Y)
    (hY_int : Integrable Y P)
    (hμ_pos : 0 < ∫ ω, Y ω ∂P)
    (hYe_eq : IsEquilibrium P Y P Ye)
    (hYseq_indep : iIndepFun Yseq P)
    (hYseq_id : ∀ k : ℕ, IdentDistrib (Yseq k) Y P P)
    (hYe_indep : IndepFun Ye (fun ω (k : ℕ) ↦ Yseq k ω) P) :
    let μ : ℝ := ∫ ω, Y ω ∂P
    let S : ℕ → Ω → ℝ := fun n ω ↦ Ye ω + ∑ k ∈ Finset.range n, Yseq k ω
    (∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∑' n : ℕ, P {ω | S n ω ∈ Ioc a b} = ENNReal.ofReal ((b - a) / μ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        let Nt : Ω → ℕ := fun ω ↦ sInf {n : ℕ | t < S n ω}
        IdentDistrib
          (fun ω (k : ℕ) ↦ S (Nt ω + k) ω - t)
          (fun ω (k : ℕ) ↦ S k ω) P P) := by
  dsimp only
  let μ : ℝ := ∫ ω, Y ω ∂P
  let Y₁ : Ω → ℝ := fun ω ↦ max (hY_int.aemeasurable.mk Y ω) 0
  have hY₁_meas : Measurable Y₁ := hY_int.aemeasurable.measurable_mk.max measurable_const
  have hY₁_nn : ∀ ω, 0 ≤ Y₁ ω := fun _ ↦ le_max_right _ 0
  have hY_ae : Y =ᵐ[P] Y₁ := by
    filter_upwards [hY_int.aemeasurable.ae_eq_mk, hY_nn] with ω h1 (h2 : 0 ≤ Y ω)
    dsimp only [Y₁]; rw [← h1, max_eq_left h2]
  have hY₁_int : Integrable Y₁ P := hY_int.congr hY_ae
  have hY₁_mean : ∫ ω, Y₁ ω ∂P = μ := (integral_congr_ae hY_ae).symm
  have hac_pair := (sec5_1_equilibrium_ac (Ω' := Ω) P hY_nn hY_int hμ_pos).1 P hYe_eq
  have hYe_pos : ∀ᵐ ω ∂P, 0 < Ye ω := by
    have hmap_Iic : (P.map Ye) (Iic 0) = 0 := by
      rw [hac_pair.1, withDensity_apply _ measurableSet_Iic,
        ← lintegral_indicator measurableSet_Iic]
      refine (lintegral_congr fun x ↦ ?_).trans lintegral_zero
      by_cases hx : x ∈ Iic (0 : ℝ)
      · have hnot : x ∉ Ioi (0 : ℝ) := fun (h : 0 < x) ↦ not_lt_of_ge (mem_Iic.mp hx) h
        rw [indicator_of_mem hx]; exact indicator_of_notMem hnot _
      · exact indicator_of_notMem hx _
    have hae : ∀ᵐ x ∂(P.map Ye), 0 < x := by
      rw [ae_iff]; convert hmap_Iic using 2; ext x; simp
    exact (ae_map_iff hYe_eq.2.2.1 measurableSet_Ioi).mp hae
  let Ye₁ : Ω → ℝ := fun ω ↦ max (hYe_eq.2.2.1.mk Ye ω) 0
  have hYe₁_meas : Measurable Ye₁ := hYe_eq.2.2.1.measurable_mk.max measurable_const
  have hYe₁_nn : ∀ ω, 0 ≤ Ye₁ ω := fun _ ↦ le_max_right _ 0
  have hYe_ae : Ye =ᵐ[P] Ye₁ := by
    filter_upwards [hYe_eq.2.2.1.ae_eq_mk, hYe_pos] with ω h1 (h2 : 0 < Ye ω)
    dsimp only [Ye₁]; rw [← h1, max_eq_left h2.le]
  have hYe₁_pos : ∀ᵐ ω ∂P, 0 < Ye₁ ω :=
    (hYe_pos.and hYe_ae).mono fun ω ⟨h1, h2⟩ ↦ h2 ▸ h1
  have hYe₁_ac : Measure.AbsolutelyContinuous (P.map Ye₁) volume := by
    rw [← Measure.map_congr hYe_ae]; exact hac_pair.2
  have hYe₁_eq : IsEquilibrium P Y₁ P Ye₁ :=
    hYe_eq.congr_identDistrib (IdentDistrib.of_ae_eq hY_int.aemeasurable hY_ae)
      (IdentDistrib.of_ae_eq hYe_eq.2.2.1 hYe_ae)
  let Yseq₁ : ℕ → Ω → ℝ := fun k ω ↦ max ((hYseq_id k).aemeasurable_fst.mk (Yseq k) ω) 0
  have hYseq₁_meas : ∀ k, Measurable (Yseq₁ k) := fun k ↦
    (hYseq_id k).aemeasurable_fst.measurable_mk.max measurable_const
  have hYseq₁_nn : ∀ k ω, 0 ≤ Yseq₁ k ω := fun _ _ ↦ le_max_right _ 0
  have hYseq_ae : ∀ k, Yseq k =ᵐ[P] Yseq₁ k := fun k ↦ by
    have hnn_k : 0 ≤ᵐ[P] Yseq k := by
      have hae0 : ∀ᵐ x ∂(P.map (Yseq k)), 0 ≤ x := by
        rw [(hYseq_id k).map_eq]
        exact (ae_map_iff hY_int.aemeasurable measurableSet_Ici).mpr hY_nn
      exact (ae_map_iff (hYseq_id k).aemeasurable_fst measurableSet_Ici).mp hae0
    filter_upwards [(hYseq_id k).aemeasurable_fst.ae_eq_mk, hnn_k] with ω h1 (h2 : 0 ≤ Yseq k ω)
    dsimp only [Yseq₁]; rw [← h1, max_eq_left h2]
  have hall_seq : ∀ᵐ ω ∂P, ∀ k, Yseq k ω = Yseq₁ k ω := ae_all_iff.mpr hYseq_ae
  have hYseq₁_indep : iIndepFun Yseq₁ P := hYseq_indep.congr hYseq_ae
  have hYseq₁_id : ∀ k, IdentDistrib (Yseq₁ k) Y₁ P P := fun k ↦
    (IdentDistrib.of_ae_eq (hYseq_id k).aemeasurable_fst (hYseq_ae k)).symm.trans
      ((hYseq_id k).trans (IdentDistrib.of_ae_eq hY_int.aemeasurable hY_ae))
  have hYe₁_indep : IndepFun Ye₁ (fun ω (k : ℕ) ↦ Yseq₁ k ω) P :=
    hYe_indep.congr hYe_ae (hall_seq.mono fun ω hω ↦ funext hω)
  let S₁ : ℕ → Ω → ℝ := fun n ω ↦ Ye₁ ω + ∑ k ∈ Finset.range n, Yseq₁ k ω
  have hall_S : ∀ᵐ ω ∂P, ∀ n, Ye ω + ∑ k ∈ Finset.range n, Yseq k ω = S₁ n ω := by
    filter_upwards [hYe_ae, hall_seq] with ω hYeω hseqω n
    dsimp only [S₁]
    rw [hYeω]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ hseqω k
  refine ⟨fun a b ha hab ↦ ?_, fun t ht ↦ ?_⟩
  · have hcongr_n : ∀ n : ℕ,
        P {ω | Ye ω + (∑ k ∈ Finset.range n, Yseq k ω) ∈ Ioc a b} =
          P {ω | S₁ n ω ∈ Ioc a b} := fun n ↦
      measure_congr (hall_S.mono fun ω hω ↦ propext (by simp [hω n]))
    simp_rw [hcongr_n]
    have h := delayed_renewal_measure_clean P hY₁_meas hY₁_nn hY₁_int (hY₁_mean.symm ▸ hμ_pos)
      hYe₁_meas hYe₁_ac hYe₁_eq hYseq₁_meas hYseq₁_nn hYseq₁_indep hYseq₁_id hYe₁_indep ha hab
    rwa [hY₁_mean] at h
  · obtain ⟨hshift_meas, hbase_meas, hmap_proc₁⟩ := post_t_stationarity_clean P hY₁_meas hY₁_nn
      hY₁_int (hY₁_mean.symm ▸ hμ_pos) hYe₁_meas hYe₁_nn hYe₁_pos hYe₁_ac hYe₁_eq hYseq₁_meas
      hYseq₁_nn hYseq₁_indep hYseq₁_id hYe₁_indep ht
    let Nt : Ω → ℕ := fun ω ↦ sInf {n : ℕ | t < Ye ω + ∑ k ∈ Finset.range n, Yseq k ω}
    let Nt₁ : Ω → ℕ := fun ω ↦ sInf {n : ℕ | t < S₁ n ω}
    let proc_shift : Ω → (ℕ → ℝ) := fun ω k ↦
      (Ye ω + ∑ j ∈ Finset.range (Nt ω + k), Yseq j ω) - t
    let proc_base : Ω → (ℕ → ℝ) := fun ω k ↦ Ye ω + ∑ j ∈ Finset.range k, Yseq j ω
    let proc₁_shift : Ω → (ℕ → ℝ) := fun ω k ↦ S₁ (Nt₁ ω + k) ω - t
    let proc₁_base : Ω → (ℕ → ℝ) := fun ω k ↦ S₁ k ω
    have hshift_ae : proc_shift =ᵐ[P] proc₁_shift := by
      filter_upwards [hall_S] with ω hω
      have hNt_eq : Nt ω = Nt₁ ω := by
        dsimp only [Nt, Nt₁]
        congr 1; ext n; simp only [mem_ofPred_eq, hω n]
      ext k
      dsimp only [proc_shift, proc₁_shift]
      rw [hNt_eq, hω (Nt₁ ω + k)]
    have hbase_ae : proc_base =ᵐ[P] proc₁_base :=
      hall_S.mono fun ω hω ↦ funext fun k ↦ hω k
    refine ⟨hshift_meas.aemeasurable.congr hshift_ae.symm,
      hbase_meas.aemeasurable.congr hbase_ae.symm, ?_⟩
    rw [Measure.map_congr hshift_ae, Measure.map_congr hbase_ae, hmap_proc₁]

end SteinMethod
