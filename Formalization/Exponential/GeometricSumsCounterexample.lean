/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.GeometricSumsCounterexampleAux

/-!
# Counterexample to Printed Theorem 5.7
(`Formalization.Exponential.GeometricSumsCounterexample`)

Machine-checks the counterexample documented in `ISSUE-5.7` (using the exact `D3` conditional
expectation identity from `docs/reviews/stmts-review-05D.md`) refuting the literal printed
statement of Theorem 5.7 (`\label{thm1710}`, eqs. `(5.4)`–`(5.5)`, `SteinIntro.tex:2915-2929`)
when joint independence of $(N, M)$ from $(X_i)_{i \ge 1}$ is omitted (even after restricting
$\mathbb{P}(M = m) = p\,\mathbb{P}(N \ge m)$ to $m \ge 1$ with $M \ge 1$).
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

section Counterexample57

open Counterexample57

private noncomputable def ceNuBern : Measure ℝ :=
  volume.withDensity ((Ioi (0 : ℝ)).indicator fun x ↦
    ENNReal.ofReal ((ceCoinMeas 4001).real
      {b | x < 1 + ceR 4001 ⟨0, by norm_num⟩ b} / 1))

private lemma ceNuBern_props :
    IsProbabilityMeasure ceNuBern ∧
    IsEquilibrium (ceCoinMeas 4001) (fun b ↦ 1 + ceR 4001 ⟨0, by norm_num⟩ b) ceNuBern id := by
  let W0 : ceCoins 4001 → ℝ := fun b ↦ 1 + ceR 4001 ⟨0, by norm_num⟩ b
  have hnn : 0 ≤ᵐ[ceCoinMeas 4001] W0 := Eventually.of_forall fun b ↦ by
    change 0 ≤ 1 + ceRad (b ⟨0, by norm_num⟩)
    have habs := ce_abs_rad (b ⟨0, by norm_num⟩)
    linarith [neg_abs_le (ceRad (b ⟨0, by norm_num⟩))]
  have hint : Integrable W0 (ceCoinMeas 4001) := ce_integrable W0
  have hmean : ∫ b, W0 b ∂ceCoinMeas 4001 = 1 := by
    dsimp only [W0]
    rw [integral_add (integrable_const 1) (ce_integrable _), integral_const, probReal_univ,
      one_smul, ce_integral_R, add_zero]
  have hpos : 0 < ∫ b, W0 b ∂ceCoinMeas 4001 := by rw [hmean]; exact zero_lt_one
  have hac := (sec5_1_equilibrium_ac (Ω' := ℝ) (ceCoinMeas 4001) hnn hint hpos).2
  dsimp only at hac
  rw [hmean] at hac
  exact ⟨hac.1, hac.2.2⟩

private instance : IsProbabilityMeasure ceNuBern := ceNuBern_props.1

private noncomputable def ceNuOne : Measure ℝ :=
  volume.withDensity ((Ioi (0 : ℝ)).indicator fun x ↦
    ENNReal.ofReal ((Measure.dirac ()).real {_u : Unit | x < (1 : ℝ)} / 1))

private lemma ceNuOne_props :
    IsProbabilityMeasure ceNuOne ∧
    IsEquilibrium (Measure.dirac ()) (fun _ : Unit ↦ (1 : ℝ)) ceNuOne id := by
  have hnn : 0 ≤ᵐ[Measure.dirac ()] (fun _ : Unit ↦ (1 : ℝ)) :=
    Eventually.of_forall fun _ ↦ zero_le_one
  have hint : Integrable (fun _ : Unit ↦ (1 : ℝ)) (Measure.dirac ()) := integrable_const 1
  have hmean : ∫ _ : Unit, (1 : ℝ) ∂Measure.dirac () = 1 := by simp
  have hpos : 0 < ∫ _ : Unit, (1 : ℝ) ∂Measure.dirac () := by rw [hmean]; exact zero_lt_one
  have hac := (sec5_1_equilibrium_ac (Ω' := ℝ) (Measure.dirac ()) hnn hint hpos).2
  dsimp only at hac
  rw [hmean] at hac
  exact ⟨hac.1, hac.2.2⟩

private instance : IsProbabilityMeasure ceNuOne := ceNuOne_props.1

private abbrev ceOmega : Type := (ceCoins 4001 × (ℝ × ℝ)) × (ℕ × ℕ)

private noncomputable def ceMeas : Measure ceOmega :=
  ((ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne)).prod (ceMuL.prod ceMuH)

private instance : IsProbabilityMeasure ceMeas := by
  unfold ceMeas; infer_instance

private def ceR_nat (i : ℕ) (b : ceCoins 4001) : ℝ :=
  if hi : 1 ≤ i ∧ i ≤ 4001 then ceR 4001 ⟨i - 1, by omega⟩ b else 0

private def ceX (i : ℕ) (ω : ceOmega) : ℝ :=
  1 + ceR_nat i ω.1.1

private def ceXe (i : ℕ) (ω : ceOmega) : ℝ :=
  if 1 ≤ i ∧ i ≤ 4001 then ω.1.2.1 else ω.1.2.2

private noncomputable def ceN (ω : ceOmega) : ℕ :=
  if ceZ 4001 ω.1.1 < 0 then ω.2.1 else ω.2.2

private lemma ceR_nat_meas (i : ℕ) : Measurable (ceR_nat i) :=
  Measurable.of_discrete

private lemma ceR_nat_abs_le (i : ℕ) (b : ceCoins 4001) : |ceR_nat i b| ≤ 1 := by
  dsimp only [ceR_nat]
  split_ifs with hi
  · rw [ceR, ce_abs_rad]
  · simp

private lemma ceX_meas (i : ℕ) : Measurable (ceX i) :=
  measurable_const.add ((ceR_nat_meas i).comp (measurable_fst.comp measurable_fst))

private lemma ceXe_meas (i : ℕ) : Measurable (ceXe i) := by
  unfold ceXe
  split_ifs
  · exact measurable_fst.comp (measurable_snd.comp measurable_fst)
  · exact measurable_snd.comp (measurable_snd.comp measurable_fst)

private lemma ceN_meas : Measurable ceN := by
  have hcond : MeasurableSet {ω : ceOmega | ceZ 4001 ω.1.1 < 0} :=
    (measurable_fst.comp measurable_fst)
      (MeasurableSet.of_discrete (s := {b : ceCoins 4001 | ceZ 4001 b < 0}))
  exact Measurable.ite hcond (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd)

private lemma ce_map_coins : ceMeas.map (fun ω : ceOmega ↦ ω.1.1) = ceCoinMeas 4001 :=
  ((measurePreserving_fst (μ := ceCoinMeas 4001) (ν := ceNuBern.prod ceNuOne)).comp
    (measurePreserving_fst
      (μ := (ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne))
      (ν := ceMuL.prod ceMuH))).map_eq

private lemma ce_map_eq1 : ceMeas.map (fun ω : ceOmega ↦ ω.1.2.1) = ceNuBern :=
  ((measurePreserving_fst (μ := ceNuBern) (ν := ceNuOne)).comp
    ((measurePreserving_snd (μ := ceCoinMeas 4001) (ν := ceNuBern.prod ceNuOne)).comp
      (measurePreserving_fst
        (μ := (ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne))
        (ν := ceMuL.prod ceMuH)))).map_eq

private lemma ce_map_eq2 : ceMeas.map (fun ω : ceOmega ↦ ω.1.2.2) = ceNuOne :=
  ((measurePreserving_snd (μ := ceNuBern) (ν := ceNuOne)).comp
    ((measurePreserving_snd (μ := ceCoinMeas 4001) (ν := ceNuBern.prod ceNuOne)).comp
      (measurePreserving_fst
        (μ := (ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne))
        (ν := ceMuL.prod ceMuH)))).map_eq

private lemma ce_map_LH : ceMeas.map (fun ω : ceOmega ↦ ω.2) = ceMuL.prod ceMuH :=
  (measurePreserving_snd
    (μ := (ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne))
    (ν := ceMuL.prod ceMuH)).map_eq

private lemma ce_map_L : ceMeas.map (fun ω : ceOmega ↦ ω.2.1) = ceMuL :=
  ((measurePreserving_fst (μ := ceMuL) (ν := ceMuH)).comp
    (measurePreserving_snd
      (μ := (ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne))
      (ν := ceMuL.prod ceMuH))).map_eq

private lemma ceX_props (i : ℕ) (hi : 1 ≤ i) :
    (∀ ω, 0 ≤ ceX i ω) ∧ MemLp (ceX i) 2 ceMeas ∧
      (∫ ω, ceX i ω ∂ceMeas = 1) ∧ (∫ ω, ceX i ω ^ 2 ∂ceMeas ≤ 2) ∧
      IsEquilibrium ceMeas (ceX i) ceMeas (ceXe i) := by
  by_cases hle : i ≤ 4001
  · have hcond : 1 ≤ i ∧ i ≤ 4001 := ⟨hi, hle⟩
    let ri : Fin 4001 := ⟨i - 1, by omega⟩
    let r0 : Fin 4001 := ⟨0, by norm_num⟩
    have hX_eq : ceX i = fun ω ↦ 1 + ceR 4001 ri ω.1.1 := by
      ext ω; simp [ceX, ceR_nat, hcond, ri]
    have hXe_eq : ceXe i = fun ω ↦ ω.1.2.1 := by ext ω; simp [ceXe, hcond]
    have hnn : ∀ ω, 0 ≤ ceX i ω := fun ω ↦ by
      rw [hX_eq]; dsimp only [ceR]
      have habs := ce_abs_rad (ω.1.1 ri)
      linarith [neg_abs_le (ceRad (ω.1.1 ri))]
    have hbdd : ∀ ω, |ceX i ω| ≤ 2 := fun ω ↦ by
      rw [abs_of_nonneg (hnn ω), hX_eq]; dsimp only [ceR]
      have habs := ce_abs_rad (ω.1.1 ri)
      linarith [le_abs_self (ceRad (ω.1.1 ri))]
    have hL2 : MemLp (ceX i) 2 ceMeas :=
      MemLp.of_bound (ceX_meas i).aestronglyMeasurable 2
        (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hbdd ω)
    have hid_coins : IdentDistrib (fun ω : ceOmega ↦ ω.1.1) id ceMeas (ceCoinMeas 4001) :=
      ⟨(measurable_fst.comp measurable_fst).aemeasurable, aemeasurable_id,
        by rw [ce_map_coins, Measure.map_id]⟩
    have hR_int : Integrable (fun ω : ceOmega ↦ ceR 4001 ri ω.1.1) ceMeas :=
      Integrable.of_bound
        ((Measurable.of_discrete : Measurable (ceR 4001 ri)).comp
          (measurable_fst.comp measurable_fst)).aestronglyMeasurable 1
        (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs, ceR, ce_abs_rad])
    have hR_mean : ∫ ω, ceR 4001 ri ω.1.1 ∂ceMeas = 0 := by
      have hid_R := (hid_coins.comp (Measurable.of_discrete : Measurable (ceR 4001 ri))).integral_eq
      simp only [Function.comp_apply, id_eq] at hid_R
      rw [hid_R]
      exact ce_integral_R 4001 ri
    have hmean : ∫ ω, ceX i ω ∂ceMeas = 1 := by
      rw [hX_eq, integral_add (integrable_const 1) hR_int, integral_const, probReal_univ,
        one_smul, hR_mean, add_zero]
    have hsq : ∫ ω, ceX i ω ^ 2 ∂ceMeas ≤ 2 := by
      have hsq_pt : (fun ω ↦ ceX i ω ^ 2) = fun ω ↦ 2 + 2 * ceR 4001 ri ω.1.1 := by
        ext ω; rw [hX_eq]
        have hr2 : ceR 4001 ri ω.1.1 ^ 2 = 1 := ce_sq_rad (ω.1.1 ri)
        linear_combination hr2
      rw [hsq_pt, integral_add (integrable_const 2) (hR_int.const_mul 2), integral_const,
        probReal_univ, one_smul, integral_const_mul, hR_mean, mul_zero, add_zero]
    have hEq : IsEquilibrium ceMeas (ceX i) ceMeas (ceXe i) := by
      have hswap_map := ce_map_invol (m := 4001)
        (τ := fun b j ↦ b (Equiv.swap r0 ri j)) (fun b ↦ by ext j; simp)
      have hid_X : IdentDistrib (fun b ↦ 1 + ceR 4001 r0 b) (ceX i)
          (ceCoinMeas 4001) ceMeas := by
        refine ⟨Measurable.of_discrete.aemeasurable, (ceX_meas i).aemeasurable, ?_⟩
        rw [hX_eq]
        have h1 : ceMeas.map (fun ω : ceOmega ↦ 1 + ceR 4001 ri ω.1.1) =
            (ceCoinMeas 4001).map (fun b ↦ 1 + ceR 4001 ri b) := by
          have hf_coins : Measurable (fun ω : ceOmega ↦ ω.1.1) :=
            measurable_fst.comp measurable_fst
          rw [← ce_map_coins,
            Measure.map_map (Measurable.of_discrete : Measurable fun b ↦ 1 + ceR 4001 ri b)
              hf_coins]
          rfl
        rw [h1, ← hswap_map,
          Measure.map_map (Measurable.of_discrete : Measurable fun b ↦ 1 + ceR 4001 ri b)
            Measurable.of_discrete]
        congr 1; ext b; simp [ceR]
      have hid_Xe : IdentDistrib id (ceXe i) ceNuBern ceMeas :=
        ⟨aemeasurable_id, (ceXe_meas i).aemeasurable, by rw [Measure.map_id, hXe_eq, ce_map_eq1]⟩
      exact ceNuBern_props.2.congr_identDistrib hid_X hid_Xe
    exact ⟨hnn, hL2, hmean, hsq, hEq⟩
  · have hcond : ¬ (1 ≤ i ∧ i ≤ 4001) := fun h ↦ hle h.2
    have hX_eq : ceX i = fun _ ↦ 1 := by ext ω; simp [ceX, ceR_nat, hcond]
    have hXe_eq : ceXe i = fun ω ↦ ω.1.2.2 := by ext ω; simp [ceXe, hcond]
    refine ⟨fun ω ↦ by rw [hX_eq]; exact zero_le_one,
      by rw [hX_eq]; exact memLp_const 1,
      by rw [hX_eq, integral_const, probReal_univ, one_smul],
      by rw [hX_eq]; simp,
      ?_⟩
    have hid_X : IdentDistrib (fun _ : Unit ↦ (1 : ℝ)) (ceX i) (Measure.dirac ()) ceMeas := by
      refine ⟨measurable_const.aemeasurable, (ceX_meas i).aemeasurable, ?_⟩
      rw [hX_eq, Measure.map_const, Measure.map_const, measure_univ, measure_univ]
    have hid_Xe : IdentDistrib id (ceXe i) ceNuOne ceMeas :=
      ⟨aemeasurable_id, (ceXe_meas i).aemeasurable, by rw [Measure.map_id, hXe_eq, ce_map_eq2]⟩
    exact ceNuOne_props.2.congr_identDistrib hid_X hid_Xe

private lemma ceX_iIndepFun : iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ ceX i.1) ceMeas := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S B hB
  by_cases hex : ∃ i ∈ S, 4001 < i.1 ∧ (1 : ℝ) ∉ B i
  · rcases hex with ⟨i₀, hi₀S, hi₀_gt, h1_not⟩
    have hpre_empty : ceX i₀.1 ⁻¹' B i₀ = ∅ := by
      ext ω; simp [ceX, ceR_nat, show ¬ i₀.1 ≤ 4001 by omega, h1_not]
    have hlhs : ceMeas (⋂ i ∈ S, ceX i.1 ⁻¹' B i) = 0 :=
      measure_mono_null (fun ω hω ↦ by
        have := (mem_iInter₂.mp hω) i₀ hi₀S; rwa [hpre_empty] at this) measure_empty
    have hrhs : (∏ i ∈ S, ceMeas (ceX i.1 ⁻¹' B i)) = 0 :=
      Finset.prod_eq_zero hi₀S (by rw [hpre_empty, measure_empty])
    rw [hlhs, hrhs]
  · simp only [not_exists, not_and, not_not] at hex
    let S_le := S.filter (fun i : {i : ℕ // 1 ≤ i} ↦ i.1 ≤ 4001)
    have hinter_eq : (⋂ i ∈ S, ceX i.1 ⁻¹' B i) = ⋂ i ∈ S_le, ceX i.1 ⁻¹' B i := by
      ext ω
      simp only [mem_iInter, S_le, Finset.mem_filter]
      refine ⟨fun h i hi ↦ h i hi.1, fun h i hiS ↦ ?_⟩
      by_cases hle : i.1 ≤ 4001
      · exact h i ⟨hiS, hle⟩
      · have h1 : (1 : ℝ) ∈ B i := hex i hiS (by omega)
        simp [ceX, ceR_nat, hle, h1]
    have hprod_eq : (∏ i ∈ S, ceMeas (ceX i.1 ⁻¹' B i)) =
        ∏ i ∈ S_le, ceMeas (ceX i.1 ⁻¹' B i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not S (fun i ↦ i.1 ≤ 4001)]
      have hones : (∏ i ∈ S.filter (fun i ↦ ¬ i.1 ≤ 4001), ceMeas (ceX i.1 ⁻¹' B i)) = 1 := by
        refine Finset.prod_eq_one fun i hi ↦ ?_
        rw [Finset.mem_filter] at hi
        have h1 : (1 : ℝ) ∈ B i := hex i hi.1 (by omega)
        have hpre_univ : ceX i.1 ⁻¹' B i = univ := by ext ω; simp [ceX, ceR_nat, hi.2, h1]
        rw [hpre_univ, measure_univ]
      rw [hones, mul_one]
    rw [hinter_eq, hprod_eq]
    let toFin : {i : {i : ℕ // 1 ≤ i} // i ∈ S_le} → Fin 4001 := fun x ↦
      ⟨x.1.1 - 1, by
        have := (Finset.mem_filter.mp x.2).2
        omega⟩
    have htoFin_inj : Function.Injective toFin := fun x y h ↦ by
      have hv := congrArg Fin.val h
      dsimp only [toFin] at hv
      have hx1 := x.1.2
      have hy1 := y.1.2
      exact Subtype.ext (Subtype.ext (by omega))
    have hind_sub : iIndepFun
        (fun x : {i : {i : ℕ // 1 ≤ i} // i ∈ S_le} ↦
          fun ω : ceOmega ↦ 1 + ceR 4001 (toFin x) ω.1.1) ceMeas := by
      have hind_coins : iIndepFun
          (fun x : {i : {i : ℕ // 1 ≤ i} // i ∈ S_le} ↦
            fun b : ceCoins 4001 ↦ 1 + ceR 4001 (toFin x) b) (ceCoinMeas 4001) :=
        ((ce_iIndepFun_R 4001).precomp htoFin_inj).comp
          (fun _ y ↦ 1 + y) (fun _ ↦ measurable_const.add measurable_id)
      rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro T C hC
      have hf_coins : Measurable (fun ω : ceOmega ↦ ω.1.1) := measurable_fst.comp measurable_fst
      have hpre_inter : (fun ω : ceOmega ↦ ω.1.1) ⁻¹'
          (⋂ x ∈ T, (fun b : ceCoins 4001 ↦ 1 + ceR 4001 (toFin x) b) ⁻¹' C x) =
          ⋂ x ∈ T, (fun ω : ceOmega ↦ 1 + ceR 4001 (toFin x) ω.1.1) ⁻¹' C x := by
        ext ω; simp
      rw [← hpre_inter, ← Measure.map_apply (μ := ceMeas) hf_coins MeasurableSet.of_discrete,
        ce_map_coins, hind_coins.measure_inter_preimage_eq_mul T hC]
      refine Finset.prod_congr rfl fun x hx ↦ ?_
      rw [← ce_map_coins,
        Measure.map_apply (μ := ceMeas) hf_coins (Measurable.of_discrete (hC x hx))]
      rfl
    have hmatch : ∀ x : {i : {i : ℕ // 1 ≤ i} // i ∈ S_le},
        ceX x.1.1 ⁻¹' B x.1 = (fun ω : ceOmega ↦ 1 + ceR 4001 (toFin x) ω.1.1) ⁻¹' B x.1 :=
      fun x ↦ by
        ext ω
        have hcond : 1 ≤ x.1.1 ∧ x.1.1 ≤ 4001 := ⟨x.1.2, (Finset.mem_filter.mp x.2).2⟩
        simp [ceX, ceR_nat, hcond, toFin]
    have hinter_sub : (⋂ i ∈ S_le, ceX i.1 ⁻¹' B i) =
        ⋂ x ∈ (Finset.univ : Finset {i : {i : ℕ // 1 ≤ i} // i ∈ S_le}),
          (fun ω : ceOmega ↦ 1 + ceR 4001 (toFin x) ω.1.1) ⁻¹' B x.1 := by
      ext ω
      simp only [mem_iInter, Finset.mem_univ, forall_true_left]
      exact ⟨fun h x ↦ by rw [← hmatch x]; exact h x.1 x.2,
        fun h i hi ↦ by have hx := h ⟨i, hi⟩; rwa [← hmatch ⟨i, hi⟩] at hx⟩
    have hprod_sub : (∏ i ∈ S_le, ceMeas (ceX i.1 ⁻¹' B i)) =
        ∏ x ∈ (Finset.univ : Finset {i : {i : ℕ // 1 ≤ i} // i ∈ S_le}),
          ceMeas ((fun ω : ceOmega ↦ 1 + ceR 4001 (toFin x) ω.1.1) ⁻¹' B x.1) := by
      rw [← Finset.prod_coe_sort S_le]
      exact Finset.prod_congr rfl fun x _ ↦ by rw [hmatch x]
    rw [hinter_sub, hprod_sub]
    exact hind_sub.measure_inter_preimage_eq_mul Finset.univ
      fun x _ ↦ hB x.1 (Finset.mem_of_mem_filter x.1 x.2)

private lemma ce_indep_eq_coords :
    IndepFun (fun ω : ceOmega ↦ ω.1.2) (fun ω : ceOmega ↦ (ω.1.1, ω.2)) ceMeas := by
  have hbase : IndepFun (Prod.snd : ceCoins 4001 × (ℝ × ℝ) → ℝ × ℝ)
      (Prod.fst : ceCoins 4001 × (ℝ × ℝ) → ceCoins 4001)
      ((ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne)) :=
    (indepFun_prod (μ := ceCoinMeas 4001) (ν := ceNuBern.prod ceNuOne)
      measurable_id measurable_id).symm
  exact indepFun_fst_comp_prod_snd (ν := ceMuL.prod ceMuH) measurable_snd measurable_fst hbase

private lemma ceXe_indep_all (i : {i : ℕ // 1 ≤ i}) :
    IndepFun (ceXe i.1)
      (fun ω : ceOmega ↦ (ceN ω, ceN ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ ceX j.1.1 ω))
      ceMeas := by
  let φ₁ : ℝ × ℝ → ℝ := fun u ↦ if 1 ≤ i.1 ∧ i.1 ≤ 4001 then u.1 else u.2
  let φ₂ : ceCoins 4001 × (ℕ × ℕ) →
      ℕ × ℕ × ({j : {k : ℕ // 1 ≤ k} // j ≠ i} → ℝ) := fun q ↦
    let n := if ceZ 4001 q.1 < 0 then q.2.1 else q.2.2
    (n, n, fun j ↦ 1 + ceR_nat j.1.1 q.1)
  have hφ₁ : Measurable φ₁ := by
    dsimp only [φ₁]; split_ifs
    · exact measurable_fst
    · exact measurable_snd
  have hφ₂ : Measurable φ₂ := by
    have hn_meas : Measurable (fun q : ceCoins 4001 × (ℕ × ℕ) ↦
        if ceZ 4001 q.1 < 0 then q.2.1 else q.2.2) :=
      Measurable.ite
        (measurable_fst (MeasurableSet.of_discrete (s := {b : ceCoins 4001 | ceZ 4001 b < 0})))
        (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
    exact hn_meas.prodMk (hn_meas.prodMk (measurable_pi_iff.mpr fun j ↦
      measurable_const.add ((ceR_nat_meas j.1.1).comp measurable_fst)))
  exact ce_indep_eq_coords.comp hφ₁ hφ₂

private lemma ce_indep_coins_LH :
    IndepFun (fun ω : ceOmega ↦ ω.1.1) (fun ω : ceOmega ↦ ω.2) ceMeas :=
  indepFun_prod (μ := (ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne))
    (ν := ceMuL.prod ceMuH) measurable_fst measurable_id

private lemma ceN_map_eq : ceMeas.map ceN = shiftedGeomLaw ceP := by
  ext s hs
  rw [Measure.map_apply ceN_meas hs]
  let A_neg : Set (ceCoins 4001) := {b | ceZ 4001 b < 0}
  let A_pos : Set (ceCoins 4001) := {b | ¬ ceZ 4001 b < 0}
  have hf_coins : Measurable (fun ω : ceOmega ↦ ω.1.1) := measurable_fst.comp measurable_fst
  have hf_LH : Measurable (fun ω : ceOmega ↦ ω.2) := measurable_snd
  have hdecomp : ceN ⁻¹' s =
      (((fun ω : ceOmega ↦ ω.1.1) ⁻¹' A_neg) ∩ ((fun ω : ceOmega ↦ ω.2) ⁻¹' (s ×ˢ univ))) ∪
      (((fun ω : ceOmega ↦ ω.1.1) ⁻¹' A_pos) ∩ ((fun ω : ceOmega ↦ ω.2) ⁻¹' (univ ×ˢ s))) := by
    ext ω
    simp only [mem_preimage, mem_union, mem_inter_iff, mem_prod, mem_univ, and_true, true_and,
      A_neg, A_pos, mem_ofPred_eq, ceN]
    by_cases hb : ceZ 4001 ω.1.1 < 0 <;> simp [hb]
  have hdisj : Disjoint
      (((fun ω : ceOmega ↦ ω.1.1) ⁻¹' A_neg) ∩ ((fun ω : ceOmega ↦ ω.2) ⁻¹' (s ×ˢ univ)))
      (((fun ω : ceOmega ↦ ω.1.1) ⁻¹' A_pos) ∩ ((fun ω : ceOmega ↦ ω.2) ⁻¹' (univ ×ˢ s))) :=
    Set.disjoint_left.mpr fun ω h1 h2 ↦ h2.1 h1.1
  have hm2 : MeasurableSet (((fun ω : ceOmega ↦ ω.1.1) ⁻¹' A_pos) ∩
      ((fun ω : ceOmega ↦ ω.2) ⁻¹' (univ ×ˢ s))) :=
    (hf_coins MeasurableSet.of_discrete).inter (hf_LH (MeasurableSet.univ.prod hs))
  rw [hdecomp, measure_union hdisj hm2,
    ce_indep_coins_LH.measure_inter_preimage_eq_mul A_neg (s ×ˢ univ)
      MeasurableSet.of_discrete (hs.prod MeasurableSet.univ),
    ce_indep_coins_LH.measure_inter_preimage_eq_mul A_pos (univ ×ˢ s)
      MeasurableSet.of_discrete (MeasurableSet.univ.prod hs),
    ← Measure.map_apply hf_coins MeasurableSet.of_discrete,
    ← Measure.map_apply hf_coins MeasurableSet.of_discrete,
    ← Measure.map_apply hf_LH (hs.prod MeasurableSet.univ),
    ← Measure.map_apply hf_LH (MeasurableSet.univ.prod hs),
    ce_map_coins, ce_map_LH, Measure.prod_prod, Measure.prod_prod,
    measure_univ, mul_one, measure_univ, one_mul, ceCoinMeas_neg_eq_half.1,
    ceCoinMeas_neg_eq_half.2, ceMuL_add_ceMuH]

private lemma ceLH_support : ∀ᵐ ω : ceOmega ∂ceMeas, (1 ≤ ω.2.1 ∧ ω.2.1 ≤ 4001) ∧ 4001 < ω.2.2 := by
  have hL : ∀ᵐ ω : ceOmega ∂ceMeas, 1 ≤ ω.2.1 ∧ ω.2.1 ≤ 4001 := by
    have h := ceMuL_support
    rw [← ce_map_L] at h
    exact ae_of_ae_map (measurable_fst.comp measurable_snd).aemeasurable h
  have hH : ∀ᵐ ω : ceOmega ∂ceMeas, 4001 < ω.2.2 := by
    have hmapH : ceMeas.map (fun ω : ceOmega ↦ ω.2.2) = ceMuH :=
      ((measurePreserving_snd (μ := ceMuL) (ν := ceMuH)).comp
        (measurePreserving_snd
          (μ := (ceCoinMeas 4001).prod (ceNuBern.prod ceNuOne))
          (ν := ceMuL.prod ceMuH))).map_eq
    have h := ceMuH_support
    rw [← hmapH] at h
    exact ae_of_ae_map (measurable_snd.comp measurable_snd).aemeasurable h
  exact hL.and hH

private lemma ceN_pos_ae : ∀ᵐ ω : ceOmega ∂ceMeas, 1 ≤ ceN ω := by
  filter_upwards [ceLH_support] with ω ⟨⟨h1, _⟩, h3⟩
  dsimp only [ceN]
  split_ifs
  · exact h1
  · omega

/-! ### Exact `D3` Expectation Calculation and Refutation of Printed Theorem 5.7 -/

private noncomputable def ceW (ω : ceOmega) : ℝ :=
  ceP * ∑ i ∈ Finset.Icc 1 (ceN ω), ceX i ω

private lemma ceW_integrable_and_mean_gt :
    Integrable ceW ceMeas ∧ 8 * ceP < (∫ ω, ceW ω ∂ceMeas) - 1 := by
  obtain ⟨hp0, hp1, _⟩ := ceP_props
  let D_sum : ceOmega → ℝ := fun ω ↦ ∑ i ∈ Finset.Icc 1 (ceN ω), ceR_nat i ω.1.1
  have hD_meas : Measurable D_sum :=
    measurable_select_nat
      (fun n ↦ Finset.measurable_sum _ fun i _ ↦
        (ceR_nat_meas i).comp (measurable_fst.comp measurable_fst))
      ceN_meas
  have hsum_min : ∀ (n : ℕ) (b : ceCoins 4001),
      (∑ i ∈ Finset.Icc 1 n, ceR_nat i b) = ∑ i ∈ Finset.Icc 1 (min n 4001), ceR_nat i b :=
    fun n b ↦ (Finset.sum_subset (Finset.Icc_subset_Icc_right (min_le_left n 4001))
      fun i hi hni ↦ by
        have hi_lu := Finset.mem_Icc.mp hi
        have hgt : ¬ i ≤ 4001 := fun hle ↦
          hni (Finset.mem_Icc.mpr ⟨hi_lu.1, le_min hi_lu.2 hle⟩)
        simp [ceR_nat, hgt]).symm
  have hsum_4001 : ∀ b : ceCoins 4001, (∑ i ∈ Finset.Icc 1 4001, ceR_nat i b) = ceZ 4001 b :=
    fun b ↦ by
      rw [sum_Icc_one_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      have hc : 1 ≤ r.1 + 1 ∧ r.1 + 1 ≤ 4001 := ⟨by omega, by omega⟩
      simp [ceR_nat, hc]
  have hD_bdd : ∀ ω, |D_sum ω| ≤ 4001 := fun ω ↦ by
    dsimp only [D_sum]
    rw [hsum_min]
    calc
      |∑ i ∈ Finset.Icc 1 (min (ceN ω) 4001), ceR_nat i ω.1.1|
          ≤ ∑ i ∈ Finset.Icc 1 (min (ceN ω) 4001), |ceR_nat i ω.1.1| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ Finset.Icc 1 (min (ceN ω) 4001), (1 : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ ceR_nat_abs_le i ω.1.1
      _ = ((min (ceN ω) 4001 : ℕ) : ℝ) := by
            rw [sum_Icc_one_eq_sum_range, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              mul_one]
      _ ≤ 4001 := by exact_mod_cast min_le_right (ceN ω) 4001
  have hD_int : Integrable D_sum ceMeas :=
    Integrable.of_bound hD_meas.aestronglyMeasurable 4001
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hD_bdd ω)
  have hNR_int : Integrable (fun ω ↦ (ceN ω : ℝ)) ceMeas := by
    have hm := integrable_cast_shiftedGeomLaw hp0 hp1.le
    rw [← ceN_map_eq] at hm
    exact (integrable_map_measure (by fun_prop) ceN_meas.aemeasurable).mp hm
  have hNR_mean : ∫ ω, (ceN ω : ℝ) ∂ceMeas = 1 / ceP := by
    have hm := integral_cast_shiftedGeomLaw hp0 hp1.le
    rw [← ceN_map_eq, integral_map ceN_meas.aemeasurable (by fun_prop)] at hm
    exact hm
  have hW_split : ceW = fun ω ↦ ceP * (ceN ω : ℝ) + ceP * D_sum ω := by
    ext ω
    dsimp only [ceW, D_sum, ceX]
    rw [Finset.sum_add_distrib, sum_Icc_one_eq_sum_range (fun _ ↦ (1 : ℝ)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, mul_add]
  have hW_int : Integrable ceW ceMeas := by
    rw [hW_split]
    exact (hNR_int.const_mul ceP).add (hD_int.const_mul ceP)
  have hW_mean_sub : (∫ ω, ceW ω ∂ceMeas) - 1 = ceP * ∫ ω, D_sum ω ∂ceMeas := by
    rw [hW_split, integral_add (hNR_int.const_mul ceP) (hD_int.const_mul ceP),
      integral_const_mul, integral_const_mul, hNR_mean, mul_one_div_cancel hp0.ne']
    ring
  -- Express `D_sum` almost everywhere as a finite sum of independent coin × `ceMuL` products
  have hD_ae : D_sum =ᵐ[ceMeas] fun ω ↦
      (∑ r : Fin 4001, (if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0) *
        {b | ceZ 4001 b < 0}.indicator (ceR 4001 r) ω.1.1) +
        {b | ¬ ceZ 4001 b < 0}.indicator (ceZ 4001) ω.1.1 := by
    filter_upwards [ceLH_support] with ω ⟨⟨hl1, hl2⟩, hh⟩
    dsimp only [D_sum, ceN]
    by_cases hb : ceZ 4001 ω.1.1 < 0
    · have hmem : ω.1.1 ∈ {b | ceZ 4001 b < 0} := hb
      have hnot : ω.1.1 ∉ {b | ¬ ceZ 4001 b < 0} := not_not.mpr hb
      simp only [hb, ↓reduceIte, indicator_of_mem hmem, indicator_of_notMem hnot, add_zero]
      rw [sum_Icc_one_eq_sum_range]
      have hsub_r : Finset.range ω.2.1 ⊆ Finset.range 4001 := Finset.range_mono hl2
      have hrhs : (∑ r : Fin 4001, (if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0) * ceR 4001 r ω.1.1) =
          ∑ k ∈ Finset.range 4001,
            (if k + 1 ≤ ω.2.1 then (1 : ℝ) else 0) * ceR_nat (k + 1) ω.1.1 := by
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun r _ ↦ ?_
        have hc : 1 ≤ r.1 + 1 ∧ r.1 + 1 ≤ 4001 := ⟨by omega, by omega⟩
        simp [ceR_nat, hc]
      rw [hrhs, ← Finset.sum_subset hsub_r]
      · refine Finset.sum_congr rfl fun k hk ↦ ?_
        have hk_lt : k < ω.2.1 := Finset.mem_range.mp hk
        have hle : k + 1 ≤ ω.2.1 := hk_lt
        simp [hle]
      · intro k _ hnk
        have hnot_le : ¬ k + 1 ≤ ω.2.1 := fun hle ↦ hnk (Finset.mem_range.mpr hle)
        simp [hnot_le]
    · have hnot : ω.1.1 ∉ {b | ceZ 4001 b < 0} := hb
      have hmem : ω.1.1 ∈ {b | ¬ ceZ 4001 b < 0} := hb
      have hmin : min ω.2.2 4001 = 4001 := min_eq_right (by omega)
      simp only [hb, ↓reduceIte, indicator_of_notMem hnot, indicator_of_mem hmem, mul_zero,
        Finset.sum_const_zero, zero_add]
      rw [hsum_min, hmin, hsum_4001]
  have hterm_prod : ∀ r : Fin 4001,
      ∫ ω, (if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0) *
        {b | ceZ 4001 b < 0}.indicator (ceR 4001 r) ω.1.1 ∂ceMeas =
      (∫ ω, (if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0) ∂ceMeas) *
        (- (1 / (2 * (4001 : ℝ))) * ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001) := fun r ↦ by
    let α : ℕ × ℕ → ℝ := fun q ↦ if r.1 + 1 ≤ q.1 then 1 else 0
    let β : ceCoins 4001 → ℝ := {b | ceZ 4001 b < 0}.indicator (ceR 4001 r)
    have hind := ce_indep_coins_LH.symm.comp (Measurable.of_discrete : Measurable α)
      (Measurable.of_discrete : Measurable β)
    have h1 := hind.integral_fun_mul_eq_mul_integral
      (Measurable.of_discrete.comp measurable_snd).aestronglyMeasurable
      (Measurable.of_discrete.comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable
    have hβ_int : ∫ ω, β ω.1.1 ∂ceMeas =
        - (1 / (2 * (4001 : ℝ))) * ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001 := by
      have hid : IdentDistrib (fun ω : ceOmega ↦ ω.1.1) id ceMeas (ceCoinMeas 4001) :=
        ⟨(measurable_fst.comp measurable_fst).aemeasurable, aemeasurable_id,
          by rw [ce_map_coins, Measure.map_id]⟩
      have hid_β := (hid.comp (Measurable.of_discrete : Measurable β)).integral_eq
      simp only [Function.comp_apply, id_eq] at hid_β
      rw [hid_β]
      exact ce_integral_R_on_neg r
    simpa only [Function.comp_apply, α, β, hβ_int] using h1
  have hsum_ind_L : ∫ ω, (∑ r : Fin 4001, if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0) ∂ceMeas =
      ∫ l, (l : ℝ) ∂ceMuL := by
    have hid_L : IdentDistrib (fun ω : ceOmega ↦ ω.2.1) id ceMeas ceMuL :=
      ⟨(measurable_fst.comp measurable_snd).aemeasurable, aemeasurable_id,
        by rw [ce_map_L, Measure.map_id]⟩
    let gL : ℕ → ℝ := fun l ↦ ∑ r : Fin 4001, if r.1 + 1 ≤ l then (1 : ℝ) else 0
    have hid_gL := (hid_L.comp (Measurable.of_discrete : Measurable gL)).integral_eq
    simp only [Function.comp_apply, id_eq] at hid_gL
    rw [hid_gL]
    refine integral_congr_ae ?_
    filter_upwards [ceMuL_support] with l ⟨_, hl2⟩
    dsimp only [gL]
    rw [Fin.sum_univ_eq_sum_range (fun k ↦ if k + 1 ≤ l then (1 : ℝ) else 0) 4001,
      ← Finset.sum_subset (Finset.range_mono hl2)]
    · have hones : ∀ k ∈ Finset.range l, (if k + 1 ≤ l then (1 : ℝ) else 0) = 1 := fun k hk ↦ by
        have hk_lt : k < l := Finset.mem_range.mp hk
        have hle : k + 1 ≤ l := hk_lt
        simp [hle]
      rw [Finset.sum_congr rfl hones, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    · intro k _ hnk
      have hnot_le : ¬ k + 1 ≤ l := fun hle ↦ hnk (Finset.mem_range.mpr hle)
      simp [hnot_le]
  have hpos_int : ∫ ω, {b | ¬ ceZ 4001 b < 0}.indicator (ceZ 4001) ω.1.1 ∂ceMeas =
      (1 / 2 : ℝ) * ∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001 := by
    let βpos : ceCoins 4001 → ℝ := {b | ¬ ceZ 4001 b < 0}.indicator (ceZ 4001)
    have hid : IdentDistrib (fun ω : ceOmega ↦ ω.1.1) id ceMeas (ceCoinMeas 4001) :=
      ⟨(measurable_fst.comp measurable_fst).aemeasurable, aemeasurable_id,
        by rw [ce_map_coins, Measure.map_id]⟩
    have hid_βpos := (hid.comp (Measurable.of_discrete : Measurable βpos)).integral_eq
    simp only [Function.comp_apply, id_eq] at hid_βpos
    rw [hid_βpos]
    exact ce_integral_Z_indicators.1
  have hint_prod_r : ∀ r : Fin 4001, Integrable (fun ω : ceOmega ↦
      (if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0) *
        {b | ceZ 4001 b < 0}.indicator (ceR 4001 r) ω.1.1) ceMeas := fun r ↦
    Integrable.of_bound
      (((Measurable.of_discrete : Measurable fun n : ℕ ↦ if r.1 + 1 ≤ n then (1 : ℝ) else 0).comp
          (measurable_fst.comp measurable_snd)).mul
        ((Measurable.of_discrete :
            Measurable ({b | ceZ 4001 b < 0}.indicator (ceR 4001 r))).comp
          (measurable_fst.comp measurable_fst))).aestronglyMeasurable 1
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
        have h2 : |{b | ceZ 4001 b < 0}.indicator (ceR 4001 r) ω.1.1| ≤ 1 := by
          by_cases hb : ω.1.1 ∈ {b | ceZ 4001 b < 0}
          · rw [indicator_of_mem hb, ceR, ce_abs_rad]
          · rw [indicator_of_notMem hb, abs_zero]; exact zero_le_one
        exact (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hint_ind_r : ∀ r : Fin 4001,
      Integrable (fun ω : ceOmega ↦ if r.1 + 1 ≤ ω.2.1 then (1 : ℝ) else 0) ceMeas := fun r ↦
    Integrable.of_bound
      (((Measurable.of_discrete : Measurable fun n : ℕ ↦ if r.1 + 1 ≤ n then (1 : ℝ) else 0).comp
        (measurable_fst.comp measurable_snd))).aestronglyMeasurable 1
      (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; split_ifs <;> norm_num)
  have hint_pos : Integrable
      (fun ω : ceOmega ↦ {b | ¬ ceZ 4001 b < 0}.indicator (ceZ 4001) ω.1.1) ceMeas :=
    Integrable.of_bound
      (((Measurable.of_discrete :
          Measurable ({b | ¬ ceZ 4001 b < 0}.indicator (ceZ 4001))).comp
        (measurable_fst.comp measurable_fst))).aestronglyMeasurable 4001
      (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs]
        by_cases hb : ω.1.1 ∈ {b | ¬ ceZ 4001 b < 0}
        · rw [indicator_of_mem hb]
          calc
            |ceZ 4001 ω.1.1| ≤ ∑ r : Fin 4001, |ceR 4001 r ω.1.1| := Finset.abs_sum_le_sum_abs _ _
            _ = 4001 := by simp [ceR, ce_abs_rad]
        · rw [indicator_of_notMem hb, abs_zero]; norm_num)
  have hD_mean : ∫ ω, D_sum ω ∂ceMeas =
      (1 / 2 : ℝ) * (∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001) *
        (1 - (∫ l, (l : ℝ) ∂ceMuL) / 4001) := by
    rw [integral_congr_ae hD_ae, integral_add (integrable_finsetSum _ fun r _ ↦ hint_prod_r r)
      hint_pos, integral_finsetSum _ fun r _ ↦ hint_prod_r r, hpos_int]
    simp_rw [hterm_prod, ← Finset.sum_mul, ← integral_finsetSum _ fun r _ ↦ hint_ind_r r,
      hsum_ind_L]
    ring
  refine ⟨hW_int, ?_⟩
  rw [hW_mean_sub, hD_mean]
  have habs_gt := ce_abs_Z_4001_gt
  have hL_le := ceMuL_mean_le
  have hD_gt_8 : 8 < (1 / 2 : ℝ) * (∫ b, |ceZ 4001 b| ∂ceCoinMeas 4001) *
      (1 - (∫ l, (l : ℝ) ∂ceMuL) / 4001) := by nlinarith only [habs_gt, hL_le]
  nlinarith only [hp0, hD_gt_8]

/-- Negation of the literal printed statement of Theorem 5.7 (`\label{thm1710}`,
eqs. `(5.4)`–`(5.5)`, `SteinIntro.tex:2915-2929`; `ISSUE-5.7`, `docs/reviews/stmts-review-05D.md`
item `D3`): even when $M \ge 1$ almost surely, $\mathbb{P}(M = m) = p\,\mathbb{P}(N \ge m)$ holds
for all $m \ge 1$, and each $X_i^e$ is jointly independent of $(N, M, (X_j)_{j \ne i})$, omitting
joint independence of $(N, M)$ from $(X_i)_{i \ge 1}$ makes the Wasserstein bound
$d_{\mathrm{W}}(W, Z) \le 2p(1 + \mu_2 / 2 + \mathbb{E}|N - M|)$ false. -/
theorem not_Thm5_7_printed :
    ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {p : ℝ} {X Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ} {Z : Ω' → ℝ},
      0 < p → p ≤ 1 →
      (∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) →
      (∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i) →
      (∀ i : ℕ, 1 ≤ i → MemLp (X i) 2 P) →
      (∀ i : ℕ, 1 ≤ i → ∫ ω, X i ω ∂P = 1) →
      iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P →
      AEMeasurable N P → AEMeasurable M P →
      (∀ᵐ ω ∂P, 1 ≤ N ω) →
      Integrable (fun ω ↦ (N ω : ℝ)) P →
      (∫ ω, (N ω : ℝ) ∂P = 1 / p) →
      (∀ᵐ ω ∂P, 1 ≤ M ω) →
      (∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω}) →
      (∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (Xe i)) →
      (∀ i : {i : ℕ // 1 ≤ i},
        IndepFun (Xe i.1)
          (fun ω ↦ (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P) →
      AEMeasurable Z P' →
      P'.map Z = stdExpLaw →
      let W : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
      let μ₂ : ℝ≥0∞ := ⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ ω, X i ω ^ 2 ∂P)
      let err₁ : ℝ≥0∞ :=
        ENNReal.ofReal (2 * p) *
          ((∫⁻ ω, ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| ∂P) +
            ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
      let err₂ : ℝ≥0∞ :=
        ENNReal.ofReal (2 * p) *
          (1 + μ₂ / 2 + ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
      wassersteinDist (P.map W) (P'.map Z) ≤ err₁ ∧ err₁ ≤ err₂) := by
  intro H
  obtain ⟨hp0, hp1, _⟩ := ceP_props
  obtain ⟨hW_int, hW_gt⟩ := ceW_integrable_and_mean_gt
  have hNR_int : Integrable (fun ω ↦ (ceN ω : ℝ)) ceMeas := by
    have hm := integrable_cast_shiftedGeomLaw hp0 hp1.le
    rw [← ceN_map_eq] at hm
    exact (integrable_map_measure (by fun_prop) ceN_meas.aemeasurable).mp hm
  have hNR_mean : ∫ ω, (ceN ω : ℝ) ∂ceMeas = 1 / ceP := by
    have hm := integral_cast_shiftedGeomLaw hp0 hp1.le
    rw [← ceN_map_eq, integral_map ceN_meas.aemeasurable (by fun_prop)] at hm
    exact hm
  have hpmf : ∀ m : ℕ, 1 ≤ m →
      ceMeas.real {ω | ceN ω = m} = ceP * ceMeas.real {ω | m ≤ ceN ω} := fun m hm ↦ by
    have h1 : ceMeas.real {ω | ceN ω = m} = (shiftedGeomLaw ceP).real {m} := by
      rw [← ceN_map_eq, map_measureReal_apply ceN_meas (measurableSet_singleton m)]
      rfl
    have h2 : ceMeas.real {ω | m ≤ ceN ω} = (shiftedGeomLaw ceP).real (Ici m) := by
      rw [← ceN_map_eq, map_measureReal_apply ceN_meas measurableSet_Ici]
      rfl
    rw [h1, h2, shiftedGeomLaw_real_singleton_of_pos hp0 hp1.le hm,
      shiftedGeomLaw_real_Ici hp0 hp1.le hm]
    ring
  have hinst := H (Ω := ceOmega) (Ω' := ℝ) ceMeas stdExpLaw
    (p := ceP) (X := ceX) (Xe := ceXe) (N := ceN) (M := ceN) (Z := id)
    hp0 hp1.le
    (fun i _ ↦ (ceX_meas i).aemeasurable)
    (fun i hi ↦ Eventually.of_forall (ceX_props i hi).1)
    (fun i hi ↦ (ceX_props i hi).2.1)
    (fun i hi ↦ (ceX_props i hi).2.2.1)
    ceX_iIndepFun
    ceN_meas.aemeasurable ceN_meas.aemeasurable
    ceN_pos_ae hNR_int hNR_mean ceN_pos_ae hpmf
    (fun i hi ↦ (ceX_props i hi).2.2.2.2)
    ceXe_indep_all
    aemeasurable_id Measure.map_id
  dsimp only at hinst
  have hdW_le_err₂ : wassersteinDist (ceMeas.map ceW) (stdExpLaw.map id) ≤
      ENNReal.ofReal (4 * ceP) := by
    refine (hinst.1.trans hinst.2).trans ?_
    have hdiff_zero : (∫⁻ ω : ceOmega, ENNReal.ofReal |(ceN ω : ℝ) - (ceN ω : ℝ)| ∂ceMeas) = 0 := by
      simp
    have hμ₂_le : (⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ ω, ceX i ω ^ 2 ∂ceMeas)) ≤ 2 := by
      refine iSup₂_le fun i hi ↦ ?_
      rw [← ENNReal.ofReal_ofNat 2]
      exact ENNReal.ofReal_le_ofReal (ceX_props i hi).2.2.2.1
    rw [hdiff_zero, add_zero]
    calc
      ENNReal.ofReal (2 * ceP) *
          (1 + (⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ ω, ceX i ω ^ 2 ∂ceMeas)) / 2)
          ≤ ENNReal.ofReal (2 * ceP) * (1 + (2 : ℝ≥0∞) / 2) :=
            mul_le_mul_of_nonneg_left
              (add_le_add le_rfl (ENNReal.div_le_div_right hμ₂_le 2)) zero_le
      _ = ENNReal.ofReal (4 * ceP) := by
            have h2div : (2 : ℝ≥0∞) / 2 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
            have h12 : (1 : ℝ≥0∞) + 1 = ENNReal.ofReal 2 := by
              rw [ENNReal.ofReal_ofNat]; norm_num
            rw [h2div, h12, ← ENNReal.ofReal_mul (by linarith only [hp0])]
            congr 1; ring
  -- Lower bound `wassersteinDist` via the `1`-Lipschitz test function `id`
  have hW_meas : Measurable ceW := by
    unfold ceW
    exact measurable_const.mul
      (measurable_select_nat (f := fun n ω ↦ ∑ i ∈ Finset.Icc 1 n, ceX i ω)
        (fun n ↦ Finset.measurable_sum _ fun i _ ↦ ceX_meas i) ceN_meas)
  have hint_id_W : Integrable (id : ℝ → ℝ) (ceMeas.map ceW) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hW_meas.aemeasurable).mpr hW_int
  have hdW_ge : ENNReal.ofReal ((∫ ω, ceW ω ∂ceMeas) - 1) ≤
      wassersteinDist (ceMeas.map ceW) (stdExpLaw.map id) := by
    rw [Measure.map_id, wassersteinDist, ipm]
    refine le_iSup₂_of_le (id : ℝ → ℝ) LipschitzWith.id ?_
    refine le_iSup_of_le ⟨hint_id_W, integrable_id_stdExpLaw⟩ ?_
    rw [integral_map hW_meas.aemeasurable measurable_id.aestronglyMeasurable]
    change ENNReal.ofReal ((∫ ω, ceW ω ∂ceMeas) - 1) ≤
      ENNReal.ofReal |(∫ ω, ceW ω ∂ceMeas) - ∫ x, x ∂stdExpLaw|
    rw [integral_id_stdExpLaw]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hle_real : ENNReal.ofReal (8 * ceP) ≤ ENNReal.ofReal (4 * ceP) :=
    (ENNReal.ofReal_le_ofReal hW_gt.le).trans (hdW_ge.trans hdW_le_err₂)
  have h8_le_4 : 8 * ceP ≤ 4 * ceP :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith only [hp0])).mp hle_real
  linarith only [hp0, h8_le_4]

end Counterexample57

end SteinMethod
