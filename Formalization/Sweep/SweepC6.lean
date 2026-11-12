/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.Basic
import Formalization.Geometric.UniformAttachment
import Formalization.Metrics.Basic
import Formalization.PoissonDep.HeadRunAsymptotics

/-!
# SWEEP-C Section 6 Library Proofs (`Formalization.Sweep.SweepC6`)

Library theorems for the approved Section 6 entries in `docs/tracks/SWEEP-C.md` (`SC-1`–`SC-7`):

* `sec6_3_not_exponential_proof`: for the in-degree $W_n$ of an independent uniformly chosen vertex
  in `uniformAttachment n`, $\mathbb{E}[W_n] = 1$, $\mathbb{P}(W_n = 0) = \frac{n - 1}{2n}$ for all
  $n \ge 1$, $d_{\mathrm{K}}(\mathcal{L}(W_n), \mathrm{Exp}(1)) \ge \frac{n - 1}{2n} \ge
  \frac{1}{4}$ for all $n \ge 2$, and $d_{\mathrm{K}}(\mathcal{L}(W_n), \mathrm{Exp}(1)) \not\to 0$
  as $n \to \infty$ (`SteinIntro.tex:3211-3212`; `SC-7`).
* `sec6_3_uniformAttachment_convergence_proof`: total variation convergence
  $d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Ge}^0(1/2)) \to 0$ as $n \to \infty$
  (`SteinIntro.tex:3342-3343`; `D-E1`).
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SteinMethod

/-! ### Exact Point-Zero Probability of Uniform Attachment In-Degree (`SC-7`) -/

private lemma prod_avoid_target_eq :
    ∀ {n v : ℕ}, v < n →
      (∏ u ∈ Finset.range n, if u < v then (1 : ℝ) else (u : ℝ) / ((u : ℝ) + 1)) =
        (v : ℝ) / (n : ℝ)
  | 0, _, hv => absurd hv (Nat.not_lt_zero _)
  | m + 1, v, hv => by
    rw [Finset.prod_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hlt | rfl
    · have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hlt)
      have hnot : ¬ (m < v) := by omega
      rw [prod_avoid_target_eq hlt, ite_eq_right hnot, Nat.cast_succ]
      exact div_mul_div_cancel₀ hm_pos.ne'
    · have hpref : (∏ x ∈ Finset.range v,
          if x < v then (1 : ℝ) else (x : ℝ) / ((x : ℝ) + 1)) = 1 := by
        refine Finset.prod_eq_one fun x hx ↦ ?_
        rw [ite_eq_left (Finset.mem_range.mp hx)]
      rw [hpref, one_mul, ite_eq_right (lt_irrefl v), Nat.cast_succ]

private lemma uniformAttachment_real_inDegree_eq_zero {n : ℕ} (v : Fin n) :
    (uniformAttachment n).real {G : Digraph (Fin n) | digraphInDegree G v = 0} =
      (v.val : ℝ) / (n : ℝ) := by
  let μ : ∀ k : Fin n, Measure (Fin (k.val + 1)) := fun k ↦
    (@PMF.uniformOfFintype (Fin (k.val + 1)) inferInstance ⟨⟨0, Nat.succ_pos _⟩⟩).toMeasure
  have hpre : digraphOfTargets ⁻¹' {G : Digraph (Fin n) | digraphInDegree G v = 0} =
      Set.univ.pi (fun u : Fin n ↦ {x : Fin (u.val + 1) | x.val ≠ v.val}) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, digraphInDegree, Set.mem_univ_pi]
    rw [Set.ncard_eq_zero (hs := Set.toFinite _)]
    simp [Set.ext_iff, digraphOfTargets]
  have henn : uniformAttachment n {G : Digraph (Fin n) | digraphInDegree G v = 0} =
      ∏ u : Fin n, μ u {x : Fin (u.val + 1) | x.val ≠ v.val} := by
    change (Measure.pi μ).map digraphOfTargets
      {G : Digraph (Fin n) | digraphInDegree G v = 0} = _
    rw [Measure.map_apply measurable_digraphOfTargets .of_discrete, hpre, Measure.pi_pi]
  have hfactor : ∀ u : Fin n,
      (μ u).real {x : Fin (u.val + 1) | x.val ≠ v.val} =
        if u.val < v.val then (1 : ℝ) else (u.val : ℝ) / ((u.val : ℝ) + 1) := by
    intro u
    have : IsProbabilityMeasure (μ u) := by dsimp [μ]; infer_instance
    by_cases huv : u.val < v.val
    · rw [ite_eq_left huv]
      have huniv : {x : Fin (u.val + 1) | x.val ≠ v.val} = Set.univ := by
        ext x; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; omega
      rw [huniv, probReal_univ]
    · rw [ite_eq_right huv]
      let x₀ : Fin (u.val + 1) := ⟨v.val, by omega⟩
      have hcompl : {x : Fin (u.val + 1) | x.val ≠ v.val} = ({x₀} : Set (Fin (u.val + 1)))ᶜ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff, Fin.ext_iff]
        rfl
      have hsing : (μ u).real {x₀} = 1 / ((u.val : ℝ) + 1) := by
        have : Nonempty (Fin (u.val + 1)) := ⟨⟨0, Nat.succ_pos _⟩⟩
        have henn_sing : μ u {x₀} = 1 / ((u.val : ℝ≥0∞) + 1) := by
          dsimp [μ]
          rw [PMF.toMeasure_uniformOfFintype_apply _ .of_discrete]
          simp [Nat.cast_succ]
        rw [measureReal_def, henn_sing, one_div, ENNReal.toReal_inv,
          ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
          ENNReal.toReal_natCast, ENNReal.toReal_one, one_div]
      rw [hcompl, probReal_compl_eq_one_sub .of_discrete, hsing]
      have hpos : (0 : ℝ) < (u.val : ℝ) + 1 := by positivity
      field_simp [hpos.ne']
      ring
  rw [measureReal_def, henn, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, hfactor]
  rw [Fin.prod_univ_eq_prod_range
    (fun u : ℕ ↦ if u < v.val then (1 : ℝ) else (u : ℝ) / ((u : ℝ) + 1)) n]
  exact prod_avoid_target_eq v.isLt

private lemma sum_range_div_natCast {n : ℕ} (hn : 0 < n) :
    (n : ℝ)⁻¹ * (∑ v ∈ Finset.range n, (v : ℝ) / (n : ℝ)) =
      ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum_nat : (∑ v ∈ Finset.range n, v) * 2 = n * (n - 1) :=
    Finset.sum_range_id_mul_two n
  have hsum_real : (∑ v ∈ Finset.range n, (v : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    have hcast : (∑ v ∈ Finset.range n, (v : ℝ)) * 2 = (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : (((∑ v ∈ Finset.range n, v) * 2 : ℕ) : ℝ) = ((n * (n - 1) : ℕ) : ℝ) :=
        congrArg Nat.cast hsum_nat
      rw [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat, Nat.cast_mul,
        Nat.cast_sub (Nat.succ_le_of_lt hn), Nat.cast_one] at h1
      exact h1
    linarith
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum_real]
  field_simp [hn_ne]

private lemma probReal_uniformAttachment_inDegree_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    P.real {ω | digraphInDegree (G ω) (I ω) = 0} = ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
  let μI : Measure (Fin n) := (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure
  have : IsProbabilityMeasure μI := by dsimp [μI]; infer_instance
  let IG : Ω → Fin n × Digraph (Fin n) := fun ω ↦ (I ω, G ω)
  have hIG : AEMeasurable IG P := hI.prodMk hG
  have hIG_law : P.map IG = μI.prod (uniformAttachment n) := by
    rw [hIndep.map_prod_eq_prod_map_map hI hG, hI_law, hG_law]
  let S : Fin n → Set (Fin n × Digraph (Fin n)) :=
    fun v ↦ ({v} : Set (Fin n)) ×ˢ {H : Digraph (Fin n) | digraphInDegree H v = 0}
  have hS_meas : ∀ v : Fin n, MeasurableSet (S v) :=
    fun v ↦ (MeasurableSet.of_discrete : MeasurableSet ({v} : Set (Fin n))).prod .of_discrete
  let E : Set (Fin n × Digraph (Fin n)) := ⋃ v ∈ (Finset.univ : Finset (Fin n)), S v
  have hE_meas : MeasurableSet E :=
    Finset.measurableSet_biUnion _ fun v _ ↦ hS_meas v
  have hpre : IG ⁻¹' E = {ω | digraphInDegree (G ω) (I ω) = 0} := by
    ext ω
    simp [IG, E, S]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) S := by
    intro u _ v _ huv
    refine Set.disjoint_left.mpr ?_
    rintro ⟨x, _⟩ ⟨hx1, _⟩ ⟨hx2, _⟩
    simp only [Set.mem_singleton_iff] at hx1 hx2
    exact huv (hx1.symm.trans hx2)
  have henn : P {ω | digraphInDegree (G ω) (I ω) = 0} =
      ∑ v : Fin n, μI {v} * uniformAttachment n {H | digraphInDegree H v = 0} := by
    rw [← hpre, ← Measure.map_apply_of_aemeasurable hIG hE_meas, hIG_law,
      measure_biUnion_finset hdisj (fun v _ ↦ hS_meas v)]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    exact Measure.prod_prod {v} {H | digraphInDegree H v = 0}
  have hμI_sing : ∀ v : Fin n, μI.real {v} = (n : ℝ)⁻¹ := by
    intro v
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [measureReal_def]
    dsimp [μI]
    rw [PMF.toMeasure_uniformOfFintype_apply _ .of_discrete]
    simp [ENNReal.toReal_inv]
  rw [measureReal_def, henn, ENNReal.toReal_sum (fun v _ ↦ ENNReal.mul_ne_top
    (measure_ne_top _ _) (measure_ne_top _ _))]
  simp_rw [ENNReal.toReal_mul, ← measureReal_def, hμI_sing,
    uniformAttachment_real_inDegree_eq_zero, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun v : ℕ ↦ (v : ℝ) / (n : ℝ)) n]
  exact sum_range_div_natCast hn

private theorem not_exponential_pointwise
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n}
    (hG : AEMeasurable G P) (hG_law : P.map G = uniformAttachment n)
    (hI : AEMeasurable I P) (hIndep : ProbabilityTheory.IndepFun I G P)
    (hI_law : P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure) :
    let W : Ω → ℕ := fun ω ↦ digraphInDegree (G ω) (I ω)
    ∫ ω, (W ω : ℝ) ∂P = 1 ∧
      P.real {ω | W ω = 0} = ((n : ℝ) - 1) / (2 * (n : ℝ)) ∧
      ENNReal.ofReal (((n : ℝ) - 1) / (2 * (n : ℝ))) ≤
        kolmogorovDist (P.map (fun ω ↦ (W ω : ℝ))) stdExpLaw ∧
      (2 ≤ n →
        ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (((n : ℝ) - 1) / (2 * (n : ℝ))) ∧
        ENNReal.ofReal (1 / 4) ≤ kolmogorovDist (P.map (fun ω ↦ (W ω : ℝ))) stdExpLaw) := by
  intro W
  obtain ⟨_, hEq, _, _⟩ :=
    uniformAttachment_inDegree_equilibrium_coupling P hn hG hG_law hI hIndep hI_law
  have hmean : ∫ ω, (W ω : ℝ) ∂P = 1 := by
    have hm := hEq.2.2.2.2.1
    norm_num at hm
    exact hm
  have hp0 : P.real {ω | W ω = 0} = ((n : ℝ) - 1) / (2 * (n : ℝ)) :=
    probReal_uniformAttachment_inDegree_eq_zero P hn hG hG_law hI hIndep hI_law
  have hW_aem : AEMeasurable W P := hEq.2.2.1
  have hWR_aem : AEMeasurable (fun ω ↦ (W ω : ℝ)) P :=
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp_aemeasurable hW_aem
  have : IsProbabilityMeasure (P.map (fun ω ↦ (W ω : ℝ))) :=
    (Measure.isProbabilityMeasure_map_iff hWR_aem).mpr inferInstance
  have hmap_Iic0 : (P.map (fun ω ↦ (W ω : ℝ))).real (Set.Iic 0) = P.real {ω | W ω = 0} := by
    rw [measureReal_def, Measure.map_apply_of_aemeasurable hWR_aem measurableSet_Iic,
      ← measureReal_def]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ by exact_mod_cast le_antisymm h (Nat.cast_nonneg _), fun h ↦ by simp [h]⟩
  have hexp_Iic0 : stdExpLaw.real (Set.Iic 0) = 0 := by
    rw [measureReal_def, show stdExpLaw = expLaw 1 from rfl, expLaw_Iic_zero, ENNReal.toReal_zero]
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfrac_nn : 0 ≤ ((n : ℝ) - 1) / (2 * (n : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  have hkolm : ENNReal.ofReal (((n : ℝ) - 1) / (2 * (n : ℝ))) ≤
      kolmogorovDist (P.map (fun ω ↦ (W ω : ℝ))) stdExpLaw := by
    rw [kolmogorovDist_eq_iSup]
    refine le_trans ?_
      (le_iSup (fun x : ℝ ↦ ENNReal.ofReal
        |(P.map (fun ω ↦ (W ω : ℝ))).real (Set.Iic x) - stdExpLaw.real (Set.Iic x)|) 0)
    rw [hmap_Iic0, hexp_Iic0, sub_zero, hp0, abs_of_nonneg hfrac_nn]
  refine ⟨hmean, hp0, hkolm, fun hn2 ↦ ?_⟩
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hquarter : (1 / 4 : ℝ) ≤ ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  exact ⟨ENNReal.ofReal_le_ofReal hquarter, (ENNReal.ofReal_le_ofReal hquarter).trans hkolm⟩

/-- Non-exponential limit of uniform attachment in-degree (`SteinIntro.tex:3211-3212`; `SC-7`):
(1) for every $n \ge 1$, the in-degree $W$ of an independent uniformly chosen vertex in
`uniformAttachment n` has $\mathbb{E}[W] = 1$, $\mathbb{P}(W = 0) = \frac{n - 1}{2n}$, and
$d_{\mathrm{K}}(\mathcal{L}(W), \mathrm{Exp}(1)) \ge \frac{n - 1}{2n}$ (which is at least
$\frac{1}{4}$ for $n \ge 2$);
(2) consequently, for any sequence $(W_{n+1})_{n \ge 0}$ of uniform attachment in-degrees,
$d_{\mathrm{K}}(\mathcal{L}(W_{n+1}), \mathrm{Exp}(1)) \not\to 0$ as $n \to \infty$. -/
theorem sec6_3_not_exponential_proof :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n},
      AEMeasurable G P →
      P.map G = uniformAttachment n →
      AEMeasurable I P →
      ProbabilityTheory.IndepFun I G P →
      P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
      let W : Ω → ℕ := fun ω ↦ digraphInDegree (G ω) (I ω)
      ∫ ω, (W ω : ℝ) ∂P = 1 ∧
        P.real {ω | W ω = 0} = ((n : ℝ) - 1) / (2 * (n : ℝ)) ∧
        ENNReal.ofReal (((n : ℝ) - 1) / (2 * (n : ℝ))) ≤
          kolmogorovDist (P.map (fun ω ↦ (W ω : ℝ))) stdExpLaw ∧
        (2 ≤ n →
          ENNReal.ofReal (1 / 4) ≤ ENNReal.ofReal (((n : ℝ) - 1) / (2 * (n : ℝ))) ∧
          ENNReal.ofReal (1 / 4) ≤ kolmogorovDist (P.map (fun ω ↦ (W ω : ℝ))) stdExpLaw)) ∧
    (∀ (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
      (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
      (G : ∀ n, Ω n → Digraph (Fin (n + 1))) (I : ∀ n, Ω n → Fin (n + 1)),
      (∀ n, AEMeasurable (G n) (P n)) →
      (∀ n, (P n).map (G n) = uniformAttachment (n + 1)) →
      (∀ n, AEMeasurable (I n) (P n)) →
      (∀ n, ProbabilityTheory.IndepFun (I n) (G n) (P n)) →
      (∀ n, (P n).map (I n) =
        (@PMF.uniformOfFintype (Fin (n + 1)) inferInstance
          ⟨⟨0, Nat.succ_pos n⟩⟩).toMeasure) →
      ¬ Filter.Tendsto
        (fun n : ℕ ↦
          kolmogorovDist ((P n).map (fun ω ↦ (digraphInDegree (G n ω) (I n ω) : ℝ))) stdExpLaw)
        Filter.atTop (nhds 0)) := by
  refine ⟨?_, ?_⟩
  · intro Ω _ P _ n hn G I hG hG_law hI hIndep hI_law
    exact not_exponential_pointwise P hn hG hG_law hI hIndep hI_law
  · intro Ω _ P _ G I hG hG_law hI hIndep hI_law htend
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        kolmogorovDist ((P n).map (fun ω ↦ (digraphInDegree (G n ω) (I n ω) : ℝ))) stdExpLaw <
          ENNReal.ofReal (1 / 4) :=
      htend.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (by norm_num)))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    let m : ℕ := max N 1
    have hlt := hN m (le_max_left N 1)
    have hm2 : 2 ≤ m + 1 := Nat.succ_le_succ (le_max_right N 1)
    have hge :=
      ((not_exponential_pointwise (P m) (Nat.succ_pos m)
        (hG m) (hG_law m) (hI m) (hIndep m) (hI_law m)).2.2.2 hm2).2
    exact not_le_of_gt hlt hge

/-! ### Section 6.3: Total Variation Convergence to $\mathrm{Ge}^0(1/2)$ (`D-E1`) -/

/-- Total variation convergence of uniform attachment in-degree to $\mathrm{Ge}^0(1/2)$
(`SteinIntro.tex:3342-3343`; `D-E1`): for any sequence $(G_n, I_n)$ with
$G_n \sim \mathrm{uniformAttachment}\,(n + 1)$ and independent uniform
$I_n \in \mathrm{Fin}\,(n + 1)$,
$d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Ge}^0(1/2)) \to 0$ as $n \to \infty$. -/
theorem sec6_3_uniformAttachment_convergence_proof :
    ∀ (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
      (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
      (G : ∀ n, Ω n → Digraph (Fin (n + 1))) (I : ∀ n, Ω n → Fin (n + 1)),
      (∀ n, AEMeasurable (G n) (P n)) →
      (∀ n, (P n).map (G n) = uniformAttachment (n + 1)) →
      (∀ n, AEMeasurable (I n) (P n)) →
      (∀ n, ProbabilityTheory.IndepFun (I n) (G n) (P n)) →
      (∀ n, (P n).map (I n) =
        (@PMF.uniformOfFintype (Fin (n + 1)) inferInstance
          ⟨⟨0, Nat.succ_pos n⟩⟩).toMeasure) →
      Filter.Tendsto
        (fun n : ℕ ↦
          tvDist ((P n).map (fun ω ↦ digraphInDegree (G n ω) (I n ω))) (geomLaw (1 / 2)))
        Filter.atTop (nhds 0) := by
  intro Ω _ P _ G I hG hG_law hI hIndep hI_law
  have : IsProbabilityMeasure (geomLaw (1 / 2)) := by unfold geomLaw; infer_instance
  have hlog : Filter.Tendsto
      (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) :=
    tendsto_log_div_natCast_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hinv : Filter.Tendsto
      (fun n : ℕ ↦ (1 : ℝ) / ((n : ℕ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Filter.Tendsto
      (fun n : ℕ ↦ (Real.log ((n + 1 : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    have hsum := hlog.add hinv
    rw [add_zero] at hsum
    refine hsum.congr fun n ↦ ?_
    rw [add_div, Nat.cast_succ]
  have hupper : Filter.Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal ((Real.log ((n + 1 : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
    simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ ↦ zero_le) (fun n ↦ ?_)
  have hsharp := tvDist_uniformAttachment_inDegree_le_sharp
    (P n) (geomLaw (1 / 2)) (Nat.succ_pos n)
    (hG n) (hG_law n) (hI n) (hIndep n) (hI_law n) (N := id) Measure.map_id
  simpa only [Measure.map_id] using hsharp

end SteinMethod
