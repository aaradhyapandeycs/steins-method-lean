/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Exchangeable.AntiVoter
import Formalization.Exchangeable.AntiVoterGraph
import Formalization.Exchangeable.SteinPairBound
import Formalization.Kolmogorov.ExchangeableBound

/-!
# Anti-Voter Model Kolmogorov Normal Approximation (`Formalization.Exer.AntiVoterKolmogorov`)

Proves `sec3_6_2_antiVoter_kolmogorov` (`EXER-5`, `Sec3_6_2_antiVoter_kolmogorov`), formalizing the
Section 3.6.2 anti-voter Kolmogorov rate claim in Nathan Ross, *"Fundamentals of Stein's method"*
(`SteinIntro.tex:1810-1812`), by combining **Theorem 3.28** (`\label{thm92}`,
`IsSteinPair.kolmogorovDist_map_stdNormal_le`) with the Section 3.3.1 (`\label{secav}`) anti-voter
$(2/n)$-Stein pair (**Theorem 3.8**, `antiVoter_steinPair_and_wasserstein_bound`), the conditional
second-moment step identity (`SteinIntro.tex:1187-1199`, `sum_antiVoterStep_sq_sub_totalSpin`),
and conditional Jensen (**Remark 3.4**, `evariance_condExp_mono`, which upper-bounds
$\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])$ by
$\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid X])$, `EX-2`).
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace SteinMethod

/-! ### Section 1: Internal One-Step Anti-Voter Coupling on `(V → Bool) × (V → Bool)` -/

private noncomputable def antiVoterJointMeasure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) :
    Measure ((V → Bool) × (V → Bool)) :=
  Measure.sum fun p : (V → Bool) × (V → Bool) ↦
    (ν {p.1} * antiVoterStep G p.1 p.2) • Measure.dirac p

private lemma antiVoterJointMeasure_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) (x y : V → Bool) :
    antiVoterJointMeasure G ν {(x, y)} = ν {x} * antiVoterStep G x y := by
  rw [antiVoterJointMeasure, Measure.sum_apply _ (measurableSet_singleton (x, y)),
    tsum_eq_single (x, y)]
  · simp
  · intro p hp; simp [hp.symm]

private lemma antiVoterJointMeasure_fst_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) (x : V → Bool) :
    antiVoterJointMeasure G ν {p | p.1 = x} = ν {x} := by
  have hpart : ({p : (V → Bool) × (V → Bool) | p.1 = x} : Set _) = ⋃ y : V → Bool, {(x, y)} := by
    ext ⟨a, b⟩; simp [Prod.ext_iff, eq_comm]
  have hdisj : Pairwise fun y₁ y₂ : V → Bool ↦
      Disjoint ({(x, y₁)} : Set ((V → Bool) × (V → Bool))) {(x, y₂)} :=
    fun _ _ hne ↦ Set.disjoint_singleton.2 fun h ↦ hne (Prod.mk.inj h).2
  rw [hpart, measure_iUnion hdisj (fun y ↦ measurableSet_singleton (x, y)), tsum_fintype]
  simp_rw [antiVoterJointMeasure_singleton, ← Finset.mul_sum]
  have hsum : ∑ y : V → Bool, antiVoterStep G x y = 1 := by simpa using (antiVoterStep G x).tsum_coe
  rw [hsum, mul_one]

private instance antiVoterJointMeasure_isProbabilityMeasure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (antiVoterJointMeasure G ν) := by
  refine ⟨?_⟩
  have huniv : (univ : Set ((V → Bool) × (V → Bool))) = ⋃ x : V → Bool, {p | p.1 = x} := by
    ext p; simp
  have hdisj : Pairwise fun x₁ x₂ : V → Bool ↦
      Disjoint {p : (V → Bool) × (V → Bool) | p.1 = x₁} {p | p.1 = x₂} :=
    fun _ _ hne ↦ Set.disjoint_left.2 fun _ h1 h2 ↦ hne (h1.symm.trans h2)
  have huniv_ν : (univ : Set (V → Bool)) = ⋃ x : V → Bool, {x} := by ext x; simp
  have hd_ν : Pairwise fun x₁ x₂ : V → Bool ↦ Disjoint ({x₁} : Set (V → Bool)) {x₂} :=
    fun _ _ hne ↦ Set.disjoint_singleton.2 hne
  rw [huniv, measure_iUnion hdisj (fun x ↦ measurable_fst (measurableSet_singleton x))]
  simp_rw [antiVoterJointMeasure_fst_eq]
  rw [← measure_iUnion hd_ν (fun x ↦ measurableSet_singleton x), ← huniv_ν, measure_univ]

private lemma antiVoterJointMeasure_map_fst {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) :
    (antiVoterJointMeasure G ν).map Prod.fst = ν := by
  refine Measure.ext_of_singleton fun x ↦ ?_
  rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
  exact antiVoterJointMeasure_fst_eq G ν x

private lemma antiVoterJointMeasure_step {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) (x y : V → Bool) :
    antiVoterJointMeasure G ν {p | p.1 = x ∧ p.2 = y} =
      antiVoterJointMeasure G ν {p | p.1 = x} * antiVoterStep G x y := by
  rw [show ({p : (V → Bool) × (V → Bool) | p.1 = x ∧ p.2 = y} : Set _) = {(x, y)} by
    ext ⟨a, b⟩; simp [Prod.ext_iff], antiVoterJointMeasure_singleton, antiVoterJointMeasure_fst_eq]

private lemma antiVoterJointMeasure_step_ne_zero_ae {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) :
    ∀ᵐ p ∂(antiVoterJointMeasure G ν), antiVoterStep G p.1 p.2 ≠ 0 := by
  have hpair : ∀ q : (V → Bool) × (V → Bool),
      ∀ᵐ p ∂(antiVoterJointMeasure G ν), p = q → antiVoterStep G q.1 q.2 ≠ 0 := fun ⟨x, y⟩ ↦ by
    by_cases hxy : antiVoterStep G x y = 0
    · rw [ae_iff]
      refine measure_mono_null (t := {(x, y)}) (fun p hp ↦ (not_imp.mp hp).1) ?_
      rw [antiVoterJointMeasure_singleton, hxy, mul_zero]
    · exact ae_of_all _ fun _ _ ↦ hxy
  filter_upwards [ae_all_iff.mpr hpair] with p hp
  exact hp p rfl

private lemma integrable_of_fintype_dom {α : Type*} [Finite α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsFiniteMeasure μ] (g : α → ℝ) :
    Integrable g μ := by
  cases nonempty_fintype α
  exact Integrable.of_bound (measurable_of_finite g).aestronglyMeasurable (∑ a : α, |g a|)
    (ae_of_all μ fun a ↦ by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun b _ ↦ abs_nonneg (g b)) (Finset.mem_univ a))

private lemma condExp_antiVoterJointMeasure_fst {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure (V → Bool)) [IsProbabilityMeasure ν]
    (F : (V → Bool) → (V → Bool) → ℝ) :
    (antiVoterJointMeasure G ν)[fun p ↦ F p.1 p.2 | MeasurableSpace.comap Prod.fst inferInstance]
      =ᵐ[antiVoterJointMeasure G ν]
      fun p ↦ ∑ y : V → Bool, (antiVoterStep G p.1 y).toReal * F p.1 y := by
  let μ := antiVoterJointMeasure G ν
  let h : (V → Bool) → ℝ := fun z ↦ ∑ y : V → Bool, (antiVoterStep G z y).toReal * F z y
  let g : (V → Bool) × (V → Bool) → ℝ := fun p ↦ h p.1
  have hf_int : Integrable (fun p : (V → Bool) × (V → Bool) ↦ F p.1 p.2) μ :=
    integrable_of_fintype_dom μ fun p ↦ F p.1 p.2
  have hg_int : Integrable g μ := integrable_of_fintype_dom μ g
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance] g μ :=
    ((measurable_of_finite h).comp
      (comap_measurable (m := inferInstance) Prod.fst)).stronglyMeasurable.aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf_int
    (fun _ _ _ ↦ hg_int.integrableOn) (fun s hs _ ↦ ?_) hgm).symm
  rcases hs with ⟨B, _, rfl⟩
  classical
  let t : Finset (V → Bool) := Finset.univ.filter (· ∈ B)
  have hUnion : (Prod.fst : (V → Bool) × (V → Bool) → V → Bool) ⁻¹' B =
      ⋃ x ∈ t, {p | p.1 = x} := by
    ext p; simp only [t, mem_preimage, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_ofPred_eq]
    exact ⟨fun hp ↦ ⟨p.1, hp, rfl⟩, fun ⟨x, hx, heq⟩ ↦ heq.symm ▸ hx⟩
  have ht_meas : ∀ x ∈ t, MeasurableSet {p : (V → Bool) × (V → Bool) | p.1 = x} :=
    fun x _ ↦ measurable_fst (measurableSet_singleton x)
  have ht_disj : Set.PairwiseDisjoint (↑t)
      (fun x : V → Bool ↦ {p : (V → Bool) × (V → Bool) | p.1 = x}) :=
    fun _ _ _ _ hne ↦ Set.disjoint_left.2 fun _ h1 h2 ↦ hne (h1.symm.trans h2)
  rw [hUnion, integral_biUnion_finset t ht_meas ht_disj (fun _ _ ↦ hg_int.integrableOn),
    integral_biUnion_finset t ht_meas ht_disj (fun _ _ ↦ hf_int.integrableOn)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hx_meas : MeasurableSet {p : (V → Bool) × (V → Bool) | p.1 = x} :=
    measurable_fst (measurableSet_singleton x)
  have hLHS : ∫ p in {p | p.1 = x}, g p ∂μ =
      ∑ y : V → Bool, ν.real {x} * (antiVoterStep G x y).toReal * F x y := by
    calc ∫ p in {p | p.1 = x}, g p ∂μ
        = ∫ _ in {p | p.1 = x}, h x ∂μ := setIntegral_congr_fun hx_meas fun _ hp ↦ congrArg h hp
      _ = μ.real {p | p.1 = x} * h x := by rw [setIntegral_const, smul_eq_mul]
      _ = ∑ y : V → Bool, ν.real {x} * (antiVoterStep G x y).toReal * F x y := by
          dsimp only [μ, h]
          rw [Measure.real, antiVoterJointMeasure_fst_eq, ← Measure.real, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ ↦ (mul_assoc _ _ _).symm
  have hpart : ({p : (V → Bool) × (V → Bool) | p.1 = x} : Set _) = ⋃ y : V → Bool, {(x, y)} := by
    ext ⟨a, b⟩; simp [Prod.ext_iff, eq_comm]
  have hs_disj : Pairwise fun y₁ y₂ : V → Bool ↦
      Disjoint ({(x, y₁)} : Set ((V → Bool) × (V → Bool))) {(x, y₂)} :=
    fun _ _ hne ↦ Set.disjoint_singleton.2 fun hEq ↦ hne (Prod.mk.inj hEq).2
  have hRHS : ∫ p in {p | p.1 = x}, F p.1 p.2 ∂μ =
      ∑ y : V → Bool, ν.real {x} * (antiVoterStep G x y).toReal * F x y := by
    rw [hpart, integral_iUnion_fintype (fun y ↦ measurableSet_singleton (x, y)) hs_disj
      (fun _ ↦ hf_int.integrableOn)]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    calc ∫ p in {(x, y)}, F p.1 p.2 ∂μ
        = ∫ _ in {(x, y)}, F x y ∂μ := setIntegral_congr_fun (measurableSet_singleton (x, y))
            fun p hp ↦ by rw [mem_singleton_iff.mp hp]
      _ = μ.real {(x, y)} * F x y := by rw [setIntegral_const, smul_eq_mul]
      _ = ν.real {x} * (antiVoterStep G x y).toReal * F x y := by
          dsimp only [μ]
          rw [Measure.real, antiVoterJointMeasure_singleton, ENNReal.toReal_mul, ← Measure.real]
  exact hLHS.trans hRHS.symm

/-! ### Section 2: Section 3.6.2 Anti-Voter Kolmogorov Bound (`EXER-5`) -/

/-- Section 3.6.2 anti-voter Kolmogorov bound (`SteinIntro.tex:1810-1812`, applying Theorem 3.28
`\label{thm92}` to the anti-voter model of Section 3.3.1 `\label{secav}`): for any stationary
distribution of the anti-voter Markov chain on a finite $r$-regular simple graph $G$ on $n = |V|$
vertices that is neither bipartite nor isomorphic to `cycleGraph |V|`, with total spin
$S = \sum_{v \in V} \operatorname{spin}(X_v)$, $\sigma = \sqrt{\operatorname{Var}(S)}$,
$W = S / \sigma$, $Q = \sum_{i \in V} \sum_{j \in N_i} \operatorname{spin}(X_i)
\operatorname{spin}(X_j)$, and $Z \sim \mathcal{N}(0, 1)$,
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(Q)}}{2 r \sigma^2} + \frac{2 n}{\sigma^3} + \frac{3}{\sigma}$.

Reading notes: (1) hypotheses match Theorem 3.8 (`Thm3_8`), without requiring the next Markov step
$X'$ on $\Omega$ (constructed internally via `antiVoterStep G`); (2) Ross states qualitatively that
Theorem 3.28 yields Kolmogorov rates comparable to Section 3.3.1's Wasserstein bound, and this
bound follows from Theorem 3.28 (`a = 2/n`, `\delta = 2/\sigma`) after upper-bounding
$\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W]) \le
\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid X])$ via conditional Jensen / Remark 3.4 (`Rem3_4`)
(with $\sigma^2 \le n$ from Lemma 3.10 giving $\frac{2n}{\sigma^3} + \frac{3}{\sigma} \le
\frac{5n}{\sigma^3}$, the same order as Theorem 3.8); (3) $n \ge 4$, $r > 0$, and $\sigma > 0$ are
derived from the hypotheses, not assumed. -/
theorem sec3_6_2_antiVoter_kolmogorov
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → V → Bool} {Z : Ω' → ℝ}
    (hReg : G.IsRegularOfDegree r)
    (hBip : ¬ G.IsBipartite)
    (hCyc : IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)))
    (hX : Measurable X)
    (hStat : IsAntiVoterStationary G (P.map X))
    (hZ : AEMeasurable Z P')
    (hZ_law : P'.map Z = stdNormalLaw) :
    let n : ℝ := Fintype.card V
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    let Q : Ω → ℝ := fun ω ↦ ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (X ω i) * spin (X ω j)
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2) +
          2 * n / σ ^ 3 +
          3 / σ) := by
  dsimp only
  set n : ℝ := (Fintype.card V : ℝ)
  set S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
  set σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
  set W : Ω → ℝ := fun ω ↦ S ω / σ
  set Q : Ω → ℝ := fun ω ↦ ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (X ω i) * spin (X ω j)
  let ν : Measure (V → Bool) := P.map X
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).mpr ‹_›
  let Ω₀ := (V → Bool) × (V → Bool)
  let μ : Measure Ω₀ := antiVoterJointMeasure G ν
  have hmap_fst : μ.map Prod.fst = ν := antiVoterJointMeasure_map_fst G ν
  have hStat₀ : IsAntiVoterStationary G (μ.map Prod.fst) := hmap_fst.symm ▸ hStat
  let S₀ : Ω₀ → ℝ := fun p ↦ ∑ v : V, spin (p.1 v)
  let S'₀ : Ω₀ → ℝ := fun p ↦ ∑ v : V, spin (p.2 v)
  let Q₀ : Ω₀ → ℝ := fun p ↦ quadSpin G p.1
  have hVarS_eq : ProbabilityTheory.variance S₀ μ = ProbabilityTheory.variance S P := by
    change ProbabilityTheory.variance (totalSpin ∘ Prod.fst) μ =
      ProbabilityTheory.variance (totalSpin ∘ X) P
    rw [← ProbabilityTheory.variance_map (measurable_of_finite totalSpin).aemeasurable
        measurable_fst.aemeasurable, hmap_fst,
      ProbabilityTheory.variance_map (measurable_of_finite totalSpin).aemeasurable hX.aemeasurable]
  have hVarQ_eq : ProbabilityTheory.variance Q₀ μ = ProbabilityTheory.variance Q P := by
    change ProbabilityTheory.variance (quadSpin G ∘ Prod.fst) μ =
      ProbabilityTheory.variance (quadSpin G ∘ X) P
    rw [← ProbabilityTheory.variance_map (measurable_of_finite (quadSpin G)).aemeasurable
        measurable_fst.aemeasurable, hmap_fst,
      ProbabilityTheory.variance_map (measurable_of_finite (quadSpin G)).aemeasurable
        hX.aemeasurable]
  let W₀ : Ω₀ → ℝ := fun p ↦ S₀ p / σ
  let W'₀ : Ω₀ → ℝ := fun p ↦ S'₀ p / σ
  have hmapW_eq : μ.map W₀ = P.map W := by
    let g : (V → Bool) → ℝ := fun x ↦ totalSpin x / σ
    change μ.map (g ∘ Prod.fst) = P.map (g ∘ X)
    rw [← Measure.map_map (measurable_of_finite g) measurable_fst, hmap_fst,
      Measure.map_map (measurable_of_finite g) hX]
  have hStein₀ := (antiVoter_steinPair_and_wasserstein_bound G μ P' hReg hBip hCyc
    measurable_fst measurable_snd hStat₀ (antiVoterJointMeasure_step G ν) hZ hZ_law).1
  dsimp only at hStein₀
  rw [hVarS_eq] at hStein₀
  have hStein : IsSteinPair μ (2 / n) W₀ W'₀ := hStein₀
  have hk_ge : 1 ≤ kappa G := one_le_kappa_of_not_isBipartite G hBip
  have hn_ge : 3 ≤ Fintype.card V := three_le_card_of_not_isBipartite G hBip
  have hr_ge : 1 ≤ r := one_le_degree_of_not_isBipartite G hReg hBip
  have hr_pos_nat : 0 < r := Nat.lt_of_lt_of_le Nat.zero_lt_one hr_ge
  have hn_pos_nat : 0 < Fintype.card V := by omega
  have : Nonempty V := Fintype.card_pos_iff.mp hn_pos_nat
  have hV : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hk_real : (1 : ℝ) ≤ (kappa G : ℝ) := by exact_mod_cast hk_ge
  have hn_real : (3 : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast hn_ge
  have hr_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge
  have hn_pos : 0 < n := by linarith [hn_real]
  have hr_pos : 0 < (r : ℝ) := by linarith [hr_real]
  have ha_pos : 0 < 2 / n := div_pos zero_lt_two hn_pos
  obtain ⟨hVar_lo, _⟩ := antiVoter_variance_bounds G P hReg hr_pos_nat hX hStat
  have hVar_pos : 0 < ProbabilityTheory.variance S P :=
    lt_of_lt_of_le (div_pos (by linarith [hk_real]) hr_pos) hVar_lo
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr hVar_pos
  have hσ_ne : σ ≠ 0 := hσ_pos.ne'
  have hσ_sq : σ ^ 2 = ProbabilityTheory.variance S P := Real.sq_sqrt hVar_pos.le
  have hMeanS₀ : ∫ p, S₀ p ∂μ = 0 :=
    antiVoter_stationary_mean_zero G μ hV hReg hr_pos_nat measurable_fst hStat₀
  have hMeanW₀ : ∫ p, W₀ p ∂μ = 0 := by
    change ∫ p, S₀ p / σ ∂μ = 0
    rw [integral_div, hMeanS₀, zero_div]
  have hVarW₀ : ProbabilityTheory.variance W₀ μ = 1 := by
    rw [ProbabilityTheory.variance_of_integral_eq_zero hStein.2.2.2.1.aemeasurable hMeanW₀,
      show (fun p : Ω₀ ↦ W₀ p ^ 2) = fun p ↦ S₀ p ^ 2 / σ ^ 2 from
        funext fun p ↦ div_pow (S₀ p) σ 2,
      integral_div,
      ← ProbabilityTheory.variance_of_integral_eq_zero (measurable_of_finite S₀).aemeasurable
        hMeanS₀,
      hVarS_eq, ← hσ_sq, div_self (pow_ne_zero 2 hσ_ne)]
  have hδ : ∀ᵐ p ∂μ, |W'₀ p - W₀ p| ≤ 2 / σ := by
    filter_upwards [antiVoterJointMeasure_step_ne_zero_ae G ν] with p hp
    have hSpinLe : |totalSpin p.2 - totalSpin p.1| ≤ 2 :=
      antiVoterStep_totalSpin_abs_sub_le_two G hp
    change |totalSpin p.2 / σ - totalSpin p.1 / σ| ≤ 2 / σ
    rw [← sub_div, abs_div, abs_of_pos hσ_pos]
    exact div_le_div_of_nonneg_right hSpinLe hσ_pos.le
  have hmWX : MeasurableSpace.comap W₀ inferInstance ≤
      MeasurableSpace.comap (Prod.fst : Ω₀ → V → Bool) inferInstance := by
    rintro _ ⟨A, hA, rfl⟩
    exact ⟨(fun x : V → Bool ↦ totalSpin x / σ) ⁻¹' A,
      measurable_of_finite (fun x : V → Bool ↦ totalSpin x / σ) hA, rfl⟩
  set D2 : Ω₀ → ℝ := fun p ↦ (W'₀ p - W₀ p) ^ 2
  set c₁ : ℝ := 2 / σ ^ 2
  set c₂ : ℝ := 2 / (n * (r : ℝ) * σ ^ 2)
  have hD2_int : Integrable D2 μ := integrable_of_fintype_dom μ D2
  have hCondD2_X :
      μ[D2 | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[μ] fun p ↦ c₁ + c₂ * Q₀ p := by
    have hBase := condExp_antiVoterJointMeasure_fst G ν
      (fun x y ↦ (totalSpin y / σ - totalSpin x / σ) ^ 2)
    have hSumD2 : ∀ x : V → Bool,
        (∑ y : V → Bool,
          (antiVoterStep G x y).toReal * (totalSpin y / σ - totalSpin x / σ) ^ 2) =
          c₁ + c₂ * quadSpin G x := fun x ↦ by
      have hSplit : ∀ y : V → Bool,
          (antiVoterStep G x y).toReal * (totalSpin y / σ - totalSpin x / σ) ^ 2 =
            ((antiVoterStep G x y).toReal * (totalSpin y - totalSpin x) ^ 2) * (σ ^ 2)⁻¹ :=
        fun y ↦ by rw [← sub_div, div_pow, div_eq_mul_inv, ← mul_assoc]
      simp_rw [hSplit]
      rw [← Finset.sum_mul, sum_antiVoterStep_sq_sub_totalSpin G hV hReg hr_pos_nat x]
      dsimp only [c₁, c₂, n]; ring
    exact hBase.mono fun p hp ↦ hp.trans (hSumD2 p.1)
  have hAffQ2 : MemLp (fun p : Ω₀ ↦ c₁ + c₂ * Q₀ p) 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_of_finite (fun p : Ω₀ ↦ c₁ + c₂ * Q₀ p)).aestronglyMeasurable).mpr
      (integrable_of_fintype_dom μ fun p ↦ (c₁ + c₂ * Q₀ p) ^ 2)
  have hc₂Q_asm : AEStronglyMeasurable (fun p : Ω₀ ↦ c₂ * Q₀ p) μ :=
    (measurable_of_finite (fun p : Ω₀ ↦ c₂ * Q₀ p)).aestronglyMeasurable
  have hc₂_nn : 0 ≤ c₂ := by positivity
  have h2a_pos : 0 < 2 * (2 / n) := by positivity
  have hTerm₁ :
      ProbabilityTheory.evariance (μ[D2 | MeasurableSpace.comap W₀ inferInstance]) μ ^
          (1 / 2 : ℝ) / ENNReal.ofReal (2 * (2 / n)) ≤
        ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2)) := by
    have hEvarLe :
        ProbabilityTheory.evariance (μ[D2 | MeasurableSpace.comap W₀ inferInstance]) μ ≤
          ENNReal.ofReal (c₂ ^ 2 * ProbabilityTheory.variance Q P) := by
      refine (evariance_condExp_mono μ hmWX measurable_fst.comap_le hD2_int).trans_eq ?_
      rw [ProbabilityTheory.evariance_congr hCondD2_X, ← ProbabilityTheory.ofReal_variance hAffQ2,
        ProbabilityTheory.variance_const_add hc₂Q_asm c₁,
        ProbabilityTheory.variance_const_mul c₂ Q₀ μ, hVarQ_eq]
    have hRpowLe :
        ProbabilityTheory.evariance (μ[D2 | MeasurableSpace.comap W₀ inferInstance]) μ ^
            (1 / 2 : ℝ) ≤
          ENNReal.ofReal (c₂ * Real.sqrt (ProbabilityTheory.variance Q P)) := by
      refine (ENNReal.rpow_le_rpow hEvarLe (by positivity)).trans_eq ?_
      rw [ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (sq_nonneg c₂) (ProbabilityTheory.variance_nonneg Q P)) (by positivity),
        ← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg c₂) (ProbabilityTheory.variance Q P),
        Real.sqrt_sq hc₂_nn]
    have hQuot₁ :
        c₂ * Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (2 / n)) =
          Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2) := by
      dsimp only [c₂]
      have hn_ne : n ≠ 0 := hn_pos.ne'
      have hr_ne : (r : ℝ) ≠ 0 := hr_pos.ne'
      field_simp [hn_ne, hr_ne, hσ_ne]
    refine (ENNReal.div_le_div_right hRpowLe _).trans_eq ?_
    rw [← ENNReal.ofReal_div_of_pos h2a_pos, hQuot₁]
  have hQuot₂ :
      (2 / σ) ^ 3 / (2 * (2 / n)) + 3 * (2 / σ) / 2 = 2 * n / σ ^ 3 + 3 / σ := by
    have hn_ne : n ≠ 0 := hn_pos.ne'
    field_simp [hn_ne, hσ_ne]
  have hT1_nn : 0 ≤ Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2) :=
    div_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hT2_nn : 0 ≤ 2 * n / σ ^ 3 + 3 / σ := by positivity
  rw [← hmapW_eq]
  calc kolmogorovDist (μ.map W₀) (P'.map Z)
      ≤ ProbabilityTheory.evariance (μ[D2 | MeasurableSpace.comap W₀ inferInstance]) μ ^
            (1 / 2 : ℝ) / ENNReal.ofReal (2 * (2 / n)) +
          ENNReal.ofReal ((2 / σ) ^ 3 / (2 * (2 / n)) + 3 * (2 / σ) / 2) :=
        hStein.kolmogorovDist_map_stdNormal_le P' hVarW₀ hδ hZ hZ_law
    _ ≤ ENNReal.ofReal (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2)) +
          ENNReal.ofReal (2 * n / σ ^ 3 + 3 / σ) := by
        rw [hQuot₂]; exact add_le_add_left hTerm₁ _
    _ = ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2) +
            (2 * n / σ ^ 3 + 3 / σ)) := (ENNReal.ofReal_add hT1_nn hT2_nn).symm
    _ = ENNReal.ofReal
          (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2) +
            2 * n / σ ^ 3 + 3 / σ) := by rw [← add_assoc]

end SteinMethod
