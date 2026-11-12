/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exponential.GeometricExample
import Mathlib.Probability.Independence.Integration

/-!
# Section 5.2 Auxiliary Lemmas (`Formalization.Exponential.GeometricSumsAux`)

Combinatorial, measurability, independence, and equilibrium-coupling helpers for random sums
$W = p \sum_{i=1}^N X_i$ used in `Formalization.Exponential.GeometricSums` and
`Formalization.Exponential.Renyi`.
-/

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace SteinMethod

lemma integrable_comp_of_lipschitz {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : Ω → ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hW : Integrable W P) (hLip : LipschitzWith K f) :
    Integrable (fun ω ↦ f (W ω)) P := by
  have hdom : Integrable (fun ω ↦ |f 0| + (K : ℝ) * ‖W ω‖) P :=
    (integrable_const |f 0|).add (hW.norm.const_mul (K : ℝ))
  refine hdom.mono'
    (hLip.continuous.measurable.comp_aemeasurable hW.aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hd := hLip.dist_le_mul (W ω) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero, ← Real.norm_eq_abs (W ω)] at hd
  rw [Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (f (W ω)) (f 0)]

lemma measurable_select_nat {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {f : ℕ → Ω → α} {M : Ω → ℕ} (hf : ∀ n, Measurable (f n)) (hM : Measurable M) :
    Measurable (fun ω ↦ f (M ω) ω) := by
  intro s hs
  have hpre : (fun ω ↦ f (M ω) ω) ⁻¹' s = ⋃ n : ℕ, (M ⁻¹' {n}) ∩ (f n ⁻¹' s) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h ↦ ⟨M ω, rfl, h⟩, fun ⟨n, hn, hfn⟩ ↦ hn.symm ▸ hfn⟩
  rw [hpre]
  exact MeasurableSet.iUnion fun n ↦ (hM (measurableSet_singleton n)).inter (hf n hs)

lemma sum_Icc_one_eq_sum_range {α : Type*} [AddCommMonoid α] (g : ℕ → α) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, g i = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
    rw [hsplit, Finset.sum_insert hnot, add_comm]

lemma Ico_one_succ (k : ℕ) : Finset.Ico 1 (k + 1) = Finset.Icc 1 k := by
  ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega

lemma sum_Icc_one_eq_tsum_ite (g : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, g i = ∑' k : ℕ, if k + 1 ≤ n then g (k + 1) else 0 := by
  rw [sum_Icc_one_eq_sum_range, tsum_eq_sum (s := Finset.range n)]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hle : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    simp [hle]
  · intro k hk
    have hgt : ¬ (k + 1 ≤ n) := by simp only [Finset.mem_range] at hk; omega
    simp [hgt]

lemma tsum_ite_le_eq_natCast (n : ℕ) :
    (∑' k : ℕ, if k + 1 ≤ n then (1 : ℝ≥0∞) else 0) = (n : ℝ≥0∞) := by
  have h := (sum_Icc_one_eq_tsum_ite (fun _ ↦ (1 : ℝ≥0∞)) n).symm
  rw [h, sum_Icc_one_eq_sum_range, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

lemma abs_equilibrium_sum_sub_le {X : ℕ → ℝ} (hX : ∀ i, 0 ≤ X i)
    {p : ℝ} (hp : 0 ≤ p) (Xe_m : ℝ) {n m : ℕ} (_hn : 1 ≤ n) (_hm : 1 ≤ m) :
    |p * ((∑ i ∈ Finset.Ico 1 m, X i) + Xe_m) - p * ∑ i ∈ Finset.Icc 1 n, X i| ≤
      p * |X m - Xe_m| + p * ∑ i ∈ Finset.Ioc (min n m) (max n m), X i := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hp, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hp
  have hm_ins : Finset.Icc 1 m = insert m (Finset.Ico 1 m) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  have hm_not : m ∉ Finset.Ico 1 m := by simp
  have hIco : (∑ i ∈ Finset.Ico 1 m, X i) + Xe_m =
      (∑ i ∈ Finset.Icc 1 m, X i) - (X m - Xe_m) := by
    rw [hm_ins, Finset.sum_insert hm_not]; ring
  rw [hIco]
  have hsplit : Finset.Icc 1 (max n m) =
      Finset.Icc 1 (min n m) ∪ Finset.Ioc (min n m) (max n m) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 (min n m)) (Finset.Ioc (min n m) (max n m)) :=
    Finset.disjoint_left.mpr fun x hx1 hx2 ↦ by
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2; omega
  have hdiff_abs : |(∑ i ∈ Finset.Icc 1 m, X i) - ∑ i ∈ Finset.Icc 1 n, X i| =
      ∑ i ∈ Finset.Ioc (min n m) (max n m), X i := by
    have hnn : 0 ≤ ∑ i ∈ Finset.Ioc (min n m) (max n m), X i :=
      Finset.sum_nonneg fun i _ ↦ hX i
    rcases le_total n m with hnm | hmn
    · have h1 : min n m = n := Nat.min_eq_left hnm
      have h2 : max n m = m := Nat.max_eq_right hnm
      rw [h1, h2] at hsplit hdisj hnn ⊢
      rw [hsplit, Finset.sum_union hdisj, add_sub_cancel_left, abs_of_nonneg hnn]
    · have h1 : min n m = m := Nat.min_eq_right hmn
      have h2 : max n m = n := Nat.max_eq_left hmn
      rw [h1, h2] at hsplit hdisj hnn ⊢
      rw [abs_sub_comm, hsplit, Finset.sum_union hdisj, add_sub_cancel_left, abs_of_nonneg hnn]
  calc
    |((∑ i ∈ Finset.Icc 1 m, X i) - (X m - Xe_m)) - ∑ i ∈ Finset.Icc 1 n, X i|
        = |((∑ i ∈ Finset.Icc 1 m, X i) - ∑ i ∈ Finset.Icc 1 n, X i) - (X m - Xe_m)| := by ring_nf
    _ ≤ |(∑ i ∈ Finset.Icc 1 m, X i) - ∑ i ∈ Finset.Icc 1 n, X i| + |X m - Xe_m| :=
          abs_sub _ _
    _ = |X m - Xe_m| + ∑ i ∈ Finset.Ioc (min n m) (max n m), X i := by rw [hdiff_abs, add_comm]

lemma sum_Ioc_eq_tsum_ite (g : ℕ → ℝ≥0∞) (a b : ℕ) :
    ∑ i ∈ Finset.Ioc a b, g i =
      ∑' k : ℕ, if k + 1 ∈ Finset.Ioc a b then g (k + 1) else 0 := by
  rw [tsum_eq_sum (s := Finset.Ico a b)]
  · refine Finset.sum_bij (fun i _ ↦ i - 1) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Ioc] at hi
      simp only [Finset.mem_Ico]
      omega
    · intro i₁ hi₁ i₂ hi₂ heq
      simp only [Finset.mem_Ioc] at hi₁ hi₂
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      refine ⟨k + 1, ?_, by omega⟩
      simp only [Finset.mem_Ioc]
      omega
    · intro i hi
      simp only [Finset.mem_Ioc] at hi
      have hsub : i - 1 + 1 = i := by omega
      have hmem : i ∈ Finset.Ioc a b := Finset.mem_Ioc.mpr hi
      simp [hsub, hmem]
  · intro k hk
    have hnot : k + 1 ∉ Finset.Ioc a b := by
      simp only [Finset.mem_Ico, Finset.mem_Ioc] at hk ⊢; omega
    simp [hnot]

lemma tsum_ite_mem_Ioc_eq_ofReal_abs_sub (n m : ℕ) :
    (∑' k : ℕ, if k + 1 ∈ Finset.Ioc (min n m) (max n m) then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal |(n : ℝ) - (m : ℝ)| := by
  rw [← sum_Ioc_eq_tsum_ite (fun _ ↦ (1 : ℝ≥0∞)), Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul,
    mul_one]
  rcases le_total n m with hnm | hmn
  · rw [Nat.min_eq_left hnm, Nat.max_eq_right hnm, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hnm)), ← Nat.cast_sub hnm,
      ENNReal.ofReal_natCast]
  · rw [Nat.min_eq_right hmn, Nat.max_eq_left hmn,
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hmn)), ← Nat.cast_sub hmn,
      ENNReal.ofReal_natCast]

lemma deriv_comp_const_add_eq (f : ℝ → ℝ) (s y : ℝ) :
    deriv (fun u ↦ f (s + u)) y = deriv f (s + y) := by
  by_cases hdiff : DifferentiableAt ℝ f (s + y)
  · have hd : HasDerivAt (fun u ↦ f (s + u)) (deriv f (s + y) * 1) y :=
      hdiff.hasDerivAt.comp y (by simpa using (hasDerivAt_id' y).const_add s)
    rw [hd.deriv, mul_one]
  · have hnd : ¬ DifferentiableAt ℝ (fun u ↦ f (s + u)) y := by
      intro hdg
      refine hdiff ?_
      let g : ℝ → ℝ := fun u ↦ f (s + u)
      have hdg' : DifferentiableAt ℝ g (-s + (s + y)) := by simpa [g] using hdg
      have hd_inv : DifferentiableAt ℝ (g ∘ fun z ↦ -s + z) (s + y) :=
        DifferentiableAt.comp (g := g) (f := fun z ↦ -s + z) (s + y) hdg'
          (differentiableAt_id.const_add (-s))
      refine hd_inv.congr_of_eventuallyEq (Eventually.of_forall fun z ↦ ?_)
      simp [g]
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hdiff]

lemma iIndepFun_indepFun_compl {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {β : ι → Type*} [m : ∀ k, MeasurableSpace (β k)] {f : ∀ k, Ω → β k}
    (hf_indep : iIndepFun f μ) (hf_meas : ∀ k, Measurable (f k)) (i : ι) :
    IndepFun (f i) (fun ω (j : {j : ι // j ≠ i}) ↦ f j.1 ω) μ := by
  rw [IndepFun_iff_Indep]
  have hdisj : Disjoint ({i} : Set ι) {j : ι | j ≠ i} :=
    Set.disjoint_singleton_left.mpr (by simp)
  have hind := indep_iSup_of_disjoint (fun k ↦ (hf_meas k).comap_le) hf_indep.iIndep hdisj
  refine indep_of_indep_of_le hind ?_ ?_
  · exact le_iSup₂_of_le i (Set.mem_singleton i) le_rfl
  · change MeasurableSpace.comap (fun ω (j : {j : ι // j ≠ i}) ↦ f j.1 ω)
        (⨆ j : {j : ι // j ≠ i}, (m j.1).comap (Function.eval j)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun j ↦ ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂_of_le j.1 j.2 le_rfl

lemma indepFun_fst_comp_prod_snd {Ω γ α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableSpace α] [MeasurableSpace β]
    {P : Measure Ω} {ν : Measure γ} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {A : Ω → α} {B : Ω → β} (hA : Measurable A) (hB : Measurable B) (hAB : A ⟂ᵢ[P] B) :
    (fun q : Ω × γ ↦ A q.1) ⟂ᵢ[P.prod ν] (fun q : Ω × γ ↦ (B q.1, q.2)) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s u hs hu
  let F : Ω × γ → α := fun q ↦ A q.1
  let G : Ω × γ → β × γ := fun q ↦ (B q.1, q.2)
  have hF : Measurable F := hA.comp measurable_fst
  have hG : Measurable G := (hB.comp measurable_fst).prodMk measurable_snd
  rw [Measure.prod_apply ((hF hs).inter (hG hu)), Measure.prod_apply (hF hs),
    Measure.prod_apply (hG hu)]
  let g₁ : α → ℝ≥0∞ := s.indicator 1
  let g₂ : β → ℝ≥0∞ := fun b ↦ ν (Prod.mk b ⁻¹' u)
  have hg₁ : Measurable g₁ := measurable_const.indicator hs
  have hg₂ : Measurable g₂ := measurable_measure_prodMk_left hu
  have hslice_inter : ∀ ω : Ω,
      ν (Prod.mk ω ⁻¹' (F ⁻¹' s ∩ G ⁻¹' u)) = g₁ (A ω) * g₂ (B ω) := fun ω ↦ by
    by_cases hω : A ω ∈ s
    · have hset : Prod.mk ω ⁻¹' (F ⁻¹' s ∩ G ⁻¹' u) = Prod.mk (B ω) ⁻¹' u := by
        ext y; simp [F, G, hω]
      simp [g₁, g₂, hω, hset]
    · have hset : Prod.mk ω ⁻¹' (F ⁻¹' s ∩ G ⁻¹' u) = ∅ := by
        ext y; simp [F, G, hω]
      simp [g₁, g₂, hω, hset]
  have hslice_F : ∀ ω : Ω, ν (Prod.mk ω ⁻¹' (F ⁻¹' s)) = g₁ (A ω) := fun ω ↦ by
    by_cases hω : A ω ∈ s
    · have hset : Prod.mk ω ⁻¹' (F ⁻¹' s) = univ := by ext y; simp [F, hω]
      simp [g₁, hω, hset]
    · have hset : Prod.mk ω ⁻¹' (F ⁻¹' s) = ∅ := by ext y; simp [F, hω]
      simp [g₁, hω, hset]
  have hslice_G : ∀ ω : Ω, ν (Prod.mk ω ⁻¹' (G ⁻¹' u)) = g₂ (B ω) := fun _ ↦ rfl
  simp_rw [hslice_inter, hslice_F, hslice_G]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hg₁.comp hA).aemeasurable (hg₂.comp hB).aemeasurable (hAB.comp hg₁ hg₂)

/-- Associativity of independence: if $X$ is independent of $Y$ and $(X, Y)$ is jointly independent
of $Z$, then $X$ is independent of $(Y, Z)$. -/
lemma indepFun_left_pair_of_indepFun_pair_right {Ω α β γ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → γ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y P) (hXYZ : IndepFun (fun ω ↦ (X ω, Y ω)) Z P) :
    IndepFun X (fun ω ↦ (Y ω, Z ω)) P := by
  have hYZ : IndepFun Y Z P := hXYZ.comp measurable_snd measurable_id
  have : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).mpr ‹_›
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable (hY.prodMk hZ).aemeasurable]
  have hmap : P.map (fun ω ↦ (X ω, (Y ω, Z ω))) =
      (P.map (fun ω ↦ ((X ω, Y ω), Z ω))).map MeasurableEquiv.prodAssoc := by
    rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable ((hX.prodMk hY).prodMk hZ)]
    rfl
  rw [hmap,
    (indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable hZ.aemeasurable).mp hXYZ,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hXY,
    Measure.prodAssoc_prod,
    ← (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp hYZ]

/-- Equilibrium coupling construction (`SteinIntro.tex:2953-2956, 2970-2984`, eq. `(5.6)`
`\label{179}`; minimal independence per `D5-1`) for clean measurable representatives
$(X_1, X_1^e, N_1, M_1)$: $W_1 = p \sum_{i=1}^{N_1} X_{1, i}$ is integrable with
$\mathbb{E}[W_1] = 1$, and $W_1^e = p (\sum_{i=1}^{M_1 - 1} X_{1, i} + X_{1, M_1}^e)$ satisfies
`IsEquilibrium P W₁ P We₁`. -/
lemma integrable_and_isEquilibrium_geom_sum_clean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} {X₁ Xe₁ : ℕ → Ω → ℝ} {N₁ M₁ : Ω → ℕ}
    (hp₀ : 0 < p)
    (hX₁_meas : ∀ i, Measurable (X₁ i))
    (hXe₁_meas : ∀ i, Measurable (Xe₁ i))
    (hX₁_nn : ∀ i ω, 0 ≤ X₁ i ω)
    (hX₁_int : ∀ i : ℕ, 1 ≤ i → Integrable (X₁ i) P)
    (hX₁_mean : ∀ i : ℕ, 1 ≤ i → ∫ ω, X₁ i ω ∂P = 1)
    (hX₁_indep : iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X₁ i.1) P)
    (hN₁_meas : Measurable N₁)
    (hM₁_meas : Measurable M₁)
    (hM₁_ge : ∀ ω, 1 ≤ M₁ ω)
    (hN₁R_int : Integrable (fun ω ↦ (N₁ ω : ℝ)) P)
    (hN₁R_mean : ∫ ω, (N₁ ω : ℝ) ∂P = 1 / p)
    (hM₁_pmf : ∀ m : ℕ, 1 ≤ m → P.real {ω | M₁ ω = m} = p * P.real {ω | m ≤ N₁ ω})
    (hXe₁_eq : ∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X₁ i) P (Xe₁ i))
    (hXe₁_indep : ∀ i : {i : ℕ // 1 ≤ i},
      IndepFun (Xe₁ i.1)
        (fun ω ↦ (N₁ ω, M₁ ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X₁ j.1.1 ω)) P)
    (hNM₁_indep : IndepFun (fun ω ↦ (N₁ ω, M₁ ω))
      (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X₁ i.1 ω) P) :
    let W₁ : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω
    let We₁ : Ω → ℝ := fun ω ↦ p * ((∑ i ∈ Finset.Ico 1 (M₁ ω), X₁ i ω) + Xe₁ (M₁ ω) ω)
    Integrable W₁ P ∧ (∫ ω, W₁ ω ∂P = 1) ∧ IsEquilibrium P W₁ P We₁ := by
  dsimp only
  let I₁ := {i : ℕ // 1 ≤ i}
  let W₁ : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω
  let We₁ : Ω → ℝ := fun ω ↦ p * ((∑ i ∈ Finset.Ico 1 (M₁ ω), X₁ i ω) + Xe₁ (M₁ ω) ω)
  have hX₁_lint : ∀ i : ℕ, 1 ≤ i → ∫⁻ ω, ENNReal.ofReal (X₁ i ω) ∂P = 1 := fun i hi ↦ by
    rw [← ofReal_integral_eq_lintegral_ofReal (hX₁_int i hi)
      (Eventually.of_forall fun ω ↦ hX₁_nn i ω), hX₁_mean i hi, ENNReal.ofReal_one]
  have hSum_meas : Measurable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) :=
    measurable_select_nat (fun n ↦ Finset.measurable_sum _ fun i _ ↦ hX₁_meas i) hN₁_meas
  have hWe₁_meas : Measurable We₁ :=
    measurable_select_nat
      (fun m ↦ measurable_const.mul
        ((Finset.measurable_sum _ fun i _ ↦ hX₁_meas i).add (hXe₁_meas m)))
      hM₁_meas
  have hW₁_nn : ∀ ω, 0 ≤ W₁ ω := fun ω ↦
    mul_nonneg hp₀.le (Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω)
  have hNM_meas : Measurable (fun ω ↦ (N₁ ω, M₁ ω)) := hN₁_meas.prodMk hM₁_meas
  have hXvec_meas : Measurable (fun ω (i : I₁) ↦ X₁ i.1 ω) :=
    measurable_pi_iff.mpr fun i ↦ hX₁_meas i.1
  have hSum_lint : ∫⁻ ω, ENNReal.ofReal (∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) ∂P =
      ENNReal.ofReal (1 / p) := by
    have hpt : ∀ ω, ENNReal.ofReal (∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) =
        ∑' k : ℕ, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (X₁ (k + 1) ω) := fun ω ↦ by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hX₁_nn i ω),
        sum_Icc_one_eq_tsum_ite (fun i ↦ ENNReal.ofReal (X₁ i ω))]
      congr 1; ext k
      by_cases hk : k + 1 ≤ N₁ ω
      · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
        rw [indicator_of_mem hmem, one_mul]
        simp only [hk, ↓reduceIte]
      · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
        rw [indicator_of_notMem hnot, zero_mul]
        simp only [hk, ↓reduceIte]
    simp_rw [hpt]
    have hm_term : ∀ k : ℕ, Measurable (fun ω ↦
        {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (X₁ (k + 1) ω)) := fun k ↦
      (measurable_const.indicator (hN₁_meas measurableSet_Ici)).mul
        (ENNReal.measurable_ofReal.comp (hX₁_meas (k + 1)))
    rw [lintegral_tsum fun k ↦ (hm_term k).aemeasurable]
    have hfactor : ∀ k : ℕ,
        ∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (X₁ (k + 1) ω) ∂P =
        ∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂P := fun k ↦ by
      let ik : I₁ := ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩
      let φ₁ : ℕ × ℕ → ℝ≥0∞ := fun q ↦ if k + 1 ≤ q.1 then 1 else 0
      let φ₂ : (I₁ → ℝ) → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (z ik)
      have hφ₁ : Measurable φ₁ := Measurable.of_discrete
      have hφ₂ : Measurable φ₂ := ENNReal.measurable_ofReal.comp (measurable_pi_apply ik)
      have hind := hNM₁_indep.comp hφ₁ hφ₂
      have hprod : (fun ω ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
          ENNReal.ofReal (X₁ (k + 1) ω)) =
          fun ω ↦ (φ₁ ∘ fun ω ↦ (N₁ ω, M₁ ω)) ω *
            (φ₂ ∘ fun ω (i : I₁) ↦ X₁ i.1 ω) ω := by
        ext ω
        dsimp only [φ₁, φ₂, Function.comp_apply]
        by_cases hk : k + 1 ≤ N₁ ω
        · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]; rfl
        · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]; rfl
      have hl1 : ∫⁻ ω, (φ₁ ∘ fun ω ↦ (N₁ ω, M₁ ω)) ω ∂P =
          ∫⁻ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂P := by
        refine lintegral_congr fun ω ↦ ?_
        dsimp only [φ₁, Function.comp_apply]
        by_cases hk : k + 1 ≤ N₁ ω
        · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]
        · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
      change lintegral P (fun ω ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (X₁ (k + 1) ω)) = _
      rw [hprod, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        (hφ₁.comp hNM_meas).aemeasurable (hφ₂.comp hXvec_meas).aemeasurable hind, hl1]
      have hl2 : ∫⁻ ω, (φ₂ ∘ fun ω (i : I₁) ↦ X₁ i.1 ω) ω ∂P = 1 :=
        hX₁_lint (k + 1) ik.2
      rw [hl2, mul_one]
    simp_rw [hfactor]
    rw [← lintegral_tsum fun k ↦
      (measurable_const.indicator (measurableSet_le measurable_const hN₁_meas)).aemeasurable]
    have htsum_N : ∀ ω, (∑' k : ℕ, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω) =
        ENNReal.ofReal (N₁ ω : ℝ) := fun ω ↦ by
      have hc : (fun k : ℕ ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω) =
          fun k ↦ if k + 1 ≤ N₁ ω then (1 : ℝ≥0∞) else 0 := by
        ext k
        by_cases hk : k + 1 ≤ N₁ ω
        · have hmem : ω ∈ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]
        · have hnot : ω ∉ {ω' | k + 1 ≤ N₁ ω'} := hk
          rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
      rw [hc, tsum_ite_le_eq_natCast, ENNReal.ofReal_natCast]
    simp_rw [htsum_N]
    rw [← ofReal_integral_eq_lintegral_ofReal hN₁R_int
      (Eventually.of_forall fun ω ↦ Nat.cast_nonneg (N₁ ω)), hN₁R_mean]
  have hSum_int : Integrable (fun ω ↦ ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) P :=
    ⟨hSum_meas.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall fun ω ↦ Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω), hSum_lint]
      exact ENNReal.ofReal_lt_top⟩
  have hW₁_int : Integrable W₁ P := hSum_int.const_mul p
  have hW₁_mean : ∫ ω, W₁ ω ∂P = 1 := by
    have hSum_mean_enn :
        ENNReal.ofReal (∫ ω, (∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) ∂P) =
          ENNReal.ofReal (1 / p) := by
      rw [ofReal_integral_eq_lintegral_ofReal hSum_int
        (Eventually.of_forall fun ω ↦ Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω), hSum_lint]
    have hSum_mean : ∫ ω, (∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω) ∂P = 1 / p := by
      have h1 := congrArg ENNReal.toReal hSum_mean_enn
      rwa [ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ Finset.sum_nonneg fun i _ ↦ hX₁_nn i ω),
        ENNReal.toReal_ofReal (by positivity)] at h1
    change ∫ ω, p * ∑ i ∈ Finset.Icc 1 (N₁ ω), X₁ i ω ∂P = 1
    rw [integral_const_mul, hSum_mean]
    field_simp [hp₀.ne']
  refine ⟨hW₁_int, hW₁_mean, Eventually.of_forall hW₁_nn, hW₁_int, hWe₁_meas.aemeasurable,
    fun f ⟨K, hLip⟩ ↦ ?_⟩
  rw [hW₁_mean, one_mul]
  let S : ℕ → Ω → ℝ := fun k ω ↦ p * ∑ i ∈ Finset.Icc 1 k, X₁ i ω
  have hS_meas : ∀ k, Measurable (S k) := fun k ↦
    measurable_const.mul (Finset.measurable_sum _ fun i _ ↦ hX₁_meas i)
  have hS_int : ∀ k, Integrable (S k) P := fun k ↦
    (integrable_finsetSum _ fun i hi ↦ hX₁_int i (Finset.mem_Icc.mp hi).1).const_mul p
  have hS_succ : ∀ k ω, S (k + 1) ω = S k ω + p * X₁ (k + 1) ω := fun k ω ↦ by
    dsimp only [S]
    rw [sum_Icc_one_eq_sum_range, sum_Icc_one_eq_sum_range, Finset.sum_range_succ, mul_add]
  have hS_mono : ∀ {a b : ℕ} (hab : a ≤ b) (ω : Ω), S a ω ≤ S b ω := fun {a b} hab ω ↦ by
    dsimp only [S]
    refine mul_le_mul_of_nonneg_left ?_ hp₀.le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ ↦ hX₁_nn i ω
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, hi.2.trans hab⟩
  have hdf_bdd : ∀ y : ℝ, |deriv f y| ≤ K := fun y ↦ by
    simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := y) hLip
  have hterm_eq : ∀ k : ℕ,
      ∫ ω, {ω' | k + 1 ≤ N₁ ω'}.indicator (fun ω' ↦ f (S (k + 1) ω') - f (S k ω')) ω ∂P =
      ∫ ω, {ω' | M₁ ω' = k + 1}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω ∂P := fun k ↦ by
    set m : ℕ := k + 1
    have hm : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le k)
    let im : I₁ := ⟨m, hm⟩
    let idx_lt : Fin k → {j : I₁ // j ≠ im} := fun r ↦
      ⟨⟨r.1 + 1, Nat.succ_le_succ (Nat.zero_le r.1)⟩, by
        intro heq
        have hval : r.1 + 1 = k + 1 := congrArg (fun x : I₁ ↦ x.1) heq
        omega⟩
    let ψS : ({j : I₁ // j ≠ im} → ℝ) → ℝ := fun z ↦ p * ∑ r : Fin k, z (idx_lt r)
    have hψS_meas : Measurable ψS :=
      measurable_const.mul (Finset.measurable_sum _ fun r _ ↦ measurable_pi_apply (idx_lt r))
    have hSk_eq_comp : S k = ψS ∘ (fun ω (j : {j : I₁ // j ≠ im}) ↦ X₁ j.1.1 ω) := by
      ext ω
      dsimp only [S, ψS, Function.comp_apply, idx_lt]
      rw [sum_Icc_one_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    have hIndep_Sk_Xm : IndepFun (S k) (X₁ m) P := by
      have hc := iIndepFun_indepFun_compl hX₁_indep (fun i : I₁ ↦ hX₁_meas i.1) im
      rw [hSk_eq_comp]
      exact (hc.comp measurable_id hψS_meas).symm
    have hIndep_Sk_Xem : IndepFun (S k) (Xe₁ m) P := by
      have hSk_triple : S k =
          (fun t : ℕ × ℕ × ({j : I₁ // j ≠ im} → ℝ) ↦ ψS t.2.2) ∘
            (fun ω ↦ (N₁ ω, M₁ ω, fun j : {j : I₁ // j ≠ im} ↦ X₁ j.1.1 ω)) := by
        ext ω; exact congrFun hSk_eq_comp ω
      rw [hSk_triple]
      exact ((hXe₁_indep im).comp measurable_id
        (hψS_meas.comp (measurable_snd.comp measurable_snd))).symm
    let Ym : Ω → ℝ := fun ω ↦ p * X₁ m ω
    let Yem : Ω → ℝ := fun ω ↦ p * Xe₁ m ω
    have hYm_meas : Measurable Ym := measurable_const.mul (hX₁_meas m)
    have hYem_meas : Measurable Yem := measurable_const.mul (hXe₁_meas m)
    have hYm_int : Integrable Ym P := (hX₁_int m hm).const_mul p
    have hYm_mean : ∫ ω, Ym ω ∂P = p := by
      change ∫ ω, p * X₁ m ω ∂P = p
      rw [integral_const_mul, hX₁_mean m hm, mul_one]
    have hEq_Ym : IsEquilibrium P Ym P Yem := (hXe₁_eq m hm).const_mul_pos hp₀
    have hIndep_Sk_Ym : IndepFun (S k) Ym P :=
      hIndep_Sk_Xm.comp measurable_id (measurable_const.mul measurable_id)
    have hIndep_Sk_Yem : IndepFun (S k) Yem P :=
      hIndep_Sk_Xem.comp measurable_id (measurable_const.mul measurable_id)
    have h_inner : ∫ ω, (f (S k ω + Ym ω) - f (S k ω)) ∂P =
        p * ∫ ω, deriv f (S k ω + Yem ω) ∂P := by
      let Φ₁ : ℝ × ℝ → ℝ := fun q ↦ f (q.1 + q.2) - f q.1
      let Φ₂ : ℝ × ℝ → ℝ := fun q ↦ deriv f (q.1 + q.2)
      have hΦ₁_meas : Measurable Φ₁ :=
        (hLip.continuous.comp (continuous_fst.add continuous_snd)).measurable.sub
          (hLip.continuous.comp continuous_fst).measurable
      have hΦ₂_meas : Measurable Φ₂ :=
        (measurable_deriv f).comp (measurable_fst.add measurable_snd)
      have : IsProbabilityMeasure (P.map (S k)) :=
        (Measure.isProbabilityMeasure_map_iff (hS_meas k).aemeasurable).mpr ‹_›
      have : IsProbabilityMeasure (P.map Ym) :=
        (Measure.isProbabilityMeasure_map_iff hYm_meas.aemeasurable).mpr ‹_›
      have : IsProbabilityMeasure (P.map Yem) :=
        (Measure.isProbabilityMeasure_map_iff hYem_meas.aemeasurable).mpr ‹_›
      have hΦ₁_int : Integrable Φ₁ ((P.map (S k)).prod (P.map Ym)) := by
        have hid_Ym : Integrable (fun y : ℝ ↦ (K : ℝ) * |y|) (P.map Ym) :=
          ((integrable_map_measure continuous_abs.measurable.aestronglyMeasurable
            hYm_meas.aemeasurable).mpr hYm_int.norm).const_mul (K : ℝ)
        have hdom : Integrable (fun q : ℝ × ℝ ↦ (K : ℝ) * |q.2|)
            ((P.map (S k)).prod (P.map Ym)) :=
          hid_Ym.comp_snd (P.map (S k))
        refine hdom.mono' hΦ₁_meas.aestronglyMeasurable (Eventually.of_forall fun q ↦ ?_)
        rw [Real.norm_eq_abs]
        have hd := hLip.dist_le_mul (q.1 + q.2) q.1
        simpa [Φ₁, Real.dist_eq] using hd
      have hΦ₂_int : Integrable Φ₂ ((P.map (S k)).prod (P.map Yem)) :=
        Integrable.of_bound hΦ₂_meas.aestronglyMeasurable K
          (Eventually.of_forall fun q ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd _)
      have hlhs_fub : ∫ ω, (f (S k ω + Ym ω) - f (S k ω)) ∂P =
          ∫ s, (∫ ω, (f (s + Ym ω) - f s) ∂P) ∂(P.map (S k)) := by
        have h1 : (fun ω ↦ f (S k ω + Ym ω) - f (S k ω)) = fun ω ↦ Φ₁ (S k ω, Ym ω) := rfl
        rw [h1, ← integral_map ((hS_meas k).prodMk hYm_meas).aemeasurable
          hΦ₁_meas.aestronglyMeasurable,
          hIndep_Sk_Ym.map_prod_eq_prod_map_map (hS_meas k).aemeasurable hYm_meas.aemeasurable,
          integral_prod Φ₁ hΦ₁_int]
        refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
        exact integral_map hYm_meas.aemeasurable
          (hΦ₁_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      have hrhs_fub : ∫ ω, deriv f (S k ω + Yem ω) ∂P =
          ∫ s, (∫ ω, deriv f (s + Yem ω) ∂P) ∂(P.map (S k)) := by
        have h1 : (fun ω ↦ deriv f (S k ω + Yem ω)) = fun ω ↦ Φ₂ (S k ω, Yem ω) := rfl
        rw [h1, ← integral_map ((hS_meas k).prodMk hYem_meas).aemeasurable
          hΦ₂_meas.aestronglyMeasurable,
          hIndep_Sk_Yem.map_prod_eq_prod_map_map (hS_meas k).aemeasurable hYem_meas.aemeasurable,
          integral_prod Φ₂ hΦ₂_int]
        refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
        exact integral_map hYem_meas.aemeasurable
          ((measurable_deriv f).comp (measurable_const.add measurable_id)).aestronglyMeasurable
      have hslice : ∀ s : ℝ,
          ∫ ω, (f (s + Ym ω) - f s) ∂P = p * ∫ ω, deriv f (s + Yem ω) ∂P := fun s ↦ by
        let gs : ℝ → ℝ := fun u ↦ f (s + u)
        have hgs_lip : LipschitzWith K gs := by
          refine LipschitzWith.of_dist_le_mul fun u v ↦ ?_
          simpa [gs, Real.dist_eq] using hLip.dist_le_mul (s + u) (s + v)
        have hgs_int : Integrable (fun ω ↦ gs (Ym ω)) P :=
          integrable_comp_of_lipschitz hYm_int hgs_lip
        have heq := hEq_Ym.2.2.2 gs ⟨K, hgs_lip⟩
        have hgs0 : gs 0 = f s := by simp [gs]
        have hder : (fun ω ↦ deriv gs (Yem ω)) = fun ω ↦ deriv f (s + Yem ω) :=
          funext fun ω ↦ deriv_comp_const_add_eq f s (Yem ω)
        rw [hgs0, hYm_mean, hder] at heq
        rw [integral_sub hgs_int (integrable_const (f s)), integral_const, probReal_univ,
          one_smul]
        exact heq
      rw [hlhs_fub, hrhs_fub, ← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall hslice)
    let α₁ : ℕ × ℕ → ℝ := fun q ↦ if m ≤ q.1 then 1 else 0
    let α₂ : ℕ → ℝ := fun q ↦ if q = m then 1 else 0
    let idx_le : Fin k → I₁ := fun r ↦ ⟨r.1 + 1, Nat.succ_le_succ (Nat.zero_le r.1)⟩
    let sum_z : (I₁ → ℝ) → ℝ := fun z ↦ p * ∑ r : Fin k, z (idx_le r)
    let β₁ : (I₁ → ℝ) → ℝ := fun z ↦ f (sum_z z + p * z im) - f (sum_z z)
    let β₂ : ℝ × ℝ → ℝ := fun q ↦ deriv f (q.1 + q.2)
    have hsum_z_meas : Measurable sum_z :=
      measurable_const.mul
        (Finset.measurable_sum _ fun r _ ↦ measurable_pi_apply (idx_le r))
    have hβ₁_meas : Measurable β₁ :=
      (hLip.continuous.measurable.comp
        (hsum_z_meas.add (measurable_const.mul (measurable_pi_apply im)))).sub
        (hLip.continuous.measurable.comp hsum_z_meas)
    have hβ₂_meas : Measurable β₂ :=
      (measurable_deriv f).comp (measurable_fst.add measurable_snd)
    have hα₁_meas : Measurable α₁ := Measurable.of_discrete
    have hα₂_meas : Measurable α₂ := Measurable.of_discrete
    have hsum_z_eq : ∀ ω, sum_z (fun i : I₁ ↦ X₁ i.1 ω) = S k ω := fun ω ↦ by
      dsimp only [sum_z, S, idx_le]
      rw [sum_Icc_one_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
    have hM₁_Sk_indep : IndepFun M₁ (S k) P := by
      have hSk_z : S k = sum_z ∘ (fun ω (i : I₁) ↦ X₁ i.1 ω) := funext fun ω ↦ (hsum_z_eq ω).symm
      rw [hSk_z]
      exact hNM₁_indep.comp measurable_snd hsum_z_meas
    have hMSk_Yem_indep : IndepFun (fun ω ↦ (M₁ ω, S k ω)) Yem P := by
      have hpair_eq : (fun ω ↦ (M₁ ω, S k ω)) =
          (fun t : ℕ × ℕ × ({j : I₁ // j ≠ im} → ℝ) ↦ (t.2.1, ψS t.2.2)) ∘
            (fun ω ↦ (N₁ ω, M₁ ω, fun j : {j : I₁ // j ≠ im} ↦ X₁ j.1.1 ω)) := by
        ext ω <;> simp [hSk_eq_comp]
      rw [hpair_eq]
      exact (hXe₁_indep im).symm.comp
        ((measurable_fst.comp measurable_snd).prodMk
          (hψS_meas.comp (measurable_snd.comp measurable_snd)))
        (measurable_const.mul measurable_id)
    have hM₁_SkYem_indep : IndepFun M₁ (fun ω ↦ (S k ω, Yem ω)) P :=
      indepFun_left_pair_of_indepFun_pair_right hM₁_meas (hS_meas k) hYem_meas
        hM₁_Sk_indep hMSk_Yem_indep
    have hlhs_prod : (fun ω ↦
        {ω' | m ≤ N₁ ω'}.indicator (fun ω' ↦ f (S (k + 1) ω') - f (S k ω')) ω) =
        fun ω ↦ α₁ (N₁ ω, M₁ ω) * β₁ (fun i : I₁ ↦ X₁ i.1 ω) := by
      ext ω
      dsimp only [α₁, β₁]
      rw [hsum_z_eq ω]
      by_cases hω : m ≤ N₁ ω
      · have hmem : ω ∈ {ω' | m ≤ N₁ ω'} := hω
        rw [indicator_of_mem hmem, hS_succ k ω]; simp only [hω, ↓reduceIte, one_mul]; rfl
      · have hnot : ω ∉ {ω' | m ≤ N₁ ω'} := hω
        rw [indicator_of_notMem hnot]; simp only [hω, ↓reduceIte, zero_mul]
    have hrhs_prod : (fun ω ↦
        {ω' | M₁ ω' = m}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω) =
        fun ω ↦ α₂ (M₁ ω) * β₂ (S k ω, Yem ω) := by
      ext ω
      dsimp only [α₂, β₂]
      by_cases hω : M₁ ω = m
      · have hWe_eq : We₁ ω = S k ω + Yem ω := by
          dsimp only [We₁, S, Yem]
          rw [hω, Ico_one_succ k, mul_add]
        have hmem : ω ∈ {ω' | M₁ ω' = m} := hω
        rw [indicator_of_mem hmem, hWe_eq]; simp only [hω, ↓reduceIte, one_mul]
      · have hnot : ω ∉ {ω' | M₁ ω' = m} := hω
        rw [indicator_of_notMem hnot]; simp only [hω, ↓reduceIte, zero_mul]
    have hβ₁_eq : (fun ω ↦ β₁ (fun i : I₁ ↦ X₁ i.1 ω)) =
        fun ω ↦ f (S k ω + Ym ω) - f (S k ω) := by
      ext ω; dsimp only [β₁, Ym]; rw [hsum_z_eq ω]
    have hβ₂_eq : (fun ω ↦ β₂ (S k ω, Yem ω)) =
        fun ω ↦ deriv f (S k ω + Yem ω) := rfl
    have hα₁_int : ∫ ω, α₁ (N₁ ω, M₁ ω) ∂P = P.real {ω | m ≤ N₁ ω} := by
      have hc : (fun ω ↦ α₁ (N₁ ω, M₁ ω)) = {ω | m ≤ N₁ ω}.indicator 1 := by
        ext ω
        by_cases hω : m ≤ N₁ ω
        · have hmem : ω ∈ {ω' | m ≤ N₁ ω'} := hω
          rw [indicator_of_mem hmem]; simp only [α₁, hω, ↓reduceIte]; rfl
        · have hnot : ω ∉ {ω' | m ≤ N₁ ω'} := hω
          rw [indicator_of_notMem hnot]; simp only [α₁, hω, ↓reduceIte]
      rw [hc]
      exact integral_indicator_one (measurableSet_le measurable_const hN₁_meas)
    have hα₂_int : ∫ ω, α₂ (M₁ ω) ∂P = P.real {ω | M₁ ω = m} := by
      have hc : (fun ω ↦ α₂ (M₁ ω)) = {ω | M₁ ω = m}.indicator 1 := by
        ext ω
        by_cases hω : M₁ ω = m
        · have hmem : ω ∈ {ω' | M₁ ω' = m} := hω
          rw [indicator_of_mem hmem]; simp only [α₂, hω, ↓reduceIte]; rfl
        · have hnot : ω ∉ {ω' | M₁ ω' = m} := hω
          rw [indicator_of_notMem hnot]; simp only [α₂, hω, ↓reduceIte]
      rw [hc]
      exact integral_indicator_one (measurableSet_eq_fun hM₁_meas measurable_const)
    rw [hlhs_prod, hrhs_prod,
      hNM₁_indep.integral_fun_comp_mul_comp hNM_meas.aemeasurable hXvec_meas.aemeasurable
        hα₁_meas.aestronglyMeasurable hβ₁_meas.aestronglyMeasurable,
      hM₁_SkYem_indep.integral_fun_comp_mul_comp hM₁_meas.aemeasurable
        ((hS_meas k).prodMk hYem_meas).aemeasurable
        hα₂_meas.aestronglyMeasurable hβ₂_meas.aestronglyMeasurable,
      hα₁_int, hα₂_int, hβ₁_eq, hβ₂_eq, h_inner, ← mul_assoc, mul_comm (P.real _) p,
      ← hM₁_pmf m hm]
  let L_seq : ℕ → Ω → ℝ := fun n ω ↦ f (S (min n (N₁ ω)) ω) - f 0
  let R_seq : ℕ → Ω → ℝ := fun n ω ↦
    {ω' | M₁ ω' ≤ n}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω
  have hL_sum : ∀ n ω, L_seq n ω =
      ∑ k ∈ Finset.range n,
        {ω' | k + 1 ≤ N₁ ω'}.indicator (fun ω' ↦ f (S (k + 1) ω') - f (S k ω')) ω := by
    intro n ω
    induction n with
    | zero => simp [L_seq, S]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      dsimp only [L_seq]
      by_cases hn : n + 1 ≤ N₁ ω
      · have hmem : ω ∈ {ω' | n + 1 ≤ N₁ ω'} := hn
        have h1 : min (n + 1) (N₁ ω) = n + 1 := Nat.min_eq_left hn
        have h2 : min n (N₁ ω) = n := Nat.min_eq_left (Nat.le_of_succ_le hn)
        rw [indicator_of_mem hmem, h1, h2]
        ring
      · have hnot : ω ∉ {ω' | n + 1 ≤ N₁ ω'} := hn
        have hle : N₁ ω ≤ n := by omega
        have h1 : min (n + 1) (N₁ ω) = N₁ ω := Nat.min_eq_right (Nat.le_succ_of_le hle)
        have h2 : min n (N₁ ω) = N₁ ω := Nat.min_eq_right hle
        rw [indicator_of_notMem hnot, h1, h2, add_zero]
  have hR_sum : ∀ n ω, R_seq n ω =
      ∑ k ∈ Finset.range n,
        {ω' | M₁ ω' = k + 1}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω := by
    intro n ω
    induction n with
    | zero =>
      dsimp only [R_seq]
      have hnot : ω ∉ {ω' | M₁ ω' ≤ 0} := by
        simp only [mem_ofPred_eq]; have := hM₁_ge ω; omega
      rw [Finset.sum_range_zero, indicator_of_notMem hnot]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      dsimp only [R_seq]
      rcases lt_trichotomy (M₁ ω) (n + 1) with hlt | heq | hgt
      · have hle1 : ω ∈ {ω' | M₁ ω' ≤ n + 1} := hlt.le
        have hle2 : ω ∈ {ω' | M₁ ω' ≤ n} := Nat.lt_succ_iff.mp hlt
        have hne : ω ∉ {ω' | M₁ ω' = n + 1} := hlt.ne
        rw [indicator_of_mem hle1, indicator_of_mem hle2, indicator_of_notMem hne, add_zero]
      · have hle1 : ω ∈ {ω' | M₁ ω' ≤ n + 1} := heq.le
        have hnot : ω ∉ {ω' | M₁ ω' ≤ n} := by simp only [mem_ofPred_eq]; omega
        have hmem : ω ∈ {ω' | M₁ ω' = n + 1} := heq
        rw [indicator_of_mem hle1, indicator_of_notMem hnot, indicator_of_mem hmem, zero_add]
      · have hnot1 : ω ∉ {ω' | M₁ ω' ≤ n + 1} := by simp only [mem_ofPred_eq]; omega
        have hnot2 : ω ∉ {ω' | M₁ ω' ≤ n} := by simp only [mem_ofPred_eq]; omega
        have hne : ω ∉ {ω' | M₁ ω' = n + 1} := hgt.ne'
        rw [indicator_of_notMem hnot1, indicator_of_notMem hnot2, indicator_of_notMem hne,
          add_zero]
  have hLR_int_eq : ∀ n : ℕ, ∫ ω, L_seq n ω ∂P = ∫ ω, R_seq n ω ∂P := fun n ↦ by
    have hL_term_int : ∀ k : ℕ, Integrable
        (fun ω ↦ {ω' | k + 1 ≤ N₁ ω'}.indicator
          (fun ω' ↦ f (S (k + 1) ω') - f (S k ω')) ω) P := fun k ↦
      ((integrable_comp_of_lipschitz (hS_int (k + 1)) hLip).sub
        (integrable_comp_of_lipschitz (hS_int k) hLip)).indicator
        (hN₁_meas measurableSet_Ici)
    have hR_term_int : ∀ k : ℕ, Integrable
        (fun ω ↦ {ω' | M₁ ω' = k + 1}.indicator (fun ω' ↦ deriv f (We₁ ω')) ω) P := fun k ↦
      (Integrable.of_bound ((measurable_deriv f).comp hWe₁_meas).aestronglyMeasurable K
        (Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hdf_bdd _)).indicator
        (hM₁_meas (measurableSet_singleton (k + 1)))
    simp_rw [hL_sum n, hR_sum n]
    rw [integral_finsetSum _ fun k _ ↦ hL_term_int k,
      integral_finsetSum _ fun k _ ↦ hR_term_int k]
    exact Finset.sum_congr rfl fun k _ ↦ hterm_eq k
  have hL_tendsto : Tendsto (fun n : ℕ ↦ ∫ ω, L_seq n ω ∂P) atTop
      (𝓝 (∫ ω, (f (W₁ ω) - f 0) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω ↦ (K : ℝ) * W₁ ω)
      (fun n ↦ ?_) (hW₁_int.const_mul (K : ℝ)) ?_ ?_
    · have hm : Measurable (L_seq n) := by
        refine (hLip.continuous.measurable.comp ?_).sub measurable_const
        exact measurable_select_nat (f := fun r ω ↦ S (min n r) ω)
          (fun r ↦ hS_meas (min n r)) hN₁_meas
      exact hm.aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun ω ↦ ?_
      rw [Real.norm_eq_abs]
      have hd := hLip.dist_le_mul (S (min n (N₁ ω)) ω) 0
      have hS0 : S 0 ω = 0 := by simp [S]
      have hSn_nn : 0 ≤ S (min n (N₁ ω)) ω := by
        rw [← hS0]; exact hS_mono (Nat.zero_le _) ω
      have hSn_le : S (min n (N₁ ω)) ω ≤ W₁ ω := hS_mono (Nat.min_le_right n (N₁ ω)) ω
      rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hSn_nn] at hd
      exact hd.trans (mul_le_mul_of_nonneg_left hSn_le K.coe_nonneg)
    · refine Eventually.of_forall fun ω ↦
        tendsto_atTop_of_eventually_const (i₀ := N₁ ω) fun n hn ↦ ?_
      dsimp only [L_seq]
      rw [Nat.min_eq_right hn]
  have hR_tendsto : Tendsto (fun n : ℕ ↦ ∫ ω, R_seq n ω ∂P) atTop
      (𝓝 (∫ ω, deriv f (We₁ ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (K : ℝ))
      (fun n ↦ (((measurable_deriv f).comp hWe₁_meas).indicator
        (hM₁_meas measurableSet_Iic)).aestronglyMeasurable)
      (integrable_const (K : ℝ)) ?_ ?_
    · intro n
      refine Eventually.of_forall fun ω ↦ ?_
      dsimp only [R_seq]
      by_cases hω : M₁ ω ≤ n
      · simp only [mem_ofPred_eq, hω, indicator_of_mem, Real.norm_eq_abs]
        exact hdf_bdd _
      · simp [hω]
    · refine Eventually.of_forall fun ω ↦
        tendsto_atTop_of_eventually_const (i₀ := M₁ ω) fun n hn ↦ ?_
      dsimp only [R_seq]
      simp [hn]
  simp_rw [hLR_int_eq] at hL_tendsto
  have hlim := tendsto_nhds_unique hL_tendsto hR_tendsto
  have hfW₁_int : Integrable (fun ω ↦ f (W₁ ω)) P := integrable_comp_of_lipschitz hW₁_int hLip
  rw [integral_sub hfW₁_int (integrable_const (f 0)), integral_const, probReal_univ,
    one_smul] at hlim
  exact hlim

lemma lintegral_ofReal_select_nat_eq_tsum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {M₁ : Ω → ℕ} {F : ℕ → Ω → ℝ}
    (hM₁_meas : Measurable M₁) (hM₁_ge : ∀ ω, 1 ≤ M₁ ω)
    (hF_meas : ∀ i, Measurable (F i))
    (hMF_indep : ∀ k : ℕ, IndepFun M₁ (F (k + 1)) P) :
    ∫⁻ ω, ENNReal.ofReal (F (M₁ ω) ω) ∂P =
      ∑' k : ℕ, P {ω' | M₁ ω' = k + 1} * ∫⁻ ω, ENNReal.ofReal (F (k + 1) ω) ∂P := by
  have hdecomp : ∀ ω, ENNReal.ofReal (F (M₁ ω) ω) =
      ∑' k : ℕ, {ω' | M₁ ω' = k + 1}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (k + 1) ω) := fun ω ↦ by
    rw [tsum_eq_single (M₁ ω - 1)]
    · have hm1 : 1 ≤ M₁ ω := hM₁_ge ω
      have hsub : M₁ ω - 1 + 1 = M₁ ω := by omega
      simp [hsub]
    · intro k hk
      have hm1 : 1 ≤ M₁ ω := hM₁_ge ω
      have hne : M₁ ω ≠ k + 1 := by omega
      simp [hne]
  simp_rw [hdecomp]
  have hm_term : ∀ k : ℕ, Measurable (fun ω ↦
      {ω' | M₁ ω' = k + 1}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (k + 1) ω)) := fun k ↦
    (measurable_const.indicator (hM₁_meas (measurableSet_singleton (k + 1)))).mul
      (ENNReal.measurable_ofReal.comp (hF_meas (k + 1)))
  rw [lintegral_tsum fun k ↦ (hm_term k).aemeasurable]
  refine tsum_congr fun k ↦ ?_
  let φ₁ : ℕ → ℝ≥0∞ := fun m ↦ if m = k + 1 then 1 else 0
  have hφ₁ : Measurable φ₁ := Measurable.of_discrete
  have hind := (hMF_indep k).comp hφ₁ ENNReal.measurable_ofReal
  have hprod : (fun ω ↦ {ω' | M₁ ω' = k + 1}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
      ENNReal.ofReal (F (k + 1) ω)) =
      fun ω ↦ (φ₁ ∘ M₁) ω * (ENNReal.ofReal ∘ F (k + 1)) ω := by
    ext ω
    dsimp only [φ₁, Function.comp_apply]
    by_cases hk : M₁ ω = k + 1
    · have hmem : ω ∈ {ω' | M₁ ω' = k + 1} := hk
      rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte, one_mul]
    · have hnot : ω ∉ {ω' | M₁ ω' = k + 1} := hk
      rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte, zero_mul]
  have hl1 : ∫⁻ ω, (φ₁ ∘ M₁) ω ∂P = P {ω' | M₁ ω' = k + 1} := by
    have hc : (fun ω ↦ (φ₁ ∘ M₁) ω) = {ω' | M₁ ω' = k + 1}.indicator 1 := by
      ext ω
      dsimp only [φ₁, Function.comp_apply]
      by_cases hk : M₁ ω = k + 1
      · have hmem : ω ∈ {ω' | M₁ ω' = k + 1} := hk
        rw [indicator_of_mem hmem]; simp only [hk, ↓reduceIte]; rfl
      · have hnot : ω ∉ {ω' | M₁ ω' = k + 1} := hk
        rw [indicator_of_notMem hnot]; simp only [hk, ↓reduceIte]
    rw [hc]
    exact lintegral_indicator_one (measurableSet_eq_fun hM₁_meas measurable_const)
  change lintegral P (fun ω ↦ {ω' | M₁ ω' = k + 1}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω *
    ENNReal.ofReal (F (k + 1) ω)) = _
  rw [hprod, lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hφ₁.comp hM₁_meas).aemeasurable
    (ENNReal.measurable_ofReal.comp (hF_meas (k + 1))).aemeasurable hind, hl1]
  rfl

end SteinMethod
