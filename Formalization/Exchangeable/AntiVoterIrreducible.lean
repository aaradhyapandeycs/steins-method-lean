/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Exchangeable.AntiVoterGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Irreducibility of the Anti-Voter Chain on Non-Constant Labelings

Constructive graph-combinatorial proof that on any connected finite simple graph `G` that is
neither bipartite nor isomorphic to `SimpleGraph.cycleGraph (Fintype.card V)`, the anti-voter
Markov chain is irreducible on the set of non-constant vertex labelings
(`SteinIntro.tex:1101-1111`, citing Aldous–Fill `[af10]`; `ISSUE-3.8`):

1. **Shortest odd cycle & tadpole subgraph**: From `¬ G.IsBipartite` and `G.Connected`, a
   minimum-length odd closed cyclic walk has no repeated vertices and no chords, embeds properly
   since `G` is not isomorphic to `cycleGraph |V|`, and attaches a pendant leaf `tadpoleGraph k`.
2. **Tadpole base case**: Every configuration on `tadpoleGraph k` (`1 ≤ k`) reaches the leaf
   singleton, which reaches all singletons, which reach all non-constant configurations.
3. **Pendant-vertex induction**: Extending the active vertex subset one connected vertex at a time
   yields irreducibility on `Finset.univ`.
-/

namespace SteinMethod

/-- Predicate that `x : V → Bool` attains both `true` (`+1`) and `false` (`-1`) on `V`
(`SteinIntro.tex:1102-1111`, `ISSUE-3.8`). -/
def IsNonConstLabeling {V : Type*} (x : V → Bool) : Prop :=
  (∃ a : V, x a = true) ∧ (∃ b : V, x b = false)

/-- Combinatorial one-step transition of the anti-voter chain on `G`: choose an edge `v ~ u` and
update `v` to `!x u` (`SteinIntro.tex:1103-1105`). -/
def AntiVoterStepRel {V : Type*} [DecidableEq V] (G : SimpleGraph V) (x y : V → Bool) : Prop :=
  ∃ v u : V, G.Adj v u ∧ y = Function.update x v (!x u)

/-- Multi-step (`≥ 0` steps) combinatorial reachability under `AntiVoterStepRel G`. -/
abbrev AntiVoterReach {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    (V → Bool) → (V → Bool) → Prop :=
  Relation.ReflTransGen (AntiVoterStepRel G)

/-- Exact support characterization of `antiVoterStep G x` on a nonempty graph without isolated
vertices (`SteinIntro.tex:1103-1105`). -/
theorem antiVoterStep_ne_zero_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : (Finset.univ : Finset V).Nonempty)
    (hN : ∀ v : V, (G.neighborFinset v).Nonempty) (x y : V → Bool) :
    antiVoterStep G x y ≠ 0 ↔ AntiVoterStepRel G x y := by
  rw [← PMF.mem_support_iff]
  unfold antiVoterStep AntiVoterStepRel
  simp only [hV, ↓reduceDIte, PMF.mem_support_bind_iff, PMF.mem_support_uniformOfFinset_iff,
    Finset.mem_univ, true_and]
  refine ⟨fun ⟨v, hv⟩ ↦ ?_, fun ⟨v, u, hadj, hy⟩ ↦ ⟨v, ?_⟩⟩
  · simp only [hN v, ↓reduceDIte, PMF.mem_support_map_iff,
      PMF.mem_support_uniformOfFinset_iff, G.mem_neighborFinset] at hv
    rcases hv with ⟨u, hu, hy⟩; exact ⟨v, u, hu, hy.symm⟩
  · subst hy
    simp only [hN v, ↓reduceDIte, PMF.mem_support_map_iff,
      PMF.mem_support_uniformOfFinset_iff, G.mem_neighborFinset]
    exact ⟨u, hadj, rfl⟩

/-- In a connected graph, any proper nonempty vertex subset `S` has an edge crossing to `Sᶜ`. -/
theorem exists_adj_mem_notMem_of_connected {V : Type*}
    {G : SimpleGraph V} (hConn : G.Connected) {S : Finset V}
    (hne : S.Nonempty) (hproper : ∃ w : V, w ∉ S) :
    ∃ u ∈ S, ∃ z ∉ S, G.Adj u z := by
  rcases hne with ⟨u₀, hu₀⟩; rcases hproper with ⟨w₀, hw₀⟩
  obtain ⟨p⟩ := hConn.preconnected u₀ w₀
  induction p with
  | nil => exact (hw₀ hu₀).elim
  | @cons a b _ hadj _ ih =>
    by_cases hb : b ∈ S; · exact ih hb hw₀
    exact ⟨a, hu₀, b, hb, hadj⟩

/-! ### Shortest odd cycle and tadpole embedding -/

private def IsOddCyclicWalk {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : Fin (2 * k + 1) → V) : Prop :=
  ∀ i : Fin (2 * k + 1), G.Adj (c i) (c (i + 1))

private lemma isOddCyclicWalk_rotate {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {c : Fin (2 * k + 1) → V} (hc : IsOddCyclicWalk G k c) (r : Fin (2 * k + 1)) :
    IsOddCyclicWalk G k (fun i ↦ c (i + r)) := fun i ↦ by
  have h : i + 1 + r = (i + r) + 1 := by abel
  simpa [h] using hc (i + r)

private lemma exists_isOddCyclicWalk {V : Type*} {G : SimpleGraph V}
    (hConn : G.Connected) (hBip : ¬ G.IsBipartite) :
    ∃ k : ℕ, ∃ c : Fin (2 * k + 1) → V, IsOddCyclicWalk G k c := by
  classical
  have hex_walk : ∃ (v : V) (w : G.Walk v v), Odd w.length := by
    by_contra hno
    obtain ⟨v₀⟩ := hConn.nonempty
    let col : V → Fin 2 := fun v ↦ if ∃ p : G.Walk v₀ v, Even p.length then 0 else 1
    refine hBip ⟨SimpleGraph.Coloring.mk col fun {u v} hadj hcol ↦ ?_⟩
    by_cases hu : ∃ p : G.Walk v₀ u, Even p.length <;>
      by_cases hv : ∃ q : G.Walk v₀ v, Even q.length
    · rcases hu with ⟨p, a, ha⟩
      rcases hv with ⟨q, b, hb⟩
      exact hno ⟨v₀, p.append ((SimpleGraph.Walk.cons hadj .nil).append q.reverse),
        ⟨a + b, by simp [ha, hb]; omega⟩⟩
    · simp [col, hu, hv] at hcol
    · simp [col, hu, hv] at hcol
    · obtain ⟨p⟩ := hConn.preconnected v₀ u
      obtain ⟨q⟩ := hConn.preconnected v₀ v
      rcases Nat.not_even_iff_odd.mp (fun h ↦ hu ⟨p, h⟩) with ⟨a, ha⟩
      rcases Nat.not_even_iff_odd.mp (fun h ↦ hv ⟨q, h⟩) with ⟨b, hb⟩
      exact hno ⟨v₀, p.append ((SimpleGraph.Walk.cons hadj .nil).append q.reverse),
        ⟨a + b + 1, by simp [ha, hb]; omega⟩⟩
  obtain ⟨v, w, ⟨k, hk⟩⟩ := hex_walk
  refine ⟨k, fun i ↦ w.getVert i.1, fun i ↦ ?_⟩
  have hi2 := i.2
  have hadj := w.adj_getVert_succ (by omega : i.1 < w.length)
  by_cases hlast : i.1 + 1 < 2 * k + 1
  · simpa [Fin.val_add_one_of_lt' hlast] using hadj
  · have hi_eq : i.1 + 1 = 2 * k + 1 := by omega
    have hval : (i + 1).1 = 0 := by simp [Fin.val_add, hi_eq]
    have hlen : w.getVert (i.1 + 1) = w.getVert 0 := by
      rw [hi_eq, ← hk, w.getVert_length, w.getVert_zero]
    simpa [hval, ← hlen] using hadj

private lemma not_odd_loop_of_min_cyclic {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {c : Fin (2 * k + 1) → V} (hc : IsOddCyclicWalk G k c)
    (hmin : ∀ k' < k, ¬ ∃ c' : Fin (2 * k' + 1) → V, IsOddCyclicWalk G k' c')
    {d : ℕ} (_hd0 : 0 < d) (hdm : d < 2 * k + 1) (hd_odd : Odd d) (heq : c 0 = c ⟨d, hdm⟩) :
    False := by
  rcases hd_odd with ⟨k', hk'⟩
  refine hmin k' (by omega) ⟨fun t ↦ c ⟨t.1, by have := t.2; omega⟩, fun t ↦ ?_⟩
  have ht2 := t.2
  by_cases ht : t.1 + 1 < 2 * k' + 1
  · have hval' : (⟨t.1, by omega⟩ + 1 : Fin (2 * k + 1)) = ⟨t.1 + 1, by omega⟩ :=
      Fin.ext (Fin.val_add_one_of_lt' (by dsimp; omega))
    simpa [Fin.val_add_one_of_lt' ht, ← hval'] using hc ⟨t.1, by omega⟩
  · have ht_eq : t.1 + 1 = 2 * k' + 1 := by omega
    have hval : (t + 1).1 = 0 := by simp [Fin.val_add, ht_eq]
    have hval' : (⟨t.1, by omega⟩ + 1 : Fin (2 * k + 1)) = ⟨d, hdm⟩ := by
      ext; rw [Fin.val_add_one_of_lt' (by dsimp; omega), ht_eq, ← hk']
    have hadj := hc ⟨t.1, by omega⟩
    rw [hval', ← heq] at hadj; simpa [hval] using hadj

private lemma not_even_chord_of_min_cyclic {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {c : Fin (2 * k + 1) → V} (hc : IsOddCyclicWalk G k c)
    (hmin : ∀ k' < k, ¬ ∃ c' : Fin (2 * k' + 1) → V, IsOddCyclicWalk G k' c')
    {r : ℕ} (hr1 : 2 ≤ r) (hrm : r ≤ 2 * k - 1) (heven : Even r)
    (hadj0r : G.Adj (c 0) (c ⟨r, by omega⟩)) : False := by
  rcases heven with ⟨k', hk'⟩
  refine hmin k' (by omega) ⟨fun t ↦ c ⟨t.1, by have := t.2; omega⟩, fun t ↦ ?_⟩
  have ht2 := t.2
  by_cases ht : t.1 + 1 < 2 * k' + 1
  · have hval' : (⟨t.1, by omega⟩ + 1 : Fin (2 * k + 1)) = ⟨t.1 + 1, by omega⟩ :=
      Fin.ext (Fin.val_add_one_of_lt' (by dsimp; omega))
    simpa [Fin.val_add_one_of_lt' ht, ← hval'] using hc ⟨t.1, by omega⟩
  · have ht_eq : t.1 + 1 = 2 * k' + 1 := by omega
    have hval : (t + 1).1 = 0 := by simp [Fin.val_add, ht_eq]
    simpa [(by omega : t.1 = r), hval] using hadj0r.symm

/-- The `(2k + 1, 1)`-tadpole graph on `Option (Fin (2 * k + 1))`: `some i` forms
`cycleGraph (2 * k + 1)` and `none` is a pendant leaf adjacent only to `some 0`. -/
def tadpoleGraph (k : ℕ) : SimpleGraph (Option (Fin (2 * k + 1))) where
  Adj a b :=
    match a, b with
    | none, none => False
    | none, some j => j = 0
    | some i, none => i = 0
    | some i, some j => (SimpleGraph.cycleGraph (2 * k + 1)).Adj i j
  symm := ⟨fun a b h ↦ by cases a <;> cases b <;> first | exact h | exact h.symm⟩
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact (SimpleGraph.cycleGraph (2 * k + 1)).irrefl h⟩

private lemma tadpoleGraph_connected {k : ℕ} : (tadpoleGraph k).Connected := by
  refine ⟨fun a b ↦ ?_⟩
  have h0 : ∀ x : Option (Fin (2 * k + 1)), (tadpoleGraph k).Reachable (some 0) x := by
    rintro (_ | j)
    · exact SimpleGraph.Adj.reachable (rfl : (tadpoleGraph k).Adj (some 0) none)
    · obtain ⟨p⟩ := (SimpleGraph.cycleGraph_connected (n := 2 * k)).preconnected 0 j
      exact ⟨p.map ⟨some, fun hadj ↦ hadj⟩⟩
  exact (h0 a).symm.trans (h0 b)

private lemma fin_eq_add_one_of_sub_val {k : ℕ} (hk : 1 ≤ k) {a b : Fin (2 * k + 1)}
    (h : (a - b).1 = 1) : a = b + 1 := by
  have h1 : a - b = 1 := by
    rcases k with _ | _
    · omega
    · exact Fin.ext h
  rw [← sub_add_cancel a b, h1]; abel

/-- Every connected finite simple graph that is neither bipartite nor isomorphic to
`cycleGraph |V|` contains a `tadpoleGraph k` (`1 ≤ k`) subgraph via an injective vertex map. -/
theorem exists_tadpole_embedding {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hConn : G.Connected) (hBip : ¬ G.IsBipartite)
    (hNotCycle : IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V))) :
    ∃ (k : ℕ) (_ : 1 ≤ k) (f : Option (Fin (2 * k + 1)) ↪ V),
      ∀ a b, (tadpoleGraph k).Adj a b → G.Adj (f a) (f b) := by
  classical
  have hex := exists_isOddCyclicWalk hConn hBip
  obtain ⟨k, ⟨c, hc⟩, hmin⟩ :
      ∃ k, (∃ c, IsOddCyclicWalk G k c) ∧ ∀ k' < k, ¬ ∃ c', IsOddCyclicWalk G k' c' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k' hk' ↦ Nat.find_min hex hk'⟩
  have hk1 : 1 ≤ k := by
    by_contra hk0
    obtain rfl : k = 0 := by omega
    exact G.loopless.irrefl (c 0) (hc 0)
  have hc_inj : Function.Injective c := by
    intro i j hij
    by_contra hne
    wlog hlt : i.1 < j.1 generalizing i j
    · have hi2 := i.2; have hj2 := j.2
      exact this hij.symm (Ne.symm hne) (by have := Fin.val_ne_of_ne hne; omega)
    have hi2 := i.2; have hj2 := j.2
    let d : ℕ := j.1 - i.1
    by_cases hd_odd : Odd d
    · have hdi : (⟨d, by omega⟩ + i : Fin (2 * k + 1)) = j := by
        ext; rw [Fin.val_add_eq_ite]; dsimp [d]; split_ifs <;> omega
      exact not_odd_loop_of_min_cyclic (isOddCyclicWalk_rotate hc i) hmin (by omega) (by omega)
        hd_odd (by rw [zero_add, hdi, hij])
    · rcases (Nat.even_or_odd d).resolve_right hd_odd with ⟨a, ha⟩
      have hdj : (⟨2 * k + 1 - d, by dsimp [d]; omega⟩ + j : Fin (2 * k + 1)) = i := by
        ext; rw [Fin.val_add_eq_ite]; dsimp [d]; split_ifs <;> omega
      exact not_odd_loop_of_min_cyclic (d := 2 * k + 1 - d) (isOddCyclicWalk_rotate hc j) hmin
        (by dsimp [d]; omega) (by dsimp [d]; omega) ⟨k - a, by dsimp [d] at ha ⊢; omega⟩
        (by rw [zero_add, hdj, hij])
  let S : Finset V := Finset.univ.map ⟨c, hc_inj⟩
  have hproper : ∃ w : V, w ∉ S := by
    by_contra hall
    have hS_univ : S = Finset.univ := Finset.eq_univ_iff_forall.mpr fun w ↦
      by_contra fun hw ↦ hall ⟨w, hw⟩
    have hcard_eq : 2 * k + 1 = Fintype.card V := by
      have hScard : S.card = 2 * k + 1 := by simp [S]
      rw [← hScard, hS_univ, Finset.card_univ]
    let e : Fin (2 * k + 1) ≃ V := Equiv.ofBijective c
      ((Fintype.bijective_iff_injective_and_card c).mpr
        ⟨hc_inj, by rw [Fintype.card_fin, hcard_eq]⟩)
    have hadj_iff : ∀ a b : Fin (2 * k + 1),
        (SimpleGraph.cycleGraph (2 * k + 1)).Adj a b ↔ G.Adj (e a) (e b) := by
      intro a b
      simp only [e, Equiv.ofBijective_apply, SimpleGraph.cycleGraph_adj']
      refine ⟨fun hab ↦ ?_, fun hab ↦ ?_⟩
      · rcases hab with h1 | h1
        · rw [fin_eq_add_one_of_sub_val hk1 h1]; exact (hc b).symm
        · rw [fin_eq_add_one_of_sub_val hk1 h1]; exact hc a
      · have hne : a ≠ b := fun h ↦ G.loopless.irrefl (c a) (h ▸ hab)
        let r : Fin (2 * k + 1) := b - a
        have hr2 := r.2
        have hr0 : r.1 ≠ 0 := fun hr ↦ hne (sub_eq_zero.mp (Fin.ext hr)).symm
        by_cases hr1 : r.1 = 1
        · exact Or.inr hr1
        · by_cases hrm : r.1 = 2 * k
          · refine Or.inl ?_
            have hab_neg : a - b = -r := by dsimp [r]; abel
            rw [hab_neg, Fin.val_neg,
              ite_eq_right_iff.mpr fun h0 ↦ (hr0 (congrArg Fin.val h0)).elim]; omega
          · by_cases h_even : Even r.1
            · have hra : (⟨r.1, r.2⟩ + a : Fin (2 * k + 1)) = b := sub_add_cancel b a
              exact (not_even_chord_of_min_cyclic (r := r.1) (isOddCyclicWalk_rotate hc a) hmin
                (by omega) (by omega) h_even
                (by change G.Adj (c (0 + a)) (c (⟨r.1, r.2⟩ + a)); simpa [hra] using hab)).elim
            · rcases Nat.not_even_iff_odd.mp h_even with ⟨m, hm⟩
              have hrb : (⟨2 * k + 1 - r.1, by omega⟩ + b : Fin (2 * k + 1)) = a := by
                have hneg : (⟨2 * k + 1 - r.1, by omega⟩ : Fin (2 * k + 1)) = -r := by
                  ext; dsimp
                  rw [Fin.val_neg, ite_eq_right_iff.mpr fun h0 ↦ (hr0 (congrArg Fin.val h0)).elim]
                rw [hneg]; dsimp [r]; abel
              exact (not_even_chord_of_min_cyclic (r := 2 * k + 1 - r.1)
                (isOddCyclicWalk_rotate hc b) hmin (by omega) (by omega) ⟨k - m, by omega⟩
                (by simpa [hrb] using hab.symm)).elim
    let iso1 : SimpleGraph.cycleGraph (2 * k + 1) ≃g G := ⟨e, fun {a b} ↦ (hadj_iff a b).symm⟩
    let iso2 : SimpleGraph.cycleGraph (2 * k + 1) ≃g
        SimpleGraph.cycleGraph (Fintype.card V) := hcard_eq ▸ SimpleGraph.Iso.refl
    exact hNotCycle.false (iso1.symm.trans iso2)
  have hSne : S.Nonempty := ⟨c 0, Finset.mem_map.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩
  obtain ⟨u, huS, z, hzS, huz⟩ := exists_adj_mem_notMem_of_connected hConn hSne hproper
  obtain ⟨r₀, _, rfl⟩ := Finset.mem_map.mp huS
  let c' : Fin (2 * k + 1) → V := fun i ↦ c (i + r₀)
  have hc' : IsOddCyclicWalk G k c' := isOddCyclicWalk_rotate hc r₀
  have hz_not : ∀ i : Fin (2 * k + 1), c' i ≠ z := fun i hiz ↦
    hzS (hiz ▸ Finset.mem_map.mpr ⟨i + r₀, Finset.mem_univ _, rfl⟩)
  let f : Option (Fin (2 * k + 1)) ↪ V :=
    { toFun := fun x ↦ match x with | none => z | some i => c' i
      inj' := by
        rintro (_ | i) (_ | j) h; · rfl
        · exact (hz_not j h.symm).elim
        · exact (hz_not i h).elim
        · exact congrArg some (add_right_cancel (hc_inj h)) }
  refine ⟨k, hk1, f, ?_⟩
  rintro (_ | i) (_ | j) hadj; · exact hadj.elim
  · subst hadj; change G.Adj z (c (0 + r₀)); simpa using huz.symm
  · subst hadj; change G.Adj (c (0 + r₀)) z; simpa using huz
  · dsimp [tadpoleGraph] at hadj; rw [SimpleGraph.cycleGraph_adj'] at hadj
    change G.Adj (c' i) (c' j)
    rcases hadj with h1 | h1
    · rw [fin_eq_add_one_of_sub_val hk1 h1]; exact (hc' j).symm
    · rw [fin_eq_add_one_of_sub_val hk1 h1]; exact hc' i

/-! ### Tadpole base case: irreducibility of `tadpoleGraph k` (`1 ≤ k`) -/

@[simp] private lemma fin_mk_eq_zero {n a : ℕ} [NeZero n] {ha : a < n} :
    (⟨a, ha⟩ : Fin n) = 0 ↔ a = 0 := by
  simp [Fin.ext_iff]

@[simp] private lemma zero_eq_fin_mk {n a : ℕ} [NeZero n] {ha : a < n} :
    (0 : Fin n) = ⟨a, ha⟩ ↔ 0 = a := by
  simp [Fin.ext_iff]

private lemma cycleGraph_adj_succ {k : ℕ} (_hk : 1 ≤ k) (j : ℕ) (hj : j + 1 < 2 * k + 1) :
    (tadpoleGraph k).Adj (some ⟨j, by omega⟩) (some ⟨j + 1, hj⟩) := by
  dsimp [tadpoleGraph]; rw [SimpleGraph.cycleGraph_adj']
  right; rw [Fin.sub_val_of_le (by simp)]; simp

private lemma cycleGraph_adj_zero_last {k : ℕ} (hk : 1 ≤ k) :
    (tadpoleGraph k).Adj (some 0) (some ⟨2 * k, by omega⟩) := by
  dsimp [tadpoleGraph]; rw [SimpleGraph.cycleGraph_adj']
  left; rw [zero_sub, Fin.val_neg, ite_eq_right_iff.mpr (by intro h; simp at h; omega)]
  dsimp; omega

private lemma tadpole_stepA_aux {k : ℕ} (hk : 1 ≤ k) (c : Bool) :
    ∀ (j : ℕ) (hj : j + 1 < 2 * k + 1) (x : Option (Fin (2 * k + 1)) → Bool),
      x (some 0) = c → x (some ⟨2 * k, by omega⟩) = !c →
      x (some ⟨j, by omega⟩) = x (some ⟨j + 1, hj⟩) →
      ∃ x' : Option (Fin (2 * k + 1)) → Bool,
        AntiVoterReach (tadpoleGraph k) x x' ∧
        x' none = c ∧ x' (some 0) = !c ∧ x' (some ⟨2 * k, by omega⟩) = !c
  | 0, hj, x, hx0, hxm, hpair => by
      let x₁ := Function.update x (some 0) (!x (some ⟨1, hj⟩))
      have hs1 : AntiVoterStepRel (tadpoleGraph k) x x₁ :=
        ⟨some 0, some ⟨1, hj⟩, cycleGraph_adj_succ hk 0 hj, rfl⟩
      have hx₁0 : x₁ (some 0) = !c := by simp [x₁, ← hpair, hx0]
      have hx₁m : x₁ (some ⟨2 * k, by omega⟩) = !c := by
        dsimp [x₁]; rw [Function.update_of_ne (by simp; omega), hxm]
      let x₂ := Function.update x₁ none (!x₁ (some 0))
      have hs2 : AntiVoterStepRel (tadpoleGraph k) x₁ x₂ := ⟨none, some 0, rfl, rfl⟩
      exact ⟨x₂, (Relation.ReflTransGen.single hs1).tail hs2,
        by simp [x₂, hx₁0], by simpa [x₂] using hx₁0, by simpa [x₂] using hx₁m⟩
  | j + 1, hj, x, hx0, hxm, hpair => by
      by_cases hprev : x (some ⟨j, by omega⟩) = x (some ⟨j + 1, by omega⟩)
      · exact tadpole_stepA_aux hk c j (by omega) x hx0 hxm hprev
      · let v : Option (Fin (2 * k + 1)) := some ⟨j + 1, by omega⟩
        let x₁ := Function.update x v (!x (some ⟨j + 2, hj⟩))
        have hs1 : AntiVoterStepRel (tadpoleGraph k) x x₁ :=
          ⟨v, some ⟨j + 2, hj⟩, cycleGraph_adj_succ hk (j + 1) hj, rfl⟩
        have hx₁_pair : x₁ (some ⟨j, by omega⟩) = x₁ v := by
          dsimp [x₁]; rw [Function.update_of_ne (by simp [v]), Function.update_self, ← hpair]
          cases hxj : x (some ⟨j, by omega⟩) <;>
            cases hxj1 : x (some ⟨j + 1, by omega⟩) <;> simp_all
        obtain ⟨x', hreach, hnone, h0, hm⟩ :=
          tadpole_stepA_aux hk c j (by omega) x₁
            (by dsimp [x₁]; rw [Function.update_of_ne (by simp [v]), hx0])
            (by dsimp [x₁]; rw [Function.update_of_ne (by simp [v]; omega), hxm])
            hx₁_pair
        exact ⟨x', Relation.ReflTransGen.head hs1 hreach, hnone, h0, hm⟩

private lemma tadpole_stepA {k : ℕ} (hk : 1 ≤ k) (x : Option (Fin (2 * k + 1)) → Bool) :
    ∃ (c : Bool) (x' : Option (Fin (2 * k + 1)) → Bool),
      AntiVoterReach (tadpoleGraph k) x x' ∧
      x' none = c ∧ x' (some 0) = !c ∧ x' (some ⟨2 * k, by omega⟩) = !c := by
  by_cases heq : x (some 0) = x (some ⟨2 * k, by omega⟩)
  · let x' := Function.update x none (!x (some 0))
    exact ⟨!x (some 0), x', Relation.ReflTransGen.single ⟨none, some 0, rfl, rfl⟩,
      by simp [x'], by simp [x'], by simp [x', ← heq]⟩
  · let c := x (some 0)
    have hxm : x (some ⟨2 * k, by omega⟩) = !c := by
      cases hx0 : x (some 0) <;> cases hxm' : x (some ⟨2 * k, by omega⟩) <;> simp_all [c]
    have hex_pair : ∃ (j : ℕ) (hj : j + 1 < 2 * k + 1),
        x (some ⟨j, by omega⟩) = x (some ⟨j + 1, hj⟩) := by
      by_contra hno
      have halt : ∀ (j : ℕ) (hj : j < 2 * k + 1),
          x (some ⟨j, hj⟩) = if Even j then c else !c := by
        intro j
        induction j with
        | zero => intro _; simp [c]
        | succ j ih =>
          intro hj
          have hneq : x (some ⟨j, by omega⟩) ≠ x (some ⟨j + 1, hj⟩) := fun h ↦ hno ⟨j, hj, h⟩
          have hj_prev := ih (by omega)
          by_cases hej : Even j
          · have hnot : ¬ Even (j + 1) := fun h ↦ (Nat.even_add_one.mp h) hej
            simp only [hej, hnot, ↓reduceIte] at hj_prev ⊢
            cases hx1 : x (some ⟨j + 1, hj⟩) <;> cases hc_val : c <;> simp_all
          · have hej1 : Even (j + 1) := Nat.even_add_one.mpr hej
            simp only [hej, hej1, ↓reduceIte] at hj_prev ⊢
            cases hx1 : x (some ⟨j + 1, hj⟩) <;> cases hc_val : c <;> simp_all
      have hlast := halt (2 * k) (by omega)
      have heven2k : Even (2 * k) := ⟨k, by omega⟩
      simp only [heven2k, ↓reduceIte] at hlast
      rw [hlast] at hxm
      cases c <;> simp at hxm
    rcases hex_pair with ⟨j, hj, hpair⟩
    obtain ⟨x', hreach, h1, h2, h3⟩ := tadpole_stepA_aux hk c j hj x rfl hxm hpair
    exact ⟨c, x', hreach, h1, h2, h3⟩

private lemma tadpole_pull_single {k : ℕ} (hk : 1 ≤ k) (c : Bool) {L : ℕ} (hL : L < 2 * k) :
    ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ L) (x : Option (Fin (2 * k + 1)) → Bool),
      x none = c → x (some ⟨2 * k, by omega⟩) = !c →
      (∀ i : ℕ, (hi : i ≤ L) → i ≠ j → x (some ⟨i, by omega⟩) = !c) →
      x (some ⟨j, by omega⟩) = c →
      ∃ x' : Option (Fin (2 * k + 1)) → Bool,
        AntiVoterReach (tadpoleGraph k) x x' ∧
        x' none = c ∧ x' (some ⟨2 * k, by omega⟩) = !c ∧
        ∀ i : ℕ, (hi : i ≤ L) → x' (some ⟨i, by omega⟩) = !c
  | 0, hj1, _, _, _, _, _, _ => by omega
  | 1, _, _, x, hnone, hxm, hother, _ => by
      let x₁ := Function.update x (some 0) (!x (some ⟨2 * k, by omega⟩))
      have hs1 : AntiVoterStepRel (tadpoleGraph k) x x₁ :=
        ⟨some 0, some ⟨2 * k, by omega⟩, cycleGraph_adj_zero_last hk, rfl⟩
      have hx₁0 : x₁ (some 0) = c := by simp [x₁, hxm]
      let x₂ := Function.update x₁ (some ⟨1, by omega⟩) (!x₁ (some 0))
      have hs2 : AntiVoterStepRel (tadpoleGraph k) x₁ x₂ :=
        ⟨some ⟨1, by omega⟩, some 0, (cycleGraph_adj_succ hk 0 (by omega)).symm, rfl⟩
      let x₃ := Function.update x₂ (some 0) (!x₂ none)
      have hs3 : AntiVoterStepRel (tadpoleGraph k) x₂ x₃ := ⟨some 0, none, rfl, rfl⟩
      refine ⟨x₃, ((Relation.ReflTransGen.single hs1).tail hs2).tail hs3,
        by simp [x₃, x₂, x₁, hnone], ?_, fun i hi ↦ ?_⟩
      · dsimp [x₃, x₂, x₁]
        rw [Function.update_of_ne (by simp; omega), Function.update_of_ne (by simp),
          Function.update_of_ne (by simp; omega), hxm]
      · by_cases hi0 : i = 0; · subst hi0; simp [x₃, x₂, x₁, hnone]
        by_cases hi1 : i = 1
        · subst hi1; dsimp [x₃, x₂]
          rw [Function.update_of_ne (by simp), Function.update_self, hx₁0]
        · dsimp [x₃, x₂, x₁]
          rw [Function.update_of_ne (by simp [hi0]), Function.update_of_ne (by simp [hi1]),
            Function.update_of_ne (by simp [hi0]), hother i hi hi1]
  | j + 2, _, hjL, x, hnone, hxm, hother, hjc => by
      have hj0 : x (some ⟨j, by omega⟩) = !c := hother j (by omega) (by omega)
      let x₁ := Function.update x (some ⟨j + 1, by omega⟩) (!x (some ⟨j, by omega⟩))
      have hs1 : AntiVoterStepRel (tadpoleGraph k) x x₁ :=
        ⟨some ⟨j + 1, by omega⟩, some ⟨j, by omega⟩,
          (cycleGraph_adj_succ hk j (by omega)).symm, rfl⟩
      have hx₁_j1 : x₁ (some ⟨j + 1, by omega⟩) = c := by simp [x₁, hj0]
      let x₂ := Function.update x₁ (some ⟨j + 2, by omega⟩) (!x₁ (some ⟨j + 1, by omega⟩))
      have hs2 : AntiVoterStepRel (tadpoleGraph k) x₁ x₂ :=
        ⟨some ⟨j + 2, by omega⟩, some ⟨j + 1, by omega⟩,
          (cycleGraph_adj_succ hk (j + 1) (by omega)).symm, rfl⟩
      have hnone2 : x₂ none = c := by simp [x₂, x₁, hnone]
      have hxm2 : x₂ (some ⟨2 * k, by omega⟩) = !c := by
        dsimp [x₂, x₁]
        rw [Function.update_of_ne (by simp; omega), Function.update_of_ne (by simp; omega), hxm]
      have hother2 : ∀ i : ℕ, (hi : i ≤ L) → i ≠ j + 1 → x₂ (some ⟨i, by omega⟩) = !c := by
        intro i hi hij1
        by_cases hij2 : i = j + 2; · subst hij2; simp [x₂, hx₁_j1]
        dsimp [x₂, x₁]
        rw [Function.update_of_ne (by simp [hij2]), Function.update_of_ne (by simp [hij1]),
          hother i hi hij2]
      have hjc2 : x₂ (some ⟨j + 1, by omega⟩) = c := by
        dsimp [x₂]; rw [Function.update_of_ne (by simp), hx₁_j1]
      obtain ⟨x', hreach, hn', hm', hall'⟩ :=
        tadpole_pull_single hk c hL (j + 1) (by omega) (by omega) x₂ hnone2 hxm2 hother2 hjc2
      exact ⟨x', ((Relation.ReflTransGen.single hs1).tail hs2).trans hreach, hn', hm', hall'⟩

private lemma tadpole_stepB {k : ℕ} (hk : 1 ≤ k) (c : Bool)
    (x : Option (Fin (2 * k + 1)) → Bool)
    (hnone : x none = c) (hx0 : x (some 0) = !c) (hxm : x (some ⟨2 * k, by omega⟩) = !c) :
    AntiVoterReach (tadpoleGraph k) x (fun w ↦ if w = none then c else !c) := by
  have hpref : ∀ (L : ℕ) (hL : L ≤ 2 * k),
      ∃ x' : Option (Fin (2 * k + 1)) → Bool,
        AntiVoterReach (tadpoleGraph k) x x' ∧
        x' none = c ∧ x' (some ⟨2 * k, by omega⟩) = !c ∧
        ∀ i : ℕ, (hi : i < L) → x' (some ⟨i, by omega⟩) = !c := by
    intro L
    induction L with
    | zero => intro _; exact ⟨x, .refl, hnone, hxm, fun _ hi ↦ (Nat.not_lt_zero _ hi).elim⟩
    | succ L ih =>
      intro hL1
      obtain ⟨x₁, hr1, hn1, hm1, hall1⟩ := ih (by omega)
      by_cases hL0 : L = 0
      · subst hL0
        refine ⟨x, .refl, hnone, hxm, fun i hi ↦ ?_⟩
        obtain rfl : i = 0 := by omega
        exact hx0
      · by_cases hx₁L : x₁ (some ⟨L, by omega⟩) = !c
        · refine ⟨x₁, hr1, hn1, hm1, fun i hi ↦ ?_⟩
          by_cases hiL : i = L; · exact hiL ▸ hx₁L
          exact hall1 i (by omega)
        · have hx₁L_c : x₁ (some ⟨L, by omega⟩) = c := by
            cases hval : x₁ (some ⟨L, by omega⟩) <;> cases c <;> simp_all
          obtain ⟨x₂, hr2, hn2, hm2, hall2⟩ :=
            tadpole_pull_single hk c (L := L) (by omega) L (by omega) le_rfl x₁ hn1 hm1
              (fun i hi hne ↦ hall1 i (by omega)) hx₁L_c
          exact ⟨x₂, hr1.trans hr2, hn2, hm2, fun i hi ↦ hall2 i (by omega)⟩
  obtain ⟨x', hreach, hn', hm', hall'⟩ := hpref (2 * k) le_rfl
  have heq : x' = fun w ↦ if w = none then c else !c := by
    ext (_ | ⟨i, hi⟩); · simp [hn']
    by_cases him : i = 2 * k; · subst him; simpa using hm'
    simpa using hall' i (by omega)
  exact heq ▸ hreach

private def singletonLabeling {α : Type*} [DecidableEq α] (a : α) : α → Bool :=
  fun w ↦ decide (w = a)

private lemma tadpole_reach_singleton_none {k : ℕ} (hk : 1 ≤ k)
    (x : Option (Fin (2 * k + 1)) → Bool) :
    AntiVoterReach (tadpoleGraph k) x (singletonLabeling none) := by
  obtain ⟨c, x₁, hreach1, hnone1, hx01, hxm1⟩ := tadpole_stepA hk x
  have hreach2 := tadpole_stepB hk c x₁ hnone1 hx01 hxm1
  cases c with
  | true =>
    have heq : (fun w : Option (Fin (2 * k + 1)) ↦ if w = none then true else !true) =
        singletonLabeling none := by ext (_ | _) <;> simp [singletonLabeling]
    exact hreach1.trans (heq ▸ hreach2)
  | false =>
    let y₀ : Option (Fin (2 * k + 1)) → Bool := fun w ↦ if w = none then false else true
    have hreach12 : AntiVoterReach (tadpoleGraph k) x y₀ := hreach1.trans hreach2
    let y₁ := Function.update y₀ (some 0) (!y₀ (some ⟨1, by omega⟩))
    have hs1 : AntiVoterStepRel (tadpoleGraph k) y₀ y₁ :=
      ⟨some 0, some ⟨1, by omega⟩, cycleGraph_adj_succ hk 0 (by omega), rfl⟩
    let y₂ := Function.update y₁ none (!y₁ (some 0))
    have hs2 : AntiVoterStepRel (tadpoleGraph k) y₁ y₂ := ⟨none, some 0, rfl, rfl⟩
    let y₃ := Function.update y₂ (some ⟨2 * k, by omega⟩) (!y₂ (some ⟨2 * k - 1, by omega⟩))
    have hs3 : AntiVoterStepRel (tadpoleGraph k) y₂ y₃ := by
      have hsucc : (⟨2 * k, by omega⟩ : Fin (2 * k + 1)) = ⟨(2 * k - 1) + 1, by omega⟩ := by
        ext; dsimp; omega
      exact ⟨some ⟨2 * k, by omega⟩, some ⟨2 * k - 1, by omega⟩,
        hsucc ▸ (cycleGraph_adj_succ hk (2 * k - 1) (by omega)).symm, rfl⟩
    have hy₃_none : y₃ none = true := by simp [y₃, y₂, y₁, y₀]
    have hy₃_0 : y₃ (some 0) = false := by
      dsimp [y₃, y₂, y₁]
      rw [Function.update_of_ne (by simp; omega), Function.update_of_ne (by simp),
        Function.update_self]; simp [y₀]
    have hy₃_m : y₃ (some ⟨2 * k, by omega⟩) = false := by
      dsimp [y₃, y₂, y₁]
      rw [Function.update_self, Function.update_of_ne (by simp),
        Function.update_of_ne (by simp; omega)]; simp [y₀]
    have hreach3 := tadpole_stepB hk true y₃ hy₃_none hy₃_0 hy₃_m
    have heq : (fun w : Option (Fin (2 * k + 1)) ↦ if w = none then true else !true) =
        singletonLabeling none := by ext (_ | _) <;> simp [singletonLabeling]
    exact (((hreach12.tail hs1).tail hs2).tail hs3).trans (heq ▸ hreach3)

private lemma reach_singleton_step {α : Type*} [DecidableEq α] {H : SimpleGraph α}
    {u v w : α} (huv : H.Adj u v) (hvw : H.Adj v w) (huw : u ≠ w) :
    AntiVoterReach H (singletonLabeling u) (singletonLabeling v) := by
  let s₁ := Function.update (singletonLabeling u) v (!(singletonLabeling u w))
  have hs1 : AntiVoterStepRel H (singletonLabeling u) s₁ := ⟨v, w, hvw, rfl⟩
  have hs₁v : s₁ v = true := by simp [s₁, singletonLabeling, huw.symm]
  let s₂ := Function.update s₁ u (!s₁ v)
  have hs2 : AntiVoterStepRel H s₁ s₂ := ⟨u, v, huv, rfl⟩
  have heq : s₂ = singletonLabeling v := by
    ext z; by_cases hzv : z = v
    · subst hzv; simp [s₂, Function.update_of_ne huv.ne', hs₁v, singletonLabeling]
    by_cases hzu : z = u
    · subst hzu; simp [s₂, hs₁v, singletonLabeling, huv.ne]
    · simp [s₂, s₁, hzv, hzu, singletonLabeling]
  exact heq ▸ (Relation.ReflTransGen.single hs1).tail hs2

private lemma tadpole_singleton_none_reach_all {k : ℕ} (hk : 1 ≤ k)
    (w : Option (Fin (2 * k + 1))) :
    AntiVoterReach (tadpoleGraph k) (singletonLabeling none) (singletonLabeling w) := by
  have h0 : AntiVoterReach (tadpoleGraph k) (singletonLabeling none)
      (singletonLabeling (some 0)) :=
    reach_singleton_step rfl (cycleGraph_adj_succ hk 0 (by omega)) (by simp)
  rcases w with _ | ⟨j, hj⟩; · exact .refl
  induction j with
  | zero => exact h0
  | succ j ih =>
    let w_next : Fin (2 * k + 1) := ⟨(j + 2) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩
    have hadj2 : (tadpoleGraph k).Adj (some ⟨j + 1, hj⟩) (some w_next) := by
      by_cases hj2 : j + 2 < 2 * k + 1
      · exact (Fin.ext (Nat.mod_eq_of_lt hj2) : w_next = ⟨j + 2, hj2⟩) ▸
          cycleGraph_adj_succ hk (j + 1) hj2
      · have hw : w_next = 0 := by
          ext; dsimp [w_next]; rw [(by omega : j + 2 = 2 * k + 1), Nat.mod_self]
        have hv : (⟨j + 1, hj⟩ : Fin (2 * k + 1)) = ⟨2 * k, by omega⟩ := by ext; dsimp; omega
        exact hw ▸ hv ▸ (cycleGraph_adj_zero_last hk).symm
    have hne : (some (⟨j, by omega⟩ : Fin (2 * k + 1))) ≠ some w_next := fun h ↦ by
      have hval : j = (j + 2) % (2 * k + 1) := congrArg Fin.val (Option.some.inj h)
      by_cases hj2 : j + 2 < 2 * k + 1
      · rw [Nat.mod_eq_of_lt hj2] at hval; omega
      · rw [(by omega : j + 2 = 2 * k + 1), Nat.mod_self] at hval; omega
    exact (ih (by omega)).trans (reach_singleton_step (cycleGraph_adj_succ hk j hj) hadj2 hne)

private lemma exists_singleton_reach_of_connected {α : Type*} [Finite α] [DecidableEq α]
    {H : SimpleGraph α} (hConn : H.Connected) {y : α → Bool} (hy : IsNonConstLabeling y) :
    ∃ w : α, AntiVoterReach H (singletonLabeling w) y := by
  cases nonempty_fintype α
  suffices ∀ (n : ℕ) (y : α → Bool),
      (Finset.univ.filter fun a : α ↦ y a = true).card = n → IsNonConstLabeling y →
      ∃ w : α, AntiVoterReach H (singletonLabeling w) y from this _ y rfl hy
  intro n; induction n with
  | zero =>
    intro y hcard ⟨⟨a, ha⟩, _⟩
    have hpos : 0 < (Finset.univ.filter fun z : α ↦ y z = true).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
    omega
  | succ m ih =>
    intro y hcard hy_nc
    let T : Finset α := Finset.univ.filter fun a : α ↦ y a = true
    have hT_card : T.card = m + 1 := hcard
    by_cases hm0 : m = 0
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (by omega : T.card = 1)
      have heq : y = singletonLabeling w := by
        ext z
        by_cases hzw : z = w
        · subst hzw; have hzT : z ∈ T := hw ▸ Finset.mem_singleton_self z
          simpa [singletonLabeling] using (Finset.mem_filter.mp hzT).2
        · have hnot : z ∉ T := by rw [hw, Finset.mem_singleton]; exact hzw
          have hyz : y z ≠ true := fun h ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h⟩)
          cases hyz' : y z <;> simp_all [singletonLabeling]
      exact ⟨w, heq ▸ .refl⟩
    · have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
      rcases hy_nc.2 with ⟨b, hb⟩
      obtain ⟨v, hvT, u, huT, hvu⟩ :=
        exists_adj_mem_notMem_of_connected hConn hT_ne ⟨b, by simp [T, hb]⟩
      have hyv : y v = true := (Finset.mem_filter.mp hvT).2
      have hyu : y u = false := by
        have hnot : y u ≠ true := fun h ↦ huT (Finset.mem_filter.mpr ⟨Finset.mem_univ u, h⟩)
        cases hyu' : y u <;> simp_all
      let y' := Function.update y v false
      have hcard' : (Finset.univ.filter fun a : α ↦ y' a = true).card = m := by
        have hfilter : (Finset.univ.filter fun a : α ↦ y' a = true) = T.erase v := by
          ext z; by_cases hzv : z = v <;> simp [y', T, hzv]
        rw [hfilter, Finset.card_erase_of_mem hvT]; dsimp [T]; omega
      obtain ⟨a', ha'⟩ := Finset.card_pos.mp
        (by omega : 0 < (Finset.univ.filter fun a : α ↦ y' a = true).card)
      have hy'_nc : IsNonConstLabeling y' :=
        ⟨⟨a', (Finset.mem_filter.mp ha').2⟩, ⟨v, by simp [y']⟩⟩
      have hs : AntiVoterStepRel H y' y := ⟨v, u, hvu, by
        ext z; by_cases hzv : z = v; · subst hzv; simp [y', Function.update_of_ne hvu.ne', hyu, hyv]
        simp [y', Function.update_of_ne hzv]⟩
      obtain ⟨w, hreach⟩ := ih y' hcard' hy'_nc
      exact ⟨w, hreach.tail hs⟩

private lemma tadpole_irreducible {k : ℕ} (hk : 1 ≤ k)
    {x y : Option (Fin (2 * k + 1)) → Bool} (hy : IsNonConstLabeling y) :
    AntiVoterReach (tadpoleGraph k) x y := by
  obtain ⟨w, hw⟩ := exists_singleton_reach_of_connected tadpoleGraph_connected hy
  exact ((tadpole_reach_singleton_none hk x).trans (tadpole_singleton_none_reach_all hk w)).trans hw

/-! ### Subset-restricted reachability and pendant-vertex induction -/

private def NonConstOn {V : Type*} (S : Finset V) (x : V → Bool) : Prop :=
  (∃ a ∈ S, x a = true) ∧ (∃ b ∈ S, x b = false)

private def AVStepOn {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (x y : V → Bool) : Prop :=
  ∃ v ∈ S, ∃ u ∈ S, G.Adj v u ∧ y = Function.update x v (!x u)

private abbrev AVReachOn {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    (V → Bool) → (V → Bool) → Prop :=
  Relation.ReflTransGen (AVStepOn G S)

private lemma avReachOn_mono {V : Type*} [DecidableEq V] {G : SimpleGraph V} {S T : Finset V}
    (hST : S ⊆ T) {x y : V → Bool} (h : AVReachOn G S x y) : AVReachOn G T x y := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with ⟨v, hv, u, hu, hadj, rfl⟩; exact ih.tail ⟨v, hST hv, u, hST hu, hadj, rfl⟩

private lemma avReachOn_lift_tadpole {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    (f : Option (Fin (2 * k + 1)) ↪ V)
    (hf : ∀ a b, (tadpoleGraph k).Adj a b → G.Adj (f a) (f b))
    {p₀ q₀ : Option (Fin (2 * k + 1)) → Bool}
    (h : AntiVoterReach (tadpoleGraph k) p₀ q₀) :
    ∀ x : V → Bool, x ∘ f = p₀ →
      ∃ y' : V → Bool, AVReachOn G (Finset.univ.map f) x y' ∧ y' ∘ f = q₀ ∧
        ∀ w ∉ Finset.univ.map f, y' w = x w := by
  induction h with
  | refl => intro x hx; exact ⟨x, .refl, hx, fun _ _ ↦ rfl⟩
  | tail _ hs ih =>
    intro x hx; obtain ⟨y₁, hreach₁, hy₁f, hy₁out⟩ := ih x hx
    rcases hs with ⟨a, b, hadj, rfl⟩
    let y₂ := Function.update y₁ (f a) (!y₁ (f b))
    have hsOn : AVStepOn G (Finset.univ.map f) y₁ y₂ :=
      ⟨f a, Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩,
       f b, Finset.mem_map.mpr ⟨b, Finset.mem_univ b, rfl⟩, hf a b hadj, rfl⟩
    refine ⟨y₂, hreach₁.tail hsOn, ?_, fun w hw ↦ ?_⟩
    · have hy₁_app (u) : y₁ (f u) = _ := congrFun hy₁f u
      ext t; by_cases hta : t = a; · subst hta; simp [y₂, hy₁_app b]
      simp [y₂, hy₁_app t, hta]
    · have hne : w ≠ f a := fun h ↦ hw (h ▸ Finset.mem_map.mpr ⟨a, Finset.mem_univ a, rfl⟩)
      simp [y₂, Function.update_of_ne hne, hy₁out w hw]

private lemma irreducibleOn_tadpole_image {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {k : ℕ} (hk : 1 ≤ k) (f : Option (Fin (2 * k + 1)) ↪ V)
    (hf : ∀ a b, (tadpoleGraph k).Adj a b → G.Adj (f a) (f b))
    {x y : V → Bool} (hout : ∀ w ∉ Finset.univ.map f, x w = y w)
    (hy : NonConstOn (Finset.univ.map f) y) :
    AVReachOn G (Finset.univ.map f) x y := by
  have hy₀ : IsNonConstLabeling (y ∘ f) := by
    rcases hy with ⟨⟨a, ha, hya⟩, ⟨b, hb, hyb⟩⟩
    obtain ⟨a₀, _, rfl⟩ := Finset.mem_map.mp ha; obtain ⟨b₀, _, rfl⟩ := Finset.mem_map.mp hb
    exact ⟨⟨a₀, hya⟩, ⟨b₀, hyb⟩⟩
  obtain ⟨y', hreach, hy'f, hy'out⟩ :=
    avReachOn_lift_tadpole f hf (tadpole_irreducible hk (x := x ∘ f) hy₀) x rfl
  have hy'_eq : y' = y := by
    ext w; by_cases hw : w ∈ Finset.univ.map f
    · obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hw; exact congrFun hy'f t
    · rw [hy'out w hw, hout w hw]
  exact hy'_eq ▸ hreach

private lemma irreducibleOn_insert {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {S : Finset V} (hEdge : ∃ a ∈ S, ∃ b ∈ S, G.Adj a b)
    (hIH : ∀ x y : V → Bool, (∀ w ∉ S, x w = y w) → NonConstOn S y → AVReachOn G S x y)
    {v₀ z : V} (hv₀ : v₀ ∈ S) (hz : z ∉ S) (hv₀z : G.Adj v₀ z)
    {x y : V → Bool} (hout : ∀ w ∉ insert z S, x w = y w)
    (hy : NonConstOn (insert z S) y) :
    AVReachOn G (insert z S) x y := by
  rcases hEdge with ⟨a₀, ha₀, b₀, hb₀, hab₀⟩
  obtain ⟨u₁, hu₁S, hu₁_ne⟩ : ∃ u₁ ∈ S, u₁ ≠ v₀ :=
    if hav : a₀ = v₀ then ⟨b₀, hb₀, hav ▸ hab₀.ne'⟩ else ⟨a₀, ha₀, hav⟩
  have mk_nc (c : Bool) (base : V → Bool) :
      NonConstOn S (fun u ↦ if u ∈ S then (if u = v₀ then c else !c) else base u) := by
    cases c
    · exact ⟨⟨u₁, hu₁S, by simp [hu₁S, hu₁_ne]⟩, ⟨v₀, hv₀, by simp [hv₀]⟩⟩
    · exact ⟨⟨v₀, hv₀, by simp [hv₀]⟩, ⟨u₁, hu₁S, by simp [hu₁S, hu₁_ne]⟩⟩
  by_cases hyS : NonConstOn S y
  · let w₀ : V → Bool := fun u ↦ if u ∈ S then (if u = v₀ then !y z else y z) else x u
    have hr1 : AVReachOn G (insert z S) x w₀ := avReachOn_mono (Finset.subset_insert z S)
      (hIH x w₀ (fun u hu ↦ by simp [w₀, hu]) (by simpa [w₀] using mk_nc (!y z) x))
    let w₁ : V → Bool := Function.update w₀ z (!w₀ v₀)
    have hs2 : AVStepOn G (insert z S) w₀ w₁ :=
      ⟨z, Finset.mem_insert_self z S, v₀, Finset.mem_insert_of_mem hv₀, hv₀z.symm, rfl⟩
    have hw₁_out : ∀ u ∉ S, w₁ u = y u := fun u hu ↦ by
      by_cases huz : u = z; · subst huz; simp [w₁, w₀, hv₀]
      simp [w₁, w₀, Function.update_of_ne huz, hu, hout u (by simp [huz, hu])]
    exact (hr1.tail hs2).trans (avReachOn_mono (Finset.subset_insert z S) (hIH w₁ y hw₁_out hyS))
  · let c : Bool := y v₀
    have hy_const_S : ∀ u ∈ S, y u = c := fun u hu ↦ by
      by_contra hne; cases hc_val : c <;> cases hyu : y u
      · exact hne (hyu.trans hc_val.symm)
      · exact hyS ⟨⟨u, hu, hyu⟩, ⟨v₀, hv₀, hc_val⟩⟩
      · exact hyS ⟨⟨v₀, hv₀, hc_val⟩, ⟨u, hu, hyu⟩⟩
      · exact hne (hyu.trans hc_val.symm)
    have hyz : y z = !c := by
      rcases hy with ⟨⟨a, ha, hya⟩, ⟨b, hb, hyb⟩⟩; cases hc_val : c
      · rcases Finset.mem_insert.mp ha with rfl | haS; · simpa [hc_val] using hya
        cases hc_val.symm.trans ((hy_const_S a haS).symm.trans hya)
      · rcases Finset.mem_insert.mp hb with rfl | hbS; · simpa [hc_val] using hyb
        cases hc_val.symm.trans ((hy_const_S b hbS).symm.trans hyb)
    let w₀ : V → Bool := fun u ↦ if u ∈ S then (if u = v₀ then c else !c) else x u
    have hr1 : AVReachOn G (insert z S) x w₀ := avReachOn_mono (Finset.subset_insert z S)
      (hIH x w₀ (fun u hu ↦ by simp [w₀, hu]) (mk_nc c x))
    let w₁ : V → Bool := Function.update w₀ z (!w₀ v₀)
    have hs2 : AVStepOn G (insert z S) w₀ w₁ :=
      ⟨z, Finset.mem_insert_self z S, v₀, Finset.mem_insert_of_mem hv₀, hv₀z.symm, rfl⟩
    have hw₁_out : ∀ u ∉ S, w₁ u = y u := fun u hu ↦ by
      by_cases huz : u = z; · subst huz; simp [w₁, w₀, hv₀, hyz]
      simp [w₁, w₀, Function.update_of_ne huz, hu, hout u (by simp [huz, hu])]
    let w₂ : V → Bool := fun u ↦ if u ∈ S then (if u = v₀ then !c else c) else y u
    have hr3 : AVReachOn G (insert z S) w₁ w₂ := avReachOn_mono (Finset.subset_insert z S)
      (hIH w₁ w₂ (fun u hu ↦ by simp [w₂, hu, hw₁_out u hu]) (by simpa [w₂] using mk_nc (!c) y))
    let w₃ : V → Bool := Function.update w₂ v₀ (!w₂ z)
    have hs4 : AVStepOn G (insert z S) w₂ w₃ :=
      ⟨v₀, Finset.mem_insert_of_mem hv₀, z, Finset.mem_insert_self z S, hv₀z, rfl⟩
    have hw₃_eq : w₃ = y := by
      ext u; by_cases huv₀ : u = v₀; · subst huv₀; simp [w₃, w₂, hz, hyz, c]
      by_cases huS : u ∈ S <;> simp [w₃, w₂, huS, huv₀, hy_const_S]
    exact hw₃_eq ▸ ((hr1.tail hs2).trans hr3).tail hs4

/-- **Combinatorial irreducibility of the anti-voter chain on non-constant labelings**
(`SteinIntro.tex:1110-1111`, citing Aldous–Fill `[af10]`; `ISSUE-3.8`): if `G` is a connected
finite simple graph that is neither bipartite nor isomorphic to `cycleGraph |V|`, then every
configuration `x : V → Bool` reaches every non-constant configuration `y : V → Bool` under
`AntiVoterReach G`. -/
theorem antiVoter_irreducible_on_nonconst {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hConn : G.Connected) (hBip : ¬ G.IsBipartite)
    (hNotCycle : IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)))
    {x y : V → Bool} (hy : IsNonConstLabeling y) :
    AntiVoterReach G x y := by
  obtain ⟨k, hk1, f, hf⟩ := exists_tadpole_embedding G hConn hBip hNotCycle
  let S₀ : Finset V := Finset.univ.map f
  have hEdge₀ : ∃ a ∈ S₀, ∃ b ∈ S₀, G.Adj a b :=
    ⟨f none, Finset.mem_map.mpr ⟨none, Finset.mem_univ _, rfl⟩,
     f (some 0), Finset.mem_map.mpr ⟨some 0, Finset.mem_univ _, rfl⟩, hf none (some 0) rfl⟩
  have hBase : ∀ p q : V → Bool, (∀ w ∉ S₀, p w = q w) → NonConstOn S₀ q → AVReachOn G S₀ p q :=
    fun _ _ hout hq ↦ irreducibleOn_tadpole_image hk1 f hf hout hq
  suffices ∀ (d : ℕ) (S : Finset V), Fintype.card V - S.card = d →
      (∃ a ∈ S, ∃ b ∈ S, G.Adj a b) →
      (∀ p q : V → Bool, (∀ w ∉ S, p w = q w) → NonConstOn S q → AVReachOn G S p q) →
      AVReachOn G Finset.univ x y by
    have h_univ := this (Fintype.card V - S₀.card) S₀ rfl hEdge₀ hBase
    clear hy hBase hEdge₀ this
    induction h_univ with
    | refl => exact .refl
    | tail _ hs ih => rcases hs with ⟨v, _, u, _, hadj, rfl⟩; exact ih.tail ⟨v, u, hadj, rfl⟩
  intro d; induction d with
  | zero =>
    intro S hd _ hS
    obtain rfl : S = Finset.univ := Finset.eq_univ_of_card S (by have := S.card_le_univ; omega)
    rcases hy with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact hS x y (fun _ hw ↦ (hw (Finset.mem_univ _)).elim)
      ⟨⟨a, Finset.mem_univ a, ha⟩, ⟨b, Finset.mem_univ b, hb⟩⟩
  | succ d ih =>
    intro S hd hEdge hS
    have hSne : S.Nonempty := by rcases hEdge with ⟨a, ha, _⟩; exact ⟨a, ha⟩
    have hproper : ∃ w : V, w ∉ S := by
      by_contra hall
      have hS_univ : S = Finset.univ := Finset.eq_univ_iff_forall.mpr fun w ↦
        by_contra fun hw ↦ hall ⟨w, hw⟩
      rw [hS_univ, Finset.card_univ] at hd; omega
    obtain ⟨v₀, hv₀, z, hz, hv₀z⟩ := exists_adj_mem_notMem_of_connected hConn hSne hproper
    have hd' : Fintype.card V - (insert z S).card = d := by
      rw [Finset.card_insert_of_notMem hz]; have := S.card_le_univ; omega
    exact ih (insert z S) hd'
      ⟨v₀, Finset.mem_insert_of_mem hv₀, z, Finset.mem_insert_self z S, hv₀z⟩
      (fun _ _ hout hq ↦ irreducibleOn_insert hEdge hS hv₀ hz hv₀z hout hq)

end SteinMethod
