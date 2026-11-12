/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.AntiVoter
import Formalization.Exchangeable.AntiVoterUnique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Non-Reversibility of the Anti-Voter Chain (`Formalization.Sweep.SweepBAntiVoter`)

Proves `Sec3_3_1_antiVoter_not_reversible` from Section 3.3.1 of Nathan Ross,
*"Fundamentals of Stein's method"* (`SteinIntro.tex:1130-1131`):
there exists a finite connected 3-regular simple graph $G$ (witnessed by the 3-regular triangular
prism $K_3 \square K_2$ on `Fin 6`) that is non-bipartite and not isomorphic to `cycleGraph 6`
such that the anti-voter Markov chain has a stationary probability measure, and *every*
stationary probability measure $\mu$ violates detailed balance at some pair of configurations.
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-- Adjacency predicate for the 3-regular triangular prism $K_3 \square K_2$ on `Fin 6`.
Vertices 0, 1, 2 form the first triangle; 3, 4, 5 form the second triangle;
and {0, 3}, {1, 4}, {2, 5} are the three matching edges. -/
def prismAdjBool (i j : Fin 6) : Bool :=
  (decide (i.1 < 3) && decide (j.1 < 3) && decide (i ≠ j)) ||
  (decide (3 ≤ i.1) && decide (3 ≤ j.1) && decide (i ≠ j)) ||
  (decide (i.1 + 3 = j.1) || decide (j.1 + 3 = i.1))

/-- The 3-regular triangular prism $K_3 \square K_2$ as a `SimpleGraph (Fin 6)`. -/
def prismGraph : SimpleGraph (Fin 6) where
  Adj i j := prismAdjBool i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel prismGraph.Adj :=
  fun i j ↦ inferInstanceAs (Decidable (prismAdjBool i j = true))

lemma prismGraph_isRegular : prismGraph.IsRegularOfDegree 3 := by
  intro v
  fin_cases v <;> decide

lemma prismGraph_connected : prismGraph.Connected := by
  refine ⟨fun a b ↦ ?_⟩
  have h0 : ∀ v : Fin 6, prismGraph.Reachable 0 v := by
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.refl 0
    · exact SimpleGraph.Adj.reachable (by decide : prismGraph.Adj 0 1)
    · exact SimpleGraph.Adj.reachable (by decide : prismGraph.Adj 0 2)
    · exact SimpleGraph.Adj.reachable (by decide : prismGraph.Adj 0 3)
    · have h03 : prismGraph.Reachable 0 3 := SimpleGraph.Adj.reachable (by decide)
      have h34 : prismGraph.Reachable 3 4 := SimpleGraph.Adj.reachable (by decide)
      exact h03.trans h34
    · have h03 : prismGraph.Reachable 0 3 := SimpleGraph.Adj.reachable (by decide)
      have h35 : prismGraph.Reachable 3 5 := SimpleGraph.Adj.reachable (by decide)
      exact h03.trans h35
  exact (h0 a).symm.trans (h0 b)

lemma prismGraph_not_bipartite : ¬ prismGraph.IsBipartite := by
  rintro ⟨col⟩
  have h01 : (col 0).1 ≠ (col 1).1 := Fin.val_ne_of_ne (col.valid (by decide))
  have h12 : (col 1).1 ≠ (col 2).1 := Fin.val_ne_of_ne (col.valid (by decide))
  have h02 : (col 0).1 ≠ (col 2).1 := Fin.val_ne_of_ne (col.valid (by decide))
  have := (col 0).2; have := (col 1).2; have := (col 2).2
  omega

lemma prismGraph_not_cycle :
    IsEmpty (prismGraph ≃g SimpleGraph.cycleGraph (Fintype.card (Fin 6))) := by
  refine ⟨fun φ ↦ ?_⟩
  have hcard : Fintype.card (Fin 6) = 6 := Fintype.card_fin 6
  let ψ : prismGraph ≃g SimpleGraph.cycleGraph 6 :=
    φ.trans (hcard ▸ SimpleGraph.Iso.refl)
  have htri : ∀ a b c : Fin 6,
      ¬ ((SimpleGraph.cycleGraph 6).Adj a b ∧
         (SimpleGraph.cycleGraph 6).Adj b c ∧
         (SimpleGraph.cycleGraph 6).Adj a c) := by decide
  exact htri (ψ 0) (ψ 1) (ψ 2)
    ⟨ψ.map_rel_iff.mpr (by decide), ψ.map_rel_iff.mpr (by decide), ψ.map_rel_iff.mpr (by decide)⟩

theorem sec3_3_1_antiVoter_not_reversible_proof :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj) (r : ℕ),
      G.IsRegularOfDegree r ∧
      G.Connected ∧
      ¬ G.IsBipartite ∧
      IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) ∧
      (∃ μ : Measure (V → Bool), IsProbabilityMeasure μ ∧ IsAntiVoterStationary G μ) ∧
      (∀ μ : Measure (V → Bool),
        IsProbabilityMeasure μ →
        IsAntiVoterStationary G μ →
        ∃ x y : V → Bool,
          μ {x} * antiVoterStep G x y ≠ μ {y} * antiVoterStep G y x) := by
  refine ⟨Fin 6, inferInstance, inferInstance, prismGraph, inferInstance, 3,
    prismGraph_isRegular, prismGraph_connected, prismGraph_not_bipartite, prismGraph_not_cycle, ?_⟩
  obtain ⟨_, ν, hν_prob, hν_stat, hν_supp, hν_uniq⟩ :=
    antiVoter_ergodic_and_unique_stationary prismGraph
      prismGraph_connected prismGraph_not_bipartite prismGraph_not_cycle
  refine ⟨⟨ν, hν_prob, hν_stat⟩, fun μ hμ_prob hμ_stat ↦ ?_⟩
  have hμ_eq_ν : μ = ν := hν_uniq μ hμ_prob hμ_stat
  -- Witness states: x has only vertex 4 true, y has vertices 0 and 4 true.
  let x : Fin 6 → Bool := ![false, false, false, false, true, false]
  let y : Fin 6 → Bool := ![true, false, false, false, true, false]
  have hx_nc : (∃ a : Fin 6, x a = true) ∧ (∃ b : Fin 6, x b = false) :=
    ⟨⟨4, rfl⟩, ⟨0, rfl⟩⟩
  have hx_pos : μ {x} ≠ 0 := by
    rw [hμ_eq_ν]
    exact (hν_supp x).mpr hx_nc
  have hV_ne : (Finset.univ : Finset (Fin 6)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hN_ne : ∀ v : Fin 6, (prismGraph.neighborFinset v).Nonempty := fun v ↦ by
    rw [← Finset.card_pos, prismGraph.card_neighborFinset_eq_degree, prismGraph_isRegular v]
    omega
  have hxy_step : antiVoterStep prismGraph x y ≠ 0 := by
    rw [antiVoterStep_ne_zero_iff prismGraph hV_ne hN_ne]
    exact ⟨0, 1, by decide, by ext i; fin_cases i <;> rfl⟩
  have hyx_step : antiVoterStep prismGraph y x = 0 := by
    by_contra hne
    have hrel : AntiVoterStepRel prismGraph y x :=
      (antiVoterStep_ne_zero_iff prismGraph hV_ne hN_ne y x).mp hne
    rcases hrel with ⟨v, u, hadj, heq⟩
    fin_cases v <;> fin_cases u <;> revert hadj heq <;> decide
  refine ⟨x, y, ?_⟩
  have hL : μ {x} * antiVoterStep prismGraph x y ≠ 0 := mul_ne_zero hx_pos hxy_step
  rw [hyx_step, mul_zero]
  exact hL

end SteinMethod
