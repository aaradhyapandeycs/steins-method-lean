/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Sweep.SweepBSteinPair
import Formalization.Sweep.SweepBAntiVoter
import Formalization.Sweep.SweepBZeroBias

/-!
# Track SWEEP-B Formalization Theorems

Proves the four approved formalization entries for Track SWEEP-B (`docs/tracks/SWEEP-B.md`):
1. `Sec3_3_eq3_18`: display `(3.18)` intermediate function-level Stein pair bound with
   coefficient `1/(6a)`.
2. `Sec3_3_eq3_18_wasserstein`: $d_{\mathrm{W}}$ corollary with cubic coefficient `1/(3a)`.
3. `Sec3_3_1_antiVoter_not_reversible`: anti-voter Markov chain on prism graph $K_3 \square K_2$.
4. `Sec3_5_identDistrib_of_integral_deriv_compactSupport`: distributional uniqueness from
   $C_c^1$ derivatives.
-/

open MeasureTheory ProbabilityTheory

namespace SteinMethod.SweepB

/-- Display `(3.18)` (`\label{511}`, `SteinIntro.tex:1043-1046`): for an $a$-Stein pair $(W, W')$
and a twice-differentiable function $f : \mathbb{R} \to \mathbb{R}$ with $|f| \le B_0$,
$|f'| \le B_1$, and $|f''| \le B_2$,
$|\mathbb{E}[f'(W) - W f(W)]| \le B_1\,\mathbb{E}|1 - \mathbb{E}[(W' - W)^2 \mid W]/(2a)| +
(B_2 / (6a))\,\mathbb{E}|W' - W|^3$, stated with `ℝ≥0∞` `lintegral`s on the right-hand side per
`D1` so non-$L^3$ increments evaluate to `⊤` rather than junk `0`. -/
def Sec3_3_eq3_18 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a B₀ B₁ B₂ : ℝ} {W W' : Ω → ℝ} {f : ℝ → ℝ},
    IsSteinPair P a W W' →
    Differentiable ℝ f →
    Differentiable ℝ (deriv f) →
    (∀ w : ℝ, |f w| ≤ B₀) →
    (∀ w : ℝ, |deriv f w| ≤ B₁) →
    (∀ w : ℝ, |deriv (deriv f) w| ≤ B₂) →
    ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P| ≤
      ENNReal.ofReal B₁ *
          (∫⁻ ω,
            ENNReal.ofReal
              |1 - (P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
                  MeasurableSpace.comap W inferInstance] ω) / (2 * a)| ∂P) +
        ENNReal.ofReal (B₂ / (6 * a)) *
          ∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P

theorem Sec3_3_eq3_18_holds : Sec3_3_eq3_18 := by
  intro Ω inst P instP a B₀ B₁ B₂ W W' f hSP hf1 hf2 hf_bdd hf'_bdd hf''_bdd
  exact sec3_3_eq3_18_proof P hSP hf1 hf2 hf_bdd hf'_bdd hf''_bdd

/-- Optional Wasserstein corollary of `(3.18)` (`\label{511}`, `SteinIntro.tex:1043-1048`):
taking the supremum of `Sec3_3_eq3_18` over `normalWassersteinClass` ($B_1 = \sqrt{2/\pi}$,
$B_2 = 2$) via Theorem 3.1 bounds $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))$ without
requiring fourth moments, with cubic coefficient $2 / (6a) = 1 / (3a)$. -/
def Sec3_3_eq3_18_wasserstein : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ},
    IsSteinPair P a W W' →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi)) *
          (∫⁻ ω,
            ENNReal.ofReal
              |1 - (P[fun ω' ↦ (W' ω' - W ω') ^ 2 |
                  MeasurableSpace.comap W inferInstance] ω) / (2 * a)| ∂P) +
        ENNReal.ofReal (1 / (3 * a)) *
          ∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P

theorem Sec3_3_eq3_18_wasserstein_holds : Sec3_3_eq3_18_wasserstein := by
  intro Ω Ω' instΩ instΩ' P instP P' instP' a W W' Z hSP hZ hZ_law
  exact sec3_3_eq3_18_wasserstein_proof P P' hSP hZ hZ_law

/-- Section 3.3.1 non-reversibility of the anti-voter Markov chain (`SteinIntro.tex:1130-1131`):
there exists a finite connected $r$-regular simple graph $G$ satisfying the Section 3.3.1
hypotheses (non-bipartite, not isomorphic to `cycleGraph |V|`, witnessed e.g. by the $3$-regular
prism $K_3 \square K_2$ on `Fin 6`) such that the anti-voter chain has a stationary probability
distribution, and **every** stationary probability distribution $\mu$ violates detailed balance at
some pair of configurations $(x, y)$. -/
def Sec3_3_1_antiVoter_not_reversible : Prop :=
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
        μ {x} * antiVoterStep G x y ≠ μ {y} * antiVoterStep G y x)

theorem Sec3_3_1_antiVoter_not_reversible_holds : Sec3_3_1_antiVoter_not_reversible :=
  sec3_3_1_antiVoter_not_reversible_proof

/-- Section 3.5 distributional uniqueness from derivatives of compactly supported $C^1$ functions
(`SteinIntro.tex:1512-1513`, inside the proof of Proposition 3.19): if two real-valued random
variables $X$ and $Y$ satisfy $\mathbb{E}[f'(X)] = \mathbb{E}[f'(Y)]$ for every continuously
differentiable function $f : \mathbb{R} \to \mathbb{R}$ with compact support, then
$X \stackrel{d}{=} Y$ (`ProbabilityTheory.IdentDistrib X Y P P'`). -/
def Sec3_5_identDistrib_of_integral_deriv_compactSupport : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : Ω' → ℝ},
    AEMeasurable X P →
    AEMeasurable Y P' →
    (∀ f : ℝ → ℝ,
        Differentiable ℝ f →
        Continuous (deriv f) →
        (∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → f x = 0) →
        ∫ ω, deriv f (X ω) ∂P = ∫ ω', deriv f (Y ω') ∂P') →
    ProbabilityTheory.IdentDistrib X Y P P'

theorem Sec3_5_identDistrib_of_integral_deriv_compactSupport_holds :
    Sec3_5_identDistrib_of_integral_deriv_compactSupport := by
  intro Ω Ω' instΩ instΩ' P instP P' instP' X Y hX hY hHyp
  exact sec3_5_identDistrib_of_integral_deriv_compactSupport_proof P P' hX hY hHyp

end SteinMethod.SweepB
