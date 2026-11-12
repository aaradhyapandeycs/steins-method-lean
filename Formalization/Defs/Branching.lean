/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs.Couplings
import Formalization.Defs.Exponential
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic

/-!
# Galton–Watson Branching Processes & Size-Bias Trees (`Formalization.Defs.Branching`)

Core definitions for Section 5.3 of Nathan Ross, *"Fundamentals of Stein's method"*
(`arXiv:1109.1880v1`, `SteinIntro.tex:2985-3189`):
* `IsGaltonWatson`: Galton–Watson branching process $(Z_n)_{n \ge 0}$ with $Z_0 = 1$ and
  $Z_{n+1} = \sum_{i < Z_n} \xi_{n, i}$ (`SteinIntro.tex:2993-2997`);
* `GWTree`, `GWVertex`, `gwTreeGenSize`, `gwLeftCount`, `gwRightCount`, `gwProb`,
  `gwSizeBiasProbV`, `gwSizeBiasProb`: depth-$n$ planar trees and the tree probabilities
  $G_n(t)$, $G_n^s(t, v)$, and $G_n^s(t)$ (`SteinIntro.tex:3030-3056, 3070-3074, 3086-3098`);
* `IsSizeBiasSpine` and `IsSizeBiasSpineCoupling`: the Lyons–Pemantle–Peres spine decomposition
  $(X_j, L_{n,j}, R_{n,j}, R_{n,j}', U)$ of the size-bias Galton–Watson tree
  (`SteinIntro.tex:3059-3068, 3117-3139`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-- A sequence of non-negative integer-valued random variables $Z_0, Z_1, \dots$ on $(\Omega, P)$
is a Galton–Watson branching process (`SteinIntro.tex:2993-2997`) if $Z_1$ has finite mean and
there exists an i.i.d. array $(\xi_{n, i})_{(n, i) \in \mathbb{N}^2}$ of copies of $Z_1$ such that
$Z_0 = 1$ a.s. and $Z_{n+1} = \sum_{i < Z_n} \xi_{n, i}$ a.s. for all $n \ge 0$. -/
def IsGaltonWatson {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℕ → Ω → ℕ) : Prop :=
  Integrable (fun ω ↦ (Z 1 ω : ℝ)) P ∧
    ∃ ξ : ℕ × ℕ → Ω → ℕ,
      (∀ p : ℕ × ℕ, AEMeasurable (ξ p) P) ∧
      iIndepFun ξ P ∧
      (∀ p : ℕ × ℕ, IdentDistrib (ξ p) (Z 1) P P) ∧
      (∀ᵐ ω ∂P, Z 0 ω = 1) ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, Z (n + 1) ω = ∑ i ∈ Finset.range (Z n ω), ξ (n, i) ω

/-- Finite planar rooted tree truncated at generation $n$ (`SteinIntro.tex:3030-3052, 3086-3090`):
at depth $0$ a single root (`Unit`), and at depth $n + 1$ the ordered list of depth-$n$ subtrees
rooted at the children of the root. -/
def GWTree : ℕ → Type
  | 0 => Unit
  | n + 1 => List (GWTree n)

/-- Size $t_n$ of generation $n$ in a depth-$n$ planar tree $t$ (`SteinIntro.tex:3073-3074`). -/
def gwTreeGenSize : ∀ {n : ℕ}, GWTree n → ℕ
  | 0, () => 1
  | _ + 1, ts => (ts.map gwTreeGenSize).sum

/-- Type of individuals in generation $n$ of a depth-$n$ planar tree $t$
(`SteinIntro.tex:3049-3052, 3088-3089`). -/
def GWVertex : ∀ {n : ℕ}, GWTree n → Type
  | 0, () => Unit
  | _ + 1, ts => Σ i : Fin ts.length, GWVertex (ts.get i)

instance instFintypeGWVertex : ∀ {n : ℕ} (t : GWTree n), Fintype (GWVertex t)
  | 0, () => inferInstanceAs (Fintype Unit)
  | _ + 1, ts =>
      letI : ∀ i : Fin ts.length, Fintype (GWVertex (ts.get i)) :=
        fun i ↦ instFintypeGWVertex (ts.get i)
      inferInstanceAs (Fintype (Σ i : Fin ts.length, GWVertex (ts.get i)))

/-- Number of individuals strictly to the left of $v$ in generation $n$ of $t$
(`SteinIntro.tex:3031-3033, 3100-3101`). -/
def gwLeftCount : ∀ {n : ℕ} (t : GWTree n), GWVertex t → ℕ
  | 0, (), () => 0
  | _ + 1, ts, ⟨i, u⟩ =>
      ((ts.take i.1).map gwTreeGenSize).sum + gwLeftCount (ts.get i) u

/-- Number of individuals to the right (inclusive) of $v$ in generation $n$ of $t$
(`SteinIntro.tex:3065, 3100-3101`). -/
def gwRightCount : ∀ {n : ℕ} (t : GWTree n), GWVertex t → ℕ
  | 0, (), () => 1
  | _ + 1, ts, ⟨i, u⟩ =>
      gwRightCount (ts.get i) u + ((ts.drop (i.1 + 1)).map gwTreeGenSize).sum

/-- Probability $G_n(t)$ that the Galton–Watson branching process with offspring PMF $p$ agrees
with the planar tree $t$ up to generation $n$ (`SteinIntro.tex:3047-3048`). -/
def gwProb (p : ℕ → ℝ) : ∀ {n : ℕ}, GWTree n → ℝ
  | 0, () => 1
  | _ + 1, ts => p ts.length * (ts.map (gwProb p)).prod

/-- Probability $G_n^s(t, v)$ that the size-bias Galton–Watson tree (for a critical offspring PMF
$p$ with mean $1$) agrees with $t$ up to generation $n$ and has $v$ as the distinguished spine
vertex $v_n$ in generation $n$, defined by the recursion at
`SteinIntro.tex:3050-3052, 3091-3098`. -/
noncomputable def gwSizeBiasProbV (p : ℕ → ℝ) :
    ∀ {n : ℕ} (t : GWTree n), GWVertex t → ℝ
  | 0, (), () => 1
  | _ + 1, ts, ⟨i, u⟩ =>
      gwSizeBiasProbV p (ts.get i) u *
        (∏ j ∈ Finset.univ.erase i, gwProb p (ts.get j)) *
        ((ts.length : ℝ) * p ts.length) * (1 / (ts.length : ℝ))

/-- Probability $G_n^s(t) = \sum_v G_n^s(t, v)$ that the size-bias Galton–Watson tree agrees with
$t$ up to generation $n$ (`SteinIntro.tex:3048-3049, 3070-3072`). -/
noncomputable def gwSizeBiasProb (p : ℕ → ℝ) {n : ℕ} (t : GWTree n) : ℝ :=
  ∑ v : GWVertex t, gwSizeBiasProbV p t v

/-- Spine decomposition of the size-bias Galton–Watson tree at generation $n$
(`SteinIntro.tex:3034-3044, 3117-3126, 3166-3168`): for each spine level $j \in \{1, \dots, n\}$,
$X_j$ is the number of siblings of $v_j$ (so $X_j + 1$ has the size-bias distribution of $Z_1$),
$A_j$ is uniformly distributed on $\{0, \dots, X_j\}$ conditional on $X_j$, and
$L_{n,j} = \sum_{r < A_j} \xi_{j,r}$, $R_{n,j} = \sum_{A_j \le r < X_j} \xi_{j,r}$ are the
generation-$n$ descendant counts of the left and right siblings of $v_j$, where
$(\xi_{j,r})_{r \ge 0}$ are i.i.d. with the law of $Z_{n-j}$ independent of $(X_j, A_j)$, and the
spine levels $j \in \{1, \dots, n\}$ are mutually independent. -/
def IsSizeBiasSpine {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Z : ℕ → Ω → ℕ)
    (P' : Measure Ω') (n : ℕ) (X L R : ℕ → Ω' → ℕ) : Prop :=
  ∃ (A : ℕ → Ω' → ℕ) (ξ : ℕ → ℕ → Ω' → ℕ),
    iIndepFun
      (fun j : Finset.Icc 1 n ↦ fun ω' ↦ (X j.1 ω', A j.1 ω', fun r : ℕ ↦ ξ j.1 r ω')) P' ∧
    ∀ j ∈ Finset.Icc 1 n,
      AEMeasurable (X j) P' ∧
      AEMeasurable (A j) P' ∧
      (∀ r : ℕ, AEMeasurable (ξ j r) P') ∧
      IsSizeBias P (fun ω ↦ (Z 1 ω : ℝ)) P' (fun ω' ↦ (X j ω' : ℝ) + 1) ∧
      (∀ ω' : Ω', A j ω' ≤ X j ω') ∧
      (∀ k m : ℕ, P'.real {ω' | X j ω' = k ∧ A j ω' = m} =
        if m ≤ k then P'.real {ω' | X j ω' = k} / ((k : ℝ) + 1) else 0) ∧
      iIndepFun (ξ j) P' ∧
      (∀ r : ℕ, P'.map (ξ j r) = P.map (Z (n - j))) ∧
      IndepFun (fun ω' ↦ (X j ω', A j ω')) (fun ω' (r : ℕ) ↦ ξ j r ω') P' ∧
      (∀ ω' : Ω', L j ω' = ∑ r ∈ Finset.range (A j ω'), ξ j r ω') ∧
      (∀ ω' : Ω', R j ω' = ∑ r ∈ Finset.Ico (A j ω') (X j ω'), ξ j r ω')

/-- Full Lyons–Pemantle–Peres size-bias spine coupling at generation $n$
(`SteinIntro.tex:3065-3067, 3128-3139`): extends `IsSizeBiasSpine` with independent variables
$R_{n,j}' \stackrel{d}{=} (R_{n,j} \mid L_{n,j} = 0)$ ($1 \le j \le n$) and
$U \sim \mathrm{Unif}(0, 1)$ independent of all else. -/
def IsSizeBiasSpineCoupling {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Z : ℕ → Ω → ℕ)
    (P' : Measure Ω') (n : ℕ) (X L R R' : ℕ → Ω' → ℕ) (U : Ω' → ℝ) : Prop :=
  IsSizeBiasSpine P Z P' n X L R ∧
    (∀ j ∈ Finset.Icc 1 n,
      AEMeasurable (R' j) P' ∧
      P'.map (R' j) = (ProbabilityTheory.cond P' {ω' | L j ω' = 0}).map (R j)) ∧
    iIndepFun (fun j : Finset.Icc 1 n ↦ R' j.1) P' ∧
    IndepFun (fun ω' (j : Finset.Icc 1 n) ↦ R' j.1 ω')
      (fun ω' (j : Finset.Icc 1 n) ↦ (X j.1 ω', L j.1 ω', R j.1 ω')) P' ∧
    MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P' ∧
    IndepFun U
      (fun ω' ↦ (fun j : Finset.Icc 1 n ↦ (X j.1 ω', L j.1 ω', R j.1 ω'),
        fun j : Finset.Icc 1 n ↦ R' j.1 ω')) P'

end SteinMethod
