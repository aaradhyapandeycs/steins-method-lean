/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs

/-!
# Section 6 Statements (`Formalization.Statements.Sec6`)

Self-contained statements from Section 6 (*Geometric approximation*, `SteinIntro.tex:3190-3388`) of
Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`), importing core definitions
only (`AGENTS.md` Rule 5).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SteinMethod

/-- Section 6 opening Wasserstein triangle-inequality bound, corrected
(`SteinIntro.tex:3193-3198`; `ISSUE-6.0`): for $0 < p \le 1$, a positive integer-valued random
variable $W$ with $\mathbb{E}[W] = 1/p$, $X \sim \mathrm{Ge}(p)$ on $\{1, 2, \dots\}$, and
$Z \sim \mathrm{Exp}(1)$, all Wasserstein distances are finite and
$|d_{\mathrm{W}}(pW, Z) - p\,d_{\mathrm{W}}(X, W)| \le p$. The printed display omits the scaling
factor $p$ on $d_{\mathrm{W}}(X, W)$ (`not_Sec6_opening_wasserstein_printed`, `ISSUE-6.0`). -/
def Sec6_opening_wasserstein_corrected : Prop :=
  ∀ {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    {p : ℝ} {W : Ω → ℕ} {X : Ω' → ℕ} {Z : Ω'' → ℝ},
    0 < p →
    p ≤ 1 →
    AEMeasurable W P →
    (∀ᵐ ω ∂P, 0 < W ω) →
    Integrable (fun ω ↦ (W ω : ℝ)) P →
    ∫ ω, (W ω : ℝ) ∂P = 1 / p →
    AEMeasurable X P' →
    P'.map X = posGeomLaw p →
    AEMeasurable Z P'' →
    P''.map Z = ProbabilityTheory.expMeasure 1 →
    wassersteinDist (P.map (fun ω ↦ p * (W ω : ℝ))) (P''.map Z) < ⊤ ∧
      wassersteinDist (P'.map (fun ω' ↦ (X ω' : ℝ))) (P.map (fun ω ↦ (W ω : ℝ))) < ⊤ ∧
      |(wassersteinDist (P.map (fun ω ↦ p * (W ω : ℝ))) (P''.map Z)).toReal -
          p * (wassersteinDist (P'.map (fun ω' ↦ (X ω' : ℝ)))
            (P.map (fun ω ↦ (W ω : ℝ)))).toReal| ≤ p

/-- Section 6 opening support-mismatch total variation formula and small-$p$ limit
(`SteinIntro.tex:3199-3200`): for $X \sim \mathrm{Ge}(p)$ on $\{1, 2, \dots\}$ ($0 < p \le 1$) and
integer $k \ge 1$, if $W =^d kX$, then
$d_{\mathrm{TV}}(W, X) = 1 - \frac{p(1 - p)^{k - 1}}{1 - (1 - p)^k}$, which converges to
$\frac{k - 1}{k}$ as $p \to 0^+$. -/
def Sec6_supportMismatch : Prop :=
  (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {k : ℕ} {W : Ω → ℕ} {X : Ω' → ℕ},
    0 < p →
    p ≤ 1 →
    1 ≤ k →
    AEMeasurable X P' →
    P'.map X = posGeomLaw p →
    P.map W = P'.map (fun ω' ↦ k * X ω') →
    tvDist (P.map W) (P'.map X) =
      ENNReal.ofReal (1 - p * (1 - p) ^ (k - 1) / (1 - (1 - p) ^ k))) ∧
  (∀ {k : ℕ}, 1 ≤ k →
    Tendsto (fun p : ℝ ↦ 1 - p * (1 - p) ^ (k - 1) / (1 - (1 - p) ^ k))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (((k : ℝ) - 1) / (k : ℝ))))

/-- Section 6 opening & 6.3 failure of exponential approximation (`SteinIntro.tex:3211-3212`):
for $n \ge 2$, the in-degree $W_n$ of an independent uniformly chosen vertex in
`uniformAttachment n` satisfies $\mathbb{P}(W_n = 0) = \frac{n - 1}{2n}$ and
$d_{\mathrm{K}}(\mathcal{L}(W_n), \mathrm{Exp}(1)) \ge \frac{n - 1}{2n}$. -/
def Sec6_3_not_exponential : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n)
    {G : Ω → Digraph (Fin n)} {I : Ω → Fin n},
    AEMeasurable G P →
    P.map G = uniformAttachment n →
    AEMeasurable I P →
    ProbabilityTheory.IndepFun I G P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, by omega⟩⟩).toMeasure →
    let W : Ω → ℕ := fun ω ↦ digraphInDegree (G ω) (I ω)
    P.real {ω | W ω = 0} = ((n : ℝ) - 1) / (2 * (n : ℝ)) ∧
    ENNReal.ofReal (((n : ℝ) - 1) / (2 * (n : ℝ))) ≤
      kolmogorovDist
        (P.map (fun ω ↦ (W ω : ℝ)))
        ((ProbabilityTheory.expMeasure 1).map id)

/-- Lemma 6.1(1) (`\label{lem173}`, `SteinIntro.tex:3229-3236`): for $0 < p \le 1$, if
$Z \sim \mathrm{Ge}^0(p)$, then $\mathbb{E}[\mathcal{A}f(Z)] = 0$ for all bounded functions
$f : \mathbb{N} \to \mathbb{R}$, where
$\mathcal{A}f(k) = (1 - p)\Delta f(k) - p f(k) + p f(0)$. -/
def Lem6_1_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} {Z : Ω → ℕ},
    0 < p →
    p ≤ 1 →
    AEMeasurable Z P →
    P.map Z = geomLaw p →
    ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, geomSteinOp p f (Z ω) ∂P = 0

/-- Lemma 6.1(2) (`\label{lem173}`, `SteinIntro.tex:3229-3241`; `ISSUE-6.1`): for $0 < p \le 1$,
if $W$ is a non-negative integer-valued random variable such that
$\mathbb{E}[\mathcal{A}f(W)] = 0$ for all bounded functions $f : \mathbb{N} \to \mathbb{R}$, then
$W \sim \mathrm{Ge}^0(p)$ (with no moment hypothesis on $W$). -/
def Lem6_1_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} {W : Ω → ℕ},
    0 < p →
    p ≤ 1 →
    AEMeasurable W P →
    (∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, geomSteinOp p f (W ω) ∂P = 0) →
    P.map W = geomLaw p

/-- Lemma 6.2 (`\label{lem174}`, `SteinIntro.tex:3243-3249, 3264-3274`; `ISSUE-TYPO-6.2`): for
$0 < p \le 1$ and $A \subseteq \mathbb{N}$, `geomSteinSol p A` satisfies $f_A(0) = 0$, solves the
geometric Stein equation
$(1 - p)\Delta f_A(k) - p f_A(k) = \mathbb{I}[k \in A] - \mathrm{Ge}^0(p)(A)$ uniquely among
functions vanishing at $0$, has forward difference
$\Delta f_A(k) = \mathbb{I}[k \in A] - p\sum_{i \in A,\, i \ge k + 1} (1 - p)^{i - k - 1}$, and
satisfies $-1 \le \Delta f_A(k) \le 1$ for all $k \in \mathbb{N}$. -/
def Lem6_2 : Prop :=
  ∀ {p : ℝ}, 0 < p → p ≤ 1 → ∀ A : Set ℕ,
    geomSteinSol p A 0 = 0 ∧
    (∀ k : ℕ,
      (1 - p) * fwdDiff 1 (geomSteinSol p A) k - p * geomSteinSol p A k =
        A.indicator 1 k - (geomLaw p).real A) ∧
    (∀ g : ℕ → ℝ,
      g 0 = 0 →
      (∀ k : ℕ,
        (1 - p) * fwdDiff 1 g k - p * g k = A.indicator 1 k - (geomLaw p).real A) →
      g = geomSteinSol p A) ∧
    (∀ k : ℕ,
      fwdDiff 1 (geomSteinSol p A) k =
        A.indicator 1 k -
          p * ∑' i : ℕ, (A ∩ Set.Ici (k + 1)).indicator (fun i ↦ (1 - p) ^ (i - (k + 1))) i) ∧
    (∀ k : ℕ, -1 ≤ fwdDiff 1 (geomSteinSol p A) k ∧ fwdDiff 1 (geomSteinSol p A) k ≤ 1)

/-- Theorem 6.3 (`\label{thm178}`, `SteinIntro.tex:3251-3258`): for $0 < p \le 1$, a non-negative
integer-valued random variable $W$ with $\mathbb{E}[W] = (1 - p)/p$, and $N \sim \mathrm{Ge}^0(p)$,
$d_{\mathrm{TV}}(W, N) \le \sup_{f \in \mathcal{F}} |\mathbb{E}[(1 - p)\Delta f(W) - p f(W)]|$. -/
def Thm6_3 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {W : Ω → ℕ} {N : Ω' → ℕ},
    0 < p →
    p ≤ 1 →
    AEMeasurable W P →
    Integrable (fun ω ↦ (W ω : ℝ)) P →
    ∫ ω, (W ω : ℝ) ∂P = (1 - p) / p →
    AEMeasurable N P' →
    P'.map N = geomLaw p →
    tvDist (P.map W) (P'.map N) ≤
      ⨆ f ∈ geomSteinClass,
        ENNReal.ofReal |∫ ω, ((1 - p) * fwdDiff 1 f (W ω) - p * f (W ω)) ∂P|

/-- Proposition 6.4 (`\label{prop172}`, `SteinIntro.tex:3292-3296`; `ISSUE-6.4`): if $W \ge 0$ is
an integer-valued random variable with $\mathbb{E}[W] = (1 - p)/p$ for $0 < p \le 1$, $W^s$ has
the size-bias distribution of $W$, and conditional on $W^s$, $W^e$ is uniform on
$\{0, 1, \dots, W^s - 1\}$, then $W^e$ has the discrete equilibrium distribution with respect to
$W$. -/
def Prop6_4 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {W : Ω → ℕ} {Ws We : Ω' → ℕ},
    0 < p →
    p ≤ 1 →
    AEMeasurable W P →
    Integrable (fun ω ↦ (W ω : ℝ)) P →
    ∫ ω, (W ω : ℝ) ∂P = (1 - p) / p →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P' (fun ω' ↦ (Ws ω' : ℝ)) →
    AEMeasurable We P' →
    (∀ m j : ℕ,
      P'.real {ω' | Ws ω' = m ∧ We ω' = j} =
        if j < m then P'.real {ω' | Ws ω' = m} / (m : ℝ) else 0) →
    IsDiscreteEquilibrium P p W P' We

/-- Remark 6.2 & discrete equilibrium existence/uniqueness, restricted to $0 < p < 1$
(`\label{rem175}`, `SteinIntro.tex:3290-3291, 3304-3310`; `ISSUE-6.4`):
1. Existence and uniqueness (`SteinIntro.tex:3290-3291`): for $0 < p < 1$ and an integer-valued
   random variable $W \ge 0$ with $\mathbb{E}[W] = (1 - p)/p$, there exists a unique probability
   measure $\nu$ on $\mathbb{N}$ whose identity map satisfies `IsDiscreteEquilibrium P p W ν id`
   (restricted from $p \le 1$ because at $p = 1$, $1 - p = 0$ makes `(6.1)` hold for every law of
   $W^e$, `ISSUE-6.4`).
2. Stationary-excess formula (`SteinIntro.tex:3304-3305`): Remark 6.2's *"the same as that from
   renewal theory"* is read as the stationary-excess formula
   $\mathbb{P}(W^e = k) = \mathbb{P}(W > k) / \mathbb{E}[W] = \frac{p}{1 - p}\mathbb{P}(W > k)$
   for all $k \in \mathbb{N}$ (stationarity of the delayed renewal process $Y^e + Y_1 + \cdots$ is
   Remark 5.3 at `SteinIntro.tex:2875-2879`). -/
def Rem6_2_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} {W : Ω → ℕ},
    0 < p →
    p < 1 →
    AEMeasurable W P →
    Integrable (fun ω ↦ (W ω : ℝ)) P →
    ∫ ω, (W ω : ℝ) ∂P = (1 - p) / p →
    (∃! ν : Measure ℕ, ∃ _ : IsProbabilityMeasure ν, IsDiscreteEquilibrium P p W ν id) ∧
      ∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {We : Ω' → ℕ},
        AEMeasurable We P' →
        (IsDiscreteEquilibrium P p W P' We ↔
          ∀ k : ℕ, P'.real {ω' | We ω' = k} = p / (1 - p) * P.real {ω | k < W ω})

/-- Theorem 6.5 (`\label{thm177}`, `SteinIntro.tex:3312-3319`): for $0 < p \le 1$,
$N \sim \mathrm{Ge}^0(p)$, and an integer-valued random variable $W \ge 0$ with
$\mathbb{E}[W] = (1 - p)/p$ and $\mathbb{E}[W^2] < \infty$, if $W^e$ has the discrete equilibrium
distribution with respect to $W$ on the same probability space, then
$d_{\mathrm{TV}}(W, N) \le 2(1 - p)\mathbb{E}|W^e - W|$. -/
def Thm6_5 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {W We : Ω → ℕ} {N : Ω' → ℕ},
    MemLp (fun ω ↦ (W ω : ℝ)) 2 P →
    IsDiscreteEquilibrium P p W P We →
    AEMeasurable N P' →
    P'.map N = geomLaw p →
    tvDist (P.map W) (P'.map N) ≤
      ENNReal.ofReal (2 * (1 - p)) * ∫⁻ ω, ENNReal.ofReal |(We ω : ℝ) - (W ω : ℝ)| ∂P

/-- Section 6.3 asymptotic geometric convergence without rate (`SteinIntro.tex:3342-3343`, citing
`[brst01]`): as $n \to \infty$, the in-degree $W_{n + 1}$ of an independent uniformly chosen vertex
in `uniformAttachment (n + 1)` converges in total variation to $\mathrm{Ge}^0(1/2)$. -/
def Sec6_3_uniformAttachment_convergence : Prop :=
  ∀ {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {G : ∀ n, Ω n → Digraph (Fin (n + 1))} {I : ∀ n, Ω n → Fin (n + 1)},
    (∀ n : ℕ,
      AEMeasurable (G n) (P n) ∧
      (P n).map (G n) = uniformAttachment (n + 1) ∧
      AEMeasurable (I n) (P n) ∧
      ProbabilityTheory.IndepFun (I n) (G n) (P n) ∧
      (P n).map (I n) =
        (@PMF.uniformOfFintype (Fin (n + 1)) inferInstance
          ⟨⟨0, Nat.succ_pos n⟩⟩).toMeasure) →
    let W : ∀ n, Ω n → ℕ := fun n ω ↦ digraphInDegree (G n ω) (I n ω)
    Tendsto (fun n : ℕ ↦ tvDist ((P n).map (W n)) (geomLaw (1 / 2)))
      atTop (nhds 0)

/-- Theorem 6.6 (`\label{thm1716}`, `SteinIntro.tex:3345-3350`; `ISSUE-TYPO-6.6`, `ISSUE-6.6`):
if $G_n$ ($n \ge 1$) is generated according to the uniform attachment directed graph model, $I$ is
an independent uniformly chosen vertex of $G_n$, $W$ is the in-degree of $I$ in $G_n$, and
$N \sim \mathrm{Ge}^0(1/2)$, then
$d_{\mathrm{TV}}(W, N) \le \frac{2(\log(n) + 1)}{n}$. -/
def Thm6_6 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {G : Ω → Digraph (Fin n)} {I : Ω → Fin n} {N : Ω' → ℕ},
    AEMeasurable G P →
    P.map G = uniformAttachment n →
    AEMeasurable I P →
    ProbabilityTheory.IndepFun I G P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    AEMeasurable N P' →
    P'.map N = geomLaw (1 / 2) →
    let W : Ω → ℕ := fun ω ↦ digraphInDegree (G ω) (I ω)
    tvDist (P.map W) (P'.map N) ≤
      ENNReal.ofReal (2 * (Real.log (n : ℝ) + 1) / (n : ℝ))

end SteinMethod
