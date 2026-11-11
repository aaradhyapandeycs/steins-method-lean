/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs

/-!
# Section 4 Statements (`Formalization.Statements.Sec4`)

Self-contained lemma and corollary statements from Section 4 of Nathan Ross,
*"Fundamentals of Stein's method"* (`SteinIntro.tex:1816-2711`), importing core definitions only
(`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-- Lemma 4.1(1) (`\label{lem101}`, `SteinIntro.tex:1823-1830`): for $\lambda > 0$, if $Z$ has the
Poisson distribution $\mathrm{Po}(\lambda)$, then $\mathbb{E}[\mathcal{A}f(Z)] = 0$ for all bounded
functions $f : \mathbb{N} \to \mathbb{R}$, where $\mathcal{A}f(k) = \lambda f(k + 1) - k f(k)$. -/
def Lem4_1_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {Z : Ω → ℕ},
    0 < r →
    AEMeasurable Z P →
    P.map Z = poissonLaw r →
    ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, poissonSteinOp r f (Z ω) ∂P = 0

/-- Lemma 4.1(2) (`\label{lem101}`, `SteinIntro.tex:1823-1835`): for $\lambda > 0$, if $W$ is a
non-negative integer-valued random variable such that $\mathbb{E}[\mathcal{A}f(W)] = 0$ for all
bounded functions $f : \mathbb{N} \to \mathbb{R}$, then $W$ has the Poisson distribution
$\mathrm{Po}(\lambda)$ (with no integrability hypothesis on $W$). -/
def Lem4_1_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {W : Ω → ℕ},
    0 < r →
    AEMeasurable W P →
    (∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, poissonSteinOp r f (W ω) ∂P = 0) →
    P.map W = poissonLaw r

/-- Lemma 4.2 (`\label{lem102}`, eq. `(4.1)` `\label{101}`, `SteinIntro.tex:1837-1848`): for
$\lambda > 0$ and $A \subseteq \mathbb{N}$, `poissonSteinSol r A` satisfies $f_A(0) = 0$, solves
the Chen–Stein equation
$\lambda f_A(k + 1) - k f_A(k) = \mathbb{I}[k \in A] - \mathrm{Po}(\lambda)(A)$ for all
$k \in \mathbb{N}$, and is the unique solution with boundary value $0$ at $k = 0$. -/
def Lem4_2 : Prop :=
  ∀ {r : ℝ≥0}, 0 < r → ∀ A : Set ℕ,
    poissonSteinSol r A 0 = 0 ∧
    (∀ k : ℕ,
      poissonSteinOp r (poissonSteinSol r A) k =
        A.indicator 1 k - (poissonLaw r).real A) ∧
    (∀ g : ℕ → ℝ,
      g 0 = 0 →
      (∀ k : ℕ, poissonSteinOp r g k = A.indicator 1 k - (poissonLaw r).real A) →
      g = poissonSteinSol r A)

/-- Corollary 4.3 (`\label{cor101}`, `SteinIntro.tex:1850-1855`): if $W$ is a non-negative
integer-valued random variable with finite mean $\lambda > 0$, then for every
$A \subseteq \mathbb{N}$,
$|\mathbb{P}(W \in A) - \mathrm{Po}(\lambda)(A)| = |\mathbb{E}[\lambda f_A(W + 1) - W f_A(W)]|$. -/
def Cor4_3 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {W : Ω → ℕ} (A : Set ℕ),
    0 < r →
    AEMeasurable W P →
    Integrable (fun ω ↦ (W ω : ℝ)) P →
    (∫ ω, (W ω : ℝ) ∂P = (r : ℝ)) →
    |P.real {ω | W ω ∈ A} - (poissonLaw r).real A| =
      |∫ ω, ((r : ℝ) * poissonSteinSol r A (W ω + 1) -
        (W ω : ℝ) * poissonSteinSol r A (W ω)) ∂P|

/-- Lemma 4.4 (`\label{lem103}`, eq. `(4.2)` `\label{102}`, `SteinIntro.tex:1879-1886`;
`ISSUE-4.4`): for $\lambda > 0$ and $A \subseteq \mathbb{N}$, the canonical Chen–Stein solution
$f_A = \mathrm{poissonSteinSol}\,r\,A$ satisfies $|f_A(k)| \le \min\{1, \lambda^{-1/2}\}$ and
$|\Delta f_A(k)| \le (1 - e^{-\lambda}) / \lambda \le \min\{1, \lambda^{-1}\}$ for all
$k \in \mathbb{N}$, where $\Delta f(k) = f(k + 1) - f(k)$. -/
def Lem4_4 : Prop :=
  ∀ {r : ℝ≥0}, 0 < r → ∀ (A : Set ℕ) (k : ℕ),
    |poissonSteinSol r A k| ≤ min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) ∧
    |fwdDiff 1 (poissonSteinSol r A) k| ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ) ∧
    (1 - Real.exp (-(r : ℝ))) / (r : ℝ) ≤ min 1 (r : ℝ)⁻¹

/-- Theorem 4.5 (`\label{thm101}`, eq. `(4.4)` `\label{1019}`, `SteinIntro.tex:1911-1916`): let
$\mathcal{F}$ be the set of functions satisfying `(4.2)` (`poissonSteinClass r`). If $W \ge 0$ is
an integer-valued random variable with mean $\lambda > 0$ and $Z \sim \mathrm{Po}(\lambda)$, then
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}} |\mathbb{E}[\lambda f(W + 1) - W f(W)]|$.

Reading notes (`stmts-review-05C` `C3`):
* `poissonSteinClass r` uses the sharp middle forward-difference bound $(1 - e^{-r}) / r$ from
  `(4.2)`, which is a subset of the outer $\min\{1, r^{-1}\}$ class by Lemma 4.4 (`Lem4_4`),
  giving a smaller supremum on the right-hand side.
* `0 < r` is typing because `(4.2)` divides by $\lambda$ in $\lambda^{-1/2}$ and
  $(1 - e^{-\lambda}) / \lambda$ (`DEFINITIONS.md` §1.2, §5.3; at $r = 0$ with $\mathbb{E}[W] = 0$,
  $W = 0$ a.s. and $\mathrm{Po}(0) = \delta_0$, proved in `Formalization.PoissonDep.Basic`). -/
def Thm4_5 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {r : ℝ≥0} {W : Ω → ℕ} {Z : Ω' → ℕ},
    0 < r →
    AEMeasurable W P →
    Integrable (fun ω ↦ (W ω : ℝ)) P →
    (∫ ω, (W ω : ℝ) ∂P = (r : ℝ)) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ poissonSteinClass r, ENNReal.ofReal |∫ ω, poissonSteinOp r f (W ω) ∂P|

/-- Section 4.1 opening prose claim (`SteinIntro.tex:1938-1939`): if $W_n \sim \mathrm{Bi}(n,
\lambda / n)$ (realized as the sum of $n$ independent indicators with success probability
$\lambda / n$) and $Z \sim \mathrm{Po}(\lambda)$, then $d_{\mathrm{TV}}(\mathcal{L}(W_n),
\mathcal{L}(Z)) \le \min\{1, \lambda\} (\lambda / n)$ for $n \ge \max(1, \lambda)$, and hence
$d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathcal{L}(Z)) \to 0$ as $n \to \infty$. -/
def Sec4_1_binomial_limit : Prop :=
  ∀ {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {r : ℝ≥0} {X : ∀ n, Fin n → Ω n → ℕ},
    (∀ n : ℕ, 0 < n → (r : ℝ) ≤ (n : ℝ) →
      (∀ i : Fin n, AEMeasurable (X n i) (P n)) ∧
      (∀ i : Fin n, ∀ᵐ ω ∂P n, X n i ω = 0 ∨ X n i ω = 1) ∧
      ProbabilityTheory.iIndepFun (X n) (P n) ∧
      (∀ i : Fin n, (P n).real {ω | X n i ω = 1} = (r : ℝ) / (n : ℝ))) →
    let W : ∀ n, Ω n → ℕ := fun n ω ↦ ∑ i : Fin n, X n i ω
    (∀ n : ℕ, 0 < n → (r : ℝ) ≤ (n : ℝ) →
      tvDist ((P n).map (W n)) (poissonLaw r) ≤
        ENNReal.ofReal (min 1 (r : ℝ) * ((r : ℝ) / (n : ℝ)))) ∧
    Filter.Tendsto (fun n : ℕ ↦ tvDist ((P n).map (W n)) (poissonLaw r))
      Filter.atTop (nhds 0)

/-- Theorem 4.6 (`\label{thm102}`, `SteinIntro.tex:1942-1949`; `ISSUE-TYPO-4.6`): if $X_1, \dots,
X_n$ ($n \ge 1$) are independent $\{0, 1\}$-indicators with $\mathbb{P}(X_i = 1) = p_i$,
$W = \sum_{i=1}^n X_i$, $\lambda = \sum_{i=1}^n p_i$, and $Z \sim \mathrm{Po}(\lambda)$, then
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1, \lambda^{-1}\} \sum_{i=1}^n p_i^2 \le
\min\{1, \lambda\} \max_i p_i$. -/
def Thm4_6 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℕ} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    ProbabilityTheory.iIndepFun X P →
    (r : ℝ) = (∑ i : Fin n, P.real {ω | X i ω = 1}) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal (min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2) ∧
      min 1 (r : ℝ)⁻¹ * (∑ i : Fin n, p i ^ 2) ≤
        min 1 (r : ℝ) * Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ p

/-- Theorem 4.7, corrected (`\label{thm103}`, `SteinIntro.tex:1970-1977`; `ISSUE-4.7`): Poisson
local-dependence total-variation bound for a sum $W = \sum_{i=1}^n X_i$ of $\{0, 1\}$-indicators
with dependency neighborhoods $N_i$ (`HasDependencyNeighborhoods`). The hypothesis `∀ i, i ∈ N i`
is added to the printed statement because the printed theorem without $i \in N_i$ is false
(`not_Thm4_7_printed`, `ISSUE-4.7`). -/
def Thm4_7_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {N : Fin n → Finset (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    HasDependencyNeighborhoods P (fun i ω ↦ (X i ω : ℝ)) N →
    (∀ i : Fin n, i ∈ N i) →
    (r : ℝ) = (∑ i : Fin n, P.real {ω | X i ω = 1}) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let p₂ : Fin n → Fin n → ℝ := fun i j ↦ ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          ((∑ i : Fin n, ∑ j ∈ N i, p i * p j) +
            ∑ i : Fin n, ∑ j ∈ (N i).erase i, p₂ i j))

/-- Remark 4.1 (`SteinIntro.tex:1978-1981`, proving from scratch the Arratia–Goldstein–Gordon
`[agg89, agg90]` $b_1 + b_2 + b_3$ bound cited there): dropping the independence assumption on
$(X_j)_{j \notin N_i}$ for neighborhoods $N_i$ ($i \in N_i$) adds a conditional-expectation
dependence error term.

Reading note (`stmts-review-05C` `C3`): Ross's prose phrase *"an additional error term that
(roughly) measures the dependence between $X_i$ and $(X_j)_{j \notin N_i}$"* is formalized
concretely as the Arratia–Goldstein–Gordon $b_3$ term
$\sum_{i=1}^n \mathbb{E}|\mathbb{E}[X_i - p_i \mid \sigma(X_j : j \notin N_i)]|$ multiplied by the
sup-norm bound $\|f\| \le \min\{1, \lambda^{-1/2}\}$ from `(4.2)` (`Lem4_4`), with explicit
`Measurable (X i)` for conditional expectation (`DEFINITIONS.md` §5). -/
def Rem4_1 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {N : Fin n → Finset (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    (∀ i : Fin n, i ∈ N i) →
    (r : ℝ) = (∑ i : Fin n, P.real {ω | X i ω = 1}) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let p₂ : Fin n → Fin n → ℝ := fun i j ↦ ∫ ω, (X i ω : ℝ) * (X j ω : ℝ) ∂P
    let b₁ : ℝ := ∑ i : Fin n, ∑ j ∈ N i, p i * p j
    let b₂ : ℝ := ∑ i : Fin n, ∑ j ∈ (N i).erase i, p₂ i j
    let b₃ : ℝ := ∑ i : Fin n,
      ∫ ω, |P[fun ω' ↦ (X i ω' : ℝ) - p i |
        MeasurableSpace.comap (fun ω' (j : {j : Fin n // j ∉ N i}) ↦ X j ω') inferInstance] ω| ∂P
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (min 1 (r : ℝ)⁻¹ * (b₁ + b₂) + min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) * b₃)

/-- Theorem 4.8 (`\label{thm104}`, eq. `(4.8)` `\label{1011}`, `SteinIntro.tex:2024-2030`): for
$1 \le k \le n$ and $0 \le p \le 1$, let $W$ be the number of head runs of length at least $k$ in
$n$ independent tosses of a coin with head probability $p$. Then
$\lambda := \mathbb{E}[W] = p^k ((n - k)(1 - p) + 1)$, and for $Z \sim \mathrm{Po}(\lambda)$,
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \lambda^2 \frac{2k + 1}{n - k + 1} +
2 \lambda p^k$. -/
def Thm4_8 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n k : ℕ} {p : ℝ} {Y : Fin n → Ω → ℕ} {r : ℝ≥0} {Z : Ω' → ℕ},
    1 ≤ k →
    k ≤ n →
    0 ≤ p →
    p ≤ 1 →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
    ProbabilityTheory.iIndepFun Y P →
    (∀ i : Fin n, P.real {ω | Y i ω = 1} = p) →
    (r : ℝ) = p ^ k * (((n : ℝ) - (k : ℝ)) * (1 - p) + 1) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    let W : Ω → ℕ := fun ω ↦ headRunCount k (fun i ↦ Y i ω)
    ∫ ω, (W ω : ℝ) ∂P = (r : ℝ) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          ((r : ℝ) ^ 2 * ((2 * (k : ℝ) + 1) / ((n : ℝ) - (k : ℝ) + 1)) +
            2 * (r : ℝ) * p ^ k)

/-- Remark 4.2 (`\label{re101}`, `SteinIntro.tex:2031-2038`; `stmts-review-05C` `C1`):
(1) Treating $k = \frac{\log(n(1 - p))}{\log(1 / p)} + c$ as a real threshold (matching
*"Roughly"* at `SteinIntro.tex:2033`), for $0 < p < 1$ and $c \in \mathbb{R}$,
$\lambda_n = p^k ((n - k)(1 - p) + 1) \to p^c$ and the `(4.8)` error expression is
$\Theta(\log(n) / n)$.
(2) Along integer thresholds $k_n \in \mathbb{N}$ with bounded offset
$x_n = k_n - \frac{\log(n(1 - p))}{\log(1 / p)}$ ($|x_n| \le M$, as required when applying
Theorem 4.8 in §4.2.1), eventually $1 \le k_n \le n$, $\lambda_n - p^{x_n} = O(\log(n) / n) \to 0$,
and `(4.8)` evaluated at $k_n$ is $O(\log(n) / n)$. -/
def Rem4_2 : Prop :=
  (∀ {p c : ℝ},
      0 < p →
      p < 1 →
      let k : ℕ → ℝ := fun n ↦ Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) + c
      let lam : ℕ → ℝ := fun n ↦ p ^ (k n) * (((n : ℝ) - k n) * (1 - p) + 1)
      let err : ℕ → ℝ := fun n ↦
        lam n ^ 2 * ((2 * k n + 1) / ((n : ℝ) - k n + 1)) + 2 * lam n * p ^ (k n)
      Filter.Tendsto lam Filter.atTop (nhds (p ^ c)) ∧
        ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
          C₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n ∧
            err n ≤ C₂ * (Real.log (n : ℝ) / (n : ℝ))) ∧
  (∀ {p M : ℝ} {k : ℕ → ℕ},
      0 < p →
      p < 1 →
      (∀ᶠ n : ℕ in Filter.atTop,
        |(k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)| ≤ M) →
      let x : ℕ → ℝ := fun n ↦ (k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)
      let lam : ℕ → ℝ := fun n ↦ p ^ (k n) * (((n : ℝ) - (k n : ℝ)) * (1 - p) + 1)
      let err : ℕ → ℝ := fun n ↦
        lam n ^ 2 * ((2 * (k n : ℝ) + 1) / ((n : ℝ) - (k n : ℝ) + 1)) +
          2 * lam n * p ^ (k n)
      Filter.Tendsto (fun n ↦ lam n - p ^ (x n)) Filter.atTop (nhds 0) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
          1 ≤ k n ∧ k n ≤ n ∧
            |lam n - p ^ (x n)| ≤ C * (Real.log (n : ℝ) / (n : ℝ)) ∧
            err n ≤ C * (Real.log (n : ℝ) / (n : ℝ)))

/-- Section 4.2.1 longest-head-run event identity and qualified Gumbel approximation
(`SteinIntro.tex:2054-2061`): (1) for $1 \le k \le n$ and $\{0, 1\}$-valued coin tosses,
$\mathbb{P}(W = 0) = \mathbb{P}(R_n < k)$; (2) for $0 < p < 1$ and integer thresholds $k_n$ with
bounded offset $x_n = k_n - \frac{\log(n(1 - p))}{\log(1 / p)} \in [-M, M]$ (the integrality
qualification noted at `SteinIntro.tex:2060`), $|\mathbb{P}(R_n - \frac{\log(n(1-p))}{\log(1/p)} <
x_n) - e^{-p^{x_n}}| \le C \frac{\log(n)}{n}$ for all sufficiently large $n$. -/
def Sec4_2_1_longestRun : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {n k : ℕ} {Y : Fin n → Ω → ℕ},
      1 ≤ k →
      k ≤ n →
      (∀ i : Fin n, AEMeasurable (Y i) P) →
      (∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
      P.real {ω | headRunCount k (fun i ↦ Y i ω) = 0} =
        P.real {ω | longestQualityRun 1 (fun i ↦ Y i ω) < k}) ∧
  (∀ {p M : ℝ} {k : ℕ → ℕ},
      0 < p →
      p < 1 →
      (∀ᶠ n : ℕ in Filter.atTop,
        |(k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)| ≤ M) →
      ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          {Y : Fin n → Ω → ℕ},
          (∀ i : Fin n, AEMeasurable (Y i) P) →
          (∀ i : Fin n, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
          ProbabilityTheory.iIndepFun Y P →
          (∀ i : Fin n, P.real {ω | Y i ω = 1} = p) →
          let x : ℝ := (k n : ℝ) - Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p)
          |P.real {ω |
              (longestQualityRun 1 (fun i ↦ Y i ω) : ℝ) -
                Real.log ((n : ℝ) * (1 - p)) / Real.log (1 / p) < x} -
            Real.exp (-(p ^ x))| ≤ C * (Real.log (n : ℝ) / (n : ℝ)))

/-- Theorem 4.9, corrected (`[\ER\ Law]`, `SteinIntro.tex:2071-2078`; `ISSUE-4.9`, proved from
scratch following Erdős–Rényi 1970): for an infinite sequence of independent coin tosses with head
probability $p$ and quality parameter $a$ satisfying $0 < p < a \le 1$, the longest quality-$a$
head run $R_n$ in the first $n$ tosses satisfies $R_n / \log(n) \to 1 / H(a, p)$ almost surely.
The hypotheses `0 < p` and `p < a` are added to the printed $0 < a \le 1$ because the printed
statement is false when $0 < a < p < 1$ (`not_Thm4_9_printed`, `ISSUE-4.9`, where $R_n / n \to 1$
so $R_n / \log(n) \to +\infty$ while $H(a, p) > 0$) and divides by zero at $a = p$ or $p = 0$. -/
def Thm4_9_corrected : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p a : ℝ} {Y : ℕ → Ω → ℕ},
    0 < p →
    p < a →
    a ≤ 1 →
    (∀ i : ℕ, AEMeasurable (Y i) P) →
    (∀ i : ℕ, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1) →
    ProbabilityTheory.iIndepFun Y P →
    (∀ i : ℕ, P.real {ω | Y i ω = 1} = p) →
    ∀ᵐ ω ∂P,
      Filter.Tendsto
        (fun n : ℕ ↦
          (longestQualityRun a (fun i : Fin n ↦ Y i.1 ω) : ℝ) / Real.log (n : ℝ))
        Filter.atTop
        (nhds (1 / klDivBernoulli a p))

/-- Remark 4.3 (`SteinIntro.tex:2079-2110`, DNA sequence comparison model; `stmts-review-05C`
joint-law strengthening): if two independent sequences $A_1 \cdots A_n$ and $B_1 \cdots B_n$ are
generated as i.i.d. draws from a $4$-letter alphabet (`Fin 4`, representing $\{A, G, C, T\}$) with
letter frequencies $q_0, q_1, q_2, q_3$, then the coordinate-wise match indicators
$Y_i = \mathbb{I}[A_i = B_i]$ are mutually independent, have joint product law
`Measure.pi (fun i ↦ P.map (Y i))`, and satisfy $\mathbb{P}(Y_i = 1) = \sum_{c : \mathrm{Fin}\,4}
q_c^2$. -/
def Rem4_3 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {A B : Fin n → Ω → Fin 4} {q : Fin 4 → ℝ},
    (∀ i : Fin n, AEMeasurable (A i) P) →
    (∀ i : Fin n, AEMeasurable (B i) P) →
    ProbabilityTheory.iIndepFun A P →
    ProbabilityTheory.iIndepFun B P →
    ProbabilityTheory.IndepFun (fun ω i ↦ A i ω) (fun ω i ↦ B i ω) P →
    (∀ (i : Fin n) (c : Fin 4), P.real {ω | A i ω = c} = q c) →
    (∀ (i : Fin n) (c : Fin 4), P.real {ω | B i ω = c} = q c) →
    let Y : Fin n → Ω → ℕ := fun i ω ↦ if A i ω = B i ω then 1 else 0
    ProbabilityTheory.iIndepFun Y P ∧
      P.map (fun ω i ↦ Y i ω) = Measure.pi (fun i ↦ P.map (Y i)) ∧
      ∀ i : Fin n, P.real {ω | Y i ω = 1} = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2

/-- Example 4.21 true-rate prose claim (`SteinIntro.tex:2702-2703`, citing `[abt03]`;
`stmts-review-05H` `H4`, `stmts-review-BL6` `BL6-1`, Backlog item 6): for the number of fixed
points $W_n(\pi) = |\{i \in \mathrm{Fin}\,n \mid \pi(i) = i\}|$ of a uniformly chosen random
permutation $\pi \in \mathrm{Sym}(n)$, the total variation distance to $\mathrm{Po}(1)$ satisfies
the super-exponential bound $d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)) \le 2^n / (n + 1)!$
for all $n \in \mathbb{N}$ and decays strictly faster than order $1/n$, i.e.
$\lim_{n \to \infty} n \, d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(1)) = 0$ in `ℝ≥0∞`. -/
def Ex4_21_true_rate : Prop :=
  let W : (n : ℕ) → Equiv.Perm (Fin n) → ℕ :=
    fun n π ↦ (Finset.univ.filter fun i : Fin n ↦ π i = i).card
  let μW : ℕ → Measure ℕ :=
    fun n ↦ ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).map (W n)).toMeasure
  (∀ n : ℕ,
    tvDist (μW n) (poissonLaw 1) ≤
      (2 : ENNReal) ^ n / (Nat.factorial (n + 1) : ENNReal)) ∧
  Filter.Tendsto
    (fun n : ℕ ↦ (n : ENNReal) * tvDist (μW n) (poissonLaw 1))
    Filter.atTop (nhds 0)

end SteinMethod
