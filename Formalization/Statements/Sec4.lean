/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.PoissonSizeBias
import Formalization.Defs.PoissonSizeBiasMonotone
import Formalization.Defs.PoissonSizeBiasSubgraph

/-!
# Section 4 Statements (`Formalization.Statements.Sec4`)

Self-contained theorem, proposition, lemma, corollary, remark, example, and prose statements from
Section 4 (`\label{poi}`, `SteinIntro.tex:1816-2711`) of Nathan Ross, *"Fundamentals of Stein's
method"* (`arXiv:1109.1880v1`), importing core definitions only (`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped NNReal

namespace SteinMethod

/-- Lemma 4.1(1) (`\label{lem101}`, unlabeled item 1, `SteinIntro.tex:1823-1830`): for
$\lambda > 0$, if $Z$ has the Poisson distribution $\mathrm{Po}(\lambda)$, then
$\mathbb{E}[\mathcal{A}f(Z)] = 0$ for all bounded functions $f : \mathbb{N} \to
\mathbb{R}$, where $\mathcal{A}f(k) = \lambda f(k + 1) - k f(k)$. -/
def Lem4_1_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {Z : Ω → ℕ},
    0 < r →
    AEMeasurable Z P →
    P.map Z = poissonLaw r →
    ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, poissonSteinOp r f (Z ω) ∂P = 0

/-- Lemma 4.1(2) (`\label{lem101}`, unlabeled item 2, `SteinIntro.tex:1823-1835`): for
$\lambda > 0$, if $W$ is a non-negative integer-valued random variable such that
$\mathbb{E}[\mathcal{A}f(W)] = 0$ for all bounded functions $f : \mathbb{N} \to
\mathbb{R}$, then $W$ has the Poisson distribution $\mathrm{Po}(\lambda)$ (with no
integrability hypothesis on $W$). -/
def Lem4_1_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {W : Ω → ℕ},
    0 < r →
    AEMeasurable W P →
    (∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, poissonSteinOp r f (W ω) ∂P = 0) →
    P.map W = poissonLaw r

/-- Lemma 4.2 (`\label{lem102}`, eq. `(4.1)` `\label{101}`, `SteinIntro.tex:1837-1848`): for
$\lambda > 0$ and $A \subseteq \mathbb{N}$, `poissonSteinSol r A` satisfies $f_A(0) = 0$,
solves the Chen–Stein equation $\lambda f_A(k + 1) - k f_A(k) = \mathbb{I}[k \in A] -
\mathrm{Po}(\lambda)(A)$ for all $k \in \mathbb{N}$, and is the unique solution with
boundary value $0$ at $k = 0$. -/
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
integer-valued random variable with finite mean $\lambda > 0$, then for every $A \subseteq
\mathbb{N}$, $|\mathbb{P}(W \in A) - \mathrm{Po}(\lambda)(A)| = |\mathbb{E}[\lambda f_A(W +
1) - W f_A(W)]|$. -/
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
`ISSUE-4.4` and `ISSUE-TYPO-4.4` in `docs/SOURCE-ISSUES.md`): for $\lambda > 0$ and $A
\subseteq \mathbb{N}$, the canonical Chen–Stein solution $f_A =
\mathrm{poissonSteinSol}\,r\,A$ satisfies $|f_A(k)| \le \min\{1, \lambda^{-1/2}\}$ and
$|\Delta f_A(k)| \le (1 - e^{-\lambda}) / \lambda \le \min\{1, \lambda^{-1}\}$ for all $k
\in \mathbb{N}$, where $\Delta f(k) = f(k + 1) - f(k)$. -/
def Lem4_4 : Prop :=
  ∀ {r : ℝ≥0}, 0 < r → ∀ (A : Set ℕ) (k : ℕ),
    |poissonSteinSol r A k| ≤ min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) ∧
    |fwdDiff 1 (poissonSteinSol r A) k| ≤ (1 - Real.exp (-(r : ℝ))) / (r : ℝ) ∧
    (1 - Real.exp (-(r : ℝ))) / (r : ℝ) ≤ min 1 (r : ℝ)⁻¹

/-- Proof of Lemma 4.4 point-mass solution properties, corrected at $j = 0, k = 0$ (unlabeled
prose in proof of Lemma 4.4 (`\ref{lem103}`), `SteinIntro.tex:1889-1899`; `ISSUE-4.4-PROSE`
in `docs/SOURCE-ISSUES.md`): for $\lambda > 0$:
1. for $j \ge 1$, $f_j = \mathrm{poissonSteinSol}\,r\,\{j\}$ satisfies all three sign and
   forward-difference bounds at `SteinIntro.tex:1895-1897`;
2. for $j = 0$, $\Delta f_0(0) = (1 - e^{-\lambda})/\lambda > 0$, while $\Delta f_0(k) < 0$ for
   all $k \ge 1$.

Difference from printed result (`ISSUE-4.4-PROSE`): printed `SteinIntro.tex:1899` claims
$\Delta f_0(k) < 0$ for all $k \in \mathbb{N}$, which fails at $k = 0$ since $f_0(0) = 0$ and
$f_0(1) = (1 - e^{-\lambda})/\lambda > 0$ (`not_Sec4_fwdDiff_f0_neg_printed`); here $k = 0$ is
separated from $k \ge 1$. -/
def Sec4_poissonSteinSol_pointMass_corrected : Prop :=
  ∀ {r : ℝ≥0}, 0 < r →
    (∀ {j : ℕ}, 1 ≤ j →
      (∀ k : ℕ, k ≤ j → poissonSteinSol r {j} k ≤ 0) ∧
      (∀ k : ℕ, j < k → 0 ≤ poissonSteinSol r {j} k) ∧
      (∀ k : ℕ, k ≠ j → fwdDiff 1 (poissonSteinSol r {j}) k ≤ 0) ∧
      0 ≤ fwdDiff 1 (poissonSteinSol r {j}) j ∧
      fwdDiff 1 (poissonSteinSol r {j}) j ≤
        min ((j : ℝ)⁻¹) ((1 - Real.exp (-(r : ℝ))) / (r : ℝ))) ∧
    fwdDiff 1 (poissonSteinSol r {0}) 0 = (1 - Real.exp (-(r : ℝ))) / (r : ℝ) ∧
    0 < fwdDiff 1 (poissonSteinSol r {0}) 0 ∧
    (∀ k : ℕ, 1 ≤ k → fwdDiff 1 (poissonSteinSol r {0}) k < 0)

/-- Theorem 4.5 (`\label{thm101}`, eq. `(4.4)` `\label{1019}`, `SteinIntro.tex:1911-1916`): let
$\mathcal{F}$ be the set of functions satisfying `(4.2)` (`poissonSteinClass r`). If $W \ge
0$ is an integer-valued random variable with mean $\lambda > 0$ and $Z \sim
\mathrm{Po}(\lambda)$, then $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \sup_{f
\in \mathcal{F}} |\mathbb{E}[\lambda f(W + 1) - W f(W)]|$.

Reading notes: (1) `poissonSteinClass r` uses the sharp middle forward-difference bound $(1 -
e^{-r}) / r$ from `(4.2)`, which is a subset of the outer $\min\{1, r^{-1}\}$ class by Lemma
4.4 (`Lem4_4`), giving a smaller supremum on the right-hand side; (2) `0 < r` is typing because
`(4.2)` divides by $\lambda$ (`DEFINITIONS.md` §1.2, §5.3). -/
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

/-- Section 4.1 opening prose claim (unlabeled prose, `SteinIntro.tex:1938-1939`): if $W_n \sim
\mathrm{Bi}(n, \lambda / n)$ (realized as the sum of $n$ independent indicators with
success probability $\lambda / n$) and $Z \sim \mathrm{Po}(\lambda)$, then
$d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathcal{L}(Z)) \le \min\{1, \lambda\} (\lambda / n)$
for $n \ge \max(1, \lambda)$, and hence $d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathcal{L}(Z))
\to 0$ as $n \to \infty$. -/
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

/-- Theorem 4.6 (`\label{thm102}` at `SteinIntro.tex:1936`, theorem body at
`SteinIntro.tex:1942-1949`; `ISSUE-TYPO-4.6` in `docs/SOURCE-ISSUES.md`): if $X_1, \dots,
X_n$ ($n \ge 1$) are independent $\{0, 1\}$-indicators with $\mathbb{P}(X_i = 1) = p_i$, $W
= \sum_{i=1}^n X_i$, $\lambda = \sum_{i=1}^n p_i$, and $Z \sim \mathrm{Po}(\lambda)$, then
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1, \lambda^{-1}\} \sum_{i=1}^n
p_i^2 \le \min\{1, \lambda\} \max_i p_i$. -/
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

/-- Theorem 4.7, corrected (`\label{thm103}`, `SteinIntro.tex:1970-1977`; `ISSUE-4.7` in
`docs/SOURCE-ISSUES.md`): Poisson local-dependence total-variation bound for a sum $W =
\sum_{i=1}^n X_i$ of $\{0, 1\}$-indicators with dependency neighborhoods $N_i$
(`HasDependencyNeighborhoods`).

Difference from printed result (`ISSUE-4.7`): adds the hypothesis `∀ i, i ∈ N i` omitted in the
printed statement; without $i \in N_i$, taking $N_i = \emptyset$ for independent indicators
gives right-hand side $0 < d_{\mathrm{TV}}(\mathrm{Bi}(n, p), \mathrm{Po}(np))$
(`not_Thm4_7_printed`). -/
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

/-- Remark 4.1 (unlabeled, `SteinIntro.tex:1978-1981`, proving from scratch the
Arratia–Goldstein–Gordon `[agg89, agg90]` $b_1 + b_2 + b_3$ bound cited there): dropping
the independence assumption on $(X_j)_{j \notin N_i}$ for neighborhoods $N_i$ ($i \in N_i$)
adds a conditional-expectation dependence error term.

Reading note: Ross's prose phrase *"at the cost of an additional error term that (roughly)
measures dependence"* (`SteinIntro.tex:1980`) is formalized concretely as the
Arratia–Goldstein–Gordon $b_3$ term $\sum_{i=1}^n \mathbb{E}|\mathbb{E}[X_i - p_i \mid
\sigma(X_j : j \notin N_i)]|$ multiplied by the sup-norm bound $\|f\| \le \min\{1,
\lambda^{-1/2}\}$ from `(4.2)` (`Lem4_4`), with explicit `Measurable (X i)` for conditional
expectation (`DEFINITIONS.md` §5). -/
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

/-- Section 4.2.1 head-run de-clumping identity (unlabeled prose, `SteinIntro.tex:2006-2023`):
for $k \ge 1$ and any $\{0, 1\}$-valued sequence `y : Fin n → ℕ`, the de-clumped indicator
sum `headRunCount k y` equals the exact number of maximal contiguous runs of ones in `y` of
length at least $k$. -/
def Sec4_2_1_headRun_declumping : Prop :=
  ∀ {n k : ℕ}, 1 ≤ k → ∀ {y : Fin n → ℕ},
    (∀ t : Fin n, y t = 0 ∨ y t = 1) →
    headRunCount k y =
      {im : ℕ × ℕ |
        k ≤ im.2 ∧
        ∃ h : im.1 + im.2 ≤ n,
          (∀ r : Fin im.2, y ⟨im.1 + r.1, by omega⟩ = 1) ∧
          (im.1 = 0 ∨ ∃ h₀ : im.1 - 1 < n, y ⟨im.1 - 1, h₀⟩ = 0) ∧
          (im.1 + im.2 = n ∨ ∃ h₁ : im.1 + im.2 < n, y ⟨im.1 + im.2, h₁⟩ = 0)}.ncard

/-- Theorem 4.8 (`\label{thm104}`, eq. `(4.8)` `\label{1011}`, `SteinIntro.tex:2024-2030`;
`ISSUE-TYPO-THM4.8` in `docs/SOURCE-ISSUES.md`): for $1 \le k \le n$ and $0 \le p \le 1$,
let $W$ be the number of head runs of length at least $k$ in $n$ independent tosses of a
coin with head probability $p$. Then $\lambda := \mathbb{E}[W] = p^k ((n - k)(1 - p) + 1)$,
and for $Z \sim \mathrm{Po}(\lambda)$, $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\lambda^2 \frac{2k + 1}{n - k + 1} + 2 \lambda p^k$. -/
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

/-- Remark 4.2 (`\label{re101}`, `SteinIntro.tex:2031-2038`):
(1) Treating $k = \frac{\log(n(1 - p))}{\log(1 / p)} + c$ as a real threshold (matching
    *"Roughly"* at `SteinIntro.tex:2033`), for $0 < p < 1$ and $c \in \mathbb{R}$, $\lambda_n =
    p^k ((n - k)(1 - p) + 1) \to p^c$ and the `(4.8)` error expression is $\Theta(\log(n) /
    n)$.
(2) Along integer thresholds $k_n \in \mathbb{N}$ with bounded offset $x_n = k_n -
    \frac{\log(n(1 - p))}{\log(1 / p)}$ ($|x_n| \le M$, as required when applying Theorem 4.8
    in §4.2.1), eventually $1 \le k_n \le n$, $\lambda_n - p^{x_n} = O(\log(n) / n) \to 0$, and
    `(4.8)` evaluated at $k_n$ is $O(\log(n) / n)$. -/
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

/-- Section 4.2.1 longest-head-run event identity and qualified Gumbel approximation (unlabeled
prose, `SteinIntro.tex:2054-2061`): (1) for $1 \le k \le n$ and $\{0, 1\}$-valued coin
tosses, $\mathbb{P}(W = 0) = \mathbb{P}(R_n < k)$; (2) for $0 < p < 1$ and integer
thresholds $k_n$ with bounded offset $x_n = k_n - \frac{\log(n(1 - p))}{\log(1 / p)} \in
[-M, M]$ (the integrality qualification noted at `SteinIntro.tex:2060`), $|\mathbb{P}(R_n -
\frac{\log(n(1-p))}{\log(1/p)} < x_n) - e^{-p^{x_n}}| \le C \frac{\log(n)}{n}$ for all
sufficiently large $n$. -/
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

/-- Theorem 4.9, corrected (unlabeled `[\ER\ Law]`, `SteinIntro.tex:2071-2078`; `ISSUE-4.9` in
`docs/SOURCE-ISSUES.md`, proved from scratch following Erdős–Rényi 1970): for an infinite
sequence of independent coin tosses with head probability $p$ and quality parameter $a$
satisfying $0 < p < a \le 1$, the longest quality-$a$ head run $R_n$ in the first $n$
tosses satisfies $R_n / \log(n) \to 1 / H(a, p)$ almost surely.

Difference from printed result (`ISSUE-4.9`): strengthens $0 < a \le 1$ (and implicit $0 \le p
\le 1$) to the rare-event regime $0 < p < a \le 1$; when $0 < a < p < 1$, $R_n / n \to 1$ so
$R_n / \log(n) \to +\infty$ while $H(a, p) > 0$ (`not_Thm4_9_printed`), and at $a = p$ or $p =
0$ the printed limit $1 / H(a, p)$ divides by zero. -/
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

/-- Remark 4.3 (unlabeled, `SteinIntro.tex:2079-2110`, DNA sequence comparison model): if two
independent sequences $A_1 \cdots A_n$ and $B_1 \cdots B_n$ are generated as i.i.d. draws
from a $4$-letter alphabet (`Fin 4`, representing $\{A, G, C, T\}$) with letter frequencies
$q_0, q_1, q_2, q_3$, then the coordinate-wise match indicators $Y_i = \mathbb{I}[A_i =
B_i]$ are mutually independent, have joint product law `Measure.pi (fun i ↦ P.map (Y i))`,
and satisfy $\mathbb{P}(Y_i = 1) = \sum_{c : \mathrm{Fin}\,4} q_c^2$. -/
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

/-- Theorem 4.10 (`\label{thm121}`, `SteinIntro.tex:2120-2127`): if $W \ge 0$ is an
integer-valued random variable with $\mathbb{E}[W] = \lambda > 0$, $W^s$ is a size-bias
coupling of $W$ on the same probability space, and $Z \sim \mathrm{Po}(\lambda)$, then
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1, \lambda\}\,\mathbb{E}|W + 1 -
W^s|$ (stated in `ℝ≥0∞` via `lintegral` so the bound remains valid when $\mathbb{E}[W^s] =
\infty$). -/
def Thm4_10 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {r : ℝ≥0} {W : Ω → ℕ} {Ws : Ω → ℝ} {Z : Ω' → ℕ},
    0 < r →
    AEMeasurable W P →
    (∫ ω, (W ω : ℝ) ∂P = (r : ℝ)) →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (min 1 (r : ℝ)) *
        ∫⁻ ω, ENNReal.ofReal |(W ω : ℝ) + 1 - Ws ω| ∂P

/-- Corollary 4.11 (`\label{cor121}`, `SteinIntro.tex:2142-2147`; `ISSUE-TYPO-4.11` in
`docs/SOURCE-ISSUES.md`, correcting unbound `X` at `SteinIntro.tex:2146` to `W`): for $\{0,
1\}$-valued random variables $X_1, \dots, X_n$ with $p_i = \mathbb{P}(X_i = 1)$, $W =
\sum_{i=1}^n X_i$, and $\lambda = \sum_{i=1}^n p_i > 0$, if $(X_j^{(i)})_{j \ne i}$ has the
conditional distribution of $(X_j)_{j \ne i}$ given $X_i = 1$ and $I$ is independent of
$(X, X^{(\cdot)})$ with $\mathbb{P}(I = i) = p_i / \lambda$, then $W^s = \sum_{j \ne I}
X_j^{(I)} + 1$ has the size-bias distribution of $W$. -/
def Cor4_11 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    let p : Fin n → ℝ := fun i ↦ P.real (X i ⁻¹' {1})
    let lam : ℝ := ∑ i : Fin n, p i
    0 < lam →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P (X i ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / lam) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1)

/-- Corollary 4.12 (`\label{cor122}`, `SteinIntro.tex:2148-2154`; `ISSUE-TYPO-4.12` in
`docs/SOURCE-ISSUES.md`, correcting `X`, `X^s` at `SteinIntro.tex:2152-2153` to `W`,
`W^s`): if $X_1, \dots, X_n$ ($n \ge 1$) are exchangeable $\{0, 1\}$-indicators and
$(X_j^{(1)})_{j \ne 1}$ has the conditional distribution of $(X_j)_{j \ne 1}$ given $X_1 =
1$, then $W^s = \sum_{j \ne 1} X_j^{(1)} + 1$ has the size-bias distribution of $W =
\sum_{i=1}^n X_i$. -/
def Cor4_12 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {Y : Ω' → ({j : Fin n // j ≠ ⟨0, hn⟩} → ℝ)},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    IsExchangeableTuple P X →
    AEMeasurable Y P' →
    (0 < P.real (X ⟨0, hn⟩ ⁻¹' {1}) →
      P'.map Y =
        (ProbabilityTheory.cond P (X ⟨0, hn⟩ ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ ⟨0, hn⟩}) ↦ X j.1 ω)) →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P'
      (fun ω' ↦ (∑ j : {j : Fin n // j ≠ ⟨0, hn⟩}, Y ω' j) + 1)

/-- Example 4.4 (unlabeled `[Law of small numbers]`, `SteinIntro.tex:2162-2172`): for
independent $\{0, 1\}$-indicators $X_1, \dots, X_n$ with $p_i = \mathbb{P}(X_i = 1)$, $W =
\sum_{i=1}^n X_i$, $\lambda = \sum_{i=1}^n p_i > 0$, an index $I$ independent of $X$ with
$\mathbb{P}(I = i) = p_i / \lambda$, and $Z \sim \mathrm{Po}(\lambda)$, $W^s = \sum_{j \ne
I} X_j + 1$ has the size-bias distribution of $W$ and $d_{\mathrm{TV}}(W, Z) \le \min\{1,
\lambda\}\mathbb{E}[X_I] = \min\{1, \lambda\}\sum_{i=1}^n
\frac{p_i}{\lambda}\mathbb{E}[X_i] = \min\{1, \lambda^{-1}\}\sum_{i=1}^n p_i^2$. -/
def Ex4_4 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {I : Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    ProbabilityTheory.iIndepFun X P →
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, (X j.1 ω : ℝ)) + 1
    0 < r →
    (∑ i : Fin n, p i = (r : ℝ)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω i ↦ X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal (min 1 (r : ℝ) * ∫ ω, (X (I ω) ω : ℝ) ∂P) ∧
      min 1 (r : ℝ) * ∫ ω, (X (I ω) ω : ℝ) ∂P =
        min 1 (r : ℝ) * ∑ i : Fin n, (p i / (r : ℝ)) * ∫ ω, (X i ω : ℝ) ∂P ∧
      min 1 (r : ℝ) * ∑ i : Fin n, (p i / (r : ℝ)) * ∫ ω, (X i ω : ℝ) ∂P =
        min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2

/-- Example 4.5 footnote comparison under the Section 3.4 proof-method reading (unlabeled
footnote in Example 4.5 (`\ref{ex122}`), `SteinIntro.tex:2181-2186`, referencing eq.
`(3.30)` `\label{78}` at `SteinIntro.tex:1380-1388`): for isolated vertices in $G \sim G(n,
p)$ ($n \ge 1$, $0 \le p \le 1$), let $W(G) = \sum_{i=1}^n X_i(G)$ be the isolated-vertex
count, $W^s_{(i)}(G) = \sum_{j \ne i} X_j(G \setminus E(v_i)) + 1$ be the vertex-$i$
edge-deletion coupling, $W^s_{\mathrm{fix}} = W^s_{(v_1)}$ be the deterministic Corollary
4.12 coupling (`Ex4_5_coupling`), and $W^s_{\mathrm{rand}}(G, I) = W^s_{(I)}(G)$ ($I \sim
\mathrm{Unif}(\mathrm{Fin}\,n)$ independent of $G$) be the randomized Corollary 4.11
coupling (`Ex3_9_sizeBias`). Then:
(1) conditioning on $G$ as in Section 3.4 (`SteinIntro.tex:1386`, via Corollary 3.16
    `\label{cor72}` at `SteinIntro.tex:1326-1332` and Remark 3.4 at `SteinIntro.tex:1000-1008`)
    gives $\mathrm{Var}(\mathbb{E}[W^s_{\mathrm{rand}} - W \mid G]) =
    \frac{1}{n^2}\mathrm{Var}(\sum_{i=1}^n (W^s_{(i)} - W))$;
(2) in the sparse normal regime $p_n = c / n$ ($c > 0$), the un-averaged quantity
    $\frac{\mu_n}{\sigma_n^2}\sqrt{\mathrm{Var}(W^s_{\mathrm{fix}} - W)}$ stays bounded away
    from $0$ as $n \to \infty$. -/
def Ex4_5_footnote_comparison : Prop :=
  (∀ {n : ℕ} (hn : 0 < n) {p : ℝ},
    0 ≤ p →
    p ≤ 1 →
    let v0 : Fin n := ⟨0, hn⟩
    let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
    let μI : Measure (Fin n) :=
      (@PMF.uniformOfFintype (Fin n) inferInstance ⟨v0⟩).toMeasure
    let Q : Measure (SimpleGraph (Fin n) × Fin n) := P.prod μI
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let W : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, X_ind i H
    let Ws_at : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ (∑ j : {j : Fin n // j ≠ i}, X_ind j.1 (H.deleteIncidenceSet i)) + 1
    let WQ : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ W ω.1
    let Ws_rand : SimpleGraph (Fin n) × Fin n → ℝ := fun ω ↦ Ws_at ω.2 ω.1
    ProbabilityTheory.variance
        (Q[fun ω ↦ Ws_rand ω - WQ ω |
          MeasurableSpace.comap Prod.fst inferInstance]) Q =
      (1 / (n : ℝ) ^ 2) *
        ProbabilityTheory.variance (fun H ↦ ∑ i : Fin n, (Ws_at i H - W H)) P) ∧
  (∀ {c : ℝ}, 0 < c →
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : 0 < n),
        let v0 : Fin n := ⟨0, hn⟩
        let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n (c / (n : ℝ))
        let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
          fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
        let W : SimpleGraph (Fin n) → ℝ := fun H ↦ ∑ i : Fin n, X_ind i H
        let Ws_fix : SimpleGraph (Fin n) → ℝ :=
          fun H ↦ (∑ j : {j : Fin n // j ≠ v0}, X_ind j.1 (H.deleteIncidenceSet v0)) + 1
        let μ : ℝ := ∫ H, W H ∂P
        let σ2 : ℝ := ProbabilityTheory.variance W P
        δ ≤ (μ / σ2) * Real.sqrt (ProbabilityTheory.variance (fun H ↦ Ws_fix H - W H) P))

/-- Example 4.5, vertex-$1$ deletion coupling and $L^1$ increment calculation (`\label{ex122}`,
`SteinIntro.tex:2189-2207`, `SteinIntro.tex:2176`): in $G \sim G(n, p)$ ($n \ge 1$, $0 \le
p \le 1$), erasing all edges incident to $v_1$ (`SimpleGraph.deleteIncidenceSet ⟨0, hn⟩`)
gives coupled isolated-vertex indicators $(X_j^{(1)})_{j \ne 1}$ having the conditional
distribution of $(X_j)_{j \ne 1}$ given $X_1 = 1$ (when $p < 1$), so $W^s = \sum_{j \ne 1}
X_j^{(1)} + 1$ has the size-bias distribution of $W = \sum_{i=1}^n X_i$, the coupling is
pointwise increasing ($X_j \le X_j^{(1)}$, `SteinIntro.tex:2203-2204`) with $X_j^{(1)} -
X_j \in \{0, 1\}$ and $\mathbb{P}(X_j^{(1)} - X_j = 1) = p(1 - p)^{n - 2}$
(`SteinIntro.tex:2205-2207`), and $\mathbb{E}|W + 1 - W^s| = \mathbb{E}|X_1 + \sum_{j \ne
1}(X_j - X_j^{(1)})| = \mathbb{E}[X_1] + \sum_{j \ne 1} \mathbb{E}[X_j^{(1)} - X_j] = (1 -
p)^{n - 1} + (n - 1) p (1 - p)^{n - 2}$. -/
def Ex4_5_coupling : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {p : ℝ} {G : Ω → SimpleGraph (Fin n)},
    0 ≤ p →
    p ≤ 1 →
    Measurable G →
    P.map G = erdosRenyi n p →
    let v0 : Fin n := ⟨0, hn⟩
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let X : Fin n → Ω → ℝ := fun i ω ↦ X_ind i (G ω)
    let X1 : {j : Fin n // j ≠ v0} → Ω → ℝ :=
      fun j ω ↦ X_ind j.1 ((G ω).deleteIncidenceSet v0)
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ v0}, X1 j ω) + 1
    (p < 1 →
      P.map (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X1 j ω) =
        (ProbabilityTheory.cond P {ω | X v0 ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ v0}) ↦ X j.1 ω)) ∧
      IsSizeBias P W P Ws ∧
      (∀ (ω : Ω) (j : {j : Fin n // j ≠ v0}), X j.1 ω ≤ X1 j ω) ∧
      (∀ j : {j : Fin n // j ≠ v0},
        (∀ ω : Ω, X1 j ω - X j.1 ω = 0 ∨ X1 j ω - X j.1 ω = 1) ∧
          P.real {ω | X1 j ω - X j.1 ω = 1} = p * (1 - p) ^ (n - 2)) ∧
      ∫ ω, |W ω + 1 - Ws ω| ∂P =
        ∫ ω, |X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)| ∂P ∧
      ∫ ω, |X v0 ω + ∑ j : {j : Fin n // j ≠ v0}, (X j.1 ω - X1 j ω)| ∂P =
        ∫ ω, X v0 ω ∂P + ∑ j : {j : Fin n // j ≠ v0}, ∫ ω, (X1 j ω - X j.1 ω) ∂P ∧
      ∫ ω, X v0 ω ∂P + ∑ j : {j : Fin n // j ≠ v0}, ∫ ω, (X1 j ω - X j.1 ω) ∂P =
        (1 - p) ^ (n - 1) + ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2)

/-- Proposition 4.13 (unlabeled proposition, `SteinIntro.tex:2208-2214`, nested in Example 4.5
`\label{ex122}` at `SteinIntro.tex:2176`): for the number $W$ of isolated vertices in $G
\sim G(n, p)$ ($n \ge 1$, $0 \le p \le 1$), $\lambda = \mathbb{E}[W] = n(1 - p)^{n - 1}$,
and $Z \sim \mathrm{Po}(\lambda)$, $d_{\mathrm{TV}}(W, Z) \le \min\{1, \lambda\}((n - 1)p(1
- p)^{n - 2} + (1 - p)^{n - 1})$, and when $p < 1$ (so $1 - p > 0$), $\min\{1, \lambda\}((n
- 1)p(1 - p)^{n - 2} + (1 - p)^{n - 1}) \le \min\{\lambda, \lambda^2\}\bigl(\frac{p}{1 - p}
+ \frac{1}{n}\bigr)$. -/
def Prop4_13 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {r : ℝ≥0}
    {G : Ω → SimpleGraph (Fin n)} {Z : Ω' → ℕ},
    0 < n →
    0 ≤ p →
    p ≤ 1 →
    AEMeasurable G P →
    P.map G = erdosRenyi n p →
    let W : Ω → ℕ := fun ω ↦ {i : Fin n | (G ω).IsIsolated i}.ncard
    ((r : ℝ) = ∫ ω, (W ω : ℝ) ∂P) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) * (((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) + (1 - p) ^ (n - 1))) ∧
    (p < 1 →
      min 1 (r : ℝ) * (((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) + (1 - p) ^ (n - 1)) ≤
        min (r : ℝ) ((r : ℝ) ^ 2) * (p / (1 - p) + 1 / (n : ℝ)))

/-- Example 4.5 asymptotic interpretation (unlabeled prose in Example 4.5,
`SteinIntro.tex:2215-2217`): if $0 \le p_n \le 1$ and $\lambda_n = n(1 - p_n)^{n - 1}$
stays bounded away from $0$ and $\infty$ for large $n$ ($0 < c_1 \le \lambda_n \le c_2$
eventually), then $p_n$ is of exact order $\log(n)/n$ (in fact $p_n / (\log(n)/n) \to 1$)
and the Proposition 4.13 upper bound $\min\{\lambda_n, \lambda_n^2\}(p_n/(1 - p_n) + 1/n)$
is of exact order $\log(n)/n$. -/
def Ex4_5_asymptotics : Prop :=
  ∀ {p : ℕ → ℝ} {c₁ c₂ : ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    0 < c₁ →
    (∀ᶠ n : ℕ in Filter.atTop,
      c₁ ≤ (n : ℝ) * (1 - p n) ^ (n - 1) ∧ (n : ℝ) * (1 - p n) ^ (n - 1) ≤ c₂) →
    let lam : ℕ → ℝ := fun n ↦ (n : ℝ) * (1 - p n) ^ (n - 1)
    let err : ℕ → ℝ := fun n ↦ min (lam n) (lam n ^ 2) * (p n / (1 - p n) + 1 / (n : ℝ))
    Filter.Tendsto (fun n : ℕ ↦ p n / (Real.log (n : ℝ) / (n : ℝ))) Filter.atTop (nhds 1) ∧
      (∃ A₁ A₂ : ℝ, 0 < A₁ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        A₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ p n ∧ p n ≤ A₂ * (Real.log (n : ℝ) / (n : ℝ))) ∧
      (∃ B₁ B₂ : ℝ, 0 < B₁ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        B₁ * (Real.log (n : ℝ) / (n : ℝ)) ≤ err n ∧ err n ≤ B₂ * (Real.log (n : ℝ) / (n : ℝ)))

/-- Example 4.6 (unlabeled `[Degree $d$ vertices]`, `SteinIntro.tex:2220-2246`;
`ISSUE-TYPO-EX4.6` in `docs/SOURCE-ISSUES.md`, correcting `SteinIntro.tex:2240` to
degree-$d$ vertices): in $G \sim G(n, p)$ ($0 < n$, $d < n$, $0 \le p \le 1$), sampling
$G^{(1)}$ from `degreeDCouplingPMF d ⟨0, hn⟩ G` forces $\deg_{G^{(1)}}(v_1) = d$, yields
coupled degree-$d$ indicators $(X_j^{(1)})_{j \ne 1}$ having the conditional distribution
of $(X_j)_{j \ne 1}$ given $X_1 = 1$ whenever $\mathbb{P}(X_1 = 1) > 0$, and gives a
size-bias representation $W^s = \sum_{j \ne 1} X_j^{(1)} + 1$ of the degree-$d$ vertex
count $W = \sum_{i=1}^n X_i$. -/
def Ex4_6 : Prop :=
  ∀ {n d : ℕ} {p : ℝ} (hn : 0 < n),
    d < n →
    0 ≤ p →
    p ≤ 1 →
    let v0 : Fin n := ⟨0, hn⟩
    let P : Measure (SimpleGraph (Fin n)) := erdosRenyi n p
    let Q : Measure (SimpleGraph (Fin n)) :=
      P.bind fun G ↦ (degreeDCouplingPMF d v0 G).toMeasure
    let X : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i G ↦ {H : SimpleGraph (Fin n) | (H.neighborSet i).ncard = d}.indicator 1 G
    let W : SimpleGraph (Fin n) → ℝ := fun G ↦ ∑ i : Fin n, X i G
    let Ws : SimpleGraph (Fin n) → ℝ :=
      fun G1 ↦ (∑ j : {j : Fin n // j ≠ v0}, X j.1 G1) + 1
    (∀ G : SimpleGraph (Fin n), ∀ H ∈ (degreeDCouplingPMF d v0 G).support,
      (H.neighborSet v0).ncard = d) ∧
    (0 < P.real {G | X v0 G = 1} →
      Q.map (fun G1 (j : {j : Fin n // j ≠ v0}) ↦ X j.1 G1) =
        (ProbabilityTheory.cond P {G | X v0 G = 1}).map
          (fun G (j : {j : Fin n // j ≠ v0}) ↦ X j.1 G)) ∧
    IsSizeBias P W Q Ws

/-- Theorem 4.14 (`\label{thm122}`, `SteinIntro.tex:2253-2263`; `ISSUE-THM-4.14` in
`docs/SOURCE-ISSUES.md`): if $X_1, \dots, X_n$ are $\{0, 1\}$-indicator random variables
with $p_i = \mathbb{P}(X_i = 1)$, $W = \sum_{i=1}^n X_i$, and $\lambda = \mathbb{E}[W] =
\sum_{i=1}^n p_i$, $(X_j^{(i)})_{j \ne i}$ has the distribution of $(X_j)_{j \ne i}$
conditional on $X_i = 1$ with $X_j^{(i)} \ge X_j$ a.s. for all $i \ne j$, $I$ is
independent of $(X, X^{(\cdot)})$ with $\mathbb{P}(I = i) = p_i / \lambda$ (so $W^s =
\sum_{j \ne I} X_j^{(I)} + 1$ has the size-bias distribution of $W$), and $Z \sim
\mathrm{Po}(\lambda)$, then $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1,
\lambda^{-1}\}(\mathrm{Var}(W) - \lambda + 2 \sum_{i=1}^n p_i^2)$. -/
def Thm4_14 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℕ)}
    {I : Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℕ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ω ∂P, X j.1 ω ≤ Y i ω j) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P (fun ω ↦ (Ws ω : ℝ)) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ)⁻¹ *
            (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
              2 * ∑ i : Fin n, p i ^ 2))

/-- Theorem 4.15 (`\label{thm123}`, `SteinIntro.tex:2289-2295`): for an Erdős–Rényi random
graph $G \sim G(n, p)$ ($0 \le p \le 1$) and a finite simple graph $H$ on $0 < v_H \le n$
vertices with $e_H$ edges and no isolated vertices, let $W =
\mathrm{subgraphCount}\,H\,n\,G$ be the number of copies of $H$ in $G$ and $\lambda =
\mathbb{E}[W]$. If $Z \sim \mathrm{Po}(\lambda)$, then $\lambda = |\Gamma|\,p^{e_H}$ and
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1,
\lambda^{-1}\}(\mathrm{Var}(W) - \lambda + 2 \lambda p^{e_H})$. -/
def Thm4_15 : Prop :=
  ∀ {V : Type*} [Fintype V] (H : SimpleGraph V)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ},
    0 < Fintype.card V →
    Fintype.card V ≤ n →
    (∀ v : V, ¬ H.IsIsolated v) →
    0 ≤ p →
    p ≤ 1 →
    AEMeasurable G P →
    P.map G = erdosRenyi n p →
    let e_H : ℕ := H.edgeSet.ncard
    let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    ∫ ω, (W ω : ℝ) ∂P = ((subgraphCopies H n).card : ℝ) * p ^ e_H ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ)⁻¹ *
            (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
              2 * (r : ℝ) * p ^ e_H))

open Classical in
/-- Section 4.3.2 Theorem 4.15 proof facts (unlabeled items 1–3 in proof of Theorem 4.15
(`\ref{thm123}`), `SteinIntro.tex:2299-2307`; `ISSUE-SEC4.3.2-EXCH` in
`docs/SOURCE-ISSUES.md`): for $G \sim G(n, p)$ ($0 \le p \le 1$), a finite simple graph $H$
on $0 < v_H \le n$ vertices with $e_H$ edges and no isolated vertices, and any fixed copy
$\alpha \in \Gamma$, setting $X_\beta^{(\alpha)}(G) = X_\beta(G \sqcup \alpha)$ satisfies:
(1) for $p > 0$, $(X_\beta^{(\alpha)})_{\beta \ne \alpha}$ has the distribution of
    $(X_\beta)_{\beta \ne \alpha}$ conditional on $X_\alpha = 1$;
(2) $X_\beta \le X_\beta^{(\alpha)}$ for all $\beta \in \Gamma \setminus \{\alpha\}$;
(3) $\mathbb{E}[X_\alpha] = p^{e_H}$. -/
def Sec4_3_2_subgraph_coupling : Prop :=
  ∀ {V : Type*} [Fintype V] (H : SimpleGraph V)
    {n : ℕ} {p : ℝ} {α : SimpleGraph (Fin n)},
    0 < Fintype.card V →
    Fintype.card V ≤ n →
    (∀ v : V, ¬ H.IsIsolated v) →
    0 ≤ p →
    p ≤ 1 →
    α ∈ subgraphCopies H n →
    let Γ : Finset (SimpleGraph (Fin n)) := subgraphCopies H n
    let e_H : ℕ := H.edgeSet.ncard
    (0 < p →
      (erdosRenyi n p).map
          (fun G (β : {β : SimpleGraph (Fin n) // β ∈ Γ.erase α}) ↦
            subgraphCopyIndicator β.1 (G ⊔ α)) =
        (ProbabilityTheory.cond (erdosRenyi n p) {G | subgraphCopyIndicator α G = 1}).map
          (fun G (β : {β : SimpleGraph (Fin n) // β ∈ Γ.erase α}) ↦
            subgraphCopyIndicator β.1 G)) ∧
    (∀ β ∈ Γ.erase α, ∀ G : SimpleGraph (Fin n),
      subgraphCopyIndicator β G ≤ subgraphCopyIndicator β (G ⊔ α)) ∧
    (∫ G, (subgraphCopyIndicator α G : ℝ) ∂erdosRenyi n p = p ^ e_H)

/-- Corollary 4.16 (`\label{cor123}`, `SteinIntro.tex:2313-2331`): for an Erdős–Rényi random
graph $G \sim G(n, p)$ ($0 \le p \le 1$), a finite simple graph $H$ on $0 < v_H \le n$
vertices with $e_H$ edges and no isolated vertices, and any fixed copy $\alpha \in \Gamma$,
the subgraph count $W = \mathrm{subgraphCount}\,H\,n\,G$ with mean $\lambda =
\mathbb{E}[W]$ has variance $\mathrm{Var}(W) = \lambda(1 - p^{e_H} + \sum_{t=1}^{e_H - 1}
|\Gamma_\alpha^t|(p^t - p^{e_H}))$ (`SteinIntro.tex:2328`) and satisfies
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1, \lambda\}(p^{e_H} +
\sum_{t=1}^{e_H - 1} |\Gamma_\alpha^t|(p^t - p^{e_H}))$ for $Z \sim \mathrm{Po}(\lambda)$. -/
def Cor4_16 : Prop :=
  ∀ {V : Type*} [Fintype V] (H : SimpleGraph V)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {α : SimpleGraph (Fin n)}
    {r : ℝ≥0} {Z : Ω' → ℕ},
    0 < Fintype.card V →
    Fintype.card V ≤ n →
    (∀ v : V, ¬ H.IsIsolated v) →
    0 ≤ p →
    p ≤ 1 →
    α ∈ subgraphCopies H n →
    AEMeasurable G P →
    P.map G = erdosRenyi n p →
    let e_H : ℕ := H.edgeSet.ncard
    let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
    let Γ_t : ℕ → Finset (SimpleGraph (Fin n)) := subgraphCopiesWithDiffEdges H n α
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
        (r : ℝ) * (1 - p ^ e_H +
          ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H)) ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ) *
            (p ^ e_H + ∑ t ∈ Finset.Ico 1 e_H, ((Γ_t t).card : ℝ) * (p ^ t - p ^ e_H)))

/-- Example 4.7 (unlabeled `[Triangles]`, eq. `(4.10)` `\label{124}`,
`SteinIntro.tex:2334-2343`): for triangle counts in $G \sim G(n, p)$ ($n \ge 3$, $0 \le p
\le 1$) with $H = K_3$ (`SimpleGraph.cycleGraph 3`), $e_H = 3$, $|\Gamma| = \binom{n}{3}$,
$|\Gamma_\alpha^1| = 0$ and $|\Gamma_\alpha^2| = 3(n - 3)$ for every $\alpha \in \Gamma$,
$W = \mathrm{subgraphCount}\,(\mathrm{cycleGraph}\,3)\,n\,G$ agrees with `(G.cliqueSet
3).ncard`, $\lambda = \mathbb{E}[W] = \binom{n}{3} p^3$, $\mathrm{Var}(W) = \binom{n}{3}
p^3 (1 - p^3 + 3(n - 3) p^2 (1 - p))$ (matching `Sec3_2_1_triangles_restricted`), and for
$Z \sim \mathrm{Po}(\lambda)$, $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\min\{1, \lambda\}(p^3 + 3(n - 3) p^2 (1 - p))$, which is of order $1 / n$ when $p \asymp 1
/ n$. -/
def Ex4_7 : Prop :=
  (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {α : SimpleGraph (Fin n)}
      {r : ℝ≥0} {Z : Ω' → ℕ},
      3 ≤ n →
      0 ≤ p →
      p ≤ 1 →
      α ∈ subgraphCopies (SimpleGraph.cycleGraph 3) n →
      AEMeasurable G P →
      P.map G = erdosRenyi n p →
      let H := SimpleGraph.cycleGraph 3
      let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
      (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
      AEMeasurable Z P' →
      P'.map Z = poissonLaw r →
      H.edgeSet.ncard = 3 ∧
        (subgraphCopies H n).card = n.choose 3 ∧
        (subgraphCopiesWithDiffEdges H n α 1).card = 0 ∧
        (subgraphCopiesWithDiffEdges H n α 2).card = 3 * (n - 3) ∧
        (∀ H₀ : SimpleGraph (Fin n), subgraphCount H n H₀ = (H₀.cliqueSet 3).ncard) ∧
        ∫ ω, (W ω : ℝ) ∂P = (n.choose 3 : ℝ) * p ^ 3 ∧
        ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
          (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) ∧
        tvDist (P.map W) (P'.map Z) ≤
          ENNReal.ofReal (min 1 (r : ℝ) * (p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)))) ∧
  (∀ {p : ℕ → ℝ} {c₁ c₂ : ℝ},
      0 < c₁ →
      c₁ ≤ c₂ →
      (∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) →
      let lam : ℕ → ℝ := fun n ↦ (n.choose 3 : ℝ) * (p n) ^ 3
      let err : ℕ → ℝ :=
        fun n ↦ min 1 (lam n) * ((p n) ^ 3 + 3 * ((n : ℝ) - 3) * (p n) ^ 2 * (1 - p n))
      ∃ B₁ B₂ : ℝ, 0 < B₁ ∧ 0 < B₂ ∧ ∀ᶠ n : ℕ in Filter.atTop,
        B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ))

/-- Example 4.8 (unlabeled `[k-cycles]`, eq. `(4.11)` `\label{125}`,
`SteinIntro.tex:2344-2366`; `ISSUE-TYPO-4.8` and `ISSUE-TYPO-4.8-PROSE` in
`docs/SOURCE-ISSUES.md`): for $k$-cycle counts in $G \sim G(n, p)$ with $H =
\mathrm{SimpleGraph.cycleGraph}\,k$ ($k \ge 3$), there exist constants $c_t > 0$ and $C_k >
0$ such that for all $n \ge k$, all $\alpha \in \Gamma$, and all $1 \le t \le k - 1$,
$|\Gamma_\alpha^t| \le \binom{k}{k - t} c_t n^{t - 1} \le C_k n^{t - 1}$; for $0 \le p \le
1$ and $Z \sim \mathrm{Po}(\lambda)$, $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\min\{1, \lambda\}(p^k + C_k p \sum_{t=1}^{k-1} (n p)^{t - 1})$; moreover, $|\Gamma| =
\binom{n}{k} \frac{(k - 1)!}{2}$ (`ISSUE-TYPO-4.8`: `SteinIntro.tex:2361` prints an extra
factor $p^k$ on the right-hand side of $|\Gamma|$), $\lambda = |\Gamma| p^k = \binom{n}{k}
\frac{(k - 1)!}{2} p^k$, $\lambda$ is of order $(np)^k$ (`SteinIntro.tex:2364`), and when
$p \asymp 1 / n$, $\lambda \asymp 1$ and `(4.11)` is of order $1 / n$. -/
def Ex4_8 : Prop :=
  ∀ {k : ℕ}, 3 ≤ k →
    ∃ (c : ℕ → ℝ) (C_k : ℝ), (∀ t, 0 < c t) ∧ 0 < C_k ∧
      (∀ {n : ℕ} {α : SimpleGraph (Fin n)},
        k ≤ n →
        α ∈ subgraphCopies (SimpleGraph.cycleGraph k) n →
        ∀ t ∈ Finset.Ico 1 k,
          ((subgraphCopiesWithDiffEdges (SimpleGraph.cycleGraph k) n α t).card : ℝ) ≤
              (k.choose (k - t) : ℝ) * c t * (n : ℝ) ^ (t - 1) ∧
            (k.choose (k - t) : ℝ) * c t * (n : ℝ) ^ (t - 1) ≤ C_k * (n : ℝ) ^ (t - 1)) ∧
      (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ},
        k ≤ n →
        0 ≤ p →
        p ≤ 1 →
        AEMeasurable G P →
        P.map G = erdosRenyi n p →
        let H := SimpleGraph.cycleGraph k
        let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
        (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
        AEMeasurable Z P' →
        P'.map Z = poissonLaw r →
        (subgraphCopies H n).card = n.choose k * (k - 1).factorial / 2 ∧
          ∫ ω, (W ω : ℝ) ∂P =
            (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * p ^ k ∧
          (2 * k ≤ n →
            ((n : ℝ) * p) ^ k / (2 * (k : ℝ) * 2 ^ k) ≤ (r : ℝ) ∧
              (r : ℝ) ≤ ((n : ℝ) * p) ^ k / (2 * (k : ℝ))) ∧
          tvDist (P.map W) (P'.map Z) ≤
            ENNReal.ofReal
              (min 1 (r : ℝ) *
                (p ^ k + C_k * p * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p) ^ (t - 1)))) ∧
      (∀ {p : ℕ → ℝ} {c₁ c₂ : ℝ},
        0 < c₁ →
        c₁ ≤ c₂ →
        (∀ᶠ n : ℕ in Filter.atTop,
          0 ≤ p n ∧ p n ≤ 1 ∧ c₁ / (n : ℝ) ≤ p n ∧ p n ≤ c₂ / (n : ℝ)) →
        let lam : ℕ → ℝ :=
          fun n ↦ (n.choose k : ℝ) * ((k - 1).factorial : ℝ) / 2 * (p n) ^ k
        let err : ℕ → ℝ :=
          fun n ↦ min 1 (lam n) *
            ((p n) ^ k + C_k * p n * ∑ t ∈ Finset.Ico 1 k, ((n : ℝ) * p n) ^ (t - 1))
        ∃ L₁ L₂ B₁ B₂ : ℝ, 0 < L₁ ∧ 0 < L₂ ∧ 0 < B₁ ∧ 0 < B₂ ∧
          ∀ᶠ n : ℕ in Filter.atTop,
            (L₁ ≤ lam n ∧ lam n ≤ L₂) ∧ (B₁ / (n : ℝ) ≤ err n ∧ err n ≤ B₂ / (n : ℝ)))

/-- Theorem 4.17, corrected (`\label{thm124}`, `SteinIntro.tex:2382-2390`; `ISSUE-4.17` and
`ISSUE-TYPO-4.17` in `docs/SOURCE-ISSUES.md`): let $\mathbf{Y} = (Y_j)_{j=1}^N$ be
independent $\{0, 1\}$-indicators and let $f_1, \dots, f_n : \{0, 1\}^N \to \{0, 1\}$ be
either all increasing (`MonotoneOn`) or all decreasing (`AntitoneOn`) on $\{0, 1\}^N$. For
$X_i = f_i(\mathbf{Y})$, $p_i = \mathbb{P}(X_i = 1)$, $W = \sum_{i=1}^n X_i$, $\lambda =
\mathbb{E}[W] = \sum_{i=1}^n p_i$, and $Z \sim \mathrm{Po}(\lambda)$,
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1,
\lambda^{-1}\}(\mathrm{Var}(W) - \lambda + 2 \sum_{i=1}^n p_i^2)$.

Difference from printed result (`ISSUE-4.17`): disambiguates *"assume $X_1, \ldots, X_n$ are
increasing or decreasing functions from $\{0,1\}^N$ into $\{0, 1\}$"*
(`SteinIntro.tex:2383-2384`) to the common-direction reading (all increasing or all decreasing
on $\{0, 1\}^N$), because the individual-direction reading (`∀ i, MonotoneOn ... ∨ AntitoneOn
...`) is false (`not_Thm4_17_printed`). -/
def Thm4_17_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {N n : ℕ} {Y : Fin N → Ω → ℕ} {f : Fin n → (Fin N → ℕ) → ℕ}
    {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ j : Fin N, AEMeasurable (Y j) P) →
    (∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1) →
    ProbabilityTheory.iIndepFun Y P →
    (∀ i : Fin n, ∀ y : Fin N → ℕ,
      (∀ j : Fin N, y j ≤ 1) → f i y = 0 ∨ f i y = 1) →
    ((∀ i : Fin n, MonotoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) ∨
      (∀ i : Fin n, AntitoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1})) →
    let X : Fin n → Ω → ℕ := fun i ω ↦ f i (fun j ↦ Y j ω)
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    (r : ℝ) = ∑ i : Fin n, p i →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
            2 * ∑ i : Fin n, p i ^ 2))

/-- Theorem 4.17 proof implicit coupling existence, corrected (unlabeled prose in proof of
Theorem 4.17 (`\ref{thm124}`), `SteinIntro.tex:2392-2394`; `ISSUE-4.17` in
`docs/SOURCE-ISSUES.md`): under the common-direction hypotheses of `Thm4_17_corrected` with
$\lambda = \sum_{i=1}^n p_i > 0$, for every $i$ every increasing $\{0, 1\}$-indicator $\phi
: \mathbb{N}^n \to \mathbb{R}$ satisfies $\mathrm{Cov}(X_i(\mathbf{Y}),
\phi(\mathbf{X}(\mathbf{Y}))) \ge 0$, and there exists a probability space
$(\tilde{\Omega}, \tilde{P})$ carrying $(\tilde{X}, \tilde{Y}, \tilde{I})$ with
$\tilde{\mathbf{X}} \stackrel{d}{=} \mathbf{X}$ satisfying all hypotheses of Theorem 4.14
(`Thm4_14`), including `IsSizeBias P W P_tilde Ws_tilde`.

Difference from printed result (`ISSUE-4.17`): requires a common monotonicity direction across
$f_1, \dots, f_n$ (mixed directions fail FKG covariance positivity) and $\lambda > 0$ so the
index weights $p_i / \lambda$ form a probability law on `Fin n`. -/
def Thm4_17_implicit_coupling_corrected : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N n : ℕ} {Y : Fin N → Ω → ℕ} {f : Fin n → (Fin N → ℕ) → ℕ}
    {r : ℝ≥0},
    (∀ j : Fin N, AEMeasurable (Y j) P) →
    (∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1) →
    ProbabilityTheory.iIndepFun Y P →
    (∀ i : Fin n, ∀ y : Fin N → ℕ,
      (∀ j : Fin N, y j ≤ 1) → f i y = 0 ∨ f i y = 1) →
    ((∀ i : Fin n, MonotoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) ∨
      (∀ i : Fin n, AntitoneOn (f i) {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1})) →
    let X : Fin n → Ω → ℕ := fun i ω ↦ f i (fun j ↦ Y j ω)
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ (i : Fin n) (φ : (Fin n → ℕ) → ℝ),
      Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
        0 ≤ ProbabilityTheory.covariance
          (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X j ω)) P) ∧
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ)
      (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ))
      (Ic : Ωc → Fin n),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, ∀ᵐ ωc ∂Pc, Xc i ωc = 0 ∨ Xc i ωc = 1) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      (∀ i : Fin n,
        0 < p i →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond Pc {ωc | Xc i ωc = 1}).map
            (fun ωc (j : {j : Fin n // j ≠ i}) ↦ Xc j.1 ωc)) ∧
      Measurable Ic ∧
      (∀ i : Fin n, Pc.real (Ic ⁻¹' {i}) = p i / (r : ℝ)) ∧
      ProbabilityTheory.IndepFun Ic (fun ωc ↦ (fun i ↦ Xc i ωc, fun i ↦ Yc i ωc)) Pc ∧
      (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ωc ∂Pc, Xc j.1 ωc ≤ Yc i ωc j) ∧
      IsSizeBias P (fun ω ↦ (W ω : ℝ)) Pc
        (fun ωc ↦ ((∑ j : {j : Fin n // j ≠ Ic ωc}, Yc (Ic ωc) ωc j) + 1 : ℕ)))

/-- Theorem 4.17 proof composition monotonicity step, corrected (unlabeled prose in proof of
Theorem 4.17 (`\ref{thm124}`), `SteinIntro.tex:2395-2396`; `ISSUE-4.17` in
`docs/SOURCE-ISSUES.md`): on the Boolean cube $\{0, 1\}^N$, if $f_1, \dots, f_n :
\mathbb{N}^N \to \mathbb{N}$ are all increasing (`MonotoneOn`) and $\phi : \mathbb{N}^n \to
\mathbb{R}$ is increasing (`Monotone`), then $\phi \circ (f_1, \dots, f_n)$ is increasing
(`MonotoneOn`) on $\{0, 1\}^N$; if $f_1, \dots, f_n$ are all decreasing (`AntitoneOn`) on
$\{0, 1\}^N$ and $\phi$ is increasing, then $\phi \circ (f_1, \dots, f_n)$ is decreasing
(`AntitoneOn`) on $\{0, 1\}^N$ (matching the common direction of $f_i$ required by
`Thm4_17_fkg` at `SteinIntro.tex:2398-2401`).

Difference from printed result (`ISSUE-4.17`): requires $f_1, \dots, f_n$ to share a common
monotonicity direction; under mixed directions, $\phi \circ \mathbf{f}$ need not be monotone in
either direction on $\{0, 1\}^N$ (`not_Thm4_17_comp_monotone_printed`). -/
def Thm4_17_comp_monotone_corrected : Prop :=
  ∀ {N n : ℕ} {f : Fin n → (Fin N → ℕ) → ℕ} {φ : (Fin n → ℕ) → ℝ},
    Monotone φ →
    let cube : Set (Fin N → ℕ) := {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}
    ((∀ i : Fin n, MonotoneOn (f i) cube) →
      MonotoneOn (fun y ↦ φ (fun i ↦ f i y)) cube) ∧
    ((∀ i : Fin n, AntitoneOn (f i) cube) →
      AntitoneOn (fun y ↦ φ (fun i ↦ f i y)) cube)

/-- FKG / Harris–Kleitman correlation inequality for independent $\{0, 1\}$-indicators
(unlabeled prose in proof of Theorem 4.17 (`\ref{thm124}`), `SteinIntro.tex:2395-2401`,
cited from `[lig05]` Chapter 2 and proved from scratch): if $\mathbf{Y} = (Y_j)_{j=1}^N$
are independent $\{0, 1\}$-indicators and $g, h : \{0, 1\}^N \to \mathbb{R}$ are both
increasing (`MonotoneOn`) or both decreasing (`AntitoneOn`) on $\{0, 1\}^N$, then
$\mathbb{E}[g(\mathbf{Y})]\,\mathbb{E}[h(\mathbf{Y})] \le
\mathbb{E}[g(\mathbf{Y})\,h(\mathbf{Y})]$. -/
def Thm4_17_fkg : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} {Y : Fin N → Ω → ℕ} {g h : (Fin N → ℕ) → ℝ},
    (∀ j : Fin N, AEMeasurable (Y j) P) →
    (∀ j : Fin N, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1) →
    ProbabilityTheory.iIndepFun Y P →
    ((MonotoneOn g {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} ∧
        MonotoneOn h {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1}) ∨
      (AntitoneOn g {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1} ∧
        AntitoneOn h {y : Fin N → ℕ | ∀ j : Fin N, y j ≤ 1})) →
    (∫ ω, g (fun j ↦ Y j ω) ∂P) * (∫ ω, h (fun j ↦ Y j ω) ∂P) ≤
      ∫ ω, g (fun j ↦ Y j ω) * h (fun j ↦ Y j ω) ∂P

/-- Lemma 4.18 (`\label{lem121}`, items `\label{i121}`–`\label{i123}`,
`SteinIntro.tex:2404-2423`): for a vector $\mathbf{X} = (X_1, \dots, X_n)$ of $\{0,
1\}$-indicators with $\mathbb{P}(X_i = 1) \gt 0$ and $\mathbf{X}^{(i)} \stackrel{d}{=}
(\mathbf{X} \mid X_i = 1)$, the following are equivalent:
(1) there exists a coupling $(\hat{\mathbf{X}}, \hat{\mathbf{X}}^{(i)})$ of $\mathbf{X}$ and
    $\mathbf{X}^{(i)}$ such that $\hat{X}_j \le \hat{X}_j^{(i)}$ almost surely for all $j$;
(2) for every increasing indicator function $\phi : \mathbb{N}^n \to \mathbb{R}$,
    $\mathbb{E}[\phi(\mathbf{X})] \le \mathbb{E}[\phi(\mathbf{X}^{(i)})]$;
(3) for every increasing indicator function $\phi : \mathbb{N}^n \to \mathbb{R}$, $0 \le
    \mathrm{Cov}(X_i, \phi(\mathbf{X}))$. -/
def Lem4_18 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ} {X_cond : Fin n → Ω' → ℕ} (i : Fin n),
    (∀ j : Fin n, Measurable (X j)) →
    (∀ j : Fin n, ∀ᵐ ω ∂P, X j ω = 0 ∨ X j ω = 1) →
    (∀ j : Fin n, Measurable (X_cond j)) →
    0 < P.real {ω | X i ω = 1} →
    P'.map (fun ω' j ↦ X_cond j ω') =
      (ProbabilityTheory.cond P {ω | X i ω = 1}).map (fun ω j ↦ X j ω) →
    let c1 : Prop :=
      ∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
        (Xc Xc_cond : Ωc → Fin n → ℕ),
        Measurable Xc ∧ Measurable Xc_cond ∧
        Pc.map Xc = P.map (fun ω j ↦ X j ω) ∧
        Pc.map Xc_cond = P'.map (fun ω' j ↦ X_cond j ω') ∧
        ∀ j : Fin n, ∀ᵐ ωc ∂Pc, Xc ωc j ≤ Xc_cond ωc j
    let c2 : Prop :=
      ∀ φ : (Fin n → ℕ) → ℝ,
        Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
          ∫ ω, φ (fun j ↦ X j ω) ∂P ≤ ∫ ω', φ (fun j ↦ X_cond j ω') ∂P'
    let c3 : Prop :=
      ∀ φ : (Fin n → ℕ) → ℝ,
        Monotone φ → (∀ x : Fin n → ℕ, φ x = 0 ∨ φ x = 1) →
          0 ≤ ProbabilityTheory.covariance
            (fun ω ↦ (X i ω : ℝ)) (fun ω ↦ φ (fun j ↦ X j ω)) P
    (c1 ↔ c2) ∧ (c2 ↔ c3)

/-- One-dimensional Strassen theorem (unlabeled prose in proof of Lemma 4.18 (`\ref{lem121}`),
`SteinIntro.tex:2415-2417`, cited from `[lig05]` and proved from scratch): for real-valued
random variables $X$ and $Y$, there exists a coupling $(\hat{X}, \hat{Y})$ with
$\mathcal{L}(\hat{X}) = \mathcal{L}(X)$, $\mathcal{L}(\hat{Y}) = \mathcal{L}(Y)$, and
$\hat{Y} \le \hat{X}$ almost surely if and only if $F_X(z) \le F_Y(z)$ ($\mathbb{P}(X \le
z) \le \mathbb{P}(Y \le z)$) for all $z \in \mathbb{R}$. -/
def Lem4_18_strassen_1d : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : Ω' → ℝ},
    AEMeasurable X P →
    AEMeasurable Y P' →
    ((∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
        (Xh Yh : Ωc → ℝ),
        Measurable Xh ∧ Measurable Yh ∧
        Pc.map Xh = P.map X ∧ Pc.map Yh = P'.map Y ∧
        ∀ᵐ ωc ∂Pc, Yh ωc ≤ Xh ωc) ↔
      ∀ z : ℝ, P.real {ω | X ω ≤ z} ≤ P'.real {ω' | Y ω' ≤ z})

/-- Example 4.10 (unlabeled `[Subgraph counts]`, `SteinIntro.tex:2424-2427`): for any template
graph $H$ and $G \sim G(n, p)$ ($0 \le p \le 1$), each copy indicator $I_\alpha = \prod_{e
\in E(\alpha)} Y_e$ is an increasing (`Monotone`) function of the edge indicators, and
Theorem 4.17 immediately recovers the Theorem 4.15 bound $d_{\mathrm{TV}}(\mathcal{L}(W),
\mathcal{L}(Z)) \le \min\{1, \lambda^{-1}\}(\mathrm{Var}(W) - \lambda + 2 \lambda
p^{e(H)})$ without constructing an explicit coupling. -/
def Ex4_10 : Prop :=
  ∀ {V : Type*} [Fintype V] (H : SimpleGraph V)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z : Ω' → ℕ},
    0 ≤ p →
    p ≤ 1 →
    AEMeasurable G P →
    P.map G = erdosRenyi n p →
    let e_H : ℕ := H.edgeSet.ncard
    let W : Ω → ℕ := fun ω ↦ subgraphCount H n (G ω)
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    (∀ α ∈ subgraphCopies H n,
      Monotone (subgraphEdgeFn α) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        subgraphCopyIndicator α G₀ =
          subgraphEdgeFn α (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀)) ∧
    ∫ ω, (W ω : ℝ) ∂P = ((subgraphCopies H n).card : ℝ) * p ^ e_H ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ)⁻¹ *
          (ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P - (r : ℝ) +
            2 * (r : ℝ) * p ^ e_H))

open Classical in
/-- Example 4.11 (unlabeled `[Large degree vertices]`, `SteinIntro.tex:2428-2439`, citing
`[bhj92]` §5.2): for $G \sim G(n, p)$ with $2 \le n$, $d \lt n$, and $0 \lt p \le 1$, let
$W = \sum_{v=1}^n \mathbb{I}[\deg(v) \ge d]$, $q_1 = \sum_{k=d}^{n-1} \binom{n-1}{k} p^k (1
- p)^{n-1-k}$, and $Z_1 \sim \mathrm{Po}(n q_1)$. Then each indicator $\mathbb{I}[\deg(v)
\ge d]$ is an increasing function of the edge indicators, $(n - 1) p q_1 \gt 0$,
$\mathbb{E}[W] = n q_1$, and $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z_1)) \le
\frac{d^2 (1 - p) [\binom{n-1}{d} p^d (1 - p)^{n-1-d}]^2}{(n - 1) p q_1} + q_1$. (The
conditions $2 \le n$, $d \lt n$, and $0 \lt p$ guard the denominator $(n - 1) p q_1$.) -/
def Ex4_11 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n d : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z₁ : Ω' → ℕ},
    2 ≤ n →
    d < n →
    0 < p →
    p ≤ 1 →
    AEMeasurable G P →
    P.map G = erdosRenyi n p →
    let q₁ : ℝ :=
      ∑ k ∈ Finset.Ico d n, ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k)
    let W : Ω → ℕ := fun ω ↦ ∑ v : Fin n, if d ≤ (G ω).degree v then 1 else 0
    (r : ℝ) = (n : ℝ) * q₁ →
    AEMeasurable Z₁ P' →
    P'.map Z₁ = poissonLaw r →
    (∀ v : Fin n,
      Monotone (largeDegEdgeFn v d) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        largeDegEdgeFn v d (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) =
          if d ≤ G₀.degree v then 1 else 0) ∧
    0 < ((n : ℝ) - 1) * p * q₁ ∧
    ∫ ω, (W ω : ℝ) ∂P = (n : ℝ) * q₁ ∧
    tvDist (P.map W) (P'.map Z₁) ≤
      ENNReal.ofReal
        (((d : ℝ) ^ 2 * (1 - p) *
            (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
          (((n : ℝ) - 1) * p * q₁) + q₁)

open Classical in
/-- Example 4.12 (unlabeled `[Small degree vertices]`, `SteinIntro.tex:2440-2449`, citing
`[bhj92]` §5.2): for $G \sim G(n, p)$ with $2 \le n$, $d \in \mathbb{N}$, and $0 \le p \lt
1$, let $W' = \sum_{v=1}^n \mathbb{I}[\deg(v) \le d]$, $q_2 = \sum_{k=0}^d \binom{n-1}{k}
p^k (1 - p)^{n-1-k}$, and $Z_2 \sim \mathrm{Po}(n q_2)$. Then each indicator
$\mathbb{I}[\deg(v) \le d]$ is a decreasing function of the edge indicators, $(n - 1)(1 -
p) q_2 \gt 0$, $\mathbb{E}[W'] = n q_2$, and $d_{\mathrm{TV}}(\mathcal{L}(W'),
\mathcal{L}(Z_2)) \le \frac{(n - d - 1)^2 p [\binom{n-1}{d} p^d (1 - p)^{n-1-d}]^2}{(n - 1)
(1 - p) q_2} + q_2$. -/
def Ex4_12 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n d : ℕ} {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {r : ℝ≥0} {Z₂ : Ω' → ℕ},
    2 ≤ n →
    0 ≤ p →
    p < 1 →
    AEMeasurable G P →
    P.map G = erdosRenyi n p →
    let q₂ : ℝ :=
      ∑ k ∈ Finset.range (d + 1), ((n - 1).choose k : ℝ) * p ^ k * (1 - p) ^ (n - 1 - k)
    let W' : Ω → ℕ := fun ω ↦ ∑ v : Fin n, if (G ω).degree v ≤ d then 1 else 0
    (r : ℝ) = (n : ℝ) * q₂ →
    AEMeasurable Z₂ P' →
    P'.map Z₂ = poissonLaw r →
    (∀ v : Fin n,
      Antitone (smallDegEdgeFn v d) ∧
      ∀ G₀ : SimpleGraph (Fin n),
        smallDegEdgeFn v d (fun j ↦ edgeIndNat ((Fintype.equivFin (EdgePair n)).symm j) G₀) =
          if G₀.degree v ≤ d then 1 else 0) ∧
    0 < ((n : ℝ) - 1) * (1 - p) * q₂ ∧
    ∫ ω, (W' ω : ℝ) ∂P = (n : ℝ) * q₂ ∧
    tvDist (P.map W') (P'.map Z₂) ≤
      ENNReal.ofReal
        ((((n : ℝ) - (d : ℝ) - 1) ^ 2 * p *
            (((n - 1).choose d : ℝ) * p ^ d * (1 - p) ^ (n - 1 - d)) ^ 2) /
          (((n : ℝ) - 1) * (1 - p) * q₂) + q₂)

/-- Theorem 4.19 (`\label{thm125}`, `SteinIntro.tex:2455-2465`): let $X_1, \dots, X_n$ be $\{0,
1\}$-indicator random variables with $p_i = \mathbb{P}(X_i = 1)$, $W = \sum_{i=1}^n X_i$,
and $\lambda = \mathbb{E}[W] = \sum_{i=1}^n p_i$. If $(X_j^{(i)})_{j \ne i}$ has the
distribution of $(X_j)_{j \ne i}$ conditional on $X_i = 1$, $I$ is independent of $(X,
X^{(\cdot)})$ with $\mathbb{P}(I = i) = p_i / \lambda$, $X_j^{(i)} \le X_j$ almost surely
for all $j \ne i$, and $Z \sim \mathrm{Po}(\lambda)$, then $W^s = \sum_{j \ne I} X_j^{(I)}
+ 1$ has the size-bias distribution of $W$ and $d_{\mathrm{TV}}(\mathcal{L}(W),
\mathcal{L}(Z)) \le \min\{1, \lambda\}(1 - \operatorname{Var}(W) / \lambda)$. -/
def Thm4_19 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℕ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℕ)} {I : Ω → Fin n}
    {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    let p : Fin n → ℝ := fun i ↦ P.real {ω | X i ω = 1}
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, (Y (I ω) ω j : ℝ)) + 1
    (r : ℝ) = ∑ i : Fin n, p i →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    (∀ i : Fin n, ∀ j : {j : Fin n // j ≠ i}, ∀ᵐ ω ∂P, Y i ω j ≤ X j.1 ω) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    IsSizeBias P (fun ω ↦ (W ω : ℝ)) P Ws ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 (r : ℝ) *
            (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ)))

/-- Example 4.13, size-bias coupling, exchangeability, and monotonicity (unlabeled
`[Hypergeometric distribution]`, `SteinIntro.tex:2487-2498`): for a uniform $m$-subset $S$
of `Fin N` ($1 \le n \le N$, $1 \le m \le N$, with red balls `{0, …, n - 1}`) and an
independent auxiliary uniform index $U \in \mathrm{Fin}\,m$, the red-ball indicators
$(X_i(S))_{i=0}^{n-1}$ are exchangeable, keeping $S$ if ball $0 \in S$ and otherwise
replacing the $U$-th element of $S$ (in canonical order) by ball $0$ yields $S'$ whose
remaining indicators $(X_j(S'))_{j \ne 0}$ have the conditional distribution of
$(X_j(S))_{j \ne 0}$ given $X_0(S) = 1$, satisfy $X_j(S') \le X_j(S)$ everywhere for $j \ne
0$, and give a size-bias version $W^s = \sum_{j \ne 0} X_j(S') + 1$ of $W =
\sum_{i=0}^{n-1} X_i(S)$. -/
def Ex4_13_sizeBias : Prop :=
  ∀ {N n m : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) (hm1 : 1 ≤ m) (_hmN : m ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)} {U : Ω → Fin m},
    (∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A}) →
    (∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) →
    Measurable U →
    ProbabilityTheory.IndepFun (fun ω (j : Fin N) ↦ decide (j ∈ S ω)) U P →
    P.map U = (@PMF.uniformOfFintype (Fin m) inferInstance ⟨⟨0, hm1⟩⟩).toMeasure →
    let b₀ : Fin N := ⟨0, lt_of_lt_of_le hn1 hnN⟩
    let S' : Ω → Finset (Fin N) := fun ω ↦
      if b₀ ∈ S ω then S ω
      else if hcard : (S ω).card = m then
        insert b₀ ((S ω).erase ((S ω).orderEmbOfFin hcard (U ω)))
      else S ω
    let X : Fin n → Finset (Fin N) → ℕ :=
      fun i A ↦ if Fin.castLE hnN i ∈ A then 1 else 0
    let i₀ : Fin n := ⟨0, hn1⟩
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i (S ω) : ℝ)
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ i₀}, (X j.1 (S' ω) : ℝ)) + 1
    IsExchangeableTuple P (fun i ω ↦ X i (S ω)) ∧
      P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S' ω)) =
        (ProbabilityTheory.cond P {ω | X i₀ (S ω) = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 (S ω)) ∧
      (∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i₀}, X j.1 (S' ω) ≤ X j.1 (S ω)) ∧
      IsSizeBias P W P Ws

/-- Example 4.13, corrected moment formulas (unlabeled `[Hypergeometric distribution]`,
`SteinIntro.tex:2499-2501`; `ISSUE-TYPO-4.13` and `ISSUE-4.13` in `docs/SOURCE-ISSUES.md`):
for the number $W$ of red balls in a uniform $m$-sample without replacement from $N$ balls
containing $n$ red balls ($1 \le n \le N$, $1 \le m \le N$), $\mathbb{E}[W] = n m / N$, and
when $2 \le N$, $\operatorname{Var}(W) = \frac{n m (N - n)(N - m)}{N^2 (N - 1)}$.

Difference from printed result (`ISSUE-TYPO-4.13`, `ISSUE-4.13`): replaces the misprinted
factor $(n - m)$ in the variance display at `SteinIntro.tex:2500` by $(N - m)$
(`not_Ex4_13_var_printed`), and assumes $2 \le N$ for the variance formula to avoid division by
$N - 1 = 0$ at $N = 1$. -/
def Ex4_13_moments_corrected : Prop :=
  ∀ {N n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)},
    1 ≤ n →
    n ≤ N →
    1 ≤ m →
    m ≤ N →
    (∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A}) →
    (∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) →
    let W : Ω → ℝ := fun ω ↦ (((S ω).filter fun j : Fin N ↦ j.1 < n).card : ℝ)
    ∫ ω, W ω ∂P = (n : ℝ) * (m : ℝ) / (N : ℝ) ∧
      (2 ≤ N →
        ProbabilityTheory.variance W P =
          (n : ℝ) * (m : ℝ) * ((N : ℝ) - (n : ℝ)) * ((N : ℝ) - (m : ℝ)) /
            ((N : ℝ) ^ 2 * ((N : ℝ) - 1)))

/-- Example 4.13, restricted to $2 \le N$ (unlabeled `[Hypergeometric distribution]`,
`SteinIntro.tex:2480-2505`; `ISSUE-4.13` and `ISSUE-TYPO-4.13` in `docs/SOURCE-ISSUES.md`):
for the hypergeometric red-ball count $W$ with $2 \le N$, $1 \le n \le N$, $1 \le m \le N$,
and $Z \sim \mathrm{Po}(nm / N)$, $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\min\{1, \frac{nm}{N}\} (\frac{n}{N - 1} + \frac{m}{N - 1} - \frac{nm}{N(N - 1)} -
\frac{1}{N - 1})$.

Difference from printed result (`ISSUE-4.13`): adds the domain guard $2 \le N$ (printed text
states only $1 \le n \le N$ and $1 \le m \le N$), because every fraction in the displayed bound
at `SteinIntro.tex:2504` divides by $N - 1$ (`0 / 0` at $N = 1$). -/
def Ex4_13_restricted : Prop :=
  ∀ {N n m : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {S : Ω → Finset (Fin N)} {r : ℝ≥0} {Z : Ω' → ℕ},
    2 ≤ N →
    1 ≤ n →
    n ≤ N →
    1 ≤ m →
    m ≤ N →
    (∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A}) →
    (∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) →
    (r : ℝ) = (n : ℝ) * (m : ℝ) / (N : ℝ) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    let W : Ω → ℕ := fun ω ↦ ((S ω).filter fun j : Fin N ↦ j.1 < n).card
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 ((n : ℝ) * (m : ℝ) / (N : ℝ)) *
          ((n : ℝ) / ((N : ℝ) - 1) + (m : ℝ) / ((N : ℝ) - 1) -
            (n : ℝ) * (m : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) - 1 / ((N : ℝ) - 1)))

/-- Remark 4.14 (unlabeled, `SteinIntro.tex:2506-2510`, proving from scratch the Harper–Pitman
representation cited from `[pit97]`): for any $1 \le n \le N$ and $1 \le m \le N$, the
hypergeometric red-ball count $W$ has the same distribution as $\sum_{i=1}^n B_i$ for some
independent $\{0, 1\}$ indicators $B_1, \dots, B_n$, and for $2 \le N$ applying Theorem
4.19 to $(B_1, \dots, B_n)$ recovers the bound of `Ex4_13_restricted`. -/
def Rem4_14 : Prop :=
  ∀ {N n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Ω → Finset (Fin N)},
    1 ≤ n →
    n ≤ N →
    1 ≤ m →
    m ≤ N →
    (∀ A : Finset (Fin N), MeasurableSet {ω | S ω = A}) →
    (∀ A ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
      P.real {ω | S ω = A} = 1 / (N.choose m : ℝ)) →
    let W : Ω → ℕ := fun ω ↦ ((S ω).filter fun j : Fin N ↦ j.1 < n).card
    ∃ (Ωb : Type) (_ : MeasurableSpace Ωb) (Pb : Measure Ωb) (_ : IsProbabilityMeasure Pb)
      (B : Fin n → Ωb → ℕ),
      (∀ i : Fin n, Measurable (B i)) ∧
      (∀ i : Fin n, ∀ᵐ ωb ∂Pb, B i ωb = 0 ∨ B i ωb = 1) ∧
      ProbabilityTheory.iIndepFun B Pb ∧
      Pb.map (fun ωb ↦ ∑ i : Fin n, B i ωb) = P.map W ∧
      (∀ (r : ℝ≥0), 2 ≤ N → (r : ℝ) = (n : ℝ) * (m : ℝ) / (N : ℝ) →
        tvDist (Pb.map (fun ωb ↦ ∑ i : Fin n, B i ωb)) (poissonLaw r) ≤
          ENNReal.ofReal
            (min 1 ((n : ℝ) * (m : ℝ) / (N : ℝ)) *
              ((n : ℝ) / ((N : ℝ) - 1) + (m : ℝ) / ((N : ℝ) - 1) -
                (n : ℝ) * (m : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) - 1 / ((N : ℝ) - 1))))

/-- Example 4.15, full-collection event equivalence (`\label{ex123}`,
`SteinIntro.tex:2522-2525`, `SteinIntro.tex:2512`): when $k$ balls are placed into $n$
boxes via `b : Fin k → Fin n`, the number of empty boxes $W = \sum_{i=1}^n
\mathbf{1}[\forall r,\,b(r) \ne i]$ equals $0$ if and only if every box receives at least
one ball (`Function.Surjective b`). -/
def Ex4_15_allTypes_iff : Prop :=
  ∀ {n k : ℕ} (b : Fin k → Fin n),
    (∑ i : Fin n, (if ∀ r : Fin k, b r ≠ i then (1 : ℕ) else 0)) = 0 ↔ Function.Surjective b

/-- Example 4.15, size-bias coupling, exchangeability, and monotonicity (`\label{ex123}`,
`SteinIntro.tex:2529-2539`, `SteinIntro.tex:2512`): for $2 \le n$ boxes and $k$ independent
uniform ball placements `B : Fin k → Ω → Fin n`, the empty-box indicators
$(X_i)_{i=0}^{n-1}$ are exchangeable, and redirecting every ball in box $0$ uniformly among
`{1, …, n - 1}` yields $(X_j')_{j \ne 0}$ with the conditional law of $(X_j)_{j \ne 0}$
given $X_0 = 1$, $X_j' \le X_j$ everywhere for $j \ne 0$, and size-bias coupling $W^s =
\sum_{j \ne 0} X_j' + 1$ of $W = \sum_{i=0}^{n-1} X_i$. -/
def Ex4_15_sizeBias : Prop :=
  ∀ {n k : ℕ} (hn : 2 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {B : Fin k → Ω → Fin n}
    {R : Fin k → Ω → {j : Fin n // j ≠ ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩}},
    (∀ r : Fin k, Measurable (B r)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ r : Fin k, ∀ i : Fin n, P.real {ω | B r ω = i} = 1 / (n : ℝ)) →
    (∀ r : Fin k, Measurable (R r)) →
    ProbabilityTheory.iIndepFun R P →
    (∀ r : Fin k, ∀ j : {j : Fin n // j ≠ ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩},
      P.real {ω | R r ω = j} = 1 / ((n : ℝ) - 1)) →
    ProbabilityTheory.IndepFun (fun ω r ↦ B r ω) (fun ω r ↦ R r ω) P →
    let i₀ : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_two hn⟩
    let B' : Fin k → Ω → Fin n := fun r ω ↦ if B r ω = i₀ then (R r ω).1 else B r ω
    let X : Fin n → Ω → ℕ := fun i ω ↦ if ∀ r : Fin k, B r ω ≠ i then 1 else 0
    let X' : Fin n → Ω → ℕ := fun i ω ↦ if ∀ r : Fin k, B' r ω ≠ i then 1 else 0
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω : ℝ)
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ i₀}, (X' j.1 ω : ℝ)) + 1
    IsExchangeableTuple P X ∧
      P.map (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X' j.1 ω) =
        (ProbabilityTheory.cond P {ω | X i₀ ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i₀}) ↦ X j.1 ω) ∧
      (∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i₀}, X' j.1 ω ≤ X j.1 ω) ∧
      IsSizeBias P W P Ws

/-- Example 4.15, restricted to $2 \le n$ (`\label{ex123}`, eq. `(4.13)` `\label{129}`,
`SteinIntro.tex:2526-2551`, `SteinIntro.tex:2512`; `ISSUE-4.15` in
`docs/SOURCE-ISSUES.md`): for $k$ balls tossed independently and uniformly into $n \ge 2$
boxes, single-box and pair avoidance probabilities equal $((n - 1)/n)^k$ and $((n -
2)/n)^k$, the empty-box count $W$ has mean $\lambda = n(1 - 1/n)^k > 0$ and variance
$\lambda[1 - (1 - 1/n)^k] + n(n - 1)[(1 - 2/n)^k - (1 - 1/n)^{2k}]$, and for $Z \sim
\mathrm{Po}(\lambda)$ both $d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z))$ and
$|\mathbb{P}(W = 0) - e^{-\lambda}|$ are at most $\min\{1, \lambda\}((1 - 1/n)^k + (n -
1)[(1 - 1/n)^k - (1 - 1/(n - 1))^k])$.

Difference from printed result (`ISSUE-4.15`): adds the domain guard $2 \le n$, because at $n =
1$ the redistribution step into the remaining $n - 1$ boxes is vacuous and the term $(1 - 1/(n
- 1))^k$ in `(4.13)` divides by $n - 1 = 0$. -/
def Ex4_15_restricted : Prop :=
  ∀ {n k : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    2 ≤ n →
    (∀ r : Fin k, Measurable (B r)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = 1 / (n : ℝ)) →
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, if ∀ t : Fin k, B t ω ≠ i then 1 else 0
    let lam : ℝ := (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k
    let err : ℝ := min 1 lam *
      ((1 - 1 / (n : ℝ)) ^ k +
        ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k))
    (r : ℝ) = lam →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    0 < r ∧
      (∀ i : Fin n, P.real {ω | ∀ t : Fin k, B t ω ≠ i} = (((n : ℝ) - 1) / (n : ℝ)) ^ k) ∧
      (∀ i j : Fin n, j ≠ i →
        P.real {ω | (∀ t : Fin k, B t ω ≠ i) ∧ (∀ t : Fin k, B t ω ≠ j)} =
          (((n : ℝ) - 2) / (n : ℝ)) ^ k) ∧
      ∫ ω, (W ω : ℝ) ∂P = lam ∧
      ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P =
        lam * (1 - (1 - 1 / (n : ℝ)) ^ k) +
          (n : ℝ) * ((n : ℝ) - 1) *
            ((1 - 2 / (n : ℝ)) ^ k - (1 - 1 / (n : ℝ)) ^ (2 * k)) ∧
      tvDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal err ∧
      |P.real {ω | W ω = 0} - Real.exp (-lam)| ≤ err

/-- Example 4.15, intermediate analytic identity and logarithmic bounds (`\label{ex123}`,
`SteinIntro.tex:2553-2560`, `SteinIntro.tex:2512`, referencing eq. `(4.13)` (`\ref{129}`)):
setting $a = \frac{n(n - 2)}{(n - 1)^2}$ and $\lambda = n(1 - 1/n)^k$, for all $2 \le n$
eq. `(4.13)` equals $\min\{1, \lambda\}(\frac{\lambda}{n} + \frac{n - 1}{n}\lambda(1 -
a^k))$ and is at most $\frac{\lambda}{n} + \lambda(1 - a^k)$, and for $3 \le n$ it
satisfies $1 - a^k \le k \log(\frac{(n - 1)^2}{n(n - 2)}) \le \frac{k}{n(n - 2)}$. -/
def Ex4_15_asymptotic_ineq : Prop :=
  ∀ {n k : ℕ},
    let a : ℝ := (n : ℝ) * ((n : ℝ) - 2) / ((n : ℝ) - 1) ^ 2
    let lam : ℝ := (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k
    (2 ≤ n →
      min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) =
        min 1 lam * (lam / (n : ℝ) + (((n : ℝ) - 1) / (n : ℝ)) * lam * (1 - a ^ k)) ∧
      min 1 lam *
          ((1 - 1 / (n : ℝ)) ^ k +
            ((n : ℝ) - 1) * ((1 - 1 / (n : ℝ)) ^ k - (1 - 1 / ((n : ℝ) - 1)) ^ k)) ≤
        lam / (n : ℝ) + lam * (1 - a ^ k)) ∧
    (3 ≤ n →
      1 - a ^ k ≤ (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) ∧
      (k : ℝ) * Real.log (((n : ℝ) - 1) ^ 2 / ((n : ℝ) * ((n : ℝ) - 2))) ≤
        (k : ℝ) / ((n : ℝ) * ((n : ℝ) - 2)))

/-- Example 4.15, asymptotic coupon-collecting rate (`\label{ex123}`,
`SteinIntro.tex:2553-2564`, `SteinIntro.tex:2512`): for any $c \in \mathbb{R}$ and any
ball-count sequence $k : \mathbb{N} \to \mathbb{N}$ satisfying $|(k_n : \mathbb{R}) - (n
\log n - c n)| \le 1$ eventually, $\lambda_n = n(1 - 1/n)^{k_n} \to e^c$ as $n \to \infty$,
and there exists $C > 0$ such that eventually for uniform coupon collecting of $k_n$ balls
into $n$ boxes, $d_{\mathrm{TV}}(\mathcal{L}(W_n), \mathrm{Po}(\lambda_n)) \le C \log(n) /
n$. -/
def Ex4_15_rate : Prop :=
  ∀ {c : ℝ} {k : ℕ → ℕ},
    (∀ᶠ n : ℕ in Filter.atTop,
      |(k n : ℝ) - ((n : ℝ) * Real.log (n : ℝ) - c * (n : ℝ))| ≤ 1) →
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k n)
        Filter.atTop (nhds (Real.exp c)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          {B : Fin (k n) → Ω → Fin n} {r : ℝ≥0},
          (∀ t : Fin (k n), Measurable (B t)) →
          ProbabilityTheory.iIndepFun B P →
          (∀ t : Fin (k n), ∀ i : Fin n, P.real {ω | B t ω = i} = 1 / (n : ℝ)) →
          (r : ℝ) = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ k n →
          let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, if ∀ t : Fin (k n), B t ω ≠ i then 1 else 0
          tvDist (P.map W) (poissonLaw r) ≤ ENNReal.ofReal (C * Real.log (n : ℝ) / (n : ℝ))

/-- Example 4.16, non-uniform redistribution size-bias coupling (unlabeled `[Coupon collecting
continued]`, `SteinIntro.tex:2569-2587`): for $k$ balls placed independently into $n$ boxes
with probabilities $(p_1, \dots, p_n)$ ($\sum_i p_i = 1$, $p_i \ge 0$), redirecting each
ball in box $i$ ($p_i < 1$) independently to box $j \ne i$ with probability $p_j / (1 -
p_i)$ yields indicators $(X_j^{(i)})_{j \ne i}$ with the conditional law of $(X_j)_{j \ne
i}$ given $X_i = 1$, satisfies $X_j^{(i)} \le X_j$ everywhere, and with independent index
$I$ ($\mathbb{P}(I = i) = (1 - p_i)^k / \lambda$) gives a size-bias coupling $W^s = \sum_{j
\ne I} X_j^{(I)} + 1$ of $W = \sum_{i=1}^n X_i$. -/
def Ex4_16_sizeBias : Prop :=
  ∀ {n k : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n}
    {R : (i : Fin n) → Fin k → Ω → {j : Fin n // j ≠ i}}
    {I : Ω → Fin n} {r : ℝ≥0},
    (∀ i : Fin n, 0 ≤ p i) →
    ∑ i : Fin n, p i = 1 →
    (∀ t : Fin k, Measurable (B t)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
    (∀ (i : Fin n) (t : Fin k), Measurable (R i t)) →
    (∀ i : Fin n, p i < 1 → ProbabilityTheory.iIndepFun (R i) P) →
    (∀ i : Fin n, p i < 1 → ∀ t : Fin k, ∀ j : {j : Fin n // j ≠ i},
      P.real {ω | R i t ω = j} = p j.1 / (1 - p i)) →
    (∀ i : Fin n, p i < 1 →
      ProbabilityTheory.IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ R i t ω) P) →
    Measurable I →
    (r : ℝ) = ∑ i : Fin n, (1 - p i) ^ k →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = (1 - p i) ^ k / (r : ℝ)) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun t ↦ B t ω, fun i t ↦ R i t ω)) P →
    let B' : (i : Fin n) → Fin k → Ω → Fin n :=
      fun i t ω ↦ if B t ω = i then (R i t ω).1 else B t ω
    let X : Fin n → Ω → ℕ := fun i ω ↦ if ∀ t : Fin k, B t ω ≠ i then 1 else 0
    let X' : (i : Fin n) → {j : Fin n // j ≠ i} → Ω → ℕ :=
      fun i j ω ↦ if ∀ t : Fin k, B' i t ω ≠ j.1 then 1 else 0
    let W : Ω → ℝ := fun ω ↦ ∑ i : Fin n, (X i ω : ℝ)
    let Ws : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, (X' (I ω) j ω : ℝ)) + 1
    (∀ i : Fin n, p i < 1 →
      P.map (fun ω (j : {j : Fin n // j ≠ i}) ↦ X' i j ω) =
        (ProbabilityTheory.cond P {ω | X i ω = 1}).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ω : Ω, ∀ j : {j : Fin n // j ≠ i}, X' i j ω ≤ X j.1 ω) ∧
      IsSizeBias P W P Ws

/-- Example 4.16, restricted away from zero denominators (unlabeled `[Coupon collecting
continued]`, `SteinIntro.tex:2566-2592`, citing `[bhj92]` §6.2 and proved from scratch;
`ISSUE-4.16` in `docs/SOURCE-ISSUES.md`): for $k \ge 1$ balls placed independently into $n
\ge 1$ boxes with probability distribution $(p_1, \dots, p_n)$ ($\sum_{i=1}^n p_i = 1$,
$p_i \ge 0$), if $\lambda = \sum_{i=1}^n (1 - p_i)^k > 0$ and $k \ne \log \lambda$, then
the empty-box count $W$ has mean $\lambda$ and for $Z \sim \mathrm{Po}(\lambda)$,
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \min\{1, \lambda\}[\max_i (1 - p_i)^k
+ \frac{k}{\lambda}(\frac{\lambda \log(k)}{k - \log(\lambda)} + \frac{4}{k})^2]$.

Difference from printed result (`ISSUE-4.16`): adds the domain guards $k \ge 1$, $\lambda > 0$,
and $k \ne \log \lambda$ because the printed bound at `SteinIntro.tex:2590` divides by $k -
\log \lambda$, which can vanish on the open simplex (`Ex4_16_exists_zero_denom`); the
inequality itself holds wherever defined. -/
def Ex4_16_restricted : Prop :=
  ∀ {n k : ℕ} (hn : 0 < n)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    1 ≤ k →
    (∀ i : Fin n, 0 ≤ p i) →
    ∑ i : Fin n, p i = 1 →
    (∀ t : Fin k, Measurable (B t)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, if ∀ t : Fin k, B t ω ≠ i then 1 else 0
    let lam : ℝ := ∑ i : Fin n, (1 - p i) ^ k
    0 < r →
    (r : ℝ) = lam →
    (k : ℝ) ≠ Real.log (r : ℝ) →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    ∫ ω, (W ω : ℝ) ∂P = lam ∧
      tvDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (min 1 lam *
            ((Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i : Fin n ↦ (1 - p i) ^ k) +
              (k : ℝ) / lam *
                (lam * Real.log (k : ℝ) / ((k : ℝ) - Real.log lam) + 4 / (k : ℝ)) ^ 2))

/-- Interior-simplex witness for the omitted zero-denominator condition in Example 4.16
(unlabeled `[Coupon collecting continued]`, `SteinIntro.tex:2590`; `ISSUE-4.16` in
`docs/SOURCE-ISSUES.md`): at $k = 2, n = 9$, there exist strictly positive box
probabilities $p_1, \dots, p_9 > 0$ summing to $1$ for which $\lambda = \sum_{i=1}^9 (1 -
p_i)^2 = e^2 > 0$, so $k - \log \lambda = 0$. -/
def Ex4_16_exists_zero_denom : Prop :=
  ∃ p : Fin 9 → ℝ,
    (∀ i : Fin 9, 0 < p i) ∧
    ∑ i : Fin 9, p i = 1 ∧
    let lam : ℝ := ∑ i : Fin 9, (1 - p i) ^ 2
    0 < lam ∧ ((2 : ℕ) : ℝ) - Real.log lam = 0

/-- Remark 4.17, at-most-$m$-balls occupancy (unlabeled, `SteinIntro.tex:2594-2598`): when $k$
balls are placed independently into $n$ boxes with probabilities $(p_1, \dots, p_n)$
($\sum_i p_i = 1$, $p_i \ge 0$), if $W$ is the number of boxes containing at most $m$ balls
and $\lambda = \mathbb{E}[W] > 0$, then a decreasing conditional coupling exists and
Theorem 4.19 (`\ref{thm125}`) gives $d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda))
\le \min\{1, \lambda\}(1 - \operatorname{Var}(W) / \lambda)$. -/
def Rem4_17_atMost : Prop :=
  ∀ {n k m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    (∀ i : Fin n, 0 ≤ p i) →
    ∑ i : Fin n, p i = 1 →
    (∀ t : Fin k, Measurable (B t)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
    let X : Fin n → Ω → ℕ := fun i ω ↦
      if ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card ≤ m then 1 else 0
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond P {ω | X i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc)) ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ)))

/-- Remark 4.17, corrected at-least-$m$-balls occupancy (unlabeled, `SteinIntro.tex:2600`;
`ISSUE-REM-4.17` and `ISSUE-TYPO-REM4.17` in `docs/SOURCE-ISSUES.md`): when $k$ balls are
placed independently into $n$ boxes with probabilities $(p_1, \dots, p_n)$ ($\sum_i p_i =
1$, $p_i \ge 0$), if $m \ge 1$, $W$ is the number of boxes containing at least $m$ balls,
and $\lambda = \mathbb{E}[W] > 0$, then a decreasing conditional coupling exists and
Theorem 4.19 (`\ref{thm125}`) gives $d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda))
\le \min\{1, \lambda\}(1 - \operatorname{Var}(W) / \lambda)$.

Difference from printed result (`ISSUE-REM-4.17`): replaces the printed citation of Theorem
4.14 (`\ref{thm122}`, positively related indicators) at `SteinIntro.tex:2600` by Theorem 4.19
(`\ref{thm125}`, negatively related indicators), because fixed-$k$ occupancy indicators
$\mathbf{1}[B_i \ge m]$ ($m \ge 1$) are negatively related and falsify Theorem 4.14
(`not_Rem4_17_atLeast_printed`). -/
def Rem4_17_atLeast_corrected : Prop :=
  ∀ {n k m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : Fin n → ℝ} {B : Fin k → Ω → Fin n} {r : ℝ≥0} {Z : Ω' → ℕ},
    1 ≤ m →
    (∀ i : Fin n, 0 ≤ p i) →
    ∑ i : Fin n, p i = 1 →
    (∀ t : Fin k, Measurable (B t)) →
    ProbabilityTheory.iIndepFun B P →
    (∀ t : Fin k, ∀ i : Fin n, P.real {ω | B t ω = i} = p i) →
    let X : Fin n → Ω → ℕ := fun i ω ↦
      if m ≤ ((Finset.univ : Finset (Fin k)).filter fun t ↦ B t ω = i).card then 1 else 0
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    0 < r →
    (r : ℝ) = ∫ ω, (W ω : ℝ) ∂P →
    AEMeasurable Z P' →
    P'.map Z = poissonLaw r →
    (∃ (Ωc : Type) (_ : MeasurableSpace Ωc) (Pc : Measure Ωc) (_ : IsProbabilityMeasure Pc)
      (Xc : Fin n → Ωc → ℕ) (Yc : (i : Fin n) → Ωc → ({j : Fin n // j ≠ i} → ℕ)),
      (∀ i : Fin n, Measurable (Xc i)) ∧
      (∀ i : Fin n, Measurable (Yc i)) ∧
      Pc.map (fun ωc i ↦ Xc i ωc) = P.map (fun ω i ↦ X i ω) ∧
      (∀ i : Fin n, 0 < P.real {ω | X i ω = 1} →
        Pc.map (Yc i) =
          (ProbabilityTheory.cond P {ω | X i ω = 1}).map
            (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j.1 ω)) ∧
      (∀ i : Fin n, ∀ ωc : Ωc, ∀ j : {j : Fin n // j ≠ i}, Yc i ωc j ≤ Xc j.1 ωc)) ∧
    tvDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (min 1 (r : ℝ) *
          (1 - ProbabilityTheory.variance (fun ω ↦ (W ω : ℝ)) P / (r : ℝ)))

/-- Theorem 4.20 (`\label{thm161}`, `SteinIntro.tex:2618-2626`; `ISSUE-TYPO-4.20` in
`docs/SOURCE-ISSUES.md`): Poisson approximation via exchangeable pairs. For an exchangeable
pair $(W, W')$ of $\mathbb{N}$-valued random variables, $\lambda > 0$, any
sub-$\sigma$-algebra $\mathcal{F} \supseteq \sigma(W)$, and any $c \in \mathbb{R}$,
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le \min\{1, \lambda^{-1/2}\}
(\mathbb{E}|\lambda - c\,\mathbb{P}(W' = W + 1 \mid \mathcal{F})| + \mathbb{E}|W -
c\,\mathbb{P}(W = W' + 1 \mid \mathcal{F})|)$, stated with `lintegral` (`ℝ≥0∞`-valued
expectations) per `D1` to avoid Bochner junk-zero when $W$ is not integrable. -/
def Thm4_20 : Prop :=
  ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {W W' : Ω → ℕ},
    0 < r →
    Measurable W →
    Measurable W' →
    IsExchangeablePair P W W' →
    ∀ {F : MeasurableSpace Ω}, F ≤ mΩ →
    MeasurableSpace.comap W inferInstance ≤ F →
    ∀ c : ℝ,
      @tvDist ℕ _ (@Measure.map Ω ℕ mΩ _ W P) (poissonLaw r) ≤
        ENNReal.ofReal (min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ)))) *
          (@lintegral Ω mΩ P (fun ω ↦ ENNReal.ofReal |(r : ℝ) - c *
              condExpAt F mΩ P
                ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω|) +
           @lintegral Ω mΩ P (fun ω ↦ ENNReal.ofReal |(W ω : ℝ) - c *
              condExpAt F mΩ P
                ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω|))

/-- Remark 4.18 (unlabeled, `SteinIntro.tex:2628-2632`): for an exchangeable pair $(W, W')$ of
$\mathbb{N}$-valued random variables, $\mathbb{P}(W' = W + 1) = \mathbb{P}(W = W' + 1)$. -/
def Rem4_18 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℕ},
    Measurable W →
    Measurable W' →
    IsExchangeablePair P W W' →
    P.real {ω | W' ω = W ω + 1} = P.real {ω | W ω = W' ω + 1}

/-- Remark 4.19 (unlabeled, `SteinIntro.tex:2633-2642`): the $\mathrm{Po}(\lambda)$ law
satisfies detailed balance $\lambda \pi(k) = (k + 1) \pi(k + 1)$ for all $k \in \mathbb{N}$
and is stationary (global balance) for the birth-death process with birth rate $\alpha(k) =
\lambda$ and death rate $\beta(k) = k$. -/
def Rem4_19 : Prop :=
  (∀ (r : ℝ≥0) (k : ℕ),
    (r : ℝ) * (poissonLaw r).real {k} =
      (↑(k + 1)) * (poissonLaw r).real {k + 1}) ∧
  (∀ r : ℝ≥0,
    (poissonLaw r).real {0} * (r : ℝ) = (poissonLaw r).real {1} ∧
      ∀ k : ℕ,
        (poissonLaw r).real {k + 1} * ((r : ℝ) + ((k + 1 : ℕ) : ℝ)) =
          (r : ℝ) * (poissonLaw r).real {k} +
            ((k + 2 : ℕ) : ℝ) * (poissonLaw r).real {k + 2})

/-- Theorem 4.20 proof anti-symmetry sub-claim (unlabeled display in proof of Theorem 4.20
(`\ref{thm161}`), `SteinIntro.tex:2645-2650`): for an exchangeable pair $(W, W')$ and any
bounded $f : \mathbb{N} \to \mathbb{R}$, $\mathbb{E}[\mathbb{I}[W' = W + 1] f(W') -
\mathbb{I}[W = W' + 1] f(W)] = 0$. -/
def Thm4_20_antisym : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℕ},
    Measurable W →
    Measurable W' →
    IsExchangeablePair P W W' →
    ∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, ((if W' ω = W ω + 1 then f (W' ω) else 0) -
             (if W ω = W' ω + 1 then f (W ω) else 0)) ∂P = 0

/-- Theorem 4.20 proof key identity eq. `(4.14)` (`\label{161}`, `SteinIntro.tex:2656-2660`):
for an exchangeable pair $(W, W')$ with integrable $W$, $\sigma(W) \subseteq \mathcal{F}$,
bounded $f : \mathbb{N} \to \mathbb{R}$, and $c \in \mathbb{R}$, $\mathbb{E}[\lambda f(W +
1) - W f(W)] = \mathbb{E}[(\lambda - c\,\mathbb{P}(W' = W + 1 \mid \mathcal{F})) f(W + 1) -
(W - c\,\mathbb{P}(W = W' + 1 \mid \mathcal{F})) f(W)]$. `Integrable (fun ω ↦ (W ω : ℝ)) P`
is included because `(4.14)` writes $\mathbb{E}[W f(W)]$ as a real expectation. -/
def Thm4_20_identity : Prop :=
  ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ≥0} {W W' : Ω → ℕ},
    0 < r →
    Measurable W →
    Measurable W' →
    IsExchangeablePair P W W' →
    Integrable (fun ω ↦ (W ω : ℝ)) P →
    ∀ {F : MeasurableSpace Ω}, F ≤ mΩ →
    MeasurableSpace.comap W inferInstance ≤ F →
    ∀ (f : ℕ → ℝ), (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
    ∀ c : ℝ,
      let _ : MeasurableSpace Ω := mΩ
      ∫ ω, poissonSteinOp r f (W ω) ∂P =
        ∫ ω, (((r : ℝ) - c *
              condExpAt F mΩ P
                ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω + 1) -
            ((W ω : ℝ) - c *
              condExpAt F mΩ P
                ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω)) ∂P

/-- Example 4.20 coupling and conditional jump probabilities (unlabeled `[Law of small
numbers]`, `SteinIntro.tex:2664-2671`): for independent $\{0, 1\}$-valued indicators $X_1,
\dots, X_n$ with $\mathbb{P}(X_i = 1) = p_i$, an independent copy $(X_1', \dots, X_n')$
with the same joint law, and a uniform random index $I \in \mathrm{Fin}\, n$ ($n > 0$)
independent of $(X, X')$, if $W = \sum_{i=1}^n X_i$ and $W' = W - X_I + X_I'$, then $(W,
W')$ is an exchangeable pair and $\mathbb{P}(W' = W + 1 \mid (X_i)) = \frac{1}{n}
\sum_{i=1}^n (1 - X_i) p_i$ and $\mathbb{P}(W = W' + 1 \mid (X_i)) = \frac{1}{n}
\sum_{i=1}^n X_i (1 - p_i)$ almost surely. -/
def Ex4_20_coupling : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    {X X' : Fin n → Ω → ℕ} {p : Fin n → ℝ} {I : Ω → Fin n},
    (∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, Measurable (X i)) →
    (∀ i, Measurable (X' i)) →
    (∀ i, P.real {ω | X i ω = 1} = p i) →
    ProbabilityTheory.iIndepFun X P →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let W' : Ω → ℕ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    IsExchangeablePair P W W' ∧
      P[{ω | W' ω = W ω + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
        (fun ω ↦ (1 / (n : ℝ)) * ∑ i : Fin n, (1 - (X i ω : ℝ)) * p i) ∧
      P[{ω | W ω = W' ω + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap (fun ω i ↦ X i ω) inferInstance] =ᵐ[P]
        (fun ω ↦ (1 / (n : ℝ)) * ∑ i : Fin n, (X i ω : ℝ) * (1 - p i))

/-- Example 4.20 (unlabeled `[Law of small numbers]`, `SteinIntro.tex:2663-2680`): for
independent $\{0, 1\}$-valued indicators $X_1, \dots, X_n$ with $\mathbb{P}(X_i = 1) =
p_i$, $W = \sum_{i=1}^n X_i$, and $\lambda = \sum_{i=1}^n p_i > 0$,
$d_{\mathrm{TV}}(\mathcal{L}(W), \mathrm{Po}(\lambda)) \le 2 \min\{1, \lambda^{-1/2}\}
\sum_{i=1}^n p_i^2$. -/
def Ex4_20 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℕ} {p : Fin n → ℝ},
    0 < n →
    (∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, Measurable (X i)) →
    (∀ i, P.real {ω | X i ω = 1} = p i) →
    (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
    ProbabilityTheory.iIndepFun X P →
    ∀ {r : ℝ≥0}, 0 < r → (r : ℝ) = (∑ i : Fin n, p i) →
    tvDist (P.map (fun ω ↦ ∑ i : Fin n, X i ω)) (poissonLaw r) ≤
      ENNReal.ofReal (2 * min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) * ∑ i : Fin n, p i ^ 2)

/-- Example 4.20 direct bound of eq. `(4.14)` (unlabeled prose, `SteinIntro.tex:2678-2679`,
referencing eq. `(4.14)` `\label{161}` at `SteinIntro.tex:2656-2660`): in the replace-one
exchangeable-pair coupling of `Ex4_20_coupling` with $\mathcal{F} = \sigma(X_1, \dots,
X_n)$, $c = n$, and $\lambda = \sum_{i=1}^n p_i > 0$, the right-hand side of
`Thm4_20_identity` (`\label{161}`) simplifies for every bounded $f : \mathbb{N} \to
\mathbb{R}$ to $\mathbb{E}[(\sum_{i=1}^n p_i X_i) \Delta f(W)]$, bounding its absolute
value directly via $\|\Delta f\| \le \min\{1, \lambda^{-1}\}$ gives
$|\mathbb{E}[\mathcal{A}f(W)]| \le \min\{1, \lambda^{-1}\} \sum_{i=1}^n p_i^2$ (matching
`Ex4_4` / `Thm4_6`), and $\min\{1, \lambda^{-1}\} \sum_{i=1}^n p_i^2 < 2 \min\{1,
\lambda^{-1/2}\} \sum_{i=1}^n p_i^2$. -/
def Ex4_20_direct_eq161 : Prop :=
  ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n)
    {X X' : Fin n → Ω → ℕ} {p : Fin n → ℝ} {I : Ω → Fin n} {r : ℝ≥0},
    (∀ i, ∀ ω, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, Measurable (X i)) →
    (∀ i, Measurable (X' i)) →
    (∀ i, P.real {ω | X i ω = 1} = p i) →
    ProbabilityTheory.iIndepFun X P →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    0 < r →
    (r : ℝ) = ∑ i : Fin n, p i →
    let _ : MeasurableSpace Ω := mΩ
    let W : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
    let W' : Ω → ℕ := fun ω ↦ W ω - X (I ω) ω + X' (I ω) ω
    (∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      ∫ ω, (((r : ℝ) - (n : ℝ) *
            condExpAt (MeasurableSpace.comap (fun ω' i ↦ X i ω') inferInstance) mΩ P
              ({ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω + 1) -
          ((W ω : ℝ) - (n : ℝ) *
            condExpAt (MeasurableSpace.comap (fun ω' i ↦ X i ω') inferInstance) mΩ P
              ({ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ)) ω) * f (W ω)) ∂P =
        ∫ ω, (∑ i : Fin n, p i * (X i ω : ℝ)) * fwdDiff 1 f (W ω) ∂P) ∧
    (∀ f : ℕ → ℝ, (∃ C : ℝ, ∀ k : ℕ, |f k| ≤ C) →
      (∀ k : ℕ, |fwdDiff 1 f k| ≤ min 1 (r : ℝ)⁻¹) →
        |∫ ω, poissonSteinOp r f (W ω) ∂P| ≤
          min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2) ∧
    min 1 (r : ℝ)⁻¹ * ∑ i : Fin n, p i ^ 2 <
      2 * min 1 ((r : ℝ) ^ (-(1 / 2 : ℝ))) * ∑ i : Fin n, p i ^ 2

/-- Example 4.21 transposition coupling and conditional jump probabilities (unlabeled `[Fixed
points of permutations]`, `SteinIntro.tex:2682-2688`; `ISSUE-TYPO-EX4.21` in
`docs/SOURCE-ISSUES.md`): for $n \ge 2$, a uniform random permutation $\sigma \in
\mathrm{Sym}(n)$, and an independent uniform random transposition $\tau$, with $W =
\mathrm{numFixedPoints}(\sigma)$, $W' = \mathrm{numFixedPoints}(\sigma \tau)$, and $W_2 =
\mathrm{numTwoCycles}(\sigma)$, $(W, W')$ is an exchangeable pair and $\mathbb{P}(W' = W +
1 \mid \sigma) = \frac{n - W - 2 W_2}{\binom{n}{2}}$ and $\mathbb{P}(W = W' + 1 \mid
\sigma) = \frac{W (n - W)}{\binom{n}{2}}$ almost surely. -/
def Ex4_21_coupling : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n)
    {σ : Ω → Equiv.Perm (Fin n)} {τ : Ω → {π : Equiv.Perm (Fin n) // π.IsSwap}},
    Measurable σ →
    Measurable τ →
    ProbabilityTheory.IndepFun σ τ P →
    P.map σ = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure →
    P.map τ =
      (@PMF.uniformOfFintype {π : Equiv.Perm (Fin n) // π.IsSwap} inferInstance
        ⟨⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩,
          ⟨0, by omega⟩, ⟨1, by omega⟩, Fin.ne_of_val_ne Nat.zero_ne_one, rfl⟩⟩).toMeasure →
    let W : Ω → ℕ := fun ω ↦ numFixedPoints (σ ω)
    let W' : Ω → ℕ := fun ω ↦ numFixedPoints (σ ω * (τ ω).1)
    let W2 : Ω → ℕ := fun ω ↦ numTwoCycles (σ ω)
    IsExchangeablePair P W W' ∧
      P[{ω' | W' ω' = W ω' + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        (fun ω ↦ ((n : ℝ) - (W ω : ℝ) - 2 * (W2 ω : ℝ)) / (Nat.choose n 2 : ℝ)) ∧
      P[{ω' | W ω' = W' ω' + 1}.indicator (1 : Ω → ℝ) |
          MeasurableSpace.comap σ inferInstance] =ᵐ[P]
        (fun ω ↦ (W ω : ℝ) * ((n : ℝ) - (W ω : ℝ)) / (Nat.choose n 2 : ℝ))

/-- Example 4.21 first-moment sub-claim (unlabeled `[Fixed points of permutations]`,
`SteinIntro.tex:2693`): for $n \ge 1$, the expected number of fixed points of a uniform
random permutation on `Fin n` is $\mathbb{E}[W] = 1$. -/
def Ex4_21_EW : Prop :=
  ∀ {n : ℕ}, 1 ≤ n →
    ∫ π, (numFixedPoints π : ℝ) ∂
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 1

/-- Example 4.21 second-moment sub-claim (unlabeled `[Fixed points of permutations]`,
`SteinIntro.tex:2701-2702`): for $n \ge 2$, the expected squared number of fixed points of
a uniform random permutation on `Fin n` is $\mathbb{E}[W^2] = 2$. -/
def Ex4_21_EW2 : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
    ∫ π, ((numFixedPoints π : ℝ) ^ 2) ∂
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 2

/-- Example 4.21 $2$-cycle expectation sub-claim (unlabeled `[Fixed points of permutations]`,
`SteinIntro.tex:2701-2702`): for $n \ge 2$, the expected number of $2$-cycles of a uniform
random permutation on `Fin n` is $\mathbb{E}[W_2] = 1 / 2$. -/
def Ex4_21_EW2cycles : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
    ∫ π, (numTwoCycles π : ℝ) ∂
      (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure = 1 / 2

/-- Example 4.21 (unlabeled `[Fixed points of permutations]`, `SteinIntro.tex:2681-2702`;
`ISSUE-TYPO-EX4.21` in `docs/SOURCE-ISSUES.md`): for $n \ge 2$, the number of fixed points
$W$ of a uniform random permutation on `Fin n` satisfies $d_{\mathrm{TV}}(\mathcal{L}(W),
\mathrm{Po}(1)) \le 4 / n$. -/
def Ex4_21 : Prop :=
  ∀ {n : ℕ}, 2 ≤ n →
    tvDist
      ((PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.map numFixedPoints)
      (poissonLaw 1) ≤ ENNReal.ofReal (4 / (n : ℝ))

/-- Example 4.21 true-rate prose claim (unlabeled `[Fixed points of permutations]`,
`SteinIntro.tex:2702-2706`, citing `[abt03]` and proved from scratch): for the number of
fixed points $W_n(\pi) = |\{i \in \mathrm{Fin}\,n \mid \pi(i) = i\}|$ of a uniformly chosen
random permutation $\pi \in \mathrm{Sym}(n)$, the total variation distance to
$\mathrm{Po}(1)$ satisfies the super-exponential bound $d_{\mathrm{TV}}(\mathcal{L}(W_n),
\mathrm{Po}(1)) \le 2^n / (n + 1)!$ for all $n \in \mathbb{N}$ and decays strictly faster
than order $1/n$, i.e. $\lim_{n \to \infty} n \, d_{\mathrm{TV}}(\mathcal{L}(W_n),
\mathrm{Po}(1)) = 0$ in `ℝ≥0∞`. -/
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
