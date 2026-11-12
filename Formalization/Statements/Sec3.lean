/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.OrnsteinUhlenbeck

/-!
# Section 3 Statements (`Formalization.Statements.Sec3`)

Self-contained theorem, proposition, lemma, corollary, remark, example, and prose statements from
Section 3 (`\label{norm}`, `SteinIntro.tex:700-1815`) of Nathan Ross, *"Fundamentals of Stein's
method"* (`arXiv:1109.1880v1`), importing core definitions only (`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace SteinMethod

/-- Section 3 Kolmogorov–Wasserstein normal comparison (unlabeled display,
`SteinIntro.tex:701-709`): for any real-valued random variable $W$ and standard normal $Z
\sim \mathcal{N}(0, 1)$, $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le (2 / \pi)^{1/4}
\sqrt{d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))}$. -/
def Sec3_dK_le_dW : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    AEMeasurable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal ((2 / Real.pi) ^ (1 / 4 : ℝ)) *
        wassersteinDist (P.map W) (P'.map Z) ^ (1 / 2 : ℝ)

/-- Section 3 opening: Wasserstein Stein-solution regularity (unlabeled prose,
`SteinIntro.tex:711-716`; `ISSUE-TYPO-SEC3-OPEN` in `docs/SOURCE-ISSUES.md`):
(1) for every $1$-Lipschitz $h : \mathbb{R} \to \mathbb{R}$, `normalSteinSol h` is
    differentiable everywhere with $|f_h| \le 2$, $|f_h'| \le \sqrt{2/\pi}$, and $2$-Lipschitz
    derivative $f_h'$, and belongs to the twice-differentiable class `normalWassersteinClass`
    iff $h$ is differentiable on $\mathbb{R}$;
(2) for every $x \in \mathbb{R}$, the Kolmogorov solution `normalSteinSolKolm x` is neither
    differentiable on $\mathbb{R}$ nor has a differentiable derivative `deriv
    (normalSteinSolKolm x)`. Under the accepted a.e./Lipschitz reading of `Lem2_5_2`, `‖f_h″‖ ≤
    2L` holds at `SteinIntro.tex:712-713` (the strict everywhere-second-derivative reading is
    characterized in Part 1). -/
def Sec3_opening_steinSol_regularity : Prop :=
  (∀ h : ℝ → ℝ, LipschitzWith 1 h →
    Differentiable ℝ (normalSteinSol h) ∧
    (∀ w : ℝ, |normalSteinSol h w| ≤ 2) ∧
    (∀ w : ℝ, |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi)) ∧
    LipschitzWith 2 (deriv (normalSteinSol h)) ∧
    (normalSteinSol h ∈ normalWassersteinClass ↔ Differentiable ℝ h)) ∧
  (∀ x : ℝ,
    ¬ Differentiable ℝ (normalSteinSolKolm x) ∧
    ¬ Differentiable ℝ (deriv (normalSteinSolKolm x)))

/-- Theorem 3.1 (`\label{thm31}`, eq. `(3.1)` `\label{35}`, `SteinIntro.tex:719-724`; `D6`
literal class): for any real-valued random variable $W$ and standard normal $Z \sim
\mathcal{N}(0, 1)$, $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \sup_{f \in
\mathcal{F}} |\mathbb{E}[f'(W) - W f(W)]|$. -/
def Thm3_1 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    AEMeasurable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ normalWassersteinClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|

/-- Theorem 3.2 (`\label{thm32}`, `SteinIntro.tex:736-742`): Wasserstein normal approximation
bound for $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ when $X_1, \dots, X_n$ are independent random
variables with $\mathbb{E}|X_i|^4 < \infty$, $\mathbb{E}[X_i] = 0$, and $\mathbb{E}[X_i^2] =
1$. -/
def Thm3_2 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / (n : ℝ) ^ (3 / 2 : ℝ) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 2 / (Real.sqrt Real.pi * (n : ℝ)) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P))

/-- Section 3.1 post-Theorem 3.2 i.i.d. rate and optimality remark (unlabeled prose,
`SteinIntro.tex:743-744`, specializing Theorem 3.2):
(1) for any i.i.d. sequence $(X_i)_{i \in \mathbb{N}}$ with $X_0 \in L^4(P)$, $\mathbb{E}[X_0] =
    0$, and $\mathbb{E}[X_0^2] = 1$, $W_n = (\sum_{i < n} X_i)/\sqrt{n}$ satisfies
    $d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1)) \le C / \sqrt{n}$ for all $n \ge 1$
    with $C = \mathbb{E}|X_0|^3 + \sqrt{2\,\mathbb{E}[X_0^4]/\pi}$;
(2) this $n^{-1/2}$ rate is best possible over Theorem 3.2's i.i.d. class: there exist a
    probability space $(\Omega, P)$, an i.i.d. sequence $(X_i)_{i \in \mathbb{N}}$ on $(\Omega,
    P)$ satisfying all hypotheses of Theorem 3.2, and $c > 0$ such that
    $d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1)) \ge c / \sqrt{n}$ for all $n \ge 1$. -/
def Sec3_1_iid_wasserstein_rate : Prop :=
  (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {X : ℕ → Ω → ℝ},
    (∀ i : ℕ, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : ℕ, ProbabilityTheory.IdentDistrib (X i) (X 0) P P) →
    MemLp (X 0) 4 P →
    ∫ ω, X 0 ω ∂P = 0 →
    ∫ ω, X 0 ω ^ 2 ∂P = 1 →
    let C : ℝ := (∫ ω, |X 0 ω| ^ 3 ∂P) + Real.sqrt (2 / Real.pi * ∫ ω, X 0 ω ^ 4 ∂P)
    ∀ n : ℕ, 0 < n →
      let W_n : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / Real.sqrt n
      wassersteinDist (P.map W_n) stdNormalLaw ≤ ENNReal.ofReal (C / Real.sqrt n)) ∧
  (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → ℝ) (c : ℝ),
    0 < c ∧
    (∀ i : ℕ, AEMeasurable (X i) P) ∧
    ProbabilityTheory.iIndepFun X P ∧
    (∀ i : ℕ, ProbabilityTheory.IdentDistrib (X i) (X 0) P P) ∧
    MemLp (X 0) 4 P ∧
    ∫ ω, X 0 ω ∂P = 0 ∧
    ∫ ω, X 0 ω ^ 2 ∂P = 1 ∧
    ∀ n : ℕ, 0 < n →
      let W_n : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range n, X i ω) / Real.sqrt n
      ENNReal.ofReal (c / Real.sqrt n) ≤ wassersteinDist (P.map W_n) stdNormalLaw)

/-- Section 3.1 third-moment normal approximation bound for independent sums (unlabeled prose,
`SteinIntro.tex:746-747`): for independent mean-zero unit-variance random variables $X_1,
\ldots, X_n \in L^3(P)$, the normalized sum $W = (\sum_i X_i)/\sqrt{n}$ satisfies
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{N}(0, 1)) \le \frac{3}{n^{3/2}} \sum_{i=1}^n
\mathbb{E}|X_i|^3$. -/
def Sec3_1_indepSum_thirdMoment : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (_hn : 0 < n) {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 3 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (3 / (n : ℝ) ^ (3 / 2 : ℝ) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P)

/-- Lemma 3.3 (`\label{lem33}`, eqs. `(3.2)`–`(3.3)` `\label{345}`–`\label{345a}`,
`SteinIntro.tex:753-759`; `ISSUE-TYPO-3.3` and `ISSUE-3.3` in `docs/SOURCE-ISSUES.md`):
leave-one-out Stein expansion for $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ and $W_i = (\sum_{j \ne
i} X_j)/\sqrt{n}$. -/
def Lem3_3 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {f : ℝ → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) →
    Differentiable ℝ f →
    (∃ B₀ : ℝ, ∀ w : ℝ, |f w| ≤ B₀) →
    (∃ B₁ : ℝ, ∀ w : ℝ, |deriv f w| ≤ B₁) →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W_i : Fin n → Ω → ℝ := fun i ω ↦ (∑ j ∈ Finset.univ.erase i, X j ω) / Real.sqrt n
    ∫ ω, W ω * f (W ω) ∂P =
      (∫ ω, (1 / Real.sqrt n) * ∑ i : Fin n,
          X i ω * (f (W ω) - f (W_i i ω) - (W ω - W_i i ω) * deriv f (W ω)) ∂P) +
        ∫ ω, (1 / Real.sqrt n) * ∑ i : Fin n,
          X i ω * (W ω - W_i i ω) * deriv f (W ω) ∂P

/-- Lemma 3.4 (`\label{lem33aa}`, eq. `(3.5)` `\label{337}`, `SteinIntro.tex:771-776`): bound on
$|\mathbb{E}[f'(W) - W f(W)]|$ for $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ when $f$ is bounded
with bounded first and second derivatives. -/
def Lem3_4 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {f : ℝ → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∫ ω, X i ω ^ 2 ∂P = 1) →
    (Differentiable ℝ f ∧ Differentiable ℝ (deriv f)) →
    (∃ B₀ : ℝ, ∀ w : ℝ, |f w| ≤ B₀) →
    ∀ {B₁ B₂ : ℝ},
      (∀ w : ℝ, |deriv f w| ≤ B₁) →
      (∀ w : ℝ, |deriv (deriv f) w| ≤ B₂) →
      let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
      |∫ ω, normalSteinOp f (W ω) ∂P| ≤
        B₂ / (2 * (n : ℝ) ^ (3 / 2 : ℝ)) * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          B₁ / (n : ℝ) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P)

/-- Theorem 3.5, corrected (`\label{thm41}`, eq. `(3.8)` `\label{41}`, `SteinIntro.tex:815-822`;
`ISSUE-3.5` and `ISSUE-3.5-PROOF-SYM` in `docs/SOURCE-ISSUES.md`): Wasserstein normal
approximation bound for $W = (\sum_{i=1}^n X_i)/\sigma$ under `IsDependencyGraph P X N` and
$\sigma^2 = \operatorname{Var}(\sum_i X_i) > 0$.

Difference from printed result (`ISSUE-3.5`): printed Theorem 3.5 assumes only dependency
neighborhoods (`HasDependencyNeighborhoods`, Definition 3.1), which is false
(`not_Thm3_5_printed`); here the hypothesis is strengthened to a symmetric dependency graph
(`IsDependencyGraph P X N`, `SteinIntro.tex:810-812`) with $\sigma^2 > 0$. -/
def Thm3_5_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)} {Z : Ω' → ℝ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    IsDependencyGraph P X N →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P)
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / σ
    let D : ℝ := ((Finset.univ.sup fun i : Fin n ↦ (N i).card : ℕ) : ℝ)
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (D ^ 2 / σ ^ 3 * (∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P) +
          Real.sqrt 26 * D ^ (3 / 2 : ℝ) / (Real.sqrt Real.pi * σ ^ 2) *
            Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P))

/-- Section 3.2 independent-variables specialization (unlabeled prose,
`SteinIntro.tex:827-828`): mutually independent random variables $(X_1, \ldots, X_n)$
satisfy both `HasDependencyNeighborhoods` and `IsDependencyGraph` with singleton
neighborhoods $N_i = \{i\}$ (and maximum neighborhood size $D = 1$ when $n \ge 1$). -/
def Sec3_2_indep_isDependencyGraph : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    HasDependencyNeighborhoods P X (fun i ↦ {i}) ∧
    IsDependencyGraph P X (fun i ↦ {i}) ∧
    (0 < n → (Finset.univ.sup fun i : Fin n ↦ ({i} : Finset (Fin n)).card) = 1)

/-- Section 3.2 intermediate dependency-neighborhood bound (unlabeled prose,
`SteinIntro.tex:908-911`, referencing eqs. `(3.11)` at `SteinIntro.tex:844-848` and `(3.12)`
at `SteinIntro.tex:859-861`): under literal Definition 3.1 (`HasDependencyNeighborhoods P X
N`, without requiring `IsDependencyGraph`), if $X_1, \ldots, X_n \in L^4(P)$ have mean zero
and $\sigma^2 = \operatorname{Var}(\sum_i X_i) > 0$, then $\sigma^2 = \mathbb{E}[\sum_i X_i
\sum_{j \in N_i} X_j]$ and $W = (\sum_i X_i)/\sigma$ satisfies
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \frac{1}{\sigma^3}\sum_{i=1}^n \sum_{j
\in N_i} \sum_{k \in N_i} \mathbb{E}|X_i X_j X_k| + \frac{\sqrt{2}}{\sqrt{\pi}\,\sigma^2}
\sqrt{\operatorname{Var}(\sum_{i=1}^n \sum_{j \in N_i} X_i X_j)}$. -/
def Sec3_2_depNeighborhoods_intermediate_bound : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {N : Fin n → Finset (Fin n)} {Z : Ω' → ℝ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    HasDependencyNeighborhoods P X N →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let σ2 : ℝ := ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P
    let σ : ℝ := Real.sqrt σ2
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / σ
    σ2 = (∫ ω, ∑ i : Fin n, X i ω * ∑ j ∈ N i, X j ω ∂P) ∧
      wassersteinDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (1 / σ ^ 3 *
              (∑ i : Fin n, ∑ j ∈ N i, ∑ k ∈ N i, ∫ ω, |X i ω * X j ω * X k ω| ∂P) +
            Real.sqrt 2 / (Real.sqrt Real.pi * σ ^ 2) *
              Real.sqrt
                (ProbabilityTheory.variance
                  (fun ω ↦ ∑ i : Fin n, ∑ j ∈ N i, X i ω * X j ω) P))

/-- Section 3.2.1 triangle-indicator setup, pairwise-independence criterion, dependency-graph
degree, and central moments (unlabeled prose, `SteinIntro.tex:918-929`; `ISSUE-3.2.1` in
`docs/SOURCE-ISSUES.md`): for $n \ge 3$ and any enumeration `enum : Fin (n.choose 3) ≃ {s :
Finset (Fin n) // s.card = 3}` of the $\binom{n}{3}$ three-vertex subsets:
(1) the triangle count $T(G)$ is $\sum_i Y_i(G)$;
(2) for $0 \le p \le 1$, defining $N_i = \{i\} \cup \{j : |V_i \cap V_j| = 2\}$ and $X_i = Y_i -
    p^3$ gives $|N_i| = 3(n - 3) + 1 = 3n - 8$, `IsDependencyGraph (erdosRenyi n p) X N`, and
    $\mathbb{E}|X_i|^k = p^3(1 - p^3)[(1 - p^3)^{k-1} + p^{3(k-1)}]$ for all $k \ge 1$;
(3) for $0 < p < 1$ and $i \ne j$, $Y_i$ and $Y_j$ are independent under $G(n, p)$ iff the edge
    sets on $V_i$ and $V_j$ are disjoint (equivalently $|V_i \cap V_j| \le 1$; the `"only if"`
    direction fails at $p \in \{0, 1\}$ for $n \ge 4$, where $Y_i$ is a.s. constant). -/
def Sec3_2_1_triangles_setup_and_moments : Prop :=
  ∀ {n : ℕ}, 3 ≤ n →
    Nonempty (Fin (n.choose 3) ≃ {s : Finset (Fin n) // s.card = 3}) ∧
    ∀ (enum : Fin (n.choose 3) ≃ {s : Finset (Fin n) // s.card = 3}),
      let Y : Fin (n.choose 3) → SimpleGraph (Fin n) → ℝ :=
        fun i ↦ {G : SimpleGraph (Fin n) | (enum i).1 ∈ G.cliqueSet 3}.indicator 1
      let N_nbhd : Fin (n.choose 3) → Finset (Fin (n.choose 3)) :=
        fun i ↦ Finset.univ.filter (fun j ↦ j = i ∨ ((enum i).1 ∩ (enum j).1).card = 2)
      (∀ G : SimpleGraph (Fin n), ((G.cliqueSet 3).ncard : ℝ) = ∑ i : Fin (n.choose 3), Y i G) ∧
      (∀ i : Fin (n.choose 3),
        (N_nbhd i).card = 3 * (n - 3) + 1 ∧
        ((N_nbhd i).card : ℝ) = 3 * (n : ℝ) - 8) ∧
      (∀ {p : ℝ}, 0 ≤ p → p ≤ 1 →
        let X : Fin (n.choose 3) → SimpleGraph (Fin n) → ℝ := fun i G ↦ Y i G - p ^ 3
        IsDependencyGraph (erdosRenyi n p) X N_nbhd ∧
        ∀ (i : Fin (n.choose 3)) (k : ℕ), 1 ≤ k →
          ∫ G, |X i G| ^ k ∂erdosRenyi n p =
            p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ (k - 1) + p ^ (3 * (k - 1)))) ∧
      (∀ {p : ℝ}, 0 < p → p < 1 →
        ∀ i j : Fin (n.choose 3), i ≠ j →
          (ProbabilityTheory.IndepFun (Y i) (Y j) (erdosRenyi n p) ↔
            Disjoint {e : EdgePair n | ∀ v ∈ e.1, v ∈ (enum i).1}
              {e : EdgePair n | ∀ v ∈ e.1, v ∈ (enum j).1}))

/-- Section 3.2.1 triangle-count application, restricted (unlabeled prose and display,
`SteinIntro.tex:918-949`; `ISSUE-TYPO-3.2.1` and `ISSUE-3.2.1` in `docs/SOURCE-ISSUES.md`):
for triangle counts $T$ in $G(n, p)$ with $n \ge 3$ and $0 < p < 1$, $\mathbb{E}[T] =
\binom{n}{3} p^3$, $\sigma^2 = \operatorname{Var}(T) = \binom{n}{3} p^3 [1 - p^3 + 3(n -
3)p^2(1 - p)]$, and $W = (T - \mathbb{E}[T])/\sigma$ satisfies the Theorem 3.5 Wasserstein
bound.

Difference from printed result (`ISSUE-TYPO-3.2.1`, `ISSUE-3.2.1`): printed `SteinIntro.tex:936`
writes $d_{\mathrm{K}}$ by typo where Theorem 3.5 bounds $d_{\mathrm{W}}$, and
`SteinIntro.tex:941` omits $n \ge 3$ and restricts $0 \le p \le 1$ to $0 < p < 1$ because
$\sigma = 0$ at $p \in \{0, 1\}$ (the literal printed $d_{\mathrm{K}}$ inequality is also proved
for $n \ge 3$ and $0 < p < 1$ in `Sec3_2_1_triangles_kolmogorov_restricted`). -/
def Sec3_2_1_triangles_restricted : Prop :=
  ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {Z : Ω' → ℝ},
    3 ≤ n →
    0 < p →
    p < 1 →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℝ := ∫ G, T G ∂erdosRenyi n p
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance T (erdosRenyi n p))
    let W : SimpleGraph (Fin n) → ℝ := fun G ↦ (T G - μ) / σ
    μ = (n.choose 3 : ℝ) * p ^ 3 ∧
      ProbabilityTheory.variance T (erdosRenyi n p) =
        (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) ∧
      wassersteinDist ((erdosRenyi n p).map W) (P'.map Z) ≤
        ENNReal.ofReal
          ((3 * (n : ℝ) - 8) ^ 2 / σ ^ 3 *
              ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 2 + p ^ 6)) +
            Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
              (Real.sqrt Real.pi * σ ^ 2) *
              Real.sqrt
                ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9)))

/-- Section 3.2.1 literal $d_{\mathrm{K}}$ inequality, restricted to $0 < p < 1$ (unlabeled
display, `SteinIntro.tex:934-939`; `ISSUE-TYPO-3.2.1` and `ISSUE-3.2.1` in
`docs/SOURCE-ISSUES.md`): although Theorem 3.5 bounds $d_{\mathrm{W}}(W, Z)$
(`Sec3_2_1_triangles_restricted`), the literal printed bound with $d_{\mathrm{K}}(W, Z)$ on
the left-hand side also holds unconditionally for all $n \ge 3$ and $0 < p < 1$.

Difference from printed result (`ISSUE-3.2.1`): restricts $0 \le p \le 1$ to $0 < p < 1$ (with
$n \ge 3$) so $\sigma = \sqrt{\operatorname{Var}(T)} > 0$ and $W = (T - \mathbb{E}[T])/\sigma$
avoids division by zero, while keeping the literally printed Kolmogorov metric $d_{\mathrm{K}}$. -/
def Sec3_2_1_triangles_kolmogorov_restricted : Prop :=
  ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {p : ℝ} {Z : Ω' → ℝ},
    3 ≤ n →
    0 < p →
    p < 1 →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let T : SimpleGraph (Fin n) → ℝ := fun G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℝ := ∫ G, T G ∂erdosRenyi n p
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance T (erdosRenyi n p))
    let W : SimpleGraph (Fin n) → ℝ := fun G ↦ (T G - μ) / σ
    μ = (n.choose 3 : ℝ) * p ^ 3 ∧
      ProbabilityTheory.variance T (erdosRenyi n p) =
        (n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3 + 3 * ((n : ℝ) - 3) * p ^ 2 * (1 - p)) ∧
      kolmogorovDist ((erdosRenyi n p).map W) (P'.map Z) ≤
        ENNReal.ofReal
          ((3 * (n : ℝ) - 8) ^ 2 / σ ^ 3 *
              ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 2 + p ^ 6)) +
            Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
              (Real.sqrt Real.pi * σ ^ 2) *
              Real.sqrt
                ((n.choose 3 : ℝ) * p ^ 3 * (1 - p ^ 3) * ((1 - p ^ 3) ^ 3 + p ^ 9)))

/-- Section 3.2.1 triangle-count variance divergence and CLT regime, restricted (unlabeled
prose, `SteinIntro.tex:941-944`; `ISSUE-TYPO-3.2.1` and `ISSUE-3.2.1` in
`docs/SOURCE-ISSUES.md`): if $0 \le p_n \le 1$ satisfies $\lim_{n \to \infty} n^\alpha p_n =
c > 0$ for some $\alpha \ge 0$, with $c < 1$ when $\alpha = 0$, then:
1. for all $0 \le \alpha < 1$, $\mathrm{Var}(T_n) \to \infty$ (`SteinIntro.tex:942-943`), and
2. for all $0 \le \alpha < 2/9$, the Section 3.2.1 Stein upper bound tends to $0$, and $W_n =
   (T_n - \mathbb{E}[T_n])/\sigma_n$ converges to $\mathcal{N}(0, 1)$ in both Wasserstein and
   Kolmogorov distance (hence in distribution).

Difference from printed result (`ISSUE-3.2.1`): adds $c < 1$ in the boundary case $\alpha = 0$
($\lim_{n \to \infty} p_n = c$) to exclude the degenerate $p_n \equiv 1$ sequence where
$\mathrm{Var}(T_n) = 0$ (the cited `[ruc88]` necessary-and-sufficient CLT criterion is proved in
`Sec3_2_1_triangles_rucinski`). -/
def Sec3_2_1_triangles_clt_regime_restricted : Prop :=
  ∀ {p : ℕ → ℝ} {α c : ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    0 ≤ α →
    0 < c →
    (α = 0 → c < 1) →
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) Filter.atTop (nhds c) →
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    let rhs : ℕ → ℝ := fun n ↦
      (3 * (n : ℝ) - 8) ^ 2 / σ n ^ 3 *
          ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 2 + p n ^ 6)) +
        Real.sqrt 26 * (3 * (n : ℝ) - 8) ^ ((3 : ℝ) / 2) /
          (Real.sqrt Real.pi * σ n ^ 2) *
          Real.sqrt
            ((n.choose 3 : ℝ) * p n ^ 3 * (1 - p n ^ 3) * ((1 - p n ^ 3) ^ 3 + p n ^ 9))
    (α < 1 →
      Filter.Tendsto (fun n : ℕ ↦ ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
        Filter.atTop Filter.atTop) ∧
    (α < 2 / 9 →
      Filter.Tendsto rhs Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          Filter.atTop (nhds 0))

/-- Section 3.2.1 Ruciński triangle-count CLT criterion (unlabeled prose,
`SteinIntro.tex:941-944`, citing Ruciński 1988 `\cite{ruc88}`, Theorem 2 specialized to $H =
K_3$ with $m(K_3) = e(K_3)/v(K_3) = 1$, proved from scratch): for $G \sim G(n, p_n)$ with $0
\le p_n \le 1$, the standardized triangle count $W_n = (T_n - \mathbb{E}[T_n]) / \sigma_n$
converges in distribution to $\mathcal{N}(0, 1)$ (equivalently pointwise in CDF, in
Kolmogorov distance $d_{\mathrm{K}}$, or in Wasserstein distance $d_{\mathrm{W}}$) if and
only if $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$.

Convention note: when $\sigma_n = 0$ (e.g. $p_n \in \{0, 1\}$ or $n < 3$), Lean's real division
evaluates $W_n = 0$; the full domain $0 \le p_n \le 1$ is sound without $0 < p_n < 1$ because if
$p_n \in \{0, 1\}$ infinitely often then $W_n \equiv 0$ along that subsequence (so normal
convergence fails) while $n p_n = 0$ or $n^2 (1 - p_n) = 0$ along that subsequence (so the
criterion also fails), whereas $n p_n \to \infty$ and $n^2 (1 - p_n) \to \infty$ force $0 < p_n
< 1$ and $\sigma_n > 0$ eventually. -/
def Sec3_2_1_triangles_rucinski : Prop :=
  ∀ {p : ℕ → ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    ((∀ x : ℝ,
        Filter.Tendsto
          (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
          Filter.atTop (nhds (stdNormalCDF x))) ↔
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) Filter.atTop Filter.atTop) ∧
    (Filter.Tendsto
        (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) Filter.atTop Filter.atTop) ∧
    (Filter.Tendsto
        (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ↔
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * (1 - p n)) Filter.atTop Filter.atTop)

/-- Section 3.2.1 power-law normal-convergence regime (unlabeled prose,
`SteinIntro.tex:942-944`, citing Ruciński 1988 `\cite{ruc88}`, Theorem 2 with $m(K_3) = 1$,
proved from scratch; `ISSUE-3.2.1` in `docs/SOURCE-ISSUES.md`): if $0 \le p_n \le 1$
satisfies $\lim_{n \to \infty} n^\alpha p_n = c > 0$ for some $\alpha \ge 0$, with $c < 1$
when $\alpha = 0$ (excluding the $p_n \to 1$ boundary, `ISSUE-3.2.1`), then:
1. for every $0 \le \alpha < 1$ (strictly containing the dependency-neighborhood regime $0 \le
   \alpha < 2/9$, since on $[2/9, 1)$ the Section 3.2.1 Stein upper bound fails to vanish), $W_n
   = (T_n - \mathbb{E}[T_n])/\sigma_n$ converges to $\mathcal{N}(0, 1)$ in Wasserstein distance,
   Kolmogorov distance, and pointwise CDF;
2. conversely, for $\alpha \ge 1$, normal convergence fails in pointwise CDF, $d_{\mathrm{K}}$,
   and $d_{\mathrm{W}}$.

Convention note: when $\sigma_n = 0$, Lean's real division sets $W_n = 0$; for $0 \le \alpha <
1$ with $c > 0$ (and $c < 1$ when $\alpha = 0$), $0 < p_n < 1$ and $\sigma_n > 0$ hold
eventually. -/
def Sec3_2_1_triangles_rucinski_power_regime : Prop :=
  ∀ {p : ℕ → ℝ} {α c : ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    0 ≤ α →
    0 < c →
    (α = 0 → c < 1) →
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) Filter.atTop (nhds c) →
    let T : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun _ G ↦ ((G.cliqueSet 3).ncard : ℝ)
    let μ : ℕ → ℝ := fun n ↦ ∫ G, T n G ∂erdosRenyi n (p n)
    let σ : ℕ → ℝ := fun n ↦ Real.sqrt (ProbabilityTheory.variance (T n) (erdosRenyi n (p n)))
    let W : (n : ℕ) → SimpleGraph (Fin n) → ℝ := fun n G ↦ (T n G - μ n) / σ n
    (α < 1 →
      Filter.Tendsto
        (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
        Filter.atTop (nhds 0) ∧
      (∀ x : ℝ,
        Filter.Tendsto
          (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
          Filter.atTop (nhds (stdNormalCDF x)))) ∧
    (1 ≤ α →
      ¬ (∀ x : ℝ,
          Filter.Tendsto
            (fun n : ℕ ↦ ((erdosRenyi n (p n)).map (W n)).real (Set.Iic x))
            Filter.atTop (nhds (stdNormalCDF x))) ∧
      ¬ Filter.Tendsto
          (fun n : ℕ ↦ kolmogorovDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          Filter.atTop (nhds 0) ∧
      ¬ Filter.Tendsto
          (fun n : ℕ ↦ wassersteinDist ((erdosRenyi n (p n)).map (W n)) stdNormalLaw)
          Filter.atTop (nhds 0))

/-- Proposition 3.6(1) (`\label{prop51}`, unlabeled item 1, `SteinIntro.tex:962-971`): if $(W,
W')$ is an exchangeable pair of real-valued random variables and $F : \mathbb{R}^2 \to
\mathbb{R}$ is antisymmetric ($F(x, y) = -F(y, x)$), then $\mathbb{E}[F(W, W')] = 0$.

No integrability hypothesis is imposed on $F(W, W')$; `Measurable F` is the typing of a
measurable function `ℝ × ℝ → ℝ`. -/
def Prop3_6_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℝ} {F : ℝ × ℝ → ℝ},
    IsExchangeablePair P W W' →
    Measurable F →
    (∀ x y : ℝ, F (x, y) = -F (y, x)) →
    ∫ ω, F (W ω, W' ω) ∂P = 0

/-- Proposition 3.6(2) (`\label{prop51}`, unlabeled item 2, `SteinIntro.tex:962`,
`SteinIntro.tex:967-971`; `D7`): if $(W, W')$ is an $a$-Stein pair with finite second moment
(`MemLp W 2 P`), then $\mathbb{E}[W] = 0$ and $\mathbb{E}[(W' - W)^2] = 2 a
\operatorname{Var}(W)$. -/
def Prop3_6_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ},
    IsSteinPair P a W W' →
    MemLp W 2 P →
    ∫ ω, W ω ∂P = 0 ∧ ∫ ω, (W' ω - W ω) ^ 2 ∂P = 2 * a * ProbabilityTheory.variance W P

/-- Theorem 3.7 (`\label{thm51}`, `SteinIntro.tex:983-988`): if $(W, W')$ is an $a$-Stein pair
with $\mathbb{E}[W^2] = 1$ and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])}}{\sqrt{2\pi}\,a} +
\frac{\mathbb{E}|W' - W|^3}{3a}$, with extended-nonnegative-real moments (`evariance`,
`lintegral`). -/
def Thm3_7 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ},
    IsSteinPair P a W W' →
    ∫ ω, W ω ^ 2 ∂P = 1 →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (Real.sqrt (2 * Real.pi) * a) +
      (∫⁻ ω, ENNReal.ofReal (|W' ω - W ω| ^ 3) ∂P) / ENNReal.ofReal (3 * a)

/-- Remark 3.3 (unlabeled, `SteinIntro.tex:990-999`): if a Markov kernel $\kappa$ is reversible
with respect to a probability measure $\mu$ (`(μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ`), then for
any measurable statistic $W$, $(W(X_0), W(X_1))$ is exchangeable under $\mu
\otimes_{\mathrm{m}} \kappa$. -/
def Rem3_3 : Prop :=
  ∀ {𝒳 α : Type*} [MeasurableSpace 𝒳] [MeasurableSpace α]
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (κ : ProbabilityTheory.Kernel 𝒳 𝒳) [ProbabilityTheory.IsMarkovKernel κ]
    {W : 𝒳 → α},
    (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ →
    Measurable W →
    IsExchangeablePair (μ ⊗ₘ κ) (fun p ↦ W p.1) (fun p ↦ W p.2)

/-- Remark 3.4 (unlabeled, `SteinIntro.tex:1000-1008`): for sub-$\sigma$-algebras $m_1 \le m_2$
of the ambient $\sigma$-algebra and any integrable random variable $Y$,
$\operatorname{Var}(\mathbb{E}[Y \mid m_1]) \le \operatorname{Var}(\mathbb{E}[Y \mid m_2])$
in `ℝ≥0∞` (`ProbabilityTheory.evariance`). -/
def Rem3_4 : Prop :=
  ∀ {Ω : Type*} {m₀ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {m₁ m₂ : MeasurableSpace Ω} {Y : Ω → ℝ},
    m₁ ≤ m₂ →
    m₂ ≤ m₀ →
    Integrable Y P →
    ProbabilityTheory.evariance (P[Y | m₁]) P ≤
      ProbabilityTheory.evariance (P[Y | m₂]) P

/-- Remark 3.5 (unlabeled, `SteinIntro.tex:1009-1024`; `ISSUE-TYPO-3.5` and `ISSUE-3.5-OU` in
`docs/SOURCE-ISSUES.md`): the Ornstein–Uhlenbeck transition kernel `ouKernel a` (`x ↦
𝒩(e^{-a} x, 1 - e^{-2a})` for `a > 0`) satisfies the three infinitesimal diffusion
properties as `a → 0⁺`:
1. $\mathbb{E}[D(t + a) - D(t) \mid D(t) = x] = -a x + o(a)$,
2. $\mathbb{E}[(D(t + a) - D(t))^2 \mid D(t) = x] = 2a + o(a)$,
3. $\mathbb{P}(|D(t + a) - D(t)| > \varepsilon \mid D(t) = x) = o(a)$ for all $\varepsilon > 0$,
   and for every $a > 0$, `ouKernel a` is a Markov kernel reversible with respect to
   `stdNormalLaw`, has stationary distribution `stdNormalLaw`, and realizes a $(1 -
   e^{-a})$-Stein pair under `stdNormalLaw ⊗ₘ ouKernel a` (`SteinIntro.tex:1021-1023`).
   Uniqueness from the infinitesimal properties (`SteinIntro.tex:1018-1019`) is formalized in
   `Rem3_5_uniqueness_restricted` and `Rem3_5_uniqueness_probTail_restricted`. -/
def Rem3_5 : Prop :=
  (∀ x : ℝ,
    Filter.Tendsto
      (fun a : ℝ ↦ ((∫ y, (y - x) ∂ouKernel a x) - (-a * x)) / a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
  (∀ x : ℝ,
    Filter.Tendsto
      (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂ouKernel a x) - 2 * a) / a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
  (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
    Filter.Tendsto
      (fun a : ℝ ↦ (ouKernel a x).real {y : ℝ | ε < |y - x|} / a)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
  (∀ a : ℝ, 0 < a →
    ProbabilityTheory.IsMarkovKernel (ouKernel a) ∧
      (stdNormalLaw ⊗ₘ ouKernel a).map Prod.swap = stdNormalLaw ⊗ₘ ouKernel a ∧
      stdNormalLaw.bind (ouKernel a) = stdNormalLaw ∧
      IsSteinPair (stdNormalLaw ⊗ₘ ouKernel a) (1 - Real.exp (-a)) Prod.fst Prod.snd)

/-- Remark 3.5, uniqueness, restricted (unlabeled, `SteinIntro.tex:1009-1024`; `ISSUE-3.5-OU`
and `ISSUE-TYPO-3.5` in `docs/SOURCE-ISSUES.md`):
1. (*Non-vacuity*): `ouKernel` forms a Chapman–Kolmogorov Markov semigroup on `(0, ∞)`
   satisfying the Lindeberg second-moment tail condition and small-time quadratic moment
   domination;
2. (*Stein generator & stationary-law uniqueness*): for any Markov kernel family `(K a)_{a > 0}`
   satisfying Remark 3.5 Items 1–2 and the Lindeberg second-moment tail condition, local
   second-moment integrability yields the infinitesimal Stein generator `normalSteinOp f x =
   f'(x) - x f(x)` on primitives `G x = ∫ u in 0..x, f u` of `C_b^1` functions, and under
   small-time quadratic moment domination every square-integrable probability measure `μ` with
   `μ.bind (K a) = μ` for small `a > 0` equals `stdNormalLaw`;
3. (*Semigroup uniqueness*): if `(K t)_{t > 0}` also satisfies Chapman–Kolmogorov `K (s + t) = K
   t ∘ₖ K s` under small-time quadratic moment domination, then `K t = ouKernel t` for all `t >
   0`, and any probability measure `μ` with `μ.bind (K t₀) = μ` for some `t₀ > 0` equals
   `stdNormalLaw`.

Difference from printed result (`ISSUE-3.5-OU`): Remark 3.5 (`SteinIntro.tex:1018-1019`) states
heuristically `"These three properties determine the O-U diffusion process"`; as the project's
reading of `"diffusion process"` without assuming Chapman–Kolmogorov semigroup structure, this
entry adds (i) the Lindeberg second-moment tail in place of Item 3's probability tail and (ii)
small-time quadratic moment domination justifying expectation interchanges (for
Chapman–Kolmogorov semigroups, `Rem3_5_uniqueness_probTail_restricted` keeps the literally
printed probability tail). -/
def Rem3_5_uniqueness_restricted : Prop :=
  ((∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t →
      ouKernel (s + t) = ProbabilityTheory.Kernel.comp (ouKernel t) (ouKernel s)) ∧
    (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂ouKernel a x) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Ioo 0 a₀, ∀ x : ℝ,
        Integrable (fun y : ℝ ↦ (y - x) ^ 2) (ouKernel a x) ∧
          |∫ y, (y - x) ∂ouKernel a x| ≤ C * a * (1 + |x|) ∧
          (∫ y, (y - x) ^ 2 ∂ouKernel a x) ≤ C * a * (1 + x ^ 2))) ∧
  (∀ K : ℝ → ProbabilityTheory.Kernel ℝ ℝ,
    (∀ a : ℝ, 0 < a → ProbabilityTheory.IsMarkovKernel (K a)) →
    (∀ x : ℝ,
      Filter.Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
    (∀ x : ℝ,
      Filter.Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
    (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun a : ℝ ↦ (∫ y in {y : ℝ | ε < |y - x|}, (y - x) ^ 2 ∂K a x) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
    (((∀ x : ℝ, ∀ᶠ a in nhdsWithin 0 (Set.Ioi 0),
          Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x)) →
        ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
          (∃ B : ℝ, (∀ u : ℝ, |f u| ≤ B) ∧ (∀ u : ℝ, |deriv f u| ≤ B)) →
          ∀ x : ℝ,
            Filter.Tendsto
              (fun a : ℝ ↦
                (∫ y, ((∫ u in (0 : ℝ)..y, f u) - (∫ u in (0 : ℝ)..x, f u)) ∂K a x) / a)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (normalSteinOp f x))) ∧
      ((∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
          ∀ a ∈ Set.Ioo 0 a₀, ∀ x : ℝ,
            Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x) ∧
              |∫ y, (y - x) ∂K a x| ≤ C * a * (1 + |x|) ∧
              (∫ y, (y - x) ^ 2 ∂K a x) ≤ C * a * (1 + x ^ 2)) →
        (∀ μ : Measure ℝ, IsProbabilityMeasure μ →
          Integrable (fun x : ℝ ↦ x ^ 2) μ →
          (∀ᶠ a in nhdsWithin 0 (Set.Ioi 0), μ.bind (K a) = μ) →
          μ = stdNormalLaw) ∧
        ((∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t →
            K (s + t) = ProbabilityTheory.Kernel.comp (K t) (K s)) →
          (∀ t : ℝ, 0 < t → K t = ouKernel t) ∧
            (∀ μ : Measure ℝ, IsProbabilityMeasure μ →
              (∃ t₀ : ℝ, 0 < t₀ ∧ μ.bind (K t₀) = μ) →
              μ = stdNormalLaw)))))

/-- Remark 3.5, semigroup uniqueness under Ross's printed probability tail, restricted
(unlabeled, `SteinIntro.tex:1009-1024`; `ISSUE-3.5-OU` and `ISSUE-TYPO-3.5` in
`docs/SOURCE-ISSUES.md`):
1. (*Non-vacuity*): `ouKernel` is a Chapman–Kolmogorov Markov semigroup satisfying Remark 3.5's
   printed Items 1–3 and small-time quadratic moment domination;
2. (*Semigroup & stationary-law uniqueness*): every Chapman–Kolmogorov Markov semigroup `(K
   t)_{t > 0}` satisfying Remark 3.5's literally printed Items 1–3 (including the probability
   tail `(K a x).real {y | ε < |y - x|} = o(a)`) and small-time quadratic moment domination
   satisfies `K t = ouKernel t` for all `t > 0`, and every probability measure `μ` with `μ.bind
   (K t₀) = μ` for some `t₀ > 0` equals `stdNormalLaw`.

Difference from printed result (`ISSUE-3.5-OU`): keeps Remark 3.5's literally printed Items 1–3
(without Lindeberg strengthening of Item 3), making explicit Chapman–Kolmogorov semigroup
structure and small-time quadratic moment domination as the regularity reading of `"diffusion
process"`. -/
def Rem3_5_uniqueness_probTail_restricted : Prop :=
  ((∀ a : ℝ, 0 < a → ProbabilityTheory.IsMarkovKernel (ouKernel a)) ∧
    (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t →
      ouKernel (s + t) = ProbabilityTheory.Kernel.comp (ouKernel t) (ouKernel s)) ∧
    (∀ x : ℝ,
      Filter.Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ∂ouKernel a x) - (-a * x)) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ x : ℝ,
      Filter.Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂ouKernel a x) - 2 * a) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun a : ℝ ↦ (ouKernel a x).real {y : ℝ | ε < |y - x|} / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Ioo 0 a₀, ∀ x : ℝ,
        Integrable (fun y : ℝ ↦ (y - x) ^ 2) (ouKernel a x) ∧
          |∫ y, (y - x) ∂ouKernel a x| ≤ C * a * (1 + |x|) ∧
          (∫ y, (y - x) ^ 2 ∂ouKernel a x) ≤ C * a * (1 + x ^ 2))) ∧
  (∀ K : ℝ → ProbabilityTheory.Kernel ℝ ℝ,
    (∀ a : ℝ, 0 < a → ProbabilityTheory.IsMarkovKernel (K a)) →
    (∀ s : ℝ, 0 < s → ∀ t : ℝ, 0 < t →
      K (s + t) = ProbabilityTheory.Kernel.comp (K t) (K s)) →
    (∀ x : ℝ,
      Filter.Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ∂K a x) - (-a * x)) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
    (∀ x : ℝ,
      Filter.Tendsto
        (fun a : ℝ ↦ ((∫ y, (y - x) ^ 2 ∂K a x) - 2 * a) / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
    (∀ x : ℝ, ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun a : ℝ ↦ (K a x).real {y : ℝ | ε < |y - x|} / a)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
    (∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Ioo 0 a₀, ∀ x : ℝ,
        Integrable (fun y : ℝ ↦ (y - x) ^ 2) (K a x) ∧
          |∫ y, (y - x) ∂K a x| ≤ C * a * (1 + |x|) ∧
          (∫ y, (y - x) ^ 2 ∂K a x) ≤ C * a * (1 + x ^ 2)) →
    (∀ t : ℝ, 0 < t → K t = ouKernel t) ∧
      (∀ μ : Measure ℝ, IsProbabilityMeasure μ →
        (∃ t₀ : ℝ, 0 < t₀ ∧ μ.bind (K t₀) = μ) →
        μ = stdNormalLaw))

/-- Display `(3.18)` (`\label{511}`, `SteinIntro.tex:1043-1046`): for an $a$-Stein pair $(W,
W')$ and a twice-differentiable function $f : \mathbb{R} \to \mathbb{R}$ with $|f| \le B_0$,
$|f'| \le B_1$, and $|f''| \le B_2$, $|\mathbb{E}[f'(W) - W f(W)]| \le B_1\,\mathbb{E}|1 -
\mathbb{E}[(W' - W)^2 \mid W]/(2a)| + (B_2 / (6a))\,\mathbb{E}|W' - W|^3$, stated with
`ℝ≥0∞` `lintegral`s on the right-hand side per `D1` so non-$L^3$ increments evaluate to `⊤`
rather than junk `0`. -/
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

/-- Wasserstein corollary of `(3.18)` (`\label{511}`, `SteinIntro.tex:1043-1049`): taking the
supremum of `Sec3_3_eq3_18` over `normalWassersteinClass` ($B_1 = \sqrt{2/\pi}$, $B_2 = 2$)
via Theorem 3.1 bounds $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z))$ without requiring
fourth moments, with cubic coefficient $2 / (6a) = 1 / (3a)$. -/
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

/-- Example 3.6, Stein-pair verification (unlabeled, `SteinIntro.tex:1053-1069`): for
independent centered unit-variance random variables $X_1, \dots, X_n$ with
$\mathbb{E}[X_i^4] < \infty$, an independent copy $(X_1', \dots, X_n')$, and an independent
uniform random index $I \in \{1, \dots, n\}$, $(W, W')$ with $W = n^{-1/2}\sum_i X_i$ and
$W' = W - X_I/\sqrt{n} + X_I'/\sqrt{n}$ is a $(1/n)$-Stein pair. -/
def Ex3_6_steinPair : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (X' i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    let W' : Ω → ℝ := fun ω ↦ W ω - X (I ω) ω / Real.sqrt n + X' (I ω) ω / Real.sqrt n
    IsSteinPair P (1 / (n : ℝ)) W W'

/-- Example 3.6, corrected Wasserstein bound (unlabeled, `SteinIntro.tex:1053-1097`; `ISSUE-3.6`
and `ISSUE-TYPO-3.5` in `docs/SOURCE-ISSUES.md`): for all $n \ge 1$, applying Theorem 3.7 to
the $(1/n)$-Stein pair $(W, W')$ yields second term $\frac{8}{3 n^{3/2}} \sum_{i=1}^n
\mathbb{E}|X_i|^3$.

Difference from printed result (`ISSUE-3.6`): replaces the printed second term $\frac{2}{3n}
\sum_{i=1}^n \mathbb{E}|X_i|^3$ at `SteinIntro.tex:1089` (resulting from a dropped factor of
$1/n$ at `SteinIntro.tex:1074`) by $\frac{8}{3 n^{3/2}} \sum_{i=1}^n \mathbb{E}|X_i|^3$,
recovering the $O(n^{-1/2})$ i.i.d. rate claimed at `SteinIntro.tex:1091` (the printed `2/(3n)`
bound itself also holds for all $n \ge 1$ as `Ex3_6_printed`). -/
def Ex3_6_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n} {Z : Ω' → ℝ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (X' i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          8 / (3 * (n : ℝ) ^ (3 / 2 : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P)

/-- Example 3.6, restricted printed Wasserstein bound (unlabeled, `SteinIntro.tex:1053-1097`;
`ISSUE-3.6` in `docs/SOURCE-ISSUES.md`): for $n \ge 16$, $\frac{8}{3 n^{3/2}} \le
\frac{2}{3n}$, so the printed bound at `SteinIntro.tex:1089` holds with second term
$\frac{2}{3n} \sum_{i=1}^n \mathbb{E}|X_i|^3$.

Difference from printed result (`ISSUE-3.6`): restricts $n \ge 1$ to $n \ge 16$ so the printed
`2/(3n)` second term dominates `Ex3_6_corrected`'s `8/(3 n^{3/2})` term (`Ex3_6_printed` proves
the printed bound for all $n \ge 1$ by handling $1 \le n \le 15$ directly). -/
def Ex3_6_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} (hn : 0 < n) {X X' : Fin n → Ω → ℝ} {I : Ω → Fin n} {Z : Ω' → ℝ},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (X' i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    ProbabilityTheory.IdentDistrib (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P P →
    ProbabilityTheory.IndepFun (fun ω i ↦ X' i ω) (fun ω i ↦ X i ω) P →
    Measurable I →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ X' i ω)) P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    16 ≤ n →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P)

/-- Example 3.6, printed Wasserstein bound (unlabeled, `SteinIntro.tex:1053-1097`; `ISSUE-3.6`
in `docs/SOURCE-ISSUES.md`): for all $n \ge 1 and independent mean-zero, unit-variance
random variables $X_1, \dots, X_n \in L^4(P)$, $W = (\sum_{i=1}^n X_i)/\sqrt{n}$ satisfies
the literally printed bound $d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sqrt{\frac{2}{\pi}}\,\frac{\sqrt{\sum_{i=1}^n \mathbb{E}[X_i^4]}}{2n} +
\frac{2}{3n}\sum_{i=1}^n \mathbb{E}|X_i|^3$ at `SteinIntro.tex:1089`. -/
def Ex3_6_printed : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
    0 < n →
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 4 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ProbabilityTheory.variance (X i) P = 1) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let W : Ω → ℝ := fun ω ↦ (∑ i : Fin n, X i ω) / Real.sqrt n
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i : Fin n, ∫ ω, X i ω ^ 4 ∂P) /
            (2 * (n : ℝ)) +
          2 / (3 * (n : ℝ)) * ∑ i : Fin n, ∫ ω, |X i ω| ^ 3 ∂P)

/-- Section 3.3.1 anti-voter ergodicity and stationary uniqueness, corrected (unlabeled prose in
Section 3.3.1, `SteinIntro.tex:1101-1111`, citing Aldous–Fill `[af10]`; `ISSUE-3.8` in
`docs/SOURCE-ISSUES.md`): if $G$ is a connected $r$-regular finite simple graph that is
neither bipartite nor isomorphic to `cycleGraph |V|`, then:
1. Every one-step transition of `antiVoterStep G` lands in the absorbing set of non-constant
   labelings $\mathcal{N}(V) = \{x : V \to \mathrm{Bool} \mid (\exists a, x_a = \mathrm{true})
   \wedge (\exists b, x_b = \mathrm{false})\}$;
2. On $\mathcal{N}(V)$, the anti-voter Markov chain is irreducible and aperiodic ($\forall x, y
   \in \mathcal{N}(V), \exists N, \forall t \ge N, P^t(x, y) > 0$);
3. The anti-voter chain on `V → Bool` has a unique stationary probability distribution, whose
   support is $\mathcal{N}(V)$.

Difference from printed result (`ISSUE-3.8`): (1) irreducibility and aperiodicity at
`SteinIntro.tex:1110-1111` are stated on the absorbing set $\mathcal{N}(V)$ of non-constant
labelings rather than on $\{-1, 1\}^V$ (constant labelings have zero incoming transition
probability, `antiVoterStep_const_eq_zero`); (2) `G.Connected` is added because stationary
uniqueness fails on disconnected graphs such as $G = K_3 \sqcup C_4$
(`not_Sec3_3_1_antiVoter_unique_printed`);
(3) `G.IsRegularOfDegree r` is retained to match §3.3.1 while the library theorem
    `antiVoter_ergodic_and_unique_stationary` drops $r$-regularity. -/
def Sec3_3_1_antiVoter_ergodic_corrected : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ},
    G.IsRegularOfDegree r →
    G.Connected →
    ¬ G.IsBipartite →
    IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) →
    (∀ ⦃x y : V → Bool⦄,
      antiVoterStep G x y ≠ 0 →
      (∃ a : V, y a = true) ∧ (∃ b : V, y b = false)) ∧
    (∀ ⦃x y : V → Bool⦄,
      ((∃ a : V, x a = true) ∧ (∃ b : V, x b = false)) →
      ((∃ a : V, y a = true) ∧ (∃ b : V, y b = false)) →
      ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
        0 < ((fun p : PMF (V → Bool) ↦ p.bind (antiVoterStep G))^[t] (PMF.pure x)) y) ∧
    (∃ ν : Measure (V → Bool),
      IsProbabilityMeasure ν ∧
      IsAntiVoterStationary G ν ∧
      (∀ x : V → Bool,
        ν {x} ≠ 0 ↔ (∃ a : V, x a = true) ∧ (∃ b : V, x b = false)) ∧
      ∀ μ : Measure (V → Bool),
        IsProbabilityMeasure μ → IsAntiVoterStationary G μ → μ = ν)

/-- Theorem 3.8 (`\label{thm52}`, `SteinIntro.tex:1114-1127`): for the anti-voter Markov chain
on an $r$-regular finite simple graph $G$ on $n = |V|$ vertices that is neither bipartite
nor a cycle, if $X$ has a stationary distribution and $X'$ is one step of the chain from
$X$, then $(W, W')$ is a $(2/n)$-Stein pair and $d_{\mathrm{W}}(\mathcal{L}(W),
\mathcal{L}(Z)) \le \frac{4n}{3\sigma^3} +
\frac{\sqrt{\operatorname{Var}(Q)}}{r\sigma^2\sqrt{2\pi}}$. -/
def Thm3_8 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X X' : Ω → V → Bool} {Z : Ω' → ℝ},
    G.IsRegularOfDegree r →
    ¬ G.IsBipartite →
    IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) →
    Measurable X →
    Measurable X' →
    IsAntiVoterStationary G (P.map X) →
    (∀ x y : V → Bool, P {ω | X ω = x ∧ X' ω = y} = P {ω | X ω = x} * antiVoterStep G x y) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let n : ℝ := Fintype.card V
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    let S' : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X' ω v)
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    let W' : Ω → ℝ := fun ω ↦ S' ω / σ
    let Q : Ω → ℝ := fun ω ↦ ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (X ω i) * spin (X ω j)
    IsSteinPair P (2 / n) W W' ∧
      wassersteinDist (P.map W) (P'.map Z) ≤
        ENNReal.ofReal
          (4 * n / (3 * σ ^ 3) +
            Real.sqrt (ProbabilityTheory.variance Q P) /
              ((r : ℝ) * σ ^ 2 * Real.sqrt (2 * Real.pi)))

/-- Section 3.3.1 non-reversibility of the anti-voter Markov chain (unlabeled prose,
`SteinIntro.tex:1130-1131`): there exists a finite connected $r$-regular simple graph $G$
satisfying the Section 3.3.1 hypotheses (non-bipartite, not isomorphic to `cycleGraph |V|`,
witnessed by the $3$-regular prism $K_3 \square K_2$ on `Fin 6`; `G.Connected` strengthens
the existential witness beyond the printed hypotheses) such that the anti-voter chain has a
stationary probability distribution, and every stationary probability distribution $\mu$
violates detailed balance at some pair of configurations $(x, y)$. -/
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

/-- Lemma 3.9 (`\label{lem51}`, `SteinIntro.tex:1133-1136`): if $W$ and $W'$ are identically
distributed integer-valued random variables defined on the same probability space such that
$\mathbb{P}(|W' - W| \le 1) = 1$, then $(W, W')$ is an exchangeable pair. -/
def Lem3_9 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W W' : Ω → ℤ},
    ProbabilityTheory.IdentDistrib W W' P P →
    (∀ᵐ ω ∂P, |W' ω - W ω| ≤ 1) →
    IsExchangeablePair P W W'

/-- Lemma 3.10 (unlabeled, `SteinIntro.tex:1208-1214`, citing Aldous–Fill `[af10]`): for any
stationary distribution of the anti-voter Markov chain on an $r$-regular finite simple graph
$G$ ($r > 0$), the variance $\sigma^2$ of the total spin $S = \sum_{v \in V}
\operatorname{spin}(X_v)$ satisfies $\frac{2 \kappa(G)}{r} \le \sigma^2 \le |V|$. -/
def Lem3_10 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → V → Bool},
    G.IsRegularOfDegree r →
    0 < r →
    Measurable X →
    IsAntiVoterStationary G (P.map X) →
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    2 * (kappa G : ℝ) / (r : ℝ) ≤ ProbabilityTheory.variance S P ∧
      ProbabilityTheory.variance S P ≤ (Fintype.card V : ℝ)

/-- Section 3.4 size-bias Stein identity (eq. `(3.23)` `\label{71}`, `SteinIntro.tex:1232-1236`;
`ISSUE-TYPO-3.4a` in `docs/SOURCE-ISSUES.md`): for $X \ge 0$ a.s. in $L^2$ with $\sigma^2 =
\operatorname{Var}(X) > 0$, $\mu = \mathbb{E}[X]$, $W = (X - \mu)/\sigma$, and size-bias
$X^s$ on the same space, if $f(W)$ and $X f(W)$ are integrable then $f((X^s - \mu)/\sigma)$
is integrable and $\mathbb{E}[W f(W)] = \frac{\mu}{\sigma}(\mathbb{E}[f((X^s - \mu)/\sigma)]
- \mathbb{E}[f(W)])$. -/
def Sec3_4_sizeBias_identity : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xs : Ω → ℝ} {f : ℝ → ℝ},
    0 ≤ᵐ[P] X →
    MemLp X 2 P →
    0 < ProbabilityTheory.variance X P →
    IsSizeBias P X P Xs →
    Measurable f →
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    let W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
    Integrable (fun ω ↦ X ω * f (W ω)) P →
    Integrable (fun ω ↦ f (W ω)) P →
    Integrable (fun ω ↦ f ((Xs ω - μ) / σ)) P ∧
      ∫ ω, W ω * f (W ω) ∂P =
        μ / σ * ((∫ ω, f ((Xs ω - μ) / σ) ∂P) - ∫ ω, f (W ω) ∂P)

/-- Proposition 3.11, restricted to $\mu > 0$ (unlabeled, `SteinIntro.tex:1239-1245`;
`ISSUE-3.11` in `docs/SOURCE-ISSUES.md`, `D8`): for $X \ge 0$ a.s. integrable with $\mu =
\mathbb{E}[X] > 0$, every size-bias random variable $X^s$ has law $dF^s(x) =
\frac{x}{\mu}\,dF(x)$, and conversely this weighted measure is a probability measure whose
identity map has the size-bias distribution with respect to $X$.

Difference from printed result (`ISSUE-3.11`): strengthens $\mu = \mathbb{E}[X] < \infty$ to $0
< \mu < \infty$, because at $\mu = 0$ ($X = 0$ a.s.) $\frac{x}{\mu}\,dF(x)$ divides by zero and
every probability law satisfies Definition 3.7. -/
def Prop3_11_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ},
    0 ≤ᵐ[P] X →
    Integrable X P →
    0 < ∫ ω, X ω ∂P →
    let μ : ℝ := ∫ ω, X ω ∂P
    (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {Xs : Ω' → ℝ},
        IsSizeBias P X P' Xs →
        P'.map Xs = (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μ))) ∧
      (let ν : Measure ℝ := (P.map X).withDensity (fun x ↦ ENNReal.ofReal (x / μ))
       IsProbabilityMeasure ν ∧ IsSizeBias P X ν id)

/-- Corollary 3.12, restricted to $\mu > 0$ (unlabeled, `SteinIntro.tex:1246-1252`; `ISSUE-3.11`
in `docs/SOURCE-ISSUES.md`): if $X \ge 0$ is a nonnegative integer-valued integrable random
variable with $\mu = \mathbb{E}[X] > 0$ and $X^s$ has the size-bias distribution of $X$,
then $\mathbb{P}(X^s = k) = \frac{k\,\mathbb{P}(X = k)}{\mu}$ for all $k \in \mathbb{N}$.

Difference from printed result (`ISSUE-3.11`): strengthens $\mu = \mathbb{E}[X] < \infty$ to $0
< \mu < \infty$, because at $\mu = 0$ ($X = 0$ a.s.) $\frac{k\,\mathbb{P}(X = k)}{\mu}$ divides
by zero and fails at $k = 0$ for any $X^s$ with $\mathbb{P}(X^s = 0) > 0$. -/
def Cor3_12_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Xs : Ω' → ℝ},
    (∀ᵐ ω ∂P, X ω ∈ Set.range (Nat.cast : ℕ → ℝ)) →
    Integrable X P →
    0 < ∫ ω, X ω ∂P →
    IsSizeBias P X P' Xs →
    let μ : ℝ := ∫ ω, X ω ∂P
    ∀ k : ℕ, P'.real {ω' | Xs ω' = k} = (k : ℝ) * P.real {ω | X ω = k} / μ

/-- Theorem 3.13 (`\label{thm71}`, `SteinIntro.tex:1255-1261`): Wasserstein normal approximation
bound via size-bias coupling on the same probability space, with extended-nonnegative-real
moments (`evariance`, `lintegral`). -/
def Thm3_13 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X Xs : Ω → ℝ} {Z : Ω' → ℝ},
    Measurable X →
    0 ≤ᵐ[P] X →
    MemLp X 2 P →
    0 < ProbabilityTheory.variance X P →
    IsSizeBias P X P Xs →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let μ : ℝ := ∫ ω, X ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X P)
    let W : Ω → ℝ := fun ω ↦ (X ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal (μ / σ ^ 2 * Real.sqrt (2 / Real.pi)) *
          ProbabilityTheory.evariance
            (P[fun ω ↦ Xs ω - X ω | MeasurableSpace.comap X inferInstance]) P ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (μ / σ ^ 3) * ∫⁻ ω, ENNReal.ofReal ((Xs ω - X ω) ^ 2) ∂P

/-- Proposition 3.14 (`\label{prop71}`, `SteinIntro.tex:1284-1299`; `ISSUE-3.14` in
`docs/SOURCE-ISSUES.md`): size-bias coupling recipe for a sum $X = \sum_{i=1}^n X_i$ of
nonnegative integrable random variables with total mean $\mu = \sum_i \mu_i > 0$. -/
def Prop3_14 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xs : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, 0 ≤ᵐ[P] X i) →
    (∀ i : Fin n, Integrable (X i) P) →
    0 < (∑ i : Fin n, ∫ ω, X i ω ∂P) →
    (∀ i : Fin n, IsSizeBias P (X i) P (Xs i)) →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      P.map (fun ω ↦ (Xs i ω, Y i ω)) =
        (P.map (Xs i)) ⊗ₘ
          ProbabilityTheory.condDistrib (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) (X i) P) →
    Measurable I →
    (∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P) →
    ProbabilityTheory.IndepFun I
      (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω, fun i ↦ Y i ω)) P →
    let Xs_total : Ω → ℝ := fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + Xs (I ω) ω
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P Xs_total

/-- Corollary 3.15 (`\label{cor71}`, `SteinIntro.tex:1319-1325`; `ISSUE-TYPO-3.15` and
`ISSUE-3.14` in `docs/SOURCE-ISSUES.md`): size-bias coupling $X^s = X - X_I + X_I^s$ for a
sum of independent nonnegative integrable random variables $X_1, \dots, X_n$ with $\mu =
\sum_i \mathbb{E}[X_i] > 0$. -/
def Cor3_15 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xs : Fin n → Ω → ℝ} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, 0 ≤ᵐ[P] X i) →
    (∀ i : Fin n, Integrable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, IsSizeBias P (X i) P (Xs i)) →
    (∀ i : Fin n,
      ProbabilityTheory.IndepFun (Xs i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) P) →
    Measurable I →
    (∀ i : Fin n,
      P.real (I ⁻¹' {i}) = (∫ ω, X i ω ∂P) / ∑ j : Fin n, ∫ ω, X j ω ∂P) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xs i ω)) P →
    0 < (∑ i : Fin n, ∫ ω, X i ω ∂P) →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ i : Fin n, X i ω) - X (I ω) ω + Xs (I ω) ω)

/-- Corollary 3.16 (`\label{cor72}`, `SteinIntro.tex:1326-1332`): size-bias coupling $X^s =
\sum_{j \ne I} X_j^{(I)} + 1$ for a sum of zero-one random variables $X_1, \dots, X_n$ with
$p_i = \mathbb{P}(X_i = 1)$ and $\mu = \sum_i p_i > 0$. -/
def Cor3_16 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ}
    {Y : (i : Fin n) → Ω → ({j : Fin n // j ≠ i} → ℝ)} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
    let p : Fin n → ℝ := fun i ↦ P.real (X i ⁻¹' {1})
    let μ : ℝ := ∑ i : Fin n, p i
    0 < μ →
    (∀ i : Fin n, AEMeasurable (Y i) P) →
    (∀ i : Fin n,
      0 < p i →
      P.map (Y i) =
        (ProbabilityTheory.cond P (X i ⁻¹' {1})).map
          (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω)) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = p i / μ) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Y i ω)) P →
    IsSizeBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j : {j : Fin n // j ≠ I ω}, Y (I ω) ω j) + 1)

/-- Example 3.8 (`\label{ex71}`, `SteinIntro.tex:1349-1353`): Ross prints no formula in Example
3.8 and leaves the derivation as an exercise; this bound is the project's solution of that
exercise, combining Corollary 3.15 (`\ref{cor71}`), Theorem 3.13 (`\ref{thm71}`), and Remark
3.4 under the independent size-bias coupling ($X_i^s$ independent of $X$ and mixture index
$I$ with $\mathbb{P}(I = i) = \mu_i / \mu$, constructed on an enlarged product space).
Reading notes:
(1) nonnegativity (`0 ≤ᵐ[P] X i`) comes from Corollary 3.15's setting (size-bias requires $X_i
    \ge 0$), not from the exercise's wording; (2) Ross gives no formula, so the right-hand side
    is the explicit solution of the exercise; (3) $\sigma^2 = \operatorname{Var}(\sum_i X_i) >
    0$ is typing. -/
def Ex3_8 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
    (∀ i : Fin n, 0 ≤ᵐ[P] X i) →
    (∀ i : Fin n, MemLp (X i) 3 P) →
    ProbabilityTheory.iIndepFun X P →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let μ : ℝ := ∫ ω, S ω ∂P
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ (S ω - μ) / σ
    wassersteinDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (1 / σ ^ 2 *
            Real.sqrt
              (2 / Real.pi *
                ∑ i : Fin n, (∫ ω, X i ω ∂P) ^ 2 * ProbabilityTheory.variance (X i) P) +
          1 / σ ^ 3 *
            ∑ i : Fin n, ((∫ ω, X i ω ^ 3 ∂P) - (∫ ω, X i ω ∂P) * ∫ ω, X i ω ^ 2 ∂P))

/-- Example 3.9, size-bias realization and increment identity (`\label{ex72}`,
`SteinIntro.tex:1379-1383`, `SteinIntro.tex:1354-1367`): for $G \sim G(n, p)$ ($n \ge 1$, $0
\le p \le 1$) and an independent uniform vertex $I \in \{1, \dots, n\}$, erasing all edges
incident to $I$ (`SimpleGraph.deleteIncidenceSet`) yields a size-bias version $X^s$ of the
isolated-vertex count $X = \sum_{i=1}^n X_i$, with increment $X^s - X = D_I +
\mathbf{1}_{d_I > 0}$, where $d_i$ is the degree of $i$ in $G$ and $D_i$ is the number of
degree-one neighbors of $i$. -/
def Ex3_9_sizeBias : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {p : ℝ} {G : Ω → SimpleGraph (Fin n)} {I : Ω → Fin n},
    0 ≤ p →
    p ≤ 1 →
    Measurable G →
    P.map G = erdosRenyi n p →
    Measurable I →
    ProbabilityTheory.IndepFun I G P →
    P.map I = (@PMF.uniformOfFintype (Fin n) inferInstance ⟨⟨0, hn⟩⟩).toMeasure →
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i H ↦ {K : SimpleGraph (Fin n) | K.IsIsolated i}.indicator 1 H
    let X : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i (G ω)
    let Xs : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X_ind i ((G ω).deleteIncidenceSet (I ω))
    let d : Fin n → Ω → ℕ := fun i ω ↦ ((G ω).neighborSet i).ncard
    let D : Fin n → Ω → ℝ :=
      fun i ω ↦ ({j : Fin n | (G ω).Adj i j ∧ ((G ω).neighborSet j).ncard = 1}.ncard : ℝ)
    IsSizeBias P X P Xs ∧
      ∀ ω : Ω, Xs ω - X ω = D (I ω) ω + {ω' : Ω | 0 < d (I ω') ω'}.indicator 1 ω

/-- Example 3.9, verified moment formulas (`\label{ex72}`, eq. `(3.28)` `\label{77}`,
`SteinIntro.tex:1370-1379`, `SteinIntro.tex:1406-1409`, `SteinIntro.tex:1354`; see
`ISSUE-3.9` in `docs/SOURCE-ISSUES.md` for the false printed formulas at
`SteinIntro.tex:1395` and `SteinIntro.tex:1397`): for $G \sim G(n, p)$ with $0 \le p \le 1$,
$\mu = \mathbb{E}[X] = n(1 - p)^{n - 1}$, $\mathbb{E}[X_i X_j] = (1 - p)^{2n - 3}$ ($i \ne
j$), $\sigma^2 = \operatorname{Var}(X) = \mu[1 + (n p - 1)(1 - p)^{n - 2}]$ ($n \ge 2$), and
$\mathbb{E}[D_i^2] = (n - 1)p(1 - p)^{n - 2} + (n - 1)(n - 2)p^2(1 - p)^{2n - 5}$ ($n \ge
3$). -/
def Ex3_9_moments : Prop :=
  ∀ {n : ℕ} {p : ℝ},
    0 ≤ p →
    p ≤ 1 →
    let X_ind : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i G ↦ {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator 1 G
    let X : SimpleGraph (Fin n) → ℝ := fun G ↦ ∑ i : Fin n, X_ind i G
    let D : Fin n → SimpleGraph (Fin n) → ℝ :=
      fun i G ↦ ({j : Fin n | G.Adj i j ∧ (G.neighborSet j).ncard = 1}.ncard : ℝ)
    (∫ G, X G ∂erdosRenyi n p = (n : ℝ) * (1 - p) ^ (n - 1)) ∧
      (∀ i j : Fin n, i ≠ j →
        ∫ G, X_ind i G * X_ind j G ∂erdosRenyi n p = (1 - p) ^ (2 * n - 3)) ∧
      (2 ≤ n →
        ProbabilityTheory.variance X (erdosRenyi n p) =
          (n : ℝ) * (1 - p) ^ (n - 1) * (1 + ((n : ℝ) * p - 1) * (1 - p) ^ (n - 2))) ∧
      (3 ≤ n →
        ∀ i : Fin n,
          ∫ G, D i G ^ 2 ∂erdosRenyi n p =
            ((n : ℝ) - 1) * p * (1 - p) ^ (n - 2) +
              ((n : ℝ) - 1) * ((n : ℝ) - 2) * p ^ 2 * (1 - p) ^ (2 * n - 5))

/-- Theorem 3.17 (unlabeled theorem, `SteinIntro.tex:1413-1420`, nested inside Example 3.9
`\label{ex72}` at `SteinIntro.tex:1354`): if $X_n$ is the number of isolated vertices in an
Erdős–Rényi graph $G(n, p_n)$ ($0 \le p_n \le 1$), $W_n = (X_n - \mu_n)/\sigma_n$, and
$\lim_{n \to \infty} n^\alpha p_n = c \in (0, \infty)$ for some $1 \le \alpha < 2$, then
there exists a constant $C$ such that $d_{\mathrm{W}}(\mathcal{L}(W_n), \mathcal{N}(0, 1))
\le C / \sigma_n$ for all sufficiently large $n$ (`∀ᶠ n in Filter.atTop`, the asymptotic
reading of the limit hypothesis). -/
def Thm3_17 : Prop :=
  ∀ {p : ℕ → ℝ} {α c : ℝ},
    (∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1) →
    1 ≤ α →
    α < 2 →
    0 < c →
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ α * p n) Filter.atTop (nhds c) →
    ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      let X : SimpleGraph (Fin n) → ℝ :=
        fun G ↦ ∑ i : Fin n, {H : SimpleGraph (Fin n) | H.IsIsolated i}.indicator 1 G
      let μ : ℝ := ∫ G, X G ∂erdosRenyi n (p n)
      let σ : ℝ := Real.sqrt (ProbabilityTheory.variance X (erdosRenyi n (p n)))
      let W : SimpleGraph (Fin n) → ℝ := fun G ↦ (X G - μ) / σ
      wassersteinDist ((erdosRenyi n (p n)).map W) stdNormalLaw ≤ ENNReal.ofReal (C / σ)

/-- Section 3.5 fixed-point characterization (unlabeled prose, `SteinIntro.tex:1450-1451`): a
real-valued random variable $W$ satisfies `IsZeroBias P W P W` ($W$ has the zero-bias
distribution with respect to itself) if and only if the law of $W$ is a centered normal
distribution $\mathcal{N}(0, v)$ (`normalLaw 0 v`, including the degenerate case $v = 0$,
$\mathcal{N}(0, 0) = \delta_0$). -/
def Sec3_5_zeroBias_fixedPoint : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ},
    AEMeasurable W P →
    (IsZeroBias P W P W ↔ ∃ v : NNReal, P.map W = normalLaw 0 v)

/-- Theorem 3.18 (`\label{thm81}`, `SteinIntro.tex:1454-1461`): if $W$ has mean zero and
variance one, $W^z$ is defined on the same probability space and has the zero-bias
distribution with respect to $W$, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le 2\,\mathbb{E}|W^z - W|$, with the
right-hand expectation in `ℝ≥0∞` (`lintegral`) per the junk-zero rule (`D1`, since
$\mathbb{E}|W^z| = \frac{1}{2}\mathbb{E}|W|^3$ may be $+\infty$ under finite second moment
alone). -/
def Thm3_18 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ},
    ProbabilityTheory.variance W P = 1 →
    IsZeroBias P W P Wz →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      2 * ∫⁻ ω, ENNReal.ofReal |Wz ω - W ω| ∂P

/-- Proposition 3.19, corrected (unlabeled proposition with items `\label{i81}`, `\label{i82}`
and eqs. `(3.31)`–`(3.32)` `\label{81}`–`\label{82}`, `SteinIntro.tex:1471-1485`;
`ISSUE-3.10` and `ISSUE-3.19` in `docs/SOURCE-ISSUES.md`, ruling `D9`): for a mean-zero
$L^2$ random variable $W$ with strictly positive variance $\sigma^2 =
\operatorname{Var}(W) > 0$,
(1) `zeroBiasDensity P W` satisfies the equivalent left-tail formula $p^z(w) =
    -\sigma^{-2}\mathbb{E}[W\mathbf{1}_{W \le w}] \ge 0$,
(2) every zero-bias random variable $W^z$ has law `volume.withDensity (ENNReal.ofReal ∘ p^z)`
    (uniqueness + Lebesgue absolute continuity), and
(3) `volume.withDensity (ENNReal.ofReal ∘ p^z)` is a probability measure whose identity map has
    the zero-bias distribution with respect to $W$ (existence).

Difference from printed result (`ISSUE-3.10`, `ISSUE-3.19`): adds $\sigma^2 =
\operatorname{Var}(W) > 0$ (at $\sigma^2 = 0$, `(3.32)` divides by zero and uniqueness in
`(3.31)` fails) and uses the dual-integrability zero-bias predicate `IsZeroBias` (requiring
$\mathbb{E}|f'(W^z)| < \infty$ as well as $\mathbb{E}|W f(W)| < \infty$, since under the printed
test class no zero-bias law exists when $\mathbb{E}|W|^3 = \infty$). -/
def Prop3_19_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ},
    MemLp W 2 P →
    ∫ ω, W ω ∂P = 0 →
    0 < ProbabilityTheory.variance W P →
    (∀ w : ℝ,
        zeroBiasDensity P W w =
          -(ProbabilityTheory.variance W P)⁻¹ *
            ∫ ω, W ω * (Set.Iic w).indicator 1 (W ω) ∂P ∧
          0 ≤ zeroBiasDensity P W w) ∧
      (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {Wz : Ω' → ℝ},
          IsZeroBias P W P' Wz →
          P'.map Wz =
            volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))) ∧
      (let ν : Measure ℝ :=
          volume.withDensity (fun w ↦ ENNReal.ofReal (zeroBiasDensity P W w))
       IsProbabilityMeasure ν ∧ IsZeroBias P W ν id)

/-- Section 3.5 distributional uniqueness from derivatives of compactly supported $C^1$
functions (unlabeled prose, `SteinIntro.tex:1512-1513`, inside the proof of Proposition
3.19): if two real-valued random variables $X$ and $Y$ satisfy $\mathbb{E}[f'(X)] =
\mathbb{E}[f'(Y)]$ for every continuously differentiable function $f : \mathbb{R} \to
\mathbb{R}$ with compact support, then $X \stackrel{d}{=} Y$
(`ProbabilityTheory.IdentDistrib X Y P P'`). -/
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

/-- Proposition 3.20, existence reading (unlabeled, `SteinIntro.tex:1519-1521`; `ISSUE-3.20` in
`docs/SOURCE-ISSUES.md`): if $W$ has mean zero and finite variance and $W^z$ has the
zero-bias distribution of $W$, then for every $a \in \mathbb{R}$ (with no positivity
requirement on $\operatorname{Var}(W)$ or $a$), $a W^z$ has the zero-bias distribution of $a
W$. (For distributional uniqueness $(a W)^z \stackrel{d}{=} a W^z$, see
`Prop3_20_restricted` and `ISSUE-3.20`.) -/
def Prop3_20 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    {W : Ω → ℝ} {Wz : Ω' → ℝ} (a : ℝ),
    IsZeroBias P W P' Wz →
    IsZeroBias P (fun ω ↦ a * W ω) P' (fun ω' ↦ a * Wz ω')

/-- Proposition 3.20, restricted to $\operatorname{Var}(W) > 0$ and $a \ne 0$ (unlabeled,
`SteinIntro.tex:1519-1521`, law-identity reading; `ISSUE-3.20` and `ISSUE-3.19` in
`docs/SOURCE-ISSUES.md`): if $W$ has mean zero and $0 < \operatorname{Var}(W) < \infty$,
$W^z$ has the zero-bias distribution of $W$, and $a \ne 0$, then $a W^z$ has the zero-bias
distribution of $a W$ and every zero-bias realization $Y$ of $a W$ satisfies $(a W)^z
\stackrel{d}{=} a W^z$.

Difference from printed result (`ISSUE-3.20`): adds $\operatorname{Var}(W) > 0$ and $a \ne 0$ so
$\operatorname{Var}(a W) = a^2 \operatorname{Var}(W) > 0$; at $a = 0$ or $\operatorname{Var}(W)
= 0$, distributional uniqueness across arbitrary zero-bias realizations fails
(`not_Prop3_20_printed`; the existence reading holds unconditionally in `Prop3_20`). -/
def Prop3_20_restricted : Prop :=
  ∀ {Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    {W : Ω → ℝ} {Wz : Ω' → ℝ} {Y : Ω'' → ℝ} {a : ℝ},
    0 < ProbabilityTheory.variance W P →
    a ≠ 0 →
    IsZeroBias P W P' Wz →
    IsZeroBias P (fun ω ↦ a * W ω) P' (fun ω' ↦ a * Wz ω') ∧
      (IsZeroBias P (fun ω ↦ a * W ω) P'' Y →
        P''.map Y = P'.map (fun ω' ↦ a * Wz ω'))

/-- Section 3.5.1 zero-bias construction from a Stein pair (unlabeled prose,
`SteinIntro.tex:1527-1528`, `%XXXX Exercise 3`, citing Goldstein–Reinert 1997
`\cite{gore97}` Lemma 2.1, proved from scratch; `ISSUE-3.19` in `docs/SOURCE-ISSUES.md`): if
$(W, W')$ is an $a$-Stein pair in $L^2(P)$ with $\sigma^2 = \mathrm{Var}(W) > 0$, then:
(1) the square-increment-biased measure $dQ = \frac{(W' - W)^2}{2 a \sigma^2}\,dP$ is a
    probability measure on $\Omega$, and on $Q \otimes \mathrm{Unif}(0, 1)$ the interpolation
    $(\omega, u) \mapsto u W(\omega) + (1 - u) W'(\omega)$ has the zero-bias distribution of
    $W$;
(2) for any probability space $(\Omega', P')$ carrying $(W^\dagger, W'^\dagger)$ with joint law
    $Q.\mathrm{map}(W, W')$ and an independent $U \sim \mathrm{Unif}(0, 1)$, $W^z = U W^\dagger
    + (1 - U) W'^\dagger$ satisfies `IsZeroBias P W P' Wz`. (Reading notes:
(1) Ross gives only the pointer to `\cite{gore97}`, so this entry states Goldstein–Reinert's
    canonical square-increment-biased interpolation explicitly; (2) `MemLp W 2 P` supplies
    finite second moment and `0 < variance W P` guards the $2 a \sigma^2$ denominator,
    `ISSUE-3.19`.) -/
def Sec3_5_1_zeroBias_of_steinPair : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} {W W' : Ω → ℝ},
    IsSteinPair P a W W' →
    MemLp W 2 P →
    0 < ProbabilityTheory.variance W P →
    let Q : Measure Ω :=
      P.withDensity fun ω ↦
        ENNReal.ofReal ((W' ω - W ω) ^ 2 / (2 * a * ProbabilityTheory.variance W P))
    (IsProbabilityMeasure Q ∧
      IsZeroBias P W (Q.prod (volume.restrict (Set.Ioo (0 : ℝ) 1)))
        (fun p ↦ p.2 * W p.1 + (1 - p.2) * W' p.1)) ∧
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      {Wd W'd U : Ω' → ℝ},
      AEMeasurable Wd P' →
      AEMeasurable W'd P' →
      AEMeasurable U P' →
      P'.map (fun ω' ↦ (Wd ω', W'd ω')) = Q.map (fun ω ↦ (W ω, W' ω)) →
      MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P' →
      ProbabilityTheory.IndepFun U (fun ω' ↦ (Wd ω', W'd ω')) P' →
      IsZeroBias P W P' (fun ω' ↦ U ω' * Wd ω' + (1 - U ω') * W'd ω')

/-- Proposition 3.21 (`\label{prop81}`, `SteinIntro.tex:1530-1551`; `ISSUE-TYPO-3.21` in
`docs/SOURCE-ISSUES.md`): if $X_1, \dots, X_n$ are independent mean-zero $L^2$ random
variables with $\sum_{i=1}^n \operatorname{Var}(X_i) = 1$, each $X_i^z$ has the zero-bias
distribution of $X_i$ and is independent of $(X_j)_{j \ne i}$, and $I$ is an index with
$\mathbb{P}(I = i) = \operatorname{Var}(X_i)$ independent of $((X_i)_i, (X_i^z)_i)$, then
$W^z = \sum_{j \ne I} X_j + X_I^z$ has the zero-bias distribution of $W = \sum_{i=1}^n X_i$.
(Reading note, parallel to `Prop3_14` / `Cor3_15`: Item 1 at `SteinIntro.tex:1533-1534` also
mentions independence of $X_i^z$ from $(X_j^z)_{j \ne i}$, which the proof never uses;
assuming only $X_i^z \perp (X_j)_{j \ne i}$ assumes strictly less and implies the printed
proposition.) -/
def Prop3_21 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} {X Xz : Fin n → Ω → ℝ} {I : Ω → Fin n},
    (∀ i : Fin n, Measurable (X i)) →
    (∀ i : Fin n, Measurable (Xz i)) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, MemLp (X i) 2 P) →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∑ i : Fin n, ProbabilityTheory.variance (X i) P) = 1 →
    (∀ i : Fin n, IsZeroBias P (X i) P (Xz i)) →
    (∀ i : Fin n,
      ProbabilityTheory.IndepFun (Xz i) (fun ω (j : {j : Fin n // j ≠ i}) ↦ X j ω) P) →
    Measurable I →
    (∀ i : Fin n, P.real (I ⁻¹' {i}) = ProbabilityTheory.variance (X i) P) →
    ProbabilityTheory.IndepFun I (fun ω ↦ (fun i ↦ X i ω, fun i ↦ Xz i ω)) P →
    IsZeroBias P (fun ω ↦ ∑ i : Fin n, X i ω) P
      (fun ω ↦ (∑ j ∈ Finset.univ.erase (I ω), X j ω) + Xz (I ω) ω)

/-- Section 3.5.2 Lindeberg sufficiency (unlabeled prose and eq. `(3.34)` `\label{85}`,
`SteinIntro.tex:1558-1564`; `ISSUE-3.22` in `docs/SOURCE-ISSUES.md`): for a triangular array
$(X_{i,n})$ of row-wise independent mean-zero $L^2$ random variables with
$\operatorname{Var}(\sum_i X_{i,n}) = 1$, the Lindeberg condition `(3.34)` implies $W_n =
\sum_i X_{i,n} \xrightarrow{d} \mathcal{N}(0, 1)$ in `MeasureTheory.ProbabilityMeasure ℝ`
(without assuming pre-existing zero-bias or random-index variables on `Ω`). -/
def Sec3_5_2_lindeberg_sufficient : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : (n : ℕ) → Fin (n + 1) → Ω → ℝ},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ ε : ℝ, 0 < ε →
      Filter.Tendsto
        (fun n : ℕ ↦
          ∑ i : Fin (n + 1),
            ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
        Filter.atTop (nhds 0)) →
    Filter.Tendsto
      (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      Filter.atTop
      (nhds stdNormalLaw.toProbabilityMeasure)

/-- Section 3.5.2 prose counterexample, corrected (unlabeled prose, `SteinIntro.tex:1565-1566`;
`ISSUE-3.5.2-PROSE` in `docs/SOURCE-ISSUES.md`): taking $X_{1, n} \sim \mathcal{N}(0, 1)$
and $X_{i, n} = 0$ for $i > 1$ gives an independent centered unit-variance triangular array
whose row sums $W_n$ converge weakly to $\mathcal{N}(0, 1)$ yet violate the Lindeberg
condition `(3.34)` (`\ref{85}`), showing that `(3.34)` is not *necessary* for the CLT.

Difference from printed result (`ISSUE-3.5.2-PROSE`): replaces the printed slip `"not
sufficient"` at `SteinIntro.tex:1566` by *not necessary* (Lindeberg's condition `(3.34)` was
just stated to be sufficient at `SteinIntro.tex:1560-1564`, and the single-Gaussian row example
refutes necessity). -/
def Sec3_5_2_lindeberg_not_necessary_corrected : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (X : (n : ℕ) → Fin (n + 1) → Ω → ℝ),
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) ∧
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) ∧
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) ∧
    Filter.Tendsto
      (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      Filter.atTop
      (nhds stdNormalLaw.toProbabilityMeasure) ∧
    ¬ (∀ ε : ℝ, 0 < ε →
        Filter.Tendsto
          (fun n : ℕ ↦
            ∑ i : Fin (n + 1),
              ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
          Filter.atTop (nhds 0))

/-- Theorem 3.22 (`\label{thm82}`, eqs. `(3.34)`–`(3.35)` `\label{85}`–`\label{86}`,
`SteinIntro.tex:1568-1575`, `SteinIntro.tex:1562-1564`; `ISSUE-3.22` in
`docs/SOURCE-ISSUES.md`): for a triangular array $(X_{i, n})$ of row-wise independent
mean-zero $L^2$ random variables with $\operatorname{Var}(\sum_i X_{i, n}) = 1$, random
index $I_n$ with $\mathbb{P}(I_n = i) = \sigma_{i, n}^2$ independent of $((X_{i, n})_i,
(X_{i, n}^z)_i)$, and zero-bias variables $X_{i, n}^z$, the Lindeberg condition `(3.34)`
holds if and only if $X_{I_n, n}^z \stackrel{p}{\to} 0$ as $n \to \infty$. -/
def Thm3_22 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Xz n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ (n : ℕ) (i : Fin (n + 1)), IsZeroBias P (X n i) P (Xz n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      ProbabilityTheory.IndepFun (Xz n i)
        (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) P) →
    (∀ n : ℕ, Measurable (I n)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P) →
    (∀ n : ℕ,
      ProbabilityTheory.IndepFun (I n)
        (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P) →
    ((∀ ε : ℝ, 0 < ε →
        Filter.Tendsto
          (fun n : ℕ ↦
            ∑ i : Fin (n + 1),
              ∫ ω, (X n i ω) ^ 2 * {x : ℝ | ε < |x|}.indicator 1 (X n i ω) ∂P)
          Filter.atTop (nhds 0)) ↔
      MeasureTheory.TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) Filter.atTop 0)

/-- Section 3.5.2 prose implication (unlabeled prose, `SteinIntro.tex:1584-1586`,
`SteinIntro.tex:1625-1646`): under the hypotheses of Theorem 3.22 (`\ref{thm82}`), $X_{I_n,
n}^z \stackrel{p}{\to} 0$ implies $\max_i \sigma_{i, n}^2 \to 0$ and $X_{I_n, n}
\stackrel{p}{\to} 0$. -/
def Sec3_5_2_zeroBias_imp_tendstoInMeasure : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Xz n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ (n : ℕ) (i : Fin (n + 1)), IsZeroBias P (X n i) P (Xz n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      ProbabilityTheory.IndepFun (Xz n i)
        (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) P) →
    (∀ n : ℕ, Measurable (I n)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P) →
    (∀ n : ℕ,
      ProbabilityTheory.IndepFun (I n)
        (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P) →
    MeasureTheory.TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) Filter.atTop 0 →
    Filter.Tendsto
        (fun n : ℕ ↦ Finset.univ.sup' Finset.univ_nonempty
          fun i : Fin (n + 1) ↦ ProbabilityTheory.variance (X n i) P)
        Filter.atTop (nhds 0) ∧
      MeasureTheory.TendstoInMeasure P (fun n ω ↦ X n (I n ω) ω) Filter.atTop 0

/-- Theorem 3.23 (`\label{thm83}`, `SteinIntro.tex:1578-1581`; `ISSUE-3.22` in
`docs/SOURCE-ISSUES.md`): in the setting of Theorem 3.22 (`\ref{thm82}`), if $X_{I_n, n}^z
\to 0$ in probability as $n \to \infty$, then $W_n = \sum_i X_{i,n}$ satisfies a central
limit theorem, i.e., the laws of $W_n$ converge weakly to `stdNormalLaw` in
`MeasureTheory.ProbabilityMeasure ℝ`. -/
def Thm3_23 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Xz : (n : ℕ) → Fin (n + 1) → Ω → ℝ} {I : (n : ℕ) → Ω → Fin (n + 1)},
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Xz n i)) →
    (∀ n : ℕ, ProbabilityTheory.iIndepFun (X n) P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), MemLp (X n i) 2 P) →
    (∀ (n : ℕ) (i : Fin (n + 1)), ∫ ω, X n i ω ∂P = 0) →
    (∀ n : ℕ, ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin (n + 1), X n i ω) P = 1) →
    (∀ (n : ℕ) (i : Fin (n + 1)), IsZeroBias P (X n i) P (Xz n i)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      ProbabilityTheory.IndepFun (Xz n i)
        (fun ω (j : {j : Fin (n + 1) // j ≠ i}) ↦ X n j ω) P) →
    (∀ n : ℕ, Measurable (I n)) →
    (∀ (n : ℕ) (i : Fin (n + 1)),
      P.real (I n ⁻¹' {i}) = ProbabilityTheory.variance (X n i) P) →
    (∀ n : ℕ,
      ProbabilityTheory.IndepFun (I n)
        (fun ω ↦ (fun i ↦ X n i ω, fun i ↦ Xz n i ω)) P) →
    MeasureTheory.TendstoInMeasure P (fun n ω ↦ Xz n (I n ω) ω) Filter.atTop 0 →
    Filter.Tendsto
      (fun n : ℕ ↦ (P.map (fun ω ↦ ∑ i : Fin (n + 1), X n i ω)).toProbabilityMeasure)
      Filter.atTop
      (nhds stdNormalLaw.toProbabilityMeasure)

/-- Section 3.6 motivating binomial rate claim (unlabeled prose, `SteinIntro.tex:1655-1657`):
for fixed $0 < p < 1$, if $W$ is a standardized $\mathrm{Bin}(n, p)$ random variable ($n \ge
1$, represented as $((\sum_{i=1}^n X_i) - n p) / \sqrt{n p (1 - p)}$ for independent $\{0,
1\}$-valued $X_i$ with $\mathbb{P}(X_i = 1) = p$) and $Z \sim \mathcal{N}(0, 1)$, then both
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z))$ and $d_{\mathrm{W}}(\mathcal{L}(W),
\mathcal{L}(Z))$ have two-sided order $n^{-1/2}$ for all $n \ge 1$. -/
def Sec3_6_binomial_order : Prop :=
  ∀ {p : ℝ},
    0 < p →
    p < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (P : Measure Ω) [IsProbabilityMeasure P]
        (P' : Measure Ω') [IsProbabilityMeasure P']
        {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ},
        1 ≤ n →
        (∀ i : Fin n, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X P →
        (∀ i : Fin n, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) →
        (∀ i : Fin n, P.real (X i ⁻¹' {1}) = p) →
        AEMeasurable Z P' →
        P'.map Z = stdNormalLaw →
        let W : Ω → ℝ :=
          fun ω ↦ ((∑ i : Fin n, X i ω) - (n : ℝ) * p) / Real.sqrt ((n : ℝ) * p * (1 - p))
        (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤ kolmogorovDist (P.map W) (P'.map Z) ∧
          kolmogorovDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ) / 2))) ∧
        (ENNReal.ofReal (c * (n : ℝ) ^ (-(1 : ℝ) / 2)) ≤ wassersteinDist (P.map W) (P'.map Z) ∧
          wassersteinDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(1 : ℝ) / 2)))

/-- Theorem 3.24, corrected (`\label{thm91}`, eq. `(3.38)` `\label{91}`,
`SteinIntro.tex:1666-1675`; `ISSUE-2.2` in `docs/SOURCE-ISSUES.md`, `D4`): if $W$ is a
real-valued random variable with finite mean and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) = \sup_{x \in \mathbb{R}} |\mathbb{E}[D_-
f_x(W) - W f_x(W)]|$, where $f_x = \mathrm{normalSteinSolKolm}\,x$ solves the
left-derivative normal Stein equation.

Difference from printed result (`ISSUE-2.2`): replaces the printed two-sided derivative
$f_x'(W)$ by the left derivative $D_- f_x(W)$ (`normalSteinOpLeft`), because $f_x$ has a unit
derivative jump at $w = x$ and the two-sided `deriv` transcription fails when $W$ has atoms
(`Cor2_3_twoSided_counterexample`). Per ruling `D4`, the printed finite-mean hypothesis
(`Integrable W P`) is retained. -/
def Thm3_24_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    Integrable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) =
      ⨆ x : ℝ, ENNReal.ofReal |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P|

/-- Lemma 3.25, corrected (`\label{lem91}`, `SteinIntro.tex:1677-1686`; `ISSUE-2.2` and
`ISSUE-3.25` in `docs/SOURCE-ISSUES.md`, `D4`): for every $x \in \mathbb{R}$, the Kolmogorov
Stein solution $f_x = \mathrm{normalSteinSolKolm}\,x$ satisfies $|f_x(w)| \le \sqrt{\pi /
2}$, $|D_- f_x(w)| \le 2$, and $|(w + u) f_x(w + u) - (w + v) f_x(w + v)| \le (|w| +
\sqrt{2\pi}/4)(|u| + |v|)$ for all $u, v, w \in \mathbb{R}$.

Difference from printed result (`ISSUE-2.2`): states the derivative bound $\|f_x'\| \le 2$ using
the left derivative $D_- f_x(w)$ (`derivWithin _ (Set.Iic w) w`) rather than a two-sided
derivative at the jump point $w = x$ (the sharp bound $|D_- f_x(w)| \le 1$ also holds and is
used in Theorem 3.28, `ISSUE-3.25`). -/
def Lem3_25_corrected : Prop :=
  ∀ x : ℝ,
    (∀ w : ℝ, |normalSteinSolKolm x w| ≤ Real.sqrt (Real.pi / 2)) ∧
    (∀ w : ℝ, |derivWithin (normalSteinSolKolm x) (Set.Iic w) w| ≤ 2) ∧
    (∀ u v w : ℝ,
      |(w + u) * normalSteinSolKolm x (w + u) - (w + v) * normalSteinSolKolm x (w + v)| ≤
        (|w| + Real.sqrt (2 * Real.pi) / 4) * (|u| + |v|))

/-- Corollary 3.26 (`\label{cor91}`, `SteinIntro.tex:1688-1694`): if $\mathcal{F}$ is the class
`normalKolmogorovClass` of differentiable functions satisfying the bounds of Lemma 3.25, $W$
is a real-valued random variable with finite mean, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \sup_{f \in \mathcal{F}}
|\mathbb{E}[f'(W) - W f(W)]|$.

Reading note: $\mathcal{F}$ (`normalKolmogorovClass`) is read as the *differentiable* functions
satisfying Lemma 3.25's bounds; this excludes $f_x$ itself and gives a smaller supremum, so the
entry implies every weaker-regularity reading (proved by smoothing $\mathbb{I}[\cdot \le x]$
with a piecewise-linear ramp). -/
def Cor3_26 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    Integrable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ normalKolmogorovClass, ENNReal.ofReal |∫ ω, normalSteinOp f (W ω) ∂P|

/-- Theorem 3.27 (unlabeled, `SteinIntro.tex:1697-1704`; `ISSUE-3.10` in
`docs/SOURCE-ISSUES.md`, `D9`): if $W$ has mean zero and variance one, $W^z$ has the
zero-bias distribution of $W$ on the same probability space with $|W^z - W| \le \delta$
almost surely, and $Z \sim \mathcal{N}(0, 1)$, then $d_{\mathrm{K}}(\mathcal{L}(W),
\mathcal{L}(Z)) \le (1 + 1/\sqrt{2\pi} + \sqrt{2\pi}/4)\,\delta$. -/
def Thm3_27 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W Wz : Ω → ℝ} {Z : Ω' → ℝ} {δ : ℝ},
    ProbabilityTheory.variance W P = 1 →
    IsZeroBias P W P Wz →
    (∀ᵐ ω ∂P, |Wz ω - W ω| ≤ δ) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * δ)

/-- Section 3.6.1 zero-bias boundedness inheritance, restricted to positive variance (unlabeled
prose, `SteinIntro.tex:1741-1742`; `ISSUE-3.19` and `ISSUE-TYPO-3.27` in
`docs/SOURCE-ISSUES.md`): if $\operatorname{Var}(W) > 0$, $|W| \le M$ almost surely, and
$W^z$ has the zero-bias distribution of $W$, then $|W^z| \le M$ almost surely.

Difference from printed result (`ISSUE-3.19`): adds $\operatorname{Var}(W) > 0$ so that *every*
zero-bias version $W^z$ inherits $|W^z| \le M$ a.s.; at $\operatorname{Var}(W) = 0$, $W \equiv
0$ admits unbounded zero-bias versions such as $\mathcal{N}(0, 1)$
(`zero_stdNormalLaw_isZeroBias_unbounded`; the existence reading without
$\operatorname{Var}(W) > 0$ is proved in `Sec3_6_zeroBias_bdd_exists`). -/
def Sec3_6_zeroBias_bdd_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Wz : Ω' → ℝ} {M : ℝ},
    0 < ProbabilityTheory.variance W P →
    IsZeroBias P W P' Wz →
    (∀ᵐ ω ∂P, |W ω| ≤ M) →
    ∀ᵐ ω' ∂P', |Wz ω'| ≤ M

/-- Section 3.6.1 zero-bias boundedness inheritance, existence reading (unlabeled prose,
`SteinIntro.tex:1741-1742`; `ISSUE-3.19` in `docs/SOURCE-ISSUES.md`): without assuming
$\operatorname{Var}(W) > 0$, if $W \in L^2(P)$ has mean zero and $|W| \le M$ almost surely,
then there exists a zero-bias law $\nu$ of $W$ supported on $[-M, M]$ (taking $\nu =
\delta_0$ when $\operatorname{Var}(W) = 0$). -/
def Sec3_6_zeroBias_bdd_exists : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} {M : ℝ},
    MemLp W 2 P →
    ∫ ω, W ω ∂P = 0 →
    (∀ᵐ ω ∂P, |W ω| ≤ M) →
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ IsZeroBias P W ν id ∧ ∀ᵐ x : ℝ ∂ν, |x| ≤ M

/-- Section 3.6.1 bounded independent-sum Kolmogorov bound (unlabeled prose,
`SteinIntro.tex:1741-1743`, `%%XXXX Exercise 3`; `ISSUE-TYPO-3.27` in
`docs/SOURCE-ISSUES.md`): if $X_1, \dots, X_n$ are independent mean-zero random variables
satisfying $|X_i| \le C$ almost surely with $\sigma^2 = \mathrm{Var}(\sum_{i=1}^n X_i) > 0$,
$W = (\sum_{i=1}^n X_i) / \sigma$, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le (1 + 1/\sqrt{2\pi} + \sqrt{2\pi}/4)\,(2
C / \sigma)$. (Reading notes: (1) centering (`∫ X_i = 0`) comes from Proposition 3.21's
zero-bias sum recipe (`SteinIntro.tex:1530-1531`); (2) Ross prints no explicit formula and
leaves the application as an exercise, so this bound is the explicit solution combining
Proposition 3.21, `Sec3_6_zeroBias_bdd_exists`, and Theorem 3.27 (`δ = 2 C / σ`);
(3) $\sigma^2 > 0$ is typing for $W = S / \sigma$.) -/
def Sec3_6_1_indepSum_kolmogorov : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ} {C : ℝ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, |X i ω| ≤ C) →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (2 * C / σ))

/-- Section 3.6.1 Kolmogorov bound in Hoeffding's combinatorial CLT (unlabeled prose,
`SteinIntro.tex:1741-1743`, `%%XXXX Exercise 3`, referencing Example 7.5 at
`SteinIntro.tex:3597-3611`; `ISSUE-TYPO-3.27` in `docs/SOURCE-ISSUES.md`): for a real array
$(a_{ij})_{i, j \in \mathrm{Fin}\,n}$ with $|a_{ij}| \le C$, a uniform random permutation
$\pi$ of `Fin n` with $\sigma^2 = \mathrm{Var}(\sum_{i=1}^n a_{i, \pi(i)}) > 0$, $\mu =
\frac{1}{n}\sum_{i, j} a_{ij}$, $W = (\sum_{i=1}^n a_{i, \pi(i)} - \mu) / \sigma$, and $Z
\sim \mathcal{N}(0, 1)$, $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le (1 +
1/\sqrt{2\pi} + \sqrt{2\pi}/4)\,(8 C / \sigma)$. (Reading notes: (1) `"under some
boundedness assumption"` (`SteinIntro.tex:1743`) is read as `|a i j| ≤ C`; (2) Ross prints
no explicit formula and leaves the derivation as an exercise, so the right-hand side
combines the two-swap square-increment-biased zero-bias coupling (`|W^z - W| ≤ 8 C / σ`)
with Theorem 3.27;
(3) $\sigma^2 > 0$ is typing for $W = (S - \mu)/\sigma$ and forces $n \ge 2$.) -/
def Sec3_6_1_combinatorial_kolmogorov : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {a : Fin n → Fin n → ℝ} {π : Ω → Equiv.Perm (Fin n)} {Z : Ω' → ℝ} {C : ℝ},
    (∀ i j : Fin n, |a i j| ≤ C) →
    AEMeasurable π P →
    P.map π = (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, a i (π ω i)) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, a i (π ω i)
    let μ : ℝ := (1 / (n : ℝ)) * ∑ i : Fin n, ∑ j : Fin n, a i j
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ (S ω - μ) / σ
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        ((1 + 1 / Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) / 4) * (8 * C / σ))

/-- Theorem 3.28 (`\label{thm92}`, `SteinIntro.tex:1750-1755`; `ISSUE-3.25` in
`docs/SOURCE-ISSUES.md`, `D7`): if $(W, W')$ is an $a$-Stein pair with
$\operatorname{Var}(W) = 1$ and $|W' - W| \le \delta$ almost surely, and $Z \sim
\mathcal{N}(0, 1)$, then $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\operatorname{Var}(\mathbb{E}[(W' - W)^2 \mid W])}}{2a} + \frac{\delta^3}{2a} +
\frac{3\delta}{2}$.

Proof note (`ISSUE-3.25`): obtaining denominator $2a$ in the first term at
`SteinIntro.tex:1766-1769` uses the sharp bound $|D_- f_x(w)| \le 1$ (CGS 2011 Lemma 2.3) rather
than the looser bound $\|f_x'\| \le 2$ printed in Lemma 3.25; the theorem holds as printed. -/
def Thm3_28 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {a δ : ℝ} {W W' : Ω → ℝ} {Z : Ω' → ℝ},
    IsSteinPair P a W W' →
    ProbabilityTheory.variance W P = 1 →
    (∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ProbabilityTheory.evariance
          (P[fun ω ↦ (W' ω - W ω) ^ 2 | MeasurableSpace.comap W inferInstance]) P ^
        (1 / 2 : ℝ) / ENNReal.ofReal (2 * a) +
      ENNReal.ofReal (δ ^ 3 / (2 * a) + 3 * δ / 2)

/-- Lemma 3.29 (`\label{lem92}`, `SteinIntro.tex:1793-1798`; `D7`): if $(W, W')$ is an $a$-Stein
pair with $\operatorname{Var}(W) = 1$ and $|W' - W| \le \delta$ almost surely, then for all
$x \in \mathbb{R}$, $\mathbb{E}[(W' - W)^2 \mathbb{I}[x < W \le x + \delta]] \le 3 \delta
a$. -/
def Lem3_29 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a δ : ℝ} {W W' : Ω → ℝ} (x : ℝ),
    IsSteinPair P a W W' →
    ProbabilityTheory.variance W P = 1 →
    (∀ᵐ ω ∂P, |W' ω - W ω| ≤ δ) →
    ∫ ω, (W' ω - W ω) ^ 2 * (Set.Ioc x (x + δ)).indicator 1 (W ω) ∂P ≤ 3 * δ * a

/-- Section 3.6.2 bounded independent-sum Kolmogorov bound via exchangeable pairs (unlabeled
prose, `SteinIntro.tex:1810-1812`, applying Theorem 3.28 (`\ref{thm92}`) with Example 3.6's
Stein pair): if $X_1, \dots, X_n$ are independent mean-zero random variables satisfying
$|X_i| \le C$ almost surely with $\sigma^2 = \mathrm{Var}(\sum_{i=1}^n X_i) > 0$, $W =
(\sum_{i=1}^n X_i) / \sigma$, and $Z \sim \mathcal{N}(0, 1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le \frac{\sqrt{\sum_{i=1}^n
\mathrm{Var}(X_i^2)}}{2 \sigma^2} + \frac{4 n C^3}{\sigma^3} + \frac{3 C}{\sigma}$. (Reading
notes: (1) centering (`∫ X_i = 0`) and the $(1/n)$-Stein pair $W' = W - X_I/\sigma +
X_I'/\sigma$ follow Example 3.6 (`SteinIntro.tex:1053-1059`); (2) Ross prints no explicit
formula at `SteinIntro.tex:1810`, so this bound is obtained from Theorem 3.28 (`a = 1/n`, `δ
= 2 C / σ`) and Remark 3.4 (`Rem3_4`); (3) $\sigma^2 > 0$ is typing for $W = S / \sigma$.) -/
def Sec3_6_2_indepSum_kolmogorov : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {n : ℕ} {X : Fin n → Ω → ℝ} {Z : Ω' → ℝ} {C : ℝ},
    (∀ i : Fin n, AEMeasurable (X i) P) →
    ProbabilityTheory.iIndepFun X P →
    (∀ i : Fin n, ∫ ω, X i ω ∂P = 0) →
    (∀ i : Fin n, ∀ᵐ ω ∂P, |X i ω| ≤ C) →
    0 < ProbabilityTheory.variance (fun ω ↦ ∑ i : Fin n, X i ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let S : Ω → ℝ := fun ω ↦ ∑ i : Fin n, X i ω
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (∑ i : Fin n, ProbabilityTheory.variance (fun ω ↦ X i ω ^ 2) P) /
            (2 * σ ^ 2) +
          4 * (n : ℝ) * C ^ 3 / σ ^ 3 +
          3 * C / σ)

/-- Section 3.6.2 anti-voter Kolmogorov bound (unlabeled prose, `SteinIntro.tex:1810-1812`,
applying Theorem 3.28 (`\ref{thm92}`) to the anti-voter model of Section 3.3.1): for any
stationary distribution of the anti-voter Markov chain on a finite $r$-regular simple graph
$G$ on $n = |V|$ vertices that is neither bipartite nor isomorphic to `cycleGraph |V|`, with
total spin $S = \sum_{v \in V} \mathrm{spin}(X_v)$, $\sigma = \sqrt{\mathrm{Var}(S)}$, $W =
S / \sigma$, $Q = \sum_{i \in V} \sum_{j \in N_i} \mathrm{spin}(X_i) \mathrm{spin}(X_j)$,
and $Z \sim \mathcal{N}(0, 1)$, $d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\frac{\sqrt{\mathrm{Var}(Q)}}{2 r \sigma^2} + \frac{2 n}{\sigma^3} + \frac{3}{\sigma}$.
(Reading notes: (1) hypotheses match Theorem 3.8 (`Thm3_8`), constructing the next Markov
step internally via `antiVoterStep G`; (2) follows from Theorem 3.28 (`a = 2/n`, `δ = 2/σ`)
and Remark 3.4 (`Rem3_4`), with Lemma 3.10 giving $\sigma^2 \le n$ and $\frac{2n}{\sigma^3}
+ \frac{3}{\sigma} \le \frac{5n}{\sigma^3}$; (3) $n \ge 4$, $r > 0$, and $\sigma > 0$ follow
from the hypotheses.) -/
def Sec3_6_2_antiVoter_kolmogorov : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → V → Bool} {Z : Ω' → ℝ},
    G.IsRegularOfDegree r →
    ¬ G.IsBipartite →
    IsEmpty (G ≃g SimpleGraph.cycleGraph (Fintype.card V)) →
    Measurable X →
    IsAntiVoterStationary G (P.map X) →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    let n : ℝ := Fintype.card V
    let S : Ω → ℝ := fun ω ↦ ∑ v : V, spin (X ω v)
    let σ : ℝ := Real.sqrt (ProbabilityTheory.variance S P)
    let W : Ω → ℝ := fun ω ↦ S ω / σ
    let Q : Ω → ℝ := fun ω ↦ ∑ i : V, ∑ j ∈ G.neighborFinset i, spin (X ω i) * spin (X ω j)
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ENNReal.ofReal
        (Real.sqrt (ProbabilityTheory.variance Q P) / (2 * (r : ℝ) * σ ^ 2) +
          2 * n / σ ^ 3 +
          3 / σ)

end SteinMethod
