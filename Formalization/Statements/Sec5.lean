/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.Branching

/-!
# Section 5 Statements: Exponential Approximation (`SteinIntro.tex:2712-3189`)

Self-contained proposition statements (`: Prop`) for Section 5 opening and Sections 5.1–5.3 of
Nathan Ross, *"Fundamentals of Stein's method"* (*Probability Surveys* 8, 2011, pp. 210–293;
`arXiv:1109.1880v1`). Imports `Formalization.Defs` and `Formalization.Defs.Branching` only.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SteinMethod

/-- Lemma 5.1(1) (`\label{lem171}`, `SteinIntro.tex:2726-2733`): if $Z \sim \mathrm{Exp}(1)$, then
$\mathcal{A}f(Z)$ is integrable and $\mathbb{E}[\mathcal{A}f(Z)] = 0$ for every locally absolutely
continuous function $f : \mathbb{R} \to \mathbb{R}$ (`D5`) satisfying
$\mathbb{E}|f'(Z)| < \infty$. -/
def Lem5_1_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} {f : ℝ → ℝ},
    AEMeasurable Z P →
    P.map Z = stdExpLaw →
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
    Integrable (fun ω ↦ deriv f (Z ω)) P →
    Integrable (fun ω ↦ expSteinOp f (Z ω)) P ∧ ∫ ω, expSteinOp f (Z ω) ∂P = 0

/-- Lemma 5.1(2) (`\label{lem171}`, `SteinIntro.tex:2734-2736`; `D5` literal): if $W \ge 0$ a.s. is
a real-valued random variable such that $\mathbb{E}[\mathcal{A}f(W)] = 0$ for every locally
absolutely continuous function $f : \mathbb{R} \to \mathbb{R}$ satisfying
$\mathbb{E}|f'(Z)| < \infty$ for $Z \sim \mathrm{Exp}(1)$, then $W \sim \mathrm{Exp}(1)$. -/
def Lem5_1_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ},
    AEMeasurable W P →
    0 ≤ᵐ[P] W →
    (∀ f : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
      Integrable (deriv f) stdExpLaw →
      ∫ ω, expSteinOp f (W ω) ∂P = 0) →
    P.map W = stdExpLaw

/-- Lemma 5.2, solution formula, boundary value, and uniqueness for continuous $h$
(`\label{lem172}`, eqs. `(5.1)`–`(5.2)` `\label{171}`–`\label{172}`,
`SteinIntro.tex:2740-2745, 2774-2779`): (i) for locally integrable $h : \mathbb{R} \to \mathbb{R}$
that is integrable under $\mathrm{Exp}(1)$, `expSteinSol h` satisfies $f_h(0) = 0$ and admits the
interval-integral representation $f_h(x) = e^x \int_0^x (h(t) - \mathbb{E}[h(Z)]) e^{-t}\,dt$ for
all $x \in \mathbb{R}$; (ii) if moreover $h$ is continuous, `expSteinSol h` solves
$f_h'(x) - f_h(x) = h(x) - \mathbb{E}[h(Z)]$ with a two-sided derivative everywhere on
$\mathbb{R}$ and is the unique differentiable solution satisfying $g(0) = 0$. -/
def Lem5_2_formula : Prop :=
  (∀ {h : ℝ → ℝ}, LocallyIntegrable h volume → Integrable h stdExpLaw →
    expSteinSol h 0 = 0 ∧
      ∀ x : ℝ, expSteinSol h x =
        Real.exp x * ∫ t in (0 : ℝ)..x, (h t - stdExpExpect h) * Real.exp (-t)) ∧
  (∀ {h : ℝ → ℝ}, Continuous h → Integrable h stdExpLaw →
    (∀ x : ℝ, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x) ∧
      ∀ g : ℝ → ℝ, g 0 = 0 →
        (∀ x : ℝ, HasDerivAt g (g x + h x - stdExpExpect h) x) →
        g = expSteinSol h)

/-- Lemma 5.2, pointwise ODE at continuity points (`\label{lem172}`, eq. `(5.1)` `\label{171}`,
`SteinIntro.tex:2740-2745, 2774-2779`; `ISSUE-5.2-ODE`): for locally integrable
$h : \mathbb{R} \to \mathbb{R}$ integrable under $\mathrm{Exp}(1)$, `expSteinSol h` satisfies
$f_h'(x) - f_h(x) = h(x) - \mathbb{E}[h(Z)]$ with a two-sided derivative at every continuity point
$x$ of $h$. -/
def Lem5_2_ode_contAt : Prop :=
  ∀ {h : ℝ → ℝ}, LocallyIntegrable h volume → Integrable h stdExpLaw →
    ∀ x : ℝ, ContinuousAt h x →
      HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x

/-- Lemma 5.2, local absolute continuity, a.e. ODE, and a.e. uniqueness (`\label{lem172}`,
eqs. `(5.1)`–`(5.2)` `\label{171}`–`\label{172}`, `SteinIntro_utf8.tex:2740-2745, 2774-2779`;
`ISSUE-5.2-ODE`, `M1`): for locally integrable $h : \mathbb{R} \to \mathbb{R}$ integrable under
$\mathrm{Exp}(1)$ — and in particular for every bounded measurable $h : \mathbb{R} \to \mathbb{R}$ —
`expSteinSol h` is locally absolutely continuous on $\mathbb{R}$, satisfies
$f_h'(x) - f_h(x) = h(x) - \mathbb{E}[h(Z)]$ with a two-sided derivative at Lebesgue-almost-every
$x \in \mathbb{R}$, and is the unique locally absolutely continuous $g : \mathbb{R} \to \mathbb{R}$
with $g(0) = 0$ satisfying $g'(x) - g(x) = h(x) - \mathbb{E}[h(Z)]$ almost everywhere. -/
def Lem5_2_ode_ae : Prop :=
  (∀ {h : ℝ → ℝ}, LocallyIntegrable h volume → Integrable h stdExpLaw →
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (expSteinSol h) a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x) ∧
      ∀ g : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b) → g 0 = 0 →
        (∀ᵐ x ∂volume, deriv g x - g x = h x - stdExpExpect h) →
        g = expSteinSol h) ∧
  (∀ {h : ℝ → ℝ} {M : ℝ}, Measurable h → (∀ x : ℝ, |h x| ≤ M) →
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval (expSteinSol h) a b) ∧
      (∀ᵐ x ∂volume, HasDerivAt (expSteinSol h) (expSteinSol h x + h x - stdExpExpect h) x) ∧
      ∀ g : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval g a b) → g 0 = 0 →
        (∀ᵐ x ∂volume, deriv g x - g x = h x - stdExpExpect h) →
        g = expSteinSol h)

/-- Lemma 5.2(1) (`\label{lem172}` item 1 `\label{i171}`, `SteinIntro.tex:2747-2750, 2781-2789`;
`D2`, `D5-3`): for measurable non-negative bounded $h : \mathbb{R} \to \mathbb{R}$ with
$0 \le h(t) \le M$ for all $t \in \mathbb{R}$, `expSteinSol h` is $2 M$-Lipschitz on $\mathbb{R}$,
and $|f_h(x)| \le M$, $|f_h'(x)| \le 2 M$, and $|D_- f_h(x)| \le 2 M$ for all $x \in \mathbb{R}$
(note Lean's `deriv` and `derivWithin` return `0` where the two-sided or left derivative does not
exist — e.g. jump points of $h$ for `deriv`, or measurable $h = \mathbf{1}_A$ with oscillating
Lebesgue density at $x$ for `derivWithin` — whereas `LipschitzWith` holds globally without
vacuity). -/
def Lem5_2_1 : Prop :=
  ∀ {h : ℝ → ℝ} {M : ℝ},
    Measurable h →
    (∀ t : ℝ, 0 ≤ h t) →
    (∀ t : ℝ, h t ≤ M) →
    LipschitzWith (Real.toNNReal (2 * M)) (expSteinSol h) ∧
      ∀ x : ℝ,
        |expSteinSol h x| ≤ M ∧
        |deriv (expSteinSol h) x| ≤ 2 * M ∧
        |derivWithin (expSteinSol h) (Set.Iic x) x| ≤ 2 * M

/-- Lemma 5.2(2) (`\label{lem172}` item 2 `\label{i172}`, `SteinIntro.tex:2751-2754, 2790-2796`;
`stmts-review-05D.md` `D2`, `ISSUE-5.2-PROOF`): for locally absolutely continuous
$h : \mathbb{R} \to \mathbb{R}$ (`D5`) satisfying $|h'(t)| \le L$ for all $t \in \mathbb{R}$,
`expSteinSol h` is everywhere differentiable, `deriv (expSteinSol h)` is $2 L$-Lipschitz on
$\mathbb{R}$, and $|f_h'(x)| \le L$ and $|f_h''(x)| \le 2 L$ for all $x \in \mathbb{R}$ (note
Lean's outer `deriv` returns `0` at points where $f_h'$ has a corner, while `LipschitzWith` holds
everywhere). -/
def Lem5_2_2 : Prop :=
  ∀ {h : ℝ → ℝ} {L : ℝ},
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b) →
    (∀ t : ℝ, |deriv h t| ≤ L) →
    Differentiable ℝ (expSteinSol h) ∧
      LipschitzWith (Real.toNNReal (2 * L)) (deriv (expSteinSol h)) ∧
      ∀ x : ℝ,
        |deriv (expSteinSol h) x| ≤ L ∧
        |deriv (deriv (expSteinSol h)) x| ≤ 2 * L

/-- Theorem 5.3(1) (`\label{thm171}`, `SteinIntro.tex:2758-2766`; `D6` literal class): if $W \ge 0$
a.s. has finite mean and $Z \sim \mathrm{Exp}(1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}_W} |\mathbb{E}[f'(W) - f(W)]|$. -/
def Thm5_3_1 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    0 ≤ᵐ[P] W →
    Integrable W P →
    AEMeasurable Z P' →
    P'.map Z = stdExpLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ expWassersteinClass, ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P|

/-- Theorem 5.3(2) (`\label{thm171}`, `SteinIntro.tex:2758-2760, 2767-2772`; `D6` literal class):
if $W \ge 0$ a.s. has finite mean and $Z \sim \mathrm{Exp}(1)$, then
$d_{\mathrm{K}}(\mathcal{L}(W), \mathcal{L}(Z)) \le
\sup_{f \in \mathcal{F}_K} |\mathbb{E}[f'(W) - f(W)]|$. -/
def Thm5_3_2 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ},
    0 ≤ᵐ[P] W →
    Integrable W P →
    AEMeasurable Z P' →
    P'.map Z = stdExpLaw →
    kolmogorovDist (P.map W) (P'.map Z) ≤
      ⨆ f ∈ expKolmogorovClass, ENNReal.ofReal |∫ ω, (deriv f (W ω) - f (W ω)) ∂P|

/-- Section 5.1 equilibrium uniqueness and Lebesgue absolute continuity (`SteinIntro.tex:2844-2845`;
`ISSUE-5.5`): for $W \ge 0$ a.s. integrable with $\mu = \mathbb{E}[W] > 0$, every equilibrium
random variable $W^e$ has the Lebesgue-absolutely-continuous law with density
$x \mapsto \frac{1}{\mu}\mathbb{P}(W > x)\mathbf{1}_{(0, \infty)}(x)$, and conversely this measure
is a probability measure absolutely continuous with respect to Lebesgue measure whose identity map
satisfies `IsEquilibrium`. -/
def Sec5_1_equilibrium_ac : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ},
    0 ≤ᵐ[P] W →
    Integrable W P →
    0 < ∫ ω, W ω ∂P →
    let μ : ℝ := ∫ ω, W ω ∂P
    let ρ : ℝ → ℝ≥0∞ :=
      (Set.Ioi (0 : ℝ)).indicator (fun x ↦ ENNReal.ofReal (P.real {ω | x < W ω} / μ))
    (∀ (P' : Measure Ω') [IsProbabilityMeasure P'] {We : Ω' → ℝ},
        IsEquilibrium P W P' We →
        P'.map We = volume.withDensity ρ ∧ Measure.AbsolutelyContinuous (P'.map We) volume) ∧
      (let ν : Measure ℝ := volume.withDensity ρ
       IsProbabilityMeasure ν ∧ Measure.AbsolutelyContinuous ν volume ∧ IsEquilibrium P W ν id)

/-- Section 5.1 prose: well-definedness of $\mathbb{E}[f'(W^e)]$ in `(5.3)` (`\label{173}`,
`SteinIntro.tex:2844-2845`; `ISSUE-5.5`, `D-E3`): for any non-negative integrable $W$ with
$\mu = \mathbb{E}[W] > 0$, any equilibrium variable $W^e$ (`IsEquilibrium P W P' We`), and any
$K$-Lipschitz function $f : \mathbb{R} \to \mathbb{R}$, $f$ is differentiable at $W^e(\omega')$
for $P'$-almost-every $\omega'$, `deriv f ∘ We` is $P'$-integrable, and every function
$g : \mathbb{R} \to \mathbb{R}$ agreeing with `deriv f` where $f$ is differentiable is
$P'$-integrable along $W^e$ with $\int g(W^e)\,dP' = \int f'(W^e)\,dP'$. -/
def Sec5_1_equilibrium_rhs_wellDefined : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {We : Ω' → ℝ} {f g : ℝ → ℝ} {K : ℝ≥0},
    (0 ≤ᵐ[P] W) →
    Integrable W P →
    0 < ∫ ω, W ω ∂P →
    IsEquilibrium P W P' We →
    LipschitzWith K f →
    (∀ x : ℝ, DifferentiableAt ℝ f x → g x = deriv f x) →
    (∀ᵐ ω' ∂P', DifferentiableAt ℝ f (We ω')) ∧
      Integrable (fun ω' ↦ deriv f (We ω')) P' ∧
      Integrable (fun ω' ↦ g (We ω')) P' ∧
      (∫ ω', g (We ω') ∂P' = ∫ ω', deriv f (We ω') ∂P')

/-- Theorem 5.4 (`\label{thm172}`, `SteinIntro.tex:2847-2853`): if $W \ge 0$ a.s. satisfies
$\mathbb{E}[W] = 1$ and $\mathbb{E}[W^2] < \infty$, $W^e$ has the equilibrium distribution with
respect to $W$ on the same probability space, and $Z \sim \mathrm{Exp}(1)$, then
$d_{\mathrm{W}}(\mathcal{L}(W), \mathcal{L}(Z)) \le 2\,\mathbb{E}|W^e - W|$ (where the Bochner
integral on the right-hand side is genuine since $W \in L^2$ implies $\mathbb{E}[W^e] =
\mathbb{E}[W^2]/2 < \infty$). -/
def Thm5_4 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W We : Ω → ℝ} {Z : Ω' → ℝ},
    0 ≤ᵐ[P] W →
    MemLp W 2 P →
    ∫ ω, W ω ∂P = 1 →
    IsEquilibrium P W P We →
    AEMeasurable Z P' →
    P'.map Z = stdExpLaw →
    wassersteinDist (P.map W) (P'.map Z) ≤ ENNReal.ofReal (2 * ∫ ω, |We ω - W ω| ∂P)

/-- Proposition 5.5 (`\label{prop171}`, `SteinIntro.tex:2863-2867`; literal per `D1`): if
$W \ge 0$ a.s. is integrable, $W^s$ has the size-bias distribution of $W$, and $U$ is uniform on
$(0, 1)$ independent of $W^s$, then $U W^s$ has the equilibrium distribution of $W$. -/
def Prop5_5 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Ws U : Ω' → ℝ},
    0 ≤ᵐ[P] W →
    Integrable W P →
    IsSizeBias P W P' Ws →
    MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P' →
    ProbabilityTheory.IndepFun U Ws P' →
    IsEquilibrium P W P' (fun ω' ↦ U ω' * Ws ω')

/-- Remark 5.3 (`\label{rem171}`, `SteinIntro.tex:2875-2880`): for $Y \ge 0$ a.s. integrable with
$\mu = \mathbb{E}[Y] > 0$, if $Y^e$ has the equilibrium distribution of $Y$ and is independent of an
i.i.d. sequence $Y_0, Y_1, \dots$ distributed as $Y$, then the delayed renewal sequence
$S_n = Y^e + \sum_{k=0}^{n-1} Y_k$ ($n \ge 0$) is stationary: (i) its renewal measure on $(a, b]$
equals $(b - a)/\mu$ for all $0 \le a \le b$, and (ii) for every $t \ge 0$, the post-$t$ epoch
process $(S_{N_t + k} - t)_{k \ge 0}$ (with $N_t = \inf\{n \in \mathbb{N} \mid t < S_n\}$) has the
same joint law on $\mathbb{N} \to \mathbb{R}$ as $(S_k)_{k \ge 0}$. -/
def Rem5_3 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y Ye : Ω → ℝ} {Yseq : ℕ → Ω → ℝ},
    0 ≤ᵐ[P] Y →
    Integrable Y P →
    0 < ∫ ω, Y ω ∂P →
    IsEquilibrium P Y P Ye →
    ProbabilityTheory.iIndepFun Yseq P →
    (∀ k : ℕ, ProbabilityTheory.IdentDistrib (Yseq k) Y P P) →
    ProbabilityTheory.IndepFun Ye (fun ω (k : ℕ) ↦ Yseq k ω) P →
    let μ : ℝ := ∫ ω, Y ω ∂P
    let S : ℕ → Ω → ℝ := fun n ω ↦ Ye ω + ∑ k ∈ Finset.range n, Yseq k ω
    (∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∑' n : ℕ, P {ω | S n ω ∈ Set.Ioc a b} = ENNReal.ofReal ((b - a) / μ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        let Nt : Ω → ℕ := fun ω ↦ sInf {n : ℕ | t < S n ω}
        ProbabilityTheory.IdentDistrib
          (fun ω (k : ℕ) ↦ S (Nt ω + k) ω - t)
          (fun ω (k : ℕ) ↦ S k ω) P P)

/-- Example 5.4, weak convergence prose claim (`\label{ex171}`, `SteinIntro.tex:2885`; `M4`):
as $p \to 0^+$, for $N_p \sim \mathrm{Ge}(p)$ on $\{1, 2, \dots\}$ and $Z \sim \mathrm{Exp}(1)$,
$p N_p$ converges to $Z$ in Wasserstein distance, in Kolmogorov distance, and weakly
($\mathbb{E}[g(p N_p)] \to \mathbb{E}[g(Z)]$ for every bounded continuous
$g : \mathbb{R} \to \mathbb{R}$). -/
def Ex5_4_weak_conv : Prop :=
  ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : Ω' → ℝ}
    {Ω : ℝ → Type*} [∀ p, MeasurableSpace (Ω p)] (P : ∀ p, Measure (Ω p))
    {N : ∀ p, Ω p → ℕ},
    AEMeasurable Z P' →
    P'.map Z = stdExpLaw →
    (∀ p ∈ Set.Ioc (0 : ℝ) 1,
      IsProbabilityMeasure (P p) ∧ AEMeasurable (N p) (P p) ∧ (P p).map (N p) = shiftedGeomLaw p) →
    Filter.Tendsto
      (fun p : ℝ ↦ wassersteinDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto
      (fun p : ℝ ↦ kolmogorovDist ((P p).map (fun ω ↦ p * (N p ω : ℝ))) (P'.map Z))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ g : ℝ → ℝ, Continuous g → (∃ M : ℝ, ∀ x : ℝ, |g x| ≤ M) →
      Filter.Tendsto
        (fun p : ℝ ↦ ∫ ω, g (p * (N p ω : ℝ)) ∂(P p))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ z, g (Z z) ∂P')))

/-- Example 5.4, corrected ceiling prose claim (`\label{ex171}`, `SteinIntro.tex:2885-2886`;
`ISSUE-TYPO-5.4`): if $Z \sim \mathrm{Exp}(\lambda)$ with $\lambda > 0$, then the smallest integer
no less than $Z$ ($\lceil Z \rceil$, printed *"no greater than"* by typo) has the positive-support
geometric distribution $\mathrm{Ge}(1 - e^{-\lambda})$. -/
def Ex5_4_ceil_corrected : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ} {Z : Ω → ℝ},
    0 < r →
    AEMeasurable Z P →
    P.map Z = expLaw r →
    P.map (fun ω ↦ Nat.ceil (Z ω)) = shiftedGeomLaw (1 - Real.exp (-r))

/-- Section 5.1 equilibrium scaling, restricted to $c > 0$ (`SteinIntro.tex:2894`; `ISSUE-5.4`):
for a constant $c > 0$, $X^e$ has the equilibrium distribution of $X$ if and only if $c X^e$ has
the equilibrium distribution of $c X$. -/
def Sec5_1_equilibrium_scale_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Xe : Ω' → ℝ} {c : ℝ},
    0 < c →
    (IsEquilibrium P X P' Xe ↔
      IsEquilibrium P (fun ω ↦ c * X ω) P' (fun ω' ↦ c * Xe ω'))

/-- Example 5.4 (`\label{ex171}`, `SteinIntro.tex:2883-2900`): for $0 < p \le 1$ and
$N \sim \mathrm{Ge}(p)$ on $\{1, 2, \dots\}$, (i) if $N^s$ has the size-bias distribution of $N$ and
$V$ is conditionally uniform on $\{1, \dots, N^s\}$, then $V \stackrel{d}{=} N$; (ii) if $U$ is
uniform on $(0, 1)$ independent of $N$, then $N - U$ has the equilibrium distribution of $N$ and
$W - p U$ has the equilibrium distribution of $W = p N$; and (iii) for $Z \sim \mathrm{Exp}(1)$,
$d_{\mathrm{W}}(\mathcal{L}(p N), \mathcal{L}(Z)) \le p$. -/
def Ex5_4 : Prop :=
  ∀ {p : ℝ}, 0 < p → p ≤ 1 →
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {N : Ω → ℕ} {Ns V : Ω' → ℕ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      AEMeasurable V P' →
      IsSizeBias P (fun ω ↦ (N ω : ℝ)) P' (fun ω' ↦ (Ns ω' : ℝ)) →
      (∀ k m : ℕ, P'.real {ω' | Ns ω' = k ∧ V ω' = m} =
        if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Ns ω' = k} / (k : ℝ) else 0) →
      P'.map V = P.map N) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {N : Ω → ℕ} {U : Ω → ℝ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P →
      ProbabilityTheory.IndepFun U N P →
      let W : Ω → ℝ := fun ω ↦ p * (N ω : ℝ)
      IsEquilibrium P (fun ω ↦ (N ω : ℝ)) P (fun ω ↦ (N ω : ℝ) - U ω) ∧
        IsEquilibrium P W P (fun ω ↦ W ω - p * U ω)) ∧
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {N : Ω → ℕ} {Z : Ω' → ℝ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      AEMeasurable Z P' →
      P'.map Z = stdExpLaw →
      wassersteinDist (P.map (fun ω ↦ p * (N ω : ℝ))) (P'.map Z) ≤ ENNReal.ofReal p)

/-- Theorem 5.6 (Rényi's Theorem, unlabeled, `SteinIntro.tex:2905-2911`; `D5-2`): for any
non-negative mean-$1$ distribution $\mathcal{L}(X_0)$, if for each $p \in (0, 1]$,
$(X_{p, i})_{i \ge 1}$ is an i.i.d. sequence distributed as $X_0$, $N_p \sim \mathrm{Ge}(p)$ is
independent of $(X_{p, i})_{i \ge 1}$, $W_p = p \sum_{i=1}^{N_p} X_{p, i}$, and
$Z \sim \mathrm{Exp}(1)$, then
$\lim_{p \to 0^+} d_{\mathrm{K}}(\mathcal{L}(W_p), \mathcal{L}(Z)) = 0$. -/
def Thm5_6 : Prop :=
  ∀ {Ω₀ Ω' : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω']
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X₀ : Ω₀ → ℝ} {Z : Ω' → ℝ}
    {Ω : ℝ → Type*} [∀ p, MeasurableSpace (Ω p)]
    (P : ∀ p, Measure (Ω p))
    {X : ∀ p, ℕ → Ω p → ℝ} {N : ∀ p, Ω p → ℕ},
    0 ≤ᵐ[P₀] X₀ →
    Integrable X₀ P₀ →
    ∫ ω₀, X₀ ω₀ ∂P₀ = 1 →
    AEMeasurable Z P' →
    P'.map Z = stdExpLaw →
    (∀ p ∈ Set.Ioc (0 : ℝ) 1,
      IsProbabilityMeasure (P p) ∧
      ProbabilityTheory.iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X p i.1) (P p) ∧
      (∀ i : ℕ, 1 ≤ i → ProbabilityTheory.IdentDistrib (X p i) X₀ (P p) P₀) ∧
      AEMeasurable (N p) (P p) ∧
      (P p).map (N p) = shiftedGeomLaw p ∧
      ProbabilityTheory.IndepFun (N p) (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X p i.1 ω) (P p)) →
    Filter.Tendsto
      (fun p : ℝ ↦
        kolmogorovDist
          ((P p).map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N p ω), X p i ω))
          (P'.map Z))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0)

/-- Section 5.2, equation (5.6) equilibrium coupling (`\label{179}`,
`SteinIntro_utf8.tex:2953-2957`; `M2`): for independent non-negative mean-$1$ summands
$(X_i)_{i \ge 1}$ (requiring $L^1$ only), integer-valued $N, M \ge 1$ a.s. with
$\mathbb{E}[N] = 1/p$ and $\mathbb{P}(M = m) = p\,\mathbb{P}(N \ge m)$ ($m \ge 1$) jointly
independent of $(X_i)_{i \ge 1}$, and equilibrium variables $X_i^e$ each independent of
$(N, M, (X_j)_{j \ne i})$, the sum $W = p \sum_{i=1}^N X_i$ is integrable with $\mathbb{E}[W] = 1$
and $W^e = p (\sum_{i=1}^{M-1} X_i + X_M^e)$ has the equilibrium distribution of $W$. -/
def Sec5_2_eq5_6 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} {X Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ},
    0 < p →
    p ≤ 1 →
    (∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) →
    (∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i) →
    (∀ i : ℕ, 1 ≤ i → Integrable (X i) P) →
    (∀ i : ℕ, 1 ≤ i → ∫ ω, X i ω ∂P = 1) →
    ProbabilityTheory.iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P →
    AEMeasurable N P →
    AEMeasurable M P →
    (∀ᵐ ω ∂P, 1 ≤ N ω) →
    Integrable (fun ω ↦ (N ω : ℝ)) P →
    ∫ ω, (N ω : ℝ) ∂P = 1 / p →
    (∀ᵐ ω ∂P, 1 ≤ M ω) →
    (∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω}) →
    (∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (Xe i)) →
    (∀ i : {i : ℕ // 1 ≤ i},
      ProbabilityTheory.IndepFun (Xe i.1)
        (fun ω ↦ (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P) →
    ProbabilityTheory.IndepFun (fun ω ↦ (N ω, M ω))
      (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P →
    let W : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
    let We : Ω → ℝ := fun ω ↦ p * ((∑ i ∈ Finset.Ico 1 (M ω), X i ω) + Xe (M ω) ω)
    Integrable W P ∧ (∫ ω, W ω ∂P = 1) ∧ IsEquilibrium P W P We

/-- Theorem 5.7, corrected (`\label{thm1710}`, eqs. `(5.4)`–`(5.5)` `\label{177}`–`\label{178}`,
`SteinIntro.tex:2915-2929`; `ISSUE-5.7`, `DEFINITIONS.md` §5.3, `D5-1`): Wasserstein exponential
approximation bound for geometric-like random sums $W = p \sum_{i=1}^N X_i$, requiring $M \ge 1$
a.s. with $\mathbb{P}(M = m) = p\,\mathbb{P}(N \ge m)$ for $m \ge 1$, the printed joint
independence of each $X_i^e$ from $(N, M, (X_j)_{j \ne i})$, and the minimal omitted joint
independence of $(N, M)$ from $(X_i)_{i \ge 1}$, and expressing potentially infinite moments on the
right-hand side in `ℝ≥0∞`. -/
def Thm5_7_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℝ} {X Xe : ℕ → Ω → ℝ} {N M : Ω → ℕ} {Z : Ω' → ℝ},
    0 < p →
    p ≤ 1 →
    (∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) →
    (∀ i : ℕ, 1 ≤ i → 0 ≤ᵐ[P] X i) →
    (∀ i : ℕ, 1 ≤ i → MemLp (X i) 2 P) →
    (∀ i : ℕ, 1 ≤ i → ∫ ω, X i ω ∂P = 1) →
    ProbabilityTheory.iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P →
    AEMeasurable N P →
    AEMeasurable M P →
    (∀ᵐ ω ∂P, 1 ≤ N ω) →
    Integrable (fun ω ↦ (N ω : ℝ)) P →
    ∫ ω, (N ω : ℝ) ∂P = 1 / p →
    (∀ᵐ ω ∂P, 1 ≤ M ω) →
    (∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω}) →
    (∀ i : ℕ, 1 ≤ i → IsEquilibrium P (X i) P (Xe i)) →
    (∀ i : {i : ℕ // 1 ≤ i},
      ProbabilityTheory.IndepFun (Xe i.1)
        (fun ω ↦ (N ω, M ω, fun j : {j : {k : ℕ // 1 ≤ k} // j ≠ i} ↦ X j.1.1 ω)) P) →
    ProbabilityTheory.IndepFun (fun ω ↦ (N ω, M ω))
      (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P →
    AEMeasurable Z P' →
    P'.map Z = stdExpLaw →
    let W : Ω → ℝ := fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω
    let μ₂ : ℝ≥0∞ := ⨆ (i : ℕ) (_ : 1 ≤ i), ENNReal.ofReal (∫ ω, X i ω ^ 2 ∂P)
    let err₁ : ℝ≥0∞ :=
      ENNReal.ofReal (2 * p) *
        ((∫⁻ ω, ENNReal.ofReal |X (M ω) ω - Xe (M ω) ω| ∂P) +
          ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
    let err₂ : ℝ≥0∞ :=
      ENNReal.ofReal (2 * p) *
        (1 + μ₂ / 2 + ∫⁻ ω, ENNReal.ofReal |(N ω : ℝ) - (M ω : ℝ)| ∂P)
    wassersteinDist (P.map W) (P'.map Z) ≤ err₁ ∧ err₁ ≤ err₂

/-- Remark 5.5 (`SteinIntro.tex:2931-2947`): (i) in the setting of Theorem 5.7, if $N^s$ has the
size-bias distribution of $N$ and $V$ is conditionally uniform on $\{1, \dots, N^s\}$, then
$M \stackrel{d}{=} V$; (ii) if $N \sim \mathrm{Ge}(p)$ ($0 < p \le 1$), then $M = N$ satisfies
$M \ge 1$ a.s. and $\mathbb{P}(M = m) = p\,\mathbb{P}(N \ge m)$ for all $m \ge 1$; and (iii) if in
addition $(X_i)_{i \ge 1}$ are independent $\mathrm{Exp}(1)$ random variables independent of $N$,
then $d_{\mathrm{W}}(\mathcal{L}(p \sum_{i=1}^N X_i), \mathcal{L}(Z)) = 0$. -/
def Rem5_5 : Prop :=
  ∀ {p : ℝ}, 0 < p → p ≤ 1 →
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {N M : Ω → ℕ} {Ns V : Ω' → ℕ},
      AEMeasurable N P →
      AEMeasurable M P →
      (∀ᵐ ω ∂P, 1 ≤ N ω) →
      Integrable (fun ω ↦ (N ω : ℝ)) P →
      ∫ ω, (N ω : ℝ) ∂P = 1 / p →
      (∀ᵐ ω ∂P, 1 ≤ M ω) →
      (∀ m : ℕ, 1 ≤ m → P.real {ω | M ω = m} = p * P.real {ω | m ≤ N ω}) →
      AEMeasurable V P' →
      IsSizeBias P (fun ω ↦ (N ω : ℝ)) P' (fun ω' ↦ (Ns ω' : ℝ)) →
      (∀ k m : ℕ, P'.real {ω' | Ns ω' = k ∧ V ω' = m} =
        if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Ns ω' = k} / (k : ℝ) else 0) →
      P.map M = P'.map V) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : Ω → ℕ},
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      (∀ᵐ ω ∂P, 1 ≤ N ω) ∧
        ∀ m : ℕ, 1 ≤ m → P.real {ω | N ω = m} = p * P.real {ω | m ≤ N ω}) ∧
    (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
      (P : Measure Ω) [IsProbabilityMeasure P]
      (P' : Measure Ω') [IsProbabilityMeasure P']
      {X : ℕ → Ω → ℝ} {N : Ω → ℕ} {Z : Ω' → ℝ},
      (∀ i : ℕ, 1 ≤ i → AEMeasurable (X i) P) →
      (∀ i : ℕ, 1 ≤ i → P.map (X i) = stdExpLaw) →
      ProbabilityTheory.iIndepFun (fun i : {i : ℕ // 1 ≤ i} ↦ X i.1) P →
      AEMeasurable N P →
      P.map N = shiftedGeomLaw p →
      ProbabilityTheory.IndepFun N (fun ω (i : {i : ℕ // 1 ≤ i}) ↦ X i.1 ω) P →
      AEMeasurable Z P' →
      P'.map Z = stdExpLaw →
      wassersteinDist (P.map (fun ω ↦ p * ∑ i ∈ Finset.Icc 1 (N ω), X i ω)) (P'.map Z) = 0)

/-- Section 5.3 existence of a non-degenerate critical Galton–Watson process with $\sigma^2 > 0$
(`I-2`, `SteinIntro.tex:2993-2997, 3007-3020`): there exists a probability space $(\Omega, P)$ and
a critical Galton–Watson process $Z$ with offspring law $\frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$
satisfying $\mathbb{E}[Z_1] = 1$, $\operatorname{Var}(Z_1) = 1 > 0$, and
$\mathbb{E}|Z_1|^3 < \infty$. -/
def Sec5_3_exists_isGaltonWatson_pos_var : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (Z : ℕ → Ω → ℕ),
    IsGaltonWatson P Z ∧
    (∫ ω, (Z 1 ω : ℝ) ∂P = 1) ∧
    ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P = 1 ∧
    Integrable (fun ω ↦ |(Z 1 ω : ℝ)| ^ 3) P ∧
    P.real {ω | Z 1 ω = 0} = 1 / 2 ∧
    P.real {ω | Z 1 ω = 2} = 1 / 2

/-- Section 5.3 existence of the Lyons–Pemantle–Peres size-bias spine coupling (`I-2`,
`SteinIntro.tex:3030-3042, 3128-3136`): for every critical Galton–Watson branching process with
finite variance and every generation $n \ge 0$, there exists a probability space $(\Omega', P')$
supporting $(X, L, R, R', U)$ satisfying `IsSizeBiasSpineCoupling`. -/
def Sec5_3_exists_isSizeBiasSpineCoupling : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    ∀ n : ℕ,
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (X L R R' : ℕ → Ω' → ℕ) (U : Ω' → ℝ),
        IsSizeBiasSpineCoupling P Z P' n X L R R' U

/-- Section 5.3 Galton–Watson extinction dichotomy (`SteinIntro.tex:3003-3004`;
`ISSUE-TYPO-5.3a`): for a Galton–Watson branching process $(Z_n)_{n \ge 0}$, (i) if
$\mathbb{E}[Z_1] \le 1$ and $\mathbb{P}(Z_1 = 1) < 1$ (printed `\IP(Z_1=1<1)` by typo), then the
population almost surely dies out ($\mathbb{P}(\exists n, Z_n = 0) = 1$), whereas (ii) if
$\mathbb{E}[Z_1] > 1$, the probability that the population lives forever is strictly positive
($\mathbb{P}(\forall n, Z_n > 0) > 0$). -/
def Sec5_3_extinction : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ((∫ ω, (Z 1 ω : ℝ) ∂P ≤ 1 → P.real {ω | Z 1 ω = 1} < 1 →
        P {ω | ∃ n : ℕ, Z n ω = 0} = 1) ∧
      (1 < ∫ ω, (Z 1 ω : ℝ) ∂P →
        0 < P {ω | ∀ n : ℕ, 0 < Z n ω}))

/-- Theorem 5.8 (Yaglom's Theorem), restricted to $\sigma^2 = \mathrm{Var}(Z_1) > 0$
(`SteinIntro.tex:3007-3013`; `ISSUE-5.8`): if $(Z_n)_{n \ge 0}$ is a Galton–Watson branching
process with $\mathbb{E}[Z_1] = 1$ and $0 < \sigma^2 = \mathrm{Var}(Z_1) < \infty$,
$Y_n \stackrel{d}{=} (Z_n \mid Z_n > 0)$, and $Z \sim \mathrm{Exp}(1)$, then
$\lim_{n \to \infty} d_{\mathrm{K}}(\mathcal{L}(2 Y_n / (n \sigma^2)), \mathcal{L}(Z)) = 0$ (at
$\sigma^2 = 0$ the printed normalization $2 Y_n / (n \sigma^2)$ is ill-defined, with
`not_Thm5_8_printed` refuting the `0 / 0 = 0` Lean transcription). -/
def Thm5_8_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {Zexp : Ω' → ℝ}
    {ΩY : ℕ → Type*} [∀ n, MeasurableSpace (ΩY n)]
    (PY : ∀ n, Measure (ΩY n)) [∀ n, IsProbabilityMeasure (PY n)]
    {Y : ∀ n, ΩY n → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P →
    (∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Y n) (PY n) ∧
      (PY n).map (Y n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n)) →
    AEMeasurable Zexp P' →
    P'.map Zexp = stdExpLaw →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    Filter.Tendsto
      (fun n : ℕ ↦
        kolmogorovDist
          ((PY n).map (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq)))
          (P'.map Zexp))
      Filter.atTop
      (nhds 0)

/-- Theorem 5.9, restricted to $\sigma^2 = \mathrm{Var}(Z_1) > 0$ and $n \ge 2$
(`SteinIntro.tex:3015-3020`; `ISSUE-5.9`): if $(Z_n)_{n \ge 0}$ is a Galton–Watson branching
process with $\mathbb{E}[Z_1] = 1$, $0 < \sigma^2 = \mathrm{Var}(Z_1) < \infty$, and
$\mathbb{E}|Z_1|^3 < \infty$, $Y_n \stackrel{d}{=} (Z_n \mid Z_n > 0)$, and
$Z \sim \mathrm{Exp}(1)$, then there exists a constant $C$ such that for all $n \ge 2$,
$d_{\mathrm{W}}(\mathcal{L}(2 Y_n / (n \sigma^2)), \mathcal{L}(Z)) \le C \log(n) / n$ (whereas at
$n = 1$, $\log 1 = 0$ makes the printed bound fail; `not_Thm5_9_printed`). -/
def Thm5_9_restricted : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {Zexp : Ω' → ℝ}
    {ΩY : ℕ → Type*} [∀ n, MeasurableSpace (ΩY n)]
    (PY : ∀ n, Measure (ΩY n)) [∀ n, IsProbabilityMeasure (PY n)]
    {Y : ∀ n, ΩY n → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P →
    0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P →
    (∀ n : ℕ, 1 ≤ n →
      AEMeasurable (Y n) (PY n) ∧
      (PY n).map (Y n) = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n)) →
    AEMeasurable Zexp P' →
    P'.map Zexp = stdExpLaw →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      wassersteinDist
        ((PY n).map (fun ω ↦ 2 * (Y n ω : ℝ) / ((n : ℝ) * σsq)))
        (P'.map Zexp) ≤
        ENNReal.ofReal (C * Real.log (n : ℝ) / (n : ℝ))

/-- Section 5.3 Equation (5.7) (`\label{1710}`, `SteinIntro.tex:3054-3056`, proved via the
definitional recursion at `SteinIntro.tex:3085-3098`; `ISSUE-TYPO-5.3b`, `I-1`): for every
offspring PMF $p : \mathbb{N} \to \mathbb{R}$, every depth-$n$ planar tree $t$, and every
individual $v$ in generation $n$ of $t$, $G_n^s(t, v) = G_n(t)$. -/
def Sec5_3_eq_1710 : Prop :=
  ∀ (p : ℕ → ℝ) {n : ℕ} (t : GWTree n) (v : GWVertex t),
    gwSizeBiasProbV p t v = gwProb p t

/-- Section 5.3 Equation (5.8) (`\label{1711}`, `SteinIntro.tex:3070-3072`; `I-1`): for every
offspring PMF $p : \mathbb{N} \to \mathbb{R}$ and every depth-$n$ planar tree $t$,
$G_n^s(t) = t_n G_n(t)$, where $t_n$ is the size of generation $n$ of $t$. -/
def Sec5_3_eq_1711 : Prop :=
  ∀ (p : ℕ → ℝ) {n : ℕ} (t : GWTree n),
    gwSizeBiasProb p t = (gwTreeGenSize t : ℝ) * gwProb p t

/-- Section 5.3 tree-probability link to the Galton–Watson generation-size law and normalization
(`I-1(a,c)`, `SteinIntro.tex:3047-3048, 3074-3076`): for a Galton–Watson process with offspring
PMF $p(k) = \mathbb{P}(Z_1 = k)$, summing `gwProb p t` over all depth-$n$ planar trees with
$t_n = k$ yields $\mathbb{P}(Z_n = k)$, and summing `gwProb p t` over all depth-$n$ planar trees
yields $1$. -/
def Sec5_3_gwProb_sum_genSize : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    let p : ℕ → ℝ := fun k ↦ P.real {ω | Z 1 ω = k}
    ∀ n : ℕ,
      (Summable (gwProb p : GWTree n → ℝ) ∧ (∑' t : GWTree n, gwProb p t) = 1) ∧
      ∀ k : ℕ,
        Summable (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwProb p t.1) ∧
        (∑' t : {t : GWTree n // gwTreeGenSize t = k}, gwProb p t.1) =
          P.real {ω | Z n ω = k}

/-- Section 5.3 size-bias tree-probability link to the spine joint law and normalization
(`I-1(b,c)`, `SteinIntro.tex:3048-3052, 3074-3079`): for a critical Galton–Watson process with
offspring PMF $p(k) = \mathbb{P}(Z_1 = k)$ and spine $(X, L, R)$ at generation $n$, summing
`gwSizeBiasProbV p t v` over all $(t, v)$ with $t_n = k$ and $\mathrm{left}(t, v) = m$ yields
$\mathbb{P}(S_n = k \wedge L_n = m)$, summing `gwSizeBiasProb p t` over $t_n = k$ yields
$\mathbb{P}(S_n = k) = k\,\mathbb{P}(Z_n = k)$, and `gwSizeBiasProb p` sums to $1$ over all
depth-$n$ planar trees. -/
def Sec5_3_gwSizeBiasProbV_sum_spine : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpine P Z P' n X L R →
    let p : ℕ → ℝ := fun k ↦ P.real {ω | Z 1 ω = k}
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    (Summable (gwSizeBiasProb p : GWTree n → ℝ) ∧ (∑' t : GWTree n, gwSizeBiasProb p t) = 1) ∧
    (∀ k : ℕ,
      Summable (fun t : {t : GWTree n // gwTreeGenSize t = k} ↦ gwSizeBiasProb p t.1) ∧
      (∑' t : {t : GWTree n // gwTreeGenSize t = k}, gwSizeBiasProb p t.1) =
        P'.real {ω' | Sn ω' = k}) ∧
    ∀ k m : ℕ,
      Summable
        (fun tv : {tv : Σ t : GWTree n, GWVertex t //
            gwTreeGenSize tv.1 = k ∧ gwLeftCount tv.1 tv.2 = m} ↦
          gwSizeBiasProbV p tv.1.1 tv.1.2) ∧
      (∑' tv : {tv : Σ t : GWTree n, GWVertex t //
          gwTreeGenSize tv.1 = k ∧ gwLeftCount tv.1 tv.2 = m},
        gwSizeBiasProbV p tv.1.1 tv.1.2) =
        P'.real {ω' | Sn ω' = k ∧ Ln ω' = m}

/-- Section 5.3 Item (1) (`\label{i171a}`, `SteinIntro.tex:3061, 3069-3076`): in the size-bias
Galton–Watson tree of a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$), the generation-$n$
size $S_n = 1 + \sum_{j=1}^n (L_{n,j} + R_{n,j})$ has the size-bias distribution of $Z_n$. -/
def Sec5_3_item_1 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpine P Z P' n X L R →
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
    IsSizeBias P (fun ω ↦ (Z n ω : ℝ)) P' Sn

/-- Section 5.3 positive-conditioning size-bias invariance (`SteinIntro.tex:3077-3078`):
conditioning a non-negative integrable random variable $X$ with $\mathbb{E}[X] > 0$ to be strictly
positive does not change its size-bias distribution. -/
def Sec5_3_sizeBias_cond_pos : Prop :=
  ∀ {Ω ΩY Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {X : Ω → ℝ} {Y : ΩY → ℝ} {Xs : Ω' → ℝ},
    0 ≤ᵐ[P] X →
    Integrable X P →
    0 < ∫ ω, X ω ∂P →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < X ω}).map X →
    (IsSizeBias P X P' Xs ↔ IsSizeBias PY Y P' Xs)

/-- Section 5.3 Item (2) (`\label{i172a}`, `SteinIntro.tex:3062-3063, 3077-3078`): in a critical
Galton–Watson process ($\mathbb{E}[Z_1] = 1$), if $Y_n \stackrel{d}{=} (Z_n \mid Z_n > 0)$ and
$Y_n^s$ has the size-bias distribution of $Y_n$, then $S_n \stackrel{d}{=} Y_n^s$. -/
def Sec5_3_item_2 : Prop :=
  ∀ {Ω ΩY Ωs Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ωs] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (Ps : Measure Ωs) [IsProbabilityMeasure Ps]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {Y : ΩY → ℕ} {Ys : Ωs → ℝ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) →
    IsSizeBias PY (fun ω ↦ (Y ω : ℝ)) Ps Ys →
    IsSizeBiasSpine P Z P' n X L R →
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
    P'.map Sn = Ps.map Ys

/-- Section 5.3 Item (3) (`\label{i173}`, `SteinIntro.tex:3064, 3078-3079`): given $S_n = k$, the
distinguished vertex $v_n$ is uniformly distributed among the $k$ individuals of generation $n$,
i.e. $\mathbb{P}(S_n = k \wedge L_n = m) = \mathbb{P}(S_n = k) / k$ for $0 \le m < k$ and
$\mathbb{P}(S_n = k \wedge R_n = m) = \mathbb{P}(S_n = k) / k$ for $1 \le m \le k$. -/
def Sec5_3_item_3 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpine P Z P' n X L R →
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
    let Rn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, R j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    (∀ k m : ℕ, P'.real {ω' | Sn ω' = k ∧ Ln ω' = m} =
      if m < k then P'.real {ω' | Sn ω' = k} / (k : ℝ) else 0) ∧
    (∀ k m : ℕ, P'.real {ω' | Sn ω' = k ∧ Rn ω' = m} =
      if 1 ≤ m ∧ m ≤ k then P'.real {ω' | Sn ω' = k} / (k : ℝ) else 0)

/-- Section 5.3 Item (4) and `L3080-3081` distributional identity (`\label{i174}`,
`SteinIntro.tex:3065-3067, 3079-3082`): if $R_n$ is the number of individuals to the right
(inclusive) of $v_n$ and $U$ is uniform on $(0, 1)$ independent of all else, then
$R_n - U \stackrel{d}{=} U S_n$ and $Y_n^e := R_n - U$ has the equilibrium distribution of
$Y_n$. -/
def Sec5_3_item_4 : Prop :=
  ∀ {Ω ΩY Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {Y : ΩY → ℕ} {X L R : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) →
    IsSizeBiasSpine P Z P' n X L R →
    MeasureTheory.pdf.IsUniform U (Set.Ioo (0 : ℝ) 1) P' →
    IndepFun U (fun ω' (j : Finset.Icc 1 n) ↦ (X j.1 ω', L j.1 ω', R j.1 ω')) P' →
    let Rn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, ((L j ω' : ℝ) + (R j ω' : ℝ))
    P'.map (fun ω' ↦ Rn ω' - U ω') = P'.map (fun ω' ↦ U ω' * Sn ω') ∧
      IsEquilibrium PY (fun ω ↦ (Y ω : ℝ)) P' (fun ω' ↦ Rn ω' - U ω')

/-- Section 5.3 Equation (5.9) (`\label{1712}`, `SteinIntro.tex:3100-3113`): in the size-bias
Galton–Watson tree of a critical Galton–Watson process ($\mathbb{E}[Z_1] = 1$),
$\mathbb{P}(L_n = 0) = \mathbb{P}(Z_n > 0)$ and $S_n \mid \{L_n = 0\} \stackrel{d}{=} Y_n$. -/
def Sec5_3_eq_1712 : Prop :=
  ∀ {Ω ΩY Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace ΩY] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (PY : Measure ΩY) [IsProbabilityMeasure PY]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {Y : ΩY → ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    AEMeasurable Y PY →
    PY.map Y = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) →
    IsSizeBiasSpine P Z P' n X L R →
    let Ln : Ω' → ℕ := fun ω' ↦ ∑ j ∈ Finset.Icc 1 n, L j ω'
    let Sn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (L j ω' + R j ω')
    P' {ω' | Ln ω' = 0} = P {ω | 0 < Z n ω} ∧
      (ProbabilityTheory.cond P' {ω' | Ln ω' = 0}).map Sn = PY.map Y

/-- Section 5.3 non-independence of $L_{n,j}$ and $R_{n,j}$ (`SteinIntro.tex:3122-3126`):
$L_{n,n}$ and $R_{n,n}$ are the numbers of siblings of $v_n$ to the left and right
($L_{n,n} + R_{n,n} = X_n$ a.s.), and for fixed $j$, $L_{n,j}$ and $R_{n,j}$ are in general not
independent (witnessed by $Z_1 \sim \frac{1}{2}\delta_0 + \frac{1}{2}\delta_2$ at $j = n$). -/
def Sec5_3_not_indep_L_R : Prop :=
  (∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    1 ≤ n →
    IsGaltonWatson P Z →
    IsSizeBiasSpine P Z P' n X L R →
    ∀ᵐ ω' ∂P', L n ω' + R n ω' = X n ω') ∧
  ∃ (Ω Ω' : Type) (_ : MeasurableSpace Ω) (_ : MeasurableSpace Ω')
    (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (P' : Measure Ω') (_ : IsProbabilityMeasure P')
    (Z : ℕ → Ω → ℕ) (X L R : ℕ → Ω' → ℕ),
    IsGaltonWatson P Z ∧
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 ∧
    IsSizeBiasSpine P Z P' 1 X L R ∧
    ¬ IndepFun (L 1) (R 1) P'

/-- Section 5.3 spine realization of $Y_n$ (`SteinIntro.tex:3128-3139`): in a full size-bias spine
coupling at generation $n$, $R_n^* := 1 + \sum_{j=1}^n (R_{n,j} \mathbf{1}_{L_{n,j} = 0} +
R_{n,j}' \mathbf{1}_{L_{n,j} > 0})$ has the distribution of $Y_n \stackrel{d}{=}
(Z_n \mid Z_n > 0)$, while $Y_n^e := R_n - U$ has the equilibrium distribution of $R_n^*$. -/
def Sec5_3_spine_coupling : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    IsSizeBiasSpineCoupling P Z P' n X L R R' U →
    let Rstar : ℕ → Ω' → ℕ := fun j ω' ↦ if L j ω' = 0 then R j ω' else R' j ω'
    let Yn : Ω' → ℕ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, Rstar j ω'
    let Rn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)
    P'.map Yn = (ProbabilityTheory.cond P {ω | 0 < Z n ω}).map (Z n) ∧
      IsEquilibrium P' (fun ω' ↦ (Yn ω' : ℝ)) P' (fun ω' ↦ Rn ω' - U ω')

/-- Section 5.3 corrected coupling difference and triangle inequality (`I-6`,
`SteinIntro.tex:3142-3145`; `ISSUE-TYPO-5.3c`): with $Y_n = R_n^*$ and $Y_n^e = R_n - U$,
$Y_n - Y_n^e = U + \sum_{j=1}^n (R_{n,j}' - R_{n,j})\mathbf{1}_{L_{n,j} > 0}$ (not $1 - U + \dots$
as printed), and
$|Y_n - Y_n^e| \le |U| + \sum_{j=1}^n R_{n,j}' \mathbf{1}_{L_{n,j} > 0} +
\sum_{j=1}^n R_{n,j} \mathbf{1}_{L_{n,j} > 0}$. -/
def Sec5_3_eq_3143_corrected : Prop :=
  ∀ {Ω' : Type*} (n : ℕ) (L R R' : ℕ → Ω' → ℕ) (U : Ω' → ℝ) (ω' : Ω'),
    let Yn : ℝ :=
      1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
    let Yne : ℝ := (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
    Yn - Yne =
      U ω' + ∑ j ∈ Finset.Icc 1 n,
        ((R' j ω' : ℝ) - (R j ω' : ℝ)) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∧
    |Yn - Yne| ≤
      |U ω'| +
        (∑ j ∈ Finset.Icc 1 n, (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω') +
        (∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω')

/-- Section 5.3 negative correlation of $S_{n,j}$ and $\mathbf{1}_{L_{n,j} = 0}$ (`L3158`) and
corrected conditional expectation chain (`L3160-3163`; `ISSUE-5.9-PROOF`, `I-8`): for every
$j \in \{1, \dots, n\}$, $\mathbb{E}[S_{n,j} \mathbf{1}_{L_{n,j} = 0}] \le
\mathbb{E}[S_{n,j}]\,\mathbb{P}(L_{n,j} = 0)$, $\mathbb{E}[R_{n,j}'] =
\mathbb{E}[R_{n,j} \mid L_{n,j} = 0] = \mathbb{E}[S_{n,j} \mid L_{n,j} = 0] \le
\mathbb{E}[S_{n,j}] = \sigma^2$, and $\mathbb{E}[S_n] - 1 = n \sigma^2$. -/
def Sec5_3_neg_corr_3158_and_3160_corrected : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    IsSizeBiasSpineCoupling P Z P' n X L R R' U →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    let Snj : ℕ → Ω' → ℝ := fun j ω' ↦ (L j ω' : ℝ) + (R j ω' : ℝ)
    let Sn : Ω' → ℝ := fun ω' ↦ 1 + ∑ j ∈ Finset.Icc 1 n, Snj j ω'
    (∫ ω', Sn ω' ∂P') - 1 = (n : ℝ) * σsq ∧
    ∀ j ∈ Finset.Icc 1 n,
      ∫ ω', Snj j ω' * {ω'' : Ω' | L j ω'' = 0}.indicator 1 ω' ∂P' ≤
        (∫ ω', Snj j ω' ∂P') * P'.real {ω' | L j ω' = 0} ∧
      ∫ ω', (R' j ω' : ℝ) ∂P' =
        ∫ ω', (R j ω' : ℝ) ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) ∧
      ∫ ω', (R j ω' : ℝ) ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) =
        ∫ ω', Snj j ω' ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) ∧
      ∫ ω', Snj j ω' ∂(ProbabilityTheory.cond P' {ω' | L j ω' = 0}) ≤
        ∫ ω', Snj j ω' ∂P' ∧
      ∫ ω', Snj j ω' ∂P' = σsq

/-- Section 5.3 spine step bound (i) (`SteinIntro.tex:3148, 3154-3164`; `ISSUE-5.9-PROOF`): in a
critical Galton–Watson process with $\operatorname{Var}(Z_1) = \sigma^2 < \infty$, for every
$j \in \{1, \dots, n\}$,
$\mathbb{E}[R_{n,j}' \mathbf{1}_{L_{n,j} > 0}] = \mathbb{E}[R_{n,j}'] \mathbb{P}(L_{n,j} > 0) \le
\sigma^2 \mathbb{P}(L_{n,j} > 0)$. -/
def Sec5_3_step_i : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    IsSizeBiasSpineCoupling P Z P' n X L R R' U →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    ∀ j ∈ Finset.Icc 1 n,
      ∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' =
        (∫ ω', (R' j ω' : ℝ) ∂P') * P'.real {ω' | 0 < L j ω'} ∧
      ∫ ω', (R' j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        σsq * P'.real {ω' | 0 < L j ω'}

/-- Section 5.3 spine step bound (ii) (`SteinIntro.tex:3149-3150, 3166-3177`; `I-9`): in a
critical Galton–Watson process with $\mathbb{E}[Z_1^3] < \infty$, for every
$j \in \{1, \dots, n\}$,
$\mathbb{E}[R_{n,j} \mathbf{1}_{L_{n,j} > 0}] \le \mathbb{E}[X_j \mathbf{1}_{L_{n,j} > 0}] \le
\mathbb{E}[Z_1^3]\,\mathbb{P}(Z_{n-j} > 0)$. -/
def Sec5_3_step_ii : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {Z : ℕ → Ω → ℕ} {n : ℕ} {X L R : ℕ → Ω' → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P →
    IsSizeBiasSpine P Z P' n X L R →
    ∀ j ∈ Finset.Icc 1 n,
      ∫ ω', (R j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        ∫ ω', (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ∧
      ∫ ω', (X j ω' : ℝ) * {ω'' : Ω' | 0 < L j ω''}.indicator 1 ω' ∂P' ≤
        (∫ ω, (Z 1 ω : ℝ) ^ 3 ∂P) * P.real {ω | 0 < Z (n - j) ω}

/-- Section 5.3 spine step bound (iii) (`SteinIntro.tex:3151, 3179-3187`; `I-3`): in a critical
Galton–Watson process with $\operatorname{Var}(Z_1) = \sigma^2 < \infty$, there exists $C > 0$
(depending only on the process) such that for all $n \ge 1$ and $j \in \{1, \dots, n\}$,
$\mathbb{P}(L_{n,j} > 0) \le \sigma^2 \mathbb{P}(Z_{n-j} > 0) \le C (n - j + 1)^{-1}$. -/
def Sec5_3_step_iii : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    (∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      {n : ℕ} {X L R : ℕ → Ω' → ℕ},
      IsSizeBiasSpine P Z P' n X L R →
      ∀ j ∈ Finset.Icc 1 n,
        P'.real {ω' | 0 < L j ω'} ≤ σsq * P.real {ω | 0 < Z (n - j) ω}) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j ∈ Finset.Icc 1 n,
      σsq * P.real {ω | 0 < Z (n - j) ω} ≤ C * ((n - j + 1 : ℕ) : ℝ)⁻¹

/-- Section 5.3 Lyons–Pemantle–Peres $o(n)$ coupling discrepancy (`I-3`,
`SteinIntro.tex:3027`): for a critical Galton–Watson process with
$\operatorname{Var}(Z_1) < \infty$, the coupled variables $(Y_n, Y_n^e)$ satisfy
$\lim_{n \to \infty} \mathbb{E}|Y_n - Y_n^e| / n = 0$. -/
def Sec5_3_lpp_mean_diff_o_n : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ}
    {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (P' : ∀ n, Measure (Ω' n)) [∀ n, IsProbabilityMeasure (P' n)]
    {X L R R' : ∀ n, ℕ → Ω' n → ℕ} {U : ∀ n, Ω' n → ℝ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    (∀ n : ℕ, 1 ≤ n → IsSizeBiasSpineCoupling P Z (P' n) n (X n) (L n) (R n) (R' n) (U n)) →
    let Yn : ∀ n, Ω' n → ℝ := fun n ω' ↦
      1 + ∑ j ∈ Finset.Icc 1 n, (if L n j ω' = 0 then (R n j ω' : ℝ) else (R' n j ω' : ℝ))
    let Yne : ∀ n, Ω' n → ℝ := fun n ω' ↦
      (1 + ∑ j ∈ Finset.Icc 1 n, (R n j ω' : ℝ)) - U n ω'
    Filter.Tendsto (fun n : ℕ ↦ (∫ ω', |Yn n ω' - Yne n ω'| ∂P' n) / (n : ℝ))
      Filter.atTop (nhds 0)

/-- Section 5.3 Kolmogorov survival asymptotic, restricted to $\sigma^2 > 0$ (`I-5`,
`SteinIntro.tex:3028, 3185-3186`; `ISSUE-5.8`): for a critical Galton–Watson process with
$0 < \sigma^2 = \operatorname{Var}(Z_1) < \infty$,
$\lim_{n \to \infty} n\,\mathbb{P}(Z_n > 0) = 2 / \sigma^2$. -/
def Sec5_3_kolmogorov_survival_restricted : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 2 P →
    0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P →
    let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * P.real {ω | 0 < Z n ω})
      Filter.atTop (nhds (2 / σsq))

/-- Section 5.3 logarithmic coupling discrepancy bound, restricted to $n \ge 2$ (`I-3`, `I-4`,
`SteinIntro.tex:3022-3023, 3140-3145`; `ISSUE-5.9`): for a critical Galton–Watson process with
$\mathbb{E}|Z_1|^3 < \infty$, there exists a constant $C$ such that for all $n \ge 2$, the coupled
variables $(Y_n, Y_n^e)$ satisfy $\mathbb{E}|Y_n - Y_n^e| \le C \log(n)$. -/
def Sec5_3_lpp_mean_diff_log_restricted : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℕ},
    IsGaltonWatson P Z →
    ∫ ω, (Z 1 ω : ℝ) ∂P = 1 →
    MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P →
    ∃ C : ℝ, ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      {n : ℕ} {X L R R' : ℕ → Ω' → ℕ} {U : Ω' → ℝ},
      2 ≤ n →
      IsSizeBiasSpineCoupling P Z P' n X L R R' U →
      let Yn : Ω' → ℝ := fun ω' ↦
        1 + ∑ j ∈ Finset.Icc 1 n, (if L j ω' = 0 then (R j ω' : ℝ) else (R' j ω' : ℝ))
      let Yne : Ω' → ℝ := fun ω' ↦
        (1 + ∑ j ∈ Finset.Icc 1 n, (R j ω' : ℝ)) - U ω'
      ∫ ω', |Yn ω' - Yne ω'| ∂P' ≤ C * Real.log (n : ℝ)

/-- Section 5.3 proof opening: non-unit-mean witness for `ISSUE-5.9-PROOF-MEAN`
(`SteinIntro.tex:3023-3024`; `SE-4`): there exists a critical Galton–Watson process with
$\sigma^2 = \mathrm{Var}(Z_1) > 0$ and $\mathbb{E}|Z_1|^3 < \infty$ for which
$\mathbb{E}[2 Y_n / (n\sigma^2)] > 1$ for every $n \ge 1$ (so Theorem 5.4 `\label{thm172}`, which
requires $\mathbb{E}[W] = 1$, does not apply directly to $2 Y_n / (n\sigma^2)$ without the
$|1 - \mathbb{E}[W]|$ bridge used in `thm5_9_restricted`). -/
def Sec5_3_scaled_Yn_mean_gt_one_witness : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (_ : IsProbabilityMeasure P) (Z : ℕ → Ω → ℕ),
    IsGaltonWatson P Z ∧
      ∫ ω, (Z 1 ω : ℝ) ∂P = 1 ∧
      MemLp (fun ω ↦ (Z 1 ω : ℝ)) 3 P ∧
      0 < ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P ∧
      ∀ n : ℕ, 1 ≤ n →
        let σsq : ℝ := ProbabilityTheory.variance (fun ω ↦ (Z 1 ω : ℝ)) P
        1 < ∫ ω, 2 * (Z n ω : ℝ) / ((n : ℝ) * σsq)
          ∂(ProbabilityTheory.cond P {ω | 0 < Z n ω})

end SteinMethod
