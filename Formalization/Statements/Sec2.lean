/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs

/-!
# Section 2 Statements (`Formalization.Statements.Sec2`)

Self-contained theorem, proposition, lemma, and corollary statements from Section 2 of Nathan Ross,
*"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`, `SteinIntro.tex:558-699`), importing core
definitions only (`AGENTS.md` Rule 5).
-/

open MeasureTheory
open scoped ENNReal

namespace SteinMethod

/-- Lemma 2.1(1) (`\label{lem1}`, `SteinIntro.tex:562-569`): if $Z$ has the standard normal
distribution $\mathcal{N}(0, 1)$, then $\mathbb{E}[\mathcal{A}f(Z)] = 0$ for every locally
absolutely continuous function $f : \mathbb{R} \to \mathbb{R}$ (`D5`) satisfying
$\mathbb{E}|f'(Z)| < \infty$. -/
def Lem2_1_1 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} {f : ℝ → ℝ},
    AEMeasurable Z P →
    P.map Z = stdNormalLaw →
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
    Integrable (fun ω ↦ deriv f (Z ω)) P →
    ∫ ω, normalSteinOp f (Z ω) ∂P = 0

/-- Lemma 2.1(2) (`\label{lem1}`, `SteinIntro.tex:570-574`; `D5` literal): if $W$ is a real-valued
random variable such that $\mathbb{E}[\mathcal{A}f(W)] = 0$ for every locally absolutely continuous
function $f : \mathbb{R} \to \mathbb{R}$ satisfying $\mathbb{E}|f'(Z)| < \infty$ for
$Z \sim \mathcal{N}(0, 1)$, then $W$ has the standard normal distribution $\mathcal{N}(0, 1)$. -/
def Lem2_1_2 : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ},
    AEMeasurable W P →
    (∀ f : ℝ → ℝ, (∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) →
      Integrable (deriv f) stdNormalLaw →
      ∫ ω, normalSteinOp f (W ω) ∂P = 0) →
    P.map W = stdNormalLaw

/-- Lemma 2.2, corrected (`\label{lem2}`, eq. `(2.1)` `\label{1a}`, `SteinIntro.tex:578-588`;
`ISSUE-2.2`, `D4`): for every $x \in \mathbb{R}$, $f_x = \mathrm{normalSteinSolKolm}\,x$ is
bounded, continuous, satisfies the left-derivative normal Stein equation everywhere and the
two-sided normal Stein equation at every $w \ne x$, admits the lower-tail integral representation,
and is the unique bounded continuous solution of the left-derivative Stein equation. -/
def Lem2_2_corrected : Prop :=
  ∀ x : ℝ,
    (∃ B : ℝ, ∀ w : ℝ, |normalSteinSolKolm x w| ≤ B) ∧
    Continuous (normalSteinSolKolm x) ∧
    (∀ w : ℝ, HasDerivWithinAt (normalSteinSolKolm x)
      (w * normalSteinSolKolm x w + (Set.Iic x).indicator 1 w - stdNormalCDF x) (Set.Iic w) w) ∧
    (∀ w : ℝ, w ≠ x → HasDerivAt (normalSteinSolKolm x)
      (w * normalSteinSolKolm x w + (Set.Iic x).indicator 1 w - stdNormalCDF x) w) ∧
    (∀ w : ℝ, normalSteinSolKolm x w =
      -Real.exp (w ^ 2 / 2) *
        ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalCDF x - (Set.Iic x).indicator 1 t)) ∧
    (∀ g : ℝ → ℝ,
      (∃ B : ℝ, ∀ w : ℝ, |g w| ≤ B) →
      Continuous g →
      (∀ w : ℝ, HasDerivWithinAt g
        (w * g w + (Set.Iic x).indicator 1 w - stdNormalCDF x) (Set.Iic w) w) →
      g = normalSteinSolKolm x)

/-- Corollary 2.3, corrected (`\label{cor1}`, eq. `(2.2)` `\label{1}`, `SteinIntro.tex:591-596`;
`ISSUE-2.2`, `D4`): for every real-valued random variable $W$ and every $x \in \mathbb{R}$,
$|\mathbb{P}(W \le x) - \Phi(x)| = |\mathbb{E}[D_- f_x(W) - W f_x(W)]|$ using the left-derivative
normal Stein operator `normalSteinOpLeft`. -/
def Cor2_3_corrected : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : Ω → ℝ} (x : ℝ),
    AEMeasurable W P →
    |P.real {ω | W ω ≤ x} - stdNormalCDF x| =
      |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P|

/-- Post-Corollary 2.3 characterization remark (eq. `(2.2)` `\label{1}`,
`SteinIntro.tex:597-600`; `ISSUE-2.2`): for any real-valued random variable $W$, the left-hand side
$|\mathbb{P}(W \le x) - \Phi(x)|$ of `(2.2)` vanishes for all $x \in \mathbb{R}$ if and only if
$W \sim \mathcal{N}(0, 1)$, and the right-hand side of `(2.2)` likewise vanishes for all
$x \in \mathbb{R}$ if and only if $W \sim \mathcal{N}(0, 1)$ (both for the left-derivative operator
`normalSteinOpLeft` and for the two-sided operator `normalSteinOp`). -/
def Sec2_cor2_3_iff_stdNormal : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → ℝ},
    AEMeasurable W P →
    ((∀ x : ℝ, |P.real {ω | W ω ≤ x} - stdNormalCDF x| = 0) ↔ P.map W = stdNormalLaw) ∧
    ((∀ x : ℝ, |∫ ω, normalSteinOpLeft (normalSteinSolKolm x) (W ω) ∂P| = 0) ↔
      P.map W = stdNormalLaw) ∧
    ((∀ x : ℝ, |∫ ω, normalSteinOp (normalSteinSolKolm x) (W ω) ∂P| = 0) ↔
      P.map W = stdNormalLaw)

/-- Gaussian upper-tail bound in the proof of Lemma 2.2 (`\label{lem2}`,
`SteinIntro.tex:612-615`): for all $w > 0$,
$1 - \Phi(w) \le \min\bigl\{\frac{1}{2}, \frac{1}{w\sqrt{2\pi}}\bigr\} e^{-w^2/2}$. -/
def Sec2_stdNormalCDF_tail_le : Prop :=
  ∀ w : ℝ, 0 < w →
    1 - stdNormalCDF w ≤ min (1 / 2) (1 / (w * Real.sqrt (2 * Real.pi))) * Real.exp (-w ^ 2 / 2)

/-- Proposition 2.4 (`\label{prop31}`, eq. `(2.5)` `\label{31}`, `SteinIntro.tex:665-670`;
`D4` literal, `D1` integrability guard): if $W$ is a real-valued random variable, $Z$ has the
standard normal distribution $\mathcal{N}(0, 1)$, and $f_h$ solves
$f_h'(w) - w f_h(w) = h(w) - \Phi(h)$ everywhere for each $h \in \mathcal{H}$, then
$d_{\mathcal{H}}(\mathcal{L}(W), \mathcal{L}(Z))$ equals the `D1`-guarded supremum of
$|\mathbb{E}[f_h'(W) - W f_h(W)]|$ over $h \in \mathcal{H}$. -/
def Prop2_4 : Prop :=
  ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    {W : Ω → ℝ} {Z : Ω' → ℝ}
    (H : Set (ℝ → ℝ)) (f : (ℝ → ℝ) → ℝ → ℝ),
    AEMeasurable W P →
    AEMeasurable Z P' →
    P'.map Z = stdNormalLaw →
    (∀ h ∈ H, ∀ w : ℝ, HasDerivAt (f h) (w * f h w + h w - stdNormalExpect h) w) →
    ipm H (P.map W) (P'.map Z) =
      ⨆ h ∈ H, ⨆ (_ : Integrable h (P.map W) ∧ Integrable h (P'.map Z)),
        ENNReal.ofReal |∫ ω, normalSteinOp (f h) (W ω) ∂P|

/-- Lemma 2.5, solution formula and representations (`\label{lem31}`, eq. `(2.6)` `\label{33}`,
`SteinIntro.tex:674-684`): (i) for measurable $h : \mathbb{R} \to \mathbb{R}$ integrable under
$\mathcal{N}(0, 1)$, `normalSteinSol h` equals the lower-tail integral representation everywhere;
(ii) if moreover $h$ is continuous, `normalSteinSol h` solves
$f_h'(w) - w f_h(w) = h(w) - \Phi(h)$ with a two-sided derivative at every $w \in \mathbb{R}$. -/
def Lem2_5_formula : Prop :=
  (∀ {h : ℝ → ℝ}, Measurable h → Integrable h stdNormalLaw →
    ∀ w : ℝ, normalSteinSol h w =
      -Real.exp (w ^ 2 / 2) *
        ∫ t in Set.Iic w, Real.exp (-t ^ 2 / 2) * (stdNormalExpect h - h t)) ∧
  (∀ {h : ℝ → ℝ}, Measurable h → Integrable h stdNormalLaw → Continuous h →
    ∀ w : ℝ, HasDerivAt (normalSteinSol h)
      (w * normalSteinSol h w + h w - stdNormalExpect h) w)

/-- Lemma 2.5, pointwise ODE at continuity points (`\label{lem31}`, eq. `(2.6)` `\label{33}`,
`SteinIntro.tex:674-684`; `ISSUE-2.2`): for measurable $h : \mathbb{R} \to \mathbb{R}$ integrable
under $\mathcal{N}(0, 1)$, `normalSteinSol h` satisfies
$f_h'(w) - w f_h(w) = h(w) - \Phi(h)$ with a two-sided derivative at every continuity point $w$
of $h$. -/
def Lem2_5_ode_contAt : Prop :=
  ∀ {h : ℝ → ℝ}, Measurable h → Integrable h stdNormalLaw →
    ∀ w : ℝ, ContinuousAt h w →
      HasDerivAt (normalSteinSol h) (w * normalSteinSol h w + h w - stdNormalExpect h) w

/-- Lemma 2.5(1) (`\label{lem31}` item 1 `\label{i31}`, `SteinIntro.tex:686-689`): for measurable
$h : \mathbb{R} \to \mathbb{R}$ satisfying $|h(t) - \Phi(h)| \le M$ for all $t \in \mathbb{R}$,
$|f_h(w)| \le \sqrt{\pi / 2}\,M$ and $|f_h'(w)| \le 2 M$ for all $w \in \mathbb{R}$. -/
def Lem2_5_1 : Prop :=
  ∀ {h : ℝ → ℝ} {M : ℝ},
    Measurable h →
    (∀ t : ℝ, |h t - stdNormalExpect h| ≤ M) →
    ∀ w : ℝ,
      |normalSteinSol h w| ≤ Real.sqrt (Real.pi / 2) * M ∧
      |deriv (normalSteinSol h) w| ≤ 2 * M

/-- Lemma 2.5(2) (`\label{lem31}` item 2 `\label{i32}`, `SteinIntro.tex:690-694`): for locally
absolutely continuous $h : \mathbb{R} \to \mathbb{R}$ (`D5`) satisfying $|h'(t)| \le L$ for all
$t \in \mathbb{R}$, $|f_h(w)| \le 2 L$, $|f_h'(w)| \le \sqrt{2 / \pi}\,L$, and
$|f_h''(w)| \le 2 L$ for all $w \in \mathbb{R}$. -/
def Lem2_5_2 : Prop :=
  ∀ {h : ℝ → ℝ} {L : ℝ},
    (∀ a b : ℝ, AbsolutelyContinuousOnInterval h a b) →
    (∀ t : ℝ, |deriv h t| ≤ L) →
    ∀ w : ℝ,
      |normalSteinSol h w| ≤ 2 * L ∧
      |deriv (normalSteinSol h) w| ≤ Real.sqrt (2 / Real.pi) * L ∧
      |deriv (deriv (normalSteinSol h)) w| ≤ 2 * L

end SteinMethod
