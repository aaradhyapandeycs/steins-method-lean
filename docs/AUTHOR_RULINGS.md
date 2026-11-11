# Author Rulings & Pre-Authorizations

This ledger records explicit user/author rulings governing the repository setup, autonomous execution protocol, and multi-item theorem split policies required by `scripts/check_frozen_anchors.py`.

---

## `RULING-SETUP-001` — Repository Path, Root Namespace, and License

* **Approved By**: Repository Owner (`aaradhyapandey`)
* **Approved At**: `2026-11-10`
* **Decision**:
  * Local repository path: `<local>`
  * Lean 4 library & root namespace: `SteinsMethod`
  * Code license: `Apache-2.0` (`LICENSE`), preserving `CC-BY-4.0` attribution for `LeanAutoformalizationSkills` in `THIRD_PARTY_NOTICES.md` and `LICENSES/CC-BY-4.0.txt`.

---

## `AUTONOMOUS_PREAUTH_V1` — Autonomous Two-Seal Progression Under `/goal`

* **Approved By**: Repository Owner (`aaradhyapandey`)
* **Approved At**: `2026-11-10`
* **Decision**:
  * The author explicitly pre-authorized autonomous progression through the Two-Seal workflow (`Statement Seal` → `DEPGRAPH` → provider proofs → `Proof Seal` + kernel replay) across Ross (2011) while away, subject to:
    1. Every frozen declaration being elaborated transiently with zero errors/warnings prior to freezing;
    2. Every frozen declaration passing an independent subagent `lean-statement-audit` review (five-bin binder classification + definition audit);
    3. Every proof slice being extracted and audited in `DEPGRAPH.md` + `DEPGRAPH_COVERAGE.md`;
    4. Every sealed theorem passing `check_frozen_anchors.py`, `#print axioms` (restricted strictly to `{propext, Classical.choice, Quot.sound}`), `Lean.Kernel.Environment.replay`, and an independent Proof Seal audit;
    5. Writing canonical, Mathlib-grade Lean 4 definitions and theorems so downstream formalizers can build directly on `SteinsMethod`.

---

## `RULING-SPLIT-ENUM-001` — Multi-Part Enumerated Source Statements

* **Approved By**: `AUTONOMOUS_PREAUTH_V1`
* **Approved At**: `2026-11-10`
* **Decision**:
  * When a numbered Proposition, Lemma, or Theorem in Ross (2011) consists of mathematically independent enumerated items `(1)`, `(2)`, `(3)` with distinct carrier types or hypotheses (for example, Proposition 1.2 `\label{prop22}` where items 1–2 live on `ℝ` while item 3 lives on a countable discrete space, Lemma 2.1 `\label{lem1}` items 1–2, and Lemma 2.5 `\label{lem31}` items 1–2 for bounded vs. Lipschitz/AC test functions), each item may be anchored as an independent one-declaration-per-file frozen theorem under `split_policy.mode = "INDEPENDENT_BY_AUTHOR"` citing `RULING-SPLIT-ENUM-001` and sharing a common `source_group` (e.g., `ross2011.prop22`, `ross2011.lem1`, `ross2011.lem31`), so callers do not pay irrelevant carrier/regularity hypotheses from sibling items.
  * Single-item source theorems, lemmas, propositions, corollaries, and definitions use `split_policy.mode = "NOT_SPLIT"` citing `AUTONOMOUS_PREAUTH_V1`.


---

## `RULING-TOTALITY-WAVE1` — Explicit Measure-Theoretic, Totality, and Pointwise Regularity Guards (Sections 1–3.1)

* **Approved By**: `AUTONOMOUS_PREAUTH_V1`
* **Approved At**: `2026-11-10`
* **Cross-References**: `FINDING-001` through `FINDING-008` (originally in `docs/FINDINGS_LEDGER.md`, now merged into [`docs/SOURCE-ISSUES.md`](SOURCE-ISSUES.md))
* **Decision**:
  1. **Random-variable measurability (`FINDING-003`)**: Ross's prose convention "random variable $W$" on a probability space $(\Omega, \mathcal{F}, P)$ is formalized with `[IsProbabilityMeasure P]` and `AEMeasurable W P` (or `Integrable W P` / `HasLaw W μ P`, which entail `AEMeasurable`) so `P.map W` is a genuine probability measure rather than Lean's non-measurable fallback `0`.
  2. **$\mathcal{P}_1(\mathbb{R})$ finite first moment for real `sSup` Wasserstein bounds (`FINDING-006`)**: In `Prop1_2_2` and `Thm3_1`, `Integrable W P` (and `Integrable Z P'` in `Prop1_2_2`) is required so `wassersteinDist` does not collapse to Lean's `¬ BddAbove` junk value `0` on heavy-tailed laws.
  3. **Left-derivative Stein operator at corners (`FINDING-002`, `FINDING-007`)**: Following Chen–Goldstein–Shao (2011, p. 15), `normalSteinOpLeft` uses `derivWithin f (Set.Iic x) x`, which agrees with `normalSteinOp` wherever `f` is differentiable while making `Lem2_2`, `Cor2_3`, and `Prop2_4` hold pointwise at every $w \in \mathbb{R}$ (including the jump point $w = x$ of $\mathbf{1}_{(-\infty, x]}$) for arbitrary discrete or continuous $W$, with explicit integrability and left-continuity hypotheses on $\mathcal{H}$ in `Prop2_4`.
  4. **Explicit boundedness witnesses for `sSup` norms & $C^2$ Wasserstein test class (`FINDING-004`, `FINDING-008`)**: Supremum norms $\|g\| := \sup_x |g(x)|$ on `ℝ` are accompanied by explicit boundedness (`AEStronglyMeasurable h volume` and `∃ B, ∀ t, |h t| ≤ B` in `Lem2_5_1`; `∃ B, ∀ t, |deriv h t| ≤ B` in `Lem2_5_2`; boundedness of $f, f'$ in `Lem3_3` and $f, f', f''$ with `Differentiable ℝ f` and `Differentiable ℝ (deriv f)` in `Lem3_4`, and `0 < n` for nonempty summands $X_1, \ldots, X_n$); and `normalWassersteinClass` in `Thm3_1` requires `ContDiff ℝ 2 f` (strengthening `Thm3_1` and preventing Cantor-function junk second derivatives).

---

## `RULING-USER-2026-11-11` — User rulings D1–D12 (supersede `AUTONOMOUS_PREAUTH_V1`)

* **Approved By**: Repository owner (aaradhyapandey), in the Claude Code chat on 2026-11-11, replying "Accept all" to the recommendations in [`docs/reviews/review-00-setup.md`](reviews/review-00-setup.md) § "Decisions needed from the user".
* **Recorded By**: Claude (critic/lead). This entry quotes the decisions exactly. Implementation details marked "spec" are the critic's rendering, and the critic reviews the builder's code against them.
* **Effect on earlier rulings**:
  * `AUTONOMOUS_PREAUTH_V1` is **revoked**. It is not a valid approver for anything, past or future.
  * `RULING-SPLIT-ENUM-001` and `RULING-TOTALITY-WAVE1` are **superseded** by D1–D9 below.
  * `RULING-SETUP-001` is amended by D11: the namespace is `SteinMethod`, not `SteinsMethod`.

### Definitions

* **D1 Metric codomain.** Every probability metric is `ℝ≥0∞`-valued. Spec:
  `ipm H μ ν := ⨆ h ∈ H, ⨆ (_ : Integrable h μ ∧ Integrable h ν), ENNReal.ofReal |∫ x, h x ∂μ - ∫ x, h x ∂ν|`.
  * `kolmogorovDist` uses `{h | ∃ x, h = (Set.Iic x).indicator 1}`.
  * `wassersteinDist` uses `{h : ℝ → ℝ | LipschitzWith 1 h}`.
  * `tvDist` uses `{h | ∃ A, MeasurableSet A ∧ h = A.indicator 1}`.
  * Suprema on the right-hand side of Prop 2.4 and Theorem 3.1 are also `ℝ≥0∞` suprema of `ENNReal.ofReal |…|`.
  * No moment hypothesis may be added where the source says "any random variable". Real-valued corollaries are derived via `toReal` under a first moment.
* **D2 Signatures.** Metrics are defined on measures. Statements about random variables use `P.map W` with `[IsProbabilityMeasure P]` and `AEMeasurable W P` (the typing of "random variable"), or `HasLaw`.
* **D3 TV carrier.** `tvDist` is generic over `{α} [MeasurableSpace α]`. The discrete formula ½∑|·| is Proposition 1.2(3).
* **D4 Normal Stein operator.** `normalSteinOp f w := deriv f w - w * f w` stays the operator.
  * Lemma 2.2, Corollary 2.3, Theorem 3.24 and Lemma 3.25 get `_corrected` entries that use the left derivative `derivWithin f (Set.Iic w) w`, each with a SOURCE-ISSUES record (counterexample W ≡ x).
  * Corollary 2.3 gets **no** `Integrable W P`, because |w f_x(w)| ≤ 1. Theorem 3.24 keeps its printed "finite mean".
  * Proposition 2.4 is stated literally, for a family `f h` with `∀ w, HasDerivAt (f h) (w * f h w + h w - Φ h) w`. No left-continuity hypothesis is allowed.
* **D5 Absolute continuity.** "Absolutely continuous" means `∀ a b, AbsolutelyContinuousOnInterval f a b`, with f' = `deriv f`; E|f'(Z)| < ∞ is `Integrable (deriv f) (gaussianReal 0 1)`. Lemma 2.1(2) is stated as printed, with Z := N(0,1) and only `AEMeasurable W P`. It gets no `_corrected` variant.
* **D6 Class 𝓕 in Theorem 3.1.** The index entry uses the literal class `Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧ (∀ w, |f w| ≤ 2) ∧ (∀ w, |deriv f w| ≤ √(2/π)) ∧ (∀ w, |deriv (deriv f) w| ≤ 2)`. The library may prove the theorem for a `ContDiff ℝ 2` subclass and derive the literal version.
* **D7 Stein pair.** `IsSteinPair` is as printed: exchangeable, `0 < a ∧ a ≤ 1`, `Measurable W`, `Integrable W P`, and `P[W' | MeasurableSpace.comap W inferInstance] =ᵐ[P] fun ω ↦ (1 - a) * W ω`. Library theorems (Prop 3.6(2), Theorems 3.7, 3.28, 7.2) are proved for any `0 < a`. Example 7.5 at n = 2 (a = 2) is recorded in SOURCE-ISSUES.
* **D8 Size bias.** Literal definition: `0 ≤ᵐ[P] X`, `Integrable X P`, and for all measurable f with `Integrable (fun ω ↦ X ω * f (X ω)) P`, `∫ X f(X) ∂P = (∫ X ∂P) * ∫ f(Xs) ∂P'`. μ = 0 is allowed. Proposition 3.11 (density x/μ) is `_restricted` to μ > 0, with a SOURCE-ISSUES record.
* **D9 Zero bias.** The builder first verifies critic finding H4: zero-bias existence fails when E|W|³ = ∞, e.g. f(w) = sin(w²)·1{w>0}.
  * If H4 is confirmed: `IsZeroBias` quantifies over locally AC f for which both `Integrable (fun ω ↦ W ω * f (W ω)) P` and `Integrable (fun ω ↦ deriv f (Wz ω)) P'` hold. This is recorded as a source-issue correction. Proposition 3.19 additionally needs σ² > 0 (ISSUE-3.19).
  * If H4 is refuted: the builder writes up the refutation for critic review and uses the literal class.

### Governance

* **D10.** All 22 entries of `frozen-anchor-manifest.json` are unapproved. The frozen-anchor workflow is retired in favour of the AGENTS.md statement index (`Formalization/Statements/SecN.lean` + `SecNProofs.lean`).
* **D11.** The `SteinsMethod/` library (with its 14 `sorry`), `SteinsMethod.lean`, the `SteinsMethod` `lean_lib`, the manifest, `DEPGRAPH*.md` and the frozen-anchor scripts and tests move to the branch `archive/steinsmethod-v0`, then leave `main`. Proofs may later be harvested into `Formalization/` under D1–D9. `SteinMethod` is the only namespace.
* **D12.** The arXiv TeX and `.bbl` are removed from git history.
  * **Done 2026-11-11 by the critic.** `main` was rewritten from `fa10cfb`/`d626e27` to `d115c4f`/`acce57a`: same messages, authors and dates, minus `docs/source/*`.
  * The files stay on disk under the new `.gitignore` rule `/docs/source/`.
  * A pre-rewrite git bundle is kept outside the repository by the critic.
  * Before the first push, run `git reflog expire --expire=now --all && git gc --prune=now` so the old objects are gone locally too.

### Website

* **R1. Paper text on the website.** Approved by the repository owner (aaradhyapandey) in the Claude Code chat on 2026-11-11, with the reply "Yes, with attribution". The reader site may render Ross's text, as the RL site does.
  * Basis: the IMS *Probability Surveys* page states "All works in this journal are licensed under a Creative Commons Attribution 4.0 International License" (checked 2026-11-11).
  * Conditions:
    1. The site builds the text from the arXiv e-print fetched and hash-verified at build time. The TeX itself stays out of git (D12).
    2. Every page carries CC BY 4.0 attribution: N. Ross, "Fundamentals of Stein's method", *Probability Surveys* 8 (2011) 210–293, DOI 10.1214/11-PS182, licensed CC BY 4.0; text rendered from arXiv:1109.1880v1. It links the licence and notes the rendering is unofficial and may differ from the published version.
    3. A fidelity check against the pinned PDF runs before deploy, as in the RL project.
* **R2. Repository name.** The repository owner (aaradhyapandey) approved it in the Claude Code chat on 2026-11-11 with the reply "Yes, use that". The public repository will be `aaradhyapandeycs/steins-method-lean`, and the site will be `https://aaradhyapandeycs.github.io/steins-method-lean/`.
  * On 2026-11-11 the name was still unused under the account.
  * Approving the name does not approve publishing. The first push still needs:
    * the `lean-public-release` checks to pass;
    * the D12 reflog/gc step;
    * the README and site to state the incomplete status prominently;
    * the owner's go-ahead for that push.

### Process

* **P1. Parallel builder agents.** The repository owner asked for this in the Claude Code chat on 2026-11-11: "make it write more lines by asking it to use as many agents and sub agents to parallize the task".
  * From Batch 5, the builder runs parallel tracks (docs/PARALLEL.md, AGENTS.md rules 7, 8, 10). Each track owns a disjoint set of files, and the lead alone integrates the shared files.
  * At most two Lean processes run machine-wide at once, through `scripts/lean-slot.sh`. This keeps the owner's earlier heat limit (2026-11-07, two jobs) and fits 16 GB of RAM.
  * The critic interprets "more lines" as more accepted results per hour. Line count is reported but never targeted, and padding is rejected in review.
* **R3. Early public release.** The repository owner (aaradhyapandey) approved it in the Claude Code chat on 2026-11-11 with the reply "Yes, early release".
  * The repository and reader site go public before the formalization is complete. They show a prominent "work in progress" status, as the RL project does.
  * The public repository is a maintained mirror with a fresh history. It is produced from committed revisions by `scripts/export_public.py`, using an allowlist, a scrub and a lint. The development history stays private.
  * Before anything is made public:
    * the critic reviews Track W;
    * the exported tree builds from a fresh checkout;
    * the owner sees the README and the planned actions (create the repository privately, push, CI green, then make it public and enable Pages) and gives a final go-ahead.
