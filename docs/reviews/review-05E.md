# Critic review 05E: Track E (§6 geometric approximation), `a620991`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L3190–3388. The statement review was stmts-review-05E (E1–E4).

## Verdict

**ACCEPTED.** 9 new statement entries are recorded in COVERAGE, bringing the total to 74 (15 corrected or restricted). All 8 numbered §6 items are now covered (Lemmas 6.1–6.2, Theorem 6.3, Definition 6.1, Proposition 6.4, Remark 6.2, Theorems 6.5–6.6), which makes 56 of 122 numbered results. One documentation fix is required (E-R1).

## Independent verification

The commands ran in the development checkout with `.locks/CRITIC-HOLD` set, at `a620991`. The working tree also held the lead's uncommitted BL9 integration (`Leftovers/Ex38IndepSum`, `Statements/Sec3*`), so the build checked a superset.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3411 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 1869 project declarations.` |
| `python3 scripts/check.py` | exit 0 |
| Per-file re-elaboration: `Defs/Geometric`, `Geometric/{Basic, Equilibrium, OpeningBound, UniformAttachment}`, `Statements/Sec6`, `Sec6Proofs` | 7/7 rc=0, 0 warnings, 0 errors |
| Wrapper identity for all 9 entries (`example : E := E_holds`) | type-checks |
| Axiom probe: the 9 wrappers, plus `not_Sec6_opening_wasserstein_printed`, `not_unique_isDiscreteEquilibrium_one`, `isDiscreteEquilibrium_geomLaw_self`, `instIsProbabilityMeasureUniformAttachment`, `measurable_digraphOfTargets`, `uniformAttachment_adj`, `geomLaw_singleton` | 16/16 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the sharp Thm 6.6 bound (log n + 1)/n changed to (log n + 1)/(2n). At n = 1 this is false: W ≡ 1, so d_TV = 3/4 > 1/2. | **rejected** (`UAMut.lean:748`, type mismatch) |
| **Mutation 2:** in a scratch copy, the Lemma 6.2 bound −1 ≤ Δf_A changed to −1/2 ≤ Δf_A. This is false for A = {k+1, k+2, …}, where Δf_A(k) = −1. | **rejected** (`GeoMut.lean:494`) |

## Statements

The entries are the approved drafts, with E1–E4 applied.
- **E1:** the non-vacuity guards are present:
  - `geomLaw_singleton` and `posGeomLaw_singleton_of_pos` (point masses);
  - the probability-measure instances for `geomLaw`, `posGeomLaw` and `uniformAttachment`;
  - `measurable_digraphOfTargets`, so `Thm6_6`'s pushforward is not the junk zero measure;
  - the cylinder law `uniformAttachment_adj`;
  - the witness `isDiscreteEquilibrium_geomLaw_self`.
- **E2:** `Sec6_supportMismatch` gives the exact value of d_TV(kX, X) and its p → 0⁺ limit (k − 1)/k. At p = 1 the formula gives 0 for k = 1 and 1 for k ≥ 2, which are the true values.
- **E3:** the Remark 6.2 reading notes are in the docstring.
- **E4:** `Sec6_opening_wasserstein_corrected` is deferred until Track D's Example 5.4 lands. The refutation `not_Sec6_opening_wasserstein_printed` lands now.

**`Thm6_3`:** the library theorem needs neither the mean nor the integrability hypothesis; the wrapper drops them. This is fine: f_A is bounded, so choosing f = f_A ∈ F gives the bound with no moment condition. It is an export stronger than the printed statement, not a discrepancy.

**ISSUE-6.4 is a genuine boundary degeneracy, not junk.** At p = 1, E[W] = 0 forces W ≡ 0, so (6.1) reads 0 = 0 for every law of Wᵉ. Uniqueness therefore really fails (`not_unique_isDiscreteEquilibrium_one`), and the stationary-excess formula is 0/0 there.

## Required fix

- **E-R1 (lead, docs only).** The `ISSUE-6.0` counterexample in `docs/SOURCE-ISSUES.md` (L362) has the wrong arithmetic.
  - It says d_W(X, 4) = E|X − 4| = 2·27/16 = 27/8, with a difference "> 2".
  - For X ~ Ge(1/4) on {1, 2, …}: E|X − 4| = 2·Σ_{x≤3}(4 − x)(3/4)^{x−1}/4 = 2·81/64 = **81/32**. The difference is 81/32 − 2/e ≈ **1.80** > 1/4.
  - The Lean proof already uses 81/32 (`OpeningBound.lean` L580). Only the prose is wrong.
  - Fix it, and check that ERRATA-AND-DEVIATIONS and the site do not repeat 27/8.

## Accepted

- **Definitions:** `geomLaw`, `posGeomLaw`, `geomSteinOp`, `geomSteinSol`, `geomSteinClass`, `IsDiscreteEquilibrium`, the comap measurable space on `Digraph`, `digraphOfTargets`, `uniformAttachment`, `digraphInDegree`.
- **Source issues:** ISSUE-6.0 (subject to E-R1), ISSUE-6.4, ISSUE-TYPO-6.2, ISSUE-TYPO-6.6, the ISSUE-6.1 reading note, the ISSUE-6.6 proof note.
- **Refutations:** `not_Sec6_opening_wasserstein_printed`, `not_unique_isDiscreteEquilibrium_one`.

## Still open in §6

The corrected opening display (E4, which waits on Track D's Example 5.4).
