# Critic review 05B: Track B (§3.6 normal approximation in the Kolmogorov metric), `c08be90`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1649–1815, re-read for the statement review (stmts-review-05B).

## Verdict

**ACCEPTED.** 7 new statement entries are recorded in COVERAGE, bringing the total to 52 (11 corrected or restricted). There are no blocking findings.

## Independent verification

The commands ran in the development checkout with `.locks/CRITIC-HOLD` set and all builder slots drained. The Lean tree is identical to `c08be90`; the only later commit, `aa7f2cd`, is docs only.

| Check | Result |
|---|---|
| `lake build` | exit 0, `Build completed successfully (3322 jobs)` |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 1374 project declarations.` |
| `python3 scripts/check.py` | exit 0, forbidden-token and statement-wrapper checks pass |
| Per-file re-elaboration: `Defs/Kolmogorov`, `Kolmogorov/{Basic, SolutionBounds, ZeroBiasBound, ExchangeableBound}`, `Statements/Sec3`, `Sec3Proofs` | 7/7 rc=0, 0 warnings, 0 errors, 12–74 s |
| Wrapper identity (`example : Thm3_24_corrected := Thm3_24_corrected_holds`, and the same for all 7 entries) | type-checks |
| Axiom probe: the 7 `_holds` wrappers plus `abs_derivWithin_Iic_normalSteinSolKolm_le_one`, `zero_stdNormalLaw_isZeroBias_unbounded` and `exists_ne_zero_mem_normalKolmogorovClass` | all `[propext, Classical.choice, Quot.sound]` |
| Mutation 1: in a scratch copy, the Lemma 3.29 constant 3δa changed to 2δa | rejected (`ExchMut.lean:263`) |
| Mutation 2: in a scratch copy, the Lemma 3.25 constant √(2π)/4 changed to √(2π)/5 | rejected (`SolMut.lean:531`) |

The Lean side was also checked on the remote codespace build from a fresh tree. That run covered the state before Track B; this review's evidence is the local run.

## Statements

All 7 entries are the drafts approved in `stmts-review-05B.md`, with its required changes applied:
- **B2:** `Sec3_6_zeroBias_bdd_restricted` requires Var W > 0 and concludes \|Wᶻ\| ≤ M a.s. for every zero-bias Wᶻ. The σ² = 0 counterexample is machine-checked (`zero_stdNormalLaw_isZeroBias_unbounded`). The existence reading is reduced to Track A's `Prop3_19_corrected` and is wired when Track A lands.
- **B3:** the `Cor3_26` docstring carries the reading note on the differentiable class, and the `Thm3_28` docstring carries the ISSUE-3.25 proof note.

ISSUE-TYPO-3.27 is accepted. It covers L1741 (`\ref{thm91}`, where Thm 3.27 is meant) and L1775 (`\ref{91}`, the equation label, where Lemma `\ref{lem91}` is meant).

## Open from this track

- **B1, `Sec3_6_binomial_order`** (L1655–1657): deferred until Track A's `Prop3_21` lands. It is listed in BACKLOG item 1.
- **`Sec3_6_zeroBias_bdd_exists`**: wired with Track A (BACKLOG item 2).
