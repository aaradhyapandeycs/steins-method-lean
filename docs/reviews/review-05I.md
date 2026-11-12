# Critic review 05I: §5.3 critical branching, Yaglom's Theorem 5.8 and Theorem 5.9 (Track I), `8b1e69f`

- **Critic:** Claude, 2026-11-11.
- **Statement review:** stmts-review-05I (I-1 to I-10).

## Verdict

**ACCEPTED.** 25 new entries are recorded in COVERAGE, bringing the total to 226 (43 corrected or restricted). Theorems 5.8 and 5.9 are covered as restricted results, which makes 121 of 122 numbered results.

- **`Thm5_8_restricted`** (Yaglom, L3007–3013) is the printed normalization: d_K(2Yₙ/(nσ²), Exp(1)) → 0, where Yₙ ~ L(Zₙ | Zₙ > 0).
  - The restriction σ² > 0 is disclosed (ISSUE-5.8). The printed statement is ill-defined at σ² = 0, not false.
  - The conditioning event has positive probability.
- **`Thm5_9_restricted`** (L3015–3020): ∃C ∀n ≥ 2, d_W ≤ C·log n/n under a finite third moment.
  - n ≥ 2 is required because the printed bound fails at n = 1 (`not_Thm5_9_printed`, ISSUE-5.9).
  - The proof does not use the gap in the source: ISSUE-5.9-PROOF-MEAN records that the printed proof applies Theorem 5.4 without E W = 1, while the library uses a |1 − E W| penalty.
- **23 further entries** for §5.3's displays, items and proof steps:
  - eqs (5.10)–(5.12);
  - items 1–4;
  - spine coupling, extinction and survival asymptotics;
  - the corrected L3143 and L3158–3160 steps.

An independent pass confirmed:
- I-1 to I-10 are all applied;
- every entry is faithful, with no junk-value traps;
- every wrapper applies a library theorem;
- the source issues ISSUE-TYPO-5.3a to 5.3d, ISSUE-5.8, ISSUE-5.9, ISSUE-5.9-PROOF and ISSUE-5.9-PROOF-MEAN are quoted verbatim.

## Independent verification

The commands ran at `e660dfe` with `.locks/CRITIC-HOLD` set.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3555 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 6612 project declarations.` |
| Re-elaboration: `Defs/Branching`, `Branching/{AuxSpine, Basic, Extinction, SizeBiasTree, YaglomRate}`, committed `Statements/Sec5`, `Sec5Proofs` | 8/8 rc=0 |
| Axiom probe: the 25 wrappers | 25/25 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the Yaglom normalization 2Yₙ/(nσ²) changed to 3Yₙ/(nσ²). This is false: the limit would be Exp(2/3), not Exp(1). | **rejected** (type mismatch) |
| **Mutation 2:** in a scratch copy, the Thm 5.9 rate log n/n changed to 1/n² | **rejected** (linarith) |

## Follow-ups (Track I, non-blocking)

1. `Sec5_3_exists_isSizeBiasSpineCoupling` ends with the tautology `1 ≤ 1 + Σ…`. Drop it, together with the docstring claim that it witnesses the infinite spine at L3043–3044.
2. Unify the issue ID: docstrings cite `ISSUE-5.9-proof`, but the ledger has `ISSUE-5.9-PROOF`.
3. Add L3024 ("for any constant c") to the ISSUE-5.4 entry.
4. Name the printed-statement refutations (`not_Thm5_8_printed`, `not_Thm5_9_printed`) in the restricted docstrings.
5. Do not commit the untracked `Branching/Aux*.lean` files: their names collide with YaglomRate.
