# Critic review SWEEP-B (prose-claim sweep entries for §3.3–3.6), `51a6fb2`

- **Critic:** Claude, 2026-11-11.
- **Statement review:** stmts-review-SWEEP-B (SB-1 to SB-8 and the re-review).

## Verdict

**ACCEPTED.** 4 new entries are recorded in COVERAGE, bringing the total to 193:

| Entry | TeX | Content |
|---|---|---|
| `Sec3_3_eq3_18` | L1043–1046 | display (3.18), function level; cubic term ‖f″‖·E\|W′−W\|³/(6a) as an ℝ≥0∞ lintegral |
| `Sec3_3_eq3_18_wasserstein` | — | its d_W form, with coefficient 1/(3a) |
| `Sec3_3_1_antiVoter_not_reversible` | L1130–1131 | there is a stationary law, and **every** stationary law violates detailed balance |
| `Sec3_5_identDistrib_of_integral_deriv_compactSupport` | L1512–1513 | — |

## Independent verification

The commands ran at `b58ce75` with `.locks/CRITIC-HOLD` set.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3541 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 5554 project declarations.` |
| Re-elaboration: `Sweep/SweepB{,AntiVoter,SteinPair,ZeroBias}`, committed `Statements/Sec3`, `Sec3Proofs` | 6/6 rc=0 |
| Axiom probe: the 4 wrappers | 4/4 `[propext, Classical.choice, Quot.sound]` (one multi-line output, parsed) |
| **Mutation 1:** in a scratch copy, the cubic error term of (3.18) dropped. This is false: a pair can satisfy E[(W′−W)² \| W] = 2a without W being normal. | **rejected** |
| **Mutation 2:** in a scratch copy, "not reversible" flipped to "detailed balance holds" | **rejected** |
