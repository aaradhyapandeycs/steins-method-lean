# Critic review 05G4: §4.3.4 negatively related indicators (Track G4 + G4b, L2453–2605), `4eed084`

- **Critic:** Claude, 2026-11-11.
- **Reviews:** stmts-review-G4-BL7 (G4-1 to G4-8) and prereview-G1-G3 (BL-1).

## Verdict

**ACCEPTED.** 15 new entries are recorded in COVERAGE, bringing the total to 189 (34 corrected or restricted). §4.3.4's numbered items (Thm 4.19, Ex 4.13, Rem 4.14, Ex 4.15, Ex 4.16, Rem 4.17) are covered, which makes 117 of 122 numbered results.

## Independent verification

The commands ran at `cc70bca` with `.locks/CRITIC-HOLD` set.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3537 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 5506 project declarations.` |
| Re-elaboration: `PoissonSizeBias/Negative/{Defs, Basic, CouponNonUniform, CouponUniform, Ex416Coupling, Hypergeometric, Occupancy, Rem417Coupling}`, committed `Statements/Sec4`, `Sec4Proofs` | 12/12 rc=0 (including the two HEAD copies) |
| Axiom probe: the 15 wrappers plus `not_rem4_17_atLeast_printed` and `not_ex4_13_var_printed` | 17/17 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the corrected Ex 4.13 variance factor (N − m) reverted to the printed (n − m) | **rejected** |
| **Mutation 2:** in a scratch copy, the Rem 4.17 decreasing coupling Y ≤ X flipped to X ≤ Y | **rejected** |

## Statements

An independent pass confirmed:
- G4-1 to G4-8 and BL-1 are all applied;
- no N = 1 junk refutation remains;
- `Ex4_16_sizeBias` is present, with its pᵢ < 1 guard;
- both Rem 4.17 entries carry the decreasing-coupling conjuncts;
- the (4.13) identity is stated;
- ISSUE-4.16 is scoped to k ≠ log λ;
- `Thm4_19` concludes `IsSizeBias`;
- the SOURCE-ISSUES quotes are verbatim.

## Low-priority follow-ups (G4)

1. `Ex4_16_restricted` docstring: add "the printed bound is true wherever defined; not a source error".
2. State the (4.13) identity for n ≥ 2, not only n ≥ 3, and drop the redundant `0 < n(n−2)`.
3. Add a status line for the "exactly m balls" clause at L2600.
4. ISSUE-REM-4.17: name the parameters (k = 1, m = 1, uniform p) behind the "−1/3 at n = 3" figure.
