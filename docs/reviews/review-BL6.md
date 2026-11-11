# Critic review BL6: Example 4.21, true rate for permutation fixed points (prose, L2702–2703), `26351ea`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L2702–2706. The statement review was stmts-review-BL6 (BL6-1).

## Verdict

**ACCEPTED.** `Ex4_21_true_rate` is recorded in COVERAGE as the prose claim "the true rate of convergence is much better than order 1/n". This brings the total to 87 entries. Example 4.21 itself, the numbered environment, belongs to Track H, so the numbered count stays at 65/122.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `26351ea`. The working tree also held the lead's uncommitted BL3 integration (`Leftovers/Ex36SmallN*`, `Statements/Sec3*`), and the full build passed with it. The statement files were re-elaborated from their committed contents.

| Check | Result |
|---|---|
| `lake build` (full) | exit 0 (3446 jobs) |
| `lake build Formalization.Statements.Sec4Proofs` | exit 0 |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 2331 project declarations.` |
| Re-elaboration: `PoissonExch/FixedPointsTrueRate`, committed `Statements/Sec4`, `Sec4Proofs` | 3/3 rc=0, 0 errors |
| Wrapper identity `example : Ex4_21_true_rate := Ex4_21_true_rate_holds` | type-checks |
| Axiom probe: `Ex4_21_true_rate_holds`, `fixedPoints_true_rate`, `tvDist_fixedPoints_poissonLaw_le_two_pow_div_factorial` | all `[propext, Classical.choice, Quot.sound]` (one multi-line output, parsed) |
| **Mutation 1:** in a scratch copy, the bound 2ⁿ/(n+1)! changed to 2ⁿ/(n+2)!. This is false at n = 1: d_TV = 1 − e^{−1} ≈ 0.632 > 1/3. | **rejected** (`FactMut.lean:350`) |
| **Mutation 2:** in a scratch copy, the exact law's alternating sign (−1)ʲ changed to 1ʲ | **rejected** (`SignMut.lean:143`) |

## Statement

The entry is the approved draft, with BL6-1 applied: for every n, d_TV(L(Wₙ), Po(1)) ≤ 2ⁿ/(n+1)!, and n·d_TV → 0 in ℝ≥0∞. The law is `PMF.map` of the uniform permutation, so there is no measurability junk. L2703 ("not clear how to get a better rate with this method") and L2705–2706 (the i-cycles pointer) are status lines.
