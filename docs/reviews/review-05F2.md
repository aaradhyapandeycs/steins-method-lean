# Critic review 05F2: Track F2 (§7.3 size-bias concentration), `6c9b695`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L3805–3887. The statement reviews were stmts-review-05F (ISSUE-7.6, F3) and stmts-review-F2-BL3.

## Verdict

**ACCEPTED.** 2 new statement entries are recorded in COVERAGE, both corrected, bringing the total to 110 (24 corrected or restricted). Theorem 7.6 and Example 7.6 are covered, which makes 77 of 122 numbered results.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `6c9b695`, on a clean Lean tree.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3469 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 3143 project declarations.` |
| Re-elaboration: `Concentration/SizeBias`, `Concentration/CircularRuns`, committed `Statements/Sec7`, `Sec7Proofs` | 4/4 rc=0, 0 errors |
| Wrapper identity for `Thm7_6_corrected` and `Ex7_6_corrected` | type-checks |
| Axiom probe: both wrappers, `not_sizeBias_tail_bounds_printed`, `Ex7_6_variance_counterexample` | 4/4 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the corrected variance factor 2·Σ changed back to the printed Σ. This is false at n = 4, k = 2, p = ½. | **rejected** (`VarMut.lean:671`) |
| **Mutation 2:** in a scratch copy, the coupling gap \|Xˢ − X\| ≤ 2k − 1 changed to ≤ k − 1. This is false at k = 1. | **rejected** (`GapMut.lean:671`) |

## Statements

- **`Thm7_6_corrected`** is Theorem 7.6 with the omitted t ≥ 0 hypothesis (ISSUE-7.6, `not_sizeBias_tail_bounds_printed`).
  - The lower tail needs Xˢ ≥ X. The upper tail needs E e^{(2/C)X} < ∞, written as `Integrable`.
  - C > 0 is derivable from σ² > 0, so 2/C is not a junk value.
- **`Ex7_6_corrected`** uses the true μ and σ throughout. It proves:
  - Xˢ is a size-bias coupling of X, with X ≤ Xˢ and \|Xˢ − X\| ≤ 2k − 1, for every n ≥ 1;
  - the mean formula np^k, for n ≥ k;
  - the corrected variance μ(1 − p^k + 2Σ_{r<k}(p^r − p^k)), for n ≥ 2k − 1. The printed formula lacks the 2 (ISSUE-EX7.6, `Ex7_6_variance_counterexample`);
  - the two-sided tail bound, for every t ≥ 0.

  This is the F3 structure.
