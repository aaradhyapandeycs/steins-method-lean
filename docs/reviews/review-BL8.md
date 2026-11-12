# Critic review BL8: Remark 3.5 O-U uniqueness (with BL8b semigroup lemmas), `0277ff8`

- **Critic:** Claude, 2026-11-11.
- **Statement review:** stmts-review-BL8 (BL8-1 to BL8-4).

## Verdict

**ACCEPTED.** `Rem3_5_uniqueness_restricted` is recorded in COVERAGE, bringing the total to 201 entries (37 corrected or restricted). Remark 3.5 is now covered as a **restricted** result rather than a partial one, which makes 119 of 122 numbered results with no partials.

The entry adds two hypotheses not literally printed:
- the Lindeberg second-moment tail, in place of Item 3's probability tail;
- small-time quadratic domination.

Under them it proves:
- **Part 1:** `ouKernel` satisfies Chapman–Kolmogorov, the Lindeberg tail and domination.
- **Part 2:** the generator on primitives of C_b¹ is `normalSteinOp`; any square-integrable law that is stationary for small a is N(0, 1).
- **Part 3:** with Chapman–Kolmogorov, K_t = ouKernel t for t > 0, and stationarity at any t₀ > 0 forces N(0, 1) with no moment hypothesis.

Whether the printed probability-tail form already suffices is an **open obligation** (BL8c is working on it).

An independent statement pass confirmed:
- **BL8-1:** the old "Part 4" kernel-family counterexample is removed; no source issue was filed;
- **BL8-2, BL8-3, BL8-4:** all applied;
- the wrapper is token-identical to the library theorem;
- the files contain no sorry or axiom.

## Independent verification

The commands ran at `e05b277` with `.locks/CRITIC-HOLD` set.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3548 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 5797 project declarations.` |
| Re-elaboration: `Leftovers/{OUSemigroup, OUUniquenessAux, OUUniqueness}`, committed `Statements/Sec3`, `Sec3Proofs` | 5/5 rc=0 |
| Axiom probe | `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the conclusion K_t = ouKernel t changed to K_t = ouKernel (2t) | **rejected** |
| **Mutation 2:** in a scratch copy, the stationary law N(0, 1) replaced by δ₀ | **rejected** |
