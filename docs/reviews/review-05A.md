# Critic review 05A: Track A (§3.5 zero-bias coupling and Lindeberg–Feller), `6b7d565`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1437–1648. The statement review was stmts-review-05A (A1–A4).

## Verdict

**ACCEPTED.** 12 new statement entries are recorded in COVERAGE, bringing the total to 65 (14 corrected or restricted). The 6 numbered §3.5 results are now covered, which makes 48 of 122 numbered results.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set. The Lean files are unchanged since `6b7d565` (the later commits are docs and site only).

| Check | Result |
|---|---|
| `lake build` | exit 0 (3399 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 1602 project declarations.` |
| `python3 scripts/check.py` | exit 0 |
| Per-file re-elaboration: `Defs/ZeroBias`, `ZeroBias/{Basic, Coupling, Density, Lindeberg, LindebergFeller}`, `Statements/Sec3`, `Sec3Proofs` | 8/8 rc=0, 0 warnings, 0 errors |
| Wrapper identity for all 12 entries (`example : E := E_holds`) | type-checks |
| Axiom probe: the 12 wrappers plus `isZeroBias_stdNormal` and `not_Prop3_20_printed` | all `[propext, Classical.choice, Quot.sound]`; one multi-line output was parsed and checked |
| Mutation 1: in a scratch copy, the Thm 3.18 constant 2 changed to 3/2 | rejected (`BasicMut.lean:237`) |
| Mutation 2: in a scratch copy, the Lindeberg sandwich factor 2·P(…) changed to 1·P(…) | rejected (`LindMut.lean:341`) |

## Statements

The entries are the approved drafts, with A1–A4 applied:
- **A1:** `Sec3_5_2_lindeberg_sufficient` is the classical Lindeberg–Feller CLT for centred rows, with no zero-bias variables assumed.
- **A2:** `Sec3_5_2_zeroBias_imp_tendstoInMeasure` now also concludes max_i σ²_{i,n} → 0.
- **A3:** `Prop3_20` (existence reading, every a) and `Prop3_20_restricted` (law identity, with a ≠ 0 and σ² > 0) are both present, with `not_Prop3_20_printed`.
- **A4:** reading notes on the weaker independence hypotheses.

Track B's deferred existence reading, `Sec3_6_zeroBias_bdd_exists`, is wired here. It holds for every bounded mean-0 L² variable W, with σ² = 0 included.
