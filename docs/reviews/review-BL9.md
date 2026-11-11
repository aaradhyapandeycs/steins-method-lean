# Critic review BL9: Example 3.8 (size-bias bound for independent sums), `c2c18a3`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1349–1353 (Example 3.8, an exercise), together with Theorem 3.13 (L1255–1261) and Corollary 3.15 (L1319–1325). The statement review was stmts-review-BL5-BL9 (BL9-1).

## Verdict

**ACCEPTED.** `Ex3_8` is recorded in COVERAGE as the project's solution of the exercise. This brings the total to 75 entries and 57 of 122 numbered results.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `c2c18a3`.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3413 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 1896 project declarations.` |
| `python3 scripts/check.py` | exit 0 |
| Per-file re-elaboration: `Leftovers/Ex38IndepSum`, `Statements/Sec3`, `Sec3Proofs` | 3/3 rc=0, 0 warnings, 0 errors |
| Wrapper identity `example : Ex3_8 := Ex3_8_holds` | type-checks |
| Axiom probe: `Ex3_8_holds`, `sizeBias_indepSum_wassersteinDist_le` | both `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the 2/π in the first term changed to 1/π | **rejected** (`PiMut.lean:761`) |
| **Mutation 2:** in a scratch copy, the second term's μᵢ E Xᵢ² changed to 2μᵢ E Xᵢ² | **rejected** (`CubeMut.lean:761`) |

## Statement

The right-hand side is (1/σ²)·√((2/π)·Σμᵢ² Var Xᵢ) + σ⁻³·Σ(E Xᵢ³ − μᵢ E Xᵢ²). I re-derived it from Thm 3.13 with the coupling of Cor 3.15, taking each Xᵢˢ independent of everything.
- **First term.** E[Xˢ − X | X₁, …, Xₙ] = μ⁻¹Σ(E Xᵢ² − μᵢXᵢ), whose variance is μ⁻²Σμᵢ² Var Xᵢ. Conditioning on the larger σ-field is allowed by Remark 3.4, since Var(E[·|X]) ≥ Var(E[·|ΣXᵢ]).
- **Second term.** μ·E(Xˢ − X)² = Σμᵢ·E(Xᵢˢ − Xᵢ)² = Σ(E Xᵢ³ − μᵢ E Xᵢ²), which is ≥ 0.

**Hypotheses:**
- **Xᵢ ≥ 0 a.s.** comes from the setting of Cor 3.15 (BL9-1).
- **`MemLp 3`** is "finite third moment".
- **σ² > 0** is typing.

The BL9-1 reading notes are in the docstring.
