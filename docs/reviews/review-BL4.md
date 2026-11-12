# Critic review BL4: §3.2.1, the literal d_K inequality for triangle counts (L935–939), `aff69cd`

- **Critic:** Claude, 2026-11-11.
- **Statement review:** stmts-review-BL4 (BL4-1, BL4-2).

## Verdict

**ACCEPTED.** `Sec3_2_1_triangles_kolmogorov_restricted` is recorded in COVERAGE, bringing the total to 139 entries (27 corrected or restricted). It is a prose item, so the numbered count stays at 93/122.

The printed §3.2.1 bound, with **d_K** on the left (ISSUE-TYPO-3.2.1), now holds for every n ≥ 3 and 0 < p < 1:
- **n ≤ 75:** the right-hand side is ≥ 1, so the bound is trivial;
- **n ≥ 76:** it follows from a genuine Kolmogorov bound proved through an Efron–Stein and monotone-coupling route.

The restriction p ∈ (0, 1) is where the printed W is defined: σ = 0 at p ∈ {0, 1}, which is class D in ISSUE-3.2.1. BL4-1 is applied, so no "refutation" based on Lean's 0/0 is present.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `be6679c`. The working tree held other agents' in-progress edits (Track D's `Exponential/*` and `Statements/Sec5Proofs`, and BL13's `Geometric/OpeningBound`). So the full build and the audit failed **outside this batch**. The BL4 closure was checked directly.

| Check | Result |
|---|---|
| `lake build Formalization.Statements.Sec3Proofs` | exit 0 (3349 jobs) |
| Re-elaboration: `Leftovers/{MonotoneKolm, TrianglesEfronStein, TrianglesKolm}`, committed `Statements/Sec3`, `Sec3Proofs` | 5/5 rc=0 |
| Wrapper identity | type-checks |
| Axiom probe: wrapper, `erdosRenyi_triangles_kolmogorovDist_le` | both `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the variance coefficient 3(n − 3) changed to 2(n − 3) | **rejected** (`VarMut.lean:255`) |
| **Mutation 2:** in a scratch copy, the right-hand side multiplied by 0 (d_K ≤ 0, which is false) | **rejected** (`ZeroMut.lean:272`) |
