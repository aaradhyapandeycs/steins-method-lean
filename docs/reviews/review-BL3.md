# Critic review BL3: Example 3.6, printed bound for every n ≥ 1, `6ba1edd`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1053–1097, the printed bound at L1089. The statement review was stmts-review-F2-BL3 (BL3-1, BL3-2).

## Verdict

**ACCEPTED.** `Ex3_6_printed` is recorded in COVERAGE. This brings the total to 88 entries. Example 3.6 was already counted, so the numbered count stays at 65/122. The printed bound of Example 3.6 now holds literally for every n ≥ 1, and the "n < 16 open" gap is closed.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `f395dee`, on a clean Lean tree with no uncommitted Lean changes.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3446 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 2331 project declarations.` |
| Re-elaboration: `Leftovers/Ex36SmallNHelper`, `Leftovers/Ex36SmallN`, committed `Statements/Sec3`, `Sec3Proofs` | 4/4 rc=0, 0 errors |
| Wrapper identity `example : Ex3_6_printed := Ex3_6_printed_holds` | type-checks |
| Axiom probe: `Ex3_6_printed_holds`, `indepSum_wassersteinDist_le_ex3_6_printed` | both `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the second term's coefficient 2/(3n) changed to 2/(300n). This is false at n = 1 with Rademacher X: d_W = E\|\|Z\| − 1\| ≈ 0.535, against a mutated bound of about 0.406. | **rejected** (`CoefMut.lean:533`) |
| **Mutation 2:** in a scratch copy, one rational constant (151057/300000 → 151058/300000) changed in the polynomial certificate | **rejected** (`CertMut.lean:356`) |

## Statement

BL3-1 is applied. `Ex3_6_printed` is the intrinsic printed claim: independent X₁, …, Xₙ in L⁴ with mean 0 and variance 1, W = ΣXᵢ/√n, and d_W ≤ √(2/π)·√(ΣE Xᵢ⁴)/(2n) + (2/(3n))·ΣE\|Xᵢ\|³, for all n ≥ 1. The coupling (X′, I) is internal to the proof. The accepted `Ex3_6_corrected` (8/(3n^{3/2})) and `Ex3_6_restricted` stay.

BL3-2 is applied. ISSUE-3.6 now records three things:
- the printed inequality is **true** for every n;
- the L1073–1074 step omits a 1/n (class C, proof slip);
- the L1091 remark ("of order n^{−1/2}") is false for the printed bound, whose second term is at least 2/3 and does not decay. It is true for the corrected bound.
