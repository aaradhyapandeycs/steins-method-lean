# Critic review 05H: Track H (§4.4 Poisson approximation via exchangeable pairs), `0ea2e40`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L2606–2711. The reviews were stmts-review-05H (H1–H4) and prereview-H (H-P1 to H-P6).

## Verdict

**ACCEPTED.** 12 new statement entries are recorded in COVERAGE, bringing the total to 122 (24 corrected or restricted). §4.4's 5 numbered items (Thm 4.20, Rem 4.18, Rem 4.19, Ex 4.20, Ex 4.21) are covered, which makes 82 of 122 numbered results.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `0ea2e40`, on a clean Lean tree.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3475 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 3338 project declarations.` |
| Re-elaboration: `Defs`, `Defs/PoissonExch`, `PoissonExch/{AuxLawSmallNumbers, Basic, FixedPoints, FixedPointsMoments, Thm420}`, committed `Statements/Sec4`, `Sec4Proofs` | 9/9 rc=0, 0 errors |
| Wrapper identity for all 12 entries | type-checks |
| Axiom probe: the 12 wrappers | 12/12 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the Ex 4.21 bound 4/n changed to 1/(4n). This is false at n = 2, where d_TV ≈ 0.448 > 1/8. | **rejected** (`RateMut.lean:492`) |
| **Mutation 2:** in a scratch copy, E[W²] = 2 changed to 3 | **rejected** (`MomMut.lean:256`) |

## Statements

The pre-integration check (prereview-H) found every entry faithful to its TeX and to its cited library theorem. H-P1 is applied: `Thm4_20_antisym` again requires f bounded.

The entries:
- **`Thm4_20`:** σ(W) ⊆ F; lintegral right-hand side; P(W′ = W − 1) is written as `W = W' + 1`, so there is no ℕ truncation.
- **`Rem4_18`, `Rem4_19`:** the latter covers detailed and global balance for Po(λ).
- **`Thm4_20_antisym`, `Thm4_20_identity`.**
- **`Ex4_20_coupling`, `Ex4_20`:** the bound 2·min{1, λ^{−1/2}}·Σpᵢ².
- **`Ex4_21_coupling`:** both transposition probabilities.
- **`Ex4_21_EW`, `Ex4_21_EW2`, `Ex4_21_EW2cycles`, `Ex4_21`:** the bound 4/n for n ≥ 2.

ISSUE-TYPO-4.20 is confirmed: L2645 is missing `\min`.
