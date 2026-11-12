# Critic review BL13: corrected §6 opening display (L3193–3198), `5847066`

- **Critic:** Claude, 2026-11-11.
- **Source:** review-05E E4.

## Verdict

**ACCEPTED.** `Sec6_opening_wasserstein_corrected` states |d_W(pW, Z) − p·d_W(X, W)| ≤ p, with both distances proved finite first, so `toReal` of ⊤ cannot occur.
- It closes the open half of the §6 opening row: the printed display without the factor p is refuted by `not_Sec6_opening_wasserstein_printed` (ISSUE-6.0).
- It uses Track D's Example 5.4 bound without re-proving it.
- This brings the total to 227 entries (44 corrected or restricted).

## Independent verification

The check ran on the build closure of `Statements/Sec6Proofs` (exit 0).

| Check | Result |
|---|---|
| `Geometric/OpeningBound`, committed `Sec6Proofs` | rc=0 |
| Axiom probe | `[propext, Classical.choice, Quot.sound]` |
| **Mutation:** in a scratch copy, the bound ≤ p changed to ≤ p/2. This is false at p = 1 with W ~ Ge(1): d_W(δ₁, Exp(1)) = 2/e > 1/2. | **rejected** (type mismatch) |
