# Statement review: BL6 (Example 4.21 true rate, TeX L2702–2706)

- **Critic:** Claude, 2026-11-11.

## Verdict: approved, with one required change

`Ex4_21_true_rate` (n · d_TV(L(Wₙ), Po(1)) → 0 in ℝ≥0∞) is a faithful reading of "the true rate of convergence is much better than order 1/n" (L2702–2703).
- **Exact law.** P(Wₙ = k) = (1/k!)·Σ_{j≤n−k}(−1)ʲ/j!, from the derangement fibres. Re-derived.
- **Bound.** The sum of the |·| terms over k ≤ n is (2ⁿ⁺¹ − 1)/(n+1)!, and the tail is at most 1/(n+1)!, so d_TV ≤ 2ⁿ/(n+1)!. Re-derived and checked numerically:

  | n | d_TV | 2ⁿ/(n+1)! |
  |---|---|---|
  | 1 | 0.632 | 1 |
  | 3 | 0.237 | 0.333 |
  | 8 | 5.86e−4 | 7.05e−4 |

- **No junk values.** `PMF.map` needs no measurability. At n = 0 the law is δ₀. TV ≤ 1, so the ℝ≥0∞ product is never ⊤.

### Required change

- **BL6-1 (medium). Add the quantitative bound as a conjunct:** ∀ n, `tvDist (μW n) (poissonLaw 1) ≤ 2 ^ n / (n + 1)!` in ℝ≥0∞.
  - "Much better than order 1/n" is stronger than the o(1/n) limit alone.
  - The factorial bound is the "well known" content, and the proof derives it anyway.
  - Keep the limit conjunct.

### Status lines (no Lean entry)

- **L2703:** "it is not clear how to get a better rate with this method". A methodological remark, with no mathematical claim to formalize.
- **L2705–2706:** "the number of i-cycles … not worth pursuing … see [abt03]". A pointer, with no claim.

Proceed to the proof. Write `STATUS: READY` in `docs/tracks/BL6.md` when it is sorry-free.
