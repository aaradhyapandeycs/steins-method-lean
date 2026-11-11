# Statement review: BL4 (§3.2.1, the literal d_K inequality), drafts in `docs/tracks/BL4.md`

- **Critic:** Claude, 2026-11-11.

## Verdict

`Sec3_2_1_triangles_kolmogorov_restricted` is **approved**: n ≥ 3 and 0 < p < 1, with the printed right-hand side and d_K on the left. There are two required changes.

### Numbers re-checked independently

Scanning p on a grid of 4,000 points:
- the first n with min_p R(n, p) < 1 is **n = 76**, where the minimum is about 0.99975 at p ≈ 0.8225;
- for n ≤ 45, T₂ ≥ 1.008 for all p;
- min_p R(100, p) ≈ 0.762, min_p R(200, p) ≈ 0.383, and min_p R(1000, p) ≈ 0.077.

So for n ≤ 75 the inequality is trivial (d_K ≤ 1 ≤ R). For n ≥ 76 it needs a genuine Kolmogorov bound.

## Required changes

- **BL4-1. Do not present the p ∈ {0, 1} case as a refutation of the printed claim.** At p ∈ {0, 1}, σ = 0, so the printed W = (T − E T)/σ and both right-hand-side terms are undefined. The printed statement is ill-posed there (class D, already recorded in ISSUE-3.2.1), not false. The "failure" of `Sec3_2_1_triangles_kolmogorov_printed` comes only from Lean's 0/0 = 0.
  - Drop `Sec3_2_1_triangles_kolmogorov_printed` and its negation.
  - Alternatively, keep a lemma named for what it shows: `Sec3_2_1_triangles_kolmogorov_boundary_illposed` ("with 0/0 = 0 the transcription fails at p = 0"), classified D.
- **BL4-2. Prove the large-n case in full, or defer it.** The proposed route for n ≥ 76 (coordinate-replacement Stein bound ≤ (31/32)·T₂) is a new argument. Numerics may guide it but cannot replace the proof.
  - Prove it for all n ≥ 76 and 0 < p < 1, or list the item under Deferred.
  - Do **not** narrow the entry to n ≤ 75 under the same name: that case is trivial and would misstate what the source claims.
