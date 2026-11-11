# Plan and statement review: Track J (Theorem 1.1, Berry–Esseen with constant 1.88), drafts at `c80d346`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L347–365 (the theorem is at L351–357).
- **Scope:** the statement and the proof route only. Nothing is accepted into COVERAGE until the batch passes the full review.

## Verdict

The **statement is approved, and the route is approved to proceed to Lean.** Two small changes are required (J1–J2).

### Statement `Thm1_1`
- It matches L351–357: i.i.d. through `iIndepFun` plus `IdentDistrib` with `X 0`, E\|X₁\|³ < ∞ as `MemLp 3`, mean 0, variance 1, and the bound for every x.
- `0 < n` is typing: at n = 0 the junk value 0/0 would make the statement false.
- The right-hand side is a genuine Bochner integral, because `MemLp 3` holds.
- The `kolmogorovDist` corollary is fine as an extra.

### Route C constant budget: re-derived independently
I re-derived each step by hand and re-ran the numbers.

| Step | Check | Result |
|---|---|---|
| ρ ≥ 1 | (\|x\| − 1)²(2\|x\| + 1) ≥ 0 | correct |
| Cantelli: P(Y ≥ y) ≤ 1/(1 + y²) | expand E[(Y + 1/y)²] | correct |
| Universal bound \|P(W ≤ x) − Φ(x)\| ≤ 11/20 | numerically, max over x > 0 of Φ(x) − 1 + 1/(1 + x²) is 0.5409 | correct, but see J1 for the algebra |
| Regime 1 (β ≥ 3/10) | 0.55 ≤ 1.88 · 0.3 = 0.564 | correct |
| n ≥ 12 in regime 2 | √n > ρ/0.3 ≥ 10/3 | correct |
| Fejér kernel | (1/2π)∫_{−T}^{T}(1 − \|t\|/T)e^{ity} dt = (1 − cos Ty)/(πTy²) | correct |
| α(16/5) lower bound | cos u ≤ 1 − u²/2 + u⁴/24 − u⁶/720 + u⁸/40320 for all u. α_low = 2·1.2259220/3.1416 = 0.780444, against a true α(3.2) ≈ 0.781090 by quadrature. | correct |
| Smoothing inequality | For y ∈ (−r, r), F is monotone and 0 ≤ Φ′ ≤ (2π)^{−1/2}, and ∫_{−r}^{r} y k_T = 0. This gives (2α − 1)Δ ≤ sup\|G_T\| + αr/√(2π). The case G(x) < 0 is symmetric. | correct |
| G_T as a Fourier integral | Fubini on ℝ × [−T, T] with G ∈ L¹ (finite first moments), so \|Ĝ(t)\| = \|φ_W(t) − e^{−t²/2}\|/\|t\| | correct |
| Characteristic-function bounds on [0, T], T = 7/(5β) | u ≤ 1.4/ρ ≤ 1.4, so 1 − u²/2 > 0. Then 1 − ρu/3 ≥ 8/15, so \|φ_X(u)\| ≤ e^{−4u²/15}. The telescoping bound with (n − 1)/n ≥ 11/12 gives a = 11/45. Also 1/(ρ√n) ≤ β. | correct |
| Gaussian moments and the final tally | I = 0.924866 (the two sub-terms are 0.611070 + 0.313795; the track file's split, 0.610498 + 0.314368, is slightly off, but the sum is right). c₁I = 0.524886, c₂/κ = 1.268831. | **total 1.793717 < 1.88** |

## Required changes

- **J1. Fix the regime-1 algebra.** The track file claims −(3x − 1)² − 4x² = −13x² + 8x − 1. It is actually −13x² + 6x − 1, and −13x² + 8x − 1 is **positive** on (0.175, 0.441). The inequality you need, 8x³ − 21x² + 8x − 1 ≤ 0 on [0, 1], is still true (its maximum is −0.171). A valid certificate splits at x = 5/8:
  - On [0, 5/8]: 8x ≤ 16x² + 1 gives the cubic ≤ x²(8x − 5) ≤ 0.
  - On [5/8, 1]: x³ ≤ x² gives the cubic ≤ −13x² + 8x − 1. That is decreasing for x ≥ 4/13, and its value at x = 5/8 is −69/64 < 0.

  Correct the track file. Expect `nlinarith` to need this split.
- **J2. Soften the history in reading note 6.** Do not write that Berry (1941) "proved 1.88"; the literature reports that Berry's numerical constant was flawed. Say only that Theorem 1.1 is true as printed because sharper constants are known (e.g. Shevtsova 2011, 0.4748), and that this formalization proves 1.88 from scratch by its own route (M10). No source issue is needed.

## Notes

- Route C is a genuinely self-contained proof. It does not use the paper's Stein-method bounds; the track's explanation of why routes A and B cannot reach 1.88 is correct. Record in COVERAGE (when it lands) that the proof is from scratch, not the source's argument, because the source only cites [ber41].
- `Formalization/BerryEsseen/**` stays out of `Formalization.lean` until it is sorry-free.
