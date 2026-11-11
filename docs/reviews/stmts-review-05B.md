# Statement review: Track B (§3.6 Kolmogorov metric), drafts at `4f90e13`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1649–1815, re-read in full.
- **Scope:** statements only. Nothing is accepted into COVERAGE until the track's batch passes the full review.

## Verdict

The drafts are **approved with three required changes (B1–B3)**. Keep proving.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `Thm3_24_corrected` | 1666–1675 | No bounded two-sided solution exists (ISSUE-2.2, accepted). With the left derivative, the equation holds at w = x with value 1 − Φ(x), so the equality with d_K is exact. `Integrable W` keeps the printed finite-mean hypothesis. | correction accepted (same pattern as `Cor2_3_corrected`) |
| `Lem3_25_corrected` | 1677–1686 | ‖f_x‖ ≤ √(π/2) is true; the sharp value is √(2π)/4. \|D₋f_x\| ≤ 2 is true; the sharp value is 1. The third inequality is CGS11 Lemma 2.3. | correction accepted (left derivative) |
| `Cor3_26` | 1688–1694 | `normalKolmogorovClass` requires differentiability, so f_x ∉ F. The entry is still true, and stronger: smoothing the indicator with a ramp gives f_h = ε⁻¹∫ f_s ds, and the Lemma 3.25 bounds are convex constraints, so averaging preserves them. Then let ε → 0. | matches under the reading in B3 |
| `Thm3_27` | 1697–1704 | I re-derived the constant. (3.40) gives δ/√(2π). (3.42) uses the third inequality with (w, u, v) = (W, 0, Wᶻ − W) and E\|W\| ≤ 1, giving δ(1 + √(2π)/4). Applying Cor 3.26 to Wᶻ needs Wᶻ integrable, which follows from \|Wᶻ\| ≤ \|W\| + δ. | matches |
| `Thm3_28` | 1750–1755 | `IsSteinPair` includes `Measurable W`, so the conditional expectation is not junk. `variance W P = 1` forces W ∈ L². δ³/(2a) follows from (1 + √(2π)/4)/4 ≤ 1/2, and 3δ/2 from Lemma 3.29. | matches |
| `Lem3_29` | 1793–1798 | The integrand is bounded. I checked the proof: ‖g‖ ≤ 3δ/2 and E\|W\| ≤ 1. | matches |

The **ISSUE-3.25 proof note** is confirmed. To get √Var(·)/(2a) at L1768, the term (3.43) needs \|f_x′\| ≤ 1 (CGS11 Lemma 2.3); the printed ‖f_x′‖ ≤ 2 would give √Var/a. The theorem is true as printed, so record this as a proof note, not an error. **ISSUE-TYPO-3.27** at L1741 is plausible: `\ref{thm91}` points to Thm 3.24, while the parenthetical about Wᶻ points to the unlabeled Thm 3.27. It is accepted as a likely typo. The status lines for L1741–1743 (exercise) and L1810–1812 (qualitative remark) are accepted.

## Required changes

- **B1. Missed prose claim, L1655–1657.** "If W is a standardized binomial random variable with parameters n and p, then both d_K(W, Z) and d_W(W, Z) are of order n^{−1/2}." This is a substantive two-sided claim, and the reason the section exists. Add it as `Sec3_6_binomial_order`: for fixed 0 < p < 1 there are c, C > 0 with c n^{−1/2} ≤ d(W_n, Z) ≤ C n^{−1/2} for d ∈ {d_K, d_W}, for all n ≥ 1, or all large n with a reading note. Routes:
  - Upper bounds: Thm 3.2 for d_W, and Thm 3.27 for d_K. For bounded summands the zero-bias coupling of Prop 3.21 gives \|Wᶻ − W\| ≤ 1/σ_n, with σ_n = √(np(1 − p)), and that needs Track A's Prop 3.21. Alternatively use Thm 3.28 with the coordinate-resampling Stein pair.
  - Lower bound for d_K: the atom size of the lattice, P(W_n = k) ≳ n^{−1/2} for the central k.
  - Lower bound for d_W: test against the 1-Lipschitz function h(x) = dist(x, lattice), which has E h(W_n) = 0 and E h(Z) ≈ s/4, with lattice span s = 1/σ_n.
  - If this is too heavy for now, record it under Deferred with that reason. Do not drop it.
- **B2. Write out the `Sec3_6_zeroBias_bdd_restricted` draft.** The track file names it as "optional", but it is a prose claim (L1741–1742), so it needs a full Lean draft in the track file:
  - Hypotheses: Var W > 0 and \|W\| ≤ M a.s.
  - Conclusion: \|Wᶻ\| ≤ M a.s. for every zero-bias Wᶻ.
  - The proof is the density support: p^z vanishes off [−M, M].
  - Also add the existence reading, which holds without the variance condition: some zero-bias version is bounded. With σ² = 0 take Wᶻ ≡ 0.
- **B3. Docstring reading notes.**
  - `Cor3_26`: F is read as the *differentiable* functions satisfying Lemma 3.25's bounds. This excludes f_x itself and gives a smaller supremum, so the entry implies every weaker-regularity reading. Say briefly that the proof smooths the indicator.
  - `Thm3_28`: point to the ISSUE-3.25 proof note.

## Coordination note for the lead

The d_K upper bound in B1 can reuse Track A's `Prop3_21` once it lands. Do not reprove the zero-bias construction in Track B.
