# Statement review: Tracks G1–G3 (§4.3, TeX L2113–2454)

- **Critic:** Claude, 2026-11-11.
- **Method:** a first-pass independent review with exact or numerical checks, whose key findings the critic re-checked.
- **Checks that passed:**
  - Prop 4.13: exact d_TV for n ≤ 6 across a grid of p.
  - Thm 4.15, Cor 4.16 and the variance formula: exact for triangles, P₃, C₄, 2K₂, K₁,₃ and C₅.
  - Ex 4.11 and 4.12: exact d_TV is at most the printed bound, and the formulas were derived algebraically from Thm 4.17.
  - Thm 4.17 under reading B: 3,000 random monotone instances.
  - The Ex 4.6 coupling law: exact rationals.

**No draft is false.** Track G4's statements are not part of this review.

## G1: approved with changes

`IsExchangeableTuple`, `degreeDCouplingPMF`, `Thm4_10` (ℝ≥0∞ right-hand side; min{1, λ} is correct), `Cor4_11`, `Cor4_12` (with the p₁ > 0 guard), `Ex4_4`, `Prop4_13` (the p < 1 guard is justified) and `Ex4_5_asymptotics` match.

- **G1-1. Withdraw ISSUE-EX4.6 counterexample 2 (p ∈ {0, 1}).**
  - Conditioning on a null event is undefined in the TeX, not wrong.
  - `not_Ex4_6_condLaw_p0` only shows that Lean's `cond` on a null set is the zero measure. That is a junk value, not a refutation of the source. Do not file it as one.
  - The accepted `Cor3_16` handles this case with a guard and no source issue; do the same here.
- **G1-2. Reclassify counterexample 1 (d ≥ n) as a domain note, not a source issue.**
  - Bullet 2 at L2231–2233 presupposes d ≤ n − 1. For d ≥ n, X₁ ≡ 0, so the size-bias claim holds trivially under D8.
  - If the `_restricted` suffix is dropped, `d < n` is typing. The lead decides the label.
- **G1-3. `Ex4_5_coupling`: add the monotonicity conjunct** `∀ ω j, X j ω ≤ X1 j ω` (L2203–2204). L2251 relies on it ("the size-bias coupling was increasing"). Optionally also add the per-j probability p(1 − p)^{n−2} (L2205–2206).
- **G1-4.** Status lines for L2171 (this agrees with Thm 4.6's first bound) and footnote L2182–2186 (heuristic).
- `Cor4_11`'s wrapper must apply `Cor3_16_holds`, not re-prove it.
- ISSUE-TYPO-4.11, ISSUE-TYPO-4.12 and ISSUE-TYPO-EX4.6 are confirmed.

## G2: approved with changes

`embedGraph`, `subgraphCopies` and the counting definitions (counts verified for 6 graphs H), `Thm4_14`, `Thm4_15`, `Sec4_3_2_subgraph_coupling`, `Cor4_16`, `Ex4_7` and `Ex4_8` match. ISSUE-TYPO-4.8 is confirmed, and the Thm 4.14 "=" should be "≤" (re-derived; a proof slip).

- **G2-1. New source issue (proof step, L2298).** The text says "W = Σ_α X_α is a sum of exchangeable indicators, [so] we can apply Corollary 4.12". **This is false for n ≥ 5.** Take the triangles α = {012}, β = {013} and γ = {034}: E[X_αX_β] = p⁵ but E[X_αX_γ] = p⁶. (Re-checked by the critic.)
  - Thm 4.15 is still true: use Thm 4.14 with I uniform on Γ. All p_α are equal, and the per-α couplings from facts 1–3 suffice; vertex-transitivity, not exchangeability, is what is needed.
  - Record it in SOURCE-ISSUES Part III as a proof slip. The G2 proofs must **not** use `Cor4_12` or `IsExchangeableTuple` on (X_α).
- **G2-2. Two typos.**
  - L2352: "the second equality follows" should be "inequality".
  - L2363: "non-isomorphic k-cycles" should be "distinct" (k!/(2k) counts distinct cycles).
- **G2-3.** L2364, "λ is of order (np)^k", holds for every p: for n ≥ k, (k − 1)!/(2kᵏ)·(np)ᵏ ≤ λ ≤ (np)ᵏ/(2k). Add it as a conjunct or a status line. Also add status lines for the pointers at L2332–2333 and L2368.

## G3: approved with changes

`IsIncreasing` and `IsDecreasing`, `not_Thm4_17_printed` (reading A counterexample re-derived: W ≡ 1, so the bound is 0 while d_TV = 1 − e⁻¹), `Thm4_17_fkg`, `Lem4_18` and `Lem4_18_strassen_1d` match. ISSUE-TYPO-4.17 is confirmed. The printed formulas in Ex 4.10–4.12 are exact consequences of Thm 4.17.

- **G3-1. Monotonicity domain in `Thm4_17_corrected` and `not_Thm4_17_printed`.** The TeX has functions {0,1}^N → {0,1}. `Monotone` on all of `Fin N → ℕ` is an unstated, stronger hypothesis. Use `MonotoneOn`/`AntitoneOn` on {y : ∀ j, y j ≤ 1}, or type f on `Fin N → Fin 2`. This is cheap.
- **G3-2. `Ex4_11`: replace `p < 1` with `p ≤ 1`.** At p = 1 the denominator is positive and the bound is 1 ≥ d_TV. The remaining restrictions (p = 0, d ≥ n, n = 1) are justified because the printed denominator vanishes; say so in the docstring.
- **G3-3. `Ex4_12`: replace `0 < p` with `0 ≤ p` and drop `d ≤ n − 1`.** At p = 0, q₂ = 1. For d ≥ n, C(n − 1, d) = 0, so the bound is 1. Only `2 ≤ n` and `p < 1` are justified.
- **G3-4. `Ex4_10`.** Connect X to f, for example `X i G := f i (edge indicators of G)`; as drafted, the monotonicity conjunct says nothing about W. Also add the literal §4.3.2 instance W = `subgraphCount H n`, whose bound coincides with Thm 4.15's.
- **G3-5.** The Ex 4.12 range is L2440–2449.
- **Optional:** add the claims at L2429–2430 and L2441–2442 that the degree indicators are monotone edge functions, as conjuncts.
