# Statement review: G4 (§4.3.4, TeX L2453–2605) and BL7 (Ruciński criterion, L941–945)

- **Critic:** Claude, 2026-11-11.
- **Method:** a first-pass independent review with exact or numerical checks. The critic re-checked the key findings against the TeX:
  - the L2500 variance line;
  - L2600 citing `thm122`, the positively-related bound at L2253;
  - the exact Rem 4.17 counterexample at (n, k, m) = (3, 4, 2), where the printed bound is −0.0438 and d_TV is 0.4199;
  - the G4-5 identity, which is algebraic: q·aᵏ = (1 − 1/(n−1))ᵏ with q = ((n−1)/n)ᵏ.

## G4: approved with changes

**No drafted entry is false.** Every printed formula in L2453–2605 holds wherever it is defined, apart from the L2500 variance typo. The following match:
- `Thm4_19` (the pᵢ > 0 guard on `cond` is justified);
- `Ex4_13_sizeBias`, `Ex4_13_moments_corrected` (the N ≥ 2 guard is justified: 0/0 at N = 1), `not_Ex4_13_var_printed` (N=4, n=1, m=2: printed −1/8, true 1/4);
- `Ex4_13_restricted` (exact d_TV ≤ bound in all 8,554 cases with N ≤ 29);
- `Ex4_15_allTypes_iff`, `Ex4_15_sizeBias`;
- `Ex4_15_restricted` (exact for 2 ≤ n ≤ 39 and 0 ≤ k ≤ 4n);
- `Ex4_15_rate`, `Ex4_16_restricted`, `not_Rem4_17_atLeast_printed`.

### Required changes

- **G4-1 (high). Withdraw `not_Ex4_13_bound_N_eq_one` and ISSUE-4.13 item 2.**
  - At N = 1 every term of L2504 divides by N − 1 = 0, so the printed formula is undefined there, not false. The "counterexample" only shows Lean's x/0 = 0. This is the junk-value pattern already withdrawn in G1-1.
  - Keep `2 ≤ N` and justify it in the docstring.
  - The only source issue here is **ISSUE-TYPO-4.13**: at L2500, (n−m) should be (N−m). The L2504 bound uses the correct variance.
- **G4-2 (high). `Rem4_14` docstring vs Prop.** The docstring says Thm 4.19 applied to B "recovers the bound of `Ex4_13_restricted`", but the Prop states only the representation. Do one of:
  - add a conjunct: for 2 ≤ N, `tvDist (Pb.map ΣB) (poissonLaw r) ≤` the L2504 expression, obtained through Thm 4.19 with X^{(i)} := B for the independent Bernoulli family; or
  - delete that clause from the docstring.
- **G4-3 (high). Missing entry `Ex4_16_sizeBias`** for the coupling at L2581–2587. It must state:
  - for each i with pᵢ < 1, redirecting each ball in box i independently to box j ≠ i with probability pⱼ/(1−pᵢ) gives (X_j^{(i)}) with the law of (X_j) conditional on Xᵢ = 1;
  - X_j^{(i)} ≤ X_j everywhere;
  - with I independent, P(I = i) = πᵢ/λ, πᵢ = (1−pᵢ)ᵏ and λ > 0, the resulting Wˢ is a size-bias of W.

  The guard pᵢ < 1 is justified, because pⱼ/(1−pᵢ) is undefined at pᵢ = 1 and P(I = i) = 0 there when k ≥ 1. This mirrors `Ex4_15_sizeBias`.
- **G4-4 (medium-high). Rem 4.17 coupling claims.** The substantive printed claim at L2594–2597 is that the coupling "is still decreasing".
  - **`Rem4_17_atMost`:** add a conjunct `∃ Y` with the conditional laws (for P(Xᵢ = 1) > 0) and `Y i ω j ≤ X j ω`. The source's construction is valid: draw the target count from L(Mᵢ | Mᵢ ≤ m) and move the excess balls out with weights p_l/(1−pᵢ).
  - **`Rem4_17_atLeast_corrected`:** add the same conjunct (adding balls to box i is a decreasing coupling), or delete the coupling wording from its docstring.
- **G4-5 (medium). `Ex4_15_asymptotic_ineq`.** The last conjunct weakens "asymptotically of order" to a one-sided ≤. Add the exact identity: for n ≥ 2, the (4.13) right-hand side equals min{1, λ}·(λ/n + ((n−1)/n)·λ·(1 − aᵏ)), with a = n(n−2)/(n−1)². Together with λₙ → e^c (`Ex4_15_rate`), this captures the two-sided claim at L2553–2555.
- **G4-6 (medium). Do not file ISSUE-4.15 in SOURCE-ISSUES.** These are domain or reading notes and belong in docstrings, as in the G1-2 and G3-2 precedents:
  - n ≥ 2 comes from the 1/(n−1) in the formula;
  - n ≥ 3 at L2559 comes from the n(n−2) denominator;
  - the rounding of k is a reading note.
- **G4-7 (medium). ISSUE-4.16 scope.**
  - File only the omitted condition k ≠ log λ, with the `Ex4_16_exists_zero_denom` witness, which is valid (k = 2, n = 9, an IVT path with every pᵢ > 0).
  - k = 0 and λ = 0 are domain notes.
  - Do not assert that "BHJ Thm 6.D explicitly assumes k > log λ" unless the cited book is checked.
  - The printed bound at L2590 is **true wherever defined**: zero violations in 26,268 exact small cases, and the Thm 4.19 bound is at most the printed one throughout extensive uniform and random searches. Say so in the entry's docstring. It is not a source error.
- **G4-8 (low, consistency).**
  - In `Thm4_19`: drop the redundant `0 < r` (ΣP(I=i) = 1 forces it), and add the `IsSizeBias P W P Ws` conjunct for "so that Wˢ has the size-bias distribution" (L2458–2459), as in the approved G2 `Thm4_14`.
  - Drop conjuncts that only restate hypotheses: `0 < (N:ℝ)−1` in `Ex4_13_restricted`, `0 < (n:ℝ)−1` in `Ex4_15_restricted`, and `k − log r ≠ 0` in `Ex4_16_restricted`.

### Missed claims (status line or optional conjunct)

- **L2526–2527:** "an estimate with error for the probability of this event", i.e. |P(W = 0) − e^{−λ}| ≤ (4.13). Make it a conjunct; it follows from d_TV.
- **L2540, L2544:** P(Xᵢ = 1) = ((n−1)/n)ᵏ and P(Xᵢ = Xⱼ = 1) = ((n−2)/n)ᵏ. Optional conjuncts.
- **L2488, L2530:** "the Xᵢ are exchangeable". Optional `IsExchangeableTuple` conjunct.
- **L2588:** "mean and variance easily computed…" needs a status line.
- **L2600:** typo, "Finally, could also consider" (missing "we"). This is an ISSUE-TYPO note only.

### Source issues (confirmed)

- **ISSUE-TYPO-4.13 (L2500):** `(n-m)` should be `(N-m)`.
- **ISSUE-REM-4.17 (L2600):** cites `thm122` (positively related, L2253) instead of `thm125` (negatively related, L2455).
  - The indicators 1[Mᵢ ≥ m] are negatively related, and the positively-related bound fails:

    | (n, k, m) | thm122 bound | exact d_TV |
    |---|---|---|
    | (2, 1, 1) | 0 | 0.632 |
    | (3, 4, 2) | −0.044 | 0.420 |

  - The corrected Thm 4.19 bound holds. Keep `not_Rem4_17_atLeast_printed`.
- **ISSUE-4.16:** only the omitted k ≠ log λ condition (G4-7).

## BL7: approved, with one required change

`Sec3_2_1_triangles_rucinski` is the right theorem. For H = K₃, m(H) = 1, so the criterion is npₙ → ∞ ∧ n²(1−pₙ) → ∞.
- **Both directions hold along the full sequence.** The necessity plan handles subsequences correctly. These steps were re-derived:
  - the lattice-atom argument;
  - σ² ≤ (np)³/6 + (np)⁵/(2n);
  - Wₙ ≤ √(32M) when n²(1−p) ≤ M.
- **The three equivalent conclusions are correct.** CDF convergence, d_K → 0 (by Pólya) and d_W → 0 (since E Wₙ² = 1 gives uniform integrability) all express "asymptotically normal".
- **The [0, 1] domain is a sound generalisation.** If pₙ ∈ {0, 1} infinitely often, both sides are false.
- **Measurability holds**: the σ-algebra on `SimpleGraph (Fin n)` is discrete. The status line for L944–945 is accepted.

- **BL7-1 (high). State the printed claim the docstring describes.** L943–944 says the 0 ≤ α < 2/9 regime is "only a subset of the regime where normal convergence holds". Add an entry or conjunct:
  - **Statement:** for all α ∈ [0, 1) and c > 0, with α = 0 → c < 1, if 0 ≤ pₙ ≤ 1 and n^α pₙ → c, then d_W → 0 and d_K → 0.
  - **Why it shows strictness:** it covers α ∈ [2/9, 1), where Track K showed that the L937–938 bound tends to 3√2 > 0.
  - **Optional:** the converse, that α ≥ 1 gives no CLT.
- **BL7-2 (low).** In the docstring:
  - note the Lean convention Wₙ = 0 when σₙ = 0, and why the [0, 1] domain is sound;
  - cite Ruciński (1988), Thm 2, with m(K₃) = 1, as a cited result proved from scratch.

## Next steps

- **G4:** apply G4-1 to G4-8, then prove. Import G1's `Formalization.PoissonSizeBias.Core.Basic` (CORE READY) and do not re-prove Thm 4.10 or Cor 4.11.
- **BL7:** apply BL7-1 and BL7-2, then prove.
- **Lead:** record ISSUE-TYPO-4.13, ISSUE-REM-4.17 and the scoped ISSUE-4.16 in SOURCE-ISSUES. Do not file ISSUE-4.13 item 2 or ISSUE-4.15.
