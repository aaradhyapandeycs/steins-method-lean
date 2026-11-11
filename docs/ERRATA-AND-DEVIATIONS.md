# Errata and Deviations from the Source

This file classifies every departure from the printed text of:

> Nathan Ross, *"Fundamentals of Stein's method"*, *Probability Surveys* 8 (2011) 210–293,
> DOI 10.1214/11-PS182, e-print `arXiv:1109.1880v1`.

The authoritative ledger of full issue descriptions, counterexamples, and Lean witnesses is
[`docs/SOURCE-ISSUES.md`](SOURCE-ISSUES.md).  Acceptance status (critic-reviewed) is recorded
in [`docs/COVERAGE.md`](COVERAGE.md).

---

## Classification

| Class | Description |
|---|---|
| **A** | False in a non-degenerate case — the printed statement is simply wrong in general. |
| **B** | Fails only at a boundary or outside the assumed range — a domain restriction is needed. |
| **C** | False proof step; the conclusion survives under a corrected argument. |
| **D** | Ambiguous, ill-posed, or a pure notational/cross-reference issue — reading clarification needed. |

---

## Count Table

| Class | Count | Description |
|---|---|---|
| A | 5 | Printed statement false in general |
| B | 11 | Boundary or domain restriction needed |
| C | 2 | Proof step or intermediate calculation error; main conclusion true |
| D | 15 | Notation, slip of the pen, cross-reference, or reading clarification |
| **Total** | **33** | |

---

## Part I — Source Typos and Cross-Reference Errata (Class D)

### `ISSUE-TYPO-1.1` · Class D — Indicator Notation Typo in Total Variation Definition

**Source**: Section 1.1.1, item 3 (`SteinIntro.tex:520–521`).

The printed class `\mathbb{I}[A\in\mathbb{R}]` is a typo for the indicator function
`\mathbb{I}[\cdot \in A]`, and line 521 contains a stray Latin-1 ligature byte (`0x8C`, `Œ`)
before the word "discrete".

**Lean witness**: `SteinMethod.tvDist` is defined via `A.indicator 1` (accepted in
[review-01](reviews/review-01.md)).

---

### `ISSUE-TYPO-3.3` · Class D — Summand Index Typo in Lemma 3.3

**Source**: Lemma 3.3 (`SteinIntro.tex:754`).

The printed sum `\sum_{j\ne i} X_i` should read `\sum_{j\ne i} X_j`.  Summing `X_i` over
`j \ne i` yields `(n-1) X_i / \sqrt{n}`, which is not independent of `X_i` and does not give
`W - W_i = X_i / \sqrt{n}`.

**Lean witness**: `SteinMethod.Lem3_3` formalizes `W_i = \sum_{j \ne i} X_j / \sqrt{n}`
(accepted in [review-03](reviews/review-03.md)).

---

### `ISSUE-TYPO-3.2.1` · Class D — Metric Symbol Typo in Section 3.2.1

**Source**: Section 3.2.1 (`SteinIntro.tex:936`).

The bound is stated for `d_K` (Kolmogorov distance), but Theorem 3.5 (which is applied)
bounds the Wasserstein distance `d_W`.

**Lean witness**: `SteinMethod.Sec3_2_1_triangles_restricted` uses `wassersteinDist`
(accepted in [review-04](reviews/review-04.md)).

---

### `ISSUE-TYPO-3.4a` · Class D — Missing Expectation Operator in Display (3.23)

**Source**: Section 3.4, display (3.23) (`SteinIntro.tex:1232–1236`).

The right-hand side of display (3.23) is a random variable but `\mathbb{E}` is omitted before
the bracket; the left-hand side `\mathbb{E}[Wf(W)]` is deterministic.

**Lean witness**: `SteinMethod.Sec3_4_sizeBias_identity` formalizes the display with
expectation on both sides (accepted in [review-04](reviews/review-04.md)).

---

### `ISSUE-TYPO-3.15` · Class D — Cross-Reference Bug in Proof of Corollary 3.15

**Source**: Proof of Corollary 3.15 (`SteinIntro.tex:1341`).

The reference `\ref{71}` resolves to equation (3.23) rather than to Corollary 3.15
(`\ref{cor71}`), so the PDF prints "Corollary 3.23".

**Lean witness**: `SteinMethod.Cor3_15` (accepted in [review-04](reviews/review-04.md)).

---

### `ISSUE-TYPO-3.9` · Class D — Cross-Reference Bug After Example 3.9

**Source**: Remark following Example 3.9 (`SteinIntro.tex:1429`).

The reference `\ref{ex71}` resolves to Example 3.8 (the normalized sum exercise), whereas
the intended target is Example 3.9 (`\ref{ex72}`, isolated vertices in `G(n,p)`).

**Status**: Accepted in [review-04](reviews/review-04.md).  The remark is prose; no Lean entry
is affected.

---

### `ISSUE-TYPO-3.21` · Class D — Omitted `\mathbb{E}[...]` and Derivative Prime in Proof of Proposition 3.21

**Source**: Proof of Proposition 3.21 (`SteinIntro.tex:1545–1549`).

Lines 1546–1547 omit `\mathbb{E}[...]` inside the sum, and line 1547 omits the derivative prime
`'` on `f`.  **Lean witness**: `SteinMethod.Prop3_21` proves Proposition 3.21 cleanly
(accepted in [review-05A](reviews/review-05A.md)).

---

### `ISSUE-TYPO-3.27` · Class D — Cross-References `\ref{thm91}` (`L1741`) and `\ref{91}` (`L1775`) in Section 3.6

**Source**: Remark after Theorem 3.27 (`SteinIntro.tex:1741–1743`) and proof of Theorem 3.28
(`SteinIntro.tex:1775`).

At `L1741`, `\ref{thm91}` points to Theorem 3.24 instead of the unlabeled zero-bias Kolmogorov
Theorem 3.27 (`L1697–1704`).  At `L1775`, `\ref{91}` points to equation `(3.38)` instead of
Lemma 3.25 (`\ref{lem91}`), printing "Lemma 3.38".  Accepted in
[review-05B](reviews/review-05B.md).

---

### `ISSUE-3.5.2-PROSE` · Class D — `"not sufficient"` Slip for `"not necessary"` After Display `(3.34)`

**Source**: Section 3.5.2 prose (`SteinIntro.tex:1565–1566`).

Immediately after stating that the Lindeberg condition `(3.34)` is sufficient for a CLT, line
1566 writes "the condition is not sufficient as we could take `X_{1,n}` to be standard normal
and the rest of the terms zero", a slip of the pen for **not necessary**.

**Lean witness**: `SteinMethod.Sec3_5_2_lindeberg_not_necessary_corrected`
(accepted in [review-05A](reviews/review-05A.md)).

---

### `ISSUE-TYPO-4.4` · Class D — Missing `\Delta` in Proof of Lemma 4.4

**Source**: Proof of Lemma 4.4 (`SteinIntro.tex:1901`).

The printed sum `\sum_{j \in A} f_j(k)` should be `\sum_{j \in A} \Delta f_j(k)`.

**Lean witness**: `SteinMethod.Lem4_4` formalizes the correct statement (accepted in
[review-01](reviews/review-01.md)).

---

### `ISSUE-TYPO-4.6` · Class D — Misplaced `\label{thm102}` Causes "Theorem 4.1" in PDF

**Source**: Theorem 4.6 (`SteinIntro.tex:1942–1949`) and cross-references at lines 1969,
1983, 1989.

The label `\label{thm102}` is placed outside the `theorem` environment, so LaTeX binds it to
the subsection counter (`4.1`) rather than Theorem 4.6.  Every `\ref{thm102}` in the
surrounding proof prints "Theorem 4.1".

**Status**: *Pending review.*  `docs/source-inventory.md` records `thm102` on Theorem 4.6.
No Lean entry for Section 4.6 has been accepted yet.

---

### `ISSUE-TYPO-6.2` · Class D — Missing Subscript `A` in `\Delta f(k)` in Lemma 6.2

**Source**: Lemma 6.2 (`SteinIntro.tex:3243–3249`).

Line 3248 prints `\Delta f(k)` in place of `\Delta f_A(k)`.  Formalized with `geomSteinSol p A`
in `SteinMethod.Lem6_2`.

---

### `ISSUE-TYPO-6.6` · Class D — Spurious Superscript `W^{e_0}` in Proof of Theorem 6.6

**Source**: Proof of Theorem 6.6 (`SteinIntro.tex:3381–3383`).

`W^{e_0}` is a typo for `W^e`; Theorem 6.6 (`SteinMethod.Thm6_6`) is unaffected.

---

### `ISSUE-TYPO-7.5` · Class D — Subscript Typo `a_{i \sigma_j}` in Example 7.5

**Source**: Example 7.5 (`SteinIntro.tex:3602, 3607`).

The index `j` in `a_{i \sigma_j}` is unbound; `L3621` confirms the intended definition is
`W = \sum_{i=1}^n a_{i,\sigma(i)} - \frac{1}{n}\sum_{i,j} a_{ij}`.

**Status**: *Pending review.*  Example 7.5 Lean entries have not yet been accepted.

---

### `ISSUE-2.1` · Class D — Unbound Variable `Z` in Lemma 2.1(2)

**Source**: Lemma 2.1(2) (`SteinIntro.tex:570–572`).

The variable `Z` appears inside item 2 without being bound there; it is bound in item 1 as a
standard normal.  No moment hypothesis is needed (the integrability condition is on `f'(Z)`
under the standard normal, not on `W`).

**Lean witness**: `SteinMethod.Lem2_1_2` formalizes the printed statement with `Z \sim N(0,1)`
(accepted in [review-02](reviews/review-02.md)).

---

### `ISSUE-3.9` · Class C — Algebra Errors in `E[Y_1 Y_2]` and `Var(\sum D_i)` in Example 3.9

**Source**: Example 3.9 (`SteinIntro.tex:1395–1397`).

The printed formula for `E[Y_1 Y_2]` at L1397 uses `(n-1)^2` where the correct value is
`(n-2)^2`.  `Var(\sum_{i=1}^n D_i)` at L1395 inherits this error and commits two additional
algebra errors.  The conclusion of Example 3.9 — that Theorem 3.17 holds — is true and
proved from scratch using the correct variance bound.

Machine-checked refutations at `n = 3`, `p = 1/2`:
- `SteinMethod.Ex3_9_L1397_counterexample`: printed `E[Y_1 Y_2]` gives `5/8`; correct value
  is `1/4`.
- `SteinMethod.Ex3_9_L1395_counterexample`: printed `Var(\sum D_i)` gives `3`; correct value
  is `3/4`.

Accepted in [review-04](reviews/review-04.md).

---

## Part II — Mathematical Source Issues (Classes A, B, C)

### `ISSUE-2.2` · Class A — Non-Existence of Two-Sided Solution; Uniqueness Failure Without Continuity

**Source**: Lemma 2.2, Corollary 2.3, and several downstream results.

Under the two-sided derivative reading, no bounded solution of the Kolmogorov Stein equation
exists at any `x \in R` (Darboux's theorem rules it out at the jump point `w = x`).  Under
the left-derivative reading, uniqueness among bounded functions fails without an added
continuity hypothesis.

Lean witnesses:
- `SteinMethod.Lem2_2_twoSided_noSolution` — no two-sided solution exists.
- `SteinMethod.Cor2_3_twoSided_counterexample` — the `deriv`+`normalSteinSolKolm`
  transcription fails at `W \equiv 0`, `x = 0`.

Corrected entries: `SteinMethod.Lem2_2_corrected`, `SteinMethod.Cor2_3_corrected`
(left-derivative operator; uniqueness among bounded continuous solutions).

Accepted in [review-02](reviews/review-02.md); updated entries re-accepted in
[review-03](reviews/review-03.md).

---

### `ISSUE-3.2.1` · Class B — Division by `\sigma = 0` at Boundary `p \in {0, 1}`

**Source**: Section 3.2.1, triangle counts in `G(n,p)` (`SteinIntro.tex:918–941`).

The source states the bound for `0 \le p \le 1`, but at `p = 0` and `p = 1` the variance
`\sigma^2 = 0`, making `W` and both denominators undefined.

**Lean witness**: `SteinMethod.Sec3_2_1_triangles_restricted` requires `0 \lt p \lt 1` and
`3 \le n` (accepted in [review-04](reviews/review-04.md)).

---

### `ISSUE-3.5` · Class A — Dependency-Neighborhood Hypothesis Too Weak in Theorem 3.5

**Source**: Theorem 3.5 (`SteinIntro.tex:815–822`).

Definition 3.1 does not require `i \in N_i`.  Without this, the printed bound is false: a
Rademacher construction with `D = 2`, `n = 2 \times 10^4` gives `d_W(W,Z) \not\to 0` while
the right-hand side tends to `0`.

Machine-checked refutation: `SteinMethod.not_Thm3_5_printed` (accepted in
[review-03](reviews/review-03.md)).

**Lean witness**: `SteinMethod.Thm3_5_corrected` uses `IsDependencyGraph` (which requires
`i \in N_i`, symmetry, and the product-independence condition from `SteinIntro.tex:810–812`)
in place of `HasDependencyNeighborhoods`.

---

### `ISSUE-3.6` · Class C — Missing `1/n` Factor in Example 3.6; Printed Bound Holds for `n \ge 16`

**Source**: Example 3.6 (`SteinIntro.tex:1072–1075`).

The intermediate bound `E|W'-W|^3 \le 8/n^{3/2} \sum E|X_i|^3` omits a factor `1/n` from
averaging over the random index `I`, giving `8/n^{5/2}` as the correct value.  Substituting
into Theorem 3.7 yields second term `8/(3 n^{3/2})`.  Since `8/(3 n^{3/2}) \le 2/(3n)` iff
`n \ge 16`, the printed bound holds for `n \ge 16` and is open for `n \lt 16`.

Lean witnesses:
- `SteinMethod.Ex3_6_corrected` — corrected bound `8/(3 n^{3/2}) \sum E|X_i|^3` for all
  `n \ge 1`.
- `SteinMethod.Ex3_6_restricted` — the printed bound `2/(3n)` for `n \ge 16`.

Accepted in [review-03](reviews/review-03.md).

---

### `ISSUE-3.8` · Class B — Anti-Voter Chain Not Irreducible on Full State Space

**Source**: Section 3.3.1 prose (`SteinIntro.tex:1108–1111`).

The two constant labelings `(+1)^V` and `(-1)^V` have zero incoming transition probability
(every step of the anti-voter chain produces a non-constant labeling), so the chain on
`{-1,1}^V` is not irreducible as printed.  Irreducibility holds after restricting to the
non-constant labelings (an absorbing set after one step).

Machine-checked refutations:
- `SteinMethod.antiVoterStep_const_eq_zero` — constant labelings have zero forward mass.
- `SteinMethod.antiVoterStep_support_nonconst` — every image is non-constant.

Accepted in [review-04](reviews/review-04.md).  Theorem 3.8 and Lemma 3.10 are proved
literally (they quantify over every stationary distribution and do not need irreducibility).

---

### `ISSUE-3.10` · Class A — Zero-Bias Distribution Does Not Exist When `E|W|^3 = \infty`

**Source**: Definition 3.10 and Proposition 3.19(1) (`SteinIntro.tex:1442–1449`, `1474–1478`).

For `W` with symmetric density `(3/2)|w|^{-4} 1_{|w| \ge 1}` (finite variance, infinite third
moment), the unique candidate zero-bias law has density `p^z(u) = 1/(4u^2)` for `|u| \gt 1`,
and `f'(W^z)` is non-integrable for a specific locally AC `f`, refuting Proposition 3.19(1)
both classically and under Lean's Bochner convention.

**Lean witness**: `SteinMethod.IsZeroBias` uses dual-integrability quantification;
`Prop3_19_corrected` requires `0 \lt \sigma^2` (accepted in [review-02](reviews/review-02.md)).

---

### `ISSUE-3.11` · Class B — Division by `\mu = 0` in Proposition 3.11 and Corollary 3.12

**Source**: Proposition 3.11 and Corollary 3.12 (`SteinIntro.tex:1239–1252`).

At `\mu = 0` (e.g. `X \equiv 0`), every distribution satisfies the size-bias equation
(`0 = 0`), so the density `x/\mu` is undefined and the size-bias law is not unique.

Lean witnesses: `SteinMethod.Prop3_11_restricted` and `SteinMethod.Cor3_12_restricted`
require `0 \lt \mu` (accepted in [review-04](reviews/review-04.md)).

---

### `ISSUE-3.19` · Class B — Non-Uniqueness and Division by `\sigma^2 = 0` in Proposition 3.19

**Source**: Proposition 3.19 (`SteinIntro.tex:1471–1485`) and Section 3.6.1 parenthetical
(`SteinIntro.tex:1741–1742`).

At `\sigma^2 = 0` (e.g. `W \equiv 0`), every distribution trivially satisfies the zero-bias
equation, so the law is not unique, the density `\sigma^{-2} E[W 1_{W \gt w}]` divides by
zero, and unbounded zero-bias versions exist (`SteinMethod.zero_stdNormalLaw_isZeroBias_unbounded`,
accepted in [review-05B](reviews/review-05B.md)).

**Lean witnesses**: `SteinMethod.Prop3_19_corrected` and
`SteinMethod.Sec3_6_zeroBias_bdd_restricted` require `0 \lt \sigma^2`
(accepted in [review-05A](reviews/review-05A.md) and [review-05B](reviews/review-05B.md)).

---

### `ISSUE-3.20` · Class B — Scaling Instance `Var(aW) = a^2 \sigma^2 = 0` in Proposition 3.20

**Source**: Proposition 3.20 (`SteinIntro.tex:1519–1521`).

The existence reading (`a W^z` is a zero-bias version of `a W`) holds for every `a \in \mathbb{R}`
(`SteinMethod.Prop3_20`), whereas distributional uniqueness `(aW)^z \stackrel{d}{=} aW^z` across
arbitrary zero-bias realizations fails at `a = 0` or `\sigma^2 = 0`
(machine-checked refutation `SteinMethod.not_Prop3_20_printed`; restricted law-identity version
`SteinMethod.Prop3_20_restricted`, accepted in [review-05A](reviews/review-05A.md)).

---

### `ISSUE-4.7` · Class B — Missing `i \in N_i` Hypothesis in Theorem 4.7

**Source**: Theorem 4.7 (`SteinIntro.tex:1970–1977`).

Without `i \in N_i`, the first inner sum `\sum_{j \in N_i} p_i p_j` can be zero while
`d_TV(W, Po(\lambda)) \gt 0` (counterexample: `n = 1`, `X_1 \equiv 1`, `N_1 = \emptyset`).
The proof requires `i \in N_i` to ensure `X_i` is absent from `V_i`.

**Lean witness**: `SteinMethod.Thm4_7_corrected` adds `\forall i, i \in N_i`
(accepted in [review-02](reviews/review-02.md)).

---

### `ISSUE-4.17` · Class A — Reading (A) of Theorem 4.17 Is False

**Source**: Theorem 4.17 (`SteinIntro.tex:2382–2390`).

The phrasing "increasing or decreasing" admits two readings: (A) each `X_i` is individually
monotone in any direction, or (B) all `X_i` share a common monotone direction.  Reading (A) is
false: with `X_1(y) = y` and `X_2(y) = 1-y` (independent monotone directions), `W \equiv 1`
gives right-hand side `0` while `d_TV(\delta_1, Po(1)) \gt 0`.

**Lean witness**: `SteinMethod.Thm4_17_corrected` uses Reading (B) — all increasing or all
decreasing (accepted in [review-02](reviews/review-02.md)).

---

### `ISSUE-5.7` · Class B — Missing `M \ge 1` Support Restriction and Independence Hypothesis

**Source**: Theorem 5.7 (`SteinIntro.tex:2915–2929`).

(1) The distribution `P(M = m) = p P(N \ge m)` is a valid probability law only for `m \ge 1`
(the formula assigns positive mass to infinitely many non-positive integers otherwise, since
`P(N \ge m) = 1` for `m \le 0`).  (2) The joint independence of `(N, M)` from `(X_i)_{i \ge 1}`
is not stated (unlike Theorem 5.6), and without it the bound can fail.

**Lean witness**: `SteinMethod.Thm5_7_corrected` requires `M \ge 1` and joint independence
(issue entry accepted in [review-02](reviews/review-02.md)).

---

### `ISSUE-5.9` · Class B — Boundary Case `n = 1` (`\log 1 = 0`) and `\sigma^2 = 0` in Theorem 5.9

**Source**: Theorem 5.9 (`SteinIntro.tex:3015–3020`).

At `n = 1`, `C \log(1)/1 = 0` for every `C \gt 0` whereas `d_W(2 Y_1/\sigma^2, \mathrm{Exp}(1)) \gt 0`
(for `P(Z_1 = 0) = P(Z_1 = 2) = 1/2`, `2 Y_1/\sigma^2 \equiv 4` and `d_W(\delta_4, \mathrm{Exp}(1)) \ge 3`),
and `\sigma^2 = 0` divides by zero.

**Lean witness**: `SteinMethod.Thm5_9_corrected` requires `0 \lt \sigma^2` and `2 \le n`
(issue entry accepted in [review-02](reviews/review-02.md)).

---

### `ISSUE-6.0` · Class A — Omitted Scaling Factor `p` on `d_W(X, W)` in Section 6 Opening Display

**Source**: Section 6 opening paragraph (`SteinIntro.tex:3193–3198`).

The display `|d_W(pW, Z) - d_W(X, W)| \le p` omits the homogeneity factor `p` on `d_W(X, W)`.
At `p = 1/4` and `W \equiv 4`, `d_W(\delta_1, \mathrm{Exp}(1)) = 2/e` whereas for
`X \sim \mathrm{Ge}(1/4)` on `\{1, 2, \dots\}`, `d_W(X, 4) = \mathbb{E}|X - 4| = 2 \cdot 81/64 = 81/32`,
giving `|d_W(pW, Z) - d_W(X, W)| \ge 81/32 - 2/e \approx 1.80 \gt 1/4 = p`.  The true triangle-inequality
bound is `|d_W(pW, Z) - p\,d_W(X, W)| \le d_W(pX, Z) \le p`.

**Lean witnesses**: `SteinMethod.not_Sec6_opening_wasserstein_printed` (refutation) and
`SteinMethod.opening_wasserstein_of_ex5_4` in `Formalization/Geometric/OpeningBound.lean`.

---

### `ISSUE-6.4` · Class B — Boundary Degeneracy at `p = 1` (`W \equiv 0`) for Discrete Equilibrium Uniqueness

**Source**: Preamble to Proposition 6.4 (`SteinIntro.tex:3290–3291`) and Remark 6.2 (`SteinIntro.tex:3304–3310`).

At `p = 1`, `\mathbb{E}[W] = (1-1)/1 = 0` forces `W = 0` a.s., every probability law on `\mathbb{N}`
satisfies the discrete equilibrium identity `0 = 0`
(`SteinMethod.not_unique_isDiscreteEquilibrium_one`), and the renewal tail formula divides by `1 - p = 0`.
`SteinMethod.Rem6_2_restricted` restricts uniqueness and the stationary-excess formula to `0 \lt p \lt 1`.

---

### `ISSUE-7.5` · Class B — Stein Parameter `a = 2/(n-1)` Violates `a \le 1` at `n = 2` in Example 7.5

**Source**: Example 7.5 and Proposition 7.3 (`SteinIntro.tex:3597–3625`).

At `n = 2`, `a = 2/(2-1) = 2 \gt 1`, violating Definition 3.2's `0 \lt a \le 1` (and `n = 1`
divides by zero).  Proposition 7.3 holds for all `n \ge 1` via the unrestricted `0 \lt a`
library concentration bound (`D7`).

---

### `ISSUE-7.6` · Class B — Missing `t \ge 0` Hypothesis in Theorem 7.6

**Source**: Theorem 7.6 (`SteinIntro.tex:3814–3826`).

The tail bounds are stated without `t \ge 0` (unlike Proposition 7.1 and Theorem 7.2).  At
`t = -3 \lt 0`, the left-tail bound evaluates to `1 \le e^{-9/4} \lt 1`, a contradiction.

**Lean witness**: `SteinMethod.Thm7_6_corrected` quantifies `\forall t \ge 0`
(accepted in [review-02](reviews/review-02.md)).

---

## Notes

- Entries marked *pending review* have been drafted in `docs/SOURCE-ISSUES.md` but not yet
  accepted by the critic in `docs/COVERAGE.md`.
- Part III reading notes (`ISSUE-3.3`, `ISSUE-3.14`, `ISSUE-3.22`, `ISSUE-3.25`,
  `ISSUE-4.4`) are prose clarifications that do not change any numbered theorem statement and
  are therefore not classified A–D above; the numbered theorems involved are formalized
  literally.
