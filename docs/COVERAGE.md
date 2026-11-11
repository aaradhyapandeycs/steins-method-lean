# Coverage

Critic-owned (AGENTS.md rule 7). Only the critic marks a result as proved. The builder reports work in `docs/reviews/builder-report-NN.md`; the critic records results here after reviewing them.

The source is N. Ross, *Fundamentals of Stein's method*, arXiv:1109.1880v1 (`SteinIntro_utf8.tex`, SHA-256 `2cb6fcad…3bf4e`). The full checklist is [`source-inventory.md`](source-inventory.md), with 122 numbered environments.

**Status: work in progress. 89 statement entries are proved and critic-accepted (18 of them as disclosed corrected or restricted variants), covering 65 of the 122 numbered results. Every other inventory entry is open.**

Status vocabulary:
- **proved**: the printed statement, under its natural reading.
- **corrected** / **restricted**: a disclosed variant with a `docs/SOURCE-ISSUES.md` entry.
- **partial**, **open**, **source issue**.

| Source result | Label | TeX lines | Lean entry (`SteinMethod.`) | Status | Accepted in |
|---|---|---|---|---|---|
| Theorem 1.1 | `thm1` | 351–357 | `Thm1_1` | proved **from scratch** (the source only cites [ber41]; milestone M10), literally with constant 1.88. The project's own route: refined Fejér smoothing plus a Cantelli bound, with the budget closing at about 1.794. | [review-05J](reviews/review-05J.md) |
| Proposition 1.2(1) | `prop22` | 523–526 | `Prop1_2_1` | proved | [review-01](reviews/review-01.md) |
| Proposition 1.2(2) | `prop22` | 527–531 | `Prop1_2_2` | proved | review-01 |
| Proposition 1.2(3) | `prop22` | 532–537 | `Prop1_2_3` | proved (the source leaves the proof as an exercise) | review-01 |
| Lemma 2.1(1) | `lem1` | 562–569 | `Lem2_1_1` | proved ("absolutely continuous" read as locally AC, D5) | [review-02](reviews/review-02.md) |
| Lemma 2.1(2) | `lem1` | 570–574 | `Lem2_1_2` | proved (D5; no moment hypothesis) | review-02 |
| Lemma 2.2 | `lem2` | 578–588 | `Lem2_2_corrected` | corrected (ISSUE-2.2): left derivative; uniqueness among bounded *continuous* solutions. `Lem2_2_twoSided_noSolution` machine-checks that no two-sided solution exists. | review-02 |
| Corollary 2.3 | `cor1` | 591–596 | `Cor2_3_corrected` | corrected (ISSUE-2.2): left-derivative operator, any W. `Cor2_3_twoSided_counterexample` machine-checks the failure of the `deriv` transcription. | review-02 |
| Proposition 2.4 | `prop31` | 665–670 | `Prop2_4` | proved (D4). Both sides use the D1 integrability guard (DEFINITIONS §5.2). The hypothesis that every f_h solves the ODE everywhere fails for test functions with jumps (ISSUE-2.2), so the entry is vacuous for the Kolmogorov class; that case is `Cor2_3_corrected`. | review-02 |
| Lemma 2.5 (preamble) | `lem31` | 674–684 | `Lem2_5_formula`, `Lem2_5_ode_contAt` | proved as far as true (ISSUE-2.2): the second representation for measurable Gaussian-integrable h; the two-sided ODE everywhere for continuous h, and at every continuity point of a measurable h. An everywhere two-sided solution does not exist for h with a jump. | review-02, [review-03](reviews/review-03.md) |
| Lemma 2.5(1) | `lem31`/`i31` | 686–689 | `Lem2_5_1` | proved | review-02 |
| Lemma 2.5(2) | `lem31`/`i32` | 690–694 | `Lem2_5_2` | proved. The source cites CGS11 Lemma 2.4; it is proved from scratch here with the printed constants. | review-02 |
| §3 prose display | — | 703–707 | `Sec3_dK_le_dW` | proved: d_K ≤ (2/π)^{1/4} √d_W for any W | review-03 |
| Theorem 3.1 | `thm31` | 719–724 | `Thm3_1` | proved (D6 class; no moment hypothesis) | review-03 |
| Theorem 3.2 | `thm32` | 736–742 | `Thm3_2` | proved | review-03 |
| Lemma 3.3 | `lem33` | 753–759 | `Lem3_3` | proved under the context reading (ISSUE-3.3; W_i typo ISSUE-TYPO-3.3) | review-03 |
| Lemma 3.4 | `lem33aa` | 771–776 | `Lem3_4` | proved | review-03 |
| Theorem 3.5 | `thm41` | 815–822 | `Thm3_5_corrected` | corrected (ISSUE-3.5): dependency-graph hypothesis, printed constant √26 kept. The printed version is false: `not_Thm3_5_printed` machine-checks a counterexample with D = 2, n = 20000. | review-03 |
| §3.2.1 triangles in G(n, p) | — | 918–941 | `Sec3_2_1_triangles_restricted` | restricted and corrected reading: n ≥ 3, 0 < p < 1 (ISSUE-3.2.1; at p ∈ {0, 1}, σ = 0, so the printed claim is undefined). Exact mean and variance proved; the printed right-hand side is proved for d_W, since it is Theorem 3.5's Wasserstein bound. The printed metric is d_K (ISSUE-TYPO-3.2.1), and the literal d_K inequality is open. | [review-04](reviews/review-04.md) |
| §3.2.1 prose (CLT regime) | — | 942–944 | — | open: "p ∼ n^{−α} gives a CLT for 0 ≤ α < 2/9" (review-04 P3) | — |
| Proposition 3.6(1) | `prop51` | 962–971 | `Prop3_6_1` | proved | review-01 |
| Proposition 3.6(2) | `prop51` | 967–971 | `Prop3_6_2` | proved (library theorem for any 0 < a, D7) | review-02 |
| Theorem 3.7 | `thm51` | 983–988 | `Thm3_7` | proved (D7; moments in ℝ≥0∞) | review-03 |
| Remark 3.3 | — | 990–999 | `Rem3_3` | proved: a reversible Markov kernel gives an exchangeable pair | review-03 |
| Remark 3.4 | — | 1000–1008 | `Rem3_4` | proved, for any integrable Y and σ-algebras m₁ ≤ m₂ | review-03 |
| Remark 3.5 | — | 1009–1024 | — | open: O-U heuristic; scope to be proposed (review-03 P2) | — |
| Example 3.6 | — | 1053–1097 | `Ex3_6_steinPair`, `Ex3_6_printed`, `Ex3_6_corrected`, `Ex3_6_restricted` | The Stein pair (with exchangeability) is proved. The **printed bound (L1089) is proved for every n ≥ 1** (BL3). The corrected 8/(3n^{3/2}) form is also proved. ISSUE-3.6 records the proof slip at L1073–1074 (a missing 1/n) and the false rate remark at L1091. | review-03, [review-BL3](reviews/review-BL3.md) |
| §3.3.1 prose (irreducibility, uniqueness) | — | 1108–1111 | `Sec3_3_1_antiVoter_ergodic_corrected`, `not_Sec3_3_1_antiVoter_unique_printed`, `antiVoterStep_const_eq_zero` | corrected (ISSUE-3.8). As printed, the chain on {−1, 1}^V is not irreducible, because the constant labelings have no predecessor. Uniqueness also fails without connectivity: K₃ ⊔ C₄ is machine-checked. The cited [af10] result is proved from scratch for connected G (r-regular, not bipartite, not a cycle): it is primitive on the non-constant labelings, and the stationary law is unique with exactly that support | review-04, [review-BL5](reviews/review-BL5.md) |
| Theorem 3.8 | `thm52` | 1114–1127 | `Thm3_8` | proved. It holds for **every** stationary law, which is more than "the" stationary law. σ > 0 and n ≥ 3 are derived, not assumed. | review-04 |
| Lemma 3.9 | `lem51` | 1133–1136 | `Lem3_9` | proved | review-03 |
| Lemma 3.10 | — | 1208–1214 | `Lem3_10` | proved from scratch (cited [af10] Ch. 14), for every stationary law; r > 0 is typing | review-04 |
| Display (3.23) | `71` | 1232–1236 | `Sec3_4_sizeBias_identity` | proved, reading the missing 𝔼 as present (ISSUE-TYPO-3.4a) | review-04 |
| Proposition 3.11 | — | 1239–1245 | `Prop3_11_restricted` | restricted to μ > 0 (ISSUE-3.11, D8): uniqueness of the law x/μ dF and existence | review-04 |
| Corollary 3.12 | — | 1246–1252 | `Cor3_12_restricted` | restricted to μ > 0 (ISSUE-3.11) | review-04 |
| Theorem 3.13 | `thm71` | 1255–1261 | `Thm3_13` | proved (ℝ≥0∞ moments; `Measurable X` because of the conditional expectation) | review-04 |
| Proposition 3.14 | `prop71` | 1296–1299 | `Prop3_14` | proved (the unused extra independence is omitted, a reading note, ISSUE-3.14) | review-04 |
| Corollary 3.15 | `cor71` | 1319–1325 | `Cor3_15` | proved (ISSUE-TYPO-3.15; reading note ISSUE-3.14) | review-04 |
| Corollary 3.16 | `cor72` | 1326–1332 | `Cor3_16` | proved | review-04 |
| Example 3.8 | `ex71` | 1349–1353 | `Ex3_8` | exercise; the project's solution is proved: Thm 3.13 with the independent size-bias coupling of Cor 3.15 gives d_W ≤ σ⁻²√((2/π)Σμᵢ² Var Xᵢ) + σ⁻³Σ(E Xᵢ³ − μᵢ E Xᵢ²). Ross prints no formula; Xᵢ ≥ 0 comes from the setting of Cor 3.15 | [review-BL9](reviews/review-BL9.md) |
| Example 3.9 | `ex72` | 1354–1411 | `Ex3_9_sizeBias`, `Ex3_9_moments` | size-bias realization and increment identity proved for 0 ≤ p < 1 (review-04 P2: p = 1 also holds under D8 and is to be added). The printed μ, σ² (3.27), E[X₁X₂] and E[D₁²] are proved. **Source issue ISSUE-3.9**: the printed E[Y₁Y₂] (L1397) and Var(ΣD_i) (L1395) are false. Refutations are machine-checked at n = 3, p = 1/2: 1/4 against the printed 5/8, and 3/4 against the printed 3. | review-04 |
| Theorem 3.17 | — | 1413–1420 | `Thm3_17` | proved (∃ C, eventually d_W ≤ C/σ_n, using a corrected variance bound in place of ISSUE-3.9's formula) | review-04 |
| §3.5 prose (normal is the unique fixed point) | — | 1450–1451 | `Sec3_5_zeroBias_fixedPoint` | proved (fixed points are exactly N(0, v), with v = 0 included) | [review-05A](reviews/review-05A.md) |
| Theorem 3.18 | `thm81` | 1454–1461 | `Thm3_18` | proved (ℝ≥0∞ right-hand side) | review-05A |
| Proposition 3.19 | `i81`, `i82` | 1471–1485 | `Prop3_19_corrected` | corrected (ISSUE-3.19, D9): σ² > 0 is added, and the dual integrability class is used. Uniqueness, the density p^z and existence are proved. | review-05A |
| Proposition 3.20 | — | 1519–1520 | `Prop3_20`, `Prop3_20_restricted` | Existence reading proved for every a. The law-identity reading is restricted to a ≠ 0 and σ² > 0 (the σ² = 0 degeneracy of ISSUE-3.19); the refutation `not_Prop3_20_printed` is machine-checked. | review-05A |
| Proposition 3.21 | `prop81` | 1530–1551 | `Prop3_21` | proved, under weaker independence than printed (reading note) | review-05A |
| §3.5.2 prose (Lindeberg implies CLT) | — | 1560–1561 | `Sec3_5_2_lindeberg_sufficient` | proved (Lindeberg–Feller, centred rows; ISSUE-3.22 note) | review-05A |
| §3.5.2 prose ("not sufficient") | — | 1565–1566 | `Sec3_5_2_lindeberg_not_necessary_corrected` | corrected: the printed "not sufficient" is a slip for "not necessary". The example is proved. | review-05A |
| Theorem 3.22 | `thm82` | 1568–1575 | `Thm3_22` | proved | review-05A |
| Theorem 3.23 | `thm83` | 1578–1581 | `Thm3_23` | proved (convergence in `ProbabilityMeasure ℝ`) | review-05A |
| §3.5.2 prose (Xᶻ → 0 gives X → 0) | — | 1585–1586 | `Sec3_5_2_zeroBias_imp_tendstoInMeasure` | proved, together with max_i σ²_{i,n} → 0 | review-05A |
| §3.6 prose (binomial order) | — | 1655–1657 | `Sec3_6_binomial_order` | proved: for fixed 0 < p < 1 there are c, C > 0 with c·n^{−1/2} ≤ d_K, d_W ≤ C·n^{−1/2} for every n ≥ 1 (two-sided order) | [review-BL1](reviews/review-BL1.md) |
| Theorem 3.24 | `thm91` | 1666–1675 | `Thm3_24_corrected` | corrected (ISSUE-2.2): no bounded two-sided solution exists, so the left-derivative operator is used; the equality with d_K is exact. Finite mean is kept. | [review-05B](reviews/review-05B.md) |
| Lemma 3.25 | `lem91` | 1677–1686 | `Lem3_25_corrected` | corrected (ISSUE-2.2, left derivative). The printed constants √(π/2), 2 and √(2π)/4 are kept; the sharp \|D₋f_x\| ≤ 1 is also proved (ISSUE-3.25). | review-05B |
| Corollary 3.26 | `cor91` | 1688–1694 | `Cor3_26` | proved. F is read as the differentiable functions with the Lemma 3.25 bounds, which is a smaller class and therefore a stronger result (reading note). | review-05B |
| Theorem 3.27 | — | 1697–1704 | `Thm3_27` | proved, with constant 1 + 1/√(2π) + √(2π)/4 | review-05B |
| §3.6.1 prose (bounded W gives bounded Wᶻ) | — | 1741–1742 | `Sec3_6_zeroBias_bdd_restricted`, `Sec3_6_zeroBias_bdd_exists` | Every zero-bias Wᶻ is bounded when Var W > 0 (at σ² = 0 a machine-checked counterexample exists; ISSUE-3.19). The existence reading (some bounded version exists) is proved for every W. ISSUE-TYPO-3.27. | review-05B, review-05A |
| §3.6.1 prose (applications) | — | 1741–1743 | — | exercise or unworked remark: status only | — |
| Theorem 3.28 | `thm92` | 1750–1755 | `Thm3_28` | proved (D7; the proof needs the sharp \|f_x′\| ≤ 1, ISSUE-3.25 proof note) | review-05B |
| Lemma 3.29 | `lem92` | 1793–1798 | `Lem3_29` | proved | review-05B |
| §3.6.2 prose (applications) | — | 1810–1812 | — | qualitative remark: status only | — |
| Lemma 4.1(1) | `lem101` | 1823–1830 | `Lem4_1_1` | proved | review-01 |
| Lemma 4.1(2) | `lem101` | 1823–1835 | `Lem4_1_2` | proved | review-01 |
| Lemma 4.2 | `lem102` | 1837–1848 | `Lem4_2` | proved | review-01 |
| Corollary 4.3 | `cor101` | 1850–1855 | `Cor4_3` | proved | review-01 |
| Lemma 4.4 | `lem103` | 1879–1886 | `Lem4_4` | proved, reading f_A as Lemma 4.2's solution with f_A(0) = 0 (ISSUE-4.4 records the other reading). The source cites BHJ92 for the first bound; it is proved from scratch here. | review-01 |
| Theorem 4.5 | `thm101` | 1911–1916 | `Thm4_5` | proved, over the sharp (4.2) class, which is a smaller class and so gives a stronger result; 0 < λ is typing, since (4.2) divides by λ | [review-05C](reviews/review-05C.md) |
| §4.1 prose (binomial → Poisson) | — | 1938–1939 | `Sec4_1_binomial_limit` | proved with the explicit rate min{1, λ}·λ/n, and d_TV → 0 | review-05C |
| Theorem 4.6 | `thm102` | 1942–1949 | `Thm4_6` | proved, both inequalities (ISSUE-TYPO-4.6: the misplaced label prints "Theorem 4.1") | review-05C |
| Theorem 4.7 | `thm103` | 1970–1977 | `Thm4_7_corrected` | corrected (ISSUE-4.7): i ∈ N_i is added, which is what the proof uses. The printed version is refuted by the machine-checked `not_Thm4_7_printed`: X₁ ≡ 1 and N₁ = ∅ give a bound of 0 against d_TV = 1 − e^{−1} | review-05C |
| Remark 4.1 | — | 1978–1981 | `Rem4_1` | proved under a concrete reading: the vague "additional error term" is taken as the Arratia–Goldstein–Gordon b₃ term times min{1, λ^{−1/2}} from (4.2). The cited AGG bound is proved from scratch | review-05C |
| Theorem 4.8 | `thm104` | 2024–2030 | `Thm4_8` | proved, including the mean formula; 1 ≤ k ≤ n is the domain of the definition. The index sanity checks (`headRunCount_sanity_0110111`, `longestQualityRun_sanity_0110111`) are proved | review-05C |
| Remark 4.2 | `re101` | 2031–2038 | `Rem4_2` | proved in two readings: real k (λ → p^c, with error Θ(log n/n)), and integer k_n with bounded offset (λ_n − p^{x_n} → 0, with error O(log n/n)) | review-05C |
| §4.2.1 prose (longest run, Gumbel) | — | 2054–2061 | `Sec4_2_1_longestRun` | proved: P(W = 0) = P(R_n < k) exactly, and \|P(R_n − log(n(1−p))/log(1/p) < x_n) − e^{−p^{x_n}}\| ≤ C log n/n along integer thresholds (the qualification at L2060) | review-05C |
| Theorem 4.9 (Erdős–Rényi law) | — | 2071–2078 | `Thm4_9_corrected` | corrected (ISSUE-4.9): restricted to 0 < p < a ≤ 1 and proved from scratch. The printed statement is false for 0 < a < p (machine-checked `not_Thm4_9_printed` at p = 1/2, a = 1/4, where R_n = n eventually) and divides by zero at a = p | review-05C |
| Remark 4.3 | — | 2079–2110 | `Rem4_3` | proved: the match indicators are i.i.d. with joint product law and P(Y_i = 1) = Σ q_c² | review-05C |
| §4.4 prose (Example 4.21, true rate) | — | 2702–2706 | `Ex4_21_true_rate` | proved: d_TV(L(Wₙ), Po(1)) ≤ 2ⁿ/(n+1)! for every n, and n·d_TV → 0 ("much better than order 1/n"). The source cites [abt03]; this is proved from scratch. L2703 and L2705–2706 are status lines | [review-BL6](reviews/review-BL6.md) |
| §6 opening display (Wasserstein triangle inequality) | — | 3193–3198 | `not_Sec6_opening_wasserstein_printed` | source issue (ISSUE-6.0): the printed \|d_W(pW, Z) − d_W(X, W)\| ≤ p is false. The machine-checked refutation is p = 1/4, W ≡ 4, where the left side is 81/32 − 2/e ≈ 1.80. The corrected display (with p·d_W(X, W)) is open, because it needs Example 5.4 from Track D (E4). | [review-05E](reviews/review-05E.md) |
| §6 opening prose (support mismatch) | — | 3199–3200 | `Sec6_supportMismatch` | proved: for W =ᵈ kX with X ~ Ge(p), the exact value is d_TV(W, X) = 1 − p(1 − p)^{k−1}/(1 − (1 − p)^k), which tends to (k − 1)/k as p → 0⁺ (the reading of "≈") | review-05E |
| Lemma 6.1 | `lem173` | 3229–3241 | `Lem6_1_1`, `Lem6_1_2` | proved; W is read as ℕ-valued, with nothing lost (ISSUE-6.1 reading note) | review-05E |
| Lemma 6.2 | `lem174` | 3243–3249 | `Lem6_2` | proved, including the uniqueness of f_A among solutions with f(0) = 0, the Δf_A formula from the proof (L3266–3272) and \|Δf_A\| ≤ 1 (ISSUE-TYPO-6.2) | review-05E |
| Theorem 6.3 | `thm178` | 3251–3258 | `Thm6_3` | proved (the library theorem does not need the mean hypothesis) | review-05E |
| Definition 6.1 | — | 3283–3289 | `IsDiscreteEquilibrium` | definition accepted (the setup conditions are conjuncts; W is ℕ-valued, ISSUE-6.1); the witness `isDiscreteEquilibrium_geomLaw_self` shows it is non-vacuous | review-05E |
| §6.2 prose (equilibrium law exists, unique) | — | 3290–3291 | `Rem6_2_restricted` (part 1) | restricted to 0 < p < 1. At p = 1, W ≡ 0 and (6.1) holds for every Wᵉ, so uniqueness genuinely fails (ISSUE-6.4, `not_unique_isDiscreteEquilibrium_one`) | review-05E |
| Proposition 6.4 | `prop172` | 3292–3296 | `Prop6_4` | proved (the conditional-uniform law is written as a joint law) | review-05E |
| Remark 6.2 | `rem175` | 3304–3310 | `Rem6_2_restricted` (part 2) | restricted to 0 < p < 1. "The same as from renewal theory" is read as the stationary-excess formula P(Wᵉ = k) = P(W > k)/E[W]; at p = 1 that formula is 0/0 (ISSUE-6.4). Stationarity of the delayed renewal process is Remark 5.3 (Track D). | review-05E |
| Theorem 6.5 | `thm177` | 3312–3319 | `Thm6_5` | proved (one probability space; ℝ≥0∞ right-hand side) | review-05E |
| Theorem 6.6 | `thm1716` | 3345–3350 | `Thm6_6` | proved with the printed constant. The library also proves the sharper (log n + 1)/n (ISSUE-6.6 proof note; ISSUE-TYPO-6.6). The measurability and probability-measure guards for `uniformAttachment` are proved. | review-05E |

Definitions accepted in review-01 (milestone M1): `ipm`, `kolmogorovDist`, `wassersteinDist`, `tvDist`, `stdNormalExpect`, `normalSteinOp`, `normalSteinOpLeft`, `normalSteinSol`, `normalSteinSolKolm`, `normalWassersteinClass`, `poissonSteinOp`, `poissonSteinSol`, `IsExchangeablePair`, `IsSteinPair`, `IsSizeBias`, `IsZeroBias` (corrected Definition 3.10, ISSUE-3.10). Accepted in review-03: `HasDependencyNeighborhoods` (Definition 3.1, literal) and `IsDependencyGraph` (prose L810–812, used by `Thm3_5_corrected`).

Accepted in review-04:
- `spin`, `antiVoterStep` (staying put at isolated vertices is a totality convention, irrelevant for r ≥ 1), `IsAntiVoterStationary`, `kappa`;
- `EdgePair`, `graphOfEdgeBits`, `erdosRenyi`, `edgeIndicator`. Non-vacuity of `erdosRenyi` is `erdosRenyi_edgeIndicator_iIndepFun_and_hasLaw`: a probability measure whose edge indicators are i.i.d. Bernoulli(p).

Accepted in review-05B: `normalKolmogorovClass`, with non-vacuity witness `exists_ne_zero_mem_normalKolmogorovClass`.

Non-vacuity witnesses accepted: in review-01, `exists_isSteinPair_rademacher` and `exists_isSizeBias_bernoulli`; in review-02, `isZeroBias_rademacher_uniform` (Rademacher ±1 has zero-bias law Uniform[−1, 1]).

Source-issue entries accepted in review-02: ISSUE-2.1, 2.2, 3.5, 3.6, 3.10, 3.11, 3.19, 4.7, 4.17, 5.7, 5.9, 7.6, plus the notes ISSUE-3.22 and ISSUE-4.4. Re-accepted after updates in review-03: ISSUE-2.2, 3.5, 3.6; newly accepted: the note ISSUE-3.3. Machine-checked refutation accepted in review-03: `not_Thm3_5_printed`.

Accepted in review-04:
- the source-issue entries ISSUE-3.8, ISSUE-3.9, ISSUE-3.2.1, ISSUE-TYPO-3.2.1, ISSUE-TYPO-3.4a, ISSUE-TYPO-3.15, ISSUE-TYPO-3.9, and the note ISSUE-3.14;
- the machine-checked refutations `antiVoterStep_const_eq_zero`, `Ex3_9_L1397_counterexample` and `Ex3_9_L1395_counterexample`.

Accepted in review-05B: ISSUE-TYPO-3.27 (L1741 and L1775), the ISSUE-3.25 proof note, and the machine-checked σ² = 0 counterexample `zero_stdNormalLaw_isZeroBias_unbounded`. These record problems in the source; they do not by themselves make any later result proved.

Accepted in review-05C:
- the definitions `headRunIndicator`, `headRunCount`, `longestQualityRun`, `klDivBernoulli`, and the sharp class `poissonSteinClass`;
- the source-issue entries ISSUE-4.7 (re-confirmed) and ISSUE-4.9 (new), with the machine-checked refutations `not_Thm4_7_printed` and `not_Thm4_9_printed`; the typo ISSUE-TYPO-4.6.

Accepted in review-05E:
- the definitions `geomLaw`, `posGeomLaw`, `geomSteinOp`, `geomSteinSol`, `geomSteinClass`, `IsDiscreteEquilibrium`, the comap measurable space on `Digraph`, `digraphOfTargets`, `uniformAttachment`, `digraphInDegree`. Non-vacuity: `isDiscreteEquilibrium_geomLaw_self`, `instIsProbabilityMeasureUniformAttachment`, `measurable_digraphOfTargets`;
- the source-issue entries ISSUE-6.0 (its prose arithmetic is to be corrected to 81/32, review-05E E-R1), ISSUE-6.4, ISSUE-TYPO-6.2, ISSUE-TYPO-6.6, the reading note ISSUE-6.1 and the proof note ISSUE-6.6;
- the machine-checked refutations `not_Sec6_opening_wasserstein_printed` and `not_unique_isDiscreteEquilibrium_one`.

Not yet covered in §3.1–3.4:
- the §3.2.1 CLT-regime prose (L942–944);
- Remark 3.5;
- the literal d_K reading of §3.2.1;
