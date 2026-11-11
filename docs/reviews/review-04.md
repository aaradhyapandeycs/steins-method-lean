# Critic review 04: Batch 4 (§3.2.1 triangles, §3.3.1 anti-voter, §3.4 size bias), `631cf06`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` (SHA-256 `2cb6fcad…3bf4e`), L918–949 and L1099–1436, re-read in full.

## Verdict

**Batch 4 is ACCEPTED.** 13 new statement entries are recorded in `docs/COVERAGE.md`, bringing the total to 45 (8 corrected or restricted). There are no blocking findings. Four follow-ups (P1–P4) go to the lead as housekeeping alongside Batch 5.

## Independent verification

The commands ran in the development checkout with `.locks/CRITIC-HOLD` set and every builder compile slot drained. The tracked Lean files are identical to `631cf06` (`git diff --stat 631cf06 -- '*.lean'` is empty).

| Check | Result |
|---|---|
| `lake build` | exit 0, `Build completed successfully (3317 jobs)` |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 1271 project declarations.` |
| `python3 scripts/check.py` | exit 0; forbidden-token check and statement-wrapper check pass |
| Axiom probe (`#print axioms`) on 13 `_holds` wrappers and 5 key library theorems | all `[propext, Classical.choice, Quot.sound]` |
| Wrapper identity (`example : Thm3_8 := Thm3_8_holds`, and the same for `Lem3_10`, `Sec3_2_1_triangles_restricted`, `Thm3_17`, `Ex3_9_moments`) | type-checks |
| Per-file `lake env lean` re-elaboration of all 13 new or changed files | 13/13 rc=0, 0 warnings, 0 errors, 23–68 s each |
| Mutation control 1: `Ex3_9_L1397_counterexample` with 1/4 changed to 1/3, in a scratch copy | rejected (`IsolatedMomentsMut.lean:769`, `change` failed) |
| Mutation control 2: `antiVoter_variance_bounds` with 2κ changed to 3κ, in a scratch copy | rejected (`AntiVoterMut.lean:277`, `linarith` failed) |

**`Audit.lean` and `lakefile.toml` change (Batch 5 isolation): accepted.**
- The audit now enumerates `git ls-files --cached Formalization`, falling back to `walkDir`. It still requires every tracked file to be imported, transitively, and still checks every constant of every imported `Formalization*` module.
- Untracked work-in-progress track files are skipped. On a clean checkout, such as the public export, the checked set is unchanged.

## Statement check

| Entry | TeX | Verdict |
|---|---|---|
| `Thm3_8` | 1114–1127 | **Matches.** It quantifies over every stationary law, which is stronger than "the" stationary law. σ > 0, n ≥ 3 and 2/n ≤ 1 are derived from non-bipartiteness and Lem 3.10, not assumed. The joint law "one step of the chain" is encoded as P{X = x, X′ = y} = P{X = x}·step(x, y). The bound has the printed constants. |
| `Lem3_10` | 1208–1214 | **Matches**, for every stationary law. I re-derived the route: E S = 0 and Var S = 2E[a₁ + a₋₁]/r, with κ ≤ a₁ + a₋₁ ≤ nr/2. r > 0 is typing. |
| L1108–1111 prose | — | **Source issue ISSUE-3.8 is confirmed and machine-checked.** The constant labelings have zero incoming probability (`antiVoterStep_const_eq_zero`). Irreducibility and uniqueness on the non-constant labelings are open (cited, M10). |
| `Sec3_2_1_triangles_restricted` | 918–941 | **Accepted as restricted plus corrected.** I re-derived the mean C(n,3)p³ and the variance C(n,3)p³[1 − p³ + 3(n − 3)p²(1 − p)] (3(n − 3) edge-sharing triangles, E[Y_iY_j] = p⁵). The right-hand side is Theorem 3.5's Wasserstein bound with D = 3n − 8 and the printed moment formulas. Restricting to 0 < p < 1 is justified, because σ = 0 at the endpoints (ISSUE-3.2.1). See P4 for the d_K versus d_W point. |
| `Sec3_4_sizeBias_identity` | 1232–1236 | **Matches** the spec; ISSUE-TYPO-3.4a (missing 𝔼). |
| `Prop3_11_restricted`, `Cor3_12_restricted` | 1239–1252 | **Matches** the spec (μ > 0, D8, ISSUE-3.11). |
| `Thm3_13` | 1255–1261 | **Matches.** The constants are μ/σ²·√(2/π) and μ/σ³ (the proof's ‖f″‖ ≤ 2 cancels the ½). ℝ≥0∞ moments, and `Measurable X`. |
| `Prop3_14`, `Cor3_15`, `Cor3_16` | 1284–1332 | **Match** the spec. The unused independence clause is omitted (reading note ISSUE-3.14), and Cor 3.16 has the 0 < p_i guard. |
| `Ex3_9_sizeBias` | 1354–1367, 1380–1383 | **Matches for 0 ≤ p < 1** (see P2). |
| `Ex3_9_moments` | 1370–1379, 1406–1409 | **Matches.** I re-derived E[D₁²] = (n − 1)p(1 − p)^{n−2} + (n − 1)(n − 2)p²(1 − p)^{2n−5}: the second term needs j, k ≠ 1 with both degree one, giving the exponent 2(n − 2) − 1. |
| L1393–1397 | — | **Source issue ISSUE-3.9 is confirmed** by independent enumeration of the 8 graphs on 3 vertices at p = ½. The degree-one count takes the value 0 on 2 graphs and 2 on 6 graphs, so Var = 3/4, against the printed 3. E[Y₁Y₂] = 1/8 ({12}) + 1/8 ({13, 23}) = 1/4, against the printed 5/8. In general E[Y₁Y₂] = p(1 − p)^{2n−4} + **(n − 2)²**p²(1 − p)^{2n−5}; the printed formula has (n − 1)². |
| `Thm3_17` | 1413–1420 | **Matches** (∃ C, eventually d_W ≤ C/σ_n). The proof avoids the false L1395 formula and uses a true variance bound. |

Example 3.8 is an exercise and gets a status line only.

## Findings for the lead (housekeeping; fold into Batch 5)

- **P1. Builder-report accuracy.** `builder-report-04.md` §2.2 misstates ISSUE-3.9:
  - it quotes the printed L1397 formula as "p(1 − p)^{n−2} + (n − 2)p²(1 − p)^{2n−5}";
  - it says E[Y₁Y₂] = 1/8 against 3/8;
  - it gives 27/64 against 99/64 for the variance.

  The Lean code and `SOURCE-ISSUES.md` are correct: 1/4 against 5/8, and 3/4 against 3, with the TeX quoted verbatim. Correct the report text so it matches. Builder reports must quote the Lean statement and the TeX, not a paraphrase.
- **P2. Drop `p < 1` from `Ex3_9_sizeBias`, or justify it.**
  - At p = 1 with n ≥ 2, X ≡ 0, so μ = 0, and `IsSizeBias` (D8) holds trivially. With n = 1 there are no edges, so p does not matter.
  - The printed example has no p restriction. As stated the entry is narrower than the source; COVERAGE records it as "for 0 ≤ p < 1" until this is fixed.
- **P3. Missed prose claim at L942–944.** "If p ∼ n^{−α} for some 0 ≤ α < 1, then the number of triangles satisfies a CLT for 0 ≤ α < 2/9."
  - Add an entry `Sec3_2_1_triangles_clt_regime`: for p_n = n^{−α} with α ∈ [0, 2/9), the right-hand side of the triangle bound tends to 0, hence d_W → 0.
  - Also check the 2/9 threshold from the bound. If the bound only goes to 0 for a different range of α, record a source issue.
- **P4. Disclose the metric in `Sec3_2_1_triangles_restricted`.** The docstring calls d_K at L936 a "typo". The printed claim is about d_K, and d_K ≤ d_W does not hold in general (only d_K ≤ (2/π)^{1/4}√d_W). Add one sentence: "the printed inequality for d_K is not established here; this entry proves the bound for d_W, which is what Theorem 3.5 yields." COVERAGE already records it that way.

## Process note

This is the second batch in which the builder's prose misquoted the TeX while its Lean code was right. The critic keeps re-reading the source for every source-issue claim.
