# Statement review: Track C (§4 opening, §4.1–4.2), drafts at `214f0d1`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1876–2112, re-read in full.
- **Scope:** statements only. Nothing is accepted into COVERAGE until the track's batch passes the full review.

## Verdict

The drafts are **approved with three required changes (C1–C3)**. Keep proving.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `poissonSteinClass` | 1881–1884 | Uses the sharp middle bound (1 − e^{−λ})/λ. The resulting class is a subset of the outer min{1, λ⁻¹} class. | matches "functions satisfying (4.2)" |
| `Thm4_5` | 1911–1916 | 0 < r is typing, since (4.2) divides by λ. Writing "mean λ" as `Integrable W` with ∫W = r is faithful. Because f is bounded, \|W f(W)\| ≤ ‖f‖W, so there is no junk value. Follows from accepted Cor 4.3 and Lem 4.4 (f_A(0) = 0 reading, ISSUE-4.4). | matches |
| `Sec4_1_binomial_limit` | 1938–1939 | "Not difficult to obtain a rate" is made explicit as min{1, λ}·λ/n, which is Thm 4.6 with p_i = λ/n. That is fine because it concludes more. Realizing W_n as a sum of independent indicators is equivalent to W_n ~ Bi(n, λ/n). | matches |
| `Thm4_6` | 1942–1949 | Both inequalities hold. At λ = 0, Lean's `min 1 0⁻¹ * 0` and the printed min{1, ∞}·0 both give 0. Requiring n > 0 is typing for max_i. | matches |
| `Thm4_7_corrected` | 1970–1977 | ISSUE-4.7 (accepted in review-02) is re-confirmed: X₁ ≡ 1, N₁ = ∅, RHS = 0 < 1 − e^{−1}. Adding i ∈ N_i is exactly what the proof at L1984–1996 uses. | correction accepted |
| `Rem4_1` | 1978–1981 | The remark is vague ("an additional error term that (roughly) measures dependence"). Reading it as the AGG b₃ term, Σ E\|E[X_i − p_i \| σ(X_j : j ∉ N_i)]\| times ‖f‖ ≤ min{1, λ^{−1/2}}, is a sound concrete reading. The constant comes from (4.2), not AGG's 1.4, and is legitimate because Lem 4.4 is proved. `Measurable (X i)` is present (junk-zero rule). | accepted as a reading; record the reading note in the docstring |
| `Thm4_8` | 2024–2030 | I checked the de-clumped indicators against L2013–2018, 0-indexed. The mean formula is a conclusion. I re-derived (4.8) from the Thm 4.7 bound: pairs with neither index 1 give ≤ q²(m−1)(2k+1) ≤ λ²(2k+1)/m, because 2(m−1)q·p^k ≥ (m−1)q²; pairs involving index 1 give ≤ 2λp^k. Here m = n − k + 1 and q = (1 − p)p^k. 1 ≤ k ≤ n is the domain of the definition at L2013–2021. | matches |
| `Rem4_2` | 2031–2037 | True with k real: p^k = p^c/(n(1 − p)), so λ → p^c, and the error is Θ(log n / n). | see C1 |
| `Sec4_2_1_longestRun` | 2054–2061 | (1) is exact equality of events. (2) is the right precise form of the "qualification": an integer threshold k_n with the bounded offset x_n in place of a fixed x, using P(R_n − L_n < x_n) = P(R_n < k_n) = P(W = 0). C may depend on p and M, and it comes before the universe-polymorphic ∀ Ω. | matches |
| `Thm4_9_corrected` and `not_Thm4_9_printed` | 2066–2078 | **ISSUE-4.9 is confirmed, and it is a new finding.** For 0 < a < p, the fourth-moment bound P(S_n < an) ≤ 48/n² (at p = 1/2, a = 1/4) and Borel–Cantelli give R_n = n eventually, so R_n/log n → ∞. Meanwhile H(1/4, 1/2) = ¾ log 3 − log 2 ≈ 0.1308 > 0. At a = p, H = 0. The correction 0 < p < a ≤ 1 is the Erdős–Rényi (1970) hypothesis. | correction accepted; machine-check the refutation as planned |
| `Rem4_3` | 2079–2110 | Matches indices are i.i.d. with P = Σ q_c². | matches; optional strengthening below |

## Required changes

- **C1. `Rem4_2`, integer k.** Theorem 4.8 needs an integer k. With k real, "λ → p^c" is literally true and matches the "Roughly" at L2033, so keep that conjunct and add a reading note saying k is treated as real there.
  - Also add the integer version that the rest of §4.2.1 actually uses: for integers k_n with bounded offset x_n = k_n − log(n(1 − p))/log(1/p), we have λ_n − p^{x_n} → 0 (in fact O(log n / n)), and (4.8) evaluated at k_n is O(log n / n).
  - With integer k_n, λ_n oscillates and has no limit unless x_n converges. The integer version is also the lemma `Sec4_2_1_longestRun` (2) needs.
- **C2. Index sanity checks for the new combinatorial definitions.** These are cheap and catch off-by-one errors in `headRunIndicator` and `longestQualityRun`.
  - Concrete evaluations, for example on y = 0110111 (n = 7):
    - `headRunCount 2 y = 2`
    - `headRunCount 3 y = 1`
    - `headRunCount 4 y = 0`
    - `longestQualityRun 1 y = 3`
    - `longestQualityRun (1/2) y = 7`
  - A lemma showing that, for 0/1 sequences, `longestQualityRun 1 y` is the longest run of ones, as the docstring claims.
- **C3. Docstring reading notes.**
  - `Rem4_1`: the b₃ reading and its constant source, as in the table above.
  - `Thm4_5`: the sharp-class choice and the r = 0 note, as in track file §3.1–3.2.
  - Record ISSUE-4.9 in SOURCE-ISSUES (lead) with the counterexample exactly as in track file §3.5.

## Optional

- `Rem4_3`: state the joint law directly, `P.map (fun ω i ↦ Y i ω) = Measure.pi (fun _ ↦ Bernoulli(p))`. This makes "exactly R_n" a one-line consequence.

## Notes for the lead

Theorem 4.9 is proved from scratch (Erdős–Rényi 1970). It needs exact-rate Chernoff bounds for both directions, plus a block or second-moment argument for the lower bound, so it is the largest item in Track C. Schedule it last within the track, and if it is not done when the rest is, let the rest land without it.
