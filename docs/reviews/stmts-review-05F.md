# Statement review: Track F (§7 concentration), drafts at `382602b`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L3389–3887, re-read in full.
- **Scope:** statements only. Nothing is accepted into COVERAGE until the track's batch passes the full review.

## Verdict

The drafts are **approved with four required changes (F1–F4)**. Keep proving.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `Prop7_1` | 3411–3417 | Matches the printed statement. The strict `>` in the proof at L3421 is harmless. | matches |
| `Ex7_1` | 3428–3445 | Mills ratio, the MGF, and both displayed bounds. | matches |
| `Ex7_2` | 3447–3458 | The MGF, both displays, and B = o(e^{−ct}) for every c > 0 and every λ > 0. | matches |
| `Ex7_2_order_restricted` and `not_…_printed` | 3458 | **ISSUE-EX7.2 is confirmed.** log B + t log t = t(1 + log λ) − λ log t + O(1), so e^{−t log t} = o(B) holds iff λ > 1/e. I re-checked the numbers at λ = 0.1, t = 100: log B = −591.57 < −460.52. | correction accepted; see F2 |
| `Sec7_mgf_hasDerivAt` | 3464–3466 | Stated on (−δ, δ), which is more than the printed (0, δ). That is fine. | matches |
| `Thm7_2` | 3479–3489 | The sub-σ-algebra handling is right. (W′ − W)² is integrable because W ∈ L² and W′ has the same law as W. | see F1 |
| `Rem7_3` | 3490–3495 | BW + C ≥ 0 a.s., and W ≥ −C/B when B > 0. | matches |
| `Ex7_4_steinPair` | 3497–3501 | E[W′ \| X] = (1 − 1/n)W, so the same holds given σ(W). | matches |
| `Ex7_4_1` | 3503–3515 | I re-derived it: C = Σ(σ_i² + C_i²)/2 and B = 0. | see F1 for the Σ = 0 case |
| `Ex7_4_2_corrected` | 3516–3536 | **ISSUE-EX7.4 is confirmed.** Under the literal reading (centered W, μ = E W = 0), take n = 16 fair coins and t = 2: P(\|S − 8\| ≥ 2) = 29786/65536 ≈ 0.4545 > 2e^{−2} ≈ 0.271. The algebra at L3520 only works with μ = Σμ_i = E[S]. The correction states the intended bound for S. | correction accepted |
| `Ex7_5_steinPair_restricted` | 3597–3611 | ISSUE-TYPO-7.5 is confirmed: j is unbound at L3602; L3621 shows a_{iσ_i}. ISSUE-7.5 was accepted in review-02: at n = 2, W′ = −W, so a = 2 > 1, which violates D7. I re-derived the constant 2/(n − 1) from the transposition count. | restriction accepted |
| `Prop7_3` | 3612–3617 | I re-derived L3621–3623: (x)² ≤ 2\|x\| ≤ 2(sum of the entries) for entries in [0, 1], which gives B = 1 and C = (2/n)Σa. It holds for all n through the general-a library theorem (D7): n ≤ 1 is trivial, and at n = 2 I checked W² ≤ W + Σa directly. | matches |
| `Prop7_4` | 3645–3653 | Gibbs measure (7.6). I checked the proof constants: \|F\| ≤ 2, \|f − f′\| ≤ 2(1 + β)/n, the tanh averaging gap ≤ β/n, and P(f ≥ s) is obtained from the strict P(f > s) by continuity. | matches |
| `Thm7_5` | 3658–3676 | f is a measurable version of the regression function (needed to evaluate f(X′)). Integrability of F(X, X′) follows from θ = 0. | see F1 |
| `Thm7_6_corrected` | 3814–3826 | ISSUE-7.6 (t ≥ 0) was accepted in review-02. C > 0 and μ > 0 follow from σ² > 0, because X = Xˢ a.s. would force Var X = 0. | correction accepted |
| `Ex7_6_corrected` | 3878–3884 | **ISSUE-EX7.6 is confirmed.** By enumeration at n = 4, k = 2, p = ½: E X = 1, E X² = 9/4, so Var X = 5/4, while the printed formula gives 1. Each window has two neighbours at every lag r < k once n ≥ 2k − 1, which is where the factor 2 comes from. The coupling (force Y₁ = ⋯ = Y_k = 1) is a valid size bias by cyclic symmetry. | correction accepted; see F3 |

## Required changes

- **F1. The x/0 = 0 junk value in the Thm 7.2, Thm 7.5 and Ex 7.4(1) bounds.**
  - At C = 0, Lean evaluates `Real.exp (-t^2 / (2*C))` as exp(0) = 1, but the printed bound is exp(−∞) = 0. The printed claim is true there:
    - In Thm 7.2 with C = 0: B > 0 gives W ≥ 0 a.s.; B = 0 gives W′ = W a.s., hence W = 0.
    - In Thm 7.5 with C = 0: f(X) = 0 a.s., as the track's own note shows.
  - The same weakening happens in the upper-tail bound when B = C = 0, and in Ex 7.4(1) when Σ(σ_i² + C_i²) = 0.
  - As drafted, these entries are strictly weaker than the printed results at the boundary. Add explicit conjuncts for those cases, for example `C = 0 → P(W ≤ −t) = 0` and `B = 0 → C = 0 → P(W ≥ t) = 0`, and likewise for Thm 7.5 and Ex 7.4(1).
  - The alternative is a disclosed `_restricted` with 0 < C. The conjunct form is preferred because it states everything that is printed.
- **F2. Ex 7.2, add the charitable reading for every λ.** Add `Ex7_2_order_corrected`: for every λ > 0 and every c > 1, e^{−c·t log t} = o(B(λ, t)). This captures "decays more slowly than e^{−t log t} at the exponential-rate level" for all λ. Keep `Ex7_2_order_restricted` (λ > 1/e, c = 1) and `not_Ex7_2_order_printed`.
- **F3. Ex 7.6, do not over-restrict the tail bound.** μ and σ are already defined as the true mean and standard deviation, so the coupling claims (IsSizeBias, X ≤ Xˢ, \|Xˢ − X\| ≤ 2k − 1) and the tail bound hold for every n ≥ 1, k ≥ 1 and 0 < p < 1. Restructure:
  - the mean formula μ = np^k gets the hypothesis n ≥ k;
  - the corrected variance formula gets n ≥ 2k − 1;
  - the other conjuncts get no restriction on n.

  Keep `Ex7_6_variance_counterexample`. This states the printed tail bound in its full range and isolates the error to the formula at L3883.
- **F4. Prose claims in range.**
  - **Required** (cheap and precise), L3677–3681: if (W, W′) is an a-Stein pair, then F(W, W′) = (W − W′)/a gives E[F \| W] = W, and the condition of Thm 7.5 reduces to (7.1) with 𝓕 = σ(W). Add it as `Sec7_thm7_2_from_thm7_5`.
  - **Recommended**, L3640–3641: for β > 0 and h > 0, the all-(+1) configuration uniquely maximizes the Gibbs weight (7.6), and symmetrically for h < 0.
  - **Status lines** in the track file for the heuristic remarks at L3443–3444, L3459–3460, L3491–3494, L3528–3535 and L3873–3875.

## Notes

- The exercise status line for L3609–3610 is accepted; the Stein-pair facts are proved anyway, which is good.
- Thm 7.6 item 2: the minimizer θ* = t/(Cμ/σ² + Ct/(2σ)) is below 2σ/C, so it is in the admissible range. The printed proof is fine.
