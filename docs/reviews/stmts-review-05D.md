# Statement review: Track D (§5 opening, §5.1–5.2), drafts at `3e42dc7`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L2712–2984, re-read in full.
- **Scope:** statements only. Nothing is accepted into COVERAGE until the track's batch passes the full review.

## Verdict

The drafts are **approved with three required changes (D1–D3)**. Keep proving.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `Lem5_1_1` | 2726–2733 | Locally AC f (D5) with E\|f′(Z)\| < ∞. By Tonelli, f(Z) is then automatically integrable. | matches |
| `Lem5_1_2` | 2734–2736 | True, including the Lean junk value. The bounded C¹ test functions alone characterize Exp(1), and for those A f(W) is integrable. | matches; see the proof hint |
| `Lem5_2_formula`, `Lem5_2_ode_contAt` | 2740–2745, 2775–2779 | ISSUE-5.2-ODE is confirmed. For h = 1_{(−∞,1]}, Darboux rules out an everywhere-differentiable solution. Uniqueness follows from g(0) = 0 alone, via (e^{−x}(g − f_h))′ = 0. This is the same pattern as `Lem2_5_formula` and `Lem2_5_ode_contAt`. | accepted as far as true |
| `Lem5_2_1`, `Lem5_2_2` | 2747–2754 | The bounds hold on all of ℝ: \|h̃\| ≤ M because h and E h(Z) are both in [0, M]. | see D2 |
| `Thm5_3_1`, `Thm5_3_2` | 2758–2773 | Smooth classes (D6), which make the theorems stronger. I checked the smoothing routes: Steklov averaging for d_W, and ramp functions plus the Exp(1) density being ≤ 1 for d_K. Integrability holds since \|f(x)\| ≤ \|x\|. | matches |
| `IsEquilibrium` | 2836–2843 | Using Lean's `deriv` for Lipschitz f is harmless. Smooth f determine the law of Wᵉ, and that law turns out to be Lebesgue-AC (when μ > 0). | see D1 |
| `Sec5_1_equilibrium_ac` | 2844–2845 | The density is P(W > x)/μ on (0, ∞). | matches (μ > 0) |
| `Thm5_4` | 2847–2853 | The Bochner right-hand side is genuine here: E Wᵉ = E[W²]/2 < ∞. | matches; see the optional note |
| `Prop5_5_restricted` | 2863–2867 | — | see D1 |
| `Rem5_3` | 2875–2880 | Reads "stationary" as (i) renewal measure (b − a)/μ on (a, b] ⊂ [0, ∞) and (ii) the post-t epoch process having the same law. Both are standard. I checked (i) by Laplace transform, (1 − F̂)/(μs) · 1/(1 − F̂) = 1/(μs); it holds even if P(Y = 0) > 0. | accepted reading |
| `Ex5_4_ceil_corrected` | 2885–2886 | ISSUE-TYPO-5.4 is confirmed. "The smallest integer no greater than Z" does not exist. The ceiling reading matches the positive-support Ge(p) defined at L2884. | accepted; see the optional note |
| `Sec5_1_equilibrium_scale_restricted` | 2894 | c > 0 is needed for the law-identity reading. | accepted |
| `Ex5_4` | 2883–2900 | (ii) checked directly: the equilibrium density of N is p(1 − p)^{k−1} on (k − 1, k), which is the law of N − U. (iii) follows from Thm 5.4 with E[pU] = p/2. | matches |
| `Thm5_6` | 2905–2911 | The family over p is equivalent, since d_K depends only on the law. L¹ only, as printed. | matches |
| `Thm5_7_corrected` and `not_Thm5_7_printed` | 2915–2929 | ISSUE-5.7 (accepted in review-02) is re-confirmed. The proof at L2976–2980 needs (N, M) ⊥ (X_i), which the printed statement omits. ℝ≥0∞ moments and μ₂. | correction accepted; fix the arithmetic (D3) |
| `Rem5_5` | 2931–2947 | (i) P(V = m) = Σ_{k≥m} P(Nˢ = k)/k = P(N ≥ m)/μ. (ii) and (iii) are immediate. | matches |

Remark 5.6 gets a literature-pointer status line, which is accepted.

## Required changes

- **D1. Make `IsEquilibrium` literal, and drop the restriction on Prop 5.5.**
  - The `0 < ∫ W` conjunct came from **my** Batch 5 brief ("needs E X ∈ (0, ∞)"). That instruction was wrong and is withdrawn.
  - Definition 5.2 allows μ = 0. Ruling D8 kept `IsSizeBias` literal at μ = 0, and Track E's `IsDiscreteEquilibrium` allows the μ = 0 case (p = 1). Use the same convention here: keep `0 ≤ᵐ W` and `Integrable W`, and drop `0 < ∫ W`.
  - Under the literal definition, **Prop 5.5 is true with no restriction.** At μ = 0 every variable satisfies (5.3), because both sides are 0. State it as `Prop5_5`.
  - The μ = 0 degeneracy only breaks the prose claim at L2844–2845, that the equilibrium law is unique and AC. So `Sec5_1_equilibrium_ac` keeps its μ > 0 restriction.
  - Reword ISSUE-5.5: the failure is in the AC/well-definedness claim at μ = 0, not in Prop 5.5.
  - The scaling entry keeps c > 0.
- **D2. `deriv` junk in `Lem5_2_1` and `Lem5_2_2`.** Lean's `deriv` is 0 wherever f_h is not differentiable: at the jumps of h in 5.2(1), and at the corners of f_h′ in 5.2(2). At those points the drafted bounds are vacuous. Add conjuncts that hold everywhere:
  - `Lem5_2_1`: the left-derivative bound \|derivWithin f_h (Iic x) x\| ≤ 2M for all x, as in `Lem2_2_corrected`.
  - `Lem5_2_2`: `Differentiable ℝ (expSteinSol h)` and `LipschitzWith (2L) (deriv (expSteinSol h))`.
  - State the `deriv` caveat in both docstrings.
  - Add a SOURCE-ISSUES **proof note** for L2790–2791. "f_h is twice differentiable" is false: for h(t) = max(t, 0), f_h′ is −e^x for x < 0 and −1 for x ≥ 0, which has a corner at 0. The bound ‖f_h″‖ ≤ 2‖h′‖ survives as a Lipschitz bound on f_h′.
- **D3. Fix the `not_Thm5_7_printed` arithmetic before machine-checking it.** The track file says E[W] − 1 = (p/2)·E\|S_m − m\|. Conditioning correctly gives:
  - on {S_m < m}: E[Σ_{i≤N} X_i \| S_m, N] = N·S_m/m, by exchangeability;
  - on {S_m > m}: the sum is S_m + (N − m) in expectation.

  So **E[W] − 1 = (p/2)·E\|S_m − m\|·(1 − E[N \| G ≤ m]/m)**. With (1 − p)^m = ½, E[N \| G ≤ m]/m ≈ 1/ln 2 − 1 ≈ 0.443. At m = 4001, E\|S_m − m\| ≈ √(2m/π) ≈ 50.5, so E[W] − 1 ≈ 14.1p. That is still greater than 4p, so **the counterexample stands**. Correct the derivation in the track file and SOURCE-ISSUES so the Lean proof follows a true computation.

## Optional

- `Thm5_4`: write the right-hand side as `ENNReal.ofReal 2 * ∫⁻ ω, ENNReal.ofReal |We ω - W ω| ∂P`, or note in the docstring why the Bochner integral is genuine.
- `Ex5_4`: the typo admits a second fix, "the largest integer no greater than Z". Since §6 uses Ge⁰, you could add ⌊Z⌋ ~ Ge⁰(1 − e^{−λ}) next to the ceiling version. Also mention in the docstring that the prose claim at L2885 (pN converges weakly to Exp(1) as p → 0) follows from (iii).

## Proof hint for `Lem5_1_2`

The printed moment route (f(x) = x^k, then Carleman) fails in Lean. When W^k is not integrable, the Bochner integral is junk 0, so the hypothesis says nothing for that f. Use bounded C¹ test functions with bounded derivative, or the Laplace transform route the source also mentions (f(x) = e^{−sx}, s > 0, which is bounded on W ≥ 0).
