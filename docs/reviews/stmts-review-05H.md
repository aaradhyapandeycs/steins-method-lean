# Statement review: Track H (§4.4 Poisson approximation by exchangeable pairs)

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L2606–2711, re-read in full.
- **Scope:** statements only.

## Verdict

The drafts are **approved with four required changes (H1–H4)**. Keep proving.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `Thm4_20` | 2618–2626 | The proof route (identity (4.3), then ‖f_A‖ ≤ min{1, λ^{−1/2}} from accepted Lem 4.4) is sound. "W′ = W − 1" is written correctly as `W = W' + 1`, which avoids ℕ truncation. | see H1 |
| `Rem4_18` | 2628–2631 | P(W′ = W + 1) = P(W′ = W − 1) follows from exchangeability. The "typically c ≈ …" part is heuristic and gets a status line. | matches |
| `Rem4_19` | 2633–2641 | Detailed balance λπ(k) = (k + 1)π(k + 1). | matches; see the optional note |
| `Thm4_20_antisym` | 2647–2650 | f is bounded. | matches |
| `Thm4_20_identity` (4.3) | 2651–2660 | — | see H2 |
| `Ex4_20` | 2663–2677 | Re-derived: with c = n, both expectations equal Σp_i², so the bound is 2 min{1, λ^{−1/2}}Σp_i². Pointwise 0/1 values match "indicators" literally. 0 < λ is typing. | matches; see H3 |
| `Ex4_21` and sub-claims | 2681–2702 | Re-derived both conditional probabilities by counting transpositions (a, π⁻¹(a)), with the 2-cycle case excluded. With c = (n − 1)/2: \|1 − (n − W − 2W₂)/n\| = (W + 2W₂)/n and \|W − W(n − W)/n\| = W²/n. So the bound is (1 + 1 + 2)/n = 4/n, using E W = 1, E W² = 2 and E W₂ = 1/2 for n ≥ 2. n ≥ 2 is typing (a transposition must exist). At n = 0 the Lean value 4/0 = 0 would make the entry false, so the hypothesis is needed. | matches; see H3 and H4 |

## Required changes

- **H1. Junk-zero in `Thm4_20`.** The theorem does **not** assume E W < ∞, and λ is not tied to E W.
  - If W is not integrable, then `∫ ω, |(W ω : ℝ) - c * …| ∂P` is the Bochner junk value 0. The right-hand side can then be small while d_TV is large, so **the drafted entry can be false**.
  - Write both expectations as `∫⁻ ω, ENNReal.ofReal |…| ∂P`, with the factor `ENNReal.ofReal (min 1 (r ^ (-1/2)))`. Then a non-integrable W gives ⊤, and the printed statement holds trivially in that case.
- **H2. `Thm4_20_identity` needs `Integrable (fun ω ↦ (W ω : ℝ)) P`.** E[W f(W)] in (4.3) needs E W < ∞. It is a proof sub-claim, not a printed theorem, so add the hypothesis and say so in the docstring.
- **H3. Add the "it is easy to see" coupling claims as entries.**
  - `Ex4_20_coupling` (L2664–2671): with I uniform and independent, and X′ an independent copy, (W, W′) is exchangeable, and both printed conditional probabilities hold given σ((X_i)).
  - `Ex4_21_coupling` (L2682–2688): with π uniform, τ a uniform transposition independent of π, and π′ = πτ, (W, W′) is exchangeable, and both printed conditional probabilities hold given σ(π).

  Both are substantive claims in the text, and the proofs need them anyway.
- **H4. Prose claim at L2702–2703:** "the true rate of convergence is much better than order 1/n".
  - Formalize it as `Ex4_21_true_rate`: n · d_TV(W, Po(1)) → 0, or the explicit bound d_TV ≤ 2ⁿ/n! (or any o(1/n) bound you can prove). Use the exact law P(W = k) = (1/k!) Σ_{j=0}^{n−k} (−1)^j/j!.
  - The claim is cited ([abt03]), so it is proved from scratch.
  - It may be listed under Deferred with a reason if it is too heavy now. Do not drop it.

## Optional

- `Rem4_19`: add the global-balance form, π(k)(λ + k) = λπ(k − 1) + (k + 1)π(k + 1) with π(−1) = 0. That is literally "stationary", and detailed balance implies it.
- Status lines for the heuristics at L2610–2617, L2629–2631 (choice of c), L2638–2641, L2678–2679 (the better bound is Thm 4.6, Track C) and L2705–2706.
- Record the L2645 typo (`\{1, \lambda^{-1}\}` should be `\min\{…\}`) as ISSUE-TYPO-4.20 for the lead to merge. It is a proof typo, separate from ISSUE-4.4.
- `iIndepFun (fun _ ↦ …) X P` is an older signature; current Mathlib takes `iIndepFun X P`.
