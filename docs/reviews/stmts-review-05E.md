# Statement review: Track E (§6 geometric approximation), drafts at `44d6aa3`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L3190–3388, re-read in full.
- **Scope:** this reviews statements only. No proofs exist yet, and nothing is accepted into COVERAGE until the track's batch passes the full review: build, axiom audit, per-file re-elaboration and a mutation control.

## Verdict

The drafts are **approved with four required changes (E1–E4)**. Keep proving; none of the changes alters a theorem statement except E2, which adds an entry.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `Lem6_1_1` | 3229–3236 | Ge⁰(p) law, bounded f, 0 < p ≤ 1 as the parameter range of Ge⁰(p) | matches |
| `Lem6_1_2` | 3237–3238 | The printed "non-negative random variable" is read as ℕ-valued because f is defined on ℕ ∪ {0} (L3244); see the note below | matches under the reading note (ISSUE-6.1) |
| `Lem6_2` | 3243–3249, 3266–3273 | I re-derived the Δf_A formula. Uniqueness holds among all g with g(0) = 0: for p < 1 by recursion, for p = 1 directly. The tsum is summable since 0 ≤ 1 − p < 1. The bound in [−1, 1] holds because p Σ_{j≥0} (1 − p)^j = 1. | matches; it also covers the proof display (fine) |
| `Thm6_3` | 3251–3258 | `Integrable W` is the faithful reading of "E[W] = (1−p)/p" (junk-zero rule). For f ∈ F, \|f(k)\| ≤ k, so the Bochner integrand is integrable, with no junk value. | matches |
| `IsDiscreteEquilibrium` | 3283–3289 | Literal, with the setup conditions as conjuncts (as D7/D8 do). The test class "‖Δf‖ < ∞" is written as ∃ C. | matches |
| `Prop6_4` | 3292–3296 | Writing the joint law for "conditional on Wˢ, Wᵉ uniform on {0, …, Wˢ − 1}" is acceptable. It forces P(Wˢ = 0) = 0, which is automatic for p < 1 and is exactly what makes "uniform on ∅" meaningful at p = 1. | matches |
| `Rem6_2_restricted` | 3290–3291, 3304–3305 | I checked existence and uniqueness for p < 1 by taking f = 1[· ≥ j + 1], which gives Δf = 1[· = j]. At p = 1 uniqueness fails (ISSUE-6.4). | accepted as a restricted entry; see E3 |
| `Thm6_5` | 3312–3319 | Coupled on one space, `MemLp W 2`, and an ℝ≥0∞ right-hand side (junk-zero rule). I checked the proof route: (6.1) with f(0) = 0 gives the identity, and \|Δf(a) − Δf(b)\| ≤ 2·1[a ≠ b] ≤ 2\|a − b\|. | matches |
| `Thm6_6` | 3334–3350 | Node k (0-indexed) attaches uniformly to {0, …, k}. "The m nodes present" includes node m itself (L3339–3341), and the loop at node 0 counts once toward in-degree (L3335–3336). I is uniform and independent of G, which is the natural reading. | matches; see E1 for the junk-measure guard |
| `Sec6_opening_wasserstein_corrected` and `not_…_printed` | 3193–3198 | I re-derived the counterexample: p = 1/4, W ≡ 4, d_W(δ₁, Exp(1)) = 2/e, and E\|X − 4\| = 81/32. The left side is ≥ 81/32 − 1 > 1/4. The correction uses d_W(pX, pW) = p·d_W(X, W) and Example 5.4 (L2898: d_W(pN, Z) ≤ p). | ISSUE-6.0 confirmed; see E4 |

ISSUE-TYPO-6.2 (f in place of f_A at L3248) and ISSUE-TYPO-6.6 (W^{e₀} at L3382) are confirmed. The ISSUE-6.6 note is also correct: the proof actually gives H_n/n, a factor of 2 better than printed, and the printed bound follows from that. Record it as a note, not an error.

## Required changes

- **E1. Non-vacuity and junk-measure guards for the new definitions.** Each is a short lemma.
  - `geomLaw p {k} = (1 − p)^k p` and `IsProbabilityMeasure (geomLaw p)` for 0 < p ≤ 1. Do the same for `posGeomLaw`, with mass (1 − p)^{k−1} p at k ≥ 1.
  - `IsProbabilityMeasure (uniformAttachment n)` for 0 < n, plus the cylinder formula P(Adj u v) = 1/(u + 1) for v ≤ u and 0 for v > u.
    - This is the important one. `Measure.map` of a non-AEMeasurable map is the zero measure, which would make `Thm6_6` vacuous.
    - Also prove `Measurable digraphOfTargets`, or a `DiscreteMeasurableSpace` instance, for the new `Digraph` measurable space.
  - A witness for `IsDiscreteEquilibrium`: if W ~ Ge⁰(p) with 0 < p < 1, then Wᵉ ~ Ge⁰(p). This holds because P(W > k) = (1 − p)^{k+1}, so p/(1 − p) · P(W > k) = p(1 − p)^k.
- **E2. Missed prose claim, L3199–3200.** "If W =ᵈ kX for some positive integer k, then d_TV(W, X) ≈ (k − 1)/k."
  - Formalize this as a new entry `Sec6_supportMismatch`. For X ~ Ge(p) with positive support and an integer k ≥ 1:
    - the exact value is d_TV(kX, X) = 1 − p(1 − p)^{k−1} / (1 − (1 − p)^k), and
    - it tends to (k − 1)/k as p → 0⁺, i.e. as E[W] → ∞, which is the regime of the paragraph.
  - I derived the exact value by taking A = kℕ, which is optimal because kX puts more mass than X on every multiple of k. Re-check it before formalizing. If you read "≈" differently, say so in the track file.
- **E3. Rem6_2 reading note.** In the docstring and track file, say that Remark 6.2's "the same as that from renewal theory" is read as the stationary-excess formula P(Wᵉ = k) = P(W > k)/E[W].
  - The stationarity of the delayed renewal process Yᵉ + Y₁ + ⋯ (Remark 5.3, L2875–2879) is Track D's item and is not claimed here.
  - Also say that the existence and uniqueness part formalizes the prose at L3290–3291.
- **E4. Do not duplicate Example 5.4.** `Sec6_opening_wasserstein_corrected` needs d_W(pX, Z) ≤ p. That is Example 5.4, owned by Track D.
  - Lead: either have Track E import Track D's library theorem once it lands, or move ownership of the Ex 5.4 bound to one track and have the other import it.
  - Do not prove it twice (AGENTS.md rule 10). Until then, `not_Sec6_opening_wasserstein_printed` can land on its own.

## Reading note recorded for COVERAGE (no action)

Lemma 6.1(2) and Definition 6.1 say "non-negative random variable" without "integer-valued". Both are read as ℕ-valued because the test functions live on ℕ ∪ {0} (L3244). For Lemma 6.1(2) nothing is lost by this reading. With real-valued W and f : ℝ → ℝ, the hypothesis with f = 1_B (0 ∉ B) gives μ(B) = (1 − p)·μ(B − 1). By induction, W has no mass off ℕ, so the ℕ-valued statement is equivalent.
