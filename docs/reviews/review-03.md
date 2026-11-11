# Critic review 03: Batch 3 (Sections 3.1–3.3, Part A fixes, stretch items C.1–C.3)

- Reviewed: 2026-11-11, by the critic (Claude).
- Batch: `batch-03 1952be2577632c60ffce642c4ee526d5480b4df7` (commits `d57a5d8`, `9b2c47c`, `93ae7a8`, `8db0580`, `1952be2`).
- Inputs:
  - [`builder-report-03.md`](builder-report-03.md) and the Batch 3 [`NEXT-PROMPT.md`](NEXT-PROMPT.md).
  - [`review-02.md`](review-02.md) and `RULING-USER-2026-11-11` in [`../AUTHOR_RULINGS.md`](../AUTHOR_RULINGS.md).
  - `docs/source/SteinIntro_utf8.tex`, SHA-256 `2cb6fcad2e479c23bbd7a607f815003d33f5a07c030047088c1a582fe6a3bf4e`.

## Verdict

- **Batch 3 Lean work: accepted.**
  - My independent build, axiom audit, forbidden-token scan, wrapper check, axiom probe, per-file re-elaboration and mutation control all pass.
  - All 14 new statement entries match the printed results or their disclosed corrections. There are no hidden hypotheses and no weakened conclusions, and every printed constant is kept, including √26 in Theorem 3.5.
  - They are now recorded in [`../COVERAGE.md`](../COVERAGE.md): 32 entries in total, 5 of them disclosed corrected or restricted variants.
- **Part A (N1–N3 from review-02): accepted.**
  - The critic files were committed unchanged (`d57a5d8`).
  - `Lem2_5_ode_contAt` is verbatim as specified.
  - `Lem2_5_formula` and every other accepted signature is unchanged (checked with `git diff d57a5d8 1952be2`).
- **New definitions `HasDependencyNeighborhoods` and `IsDependencyGraph`: accepted.** Both are verbatim as specified.
  - In `IsDependencyGraph`, the sets A and B are automatically disjoint: if a ∈ A ∩ B then a ∈ N a, which violates the separation hypothesis.
- **Updated source issues ISSUE-2.2, ISSUE-3.5 and ISSUE-3.6, and the new reading note ISSUE-3.3: accepted.**
- **Machine-checked refutation of the printed Theorem 3.5 (`not_Thm3_5_printed`): accepted.** It holds even with i ∈ N_i assumed.
- **Findings for Batch 4** are both low severity; nothing here blocks acceptance.
  - P1: two corrected-entry docstrings should say how they differ from the printed result.
  - P2: a coverage note about Remark 3.5.

## Commands run by the critic (exact outputs)

All commands were run in `<local>` at `1952be2`, with a clean working tree. Before each Lean command I confirmed that no other `lake` or `lean` process was running.

```text
$ lake build
ℹ [3244/3245] Replayed Audit
info: Audit.lean:27:0: Axiom audit passed for 795 project declarations.
Build completed successfully (3245 jobs).
build rc=0

$ lake env lean Audit.lean
Axiom audit passed for 795 project declarations.
audit rc=0

$ python3 scripts/check.py        (tail)
Axiom audit passed for 795 project declarations.
Forbidden token check passed (0 hits outside comments/strings).
Statement wrapper check passed (all Statements/SecN.lean entries have _holds proofs).
check-exit=0
```

### Axiom probe

The probe imports `Formalization` and runs `#print axioms` on 19 constants. Every one reports exactly `[propext, Classical.choice, Quot.sound]`.

- **The 14 new wrappers:** `Lem2_5_ode_contAt_holds`, `Sec3_dK_le_dW_holds`, `Thm3_1_holds`, `Thm3_2_holds`, `Lem3_3_holds`, `Lem3_4_holds`, `Thm3_5_corrected_holds`, `Thm3_7_holds`, `Lem3_9_holds`, `Ex3_6_steinPair_holds`, `Ex3_6_corrected_holds`, `Ex3_6_restricted_holds`, `Rem3_3_holds` and `Rem3_4_holds`.
- **The source-issue witnesses:** `Thm3_5_counterexample` and `not_Thm3_5_printed`.
- **Library theorems:** `IsDependencyGraph.hasDependencyNeighborhoods`, `steinPair_iSup_normalWassersteinClass_le` and `depGraph_variance_quadSum_le`.

`#check` confirms the shapes. Two of them:
- `steinPair_iSup_normalWassersteinClass_le` needs only `0 < a` (D7), measurable W, the linearity condition `P[W' | σ(W)] =ᵐ (1 − a)W`, and `∫ W² = 1`.
- `depGraph_variance_quadSum_le` proves Var(Σ_i Σ_{k∈N_i} X_i X_k) ≤ 8 D³ Σ E X_i⁴. This is sharper than the source's 13 D³, and the printed √26 = √2·√13 is kept by weakening 8 to 13 at the very end.

### Per-file re-elaboration (`lake env lean <file>`)

| File | Exit | Time | Warnings |
|---|---|---|---|
| `Defs/Dependency.lean` | 0 | 2 s | 0 |
| `Normal/WassersteinBound.lean` | 0 | 4 s | 0 |
| `Normal/IndependentSums.lean` | 0 | 4 s | 0 |
| `Normal/DependencyCount.lean` | 0 | 4 s | 0 |
| `Normal/DependencyNeighborhoods.lean` | 0 | 4 s | 0 |
| `Normal/DependencyCounterexample.lean` | 0 | 4 s | 0 |
| `Exchangeable/SteinPairBound.lean` | 0 | 4 s | 0 |
| `Exchangeable/IndepSumPair.lean` | 0 | 3 s | 0 |
| `Exchangeable/IndepSumPairBounds.lean` | 0 | 3 s | 0 |
| `Statements/Sec2.lean`, `Sec2Proofs.lean`, `Sec3.lean`, `Sec3Proofs.lean`, `Formalization.lean` | 0 | 2–3 s each | 0 |

**Mutation control.** I changed one constant in each of two scratch copies.
- In `DependencyCount.lean` L540, I changed `13 * D ^ 3` to `7 * D ^ 3`. `lake env lean` rejected it at L688 (`linarith failed`).
- In `DependencyNeighborhoods.lean` L411, I changed `Real.sqrt 26` to `Real.sqrt 25`. It was rejected at L412 (`unsolved goals`) and again at L462.
- So the short times above are real re-checks, not cache hits. The scratch copies live in the critic's scratch area; no builder file was touched.

## Statement-by-statement check against the TeX

I re-read L700–1136. The line citations in every docstring are correct.

| Entry | TeX | Verdict |
|---|---|---|
| `Lem2_5_ode_contAt` | `lem31` preamble, L674–684 | **Proved,** verbatim as specified. With `Lem2_5_formula`, this completes the Lemma 2.5 preamble as far as it is true (ISSUE-2.2). |
| `Sec3_dK_le_dW` | prose display, L703–707 | **Proved, literal.** It follows from Prop 1.2(2) with C = 1/√(2π): √(2C) = (2/π)^{1/4}. W is any AEMeasurable random variable. |
| `Thm3_1` | `thm31`, L719–724 | **Proved, literal under D6, with no moment hypothesis.** A Bochner junk zero on the right side (when W·f(W) is not integrable) only makes the Lean right side smaller, so the Lean theorem is at least as strong as the printed one. For integrable W the D1 guard admits every 1-Lipschitz h, so the left side is the true d_W. |
| `Thm3_2` | `thm32`, L736–742 | **Proved, literal.** "E\|X_i\|⁴ < ∞" is `MemLp (X i) 4`. `0 < n` is the non-empty-family typing condition (DEFINITIONS §5.5). The constants 1 and √2/√π are kept. All right-side Bochner integrals are of L¹ functions, so there is no junk zero. The `AEMeasurable (X i)` hypothesis is implied by `MemLp`, so it is redundant and harmless. |
| `Lem3_3` | `lem33`, L753–759 | **Proved under the context reading (ISSUE-3.3).** The printed lemma states no regularity for f; the context at L750–751 says "bounded f with bounded first and second derivative". The entry assumes less (f differentiable, with f and f′ bounded). W_i uses j ≠ i (ISSUE-TYPO-3.3). All three expectations are genuine integrals. |
| `Lem3_4` | `lem33aa`, L771–776 | **Proved, literal.** Every pair of bounds B₁ ≥ ‖f′‖ and B₂ ≥ ‖f″‖ is allowed. The left side is a genuine integral (f′ bounded, W ∈ L¹, f bounded). |
| `Thm3_5_corrected` | `thm41`, L815–822 | **Corrected (ISSUE-3.5).** The hypothesis is upgraded from dependency neighbourhoods (Definition 3.1) to a dependency graph (L810–812, the notion the proof's counting at L882–894 uses). `0 < Var(Σ X_i)` is well-definedness, since the source divides by σ. D = max \|N_i\| and the bound with √26 are exactly as printed. `not_Thm3_5_printed` refutes the printed version (see below). See P1 for the docstring. |
| `Thm3_7` | `thm51`, L983–988 | **Proved, literal under D7, with ℝ≥0∞ moments.** `∫ W² = 1` forces W ∈ L², so W′ ∈ L² by exchangeability and (W′ − W)² is integrable. Hence the conditional expectation is genuine; the ℝ≥0∞ forms only guard the case E\|W′ − W\|³ = ∞, where the right side is ∞. |
| `Rem3_3` | remark, L990–999 | **Proved.** "Markov chain in stationarity, reversible w.r.t. μ" is encoded as `(μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ`, which is detailed balance and implies stationarity. |
| `Rem3_4` | remark, L1000–1008 | **Proved, generalised.** It is stated for any integrable Y and σ-algebras m₁ ≤ m₂ in ℝ≥0∞. It implies the printed (W′ − W)² instance with m₁ = σ(W). |
| `Ex3_6_steinPair` | example, L1053–1069 | **Proved, literal.** This includes the exchangeability that the source leaves as "a simple exercise" (L1061), since `IsSteinPair` contains `IsExchangeablePair`. "Choosing an index uniformly at random" is read as I independent of (X, X′). |
| `Ex3_6_corrected` | example, L1053–1097 | **Corrected (ISSUE-3.6).** I re-derived both terms. The first term, n·√(n⁻⁴ Σ E X_i⁴)/√(2π) = √(2/π)·√(Σ E X_i⁴)/(2n), equals the printed one. The second, (n/3)·8 n^{−5/2} Σ E\|X_i\|³, is the corrected 8/(3 n^{3/2}). See P1. |
| `Ex3_6_restricted` | L1089 | **Restricted (ISSUE-3.6):** the printed bound for n ≥ 16. The case n < 16 stays open. |
| `Lem3_9` | `lem51`, L1133–1136 | **Proved, literal.** W and W′ are ℤ-valued, identically distributed, with \|W′ − W\| ≤ 1 almost surely. |

### Theorem 3.5 counterexample, re-derived

Take A_1, …, A_m, S i.i.d. Rademacher, X_{2r−1} = A_r, X_{2r} = S·A_r and N_{2r−1} = N_{2r} = {2r−1, 2r}.

- **Definition 3.1 holds.** S·A_r is independent of (A_s, S·A_s)_{s≠r}: that vector determines S, and given S, S·A_r is a fresh Rademacher. The case of A_r is clear.
- **The variance is σ² = 2m.** The summands are uncorrelated, since X_{2r−1}X_{2r} = S.
- **The left side is bounded below.** Σ X_i = (1 + S)·Σ A_r, so W = 0 when S = −1, and otherwise W = √2·Σ A_r/√m. By Jensen, E\|W\| ≤ ½·√2·1 = 1/√2. Testing against h = \|·\| gives d_W ≥ √(2/π) − 1/√2 ≈ 0.0908.
- **The right side is smaller.** At m = 10⁴ it is 4/√(2m) + √26·2^{3/2}/(√π·√(2m)) ≈ 0.0283 + 0.0575 = 0.0858 < 0.0908.
- **The Lean statement matches.** It quantifies over the printed hypotheses plus i ∈ N_i (universe 0, which suffices for a refutation).

## Findings (both low; fix in Batch 4, Part A)

- **P1. Corrected-entry docstrings.** AGENTS.md says a corrected entry's docstring "states how it differs from the printed result".
  - Add one sentence to `Thm3_5_corrected`: the hypothesis is strengthened from Definition 3.1 to a dependency graph, because the printed theorem is false (`not_Thm3_5_printed`, ISSUE-3.5).
  - Add one sentence to `Ex3_6_corrected`: the printed second term is 2/(3n)·Σ E\|X_i\|³ (L1089); it is replaced by 8/(3 n^{3/2})·Σ E\|X_i\|³ (ISSUE-3.6).
  - Change docstrings only; signatures stay frozen.
- **P2. Remark 3.5, the O-U heuristic at L1009–1024 (no action this batch).** COVERAGE records it as open. Its factual content is:
  - The O-U transition satisfies properties 1–3.
  - Properties 1–3 determine the process.
  - The process is reversible with N(0, 1) stationary.

  The first and third can be stated for the explicit Mehler transition. The second needs diffusion theory that is not in Mathlib. A later batch will propose a scope for the user.

## Open user-overridable interpretations

1. `Lem4_4` reads f_A as Lemma 4.2's solution (unchanged).
2. The D1 guard on the right side of Prop 2.4 (unchanged).
3. **New:** `Thm3_5_corrected` uses the dependency-graph hypothesis.
   - Weaker local-dependence conditions might also suffice for the √26 bound, for example the pairwise condition (LD2) of Chen–Goldstein–Shao that an earlier ISSUE-3.5 draft proposed.
   - The dependency graph is what the source's own prose (L810–812) and proof (L882–894) use, so it was chosen.
