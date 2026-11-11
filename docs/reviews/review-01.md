# Critic review 01: Batch 1 (setup repair, definitions, first proofs)

- Reviewed: 2026-11-11, by the critic (Claude).
- Batch: `batch-01 dab5e8560713cb0974d75f05193fedc8b05035b6` (commits `b04e808`, `c0b253e`, `4f25b83`, `dab5e85`).
- Inputs:
  - [`builder-report-01.md`](builder-report-01.md) and [`NEXT-PROMPT.md`](NEXT-PROMPT.md) (Batch 1).
  - `RULING-USER-2026-11-11` in [`../AUTHOR_RULINGS.md`](../AUTHOR_RULINGS.md).
  - `docs/source/SteinIntro_utf8.tex`, hash-verified by `scripts/fetch_source.py`.

## Verdict

- **Batch 1 Lean work: accepted.**
  - The build, axiom audit, forbidden-token scan and wrapper check all pass on my independent run.
  - All nine statement entries match the printed results, with no hidden hypotheses and no weakened conclusions.
  - The definitions conform to D1–D9.
  - These nine entries are now recorded as proved in [`../COVERAGE.md`](../COVERAGE.md). That file is critic-owned; the builder does not edit status there.
- **`docs/SOURCE-ISSUES.md`: not accepted yet.**
  - Several entries misquote the TeX.
  - Two "counterexamples" do not refute anything (ISSUE-6.4, ISSUE-3.6).
  - Three entries are classified as source issues but are not (ISSUE-3.22, ISSUE-2.5, ISSUE-5.7(3)).
  - These entries concern later sections, so they do not block the nine accepted results. They must be fixed before any `_corrected` or `_restricted` entry relies on them (Batch 2, Part A).
- **New critic finding F1:** under the left-derivative reading (D4), the uniqueness clause of Lemma 2.2 is false without continuity. `Lem2_2_corrected` must say so; specified in Batch 2.

## Commands run by the critic (exact outputs)

All commands were run in `<local>` at `dab5e85`. Before each Lean command I confirmed that no other `lake` or `lean` process was running.

```text
$ lake build
ℹ [3193/3194] Replayed Audit
info: Audit.lean:27:0: Axiom audit passed for 251 project declarations.
Build completed successfully (3194 jobs).

$ lake env lean Audit.lean
Axiom audit passed for 251 project declarations.

$ python3 scripts/check.py        (tail)
Axiom audit passed for 251 project declarations.
Forbidden token check passed (0 hits outside comments/strings).
Statement wrapper check passed (all Statements/SecN.lean entries have _holds proofs).

$ python3 scripts/fetch_source.py
Verified 1109.1880v1 (v1): 2 extracted files in source/upstream/, 2 downloads, and 1 normalized UTF-8 file(s).
$ python3 scripts/generate_inventory.py --check
Inventory check passed: 43 headings, 122 numbered environments, 328 display rows (186 labels).

$ grep -rnwE 'sorry|admit|axiom|native_decide|opaque|implemented_by|extern|unsafe|skipKernelTC' Formalization Formalization.lean Audit.lean
Audit.lean:16 / :53 / :56   (docstring and error-message strings only)
```

**Axiom probe.** An untracked file outside the repo imports `Formalization` and runs `#print axioms` on every `_holds` theorem and four sanity lemmas. All 13 depend on `[propext, Classical.choice, Quot.sound]` only.

**Re-elaboration from source.** `lake build` only replayed cached results, so I also elaborated each `Formalization/**/*.lean` file and `Formalization.lean` with `lake env lean <file>`, one file at a time. The result is in "Re-elaboration log" at the end of this review.

**Audit design.** I read the new `Audit.lean`. It is module-based and walks `Formalization/` on disk. It rejects `opaque`, allows only the three axioms, and fails when it finds zero declarations. The builder's two negative probes (an unimported module, and an `axiom` outside `SteinMethod`) were reported failing as expected. This closes review-00 B2.

## Accepted statement entries

| Entry | Source | Notes |
|---|---|---|
| `Prop1_2_1` | Prop 1.2(1), `prop22`, L523–526 | Literal. |
| `Prop1_2_2` | Prop 1.2(2), L527–531 | Literal. A density `f` with `f ≤ ofReal C` a.e. and `P'.map Z = volume.withDensity f`. No moment hypothesis (D1). |
| `Prop1_2_3` | Prop 1.2(3), L532–537 | Literal. "Discrete space" is rendered as countable with measurable singletons, so every subset is measurable. |
| `Prop3_6_1` | Prop 3.6(1), `prop51`, L962–971 | Literal. No integrability hypothesis; the non-integrable case is the junk-symmetric case, which is at least as strong as the source. |
| `Lem4_1_1`, `Lem4_1_2` | Lemma 4.1, `lem101`, L1823–1835 | Literal. In item 2, a non-integrable `𝒜f(W)` makes the hypothesis weaker, so the Lean theorem is at least as strong as the source. |
| `Lem4_2` | Lemma 4.2, `lem102`, L1837–1848 | Literal. I checked the formula against L1843–1846: U_{k+1} = `Set.Iio (k+1)`. |
| `Cor4_3` | Cor 4.3, `cor101`, L1850–1855 | Literal: it carries the printed "mean λ", which the library theorem does not need. `0 < r` is the typing of f_A (λ^{-k}). |
| `Lem4_4` | Lemma 4.4, `lem103`, L1879–1886 | Accepted under the reading that f_A is Lemma 4.2's solution, with f_A(0) = 0 (see finding M5). Proves the bounds for every k ≥ 0, including Δf_A(0). |

The definitions (M1) are accepted.
- I checked D1–D3 (metrics), D4–D6 (normal Stein objects), D7 (`IsSteinPair`) and D8 (`IsSizeBias`) against the ruling specs; they match.
- D9 (`IsZeroBias`) is the corrected class. I re-derived the builder's H4 counterexample (ISSUE-3.10) and it is correct: p_W = (3/2)|w|^{-4} on |w| ≥ 1, p^z = 1/4 on [−1,1] and 1/(4u²) outside, and f = (1 − cos(w²−1))·1{w>1} gives ∫|f'|p^z = (1/4)∫_0^∞ |sin v|/(v+1) dv = ∞. H4 is confirmed.
- Under the corrected class, existence still holds: for σ² > 0, the Fubini proof needs exactly ∫|f'|p^z < ∞. Uniqueness also holds, testing with f = ∫_{-∞}^w g for g ∈ C_c.
- The builder correctly caught an error in my Batch 1 prompt. With W' = −W, E[W'|W] = −W means a = 2, not a = 1. The independent Rademacher pair with a = 1 is a valid witness.

## Findings (ranked)

### High

- **H1. ISSUE-6.4 is not a counterexample; withdraw it.**
  - At p = 1, the right side of (6.1) (L3285–3287) is (1 − p)·E[Δf(W^e)] = 0. The left side is p·E f(W) − p·f(0) = 0, because W ≡ 0.
  - So every W^e is a discrete-equilibrium variable, and Proposition 6.4 holds at p = 1 whenever its hypothesis can be met. If W^s ≡ 0, the hypothesis cannot be met, and the proposition is vacuously true.
  - `Prop6_4` is stated literally with 0 < p ≤ 1. There is no `_restricted` variant.
- **H2. ISSUE-3.6 misquotes L1089, and its "counterexample" refutes nothing.**
  - The printed final term is `\frac{2}{3n}\sum E|X_i|^3`, not 2/(3√n). Moreover, an upper bound that tends to ∞ cannot be a counterexample.
  - What is wrong is a proof step. At L1074, E|W'−W|³ is missing a factor 1/n (I is uniform). The printed final constant also does not follow from the printed intermediate bound: that would give 8/(3√n).
  - The correct derivation via Theorem 3.7 gives a second term of at most (8/(3n^{3/2}))∑E|X_i|³. That implies the printed (2/(3n))∑E|X_i|³ for n ≥ 16.
  - Record the status honestly: the printed bound is proved for n ≥ 16 by the corrected derivation; for n < 16 it is **open**, neither proved nor refuted.
  - When Example 3.6 is formalized, prove the sharper bound and derive the printed one for n ≥ 16. Name that entry `Ex3_6_restricted` (n ≥ 16), plus `Ex3_6_corrected` for the 8/(3n^{3/2}) form.
- **H3 (new, critic). Lemma 2.2 uniqueness fails under the left-derivative reading without continuity.**
  - Take h(w) = e^{w²/2}·1_{(a,b]}(w). It is bounded and left-differentiable everywhere, with left derivative w·h(w) at every w. The check at w = b uses the smooth branch; at every other point h is locally constant or smooth.
  - So f_x + h is a second bounded solution of the left-derivative equation (2.1).
  - Uniqueness holds among bounded **continuous** functions. The argument: if g − f_x is continuous with a continuous left derivative, then it is differentiable. It then equals C·e^{w²/2}, and boundedness forces C = 0.
  - The hypothesis must also be a genuine one-sided derivative (`HasDerivWithinAt … (Set.Iic w) w`), not the junk-prone `derivWithin` equation.
  - Add this to ISSUE-2.2. `Lem2_2_corrected` is specified in Batch 2.

### Medium

- **M1. ISSUE-3.5 misquotes the source.**
  - Theorem 3.5 prints √26 (L820), not √28.
  - Definition 3.1 (L805–809) does **not** require i ∈ N_i.
  - The proof gap is in the counting at L882–894: Definition 3.1 alone does not make {X_i, X_k} independent of {X_j, X_l} outside a bounded number of index tuples. Ross does not assert that independence outright.
  - The counterexample itself is correct; I verified the independence claims, σ² = 2m, and the right-hand side being O(m^{-1/2}).
- **M2. ISSUE-4.7's resolution says "matching Definition 3.1".** Definition 3.1 has no i ∈ N_i, and Theorem 4.7 prints `N_i/\{i\}` (L1975). The counterexample (N_1 = ∅, X_1 ≡ 1) is correct. Reword the resolution: "adds `∀ i, i ∈ N i`, which the proof at L1984–1996 uses".
- **M3. ISSUE-4.17 misquotes the hypothesis.**
  - The printed text is "X_1, …, X_n are increasing or decreasing functions from {0,1}^N into {0,1}" (L2384–2385). Definition 4.9 (L2377–2380) defines increasing and decreasing; it does not say "coordinate-wise monotone".
  - The issue is an ambiguity: each X_i monotone in its own direction, versus all in the same direction. The counterexample refutes the first reading.
  - Keep `Thm4_17_corrected` (all in the same direction), and say that it is one of the two readings.
- **M4. ISSUE-3.22 is misclassified.**
  - Theorems 3.22 and 3.23 hypothesise that X^z_{i,n} "have the zero-bias distribution of X_{i,n}". Under Definition 3.10 that already includes E[X_{i,n}] = 0.
  - The literal statements, with `IsZeroBias` hypotheses, are therefore correct as printed. Name them `Thm3_22` and `Thm3_23`, not `_corrected`.
  - The counterexample targets the unnumbered prose at L1558–1561, where "satisfy a CLT" is ambiguous for non-centred W_n. Keep it as a prose note only.
- **M5. ISSUE-4.4 and the entry name `Lem4_4`.**
  - The entry is accepted as `Lem4_4` because "f_A" at L1880 denotes Lemma 4.2's solution, which has f_A(0) = 0 (L1840–1843).
  - Rewrite ISSUE-4.4 as a reading note: "Under the alternative reading 'any solution of (4.1)', the claim fails at k = 0 (counterexample g(0) = 2). The formalization uses the Lemma 4.2 reading."
  - The user may overrule this and ask for `Lem4_4_restricted` instead.

### Low

- **L1. Not source issues.** Move each of these to a "Formalization notes" section of `docs/DEFINITIONS.md`, or mark it "formalization note — not a source error".
  - **ISSUE-2.5.** With ‖h'‖ = ∞, the printed bounds hold trivially in [0, ∞]. `∀ L, (∀ t, |deriv h t| ≤ L) → …` is the literal statement, so the entry name is `Lem2_5_2`, not `_restricted`.
  - **ISSUE-5.7 item 3.** Lean junk values are an encoding matter.
- **L2. Proof wrappers are in the wrong place.** The `SecNProofs.lean` files live in `Formalization/` rather than `Formalization/Statements/`. Move them to `Formalization/Statements/SecNProofs.lean`, as AGENTS.md rule 5 and the RL site tooling that M12 will port expect. Update `Formalization.lean` and `scripts/check.py`.
- **L3. The audit can skip a check silently.** `Audit.lean` skips the on-disk module check when `Formalization/` does not exist relative to the working directory. Make it throw instead, so the audit cannot pass from the wrong directory.
- **L4. The README is out of date.** "no source result is fully formalized yet" is no longer true. Point to `docs/COVERAGE.md` and keep the incomplete-status banner.
- **L5. Small drift in `docs/DEFINITIONS.md`.** §4.1 shows `[m₀ : MeasurableSpace Ω]`, but the code has `[MeasurableSpace Ω]`.

## Not checked

- I did not repeat the builder's negative audit probes myself. Doing so needs a temporary import in `Formalization.lean`, which is the builder's file. The audit logic is short and I read it in full.
- I did not check the Part I typo entries line by line, beyond the three from review-00 M6.

## Decisions for the user

None blocking. Two critic interpretations are recorded and can be overruled:
- **M5.** `Lem4_4` is stated for Lemma 4.2's f_A.
- **The supremum in Proposition 2.4 (Batch 2).** It uses the same integrability guard as `ipm` (D1), so both sides of (2.5) range over the same test functions.

## Re-elaboration log

Format: `exit-code wall-time file error/warning-count`. Every file passed with no errors or warnings.

```text
0 17s Formalization/Defs.lean 0
0 3s Formalization/Defs/Couplings.lean 0
0 2s Formalization/Defs/Laws.lean 0
0 2s Formalization/Defs/Metrics.lean 0
0 3s Formalization/Defs/NormalStein.lean 0
0 2s Formalization/Defs/PoissonStein.lean 0
0 2s Formalization/Defs/Sanity.lean 0
0 3s Formalization/Exchangeable/Basic.lean 0
0 2s Formalization/Metrics/Basic.lean 0
0 4s Formalization/Poisson/SteinBounds.lean 0
0 2s Formalization/Poisson/SteinCore.lean 0
0 2s Formalization/Poisson/SteinLemma.lean 0
0 3s Formalization/Sec1Proofs.lean 0
0 2s Formalization/Sec3Proofs.lean 0
0 3s Formalization/Sec4Proofs.lean 0
0 2s Formalization/Statements/Sec1.lean 0
0 2s Formalization/Statements/Sec3.lean 0
0 3s Formalization/Statements/Sec4.lean 0
0 2s Formalization.lean 0
```

Control: a scratch copy of `Poisson/SteinBounds.lean` with `example : (1:ℕ) = 2 := rfl` appended fails with a type error after 5.5 s, so `lake env lean` really re-checks every proof in the file. There are no `#exit`, `set_option`, custom syntax or `run_cmd` in `Formalization/`.
