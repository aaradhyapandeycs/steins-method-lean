# Critic review 02: Batch 2 (Section 2, source-issue fixes, Prop 3.6(2))

- Reviewed: 2026-11-11, by the critic (Claude).
- Batch: `batch-02 f71de05637598376eb358baa0b7f25e442753f52` (commits `0959e7c`, `fe93f6b`, `819ded8`, `9304ab9`, `f71de05`).
- Inputs:
  - [`builder-report-02.md`](builder-report-02.md) and the Batch 2 [`NEXT-PROMPT.md`](NEXT-PROMPT.md).
  - [`review-01.md`](review-01.md) and `RULING-USER-2026-11-11` in [`../AUTHOR_RULINGS.md`](../AUTHOR_RULINGS.md).
  - `docs/source/SteinIntro_utf8.tex`, SHA-256 `2cb6fcad2e479c23bbd7a607f815003d33f5a07c030047088c1a582fe6a3bf4e`.

## Verdict

- **Batch 2 Lean work: accepted.**
  - My independent build, axiom audit, forbidden-token scan, wrapper check, axiom probe, per-file re-elaboration and mutation control all pass.
  - All nine new statement entries match the printed results (or the disclosed corrections), with no hidden hypotheses and no weakened conclusions.
  - They are now recorded in [`../COVERAGE.md`](../COVERAGE.md): 18 entries in total.
- **Part A (fixes from review-01): accepted.** Every item H1–H3, M1–M5 and L1–L5 is done as specified. The critic files were committed unchanged (`0959e7c`), and the accepted definitions are untouched.
- **`docs/SOURCE-ISSUES.md`: accepted for the entries listed below.** The rest are re-checked when their sections land.
- **Findings for Batch 3** are all low severity; nothing here blocks acceptance.
  - N1: ISSUE-2.2 overstates "refuting".
  - N2: the Lemma 2.5 preamble needs a continuity-point entry, and ISSUE-2.2 should cover it.
  - N3: ISSUE-3.6 should cite the remark at L1091.
  - N4: a coverage note on when Prop 2.4 is vacuous.

## Commands run by the critic (exact outputs)

All commands were run in `<local>` at `f71de05`, with a clean working tree. Before each Lean command I confirmed that no other `lake` or `lean` process was running.

```text
$ lake build
ℹ [3203/3204] Replayed Audit
info: Audit.lean:27:0: Axiom audit passed for 509 project declarations.
Build completed successfully (3204 jobs).
build-exit=0

$ lake env lean Audit.lean
Axiom audit passed for 509 project declarations.
audit-exit=0

$ python3 scripts/check.py        (tail)
Axiom audit passed for 509 project declarations.
Forbidden token check passed (0 hits outside comments/strings).
Statement wrapper check passed (all Statements/SecN.lean entries have _holds proofs).
check-exit=0
```

### Axiom probe

The probe imports `Formalization` and runs `#print axioms` on the following. Every one reports exactly `[propext, Classical.choice, Quot.sound]`.

- The nine new wrappers: `Lem2_1_1_holds`, `Lem2_1_2_holds`, `Lem2_2_corrected_holds`, `Cor2_3_corrected_holds`, `Prop2_4_holds`, `Lem2_5_formula_holds`, `Lem2_5_1_holds`, `Lem2_5_2_holds` and `Prop3_6_2_holds`.
- The machine-checked source issues: `Lem2_2_twoSided_noSolution`, `Cor2_3_twoSided_counterexample` and `not_differentiableAt_normalSteinSolKolm`.
- The non-vacuity witnesses: `isZeroBias_rademacher_uniform` and `exists_isZeroBias_rademacher`.
- The library facts: `integrable_mul_of_integrable_deriv_stdNormal` and `stdNormalExpect_indicator_Iic`.

`#check` confirms the shapes:
- `Lem2_2_twoSided_noSolution : ∀ x, ¬∃ f, ∀ w, HasDerivAt f (w * f w + (Set.Iic x).indicator 1 w - stdNormalCDF x) w`.
- `isZeroBias_rademacher_uniform : IsZeroBias bernoulliHalfMeasure rademacherVal uniformIccNegOneOne id`, where `uniformIccNegOneOne = 2⁻¹ • volume.restrict (Icc (-1) 1)`.

### Per-file re-elaboration (`lake env lean <file>`)

| File | Exit | Time | Warnings |
|---|---|---|---|
| `Normal/MillRatio.lean` | 0 | 4 s | 0 |
| `Normal/SolutionBounds.lean` | 0 | 5 s | 0 |
| `Normal/KolmogorovSolution.lean` | 0 | 3 s | 0 |
| `Normal/SteinLemma.lean` | 0 | 3 s | 0 |
| `Exchangeable/Basic.lean` | 0 | 2 s | 0 |
| `Defs/Sanity.lean` | 0 | 3 s | 0 |
| `Statements/Sec2.lean`, `Sec2Proofs.lean`, `Sec3.lean`, `Sec3Proofs.lean`, `Sec1Proofs.lean`, `Sec4Proofs.lean`, `Formalization.lean` | 0 | 2–3 s each | 0 |

**Mutation control.** In a scratch copy of `SolutionBounds.lean` I changed the conclusion of `abs_deriv_normalSteinSol_le_of_bounded` from `≤ 2 * M` to `≤ (3/2) * M`.
- `lake env lean` rejected it inside that proof (line 297) and again at the downstream use (line 697).
- So the short times above are real re-checks, not cache hits.
- The scratch copy was deleted. No builder file was touched.

## Statement-by-statement check against the TeX

I re-read L558–699 and L962–971. The line citations in every docstring are correct; they are slightly more precise than my Batch 2 prompt, whose line numbers were off by one or two.

| Entry | TeX | Verdict |
|---|---|---|
| `Lem2_1_1` | `lem1` item 1, L562–569 | **Proved, literal under D5.** The hypotheses are `P.map Z = stdNormalLaw`, f locally AC, and `Integrable (deriv f ∘ Z)`. The library also proves `Integrable (Z · f(Z))`, so the zero is not a junk value. |
| `Lem2_1_2` | `lem1` item 2, L570–574 | **Proved, literal under D5,** with no moment hypothesis. A Bochner junk zero only makes the Lean hypothesis easier to satisfy, so the Lean theorem implies the printed one. The proof tests against `f_h` for bounded continuous h (`exists_ac_normalSteinSol_of_continuous_bounded`), for which `𝒜f_h(W) = h(W) − Φ(h)` is bounded for every W. |
| `Lem2_2_corrected` | `lem2`, L578–588 | **Corrected (ISSUE-2.2).** Clauses (a)–(f) exactly as specified. The library also has `abs_normalSteinSolKolm_le` (‖f_x‖ ≤ √(π/2), L620–622). Clause (f) includes `Continuous`, closing finding H3. |
| `Cor2_3_corrected` | `cor1`, L591–596 | **Corrected (ISSUE-2.2).** Uses the left derivative, for every AEMeasurable W, with no integrability hypothesis. |
| `Prop2_4` | `prop31`, L665–670 | **Proved under D4, with the D1 guard on both sides** (critic spec, recorded in DEFINITIONS §5.2). See N4 for when the hypothesis can hold. |
| `Lem2_5_formula` | `lem31` preamble, L674–684 | **Proved for the clauses stated:** (i) the second representation for measurable, Gaussian-integrable h; (ii) the two-sided ODE everywhere for continuous h. See N2. |
| `Lem2_5_1` | `lem31` item 1, L686–689 | **Proved, literal.** "h bounded" is read as measurable h with \|h − Φ(h)\| ≤ M, for any M. The bound on `deriv` is the real derivative wherever f_h is differentiable, which is what ‖f_h'‖ means for a discontinuous h. |
| `Lem2_5_2` | `lem31` item 2, L690–694 | **Proved, literal.** This is CGS11 Lemma 2.4, which the source only cites, proved from scratch. For locally AC h, "\|deriv h\| ≤ L at every point" is equivalent to ‖h'‖_∞ ≤ L, because h is then L-Lipschitz. The printed constants 2, √(2/π) and 2 are all kept. |
| `Prop3_6_2` | `prop51` item 2, L967–971 | **Proved, literal.** "Var(W) = σ²" is read as `MemLp W 2 P`. The library theorem `steinPair_integral_eq_zero_and_sq_sub_eq` needs only 0 < a (D7). |

**Non-vacuity.** `isZeroBias_rademacher_uniform` shows that `IsZeroBias` is satisfiable: a ±1 Rademacher variable has zero-bias law Uniform[−1, 1]. Accepted.

## Part A (review-01 fixes)

Each item was checked against the TeX:

- **H1.** ISSUE-6.4 is withdrawn.
- **H2.** ISSUE-3.6 is rewritten correctly. I re-derived it:
  - E\|W′ − W\|³ = n^{−5/2} Σ E\|X_i − X_i′\|³ ≤ 8 n^{−5/2} Σ E\|X_i\|³.
  - With a = 1/n, Theorem 3.7's third-moment term is (n/3)·8 n^{−5/2} Σ = 8/(3 n^{3/2}) Σ.
  - This is at most 2/(3n) Σ exactly when n ≥ 16.
  - The first term √(2/π)·√(Σ E X_i⁴)/(2n) is correct as printed: Var(E[(W′ − W)²|X]) ≤ n^{−4} Σ E X_i⁴ (L1079–1086).
- **H3.** The counterexample h = e^{w²/2}·1_{(a,b]} is written out with all three cases.
- **M1.** ISSUE-3.5 now quotes √26 (L820) and Definition 3.1 verbatim, and points at the counting in (3.15), L882–894.
  - I re-checked the counterexample (X_{2r−1} = A_r, X_{2r} = S·A_r). Definition 3.1 holds with D = 2, and σ² = 2m.
  - The right side is O(m^{−1/2}), while W → ½δ₀ + ½N(0, 2).
- **M2–M5, L1–L5.** All done as specified.

`docs/SOURCE-ISSUES.md` is now **accepted** for these entries:
- ISSUE-2.1, 2.2, 3.5, 3.6, 3.10, 3.11, 3.19, 4.7, 4.17, 5.7, 5.9 and 7.6.
- The Part III notes ISSUE-3.22 and ISSUE-4.4.

I re-derived each of their counterexamples; the ISSUE-5.7 item 2 construction gives p·E[S_N] = Θ(√p) > 4p.

ISSUE-7.5, the ISSUE-3.25 note and the Part I typo entries are re-checked when §7 and §3.6 land.

## Findings (all low; fix in Batch 3, Part A)

- **N1. ISSUE-2.2 wording.** "Refuting Corollary 2.3 and Theorem 3.24 at W ≡ 0" overstates the point.
  - Under the two-sided reading, no f_x exists at all, by `Lem2_2_twoSided_noSolution`. The printed corollary therefore refers to an object that does not exist; it is not refuted.
  - What `Cor2_3_twoSided_counterexample` refutes is the transcription that uses `deriv` together with `normalSteinSolKolm`.
  - Say exactly that.
- **N2. Lemma 2.5 preamble.**
  - Lemma 2.5 calls f_h "the solution" of (2.6) for every bounded h (item 1). That includes indicators, for which Darboux rules out an everywhere two-sided solution: this is ISSUE-2.2 again.
  - The library already proves the ODE at every continuity point of h: `hasDerivAt_normalSteinSol (hInt) (hCont : ContinuousAt h w)`.
  - Add a new entry `Lem2_5_ode_contAt` for this, and keep `Lem2_5_formula` unchanged (accepted signatures stay frozen).
  - Extend ISSUE-2.2's "Source" list to Lemma 2.5 (L674–684) and the "f_h solve" premise of Proposition 2.4 (L659–663).
- **N3. ISSUE-3.6 corroboration.**
  - The remark at L1091, "if the X_i are i.i.d. then this term is of order n^{−1/2}", holds for the corrected bound but not for the printed one.
  - For i.i.d. X_i with Var X_i = 1, the printed second term is (2/3) E\|X₁\|³ ≥ 2/3 (by Lyapunov), which does not decay.
  - Add this as supporting evidence that the printed L1089 constant is a slip.
- **N4. Coverage note on Prop 2.4 (no action for the builder).** `Prop2_4` is vacuous when some h ∈ H admits no everywhere solution, e.g. the Kolmogorov indicators. That case is handled by `Cor2_3_corrected` and, later, `Thm3_24_corrected`. COVERAGE records this.

## Open user-overridable interpretations (unchanged from review-01)

1. `Lem4_4` reads f_A as Lemma 4.2's solution.
2. The D1 guard on the right side of Prop 2.4.

Both are recorded in COVERAGE and DEFINITIONS §5.
