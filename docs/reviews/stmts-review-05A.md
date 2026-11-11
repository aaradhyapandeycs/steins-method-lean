# Statement review: Track A (§3.5 zero bias), drafts at `4ed69e1`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1437–1648, re-read in full.
- **Scope:** statements only. Nothing is accepted into COVERAGE until the track's batch passes the full review.

## Verdict

The drafts are **approved with four required changes (A1–A4)**. Keep proving.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `Sec3_5_zeroBias_fixedPoint` | 1450–1451 | Including v = 0 is required, because W ≡ 0 is a fixed point under D9. For v > 0 the left side follows from Stein's lemma with dual integrability. The right side is the characterization, with σ² = 0 giving δ₀. | matches ("unique fixed point" read up to variance, the degenerate normal included) |
| `Thm3_18` | 1454–1461 | ℝ≥0∞ right-hand side (junk-zero rule). I checked the proof route: Lemma 2.5 gives ‖f_h‖ ≤ 2 and bounded f_h′, so the D9 integrability conditions hold for f_h. | matches |
| `Prop3_19_corrected` | 1471–1485 | ISSUE-3.19 (σ² > 0) was accepted in review-02. Existence under D9 is fine: Tonelli applies on {u > 0}, since E[W 1{W > u}] ≥ 0 there, and symmetrically on {u < 0}. | correction accepted |
| `Prop3_20_restricted` | 1519–1520 | The counterexample is valid. At a = 0, Var(aW) = 0, so Y ≡ 1 is a zero-bias of 0·W. | see A3 |
| `Prop3_21` | 1530–1551 | Assuming only "X_iᶻ ⊥ (X_j)_{j≠i}" assumes **less** than printed (Items 1–2), so the entry implies the printed proposition. | matches; see A4 |
| `Sec3_5_2_lindeberg_not_necessary_corrected` | 1565–1566 | The prose slip is confirmed. The example (X_{1,n} ~ N(0,1), all other terms 0) satisfies the CLT and violates (3.34), so it shows Lindeberg is *not necessary*. | correction accepted |
| `Thm3_22` | 1568–1575 | The mean-zero hypothesis is implied by `IsZeroBias`, so it is redundant but harmless (ISSUE-3.22 note). "Independent of all else" is weakened to what the proofs use, which is fine. Using `Fin (n+1)` rows is a sound way to avoid an empty `Fin 0` index; the 0-indexing note is correct. | matches |
| `Sec3_5_2_zeroBias_imp_tendstoInMeasure` | 1585–1586, 1625–1645 | The conclusion matches L1586. | see A2 |
| `Thm3_23` | 1578–1581 | "Satisfies a CLT" means W_n →ᵈ N(0, 1), stated as convergence in `ProbabilityMeasure ℝ`. | matches |

The ISSUE-TYPO-3.21 finding is confirmed: L1546–1547 omit 𝔼 on both lines and the prime on f at L1547. The L1527–1528 pointer (`%XXXX Exercise 3`) correctly gets a status line, not an entry.

## Required changes

- **A1. Missed prose claim, L1560–1561.** "A sufficient condition for W_n to satisfy a CLT is the Lindeberg condition (3.34)." This is the Lindeberg–Feller CLT, cited, so it is proved from scratch. Add it as `Sec3_5_2_lindeberg_sufficient`:
  - Hypotheses: rows independent, mean zero, L², Var(W_n) = 1, and (3.34).
  - Conclusion: W_n →ᵈ N(0, 1).
  - **Do not assume** that zero-bias variables or I_n exist.
  - The natural proof is Thm 3.22 + Thm 3.23 on an enlarged product space. That needs Prop 3.19 existence for σ²_{i,n} > 0, and Xᶻ ≡ 0 when σ²_{i,n} = 0.
  - Note the centering in the docstring (ISSUE-3.22 prose note).
- **A2. Docstring and statement mismatch.** The docstring of `Sec3_5_2_zeroBias_imp_tendstoInMeasure` says the conclusion includes max_i σ²_{i,n} → 0, but the Lean statement does not. Add that conjunct (L1633–1645), or remove it from the docstring; adding it is preferred.
- **A3. Prop 3.20 has two readings; state both.**
  - **Existence reading:** "a·Wᶻ is a zero-bias of aW" for every a ∈ ℝ, with no variance condition. This holds as printed, and the track already plans `IsZeroBias.const_mul`. Make it the entry `Prop3_20`.
  - **Law-identity reading:** keep `Prop3_20_restricted` with a ≠ 0 and σ² > 0, plus `not_Prop3_20_printed`.
  - In SOURCE-ISSUES, record ISSUE-3.20 as the Var(aW) = a²σ² = 0 instance of the ISSUE-3.19 degeneracy, not as an independent error.
- **A4. ISSUE-3.21 is a reading note, not a source issue.** An entry that assumes less than printed implies the printed result; the same treatment was accepted for Prop 3.14 and Cor 3.15 in Batch 4. Move it to the docstring as a reading note.

## Proof hint for `Prop3_21` (not a statement change)

Under D9, a test function only satisfies E\|Wf(W)\| < ∞ and E\|f′(Wᶻ)\| < ∞. That does **not** give E\|X_i f(W)\| < ∞, so the term-by-term route at L1545–1548 is not directly justified for every admissible f.

A route that works:
1. Identify the law of the constructed Wᶻ using C_c^∞ test functions, where every integral is finite.
2. Transfer to the full D9 class through `Prop3_19_corrected` (3). Here Var W = Σσ_i² = 1 > 0, and IsZeroBias depends only on the law of Wᶻ.
