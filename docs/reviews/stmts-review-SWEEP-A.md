# Statement review: SWEEP-A (§1–2 and the start of §3, prose-claim sweep, `docs/tracks/SWEEP-A.md`)

- **Critic:** Claude, 2026-11-11.
- **Method:** an independent read-only pass with numerical checks. The critic re-checked the new proof-step finding at L853–855 by direct count: with N₁ = {1} and Nᵢ = {1, i} for n = 6, the coefficient is 11 = 2n − 1, against D² = 4.

## Verdict: approved with changes SA-1 to SA-10

SWEEP-A owns L347–949; SWEEP-B is cut back to L950–1815 (stmts-review-SWEEP-B, SB-1). Where the two overlap, SWEEP-A's items win: A8, A9, A11 and A12 replace B1, B2, B5 and B6.

| Item | Verdict |
|---|---|
| A1 metric axioms (L503–521) | approve with SA-1 |
| A2 CDF sup ⇒ weak convergence (L513–515, 708) | **approve** |
| A3 d_K ≤ d_W for N(m, v) and Exp(r) (L551–555) | status line: a restatement of `Prop1_2_2`; the standard-normal case is `Sec3_dK_le_dW` |
| A4 all-x characterization (L597–599) | **approve** |
| A5 Gaussian tail bound (L612–615) | **approve** |
| A6 piecewise f_x (L615–624) | status line, citing `Lem3_25_corrected`. "Sharp" is false: sup f_x = √(2π)/4 < √(π/2). |
| A7 IPM law-invariance (L655–659) | status line (notation, D2) |
| A8 regularity contrast (L711–715) | approve with SA-4; **withdraw the proposed source issue** |
| A9 i.i.d. rate and optimality (L743–744) | **approve** |
| A10 independent ⇒ dependency graph (L827–828) | **approve** (also a non-vacuity witness) |
| A11 intermediate bound (3.11)+(3.12) (L908–910) | approve with SA-5 |
| A12 triangle setup and moments (L919–928) | approve with SA-6 |
| TYPO-2.0-PRIME (L648), TYPO-3.5-PROOF (L832), SL-A1–A7, SL-A9–A11, SL-A13–A17 | accepted |

## Required changes

- **SA-1. A1.** `λ` is reserved syntax in Lean; rename the binder to `ρ`.
- **SA-2. A3** becomes a status line.
- **SA-3. A6** becomes a status line. Delete "sharp".
- **SA-4. A8: withdraw `ISSUE-SEC3-WASS-REG`.**
  - Under the project's accepted reading of Lemma 2.5(2), ‖f_h″‖ is an a.e. (Lipschitz) quantity, as already accepted for `Lem2_5_2`. Under that reading, L712–713 holds; the "failure" comes only from the strict `deriv` reading.
  - Rename the entry to `Sec3_opening_steinSol_regularity`, and the refutation to a `_strictReading` name. Explain the reading in the docstring.
  - Keep the "Proposition \ref{lem31}" → Lemma 2.5 cross-reference typo (L713, L715) as an ISSUE-TYPO.
- **SA-5. A11.** The docstring numbering should say "the unnumbered display at L865", not (3.13), which is `\label{48c}` at L870.
- **SA-6. A12.** Fix the type error: write `(enum i).1 ∈ G.cliqueSet 3`, since `cliqueSet : Set (Finset α)`. The p ∈ {0, 1} "iff" failure is genuine (the source asserts 0 ≤ p ≤ 1 at L941); record it as a note under ISSUE-3.2.1.
- **SA-7. SL-A8: rewrite TYPO-2.1-PROOF.** There is **one** sign slip, at L632 and inherited by L633: the second term needs a leading minus. It is not a "double slip that cancels". A numerical check with f(w) = w gives L631 = L634 = 1, while the printed L632 = L633 = 0.
- **SA-8. SL-A12.** L746–747 ("a small modification … yields a similar theorem assuming only third moments") asserts a result, so it cannot be a status line. Track it as SWEEP-B B4, or as an open item.
- **SA-9. Numbering.** The ledger row for L717–724 says "(3.2)"; it should be "(3.1)". The `Thm3_1` docstring in `Statements/Sec3.lean` (L37) has the same mislabel.
- **SA-10. New proof note (lead, SOURCE-ISSUES Part III; confirmed by the critic).** The step at L855,

  Σᵢ Σ_{j,k∈Nᵢ} E|Xⱼ|³ ≤ D² Σⱼ E|Xⱼ|³,

  needs each j to lie in at most D neighbourhoods, i.e. symmetric neighbourhoods. Definition 3.1 does not give that.
  - Counterexample to the step: N₁ = {1}, Nᵢ = {1, i}, so D = 2. The coefficient of E|X₁|³ is 2n − 1 on the left, against 4 on the right.
  - This is the second failing step in the proof of Theorem 3.5, after (3.15) in ISSUE-3.5.
  - `Thm3_5_corrected` already assumes symmetry, so no Lean change is needed.

No other uncovered substantive claim was found in L347–949.
