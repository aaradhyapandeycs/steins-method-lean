# Statement review: SWEEP-F (§7, TeX L3389–3887)

- **Critic:** Claude, 2026-11-11.
- **Method:** an independent read-only pass. All 45 fenced TeX quotes were checked by script and are verbatim. The critic re-checked by grep that the cited library declarations are absent.

## Verdict: approved with required changes

**Main defect.** SWEEP-F, and Track F's F.md §6, cite library declarations that do **not exist**: `indepSum_unitInterval_bound_order`, `poisson_bound_order_not_tendsto_of_le`, `Sec7_eq7_4` and `Ex7_4_2_order`. The Track F follow-ups F5-1 to F5-8 have not landed, although F.md says `STATUS: READY`:
- `curieWeiss_mode` still lacks h = 0;
- `stdNormal_concentration` has no minimizer conjunct;
- `combinatorial_isSteinPair_restricted` still takes 3 ≤ n.

## Required changes (SWEEP-F)

- **SF-1.** Delete every claim that something is "already proved in the library" for a declaration that does not exist. Say that the F5 follow-ups have not landed.
- **SF-2.** Recast F-D1 (`Ex7_4_2_order`), F-D2 (`Sec7_eq7_4`) and §3 as cross-references to Track F's F5-1 to F5-8. Do not write second drafts.
- **SF-3.** S-F5, S-F6, S-F13, S-F18, S-F23 and S-F25 should say "pending F5-x (not committed)".
- **SF-4.** Give each duplicated status line (S-F1, 5, 6, 9, 13, 16, 18, 20, 27) a single home: a one-line pointer to F.md §4.3 or F2.md §5.
- **SF-5.** Mark ISSUE-7.2 (strict signs) and the ISSUE-7.6 "t > 0" fix as already drafted in F.md §6.4. Fix the `SOURCE-ISSUES.md:632` citation to `:658`.
- **SF-6. F-D3 (eq. (7.12) minimizer).** The mathematics is correct (checked numerically). Keep ISSUE-7.6-PROOF as a Part III note, with "Failure 2" reworded as an unjustified test point rather than a false bound. Add Statements entries only once library proofs exist.
- **SF-7. ISSUE-7.2-INT.** The counterexample is genuine. Add that the monotone-f rescue uses E|W| < ∞, which follows from Var W < ∞, and justify the truncation step.
- **SF-8.** Correct the header ranges of S-F17, S-F19, S-F21 and S-F22, and label the cited private helpers as private.

## Accepted

- The new typo/issue findings are genuine:
  - ISSUE-TYPO-7.4: the missing k ≠ i (at n = 3 the printed exponent is 5/3, where 1 is correct), B, C > 0 against B = 0, and the subscript at L3777;
  - ISSUE-7.2-INT;
  - ISSUE-7.6-PROOF.
- The remaining status lines are fine.
