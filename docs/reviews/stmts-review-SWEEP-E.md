# Statement review: SWEEP-E (§5, TeX L2712–3189)

- **Critic:** Claude, 2026-11-11.
- **Method:** an independent read-only pass. All 45 quotes match the cited lines; 11 of them are split-range or mid-line quotes. Cited names were checked by grep.

## Verdict: returned for changes SE-1 to SE-8

- **SE-1. Duplicates.** D-E1, D-E4 and D-E5 duplicate items assigned elsewhere:
  - D-E1 (`Lem5_2_ode_ae`) duplicates D2.md;
  - D-E4 (`Ex5_4_weak_conv`) duplicates D.md M4;
  - D-E5 duplicates D2.md `Sec5_2_eq5_6`.

  Replace them with pointers, and fix the false "uncovered" claims in the ledger. The real gap is for the lead: these three entries are not yet in `Statements/Sec5.lean`.
- **SE-2.** `lem5_2_ode_ae` lives in `Exponential/Sec5Extras.lean`.
- **SE-3. D-E2 (Carleman moments).** Parts (1)–(3) are true. Part (4), "moments k! ⇒ Exp(1)", needs moment determinacy, which is not proved here and not in Mathlib.
  - Either make it a status line consistent with D.md (`lem5_1_2` bypasses it via `expRamp`), or mark (4) as an open obligation.
  - D.md's range for this passage should be L2811–2818.
- **SE-4. D-E6, ISSUE-5.9-PROOF-MEAN: genuine and new.** The proof of Theorem 5.9 applies Theorem 5.4 to 2Yₙ/(nσ²), whose mean is not 1 for finite n.
  - Record it in SOURCE-ISSUES Part III, with the resolution: the library already handles this through `thm5_9_restricted`, using a |1 − E W| penalty.
  - Drop (1) and (2), or align them with the library route; (2) duplicates `sec5_3_kolmogorov_survival_restricted`.
  - Keep (3) only as the witness lemma.
- **SE-5. Names.**
  - `Prop5_3`/`prop5_3` should be `Prop5_5`/`prop5_5`.
  - `not_exists_isEquilibrium_zero` does not exist; cite ISSUE-5.5.
  - `exponentialMeasure` should be `expMeasure`.
- **SE-6.** Merge the duplicated status lines (SL-E1, E8, E9, E14, E17, E18, E19) into cross-references to D.md §1.2.
- **SE-7.** The footer must not claim STATEMENTS READY while D-E2 (4), D-E3 and D-E6 are unproved obligations.
- **SE-8.** Restore the `$` delimiters in the inline quotes (ledger L57–58).

**Accepted:**
- D-E3 (low priority);
- the §4.2 typo list (verified);
- the remaining status lines.
