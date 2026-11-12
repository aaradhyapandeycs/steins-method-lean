# Statement review: SWEEP-D (§4.3–4.4, TeX L2113–2711)

- **Critic:** Claude, 2026-11-11.
- **Method:** an independent read-only pass.
  - Quotes were checked line by line by script: 33 of 34 blocks match exactly.
  - Cited declarations were checked by grep.
  - The n = 3, p = ½ numbers were recomputed exactly.

## Verdict: returned for changes SD-1 to SD-7

The four drafted Props are true. D-D2, D-D3 and D-D4 are accepted, with SD-5 applied to D-D4. The sweep also cites declarations that do not exist and claims a quote check that was not performed as described.

- **SD-1.** The S-D7 citation should be L2242–2244, not L2242–2245, where the last line is blank. Correct the Part 5 claim: the real result was 34 blocks with 1 mismatch, and the method joined lines without newlines, which is a weak check.
- **SD-2. Part 2 (G4 cross-check) cites non-existent names** (`ex4_15_regime1/2`, `not_ex4_15_printed_n_eq_1`, `rem4_14_sizeBias`, and others). It also labels restricted or corrected results as "Proved". Defer Part 2 to Track G4, which is still in progress.
- **SD-3. Wrong names:**
  - S-D13 should cite `lem4_18_strassen_1d_iff` (`Monotone/Basic.lean:249`);
  - S-D18 should cite the private `unifProb_nn` and `unifProb_sum`;
  - S-D19 should cite `not_rem4_17_atLeast_printed`.
- **SD-4. Withdraw `ISSUE-EX4.5-FOOTNOTE`.** The footnote at L2181–2186 is accurate in context: eq. (78) at L1380–1388 carries the 1/n² factor.
  - For D-D1, keep conjunct 3 and the sparse-regime conjunct, labelled as the §3.4 proof-method reading.
  - Drop conjunct 4, which is a tautology, and move conjuncts 1–2 into a note.
- **SD-5. D-D4.** Drop the tvDist conjunct; it duplicates `Ex4_4`/`Thm4_6`.
- **SD-6.** Repair the corrupted `\ref{thm122}`/`\ref{thm125}` text at SWEEP-D.md lines 618–620, where `\r` was turned into a newline.
- **SD-7.** Mark cited private declarations as private.

**Accepted:**
- the ISSUE-4.17 pinpoint note (counterexamples verified);
- the missing-"we" typo at L2600;
- the other status lines.

ISSUE-TYPO-EX4.21 is optional.
