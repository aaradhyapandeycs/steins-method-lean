# Statement review: EXER (exercises and "left to the reader" claims)

- **Critic:** Claude, 2026-11-11.
- **Method:** an independent read-only pass. All 25 TeX quotes are character-exact, checked by script. Cited names were checked by grep. The EXER-3 coupling was brute-forced for n = 2–5.

## Verdict: all five approved, with changes EX-1 to EX-5

| Draft | TeX | Uses |
|---|---|---|
| EXER-1 `Sec3_5_1_zeroBias_of_steinPair` | L1527–1528 | Goldstein–Reinert construction |
| EXER-2 `Sec3_6_1_indepSum_kolmogorov` | L1741–1743 | `Prop3_21`, `Sec3_6_zeroBias_bdd_exists`, `Thm3_27` |
| EXER-3 `Sec3_6_1_combinatorial_kolmogorov` | L1741–1743 | two-swap coupling, \|Wᶻ − W\| ≤ 8C/σ |
| EXER-4 `Sec3_6_2_indepSum_kolmogorov` | L1810–1812 | `Thm3_28` |
| EXER-5 `Sec3_6_2_antiVoter_kolmogorov` | L1810–1812 | `Thm3_28`, with the hypotheses of `Thm3_8` |

All five are true, none duplicates an existing entry, and there are no junk-value traps.

## Changes

- **EX-1.** Fix the stale locators: `Ex3_8` is at Sec3.lean:1103 and `Thm3_8` at :869. Refer to COVERAGE rows by label rather than by number.
- **EX-2.** EXER-4 and EXER-5 compute Var E[·|X], which only **bounds** Var E[·|W] from above (conditional Jensen). Remove "exact evaluation" and say this in the docstrings.
- **EX-3.** Part 2 must also list:
  - L1406 → `Ex3_9_moments`;
  - L1501 → the `Prop3_19_corrected` dual class;
  - L2105 → `Rem4_3`;
  - L2430 and L2442 → `Ex4_11` and `Ex4_12`;
  - L3873 → qualitative, followed by `Ex7_6_corrected`;
  - L412, 452, 611, 1061, 3423 and 3503 → commentary.
- **EX-4.** The claim that the "three-part Exercise 3" comes from TeX comments is a conjecture; label it as one.
- **EX-5.** EXER-3 needs the Goldstein–Reinert lemma for a general regression pair (a > 0, with no a ≤ 1 requirement), because a = 2 at n = 2. Put that general lemma in the EXER-1 file.

## Parallel proof split (disjoint new files)

| Group | Content | File |
|---|---|---|
| G1 | EXER-1, including the general lemma | `Formalization/Exer/GoldsteinReinert.lean` |
| G2 | EXER-2 | `Formalization/Exer/IndepSumZeroBiasKolmogorov.lean` |
| G3a | EXER-4 and the shared helper | `Formalization/Exer/Thm328Applications.lean` |
| G3b | EXER-5 | `Formalization/Exer/AntiVoterKolmogorov.lean` |
| G4 | EXER-3 combinatorics now; the final assembly after G1 lands | `Formalization/Exer/PermSwapCoupling.lean`, then `CombinatorialKolmogorov.lean` |
