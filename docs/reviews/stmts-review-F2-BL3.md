# Statement review: F2 (§7.3 size-bias concentration) and BL3 (Example 3.6 printed bound for n < 16)

- **Critic:** Claude, 2026-11-11.

## F2: approved, no changes

`Thm7_6_corrected` is the statement already approved in stmts-review-05F. `Ex7_6_corrected` applies the required F3 restructuring:
- the coupling claims and the two-sided tail bound hold for every n ≥ 1 and k ≥ 1, with 0 < p < 1;
- the mean formula carries the hypothesis k ≤ n;
- the corrected variance formula carries 2k − 1 ≤ n.

I spot-checked the n < k wrap-around case. Every window covers all the coins, so X = n·ΠY_j and Xˢ ≡ n. That is the size-bias of a {0, n}-valued variable, and \|Xˢ − X\| ≤ n ≤ 2k − 1. The positivity of μ and C is derived, not assumed. The status line for L3873–3875 is accepted.

## BL3: approved, with two required changes

The claim that the printed final bound at L1089 holds for **every** n ≥ 1 is plausible, and the proof route is concrete:
- for n ≥ 2, a leave-one-out Stein kernel with exact rational SOS and positive-basis certificates;
- for n = 1, a direct Lipschitz-shift argument.

The supporting numbers are consistent:
- the right-hand side is at least √(2/π)/(2√n) + 2/3, which is about 1.066 at n = 1 and 0.770 at n = 15;
- the worst case reported for d_W over mean-0, variance-1 laws is about 0.848.

The proof itself is what will be reviewed when the batch lands.

- **BL3-1. Make the intrinsic statement the main entry.**
  - Example 3.6's printed claim is about W = ΣX_i/√n. The pair (X′, I) is the proof method, not a hypothesis.
  - Make `Ex3_6_printed_indep` the entry, preferably renamed `Ex3_6_printed`, stated for all n ≥ 1. Once that holds, `Ex3_6_small_n` is redundant, so drop it or keep it only as an internal lemma.
  - Keep the accepted `Ex3_6_corrected` and `Ex3_6_restricted`.
- **BL3-2. Update ISSUE-3.6 through the lead.**
  - The printed final inequality at L1089 is **true**.
  - What fails is the intermediate step at L1073–1074 (the missing 1/n when averaging over I; class C, proof slip) and the remark at L1091.
  - The remark says "if the X_i are i.i.d. then this term is of order n^{−1/2}". For the printed bound the second term is (2/3)·E\|X\|³, which does not decay. The remark is true only for the corrected 8/(3n^{3/2}) bound. Record it as a false remark with that one-line computation.
