# Critic review: batch-BL8c (3a4178c)

Verdict: **ACCEPTED**. Resolves the open obligation BL8-2 (Remark 3.5, Item 3 probability tail).

Verified at HEAD 83cebd0 (clean Formalization tree), under `.locks/CRITIC-HOLD`:

- `lake build`: success (3568 jobs). `lake env lean Audit.lean`: axiom audit passed for 6952 declarations.
- `Formalization/Leftovers/OUProbTail.lean` and committed `Statements/Sec3`, `Sec3Proofs` re-elaborate with 0 errors.
- `Rem3_5_uniqueness_probTail_restricted_holds` depends only on [propext, Classical.choice, Quot.sound];
  the wrapper is a direct application of `rem3_5_uniqueness_probTail_proof`.
- Mutations rejected: the diffusion limit `2 * a` -> `a` in the uniqueness hypotheses (type mismatch at
  L1718), and `2 * a` -> `3 * a` in the O-U non-vacuity part (type mismatch at L1714).

Fidelity (`SteinIntro_utf8.tex:1009-1024`, Items at L1014-1016):

- Items 1-3 are transcribed literally as small-time limits of the drift, second moment and probability tail
  `(K a x).real {y | ε < |y - x|} = o(a)`; the Lindeberg second-moment tail used by `Rem3_5_uniqueness_restricted`
  is no longer assumed.
- The single extra hypothesis is small-time quadratic moment domination (with integrability), the disclosed
  regularity reading of "diffusion process". Part 1 proves `ouKernel` satisfies every hypothesis, so the
  uniqueness statement is not vacuous.
- Conclusions: `K t = ouKernel t` for all t > 0 and uniqueness of the stationary law, matching "these three
  properties determine the O-U diffusion process ... with the standard normal distribution as its stationary
  distribution".

Statement index: 241 -> 242 accepted entries (48 corrected/restricted); numbered coverage unchanged at 121/122.
