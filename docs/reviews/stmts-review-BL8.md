# Statement review: BL8 (Remark 3.5 uniqueness, TeX L1009–1024)

- **Critic:** Claude, 2026-11-11.
- **Printed claim (L1018–1019):** "These three properties determine the O-U diffusion process, and this process is reversible with the standard normal distribution as its stationary distribution."

## Verdict: approved with changes; the source-issue claim is rejected

Parts 1–3 of `Rem3_5_uniqueness_restricted` are true and provable, so the uniqueness route is sound:
- **Part 1:** `ouKernel` satisfies Chapman–Kolmogorov, the Lindeberg tail and quadratic domination.
- **Part 2:** generator identification on primitives of C_b¹ functions; and every square-integrable law that is stationary for all small a is the standard normal law.
- **Part 3:** Chapman–Kolmogorov forces K_t = ouKernel t, and gives moment-free stationary uniqueness.

**The proof route (my reconstruction, for the agent):**
- Compare K with Q = ouKernel through φ(s) = (K_s Q_{t−s} f)(x) on (0, t), for smooth f with bounded derivatives.
- The right derivative of φ is K_s(L Q_{t−s} f) − K_s(L Q_{t−s} f) = 0. Passing the limit inside K_s uses dominated convergence: by Taylor, |K_h g − g| ≤ C h (1 + y²) for g ∈ C_b², and the second moments of K_s are finite by iterating domination through Chapman–Kolmogorov.
- φ is continuous, with φ(0+) = Q_t f(x) and φ(t−) = K_t f(x). Mathlib's right-derivative constancy lemma then gives K_t f = Q_t f, and smooth bounded f determine the measure.
- The OU backward equation ∂_r Q_r f = L Q_r f comes from Mehler's formula and Gaussian integration by parts.
- Stationary uniqueness in Part 3: μ = μK_{nt₀} → N(0, 1).

### Required changes

- **BL8-1 (high). Part 4 is not a refutation of the printed text. Do not file it as a source issue.**
  - The printed claim concerns a *process* (D(t))_{t≥0}, a time-homogeneous Markov diffusion, whose transition kernels satisfy Chapman–Kolmogorov. Part 4's three-atom family has no Chapman–Kolmogorov, so it is not such a process.
  - Without Chapman–Kolmogorov, uniqueness fails trivially, even under the Lindeberg tail: K_a := ouKernel(a + a²) satisfies Items 1–2, the Lindeberg tail and domination, yet K_a ≠ ouKernel a. So "K_a ≠ ouKernel a" is no evidence about Item 3.
  - The name `ISSUE-3.5` is also already taken (Theorem 3.5 singleton neighbourhoods).
  - **What to do:**
    - remove the "necessity" wording;
    - drop Part 4, or move it to a separate reading-note lemma `Rem3_5_kernelFamily_note` with a neutral docstring: "without the semigroup property, the untruncated Items 1–2 with the probability tail do not determine the generator; this is why the entry uses the Lindeberg form".
    - It must not be cited as evidence of a source error.
- **BL8-2 (high). Honest restriction and an open obligation.** The entry adds two hypotheses the remark does not print:
  1. the Lindeberg second-moment tail in place of Item 3's probability tail;
  2. small-time quadratic domination, a regularity reading of "diffusion process".

  The docstring must say so. Whether the printed probability-tail form already suffices for Chapman–Kolmogorov Markov semigroups is **open**:
  - Item 3 rules out jumps at the generator level.
  - Far mass of order o(a) can still carry Θ(a) of the untruncated second moment.
  - I know of no semigroup that does this, but I have no proof that none exists.

  The critic records it in COVERAGE as an open obligation, not a source issue. A Chapman–Kolmogorov counterexample (a Markov semigroup satisfying the printed Items 1–3 plus domination that is not OU) would make it a genuine issue. Otherwise leave it open.
- **BL8-3 (low). Tighten hypotheses.** The generator-identification conclusion in Part 2 needs only Items 1–2 and the Lindeberg tail, plus local integrability (second moment finite for small a). Move the quadratic-domination hypothesis down to the two conclusions that use it, if the proof allows. This is optional and will not block acceptance.
- **BL8-4 (low). Reversibility.** In the docstring, point to Track K's accepted `ouKernel` reversibility and stationarity for "this process is reversible with the standard normal distribution as its stationary distribution". Parts 2–3 add the "its" (uniqueness of the stationary law).

### Status lines

- **L1020–1023:** "Roughly, if we think of W as D(t)…". The correspondence between Items 1–3 and the Theorem 3.5 error terms is heuristic, and Track K's status line already covers it.

Proceed to the proof of Parts 1–3 in `Formalization/Leftovers/OUUniqueness.lean`. Write `STATUS: READY` in `docs/tracks/BL8.md` when it is sorry-free.
