# Critic review BL1: §3.6 binomial order n^{−1/2} (prose, L1655–1657), `c78353f`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1651–1657: "if W is a standardized binomial random variable with parameters n and p, then both d_K(W, Z) and d_W(W, Z) are of order n^{−1/2}". This is BACKLOG item 1 (Track B deferral B1).
- **Note:** no statement draft was handed off before proving, so the statement and the proof are reviewed together here.

## Verdict

**ACCEPTED.** `Sec3_6_binomial_order` is recorded in COVERAGE. This brings the total to 76 entries. The prose row does not change the numbered count, which stays at 57/122.

## Statement

For fixed 0 < p < 1 there are c, C > 0 such that, for every n ≥ 1, both d_K and d_W lie between c·n^{−1/2} and C·n^{−1/2}. W is the standardized sum of n independent Bernoulli(p) indicators.

This is the natural reading of "of order n^{−1/2}" with p fixed. Both directions are needed to support the text's point that the √d_W route, which gives n^{−1/4}, is suboptimal for d_K. The statement is true:
- **Upper bounds:** Berry–Esseen-type and Wasserstein bounds.
- **Lower bounds:** W lives on a lattice of spacing h = 1/√(np(1−p)).
  - d_K is at least half the largest atom, which is of order h.
  - d_W is at least E[dist(Z, lattice)], because dist(·, lattice) is 1-Lipschitz and vanishes on W's support. This is of order h. The library uses a smooth periodic cosine test function to the same effect.

The constants depend on p, as "of order" with p fixed allows. Every hypothesis is either typing or the setup of the claim.

## Independent verification

The commands ran at `c78353f` with `.locks/CRITIC-HOLD` set. The BL1 files (`Kolmogorov/Binomial*`, `Statements/Sec3*`) are identical to HEAD.

The working tree also held the lead's **uncommitted, failing** Track C integration: `Statements/Sec4Proofs.lean` had 6 type mismatches. Because of that, a full `lake build` and `Audit.lean` could not complete in this checkout. The BL1 closure was therefore checked directly. The full axiom audit is to be re-run at the next clean handoff (batch-05C).

| Check | Result |
|---|---|
| `lake build Formalization.Statements.Sec3Proofs` (the BL1 closure) | exit 0 (3330 jobs) |
| Full `lake build` / `Audit.lean` / `check.py` | blocked by the lead's uncommitted `Sec4Proofs.lean` errors (not BL1); deferred to batch-05C |
| Per-file re-elaboration: `Kolmogorov/BinomialUpper`, `Kolmogorov/BinomialOrder`, `Statements/Sec3`, `Sec3Proofs` | 4/4 rc=0, 0 warnings, 0 errors |
| Wrapper identity `example : Sec3_6_binomial_order := Sec3_6_binomial_order_holds` | type-checks |
| Axiom probe (importing `Sec3Proofs`): `Sec3_6_binomial_order_holds`, `binomial_kolmogorovDist_and_wassersteinDist_order` | both `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the d_K upper bound C·n^{−1/2} changed to C·n^{−1}. This is false, given the lower bound. | **rejected** (`UpMut.lean:521`) |
| **Mutation 2:** in a scratch copy, the d_W lower bound c·n^{−1/2} changed to c·n^{−1/4}. This is false, given the upper bound. | **rejected** (`LowMut.lean:522`) |
