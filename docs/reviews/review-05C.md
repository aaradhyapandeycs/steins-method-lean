# Critic review 05C: Track C (§4 opening and §4.1–4.2, Poisson approximation under dependence), `12aaa3a`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1876–2112. The statement review was stmts-review-05C (C1–C3).

## Verdict

**ACCEPTED.** 10 new statement entries are recorded in COVERAGE, bringing the total to 86 (17 corrected or restricted). §4.1–4.2 adds 8 numbered items: Theorems 4.5–4.9 and Remarks 4.1–4.3. That makes 65 of 122 numbered results.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set. The full build, the audit and `check.py` ran at `12aaa3a`.

During the per-file pass, the lead had begun the uncommitted BL6 integration in `Statements/Sec4*.lean`. So the two statement files were re-elaborated from their **committed** contents (`git show HEAD:…`). This full axiom audit also covers BL1's deferred audit.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3440 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 2221 project declarations.` |
| `python3 scripts/check.py` | exit 0 |
| Per-file re-elaboration: `Defs/PoissonDep`, `PoissonDep/{Basic, ErdosRenyiBounds, ErdosRenyiCounterexample, ErdosRenyiLaw, HeadRunAsymptotics, HeadRuns, LocalDependence}`, committed `Statements/Sec4` and `Sec4Proofs` | 10/10 rc=0, 0 errors |
| Wrapper identity for all 10 entries (`example : E := E_holds`) | type-checks |
| Axiom probe: the 10 wrappers, plus `not_Thm4_7_printed`, `not_Thm4_9_printed`, `headRunCount_sanity_0110111`, `longestQualityRun_sanity_0110111`, `longestQualityRun_one_eq_findGreatest_ones`, `erdos_renyi_longestQualityRun_ae` | 16/16 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the Erdős–Rényi limit 1/H(a, p) changed to 2/H(a, p) | **rejected** (`ERMut.lean:713`, linarith fails) |
| **Mutation 2:** in a scratch copy, the Thm 4.6 bound min{1, λ⁻¹}Σpᵢ² halved. This is false for a single Bernoulli(p) with small p. | **rejected** (`IndMut.lean:343`) |

## Statements

The entries are the approved drafts, with C1–C3 applied.
- **C1:** `Rem4_2` has both the real-k reading (λ → p^c, with error Θ(log n/n)) and the integer-k_n version with bounded offset.
- **C2:** the index sanity checks on y = 0110111 are proved:
  - `headRunCount` gives 2, 1 and 0 for k = 2, 3, 4;
  - `longestQualityRun` gives 3 at a = 1 and 7 at a = 1/2;
  - `longestQualityRun 1` equals the longest run of ones on {0, 1} sequences.
- **C3:** the reading notes are in the docstrings.

**`Thm4_9_corrected`.** The Erdős–Rényi law is proved from scratch for 0 < p < a ≤ 1, with a.s. convergence along prefixes of one infinite sequence.
- Natural logarithms in both log n and H are harmless, since the ratio does not depend on the base.
- At a = 1, `klDivBernoulli` is log(1/p), as printed.

**`not_Thm4_9_printed`** is a genuine refutation, not a junk value. At p = 1/2 and a = 1/4, H is finite and positive (≈ 0.1308), but R_n = n eventually.

**`not_Thm4_7_printed`** is also genuine. With X₁ ≡ 1 and N₁ = ∅, the printed bound is 0, while d_TV = 1 − e^{−1}.

## Accepted

- **Definitions:** `headRunIndicator`, `headRunCount`, `longestQualityRun`, `klDivBernoulli`, `poissonSteinClass`.
- **Source issues:** ISSUE-4.7 (re-confirmed), ISSUE-4.9 (new), ISSUE-TYPO-4.6.

## Note for the lead

The uncommitted BL6 wiring in `Sec4Proofs.lean` imports `Formalization.PoissonExch.FixedPointsTrueRate`. That module must be in the build closure (`Formalization.lean`) and compiled before the file elaborates. Make sure the build is green before committing batch-BL6.
