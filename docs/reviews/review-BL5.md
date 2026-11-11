# Critic review BL5: anti-voter ergodicity and uniqueness (prose, L1110–1111, citing [af10]), `5d837a3`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L1101–1111. The statement review was stmts-review-BL5-BL9 (BL5-1 to BL5-3).

## Verdict

**ACCEPTED.** `Sec3_3_1_antiVoter_ergodic_corrected` is recorded in COVERAGE as a disclosed corrected variant, together with the machine-checked refutation `not_Sec3_3_1_antiVoter_unique_printed`. This brings the total to 89 entries (18 corrected or restricted). It is a prose claim, so the numbered count stays at 65/122.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `5d837a3`. The working tree also held the lead's next uncommitted integration in `Statements/Sec3*`, and the full build passed with it. The committed statement files were re-elaborated separately.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3456 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 2773 project declarations.` |
| Re-elaboration: `Exchangeable/AntiVoterIrreducible`, `Exchangeable/AntiVoterUnique`, committed `Statements/Sec3`, `Sec3Proofs` | 4/4 rc=0, 0 errors |
| Wrapper identity `example : Sec3_3_1_antiVoter_ergodic_corrected := …_holds` | type-checks |
| Axiom probe: the wrapper, `not_Sec3_3_1_antiVoter_unique_printed`, `antiVoter_ergodic_and_unique_stationary`, `antiVoter_disconnected_counterexample` | 4/4 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the hypothesis `G.Connected` replaced by `True`. The result is then false, as K₃ ⊔ C₄ shows. | **rejected** (`ConnMut.lean:342`) |
| **Mutation 2:** in a scratch copy, the support conclusion changed to "ν{x} ≠ 0 for every x". This is false, because the constant labelings are transient. | **rejected** (`SuppMut.lean:361`) |

## Statements

- **`Sec3_3_1_antiVoter_ergodic_corrected`.** For a connected r-regular graph that is neither bipartite nor a cycle:
  1. every step lands in the non-constant labelings N(V);
  2. the chain on N(V) is primitive (∃N, ∀t ≥ N, Pᵗ(x, y) > 0), i.e. irreducible and aperiodic;
  3. the stationary law on `V → Bool` is unique, and its support is exactly N(V).

  The docstring lists all three deviations from L1110 (BL5-2). r-regularity is kept in the entry and dropped in the library theorem, which is a strengthening.
- **`not_Sec3_3_1_antiVoter_unique_printed`.** The printed claim (r-regular, not bipartite, not a cycle ⇒ unique stationary law) is refuted by K₃ ⊔ C₄ on `Fin 7`. That graph is 2-regular, not bipartite and not a cycle, and its chain has two closed classes. This is a genuine refutation, not a junk value. The critic had already confirmed it by enumeration.
- ISSUE-3.8 now records the omitted connectivity hypothesis and the uniqueness refutation (BL5-1).

## Minor (non-blocking)

`Sec3_3_1_antiVoter_unique_printed` is a `def` in `Statements/Sec3Proofs.lean`. For consistency with `Thm4_7_printed` and `Thm4_9_printed`, move the printed-claim def and its refutation into `Exchangeable/AntiVoterUnique.lean`, and re-export the refutation from `Sec3Proofs`.
