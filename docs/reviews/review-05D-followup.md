# Critic review 05D-followup: Track D fixes and §5 extras, `b4286f9`

- **Critic:** Claude, 2026-11-11.
- **Review:** review-05D (D5-1 to D5-3, N1, M1, M2, M4).

## Verdict

**ACCEPTED.** The two held entries are now accepted, and 3 new entries are added, bringing the total to 198 (35 corrected or restricted). Lemma 5.2 is now fully covered and Theorem 5.7 is covered as a corrected result, which makes 118 of 122 numbered results.

- **D5-1, `Thm5_7_corrected`:** reproved under the minimal correction via `thm5_7_corrected_minimal`. The hypotheses are the printed joint independence `Xe i ⊥ (N, M, (X_j)_{j≠i})` plus the one omitted condition `(N, M) ⊥ (X_i)_i`, which `not_Thm5_7_printed` shows is needed. The redundant `Integrable N` (note N2) is harmless.
- **D5-3, `Lem5_2_1`:** now carries `LipschitzWith (2M) (expSteinSol h)`, the junk-free form of ‖f_h′‖ ≤ 2‖h‖, with its docstring fixed.
- **D5-2:** the `Thm5_6` docstring citation is fixed.
- **New entries:**
  - `Lem5_2_ode_ae`: the a.e. ODE, plus uniqueness among locally AC g with g(0) = 0 (M1);
  - `Sec5_2_eq5_6`: the equilibrium coupling of eq. (5.6) (M2);
  - `Ex5_4_weak_conv`: pN converges weakly to Exp(1) (M4).

## Independent verification

The commands ran at `06c484f` with `.locks/CRITIC-HOLD` set.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3542 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 5571 project declarations.` |
| Re-elaboration: the changed `Exponential/{GeometricExample, GeometricSums, GeometricSumsAux, Renyi, Sec5Extras, SteinEquation}`, committed `Statements/Sec5`, `Sec5Proofs` | 8/8 rc=0 |
| Axiom probe: all 21 §5 wrappers | 21/21 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the bound \|f_h\| ≤ M changed to \|f_h\| ≤ 0 | **rejected** |
| **Mutation 2:** in a scratch copy, the (N, M) ⊥ X hypothesis of Thm 5.7 replaced by `True` | **rejected**: the proof uses the independence (`IndMut.lean:120`) |

A first attempt at mutation 2 failed on a syntax error introduced by the mutation script, so it tested nothing. It was redone correctly, as shown above.
