# Critic review 05D: Track D (§5 opening, §5.1–5.2 exponential approximation), `14fdf88`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L2712–2984. The statement review was stmts-review-05D (D1–D6).
- **Method:** an independent statement-fidelity pass (read-only, with re-derivations), whose findings the critic checked.

## Verdict

**ACCEPTED IN PART.** 16 of the 18 entries are accepted, bringing the total to 138 (26 corrected or restricted). Two are **held** until the fixes below land:
- `Lem5_2_1`: D5-3;
- `Thm5_7_corrected`: D5-1.

Of §5.1–5.2's 13 numbered items, 11 are now covered, Lemma 5.2 only partially. Theorem 5.7 is open pending D5-1, and Remark 5.6 is open (a vague pointer to [rope10]). That makes 93 of 122 numbered results.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `14fdf88`.

The working tree held two other agents' in-progress edits: the F5 agent had broken `Concentration/Basic.lean`, and the SWEEP-C files were present. So the full `lake build` and `Audit.lean` failed **for reasons outside this batch**. The §5 closure was built and checked directly, and the full axiom audit is re-run at the next clean handoff.

| Check | Result |
|---|---|
| `lake build Formalization.Statements.Sec5Proofs` (the §5 closure) | exit 0 (3313 jobs) |
| Full `lake build` / `Audit.lean` | blocked by the uncommitted `Concentration/Basic.lean` WIP (not this batch); deferred |
| Re-elaboration: `Defs`, `Defs/Exponential`, all 12 `Exponential/*` files, committed `Statements/Sec5`, `Sec5Proofs` | 16/16 rc=0, 0 errors |
| Wrapper identity for all 18 entries | type-checks |
| Axiom probe: the 18 wrappers, plus `not_Thm5_7_printed` and `not_exists_hasDerivAt_expStein_Iic` | 20/20 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the Lem 5.2(1) bound \|f_h\| ≤ M changed to \|f_h\| ≤ 0 | **rejected** (`SolMut.lean:378`) |
| **Mutation 2:** in a scratch copy, the Thm 5.4 constant 2 changed to 1/4 | **rejected** (`EqMut.lean:568`) |

## Statements

D1–D3 are applied:
- **D1:** `IsEquilibrium` no longer assumes μ > 0. `Prop5_5` holds literally, and ISSUE-5.5 records the μ = 0 failure of uniqueness and absolute continuity.
- **D2:** the left-derivative and Lipschitz forms are in place, and ISSUE-5.2-PROOF is added.
- **D3:** ISSUE-5.7's E[W] − 1 formula has been re-derived.

The definitions are faithful: `expLaw`, `expSteinOp`, `expSteinSol` (5.2), `IsEquilibrium`, `shiftedGeomLaw`.

Both refutations are genuine, not junk values:
- **`not_Thm5_7_printed`:** N = M ~ Ge(p), with every error term a lintegral.
- **`not_exists_hasDerivAt_expStein_Iic`:** uses a real `HasDerivAt` and an h that is genuinely integrable.

## Held entries and required fixes (Track D)

- **D5-1 (`Thm5_7_corrected`, blocking).** The entry assumes `IndepFun (N, M) ((Xᵢ, Xᵢᵉ))ᵢ` plus `Xᵢᵉ ⊥ (Xⱼ)_{j≠i}`. That is stronger than the printed joint independence of Xᵢᵉ and (N, M, (Xⱼ)_{j≠i}) plus the minimal omitted condition (N, M) ⊥ (Xᵢ)ᵢ.
  - The weaker version is true. Restate the hypotheses in that form and reprove.
  - Otherwise, disclose the stronger hypothesis and record the minimal version as an open obligation.
- **D5-3 (`Lem5_2_1`, blocking).** The docstring's claim that the left-derivative bound "holds everywhere without vacuity" is false: `derivWithin` takes a junk value where no one-sided derivative exists.
  - Add the conjunct `LipschitzWith (Real.toNNReal (2 * M)) (expSteinSol h)`, which `lem5_2_1` already proves. Pass the full theorem in the wrapper, and fix the docstring.
- **D5-2 (`Thm5_6` docstring, required).** There is no `\label{thm179}`. The environment is the unlabeled Rényi theorem at L2905–2911; `\label{179}` is eq. (5.6).
- **Further items.** Missing entries or status lines:
  - **M1:** `Lem5_2_ode_ae`;
  - **M2:** the eq. (5.6) equilibrium coupling;
  - **M3:** the L2914 "implies Rényi" status line;
  - **M4:** L2885, pN converges weakly;
  - **M5:** the heuristics.
