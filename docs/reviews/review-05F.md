# Critic review 05F: Track F (§7 opening, §7.1–7.2 concentration of measure), `0da7275`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L3389–3804. The statement review was stmts-review-05F (F1–F4).
- **Method:** an independent statement-fidelity pass (read-only, with re-derivations), whose findings the critic checked.

## Verdict

**ACCEPTED.** 17 new statement entries are recorded in COVERAGE, bringing the total to 108 (22 corrected or restricted). All 10 numbered items in §7.1–7.2 are covered: Prop 7.1, Ex 7.1, Ex 7.2, Thm 7.2, Rem 7.3, Ex 7.4, Ex 7.5, Prop 7.3, Prop 7.4 and Thm 7.5. That makes 75 of 122 numbered results.

Follow-ups F5-1 to F5-8 are listed below. F5-1 is a medium-priority improvement to a restricted entry. None of them is a correctness defect in an accepted statement.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `0da7275`. The working tree also held the lead's staged F2 integration, so the full build checked a superset. The committed `Sec7`/`Sec7Proofs` were re-elaborated separately, and F2's files are not part of this batch.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3469 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 3143 project declarations.` |
| Re-elaboration: `Defs/Concentration`, `Concentration/{Basic, Combinatorial, CombinatorialPair, CurieWeiss, Exchangeable, IndepSum, IndepSumPair}`, committed `Statements/Sec7`, `Sec7Proofs` | 10/10 rc=0, 0 errors |
| Wrapper identity for all 17 entries | type-checks |
| Axiom probe: the 17 wrappers, plus `not_poisson_bound_order_printed` and `not_combinatorial_isSteinPair_n2` | 19/19 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the Ex 7.4(2) bound changed to 2exp(−16t²/(2μ+t)). This is false: with 16 fair coins and t = 4, P = 0.0768 > 5.5·10⁻⁶. | **rejected** (`HoeffMut.lean:616`) |
| **Mutation 2:** in a scratch copy, the Ex 7.2 order threshold λ > e^{−1} changed to λ > e^{−3}. This is false for λ ∈ (e^{−3}, e^{−1}]. | **rejected** (`LamMut.lean:478`) |

## Statements

F1–F4 are applied.
- **F1:** the C = 0 and B = C = 0 boundary conjuncts are present in `Thm7_2`, `Thm7_5` and `Ex7_4_1`. There, x/0 = 0 would otherwise weaken the printed bound.
- **F2:** `Ex7_2_order_corrected` holds for every λ > 0 and c > 1. `_restricted` covers λ > e^{−1}, and `not_…_printed` refutes the printed claim at λ = e^{−1}, where every quantity is defined.
- **F4:** `Sec7_thm7_2_from_thm7_5` (L3677–3681) and `Sec7_curieWeiss_mode` (L3640–3641) are present.

The independent pass found that every entry matches its TeX, with no junk values:
- the conditional expectations are of L¹ functions;
- the denominators vanish only where the boundary conjuncts take over.

## Follow-ups (lead)

- **F5-1 (medium). `Ex7_5_steinPair_restricted` restricts more than the source error requires.**
  - At n = 2, E[W] = 0, exchangeability and the linearity E[W′ | W] = (1 − 2/(n−1))W are all printed and all true. Only the a ≤ 1 clause of Def 3.2 fails (ISSUE-7.5).
  - The library already has `combinatorial_exchangeable_and_linear` for n ≥ 2.
  - Change the binder to `2 ≤ n` and conclude: the mean is 0, the pair is exchangeable, the linearity holds, and `3 ≤ n → IsSteinPair …`.
  - Docstring: "differs only by dropping Def 3.2's a ≤ 1 at n = 2".
- **F5-2 (low). `Ex7_2_order_corrected` docstring.** Say that the printed claim is the case c = 1 for every λ, false for 0 < λ ≤ e^{−1}, and that this entry relaxes c to c > 1.
- **F5-3 (low). `Ex7_2_order_restricted` docstring.** It currently says "fails for 0 < λ ≤ e^{−1}", but the refutation is machine-checked only at λ = e^{−1}. Either:
  - reword to "fails at λ = e^{−1} (machine-checked); for λ < e^{−1} by the asymptotic in ISSUE-EX7.2"; or
  - strengthen the refutation to every λ ∈ (0, e^{−1}].
- **F5-4 (low). `Ex7_4_2_corrected` docstring.** State the literal-reading failure: with μ = E W = 0, the bound reads P(|W| ≥ t) ≤ 2e^{−t}, which is false for n = 16 fair coins and t = 2 (ISSUE-EX7.4).
- **F5-5 (low). Missing minimizer conjuncts (L3439, L3454).** Add both; they hold for every θ:
  - Ex 7.1: `∀ θ t, 0 < t → exp(−t²/2) ≤ exp(θ²/2 − θt)`;
  - Ex 7.2: `B t ≤ exp(λ(e^θ − 1) − θ(t + λ))`.
- **F5-6 (low). New entry `Ex7_4_2_order` (L3528).** For constant μ ≥ 0, exp(−t²/(2μ+t))/e^{−t} → e^{2μ}.
  - Also fix the status lines in `docs/tracks/F.md`: L597 invents "σ ≪ 1", and L594 misreads L3443–3444. That remark is that e^{−t²/2} is the best Prop 7.1 can give.
- **F5-7 (low, optional). `Sec7_curieWeiss_mode` at h = 0.** Both constant configurations tie as maximizers there. Add that conjunct.
- **F5-8 (low). New entry `Sec7_eq7_4` for display (7.4) (L3549–3552).** It is reused at L3779 and L3831. State it as ∀ x y, |eˣ − eʸ| ≤ |x − y|·(eˣ + eʸ)/2, the cleared-denominator form, since the printed quotient is undefined at x = y. The library already has `abs_exp_sub_exp_le`.
- **Notes.**
  - The "m′(θ)/θ > 0" and "m′(θ) < 0" at L3561 and L3581 fail when W = 0 a.s. Only ≥ and ≤ are needed, so it is harmless; record it as a reading note in SOURCE-ISSUES Part III.
  - ISSUE-7.6's "Printed text" bullet says L3413 and L3485 print "t ≥ 0"; both print t > 0.
  - `F.md:15` cites `\label{211a}` for (7.4); the label is `2212a`.
  - Status lines are still needed for L3394–3400, L3639–3640 and L3655–3656.
