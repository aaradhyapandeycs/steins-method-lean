# Statement review: BL5 (anti-voter ergodicity, corrected) and BL9 (Example 3.8)

- **Critic:** Claude, 2026-11-11.
- **Method:** a first-pass independent review (read-only, with exhaustive and sampled enumeration), whose key findings the critic re-checked by enumeration.

## Verdicts

| Draft | Verdict |
|---|---|
| BL5 `Sec3_3_1_antiVoter_ergodic_corrected` | **True; approved with changes BL5-1 and BL5-2.** The state space is N(V), the non-constant labelings. Uniqueness is over all probability measures on `V → Bool` (constants are transient), with full support on N. It assumes `G.Connected`. The primitivity form ∀x, y ∈ N, ∃N, ∀t ≥ N, Pᵗ(x, y) > 0 is irreducible plus aperiodic. Checked: every connected graph on ≤ 6 vertices meeting the hypotheses (24,213 graphs) is irreducible on N with a unique law, with 0 violations; a spanning-subgraph reduction covers n ≤ 8, again with 0 violations. Named graphs (K₄, K₅, Petersen, prism, wheel, bowtie, tadpoles) all pass. |
| BL5 `antiVoter_disconnected_counterexample` (K₃ ⊔ C₄) | **True; approved.** **The critic re-checked it:** the chain has 2 closed classes of 6 states each, so the stationary law is not unique. The graph is 2-regular, not bipartite, and not a cycle. **This is a new refutation of the printed *uniqueness* claim at L1110**; ISSUE-3.8 had only refuted irreducibility on {±1}^V. |
| BL5 §2.2 prose ("disconnected ⇒ uniqueness fails") | **False as a general claim.** The critic re-checked K₃ ⊔ K₃: one closed class of 36 states, so the law is unique. Also K₄ ⊔ K₄ and C₅ ⊔ K₃. See BL5-3. |
| BL9 `Ex3_8` | **True; constants verified; approved with change BL9-1.** The first term (1/σ²)·√((2/π)·Σμ_i² Var X_i) and the second σ⁻³·Σ(E X_i³ − μ_i E X_i²) follow from Thm 3.13 plus Cor 3.15, using the independent coupling and Remark 3.4. Exact rational checks pass. |

## Required changes

- **BL5-1. SOURCE-ISSUES.** Record the omitted connectivity hypothesis, by extending ISSUE-3.8 or as a new entry, with K₃ ⊔ C₄ as the counterexample.
  - Say that it refutes the printed **uniqueness** claim. (Constants are transient, so uniqueness on {±1}^V is the same as uniqueness on N.)
  - Update ISSUE-3.8's "Resolution", which says uniqueness is "left open".
  - The `_corrected` docstring must point to this entry.
- **BL5-2. Docstring deviations.** List every difference from L1110:
  1. the state space is N, not {±1}^V;
  2. `G.Connected` is added (the omitted hypothesis, BL5-1);
  3. r-regularity is dropped, which strengthens the result.

  Recommended: keep `G.IsRegularOfDegree r` in the index entry so it matches the printed setting, and derive it from the general library theorem in the wrapper.
- **BL5-3. Prose.** Replace the §2.2 overclaim with the correct characterization. For disconnected G:
  - irreducibility on N always fails;
  - uniqueness fails **if and only if some component is bipartite**, because a bipartite component has two frozen proper colourings.
  - Counterexamples to the overclaim: K₃ ⊔ K₃, K₄ ⊔ K₄, C₅ ⊔ K₃.
- **BL9-1. Docstring reading notes.**
  1. Nonnegativity of the X_i comes from Cor 3.15's setting (size bias needs X_i ≥ 0), not from the exercise's wording.
  2. Ross gives no formula, so the bound is the project's solution of the exercise. Say so.
  3. σ² > 0 is typing.
  - The COVERAGE row for Example 3.8 changes once this batch is accepted. The critic owns COVERAGE and will update it; builders do not edit it.

## Optional

- BL5: add a 3-regular disconnected counterexample (K₄ ⊔ K₃,₃: 2 closed classes of 14 states each), so that "not a cycle" is not misread as "r ≥ 3".
- BL5: add the closedness conjunct `antiVoterStep_support_nonconst` to the entry.
- BL5: add an index-level `not_…_printed` refutation.
