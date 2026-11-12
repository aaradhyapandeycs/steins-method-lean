# Critic review BL7: Ruciński's triangle-count CLT criterion (prose, L942–945, citing [ruc88]), `f7811b2`

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L936–945. The statement review was stmts-review-G4-BL7 (BL7-1, BL7-2).

## Verdict

**ACCEPTED.** Two entries are recorded in COVERAGE: `Sec3_2_1_triangles_rucinski` and `Sec3_2_1_triangles_rucinski_power_regime`. This brings the total to 91 entries. They are prose claims, so the numbered count stays at 65/122. The "§3.2.1 prose (CLT regime)" row, open since review-04, is now covered.

## Independent verification

The commands ran with `.locks/CRITIC-HOLD` set, at `f7811b2`, on a clean Lean tree.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3456 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 2773 project declarations.` |
| Re-elaboration: `RandomGraph/TrianglesRucinski{Identities, Moments, Coupling, Sufficiency, Necessity, CLT}`, committed `Statements/Sec3`, `Sec3Proofs` | 8/8 rc=0, 0 errors |
| Wrapper identity for both entries | type-checks |
| Axiom probe: both wrappers, `tendsto_triangles_wassersteinDist_zero_of_rucinski`, `triangles_sizeBias_coupling` | 4/4 `[propext, Classical.choice, Quot.sound]` (one multi-line output, parsed) |
| **Mutation 1:** in a scratch copy, the criterion n²(1 − pₙ) → ∞ changed to n(1 − pₙ) → ∞. This is false for pₙ = 1 − n^{−3/2}. | **rejected** (`CritMut.lean:221`) |
| **Mutation 2:** in a scratch copy, the normal regime α < 1 extended to α < 2. This is false at α = 1: the count is asymptotically Poisson. | **rejected** (`AlphaMut.lean:275`) |

## Statements

- **`Sec3_2_1_triangles_rucinski`.** For G ~ G(n, pₙ) with 0 ≤ pₙ ≤ 1, the standardized triangle count Wₙ → N(0, 1) if and only if npₙ → ∞ and n²(1 − pₙ) → ∞. The entry states three equivalent forms: pointwise CDF, d_K and d_W.
  - This is Ruciński (1988), Theorem 2, with m(K₃) = 1, proved from scratch.
  - The [0, 1] domain is a sound generalization (BL7-2 note in the docstring): if pₙ ∈ {0, 1} infinitely often, both sides fail.
- **`Sec3_2_1_triangles_rucinski_power_regime`** (BL7-1) is the printed claim at L943–944 that 0 ≤ α < 2/9 is "only a subset" of the normal regime.
  - For every α ∈ [0, 1) with n^α pₙ → c > 0 (c < 1 when α = 0), there is normal convergence in d_W, d_K and CDF. This strictly contains [2/9, 1), where Track K showed the §3.2.1 Stein bound does not vanish.
  - It also includes the optional converse: for α ≥ 1 there is no normal convergence.
