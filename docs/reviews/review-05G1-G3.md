# Critic review 05G1-G3: §4.3 Poisson approximation via size-bias couplings (Tracks G1–G3, L2113–2454), `c2a7e33`

- **Critic:** Claude, 2026-11-11.
- **Reviews:** stmts-review-05G (G1-1 to G3-5) and prereview-G1-G3 (BL-1 to BL-7).

## Verdict

**ACCEPTED.** 21 new statement entries are recorded in COVERAGE, bringing the total to 164 (29 corrected or restricted). §4.3.s 18 numbered items in L2113–2454 are covered (Thm 4.10 through Ex 4.12), which makes 111 of 122 numbered results.

## Independent verification

The commands ran at `e3b32e1` with `.locks/CRITIC-HOLD` set. The full build was green, so this audit also covers the deferred audits of 05D, BL4 and SWEEP-C.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3518 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 5011 project declarations.` |
| Re-elaboration: `Defs/PoissonSizeBias`, `PoissonSizeBias/{Core, Subgraph, Monotone}/*` (21 files), committed `Statements/Sec4`, `Sec4Proofs` | 25/25 rc=0 |
| Wrapper identity for all 21 entries | type-checks |
| Axiom probe: the 21 wrappers plus 5 refutations (`not_thm4_17_printed`, `not_Ex4_8_L2361_printed`, `not_isExchangeableTuple_subgraphCopyIndicator_triangles`, `not_isIsolated_cycleGraph`, `not_isIsolated_cycleGraph_three`) | 26/26 `[propext, Classical.choice, Quot.sound]` (one multi-line output, parsed) |
| **Mutation 1:** in a scratch copy, the Thm 4.10 factor min{1, λ} changed to min{1, λ}/4. This is false for a single Bernoulli(p). | **rejected** (`T410Mut.lean:282`) |
| **Mutation 2:** in a scratch copy, the Thm 4.17 term 2Σpᵢ² changed to Σpᵢ²/4. This is false: the bound becomes negative for independent indicators. | **rejected** (`FKGMut.lean:220`) |

## Statements

An independent diff found all 21 integrated `def` bodies token-identical to the reviewed drafts. Every required change is applied:
- G1-1 to G1-4;
- G2-1 to G2-3;
- G3-1 to G3-5;
- BL-1 to BL-7.

The G2 subgraph route does not use Cor 4.12 or exchangeability (G2-1). The source issues for L2298 and L2352 are quoted verbatim.

Minor, accepted:
- `Ex4_8`'s λ-order conjunct uses 2k ≤ n, with constants (np)^k/(2k·2^k) ≤ λ ≤ (np)^k/(2k).
- `not_Thm4_17_printed` lives in the library as `not_thm4_17_printed`.
- `Cor4_11` applies the same library theorem as `Cor3_16`.
