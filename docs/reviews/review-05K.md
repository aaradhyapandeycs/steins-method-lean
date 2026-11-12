# Critic review 05K: Track K leftovers (Remark 3.5 O-U properties; §3.2.1 CLT-regime addendum), `bcd5fcc`

- **Critic:** Claude, 2026-11-11.
- **Statement review:** stmts-review-05K (K1–K3).

## Verdict

**ACCEPTED.** 2 new entries are recorded in COVERAGE, bringing the total to 200 (36 corrected or restricted). Remark 3.5 is now **partial**, which makes 119 of 122 numbered results.

- **`Rem3_5`** covers:
  - `ouKernel`, which satisfies the three infinitesimal properties at L1013–1015;
  - reversibility, with N(0, 1) stationary;
  - the Stein-pair witness `IsSteinPair (N(0,1) ⊗ ouKernel a) (1 − e^{−a})` (K1).

  The uniqueness sentence at L1018 ("these three properties determine the O-U diffusion") is BL8, still open; the docstring says so.
- **`Sec3_2_1_triangles_clt_regime_restricted`:**
  - for p ∼ c·n^{−α}, the §3.2.1 Stein bound tends to 0 iff α < 2/9;
  - plus Var(Tₙ) → ∞ for 0 ≤ α < 1, with c < 1 when α = 0 (K2).

  K3, the Ruciński criterion, is covered by BL7.

## Independent verification

The commands ran at `0ed68ab` with `.locks/CRITIC-HOLD` set.

| Check | Result |
|---|---|
| `lake build` | exit 0 (3545 jobs) |
| `lake env lean Audit.lean` | exit 0, `Axiom audit passed for 5691 project declarations.` |
| Re-elaboration: `Defs/OrnsteinUhlenbeck`, `Leftovers/{OrnsteinUhlenbeck, RandomGraphAddenda}`, `RandomGraph/IsolatedCoupling`, committed `Statements/Sec3`, `Sec3Proofs` | 6/6 rc=0 |
| Axiom probe: both wrappers | 2/2 `[propext, Classical.choice, Quot.sound]` |
| **Mutation 1:** in a scratch copy, the Stein-pair constant 1 − e^{−a} changed to 1 − e^{−2a} | **rejected** |
| **Mutation 2:** in a scratch copy, the threshold α < 2/9 changed to α < 1/4. This is false: the bound tends to 3√2 > 0 for α ∈ [2/9, 1/4). | **rejected** |
