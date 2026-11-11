# Statement review: Track K (leftovers: Remark 3.5, Example 3.8, Example 3.9 P2, §3.2.1 CLT regime)

- **Critic:** Claude, 2026-11-11.
- **Source:** `SteinIntro_utf8.tex` L941–945, L1009–1024, L1349–1383, re-read in full.

## Verdict

The drafts are **approved with three required changes (K1–K3)**. Keep proving.

| Draft | TeX | Check | Verdict |
|---|---|---|---|
| `ouKernel` and `Rem3_5` | 1009–1024 | I checked all three properties for the kernel N(e^{−a}x, 1 − e^{−2a}):<br>(1) the mean increment is (e^{−a} − 1)x = −ax + O(a²);<br>(2) the second moment is (e^{−a} − 1)²x² + 1 − e^{−2a} = 2a + O(a²);<br>(3) the tail is ≈ exp(−ε²/(4a)) = o(a).<br>Reversibility and N(0, 1)-stationarity are standard. Reading o(a) as a → 0⁺ fits the forward increment. | approved; see K1 |
| ISSUE-TYPO-3.5 | 1020 | **Confirmed.** `\label{51}` is the display at L1032 inside the proof of Thm 3.7, so it prints "Theorem 3.16". **The same typo also occurs at L1096** (Example 3.6, "Theorem \ref{51}"); add that line to the entry. | confirmed |
| Example 3.8 | 1349–1353 | Exercise, so it gets a status line. | accepted |
| `Ex3_9_sizeBias` (0 ≤ p ≤ 1) | 1354–1383 | This resolves review-04 P2. It covers the cases n = 1 (no edges) and p = 1 with n ≥ 2 (X = 0, so D8 applies trivially). Generalizing an accepted entry this way assumes less, and is acceptable. | approved |
| `Sec3_2_1_triangles_clt_regime_restricted` | 941–945 | I re-derived the asymptotics: σ_n² ~ (c⁵/2)·n^{4−5α}, RHS₁ ~ 3√2·c^{−9/2}·n^{(9/2)α−1} and RHS₂ ~ C·n^{(7/2)α−1}. So the bound tends to 0 iff α < 2/9, which confirms the printed 2/9. At α = 0 the literal p_n ∼ 1 allows p_n → 1, where there is no CLT (p_n = 1 − n^{−5}); the extra condition c < 1 at α = 0 is justified as a disclosed restriction (ISSUE-3.2.1 addendum). The conclusion includes d_W and d_K → 0, which captures "satisfies a CLT". | approved; see K2 and K3 |

## Required changes

- **K1. `Rem3_5` is partial; say so.**
  - The remark also asserts that "these three properties determine the O-U diffusion process". That is a uniqueness claim for the martingale problem, and it is not formalized.
  - Write that in the docstring, and record it in the track file as **open**. COVERAGE will mark Remark 3.5 as *partial*.
  - Recommended: add your Stein-pair witness, `IsSteinPair (stdNormalLaw ⊗ₘ ouKernel a) (1 - exp (-a)) Prod.fst Prod.snd` for a > 0, as a conjunct. It is the precise content of "Item 1 corresponds to the a-Stein pair linearity condition".
- **K2. Printed parenthetical at L942–943:** "p ∼ n^{−α} for some 0 ≤ α < 1 (so that Var(T) → ∞)". Add a conjunct, or a separate entry, stating Var(T_n) → ∞ for all 0 ≤ α < 1, with c < 1 at α = 0. It is true: σ² ≳ C(n,3)p³ ~ (c³/6)·n^{3−3α}, which tends to ∞ for α < 1. The current entry only covers α < 2/9.
- **K3. Cited claim at L944:** "only a subset of the regime where normal convergence holds [ruc88]" (Ruciński 1988). Record it in the track file as an **open cited claim**. It needs Ruciński's characterization, for which a sufficient condition is np → ∞ and n²(1 − p) → ∞. It may be deferred, but it should be listed, not dropped. Also give a status line for the speculative sentence at L944–945.

## Notes

- `ouKernel` uses `Kernel.id` for a ≤ 0 as a totality convention. That is fine, because the entry only uses a > 0.
- Use `scripts/lean-remote.sh` for compile checks.
