# Critic review: batch-CANON phase 1 (docs/reviews/canon-audit.md, 312ec25)

Verdict: **APPROVED for phase 2**, with the decisions below.

Spot checks against the pinned Mathlib (`.lake/packages/mathlib/Mathlib`): no file mentions Wasserstein,
Kantorovich or a TV distance; the "Kolmogorov" hits are unrelated (Kolmogorov spaces, extension), so
`ipm`, `kolmogorovDist`, `wassersteinDist`, `tvDist` are correctly KEEP/BRIDGE. `poissonMeasure`,
`gaussianReal`, `ProbabilityTheory.cdf`, `Kernel.Invariant`, `SignedMeasure.totalVariation` and
`SimpleGraph.binomialRandom` exist at the cited files. The factor-2 relation between Mathlib's total variation of
μ − ν and Ross's sup-over-sets d_TV is correct for probability measures.

Decisions on §3.2:
1. (a) `shiftedGeomLaw`/`posGeomLaw` and (c) `IsIncreasing`/`IsDecreasing`: REPLACE allowed, but only as
   `abbrev` of the canonical notion (posGeomLaw := shiftedGeomLaw; IsIncreasing := Monotone; IsDecreasing :=
   Antitone) and only if the `rfl`/`Iff.rfl` bridge compiles first, every Statements file builds unchanged and
   the Prop-body diff of Statements is empty. Otherwise BRIDGE.
   (b) `embedGraph`: BRIDGE only (`embedGraph_eq_map`), no redefinition.
   (d) `Sanity.lean` witnesses (not imported by Statements): REPLACE by `spin`, `bernoulliMeasure`, `Bool.toNat`,
   `uniformOn` is approved, again only with the bridge proved first.
2. Library duplicates (clusters D2–D6): add `Formalization/Canon/LibraryDuplicates.lean` with bridge lemmas only.
   It may import the proof modules that define those helpers; no Statements file may import any Canon file.

Requirements for phase 2 lemmas:
- Each lemma states the exact relation (equality, `Iff`, `Equiv`), with only the hypotheses the relation needs
  (e.g. probability measures for the TV factor 2, finite first moments for the Wasserstein characterization),
  and a docstring giving the Mathlib notion and the source line of the book's definition.
- `erdosRenyi_eq_binomialRandom` and every claimed `rfl` must actually be proved; if one fails, record it as
  KEEP with the reason instead of weakening it.
- I will verify with: statement-diff (must be empty), full build, axiom audit, per-file re-elaboration, axiom
  probes on the bridges, and a mutation control on at least the TV factor 2 and the Kolmogorov bridge.
