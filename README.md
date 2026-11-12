# Stein's Method in Lean 4 (`SteinMethod`)

> **Work in progress. The paper is not yet fully formalized.**

[![Lean and source checks](https://github.com/aaradhyapandeycs/steins-method-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/aaradhyapandeycs/steins-method-lean/actions/workflows/lean.yml)
[![Reader site](https://img.shields.io/badge/reader-site-blue)](https://aaradhyapandeycs.github.io/steins-method-lean/)

Lean 4 + Mathlib formalization of Nathan Ross's survey on Stein's method:

> Nathan Ross, *"Fundamentals of Stein's method"*, *Probability Surveys*, Vol. 8 (2011),
> pp. 210–293, DOI [`10.1214/11-PS182`](https://doi.org/10.1214/11-PS182),
> e-print [`arXiv:1109.1880v1`](https://arxiv.org/abs/1109.1880v1).

For current progress (number of proved results, open entries, and per-section status), see
the **[progress page](https://aaradhyapandeycs.github.io/steins-method-lean/)**.  Hard-coded
counts are not given here because they go stale; the site derives them from the critic ledger at
build time.

> [!IMPORTANT]
> Only [`docs/COVERAGE.md`](docs/COVERAGE.md) records accepted results.  Every other compiled
> declaration is work in progress and has not yet been independently reviewed.

---

## Scope

The formalization targets all numbered definitions, propositions, lemmas, theorems, corollaries,
and every substantive claim in the running text in Ross (2011), Sections 1–7.  Each printed
statement is matched to a Lean 4 `Prop` declaration in `Formalization/Statements/SecN.lean`; a
`_holds` proof wrapper in `Formalization/Statements/SecNProofs.lean` discharges the statement from
the proof library.

Where the source contains a typo, false hypothesis, or false proof step, a disclosed
`_corrected` or `_restricted` variant is formalized and, where feasible, a machine-checked
refutation of the printed text is proved; every such deviation is recorded in both
[`docs/SOURCE-ISSUES.md`](docs/SOURCE-ISSUES.md) and
[`docs/ERRATA-AND-DEVIATIONS.md`](docs/ERRATA-AND-DEVIATIONS.md).

---

## Toolchain

| Component | Version / commit |
|---|---|
| Lean | v4.34.0 |
| Mathlib | commit `5ed2965256430c3649e86755f9576b54eca72435` |

---

## Repository Layout

- `Formalization/Defs/` — Core definitions in namespace `SteinMethod` (normal and Poisson laws,
  `ℝ≥0∞`-valued integral probability metrics, Stein operators and solutions, and couplings).
- `Formalization/Metrics/`, `Formalization/Normal/`, `Formalization/Exchangeable/`,
  `Formalization/Poisson/`, `Formalization/RandomGraph/`, `Formalization/Kolmogorov/` —
  Proof libraries organized by mathematical topic.
- `Formalization/Statements/SecN.lean` — Self-contained theorem statements (`Prop`) importing
  `Formalization.Defs` only.
- `Formalization/Statements/SecNProofs.lean` — Proof wrappers (`<Name>_holds`) discharging each
  statement entry from the proof library.
- `Audit.lean` — Module-based kernel axiom and opacity audit.
- `docs/` — Source inventory, pinned source digests, definitional specifications, source errata,
  author rulings, and critic reviews.
- `site/` — Reader website source (builds from the hash-verified arXiv TeX at build time).
- `scripts/` — Build helpers, source fetcher, inventory generator, and audit checks.
- `.github/workflows/` — CI workflows (`lean.yml`, `pages.yml`).

---

## Reproduce the Build

1. **Fetch and hash-verify the arXiv source locally** (writes into git-ignored
   `source/upstream/`):
   ```bash
   python3 scripts/fetch_source.py
   ```
2. **Download the precompiled Mathlib `.olean` cache**:
   ```bash
   lake exe cache get
   ```
3. **Build the library and axiom audit**:
   ```bash
   lake build
   ```
4. **Run the standalone kernel axiom audit**:
   ```bash
   lake env lean Audit.lean
   ```
5. **Run all build, audit, forbidden-token, and statement-wrapper checks**:
   ```bash
   python3 scripts/check.py
   ```

---

## Axiom Policy

Every declaration in `Formalization` and `Formalization.*` depends on no axioms other than
`propext`, `Classical.choice` and `Quot.sound`.  `Audit.lean` machine-checks this.

---

## Process

Theorem statements are drafted and proved by **builder agents** that implement the formalization
track by track.  Results are then sent for independent review by **critic agents** that check
both correctness and faithfulness to the source.  Only the critic records a result as accepted
in [`docs/COVERAGE.md`](docs/COVERAGE.md).

---

## Errata and Deviations

[`docs/ERRATA-AND-DEVIATIONS.md`](docs/ERRATA-AND-DEVIATIONS.md) classifies every departure
from the printed text:

- **Class A** — false in a non-degenerate case (the printed statement is simply wrong in general).
- **Class B** — fails only at a boundary or outside the assumed range (domain restriction
  needed).
- **Class C** — false proof step; the conclusion survives under a corrected argument.
- **Class D** — ambiguous, ill-posed, or a pure notational issue (reading clarification needed).

Where a machine-checked refutation exists (a `not_…_printed` Lean declaration), it is
cited alongside the corrected formalization.

---

## Licences

- **Lean 4 and Python code** in this repository: [Apache-2.0](LICENSE) (see also
  [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) for third-party components).
- **Paper text**: Nathan Ross, *"Fundamentals of Stein's method"*, *Probability Surveys* 8 (2011)
  210–293, [DOI 10.1214/11-PS182](https://doi.org/10.1214/11-PS182), is published open-access by
  the Institute of Mathematical Statistics; *Probability Surveys* applies the
  [Creative Commons Attribution License](https://imstat.org/journals-and-publications/probability-surveys/probability-surveys-manuscript-submission/) to all its articles (the author retains copyright).
  The TeX source is **not** stored in this repository; the reader website fetches and hash-verifies
  the author's preprint `arXiv:1109.1880v1` (arXiv non-exclusive distribution license) at build time
  and renders it with attribution and a DOI link.  The rendering is unofficial, may differ from the
  published version, and changes only formatting.

---

## Citation

If you use this formalization, please cite it as:

```bibtex
@software{steins_method_lean4,
  author       = {aaradhyapandeycs},
  title        = {{Lean 4 Formalization of Fundamentals of Stein's Method}},
  year         = {2026},
  url          = {https://github.com/aaradhyapandeycs/steins-method-lean},
  note         = {Work in progress}
}
```

The formalized paper is:

```bibtex
@article{ross2011,
  author  = {Ross, Nathan},
  title   = {Fundamentals of {S}tein's method},
  journal = {Probability Surveys},
  volume  = {8},
  year    = {2011},
  pages   = {210--293},
  doi     = {10.1214/11-PS182}
}
```
