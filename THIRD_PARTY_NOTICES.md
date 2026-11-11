# Third-Party Notices

This repository (`steins-method-lean`) is distributed under the Apache License, Version 2.0
(see [`LICENSE`](LICENSE) and [`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt)).

It incorporates workflow governance scripts, templates, and agent skill folders from external
open-source projects, and formalizes mathematical results from Nathan Ross's 2011 survey.
Required licence and provenance attributions are recorded below.

---

## 1. Mathematical Source Formalized

* **Title**: *Fundamentals of Stein's method*
* **Author**: Nathan Ross
* **Publication**: *Probability Surveys*, Vol. 8 (2011), pp. 210–293,
  DOI: `10.1214/11-PS182`, published open-access under
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) by the Institute of
  Mathematical Statistics.
* **Pinned e-print**: `arXiv:1109.1880v1`; exact SHA-256 hash recorded in
  [`source/provenance.json`](source/provenance.json).

**The paper text is not redistributed.**  The reader website fetches the arXiv TeX source at
build time, verifies it against the pinned SHA-256 hash, and renders it under CC BY 4.0 with
the following attribution on every page:

> N. Ross, "Fundamentals of Stein's method", *Probability Surveys* 8 (2011) 210–293,
> DOI 10.1214/11-PS182, licensed [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/);
> text rendered from arXiv:1109.1880v1.  This rendering is unofficial and may differ from the
> published version.

All Lean 4 formalizations, proofs, and reusable library APIs in `Formalization/` are original
Lean 4 code authored for this repository under Apache-2.0.

---

## 2. Scott Armstrong — `LeanAutoformalizationSkills` (CC BY 4.0)

* **Source**: <https://github.com/scottnarmstrong/LeanAutoformalizationSkills>
* **Creator**: Scott Armstrong
* **License**: Creative Commons Attribution 4.0 International Public License
  ([`LICENSES/CC-BY-4.0.txt`](LICENSES/CC-BY-4.0.txt) /
  <https://creativecommons.org/licenses/by/4.0/>)
* **Disclaimer of Warranties**: The Licensed Material is provided "as-is" and
  "as-available" without warranties of any kind (see Section 5 of
  [`LICENSES/CC-BY-4.0.txt`](LICENSES/CC-BY-4.0.txt)).

### Adapted Workflow Design and Agent Skills (Development Process)

Workflow governance conventions (`Audit.lean` kernel-axiom gate, `scripts/check.py` mechanical
token and statement-wrapper checks, and builder/critic verification protocols) draw on
`LeanAutoformalizationSkills` by Scott Armstrong (CC BY 4.0,
[`LICENSES/CC-BY-4.0.txt`](LICENSES/CC-BY-4.0.txt)), which in turn adapts skill reference
material from:

### `cameronfreer/lean4-skills` (MIT)

Upstream skill guidance referenced during development originates in part from
<https://github.com/cameronfreer/lean4-skills>:

```text
MIT License

Copyright (c) 2025 Lean 4 Theorem Proving Skill Contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

### `leanprover/skills` (Apache-2.0)

Upstream workflow references cite <https://github.com/leanprover/skills> under the Apache
License, Version 2.0 (<https://www.apache.org/licenses/LICENSE-2.0>).

---

## 4. Reader Website (`site/`) and MathJax (Apache-2.0)

* **Reader architecture**: adapted from
  <https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean> under the Apache
  License, Version 2.0 ([`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt)).
* **MathJax 3**: mathematical formulas on the rendered website are typeset client-side by
  [MathJax](https://www.mathjax.org/) under the Apache License, Version 2.0
  (<https://www.apache.org/licenses/LICENSE-2.0>).

---

## 5. `leanprover-community/mathlib4` (Apache-2.0)

* **Source**: <https://github.com/leanprover-community/mathlib4>
  (commit `5ed2965256430c3649e86755f9576b54eca72435`, pinned as `v4.34.0`)
* **License**: Apache License, Version 2.0 (<https://www.apache.org/licenses/LICENSE-2.0>)

Mathlib is used as a dependency via Lake; its source is not vendored in this repository.
