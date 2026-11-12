/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Canon.Distributions
import Formalization.Canon.Metrics
import Formalization.Canon.MarkovAndEntropy
import Formalization.Canon.GraphsAndPerms
import Formalization.Canon.DefsUnification
import Formalization.Canon.LibraryDuplicates

/-!
# Stein's Method Formalization: Canonical Mathlib Bridges (`Formalization.Canon`)

Barrel module aggregating canonical bridges between project-specific definitions in
`Formalization/Defs/` and Mathlib `v4.34.0` standard representations:
* `Formalization.Canon.Distributions`: bridges for standard normal, Poisson, exponential,
  geometric, and Bernoulli laws;
* `Formalization.Canon.Metrics`: total variation factor-2 relation with signed measures,
  Kolmogorov distance CDF supremum, and Lipschitz-1 IPM Wasserstein characterization;
* `Formalization.Canon.MarkovAndEntropy`: anti-voter kernel invariance, Ornstein–Uhlenbeck
  kernel Gaussian bridge and stationarity, relative entropy / KL-divergence bridge to
  `InformationTheory.klDiv`, and Curie–Weiss Gibbs measure representation via `PMF.ofFintype`;
* `Formalization.Canon.GraphsAndPerms`: Erdős–Rényi law equality with `binomialRandom`,
  edge-pair equivalence with `Sym2.diagSetᶜ`, subgraph embedding characterization, and
  permutation fixed point and cycle type counts;
* `Formalization.Canon.DefsUnification`: monotonicity definitions as `Monotone`/`Antitone`,
  Stein operators expressed via Mathlib's `fwdDiff 1`, and Rademacher spin unifications;
* `Formalization.Canon.LibraryDuplicates`: cross-module library duplicate bridges
  (Clusters D2–D6).
-/
