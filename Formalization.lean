/-
Copyright (c) 2026 Aaradhya Pandey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaradhya Pandey
-/
import Formalization.Defs
import Formalization.Defs.Sanity
import Formalization.BerryEsseen.BerryEsseen
import Formalization.BerryEsseen.Cantelli
import Formalization.BerryEsseen.CharFunBounds
import Formalization.BerryEsseen.FejerKernel
import Formalization.BerryEsseen.FejerSmoothing
import Formalization.Exchangeable.AntiVoter
import Formalization.Exchangeable.AntiVoterGraph
import Formalization.Exchangeable.AntiVoterIrreducible
import Formalization.Exchangeable.AntiVoterUnique
import Formalization.Exchangeable.Basic
import Formalization.Exchangeable.IndepSumPair
import Formalization.Exchangeable.IndepSumPairBounds
import Formalization.Exchangeable.SteinPairBound
import Formalization.Geometric.Basic
import Formalization.Geometric.Equilibrium
import Formalization.Geometric.OpeningBound
import Formalization.Geometric.UniformAttachment
import Formalization.Kolmogorov.Basic
import Formalization.Kolmogorov.BinomialOrder
import Formalization.Kolmogorov.BinomialUpper
import Formalization.Kolmogorov.ExchangeableBound
import Formalization.Kolmogorov.SolutionBounds
import Formalization.Kolmogorov.ZeroBiasBound
import Formalization.Leftovers.Ex36SmallN
import Formalization.Leftovers.Ex36SmallNHelper
import Formalization.Leftovers.Ex38IndepSum
import Formalization.Metrics.Basic
import Formalization.Normal.DependencyCount
import Formalization.Normal.DependencyCounterexample
import Formalization.Normal.DependencyNeighborhoods
import Formalization.Normal.IndependentSums
import Formalization.Normal.KolmogorovSolution
import Formalization.Normal.MillRatio
import Formalization.Normal.SolutionBounds
import Formalization.Normal.SteinLemma
import Formalization.Normal.WassersteinBound
import Formalization.Poisson.SteinLemma
import Formalization.PoissonDep.Basic
import Formalization.PoissonDep.ErdosRenyiBounds
import Formalization.PoissonDep.ErdosRenyiCounterexample
import Formalization.PoissonDep.ErdosRenyiLaw
import Formalization.PoissonDep.HeadRunAsymptotics
import Formalization.PoissonDep.HeadRuns
import Formalization.PoissonDep.LocalDependence
import Formalization.PoissonExch.FixedPointsTrueRate
import Formalization.RandomGraph.ErdosRenyi
import Formalization.RandomGraph.IsolatedCoupling
import Formalization.RandomGraph.IsolatedMoments
import Formalization.RandomGraph.IsolatedVertices
import Formalization.RandomGraph.Triangles
import Formalization.RandomGraph.TrianglesRucinskiCLT
import Formalization.RandomGraph.TrianglesRucinskiCoupling
import Formalization.RandomGraph.TrianglesRucinskiIdentities
import Formalization.RandomGraph.TrianglesRucinskiMoments
import Formalization.RandomGraph.TrianglesRucinskiNecessity
import Formalization.RandomGraph.TrianglesRucinskiSufficiency
import Formalization.SizeBias.Basic
import Formalization.SizeBias.Coupling
import Formalization.ZeroBias.Basic
import Formalization.ZeroBias.Coupling
import Formalization.ZeroBias.Density
import Formalization.ZeroBias.Lindeberg
import Formalization.ZeroBias.LindebergFeller
import Formalization.Statements.Sec1
import Formalization.Statements.Sec2
import Formalization.Statements.Sec3
import Formalization.Statements.Sec4
import Formalization.Statements.Sec6
import Formalization.Statements.Sec1Proofs
import Formalization.Statements.Sec2Proofs
import Formalization.Statements.Sec3Proofs
import Formalization.Statements.Sec4Proofs
import Formalization.Statements.Sec6Proofs

/-!
# Root Formalization Module (`Formalization`)

Imports core definitions, non-vacuity sanity checks, proof libraries, statement indices, and
`_holds` proof wrappers for Nathan Ross, *"Fundamentals of Stein's method"* (`arXiv:1109.1880v1`).
-/
