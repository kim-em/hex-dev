/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.PrimeSelection
public import HexBerlekampZassenhaus.FactorizationData
public import HexBerlekampZassenhaus.Certificate
public import HexBerlekampZassenhaus.CertReify
public import HexBerlekampZassenhaus.ChoosePrimeData
public import HexBerlekampZassenhaus.FactorizationResult
public import HexBerlekampZassenhaus.Lattice
public import HexBerlekampZassenhaus.BhksCandidates
public import HexBerlekampZassenhaus.BhksRecover
public import HexBerlekampZassenhaus.Recombination
public import HexBerlekampZassenhaus.Factorization
public import HexBerlekampZassenhaus.EisensteinCore
public import HexBerlekampZassenhaus.IrreducibleCore
public import HexBerlekampZassenhaus.IrreducibleDecide
public import HexBerlekampZassenhaus.Factored
public import HexBerlekampZassenhaus.FactorProvider
public import HexBerlekampZassenhaus.RecombinationFactors
public import HexBerlekampZassenhaus.TrialFactorization
public import HexBerlekampZassenhaus.QuadraticFactors
public import HexBerlekampZassenhaus.PrimitiveFactors
public import HexBerlekampZassenhaus.FactorProduct
public import HexBerlekampZassenhaus.SmallModSingleton
public import HexBerlekampZassenhaus.WordCld

public section

/-!
The `HexBerlekampZassenhaus` library exposes the executable integer
Berlekamp-Zassenhaus factorization pipeline: normalization, good-prime
selection, Hensel-lift packaging, LLL-based recombination, bounded/default
factor entry points, and the integer irreducibility certificate checker.

The core checks (`HexBerlekampZassenhaus.Conformance`) and the
LLL-vs-exhaustive recombination cross-check
(`HexBerlekampZassenhaus.CrossCheck`) live under the `conformance/`
sub-project, which builds in the same `lake build`.
-/
