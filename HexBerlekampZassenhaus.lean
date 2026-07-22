/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus.PrimeSelection
public import HexBerlekampZassenhaus.Records
public import HexBerlekampZassenhaus.Certificate
public import HexBerlekampZassenhaus.ChoosePrimeData
public import HexBerlekampZassenhaus.ReassemblyProofs
public import HexBerlekampZassenhaus.Lattice
public import HexBerlekampZassenhaus.BhksCandidates
public import HexBerlekampZassenhaus.BhksRecover
public import HexBerlekampZassenhaus.Recombination
public import HexBerlekampZassenhaus.FactorEntryPoints
public import HexBerlekampZassenhaus.IrreducibleCore
public import HexBerlekampZassenhaus.RecombineProofs
public import HexBerlekampZassenhaus.TrialProofs
public import HexBerlekampZassenhaus.QuadraticRootProofs
public import HexBerlekampZassenhaus.PrimitivityProofs
public import HexBerlekampZassenhaus.ProductProofs
public import HexBerlekampZassenhaus.SmallModSingleton
public import HexBerlekampZassenhaus.WordCld

public section

/-!
The `HexBerlekampZassenhaus` library exposes the executable integer
Berlekamp-Zassenhaus factorization pipeline: normalization, good-prime
selection, Hensel-lift packaging, LLL-based recombination, bounded/default
factor entry points, and the integer irreducibility certificate checker.

The Phase 3 core checks (`HexBerlekampZassenhaus.Conformance`) and the
SPEC-sanctioned LLL-vs-exhaustive recombination cross-check
(`HexBerlekampZassenhaus.CrossCheck`) live under the `conformance/`
sub-project, which builds in the same `lake build`.
-/
