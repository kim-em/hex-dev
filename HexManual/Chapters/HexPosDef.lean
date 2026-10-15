/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexPosDefTheory
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexPosDef: exact positive-definiteness certificates" =>
%%%
tag := "hex-pos-def"
%%%

`HexPosDef` computes exact certificates for integer and Gaussian-integer
matrices. `HexPosDefTheory` interprets accepted certificates as Mathlib
positive definiteness or its negation and supplies the `pos_def` tactic.
The executable library is Mathlib-free.

# Proving positivity
%%%
tag := "hex-pos-def-tactic"
%%%

The tactic accepts closed square matrices over integers, rationals, reals
with rational entries, and complex numbers with rational components.
It recognizes literals, closed matrix functions, and bounded unfolding
of definitions, including the Cartan matrices directly.

```lean
example : (CartanMatrix.E 8).PosDef := by pos_def
```

The default method uses a lower triangular transform whose congruence
with the matrix is a positive diagonal matrix. The kernel checks the
transform's list certificate; it does not replay elimination.

For a symmetric real matrix with nonpositive off-diagonal entries, an
explicitly selected method instead solves for a positive vector and
checks that its matrix product is positive in every coordinate.

```lean
example : (CartanMatrix.E 8).PosDef := by
  pos_def (method := .positiveVector)
```

An unavailable specialization reports a capability decline. It does
not supply a negative result or automatically run the general method.

# A symmetrizer supplied by the caller
%%%
tag := "hex-pos-def-symmetrizer"
%%%

The E₈ Cartan matrix is already symmetric, so the constant symmetrizer
`1` suffices. The existential witness and its coordinate positivity are
ordinary Lean proof steps; `pos_def` proves the matrix assertion.

```lean
example : ∃ d : Fin 8 → ℤ, (∀ i, 0 < d i) ∧
    (Matrix.diagonal d * CartanMatrix.E 8).PosDef := by
  refine ⟨fun _ => 1, by simp, ?_⟩
  have h : (CartanMatrix.E 8).PosDef := by pos_def
  simpa using h
```

# Complex matrices and refutations
%%%
tag := "hex-pos-def-complex"
%%%

Gaussian arithmetic retains both components and conjugates certificate
vectors where required. The standard complex order is supplied by
`ComplexOrder`.

```lean
open scoped ComplexOrder in
example :
    (!![(2 : ℂ), Complex.I; -Complex.I, 2]).PosDef := by
  pos_def
```

A nonzero vector with zero quadratic value already refutes positive
definiteness. It need not be a kernel vector of the whole matrix.

```lean
open scoped ComplexOrder in
example :
    ¬ (!![(1 : ℂ), Complex.I; -Complex.I, 1]).PosDef := by
  pos_def
```

The tactic checks the evidence before reporting an opposite-polarity
result and leaves the requested goal unproved.

# Executable certificates and correspondence
%%%
tag := "hex-pos-def-api"
%%%

{docstring Hex.PosDef.Certificate}

{docstring Hex.PosDef.PositiveCert}

{docstring Hex.PosDef.NegativeCert}

{name}`Hex.PosDef.Int.certify` accepts an executable square integer
matrix and an optional method. {name}`Hex.PosDef.Gaussian.certify`
uses the general method. Successful returns have been rechecked against
the original rows. Unsupported methods and rejected producer
certificates are separate error constructors.

{docstring Hex.PosDef.Int.certify_check}

{docstring Hex.PosDef.Gaussian.certify_check}

The checkers validate exact shapes before list dot products. Positive
certificates establish positivity for arbitrary test vectors in the
target carrier. Negative certificates give either a non-Hermitian
coordinate or a nonzero vector with real nonpositive quadratic value.
The soundness theorems accept arbitrary certificates, without a producer
provenance assumption.

{docstring Hex.PosDefTheory.Int.checkPositive_sound}

{docstring Hex.PosDefTheory.Int.checkNegative_sound}

{docstring Hex.PosDefTheory.Gaussian.checkPositive_sound}

{docstring Hex.PosDefTheory.Gaussian.checkNegative_sound}

Rational quotation uses one positive denominator for the whole matrix.
The Theory wrappers transport the checked result along the proved
scaling equation. Real and complex entry equalities are proved by scalar
normalization; classical equality is not evaluated by the checker.

The unrestricted general producers always return a classification. Their
positive outcome is equivalent to positive definiteness of the decoded
matrix; the explicitly selected vector method promises soundness on success.

{docstring Hex.PosDefTheory.Int.certify_complete}

{docstring Hex.PosDefTheory.Gaussian.certify_complete}
