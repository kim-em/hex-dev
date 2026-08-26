/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexSmithMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexSmith: integer Smith normal form" =>
%%%
tag := "hex-smith"
%%%

# Introduction
%%%
tag := "hex-smith-intro"
%%%

`HexSmith` computes canonical Smith normal form for rectangular integer
matrices. The Mathlib-free executable layer provides a form-only path, a
transform-producing path with explicit inverses, an independent certificate
checker, invariant factors, system criteria, and abelian-presentation data.

The companion `HexSmithMathlib` is correspondence-only: it builds Mathlib's
Smith-basis and quotient-decomposition structures from the executable output
without running a second Smith computation.

# Form-only and certified-transform use
%%%
tag := "hex-smith-entry-points"
%%%

Use {name}`Hex.Matrix.snf` when only the canonical matrix is needed. The
projections {name}`Hex.Matrix.snfRank` and
{name}`Hex.Matrix.invariantFactors` use the same form-only engine and do not
accumulate transforms. Use {name}`Hex.Matrix.snfData` when a change of basis
or replayable certificate is required.

{docstring Hex.Matrix.snf}

{docstring Hex.Matrix.snfRank}

{docstring Hex.Matrix.invariantFactors}

{docstring Hex.Matrix.snfData}

{docstring Hex.Matrix.snfCert}

The following code is elaborated with the manual. The input diagonal does not
yet form a divisibility chain: the canonical output replaces `(6,4)` by
`(2,12)`.

```lean
open Hex Hex.Matrix

namespace HexSmithChapterExample

private def A : Matrix Int 2 2 := #m[6, 0; 0, 4]

#guard snf A == #m[2, 0; 0, 12]
#guard (invariantFactors A).toList == [2, 12]

private def S : SmithData 2 2 := snfData A

#guard S.left * A * S.right == diagMatrix S.diag 2 2
#guard S.left * S.leftInv == Matrix.identity 2
#guard S.right * S.rightInv == Matrix.identity 2
#guard snfCert A S (S.left * A)

end HexSmithChapterExample
```

Diagonal input has a specialized route that bypasses the classical pivot
loop. Its transform-producing counterpart follows the same fixed gcd/lcm
network.

{docstring Hex.Matrix.snfDiagonal}

{docstring Hex.Matrix.snfDiagonalData}

# Systems and presentations
%%%
tag := "hex-smith-systems"
%%%

The Smith layer characterizes integer solvability by transformed-coordinate
divisibility and a trailing-zero condition. The executable coefficient solver
is the existing Hermite operation {name}`Hex.Matrix.latticeCoeffs`; Smith does
not duplicate it.

{docstring Hex.Matrix.solvable_iff_dvd}

{docstring Hex.Matrix.latticeCoeffs}

```lean
open Hex Hex.Matrix

namespace HexSmithSystemsExample

private def A : Matrix Int 2 2 := #m[2, 0; 0, 6]
private def solvable : Vector Int 2 := #v[4, 18]
private def impossible : Vector Int 2 := #v[1, 0]

#guard (latticeCoeffs A solvable).isSome
#guard !(latticeCoeffs A impossible).isSome

private def presentation : Matrix Int 2 3 :=
  #m[2, 0, 0; 0, 6, 0]

#guard (abelianStructure presentation).freeRank == 1
#guard
  (abelianStructure presentation).torsionFactors == #[2, 6]

end HexSmithSystemsExample
```

{docstring Hex.Matrix.abelianStructure}

{docstring Hex.Matrix.abelianStructure_torsionFactors}

{docstring Hex.Matrix.smithBasis}

# Determinantal divisors and uniqueness
%%%
tag := "hex-smith-uniqueness"
%%%

{name}`Hex.Matrix.detDivisor` is defined independently as the gcd of all
minors of a fixed size. The Smith contract identifies it with the product of
the leading invariant factors; comparing those products proves that any two
valid Smith data records have the same rank, invariant factors, and form.

{docstring Hex.Matrix.detDivisor}

{docstring Hex.Matrix.IsSNF.detDivisor_eq}

{docstring Hex.Matrix.IsSNF.rank_eq}

{docstring Hex.Matrix.IsSNF.diag_eq}

```lean
open Hex Hex.Matrix

namespace HexSmithUniquenessExample

example (A : Matrix Int 2 2) :
    detDivisor A 1 =
      if 1 ≤ (snfData A).rank then
        (((snfData A).diag.take 1).foldl (· * ·) 1).natAbs
      else 0 :=
  (snfData_isSNF A).detDivisor_eq 1

example {A : Matrix Int 2 2} {S T : SmithData 2 2}
    (hS : IsSNF A S) (hT : IsSNF A T) :
    diagMatrix S.diag 2 2 = diagMatrix T.diag 2 2 :=
  hS.form_eq hT

end HexSmithUniquenessExample
```

# Failure and complexity guidance
%%%
tag := "hex-smith-guidance"
%%%

`snf`, `snfRank`, and `invariantFactors` are total. A failed
`latticeCoeffs` result means no verified coefficient vector was found;
completeness says it returns `some` whenever an integer solution exists. A
false `snfCert` result means only that the supplied data failed replay and
must not be trusted; {name}`Hex.Matrix.snfCert_sound` is the acceptance
boundary.

The general implementation is the classical pivot loop. Its declared matrix
operation model is cubic, while integer coefficient growth is tracked
separately in the committed performance report. `snfDiagonal` uses a
quadratic fixed network and has a measured, growing advantage over routing
the same input through general elimination. Transform-producing calls cost
more because they maintain four dense matrices.

Do not evaluate `detDivisor` to compute invariants on nontrivial matrices: it
enumerates exponentially many minors. Compute {name}`Hex.Matrix.invariantFactors`
and use {name}`Hex.Matrix.IsSNF.detDivisor_eq` to reason about the result.

# The Mathlib correspondence
%%%
tag := "hex-smith-mathlib"
%%%

The bridge realizes the executable right inverse as an ambient basis and the
independent left-transformed relation rows as a basis of the row span.

{docstring HexSmithMathlib.ambientBasis}

{docstring HexSmithMathlib.relationBasis}

These bases and the executable invariant factors construct Mathlib's
simultaneous Smith-normal-form structure. The separate chain theorem restores
the canonical order not stored in that structure.

{docstring HexSmithMathlib.smithNormalForm}

{docstring HexSmithMathlib.smithNormalForm_chain}

Finally, the quotient equivalence separates free coordinates from cyclic
torsion factors, again using the same executable invariant factors.

{docstring HexSmithMathlib.quotientEquiv}

# Cross-references
%%%
tag := "hex-smith-cross-references"
%%%

`HexSmith` uses {ref "hex-matrix"}[HexMatrix] for matrix operations and
{ref "hex-determinant"}[HexDeterminant] for minors and determinants. The
Hermite solver and lattice-index operations are supplied by `HexHermite`.
