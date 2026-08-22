/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSparsePoly

public section

/-!
Downstream module-boundary checks for the kernel-reduction closure of
`Hex.SparsePoly`: `SparsePolyCanonical`, `addTerm`, `ofTerms`, `coeff`,
and the `DecidableEq` instance must reduce under `decide` from a module
that only imports the public library. A failure here means an `@[expose]`
or `@[csimp]` boundary regressed.
-/

namespace Hex.SparsePoly.KernelTests

open Hex
open scoped Hex

abbrev P := SparsePoly Int

example : SparsePolyCanonical (#[(0, 5), (3, 1)] : Array (Nat × Int)) := by
  decide +kernel

example : ¬ SparsePolyCanonical (#[(3, 1), (0, 5)] : Array (Nat × Int)) := by
  decide +kernel

example : ¬ SparsePolyCanonical (#[(0, 0)] : Array (Nat × Int)) := by
  decide +kernel

-- `ofTerms` canonicalises: unsorted input, repeated exponents summed,
-- zeros dropped.
example : (#sp[(3, 1), (0, 5)] : P) = #sp[(0, 5), (3, 1)] := by
  decide +kernel

example : (#sp[(1, 2), (1, 3)] : P) = #sp[(1, 5)] := by
  decide +kernel

example : (#sp[(0, 0)] : P) = 0 := by
  decide +kernel

example : (#sp[(1, 2), (1, -2)] : P) = 0 := by
  decide +kernel

-- `addTerm` inserts, combines, and deletes.
example : ((0 : P).addTerm 5 3).coeff 5 = 3 := by
  decide +kernel

example : ((#sp[(5, 3)] : P).addTerm 5 (-3)) = 0 := by
  decide +kernel

-- `coeff` reduces at a large exponent: the cost is the term count, not
-- the degree.
example : (#sp[(0, 5), (1000000, 3)] : P).coeff 1000000 = 3 := by
  decide +kernel

example : (#sp[(0, 5), (1000000, 3)] : P).coeff 999999 = 0 := by
  decide +kernel

-- `add` and `mul` reduce as specified: the linear merge and the
-- canonicalised pairwise product.
example : (#sp[(0, 1), (3, 4)] : P) + #sp[(3, -4), (9, 2)] =
    #sp[(0, 1), (9, 2)] := by
  decide +kernel

example : (#sp[(0, 1), (1, 1)] : P) * #sp[(0, -1), (1, 1)] =
    #sp[(0, -1), (2, 1)] := by
  decide +kernel

-- `ofDense` reduces.
example : SparsePoly.ofDense (#p[5, 0, 0, 1] : DensePoly Int) =
    #sp[(0, 5), (3, 1)] := by
  decide +kernel

example : SparsePoly.ofDense ((0 : P).toDense) = 0 := by
  decide +kernel

-- The `DecidableEq` instance reduces across the module boundary.
example : (0 : P) ≠ #sp[(0, 1)] := by
  decide +kernel

example : decide (#sp[(2, 7)] = (#sp[(2, 7)] : P)) = true := by
  decide +kernel

end Hex.SparsePoly.KernelTests
