/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexDeterminantalIdealFixtures

/-!
Core executable conformance checks for `hex-determinantal-ideal`.

Oracle: SymPy, through `scripts/oracle/detideal_sympy.py` on the committed
stream `conformance-fixtures/HexDeterminantalIdeal/detideal.jsonl`
Mode: `if_available` locally, required in release CI

Covered operations:
- `minors r A` on integer and on symbolic matrices, at `r = 0`, inside the
  shape, and above it;
- `detIdealGens r A`, including the zero-dropping and duplicate-dropping
  behaviour;
- `Matrix.map`, through the lift of the coefficients from `Int` to `Rat`;
- `specialize A p` on integer and on symbolic matrices;
- `rankAt A p` and the `Decidable` decision of `InLocus r A p`.

Covered properties:
- the enumeration order is colexicographic, rows outer and columns inner:
  the six `2 × 2` minors of a `2 × 4` matrix of distinct integers pin the
  order of the column selections and reject a lexicographic enumeration;
- `(minors r A).length = n.choose r * m.choose r`;
- `minors 0 A = [1]` on every shape, and `minors r A = []` once `r` exceeds a
  dimension, so `I_0(A)` is the unit ideal and `I_r(A)` the zero ideal;
- `minors r A.transpose` is a permutation of `minors r A`, and on a `3 × 3`
  matrix at `r = 2` it is a different list, so the permutation is not an
  equality;
- the classical closed forms: the `2 × 3` generic matrix's three maximal
  minors, the Vandermonde determinants `∏_{i<j} (x_j - x_i)`, and the
  bordered identity's single generator `t - v · u`;
- `detIdealGens r A` keeps one copy of a repeated minor while `minors r A`
  keeps both, and keeps first occurrences in enumeration order;
- the rank-versus-minors theorem, executably: `rankAt A p < r` agrees with
  the decision of `InLocus r A p`, including at `r = 0` and above the shape,
  and `rank_eq_iff_minors` applied to a
  `3 × 3` matrix over `Rat` of rank `2`;
- invariance under an explicit unimodular integer left factor: the rank and
  the locus decision at two points are unchanged.

Covered edge cases:
- the `0 × 0`, `0 × 2` and `2 × 0` shapes at `r = 0`;
- `r` above the shape for a square matrix and for both rectangular
  orientations;
- the zero matrix, whose minors are all zero and whose generating list is
  empty;
- a matrix with two equal columns of indeterminates, whose minors repeat and
  include a zero;
- Vandermonde points with two equal coordinates, with all coordinates equal,
  and with distinct coordinates;
- bordered identities at points on and off the hypersurface `t = v · u`.
-/

namespace Hex.DeterminantalIdealConformance

open Hex
open Hex.Matrix
open Hex.MvPoly
open Hex.DeterminantalIdealFixtures

/-! # `minors`: enumeration order -/

/-! The `2 × 2` minors of a `2 × 4` matrix of distinct integers, in the
colexicographic column order `01, 02, 12, 03, 13, 23`. -/
#guard Matrix.minors 2 distinct24 =
  [C (-3), C (-4), C 1, C (-7), C (-2), C (-5)]

/-! The three maximal minors of the generic `2 × 3` matrix. -/
#guard Matrix.minors 2 generic23 =
  [X 0 * X 4 - X 1 * X 3, X 0 * X 5 - X 2 * X 3, X 1 * X 5 - X 2 * X 4]

/-! Two equal columns: the first minor vanishes and the other two coincide. -/
#guard Matrix.minors 2 equalCols =
  [0, X 0 * X 3 - X 1 * X 2, X 0 * X 3 - X 1 * X 2]

/-! Every minor of the zero matrix is zero. -/
#guard Matrix.minors 1 zero22 = List.replicate 4 0

/-! # `minors`: length and the two boundary conventions -/

#guard (Matrix.minors 2 distinct24).length = Nat.choose 2 2 * Nat.choose 4 2
#guard (Matrix.minors 1 zero22).length = Nat.choose 2 1 * Nat.choose 2 1
#guard (Matrix.minors 2 vandermonde3).length = Nat.choose 3 2 * Nat.choose 3 2
#guard (Matrix.minors 2 generic23).length = Nat.choose 2 2 * Nat.choose 3 2

/-! `r = 0`: one zero-sized minor, equal to `1`, on every shape. -/
#guard Matrix.minors 0 empty00 = [1]
#guard Matrix.minors 0 empty02 = [1]
#guard Matrix.minors 0 empty20 = [1]
#guard Matrix.minors 0 small23 = [1]

/-! `r > min n m`: no minors, for a square matrix and for both rectangular
orientations. -/
#guard Matrix.minors 3 square22 = []
#guard Matrix.minors 3 small23 = []
#guard Matrix.minors 3 small32 = []

/-! # `minors`: the transpose permutes the enumeration -/

#guard (Matrix.minors 2 generic32).isPerm (Matrix.minors 2 generic23)
#guard (Matrix.minors 1 bordered1.transpose).isPerm (Matrix.minors 1 bordered1)
#guard (Matrix.minors 2 vandermonde3.transpose).isPerm
  (Matrix.minors 2 vandermonde3)

/-! With both enumerations nontrivial the permutation is not an equality: the
transpose swaps the outer and inner loops. -/
#guard Matrix.minors 2 vandermonde3.transpose ≠ Matrix.minors 2 vandermonde3

/-! # `detIdealGens` -/

/-! All six minors are nonzero and pairwise distinct, so nothing is dropped. -/
#guard Matrix.detIdealGens 2 distinct24 = Matrix.minors 2 distinct24

/-! Every minor is zero, so the generating list is empty. -/
#guard Matrix.detIdealGens 1 zero22 = []

/-! The zero minor is dropped and the repeated minor keeps one copy. -/
#guard Matrix.detIdealGens 2 equalCols = [X 0 * X 3 - X 1 * X 2]

/-! Repeats among several distinct values keep the first occurrences, in
enumeration order. -/
#guard Matrix.minors 2 repeatCols = [C 1, 0, C (-1), C 1, 0, C 1]
#guard Matrix.detIdealGens 2 repeatCols = [C 1, C (-1)]

/-! `I_0(A)` is the unit ideal and `I_r(A)` above the shape is the zero
ideal. -/
#guard Matrix.detIdealGens 0 empty00 = [1]
#guard Matrix.detIdealGens 3 square22 = []

/-! The Vandermonde determinants `∏_{i<j} (x_j - x_i)`. -/
#guard Matrix.detIdealGens 2 vandermonde2 = [X 1 - X 0]
#guard Matrix.detIdealGens 3 vandermonde3 =
  [(X 1 - X 0) * (X 2 - X 0) * (X 2 - X 1)]

/-! The bordered identity of size `k + 1` has `1` among its `k × k` minors,
and the single generator `t - v · u` at `r = k + 1`. -/
#guard (Matrix.minors 1 bordered1).contains 1
#guard (Matrix.minors 2 bordered2).contains 1
#guard Matrix.detIdealGens 2 bordered1 = [X 2 - X 0 * X 1]
#guard Matrix.detIdealGens 3 bordered2 = [X 4 - X 0 * X 2 - X 1 * X 3]

/-! # `Matrix.map`: lifting the coefficients to the field -/

#guard (toRat small23).rows = #v[#v[C 1, C 2, C 3], #v[C 4, C 5, C 6]]
#guard (toRat zero22).rows = #v[#v[0, 0], #v[0, 0]]
#guard (toRat generic23).rows = #v[#v[X 0, X 1, X 2], #v[X 3, X 4, X 5]]

/-! # `specialize` -/

#guard (Matrix.specialize (toRat vandermonde2) (pointOf #v[2, 5])).rows =
  #v[#v[1, 2], #v[1, 5]]
#guard (Matrix.specialize (toRat zero22) (pointOf #v[])).rows =
  #v[#v[0, 0], #v[0, 0]]
#guard (Matrix.specialize (toRat bordered2) (pointOf #v[2, 3, 5, 7, 31])).rows =
  #v[#v[1, 0, 2], #v[0, 1, 3], #v[5, 7, 31]]

/-! # `rankAt` -/

/-- info: 2 -/
#guard_msgs in #eval Matrix.rankAt (toRat vandermonde2) (pointOf #v[2, 5])

/-- info: 1 -/
#guard_msgs in #eval Matrix.rankAt (toRat vandermonde2) (pointOf #v[3, 3])

/-- info: 0 -/
#guard_msgs in #eval Matrix.rankAt (toRat zero22) (pointOf #v[])

/-- info: 2 -/
#guard_msgs in #eval Matrix.rankAt (toRat distinct24) (pointOf #v[])

/-- info: 3 -/
#guard_msgs in #eval Matrix.rankAt (toRat vandermonde3) (pointOf #v[1, 2, 3])

/-- info: 2 -/
#guard_msgs in #eval Matrix.rankAt (toRat vandermonde3) (pointOf #v[1, 1, 2])

/-- info: 1 -/
#guard_msgs in #eval Matrix.rankAt (toRat vandermonde3) (pointOf #v[5, 5, 5])

/-- info: 2 -/
#guard_msgs in #eval Matrix.rankAt (toRat bordered2) (pointOf #v[2, 3, 5, 7, 31])

/-- info: 3 -/
#guard_msgs in #eval Matrix.rankAt (toRat bordered2) (pointOf #v[2, 3, 5, 7, 30])

/-! # `InLocus` -/

/-! Two equal Vandermonde coordinates put the point in the locus at `r = 2`;
distinct coordinates do not. -/
#guard decide (Matrix.InLocus 2 (toRat vandermonde2) (pointOf #v[3, 3]))
#guard !decide (Matrix.InLocus 2 (toRat vandermonde2) (pointOf #v[2, 5]))

/-! All coordinates equal drops the rank of `V_3` to `1`, so the point lies in
the locus at `r = 2`; `V_2` at `r = 1` has the minor `1`, so no point lies in
its locus. -/
#guard decide (Matrix.InLocus 2 (toRat vandermonde3) (pointOf #v[5, 5, 5]))
#guard !decide (Matrix.InLocus 1 (toRat vandermonde2) (pointOf #v[4, 4]))

/-! The zero matrix puts every point in the locus at `r = 1`. -/
#guard decide (Matrix.InLocus 1 (toRat zero22) (pointOf #v[]))

/-! The bordered identity: `1` is a `k × k` minor, so no point lies in the
locus at `r = k`, while at `r = k + 1` the locus is the hypersurface
`t = v · u`. -/
#guard !decide (Matrix.InLocus 1 (toRat bordered1) (pointOf #v[2, 3, 6]))
#guard decide (Matrix.InLocus 2 (toRat bordered1) (pointOf #v[2, 3, 6]))
#guard !decide (Matrix.InLocus 2 (toRat bordered1) (pointOf #v[2, 3, 7]))
#guard !decide (Matrix.InLocus 2 (toRat bordered2) (pointOf #v[2, 3, 5, 7, 31]))
#guard decide (Matrix.InLocus 3 (toRat bordered2) (pointOf #v[2, 3, 5, 7, 31]))
#guard !decide (Matrix.InLocus 3 (toRat bordered2) (pointOf #v[2, 3, 5, 7, 30]))

/-! # The rank-versus-minors theorem -/

/-- `rank_lt_iff_minors_eq_zero`, executably: the rank drops below `r` exactly
where the locus decision says it does. -/
private def rankLocusAgrees {k n m : Nat} (r : Nat) (A : Matrix (P k) n m)
    (v : Vector Int k) : Bool :=
  decide (Matrix.rankAt (toRat A) (pointOf v) < r) =
    decide (Matrix.InLocus r (toRat A) (pointOf v))

#guard rankLocusAgrees 2 vandermonde2 #v[3, 3]
#guard rankLocusAgrees 2 vandermonde2 #v[2, 5]
#guard rankLocusAgrees 1 vandermonde2 #v[4, 4]
#guard rankLocusAgrees 3 vandermonde3 #v[1, 1, 2]
#guard rankLocusAgrees 3 vandermonde3 #v[1, 2, 3]
#guard rankLocusAgrees 2 vandermonde3 #v[5, 5, 5]
#guard rankLocusAgrees 2 bordered2 #v[2, 3, 5, 7, 31]
#guard rankLocusAgrees 3 bordered2 #v[2, 3, 5, 7, 31]
#guard rankLocusAgrees 3 bordered2 #v[2, 3, 5, 7, 30]
#guard rankLocusAgrees 1 zero22 #v[]
#guard rankLocusAgrees 2 distinct24 #v[]

/-! The boundaries: at `r = 0` the minor `1` never vanishes and the rank is
never below `0`; above the shape the vacuous locus holds and the rank is below
`r`, on the empty shapes and on both rectangular orientations. -/
#guard rankLocusAgrees 0 empty00 #v[]
#guard rankLocusAgrees 0 empty02 #v[]
#guard rankLocusAgrees 0 empty20 #v[]
#guard rankLocusAgrees 0 small23 #v[]
#guard rankLocusAgrees 3 square22 #v[]
#guard rankLocusAgrees 3 small23 #v[]
#guard rankLocusAgrees 3 small32 #v[]
#guard !decide (Matrix.InLocus 0 (toRat empty02) (pointOf #v[]))
#guard decide (Matrix.InLocus 3 (toRat small32) (pointOf #v[]))
#guard Matrix.rankAt (toRat empty20) (pointOf #v[]) = 0
#guard Matrix.rankAt (toRat small32) (pointOf #v[]) = 2

/-- A `3 × 3` matrix over `Rat` with integer entries. -/
def ratSingular : Matrix Rat 3 3 :=
  Matrix.specialize (toRat singular33) (pointOf #v[])

#guard ratSingular.rows = #v[#v[1, 2, 3], #v[4, 5, 6], #v[7, 8, 9]]

/-! The nine `2 × 2` minors and the vanishing determinant, by hand. -/
#guard Matrix.minors 2 ratSingular = [-3, -6, -3, -6, -12, -6, -3, -6, -3]
#guard Matrix.minors 3 ratSingular = [0]

/-- The executable rank agrees with `rank_eq_iff_minors`: the `2 × 2` minor
`-3` is nonzero and the determinant vanishes, so the rank is `2`. -/
example : Matrix.rowReduce_rank ratSingular = 2 :=
  (rank_eq_iff_minors ratSingular 2).mpr
    ⟨⟨-3, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩

example : Matrix.rowReduce_rank ratSingular = 2 := by decide +kernel

/-! # Invariance under a unimodular left factor -/

#guard Matrix.det unimodular = 1

#guard Matrix.rankAt (toRat invarImage) (pointOf #v[2, 3]) =
  Matrix.rankAt (toRat invarBase) (pointOf #v[2, 3])
#guard Matrix.rankAt (toRat invarImage) (pointOf #v[1, 1]) =
  Matrix.rankAt (toRat invarBase) (pointOf #v[1, 1])
#guard decide (Matrix.InLocus 2 (toRat invarImage) (pointOf #v[2, 3])) =
  decide (Matrix.InLocus 2 (toRat invarBase) (pointOf #v[2, 3]))
#guard decide (Matrix.InLocus 2 (toRat invarImage) (pointOf #v[1, 1])) =
  decide (Matrix.InLocus 2 (toRat invarBase) (pointOf #v[1, 1]))

end Hex.DeterminantalIdealConformance
