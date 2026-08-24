/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexSparsePolyFixtures

/-!
Core executable conformance checks for `hex-sparse-poly`.

Oracle: SymPy sparse ring elements (`sympy.polys.rings`), via
`scripts/oracle/sparsepoly_sympy.py` on the stream from
`lake exe hexsparsepoly_emit_fixtures`.
Mode: `if_available` locally, required in release CI.

Covered operations:
- construction (`ofTerms` / `#sp[…]`, `addTerm`, `monomial`, `C`, `X`),
  the observation API (`coeff`, `support`, `numTerms`, `degree?`,
  `leadingCoeff`, `isZero`, `toTerms`, `foldTerms`), and decidable
  equality;
- `add`, `sub`, `neg`, `scale`, `mulMonomial`, `mul`, `pow`;
- `eval`, `derivative`, `substPow`, `substScale`, `compose`;
- `toDense`, `ofDense`, and the array workers `coeffsOfTerms` /
  `termsOfCoeffs`;
- `divModMonic`, `divMod`, `gcd`, `divExactMonic?`, `divMonomial?`,
  and `Monic`.

Covered properties:
- every constructed value satisfies `SparsePolyCanonical` (checked with
  the decidable `isCanonical` route), and the observation API agrees
  with the stored terms;
- addition commutes and associates, multiplication distributes, and the
  degree of a product is the sum of the degrees on committed inputs;
- evaluation is additive and multiplicative on committed inputs;
- `substPow` agrees with `compose` at `monomial k 1`;
- both round trips (`ofDense_toDense`, `toDense_ofDense`), and the
  necessity of each round-trip hypothesis at the array level;
- `mulMonomial` inverts `divMonomial?`;
- differential agreement with `DensePoly` for `add`, `mul`, `gcd`, and
  `divMod` through `toDense` (a test of the conversions, not of the
  Euclidean algorithm).

Covered edge cases:
- `ofTerms` on empty, unsorted, duplicate-exponent, zero-coefficient,
  and cancelling-duplicate input;
- `add` cancelling at the lowest, an interior, the highest exponent,
  and everywhere at once;
- `mul` collision cancellation over `Int`, and a zero coefficient
  product with both factors nonzero over composite `ZMod64 6`;
- `compose` contributions colliding at one exponent and cancelling;
- `scale` by zero and by a zero divisor deleting an interior term only;
- `derivative` over `ZMod64 5` of `x^5` (zero), `x^5 + x^10` (zero),
  and `x^5 + x` (one term);
- `substPow 0` with and without a cancelling coefficient sum;
- degree-`10^6` inputs on every operation that stays sparse.

The `module` + `public import` probe for the `DecidableEq` kernel
hazard lives in `HexSparsePoly.KernelTests` (built via the
`HexSparsePolyTests` target), which `decide +kernel`s the whole
kernel-exposure closure from a downstream module.
-/

namespace Hex.SparsePolyConformance

open Hex
open Hex.SparsePoly
open Hex.SparsePolyFixtures

/-- The stored representation is canonical and every observation agrees
with the stored terms. -/
private def representationContract (s : PZ) : Bool :=
  isCanonical s.terms &&
  decide (s.numTerms = s.toTerms.length) &&
  decide (s.support = (s.toTerms.map Prod.fst).toArray) &&
  decide (s.degree? = (s.toTerms.map Prod.fst).max?) &&
  decide (s.isZero = s.toTerms.isEmpty) &&
  decide (s.foldTerms (fun acc e c => acc + Int.ofNat e + c) 0 =
    s.toTerms.foldl (fun acc t => acc + Int.ofNat t.1 + t.2) 0) &&
  decide (s.leadingCoeff = (s.toTerms.map Prod.snd).getLast?.getD 0) &&
  s.toTerms.all (fun t => decide (t.2 ≠ 0) && decide (s.coeff t.1 = t.2))

/-- Coefficient lookup off the support reads `0`. -/
private def absentContract (s : PZ) (absent : Nat) : Bool :=
  decide (s.coeff absent = 0)

#guard representationContract pDisjoint
#guard representationContract qDisjoint
#guard representationContract pOverlap
#guard representationContract binom6
#guard representationContract 0
#guard absentContract pDisjoint 1
#guard absentContract binom6 999999
#guard absentContract 0 0

-- Construction: `ofTerms` canonicalises arbitrary input.
#guard (#sp[] : PZ) = 0
#guard (#sp[(3, 1), (0, 5)] : PZ).toTerms = [(0, 5), (3, 1)]
#guard (#sp[(1, 2), (1, 3)] : PZ) = #sp[(1, 5)]
#guard (#sp[(0, 0), (2, 4)] : PZ).toTerms = [(2, 4)]
#guard (#sp[(1, 2), (1, -2)] : PZ) = 0
#guard (#sp[(0, 0)] : PZ) = 0

-- `addTerm`: insert, combine, delete.
#guard ((0 : PZ).addTerm 5 3).toTerms = [(5, 3)]
#guard (pDisjoint.addTerm 5 2).toTerms = [(0, 3), (9, 4)]
#guard (pDisjoint.addTerm 5 1).coeff 5 = -1
#guard (pDisjoint.addTerm 7 0) = pDisjoint

-- `monomial`, `C`, `X`, `One`.
#guard (monomial 4 9 : PZ).toTerms = [(4, 9)]
#guard (monomial 4 0 : PZ) = 0
#guard (C 7 : PZ) = monomial 0 7
#guard (X : PZ) = monomial 1 1
#guard (1 : PZ) = C 1

-- Decidable equality distinguishes canonical representations.
#guard pDisjoint = pDisjoint
#guard pDisjoint ≠ qDisjoint
#guard (#sp[(1, 5)] : PZ) ≠ 0

-- `add`: cancellation at the lowest, an interior, the highest
-- exponent, and everywhere at once.
#guard (pOverlap + qOverlap).toTerms = [(5, 2), (7, 2)]
#guard (#sp[(0, 1), (3, 4)] + #sp[(3, -4), (9, 2)] : PZ).toTerms =
  [(0, 1), (9, 2)]
#guard (#sp[(0, 1), (5, 2)] + #sp[(5, -2)] : PZ).toTerms = [(0, 1)]
#guard (pDisjoint + (-pDisjoint)) = 0
#guard (binom6 + binom6).toTerms = [(0, -2), (1000000, 2)]
#guard (pDisjoint + 0) = pDisjoint

-- `add` commutes and associates on committed inputs.
#guard pDisjoint + qDisjoint = qDisjoint + pDisjoint
#guard (pDisjoint + qDisjoint) + pOverlap =
  pDisjoint + (qDisjoint + pOverlap)

-- `sub` and `neg`.
#guard (pDisjoint - pDisjoint) = 0
#guard (0 - pDisjoint) = -pDisjoint
#guard (-binom6).toTerms = [(0, 1), (1000000, -1)]
#guard (pOverlap - qOverlap).toTerms = [(0, 2), (3, 8), (5, 2), (7, -2)]

-- `scale` by zero, by a unit, and by a zero divisor over `ZMod64 6`
-- (deleting an interior term while keeping its neighbours).
#guard scale 0 pDisjoint = 0
#guard (scale 2 binom3).toTerms = [(0, -2), (1000, 2)]
#guard (scale (ZMod64.ofNat 6 2)
    (#sp[(0, ZMod64.ofNat 6 1), (2, ZMod64.ofNat 6 3),
      (5, ZMod64.ofNat 6 5)] : P6)).support = #[0, 5]

-- `mulMonomial`: the cheap shift.
#guard (mulMonomial 3 2 (#sp[(0, 1), (1, 1)] : PZ)).toTerms =
  [(3, 2), (4, 2)]
#guard mulMonomial 0 1 pDisjoint = pDisjoint
#guard (mulMonomial 2 0 pDisjoint) = 0
#guard (mulMonomial 1000000 1 binom6).toTerms =
  [(1000000, -1), (2000000, 1)]

-- `mul`: collision cancellation over `Int`, checked on the term array
-- so a stored `(1, 0)` fails; a zero coefficient product with both
-- factors nonzero over composite `ZMod64 6`.
#guard (#sp[(0, 1), (1, 1)] * #sp[(0, -1), (1, 1)] : PZ).toTerms =
  [(0, -1), (2, 1)]
#guard (#sp[(1, ZMod64.ofNat 6 2)] * #sp[(1, ZMod64.ofNat 6 3),
    (2, ZMod64.ofNat 6 1)] : P6).support = #[3]
#guard (binom6 * binom6).toTerms =
  [(0, 1), (1000000, -2), (2000000, 1)]
#guard pDisjoint * 0 = 0
#guard pDisjoint * 1 = pDisjoint

-- `mul` distributes and its degree adds, on committed inputs.
#guard pDisjoint * (qDisjoint + pOverlap) =
  pDisjoint * qDisjoint + pDisjoint * pOverlap
#guard (pDisjoint * qDisjoint).degree? = some (9 + 11)
#guard pDisjoint * qDisjoint = qDisjoint * pDisjoint

-- `pow` is iterated multiplication.
#guard (#sp[(0, 1), (1, 1)] : PZ) ^ 3 =
  #sp[(0, 1), (1, 3), (2, 3), (3, 1)]
#guard pDisjoint ^ 0 = 1
#guard (binom6 ^ 2) = binom6 * binom6

-- `eval` is additive and multiplicative on committed inputs, and reads
-- gap Horner off a degree-`10^6` input over `ZMod64 7`.
#guard pDisjoint.eval 3 = 3 - 2 * 3 ^ 5 + 4 * 3 ^ 9
#guard (0 : PZ).eval 17 = 0
#guard (pDisjoint + qDisjoint).eval 2 =
  pDisjoint.eval 2 + qDisjoint.eval 2
#guard (pDisjoint * qDisjoint).eval 2 =
  pDisjoint.eval 2 * qDisjoint.eval 2
#guard pMod7Big.eval (ZMod64.ofNat 7 2) =
  ZMod64.ofNat 7 2 + ZMod64.ofNat 7 4 *
    (ZMod64.ofNat 7 2) ^ (1000003 % 6)
#guard binom3.eval 1 = 0

-- `derivative`: the positive-characteristic zero filter, on the term
-- array. Over `ZMod64 5` the derivative of `x^5` and of `x^5 + x^10`
-- is the zero polynomial, and `x^5 + x` keeps one term.
#guard (#sp[(5, ZMod64.ofNat 5 1)] : P5).derivative = 0
#guard (#sp[(5, ZMod64.ofNat 5 1), (10, ZMod64.ofNat 5 1)] : P5).derivative
  = 0
#guard ((#sp[(1, ZMod64.ofNat 5 1), (5, ZMod64.ofNat 5 1)] : P5).derivative).toTerms
  = [(0, ZMod64.ofNat 5 1)]
#guard (#sp[(1, 3), (4, 2)] : PZ).derivative = #sp[(0, 3), (3, 8)]
#guard (C 7 : PZ).derivative = 0
#guard binom6.derivative.toTerms = [(999999, 1000000)]

-- `substPow`: `k = 0` is a canonicalisation, not an error; `k ≥ 1`
-- rescales exponents and touches nothing else.
#guard (#sp[(0, 3), (2, -3)] : PZ).substPow 0 = 0
#guard (#sp[(0, 3), (2, 4)] : PZ).substPow 0 = C 7
#guard (binom6.substPow 2).toTerms = [(0, -1), (2000000, 1)]
#guard (phi3.substPow 9).toTerms = [(0, 1), (9, 1), (18, 1)]
#guard pDisjoint.substPow 1 = pDisjoint

-- `substPow` agrees with `compose` at `monomial k 1`.
#guard phi3.substPow 9 = phi3.compose (monomial 9 1)
#guard pDisjoint.substPow 3 = pDisjoint.compose (monomial 3 1)
#guard pOverlap.substPow 0 = pOverlap.compose (monomial 0 1)

-- `substScale` computes `c · a^e` from the gaps.
#guard ((#sp[(1, 1), (3, 1)] : PZ).substScale 2).toTerms =
  [(1, 2), (3, 8)]
#guard (pDisjoint.substScale 0).toTerms = [(0, 3)]
#guard ((#sp[(1, ZMod64.ofNat 6 2), (3, ZMod64.ofNat 6 5)] : P6).substScale
    (ZMod64.ofNat 6 3)).support = #[3]

-- `compose`: contributions from different terms colliding at one
-- exponent and cancelling.
#guard ((#sp[(0, 2), (1, -1), (2, 1)] : PZ).compose
    (#sp[(0, 1), (1, 1)])).toTerms = [(0, 2), (1, 1), (2, 1)]
#guard ((#sp[(1, 1), (2, -1)] : PZ).compose (#sp[(0, 1), (1, 1)])).toTerms
  = [(1, -1), (2, -1)]
#guard ((X : PZ).compose pDisjoint) = pDisjoint
#guard ((C 5 : PZ).compose qDisjoint) = C 5

-- Conversions: round trips at the bundled level.
#guard ofDense pDisjoint.toDense = pDisjoint
#guard ofDense (0 : PZ).toDense = 0
#guard (ofDense (#p[5, 0, 0, 1] : DensePoly Int)).toDense = #p[5, 0, 0, 1]
#guard (#sp[(0, 5), (3, 1)] : PZ).toDense = #p[5, 0, 0, 1]
#guard (ofDense (#p[0, 2, 0, 0, 7] : DensePoly Int)).toTerms =
  [(1, 2), (4, 7)]

-- The necessity of each round-trip hypothesis, at the array level: a
-- stored zero vanishes, a duplicate is overwritten, unsorted input
-- comes back sorted, and a trailing zero is not reconstructed.
#guard coeffsOfTerms (#[((0 : Nat), (0 : Int))]) = #[0]
#guard termsOfCoeffs (#[(0 : Int)]) = #[]
#guard coeffsOfTerms (#[((1 : Nat), (2 : Int)), (1, 3)]) = #[0, 3]
#guard termsOfCoeffs (coeffsOfTerms #[((1 : Nat), (2 : Int)), (1, 3)]) =
  #[(1, 3)]
#guard termsOfCoeffs (coeffsOfTerms #[((1 : Nat), (2 : Int)), (0, 3)]) =
  #[(0, 3), (1, 2)]
#guard termsOfCoeffs (#[(1 : Int), 0]) = #[(0, 1)]
#guard coeffsOfTerms (termsOfCoeffs (#[(1 : Int), 0])) = #[1]

-- Differential agreement with `DensePoly` for the arithmetic the two
-- representations implement independently.
#guard (pOverlap + qOverlap).toDense = pOverlap.toDense + qOverlap.toDense
#guard (pOverlap * qOverlap).toDense = pOverlap.toDense * qOverlap.toDense
#guard (pDisjoint - qDisjoint).toDense =
  pDisjoint.toDense - qDisjoint.toDense

-- `Monic` and the Euclidean layer. `x^25 − 1` modulo the monic
-- `x^5 − 1` starts the two-term remainder sequence the SPEC describes.
private def x25m1 : PQ := #sp[(0, -1), (25, 1)]
private def x5m1 : PQ := #sp[(0, -1), (5, 1)]

#guard x5m1.Monic
#guard ¬ (#sp[(3, (2 : Rat))] : PQ).Monic
#guard (divModMonic x25m1 x5m1 (by decide)) =
  (#sp[(0, 1), (5, 1), (10, 1), (15, 1), (20, 1)], 0)
#guard (divModMonic (#sp[(0, (3 : Rat))] : PQ) x5m1 (by decide)) =
  (0, #sp[(0, (3 : Rat))])
#guard (divExactMonic? x25m1 x5m1 (by decide)).isSome
#guard divExactMonic? (#sp[(0, (3 : Rat)), (1, 1)] : PQ) x5m1 (by decide)
  = none

-- `divMod` and `gcd` compared against the same computation done
-- entirely in `DensePoly`: a differential test of the conversions.
private def gA : PQ := #sp[(0, -1), (6, 1)]
private def gB : PQ := #sp[(0, -1), (4, 1)]

#guard (gcd gA gB).toDense = DensePoly.gcd gA.toDense gB.toDense
#guard ((divMod gA gB).1.toDense, (divMod gA gB).2.toDense) =
  DensePoly.divMod gA.toDense gB.toDense
#guard (divMod x25m1 x5m1).1 * x5m1 + (divMod x25m1 x5m1).2 = x25m1
#guard (gA % gcd gA gB) = 0
#guard (gB % gcd gA gB) = 0

-- `divMonomial?`: exact when every exponent clears the monomial,
-- `none` otherwise, and `mulMonomial` inverts it.
#guard divMonomial? (#sp[(3, 2), (7, 5)] : PZ) 3 = some #sp[(0, 2), (4, 5)]
#guard divMonomial? (#sp[(3, 2), (7, 5)] : PZ) 4 = none
#guard divMonomial? (0 : PZ) 5 = some 0
#guard (divMonomial? (mulMonomial 9 1 pDisjoint) 9) = some pDisjoint

end Hex.SparsePolyConformance
