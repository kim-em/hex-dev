/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public section

/-!
# Finite Hilbert class polynomial table

Classical j-polynomials (`polclass(-d, 0)`) from PARI/GP 2.17.3.
Source release: https://pari.math.u-bordeaux.fr/pub/pari/unix/pari-2.17.3.tar.gz
SHA256: 8d9c4fcd584c468d27e0f23c36836587284452094c4b1c404c20c4b810462dcb.
The table contains every discriminant with class number at most two and
absolute value at most 500, except the nine original invariants. Coefficients
are in ascending order. `scripts/oracle/ecpp_class_polynomials.py` independently
checks reduced primitive forms and analytic j-values at two precisions.
These are arithmetic proposals; certificate acceptance does not trust CM data.
-/

namespace Hex.ECPP.CM

/-- A negative discriminant's absolute value and its monic Hilbert polynomial. -/
structure ClassPolynomial where
  d : Nat
  coefficients : List Int
deriving Repr

/-- Thirty-three fixed linear/quadratic polynomials; no subject-specific data. -/
def classPolynomials : List ClassPolynomial :=
  [⟨12, [-54000, 1]⟩,
   ⟨15, [-121287375, 191025, 1]⟩,
   ⟨16, [-287496, 1]⟩,
   ⟨20, [-681472000, -1264000, 1]⟩,
   ⟨24, [14670139392, -4834944, 1]⟩,
   ⟨27, [12288000, 1]⟩,
   ⟨28, [-16581375, 1]⟩,
   ⟨32, [12167000000, -52250000, 1]⟩,
   ⟨35, [-134217728000, 117964800, 1]⟩,
   ⟨36, [-1790957481984, -153542016, 1]⟩,
   ⟨40, [9103145472000, -425692800, 1]⟩,
   ⟨48, [6549518250000, -2835810000, 1]⟩,
   ⟨51, [6262062317568, 5541101568, 1]⟩,
   ⟨52, [-567663552000000, -6896880000, 1]⟩,
   ⟨60, [153173312762625, -37018076625, 1]⟩,
   ⟨64, [-7367066619912, -82226316240, 1]⟩,
   ⟨72, [232381513792000000, -377674768000, 1]⟩,
   ⟨75, [5209253090426880, 654403829760, 1]⟩,
   ⟨88, [15798135578688000000, -6294842640000, 1]⟩,
   ⟨91, [-3845689020776448, 10359073013760, 1]⟩,
   ⟨99, [-56171326053810176, 37616060956672, 1]⟩,
   ⟨100, [-292143758886942437376, -44031499226496, 1]⟩,
   ⟨112, [1337635747140890625, -274917323970000, 1]⟩,
   ⟨115, [130231327260672000, 427864611225600, 1]⟩,
   ⟨123, [148809594175488000000, 1354146840576000, 1]⟩,
   ⟨147, [11356800389480448000000, 34848505552896000, 1]⟩,
   ⟨148, [-7898242515936467904000000, -39660183801072000, 1]⟩,
   ⟨187, [-3845689020776448000000, 4545336381788160000, 1]⟩,
   ⟨232, [14871070713157137145512000000000, -604729957849891344000, 1]⟩,
   ⟨235, [11946621170462723407872000, 823177419449425920000, 1]⟩,
   ⟨267, [531429662672621376897024000000, 19683091854079488000000, 1]⟩,
   ⟨403, [-108844203402491055833088000000, 2452811389229331391979520000, 1]⟩,
   ⟨427, [155041756222618916546936832000000, 15611455512523783919812608000, 1]⟩]

end Hex.ECPP.CM
