import Hex.Conformance.Emit
import HexHensel

/-!
JSONL emit driver for the `hex-hensel` oracle.

`lake exe hexhensel_emit_fixtures` writes one JSONL record per
fixture component (the `(p, k)` pair, the target polynomial, and each
input factor) followed by one `result` record carrying Lean's lifted
factor array.  The companion oracle driver
`scripts/oracle/hensel_pari.py` reads the same stream and re-runs each
lift through PARI's `factorpadic`.

`python-flint` does not expose mod-`p^k` polynomial factorisation, so
the oracle for the multifactor Hensel lift is PARI (via cypari2)
rather than FLINT.
-/

namespace Hex.HenselEmit

open Hex.Conformance.Emit
open Hex
open Hex.DensePoly

private def lib : String := "HexHensel"

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩
private instance boundsSeven : ZMod64.Bounds 7 := ⟨by decide, by decide⟩

/-- A multifactor Hensel-lift fixture.

`f` is the target polynomial in `Z[x]` (coefficients ascending).  Each
entry of `factors` is a small representative of a factor of `f` modulo
`p`; `multifactorLiftQuadratic` lifts these to factors of `f` modulo
`p^k`.  `lift` carries the `[ZMod64.Bounds p]` instance so the case
table can mix primes. -/
private structure Case where
  id      : String
  p       : Nat
  k       : Nat
  f       : List Int
  factors : List (List Int)
  lift    : ZPoly → Array ZPoly → Array ZPoly

/-- Render a list of coefficient lists as a JSON array of arrays. -/
private def factorsValue (factors : List (List Int)) : String := Id.run do
  let mut out := "["
  let mut first := true
  for fc in factors do
    if first then
      first := false
    else
      out := out.push ','
    out := out ++ polyValue fc
  out.push ']'

/-- Three monic linear factors whose lifts are non-trivial: the input
factors `(x+1), (x+2), (x+3)` mod 5 lift to `(x+6), (x+12), (x+8)` mod
`5^4`, since `f = (x+6)(x+12)(x+8)` over `Z`. -/
private def typicalCase : Case :=
  { id := "multifactor/typical"
    p := 5, k := 4
    -- (x+6)(x+12)(x+8) = x^3 + 26 x^2 + 216 x + 576
    f := [576, 216, 26, 1]
    factors := [[1, 1], [2, 1], [3, 1]]
    lift := fun f fs => ZPoly.multifactorLiftQuadratic 5 4 f fs }

/-- Mixed-degree factor set with one irreducible quadratic.  The input
factors `(x+1), (x²+1), (x+2)` mod 7 lift to `(x+8), (x²+1), (x+2)` mod
`7^2`, since `f = (x+8)(x²+1)(x+2)` over `Z`. -/
private def mixedCase : Case :=
  { id := "multifactor/mixed"
    p := 7, k := 2
    -- (x+8)(x^2+1)(x+2) = x^4 + 10 x^3 + 17 x^2 + 10 x + 16
    f := [16, 10, 17, 10, 1]
    factors := [[1, 1], [1, 0, 1], [2, 1]]
    lift := fun f fs => ZPoly.multifactorLiftQuadratic 7 2 f fs }

/-- Four monic linear factors at `k = 8` to exercise the quadratic
doubling loop deeper.  All four input factors are already exact
`Z`-factors of `f`, so the lift collapses to the input — the test value
is the doubling-step machinery returning consistent factors at high
precision.  `f = (x+1)(x+2)(x+3)(x+4)` over `Z`. -/
private def adversarialCase : Case :=
  { id := "multifactor/adversarial"
    p := 5, k := 8
    -- (x+1)(x+2)(x+3)(x+4) = x^4 + 10 x^3 + 35 x^2 + 50 x + 24
    f := [24, 50, 35, 10, 1]
    factors := [[1, 1], [2, 1], [3, 1], [4, 1]]
    lift := fun f fs => ZPoly.multifactorLiftQuadratic 5 8 f fs }

private def cases : List Case :=
  [typicalCase, mixedCase, adversarialCase]

private def emitCase (c : Case) : IO Unit := do
  emitPrimeFixture lib (c.id ++ "/pk") (Int.ofNat c.p) (Int.ofNat c.k)
  emitPolyFixture lib (c.id ++ "/f") c.f
  let mut i := 0
  for fc in c.factors do
    emitPolyFixture lib (c.id ++ "/factor/" ++ toString i) fc
    i := i + 1
  let f : ZPoly := ofCoeffs c.f.toArray
  let factorArr : Array ZPoly :=
    (c.factors.map (fun fc => (ofCoeffs fc.toArray : ZPoly))).toArray
  let lifted := c.lift f factorArr
  let canonical := lifted.map (fun g => ZPoly.reduceModPow g c.p c.k)
  let factorLists := canonical.toList.map (fun g => g.toArray.toList)
  emitResult lib c.id "multifactor_lift" (factorsValue factorLists)

end Hex.HenselEmit

def main : IO Unit := do
  for c in Hex.HenselEmit.cases do Hex.HenselEmit.emitCase c
