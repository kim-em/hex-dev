import Hex.Conformance.Emit
import HexConway.Basic

/-!
JSONL emit driver for the `hex-conway` oracle.

`lake exe hexconway_emit_fixtures` writes one `conway` fixture record
and one `result` record per committed Lübeck cache entry.  The companion
oracle driver compares the emitted coefficients against the committed
cache and, when requested, the optional Python `conway-polynomials`
package table adapter.
-/

namespace Hex.ConwayEmit

open Hex.Conformance.Emit
open Hex
open Hex.Conway

private def lib : String := "HexConway"

private def coeffNats {p : Nat} [ZMod64.Bounds p] (f : FpPoly p) : List Int :=
  f.toArray.toList.map (fun c => Int.ofNat c.toNat)

private def emitAt (p n : Nat) [ZMod64.Bounds p] : IO Unit := do
  match luebeckConwayPolynomial? p n with
  | none => pure ()
  | some poly =>
      let caseId := s!"p{p}_n{n}"
      emitConwayFixture lib caseId (Int.ofNat p) (Int.ofNat n)
      emitResult lib caseId "coeffs" (polyValue (coeffNats poly))

def emitAll : IO Unit := do
  emitAt 2 1
  emitAt 2 2
  emitAt 2 3
  emitAt 2 4
  emitAt 2 5
  emitAt 2 6
  emitAt 3 1
  emitAt 3 2
  emitAt 3 3
  emitAt 3 4
  emitAt 3 5
  emitAt 3 6
  emitAt 5 1
  emitAt 5 2
  emitAt 5 3
  emitAt 5 4
  emitAt 5 5
  emitAt 5 6
  emitAt 7 1
  emitAt 7 2
  emitAt 7 3
  emitAt 7 4
  emitAt 7 5
  emitAt 7 6
  emitAt 11 1
  emitAt 11 2
  emitAt 11 3
  emitAt 11 4
  emitAt 11 5
  emitAt 11 6
  emitAt 13 1
  emitAt 13 2
  emitAt 13 3
  emitAt 13 4
  emitAt 13 5
  emitAt 13 6

end Hex.ConwayEmit

def main : IO Unit :=
  Hex.ConwayEmit.emitAll
