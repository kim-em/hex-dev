/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexConway

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
  for (p, n) in supportedPairs do
    if h0 : 0 < p then
      if h1 : p < 2 ^ 31 then
        letI : ZMod64.Bounds p := ⟨h0, h1⟩
        emitAt p n
      else
        throw <| IO.userError s!"unsupported characteristic bound: {p}"
    else
      throw <| IO.userError "zero characteristic in verified scope"

end Hex.ConwayEmit

def main : IO Unit :=
  Hex.ConwayEmit.emitAll
