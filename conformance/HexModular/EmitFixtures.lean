/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexModular

/-!
Deterministic JSONL fixtures for the `HexModular` external oracle profile.

The stream contains the three fixture kinds required by the SPEC: symmetric
representatives, incremental scalar CRT, and bounded rational reconstruction.
Inputs alone determine the oracle answer; result records carry only Lean's
computed value. Failure is encoded as JSON `null`.
-/

namespace Hex.ModularEmit

open Hex.Conformance.Emit
open Hex.Modular

private def lib : String := "HexModular"

private structure SymCase where
  id : String
  a : Int
  m : Nat

private def symCases : List SymCase := [
  ⟨"symmod/typical", 987654321, 1009⟩,
  ⟨"symmod/zero-modulus", -37, 0⟩,
  ⟨"symmod/positive-tie", 3, 6⟩,
  ⟨"symmod/negative-tie", -3, 6⟩,
  ⟨"symmod/negative", -100, 17⟩,
  ⟨"symmod/modulus-one", 12345, 1⟩]

private structure CrtCase where
  id : String
  steps : List (Int × Nat)

private def crtCases : List CrtCase := [
  ⟨"crt/typical", [(2, 5), (3, 7), (8, 11)]⟩,
  ⟨"crt/single", [(17, 11)]⟩,
  ⟨"crt/outer-reduction", [(1, 3), (0, 2)]⟩,
  ⟨"crt/zero-modulus", [(4, 0)]⟩,
  ⟨"crt/modulus-one", [(4, 1)]⟩,
  ⟨"crt/non-coprime", [(1, 6), (2, 9)]⟩]

private def runCrt : Crt → List (Int × Nat) → Option Crt
  | state, [] => some state
  | state, (residue, modulus) :: rest => do
      let next ← state.push residue modulus
      runCrt next rest

private structure RatCase where
  id : String
  a : Int
  m : Nat
  p : Int
  q : Int

private def ratCases : List RatCase := [
  ⟨"ratrecon/zero-modulus-one", 0, 1, 0, 1⟩,
  ⟨"ratrecon/typical", 68, 101, 8, 8⟩,
  ⟨"ratrecon/negative", 33, 101, 8, 8⟩,
  ⟨"ratrecon/integer", 7, 101, 8, 8⟩,
  ⟨"ratrecon/failure", 50, 101, 1, 1⟩,
  ⟨"ratrecon/zero-modulus", 17, 0, 8, 8⟩,
  ⟨"ratrecon/nonunique-bounds", 3, 8, 4, 4⟩,
  ⟨"ratrecon/denominator-one", -9, 1009, 10, 1⟩,
  ⟨"ratrecon/numerator-boundary", 11, 97, 11, 1⟩,
  ⟨"ratrecon/numerator-outside", 12, 97, 11, 1⟩,
  ⟨"ratrecon/denominator-boundary", 621, 1009, 1, 13⟩,
  ⟨"ratrecon/denominator-outside", 621, 1009, 1, 12⟩]

private def emitSym (c : SymCase) : IO Unit := do
  emitSymModFixture lib c.id c.a c.m
  emitResult lib c.id "symmod" (toString (symMod c.a c.m))

private def emitCrt (c : CrtCase) : IO Unit := do
  emitCrtFixture lib c.id c.steps
  let value :=
    match runCrt Crt.init c.steps with
    | none => "null"
    | some result => intListValue [result.value, Int.ofNat result.modulus]
  emitResult lib c.id "crt" value

private def emitRat (c : RatCase) : IO Unit := do
  emitRatReconFixture lib c.id c.a c.m c.p c.q
  let value :=
    match ratRecon? c.a c.m c.p c.q with
    | none => "null"
    | some result => intListValue [result.num, Int.ofNat result.den]
  emitResult lib c.id "ratrecon" value

end Hex.ModularEmit

def main : IO Unit := do
  for c in Hex.ModularEmit.symCases do Hex.ModularEmit.emitSym c
  for c in Hex.ModularEmit.crtCases do Hex.ModularEmit.emitCrt c
  for c in Hex.ModularEmit.ratCases do Hex.ModularEmit.emitRat c
