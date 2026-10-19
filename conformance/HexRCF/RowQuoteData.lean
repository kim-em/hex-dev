/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RowQuote
public section
namespace Hex.RCF.RowQuoteTests
open Hex Hex.SignDet
abbrev Root := Descriptor Int Unit Int.sign ()
structure Input (stored : Int) where
  first : Root
  second : Root
  rootEq : first = second
  q0 : DensePoly Int
  q1 : DensePoly Int
  queryEq : [q0] = [q1]
  evidence : Hex.SignDet.Replay Int Unit
  checked : first.checkSigns [q0] #v[stored] evidence = true
@[expose] def source (input : Input stored) : SelectedSigns input.first [input.q0] :=
  ⟨#v[stored],input.evidence,input.checked⟩
@[expose] def castRow (input : Input stored) : SelectedSigns input.first [input.q1] :=
  input.queryEq ▸ source input
@[expose] def gate (decision : Bool) : Except String Nat :=
  if decision then .ok 17 else .ok 23
end Hex.RCF.RowQuoteTests
