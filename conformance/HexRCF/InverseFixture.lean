/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.TowerCatalog
import HexRealClosure.InverseEquation
import HexSignDet.Codec
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet

namespace Hex.RCF.SelectedInverseFixture

def registry : BaseContext.Registry := fun _ => none
abbrev base := Tower.Context.base (BaseContext.rational registry)

def packet : Option Codec.Json :=
  letI : Hashable base.Value := ⟨fun a => hash (base.codec.encode a)⟩
  letI : Hashable Tower.Signature := ⟨fun _ => 0⟩
  do
    let root ← Descriptor.validate base.sign base.signature
      { context := base.signature, head := DensePoly.ofList [-((2 : Nat) : base.Value),0,1],
        lower := .finite 1, upper := .finite ((2 : Nat) : base.Value), indices := [], signs := [] }
    let native := Algebraic.Context.adjoin root base.isClean
    let alpha := Algebraic.Element.ofPoly (context := native) (DensePoly.ofList [0,1])
    let p : base.Poly := DensePoly.ofList [0,1/((2 : Nat) : base.Value)] + root.raw.head
    let kept := native.reduce p
    let .ok scalar := native.buildSigns [kept] | none
    let .ok joint := native.buildSigns [kept, p-kept] | none
    let fact : Algebraic.SignFact native := ⟨kept, native.signPoly kept, rfl⟩
    let entry ← Algebraic.Packing.make? native.reduce rfl [fact] p joint
    let .ok equation := native.buildSigns
      [alpha.polynomial, alpha.polynomial * entry.value.polynomial - 1] | none
    return .arr #[Codec.poly base.codec p, Codec.poly base.codec kept,
      .number fact.sign, Codec.graph base.codec Tower.Signature.codec (Dag.encode scalar.evidence),
      Codec.graph base.codec Tower.Signature.codec (Dag.encode joint.evidence),
      Codec.graph base.codec Tower.Signature.codec (Dag.encode equation.evidence)]
end Hex.RCF.SelectedInverseFixture

/-- Regenerate the supplied-inverse fixture with native production. Its
ordinary-kernel conformance consumers independently check the frozen data. -/
def main (args : List String) : IO Unit := do
  let some data := Hex.RCF.SelectedInverseFixture.packet |
    throw (IO.userError "inverse fixture producer declined")
  let destination := args.headD "conformance-fixtures/HexRCF/selected-inverse.json"
  let some text := String.fromUTF8? data.writeBytes |
    throw (IO.userError "inverse fixture encoding is not UTF-8")
  IO.FS.writeFile destination (text.trimAsciiEnd.toString ++ "\n")
