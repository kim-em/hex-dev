/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Data
import HexRealClosure.SignCodec
import HexRealClosure.FactOperations
import HexRCF.SelectedRoot.Literals

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests.Data
namespace Hex.RCF.SelectedRootTests.Read
open Hex.RCF.SelectedRootTests

def rootRead (facts : List (Algebraic.SignFact native)) :=
  Algebraic.RootReplay.readDescriptor (Algebraic.Element.signCodec base.codec facts)
    Tower.Signature.codec parent.sign parent.signature Literals.upperSubject
    Literals.upperGraph

def rawProgram (facts : List (Algebraic.SignFact native)) : Bool :=
  (Algebraic.SignRequests.readRoot (Algebraic.Element.signCodec base.codec facts)
    Tower.Signature.codec Literals.upperSubject).isOk

def rootProgramAt (facts : List (Algebraic.SignFact native)) (binding : Tower.Signature) : Bool :=
  let value := Algebraic.Element.signCodec base.codec facts
  (@Algebraic.RootReplay.readDescriptor (Algebraic.Element native) Tower.Signature _ _ _
    (Algebraic.Element.cachedOne reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq facts)
    (Algebraic.Element.cachedSub reduction reduction_eq facts)
    (Algebraic.Element.cachedMul reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
    value Tower.Signature.codec Algebraic.Element.sign binding
    Literals.upperSubject Literals.upperGraph).isOk

def rootProgram (facts : List (Algebraic.SignFact native)) : Bool :=
  rootProgramAt facts parent.signature

theorem rootProgram_frozen (facts : List (Algebraic.SignFact native)) :
    rootProgram facts = rootProgramAt facts frozenSignature :=
  congrArg (rootProgramAt facts) signature_eq

theorem rootProgram_eq (facts : List (Algebraic.SignFact native)) :
    rootProgram facts = (rootRead facts).isOk := by
  unfold rootProgram rootProgramAt
  dsimp only
  erw [Algebraic.Element.cachedOne_eq reduction reduction_eq facts,
    Algebraic.Element.cachedAdd_eq reduction reduction_eq facts,
    Algebraic.Element.cachedSub_eq reduction reduction_eq facts,
    Algebraic.Element.cachedMul_eq reduction reduction_eq facts,
    Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts]
  rfl

def fromPacket? (polynomial : Codec.Json) (claimed : Int) (evidence : Codec.Json) :
    Option (Algebraic.SignFact native) := do
  let p ← (Codec.readPoly base.codec polynomial).toOption
  let graph ← (Codec.readGraph base.codec Tower.Signature.codec base.signature lower.raw.head
    lower.raw.lower lower.raw.upper evidence).toOption
  let memo ← graph.validate? base.sign base.signature lower.raw.head lower.raw.lower lower.raw.upper
  native.readSignFact? rational.value rational.zero_iff rational.one rational.add rational.sub
    rational.mul rational.nat rational.sign rational.neg rational.inv p claimed memo graph.root
/-- info: 'Hex.RCF.SelectedRootTests.Read.rootProgram_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootProgram_eq
end Hex.RCF.SelectedRootTests.Read
