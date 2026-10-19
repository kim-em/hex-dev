/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Read

open Hex Hex.RealClosure Hex.SignDet
open Hex.RCF.SelectedRootTests.Data
namespace Hex.RCF.SelectedRootTests.PacketFields
open Hex.RCF.SelectedRootTests

def key (literal : Codec.Json) : base.Poly :=
  (Codec.readPoly base.codec literal).toOption.getD 0

theorem fields (literal : Codec.Json) (claimed : Int) (evidence : Codec.Json)
    (fact : Algebraic.SignFact native)
    (accepted : Read.fromPacket? literal claimed evidence = some fact) :
    fact.polynomial = key literal ∧ fact.sign = claimed := by
  unfold Read.fromPacket? at accepted
  cases hp : Codec.readPoly base.codec literal with
  | error message => simp [hp, bind, Option.bind, Except.toOption] at accepted
  | ok polynomial =>
    simp only [hp, Except.toOption, bind, Option.bind] at accepted
    cases hg : Codec.readGraph base.codec Tower.Signature.codec base.signature lower.raw.head
        lower.raw.lower lower.raw.upper evidence with
    | error message => simp [hg] at accepted
    | ok graph =>
      simp only [hg] at accepted
      cases hm : graph.validate? base.sign base.signature lower.raw.head lower.raw.lower lower.raw.upper with
      | none => simp [hm] at accepted
      | some memo =>
        simp only [hm] at accepted
        have exactFields := native.readSignFact_fields rational.value rational.zero_iff rational.one
          rational.add rational.sub rational.mul rational.nat rational.sign rational.neg rational.inv
          polynomial claimed memo graph.root fact accepted
        simpa only [key, hp, Except.toOption, Option.getD_some] using exactFields

/-- Literal key and sign fields reuse the already checked packet acceptance.
Only the rational key parser is needed for subsequent scalar lookups. -/
def restore (literal : Codec.Json) (claimed : Int) (evidence : Codec.Json)
    (accepted : (Read.fromPacket? literal claimed evidence).isSome = true) :
    Algebraic.SignFact native :=
  let read := Read.fromPacket? literal claimed evidence
  let fact := read.get accepted
  let exactFields := fields literal claimed evidence fact (Option.some_get accepted).symm
  {polynomial := key literal, sign := claimed, checked := by
    rw [← exactFields.1, ← exactFields.2]
    exact fact.checked}

end Hex.RCF.SelectedRootTests.PacketFields
