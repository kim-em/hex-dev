/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRealClosureTheory.NativeFactory
public import HexRealClosure.SignCodec

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta Hex.SignDet

/-- Ordered original owners and their native coefficient codecs. The reader
callback receives the independently checked predecessor codec for each packet;
its result is checked at the original scalar request by `readScalar`. -/
structure NativeCodecs where
  factory : NativeFactory
  base : Expr
  read : Nat → Expr → Expr → Expr → Expr → MetaM Expr

private def fields (value : Codec.Json) : MetaM (Array Codec.Json) :=
  match value.getArr? with
  | .ok result => pure result
  | .error error => throwError "native coefficient fields: {error}"

/-- Recursively prove every nonzero stored coefficient key. Literal lower
coefficients and graph coefficients are saturated separately, since replay
graphs may contain coefficients absent from the requested polynomial. Native
evaluation exports only JSON; every scalar fact is read and kernel-checked.
Depth counts actual algebraic owners above the supplied base codec. -/
unsafe def NativeCodecs.values (data : NativeCodecs) (depth : Nat)
    (values : Array Codec.Json) : MetaM Expr := do
  match depth with
  | 0 => return data.base
  | depth + 1 =>
    let some owner := data.factory.owners[depth]? |
      throwError "native coefficient codec has no original owner at depth {depth}"
    let mut keys := #[]
    let mut lower := #[]
    for value in values.toList.eraseDups do
      let pair ← fields value
      if pair.isEmpty then continue
      unless pair.size == 2 do throwError "stored coefficient has wrong field count"
      lower := lower ++ (← fields pair[0]!)
      keys := keys.push pair
    let coefficientCodec ← data.values depth lower
    let mut facts := []
    for pair in keys do
      let polynomial ← checkedRecord (← mkAppM ``Except.toOption
        #[← mkAppM ``Codec.readPoly #[coefficientCodec, jsonExpr pair[0]!]])
      let tag ← match Codec.Json.decode (α := Int) pair[1]! with
        | .ok tag => pure tag
        | .error error => throwError "stored coefficient sign: {error}"
      unless tag != 0 do throwError "noncanonical stored zero coefficient"
      let (claimed, packet) ← NativePackets.sign owner.valueCodec owner.contextCodec
        owner.context polynomial (data.factory.owners.map NativeOwner.context)
      unless claimed == tag do throwError "stored coefficient sign disagrees with native packet"
      let graphCodec ← match depth with
        | 0 => pure data.base
        | previous + 1 => do
          let some predecessor := data.factory.owners[previous]? |
            throwError "native coefficient codec lost its predecessor"
          let children ← NativePackets.children predecessor.valueCodec owner.contextCodec
            owner.context (jsonExpr packet)
          data.values (previous + 1) (← fields children)
      let reader ← data.read depth graphCodec polynomial (toExpr claimed) (jsonExpr packet)
      let fact ← data.factory.readScalar owner polynomial (toExpr claimed) reader
      facts := facts ++ [fact]
    let factsExpr ← mkListLit (← mkAppM ``SignFact #[owner.context]) facts
    mkAppM ``Element.signCodec #[coefficientCodec, factsExpr]

/-- Build a strict coefficient codec for the entire literal graph at one
retained owner. Original domain checks remain in the eventual graph reader. -/
unsafe def NativeCodecs.graph (data : NativeCodecs) (index : Nat)
    (packet : Codec.Json) : MetaM Expr := do
  match index with
  | 0 => return data.base
  | previous + 1 =>
    let some owner := data.factory.owners[index]? |
      throwError "native graph codec has no original owner"
    let some predecessor := data.factory.owners[previous]? |
      throwError "native graph codec has no original predecessor"
    let children ← NativePackets.children predecessor.valueCodec owner.contextCodec
      owner.context (jsonExpr packet)
    data.values (previous + 1) (← fields children)

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
