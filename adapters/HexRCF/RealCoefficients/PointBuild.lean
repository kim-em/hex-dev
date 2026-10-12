/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.PointReplay
public section
namespace Hex.RCF.RealCoefficients.PointBuild
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet

/-- An untrusted ordinary point proposal. Encoded values are hints for checked
scalar records; they do not authenticate the point or any arithmetic. -/
structure Packet where
  subject : Codec.Json
  values : List Codec.Json
  deriving Repr

inductive Error where
  | divisor
  | unresolved
  deriving Repr

/-- A parent-field candidate from a point handle or linear selected head.
This proposes data only; no identity with the selected root is assumed. -/
def rootPoint? {registry : BaseContext.Registry} {parent : Context registry} :
    Root parent → Option parent.Value
  | .point a => some a
  | .selected descriptor _ _ =>
      if descriptor.raw.head.size = 2 then
        some (-descriptor.raw.head.coeff 0 / descriptor.raw.head.leadingCoeff)
      else none

/-- Propose an ordinary parent-field point for an owner's region whose finite
boundaries admit parent-field candidates. Further nonlinear selected roots
need conversion certificates and are outside this helper. Replay checks the
resulting point directly, without trusting its proposed region label. -/
def candidate {registry : BaseContext.Registry} {parent : Context registry} :
    Tower.Sample.Region parent → Option parent.Value
  | .section root => rootPoint? root
  | .whole => some 0
  | .left root => (rootPoint? root).map (fun a => a - 1)
  | .right root => (rootPoint? root).map (fun a => a + 1)
  | .between lower upper => do
      let a ← rootPoint? lower
      let b ← rootPoint? upper
      return (a + b) / (1 + 1)

/-- Search the owner's actual sorted, deduplicated family for a true ordinary
parent-field point. `none` means no supported witness, not a false sentence.
All original guards are preflighted before root production. -/
def build {registry : BaseContext.Registry} (parent : Context registry)
    (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) : Except Error (Option Packet) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let required := RepresentationSpecialize.prepare values formula
  let family := Tower.Sample.family parent required
  for region in family.cells do
    let some sample := candidate region | continue
    match Samples.Row.eval formula (required.map (fun p => parent.sign (p.eval sample))) with
    | none => throw .unresolved
    | some false => pure ()
    | some true => return some {
        subject := parent.codec.encode sample
        values := (sample :: List.ofFn values ++ guards).map parent.codec.encode }
  return none
end Hex.RCF.RealCoefficients.PointBuild
