/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRoots
public import HexRealClosure.TowerEnlargement
public import HexRealClosure.SignCodec

public section

open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.SignDet.Codec (Json)

private def registry : BaseContext.Registry := fun _ => none
private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)
private def emit (data : Json) : IO Unit := do
  let some text := String.fromUTF8? data.writeBytes | throw (IO.userError "invalid fixture UTF-8")
  IO.println text.trimAsciiEnd.toString

private def descriptor {parent : Context registry} (root : Tower.Root parent) : IO Json := do
  let .selected data _ _ := root | throw (IO.userError "expected a selected algebraic root")
  unless data.raw.check parent.sign parent.signature data.evidence do
    throw (IO.userError "selected-root replay failed")
  return Tower.rootData parent.codec data

/-- Exact introductory examples from de Moura–Passmore, CADE 2013, section 4.
The selected square root is retained while adding the later infinitesimal. -/
def main : IO Unit := do
  let base := Context.base (BaseContext.rational registry)
  let x : base.Poly := DensePoly.ofList [0,1]
  let .finite [negative, positive] := base.roots (x*x-DensePoly.C (1+1))
    | throw (IO.userError "square-root producer result changed")
  unless negative.multiplicity == 1 && positive.multiplicity == 1 &&
      negative.root.compare positive.root == .lt &&
      negative.root.context.sign negative.root.value == -1 &&
      positive.root.context.sign positive.root.value == 1 do
    throw (IO.userError "square-root order or multiplicity changed")
  let owner := positive.root.context
  let alpha := positive.root.value
  let inverse := alpha⁻¹
  let square := alpha*alpha
  let cube := square*alpha+1
  unless square == (1+1 : owner.Value) && alpha*inverse == 1 do
    throw (IO.userError "square-root arithmetic failed")
  let squareSigns := [owner.sign alpha, owner.sign inverse, owner.sign square, owner.sign cube]
  emit (object [("case", .string "basic square root"),
    ("context", owner.signature.literal.toJson),
    ("roots", .array (Json.Values.cons (← descriptor negative.root)
      (Json.Values.cons (← descriptor positive.root) .nil))),
    ("multiplicities", Json.of ([1,1] : List Nat)),
    ("values", .arr (#[alpha,inverse,square,cube].map owner.codec.encode)),
    ("signs", Json.of squareSigns)])

  let some enlarged := owner.enlargeWithParameter?
    | throw (IO.userError "square-root enlargement failed")
  let parent := enlarged.conversion.context
  let epsilon := enlarged.parameter
  let moved := enlarged.conversion.value alpha
  let huge : parent.Value := NatCast.natCast (10 ^ 27)
  let bound := epsilon⁻¹-huge
  unless parent.sign epsilon == 1 && parent.sign (epsilon-1) == -1 &&
      moved*moved == (1+1 : parent.Value) && parent.sign moved == 1 &&
      parent.sign bound == 1 do
    throw (IO.userError "infinitesimal or transported square root changed")
  let y : parent.Poly := DensePoly.ofList [0,1]
  let head := y*y*y-DensePoly.C epsilon
  let .finite [entry] := parent.roots head
    | throw (IO.userError "infinitesimal cubic producer result changed")
  let child := entry.root.context
  let beta := entry.root.value
  let embeddedEpsilon := entry.root.embed epsilon
  let difference := beta-embeddedEpsilon
  let equation := beta*beta*beta-embeddedEpsilon
  let values := #[beta,embeddedEpsilon,difference,equation,beta-1]
  let signs := values.map child.sign
  unless entry.multiplicity == 1 && signs == #[1,1,1,0,-1] do
    throw (IO.userError "infinitesimal cube-root arithmetic failed")
  emit (object [("case", .string "basic infinitesimal"),
    ("parent", parent.signature.literal.toJson), ("context", child.signature.literal.toJson),
    ("parameter", parent.codec.encode epsilon), ("transported", parent.codec.encode moved),
    ("bound", parent.codec.encode bound),
    ("head", .arr (head.toArray.map parent.codec.encode)), ("root", ← descriptor entry.root),
    ("multiplicity", Json.of entry.multiplicity),
    ("values", .arr (values.map child.codec.encode)), ("signs", Json.of signs.toList)])

  emit (object [("case", .string "basic unsupported"),
    ("cases", Json.of (["pi-infinitesimal-cubic", "pi-infinitesimal-comparison"] : List String)),
    ("reason", .string "requires a caller-validated pi approximation provider and progress laws")])
