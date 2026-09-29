/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Input
import HexRationalFn
import HexOrderedFn.Infinitesimal
import Lean.Data.Json
import Hex.Conformance.Emit

namespace Hex.SignDetBench.Nested
open Hex.SignDet

/-- An actual effective coefficient field, with its ordinary total sign.
Successive fields use the existing lawful rational-function instance. -/
structure Coefficients where
  Carrier : Type
  field : Lean.Grind.Field Carrier
  equality : DecidableEq Carrier
  sign : Carrier → Int
  fingerprint : Carrier → UInt64
  encode : Carrier → Lean.Json
  generator : Carrier

/-- Add a positive infinitesimal smaller than every positive predecessor value.
The generator is the sum of all infinitesimals introduced so far. -/
def extend (base : Coefficients) : Coefficients :=
  letI := base.field
  letI := base.equality
  { Carrier := RationalFn base.Carrier
    field := inferInstance
    equality := inferInstance
    sign := OrderedFn.Infinitesimal.sign base.sign
    fingerprint := fun f => hash (f.num.toArray.map base.fingerprint,
      f.den.toArray.map base.fingerprint)
    encode := fun f => Lean.Json.mkObj [
      ("num", Lean.Json.arr (f.num.toArray.map base.encode)),
      ("den", Lean.Json.arr (f.den.toArray.map base.encode))]
    generator := RationalFn.C base.generator + RationalFn.X }

/-- Depth zero is the rational field. Positive depths are iterated rational
function fields using canonical arithmetic and the existing proved field laws. -/
def coefficients : Nat → Coefficients
  | 0 => ⟨Rat, inferInstance, inferInstance, Sturm.orderSign, hash,
    (fun q => Lean.toJson #[q.num, (q.den : Int)]), 0⟩
  | n + 1 => extend (coefficients n)

private def inputWith {E : Type} [Lean.Grind.Field E] [DecidableEq E]
    (g : E) : DensePoly E × List (DensePoly E) :=
  let x : DensePoly E := DensePoly.ofCoeffs #[0, 1]
  (x * x - DensePoly.C (g * g), [x, x - DensePoly.C g])

/-- At positive depth the head has the two roots ±g. The query X-g has
signs - and 0 there; the query X has signs - and +. The defining equation
and query values are checked by direct polynomial evaluation as well as BKR. -/
private def validWith {E : Type} [Lean.Grind.Field E] [DecidableEq E] [Hashable E]
    (sign : E → Int) (g : E) : Bool :=
  letI : NatCast E := Lean.Grind.Semiring.natCast
  Id.run do
    let (p, qs) := inputWith g
    if !(sign g == 1 && sign (-g) == -1 && p.eval g == 0 && p.eval (-g) == 0 &&
        qs.map (fun q => sign (q.eval (-g))) == [-1, -1] &&
        qs.map (fun q => sign (q.eval g)) == [1, 0]) then
      return false
    let some domain := Sturm.prepare sign p .negInf .posInf | return false
    let .ok reduced := buildPrepared (10377 : Nat) domain qs | return false
    let .ok direct := buildPrepared (10377 : Nat) domain qs false | return false
    let .ok full := referencePrepared (10377 : Nat) domain qs | return false
    let expected := [([-1, -1], (1 : Int)), ([1, 0], 1)]
    if !(entries reduced.val.node.system == expected &&
        entries direct.val.node.system == expected && entries full.system == expected &&
        full.check sign 10377 p .negInf .posInf qs) then
      return false
    let graph := Dag.encode reduced.val
    if !graph.check sign 10377 p .negInf .posInf qs then
      return false
    -- Context checks must reject even when the underlying arithmetic is identical.
    if graph.check sign 10378 p .negInf .posInf qs then
      return false
    let stale := { graph with entries := graph.entries.modify 0 fun entry =>
      { entry with node := { entry.node with context := 10378 } } }
    if stale.check sign 10377 p .negInf .posInf qs then
      return false
    return true

/-- Run the field-specific check using the actual dictionaries at this depth. -/
def valid (depth : Nat) : Bool :=
  if depth == 0 then false else
    let k := coefficients depth
    letI := k.field
    letI := k.equality
    letI : Hashable k.Carrier := ⟨k.fingerprint⟩
    validWith k.sign k.generator

private def inputJson (depth : Nat) : Lean.Json :=
  let k := coefficients depth
  letI := k.field
  letI := k.equality
  let (p, qs) := inputWith k.generator
  Lean.Json.mkObj [
    ("coefficientContext", Lean.Json.mkObj [
      ("id", Lean.toJson (10377 : Nat)),
      ("levels", Lean.toJson ((List.range depth).map fun i => s!"epsilon{i + 1}")),
      ("order", Lean.toJson "each-new-level-smaller-than-positive-base-elements")]),
    ("head", Lean.Json.arr (p.toArray.map k.encode)),
    ("queries", Lean.Json.arr (qs.toArray.map fun q => Lean.Json.arr (q.toArray.map k.encode)))]

/-- Untimed conformance only. No scaling, allocation or semantic replay theorem
is inferred from this check. Full cross-level proof sharing is separate. -/
def inspect : IO UInt32 := do
  unless !valid 0 do throw (IO.userError "depth-zero generator is not squarefree")
  for depth in #[1, 2, 3, 4] do
    unless valid depth do throw (IO.userError s!"nested field failed at depth {depth}")
    let row := Lean.Json.mkObj [
      ("family", Lean.toJson "nested-infinitesimal-coefficients"),
      ("extensionDepth", Lean.toJson depth), ("headDegree", Lean.toJson (2 : Nat)),
      ("queries", Lean.toJson (2 : Nat)), ("realizedSupport", Lean.toJson (2 : Nat)),
      ("input", inputJson depth),
      ("table", Lean.toJson [([-1, -1], (1 : Int)), ([1, 0], 1)]),
      ("reduced", Lean.toJson true), ("unreduced", Lean.toJson true),
      ("fullReference", Lean.toJson true), ("foreignContextRejected", Lean.toJson true),
      ("staleChildRejected", Lean.toJson true)]
    Hex.Conformance.Emit.emitResult "HexSignDet" s!"nested-field/depth-{depth}" "table"
      row.compress
    (← IO.getStdout).flush
  return 0

end Hex.SignDetBench.Nested

/-- Run the fixed nested-field conformance cases. -/
def main : IO UInt32 := Hex.SignDetBench.Nested.inspect
