/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet
import HexRationalFn
import HexOrderedFn.Infinitesimal
import Lean.Data.Json
import Hex.Conformance.Emit

namespace Hex.SignDet.NestedFields
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
  anchor : Carrier

/-- Add a positive infinitesimal smaller than every positive predecessor value.
The first generator is ε₁-ε₁²; later levels subtract the new infinitesimal. -/
def extend (base : Coefficients) (initial : Bool) : Coefficients :=
  letI := base.field
  letI := base.equality
  let e : RationalFn base.Carrier := RationalFn.X
  { Carrier := RationalFn base.Carrier
    field := inferInstance
    equality := inferInstance
    sign := OrderedFn.Infinitesimal.sign base.sign
    fingerprint := fun f => hash (f.num.toArray.map base.fingerprint,
      f.den.toArray.map base.fingerprint)
    encode := fun f => Lean.Json.mkObj [
      ("num", Lean.Json.arr (f.num.toArray.map base.encode)),
      ("den", Lean.Json.arr (f.den.toArray.map base.encode))]
    generator := if initial then e - e * e else RationalFn.C base.generator - e
    anchor := if initial then e else RationalFn.C base.generator }

/-- Depth zero is the rational field. Positive depths are iterated rational
function fields using canonical arithmetic and the existing proved field laws. -/
def coefficients : Nat → Coefficients
  | 0 => ⟨Rat, inferInstance, inferInstance, Sturm.orderSign, hash,
    (fun q => Lean.toJson #[q.num, (q.den : Int)]), 0, 0⟩
  | n + 1 => extend (coefficients n) (n == 0)

private def entries {r : Nat} (s : System r) : List (List Int × Int) :=
  s.positive.map fun i => (s.columns[i], s.counts[i])

private def inputWith {E : Type} [Lean.Grind.Field E] [DecidableEq E]
    (g a : E) : DensePoly E × List (DensePoly E) :=
  let x : DensePoly E := DensePoly.ofCoeffs #[0, 1]
  (x * x - DensePoly.C (g * g), [x - DensePoly.C g, x - DensePoly.C a])

private def failure (message : String) : Lean.Json :=
  Lean.Json.mkObj [("status", Lean.toJson "error"), ("error", Lean.toJson message)]

private def produced {E : Type} [Lean.Grind.Field E] [DecidableEq E] [Hashable E]
    [NatCast E] (sign : E → Int) (domain : Sturm.PreparedDomain E)
    (qs : List (DensePoly E)) (foreign : Replay E Nat) (reduced : Bool) : Lean.Json :=
  match buildPrepared (10377 : Nat) domain qs reduced with
  | .error error => failure (reprStr error)
  | .ok built =>
    let tree := built.val
    let graph := Dag.encode tree
    let layout := graph.root != 0 && graph.entries[0]?.any (fun entry => entry.children.isNone)
    let stale := { graph with entries := graph.entries.modify 0 fun entry =>
      { entry with node := { entry.node with context := 10378 } } }
    let copied := { graph with entries := graph.entries.modify 0 fun entry =>
      { entry with node := foreign.node } }
    let copiedMoment := { copied with entries := copied.entries.modify 0 fun entry =>
      { entry with node := { entry.node with head := domain.head } } }
    Lean.Json.mkObj [
      ("status", Lean.toJson "ok"), ("table", Lean.toJson (entries tree.node.system)),
      ("replay", Lean.toJson (tree.check sign 10377 domain.head .negInf .posInf qs)),
      ("graphReplay", Lean.toJson (graph.check sign 10377 domain.head .negInf .posInf qs)),
      ("leafLayout", Lean.toJson layout),
      ("foreignContextReplay", Lean.toJson (graph.check sign 10378 domain.head .negInf .posInf qs)),
      ("staleChildReplay", Lean.toJson (stale.check sign 10377 domain.head .negInf .posInf qs)),
      ("copiedHeadReplay", Lean.toJson (copied.check sign 10377 domain.head .negInf .posInf qs)),
      ("copiedMomentReplay", Lean.toJson (copiedMoment.check sign 10377 domain.head .negInf .posInf qs)),
      ("missingSupportReplay", Lean.toJson ((Replay.leaf tree.node).check sign 10377
        domain.head .negInf .posInf qs))]

private def resultWith {E : Type} [Lean.Grind.Field E] [DecidableEq E] [Hashable E]
    (sign : E → Int) (encode : E → Lean.Json) (g a : E) : Lean.Json :=
  letI : NatCast E := Lean.Grind.Semiring.natCast
  let (p, qs) := inputWith g a
  let data := Lean.Json.mkObj [
    ("head", Lean.Json.arr (p.toArray.map encode)),
    ("queries", Lean.Json.arr (qs.toArray.map fun q => Lean.Json.arr (q.toArray.map encode)))]
  match Sturm.prepare sign p .negInf .posInf with
  | none => failure "invalid root domain"
  | some domain =>
    let (foreignHead, _) := inputWith (g + g) a
    match Sturm.prepare sign foreignHead .negInf .posInf with
    | none => failure "invalid foreign root domain"
    | some other =>
      match buildPrepared (10377 : Nat) other (qs.take 1), referencePrepared (10377 : Nat) domain qs with
      | .ok foreign, .ok full => Lean.Json.mkObj [
          ("status", Lean.toJson "ok"), ("input", data),
          ("generatorSign", Lean.toJson (sign g)),
          ("anchorDifferenceSign", Lean.toJson (sign (g - a))),
          ("foreignChildValid", Lean.toJson (foreign.val.check sign 10377 foreignHead
            .negInf .posInf (qs.take 1))),
          ("reduced", produced sign domain qs foreign.val true),
          ("direct", produced sign domain qs foreign.val false),
          ("reference", Lean.Json.mkObj [("status", Lean.toJson "ok"),
            ("table", Lean.toJson (entries full.system)),
            ("replay", Lean.toJson (full.check sign 10377 p .negInf .posInf qs))])]
      | _, _ => failure "foreign leaf or full-reference construction failed"

private def result (depth : Nat) : Lean.Json :=
  let k := coefficients depth
  letI := k.field
  letI := k.equality
  letI : Hashable k.Carrier := ⟨k.fingerprint⟩
  resultWith k.sign k.encode k.generator k.anchor

/-- Exercise the actual invalid-domain operation at depth zero. -/
private def zeroInvalid : Bool :=
  let (p, _) := inputWith (0 : Rat) 0
  (Sturm.prepare Sturm.orderSign p .negInf .posInf).isNone

/-- Emit computed tables and replay decisions. The independent oracle checks
all returned results, including rejected stale and incomplete evidence. -/
def emit (localProfile : Bool) : IO UInt32 := do
  unless zeroInvalid do throw (IO.userError "depth-zero head unexpectedly accepted")
  for depth in (if localProfile then #[1, 2, 3, 4] else #[1, 2]) do
    let start ← IO.monoNanosNow
    let context := Lean.Json.mkObj [
      ("id", Lean.toJson (10377 : Nat)),
      ("levels", Lean.toJson ((List.range depth).map fun i => s!"epsilon{i + 1}")),
      ("order", Lean.toJson "each-new-level-smaller-than-positive-base-elements")]
    let row := Lean.Json.mkObj [
      ("family", Lean.toJson "nested-infinitesimal-coefficients"),
      ("extensionDepth", Lean.toJson depth), ("coefficientContext", context),
      ("zeroDomainRejected", Lean.toJson zeroInvalid), ("result", result depth)]
    Hex.Conformance.Emit.emitResult "HexSignDet" s!"nested-field/depth-{depth}" "table" row.compress
    (← IO.getStdout).flush
    let elapsed := (← IO.monoNanosNow) - start
    (← IO.getStderr).putStrLn s!"nested-field/depth-{depth}: {elapsed} ns"
  return 0

end Hex.SignDet.NestedFields

def main (args : List String) : IO UInt32 :=
  if args == [] || args == ["--profile", "ci"] then Hex.SignDet.NestedFields.emit false
  else if args == ["--profile", "local"] then Hex.SignDet.NestedFields.emit true
  else do
    (← IO.getStderr).putStrLn "usage: hexsigndet_emit_nested_fields [--profile ci|local]"
    return 1
