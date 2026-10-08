/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet
public import HexRationalFn
public import HexOrderedFn.Infinitesimal
public import Lean.Data.Json

public section

namespace Hex.SignDetBench.NestedTrace
open Hex.SignDet

private structure Coefficients where
  Carrier : Type
  field : Lean.Grind.Field Carrier
  equality : DecidableEq Carrier
  sign : Carrier → Int
  encode : Carrier → Lean.Json
  size : Carrier → Nat × Nat
  epsilon : Carrier

private def coefficients : Nat → Coefficients
  | 0 => ⟨Rat, inferInstance, inferInstance, Sturm.orderSign,
      fun q => Lean.toJson (q.num, q.den),
      fun q => (max (q.num.natAbs.log2 + 1) (q.den.log2 + 1), 1), 1⟩
  | depth + 1 =>
    let base := coefficients depth
    letI := base.field
    letI := base.equality
    { Carrier := RationalFn base.Carrier
      field := inferInstance
      equality := inferInstance
      sign := OrderedFn.Infinitesimal.sign base.sign
      encode := fun f => Lean.Json.mkObj [
        ("num", Lean.Json.arr (f.num.toArray.map base.encode)),
        ("den", Lean.Json.arr (f.den.toArray.map base.encode))]
      size := fun f => (f.num.toArray ++ f.den.toArray).foldl
        (fun (bits, slots) c => let (b, s) := base.size c; (max bits b, slots+s)) (1, 0)
      epsilon := RationalFn.X }

structure Stats where
  context : Nat := 10377
  calls : Nat := 0
  maxBits : Nat := 1
  maxSlots : Nat := 1
  deriving Inhabited
initialize stats : IO.Ref Stats ← IO.mkRef {}

@[noinline, never_extract]
private unsafe def record (bits slots : Nat) : Bool := (unsafeIO do
  stats.modify fun s => { s with
    calls := s.calls + 1
    maxBits := max s.maxBits bits
    maxSlots := max s.maxSlots slots }
  return true).toOption.getD true

@[implemented_by record, noinline, never_extract]
private def observed (_bits _slots : Nat) : Bool := true

@[noinline, never_extract] private def addZero {E : Type} [Lean.Grind.Field E] (q : E) : E := q+0
@[noinline, never_extract] private def keep {E : Type} [Lean.Grind.Field E]
    (flag : Bool) (q : E) : E := if flag then q else addZero q

private theorem keep_eq {E : Type} [Lean.Grind.Field E] (flag : Bool) (q : E) : keep flag q = q := by
  cases flag <;> simp [keep, addZero, Lean.Grind.Semiring.add_zero]

@[noinline, never_extract] private def observe {E : Type} [Lean.Grind.Field E]
    (size : E → Nat × Nat) (a b c : E) : E :=
  let sa := size a
  let sb := size b
  let sc := size c
  keep (observed (max sa.1 (max sb.1 sc.1)) (max sa.2 (max sb.2 sc.2))) c

/-- Observe coefficient operands of the existing nested-table family.
The recursive fields and all their arithmetic are the existing instances. -/
@[noinline, never_extract] private def run (depth count context : Nat) : Option Lean.Json :=
  let k := coefficients depth
  letI := k.field
  letI := k.equality
  letI : NatCast k.Carrier := Lean.Grind.Semiring.natCast
  let check := fun (p : DensePoly k.Carrier) (qs : List (DensePoly k.Carrier))
      (t : Replay k.Carrier Nat) => t.check k.sign context p .negInf .posInf qs
  let add := fun a b : k.Carrier => observe k.size a b (a+b)
  let sub := fun a b : k.Carrier => observe k.size a b (a-b)
  let mul := fun a b : k.Carrier => observe k.size a b (a*b)
  let inv := fun a : k.Carrier => observe k.size a a a⁻¹
  let neg := fun a : k.Carrier => observe k.size a a (-a)
  let cast := fun n : Nat => let a : k.Carrier := n; observe k.size a a a
  let sign := fun a : k.Carrier => k.sign (observe k.size a a a)
  letI : Add k.Carrier := ⟨add⟩
  letI : Sub k.Carrier := ⟨sub⟩
  letI : Mul k.Carrier := ⟨mul⟩
  letI : Inv k.Carrier := ⟨inv⟩
  letI : Neg k.Carrier := ⟨neg⟩
  letI : NatCast k.Carrier := ⟨cast⟩
  do
    let p : DensePoly k.Carrier := DensePoly.ofCoeffs #[0, 1]
    let qs := List.replicate count (DensePoly.C k.epsilon)
    let some domain := Sturm.prepare sign p .negInf .posInf | none
    let .ok built := buildPrepared context domain qs | none
    let tree : Replay k.Carrier Nat := built.val
    let entries := tree.node.system.columns.toArray.zip tree.node.system.counts.toArray
    if !check p qs tree || entries != #[(List.replicate count (1 : Int), (1 : Int))] then none
    else return Lean.Json.mkObj [
      ("depth", Lean.toJson depth), ("queries", Lean.toJson count),
      ("context", Lean.toJson context), ("coefficient", k.encode k.epsilon),
      ("head", Lean.Json.arr (p.toArray.map k.encode)),
      ("queryPolynomials", Lean.toJson (qs.map fun q => Lean.Json.arr (q.toArray.map k.encode))),
      ("lower", Lean.toJson (match tree.node.lower with | .negInf => "negInf" | _ => "wrong")),
      ("upper", Lean.toJson (match tree.node.upper with | .posInf => "posInf" | _ => "wrong")),
      ("entries", Lean.toJson entries), ("standardReplayAccepted", Lean.toJson true)]

def runMain : IO UInt32 := do
  for depth in #[1, 2] do
    for count in #[4, 8] do
      stats.set {context := 10377 + depth*10 + count}
      let context := (← stats.get).context
      let some result := run depth count context | throw (IO.userError "nested coefficient trace failed")
      let s ← stats.get
      if s.calls == 0 then throw (IO.userError "nested observer was eliminated")
      IO.println <| (Lean.Json.mkObj [("result", result),
        ("coefficientCalls", Lean.toJson s.calls), ("maxNormalizedRatBits", Lean.toJson s.maxBits),
        ("maxRationalSlots", Lean.toJson s.maxSlots)]).compress
  return 0
end Hex.SignDetBench.NestedTrace

def main : IO UInt32 := Hex.SignDetBench.NestedTrace.runMain
