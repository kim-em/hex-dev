/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealClosure.Algebraic
import HexSignDet.Codec
import HexOrderedFn.Infinitesimal
import Lean.Data.Json
import LeanBench

namespace Hex.RealClosure.NestedNormalization

open SignDet

/-- Ordinary coefficient operations. Raw algebraic values are deliberately
not given a ring or field instance. Each arm changes packing at every level. -/
structure Level where
  Carrier : Type
  zero : Zero Carrier
  equality : DecidableEq Carrier
  one : One Carrier
  add : Add Carrier
  neg : Neg Carrier
  sub : Sub Carrier
  mul : Mul Carrier
  inv : Inv Carrier
  div : Div Carrier
  nat : NatCast Carrier
  alpha : Carrier
  sign : Carrier → Int
  clean : Carrier → Bool
  encode : Carrier → Codec.Json
  decode : Codec.Json → Except String Carrier
  replay : Carrier → Codec.Json → Except String Unit
  replayRoots : Unit → Except String Unit
  evidence : Carrier → Except String Codec.Json
  heads : Array Codec.Json := #[]
  roots : Array Codec.Json := #[]
  reductions : Array Bool := #[]

instance (level : Level) : Zero level.Carrier := level.zero
instance (level : Level) : DecidableEq level.Carrier := level.equality
instance (level : Level) : One level.Carrier := level.one
instance (level : Level) : Add level.Carrier := level.add
instance (level : Level) : Neg level.Carrier := level.neg
instance (level : Level) : Sub level.Carrier := level.sub
instance (level : Level) : Mul level.Carrier := level.mul
instance (level : Level) : Inv level.Carrier := level.inv
instance (level : Level) : Div level.Carrier := level.div
instance (level : Level) : NatCast level.Carrier := level.nat

private def ratJson (q : Rat) : Codec.Json := .arr #[.number q.num, .number q.den]

/-- Rat retains its exact ordinary primitives. -/
def rational : Level where
  Carrier := Rat
  zero := inferInstance
  equality := fun a b => inferInstanceAs (Decidable (a = b))
  one := inferInstance
  add := ⟨fun a b => a + b⟩
  neg := ⟨fun a => -a⟩
  sub := ⟨fun a b => a - b⟩
  mul := ⟨fun a b => a * b⟩
  inv := ⟨fun a => a⁻¹⟩
  div := ⟨fun a b => a / b⟩
  nat := inferInstance
  alpha := 1
  sign := fun a => OrderedFn.orderSign a
  clean := fun a => decide (a.den = 1)
  encode := ratJson
  decode := ValueCodec.rat.decode
  replay := fun _ _ => .ok ()
  replayRoots := fun _ => .ok ()
  evidence := fun _ => .ok (.arr #[])

private def codec (level : Level) : ValueCodec level.Carrier :=
  ⟨level.encode, level.decode⟩
private def unitCodec : ValueCodec Unit :=
  ⟨fun _ => .null, fun j => if j == .null then .ok () else .error "expected null context"⟩

variable {E : Type} [Zero E] [DecidableEq E] [One E] [Add E] [Neg E]
  [Sub E] [Mul E] [Inv E] [Div E] [NatCast E] {sign : E → Int}
  {context : Algebraic.Context E Unit sign ()}

private def treeNodes : Replay E Unit → Nat
  | .leaf _ => 1
  | .split _ left right => 1 + treeNodes left + treeNodes right

private def graphJson (level : Level) (tree : Replay level.Carrier Unit) : Codec.Json :=
  letI : Hashable level.Carrier := ⟨fun a => hash (level.encode a)⟩
  let graph := Dag.encode tree
  .arr #[.number (treeNodes tree), .number graph.entries.size,
    Codec.graph (codec level) unitCodec graph]

/-- Both storage arms retain one positive quadratic root and the extraneous
root 3. The nonmonic family uses `(2X² - alpha)(X - 3)` and interval `(0,1]`;
the monic family uses `(X² - alpha)(X - 3)` and interval `(0,2]`.
Eager uses a monic working polynomial while retaining the original descriptor. -/
def adjoin (parent : Level) (eager : Bool)
    (monicDefinition : Bool := false) : Option Level :=
  let quadratic := DensePoly.monomial 2 (NatCast.natCast (if monicDefinition then 1 else 2) : parent.Carrier) - DensePoly.C parent.alpha
  let linear := DensePoly.monomial 1 (1 : parent.Carrier) - DensePoly.C (NatCast.natCast 3 : parent.Carrier)
  let head : DensePoly parent.Carrier := quadratic * linear
  let raw : RawDescriptor parent.Carrier Unit := ⟨(), head, .finite 0, .finite (if monicDefinition then 1 + 1 else 1), [], []⟩
  match Descriptor.validate parent.sign () raw with
  | none => none
  | some descriptor =>
    let context := Algebraic.Context.adjoin descriptor parent.clean
    let working := DensePoly.monicize head
    if monic : working.leadingCoeff = 1 then
      let pack (p : DensePoly parent.Carrier) : Algebraic.Element context :=
        if eager then Algebraic.Element.ofPoly (DensePoly.divModMonic p working monic).2
        else Algebraic.Element.ofPoly p
      let inverse (a : Algebraic.Element context) : Algebraic.Element context :=
        match a.stored with
        | none => 0
        | some _ => pack a.inverseCandidate
      let multiply (a b : Algebraic.Element context) : Algebraic.Element context :=
        pack (a.polynomial * b.polynomial)
      some {
        Carrier := Algebraic.Element context
        zero := inferInstance
        equality := fun a b => inferInstanceAs (Decidable (a = b))
        one := ⟨pack 1⟩
        add := ⟨fun a b => pack (a.polynomial + b.polynomial)⟩
        neg := ⟨fun a => pack (0 - a.polynomial)⟩
        sub := ⟨fun a b => pack (a.polynomial - b.polynomial)⟩
        mul := ⟨multiply⟩
        inv := ⟨inverse⟩
        div := ⟨fun a b => multiply a (inverse b)⟩
        nat := ⟨fun n => pack (DensePoly.C n)⟩
        alpha := pack (DensePoly.monomial 1 1)
        sign := fun a => a.sign
        clean := Algebraic.Element.isClean
        encode := fun a => Codec.poly (codec parent) a.polynomial
        decode := fun j => do
          let polynomial ← Codec.readPoly (codec parent) j
          let value : Algebraic.Element context := Algebraic.Element.ofPoly polynomial
          if Codec.poly (codec parent) value.polynomial == j then return value
          else throw "noncanonical algebraic value"
        replayRoots := fun _ => do
          let _ ← parent.replayRoots ()
          let packet ← Codec.tuple 3 (graphJson parent descriptor.evidence)
          let _ ← Dag.decodeDescriptor (codec parent) unitCodec parent.sign () raw
            packet[2].writeBytes
          return ()
        replay := fun a packet => do
          let fields ← Codec.tuple 3 packet
          let _ ← Dag.decodeSigns (codec parent) unitCodec descriptor [a.polynomial]
            ⟨#[a.sign], rfl⟩ fields[2].writeBytes
          return ()
        evidence := fun a => do
          let signs ← (descriptor.buildSigns [a.polynomial]).mapError (fun error => s!"{repr error}")
          return graphJson parent signs.evidence
        heads := parent.heads.push (Codec.poly (codec parent) head)
        roots := parent.roots.push (graphJson parent descriptor.evidence)
        reductions := parent.reductions.push context.canReduce
      }
    else none

/-- Assemble actual cached contexts outside the measured workload. -/
def prepare (depth : Nat) (eager : Bool) (monicDefinition : Bool := false) : Option Level := do
  let mut level := if monicDefinition then { rational with alpha := rational.nat.natCast 2 } else rational
  for _ in List.range depth do
    level ← adjoin level eager monicDefinition
  return level

/-- This grows the stored multiplication chain and exercises a genuine local
inverse split at every requested top level: the selected root never equals 3. -/
@[noinline] def run (level : Level) (steps : Nat) (alpha : level.Carrier) : level.Carrier :=
  let seed := 1 + alpha
  let product := (List.range steps).foldl (fun a _ => a * seed) 1
  product / (alpha - NatCast.natCast 3)

private def leanJson (value : Codec.Json) : Except String Lean.Json :=
  Lean.Json.parse (String.fromUTF8! value.writeBytes)

/-- Functional output only. A scientific protocol, frozen source and capture
schedule must be registered before elapsed times are used as evidence. -/
def emit (depth steps : Nat) (eager : Bool) (reportHash : Bool := true)
    (monicDefinition : Bool := false) : IO Unit := do
  let some level := prepare depth eager monicDefinition | throw (IO.userError "nested context preparation failed")
  if monicDefinition then
    unless level.reductions.size == depth && level.reductions.all id do
      throw (IO.userError "monic clean production reduction was not enabled")
  let input ← IO.mkRef (some level.alpha)
  let some alpha ← input.get | throw (IO.userError "missing nested input")
  let value := run level steps alpha
  let encoded := level.encode value
  let digest := hash encoded
  if reportHash then IO.println s!"hash {digest}"
  let .ok proof := level.evidence value | throw (IO.userError "query evidence production failed")
  let .ok decoded := level.decode encoded | throw (IO.userError "value reader rejected")
  unless level.encode decoded == encoded do throw (IO.userError "value roundtrip mismatch")
  let .ok _ := level.replayRoots () | throw (IO.userError "root graph replay rejected")
  let .ok _ := level.replay value proof | throw (IO.userError "query graph replay rejected")
  let .ok result := leanJson encoded | throw (IO.userError "value serialization failed")
  let .ok definitions := leanJson (.arr level.heads) | throw (IO.userError "definition serialization failed")
  let .ok roots := leanJson (.arr level.roots) | throw (IO.userError "root evidence serialization failed")
  let .ok proof := leanJson proof | throw (IO.userError "query evidence serialization failed")
  IO.println <| (Lean.Json.mkObj ([
    ("depth", Lean.toJson depth), ("steps", Lean.toJson steps),
    ("eager", Lean.toJson eager), ("hash", Lean.toJson digest.toNat),
    ("sign", Lean.toJson (level.sign value)), ("value", result),
    ("value_roundtrip", Lean.toJson true), ("roots_replayed", Lean.toJson true),
    ("query_replayed", Lean.toJson true),
    ("heads", definitions), ("roots", roots), ("query", proof)] ++
      (if monicDefinition then [("monic", Lean.toJson true),
        ("production_reductions", Lean.toJson level.reductions)] else []))).compress

namespace Measure

/-- Each registered action reads its actual typed input through IO before
running the pure kernel. This prevents preparation from evaluating the workload. -/
private def action (level : Level) (steps : Nat) : IO (IO UInt64) := do
  let input ← IO.mkRef level.alpha
  return do
    let alpha ← input.get
    return hash (level.encode (run level steps alpha))

initialize actions : IO.Ref (List ((Nat × Nat × Bool) × IO UInt64)) ← IO.mkRef []
initialize monicActions : IO.Ref (List ((Nat × Nat) × IO UInt64)) ← IO.mkRef []

/-- All context/descriptor construction is completed before harness timing. -/
def install : IO Unit := do
  let mut inputs := []
  for depth in [1, 2] do
    for eager in [false, true] do
      let some level := prepare depth eager | throw (IO.userError "measurement context rejected")
      for steps in [2, 4, 8, 16] do
        let compute ← action level steps
        inputs := inputs ++ [((depth, steps, eager), compute)]
  actions.set inputs
  let mut monicInputs := []
  for depth in [1, 2] do
    let some level := prepare depth false true
      | throw (IO.userError "monic context rejected")
    unless level.reductions.size == depth && level.reductions.all id do
      throw (IO.userError "monic clean reduction was not enabled")
    for steps in [2, 4, 8, 16] do
      let compute ← action level steps
      monicInputs := monicInputs ++ [((depth, steps), compute)]
  monicActions.set monicInputs

/-- Production packing in the monic-clean family. Every stored context enables
its existing monic remainder path; no additional eager reduction is applied. -/
private def measureMonic (depth steps : Nat) : IO UInt64 := do
  let some input := (← monicActions.get).find? (fun input => input.1 == (depth, steps))
    | throw (IO.userError "missing monic measurement input")
  input.2

private def measure (depth steps : Nat) (eager : Bool) : IO UInt64 := do
  let some (_, compute) := (← actions.get).find? (fun input => input.1 == (depth, steps, eager)) |
    throw (IO.userError "measurement input missing")
  compute

namespace Depth1

def clean2 (_ : Unit) : IO UInt64 := measure 1 2 false

setup_fixed_benchmark clean2 where {
  expectedHash := some 0xc0fb77a71e36c625
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean4 (_ : Unit) : IO UInt64 := measure 1 4 false

setup_fixed_benchmark clean4 where {
  expectedHash := some 0x89c0b97ebc57fd9a
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean8 (_ : Unit) : IO UInt64 := measure 1 8 false

setup_fixed_benchmark clean8 where {
  expectedHash := some 0xab29785e84ba06
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean16 (_ : Unit) : IO UInt64 := measure 1 16 false

setup_fixed_benchmark clean16 where {
  expectedHash := some 0x65836c88d9e27258
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager2 (_ : Unit) : IO UInt64 := measure 1 2 true

setup_fixed_benchmark eager2 where {
  expectedHash := some 0x6543b969183eca94
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager4 (_ : Unit) : IO UInt64 := measure 1 4 true

setup_fixed_benchmark eager4 where {
  expectedHash := some 0x72d28e9734488a8c
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager8 (_ : Unit) : IO UInt64 := measure 1 8 true

setup_fixed_benchmark eager8 where {
  expectedHash := some 0x7f3ac14148f96d7d
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager16 (_ : Unit) : IO UInt64 := measure 1 16 true

setup_fixed_benchmark eager16 where {
  expectedHash := some 0x5d0e7bba1e93af81
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic2 (_ : Unit) : IO UInt64 := measureMonic 1 2

setup_fixed_benchmark monic2 where {
  expectedHash := some 0x52be5927adeac334
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic4 (_ : Unit) : IO UInt64 := measureMonic 1 4

setup_fixed_benchmark monic4 where {
  expectedHash := some 0xcc5de4e3a24f98e7
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic8 (_ : Unit) : IO UInt64 := measureMonic 1 8

setup_fixed_benchmark monic8 where {
  expectedHash := some 0xeb4f7d69b64e3813
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic16 (_ : Unit) : IO UInt64 := measureMonic 1 16

setup_fixed_benchmark monic16 where {
  expectedHash := some 0x2e9d1cd90b33a280
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

end Depth1

namespace Depth2

def clean2 (_ : Unit) : IO UInt64 := measure 2 2 false

setup_fixed_benchmark clean2 where {
  expectedHash := some 0xd810a57d553cd32a
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean4 (_ : Unit) : IO UInt64 := measure 2 4 false

setup_fixed_benchmark clean4 where {
  expectedHash := some 0xf9c32eabe35d037a
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean8 (_ : Unit) : IO UInt64 := measure 2 8 false

setup_fixed_benchmark clean8 where {
  expectedHash := some 0x93ef161c7f29988d
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def clean16 (_ : Unit) : IO UInt64 := measure 2 16 false

setup_fixed_benchmark clean16 where {
  expectedHash := some 0xb42a715536ce7cc9
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager2 (_ : Unit) : IO UInt64 := measure 2 2 true

setup_fixed_benchmark eager2 where {
  expectedHash := some 0xff1c20bd74c34c12
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager4 (_ : Unit) : IO UInt64 := measure 2 4 true

setup_fixed_benchmark eager4 where {
  expectedHash := some 0x3a11f59e602ed3e2
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager8 (_ : Unit) : IO UInt64 := measure 2 8 true

setup_fixed_benchmark eager8 where {
  expectedHash := some 0x45a014cfa05b79bb
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def eager16 (_ : Unit) : IO UInt64 := measure 2 16 true

setup_fixed_benchmark eager16 where {
  expectedHash := some 0x8ce9f2bcbdb855b6
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic2 (_ : Unit) : IO UInt64 := measureMonic 2 2

setup_fixed_benchmark monic2 where {
  expectedHash := some 0xfac083410288fa84
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic4 (_ : Unit) : IO UInt64 := measureMonic 2 4

setup_fixed_benchmark monic4 where {
  expectedHash := some 0xba69f215fcd43836
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic8 (_ : Unit) : IO UInt64 := measureMonic 2 8

setup_fixed_benchmark monic8 where {
  expectedHash := some 0x3c8d7d9d636caaa5
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

def monic16 (_ : Unit) : IO UInt64 := measureMonic 2 16

setup_fixed_benchmark monic16 where {
  expectedHash := some 0x3000f3c7ecbeba3d
  warmupFirstIter := true
  minTotalSeconds := 0.5
  maxSecondsPerCall := 120.0
}

end Depth2

end Measure

end Hex.RealClosure.NestedNormalization

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    Hex.RealClosure.NestedNormalization.emit 2 2 false false
    Hex.RealClosure.NestedNormalization.emit 2 2 true false
  | "run" :: _ | "compare" :: _ | "profile" :: _ | "_probe_floor" :: _ |
      "_child" :: _ | "verify" :: _ | "list" :: _ | "--help" :: _ =>
    Hex.RealClosure.NestedNormalization.Measure.install
    return ← LeanBench.Cli.dispatch args
  | ["monic"] =>
    for depth in [1, 2] do
      for steps in [2, 4, 8, 16] do
        Hex.RealClosure.NestedNormalization.emit depth steps false false true
  | ["monic", depth, steps] =>
    let some depth := depth.toNat? | throw (IO.userError "invalid depth")
    let some steps := steps.toNat? | throw (IO.userError "invalid steps")
    unless depth > 0 do throw (IO.userError "positive depth required")
    Hex.RealClosure.NestedNormalization.emit depth steps false true true
  | [depth, steps, policy, "plain"] =>
    let some depth := depth.toNat? | throw (IO.userError "invalid depth")
    let some steps := steps.toNat? | throw (IO.userError "invalid steps")
    unless depth > 0 && (policy == "clean" || policy == "eager") do
      throw (IO.userError "usage: hexrealclosure_nested_normalization depth steps clean|eager plain")
    Hex.RealClosure.NestedNormalization.emit depth steps (policy == "eager")
  | _ => throw (IO.userError "usage: hexrealclosure_nested_normalization depth steps clean|eager plain")
  return 0
