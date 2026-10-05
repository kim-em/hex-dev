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

/-- Runtime diagnostics preserve the ordinary kernel computation. The event
counts one executed callback; rational gcds internal to Rat are not observed. -/
def traceOp {A : Type} (enabled : Bool) (depth : Nat) (operation : String)
    (run : Unit → A) : A :=
  if enabled then dbgTrace s!"NESTED {depth} {operation}" run else run ()

theorem traceOp_eq {A : Type} (enabled : Bool) (depth : Nat) (operation : String)
    (run : Unit → A) : traceOp enabled depth operation run = run () := by
  cases enabled <;> rfl

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

/-- Rat retains its exact ordinary primitives. Trace wrappers add no arithmetic
and never reject a completed operation or timing sample. -/
def rational (trace : Bool) : Level where
  Carrier := Rat
  zero := inferInstance
  equality := fun a b =>
    if trace then traceOp true 0 (if a.num == 0 || b.num == 0 then "zero" else "eq")
      (fun _ => inferInstanceAs (Decidable (a = b)))
    else inferInstanceAs (Decidable (a = b))
  one := inferInstance
  add := ⟨fun a b => traceOp trace 0 "add" (fun _ => a + b)⟩
  neg := ⟨fun a => traceOp trace 0 "neg" (fun _ => -a)⟩
  sub := ⟨fun a b => traceOp trace 0 "sub" (fun _ => a - b)⟩
  mul := ⟨fun a b => traceOp trace 0 "mul" (fun _ => a * b)⟩
  inv := ⟨fun a => traceOp trace 0 "inv" (fun _ => a⁻¹)⟩
  div := ⟨fun a b => traceOp trace 0 "div" (fun _ => a / b)⟩
  nat := inferInstance
  alpha := 1
  sign := fun a => traceOp trace 0 "sign" (fun _ => OrderedFn.orderSign a)
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

/-- Execute inverseFactor and xgcdLeft once each, following the production
inverseCandidate. The split event observes the already computed local gcd. These events count
only the local inverse sites; gcd calls within other kernels are not counted. -/
def inverseRaw (trace : Bool) (depth : Nat) (a : Algebraic.Element context) : DensePoly E :=
  let factors := traceOp trace depth "inverse_gcd" (fun _ => a.inverseFactor)
  let factors := traceOp (trace && factors.1.natDegree > 0) depth "split" (fun _ => factors)
  let eg := traceOp trace depth "inverse_xgcd" (fun _ => DensePoly.xgcdLeft a.polynomial factors.2)
  DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left

theorem inverseRaw_eq (trace : Bool) (depth : Nat) (a : Algebraic.Element context) :
    inverseRaw trace depth a = a.inverseCandidate := by
  simp only [inverseRaw, traceOp_eq]
  rfl

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
def adjoin (parent : Level) (depth : Nat) (eager trace : Bool)
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
        traceOp trace depth "inv" fun _ =>
          match a.stored with
          | none => 0
          | some _ => pack (inverseRaw trace depth a)
      let multiply (a b : Algebraic.Element context) : Algebraic.Element context :=
        traceOp trace depth "mul" fun _ => pack (a.polynomial * b.polynomial)
      some {
        Carrier := Algebraic.Element context
        zero := inferInstance
        equality := fun a b =>
        if trace then traceOp true depth (if a.stored.isNone || b.stored.isNone then "zero" else "eq")
          (fun _ => inferInstanceAs (Decidable (a = b)))
        else inferInstanceAs (Decidable (a = b))
        one := ⟨pack 1⟩
        add := ⟨fun a b => traceOp trace depth "add" (fun _ => pack (a.polynomial + b.polynomial))⟩
        neg := ⟨fun a => traceOp trace depth "neg" (fun _ => pack (0 - a.polynomial))⟩
        sub := ⟨fun a b => traceOp trace depth "sub" (fun _ => pack (a.polynomial - b.polynomial))⟩
        mul := ⟨multiply⟩
        inv := ⟨inverse⟩
        div := ⟨fun a b => traceOp trace depth "div" (fun _ => multiply a (inverse b))⟩
        nat := ⟨fun n => pack (DensePoly.C n)⟩
        alpha := pack (DensePoly.monomial 1 1)
        sign := fun a => traceOp trace depth "sign" (fun _ => a.sign)
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
def prepare (depth : Nat) (eager trace : Bool) (monicDefinition : Bool := false) : Option Level := do
  let mut level := if monicDefinition then { rational trace with alpha := (rational trace).nat.natCast 2 } else rational trace
  for index in List.range depth do
    level ← adjoin level (index + 1) eager trace monicDefinition
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
def emit (depth steps : Nat) (eager trace : Bool) (reportHash : Bool := true)
    (monicDefinition : Bool := false) : IO Unit := do
  let some level := prepare depth eager trace monicDefinition | throw (IO.userError "nested context preparation failed")
  if monicDefinition then
    unless level.reductions.size == depth && level.reductions.all id do
      throw (IO.userError "monic clean production reduction was not enabled")
  let input ← IO.mkRef (some level.alpha)
  let some alpha ← input.get | throw (IO.userError "missing nested input")
  if trace then
    (← IO.getStderr).putStrLn "NESTED BEGIN"
    (← IO.getStderr).flush
  let value := run level steps alpha
  let encoded := level.encode value
  let digest := hash encoded
  if reportHash then IO.println s!"hash {digest}"
  if trace then
    (← IO.getStderr).putStrLn "NESTED END"
    (← IO.getStderr).flush
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
      let some level := prepare depth eager false | throw (IO.userError "measurement context rejected")
      for steps in [2, 4, 8, 16] do
        let compute ← action level steps
        inputs := inputs ++ [((depth, steps, eager), compute)]
  actions.set inputs
  let mut monicInputs := []
  for depth in [1, 2] do
    let some level := prepare depth false false true
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
    Hex.RealClosure.NestedNormalization.emit 2 2 false false false
    Hex.RealClosure.NestedNormalization.emit 2 2 true false false
  | "run" :: _ | "compare" :: _ | "profile" :: _ | "_probe_floor" :: _ |
      "_child" :: _ | "verify" :: _ | "list" :: _ | "--help" :: _ =>
    Hex.RealClosure.NestedNormalization.Measure.install
    return ← LeanBench.Cli.dispatch args
  | ["monic"] =>
    for depth in [1, 2] do
      for steps in [2, 4, 8, 16] do
        Hex.RealClosure.NestedNormalization.emit depth steps false false false true
  | ["monic", depth, steps] =>
    let some depth := depth.toNat? | throw (IO.userError "invalid depth")
    let some steps := steps.toNat? | throw (IO.userError "invalid steps")
    unless depth > 0 do throw (IO.userError "positive depth required")
    Hex.RealClosure.NestedNormalization.emit depth steps false false true true
  | ["monic", depth, steps, "trace"] =>
    let some depth := depth.toNat? | throw (IO.userError "invalid depth")
    let some steps := steps.toNat? | throw (IO.userError "invalid steps")
    unless depth > 0 do throw (IO.userError "positive depth required")
    Hex.RealClosure.NestedNormalization.emit depth steps false true true true
  | [depth, steps, policy, diagnostic] =>
    let some depth := depth.toNat? | throw (IO.userError "invalid depth")
    let some steps := steps.toNat? | throw (IO.userError "invalid steps")
    unless depth > 0 && (policy == "clean" || policy == "eager") &&
        (diagnostic == "plain" || diagnostic == "trace") do
      throw (IO.userError "usage: hexrealclosure_nested_normalization depth steps clean|eager plain|trace")
    Hex.RealClosure.NestedNormalization.emit depth steps (policy == "eager") (diagnostic == "trace")
  | _ => throw (IO.userError "usage: hexrealclosure_nested_normalization depth steps clean|eager plain|trace")
  return 0
