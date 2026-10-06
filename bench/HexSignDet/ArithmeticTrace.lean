/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet
import HexSignDet.Compare
import Lean

namespace Hex.SignDetBench.ArithmeticTrace
open Hex.SignDet

structure Stats where
  context : Nat := 10377
  calls : Nat := 0
  operations : Array Nat := Array.replicate 8 0
  maxBits : Nat := 1
  deriving Inhabited

initialize stats : IO.Ref Stats ← IO.mkRef {}

private def bits (q : Rat) : Nat :=
  max (if q.num == 0 then 0 else q.num.natAbs.log2 + 1) (q.den.log2 + 1)

@[noinline, never_extract]
private unsafe def record (op : Nat) (a b c : Rat) : Bool := (unsafeIO do
  stats.modify fun s => { s with
    calls := s.calls + 1
    operations := s.operations.set! op (s.operations[op]! + 1)
    maxBits := max s.maxBits (max (bits a) (max (bits b) (bits c)))}
  return true).toOption.getD true

/-- Measurement cannot affect arithmetic values, even if its Boolean differs. -/
@[implemented_by record, noinline, never_extract]
private def observed (_op : Nat) (_a _b _c : Rat) : Bool := true

@[noinline, never_extract] private def addZero (q : Rat) : Rat := q + 0

@[noinline, never_extract] private def keep (flag : Bool) (q : Rat) : Rat :=
  if flag then q else addZero q

theorem keep_eq (flag : Bool) (q : Rat) : keep flag q = q := by
  cases flag <;> simp [keep, addZero, Rat.add_zero]

@[noinline, never_extract] private def add (a b : Rat) : Rat :=
  let c := a + b
  keep (observed 0 a b c) c
@[noinline, never_extract] private def sub (a b : Rat) : Rat :=
  let c := a - b
  keep (observed 1 a b c) c
@[noinline, never_extract] private def mul (a b : Rat) : Rat :=
  let c := a * b
  keep (observed 2 a b c) c
@[noinline, never_extract] private def div (a b : Rat) : Rat :=
  let c := a / b
  keep (observed 3 a b c) c
@[noinline, never_extract] private def inv (a : Rat) : Rat :=
  let c := a⁻¹
  keep (observed 4 a a c) c
@[noinline, never_extract] private def neg (a : Rat) : Rat :=
  let c := -a
  keep (observed 5 a a c) c
@[noinline, never_extract] private def cast (n : Nat) : Rat :=
  let c : Rat := n
  keep (observed 6 c c c) c
@[noinline, never_extract] private def sign (a : Rat) : Int :=
  Sturm.orderSign (keep (observed 7 a a a) a)

/-- Check the intended subjects with ordinary unobserved coefficient operations. -/
private def checkComparison {context : Nat}
    {left right : Descriptor Rat Nat Sturm.orderSign context}
    (c : Comparison left right) : Bool :=
  [left, right, c.leftEncoding.target, c.rightEncoding.target].all
    (fun d => d.raw.check Sturm.orderSign context d.evidence) &&
  c.common.check context left.raw.head right.raw.head &&
  left.checkReencoding c.leftEncoding.target c.common.head .negInf .posInf
    c.leftEncoding.evidence &&
  right.checkReencoding c.rightEncoding.target c.common.head .negInf .posInf
    c.rightEncoding.evidence &&
  decide (c.leftEncoding.target.fullOrder c.rightEncoding.target = some c.order)

private def endpoint (q : Rat) : Lean.Json := Lean.toJson (q.num, q.den)

private def interval (d : RawDescriptor Rat Nat) : Lean.Json :=
  match d.lower, d.upper with
  | .finite lo, .finite hi => Lean.toJson [endpoint lo, endpoint hi]
  | _, _ => Lean.Json.null

private def polynomial (p : DensePoly Rat) : Lean.Json :=
  Lean.toJson (p.toArray.toList.map fun c => (c.num, c.den))

/-- The public constructors run with value-preserving observed operations.
No field instance or alternate query implementation is introduced. -/
@[noinline, never_extract] private def run (n context : Nat) : Option Lean.Json :=
  letI : Add Rat := ⟨add⟩
  letI : Sub Rat := ⟨sub⟩
  letI : Mul Rat := ⟨mul⟩
  letI : Div Rat := ⟨div⟩
  letI : Inv Rat := ⟨inv⟩
  letI : Neg Rat := ⟨neg⟩
  letI : NatCast Rat := ⟨cast⟩
  do
    let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
    let p := x * x - DensePoly.C 2
    let q := (List.range n).foldl
      (fun q (k : Nat) => q * (x - DensePoly.C ((k : Rat) + 3))) p
    let select := fun head lo hi => (
      match Descriptor.build sign context
        (⟨context, head, .finite lo, .finite hi, [], []⟩ : RawDescriptor Rat Nat) with
      | .ok (.ok d) => some d
      | _ => none)
    let selectedLeft ← select p 0 2
    let selectedSame ← select q 0 2
    let selectedLast ← select q ((n : Rat) + 3/2) ((n : Rat) + 5/2)
    let .ok equal := selectedLeft.buildComparison selectedSame | none
    let .ok strict := selectedLeft.buildComparison selectedLast | none
    if equal.order != .eq || strict.order != .lt ||
        !checkComparison equal || !checkComparison strict then none
    else return Lean.Json.mkObj [
      ("extraFactors", Lean.toJson n), ("context", Lean.toJson selectedLeft.raw.context),
      ("left", polynomial selectedLeft.raw.head), ("right", polynomial selectedSame.raw.head),
      ("factor", polynomial equal.common.factor), ("commonHead", polynomial equal.common.head),
      ("strictFactor", polynomial strict.common.factor),
      ("strictCommonHead", polynomial strict.common.head),
      ("leftInterval", interval selectedLeft.raw), ("sameInterval", interval selectedSame.raw),
      ("lastInterval", interval selectedLast.raw),
      ("equalOrder", Lean.toJson (if equal.order == .eq then "eq" else "wrong")),
      ("strictOrder", Lean.toJson (if strict.order == .lt then "lt" else "wrong")),
      ("standardReplayAccepted", Lean.toJson true)]

def runMain : IO UInt32 := do
  for n in #[1, 2, 3] do
    stats.set {context := 10377 + n}
    -- This read makes the computation depend on the completed reset.
    let context := (← stats.get).context
    let some result := run n context | throw (IO.userError s!"arithmetic trace failed at {n}")
    let s ← stats.get
    if s.operations.any (· == 0) then
      throw (IO.userError "an arithmetic observer has no recorded calls")
    IO.println <| (Lean.Json.mkObj [("result", result),
      ("coefficientCalls", Lean.toJson s.calls),
      ("operationCalls", Lean.toJson s.operations),
      ("maxNormalizedBits", Lean.toJson s.maxBits),
      ("temporaryBitBound", Lean.toJson (2*s.maxBits + 1))]).compress
  return 0

end Hex.SignDetBench.ArithmeticTrace

def main : IO UInt32 := Hex.SignDetBench.ArithmeticTrace.runMain
