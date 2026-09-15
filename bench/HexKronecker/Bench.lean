/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexKronecker
import LeanBench
import Lean.Data.Json

/-!
The two SPEC families traverse the full atom/degree grid. Accepted points and
declines have separate registrations. The parameter identifies a grid point;
the cost functions use its reported packed bit size, not its atom count.

Mode 2: GMP switches between basecase, Karatsuba, Toom and FFT multiplication
across this grid, so no single tight exponent applies. The published quadratic
upper bound charges every integer multiplication at N², plus traversal and
the coefficient-cap construction. Here coefficient bounds fit in one GMP
limb, so capped arithmetic scans at most the fixed budget's bit count.
See https://gmplib.org/manual/Multiplication-Algorithms and
https://gmplib.org/manual/Basecase-Multiplication .
-/

namespace Hex.Kronecker.Bench

open Hex.MvPoly.Kernel

def budget : Budget := {}

def grid : List (Nat × Nat) :=
  [1,2,3,4,6,8].flatMap fun k => [2,4,8,16].map (k,·)

def sumAtoms (k : Nat) : Expr :=
  (List.range k).foldl (fun a i => .add a (.atom i)) (.int 0)

def treePlan (k d : Nat) : Except SizeError SizeBound :=
  sizeExprEq budget k (.pow (sumAtoms k) d) (.pow (sumAtoms k) d)

def fits (s : Except SizeError SizeBound) : Bool :=
  match s with
  | .ok s => s.accepts budget
  | .error _ => false

def treeAccepted : List (Nat × Nat) := grid.filter fun (k,d) => fits (treePlan k d)
def treeDeclined : List (Nat × Nat) := grid.filter fun (k,d) => !fits (treePlan k d)

def powTerms (k : Nat) (p : PolyList Int) : Nat → PolyList Int
  | 0 => [((List.replicate k 0),1)]
  | n+1 => Hex.MvPoly.Kernel.mul (powTerms k p n) p

def termExpr (e : List Nat) (c : Int) : Expr :=
  (e.zipIdx).foldl (fun a (d,i) => .mul a (.pow (.atom i) d)) (.int c)

def termsExpr (ts : PolyList Int) : Expr :=
  ts.foldl (fun a (e,c) => .add a (termExpr e c)) (.int 0)

def nodes : Expr → Nat
  | .int _ | .atom _ => 1
  | .neg a | .pow a _ => 1 + nodes a
  | .add a b | .sub a b | .mul a b => 1 + nodes a + nodes b

def powMuls : Nat → Nat
  | 0 => 0
  | n+1 => (n+1).log2 + 1 + (Nat.toDigits 2 (n+1)).count '1'

def treeMuls (strides : List Nat) : Expr → Nat
  | .int _ => 0
  | .atom i => powMuls (strides.getD i 0)
  | .neg a => treeMuls strides a
  | .pow a n => treeMuls strides a + powMuls n
  | .add a b | .sub a b => treeMuls strides a + treeMuls strides b
  | .mul a b => treeMuls strides a + treeMuls strides b + 1

structure TreeInput where
  k : Nat
  degree : Nat
  lhs : Expr
  rhs : Expr
  size : SizeBound

instance : Hashable TreeInput where
  hash a := mixHash (hash a.k) (hash a.degree)

def prepTree (i : Nat) : TreeInput :=
  let (k,d) := treeAccepted.getD (i-1) (1,2)
  let p := (List.range k).map fun j => (atomDegrees k j, (1 : Int))
  let lhs := Expr.pow (sumAtoms k) d
  let rhs := termsExpr (powTerms k p d)
  let size := (sizeExprEq budget k lhs rhs).toOption.getD (makeSize budget (Bounds.zero k) [])
  ⟨k,d,lhs,rhs,size⟩

@[noinline] def runTree (a : TreeInput) : UInt64 :=
  if checkExprEq budget a.k a.lhs a.rhs then 1 else 0

def treeWork (i : Nat) : Nat :=
  let a := prepTree i
  (nodes a.lhs + nodes a.rhs) * budget.maxPackedBits +
    (treeMuls a.size.strides a.lhs + treeMuls a.size.strides a.rhs) * a.size.packedBits^2

def termsInput (k d : Nat) : TermMatrix × TermMatrix × TermMatrix :=
  let z := List.replicate k 0
  let p : PolyList Int := (List.range k).map (fun i => (scaleDegrees (d/2) (atomDegrees k i),1)) ++ [(z,1)]
  let q : PolyList Int := (List.range k).map (fun i => (scaleDegrees (d/2) (atomDegrees k i),1)) ++ [(z,-1)]
  let c := Hex.MvPoly.Kernel.smul 2 (Hex.MvPoly.Kernel.mul p q)
  ([[p,q]],[[q],[p]],[[c]])

def productPlan (mode : MulMode) (k d : Nat) : Except SizeError SizeBound :=
  let (a,b,c) := termsInput k d
  sizeMulTerms budget mode k 1 2 1 a b c

def productAccepted (mode : MulMode) : List (Nat × Nat) := grid.filter fun (k,d) => fits (productPlan mode k d)
def productDeclined (mode : MulMode) : List (Nat × Nat) := grid.filter fun (k,d) => !fits (productPlan mode k d)

structure ProductInput where
  k : Nat
  degree : Nat
  a : TermMatrix
  b : TermMatrix
  c : TermMatrix
  size : SizeBound

instance : Hashable ProductInput where
  hash a := mixHash (hash a.k) (hash a.degree)

def prepProduct (mode : MulMode) (i : Nat) : ProductInput :=
  let (k,d) := (productAccepted mode).getD (i-1) (1,2)
  let (a,b,c) := termsInput k d
  ⟨k,d,a,b,c,(sizeMulTerms budget mode k 1 2 1 a b c).toOption.getD (makeSize budget (Bounds.zero k) [])⟩

def prepPlain := prepProduct .plain
def prepPacked := prepProduct .signedPacked

@[noinline] def runPlain (a : ProductInput) : UInt64 :=
  if checkMulTerms budget .plain a.k 1 2 1 a.a a.b a.c then 1 else 0

@[noinline] def runPacked (a : ProductInput) : UInt64 :=
  if checkMulTerms budget .signedPacked a.k 1 2 1 a.a a.b a.c then 1 else 0

def productSupport (a : ProductInput) : PolyList Int :=
  (a.a.flatten ++ a.b.flatten ++ a.c.flatten).flatten

def productMuls (mode : MulMode) (a : ProductInput) : Nat :=
  (productSupport a).foldl (fun n (e,_) => n + 1 + powMuls (code a.size.strides e))
    (if mode == .plain then 2 else 4)

def productWork (mode : MulMode) (i : Nat) : Nat :=
  let a := prepProduct mode i
  (productSupport a).length * (a.k+1) * budget.maxPackedBits + productMuls mode a * a.size.packedBits^2

-- Cost model (mode 2): traversal plus the quadratic bound per packed multiplication,
-- using the actual report N and the explicit operation count at each grid point.
setup_benchmark runTree i => treeWork i with prep := prepTree where {
  paramFloor := 1
  paramCeiling := treeAccepted.length
  paramSchedule := .custom ((List.range treeAccepted.length).map (·+1)).toArray
  maxSecondsPerCall := 10.0
  targetInnerNanos := 20000000
  signalFloorMultiplier := 1.0
}

-- Cost model (mode 2): direct support packing and two N-bit dot multiplications.
-- N is the inner report, and the count includes every square-and-multiply step.
setup_benchmark runPlain i => productWork .plain i with prep := prepPlain where {
  paramFloor := 1
  paramCeiling := (productAccepted .plain).length
  paramSchedule := .custom ((List.range (productAccepted .plain).length).map (·+1)).toArray
  maxSecondsPerCall := 10.0
  targetInnerNanos := 20000000
  signalFloorMultiplier := 1.0
}

-- Cost model (mode 2): support packing plus four outer multiplications, charged
-- at the report's larger N. No crossover or tight common GMP exponent is assumed.
setup_benchmark runPacked i => productWork .signedPacked i with prep := prepPacked where {
  paramFloor := 1
  paramCeiling := (productAccepted .signedPacked).length
  paramSchedule := .custom ((List.range (productAccepted .signedPacked).length).map (·+1)).toArray
  maxSecondsPerCall := 10.0
  targetInnerNanos := 20000000
  signalFloorMultiplier := 1.0
}

initialize treeDeclineInput : IO.Ref (List (Nat × Nat)) ← IO.mkRef treeDeclined

initialize productDeclineInput : IO.Ref (List (MulMode × Nat × Nat)) ←
  IO.mkRef ([MulMode.plain,.signedPacked].flatMap fun mode =>
    (productDeclined mode).map fun (k,d) => (mode,k,d))

/-- Every declined grid point runs preflight on runtime-supplied input. -/
@[noinline] def runTreeDeclines (_ : Unit) : IO UInt64 := do
  let points ← treeDeclineInput.get
  return hash (points.all fun (k,d) => !fits (treePlan k d))

@[noinline] def runProductDeclines (_ : Unit) : IO UInt64 := do
  let points ← productDeclineInput.get
  return hash (points.all fun (mode,k,d) => !fits (productPlan mode k d))

setup_fixed_benchmark runTreeDeclines where { maxSecondsPerCall := 10.0 }
setup_fixed_benchmark runProductDeclines where { maxSecondsPerCall := 10.0 }

open Lean

def metadata : IO Unit := do
  for (k,d) in grid do
    for family in ["tree","plain","signedPacked"] do
      let mode := if family == "plain" then MulMode.plain else .signedPacked
      let plan := if family == "tree" then treePlan k d else productPlan mode k d
      let .ok s := plan | throw (IO.userError "invalid benchmark shape")
      let accepted := s.accepts budget
      let (support,muls,result) := if !accepted then (0,0,0) else
        if family == "tree" then
          let i := (treeAccepted.idxOf (k,d))+1
          let a := prepTree i
          (nodes a.lhs+nodes a.rhs, treeMuls s.strides a.lhs+treeMuls s.strides a.rhs, runTree a)
        else
          let i := ((productAccepted mode).idxOf (k,d))+1
          let a := prepProduct mode i
          ((productSupport a).length, productMuls mode a, if mode == .plain then runPlain a else runPacked a)
      if accepted && result != 1 then throw (IO.userError "benchmark identity rejected")
      let row := Json.mkObj [
        ("family",toJson family),("atoms",toJson k),("degree",toJson d),("accepted",toJson accepted),
        ("digits",toJson s.digits),("digitBits",toJson s.digitBits),("packedBits",toJson s.packedBits),
        ("innerBits",toJson s.innerBits),("outerSlotBits",toJson s.outerSlotBits?),
        ("inputNodesOrSupport",toJson support),("integerMultiplications",toJson muls),
        ("gmpMultiplicationsUpper",toJson muls),("matrixInnerDimension",toJson (if family == "tree" then 0 else 2)),
        ("hash",toJson result.toNat)]
      IO.println row.compress

end Hex.Kronecker.Bench

def main (args : List String) : IO UInt32 := do
  if args == ["metadata"] then
    Hex.Kronecker.Bench.metadata
    return 0
  LeanBench.Cli.dispatch args
