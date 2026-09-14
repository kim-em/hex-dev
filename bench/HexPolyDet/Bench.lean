/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDet
import Lean.Data.Json
import LeanBench

/-!
Mode 3: each feasible (dimension, atoms, degree, support) workload has a
fixed ceiling, not one cubic model across support and degree changes.
The dense integer matrix (3 on the diagonal, 1 elsewhere) is row-scaled by
sparse polynomials. The exceptional 2x2/four-variable/linear monomial case
uses four independent entries. This is structured support-growth evidence,
not independent random polynomial entries or worst-case complexity.
Comparator: no-comparable-surface-in-named-comparator; SymPy is the oracle.
-/

namespace Hex.PolyDetBench
open Hex.Matrix Lean

abbrev Poly (k : Nat) := MvPoly k Int Mono.grevlex

structure Workload where
  n : Nat
  k : Nat
  degree : Nat
  support : Nat
  deriving Repr, ToJson

def Workload.label (w : Workload) := s!"n{w.n}.k{w.k}.d{w.degree}.s{w.support}"

def exponents : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, d => (List.range (d + 1)).flatMap fun e => (exponents k (d - e)).map (e :: ·)

def candidates : List Workload :=
  [2, 4, 8].flatMap fun n => [1, 2, 4].flatMap fun k =>
  [1, 2, 4].flatMap fun degree => [1, 4, 16].map fun support => ⟨n, k, degree, support⟩

def workloads := candidates.filter fun w => w.support ≤ (exponents w.k w.degree).length

def unitExp (k i : Nat) := (List.range k).map fun j => if i == j then 1 else 0

def polynomial (w : Workload) (row : Nat) : Poly w.k :=
  let lead := if w.n == 2 && w.k == 4 && w.support == 1 && w.degree > 1 then
      (List.range w.k).map fun j => if j == 2 * row then w.degree - 1 else if j == 2 * row + 1 then 1 else 0
    else (unitExp w.k (row % w.k)).map (· * w.degree)
  let preferred := lead :: ((List.range w.k).map fun j => unitExp w.k ((row + j) % w.k))
  let terms := ((preferred ++ exponents w.k w.degree).eraseDups.take w.support).zipIdx.map
    fun (m, j) => (m, (1 + (row + j) % 3 : Int))
  MvPoly.Kernel.denote terms

def input (w : Workload) : Matrix (Poly w.k) w.n w.n :=
  Matrix.ofFn fun i j =>
    if w.n == 2 && w.k == 4 && w.degree == 1 && w.support == 1 then
      MvPoly.Kernel.denote [(unitExp w.k (2 * i.val + j.val), 1)]
    else MvPoly.C (if i.val == j.val then 3 else 1) * polynomial w i.val

structure Prepared (w : Workload) where
  matrix : Matrix (Poly w.k) w.n w.n
  rows : List (List (MvPoly.Kernel.PolyList Int))
  witness : DetWitness (MvPoly.Kernel.PolyList Int)

def prepare (w : Workload) : IO (Prepared w) := do
  let A := input w
  let c ← match PolyDet.polyDetWitness A with
    | .ok c => pure c
    | .error msg => throw (IO.userError msg)
  return {
    matrix := A
    rows := A.rows.toList.map (fun row => row.toList.map PolyDet.toList)
    witness := c.map PolyDet.toList }

def registerAll : IO Unit := do
  for w in workloads do
    let cache ← IO.mkRef (none : Option (Prepared w))
    let prepared : IO (Prepared w) := do
      if let some p ← cache.get then return p
      let p ← prepare w
      cache.set (some p)
      return p
    for checker in [false, true] do
      let name := (s!"Hex.PolyDetBench.{w.label}.{if checker then "checker" else "producer"}").toName
      let config : LeanBench.FixedBenchmarkConfig := {
        repeats := 5, maxSecondsPerCall := 5.0, minTotalSeconds := 0.001,
        expectedHash := if checker then some (hash true) else none,
        tags := #["symbolic", if checker then "checker" else "producer"] }
      let call : IO (Unit → IO UInt64) := do
        let p ← prepared
        if checker then
          return fun _ => pure (hash (checkDetPolyList (PolyDet.ops w.k) w.n p.rows p.witness))
        else
          let rows := p.matrix.rows.toList.map (·.toList)
          return fun _ => do
            match detWitnessWith Hex.exactDiv w.n (fun _ _ => true) rows with
            | .error msg => throw (IO.userError msg)
            | .ok c => return hash c.value.termCount
      LeanBench.registerFixed { name, hashable := true, config } fun count => do
        let f ← call
        let start ← IO.monoNanosNow
        let mut first := none
        for i in [:count] do
          let h ← f ()
          if i == 0 then first := some h
          LeanBench.blackBox h
        return ((← IO.monoNanosNow) - start, first)
      LeanBench.registerKernel name fun _ => do
        let f ← call
        LeanBench.kernelLoop f id true true

end Hex.PolyDetBench

def main (args : List String) : IO UInt32 := do
  Hex.PolyDetBench.registerAll
  if args == ["verify-ci"] then
    LeanBench.Cli.dispatch ["verify",
      "Hex.PolyDetBench.n2.k1.d1.s1.producer", "Hex.PolyDetBench.n2.k1.d1.s1.checker",
      "Hex.PolyDetBench.n4.k2.d2.s4.producer", "Hex.PolyDetBench.n4.k2.d2.s4.checker"]
  else LeanBench.Cli.dispatch args
