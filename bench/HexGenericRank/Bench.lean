/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRank
import HexMvPoly.Kernel
import Init.Data.List.Control
import Lean.Data.Json
import LeanBench

/-!
The symbolic family uses the full Cartesian product of dimensions 2/4/8,
variables 1/2/4/8, degree 1/2/4 and support caps 1/4/16, at full and low rank.
Mode 3: each fixed workload has its own absolute ceiling; these ladders do
not assert a common cubic cost model. The upper-triangular full-rank inputs
and factorised low-rank inputs have bounded realised minor support. They
measure these structured inputs, not worst-case expression swell.

Comparator: no-comparable-surface-in-named-comparator. python-flint has no
multivariate polynomial matrix surface; SymPy is a conformance oracle only.

Fixed registrations use lean-bench's registration API so preparation happens
before the runner's timer. Each checker caches its own certificate, lazily on
first use; registering the Cartesian product does not produce certificates.
-/

namespace Hex.GenericRankBench

open Hex Hex.Matrix Lean

abbrev Poly (k : Nat) := MvPoly k Int Mono.grevlex

structure Workload where
  n : Nat
  k : Nat
  degree : Nat
  support : Nat
  low : Bool
  deriving Repr, ToJson

def Workload.label (w : Workload) : String :=
  s!"{if w.low then "low" else "full"}.n{w.n}.k{w.k}.d{w.degree}.s{w.support}"

def workloads : List Workload :=
  [2, 4, 8].flatMap fun n =>
  [1, 2, 4, 8].flatMap fun k =>
  [1, 2, 4].flatMap fun degree =>
  [1, 4, 16].flatMap fun support =>
  [false, true].map fun low => ⟨n, k, degree, support, low⟩

/-- Exponent vectors of total degree at most the budget. -/
def exponents : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, d => (List.range (d + 1)).flatMap fun e => (exponents k (d - e)).map (e :: ·)

def polynomial (w : Workload) (salt : Nat) : Poly w.k :=
  MvPoly.Kernel.denote ((exponents w.k w.degree).reverse.take w.support |>.zipIdx |>.map
    fun (e, j) => (e, ((1 + (salt + j) % 5 : Nat) : Int)))

/-- Full rank comes from an upper-triangular block with nonzero polynomial
first diagonal. Low rank is the product of a full-column-rank factor and a
full-row-rank factor, both with a visible nonsingular leading minor. -/
def input (w : Workload) : Matrix (Poly w.k) w.n w.n :=
  if w.low then
    let r := w.n / 2
    let L : Matrix (Poly w.k) w.n r := Matrix.ofFn fun i j =>
      if i.val < r then if i.val = j.val then
        if i.val = 0 then polynomial w 0 else 1 else 0
      else if j.val = 0 then polynomial w (i.val + 1) else 0
    let R : Matrix (Poly w.k) r w.n := Matrix.ofFn fun i j =>
      if i.val = j.val then 1 else if j.val ≥ r then polynomial w (i.val + j.val) else 0
    L * R
  else Matrix.ofFn fun i j =>
    if i.val = 0 then polynomial w j.val else if i = j then 1 else 0

def expected (w : Workload) : Nat := if w.low then w.n / 2 else w.n

def termCount (A : Matrix (Poly k) n m) : Nat :=
  A.rows.toList.foldl (fun acc row => acc + row.toList.foldl (fun s p => s + p.termCount) 0) 0

def peakSupport (A : Matrix (Poly k) n m) : Nat :=
  A.rows.toList.foldl (fun acc row => row.toList.foldl (fun s p => max s p.termCount) acc) 0

def degree (p : Poly k) : Nat :=
  p.termsList.foldl (fun d t => max d (t.1.toList.foldl (· + ·) 0)) 0

def polyJson (p : Poly k) : Json :=
  toJson (p.termsList.map fun (e, c) => Json.arr #[toJson e.toList, toJson c])

def certJson (c : RankCert (Poly k) n m) : Json := Json.mkObj [
  ("rank", toJson c.rank), ("rows", toJson (c.rows.toList.map Fin.val)),
  ("cols", toJson (c.cols.toList.map Fin.val)), ("denom", polyJson c.denom),
  ("adj", toJson (c.adj.rows.toList.map fun row => row.toList.map polyJson))]

/-- State support on the producer's actual column-step sequence. This untimed
instrumentation includes both passes, including the augmented identity block. -/
def passSupport (A : Matrix (Poly k) n m) : Nat :=
  ((List.finRange m).foldl (fun (state, peak) j =>
    let next := reduceStep Hex.exactDiv state j
    (next, max peak (max next.denom.termCount (peakSupport next.matrix))))
      (initialForm A, peakSupport A)).2

structure Prepared (w : Workload) where
  matrix : Matrix (Poly w.k) w.n w.n
  cert : RankCert (Poly w.k) w.n w.n

/-- Cached preparation is outside the measured loop. -/
def prepared (w : Workload) (cache : IO.Ref (Option (Prepared w))) : IO (Prepared w) := do
  if let some p ← cache.get then return p
  let A := input w
  let c := GenericRank.genericCert A
  unless c.rank == expected w && checkRank A c do
    throw <| IO.userError s!"invalid symbolic fixture {w.label}"
  let p := { matrix := A, cert := c }
  cache.set (some p)
  return p

def config (w : Workload) (checker : Bool) : LeanBench.FixedBenchmarkConfig := {
  repeats := 5
  maxSecondsPerCall := 5.0
  minTotalSeconds := 0.001
  expectedHash := if checker then some (hash true) else none
  tags := #["symbolic", if w.low then "low" else "full", if checker then "checker" else "producer"] }

/-- Register a producer and a compiled checker separately at every fixed rung. -/
def registerAll : IO Unit := do
  for w in workloads do
    let matrixCache ← IO.mkRef (none : Option (Matrix (Poly w.k) w.n w.n))
    let getMatrix : IO (Matrix (Poly w.k) w.n w.n) := do
      if let some A ← matrixCache.get then return A
      let A := input w
      matrixCache.set (some A)
      return A
    let certCache ← IO.mkRef (none : Option (Prepared w))
    for checker in [false, true] do
      let name := (s!"Hex.GenericRankBench.{w.label}.{if checker then "checker" else "producer"}").toName
      let call : IO (Unit → IO UInt64) := do
        if checker then
          let p ← prepared w certCache
          return fun _ => return hash (checkRank p.matrix p.cert)
        else
          let A ← getMatrix
          return fun _ => do
            let c := GenericRank.genericCert A
            unless c.rank == expected w do throw <| IO.userError "incorrect generic rank"
            return hash (c.rank, c.denom.termCount, termCount c.adj)
      LeanBench.registerFixed { name, hashable := true, config := config w checker } fun count => do
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

def statistics : IO Unit := do
  for w in workloads do
    let A := input w
    let c := GenericRank.genericCert A
    unless c.rank == expected w && checkRank A c do
      throw <| IO.userError s!"invalid symbolic fixture {w.label}"
    let B := selectedSubmatrix A c.rows c.cols
    let row := Json.mkObj [
      ("workload", toJson w), ("label", toJson w.label), ("rank", toJson c.rank),
      ("entry_support", toJson (peakSupport A)), ("entry_terms", toJson (termCount A)),
      ("denom_terms", toJson c.denom.termCount), ("denom_degree", toJson (degree c.denom)),
      ("adj_terms", toJson (termCount c.adj)), ("certificate_bytes", toJson (certJson c).compress.utf8ByteSize),
      ("intermediate_support", toJson (max (passSupport A) (passSupport (augmentIdentity B))))]
    IO.println row.compress

end Hex.GenericRankBench

def main (args : List String) : IO UInt32 := do
  if args == ["stats"] then
    Hex.GenericRankBench.statistics
    return 0
  Hex.GenericRankBench.registerAll
  LeanBench.Cli.dispatch args
