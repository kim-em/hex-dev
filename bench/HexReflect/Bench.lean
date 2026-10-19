/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexReflect
import LeanBench

/-!
Benchmark registrations for `hex-reflect`.

The registrations cover the three SPEC families with pure inputs, so the
executable stays independent of an elaboration environment:

* batch sharing: interning a batch of `n` canonical atoms, each repeated
  across the batch, through the same pointer-keyed atom map the session uses,
  `O(n)` expected hash-map operations;
* characteristic-aware normalization: converting a product of `n` distinct
  linear factors both without characteristic evidence and modulo a small
  characteristic, `O(2^n)` output terms with the reference model at the
  exponent `n`;
* proof reconstruction: quoting the converted term list of a dense
  two-variable polynomial with `n` terms as the `Lean.Expr` literal used by
  the interpretation proof, `O(n)` syntax nodes.

Input construction is hoisted through `prep`. Timed targets return structural
hashes of their outputs so result traversal stays within the declared cost.
-/

namespace Hex.ReflectBench

open Hex Hex.Reflect
open Lean.Grind.CommRing (Expr)

/-! # Batch sharing -/

/-- A batch of expressions over `n` shared atoms. Every input is a distinct
`Lean.Expr` object built from the shared atom objects, so pointer-keyed
interning sees repeated atoms. -/
structure SharingInput where
  n : Nat
  atoms : Array Lean.Expr
  batch : Array (Array Lean.Expr)

instance : Hashable SharingInput where
  hash input := mixHash (hash input.n) (hash input.atoms.size)

def prepSharing (n : Nat) : SharingInput :=
  let atoms := (Array.range n).map fun i => Lean.mkFVar ⟨Lean.Name.mkNum `atom i⟩
  let batch := (Array.range n).map fun i =>
    (Array.range n).map fun j => atoms[(i + j) % n]!
  { n, atoms, batch }

/-- Intern every atom occurrence of the batch, returning the number of
distinct identifiers and a hash of the assignment. -/
def runSharing (input : SharingInput) : UInt64 := Id.run do
  let mut index : AtomMap := {}
  let mut acc : UInt64 := 0
  for row in input.batch do
    for e in row do
      let i ← match index[({ expr := e } : Lean.Meta.Sym.ExprPtr)]? with
        | some i => pure i
        | none =>
          let i := index.size
          index := index.insert { expr := e } i
          pure i
      acc := mixHash acc (hash i)
  return mixHash acc (hash index.size)

/-! # Characteristic-aware normalization -/

/-- The product of `n` distinct linear forms `x_i + 1` over `n` variables. -/
def prepProduct (n : Nat) : RingExpr :=
  (List.range n).foldl (fun acc i => .mul acc (.add (.var i) (.num 1))) (.num 1)

private def termsHash {n : Nat} (ts : List (Mono n × Int)) : UInt64 :=
  ts.foldl (fun acc t => mixHash acc (mixHash (hash t.1.toArray) (hash t.2))) (hash ts.length)

/-- Convert without characteristic evidence. -/
def runConvert (e : RingExpr) : UInt64 :=
  match convertTerms? (RingExpr.varBound e) none e with
  | some ts => termsHash ts
  | none => 0

/-- Convert modulo the characteristic `3`. -/
def runConvertChar3 (e : RingExpr) : UInt64 :=
  match convertTerms? (RingExpr.varBound e) (some 3) e with
  | some ts => termsHash ts
  | none => 0

/-! # Proof reconstruction -/

/-- A converted term list over two variables. -/
structure TermsInput where
  n : Nat
  terms : List (Mono 2 × Int)

instance : Hashable TermsInput where
  hash input := mixHash (hash input.n) (termsHash input.terms)

/-- The dense two-variable polynomial with `n` terms of the form
`(i + 1) * x^i * y^(n - i)`. -/
def prepTerms (n : Nat) : TermsInput :=
  { n
    terms := (List.range n).map fun i =>
      (Mono.mul (Mono.scale i (Mono.unit 0)) (Mono.scale (n - i) (Mono.unit 1)),
        Int.ofNat (i + 1)) }

/-- Quote the term list as the `Lean.Expr` literal used by proof
reconstruction, returning its hash. -/
def runQuoteTerms (input : TermsInput) : UInt64 :=
  hash (quoteTerms 2 input.terms)

/- Cost model: each atom occurrence is one pointer hash and one map lookup,
so a batch of `n` rows of `n` occurrences costs `O(n²)` operations. -/
setup_benchmark runSharing n => n ^ 2
  with prep := prepSharing
  where {
    paramFloor := 8
    paramCeiling := 256
    paramSchedule := .custom #[8, 16, 32, 64, 128, 256]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: expanding `n` linear factors produces `2^n` monomials, and the
sorted-list product inserts each of them at a cost linear in the running
term count, so the reference model is `4^n`. -/
setup_benchmark runConvert n => 4 ^ n
  with prep := prepProduct
  where {
    paramFloor := 4
    paramCeiling := 12
    paramSchedule := .custom #[4, 6, 8, 10, 12]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: the same expansion with every coefficient reduced modulo `3`;
no coefficient of this family vanishes, so the term count is unchanged. -/
setup_benchmark runConvertChar3 n => 4 ^ n
  with prep := prepProduct
  where {
    paramFloor := 4
    paramCeiling := 12
    paramSchedule := .custom #[4, 6, 8, 10, 12]
    maxSecondsPerCall := 10.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

/- Cost model: each term quotes to a constant number of syntax nodes, so the
literal has `O(n)` nodes. -/
setup_benchmark runQuoteTerms n => n
  with prep := prepTerms
  where {
    paramFloor := 16
    paramCeiling := 4096
    paramSchedule := .custom #[16, 64, 256, 1024, 4096]
    maxSecondsPerCall := 6.0
    targetInnerNanos := 200000000
    signalFloorMultiplier := 1.0
  }

end Hex.ReflectBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
