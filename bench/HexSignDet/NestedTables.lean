/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Input
import HexRationalFn
import HexOrderedFn.Infinitesimal
import LeanBench
import Lean.Data.Json

namespace Hex.SignDetBench.NestedTables
open Hex.SignDet

private structure Coefficients where
  Carrier : Type
  field : Lean.Grind.Field Carrier
  equality : DecidableEq Carrier
  sign : Carrier → Int
  fingerprint : Carrier → UInt64
  encode : Carrier → Lean.Json
  epsilon : Carrier

private def coefficients : Nat → Coefficients
  | 0 => ⟨Rat, inferInstance, inferInstance, OrderedFn.orderSign, hash,
      fun q => Lean.toJson #[q.num, (q.den : Int)], 1⟩
  | depth + 1 =>
    let base := coefficients depth
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
      epsilon := RationalFn.X }

section Hashes
variable {E : Type} [Lean.Grind.Field E] [DecidableEq E] [Hashable E] [NatCast E]
def polyHash (p : DensePoly E) : UInt64 := hash p.toArray
private def endpointHash : Endpoint E → UInt64
  | .negInf => hash (0 : Nat)
  | .posInf => hash (2 : Nat)
  | .finite q => hash ((1 : Nat), q)

private def remainderHash (s : RemainderStep E) : UInt64 :=
  hash (s.leftScale, polyHash s.quotient, s.rightScale)

private def chainHash (c : SignedRemainderChain E) : UInt64 :=
  hash (c.chain.map polyHash, c.degrees, remainderHash c.initial,
    c.steps.map remainderHash, c.terminal.map fun (s, p) => (s, polyHash p))

private def certHash (c : TarskiCertificate E E Nat) : UInt64 :=
  hash (c.context, polyHash c.head, polyHash c.queryPoly,
    endpointHash c.lower, endpointHash c.upper,
    chainHash c.squarefree, chainHash c.remainders, c.lowerSigns, c.upperSigns,
    c.lowerVariations, c.upperVariations, c.value)

private def stepHash (s : ReductionStep E) : UInt64 :=
  hash (s.index, polyHash s.next, remainderHash s.witness)

private def reductionHash (r : Reduction E) : UInt64 :=
  hash (r.steps.map stepHash, polyHash r.result)

def matrixHash {n m : Nat} (a : Matrix Int n m) : UInt64 :=
  hash (a.rows.toArray.map fun r => r.toArray)

private def nodeHash (n : Node E Nat) : UInt64 :=
  hash (n.context, polyHash n.head, endpointHash n.lower, endpointHash n.upper,
    n.queries.map polyHash, n.size, n.system.rows.toArray, n.system.columns.toArray,
    n.system.counts.toArray, n.system.values.toArray, n.system.denominator,
    matrixHash n.system.inverse, n.moments.toArray.map certHash,
    n.reductions.toArray.map fun r => r.map reductionHash,
    n.preparation.map fun p => p.steps.map stepHash,
    n.basis.rank, n.basis.rows.toArray.map Fin.val, n.basis.cols.toArray.map Fin.val,
    n.basis.denom, matrixHash n.basis.adj)

private def treeHash : Replay E Nat → UInt64
  | .leaf n => hash ((0 : Nat), nodeHash n)
  | .split n l r => hash ((1 : Nat), nodeHash n, treeHash l, treeHash r)

private def graphHash (d : Dag E Nat) : UInt64 :=
  hash (d.root, d.entries.map fun e => (nodeHash e.node, e.children))

private def domainHash (d : Sturm.PreparedDomain E) : UInt64 :=
  hash (polyHash d.head, endpointHash d.lower, endpointHash d.upper, chainHash d.squarefree)


end Hashes

private structure Data (E : Type) [Lean.Grind.Field E] [DecidableEq E] [NatCast E] where
  head : DensePoly E
  queries : List (DensePoly E)
  domain : Sturm.PreparedDomain E
  tree : Replay E Nat
  graph : Dag E Nat

/-- A genuine typed field and supplied evidence, rather than a callback closure.
The complete polynomial/domain/tree/graph fingerprint is computed in preparation. -/
private structure Input where
  coefficients : Coefficients
  data :
    letI := coefficients.field
    letI := coefficients.equality
    letI : NatCast coefficients.Carrier := Lean.Grind.Semiring.natCast
    Data coefficients.Carrier
  fingerprint : UInt64

private instance : Hashable Input := ⟨Input.fingerprint⟩

private def input (depth size : Nat) : Option Input :=
  let k := coefficients depth
  letI := k.field
  letI := k.equality
  letI : Hashable k.Carrier := ⟨k.fingerprint⟩
  letI : NatCast k.Carrier := Lean.Grind.Semiring.natCast
  let p : DensePoly k.Carrier := DensePoly.ofCoeffs #[0, 1]
  let qs : List (DensePoly k.Carrier) := List.replicate size (DensePoly.C k.epsilon)
  match Sturm.prepare k.sign p .negInf .posInf with
  | none => none
  | some domain =>
    match buildPrepared (E := k.Carrier) (10377 : Nat) domain qs with
    | .error _ => none
    | .ok built =>
      let tree : Replay k.Carrier Nat := built.val
      let graph : Dag k.Carrier Nat := Dag.encode tree
      let expected := [(List.replicate size (1 : Int), (1 : Int))]
      if entries tree.node.system != expected ||
          !tree.check k.sign 10377 p .negInf .posInf qs ||
          !graph.check k.sign 10377 p .negInf .posInf qs then none
      else
        let fingerprint := hash (depth, polyHash p, qs.map polyHash,
          domainHash domain, treeHash tree, graphHash graph)
        some ⟨k, ⟨p, qs, domain, tree, graph⟩, fingerprint⟩

/-- Build using the shared prepared queries and actual BKR producer.
Polynomial/field construction and the input's reference evidence are outside timing. -/
@[noinline] private def produce (argument : Option Input) : Option UInt64 :=
  match argument with
  | none => none
  | some i =>
    letI := i.coefficients.field
    letI := i.coefficients.equality
    letI : Hashable i.coefficients.Carrier := ⟨i.coefficients.fingerprint⟩
    letI : NatCast i.coefficients.Carrier := Lean.Grind.Semiring.natCast
    match buildPrepared (10377 : Nat) i.data.domain i.data.queries with
    | .error _ => none
    | .ok built => some (hash (entries built.val.node.system))

@[noinline] private def checkTree (i : Option Input) : Bool :=
  match i with
  | none => false
  | some i =>
    letI := i.coefficients.field
    letI := i.coefficients.equality
    letI : NatCast i.coefficients.Carrier := Lean.Grind.Semiring.natCast
    i.data.tree.check i.coefficients.sign 10377 i.data.head
      .negInf .posInf i.data.queries

@[noinline] private def checkGraph (i : Option Input) : Bool :=
  match i with
  | none => false
  | some i =>
    letI := i.coefficients.field
    letI := i.coefficients.equality
    letI : NatCast i.coefficients.Carrier := Lean.Grind.Semiring.natCast
    i.data.graph.check i.coefficients.sign 10377 i.data.head
      .negInf .posInf i.data.queries

/-
For each fixed coefficient depth, P=X has one root and each query is the
same positive constant. Every parent retains one sign column and the constant
row; leaves have three moment rows. Thus every polynomial degree, coefficient
representation and matrix dimension is bounded independently of s. There are
2s-1 tree nodes and balanced arity volume s*(log2(s)+1). Constructing/checking
the literal length-k query/sign/exponent lists costs O(k) at a node, giving
Theta(s log s). Graph sharing reduces repeated child entries but its root
still contains length-s lists; this registration makes no tight graph model.
Depth is a separately fixed facet, not a fitted arithmetic exponent.
-/

def input1 (size : Nat) : Option Input := input 1 size
def input2 (size : Nat) : Option Input := input 2 size

@[noinline] def runProduce1 (i : Option Input) := produce i

setup_benchmark runProduce1 s => s * (Nat.log2 s + 1)
  with prep := input1
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    paramFloor := 8
    paramCeiling := 128
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 300
  }

@[noinline] def runTree1 (i : Option Input) := checkTree i

setup_benchmark runTree1 s => s * (Nat.log2 s + 1)
  with prep := input1
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    paramFloor := 8
    paramCeiling := 128
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 300
  }

@[noinline] def runProduce2 (i : Option Input) := produce i

setup_benchmark runProduce2 s => s * (Nat.log2 s + 1)
  with prep := input2
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    paramFloor := 8
    paramCeiling := 128
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 300
  }

@[noinline] def runTree2 (i : Option Input) := checkTree i

setup_benchmark runTree2 s => s * (Nat.log2 s + 1)
  with prep := input2
  where {
    paramSchedule := .custom #[8, 16, 32, 64, 128]
    paramFloor := 8
    paramCeiling := 128
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 300
  }

private def nodes {E : Type} [Zero E] [DecidableEq E] : Replay E Nat → List (Node E Nat)
  | .leaf n => [n]
  | .split n l r => n :: nodes l ++ nodes r

private def inventory (depth size : Nat) (i : Input) : Lean.Json :=
  letI := i.coefficients.field
  letI := i.coefficients.equality
  letI : NatCast i.coefficients.Carrier := Lean.Grind.Semiring.natCast
  let ns := nodes i.data.tree
  let table := entries i.data.tree.node.system
  Lean.Json.mkObj [
    ("depth", Lean.toJson depth), ("queries", Lean.toJson size),
    ("headDegree", Lean.toJson i.data.head.natDegree),
    ("queryDegree", Lean.toJson (i.data.queries.foldl (fun n p => max n p.natDegree) 0)),
    ("rootCount", Lean.toJson (i.data.tree.node.system.counts.toList.foldl (· + ·) 0)),
    ("realizedSupport", Lean.toJson i.data.tree.node.system.support.length),
    ("head", Lean.Json.arr (i.data.head.toArray.map i.coefficients.encode)),
    ("queryPolynomials", Lean.Json.arr (i.data.queries.toArray.map
      fun p => Lean.Json.arr (p.toArray.map i.coefficients.encode))),
    ("table", Lean.toJson table),
    ("treeNodes", Lean.toJson ns.length),
    ("momentSlots", Lean.toJson (ns.foldl (fun n node => n + node.size) 0)),
    ("maxMatrixSize", Lean.toJson (ns.foldl (fun n node => max n node.size) 0)),
    ("coefficient", i.coefficients.encode i.coefficients.epsilon),
    ("graphNodes", Lean.toJson i.data.graph.entries.size),
    ("graphEdges", Lean.toJson (i.data.graph.entries.foldl
      (fun n e => n + if e.children.isSome then 2 else 0) (0 : Nat))),
    ("inputHash", Lean.toJson (hash (some i)).toNat),
    ("productionResultHash", Lean.toJson (hash (some (hash table))).toNat),
    ("replayResultHash", Lean.toJson (hash true).toNat)]

/-- Exact one-root tables and supplied tree/graph checks before measurement.
The coefficient encoding shows the actual positive newest infinitesimal. -/
def inspectFor (depths sizes : Array Nat) : IO UInt32 := do
  for depth in depths do
    for size in sizes do
      let some i := input depth size | throw (IO.userError "nested table preparation failed")
      letI := i.coefficients.field
      letI := i.coefficients.equality
      letI : NatCast i.coefficients.Carrier := Lean.Grind.Semiring.natCast
      let expected := some (hash [(List.replicate size (1 : Int), (1 : Int))])
      unless produce (some i) == expected && checkTree (some i) && checkGraph (some i) do
        throw (IO.userError "nested table callback failed")
      IO.println (inventory depth size i).compress
      (← IO.getStdout).flush
  return 0

end Hex.SignDetBench.NestedTables
