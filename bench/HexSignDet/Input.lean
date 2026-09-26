/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet

namespace Hex.SignDetBench
open Hex.SignDet

def polyHash (p : DensePoly Rat) : UInt64 := hash p.toArray
private def endpointHash : Endpoint Rat → UInt64
  | .negInf => hash (0 : Nat)
  | .posInf => hash (2 : Nat)
  | .finite q => hash ((1 : Nat), q)

private def remainderHash (s : RemainderStep Rat) : UInt64 :=
  hash (s.leftScale, polyHash s.quotient, s.rightScale)

private def chainHash (c : SignedRemainderChain Rat) : UInt64 :=
  hash (c.chain.map polyHash, c.degrees, remainderHash c.initial,
    c.steps.map remainderHash, c.terminal.map fun (s, p) => (s, polyHash p))

private def certHash (c : TarskiCertificate Rat Rat Nat) : UInt64 :=
  hash (c.context, polyHash c.head, polyHash c.queryPoly,
    endpointHash c.lower, endpointHash c.upper,
    chainHash c.squarefree, chainHash c.remainders, c.lowerSigns, c.upperSigns,
    c.lowerVariations, c.upperVariations, c.value)

private def stepHash (s : ReductionStep Rat) : UInt64 :=
  hash (s.index, polyHash s.next, remainderHash s.witness)

private def reductionHash (r : Reduction Rat) : UInt64 :=
  hash (r.steps.map stepHash, polyHash r.result)

def matrixHash {n m : Nat} (a : Matrix Int n m) : UInt64 :=
  hash (a.rows.toArray.map fun r => r.toArray)

private def nodeHash (n : Node Rat Nat) : UInt64 :=
  hash (n.context, polyHash n.head, endpointHash n.lower, endpointHash n.upper,
    n.queries.map polyHash, n.size, n.system.rows.toArray, n.system.columns.toArray,
    n.system.counts.toArray, n.system.values.toArray, n.system.denominator,
    matrixHash n.system.inverse, n.moments.toArray.map certHash,
    n.reductions.toArray.map fun r => r.map reductionHash,
    n.preparation.map fun p => p.steps.map stepHash,
    n.basis.rank, n.basis.rows.toArray.map Fin.val, n.basis.cols.toArray.map Fin.val,
    n.basis.denom, matrixHash n.basis.adj)

private def treeHash : Replay Rat Nat → UInt64
  | .leaf n => hash ((0 : Nat), nodeHash n)
  | .split n l r => hash ((1 : Nat), nodeHash n, treeHash l, treeHash r)

private def graphHash (d : Dag Rat Nat) : UInt64 :=
  hash (d.root, d.entries.map fun e => (nodeHash e.node, e.children))

private def domainHash (d : Sturm.PreparedDomain Rat) : UInt64 :=
  hash (polyHash d.head, endpointHash d.lower, endpointHash d.upper, chainHash d.squarefree)

structure Input where
  head : DensePoly Rat
  queries : List (DensePoly Rat)
  domain : Option (Sturm.PreparedDomain Rat)
  tree : Option (Replay Rat Nat)
  graph : Option (Dag Rat Nat)

instance : Hashable Input where
  hash i := hash (polyHash i.head, i.queries.map polyHash,
    i.domain.map domainHash, i.tree.map treeHash, i.graph.map graphHash)

def entries {r : Nat} (s : System r) : List (List Int × Int) :=
  s.positive.map fun i => (s.columns[i], s.counts[i])

/-- This fixture-specific graph uses equal left/right query blocks. Every
result is independently checked before use; it is not a general encoder. -/
private def sharedEntries : Replay Rat Nat → Array (Dag.Entry Rat Nat)
  | .leaf n => #[⟨n, none⟩]
  | .split n l _ =>
    let nodes := sharedEntries l
    nodes.push ⟨n, some (nodes.size - 1, nodes.size - 1)⟩

private def x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]

/-- Preparation records no evidence on an invalid fixture. Inspection and
export validation reject that result. Scientific parameters are positive powers
of two; the harness's zero/one smoke inputs are handled explicitly. -/
def input (s : Nat) : Input :=
  let p := x * x - 1
  let qs := List.replicate s x
  match Sturm.prepare Sturm.orderSign p .negInf .posInf with
  | none => ⟨p, qs, none, none, none⟩
  | some domain =>
    match buildPrepared (10377 : Nat) domain qs, buildPrepared (10377 : Nat) domain qs false with
    | .ok reduced, .ok direct =>
      let expected := if s == 0 then [([], (2 : Int))]
        else [(List.replicate s (-1), (1 : Int)), (List.replicate s 1, 1)]
      let nodes := sharedEntries reduced.val
      let graph : Dag Rat Nat := ⟨nodes, nodes.size - 1⟩
      if entries reduced.val.node.system != expected || entries direct.val.node.system != expected ||
          !graph.check Sturm.orderSign 10377 p .negInf .posInf qs then
        ⟨p, qs, none, none, none⟩
      else ⟨p, qs, some domain, some reduced.val, some graph⟩
    | _, _ => ⟨p, qs, none, none, none⟩

def nodes : Replay Rat Nat → List (Node Rat Nat)
  | .leaf n => [n]
  | .split n l r => n :: nodes l ++ nodes r

end Hex.SignDetBench
