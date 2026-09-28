/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Small

namespace Hex.SignDetBench.Joint
open Hex.SignDet

abbrev Root := Descriptor Rat Nat Sturm.orderSign 10377

/-- Keep the actual source descriptors and both joint tables available for
separate completion, comparison, construction and replay measurements. -/
structure Case where
  leftPartial : Root
  rightPartial : Root
  leftFull : Root
  rightFull : Root
  left : Input
  right : Input
  leftDirect : Replay Rat Nat
  rightDirect : Replay Rat Nat
  order : Ordering

private def signs (qs : List (DensePoly Rat)) (x : Rat) : List Int :=
  qs.map fun q => Sturm.orderSign (q.eval x)

/-- For odd n, the sources X^n-1 and X^n+1 have unique real roots 1 and -1.
The actual gcd is -2, so the common head is -(X^(2n)-1)/2. Each re-encoding uses its own list of
2n target derivatives followed by the n+1 source constraints: 3n+1 queries.
The sources share derivative vectors but their defining equations differ. -/
def input (n : Nat) : Option Case := do
  if n < 3 || n % 2 != 1 then none else do
    let x : DensePoly Rat := DensePoly.monomial n 1
    let p := x - 1
    let q := x + 1
    let raw := fun head => (⟨10377, head, .negInf, .posInf, [n], [1]⟩ : RawDescriptor Rat Nat)
    let .ok (.ok l) := Descriptor.build Sturm.orderSign 10377 (raw p) | none
    let .ok (.ok r) := Descriptor.build Sturm.orderSign 10377 (raw q) | none
    let .ok lc := l.buildCompletion | none
    let .ok rc := r.buildCompletion | none
    let lf := lc.descriptor
    let rf := rc.descriptor
    if lf.raw.signs != signs lf.raw.queries 1 || rf.raw.signs != signs rf.raw.queries (-1) then none else do
      let .ok comparison := lf.buildComparison rf | none
      let h := DensePoly.scale (-1/2 : Rat) (DensePoly.monomial (2*n) (1 : Rat) - 1)
      if comparison.common.head != h || comparison.common.factor != DensePoly.C (-2 : Rat) ||
          comparison.order != .gt ||
          p.eval 1 != 0 || q.eval (-1) != 0 || h.eval 1 != 0 || h.eval (-1) != 0 then none else do
        let domain ← Sturm.prepare Sturm.orderSign h .negInf .posInf
        let target : RawDescriptor Rat Nat := ⟨10377, h, .negInf, .posInf, [], []⟩
        let lqs := (target.full []).queries ++ lf.raw.constraints
        let rqs := (target.full []).queries ++ rf.raw.constraints
        let lt := comparison.leftEncoding.evidence
        let rt := comparison.rightEncoding.evidence
        let .ok ld := buildPrepared (10377 : Nat) domain lqs false | none
        let .ok rd := buildPrepared (10377 : Nat) domain rqs false | none
        let expected := fun qs => [(signs qs 1, (1 : Int)), (signs qs (-1), 1)]
        if lqs.length != 3*n+1 || rqs.length != 3*n+1 ||
            lt.node.queries != lqs || rt.node.queries != rqs ||
            entries lt.node.system != expected lqs || entries rt.node.system != expected rqs ||
            entries ld.val.node.system != expected lqs || entries rd.val.node.system != expected rqs ||
            comparison.leftEncoding.target.raw.signs != signs (target.full []).queries 1 ||
            comparison.rightEncoding.target.raw.signs != signs (target.full []).queries (-1) then none else
          some ⟨l, r, lf, rf, ⟨h, lqs, some domain, some lt, some (Dag.encode lt)⟩,
            ⟨h, rqs, some domain, some rt, some (Dag.encode rt)⟩, ld.val, rd.val, comparison.order⟩

private def bits (z : Int) : Nat := if z == 0 then 0 else z.natAbs.log2 + 1

private def ratBits (q : Rat) : Nat := max (bits q.num) (q.den.log2 + 1)
private def polyBits (p : DensePoly Rat) : Nat :=
  p.toArray.foldl (fun k q => max k (ratBits q)) 0
private def stepBits (s : RemainderStep Rat) : Nat :=
  max (polyBits s.quotient) (max (ratBits s.leftScale) (ratBits s.rightScale))
private def chainBits (c : SignedRemainderChain Rat) : Nat :=
  max (c.chain.foldl (fun k p => max k (polyBits p)) 0)
    (max (c.steps.foldl (fun k s => max k (stepBits s)) (stepBits c.initial))
      ((c.terminal.map (fun (s, q) => max (ratBits s) (polyBits q))).getD 0))
private def witnessBits (tree : Replay Rat Nat) : Nat := (nodes tree).foldl (fun k n =>
  let k := n.moments.toList.foldl (fun k c =>
    max k (max (polyBits c.queryPoly) (max (chainBits c.squarefree) (chainBits c.remainders)))) k
  let steps := (n.preparation.map (·.steps)).getD [] ++
    n.reductions.toList.flatMap (fun r => (r.map (·.steps)).getD [])
  steps.foldl (fun k s => max k (max (polyBits s.next) (stepBits s.witness))) k) 0


private def record (n : Nat) (side : String) (source : Root) (i : Input)
    (direct : Replay Rat Nat) (order : Ordering) : IO Lean.Json := do
  let some tree := i.tree | throw (IO.userError "missing joint tree")
  let some graph := i.graph | throw (IO.userError "missing joint graph")
  let directGraph := Dag.encode direct
  let ns := nodes tree
  let treeBytes := graph.encodeBytes ValueCodec.rat ValueCodec.nat
  let directBytes := directGraph.encodeBytes ValueCodec.rat ValueCodec.nat
  let expected := [(signs i.queries 1, (1 : Int)), (signs i.queries (-1), 1)]
  for (g, bytes) in [(graph, treeBytes), (directGraph, directBytes)] do
    let some replayed := g.replay? Sturm.orderSign 10377 i.head .negInf .posInf i.queries
      | throw (IO.userError "joint graph replay failed")
    let .ok decoded := Dag.decodeBytes ValueCodec.rat ValueCodec.nat Sturm.orderSign
        10377 i.head .negInf .posInf i.queries bytes {bytes := max 16777216 bytes.size}
      | throw (IO.userError "joint byte replay failed")
    unless entries replayed.val.node.system == expected &&
        entries decoded.val.node.system == expected do
      throw (IO.userError "joint replay table differs from the independent root table")
  return Lean.Json.mkObj [
    ("degree", Lean.toJson n), ("side", Lean.toJson side),
    ("context", Lean.toJson (10377 : Nat)), ("source", Codec.poly ValueCodec.rat source.raw.head),
    ("sourceIndices", Lean.toJson source.raw.indices), ("sourceSigns", Lean.toJson source.raw.signs),
    ("head", Codec.poly ValueCodec.rat i.head),
    ("queries", Codec.list (Codec.poly ValueCodec.rat) i.queries),
    ("table", Lean.toJson (entries tree.node.system)),
    ("directTable", Lean.toJson (entries direct.node.system)),
    ("order", Lean.toJson (match order with | .lt => "lt" | .eq => "eq" | .gt => "gt")),
    ("querySlots", Lean.toJson (ns.foldl (fun k node => k + node.size) 0)),
    ("maxColumns", Lean.toJson (ns.foldl (fun k node => max k node.size) 0)),
    ("maxSupport", Lean.toJson (ns.foldl (fun k node => max k node.system.support.length) 0)),
    ("maxInverseBits", Lean.toJson (ns.foldl (fun k node =>
      node.system.inverse.rows.toArray.foldl (fun k row =>
        row.toArray.foldl (fun k z => max k (bits z)) k) k) 0)),
    ("maxDenominatorBits", Lean.toJson (ns.foldl (fun k node => max k (bits node.system.denominator)) 0)),
    ("treeNodes", Lean.toJson ns.length), ("graphNodes", Lean.toJson graph.entries.size),
    ("graphEdges", Lean.toJson (graph.entries.foldl (fun k e => k + if e.children.isSome then 2 else 0) 0)),
    ("reducedQueryWitnessBits", Lean.toJson (witnessBits tree)),
    ("directQueryWitnessBits", Lean.toJson (witnessBits direct)),
    ("reducedGraphBytes", Lean.toJson treeBytes.size), ("directGraphBytes", Lean.toJson directBytes.size)]

/-- Untimed input inventory of actual completion and cross-polynomial comparison.
The root/sign table is checked by direct rational evaluation at the known roots;
no exponential reference enumeration is attempted for these joint lists. -/
def inspect (ns : Array Nat) : IO UInt32 := do
  for n in ns do
    let some i := input n | throw (IO.userError s!"invalid joint input at {n}")
    for (side, source, joint, direct) in
        [("left", i.leftFull, i.left, i.leftDirect), ("right", i.rightFull, i.right, i.rightDirect)] do
      IO.println (← record n side source joint direct i.order).compress
      (← IO.getStdout).flush
  return 0

/-- The degree-three CI input includes both graph and byte replay paths. -/
def verify : IO Unit := do
  let some i := input 3 | throw (IO.userError "joint fixture failed at degree three")
  for (side, source, joint, direct) in
      [("left", i.leftFull, i.left, i.leftDirect), ("right", i.rightFull, i.right, i.rightDirect)] do
    discard <| record 3 side source joint direct i.order

end Hex.SignDetBench.Joint
