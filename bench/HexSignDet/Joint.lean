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

/-- Diagnostic reports use Lean JSON; certificate replay uses the proved codec. -/
private def reportJson (value : Codec.Json) : IO Lean.Json := do
  let some text := String.fromUTF8? value.writeBytes
    | throw (IO.userError "report encoding emitted invalid UTF-8")
  match Lean.Json.parse text with
  | .ok result => return result
  | .error message => throw (IO.userError message)

private def rootHash (d : Root) : UInt64 :=
  let input : Input := ⟨d.raw.head, d.raw.queries, none, some d.evidence, none⟩
  hash (hash input, d.raw.indices, d.raw.signs)

instance : Hashable Case where
  hash i :=
    let leftDirect : Input := { i.left with tree := some i.leftDirect, graph := none }
    let rightDirect : Input := { i.right with tree := some i.rightDirect, graph := none }
    hash (rootHash i.leftPartial, rootHash i.rightPartial,
      rootHash i.leftFull, rootHash i.rightFull, hash i.left, hash i.right,
      hash leftDirect, hash rightDirect)

/-- Only the two descriptors used by completion or comparison. -/
structure Sources where
  left : Root
  right : Root

instance : Hashable Sources where
  hash i := hash (rootHash i.left, rootHash i.right)

/-- Only the prepared domains, queries and supplied evidence used by a table
operation. Production does not need evidence; checking receives it explicitly. -/
structure Tables where
  left : Input
  right : Input

instance : Hashable Tables where
  hash i := hash (hash i.left, hash i.right)

/-- Complete both original partial descriptors, including their actual table
production and derivative-word selection. Preparation is outside this body. -/
@[noinline] def runCompletion (input : Option Sources) : Option (UInt64 × UInt64) := do
  let i ← input
  let .ok l := i.left.buildCompletion | none
  let .ok r := i.right.buildCompletion | none
  return (hash l.descriptor.raw.signs, hash r.descriptor.raw.signs)

/-- Compare the already completed sources through the actual common-product
and re-encoding producers. Keep the returned head and both root identities. -/
@[noinline] def runComparison (input : Option Sources) : Option UInt64 := do
  let i ← input
  let .ok c := i.left.buildComparison i.right | none
  let order : Nat := match c.order with | .lt => 0 | .eq => 1 | .gt => 2
  return hash (order, polyHash c.common.head,
    c.leftEncoding.target.raw.signs, c.rightEncoding.target.raw.signs)

private def runTables (input : Option Tables) (reduced : Bool) : Option (UInt64 × UInt64) := do
  let i ← input
  let ld ← i.left.domain
  let rd ← i.right.domain
  let .ok l := buildPrepared (10377 : Nat) ld i.left.queries reduced | none
  let .ok r := buildPrepared (10377 : Nat) rd i.right.queries reduced | none
  return (hash (entries l.val.node.system), hash (entries r.val.node.system))

/-- Construct both original ordered joint tables with modulo-head products. -/
@[noinline] def runReduced (input : Option Tables) : Option (UInt64 × UInt64) :=
  runTables input true

/-- Construct the same two tables with unreduced moment products. -/
@[noinline] def runDirect (input : Option Tables) : Option (UInt64 × UInt64) :=
  runTables input false

/-- Check both supplied reduced evidence trees, including their literal
polynomial, interval, context, support and exact matrix witnesses. -/
@[noinline] def runCheckReduced (input : Option Tables) : Bool :=
  match input with
  | none => false
  | some i =>
    match i.left.tree, i.right.tree with
    | some l, some r =>
      l.check Sturm.orderSign 10377 i.left.head .negInf .posInf i.left.queries &&
      r.check Sturm.orderSign 10377 i.right.head .negInf .posInf i.right.queries
    | _, _ => false

/-- Check the supplied direct evidence against the same caller bindings. -/
@[noinline] def runCheckDirect (input : Option Tables) : Bool :=
  match input with
  | none => false
  | some i =>
    match i.left.tree, i.right.tree with
    | some l, some r =>
      l.check Sturm.orderSign 10377 i.left.head .negInf .posInf i.left.queries &&
      r.check Sturm.orderSign 10377 i.right.head .negInf .posInf i.right.queries
    | _, _ => false

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

/-- Validate just the original partial selections. Completing them is the
measured operation, so no completion or comparison runs here. -/
def sourceInput (n : Nat) : Option Sources := do
  if n < 3 || n % 2 != 1 then none else do
    let x : DensePoly Rat := DensePoly.monomial n 1
    let raw := fun head => (⟨10377, head, .negInf, .posInf, [n], [1]⟩ : RawDescriptor Rat Nat)
    let .ok (.ok l) := Descriptor.build Sturm.orderSign 10377 (raw (x - 1)) | none
    let .ok (.ok r) := Descriptor.build Sturm.orderSign 10377 (raw (x + 1)) | none
    if l.raw.head.eval 1 != 0 || r.raw.head.eval (-1) != 0 then none else
      some ⟨l, r⟩

/-- Comparison starts with complete original identities. Do not also compute
its common-head result or either direct reference table during preparation. -/
def comparisonInput (n : Nat) : Option Sources := do
  let i ← sourceInput n
  let .ok l := i.left.buildCompletion | none
  let .ok r := i.right.buildCompletion | none
  if l.descriptor.raw.signs != signs l.descriptor.raw.queries 1 ||
      r.descriptor.raw.signs != signs r.descriptor.raw.queries (-1) then none else
    some ⟨l.descriptor, r.descriptor⟩

/-- Construct the actual common head and ordered joint queries. No table
production or root comparison is needed to prepare a table producer. -/
def tableInput (n : Nat) : Option Tables := do
  if n < 3 || n % 2 != 1 then none else do
    let x : DensePoly Rat := DensePoly.monomial n 1
    let p := x - 1
    let q := x + 1
    let .ok common := CommonProduct.build (10377 : Nat) p q | none
    let h := DensePoly.scale (-1/2 : Rat) (DensePoly.monomial (2*n) (1 : Rat) - 1)
    if common.val.head != h || common.val.factor != DensePoly.C (-2 : Rat) then none else do
      let domain ← Sturm.prepare Sturm.orderSign h .negInf .posInf
      let raw := fun head => (⟨10377, head, .negInf, .posInf, [], []⟩ : RawDescriptor Rat Nat)
      let target := ((raw h).full []).queries
      let lqs := target ++ ((raw p).full []).constraints
      let rqs := target ++ ((raw q).full []).constraints
      if lqs.length != 3*n+1 || rqs.length != 3*n+1 then none else
        some ⟨⟨h, lqs, some domain, none, none⟩, ⟨h, rqs, some domain, none, none⟩⟩

/-- Prepare only the two supplied trees checked by the chosen replay arm.
Validate their answers independently by exact evaluation at ±1. -/
def evidenceInput (n : Nat) (reduced : Bool) : Option Tables := do
  let i ← tableInput n
  let ld ← i.left.domain
  let rd ← i.right.domain
  let .ok l := buildPrepared (10377 : Nat) ld i.left.queries reduced | none
  let .ok r := buildPrepared (10377 : Nat) rd i.right.queries reduced | none
  let expected := fun qs => [(signs qs 1, (1 : Int)), (signs qs (-1), 1)]
  if entries l.val.node.system != expected i.left.queries ||
      entries r.val.node.system != expected i.right.queries then none else
    some ⟨{i.left with tree := some l.val}, {i.right with tree := some r.val}⟩

def reducedInput (n : Nat) : Option Tables := evidenceInput n true
def directInput (n : Nat) : Option Tables := evidenceInput n false

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
    ("context", Lean.toJson (10377 : Nat)), ("source", (← reportJson (Codec.poly ValueCodec.rat source.raw.head))),
    ("sourceIndices", Lean.toJson source.raw.indices), ("sourceSigns", Lean.toJson source.raw.signs),
    ("head", (← reportJson (Codec.poly ValueCodec.rat i.head))),
    ("queries", (← reportJson (Codec.list (Codec.poly ValueCodec.rat) i.queries))),
    ("table", Lean.toJson (entries tree.node.system)),
    ("directTable", Lean.toJson (entries direct.node.system)),
    ("order", Lean.toJson (match order with | .lt => "lt" | .eq => "eq" | .gt => "gt")),
    ("querySlots", Lean.toJson (ns.foldl (fun k node => k + node.size) 0)),
    ("maxColumns", Lean.toJson (ns.foldl (fun k node => max k node.size) 0)),
    ("maxSupport", Lean.toJson (ns.foldl (fun k node => max k node.system.support.length) 0)),
    ("maxExponentSum", Lean.toJson ((ns ++ nodes direct).foldl (fun k node =>
      node.system.rows.toList.foldl (fun k es => max k es.sum) k) 0)),
    ("maxDirectChainLength", Lean.toJson ((nodes direct).foldl (fun k node =>
      node.moments.toList.foldl (fun k c => max k c.remainders.chain.size) k) 0)),
    ("maxReducedChainLength", Lean.toJson (ns.foldl (fun k node =>
      node.moments.toList.foldl (fun k c => max k c.remainders.chain.size) k) 0)),
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

/-- Untimed result bindings for the timed callbacks. Expected words and tables
come from exact evaluation at the known roots, not from the timed functions. -/
def inspectTimings (ns : Array Nat) : IO UInt32 := do
  for n in ns do
    let some i := input n | throw (IO.userError s!"invalid joint input at {n}")
    let target : RawDescriptor Rat Nat := ⟨10377, i.left.head, .negInf, .posInf, [], []⟩
    let leftTable := [(signs i.left.queries 1, (1 : Int)), (signs i.left.queries (-1), 1)]
    let rightTable := [(signs i.right.queries 1, (1 : Int)), (signs i.right.queries (-1), 1)]
    let completion := some (hash (signs i.leftFull.raw.queries 1),
      hash (signs i.rightFull.raw.queries (-1)))
    let comparison := some (hash ((2 : Nat), polyHash i.left.head,
      signs (target.full []).queries 1, signs (target.full []).queries (-1)))
    let tables := some (hash leftTable, hash rightTable)
    unless runCompletion (some ⟨i.leftPartial, i.rightPartial⟩) == completion && runComparison (some ⟨i.leftFull, i.rightFull⟩) == comparison &&
        runReduced (some ⟨i.left, i.right⟩) == tables && runDirect (some ⟨i.left, i.right⟩) == tables &&
        runCheckReduced (some ⟨i.left, i.right⟩) && runCheckDirect (some ⟨{i.left with tree := some i.leftDirect},
          {i.right with tree := some i.rightDirect}⟩) do
      throw (IO.userError s!"joint callback differs from the independent root answers at {n}")
    unless runCompletion (sourceInput n) == completion &&
        runComparison (comparisonInput n) == comparison &&
        runReduced (tableInput n) == tables && runDirect (tableInput n) == tables &&
        runCheckReduced (reducedInput n) && runCheckDirect (directInput n) do
      throw (IO.userError s!"separate joint preparation differs at {n}")
    let some prepared := tableInput n | throw (IO.userError "missing prepared joint queries")
    unless prepared.left.head == i.left.head && prepared.right.head == i.right.head &&
        prepared.left.queries == i.left.queries && prepared.right.queries == i.right.queries do
      throw (IO.userError s!"separate joint preparation changed literal bindings at {n}")
    IO.println <| (Lean.Json.mkObj [
      ("degree", Lean.toJson n), ("queries", Lean.toJson (3*n+1)),
      ("completionResultHash", Lean.toJson (hash completion).toNat),
      ("comparisonResultHash", Lean.toJson (hash comparison).toNat),
      ("tableResultHash", Lean.toJson (hash tables).toNat),
      ("replayResultHash", Lean.toJson (hash true).toNat)]).compress
    (← IO.getStdout).flush
  return 0

/-- The degree-three CI input includes both graph and byte replay paths. -/
def verify : IO Unit := do
  let some i := input 3 | throw (IO.userError "joint fixture failed at degree three")
  -- Individual query preprocessing only normalizes these monomials. Moment
  -- construction also reduces their products: (-3X^5)^2 becomes X^4 modulo
  -- (1-X^6)/2 after positive normalization. Direct mode retains 9X^10.
  let q := DensePoly.monomial 5 (-3 : Rat)
  let some tree := i.left.tree | throw (IO.userError "missing joint tree")
  let some reduced := (nodes tree).find? (fun node => node.queries == [q])
    | throw (IO.userError "missing first-derivative reduced leaf")
  let some direct := (nodes i.leftDirect).find? (fun node => node.queries == [q])
    | throw (IO.userError "missing first-derivative direct leaf")
  let some reducedMoment := reduced.moments.toArray[2]?
    | throw (IO.userError "missing squared reduced moment")
  let some directMoment := direct.moments.toArray[2]?
    | throw (IO.userError "missing squared direct moment")
  unless reducedMoment.queryPoly == DensePoly.monomial 4 (1 : Rat) &&
      directMoment.queryPoly == DensePoly.monomial 10 (9 : Rat) do
    throw (IO.userError "joint moment reduction differs from the polynomial remainder")
  for (side, source, joint, direct) in
      [("left", i.leftFull, i.left, i.leftDirect), ("right", i.rightFull, i.right, i.rightDirect)] do
    discard <| record 3 side source joint direct i.order

end Hex.SignDetBench.Joint
