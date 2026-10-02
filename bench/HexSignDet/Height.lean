/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Input
import Lean.Data.Json

namespace Hex.SignDetBench
open Hex.SignDet

private def bits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1

namespace Height

/-- Fixed degree and support, with independently increasing coefficient bits.
The only real root of the head is one; all three queries are positive there.
The full ternary reference is checked in addition to this independent oracle. -/
def input (height : Nat) : Option (Input × Replay Rat Nat × Node Rat Nat) := do
  if height < 2 then none else do
    let c : Rat := ((2^height - 1 : Nat) : Rat)
    let p : DensePoly Rat := DensePoly.monomial 3 1 - 1
    let qs := [DensePoly.monomial 2 c, DensePoly.monomial 1 c, DensePoly.C c]
    if p.eval 1 != 0 || !qs.all (fun q => Sturm.orderSign (q.eval 1) == 1) then none else do
      let domain ← Sturm.prepare Sturm.orderSign p .negInf .posInf
      let .ok reduced := buildPrepared (10377 : Nat) domain qs | none
      let .ok direct := buildPrepared (10377 : Nat) domain qs false | none
      let .ok full := referencePrepared (10377 : Nat) domain qs | none
      let expected := [([1, 1, 1], (1 : Int))]
      let graph := Dag.encode reduced.val
      if entries reduced.val.node.system != expected || entries direct.val.node.system != expected ||
          entries full.system != expected || full.size != 27 ||
          !full.check Sturm.orderSign 10377 p .negInf .posInf qs ||
          !graph.check Sturm.orderSign 10377 p .negInf .posInf qs then none else
        some (⟨p, qs, some domain, some reduced.val, some graph⟩, direct.val, full)

private def ratBits (q : Rat) : Nat := max (bits q.num) (q.den.log2 + 1)
private def polyBits (p : DensePoly Rat) : Nat :=
  p.toArray.foldl (fun k q => max k (ratBits q)) 0
private def stepBits (s : RemainderStep Rat) : Nat :=
  max (polyBits s.quotient) (max (ratBits s.leftScale) (ratBits s.rightScale))
private def chainBits (c : SignedRemainderChain Rat) : Nat :=
  max (c.chain.foldl (fun k p => max k (polyBits p)) 0)
    (max (c.steps.foldl (fun k s => max k (stepBits s)) (stepBits c.initial))
      ((c.terminal.map (fun (s, q) => max (ratBits s) (polyBits q))).getD 0))
def witnessBits (tree : Replay Rat Nat) : Nat := (nodes tree).foldl (fun k n =>
  let k := n.moments.toList.foldl (fun k c =>
    max k (max (polyBits c.queryPoly) (max (chainBits c.squarefree) (chainBits c.remainders)))) k
  let steps := (n.preparation.map (·.steps)).getD [] ++
    n.reductions.toList.flatMap (fun r => (r.map (·.steps)).getD [])
  steps.foldl (fun k s => max k (max (polyBits s.next) (stepBits s.witness))) k) 0

/-- The height ladder fixes every degree and support dimension. It records
literal coefficient/witness bits and byte sizes, not elapsed-time, allocation
or peak live arithmetic measurements. -/
def inspect : IO UInt32 := do
  for height in #[64, 128, 256, 512, 1024, 2048, 4096] do
    let some (i, direct, full) := input height | throw (IO.userError "invalid height input")
    let some reduced := i.tree | throw (IO.userError "missing height tree")
    let some graph := i.graph | throw (IO.userError "missing height graph")
    let directGraph := Dag.encode direct
    let reducedBytes := graph.encodeBytes ValueCodec.rat ValueCodec.nat
    let directBytes := directGraph.encodeBytes ValueCodec.rat ValueCodec.nat
    let ns := nodes reduced
    let slots := ns.foldl (fun k n => k + n.size) 0
    let maxColumns := ns.foldl (fun k n => max k n.size) 0
    unless i.head.natDegree == 3 && i.queries.map DensePoly.natDegree == [2, 1, 0] &&
        slots == 11 && ns.length == 5 && maxColumns == 3 && full.size == 27 do
      throw (IO.userError "height input dimensions changed")
    let expected := [([1, 1, 1], (1 : Int))]
    for (g, bytes) in [(graph, reducedBytes), (directGraph, directBytes)] do
      let some replayed := g.replay? Sturm.orderSign 10377 i.head .negInf .posInf i.queries
        | throw (IO.userError "height graph replay failed")
      let .ok decoded := Dag.decodeBytes ValueCodec.rat ValueCodec.nat Sturm.orderSign
          10377 i.head .negInf .posInf i.queries bytes
        | throw (IO.userError "height byte replay failed")
      unless entries replayed.val.node.system == expected &&
          entries decoded.val.node.system == expected do
        throw (IO.userError "height replay table differs from the independent root table")
    IO.println <| (Lean.Json.mkObj [
      ("height", Lean.toJson height), ("context", Lean.toJson (10377 : Nat)),
      ("head", Codec.poly ValueCodec.rat i.head),
      ("queries", Codec.list (Codec.poly ValueCodec.rat) i.queries),
      ("table", Lean.toJson (entries reduced.node.system)),
      ("directTable", Lean.toJson (entries direct.node.system)),
      ("fullTable", Lean.toJson (entries full.system)),
      ("queryCoefficientBits", Lean.toJson (i.queries.foldl (fun k q => max k (polyBits q)) 0)),
      ("reducedWitnessBits", Lean.toJson (witnessBits reduced)),
      ("directWitnessBits", Lean.toJson (witnessBits direct)),
      ("querySlots", Lean.toJson slots), ("maxColumns", Lean.toJson maxColumns),
      ("treeNodes", Lean.toJson ns.length), ("graphNodes", Lean.toJson graph.entries.size),
      ("graphEdges", Lean.toJson (graph.entries.foldl (fun k e => k + if e.children.isSome then 2 else 0) 0)),
      ("reducedGraphBytes", Lean.toJson reducedBytes.size),
      ("directGraphBytes", Lean.toJson directBytes.size),
      ("inputHash", Lean.toJson (hash i).toNat),
      ("productionResultHash", Lean.toJson (hash (some (hash (entries reduced.node.system)))).toNat),
      ("replayResultHash", Lean.toJson (hash true).toNat)]).compress
    (← IO.getStdout).flush
  return 0

/-- A fixed phase ladder avoids the bounded BKR work in the small inventory.
The largest integer occupies 64 KiB before allocator headers. -/
def phaseHeights : Array Nat := #[8192, 16384, 32768, 65536, 131072, 262144, 524288]

structure PhaseInput where
  head : DensePoly Rat
  queries : List (DensePoly Rat)
  reduction : QueryReduction Rat

/-- Integer hashes truncate to 64 bits. Bit lengths keep the phase
fingerprint sensitive to these large coefficients; they are not equality proofs. -/
private def reductionHash (r : QueryReduction Rat) : UInt64 :=
  hash (r.steps.map fun s => (s.index, polyHash s.next,
    s.witness.leftScale, polyHash s.witness.quotient, s.witness.rightScale,
    s.witness.rightScale.num.natAbs.log2, s.witness.rightScale.den.log2))

instance : Hashable PhaseInput where
  hash i := hash (polyHash i.head, i.queries.map polyHash, reductionHash i.reduction)

/-- Prepare only the actual query preprocessing phase. Unlike the small-input
inventory, this does not construct unreduced powers of the large coefficient. -/
def phaseInput (height : Nat) : PhaseInput :=
  let c : Rat := ((2^height - 1 : Nat) : Rat)
  let p : DensePoly Rat := DensePoly.monomial 3 1 - 1
  let qs := [DensePoly.monomial 2 c, DensePoly.monomial 1 c, DensePoly.C c]
  ⟨p, qs, QueryReduction.build Sturm.orderSign p qs⟩

/-- Check every literal preprocessing field against the symbolic monomial
oracle. Maxima alone would not justify the fixed number of large operands. -/
def phaseValid (height : Nat) (i : PhaseInput) : Bool :=
  let c : Rat := ((2^height - 1 : Nat) : Rat)
  let units : List (DensePoly Rat) :=
    [DensePoly.monomial 2 1, DensePoly.monomial 1 1, DensePoly.C 1]
  height > 1 && ratBits c == height &&
    i.head == DensePoly.monomial 3 1 - 1 &&
    i.queries == units.map (DensePoly.scale c) &&
    i.reduction.steps.length == 3 &&
    (i.reduction.steps.zip units).zipIdx.all (fun ((s, q), j) =>
      s.index == j && s.next == q && s.witness.leftScale == 1 &&
      s.witness.quotient == 0 && s.witness.rightScale == c) &&
    i.reduction.check Sturm.orderSign i.head i.queries

@[noinline] def runReduce (i : PhaseInput) : UInt64 :=
  reductionHash (QueryReduction.build Sturm.orderSign i.head i.queries)

@[noinline] def runCheck (i : PhaseInput) : Nat × Bool :=
  let height := ((i.queries.getD 2 0).coeff 0).num.natAbs.log2 + 1
  (height, i.reduction.check Sturm.orderSign i.head i.queries)

/-- Large-phase inputs are recorded symbolically, avoiding decimal JSON tokens
whose parser limits are unrelated to normalization or replay performance. -/
def inspectPhases : IO UInt32 := do
  for height in phaseHeights do
    let i := phaseInput height
    unless phaseValid height i do
      throw (IO.userError s!"invalid height normalization input at {height}")
    IO.println <| (Lean.Json.mkObj [
      ("height", Lean.toJson height),
      ("coefficient", Lean.toJson "2^height-1"),
      ("head", Lean.toJson "X^3-1"),
      ("queryDegrees", Lean.toJson ([2, 1, 0] : List Nat)),
      ("steps", Lean.toJson i.reduction.steps.length),
      ("coefficientBits", Lean.toJson height),
      ("coefficientBytes", Lean.toJson ((height + 7) / 8)),
      ("inputHash", Lean.toJson (hash i).toNat),
      ("productionResultHash", Lean.toJson (hash (reductionHash i.reduction)).toNat),
      ("replayResultHash", Lean.toJson (hash (runCheck i)).toNat)]).compress
    (← IO.getStdout).flush
  return 0

/-- CI exercises the actual normalization and replay without scientific timings. -/
def verify : IO Unit := do
  unless phaseValid 8192 (phaseInput 8192) do
    throw (IO.userError "height phase fixture failed at 8192 bits")

end Height

end Hex.SignDetBench
