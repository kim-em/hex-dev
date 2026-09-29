/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Phases
import HexSignDet.Small
import HexSignDet.Joint
import HexSignDet.Paired
import HexSignDet.Maximal
import LeanBench
import Lean.Data.Json

/-!
Computational performance owner: `HexSignDet`.

The sparse-support family fixes P=X²−1, uses s copies of X and takes s to be
a power of two. There are exactly two realized words. Leaves have three
columns; every internal candidate has four columns, of which two survive.
All coefficient and matrix scalar sizes stay bounded independently of s.
Every node of arity k scans/copies Θ(k) query, exponent and sign slots, with
bounded matrix dimensions and at most two nonzero exponents per moment row.
Summing across the balanced tree gives Θ(s log s) production and tree replay.
Query-kernel work also contributes a linear term, so the asymptotic log term
need not dominate at the measured finite sizes; the retained verdict must be
interpreted with the measured phase attribution and input inventory.

For these identical blocks only, the graph fixture retains one node per
arity and binds both child edges to the same smaller accepted node. Its
query/sign-slot volume is s+s/2+…+1, giving Θ(s) graph replay. Preparation
checks the graph and both full-tree producer modes against the known table.
It is outside the timed bodies. This is a sparse-support family, not coverage
of maximal realized support, growing head/query degree, coefficient bits,
extension levels or the other required Phase-4 tracks.
-/
namespace Hex.SignDetBench
open Hex.SignDet

@[noinline] def runProduce (i : Input) : Option UInt64 := do
  let d ← i.domain
  match buildPrepared (10377 : Nat) d i.queries with
  | .error _ => none
  | .ok t => some (hash (entries t.val.node.system))

@[noinline] def runDirect (i : Input) : Option UInt64 := do
  let d ← i.domain
  match buildPrepared (10377 : Nat) d i.queries false with
  | .error _ => none
  | .ok t => some (hash (entries t.val.node.system))

@[noinline] def runTree (i : Input) : Bool :=
  match i.tree with
  | none => false
  | some t => t.check Sturm.orderSign 10377 i.head .negInf .posInf i.queries

@[noinline] def runGraph (i : Input) : Bool :=
  match i.graph with
  | none => false
  | some d => d.check Sturm.orderSign 10377 i.head .negInf .posInf i.queries

-- Declared cost-model: Θ(s log s), direct moments and bounded-size systems on the two-root family.
setup_benchmark runSmallReduced s => s * (Nat.log2 s + 1)
  with prep := smallInput
  where {
    paramSchedule := .custom #[1, 2, 3, 4, 5]
    paramFloor := 1
    paramCeiling := 5
    outerTrials := 6
    targetInnerNanos := 1000000000
    maxSecondsPerCall := 60
  }

-- Declared cost-model: Θ(27^s) from cubic work on a full 3^s square system:
-- dense Gauss-Jordan worst-case and inverse-identity replay. The structured
-- moment matrix can have fewer row additions; retain any model mismatch.
setup_benchmark runSmallFull s => 27^s
  with prep := smallInput
  where {
    paramSchedule := .custom #[1, 2, 3, 4, 5]
    paramFloor := 1
    paramCeiling := 5
    outerTrials := 6
    targetInnerNanos := 1000000000
    maxSecondsPerCall := 60
  }


-- Declared cost-model: Θ(s log s), bounded-size systems and Θ(k) slot work at every balanced node.
setup_benchmark runProduce s => s * (Nat.log2 s + 1)
  with prep := input
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

-- Declared cost-model: Θ(s log s), each direct row scans k factors but at most two exponents are nonzero.
setup_benchmark runDirect s => s * (Nat.log2 s + 1)
  with prep := input
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

-- Declared cost-model: Θ(s log s), full literal replay visits every balanced node and its k ordered slots.
setup_benchmark runTree s => s * (Nat.log2 s + 1)
  with prep := input
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

-- Declared cost-model: Θ(s), one node per arity has total query/sign-slot volume s+s/2+…+1.
setup_benchmark runGraph s => s
  with prep := input
  where {
    paramSchedule := .custom #[64, 128, 256, 512, 1024, 2048]
    paramFloor := 64
    paramCeiling := 2048
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 10
  }

/- Joint Thom-query family: n is the odd source degree, the target degree is
2n, and each joint list has 3n+1 entries. The model counts coefficient
operations: leaf squares give Ω(n³); moment/head-derivative products and
pseudo-division contribute O(n²) per row over O(n) rows. The actual direct
power algorithm also computes unused squares. Production includes replay.
Candidate dimensions stay at most four; every
moment row has exponent sum at most two. The sparse binomial/monomial PRS
has bounded chain length. Remaining query-slot scans sum to O(n² log n).
The inventory checks these structural hypotheses. Rational bit sizes grow;
this is not a unit-bit model or a general-head complexity claim. See
reports/sign-det-joint-performance.md for the scope and derivation. -/

-- Declared cost-model: Θ(n³) coefficient operations for two source completion tables; see the joint derivation above.
setup_benchmark Joint.runCompletion n => n^3
  with prep := Joint.input
  where {
    paramSchedule := .custom #[3, 7, 15, 31, 63]
    paramFloor := 3
    paramCeiling := 63
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

-- Declared cost-model: Θ(n³) coefficient operations for four common-head re-encoding/descriptor tables; see the joint derivation above.
setup_benchmark Joint.runComparison n => n^3
  with prep := Joint.input
  where {
    paramSchedule := .custom #[3, 7, 15, 31, 63]
    paramFloor := 3
    paramCeiling := 63
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

-- Declared cost-model: Θ(n³) coefficient operations for both joint tables with reduced products; see the joint derivation above.
setup_benchmark Joint.runReduced n => n^3
  with prep := Joint.input
  where {
    paramSchedule := .custom #[3, 7, 15, 31, 63]
    paramFloor := 3
    paramCeiling := 63
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

-- Declared cost-model: Θ(n³) coefficient operations for both joint tables with direct products; see the joint derivation above.
setup_benchmark Joint.runDirect n => n^3
  with prep := Joint.input
  where {
    paramSchedule := .custom #[3, 7, 15, 31, 63]
    paramFloor := 3
    paramCeiling := 63
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

-- Declared cost-model: Θ(n³) coefficient operations for literal reduced evidence checks; see the joint derivation above.
setup_benchmark Joint.runCheckReduced n => n^3
  with prep := Joint.input
  where {
    paramSchedule := .custom #[3, 7, 15, 31, 63]
    paramFloor := 3
    paramCeiling := 63
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

-- Declared cost-model: Θ(n³) coefficient operations for literal direct evidence checks; see the joint derivation above.
setup_benchmark Joint.runCheckDirect n => n^3
  with prep := Joint.input
  where {
    paramSchedule := .custom #[3, 7, 15, 31, 63]
    paramFloor := 3
    paramCeiling := 63
    outerTrials := 6
    targetInnerNanos := 100000000
    signalFloorMultiplier := 1
    maxSecondsPerCall := 180
  }

private def intBits (z : Int) : Nat := if z = 0 then 0 else z.natAbs.log2 + 1
private def ratBits (q : Rat) : Nat := max (intBits q.num) (q.den.log2 + 1)

private def treeEdges : Replay Rat Nat → Nat
  | .leaf _ => 0
  | .split _ left right => 2 + treeEdges left + treeEdges right

/-- Untimed inventory validates the structural hypotheses used by the declared
family model. It reports actual stored dimensions, exponents and slot counts. -/
def inspect : IO UInt32 := do
  for s in #[64, 128, 256, 512, 1024, 2048] do
    let i := input s
    let some tree := i.tree | throw (IO.userError "missing tree")
    let some graph := i.graph | throw (IO.userError "missing graph")
    let ns := nodes tree
    let queries := ns.foldl (fun k n => k + n.size) 0
    let maxColumns := ns.foldl (fun k n => max k n.size) 0
    let maxSupport := ns.foldl (fun k n => max k n.system.support.length) 0
    let maxExponentSum := ns.foldl (fun k n =>
      n.system.rows.toList.foldl (fun k es => max k es.sum) k) 0
    let actualTreeEdges := treeEdges tree
    let actualGraphEdges := graph.entries.foldl (fun k e =>
      k + if e.children.isSome then 2 else 0) 0
    let storedCoefficientBits := ns.foldl (fun k n => n.moments.toList.foldl (fun k c =>
      c.remainders.chain.foldl (fun k p => p.toArray.foldl (fun k q => max k (ratBits q)) k) k) k) 0
    unless ns.length == 2 * s - 1 && queries == 7 * s - 4 && maxColumns == 4 &&
        maxSupport == 2 && maxExponentSum == 2 && storedCoefficientBits ≤ 4 &&
        graph.entries.size == s.log2 + 1 && actualTreeEdges == 2 * (s - 1) &&
        actualGraphEdges == 2 * s.log2 && runTree i && runGraph i &&
        runProduce i == runDirect i do
      throw (IO.userError s!"sparse model invariant failed at {s}")
    IO.println <| (Lean.Json.mkObj [
      ("family", Lean.toJson "repeated-query-sparse-support"), ("queries", Lean.toJson s),
      ("headDegree", Lean.toJson i.head.natDegree), ("queryDegree", Lean.toJson (1 : Nat)),
      ("treeNodes", Lean.toJson ns.length), ("treeEdges", Lean.toJson actualTreeEdges),
      ("querySlots", Lean.toJson queries), ("maxColumns", Lean.toJson maxColumns),
      ("maxSupport", Lean.toJson maxSupport), ("maxExponentSum", Lean.toJson maxExponentSum),
      ("remainderCoefficientBits", Lean.toJson storedCoefficientBits),
      ("graphNodes", Lean.toJson graph.entries.size),
      ("graphEdges", Lean.toJson actualGraphEdges),
      ("treeArityVolume", Lean.toJson (ns.foldl (fun k n => k + n.queries.length) 0)),
      ("graphArityVolume", Lean.toJson (graph.entries.foldl (fun k e => k + e.node.queries.length) 0)),
      ("inputHash", Lean.toJson (hash i).toNat),
      ("productionResultHash", Lean.toJson (hash (some (hash
        [(List.replicate s (-1 : Int), (1 : Int)), (List.replicate s (1 : Int), (1 : Int))]))).toNat),
      ("replayResultHash", Lean.toJson (hash true).toNat)]).compress
  return 0

end Hex.SignDetBench

def main (args : List String) : IO UInt32 :=
  if args == ["inspect"] then Hex.SignDetBench.inspect
  else if args == ["inspect-phases"] then Hex.SignDetBench.inspectPhases
  else if args == ["inspect-small"] then Hex.SignDetBench.inspectSmall
  else if args == ["inspect-maximal"] then Hex.SignDetBench.inspectMaximal
  else if args == ["inspect-joint"] then Hex.SignDetBench.Joint.inspect #[3, 7, 15, 31, 63]
  else if let ["inspect-joint", degree] := args then
    match degree.toNat? with
    | some n => Hex.SignDetBench.Joint.inspect #[n]
    | none => throw (IO.userError "expected an odd integer degree at least three")
  else if args == ["inspect-joint-timings"] then Hex.SignDetBench.Joint.inspectTimings #[3, 7, 15, 31, 63]
  else if let ["inspect-joint-timings", degree] := args then
    match degree.toNat? with
    | some n => Hex.SignDetBench.Joint.inspectTimings #[n]
    | none => throw (IO.userError "expected an odd integer degree at least three")
  else if args == ["inspect-full"] then Hex.SignDetBench.inspectFull
  else if let ["paired-small", path] := args then
    Hex.SignDetBench.paired ``Hex.SignDetBench.runSmallReduced ``Hex.SignDetBench.runSmallFull path
  else if let ["paired-joint-production", path] := args then
    Hex.SignDetBench.paired ``Hex.SignDetBench.Joint.runReduced ``Hex.SignDetBench.Joint.runDirect path
  else if let ["paired-joint-replay", path] := args then
    Hex.SignDetBench.paired ``Hex.SignDetBench.Joint.runCheckReduced ``Hex.SignDetBench.Joint.runCheckDirect path
  else if args.head? == some "verify" then do
    match Hex.SignDetBench.buildMaximal 2 with
    | .ok _ => pure ()
    | .error message => throw (IO.userError s!"maximal-support fixture failed: {message}")
    Hex.SignDetBench.Joint.verify
    discard <| Hex.SignDetBench.Joint.inspectTimings #[3]
    LeanBench.Cli.dispatch args
  else LeanBench.Cli.dispatch args
