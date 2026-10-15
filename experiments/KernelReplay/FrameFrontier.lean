/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameNested
public meta import KernelReplay.NativeAssemblyStaged
import all KernelReplay.NativeAssemblyNestedData
public meta import KernelReplay.FiniteChain
public meta import KernelReplay.FiniteBase
public meta import KernelReplay.FiniteData
public meta import HexRealClosureTheory.NativeAssemblyModels
import all HexRowReduce.Loop
import all HexRowReduce.Pivot
import all HexRowReduce.Api
-- Kernel replay inspects the actual validated producer result. Access to
-- preparation internals is restricted to this exact experiment by the DAG lint.
import all HexSturm.Basic
import all HexRealClosure.BaseContext
import all HexRealClosure.BaseJson
import all HexRealClosure.FrameFormat
import all HexRealClosure.TowerContext
import all HexRealClosure.InversePacking
import all HexRealClosure.Algebraic
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Table
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Std.Data.DHashMap.Basic
import all Std.Data.DHashMap.Raw
import all Std.Data.DHashMap.Internal.Defs
import all Std.Data.DHashMap.Internal.AssocList.Basic
import all Init.Prelude
import all Init.Util
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.RecordPackets
import all HexRealClosure.InversePackets
import all HexSignDet.Dag
import all HexSignDet.DagEncode
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra
import all HexRealClosure.RecordReaders
import all HexRealClosure.QueryOperations
import all HexRealClosure.RecordQueries
import all HexRealClosureTheory.SignReplay
import all HexRealClosure.SignCodec

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameFrontier
open Lean Meta Elab Command FiniteData

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"{message} [heartbeats={(← IO.getNumHeartbeats) / 1000}]"
      handle.flush

syntax (name := frameFrontier) "#frame_frontier" : command
@[command_elab frameFrontier]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <|
  withOptions (fun options => smartUnfolding.set options false) do
    let native ← withExporting (isExporting := false) do
      NativeChain.ofContext (← mkAppM ``FrameNested.extend
        #[← mkAppM ``Context.root #[mkConst ``NativeAssemblyStaged.owner]])
    unless native.owners.size == 2 do throwError "frontier lost an original owner"
    diagnostic "frontier: actual two-level owners extracted"
    let carrier ← mkAppM ``BaseContext.Element #[native.base]
    withLocalDeclD `baseReader (← mkArrow carrier (mkConst ``Real)) fun read => do
      native.withLevels read fun levels => do
        let types (current : Array FiniteData.Level) : MetaM (Array Expr) := do
          let some second := current[1]? | throwError "second native level missing"
          return #[← mkAppM ``Packing.Inventory.Data
            #[second.context, second.entries, second.records, second.facts, second.read]]
        let discovery ← collectDependencies 0 levels types FiniteDataProbe.supply
          (fun _ _ => throwError "zero-budget frontier invoked a record producer")
        unless discovery.requests.isEmpty && !discovery.saturated && !discovery.leaves.isEmpty do
          throwError "empty-inventory frontier did not retain its missing support"
        let mut lookups := 0
        for leaf in discovery.leaves do
          if let some lookup ← leaf.lookup? then
            let depth := native.owners.findIdx? (· == lookup.request.context)
            let printed ← withOptions (fun options => pp.maxSteps.set options 200) do
              ppExpr lookup.request.polynomial
            diagnostic s!"frontier: lookup={lookups} depth={depth} polynomial={printed}"
            lookups := lookups + 1
        unless lookups > 0 do throwError "native frontier retained no original lookup"
        diagnostic s!"frontier: leaves={discovery.leaves.size} lookups={lookups}"
    logInfo "actual second-descriptor frontier retained original missing support without producing records"

end Hex.RealClosure.Algebraic.KernelReplay.FrameFrontier

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: actual second-descriptor frontier retained original missing support without producing records -/
#guard_msgs in
#frame_frontier
