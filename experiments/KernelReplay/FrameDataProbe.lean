/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.NativeAssemblyStaged
public import KernelReplay.FrameData
import all KernelReplay.FrameEncode
import all KernelReplay.FrameData
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

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe
open Hex.SignDet

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
/-- Ordinary kernel evaluation forces the complete first frame, including its
serialized graph. Reflexive source signatures cannot use native hashing here. -/
theorem frame_reduces :
    decide (FrameEncode.frameData NativeAssemblyStaged.base.codec NativeAssemblyStaged.owner.root =
      FrameEncode.frameData NativeAssemblyStaged.base.codec NativeAssemblyStaged.owner.root) = true := by
  decide +kernel

theorem frame_agrees :
    FrameEncode.frameData NativeAssemblyStaged.base.codec NativeAssemblyStaged.owner.root =
      Tower.rootData NativeAssemblyStaged.base.codec NativeAssemblyStaged.owner.root := by
  rw [FrameEncode.frameData_eq]

local instance : Hashable (BaseContext.Element FiniteBaseProbe.base) := ⟨fun _ => 0⟩
local instance : Hashable Tower.Signature := ⟨fun _ => 0⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
/-- A repeated child is stored once, and the parent keeps both earlier-node
references. The node is the actual retained descriptor's first leaf. -/
theorem shared_children :
    (match NativeAssemblyStaged.owner.root.evidence with
    | .leaf node =>
      let graph := FrameEncode.encodeLinear (.split node (.leaf node) (.leaf node))
      graph.entries.size == 2 && graph.root == 1 &&
        (graph.entries[1]?).map (·.children) == some (some (0, 0))
    | .split _ _ _ => false) = true := by
  decide +kernel

end Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe.frame_reduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe.frame_reduces
/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe.frame_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe.frame_agrees

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe.shared_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FrameDataProbe.shared_children
