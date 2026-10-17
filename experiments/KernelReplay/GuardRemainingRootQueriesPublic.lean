/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingProof01

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRootQueriesPublic

/-- The original first query at record one's root node. -/
theorem first : GuardRemainingQuery.record1.node0.query0.statement :=
  GuardRemainingQuery.record1.node0.query0.data

/-- The original second query at the same node, including both complete chains. -/
theorem second : GuardRemainingQuery.record1.node0.query1.statement :=
  GuardRemainingQuery.record1.node0.query1.data

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRootQueriesPublic
