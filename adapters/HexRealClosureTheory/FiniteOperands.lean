/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteData
public meta import HexRealClosureTheory.FiniteData

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

/-- Collect the original source coefficients and scalar operands of a reached
polynomial operation. These can be absent from its output after cancellation.
The returned list keeps its native coefficient type and local hypotheses. -/
def Leaf.coefficients? (leaf : Leaf) : MetaM (Option Expr) := leaf.withContext do
  let type := leaf.type
  let args := type.getAppArgs
  let coefficients (p : Expr) : MetaM Expr :=
    mkAppM ``Transport.Inventory.coefficients #[p]
  if #[``Transport.Sum, ``Transport.Product, ``Transport.Difference].any
      (fun name => type.getAppFn.isConstOf name) then
    let left ← coefficients args[args.size - 2]!
    let right ← coefficients args.back!
    return some (← mkAppM ``List.append #[left, right])
  if type.getAppFn.isConstOf ``Transport.Scaling then
    let scalar := args[args.size - 2]!
    let rest ← coefficients args.back!
    return some (← mkAppM ``List.cons #[scalar, rest])
  if type.getAppFn.isConstOf ``Transport.Evaluation then
    let argument := args.back!
    let rest ← coefficients args[args.size - 2]!
    return some (← mkAppM ``List.cons #[argument, rest])
  if type.getAppFn.isConstOf ``Transport.Differentiation ||
      type.getAppFn.isConstOf ``Transport.Leading then
    return some (← coefficients args.back!)
  if type.getAppFn.isConstOf ``Transport.PowerData then
    return some (← coefficients args[args.size - 2]!)
  return none

/-- Observe arithmetic inputs before the supplier or structural traversal
discharges a reached operation. Discovery accepts an unchosen local reader,
retains each operation's local context, and makes no proof claim. A supplied
proof of a larger premise can hide its internal operations; callers collecting
predecessor support must traverse those premises rather than supply them. -/
def inputs (type : Expr) (supply : Supplier) : MetaM (Array Leaf) := do
  let found ← IO.mkRef (#[] : Array Leaf)
  let _ ← leaves type (fun statement => do
    let leaf : Leaf := ⟨← instantiateMVars statement, ← getLCtx, ← getLocalInstances⟩
    if (← leaf.coefficients?).isSome then found.modify (·.push leaf)
    supply statement)
  found.get

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
