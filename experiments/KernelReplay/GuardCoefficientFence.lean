/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardCoefficientIndex
public meta import KernelReplay.GuardCoefficientIndex
import all KernelReplay.GuardCoefficientIndex
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientFence
open Lean Meta FiniteData GuardDescriptorInputs

/-- Accept a closed domain proof only at its complete original kernel type.
Literal type mismatches are misses; resource and other errors propagate. -/
private def attempt (began : Nat) (type value : Expr) : MetaM (Option Expr) := do
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `coefficientDomain)
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  match (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.thmDecl { name, levelParams := [], type, value }) none (doCheck := true) with
  | .ok environment =>
    setEnv environment
    return some (mkConst name)
  | .error (.appTypeMismatch ..) => return none
  | .error (.declTypeMismatch ..) => return none
  | .error (.exprTypeMismatch ..) => return none
  | .error error => ofExceptKernelException (Except.error error)

/-- Retain and compile one native coefficient separately from its encoder.
The data declaration is kernel checked and is never inlined into the encoder. -/
private def coefficient (began : Nat) (type value : Expr) : MetaM Expr := do
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `coefficientValue)
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  setEnv (← ofExcept <| Compiler.setInlineAttribute (← getEnv) name .noinline)
  withOptions (Elab.async.set · false) do
    withOptions (fun options => options.setBool `compiler.postponeCompile false) do
      compileDecl declaration
  return mkConst name

/-- Kernel-match the existing zero and unit domain proofs first. Other closed
coefficients use separately compiled data as a native index hint, followed by
an ordinary kernel proof of the complete original guarded-domain proposition. -/
unsafe def prepare (began : Nat) (origin : Base) (agreement : Expr)
    (beforeCompile : Option (Expr → MetaM Unit) := none)
    (compileValue : Expr → MetaM Expr := pure) : MetaM Supplier := do
  let indexed ← GuardCoefficientIndex.prepare began agreement
  let .forallE _ carrier _ _ ← whnf (← inferType origin.read) |
    throwError "coefficient reader has no native carrier"
  let zero ← mkAppM ``Transport.Closed.zero #[origin.closed]
  let unit ← mkAppM ``Transport.Closed.one #[origin.closed]
  let cache ← IO.mkRef ({} : PHashMap Expr Expr)
  return fun type => do
    if type.hasFVar || type.hasMVar || type.hasSorry then return none
    unless type.getAppFn == origin.domain.getAppFn do return none
    let .app predicate wanted := type | return none
    if let some proof := (← cache.get).find? type then return some proof
    for value in #[zero, unit] do
      if let some proof ← attempt began type value then
        cache.modify (·.insert type proof)
        return some proof
    if let some inspect := beforeCompile then inspect type
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"native coefficient fence begins: heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
        handle.flush
    let named ← coefficient began carrier (← compileValue wanted)
    let some value ← indexed (mkApp predicate named) |
      throwError "named coefficient has no original finite inventory position"
    let some proof ← attempt began type value |
      throwError "named coefficient proof does not check at the original domain request"
    cache.modify (·.insert type proof)
    return some proof

end Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientFence
