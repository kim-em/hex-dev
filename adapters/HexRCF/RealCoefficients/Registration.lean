/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnMathlib.Oracle
public meta import Lean

public section

namespace Hex.RCF.RealCoefficients

open Hex.OrderedFn.Oracle

/-- A caller's finite bounds for one exact closed real subject. Containment is
required; requested-width and progress proofs remain separate. A fixed wide
bound is therefore a valid registration, but may not settle a tactic goal.
In Lean modules, expose the computational definitions needed to prove the
callback's frozen-result equality, and meta-import them in consumers that
execute the callback. The containment theorem itself remains ordinary proof. -/
structure Registration (subject : ℝ) where
  /-- Version included in the finite evidence binding. -/
  version : Nat
  /-- The caller's executable approximation; Hex supplies no analytic provider. -/
  approximation : Rat → Bounds
  /-- Ordinary proof for this exact subject, procedure and positive request. -/
  containment : ∀ δ, 0 < δ → Contains (approximation δ) subject

end Hex.RCF.RealCoefficients

public meta section

namespace Hex.RCF.RealCoefficients.Registration

open Lean Meta

private initialize registry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.flatten
    addEntryFn := fun entries name => entries.push name
  }

/-- Read the indexed subject without evaluating the approximation procedure. -/
def subject (name : Name) : MetaM Expr := do
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do
    throwError "rcf_constant: {name} must be monomorphic"
  let type ← whnf info.type
  unless type.isAppOfArity ``Registration 1 do
    throwError "rcf_constant: {name} must have type Registration subject"
  let value := type.appArg!
  if value.hasFVar || value.hasMVar || value.hasLooseBVars then
    throwError "rcf_constant: {name} needs a closed real subject"
  return value

initialize registerBuiltinAttribute {
  name := `rcf_constant
  descr := "register caller-supplied authenticated finite bounds for rcf"
  applicationTime := .afterCompilation
  add := fun name stx kind => do
    Attribute.Builtin.ensureNoArgs stx
    unless kind == .global do throwAttrMustBeGlobal `rcf_constant kind
    let _ ← MetaM.run' (subject name)
    modifyEnv fun env => registry.addEntry env name
}

/-- Deterministic declaration order, independent of import/attribute order. -/
def names : CoreM (Array Name) := do
  return (registry.getState (← getEnv)).qsort Name.lt |>.eraseReps

/-- Matching uses reducible definitional equality without assigning caller
metavariables. Every duplicate match is rejected, even if the bounds agree. -/
def sameSubject (left right : Expr) : MetaM Bool := do
  withNewMCtxDepth <| withTransparency .reducible <| isDefEq left right

/-- Validate all subjects before any approximation, including duplicate matches. -/
def entries : MetaM (Array (Name × Expr)) := do
  let mut result : Array (Name × Expr) := #[]
  for name in ← names do
    let value ← subject name
    for (previous, other) in result do
      if ← sameSubject value other then
        throwError "rcf: duplicate constant registrations {previous} and {name}"
    result := result.push (name, value)
  return result

end Hex.RCF.RealCoefficients.Registration
