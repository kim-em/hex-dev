/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnMathlib.Oracle
public meta import Lean
public meta import HexRCF.Reify
public meta import HexReflect.Budget

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

/-- The delivered ordered-function interface for exact rational coefficients.
Requested width, when supplied, remains a separate `ApproximationWidth` law. -/
theorem Registration.correct {subject : ℝ} (registration : Registration subject) :
    ApproximationCorrect (Rat.castHom ℝ) subject
      (.ofConstant registration.approximation) :=
  ApproximationCorrect.ofConstant _ _ registration.containment

end Hex.RCF.RealCoefficients

public meta section

namespace Hex.RCF.RealCoefficients.Registration

open Lean Meta Qq

private initialize registry :
    SimplePersistentEnvExtension (Name × Expr) (Array (Name × Expr)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.flatten
    addEntryFn := fun entries entry => entries.push entry
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
    let value ← MetaM.run' (subject name)
    modifyEnv fun env => registry.addEntry env (name, value)
}

/-- Deterministic declaration order, independent of import/attribute order. -/
def names : CoreM (Array Name) := do
  return (registry.getState (← getEnv)).map Prod.fst |>.qsort Name.lt |>.eraseReps

/-- Matching uses reducible definitional equality without assigning caller
metavariables. Every duplicate match is rejected, even if the bounds agree. -/
def sameSubject (left right : Expr) : MetaM Bool := do
  withNewMCtxDepth <| withTransparency .reducible <| isDefEq left right

/-- Read checked candidate signatures without executing unrelated providers. -/
def candidates : MetaM (Array (Name × Expr)) := do
  -- Store the normalized subject at registration time: an unrelated imported
  -- type alias need not expose its body merely to participate in lookup.
  let entries := (registry.getState (← getEnv)).qsort (fun a b => Name.lt a.1 b.1)
  return entries.foldl (fun result entry =>
    if result.any (fun previous => previous.1 == entry.1) then result else result.push entry) #[]

private def validate (entries : Array (Name × Expr)) : MetaM Unit := do
  for i in [:entries.size] do
    for j in [:i] do
      if ← sameSubject entries[i]!.2 entries[j]!.2 then
        throwError "rcf: duplicate constant registrations {entries[j]!.1} and {entries[i]!.1}"

/-- Full registry validation, useful for explicit diagnostics. Tactic consumers
use `used` instead so an unrelated duplicate cannot take over another goal. -/
def entries : MetaM (Array (Name × Expr)) := do
  let entries ← candidates
  validate entries
  return entries

/-- Providers occurring in the supplied sources, in registry order. Whole-subject
matching precedes descent; validation is separate so eligibility stays read-only. -/
def matching (entries : Array (Name × Expr)) (sources : Array Expr) :
    MetaM (Array (Name × Expr)) := do
  let mut names : Array Name := #[]
  for source in sources do
    let (_, found) ← (Meta.transformWithCache (m := StateRefT (Array Name) MetaM)
      source {} (pre := fun e => do
        let matching ← entries.filterM fun (_, subject) => Registration.sameSubject e subject
        if matching.isEmpty then return .continue
        modify fun names => names ++ matching.map Prod.fst
        return .done e) (skipInstances := true)).run names
    names := found
  return entries.filter fun entry => names.contains entry.1

/-- Validate just the matched provider subset. -/
def used (entries : Array (Name × Expr)) (sources : Array Expr) :
    MetaM (Array (Name × Expr)) := do
  let result ← matching entries sources
  validate result
  return result

private def exactRoot (exponent : Expr) : MetaM Bool := do
  let exponent : Q(ℝ) := exponent
  let result ← observing? do
    let ⟨value, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat exponent
      (_inst := q(inferInstance))
    return value
  let some value := result | return false
  return value.num == 1 && value.den ≤ (Hex.Reflect.Budget.default).exponent

private def exactLiteral (value : Expr) : MetaM Bool := do
  let value : Q(ℝ) := value
  let result ← observing? do
    let ⟨value, _, _, _⟩ ← Mathlib.Meta.NormNum.deriveRat value
      (_inst := q(inferInstance))
    return value
  let some value := result | return false
  return value.num.natAbs.log2 + 1 + value.den.log2 + 1 ≤
    (Hex.Reflect.Budget.default).coefficientBits

private partial def exactSyntax (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  let (op, args) := e.getAppFnArgs
  if e.isAppOfArity `Hex.RealAlgebraicNumber.toReal 1 then return true
  if e.isAppOfArity `Real.sqrt 1 then return ← exactSyntax e.appArg!
  if e.isAppOfArity `Real.rpow 2 then
    return (← exactSyntax args[0]!) && (← exactRoot args[1]!)
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv].contains op && args.size == 6 then
    return (← exactSyntax args[4]!) && (← exactSyntax args[5]!)
  if [``Neg.neg, ``Inv.inv].contains op && args.size == 3 then
    return ← exactSyntax args[2]!
  if e.isAppOfArity ``HPow.hPow 6 then
    if (← inferType args[5]!).isConstOf ``Real then
      return (← exactSyntax args[4]!) && (← exactRoot args[5]!)
    unless (← inferType args[5]!).isConstOf ``Nat do return false
    let some n ← getNatValue? args[5]! | return false
    if n > (Hex.Reflect.Budget.default).exponent then return false
    return ← exactSyntax args[4]!
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let some n ← getNatValue? args[1]! | return false
    return n.log2 + 1 ≤ (Hex.Reflect.Budget.default).coefficientBits
  if [``Nat.cast, ``Int.cast, ``Rat.cast, ``RatCast.ratCast,
      ``OfScientific.ofScientific].contains op then return ← exactLiteral e
  return false

/-- Select the supplied frontend before exact reification for opaque registered
subjects outside its scalar syntax/envelope. This is an eligibility check, not
fallback after a solver, budget or replay failure. Small algebraic composites
retain the existing exact path. Checked alias discovery uses the base API. -/
def deferExact (target : Expr) : MetaM Bool := do
  let entries ← candidates
  if entries.isEmpty then return false
  let saved ← saveState
  try
    let mut closed := target
    for id in (Lean.collectFVars {} target).fvarIds do
      if let some binding ← Hex.RCF.Reify.closeCoefficient? (mkFVar id) then
        closed := closed.replaceFVar (mkFVar id) binding.value
    -- Reducible matching may unfold a stored alias. Eligibility must inspect
    -- the syntax in the goal, which the exact frontend will actually parse.
    let (_, defer) ← (Meta.transformWithCache (m := StateRefT Bool MetaM)
      closed {} (pre := fun e => do
        unless ← entries.anyM (fun (_, subject) => sameSubject e subject) do
          return .continue
        unless ← exactSyntax e do modify fun _ => true
        return .done e) (skipInstances := true)).run false
    return defer
  finally saved.restore

end Hex.RCF.RealCoefficients.Registration
