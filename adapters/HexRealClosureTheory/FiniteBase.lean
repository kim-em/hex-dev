/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteScalars
public import HexRealClosureTheory.BaseFiniteReplay
public meta import HexRealClosureTheory.FiniteScalars

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

/-- A guarded base interpretation. Its closure proof is supplied by the
validated base history, separately from finite coefficient memberships. -/
structure Base where
  read : Expr
  domain : Expr
  closed : Expr

def Base.ofClosed (closed : Expr) : MetaM Base := do
  let type ← inferType closed
  unless type.getAppFn.isConstOf ``Transport.Closed do
    throwError "expected a guarded base interpretation"
  let args := type.getAppArgs
  return ⟨args[args.size - 2]!, args.back!, closed⟩

private def sameType (proof type : Expr) : MetaM Bool :=
  withTransparency .all do isDefEq (← inferType proof) type

private initialize membershipCache : EnvExtension (PHashMap (Array Expr) Expr) ←
  registerEnvExtension (pure {}) (asyncMode := .local)

private def Base.members (base : Base) (p : Expr) (domains : Supplier) : MetaM Expr := do
  let key := #[base.read, base.domain, base.closed, p]
  let cacheable := !key.any (fun expression => expression.hasFVar || expression.hasMVar)
  if cacheable then
    if let some proof := membershipCache.getState (← getEnv) |>.find? key then
      diagnostic "base: exact coefficient memberships reused"
      return proof
  let size ← mkAppM ``DensePoly.size #[p]
  let type ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let bound ← mkAppM ``Nat.lt #[i, size]
    withLocalDeclD `bound bound fun h => do
      let coefficient ← mkAppM ``DensePoly.coeff #[p, i]
      mkForallFVars #[i, h] (mkApp base.domain coefficient)
  let proof ← build type domains
  if cacheable && !proof.hasFVar then
    modifyEnv fun environment => membershipCache.modifyState environment (·.insert key proof)
  return proof

/-- Use actual finite coefficient memberships to discharge reached base
operations. No equation is asserted outside the guarded domain. -/
def Base.supply (base : Base) (domains previous : Supplier) : Supplier := fun type => do
  let args := type.getAppArgs
  for (target, theoremName, count) in #[
      (``Transport.Sum, ``Transport.Sum.of_closed, 2),
      (``Transport.Product, ``Transport.Product.of_closed, 2),
      (``Transport.Difference, ``Transport.Difference.of_closed, 2),
      (``Transport.Scaling, ``Transport.Scaling.of_closed, 2),
      (``Transport.Differentiation, ``Transport.Differentiation.of_closed, 1),
      (``Transport.Evaluation, ``Transport.Evaluation.of_closed, 2),
      (``Transport.PowerData, ``Transport.PowerData.of_closed, 2)] do
    if type.getAppFn.isConstOf target then
      diagnostic s!"base: begin {target}"
      unless ← withTransparency .all (isDefEq args[args.size - count - 1]! base.read) do
        return ← previous type
      let operands := args.extract (args.size - count) args.size
      diagnostic "base: original reader checked"
      let proofs ← if target == ``Transport.Scaling then
          pure #[← build (mkApp base.domain operands[0]!) domains,
            ← base.members operands[1]! domains]
        else if target == ``Transport.Evaluation then
          pure #[← build (mkApp base.domain operands[1]!) domains,
            ← base.members operands[0]! domains]
        else if target == ``Transport.PowerData || count == 1 then
          pure #[← base.members operands[0]! domains]
        else pure #[← base.members operands[0]! domains, ← base.members operands[1]! domains]
      diagnostic "base: coefficient memberships proved"
      let proof ← withTransparency .all
        (mkAppM theoremName (#[base.read, base.domain, base.closed] ++ operands ++ proofs))
      diagnostic s!"base: {target} supplied"
      return some proof
  if type.getAppFn.isConstOf ``Eq && args.size == 3 then
    let .app read value := args[1]! | return ← previous type
    if ← withTransparency .all (isDefEq read base.read) then
      for theoremName in #[``Transport.Closed.read_zero, ``Transport.Closed.read_one] do
        let proof ← mkAppM theoremName #[base.closed]
        if ← sameType proof type then return some proof
      let cast := value.getAppArgs
      let n? := if value.getAppFn.isConstOf ``Nat.cast ||
          value.getAppFn.isConstOf ``NatCast.natCast then cast.back?
        else if value.getAppFn.isConstOf ``OfNat.ofNat then cast[1]?
        else none
      if let some n := n? then
        if ← isDefEq (← inferType n) (mkConst ``Nat) then
          let proof ← mkAppM ``Transport.Closed.read_natCast #[base.closed, n]
          if ← sameType proof type then return some proof
  previous type

/-- Supply a retained coefficient's domain, sign and zero-reflection premises
from one finite agreement proof. Membership proofs follow the actual literal
list; missing coefficients return no proof. The agreement itself must come
from the base bootstrap, rather than an independent real-sign assumption. -/
private def agreementLookup (agreement : Expr) : Supplier := fun type => do
  let dataType ← inferType agreement
  unless dataType.getAppFn.isConstOf ``Transport.Inventory.Agreement do
    throwError "expected a finite base agreement proof"
  let dataArgs := dataType.getAppArgs
  let domain := dataArgs[dataArgs.size - 4]!
  -- The agreement supplies only these three atomic predicates. In particular,
  -- comparing its domain membership with a structural or quantified premise
  -- can unfold the chosen interpretation's domain before traversal has begun.
  unless type.getAppFn == domain.getAppFn || type.getAppFn.isConstOf ``Eq ||
      type.getAppFn.isConstOf ``Iff do return none
  let mut rest := dataArgs.back!
  let mut earlier : Array Expr := #[]
  while true do
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then return none
    unless literal.getAppFn.isConstOf ``List.cons do
      throwError "base agreement requires a literal finite inventory"
    let args := literal.getAppArgs
    let value := args[1]!
    rest := args[2]!
    let mut member ← mkAppOptM ``List.mem_cons_self #[some args[0]!, some value, some rest]
    for head in earlier.reverse do
      member ← mkAppM ``List.mem_cons_of_mem #[head, member]
    let data := mkApp2 agreement value member
    let mut proofs := #[]
    if type.getAppFn == domain.getAppFn then
      proofs := proofs.push (← mkAppM ``And.left #[data])
    if type.getAppFn.isConstOf ``Eq || type.getAppFn.isConstOf ``Iff then
      let signs ← mkAppM ``And.right #[data]
      if type.getAppFn.isConstOf ``Eq then
        proofs := proofs.push (← mkAppM ``And.left #[signs])
      if type.getAppFn.isConstOf ``Iff then
        proofs := proofs.push (← mkAppM ``And.right #[signs])
    for proof in proofs do
      if ← sameType proof type then return some proof
    earlier := earlier.push value
  return none

/-- Preserve leading coefficients from the same finite sign/zero agreement,
and supply its exact coefficient guards. No nonzero interpretation is assumed
for an unretained coefficient. -/
def agreementSupplier (agreement : Expr) : Supplier := fun type => do
  if type.getAppFn.isConstOf ``Transport.Leading then
    let dataType ← inferType agreement
    unless dataType.getAppFn.isConstOf ``Transport.Inventory.Agreement do
      throwError "expected a finite base agreement proof"
    let args := type.getAppArgs
    let dataArgs := dataType.getAppArgs
    unless ← withTransparency .all (isDefEq args[args.size - 2]! dataArgs[dataArgs.size - 5]!) do
      return none
    let coefficients ← mkAppM ``Transport.Inventory.coefficients #[args.back!]
    let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size - 1) coefficients)
    let data ← build required (agreementLookup agreement)
    let theoremName := ``Transport.Inventory.Agreement.leading
    let mut signature := (← getConstInfo theoremName).type
    let mut parameters : Array (Option Expr) := #[]
    while let .forallE name _ body _ := signature do
      let value := if name == `read then some dataArgs[dataArgs.size - 5]!
        else if name == `S then some dataArgs[dataArgs.size - 4]!
        else if name == `sourceSign then some dataArgs[dataArgs.size - 3]!
        else if name == `targetSign then some dataArgs[dataArgs.size - 2]!
        else if name == `p then some args.back!
        else if name == `data then some data
        else none
      parameters := parameters.push value
      signature := body
    return some (← withTransparency .all (mkAppOptM theoremName parameters))
  agreementLookup agreement type

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
