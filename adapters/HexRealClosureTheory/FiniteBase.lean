/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteScalars
public import HexRealClosureTheory.BaseFiniteReplay
public meta import HexRealClosureTheory.FiniteScalars
public meta import HexRealClosureTheory.FiniteIndex

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteData
open Lean Meta

private def diagnostic (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"{message} [heartbeats={(← IO.getNumHeartbeats) / 1000}]"
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

/-- Retain the finite agreement at this reader and guarded domain. A chosen
interpretation may have a shared name while its existence proof still uses
the original choice expression. Closed agreements become kernel-checked
theorems; open agreements retain their hypotheses for subsequent kernel checks. -/
def Base.bindAgreement (base : Base) (agreement : Expr) : MetaM Expr := do
  diagnostic "base agreement: begin named reader binding"
  let agreement ← instantiateMVars agreement
  let obtained ← instantiateMVars (← inferType agreement)
  for value in #[agreement, obtained, base.read, base.domain, base.closed] do
    if (← instantiateMVars value).hasMVar then
      throwError "incomplete finite base agreement"
  unless obtained.getAppFn.isConstOf ``Transport.Inventory.Agreement do
    throwError "expected a finite base agreement proof"
  let args := obtained.getAppArgs
  let required := mkAppN obtained.getAppFn
    (args.set! (args.size - 5) base.read |>.set! (args.size - 4) base.domain)
  let proof ← withTransparency .all do
    mkAppOptM ``id #[some required, some agreement]
  diagnostic "base agreement: named reader conversion checked"
  let proof ← instantiateMVars proof
  let required ← instantiateMVars required
  if required.hasMVar || proof.hasMVar || proof.hasSorry then
    throwError "incomplete finite base agreement"
  if required.hasFVar || proof.hasFVar then return proof
  let _ ← auditProof proof required
  let name := mkPrivateName (← getEnv) (← mkFreshUserName `__finiteBaseAgreement)
  let levels := collectLevelParams (collectLevelParams {} required) proof |>.params.toList
  let declaration := Declaration.thmDecl {
    name, levelParams := levels, type := required, value := proof }
  let options := (← getOptions).setBool `debug.skipKernelTC false
  setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
    (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
    declaration none (doCheck := true))
  diagnostic "base agreement: named proof kernel checked"
  return mkConst name (levels.map Level.param)

private def sameType (proof type : Expr) : MetaM Bool :=
  withNewMCtxDepth do
    withTransparency .all do isDefEq (← inferType proof) type

private def same (left right : Expr) : MetaM Bool := do
  if left == right then return true
  withNewMCtxDepth do withTransparency .all (isDefEq left right)

-- Follow arithmetic operands and native coefficient wrappers, without
-- traversing dictionaries or context signatures. A reached natural cast is
-- only a proof-search hint: its complete guarded proposition must still match.
private def naturalCasts (limit : Nat) (coefficient : Expr) : MetaM (Array Expr) := do
  let carrier ← inferType coefficient
  let mut pending := [coefficient]
  let mut seen : ExprSet := {}
  let mut result := #[]
  for _ in [:limit] do
    let value :: rest := pending | break
    pending := rest
    if seen.contains value then continue
    seen := seen.insert value
    let head := value.getAppFn
    let args := value.getAppArgs
    let candidate := if head.isConstOf ``Nat.cast || head.isConstOf ``NatCast.natCast then
        args.back?
      else if head.isConstOf ``OfNat.ofNat then args[1]?
      else none
    if let some n := candidate then
      let target ← inferType value
      let allowed ← if target.isConstOf ``Rat || target.getAppFn.isConstOf ``RationalFn then
          pure true
        else same target carrier
      if allowed && (← same (← inferType n) (mkConst ``Nat)) then
        unless n.rawNatLit? == some 0 || n.rawNatLit? == some 1 || result.contains n do
          result := result.push n
        continue
    let children := if head.isConstOf ``BaseContext.Element.mk ||
        head.isConstOf ``BaseContext.Element.stored || head.isConstOf ``RationalFn.C then
        args.extract (args.size - 1) args.size
      else if head.isConstOf ``HAdd.hAdd || head.isConstOf ``HMul.hMul ||
          head.isConstOf ``HSub.hSub || head.isConstOf ``Add.add ||
          head.isConstOf ``Mul.mul || head.isConstOf ``Sub.sub then
        args.extract (args.size - 2) args.size
      else #[]
    if children.isEmpty then
      let reduced ← withTransparency .all (whnf value)
      if reduced != value then pending := reduced :: pending
    else
      pending := children.toList ++ pending
  return result

/-- Use the guarded reader's zero, unit and reached natural-cast memberships
before searching its finite inventory. Match the complete guarded proposition
without assigning caller metavariables. -/
def Base.domains (base : Base) (previous : Supplier) : Supplier := fun type => do
  unless type.getAppFn == base.domain.getAppFn do return ← previous type
  let .app predicate wanted := type | return ← previous type
  unless ← same predicate base.domain do return ← previous type
  for theoremName in #[``Transport.Closed.zero, ``Transport.Closed.one] do
    let proof ← mkAppM theoremName #[base.closed]
    if ← sameType proof type then
      diagnostic s!"base domain: closed membership supplied by {theoremName}"
      return some proof
  for n in (← withNewMCtxDepth (naturalCasts 128 wanted)) do
    let proof ← mkAppM ``Transport.Closed.natCast #[base.closed, n]
    if ← sameType proof type then
      diagnostic "base domain: closed natural-cast membership supplied"
      return some proof
  previous type

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
      unless ← same args[args.size - count - 1]! base.read do
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
      -- Elaborate the guarded reader and dictionaries. The actual
      -- operands and membership proofs remain explicit theorem arguments,
      -- checked by the enclosing ordinary-kernel proof boundary.
      let guarded ← withTransparency .all
        (mkAppM theoremName #[base.read, base.domain, base.closed])
      let proof := mkAppN guarded (operands ++ proofs)
      diagnostic s!"base: {target} supplied"
      return some proof
  if type.getAppFn.isConstOf ``Eq && args.size == 3 then
    let .app read value := args[1]! | return ← previous type
    if ← same read base.read then
      for theoremName in #[``Transport.Closed.read_zero, ``Transport.Closed.read_one] do
        let proof ← mkAppM theoremName #[base.closed]
        if ← sameType proof type then return some proof
      let cast := value.getAppArgs
      let n? := if value.getAppFn.isConstOf ``Nat.cast ||
          value.getAppFn.isConstOf ``NatCast.natCast then cast.back?
        else if value.getAppFn.isConstOf ``OfNat.ofNat then cast[1]?
        else none
      if let some n := n? then
        if ← same (← inferType n) (mkConst ``Nat) then
          let proof ← mkAppM ``Transport.Closed.read_natCast #[base.closed, n]
          if ← sameType proof type then return some proof
  previous type

private def agreementMember (elementType value rest : Expr) (earlier : Array Expr) :
    MetaM Expr := do
  let mut member ← mkAppOptM ``List.mem_cons_self #[some elementType, some value, some rest]
  for head in earlier.reverse do
    member ← mkAppM ``List.mem_cons_of_mem #[head, member]
  return member

private def agreementHead (agreement : Expr) : Supplier := fun type => withNewMCtxDepth do
  let agreement ← instantiateMVars agreement
  let type ← instantiateMVars type
  if agreement.hasMVar || type.hasMVar || agreement.hasSorry || type.hasSorry then return none
  let data ← inferType agreement
  unless data.getAppFn.isConstOf ``Transport.Inventory.Agreement do return none
  let parameters := data.getAppArgs
  let inventory := parameters.back!
  if inventory.hasFVar || inventory.hasMVar then return none
  let domain := parameters[parameters.size - 4]!
  let .app predicate wanted := type | return none
  unless predicate == domain && wanted.getAppFn.isConstOf ``DensePoly.coeff do return none
  let literal ← withTransparency .all (whnf inventory)
  unless literal.getAppFn.isConstOf ``List.cons do return none
  let arguments := literal.getAppArgs
  let value := arguments[1]!
  let reduced ← withTransparency .all (whnf wanted)
  unless ← withTransparency .all (isDefEq value reduced) do return none
  let member ← mkAppOptM ``List.mem_cons_self
    #[some arguments[0]!, some value, some arguments[2]!]
  let proof ← mkAppM ``And.left #[mkApp2 agreement value member]
  let proof ← withTransparency .all do mkAppOptM ``id #[some type, some proof]
  let proof ← instantiateMVars proof
  unless (← instantiateMVars (← inferType proof)) == type do return none
  if proof.hasMVar || proof.hasSorry then return none
  diagnostic "base domain: first retained coefficient supplied"
  return some proof

/-- Supply a retained coefficient's domain, sign and zero-reflection premises
from one finite agreement proof. Membership proofs follow the actual literal
list; missing coefficients return no proof. The agreement itself must come
from the base bootstrap, rather than an independent real-sign assumption. -/
private def agreementLookup (agreement : Expr) (cache : Option CoefficientCache) : Supplier :=
    fun type => do
  if let some proof ← agreementHead agreement type then return some proof
  let indexed := match cache with
    | some cache => lookupCoefficientCached agreement cache
    | none => lookupCoefficient agreement
  if let some proof ← indexed type then return some proof
  let domainRequest := type.getAppFn.isConstOf ``BaseContext.Context.partialDomain
  if domainRequest then diagnostic "base domain: begin agreement type inference"
  let dataType ← inferType agreement
  if domainRequest then diagnostic "base domain: agreement type inferred"
  unless dataType.getAppFn.isConstOf ``Transport.Inventory.Agreement do
    throwError "expected a finite base agreement proof"
  let dataArgs := dataType.getAppArgs
  let domain := dataArgs[dataArgs.size - 4]!
  if domainRequest then
    diagnostic s!"base domain: requested head {type.getAppFn.constName?}, agreement domain head {domain.getAppFn.constName?}"
  -- The agreement supplies only these three atomic predicates. In particular,
  -- comparing its domain membership with a structural or quantified premise
  -- can unfold the chosen interpretation's domain before traversal has begun.
  unless type.getAppFn == domain.getAppFn || type.getAppFn.isConstOf ``Eq ||
      type.getAppFn.isConstOf ``Iff do return none
  -- Compare coefficients before constructing membership proofs for unrelated
  -- entries. Definitional equality identifies the complete
  -- guarded proposition; enclosing kernel checks validate the projected proof.
  -- The final pass retains general predicate lookup.
  if type.getAppFn == domain.getAppFn then
    let .app predicate _ := type | return none
    unless ← same predicate domain do return none
    if let some wanted := type.getAppArgs.back? then
      if domainRequest then
        diagnostic s!"base domain: coefficient request head {wanted.getAppFn.constName?}"
        if wanted.getAppFn.isConstOf ``DensePoly.coeff then
          if (← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE").isSome then
            let printed ← withOptions (fun options => pp.maxSteps.set options 100) do
              ppExpr wanted.getAppArgs.back!
            diagnostic s!"base domain: requested index {printed}"
      if domainRequest then diagnostic "base domain: begin coefficient scan"
      -- Reduce the requested coefficient once before comparing it with each
      -- retained entry. The complete guarded proposition is still checked
      -- against the original request before returning its proof.
      let reduced ← withTransparency .all (whnf wanted)
      if domainRequest then
        if (← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE").isSome then
          let printed ← withOptions (fun options => pp.maxSteps.set options 200) do
            ppExpr reduced
          diagnostic s!"base domain: reduced coefficient {printed}"
      let mut rest := dataArgs.back!
      let mut earlier : Array Expr := #[]
      while true do
        let literal ← withTransparency .all (whnf rest)
        if literal.getAppFn.isConstOf ``List.nil then break
        unless literal.getAppFn.isConstOf ``List.cons do
          throwError "base agreement requires a literal finite inventory"
        let args := literal.getAppArgs
        let value := args[1]!
        rest := args[2]!
        let exact := value == wanted
        let same ← if exact then pure true else withNewMCtxDepth do
          withTransparency .all (isDefEq value reduced)
        if same then
          if domainRequest then
            diagnostic s!"base domain: coefficient matched after {earlier.size} entries, aliases {!exact}"
          let member ← agreementMember args[0]! value rest earlier
          let proof ← mkAppM ``And.left #[mkApp2 agreement value member]
          if domainRequest then diagnostic "base domain: matching membership projected"
          if ← sameType proof type then
            if domainRequest then diagnostic "base domain: complete guarded type checked"
            return some proof
        earlier := earlier.push value
      if domainRequest then
        diagnostic s!"base domain: exhausted {earlier.size} coefficient entries"
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
    let member ← agreementMember args[0]! value rest earlier
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

-- Unfold closed, unapplied support aliases, stopping before coefficient
-- enumeration or opaque packet inventories. Unsupported shapes use the
-- existing literal membership supplier.
private def supportHead (value : Expr) : MetaM Expr := do
  let mut value := value
  for _ in [:64] do
    if value.getAppFn.isConstOf ``List.append || value.getAppFn.isConstOf ``List.cons ||
        value.getAppFn.isConstOf ``List.nil ||
        value.getAppFn.isConstOf ``Transport.Inventory.coefficients then return value
    let .const name levels := value | return value
    let .defnInfo info ← getConstInfo name | return value
    value := info.value.instantiateLevelParams info.levelParams levels
  return value

private def coefficientPath (inventory function : Expr) : MetaM (Option (Array Nat)) := do
  let mut pending := [(inventory, #[])]
  for _ in [:10000] do
    let (value, path) :: rest := pending | return none
    pending := rest
    let value ← supportHead value
    let args := value.getAppArgs
    if value.getAppFn.isConstOf ``Transport.Inventory.coefficients then
      if args == function.getAppArgs then return some path
    else if value.getAppFn.isConstOf ``List.append then
      pending := (args[args.size - 2]!, path.push 0) ::
        (args.back!, path.push 1) :: pending
    else if value.getAppFn.isConstOf ``List.cons then
      pending := (args.back!, path.push 2) :: pending
  return none

-- A whole coefficient list was retained before choosing this interpretation.
-- Project its agreement rather than enumerate its indices and prove each
-- global list position separately. The complete original quantified type,
-- including its bound, coefficient dictionaries and guarded predicate, must
-- match. These are ordinary theorem applications, checked with the enclosing
-- finite-data proof; this adds no proof cache or new trusted boundary.
private def agreementMembers (agreement : Expr) : Supplier := fun type =>
    withNewMCtxDepth <| withTransparency .all do
  let type ← instantiateMVars type
  let agreement ← instantiateMVars agreement
  if type.hasMVar || agreement.hasMVar || type.hasSorry || agreement.hasSorry then return none
  let .forallE _ indexType (.forallE _ bound body _) _ := type | return none
  unless indexType.isConstOf ``Nat do return none
  let .app predicate coefficient := body | return none
  unless coefficient.getAppFn.isConstOf ``DensePoly.coeff do return none
  let args := coefficient.getAppArgs
  unless args.size ≥ 3 && args.back! == .bvar 1 do return none
  let polynomial := args[args.size - 2]!
  if polynomial.hasLooseBVars || predicate.hasLooseBVars then return none
  let bounds := bound.getAppArgs
  if bound.getAppFn.isConstOf ``Nat.lt then
    unless bounds.size == 2 do return none
  else if bound.getAppFn.isConstOf ``LT.lt then
    unless bounds.size == 4 && bounds[0]! == mkConst ``Nat do return none
    unless ← withTransparency .instances (isDefEq bounds[1]! (mkConst ``instLTNat)) do return none
  else return none
  unless bounds[bounds.size - 2]! == .bvar 0 do return none
  let size := bounds.back!
  unless size.getAppFn.isConstOf ``DensePoly.size && size.getAppArgs.back! == polynomial do
    return none
  let agreementType ← inferType agreement
  unless agreementType.getAppFn.isConstOf ``Transport.Inventory.Agreement do return none
  let parameters := agreementType.getAppArgs
  unless predicate == parameters[parameters.size - 4]! do return none
  let inventory := parameters.back!
  if inventory.hasFVar || inventory.hasMVar then return none
  let before ← IO.getNumHeartbeats
  let some path ← coefficientPath inventory coefficient.appFn! | return none
  let mut data := agreement
  for direction in path do
    let inventory := (← inferType data).getAppArgs.back!
    let literal ← supportHead inventory
    if direction < 2 then
      unless literal.getAppFn.isConstOf ``List.append do return none
      let split ← mkAppM ``Transport.Inventory.Agreement.append #[data]
      data ← mkAppM (if direction == 0 then ``And.left else ``And.right) #[split]
    else
      unless literal.getAppFn.isConstOf ``List.cons do return none
      let args := literal.getAppArgs
      let subset ← withLocalDeclD `value args[0]! fun value => do
        let memberType ← mkAppM ``List.Mem #[value, args[2]!]
        withLocalDeclD `member memberType fun member => do
          let lifted ← mkAppM ``List.mem_cons_of_mem #[args[1]!, member]
          mkLambdaFVars #[value, member] lifted
      data ← mkAppM ``Transport.Inventory.Agreement.mono #[data, subset]
  let proof ← mkAppM ``Transport.Inventory.Agreement.members #[data]
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasSorry then return none
  unless ← withTransparency .all (isDefEq (← inferType proof) type) do return none
  diagnostic s!"base support: whole coefficient memberships supplied, depth={path.size} supplyHB={((← IO.getNumHeartbeats)-before)/1000}"
  return some proof

-- Project a reached closed index from its retained whole coefficient block.
-- The natural bound is checked on the original polynomial; no global list
-- position or new proof cache is needed. Unsupported requests keep the
-- individual membership fallback.
private def agreementCoefficient (agreement : Expr) : Supplier := fun type =>
    withNewMCtxDepth <| withTransparency .all do
  let agreement ← instantiateMVars agreement
  let type ← instantiateMVars type
  if agreement.hasMVar || type.hasMVar || agreement.hasSorry || type.hasSorry ||
      type.hasLooseBVars then return none
  let .app predicate coefficient := type | return none
  unless coefficient.getAppFn.isConstOf ``DensePoly.coeff do return none
  let args := coefficient.getAppArgs
  unless args.size ≥ 3 do return none
  let polynomial := args[args.size - 2]!
  let index := args.back!
  if index.hasFVar || index.hasLooseBVars then return none
  let size ← mkAppM ``DensePoly.size #[polynomial]
  let whole ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let bound ← mkAppM ``Nat.lt #[i, size]
    withLocalDeclD `bound bound fun h => do
      mkForallFVars #[i, h] (mkApp predicate (mkApp coefficient.appFn! i))
  let some members ← agreementMembers agreement whole | return none
  let some n ← getNatValue? (← whnf index) | return none
  let some count ← getNatValue? (← whnf size) | return none
  unless n < count do return none
  let bound ← mkAppM ``Nat.lt #[index, size]
  -- Supply Nat's standard decision procedure explicitly: instance search
  -- need not identify a raw Nat.lt application with notation's LT.lt.
  let decision := mkApp2 (mkConst ``Nat.decLt) index size
  let boundProof := mkAppN (mkConst ``of_decide_eq_true)
    #[bound, decision, ← mkEqRefl (mkConst ``Bool.true)]
  let proof := mkApp2 members index boundProof
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasSorry then return none
  unless ← isDefEq (← inferType proof) type do return none
  diagnostic "base support: indexed coefficient supplied from retained block"
  return some proof

/-- Supply coefficient guards and leading coefficients from the same finite
sign/zero agreement. Bounded coefficient-domain goals first project a retained
whole coefficient block, matching its domain, bound and dictionaries. Closed
indices in retained blocks use that same projection and a checked natural
bound. Other shapes use individual membership search. No nonzero interpretation is assumed
for an unretained coefficient. -/
def agreementSupplier (agreement : Expr) (cache : Option CoefficientCache := none) : Supplier :=
    fun type => do
  if let some proof ← agreementMembers agreement type then return some proof
  if let some proof ← agreementCoefficient agreement type then return some proof
  if type.getAppFn.isConstOf ``Transport.Leading then
    let dataType ← inferType agreement
    unless dataType.getAppFn.isConstOf ``Transport.Inventory.Agreement do
      throwError "expected a finite base agreement proof"
    let args := type.getAppArgs
    let dataArgs := dataType.getAppArgs
    unless ← same args[args.size - 2]! dataArgs[dataArgs.size - 5]! do
      return none
    let coefficients ← mkAppM ``Transport.Inventory.coefficients #[args.back!]
    let required := mkAppN dataType.getAppFn (dataArgs.set! (dataArgs.size - 1) coefficients)
    let data ← build required (agreementLookup agreement cache)
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
  agreementLookup agreement cache type

end Hex.RealClosure.Algebraic.KernelReplay.FiniteData
