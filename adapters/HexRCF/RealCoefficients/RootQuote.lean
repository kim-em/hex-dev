/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootReplay
public import HexRealClosure.TowerContext
public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.Tactic

public section
namespace Hex.RCF.RealCoefficients.RootQuote

/-- Restore the exact successful reader equation from its optional result. -/
theorem read_eq {ε α : Type} (reader : Except ε α) (value : α)
    (checked : reader.toOption = some value) : reader = .ok value := by
  cases reader with
  | error message => contradiction
  | ok result =>
    exact congrArg Except.ok (by simpa only [Except.toOption, Option.some.injEq] using checked)

/-- Retain a successful reader equation at the optional-result boundary. -/
theorem read_some {ε α : Type} (reader : Except ε α) (value : α)
    (checked : reader = .ok value) : reader.toOption = some value := by
  rw [checked]
  rfl

/-- Lift a supplied optional reader without changing its accepted value. -/
@[expose] def fromOption {α : Type} (reader : Option α) : Except String α :=
  match reader with
  | none => .error "supplied optional reader rejected its input"
  | some value => .ok value

/-- Recover the original optional-reader equation from its checked lift. -/
theorem option_eq {α : Type} (reader : Option α) (value : α)
    (checked : (fromOption reader).toOption = some value) : reader = some value := by
  cases reader <;> exact checked

end Hex.RCF.RealCoefficients.RootQuote

public meta section

namespace Hex.RCF.RealCoefficients.RootQuote
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RealFormula.Reify

/-- Propose an ordinary equality for a demanded reader boundary, including
scalar decoding and Boolean normalization. A missing proposal leaves other
literal rules available. Every equation is checked against the exact input. -/
abbrev Decoder := Expr → MetaM (Option Expr)

/-- A boundary proposal in the enclosing reflection request. Work performed by
the callback consumes the same budget even when the callback declines.
Return `none` to decline; every structured error, including `providerDeclined`,
is terminal. -/
abbrev DecoderM := Expr → ReifyM (Option Expr)

/-- Reconstructed data and the checked equation from the original reader to
that data. Usage continues the caller's reflection request. -/
structure Result where
  value : Expr
  proof : Expr
  usage : Hex.Reflect.BudgetUsage

private def replayRules : Array (Name × Name × Bool) := #[
  (``Hex.SignDet.Replay.check, ``Hex.SignDet.Replay.check.eq_1, false),
  (``Hex.SignDet.Replay.check, ``Hex.SignDet.Replay.check.eq_2, false),
  (``SignTable.count, ``Replay.table_lookup, false),
  (``Dag.replay?, ``Dag.replay_eq, false),
  (``Dag.step, ``Dag.step_eq, false),
  (``Node.check, ``Node.check_eq, false),
  (``checkMoment, ``checkMoment_eq, false),
  (``TarskiCertificate.checkCached, ``TarskiCertificate.checkCached_eq, false),
  (``TarskiCertificate.check, ``TarskiCertificate.check_eq, false),
  (``Array.toList, ``Array.toList_range, false),
  (``Array.all, ``Array.all_toList, true),
  (``Array.foldlM, ``Array.foldlM_toList, true)]

private def numericHeads : Array Name := #[
  ``Nat.add,``Nat.sub,``Nat.mul,``Nat.div,``Nat.mod,``Nat.pow,``Nat.gcd,
  ``Nat.beq,``Nat.ble,``Nat.land,``Nat.lor,``Nat.xor,``Nat.shiftLeft,``Nat.shiftRight]

private partial def irreducible? (protectedNames : Array Name) (expression : Expr)
    : ReifyM (Option Name) := Core.withIncRecDepth do
  charge .proofNodes 1
  Core.checkSystem "literal reader reducibility boundary"
  let reduced ← withTransparency .default (whnf expression)
  if let some name := reduced.getAppFn.constName? then
    if protectedNames.contains name then return none
    if (← getReducibilityStatus name) == .irreducible then
      if let .defnInfo _ ← getConstInfo name then return some name
  match reduced with
  | .proj _ _ body => irreducible? protectedNames body
  | .mdata _ body => irreducible? protectedNames body
  | _ =>
    if let .proj _ _ body := reduced.getAppFn then
      return ← irreducible? protectedNames body
    if let some name := reduced.getAppFn.constName? then
      if numericHeads.contains name then
        for argument in reduced.getAppArgs do
          if let some stuck ← irreducible? protectedNames argument then return some stuck
    if let .const name _ := reduced.getAppFn then
      -- Quotient elimination has no ordinary recursor metadata.
      if name == ``Quot.lift && reduced.getAppNumArgs == 6 then
        return ← irreducible? protectedNames reduced.getAppArgs[5]!
      if let .recInfo recursor ← getConstInfo name then
        if let some major := reduced.getAppArgs[recursor.getMajorIdx]? then
          return ← irreducible? protectedNames major
    return none

private def protectedNames : Array Name :=
  (replayRules.filterMap fun rule =>
    if #[``Array.toList,``Array.all,``Array.foldlM].contains rule.1 then none else some rule.1).push
      ``Algebraic.Element.codec

private def replayWhnf (expression : Expr) : ReifyM Expr :=
  withoutModifyingEnv <| withFreshCache do
    for name in protectedNames do setReducibilityStatus name .irreducible
    while true do
      charge .proofNodes 1
      Core.checkSystem "literal reader reducibility budget"
      let reduced ← withOptions (fun options => smartUnfolding.set options false) do
        withTransparency .default (whnf expression)
      let some name ← irreducible? protectedNames reduced | return reduced
      setReducibilityStatus name .semireducible
      resetCache
    throwError "rcf: literal reducibility loop terminated unexpectedly"

private def replayProof? (expression : Expr) : ReifyM (Option Expr) := do
  if expression.hasLooseBVars || expression.hasMVar then return none
  let some head := expression.getAppFn.constName? | return none
  for (key,name,inverse) in replayRules do
    if head == key then
      let ruleConst ← mkConstWithFreshMVarLevels name
      let (parameters,_,_) ← forallMetaTelescopeReducing (← inferType ruleConst)
      let proof := mkAppN ruleConst parameters
      let proof ← if inverse then mkEqSymm proof else pure proof
      let type ← inferType proof
      unless type.isAppOfArity ``Eq 3 do throwError "public replay rule is not an equation"
      let lhs := type.getAppArgs[1]!
      if ← withTransparency .all <| isDefEq lhs expression then
        let proof ← instantiateMVars proof
        unless !proof.hasMVar do throwError "public replay rule left unresolved arguments"
        return some proof
  return none

private def codecProof? (decode : DecoderM) (expression : Expr) : ReifyM (Option Expr) := do
  charge .proofNodes 1
  if expression.hasLooseBVars || expression.hasMVar then return none
  if let .proj ``ValueCodec 1 codec := expression.getAppFn then
    if codec.isAppOfArity ``Tower.contextCodec 1 && expression.getAppNumArgs == 1 then
      let proof ← mkAppM ``Tower.contextCodec_self #[codec.appArg!]
      let type ← inferType proof
      if ← withTransparency .all <| withNewMCtxDepth (isDefEq expression type.getAppArgs[1]!) then
        return some proof
  let signatureCodec? := match expression.getAppFn with
    | .proj ``ValueCodec 1 codec =>
      if expression.getAppNumArgs == 1 then some codec else none
    | .const ``ValueCodec.decode _ =>
      if expression.getAppNumArgs == 3 then some expression.getAppArgs[1]! else none
    | _ => none
  if let some codec := signatureCodec? then
    if codec.isConstOf ``Tower.Signature.codec then
      let payload ← withTransparency .all <| whnf expression.getAppArgs.back!
      let signature? := match payload.getAppFn with
        | .proj ``ValueCodec 0 encoder =>
          if encoder.isConstOf ``Tower.Signature.codec && payload.getAppNumArgs == 1 then
            some payload.appArg! else none
        | .const ``ValueCodec.encode _ =>
          if payload.getAppNumArgs == 3 && payload.getAppArgs[1]!.isConstOf ``Tower.Signature.codec then
            some payload.getAppArgs[2]! else none
        | _ => none
      if let some signature := signature? then
        let proof := mkApp (mkConst ``Tower.Signature.codec_lawful) signature
        let kind ← inferType proof
        let statement ← mkEq expression kind.getAppArgs[2]!
        accountProof proof
        return some (← Hex.RCF.checkProof `RootQuote.signature statement
          (mkExpectedPropHint proof statement))
  let saved ← (saveState : MetaM SavedState)
  let candidate ← try decode expression catch error =>
    saved.restore
    throw error
  let some proof := candidate | do
    saved.restore
    return none
  let proof ← instantiateMVars proof
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Eq 3 do throwError "rcf: literal codec proposal is not an equation"
  let statement ← mkEq expression type.getAppArgs[2]!
  let proof := mkExpectedPropHint proof statement
  accountProof proof
  return some (← Hex.RCF.checkProof `RootQuote.codec statement proof)

private def reflexiveProof? (expression : Expr) : ReifyM (Option Expr) := do
  unless expression.getAppFn.isConstOf ``withPtrEqDecEq do return none
  let type ← whnf (← inferType expression)
  unless type.isAppOfArity ``Decidable 1 do return none
  let proposition := type.appArg!
  unless proposition.isAppOfArity ``Eq 3 do return none
  let args := proposition.getAppArgs
  unless ← withTransparency .all <| withNewMCtxDepth (isDefEq args[1]! args[2]!) do return none
  let accepted := mkApp2 (mkConst ``Decidable.isTrue) proposition (← mkEqRefl args[1]!)
  return some (← mkAppM ``Subsingleton.elim #[expression,accepted])
/-- Abstract closed proof helpers together with the protected codec they use. -/
private partial def withDependents (constants : Array (Expr × Expr)) (index : Nat)
    (replace : Expr → Expr) (parameters : Array Expr)
    (consume : (Expr → Expr) → Array Expr → ReifyM (Expr × Expr)) : ReifyM (Expr × Expr) := do
  charge .proofNodes 1
  Core.checkSystem "dependent context telescope"
  if index == constants.size then return ← consume replace parameters
  let (original,type) := constants[index]!
  withLocalDeclD `dependent (replace type) fun parameter => do
    let replaceNext := fun (expression : Expr) =>
      (replace expression).replace fun part => if part == original then some parameter else none
    withDependents constants (index+1) replaceNext (parameters.push parameter) consume

/-- Keep a replay function abstract throughout an enclosing Boolean conversion,
even when its demanded boundary is a fold. Retain codec-constructor
priority and abstract dependent proof helpers before supplying the function. -/
private def contextStep? (current subject rhs motive : Expr) : ReifyM (Option Expr) := do
  let boundary? ← match current.find? (fun part => part.isConstOf ``Algebraic.Element.codec) with
    | some boundary => pure (some boundary)
    | none => do
      unless (← withTransparency .reducible <| whnf (← inferType current)).isConstOf ``Bool &&
          (← withTransparency .reducible <| whnf (← inferType subject)).isConstOf ``Bool do
        return none
      pure (current.find? fun part => protectedNames.any (fun name => part.isConstOf name))
  let some boundary := boundary? | return none
  let boundaryType ← inferType boundary
  let gathered ← IO.mkRef (#[] : Array Expr)
  for expression in #[current,subject,motive] do
    expression.forEach fun part => do
      charge .proofNodes 1
      if part.isConst then
        gathered.modify fun found => if found.contains part then found else found.push part
  let entries ← (← gathered.get).mapM fun expression => do
    pure (expression,← inferType expression)
  let mut dependents : Array (Expr × Expr) := #[]
  let mut changed := true
  while changed do
    changed := false
    for entry in entries do
      charge .proofNodes 1
      unless dependents.any (fun found => found.1 == entry.1) do
        if (entry.2.find? fun part => part == boundary ||
            dependents.any (fun found => part == found.1)).isSome then
          dependents := dependents.push entry
          changed := true
  let (kind,value) ← withLocalDeclD `replay boundaryType fun placeholder => do
    let replace := fun (expression : Expr) =>
      expression.replace fun part => if part == boundary then some placeholder else none
    withDependents dependents 0 replace #[] fun replace parameters => do
      withLocalDeclD `next (replace (← inferType rhs)) fun next => do
        withLocalDeclD `checked (← mkEq (replace subject) next) fun checked => do
          let context := replace motive
          let target ← mkEq (replace current) (context.bindingBody!.instantiate1 next)
          let proof := mkExpectedPropHint (← mkAppM ``congrArg #[context,checked]) target
          let binders := #[placeholder] ++ parameters ++ #[next,checked]
          return (← mkForallFVars binders target,← mkLambdaFVars binders proof)
  accountProof kind
  accountProof value
  let generic ← Hex.RCF.checkProof `RootQuote.contextStep kind value
  return some (mkAppN generic (#[boundary] ++ dependents.map (·.1) ++ #[rhs]))

private def checkedStep (current whole subject law : Expr) : ReifyM (Expr × Expr) := do
  let type ← inferType subject
  let lawType ← inferType law
  let rhs := lawType.getAppArgs[2]!
  let motive ← withLocalDeclD `boundary type fun boundary => do
    let body := whole.replace fun expression => if expression == subject then some boundary else none
    mkLambdaFVars #[boundary] body
  unless motive.bindingBody!.hasLooseBVars do
    throwError "demanded boundary does not occur in its reconstructed reader"
  let next := motive.bindingBody!.instantiate1 rhs
  if next == whole then throwError "demanded boundary made no change"
  let statement ← mkEq current next
  let inspected := subject.consumeMData
  let codec? ← match inspected.getAppFn.consumeMData with
    | .proj ``ValueCodec 1 codec => do
      unless inspected.getAppNumArgs == 1 do
        throwError "rcf: literal codec step expects a complete decode projection"
      pure (some codec)
    | .const ``ValueCodec.decode _ => do
      unless inspected.getAppNumArgs == 3 do
        throwError "rcf: literal codec step expects a complete decode application"
      pure (some inspected.getAppArgs[1]!)
    | _ => pure none
  let boundary? := match codec? with
    | some codec => if codec.getAppFn.isConstOf ``Algebraic.Element.codec then some codec else none
    | none =>
      let head := inspected.getAppFn.consumeMData
      match head.constName? with
      | some name => if protectedNames.contains name && (Expr.find? (fun part => part == head) current).isSome
          then some head else none
      | none => none
  let candidate ← match boundary? with
    | some boundary => do
      -- Keep replay functions abstract during conversion; instantiate with
      -- the actual function and its checked public equation afterwards.
      let boundaryType ← inferType boundary
      let prepared ← liftM <| withLocalDeclD `replayBoundary boundaryType fun placeholder => do
        let replace := fun (e : Expr) =>
          e.replace fun part => if part == boundary then some placeholder else none
        let original := replace current
        if original == current then return none
        let premise ← mkEq (replace subject) (replace rhs)
        withLocalDeclD `checked premise fun h => do
          let target ← mkEq original (replace next)
          let candidate := mkExpectedPropHint (← mkAppM ``congrArg #[replace motive,h]) target
          return some (← mkForallFVars #[placeholder,h] target,
            ← mkLambdaFVars #[placeholder,h] candidate)
      let some (kind,value) := prepared
        | abort (.providerFailure (.invalidProviderEvidence
            ⟨`Hex.RCF.RealCoefficients.RootQuote.boundary,0⟩
            "keep the protected replay boundary explicit before quotation") #[])
      accountProof kind
      accountProof value
      let step ← Hex.RCF.checkProof `RootQuote.boundaryStep kind value
      pure (mkApp2 step boundary law)
    | none => do
      if let some prepared ← contextStep? current subject rhs motive then
        pure (mkApp prepared law)
      else
        pure (mkExpectedPropHint (← mkAppM ``congrArg #[motive,law]) statement)
  accountProof candidate
  let proof ← Hex.RCF.checkProof `RootQuote.step statement candidate
  return (next,proof)


/-- Inspect post-major argument domains with a fresh major. -/
private def trailingDepends (app : Expr) (index : Nat) : ReifyM Bool := do
  let args := app.getAppArgs
  let major := args[index]!
  let beforeMajor := mkAppN app.getAppFn (args.extract 0 index)
  withLocalDeclD `major (← inferType major) fun pivot => do
    let type ← inferType (mkApp beforeMajor pivot)
    forallBoundedTelescope type (some (args.size-index-1)) fun binders _ => do
      for binder in binders do
        if (← inferType binder).containsFVar pivot.fvarId! then return true
      return false

/-- Move a function of a proof by transporting only its proof input. Its
result type must reduce to a type independent of the major and equality. -/
private def proofFunction? (argument domain pivot same : Expr) : ReifyM (Option Expr) := do
  charge .proofNodes 1
  let .forallE _ proofType body _ ← whnf domain | return none
  unless ← isProp proofType do return none
  if proofType.containsFVar same.fvarId! || body.hasLooseBVars then return none
  let resultType ← whnf body
  if resultType.containsFVar pivot.fvarId! || resultType.containsFVar same.fvarId! then
    return none
  let family ← mkLambdaFVars #[pivot] proofType
  let equality ← mkAppM ``congrArg #[family,same]
  withLocalDeclD `proof proofType fun proof => do
    let original ← mkAppM ``Eq.mpr #[equality,proof]
    return some (← mkLambdaFVars #[proof] (mkApp argument original))

/-- Introduce the new proof arguments, retaining independent data and moving
functions of proofs without casting their returned data. -/
private partial def withProofArgs (original : Array Expr) (index : Nat)
    (built pivot same : Expr) (proofs : Array Expr)
    (consume : Array Expr → Expr → ReifyM (Expr × Expr)) : ReifyM (Expr × Expr) := do
  charge .proofNodes 1
  Core.checkSystem "dependent proof telescope"
  if index == original.size then return ← consume proofs built
  let .forallE _ domain _ _ ← whnf (← inferType built)
    | throwError "rcf: dependent recursor lost its trailing telescope"
  if ← isProp domain then
    withLocalDeclD `proof domain fun proof =>
      withProofArgs original (index+1) (mkApp built proof) pivot same (proofs.push proof) consume
  else
    if domain.containsFVar pivot.fvarId! || domain.containsFVar same.fvarId! ||
        proofs.any (fun proof => domain.containsFVar proof.fvarId!) then
      if proofs.any (fun proof => domain.containsFVar proof.fvarId!) then
        throwError "rcf: dependent recursor requires transport of a non-proof argument"
      let some moved ← proofFunction? original[index]! domain pivot same
        | throwError "rcf: dependent recursor requires transport of a non-proof argument"
      return ← withProofArgs original (index+1) (mkApp built moved) pivot same proofs consume
    unless ← withNewMCtxDepth <| isDefEq (← inferType original[index]!) domain do
      throwError "rcf: dependent recursor has incompatible trailing data"
    withProofArgs original (index+1) (mkApp built original[index]!) pivot same proofs consume

/-- Prove transport with an abstract major, then instantiate exact closed data.
Proof arguments and functions of proofs move; independent data is retained. -/
private def transportMajor (app : Expr) (index : Nat) (next step : Expr) : ReifyM Expr := do
  let args := app.getAppArgs
  let major := args[index]!
  let majorType ← inferType major
  let original := args.extract (index+1) args.size
  let beforeMajor := mkAppN app.getAppFn (args.extract 0 index)
  let (kind,value) ← withLocalDeclD `major majorType fun old => do
    let applied := mkApp beforeMajor old
    forallBoundedTelescope (← inferType applied) (some original.size) fun oldArgs _ => do
      let lhs := mkAppN applied oldArgs
      withLocalDeclD `next majorType fun pivot => do
        withLocalDeclD `same (← mkEq old pivot) fun same => do
          withProofArgs oldArgs 0 (mkApp beforeMajor pivot) pivot same #[] fun proofs rhs => do
            let resultType ← whnf (← inferType rhs)
            if resultType.containsFVar pivot.fvarId! || resultType.containsFVar same.fvarId! ||
                proofs.any (fun proof => resultType.containsFVar proof.fvarId!) then
              throwError "rcf: dependent recursor has a varying result type"
            let statement ← mkEq lhs rhs
            let target ← mkForallFVars proofs statement
            let motive ← mkLambdaFVars #[pivot,same] target
            let baseType := (mkApp2 motive old (← mkEqRefl old)).headBeta
            let base ← forallTelescope baseType fun binders equation => do
              mkLambdaFVars binders (mkExpectedPropHint (← mkEqRefl lhs) equation)
            let proof ← mkEqRec motive base same
            let parameters := #[old] ++ oldArgs ++ #[pivot,same] ++ proofs
            return (← mkForallFVars parameters statement,
              ← mkLambdaFVars parameters (mkAppN proof proofs))
  accountProof kind
  accountProof value
  let generic ← Hex.RCF.checkProof `RootQuote.majorTransport kind value
  let families ← withLocalDeclD `next majorType fun pivot => do
    withLocalDeclD `same (← mkEq major pivot) fun same => do
      let mut built := mkApp beforeMajor pivot
      let mut families : Array Expr := #[]
      for argument in original do
        charge .proofNodes 1
        let .forallE _ domain _ _ ← whnf (← inferType built)
          | throwError "rcf: dependent recursor lost its trailing telescope"
        let moved ← if ← isProp domain then do
          let motive ← mkLambdaFVars #[pivot,same] domain
          mkEqRec motive argument same
        else do
          if domain.containsFVar pivot.fvarId! || domain.containsFVar same.fvarId! then
            let some moved ← proofFunction? argument domain pivot same
              | throwError "rcf: dependent recursor requires transport of a non-proof argument"
            pure moved
          else
            pure argument
        families := families.push (← mkLambdaFVars #[pivot,same] moved)
        built := mkApp built moved
      return families
  let mut rebuilt := mkApp beforeMajor next
  let mut proofs : Array Expr := #[]
  for family in families do
    let .forallE _ domain _ _ ← whnf (← inferType rebuilt)
      | throwError "rcf: dependent recursor lost its trailing telescope"
    let moved := (mkApp2 family next step).headBeta
    if ← isProp domain then
      accountProof domain
      accountProof moved
      let sealed ← Hex.RCF.checkProof `RootQuote.movedProof domain moved
      proofs := proofs.push sealed
      rebuilt := mkApp rebuilt sealed
    else
      rebuilt := mkApp rebuilt moved
  let candidate := mkAppN generic (#[major] ++ original ++ #[next,step] ++ proofs)
  let statement ← mkEq app rebuilt
  accountProof rebuilt
  accountProof candidate
  Hex.RCF.checkProof `RootQuote.dependentMajor statement (mkExpectedPropHint candidate statement)

private partial def demanded (decode : DecoderM) (dependent : Expr → ReifyM Expr) (expression : Expr) :
    ReifyM (Option (Expr × Expr × Expr)) := Core.withIncRecDepth do
  charge .proofNodes 1
  Core.checkSystem "demanded literal-reader boundary"
  if let some proof ← replayProof? expression then return some (expression,expression,proof)
  if let some proof ← codecProof? decode expression then return some (expression,expression,proof)
  if let some proof ← reflexiveProof? expression then return some (expression,expression,proof)
  let reduced ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (replayWhnf expression)
  if let some proof ← replayProof? reduced then return some (reduced,reduced,proof)
  if let some proof ← codecProof? decode reduced then return some (reduced,reduced,proof)
  if let some proof ← reflexiveProof? reduced then return some (reduced,reduced,proof)
  match reduced with
  | .proj name index body =>
    let some (expanded,subject,proof) ← demanded decode dependent body | return none
    return some (.proj name index expanded,subject,proof)
  | .mdata metadata body =>
    let some (expanded,subject,proof) ← demanded decode dependent body | return none
    return some (.mdata metadata expanded,subject,proof)
  | _ =>
    if let .proj name index body := reduced.getAppFn then
      let some (expanded,subject,proof) ← demanded decode dependent body | return none
      return some (mkAppN (.proj name index expanded) reduced.getAppArgs,subject,proof)
    if let some name := reduced.getAppFn.constName? then
      if numericHeads.contains name then
        let args := reduced.getAppArgs
        for index in [:args.size] do
          if let some (expanded,subject,proof) ← demanded decode dependent args[index]! then
            return some (mkAppN reduced.getAppFn (args.set! index expanded),subject,proof)
    if let .const name _ := reduced.getAppFn then
      if let .recInfo recursor ← getConstInfo name then
        let args := reduced.getAppArgs
        if name == ``Bool.rec && args.size ≥ 5 then
          let witness := args[4]!
          let reflected := witness.isAppOfArity ``Decidable.reflects_decide 2 ||
            match witness with
            | .proj ``Decidable 1 _ => true
            | _ => false
          if reflected then
            let applied := mkAppN reduced.getAppFn (args.extract 0 5)
            let proof ← dependent applied
            return some (reduced,applied,proof)
        if let some major := args[recursor.getMajorIdx]? then
          let some (expanded,subject,proof) ← demanded decode dependent major | return none
          let index := recursor.getMajorIdx
          if index+1 < args.size && (← trailingDepends reduced index) then
            let (next,step) ← checkedStep major expanded subject proof
            let law ← transportMajor reduced index next step
            return some (reduced,reduced,law)
          return some (mkAppN reduced.getAppFn
            (args.set! index expanded),subject,proof)
    return none

private def checkedBool (decode : DecoderM) (dependent : Expr → ReifyM Expr) (original : Expr) : ReifyM (Bool × Expr) := do
  let mut current := original
  let mut transport ← mkEqRefl original
  while true do
    charge .proofNodes 1
    unless current.isConstOf ``Bool.true || current.isConstOf ``Bool.false do
      if let some law ← codecProof? decode current then
        let next := (← inferType law).getAppArgs[2]!
        if next == current then throwError "Boolean normalization made no change"
        transport ← mkEqTrans transport law
        current := next
        continue
    let reduced ← withOptions (fun options => smartUnfolding.set options false) do
      withTransparency .all (replayWhnf current)
    if reduced.isConstOf ``Bool.true || reduced.isConstOf ``Bool.false then
      let value := reduced.isConstOf ``Bool.true
      let statement ← mkEq original (mkConst (if value then ``Bool.true else ``Bool.false))
      let candidate := mkExpectedPropHint transport statement
      accountProof candidate
      let proof ← Hex.RCF.checkProof `RootQuote.major statement candidate
      return (value,proof)
    let some (whole,subject,law) ← demanded decode dependent reduced
      | do
        let shape := match reduced.getAppFn with
          | .proj name index _ => s!"projection {name}/{index}"
          | .const name _ => toString name
          | _ => "an unsupported expression"
        throwError "rcf: literal Boolean replay remains at {shape}"
    let (next,proof) ← checkedStep current whole subject law
    current := next
    transport ← mkEqTrans transport proof
  throwError "rcf: literal Boolean loop terminated unexpectedly"

private partial def discharge (decode : DecoderM) (node : Expr) : ReifyM Expr := Core.withIncRecDepth do
  Core.checkSystem "dependent decision discharge"
  unless node.isAppOfArity ``Bool.rec 5 do
    throwError "dependent sibling is not a single Boolean reflects_decide argument: {node.getAppFn.constName?}, arguments={node.getAppNumArgs}"
  let args := node.getAppArgs
  let witness := args[4]!
  let (condition,decision) ← do
    if witness.isAppOfArity ``Decidable.reflects_decide 2 then
      let fields := witness.getAppArgs
      pure (fields[0]!,fields[1]!)
    else if let .proj ``Decidable 1 decision := witness then
      let type ← inferType decision
      unless type.isAppOfArity ``Decidable 1 do throwError "invalid decision dictionary"
      pure (type.appArg!,decision)
    else throwError "dependent sibling is not reflects_decide"
  let (value,majorProof) ← checkedBool decode (discharge decode) args[3]!
  let decisionBool := mkApp2 (mkConst ``Decidable.decide) condition decision
  let literal := mkConst (if value then ``Bool.true else ``Bool.false)
  let decisionStatement ← mkEq decisionBool literal
  let candidate := mkExpectedPropHint majorProof decisionStatement
  accountProof candidate
  let decisionProof ← Hex.RCF.checkProof `RootQuote.decision decisionStatement candidate
  let branchProof := mkApp3
    (mkConst (if value then ``of_decide_eq_true else ``of_decide_eq_false))
    condition decision decisionProof
  let branchTarget ← if value then pure condition else mkAppM ``Not #[condition]
  accountProof branchProof
  let branchProof ← Hex.RCF.checkProof `RootQuote.branch branchTarget branchProof
  let alpha ← inferType node
  let level ← getLevel alpha
  let branch := if value then args[2]! else args[1]!
  let proof := mkAppN
    (mkConst (if value then ``dite_eq_left else ``dite_eq_right) [level])
    #[condition,decision,branchProof,alpha,args[2]!,args[1]!]
  let statement ← mkEq node (mkApp branch branchProof)
  let candidate := mkExpectedPropHint proof statement
  accountProof candidate
  let proof ← Hex.RCF.checkProof `RootQuote.discharge statement candidate
  return proof

private partial def quoteCore (reader : Expr) (decode : DecoderM) : ReifyM Result := do
  let reader ← instantiateMVars reader
  accountProof reader
  let reader ← Hex.RCF.checkExpr `RootQuote.reader reader
  Meta.check reader
  let type ← whnf (← inferType reader)
  unless type.isAppOfArity ``Except 2 do
    throwError "rcf: expected a literal Except reader"
  let original ← mkAppM ``Except.toOption #[reader]
  let mut current := original
  let mut transport ← mkEqRefl original
  while true do
    charge .proofNodes 1
    Core.checkSystem "literal root quotation"
    let reduced ← replayWhnf current
    if reduced.getAppFn.isConstOf ``Option.some then
      let value := reduced.getAppArgs.back!
      let conversion ← mkEq current reduced
      let conversion := mkExpectedPropHint (← mkEqRefl reduced) conversion
      let complete ← mkEqTrans transport conversion
      let statement ← mkEq original reduced
      let candidate := mkExpectedPropHint complete statement
      accountProof candidate
      let proof ← Hex.RCF.checkProof `RootQuote.accepted statement candidate
      return ⟨value,proof,(← get).budget.consumed⟩
    if reduced.getAppFn.isConstOf ``Option.none then
      abort (.providerFailure (.invalidProviderEvidence ⟨`Hex.RCF.RealCoefficients.RootQuote,0⟩
        "literal reader rejected its supplied input") #[])
    let some (whole,subject,law) ← demanded decode (discharge decode) reduced
      | throwError "rcf: literal root replay remains at {reduced.getAppFn.constName?}"
    let (next,proof) ← checkedStep current whole subject law
    current := next
    transport ← mkEqTrans transport proof
  throwError "rcf: literal quotation loop terminated unexpectedly"

/-- Quote inside an existing reflection request. Scalar callbacks, replay and
the final checked proof share its budget. Structured callback failures propagate
without trying another rule. The caller supplies the enclosing transaction;
`quote` provides that boundary for an ordinary `MetaM` callback.
A canonical `Algebraic.Element.codec` decode stays protected: supply its exact
checked equation through the callback, or quotation fails closed. The original
reader expression must expose that codec; expand a hiding definition first.
This guarantee covers explicit `Element.codec` applications, not codec aliases.
Dependent recursors transport trailing proofs and functions of one proof into
a fixed type, retaining independent trailing data. Other dependent data
transports and ill-typed abstractions remain terminal. -/
def quoteWith (reader : Expr) (decode : DecoderM := fun _ => pure none) : ReifyM Result :=
  quoteCore reader decode

/-- Quote a supplied `Option` reader and check its original equation. The
lift, nested callbacks and final transport share the enclosing budget. A
rejected reader remains a terminal rejection. The caller supplies the
`runWith` transaction; no source identity or model is synthesized here. -/
def quoteOptionWith (reader : Expr) (decode : DecoderM := fun _ => pure none) : ReifyM Result := do
  let reader ← instantiateMVars reader
  accountProof reader
  let reader ← Hex.RCF.checkExpr `RootQuote.optionReader reader
  Meta.check reader
  let type ← whnf (← inferType reader)
  unless type.isAppOfArity ``Option 1 do
    throwError "rcf: expected a supplied Option reader"
  let lifted := mkApp2 (mkConst ``fromOption) type.appArg! reader
  let result ← quoteWith lifted decode
  let statement ← mkEq reader (← mkAppM ``Option.some #[result.value])
  let candidate := mkAppN (mkConst ``option_eq)
    #[type.appArg!,reader,result.value,result.proof]
  accountProof candidate
  let proof ← Hex.RCF.checkProof `RootQuote.option statement candidate
  return {result with proof,usage := (← get).budget.consumed}

/-- Run checked quotation actions in one reflection request. Their callbacks
and proof construction share its budget; the returned usage includes charges
after the final quoted proof. Success restores caller
metavariables and retains checked auxiliaries and accepted decoder callbacks'
environment effects; rejection or failure restores
the complete saved state. Source identities and real semantics compose with
this reader equation separately. Scalar callbacks share the same reflection
state and budget. The actions perform their own proof checks. No handler is registered here. -/
def runWith (action : ReifyM Result)
    (config : Hex.RealFormula.Reify.Config := {})
    (usage : Hex.Reflect.BudgetUsage := Hex.Reflect.Budget.zero) :
    MetaM (Except Hex.RealFormula.Reify.Error Result) := do
  let saved ← saveState
  let depthLimit := (← readThe Core.Context).maxRecDepth
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `RootQuote)
  let action := (action.run
    {config,budget := {initial := config.ring.budget,consumed := usage}}).run
  let (result,_) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <|
      Core.withIncRecDepth <| withOptions (fun options => maxRecDepth.set
        (debug.skipKernelTC.set (Elab.async.set options false) false) depthLimit) action)
    fun result => do
      match result with
      | some (.ok _) => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | _ => saved.restore
  return result.map fun (value,state) => {value with usage := state.budget.consumed}

/-- Run a literal reader with scalar callbacks in one transactional reflection
request. Nested `quoteWith` calls retain this request's resource accounting.
Canonical `Element.codec` decodes remain protected and require a checked
callback equation; absence of a proposal fails closed. -/
def run (reader : Expr) (decode : DecoderM := fun _ => pure none)
    (config : Hex.RealFormula.Reify.Config := {})
    (usage : Hex.Reflect.BudgetUsage := Hex.Reflect.Budget.zero) :
    MetaM (Except Hex.RealFormula.Reify.Error Result) :=
  runWith (quoteWith reader decode) config usage

/-- Quote with an ordinary `MetaM` scalar callback. This preserves the original
API; callbacks which perform nested quotation use `run` and `quoteWith` to
keep that work in the enclosing reflection request. -/
def quote (reader : Expr) (decode : Decoder := fun _ => pure none)
    (config : Hex.RealFormula.Reify.Config := {})
    (usage : Hex.Reflect.BudgetUsage := Hex.Reflect.Budget.zero) :
    MetaM (Except Hex.RealFormula.Reify.Error Result) :=
  run reader (fun expression => liftM (decode expression)) config usage

end Hex.RCF.RealCoefficients.RootQuote
