/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameJoint
public meta import KernelReplay.FrameJoint
public meta import KernelReplay.AxiomClosure
import all KernelReplay.FrameJoint
import all KernelReplay.AxiomClosure
import all HexSignDet.QueryHandle
import all HexSignDet.SelectedSigns

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardNativeFrontier
open Lean Meta Elab

section
variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- Identify the native scalar branch; this does not bound coefficient work. -/
def constantQuery (context : Context E Ctx coeffSign parent) (p : DensePoly E) : Bool :=
  decide ((context.queryPoly p).size ≤ 1)
end

meta section

private def bounded (began : Nat) : MetaM Nat := do
  Core.checkSystem "captured native sign frontier"
  let used := ((← IO.getNumHeartbeats) - began) / 1000
  if used ≥ 1500000 then throwError "aggregate native frontier budget exhausted"
  return 1500000 - used

private def dependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo info => info.type.getUsedConstants
  | .defnInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .thmInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .opaqueInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .ctorInfo info => info.type.getUsedConstants
  | .recInfo info => info.type.getUsedConstants
  | .inductInfo info => info.type.getUsedConstants ++ info.ctors.toArray
  | .quotInfo _ => #[]

private def sourceFacts (began : Nat) : MetaM (Array Name) := do
  let root := ``GuardCapture.second.data
  let reference := `Hex.RealClosure.BaseContext.PackedContext.Realization.reference
  let .thmInfo data ← getConstInfo root | throwError "missing captured data"
  let mut original : NameSet := {}
  for name in data.type.getUsedConstants ++ data.value.getUsedConstants do
    let info ← getConstInfo name
    if let some body := info.value? (allowOpaque := true) then
      if info.type.getAppFn.isConstOf ``SignFact && body.getAppFn.isConstOf ``SignFact.mk &&
          body.getUsedConstants.contains reference then
        original := original.insert name
  unless original.size == 5 do throwError "lost original five source facts"
  let mut found := original.toArray
  let mut queue := #[root]
  let mut queued : NameSet := ({} : NameSet).insert root
  let mut cursor := 0
  while cursor < queue.size do
    let _ ← bounded began
    if queue.size > 150000 then throwError "native frontier graph bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if original.contains name then continue
    let info ← getConstInfo name
    if let some body := info.value? (allowOpaque := true) then
      if info.type.getAppFn.isConstOf ``SignFact && body.getAppFn.isConstOf ``SignFact.mk &&
          body.getUsedConstants.contains reference then
        found := found.push name
    for dependency in dependencies info do
      unless queued.contains dependency do
        queued := queued.insert dependency
        queue := queue.push dependency
  unless found.size == 17 do throwError "native source frontier changed: {found.size}"
  logInfo m!"native frontier discovery: sites={found.size} inspected={cursor}"
  return found

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let sources ← sourceFacts began
  let sourceSet := sources.foldl (fun found name => found.insert name) ({} : NameSet)
  let mut replacements : Array Name := #[]
  let mut replacementMap : NameMap Name := {}
  let mut total : Nat := 0
  let mut constantCount : Nat := 0
  let mut todo := sources
  while !todo.isEmpty do
   let mut deferred : Array Name := #[]
   let mut advanced := false
   for name in todo do
    let info ← getConstInfo name
    let some body := info.value? (allowOpaque := true) | throwError "missing native source body"
    unless body.getAppFn.isConstOf ``SignFact.mk do throwError "source record changed"
    let originalArguments := body.getAppArgs
    let originalPolynomial := originalArguments[originalArguments.size - 3]!
    let originalSign := originalArguments[originalArguments.size - 2]!
    -- Rebuild only these seventeen literal records. No other declarations
    -- are copied, unfolded or cloned, and the original owner type is retained.
    let fields := originalArguments.extract 0 (originalArguments.size - 1)
    if info.type.getUsedConstants.any sourceSet.contains then
      throwError "original owner type depends on another source sign record"
    let fieldDependencies := fields.flatMap Expr.getUsedConstants
    if fieldDependencies.any (fun dependency =>
        sourceSet.contains dependency && !replacementMap.contains dependency) then
      deferred := deferred.push name
      continue
    let restore := fun expression : Expr => expression.replace fun term =>
      match term with
      | .const name levels => (replacementMap.find? name).map (mkConst · levels)
      | _ => none
    let arguments := originalArguments.map restore
    let polynomial := arguments[arguments.size - 3]!
    let sign := arguments[arguments.size - 2]!
    let owner := info.type.getAppArgs.back!
    logInfo m!"native frontier begins: index={replacements.size} source={name} polynomialHash={hash polynomial} signHash={hash sign}"
    let query ← mkAppM ``constantQuery #[owner, polynomial]
    let observed ← withTransparency .all (whnf query)
    unless observed.isConstOf ``Bool.true || observed.isConstOf ``Bool.false do
      throwError "native query classification did not compute a Boolean"
    kernelCheck `__frontierConstantQuery (← mkEq query observed) (← mkEqRefl observed)
    let isConstant := observed.isConstOf ``Bool.true
    if isConstant then constantCount := constantCount + 1
    logInfo m!"native frontier query classification: index={replacements.size} constant={isConstant}"
    let proof ← mkEqRefl sign
    let replacement := mkAppN body.getAppFn (arguments.set! (arguments.size - 1) proof)
    for expression in #[info.type, replacement] do
      if expression.hasFVar || expression.hasMVar || expression.hasSorry then
        throwError "native frontier requires closed original source data"
    let fresh := mkPrivateName (← getEnv) (← mkFreshUserName `__nativeFrontierSign)
    let levels := collectLevelParams (collectLevelParams {} info.type) replacement |>.params.toList
    let remaining ← bounded began
    let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
    let before ← IO.getNumHeartbeats
    setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.defnDecl {
        name := fresh, levelParams := levels, type := info.type, value := replacement,
        hints := .regular 0, safety := .safe }) none (doCheck := true))
    let cost := ((← IO.getNumHeartbeats) - before) / 1000
    for (field, original) in #[(0, originalPolynomial), (1, originalSign)] do
      let value := Expr.proj ``SignFact field (mkConst fresh (levels.map Level.param))
      kernelCheck `__frontierOriginalField (← mkEq value original) (← mkEqRefl original)
    -- Store provenance separately: these comparison theorems mention the old
    -- inputs, while the fresh record never depends on the comparison proof.
    let freshValue := mkConst fresh (levels.map Level.param)
    let sourceValue := mkConst name (info.levelParams.map Level.param)
    let polynomialBinding ← mkEq (Expr.proj ``SignFact 0 freshValue)
      (Expr.proj ``SignFact 0 sourceValue)
    let signBinding ← mkEq (Expr.proj ``SignFact 1 freshValue)
      (Expr.proj ``SignFact 1 sourceValue)
    let bindingType ← mkAppM ``And #[polynomialBinding, signBinding]
    let bindingProof ← mkAppM ``And.intro
      #[← mkEqRefl (Expr.proj ``SignFact 0 sourceValue),
        ← mkEqRefl (Expr.proj ``SignFact 1 sourceValue)]
    let remaining ← bounded began
    let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
    setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.thmDecl {
        name := fresh.appendAfter "_binding", levelParams := levels,
        type := bindingType, value := bindingProof }) none (doCheck := true))
    let _ ← bounded began
    total := total + cost
    replacements := replacements.push fresh
    replacementMap := replacementMap.insert name fresh
    advanced := true
    logInfo m!"native frontier checked: index={replacements.size - 1} kernelHB={cost} replacement={fresh} originalTypeHash={hash info.type}"
   unless advanced do throwError "literal source records have an unresolved dependency cycle"
   todo := deferred
  -- Full private-body dependency auditing is a separate importing driver.
  -- Keep the module's computational data export independent of audit visibility.
  for (record, index) in replacements.zipIdx do
    let value := mkConst record
    let type ← inferType value
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardNativeFrontier ++
      Name.mkSimple s!"sign{index}"
    let remaining ← bounded began
    let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
    setEnv (← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe })
      none (doCheck := true))
  logInfo m!"native module record export: checked={replacements.size} originalFieldsBound=true publicSignAliases=17 dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end

end Hex.RealClosure.Algebraic.KernelReplay.GuardNativeFrontier
