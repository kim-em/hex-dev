/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Lean
public meta section

namespace Hex.RCF.ProofEvidence
open Lean Meta

private meta structure Seen where
  expressions : ExprMap Unit := {}
  declarations : NameHashSet := {}

private meta abbrev Scan := StateT Seen MetaM

mutual
  private meta partial def expression (predicate : Expr → Bool) (e : Expr) : Scan Bool := do
    if (← get).expressions.contains e then return false
    modify fun s => { s with expressions := s.expressions.insert e () }
    if predicate e then return true
    match e with
    | .app f a => return (← expression predicate f) || (← expression predicate a)
    | .lam _ t b _ | .forallE _ t b _ =>
        return (← expression predicate t) || (← expression predicate b)
    | .letE _ t v b _ =>
        return (← expression predicate t) || (← expression predicate v) ||
          (← expression predicate b)
    | .mdata _ b | .proj _ _ b => expression predicate b
    | .const name _ => declaration predicate name
    | _ => return false
  private meta partial def declaration (predicate : Expr → Bool) (name : Name) : Scan Bool := do
    if (← get).declarations.contains name then return false
    modify fun s => { s with declarations := s.declarations.insert name }
    if (← getEnv).getModuleIdxFor? name |>.isSome then return false
    let info ← getConstInfo name
    let some body := info.value? (allowOpaque := true) | return false
    expression predicate body
end

/-- Inspect the actual proof and reachable local auxiliaries, with imported
library bodies as leaves and shared syntax visited once. -/
meta def contains (theoremName : Name) (predicate : Expr → Bool) : MetaM Bool :=
  Prod.fst <$> (declaration predicate theoremName).run {}

/-- Collect declaration types and bodies throughout project modules. Upstream
packages are leaves; imported project declarations are followed. Each name is
visited once, including forbidden entry points before any boundary decision. -/
meta def projectDependencies (roots : Array Name) : MetaM NameHashSet := do
  let environment ← getEnv
  let modules := environment.header.moduleNames
  let mut pending := roots.toList
  let mut seen : NameHashSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some index := environment.getModuleIdxFor? name then
      if #[`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `TauCeti].any
          (fun boundary => boundary.isPrefixOf modules[index]!) then continue
    let declaration ← getConstInfo name
    pending := declaration.type.getUsedConstants.toList ++ pending
    if let some body := declaration.value? (allowOpaque := true) then
      pending := body.getUsedConstants.toList ++ pending
  return seen

private def returnsClass (className : Name) : Expr → Bool
  | .forallE _ _ body _ => returnsClass className body
  | body => body.isAppOfArity className 1

/-- Inspect explicit unary class predicates and closed named applications
returning that class at a literal parameter or its reducible aliases. Bound
applications and opaque parameter equivalences are outside this syntactic
scan. This follows complete project types/bodies with upstream packages as
leaves; it does not evaluate source normalization searches. -/
meta def quotesClass (names : NameHashSet) (className : Name) (common : Expr)
    (expressions : Array Expr := #[]) : MetaM Bool := do
  let visited ← IO.mkRef ({} : ExprMap Unit)
  let comparisons ← IO.mkRef ({} : ExprMap Bool)
  let providers ← IO.mkRef ({} : NameMap Bool)
  let found ← IO.mkRef false
  let rec scan (part : Expr) : MetaM Unit := do
    if (← found.get) || (← visited.get).contains part then return
    visited.modify (fun seen => seen.insert part ())
    let closed := !part.hasLooseBVars && !part.hasFVar && !part.hasMVar
    let mut candidate : Option Expr := none
    if closed && part.isAppOfArity className 1 then
      candidate := some part.getAppArgs[0]!
    else if closed then
      if let some name := part.getAppFn.constName? then
        let provider ← match (← providers.get).find? name with
          | some result => pure result
          | none => do
            let result := returnsClass className (← getConstInfo name).type
            providers.modify (fun seen => seen.insert name result)
            pure result
        if provider then
          let type ← inferType part
          if type.isAppOfArity className 1 then
            candidate := some type.getAppArgs[0]!
    if let some polynomial := candidate then
      let equal ← match (← comparisons.get).get? polynomial with
        | some result => pure result
        | none => do
          let result ← withoutModifyingState (withReducible (isDefEq polynomial common))
          comparisons.modify (fun seen => seen.insert polynomial result)
          pure result
      if equal then found.set true
    match part with
    | .app f a => scan f; scan a
    | .lam _ type body _ | .forallE _ type body _ => scan type; scan body
    | .letE _ type value body _ => scan type; scan value; scan body
    | .mdata _ body | .proj _ _ body => scan body
    | _ => pure ()
  for expression in expressions do scan expression
  let environment ← getEnv
  let modules := environment.header.moduleNames
  for name in names.toArray do
    if let some index := environment.getModuleIdxFor? name then
      if #[`Init,`Lean,`Std,`Batteries,`Mathlib,`Aesop,`Qq,`TauCeti].any
          (fun boundary => boundary.isPrefixOf modules[index]!) then continue
    let info ← getConstInfo name
    scan info.type
    if let some body := info.value? (allowOpaque := true) then scan body
  return ← found.get

end Hex.RCF.ProofEvidence
