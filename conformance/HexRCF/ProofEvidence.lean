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

end Hex.RCF.ProofEvidence
