/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.SyntaxFixture
import all HexRCF.ProofProbe.SyntaxFixture
public meta import Lean
public meta section

/-! Count reachable proof syntax without flattening expression sharing.
Imported declarations outside the selected source module remain constant leaves. -/
namespace Hex.RCF.ProofProbe.Syntax
open Lean Meta

private meta structure Work where
  surface : Nat
  expanded : Nat

private meta def Work.add (a b : Work) : Work :=
  ⟨a.surface + b.surface, a.expanded + b.expanded⟩

private meta structure Counts where
  expressions : ExprMap Work := {}
  declarations : Std.HashMap Name Work := {}
  active : NameHashSet := {}

private meta abbrev Audit := StateT Counts MetaM

mutual
  private meta partial def expression (owner : ModuleIdx) (e : Expr) : Audit Work := do
    if let some work := (← get).expressions[e]? then return work
    let children ← match e with
      | .app f a => pure ((← expression owner f).add (← expression owner a))
      | .lam _ t b _ | .forallE _ t b _ =>
          pure ((← expression owner t).add (← expression owner b))
      | .letE _ t v b _ =>
          pure (((← expression owner t).add (← expression owner v)).add (← expression owner b))
      | .mdata _ b | .proj _ _ b => expression owner b
      | .const name _ =>
          if (← getEnv).getModuleIdxFor? name == some owner then
            pure ⟨0, (← declaration owner name).expanded⟩
          else pure ⟨0, 0⟩
      | _ => pure ⟨0, 0⟩
    let work : Work := ⟨1 + children.surface, 1 + children.expanded⟩
    modify fun s => { s with expressions := s.expressions.insert e work }
    return work

  private meta partial def declaration (owner : ModuleIdx) (name : Name) : Audit Work := do
    if let some work := (← get).declarations[name]? then return work
    if (← get).active.contains name then throwError "cyclic local declaration: {name}"
    modify fun s => { s with active := s.active.insert name }
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true) |
      throwError "local declaration has no available body: {name}"
    let work := (← expression owner info.type).add (← expression owner value)
    modify fun s => { s with
      declarations := s.declarations.insert name work
      active := s.active.erase name }
    return work
end

meta def measure (name : Name) : MetaM Json := do
  let some owner := (← getEnv).getModuleIdxFor? name |
    throwError "proof must be imported from its completed source module: {name}"
  let (work, counts) ← (declaration owner name).run {}
  let emitted := counts.declarations.fold (fun total _ work => total + work.surface) 0
  return Json.mkObj [
    ("proof", toJson name.toString),
    ("unique_syntax_nodes", toJson counts.expressions.size),
    ("local_declarations", toJson counts.declarations.size),
    ("local_expression_tree_nodes", toJson emitted),
    ("expanded_local_reference_nodes", toJson work.expanded)]

-- An application with two references to one leaf has three occurrences but
-- two unique nodes. A repeated application has seven occurrences and three nodes.
run_meta do
  let some owner := (← getEnv).getModuleIdxFor? ``Hex.RCF.ProofProbe.SyntaxFixture.token |
    throwError "missing counter fixture module"
  let leaf := mkConst ``True.intro
  let pair := mkApp leaf leaf
  let (work, counts) ← (expression owner pair).run {}
  unless work.surface == 3 && work.expanded == 3 && counts.expressions.size == 2 do
    throwError "incorrect leaf accounting: {work.surface}/{work.expanded}, {counts.expressions.size}"
  let (work, counts) ← (expression owner (mkApp pair pair)).run {}
  unless work.surface == 7 && work.expanded == 7 && counts.expressions.size == 3 do throwError "incorrect shared accounting"
  let mut shared := leaf
  for _ in [:40] do shared := mkApp shared shared
  let (work, counts) ← (expression owner shared).run {}
  unless work.surface == 2 ^ 41 - 1 && work.expanded == 2 ^ 41 - 1 &&
      counts.expressions.size == 41 do
    throwError "incorrect deep DAG accounting"
  let (work, counts) ← (expression owner (mkConst ``Hex.RCF.ProofProbe.SyntaxFixture.token)).run {}
  unless work.surface == 1 && work.expanded == 3 &&
      counts.expressions.size == 3 && counts.declarations.size == 1 do
    throwError "incorrect local-declaration accounting"

end Hex.RCF.ProofProbe.Syntax
