/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Windows.FixedOriginal
import all HexRCF.ProofProbe.Windows.FixedOriginal
public import HexRCF.ProofProbe.Windows.FixedRefined
import all HexRCF.ProofProbe.Windows.FixedRefined
public import HexRCF.ProofProbe.Windows.FurtherOriginal
import all HexRCF.ProofProbe.Windows.FurtherOriginal
public import HexRCF.ProofProbe.Windows.FurtherRefined
import all HexRCF.ProofProbe.Windows.FurtherRefined
public import HexRCF.ProofProbe.Windows.ReciprocalOriginal
import all HexRCF.ProofProbe.Windows.ReciprocalOriginal
public import HexRCF.ProofProbe.Windows.ReciprocalRefined
import all HexRCF.ProofProbe.Windows.ReciprocalRefined
public import HexRCF.ProofProbe.Windows.CubicOriginal
import all HexRCF.ProofProbe.Windows.CubicOriginal
public import HexRCF.ProofProbe.Windows.CubicRefined
import all HexRCF.ProofProbe.Windows.CubicRefined
public meta import Lean
public meta section
namespace Hex.RCF.ProofProbe.Windows.Audit
open Lean Meta

private meta structure Counts where
  expressions : ExprMap Unit := {}
  declarations : NameHashSet := {}
  tables : List (Nat × Nat × Bool) := []

/-- Count the explicit entry list without expanding proof or library bodies. -/
private meta partial def entries (list : Expr) : MetaM (Nat × Nat) := do
  if list.isAppOfArity ``List.nil 1 then return (0, 0)
  unless list.isAppOfArity ``List.cons 3 do throwError "sign entries are not a literal list"
  let entry := list.getAppArgs[1]!
  unless entry.isAppOfArity `Hex.RCF.RealCoefficients.LiteralSign.Entry.mk 4 do
    throwError "sign entry is not a literal constructor"
  let evidence := entry.getAppArgs[3]!
  let (interval, query) ← entries list.getAppArgs[2]!
  if evidence.isAppOfArity ``Option.none 1 then return (interval + 1, query)
  if evidence.isAppOfArity ``Option.some 2 then return (interval, query + 1)
  throwError "sign evidence is not a literal option constructor"

private meta abbrev Scan := StateT Counts MetaM
mutual
  private meta partial def expression (owner : ModuleIdx) (e : Expr) : Scan Unit := do
    if (← get).expressions.contains e then return
    modify fun s => { s with expressions := s.expressions.insert e () }
    if e.isAppOfArity `Hex.RCF.RealCoefficients.LiteralSign.Table.mk 7 then
      let split ← entries e.getAppArgs[5]!
      let window := e.getAppArgs[6]!
      unless window.isAppOfArity ``Option.none 1 || window.isAppOfArity ``Option.some 2 do
        throwError "generator window is not a literal option constructor"
      modify fun s => { s with tables :=
        (split.1, split.2, window.isAppOfArity ``Option.some 2) :: s.tables }
    match e with
    | .app f a => expression owner f; expression owner a
    | .lam _ t b _ | .forallE _ t b _ => expression owner t; expression owner b
    | .letE _ t v b _ => expression owner t; expression owner v; expression owner b
    | .mdata _ b | .proj _ _ b => expression owner b
    | .const name _ =>
        if (← getEnv).getModuleIdxFor? name == some owner then declaration owner name
    | _ => pure ()
  private meta partial def declaration (owner : ModuleIdx) (name : Name) : Scan Unit := do
    if (← get).declarations.contains name then return
    modify fun s => { s with declarations := s.declarations.insert name }
    let info ← getConstInfo name
    let some body := info.value? (allowOpaque := true) |
      throwError "local proof declaration has no available body: {name}"
    expression owner info.type
    expression owner body
end

meta def measure (name : Name) : MetaM Json := do
  let some owner := (← getEnv).getModuleIdxFor? name | throwError "probe is not imported"
  let (_, counts) ← (declaration owner name).run {}
  unless !counts.tables.isEmpty do throwError "no literal sign table in quoted proof"
  return Json.mkObj [
    ("proof", toJson name.toString),
    ("local_declarations", toJson counts.declarations.size),
    ("distinct_table_syntax", toJson counts.tables.length),
    ("tables", toJson (counts.tables.reverse.map fun (interval, query, refined) =>
      Json.mkObj [("interval_entries", toJson interval), ("query_entries", toJson query), ("refined_window", toJson refined)]))]

run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FixedOriginal.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FixedRefined.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FurtherOriginal.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FurtherRefined.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.ReciprocalOriginal.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.ReciprocalRefined.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.CubicOriginal.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.CubicRefined.witness).compress}"
end Hex.RCF.ProofProbe.Windows.Audit
