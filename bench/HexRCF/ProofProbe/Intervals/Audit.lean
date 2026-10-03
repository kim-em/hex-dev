/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Intervals.FurtherQuery
import all HexRCF.ProofProbe.Intervals.FurtherQuery
public import HexRCF.ProofProbe.Intervals.FurtherHorner
import all HexRCF.ProofProbe.Intervals.FurtherHorner
public import HexRCF.ProofProbe.Intervals.ReciprocalQuery
import all HexRCF.ProofProbe.Intervals.ReciprocalQuery
public import HexRCF.ProofProbe.Intervals.ReciprocalHorner
import all HexRCF.ProofProbe.Intervals.ReciprocalHorner
public import HexRCF.ProofProbe.Intervals.CubicQuery
import all HexRCF.ProofProbe.Intervals.CubicQuery
public import HexRCF.ProofProbe.Intervals.CubicHorner
import all HexRCF.ProofProbe.Intervals.CubicHorner
public meta import Lean
public meta section
namespace Hex.RCF.ProofProbe.Intervals.Audit
open Lean Meta

private meta structure Counts where
  expressions : ExprMap Unit := {}
  declarations : NameHashSet := {}
  tables : List (Nat × Nat) := []

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
    if e.isAppOfArity `Hex.RCF.RealCoefficients.LiteralSign.Table.mk 6 then
      let split ← entries e.getAppArgs[5]!
      modify fun s => { s with tables := split :: s.tables }
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

private meta def measure (name : Name) : MetaM Json := do
  let some owner := (← getEnv).getModuleIdxFor? name | throwError "probe is not imported"
  let (_, counts) ← (declaration owner name).run {}
  unless !counts.tables.isEmpty do throwError "no literal sign table in quoted proof"
  return Json.mkObj [
    ("proof", toJson name.toString),
    ("local_declarations", toJson counts.declarations.size),
    ("distinct_table_syntax", toJson counts.tables.length),
    ("tables", toJson (counts.tables.reverse.map fun (interval, query) =>
      Json.mkObj [("interval_entries", toJson interval), ("query_entries", toJson query)]))]

run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Intervals.FurtherQuery.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Intervals.FurtherHorner.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Intervals.ReciprocalQuery.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Intervals.ReciprocalHorner.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Intervals.CubicQuery.witness).compress}"
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Intervals.CubicHorner.witness).compress}"
end Hex.RCF.ProofProbe.Intervals.Audit
