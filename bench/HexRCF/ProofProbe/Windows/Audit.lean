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


/-- Expand references to the probe's own declarations, including their types.
Imported bodies remain leaves. Memoization computes the unshared tree count
without materializing that tree; this does not measure kernel reductions. -/
private meta structure Sizes where
  expressions : ExprMap Nat := {}
  declarations : NameMap Nat := {}
  active : NameHashSet := {}
  maxNatBits : Nat := 0

private meta def natBits (value : Nat) : Nat := Id.run do
  let mut n := value
  let mut bits := 0
  while n > 0 do
    bits := bits + 1
    n := n / 2
  return bits

private meta abbrev Bodies := NameMap (Expr × Expr)
private meta abbrev SizeScan := StateRefT Sizes MetaM
mutual
  private meta partial def size (bodies : Bodies) (e : Expr) : SizeScan Nat := do
    if let some n ← modifyGet (fun s => (s.expressions[e]?, s)) then return n
    let n ← match e with
      | .app f a => pure <| 1 + (← size bodies f) + (← size bodies a)
      | .lam _ t b _ | .forallE _ t b _ => pure <| 1 + (← size bodies t) + (← size bodies b)
      | .letE _ t v b _ => pure <| 1 + (← size bodies t) + (← size bodies v) + (← size bodies b)
      | .mdata _ b | .proj _ _ b => pure <| 1 + (← size bodies b)
      | .const name _ =>
          if bodies.contains name then pure <| 1 + (← declSize bodies name) else pure 1
      | .lit (.natVal n) =>
          let bits := natBits n
          modify fun s => {s with maxNatBits := max s.maxNatBits bits}
          pure 1
      | _ => pure 1
    modify fun s => {s with expressions := s.expressions.insert e n}
    return n
  private meta partial def declSize (bodies : Bodies) (name : Name) : SizeScan Nat := do
    if let some n ← modifyGet (fun s => (s.declarations.find? name, s)) then return n
    if ← modifyGet (fun s => (s.active.contains name, s)) then
      throwError "cyclic local proof reference: {name}"
    modify fun s => {s with active := s.active.insert name}
    let some (type, body) := bodies.find? name | throwError "missing local proof: {name}"
    let n := (← size bodies type) + (← size bodies body)
    modify fun s => {s with active := s.active.erase name, declarations := s.declarations.insert name n}
    return n
end

meta def measure (name : Name) : MetaM Json := do
  let some owner := (← getEnv).getModuleIdxFor? name | throwError "probe is not imported"
  let (_, counts) ← (declaration owner name).run {}
  unless !counts.tables.isEmpty do throwError "no literal sign table in quoted proof"
  let mut bodies : Bodies := {}
  for decl in counts.declarations.toList do
    let info ← getConstInfo decl
    let some body := info.value? (allowOpaque := true) | throwError "missing proof body: {decl}"
    bodies := bodies.insert decl (info.type, body)
  let (expanded, _) ← (declSize bodies name).run {}
  let windows := counts.expressions.toList.filterMap fun (e, _) =>
    if e.isAppOfArity `Hex.RCF.RealCoefficients.LiteralSign.Window.mk 3 then some e else none
  let regionSizes ← windows.mapM fun e => do
    let (nodes, state) ← (size bodies e).run {}
    return Json.mkObj [("unique_expressions", toJson state.expressions.size),
      ("expanded_nodes", toJson nodes), ("max_nat_bits", toJson state.maxNatBits)]
  let conjunctions := counts.expressions.toList.filter fun (e, _) => e.isAppOfArity ``And.intro 4
  return Json.mkObj [
    ("unique_expressions", toJson counts.expressions.size),
    ("expanded_local_nodes", toJson expanded),
    ("unique_conjunction_apps", toJson conjunctions.length),
    ("window_regions", toJson regionSizes),
    ("proof", toJson name.toString),
    ("local_declarations", toJson counts.declarations.size),
    ("distinct_table_syntax", toJson counts.tables.length),
    ("tables", toJson (counts.tables.reverse.map fun (interval, query, refined) =>
      Json.mkObj [("interval_entries", toJson interval), ("query_entries", toJson query), ("refined_window", toJson refined)]))]

-- Repeated edges contribute repeatedly to expansion but once to memo storage.
run_meta do
  let a := mkConst ``Bool
  let b := mkConst ``Bool.true
  let child := mkApp a b
  let (_, state) ← (size {} (mkApp child child)).run {}
  let (nodes, _) ← (size {} (mkApp child child)).run {}
  unless nodes = 7 && state.expressions.size = 4 do
    throwError "shared-expression expansion accounting failed"
  let localName := `Hex.RCF.ProofProbe.Windows.Audit.synthetic
  let bodies : Bodies := ({} : Bodies).insert localName (a, child)
  let (nodes, state) ← (size bodies (mkApp (mkConst localName) (mkConst localName))).run {}
  unless nodes = 11 && state.declarations.size = 1 do
    throwError "local-declaration reference expansion accounting failed"

run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FixedOriginal.witness).compress}"
run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FixedRefined.witness).compress}"
run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FurtherOriginal.witness).compress}"
run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.FurtherRefined.witness).compress}"
run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.ReciprocalOriginal.witness).compress}"
run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.ReciprocalRefined.witness).compress}"
run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.CubicOriginal.witness).compress}"
run_meta do
  logInfo m!"{(← measure ``Hex.RCF.ProofProbe.Windows.CubicRefined.witness).compress}"
end Hex.RCF.ProofProbe.Windows.Audit
