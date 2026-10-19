/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.ReprProviderData
public meta import HexRealClosureTheory.ReprProviderData
public meta import HexRealClosure.TowerRepr
public meta import HexRealClosure.RootBytes
public meta import HexRealClosure.TowerBytes
public meta import Lean

public meta section

namespace Hex.RealClosure.Tower.ReprProviderTests

open Lean Meta Elab Command

private unsafe def check (label source : String) : TermElabM Unit := do
  let parsed ← match Parser.runParserCategory (← getEnv) `term source with
    | .ok parsed => pure parsed
    | .error message => throwError "{label}: emitted code did not parse: {message}"
  unless ← Term.evalTerm Bool (mkConst ``Bool) parsed do
    throwError "{label}: emitted reconstruction check failed"

private def bindings := "Hex.RealClosure.Tower.ReprProviderData."
private def tower := "Hex.RealClosure.Tower."

syntax (name := reprProvider) "#repr_provider" : command

@[command_elab reprProvider]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let result := ReprProviderData.samples
  if let .error message := result then
    throwError "registered-provider samples were rejected: {message}"
  let .ok samples := result
    | throwError "registered-provider samples were rejected"
  unless !samples.root.parent.signature.roots.isEmpty &&
      !samples.roots.parent.signature.roots.isEmpty do
    throwError "registered-provider root checks lost their algebraic predecessor"
  unless ((ReprProviderData.baseCatalog 2).read ⟨[ReprProviderData.key 2], 0⟩).isSome &&
      ((ReprProviderData.baseCatalog 2).read ⟨[ReprProviderData.key 1], 0⟩).isNone do
    throwError "changed-version catalog lost its actual validated prefix"
  let packedCases := #[
    ("Element", reprStr samples.element, samples.element.writeText),
    ("Polynomial", reprStr samples.polynomial, samples.polynomial.writeText),
    ("Root", reprStr samples.root, samples.root.writeText),
    ("RootSet", reprStr samples.roots, samples.roots.writeText)]
  for (kind, expression, wire) in packedCases do
    let expected := ReprFormat.quote wire
    let observation := if kind == "Element" then
        " && value.context.sign value.value == 1"
      else if kind == "Polynomial" then
        " && value.context.sign (value.value.coeff 0) == -1" ++
        " && value.context.sign (value.value.coeff 1) == 1"
      else ""
    let source := "let catalog := " ++ bindings ++ "catalog 1; let value : " ++
      tower ++ "Packed" ++ kind ++ " " ++ bindings ++ "registry := " ++ expression ++
      "; value.writeText == " ++ expected ++ observation
    check ("packed " ++ kind) source
    for (label, rejected) in [("changed version", bindings ++ "catalog 2"),
        ("missing provider", bindings ++ "emptyCatalog")] do
      check ("rejected " ++ kind ++ ": " ++ label) ("let catalog := " ++ rejected ++
        "; match " ++ tower ++ "ReprFormat.readPacket " ++ expected ++
        " with | .error _ => false | .ok packet => (match " ++ tower ++
        "Catalog.restore" ++ kind ++ " catalog packet with" ++
        " | .error message => message == \"unknown validated base\" | .ok _ => false)")
  let indexedCases := #[
      ("Root", reprStr samples.root.root, samples.root.writeText),
      ("RootSet", reprStr samples.roots.roots, samples.roots.writeText)]
  for (kind, expression, wire) in indexedCases do
    let expected := ReprFormat.quote wire
    check ("indexed " ++ kind) ("let catalog := " ++ bindings ++ "catalog 1; let parent := (" ++
      tower ++ "Catalog.restore" ++ kind ++ "Text! catalog " ++ expected ++ ").parent; " ++
      "let value : " ++ tower ++ kind ++ " parent := " ++ expression ++
      "; value.writeText == " ++ expected)
  logInfo s!"registered provider reconstruction: {packedCases.size + indexedCases.size} emitted expressions and {packedCases.size * 2} catalog rejections checked"

end Hex.RealClosure.Tower.ReprProviderTests

/-- info: registered provider reconstruction: 6 emitted expressions and 8 catalog rejections checked -/
#guard_msgs in
#repr_provider
