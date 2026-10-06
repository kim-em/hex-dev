/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Pari
import HexPrimality.Elab
import Lean.Elab.Command

/-! Explicit batch production/export. The reifier is HexPrimality.Elab's existing
PrimeCert reifier. Exclusive creation and editor gating follow
HexECPPTheory.Compact. Emitted modules import computational Replay alone. -/

open Lean Elab Meta

namespace Hex.Nat.FactorExport

/-- Source and elaboration allocations. -/
structure Budget where
  maxSourceBytes : Nat := 262144
  maxHeartbeats : Nat := 2000000
  maxRecDepth : Nat := 8192

mutual
private def primeText : PrimeCert → String
  | .small n => s!"(Hex.Nat.PrimeCert.small {n})"
  | .pock n fs => s!"(Hex.Nat.PrimeCert.pock {n} [{factorsText fs}])"
  | .pock3 n r s w fs => s!"(Hex.Nat.PrimeCert.pock3 {n} {r} {s} {w} [{factorsText fs}])"
  | .pock3Sieve n r s w m fs =>
      s!"(Hex.Nat.PrimeCert.pock3Sieve {n} {r} {s} {w} {m} [{factorsText fs}])"

private def factorsText : List (Nat × Nat × PrimeCert) → String
  | [] => ""
  | (a, e, c) :: rest =>
      s!"({a}, {e}, {primeText c})" ++ (if rest.isEmpty then "" else ", " ++ factorsText rest)
end

private def powersText (fs : List PrimePower) : String :=
  "[" ++ String.intercalate ", " (fs.map fun e =>
    s!"⟨{e.exponent}, {primeText e.cert}⟩") ++ "]"

private meta def rawExpr (n : Nat) (value : CheckedFactors n) : MetaM Expr := do
  let fs := value.raw.factors.map fun e =>
    mkApp2 (mkConst ``PrimePower.mk) (mkNatLit e.exponent)
      (Hex.PrimalityTactic.reifyPrimeCert e.cert)
  let fs ← mkListLit (mkConst ``PrimePower) fs
  return match value with
  | .complete _ => mkApp2 (mkConst ``Factorization.mk) (mkNatLit n) fs
  | .partialResult _ =>
      mkApp3 (mkConst ``PartialFactorization.mk) (mkNatLit n) fs (mkNatLit value.raw.residual)

/-- Bound and replay acceptance before publishing any text. No proof stored in
compiled search output is trusted: the actual constructor proof is checked anew. -/
meta def validate (n : Nat) (value : CheckedFactors n) (budget : Budget := {}) : MetaM Unit := do
  if budget.maxHeartbeats == 0 || budget.maxRecDepth == 0 then
    throwError "factor export: proof budgets must be positive"
  let limits : ImportBudget := {}
  let raw := value.raw
  unless raw.subject == n && HexArith.bitLength n ≤ limits.maxBits &&
      (raw.factors.take (limits.maxEntries + 1)).length ≤ limits.maxEntries do throwError "factor export: subject/data bounds"
  for e in raw.factors do
    unless e.exponent > 0 && e.exponent ≤ limits.maxExponent &&
        FactorImport.certificateFits limits e.cert do throwError "factor export: certificate bounds"
  let .ok _ := FactorImport.accept n raw | throwError "factor export: checker rejection"
  let ctor := match value with
    | .complete _ => ``CheckedFactorization.mk
    | .partialResult _ => ``CheckedPartialFactorization.mk
  let proof := mkApp4 (mkConst ctor) (mkNatLit n) (← rawExpr n value)
    (← mkEqRefl (mkNatLit n)) Hex.PrimalityTactic.reflTrue
  checkWithKernel proof

/-- Deterministic complete/partial source for fixed checked data. The same
formatter is used for suggestions and exclusive file export. -/
meta def source (name : Name) (n : Nat) (value : CheckedFactors n)
    (budget : Budget := {}) : MetaM String := do
  validate n value budget
  let (rawType, checkedType) := match value with
    | .complete _ => ("Factorization", "CheckedFactorization")
    | .partialResult _ => ("PartialFactorization", "CheckedPartialFactorization")
  let data := match value with
    | .complete _ => s!"⟨{n}, {powersText value.raw.factors}⟩"
    | .partialResult _ => s!"⟨{n}, {powersText value.raw.factors}, {value.raw.residual}⟩"
  let text := s!"module\n\npublic import HexIntFactor.Replay\n\npublic section\n\nset_option maxHeartbeats {budget.maxHeartbeats}\nset_option maxRecDepth {budget.maxRecDepth}\n\n@[expose] def {name} : Hex.Nat.{rawType} :=\n  {data}\n\n@[expose] def {name}_checked : Hex.Nat.{checkedType} {n} :=\n  ⟨{name}, rfl, by decide +kernel⟩\n"
  if text.utf8ByteSize > budget.maxSourceBytes then throwError "factor export: source byte limit"
  return text

private meta def subject (term : Term) : TermElabM Nat :=
  withOptions (maxRecDepth.set · 8192) do
  let e ← Term.elabTermEnsuringType term (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  Hex.PrimalityTactic.checkClosed "integer factorization" e
  let some n ← getNatValue? (← whnf e)
    | throwError "integer factorization: expected a closed transparent natural expression"
  unless ← isDefEq e (mkNatLit n) do throwError "integer factorization: opaque subject"
  if HexArith.bitLength n > 256 then throwError "integer factorization: subject exceeds 256 bits"
  return n

private meta def generate (n : Nat) : MetaM (CheckedFactors n) := do
  let executable := (← IO.getEnv "HEX_INT_FACTOR_GP").getD "gp"
  let result ← Pari.factor n (Hex.Rand.ofSeed n) (executable := executable)
    (cancel := (← readThe Core.Context).cancelTk?)
  for diagnostic in result.diagnostics do
    match diagnostic with
    | .cancelled => throwError "integer factorization: cancelled"
    | .nativeProgress subject attempts _ =>
        logInfo m!"integer factorization: native fallback for {subject} used {attempts} attempts"
    | _ => logInfo m!"integer factorization: {repr diagnostic}"
  let some value := result.value | throwError "integer factorization: no checked result"
  return value

private def asciiName (s : String) : Bool :=
  let alpha := fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
  s != "_" && s.toList.head?.any alpha &&
    s.toList.all (fun c => alpha c || ('0' ≤ c && c ≤ '9'))

private def destination (modName declName : Name) : Except String System.FilePath := do
  unless modName.toString.splitOn "." |>.all asciiName do
    throw "module name must consist of ASCII identifier components"
  unless declName.isAtomic && asciiName declName.toString do
    throw "declaration name must be an identifier without a namespace"
  return .mk ((modName.toString.replace "." "/") ++ ".lean")

private meta def editorInstructions : Command.CommandElabM Bool := do
  if Elab.inServer.get (← getOptions) then
    logInfo m!"Integer factor production runs only in batch builds. Run `lake build +{(← getEnv).mainModule}`, then remove the generation command."
    return true
  return false

/-- Explicit batch-only deterministic frozen-certificate suggestion. -/
syntax (name := suggestCmd) "#int_factor " "for " term : command

@[command_elab suggestCmd] meta def suggest : Command.CommandElab := fun stx => do
  if ← editorInstructions then return
  let `(command| #int_factor for $term:term) := stx | throwUnsupportedSyntax
  let text ← Command.liftTermElabM do
    let n ← subject term
    let value ← generate n
    source `certificate n value
  logInfo m!"Frozen certificate:\n{text}"

/-- Explicit batch export; validate before exclusively creating the destination. -/
syntax (name := exportCmd) "#int_factor_export " ident ident " for " term : command

@[command_elab exportCmd] meta def exportFile : Command.CommandElab := fun stx => do
  if ← editorInstructions then return
  let `(command| #int_factor_export $mod:ident $decl:ident for $term:term) := stx
    | throwUnsupportedSyntax
  let path ← match destination mod.getId decl.getId with
    | .ok path => pure path
    | .error err => throwError "factor export: {err}"
  if ← path.pathExists then throwError "factor export: {path} already exists"
  let text ← Command.liftTermElabM do
    let n ← subject term
    let value ← generate n
    source (mod.getId ++ decl.getId) n value
  if let some parent := path.parent then IO.FS.createDirAll parent
  let handle ← IO.FS.Handle.mk path .writeNew
  handle.putStr text
  handle.flush
  logInfo m!"Wrote {path}. Import {mod.getId}, use {mod.getId ++ decl.getId}_checked, then remove the export command."

end Hex.Nat.FactorExport
