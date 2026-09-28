/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Elab
import Lean.Elab.Command

/-!
# Compact frozen ECPP certificates

`ecpp_cert% "PARI rows" using leaf` expands bounded certificate data to raw
constructors during elaboration. It does not run PARI or search for a terminal
prime. The explicit Hex terminal certificate and all generated inverse
witnesses are checked by the ordinary checker and replayed in the kernel.
-/

open Lean Elab Meta

namespace Hex.ECPP

/-- Compact, self-contained source for an ECPP certificate. -/
syntax (name := compactCertTerm) "ecpp_cert% " str " using " term : term

@[term_elab compactCertTerm] meta def elabCompactCert : Term.TermElab := fun stx _ =>
  withOptions (maxRecDepth.set · 65536) do
  let `(term| ecpp_cert% $source:str using $leaf:term) := stx
    | throwUnsupportedSyntax
  let e ← Term.withoutErrToSorry do
    Term.elabTermEnsuringType leaf (mkConst ``Hex.Nat.PrimeCert)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let .base terminal ← readCert (mkApp (mkConst ``Hex.ECPP.Cert.base) e)
    | throwError "ecpp_cert%: expected a terminal PrimeCert"
  let cert ← match convertText defaultImportBudget source.getString terminal with
    | .ok cert => pure cert
    | .error err => throwError "ecpp_cert%: row {err.row}: {repr err.kind}"
  validateCert cert
  -- Keep the enclosing term small so its type can be inferred under the
  -- user's ordinary recursion limit. The exposed body is only raw data.
  let name ← Term.mkAuxName `ecpp
  let decl := Declaration.defnDecl {
    name := name
    levelParams := []
    type := mkConst ``Hex.ECPP.Cert
    value := reifyCert cert
    hints := .abbrev
    safety := .safe }
  addDecl decl (forceExpose := true)
  compileDecl decl
  return mkConst name

/-- The explicit terminal certificate embedded by a complete ECPP chain. -/
meta def terminalCert : Cert → Hex.Nat.PrimeCert
  | .base leaf => leaf
  | .step _ _ _ _ _ _ _ child => terminalCert child

/-- Freeze conversion inputs, avoiding the expanded inverse transcript in source. -/
meta def compactSyntax (source : String) (cert : Cert) : MetaM Term := do
  let leaf ← Hex.PrimalityTactic.certificateSyntax (terminalCert cert)
  let source := Syntax.mkStrLit source
  `(term| ecpp_cert% $source:str using $leaf)

/-- Common explicit export for certificate producers. Validate the destination
before search, then create it exclusively after kernel-checked generation. -/
meta def exportCertificate (mod decl : TSyntax `ident) (term : Term)
    (generator : Nat → MetaM (String × Cert)) : Command.CommandElabM Unit := do
  if Elab.inServer.get (← getOptions) then
    logInfo m!"#ecpp_export writes files only in batch builds. Run `lake build +{(← getEnv).mainModule}` to generate the certificate, then remove this command."
    return
  let modName := mod.getId
  let declName := decl.getId
  let valid := fun (s : String) => s != "_" &&
    (s.toList.head?.any (fun c => c.isAlpha || c == '_')) &&
    s.toList.all (fun c => c.isAlphanum || c == '_')
  unless modName.toString.splitOn "." |>.all valid do
    throwError "#ecpp_export: module name must consist of ASCII identifier components"
  unless declName.isAtomic && valid declName.toString do
    throwError "#ecpp_export: declaration name must be an identifier without a namespace"
  let path := System.FilePath.mk ((modName.toString.replace "." "/") ++ ".lean")
  if ← path.pathExists then throwError "#ecpp_export: {path} already exists"
  let (source, cert) ← Command.liftTermElabM do
    let e ← Term.elabTermEnsuringType term (mkConst ``Nat)
    Term.synthesizeSyntheticMVarsNoPostponing
    Hex.PrimalityTactic.checkClosed "#ecpp_export" e
    let some n ← getNatValue? (← whnf (← instantiateMVars e))
      | throwError "#ecpp_export: expected a closed natural-number numeral"
    unless ← isDefEq e (mkNatLit n) do
      throwError "#ecpp_export: subject must be definitionally transparent"
    generator n
  let fullName := modName ++ declName
  let literal ← Command.liftTermElabM <| compactSyntax source cert
  let definition ← `(command| def $(mkIdent fullName):ident : Hex.ECPP.Cert := $literal)
  let rendered ← Command.liftTermElabM <| PrettyPrinter.ppCommand definition
  let body := s!"import HexECPPMathlib.Compact\n\n{rendered}\n"
  if let some parent := path.parent then IO.FS.createDirAll parent
  let handle ← IO.FS.Handle.mk path .writeNew
  handle.putStr body
  handle.flush
  logInfo m!"Wrote {path}. Add `import {modName}` at the top of your file, then use `ecpp using {fullName}`. Remove the export command after generation."

end Hex.ECPP
