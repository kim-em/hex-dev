/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Elab
public import Lean.Elab.Command

/-!
# Saving elliptic curve primality certificates as short Lean expressions

`ecpp_cert% "rows" using lastPrimeCertificate` stores curves and points in
PARI's row format, together with a HexPrimality certificate for the prime
that ends the chain. Elaboration reconstructs the modular inverses and turns
the result into explicit `Cert` data. `ecpp using` then proves primality by
verifying the complete certificate in Lean's kernel.

Reading a saved expression does not run PARI or search for any of its primes.
The shared export helper creates a Lean module for data from a generator
that has checked the exact saved certificate and its proof.
-/

@[expose] public section

open Lean Elab Meta

namespace Hex.ECPP

/-- A saved elliptic curve primality certificate, encoded as PARI rows and
a HexPrimality certificate for the last prime. Use
`ecpp using (ecpp_cert% "rows" using lastPrimeCertificate)` to prove the
recorded integer prime. This notation reconstructs the certificate's
arithmetic witnesses; it does not invoke PARI or repeat curve search. -/
syntax (name := compactCertTerm) "ecpp_cert% " str " using " term : term

/-- Read a saved certificate's rows and last-prime certificate, reconstruct
the modular inverses, and expose the resulting constructor data for proof
checking. Reject invalid input or exceeded certificate limits. -/
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
  -- Exposed auxiliary data needs a public, globally unique name even when the
  -- enclosing declaration is private. Include the module before asking the
  -- generator to check conflicts; removing privacy afterward loses uniqueness.
  let generator ← getDeclNGen
  let moduleName := (← getEnv).mainModule
  let namePrefix := if isPrivateName generator.namePrefix then
      privateToUserName generator.namePrefix ++ .num (`_ecpp ++ moduleName) 0
    else generator.namePrefix
  let name ← try
      -- Retain the branch indices used by parallel elaboration. The numeric
      -- component delimits the module suffix from user-written namespaces.
      setDeclNGen { generator with namePrefix := namePrefix }
      withExporting <| Term.mkAuxName `ecpp
    finally
      let advanced ← getDeclNGen
      setDeclNGen { advanced with namePrefix := generator.namePrefix }
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

/-- Extract the HexPrimality certificate that proves the last prime in an
ECPP certificate's chain. -/
meta def terminalCert : Cert → Hex.Nat.PrimeCert
  | .base leaf => leaf
  | .step _ _ _ _ _ _ _ child => terminalCert child

/-- Render saved curves and points with their last-prime certificate as an
`ecpp_cert%` expression. Modular inverses are reconstructed when that saved
expression is elaborated, so they need not all appear in the source text. -/
meta def compactSyntax (source : String) (cert : Cert) : MetaM Term := do
  let leaf ← Hex.PrimalityTactic.certificateSyntax (terminalCert cert)
  let source := Syntax.mkStrLit source
  `(term| ecpp_cert% $source:str using $leaf)

set_option hygiene false in
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
    let e ← instantiateMVars e
    Hex.PrimalityTactic.checkClosed "#ecpp_export" e
    let some n ← getNatValue? (← whnf (← instantiateMVars e))
      | throwError "#ecpp_export: expected a closed natural-number numeral"
    unless ← isDefEq e (mkNatLit n) do
      throwError "#ecpp_export: subject must be definitionally transparent"
    generator n
  let fullName := modName ++ declName
  let literal ← Command.liftTermElabM <| compactSyntax source cert
  let definition ← `(command| @[expose] public def $(mkIdent fullName):ident : Hex.ECPP.Cert := $literal)
  let rendered ← Command.liftTermElabM <| PrettyPrinter.ppCommand definition
  let body := s!"module\n\npublic import HexECPPMathlib.Compact\n\n{rendered}\n"
  if let some parent := path.parent then IO.FS.createDirAll parent
  let handle ← IO.FS.Handle.mk path .writeNew
  handle.putStr body
  handle.flush
  logInfo m!"Wrote {path}. Add `public import {modName}` at the top of your file, then use `ecpp using {fullName}`. Remove the export command after generation."

end Hex.ECPP
