/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Mixed.Pari
public meta import HexIntFactor.Mixed.Pari
public import HexECPP.ElabData
public meta import HexECPP.ElabData
public import Lean.Elab.Command

public section

/-! Explicit batch mixed suggestions and exclusive exports. Before publishing,
constructor-data admission and subject-bound acceptance are checked in the kernel. -/

open Lean Elab Meta

namespace Hex.Nat.Mixed.FactorExport

/-- Independent frozen-source, syntax, reification and kernel allocations. -/
structure Budget where
  maxSourceBytes : Nat := 2097152
  maxSyntaxNodes : Nat := 1048576
  maxHeartbeats : Nat := 20000000
  maxRecDepth : Nat := 65536

/-- Caller allocations may tighten the supported export ceilings. -/
meta def Budget.cap (b : Budget) : Budget := {
  maxSourceBytes := min b.maxSourceBytes 2097152
  maxSyntaxNodes := min b.maxSyntaxNodes 1048576
  maxHeartbeats := min b.maxHeartbeats 20000000
  maxRecDepth := min b.maxRecDepth 65536 }

private meta def withBudget {α} (budget : Budget) (action : TermElabM α) : TermElabM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget.cap.maxHeartbeats * 1000 }) <|
    withOptions (fun opts => maxRecDepth.set
      (maxHeartbeats.set opts budget.cap.maxHeartbeats) budget.cap.maxRecDepth) <|
      withCurrHeartbeats action

private meta abbrev TextM := StateT Nat (Except String)

/-- Charge each fragment before joining it to bounded output. -/
private meta def emit (s : String) : TextM String := do
  let remaining ← get
  if s.utf8ByteSize > remaining then throw "mixed factor export: source byte limit"
  set (remaining - s.utf8ByteSize)
  return s

mutual
private meta def primeText : PrimeCert → TextM String
  | .small n => emit s!"(Hex.Nat.PrimeCert.small {n})"
  | .pock n fs => do
      let head ← emit s!"(Hex.Nat.PrimeCert.pock {n} ["
      let body ← factorsText fs
      return head ++ body ++ (← emit "])")
  | .pock3 n r s w fs => do
      let head ← emit s!"(Hex.Nat.PrimeCert.pock3 {n} {r} {s} {w} ["
      let body ← factorsText fs
      return head ++ body ++ (← emit "])")
  | .pock3Sieve n r s w m fs => do
      let head ← emit s!"(Hex.Nat.PrimeCert.pock3Sieve {n} {r} {s} {w} {m} ["
      let body ← factorsText fs
      return head ++ body ++ (← emit "])")

private meta def factorsText : List (Nat × Nat × PrimeCert) → TextM String
  | [] => pure ""
  | (a, e, c) :: rest => do
      let head ← emit s!"({a}, {e}, "
      let cert ← primeText c
      let close ← emit ")"
      let sep ← emit (if rest.isEmpty then "" else ", ")
      return head ++ cert ++ close ++ sep ++ (← factorsText rest)
end

private meta def ecppText : Hex.ECPP.Cert → TextM String
  | .base c => do
      let head ← emit "(Hex.ECPP.Cert.base "
      let cert ← primeText c
      return head ++ cert ++ (← emit ")")
  | .step n a b x y d ws child => do
      let head ← emit s!"(Hex.ECPP.Cert.step {n} {a} {b} {x} {y} {d} ["
      let witnesses ← ws.mapM fun w => emit (toString w)
      discard <| emit (String.intercalate "" (List.replicate (ws.length - 1) ", "))
      let close ← emit "] "
      let cert ← ecppText child
      -- Separator bytes are reserved independently before joining witnesses.
      return head ++ String.intercalate ", " witnesses ++ close ++ cert ++ (← emit ")")

private meta def evidenceText : Evidence → TextM String
  | .legacy c => do
      let head ← emit "(Hex.Nat.Mixed.Evidence.legacy "
      let cert ← primeText c
      return head ++ cert ++ (← emit ")")
  | .ecpp c => do
      let head ← emit "(Hex.Nat.Mixed.Evidence.ecpp "
      let cert ← ecppText c
      return head ++ cert ++ (← emit ")")

private meta def powersText (fs : List PrimePower) : TextM String := do
  let head ← emit "["
  let entries ← fs.mapM fun e => do
    let head ← emit s!"⟨{e.prime}, {e.exponent}, "
    let cert ← evidenceText e.cert
    return head ++ cert ++ (← emit "⟩")
  discard <| emit (String.intercalate "" (List.replicate (fs.length - 1) ", "))
  return head ++ String.intercalate ", " entries ++ (← emit "]")

private meta def evidenceExpr : Evidence → Expr
  | .legacy c => mkApp (mkConst ``Evidence.legacy) (Hex.PrimalityTactic.reifyPrimeCert c)
  | .ecpp c => mkApp (mkConst ``Evidence.ecpp) (Hex.ECPP.reifyCert c)

private meta def rawExpr (n : Nat) (value : CheckedFactors n) : MetaM Expr := do
  let fs := value.raw.factors.map fun e =>
    mkApp3 (mkConst ``PrimePower.mk) (mkNatLit e.prime) (mkNatLit e.exponent) (evidenceExpr e.cert)
  let fs ← mkListLit (mkConst ``PrimePower) fs
  return match value with
  | .complete _ => mkApp2 (mkConst ``Factorization.mk) (mkNatLit n) fs
  | .partialResult _ => mkApp3 (mkConst ``PartialFactorization.mk) (mkNatLit n) fs
      (mkNatLit value.raw.residual)

private meta def preflight (n : Nat) (value : CheckedFactors n) : MetaM Unit := do
  let limits : ImportBudget := {}
  let raw := value.raw
  unless raw.subject == n && raw.residual ≤ n && HexArith.bitLength n ≤ limits.maxSubjectBits &&
      (raw.factors.take (limits.maxEntries + 1)).length ≤ limits.maxEntries do
    throwError "mixed factor export: subject/data bounds"
  for e in raw.factors do
    unless HexArith.bitLength e.prime ≤ limits.maxBaseBits && e.exponent > 0 &&
        e.exponent ≤ limits.maxExponent && FactorImport.certificateFits limits e.cert do
      throwError "mixed factor export: certificate bounds"

/-- Preflight raw data, discard compiled producer proofs and kernel-check a
fresh subject-indexed acceptance constructor under finite options. -/
meta def validate (n : Nat) (value : CheckedFactors n) (budget : Budget := {}) : MetaM Unit := do
  let budget := budget.cap
  if budget.maxHeartbeats == 0 || budget.maxRecDepth == 0 then
    throwError "mixed factor export: proof budgets must be positive"
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget.maxHeartbeats * 1000 }) <|
    withOptions (fun opts => maxRecDepth.set (maxHeartbeats.set opts budget.maxHeartbeats) budget.maxRecDepth) <|
    withCurrHeartbeats do
    checkSystem "mixed factor export"
    preflight n value
    let .ok _ := FactorImport.accept n value.raw | throwError "mixed factor export: checker rejection"
    let data ← rawExpr n value
    discard <| Hex.ECPP.auditData data {
      maxNodes := budget.maxSyntaxNodes, numeralBits := 4096
      extraNames := [``Factorization, ``Factorization.mk, ``PartialFactorization,
        ``PartialFactorization.mk, ``PrimePower, ``PrimePower.mk, ``Evidence,
        ``Evidence.legacy, ``Evidence.ecpp] }
    let ctor := match value with
      | .complete _ => ``CheckedFactorization.mk
      | .partialResult _ => ``CheckedPartialFactorization.mk
    let proof := mkApp4 (mkConst ctor) (mkNatLit n) data
      (← mkEqRefl (mkNatLit n)) Hex.PrimalityTactic.reflTrue
    checkSystem "mixed factor export"
    let decl := Declaration.defnDecl {
      name := ← mkAuxDeclName `mixedAcceptance
      levelParams := []
      type := ← inferType proof
      value := proof
      hints := .abbrev
      safety := .safe }
    let opts ← getOptions
    -- Synchronous kernel checking with cancellation; discard the temporary environment.
    match (← getEnv).addDeclCore (Core.getMaxHeartbeats opts).toUSize
        budget.maxRecDepth.toUSize decl (← readThe Core.Context).cancelTk? (doCheck := true) with
    | .ok _ => pure ()
    | .error error => throwKernelException error

/-- Deterministic public exposed data and kernel acceptance, importing replay only. -/
meta def source (name : Name) (n : Nat) (value : CheckedFactors n) (budget : Budget := {}) :
    MetaM String := do
  let budget := budget.cap
  preflight n value
  let (rawType, checkedType) := match value with
    | .complete _ => ("Factorization", "CheckedFactorization")
    | .partialResult _ => ("PartialFactorization", "CheckedPartialFactorization")
  let format : TextM String := do
    let head ← emit s!"module\n\npublic import HexIntFactor.Mixed.Replay\n\npublic section\n\nset_option maxHeartbeats {budget.maxHeartbeats}\nset_option maxRecDepth {budget.maxRecDepth}\n\n@[expose] def {name} : Hex.Nat.Mixed.{rawType} :=\n  ⟨{n}, "
    let fs ← powersText value.raw.factors
    let residual ← emit (match value with
      | .complete _ => ""
      | .partialResult _ => s!", {value.raw.residual}")
    let tail ← emit s!"⟩\n\n@[expose] def {name}_checked : Hex.Nat.Mixed.{checkedType} {n} :=\n  ⟨{name}, rfl, by decide +kernel⟩\n"
    return head ++ fs ++ residual ++ tail
  let text ← match format.run budget.maxSourceBytes with
    | .ok (text, _) => pure text
    | .error error => throwError "{error}"
  validate n value budget
  return text

private meta def dataBudget (b : Budget) : Hex.ECPP.DataBudget := {
  maxNodes := b.maxSyntaxNodes, numeralBits := 4096
  extraNames := [``FactorProposal, ``FactorProposal.mk, ``Evidence, ``Evidence.legacy,
    ``Evidence.ecpp, ``Int, ``Int.ofNat, ``Int.negSucc, ``Option, ``Option.some,
    ``Option.none, ``Neg, ``Neg.neg, ``Int.instNegInt, ``instOfNat] }

private meta unsafe def evalProposalUnsafe (e : Expr) : MetaM FactorProposal :=
  evalExpr FactorProposal (mkConst ``FactorProposal) e

@[implemented_by evalProposalUnsafe]
private meta opaque evalProposal (e : Expr) : MetaM FactorProposal

private meta def readProposal (term : Term) (b : Budget := {}) : TermElabM FactorProposal := do
  let e ← Term.withoutErrToSorry <| Term.elabTermEnsuringType term (mkConst ``FactorProposal)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let data ← Hex.ECPP.auditData e (dataBudget b)
  evalProposal data

private meta def subject (term : Term) : TermElabM Nat := do
  let e ← Term.withoutErrToSorry <| Term.elabTermEnsuringType term (mkConst ``Nat)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  discard <| Hex.ECPP.auditData e { numeralBits := 4096 }
  let some n ← getNatValue? (← whnf e) | throwError "mixed factor: expected a closed natural numeral"
  unless ← isDefEq e (mkNatLit n) do throwError "mixed factor: opaque subject"
  if HexArith.bitLength n > 4096 then throwError "mixed factor: subject exceeds 4096 bits"
  return n

private meta def policy (bits : Option (TSyntax `num)) : MetaM ImportBudget := do
  let bits := bits.map TSyntax.getNat
  if let some bits := bits then
    unless bits == 256 || bits == 512 do throwError "mixed factor: ECPP bits must be 256 or 512"
  return { ecppBits := bits }

private meta def generate (n : Nat) (proposal : FactorProposal) (b : ImportBudget) : MetaM (CheckedFactors n) := do
  let result ← match importFactors b n proposal (Hex.Rand.ofSeed n) with
    | .ok result => pure result
    | .error error => throwError "mixed factor: proposal rejected ({repr error})"
  for piece in result.unresolved do
    logInfo m!"mixed factor: {piece.base}^{piece.exponent}: {repr piece.legacyStop}; {repr piece.stop}"
  return result.value

private meta def generatePari (n : Nat) (b : ImportBudget) : MetaM (CheckedFactors n) := do
  let executable := (← IO.getEnv "HEX_INT_FACTOR_GP").getD "gp"
  let result ← Pari.factor n (Hex.Rand.ofSeed n) b (executable := executable)
    (cancel := (← readThe Core.Context).cancelTk?)
  if let some (.process .cancelled) := result.producer then throwError "mixed factor: cancelled"
  if let some error := result.producer then logInfo m!"mixed factor: {repr error}"
  let some result := result.value | throwError "mixed factor: no checked result"
  return result.value

private meta def asciiName (s : String) : Bool :=
  let alpha := fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
  s != "_" && s.toList.head?.any alpha &&
    s.toList.all (fun c => alpha c || ('0' ≤ c && c ≤ '9'))

private meta def destination (modName declName : Name) : Except String System.FilePath := do
  unless modName.toString.splitOn "." |>.all asciiName do
    throw "module name must consist of ASCII identifier components"
  unless declName.isAtomic && asciiName declName.toString do
    throw "declaration name must be an identifier without a namespace"
  return .mk ((modName.toString.replace "." "/") ++ ".lean")

private meta def editorInstructions : Command.CommandElabM Bool := do
  if Elab.inServer.get (← getOptions) then
    logInfo m!"Mixed factor production runs only in batch builds. Run `lake build +{(← getEnv).mainModule}`, then remove the generation command."
    return true
  return false

/-- Explicit supplied mixed proposal suggestion, with ECPP completion opt-in. -/
syntax (name := mixedSuggest) "#int_factor_mixed" (" (" &"ecpp" " := " num ")")?
  " for " term " using " term : command

/-- Explicit PARI mixed proposal suggestion, with independent completion policy. -/
syntax (name := mixedPariSuggest) "#int_factor_mixed" " (" &"method" " := " &"pari" ")"
  (" (" &"ecpp" " := " num ")")? " for " term : command

@[command_elab mixedSuggest, command_elab mixedPariSuggest]
meta def suggest : Command.CommandElab := fun stx => do
  if ← editorInstructions then return
  let text ← Command.liftTermElabM <| withBudget {} do
    match stx with
    | `(command| #int_factor_mixed $[(ecpp := $bits:num)]? for $term:term using $proposal:term) =>
        let n ← subject term
        let b ← policy bits
        let value ← generate n (← readProposal proposal) b
        source `certificate n value
    | `(command| #int_factor_mixed (method := pari) $[(ecpp := $bits:num)]? for $term:term) =>
        let n ← subject term
        let value ← generatePari n (← policy bits)
        source `certificate n value
    | _ => throwUnsupportedSyntax
  logInfo m!"Try this:\n{text}"

/-- Explicit supplied-data exclusive export, gated out of editor elaboration. -/
syntax (name := mixedExport) "#int_factor_mixed_export" (" (" &"ecpp" " := " num ")")?
  ident ident " for " term " using " term : command

/-- Explicit PARI exclusive export, with ECPP completion opt-in. -/
syntax (name := mixedPariExport) "#int_factor_mixed_export" " (" &"method" " := " &"pari" ")"
  (" (" &"ecpp" " := " num ")")? ident ident " for " term : command

@[command_elab mixedExport, command_elab mixedPariExport]
meta def exportFile : Command.CommandElab := fun stx => do
  if ← editorInstructions then return
  let (mod, decl) ← match stx with
    | `(command| #int_factor_mixed_export $[(ecpp := $_:num)]? $mod:ident $decl:ident for $_:term using $_:term) => pure (mod, decl)
    | `(command| #int_factor_mixed_export (method := pari) $[(ecpp := $_:num)]? $mod:ident $decl:ident for $_:term) => pure (mod, decl)
    | _ => throwUnsupportedSyntax
  let path ← match destination mod.getId decl.getId with
    | .ok path => pure path
    | .error e => throwError "mixed factor export: {e}"
  if ← path.pathExists then throwError "mixed factor export: {path} already exists"
  let text ← Command.liftTermElabM <| withBudget {} do
    match stx with
    | `(command| #int_factor_mixed_export $[(ecpp := $bits:num)]? $_:ident $_:ident for $term:term using $proposal:term) =>
        let n ← subject term
        let value ← generate n (← readProposal proposal) (← policy bits)
        source (mod.getId ++ decl.getId) n value
    | `(command| #int_factor_mixed_export (method := pari) $[(ecpp := $bits:num)]? $_:ident $_:ident for $term:term) =>
        let n ← subject term
        let value ← generatePari n (← policy bits)
        source (mod.getId ++ decl.getId) n value
    | _ => throwUnsupportedSyntax
  if let some parent := path.parent then IO.FS.createDirAll parent
  let handle ← IO.FS.Handle.mk path .writeNew
  handle.putStr text
  handle.flush
  logInfo m!"Wrote {path}. Import {mod.getId} and use {mod.getId ++ decl.getId}_checked."

end Hex.Nat.Mixed.FactorExport
