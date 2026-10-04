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

mutual
private meta def primeText : PrimeCert → String
  | .small n => s!"(Hex.Nat.PrimeCert.small {n})"
  | .pock n fs => s!"(Hex.Nat.PrimeCert.pock {n} [{factorsText fs}])"
  | .pock3 n r s w fs => s!"(Hex.Nat.PrimeCert.pock3 {n} {r} {s} {w} [{factorsText fs}])"
  | .pock3Sieve n r s w m fs =>
      s!"(Hex.Nat.PrimeCert.pock3Sieve {n} {r} {s} {w} {m} [{factorsText fs}])"

private meta def factorsText : List (Nat × Nat × PrimeCert) → String
  | [] => ""
  | (a, e, c) :: rest =>
      s!"({a}, {e}, {primeText c})" ++ (if rest.isEmpty then "" else ", " ++ factorsText rest)
end

private meta def ecppText : Hex.ECPP.Cert → String
  | .base c => s!"(Hex.ECPP.Cert.base {primeText c})"
  | .step n a b x y d ws child =>
      s!"(Hex.ECPP.Cert.step {n} {a} {b} {x} {y} {d} [" ++
      String.intercalate ", " (ws.map toString) ++ s!"] {ecppText child})"

private meta def evidenceText : Evidence → String
  | .legacy c => s!"(Hex.Nat.Mixed.Evidence.legacy {primeText c})"
  | .ecpp c => s!"(Hex.Nat.Mixed.Evidence.ecpp {ecppText c})"

private meta def powersText (fs : List PrimePower) : String :=
  "[" ++ String.intercalate ", " (fs.map fun e =>
    s!"⟨{e.prime}, {e.exponent}, {evidenceText e.cert}⟩") ++ "]"

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

/-- Preflight raw data, discard compiled producer proofs and kernel-check a
fresh subject-indexed acceptance constructor under finite options. -/
meta def validate (n : Nat) (value : CheckedFactors n) (budget : Budget := {}) : MetaM Unit := do
  if budget.maxHeartbeats == 0 || budget.maxRecDepth == 0 then
    throwError "mixed factor export: proof budgets must be positive"
  withOptions (fun opts => maxRecDepth.set (maxHeartbeats.set opts budget.maxHeartbeats) budget.maxRecDepth) do
    let limits : ImportBudget := {}
    let raw := value.raw
    unless raw.subject == n && HexArith.bitLength n ≤ limits.maxSubjectBits &&
        (raw.factors.take (limits.maxEntries + 1)).length ≤ limits.maxEntries do
      throwError "mixed factor export: subject/data bounds"
    for e in raw.factors do
      unless e.exponent > 0 && e.exponent ≤ limits.maxExponent &&
          FactorImport.certificateFits limits e.cert do
        throwError "mixed factor export: certificate bounds"
    let .ok _ := FactorImport.accept n raw | throwError "mixed factor export: checker rejection"
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
    checkWithKernel proof

/-- Deterministic public exposed data and kernel acceptance, importing replay only. -/
meta def source (name : Name) (n : Nat) (value : CheckedFactors n) (budget : Budget := {}) :
    MetaM String := do
  validate n value budget
  let (rawType, checkedType) := match value with
    | .complete _ => ("Factorization", "CheckedFactorization")
    | .partialResult _ => ("PartialFactorization", "CheckedPartialFactorization")
  let data := match value with
    | .complete _ => s!"⟨{n}, {powersText value.raw.factors}⟩"
    | .partialResult _ => s!"⟨{n}, {powersText value.raw.factors}, {value.raw.residual}⟩"
  let text := s!"module\n\npublic import HexIntFactor.Mixed.Replay\n\npublic section\n\nset_option maxHeartbeats {budget.maxHeartbeats}\nset_option maxRecDepth {budget.maxRecDepth}\n\n@[expose] def {name} : Hex.Nat.Mixed.{rawType} :=\n  {data}\n\n@[expose] def {name}_checked : Hex.Nat.Mixed.{checkedType} {n} :=\n  ⟨{name}, rfl, by decide +kernel⟩\n"
  if text.utf8ByteSize > budget.maxSourceBytes then throwError "mixed factor export: source byte limit"
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
  let text ← Command.liftTermElabM <| withOptions (fun opts =>
      maxRecDepth.set (maxHeartbeats.set opts 20000000) 65536) do
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
  let text ← Command.liftTermElabM <| withOptions (fun opts =>
      maxRecDepth.set (maxHeartbeats.set opts 20000000) 65536) do
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
