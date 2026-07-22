/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.CertReify
public meta import HexBerlekamp.IrreducibleDecide
public meta import HexBerlekamp.Factored
public import HexBerlekamp.CertReify
public import HexBerlekamp.IrreducibleDecide
public import HexBerlekamp.Factored
public import Lean

public section

/-!
Shared infrastructure for the `factor_poly` / `irreducibility` elaborators:
input classification, compiled-evaluation shims, the kernel-replay budget, and
the provider hook through which downstream libraries extend the tactics to
further input types.

## The provider hook

The elaborators handle `Hex.FpPoly p` natively. Every other input type is
offered to *providers*: values of `Hex.FactorTactic.Provider` declared by
downstream libraries under one of the well-known names in `providerNames`
(`HexBerlekampZassenhaus` adds the `Hex.ZPoly` arms; the Mathlib bridge
libraries add `Polynomial (ZMod q)` / `Polynomial ℤ`). Nothing here imports
those libraries — the driver probes the environment by name at elaboration
time and evaluates the provider through the interpreter, so this library
builds and works standalone, and importing a bridge upgrades the tactics.

A provider module must `public meta import HexBerlekamp.TacticCore` (the
constructor of `Provider` is meta code) and declare its provider as a
`public meta def`. Renaming a probed constant silently severs the hook, so
each provider carries a cross-referencing comment and the bridge test suites
act as liveness canaries; the `version` field is checked against
`Provider.abiVersion` at probe time so a stale provider fails loudly.
-/

namespace Hex.FactorTactic

open Lean Meta Elab

/-- Outcome of offering an input to a provider. `notApplicable` means the
provider does not handle this input type at all (try the next silently);
`declined` means it handles the type but cannot certify this input (try the
next, keep the diagnostic for the final error); `fatal` aborts dispatch. -/
meta inductive ProviderResult where
  | notApplicable
  | declined (why : MessageData)
  | success (e : Expr)
  | fatal (msg : MessageData)

/-- Capabilities a downstream library registers to extend
`factor_poly`/`irreducibility` to further input types. The arguments of the
term hooks are the original syntax, the elaborated polynomial, its
`whnfR`-normalized type, and the expected type of the surrounding
elaboration. -/
meta structure Provider where
  /-- ABI guard, checked against `Provider.abiVersion` at probe time. -/
  version : Nat
  /-- Handle a `factor_poly p` term elaboration. -/
  factorPoly? : Syntax → Expr → Expr → Option Expr → Term.TermElabM ProviderResult
  /-- Handle an `irreducibility p` term elaboration. -/
  irreducibility? : Syntax → Expr → Expr → Option Expr → Term.TermElabM ProviderResult
  /-- Handle goal-closing `irreducibility` on the given goal. -/
  goalIrred? : MVarId → Tactic.TacticM ProviderResult

/-- The provider ABI version this driver expects. -/
meta def Provider.abiVersion : Nat := 1

/-- Well-known provider constants, probed in order. Downstream libraries
declare a `public meta def` of type `Provider` under one of these names;
adding an entry requires a `HexBerlekamp` release. -/
meta def providerNames : List Name :=
  [`HexBerlekampZassenhaus.FactorTactic.provider,
   `HexBerlekampMathlib.FactorTactic.provider,
   `HexBerlekampZassenhausMathlib.FactorTactic.provider]

private meta unsafe def evalProviderUnsafe (n : Name) : MetaM Provider :=
  evalConst Provider n

@[implemented_by evalProviderUnsafe]
private meta opaque evalProviderCore (n : Name) : MetaM Provider

/-- All providers present in the current environment, in probe order, with
the declared type and ABI version checked before use. -/
meta def providers : MetaM (List Provider) := do
  let env ← getEnv
  let mut found := []
  for n in providerNames do
    if let some info := env.find? n then
      unless info.type.isConstOf ``Provider do
        throwError "factor_poly/irreducibility: provider {n} has unexpected \
            type{indentExpr info.type}"
      let prov ← evalProviderCore n
      unless prov.version == Provider.abiVersion do
        throwError "factor_poly/irreducibility: provider {n} has ABI version \
            {prov.version}, but this driver expects {Provider.abiVersion}; \
            rebuild the provider library against the current HexBerlekamp"
      found := found ++ [prov]
  return found

/-- Classification of a `factor_poly`/`irreducibility` input by its
`whnfR`-normalized type. -/
meta inductive PolyInput where
  /-- `Hex.FpPoly p` for a literal prime `p`, with the instance and
  coefficient-type expressions extracted from the input's type. -/
  | fp (p : Nat) (pE boundsE RE zeroE decE : Expr)
  /-- `Hex.ZPoly`, with the instance expressions from the input's type. -/
  | zpoly (RE zeroE decE : Expr)
  /-- Anything else (offered to providers). -/
  | other

/-- Classify an input's type: `DensePoly (ZMod64 p) → .fp`,
`DensePoly Int → .zpoly`, anything else `→ .other`. The `FpPoly`/`ZPoly`
abbreviations are reducible, so `whnfR` exposes the `DensePoly` application;
the instance expressions are taken from the type itself, never synthesized. -/
meta def classify (ty : Expr) : MetaM PolyInput := do
  let ty ← whnfR ty
  let_expr Hex.DensePoly R zeroE decE := ty | return .other
  let R' ← whnfR R
  if R'.isConstOf ``Int then
    return .zpoly R zeroE decE
  let_expr Hex.ZMod64 pE boundsE := R' | return .other
  let some p := pE.nat? | return .other
  return .fp p pE boundsE R zeroE decE

private meta unsafe def evalFpPolyUnsafe (p : Nat) [Hex.ZMod64.Bounds p]
    (tyE e : Expr) : MetaM (Except String (Hex.FpPoly p)) :=
  try
    return .ok (← evalExpr (Hex.FpPoly p) tyE e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalFpPolyUnsafe]
private meta opaque evalFpPolyCore (p : Nat) [Hex.ZMod64.Bounds p]
    (tyE e : Expr) : MetaM (Except String (Hex.FpPoly p))

/-- Evaluate a closed `Hex.FpPoly p` expression to its runtime value at
elaboration time (compiled/interpreted evaluation, not kernel reduction). -/
meta def evalFpPoly (tactic : String) (p : Nat) [Hex.ZMod64.Bounds p]
    (pE boundsE e : Expr) : MetaM (Hex.FpPoly p) := do
  match ← evalFpPolyCore p (Hex.CertReify.fpPolyType pE boundsE) e with
  | .ok f => return f
  | .error msg =>
      throwError "{tactic}: failed to evaluate the polynomial{indentExpr e}\
          \n{msg}\
          \nIf it refers to definitions from another module, that module may \
          need to be imported with `public meta import`."

/-- Ceiling on `degree · p`, the cost driver of one kernel Rabin-certificate
replay. Inputs over budget fail at elaboration time with a clear message
instead of emitting a proof the kernel cannot afford to check. -/
meta def replayBudget : Nat := 1 <<< 26

/-- Fail fast when a Rabin replay for a degree-`deg` factor at modulus `p`
would exceed `replayBudget`. -/
meta def checkReplayBudget (tactic : String) (p deg : Nat) : MetaM Unit := do
  if deg * p > replayBudget then
    throwError "{tactic}: certifying a degree-{deg} factor over F_{p} needs a \
        kernel Rabin replay of roughly {deg * p} modular polynomial \
        operations, over the supported budget ({replayBudget}); pick a \
        smaller modulus or degree"

/-- Reject inputs the compiled evaluator cannot see: free variables and
metavariables. -/
meta def checkClosed (tactic : String) (e : Expr) : MetaM Unit := do
  if e.hasFVar || e.hasExprMVar then
    throwError "{tactic}: the polynomial{indentExpr e}\
        \nmust be a closed term (no local hypotheses or metavariables)"

/-- Run provider dispatch over `providers`, accumulating decline diagnostics;
`whenNone` renders the final error when no provider succeeds. -/
meta def dispatch (run : Provider → Term.TermElabM ProviderResult)
    (whenNone : Array MessageData → Term.TermElabM Expr) :
    Term.TermElabM Expr := do
  let mut declines : Array MessageData := #[]
  for prov in (← providers) do
    match ← run prov with
    | .success e => return e
    | .notApplicable => pure ()
    | .declined why => declines := declines.push why
    | .fatal msg => throwError msg
  whenNone declines

/-- The standard "unsupported input type" tail for dispatch failures,
including any provider decline diagnostics. -/
meta def unsupportedMessage (tactic : String) (ty : Expr)
    (declines : Array MessageData) : MessageData :=
  let base := m!"{tactic}: unsupported polynomial type{indentExpr ty}\
      \nSupported without further imports: Hex.FpPoly p (prime p). \
      Importing HexBerlekampZassenhaus adds Hex.ZPoly; the Mathlib bridge \
      libraries add Polynomial (ZMod q) and Polynomial ℤ."
  declines.foldl (fun acc d => acc ++ m!"\n\n{d}") base

end Hex.FactorTactic
