/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.CertificateSyntax
public meta import HexBerlekamp.IrreducibleDecide
public meta import HexBerlekamp.Factored
public import HexBerlekamp.CertificateSyntax
public import HexBerlekamp.IrreducibleDecide
public import HexBerlekamp.Factored
public import Lean

public section

/-!
Shared infrastructure for the `factor_poly` / `irreducibility` elaborators:
input classification, compiled-evaluation shims, the kernel-replay budget, and
the registered extensions through which downstream libraries add support for
further input types.

# Tactic extensions

The elaborators handle `Hex.FpPoly p` natively. Every other input type is
offered to *extensions*: values of `Hex.FactorTactic.Extension` declared by
downstream libraries under one of the well-known names in `extensionNames`
(`HexBerlekampZassenhaus` adds the `Hex.ZPoly` cases; the Mathlib integration
libraries add `Polynomial (ZMod q)` and `Polynomial ℤ`). Nothing here imports
those libraries. At elaboration time the driver looks up the declarations by
name and evaluates each extension through the interpreter. Thus this library
works standalone, while importing an integration library adds its input types.

An extension module must `public meta import HexBerlekamp.PolynomialTactic`
because the constructor of `Extension` is meta code, and must declare its
extension as a `public meta def`. Its registration comment names
`extensionNames`, and regression tests ensure that the declaration remains
discoverable after renaming. The driver checks that every discovered
declaration has type `Extension` before evaluating it.
-/

namespace Hex.FactorTactic

open Lean Meta Elab

/-- Outcome of offering an input to an extension. `notApplicable` means the
extension does not handle this input type at all (try the next silently);
`declined` means it handles the type but cannot certify this input (try the
next, keep the diagnostic for the final error); `fatal` aborts selection. -/
meta inductive ExtensionResult where
  | notApplicable
  | declined (why : MessageData)
  | success (e : Expr)
  | fatal (msg : MessageData)

/-- Capabilities a downstream library registers to extend
`factor_poly`/`irreducibility` to further input types. The arguments of the
term hooks are the original syntax, the elaborated polynomial, its
`whnfR`-normalized type, and the expected type of the surrounding
elaboration. -/
meta structure Extension where
  /-- Handle a `factor_poly p` term elaboration. -/
  factorPoly? : Syntax → Expr → Expr → Option Expr → Term.TermElabM ExtensionResult
  /-- Handle an `irreducibility p` term elaboration. -/
  irreducibility? : Syntax → Expr → Expr → Option Expr → Term.TermElabM ExtensionResult
  /-- Handle goal-closing `irreducibility` on the given goal. -/
  goalIrred? : MVarId → Tactic.TacticM ExtensionResult

/-- Well-known extension constants, checked in order. Downstream libraries
declare a `public meta def` of type `Extension` under one of these names;
adding an entry requires a `HexBerlekamp` release. -/
meta def extensionNames : List Name :=
  [`HexBerlekampZassenhaus.FactorTactic.extension,
   `HexBerlekampMathlib.FactorTactic.extension,
   `HexBerlekampZassenhausMathlib.FactorTactic.extension]

private meta unsafe def evalExtensionUnsafe (n : Name) : MetaM Extension :=
  evalConst Extension n

@[implemented_by evalExtensionUnsafe]
private meta opaque evalExtensionCore (n : Name) : MetaM Extension

/-- All extensions present in the current environment, in lookup order, with
the declared type checked before use. -/
meta def extensions : MetaM (List Extension) := do
  let env ← getEnv
  let mut found := []
  for n in extensionNames do
    if let some info := env.find? n then
      unless info.type.isConstOf ``Extension do
        throwError "factor_poly/irreducibility: extension {n} has unexpected \
            type{indentExpr info.type}"
      let ext ← evalExtensionCore n
      found := found ++ [ext]
  return found

/-- Classification of a `factor_poly`/`irreducibility` input by its
`whnfR`-normalized type. -/
meta inductive PolyInput where
  /-- `Hex.FpPoly p` for a literal prime `p`, with the instance and
  coefficient-type expressions extracted from the input's type. -/
  | fp (p : Nat) (pE boundsE RE zeroE decE : Expr)
  /-- `Hex.ZPoly`, with the instance expressions from the input's type. -/
  | zpoly (RE zeroE decE : Expr)
  /-- Anything else (offered to extensions). -/
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
  match ← evalFpPolyCore p (Hex.CertificateSyntax.fpPolyType pE boundsE) e with
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

/-- Ceiling on candidate remainder tests in one kernel primality replay.
`2^16` covers the full `ZMod64` modulus range, whose largest square-root scan
tests fewer than `2^16` candidates. -/
meta def primeReplayBudget : Nat := 1 <<< 16

/--
Worst-case number of remainder tests in `Hex.Nat.isPrimeTrial n`. This mirrors
the checker's square stopping convention without performing any divisions, and
is used only at elaboration time to budget the proof that the kernel will
replay.
-/
meta def primeReplayCost (n : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := n + 1
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if mid * mid ≤ n then
      lo := mid
    else
      hi := mid
  return lo - 1

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

/-- Try the registered extensions in order, retaining decline diagnostics.
`whenNone` renders the final error when no extension succeeds. -/
meta def applyExtensions (run : Extension → Term.TermElabM ExtensionResult)
    (whenNone : Array MessageData → Term.TermElabM Expr) :
    Term.TermElabM Expr := do
  let mut declines : Array MessageData := #[]
  for ext in (← extensions) do
    match ← run ext with
    | .success e => return e
    | .notApplicable => pure ()
    | .declined why => declines := declines.push why
    | .fatal msg => throwError msg
  whenNone declines

/-- The standard "unsupported input type" tail for selection failures,
including any extension decline diagnostics. -/
meta def unsupportedMessage (tactic : String) (ty : Expr)
    (declines : Array MessageData) : MessageData :=
  let base := m!"{tactic}: unsupported polynomial type{indentExpr ty}\
      \nSupported without further imports: Hex.FpPoly p (prime p). \
      Importing HexBerlekampZassenhaus adds Hex.ZPoly; the Mathlib integration \
      libraries add Polynomial (ZMod q) and Polynomial ℤ."
  declines.foldl (fun acc d => acc ++ m!"\n\n{d}") base

end Hex.FactorTactic
