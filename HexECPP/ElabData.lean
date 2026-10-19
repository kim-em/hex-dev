/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPP.Cert
public meta import HexECPP.Cert
public import HexECPP.Policy
public meta import HexECPP.Policy
public import HexPrimality.Elab
public import Lean.Elab.Tactic

/-! Bounded constructor-data auditing and ECPP reification, shared by
computational exporters and mathematical proof elaborators. -/

@[expose] public section

open Lean Elab Meta

namespace Hex.ECPP

/-- Finite admission policy for constructor data enclosing certificates.
Extra names must be the enclosing type's trusted constructors and instances. -/
structure DataBudget where
  /-- Maximum visited syntax nodes, including expanded let occurrences. -/
  maxNodes : Nat := 131072
  /-- Maximum numeral size; certificate fields are admitted separately. -/
  numeralBits : Nat := 512
  /-- Additional constructors and numeral instances for an enclosing type. -/
  extraNames : List Name := []

private meta def certType : Expr := mkConst ``Hex.ECPP.Cert
private meta def natType : Expr := mkConst ``Nat

-- Raw literals avoid an OfNat wrapper at every inverse witness. The reader
-- checks the same numeral values and retains its fixed syntax-node ceiling.
private meta def reifyNats : List Nat → Expr
  | [] => mkApp (mkConst ``List.nil [.zero]) natType
  | x :: xs => mkApp3 (mkConst ``List.cons [.zero]) natType
      (mkRawNatLit x) (reifyNats xs)

/-- Reify a bounded raw proposal as kernel-checkable constructor data. Call
`validateCert` first when the proposal has not already passed replay preflight. -/
meta def reifyCert : Cert → Expr
  | .base c => mkApp (mkConst ``Hex.ECPP.Cert.base) (Hex.PrimalityTactic.reifyPrimeCert c)
  | .step n a b x y d ws child =>
      mkAppN (mkConst ``Hex.ECPP.Cert.step) #[mkRawNatLit n, mkRawNatLit a,
        mkRawNatLit b, mkRawNatLit x, mkRawNatLit y, mkRawNatLit d,
        reifyNats ws, reifyCert child]

private meta def maxSyntaxNodes : Nat := 131072
private meta def maxInverseWitnesses : Nat := 1024
private meta def maxCertNodes : Nat := 32

private meta def dataConstant (name : Name) : Bool :=
  name == ``Hex.ECPP.Cert || name == ``Hex.Nat.PrimeCert ||
  name == ``Nat || name == ``List || name == ``Prod ||
  name == ``OfNat || name == ``OfNat.ofNat || name == ``OfNat.mk ||
  name == ``instOfNatNat ||
  name == ``Hex.ECPP.Cert.base || name == ``Hex.ECPP.Cert.step ||
  name == ``Hex.Nat.PrimeCert.small || name == ``Hex.Nat.PrimeCert.pock ||
  name == ``Hex.Nat.PrimeCert.pock3 ||
  name == ``Hex.Nat.PrimeCert.pock3Sieve ||
  name == ``List.nil || name == ``List.cons || name == ``Prod.mk

/-- A persistent substitution scope for constructor-data let bindings. -/
private meta inductive DataContext where
  | nil
  | cons (value : Expr) (scope tail : DataContext)

-- Lookup consumes traversal fuel as well, bounding deeply nested references.
private meta def DataContext.lookup : DataContext → Nat → Nat → Option (Expr × DataContext × Nat)
  | .nil, _, _ | _, _, 0 => none
  | .cons value scope _, 0, fuel + 1 => some (value, scope, fuel)
  | .cons _ _ tail, i + 1, fuel + 1 => tail.lookup i fuel

/-- Audit all syntax, then charge expanded occurrences through a persistent
scope. Each pass has finite fuel, including nested definitions and lookups. -/
private meta partial def checkData (b : DataBudget) (e : Expr) (fuel : Nat)
    (context : DataContext := .nil) (expandLets : Bool := false) : MetaM Nat := do
  if fuel == 0 then throwError "ecpp: certificate syntax exceeds {b.maxNodes} nodes"
  let fuel := fuel - 1
  match e with
  | .app f a => checkData b a (← checkData b f fuel context expandLets) context expandLets
  | .lit (.natVal n) =>
      if HexArith.bitLength n > b.numeralBits then
        throwError "ecpp: a certificate numeral exceeds {b.numeralBits} bits"
      return fuel
  | .const name _ =>
      if dataConstant name || b.extraNames.contains name then return fuel
      let env ← getEnv
      if (Compiler.getImplementedBy? env name).isSome then
        throwError "ecpp: `{name}` has a compiled implementation; use constructor data"
      unless env.hasExposedBody name do
        throwError "ecpp: `{privateToUserName name}` is not an exposed data definition"
      let some (.defnInfo info) := env.find? name
        | throwError "ecpp: `{name}` is not a data definition"
      try checkData b info.value fuel .nil expandLets
      catch ex => throwError "ecpp: in exposed `{name}`: {ex.toMessageData}"
  | .mdata _ body => checkData b body fuel context expandLets
  | .letE _ ty val body _ =>
      if expandLets then
        -- Persistent closures avoid repeated substitution of a large body.
        checkData b body fuel (.cons val context context) true
      else
        -- Audit all values, including unused ones, before expanding occurrences.
        checkData b body (← checkData b val (← checkData b ty fuel) context) context
  | .bvar i =>
      if !expandLets then return fuel
      let some (value, scope, fuel) := context.lookup i fuel
        | throwError "ecpp: certificate syntax exceeds {b.maxNodes} nodes"
      checkData b value fuel scope true
  | .sort _ => return fuel
  | _ => throwError "ecpp: certificate must be constructor data; got {e}"

-- Consume fuel while visiting nodes, including repeated children in a shared
-- tree. Exhaustion must stop traversal before reification or checker evaluation.
private meta partial def primeCertFuel (fuel : Nat) (cert : Hex.Nat.PrimeCert) : Option Nat := do
  let fuel ← match fuel with | 0 => none | n + 1 => some n
  match cert with
  | .small _ => return fuel
  | .pock _ fs | .pock3 _ _ _ _ fs | .pock3Sieve _ _ _ _ _ fs =>
      let mut fuel := fuel
      for (_, _, child) in fs do
        fuel ← primeCertFuel fuel child
      return fuel

private meta def certFuel : Nat → Cert → Option Nat
  | 0, _ => none
  | fuel + 1, .base c => primeCertFuel fuel c
  | fuel + 1, .step _ _ _ _ _ _ _ child => certFuel fuel child

private meta def checkCertBudget : Cert → MetaM Unit
  | .base _ => pure ()
  | .step n _ _ _ _ _ ws child => do
      if HexArith.bitLength n > maxBits then
        throwError "ecpp: certificate subject exceeds {maxBits} bits"
      if (ws.take (maxInverseWitnesses + 1)).length > maxInverseWitnesses then
        throwError "ecpp: inverse transcript exceeds {maxInverseWitnesses} witnesses"
      checkCertBudget child

/-- Expand audited data with persistent scopes, bounding substitution work. -/
private meta partial def expandData (b : DataBudget) (e : Expr) (fuel : Nat)
    (context : DataContext := .nil) : MetaM (Expr × Nat) := do
  if fuel == 0 then throwError "ecpp: certificate syntax exceeds {b.maxNodes} nodes"
  let fuel := fuel - 1
  match e with
  | .app f a =>
      let (f, fuel) ← expandData b f fuel context
      let (a, fuel) ← expandData b a fuel context
      return (mkApp f a, fuel)
  | .const name levels =>
      if dataConstant name || b.extraNames.contains name then return (e, fuel)
      let some (.defnInfo info) := (← getEnv).find? name
        | throwError "ecpp: `{name}` is not a data definition"
      expandData b (info.value.instantiateLevelParams info.levelParams levels) fuel
  | .mdata _ body => expandData b body fuel context
  | .letE _ _ val body _ => expandData b body fuel (.cons val context context)
  | .bvar i =>
      let some (value, scope, fuel) := context.lookup i fuel
        | throwError "ecpp: certificate syntax exceeds {b.maxNodes} nodes"
      expandData b value fuel scope
  | .lit _ | .sort _ => return (e, fuel)
  | _ => throwError "ecpp: certificate must be constructor data; got {e}"

/-- Audit exposed constructor data and bounded let expansion before evaluation.
No compiled override or executable body enters the returned expression. -/
meta def auditData (e : Expr) (b : DataBudget := {}) : MetaM Expr := do
  Hex.PrimalityTactic.checkClosed "certificate data" e
  if e.hasSorry then throwError "ecpp: certificate contains an unfinished proof"
  discard <| checkData b e b.maxNodes
  discard <| checkData b e b.maxNodes (expandLets := true)
  return (← expandData b e b.maxNodes).1

private meta unsafe def evalCertUnsafe (e : Expr) : MetaM Cert := do
  -- Audits precede evaluation. Expanding definitions and lets with persistent
  -- scopes avoids quadratic substitution and needs no meta import of data.
  let (data, _) ← expandData {} e maxSyntaxNodes
  evalExpr Cert certType data

@[implemented_by evalCertUnsafe]
private meta opaque evalCert (e : Expr) : MetaM Cert

/-- Build a proof from a supplied exposed certificate. The evaluated producer
is discarded; the kernel checks the reified raw data and checker reduction. -/
meta def readCert (e : Expr) : MetaM Cert := do
  Hex.PrimalityTactic.checkClosed "ecpp using" e
  if e.hasSorry then throwError "ecpp: certificate contains an unfinished proof"
  discard <| checkData {} e maxSyntaxNodes
  discard <| checkData {} e maxSyntaxNodes (expandLets := true)
  let cert ← evalCert e
  if (certFuel maxCertNodes cert).isNone then
    throwError "ecpp: certificate exceeds {maxCertNodes} total nodes"
  checkCertBudget cert
  unless check cert do
    throwError "ecpp: certificate failed check"
  return cert

/-- Validate a raw proposal against the finite replay policy. -/
meta def validateCert (cert : Cert) : MetaM Unit := do
  if (certFuel maxCertNodes cert).isNone then
    throwError "ecpp: certificate exceeds {maxCertNodes} total nodes"
  checkCertBudget cert
  discard <| checkData {} (reifyCert cert) maxSyntaxNodes
  unless check cert do
    throwError "ecpp: certificate failed check"

end Hex.ECPP
