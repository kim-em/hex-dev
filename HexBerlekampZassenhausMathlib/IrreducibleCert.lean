/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekampZassenhaus.CertReify
public import HexBerlekampZassenhausMathlib.ToMonicUniqueness
public import HexBerlekampZassenhaus.CertReify

public section
set_option backward.proofsInPublic true

/-!
The `irreducible_cert` tactic: certifying irreducibility for integer
polynomials with compiled certificate prep and a cheap kernel check.

For a goal `Irreducible (HexPolyZMathlib.toPolynomial f)` with `f` a closed
`Hex.ZPoly` term, the tactic:

1. evaluates `Hex.certifyIrreducible? f` at elaboration time (compiled
   evaluation; Berlekamp factoring and Rabin certificate generation never
   reach the kernel);
2. reifies the resulting certificate as a literal `Expr`
   (`Hex.CertReify`);
3. closes the goal with `irreducible_of_checkIrreducibleCertLinear` applied to
   the reified certificate, filling all four Boolean hypothesis slots with
   `Eq.refl true`.

The only kernel work is reducing `checkIrreducibleCertLinear` (the incremental
pow-chain replay, `O(n · p)` per modular factor) plus the three cheap side
checks (primality of the handful of recorded primes, `content f = 1`, and
`0 < degree`), all on literal data.
-/

namespace HexBerlekampZassenhausMathlib.IrreducibleCert

open Lean Meta

private meta unsafe def evalZPolyUnsafe (e : Expr) :
    MetaM (Except String Hex.ZPoly) :=
  try
    return .ok (← evalExpr Hex.ZPoly (mkConst ``Hex.ZPoly) e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalZPolyUnsafe]
private meta opaque evalZPolyCore (e : Expr) : MetaM (Except String Hex.ZPoly)

/-- Evaluate a closed `Hex.ZPoly` expression to its runtime value at
elaboration time (compiled/interpreted evaluation, not kernel reduction). -/
meta def evalZPoly (e : Expr) : MetaM Hex.ZPoly := do
  match ← evalZPolyCore e with
  | .ok f => return f
  | .error msg =>
      throwError "irreducible_cert: failed to evaluate the polynomial\
          {indentExpr e}\n{msg}"

private meta unsafe def evalCertificateUnsafe (e : Expr) :
    MetaM (Except String Hex.ZPolyIrreducibilityCertificate) :=
  try
    return .ok (← evalExpr Hex.ZPolyIrreducibilityCertificate
      (mkConst ``Hex.ZPolyIrreducibilityCertificate) e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalCertificateUnsafe]
private meta opaque evalCertificateCore (e : Expr) :
    MetaM (Except String Hex.ZPolyIrreducibilityCertificate)

/-- Evaluate a closed `Hex.ZPolyIrreducibilityCertificate` expression to its
runtime value at elaboration time. Used by the reification round-trip tests. -/
meta def evalCertificate (e : Expr) : MetaM Hex.ZPolyIrreducibilityCertificate := do
  match ← evalCertificateCore e with
  | .ok cert => return cert
  | .error msg =>
      throwError "irreducible_cert: failed to evaluate the certificate\
          {indentExpr e}\n{msg}"

/--
Match a goal of the form `Irreducible (HexPolyZMathlib.toPolynomial f)`
(or the unfolded `HexPolyMathlib.toPolynomial` at `R = ℤ`) and return `f`.
-/
private meta def matchIrreducibleGoal (tgt : Expr) : MetaM (Option Expr) := do
  let tgt ← whnfR tgt
  let_expr Irreducible _M _inst arg := tgt | return none
  if arg.getAppFn.isConstOf ``HexPolyZMathlib.toPolynomial &&
      arg.getAppNumArgs == 1 then
    return some arg.appArg!
  let arg ← whnfR arg
  if arg.getAppFn.isConstOf ``HexPolyMathlib.toPolynomial &&
      arg.getAppNumArgs == 4 then
    let args := arg.getAppArgs
    if args[0]!.isConstOf ``Int then
      return some args[3]!
  return none

/--
`irreducible_cert` proves `Irreducible (HexPolyZMathlib.toPolynomial f)` for a
closed `Hex.ZPoly` term `f` by running the compiled certificate generator
`Hex.certifyIrreducible?` at elaboration time, reifying the certificate as
literal data, and letting the kernel replay only the cheap
`checkIrreducibleCertLinear` reduction plus the primality / content / degree
side checks.

The tactic fails cleanly when the generator declines: reducible, non-primitive,
or constant inputs, and irreducible inputs whose balanced modular
factorizations fall outside the per-prime degree-sum obstruction language
(e.g. Swinnerton-Dyer polynomials).
-/
elab "irreducible_cert" : tactic => do
  let goal ← Elab.Tactic.getMainGoal
  goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    let some fE ← matchIrreducibleGoal tgt
      | throwError "irreducible_cert: the goal must have the form\
          \n  Irreducible (HexPolyZMathlib.toPolynomial f)\
          \nwith f a closed Hex.ZPoly term, but the goal is{indentExpr tgt}"
    if fE.hasFVar || fE.hasExprMVar then
      throwError "irreducible_cert: the polynomial{indentExpr fE}\
          \nmust be a closed term (no local hypotheses or metavariables)"
    let f ← evalZPoly fE
    let some cert := Hex.certifyIrreducible? f
      | throwError "irreducible_cert: certifyIrreducible? produced no \
          certificate for{indentExpr fE}\
          \nThe polynomial is reducible, non-primitive, or constant, or it \
          is irreducible but its modular factorizations are balanced at every \
          admissible prime (e.g. Swinnerton-Dyer polynomials), which the \
          per-prime degree-sum obstruction language cannot certify."
    unless Hex.checkIrreducibleCertLinear f cert do
      throwError "irreducible_cert: internal error: the generated \
          certificate fails checkIrreducibleCertLinear; please report this"
    let certE := Hex.CertReify.reifyCertificate cert
    -- Each hypothesis slot receives `Eq.refl true`; the kernel verifies it by
    -- reducing the corresponding Boolean check on the literal certificate.
    let proof := mkApp6
      (mkConst ``HexBerlekampZassenhausMathlib.irreducible_of_checkIrreducibleCertLinear)
      fE certE Hex.CertReify.reflTrue Hex.CertReify.reflTrue Hex.CertReify.reflTrue
      Hex.CertReify.reflTrue
    unless ← isDefEq (← inferType proof) tgt do
      throwError "irreducible_cert: the certified statement\
          {indentExpr (← inferType proof)}\
          \nis not definitionally equal to the goal{indentExpr tgt}"
    goal.assign proof
  Elab.Tactic.replaceMainGoal []

end HexBerlekampZassenhausMathlib.IrreducibleCert
