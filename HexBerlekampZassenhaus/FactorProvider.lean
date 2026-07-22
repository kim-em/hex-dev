/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.TacticCore
public meta import HexBerlekampZassenhaus.CertReify
public meta import HexBerlekampZassenhaus.IrreducibleDecide
public meta import HexBerlekampZassenhaus.Factored
public meta import HexBerlekampZassenhaus.FactorEntryPoints
public import HexBerlekamp.TacticCore
public import HexBerlekampZassenhaus.CertReify
public import HexBerlekampZassenhaus.IrreducibleDecide
public import HexBerlekampZassenhaus.Factored
public import HexBerlekampZassenhaus.FactorEntryPoints

public section

/-!
The `Hex.ZPoly` provider for the `factor_poly`/`irreducibility` elaborators:
importing this library upgrades the tactics (declared in
`HexBerlekamp.TacticCore` / probed by name, see `providerNames`) to handle
integer polynomials.

The compiled Berlekamp–Zassenhaus factorizer runs at elaboration time as
untrusted search; per-factor irreducibility is certified through
`Hex.ZPoly.IrredWitness` (prime constant / primitive linear / single-prime
modular certificate), and the emitted terms carry only kernel checks on
reified literal data. Factors that are irreducible over `ℤ` but reducible
mod every candidate prime (balanced factors, e.g. Swinnerton-Dyer
polynomials or `X⁴+1`) have no single-prime witness: this provider then
*declines* with a diagnostic, so the Mathlib bridge provider (multi-prime
degree-obstruction certificates) can take over when imported, and the final
error explains the gap otherwise.
-/

namespace HexBerlekampZassenhaus.FactorTactic

open Lean Meta Elab
open Hex.FactorTactic (ProviderResult)

private meta unsafe def evalZPolyUnsafe (e : Expr) :
    MetaM (Except String Hex.ZPoly) :=
  try
    return .ok (← evalExpr Hex.ZPoly (mkConst ``Hex.ZPoly) e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalZPolyUnsafe]
private meta opaque evalZPolyCore (e : Expr) : MetaM (Except String Hex.ZPoly)

/-- Evaluate a closed `Hex.ZPoly` expression to its runtime value at
elaboration time. -/
meta def evalZPoly (tactic : String) (e : Expr) : MetaM Hex.ZPoly := do
  match ← evalZPolyCore e with
  | .ok f => return f
  | .error msg =>
      throwError "{tactic}: failed to evaluate the polynomial{indentExpr e}\
          \n{msg}\
          \nIf it refers to definitions from another module, that module may \
          need to be imported with `public meta import`."

/-- Candidate primes for the single-prime witness search. -/
meta def witnessPrimes : List Nat :=
  (List.range 512).filter Hex.Nat.isPrimeTrial

/-- Search for a single-prime modular witness for `q` (already known
non-constant, non-linear). Returns `none` when no candidate prime works —
either `q` is reducible, or it is balanced at every candidate prime. -/
meta def searchModPWitness (q : Hex.ZPoly) : Option Hex.ZPoly.ModPWitness := Id.run do
  for p in witnessPrimes do
    if h1 : 0 < p then
      if h2 : p < 2 ^ 31 then
        let bounds : Hex.ZMod64.Bounds p := ⟨h1, h2⟩
        if q.size * p ≤ Hex.FactorTactic.replayBudget then
          if @Hex.ZPoly.leadingCoeffModP q p bounds ≠ 0 then
            let g := @Hex.ZPoly.modP p bounds q
            let (c, m) := @Hex.FpPoly.normalizeMonic p bounds g
            if hmonic : Hex.DensePoly.leadingCoeff m = 1 then
              match @Hex.Berlekamp.buildIrreducibilityCertificate? p bounds m
                  (by exact hmonic) with
              | some cert =>
                  return some { p := p, bounds := bounds, m := m, c := c,
                                cert := cert }
              | none => pure ()
  return none

/-- Search for an irreducibility witness for `q`. -/
meta def searchWitness (q : Hex.ZPoly) : Option Hex.ZPoly.IrredWitness := Id.run do
  if q.size = 1 then
    if Hex.ZPoly.isNatPrime (q.coeff 0).natAbs then
      return some .primeConst
    else
      return none
  if q.size = 2 && Hex.ZPoly.content q == 1 then
    return some .linear
  match searchModPWitness q with
  | some w => return some (.modP w)
  | none => return none

/-- Reify a `ModPWitness` as a constructor application over reified pieces. -/
meta def reifyModPWitness (w : Hex.ZPoly.ModPWitness) : Expr :=
  letI := w.bounds
  let pE := mkNatLit w.p
  let boundsE := Hex.CertReify.reifyBounds pE
  mkApp5 (mkConst ``Hex.ZPoly.ModPWitness.mk) pE boundsE
    (Hex.CertReify.reifyFpPolyOfNats pE boundsE (Hex.CertReify.fpCoeffNats w.m))
    (Hex.CertReify.reifyZMod64 pE boundsE w.c.toNat)
    (Hex.CertReify.reifyRabinCert w.cert)

/-- Reify an `IrredWitness`. -/
meta def reifyWitness : Hex.ZPoly.IrredWitness → Expr
  | .primeConst => mkConst ``Hex.ZPoly.IrredWitness.primeConst
  | .linear => mkConst ``Hex.ZPoly.IrredWitness.linear
  | .modP w => mkApp (mkConst ``Hex.ZPoly.IrredWitness.modP) (reifyModPWitness w)

/-- Literal `List` expression (shared shape with the `FpPoly` elaborator). -/
meta def listLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil

/-- Deduplicate a `ZPoly` list by coefficient equality (order-preserving). -/
meta def dedupZPolys (l : List Hex.ZPoly) : List Hex.ZPoly :=
  l.foldl (init := []) fun acc q =>
    if acc.any fun r => Hex.DensePoly.beqCoeffs r q then acc else acc ++ [q]

/-- The balanced-factor decline diagnostic. -/
meta def balancedDecline (tactic : String) (q : Hex.ZPoly) : MetaM MessageData := do
  let qE ← Hex.CertReify.reifyZPoly q
  return m!"{tactic}: the irreducible factor{indentExpr qE}\
      \nhas no single-prime modular witness among the candidate primes \
      (its modular factorizations are balanced, e.g. Swinnerton-Dyer \
      polynomials or X⁴+1); the Mathlib bridge's multi-prime \
      degree-obstruction certificates may certify it — import \
      HexBerlekampZassenhausMathlib."

/-- The opaque-input contract check: the user's term must be definitionally
transparent down to its evaluated literal. -/
meta def checkTransparent (tactic : String) (f : Hex.ZPoly) (fE : Expr) :
    MetaM Expr := do
  let fLit ← Hex.CertReify.reifyZPoly f
  unless ← isDefEq fLit fE do
    throwError "{tactic}: the polynomial{indentExpr fE}\
        \nevaluates to{indentExpr fLit}\
        \nbut is not definitionally transparent to the elaborator (an \
        imported definition without `@[expose]`?); the kernel could not \
        check the emitted certificate against it"
  return fLit

/-- The `factor_poly` arm: factorize, certify each distinct factor by an
`IrredWitness`, and emit a reified `Hex.ZPoly.Factored`. Declines when some
factor has no free-layer witness. -/
meta def factorPolyZPoly (zeroE decE fE : Expr) :
    Term.TermElabM ProviderResult := do
  let f ← evalZPoly "factor_poly" fE
  discard <| checkTransparent "factor_poly" f fE
  let φ := Hex.ZPoly.factorize f
  let factors := (φ.factors.toList.flatMap fun (q, e) =>
    List.replicate e q).mergeSort fun a b => a.size ≤ b.size
  let scalar := φ.scalar
  unless Hex.DensePoly.beqCoeffs (Hex.DensePoly.C scalar * factors.prod) f do
    throwError "factor_poly: internal error: the factorization product does \
        not reconstruct the input; please report this"
  let mut certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness) := []
  for q in dedupZPolys factors do
    match searchWitness q with
    | some w =>
        unless Hex.ZPoly.checkIrredWitness q w do
          throwError "factor_poly: internal error: a generated witness fails \
              checkIrredWitness; please report this"
        certified := certified ++ [(q, w)]
    | none =>
        return .declined (← balancedDecline "factor_poly" q)
  unless Hex.ZPoly.checkIrredCover factors certified do
    throwError "factor_poly: internal error: the generated witnesses fail \
        checkIrredCover; please report this"
  let intE := mkConst ``Int
  let zpolyTy := mkApp3 (mkConst ``Hex.DensePoly [Level.zero]) intE zeroE decE
  let scalarE := toExpr scalar
  let factorsE := listLit zpolyTy
    (← factors.mapM fun q => Hex.CertReify.reifyZPoly q)
  let witnessTy := mkConst ``Hex.ZPoly.IrredWitness
  let pairTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) zpolyTy witnessTy
  let certifiedE := listLit pairTy (← certified.mapM fun (q, w) => do
    return mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) zpolyTy witnessTy
      (← Hex.CertReify.reifyZPoly q) (reifyWitness w))
  let lhsE ← mkAppM ``HMul.hMul
    #[← mkAppM ``Hex.DensePoly.C #[scalarE], ← mkAppM ``List.prod #[factorsE]]
  let hmulE := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
    intE zeroE decE lhsE fE Hex.CertReify.reflTrue
  let hirredE := mkApp3 (mkConst ``Hex.ZPoly.irreducible_of_checkIrredCover)
    factorsE certifiedE Hex.CertReify.reflTrue
  return .success (mkApp5 (mkConst ``Hex.ZPoly.Factored.mk)
    fE scalarE factorsE hmulE hirredE)

/-- The `irreducibility` proof for a runtime `ZPoly` and its expression:
shared by the term arm and goal mode. -/
meta def irredProof (fE : Expr) (f : Hex.ZPoly) :
    MetaM (Except MessageData Expr) := do
  discard <| checkTransparent "irreducibility" f fE
  if f.size = 0 then
    throwError "irreducibility: the zero polynomial is not irreducible"
  if Hex.ZPoly.IsUnit f then
    throwError "irreducibility: the polynomial{indentExpr fE}\
        \nis a unit (±1), not irreducible"
  match searchWitness f with
  | some w =>
      unless Hex.ZPoly.checkIrredWitness f w do
        throwError "irreducibility: internal error: a generated witness \
            fails checkIrredWitness; please report this"
      return .ok (mkApp3 (mkConst ``Hex.ZPoly.irreducible_of_checkIrredWitness)
        fE (reifyWitness w) Hex.CertReify.reflTrue)
  | none =>
      if Hex.ZPoly.isIrreducible f then
        return .error (← balancedDecline "irreducibility" f)
      else
        let φ := Hex.ZPoly.factorize f
        let count := φ.factors.foldl (fun acc (_, e) => acc + e) 0
        throwError "irreducibility: the polynomial{indentExpr fE}\
            \nis not irreducible over ℤ: factor_poly finds {count} \
            irreducible factors (with multiplicity), scalar {φ.scalar}"

/-- The `irreducibility` term arm. -/
meta def irreducibilityZPoly (fE : Expr) : Term.TermElabM ProviderResult := do
  let f ← evalZPoly "irreducibility" fE
  match ← irredProof fE f with
  | .ok proof => return .success proof
  | .error why => return .declined why

/-- Goal mode: close `Hex.ZPoly.Irreducible e`. -/
meta def goalIrredZPoly (goal : MVarId) : Tactic.TacticM ProviderResult := do
  goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    unless tgt.getAppFn.isConstOf ``Hex.ZPoly.Irreducible &&
        tgt.getAppNumArgs == 1 do
      return .notApplicable
    let fE := tgt.appArg!
    Hex.FactorTactic.checkClosed "irreducibility" fE
    let f ← evalZPoly "irreducibility" fE
    match ← irredProof fE f with
    | .ok proof =>
        unless ← isDefEq (← inferType proof) tgt do
          throwError "irreducibility: the certified statement\
              {indentExpr (← inferType proof)}\
              \nis not definitionally equal to the goal{indentExpr tgt}"
        return .success proof
    | .error why => return .declined why

end HexBerlekampZassenhaus.FactorTactic

namespace HexBerlekampZassenhaus.FactorTactic

open Lean Elab

/-- The `Hex.ZPoly` provider, probed by name from
`Hex.FactorTactic.providerNames` — renaming it severs the hook (the free and
bridge test suites are the liveness canaries). -/
public meta def provider : Hex.FactorTactic.Provider where
  version := Hex.FactorTactic.Provider.abiVersion
  factorPoly? := fun _stx pE ty _expectedType? => do
    match ← Hex.FactorTactic.classify ty with
    | .zpoly _ zeroE decE => factorPolyZPoly zeroE decE pE
    | _ => return .notApplicable
  irreducibility? := fun _stx pE ty _expectedType? => do
    match ← Hex.FactorTactic.classify ty with
    | .zpoly _ _ _ => irreducibilityZPoly pE
    | _ => return .notApplicable
  goalIrred? := goalIrredZPoly

end HexBerlekampZassenhaus.FactorTactic
