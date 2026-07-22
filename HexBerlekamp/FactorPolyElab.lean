/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.TacticCore
public meta import HexPolyFp.SquareFree
public meta import HexBerlekamp.Factor
public import HexBerlekamp.TacticCore
public import HexPolyFp.SquareFree
public import HexBerlekamp.Factor

public section

/-!
The `factor_poly` term elaborator and tactic.

`factor_poly f` elaborates to a `Hex.FpPoly.Factored f` value (further input
types via providers): the compiled Yun square-free decomposition and Berlekamp
factorizer run at elaboration time as untrusted search, and the emitted
structure carries kernel checks on reified literal data — one
`DensePoly.beqCoeffs` product check and one `Berlekamp.checkIrredCover` pass
replaying each distinct factor's Rabin certificate once. The factorizer never
runs in the kernel.

The tactic form `factor_poly f` introduces `scalar` and `factors` as `let`
bindings (transparent literals) plus `factors_mul` and `factors_irred`
hypotheses stated over them.
-/

namespace Hex.FactorTactic

open Lean Meta Elab

/-- Literal `List` expression `[x₁, …, xₙ] : List ty`. -/
meta def listLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil

/-- The type `FpPoly p × ZMod64 p × Berlekamp.IrreducibilityCertificate` of a
certified-cover entry, at a reified prime and bounds instance. -/
meta def coverEntryType (pE boundsE : Expr) : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
    (Hex.CertReify.fpPolyType pE boundsE)
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
      (Hex.CertReify.zmodType pE boundsE)
      (mkConst ``Hex.Berlekamp.IrreducibilityCertificate))

/-- Reify one certified-cover entry `(m, c, cert)`. -/
meta def reifyCoverEntry (pE boundsE : Expr) {p : Nat} [Hex.ZMod64.Bounds p]
    (m : Hex.FpPoly p) (c : Hex.ZMod64 p)
    (cert : Hex.Berlekamp.IrreducibilityCertificate) : Expr :=
  let mE := Hex.CertReify.reifyFpPolyOfNats pE boundsE (Hex.CertReify.fpCoeffNats m)
  let cE := Hex.CertReify.reifyZMod64 pE boundsE c.toNat
  let certE := Hex.CertReify.reifyRabinCert cert
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
    (Hex.CertReify.fpPolyType pE boundsE)
    (mkApp2 (mkConst ``Prod [Level.zero, Level.zero])
      (Hex.CertReify.zmodType pE boundsE)
      (mkConst ``Hex.Berlekamp.IrreducibilityCertificate))
    mE
    (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
      (Hex.CertReify.zmodType pE boundsE)
      (mkConst ``Hex.Berlekamp.IrreducibilityCertificate) cE certE)

/-- The untrusted factor search for `f : FpPoly p`: leading unit plus monic
irreducible factors with repetition, in nondecreasing size order. Correctness
is carried entirely by the emitted kernel checks. -/
meta def fpFactorSearch (p : Nat) [Hex.ZMod64.Bounds p]
    (hp : Hex.Nat.Prime p) (f : Hex.FpPoly p) :
    Hex.ZMod64 p × List (Hex.FpPoly p) :=
  letI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hp
  if f.size ≤ 1 then
    (f.coeff 0, [])
  else
    let dec := Hex.FpPoly.squareFreeDecomposition hp f
    let factors := dec.factors.flatMap fun sf =>
      let parts :=
        if hmonic : Hex.DensePoly.leadingCoeff sf.factor = 1 then
          (Hex.Berlekamp.berlekampFactor sf.factor (by exact hmonic)).factors
        else [sf.factor]
      parts.flatMap fun part => List.replicate sf.multiplicity part
    (dec.unit, factors.mergeSort fun a b => a.size ≤ b.size)

/-- Deduplicate a factor list by coefficient equality (order-preserving). -/
meta def dedupFactors {p : Nat} [Hex.ZMod64.Bounds p]
    (l : List (Hex.FpPoly p)) : List (Hex.FpPoly p) :=
  l.foldl (init := []) fun acc q =>
    if acc.any fun r => Hex.DensePoly.beqCoeffs r q then acc else acc ++ [q]

/-- Build the certified-cover entries for the distinct factors: each factor is
monic by construction, so the entry is `(q, 1, cert)`. Errors if a Rabin
certificate cannot be produced (the factors come from Berlekamp on square-free
parts, so this indicates an internal error) or if a replay is over budget. -/
meta def fpCoverEntries (tactic : String) (p : Nat) [Hex.ZMod64.Bounds p]
    (factors : List (Hex.FpPoly p)) :
    MetaM (List (Hex.FpPoly p × Hex.ZMod64 p ×
      Hex.Berlekamp.IrreducibilityCertificate)) := do
  let mut entries := []
  for q in dedupFactors factors do
    checkReplayBudget tactic p q.size
    if hmonic : Hex.DensePoly.leadingCoeff q = 1 then
      let some cert := Hex.Berlekamp.buildIrreducibilityCertificate? q (by exact hmonic)
        | throwError "{tactic}: internal error: no Rabin certificate for a \
            Berlekamp factor; please report this"
      entries := entries ++ [(q, (1 : Hex.ZMod64 p), cert)]
    else
      throwError "{tactic}: internal error: non-monic Berlekamp factor; \
          please report this"
  return entries

/-- Instance-carrying core of the `factor_poly` elaboration for
`f : FpPoly p`: returns the `Hex.FpPoly.Factored f` value as a raw `Expr`
over reified literal data. -/
meta def elabFpFactoredCore (tactic : String) (p : Nat)
    [Hex.ZMod64.Bounds p] (hpt : Hex.Nat.isPrimeTrial p = true)
    (pE boundsE RE zeroE decE fE : Expr) : MetaM Expr := do
      let hp : Hex.Nat.Prime p := Hex.Nat.isPrimeTrial_isPrime hpt
      let f ← evalFpPoly tactic p pE boundsE fE
      -- Opaque-input contract: the emitted checks state over the user's term,
      -- so it must be definitionally transparent down to its literal.
      let fLit := Hex.CertReify.reifyFpPolyOfNats pE boundsE
        (Hex.CertReify.fpCoeffNats f)
      unless ← isDefEq fLit fE do
        throwError "{tactic}: the polynomial{indentExpr fE}\
            \nevaluates to{indentExpr fLit}\
            \nbut is not definitionally transparent to the elaborator (an \
            imported definition without `@[expose]`?); the kernel could not \
            check the emitted certificate against it"
      let (scalar, factors) := fpFactorSearch p hp f
      -- Untrusted-search self-check before emitting anything.
      unless Hex.DensePoly.beqCoeffs
          (Hex.DensePoly.C scalar * factors.prod) f do
        throwError "{tactic}: internal error: the factor search product does \
            not reconstruct the input; please report this"
      let entries ← fpCoverEntries tactic p factors
      unless Hex.Berlekamp.checkIrredCover factors entries do
        throwError "{tactic}: internal error: the generated certificates fail \
            checkIrredCover; please report this"
      let polyTy := Hex.CertReify.fpPolyType pE boundsE
      let scalarE := Hex.CertReify.reifyZMod64 pE boundsE scalar.toNat
      let factorsE := listLit polyTy (factors.map fun q =>
        Hex.CertReify.reifyFpPolyOfNats pE boundsE (Hex.CertReify.fpCoeffNats q))
      let certifiedE := listLit (coverEntryType pE boundsE)
        (entries.map fun (m, c, cert) => reifyCoverEntry pE boundsE m c cert)
      let lhsE ← mkAppM ``HMul.hMul
        #[← mkAppM ``Hex.DensePoly.C #[scalarE], ← mkAppM ``List.prod #[factorsE]]
      let hmulE := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
        RE zeroE decE lhsE fE Hex.CertReify.reflTrue
      let hirredE := mkApp6
        (mkConst ``Hex.Berlekamp.irreducible_of_checkIrredCover)
        pE boundsE Hex.CertReify.reflTrue factorsE certifiedE
        Hex.CertReify.reflTrue
      return mkApp7 (mkConst ``Hex.FpPoly.Factored.mk)
        pE boundsE fE scalarE factorsE hmulE hirredE

/-- Dispatch the `factor_poly` elaboration for `f : FpPoly p`: primality and
bounds checks on the literal modulus, then the instance-carrying core. -/
meta def elabFactorPolyFp (tactic : String) (p : Nat)
    (pE boundsE RE zeroE decE fE : Expr) : MetaM Expr := do
  if hpt : Hex.Nat.isPrimeTrial p = true then
    if h1 : 0 < p then
      if h2 : p < 2 ^ 31 then
        @elabFpFactoredCore tactic p ⟨h1, h2⟩ hpt pE boundsE RE zeroE decE fE
      else
        throwError "{tactic}: internal error: modulus over the ZMod64 bound \
            despite a Bounds instance"
    else
      throwError "{tactic}: internal error: zero modulus despite a Bounds \
          instance"
  else
    throwError "{tactic}: the modulus {p} is not prime; factorization into \
        irreducibles requires a prime field"

/-- Elaborate a `factor_poly` argument and produce the structure value,
dispatching to providers for non-`FpPoly` input types. -/
meta def elabFactorPolyCore (stx : Syntax) (t : Syntax)
    (expectedType? : Option Expr) : Term.TermElabM Expr := do
  let pE ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let pE ← instantiateMVars pE
  checkClosed "factor_poly" pE
  let ty ← inferType pE
  match ← classify ty with
  | .fp p pE' boundsE RE zeroE decE =>
      elabFactorPolyFp "factor_poly" p pE' boundsE RE zeroE decE pE
  | _ =>
      dispatch (fun prov => prov.factorPoly? stx pE ty expectedType?)
        (fun declines =>
          throwError (unsupportedMessage "factor_poly" ty declines))

/-- `factor_poly f` elaborates to a certified irreducible factorization of
`f` (a `Hex.FpPoly.Factored f` for `f : FpPoly p`; providers add further
input types), usable as
`obtain ⟨scalar, factors, factors_mul, factors_irred⟩ := factor_poly f`. -/
syntax (name := factorPolyTerm) "factor_poly" term:max : term

@[term_elab factorPolyTerm] meta def elabFactorPoly : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(factor_poly $t) => do
        let e ← elabFactorPolyCore stx t expectedType?
        Term.ensureHasType expectedType? e
    | _ => Elab.throwUnsupportedSyntax

/-- The tactic form of `factor_poly`: introduces `scalar` and `factors` as
`let` bindings holding the literal factorization data, plus `factors_mul` and
`factors_irred` hypotheses stated over them. -/
syntax (name := factorPolyTac) "factor_poly" term:max : tactic

@[tactic factorPolyTac] meta def evalFactorPolyTac : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| factor_poly $t) => do
        let e ← Tactic.withMainContext do
          elabFactorPolyCore stx t none
        -- Destructure the emitted `Factored.mk` application.
        let args := e.getAppArgs
        unless e.getAppFn.isConstOf ``Hex.FpPoly.Factored.mk &&
            args.size == 7 do
          -- Provider-produced results: fall back to a plain `have`.
          Tactic.liftMetaTactic fun g => do
            let ty ← inferType e
            let (_, g) ← (← g.assert `factored ty e).intro1P
            return [g]
          return
        let (pE, boundsE, fE) := (args[0]!, args[1]!, args[2]!)
        let (scalarE, factorsE) := (args[3]!, args[4]!)
        let (hmulE, hirredE) := (args[5]!, args[6]!)
        Tactic.liftMetaTactic fun g => do
          let zmodTy := Hex.CertReify.zmodType pE boundsE
          let polyTy := Hex.CertReify.fpPolyType pE boundsE
          let listTy := mkApp (mkConst ``List [Level.zero]) polyTy
          let (fvS, g) ← (← g.define `scalar zmodTy scalarE).intro1P
          let (fvF, g) ← (← g.define `factors listTy factorsE).intro1P
          g.withContext do
            let sE := mkFVar fvS
            let fsE := mkFVar fvF
            let lhs ← mkAppM ``HMul.hMul
              #[← mkAppM ``Hex.DensePoly.C #[sE], ← mkAppM ``List.prod #[fsE]]
            let hmulTy ← mkAppM ``Eq #[lhs, fE]
            let (_, g) ← (← g.assert `factors_mul hmulTy hmulE).intro1P
            g.withContext do
              let hirredTy ←
                withLocalDeclD `q polyTy fun q => do
                  let mem ← mkAppM ``Membership.mem #[fsE, q]
                  let irred ← mkAppM ``Hex.FpPoly.Irreducible #[q]
                  mkForallFVars #[q] (← mkArrow mem irred)
              let (_, g) ← (← g.assert `factors_irred hirredTy hirredE).intro1P
              return [g]
    | _ => Elab.throwUnsupportedSyntax

end Hex.FactorTactic
