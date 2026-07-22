/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.FactorPolyElab
public meta import HexBerlekampMathlib.FactorPoly
public import HexBerlekamp.FactorPolyElab
public import HexBerlekampMathlib.FactorPoly

public section

/-!
The `Polynomial (ZMod q)` provider for the `factor_poly`/`irreducibility`
elaborators: importing this library upgrades the tactics (declared in
`HexBerlekamp.TacticCore` / probed by name, see `providerNames`) to handle
Mathlib polynomials over prime fields with a literal modulus.

The heart of the provider is a parser-with-proof: a meta recursion over the
input `Polynomial (ZMod q)` expression that simultaneously evaluates each node
to an executable `Hex.FpPoly q` value and builds a proof that the transported
value equals the node, combining child proofs through the named
`toMathlibPolynomial_*` transport lemmas. The compiled Berlekamp factorizer
then runs as untrusted search exactly as in the `FpPoly` pipeline, and the
emitted terms apply the kernel-decidable assemblers `Hex.FactoredPoly.ofFp` /
`HexBerlekampMathlib.irreducible_ofFp` to reified literal data: every
certification slot is discharged by `Eq.refl true`/`Eq.refl false`, plus the
parser-built bridge equation. The factorizer never appears in emitted terms.
-/

namespace HexBerlekampMathlib.FactorTactic

open Lean Meta Elab
open Hex.FactorTactic (ProviderResult)

/-- Match a (whnfR-normalized) type against `Polynomial (ZMod q)` for a
literal `q`, returning the modulus and its literal expression. -/
meta def zmodInput? (ty : Expr) : MetaM (Option (Nat × Expr)) := do
  let ty ← whnfR ty
  let_expr Polynomial R _sem := ty | return none
  let R ← whnfR R
  let_expr ZMod qE := R | return none
  let some q := qE.nat? | return none
  return some (q, qE)

/-- Extract a `Nat` literal from an exponent expression (numerals and raw
literals). -/
meta def getNatLit (tactic : String) (e : Expr) : MetaM Nat := do
  match ← getNatValue? e with
  | some n => return n
  | none =>
    match (← whnfR e).getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) =>
      match ← getNatValue? n with
      | some k => return k
      | none => throwError "{tactic}: expected a Nat literal exponent{indentExpr e}"
    | _ => throwError "{tactic}: expected a Nat literal exponent{indentExpr e}"

/-- Evaluate a closed `ZMod q` coefficient expression to its canonical `Nat`
representative by whnf-reducing `ZMod.val c`. -/
meta def evalZModVal (tactic : String) (pE cE : Expr) : MetaM Nat := do
  let valE ← mkAppOptM ``ZMod.val #[some pE, some cE]
  let r ← whnf valE
  match ← getNatValue? r with
  | some n => return n
  | none =>
      throwError "{tactic}: failed to evaluate the coefficient{indentExpr cE}\
          \nto a canonical residue (reduction got stuck at{indentExpr r})"

/-- Certify a scalar equality `toZMod (ofNat q k) = c` by `decide`, checking at
elaboration time that the Boolean actually reduces to `true`. -/
meta def scalarDecideProof (tactic : String) (prop : Expr) : MetaM Expr := do
  let d ← mkDecide prop
  let r ← whnf d
  unless r.isConstOf ``Bool.true do
    throwError "{tactic}: failed to certify the coefficient equality{indentExpr prop}\
        \nby kernel reduction"
  mkDecideProof prop

/-- The partial application `toMathlibPolynomial (p := q)` as an expression. -/
meta def tomlFn (pE boundsE : Expr) : Expr :=
  mkApp2 (mkConst ``HexBerlekampMathlib.toMathlibPolynomial) pE boundsE

/-- Combine two parsed children through a binary transport lemma: given child
results `(va, vaE, pa)`/`(vb, vbE, pb)` with `pa : toMathlibPolynomial vaE = a`
(and likewise `pb`), produce the node value `v`, the executable expression
`vaE ⋄ vbE`, and the chained proof
`toMathlibPolynomial (vaE ⋄ vbE) = a ⋄ b`. -/
meta def combineBinary {q : Nat} [Hex.ZMod64.Bounds q]
    (pE boundsE eOrig : Expr) (v : Hex.FpPoly q)
    (vaE vbE pa pb : Expr) (lem op : Name) :
    MetaM (Hex.FpPoly q × Expr × Expr) := do
  let vE ← mkAppM op #[vaE, vbE]
  let t1 ← mkAppOptM lem #[some pE, some boundsE, some vaE, some vbE]
  let polyTy ← inferType eOrig
  let fnE ← mkAppOptM op #[some polyTy, some polyTy, some polyTy, none]
  let t2 ← mkCongr (← mkCongrArg fnE pa) pb
  return (v, vE, ← mkEqTrans t1 t2)

/-- Build a constant leaf from the canonical residue `k`: value
`DensePoly.C (ofNat q k)`, its literal expression, and the transport proof
against the Mathlib scalar `cRhsE` (certified by `decide`), chained through
`hTail : Polynomial.C cRhsE = e` when the leaf is not literally a `C`
application. -/
meta def constLeaf {q : Nat} [Hex.ZMod64.Bounds q]
    (tactic : String) (pE boundsE : Expr) (k : Nat) (cRhsE : Expr)
    (hTail? : Option Expr) : MetaM (Hex.FpPoly q × Expr × Expr) := do
  let v : Hex.FpPoly q := Hex.DensePoly.C (Hex.ZMod64.ofNat q k)
  let zLit := Hex.CertReify.reifyZMod64 pE boundsE k
  let vE ← mkAppM ``Hex.DensePoly.C #[zLit]
  let t1 ← mkAppOptM ``HexBerlekampMathlib.toMathlibPolynomial_C
    #[some pE, some boundsE, some zLit]
  -- t1 : toMathlibPolynomial (C zLit) = Polynomial.C (toZMod zLit)
  let toZModE ← mkAppOptM ``HexModArithMathlib.ZMod64.toZMod
    #[some pE, some boundsE, some zLit]
  let hc ← scalarDecideProof tactic (← mkEq toZModE cRhsE)
  let some (_, _, rhs) := (← inferType t1).eq?
    | throwError "{tactic}: internal error: malformed transport lemma; please report this"
  let t2 ← mkCongrArg rhs.appFn! hc
  let prf ← mkEqTrans t1 t2
  match hTail? with
  | none => return (v, vE, prf)
  | some hTail => return (v, vE, ← mkEqTrans prf hTail)

/--
The parser-with-proof over `Polynomial (ZMod q)` expressions: interpret
`X / C / numerals / + / - / * / neg / ^ (Nat literal)` (with named defs
unfolded one delta step at a time under a fuel guard), returning the
executable value `v : FpPoly q`, an executable expression `vE` denoting it
(built from reified literals and executable operations), and a proof
`toMathlibPolynomial vE = e` (up to definitional equality on the right).
Structural heads are matched on the raw term: `whnf` would unfold
`Polynomial.C`/`X`/numerals into their `Finsupp` normal form and defeat the
match.
-/
meta partial def parseCore (tactic : String) (q : Nat) [Hex.ZMod64.Bounds q]
    (pE boundsE : Expr) (fuel : Nat) (e : Expr) :
    MetaM (Hex.FpPoly q × Expr × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (va, vaE, pa) ← parseCore tactic q pE boundsE fuel a
      let (vb, vbE, pb) ← parseCore tactic q pE boundsE fuel b
      combineBinary pE boundsE e (va + vb) vaE vbE pa pb
        ``HexBerlekampMathlib.toMathlibPolynomial_add ``HAdd.hAdd
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let (va, vaE, pa) ← parseCore tactic q pE boundsE fuel a
      let (vb, vbE, pb) ← parseCore tactic q pE boundsE fuel b
      combineBinary pE boundsE e (va - vb) vaE vbE pa pb
        ``HexBerlekampMathlib.toMathlibPolynomial_sub ``HSub.hSub
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      let (va, vaE, pa) ← parseCore tactic q pE boundsE fuel a
      let (vb, vbE, pb) ← parseCore tactic q pE boundsE fuel b
      combineBinary pE boundsE e (va * vb) vaE vbE pa pb
        ``HexBerlekampMathlib.toMathlibPolynomial_mul ``HMul.hMul
  | (``Neg.neg, #[_, _, a]) => do
      let (va, vaE, pa) ← parseCore tactic q pE boundsE fuel a
      let vE ← mkAppM ``Neg.neg #[vaE]
      let t1 ← mkAppOptM ``HexBerlekampMathlib.toMathlibPolynomial_neg
        #[some pE, some boundsE, some vaE]
      let polyTy ← inferType e
      let negFn ← mkAppOptM ``Neg.neg #[some polyTy, none]
      let t2 ← mkCongrArg negFn pa
      return (-va, vE, ← mkEqTrans t1 t2)
  | (``HPow.hPow, #[_, _, _, _, a, nE]) => do
      let (va, vaE, pa) ← parseCore tactic q pE boundsE fuel a
      let n ← getNatLit tactic nE
      let polyTy ← inferType e
      let fpTy := Hex.CertReify.fpPolyType pE boundsE
      let mulFn ← mkAppOptM ``HMul.hMul #[some polyTy, some polyTy, some polyTy, none]
      -- `a ^ 0`: value `1`, proof through `toMathlibPolynomial_one` and `pow_zero`.
      let mut v : Hex.FpPoly q := 1
      let mut vE ← mkAppOptM ``One.one #[some fpTy, none]
      let oneLem ← mkAppOptM ``HexBerlekampMathlib.toMathlibPolynomial_one
        #[some pE, some boundsE]
      let mut prf ← mkEqTrans oneLem (← mkEqSymm (← mkAppM ``pow_zero #[a]))
      -- `a ^ (k+1) = a ^ k * a`, peeled by `pow_succ`.
      for k in [0:n] do
        let vE' ← mkAppM ``HMul.hMul #[vE, vaE]
        let t1 ← mkAppOptM ``HexBerlekampMathlib.toMathlibPolynomial_mul
          #[some pE, some boundsE, some vE, some vaE]
        let t2 ← mkCongr (← mkCongrArg mulFn prf) pa
        let t3 ← mkEqSymm (← mkAppM ``pow_succ #[a, mkNatLit k])
        v := v * va
        vE := vE'
        prf ← mkEqTrans t1 (← mkEqTrans t2 t3)
      return (v, vE, prf)
  | (``Polynomial.X, _) => do
      let vE := mkApp2 (mkConst ``Hex.FpPoly.X) pE boundsE
      let prf ← mkAppOptM ``HexBerlekampMathlib.toMathlibPolynomial_X
        #[some pE, some boundsE]
      return (Hex.FpPoly.X (p := q), vE, prf)
  | (``Polynomial.C, #[_, _, c]) => do
      let k ← evalZModVal tactic pE c
      constLeaf tactic pE boundsE k c none
  | (``DFunLike.coe, args) =>
      -- `Polynomial.C c` elaborates to `⇑Polynomial.C c`.
      if args.size == 6 && args[4]!.getAppFn.isConstOf ``Polynomial.C then do
        let c := args[5]!
        let k ← evalZModVal tactic pE c
        constLeaf tactic pE boundsE k c none
      else
        throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"
  | (``OfNat.ofNat, #[_, nE, _]) => do
      let n ← getNatLit tactic nE
      let zmodTy := mkApp (mkConst ``ZMod) pE
      let cRhs ← mkAppOptM ``OfNat.ofNat #[some zmodTy, some (mkRawNatLit n), none]
      -- `Polynomial.C (OfNat n) = OfNat n` at the polynomial level.
      let hTail ←
        if n == 0 then
          mkAppOptM ``Polynomial.C_0 #[some zmodTy, none]
        else if n == 1 then
          mkAppOptM ``Polynomial.C_1 #[some zmodTy, none]
        else do
          let cHom ← mkAppOptM ``Polynomial.C #[some zmodTy, none]
          let polyTy ← inferType e
          mkAppOptM ``map_ofNat #[some zmodTy, some polyTy, some (← inferType cHom),
            none, none, none, none, some cHom, some (mkRawNatLit n), none]
      constLeaf tactic pE boundsE (n % q) cRhs (some hTail)
  | _ =>
      -- Unfold a named def by one delta step under the fuel guard, else fail.
      if fuel == 0 then
        throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"
      else
        match ← unfoldDefinition? e with
        | some e' => parseCore tactic q pE boundsE (fuel - 1) e'
        | none => throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"

/-- Parse the full input: run `parseCore`, then recombine the parsed
expression with the flat reified literal of its value through one
`eq_of_beqCoeffs` kernel check, yielding `(f, fLit, hP)` with
`hP : toMathlibPolynomial fLit = e`. -/
meta def parseInput (tactic : String) (q : Nat) [Hex.ZMod64.Bounds q]
    (pE boundsE : Expr) (e : Expr) :
    MetaM (Hex.FpPoly q × Expr × Expr) := do
  let (v, vE, prf) ← parseCore tactic q pE boundsE 16 e
  let fLit := Hex.CertReify.reifyFpPolyOfNats pE boundsE (Hex.CertReify.fpCoeffNats v)
  let RE := Hex.CertReify.zmodType pE boundsE
  let zeroE ← synthInstance (← mkAppM ``Zero #[RE])
  let decE ← synthInstance (← mkAppM ``DecidableEq #[RE])
  let hroot := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
    RE zeroE decE fLit vE Hex.CertReify.reflTrue
  let hP ← mkEqTrans (← mkCongrArg (tomlFn pE boundsE) hroot) prf
  return (v, fLit, hP)

/-- The `factor_poly` arm: parse with proof, run the shared `FpPoly` factor
search as untrusted search, self-check, and emit a reified
`Hex.FactoredPoly.ofFp` application. -/
meta def elabFactorZMod (tactic : String) (q : Nat) [Hex.ZMod64.Bounds q]
    (hpt : Hex.Nat.isPrimeTrial q = true) (pE e : Expr) :
    Term.TermElabM Expr := do
  let boundsE := Hex.CertReify.reifyBounds pE
  let (f, fLit, hP) ← parseInput tactic q pE boundsE e
  let hp : Hex.Nat.Prime q := Hex.Nat.isPrimeTrial_isPrime hpt
  let (scalar, factors) := Hex.FactorTactic.fpFactorSearch q hp f
  -- Untrusted-search self-checks before emitting anything.
  unless Hex.DensePoly.beqCoeffs (Hex.DensePoly.C scalar * factors.prod) f do
    throwError "{tactic}: internal error: the factor search product does not \
        reconstruct the input; please report this"
  unless factors.all (fun g => decide (0 < g.degree?.getD 0)) do
    throwError "{tactic}: internal error: a constant factor appeared in the \
        factor list; please report this"
  let entries ← Hex.FactorTactic.fpCoverEntries tactic q factors
  unless Hex.Berlekamp.checkIrredCover factors entries do
    throwError "{tactic}: internal error: the generated certificates fail \
        checkIrredCover; please report this"
  let polyTy := Hex.CertReify.fpPolyType pE boundsE
  let scalarE := Hex.CertReify.reifyZMod64 pE boundsE scalar.toNat
  let factorsE := Hex.FactorTactic.listLit polyTy (factors.map fun g =>
    Hex.CertReify.reifyFpPolyOfNats pE boundsE (Hex.CertReify.fpCoeffNats g))
  let certifiedE := Hex.FactorTactic.listLit (Hex.FactorTactic.coverEntryType pE boundsE)
    (entries.map fun (m, c, cert) => Hex.FactorTactic.reifyCoverEntry pE boundsE m c cert)
  return mkAppN (mkConst ``Hex.FactoredPoly.ofFp)
    #[pE, boundsE, e, fLit, scalarE, factorsE, certifiedE,
      Hex.CertReify.reflTrue, Hex.CertReify.reflTrue, Hex.CertReify.reflTrue,
      Hex.CertReify.reflTrue, hP]

/-- The `irreducibility` arm: parse with proof, build the Rabin certificate as
untrusted search, self-check, and emit a reified
`HexBerlekampMathlib.irreducible_ofFp` application. -/
meta def elabIrredZMod (tactic : String) (q : Nat) [Hex.ZMod64.Bounds q]
    (hpt : Hex.Nat.isPrimeTrial q = true) (pE e : Expr) :
    Term.TermElabM Expr := do
  let boundsE := Hex.CertReify.reifyBounds pE
  let (f, fLit, hP) ← parseInput tactic q pE boundsE e
  if f.size = 0 then
    throwError "{tactic}: the zero polynomial is not irreducible"
  if f.size = 1 then
    throwError "{tactic}: the polynomial{indentExpr e}\
        \nis a nonzero constant, hence a unit over F_{q}, not irreducible"
  Hex.FactorTactic.checkReplayBudget tactic q f.size
  let (unit, m) := Hex.FpPoly.normalizeMonic f
  if hmonic : Hex.DensePoly.leadingCoeff m = 1 then
    match Hex.Berlekamp.buildIrreducibilityCertificate? m (by exact hmonic) with
    | none =>
        let hp : Hex.Nat.Prime q := Hex.Nat.isPrimeTrial_isPrime hpt
        let (_, factors) := Hex.FactorTactic.fpFactorSearch q hp f
        throwError "{tactic}: the polynomial{indentExpr e}\
            \nis not irreducible over F_{q}: factor_poly finds \
            {factors.length} irreducible factors (with multiplicity)"
    | some cert =>
        -- Untrusted-search self-checks before emitting anything.
        unless decide (unit = 0) = false &&
            Hex.DensePoly.beqCoeffs (Hex.DensePoly.scale unit m) f &&
            Hex.Berlekamp.checkMonicCert m cert &&
            decide (0 < f.degree?.getD 0) do
          throwError "{tactic}: internal error: the generated certificate \
              fails its own checks; please report this"
        let mE := Hex.CertReify.reifyFpPolyOfNats pE boundsE (Hex.CertReify.fpCoeffNats m)
        let cE := Hex.CertReify.reifyZMod64 pE boundsE unit.toNat
        let certE := Hex.CertReify.reifyRabinCert cert
        return mkAppN (mkConst ``HexBerlekampMathlib.irreducible_ofFp)
          #[pE, boundsE, e, fLit, mE, cE, certE,
            Hex.CertReify.reflTrue, Hex.CertReify.reflFalse, Hex.CertReify.reflTrue,
            Hex.CertReify.reflTrue, Hex.CertReify.reflTrue, hP]
  else
    throwError "{tactic}: internal error: non-monic normalization; please \
        report this"

/-- Shared modulus scaffolding: match the input type, check primality and the
`ZMod64` bounds, and run the continuation with the `Bounds` instance in
scope. Non-`Polynomial (ZMod q)` types are `notApplicable`; composite or
oversized moduli are declined with a diagnostic. -/
meta def withZModInput (tactic : String) (ty : Expr)
    (k : (q : Nat) → Hex.ZMod64.Bounds q → Hex.Nat.isPrimeTrial q = true →
      Expr → Term.TermElabM Expr) :
    Term.TermElabM ProviderResult := do
  let some (q, qE) ← zmodInput? ty | return .notApplicable
  -- `isPrimeTrial` is Θ(q) at elaboration time, and its emitted slot
  -- kernel-replays at the same cost, so check the `ZMod64` bound and the
  -- replay budget before running it.
  if h1 : 0 < q then
    if h2 : q < 2 ^ 31 then
      if q ≤ Hex.FactorTactic.replayBudget then
        if hpt : Hex.Nat.isPrimeTrial q = true then
          return .success (← k q ⟨h1, h2⟩ hpt qE)
        else
          return .declined m!"{tactic}: Polynomial (ZMod q) inputs need a \
              prime modulus, but {q} is not prime"
      else
        return .declined m!"{tactic}: the modulus {q} needs a kernel \
            primality replay of roughly {q} steps, over the supported \
            budget ({Hex.FactorTactic.replayBudget})"
    else
      return .declined m!"{tactic}: the modulus {q} is over the ZMod64 \
          bound (2^31), so the Polynomial (ZMod q) provider cannot \
          certify it"
  else
    return .notApplicable

/-- Goal mode: close `Irreducible P` for `P : Polynomial (ZMod q)`. -/
meta def goalIrredZMod (goal : MVarId) : Tactic.TacticM ProviderResult := do
  goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    unless tgt.getAppFn.isConstOf ``Irreducible && tgt.getAppNumArgs == 3 do
      return .notApplicable
    let args := tgt.getAppArgs
    let eP := args[2]!
    let some _ ← zmodInput? args[0]! | return .notApplicable
    Hex.FactorTactic.checkClosed "irreducibility" eP
    withZModInput "irreducibility" args[0]! fun q inst hpt qE => do
      let proof ← @elabIrredZMod "irreducibility" q inst hpt qE eP
      unless ← isDefEq (← inferType proof) tgt do
        throwError "irreducibility: the certified statement\
            {indentExpr (← inferType proof)}\
            \nis not definitionally equal to the goal{indentExpr tgt}"
      return proof

end HexBerlekampMathlib.FactorTactic

namespace HexBerlekampMathlib.FactorTactic

open Lean Elab

/-- The `Polynomial (ZMod q)` provider, probed by name from
`Hex.FactorTactic.providerNames` — renaming it severs the hook (the bridge
test suite is the liveness canary). -/
public meta def provider : Hex.FactorTactic.Provider where
  version := Hex.FactorTactic.Provider.abiVersion
  factorPoly? := fun _stx eP ty _expectedType? =>
    withZModInput "factor_poly" ty fun q inst hpt qE =>
      @elabFactorZMod "factor_poly" q inst hpt qE eP
  irreducibility? := fun _stx eP ty _expectedType? =>
    withZModInput "irreducibility" ty fun q inst hpt qE =>
      @elabIrredZMod "irreducibility" q inst hpt qE eP
  goalIrred? := goalIrredZMod

end HexBerlekampMathlib.FactorTactic
