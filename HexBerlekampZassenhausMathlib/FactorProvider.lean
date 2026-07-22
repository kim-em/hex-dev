/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexBerlekamp.TacticCore
public meta import HexBerlekampZassenhaus.FactorProvider
public meta import HexBerlekampZassenhaus.ChoosePrimeData
public meta import HexBerlekampZassenhaus.CertReify
public meta import HexPolyZMathlib.PolyParse
public meta import HexBerlekampZassenhausMathlib.FactorTransport
public import HexBerlekamp.TacticCore
public import HexBerlekampZassenhaus.FactorProvider
public import HexBerlekampZassenhaus.ChoosePrimeData
public import HexBerlekampZassenhaus.CertReify
public import HexPolyZMathlib.PolyParse
public import HexBerlekampZassenhausMathlib.FactorTransport

public section

/-!
The `Polynomial ℤ` and strong `Hex.ZPoly` provider for the
`factor_poly`/`irreducibility` elaborators: importing this library upgrades
the tactics (declared in `HexBerlekamp.TacticCore` / probed by name, see
`providerNames`) to handle Mathlib integer polynomials, and extends the
`Hex.ZPoly` coverage of the free `HexBerlekampZassenhaus` provider (probed
first) with multi-prime degree-obstruction certificates for balanced factors
it declines.

For `Polynomial ℤ` inputs the heart is a parser-with-proof mirroring the
`Polynomial (ZMod q)` provider: a meta recursion over the input expression
that simultaneously evaluates each node to an executable `Hex.ZPoly` value
and builds a proof that `HexPolyZMathlib.toPolynomial` of the value equals
the node, combining child proofs through the named `toPolynomial_*` transport
lemmas. The compiled Berlekamp-Zassenhaus factorizer then runs as untrusted
search, per-factor irreducibility is certified by a free-layer
`Hex.ZPoly.IrredWitness` where one exists and by a multi-prime certificate
(`Hex.certifyIrreducible?`) otherwise, and the emitted terms apply the
kernel-decidable assemblers `Hex.FactoredPoly.ofZ` / `irreducible_ofZ` to
reified literal data with every certification slot discharged by
`Eq.refl true`. The factorizer never appears in emitted terms.

Balanced factors that are not Eisenstein at any small shift (the free
layer certifies e.g. `X⁴+1` that way) and whose modular factorizations also
fall outside the per-prime degree-sum obstruction language (e.g.
Swinnerton-Dyer polynomials) have no certificate in either language; the
provider declines with a diagnostic pointing at the kernel-decide fallbacks
`irreducibility!` / `factor_poly!` (`BangElab.lean`), which certify small
such inputs by re-running the factorizer in the kernel.
-/

namespace HexBerlekampZassenhausMathlib.FactorTactic

open Lean Meta Elab
open Hex.FactorTactic (ProviderResult)
open HexBerlekampZassenhaus.FactorTactic (evalZPoly checkTransparent
  searchWitness reifyWitness dedupZPolys)

/-- Match a (whnfR-normalized) type against `Polynomial ℤ`. -/
meta def intPolyInput? (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  let_expr Polynomial R _sem := ty | return false
  return (← whnfR R).isConstOf ``Int

/-- The type `Hex.ZPoly` as an expression. -/
meta def zpolyTy : Expr := mkConst ``Hex.ZPoly

/-- The transport `HexPolyZMathlib.toPolynomial` as an expression. -/
meta def tomlFn : Expr := mkConst ``HexPolyZMathlib.toPolynomial

/-- Certify a scalar equality `(k : ℤ) = c` by `decide`, checking at
elaboration time that the Boolean actually reduces to `true`. -/
meta def intDecideProof (tactic : String) (prop : Expr) : MetaM Expr := do
  let d ← mkDecide prop
  let r ← whnf d
  unless r.isConstOf ``Bool.true do
    throwError "{tactic}: failed to certify the coefficient equality{indentExpr prop}\
        \nby kernel reduction"
  mkDecideProof prop

/-- Combine two parsed children through a binary transport lemma: given child
results `(va, vaE, pa)`/`(vb, vbE, pb)` with `pa : toPolynomial vaE = a`
(and likewise `pb`), produce the node value `v`, the executable expression
`vaE ⋄ vbE`, and the chained proof `toPolynomial (vaE ⋄ vbE) = a ⋄ b`. -/
meta def combineBinary (eOrig : Expr) (v : Hex.ZPoly)
    (vaE vbE pa pb : Expr) (lem op : Name) :
    MetaM (Hex.ZPoly × Expr × Expr) := do
  let vE ← mkAppM op #[vaE, vbE]
  let t1 ← mkAppM lem #[vaE, vbE]
  let polyTy ← inferType eOrig
  let fnE ← mkAppOptM op #[some polyTy, some polyTy, some polyTy, none]
  let t2 ← mkCongr (← mkCongrArg fnE pa) pb
  return (v, vE, ← mkEqTrans t1 t2)

/-- Build a constant leaf from the evaluated coefficient `k`: value
`DensePoly.C k`, its literal expression, and the transport proof against the
Mathlib scalar `cRhsE` (certified by `decide`), chained through
`hTail : Polynomial.C cRhsE = e` when the leaf is not literally a `C`
application. -/
meta def constLeaf (tactic : String) (k : Int) (cRhsE : Expr)
    (hTail? : Option Expr) : MetaM (Hex.ZPoly × Expr × Expr) := do
  let v : Hex.ZPoly := Hex.DensePoly.C k
  let kE := toExpr k
  let vE ← mkAppM ``Hex.DensePoly.C #[kE]
  let t1 ← mkAppM ``HexPolyZMathlib.toPolynomial_C #[kE]
  -- t1 : toPolynomial (C k) = Polynomial.C k
  let hc ← intDecideProof tactic (← mkEq kE cRhsE)
  let some (_, _, rhs) := (← inferType t1).eq?
    | throwError "{tactic}: internal error: malformed transport lemma; please report this"
  let t2 ← mkCongrArg rhs.appFn! hc
  let prf ← mkEqTrans t1 t2
  match hTail? with
  | none => return (v, vE, prf)
  | some hTail => return (v, vE, ← mkEqTrans prf hTail)

/--
The parser-with-proof over `Polynomial ℤ` expressions: interpret
`X / C / numerals / + / - / * / neg / ^ (Nat literal)` (with named defs
unfolded one delta step at a time under a fuel guard), returning the
executable value `v : Hex.ZPoly`, an executable expression `vE` denoting it
(built from reified literals and executable operations), and a proof
`toPolynomial vE = e` (up to definitional equality on the right). Structural
heads are matched on the raw term: `whnf` would unfold
`Polynomial.C`/`X`/numerals into their `Finsupp` normal form and defeat the
match.
-/
meta partial def parseCore (tactic : String) (fuel : Nat) (e : Expr) :
    MetaM (Hex.ZPoly × Expr × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (va, vaE, pa) ← parseCore tactic fuel a
      let (vb, vbE, pb) ← parseCore tactic fuel b
      combineBinary e (va + vb) vaE vbE pa pb
        ``HexPolyZMathlib.toPolynomial_add ``HAdd.hAdd
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let (va, vaE, pa) ← parseCore tactic fuel a
      let (vb, vbE, pb) ← parseCore tactic fuel b
      combineBinary e (va - vb) vaE vbE pa pb
        ``HexPolyZMathlib.toPolynomial_sub ``HSub.hSub
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      let (va, vaE, pa) ← parseCore tactic fuel a
      let (vb, vbE, pb) ← parseCore tactic fuel b
      combineBinary e (va * vb) vaE vbE pa pb
        ``HexPolyZMathlib.toPolynomial_mul ``HMul.hMul
  | (``Neg.neg, #[_, _, a]) => do
      let (va, vaE, pa) ← parseCore tactic fuel a
      let vE ← mkAppM ``Neg.neg #[vaE]
      let t1 ← mkAppM ``HexPolyZMathlib.toPolynomial_neg #[vaE]
      let polyTy ← inferType e
      let negFn ← mkAppOptM ``Neg.neg #[some polyTy, none]
      let t2 ← mkCongrArg negFn pa
      return (-va, vE, ← mkEqTrans t1 t2)
  | (``HPow.hPow, #[_, _, _, _, a, nE]) => do
      let (va, vaE, pa) ← parseCore tactic fuel a
      let n ← HexPolyZMathlib.PolyParse.getNat tactic nE
      let polyTy ← inferType e
      let mulFn ← mkAppOptM ``HMul.hMul #[some polyTy, some polyTy, some polyTy, none]
      -- `a ^ 0`: value `1`, proof through `toPolynomial_one` and `pow_zero`.
      let mut v : Hex.ZPoly := 1
      let mut vE ← mkAppOptM ``One.one #[some zpolyTy, none]
      let mut prf ← mkEqTrans (mkConst ``HexPolyZMathlib.toPolynomial_one)
        (← mkEqSymm (← mkAppM ``pow_zero #[a]))
      -- `a ^ (k+1) = a ^ k * a`, peeled by `pow_succ`.
      for k in [0:n] do
        let vE' ← mkAppM ``HMul.hMul #[vE, vaE]
        let t1 ← mkAppM ``HexPolyZMathlib.toPolynomial_mul #[vE, vaE]
        let t2 ← mkCongr (← mkCongrArg mulFn prf) pa
        let t3 ← mkEqSymm (← mkAppM ``pow_succ #[a, mkNatLit k])
        v := v * va
        vE := vE'
        prf ← mkEqTrans t1 (← mkEqTrans t2 t3)
      return (v, vE, prf)
  | (``Polynomial.X, _) => do
      let v : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[0, 1]
      let vE ← Hex.CertReify.reifyZPoly v
      return (v, vE, mkConst ``HexBerlekampZassenhausMathlib.toPolynomial_X)
  | (``Polynomial.C, #[_, _, c]) => do
      let k ← HexPolyZMathlib.PolyParse.evalIntLit tactic c
      constLeaf tactic k c none
  | (``DFunLike.coe, args) =>
      -- `Polynomial.C c` elaborates to `⇑Polynomial.C c`.
      if args.size == 6 && args[4]!.getAppFn.isConstOf ``Polynomial.C then do
        let c := args[5]!
        let k ← HexPolyZMathlib.PolyParse.evalIntLit tactic c
        constLeaf tactic k c none
      else
        throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"
  | (``OfNat.ofNat, #[_, nE, _]) => do
      let n ← HexPolyZMathlib.PolyParse.getNat tactic nE
      let intTy := mkConst ``Int
      let cRhs ← mkAppOptM ``OfNat.ofNat #[some intTy, some (mkRawNatLit n), none]
      -- `Polynomial.C (OfNat n) = OfNat n` at the polynomial level.
      let hTail ←
        if n == 0 then
          mkAppOptM ``Polynomial.C_0 #[some intTy, none]
        else if n == 1 then
          mkAppOptM ``Polynomial.C_1 #[some intTy, none]
        else do
          let cHom ← mkAppOptM ``Polynomial.C #[some intTy, none]
          let polyTy ← inferType e
          mkAppOptM ``map_ofNat #[some intTy, some polyTy, some (← inferType cHom),
            none, none, none, none, some cHom, some (mkRawNatLit n), none]
      constLeaf tactic (Int.ofNat n) cRhs (some hTail)
  | _ =>
      -- Unfold a named def by one delta step under the fuel guard, else fail.
      if fuel == 0 then
        throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"
      else
        match ← unfoldDefinition? e with
        | some e' => parseCore tactic (fuel - 1) e'
        | none => throwError "{tactic}: unsupported polynomial syntax{indentExpr e}"

/-- Parse the full input: run `parseCore`, then recombine the parsed
expression with the flat reified literal of its value through one
`eq_of_beqCoeffs` kernel check, yielding `(f, fLit, hP)` with
`hP : toPolynomial fLit = e`. -/
meta def parseInput (tactic : String) (e : Expr) :
    MetaM (Hex.ZPoly × Expr × Expr) := do
  let (v, vE, prf) ← parseCore tactic 16 e
  let fLit ← Hex.CertReify.reifyZPoly v
  let intE := mkConst ``Int
  let zeroE ← synthInstance (← mkAppM ``Zero #[intE])
  let decE ← synthInstance (← mkAppM ``DecidableEq #[intE])
  let hroot := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
    intE zeroE decE fLit vE Hex.CertReify.reflTrue
  let hP ← mkEqTrans (← mkCongrArg tomlFn hroot) prf
  return (v, fLit, hP)

/-- The decline diagnostic for factors outside both certificate languages. -/
meta def coverDecline (tactic : String) (q : Hex.ZPoly) : MetaM MessageData := do
  let qE ← Hex.CertReify.reifyZPoly q
  return m!"{tactic}: the irreducible factor{indentExpr qE}\
      \nhas no single-prime modular witness, is not Eisenstein at any small \
      shift, and its balanced modular factorizations fall outside the \
      multi-prime per-prime degree-sum obstruction language (e.g. \
      Swinnerton-Dyer polynomials); no certificate-backed proof is \
      available, but the kernel-decide fallbacks `irreducibility!` / \
      `factor_poly!` can still certify small inputs by re-running the \
      factorizer in the kernel"

/-- Search a mixed certificate cover for a factor list: a free-layer
`IrredWitness` per distinct factor where one exists, a multi-prime
degree-obstruction certificate otherwise. Returns the decline diagnostic when
some factor has neither. -/
meta def searchCover (tactic : String) (factors : List Hex.ZPoly) :
    MetaM (Except MessageData
      (List (Hex.ZPoly × Hex.ZPoly.IrredWitness) ×
        List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate))) := do
  let mut certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness) := []
  let mut multiPrime : List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate) := []
  for q in dedupZPolys factors do
    match searchWitness q with
    | some w =>
        unless Hex.ZPoly.checkIrredWitness q w do
          throwError "{tactic}: internal error: a generated witness fails \
              checkIrredWitness; please report this"
        certified := certified ++ [(q, w)]
    | none =>
        match Hex.certifyIrreducible? q with
        | some cert =>
            unless checkMultiPrimeCert q cert do
              throwError "{tactic}: internal error: a generated multi-prime \
                  certificate fails checkMultiPrimeCert; please report this"
            multiPrime := multiPrime ++ [(q, cert)]
        | none => return .error (← coverDecline tactic q)
  unless checkMultiPrimeCover factors certified multiPrime do
    throwError "{tactic}: internal error: the generated certificates fail \
        checkMultiPrimeCover; please report this"
  return .ok (certified, multiPrime)

/-- Reify a `(factor, IrredWitness)` list as a literal `Expr`. -/
meta def reifyCertifiedList
    (certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness)) : MetaM Expr := do
  let pairTy := mkApp2 (mkConst ``Prod [.zero, .zero]) zpolyTy
    (mkConst ``Hex.ZPoly.IrredWitness)
  return Hex.FactorTactic.listLit pairTy (← certified.mapM fun (q, w) => do
    return mkApp4 (mkConst ``Prod.mk [.zero, .zero]) zpolyTy
      (mkConst ``Hex.ZPoly.IrredWitness)
      (← Hex.CertReify.reifyZPoly q) (reifyWitness w))

/-- Reify a `(factor, multi-prime certificate)` list as a literal `Expr`. -/
meta def reifyMultiList
    (multiPrime : List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate)) :
    MetaM Expr := do
  let certTy := mkConst ``Hex.ZPolyIrreducibilityCertificate
  let pairTy := mkApp2 (mkConst ``Prod [.zero, .zero]) zpolyTy certTy
  return Hex.FactorTactic.listLit pairTy (← multiPrime.mapM fun (q, cert) => do
    return mkApp4 (mkConst ``Prod.mk [.zero, .zero]) zpolyTy certTy
      (← Hex.CertReify.reifyZPoly q) (Hex.CertReify.reifyCertificate cert))

/-- The untrusted factor search shared by both `factor_poly` arms: factors
with repetition in nondecreasing size order, plus the scalar, self-checked
against the input. -/
meta def factorSearch (tactic : String) (f : Hex.ZPoly) :
    MetaM (Int × List Hex.ZPoly) := do
  let φ := Hex.ZPoly.factorize f
  let factors := (φ.factors.toList.flatMap fun (q, k) =>
    List.replicate k q).mergeSort fun a b => a.size ≤ b.size
  unless Hex.DensePoly.beqCoeffs (Hex.DensePoly.C φ.scalar * factors.prod) f do
    throwError "{tactic}: internal error: the factorization product does not \
        reconstruct the input; please report this"
  return (φ.scalar, factors)

/-- One irreducibility witness of either kind for a single polynomial. -/
meta inductive OneWitness where
  | free (w : Hex.ZPoly.IrredWitness)
  | multi (cert : Hex.ZPolyIrreducibilityCertificate)

/-- Search a single-polynomial witness: free-layer first, multi-prime
fallback; decline diagnostic for balanced inputs outside both languages,
targeted errors for zero/unit/reducible inputs. -/
meta def searchOne (tactic : String) (fE : Expr) (f : Hex.ZPoly) :
    MetaM (Except MessageData OneWitness) := do
  if f.size = 0 then
    throwError "{tactic}: the zero polynomial is not irreducible"
  if Hex.ZPoly.IsUnit f then
    throwError "{tactic}: the polynomial{indentExpr fE}\
        \nis a unit (±1), not irreducible"
  match searchWitness f with
  | some w =>
      unless Hex.ZPoly.checkIrredWitness f w do
        throwError "{tactic}: internal error: a generated witness fails \
            checkIrredWitness; please report this"
      return .ok (.free w)
  | none =>
      match Hex.certifyIrreducible? f with
      | some cert =>
          unless checkMultiPrimeCert f cert do
            throwError "{tactic}: internal error: a generated multi-prime \
                certificate fails checkMultiPrimeCert; please report this"
          return .ok (.multi cert)
      | none =>
          if Hex.ZPoly.isIrreducible f then
            return .error (← coverDecline tactic f)
          else
            let φ := Hex.ZPoly.factorize f
            let count := φ.factors.foldl (fun acc entry => acc + entry.2) 0
            throwError "{tactic}: the polynomial{indentExpr fE}\
                \nis not irreducible over ℤ: factor_poly finds {count} \
                irreducible factors (with multiplicity), scalar {φ.scalar}"

/-- Emit `irreducible_ofZ P fLit certified multiPrime (Eq.refl true) hP` for a
single-polynomial witness of either kind. -/
meta def emitIrreducibleOfZ (tactic : String) (P fLit hP : Expr)
    (f : Hex.ZPoly) (w : OneWitness) : MetaM Expr := do
  let (certified, multiPrime) :=
    match w with
    | .free wit => ([(f, wit)], [])
    | .multi cert => ([], [(f, cert)])
  unless checkMultiPrimeCover [f] certified multiPrime do
    throwError "{tactic}: internal error: the singleton certificate cover \
        fails checkMultiPrimeCover; please report this"
  return mkApp6 (mkConst ``HexBerlekampZassenhausMathlib.irreducible_ofZ)
    P fLit (← reifyCertifiedList certified) (← reifyMultiList multiPrime)
    Hex.CertReify.reflTrue hP

/-- Emit the free-layer proof `Hex.ZPoly.Irreducible fE` for a witness of
either kind. -/
meta def zpolyIrredProof (fE : Expr) (w : OneWitness) : MetaM Expr :=
  match w with
  | .free wit =>
      return mkApp3 (mkConst ``Hex.ZPoly.irreducible_of_checkIrredWitness)
        fE (reifyWitness wit) Hex.CertReify.reflTrue
  | .multi cert =>
      return mkApp6 (mkConst
          ``HexBerlekampZassenhausMathlib.zpolyIrreducible_of_checkIrreducibleCertLinear)
        fE (Hex.CertReify.reifyCertificate cert) Hex.CertReify.reflTrue
        Hex.CertReify.reflTrue Hex.CertReify.reflTrue Hex.CertReify.reflTrue

/-- The `factor_poly` arm for `Polynomial ℤ`: parse with proof, factorize as
untrusted search, certify the cover, and emit a reified
`Hex.FactoredPoly.ofZ` application. -/
meta def elabFactorInt (tactic : String) (e : Expr) :
    Term.TermElabM ProviderResult := do
  let (f, fLit, hP) ← parseInput tactic e
  let (scalar, factors) ← factorSearch tactic f
  match ← searchCover tactic factors with
  | .error why => return .declined why
  | .ok (certified, multiPrime) =>
      let factorsE := Hex.FactorTactic.listLit zpolyTy
        (← factors.mapM fun q => Hex.CertReify.reifyZPoly q)
      return .success (mkAppN (mkConst ``Hex.FactoredPoly.ofZ)
        #[e, fLit, toExpr scalar, factorsE, ← reifyCertifiedList certified,
          ← reifyMultiList multiPrime, Hex.CertReify.reflTrue,
          Hex.CertReify.reflTrue, hP])

/-- The `irreducibility` arm for `Polynomial ℤ`. -/
meta def elabIrredInt (tactic : String) (e : Expr) :
    Term.TermElabM ProviderResult := do
  let (f, fLit, hP) ← parseInput tactic e
  match ← searchOne tactic e f with
  | .error why => return .declined why
  | .ok w => return .success (← emitIrreducibleOfZ tactic e fLit hP f w)

/-- The strong `Hex.ZPoly` `factor_poly` arm: probed after the free provider,
so it certifies covers the free layer declines (balanced factors) through the
multi-prime certificates, emitting a `Hex.ZPoly.Factored` whose
`factors_irred` is one `irreducible_of_checkMultiPrimeCover` check. -/
meta def factorZPolyStrong (fE : Expr) : Term.TermElabM ProviderResult := do
  let f ← evalZPoly "factor_poly" fE
  discard <| checkTransparent "factor_poly" f fE
  let (scalar, factors) ← factorSearch "factor_poly" f
  match ← searchCover "factor_poly" factors with
  | .error why => return .declined why
  | .ok (certified, multiPrime) =>
      let intE := mkConst ``Int
      let zeroE ← synthInstance (← mkAppM ``Zero #[intE])
      let decE ← synthInstance (← mkAppM ``DecidableEq #[intE])
      let scalarE := toExpr scalar
      let factorsE := Hex.FactorTactic.listLit zpolyTy
        (← factors.mapM fun q => Hex.CertReify.reifyZPoly q)
      let lhsE ← mkAppM ``HMul.hMul
        #[← mkAppM ``Hex.DensePoly.C #[scalarE], ← mkAppM ``List.prod #[factorsE]]
      let hmulE := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
        intE zeroE decE lhsE fE Hex.CertReify.reflTrue
      let hirredE := mkApp4
        (mkConst ``HexBerlekampZassenhausMathlib.irreducible_of_checkMultiPrimeCover)
        factorsE (← reifyCertifiedList certified) (← reifyMultiList multiPrime)
        Hex.CertReify.reflTrue
      return .success (mkApp5 (mkConst ``Hex.ZPoly.Factored.mk)
        fE scalarE factorsE hmulE hirredE)

/-- The strong `Hex.ZPoly` `irreducibility` arm: free-layer conclusion
`Hex.ZPoly.Irreducible fE`, certified through the multi-prime checker when
the free provider declined. -/
meta def irredZPolyStrong (fE : Expr) : Term.TermElabM ProviderResult := do
  let f ← evalZPoly "irreducibility" fE
  discard <| checkTransparent "irreducibility" f fE
  match ← searchOne "irreducibility" fE f with
  | .error why => return .declined why
  | .ok w => return .success (← zpolyIrredProof fE w)

/-- Match `HexPolyZMathlib.toPolynomial f` (or the unfolded
`HexPolyMathlib.toPolynomial` at `R = ℤ`) and return `f`. -/
meta def matchToPolynomial? (arg : Expr) : MetaM (Option Expr) := do
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

/-- Certify `proof` against the goal up to definitional equality and report
success. -/
meta def closeGoal (tgt proof : Expr) : MetaM ProviderResult := do
  unless ← isDefEq (← inferType proof) tgt do
    throwError "irreducibility: the certified statement\
        {indentExpr (← inferType proof)}\
        \nis not definitionally equal to the goal{indentExpr tgt}"
  return .success proof

/-- Goal mode: close `Hex.ZPoly.Irreducible e` (free-layer statement),
`Irreducible (toPolynomial f)`, and `Irreducible P` for parseable
`P : Polynomial ℤ`. -/
meta def goalIrredInt (goal : MVarId) : Tactic.TacticM ProviderResult := do
  goal.withContext do
    let tgt ← instantiateMVars (← goal.getType)
    if tgt.getAppFn.isConstOf ``Hex.ZPoly.Irreducible &&
        tgt.getAppNumArgs == 1 then
      let fE := tgt.appArg!
      Hex.FactorTactic.checkClosed "irreducibility" fE
      let f ← evalZPoly "irreducibility" fE
      discard <| checkTransparent "irreducibility" f fE
      match ← searchOne "irreducibility" fE f with
      | .error why => return .declined why
      | .ok w => closeGoal tgt (← zpolyIrredProof fE w)
    else
      let tgtW ← whnfR tgt
      let_expr Irreducible M _inst arg := tgtW | return .notApplicable
      unless ← intPolyInput? M do return .notApplicable
      Hex.FactorTactic.checkClosed "irreducibility" arg
      match ← matchToPolynomial? arg with
      | some fE =>
          let f ← evalZPoly "irreducibility" fE
          discard <| checkTransparent "irreducibility" f fE
          let fLit ← Hex.CertReify.reifyZPoly f
          let intE := mkConst ``Int
          let zeroE ← synthInstance (← mkAppM ``Zero #[intE])
          let decE ← synthInstance (← mkAppM ``DecidableEq #[intE])
          let hroot := mkApp6 (mkConst ``Hex.DensePoly.eq_of_beqCoeffs [Level.zero])
            intE zeroE decE fLit fE Hex.CertReify.reflTrue
          let hP ← mkCongrArg tomlFn hroot
          match ← searchOne "irreducibility" fE f with
          | .error why => return .declined why
          | .ok w =>
              closeGoal tgt
                (← emitIrreducibleOfZ "irreducibility" (mkApp tomlFn fE) fLit hP f w)
      | none =>
          let (f, fLit, hP) ← parseInput "irreducibility" arg
          match ← searchOne "irreducibility" arg f with
          | .error why => return .declined why
          | .ok w =>
              closeGoal tgt (← emitIrreducibleOfZ "irreducibility" arg fLit hP f w)

end HexBerlekampZassenhausMathlib.FactorTactic

namespace HexBerlekampZassenhausMathlib.FactorTactic

open Lean Elab

/-- The `Polynomial ℤ` / strong `Hex.ZPoly` provider, probed by name from
`Hex.FactorTactic.providerNames` — renaming it severs the hook (the bridge
test suite is the liveness canary). Probed after the free `Hex.ZPoly`
provider, so its `ZPoly` arms only see inputs the free layer declined. -/
public meta def provider : Hex.FactorTactic.Provider where
  version := Hex.FactorTactic.Provider.abiVersion
  factorPoly? := fun _stx eP ty _expectedType? => do
    match ← Hex.FactorTactic.classify ty with
    | .zpoly _ _ _ => factorZPolyStrong eP
    | .fp _ _ _ _ _ _ => return .notApplicable
    | .other =>
        if ← intPolyInput? ty then elabFactorInt "factor_poly" eP
        else return .notApplicable
  irreducibility? := fun _stx eP ty _expectedType? => do
    match ← Hex.FactorTactic.classify ty with
    | .zpoly _ _ _ => irredZPolyStrong eP
    | .fp _ _ _ _ _ _ => return .notApplicable
    | .other =>
        if ← intPolyInput? ty then elabIrredInt "irreducibility" eP
        else return .notApplicable
  goalIrred? := goalIrredInt

end HexBerlekampZassenhausMathlib.FactorTactic
