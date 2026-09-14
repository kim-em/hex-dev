/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexCharPoly.CharPolyElab
public meta import Mathlib.Data.Fin.VecNotation
public import HexCharPolyMathlib.Kernel
public meta import HexMatrixMathlib.Literal
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Lean

public section

/-!
The Mathlib `Matrix (Fin n) (Fin n) Int` arm of `char_poly`.

The matrix is materialized for compiled evaluation and
computed by the Mathlib-free Berkowitz implementation.  The emitted proof
uses `equiv_charPoly`; Mathlib's noncomputable `Matrix.charpoly` is never
evaluated by the elaborator or by a Boolean checker.
-/

namespace HexCharPolyMathlib

open Hex HexMatrixMathlib HexPolyMathlib
open Matrix Polynomial

/-- A Mathlib characteristic polynomial computed and certified by
`char_poly`. -/
structure CharPolyResult {n : Nat} (A : Matrix (Fin n) (Fin n) Int) where
  /-- The computed Mathlib polynomial. -/
  poly : Polynomial Int
  /-- The computed polynomial is Mathlib's characteristic polynomial. -/
  charPoly_eq : A.charpoly = poly

/-- The certified result type for the Mathlib frontend. -/
abbrev Certified {n : Nat} (A : Matrix (Fin n) (Fin n) Int) := CharPolyResult A

/-- The literal identification and packed certificate yield the polynomial. -/
@[expose] noncomputable def CharPolyResult.ofCheck {n : Nat}
    (A : Matrix (Fin n) (Fin n) Int) (rs : List (List Int))
    (w : Hex.Matrix.CharPolyKernel.Witness) (descending : List Int) (p : Hex.DensePoly Int)
    (ha : A = HexMatrixMathlib.ofLists n n rs)
    (hc : Hex.Matrix.CharPolyKernel.checkCharPolyList n rs w descending = true)
    (hp : Hex.DensePoly.beqCoeffs (Hex.DensePoly.ofCoeffs descending.reverse.toArray) p = true) :
    CharPolyResult A where
  poly := equiv p
  charPoly_eq := by
    rw [ha, charpoly_eq_of_checkList n rs w descending hc]
    exact congrArg equiv (Hex.DensePoly.eq_of_beqCoeffs hp)

/-- The executable dense polynomial `#[0, 1]` transports to Mathlib's `X`. -/
theorem toPolynomial_x :
    HexPolyMathlib.toPolynomial
      (Hex.DensePoly.ofCoeffs #[(0 : Int), 1]) =
      (Polynomial.X : Polynomial Int) := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, Hex.DensePoly.coeff_ofCoeffs,
    Polynomial.coeff_X]
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => rfl

namespace CharPolyTactic

open Lean Meta Elab

/-- A closed, evaluated Mathlib matrix with its dependent dimension. -/
private meta structure MathlibInput where
  n : Nat
  expr : Expr
  value : Hex.Matrix Int n n
  literal : HexMatrixMathlib.Literal.Recognized

/-- Match `Fin n → Fin n → Int`, the reducible representation of the
supported Mathlib matrix type. -/
private meta def matrixDim? (ty : Expr) : MetaM (Option Nat) := do
  let_expr _root_.Matrix rows cols coeff := ty | return none
  let_expr Fin nRows := (← whnfR rows) | return none
  let_expr Fin nCols := (← whnfR cols) | return none
  unless (← whnfR coeff).isConstOf ``Int do
    throwError "char_poly declined: unsupported Mathlib matrix coefficient type{indentExpr coeff}\nOnly Int matrices are currently supported"
  let some n ← getNatValue? nRows |
    throwError "char_poly: the Mathlib matrix dimension must reduce to a concrete natural number{indentExpr nRows}"
  let some m ← getNatValue? nCols |
    throwError "char_poly: the Mathlib matrix dimension must reduce to a concrete natural number{indentExpr nCols}"
  unless n == m do
    throwError "char_poly: expected equal Mathlib row and column dimensions, but got Fin {n} and Fin {m}"
  return some n

private meta def input? (e : Expr) : MetaM (Option MathlibInput) := do
  let e ← instantiateMVars e
  let ty ← inferType e
  let some n ← matrixDim? ty | return none
  Hex.CharPolyTactic.checkClosed "matrix" e
  let some literal ← HexMatrixMathlib.Literal.literal? e |
    throwError "char_poly declined: no supported closed matrix literal was found within the unfolding budget"
  let values ← literal.entries.mapIdxM fun i row => row.mapIdxM fun j entry => do
    try
      let q ← HexMatrixMathlib.Literal.evalEntry entry
      unless q.den == 1 do
        throwError "expected an integer"
      return q.num
    catch ex =>
      throwError "char_poly declined: could not evaluate integer entry ({i}, {j})\n{ex.toMessageData}"
  let value : Hex.Matrix Int n n := Hex.Matrix.ofFn (fun i j => (values[i.val]!)[j.val]!)
  return some ⟨n, e, value, literal⟩

private meta def matrixType (n : Expr) : MetaM Expr := do
  let fin := mkApp (mkConst ``Fin) n
  let row ← mkArrow fin (mkConst ``Int)
  mkArrow fin row

private meta def elabArgument? (t : Syntax) : Term.TermElabM (Option MathlibInput) := do
  let e ←
    if t.getKind == ``Matrix.matrixNotation ||
        t.getKind == ``Matrix.matrixNotationRx0 ||
        t.getKind == ``Matrix.matrixNotation0xC then
      let n ← mkFreshExprMVar (mkConst ``Nat)
      Term.elabTerm t (some (← matrixType n))
    else
      Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  input? e

/-- Materialize the matrix only for compiled certificate production. -/
private meta def coreInput (input : MathlibInput) : MetaM Hex.CharPolyTactic.CoreInput := do
  let value := input.value
  return ⟨input.n, ← Hex.CharPolyTactic.reifyIntMatrix value, value⟩

private meta def identify (input : MathlibInput) (rows : Expr) : MetaM Expr := do
  let proof ← HexMatrixMathlib.Literal.identification input.literal input.expr rows
  let target ← mkEq input.expr (← mkAppM ``HexMatrixMathlib.ofLists
    #[mkNatLit input.n, mkNatLit input.n, rows])
  HexMatrixMathlib.Literal.addClosedProof target proof

private meta def resultForMathlib (input : MathlibInput) : MetaM Expr := do
  let core ← coreInput input
  let (_, p) ← Hex.CharPolyTactic.computedPoly core
  let c ← Hex.CharPolyTactic.certificateExpr core
  let ha ← identify input c.rows
  let hp ← Hex.CharPolyTactic.beqCoeffsProof
    (← Hex.CharPolyTactic.polyOfDescending c.literal) p
  mkAppM ``CharPolyResult.ofCheck
    #[input.expr, c.rows, c.witness, c.literal, p, ha, c.proof, hp]

private meta unsafe def evalIntUnsafe (e : Expr) : MetaM (Except String Int) := do
  try
    return .ok (← evalExpr Int (mkConst ``Int) e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalIntUnsafe]
private meta opaque evalIntCore (e : Expr) : MetaM (Except String Int)

private meta def evalInt (e : Expr) : MetaM Int := do
  Hex.CharPolyTactic.checkClosed "integer coefficient" e
  match ← evalIntCore e with
  | .ok z => return z
  | .error msg =>
      throwError "char_poly declined: failed to evaluate the integer coefficient{indentExpr e}\n{msg}"

private meta def getNatLit (e : Expr) : MetaM Nat := do
  match ← getNatValue? e with
  | some n => return n
  | none =>
      match (← whnfR e).getAppFnArgs with
      | (``OfNat.ofNat, #[_, n, _]) =>
          match ← getNatValue? n with
          | some k => return k
          | none => throwError "char_poly: polynomial exponents must be natural-number literals{indentExpr e}"
      | _ =>
          throwError "char_poly: polynomial exponents must be natural-number literals{indentExpr e}"

private meta def densePolyType : MetaM Expr := do
  let int := mkConst ``Int
  let zero ← synthInstance (mkApp (mkConst ``Zero [Level.zero]) int)
  let dec := mkConst ``Int.instDecidableEq
  return mkApp3 (mkConst ``Hex.DensePoly [Level.zero]) int zero dec

private meta def toPolynomialFn : MetaM Expr := do
  let int := mkConst ``Int
  let semiring ← synthInstance (mkApp (mkConst ``Semiring [Level.zero]) int)
  let dec := mkConst ``Int.instDecidableEq
  return mkApp3 (mkConst ``HexPolyMathlib.toPolynomial [Level.zero]) int semiring dec

private meta structure ParsedPolynomial where
  value : Hex.DensePoly Int
  literal : Expr
  proof : Expr

private meta def combineBinary (original : Expr) (value : Hex.DensePoly Int)
    (left right : ParsedPolynomial) (transport operation : Name) :
    MetaM ParsedPolynomial := do
  let literal ← Hex.CharPolyTactic.reifyZPoly value
  let combined ← mkAppM operation #[left.literal, right.literal]
  let hcheck ← Hex.CharPolyTactic.beqCoeffsProof literal combined
  let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
  let t0 ← mkCongrArg (← toPolynomialFn) hroot
  let t1 ← mkAppM transport #[left.literal, right.literal]
  let polyTy ← inferType original
  let operationFn ← mkAppOptM operation
    #[some polyTy, some polyTy, some polyTy, none]
  let t2 ← mkCongr (← mkCongrArg operationFn left.proof) right.proof
  return ⟨value, literal, ← mkEqTrans t0 (← mkEqTrans t1 t2)⟩

private meta def constLeaf (z : Int) (coefficient : Expr)
    (tail? : Option Expr) : MetaM ParsedPolynomial := do
  let value : Hex.DensePoly Int := Hex.DensePoly.C z
  let literal ← Hex.CharPolyTactic.reifyZPoly value
  let zExpr := toExpr z
  let constant ← mkAppM ``Hex.DensePoly.C #[zExpr]
  let hcheck ← Hex.CharPolyTactic.beqCoeffsProof literal constant
  let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
  let t0 ← mkCongrArg (← toPolynomialFn) hroot
  let t1 ← mkAppM ``HexPolyMathlib.toPolynomial_C #[zExpr]
  let coefficientEq ← mkEq zExpr coefficient
  let hCoefficient ← Hex.CharPolyTactic.kernelDecideProof coefficientEq
  let some (_, _, constantRhs) := (← inferType t1).eq? |
    throwError "char_poly: internal error while constructing a constant-polynomial proof"
  let t2 ← mkCongrArg constantRhs.appFn! hCoefficient
  let mut proof ← mkEqTrans t0 (← mkEqTrans t1 t2)
  if let some tail := tail? then
    proof ← mkEqTrans proof tail
  return ⟨value, literal, proof⟩

/-- Parse an ordinary `Polynomial Int` expression while constructing a proof
that its flat executable literal transports back to the original expression.
The `seen` list prevents cycles while unfolding named transparent definitions. -/
private meta partial def parsePolynomial (e : Expr) (seen : List Name := []) :
    MetaM ParsedPolynomial := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let left ← parsePolynomial a seen
      let right ← parsePolynomial b seen
      combineBinary e (left.value + right.value) left right
        ``HexPolyMathlib.toPolynomial_add ``HAdd.hAdd
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let left ← parsePolynomial a seen
      let right ← parsePolynomial b seen
      combineBinary e (left.value - right.value) left right
        ``HexPolyMathlib.toPolynomial_sub ``HSub.hSub
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      let left ← parsePolynomial a seen
      let right ← parsePolynomial b seen
      combineBinary e (left.value * right.value) left right
        ``HexPolyMathlib.toPolynomial_mul ``HMul.hMul
  | (``Neg.neg, #[_, _, a]) => do
      let child ← parsePolynomial a seen
      let value := -child.value
      let literal ← Hex.CharPolyTactic.reifyZPoly value
      let negated ← mkAppM ``Neg.neg #[child.literal]
      let hcheck ← Hex.CharPolyTactic.beqCoeffsProof literal negated
      let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
      let t0 ← mkCongrArg (← toPolynomialFn) hroot
      let t1 ← mkAppM ``HexPolyMathlib.toPolynomial_neg #[child.literal]
      let polyTy ← inferType e
      let negFn ← mkAppOptM ``Neg.neg #[some polyTy, none]
      let t2 ← mkCongrArg negFn child.proof
      return ⟨value, literal, ← mkEqTrans t0 (← mkEqTrans t1 t2)⟩
  | (``HPow.hPow, #[_, _, _, _, a, exponent]) => do
      let base ← parsePolynomial a seen
      let n ← getNatLit exponent
      let denseTy ← densePolyType
      let oneDense ← mkAppOptM ``One.one #[some denseTy, none]
      let mut value : Hex.DensePoly Int := 1
      let mut literal ← Hex.CharPolyTactic.reifyZPoly value
      let hOneCheck ← Hex.CharPolyTactic.beqCoeffsProof literal oneDense
      let hOne ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hOneCheck]
      let t0 ← mkCongrArg (← toPolynomialFn) hOne
      let toPoly ← toPolynomialFn
      let toPolyArgs := toPoly.getAppArgs
      let t1 := mkApp3
        (mkConst ``HexPolyMathlib.toPolynomial_one [Level.zero])
        toPolyArgs[0]! toPolyArgs[1]! toPolyArgs[2]!
      let mut proof ← mkEqTrans t0
        (← mkEqTrans t1 (← mkEqSymm (← mkAppM ``pow_zero #[a])))
      let polyTy ← inferType e
      let mulFn ← mkAppOptM ``HMul.hMul
        #[some polyTy, some polyTy, some polyTy, none]
      for k in [0:n] do
        let nextValue := value * base.value
        let nextLiteral ← Hex.CharPolyTactic.reifyZPoly nextValue
        let product ← mkAppM ``HMul.hMul #[literal, base.literal]
        let hcheck ← Hex.CharPolyTactic.beqCoeffsProof nextLiteral product
        let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
        let s0 ← mkCongrArg (← toPolynomialFn) hroot
        let s1 ← mkAppM ``HexPolyMathlib.toPolynomial_mul #[literal, base.literal]
        let s2 ← mkCongr (← mkCongrArg mulFn proof) base.proof
        let s3 ← mkEqSymm (← mkAppM ``pow_succ #[a, mkNatLit k])
        value := nextValue
        literal := nextLiteral
        proof ← mkEqTrans s0 (← mkEqTrans s1 (← mkEqTrans s2 s3))
      return ⟨value, literal, proof⟩
  | (``Polynomial.X, _) => do
      let value : Hex.DensePoly Int := Hex.DensePoly.ofCoeffs #[0, 1]
      let literal ← Hex.CharPolyTactic.reifyZPoly value
      let canonical ← Hex.CharPolyTactic.reifyZPoly
        (Hex.DensePoly.ofCoeffs #[(0 : Int), 1])
      let hcheck ← Hex.CharPolyTactic.beqCoeffsProof literal canonical
      let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
      let t0 ← mkCongrArg (← toPolynomialFn) hroot
      return ⟨value, literal, ← mkEqTrans t0 (mkConst ``toPolynomial_x)⟩
  | (``Polynomial.C, #[_, _, coefficient]) =>
      constLeaf (← evalInt coefficient) coefficient none
  | (``DFunLike.coe, args) =>
      if args.size == 6 && args[4]!.getAppFn.isConstOf ``Polynomial.C then
        let coefficient := args[5]!
        constLeaf (← evalInt coefficient) coefficient none
      else
        throwError "char_poly declined: unsupported Mathlib polynomial syntax{indentExpr e}"
  | (``OfNat.ofNat, #[_, numeral, _]) => do
      let n ← getNatLit numeral
      let intTy := mkConst ``Int
      let coefficient ← mkAppOptM ``OfNat.ofNat
        #[some intTy, some (mkRawNatLit n), none]
      let tail ←
        if n == 0 then
          mkAppOptM ``Polynomial.C_0 #[some intTy, none]
        else if n == 1 then
          mkAppOptM ``Polynomial.C_1 #[some intTy, none]
        else do
          let cHom ← mkAppOptM ``Polynomial.C #[some intTy, none]
          let polyTy ← inferType e
          mkAppOptM ``map_ofNat
            #[some intTy, some polyTy, some (← inferType cHom), none, none,
              none, none, some cHom, some (mkRawNatLit n), none]
      constLeaf (Int.ofNat n) coefficient (some tail)
  | _ =>
      let head := e.getAppFn
      let name? := if head.isConst then some head.constName! else none
      if let some name := name? then
        if seen.contains name then
          throwError "char_poly: recursive or cyclic polynomial definition encountered at `{name}`"
      match ← unfoldDefinition? e with
      | some unfolded =>
          if unfolded == e then
            throwError "char_poly declined: unsupported Mathlib polynomial syntax{indentExpr e}"
          else
            parsePolynomial unfolded <|
              match name? with
              | some name => name :: seen
              | none => seen
      | none =>
          throwError "char_poly declined: unsupported Mathlib polynomial syntax{indentExpr e}\nSupported forms are X, C, numerals, +, -, *, negation, and literal natural powers"

private meta def mathlibGoal? (target : Expr) :
    MetaM (Option (Expr × Expr × Bool)) := do
  let some (_, lhs, rhs) := target.eq? | return none
  if lhs.getAppFn.isConstOf ``Matrix.charpoly then
    return some (lhs.getAppArgs.back!, rhs, false)
  if rhs.getAppFn.isConstOf ``Matrix.charpoly then
    return some (rhs.getAppArgs.back!, lhs, true)
  return none

private meta def proveMathlibEquality (input : MathlibInput) (rhs : Expr)
    (reverse : Bool) : MetaM Expr := do
  Hex.CharPolyTactic.checkClosed "polynomial" rhs
  let core ← coreInput input
  let (computed, computedLiteral) ← Hex.CharPolyTactic.computedPoly core
  let parsed ← parsePolynomial rhs
  unless Hex.DensePoly.beqCoeffs computed parsed.value do
    throwError "char_poly: the supplied polynomial has coefficients {parsed.value.toArray.toList}, but the computed characteristic polynomial has coefficients {computed.toArray.toList}"
  let c ← Hex.CharPolyTactic.certificateExpr core
  let ha ← identify input c.rows
  let hp ← Hex.CharPolyTactic.beqCoeffsProof
    (← Hex.CharPolyTactic.polyOfDescending c.literal) computedLiteral
  let certified ← mkAppM ``CharPolyResult.ofCheck
    #[input.expr, c.rows, c.witness, c.literal, computedLiteral, ha, c.proof, hp]
  let canonical ← mkAppM ``CharPolyResult.charPoly_eq #[certified]
  let hcheck ← Hex.CharPolyTactic.beqCoeffsProof computedLiteral parsed.literal
  let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
  let equivApply ← mkAppM ``HexPolyMathlib.equiv_apply #[computedLiteral]
  let mapped ← mkCongrArg (← toPolynomialFn) hroot
  let proof ← mkEqTrans canonical
    (← mkEqTrans equivApply (← mkEqTrans mapped parsed.proof))
  if reverse then mkEqSymm proof else return proof

@[term_elab Hex.CharPolyTactic.charPolyTerm]
public meta def elabCharPolyMathlib : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(char_poly $t) =>
        let some input ← elabArgument? t | Elab.throwUnsupportedSyntax
        let result ← resultForMathlib input
        Term.ensureHasType expectedType? result
    | _ => Elab.throwUnsupportedSyntax

@[term_elab Hex.CharPolyTactic.charPolyProofTerm]
public meta def elabCharPolyProofMathlib : Term.TermElab :=
  fun _stx expectedType? => do
    let some expectedType := expectedType? |
      throwError "char_poly: bare term syntax needs an expected characteristic-polynomial equality"
    Term.synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars expectedType
    let some (matrix, rhs, reverse) ← mathlibGoal? target |
      Elab.throwUnsupportedSyntax
    let some input ← input? matrix |
      throwError "char_poly: Mathlib support requires `Matrix (Fin n) (Fin n) Int`"
    let proof ← proveMathlibEquality input rhs reverse
    Term.ensureHasType expectedType? proof

end CharPolyTactic

end HexCharPolyMathlib
