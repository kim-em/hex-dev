/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexCharPoly.CharPolyElab
public meta import Mathlib.Data.Fin.VecNotation
public import HexCharPolyMathlib.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Lean

public section

/-!
The Mathlib `Matrix (Fin n) (Fin n) Int` arm of `char_poly`.

The matrix is materialized through `HexMatrixMathlib.matrixEquiv.symm` and
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

/-- The executable characteristic polynomial with the exact commutative-ring
instance used by the Mathlib correspondence theorem. -/
@[expose]
def checkedCharPoly {n : Nat} (A : Hex.Matrix Int n n) : Hex.DensePoly Int :=
  @Hex.Matrix.charPoly Int (CommRing.toGrindCommRing Int)
    Int.instDecidableEq n A

/-- Read one entry of a materialized Hex matrix. -/
@[expose]
def matrixEntry {n : Nat} (B : Hex.Matrix Int n n) (i j : Nat)
    (hi : i < n) (hj : j < n) : Int :=
  B[((⟨i, hi⟩ : Fin n), (⟨j, hj⟩ : Fin n))]

/-- A certified prefix of one row in the Mathlib-to-Hex matrix bridge. -/
inductive RowCertificate {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
    (B : Hex.Matrix Int n n) (i : Nat) (hi : i < n) : Nat → Prop where
  | zero : RowCertificate A B i hi 0
  | step {j : Nat} (hj : j < n)
      (certificate : RowCertificate A B i hi j)
      (entry : matrixEntry B i j hi hj =
        A ⟨i, hi⟩ ⟨j, hj⟩) :
      RowCertificate A B i hi (j + 1)

/-- Recover one entry from a certified row prefix. -/
theorem RowCertificate.entry {n count : Nat}
    {A : Matrix (Fin n) (Fin n) Int} {B : Hex.Matrix Int n n}
    {i : Nat} {hi : i < n} (certificate : RowCertificate A B i hi count)
    (j : Fin n) (hj : j.val < count) :
    matrixEntry B i j.val hi j.isLt = A ⟨i, hi⟩ j := by
  induction certificate generalizing j with
  | zero => omega
  | @step k hk certificate head ih =>
      by_cases h : j.val = k
      · have : j = ⟨k, hk⟩ := Fin.ext h
        subst j
        exact head
      · exact ih j (by omega)

/-- A certified prefix of the rows in the Mathlib-to-Hex matrix bridge. -/
inductive MatrixCertificate {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
    (B : Hex.Matrix Int n n) : Nat → Prop where
  | zero : MatrixCertificate A B 0
  | step {i : Nat} (hi : i < n)
      (certificate : MatrixCertificate A B i)
      (row_certificate : RowCertificate A B i hi n) :
      MatrixCertificate A B (i + 1)

/-- Recover a complete certified row. -/
theorem MatrixCertificate.row {n count : Nat}
    {A : Matrix (Fin n) (Fin n) Int} {B : Hex.Matrix Int n n}
    (certificate : MatrixCertificate A B count)
    (i : Fin n) (hi : i.val < count) : RowCertificate A B i.val i.isLt n := by
  induction certificate generalizing i with
  | zero => omega
  | @step k hk certificate row_certificate ih =>
      by_cases h : i.val = k
      · have : i = ⟨k, hk⟩ := Fin.ext h
        subst i
        exact row_certificate
      · exact ih i (by omega)

/-- A complete bridge certificate proves that `B` materializes `A`. -/
theorem MatrixCertificate.eq_matrixEquiv {n : Nat}
    {A : Matrix (Fin n) (Fin n) Int} {B : Hex.Matrix Int n n}
    (certificate : MatrixCertificate A B n) : matrixEquiv B = A := by
  funext i j
  change matrixEntry B i.val j.val i.isLt j.isLt = A i j
  exact (certificate.row i i.isLt).entry j j.isLt

/-- Kernel-checkable Mathlib endpoint combining the materialization,
Berkowitz, and final coefficient certificates. -/
@[expose]
noncomputable def CharPolyResult.ofCheck {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
    (B : Hex.Matrix Int n n) (descending : _root_.Vector Int (n + 1))
    (p : Hex.DensePoly Int)
    (matrix_certificate : MatrixCertificate A B n)
    (certificate : @Hex.Matrix.BerkowitzCertificate n
      (CommRing.toGrindCommRing Int) B n descending)
    (h : Hex.DensePoly.beqCoeffs
      (Hex.DensePoly.ofCoeffs descending.reverse.toArray) p = true) :
    CharPolyResult A where
  poly := equiv p
  charPoly_eq := by
    have hp : checkedCharPoly B = p := by
      unfold checkedCharPoly Hex.Matrix.charPoly Hex.Matrix.berkowitz
      rw [certificate.eq_berkowitzAux (Nat.le_refl n)]
      exact Hex.DensePoly.eq_of_beqCoeffs h
    calc
      A.charpoly = (matrixEquiv B).charpoly :=
        congrArg Matrix.charpoly matrix_certificate.eq_matrixEquiv.symm
      _ = equiv (checkedCharPoly B) := (equiv_charPoly B).symm
      _ = equiv p := congrArg equiv hp

/-- Equality projection of `CharPolyResult.ofCheck`, used by goal-closing
`char_poly`. -/
theorem charPoly_eq_of_check {n : Nat} (A : Matrix (Fin n) (Fin n) Int)
    (B : Hex.Matrix Int n n) (descending : _root_.Vector Int (n + 1))
    (p : Hex.DensePoly Int) (matrix_certificate : MatrixCertificate A B n)
    (certificate : @Hex.Matrix.BerkowitzCertificate n
      (CommRing.toGrindCommRing Int) B n descending)
    (h : Hex.DensePoly.beqCoeffs
      (Hex.DensePoly.ofCoeffs descending.reverse.toArray) p = true) :
    A.charpoly = equiv p :=
  (CharPolyResult.ofCheck A B descending p matrix_certificate certificate h).charPoly_eq

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

private meta unsafe def evalMatrixUnsafe (n : Nat) (ty e : Expr) :
    MetaM (Except String (Matrix (Fin n) (Fin n) Int)) := do
  try
    return .ok (← evalExpr (Matrix (Fin n) (Fin n) Int) ty e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalMatrixUnsafe]
private meta opaque evalMatrixCore (n : Nat) (ty e : Expr) :
    MetaM (Except String (Matrix (Fin n) (Fin n) Int))

/-- A closed, evaluated Mathlib matrix with its dependent dimension. -/
private meta structure MathlibInput where
  n : Nat
  expr : Expr
  value : Matrix (Fin n) (Fin n) Int

/-- Match `Fin n → Fin n → Int`, the reducible representation of the
supported Mathlib matrix type. -/
private meta def matrixDim? (ty : Expr) : MetaM (Option Nat) := do
  let_expr _root_.Matrix rows cols coeff := ty | return none
  let_expr Fin nRows := (← whnfR rows) | return none
  let_expr Fin nCols := (← whnfR cols) | return none
  unless (← whnfR coeff).isConstOf ``Int do
    throwError "char_poly: unsupported Mathlib matrix coefficient type{indentExpr coeff}\nOnly Int matrices are currently supported"
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
  match ← evalMatrixCore n ty e with
  | .error msg =>
      throwError "char_poly: failed to evaluate the Mathlib matrix with compiled code{indentExpr e}\n{msg}"
  | .ok value => return some ⟨n, e, value⟩

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

/-- Build `matrixEquiv.symm A` as a raw expression. -/
private meta def toHexExpr (input : MathlibInput) : MetaM Expr := do
  let equiv := mkApp3 (mkConst ``HexMatrixMathlib.matrixEquiv [Level.zero])
    (mkConst ``Int) (mkNatLit input.n) (mkNatLit input.n)
  let symm ← mkAppM ``Equiv.symm #[equiv]
  mkAppM ``Equiv.toFun #[symm, input.expr]

/-- Convert the evaluated function matrix to the executable representation
and reuse the core computation/transparency checks. -/
private meta def coreInput (input : MathlibInput) : MetaM Hex.CharPolyTactic.CoreInput := do
  let expr ← toHexExpr input
  let value := Hex.Matrix.ofFn input.value
  return ⟨input.n, expr, value⟩

private meta def certificateRing : MetaM Expr :=
  pure <| mkApp2 (mkConst ``CommRing.toGrindCommRing [Level.zero])
    (mkConst ``Int) (mkConst ``Int.instCommRing)

private meta def buildMatrixCertificate (input : MathlibInput)
    (matrixLiteral : Expr) : MetaM Expr := do
  let mut certificate := mkAppN (mkConst ``MatrixCertificate.zero)
    #[mkNatLit input.n, input.expr, matrixLiteral]
  for i in [0:input.n] do
    if _hi : i < input.n then
      let hiProof ← Hex.CharPolyTactic.kernelDecideProof
        (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit input.n])
      let finI := mkApp3 (mkConst ``Fin.mk)
        (mkNatLit input.n) (mkNatLit i) hiProof
      let mut rowCertificate := mkAppN (mkConst ``RowCertificate.zero)
        #[mkNatLit input.n, input.expr, matrixLiteral, mkNatLit i, hiProof]
      for j in [0:input.n] do
        if _hj : j < input.n then
          let hjProof ← Hex.CharPolyTactic.kernelDecideProof
            (← mkAppM ``LT.lt #[mkNatLit j, mkNatLit input.n])
          let finJ := mkApp3 (mkConst ``Fin.mk)
            (mkNatLit input.n) (mkNatLit j) hjProof
          let source := mkAppN (mkConst ``matrixEntry)
            #[mkNatLit input.n, matrixLiteral, mkNatLit i, mkNatLit j,
              hiProof, hjProof]
          let target := mkApp (mkApp input.expr finI) finJ
          let entryProof ← Hex.CharPolyTactic.kernelDecideProof
            (← mkEq source target)
          rowCertificate := mkAppN (mkConst ``RowCertificate.step)
            #[mkNatLit input.n, input.expr, matrixLiteral, mkNatLit i,
              hiProof, mkNatLit j, hjProof, rowCertificate, entryProof]
        else
          throwError "char_poly: internal Mathlib column index escaped its dimension"
      certificate := mkAppN (mkConst ``MatrixCertificate.step)
        #[mkNatLit input.n, input.expr, matrixLiteral, mkNatLit i, hiProof,
          certificate, rowCertificate]
    else
      throwError "char_poly: internal Mathlib row index escaped its dimension"
  return certificate

private meta def resultForMathlib (input : MathlibInput) : MetaM Expr := do
  let core ← coreInput input
  let (_, p) ← Hex.CharPolyTactic.computedPoly core
  let matrixLiteral ← Hex.CharPolyTactic.reifyIntMatrix core.value
  let certificateInput := { core with expr := matrixLiteral }
  let certificate ← Hex.CharPolyTactic.certificateExpr certificateInput
    (← certificateRing)
  let matrixCertificate ← buildMatrixCertificate input matrixLiteral
  let source ← Hex.CharPolyTactic.polyOfDescending certificate.literal
  let check ← Hex.CharPolyTactic.beqCoeffsProof source p
  try
    mkAppM ``CharPolyResult.ofCheck
      #[input.expr, matrixLiteral, certificate.literal, p, matrixCertificate,
        certificate.proof, check]
  catch _ =>
    throwError "char_poly: compiled evaluation succeeded, but the kernel could not replay the Mathlib bridge certificate"

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
      throwError "char_poly: failed to evaluate the integer coefficient{indentExpr e}\n{msg}"

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
        throwError "char_poly: unsupported Mathlib polynomial syntax{indentExpr e}"
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
            throwError "char_poly: unsupported Mathlib polynomial syntax{indentExpr e}"
          else
            parsePolynomial unfolded <|
              match name? with
              | some name => name :: seen
              | none => seen
      | none =>
          throwError "char_poly: unsupported Mathlib polynomial syntax{indentExpr e}\nSupported forms are X, C, numerals, +, -, *, negation, and literal natural powers"

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
  let matrixLiteral ← Hex.CharPolyTactic.reifyIntMatrix core.value
  let certificateInput := { core with expr := matrixLiteral }
  let certificate ← Hex.CharPolyTactic.certificateExpr certificateInput
    (← certificateRing)
  let matrixCertificate ← buildMatrixCertificate input matrixLiteral
  let source ← Hex.CharPolyTactic.polyOfDescending certificate.literal
  let matrixCheck ← Hex.CharPolyTactic.beqCoeffsProof source computedLiteral
  let canonical ← mkAppM ``charPoly_eq_of_check
    #[input.expr, matrixLiteral, certificate.literal, computedLiteral,
      matrixCertificate, certificate.proof, matrixCheck]
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
