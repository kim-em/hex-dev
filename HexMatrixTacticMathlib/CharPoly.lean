/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTacticMathlib.Literal
public import HexMatrixTacticMathlib.Literal
public import HexCharPolyMathlib

public section

/-!
The `char_poly` frontend on closed `Matrix (Fin n) (Fin n) Int` inputs.

The matrix is reconstructed through the shared literal certificate, the
Berkowitz certificate of `HexCharPoly` is replayed on the Hex literal, and the
result is transported through `equiv_charPoly`; Mathlib's noncomputable
`Matrix.charpoly` is never evaluated by the elaborator or by a Boolean checker.
Direct equality goals accept ordinary `Polynomial Int` expressions built from
`X`, `C`, numerals, `+`, `-`, `*`, negation and literal natural powers.
-/

namespace HexMatrixTacticMathlib

open Hex HexMatrixMathlib HexPolyMathlib HexCharPolyMathlib
open Matrix Polynomial

/-- The executable characteristic polynomial with the exact commutative-ring
instance used by the Mathlib correspondence theorem. -/
@[expose]
def checkedCharPoly {n : Nat} (A : Hex.Matrix Int n n) : Hex.DensePoly Int :=
  @Hex.Matrix.charPoly Int (CommRing.toGrindCommRing Int)
    Int.instDecidableEq n A

/-- Kernel-checkable Mathlib endpoint combining the reconstruction, the
Berkowitz certificate and the final coefficient check. -/
theorem charPoly_eq_of_check {n : Nat} (B : Hex.Matrix Int n n)
    (A : Matrix (Fin n) (Fin n) Int) (hB : matrixEquiv B = A)
    (descending : _root_.Vector Int (n + 1)) (p : Hex.DensePoly Int)
    (certificate : @Hex.Matrix.BerkowitzCertificate n
      (CommRing.toGrindCommRing Int) B n descending)
    (h : Hex.DensePoly.beqCoeffs
      (Hex.DensePoly.ofCoeffs descending.reverse.toArray) p = true) :
    A.charpoly = equiv p := by
  have hp : checkedCharPoly B = p := by
    unfold checkedCharPoly Hex.Matrix.charPoly Hex.Matrix.berkowitz
    rw [certificate.eq_berkowitzAux (Nat.le_refl n)]
    exact Hex.DensePoly.eq_of_beqCoeffs h
  calc
    A.charpoly = (matrixEquiv B).charpoly := by rw [hB]
    _ = equiv (checkedCharPoly B) := (equiv_charPoly B).symm
    _ = equiv p := congrArg equiv hp

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

namespace CharPoly

open Lean Meta Elab Hex.MatrixTactic Literal

/-- Evaluate a Mathlib input as the integer core input of the Berkowitz
certificate builder. -/
private meta def coreInput (input : Input) : MetaM Hex.MatrixTactic.CharPoly.CoreInput := do
  unless input.carrier.isConstOf ``Int do
    throwError "char_poly: declined: only integer matrices are supported, but the carrier is{indentExpr input.carrier}"
  unless input.n = input.m do
    throwError "char_poly: expected a square matrix, but got dimensions {input.n} × {input.m}"
  let some core ← Hex.MatrixTactic.CharPoly.coreInput?
      (← toHexExpr input.carrier input.n input.n input.expr) |
    throwError "char_poly: internal error: the reconstructed Hex matrix was not recognized"
  return core

private meta def certificateRing : MetaM Expr :=
  pure <| mkApp2 (mkConst ``CommRing.toGrindCommRing [Level.zero])
    (mkConst ``Int) (mkConst ``Int.instCommRing)

/-- The computed polynomial literal and the proof `A.charpoly = equiv p`. -/
private meta def certifiedPoly (input : Input) (core : Hex.MatrixTactic.CharPoly.CoreInput) :
    MetaM (Expr × Expr) := do
  let (_, p) ← Hex.MatrixTactic.CharPoly.computedPoly core
  let certificateInput := { core with expr := input.hex.literal }
  let certificate ← Hex.MatrixTactic.CharPoly.certificateExpr certificateInput
    (← certificateRing)
  let hB ← reconstructionProof "char_poly" input
  let source ← Hex.MatrixTactic.CharPoly.polyOfDescending certificate.literal
  let check ← beqCoeffsProof "char_poly" source p
  let proof ← try
      mkAppM ``charPoly_eq_of_check
        #[input.hex.literal, input.expr, hB, certificate.literal, p, certificate.proof, check]
    catch _ =>
      throwError "char_poly: compiled evaluation succeeded, but the kernel could not replay the Mathlib bridge certificate"
  return (p, proof)

/-- The `char_poly A` record for a Mathlib input: `Hex.MatrixTactic.Certified Matrix.charpoly A`. -/
private meta def resultForMathlib (input : Input) : MetaM Expr := do
  let (_, proof) ← certifiedPoly input (← coreInput input)
  let some (_, lhs, rhs) := (← inferType proof).eq? |
    throwError "char_poly: internal error: the adapter did not return an equality"
  mkAppOptM ``Hex.MatrixTactic.Certified.mk #[none, none, some lhs.appFn!, some input.expr, some rhs, some proof]

private meta unsafe def evalIntUnsafe (e : Expr) : MetaM (Except String Int) := do
  try
    return .ok (← evalExpr Int (mkConst ``Int) e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalIntUnsafe]
private meta opaque evalIntCore (e : Expr) : MetaM (Except String Int)

private meta def evalInt (e : Expr) : MetaM Int := do
  checkClosed "char_poly" "integer coefficient" e
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
  let literal ← reifyZPoly value
  let combined ← mkAppM operation #[left.literal, right.literal]
  let hcheck ← beqCoeffsProof "char_poly" literal combined
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
  let literal ← reifyZPoly value
  let zExpr := toExpr z
  let constant ← mkAppM ``Hex.DensePoly.C #[zExpr]
  let hcheck ← beqCoeffsProof "char_poly" literal constant
  let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
  let t0 ← mkCongrArg (← toPolynomialFn) hroot
  let t1 ← mkAppM ``HexPolyMathlib.toPolynomial_C #[zExpr]
  let coefficientEq ← mkEq zExpr coefficient
  let hCoefficient ← kernelDecideProof "char_poly" coefficientEq
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
      let literal ← reifyZPoly value
      let negated ← mkAppM ``Neg.neg #[child.literal]
      let hcheck ← beqCoeffsProof "char_poly" literal negated
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
      let mut literal ← reifyZPoly value
      let hOneCheck ← beqCoeffsProof "char_poly" literal oneDense
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
        let nextLiteral ← reifyZPoly nextValue
        let product ← mkAppM ``HMul.hMul #[literal, base.literal]
        let hcheck ← beqCoeffsProof "char_poly" nextLiteral product
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
      let literal ← reifyZPoly value
      let canonical ← reifyZPoly
        (Hex.DensePoly.ofCoeffs #[(0 : Int), 1])
      let hcheck ← beqCoeffsProof "char_poly" literal canonical
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

private meta def proveMathlibEquality (input : Input) (rhs : Expr)
    (reverse : Bool) : MetaM Expr := do
  checkClosed "char_poly" "polynomial" rhs
  let core ← coreInput input
  let (computed, computedLiteral) ← Hex.MatrixTactic.CharPoly.computedPoly core
  let parsed ← parsePolynomial rhs
  unless Hex.DensePoly.beqCoeffs computed parsed.value do
    throwError "char_poly: the supplied polynomial has coefficients {parsed.value.toArray.toList}, but the computed characteristic polynomial has coefficients {computed.toArray.toList}"
  let (_, canonical) ← certifiedPoly input core
  let hcheck ← beqCoeffsProof "char_poly" computedLiteral parsed.literal
  let hroot ← mkAppM ``Hex.DensePoly.eq_of_beqCoeffs #[hcheck]
  let equivApply ← mkAppM ``HexPolyMathlib.equiv_apply #[computedLiteral]
  let mapped ← mkCongrArg (← toPolynomialFn) hroot
  let proof ← mkEqTrans canonical
    (← mkEqTrans equivApply (← mkEqTrans mapped parsed.proof))
  if reverse then mkEqSymm proof else return proof

@[term_elab Hex.MatrixTactic.charPolyTerm]
public meta def elabCharPolyMathlib : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(char_poly $t) =>
        let input ← (← input? "char_poly" (← elabArgument t)).get "char_poly"
        Term.ensureHasType expectedType? (← resultForMathlib input)
    | _ => throwUnsupportedSyntax

@[tactic Hex.MatrixTactic.charPolyTac]
public meta def evalCharPolyMathlibTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let target ← Tactic.getMainTarget
  let some (matrix, rhs, reverse) ← mathlibGoal? target | throwUnsupportedSyntax
  let input ← (← input? "char_poly" matrix).get "char_poly"
  let proof ← proveMathlibEquality input rhs reverse
  Tactic.closeMainGoal `char_poly proof

end CharPoly

end HexMatrixTacticMathlib
