/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexCharPoly.Kernel
public import HexCharPoly.Kernel
public import Lean

public section

/-!
The `char_poly` result elaborator and tactics for closed integer matrices.

Compiled evaluation is used only to discover coefficients and intermediate
values. Every emitted result carries a packed integer-list certificate,
checked once by the kernel.
-/

namespace Hex.Matrix

/-- A characteristic polynomial computed and certified by `char_poly`. -/
structure CharPolyResult {n : Nat} (A : Matrix Int n n) where
  /-- The computed polynomial in ascending coefficient order. -/
  poly : DensePoly Int
  /-- Its characteristic-polynomial identity. -/
  charPoly_eq : charPoly A = poly

/-- The certified result type for the core frontend. -/
abbrev CharPolyKernel.Certified {n : Nat} (A : Matrix Int n n) := CharPolyResult A

/-- Identify a closed core matrix with the row list, once at the literal boundary. -/
@[expose] def checkRows {n : Nat} (A : Matrix Int n n) (rs : List (List Int)) : Bool :=
  CharPolyKernel.eqList A.data.toList (CharPolyKernel.ofLists n rs).data.toList

theorem eq_of_checkRows {n : Nat} (A : Matrix Int n n) (rs : List (List Int))
    (h : checkRows A rs = true) : A = CharPolyKernel.ofLists n rs := by
  have he := Vector.toList_inj.mp ((CharPolyKernel.eqList_iff ..).mp h)
  exact congrArg Matrix.mk he

/-- The checked literal certificate yields a core characteristic-polynomial equality. -/
theorem charPoly_eq_of_check {n : Nat} (A : Matrix Int n n)
    (rs : List (List Int)) (w : CharPolyKernel.Witness) (descending : List Int) (p : DensePoly Int)
    (ha : A = CharPolyKernel.ofLists n rs)
    (hc : CharPolyKernel.checkCharPolyList n rs w descending = true)
    (hp : DensePoly.beqCoeffs (DensePoly.ofCoeffs descending.reverse.toArray) p = true) :
    charPoly A = p := by
  rw [ha, CharPolyKernel.charPoly_eq_of_checkList n rs w descending hc]
  exact DensePoly.eq_of_beqCoeffs hp

/-- The result record keeps its polynomial projection definitionally visible. -/
@[expose] def CharPolyResult.ofCheck {n : Nat} (A : Matrix Int n n)
    (rs : List (List Int)) (w : CharPolyKernel.Witness) (descending : List Int) (p : DensePoly Int)
    (ha : A = CharPolyKernel.ofLists n rs)
    (hc : CharPolyKernel.checkCharPolyList n rs w descending = true)
    (hp : DensePoly.beqCoeffs (DensePoly.ofCoeffs descending.reverse.toArray) p = true) :
    CharPolyResult A := ⟨p, charPoly_eq_of_check A rs w descending p ha hc hp⟩

end Hex.Matrix

namespace Hex.CharPolyTactic

open Lean Meta Elab

/-- Build a kernel `decide` proof of a proposition.  This is used instead of
raw reflexivity because some current-toolchain reductions available to the
kernel evaluator are not available to ordinary `rfl` unification across
module boundaries. -/
public meta def kernelDecideProof (prop : Expr) : MetaM Expr := do
  let d ← mkDecide prop
  let proof := mkApp3 (mkConst ``of_decide_eq_true) prop d.appArg!
    (← mkEqRefl (mkConst ``Bool.true))
  if prop.hasFVar || prop.hasMVar || proof.hasFVar || proof.hasMVar then
    throwError "char_poly failure: certificate proof is not closed"
  let levels := (collectLevelParams (collectLevelParams {} prop) proof).params.toList
  try
    let name ← withOptions (Lean.Elab.async.set · false) <|
      mkAuxLemma levels prop proof (cache := false)
    return mkConst name (levels.map Level.param)
  catch ex =>
    throwError "char_poly failure: the kernel rejected the certificate\n{ex.toMessageData}"

/-- Prove `DensePoly.beqCoeffs a b = true` by kernel evaluation. -/
public meta def beqCoeffsProof (a b : Expr) : MetaM Expr := do
  let check ← mkAppM ``DensePoly.beqCoeffs #[a, b]
  let prop ← mkEq check (mkConst ``Bool.true)
  kernelDecideProof prop

/-- Literal `Array` expression backed by a literal list. -/
public meta def arrayLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  let list := xs.foldr (fun x acc =>
    mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil
  mkApp2 (mkConst ``List.toArray [Level.zero]) ty list

/-- Literal list expression. -/
public meta def listLit (ty : Expr) (xs : List Expr) : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) ty
  xs.foldr (fun x acc =>
    mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc) nil

/-- Reify a fixed-length integer vector. -/
public meta def reifyIntVector {n : Nat} (v : _root_.Vector Int n) : MetaM Expr := do
  let data := arrayLit (mkConst ``Int) (v.toArray.toList.map toExpr)
  let size := mkNatLit n
  let sizeProof ← mkAppM ``Eq.refl #[size]
  mkAppM ``_root_.Vector.mk #[data, sizeProof]

/-- Reify an integer dense polynomial as `DensePoly.ofCoeffs #[...]`. -/
public meta def reifyZPoly (p : DensePoly Int) : MetaM Expr :=
  mkAppM ``DensePoly.ofCoeffs
    #[arrayLit (mkConst ``Int) (p.toArray.toList.map toExpr)]

/-- Reify the flat data of an integer matrix for kernel certificate replay. -/
public meta def reifyIntMatrix {n m : Nat} (A : Matrix Int n m) : MetaM Expr := do
  let vector ← reifyIntVector A.data
  return mkApp4 (mkConst ``Matrix.mk [Level.zero])
    (mkConst ``Int) (mkNatLit n) (mkNatLit m) vector

private meta unsafe def evalMatrixUnsafe (n : Nat) (ty e : Expr) :
    MetaM (Except String (Matrix Int n n)) := do
  try
    return .ok (← evalExpr (Matrix Int n n) ty e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalMatrixUnsafe]
private meta opaque evalMatrixCore (n : Nat) (ty e : Expr) :
    MetaM (Except String (Matrix Int n n))

private meta unsafe def evalPolyUnsafe (ty e : Expr) :
    MetaM (Except String (DensePoly Int)) := do
  try
    return .ok (← evalExpr (DensePoly Int) ty e)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalPolyUnsafe]
private meta opaque evalPolyCore (ty e : Expr) :
    MetaM (Except String (DensePoly Int))

/-- A closed, evaluated core matrix with its dependent dimension. -/
public meta structure CoreInput where
  n : Nat
  expr : Expr
  value : Matrix Int n n

/-- Reject free variables and unresolved metavariables before compiled
evaluation. -/
public meta def checkClosed (what : String) (e : Expr) : MetaM Unit := do
  if e.hasFVar || e.hasExprMVar then
    throwError "char_poly: the {what}{indentExpr e}\nmust be a closed term (no local hypotheses or metavariables)"

/-- Classify and evaluate an already elaborated `Hex.Matrix Int n n`.  A
non-Hex type returns `none`, allowing another elaborator for the same syntax
kind to try it. -/
public meta def coreInput? (e : Expr) : MetaM (Option CoreInput) := do
  let e ← instantiateMVars e
  let ty ← whnfR (← inferType e)
  let_expr Matrix R rows cols := ty | return none
  unless (← whnfR R).isConstOf ``Int do
    throwError "char_poly declined: unsupported coefficient type{indentExpr R}\nOnly Int matrices are currently supported"
  let some n ← getNatValue? rows |
    throwError "char_poly declined: the row dimension must reduce to a concrete natural number{indentExpr rows}"
  let some m ← getNatValue? cols |
    throwError "char_poly declined: the column dimension must reduce to a concrete natural number{indentExpr cols}"
  unless n == m do
    throwError "char_poly: expected a square matrix, but got dimensions {n} × {m}"
  checkClosed "matrix" e
  match ← evalMatrixCore n ty e with
  | .error msg =>
      throwError "char_poly declined: failed to evaluate the matrix with compiled code{indentExpr e}\n{msg}"
  | .ok value => return some ⟨n, e, value⟩

/-- Require a compiled matrix value to be definitionally visible to the
kernel through its original expression. -/
public meta def checkMatrixTransparent (input : CoreInput) : MetaM Unit := do
  let literal ← reifyIntMatrix input.value
  unless ← withTransparency .all <| isDefEq literal input.expr do
    throwError "char_poly declined: the matrix{indentExpr input.expr}\nevaluates to{indentExpr literal}\nbut is not definitionally transparent to the elaborator (an imported definition without `@[expose]`?); the kernel could not replay the characteristic-polynomial check"

/-- Compute and reify the characteristic polynomial after checking the input
transparency contract. -/
public meta def computedPoly (input : CoreInput) : MetaM (DensePoly Int × Expr) := do
  checkMatrixTransparent input
  let p := Matrix.charPoly input.value
  return (p, ← reifyZPoly p)

/-- Reified list data and its single checked Boolean proof. -/
public meta structure CertificateExpr where
  rows : Expr
  witness : Expr
  literal : Expr
  proof : Expr

/-- Reify the packed certificate produced by the existing computation. -/
public meta def certificateExpr (input : CoreInput) : MetaM CertificateExpr := do
  let rows := Matrix.CharPolyKernel.toRows input.value
  let w := Matrix.CharPolyKernel.produce input.value
  let descending := (Matrix.berkowitz input.value).toList
  unless Matrix.CharPolyKernel.checkCharPolyList input.n rows w descending do
    throwError "char_poly failure: the producer's packed certificate failed its compiled recheck"
  let steps := w.steps.map fun c => mkApp5 (mkConst ``Matrix.CharPolyKernel.Step.mk)
    (toExpr c.column) (toExpr c.vectors) (toExpr c.coefficients) (toExpr c.packedColumns) (toExpr c.product)
  let witness := mkApp3 (mkConst ``Matrix.CharPolyKernel.Witness.mk)
    (mkNatLit w.bound) (mkNatLit w.width) (listLit (mkConst ``Matrix.CharPolyKernel.Step) steps)
  let rowExpr := toExpr rows
  let literal := toExpr descending
  let check ← mkAppM ``Matrix.CharPolyKernel.checkCharPolyList
    #[mkNatLit input.n, rowExpr, witness, literal]
  let proof ← kernelDecideProof (← mkEq check (mkConst ``Bool.true))
  return ⟨rowExpr, witness, literal, proof⟩

/-- The polynomial represented by a descending coefficient list. -/
public meta def polyOfDescending (descending : Expr) : MetaM Expr := do
  let reverse ← mkAppM ``List.reverse #[descending]
  let coefficients ← mkAppM ``List.toArray #[reverse]
  mkAppM ``DensePoly.ofCoeffs #[coefficients]

private meta def identifyCore (input : CoreInput) (rows : Expr) : MetaM Expr := do
  let check ← mkAppM ``Matrix.checkRows #[input.expr, rows]
  let proof ← kernelDecideProof (← mkEq check (mkConst ``Bool.true))
  mkAppM ``Matrix.eq_of_checkRows #[input.expr, rows, proof]

/-- Elaborate a matrix argument.  A raw `#m[...]` literal is given an integer
coefficient expectation so its numerals do not default to `Nat`. -/
public meta def elabCoreArgument? (t : Syntax) : Term.TermElabM (Option CoreInput) := do
  let e ←
    if t.getKind == ``Matrix.matrixLiteral then
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let expected := mkApp3 (mkConst ``Matrix [Level.zero]) (mkConst ``Int) n n
      Term.elabTerm t (some expected)
    else
      Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  coreInput? e

/-- Emit the certified result for a core matrix. -/
public meta def resultForCore (input : CoreInput) : MetaM Expr := do
  let (_, p) ← computedPoly input
  let c ← certificateExpr input
  let ha ← identifyCore input c.rows
  let hp ← beqCoeffsProof (← polyOfDescending c.literal) p
  mkAppM ``Matrix.CharPolyResult.ofCheck
    #[input.expr, c.rows, c.witness, c.literal, p, ha, c.proof, hp]

/-- Evaluate and check a core dense-polynomial RHS, returning an informative
mismatch before asking the kernel to replay the equality. -/
private meta def checkCoreRhs (computed : DensePoly Int) (rhs : Expr) : MetaM Unit := do
  checkClosed "polynomial" rhs
  let ty ← inferType rhs
  match ← evalPolyCore ty rhs with
  | .error msg =>
      throwError "char_poly declined: failed to evaluate the polynomial in the goal{indentExpr rhs}\n{msg}"
  | .ok supplied =>
      unless DensePoly.beqCoeffs computed supplied do
        throwError "char_poly: the supplied polynomial has coefficients {supplied.toArray.toList}, but the computed characteristic polynomial has coefficients {computed.toArray.toList}"
      let literal ← reifyZPoly supplied
      unless ← withTransparency .all <| isDefEq literal rhs do
        throwError "char_poly: the polynomial{indentExpr rhs}\nevaluates to{indentExpr literal}\nbut is not definitionally transparent enough for kernel replay"

/-- Emit a proof of a direct core characteristic-polynomial equality. -/
private meta def proveCoreEquality (input : CoreInput) (rhs : Expr)
    (reverse : Bool) : MetaM Expr := do
  let (computed, _) ← computedPoly input
  checkCoreRhs computed rhs
  let c ← certificateExpr input
  let ha ← identifyCore input c.rows
  let hp ← beqCoeffsProof (← polyOfDescending c.literal) rhs
  let proof ← mkAppM ``Matrix.charPoly_eq_of_check
    #[input.expr, c.rows, c.witness, c.literal, rhs, ha, c.proof, hp]
  if reverse then mkEqSymm proof else return proof

/-- Find a core `charPoly` application on one side of an equality. -/
private meta def coreGoal? (target : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let some (_, lhs, rhs) := target.eq? | return none
  if lhs.getAppFn.isConstOf ``Matrix.charPoly then
    return some (lhs.getAppArgs.back!, rhs, false)
  if rhs.getAppFn.isConstOf ``Matrix.charPoly then
    return some (rhs.getAppArgs.back!, lhs, true)
  return none

/-- The result-producing term syntax. -/
syntax (name := charPolyTerm) "char_poly" term:max : term

/-- Expected-type-driven proof syntax used by bare `char_poly`. -/
syntax (name := charPolyProofTerm) "char_poly" : term

@[term_elab charPolyTerm] public meta def elabCharPoly : Term.TermElab :=
  fun stx expectedType? => do
    match stx with
    | `(char_poly $t) =>
        let some input ← elabCoreArgument? t | Elab.throwUnsupportedSyntax
        let result ← resultForCore input
        Term.ensureHasType expectedType? result
    | _ => Elab.throwUnsupportedSyntax

@[term_elab charPolyProofTerm] public meta def elabCharPolyProof : Term.TermElab :=
  fun _stx expectedType? => do
    let some expectedType := expectedType? |
      throwError "char_poly: bare term syntax needs an expected characteristic-polynomial equality"
    let target ← instantiateMVars expectedType
    let some (matrix, rhs, reverse) ← coreGoal? target |
      Elab.throwUnsupportedSyntax
    let some input ← coreInput? matrix | Elab.throwUnsupportedSyntax
    let proof ← proveCoreEquality input rhs reverse
    Term.ensureHasType expectedType? proof

/-- Introduce the fields of either supported result type as a `poly` let and
a `charPoly_eq` hypothesis. -/
private meta def introResult (e : Expr) : Tactic.TacticM Unit := do
  let ty ← whnf (← inferType e)
  let fn := ty.getAppFn
  let fields? : Option (Name × Name) :=
    if fn.isConstOf ``Matrix.CharPolyResult then
      some (``Matrix.CharPolyResult.poly, ``Matrix.CharPolyResult.charPoly_eq)
    else if fn.isConstOf `HexCharPolyMathlib.CharPolyResult then
      some (`HexCharPolyMathlib.CharPolyResult.poly,
        `HexCharPolyMathlib.CharPolyResult.charPoly_eq)
    else none
  let some (polyName, equalityName) := fields? |
    throwError "char_poly: internal error: unrecognized result type{indentExpr ty}"
  let polyE ← mkAppM polyName #[e]
  let equalityE ← mkAppM equalityName #[e]
  let polyTy ← inferType polyE
  Tactic.liftMetaTactic fun goal => do
    let (polyFVar, goal) ← (← goal.define `poly polyTy polyE).intro1P
    goal.withContext do
      let equalityTy := (← inferType equalityE).replace fun x =>
        if x == polyE then some (mkFVar polyFVar) else none
      let (_, goal) ← (← goal.assert `charPoly_eq equalityTy equalityE).intro1P
      return [goal]

/-- Tactic form which introduces the certified result fields. -/
syntax (name := charPolyTac) "char_poly" term:max : tactic

@[tactic charPolyTac] public meta def evalCharPolyTac : Tactic.Tactic :=
  fun stx => do
    match stx with
    | `(tactic| char_poly $t) => do
        let term ← `(char_poly $t)
        let e ← Tactic.withMainContext do
          Term.elabTerm term none
        introResult e
    | _ => Elab.throwUnsupportedSyntax

/-- Bare tactic form: close a direct characteristic-polynomial equality. -/
macro "char_poly" : tactic => `(tactic| exact char_poly)

end Hex.CharPolyTactic
