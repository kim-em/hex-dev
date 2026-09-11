/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexMatrixTactic.Model
public import HexMatrixTactic.Model
public meta import HexMatrixTactic.Syntax
public import HexMatrixTactic.Syntax

public section

/-!
The `char_poly` frontend on closed `Hex.Matrix Int n n` inputs.

Compiled evaluation discovers the coefficients and every intermediate
Berkowitz vector; the emitted proof is the stepwise certificate of
`HexCharPoly.Certificate`, whose scalar, vector, and final coefficient checks
the kernel replays, closed by `Hex.Matrix.charPoly_eq_of_check`.
-/

namespace Hex.MatrixTactic.CharPoly

open Lean Meta Elab

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

/-- Classify and evaluate an already elaborated `Hex.Matrix Int n n`.  A
non-Hex type returns `none`, allowing another elaborator for the same syntax
kind to try it. -/
public meta def coreInput? (e : Expr) : MetaM (Option CoreInput) := do
  let e ← instantiateMVars e
  let some shape ← shape? "char_poly" (← inferType e) | return none
  unless shape.carrier.isConstOf ``Int do
    throwError "char_poly: unsupported coefficient type{indentExpr shape.carrier}\nOnly Int matrices are currently supported"
  unless shape.rows = shape.cols do
    throwError "char_poly: expected a square matrix, but got dimensions {shape.rows} × {shape.cols}"
  let (value, _) ← evalMatrixChecked Int "char_poly" (mkConst ``Int) (fun z => pure (toExpr z))
    shape.rows shape.rows e
  return some ⟨shape.rows, e, value⟩

/-- Compute and reify the characteristic polynomial. -/
public meta def computedPoly (input : CoreInput) : MetaM (DensePoly Int × Expr) := do
  let p := Matrix.charPoly input.value
  return (p, ← reifyZPoly p)

/-- Reified data and proof for one depth of a stepwise certificate. -/
public meta structure CertificateExpr (k : Nat) where
  value : _root_.Vector Int (k + 1)
  literal : Expr
  proof : Expr

private meta structure MomentsExpr (count : Nat) where
  values : List Int
  literal : Expr
  proof : Expr

private meta abbrev EntryProof (k : Nat) :=
  (i : Fin k) → (hiExpr : Expr) → MetaM Expr

private meta abbrev MatrixEntryProof (k : Nat) :=
  (i : Fin k) → (hiExpr : Expr) → EntryProof k

private meta def directEntryProof {k : Nat} (v : _root_.Vector Int k)
    (vExpr : Expr) : EntryProof k := fun i hiExpr => do
  let source := mkAppN (mkConst ``Matrix.vectorEntry)
    #[mkNatLit k, vExpr, mkNatLit i.val, hiExpr]
  kernelDecideProof "char_poly" (← mkEq source (toExpr v[i]))

private meta def finishEntryProof (lemma : Expr) (value : Int) : MetaM Expr := do
  let some (_, _, rhs) := (← inferType lemma).eq? |
    throwError "char_poly: internal entry-reduction lemma is not an equality"
  let checked ← kernelDecideProof "char_poly" (← mkEq rhs (toExpr value))
  mkAppM ``Eq.trans #[lemma, checked]

private meta structure DotExpr (k : Nat) where
  value : Int
  indices : Expr
  proof : Expr

private meta def buildDotFold {k : Nat} (ring : Expr)
    (u : _root_.Vector Int k) (uExpr : Expr)
    (v : _root_.Vector Int k) (vExpr : Expr)
    (uEntry vEntry : EntryProof k) :
    (indices : List (Fin k)) → (acc : Int) → Expr → MetaM (DotExpr k)
  | [], acc, accExpr => do
      let finType := mkApp (mkConst ``Fin) (mkNatLit k)
      let indicesExpr := listLit finType []
      let proof := mkAppN (mkConst ``Matrix.DotProductCertificate.nil)
        #[ring, mkNatLit k, uExpr, vExpr, accExpr]
      return ⟨acc, indicesExpr, proof⟩
  | i :: indices, acc, accExpr => do
      let hiProof ← kernelDecideProof "char_poly"
        (← mkAppM ``LT.lt #[mkNatLit i.val, mkNatLit k])
      let fin := mkApp3 (mkConst ``Fin.mk)
        (mkNatLit k) (mkNatLit i.val) hiProof
      let left := u[i]
      let right := v[i]
      let leftExpr := toExpr left
      let rightExpr := toExpr right
      let leftProof ← uEntry i hiProof
      let rightProof ← vEntry i hiProof
      let next := acc + left * right
      let nextExpr := toExpr next
      let product := mkApp3 (mkConst ``Matrix.mulWith)
        ring leftExpr rightExpr
      let sum := mkApp3 (mkConst ``Matrix.addWith) ring accExpr product
      let stepProof ← kernelDecideProof "char_poly" (← mkEq sum nextExpr)
      let tail ← buildDotFold ring u uExpr v vExpr uEntry vEntry
        indices next nextExpr
      let finType := mkApp (mkConst ``Fin) (mkNatLit k)
      let indicesExpr := mkApp3 (mkConst ``List.cons [Level.zero])
        finType fin tail.indices
      let proof := mkAppN (mkConst ``Matrix.DotProductCertificate.cons)
        #[ring, mkNatLit k, uExpr, vExpr, fin, tail.indices, accExpr,
          leftExpr, rightExpr, nextExpr, toExpr tail.value, leftProof,
          rightProof, stepProof, tail.proof]
      return ⟨tail.value, indicesExpr, proof⟩

private meta def buildDotCertificate {k : Nat} (ring : Expr)
    (u : _root_.Vector Int k) (uExpr : Expr)
    (v : _root_.Vector Int k) (vExpr : Expr)
    (uEntry vEntry : EntryProof k) : MetaM (DotExpr k) := do
  let zeroExpr := mkApp (mkConst ``Matrix.zeroWith) ring
  buildDotFold ring u uExpr v vExpr uEntry vEntry
    (List.finRange k) 0 zeroExpr

private meta def buildMulVecCertificate {k : Nat} (ring : Expr)
    (B : Matrix Int k k) (matrixExpr : Expr)
    (matrixEntry : MatrixEntryProof k)
    (w : _root_.Vector Int k) (wExpr nextExpr : Expr)
    (wEntry : EntryProof k) : MetaM Expr := do
  let mut proof := mkAppN (mkConst ``Matrix.MulVecCertificate.zero)
    #[ring, mkNatLit k, matrixExpr, wExpr, nextExpr]
  for i in [0:k] do
    if hi : i < k then
      let hiProp ← mkAppM ``LT.lt #[mkNatLit i, mkNatLit k]
      let hiProof ← kernelDecideProof "char_poly" hiProp
      let fin := mkApp3 (mkConst ``Fin.mk)
        (mkNatLit k) (mkNatLit i) hiProof
      let row := Matrix.row B ⟨i, hi⟩
      let rowExpr := mkAppN (mkConst ``Matrix.row [Level.zero])
        #[mkConst ``Int, mkNatLit k, mkNatLit k, matrixExpr, fin]
      let dot ← buildDotCertificate ring row rowExpr w wExpr
        (matrixEntry ⟨i, hi⟩ hiProof) wEntry
      let target := mkAppN (mkConst ``Matrix.vectorEntry)
        #[mkNatLit k, nextExpr, mkNatLit i, hiProof]
      let entryProof ← kernelDecideProof "char_poly" (← mkEq target (toExpr dot.value))
      proof := mkAppN (mkConst ``Matrix.MulVecCertificate.step)
        #[ring, mkNatLit k, matrixExpr, wExpr, nextExpr, mkNatLit i,
          hiProof, toExpr dot.value, proof, dot.proof, entryProof]
    else
      throwError "char_poly: internal matrix-vector certificate index escaped its dimension"
  return proof

private meta def buildMoments {k : Nat} (ring : Expr)
    (B : Matrix Int k k) (matrixExpr : Expr)
    (matrixEntry : MatrixEntryProof k)
    (row : _root_.Vector Int k) (rowExpr : Expr) (rowEntry : EntryProof k) :
    (count : Nat) → (w : _root_.Vector Int k) → Expr → EntryProof k →
      MetaM (MomentsExpr count)
  | 0, _w, wExpr, _wEntry => do
      let literal := listLit (mkConst ``Int) []
      let proof := mkAppN (mkConst ``Matrix.MomentsCertificate.zero)
        #[ring, mkNatLit k, matrixExpr, rowExpr, wExpr]
      return ⟨[], literal, proof⟩
  | 1, w, wExpr, wEntry => do
      let dot ← buildDotCertificate ring row rowExpr w wExpr rowEntry wEntry
      let value := -dot.value
      let valueExpr := toExpr value
      let negated := mkApp2 (mkConst ``Matrix.negWith) ring (toExpr dot.value)
      let headProof ← kernelDecideProof "char_poly" (← mkEq negated valueExpr)
      let literal := listLit (mkConst ``Int) [valueExpr]
      let proof := mkAppN (mkConst ``Matrix.MomentsCertificate.one)
        #[ring, mkNatLit k, matrixExpr, rowExpr, wExpr, valueExpr,
          toExpr dot.value, dot.proof, headProof]
      return ⟨[value], literal, proof⟩
  | j + 2, w, wExpr, wEntry => do
      let dot ← buildDotCertificate ring row rowExpr w wExpr rowEntry wEntry
      let value := -dot.value
      let valueExpr := toExpr value
      let negated := mkApp2 (mkConst ``Matrix.negWith) ring (toExpr dot.value)
      let headProof ← kernelDecideProof "char_poly" (← mkEq negated valueExpr)
      let next := B * w
      let nextExpr ← reifyIntVector next
      let mulCertificate ← buildMulVecCertificate ring B matrixExpr matrixEntry
        w wExpr nextExpr wEntry
      let nextEntry := directEntryProof next nextExpr
      let tail ← buildMoments ring B matrixExpr matrixEntry row rowExpr rowEntry
        (j + 1) next nextExpr nextEntry
      let literal := mkApp3 (mkConst ``List.cons [Level.zero])
        (mkConst ``Int) valueExpr tail.literal
      let proof := mkAppN (mkConst ``Matrix.MomentsCertificate.step)
        #[ring, mkNatLit k, matrixExpr, rowExpr, mkNatLit j, wExpr,
          nextExpr, valueExpr, toExpr dot.value, tail.literal, dot.proof,
          headProof, mulCertificate, tail.proof]
      return ⟨value :: tail.values, literal, proof⟩

private meta def buildCertificate (input : CoreInput) (ring : Expr) :
    (k : Nat) → k ≤ input.n → MetaM (CertificateExpr k)
  | 0, _ => do
      let proof := mkApp3 (mkConst ``Matrix.BerkowitzCertificate.zero)
        (mkNatLit input.n) ring input.expr
      let type ← inferType proof
      let literal := type.getAppArgs.back!
      return ⟨#v[1], literal, proof⟩
  | k + 1, hk => do
      let previous ← buildCertificate input ring k (by omega)
      let leProp ← mkAppM ``LE.le #[mkNatLit (k + 1), mkNatLit input.n]
      let leProof ← kernelDecideProof "char_poly" leProp
      let block := Matrix.trailingBlock input.value k (by omega)
      let row := @Matrix.berkowitzRow Int input.n input.value k hk
      let col := @Matrix.berkowitzCol Int input.n input.value k hk
      let blockLeProof ← kernelDecideProof "char_poly"
        (← mkAppM ``LE.le #[mkNatLit k, mkNatLit input.n])
      let blockExpr := mkAppN (mkConst ``Matrix.trailingBlock [Level.zero])
        #[mkConst ``Int, mkNatLit input.n, input.expr, mkNatLit k,
          blockLeProof]
      let rowExpr := mkAppN (mkConst ``Matrix.berkowitzRow [Level.zero])
        #[mkConst ``Int, mkNatLit input.n, input.expr, mkNatLit k, leProof]
      let colExpr := mkAppN (mkConst ``Matrix.berkowitzCol [Level.zero])
        #[mkConst ``Int, mkNatLit input.n, input.expr, mkNatLit k, leProof]
      let matrixEntry : MatrixEntryProof k := fun i hiExpr j hjExpr => do
        let lemma ← mkAppM ``Matrix.vectorEntry_row_trailingBlock
          #[input.expr, mkNatLit k, blockLeProof, mkNatLit i.val,
            mkNatLit j.val, hiExpr, hjExpr]
        finishEntryProof lemma block[(i, j)]
      let rowEntry : EntryProof k := fun j hjExpr => do
        let lemma ← mkAppM ``Matrix.vectorEntry_berkowitzRow
          #[input.expr, leProof, mkNatLit j.val, hjExpr]
        finishEntryProof lemma row[j]
      let colEntry : EntryProof k := fun i hiExpr => do
        let lemma ← mkAppM ``Matrix.vectorEntry_berkowitzCol
          #[input.expr, leProof, mkNatLit i.val, hiExpr]
        finishEntryProof lemma col[i]
      let moments ← buildMoments ring block blockExpr matrixEntry row rowExpr
        rowEntry k col colExpr colEntry
      let column := @Matrix.berkowitzColumn Int Lean.Grind.instCommRingInt
        input.n input.value k hk
      let columnLiteral ← reifyIntVector column
      let columnSource := mkAppN (mkConst ``Matrix.columnOfMoments)
        #[ring, mkNatLit input.n, input.expr, mkNatLit k, leProof, moments.literal]
      let columnCheck ← mkAppM ``Matrix.Vector.beqEntries
        #[columnSource, columnLiteral]
      let columnProp ← mkEq columnCheck (mkConst ``Bool.true)
      let columnProof ← kernelDecideProof "char_poly" columnProp
      let next := Matrix.toeplitzMulVec column previous.value
      let nextLiteral ← reifyIntVector next
      let step := mkAppN (mkConst ``Matrix.toeplitzMulVec [Level.zero])
        #[mkConst ``Int, ring, mkNatLit k, columnLiteral, previous.literal]
      let stepCheck ← mkAppM ``Matrix.Vector.beqEntries #[step, nextLiteral]
      let stepProp ← mkEq stepCheck (mkConst ``Bool.true)
      let stepProof ← kernelDecideProof "char_poly" stepProp
      let proof := mkAppN (mkConst ``Matrix.BerkowitzCertificate.step)
        #[mkNatLit input.n, ring, input.expr, mkNatLit k, leProof,
          previous.literal, nextLiteral, moments.literal, columnLiteral,
          previous.proof, moments.proof, columnProof, stepProof]
      return ⟨next, nextLiteral, proof⟩

/-- Build the complete stepwise certificate for an input matrix using the
supplied commutative-ring instance expression. -/
public meta def certificateExpr (input : CoreInput) (ring : Expr) :
    MetaM (CertificateExpr input.n) :=
  buildCertificate input ring input.n (Nat.le_refl input.n)

/-- `DensePoly.ofCoeffs descending.reverse.toArray` as an expression. -/
public meta def polyOfDescending (descending : Expr) : MetaM Expr := do
  let reverse ← mkAppM ``_root_.Vector.reverse #[descending]
  let coefficients ← mkAppM ``_root_.Vector.toArray #[reverse]
  mkAppM ``DensePoly.ofCoeffs #[coefficients]

/-- Emit the certified result for a core matrix. -/
public meta def resultForCore (input : CoreInput) : MetaM Expr := do
  let (_, p) ← computedPoly input
  let matrixLiteral ← reifyIntMatrix input.value
  let certificateInput := { input with expr := matrixLiteral }
  let certificate ← certificateExpr certificateInput
    (mkConst ``Lean.Grind.instCommRingInt)
  let source ← polyOfDescending certificate.literal
  let check ← beqCoeffsProof "char_poly" source p
  let proof ← try
      withTransparency .all <| mkAppM ``Matrix.charPoly_eq_of_check
        #[input.expr, certificate.literal, p, certificate.proof, check]
    catch _ =>
      throwError "char_poly: compiled evaluation succeeded, but the kernel could not replay the characteristic-polynomial check; the input is too opaque or Lean's ordinary reduction limits were reached"
  let some (_, lhs, _) := (← inferType proof).eq? |
    throwError "char_poly: internal error: the certificate endpoint is not an equality"
  mkAppOptM ``Hex.MatrixTactic.Certified.mk
    #[none, none, some lhs.appFn!, some input.expr, some p, some proof]

/-- Evaluate and check a core dense-polynomial RHS, returning an informative
mismatch before asking the kernel to replay the equality. -/
private meta def checkCoreRhs (computed : DensePoly Int) (rhs : Expr) : MetaM Unit := do
  checkClosed "char_poly" "polynomial" rhs
  let ty ← inferType rhs
  match ← evalPolyCore ty rhs with
  | .error msg =>
      throwError "char_poly: failed to evaluate the polynomial in the goal{indentExpr rhs}\n{msg}"
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
  let matrixLiteral ← reifyIntMatrix input.value
  let certificateInput := { input with expr := matrixLiteral }
  let certificate ← certificateExpr certificateInput
    (mkConst ``Lean.Grind.instCommRingInt)
  let source ← polyOfDescending certificate.literal
  let check ← beqCoeffsProof "char_poly" source rhs
  let proof ← try
      mkAppM ``Matrix.charPoly_eq_of_check
        #[input.expr, certificate.literal, rhs, certificate.proof, check]
    catch _ =>
      throwError "char_poly: compiled evaluation succeeded, but the kernel could not replay the equality; Lean's ordinary reduction limits may have been reached"
  if reverse then mkEqSymm proof else return proof

/-- Find a core `charPoly` application on one side of an equality. -/
private meta def coreGoal? (target : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let some (_, lhs, rhs) := target.eq? | return none
  if lhs.getAppFn.isConstOf ``Matrix.charPoly then
    return some (lhs.getAppArgs.back!, rhs, false)
  if rhs.getAppFn.isConstOf ``Matrix.charPoly then
    return some (rhs.getAppArgs.back!, lhs, true)
  return none

@[term_elab Hex.MatrixTactic.charPolyTerm]
public meta def elabCharPoly : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(char_poly $t) =>
      let some input ← coreInput? (← elabMatrixArgument t) | throwUnsupportedSyntax
      let result ← resultForCore input
      Term.ensureHasType expectedType? result
  | _ => throwUnsupportedSyntax

@[tactic Hex.MatrixTactic.charPolyTac]
public meta def evalCharPolyTac : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let target ← Tactic.getMainTarget
  let some (matrix, rhs, reverse) ← coreGoal? target | throwUnsupportedSyntax
  let some input ← coreInput? matrix | throwUnsupportedSyntax
  let proof ← proveCoreEquality input rhs reverse
  Tactic.closeMainGoal `char_poly proof

/-- Introduce the fields of a certified characteristic polynomial as a `poly`
let and a `charPoly_eq` hypothesis. -/
public meta def introResult (e : Expr) : Tactic.TacticM Unit := do
  let polyE ← mkAppM ``Hex.MatrixTactic.Certified.value #[e]
  let equalityE ← mkAppM ``Hex.MatrixTactic.Certified.proof #[e]
  let polyTy ← inferType polyE
  Tactic.liftMetaTactic fun goal => do
    let (polyFVar, goal) ← (← goal.define `poly polyTy polyE).intro1P
    goal.withContext do
      let equalityTy := (← inferType equalityE).replace fun x =>
        if x == polyE then some (mkFVar polyFVar) else none
      let (_, goal) ← (← goal.assert `charPoly_eq equalityTy equalityE).intro1P
      return [goal]

@[tactic Hex.MatrixTactic.charPolyIntroTac]
public meta def evalCharPolyIntroTac : Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| char_poly $t) => do
      let term ← `(char_poly $t)
      let e ← Tactic.withMainContext do
        let e ← Term.elabTerm term none
        Term.synthesizeSyntheticMVarsNoPostponing
        instantiateMVars e
      introResult e
  | _ => throwUnsupportedSyntax

end Hex.MatrixTactic.CharPoly
