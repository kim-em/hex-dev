/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMinPolyMathlib.Kernel
public meta import HexMinPolyMathlib.Kernel
public meta import HexPolyMathlib.Literal
public meta import Lean

public meta section

/-! Certified minimal polynomials of closed rational matrix literals. -/

namespace HexMinPolyMathlib.Tactic

open Lean Meta Elab HexMatrixMathlib HexMatrixMathlib.Literal Hex.Matrix.Lists

local instance : Lean.Grind.Field ℚ := Field.toGrindField

deriving instance ToExpr for Scaled
deriving instance ToExpr for ScaledRows
deriving instance ToExpr for Hex.Matrix.OrderWitness
deriving instance ToExpr for Hex.Matrix.LcmWitness
deriving instance ToExpr for Hex.Matrix.MinPolyWitness

inductive Outcome (α : Type) where
  | notApplicable
  | declined (message : MessageData)
  | success (value : α)

structure Certificate where
  literal : Recognized
  rows : List (List _root_.Rat)
  witness : Hex.Matrix.MinPolyWitness

/-- The advertised initial capability bound; soundness has no dimension bound. -/
def dimensionBudget : Nat := 16

def certify (A : Expr) : MetaM (Outcome Certificate) := do
  let some (n, m, carrier) ← shape? (← inferType A) | return .notApplicable
  unless (← whnfR carrier).isConstOf ``_root_.Rat do return .notApplicable
  unless n == m do return .notApplicable
  if n > dimensionBudget then
    return .declined m!"dimension {n} exceeds the configured dimension budget of {dimensionBudget}"
  let some lit ← literal? A |
    return .declined m!"the matrix must be a closed literal within the unfolding budget of {unfoldBudget}{indentExpr A}"
  let entries ← try evalEntries lit catch e => return .declined e.toMessageData
  let values : Array (Array _root_.Rat) :=
    entries.map (fun row => row.map (fun q => (q.num / q.den : _root_.Rat)))
  let rows := values.toList.map (·.toList)
  let matrix : Hex.Matrix ℚ n n := Hex.Matrix.ofFn fun i j => (values[i.val]!)[j.val]!
  let witness := Hex.Matrix.MinPolyWitness.ofCert matrix (Hex.Matrix.minPolyCert matrix)
  unless Hex.Matrix.checkMinPolyList n rows witness do
    throwError "min_poly: failure: the producer's certificate fails its integer list check"
  if ← isTracingEnabledFor `HexMatrix.certificate then
    let polys := witness.poly :: witness.order.map (·.poly) ++ witness.steps.flatMap
      (fun s => [s.common, s.left, s.right, s.bezoutLeft, s.bezoutRight, s.result])
    let matrices := witness.input :: witness.order.map (·.inv)
    let nums := rows.flatten.map (·.num) ++
      polys.flatMap (·.nums) ++ matrices.flatMap (·.nums.flatten)
    let denominators := rows.flatten.map (·.den) ++
      polys.map (·.denom) ++ matrices.map (·.denom)
    let inputHeight := witness.input.nums.flatten.foldl (fun b z => max b (integerBits z))
      (witness.input.denom.log2 + 1)
    reportCertificate "min_poly" (reprStr (rows, witness)) nums denominators
      [("scaled_input_bits", toJson inputHeight),
       ("polynomial_lengths", toJson (polys.map (·.nums.length))),
       ("order_degrees", toJson (witness.order.map (·.deg)))]
  return .success ⟨lit, rows, witness⟩

/-- Quote the complete proof and let the kernel check it once. -/
def checked (proof : Expr) : MetaM Expr := do
  try withOptions (Lean.Elab.async.set · false) do mkAuxTheorem (← inferType proof) proof
  catch e => throwError "min_poly: failure: the kernel rejected the certificate: {e.toMessageData}"

def valueProof (A : Expr) (c : Certificate) : MetaM Expr := do
  let hA ← identification c.literal A (toExpr c.rows)
  let hc ← decideProof (← mkEq
    (← mkAppM ``Hex.Matrix.checkMinPolyList #[mkNatLit c.literal.n, toExpr c.rows, toExpr c.witness])
    (mkConst ``Bool.true))
  mkAppM ``minpoly_eq_of_checkList #[A, toExpr c.rows, toExpr c.witness, hA, hc]

/-- Include the shared polynomial adapter's identification and the integer
comparison with the target in the same proof. -/
def targetProof (c : Certificate) (p : Expr) (qs : List _root_.Rat) (hpoly : Expr) : MetaM Expr := do
  let s := Scaled.encode qs
  unless Hex.Matrix.MinPolyLists.eqPoly c.witness.poly s do
    throwError "min_poly: the stated polynomial is false; computed ascending coefficients {decodeList c.witness.poly}"
  let hp ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit c.witness.poly.denom])
  let hs ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit s.denom])
  let hscale ← decideProof (← mkEq
    (← mkAppM ``scaleRow #[mkNatLit s.denom, toExpr qs, toExpr s.nums]) (mkConst ``Bool.true))
  let he ← decideProof (← mkEq
    (← mkAppM ``Hex.Matrix.MinPolyLists.eqPoly #[toExpr c.witness.poly, toExpr s]) (mkConst ``Bool.true))
  mkAppM ``eq_target #[toExpr c.witness, hp, p, toExpr qs, toExpr s, hs, hscale, he, hpoly]

def result (A : Expr) (c : Certificate) : MetaM Expr := do
  let qs := decodeList c.witness.poly
  let p ← mkAppM ``HexPolyMathlib.polynomialOfList #[toExpr qs]
  let ht ← targetProof c p qs (← mkEqRefl p)
  let proof ← checked (← mkEqTrans (← valueProof A c) ht)
  mkAppOptM ``Certified.mk #[none, none, none, some A, some p, some proof]

def prove (target : Expr) : MetaM (Outcome Expr) := do
  let some (_, lhs, rhs) := (← instantiateMVars target).eq? | return .notApplicable
  let (operation, p, reversed) ←
    if lhs.getAppFn.isConstOf ``minpoly then pure (lhs, rhs, false)
    else if rhs.getAppFn.isConstOf ``minpoly then pure (rhs, lhs, true)
    else return .notApplicable
  let A := operation.appArg!
  let c ← match ← certify A with
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .success c => pure c
  let resultType ← whnfR (← mkAppM ``MinPolyResult #[A])
  let expectedOperation := (mkApp resultType.appFn!.appArg! A).headBeta
  unless ← isDefEq operation expectedOperation do return .notApplicable
  let literal ← try HexPolyMathlib.Literal.recognize p
    catch e => return .declined e.toMessageData
  let ht ← targetProof c p literal.coefficients literal.proof
  let proof ← mkEqTrans (← valueProof A c) ht
  let proof ← if reversed then mkEqSymm proof else pure proof
  return .success (← checked proof)

syntax (name := minPolyTerm) "min_poly% " term : term

@[term_elab minPolyTerm] def elabMinPolyTerm : Term.TermElab := fun stx expected => do
  let `(min_poly% $t) := stx | throwUnsupportedSyntax
  let A ← elabArgument t (mkConst ``_root_.Rat)
  match ← certify A with
  | .success c => Term.ensureHasType expected (← result A c)
  | .notApplicable => throwError "min_poly: the input must be a square rational matrix"
  | .declined msg => throwError "min_poly: declined: {msg}"

syntax (name := minPolyTac) &"min_poly" : tactic

@[tactic minPolyTac] def evalMinPoly : Tactic.Tactic := fun _ => Tactic.withMainContext do
  match ← prove (← Tactic.getMainTarget) with
  | .success proof => Tactic.closeMainGoal `min_poly proof
  | .notApplicable => throwError "min_poly: expected minpoly ℚ A = p or p = minpoly ℚ A for a square rational literal"
  | .declined msg => throwError "min_poly: declined: {msg}"

end HexMinPolyMathlib.Tactic
