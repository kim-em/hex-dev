/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDetMathlib.Packed
public import HexPolyDetMathlib.Tree
public meta import HexPolyDetMathlib.Packed
public meta import HexPolyDetMathlib.Tree
public meta import HexPolyDet.Select
public meta import HexReflect.Session
public meta import HexMatrixMathlib.Literal

public meta section

namespace HexMatrixMathlib.DetPoly.Certificate

open Lean Meta Hex Hex.PolyDet Hex.PolyDet.Packed Hex.Reflect
open HexMatrixMathlib.Literal
open scoped HexMvPolyMathlib

register_option hex.det.checker : Nat := {
  defValue := 0
  descr := "det checker: 0 measured automatic selection, 1 term lists, 2 plain packing, 3 signed packing (comparison only)"
}
register_option hex.det.quotients : Bool := {
  defValue := true
  descr := "prepare optional integer quotient payloads for residue determinant certificates"
}

def arm (o : Options) : Arm :=
  match hex.det.checker.get o with
  | 1 => .lists | 2 => .packed | 3 => .signedPacked | _ => .automatic

/-- Fixed hard limits shared by preparation and the quoted checker. -/
def budget : Kronecker.Budget := { maxDenseDigits := 65536, maxPackedBits := 16777216 }

def quoteBudget : MetaM Expr :=
  mkAppM ``Kronecker.Budget.mk #[toExpr budget.maxDenseDigits, toExpr budget.maxPackedBits]

def quoteMode (m : Kronecker.MulMode) : Expr :=
  mkConst (match m with | .plain => ``Kronecker.MulMode.plain | .signedPacked => ``Kronecker.MulMode.signedPacked)

def selectOrFail (r : Except String Selection) : MetaM Selection :=
  match r with
  | .ok s => pure s
  | .error e => throwError "det: certificate failure: {e}"

/-- Structured certificate trace shared by tactic, term, and simproc forms. -/
def fields (s : Selection) (encoding : String) : List (String × Json) :=
  [("route", toJson s.route), ("encoding", toJson encoding),
   ("quotient_support", toJson s.quotientSupport),
   ("decline_reason", toJson s.reason),
   ("products", toJson (s.reports.map fun r => Json.mkObj
     [("row", toJson r.row), ("degrees", toJson r.size.degrees),
      ("strides", toJson r.size.strides), ("digits", toJson r.size.digits),
      ("coefficientBound", toJson r.size.coefficientBound), ("digitBits", toJson r.size.digitBits),
      ("packedBits", toJson r.size.packedBits), ("innerBits", toJson r.size.innerBits),
      ("outerSlotBits", toJson r.size.outerSlotBits?),
      ("limitingStage", toJson (reprStr r.size.limitingStage)), ("key", toJson (reprStr r.key))]))]

/-- Prepare exactly one Boolean proof after compiled validation of the selected arm. -/
def integer (k n : Nat) (rows : List (List (MvPoly.Kernel.PolyList Int)))
    (w : Matrix.DetWitness (MvPoly.Kernel.PolyList Int)) (rowsE wE : Expr) : MetaM (Expr × Selection) := do
  let opts ← getOptions
  let s ← selectOrFail <| profileit "det.symbolic.preflight" opts fun _ =>
    select budget (arm opts) k (products (ops k) n rows w)
  let ok := profileit "det.symbolic.selfcheck" opts fun _ =>
    if s.packed then checkDetPolyPacked budget s.mode k n rows w
    else Matrix.checkDetPolyList (ops k) n rows w
  unless ok do throwError "det: certificate failure: selected {s.route} checker returned false"
  let check ← if s.packed then
      mkAppM ``checkDetPolyPacked #[← quoteBudget, quoteMode s.mode, toExpr k, toExpr n, rowsE, wE]
    else
      mkAppM ``Matrix.checkDetPolyList #[← mkAppM' (mkApp (mkConst ``Polynomial.ops) (mkConst ``Int)) #[toExpr k], toExpr n, rowsE, wE]
  let h ← profileitM Exception "det.symbolic.certificate" opts <|
    decideProof (← mkEq check (mkConst ``Bool.true))
  let hdet ← if s.packed then
      mkAppM ``Polynomial.checkDetPolyPacked_sound
        #[← quoteBudget, quoteMode s.mode, toExpr k, toExpr n, rowsE, wE, h]
    else mkAppM ``Polynomial.checkDetPolyList_sound #[toExpr k, toExpr n, rowsE, wE, h]
  return (hdet, s)

/-- Admit every tree product and the target before quoting a tree certificate.
Structural bounds may exceed list bounds, in which case the existing route runs. -/
def tree? (k n : Nat) (rows : List (List (MvPoly.Kernel.PolyList Int)))
    (trees : Kronecker.TreeMatrix) (w : Matrix.DetWitness (MvPoly.Kernel.PolyList Int))
    (target : Kronecker.Expr) (value : MvPoly.Kernel.PolyList Int)
    (rowsE wE targetE valueE : Expr) : MetaM (Option (Expr × Expr × Selection)) := do
  let opts ← getOptions
  let arm := arm opts
  if arm == .lists then return none
  let mode := if arm == .signedPacked then Kronecker.MulMode.signedPacked else .plain
  let ps := products (ops k) n rows w
  let permuted := match w with
    | .triangular swaps _ _ => Matrix.DetWitness.permute swaps trees
    | .singular _ => trees
  let mut reports := []
  for p in ps do
    let b := match w with
      | .triangular .. => leading p.inner permuted
      | .singular _ => permuted
    let .ok size := Kronecker.sizeMulTree budget mode k 1 p.inner p.width [p.left] b [p.result]
      | throwError "det: malformed tree product at row {p.row}"
    let report : Report := ⟨p.row, size, p.key size⟩
    if !size.accepts budget then
      trace[HexMatrix.certificate] "det tree preflight: {declineMessage budget report}"
      return none
    reports := reports ++ [report]
  let .ok size := Kronecker.sizeTreeTermsEq budget k target value
    | throwError "det: malformed tree target"
  if !size.accepts budget then
    trace[HexMatrix.certificate] "det tree target preflight exceeds packing budget; using list entry proofs"
    return none
  if arm == .automatic && !reports.all (fun r => crossover.contains r.key) then return none
  let selection : Selection := { mode, packed := true, reports }
  unless profileit "det.symbolic.selfcheck" opts (fun _ =>
      checkDetPolyPackedTree budget mode k n trees w && Kronecker.checkTreeTermsEq budget k target value) do
    throwError "det: tree certificate failed its compiled check"
  let check ← mkAppM ``checkDetPolyPackedTree
    #[← quoteBudget, quoteMode mode, toExpr k, toExpr n, rowsE, wE]
  let h ← profileitM Exception "det.symbolic.certificate" opts <|
    decideProof (← mkEq check (mkConst ``Bool.true))
  let hdet ← mkAppM ``Tree.checkDetPolyPackedTree_sound
    #[← quoteBudget, quoteMode mode, toExpr k, toExpr n, rowsE, wE, h]
  let checkTarget ← mkAppM ``Kronecker.Kernel.treeTermsEq #[toExpr k, targetE, valueE]
  let htarget ← decideProof (← mkEq checkTarget (mkConst ``Bool.true))
  return some (hdet, htarget, selection)

def residue (p k n : Nat) (rows : List (List (MvPoly.Kernel.PolyList Nat)))
    (w : Matrix.DetWitness (MvPoly.Kernel.PolyList Nat)) (rowsE wE : Expr)
    (remaining : QuotientBudget) : MetaM (Expr × Selection) := do
  let opts ← getOptions
  let ps := (products (opsMod p k) n rows w).map (Product.map lift)
  let qs ← if hex.det.quotients.get opts && arm opts != .lists then do
      match profileit "det.symbolic.quotients" opts fun _ => prepareQuotients remaining p ps with
      | .ok qs => pure (some qs)
      | .error .unavailable => pure none
      | .error .invalidModulus => throwError "det: certificate failure: zero residue modulus"
      | .error (.indivisible i j) => throwError "det: certificate failure: residue product ({i}, {j}) is not divisible by {p}"
    else pure none
  let s ← selectOrFail <| profileit "det.symbolic.preflight" opts fun _ =>
    select budget (arm opts) k ps (some p) qs
  let qs ← if s.packed then
      match qs with
      | some qs => pure qs
      | none => throwError "det: certificate failure: selected packed checker without quotient payload"
    else pure []
  let ok := profileit "det.symbolic.selfcheck" opts fun _ =>
    if s.packed then checkDetPolyPackedMod budget s.mode p k n rows w qs
    else Matrix.checkDetPolyList (opsMod p k) n rows w
  unless ok do throwError "det: certificate failure: selected {s.route} checker returned false"
  let check ← if s.packed then
      mkAppM ``checkDetPolyPackedMod #[← quoteBudget, quoteMode s.mode, toExpr p, toExpr k, toExpr n, rowsE, wE, toExpr qs]
    else mkAppM ``Matrix.checkDetPolyList #[← mkAppM ``opsMod #[toExpr p, toExpr k], toExpr n, rowsE, wE]
  let h ← profileitM Exception "det.symbolic.certificate" opts <|
    decideProof (← mkEq check (mkConst ``Bool.true))
  let hdet ← if s.packed then
      mkAppM ``Residue.checkDetPolyPackedMod_sound
        #[toExpr p, ← quoteBudget, quoteMode s.mode, toExpr k, toExpr n, rowsE, wE, toExpr qs, h]
    else mkAppM ``Residue.checkDetPolyList_sound #[toExpr p, toExpr k, toExpr n, rowsE, wE, h]
  return (hdet, s)

end HexMatrixMathlib.DetPoly.Certificate
