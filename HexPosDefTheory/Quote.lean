/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Quotation
public import HexPosDef.Scaled
public meta import HexPosDef.Scaled
public meta import HexMatrixTheory.Literal
public meta import Mathlib.Tactic.NormNum
public meta import Lean

public meta section

/-! Proof-producing quotation of closed rational real and complex entries. -/

namespace Hex.PosDefTheory.Quote

open Lean Meta
open HexMatrixTheory.Literal

deriving instance ToExpr for Hex.PosDef.Gaussian
deriving instance ToExpr for Hex.PosDef.PositiveCert
deriving instance ToExpr for Hex.PosDef.NegativeCert
deriving instance ToExpr for Hex.PosDef.Certificate

/-- Assemble a finite universal proof from its closed coordinate proofs. -/
def forallFin : (n : Nat) → Expr → Array Expr → MetaM Expr
  | 0, motive, _ => do
    withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit 0)) fun i => do
      mkLambdaFVars #[i] (mkApp2 (mkConst ``Fin.elim0 [Level.zero]) (mkApp motive i) i)
  | n + 1, motive, proofs => do
    let succMotive ← withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit n)) fun i =>
      mkLambdaFVars #[i] (mkApp motive (mkApp2 (mkConst ``Fin.succ) (mkNatLit n) i))
    let hs ← forallFin n succMotive (proofs.extract 1 proofs.size)
    return mkApp4 (mkConst ``Fin.cases [Level.zero]) (mkNatLit n) motive proofs[0]! hs

/-- A scalar equality is certified by ordinary proof-producing normalization. -/
def proveScalar (target : Expr) : MetaM Expr := do
  let goal ← mkFreshExprMVar target
  let some (carrier, _, _) := target.eq? | throwError "expected a scalar equality"
  let code ← if carrier.isConstOf ``Complex then
      `(tactic| apply Complex.ext <;> norm_num)
    else `(tactic| norm_num)
  let goals ← Lean.Elab.runTactic' goal.mvarId! code
  unless goals.isEmpty do throwError "entry normalization left an unproved equality{indentExpr target}"
  instantiateMVars goal

/-- A canonical rational cast in a supported field carrier. -/
def rationalValue (R : Expr) (q : Rat) : MetaM Expr :=
  mkAppOptM ``Rat.cast #[some R, none, some (toExpr q)]

def atEntry {α : Type} (lit : Recognized) (i j : Nat) (action : MetaM α) : MetaM α := do
  try action catch ex =>
    if ex.isRuntime then throw ex
    throwError "entry ({i}, {j}) over {lit.carrier}: {ex.toMessageData}"

/-- Preserve a normalization proof instead of evaluating the original entry again. -/
def scalar (e : Expr) : MetaM (Rat × Expr) := do
  let (q,h) ← evalEntryWithProof e
  let some (_,_,raw) := (← inferType h).eq? | throwError "expected a scalar equation"
  let value ← rationalValue (← inferType e) q
  let h ← if ← withReducible (isDefEq raw value) then pure h
    else mkEqTrans h (← proveScalar (← mkEq raw value))
  return (q, ← mkExpectedTypeHint h (← mkEq e value))

/-- Only unsupported entry normalization is a capability decline. -/
def entries {S : Type} (action : MetaM S) : MetaM (Except MessageData S) := do
  try return .ok (← action) catch ex =>
    if ex.isRuntime then throw ex
    return .error ex.toMessageData

/-- Assemble matrix identification from the normalization proofs. -/
def identify (lit : Recognized) (A decoded : Expr) (equations : Array (Array Expr)) : MetaM Expr := do
  let fin := mkApp (mkConst ``Fin) (mkNatLit lit.n)
  let mut rowProofs := #[]
  for i in [:lit.n] do
    let ii ← finLit lit.n i
    let mut proofs := #[]
    for j in [:lit.n] do
      let jj ← finLit lit.n j
      let expected ← mkEq (mkApp2 A ii jj) (mkApp2 decoded ii jj)
      proofs := proofs.push (← mkExpectedTypeHint (equations[i]!)[j]! expected)
    let motive ← withLocalDeclD `j fin fun j => do
      mkLambdaFVars #[j] (← mkEq (mkApp2 A ii j) (mkApp2 decoded ii j))
    rowProofs := rowProofs.push (← forallFin lit.n motive proofs)
  let motive ← withLocalDeclD `i fin fun i => withLocalDeclD `j fin fun j => do
    let prop ← mkEq (mkApp2 A i j) (mkApp2 decoded i j)
    mkLambdaFVars #[i] (← mkForallFVars #[j] prop)
  mkAppM ``_root_.Matrix.ext #[← forallFin lit.n motive rowProofs]

/-- Transport identification through scalar multiplication and its checked encoding. -/
def scaleEquation (lit : Recognized) (A : Expr) (s : Nat) (identification check : Expr) : MetaM Expr := do
  let scale ← mkAppOptM ``Nat.cast #[some lit.carrier, none, some (mkNatLit s)]
  let multiply ← withLocalDeclD `M (← inferType A) fun M => do
    mkLambdaFVars #[M] (← mkAppM ``HSMul.hSMul #[scale,M])
  mkEqTrans (← mkCongrArg multiply identification) check

/-- Quoted matrix data and a checked positive common scale. -/
structure Input (S : Type) where
  rows : List (List S)
  scale : Nat
  rowsExpr : Expr
  positiveScale : Expr
  equation : Expr

/-- Reuse literal identification for integer/rational carriers; normalize real entries with proofs. -/
def integer (lit : Recognized) (A : Expr) : MetaM (Except MessageData (Input Int)) := do
  let numeric := lit.carrier.isConstOf ``Int || lit.carrier.isConstOf ``Rat
  let input ← entries do
    let mut qs : Array (Array Rat) := #[]
    let mut equations := #[]
    let mut reducible := true
    for i in [:lit.n] do
      let mut row := #[]
      let mut proofs := #[]
      for j in [:lit.n] do
        let e := (lit.entries[i]!)[j]!
        if numeric then
          let (q,h) ← atEntry lit i j (evalEntryWithProof e)
          let value := if lit.carrier.isConstOf ``Int then toExpr q.num else toExpr q
          reducible := reducible && (← withReducible (isDefEq e value))
          let some (_,_,raw) := (← inferType h).eq? | throwError "expected an entry equation"
          let h ← if ← withReducible (isDefEq raw value) then pure h
            else mkEqTrans h (← atEntry lit i j (proveScalar (← mkEq raw value)))
          row := row.push q
          proofs := proofs.push h
        else
          let (q,h) ← atEntry lit i j (scalar e)
          row := row.push q
          proofs := proofs.push h
      qs := qs.push row
      equations := equations.push proofs
    return (qs,equations,reducible)
  match input with
  | .error msg => return .error msg
  | .ok (qs,equations,reducible) =>
    if lit.carrier.isConstOf ``Int then
      let nums := qs.toList.map (fun row => row.toList.map Rat.num)
      let rows := toExpr nums
      let hA ← if reducible then identification lit A rows else do
        let decoded ← mkAppM ``HexMatrixTheory.ofLists #[mkNatLit lit.n,mkNatLit lit.n,rows]
        identify lit A decoded equations
      let he ← mkAppM ``integer_identify #[A,rows,hA]
      let hs ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0,mkNatLit 1])
      return .ok ⟨nums,1,rows,hs,he⟩
    let qs := qs.toList.map Array.toList
    let data := Hex.Matrix.Lists.ScaledRows.encode qs
    let rows := toExpr data.nums
    let normalized ← mkAppM ``rationalMatrix #[lit.carrier,mkNatLit lit.n,toExpr qs]
    let hA ← if lit.carrier.isConstOf ``Rat then do
        let h ← if reducible then identification lit A (toExpr qs) else do
          let decoded ← mkAppM ``HexMatrixTheory.ofLists #[mkNatLit lit.n,mkNatLit lit.n,toExpr qs]
          identify lit A decoded equations
        mkAppM ``rational_identify #[A,toExpr qs,h]
      else identify lit A normalized equations
    let hs ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0,mkNatLit data.denom])
    let check ← decideProof (← mkEq (← mkAppM ``Hex.Matrix.Lists.scaleRows
      #[mkNatLit data.denom,toExpr qs,rows]) (mkConst ``Bool.true))
    let he ← mkAppM ``rational_scale
      #[lit.carrier,mkNatLit lit.n,mkNatLit data.denom,toExpr qs,rows,hs,check]
    return .ok ⟨data.nums,data.denom,rows,hs,← scaleEquation lit A data.denom hA he⟩

/-- Certify both complex components, then check all denominator cross products once. -/
def gaussian (lit : Recognized) (A : Expr) :
    MetaM (Except MessageData (Input Hex.PosDef.Gaussian)) := do
  let input ← entries do
    let mut qs : Array (Array (Rat × Rat)) := #[]
    let mut equations := #[]
    for i in [:lit.n] do
      let mut row := #[]
      let mut proofs := #[]
      for j in [:lit.n] do
        let e := (lit.entries[i]!)[j]!
        let (re,hr) ← atEntry lit i j (scalar (← mkAppM ``Complex.re #[e]))
        let (im,hi) ← atEntry lit i j (scalar (← mkAppM ``Complex.im #[e]))
        let value ← mkAppM ``Complex.mk #[← rationalValue (mkConst ``Real) re,
          ← rationalValue (mkConst ``Real) im]
        let h ← mkAppOptM ``Complex.ext #[some e,some value,some hr,some hi]
        proofs := proofs.push h
        row := row.push (re,im)
      qs := qs.push row
      equations := equations.push proofs
    return (qs,equations)
  match input with
  | .error msg => return .error msg
  | .ok (qs,equations) =>
    let qs := qs.toList.map Array.toList
    let data := Hex.PosDef.Gaussian.ScaledRows.encode qs
    let rows := toExpr data.nums
    let normalized ← mkAppM ``complexMatrix #[mkNatLit lit.n,toExpr qs]
    let hA ← identify lit A normalized equations
    let hs ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0,mkNatLit data.denom])
    let check ← decideProof (← mkEq (← mkAppM ``Hex.PosDef.Gaussian.scaleRows
      #[mkNatLit data.denom,toExpr qs,rows]) (mkConst ``Bool.true))
    let he ← mkAppM ``gaussian_scale #[mkNatLit lit.n,mkNatLit data.denom,toExpr qs,rows,hs,check]
    return .ok ⟨data.nums,data.denom,rows,hs,← scaleEquation lit A data.denom hA he⟩

end Hex.PosDefTheory.Quote
