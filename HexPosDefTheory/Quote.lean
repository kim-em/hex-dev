/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Scaling
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

def intCast (R : Expr) (z : Int) : MetaM Expr :=
  mkAppOptM ``Int.cast #[some R, none, some (toExpr z)]

/-- A canonical rational value in a supported scalar carrier. -/
def rationalValue (R : Expr) (q : Rat) : MetaM Expr := do
  let num ← intCast R q.num
  if q.den = 1 then return num
  let den ← mkAppOptM ``Nat.cast #[some R, none, some (toExpr q.den)]
  mkAppM ``HDiv.hDiv #[num, den]

/-- Read a rational through the existing normalization interfaces while
preserving runtime exceptions. -/
def evalEntry (e : Expr) : MetaM Rat := do
  let numeric (e : Expr) : MetaM Rat := do
    let ⟨_, _, eQ⟩ ← Qq.inferTypeQ' e
    let result ← Mathlib.Meta.NormNum.derive eQ
    let some q := result.toRat |
      throwError "the following entry cannot be simplified to a numeral{indentExpr e}"
    return q
  try numeric e catch ex =>
    if ex.isRuntime then throw ex
    let ctx ← Simp.mkContext (config := { decide := true })
      (simpTheorems := #[← getSimpTheorems]) (congrTheorems := ← getSimpCongrTheorems)
    let result ← Mathlib.Meta.NormNum.deriveSimp ctx #[] true e
    numeric result.expr

def atEntry {α : Type} (lit : Recognized) (i j : Nat) (action : MetaM α) : MetaM α := do
  try action catch ex =>
    if ex.isRuntime then throw ex
    throwError "entry ({i}, {j}) over {lit.carrier}: {ex.toMessageData}"

/-- Build the matrix equality from scalar proofs, without a real or complex equality decision. -/
def scaling (lit : Recognized) (A : Expr) (s : Nat) (decoded : Expr)
    (values equations : Array (Array Expr)) : MetaM Expr := do
  let scale ← mkAppOptM ``Nat.cast #[some lit.carrier, none, some (mkNatLit s)]
  let scaled ← mkAppM ``HSMul.hSMul #[scale, A]
  let fin := mkApp (mkConst ``Fin) (mkNatLit lit.n)
  let mut rowProofs := #[]
  for i in [:lit.n] do
    let ii ← finLit lit.n i
    let mut proofs := #[]
    for j in [:lit.n] do
      let jj ← finLit lit.n j
      let he := (equations[i]!)[j]!
      let some (_, _, q) := (← inferType he).eq? | throwError "expected an entry equation"
      let multiply ← withLocalDeclD `x lit.carrier fun x => do
        mkLambdaFVars #[x] (← mkAppM ``HMul.hMul #[scale, x])
      let transport ← mkCongrArg multiply he
      let lhs ← mkAppM ``HMul.hMul #[scale, q]
      let arithmetic ← atEntry lit i j (proveScalar (← mkEq lhs (values[i]!)[j]!))
      let hp ← mkEqTrans transport arithmetic
      let expected ← mkEq (mkApp2 scaled ii jj) (mkApp2 decoded ii jj)
      proofs := proofs.push (← mkExpectedTypeHint hp expected)
    let motive ← withLocalDeclD `j fin fun j => do
      mkLambdaFVars #[j] (← mkEq (mkApp2 scaled ii j) (mkApp2 decoded ii j))
    rowProofs := rowProofs.push (← forallFin lit.n motive proofs)
  let motive ← withLocalDeclD `i fin fun i => withLocalDeclD `j fin fun j => do
    let prop ← mkEq (mkApp2 scaled i j) (mkApp2 decoded i j)
    mkLambdaFVars #[i] (← mkForallFVars #[j] prop)
  mkAppM ``_root_.Matrix.ext #[← forallFin lit.n motive rowProofs]

/-- Quoted matrix data and a checked positive common scale. -/
structure Input (S : Type) where
  rows : List (List S)
  scale : Nat
  rowsExpr : Expr
  positiveScale : Expr
  equation : Expr

/-- Quote rational entries of an integer, rational, real, or real-valued complex matrix. -/
def integer (lit : Recognized) (A : Expr) : MetaM (Input Int) := do
  let mut qs : Array (Array Rat) := #[]
  let mut equations := #[]
  for i in [:lit.n] do
    let mut row := #[]
    let mut proofs := #[]
    for j in [:lit.n] do
      let e := (lit.entries[i]!)[j]!
      let q ← atEntry lit i j (evalEntry e)
      let value ← rationalValue lit.carrier q
      proofs := proofs.push (← atEntry lit i j (proveScalar (← mkEq e value)))
      row := row.push q
    qs := qs.push row
    equations := equations.push proofs
  let data := Hex.Matrix.Lists.ScaledRows.encode (qs.toList.map Array.toList)
  let rows ← rowList (mkConst ``Int) (data.nums.toArray.map (fun row => row.toArray.map toExpr))
  let model ← mkAppOptM ``Hex.PosDefTheory.intModel #[some lit.carrier, none, none, none, none, none]
  let decoded ← mkAppM ``Hex.PosDefTheory.Lists.matrix #[model, mkNatLit lit.n, rows]
  let values ← data.nums.toArray.mapM fun row => row.toArray.mapM (intCast lit.carrier)
  let hs ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit data.denom])
  return ⟨data.nums, data.denom, rows, hs, ← scaling lit A data.denom decoded values equations⟩

/-- Quote genuine complex data by certifying both rational components. -/
def gaussian (lit : Recognized) (A : Expr) : MetaM (Input Hex.PosDef.Gaussian) := do
  let mut qs : Array (Array (Rat × Rat)) := #[]
  let mut equations := #[]
  for i in [:lit.n] do
    let mut row := #[]
    let mut proofs := #[]
    for j in [:lit.n] do
      let e := (lit.entries[i]!)[j]!
      let re ← atEntry lit i j (evalEntry (← mkAppM ``Complex.re #[e]))
      let im ← atEntry lit i j (evalEntry (← mkAppM ``Complex.im #[e]))
      let value ← mkAppM ``Complex.mk #[← rationalValue (mkConst ``Real) re,
        ← rationalValue (mkConst ``Real) im]
      proofs := proofs.push (← atEntry lit i j (proveScalar (← mkEq e value)))
      row := row.push (re, im)
    qs := qs.push row
    equations := equations.push proofs
  let data := Hex.PosDef.Gaussian.ScaledRows.encode (qs.toList.map Array.toList)
  let rows ← rowList (mkConst ``Hex.PosDef.Gaussian)
    (data.nums.toArray.map (fun row => row.toArray.map toExpr))
  let decoded ← mkAppM ``Hex.PosDefTheory.Lists.matrix
    #[mkConst ``Hex.PosDefTheory.gaussianModel, mkNatLit lit.n, rows]
  let values ← data.nums.toArray.mapM fun row => row.toArray.mapM fun z => do
    mkAppM ``Complex.mk #[← intCast (mkConst ``Real) z.re, ← intCast (mkConst ``Real) z.im]
  let hs ← decideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit data.denom])
  -- Complex extensionality reduces each scalar equality to its two real components.
  let equation ← scaling lit A data.denom decoded values equations
  return ⟨data.nums, data.denom, rows, hs, equation⟩

end Hex.PosDefTheory.Quote
