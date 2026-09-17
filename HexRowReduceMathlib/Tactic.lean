/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRowReduceMathlib.Kernel
public meta import HexRowReduceMathlib.Kernel
public meta import HexRowReduce.Witness
public meta import Lean

public meta section

namespace HexRowReduceMathlib.Tactic

open Lean Meta Elab HexMatrixMathlib HexMatrixMathlib.Literal Hex.Matrix.Lists

local instance : Lean.Grind.Field ℚ := Field.toGrindField

deriving instance ToExpr for Scaled
deriving instance ToExpr for ScaledRows
deriving instance ToExpr for Hex.Matrix.InverseWitness
deriving instance ToExpr for Hex.Matrix.SolveBasis
deriving instance ToExpr for Hex.Matrix.SolveWitness

inductive Outcome (α : Type) where
  | notApplicable
  | declined (message : MessageData)
  | success (value : α)

structure Input where
  literal : Recognized
  rows : List (List _root_.Rat)

structure VecInput where
  literal : VectorLiteral
  entries : List _root_.Rat

/-- Constant zero and identity matrices use the shared closed-function route. -/
def matrixLiteral? (A : Expr) (n m : Nat) : MetaM (Option Recognized) := do
  if let some lit ← literal? A then return some lit
  let ty ← inferType A
  let zero ← mkNumeral ty 0
  let constant ← if ← isDefEq A zero then pure true else
    if n == m then isDefEq A (← mkNumeral ty 1) else pure false
  unless constant do return none
  withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit n)) fun i =>
    withLocalDeclD `j (mkApp (mkConst ``Fin) (mkNatLit m)) fun j => do
      literal? (← mkLambdaFVars #[i, j] (mkApp2 A i j))

/-- Rational matrix recognition, with shared literal identification. -/
def readMatrix (A : Expr) : MetaM (Outcome Input) := do
  let some (n, m, carrier) ← shape? (← inferType A) | return .notApplicable
  unless (← whnfR carrier).isConstOf ``_root_.Rat do return .notApplicable
  if A.hasFVar || A.hasMVar then return .notApplicable
  if n > 32 || m > 32 then
    return .declined m!"matrix shape {n} × {m} exceeds the dimension budget of 32"
  let some lit ← matrixLiteral? A n m |
    return .declined m!"expected a closed rational matrix literal within the unfolding budget of {unfoldBudget}"
  let mut rows := []
  for i in [:n] do
    let mut row := []
    for j in [:m] do
      let q ← try evalEntry (lit.entries[i]!)[j]!
        catch e => return .declined m!"rational entry ({i}, {j}): {e.toMessageData}"
      row := q :: row
    rows := row.reverse :: rows
  return .success ⟨lit, rows.reverse⟩

def closedVector? (v : Expr) : MetaM (Option VectorLiteral) := do
  if let some lit ← vectorLiteral? v then return some lit
  let ty ← inferType v
  let .forallE _ domain carrier _ := ← whnf ty | return none
  unless carrier.isConstOf ``_root_.Rat do return none
  unless ← isDefEq v (← mkNumeral ty 0) do return none
  withLocalDeclD `i domain fun i => do
    vectorLiteral? (← mkLambdaFVars #[i] (mkApp v i))

def readVector (v : Expr) : MetaM (Outcome VecInput) := do
  if v.hasFVar || v.hasMVar then return .notApplicable
  let some lit ← closedVector? v |
    return .declined m!"expected a closed rational vector literal within the unfolding budget of {unfoldBudget}"
  unless lit.carrier.isConstOf ``_root_.Rat do return .notApplicable
  let mut entries := []
  for i in [:lit.size] do
    let q ← try evalEntry lit.entries[i]!
      catch e => return .declined m!"rational vector entry {i}: {e.toMessageData}"
    entries := q :: entries
  return .success ⟨lit, entries.reverse⟩

def inputMatrix (c : Input) : Hex.Matrix ℚ c.literal.n c.literal.m :=
  let rows := c.rows.toArray.map List.toArray
  Hex.Matrix.ofFn fun i j => (rows[i.val]!)[j.val]!

def inputVector (c : VecInput) : Vector ℚ c.literal.size :=
  let xs := c.entries.toArray
  Vector.ofFn fun i => xs[i.val]!

def truth (check : Expr) : MetaM Expr := do
  let t := mkConst ``Bool.true
  let prop ← mkEq check t
  -- Keep instance synthesis from inspecting the certificate computation.
  let inst := mkApp2 (mkConst ``Bool.decEq) check t
  return mkApp3 (mkConst ``of_decide_eq_true) prop inst (← mkEqRefl t)

def positive (n : Nat) : MetaM Expr := do
  decideProof (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit n])

/-- One synchronous kernel declaration, without a preliminary type check. -/
def checked (operation : String) (target proof : Expr) : MetaM Expr := do
  try addClosedProof target proof
  catch e => throwError "{operation}: failure: the kernel rejected the certificate: {e.toMessageData}"

def andLeft (h : Expr) : MetaM Expr := mkAppM ``And.left #[h]
def andRight (h : Expr) : MetaM Expr := mkAppM ``And.right #[h]

def identifyMatrix (A : Expr) (c : Input) (s : ScaledRows) : MetaM Expr := do
  let hA ← identification c.literal A (toExpr c.rows)
  let hs ← truth (← mkAppM ``scaleRows #[mkNatLit s.denom, toExpr c.rows, toExpr s.nums])
  mkAppM ``FieldCertificate.identify_matrix #[A, toExpr c.rows, toExpr s, hA, ← positive s.denom, hs]

def identifyVector (v : Expr) (c : VecInput) (s : Scaled) : MetaM Expr := do
  let hv ← vectorIdentification c.literal v (toExpr c.entries)
  let hs ← truth (← mkAppM ``scaleRow #[mkNatLit s.denom, toExpr c.entries, toExpr s.nums])
  mkAppM ``FieldCertificate.identify_vector #[v, toExpr c.entries, toExpr s, hv, ← positive s.denom, hs]

def matrixLiteral (n m : Nat) (s : ScaledRows) : MetaM (Expr × Expr) := do
  let rows := decodeRows s
  let A ← mkAppM ``ofLists #[mkNatLit n, mkNatLit m, toExpr rows]
  let hs ← truth (← mkAppM ``scaleRows #[mkNatLit s.denom, toExpr rows, toExpr s.nums])
  let he ← mkAppM ``FieldCertificate.identify_matrix
    #[A, toExpr rows, toExpr s, ← mkEqRefl A, ← positive s.denom, hs]
  return (A, he)

def vectorLiteral (n : Nat) (s : Scaled) : MetaM (Expr × Expr) := do
  let xs := decodeList s
  let v ← mkAppM ``vecOfList #[mkNatLit n, toExpr xs]
  let hs ← truth (← mkAppM ``scaleRow #[mkNatLit s.denom, toExpr xs, toExpr s.nums])
  let he ← mkAppM ``FieldCertificate.identify_vector
    #[v, toExpr xs, toExpr s, ← mkEqRefl v, ← positive s.denom, hs]
  return (v, he)

def inputHeights (rows : List (List _root_.Rat)) (input : ScaledRows) : List (String × Json) :=
  [("input_numerator_bits", toJson (rows.flatten.foldl (fun h q => max h (integerBits q.num)) 0)),
   ("input_denominator_bits", toJson (rows.flatten.foldl (fun h q => max h (q.den.log2 + 1)) 0)),
   ("scaled_input_numerator_bits", toJson (input.nums.flatten.foldl (fun h z => max h (integerBits z)) 0)),
   ("input_scale_bits", toJson (input.denom.log2 + 1))]

def reportInverse (c : Input) (w : Hex.Matrix.InverseWitness) : MetaM Unit := do
  let (matrices, vectors) := match w with
    | .invertible a b => ([a, b], [])
    | .singular a v _ => ([a], [v])
  reportCertificate "inverse" (reprStr (c.rows, w))
    (matrices.flatMap (·.nums.flatten) ++ vectors.flatMap (·.nums))
    (matrices.map (·.denom) ++ vectors.map (·.denom))
    (inputHeights c.rows matrices.head!)

def reportSolve (c : Input) (b : VecInput) (w : Hex.Matrix.SolveWitness) : MetaM Unit := do
  let (matrices, vectors) := match w with
    | .consistent a b d => ([a, d.reduced, d.transform, d.inverse, d.basis], [b, d.value])
    | .inconsistent a b y => ([a], [b, y])
  reportCertificate "solve" (reprStr (c.rows, b.entries, w))
    (matrices.flatMap (·.nums.flatten) ++ vectors.flatMap (·.nums))
    (matrices.map (·.denom) ++ vectors.map (·.denom))
    (inputHeights c.rows matrices.head!)

def inverseWitness (c : Input) : MetaM Hex.Matrix.InverseWitness := do
  if h : c.literal.n = c.literal.m then
    let A : Hex.Matrix ℚ c.literal.n c.literal.n := h ▸ inputMatrix c
    let w := Hex.Matrix.inverseWitness id A
    unless Hex.Matrix.checkInverseList c.literal.n c.rows w do
      throwError "inverse: failure: the producer's certificate fails its integer list check"
    if ← isTracingEnabledFor `HexMatrix.certificate then reportInverse c w
    return w
  else throwError "inverse: declined: expected a square matrix"

def solveWitness (c : Input) (b : VecInput) : MetaM Hex.Matrix.SolveWitness := do
  if h : b.literal.size = c.literal.n then
    let rhs : Vector ℚ c.literal.n := h ▸ inputVector b
    let w := Hex.Matrix.solveWitness id (inputMatrix c) rhs
    unless Hex.Matrix.checkSolveList c.literal.n c.literal.m c.rows b.entries w do
      throwError "solve: failure: the producer's certificate fails its integer list check"
    if ← isTracingEnabledFor `HexMatrix.certificate then reportSolve c b w
    return w
  else throwError "solve: declined: right-hand side length does not match the row count"

def inverseProof (A : Expr) (c : Input) (w : Hex.Matrix.InverseWitness) : MetaM Expr := do
  let hA ← identification c.literal A (toExpr c.rows)
  let hc ← truth (← mkAppM ``Hex.Matrix.checkInverseList #[mkNatLit c.literal.n, toExpr c.rows, toExpr w])
  mkAppM ``inverse_facts #[A, toExpr c.rows, toExpr w, hA, hc]

def solveProof (A b : Expr) (c : Input) (rhs : VecInput) (w : Hex.Matrix.SolveWitness) : MetaM Expr := do
  let hA ← identification c.literal A (toExpr c.rows)
  let hb ← vectorIdentification rhs.literal b (toExpr rhs.entries)
  let hc ← truth (← mkAppM ``Hex.Matrix.checkSolveList
    #[mkNatLit c.literal.n, mkNatLit c.literal.m, toExpr c.rows, toExpr rhs.entries, toExpr w])
  mkAppM ``solve_facts #[A, b, toExpr c.rows, toExpr rhs.entries, toExpr w, hA, hb, hc]

def inverseResult (A : Expr) (c : Input) (w : Hex.Matrix.InverseWitness) : MetaM Expr := do
  let h ← inverseProof A c w
  match w with
  | .invertible _ s =>
    let (B, hB) ← matrixLiteral c.literal.n c.literal.n s
    let facts ← mkAppM ``FieldCertificate.inverse_literal #[h, hB]
    let facts ← checked "inverse" (← inferType facts) facts
    mkAppM ``InverseResult.invertible
      #[B, ← andLeft facts, ← andLeft (← andRight facts), ← andRight (← andRight facts)]
  | .singular _ s _ =>
    let (v, hv) ← vectorLiteral c.literal.n s
    let facts ← mkAppM ``FieldCertificate.singular_literal #[h, hv]
    let facts ← checked "inverse" (← inferType facts) facts
    mkAppM ``InverseResult.singular #[v, ← andLeft facts, ← andLeft (← andRight facts),
      ← andLeft (← andRight (← andRight facts)), ← andRight (← andRight (← andRight facts))]

def solveResult (A b : Expr) (c : Input) (rhs : VecInput) (w : Hex.Matrix.SolveWitness) : MetaM Expr := do
  let h ← solveProof A b c rhs w
  match w with
  | .consistent _ _ d =>
    let (v, hv) ← vectorLiteral c.literal.m d.value
    let (B, hB) ← matrixLiteral c.literal.m d.nullity d.basis
    let facts ← mkAppM ``FieldCertificate.solve_literal #[h, hv, hB]
    let facts ← checked "solve" (← inferType facts) facts
    mkAppM ``SolveResult.consistent #[v, mkNatLit d.nullity, B, ← andLeft facts, ← andRight facts]
  | .inconsistent _ _ s =>
    let (y, hy) ← vectorLiteral c.literal.n s
    let facts ← mkAppM ``FieldCertificate.separator_literal #[h, hy]
    let facts ← checked "solve" (← inferType facts) facts
    mkAppM ``SolveResult.inconsistent
      #[y, ← andLeft facts, ← andLeft (← andRight facts), ← andRight (← andRight facts)]

def inverseGoal (target : Expr) : MetaM (Outcome Expr) := do
  let some (_, lhs, rhs) := target.eq? | return .notApplicable
  let isOperation (e : Expr) := e.getAppFn.isConstOf ``Inv.inv || e.getAppFn.isConstOf ``HMul.hMul
  let (op, other, reversed) ←
    if isOperation lhs then pure (lhs, rhs, false)
    else if isOperation rhs then pure (rhs, lhs, true)
    else return .notApplicable
  let product := op.getAppFn.isConstOf ``HMul.hMul
  let args := op.getAppArgs
  let A := if product then args[args.size - 2]! else args.back!
  let B := if product then args.back! else other
  let c ← match ← readMatrix A with
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .success c => pure c
  unless c.literal.n == c.literal.m do return .notApplicable
  let index := mkApp (mkConst ``Fin) (mkNatLit c.literal.n)
  let matrixType := mkApp3 (mkConst ``Matrix [Level.zero, Level.zero, Level.zero])
    index index (mkConst ``_root_.Rat)
  let canonical ← if product then
      mkAppOptM ``HMul.hMul #[some matrixType, some matrixType, some matrixType, none, some A, some B]
    else mkAppOptM ``Inv.inv #[some matrixType, none, some A]
  let instanceIndex := if product then 3 else 1
  unless ← isDefEq args[instanceIndex]! canonical.getAppArgs[instanceIndex]! do return .notApplicable
  if product then
    unless ← isDefEq other (← mkNumeral (← inferType op) 1) do return .notApplicable
  let w ← inverseWitness c
  let proof ← match w with
    | .invertible _ s =>
      let targetInput ← match ← readMatrix B with
        | .notApplicable => return .notApplicable
        | .declined msg => return .declined msg
        | .success b => pure b
      unless scaleRows s.denom targetInput.rows s.nums do
        throwError "inverse: declined: the stated inverse is false; computed inverse {decodeRows s}"
      let facts ← mkAppM ``FieldCertificate.inverse_literal
        #[← inverseProof A c w, ← identifyMatrix B targetInput s]
      if product then andLeft facts else andRight (← andRight facts)
    | .singular _ v _ =>
      if product then
        throwError "inverse: declined: certified singular matrix; nonzero kernel vector {decodeList v}"
      let zero ← mkNumeral (← inferType B) 0
      let hB ← if ← isDefEq B zero then mkEqRefl B else do
        let targetInput ← match ← readMatrix B with
          | .notApplicable => return .notApplicable
          | .declined msg => return .declined msg
          | .success b => pure b
        let s : ScaledRows := ⟨1, List.replicate c.literal.n (List.replicate c.literal.n 0)⟩
        unless scaleRows 1 targetInput.rows s.nums do
          throwError "inverse: declined: the stated inverse is false; certified singularity with kernel {decodeList v}, inverse 0"
        mkEqTrans (← identifyMatrix B targetInput s)
          (← mkAppM ``FieldCertificate.zero_matrix #[mkNatLit c.literal.n, mkNatLit c.literal.n])
      let facts ← inverseProof A c w
      let hinv ← andRight (← andRight (← andRight facts))
      mkEqTrans hinv (← mkEqSymm hB)
  let proof ← if reversed then mkEqSymm proof else pure proof
  return .success (← checked "inverse" target proof)

/-- The equation inside either an ordinary or existential solve goal. -/
structure SolveGoal where
  matrix : Expr
  rhs : Expr
  candidate : Option Expr
  reversed : Bool := false
  negative : Bool := false

def matchSolve? (target : Expr) : MetaM (Option SolveGoal) := do
  let negative := target.getAppFn.isConstOf ``Not
  let target := if negative then target.appArg! else target
  let existential := target.getAppFn.isConstOf ``Exists
  if negative && !existential then return none
  let equation ← if existential then
      match target.appArg! with
      | .lam _ _ body _ => pure body
      | _ => return none
    else pure target
  let some (_, lhs, rhs) := equation.eq? | return none
  let (op, b, reversed) ←
    if lhs.getAppFn.isConstOf ``Matrix.mulVec then pure (lhs, rhs, false)
    else if rhs.getAppFn.isConstOf ``Matrix.mulVec && !existential then pure (rhs, lhs, true)
    else return none
  let args := op.getAppArgs
  let A := args[args.size - 2]!
  let x := args.back!
  if A.hasLooseBVars || b.hasLooseBVars then return none
  if existential then
    unless x == .bvar 0 do return none
    return some ⟨A, b, none, false, negative⟩
  return some ⟨A, b, some x, reversed, false⟩

def solveGoal (target : Expr) : MetaM (Outcome Expr) := do
  let some goal ← matchSolve? target | return .notApplicable
  let A := goal.matrix
  let b := goal.rhs
  let c ← match ← readMatrix A with
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .success c => pure c
  let rhs ← match ← readVector b with
    | .notApplicable => return .notApplicable
    | .declined msg => return .declined msg
    | .success rhs => pure rhs
  if let some x := goal.candidate then
    let candidate ← match ← readVector x with
      | .notApplicable => return .notApplicable
      | .declined msg => return .declined msg
      | .success candidate => pure candidate
    if Hex.Matrix.checkSolutionList c.literal.n c.literal.m c.rows rhs.entries candidate.entries then
      if ← isTracingEnabledFor `HexMatrix.certificate then
        let input := Hex.Matrix.FieldLists.encodeRows c.rows
        let b := Hex.Matrix.FieldLists.encode rhs.entries
        let x := Hex.Matrix.FieldLists.encode candidate.entries
        reportCertificate "solve-residual" (reprStr (c.rows, rhs.entries, candidate.entries, input, b, x))
          (input.nums.flatten ++ b.nums ++ x.nums) [input.denom, b.denom, x.denom]
          (inputHeights c.rows input)
      let hA ← identification c.literal A (toExpr c.rows)
      let hb ← vectorIdentification rhs.literal b (toExpr rhs.entries)
      let hx ← vectorIdentification candidate.literal x (toExpr candidate.entries)
      let hc ← truth (← mkAppM ``Hex.Matrix.checkSolutionList #[mkNatLit c.literal.n,
        mkNatLit c.literal.m, toExpr c.rows, toExpr rhs.entries, toExpr candidate.entries])
      let h ← mkAppM ``solve_of_checkList
        #[A, b, x, toExpr c.rows, toExpr rhs.entries, toExpr candidate.entries, hA, hb, hx, hc]
      let h ← if goal.reversed then mkEqSymm h else pure h
      return .success (← checked "solve" target h)
    let w ← solveWitness c rhs
    match w with
    | .consistent _ _ d =>
      let xs := candidate.entries.toArray
      let vector : Vector ℚ c.literal.m := Vector.ofFn fun i => xs[i.val]!
      let actual := ((inputMatrix c) * vector).toList
      let residual := (actual.zip rhs.entries).map (fun (x, y) => x - y)
      throwError "solve: declined: incorrect candidate; residual {residual}; particular solution {decodeList d.value}"
    | .inconsistent _ _ y =>
      let pairing := (decodeList y |>.zip rhs.entries).foldl (fun s (x, b) => s + x * b) 0
      throwError "solve: declined: certified inconsistent system; separator {decodeList y}; yᵀA = 0, yᵀb = {pairing} ≠ 0"
  let w ← solveWitness c rhs
  let proof ← match w with
    | .consistent _ _ d =>
      if goal.negative then
        throwError "solve: declined: the system is consistent; particular solution {decodeList d.value}"
      let facts ← solveProof A b c rhs w
      let value ← mkAppM ``FieldCertificate.vector #[mkNatLit c.literal.m, toExpr d.value]
      mkAppOptM ``Exists.intro #[none, some target.appArg!, some value, some (← andLeft facts)]
    | .inconsistent _ _ y =>
      if !goal.negative then
        let pairing := (decodeList y |>.zip rhs.entries).foldl (fun s (x, b) => s + x * b) 0
        throwError "solve: declined: certified inconsistent system; separator {decodeList y}; yᵀA = 0, yᵀb = {pairing} ≠ 0"
      andRight (← andRight (← solveProof A b c rhs w))
  return .success (← checked "solve" target proof)

syntax (name := inverseTerm) "inverse% " term : term
syntax (name := solveTerm) "solve% " term:max term:max : term

@[term_elab inverseTerm] def inverseTermFallback : Term.TermElab := fun _ _ =>
  throwError "inverse: not applicable: expected a closed square rational matrix"

@[term_elab inverseTerm] def elabInverseTerm : Term.TermElab := fun stx expected => do
  let `(inverse% $t) := stx | throwUnsupportedSyntax
  let A ← elabArgument t (mkConst ``_root_.Rat)
  match ← readMatrix A with
  | .notApplicable => throwUnsupportedSyntax
  | .declined msg => throwError "inverse: declined: {msg}"
  | .success c => Term.ensureHasType expected (← inverseResult A c (← inverseWitness c))

@[term_elab solveTerm] def solveTermFallback : Term.TermElab := fun _ _ =>
  throwError "solve: not applicable: expected a closed rational matrix and vector"

@[term_elab solveTerm] def elabSolveTerm : Term.TermElab := fun stx expected => do
  let `(solve% $t $v) := stx | throwUnsupportedSyntax
  let A ← elabArgument t (mkConst ``_root_.Rat)
  let c ← match ← readMatrix A with
    | .notApplicable => throwUnsupportedSyntax
    | .declined msg => throwError "solve: declined: {msg}"
    | .success c => pure c
  let vectorType ← mkArrow (mkApp (mkConst ``Fin) (mkNatLit c.literal.n)) (mkConst ``_root_.Rat)
  let b ← Term.elabTerm v (some vectorType)
  Term.synthesizeSyntheticMVarsNoPostponing
  let b ← instantiateMVars b
  match ← readVector b with
  | .notApplicable => throwUnsupportedSyntax
  | .declined msg => throwError "solve: declined: {msg}"
  | .success rhs => Term.ensureHasType expected (← solveResult A b c rhs (← solveWitness c rhs))

syntax (name := inverseTac) &"inverse" : tactic
syntax (name := solveTac) &"solve" : tactic

@[tactic inverseTac, no_fallback] def inverseFallback : Tactic.Tactic := fun _ =>
  throwError "inverse: not applicable: expected A * B = 1 or A⁻¹ = B over ℚ, in either orientation"

@[tactic inverseTac, no_fallback] def evalInverse : Tactic.Tactic := fun _ => Tactic.withMainContext do
  match ← inverseGoal (← Tactic.getMainTarget) with
  | .notApplicable => throwUnsupportedSyntax
  | .declined msg => throwError "inverse: declined: {msg}"
  | .success proof => Tactic.closeMainGoal `inverse proof

@[tactic solveTac, no_fallback] def solveFallback : Tactic.Tactic := fun _ =>
  throwError "solve: not applicable: expected a rational mulVec equation, existence, or nonexistence"

@[tactic solveTac, no_fallback] def evalSolve : Tactic.Tactic := fun _ => Tactic.withMainContext do
  match ← solveGoal (← Tactic.getMainTarget) with
  | .notApplicable => throwUnsupportedSyntax
  | .declined msg => throwError "solve: declined: {msg}"
  | .success proof => Tactic.closeMainGoal `solve proof

end HexRowReduceMathlib.Tactic
