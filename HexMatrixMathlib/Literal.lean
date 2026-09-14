/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Data.Fin.VecNotation
public meta import Mathlib.Tactic.Echelon.Rat
public meta import Lean

public section

/-!
The Mathlib matrix literal layer shared by the matrix tactics (`rank`, `det`,
`char_poly`): a row list as a Mathlib matrix, the two ways a closed literal
is identified with its row list, and the recognition of the four literal
syntaxes.

`ofLists n m L` is the Mathlib matrix of a row list, built so that a literal
`!![…]` or `Matrix.of ![…]` is definitionally `ofLists n m [[…], …]` after
unfolding, one step per entry; a tactic discharges that identification by
`rfl` and the kernel never evaluates an entry through `Matrix.of`/`vecCons`
inside a certificate's arithmetic.  This costs about `6 ms` at `16 × 16`.

A `fun i j => …` or `Matrix.ofArray xs h` literal is not a `vecCons` chain,
so it is identified with its row list by one kernel `decide` on the
entrywise comparison `entriesEq`, which evaluates `A i j` for every index
pair; this costs about `200 ms` at `16 × 16`, and is the fallback route.

The meta section recognizes a closed literal behind definitions, returns its
shape, carrier and entry expressions with the identification route, and
quotes row lists and the identification proof.
-/

open Matrix

namespace HexMatrixMathlib

/-! # `List.getD` -/

theorem getD_eq_getElem' {α : Type*} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_eq_default' {α : Type*} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-! # Row lists as Mathlib matrices -/

/-- A list as a vector, padded with zeros; `vecOfList (k + 1) (a :: l)` unfolds
to `vecCons a (vecOfList k l)`, so a `![…]` literal is definitionally
`vecOfList` of its entries. -/
@[expose] def vecOfList {α : Type*} [Zero α] : (k : Nat) → List α → (Fin k → α)
  | 0, _ => ![]
  | k + 1, a :: l => Matrix.vecCons a (vecOfList k l)
  | _ + 1, [] => fun _ => 0

/-- The Mathlib matrix of a row list, padded with zeros. -/
@[expose] def ofLists {α : Type*} [Zero α] (n m : Nat) (L : List (List α)) :
    Matrix (Fin n) (Fin m) α :=
  Matrix.of (vecOfList n (L.map (vecOfList m)))

theorem vecOfList_apply {α : Type*} [Zero α] (k : Nat) (l : List α) (i : Fin k) :
    vecOfList k l i = l.getD i 0 := by
  induction k generalizing l with
  | zero => exact i.elim0
  | succ k ih =>
    cases l with
    | nil => simp [vecOfList]
    | cons a l =>
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [vecOfList]
      · simp [vecOfList, ih]

theorem ofLists_apply {α : Type*} [Zero α] (n m : Nat) (L : List (List α)) (i : Fin n)
    (j : Fin m) : ofLists n m L i j = (L.getD i []).getD j 0 := by
  rw [ofLists, Matrix.of_apply, vecOfList_apply]
  by_cases hi : (i : Nat) < L.length
  · rw [getD_eq_getElem' _ _ _ (by simpa using hi), List.getElem_map, vecOfList_apply,
      getD_eq_getElem' _ _ _ hi]
  · have h1 : (L.map (vecOfList m)).getD i 0 = 0 := getD_eq_default' _ _ _ (by simpa using hi)
    have h2 : L.getD i [] = [] := getD_eq_default' _ _ _ (by omega)
    rw [h1, h2]
    rfl

/-! # Entrywise identification -/

/-- The entrywise comparison of a matrix with its row list, as a Boolean the
kernel evaluates by enumerating every index pair. -/
@[expose] def entriesEq {α : Type*} [Zero α] [DecidableEq α] (n m : Nat)
    (A : Matrix (Fin n) (Fin m) α) (L : List (List α)) : Bool :=
  (List.finRange n).all fun i => (List.finRange m).all fun j => decide (A i j = ofLists n m L i j)

/-- A passing entrywise comparison identifies the matrix with its row list. -/
theorem eq_ofLists_of_entriesEq {α : Type*} [Zero α] [DecidableEq α] (n m : Nat)
    (A : Matrix (Fin n) (Fin m) α) (L : List (List α)) (h : entriesEq n m A L = true) :
    A = ofLists n m L := by
  ext i j
  have h := List.all_eq_true.mp h i (List.mem_finRange i)
  have h := List.all_eq_true.mp h j (List.mem_finRange j)
  exact of_decide_eq_true h

/-- Compare a closed vector with the list used by a certificate. -/
@[expose] def vectorEntriesEq {α : Type*} [Zero α] [DecidableEq α] (n : Nat)
    (v : Fin n → α) (xs : List α) : Bool :=
  (List.finRange n).all fun i => decide (v i = vecOfList n xs i)

/-- The entrywise identification route for closed vector functions. -/
theorem eq_vecOfList_of_entriesEq {α : Type*} [Zero α] [DecidableEq α] (n : Nat)
    (v : Fin n → α) (xs : List α) (h : vectorEntriesEq n v xs = true) :
    v = vecOfList n xs := by
  funext i
  exact of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

/-! # Certified values -/

/-- The record returned by the result-producing term forms (`det% A`): the
value of `f a` and the proof. -/
structure Certified {α : Type*} {β : Type*} (f : α → β) (a : α) where
  /-- The computed value. -/
  value : β
  /-- The certificate that it is `f a`. -/
  proof : f a = value

/-- Configuration shared by the matrix tactics `rank` and `det`, in the
style of `decide +kernel`: `rank -packing`, `det -packing`. -/
structure KernelConfig where
  /-- Evaluate the certificate's dot products on Kronecker-packed rows (one
  multiplication, shift and mask per dot product in the kernel) instead of
  term by term.  The certificate is the same; the packed checker is proven
  equal to the plain one under a bound the kernel verifies. -/
  packing : Bool := true

end HexMatrixMathlib

end

public meta section

namespace HexMatrixMathlib.Literal

/-- Elaborate the `optConfig` of a matrix tactic into a `KernelConfig`. -/
declare_config_elab elabKernelConfig KernelConfig

open Lean Meta Elab

initialize registerTraceClass `HexMatrix.certificate

/-- Bit length of a signed certificate scalar, excluding its sign. -/
def integerBits (z : Int) : Nat := if z == 0 then 0 else z.natAbs.log2 + 1

/-- Optional certificate measurements for the external proof-probe runner.
No clock is read here; kernel time comes from Lean's external profiler. -/
def reportCertificate (tactic : String) (serialized : String) (integers : List Int)
    (denominators : List Nat := []) (extra : List (String × Json) := []) : MetaM Unit := do
  let payload := Json.mkObj (
    [("tactic", toJson tactic), ("integer_entries", toJson integers.length),
      ("denominator_entries", toJson denominators.length),
      ("serialized_bytes", toJson serialized.utf8ByteSize),
      ("max_numerator_bits", toJson (integers.foldl (fun b z => max b (integerBits z)) 0)),
      ("max_denominator_bits", toJson (denominators.foldl
        (fun b d => max b (if d == 0 then 0 else d.log2 + 1)) 0))] ++ extra)
  trace[HexMatrix.certificate] "{payload.compress}"

/-- How a recognized literal is identified with its row list. -/
inductive Route where
  /-- A `Matrix.of` vector chain (`!![…]`, `Matrix.of ![…]`): `A = ofLists n m L` is `rfl`. -/
  | chain
  /-- A `fun i j => …` or `Matrix.ofArray xs h` literal: `A = ofLists n m L` by one kernel
  `decide` on `entriesEq`. -/
  | entrywise
  deriving Repr, DecidableEq

/-- A recognized closed matrix literal. -/
structure Recognized where
  /-- Rows. -/
  n : Nat
  /-- Columns. -/
  m : Nat
  /-- The entry carrier. -/
  carrier : Expr
  /-- The entry expressions, row-major, as they appear in the literal (or, for
  the `fun` and `ofArray` forms, as instantiated at each index pair). -/
  entries : Array (Array Expr)
  /-- The identification route. -/
  route : Route

/-- How many definitions are unfolded when looking for a literal. -/
def unfoldBudget : Nat := 8

/-- The shape of the type `Matrix (Fin n) (Fin m) R` with closed dimensions:
`(n, m, R)`, or of the function type `Fin n → Fin m → R` a bare lambda has.
The dimensions may be any closed expressions that evaluate to numerals, as
`Matrix.of ![…]` elaborates them as `Nat.succ` chains. -/
def shape? (ty : Expr) : MetaM (Option (Nat × Nat × Expr)) := do
  let (finN, finM, R) ← match ← whnfR ty with
    | .app (.app (.app (.const ``Matrix _) finN) finM) R => pure (finN, finM, R)
    | .forallE _ finN (.forallE _ finM R _) _ =>
        if R.hasLooseBVars then return none else pure (finN, finM, R)
    | _ => return none
  let_expr Fin nE := ← whnfR finN | return none
  let_expr Fin mE := ← whnfR finM | return none
  let some n ← (Meta.evalNat nE).run | return none
  let some m ← (Meta.evalNat mE).run | return none
  return some (n, m, R)

/-- Match a `Matrix.of ![…]` chain (the `!![…]` notation included) of the given
shape.  Like Mathlib's `matchMatrixLit?`, but every `vecCons` chain must end in
`vecEmpty`, so that the literal is definitionally the `ofLists` of its
entries. -/
def matchChain? (n m : Nat) (A : Expr) : MetaM (Option (Array (Array Expr))) := do
  let_expr DFunLike.coe _ _ _ _ f v := A | return none
  let_expr Matrix.of _ _ _ := f | return none
  let (rows, _, tail) ← Matrix.matchVecConsPrefix (mkNatLit n) v
  unless rows.length == n && tail.getAppFn.isConstOf ``Matrix.vecEmpty do return none
  let mut entries := #[]
  for row in rows do
    let (es, _, tail) ← Matrix.matchVecConsPrefix (mkNatLit m) row
    unless es.length == m && tail.getAppFn.isConstOf ``Matrix.vecEmpty do return none
    entries := entries.push es.toArray
  return some entries

/-- `⟨k, _⟩ : Fin n`. -/
def finLit (n k : Nat) : MetaM Expr := do
  let lt ← mkAppM ``LT.lt #[mkNatLit k, mkNatLit n]
  return mkApp3 (mkConst ``Fin.mk) (mkNatLit n) (mkNatLit k) (← mkDecideProof lt)

/-- Match a `fun i j => …` literal: the body instantiated at every index pair. -/
def matchFn? (n m : Nat) (A : Expr) : MetaM (Option (Array (Array Expr))) := do
  let .lam _ _ (.lam ..) _ := A | return none
  let rows ← (List.range n).toArray.mapM fun i => do
    let iE ← finLit n i
    (List.range m).toArray.mapM fun j => do
      let jE ← finLit m j
      return (mkApp2 A iE jE).headBeta
  return some rows

/-- Match a `Matrix.ofArray xs h` literal whose array is a `#[…]` literal of
`n * m` entries. -/
def matchOfArray? (n m : Nat) (A : Expr) : MetaM (Option (Array (Array Expr))) := do
  let_expr Matrix.ofArray _ _ _ xs _ := A | return none
  let some (_, es) := xs.listLit? <|> (do
      let_expr List.toArray _ l := xs | none
      l.listLit?) | return none
  unless es.length == n * m do return none
  let es := es.toArray
  return some ((List.range n).toArray.map fun i => (List.range m).toArray.map fun j => es[i * m + j]!)

/-- Find the literal behind `A : Matrix (Fin n) (Fin m) R`, unfolding definitions
within `unfoldBudget`. Symbolic consumers may enable open entries. -/
partial def matchLiteral? (n m : Nat) (R : Expr) (A : Expr) (budget : Nat := unfoldBudget) (allowOpen : Bool := false) :
    MetaM (Option Recognized) := do
  if (!allowOpen && A.hasFVar) || A.hasMVar then return none
  if let some es ← matchChain? n m A then return some ⟨n, m, R, es, .chain⟩
  if let some es ← matchFn? n m A then return some ⟨n, m, R, es, .entrywise⟩
  if let some es ← matchOfArray? n m A then return some ⟨n, m, R, es, .entrywise⟩
  if budget = 0 then return none
  match ← unfoldDefinition? A with
  | some A' => matchLiteral? n m R A' (budget - 1) allowOpen
  | none => return none

/-- Recognize a matrix literal, requiring closed entries unless explicitly enabled. -/
def literal? (A : Expr) (allowOpen : Bool := false) : MetaM (Option Recognized) := do
  let A ← instantiateMVars A
  let some (n, m, R) ← shape? (← inferType A) | return none
  matchLiteral? n m (← whnfR R) A (allowOpen := allowOpen)

/-- Evaluate an entry to a rational with `norm_num`; an entry `norm_num` alone
does not evaluate (the `fun i j => …` form instantiates its body at `Fin`
literals, leaving `Fin.val`, casts and `if i = j` tests) is first simplified
with the default simp set.  An entry that is not a closed numeric expression
is an error naming it. -/
def evalEntry (e : Expr) : MetaM Rat := do
  try Mathlib.Tactic.Echelon.evalRatEntry true e
  catch _ =>
    let ctx ← Simp.mkContext (config := { decide := true })
      (simpTheorems := #[← getSimpTheorems]) (congrTheorems := ← getSimpCongrTheorems)
    let r ← Mathlib.Meta.NormNum.deriveSimp ctx true e
    Mathlib.Tactic.Echelon.evalRatEntry true r.expr

/-- Evaluate every entry to a rational. -/
def evalEntries (lit : Recognized) : MetaM (Array (Array Rat)) :=
  lit.entries.mapM (·.mapM evalEntry)

/-- The row list of quoted entries, as a `List (List type)`. -/
def rowList (type : Expr) (rows : Array (Array Expr)) : MetaM Expr := do
  let rows ← rows.toList.mapM fun row => mkListLit type row.toList
  mkListLit (mkApp (mkConst ``List [Level.zero]) type) rows

/-- `of_decide_eq_true` on a closed decidable proposition, for the kernel to
evaluate; no elaborator-side evaluation happens. -/
def decideProof (prop : Expr) : MetaM Expr := do
  let d ← mkDecide prop
  return mkApp3 (mkConst ``of_decide_eq_true) prop d.appArg! (← mkEqRefl (mkConst ``Bool.true))

/-- Add the closed proof `proof : target` as an auxiliary lemma, checked by
the kernel synchronously and exactly once, and return the constant.  This
is the declaration-checking path `decide +kernel` uses (`mkAuxLemma`),
without reuse of an earlier lemma for the same statement, so every
supplied proof is checked.  `mkAuxTheorem` is not used: with its default
`zetaDelta := false` its closure step type-checks the proof in the
elaborator (`Meta.check`) before the kernel does, which evaluates the
certificate a second time.  The target and the proof must be closed, with
no free variables and no expression or universe metavariables; the
universe parameters are the level parameters they mention. -/
def addClosedProof (target proof : Expr) : MetaM Expr := do
  if target.hasFVar || target.hasMVar || proof.hasFVar || proof.hasMVar then
    throwError "the target and the proof must be closed{indentExpr target}"
  let levels := (collectLevelParams (collectLevelParams {} target) proof).params.toList
  let name ← withOptions (Lean.Elab.async.set · false) do
    mkAuxLemma levels target proof (cache := false)
  return mkConst name (levels.map Level.param)

/-- The proof of `A = ofLists n m L` along the literal's route: `rfl` for a
vector chain, one kernel `decide` on `entriesEq` otherwise. -/
def identification (lit : Recognized) (A L : Expr) : MetaM Expr := do
  let ofL ← mkAppM ``HexMatrixMathlib.ofLists #[mkNatLit lit.n, mkNatLit lit.m, L]
  match lit.route with
  | .chain => mkExpectedTypeHint (← mkEqRefl A) (← mkEq A ofL)
  | .entrywise =>
      let check ← mkEq (← mkAppM ``HexMatrixMathlib.entriesEq #[mkNatLit lit.n, mkNatLit lit.m, A, L])
        (mkConst ``Bool.true)
      mkAppM ``HexMatrixMathlib.eq_ofLists_of_entriesEq
        #[mkNatLit lit.n, mkNatLit lit.m, A, L, ← decideProof check]

/-- Elaborate a matrix argument with the frontend's carrier expectation.
Integer frontends use the default; field frontends supply their field so
unannotated numerals and fractions elaborate in that carrier. -/
def elabArgument (t : Syntax) (carrier : Expr := mkConst ``Int) : Term.TermElabM Expr := do
  let e ←
    if t.getKind == ``Matrix.matrixNotation ||
        t.getKind == ``Matrix.matrixNotationRx0 ||
        t.getKind == ``Matrix.matrixNotation0xC then
      let n ← mkFreshExprMVar (mkConst ``Nat)
      let m ← mkFreshExprMVar (mkConst ``Nat)
      let fin (k : Expr) := mkApp (mkConst ``Fin) k
      let expected := mkApp3 (mkConst ``Matrix [Level.zero, Level.zero, Level.zero])
        (fin n) (fin m) carrier
      Term.elabTerm t (some expected)
    else
      Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- A closed vector literal, including a stated invariant-factor function. -/
structure VectorLiteral where
  size : Nat
  carrier : Expr
  entries : Array Expr
  route : Route

/-- Recognize vector notation or a closed lambda behind bounded unfolding. -/
partial def matchVector? (n : Nat) (carrier v : Expr)
    (budget : Nat := unfoldBudget) : MetaM (Option VectorLiteral) := do
  if v.hasFVar || v.hasMVar then return none
  let (entries, _, tail) ← Matrix.matchVecConsPrefix (mkNatLit n) v
  if entries.length == n && tail.getAppFn.isConstOf ``Matrix.vecEmpty then
    return some ⟨n, carrier, entries.toArray, .chain⟩
  if v.isLambda then
    let entries ← (List.range n).toArray.mapM fun i => do
      return (mkApp v (← finLit n i)).headBeta
    return some ⟨n, carrier, entries, .entrywise⟩
  if budget == 0 then return none
  match ← unfoldDefinition? v with
  | some v' => matchVector? n carrier v' (budget - 1)
  | none => return none

/-- Recognize a closed vector from its function type. -/
def vectorLiteral? (v : Expr) : MetaM (Option VectorLiteral) := do
  let v ← instantiateMVars v
  let .forallE _ domain carrier _ := ← whnf (← inferType v) | return none
  if carrier.hasLooseBVars then return none
  let_expr Fin n := ← whnfR domain | return none
  let some n ← (Meta.evalNat n).run | return none
  matchVector? n (← whnfR carrier) v

/-- Identify a vector with its quoted list along the recognized route. -/
def vectorIdentification (lit : VectorLiteral) (v xs : Expr) : MetaM Expr := do
  let n := mkNatLit lit.size
  match lit.route with
  | .chain =>
      let rhs ← mkAppM ``HexMatrixMathlib.vecOfList #[n, xs]
      mkExpectedTypeHint (← mkEqRefl v) (← mkEq v rhs)
  | .entrywise =>
      let check ← mkEq (← mkAppM ``HexMatrixMathlib.vectorEntriesEq #[n, v, xs])
        (mkConst ``Bool.true)
      mkAppM ``HexMatrixMathlib.eq_vecOfList_of_entriesEq #[n, v, xs, ← decideProof check]

end HexMatrixMathlib.Literal
