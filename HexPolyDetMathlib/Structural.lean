/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDetMathlib.Small
public import Mathlib.LinearAlgebra.Matrix.Block
public meta import HexPolyDetMathlib.Small
public meta import Mathlib.Tactic.Ring

public section
namespace HexPolyDetMathlib.Structural
open HexMatrixMathlib HexMatrixMathlib.DetPoly.Polynomial

/-- The operations used by the structural identities, tied to their ring instance. -/
@[expose] def ringOps {R : Type u} [CommRing R] (a b : R) (n : Nat) : List R :=
  [0, 1, a+b, a*b, a-b, -a, a^n]

@[expose] def product {R : Type u} [Mul R] [One R] : List R → R
  | [] => 1
  | a :: as => as.foldl (· * ·) a

private theorem prod_vec {R : Type u} [CommRing R] (f : List R) :
    (∏ i : Fin f.length, vecOfList f.length f i) = product f := by
  have h : (∏ i : Fin f.length, vecOfList f.length f i) = f.prod := by
    induction f with
    | nil => simp
    | cons a f ih => simpa [Fin.prod_univ_succ, vecOfList] using congrArg (a * ·) ih
  rw [h, List.prod_eq_foldl]
  cases f with
  | nil => rfl
  | cons a f => simp [product]

private theorem sum_vec {R : Type u} [CommRing R] (f : List R) :
    (∑ i : Fin f.length, vecOfList f.length f i) = f.sum := by
  induction f with
  | nil => simp
  | cons a f ih => simpa [Fin.sum_univ_succ, vecOfList] using congrArg (a + ·) ih

/-- Finite entry hints avoid a decidable equality on the carrier. -/
theorem triangular {R : Type u} [CommRing R] (n : Nat)
    (A : Matrix (Fin n) (Fin n) R) (f : List R) (upper : Bool)
    (hlen : f.length = n)
    (hd : AllFin n (fun i => A i i = vecOfList n f i))
    (hz : AllFin n (fun i => AllFin n (fun j =>
      if (if upper then j < i else i < j) then A i j = 0 else True))) :
    A.det = product f := by
  subst n
  have hdet : A.det = ∏ i, A i i := by
    cases upper with
    | false =>
      apply Matrix.det_of_isLowerTriangular
      intro i j hij
      change i < j at hij
      simpa [hij] using allFin _ _ (allFin _ _ hz i) j
    | true =>
      apply Matrix.det_of_isUpperTriangular
      intro i j hij
      change j < i at hij
      simpa [hij] using allFin _ _ (allFin _ _ hz i) j
  rw [hdet, ← prod_vec]
  exact Finset.prod_congr rfl fun i _ => allFin _ _ hd i

theorem zeroRow {R : Type u} [CommRing R] (n : Nat)
    (A : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (h : AllFin n (fun j => A i j = 0)) : A.det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero i (allFin _ _ h)

theorem zeroColumn {R : Type u} [CommRing R] (n : Nat)
    (A : Matrix (Fin n) (Fin n) R) (j : Fin n)
    (h : AllFin n (fun i => A i j = 0)) : A.det = 0 :=
  Matrix.det_eq_zero_of_column_eq_zero j (allFin _ _ h)

/-- Cofactor values are supplied only for the selected expansion. -/
theorem cofactor {R : Type u} [CommRing R] (n : Nat)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (i : Fin (n+1)) (v : List R)
    (hlen : v.length = n+1)
    (h : AllFin (n+1) (fun j =>
      (-1 : R) ^ (i.val + j.val) * A i j *
        (A.submatrix i.succAbove j.succAbove).det = vecOfList (n+1) v j)) :
    A.det = v.sum := by
  rw [Matrix.det_succ_row A i]
  have hv : (∑ j : Fin (n+1), vecOfList (n+1) v j) = v.sum := by
    rw [← hlen]
    exact sum_vec v
  rw [← hv]
  exact Finset.sum_congr rfl fun j _ => allFin _ _ h j

/-- Factored four-dimensional formula, for terminal sparse minors only. -/
theorem four {R : Type u} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0*(A 1 1*(A 2 2*A 3 3-A 2 3*A 3 2) - A 1 2*(A 2 1*A 3 3-A 2 3*A 3 1) + A 1 3*(A 2 1*A 3 2-A 2 2*A 3 1)) -
      A 0 1*(A 1 0*(A 2 2*A 3 3-A 2 3*A 3 2) - A 1 2*(A 2 0*A 3 3-A 2 3*A 3 0) + A 1 3*(A 2 0*A 3 2-A 2 2*A 3 0)) +
      A 0 2*(A 1 0*(A 2 1*A 3 3-A 2 3*A 3 1) - A 1 1*(A 2 0*A 3 3-A 2 3*A 3 0) + A 1 3*(A 2 0*A 3 1-A 2 1*A 3 0)) -
      A 0 3*(A 1 0*(A 2 1*A 3 2-A 2 2*A 3 1) - A 1 1*(A 2 0*A 3 2-A 2 2*A 3 0) + A 1 2*(A 2 0*A 3 1-A 2 1*A 3 0)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring
theorem cofactorEntry {R : Type u} [CommRing R] (s a d v : R) (h : d = v) :
    s * a * d = s * a * v := congrArg (s * a * ·) h

theorem cofactorZero {R : Type u} [CommRing R] (s d : R) : s * 0 * d = 0 := by simp

end HexPolyDetMathlib.Structural

public meta section
namespace HexPolyDetMathlib.Structural
open Lean Meta HexMatrixMathlib HexMatrixMathlib.Literal
open HexMatrixMathlib.DetPoly.Frontend

private def matrixExpr (carrier : Expr) (es : Array (Array Expr)) : MetaM Expr := do
  let rows ← es.toList.mapM fun row => mkListLit carrier row.toList
  let rows ← mkListLit (← mkAppM ``List #[carrier]) rows
  mkAppM ``ofLists #[toExpr es.size, toExpr es.size, rows]

private def resultOf (proof : Expr) : MetaM Result := do
  let some (_, _, value) := (← inferType proof).eq? | throwError "det: invalid structural equality"
  return {value, proof}

private def zeros (carrier : Expr) (es : Array (Array Expr)) : MetaM (Array (Array Bool)) := do
  let zero ← mkNumeral carrier 0
  es.mapM fun row => row.mapM fun e => withTransparency .reducible (isDefEq e zero)

private def finalize? (A : Expr) (r : Result) (route : String) (cfg : Hex.Reflect.Config) : MetaM (Option Result) := do
  let target ← mkEq (← mkAppM ``Matrix.det #[A]) r.value
  let out ← Hex.Reflect.run (Hex.Reflect.withOutcome do
    checkedBudgeted target (mkExpectedPropHint r.proof target)) cfg
  match out with
  | .success (proof, nodes) _ =>
    trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson route),
      ("proof_node_budget", toJson nodes)]).compress}"
    return some {r with proof}
  | .failure error => throwError error.toMessageData
  | _ => return none

private def admitted (A : Expr) (lit : Recognized) : MetaM Bool := do
  unless !A.hasExprMVar && lit.n ≤ maxDimension &&
      HexMatrixMathlib.DetPoly.Certificate.arm (← getOptions) == .automatic &&
      Hex.Reflect.proofNodeCount #[A] 100001 ≤ 100000 do return false
  let some u := (← getLevel lit.carrier).dec | return false
  let .some ring ← trySynthInstance (← mkAppM ``CommRing #[lit.carrier]) | return false
  withLocalDeclD `a lit.carrier fun a => withLocalDeclD `b lit.carrier fun b =>
    withLocalDeclD `n (mkConst ``Nat) fun n => do
      let actual ← mkListLit lit.carrier [← mkNumeral lit.carrier 0, ← mkNumeral lit.carrier 1,
        ← mkAppM ``HAdd.hAdd #[a,b], ← mkAppM ``HMul.hMul #[a,b],
        ← mkAppM ``HSub.hSub #[a,b], ← mkAppM ``Neg.neg #[a], ← mkAppM ``HPow.hPow #[a,n]]
      let expected := mkAppN (mkConst ``ringOps [u]) #[lit.carrier, ring, a, b, n]
      withTransparency .default (isDefEq actual expected)

/-- Direct triangular and zero identities, without polynomial normalization. -/
def direct? (A : Expr) (lit : Recognized) (cfg : Hex.Reflect.Config := {}) : MetaM (Option Result) := do
  unless ← admitted A lit do return none
  if lit.n == 0 then return none
  let saved ← saveState
  let result ← withLetDecl `detInput (← inferType A) A fun A => do
    let es ← lit.entries.mapM (·.mapM reduceIndices)
    let zs ← zeros lit.carrier es
    let some u := (← getLevel lit.carrier).dec | return none
    let .some ring ← trySynthInstance (← mkAppM ``CommRing #[lit.carrier]) | return none
    for column in [false, true] do
      for i in [:lit.n] do
        if (List.range lit.n).all (fun j => if column then (zs[j]!)[i]! else (zs[i]!)[j]!) then
          let head := mkAppN (mkConst (if column then ``zeroColumn else ``zeroRow) [u])
            #[lit.carrier, ring, toExpr lit.n, A, ← finLit lit.n i]
          let .forallE _ expected _ _ ← inferType head | return none
          let hints ← (List.range lit.n).mapM fun j => mkEqRefl (if column then (es[j]!)[i]! else (es[i]!)[j]!)
          let proof := mkApp head (← allFinHints expected hints)
          return ← finalize? A (← resultOf proof) "zero" cfg
    for upper in [true, false] do
      let triangularShape :=  (List.range lit.n).all fun i => (List.range lit.n).all fun j =>
        !(if upper then j < i else i < j) || (zs[i]!)[j]!
      if triangularShape then
        let diagonal := es.mapIdx fun i row => row[i]!
        let fs ← mkListLit lit.carrier diagonal.toList
        let hlen ← mkEqRefl (toExpr lit.n)
        let head := mkAppN (mkConst ``triangular [u])
          #[lit.carrier, ring, toExpr lit.n, A, fs, toExpr upper, hlen]
        let .forallE _ expected _ _ ← inferType head | return none
        let hd ← allFinHints expected (← diagonal.toList.mapM mkEqRefl)
        let head := mkApp head hd
        let hints ← es.mapIdxM fun i row => row.mapIdxM fun j e =>
          if (if upper then j < i else i < j) then mkEqRefl e else pure (mkConst ``True.intro)
        let proof ← applyEntryHints head hints
        -- Quote a left-associated diagonal product, omitting a leading one.
        let mut value := diagonal[0]!
        for e in diagonal[1:] do value ← mkAppM ``HMul.hMul #[value, e]
        return ← finalize? A {value, proof} "triangular" cfg
    return none
  if result.isNone then saved.restore
  return result

/-- A preflight tree contains only the minors actually chosen for expansion. -/
inductive Expansion where
  | leaf
  | row (transpose : Bool) (index : Nat) (children : Array (Option Expansion))
  deriving Inhabited

partial def plan? (zs : Array (Array Bool)) (terminal : Bool)
    (remaining : Nat) : Option (Expansion × Nat) := do
  let n := zs.size
  if terminal && n ≤ 4 then
    let leaves := n.factorial
    if leaves > remaining then none else some (.leaf, remaining-leaves)
  else
    let mut best := n+1
    let mut column := false
    let mut index := 0
    for col in [false, true] do
      for i in [:n] do
        let count := (List.range n).countP fun j => !(if col then (zs[j]!)[i]! else (zs[i]!)[j]!)
        if count < best then
          best := count
          column := col
          index := i
    if best > 2 then failure
    let zs := if column then (List.range n).toArray.map (fun j => zs.map (·[j]!)) else zs
    let mut children := #[]
    let mut left := remaining
    for j in [:n] do
      if (zs[index]!)[j]! then children := children.push none
      else
        let minor := (zs.eraseIdxIfInBounds index).map (·.eraseIdxIfInBounds j)
        let (child, rest) ← plan? minor true left
        left := rest
        children := children.push (some child)
    return (.row column index children, left)

private def mul (a b : Expr) : MetaM Expr := mkAppM ``HMul.hMul #[a, b]
private def sub (a b : Expr) : MetaM Expr := mkAppM ``HSub.hSub #[a, b]
private def add (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a, b]

private def formula3 (es : Array (Array Expr)) : MetaM Expr := do
  let pair (i j : Nat) := do sub (← mul (es[1]!)[i]! (es[2]!)[j]!) (← mul (es[1]!)[j]! (es[2]!)[i]!)
  add (← sub (← mul (es[0]!)[0]! (← pair 1 2)) (← mul (es[0]!)[1]! (← pair 0 2)))
    (← mul (es[0]!)[2]! (← pair 0 1))

private def formula4 (es : Array (Array Expr)) : MetaM Expr := do
  let terms ← (List.range 4).toArray.mapM fun j => do
    mul (es[0]!)[j]! (← formula3 ((es.eraseIdxIfInBounds 0).map (·.eraseIdxIfInBounds j)))
  sub (← add (← sub terms[0]! terms[1]!) terms[2]!) terms[3]!

/-- Reindexing literal rows is extensional, not generally definitional. -/
private def identify (A B : Expr) (es : Array (Array Expr)) : MetaM Expr := do
  let hints ← es.mapM (·.mapM mkEqRefl)
  applyEntryHints (← mkAppM ``HexMatrixMathlib.DetPoly.Polynomial.identify #[A, B]) hints

private def transport (A h proof : Expr) : MetaM Expr := do
  let determinant := (← mkAppM ``Matrix.det #[A]).appFn!
  mkEqTrans (← mkCongrArg determinant h) proof

private initialize budgetException : InternalExceptionId ←
  registerInternalExceptionId `HexPolyDetMathlib.Structural.budget

private partial def assemble (carrier : Expr) (es : Array (Array Expr))
    (tree : Expansion) (cfg : Hex.Reflect.Config) : MetaM Result := do
  let n := es.size
  let A ← matrixExpr carrier es
  let result ← match tree with
  | .leaf =>
    if n == 4 then do
      return { proof := ← mkAppM ``four #[A], value := ← formula4 es }
    else Small.build A {n, m := n, carrier, entries := es, route := .chain}
  | .row transpose i children => do
    let rows := if transpose then (List.range n).toArray.map (fun j => es.map (·[j]!)) else es
    let B ← matrixExpr carrier rows
    let iE ← finLit n i
    let rowFn ← mkAppM ``Fin.succAbove #[iE]
    let minus ← mkAppM ``Neg.neg #[← mkNumeral carrier 1]
    let mut values := #[]
    let mut proofs := #[]
    for j in [:n] do
      let jE ← finLit n j
      let minor ← mkAppM ``Matrix.submatrix #[B, rowFn, ← mkAppM ``Fin.succAbove #[jE]]
      let d ← mkAppM ``Matrix.det #[minor]
      let s ← mkAppM ``HPow.hPow #[minus, toExpr (i+j)]
      match children[j]! with
      | none =>
        let h ← mkAppM ``cofactorZero #[s, d]
        values := values.push (← mkNumeral carrier 0)
        proofs := proofs.push h
      | some child =>
        let r ← assemble carrier ((rows.eraseIdxIfInBounds i).map (·.eraseIdxIfInBounds j)) child cfg
        let minorEntries := (rows.eraseIdxIfInBounds i).map (·.eraseIdxIfInBounds j)
        let C ← matrixExpr carrier minorEntries
        let hd ← transport minor (← identify minor C minorEntries) r.proof
        let head ← mkAppM ``cofactorEntry #[s, (rows[i]!)[j]!, d, r.value]
        let h ← applyHint head hd
        values := values.push (← mkAppM ``HMul.hMul #[← mkAppM ``HMul.hMul #[s, (rows[i]!)[j]!], r.value])
        proofs := proofs.push h
    let v ← mkListLit carrier values.toList
    let head ← mkAppM ``cofactor #[toExpr (n-1), B, iE, v, ← mkEqRefl (toExpr n)]
    let .forallE _ expected _ _ ← inferType head | throwError "det: invalid cofactor head"
    let proof := mkApp head (← allFinHints expected proofs.toList)
    let proof ← if transpose then
        let AT ← mkAppM ``Matrix.transpose #[A]
        let h ← transport AT (← identify AT B rows) proof
        mkEqTrans (← mkEqSymm (← mkAppM ``Matrix.det_transpose #[A])) h
      else pure proof
    let value ← values.foldrM (fun a b => mkAppM ``HAdd.hAdd #[a, b]) (← mkNumeral carrier 0)
    return {value, proof}
  let limit := cfg.budget.proofNodes
  if Hex.Reflect.proofNodeCount #[result.proof] (limit+1) > limit then
    throw (.internal budgetException)
  return result

/-- A bounded cofactor proof, selected only after an actual sparse step. -/
def sparse? (A : Expr) (lit : Recognized) (cfg : Hex.Reflect.Config := {}) : MetaM (Option Result) := do
  unless ← admitted A lit do return none
  if lit.n ≤ 3 then return none
  withLetDecl `detInput (← inferType A) A fun A => do
    let es ← lit.entries.mapM (·.mapM reduceIndices)
    let some (tree, _) := plan? (← zeros lit.carrier es) false 64 | return none
    let saved ← saveState
    let result ← try some <$> assemble lit.carrier es tree cfg catch e =>
      match e with
      | .internal id _ =>
        if id == budgetException then
          trace[HexMatrix.certificate] "sparse proof node budget exhausted (limit {cfg.budget.proofNodes})"
          pure none
        else throw e
      | _ => throw e
    match result with
    | none => saved.restore; return none
    | some r =>
      let B ← matrixExpr lit.carrier es
      let proof ← transport A (← identify A B es) r.proof
      let result ← finalize? A {r with proof} "sparse-cofactor" cfg
      if result.isNone then saved.restore
      return result

end HexPolyDetMathlib.Structural
