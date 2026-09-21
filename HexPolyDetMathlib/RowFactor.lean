/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyDetMathlib.Frontend
public import HexBareissMathlib.Tactic
public meta import HexPolyDetMathlib.Frontend
public meta import HexBareissMathlib.Tactic
public meta import Lean

public section

namespace HexPolyDetMathlib.RowFactor

open HexMatrixMathlib

/-- Integer coefficients multiplied by one arbitrary expression per row. -/
@[expose] def matrix {R : Type u} [CommRing R] (n : Nat)
    (C : Matrix (Fin n) (Fin n) Int) (f : List R) : Matrix (Fin n) (Fin n) R :=
  fun i j => (C i j : R) * vecOfList n f i

private theorem prod_vec {R : Type u} [CommRing R] (f : List R) :
    (∏ i : Fin f.length, vecOfList f.length f i) = f.prod := by
  induction f with
  | nil => simp
  | cons a f ih => simpa [Fin.prod_univ_succ, vecOfList] using congrArg (a * ·) ih

/-- The numeric determinant certificate leaves the common factors unexpanded. -/
theorem det {R : Type u} [CommRing R] (n : Nat)
    (C : Matrix (Fin n) (Fin n) Int) (f : List R) (d : Int) (e : R)
    (hlen : f.length = n) (hdet : C.det = d) (he : (d : R) = e) :
    (matrix n C f).det = f.foldl (· * ·) e := by
  subst n
  have hm : matrix f.length C f =
      Matrix.of (fun i j => vecOfList f.length f i * (C.map (Int.castRingHom R)) i j) := by
    ext i j
    exact mul_comm _ _
  rw [hm, Matrix.det_mul_column]
  have hc : (C.map (Int.castRingHom R)).det = (d : R) :=
    ((Int.castRingHom R).map_det C).symm.trans (congrArg (Int.castRingHom R) hdet)
  have : Std.Associative (fun a b : R => a * b) := ⟨mul_assoc⟩
  rw [hc, he, prod_vec, mul_comm, List.prod_eq_foldl]
  simpa only [mul_one] using (List.foldl_assoc (op := (· * ·))
    (l := f) (a₁ := e) (a₂ := 1)).symm

theorem entry {R : Type u} [CommRing R] (z : Int) (a f : R) (h : a = (z : R)) :
    a * f = (z : R) * f := congrArg (· * f) h

end HexPolyDetMathlib.RowFactor

public meta section

namespace HexPolyDetMathlib.RowFactor

open Lean Meta HexMatrixMathlib HexMatrixMathlib.Literal
open HexMatrixMathlib.DetPoly.Frontend

/-- Read only signed numeral syntax. The reconstructed cast and multiplication
are subsequently compared with the actual entry, including its instances. -/
private partial def coefficient? (e : Expr) : Option Int :=
  match e.consumeMData.getAppFnArgs with
  | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => some (Int.ofNat n)
  | (``Neg.neg, #[_, _, a]) => (coefficient? a).map Int.neg
  | _ => none

private def castProof? (carrier coeff : Expr) (z : Int) : MetaM (Option Expr) := do
  let cast ← mkAppOptM ``Int.cast #[some carrier, none, some (toExpr z)]
  if ← withTransparency .default (isDefEq coeff cast) then return some (← mkEqRefl coeff)
  let some u := (← getLevel carrier).dec | return none
  let ring ← synthInstance (← mkAppM ``Ring #[carrier])
  let proof ← try
      let ⟨_, h⟩ ← Mathlib.Meta.NormNum.deriveInt (u := u) (α := carrier) coeff ring
      mkAppM ``Mathlib.Meta.NormNum.IsInt.out #[h]
    catch _ => return none
  let some (_, lhs, rhs) := (← inferType proof).eq? | return none
  unless ← withTransparency .default (isDefEq lhs coeff <&&> isDefEq rhs cast) do return none
  return some proof

/-- A common row factor avoids polynomial production entirely. A target must
already have the factored result's form; otherwise the regular frontend runs. -/
def compute? (A : Expr) (lit : Recognized) (rhs? : Option Expr) : MetaM (Option Result) := do
  if A.hasExprMVar || rhs?.any (·.hasExprMVar) then return none
  if lit.n == 0 || lit.n > maxDimension then return none
  if HexMatrixMathlib.DetPoly.Certificate.arm (← getOptions) != .automatic then return none
  if Hex.Reflect.proofNodeCount #[A] 100001 +
      (rhs?.map (fun e => Hex.Reflect.proofNodeCount #[e] 100001)).getD 0 > 100000 then return none
  let .some ring ← trySynthInstance (← mkAppM ``CommRing #[lit.carrier]) | return none
  let some u := (← getLevel lit.carrier).dec | return none
  let entryHead := mkApp2 (mkConst ``RowFactor.entry [u]) lit.carrier ring
  let mut rows : Array (Array Int) := #[]
  let mut factors : Array Expr := #[]
  let mut sources : Array (Array (Expr × Expr)) := #[]
  for row in lit.entries do
    let mut coefficients := #[]
    let mut entries := #[]
    let mut factor? := none
    for entry in row do
      let entry ← reduceIndices entry
      let_expr HMul.hMul α β γ _ coeff factor := entry | return none
      unless ← withTransparency .reducible
          (isDefEq α lit.carrier <&&> isDefEq β lit.carrier <&&> isDefEq γ lit.carrier) do
        return none
      let some z := coefficient? coeff | return none
      if z.natAbs.log2 > 4096 then return none
      match factor? with
      | none => factor? := some factor
      | some f => if f != factor then return none
      coefficients := coefficients.push z
      entries := entries.push (entry, coeff)
    let some factor := factor? | return none
    rows := rows.push coefficients
    factors := factors.push factor
    sources := sources.push entries
  -- Expanded targets cannot use this route. Reject their shape before any
  -- coefficient proofs or elimination, without unfolding their polynomials.
  if let some rhs := rhs? then
    let mut head := rhs.consumeMData
    for factor in factors.reverse do
      let_expr HMul.hMul _ _ _ _ rest tail := head | return none
      unless tail.consumeMData == factor.consumeMData do return none
      head := rest.consumeMData
  let bits := rows.flatten.foldl (fun b z => max b (integerBits z)) 1
  if 2 * lit.n * (bits + lit.n.log2 + 2) > Hex.Reflect.Budget.default.coefficientBits then
    return none
  let .ok witness := Hex.Matrix.detWitnessOfLists lit.n (rows.toList.map Array.toList)
    | throwError "det: numeric row-factor producer failed its certificate check"
  let coeff ← mkNumeral lit.carrier witness.value.natAbs
  let coeff ← if witness.value < 0 then mkAppM ``Neg.neg #[coeff] else pure coeff
  let some hc ← castProof? lit.carrier coeff witness.value | return none
  let mut value := coeff
  for f in factors do value ← mkAppM ``HMul.hMul #[value, f]
  if let some rhs := rhs? then
    unless ← withTransparency .default (isDefEq value rhs) do return none
  let mut hints := #[]
  for i in [:lit.n] do
    let mut proofs := #[]
    for j in [:lit.n] do
      let (source, coeff) := (sources[i]!)[j]!
      let z := (rows[i]!)[j]!
      let head := mkAppN entryHead #[toExpr z, coeff, factors[i]!]
      let .forallE _ expected result _ ← inferType head | return none
      let some (_, lhs, rhs) := result.eq? | return none
      -- Concrete casts usually reduce directly. Check against the theorem's
      -- canonical ring operations, then emit only a denotation hint.
      if ← withTransparency .default (isDefEq source rhs) then
        proofs := proofs.push (← mkEqRefl source)
        continue
      unless ← withTransparency .default (isDefEq source lhs) do return none
      let some hc ← castProof? lit.carrier coeff z | return none
      unless ← withTransparency .default (isDefEq (← inferType hc) expected) do return none
      let proof := mkApp head (mkExpectedPropHint hc expected)
      proofs := proofs.push proof
    hints := hints.push proofs
  let C ← mkAppM ``ofLists #[toExpr lit.n, toExpr lit.n, toExpr (rows.toList.map Array.toList)]
  let numeric : Det.Cert := {
    lit := { n := lit.n
             m := lit.n
             carrier := mkConst ``Int
             entries := rows.map (·.map toExpr)
             route := .chain }
    witness := witness
    rows := rows
    rat := none }
  let fs ← mkListLit lit.carrier factors.toList
  -- Share payloads explicitly in the closed theorem. In particular, AllFin's
  -- suffix predicates must not repeat the whole input literal at every entry.
  withLetDecl `detInput (← inferType A) A fun A => do
    withLetDecl `detCoefficients (← inferType C) C fun C => do
      withLetDecl `detFactors (← inferType fs) fs fun fs => do
        let numericProof ← Det.build {} C numeric
        let B := mkAppN (mkConst ``matrix [u]) #[lit.carrier, ring, toExpr lit.n, C, fs]
        let hA ← applyEntryHints (← mkAppM ``DetPoly.Polynomial.identify #[A, B]) hints
        let hlen ← decideProof (← mkEq (← mkAppM ``List.length #[fs]) (toExpr lit.n))
        let hdet := mkAppN (mkConst ``det [u])
          #[lit.carrier, ring, toExpr lit.n, C, fs, numericProof.value, coeff,
            hlen, numericProof.proof]
        let .forallE _ expected _ _ ← inferType hdet | return none
        let hc ← mkEqSymm hc
        unless ← withTransparency .default (isDefEq (← inferType hc) expected) do return none
        let hdet := mkApp hdet (mkExpectedPropHint hc expected)
        let some (_, _, denoted) := (← inferType hdet).eq? | return none
        unless ← withTransparency .default (isDefEq denoted value) do return none
        let determinant := (← mkAppM ``Matrix.det #[A]).appFn!
        let proof ← mkEqTrans (← mkCongrArg determinant hA) hdet
        let target ← mkEq (← mkAppM ``Matrix.det #[A]) value
        let outcome ← Hex.Reflect.run <| Hex.Reflect.withOutcome do
          checkedBudgeted target (mkExpectedPropHint proof target)
        let (proof, nodes) ← match outcome with
          | .success result _ => pure result
          | .failure error => throwError error.toMessageData
          | .notApplicable | .declined .. => return none
        trace[HexMatrix.certificate] "{(Json.mkObj [("route", toJson "row-factor"),
          ("dimension", toJson lit.n), ("proof_node_budget", toJson nodes)]).compress}"
        return some { value, proof }

end HexPolyDetMathlib.RowFactor
