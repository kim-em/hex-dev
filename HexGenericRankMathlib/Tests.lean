/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGenericRankMathlib.Tactic
import Mathlib.Algebra.Field.ZMod
public meta import Lean
public meta import HexReflect

open Matrix

example (x : ℚ) (hx : x ≠ 0) : (!![x]).rank = 1 := by
  rank

example (x : ℚ) : (!![x]).rank ≤ 1 := by
  rank

example (x : ℚ) (hx : x ^ 2 - 1 ≠ 0) : (!![x, 1; 1, x]).rank = 2 := by
  rank

example (x : ℚ) (hx : x ≠ 0) : (!![x]).rank = 1 := by
  exact (rank% !![x]).proof

example (x : ℚ) : (generic_rank% !![x]).value = 1 := rfl

open MvPolynomial in
example : (!![X (0 : Fin 1)] : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) ℤ)).rank = 1 := by
  rank

open MvPolynomial in
example : (!![X (0 : Fin 1), 1; 1, X 0] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℤ)).rank = 2 := by
  rank

open MvPolynomial in
example : (!![X (0 : Fin 2), X 1] : Matrix (Fin 1) (Fin 2) (MvPolynomial (Fin 2) ℤ)).rank = 1 := by
  rank

example (x : ZMod 3) (hx : x ^ 3 - x ≠ 0) : (!![x ^ 3 - x]).rank = 1 := by
  rank

example (x : ZMod 3) : (!![x ^ 3 - x]).rank ≤ 1 := by
  rank

example (x : ZMod 3) (h : True → x ^ 3 - x ≠ 0) : (!![x ^ 3 - x]).rank = 1 := by
  rank
  guard_target = x ^ 3 - x ≠ 0
  exact h trivial

open MvPolynomial in
example :
    ((!![X (0 : Fin 1), 1; 1, X 0] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℤ)).map
      (algebraMap _ (FractionRing (MvPolynomial (Fin 1) ℤ)))).rank = 2 := by
  rank

open MvPolynomial in
example {K : Type*} [Field K] [Algebra (MvPolynomial (Fin 1) ℤ) K]
    [IsFractionRing (MvPolynomial (Fin 1) ℤ) K] :
    ((!![X (0 : Fin 1), 1; 1, X 0] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 1) ℤ)).map
      (algebraMap _ K)).rank = 2 := by
  rank

example (x : ℚ) (h : True → x ≠ 0) : (!![x]).rank = 1 := by
  rank
  guard_target = x ≠ 0
  exact h trivial

example (x : ℚ) (h : True → x ^ 2 - 1 ≠ 0) : (!![x, 1; 1, x]).rank = 2 := by
  rank
  guard_target = x ^ 2 - 1 ≠ 0
  exact h trivial

example (x : ℚ) (hx : x ≠ 0) : 1 ≤ (!![x]).rank := by rank
example (x : ℚ) (hx : x ≠ 0) : 1 = (!![x]).rank := by rank
example (x : ℚ) (hx : x ≠ 0) : (!![x]).rank ≥ 0 := by rank
example (x : ℚ) : 2 ≥ (!![x]).rank := by rank
example (x : ℚ) (hx : x ≠ 0) : Matrix.rank (fun _ _ : Fin 2 => x) = 1 := by rank
example (x : ℚ) (hx : x ≠ 0) :
    (Matrix.ofArray (m := 2) (n := 2) #[x, x, x, x] rfl).rank = 1 := by rank
example (x : ℚ) : Matrix.rank (fun (_ : Fin 0) (_ : Fin 3) => x) = 0 := by rank
example (x : ℚ) : Matrix.rank (fun (_ : Fin 3) (_ : Fin 0) => x) = 0 := by rank

example : (!![(1 : ℤ), 2; 2, 4]).rank = 1 := by rank
example : (!![(1 : ℚ), 2; 2, 4]).rank = 1 := by rank -packing
example : (!![(2 : ℚ) + 3]).rank = 1 := by rank

example {F : Type*} [Field F] [CharZero F] (x : F) (hx : x ≠ 0) : (!![x]).rank = 1 := by rank
example (x y : ℚ) (h : x / y ≠ 0) : (!![x / y]).rank = 1 := by rank
example (x y : ℚ) : (generic_rank% !![x / y]).value = 1 := rfl
example (x : ℚ) (_hx : x = 0) : (generic_rank% !![x]).value = 1 := rfl
example (x : ℚ) : (generic_rank% !![x - x]).value = 0 := rfl

-- Bounds inconsistent with the generic rank decline without replacing the goal.
example (x : ℚ) (_hx : x = 0) : True := by
  fail_if_success have : (!![x]).rank = 0 := by rank
  fail_if_success have : 2 ≤ (!![x]).rank := by rank
  fail_if_success have : (!![x]).rank ≤ 0 := by rank
  fail_if_success have r := rank% !![x]
  trivial

-- A different nonzero minor does not discharge the chosen pivot's condition.
set_option linter.unusedVariables false in
example (x y : ℚ) (_hy : y ≠ 0) : True := by
  fail_if_success have r := rank% !![x, y]
  trivial

-- The finite-field identity is outside the fixed ring language.
set_option linter.unusedVariables false in
example (x : ZMod 3) : True := by
  fail_if_success have : (!![x ^ 3 - x]).rank = 0 := by rank
  fail_if_success have r := rank% !![x ^ 3 - x]
  trivial

-- An opaque coefficient atom in a polynomial ring is a specialisation.
open MvPolynomial in
example (a : ℤ) (h : True → (C a : MvPolynomial (Fin 1) ℤ) ≠ 0) :
    (!![C a] : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) ℤ)).rank = 1 := by
  rank
  guard_target = (C a : MvPolynomial (Fin 1) ℤ) ≠ 0
  exact h trivial

-- Reserved case splitting and matrix-size exhaustion are declines.
set_option linter.unusedVariables false in
example (x : ℚ) : True := by
  fail_if_success have : (!![x]).rank ≤ 1 := by rank (matrixSize := 0)
  fail_if_success have : (!![x]).rank ≤ 1 := by rank (caseSplits := 1)
  trivial

-- Output 1 over positive-characteristic polynomial rings is recorded as a
-- non-test in bench/HexGenericRankMathlib/ProofProbe/FiniteGeneric.lean until
-- the shared residue encoding (#10257) lands.

namespace KernelTests
open HexGenericRankMathlib

def x : PolyLists.Poly Int := [([1], 1)]
def one : PolyLists.Poly Int := [([0], 1)]
def A : PolyLists.Rows Int := [[x]]
def c : PolyWitness Int := ⟨1, [0], [0], x, [[one]]⟩

-- These proofs reduce only lists and primitive integer/natural arithmetic.
example : checkRankPolyList 1 1 1 A c = true := by decide
example : checkRankPolyList 1 1 1 A { c with denom := [] } = false := by decide
example : checkRankPolyList 1 1 1 A { c with adj := [[[]]] } = false := by decide
example : checkRankPolyList 1 1 1 A { c with rows := [1] } = false := by decide
example : checkRankPolyList 1 1 1 A { c with cols := [] } = false := by decide
example : checkRankPolyList 1 1 1 A { c with rank := 2 } = false := by decide
example : checkRankPolyList 2 1 1 A c = false := by decide
example : checkRankPolyList 1 1 1 [[x, x]] c = false := by decide
example : checkRankPolyList 1 1 1 [[([([1], 1), ([1], 1)] : PolyLists.Poly Int)]] c = false := by decide
example : checkRankPolyList 1 1 1 [[([([1], 0)] : PolyLists.Poly Int)]] c = false := by decide

-- The pivot check alone cannot certify additional columns.
example : checkRankPolyList 1 1 2 [[x, one]] { c with adj := [[one]] } = true := by decide
example : checkRankPolyList 1 2 1 [[x], [one]] { c with adj := [[one]] } = true := by decide
example : checkRankPolyList 1 2 2 [[x, []], [[], one]] c = false := by decide

-- Integer representatives may satisfy the residue identities but not the
-- integer identities; denominator reduction must still be nonzero.
example : Modular.checkRankPolyList 3 1 1 1 [[x]] { c with denom := [([1], 4)] } = true := by decide
example : Modular.checkRankPolyList 3 1 1 1 [[x]] { c with denom := [([1], 3)] } = false := by decide
example : checkRankPolyList 1 1 1 [[x]] { c with denom := [([1], 4)] } = false := by decide
end KernelTests

open Lean Meta Elab Hex.Reflect in
elab "inspect_generic " A:term : tactic => Tactic.withMainContext do
  let A ← Term.elabTerm A none
  Term.synthesizeSyntheticMVarsNoPostponing
  let A ← instantiateMVars A
  let .success r usage ← HexGenericRankMathlib.Provider.rank A
    | throwError "expected successful symbolic provider"
  unless r.rank == 1 && r.conditional.conditions.size == 1 && usage.atoms == 1 do
    throwError "incorrect rank, atom count or number of conditions"
  let c := r.conditional.conditions[0]!
  unless c.provider == HexGenericRankMathlib.Provider.id.name &&
      c.source == A && c.operation == "rank" && !c.reason.isEmpty do
    throwError "missing condition provenance"
  let cfg : HexGenericRankMathlib.Provider.Config := {
    conditions.normalizers := #[fun _ => throwError "normalizer ran before matching local hypothesis"] }
  unless (← HexGenericRankMathlib.Provider.discharge r cfg).isSome do
    throwError "matching local hypothesis did not discharge the condition"
  for dim in [BudgetDimension.sourceNodes, .atoms, .reflectedNodes, .exponent,
      .terms, .coefficientBits, .proofNodes] do
    let cfg : HexGenericRankMathlib.Provider.Config := {
      reflection.budget := Budget.default.set dim 0 }
    match ← HexGenericRankMathlib.Provider.rank A cfg with
    | .declined (.budgetExhausted exhausted) _ =>
      unless exhausted.dimension == dim do throwError "wrong exhausted dimension"
    | _ => throwError "zero resource limit did not decline"
  Tactic.closeMainGoal `inspect_generic (mkConst ``True.intro)

example (x : ℚ) (_hx : x ^ 2 ≠ 0) : True := by
  inspect_generic !![x ^ 2]

-- The characteristic affects the generic rank, even with only 0/1 input coefficients.
example (x : ZMod 2) : (generic_rank% !![x, x, 0; x, 0, x; 0, x, x]).value = 2 := rfl
example (x : ZMod 2) (hx : x ^ 2 ≠ 0) :
    (!![x, x, 0; x, 0, x; 0, x, x]).rank = 2 := by rank
example (x : ZMod 2) : (generic_rank% !![x + x]).value = 0 := rfl

example (x : ℚ) : (!![x, 1; 1, x]).rank ≤ 2 := by rank
example : (!![(1 : ℚ), 1; 1, 1]).rank = 1 := by rank

#print axioms HexGenericRankMathlib.genericCert_check
#print axioms HexGenericRankMathlib.genericRank_eq
#print axioms HexGenericRankMathlib.genericCert_minor
#print axioms HexGenericRankMathlib.genericRank_succ_minor
#print axioms HexGenericRankMathlib.checkRankPolyList_sound
#print axioms HexGenericRankMathlib.Modular.checkRankPolyList_sound
#print axioms HexMatrixMathlib.checkRank_sound_at

-- Closed numeral conditions may be polymorphic in the carrier and instances.
example {F : Type*} [Field F] [CharZero F] (x : F) : (!![x - x]).rank = 0 := by rank
example {F : Type*} [Field F] [CharZero F] : (!![(1 : F)]).rank = 1 := by rank
example {F : Type*} [CommRing F] [IsDomain F] (x : F) :
    (rank% !![x - x]).value = 0 := rfl
