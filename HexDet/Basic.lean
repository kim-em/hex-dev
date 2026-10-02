/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss
public import HexCharPoly

public section

/-!
The production determinant entry point.

`Hex.Det.det` adds no determinant algorithm. It interprets a typed recipe,
`Hex.Det.Policy`, which names the algorithm to run and carries the coefficient
operations that algorithm needs, and reports which arms were attempted.

A recipe is executable configuration. The determinant equations for each arm,
and the law class an installed recipe must satisfy, live in the Mathlib
companion `HexDetMathlib`; a recipe by itself proves nothing.

Every recipe runs the mandatory small arm at `n ≤ 2` first. Above that, this
version ships two algorithms: fraction-free Bareiss from `HexBareiss` on the
carriers that have an exact quotient, and Berkowitz through
`Hex.Matrix.charPoly` from `HexCharPoly` on every other commutative ring. The
field, modular and divisor arms of [hex-det](SPEC/hex-det.md) name
algorithms that do not exist below dispatch yet, so no recipe can select them:
the field and integer recipes carry an arm selector whose constructors are
exactly the arms implemented for that carrier, and both currently offer only
Bareiss. Selection regions, cutoff tie rules, input-size statistics, and modular
fuel and seed settings arrive with the arm that consumes them; with one
admissible arm per carrier there is no crossover to record.
-/

namespace Hex.Det

universe u

variable {R : Type u} {n : Nat}

/-- A determinant algorithm dispatch can run. -/
inductive Arm where
  /-- The `n ≤ 2` closed forms every recipe runs first. -/
  | small
  /-- Fraction-free Bareiss elimination. -/
  | bareiss
  /-- Forward elimination with row pivoting over a field. -/
  | elimination
  /-- The signed constant coefficient of the Samuelson--Berkowitz
  characteristic polynomial. -/
  | berkowitz
  /-- Multi-modular reconstruction. -/
  | modular
  /-- Reconstruction through a large known divisor of the determinant. -/
  | divisor
deriving DecidableEq, Repr, BEq, Inhabited

/-- The arms one determinant call attempted, in order, ending with the arm that
returned the value. Nonempty by construction, and it stores its endpoints once. -/
structure Route where
  /-- The arm the recipe selected. -/
  first : Arm
  /-- Any further arms the run fell through to, in order. -/
  rest : List Arm
deriving DecidableEq, Repr, BEq, Inhabited

namespace Route

/-- The route of a run that returned from the arm it selected. -/
@[expose] def single (arm : Arm) : Route := { first := arm, rest := [] }

/-- The arm the recipe selected. -/
@[expose] def selected (route : Route) : Arm := route.first

/-- The arm that produced the value. -/
@[expose] def completed (route : Route) : Arm := route.rest.getLastD route.first

/-- Every arm attempted, selection first. -/
@[expose] def attempts (route : Route) : List Arm := route.first :: route.rest

@[simp] theorem selected_single (arm : Arm) : (single arm).selected = arm := rfl

@[simp] theorem completed_single (arm : Arm) : (single arm).completed = arm := rfl

@[simp] theorem attempts_single (arm : Arm) : (single arm).attempts = [arm] := rfl

end Route

/-- A determinant value together with the route that produced it. -/
structure Result (R : Type u) where
  /-- The determinant. -/
  value : R
  /-- The arms this run attempted. -/
  route : Route

namespace Result

/-- The arm the recipe selected. -/
@[expose] def selected (result : Result R) : Arm := result.route.selected

/-- The arm that produced `value`. -/
@[expose] def completed (result : Result R) : Arm := result.route.completed

/-- Every arm attempted, selection first. -/
@[expose] def attempts (result : Result R) : List Arm := result.route.attempts

end Result

/-- The arms an integer recipe may select. Modular and divisor selection, with
the fuel, seed and coefficient-size region they need, join this type when
`hex-modular-matrix` supplies those algorithms. -/
inductive IntArm where
  /-- Fraction-free Bareiss on the integer backend. -/
  | bareiss
deriving DecidableEq, Repr, BEq, Inhabited

/-- The arms a field recipe may select. Forward elimination, with the dimension
region measured against Bareiss, joins this type when `HexRowReduce` supplies a
determinant-specific elimination. -/
inductive FieldArm where
  /-- Fraction-free Bareiss through the field's division. -/
  | bareiss
deriving DecidableEq, Repr, BEq, Inhabited

/-- A typed recipe: which algorithm to run above the small cases, and the
coefficient operations that algorithm needs. -/
inductive Policy (R : Type u) where
  /-- Berkowitz, which needs only decidable equality. -/
  | berkowitz (deq : DecidableEq R)
  /-- Exact-quotient Bareiss, with decidable equality and the quotient. The
  companion requires `quot (a * b) b = a` for `b ≠ 0`. -/
  | bareiss (deq : DecidableEq R) (quot : R → R → R)
  /-- Field selection, with decidable equality and the field's division. The
  division must extend the ambient multiplication, not a second ring structure
  on the same type. -/
  | field (deq : DecidableEq R) (div : R → R → R) (arm : FieldArm)
  /-- Integer selection. `toInt` and `ofInt` carry entries to the integer
  backend and the answer back; the companion requires them to be mutually
  inverse ring maps. The shipped `Int` recipe uses identity maps. -/
  | integer (toInt : R → Int) (ofInt : Int → R) (arm : IntArm)

/-- The `n ≤ 2` closed forms. Every recipe runs these before its own arm: this
is a size case, not a tuned crossover. -/
@[expose] def small? [Lean.Grind.CommRing R] : {n : Nat} → Matrix R n n → Option R
  | 0, _ => some 1
  | 1, A => some A[((0 : Fin 1), (0 : Fin 1))]
  | 2, A =>
      some (A[((0 : Fin 2), (0 : Fin 2))] * A[((1 : Fin 2), (1 : Fin 2))] -
        A[((0 : Fin 2), (1 : Fin 2))] * A[((1 : Fin 2), (0 : Fin 2))])
  | _ + 3, _ => none

/-- The Berkowitz determinant: the signed constant coefficient of the
characteristic polynomial. -/
@[expose] def berkowitzDet [Lean.Grind.CommRing R] [deq : DecidableEq R]
    (A : Matrix R n n) : R :=
  (-1 : R) ^ n * (Matrix.charPoly A).coeff 0

/-- Fraction-free Bareiss elimination at a supplied equality test and exact
quotient. -/
@[expose] def bareissDet [Lean.Grind.CommRing R] [deq : DecidableEq R]
    (quot : R → R → R) (A : Matrix R n n) : R :=
  Matrix.bareissWith quot A

/-- A field's division made total, so it meets the exact-quotient contract
`Hex.Matrix.bareissWith` expects. -/
@[expose] def guardQuot [Lean.Grind.CommRing R] [deq : DecidableEq R]
    (div : R → R → R) (a b : R) : R :=
  if b = 0 then 0 else div a b

/-- Carry the entries of `A` into `Int`. -/
@[expose] def toIntMatrix [Lean.Grind.CommRing R] (toInt : R → Int)
    (A : Matrix R n n) : Matrix Int n n :=
  Matrix.ofFn fun i j => toInt A[(i, j)]

/-- Run the integer backend on the image of `A` under `toInt` and carry the
answer back through `ofInt`. -/
@[expose] def integerDet [Lean.Grind.CommRing R] (toInt : R → Int) (ofInt : Int → R)
    (A : Matrix R n n) : R :=
  ofInt (Matrix.bareiss (toIntMatrix toInt A))

/-- The arm a recipe selects above the small cases. -/
@[expose] def Policy.arm : Policy R → Arm
  | .berkowitz _ => .berkowitz
  | .bareiss _ _ => .bareiss
  | .field _ _ .bareiss => .bareiss
  | .integer _ _ .bareiss => .bareiss

/-- The value of the arm a recipe selects, computed with the recipe's own
coefficient operations. -/
@[expose] def Policy.eval [Lean.Grind.CommRing R] : Policy R → Matrix R n n → R
  | .berkowitz deq, A => berkowitzDet (deq := deq) A
  | .bareiss deq quot, A => bareissDet (deq := deq) quot A
  | .field deq div .bareiss, A =>
      bareissDet (deq := deq) (guardQuot (deq := deq) div) A
  | .integer toInt ofInt .bareiss, A => integerDet toInt ofInt A

/-- Interpret a recipe: run the small arm when it applies, otherwise the arm the
recipe selects, recording the route in the branch that returns the value. -/
@[expose] def runWith [Lean.Grind.CommRing R] (policy : Policy R) (A : Matrix R n n) :
    Result R :=
  match small? A with
  | some value => { value := value, route := .single .small }
  | none => { value := policy.eval A, route := .single policy.arm }

/-- The recipe a carrier installs as its default. This is executable
configuration; `HexDetMathlib.LawfulDetOps` carries its correctness. -/
class DetOps (R : Type u) [Lean.Grind.CommRing R] where
  /-- The installed recipe. -/
  policy : Policy R

/-- Run the installed recipe. -/
@[expose] def DetOps.run [Lean.Grind.CommRing R] [DetOps R] (A : Matrix R n n) : Result R :=
  runWith DetOps.policy A

/-- The determinant of a square matrix, through the installed recipe. This is
the value projection of `DetOps.run`, not a second dispatch. -/
@[expose] def det [Lean.Grind.CommRing R] [DetOps R] (A : Matrix R n n) : R :=
  (DetOps.run A).value

@[simp] theorem det_eq_run_value [Lean.Grind.CommRing R] [DetOps R]
    (A : Matrix R n n) : det A = (DetOps.run A).value := rfl

/-- Berkowitz needs no quotient, so it serves every commutative ring with
decidable equality, including rings with zero divisors and the trivial ring. Its
low priority lets the carrier instance modules override it. -/
instance (priority := 100) instDetOpsBerkowitz [Lean.Grind.CommRing R] [DecidableEq R] :
    DetOps R where
  policy := .berkowitz inferInstance

/-- The recipe for a commutative ring with an exact quotient, to install locally
or from a carrier's integration module. It is deliberately not an instance:
importing a division provider must not silently change a carrier's policy. -/
@[expose] def quotientPolicy [Lean.Grind.CommRing R] [DecidableEq R] [Div R] : Policy R :=
  .bareiss inferInstance Hex.exactDiv

end Hex.Det
