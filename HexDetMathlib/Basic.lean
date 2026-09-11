/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetMathlib.Small
public import HexPolyMathlib

public section

/-!
The dispatch contract.

`ValidRoute` says what a run is allowed to report: the route it returns, and the
value that route's completed arm produces on the same input with the recipe's own
coefficient operations. It follows the branches of `Hex.Det.runWith` rather than
trusting the reported tags.

`LawfulPolicy` pairs that with the determinant equation. It is separate from
`Hex.Det.DetOps`: a recipe is executable configuration, and selection metadata is
ordinary data, so neither establishes a determinant equation on its own.
-/

namespace HexDetMathlib

open Hex.Det

universe u

variable {R : Type u} {n : Nat}

section Shape

/-- No recipe selects the small arm: the interpreter runs it on size alone. -/
theorem Policy.arm_ne_small (policy : Policy R) : policy.arm ≠ Arm.small := by
  match policy with
  | .berkowitz _ | .bareiss _ _ | .field _ _ .bareiss | .integer _ _ .bareiss =>
      simp [Hex.Det.Policy.arm]

end Shape

/-- The route and value one run of `policy` on `A` is allowed to report.

A small completion asserts `n ≤ 2` and the closed form. Any other completion
asserts that the arm is the one the recipe selects, that the small arm did not
apply, and that the value is that arm's result on the same input.

A nonempty tail records arms that were attempted and failed. No shipped arm can
fail, so that case is empty; it gains content with the modular arm, whose
transition is justified by the failure equation of the attempt it falls through
from. -/
def ValidRoute [Lean.Grind.CommRing R] (policy : Policy R) (A : Hex.Matrix R n n)
    (result : Result R) : Prop :=
  match result.route.first, result.route.rest with
  | .small, [] => n ≤ 2 ∧ small? A = some result.value
  | arm, [] => arm = policy.arm ∧ small? A = none ∧ result.value = policy.eval A
  | _, _ :: _ => False

/-- The laws an explicit recipe must satisfy: it computes the reference
determinant, and it reports a route it is entitled to report. -/
class LawfulPolicy [Lean.Grind.CommRing R] (policy : Policy R) : Prop where
  /-- The interpreted recipe computes the Leibniz reference determinant. -/
  value_eq : ∀ {n : Nat} (A : Hex.Matrix R n n),
    (runWith policy A).value = Hex.Matrix.det A
  /-- The reported route is one the interpreter is entitled to report. -/
  route_sound : ∀ {n : Nat} (A : Hex.Matrix R n n),
    ValidRoute policy A (runWith policy A)

/-- The installed recipe of a carrier satisfies the recipe laws. -/
class LawfulDetOps (R : Type u) [Lean.Grind.CommRing R] [DetOps R] : Prop where
  /-- The laws of the installed recipe. This field is deliberately not itself an
  instance: the law for an arbitrary `DetOps R` is always the law of that
  instance's own recipe. -/
  lawful : LawfulPolicy (DetOps.policy (R := R))

/-- Every run above the small sizes reports the arm its recipe selects. -/
theorem validRoute_of_arm [Lean.Grind.CommRing R] {policy : Policy R}
    {A : Hex.Matrix R n n} (hnone : small? A = none) :
    ValidRoute policy A (runWith policy A) := by
  have harm := Policy.arm_ne_small policy
  have hrun : runWith policy A =
      { value := policy.eval A, route := Route.single policy.arm } := by
    unfold runWith
    rw [hnone]
  rw [hrun]
  unfold ValidRoute
  cases hcases : policy.arm with
  | small => exact absurd hcases harm
  | _ => exact ⟨rfl, hnone, rfl⟩

/-- Every run at the small sizes reports the small arm. -/
theorem validRoute_of_small [Lean.Grind.CommRing R] {policy : Policy R}
    {A : Hex.Matrix R n n} {value : R} (hsome : small? A = some value) :
    ValidRoute policy A (runWith policy A) := by
  have hrun : runWith policy A =
      { value := value, route := Route.single Arm.small } := by
    unfold runWith
    rw [hsome]
  rw [hrun]
  exact ⟨le_two_of_small?_eq_some hsome, hsome⟩

/-- The route half of `LawfulPolicy` holds for every recipe: the interpreter
reports the small arm exactly when it runs it, and the recipe's own arm
otherwise. -/
theorem validRoute_runWith [Lean.Grind.CommRing R] (policy : Policy R)
    (A : Hex.Matrix R n n) : ValidRoute policy A (runWith policy A) := by
  cases hcases : small? A with
  | none => exact validRoute_of_arm hcases
  | some value => exact validRoute_of_small hcases

/-- A recipe computes the reference determinant as soon as its own arm does:
below its arm the interpreter runs the small closed forms, which are the
reference determinant's own. -/
theorem value_eq_of_eval_eq [Lean.Grind.CommRing R] {policy : Policy R}
    (heval : ∀ {n : Nat} (A : Hex.Matrix R n n), policy.eval A = Hex.Matrix.det A)
    (A : Hex.Matrix R n n) : (runWith policy A).value = Hex.Matrix.det A := by
  cases hcases : small? A with
  | none =>
      have hrun : runWith policy A =
          { value := policy.eval A, route := Route.single policy.arm } := by
        unfold runWith
        rw [hcases]
      rw [hrun]
      exact heval A
  | some value =>
      have hrun : runWith policy A =
          { value := value, route := Route.single Arm.small } := by
        unfold runWith
        rw [hcases]
      rw [hrun]
      exact eq_det_of_small?_eq_some hcases

/-- The recipe laws follow from the determinant equation for the recipe's own
arm: the small arm and the route report are common to every recipe. -/
theorem lawfulPolicy_of_eval_eq [Lean.Grind.CommRing R] {policy : Policy R}
    (heval : ∀ {n : Nat} (A : Hex.Matrix R n n), policy.eval A = Hex.Matrix.det A) :
    LawfulPolicy policy where
  value_eq A := value_eq_of_eval_eq heval A
  route_sound A := validRoute_runWith policy A

/-- Dispatch computes the Leibniz reference determinant. -/
theorem det_eq [Lean.Grind.CommRing R] [DetOps R] [LawfulDetOps R]
    (A : Hex.Matrix R n n) : Hex.Det.det A = Hex.Matrix.det A :=
  (LawfulDetOps.lawful (R := R)).value_eq A

-- The two ring parameters are the point of the statement, and `GrindReduct` is
-- exactly the hypothesis that they agree, so the diamond the linter reports is
-- the one this theorem resolves.
set_option linter.overlappingInstances false in
/-- Dispatch computes Mathlib's determinant of the transported matrix.

The Mathlib structure is an explicit hypothesis, with `HexPolyMathlib.GrindReduct`
recording that its lightweight reduct is the executable instance the carrier
computes with. A carrier with no global Mathlib structure supplies one at the use
site, with `letI : CommRing R := HexPolyMathlib.commRingOfGrind`; that is a
definition rather than an instance, so instance search will not install it on the
caller's behalf. `HexDetMathlib.Carriers` has an example of each form. -/
theorem det_eq_mathlib [s : Lean.Grind.CommRing R] [inst : CommRing R]
    [HexPolyMathlib.GrindReduct R] [DetOps R] [LawfulDetOps R]
    (A : Hex.Matrix R n n) :
    Hex.Det.det A = Matrix.det (HexMatrixMathlib.matrixEquiv A) := by
  have hreduct : @CommRing.toGrindCommRing R inst = s :=
    HexPolyMathlib.GrindReduct.toGrind_eq
  have hmathlib := HexMatrixMathlib.det_eq (R := R) A
  rw [hreduct] at hmathlib
  exact (det_eq A).trans hmathlib

end HexDetMathlib
