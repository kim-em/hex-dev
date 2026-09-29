/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.IsolationRoots
public import HexSignDet.Compare
public import HexSignDet.SelectedSigns

public section

namespace Hex.RealClosure.Isolation

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [DecidableEq Ctx]

/-- An emitted coefficient value or a root selected by an actual descriptor.
Both forms retain the coefficient carrier and immutable context. -/
inductive Root (sign : E → Int) (context : Ctx) where
  | point (value : E)
  | selected (descriptor : SignDet.Descriptor E Ctx sign context)

/-- Convert a checked ternary sign to an order. Invalid coefficient signs
remain an internal diagnostic. -/
@[expose] def signOrder (s : Int) : Except SignDet.BuildError Ordering :=
  if s = -1 then .ok .lt
  else if s = 0 then .ok .eq
  else if s = 1 then .ok .gt
  else .error .system

/-- The polynomial whose sign at a selected root compares it to a point. -/
@[expose] def difference (x : E) : DensePoly E :=
  DensePoly.monomial 1 1 - DensePoly.C x

variable [Div E]

/-- Compare the actual output forms. Point comparisons use one difference;
mixed comparisons use the shared selected-sign producer, and two descriptors
use its common-product comparison. No failure is interpreted as equality.
Strict mathematical order for the last case still needs the upstream Thom
order theorem. -/
@[expose] def Root.compare {sign : E → Int} {context : Ctx} :
    Root sign context → Root sign context → Except SignDet.BuildError Ordering
  | .point a, .point b => signOrder (sign (a - b))
  | .selected d, .point x =>
      match d.buildSigns [difference x] with
      | .error error => .error error
      | .ok signs => signOrder signs.value
  | .point x, .selected d =>
      match d.buildSigns [difference x] with
      | .error error => .error error
      | .ok signs =>
        match signOrder signs.value with
        | .error error => .error error
        | .ok order => .ok order.swap
  | .selected a, .selected b =>
      match a.buildComparison b with
      | .error error => .error error
      | .ok comparison => .ok comparison.order

/-- Insert one output root using the actual comparator. Equal roots are an
internal error: squarefree completion and coprime factor lists must be distinct. -/
def Root.insert {sign : E → Int} {context : Ctx} (root : Root sign context) :
    List (Root sign context) → Except SignDet.BuildError (List (Root sign context))
  | [] => .ok [root]
  | first :: rest =>
      match root.compare first with
      | .error error => .error error
      | .ok .lt => .ok (root :: first :: rest)
      | .ok .eq => .error .system
      | .ok .gt =>
        match root.insert rest with
        | .error error => .error error
        | .ok result => .ok (first :: result)

/-- Successful insertion preserves every supplied root exactly once. -/
theorem Root.insert_perm {sign : E → Int} {context : Ctx} (root : Root sign context)
    {roots out : List (Root sign context)} (accepted : root.insert roots = .ok out) :
    out.Perm (root :: roots) := by
  induction roots generalizing out with
  | nil => simpa [Root.insert] using accepted.symm
  | cons first rest ih =>
    cases compared : root.compare first with
    | error error => simp [Root.insert, compared] at accepted
    | ok order =>
      cases order with
      | eq => simp [Root.insert, compared] at accepted
      | lt =>
        have same : out = root :: first :: rest := by
          simpa [Root.insert, compared] using accepted.symm
        rw [same]
      | gt =>
        cases inserted : root.insert rest with
        | error error => simp [Root.insert, compared, inserted] at accepted
        | ok result =>
          have same : out = first :: result := by
            simpa [Root.insert, compared, inserted] using accepted.symm
          rw [same]
          exact (List.Perm.cons first (ih inserted)).trans (List.Perm.swap _ _ _)

/-- Finite insertion sorting, preserving internal comparison diagnostics. -/
def Root.sort {sign : E → Int} {context : Ctx} :
    List (Root sign context) → Except SignDet.BuildError (List (Root sign context))
  | [] => .ok []
  | root :: rest =>
      match Root.sort rest with
      | .error error => .error error
      | .ok result => root.insert result

/-- Successful sorting is a permutation of the actual input. Mathematical
strict sortedness is separate from this computational preservation theorem. -/
theorem Root.sort_perm {sign : E → Int} {context : Ctx}
    {roots out : List (Root sign context)} (accepted : Root.sort roots = .ok out) :
    out.Perm roots := by
  induction roots generalizing out with
  | nil => simpa [Root.sort] using accepted.symm
  | cons root rest ih =>
    cases sorted : Root.sort rest with
    | error error => simp [Root.sort, sorted] at accepted
    | ok result =>
      have inserted : root.insert result = .ok out := by
        simpa [Root.sort, sorted] using accepted
      exact (root.insert_perm inserted).trans (List.Perm.cons root (ih sorted))

/-- Collect the actual point and descriptor output before ordering. -/
@[expose] def Output.entries {sign : E → Int} {context : Ctx}
    (output : Output sign context) : List (Root sign context) :=
  output.points.map Root.point ++ output.descriptors.map Root.selected

end Hex.RealClosure.Isolation
