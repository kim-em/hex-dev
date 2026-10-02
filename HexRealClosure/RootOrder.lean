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
@[expose] def pointQuery (x : E) : DensePoly E :=
  DensePoly.monomial 1 1 - DensePoly.C x

variable [Div E]

/-- Compare the actual output forms. Point comparisons use one difference;
mixed comparisons use the shared selected-sign producer, and two descriptors
use its common-product comparison. No failure is interpreted as equality.
The companion proves producer success and mathematical order in all cases. -/
@[expose] def Root.compare {sign : E → Int} {context : Ctx} :
    Root sign context → Root sign context → Except SignDet.BuildError Ordering
  | .point a, .point b => signOrder (sign (a - b))
  | .selected d, .point x =>
      match d.buildSigns [pointQuery x] with
      | .error error => .error error
      | .ok signs => signOrder signs.value
  | .point x, .selected d =>
      match d.buildSigns [pointQuery x] with
      | .error error => .error error
      | .ok signs =>
        match signOrder signs.value with
        | .error error => .error error
        | .ok order => .ok order.swap
  | .selected a, .selected b =>
      match a.buildComparison b with
      | .error error => .error error
      | .ok comparison => .ok comparison.order

/-- Insert an entry by its selected root, retaining the entire entry.
Equal roots remain an internal duplicate diagnostic. -/
@[expose] def Root.insertBy {sign : E → Int} {context : Ctx} {A : Type x}
    (key : A → Root sign context) (root : A) :
    List A → Except SignDet.BuildError (List A)
  | [] => .ok [root]
  | first :: rest =>
      match (key root).compare (key first) with
      | .error error => .error error
      | .ok .lt => .ok (root :: first :: rest)
      | .ok .eq => .error .system
      | .ok .gt =>
        match Root.insertBy key root rest with
        | .error error => .error error
        | .ok result => .ok (first :: result)

/-- Successful insertion preserves every supplied root exactly once. -/
theorem Root.insertBy_perm {sign : E → Int} {context : Ctx} {A : Type x}
    (key : A → Root sign context) (root : A)
    {roots out : List A} (accepted : Root.insertBy key root roots = .ok out) :
    out.Perm (root :: roots) := by
  induction roots generalizing out with
  | nil => simpa [Root.insertBy] using accepted.symm
  | cons first rest ih =>
    cases compared : (key root).compare (key first) with
    | error error => simp [Root.insertBy, compared] at accepted
    | ok order =>
      cases order with
      | eq => simp [Root.insertBy, compared] at accepted
      | lt =>
        have same : out = root :: first :: rest := by
          simpa [Root.insertBy, compared] using accepted.symm
        rw [same]
      | gt =>
        cases inserted : Root.insertBy key root rest with
        | error error => simp [Root.insertBy, compared, inserted] at accepted
        | ok result =>
          have same : out = first :: result := by
            simpa [Root.insertBy, compared, inserted] using accepted.symm
          rw [same]
          exact (List.Perm.cons first (ih inserted)).trans (List.Perm.swap _ _ _)

/-- Finite sorting by selected roots retains payloads and comparison diagnostics. -/
@[expose] def Root.sortBy {sign : E → Int} {context : Ctx} {A : Type x}
    (key : A → Root sign context) : List A → Except SignDet.BuildError (List A)
  | [] => .ok []
  | root :: rest =>
      match Root.sortBy key rest with
      | .error error => .error error
      | .ok result => Root.insertBy key root result

/-- Successful sorting is a permutation of the actual input. Mathematical
strict sortedness is separate from this computational preservation theorem. -/
theorem Root.sortBy_perm {sign : E → Int} {context : Ctx} {A : Type x}
    (key : A → Root sign context)
    {roots out : List A} (accepted : Root.sortBy key roots = .ok out) :
    out.Perm roots := by
  induction roots generalizing out with
  | nil => simpa [Root.sortBy] using accepted.symm
  | cons root rest ih =>
    cases sorted : Root.sortBy key rest with
    | error error => simp [Root.sortBy, sorted] at accepted
    | ok result =>
      have inserted : Root.insertBy key root result = .ok out := by
        simpa [Root.sortBy, sorted] using accepted
      exact (Root.insertBy_perm key root inserted).trans (List.Perm.cons root (ih sorted))

/-- Insert one root using the same sorter as multiplicity entries. -/
@[expose] def Root.insert {sign : E → Int} {context : Ctx} (root : Root sign context)
    (roots : List (Root sign context)) : Except SignDet.BuildError (List (Root sign context)) :=
  Root.insertBy id root roots

theorem Root.insert_perm {sign : E → Int} {context : Ctx} (root : Root sign context)
    {roots out : List (Root sign context)} (accepted : root.insert roots = .ok out) :
    out.Perm (root :: roots) := Root.insertBy_perm id root accepted

/-- Sort roots with the actual comparator, retaining diagnostic failures. -/
@[expose] def Root.sort {sign : E → Int} {context : Ctx}
    (roots : List (Root sign context)) : Except SignDet.BuildError (List (Root sign context)) :=
  Root.sortBy id roots

theorem Root.sort_perm {sign : E → Int} {context : Ctx}
    {roots out : List (Root sign context)} (accepted : Root.sort roots = .ok out) :
    out.Perm roots := Root.sortBy_perm id accepted

/-- Collect the actual point and descriptor output before ordering. -/
@[expose] def Output.entries {sign : E → Int} {context : Ctx}
    (output : Output sign context) : List (Root sign context) :=
  output.points.map Root.point ++ output.descriptors.map Root.selected

/-- Sort the actual completed output, retaining comparison diagnostics. -/
@[expose] def Completion.sort {sign : E → Int} {context : Ctx} {p : DensePoly E}
    (completion : Completion sign context p) :
    Except SignDet.BuildError (List (Root sign context)) :=
  Root.sort completion.roots.entries

end Hex.RealClosure.Isolation
