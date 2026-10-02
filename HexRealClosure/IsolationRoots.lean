/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Isolation
public import HexSignDet.RootList

public section

namespace Hex.RealClosure.Isolation

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [DecidableEq Ctx]

/-- Root values emitted by capped bisection and descriptors completing its
remaining cells. This intermediate output does not assert global ordering. -/
structure Output (sign : E → Int) (context : Ctx) where
  points : List E
  descriptors : List (SignDet.Descriptor E Ctx sign context)

/-- Complete one actual cell according to its retained root count. Empty
cells emit nothing; singleton cells query no derivatives using their stored
prepared domain. Only unresolved cells use all-derivative enumeration. -/
@[expose] def completeCell {sign : E → Int} (context : Ctx) {head : DensePoly E}
    (cell : Bisection.Cell sign head) :
    Except SignDet.BuildError (List (SignDet.Descriptor E Ctx sign context)) :=
  if cell.count = 0 then .ok []
  else if cell.count = 1 then
    let raw : SignDet.RawDescriptor E Ctx :=
      ⟨context, head, .finite cell.lower, .finite cell.upper, [], []⟩
    match SignDet.buildPrepared context cell.domain [] with
    | .error error => .error error
    | .ok replay =>
      match SignDet.Descriptor.ofReplay? sign context raw replay.val with
      | none => .error .replay
      | some descriptor => .ok [descriptor]
  else
    match SignDet.Descriptor.buildRoots sign context head (.finite cell.lower) (.finite cell.upper) with
    | .error error => .error error
    | .ok none => .error .system
    | .ok (some roots) => .ok roots

/-- Complete every actual retained cell; producer failures stay diagnostic. -/
@[expose] def completeCells {sign : E → Int} (context : Ctx) {head : DensePoly E} :
    List (Bisection.Cell sign head) →
      Except SignDet.BuildError (List (SignDet.Descriptor E Ctx sign context))
  | [] => .ok []
  | cell :: cells =>
    match completeCell context cell with
    | .error error => .error error
    | .ok roots =>
      match completeCells context cells with
      | .error error => .error error
      | .ok rest => .ok (roots ++ rest)

/-- Successful cell completion retains both actual producer results. -/
theorem completeCells_cons {sign : E → Int} {context : Ctx} {head : DensePoly E}
    {cell : Bisection.Cell sign head} {cells : List (Bisection.Cell sign head)}
    {out : List (SignDet.Descriptor E Ctx sign context)}
    (accepted : completeCells context (cell :: cells) = .ok out) :
    ∃ roots rest, completeCell context cell = .ok roots ∧
      completeCells context cells = .ok rest ∧ out = roots ++ rest := by
  cases produced : completeCell context cell with
  | error error => simp [completeCells, produced] at accepted
  | ok roots =>
    cases remaining : completeCells context cells with
    | error error => simp [completeCells, produced, remaining] at accepted
    | ok rest =>
      exact ⟨roots, rest, rfl, rfl, by
        simpa only [completeCells, produced, remaining, Except.ok.injEq] using accepted.symm⟩

/-- Complete the actual search route. Bounded completion retains every emitted
point and enumerates every remaining cell; whole-line completion uses its
stored head and endpoints. Unresolved and whole-line enumeration currently
prepares these domains again. -/
@[expose] def Route.complete {sign : E → Int} {p : DensePoly E} (context : Ctx) :
    Route sign p → Except SignDet.BuildError (Output sign context)
  | .bounded _ frontier =>
    match completeCells context frontier.cells with
    | .error error => .error error
    | .ok roots => .ok ⟨frontier.removed, roots⟩
  | .whole stored =>
    match SignDet.Descriptor.buildRoots sign context stored.domain.head
        stored.domain.lower stored.domain.upper with
    | .error error => .error error
    | .ok none => .error .system
    | .ok (some roots) => .ok ⟨[], roots⟩

/-- Successful completion tied to the actual capped search and enumeration.
All constructor evidence is erased from native execution. -/
structure Completion (sign : E → Int) (context : Ctx) (p : DensePoly E) where
  private mk ::
  search : Search sign p
  roots : Output sign context
  computed : search.route.complete context = .ok roots

/-- Run finite bound search, capped bisection and shared descriptor enumeration.
The absent search domain is separate from internal producer failures. -/
def complete? (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Except SignDet.BuildError (Option (Completion sign context p)) :=
  match search? sign p with
  | none =>
    match Bounds.find? sign p with
    | none => .ok none
    | some bound =>
      if (Bisection.Frontier.prepare? sign p (-bound.value) bound.value).isSome then
        .error .system
      else .ok none
  | some search =>
    match h : search.route.complete context with
    | .error error => .error error
    | .ok roots => .ok (some ⟨search, roots, h⟩)

/-- Successful dispatch and completion give the actual checked wrapper result. -/
theorem complete?_of_search {sign : E → Int} {context : Ctx} {p : DensePoly E}
    (search : Search sign p) (searched : search? sign p = some search)
    (roots : Output sign context) (completed : search.route.complete context = .ok roots) :
    ∃ result, complete? sign context p = .ok (some result) := by
  unfold complete?
  simp only [searched]
  split
  · rename_i error failed
    rw [completed] at failed
    cases failed
  · exact ⟨_, rfl⟩

/-- An absent completed domain came from a failed search. -/
theorem complete?_none_search {sign : E → Int} {context : Ctx}
    {p : DensePoly E} (absent : complete? sign context p = .ok none) :
    search? sign p = none := by
  cases searched : search? sign p with
  | none => rfl
  | some search =>
    simp only [complete?, searched] at absent
    split at absent <;> cases absent

/-- A missing completed domain after an accepted finite bound means the
initial domain itself was rejected. Failure after that point is diagnostic. -/
theorem complete?_none_unprepared {sign : E → Int} {context : Ctx}
    {p : DensePoly E} {bound : Bounds.Bound sign p}
    (accepted : complete? sign context p = .ok none)
    (bounded : Bounds.find? sign p = some bound) :
    Bisection.Frontier.prepare? sign p (-bound.value) bound.value = none := by
  cases prepared : Bisection.Frontier.prepare? sign p (-bound.value) bound.value with
  | none => rfl
  | some initial =>
    cases searched : search? sign p with
    | none => simp [complete?, searched, bounded, prepared] at accepted
    | some search =>
      simp only [complete?, searched] at accepted
      split at accepted <;> cases accepted

end Hex.RealClosure.Isolation
