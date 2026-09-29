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
structure Roots (sign : E → Int) (context : Ctx) where
  points : List E
  descriptors : List (SignDet.Descriptor E Ctx sign context)

/-- Enumerate each actual retained cell using the shared root producer.
Absent domains and producer diagnostics remain failures of completion. -/
@[expose] def completeCells {sign : E → Int} (context : Ctx) {head : DensePoly E} :
    List (Bisection.Cell sign head) →
      Except SignDet.BuildError (List (SignDet.Descriptor E Ctx sign context))
  | [] => .ok []
  | cell :: cells =>
    match SignDet.Descriptor.buildRoots sign context head (.finite cell.lower) (.finite cell.upper) with
    | .error error => .error error
    | .ok none => .error .replay
    | .ok (some roots) =>
      match completeCells context cells with
      | .error error => .error error
      | .ok rest => .ok (roots ++ rest)

/-- Successful cell completion retains both actual producer results. -/
theorem completeCells_cons {sign : E → Int} {context : Ctx} {head : DensePoly E}
    {cell : Bisection.Cell sign head} {cells : List (Bisection.Cell sign head)}
    {out : List (SignDet.Descriptor E Ctx sign context)}
    (accepted : completeCells context (cell :: cells) = .ok out) :
    ∃ roots rest,
      SignDet.Descriptor.buildRoots sign context head (.finite cell.lower) (.finite cell.upper) =
        .ok (some roots) ∧ completeCells context cells = .ok rest ∧ out = roots ++ rest := by
  cases produced : SignDet.Descriptor.buildRoots sign context head
      (.finite cell.lower) (.finite cell.upper) with
  | error error => simp [completeCells, produced] at accepted
  | ok result =>
    cases result with
    | none => simp [completeCells, produced] at accepted
    | some roots =>
      cases remaining : completeCells context cells with
      | error error => simp [completeCells, produced, remaining] at accepted
      | ok rest =>
        exact ⟨roots, rest, rfl, rfl, by
          simpa only [completeCells, produced, remaining, Except.ok.injEq] using accepted.symm⟩

/-- Complete the actual search route. Bounded completion retains every emitted
point and enumerates every remaining cell; whole-line completion uses its
stored head and endpoints. Enumeration currently prepares these domains again. -/
@[expose] def Route.complete {sign : E → Int} {p : DensePoly E} (context : Ctx) :
    Route sign p → Except SignDet.BuildError (Roots sign context)
  | .bounded _ frontier =>
    match completeCells context frontier.cells with
    | .error error => .error error
    | .ok roots => .ok ⟨frontier.removed, roots⟩
  | .whole stored =>
    match SignDet.Descriptor.buildRoots sign context stored.domain.head
        stored.domain.lower stored.domain.upper with
    | .error error => .error error
    | .ok none => .error .replay
    | .ok (some roots) => .ok ⟨[], roots⟩

/-- Successful completion tied to the actual capped search and enumeration.
All constructor evidence is erased from native execution. -/
structure Completion (sign : E → Int) (context : Ctx) (p : DensePoly E) where
  private mk ::
  search : Search sign p
  roots : Roots sign context
  computed : search.route.complete context = .ok roots

/-- Run finite bound search, capped bisection and shared descriptor enumeration.
The absent search domain is separate from internal producer failures. -/
def complete? (sign : E → Int) (context : Ctx) (p : DensePoly E) :
    Except SignDet.BuildError (Option (Completion sign context p)) :=
  match search? sign p with
  | none => .ok none
  | some search =>
    match h : search.route.complete context with
    | .error error => .error error
    | .ok roots => .ok (some ⟨search, roots, h⟩)

end Hex.RealClosure.Isolation
