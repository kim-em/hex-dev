/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Build
public import HexPermGroup.Search.Transporter

public section

namespace Hex.PermGroup.Search

namespace Node

variable {G : Group n}

/-- Assigned source points are stored in reverse order for successive
transporter extension from point zero upward. -/
@[expose] def assigned (t : Node G) : List (Fin n) :=
  ((List.finRange n).filter fun x => x.val < t.base).reverse

theorem mem_assigned (t : Node G) (x : Fin n) : x ∈ t.assigned ↔ x.val < t.base := by
  simp [assigned]

end Node

namespace Intersection

variable {G : Group n}

/-- A failed simultaneous transporter in `H` excludes every completion of the
prefix. Individual point-orbit membership would not establish this. -/
@[expose] def reject (H : Group n) (t : Node G) : Bool :=
  (transport H t.rep.val t.assigned).failed

theorem reject_sound (H : Group n) (t : Node G) (h : reject H t = true)
    (p : Perm n) (hp : t.Contains p) : (Predicate.subgroup H).test p = false := by
  apply Bool.eq_false_iff.mpr
  intro hm
  apply ((transport H t.rep.val t.assigned).failed_iff).mp h
  refine ⟨⟨p, (H.contains_iff p).mp hm⟩, ?_⟩
  intro x hx
  exact t.agrees hp x ((t.mem_assigned x).mp hx)

/-- The replay repeats the successive stabilizer and orbit tests in `H`. -/
@[expose] def constraint (G H : Group n) : Constraint G (Predicate.subgroup H) :=
  .ofTest (reject H) (reject_sound H)

end Intersection

end Hex.PermGroup.Search

namespace Hex.PermGroup.Group

@[expose] def intersectionSearch (G H : Group n) : Search.Solution (Search.Intersection.constraint G H) :=
  Search.solve (Search.Intersection.constraint G H)

/-- Exact intersection with complete replay of simultaneous-prefix pruning. -/
@[expose] def intersection (G H : Group n) : Group n := (G.intersectionSearch H).group

theorem mem_intersection (G H : Group n) (p : Perm n) :
    Generated (G.intersection H).generators p ↔ Generated G.generators p ∧ Generated H.generators p := by
  rw [intersection, Search.Solution.spec]
  exact and_congr_right (fun _ => H.contains_iff p)

end Hex.PermGroup.Group
