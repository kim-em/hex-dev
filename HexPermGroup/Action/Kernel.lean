/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Build
public import HexPermGroup.Action.Schreier
public import HexPermGroup.Action.Image

public section

namespace Hex.PermGroup.Action

variable {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α}

omit [DecidableEq α] in
theorem Domain.restrict {objects : Array α} (hd : a.Domain objects)
    (H : Group n) (hi : H.IsSubgroup G) : (a.restrict H hi).Domain objects := by
  refine ⟨hd.1, ?_⟩
  intro i j
  let p : Element G := ⟨H.generators[i.val], hi _ (.generator (Array.getElem_mem i.isLt))⟩
  exact ⟨(hd.invariant p _).mp (Array.getElem_mem j.isLt),
    (hd.invariant p.inv _).mp (Array.getElem_mem j.isLt)⟩

/-- A checked subgroup consisting exactly of elements fixing every supplied
object. Its elements retain the original action degree. -/
structure Kernel (a : Action G α) (objects : Array α) where
  group : Group n
  spec : ∀ p : Perm n, Generated group.generators p ↔
    ∃ hp : Generated G.generators p, ∀ y ∈ objects, a.act ⟨p, hp⟩ y = y

namespace Kernel

omit [DecidableEq α] in
theorem subgroup {objects : Array α} (kernel : Kernel a objects) : kernel.group.IsSubgroup G :=
  fun p hp => ((kernel.spec p).mp hp).choose

/-- Add the first fixed-object condition to a kernel in its stabilizer. -/
@[expose] def prepend (H : Group n) (hi : H.IsSubgroup G) (x : α) (points : List α)
    (hs : ∀ p : Perm n, Generated H.generators p ↔
      ∃ hp : Generated G.generators p, a.act ⟨p, hp⟩ x = x)
    (child : Kernel (a.restrict H hi) points.toArray) : Kernel a (x :: points).toArray :=
  ⟨child.group, by
    intro p
    rw [child.spec]
    constructor
    · rintro ⟨hH, htail⟩
      obtain ⟨hG, hhead⟩ := (hs p).mp hH
      refine ⟨hG, ?_⟩
      intro y hy
      simp only [List.mem_toArray, List.mem_cons] at hy
      rcases hy with hy | hy
      · subst y
        exact hhead
      · exact htail y (by simpa using hy)
    · rintro ⟨hG, hfix⟩
      have hH : Generated H.generators p :=
        (hs p).mpr ⟨hG, hfix x (by simp)⟩
      refine ⟨hH, ?_⟩
      intro y hy
      exact hfix y (by simpa using List.mem_cons_of_mem x (List.mem_toArray.mp hy))⟩

/-- Successive full Schreier stabilizers compute the common fixed subgroup.
The domain remains invariant after each restriction and bounds every orbit. -/
@[expose] def fromDomain {G : Group n} (a : Action G α) (domain : Array α) (hd : a.Domain domain)
    (points : List α) (hp : ∀ y ∈ points, y ∈ domain) : Kernel a points.toArray :=
  match points with
  | [] => ⟨G, by
      intro p
      constructor
      · intro h
        exact ⟨h, by simp⟩
      · rintro ⟨h, _⟩
        exact h⟩
  | x :: points =>
    let orbit := a.orbitOfDomain domain hd x (hp x (List.mem_cons_self ..))
    let H := Orbit.stabilizer orbit.property.1
    let hi := Orbit.stabilizer_subgroup orbit.property.1
    let child := fromDomain (a.restrict H hi) domain (hd.restrict H hi) points
      (fun y hy => hp y (List.mem_cons_of_mem _ hy))
    prepend H hi x points (Orbit.mem_stabilizer orbit.property.1) child

end Kernel

/-- Validate the explicit domain budget and invariance, then intersect complete
object stabilizers. On an empty domain this returns the original group. -/
@[expose] def actionKernel (a : Action G α) (cap : Nat) (objects : Array α) :
    Except ImageError (Kernel a objects) :=
  if objects.size ≤ cap then
    if hd : a.Domain objects then
      .ok (cast (congrArg (Kernel a) (by simp : objects.toList.toArray = objects))
        (Kernel.fromDomain a objects hd objects.toList (by intro y hy; simpa using hy)))
    else .error .invalidDomain
  else .error (.sizeLimit ⟨objects.size, cap⟩)

theorem actionKernel_ok (a : Action G α) (cap : Nat) (objects : Array α) :
    (∃ kernel, a.actionKernel cap objects = .ok kernel) ↔ objects.size ≤ cap ∧ a.Domain objects := by
  unfold actionKernel
  split <;> rename_i hc
  · split <;> simp_all
  · simp_all
    omega

@[simp] theorem actionKernel_empty (a : Action G α) (cap : Nat) :
    (a.actionKernel cap #[]).map Kernel.group = .ok G := by
  simp [actionKernel, Domain, Kernel.fromDomain]
  rfl

end Hex.PermGroup.Action
