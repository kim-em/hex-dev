/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Build.Bounded
public import HexPermGroup.Normal.Closure

public section

/-! Bounded normal closure shares its meter with every strict subgroup rebuild. -/

namespace Hex.PermGroup.Normal

open Execution

/-- Reserve a complete conjugation pass before evaluating it. Short-circuiting
may use less than the reservation; it never performs an uncharged sift. -/
@[expose] def probe {budget : Budget} (G H : Group n) :
    Build.Computation budget (failure? G H) := do
  let pairs := G.chain.generators.size * H.generators.size
  reserve .sifts ((n + 1) * pairs)
  reserve .images ((2 * n * n + 4 * n) * pairs)
  reserve .storage (G.chain.generators.size + pairs)
  return ⟨failure? G H, rfl⟩

/-- Every completed iteration retains its ordinary normal-closure certificate.
An exhausted pass or chain construction exposes no terminal normality claim. -/
@[expose] def iterateWith {budget : Budget} (G : Group n) (remaining : Nat)
    (H : Group n) (hH : H.IsSubgroup G) (bound : G.order - H.order ≤ remaining) :
    Run budget (Closure G H) := do
  let tested ← probe G H
  match ht : tested.val with
  | none => return ⟨H, [], rfl, (failure_none G H).mp (tested.property.symm.trans ht)⟩
  | some (i, j) =>
    have failed : failure? G H = some (i, j) := tested.property.symm.trans ht
    have hn := failure_sound G H i j failed
    have hd := adjoin_decreases G H hH i j hn
    match hr : remaining with
    | 0 => return False.elim (by rw [hr] at bound; omega)
    | remaining + 1 =>
      reserve .images (3 * n)
      reserve .storage (H.generators.size + 1)
      let inserted ← Group.construct (H.generators.push (G.chain.generators[i.val].conj H.generators[j.val]))
      let K := inserted.val
      have he : K = H.adjoin (G.chain.generators[i.val].conj H.generators[j.val]) := inserted.property
      have hK : K.IsSubgroup G := by
        rw [he]
        exact step_inside (step_adjoin G H i j hn) hH
      have hb : G.order - K.order ≤ remaining := by
        rw [he]
        rw [hr] at bound
        omega
      let child ← iterateWith G remaining K hK hb
      reserve .certificates 1
      return {
          group := child.group
          trace := ⟨i.val, j.val, K.chain⟩ :: child.trace
          replayed := by
            have hs : step G H ⟨i.val, j.val, K.chain⟩ = some K := by
              rw [he]
              exact step_adjoin G H i j hn
            simpa only [replay, hs, Option.bind_some] using child.replayed
          normal := child.normal }

termination_by remaining

end Hex.PermGroup.Normal

namespace Hex.PermGroup.Group

/-- Bounded normal closure returns either a fully checked closure certificate or
an explicit exhausted resource. All conjugations and nested suffix rebuilds
consume one producer meter. -/
@[expose] def normalClosureWith (budget : Execution.Budget) (G H : Group n) (hH : H.IsSubgroup G) :
    Execution.Measured budget (Normal.Closure G H) :=
  Execution.run budget (Normal.iterateWith G (G.order - H.order) H hH (Nat.le_refl _))

end Hex.PermGroup.Group
