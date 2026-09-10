/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Normal.Bounded
public import HexPermGroup.Normal.DerivedCheck

public section

namespace Hex.PermGroup.Derived

open Execution

/-- A derived step reserves its commutator array before materialization, then
threads the same meter through the seed chain and every normal-closure rebuild. -/
@[expose] def construct {budget : Budget} (G : Group n) : Run budget (Result G) := do
  let count := G.generators.size * G.generators.size
  -- Two inverses and three products per commutator, then an identity for
  -- filtering. Auxiliary reservations include flat-map and duplicate removal.
  reserve .images (6 * n * count)
  reserve .storage (4 * count * count + 4 * count + G.generators.size)
  let S := seeds G
  let built ← Group.construct S
  let H : Group n :=
    { generators := S
      chain := built.val.chain
      valid := by simpa only [built.property, Group.generators_ofGenerators] using built.val.valid }
  have hH : H.IsSubgroup G := seed_inside G
  let closed ← Normal.iterateWith G (G.order - H.order) H hH (Nat.le_refl _)
  reserve .certificates 1
  return {
    group := closed.group
    certificate := ⟨H.chain, closed.trace⟩
    checked := by
      unfold check
      split
      · exact closed.checked
      · rename_i hn
        exact False.elim (hn H.valid) }

end Hex.PermGroup.Derived

namespace Hex.PermGroup.Group

/-- Exhaustion of a derived step returns no final derived subgroup. Its seed
construction and normal closure consume a single cumulative producer meter. -/
@[expose] def derivedWith (budget : Execution.Budget) (G : Group n) :
    Execution.Measured budget (Derived.Result G) := Execution.run budget (Derived.construct G)

end Hex.PermGroup.Group
