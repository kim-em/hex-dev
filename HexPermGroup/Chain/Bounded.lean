/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Chain
public import HexPermGroup.Budget

public section

namespace Hex.PermGroup.Chain

open Execution

/-- Sift with a reservation before each visited level and each permutation
allocation. A missing orbit entry stops immediately, retaining the same result
as the ordinary sift. This works on raw chains without assuming their depth. -/
@[expose] def siftWith {budget : Budget} (c : Chain n) (base : Nat) (p : Perm n) :
    Run budget {result : SiftResult n // result = c.sift base p} := do
  reserve .sifts 1
  match hc : c with
  | .leaf _ _ =>
    reserve .images n
    return ⟨if p = Perm.id n then .member [] else .residual p, by simp [hc, sift]⟩
  | .cons level tail =>
    if hb : base < n then
      let image := p.get ⟨base, hb⟩
      match hx : level.orbit.lookup[image.val] with
      | none => return ⟨.missing base image, by simp [hc, sift, hb, image, hx]⟩
      | some x =>
        reserve .images (2 * n)
        let result ← tail.siftWith (base + 1) (level.orbit.reps[x.val].inv.comp p)
        return ⟨result.val.prepend x.val, by simp [hc, sift, hb, image, hx, result.property]⟩
    else return ⟨.shape base, by simp [hc, sift, hb]⟩

end Hex.PermGroup.Chain
