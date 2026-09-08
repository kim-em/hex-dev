/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.First
public import HexPermGroup.Search.Budget
public import HexPermGroup.Word.Size

public section

namespace Hex.PermGroup.Search

variable {G : Group n} {test : Perm n → Bool} {budget : Budget}

/-- Sift once to obtain the chain choices, reserve the exact number of program
nodes, then construct the positive certificate in the original generators. -/
@[expose] def Witness.ofElementWith (p : Element G) (hp : test p.val = true) (m : Meter budget) :
    Measured budget (Witness G test) :=
  match m.spend .sifts 1 with
  | .error failure => .exhausted failure
  | .ok meter =>
    let digits := (G.chain.choose 0 p.val).get (by
      rw [Chain.choose_isSome]
      exact (G.contains_iff _).mpr p.property)
    match meter.spend .certificates (G.programSize digits) with
    | .error failure => .exhausted failure
    | .ok meter =>
      .ok
        { value := p.val
          word := G.program digits
          checked := by
            rw [checkWitness, Bool.and_eq_true]
            refine ⟨?_, hp⟩
            have hc : G.chain.choose 0 p.val = some digits := by simp [digits]
            simpa only [Chain.choose_sound hc] using G.check_program digits }
        meter

end Hex.PermGroup.Search
