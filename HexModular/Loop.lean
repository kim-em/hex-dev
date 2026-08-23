/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.Crt

public section

/-!
Fuelled multi-modular reconstruction loops.
-/
namespace Hex

namespace Modular

/-- Consume the remaining supply entries, skipping rejected images and
non-coprime moduli and testing `accept` only after a successful CRT push. -/
private def crtLoop.go (image : Nat → Option (Vector Int k))
    (accept : CrtVec k → Option α) (supply : Array Nat)
    (fuel index : Nat) (state : CrtVec k) : Option α :=
  if hf : fuel = 0 then
    none
  else if hi : index < supply.size then
    let modulus := supply[index]
    match image modulus with
    | none => crtLoop.go image accept supply (fuel - 1) (index + 1) state
    | some residues =>
        match state.push residues modulus with
        | none => crtLoop.go image accept supply (fuel - 1) (index + 1) state
        | some next =>
            match accept next with
            | some result => some result
            | none => crtLoop.go image accept supply (fuel - 1) (index + 1) next
  else
    none
termination_by fuel
decreasing_by all_goals omega

/-- Fold moduli into a vector CRT state until the caller-supplied exact check
accepts a reconstruction. A rejected image never enters the state, and the
fuel bounds the number of supply entries inspected. -/
def crtLoop (image : Nat → Option (Vector Int k))
    (accept : CrtVec k → Option α) (supply : Array Nat) (fuel : Nat) :
    Option α :=
  crtLoop.go image accept supply fuel 0 (CrtVec.init k)

/-- Every successful loop result was returned by `accept` on some accumulated
CRT state; the loop itself never manufactures a caller result. -/
theorem crtLoop_of_some {image : Nat → Option (Vector Int k)}
    {accept : CrtVec k → Option α} {supply : Array Nat} {fuel : Nat} {x : α}
    (h : crtLoop image accept supply fuel = some x) :
    ∃ state, accept state = some x := by
  have go : ∀ (remaining index : Nat) (state : CrtVec k),
      crtLoop.go image accept supply remaining index state = some x →
        ∃ state, accept state = some x := by
    intro remaining
    induction remaining with
    | zero =>
        intro index state h
        simp [crtLoop.go] at h
    | succ remaining ih =>
        intro index state h
        unfold crtLoop.go at h
        simp only [Nat.succ_ne_zero, ↓reduceDIte] at h
        split at h
        · split at h
          · exact ih _ _ h
          · split at h
            · exact ih _ _ h
            · split at h
              · rename_i result next hnext
                cases h
                exact ⟨_, by assumption⟩
              · exact ih _ _ h
        · contradiction
  exact go fuel 0 (CrtVec.init k) h

end Modular

end Hex
