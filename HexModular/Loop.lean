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

/-- Reachability through an exact prefix of the modulus supply.  Rejected
images and failed CRT pushes advance the prefix without changing the state;
successful pushes retain the equality consumed by the CRT congruence lemmas. -/
inductive CrtTrace (image : Nat → Option (Vector Int k)) (supply : Array Nat) :
    Nat → CrtVec k → Prop where
  | init : CrtTrace image supply 0 (CrtVec.init k)
  | skip {index : Nat} {state : CrtVec k}
      (trace : CrtTrace image supply index state)
      (hi : index < supply.size)
      (himage : image supply[index] = none) :
      CrtTrace image supply (index + 1) state
  | reject {index : Nat} {state : CrtVec k}
      (trace : CrtTrace image supply index state)
      (hi : index < supply.size) {residues : Vector Int k}
      (himage : image supply[index] = some residues)
      (hpush : state.push residues supply[index] = none) :
      CrtTrace image supply (index + 1) state
  | push {index : Nat} {state next : CrtVec k}
      (trace : CrtTrace image supply index state)
      (hi : index < supply.size) {residues : Vector Int k}
      (himage : image supply[index] = some residues)
      (hpush : state.push residues supply[index] = some next) :
      CrtTrace image supply (index + 1) next

/-- A traced state has consumed no more than the available supply. -/
theorem CrtTrace.le_size {image : Nat → Option (Vector Int k)}
    {supply : Array Nat} {consumed : Nat} {state : CrtVec k}
    (trace : CrtTrace image supply consumed state) :
    consumed ≤ supply.size := by
  induction trace with
  | init => simp
  | skip _ hi _ ih => omega
  | reject _ hi _ _ ih => omega
  | push _ hi _ _ ih => omega

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

/-- A successful loop result is accepted on a state reached by replaying the
exact consumed supply prefix.  The consumed prefix is nonempty because the
loop tests `accept` only after a successful push, and it cannot exceed fuel. -/
theorem crtLoop_trace {image : Nat → Option (Vector Int k)}
    {accept : CrtVec k → Option α} {supply : Array Nat} {fuel : Nat} {x : α}
    (h : crtLoop image accept supply fuel = some x) :
    ∃ consumed state,
      0 < consumed ∧ consumed ≤ fuel ∧ consumed ≤ supply.size ∧
        CrtTrace image supply consumed state ∧ accept state = some x := by
  have go : ∀ (remaining index : Nat) (state : CrtVec k),
      CrtTrace image supply index state →
      crtLoop.go image accept supply remaining index state = some x →
        ∃ consumed state',
          index < consumed ∧ consumed ≤ index + remaining ∧
            CrtTrace image supply consumed state' ∧ accept state' = some x := by
    intro remaining
    induction remaining with
    | zero =>
        intro index state trace h
        simp [crtLoop.go] at h
    | succ remaining ih =>
        intro index state trace h
        unfold crtLoop.go at h
        simp only [Nat.succ_ne_zero, ↓reduceDIte] at h
        split at h
        · rename_i hi
          split at h
          · rename_i himage
            obtain ⟨consumed, state', hindex, hbound, htrace, haccept⟩ :=
              ih (index + 1) state (trace.skip hi himage) h
            exact ⟨consumed, state', by omega, by omega, htrace, haccept⟩
          · rename_i residues himage
            split at h
            · rename_i hpush
              obtain ⟨consumed, state', hindex, hbound, htrace, haccept⟩ :=
                ih (index + 1) state (trace.reject hi himage hpush) h
              exact ⟨consumed, state', by omega, by omega, htrace, haccept⟩
            · rename_i next hpush
              split at h
              · rename_i result haccept
                cases h
                exact ⟨index + 1, next, by omega, by omega,
                  trace.push hi himage hpush, haccept⟩
              · rename_i haccept
                obtain ⟨consumed, state', hindex, hbound, htrace, haccept'⟩ :=
                  ih (index + 1) next (trace.push hi himage hpush) h
                exact ⟨consumed, state', by omega, by omega, htrace, haccept'⟩
        · contradiction
  obtain ⟨consumed, state, hpos, hfuel, trace, haccept⟩ :=
    go fuel 0 (CrtVec.init k) .init h
  exact ⟨consumed, state, hpos, by simpa using hfuel, trace.le_size,
    trace, haccept⟩

/-- Every successful loop result was returned by `accept` on some accumulated
CRT state; the loop itself never manufactures a caller result. -/
theorem crtLoop_of_some {image : Nat → Option (Vector Int k)}
    {accept : CrtVec k → Option α} {supply : Array Nat} {fuel : Nat} {x : α}
    (h : crtLoop image accept supply fuel = some x) :
    ∃ state, accept state = some x := by
  obtain ⟨_, state, _, _, _, _, haccept⟩ := crtLoop_trace h
  exact ⟨state, haccept⟩

end Modular

end Hex
