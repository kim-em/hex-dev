/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexModular.Loop
public import HexModular.Loop

public section

/-! Focused conformance cases for the fuelled CRT loop. -/

namespace Hex.Modular.LoopTests

private def ones (_modulus : Nat) : Option (Vector Int 1) :=
  some (Vector.replicate 1 1)

private def skipTwo (modulus : Nat) : Option (Vector Int 1) :=
  if modulus = 2 then none else ones modulus

private def acceptModulus (target : Nat) (state : CrtVec 1) : Option Nat :=
  if state.modulus = target then some state.modulus else none

-- The first successful push may be accepted immediately.
#guard crtLoop ones (acceptModulus 3) #[3] 1 == some 3

-- Rejected reconstructions keep accumulating successful pushes.
#guard crtLoop ones (acceptModulus 15) #[3, 5] 2 == some 15

-- Missing images and non-coprime pushes consume supply entries without
-- entering the accumulated state.
#guard crtLoop skipTwo (acceptModulus 15) #[2, 3, 6, 5] 4 == some 15

-- Fuel exhaustion is an ordinary failure and does not inspect later supply.
#guard (crtLoop skipTwo (acceptModulus 15) #[2, 3, 6, 5] 3).isNone

/-- The public provenance theorem instantiates on the skip/reject route. -/
example (h : crtLoop skipTwo (acceptModulus 15) #[2, 3, 6, 5] 4 = some 15) :
    ∃ consumed state,
      0 < consumed ∧ consumed ≤ 4 ∧ consumed ≤ #[2, 3, 6, 5].size ∧
        CrtTrace skipTwo #[2, 3, 6, 5] consumed state ∧
          acceptModulus 15 state = some 15 :=
  crtLoop_trace h

/-- The equality retained by a push trace step feeds the public CRT facts
without reconstructing or trusting the producer's residues. -/
example {state next : CrtVec 1} {residues : Vector Int 1} {modulus divisor : Nat}
    (hd : divisor ∣ state.modulus)
    (hpush : state.push residues modulus = some next) :
    next.modulus = state.modulus * modulus ∧
      (∀ i : Fin 1, next.value[i] % (modulus : Int) = residues[i] % (modulus : Int)) ∧
      (∀ i : Fin 1, next.value[i] % (divisor : Int) = state.value[i] % (divisor : Int)) :=
  ⟨CrtVec.push_modulus hpush, CrtVec.push_congr_new hpush,
    CrtVec.push_congr_old hd hpush⟩

end Hex.Modular.LoopTests
