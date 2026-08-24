/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.Crt
public import HexModular.Loop
public import HexModular.Recon

public section

/-!
Small kernel-reduction canaries for the executable certificate closure.  The
search routines are exercised only on tiny values; certificate replay itself
reduces through `symMod`, `Crt.push`, and `ratReconCheck`.
-/

namespace Hex.Modular.KernelTests

/-- The outer-reduction regression from the SPEC. -/
@[expose] def outerReduction : Option (Nat × Int) := do
  let first ← Crt.init.push 1 3
  let second ← first.push 0 2
  pure (second.modulus, second.value)

example : outerReduction = some (6, -2) := by
  decide +kernel

/-- Degenerate and non-coprime moduli are rejected. -/
example : (Crt.init.push 1 0).isNone = true := by
  decide +kernel

example : (Crt.init.push 1 1).isNone = true := by
  decide +kernel

@[expose] def nonCoprimeRejected : Bool :=
  match Crt.init.push 1 3 with
  | none => false
  | some state => (state.push 2 6).isNone

example : nonCoprimeRejected = true := by
  decide +kernel

/-- `2/3` represents residue `68` modulo `101`. -/
example : ratReconCheck 68 101 8 8 (Rat.divInt 2 3) = true := by
  decide +kernel

/-- A wrong numerator is rejected even when it lies inside the bounds. -/
example : ratReconCheck 68 101 8 8 (Rat.divInt 1 3) = false := by
  decide +kernel

end Hex.Modular.KernelTests
