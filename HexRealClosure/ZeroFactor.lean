/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Deflation

public section

namespace Hex.RealClosure.ZeroFactor

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]

/-- Remove successive exact factors of `X`. The returned multiplicity counts
only successful divisions, and the returned head retains the original scalar.
The input degree supplies enough fuel under a lawful coefficient interpretation. -/
@[expose] def extract (p : DensePoly E) : Nat → DensePoly E × Nat
  | 0 => (p, 0)
  | fuel + 1 =>
    match deflate? p 0 with
    | none => (p, 0)
    | some d =>
      let result := extract d.quotient fuel
      (result.1, result.2 + 1)

/-- Extract the complete power of `X` from a nonzero polynomial. Zero is left
as `(0, 0)`; the eventual root-set API must retain its separate `all` case. -/
@[expose] def remove (p : DensePoly E) : DensePoly E × Nat := extract p p.natDegree

theorem extract_zero (fuel : Nat) : extract (0 : DensePoly E) fuel = (0, 0) := by
  have h : deflate? (0 : DensePoly E) 0 = none := by
    cases hd : deflate? (0 : DensePoly E) 0 with
    | none => rfl
    | some d => exact False.elim (d.nonzero rfl)
  cases fuel <;> simp [extract, h]

theorem remove_zero : remove (0 : DensePoly E) = (0, 0) := extract_zero _

end Hex.RealClosure.ZeroFactor
