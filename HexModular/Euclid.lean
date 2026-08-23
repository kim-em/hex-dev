/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexArith

public section

/-!
Truncated extended-Euclidean rows for rational reconstruction.
-/
namespace Hex

namespace Modular

/-- One row of the extended Euclidean remainder sequence on `(m, a)`. The
omitted coefficient of `m` is never inspected by reconstruction consumers. -/
structure Row where
  /-- The current Euclidean remainder. -/
  r : Int
  /-- The coefficient of the second input `a`. -/
  t : Int
  deriving DecidableEq

/-- Continue the nonnegative Euclidean recurrence until the current remainder
is at most `P`, or until the zero remainder is reached. -/
private def euclidUntil.go (P : Int) (oldR r : Nat) (oldT t : Int) : Row :=
  if (r : Int) ≤ P then
    { r := Int.ofNat r, t }
  else if _hr : r = 0 then
    { r := 0, t }
  else
    let q := oldR / r
    euclidUntil.go P r (oldR % r) t (oldT - Int.ofNat q * t)
termination_by r
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hr)

/-- Return the first row of the extended Euclidean remainder sequence on
`(m, a)` whose remainder is at most `P`. The modulus is interpreted up to
sign, and `a` is reduced before entering the recurrence. -/
def euclidUntil (m a P : Int) : Row :=
  let modulus := m.natAbs
  if _hm : modulus = 0 then
    { r := 0, t := 0 }
  else
    let residue := (a % (Int.ofNat modulus)).natAbs
    euclidUntil.go P modulus residue 0 1

#guard euclidUntil 1 0 1 == { r := 0, t := 1 }
#guard euclidUntil 101 51 2 == { r := 1, t := 2 }

end Modular

end Hex
