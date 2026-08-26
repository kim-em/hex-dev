/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexModArith.Residue
public meta import HexModArith.WordMod
public import HexModArith.Residue
public import HexModArith.WordMod

public section

/-!
Executable `#guard` / `#eval` checks for the default `ZMod64` extern paths.

Because `Hex.ZMod64.mul`, `pow`, and `inv` are extern-backed, these checks live
in a separate module so `#eval` runs against the compiled native
implementations from `HexModArith.Residue`.
-/
namespace Hex
namespace ZMod64

instance : Bounds (2 ^ 31 - 1) := ⟨by decide, by decide⟩
instance : Bounds 7 := ⟨by decide, by decide⟩
instance : Bounds 15 := ⟨by decide, by decide⟩

private def mersenneA : ZMod64 (2 ^ 31 - 1) := ofNat _ (2 ^ 31 - 2)
private def mersenneB : ZMod64 (2 ^ 31 - 1) := ofNat _ (2 ^ 31 - 3)
private def smallA : ZMod64 7 := ofNat _ 3
private def nonCoprimeA : ZMod64 15 := ofNat _ 6

/-- info: 2 -/
#guard_msgs in #eval (mul mersenneA mersenneB).toNat

/-- info: 5 -/
#guard_msgs in #eval (pow smallA 5).toNat

/-- info: 5 -/
#guard_msgs in #eval (inv smallA).toNat

/-- info: 1 -/
#guard_msgs in #eval (mul (inv smallA) smallA).toNat

/-- info: 13 -/
#guard_msgs in #eval (inv nonCoprimeA).toNat

#guard (mul mersenneA mersenneB).toNat = 2
#guard (pow smallA 5).toNat = 5
#guard (inv smallA).toNat = 5
#guard (mul (inv smallA) smallA).toNat = 1
#guard (inv nonCoprimeA).toNat = 13

end ZMod64

/-! # Full-word Montgomery and modular add/sub externs -/

private def wordPrime : UInt64 := UInt64.ofNat 18446744073709551557
private def wordCtx : _root_.MontCtx wordPrime :=
  _root_.MontCtx.mk wordPrime (by decide)

private def wordA : UInt64 := wordPrime - 1
private def wordB : UInt64 := wordPrime - 2

-- Carry across `2^64`, followed by the modular correction.
#guard Hex.addModWord wordPrime wordA wordB = wordPrime - 3
-- Reduction without a machine-word carry.
#guard Hex.addModWord 17 11 9 = 3
-- Borrow and non-borrow subtraction branches.
#guard Hex.subModWord 17 3 5 = 15
#guard Hex.subModWord 17 11 9 = 2
#guard Hex.subModWord wordPrime 1 (wordPrime - 1) = 2

-- Boundary-size Montgomery round-trip and product through the native externs.
#guard wordCtx.fromMont (wordCtx.toMont wordA) = wordA
#guard (wordCtx.fromMont
    (wordCtx.mulMont (wordCtx.toMont wordA) (wordCtx.toMont wordB))).toNat = 2

end Hex
