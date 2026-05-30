import HexModArith.Basic

/-!
Executable `#guard` / `#eval` checks for the default `ZMod64` multiplication path.

Because `Hex.ZMod64.mul` is extern-backed, these checks live in a separate
module so `#eval` runs against the compiled native implementation from
`HexModArith.Basic`.
-/
namespace Hex
namespace ZMod64

instance : Bounds (2 ^ 31 - 1) := ⟨by decide, by decide⟩
instance : Bounds (2 ^ 63 + 29) := ⟨by decide, by decide⟩
instance : Bounds 7 := ⟨by decide, by decide⟩

private def mersenneA : ZMod64 (2 ^ 31 - 1) := ofNat _ (2 ^ 31 - 2)
private def mersenneB : ZMod64 (2 ^ 31 - 1) := ofNat _ (2 ^ 31 - 3)
private def wideA : ZMod64 (2 ^ 63 + 29) := ofNat _ (2 ^ 63 + 1)
private def wideB : ZMod64 (2 ^ 63 + 29) := ofNat _ (2 ^ 63 - 17)
private def smallA : ZMod64 7 := ofNat _ 3

/-- info: 2 -/
#guard_msgs in #eval (mul mersenneA mersenneB).toNat

/-- info: 1288 -/
#guard_msgs in #eval (mul wideA wideB).toNat

/-- info: 5 -/
#guard_msgs in #eval (pow smallA 5).toNat

/-- info: 5 -/
#guard_msgs in #eval (inv smallA).toNat

/-- info: 1 -/
#guard_msgs in #eval (mul (inv smallA) smallA).toNat

#guard (mul mersenneA mersenneB).toNat = 2
#guard (mul wideA wideB).toNat = 1288
#guard (pow smallA 5).toNat = 5
#guard (inv smallA).toNat = 5
#guard (mul (inv smallA) smallA).toNat = 1

end ZMod64
end Hex
