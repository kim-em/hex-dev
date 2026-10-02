/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexReflect.Convert
public import HexMvPoly.Kernel

@[expose] public section

namespace Hex.Reflect.Kernel

open Hex.MvPoly.Kernel

/-- The exponent list of an independent atom. An out-of-range index gives
all zeros; the interpretation theorem requires the reflected variable bound. -/
def unitExp : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, 0 => 1 :: zeroExp k
  | k + 1, i + 1 => 0 :: unitExp k i

/-- An integer constant in canonical list form. -/
def constant (k : Nat) (z : Int) : PolyList Int := smul z (one k)

/-- A single independent atom in canonical list form. -/
def atom (k i : Nat) : PolyList Int := [(unitExp k i, 1)]

/-- Structural polynomial exponentiation. -/
def power (k : Nat) (p : PolyList Int) : Nat → PolyList Int
  | 0 => one k
  | n + 1 => mul (power k p n) p

/-- Replay a reflected ring expression using only canonical term lists.
The producer independently supplies the final list and the kernel compares
it with this list computation, without converting reference polynomial trees. -/
def ringList (k : Nat) : RingExpr → PolyList Int
  | .num z | .intCast z => constant k z
  | .natCast z => constant k (Int.ofNat z)
  | .var i => atom k i
  | .add a b => add (ringList k a) (ringList k b)
  | .sub a b => sub (ringList k a) (ringList k b)
  | .mul a b => mul (ringList k a) (ringList k b)
  | .neg a => neg (ringList k a)
  | .pow a n => power k (ringList k a) n

theorem length_unitExp (k i : Nat) : (unitExp k i).length = k := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => cases i <;> simp [unitExp, length_zeroExp, ih]

theorem canonical_constant (k : Nat) (z : Int) : Canonical k (constant k z) :=
  smul_canonical z (one_canonical k)

theorem canonical_atom (k i : Nat) : Canonical k (atom k i) := by
  simp [atom, Canonical, length_unitExp]

theorem canonical_power (k : Nat) (p : PolyList Int) (n : Nat) (hp : Canonical k p) :
    Canonical k (power k p n) := by
  induction n with
  | zero => exact one_canonical k
  | succ n ih => exact mul_canonical ih hp

theorem canonical_ringList (k : Nat) (e : RingExpr) : Canonical k (ringList k e) := by
  induction e with
  | num z | intCast z => exact canonical_constant k z
  | natCast z => exact canonical_constant k (Int.ofNat z)
  | var i => exact canonical_atom k i
  | add a b ha hb => exact add_canonical ha hb
  | sub a b ha hb => exact sub_canonical ha hb
  | mul a b ha hb => exact mul_canonical ha hb
  | neg a ha => exact neg_canonical ha
  | pow a n ha => exact canonical_power k _ n ha

end Hex.Reflect.Kernel
