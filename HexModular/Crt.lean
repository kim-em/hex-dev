/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.SymMod

public section

/-!
Incremental scalar and vector Chinese remaindering for `hex-modular`.
-/
namespace Hex

namespace Modular

/-- A residue accumulated from coprime moduli. `value` is the symmetric
representative of their common solution modulo `modulus`. -/
structure Crt where
  /-- Product of the moduli already folded into the state. -/
  modulus : Nat
  /-- Symmetric representative of the accumulated residue. -/
  value : Int
  /-- The accumulated modulus is positive. -/
  pos : 0 < modulus
  /-- The representative lies in the symmetric interval. -/
  le : 2 * value.natAbs ≤ modulus

namespace Crt

/-- The empty scalar CRT accumulation, modulo one. -/
@[expose]
def init : Crt :=
  { modulus := 1, value := 0, pos := by decide, le := by decide }

/-- Fold the residue `r` modulo `m` into a scalar CRT accumulation using one
Garner mixed-radix step. Moduli zero and one and moduli not coprime to the
accumulated modulus are rejected. -/
@[expose]
def push (c : Crt) (r : Int) (m : Nat) : Option Crt :=
  if hm : 1 < m then
    let eg := Hex.pureIntExtGcd (Int.ofNat (c.modulus % m)) (Int.ofNat m)
    if hg : eg.1 = 1 then
      let inverse := eg.2.1
      let delta := symMod ((r - c.value) * inverse) m
      let modulus := c.modulus * m
      let value := symMod (c.value + Int.ofNat c.modulus * delta) modulus
      some
        { modulus
          value
          pos := Nat.mul_pos c.pos (by omega)
          le := symMod_le (Nat.mul_pos c.pos (by omega)) }
    else
      none
  else
    none

/-- GMP-backed compiled implementation of `Crt.push`. -/
def pushImpl (c : Crt) (r : Int) (m : Nat) : Option Crt :=
  if hm : 1 < m then
    let eg := HexArith.Int.extGcd (Int.ofNat (c.modulus % m)) (Int.ofNat m)
    if hg : eg.1 = 1 then
      let inverse := eg.2.1
      let delta := symMod ((r - c.value) * inverse) m
      let modulus := c.modulus * m
      let value := symMod (c.value + Int.ofNat c.modulus * delta) modulus
      some
        { modulus
          value
          pos := Nat.mul_pos c.pos (by omega)
          le := symMod_le (Nat.mul_pos c.pos (by omega)) }
    else
      none
  else
    none

/-- The compiled CRT step agrees with its kernel-reducible reference. -/
theorem push_eq_impl : @push = @pushImpl := by
  funext c r m
  simp only [push, pushImpl, HexArith.Int.extGcd]
  rfl

@[csimp] theorem push_csimp : @push = @pushImpl := push_eq_impl

/-- A successful scalar push multiplies the accumulated modulus by the new
one. -/
theorem push_modulus {c c' : Crt} {r : Int} {m : Nat}
    (h : c.push r m = some c') :
    c'.modulus = c.modulus * m := by
  unfold push at h
  split at h
  · simp only at h
    split at h
    · cases h
      rfl
    · contradiction
  · contradiction

/-- A successful scalar push records the requested new residue. -/
theorem push_congr_new {c c' : Crt} {r : Int} {m : Nat}
    (h : c.push r m = some c') :
    c'.value % (m : Int) = r % (m : Int) := by
  sorry

/-- A successful scalar push preserves the accumulated value modulo every
divisor of the old accumulated modulus. -/
theorem push_congr_old {c c' : Crt} {r : Int} {m d : Nat}
    (hd : d ∣ c.modulus) (h : c.push r m = some c') :
    c'.value % (d : Int) = c.value % (d : Int) := by
  sorry

/-- A successful scalar push preserves the symmetric-size invariant. -/
theorem push_le {c c' : Crt} {r : Int} {m : Nat}
    (_h : c.push r m = some c') :
    2 * c'.value.natAbs ≤ c'.modulus := by
  exact c'.le

end Crt

/-- Several accumulated residues sharing one positive product modulus. -/
structure CrtVec (k : Nat) where
  /-- Product of the moduli already folded into the state. -/
  modulus : Nat
  /-- Symmetric representatives of the accumulated residues. -/
  value : Vector Int k
  /-- The accumulated modulus is positive. -/
  pos : 0 < modulus
  /-- Every representative lies in the symmetric interval. -/
  le : ∀ i : Fin k, 2 * value[i].natAbs ≤ modulus

namespace CrtVec

/-- The empty vector CRT accumulation, modulo one. -/
@[expose]
def init (k : Nat) : CrtVec k :=
  { modulus := 1
    value := Vector.replicate k 0
    pos := by decide
    le := by intro i; simp }

/-- Fold `k` residues sharing modulus `m` into a vector CRT accumulation. The
extended GCD and modular inverse are computed once and reused for every
coordinate. -/
def push (c : CrtVec k) (r : Vector Int k) (m : Nat) : Option (CrtVec k) :=
  if hm : 1 < m then
    let eg := Hex.pureIntExtGcd (Int.ofNat (c.modulus % m)) (Int.ofNat m)
    if hg : eg.1 = 1 then
      let inverse := eg.2.1
      let modulus := c.modulus * m
      let value := Vector.zipWith
        (fun old new =>
          let delta := symMod ((new - old) * inverse) m
          symMod (old + Int.ofNat c.modulus * delta) modulus)
        c.value r
      some
        { modulus
          value
          pos := Nat.mul_pos c.pos (by omega)
          le := by
            intro i
            have hle := symMod_le (a :=
              c.value[i] + Int.ofNat c.modulus *
                symMod ((r[i] - c.value[i]) * inverse) m)
              (m := modulus) (Nat.mul_pos c.pos (by omega))
            grind }
    else
      none
  else
    none

/-- GMP-backed compiled implementation of `CrtVec.push`. -/
def pushImpl (c : CrtVec k) (r : Vector Int k) (m : Nat) : Option (CrtVec k) :=
  if hm : 1 < m then
    let eg := HexArith.Int.extGcd (Int.ofNat (c.modulus % m)) (Int.ofNat m)
    if hg : eg.1 = 1 then
      let inverse := eg.2.1
      let modulus := c.modulus * m
      let value := Vector.zipWith
        (fun old new =>
          let delta := symMod ((new - old) * inverse) m
          symMod (old + Int.ofNat c.modulus * delta) modulus)
        c.value r
      some
        { modulus
          value
          pos := Nat.mul_pos c.pos (by omega)
          le := by
            intro i
            have hle := symMod_le (a :=
              c.value[i] + Int.ofNat c.modulus *
                symMod ((r[i] - c.value[i]) * inverse) m)
              (m := modulus) (Nat.mul_pos c.pos (by omega))
            grind }
    else
      none
  else
    none

/-- The compiled vector CRT step agrees with its kernel-reducible reference. -/
theorem push_eq_impl : @push = @pushImpl := by
  funext k c r m
  simp only [push, pushImpl, HexArith.Int.extGcd]
  rfl

@[csimp] theorem push_csimp : @push = @pushImpl := push_eq_impl

/-- A successful vector push multiplies the accumulated modulus by the new
one. -/
theorem push_modulus {c c' : CrtVec k} {r : Vector Int k} {m : Nat}
    (h : c.push r m = some c') :
    c'.modulus = c.modulus * m := by
  unfold push at h
  split at h
  · simp only at h
    split at h
    · cases h
      rfl
    · contradiction
  · contradiction

/-- A successful vector push records every requested new residue. -/
theorem push_congr_new {c c' : CrtVec k} {r : Vector Int k} {m : Nat}
    (h : c.push r m = some c') :
    ∀ i : Fin k, c'.value[i] % (m : Int) = r[i] % (m : Int) := by
  sorry

/-- A successful vector push preserves every old accumulated residue modulo
every divisor of the old modulus. -/
theorem push_congr_old {c c' : CrtVec k} {r : Vector Int k} {m d : Nat}
    (hd : d ∣ c.modulus) (h : c.push r m = some c') :
    ∀ i : Fin k, c'.value[i] % (d : Int) = c.value[i] % (d : Int) := by
  sorry

/-- A successful vector push preserves every symmetric-size invariant. -/
theorem push_le {c c' : CrtVec k} {r : Vector Int k} {m : Nat}
    (_h : c.push r m = some c') :
    ∀ i : Fin k, 2 * c'.value[i].natAbs ≤ c'.modulus := by
  exact c'.le

end CrtVec

/-- Two integers strictly smaller than half the accumulated modulus and
congruent modulo that modulus are equal. -/
theorem crt_unique {c : Crt} {x y : Int}
    (h : 2 * x.natAbs < c.modulus)
    (h' : 2 * y.natAbs < c.modulus)
    (hx : x % (c.modulus : Int) = y % (c.modulus : Int)) :
    x = y := by
  have hxs : symMod y c.modulus = x := symMod_unique h hx
  have hys : symMod y c.modulus = y := symMod_unique h' rfl
  exact hxs.symm.trans hys

end Modular

end Hex
