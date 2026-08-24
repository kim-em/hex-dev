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

private theorem emod_eq_of_dvd {x y modulus : Int}
    (h : modulus ∣ x - y) :
    x % modulus = y % modulus := by
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
  exact Int.emod_eq_zero_of_dvd h

private theorem symMod_emod_dvd {a : Int} {modulus divisor : Nat}
    (hmodulus : 0 < modulus) (hdivisor : divisor ∣ modulus) :
    symMod a modulus % (divisor : Int) = a % (divisor : Int) := by
  apply emod_eq_of_dvd
  apply Int.dvd_trans (Int.ofNat_dvd.mpr hdivisor)
  exact Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (symMod_emod hmodulus))

private theorem garner_congr_new {old new inverse delta : Int} {oldModulus modulus : Nat}
    (holdModulus : 0 < oldModulus) (hmodulus : 0 < modulus)
    (hdelta : delta % (modulus : Int) =
      ((new - old) * inverse) % (modulus : Int))
    (hinverse : (Int.ofNat oldModulus * inverse) % (modulus : Int) =
      1 % (modulus : Int)) :
    symMod (old + Int.ofNat oldModulus * delta) (oldModulus * modulus) %
        (modulus : Int) =
      new % (modulus : Int) := by
  rw [symMod_emod_dvd (Nat.mul_pos holdModulus hmodulus) (Nat.dvd_mul_left _ _)]
  apply emod_eq_of_dvd
  have hdeltaDvd : (modulus : Int) ∣ delta - (new - old) * inverse :=
    Int.dvd_of_emod_eq_zero
      (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hdelta)
  have hinverseDvd : (modulus : Int) ∣ Int.ofNat oldModulus * inverse - 1 :=
    Int.dvd_of_emod_eq_zero
      (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hinverse)
  rw [show old + Int.ofNat oldModulus * delta - new =
      Int.ofNat oldModulus * (delta - (new - old) * inverse) +
        (new - old) * (Int.ofNat oldModulus * inverse - 1) by
    simp only [Int.mul_sub, Int.mul_one]
    have : Int.ofNat oldModulus * ((new - old) * inverse) =
        (new - old) * (Int.ofNat oldModulus * inverse) := by
      ac_rfl
    rw [this]
    omega]
  exact Int.dvd_add (Int.dvd_mul_of_dvd_right hdeltaDvd)
    (Int.dvd_mul_of_dvd_right hinverseDvd)

private theorem garner_congr_old {old delta : Int} {oldModulus modulus divisor : Nat}
    (holdModulus : 0 < oldModulus) (hmodulus : 0 < modulus)
    (hdivisor : divisor ∣ oldModulus) :
    symMod (old + Int.ofNat oldModulus * delta) (oldModulus * modulus) %
        (divisor : Int) =
      old % (divisor : Int) := by
  rw [symMod_emod_dvd (Nat.mul_pos holdModulus hmodulus)
    (Nat.dvd_trans hdivisor (Nat.dvd_mul_right _ _))]
  apply emod_eq_of_dvd
  rw [show old + Int.ofNat oldModulus * delta - old =
      Int.ofNat oldModulus * delta by omega]
  exact Int.dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hdivisor)

private theorem garner_inverse {oldModulus modulus : Nat}
    (hcoprime : (Hex.pureIntExtGcd
      (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).1 = 1) :
    (Int.ofNat oldModulus *
        (Hex.pureIntExtGcd
          (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1) %
        (modulus : Int) =
      1 % (modulus : Int) := by
  have hbez := Hex.pureIntExtGcd_bezout_proj
    (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)
  rw [hcoprime] at hbez
  apply emod_eq_of_dvd
  have hrem : (modulus : Int) ∣
      Int.ofNat oldModulus - Int.ofNat (oldModulus % modulus) := by
    refine ⟨Int.ofNat (oldModulus / modulus), ?_⟩
    have hnat := congrArg Int.ofNat (Nat.mod_add_div oldModulus modulus)
    change Int.ofNat (oldModulus % modulus) +
        (modulus : Int) * Int.ofNat (oldModulus / modulus) =
      Int.ofNat oldModulus at hnat
    omega
  have hbezDvd : (modulus : Int) ∣
      (Hex.pureIntExtGcd
          (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1 *
          Int.ofNat (oldModulus % modulus) - 1 := by
    rw [show
      (Hex.pureIntExtGcd
          (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1 *
            Int.ofNat (oldModulus % modulus) - 1 =
          -((Hex.pureIntExtGcd
            (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.2 *
              Int.ofNat modulus) by
      omega]
    exact Int.dvd_neg.mpr (Int.dvd_mul_left _ _)
  rw [show
    Int.ofNat oldModulus *
          (Hex.pureIntExtGcd
            (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1 - 1 =
        (Hex.pureIntExtGcd
          (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1 *
            (Int.ofNat oldModulus - Int.ofNat (oldModulus % modulus)) +
          ((Hex.pureIntExtGcd
              (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1 *
                Int.ofNat (oldModulus % modulus) - 1) by
    simp only [Int.mul_sub]
    have : Int.ofNat oldModulus *
          (Hex.pureIntExtGcd
            (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1 =
        (Hex.pureIntExtGcd
          (Int.ofNat (oldModulus % modulus)) (Int.ofNat modulus)).2.1 *
          Int.ofNat oldModulus := by
      ac_rfl
    rw [this]
    omega]
  exact Int.dvd_add (Int.dvd_mul_of_dvd_right hrem) hbezDvd

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
  unfold push at h
  split at h <;> try contradiction
  next hm =>
    dsimp only at h
    split at h <;> try contradiction
    next hg =>
      cases h
      apply garner_congr_new c.pos (by omega) (symMod_emod (by omega))
      exact garner_inverse hg

/-- A successful scalar push preserves the accumulated value modulo every
divisor of the old accumulated modulus. -/
theorem push_congr_old {c c' : Crt} {r : Int} {m d : Nat}
    (hd : d ∣ c.modulus) (h : c.push r m = some c') :
    c'.value % (d : Int) = c.value % (d : Int) := by
  unfold push at h
  split at h <;> try contradiction
  next hm =>
    dsimp only at h
    split at h <;> try contradiction
    next _ =>
      cases h
      exact garner_congr_old c.pos (by omega) hd

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
  unfold push at h
  split at h <;> try contradiction
  next hm =>
    dsimp only at h
    split at h <;> try contradiction
    next hg =>
      cases h
      intro i
      change
        (Vector.zipWith
            (fun old new =>
              symMod
                (old + Int.ofNat c.modulus *
                  symMod ((new - old) *
                    (Hex.pureIntExtGcd
                      (Int.ofNat (c.modulus % m)) (Int.ofNat m)).2.1) m)
                (c.modulus * m))
            c.value r)[i.val] % (m : Int) =
          r[i.val] % (m : Int)
      rw [Vector.getElem_zipWith i.isLt]
      apply garner_congr_new c.pos (by omega) (symMod_emod (by omega))
      exact garner_inverse hg

/-- A successful vector push preserves every old accumulated residue modulo
every divisor of the old modulus. -/
theorem push_congr_old {c c' : CrtVec k} {r : Vector Int k} {m d : Nat}
    (hd : d ∣ c.modulus) (h : c.push r m = some c') :
    ∀ i : Fin k, c'.value[i] % (d : Int) = c.value[i] % (d : Int) := by
  unfold push at h
  split at h <;> try contradiction
  next hm =>
    dsimp only at h
    split at h <;> try contradiction
    next _ =>
      cases h
      intro i
      change
        (Vector.zipWith
            (fun old new =>
              symMod
                (old + Int.ofNat c.modulus *
                  symMod ((new - old) *
                    (Hex.pureIntExtGcd
                      (Int.ofNat (c.modulus % m)) (Int.ofNat m)).2.1) m)
                (c.modulus * m))
            c.value r)[i.val] % (d : Int) =
          c.value[i.val] % (d : Int)
      rw [Vector.getElem_zipWith i.isLt]
      exact garner_congr_old c.pos (by omega) hd

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
