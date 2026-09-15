/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.KernelMap

@[expose] public section

/-! Positive-characteristic certificate arithmetic on ordinary natural-number
residues. The local operation dictionaries below carry no ring-law instances.
Producer and denotation conversions live in `KernelResidue.Denote`. -/

namespace Hex.MvPoly.Kernel

/-- Modular addition of coefficients. -/
def residueAdd (p a b : Nat) : Nat := Nat.mod (Nat.add a b) p

/-- Modular multiplication of coefficients. -/
def residueMul (p a b : Nat) : Nat := Nat.mod (Nat.mul a b) p

/-- Negation by multiplication by the residue of `-1`. Pattern matching on the
modulus keeps the coefficient path within natural addition, multiplication,
modulus, and structural recursion. -/
def residueNeg (p a : Nat) : Nat :=
  match p with
  | 0 => 0
  | k + 1 => residueMul p k a

/-- Merge canonical residue lists, reducing every coefficient collision. -/
def addMod (p : Nat) (a b : PolyList Nat) : PolyList Nat :=
  letI : Add Nat := ⟨residueAdd p⟩
  add a b

/-- Multiply translated rows with modular products and balanced modular merges. -/
def mulMod (p : Nat) (a b : PolyList Nat) : PolyList Nat :=
  letI : Add Nat := ⟨residueAdd p⟩
  letI : Mul Nat := ⟨residueMul p⟩
  mul a b

/-- Negate residue coefficients and remove zero results. -/
def negMod (p : Nat) (a : PolyList Nat) : PolyList Nat :=
  mapCoeffs (residueNeg p) a

/-- Multiply by an arbitrary natural-number scalar modulo the modulus. -/
def smulMod (p c : Nat) (a : PolyList Nat) : PolyList Nat :=
  mapCoeffs (residueMul p c) a

/-- Subtraction of canonical residue lists. -/
def subMod (p : Nat) (a b : PolyList Nat) : PolyList Nat :=
  addMod p a (negMod p b)

/-- Canonical exponents and nonzero coefficients strictly below the modulus. -/
def CanonicalMod (p n : Nat) (a : PolyList Nat) : Prop :=
  Canonical n a ∧ ∀ t ∈ a, t.2 < p

/-- Check canonical form and the residue bound on untrusted certificate data. -/
def isCanonicalMod (p n : Nat) (a : PolyList Nat) : Bool :=
  isCanonical n a && a.all (fun t => Nat.blt t.2 p)

/-- The Boolean check is equivalent to canonical residue form. -/
theorem isCanonicalMod_iff {p n : Nat} {a : PolyList Nat} :
    isCanonicalMod p n a = true ↔ CanonicalMod p n a := by
  simp [isCanonicalMod, CanonicalMod, isCanonical_iff, List.all_eq_true, Nat.blt_eq]

/-- The multiplicative identity, including the trivial residue ring. -/
def oneMod (p n : Nat) : PolyList Nat :=
  if Nat.blt 1 p then [(zeroExp n, 1)] else []

/-- The modular identity is canonical for every modulus. -/
theorem oneMod_canonical (p n : Nat) : CanonicalMod p n (oneMod p n) := by
  unfold oneMod
  split
  · rename_i h
    have hp : 1 < p := Nat.blt_eq.mp h
    simp [CanonicalMod, Canonical, length_zeroExp, hp]
  · simp [CanonicalMod, Canonical]

private theorem eq_nil_of_mod_zero {n : Nat} {a : PolyList Nat}
    (ha : CanonicalMod 0 n a) : a = [] := by
  cases a with
  | nil => rfl
  | cons t ts => have := ha.2 t (by simp); omega

/-- Modular addition preserves canonical residue form for every modulus. -/
theorem addMod_canonical (p : Nat) {n : Nat} {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    CanonicalMod p n (addMod p a b) := by
  cases p with
  | zero =>
    rw [eq_nil_of_mod_zero ha, eq_nil_of_mod_zero hb]
    simp [CanonicalMod, Canonical, addMod, add, merge]
  | succ p =>
    letI : Add Nat := ⟨residueAdd (Nat.succ p)⟩
    exact ⟨add_canonical ha.1 hb.1,
      coeffs_add (fun c => c < Nat.succ p) (fun _ _ _ _ => Nat.mod_lt _ (Nat.zero_lt_succ p))
        a b ha.2 hb.2⟩

/-- Modular multiplication preserves canonical residue form for every modulus. -/
theorem mulMod_canonical (p : Nat) {n : Nat} {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    CanonicalMod p n (mulMod p a b) := by
  cases p with
  | zero =>
    rw [eq_nil_of_mod_zero ha, eq_nil_of_mod_zero hb]
    simp [CanonicalMod, Canonical, mulMod, mul, mergeRows]
  | succ p =>
    letI : Add Nat := ⟨residueAdd (Nat.succ p)⟩
    letI : Mul Nat := ⟨residueMul (Nat.succ p)⟩
    exact ⟨mul_canonical ha.1 hb.1,
      coeffs_mul (fun c => c < Nat.succ p) (fun _ _ _ _ => Nat.mod_lt _ (Nat.zero_lt_succ p))
        (fun _ _ => Nat.mod_lt _ (Nat.zero_lt_succ p)) a b⟩

/-- Modular negation preserves canonical residue form for every modulus. -/
theorem negMod_canonical (p : Nat) {n : Nat} {a : PolyList Nat}
    (ha : CanonicalMod p n a) : CanonicalMod p n (negMod p a) := by
  cases p with
  | zero =>
    rw [eq_nil_of_mod_zero ha]
    simp [CanonicalMod, Canonical, negMod, mapCoeffs]
  | succ p =>
    exact ⟨mapCoeffs_canonical _ ha.1,
      coeffs_mapCoeffs (fun c => c < Nat.succ p) _ (fun _ => Nat.mod_lt _ (Nat.zero_lt_succ p)) a⟩

/-- Modular scaling preserves canonical form for every modulus and scalar. -/
theorem smulMod_canonical (p c : Nat) {n : Nat} {a : PolyList Nat}
    (ha : CanonicalMod p n a) : CanonicalMod p n (smulMod p c a) := by
  cases p with
  | zero =>
    rw [eq_nil_of_mod_zero ha]
    simp [CanonicalMod, Canonical, smulMod, mapCoeffs]
  | succ p =>
    exact ⟨mapCoeffs_canonical _ ha.1,
      coeffs_mapCoeffs (fun c => c < Nat.succ p) _ (fun _ => Nat.mod_lt _ (Nat.zero_lt_succ p)) a⟩

/-- Modular subtraction preserves canonical residue form for every modulus. -/
theorem subMod_canonical (p : Nat) {n : Nat} {a b : PolyList Nat}
    (ha : CanonicalMod p n a) (hb : CanonicalMod p n b) :
    CanonicalMod p n (subMod p a b) :=
  addMod_canonical p ha (negMod_canonical p hb)

end Hex.MvPoly.Kernel
