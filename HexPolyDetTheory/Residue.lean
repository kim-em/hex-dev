/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetTheory.Sound
public import HexReflectTheory.KernelResidue
public import Mathlib.Algebra.Field.ZMod

public section

namespace HexMatrixTheory.DetPoly.Residue

open Hex Hex.Matrix Hex.MvPoly.Kernel
open HexMvPolyTheory.Kernel (denoteMod)
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

variable (p : Nat) [Hex.ZMod64.Bounds p]

/-- Interpret the shared residue operations in Mathlib's polynomial ring. -/
@[expose] noncomputable def decode (k : Nat) :
    Decode (Hex.PolyDet.opsMod p k) (MvPolynomial (Fin k) (ZMod p)) where
  eval := denoteMod p (n := k) (cmp := Mono.grevlex)
  zero := HexMvPolyTheory.Kernel.denoteMod_nil p
  one := HexMvPolyTheory.Kernel.denoteMod_oneMod p
  valid_zero := rfl
  valid_one := isCanonicalMod_iff.mpr (oneMod_canonical p k)
  valid_add _ _ ha hb := isCanonicalMod_iff.mpr
    (addMod_canonical p (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb))
  valid_mul _ _ ha hb := isCanonicalMod_iff.mpr
    (mulMod_canonical p (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb))
  valid_neg _ ha := isCanonicalMod_iff.mpr (negMod_canonical p (isCanonicalMod_iff.mp ha))
  add _ _ ha hb := HexMvPolyTheory.Kernel.denoteMod_addMod p
    (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb)
  mul _ _ ha hb := HexMvPolyTheory.Kernel.denoteMod_mulMod p
    (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb)
  neg _ ha := HexMvPolyTheory.Kernel.denoteMod_negMod p (isCanonicalMod_iff.mp ha)
  beq _ _ ha hb := HexMvPolyTheory.Kernel.beq_mod_iff p
    (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb)

/-- The polynomial value carried by a residue witness. -/
@[expose] def value : DetWitness (PolyList Nat) → PolyList Nat
  | .triangular _ _ d => d
  | .singular _ => []

/-- Soundness of the plain modular polynomial list check. -/
theorem checkDetPolyList_sound [Hex.ZMod64.PrimeModulus p] (k n : Nat)
    (rows : List (List (PolyList Nat))) (w : DetWitness (PolyList Nat))
    (h : checkDetPolyList (Hex.PolyDet.opsMod p k) n rows w = true) :
    ((decode p k).matrix n rows).det = HexMvPolyTheory.Kernel.denoteMod p
      (n := k) (cmp := Mono.grevlex) (value w) := by
  let : Fact (Nat.Prime p) := ⟨Nat.prime_def.mpr Hex.ZMod64.PrimeModulus.prime⟩
  have hs := (decode p k).sound n rows w h
  cases w <;> simpa [value, decode] using hs

end HexMatrixTheory.DetPoly.Residue
