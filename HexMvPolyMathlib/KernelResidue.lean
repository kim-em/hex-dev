/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.Kernel
public import HexMvPoly.KernelResidue
public import HexModArithMathlib.Ring
public import Mathlib.Algebra.MvPolynomial.Equiv

public section

/-! Semantic transport of natural-residue certificates to Mathlib `ZMod`.
All closed certificate computation remains in the Mathlib-free list layer. -/

namespace HexMvPolyMathlib.Kernel

open Hex
open Hex.MvPoly
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

variable (p : Nat) [Hex.ZMod64.Bounds p]
variable {n : Nat} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Change both the polynomial representation and its residue coefficient carrier. -/
noncomputable def residueEquiv :
    MvPoly n (Hex.ZMod64 p) cmp ≃+* MvPolynomial (Fin n) (ZMod p) :=
  (HexMvPolyMathlib.equiv (cmp := cmp)).trans
    (MvPolynomial.mapEquiv (Fin n) HexModArithMathlib.ZMod64.equiv)

/-- Mathlib denotation of the kernel's natural-residue encoding. -/
@[expose] noncomputable def denoteMod (a : PolyList Nat) :
    MvPolynomial (Fin n) (ZMod p) :=
  residueEquiv p (cmp := cmp) (Hex.MvPoly.Kernel.denoteMod p (cmp := cmp) a)

/-- Modular addition denotes Mathlib polynomial addition. -/
theorem denoteMod_addMod {a b : PolyList Nat}
    (ha : Hex.MvPoly.Kernel.CanonicalMod p n a)
    (hb : Hex.MvPoly.Kernel.CanonicalMod p n b) :
    denoteMod p (cmp := cmp) (Hex.MvPoly.Kernel.addMod p a b) =
      denoteMod p (cmp := cmp) a + denoteMod p (cmp := cmp) b := by
  exact (congrArg (residueEquiv p (cmp := cmp))
    (Hex.MvPoly.Kernel.denoteMod_addMod p (cmp := cmp) ha hb)).trans (map_add _ _ _)

/-- Modular multiplication denotes Mathlib polynomial multiplication. -/
theorem denoteMod_mulMod {a b : PolyList Nat}
    (ha : Hex.MvPoly.Kernel.CanonicalMod p n a)
    (hb : Hex.MvPoly.Kernel.CanonicalMod p n b) :
    denoteMod p (cmp := cmp) (Hex.MvPoly.Kernel.mulMod p a b) =
      denoteMod p (cmp := cmp) a * denoteMod p (cmp := cmp) b := by
  exact (congrArg (residueEquiv p (cmp := cmp))
    (Hex.MvPoly.Kernel.denoteMod_mulMod p (cmp := cmp) ha hb)).trans (map_mul _ _ _)

/-- Modular negation denotes Mathlib polynomial negation. -/
theorem denoteMod_negMod {a : PolyList Nat}
    (ha : Hex.MvPoly.Kernel.CanonicalMod p n a) :
    denoteMod p (cmp := cmp) (Hex.MvPoly.Kernel.negMod p a) = -denoteMod p (cmp := cmp) a := by
  exact (congrArg (residueEquiv p (cmp := cmp))
    (Hex.MvPoly.Kernel.denoteMod_negMod p (cmp := cmp) ha)).trans (map_neg _ _)

/-- Modular subtraction denotes Mathlib polynomial subtraction. -/
theorem denoteMod_subMod {a b : PolyList Nat}
    (ha : Hex.MvPoly.Kernel.CanonicalMod p n a)
    (hb : Hex.MvPoly.Kernel.CanonicalMod p n b) :
    denoteMod p (cmp := cmp) (Hex.MvPoly.Kernel.subMod p a b) =
      denoteMod p (cmp := cmp) a - denoteMod p (cmp := cmp) b := by
  exact (congrArg (residueEquiv p (cmp := cmp))
    (Hex.MvPoly.Kernel.denoteMod_subMod p (cmp := cmp) ha hb)).trans (map_sub _ _ _)

/-- Executable constants map to constants over Mathlib residues. -/
theorem residueEquiv_C (c : Hex.ZMod64 p) :
    residueEquiv p (cmp := cmp) (Hex.MvPoly.C c) =
      MvPolynomial.C (HexModArithMathlib.ZMod64.equiv c) := by
  simp [residueEquiv, HexMvPolyMathlib.equiv_apply]

/-- Modular scaling denotes multiplication by the natural scalar in `ZMod p`. -/
theorem denoteMod_smulMod (c : Nat) {a : PolyList Nat}
    (ha : Hex.MvPoly.Kernel.CanonicalMod p n a) :
    denoteMod p (cmp := cmp) (Hex.MvPoly.Kernel.smulMod p c a) =
      MvPolynomial.C (c : ZMod p) * denoteMod p (cmp := cmp) a := by
  have h := congrArg (residueEquiv p (cmp := cmp))
    (Hex.MvPoly.Kernel.denoteMod_smulMod p (cmp := cmp) c ha)
  rw [map_mul, residueEquiv_C] at h
  have hc : HexModArithMathlib.ZMod64.equiv (Hex.ZMod64.ofNat p c) = (c : ZMod p) :=
    HexModArithMathlib.ZMod64.toZMod_natCast c
  rw [hc] at h
  exact h

/-- Canonical residue zero tests are exact in Mathlib. -/
theorem isZero_mod_iff {a : PolyList Nat}
    (ha : Hex.MvPoly.Kernel.CanonicalMod p n a) :
    Hex.MvPoly.Kernel.isZero a = true ↔ denoteMod p (cmp := cmp) a = 0 := by
  rw [Hex.MvPoly.Kernel.isZero_mod_iff p (cmp := cmp) ha]
  exact (map_eq_zero_iff (residueEquiv p (cmp := cmp))
    (residueEquiv p (cmp := cmp)).injective).symm

/-- Canonical residue equality tests are exact in Mathlib. -/
theorem beq_mod_iff {a b : PolyList Nat}
    (ha : Hex.MvPoly.Kernel.CanonicalMod p n a)
    (hb : Hex.MvPoly.Kernel.CanonicalMod p n b) :
    Hex.MvPoly.Kernel.beq a b = true ↔
      denoteMod p (cmp := cmp) a = denoteMod p (cmp := cmp) b := by
  rw [Hex.MvPoly.Kernel.beq_mod_iff p (cmp := cmp) ha hb]
  exact (residueEquiv p (cmp := cmp)).injective.eq_iff.symm

/-- The complete producer encoding denotes the corresponding Mathlib polynomial. -/
theorem denoteMod_ofResidues (a : MvPoly n (Hex.ZMod64 p) cmp) :
    denoteMod p (cmp := cmp) (Hex.MvPoly.Kernel.ofResidues p (Hex.MvPoly.Kernel.toList a)) =
      residueEquiv p (cmp := cmp) a := by
  exact congrArg (residueEquiv p) (Hex.MvPoly.Kernel.denoteMod_ofResidues p (cmp := cmp) a)

end HexMvPolyMathlib.Kernel
