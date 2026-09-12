/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.Equiv

public section

/-!
Mathlib denotation of canonical kernel term lists.

This is deliberately only a semantic bridge. Certificate computation remains
in `Hex.MvPoly.Kernel`, over ordinary lists and primitive coefficient
arithmetic; the bridge transports its proved denotation through the ring
equivalence with `MvPolynomial`.
-/

namespace HexMvPolyMathlib.Kernel

open Hex
open Hex.MvPoly
open scoped HexMvPolyMathlib

universe u

abbrev Term := Hex.MvPoly.Kernel.Term
abbrev PolyList := Hex.MvPoly.Kernel.PolyList

/-- Denote a kernel term list as a Mathlib multivariate polynomial. -/
noncomputable def denote {n : Nat} {R : Type u} [CommSemiring R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p : PolyList R) : MvPolynomial (Fin n) R :=
  HexMvPolyMathlib.equiv (cmp := cmp) (Hex.MvPoly.Kernel.denote (cmp := cmp) p)

/-- List addition has the same denotation as Mathlib addition. -/
theorem denote_add {n : Nat} {R : Type u} [CommSemiring R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p q : PolyList R) :
    denote (cmp := cmp) (Hex.MvPoly.Kernel.add p q) =
      denote (cmp := cmp) p + denote (cmp := cmp) q := by
  unfold denote
  rw [Hex.MvPoly.Kernel.denote_add, map_add]

/-- List multiplication has the same denotation as Mathlib multiplication. -/
theorem denote_mul {n : Nat} {R : Type u} [CommSemiring R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p q : PolyList R)
    (hp : ∀ t ∈ p, t.1.length = n) (hq : ∀ t ∈ q, t.1.length = n) :
    denote (cmp := cmp) (Hex.MvPoly.Kernel.mul p q) =
      denote (cmp := cmp) p * denote (cmp := cmp) q := by
  unfold denote
  rw [Hex.MvPoly.Kernel.denote_mul p q hp hq, map_mul]

/-- List negation has the same denotation as Mathlib negation. -/
theorem denote_neg {n : Nat} {R : Type u} [CommRing R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p : PolyList R) :
    denote (cmp := cmp) (Hex.MvPoly.Kernel.neg p) = -denote (cmp := cmp) p := by
  unfold denote
  rw [Hex.MvPoly.Kernel.denote_neg, map_neg]

/-- List scalar multiplication denotes multiplication by a Mathlib constant. -/
theorem denote_smul {n : Nat} {R : Type u} [CommSemiring R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (a : R) (p : PolyList R) :
    denote (cmp := cmp) (Hex.MvPoly.Kernel.smul a p) =
      MvPolynomial.C a * denote (cmp := cmp) p := by
  unfold denote
  rw [Hex.MvPoly.Kernel.denote_smul, map_mul,
    HexMvPolyMathlib.equiv_apply, HexMvPolyMathlib.toMvPolynomial_C]

/-- Producer conversion reads as the corresponding Mathlib polynomial. -/
theorem denote_toList {n : Nat} {R : Type u} [CommSemiring R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] (p : MvPoly n R cmp) :
    denote (cmp := cmp) (Hex.MvPoly.Kernel.toList p) =
      HexMvPolyMathlib.equiv (cmp := cmp) p := by
  unfold denote
  rw [Hex.MvPoly.Kernel.denote_toList]

/-- The list zero test agrees with zero Mathlib denotation on canonical
inputs. -/
theorem isZero_iff {n : Nat} {R : Type u} [CommSemiring R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] {p : PolyList R}
    (hp : Hex.MvPoly.Kernel.Canonical n p) :
    Hex.MvPoly.Kernel.isZero p = true ↔ denote (cmp := cmp) p = 0 := by
  rw [Hex.MvPoly.Kernel.isZero_iff (cmp := cmp) hp]
  constructor
  · intro h
    unfold denote
    rw [h, map_zero]
  · intro h
    apply (HexMvPolyMathlib.equiv (cmp := cmp)).injective
    simpa [denote] using h

/-- The list equality test agrees with equality of Mathlib denotations on
canonical inputs. -/
theorem beq_iff {n : Nat} {R : Type u} [CommSemiring R]
    [BEq R] [LawfulBEq R] [DecidableEq R]
    {cmp : Mono n → Mono n → Ordering} [Std.TransCmp cmp]
    [Std.LawfulEqCmp cmp] {p q : PolyList R}
    (hp : Hex.MvPoly.Kernel.Canonical n p)
    (hq : Hex.MvPoly.Kernel.Canonical n q) :
    Hex.MvPoly.Kernel.beq p q = true ↔
      denote (cmp := cmp) p = denote (cmp := cmp) q := by
  rw [Hex.MvPoly.Kernel.beq_iff (cmp := cmp) hp hq]
  unfold denote
  exact (HexMvPolyMathlib.equiv (n := n) (R := R) (cmp := cmp)).injective.eq_iff.symm

end HexMvPolyMathlib.Kernel
