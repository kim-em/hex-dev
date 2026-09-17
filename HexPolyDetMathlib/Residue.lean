/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib.Sound
public import HexReflectMathlib.KernelResidue
public import Mathlib.Algebra.Field.ZMod

public section

namespace HexMatrixMathlib.DetPoly.Residue

open Hex Hex.Matrix Hex.MvPoly.Kernel
open HexMvPolyMathlib.Kernel (denoteMod)
open scoped HexMvPolyMathlib HexModArithMathlib.ZMod64

variable (p : Nat) [Hex.ZMod64.Bounds p]

/-- Interpret the shared residue operations in Mathlib's polynomial ring. -/
noncomputable def decode (k : Nat) :
    Decode (Hex.PolyDet.opsMod p k) (MvPolynomial (Fin k) (ZMod p)) where
  eval := denoteMod p (n := k) (cmp := Mono.grevlex)
  zero := HexMvPolyMathlib.Kernel.denoteMod_nil p
  one := HexMvPolyMathlib.Kernel.denoteMod_oneMod p
  valid_zero := rfl
  valid_one := isCanonicalMod_iff.mpr (oneMod_canonical p k)
  valid_add _ _ ha hb := isCanonicalMod_iff.mpr
    (addMod_canonical p (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb))
  valid_mul _ _ ha hb := isCanonicalMod_iff.mpr
    (mulMod_canonical p (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb))
  valid_neg _ ha := isCanonicalMod_iff.mpr (negMod_canonical p (isCanonicalMod_iff.mp ha))
  add _ _ ha hb := HexMvPolyMathlib.Kernel.denoteMod_addMod p
    (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb)
  mul _ _ ha hb := HexMvPolyMathlib.Kernel.denoteMod_mulMod p
    (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb)
  neg _ ha := HexMvPolyMathlib.Kernel.denoteMod_negMod p (isCanonicalMod_iff.mp ha)
  beq _ _ ha hb := HexMvPolyMathlib.Kernel.beq_mod_iff p
    (isCanonicalMod_iff.mp ha) (isCanonicalMod_iff.mp hb)

/-- The polynomial value carried by a residue witness. -/
@[expose] def value : DetWitness (PolyList Nat) → PolyList Nat
  | .triangular _ _ d => d
  | .singular _ => []

variable {F : Type u} [CommRing F] [CharP F p]

/-- Evaluation factors through the residue polynomial equivalence. -/
noncomputable def hom (k : Nat) (ctx : Lean.RArray F) :
    MvPolynomial (Fin k) (ZMod p) →+* F :=
  (HexReflectMathlib.Kernel.homMod p k ctx).comp
    (HexMvPolyMathlib.Kernel.residueEquiv p (cmp := Mono.grevlex)).symm.toRingHom

theorem eval_denote (k : Nat) (ctx : Lean.RArray F) (a : PolyList Nat) :
    hom p k ctx (denoteMod p (cmp := Mono.grevlex) a) =
      HexReflectMathlib.Kernel.homMod p k ctx (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) a) := by
  simp [hom, HexMvPolyMathlib.Kernel.denoteMod]

/-- Entry interpretation reduces direct list accesses outside certificate arithmetic. -/
noncomputable abbrev evaluated (k n : Nat) (rows : List (List (PolyList Nat)))
    (ctx : Lean.RArray F) : Matrix (Fin n) (Fin n) F :=
  ofLists n n (rows.map (List.map (fun a =>
    HexReflectMathlib.Kernel.homMod p k ctx (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) a))))

theorem evaluated_eq (k n : Nat) (rows : List (List (PolyList Nat))) (ctx : Lean.RArray F) :
    evaluated p k n rows ctx = ((decode p k).matrix n rows).map (hom p k ctx) := by
  ext i j
  simp only [evaluated, Decode.matrix, Matrix.map_apply, ofLists_apply, decode]
  rw [show (rows.map (List.map (fun a => HexReflectMathlib.Kernel.homMod p k ctx
        (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) a)))).getD i [] =
      (rows.getD i []).map (fun a => HexReflectMathlib.Kernel.homMod p k ctx
        (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) a)) from List.getD_map rows [] _,
    show (rows.map (List.map (HexMvPolyMathlib.Kernel.denoteMod p (n := k) (cmp := Mono.grevlex)))).getD i [] =
      (rows.getD i []).map (HexMvPolyMathlib.Kernel.denoteMod p (n := k) (cmp := Mono.grevlex)) from List.getD_map rows [] _]
  rw [← map_zero (hom p k ctx), ← List.getD_map _ _ (hom p k ctx), List.map_map]
  simp only [Function.comp_def, eval_denote]

/-- Read an evaluated entry without reducing residue polynomial denotation. -/
theorem evaluated_apply (k n : Nat) (rows : List (List (PolyList Nat)))
    (ctx : Lean.RArray F) (i j : Fin n) :
    evaluated p k n rows ctx i j = HexReflectMathlib.Kernel.homMod p k ctx
      (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) ((rows.getD i []).getD j [])) := by
  let f := fun a => HexReflectMathlib.Kernel.homMod p k ctx
    (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) a)
  have hz : f [] = 0 := map_zero _
  simp only [evaluated, ofLists_apply]
  change ((rows.map (List.map f)).getD i []).getD j 0 = _
  rw [show (rows.map (List.map f)).getD i [] = (rows.getD i []).map f from List.getD_map rows [] _,
    ← hz, List.getD_map]

/-- Entry proofs identify the matrix through structural list access only. -/
theorem identify (k n : Nat) (rows : List (List (PolyList Nat))) (ctx : Lean.RArray F)
    (A : Matrix (Fin n) (Fin n) F)
    (h : Polynomial.AllFin n (fun i => Polynomial.AllFin n (fun j =>
      A i j = HexReflectMathlib.Kernel.homMod p k ctx
        (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) ((rows.getD i []).getD j []))))) :
    A = evaluated p k n rows ctx := by
  ext i j
  rw [evaluated_apply]
  exact Polynomial.allFin n _ (Polynomial.allFin n _ h i) j

/-- A passing residue certificate determines the determinant after any valuation. -/
theorem result [Hex.ZMod64.PrimeModulus p] (k n : Nat) (rows : List (List (PolyList Nat)))
    (w : DetWitness (PolyList Nat)) (ctx : Lean.RArray F)
    (A : Matrix (Fin n) (Fin n) F) (e : F)
    (hcheck : checkDetPolyList (Hex.PolyDet.opsMod p k) n rows w = true)
    (hA : A = evaluated p k n rows ctx)
    (he : HexReflectMathlib.Kernel.homMod p k ctx
      (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) (value w)) = e) : A.det = e := by
  let : Fact (Nat.Prime p) := ⟨Nat.prime_def.mpr Hex.ZMod64.PrimeModulus.prime⟩
  have hs := (decode p k).transport (hom p k ctx) n rows w A hcheck
    (hA.trans (evaluated_eq p k n rows ctx))
  cases w with
  | triangular s t d => exact hs.trans ((eval_denote p k ctx d).trans he)
  | singular v => simpa [value] using hs.trans (by simpa [value] using he)

/-- Target agreement is structural equality of canonical natural-residue lists. -/
theorem target [Hex.ZMod64.PrimeModulus p] (k n : Nat) (rows : List (List (PolyList Nat)))
    (w : DetWitness (PolyList Nat)) (ctx : Lean.RArray F)
    (A : Matrix (Fin n) (Fin n) F) (q : PolyList Nat) (e : F)
    (hcheck : checkDetPolyList (Hex.PolyDet.opsMod p k) n rows w = true)
    (hA : A = evaluated p k n rows ctx)
    (he : HexReflectMathlib.Kernel.homMod p k ctx
      (Hex.MvPoly.Kernel.denoteMod p (cmp := Mono.grevlex) q) = e)
    (hq : beq (value w) q = true) : A.det = e := by
  apply result p k n rows w ctx A e hcheck hA
  rwa [beq_eq_true_iff.mp hq]

end HexMatrixMathlib.DetPoly.Residue
