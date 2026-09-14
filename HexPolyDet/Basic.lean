/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss
public import HexMvPoly.Kernel
public import HexMvGcd.Divide
public import HexMvGcd.Instances

@[expose] public section

namespace Hex.PolyDet

open Hex.Matrix

/-- Canonical list arithmetic supplied to the generic determinant checker. -/
def ops {C : Type} [Lean.Grind.CommRing C] [BEq C] [DecidableEq C]
    (k : Nat) : DetOps (MvPoly.Kernel.PolyList C) where
  zero := []
  one := MvPoly.Kernel.one k
  add := MvPoly.Kernel.add
  mul := MvPoly.Kernel.mul
  neg := MvPoly.Kernel.neg
  beq := MvPoly.Kernel.beq
  valid := MvPoly.Kernel.isCanonical k

variable {k n : Nat} {C : Type} {cmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] [Lean.Grind.CommRing C]
  [DecidableEq C] [BEq C] [LawfulBEq C]

/-- Producer-side conversion to canonical exponent order in `O(T log T)`
comparisons. The kernel validates the resulting list; it never runs this sort.
Unlike insertion normalization this remains efficient for grevlex polynomials. -/
def toList (p : MvPoly k C cmp) : MvPoly.Kernel.PolyList C :=
  (p.termsList.map fun (m, c) => (m.toList, c)).mergeSort
    (fun a b => (compare a.1 b.1).isGE)

/-- Check the polynomial witness using canonical lists in compiled code.
Kernel quotation uses integer coefficients; residue quotation additionally
requires the reduced-Nat adapter from #10257. -/
def check (n : Nat) (rows : List (List (MvPoly k C cmp)))
    (w : DetWitness (MvPoly k C cmp)) : Bool :=
  checkDetPolyList (ops k) n (rows.map (List.map toList)) (w.map toList)

variable [Dvd C] [GcdOps C] [IsMonomialOrder cmp] [LawfulGcdOps C]

/-- Fraction-free elimination with polynomial exact division and a retained
transform, accepting the witness only after the compiled list check. -/
def polyDetWitness (P : Matrix (MvPoly k C cmp) n n) :
    Except String (DetWitness (MvPoly k C cmp)) :=
  detWitnessWith Hex.exactDiv n (check n) (P.rows.toList.map (·.toList))

/-- Row-pivoted Bareiss determinant at the polynomial coefficient domain. -/
def polyDet (P : Matrix (MvPoly k C cmp) n n) : MvPoly k C cmp :=
  Matrix.bareissWith Hex.exactDiv P

/-- The checked witness, with failure represented by `none`. -/
def polyDetWitness? (P : Matrix (MvPoly k C cmp) n n) :
    Option (DetWitness (MvPoly k C cmp)) := (polyDetWitness P).toOption

end Hex.PolyDet
