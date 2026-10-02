/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal.Kernel
public import HexMvPoly.KernelResidue.Denote

@[expose] public section

namespace Hex.Matrix

open Hex.MvPoly.Kernel

/-- Polynomial residue arithmetic keeps machine words off the kernel path. -/
def MinorArithmetic.residue (p k : Nat) : MinorArithmetic (PolyList Nat) where
  zero := []
  one := oneMod p k
  add := addMod p
  mul := mulMod p
  neg := negMod p
  isZero := Hex.MvPoly.Kernel.isZero
  beq := Hex.MvPoly.Kernel.beq

-- The coefficient carrier has a direct `Zero` instance. Supplying the
-- polynomial ring explicitly lets elaboration reconcile it with the numeral
-- zero carried by `Lean.Grind.CommRing`.
local instance residueRing (p k : Nat) [ZMod64.Bounds p]
    (cmp : Mono k → Mono k → Ordering) [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    Lean.Grind.CommRing (MvPoly k (ZMod64 p) cmp) :=
  @MvPoly.instGrindCommRing k (ZMod64 p) cmp inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance

/-- The canonical residue interpretation, including equality reflection. -/
def MinorArithmetic.residueInterpretation (p : Nat) [ZMod64.Bounds p] {k : Nat}
    {cmp : Mono k → Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] :
    (MinorArithmetic.residue p k).Interpretation (MvPoly k (ZMod64 p) cmp) where
  Valid := CanonicalMod p k
  denote := denoteMod p
  valid_zero := by simp [MinorArithmetic.residue, CanonicalMod, Canonical]
  valid_one := oneMod_canonical p k
  valid_add := addMod_canonical p
  valid_mul := mulMod_canonical p
  valid_neg := negMod_canonical p
  denote_zero := rfl
  denote_one := denoteMod_oneMod p
  denote_add := denoteMod_addMod p
  denote_mul := denoteMod_mulMod p
  denote_neg := denoteMod_negMod p
  isZero_iff := isZero_mod_iff p
  beq_iff := beq_mod_iff p

namespace Residue

/-- Reduction of a signed coefficient uses only integer remainder. -/
def coefficient (p : Nat) (c : Int) : Nat := (c % (p : Int)).toNat

/-- One reduced term, omitting a zero coefficient. -/
def term (p : Nat) (t : Term Int) : PolyList Nat :=
  let c := coefficient p t.2
  if Nat.beq c 0 then [] else [(t.1, c)]

/-- Normalize arbitrary reflected terms directly with natural residue arithmetic. -/
def reduce (p : Nat) : PolyList Int → PolyList Nat
  | [] => []
  | t :: ts => addMod p (term p t) (reduce p ts)

variable (p : Nat) [ZMod64.Bounds p]

theorem coefficient_eq (c : Int) : coefficient p c = (ZMod64.intCast p c).toNat := by
  have h := congrArg Int.toNat (ZMod64.toNat_intCast (p := p) c)
  simpa only [coefficient, Int.toNat_natCast] using h.symm

theorem term_canonical {k : Nat} (t : Term Int) (ht : t.1.length = k) :
    CanonicalMod p k (term p t) := by
  simp only [term]
  split
  · simp [CanonicalMod, Canonical]
  · rename_i h
    have hc : coefficient p t.2 ≠ 0 := by simpa only [Nat.beq_eq] using h
    have hb : coefficient p t.2 < p := by rw [coefficient_eq]; exact ZMod64.toNat_lt _
    simp [CanonicalMod, Canonical, ht, hc, hb]

theorem reduce_canonical {k : Nat} (a : PolyList Int) (ha : ∀ t ∈ a, t.1.length = k) :
    CanonicalMod p k (reduce p a) := by
  induction a with
  | nil => simp [reduce, CanonicalMod, Canonical]
  | cons t ts ih =>
    exact addMod_canonical p (term_canonical p t (ha t (by simp)))
      (ih (fun u hu => ha u (by simp [hu])))

variable {k : Nat} {cmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

theorem denote_term (t : Term Int) :
    denoteMod p (cmp := cmp) (term p t) = MvPoly.monomial (mono k t.1) (ZMod64.intCast p t.2) := by
  have hc : ZMod64.ofNat p (coefficient p t.2) = ZMod64.intCast p t.2 := by
    rw [coefficient_eq, ZMod64.ofNat_toNat]
  simp only [term]
  split
  · rename_i h
    have he : coefficient p t.2 = 0 := Nat.beq_eq.mp h
    rw [he] at hc
    rw [← hc]
    change (0 : MvPoly k (ZMod64 p) cmp) = MvPoly.monomial (mono k t.1) 0
    apply MvPoly.ext
    intro e
    simp only [MvPoly.coeff_monomial, MvPoly.coeff_zero]
    split <;> rfl
  · simp only [denoteMod, toResidues, CoeffMap.map, List.map_cons, List.map_nil,
      denote, hc]
    exact MvPoly.add_zero _

/-- Reduction denotes the original reflected polynomial in the residue ring. -/
theorem denote_reduce (a : PolyList Int) (ha : ∀ t ∈ a, t.1.length = k) :
    denoteMod p (cmp := cmp) (reduce p a) =
      denote (cmp := cmp) (CoeffMap.map (ZMod64.intCast p) a) := by
  induction a with
  | nil => rfl
  | cons t ts ih =>
    rw [reduce, denoteMod_addMod p (term_canonical p t (ha t (by simp)))
      (reduce_canonical p ts (fun u hu => ha u (by simp [hu]))),
      denote_term, ih (fun u hu => ha u (by simp [hu]))]
    rfl

end Residue

/-- Transport a complete residue generator list to its polynomial matrix. -/
theorem detIdealGensMod_denote (p : Nat) [ZMod64.Bounds p] {k : Nat}
    {cmp : Mono k → Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (L : List (List (PolyList Nat))) (P : Matrix (MvPoly k (ZMod64 p) cmp) n m)
    (hL : ∀ row ∈ L, ∀ a ∈ row, CanonicalMod p k a)
    (hP : L.map (List.map (denoteMod p)) = rowLists P) (r : Nat) :
    (detIdealGensList (MinorArithmetic.residue p k) r L).map (denoteMod p) = detIdealGens r P :=
  (MinorArithmetic.residueInterpretation p).denote_gens L hL P hP r

/-- Transport just the selected residue minor and its index memberships. -/
theorem minorMod_mem (p : Nat) [ZMod64.Bounds p] {k : Nat}
    {cmp : Mono k → Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (L : List (List (PolyList Nat))) (P : Matrix (MvPoly k (ZMod64 p) cmp) n m)
    (hL : ∀ row ∈ L, ∀ a ∈ row, CanonicalMod p k a)
    (hP : L.map (List.map (denoteMod p)) = rowLists P) (r : Nat)
    (rows cols : List Nat) (hr : rows ∈ indexTuples r n) (hc : cols ∈ indexTuples r m) :
    denoteMod p (minorList (MinorArithmetic.residue p k) rows cols L) ∈ minors r P :=
  (MinorArithmetic.residueInterpretation p).minor_mem L hL P hP r rows cols hr hc

end Hex.Matrix
