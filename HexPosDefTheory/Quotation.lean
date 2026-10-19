/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Scaling
public import HexMatrixTheory.Rational
public import HexPosDef.Scaled

public section

/-! Denominator-check soundness for proof-producing matrix quotation. -/

open scoped ComplexOrder

open Hex.PosDef
open Hex.Matrix.Lists (entry entry_eq_getD)
open HexMatrixTheory

namespace Hex.PosDefTheory.Quote

/-- Interpret rational rows in the requested characteristic-zero field. -/
@[expose] def rationalMatrix (R : Type*) [Field R] [CharZero R] (n : Nat)
    (rows : List (List Rat)) : _root_.Matrix (Fin n) (Fin n) R :=
  fun i j => ((entry 0 (entry [] rows i) j : Rat) : R)

/-- Integer literal identification needs no scalar normalization. -/
theorem integer_identify (A : _root_.Matrix (Fin n) (Fin n) Int) (rows : List (List Int))
    (h : A = ofLists n n rows) :
    (1 : Int) • A = Lists.matrix (intModel Int) n rows := by
  rw [one_smul,h]
  ext i j
  simp [ofLists_apply, Lists.matrix, PosDef.Lists.get, intModel, PosDef.Lists.intArithmetic, entry_eq_getD]

/-- One cross-product check identifies the entire rational scaling. -/
theorem rational_scale (R : Type*) [Field R] [CharZero R] [PartialOrder R] [StarRing R]
    [IsStrictOrderedRing R] (n d : Nat) (rows : List (List Rat)) (nums : List (List Int))
    (hd : 0 < d) (hc : Hex.Matrix.Lists.scaleRows d rows nums = true) :
    (d : R) • rationalMatrix R n rows = Lists.matrix (intModel R) n nums := by
  have he := scaleRows_sound d rows nums hd hc
  ext i j
  have hRat : (d : Rat) * entry 0 (entry [] rows i) j =
      ((entry (0 : Int) (entry [] nums i) j : Int) : Rat) := by
    simp only [entry_eq_getD]
    rw [he, decodeRows_getD]
    dsimp only [decodeScalar]
    field_simp [show (d : Rat) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hd)]
  have hcast := congrArg (fun q : Rat => (q : R)) hRat
  simpa [rationalMatrix, Lists.matrix, PosDef.Lists.get, intModel, PosDef.Lists.intArithmetic] using hcast

/-- Identify a rational literal through the shared literal route. -/
theorem rational_identify (A : _root_.Matrix (Fin n) (Fin n) Rat) (rows : List (List Rat))
    (h : A = ofLists n n rows) : A = rationalMatrix Rat n rows := by
  rw [h]
  ext i j
  simp [rationalMatrix, ofLists_apply, entry_eq_getD]

theorem entry_map {S T : Type} (f : S → T) (d : S) (xs : List S) (i : Nat) :
    entry (f d) (xs.map f) i = f (entry d xs i) := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [entry, ih]

theorem matrix_entry_map {S T : Type} (f : S → T) (d : S) (rows : List (List S))
    (i j : Nat) : entry (f d) (entry [] (rows.map (List.map f)) i) j =
      f (entry d (entry [] rows i) j) := by
  change entry (f d) (entry (List.map f []) (rows.map (List.map f)) i) j = _
  rw [entry_map, entry_map]

private theorem row_parts (d : Nat) (rows : List (Rat × Rat)) (nums : List PosDef.Gaussian)
    (h : PosDef.Gaussian.scaleRow d rows nums = true) :
    Hex.Matrix.Lists.scaleRow d (rows.map Prod.fst) (nums.map PosDef.Gaussian.re) = true ∧
    Hex.Matrix.Lists.scaleRow d (rows.map Prod.snd) (nums.map PosDef.Gaussian.im) = true := by
  induction rows generalizing nums with
  | nil => cases nums <;> simp_all [PosDef.Gaussian.scaleRow, Hex.Matrix.Lists.scaleRow]
  | cons q qs ih =>
    cases nums with
    | nil => simp [PosDef.Gaussian.scaleRow] at h
    | cons z zs =>
      simp only [PosDef.Gaussian.scaleRow, Bool.and_eq_true_iff] at h
      obtain ⟨hr,hi⟩ := ih zs h.2
      exact ⟨Bool.and_eq_true_iff.mpr ⟨h.1.1,hr⟩, Bool.and_eq_true_iff.mpr ⟨h.1.2,hi⟩⟩

private theorem rows_parts (d : Nat) (rows : List (List (Rat × Rat)))
    (nums : List (List PosDef.Gaussian)) (h : PosDef.Gaussian.scaleRows d rows nums = true) :
    Hex.Matrix.Lists.scaleRows d (rows.map (List.map Prod.fst))
      (nums.map (List.map PosDef.Gaussian.re)) = true ∧
    Hex.Matrix.Lists.scaleRows d (rows.map (List.map Prod.snd))
      (nums.map (List.map PosDef.Gaussian.im)) = true := by
  induction rows generalizing nums with
  | nil => cases nums <;> simp_all [PosDef.Gaussian.scaleRows, Hex.Matrix.Lists.scaleRows]
  | cons q qs ih =>
    cases nums with
    | nil => simp [PosDef.Gaussian.scaleRows] at h
    | cons z zs =>
      simp only [PosDef.Gaussian.scaleRows, Bool.and_eq_true_iff] at h
      obtain ⟨hr,hi⟩ := ih zs h.2
      obtain ⟨hr0,hi0⟩ := row_parts d q z h.1
      exact ⟨Bool.and_eq_true_iff.mpr ⟨hr0,hr⟩, Bool.and_eq_true_iff.mpr ⟨hi0,hi⟩⟩

/-- Interpret rational real and imaginary components without equality evaluation. -/
@[expose] def complexMatrix (n : Nat) (rows : List (List (Rat × Rat))) :
    _root_.Matrix (Fin n) (Fin n) Complex := fun i j =>
  let q := entry (0,0) (entry [] rows i) j
  ⟨(q.1 : Real), (q.2 : Real)⟩

/-- The Gaussian cross-product checker proves the entire matrix scaling,
using the existing rational denominator theorem separately on both components. -/
theorem gaussian_scale (n d : Nat) (rows : List (List (Rat × Rat)))
    (nums : List (List PosDef.Gaussian)) (hd : 0 < d)
    (hc : PosDef.Gaussian.scaleRows d rows nums = true) :
    (d : Complex) • complexMatrix n rows = Lists.matrix gaussianModel n nums := by
  obtain ⟨hr,hi⟩ := rows_parts d rows nums hc
  have hRe := rational_scale Real n d _ _ hd hr
  have hIm := rational_scale Real n d _ _ hd hi
  have hfst (rs : List (List (Rat × Rat))) (i j : Nat) :
      entry 0 (entry [] (rs.map (List.map Prod.fst)) i) j =
        (entry (0,0) (entry [] rs i) j).1 := matrix_entry_map Prod.fst (0,0) rs i j
  have hsnd (rs : List (List (Rat × Rat))) (i j : Nat) :
      entry 0 (entry [] (rs.map (List.map Prod.snd)) i) j =
        (entry (0,0) (entry [] rs i) j).2 := matrix_entry_map Prod.snd (0,0) rs i j
  have hre (rs : List (List PosDef.Gaussian)) (i j : Nat) :
      entry 0 (entry [] (rs.map (List.map PosDef.Gaussian.re)) i) j =
        (entry PosDef.Gaussian.zero (entry [] rs i) j).re :=
      matrix_entry_map PosDef.Gaussian.re PosDef.Gaussian.zero rs i j
  have him (rs : List (List PosDef.Gaussian)) (i j : Nat) :
      entry 0 (entry [] (rs.map (List.map PosDef.Gaussian.im)) i) j =
        (entry PosDef.Gaussian.zero (entry [] rs i) j).im :=
      matrix_entry_map PosDef.Gaussian.im PosDef.Gaussian.zero rs i j
  ext i j
  apply Complex.ext
  · have he := congrFun (congrFun hRe i) j
    simpa [rationalMatrix, complexMatrix, Lists.matrix, PosDef.Lists.get,
      gaussianModel, toComplex, intModel, PosDef.Lists.intArithmetic, PosDef.Lists.gaussianArithmetic, hfst, hsnd, hre, him,
      Complex.mul_re] using he
  · have he := congrFun (congrFun hIm i) j
    simpa [rationalMatrix, complexMatrix, Lists.matrix, PosDef.Lists.get,
      gaussianModel, toComplex, intModel, PosDef.Lists.intArithmetic, PosDef.Lists.gaussianArithmetic, hfst, hsnd, hre, him,
      Complex.mul_im] using he

end Hex.PosDefTheory.Quote
