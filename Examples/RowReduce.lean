/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRowReduceMathlib
import HexRationalFnMathlib
import HexModArithMathlib
import HexPolyFp.PrimeField

/-!
Proof checks of field inversion, complete affine solving, and inconsistency
certificates. Rational and rational-function calls select the Mathlib-induced
field before constructing values. Modular calls keep the executable field and
transport their answers entrywise to `ZMod`.
-/

namespace Examples.RowReduce
open HexMatrixMathlib
attribute [local instance 2000] Field.toGrindField

example (A B : Hex.Matrix Rat n n) (h : Hex.Matrix.inverse? A = some B) :
    matrixEquiv B = (matrixEquiv A)⁻¹ := inverse?_eq_inv A B h

example (A : Hex.Matrix Rat n m) (b : Vector Rat n) (s : Hex.Matrix.SolveData A)
    (h : Hex.Matrix.solve? A b = some s) (x : Fin m → Rat) :
    (matrixEquiv A).mulVec x = vectorEquiv b ↔
      ∃! c : Fin (m - Hex.Matrix.rowReduce_rank A) → Rat,
        x = vectorEquiv s.1 + (matrixEquiv s.2).mulVec c :=
  solve?_parameters A b s h x

abbrev RF := Hex.RationalFn Rat

example (A B : Hex.Matrix RF n n) (h : Hex.Matrix.inverse? A = some B) :
    matrixEquiv B = (matrixEquiv A)⁻¹ := inverse?_eq_inv A B h

example (A : Hex.Matrix RF n m) (b : Vector RF n) :
    Hex.Matrix.solve? A b = none ↔
      ∃ y : Fin n → RF, Matrix.vecMul y (matrixEquiv A) = 0 ∧
        dotProduct y (vectorEquiv b) ≠ 0 := solve?_none_witness A b

example (A : Hex.Matrix RF n m) (b : Vector RF n) (s : Hex.Matrix.SolveData A)
    (h : Hex.Matrix.solve? A b = some s) (x : Fin m → RF) :
    (matrixEquiv A).mulVec x = vectorEquiv b ↔
      ∃! c : Fin (m - Hex.Matrix.rowReduce_rank A) → RF,
        x = vectorEquiv s.1 + (matrixEquiv s.2).mulVec c :=
  solve?_parameters A b s h x

-- Interpret the executable rational-function answers in Mathlib's RatFunc field.
private noncomputable abbrev rfEquiv := HexRationalFnMathlib.equiv (K := Rat)

example (A B : Hex.Matrix RF n n) (h : Hex.Matrix.inverse? A = some B) :
    (matrixEquiv A).map rfEquiv * (matrixEquiv B).map rfEquiv = 1 ∧
      (matrixEquiv B).map rfEquiv * (matrixEquiv A).map rfEquiv = 1 := by
  obtain ⟨hl, hr⟩ := Hex.Matrix.inverse?_spec A B h
  have hi : matrixEquiv (Hex.Matrix.identity (R := RF) n) = 1 := matrixEquiv_one
  constructor
  · rw [← Matrix.map_mul, ← matrixEquiv_mul, hl, hi]
    exact Matrix.map_one _ (map_zero rfEquiv) (map_one rfEquiv)
  · rw [← Matrix.map_mul, ← matrixEquiv_mul, hr, hi]
    exact Matrix.map_one _ (map_zero rfEquiv) (map_one rfEquiv)

example (A : Hex.Matrix RF n m) (b : Vector RF n) (s : Hex.Matrix.SolveData A)
    (h : Hex.Matrix.solve? A b = some s) :
    ((matrixEquiv A).map rfEquiv).mulVec (rfEquiv ∘ vectorEquiv s.1) =
      rfEquiv ∘ vectorEquiv b := by
  have hp := (solve?_spec A b s h).1
  funext i
  have hm : rfEquiv ((matrixEquiv A).mulVec (vectorEquiv s.1) i) =
      ((matrixEquiv A).map rfEquiv).mulVec (rfEquiv ∘ vectorEquiv s.1) i :=
    RingHom.map_mulVec rfEquiv.toRingHom (matrixEquiv A) (vectorEquiv s.1) i
  exact hm.symm.trans (congrArg (fun v : Fin n → RF => rfEquiv (v i)) hp)

example : (matrixEquiv (Hex.Matrix.identity (R := Rat) 0)).det = 1 := by simp
example : Hex.Matrix.inverse? (Hex.Matrix.identity (R := Rat) 0) =
    some (Hex.Matrix.identity 0) := by decide +kernel
example : (Hex.Matrix.solve? (Hex.Matrix.identity (R := Rat) 0) #v[]).isSome := by
  rw [Hex.Matrix.solve?_isSome]
  exact ⟨#v[], Hex.Matrix.identity_mulVec _⟩

private def singular : Hex.Matrix Rat 2 2 := Hex.Matrix.ofFn fun i j =>
  if i.val = 0 ∧ j.val = 0 then 1 else 0

example : Hex.Matrix.inverse? singular = none := by
  rw [inverse?_eq_none]
  have hm : matrixEquiv singular = !![(1 : Rat), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hm, Matrix.det_fin_two]
  norm_num

private def inconsistent : Hex.Matrix Rat 2 3 := Hex.Matrix.ofFn fun _ j =>
  if j.val = 0 then 1 else 0

example : Hex.Matrix.solve? inconsistent #v[0, 1] = none := by
  rw [solve?_none_witness]
  refine ⟨![(-1 : Rat), 1], ?_, ?_⟩
  · rw [inconsistent, matrixEquiv_ofFn]
    ext j
    fin_cases j <;> norm_num [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · norm_num [dotProduct, Fin.sum_univ_two, vectorEquiv]

namespace Modular
noncomputable section
-- No Mathlib field on ZMod64 is needed: only its ring equivalence.
variable {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
  [Fact (Nat.Prime p)]

private abbrev e := HexModArithMathlib.ZMod64.equiv (p := p)
private def vm (v : Vector (Hex.ZMod64 p) n) : Fin n → ZMod p := fun i => e v[i]
private def mm (A : Hex.Matrix (Hex.ZMod64 p) n m) : Matrix (Fin n) (Fin m) (ZMod p) :=
  fun i j => e A[i][j]

omit [Hex.ZMod64.PrimeModulus p] in
private theorem dot_map (v w : Vector (Hex.ZMod64 p) n) :
    e (Vector.dotProduct v w) = dotProduct (vm v) (vm w) := by
  have hf (xs : List (Fin n)) (z : Hex.ZMod64 p) :
      e (xs.foldl (fun a i => a + v[i] * w[i]) z) =
        xs.foldl (fun a i => a + e v[i] * e w[i]) (e z) := by
    induction xs generalizing z with
    | nil => rfl
    | cons i xs ih => simpa only [List.foldl_cons, map_add, map_mul] using ih (z + v[i] * w[i])
  unfold Vector.dotProduct
  have hz : e (0 : Hex.ZMod64 p) = 0 := HexModArithMathlib.ZMod64.toZMod_zero
  rw [hf, hz, foldl_finRange_eq_sum]
  rfl

omit [Hex.ZMod64.PrimeModulus p] in
private theorem mv_map (A : Hex.Matrix (Hex.ZMod64 p) n m) (x : Vector (Hex.ZMod64 p) m) :
    vm (A * x) = (mm A).mulVec (vm x) := by
  funext i
  change e ((A * x)[i]) = _
  rw [Hex.Matrix.getElem_mulVec, dot_map]
  rfl

omit [Hex.ZMod64.PrimeModulus p] [Fact (Nat.Prime p)] in
private theorem vm_injective : Function.Injective (vm (p := p) (n := n)) := by
  intro x y h
  apply Vector.ext
  intro i hi
  exact e.injective (congrFun h ⟨i, hi⟩)

omit [Hex.ZMod64.PrimeModulus p] [Fact (Nat.Prime p)] in
private theorem vm_surjective : Function.Surjective (vm (p := p) (n := n)) := by
  intro x
  refine ⟨Vector.ofFn (fun i => e.symm (x i)), ?_⟩
  funext i
  simp [vm]

omit [Hex.ZMod64.PrimeModulus p] in
private theorem vm_zero : vm (0 : Vector (Hex.ZMod64 p) n) = 0 := by
  funext i
  change e ((0 : Vector (Hex.ZMod64 p) n)[i.val]) = 0
  rw [Vector.getElem_zero]
  exact HexModArithMathlib.ZMod64.toZMod_zero

omit [Hex.ZMod64.PrimeModulus p] in
private theorem vm_add (x y : Vector (Hex.ZMod64 p) n) : vm (x + y) = vm x + vm y := by
  funext i
  change e ((x + y)[i.val]) = e x[i.val] + e y[i.val]
  have h := Vector.getElem_add x y i.val i.isLt
  rw [h, map_add]

example (A : Hex.Matrix (Hex.ZMod64 p) n m) (b : Vector (Hex.ZMod64 p) n) :
    Hex.Matrix.solve? A b = none ↔ ¬ ∃ x, (mm A).mulVec x = vm b := by
  rw [Hex.Matrix.solve?_eq_none]
  apply not_congr
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨vm x, by rw [← mv_map, hx]⟩
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := vm_surjective x
    exact ⟨v, vm_injective (by rwa [mv_map])⟩

example (A : Hex.Matrix (Hex.ZMod64 p) n m) (b : Vector (Hex.ZMod64 p) n)
    (s : Hex.Matrix.SolveData A) (h : Hex.Matrix.solve? A b = some s) (x : Fin m → ZMod p) :
    (mm A).mulVec x = vm b ↔
      ∃! c : Fin (m - Hex.Matrix.rowReduce_rank A) → ZMod p,
        x = vm s.1 + (mm s.2).mulVec c := by
  obtain ⟨v, rfl⟩ := vm_surjective x
  have hv : (mm A).mulVec (vm v) = vm b ↔ A * v = b := by
    rw [← mv_map, vm_injective.eq_iff]
  rw [hv, (Hex.Matrix.solve?_spec A b s h).2.2]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨vm c, ?_, ?_⟩
    · rw [hc, vm_add, mv_map]
    · intro d hd
      obtain ⟨w, rfl⟩ := vm_surjective d
      apply congrArg vm
      apply Hex.Matrix.solve?_unique A b s _ _ h
      apply vm_injective
      rw [mv_map, mv_map]
      have he := congrArg vm hc
      rw [vm_add, mv_map] at he
      exact add_left_cancel (hd.symm.trans he)
  · rintro ⟨c, hc, _⟩
    obtain ⟨w, rfl⟩ := vm_surjective c
    exact ⟨w, vm_injective (by simpa only [vm_add, mv_map] using hc)⟩

omit [Hex.ZMod64.PrimeModulus p] in
private theorem mm_mul (A : Hex.Matrix (Hex.ZMod64 p) n m)
    (B : Hex.Matrix (Hex.ZMod64 p) m k) : mm (A * B) = mm A * mm B := by
  ext i j
  change e ((A * B)[i][j]) = _
  rw [Hex.Matrix.getElem_mul, dot_map]
  simp only [dotProduct, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  change e ((Hex.Matrix.row A i)[l]) * e ((Hex.Matrix.col B j)[l]) =
    e A[i][l] * e B[l][j]
  rw [Hex.Matrix.getElem_row, Hex.Matrix.getElem_col]

omit [Hex.ZMod64.PrimeModulus p] in
private theorem mm_identity : mm (Hex.Matrix.identity (R := Hex.ZMod64 p) n) = 1 := by
  ext i j
  change e ((Hex.Matrix.identity n)[i][j]) = _
  rw [Hex.Matrix.getElem_identity, Matrix.one_apply]
  split <;> simp_all only [e, HexModArithMathlib.ZMod64.equiv_apply,
    HexModArithMathlib.ZMod64.toZMod_zero, HexModArithMathlib.ZMod64.toZMod_one]

example (A B : Hex.Matrix (Hex.ZMod64 p) n n) (h : Hex.Matrix.inverse? A = some B) :
    mm A * mm B = 1 ∧ mm B * mm A = 1 := by
  obtain ⟨hl, hr⟩ := Hex.Matrix.inverse?_spec A B h
  constructor
  · rw [← mm_mul, hl, mm_identity]
  · rw [← mm_mul, hr, mm_identity]

omit [Hex.ZMod64.PrimeModulus p] in
private theorem vm_vecMul (y : Vector (Hex.ZMod64 p) n)
    (A : Hex.Matrix (Hex.ZMod64 p) n m) :
    vm (Hex.Matrix.vecMul y A) = Matrix.vecMul (vm y) (mm A) := by
  funext j
  change e ((Hex.Matrix.vecMul y A)[j]) = _
  rw [Hex.Matrix.vecMul, Hex.Matrix.getElem_mulVec, Hex.Matrix.row_transpose, dot_map]
  change (∑ i : Fin n, e ((Hex.Matrix.col A j)[i]) * e y[i]) =
    ∑ i : Fin n, e y[i] * e A[i][j]
  apply Finset.sum_congr rfl
  intro i _
  rw [Hex.Matrix.getElem_col, mul_comm]

example (A : Hex.Matrix (Hex.ZMod64 p) n m) (b y : Vector (Hex.ZMod64 p) n)
    (h : Hex.Matrix.solve A b = .error y) :
    Matrix.vecMul (vm y) (mm A) = 0 ∧ dotProduct (vm y) (vm b) ≠ 0 := by
  obtain ⟨ha, hb⟩ := Hex.Matrix.solve_error A b y h
  constructor
  · rw [← vm_vecMul, ha]
    exact vm_zero
  · intro hz
    apply hb
    apply e.injective
    rw [dot_map, hz]
    exact HexModArithMathlib.ZMod64.toZMod_zero.symm

example (A : Hex.Matrix (Hex.ZMod64 p) n m) (b : Vector (Hex.ZMod64 p) n) :
    Hex.Matrix.solve? A b = none ↔
      ∃ y, Matrix.vecMul y (mm A) = 0 ∧ dotProduct y (vm b) ≠ 0 := by
  rw [Hex.Matrix.solve?_none_witness]
  constructor
  · rintro ⟨y, ha, hb⟩
    refine ⟨vm y, ?_, ?_⟩
    · rw [← vm_vecMul, ha]
      exact vm_zero
    · intro hz
      apply hb
      apply e.injective
      rw [dot_map, hz]
      exact HexModArithMathlib.ZMod64.toZMod_zero.symm
  · rintro ⟨y, ha, hb⟩
    obtain ⟨v, rfl⟩ := vm_surjective y
    refine ⟨v, vm_injective ?_, ?_⟩
    · rw [vm_vecMul, ha]
      exact vm_zero.symm
    · intro hz
      apply hb
      rw [← dot_map, hz]
      exact HexModArithMathlib.ZMod64.toZMod_zero

end
end Modular
end Examples.RowReduce
