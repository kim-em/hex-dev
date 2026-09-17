/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Image
public import HexModularMatrix.Bound
public import HexModArith.Modulus
public import HexModular.SymMod

public section

namespace Hex.Matrix

/-- The reusable modular inverse and determinant residue for Dixon lifting. -/
structure Decomp (n : Nat) where
  A : Matrix Int n n
  p : Nat
  [bounds : ZMod64.Bounds p]
  one_lt : 1 < p
  inv : Matrix (ZMod64 p) n n
  inv_mul : inv * A.mapEntries (ZMod64.intCast p) = Matrix.identity n
  detImage : Int
  detImage_congr : (Matrix.det A - detImage) % (p : Int) = 0
  detImage_le : 2 * detImage.natAbs ≤ p
  detImage_ne_zero : detImage ≠ 0

/-- A nonzero bounded residue certifies nonsingularity over the integers. -/
theorem Decomp.det_ne_zero (D : Decomp n) : det D.A ≠ 0 := by
  intro hz
  have hdiv : (D.p : Int) ∣ D.detImage := by
    have h := Int.dvd_of_emod_eq_zero D.detImage_congr
    rw [hz, Int.zero_sub] at h
    exact Int.dvd_neg.mp h
  have hsmall : D.detImage.natAbs < (D.p : Int).natAbs := by
    have hp := D.one_lt
    have hb := D.detImage_le
    simp only [Int.natAbs_natCast]
    omega
  exact D.detImage_ne_zero (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hsmall)

namespace Dixon

variable {p : Nat} [ZMod64.Bounds p]

/-- Gauss-Jordan state with the transform and determinant equations erased
at runtime. The factor accumulates signed pivots. -/
structure Reduction (A : Matrix (ZMod64 p) n n) where
  echelon : Matrix (ZMod64 p) n n
  transform : Matrix (ZMod64 p) n n
  factor : ZMod64 p
  transform_mul : transform * A = echelon
  det_eq : det A = factor * det echelon

def Reduction.initial (A : Matrix (ZMod64 p) n n) : Reduction A where
  echelon := A
  transform := Matrix.identity n
  factor := 1
  transform_mul := identity_mul A
  det_eq := by simp

variable {A : Matrix (ZMod64 p) n n}

def Reduction.swap (S : Reduction A) (i j : Fin n) : Reduction A where
  echelon := S.echelon.rowSwap i j
  transform := S.transform.rowSwap i j
  factor := if i = j then S.factor else -S.factor
  transform_mul := rowSwap_transform_mul_preserve i j S.transform_mul
  det_eq := by
    by_cases h : i = j
    · subst j; simpa using S.det_eq
    · rw [ite_eq_right h, det_rowSwap _ _ _ h]
      have hd := S.det_eq
      grind only

def Reduction.scale (S : Reduction A) (i : Fin n) (a b : ZMod64 p)
    (hab : a * b = 1) : Reduction A where
  echelon := S.echelon.rowScale i b
  transform := S.transform.rowScale i b
  factor := S.factor * a
  transform_mul := rowScale_transform_mul_preserve i b S.transform_mul
  det_eq := by
    rw [det_rowScale]
    have h := S.det_eq
    grind only

def Reduction.add (S : Reduction A) (i j : Fin n) (c : ZMod64 p)
    (hij : i ≠ j) : Reduction A where
  echelon := S.echelon.rowAdd i j c
  transform := S.transform.rowAdd i j c
  factor := S.factor
  transform_mul := rowAdd_transform_mul_preserve i j c S.transform_mul
  det_eq := by rw [det_rowAdd _ _ _ _ hij]; exact S.det_eq

/-- Compiled row update with specialised arithmetic and zero-multiplier skipping. -/
def Reduction.addFast (S : Reduction A) (i j : Fin n) (c : ZMod64 p)
    (hij : i ≠ j) : Reduction A where
  echelon := Word.add S.echelon i j c
  transform := Word.add S.transform i j c
  factor := S.factor
  transform_mul := by
    rw [Word.add_eq, Word.add_eq]
    exact rowAdd_transform_mul_preserve i j c S.transform_mul
  det_eq := by rw [Word.add_eq, det_rowAdd _ _ _ _ hij]; exact S.det_eq

@[csimp] theorem Reduction.add_eq_fast : @Reduction.add = @Reduction.addFast := by
  funext n p inst A S i j c hij
  simp only [Reduction.add, Reduction.addFast, Word.add_eq]

/-- Retain a found pivot, otherwise test the next row. -/
@[expose]
def pivotStep (E : Matrix (ZMod64 p) n n) (j : Fin n)
    (found : Option (Fin n × ZMod64 p)) (i : Fin n) : Option (Fin n × ZMod64 p) :=
  match found with
  | some v => some v
  | none => if j ≤ i then (ZMod64.inv? E[(i, j)]).map (i, ·) else none

/-- Search at or below the diagonal for a unit pivot. -/
def pivot? (E : Matrix (ZMod64 p) n n) (j : Fin n) :
    Option (Fin n × ZMod64 p) :=
  Fin.foldl n (pivotStep E j) none

/-- Clear one row against a normalised pivot row. -/
@[expose]
def Reduction.clearRow (j : Fin n) (S : Reduction A) (i : Fin n) : Reduction A :=
  if h : j = i then S else S.add j i (-S.echelon[(i, j)]) h

/-- One diagonal pivot, normalised and cleared above and below. -/
def Reduction.step (S : Reduction A) (j : Fin n) : Option (Reduction A) := do
  let (i, b) ← pivot? S.echelon j
  let S := S.swap j i
  let a := S.echelon[(j, j)]
  if h : a * b = 1 then
    let S := S.scale j a b h
    return Fin.foldl n (Reduction.clearRow j) S
  else none

/-- Continue the diagonal pass from column `k`. -/
def Reduction.reduceFrom (S : Reduction A) (k : Nat) : Option (Reduction A) :=
  if hk : k < n then do
    let T ← S.step ⟨k, hk⟩
    T.reduceFrom (k + 1)
  else some S
termination_by n - k

/-- The modular Gauss-Jordan pass; no integer determinant is evaluated. -/
def reduce? (A : Matrix (ZMod64 p) n n) : Option (Reduction A) :=
  (Reduction.initial A).reduceFrom 0

/-- Forward elimination keeps the upper factor sparse until back substitution. -/
def Reduction.forwardStep (S : Reduction A) (j : Fin n) : Option (Reduction A) := do
  let (i, b) ← pivot? S.echelon j
  let S := S.swap j i
  let a := S.echelon[(j, j)]
  if h : a * b = 1 then
    let S := S.scale j a b h
    return Fin.foldl n (fun S i =>
      if j < i then S.clearRow j i else S) S
  else none

def Reduction.forwardFrom (S : Reduction A) (k : Nat) : Option (Reduction A) :=
  if hk : k < n then do
    let T ← S.forwardStep ⟨k, hk⟩
    T.forwardFrom (k + 1)
  else some S
termination_by n - k

/-- Clear above pivots in reverse order, preserving sparsity of the upper factor. -/
def fastReduce? (A : Matrix (ZMod64 p) n n) : Option (Reduction A) := do
  let S ← (Reduction.initial A).forwardFrom 0
  return Fin.foldr n (fun j S => Fin.foldl n
    (fun S i => if i < j then S.clearRow j i else S) S) S

end Dixon

/-- Check a modular reduction and package its inverse and determinant image. -/
def decompFrom? (A : Matrix Int n n) (p : Nat) [ZMod64.Bounds p] (hp : 1 < p)
    (state : Option (Dixon.Reduction (A.mapEntries (ZMod64.intCast p)))) :
    Option (Decomp n) := do
  let S ← state
  if hI : S.echelon = Matrix.identity n then
    let d := Modular.symMod (S.factor.toNat : Int) p
    if hd : d ≠ 0 then
      have hdet : ZMod64.intCast p (det A) = S.factor := by
        have h := S.det_eq
        rw [hI, det_identity] at h
        rw [det_mapEntries A (ZMod64.intCast p)
          (Lean.Grind.Ring.intCast_zero) (Lean.Grind.Ring.intCast_one)
          (Lean.Grind.Ring.intCast_add) (Lean.Grind.Ring.intCast_mul)] at h
        simpa using h
      have hmod : det A % (p : Int) = d % (p : Int) := by
        rw [Modular.symMod_emod (by omega)]
        have h := congrArg (fun x : ZMod64 p => (x.toNat : Int)) hdet
        rw [ZMod64.toNat_intCast] at h
        rw [← h, Int.emod_emod]
      return { A, p, one_lt := hp, inv := S.transform
               inv_mul := S.transform_mul.trans hI
               detImage := d
               detImage_congr := by rw [Int.sub_emod, hmod, Int.sub_self, Int.zero_emod]
               detImage_le := Modular.symMod_le (by omega)
               detImage_ne_zero := hd }
    else none
  else none

/-- Decompose at one bounded modulus. Try forward/back substitution first;
if its checked candidate fails, use the complete diagonal Gauss-Jordan pass. -/
def decompAt? (A : Matrix Int n n) (p : Nat) [ZMod64.Bounds p] (hp : 1 < p) :
    Option (Decomp n) :=
  match decompFrom? A p hp (Dixon.fastReduce? (A.mapEntries (ZMod64.intCast p))) with
  | some D => some D
  | none => decompFrom? A p hp (Dixon.reduce? (A.mapEntries (ZMod64.intCast p)))

/-- Try the first `fuel` primes in the descending word-prime supply. -/
def decompSearch (A : Matrix Int n n) (fuel : Nat) : Option (Decomp n) :=
  (ZMod64.primesBelow (2 ^ 31 - 1) fuel).foldl (fun found (q : ZMod64.Prime) =>
    match found with
    | some D => some D
    | none =>
      letI : ZMod64.Bounds q.m := q.bounds
      decompAt? A q.m q.prime.one_lt) none

/-- Probe one prime before materialising the complete fallback supply. -/
def decomp? (A : Matrix Int n n) (fuel : Nat) : Option (Decomp n) :=
  match decompSearch A (min fuel 1) with
  | some D => some D
  | none => decompSearch A fuel

/-- Default prime-search budget, separate from the lifting digit count. -/
def solveFuel (A : Matrix Int n n) : Nat := A.hadamardBound.log2 / 30 + 1

/-- A checked reduction retains the input and modulus. -/
theorem decompFrom?_A {A : Matrix Int n n} {p : Nat} [ZMod64.Bounds p]
    {hp : 1 < p} {state} {D : Decomp n} (h : decompFrom? A p hp state = some D) :
    D.A = A ∧ D.p = p := by
  unfold decompFrom? at h
  obtain ⟨S, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl⟩

/-- The decomposition preserves its input matrix and selected modulus. -/
theorem decompAt?_A {A : Matrix Int n n} {p : Nat} [ZMod64.Bounds p]
    {hp : 1 < p} {D : Decomp n} (h : decompAt? A p hp = some D) :
    D.A = A ∧ D.p = p := by
  unfold decompAt? at h
  split at h
  · rename_i E he
    cases h
    exact decompFrom?_A he
  · exact decompFrom?_A h

/-- Prime search preserves the matrix on every successful return. -/
theorem decompSearch_A {A : Matrix Int n n} {fuel : Nat} {D : Decomp n}
    (h : decompSearch A fuel = some D) : D.A = A := by
  unfold decompSearch at h
  have inv : ∀ (xs : List ZMod64.Prime) (s : Option (Decomp n)),
      (∀ D, s = some D → D.A = A) →
      ∀ D, xs.foldl (fun found (q : ZMod64.Prime) =>
        match found with
        | some D => some D
        | none => @decompAt? n A q.m q.bounds q.prime.one_lt) s = some D → D.A = A := by
    intro xs
    induction xs with
    | nil => intro s hs; exact hs
    | cons q xs ih =>
      intro s hs D hD
      apply ih _ ?_ D hD
      intro E hE
      cases s with
      | none => exact (@decompAt?_A n A q.m q.bounds q.prime.one_lt E hE).1
      | some E' => exact hs _ hE
  rw [← Array.foldl_toList] at h
  exact inv _ none (by simp) D h

/-- Prime search preserves the matrix on every successful return. -/
theorem decomp?_A {A : Matrix Int n n} {fuel : Nat} {D : Decomp n}
    (h : decomp? A fuel = some D) : D.A = A := by
  unfold decomp? at h
  split at h
  · rename_i E he
    cases h
    exact decompSearch_A he
  · exact decompSearch_A h

/-- Failure means every attempted prime decomposition failed. -/
theorem decomp?_none {A : Matrix Int n n} {fuel : Nat}
    (h : decomp? A fuel = none) (q : ZMod64.Prime)
    (hq : q ∈ ZMod64.primesBelow (2 ^ 31 - 1) fuel) :
    @decompAt? n A q.m q.bounds q.prime.one_lt = none := by
  have go (xs : List ZMod64.Prime) (s : Option (Decomp n)) :
      xs.foldl (fun found (q : ZMod64.Prime) => match found with
        | some D => some D
        | none => @decompAt? n A q.m q.bounds q.prime.one_lt) s = none →
      s = none ∧ ∀ q ∈ xs, @decompAt? n A q.m q.bounds q.prime.one_lt = none := by
    induction xs generalizing s with
    | nil => simp
    | cons a xs ih =>
      intro h
      obtain ⟨ha, hs⟩ := ih _ h
      cases s with
      | some D => contradiction
      | none =>
        refine ⟨rfl, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ha
        · exact hs q hq
  unfold decomp? at h
  split at h <;> try contradiction
  unfold decompSearch at h
  rw [← Array.foldl_toList] at h
  exact (go _ none h).2 q (by simpa using hq)

end Hex.Matrix
