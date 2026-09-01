/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.BerlekampMatrix
public import HexRowReduce.Pivot
public import HexRowReduce.Loop
public import HexRowReduce.Nullspace
public import HexRowReduce.RowEchelon
import all HexBerlekamp.BerlekampMatrix
import all HexRowReduce.Pivot
import all HexRowReduce.Loop
import all HexRowReduce.Nullspace
import all HexRowReduce.RowEchelon

public section

/-!
A packed finite-field matrix for Berlekamp's fixed space.

`Hex.Matrix (ZMod64 p)` stores one boxed residue per entry, and
`Hex.Matrix.rowReduce` maintains an `n x n` transform in lockstep that the
nullspace never reads. Both costs dominate the Berlekamp split on the large
cyclotomic rows of the factorization corpus.

This module keeps the same flat row-major backing but stores each residue as a
`UInt32` word, faithful because `ZMod64.Bounds` caps the modulus at `2^31` and
allocation-free because `lean_box_uint32` is a tagged immediate on a 64-bit
runtime. The reduction loop is specialized end to end -- pivot search, swap,
scale, elimination, and the nullspace readback -- and drops the transform.

Every packed step is proved to interpret to the corresponding step of the
generic development, and the whole file lands on one equality,
`Hex.Berlekamp.fixedSpaceKernelVectors_eq_packed`, registered `@[csimp]` so
that compiled code runs the packed path while the Berlekamp soundness and
completeness proofs keep reasoning about ordinary matrices.
-/

namespace Hex

namespace Berlekamp

namespace Packed

/-! # Modular arithmetic on packed words

Residues are held as `UInt32` words below the modulus word `q`. The modulus
bound `p < 2^31` makes the unreduced sum of two residues fit in a `UInt32` and
the unreduced product of two arbitrary words fit in a `UInt64`, so neither
operation needs a widening beyond `UInt64` and only the product needs a
division.
-/

/-- Modular product of two packed words. The operands are widened to `UInt64`,
where their product is exact for any `UInt32` inputs. -/
@[inline] def mulMod (q a b : UInt32) : UInt32 :=
  ((a.toUInt64 * b.toUInt64) % q.toUInt64).toUInt32

/-- Modular sum of two packed residues below `q`. The unreduced sum fits in a
`UInt32` because `q < 2^31`, so one conditional subtraction canonicalizes it. -/
@[inline] def addMod (q a b : UInt32) : UInt32 :=
  let s := a + b
  if s < q then s else s - q

/-- Modular negation of a packed residue below `q`. -/
@[inline] def negMod (q a : UInt32) : UInt32 :=
  if a == 0 then 0 else q - a

/-! ## Word/residue conversion -/

variable {p : Nat} [ZMod64.Bounds p]

/-- The modulus as a packed word. -/
@[inline] def modWord (p : Nat) : UInt32 :=
  UInt32.ofNat p

/-- Read a packed word as a residue. -/
@[inline] def toZMod (p : Nat) [ZMod64.Bounds p] (a : UInt32) : ZMod64 p :=
  ZMod64.ofNat p a.toNat

/-- Write a residue as a packed word. -/
@[inline] def ofZMod (a : ZMod64 p) : UInt32 :=
  a.val.toUInt32

/-- A residue is below `2 ^ 32`, so `ofZMod` loses nothing: `ZMod64.Bounds`
caps the modulus at `2 ^ 31`. -/
theorem toNat_lt_two_pow_32 (a : ZMod64 p) : a.toNat < 2 ^ 32 :=
  Nat.lt_trans a.isLt (Nat.lt_trans (ZMod64.Bounds.pLtR (p := p)) (by decide))

/-- Packing a residue preserves its numeral. -/
@[simp] theorem toNat_ofZMod (a : ZMod64 p) : (ofZMod a).toNat = a.toNat := by
  show (a.val.toUInt32).toNat = a.toNat
  rw [UInt64.toNat_toUInt32]
  exact Nat.mod_eq_of_lt (toNat_lt_two_pow_32 a)

/-- `ofZMod` is a section of `toZMod`: packing then reading recovers the
residue. -/
@[simp] theorem toZMod_ofZMod (a : ZMod64 p) : toZMod p (ofZMod a) = a := by
  rw [toZMod, toNat_ofZMod, ZMod64.ofNat_toNat]

/-- Reading an arbitrary packed word canonicalizes it modulo `p`.
Not `@[simp]`: `ZMod64.toNat_eq_val` rewrites the `ZMod64.toNat` head of the
left-hand side, so this shape is not simp-normal. -/
theorem toNat_toZMod (a : UInt32) : (toZMod p a).toNat = a.toNat % p := by
  simp [toZMod]

/-- The packed modulus word carries the modulus faithfully. -/
@[simp] theorem toNat_modWord : (modWord p).toNat = p := by
  show (UInt32.ofNat p).toNat = p
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt
    (Nat.lt_trans (ZMod64.Bounds.pLtR (p := p)) (by decide))

/-- Every packed word is below `2 ^ 32`. -/
theorem toNat_lt_size (a : UInt32) : a.toNat < 2 ^ 32 := by
  simpa [UInt32.size] using a.toNat_lt_size

/-- The modulus is below `2 ^ 32`, so it is faithful as a packed word. -/
theorem pLt32 : p < 2 ^ 32 :=
  Nat.lt_trans (ZMod64.Bounds.pLtR (p := p)) (by decide)

/-- A packed word below the modulus is recovered exactly by `toZMod`. -/
theorem toNat_toZMod_of_lt {a : UInt32} (h : a.toNat < p) :
    (toZMod p a).toNat = a.toNat := by
  rw [toNat_toZMod, Nat.mod_eq_of_lt h]

/-! ## Correctness of the packed operations -/

/-- `mulMod` computes the modular product of its operands as naturals. The
`UInt64` widening keeps the unreduced product exact for arbitrary `UInt32`
inputs, so no reducedness hypothesis is needed. -/
theorem toNat_mulMod {q a b : UInt32} (hq : q.toNat = p) :
    (mulMod q a b).toNat = (a.toNat * b.toNat) % p := by
  have hprod : (a.toUInt64 * b.toUInt64).toNat = a.toNat * b.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
    refine Nat.mod_eq_of_lt ?_
    have ha : a.toNat < 2 ^ 32 := toNat_lt_size a
    have hb : b.toNat < 2 ^ 32 := toNat_lt_size b
    calc a.toNat * b.toNat < 2 ^ 32 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_lt_of_lt ha hb
      _ = 2 ^ 64 := by decide +kernel
  have hmod : ((a.toUInt64 * b.toUInt64) % q.toUInt64).toNat = (a.toNat * b.toNat) % p := by
    rw [UInt64.toNat_mod, hprod, UInt32.toNat_toUInt64, hq]
  show (((a.toUInt64 * b.toUInt64) % q.toUInt64).toUInt32).toNat = _
  rw [UInt64.toNat_toUInt32, hmod]
  exact Nat.mod_eq_of_lt
    (Nat.lt_trans (Nat.mod_lt _ (ZMod64.Bounds.pPos (p := p))) (pLt32 (p := p)))

/-- `mulMod` returns a reduced residue. -/
theorem mulMod_lt {q a b : UInt32} (hq : q.toNat = p) : (mulMod q a b).toNat < p := by
  rw [toNat_mulMod hq]
  exact Nat.mod_lt _ (ZMod64.Bounds.pPos (p := p))

/-- `addMod` computes the modular sum of two reduced operands. Reducedness is
required: the single conditional subtraction only canonicalizes a sum that is
below `2 * p`. -/
theorem toNat_addMod {q a b : UInt32} (hq : q.toNat = p)
    (ha : a.toNat < p) (hb : b.toNat < p) :
    (addMod q a b).toNat = (a.toNat + b.toNat) % p := by
  have hp31 : p < 2 ^ 31 := ZMod64.Bounds.pLtR (p := p)
  have hsum : (a + b).toNat = a.toNat + b.toNat := by
    rw [UInt32.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  unfold addMod
  by_cases hlt : a + b < q
  · rw [ite_eq_left hlt]
    have hlt' : (a + b).toNat < q.toNat := UInt32.lt_iff_toNat_lt.mp hlt
    rw [hq, hsum] at hlt'
    rw [hsum, Nat.mod_eq_of_lt hlt']
  · rw [ite_eq_right hlt]
    have hge : p ≤ a.toNat + b.toNat :=
      Nat.le_of_not_lt fun hcon =>
        hlt (UInt32.lt_iff_toNat_lt.mpr (by rw [hq, hsum]; exact hcon))
    rw [UInt32.toNat_sub, hsum, hq]
    rw [show 2 ^ 32 - p + (a.toNat + b.toNat)
          = (a.toNat + b.toNat - p) + 2 ^ 32 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a.toNat + b.toNat - p < 2 ^ 32)]
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]

/-- `addMod` returns a reduced residue when both operands are reduced. -/
theorem addMod_lt {q a b : UInt32} (hq : q.toNat = p)
    (ha : a.toNat < p) (hb : b.toNat < p) : (addMod q a b).toNat < p := by
  rw [toNat_addMod hq ha hb]
  exact Nat.mod_lt _ (ZMod64.Bounds.pPos (p := p))

/-- `negMod` computes the modular negation of a reduced operand. The `a == 0`
branch is what makes the result reduced rather than `p`. -/
theorem toNat_negMod {q a : UInt32} (hq : q.toNat = p) (ha : a.toNat < p) :
    (negMod q a).toNat = (p - a.toNat) % p := by
  have hp32 : p < 2 ^ 32 := pLt32 (p := p)
  unfold negMod
  by_cases h : a == 0
  · rw [ite_eq_left h]
    have ha0 : a.toNat = 0 := by
      have : a = 0 := by simpa using h
      simp [this]
    simp [ha0]
  · rw [ite_eq_right h]
    have ha0 : a.toNat ≠ 0 := by
      intro hz
      exact h (by simpa using UInt32.toNat_inj.mp (by simpa using hz))
    rw [UInt32.toNat_sub, hq]
    rw [show 2 ^ 32 - a.toNat + p = (p - a.toNat) + 2 ^ 32 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : p - a.toNat < 2 ^ 32)]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- `negMod` returns a reduced residue when its operand is reduced. -/
theorem negMod_lt {q a : UInt32} (hq : q.toNat = p) (ha : a.toNat < p) :
    (negMod q a).toNat < p := by
  rw [toNat_negMod hq ha]
  exact Nat.mod_lt _ (ZMod64.Bounds.pPos (p := p))

/-- The packed negation of a packed residue is the packed negated residue. -/
theorem toZMod_negMod {q a : UInt32} (hq : q.toNat = p) (ha : a.toNat < p) :
    toZMod p (negMod q a) = -(toZMod p a) := by
  apply ZMod64.ext_toNat
  rw [toNat_toZMod_of_lt (negMod_lt hq ha), toNat_negMod hq ha]
  show _ = (ZMod64.neg (toZMod p a)).toNat
  rw [ZMod64.toNat_neg, toNat_toZMod_of_lt ha]

/-- The packed product of packed residues is the packed product residue. -/
theorem toZMod_mulMod {q a b : UInt32} (hq : q.toNat = p)
    (ha : a.toNat < p) (hb : b.toNat < p) :
    toZMod p (mulMod q a b) = toZMod p a * toZMod p b := by
  apply ZMod64.ext_toNat
  rw [toNat_toZMod_of_lt (mulMod_lt hq), toNat_mulMod hq]
  show _ = (ZMod64.mul (toZMod p a) (toZMod p b)).toNat
  rw [ZMod64.toNat_mul, toNat_toZMod_of_lt ha, toNat_toZMod_of_lt hb]

/-- The packed sum of packed residues is the packed sum residue. -/
theorem toZMod_addMod {q a b : UInt32} (hq : q.toNat = p)
    (ha : a.toNat < p) (hb : b.toNat < p) :
    toZMod p (addMod q a b) = toZMod p a + toZMod p b := by
  apply ZMod64.ext_toNat
  rw [toNat_toZMod_of_lt (addMod_lt hq ha hb), toNat_addMod hq ha hb]
  show _ = (ZMod64.add (toZMod p a) (toZMod p b)).toNat
  rw [ZMod64.toNat_add, toNat_toZMod_of_lt ha, toNat_toZMod_of_lt hb]

/-- Modular inverse of a packed residue, routed through {name}`Hex.ZMod64.inv`.
This runs once per pivot column, so it never appears in the inner loop and does
not need a word-level extended-Euclid specialization. -/
@[inline] def invMod (p : Nat) [ZMod64.Bounds p] (a : UInt32) : UInt32 :=
  ofZMod (ZMod64.inv (toZMod p a))

/-- The packed inverse of a packed word is the packed inverse residue. -/
@[simp] theorem toZMod_invMod (a : UInt32) :
    toZMod p (invMod p a) = (toZMod p a)⁻¹ := by
  rw [invMod, toZMod_ofZMod]
  rfl

/-- `invMod` returns a reduced residue for any input word. -/
theorem invMod_lt (a : UInt32) : (invMod p a).toNat < p := by
  rw [invMod, toNat_ofZMod]
  exact (ZMod64.inv (toZMod p a)).isLt

/-- A packed word is zero exactly when the residue it represents is zero. -/
theorem toZMod_eq_zero_iff {a : UInt32} (ha : a.toNat < p) :
    toZMod p a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg ZMod64.toNat h
    rw [toNat_toZMod_of_lt ha] at this
    have hz : a.toNat = 0 := by
      rw [this]
      exact ZMod64.toNat_zero (p := p)
    exact UInt32.toNat_inj.mp (by simpa using hz)
  · intro h
    subst h
    apply ZMod64.ext_toNat
    rw [toNat_toZMod_of_lt ha]
    exact (ZMod64.toNat_zero (p := p)).symm

/-! # Packed matrices and their interpretation

A packed matrix is a {name}`Hex.Matrix` of `UInt32` words: the same flat
row-major backing buffer, with one tagged-immediate word per entry instead of
one boxed residue. `Rep` says that a packed matrix represents a residue matrix
entry for entry; because residues are canonical, it also carries the invariant
that every packed word is below the modulus.
-/

variable {n m : Nat}

/-- The packed matrix `A` represents the residue matrix `E`. -/
def Rep (A : Matrix UInt32 n m) (E : Matrix (ZMod64 p) n m) : Prop :=
  ∀ (i : Fin n) (j : Fin m), A[i][j].toNat = E[i][j].toNat

/-- Every entry of a representing packed matrix is a reduced residue word,
because the residues it represents are canonical. -/
theorem Rep.lt {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m}
    (h : Rep A E) (i : Fin n) (j : Fin m) : A[i][j].toNat < p := by
  rw [h i j]
  exact E[i][j].isLt

/-- Reading an entry of a representing packed matrix recovers the residue
entry. This is the form `Rep` is consumed in once the goal is stated over
residues rather than over `toNat`. -/
theorem Rep.toZMod_eq {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m}
    (h : Rep A E) (i : Fin n) (j : Fin m) : toZMod p A[i][j] = E[i][j] :=
  ZMod64.ext_toNat (by rw [toNat_toZMod_of_lt (h.lt i j), h i j])

/-- Scale row `i` of a packed matrix by the packed residue `c`. Mirrors
{name}`Hex.Matrix.rowScale`, which is the same per-entry in-place
{name}`Hex.Matrix.modifyEntries` with the generic product replaced by the
modular one. -/
@[expose]
def rowScale (q : UInt32) (A : Matrix UInt32 n m) (i : Fin n) (c : UInt32) :
    Matrix UInt32 n m :=
  A.modifyEntries i.val fun _ x => mulMod q c x

/-- Replace row `dst` of a packed matrix by `row dst + c * rsrc`, with the source
row supplied by the caller instead of read out of the matrix.

`rsrc` must be a freshly materialized row, as {name}`Hex.Matrix.getRow` produces.
A borrow of `A`'s own backing buffer would leave that buffer multiply
referenced, and the {name}`Hex.Matrix.modifyEntries` below would copy the whole
matrix per row addition instead of writing in place. -/
@[inline, expose]
def rowAddFrom (q : UInt32) (A : Matrix UInt32 n m) (rsrc : Vector UInt32 m)
    (dst : Fin n) (c : UInt32) : Matrix UInt32 n m :=
  A.modifyEntries dst.val fun k x => addMod q x (mulMod q c rsrc[k])

/-- Replace row `dst` of a packed matrix by `row dst + c * row src`. Mirrors
{name}`Hex.Matrix.rowAdd`: the source row is read once, then the destination
row's entries are updated in place. -/
@[expose]
def rowAdd (q : UInt32) (A : Matrix UInt32 n m) (src dst : Fin n) (c : UInt32) :
    Matrix UInt32 n m :=
  rowAddFrom q A (Matrix.getRow A src) dst c

/-- Entrywise characterisation of `rowScale`: row `i` is scaled, every other
row is untouched. -/
theorem getElem_rowScale (q : UInt32) (A : Matrix UInt32 n m) (i r : Fin n)
    (c : UInt32) (k : Fin m) :
    (rowScale q A i c)[r][k] = if r = i then mulMod q c A[i][k] else A[r][k] := by
  rw [rowScale, Matrix.getElem_modifyEntries]
  by_cases h : r = i
  · rw [ite_eq_left (congrArg Fin.val h), ite_eq_left h, h]
  · rw [ite_eq_right (fun hv => h (Fin.ext hv)), ite_eq_right h]

/-- Entrywise characterisation of `rowAddFrom`: row `dst` gains `c * rsrc`,
every other row is untouched. -/
theorem getElem_rowAddFrom (q : UInt32) (A : Matrix UInt32 n m)
    (rsrc : Vector UInt32 m) (dst r : Fin n) (c : UInt32) (k : Fin m) :
    (rowAddFrom q A rsrc dst c)[r][k] =
      if r = dst then addMod q A[dst][k] (mulMod q c rsrc[k]) else A[r][k] := by
  rw [rowAddFrom, Matrix.getElem_modifyEntries]
  by_cases h : r = dst
  · rw [ite_eq_left (congrArg Fin.val h), ite_eq_left h, h]
  · rw [ite_eq_right (fun hv => h (Fin.ext hv)), ite_eq_right h]

/-- Entrywise characterisation of `rowAdd`, the `rowAddFrom` special case that
reads the source row out of the matrix. -/
theorem getElem_rowAdd (q : UInt32) (A : Matrix UInt32 n m) (src dst r : Fin n)
    (c : UInt32) (k : Fin m) :
    (rowAdd q A src dst c)[r][k] =
      if r = dst then addMod q A[dst][k] (mulMod q c A[src][k]) else A[r][k] := by
  rw [rowAdd]
  exact getElem_rowAddFrom q A (Matrix.getRow A src) dst r c k

/-! ## The packed elementary operations interpret to the generic ones -/

/-- A packed row swap interprets the reference row swap. -/
theorem Rep.rowSwap {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m}
    (h : Rep A E) (i j : Fin n) :
    Rep (Matrix.rowSwap A i j) (Matrix.rowSwap E i j) := by
  intro r k
  rw [Matrix.getElem_rowSwap, Matrix.getElem_rowSwap]
  by_cases hrj : r = j
  · simp only [ite_eq_left hrj]; exact h i k
  · by_cases hri : r = i
    · simp only [ite_eq_right hrj, ite_eq_left hri]; exact h j k
    · simp only [ite_eq_right hrj, ite_eq_right hri]; exact h r k

/-- A packed row scaling by a word representing `γ` interprets the reference
row scaling by `γ`. -/
theorem Rep.rowScale {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m} (h : Rep A E)
    (i : Fin n) {c : UInt32} {γ : ZMod64 p} (hc : c.toNat = γ.toNat) :
    Rep (rowScale q A i c) (Matrix.rowScale E i γ) := by
  intro r k
  rw [getElem_rowScale, Matrix.getElem_rowScale]
  by_cases hri : r = i
  · rw [ite_eq_left hri, ite_eq_left hri, toNat_mulMod hq]
    show _ = (ZMod64.mul γ E[i][k]).toNat
    rw [ZMod64.toNat_mul, hc, h i k]
  · rw [ite_eq_right hri, ite_eq_right hri]; exact h r k

/-- A caller-supplied source row that agrees entrywise with row `src` of the
packed matrix interprets the reference row addition, just as reading the row out
of the matrix does. -/
theorem Rep.rowAddFrom {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m} (h : Rep A E)
    {rsrc : Vector UInt32 m} (src dst : Fin n)
    (hsrc : ∀ k : Fin m, rsrc[k] = A[src][k])
    {c : UInt32} {γ : ZMod64 p} (hc : c.toNat = γ.toNat) :
    Rep (rowAddFrom q A rsrc dst c) (Matrix.rowAdd E src dst γ) := by
  intro r k
  rw [getElem_rowAddFrom, Matrix.getElem_rowAdd]
  by_cases hrd : r = dst
  · rw [ite_eq_left hrd, ite_eq_left hrd, hsrc k]
    rw [toNat_addMod hq (h.lt dst k) (mulMod_lt hq), toNat_mulMod hq]
    show _ = (ZMod64.add E[dst][k] (ZMod64.mul γ E[src][k])).toNat
    rw [ZMod64.toNat_add, ZMod64.toNat_mul, h dst k, hc, h src k]
  · rw [ite_eq_right hrd, ite_eq_right hrd]; exact h r k

/-- A packed row addition by a word representing `γ` interprets the reference
row addition by `γ`. -/
theorem Rep.rowAdd {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m} (h : Rep A E)
    (src dst : Fin n) {c : UInt32} {γ : ZMod64 p} (hc : c.toNat = γ.toNat) :
    Rep (rowAdd q A src dst c) (Matrix.rowAdd E src dst γ) :=
  h.rowAddFrom hq src dst (fun _ => rfl) hc

/-! # Packed Gauss-Jordan

The packed loop mirrors {name}`Hex.Matrix.rowReduceLoop` step for step, with two
differences: the entries are packed words rather than residues, and the `n x n`
transform is dropped, because {name}`Hex.Matrix.nullspace` reads only the rank,
the echelon form, and the pivot columns.

Entries are read through the `O(1)` flat pair accessor `A[(i, j)]`; the nested
row accessor `A[i]` is deliberately noncomputable in `HexMatrix` because it
would materialize a row per read.
-/

/-- Packed pivot search: the first row at or below `start` whose `col` entry is
nonzero. Mirrors `Hex.Matrix.findPivotAux`. -/
def findPivotAux (A : Matrix UInt32 n m) (col : Fin m) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if A[(i, col)] == 0 then
          findPivotAux A col (start + 1) fuel
        else
          some i
      else
        none

/-- Packed pivot search from `start`. Mirrors `Hex.Matrix.findPivot?`. -/
def findPivot? (A : Matrix UInt32 n m) (col : Fin m) (start : Nat) : Option (Fin n) :=
  findPivotAux A col start (n - start)

/-- Eliminate every non-pivot entry of a packed pivot column. Mirrors
`Hex.Matrix.eliminateColumn` with the transform component dropped.

The pivot row is read once for the whole column rather than once per row
addition: the fold skips `j = pivotRow`, so nothing it writes can change what
the next row addition reads. A dense column's `n - 1` source-row copies become
one. -/
def eliminateColumn (q : UInt32) (A : Matrix UInt32 n m) (pivotRow : Fin n)
    (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := Matrix.getRow A pivotRow
  (List.finRange n).foldl
    (fun A j =>
      if j = pivotRow then
        A
      else
        let c := negMod q A[(j, col)]
        if c == 0 then A else rowAddFrom q A rsrc j c)
    A

/-- Running state of the packed Gauss-Jordan loop. Mirrors
{name}`Hex.Matrix.RowReduceState` without the transform. -/
structure State (n m : Nat) where
  /-- Rows already assigned a pivot. -/
  row : Nat
  /-- The partially reduced packed matrix. -/
  echelon : Matrix UInt32 n m
  /-- Pivot columns found so far, in increasing order. -/
  pivots : List (Fin m)

/-- The packed Gauss-Jordan loop. Mirrors {name}`Hex.Matrix.rowReduceLoop`. -/
def reduceLoop (p : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (q : UInt32) (col fuel : Nat) (s : State n m) : State n m :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
      if hRow : s.row < n then
        if hCol : col < m then
          let colFin : Fin m := ⟨col, hCol⟩
          match findPivot? s.echelon colFin s.row with
          | none =>
              reduceLoop p q (col + 1) fuel s
          | some pivot =>
              let target : Fin n := ⟨s.row, hRow⟩
              let swapped := Matrix.rowSwap s.echelon target pivot
              let pivotVal := swapped[(target, colFin)]
              let scaled := rowScale q swapped target (invMod p pivotVal)
              let eliminated := eliminateColumn q scaled target colFin
              reduceLoop p q (col + 1) fuel
                { row := s.row + 1
                  echelon := eliminated
                  pivots := s.pivots.concat colFin }
        else
          s
      else
        s

/-! ## The packed loop simulates the generic one -/

section Simulation

variable [ZMod64.PrimeModulus p]

omit [ZMod64.PrimeModulus p] in
/-- A packed entry is zero exactly when the residue entry it represents is. -/
private theorem rep_eq_zero_iff {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m}
    (h : Rep A E) (i : Fin n) (j : Fin m) : A[(i, j)] = 0 ↔ E[(i, j)] = 0 := by
  rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested,
    ← h.toZMod_eq i j]
  exact (toZMod_eq_zero_iff (h.lt i j)).symm

/-- Packed pivot search agrees with the reference pivot search. -/
private theorem findPivotAux_eq {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m}
    (h : Rep A E) (col : Fin m) :
    ∀ start fuel, findPivotAux A col start fuel = Hex.Matrix.findPivotAux E col start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      unfold findPivotAux Hex.Matrix.findPivotAux
      by_cases hstart : start < n
      · rw [dite_eq_left hstart, dite_eq_left hstart]
        have hiff := rep_eq_zero_iff h ⟨start, hstart⟩ col
        show (if (A[((⟨start, hstart⟩ : Fin n), col)] == 0) = true then
              findPivotAux A col (start + 1) fuel else some ⟨start, hstart⟩)
            = (if E[((⟨start, hstart⟩ : Fin n), col)] = 0 then
              Hex.Matrix.findPivotAux E col (start + 1) fuel else some ⟨start, hstart⟩)
        by_cases hA : A[((⟨start, hstart⟩ : Fin n), col)] = 0
        · rw [ite_eq_left (beq_iff_eq.mpr hA), ite_eq_left (hiff.mp hA)]
          exact ih (start + 1)
        · rw [ite_eq_right (fun hb => hA (beq_iff_eq.mp hb)),
            ite_eq_right (fun hE => hA (hiff.mpr hE))]
      · rw [dite_eq_right hstart, dite_eq_right hstart]

/-- Packed pivot search agrees with the reference pivot search. -/
private theorem findPivot?_eq {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m}
    (h : Rep A E) (col : Fin m) (start : Nat) :
    findPivot? A col start = Hex.Matrix.findPivot? E col start :=
  findPivotAux_eq h col start (n - start)

omit [ZMod64.PrimeModulus p] in
/-- One elimination step of the packed fold represents one elimination step of
the reference fold. -/
private theorem rep_elim_step {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {st : Matrix (ZMod64 p) n m × Matrix (ZMod64 p) n n}
    (h : Rep A st.1) (pivotRow : Fin n) (col : Fin m) (j : Fin n)
    {rsrc : Vector UInt32 m} (hsrc : ∀ k : Fin m, rsrc[k] = A[pivotRow][k]) :
    Rep
      (if j = pivotRow then A
        else
          let c := negMod q A[(j, col)]
          if c == 0 then A else rowAddFrom q A rsrc j c)
      (if _hj : j = pivotRow then st
        else
          have coeff := -st.1[(j, col)]
          if coeff = 0 then st
          else (Matrix.rowAdd st.1 pivotRow j coeff, Matrix.rowAdd st.2 pivotRow j coeff)).1 := by
  by_cases hj : j = pivotRow
  · rw [ite_eq_left hj, dite_eq_left hj]; exact h
  · rw [ite_eq_right hj, dite_eq_right hj]
    have hcoeff : (negMod q A[(j, col)]).toNat = (-st.1[(j, col)]).toNat := by
      rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested,
        toNat_negMod hq (h.lt j col), h j col]
      show _ = (ZMod64.neg st.1[j][col]).toNat
      rw [ZMod64.toNat_neg]
    have hiff : negMod q A[(j, col)] = 0 ↔ -st.1[(j, col)] = 0 := by
      constructor
      · intro hz
        apply ZMod64.ext_toNat
        rw [← hcoeff, hz]
        exact (ZMod64.toNat_zero (p := p)).symm
      · intro hz
        apply UInt32.toNat_inj.mp
        rw [hcoeff, hz]
        exact ZMod64.toNat_zero (p := p)
    by_cases hA : negMod q A[(j, col)] = 0
    · rw [ite_eq_left (beq_iff_eq.mpr hA), ite_eq_left (hiff.mp hA)]
      exact h
    · rw [ite_eq_right (fun hb => hA (beq_iff_eq.mp hb)),
        ite_eq_right (fun hE => hA (hiff.mpr hE))]
      exact h.rowAddFrom hq pivotRow j hsrc hcoeff

/-- One elimination step leaves the pivot row alone: the step either does
nothing or adds into a row `j ≠ pivotRow`. This is what makes the hoisted source
row still the accumulated buffer's pivot row at the next step. -/
private theorem elim_step_pivotRow {q : UInt32} (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) (j : Fin n) (rsrc : Vector UInt32 m)
    (k : Fin m) :
    (if j = pivotRow then A
      else
        let c := negMod q A[(j, col)]
        if c == 0 then A else rowAddFrom q A rsrc j c)[pivotRow][k]
      = A[pivotRow][k] := by
  by_cases hj : j = pivotRow
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj]
    by_cases hA : negMod q A[(j, col)] = 0
    · rw [ite_eq_left (beq_iff_eq.mpr hA)]
    · rw [ite_eq_right (fun hb => hA (beq_iff_eq.mp hb)), getElem_rowAddFrom,
        ite_eq_right (fun hp => hj hp.symm)]

omit [ZMod64.PrimeModulus p] in
/-- The packed column elimination represents the reference column elimination.
The source row `rsrc` is hoisted out of the fold, so the fold carries the
invariant that it still agrees with the accumulated buffer's pivot row. -/
theorem rep_eliminateColumn_foldl {q : UInt32} (hq : q.toNat = p) (pivotRow : Fin n)
    (col : Fin m) (rsrc : Vector UInt32 m) :
    ∀ (xs : List (Fin n)) (A : Matrix UInt32 n m)
      (st : Matrix (ZMod64 p) n m × Matrix (ZMod64 p) n n),
      Rep A st.1 →
      (∀ k : Fin m, rsrc[k] = A[pivotRow][k]) →
      Rep
        (xs.foldl
          (fun A j =>
            if j = pivotRow then A
            else
              let c := negMod q A[(j, col)]
              if c == 0 then A else rowAddFrom q A rsrc j c) A)
        (xs.foldl
          (fun st j =>
            if _hj : j = pivotRow then st
            else
              have coeff := -st.1[(j, col)]
              if coeff = 0 then st
              else (Matrix.rowAdd st.1 pivotRow j coeff, Matrix.rowAdd st.2 pivotRow j coeff))
          st).1 := by
  intro xs
  induction xs with
  | nil => intro A st h _; exact h
  | cons x xs ih =>
      intro A st h hsrc
      simp only [List.foldl_cons]
      exact ih _ _ (rep_elim_step hq h pivotRow col x hsrc)
        (fun k => (hsrc k).trans (elim_step_pivotRow A pivotRow col x rsrc k).symm)

/-- The packed column elimination represents the reference column elimination. -/
private theorem rep_eliminateColumn {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m} (h : Rep A E)
    (T : Matrix (ZMod64 p) n n) (pivotRow : Fin n) (col : Fin m) :
    Rep (eliminateColumn q A pivotRow col)
      (Hex.Matrix.eliminateColumn E T pivotRow col).1 := by
  unfold eliminateColumn Hex.Matrix.eliminateColumn
  exact rep_eliminateColumn_foldl hq pivotRow col (Matrix.getRow A pivotRow)
    (List.finRange n) A (E, T) h (fun _ => rfl)


omit [ZMod64.PrimeModulus p] in
/-- The packed inverse of a packed residue is the packed inverse residue. -/
private theorem toNat_invMod_eq {a : UInt32} {γ : ZMod64 p} (h : toZMod p a = γ) :
    (invMod p a).toNat = (γ⁻¹).toNat := by
  rw [invMod, toNat_ofZMod, h]
  rfl

/-- The packed Gauss-Jordan loop simulates {name}`Hex.Matrix.rowReduceLoop`: it
finds the same pivot columns in the same order, advances the same row counter,
and its packed buffer represents the reference echelon matrix at every step.
The reference transform is carried along on the right and never inspected. -/
theorem reduceLoop_sim {q : UInt32} (hq : q.toNat = p) :
    ∀ (fuel col row : Nat) (pivots : List (Fin m)) (A : Matrix UInt32 n m)
      (E : Matrix (ZMod64 p) n m) (T : Matrix (ZMod64 p) n n),
      Rep A E →
      (reduceLoop p q col fuel ⟨row, A, pivots⟩).row
          = (Matrix.rowReduceLoop col fuel ⟨row, E, T, pivots⟩).row ∧
        (reduceLoop p q col fuel ⟨row, A, pivots⟩).pivots
          = (Matrix.rowReduceLoop col fuel ⟨row, E, T, pivots⟩).pivots ∧
        Rep (reduceLoop p q col fuel ⟨row, A, pivots⟩).echelon
          (Matrix.rowReduceLoop col fuel ⟨row, E, T, pivots⟩).echelon := by
  intro fuel
  induction fuel with
  | zero =>
      intro col row pivots A E T h
      exact ⟨rfl, rfl, h⟩
  | succ fuel ih =>
      intro col row pivots A E T h
      by_cases hRow : row < n
      · by_cases hCol : col < m
        · have hfp := findPivot?_eq h ⟨col, hCol⟩ row
          cases hpv : Hex.Matrix.findPivot? E ⟨col, hCol⟩ row with
          | none =>
              simp only [reduceLoop, Matrix.rowReduceLoop, dite_eq_left hRow, dite_eq_left hCol,
                hfp, hpv]
              exact ih (col + 1) row pivots A E T h
          | some pivot =>
              simp only [reduceLoop, Matrix.rowReduceLoop, dite_eq_left hRow, dite_eq_left hCol,
                hfp, hpv]
              have hswap := h.rowSwap (⟨row, hRow⟩ : Fin n) pivot
              have hinv :
                  (invMod p
                      (Matrix.rowSwap A (⟨row, hRow⟩ : Fin n) pivot)[((⟨row, hRow⟩ : Fin n),
                        (⟨col, hCol⟩ : Fin m))]).toNat
                    = ((Matrix.rowSwap E (⟨row, hRow⟩ : Fin n) pivot)[((⟨row, hRow⟩ : Fin n),
                        (⟨col, hCol⟩ : Fin m))]⁻¹).toNat := by
                apply toNat_invMod_eq
                rw [Matrix.getElem_pair_eq_nested, Matrix.getElem_pair_eq_nested]
                exact hswap.toZMod_eq (⟨row, hRow⟩ : Fin n) (⟨col, hCol⟩ : Fin m)
              have hscale := hswap.rowScale hq (⟨row, hRow⟩ : Fin n) hinv
              have helim :=
                rep_eliminateColumn hq hscale
                  (Matrix.rowScale (Matrix.rowSwap T (⟨row, hRow⟩ : Fin n) pivot)
                    (⟨row, hRow⟩ : Fin n)
                    ((Matrix.rowSwap E (⟨row, hRow⟩ : Fin n) pivot)[((⟨row, hRow⟩ : Fin n),
                      (⟨col, hCol⟩ : Fin m))]⁻¹))
                  (⟨row, hRow⟩ : Fin n) (⟨col, hCol⟩ : Fin m)
              exact ih (col + 1) (row + 1) (pivots.concat (⟨col, hCol⟩ : Fin m)) _ _ _ helim
        · simp only [reduceLoop, Matrix.rowReduceLoop, dite_eq_left hRow, dite_eq_right hCol]
          exact ⟨trivial, trivial, h⟩
      · simp only [reduceLoop, Matrix.rowReduceLoop, dite_eq_right hRow]
        exact ⟨trivial, trivial, h⟩

end Simulation

/-! ## The finished packed reduction -/

/-- Packed Gauss-Jordan elimination of `A`. Mirrors {name}`Hex.Matrix.rowReduce`
without the transform. -/
def reduce (p : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p] (q : UInt32)
    (A : Matrix UInt32 n m) : State n m :=
  reduceLoop p q 0 m { row := 0, echelon := A, pivots := [] }

variable [ZMod64.PrimeModulus p]

/-- The packed reduction finds the reference pivot columns. -/
theorem reduce_pivots {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m} (h : Rep A E) :
    (reduce p q A).pivots = (Matrix.rowReduce E).pivotCols.toList := by
  have := (reduceLoop_sim hq m 0 0 [] A E (Matrix.identity n) h).2.1
  simpa [reduce, Matrix.rowReduce] using this

/-- The packed reduction finds the reference rank. -/
theorem reduce_rank {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m} (h : Rep A E) :
    (reduce p q A).pivots.length = (Matrix.rowReduce E).rank := by
  rw [reduce_pivots hq h]
  simp

/-- The packed reduction's buffer represents the reference echelon form. -/
theorem reduce_rep {q : UInt32} (hq : q.toNat = p)
    {A : Matrix UInt32 n m} {E : Matrix (ZMod64 p) n m} (h : Rep A E) :
    Rep (reduce p q A).echelon (Matrix.rowReduce E).echelon := by
  have := (reduceLoop_sim hq m 0 0 [] A E (Matrix.identity n) h).2.2
  simpa [reduce, Matrix.rowReduce] using this

/-! # The packed nullspace basis

The readback mirrors {name}`Hex.Matrix.IsRowReduced.nullspaceMatrix` column for
column, but assembles the basis vectors directly out of packed words instead of
materializing an `m x (m - rank)` residue matrix and then slicing it. The pivot
columns are carried as a plain list, so nothing here is indexed by the rank.
-/

/-- The pivot row of column `j`, searching from row `i`. Mirrors
`Hex.Matrix.IsRowReduced.pivotIndexAux` walking the pivot-column list. -/
def pivotRowOf : List (Fin m) → Fin m → Nat → Option Nat
  | [], _, _ => none
  | c :: cs, j, i => if c = j then some i else pivotRowOf cs j (i + 1)

/-- The non-pivot columns, in increasing order. Mirrors
{name}`Hex.Matrix.IsEchelonForm.freeColsList` with the echelon witness dropped. -/
def freeColsList (pivots : List (Fin m)) : List (Fin m) :=
  (List.finRange m).filter fun j => j ∉ pivots

/-- The nullspace basis read straight off a reduced packed buffer: one vector
per free column, with a `1` in its own free column, the negated pivot-row entry
in each pivot column, and `0` elsewhere.

The `i < n` test is never false on a reduction's own output -- there are at most
`n` pivots -- and `nullspaceArray_eq` discharges it. -/
def nullspaceArray (q : UInt32) (A : Matrix UInt32 n m) (pivots : List (Fin m)) :
    Array (Vector (ZMod64 p) m) :=
  (freeColsList pivots).toArray.map fun fc =>
    Vector.ofFn fun j =>
      if j = fc then
        1
      else
        match pivotRowOf pivots j 0 with
        | some i =>
            if hi : i < n then toZMod p (negMod q A[((⟨i, hi⟩ : Fin n), fc)]) else 0
        | none => 0

section Basis

omit [ZMod64.PrimeModulus p] in
/-- Walking the pivot-column list from `start` is the reference pivot-index
search from `start`. -/
private theorem pivotRowOf_drop (D : Matrix.RowEchelonData (ZMod64 p) n m) (j : Fin m) :
    ∀ (fuel start : Nat), start + fuel = D.rank →
      pivotRowOf (D.pivotCols.toList.drop start) j start
        = (Matrix.IsRowReduced.pivotIndexAux D j start fuel).map Fin.val := by
  intro fuel
  induction fuel with
  | zero =>
      intro start hstart
      have hdrop : D.pivotCols.toList.drop start = [] := by
        apply List.drop_eq_nil_of_le
        simp [Vector.length_toList]
        omega
      rw [hdrop]
      rfl
  | succ fuel ih =>
      intro start hstart
      have hlt : start < D.rank := by omega
      have hlen : start < D.pivotCols.toList.length := by
        simpa [Vector.length_toList] using hlt
      have hdrop : D.pivotCols.toList.drop start
          = D.pivotCols.toList[start] :: D.pivotCols.toList.drop (start + 1) :=
        (List.drop_eq_getElem_cons hlen)
      have hget : D.pivotCols.toList[start] = D.pivotCols.get ⟨start, hlt⟩ := by
        simp [Vector.get]
      rw [hdrop, hget, pivotRowOf, Matrix.IsRowReduced.pivotIndexAux, dite_eq_left hlt]
      show (if D.pivotCols.get ⟨start, hlt⟩ = j then some start
            else pivotRowOf (D.pivotCols.toList.drop (start + 1)) j (start + 1))
          = Option.map Fin.val
              (if D.pivotCols.get ⟨start, hlt⟩ = j then some ⟨start, hlt⟩
               else Matrix.IsRowReduced.pivotIndexAux D j (start + 1) fuel)
      by_cases hc : D.pivotCols.get ⟨start, hlt⟩ = j
      · rw [ite_eq_left hc, ite_eq_left hc]; rfl
      · rw [ite_eq_right hc, ite_eq_right hc]
        exact ih (start + 1) (by omega)

omit [ZMod64.PrimeModulus p] in
/-- Walking the pivot-column list is the reference pivot-index search. -/
private theorem pivotRowOf_eq (D : Matrix.RowEchelonData (ZMod64 p) n m) (j : Fin m) :
    pivotRowOf D.pivotCols.toList j 0
      = (Matrix.IsRowReduced.pivotIndex? D j).map Fin.val := by
  have := pivotRowOf_drop D j D.rank 0 (by omega)
  simpa [Matrix.IsRowReduced.pivotIndex?] using this

/-- The packed nullspace readback reproduces {name}`Hex.Matrix.nullspace`. -/
theorem nullspaceArray_eq {q : UInt32} (hq : q.toNat = p)
    {E : Matrix (ZMod64 p) n m} {A : Matrix UInt32 n m}
    (h : Rep A (Matrix.rowReduce E).echelon)
    {pivots : List (Fin m)} (hpv : pivots = (Matrix.rowReduce E).pivotCols.toList) :
    nullspaceArray q A pivots = (Matrix.nullspace E).toArray := by
  subst hpv
  have hE := Matrix.rowReduce_isRowReduced E
  have hrank := Matrix.rowReduce_rank_le_n E
  have hfree : freeColsList (Matrix.rowReduce E).pivotCols.toList
      = hE.toIsEchelonForm.freeColsList := rfl
  have hlen : (freeColsList (Matrix.rowReduce E).pivotCols.toList).length
      = m - (Matrix.rowReduce E).rank := by
    rw [hfree]; exact hE.toIsEchelonForm.freeColsList_length
  unfold nullspaceArray
  apply Array.ext
  · simp only [Array.size_map, List.size_toArray, hlen]
    rw [Matrix.nullspace]
    simp [Matrix.rowReduce_rank]
  · intro k hk1 hk2
    have hklt : k < m - (Matrix.rowReduce E).rank := by
      simpa [hlen] using hk1
    have hkfree : k < (freeColsList (Matrix.rowReduce E).pivotCols.toList).length := by omega
    have hgetfree :
        (freeColsList (Matrix.rowReduce E).pivotCols.toList)[k]'hkfree
          = hE.toIsEchelonForm.freeCols.get ⟨k, hklt⟩ := by
      rw [Matrix.IsEchelonForm.freeCols]
      simp [Vector.get, hfree]
    have harr : (Matrix.nullspace E).toArray
        = Array.ofFn (fun t : Fin (m - (Matrix.rowReduce E).rank) =>
            Matrix.col (Matrix.IsRowReduced.nullspaceMatrix hE) t) := rfl
    simp only [Array.getElem_map, List.getElem_toArray, harr, Array.getElem_ofFn]
    apply Vector.ext
    intro j hj
    rw [Vector.getElem_ofFn]
    simp only [Matrix.col, Vector.getElem_ofFn, Matrix.IsRowReduced.nullspaceMatrix,
      Matrix.getElem_pair_eq_nested, Matrix.getElem_ofFn]
    rw [hgetfree]
    by_cases hjf : (⟨j, hj⟩ : Fin m) = hE.toIsEchelonForm.freeCols.get ⟨k, hklt⟩
    · rw [ite_eq_left hjf, dite_eq_left hjf]
    · rw [ite_eq_right hjf, dite_eq_right hjf, pivotRowOf_eq (Matrix.rowReduce E) ⟨j, hj⟩]
      rw [Matrix.IsRowReduced.pivotRows_get]
      cases hpi : Matrix.IsRowReduced.pivotIndex? (Matrix.rowReduce E) (⟨j, hj⟩ : Fin m) with
      | none => rfl
      | some i =>
          have hin : i.val < n := Nat.lt_of_lt_of_le i.isLt hrank
          show (if hi : i.val < n then toZMod p (negMod q _) else 0) = _
          rw [dite_eq_left hin, toZMod_negMod hq (h.lt _ _), h.toZMod_eq _ _]
          rfl

end Basis



/-! # The packed fixed-space matrix and kernel

The packed buffer is filled straight from the Berlekamp column polynomials: no
`Matrix (ZMod64 p)` is ever built, so neither the conversion into the generic
representation nor a separate packing pass is paid.
-/

/-- The fixed-space matrix `Q_f - I`, built directly into a packed buffer from
the Berlekamp column polynomials. -/
@[expose]
def fixedSpace (p : Nat) [ZMod64.Bounds p] (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Matrix UInt32 (basisSize f) (basisSize f) :=
  let frobX := FpPoly.frobeniusXMod f hmonic
  let polys := berlekampColumnPolys f hmonic frobX (basisSize f) 1 #[]
  Matrix.ofFn fun i j =>
    ofZMod ((polys[j.val]?.getD 0).coeff i.val - (if i = j then 1 else 0))

omit [ZMod64.PrimeModulus p] in
/-- The packed fixed-space buffer represents
{name}`Hex.Berlekamp.fixedSpaceMatrix`. -/
theorem fixedSpace_rep (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Rep (fixedSpace p f hmonic) (fixedSpaceMatrix f hmonic) := by
  intro i j
  rw [fixedSpace, Matrix.getElem_ofFn, toNat_ofZMod, getElem_fixedSpaceMatrix,
    berlekampMatrix_entry_eq_columnPolys_coeff]

/-- The Berlekamp fixed-space kernel basis, computed on the packed
representation: build the packed `Q_f - I`, reduce it in place with the
specialized Gauss-Jordan loop, and read the basis off the reduced buffer. -/
@[expose]
def kernelArray (p : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    Array (Vector (ZMod64 p) (basisSize f)) :=
  let q := modWord p
  let r := reduce p q (fixedSpace p f hmonic)
  nullspaceArray q r.echelon r.pivots

/-- **The correspondence theorem.** The packed kernel computation returns
exactly {name}`Hex.Matrix.nullspace` of the fixed-space matrix. -/
theorem kernelArray_eq (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    kernelArray p f hmonic = (Matrix.nullspace (fixedSpaceMatrix f hmonic)).toArray := by
  have hq : (modWord p).toNat = p := toNat_modWord
  have hrep := fixedSpace_rep f hmonic
  exact nullspaceArray_eq hq (reduce_rep hq hrep) (reduce_pivots hq hrep)

end Packed


/-! # The fast path

`fixedSpaceKernelVectorsPacked` has the same type as
{name}`Hex.Berlekamp.fixedSpaceKernelVectors`, with the size index discharged by
the correspondence theorem rather than recomputed: the returned array's length
is only ever mentioned inside an erased proof, so nothing at runtime demands
`basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)`, which would
run a second full row reduction.
-/

variable {p : Nat} [ZMod64.Bounds p]

/-- The packed implementation of
{name}`Hex.Berlekamp.fixedSpaceKernelVectors`, selected in compiled code by the
`@[csimp]` theorem `fixedSpaceKernelVectors_eq_packed` below. -/
@[expose]
def fixedSpaceKernelVectorsPacked (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [ZMod64.PrimeModulus p] :
    Vector (Vector (ZMod64 p) (basisSize f))
      (basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)) :=
  ⟨Packed.kernelArray p f hmonic, by
    rw [Packed.kernelArray_eq]
    exact (Matrix.nullspace (fixedSpaceMatrix f hmonic)).size_toArray⟩

/-- The packed fixed-space kernel is the generic one. Registered `@[csimp]`, so
compiled code runs the packed reduction while every Berlekamp soundness and
completeness proof keeps reasoning about `Matrix (ZMod64 p)` and
{name}`Hex.Matrix.nullspace`. -/
@[csimp] theorem fixedSpaceKernelVectors_eq_packed :
    @fixedSpaceKernelVectors = @fixedSpaceKernelVectorsPacked := by
  funext p _ f hmonic _
  apply Vector.toArray_inj.mp
  exact (Packed.kernelArray_eq f hmonic).symm


/-- The fixed-space kernel basis converted back to polynomial representatives.

Compute the vector basis once and map the conversion over it. Keep the basis
outside any per-index body so matrix construction and row reduction remain
shared; mapping also carries its dependent length without recomputing rank. -/
@[expose]
def fixedSpaceKernel (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [ZMod64.PrimeModulus p] :
    Vector (FpPoly p)
      (basisSize f - Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic)) :=
  let vectors := fixedSpaceKernelVectors f hmonic
  vectors.map vectorToPoly

/-- Every polynomial representative returned by `fixedSpaceKernel` satisfies the
executable fixed-space kernel condition. -/
theorem fixedSpaceKernel_sound (f : FpPoly p) (hmonic : DensePoly.Monic f)
    [ZMod64.PrimeModulus p]
    (k : Fin (basisSize f -
      Matrix.rowReduce_rank (fixedSpaceMatrix f hmonic))) :
    IsFixedSpaceKernelPolynomial f hmonic ((fixedSpaceKernel f hmonic).get k) := by
  have hk : (fixedSpaceKernel f hmonic).get k =
      vectorToPoly ((fixedSpaceKernelVectors f hmonic).get k) := by
    unfold fixedSpaceKernel
    exact Vector.getElem_map vectorToPoly k.isLt
  unfold IsFixedSpaceKernelPolynomial
  rw [hk, coeffVector_vectorToPoly]
  exact fixedSpaceKernelVectors_sound f hmonic k

end Berlekamp

end Hex
