/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Int
public import HexArith.ExtGcd
public import HexMatrix.Notation
public import HexMatrix.Packed

public section

/-!
The kernel certificate for rank: `RankWitness`, its checker `checkRankList`,
and the producer `rankWitness`.

`checkRank` is the reference checker: it states the two certificate
identities as matrix equations, which is the right form for proofs and for
compiled re-checking.  It is not the right form for the kernel.  Every entry
access through the flat buffer costs a list traversal, every `ofFn` matrix is
rebuilt at each access, and the identities do about `3 n³` multiplications at
full rank.  `checkRankList` is the kernel form: the same rank, on the same
pivot rows and columns, certified by data the kernel consumes with structural
recursion over lists and GMP-backed `Nat` arithmetic only.

The witness names pivot rows `rows` (elimination order) and pivot columns
`cols` (increasing), and carries

* a lower bound modulo `modulus`: the columns `vt` of a matrix `V` with
  `B * V ≡ L (mod modulus)` for the pivot block `B` and some lower triangular
  `L` with unit diagonal.  Then `det B · det V ≡ 1`, so `det B` is nonzero
  over `Int`.  The kernel computes only the diagonal and the entries above
  it.  Column `j` of the producer's upper-triangular `V` has `j + 1`
  entries, so the check costs about `rank³ / 3` small multiplications.
  Primality of the modulus plays no role.
* an upper bound over `Int`: for every non-pivot row `i`, in increasing
  order, coefficients `z` with `denom • A_i = Σ z_l • A_{rows l}`, so every
  row of `denom • A` lies in the span of the pivot rows.  This costs
  `(n - rank) · rank · m` integer multiplications and nothing at full rank.

The producer derives `z` from the full pivot-block adjugate (identity 3
restricted to a row).  Column `j` of `V` is `B_j⁻¹ e_j` modulo `modulus`
for the leading `(j + 1) × (j + 1)` pivot block `B_j`, so `V` is upper
triangular and `B * V` is lower triangular with unit diagonal.  It obtains
every column from one Gaussian elimination of the block modulo `modulus`
without pivoting, whose upper factor's leading blocks are the upper
factors of the `B_j`, by back substitution: `O(rank³)` modular arithmetic
operations in all.  While the preceding pivots are units, a pivot is a
unit exactly when the leading block it completes is, so the first pivot
that is not a unit is the first leading block that is not, and it sends
the producer to the next modulus.  It re-checks its own output
before returning it.  The two halves are independent: nothing relates
`denom` to the modular data, and each bound is sound on its own.

The soundness theorem `rank_eq_of_checkList` (`Matrix.rank` of the Mathlib
matrix equals `rank`) is in `HexRankMathlib`.
-/

namespace Hex.Matrix

/-- A kernel-checkable rank certificate.  See the module docstring. -/
structure RankWitness where
  /-- The certified rank. -/
  rank : Nat
  /-- The modulus of the lower-bound check; any value at least `2` is sound. -/
  modulus : Nat
  /-- Pivot rows, in elimination order. -/
  rows : List Nat
  /-- Pivot columns, increasing. -/
  cols : List Nat
  /-- Column `j` of `V`, its leading entries reduced modulo `modulus`;
  entries past the end of a column are zero. -/
  vt : List (List Nat)
  /-- The nonzero denominator; `det B` for the producer. -/
  denom : Int
  /-- Coefficients of the non-pivot rows over the pivot rows, in increasing
  row order. -/
  z : List (List Int)
  deriving Repr, Inhabited, DecidableEq

namespace RankWitness

open Packed (dotNat packRow packRows packCol packCols dotPacked)

/-! # Kernel primitives

Structural recursion over lists, `Nat.mul`/`Nat.add`/`Nat.mod` and
`Int.mul`/`Int.add` called directly, `Nat.beq`/`Nat.blt` for comparisons.
Nothing here touches `Array`, `Vector`, `Fin` or an instance chain, so the
kernel reduces each step in a bounded number of unfoldings.  The pivot
block is read in one walk of each pivot row against the increasing pivot
columns (`pickCols`), never by an indexed read per entry: `nthInt` is
`O(index)`, and reading `r²` entries that way cost as many list steps as
the arithmetic. -/

/-- Row `i` of a row list, `[]` past the end.  Structural recursion, one step
per element walked; `List.getD` is specified in terms of it. -/
@[expose] def nthRow : List (List Int) → Nat → List Int
  | [], _ => []
  | a :: _, 0 => a
  | _ :: as, i + 1 => nthRow as i

/-- Entry `j` of a row, `0` past the end. -/
@[expose] def nthInt : List Int → Nat → Int
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, j + 1 => nthInt as j

/-- The residue of `a` modulo `M`, as a natural number. -/
@[expose] def residue (M : Nat) (a : Int) : Nat := (Int.emod a (Int.ofNat M)).toNat

/-- Every entry is below `k`. -/
@[expose] def allLt (k : Nat) : List Nat → Bool
  | [] => true
  | i :: is => Nat.blt i k && allLt k is

/-- Strictly increasing. -/
@[expose] def strictInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: cs => Nat.blt a b && strictInc (b :: cs)

/-- A zero for every entry. -/
@[expose] def zerosLike : List Nat → List Nat
  | [] => []
  | _ :: cs => 0 :: zerosLike cs

/-- The entries of a row at the strictly increasing positions `cols`, reduced
modulo `M`, read in one walk of the row: `k` is the position of the row's
head, and every position in `cols` is at least `k`.  A position past the
end of the row reads as `0`. -/
@[expose] def pickCols (M : Nat) : List Nat → Nat → List Int → List Nat
  | [], _, _ => []
  | cs, _, [] => zerosLike cs
  | c :: cs, k, a :: as =>
      cond (Nat.beq c k) (residue M a :: pickCols M cs (k + 1) as)
        (pickCols M (c :: cs) (k + 1) as)

/-- Membership by `Nat.beq`. -/
@[expose] def memNat (i : Nat) : List Nat → Bool
  | [] => false
  | r :: rs => Nat.beq i r || memNat i rs

/-- The row `b` is orthogonal modulo `M` to every column in the list. -/
@[expose] def zeroRow (M : Nat) (b : List Nat) : List (List Nat) → Bool
  | [] => true
  | c :: cs => Nat.beq (Nat.mod (dotNat b c) M) 0 && zeroRow M b cs

/-- `b ⬝ c ≡ 1` modulo `M`. -/
@[expose] def unitDiag (M : Nat) (b c : List Nat) : Bool :=
  Nat.beq (Nat.mod (dotNat b c) M) 1

/-- Row `i` of `B` against columns `i, i + 1, …` of `V`: the diagonal entry is
`1` and the entries to its right vanish, modulo `M`.  Consumes one row and
one column per step. -/
@[expose] def lowerCheck (M : Nat) : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | b :: bs, c :: cs => unitDiag M b c && zeroRow M b cs && lowerCheck M bs cs
  | _, _ => false

/-! # Packed evaluation

The lower-bound dot products on Kronecker-packed rows (`Hex.Matrix.Packed`):
a row of residues is one number with `W`-bit slots and the dot product of a
row with a reverse-packed column is one multiplication, shift and mask in
the kernel instead of `r` multiply-adds.  Exactness needs entries below
`M` and `r · M² < 2^W`, which `checkRankListPacked` verifies. -/

/-- Every entry of every row is below `k`. -/
@[expose] def allLtRows (k : Nat) : List (List Nat) → Bool
  | [] => true
  | r :: rs => allLt k r && allLtRows k rs

/-- `zeroRow` on packed data. -/
@[expose] def zeroRowPacked (M W r : Nat) (b : Nat) : List Nat → Bool
  | [] => true
  | c :: cs => Nat.beq (Nat.mod (dotPacked W r b c) M) 0 && zeroRowPacked M W r b cs

/-- `lowerCheck` on packed data. -/
@[expose] def lowerCheckPacked (M W r : Nat) : List Nat → List Nat → Bool
  | [], [] => true
  | b :: bs, c :: cs =>
      Nat.beq (Nat.mod (dotPacked W r b c) M) 1 && zeroRowPacked M W r b cs &&
        lowerCheckPacked M W r bs cs
  | _, _ => false

/-- Structural form of `scaleRow`, the compiled implementation. -/
@[expose] def scaleRowImpl (d : Int) : List Int → List Int
  | [] => []
  | a :: as => Int.mul d a :: scaleRowImpl d as

/-- `d • a`; `List.rec` directly, as `Packed.dotInt`. -/
@[expose] noncomputable def scaleRow (d : Int) : List Int → List Int :=
  List.rec (motive := fun _ => List Int) [] (fun a _ ih => Int.mul d a :: ih)

@[simp] theorem scaleRow_nil (d : Int) : scaleRow d [] = [] := rfl
@[simp] theorem scaleRow_cons (d a : Int) (as : List Int) :
    scaleRow d (a :: as) = Int.mul d a :: scaleRow d as := rfl

@[csimp] theorem scaleRow_eq_impl : @scaleRow = @scaleRowImpl := by
  funext d a
  induction a with
  | nil => rfl
  | cons x xs ih => simp [scaleRowImpl, ih]

/-- Structural form of `addScaled`, the compiled implementation. -/
@[expose] def addScaledImpl (z : Int) : List Int → List Int → List Int
  | p :: ps, a :: as => Int.add (Int.mul z p) a :: addScaledImpl z ps as
  | _, _ => []

/-- `z • p + a`, stopping at the shorter list; `List.rec` directly, as `Packed.dotInt`. -/
@[expose] noncomputable def addScaled (z : Int) : List Int → List Int → List Int :=
  fun l₁ => List.rec (motive := fun _ => List Int → List Int) (fun _ => [])
    (fun p _ ih l₂ => match l₂ with
      | a :: as => Int.add (Int.mul z p) a :: ih as
      | [] => []) l₁

@[simp] theorem addScaled_nil (z : Int) (l : List Int) : addScaled z [] l = [] := rfl
@[simp] theorem addScaled_cons_nil (z p : Int) (ps : List Int) : addScaled z (p :: ps) [] = [] := rfl
@[simp] theorem addScaled_cons_cons (z p a : Int) (ps as : List Int) :
    addScaled z (p :: ps) (a :: as) = Int.add (Int.mul z p) a :: addScaled z ps as := rfl

@[csimp] theorem addScaled_eq_impl : @addScaled = @addScaledImpl := by
  funext z a b
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih => cases b with
    | nil => rfl
    | cons y ys => simp [addScaledImpl, ih]

/-- The zero row of length `m`. -/
@[expose] def zeros : Nat → List Int
  | 0 => []
  | k + 1 => 0 :: zeros k

/-- `Σ z_l • P_l`, a row of length `m`. -/
@[expose] def combo (m : Nat) : List Int → List (List Int) → List Int
  | z :: zs, p :: ps => addScaled z p (combo m zs ps)
  | _, _ => zeros m

/-- Equality of integer lists. -/
@[expose] def beqInt : List Int → List Int → Bool
  | a :: as, b :: bs => decide (a = b) && beqInt as bs
  | [], [] => true
  | _, _ => false

/-- Walk the rows of `A` from index `i`: a pivot row is skipped, a non-pivot
row `a` consumes the next coefficient row `z` and must satisfy
`d • a = combo z P`. -/
@[expose] def rowsCheck (d : Int) (rows : List Nat) (P : List (List Int)) (m : Nat) :
    Nat → List (List Int) → List (List Int) → Bool
  | _, [], [] => true
  | i, a :: as, zs =>
      cond (memNat i rows) (rowsCheck d rows P m (i + 1) as zs)
        (match zs with
          | z :: zs' => beqInt (scaleRow d a) (combo m z P) && rowsCheck d rows P m (i + 1) as zs'
          | [] => false)
  | _, [], _ :: _ => false

/-- `d • a = z · Pᵀ` entrywise on packed data: the entries of the non-pivot
row `a` against the packed columns of the pivot rows. -/
@[expose] def rowSpanPacked (W r : Nat) (d : Int) (zp : Nat × Nat) :
    List Int → List (Nat × Nat) → Bool
  | [], [] => true
  | x :: xs, c :: cs =>
      decide (Int.mul d x = Packed.dotIntPacked W r zp c) && rowSpanPacked W r d zp xs cs
  | _, _ => false

/-- `rowsCheck` on packed data: `Pcols` the packed columns of the pivot rows,
each non-pivot row's coefficients cut or padded to the rank and packed. -/
@[expose] def rowsCheckPacked (W r : Nat) (d : Int) (rows : List Nat) (Pcols : List (Nat × Nat)) :
    Nat → List (List Int) → List (List Int) → Bool
  | _, [], [] => true
  | i, a :: as, zs =>
      cond (memNat i rows) (rowsCheckPacked W r d rows Pcols (i + 1) as zs)
        (match zs with
          | z :: zs' => rowSpanPacked W r d (Packed.packSignedCut W r z) a Pcols &&
              rowsCheckPacked W r d rows Pcols (i + 1) as zs'
          | [] => false)
  | _, [], _ :: _ => false

/-- Every row has length `m`. -/
@[expose] def rowsLen (m : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => Nat.beq r.length m && rowsLen m rs

/-- The selected rows of `A`. -/
@[expose] def pivotRows (A : List (List Int)) (rows : List Nat) : List (List Int) :=
  rows.map fun i => nthRow A i

/-- The pivot block of `A`, reduced modulo `M`: each pivot row walked once
against the increasing pivot columns. -/
@[expose] def block (M : Nat) (A : List (List Int)) (rows cols : List Nat) : List (List Nat) :=
  rows.map fun i => pickCols M cols 0 (nthRow A i)

end RankWitness

open RankWitness in
/-- The kernel checker.  `A` is the matrix as a list of `n` rows of length
`m`.  Checks the shapes and index ranges, that the pivot columns increase,
`denom ≠ 0`, the modular lower bound and the integral upper bound; see the
module docstring. -/
@[expose] def checkRankList (n m : Nat) (A : List (List Int)) (c : RankWitness) : Bool :=
  Nat.beq A.length n && rowsLen m A &&
  Nat.blt 1 c.modulus &&
  Nat.beq c.rows.length c.rank && Nat.beq c.cols.length c.rank &&
  allLt n c.rows && allLt m c.cols && strictInc c.cols &&
  !(decide (c.denom = 0)) &&
  lowerCheck c.modulus (block c.modulus A c.rows c.cols) c.vt &&
  rowsCheck c.denom c.rows (pivotRows A c.rows) m 0 A c.z

open RankWitness in
/-- The kernel checker with both bounds on packed rows, slot width `W` and
entry bound `k`: `checkRankList` with `lowerCheck` replaced by
`lowerCheckPacked` on the packed block and columns and `rowsCheck` by
`rowsCheckPacked` on the packed columns of the pivot rows, plus the bounds
that make the packed dot products exact: every entry of `vt` below the
modulus and `rank · modulus² < 2^W`; every entry of `A` and of `z` below
`k > 0` in absolute value and `rank · k² < 2^W`.  A passing packed check
implies a passing `checkRankList`; see the companion's
`checkRankList_of_packed`. -/
@[expose] def checkRankListPacked (W k n m : Nat) (A : List (List Int)) (c : RankWitness) : Bool :=
  Nat.beq A.length n && rowsLen m A &&
  Nat.blt 1 c.modulus &&
  Nat.beq c.rows.length c.rank && Nat.beq c.cols.length c.rank &&
  allLt n c.rows && allLt m c.cols && strictInc c.cols &&
  !(decide (c.denom = 0)) &&
  allLtRows c.modulus c.vt &&
  Nat.blt (Nat.mul c.rank (Nat.mul c.modulus c.modulus)) (Nat.pow 2 W) &&
  lowerCheckPacked c.modulus W c.rank (Packed.packRows W (block c.modulus A c.rows c.cols))
    (Packed.packCols W c.rank c.vt) &&
  Nat.blt 0 k && Packed.allAbsLtRows k A && Packed.allAbsLtRows k c.z &&
  Nat.blt (Nat.mul c.rank (Nat.mul k k)) (Nat.pow 2 W) &&
  rowsCheckPacked W c.rank c.denom c.rows
    (Packed.packSignedCols W c.rank (Packed.columns m (pivotRows A c.rows))) 0 A c.z

/-! # The producer -/

variable {n m : Nat}

/-- The rows of a matrix as lists. -/
def toLists (A : Matrix Int n m) : List (List Int) := A.rows.toList.map (·.toList)

/-- The moduli tried in order, Mersenne primes.  Primality is irrelevant
to soundness; it makes the leading pivot-block determinants likely to be
units on the first try. -/
def witnessModuli : List Nat := [2147483647, 2305843009213693951, 618970019642690137449562111]

/-- The inverse of `u` modulo `M`, when `u` is a unit. -/
def invMod? (u M : Nat) : Option Nat :=
  let (g, s, _) := HexArith.extGcd (u % M) M
  if g = 1 then some (Int.emod s (Int.ofNat M)).toNat else none

private structure WitnessData (n m : Nat) where
  matrix : List (List Int)
  rank : Nat
  rows : List Nat
  cols : List Nat
  /-- The pivot block `B`, rows in elimination order, columns increasing. -/
  block : List (List Int)
  denom : Int
  z : List (List Int)

/-- The modulus-independent part of a kernel witness: the profile, the pivot
block, and the upper-bound coefficients from the full-block adjugate. -/
private def witnessData (A : Matrix Int n m) : WitnessData n m :=
  let c := rankCert A
  let r := c.rank
  let rowsL := c.rows.toList.map (·.val)
  let colsL := c.cols.toList.map (·.val)
  let B := selectedSubmatrix A c.rows c.cols
  let nonPivot := (List.finRange n).filter fun i => !(RankWitness.memNat i.val rowsL)
  let z := nonPivot.map fun i => (List.finRange r).map fun l =>
    (List.finRange r).foldl (fun acc k => acc + A[(i, c.cols[k])] * c.adj[(k, l)]) 0
  { matrix := toLists A, rank := r, rows := rowsL, cols := colsL
    block := toLists B, denom := c.denom, z := z }

/-- Gaussian elimination without pivoting modulo `M` on the residues of the
pivot block: the upper triangular factor `U` and the inverses of its
diagonal, or `none` at the first pivot that is not a unit, which is the
first leading principal minor that is not a unit modulo `M`. -/
private def upperFactorMod (M : Nat) (B : List (List Int)) :
    Option (Array (Array Nat) × Array Nat) := Id.run do
  let mut U : Array (Array Nat) := B.toArray.map fun row => row.toArray.map (RankWitness.residue M)
  let r := U.size
  let mut invDiag : Array Nat := #[]
  for k in [0:r] do
    let some inv := invMod? (U[k]![k]!) M | return none
    invDiag := invDiag.push inv
    let rowk := U[k]!
    for i in [k + 1:r] do
      let rowi := U[i]!
      let f := rowi[k]! * inv % M
      if f != 0 then
        U := U.set! i (Array.ofFn (n := r) fun j =>
          (rowi[j]! + (M - f * rowk[j]! % M)) % M)
  return some (U, invDiag)

/-- Column `j` of `V`, the last column of the inverse of the leading
`(j + 1) × (j + 1)` block of `U`, by back substitution modulo `M`: `j + 1`
entries. -/
private def solveColumn (M : Nat) (U : Array (Array Nat)) (invDiag : Array Nat) (j : Nat) :
    List Nat := Id.run do
  let mut v : Array Nat := Array.replicate (j + 1) 0
  v := v.set! j invDiag[j]!
  for t in [0:j] do
    let i := j - 1 - t
    let mut s := 0
    for k in [i + 1:j + 1] do
      s := (s + U[i]![k]! * v[k]!) % M
    v := v.set! i ((M - s) % M * invDiag[i]! % M)
  return v.toList

open RankWitness in
/-- Instantiate prepared witness data at one modulus: the columns of `V`
from one elimination of the pivot block modulo `M`, or a leading pivot
block that is not a unit, or a failed producer self-check. -/
private def rankWitnessOf (M : Nat) (d : WitnessData n m) : Except String RankWitness := do
  let some (U, invDiag) := upperFactorMod M d.block |
    throw s!"a leading pivot block of order at most {d.rank} is not a unit modulo {M}"
  let vt := (List.range d.rank).map (solveColumn M U invDiag)
  let w : RankWitness :=
    { rank := d.rank, modulus := M, rows := d.rows, cols := d.cols, vt := vt
      denom := d.denom, z := d.z }
  if checkRankList n m d.matrix w then pure w
  else throw s!"the witness fails its own check modulo {M}"

/-- The witness for one fixed modulus. The modulus-independent integer
reductions are shared across retries by `rankWitness`. -/
def rankWitnessWith (M : Nat) (A : Matrix Int n m) : Except String RankWitness :=
  rankWitnessOf M (witnessData A)

/-- The kernel witness of an integer matrix: the first modulus in
`witnessModuli` that works, or the reasons every modulus failed. -/
def rankWitness (A : Matrix Int n m) : Except String RankWitness :=
  go (witnessData A) witnessModuli []
where
  /-- Try the moduli in order, collecting the failure reasons. -/
  go (d : WitnessData n m) : List Nat → List String → Except String RankWitness
    | [], reasons => throw (String.intercalate "; " reasons.reverse)
    | M :: Ms, reasons =>
        match rankWitnessOf M d with
        | .ok w => pure w
        | .error e => go d Ms (e :: reasons)

/-- Compiled sanity check on a `3 × 4` matrix of rank `2`, and the same
witness replayed by the kernel. -/
private def witnessExample : Matrix Int 3 4 := #m[1, 2, 3, 4; 2, 4, 6, 8; 1, 0, 1, 0]

#guard (rankWitness witnessExample).toOption.map (·.rank) = some 2
#guard (rankWitness witnessExample).toOption.all fun w =>
  checkRankList 3 4 (toLists witnessExample) w

end Hex.Matrix
