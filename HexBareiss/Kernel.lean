/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss.Bareiss
public import HexArith.ExactDiv
public import HexMatrix.Notation

public section

/-!
The kernel certificate for the determinant: `DetWitness`, its checker
`checkDetList`, and the producer `detWitness`.

`bareissWith` is the reference computation, and replaying it in the kernel
is the wrong certificate: the kernel would traverse `Vector` buffers, rebuild
`ofFn` matrices at every access and run the pivot search and the exact
divisions.  The kernel form is the triangularization the elimination
produces, checked as lists.

For `A` an `n × n` integer matrix given as a row list, a nonsingular
witness carries

* the row swaps of the pivot search, `swaps`, in the order they were applied;
  the kernel arranges the rows itself and reads the sign of the arrangement
  off the number of swaps;
* the transform `L`, one row per pivot: row `i` lists its `i + 1` leading
  entries, so `L` is lower triangular with diagonal `lᵢ`, the last entry of
  each row, all nonzero;
* the value `d`.

The check computes, for every row `i` of `L`, its products with the columns
`0, …, i` of the arranged matrix: the first `i` must vanish and the last is
the diagonal entry `uᵢ` of the upper triangular product `U = L · σA`.  Then
`det L · det (σA) = det U`, that is `(∏ lᵢ) · det (σA) = ∏ uᵢ`, and the value
is confirmed by `(∏ lᵢ) · d = sign σ · ∏ uᵢ` over `Int`.  The cost is about
`n³ / 3` products of minor-sized integers.  Nothing above the diagonal of
`U` is computed.

A singular matrix is certified more cheaply by a nonzero integer row vector
`v` with `v · A = 0`, checked as `n²` products; the value is `0`.

The producer is the row-pivoted fraction-free elimination in echelon form,
run on `[A | I]` so that the right block is the transform: after `r`
pivots the block entries are minors of `[A | I]`, so every division is
exact.  With full rank the transform's diagonal is `1, d₁, …, dₙ₋₁` and the
triangular product's is `d₁, …, dₙ` (the leading principal minors of the
arranged matrix), so `d = sign σ · dₙ`.  With fewer than `n` pivots the last
row of the triangular product is zero, so the last row of the right block
is a left kernel vector.  The producer re-checks its own output before
returning it.

The soundness theorem `det_eq_of_checkList` (`Matrix.det` of the Mathlib
matrix equals the value) is in `HexBareissMathlib`.
-/

namespace Hex.Matrix

/-- A kernel-checkable determinant certificate.  See the module docstring. -/
inductive DetWitness where
  /-- A triangularization: the row swaps in application order, the rows of the
  lower triangular transform (row `i` holds its `i + 1` leading entries), and
  the value. -/
  | triangular (swaps : List (Nat × Nat)) (transform : List (List Int)) (value : Int)
  /-- A nonzero left kernel vector: the value is `0`. -/
  | singular (vec : List Int)
  deriving Repr, Inhabited, DecidableEq

namespace DetWitness

/-- The certified value. -/
@[expose] def value : DetWitness → Int
  | .triangular _ _ d => d
  | .singular _ => 0

/-! # Kernel primitives

Structural recursion over lists, `Int.mul`/`Int.add`/`Int.neg` called
directly, `Nat.beq`/`Nat.blt` and `Int.decEq` for comparisons.  Nothing here
touches `Array`, `Vector`, `Fin` or an instance chain, so the kernel reduces
each step in a bounded number of unfoldings. -/

/-- Row `i` of a row list, `[]` past the end. -/
@[expose] def nthRow : List (List Int) → Nat → List Int
  | [], _ => []
  | a :: _, 0 => a
  | _ :: as, i + 1 => nthRow as i

/-- Entry `j` of a row, `0` past the end. -/
@[expose] def nthInt : List Int → Nat → Int
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, j + 1 => nthInt as j

/-- Row `i` replaced by `r`; unchanged past the end. -/
@[expose] def replaceRow : List (List Int) → Nat → List Int → List (List Int)
  | [], _, _ => []
  | _ :: as, 0, r => r :: as
  | a :: as, i + 1, r => a :: replaceRow as i r

/-- Rows `a` and `b` exchanged. -/
@[expose] def swapRows (a b : Nat) (A : List (List Int)) : List (List Int) :=
  replaceRow (replaceRow A a (nthRow A b)) b (nthRow A a)

/-- The swaps applied in order. -/
@[expose] def applySwaps : List (Nat × Nat) → List (List Int) → List (List Int)
  | [], A => A
  | (a, b) :: s, A => applySwaps s (swapRows a b A)

/-- Every swap exchanges two distinct rows below `n`. -/
@[expose] def swapsOk (n : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (a, b) :: s => Nat.blt a n && Nat.blt b n && !(Nat.beq a b) && swapsOk n s

/-- The sign of the arrangement: `(-1)^(number of swaps)`. -/
@[expose] def signOf : List (Nat × Nat) → Int
  | [] => 1
  | _ :: s => Int.neg (signOf s)

/-- Every row has length `m`. -/
@[expose] def rowsLen (m : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => Nat.beq r.length m && rowsLen m rs

/-- The dot product of two integer lists, stopping at the shorter. -/
@[expose] def dotInt : List Int → List Int → Int
  | a :: as, b :: bs => Int.add (Int.mul a b) (dotInt as bs)
  | _, _ => 0

/-- Column `j` of a row list. -/
@[expose] def column (j : Nat) : List (List Int) → List Int
  | [] => []
  | r :: rs => nthInt r j :: column j rs

/-- Columns `j, …, j + k - 1` of a row list. -/
@[expose] def columnsFrom (A : List (List Int)) (j : Nat) : Nat → List (List Int)
  | 0 => []
  | k + 1 => column j A :: columnsFrom A (j + 1) k

/-- The `m` columns of a row list. -/
@[expose] def columns (m : Nat) (A : List (List Int)) : List (List Int) := columnsFrom A 0 m

/-- The row is orthogonal to every column in the list. -/
@[expose] def zeroDots (t : List Int) : List (List Int) → Bool
  | [] => true
  | c :: cs => decide (dotInt t c = 0) && zeroDots t cs

/-- Some entry is nonzero. -/
@[expose] def anyNonzero : List Int → Bool
  | [] => false
  | a :: as => !(decide (a = 0)) || anyNonzero as

/-- Walk the transform rows against the columns of the arranged matrix.  Row
`i` (with `done` the `i` columns already passed, in any order) must have
length `i + 1`, a nonzero last entry `lᵢ`, and zero products with the
earlier columns; its product with column `i` is the diagonal entry `uᵢ` of
the triangular product.  `pl` and `pu` accumulate `∏ lᵢ` and `sign · ∏ uᵢ`,
and at the end `pl · d = pu` is required. -/
@[expose] def triangularCheck (d : Int) :
    List (List Int) → Nat → List (List Int) → List (List Int) → Int → Int → Bool
  | _, _, [], [], pl, pu => decide (Int.mul pl d = pu)
  | done, i, t :: ts, c :: cs, pl, pu =>
      let l := nthInt t i
      Nat.beq t.length (i + 1) && !(decide (l = 0)) && zeroDots t done &&
        triangularCheck d (c :: done) (i + 1) ts cs (Int.mul pl l) (Int.mul pu (dotInt t c))
  | _, _, _, _, _, _ => false

/-! # Rational rows

A rational matrix is certified through an integer one: every row is scaled
by a positive integer to an integer row, the integer matrix carries the
witness, and the value is confirmed against the product of the scales.  The
rational arithmetic is `Rat.mul` and `Rat.ofInt` on `n²` entries, one
`Rat.decEq` each. -/

/-- `k • q = b` entrywise. -/
@[expose] def scaledRow (k : Nat) : List Rat → List Int → Bool
  | [], [] => true
  | q :: qs, b :: bs => decide (Rat.mul (Rat.ofInt (Int.ofNat k)) q = Rat.ofInt b) && scaledRow k qs bs
  | _, _ => false

/-- Every row of `A` scaled by its positive scale is the row of `B`. -/
@[expose] def scaledRows : List Nat → List (List Rat) → List (List Int) → Bool
  | [], [], [] => true
  | k :: ks, q :: qs, b :: bs => Nat.blt 0 k && scaledRow k q b && scaledRows ks qs bs
  | _, _, _ => false

/-- The product of the scales. -/
@[expose] def prodNat : List Nat → Nat
  | [] => 1
  | k :: ks => Nat.mul k (prodNat ks)

end DetWitness

open DetWitness in
/-- The kernel checker.  `A` is the matrix as a list of `n` rows of length
`n`.  Checks the shape, and then either the triangularization or the left
kernel vector; see the module docstring. -/
@[expose] def checkDetList (n : Nat) (A : List (List Int)) : DetWitness → Bool
  | .triangular swaps T d =>
      Nat.beq A.length n && rowsLen n A && swapsOk n swaps &&
        triangularCheck d [] 0 T (columns n (applySwaps swaps A)) 1 (signOf swaps)
  | .singular v =>
      Nat.beq A.length n && rowsLen n A && Nat.beq v.length n && anyNonzero v &&
        zeroDots v (columns n A)

open DetWitness in
/-- The kernel checker for a rational matrix `A` given as `n` rows: the
scales `s` take the rows of `A` to the rows of the integer matrix `B`, which
`c` certifies, and the value `v` satisfies `v · ∏ s = value c`. -/
@[expose] def checkDetRat (n : Nat) (A : List (List Rat)) (s : List Nat) (B : List (List Int))
    (c : DetWitness) (v : Rat) : Bool :=
  Nat.beq A.length n && Nat.beq s.length n && scaledRows s A B && checkDetList n B c &&
    decide (Rat.mul v (Rat.ofInt (Int.ofNat (prodNat s))) = Rat.ofInt c.value)

/-! # The producer -/

variable {n : Nat}

/-- The rows of a square matrix as lists. -/
def rowLists (A : Matrix Int n n) : List (List Int) := A.rows.toList.map (·.toList)

namespace DetWitness

/-- The state of the elimination on `[A | I]`: the current left block, the
current right block, the original index of each current row, the swaps so
far (reversed), the previous pivot, and the number of pivots found. -/
private structure Elim where
  left : Array (Array Int)
  right : Array (Array Int)
  perm : Array Nat
  swaps : List (Nat × Nat)
  prev : Int
  pivots : Nat

/-- The first row at or below `r` with a nonzero entry in column `c`. -/
private def findPivot (M : Array (Array Int)) (r c : Nat) : Option Nat :=
  (List.range (M.size - r)).findSome? fun k =>
    let i := r + k
    if M[i]![c]! != 0 then some i else none

/-- One fraction-free step: the pivot in column `c` is moved to row `r` and
rows below `r` are eliminated in both blocks. -/
private def step (e : Elim) (c : Nat) : Elim :=
  let r := e.pivots
  match findPivot e.left r c with
  | none => e
  | some i =>
    let e := if i = r then e else
      { e with left := e.left.swapIfInBounds r i, right := e.right.swapIfInBounds r i,
               perm := e.perm.swapIfInBounds r i, swaps := (r, i) :: e.swaps }
    let p := e.left[r]![c]!
    let pivotL := e.left[r]!
    let pivotR := e.right[r]!
    let update (M : Array (Array Int)) (pivotRow : Array Int) : Array (Array Int) :=
      (List.range M.size).foldl (init := M) fun M i =>
        if i ≤ r then M else
          let f := e.left[i]![c]!
          M.set! i <| (M[i]!).zipWith (fun x y => HexArith.Int.exactDiv (p * x - f * y) e.prev) pivotRow
    { e with left := update e.left pivotL, right := update e.right pivotR, prev := p,
             pivots := r + 1 }

/-- The witness assembled from a finished elimination. -/
private def assemble (n : Nat) (e : Elim) : DetWitness :=
  if e.pivots = n then
    let sign : Int := if e.swaps.length % 2 = 0 then 1 else -1
    let transform := (List.range n).map fun i =>
      (List.range (i + 1)).map fun k => e.right[i]![e.perm[k]!]!
    let last := if n = 0 then 1 else e.left[n - 1]![n - 1]!
    .triangular e.swaps.reverse transform (sign * last)
  else
    .singular (e.right[n - 1]!.toList)

end DetWitness

open DetWitness in
/-- The kernel witness of a square integer matrix given as `n` rows of length
`n`, by fraction-free elimination on `[A | I]`, or the reason its own check
fails. -/
def detWitnessOfLists (n : Nat) (A : List (List Int)) : Except String DetWitness := do
  unless A.length = n ∧ A.all (·.length = n) do
    throw s!"the matrix is not {n} × {n}"
  let left : Array (Array Int) := (A.map (·.toArray)).toArray
  let right : Array (Array Int) := (List.range n).toArray.map fun i =>
    (List.range n).toArray.map fun j => if i = j then 1 else 0
  let e : Elim := { left, right, perm := (List.range n).toArray, swaps := [], prev := 1, pivots := 0 }
  let e := (List.range n).foldl step e
  let w := assemble n e
  if checkDetList n A w then pure w
  else throw "the witness fails its own check"

/-- The kernel witness of a square integer matrix. -/
def detWitness (A : Matrix Int n n) : Except String DetWitness :=
  detWitnessOfLists n (rowLists A)

/-- Compiled sanity checks: a `3 × 3` matrix needing a row swap, a singular
`3 × 3` matrix, and the same witnesses replayed by the kernel. -/
private def witnessExample : Matrix Int 3 3 := #m[0, 2, 1; 3, 1, 4; 1, 5, 9]

private def singularExample : Matrix Int 3 3 := #m[1, 2, 3; 2, 4, 6; 1, 0, 1]

#guard (detWitness witnessExample).toOption.map (·.value) = some (-32)
#guard (detWitness witnessExample).toOption.all fun w => checkDetList 3 (rowLists witnessExample) w
#guard (detWitness singularExample).toOption.map (·.value) = some 0
#guard (detWitness singularExample).toOption.all fun w => checkDetList 3 (rowLists singularExample) w
#guard (detWitnessOfLists 0 []).toOption.map (·.value) = some 1
#guard (detWitnessOfLists 2 [[1, 2], [3, 4]]).toOption.all fun w =>
  checkDetRat 2 [[1 / 2, 1], [3 / 2, 2]] [2, 2] [[1, 2], [3, 4]] w (-1 / 2)

end Hex.Matrix
