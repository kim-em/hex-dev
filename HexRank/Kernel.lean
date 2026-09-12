/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Int
public import HexArith.ExtGcd
public import HexMatrix.Notation

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
restricted to a row).  Column `j` of `V` is the last column of the adjugate
of the leading `(j + 1) × (j + 1)` pivot block, scaled by the inverse of that
block's determinant modulo `modulus`.  Thus `V` is upper triangular and
`B * V` is lower triangular with unit diagonal.  It re-checks its own output
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

/-! # Kernel primitives

Structural recursion over lists, `Nat.mul`/`Nat.add`/`Nat.mod` and
`Int.mul`/`Int.add` called directly, `Nat.beq`/`Nat.blt` for comparisons.
Nothing here touches `Array`, `Vector`, `Fin` or an instance chain, so the
kernel reduces each step in a bounded number of unfoldings. -/

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

/-- The dot product of two natural-number lists, stopping at the shorter. -/
@[expose] def dotNat : List Nat → List Nat → Nat
  | a :: as, b :: bs => Nat.add (Nat.mul a b) (dotNat as bs)
  | _, _ => 0

/-- Every entry is below `k`. -/
@[expose] def allLt (k : Nat) : List Nat → Bool
  | [] => true
  | i :: is => Nat.blt i k && allLt k is

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

/-- `d • a`. -/
@[expose] def scaleRow (d : Int) : List Int → List Int
  | [] => []
  | a :: as => Int.mul d a :: scaleRow d as

/-- `z • p + a`, stopping at the shorter list. -/
@[expose] def addScaled (z : Int) : List Int → List Int → List Int
  | p :: ps, a :: as => Int.add (Int.mul z p) a :: addScaled z ps as
  | _, _ => []

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

/-- Every row has length `m`. -/
@[expose] def rowsLen (m : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => Nat.beq r.length m && rowsLen m rs

/-- The selected rows of `A`. -/
@[expose] def pivotRows (A : List (List Int)) (rows : List Nat) : List (List Int) :=
  rows.map fun i => nthRow A i

/-- The pivot block of `A`, reduced modulo `M`. -/
@[expose] def block (M : Nat) (A : List (List Int)) (rows cols : List Nat) : List (List Nat) :=
  rows.map fun i => cols.map fun j => residue M (nthInt (nthRow A i) j)

end RankWitness

open RankWitness in
/-- The kernel checker.  `A` is the matrix as a list of `n` rows of length
`m`.  Checks the shapes and index ranges, `denom ≠ 0`, the modular lower
bound and the integral upper bound; see the module docstring. -/
@[expose] def checkRankList (n m : Nat) (A : List (List Int)) (c : RankWitness) : Bool :=
  Nat.beq A.length n && rowsLen m A &&
  Nat.blt 1 c.modulus &&
  Nat.beq c.rows.length c.rank && Nat.beq c.cols.length c.rank &&
  allLt n c.rows && allLt m c.cols &&
  !(decide (c.denom = 0)) &&
  lowerCheck c.modulus (block c.modulus A c.rows c.cols) c.vt &&
  rowsCheck c.denom c.rows (pivotRows A c.rows) m 0 A c.z

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

private structure LeadingColumn where
  order : Nat
  denom : Int
  entries : List Int

private structure WitnessData (n m : Nat) where
  matrix : List (List Int)
  rank : Nat
  rows : List Nat
  cols : List Nat
  leading : List LeadingColumn
  denom : Int
  z : List (List Int)

/-- Compute the modulus-independent part of a kernel witness once, including
the adjugate column and denominator of every leading pivot block. -/
private def witnessData (A : Matrix Int n m) : WitnessData n m :=
  let c := rankCert A
  let r := c.rank
  let rowsL := c.rows.toList.map (·.val)
  let colsL := c.cols.toList.map (·.val)
  let B := selectedSubmatrix A c.rows c.cols
  let leading := (List.finRange r).map fun j =>
    let k := j.val + 1
    if h : k = r then
      { order := k, denom := c.denom
        entries := (List.finRange k).map fun i => c.adj[(Fin.cast h i, j)] }
    else
      let Bk : Matrix Int k k := ofFn fun i l =>
        B[((⟨i.val, by omega⟩ : Fin r), (⟨l.val, by omega⟩ : Fin r))]
      let Dk := rowReduceFF (augmentIdentity Bk)
      { order := k, denom := Dk.denom
        entries := (List.finRange k).map fun i => (adjugateOf Dk)[(i, Fin.last j.val)] }
  let nonPivot := (List.finRange n).filter fun i => !(RankWitness.memNat i.val rowsL)
  let z := nonPivot.map fun i => (List.finRange r).map fun l =>
    (List.finRange r).foldl (fun acc k => acc + A[(i, c.cols[k])] * c.adj[(k, l)]) 0
  { matrix := toLists A, rank := r, rows := rowsL, cols := colsL
    leading := leading, denom := c.denom, z := z }

open RankWitness in
/-- Instantiate prepared witness data at one modulus, or report a non-unit
leading pivot-block denominator or a failed producer self-check. -/
private def rankWitnessOf (M : Nat) (d : WitnessData n m) : Except String RankWitness := do
  let vt ← d.leading.mapM fun col => do
    let some dinv := invMod? (residue M col.denom) M |
      throw s!"the leading pivot-block denominator {col.denom} of order {col.order} is not a unit modulo {M}"
    pure <| col.entries.map fun x => Nat.mod (Nat.mul (residue M x) dinv) M
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
