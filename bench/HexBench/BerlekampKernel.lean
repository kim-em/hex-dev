/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexBerlekampZassenhaus
import Lean.Data.Json

/-!
# Berlekamp fixed-space kernel attribution and packed-representation pricing

Diagnostic support for issue #9132's measurement gate. Two things live here.

**Attribution.** `kernelPhases` walks one Berlekamp fixed-space kernel
computation stage by stage, calling the production function each stage names in
production order: the Frobenius power `X^p mod f`, the column-polynomial
recurrence, the conversion of those columns into the generic `Hex.Matrix`
representation, the diagonal decrement that forms `Q_f - I`, Gauss-Jordan pivot
search, row swap and scale, row addition, the nullspace-basis construction, and
the conversion of basis vectors back to polynomials.

Gauss-Jordan is the one place this does not call the production function
verbatim: `Hex.Matrix.rowReduce`'s loop reports only its final
`RowEchelonData`, so `countedRowReduce` mirrors `rowReduceLoop` column for
column -- same pivot rule, same elimination order, same elementary operations
from `HexMatrix.Elementary` -- while marking the clock between stages. The
mirror is checked against the production `rowReduce` on every call, and the
driver fails loudly on any disagreement. Marks are taken once per pivot column,
not once per row operation, so the clock reads cost `O(n)` rather than `O(n^2)`.

**Pricing.** The same mirror is instantiated four more ways, to separate the
three costs a packed representation would remove:

* `countedRowReduce` with `transform := false` drops the `n x n` row-operation
  transform that `rowReduce` maintains in lockstep and that the nullspace never
  reads;
* `packedReduce .word` stores entries as raw `UInt64` words in one contiguous
  row-major `Array` and multiplies through a Barrett reciprocal;
* `packedReduce .halfWord` stores them as `UInt32` instead, which is faithful
  because `ZMod64.Bounds` caps the modulus at `2^31`, and which boxes without
  allocating on a 64-bit runtime;
* `packedReduce .halfWordDiv` is the same `UInt32` storage with a hardware
  remainder in place of the Barrett reciprocal, isolating the division cost.

Every packed variant recomputes the rank and the nullspace basis and is checked
entry for entry against the production `Hex.Matrix.nullspace`, so a variant that
is fast because it is wrong cannot be reported as fast.

**Attribution of the integrated packed kernel** (issue #9160). The landed
`Hex.Berlekamp.Packed` loop is slower than the prototype above, and the gap is
scaffolding rather than arithmetic. Two measurements separate it.

* `countedPackedReduce` mirrors `Packed.reduceLoop` column for column and marks
  the clock once per pivot column, splitting the reduction into pivot search,
  row swap and scale, and column elimination. It is checked against the
  production `Packed.reduce` on every call.
* `ladderLoop` is that same loop with its column elimination passed in, so a
  rung can drop exactly one scaffolding choice: `Packed.eliminateColumn`
  verbatim, then the same with the pivot row read once per column instead of
  once per row addition, then the same again writing the flat backing buffer
  directly instead of through `Matrix.modifyEntries`, and finally the prototype
  loop above run on the packed buffer, which additionally drops the
  `List.finRange`/`List.concat` scaffolding. Successive differences attribute
  the gap; the last rung's difference from the prototype's own column is the
  residual.

The inner modular multiply is priced by `eliminateFlatDoubleMul`, which performs
a second, salted modular multiply per inner-loop entry and combines the two
results by `min`. The salt is an `IO.Ref` holding zero, so the second product
equals the first and the reduction stays correct entry for entry, while the
compiler cannot fold the two together. Its excess over `eliminateFlatSalted`,
which performs the salted multiply alone, is the marginal in-situ cost of one
modular multiply across the whole reduction.

This module is a diagnostic; nothing here is reachable from
`Hex.ZPoly.factorize`.
-/

open Lean (Json JsonNumber)
open Hex

namespace HexBench.BerlekampKernel

/-! ## Timing marks -/

/-- A clock and small-allocation reading. -/
structure Mark where
  /-- Monotonic nanoseconds. -/
  nanos : Nat
  /-- Small allocations performed on this thread so far. -/
  allocs : Nat

/-- Read the clock and the small-allocation counter. -/
def mark : IO Mark := do
  let allocs ← IO.getNumHeartbeats
  let nanos ← IO.monoNanosNow
  return { nanos, allocs }

/-- Nanoseconds and small allocations between two marks. -/
def Mark.since (stop start : Mark) : Nat × Nat :=
  (stop.nanos - start.nanos, stop.allocs - start.allocs)

private def natJson (n : Nat) : Json :=
  Json.num (JsonNumber.fromInt (Int.ofNat n))

/-- A `{nanos, smallAllocs}` object, the shape the phase-profile record uses. -/
def spanJson (nanos allocs : Nat) : Json :=
  Json.mkObj [("nanos", natJson nanos), ("smallAllocs", natJson allocs)]

/-- Kilobytes reported on a `/proc/self/status` line such as `VmHWM:  1234 kB`. -/
private def statusKilobytes (text field : String) : Nat := Id.run do
  for line in text.splitOn "\n" do
    if line.startsWith field then
      let digits := line.toList.filter Char.isDigit
      return (String.ofList digits).toNat?.getD 0
  return 0

/-- Resident set size of this process in bytes, read from `/proc/self/status`.
`peak := true` reads the high-water mark. Returns `0` where the file is
unavailable, which is the honest reading on a platform that does not publish
it. -/
def residentBytes (peak : Bool) : IO Nat := do
  let path : System.FilePath := "/proc/self/status"
  if !(← path.pathExists) then
    return 0
  let text ← IO.FS.readFile path
  return statusKilobytes text (if peak then "VmHWM:" else "VmRSS:") * 1024

/-! ## Counted Gauss-Jordan mirror

`Hex.Matrix.rowReduce` keeps its pivot search and its column elimination
private, so the attribution mirrors them here. Both mirrors use the public
elementary operations from `HexMatrix.Elementary`, so the arithmetic being timed
is the production arithmetic; only the loop scaffolding is duplicated.
-/

variable {R : Type} [Lean.Grind.Field R] [DecidableEq R] {n m : Nat}

/-- Pivot search: the first row at or below `start` whose `col` entry is
nonzero. Mirrors `Hex.Matrix.findPivot?`. -/
private def findPivotAux (M : Matrix R n m) (col : Fin m) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[(i, col)] = 0 then findPivotAux M col (start + 1) fuel else some i
      else
        none

/-- Pivot search from `start`. Mirrors `Hex.Matrix.findPivot?`. -/
private def findPivot? (M : Matrix R n m) (col : Fin m) (start : Nat) :
    Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- Running attribution of one counted Gauss-Jordan run. -/
structure ReduceCounters where
  /-- Nanoseconds in pivot search. -/
  pivotNanos : Nat := 0
  /-- Small allocations in pivot search. -/
  pivotAllocs : Nat := 0
  /-- Nanoseconds in row swap, row scale, and the `O(n)` column pass that
  counts the eliminations the next stage will perform. -/
  swapScaleNanos : Nat := 0
  /-- Small allocations in row swap, row scale, and the column count. -/
  swapScaleAllocs : Nat := 0
  /-- Nanoseconds in row addition. -/
  rowAddNanos : Nat := 0
  /-- Small allocations in row addition. -/
  rowAddAllocs : Nat := 0
  /-- Row additions actually performed. -/
  rowAdds : Nat := 0
  /-- Eliminations skipped because the coefficient was already zero. -/
  rowAddsSkipped : Nat := 0
  /-- Pivot columns found. -/
  pivots : Nat := 0
  /-- Columns inspected and found pivot-free. -/
  freeColumns : Nat := 0

/-- Result of a counted Gauss-Jordan run: the same data `rowReduce` returns,
plus the attribution. -/
structure ReduceResult (R : Type) (n m : Nat) where
  /-- The reduced matrix. -/
  echelon : Matrix R n m
  /-- The accumulated transform, or the identity when the run skipped it. -/
  transform : Matrix R n n
  /-- Pivot columns in increasing order. -/
  pivots : List (Fin m)
  /-- Per-stage attribution. -/
  counters : ReduceCounters

/-- Row additions a column elimination will perform, and the ones it will skip.
Counted in a separate `O(n)` pass over the pivot column so that the elimination
fold below can keep the exact pair shape `Hex.Matrix.eliminateColumn` has: a
fold threading extra counters would hold a second reference to the matrix and
defeat the in-place update the production path relies on. -/
private def countColumn (M : Matrix R n m) (pivotRow : Fin n) (col : Fin m) :
    Nat × Nat :=
  (List.finRange n).foldl
    (fun (acc : Nat × Nat) j =>
      if j = pivotRow then acc
      else if M[(j, col)] = 0 then (acc.1, acc.2 + 1) else (acc.1 + 1, acc.2))
    (0, 0)

/-- Eliminate every non-pivot entry of a pivot column. Mirrors
`Hex.Matrix.eliminateColumn` shape for shape; `withTransform := false` drops the
transform update, which no nullspace consumer reads. -/
private def eliminateColumn (withTransform : Bool) (M : Matrix R n m)
    (T : Matrix R n n) (pivotRow : Fin n) (col : Fin m) :
    Matrix R n m × Matrix R n n :=
  (List.finRange n).foldl
    (fun (state : Matrix R n m × Matrix R n n) j =>
      if j = pivotRow then
        state
      else
        let coeff := -state.1[(j, col)]
        if coeff = 0 then
          state
        else
          ( Matrix.rowAdd state.1 pivotRow j coeff,
            if withTransform then Matrix.rowAdd state.2 pivotRow j coeff
            else state.2 ))
    (M, T)

/-- Gauss-Jordan elimination mirroring `Hex.Matrix.rowReduceLoop`, marking the
clock once per column rather than once per row operation. -/
private partial def reduceLoop (withTransform : Bool) (col : Nat)
    (row : Nat) (echelon : Matrix R n m) (transform : Matrix R n n)
    (pivots : List (Fin m)) (c : ReduceCounters) :
    IO (ReduceResult R n m) := do
  if hRow : row < n then
    if hCol : col < m then
      let colFin : Fin m := ⟨col, hCol⟩
      let t0 ← mark
      let found := findPivot? echelon colFin row
      let t1 ← mark
      let (pn, pa) := t1.since t0
      let c := { c with pivotNanos := c.pivotNanos + pn,
                        pivotAllocs := c.pivotAllocs + pa }
      match found with
      | none =>
          reduceLoop withTransform (col + 1) row echelon transform pivots
            { c with freeColumns := c.freeColumns + 1 }
      | some pivot =>
          let target : Fin n := ⟨row, hRow⟩
          let swappedEchelon := Matrix.rowSwap echelon target pivot
          let swappedTransform :=
            if withTransform then Matrix.rowSwap transform target pivot
            else transform
          let pivotVal := swappedEchelon[(target, colFin)]
          let scaledEchelon := Matrix.rowScale swappedEchelon target pivotVal⁻¹
          let scaledTransform :=
            if withTransform then Matrix.rowScale swappedTransform target pivotVal⁻¹
            else swappedTransform
          let (adds, skipped) := countColumn scaledEchelon target colFin
          let t2 ← mark
          let (sn, sa) := t2.since t1
          let (e, tr) :=
            eliminateColumn withTransform scaledEchelon scaledTransform target colFin
          let t3 ← mark
          let (en, ea) := t3.since t2
          reduceLoop withTransform (col + 1) (row + 1) e tr (pivots.concat colFin)
            { c with
                swapScaleNanos := c.swapScaleNanos + sn
                swapScaleAllocs := c.swapScaleAllocs + sa
                rowAddNanos := c.rowAddNanos + en
                rowAddAllocs := c.rowAddAllocs + ea
                rowAdds := c.rowAdds + adds
                rowAddsSkipped := c.rowAddsSkipped + skipped
                pivots := c.pivots + 1 }
    else
      return { echelon, transform, pivots, counters := c }
  else
    return { echelon, transform, pivots, counters := c }

/-- Counted Gauss-Jordan elimination of `M`. With `withTransform := true` this
mirrors `Hex.Matrix.rowReduce` exactly and is checked against it; with
`withTransform := false` the `n x n` transform is not maintained, which prices
the half of the elementary-operation work the nullspace never reads. -/
def countedRowReduce (withTransform : Bool) (M : Matrix R n m) :
    IO (ReduceResult R n m) :=
  reduceLoop withTransform 0 0 M (Matrix.identity n) [] {}

/-- The counted mirror agrees with the production `rowReduce`. Checked on every
call so a divergent mirror cannot silently report attribution for an algorithm
production does not run. -/
def mirrorAgrees [BEq R] (M : Matrix R n m) (r : ReduceResult R n m) : Bool :=
  let D := Matrix.rowReduce M
  D.rank == r.pivots.length
    && D.echelon == r.echelon
    && D.pivotCols.toList == r.pivots

/-! ## Packed prototype

A contiguous row-major buffer of machine words with the modulus's Barrett
reciprocal alongside it. This is the representation issue #9132 proposes,
prototyped here to price it before any production specialization is written.
-/

/-- Which packed element storage and modular multiply to price. -/
inductive PackedKind where
  /-- Raw `UInt64` words, Barrett multiply. Boxing a `UInt64` allocates. -/
  | word
  /-- `UInt32` words, Barrett multiply. Boxing a `UInt32` does not allocate on a
  64-bit runtime, and `ZMod64.Bounds` caps the modulus at `2^31`. -/
  | halfWord
  /-- `UInt32` words, hardware remainder instead of a Barrett reciprocal. -/
  | halfWordDiv
  /-- `UInt32` words and a Barrett reciprocal, additionally skipping the
  multiply where the source-row entry is already zero. Prices an algorithmic
  optimization the generic path does not have. -/
  | halfWordSkipZero
deriving Repr, DecidableEq, BEq

/-- Barrett reciprocal `floor(2^64 / p)` for a modulus below `2^32`. -/
@[inline] def reciprocal (p : UInt64) : UInt64 :=
  if p == 0 then 0 else (0xFFFFFFFFFFFFFFFF : UInt64) / p

/-- Barrett reduction of a word known to be below `p^2`. Mirrors
`HexArith.barrettReduce`, whose `toNat_barrettReduce_eq_mod` proves it is the
ordinary remainder on this range. -/
@[inline] def barrett (p pinv t : UInt64) : UInt64 :=
  let q := UInt64.mulHi t pinv
  let r := t - q * p
  if r ≥ p then r - p else r

/-- Modular sum of two residues below `p < 2^31`, without division. -/
@[inline] def addMod32 (p a b : UInt32) : UInt32 :=
  let s := a + b
  if s ≥ p then s - p else s

/-- Modular sum of two residues below `p < 2^31`, without division. -/
@[inline] def addMod64 (p a b : UInt64) : UInt64 :=
  let s := a + b
  if s ≥ p then s - p else s

/-- Modular negation of a residue below `p`. -/
@[inline] def negMod32 (p a : UInt32) : UInt32 :=
  if a == 0 then 0 else p - a

/-- Modular negation of a residue below `p`. -/
@[inline] def negMod64 (p a : UInt64) : UInt64 :=
  if a == 0 then 0 else p - a

/-- Extended Euclid on machine words, carrying the first cofactor modulo `p`.
Runs once per pivot column, so its cost is `O(n log p)` across a reduction and
never appears in the inner loop. -/
private def invModAux (p : UInt64) : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, s, _ => s
  | fuel + 1, r0, r1, s0, s1 =>
      if r1 == 0 then s0
      else
        let q := r0 / r1
        invModAux p fuel r1 (r0 - q * r1) s1 (addMod64 p s0 (negMod64 p (barrett p (reciprocal p) ((q % p) * s1))))

/-- Modular inverse of a nonzero residue `a` below the prime `p`. -/
def invMod (p a : UInt64) : UInt64 :=
  if a == 0 then 0 else invModAux p 128 p a 0 1

/-- Attribution of one packed reduction, in the same stages as the generic
mirror. -/
structure PackedCounters where
  /-- Nanoseconds packing the generic matrix into the contiguous buffer. -/
  packNanos : Nat := 0
  /-- Nanoseconds in the packed Gauss-Jordan reduction. -/
  reduceNanos : Nat := 0
  /-- Nanoseconds building the nullspace basis and unpacking it. -/
  nullspaceNanos : Nat := 0
  /-- Small allocations across the whole packed reduction. -/
  allocs : Nat := 0
  /-- Row additions performed. -/
  rowAdds : Nat := 0
  /-- Rank found. -/
  rank : Nat := 0

/-- Packed Gauss-Jordan over `UInt32` storage, returning the echelon buffer and
the pivot columns.

Row additions are full width, matching the generic `Hex.Matrix.rowAdd`, which
evaluates `x + c * rsrc[k]` at every entry. `skipZero` additionally skips the
multiply and the store where the source entry is already zero -- an algorithmic
optimization the generic path does not have, priced separately so it is not
counted as a gain from the representation. Both variants skip a whole row
addition when its coefficient is zero, which the generic path also does. -/
private def reduce32 (useBarrett skipZero : Bool) (p : UInt32) (n m : Nat)
    (buf : Array UInt32) : Array UInt32 × Array Nat × Nat :=
  Id.run do
    let p64 := p.toUInt64
    let pinv := reciprocal p64
    let mut a := buf
    let mut row := 0
    let mut pivotCols : Array Nat := #[]
    let mut adds := 0
    for col in [0:m] do
      if row ≥ n then
        break
      -- pivot search
      let mut pivot := n
      for i in [row:n] do
        if a[i * m + col]! != 0 then
          pivot := i
          break
      if pivot == n then
        continue
      -- swap rows `row` and `pivot`
      if pivot != row then
        for k in [0:m] do
          let x := a[row * m + k]!
          a := a.set! (row * m + k) a[pivot * m + k]!
          a := a.set! (pivot * m + k) x
      -- scale the pivot row to a leading one
      let pv := a[row * m + col]!
      let inv := invMod p64 pv.toUInt64
      let inv32 := inv.toUInt32
      if inv32 != 1 then
        for k in [0:m] do
          let x := a[row * m + k]!
          let prod :=
            if useBarrett then barrett p64 pinv (x.toUInt64 * inv)
            else (x.toUInt64 * inv) % p64
          a := a.set! (row * m + k) prod.toUInt32
      -- eliminate the column
      for j in [0:n] do
        if j != row then
          let c := a[j * m + col]!
          if c != 0 then
            adds := adds + 1
            let neg := negMod32 p c
            let neg64 := neg.toUInt64
            for k in [0:m] do
              let s := a[row * m + k]!
              if !skipZero || s != 0 then
                let prod :=
                  if useBarrett then barrett p64 pinv (s.toUInt64 * neg64)
                  else (s.toUInt64 * neg64) % p64
                a := a.set! (j * m + k)
                  (addMod32 p a[j * m + k]! prod.toUInt32)
      pivotCols := pivotCols.push col
      row := row + 1
    return (a, pivotCols, adds)

/-- Packed Gauss-Jordan over `UInt64` storage. Identical arithmetic to
`reduce32`; only the element width differs, which is what separates the boxing
cost from the arithmetic cost. -/
private def reduce64 (p : UInt64) (n m : Nat) (buf : Array UInt64) :
    Array UInt64 × Array Nat × Nat :=
  Id.run do
    let pinv := reciprocal p
    let mut a := buf
    let mut row := 0
    let mut pivotCols : Array Nat := #[]
    let mut adds := 0
    for col in [0:m] do
      if row ≥ n then
        break
      let mut pivot := n
      for i in [row:n] do
        if a[i * m + col]! != 0 then
          pivot := i
          break
      if pivot == n then
        continue
      if pivot != row then
        for k in [0:m] do
          let x := a[row * m + k]!
          a := a.set! (row * m + k) a[pivot * m + k]!
          a := a.set! (pivot * m + k) x
      let pv := a[row * m + col]!
      let inv := invMod p pv
      if inv != 1 then
        for k in [0:m] do
          let x := a[row * m + k]!
          a := a.set! (row * m + k) (barrett p pinv (x * inv))
      for j in [0:n] do
        if j != row then
          let c := a[j * m + col]!
          if c != 0 then
            adds := adds + 1
            let neg := negMod64 p c
            for k in [0:m] do
              let s := a[row * m + k]!
              a := a.set! (j * m + k)
                (addMod64 p a[j * m + k]! (barrett p pinv (s * neg)))
      pivotCols := pivotCols.push col
      row := row + 1
    return (a, pivotCols, adds)

/-! ## Packed drivers and validation -/

/-- Read the generic matrix into one contiguous row-major `UInt32` buffer. -/
private def pack32 {p : Nat} [ZMod64.Bounds p] {n m : Nat}
    (M : Matrix (ZMod64 p) n m) : Array UInt32 :=
  Id.run do
    let mut a : Array UInt32 := Array.emptyWithCapacity (n * m)
    for i in [0:n] do
      if h : i < n then
        for j in [0:m] do
          if hj : j < m then
            a := a.push M[((⟨i, h⟩ : Fin n), (⟨j, hj⟩ : Fin m))].val.toUInt32
    return a

/-- Read the generic matrix into one contiguous row-major `UInt64` buffer. -/
private def pack64 {p : Nat} [ZMod64.Bounds p] {n m : Nat}
    (M : Matrix (ZMod64 p) n m) : Array UInt64 :=
  Id.run do
    let mut a : Array UInt64 := Array.emptyWithCapacity (n * m)
    for i in [0:n] do
      if h : i < n then
        for j in [0:m] do
          if hj : j < m then
            a := a.push M[((⟨i, h⟩ : Fin n), (⟨j, hj⟩ : Fin m))].val
    return a

/-- Columns of `[0, m)` that are not pivot columns, in increasing order. -/
private def freeColumns (m : Nat) (pivotCols : Array Nat) : Array Nat :=
  Id.run do
    let mut free : Array Nat := #[]
    for j in [0:m] do
      if !pivotCols.contains j then
        free := free.push j
    return free

/-- Nullspace basis read off a reduced buffer, as one row-major
`(free count) x m` array of `Nat` residues. Column `k` of the basis has a `1`
in its own free column, the negated pivot-row entry in each pivot column, and
`0` elsewhere -- the same rule as `Hex.Matrix.IsRowReduced.nullspaceMatrix`. -/
private def basisOfBuffer32 (p : UInt32) (m : Nat) (buf : Array UInt32)
    (pivotCols : Array Nat) : Array (Array Nat) :=
  Id.run do
    let free := freeColumns m pivotCols
    let mut out : Array (Array Nat) := #[]
    for k in [0:free.size] do
      let fc := free[k]!
      let mut v : Array Nat := Array.replicate m 0
      v := v.set! fc 1
      for i in [0:pivotCols.size] do
        v := v.set! pivotCols[i]!
          (negMod32 p buf[i * m + fc]!).toNat
      out := out.push v
    return out

/-- Nullspace basis read off a reduced `UInt64` buffer. -/
private def basisOfBuffer64 (p : UInt64) (m : Nat) (buf : Array UInt64)
    (pivotCols : Array Nat) : Array (Array Nat) :=
  Id.run do
    let free := freeColumns m pivotCols
    let mut out : Array (Array Nat) := #[]
    for k in [0:free.size] do
      let fc := free[k]!
      let mut v : Array Nat := Array.replicate m 0
      v := v.set! fc 1
      for i in [0:pivotCols.size] do
        v := v.set! pivotCols[i]! (negMod64 p buf[i * m + fc]!).toNat
      out := out.push v
    return out

/-- Force a value into an `IO.Ref` so the compiler cannot sink its computation
past the next clock read. Pure `let`s whose result is used only later are moved
to their use site by the compiler's let-floating pass, which would silently
attribute a stage's cost to whichever later stage first demands it. -/
def observe (sink : IO.Ref Nat) (value : Nat) : IO Unit :=
  sink.modify (· + value % 2)

/-- One entry of a matrix, as a `Nat`, for forcing it.

`salt` carries a value read from the sink at runtime. Without it the compiler
common-subexpression-eliminates repeated `probeEntry (fixedSpaceMatrix f h)`
calls, and the matrix builds they were meant to force float down into whichever
consumer first demands them; the second and later rebuilds then measure about
130 ns on a 240x240 matrix and their cost is charged to the stage under test. A
runtime-varying operand makes each call a distinct expression. -/
private def probeEntry {p : Nat} [ZMod64.Bounds p] {n m : Nat}
    (salt : Nat) (M : Matrix (ZMod64 p) n m) : Nat :=
  salt % 2 +
    (if h : 0 < n then
      if hm : 0 < m then M[((⟨0, h⟩ : Fin n), (⟨0, hm⟩ : Fin m))].toNat else 0
    else 0)

/-- Build a fixed-space matrix, force it past the compiler's code motion, and
report the build time and allocations. The matrix is returned uniquely
referenced, so the consumer's elementary operations still update the flat buffer
in place. -/
private def freshFixedSpace {p : Nat} [ZMod64.Bounds p]
    (sink : IO.Ref Nat) (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    IO (Matrix (ZMod64 p) (Berlekamp.basisSize f) (Berlekamp.basisSize f)
        × Nat × Nat) := do
  let salt ← sink.get
  let t0 ← mark
  let M := Berlekamp.fixedSpaceMatrix f hmonic
  observe sink (probeEntry salt M)
  let t1 ← mark
  return (M, (t1.since t0).1, (t1.since t0).2)

/-- A nullspace basis as `Nat` residues, for comparing representations. -/
private def basisNats {p : Nat} [ZMod64.Bounds p] {m k : Nat}
    (basis : Vector (Vector (ZMod64 p) m) k) : Array (Array Nat) :=
  basis.toArray.map fun v => v.toArray.map ZMod64.toNat

/-- Timed packed reduction of `M`, checked entry for entry against `expected`,
the production `Hex.Matrix.nullspace` basis of the same matrix.

`M` must be uniquely referenced: `pack32`/`pack64` only read it, but the caller
must not retain it, because a shared matrix would make the generic comparison
run against a copied buffer instead of the in-place one. -/
def packedReduce {p : Nat} [ZMod64.Bounds p] {n m : Nat}
    (sink : IO.Ref Nat) (kind : PackedKind) (M : Matrix (ZMod64 p) n m)
    (expected : Array (Array Nat)) : IO (PackedCounters × Bool) := do
  let pw : UInt64 := UInt64.ofNat p
  let t0 ← mark
  match kind with
  | .word =>
      let buf := pack64 M
      observe sink buf.size
      let t1 ← mark
      let (reduced, pivotCols, adds) := reduce64 pw n m buf
      observe sink (reduced.size + pivotCols.size)
      let t2 ← mark
      let basis := basisOfBuffer64 pw m reduced pivotCols
      observe sink basis.size
      let t3 ← mark
      return ({ packNanos := (t1.since t0).1
                reduceNanos := (t2.since t1).1
                nullspaceNanos := (t3.since t2).1
                allocs := (t3.since t0).2
                rowAdds := adds
                rank := pivotCols.size }, basis == expected)
  | .halfWord | .halfWordDiv | .halfWordSkipZero =>
      let buf := pack32 M
      observe sink buf.size
      let t1 ← mark
      let (reduced, pivotCols, adds) :=
        reduce32 (kind != .halfWordDiv) (kind == .halfWordSkipZero)
          (UInt32.ofNat p) n m buf
      observe sink (reduced.size + pivotCols.size)
      let t2 ← mark
      let basis := basisOfBuffer32 (UInt32.ofNat p) m reduced pivotCols
      observe sink basis.size
      let t3 ← mark
      return ({ packNanos := (t1.since t0).1
                reduceNanos := (t2.since t1).1
                nullspaceNanos := (t3.since t2).1
                allocs := (t3.since t0).2
                rowAdds := adds
                rank := pivotCols.size }, basis == expected)

/-- JSON for one packed variant. -/
def packedJson (label : String) (c : PackedCounters) (ok : Bool) : String × Json :=
  (label, Json.mkObj
    [ ("packNanos", natJson c.packNanos),
      ("reduceNanos", natJson c.reduceNanos),
      ("nullspaceNanos", natJson c.nullspaceNanos),
      ("totalNanos", natJson (c.packNanos + c.reduceNanos + c.nullspaceNanos)),
      ("smallAllocs", natJson c.allocs),
      ("rowAdds", natJson c.rowAdds),
      ("rank", natJson c.rank),
      ("agreesWithNullspace", Json.bool ok) ])

/-! ## The integrated packed kernel

`HexBerlekamp/PackedKernel.lean` is what compiled code runs at the
`fixedSpaceKernelVectors` boundary, selected by a `@[csimp]` equality. The
prototype above is faster than it on the rows where the reduction dominates, on
the same matrix and the same row-addition count, so the gap is scaffolding. The
definitions below attribute it.

All of them are exercised on their own freshly built `Packed.fixedSpace` buffer.
The packed elementary operations update the flat buffer in place only while it
is uniquely referenced, so a buffer shared between two rungs would cost the
second one a full copy per row operation and the ladder would read as noise.
-/

/-- One entry of a packed matrix, as a `Nat`, for forcing it past the compiler's
code motion. `salt` carries a runtime value, for the reason `probeEntry`
documents. -/
private def probePacked {n m : Nat} (salt : Nat) (A : Matrix UInt32 n m) : Nat :=
  salt % 2 +
    (if h : 0 < n then
      if hm : 0 < m then A[((⟨0, h⟩ : Fin n), (⟨0, hm⟩ : Fin m))].toNat else 0
    else 0)

/-! ### Stage attribution of the production loop -/

/-- Running attribution of one counted packed reduction, in the stages
`Hex.Berlekamp.Packed.reduceLoop` has. -/
structure PackedStages where
  /-- Nanoseconds in pivot search. -/
  pivotNanos : Nat := 0
  /-- Small allocations in pivot search. -/
  pivotAllocs : Nat := 0
  /-- Nanoseconds in row swap, row scale, and the `O(n)` column pass that counts
  the eliminations the next stage will perform. -/
  swapScaleNanos : Nat := 0
  /-- Small allocations in row swap, row scale, and the column count. -/
  swapScaleAllocs : Nat := 0
  /-- Nanoseconds in column elimination. -/
  eliminateNanos : Nat := 0
  /-- Small allocations in column elimination. -/
  eliminateAllocs : Nat := 0
  /-- Nanoseconds in the `O(n)` pass that counts the eliminations the next stage
  will perform. Instrument overhead, not a production stage: it is reported on
  its own so it is not charged to any stage the production loop has. -/
  countNanos : Nat := 0
  /-- Small allocations in the counting pass. -/
  countAllocs : Nat := 0
  /-- Row additions actually performed. -/
  rowAdds : Nat := 0
  /-- Eliminations skipped because the entry was already zero. -/
  rowAddsSkipped : Nat := 0
  /-- Pivot columns found. -/
  pivots : Nat := 0
  /-- Columns inspected and found pivot-free. -/
  freeColumns : Nat := 0

/-- Result of a counted packed reduction: the data `Packed.reduce` returns, plus
the attribution. -/
structure PackedStageResult (n m : Nat) where
  /-- The reduced packed buffer. -/
  echelon : Matrix UInt32 n m
  /-- Pivot columns in increasing order. -/
  pivots : List (Fin m)
  /-- Per-stage attribution. -/
  stages : PackedStages

/-- Row additions a packed column elimination will perform, and the ones it will
skip. Counted in a separate `O(n)` pass for the reason `countColumn` gives:
threading counters through the elimination fold would hold a second reference to
the buffer and defeat the in-place update. -/
private def countPackedColumn {n m : Nat} (A : Matrix UInt32 n m) (pivotRow : Fin n)
    (col : Fin m) : Nat × Nat :=
  (List.finRange n).foldl
    (fun (acc : Nat × Nat) j =>
      if j = pivotRow then acc
      else if A[(j, col)] == 0 then (acc.1, acc.2 + 1) else (acc.1 + 1, acc.2))
    (0, 0)

/-- Packed Gauss-Jordan mirroring `Hex.Berlekamp.Packed.reduceLoop`, marking the
clock once per column rather than once per row operation. Every elementary
operation is the production one, so the arithmetic being timed is the production
arithmetic; only the loop scaffolding is duplicated.

The eliminated buffer is pushed into `sink` before the clock is read again. Its
consumer is the tail call, so without that push the compiler's let-floating pass
moves the whole elimination past the mark and the stage reads as free: the first
run of this loop charged 236 columns of elimination 11 us against a 46 ms wall.
The push is one `IO.Ref` update per pivot column, which is the granularity the
rest of the marking already uses.

The `O(n)` counting pass is marked on its own, between the swap-and-scale stage
and the elimination, because production has no such pass and charging it to a
production stage would misreport that stage. It still touches the pivot column's
entries just before the elimination writes those rows, which is a cache-state
confound the marking cannot remove; on the rows where the elimination dominates
it is `n` reads against `n * m` read-modify-writes. -/
private partial def packedStageLoop (p : Nat) [ZMod64.Bounds p] {n m : Nat}
    (sink : IO.Ref Nat) (q : UInt32) (col row : Nat) (echelon : Matrix UInt32 n m)
    (pivots : List (Fin m)) (c : PackedStages) : IO (PackedStageResult n m) := do
  if hRow : row < n then
    if hCol : col < m then
      let colFin : Fin m := ⟨col, hCol⟩
      let t0 ← mark
      let found := Berlekamp.Packed.findPivot? echelon colFin row
      let t1 ← mark
      let (pn, pa) := t1.since t0
      let c := { c with pivotNanos := c.pivotNanos + pn,
                        pivotAllocs := c.pivotAllocs + pa }
      match found with
      | none =>
          packedStageLoop p sink q (col + 1) row echelon pivots
            { c with freeColumns := c.freeColumns + 1 }
      | some pivot =>
          let target : Fin n := ⟨row, hRow⟩
          let swapped := Matrix.rowSwap echelon target pivot
          let pivotVal := swapped[(target, colFin)]
          let scaled :=
            Berlekamp.Packed.rowScale q swapped target (Berlekamp.Packed.invMod p pivotVal)
          observe sink (probePacked col scaled)
          let t2 ← mark
          let (sn, sa) := t2.since t1
          let (adds, skipped) := countPackedColumn scaled target colFin
          let t2b ← mark
          let (cn, ca) := t2b.since t2
          let e := Berlekamp.Packed.eliminateColumn q scaled target colFin
          observe sink (probePacked col e)
          let t3 ← mark
          let (en, ea) := t3.since t2b
          packedStageLoop p sink q (col + 1) (row + 1) e (pivots.concat colFin)
            { c with
                swapScaleNanos := c.swapScaleNanos + sn
                swapScaleAllocs := c.swapScaleAllocs + sa
                countNanos := c.countNanos + cn
                countAllocs := c.countAllocs + ca
                eliminateNanos := c.eliminateNanos + en
                eliminateAllocs := c.eliminateAllocs + ea
                rowAdds := c.rowAdds + adds
                rowAddsSkipped := c.rowAddsSkipped + skipped
                pivots := c.pivots + 1 }
    else
      return { echelon, pivots, stages := c }
  else
    return { echelon, pivots, stages := c }

/-- Counted packed Gauss-Jordan of `A`. Mirrors
`Hex.Berlekamp.Packed.reduce`. -/
def countedPackedReduce (p : Nat) [ZMod64.Bounds p] {n m : Nat} (sink : IO.Ref Nat)
    (q : UInt32) (A : Matrix UInt32 n m) : IO (PackedStageResult n m) :=
  packedStageLoop p sink q 0 0 A [] {}

/-! ### The scaffolding ladder

`ladderLoop` is `Packed.reduceLoop` with its column elimination and its modular
inversion passed in. Both are called once per pivot column, never in the inner
loop, so a rung differs from production only in the elimination it names.
-/

/-- The packed reduction loop with its column elimination as a parameter. -/
private def ladderLoop {n m : Nat}
    (elim : Matrix UInt32 n m → Fin n → Fin m → Matrix UInt32 n m)
    (inv : UInt32 → UInt32) (q : UInt32) (col fuel row : Nat)
    (A : Matrix UInt32 n m) (pivots : List (Fin m)) :
    Matrix UInt32 n m × List (Fin m) :=
  match fuel with
  | 0 => (A, pivots)
  | fuel + 1 =>
      if hRow : row < n then
        if hCol : col < m then
          let colFin : Fin m := ⟨col, hCol⟩
          match Berlekamp.Packed.findPivot? A colFin row with
          | none => ladderLoop elim inv q (col + 1) fuel row A pivots
          | some pivot =>
              let target : Fin n := ⟨row, hRow⟩
              let swapped := Matrix.rowSwap A target pivot
              let pivotVal := swapped[(target, colFin)]
              let scaled := Berlekamp.Packed.rowScale q swapped target (inv pivotVal)
              let eliminated := elim scaled target colFin
              ladderLoop elim inv q (col + 1) fuel (row + 1) eliminated
                (pivots.concat colFin)
        else
          (A, pivots)
      else
        (A, pivots)

/-- `ladderLoop` accumulating the pivot columns in an `Array` with `push`
instead of a `List` with `concat`, which is `O(length)` per pivot. **This
differs from `ladderLoop` in the pivot accumulation and nothing else**; the
`Array` is converted back to a `List` once, after the loop, for the readback. -/
private def ladderLoopArray {n m : Nat}
    (elim : Matrix UInt32 n m → Fin n → Fin m → Matrix UInt32 n m)
    (inv : UInt32 → UInt32) (q : UInt32) (col fuel row : Nat)
    (A : Matrix UInt32 n m) (pivots : Array (Fin m)) :
    Matrix UInt32 n m × Array (Fin m) :=
  match fuel with
  | 0 => (A, pivots)
  | fuel + 1 =>
      if hRow : row < n then
        if hCol : col < m then
          let colFin : Fin m := ⟨col, hCol⟩
          match Berlekamp.Packed.findPivot? A colFin row with
          | none => ladderLoopArray elim inv q (col + 1) fuel row A pivots
          | some pivot =>
              let target : Fin n := ⟨row, hRow⟩
              let swapped := Matrix.rowSwap A target pivot
              let pivotVal := swapped[(target, colFin)]
              let scaled := Berlekamp.Packed.rowScale q swapped target (inv pivotVal)
              let eliminated := elim scaled target colFin
              ladderLoopArray elim inv q (col + 1) fuel (row + 1) eliminated
                (pivots.push colFin)
        else
          (A, pivots)
      else
        (A, pivots)

/-- `Hex.Berlekamp.Packed.rowAdd` with the source row supplied by the caller
rather than read out of the matrix per row addition. -/
@[inline] private def rowAddFrom {n m : Nat} (q : UInt32) (A : Matrix UInt32 n m)
    (rsrc : Vector UInt32 m) (dst : Fin n) (c : UInt32) : Matrix UInt32 n m :=
  A.modifyEntries dst.val fun k x =>
    Berlekamp.Packed.addMod q x (Berlekamp.Packed.mulMod q c rsrc[k])

/-- `Hex.Berlekamp.Packed.eliminateColumn` with the pivot row read once per
column. The pivot row is invariant across the column's elimination, so this is
the same arithmetic with `n - 1` of every `n` row copies removed. -/
private def eliminateHoisted {n m : Nat} (q : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := Matrix.getRow A pivotRow
  (List.finRange n).foldl
    (fun A j =>
      if j = pivotRow then
        A
      else
        let c := Berlekamp.Packed.negMod q A[(j, col)]
        if c == 0 then A else rowAddFrom q A rsrc j c)
    A

/-- Write `row dst + c * rsrc` straight into the flat backing buffer, with no
`Hex.Matrix.modifyEntries` closure. Shared by the rungs below so that they
differ from each other in exactly one place. -/
@[inline] private def rowAddFlat {n m : Nat} (q : UInt32) (d : Vector UInt32 (n * m))
    (rsrc : Array UInt32) (dst : Nat) (c : UInt32) : Vector UInt32 (n * m) :=
  Id.run do
    let mut v := d
    let base := dst * m
    for k in [0:m] do
      v := v.set! (base + k)
        (Berlekamp.Packed.addMod q v.toArray[base + k]!
          (Berlekamp.Packed.mulMod q c rsrc[k]!))
    return v

/-- `eliminateHoisted` writing the destination row straight into the flat
backing buffer instead of through `Hex.Matrix.modifyEntries`, whose `Fin.foldl`
invokes a closure per entry. **The outer scan is still `(List.finRange n).foldl`,
so this differs from `eliminateHoisted` in the row write and nothing else.** The
buffer stays a `Vector` so the length index never has to be re-proved. -/
private def eliminateFlatRow {n m : Nat} (q : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := (Matrix.getRow A pivotRow).toArray
  match A with
  | ⟨d0⟩ =>
      ⟨(List.finRange n).foldl
        (fun d j =>
          if j = pivotRow then
            d
          else
            let c := Berlekamp.Packed.negMod q d.toArray[j.val * m + col.val]!
            if c == 0 then d else rowAddFlat q d rsrc j.val c)
        d0⟩

/-- `eliminateFlatRow` with the outer `(List.finRange n).foldl` replaced by a
`Nat` range. **This differs from `eliminateFlatRow` in the outer column scan and
nothing else**, so the pair prices `List.finRange`'s per-row cons cell and `Fin`
box. -/
private def eliminateFlat {n m : Nat} (q : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := (Matrix.getRow A pivotRow).toArray
  match A with
  | ⟨d0⟩ => Id.run do
      let mut d := d0
      for j in [0:n] do
        if j != pivotRow.val then
          let c := Berlekamp.Packed.negMod q (d.toArray[j * m + col.val]!)
          if c != 0 then
            d := rowAddFlat q d rsrc j c
      return ⟨d⟩

/-! #### Pricing the inner modular multiply

Three bodies, in each of two loop shapes. `salted` performs one multiply on a
salted operand; `saltedMin` performs the same multiply and then a compare and
select on a second salted value; `doubled` performs a second multiply where
`saltedMin` performs an increment, and selects between the two products.

`z` is read from an `IO.Ref` holding zero, so every salted value equals its
unsalted counterpart at runtime and every rung computes the same reduction,
checked entry for entry against `Hex.Matrix.nullspace`. The compiler cannot see
that they agree, so no product is folded away as a common subexpression.

`doubled - saltedMin` is therefore one modular multiply against one `UInt32`
increment, per inner-loop entry. `saltedMin - salted` prices the compare and
select on its own, and `salted - plain` prices the salt. Measuring the same
quantity in both the `modifyEntries` shape and the flat shape is what tests
whether the cost transfers between loop shapes. -/

/-- The salted single multiply, `Hex.Matrix.modifyEntries` shape. -/
@[inline] private def rowAddFromSalted {n m : Nat} (q z : UInt32)
    (A : Matrix UInt32 n m) (rsrc : Vector UInt32 m) (dst : Fin n) (c : UInt32) :
    Matrix UInt32 n m :=
  A.modifyEntries dst.val fun k x =>
    let u := Berlekamp.Packed.mulMod q (c + z) rsrc[k]
    let w := u + z
    Berlekamp.Packed.addMod q x (if u ≤ w then u else w)

/-- The doubled multiply, `Hex.Matrix.modifyEntries` shape. -/
@[inline] private def rowAddFromDoubled {n m : Nat} (q z : UInt32)
    (A : Matrix UInt32 n m) (rsrc : Vector UInt32 m) (dst : Fin n) (c : UInt32) :
    Matrix UInt32 n m :=
  A.modifyEntries dst.val fun k x =>
    let u := Berlekamp.Packed.mulMod q c rsrc[k]
    let v := Berlekamp.Packed.mulMod q (c + z) rsrc[k]
    Berlekamp.Packed.addMod q x (if u ≤ v then u else v)

/-- `eliminateHoisted` with the salted single multiply and the select. -/
private def eliminateHoistedMin {n m : Nat} (q z : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := Matrix.getRow A pivotRow
  (List.finRange n).foldl
    (fun A j =>
      if j = pivotRow then A
      else
        let c := Berlekamp.Packed.negMod q A[(j, col)]
        if c == 0 then A else rowAddFromSalted q z A rsrc j c)
    A

/-- `eliminateHoisted` with the doubled multiply. -/
private def eliminateHoistedDoubled {n m : Nat} (q z : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := Matrix.getRow A pivotRow
  (List.finRange n).foldl
    (fun A j =>
      if j = pivotRow then A
      else
        let c := Berlekamp.Packed.negMod q A[(j, col)]
        if c == 0 then A else rowAddFromDoubled q z A rsrc j c)
    A

/-- `eliminateFlat` with the multiply's operand salted, and no select. Prices
the salt alone against `eliminateFlat`. -/
private def eliminateFlatSalted {n m : Nat} (q z : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := (Matrix.getRow A pivotRow).toArray
  match A with
  | ⟨d0⟩ => Id.run do
      let mut d := d0
      for j in [0:n] do
        if j != pivotRow.val then
          let c := Berlekamp.Packed.negMod q (d.toArray[j * m + col.val]!)
          if c != 0 then
            let base := j * m
            let cz := c + z
            for k in [0:m] do
              d := d.set! (base + k)
                (Berlekamp.Packed.addMod q d.toArray[base + k]!
                  (Berlekamp.Packed.mulMod q cz rsrc[k]!))
      return ⟨d⟩

/-- `eliminateFlatSalted` with the compare and select `eliminateFlatDoubleMul`
performs, on a second salted value rather than a second product. This is the
control the multiply is priced against. -/
private def eliminateFlatSaltedMin {n m : Nat} (q z : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := (Matrix.getRow A pivotRow).toArray
  match A with
  | ⟨d0⟩ => Id.run do
      let mut d := d0
      for j in [0:n] do
        if j != pivotRow.val then
          let c := Berlekamp.Packed.negMod q (d.toArray[j * m + col.val]!)
          if c != 0 then
            let base := j * m
            let cz := c + z
            for k in [0:m] do
              let u := Berlekamp.Packed.mulMod q cz rsrc[k]!
              let w := u + z
              d := d.set! (base + k)
                (Berlekamp.Packed.addMod q d.toArray[base + k]!
                  (if u ≤ w then u else w))
      return ⟨d⟩

/-- `eliminateFlatSaltedMin` with a second modular multiply where the control
has an increment. -/
private def eliminateFlatDoubleMul {n m : Nat} (q z : UInt32) (A : Matrix UInt32 n m)
    (pivotRow : Fin n) (col : Fin m) : Matrix UInt32 n m :=
  let rsrc := (Matrix.getRow A pivotRow).toArray
  match A with
  | ⟨d0⟩ => Id.run do
      let mut d := d0
      for j in [0:n] do
        if j != pivotRow.val then
          let c := Berlekamp.Packed.negMod q (d.toArray[j * m + col.val]!)
          if c != 0 then
            let base := j * m
            let cz := c + z
            for k in [0:m] do
              let s := rsrc[k]!
              let u := Berlekamp.Packed.mulMod q c s
              let v := Berlekamp.Packed.mulMod q cz s
              d := d.set! (base + k)
                (Berlekamp.Packed.addMod q d.toArray[base + k]!
                  (if u ≤ v then u else v))
      return ⟨d⟩

/-! ### Ladder drivers -/

/-- Which direction to run the ladder in on the next call. The driver repeats
each instance, and each repeat flips this, so a systematic order effect cancels
across the repeats instead of biasing one end of the ladder. -/
initialize ladderForward : IO.Ref Bool ← IO.mkRef true

/-- One rung of the ladder: build, reduce, read the basis back. -/
structure LadderRung where
  /-- Nanoseconds building the packed fixed-space buffer. -/
  buildNanos : Nat := 0
  /-- Nanoseconds in the reduction. This is the quantity the ladder compares. -/
  reduceNanos : Nat := 0
  /-- Nanoseconds reading the nullspace basis off the reduced buffer. -/
  readbackNanos : Nat := 0
  /-- Small allocations across build, reduce and readback. -/
  allocs : Nat := 0
  /-- Rank found. -/
  rank : Nat := 0
  /-- Whether the basis agrees with `Hex.Matrix.nullspace` entry for entry. -/
  agrees : Bool := true

/-- JSON for one ladder rung. -/
def rungJson (label : String) (r : LadderRung) : String × Json :=
  (label, Json.mkObj
    [ ("buildNanos", natJson r.buildNanos),
      ("reduceNanos", natJson r.reduceNanos),
      ("readbackNanos", natJson r.readbackNanos),
      ("totalNanos", natJson (r.buildNanos + r.reduceNanos + r.readbackNanos)),
      ("smallAllocs", natJson r.allocs),
      ("rank", natJson r.rank),
      ("agreesWithNullspace", Json.bool r.agrees) ])

/-- A packed nullspace basis as `Nat` residues, for comparing rungs. -/
private def packedBasisNats {p : Nat} [ZMod64.Bounds p] {m : Nat}
    (basis : Array (Vector (ZMod64 p) m)) : Array (Array Nat) :=
  basis.map fun v => v.toArray.map ZMod64.toNat

/-- Time one ladder rung on its own freshly built packed buffer, and check its
basis against `expected`, the production `Hex.Matrix.nullspace` basis. -/
private def runRung {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (sink : IO.Ref Nat) (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (expected : Array (Array Nat))
    (elim : Matrix UInt32 (Berlekamp.basisSize f) (Berlekamp.basisSize f) →
      Fin (Berlekamp.basisSize f) → Fin (Berlekamp.basisSize f) →
      Matrix UInt32 (Berlekamp.basisSize f) (Berlekamp.basisSize f)) :
    IO LadderRung := do
  let n := Berlekamp.basisSize f
  let q := Berlekamp.Packed.modWord p
  let salt ← sink.get
  let t0 ← mark
  let A := Berlekamp.Packed.fixedSpace p f hmonic
  observe sink (probePacked salt A)
  let t1 ← mark
  let (echelon, pivots) :=
    ladderLoop elim (Berlekamp.Packed.invMod p) q 0 n 0 A []
  observe sink (probePacked salt echelon + pivots.length)
  let t2 ← mark
  let basis := packedBasisNats (Berlekamp.Packed.nullspaceArray (p := p) q echelon pivots)
  observe sink basis.size
  let t3 ← mark
  return { buildNanos := (t1.since t0).1
           reduceNanos := (t2.since t1).1
           readbackNanos := (t3.since t2).1
           allocs := (t3.since t0).2
           rank := pivots.length
           agrees := basis == expected }

/-- `runRung` with the pivot columns accumulated in an `Array`. Prices the
`List (Fin m)` pivot accumulation the integration report named. -/
private def runArrayPivotRung {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (sink : IO.Ref Nat) (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (expected : Array (Array Nat))
    (elim : Matrix UInt32 (Berlekamp.basisSize f) (Berlekamp.basisSize f) →
      Fin (Berlekamp.basisSize f) → Fin (Berlekamp.basisSize f) →
      Matrix UInt32 (Berlekamp.basisSize f) (Berlekamp.basisSize f)) :
    IO LadderRung := do
  let n := Berlekamp.basisSize f
  let q := Berlekamp.Packed.modWord p
  let salt ← sink.get
  let t0 ← mark
  let A := Berlekamp.Packed.fixedSpace p f hmonic
  observe sink (probePacked salt A)
  let t1 ← mark
  let (echelon, pivots) :=
    ladderLoopArray elim (Berlekamp.Packed.invMod p) q 0 n 0 A #[]
  observe sink (probePacked salt echelon + pivots.size)
  let t2 ← mark
  let basis :=
    packedBasisNats (Berlekamp.Packed.nullspaceArray (p := p) q echelon pivots.toList)
  observe sink basis.size
  let t3 ← mark
  return { buildNanos := (t1.since t0).1
           reduceNanos := (t2.since t1).1
           readbackNanos := (t3.since t2).1
           allocs := (t3.since t0).2
           rank := pivots.size
           agrees := basis == expected }

/-- The production packed reduction, timed on the same three stages as a ladder
rung. This is the rung the ladder measures against: no mirror, no parameter,
`Hex.Berlekamp.Packed.reduce` itself. -/
private def runIntegrated {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (sink : IO.Ref Nat) (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (expected : Array (Array Nat)) : IO LadderRung := do
  let q := Berlekamp.Packed.modWord p
  let salt ← sink.get
  let t0 ← mark
  let A := Berlekamp.Packed.fixedSpace p f hmonic
  observe sink (probePacked salt A)
  let t1 ← mark
  let s := Berlekamp.Packed.reduce p q A
  observe sink (probePacked salt s.echelon + s.pivots.length)
  let t2 ← mark
  let basis := packedBasisNats (Berlekamp.Packed.nullspaceArray (p := p) q s.echelon s.pivots)
  observe sink basis.size
  let t3 ← mark
  return { buildNanos := (t1.since t0).1
           reduceNanos := (t2.since t1).1
           readbackNanos := (t3.since t2).1
           allocs := (t3.since t0).2
           rank := s.pivots.length
           agrees := basis == expected }

/-- The prototype loop `reduce32` run on the packed fixed-space buffer, with the
hardware remainder the production path also uses. This is the bottom rung: on
top of the flat row write it drops the `List.finRange` elimination fold and the
`List.concat` pivot accumulation, and it never copies the pivot row at all.

The buffer is taken straight off the packed matrix rather than repacked, so the
rung shares the build with every other rung and its `reduceNanos` is comparable
to theirs. -/
private def runPrototypeRung {p : Nat} [ZMod64.Bounds p]
    (sink : IO.Ref Nat) (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (expected : Array (Array Nat)) : IO LadderRung := do
  let n := Berlekamp.basisSize f
  let pw := UInt32.ofNat p
  let salt ← sink.get
  let t0 ← mark
  let A := Berlekamp.Packed.fixedSpace p f hmonic
  observe sink (probePacked salt A)
  let t1 ← mark
  let (reduced, pivotCols, _) := reduce32 false false pw n n A.data.toArray
  observe sink (reduced.size + pivotCols.size)
  let t2 ← mark
  let basis := basisOfBuffer32 pw n reduced pivotCols
  observe sink basis.size
  let t3 ← mark
  return { buildNanos := (t1.since t0).1
           reduceNanos := (t2.since t1).1
           readbackNanos := (t3.since t2).1
           allocs := (t3.since t0).2
           rank := pivotCols.size
           agrees := basis == expected }

/-! ## Full fixed-space kernel attribution -/

/-- JSON for one counted Gauss-Jordan run. -/
private def counterJson (c : ReduceCounters) (wallNanos wallAllocs : Nat) : Json :=
  Json.mkObj
    [ ("pivotSearch", spanJson c.pivotNanos c.pivotAllocs),
      ("rowSwapScale", spanJson c.swapScaleNanos c.swapScaleAllocs),
      ("rowAdd", spanJson c.rowAddNanos c.rowAddAllocs),
      ("rowAdds", natJson c.rowAdds),
      ("rowAddsSkipped", natJson c.rowAddsSkipped),
      ("pivots", natJson c.pivots),
      ("freeColumns", natJson c.freeColumns),
      ("stagedNanos",
        natJson (c.pivotNanos + c.swapScaleNanos + c.rowAddNanos)),
      ("wall", spanJson wallNanos wallAllocs) ]

/-- Stage-by-stage attribution of one Berlekamp fixed-space kernel computation
on the monic modular image `f`, together with the packed pricing.

Two measurement hazards shape the structure below, and both are handled rather
than hoped away.

*Let-floating.* Every stage's result is pushed into `sink` before the next clock
read. Without that the compiler moves a pure `let` down to its first use, and a
stage's cost lands in whichever later stage first demands its value.

*Aliasing.* `Hex.Matrix`'s elementary operations update the flat backing buffer
in place only while the matrix is uniquely referenced, so a single shared
`fixedSpaceMatrix` handed to several variants would make every variant but the
last copy the whole matrix per row operation. Each timed consumer therefore gets
its own freshly built matrix, and the build is timed separately so the extra
builds can be subtracted. -/
def kernelPhases {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f) : IO Json := do
  let sink ← IO.mkRef 0
  let n := Berlekamp.basisSize f
  let rss0 ← residentBytes false
  -- 1. Berlekamp matrix column construction.
  let t0 ← mark
  let frobX := FpPoly.frobeniusXMod f hmonic
  observe sink frobX.size
  let t1 ← mark
  let polys := Berlekamp.berlekampColumnPolys f hmonic frobX n 1 #[]
  observe sink polys.size
  let t2 ← mark
  -- 2. Conversion to the generic matrix representation, then the diagonal
  -- decrement that turns `Q_f` into `Q_f - I`.
  let salt2 ← sink.get
  let Q := Berlekamp.berlekampMatrix f hmonic
  observe sink (probeEntry salt2 Q)
  let t3 ← mark
  let (fixedA, buildA, buildAllocs) ← freshFixedSpace sink f hmonic
  let t4 ← mark
  -- 3-4. Pivot search, row swap and scale, row addition. `fixedA` is consumed
  -- here and never read again, so the elementary operations update in place.
  let withT ← countedRowReduce true fixedA
  observe sink withT.pivots.length
  let t5 ← mark
  let (fixedB, buildB, _) ← freshFixedSpace sink f hmonic
  let t6 ← mark
  let withoutT ← countedRowReduce false fixedB
  observe sink withoutT.pivots.length
  let t7 ← mark
  -- 5. Rank and nullspace-basis construction, through the production path.
  -- `rowReduce` is timed on its own so the mirror above can be checked against
  -- it for speed as well as for result, and so the basis construction is the
  -- difference between the two rather than an unattributed remainder.
  let (fixedR, buildR, _) ← freshFixedSpace sink f hmonic
  let t7a ← mark
  let salt3 ← sink.get
  let reduced := Matrix.rowReduce fixedR
  observe sink (reduced.rank + probeEntry salt3 reduced.echelon)
  let t7b ← mark
  let (fixedC, buildC, _) ← freshFixedSpace sink f hmonic
  let t8 ← mark
  -- Read the basis out as a plain `Array` first. Every `Vector` operation takes
  -- the length index as a runtime argument, and here that index is
  -- `m - Matrix.rowReduce_rank fixedC`, so demanding it runs a second row
  -- reduction; going through `toArray` keeps the conversion stage measuring the
  -- conversion.
  let basisArray := (Matrix.nullspace fixedC).toArray
  observe sink (basisArray.foldl (fun acc v => acc + v.toArray.size) 0)
  let t9 ← mark
  -- 6. Conversion of basis vectors back to polynomials.
  let polysOut := basisArray.map Berlekamp.vectorToPoly
  observe sink (polysOut.foldl (fun acc g => acc + g.size) 0)
  let t10 ← mark
  -- The two production entry points this attribution is about, timed whole:
  -- the fixed-space kernel boundary a specialization would replace, and the
  -- Berlekamp split that contains it.
  let kernelVectors := Berlekamp.fixedSpaceKernelVectors f hmonic
  observe sink kernelVectors.toArray.size
  let t11 ← mark
  let split := (Berlekamp.berlekampFactor f hmonic).factors
  observe sink split.length
  let t12 ← mark
  let rss1 ← residentBytes false
  let expected := basisArray.map fun v => v.toArray.map ZMod64.toNat
  -- Packed pricing, each against its own fresh matrix.
  let (fixedW, _, _) ← freshFixedSpace sink f hmonic
  let (pWord, okWord) ← packedReduce sink .word fixedW expected
  let (fixedH, _, _) ← freshFixedSpace sink f hmonic
  let (pHalf, okHalf) ← packedReduce sink .halfWord fixedH expected
  let (fixedD, _, _) ← freshFixedSpace sink f hmonic
  let (pHalfDiv, okHalfDiv) ← packedReduce sink .halfWordDiv fixedD expected
  let (fixedS, _, _) ← freshFixedSpace sink f hmonic
  let (pSkip, okSkip) ← packedReduce sink .halfWordSkipZero fixedS expected
  -- Attribution of the integrated packed kernel (issue #9160). The stage split
  -- first, on its own buffer, then the scaffolding ladder, each rung on its own
  -- buffer: the packed operations update in place only while the buffer is
  -- uniquely referenced.
  let q := Berlekamp.Packed.modWord p
  let saltP ← sink.get
  let tk0 ← mark
  let packedA := Berlekamp.Packed.fixedSpace p f hmonic
  observe sink (probePacked saltP packedA)
  let tk1 ← mark
  let staged ← countedPackedReduce p sink q packedA
  observe sink (probePacked saltP staged.echelon + staged.pivots.length)
  let tk2 ← mark
  let stagedBasis :=
    packedBasisNats (Berlekamp.Packed.nullspaceArray (p := p) q staged.echelon staged.pivots)
  observe sink stagedBasis.size
  let tk3 ← mark
  -- The stage mirror against the production packed reduction, on its own
  -- buffer, so a divergent mirror cannot report attribution for a loop
  -- production does not run.
  let checkA := Berlekamp.Packed.fixedSpace p f hmonic
  let checked := Berlekamp.Packed.reduce p q checkA
  let packedMirrorOk :=
    checked.echelon == staged.echelon && checked.pivots == staged.pivots
  let zeroRef ← IO.mkRef (0 : UInt32)
  let z ← zeroRef.get
  -- The rungs are run in one order on one call and the reverse on the next, so
  -- that a systematic order effect (allocator or cache state accumulated by the
  -- earlier rungs) cancels across the driver's repeats rather than biasing one
  -- end of the ladder.
  let forward ← ladderForward.get
  ladderForward.set (!forward)
  let rungs : Array (String × IO LadderRung) :=
    #[ ("integrated", runIntegrated sink f hmonic expected),
       ("mirrored", runRung sink f hmonic expected (Berlekamp.Packed.eliminateColumn q)),
       ("hoistedPivotRow", runRung sink f hmonic expected (eliminateHoisted q)),
       ("arrayPivots", runArrayPivotRung sink f hmonic expected (eliminateHoisted q)),
       ("hoistedSaltedMin", runRung sink f hmonic expected (eliminateHoistedMin q z)),
       ("hoistedDoubledMultiply",
         runRung sink f hmonic expected (eliminateHoistedDoubled q z)),
       ("flatRowWrite", runRung sink f hmonic expected (eliminateFlatRow q)),
       ("flatBothLoops", runRung sink f hmonic expected (eliminateFlat q)),
       ("saltedMultiply", runRung sink f hmonic expected (eliminateFlatSalted q z)),
       ("saltedMinMultiply", runRung sink f hmonic expected (eliminateFlatSaltedMin q z)),
       ("doubledMultiply", runRung sink f hmonic expected (eliminateFlatDoubleMul q z)),
       ("flatBuffer", runPrototypeRung sink f hmonic expected) ]
  let ordered := if forward then rungs else rungs.reverse
  let mut ladder : Array (String × LadderRung) := #[]
  for (label, act) in ordered do
    let r ← act
    ladder := ladder.push (label, r)
  let rungOf (label : String) : LadderRung :=
    ((ladder.find? fun pair => pair.1 == label).map Prod.snd).getD {}
  let peak ← residentBytes true
  -- Validation: the counted mirror against the production row reduction, and
  -- the transform-free run against the mirror that keeps the transform.
  let (fixedV, _, _) ← freshFixedSpace sink f hmonic
  let mirrorOk := mirrorAgrees fixedV withT
  let echelonOk := withT.echelon == withoutT.echelon
    && withT.pivots == withoutT.pivots
  let sunk ← sink.get
  return Json.mkObj
    [ ("basisSize", natJson n),
      ("modulus", natJson p),
      ("rank", natJson withT.pivots.length),
      ("kernelDimension", natJson basisArray.size),
      ("sink", natJson sunk),
      ("frobeniusPower", spanJson (t1.since t0).1 (t1.since t0).2),
      ("columnPolys", spanJson (t2.since t1).1 (t2.since t1).2),
      ("berlekampMatrixWall", spanJson (t3.since t2).1 (t3.since t2).2),
      ("fixedSpaceMatrixWall", spanJson buildA buildAllocs),
      -- Nested spans, so these are differences; `Nat` subtraction clamps, and
      -- the sign flag records when the difference was negative rather than
      -- letting a clamp read as a zero-cost stage.
      ("matrixConversionNanos", natJson ((t3.since t2).1 - (t2.since t0).1)),
      ("matrixConversionNegative",
        Json.bool ((t3.since t2).1 < (t2.since t0).1)),
      ("fixedSpaceDiagonalNanos", natJson ((t4.since t3).1 - (t3.since t2).1)),
      ("fixedSpaceDiagonalNegative",
        Json.bool ((t4.since t3).1 < (t3.since t2).1)),
      ("matrixRebuild", spanJson buildB 0),
      ("productionRowReduce", spanJson (t7b.since t7a).1 (t7b.since t7a).2),
      -- The nullspace-basis construction, as the difference between two
      -- adjacent stages of *this* execution rather than between medians of
      -- two ~300 ms stages, which would not resolve a millisecond.
      ("nullspaceBasisNanos",
        natJson ((t9.since t8).1 - (t7b.since t7a).1)),
      ("nullspaceBasisNegative",
        Json.bool ((t9.since t8).1 < (t7b.since t7a).1)),
      ("nullspaceBasisMagnitudeNanos",
        natJson (max ((t9.since t8).1 - (t7b.since t7a).1)
                     ((t7b.since t7a).1 - (t9.since t8).1))),
      ("countedWithTransform",
        counterJson withT.counters (t5.since t4).1 (t5.since t4).2),
      ("countedEchelonOnly",
        counterJson withoutT.counters (t7.since t6).1 (t7.since t6).2),
      ("productionMatrixRebuild", spanJson buildC 0),
      ("rowReduceMatrixRebuild", spanJson buildR 0),
      ("productionNullspace", spanJson (t9.since t8).1 (t9.since t8).2),
      ("basisToPolynomials", spanJson (t10.since t9).1 (t10.since t9).2),
      ("fixedSpaceKernelVectors", spanJson (t11.since t10).1 (t11.since t10).2),
      ("berlekampSplit", spanJson (t12.since t11).1 (t12.since t11).2),
      ("splitFactors", natJson split.length),
      ("residentBytesBefore", natJson rss0),
      ("residentBytesAfter", natJson rss1),
      ("peakResidentBytes", natJson peak),
      ("mirrorAgreesWithRowReduce", Json.bool mirrorOk),
      ("echelonOnlyAgrees", Json.bool echelonOk),
      packedJson "packedWord" pWord okWord,
      packedJson "packedHalfWord" pHalf okHalf,
      packedJson "packedHalfWordDivision" pHalfDiv okHalfDiv,
      packedJson "packedHalfWordSkipZero" pSkip okSkip,
      ("packedStages", Json.mkObj
        [ ("build", spanJson (tk1.since tk0).1 (tk1.since tk0).2),
          ("pivotSearch",
            spanJson staged.stages.pivotNanos staged.stages.pivotAllocs),
          ("rowSwapScale",
            spanJson staged.stages.swapScaleNanos staged.stages.swapScaleAllocs),
          ("eliminate",
            spanJson staged.stages.eliminateNanos staged.stages.eliminateAllocs),
          ("columnCount",
            spanJson staged.stages.countNanos staged.stages.countAllocs),
          ("readback", spanJson (tk3.since tk2).1 (tk3.since tk2).2),
          ("stagedNanos",
            natJson (staged.stages.pivotNanos + staged.stages.swapScaleNanos
              + staged.stages.eliminateNanos)),
          ("wall", spanJson (tk2.since tk1).1 (tk2.since tk1).2),
          ("rowAdds", natJson staged.stages.rowAdds),
          ("rowAddsSkipped", natJson staged.stages.rowAddsSkipped),
          ("pivots", natJson staged.stages.pivots),
          ("freeColumns", natJson staged.stages.freeColumns),
          ("innerMultiplies", natJson (staged.stages.rowAdds * n)),
          ("scaleMultiplies", natJson (staged.stages.pivots * n)),
          ("agreesWithPackedReduce", Json.bool packedMirrorOk),
          ("agreesWithNullspace", Json.bool (stagedBasis == expected)) ]),
      ("packedLadder", Json.mkObj
        (("ladderForward", Json.bool forward)
          :: (ladder.toList.map fun pair => rungJson pair.1 (rungOf pair.1)))) ]

end HexBench.BerlekampKernel
