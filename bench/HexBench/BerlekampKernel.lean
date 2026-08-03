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

/-- One entry of a matrix, as a `Nat`, for forcing it. -/
private def probeEntry {p : Nat} [ZMod64.Bounds p] {n m : Nat}
    (M : Matrix (ZMod64 p) n m) : Nat :=
  if h : 0 < n then
    if hm : 0 < m then M[((⟨0, h⟩ : Fin n), (⟨0, hm⟩ : Fin m))].toNat else 0
  else 0

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
  let Q := Berlekamp.berlekampMatrix f hmonic
  observe sink (probeEntry Q)
  let t3 ← mark
  let fixedA := Berlekamp.fixedSpaceMatrix f hmonic
  observe sink (probeEntry fixedA)
  let t4 ← mark
  -- 3-4. Pivot search, row swap and scale, row addition. `fixedA` is consumed
  -- here and never read again, so the elementary operations update in place.
  let withT ← countedRowReduce true fixedA
  observe sink withT.pivots.length
  let t5 ← mark
  let fixedB := Berlekamp.fixedSpaceMatrix f hmonic
  observe sink (probeEntry fixedB)
  let t6 ← mark
  let withoutT ← countedRowReduce false fixedB
  observe sink withoutT.pivots.length
  let t7 ← mark
  -- 5. Rank and nullspace-basis construction, through the production path.
  -- `rowReduce` is timed on its own so the mirror above can be checked against
  -- it for speed as well as for result, and so the basis construction is the
  -- difference between the two rather than an unattributed remainder.
  let fixedR := Berlekamp.fixedSpaceMatrix f hmonic
  observe sink (probeEntry fixedR)
  let t7a ← mark
  let reduced := Matrix.rowReduce fixedR
  observe sink (reduced.rank + probeEntry reduced.echelon)
  let t7b ← mark
  let fixedC := Berlekamp.fixedSpaceMatrix f hmonic
  observe sink (probeEntry fixedC)
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
  let fixedW := Berlekamp.fixedSpaceMatrix f hmonic
  let (pWord, okWord) ← packedReduce sink .word fixedW expected
  let fixedH := Berlekamp.fixedSpaceMatrix f hmonic
  let (pHalf, okHalf) ← packedReduce sink .halfWord fixedH expected
  let fixedD := Berlekamp.fixedSpaceMatrix f hmonic
  let (pHalfDiv, okHalfDiv) ← packedReduce sink .halfWordDiv fixedD expected
  let fixedS := Berlekamp.fixedSpaceMatrix f hmonic
  let (pSkip, okSkip) ← packedReduce sink .halfWordSkipZero fixedS expected
  let peak ← residentBytes true
  -- Validation: the counted mirror against the production row reduction, and
  -- the transform-free run against the mirror that keeps the transform.
  let fixedV := Berlekamp.fixedSpaceMatrix f hmonic
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
      ("fixedSpaceMatrixWall", spanJson (t4.since t3).1 (t4.since t3).2),
      -- Nested spans, so these are differences; `Nat` subtraction clamps, and
      -- the sign flag records when the difference was negative rather than
      -- letting a clamp read as a zero-cost stage.
      ("matrixConversionNanos", natJson ((t3.since t2).1 - (t2.since t0).1)),
      ("matrixConversionNegative",
        Json.bool ((t3.since t2).1 < (t2.since t0).1)),
      ("fixedSpaceDiagonalNanos", natJson ((t4.since t3).1 - (t3.since t2).1)),
      ("fixedSpaceDiagonalNegative",
        Json.bool ((t4.since t3).1 < (t3.since t2).1)),
      ("matrixRebuild", spanJson (t6.since t5).1 (t6.since t5).2),
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
      ("productionMatrixRebuild", spanJson (t8.since t7b).1 (t8.since t7b).2),
      ("rowReduceMatrixRebuild", spanJson (t7a.since t7).1 (t7a.since t7).2),
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
      packedJson "packedHalfWordSkipZero" pSkip okSkip ]

end HexBench.BerlekampKernel
