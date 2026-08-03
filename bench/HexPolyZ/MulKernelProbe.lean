/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyZ

/-!
Throwaway measurement probe for issue #9142: compare the schoolbook dense
polynomial product against thresholded Karatsuba and against Kronecker
substitution on the shapes the Hensel lift actually issues.

Not part of the shipped library; deleted once the kernel choice is recorded.
-/

open Hex

namespace MulKernelProbe

/-! # Inputs -/

/-- Deterministic xorshift over `UInt64`. -/
def nextRand (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- A pseudorandom nonnegative integer of about `bits` bits. -/
partial def randNat (bits : Nat) (s : UInt64) : Nat × UInt64 :=
  let rec go (acc : Nat) (need : Nat) (s : UInt64) : Nat × UInt64 :=
    if need == 0 then (acc, s)
    else
      let s := nextRand s
      let take := min need 32
      let chunk := (s.toNat) % (2 ^ take)
      go (acc * 2 ^ take + chunk) (need - take) s
  go 0 bits s

/-- `n` pseudorandom coefficients of about `bits` bits each. -/
def randCoeffs (n bits : Nat) (seed : UInt64) : Array Int := Id.run do
  let mut out : Array Int := Array.emptyWithCapacity n
  let mut s := seed
  for _ in [0:n] do
    let (v, s') := randNat bits s
    out := out.push (Int.ofNat (v ||| 1))
    s := s'
  return out

/-! # Karatsuba -/

/-- Schoolbook product of two coefficient slices, returning `alen + blen - 1`
coefficients. -/
def schoolbookArr (a b : Array Int) : Array Int := Id.run do
  if a.size == 0 || b.size == 0 then return #[]
  let mut out := Array.replicate (a.size + b.size - 1) (0 : Int)
  for i in [0:a.size] do
    let ai := a[i]!
    for j in [0:b.size] do
      out := out.modify (i + j) (· + ai * b[j]!)
  return out

/-- Coefficientwise sum, padding the shorter operand with zeros. -/
def addArr (a b : Array Int) : Array Int := Id.run do
  let n := max a.size b.size
  let mut out := Array.emptyWithCapacity n
  for i in [0:n] do
    out := out.push (a.getD i 0 + b.getD i 0)
  return out

/-- In-place `a[off+i] += b[i]`, growing `a` as needed. -/
def addAtArr (a : Array Int) (off : Nat) (b : Array Int) : Array Int := Id.run do
  let mut a := a
  for i in [0:b.size] do
    let k := off + i
    if k < a.size then
      a := a.modify k (· + b[i]!)
    else
      a := a.push b[i]!
  return a

/-- In-place `a[off+i] -= b[i]`. -/
def subAtArr (a : Array Int) (off : Nat) (b : Array Int) : Array Int := Id.run do
  let mut a := a
  for i in [0:b.size] do
    let k := off + i
    if k < a.size then
      a := a.modify k (· - b[i]!)
    else
      a := a.push (-b[i]!)
  return a

/-- Thresholded Karatsuba on coefficient arrays, base case `τ`. -/
partial def karatsubaArr (tau : Nat) (a b : Array Int) : Array Int :=
  if a.size == 0 || b.size == 0 then #[]
  else if a.size ≤ tau || b.size ≤ tau then schoolbookArr a b
  else
    let k := (max a.size b.size + 1) / 2
    let a0 := a.extract 0 (min k a.size)
    let a1 := a.extract (min k a.size) a.size
    let b0 := b.extract 0 (min k b.size)
    let b1 := b.extract (min k b.size) b.size
    let z0 := karatsubaArr tau a0 b0
    let z2 := karatsubaArr tau a1 b1
    let z1 := karatsubaArr tau (addArr a0 a1) (addArr b0 b1)
    let n := a.size + b.size - 1
    let out := Array.replicate n (0 : Int)
    let out := addAtArr out 0 z0
    let out := addAtArr out k z1
    let out := subAtArr out k z0
    let out := subAtArr out k z2
    let out := addAtArr out (2 * k) z2
    out

/-! # Kronecker substitution -/

/-- Bit length of the largest coefficient (assumed nonnegative). -/
def maxBits (a : Array Int) : Nat := Id.run do
  let mut m : Nat := 0
  for x in a do
    let v := x.toNat
    if v > m then m := v
  return if m == 0 then 0 else Nat.log2 m + 1

/-- Smallest `t` with `n ≤ 2 ^ t`. -/
def ceilLog2 (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- Divide-and-conquer packing: `∑ a[lo+i] * 2 ^ (b * i)`. -/
partial def packArr (b : Nat) (a : Array Int) (lo len : Nat) : Nat :=
  if len == 0 then 0
  else if len == 1 then a[lo]!.toNat
  else
    let half := len / 2
    packArr b a lo half + (packArr b a (lo + half) (len - half)) <<< (b * half)

/-- Divide-and-conquer digit extraction in base `2 ^ b`. -/
partial def unpackArr (b : Nat) (n : Nat) (len : Nat) : Array Nat :=
  if len == 0 then #[]
  else if len == 1 then #[n]
  else
    let half := len / 2
    let d := b * half
    let hi := n >>> d
    let lo := n - (hi <<< d)
    unpackArr b lo half ++ unpackArr b hi (len - half)

/-- Kronecker product for nonnegative coefficient arrays. -/
def kroneckerArr (a b : Array Int) : Array Int :=
  if a.size == 0 || b.size == 0 then #[]
  else
    let b0 := max (maxBits a) (maxBits b)
    let slots := a.size + b.size - 1
    let w := 2 * b0 + ceilLog2 (min a.size b.size)
    let pa := packArr w a 0 a.size
    let pb := packArr w b 0 b.size
    let prod := pa * pb
    (unpackArr w prod slots).map Int.ofNat

/-! # Timing -/

/-- Run `f` `reps` times, returning nanoseconds per rep and a checksum. -/
def timeIt (reps : Nat) (f : Unit → Array Int) : IO (Float × Int) := do
  -- warm up
  let _ := f ()
  let t0 ← IO.monoNanosNow
  let mut chk : Int := 0
  for _ in [0:reps] do
    let r := f ()
    chk := chk + r[0]!
  let t1 ← IO.monoNanosNow
  return (Float.ofNat (t1 - t0) / Float.ofNat reps, chk)

def probeShape (name : String) (n bits reps : Nat) : IO Unit := do
  let a := randCoeffs n bits 0x243f6a8885a308d3
  let b := randCoeffs n bits 0x13198a2e03707344
  let pa : ZPoly := DensePoly.ofCoeffs a
  let pb : ZPoly := DensePoly.ofCoeffs b
  let (tSchool, c0) ← timeIt reps (fun _ => (pa * pb).toArray)
  let (tSchoolArr, c1) ← timeIt reps (fun _ => schoolbookArr a b)
  let (tKron, c2) ← timeIt reps (fun _ => kroneckerArr a b)
  let mut best := ""
  let mut bestT := tSchool
  IO.println s!"shape {name}: n={n} bits={bits}"
  IO.println s!"  schoolbook (DensePoly) {tSchool} ns  chk={c0}"
  IO.println s!"  schoolbook (Array)     {tSchoolArr} ns  chk={c1}"
  IO.println s!"  kronecker              {tKron} ns  chk={c2}"
  for tau in [4, 8, 16, 24, 32, 48] do
    let (t, c) ← timeIt reps (fun _ => karatsubaArr tau a b)
    if c != c1 then IO.println s!"  !! karatsuba tau={tau} MISMATCH {c} vs {c1}"
    IO.println s!"  karatsuba tau={tau}      {t} ns"
    if t < bestT then
      bestT := t
      best := s!"karatsuba tau={tau}"
  if c2 != c1 then IO.println s!"  !! kronecker MISMATCH {c2} vs {c1}"
  IO.println s!"  best karatsuba: {best} at {bestT} ns"

def main : IO Unit := do
  -- cyclo_phi179: degree-89 factors, bignum steps at 92 and 181 bits
  probeShape "phi179-step29" 90 92 200
  probeShape "phi179-step57" 90 181 200
  -- cyclo_phi385: degree-60 shape
  probeShape "phi385" 60 120 300
  -- below any plausible crossover
  probeShape "small-8" 8 64 5000
  probeShape "small-16" 16 64 3000
  probeShape "small-32" 32 92 1000
  -- wilkinson_56
  probeShape "wilkinson56" 56 200 300

end MulKernelProbe

def main : IO Unit := MulKernelProbe.main
