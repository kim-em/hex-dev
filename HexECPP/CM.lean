/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Import

public section

/-!
# Bounded CM arithmetic proposals

Jacobi, Tonelli–Shanks and Cornacchia supply search proposals, including over
composite moduli. Returned roots and norm equations are verified by integer
arithmetic. No primality implication depends on these algorithms or the CM
invariants. The class number one table is the standard singular j-invariant
table (Cox, *Primes of the Form x² + ny²*, Chapter 12).
-/

namespace Hex.ECPP.CM

/-- Binary Jacobi algorithm; fuel bounds every halving and reciprocity step. -/
def jacobi : Nat → Nat → Nat → Int → Int
  | 0, _, _, _ => 0
  | fuel + 1, a, n, sign =>
      if n == 0 || n % 2 == 0 then 0
      else if a == 0 then if n == 1 then sign else 0
      else if a % 2 == 0 then
        jacobi fuel (a / 2) n (if n % 8 == 3 || n % 8 == 5 then -sign else sign)
      else jacobi fuel (n % a) a (if a % 4 == 3 && n % 4 == 3 then -sign else sign)

/-- Fuel is linear in input bits; exhaustion conservatively returns zero. -/
def symbol (a n : Nat) : Int := jacobi (4 * HexArith.bitLength n + 4) (a % n) n 1

/-- Check a canonical root proposal before using it. -/
def rootValid (n a r : Nat) : Bool := 1 < n && r < n && r * r % n == a % n

private def tonelli (n : Nat) : Nat → Nat → Nat → Nat → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel + 1, m, c, t, x =>
      if t == 1 then some x
      else Id.run do
        let mut v := t
        let mut index := 0
        for i in [:m] do
          if v == 1 then
            index := i
            break
          v := v * v % n
          index := i + 1
        if index == 0 || index >= m then return none
        let b := HexArith.powMod c (2 ^ (m - index - 1)) n
        let b2 := b * b % n
        return tonelli n fuel index b2 (t * b2 % n) (x * b % n)

/-- Bounded Tonelli–Shanks with a caller-supplied nonresidue. Even for a
composite modulus, success requires the actual root equation. -/
def sqrt? (n z a : Nat) : Option Nat := do
  if n ≤ 2 || n % 2 == 0 then none else do
    let a := a % n
    if a == 0 then return 0
    if symbol a n != 1 then none else do
      let r ← if n % 4 == 3 then
        some (HexArith.powMod a ((n + 1) / 4) n)
      else do
        if HexArith.powMod z ((n - 1) / 2) n != n - 1 then none else do
          let (s, d) := Hex.Nat.oddSplit (n - 1)
          tonelli n (s + 1) s (HexArith.powMod z d n)
            (HexArith.powMod a d n) (HexArith.powMod a ((d + 1) / 2) n)
      if rootValid n a r then some r else none

structure Invariant where
  /-- Absolute value of the negative discriminant. -/
  d : Nat
  j : Int
deriving Repr

/-- A fixed portfolio; no subject-specific trace or factorization is stored. -/
def portfolio : List Invariant :=
  [⟨3, 0⟩, ⟨4, 1728⟩, ⟨7, -3375⟩, ⟨8, 8000⟩, ⟨11, -32768⟩,
   ⟨19, -884736⟩, ⟨43, -884736000⟩, ⟨67, -147197952000⟩,
   ⟨163, -262537412640768000⟩]

/-- Check the exact Cornacchia norm equation, independently of the search. -/
def normValid (n d t v : Nat) : Bool := t * t + d * v * v == 4 * n

private def cornacchia (m d : Nat) : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel + 1, a, b =>
      if b * b ≤ m then
        let rest := m - b * b
        if d == 0 || rest % d != 0 then none else
          let v := Nat.sqrt (rest / d)
          if b * b + d * v * v == m then some (b, v) else none
      else if b == 0 then none
      else cornacchia m d fuel b (a % b)

/-- Solve `t² + d*v² = 4*n` from a checked modular root. For odd
discriminants lift the root to an odd root modulo `4*n`; even discriminants
use the equivalent norm equation modulo `n`. -/
def norm? (n d root : Nat) : Option (Nat × Nat) := do
  if n ≤ 2 || d == 0 then none else do
    let (m, k, r) := if d % 4 == 0 then (n, d / 4, root)
      else (4 * n, d, if root % 2 == 1 then root else root + n)
    if !rootValid m (modSub m 0 (k % m)) r then none else do
      let (x, v) ← cornacchia m k (4 * HexArith.bitLength m + 4) m r
      let t := if d % 4 == 0 then 2 * x else x
      if normValid n d t v then some (t, v) else none

/-- Candidate traces, including all extra associates for j=0 and j=1728. -/
def traces (d t v : Nat) : List Int :=
  let t : Int := t
  let v : Int := v
  let positive := if d == 3 then [t, (t + 3 * v) / 2, (t - 3 * v) / 2]
    else if d == 4 then [t, 2 * v] else [t]
  positive.flatMap fun a => [a, -a]

/-- All exceptional twist classes use powers of a sextic/quartic nonresidue.
Ordinary invariants use the curve and its quadratic twist. -/
def curves (n : Nat) (inv : Invariant) (g : Nat) : List (Nat × Nat) :=
  if inv.d == 3 then
    (List.range 6).map fun i => (0, HexArith.powMod g i n)
  else if inv.d == 4 then
    (List.range 4).map fun i => (HexArith.powMod g i n, 0)
  else
    let j := residue n inv.j
    match inverse? n (modSub n 1728 j) with
    | none => []
    | some u =>
        let k := j * u % n
        let a := 3 * k % n
        let b := 2 * k % n
        [(a, b), (a * g * g % n, b * g * g * g % n)]

end Hex.ECPP.CM
