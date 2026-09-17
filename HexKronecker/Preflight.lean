/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexKronecker.Size

@[expose] public section
namespace Hex.Kronecker.Preflight

/-- Exact clipping at a power-of-two threshold. Construct the threshold only
when a value actually saturates; the zero case also covers a zero bit budget. -/
def clip (bits n : Nat) : Nat :=
  if n == 0 || n.log2 < bits then n else 2 ^ bits

def add (bits a b : Nat) : Nat := clip bits (a + b)

/-- A sum of floor logarithms is a lower bound on the product logarithm.
Only this lower bound may certify overflow. The remaining product has at most
one bit beyond the threshold, and is clipped exactly. -/
def mul (bits a b : Nat) : Nat :=
  if a == 0 || b == 0 then 0
  else if bits ≤ a.log2 + b.log2 then 2 ^ bits
  else clip bits (a * b)

def powAux (bits : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | fuel + 1, a, n =>
      if n == 0 then 1
      else if a == 0 then 0
      else
        let q := powAux bits fuel a (n / 2)
        if q != 0 && bits ≤ q.log2 then 2 ^ bits
        else
          let square := mul bits q q
          if n % 2 == 0 then square else mul bits square a

def pow (bits a n : Nat) : Nat := powAux bits n a n

def sum (bits : Nat) (a b : Bounds) : Bounds :=
  ⟨maxDegrees a.degrees b.degrees, add bits a.height b.height⟩

def product (bits : Nat) (a b : Bounds) : Bounds :=
  ⟨addDegrees a.degrees b.degrees, mul bits a.height b.height⟩

def power (bits : Nat) (a : Bounds) (n : Nat) : Bounds :=
  ⟨scaleDegrees n a.degrees, pow bits a.height n⟩

/-- The same exceptional-descendant scan as the public preflight, using
bit-length guards instead of eagerly constructing its coefficient threshold. -/
def scan (bits k : Nat) (e : Expr) : Bounds × (List Bounds → List Bounds) :=
  Expr.rec
    (fun z => (Bounds.mk (zeroDegrees k) (clip bits z.natAbs), id))
    (fun i => (Bounds.mk (atomDegrees k i) 1, id))
    (fun _ _ a b => (sum bits a.1 b.1, fun acc => a.2 (b.2 acc)))
    (fun _ _ a b => (sum bits a.1 b.1, fun acc => a.2 (b.2 acc)))
    (fun _ a => a)
    (fun _ _ a b =>
      (product bits a.1 b.1, fun acc =>
        if a.1.height == 0 || b.1.height == 0 then a.1 :: b.1 :: a.2 (b.2 acc)
        else a.2 (b.2 acc)))
    (fun _ n a => (power bits a.1 n, fun acc => if n == 0 then a.1 :: a.2 acc else a.2 acc)) e

def analyze (bits k : Nat) (e : Expr) (acc : List Bounds) : Bounds × List Bounds :=
  let (b, bs) := scan bits k e
  (b, b :: bs acc)

/-- An equivalent full size report, with the cap allocated only upon saturation. -/
def exprEq (budget : Budget) (k : Nat) (lhs rhs : Expr) : Except SizeError SizeBound :=
  if !(lhs.wellFormed k && rhs.wellFormed k) then .error .atomIndex else
    let (l, bs) := analyze budget.maxPackedBits k lhs []
    let (r, bs) := analyze budget.maxPackedBits k rhs bs
    .ok (makeSize budget (sum budget.maxPackedBits l r) bs)

end Hex.Kronecker.Preflight
