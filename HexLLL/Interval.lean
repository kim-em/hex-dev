/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL.Lattice

public section

/-!
Fixed-precision dyadic interval-arithmetic kernel (`Ival`, `IntervalGS`):
closed integer-mantissa intervals at a shared power-of-two scale, used by
the enclosure reducedness checker. Mathlib-free; no floating point.
-/

namespace Hex.Internal

/-! ### Fixed-precision dyadic interval kernel

The certified-dispatch reducedness clause is decided first by a sound
enclosure pass at fixed working precision; only on indecision does it fall
back to the exact integer checker. The kernel below is the Mathlib-free
executable surface: closed dyadic intervals whose endpoints are `Int`
mantissas at a shared power-of-two scale. Per-operation containment lemmas
and the composed soundness theorem (`lllReducedInterval_sound`) live in
HexLLLMathlib. -/

/-- Closed dyadic interval `[lo / S, hi / S]` whose endpoints are integer
mantissas at a shared power-of-two scale `S = 2 ^ prec`. The scale is not
stored; every operation that rounds takes `S` explicitly, so the working
precision stays a parameter of the checker. -/
structure Ival where
  lo : Int
  hi : Int
deriving Repr, BEq, Inhabited

namespace Ival

/-- The rational `x` lies in the dyadic interval `I` read at scale `S`. -/
@[expose]
def mem (S : Int) (I : Ival) (x : Rat) : Prop :=
  (I.lo : Rat) ≤ x * (S : Rat) ∧ x * (S : Rat) ≤ (I.hi : Rat)

/-- Exact embedding of an integer at scale `S`. -/
@[expose]
def ofInt (S z : Int) : Ival :=
  ⟨z * S, z * S⟩

/-- Ceiling division for a positive divisor, via `Int.fdiv` of the
negated dividend. -/
@[expose]
def cdiv (a b : Int) : Int :=
  -(Int.fdiv (-a) b)

/-- One-ulp enclosure of a rational at scale `S`. -/
@[expose]
def ofRat (S : Int) (q : Rat) : Ival :=
  ⟨Int.fdiv (q.num * S) q.den, cdiv (q.num * S) q.den⟩

/-- Interval addition. Fixed-point addition is exact: no rounding. -/
@[expose]
def add (a b : Ival) : Ival :=
  ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Interval subtraction. Exact, like `add`. -/
@[expose]
def sub (a b : Ival) : Ival :=
  ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- Interval multiplication. Endpoint products land at scale `S²`, so the
result rounds outward through one floor / ceiling division by `S`. -/
@[expose]
def mul (S : Int) (a b : Ival) : Ival :=
  let p₁ := a.lo * b.lo
  let p₂ := a.lo * b.hi
  let p₃ := a.hi * b.lo
  let p₄ := a.hi * b.hi
  ⟨Int.fdiv (min (min p₁ p₂) (min p₃ p₄)) S,
    cdiv (max (max p₁ p₂) (max p₃ p₄)) S⟩

/-- Interval division by an interval the caller has checked to be strictly
positive (`0 < b.lo`). The numerator rescales by `S` so the quotient lands
back at scale `S`. Well-defined but junk when the positivity precondition
fails; the containment lemma is conditional on it. -/
@[expose]
def divPos (S : Int) (a b : Ival) : Ival :=
  ⟨min (Int.fdiv (a.lo * S) b.lo) (Int.fdiv (a.lo * S) b.hi),
    max (cdiv (a.hi * S) b.lo) (cdiv (a.hi * S) b.hi)⟩

/-- Endpoint bounds of the product of two intervals, sign-cased so the
common (sign-definite) cases cost two integer multiplications instead of
four products plus comparisons. Returns `(lo, hi)` at the product scale of
its inputs. -/
@[expose, inline] def prodBounds (a b : Ival) : Int × Int :=
  if 0 ≤ a.lo then
    if 0 ≤ b.lo then (a.lo * b.lo, a.hi * b.hi)
    else if b.hi ≤ 0 then (a.hi * b.lo, a.lo * b.hi)
    else (a.hi * b.lo, a.hi * b.hi)
  else if a.hi ≤ 0 then
    if 0 ≤ b.lo then (a.lo * b.hi, a.hi * b.lo)
    else if b.hi ≤ 0 then (a.hi * b.hi, a.lo * b.lo)
    else (a.lo * b.hi, a.lo * b.lo)
  else
    if 0 ≤ b.lo then (a.lo * b.hi, a.hi * b.hi)
    else if b.hi ≤ 0 then (a.hi * b.lo, a.lo * b.lo)
    else (min (a.lo * b.hi) (a.hi * b.lo), max (a.lo * b.lo) (a.hi * b.hi))

end Ival

namespace IntervalGS

/-- One step of the Gram-Schmidt dot recurrence on enclosures:
`g − Σ_{k < t} mu[k] · r[k]`, with `g` an exact Gram entry. With
`mu = μ[j][·]` and `r = r[i][·]` this encloses `⟨b_i, b*_j⟩`; with
`mu = r = ` row `i`'s own data it encloses `‖b*_i‖²`.

The sum accumulates exactly at scale `S²` (endpoint products of scale-`S`
mantissas) and rounds outward through a single floor / ceiling division at
the end, so a length-`t` dot recurrence costs one rounding division rather
than `t` of them. -/
@[expose]
def dotStep (S : Int) (mu r : Array Ival) (g : Int) (t : Nat) : Ival :=
  let acc :=
    (List.range t).foldl
      (fun (acc : Int × Int) k =>
        let p := Ival.prodBounds mu[k]! r[k]!
        (acc.1 - p.2, acc.2 - p.1))
      (g * S * S, g * S * S)
  ⟨Int.fdiv acc.1 S, Ival.cdiv acc.2 S⟩

/-- One column step of the per-row fold: extend the `r` row with the
enclosure of `⟨b_i, b*_j⟩` and the `μ` row with the enclosure of
`μ[i][j] = ⟨b_i, b*_j⟩ / ‖b*_j‖²`. -/
@[expose, inline] def rowStep (S : Int) (gRow : Array Int) (mus : Array (Array Ival))
    (bstars : Array Ival) (acc : Array Ival × Array Ival) (j : Nat) :
    Array Ival × Array Ival :=
  let r := dotStep S mus[j]! acc.1 gRow[j]! j
  (acc.1.push r, acc.2.push (Ival.divPos S r bstars[j]!))

/-- Enclosure pass for one basis row: from the exact Gram row `gRow` and the
enclosure rows of all earlier indices, produce the `μ[i][·]` enclosure row
and the `‖b*_i‖²` enclosure. The intermediate `r` row encloses the dot
products `⟨b_i, b*_j⟩`. -/
@[expose]
def row (S : Int) (gRow : Array Int) (mus : Array (Array Ival))
    (bstars : Array Ival) (i : Nat) : Array Ival × Ival :=
  let acc := (List.range i).foldl (rowStep S gRow mus bstars) (#[], #[])
  (acc.2, dotStep S acc.2 acc.1 gRow[i]! i)

/-- One row step of the pass fold: run `row`, demand a strictly positive
norm enclosure, and extend the accumulated enclosure state. -/
@[expose, inline] def passStep (S : Int) (g : Array (Array Int))
    (acc : Array (Array Ival) × Array Ival) (i : Nat) :
    Option (Array (Array Ival) × Array Ival) :=
  let r := row S g[i]! acc.1 acc.2 i
  if 0 < r.2.lo then
    some (acc.1.push r.1, acc.2.push r.2)
  else
    none

/-- Full interval Gram-Schmidt pass over the exact `n × n` Gram matrix:
`O(n³)` interval operations on fixed-scale mantissas, independent of the
Gram-determinant bit growth of the input family. Returns the enclosure rows
of the Gram-Schmidt coefficients and the squared basis norms, or `none` as
soon as some norm enclosure fails strict positivity (the division by that
norm would be unsound, and reducedness could not be decided either way). -/
@[expose]
def pass (S : Int) (g : Array (Array Int)) (n : Nat) :
    Option (Array (Array Ival) × Array Ival) :=
  (List.range n).foldlM (passStep S g) (#[], #[])

/-- Size-reduction clause on enclosures: every `μ[i][j]` interval lies
inside `[−η, η]`, compared exactly through `η = η.num / η.den`. -/
@[expose]
def sizeOK (S : Int) (η : Rat) (mus : Array (Array Ival)) (n : Nat) : Bool :=
  (List.range n).all fun i =>
    (List.range i).all fun j =>
      let I := mus[i]![j]!
      decide (I.hi * (η.den : Int) ≤ η.num * S) &&
        decide (-(η.num * S) ≤ I.lo * (η.den : Int))

/-- Lovász clause on enclosures at every adjacent pair: the largest possible
`δ‖b*_i‖²` is at most the smallest possible `‖b*_{i+1}‖² + μ²‖b*_i‖²`. -/
@[expose]
def lovaszOK (S : Int) (δ : Rat) (mus : Array (Array Ival))
    (bstars : Array Ival) (n : Nat) : Bool :=
  let Iδ := Ival.ofRat S δ
  (List.range (n - 1)).all fun i =>
    let μ := mus[i + 1]![i]!
    let lhs := Ival.mul S Iδ bstars[i]!
    let rhs := (bstars[i + 1]!).add (Ival.mul S (Ival.mul S μ μ) bstars[i]!)
    decide (lhs.hi ≤ rhs.lo)

end IntervalGS

end Hex.Internal
