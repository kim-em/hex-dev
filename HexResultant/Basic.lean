/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly
public meta import HexPoly.Dense

public section

/-!
Fraction-free polynomial pseudo-division.

For `n = degree f`, `m = degree g`, `d = n - m + 1`, and `b = lc(g)`,
`pseudoDivMod` computes the coefficients of the usual pseudo-division loop
directly.  It first builds `b^0, ..., b^d`, then the successive cancelled
leading coefficients

```
a_i = b^i * f[n-i]
      - sum (a_j * b^(i-1-j) * g[m+j-i]),
```

where `max(0, i-m) <= j < i`.  The quotient coefficients are
`q[k] = a_(d-1-k) * b^k`; the low `m` coefficients of
`b^d*f - q*g` are the remainder.  This dynamic coefficient recurrence avoids
materializing and rescaling the full quotient and remainder at every
elimination step.  Its nested folds have `O(d*m)` summands and it uses
`O(d+m)` coefficient storage.

The fixed `b^d` factor is built into both output formulas.  Consequently the
residual scaling required when cancellation drops the degree by more than one
is automatic rather than a special loop case.

The function is total.  A zero divisor is a junk input and returns `(0, f)`.
An already-smaller dividend also returns `(0, f)`; this agrees with ordinary
division, although the fixed-exponent pseudo-division contract is stated only
for the degree-ordered case.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u} [Zero R] [DecidableEq R]

/--
Polynomial pseudo-division without coefficient division.

For `g != 0` and `g.degree? <= f.degree?`, let
`d = f.degree - g.degree + 1`.  Over a commutative ring its result `(q, r)`
satisfies

```
lc(g) ^ (f.degree - g.degree + 1) * f = q * g + r
```

with `r.degree? < g.degree?`.  The implementation asks only for the concrete
operations it executes; algebraic laws belong to the correctness theorems.
Its nested array folds have `O(d*m)` summands, matching the
pseudo-division complexity contract.

For the two inputs outside that contract, behavior is deliberately simple and
stable: `pseudoDivMod f 0 = (0, f)`, and if `f` is already smaller than a
nonzero `g`, then `pseudoDivMod f g = (0, f)`.
-/
@[expose]
def pseudoDivMod [One R] [Add R] [Sub R] [Mul R]
    (f g : DensePoly R) : DensePoly R × DensePoly R :=
  if g.isZero then
    (0, f)
  else if f.size < g.size then
    (0, f)
  else
    let n := f.size - 1
    let m := g.size - 1
    let d := f.size - g.size + 1
    let b := g.leadingCoeff
    let powers :=
      (Array.range d).foldl
        (fun powers _ =>
          powers.push (powers.getD (powers.size - 1) 1 * b))
        #[1]
    let active :=
      (Array.range d).foldl
        (fun active i =>
          let first := i - m
          let correction :=
            (Array.range (i - first)).foldl
              (fun acc offset =>
                let j := first + offset
                acc + active.getD j 0 * powers.getD (i - 1 - j) 0 *
                  g.coeff (m + j - i))
              0
          active.push (powers.getD i 0 * f.coeff (n - i) - correction))
        #[]
    let quotient :=
      (Array.range d).foldl
        (fun coeffs k =>
          coeffs.push (active.getD (d - 1 - k) 0 * powers.getD k 0))
        #[]
    let remainder :=
      (Array.range m).foldl
        (fun coeffs t =>
          let correction :=
            (Array.range (min (t + 1) d)).foldl
              (fun acc k =>
                acc + quotient.getD k 0 * g.coeff (t - k))
              0
          coeffs.push (powers.getD d 0 * f.coeff t - correction))
        #[]
    (ofCoeffs quotient, ofCoeffs remainder)

/-- A zero divisor takes the documented junk branch and leaves the dividend unchanged. -/
@[simp, grind =]
theorem pseudoDivMod_zero_right [One R] [Add R] [Sub R] [Mul R] (f : DensePoly R) :
    pseudoDivMod f 0 = (0, f) := by
  rfl

/-- If the dividend is already smaller, pseudo-division is ordinary division by inspection. -/
theorem pseudoDivMod_of_size_lt [One R] [Add R] [Sub R] [Mul R]
    (f g : DensePoly R) (h : f.size < g.size) :
    pseudoDivMod f g = (0, f) := by
  have hg : g.isZero = false :=
    (isZero_eq_false_iff g).2 (by omega)
  simp [pseudoDivMod, hg, h]

/-- Pseudo-division reconstructs the fixed leading-coefficient multiple of the dividend.

This theorem deliberately uses a fresh coefficient type: an ambient `Zero`
instance is not necessarily coherent with the zero supplied by
`Lean.Grind.CommRing`. -/
theorem pseudoDivMod_reconstruct_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (f g : DensePoly S) (hg : g ≠ 0) (hfg : g.size ≤ f.size) :
    let qr := pseudoDivMod f g
    scale (g.leadingCoeff ^ (f.size - g.size + 1)) f = qr.1 * g + qr.2 := by
  sorry

/-- Under the pseudo-division preconditions, the remainder is smaller than the divisor. -/
theorem pseudoDivMod_remainder_lt_core {S : Type u}
    [Lean.Grind.CommRing S] [DecidableEq S]
    (f g : DensePoly S) (hg : g ≠ 0) (hfg : g.size ≤ f.size) :
    (pseudoDivMod f g).2.size < g.size := by
  sorry

/-! Small compiled regressions for the pseudo-division loop. -/

-- `4 * (X^2 + 1) = (2*X - 1) * (2*X + 1) + 5`.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 0, 1] : List Int))
        (ofList ([1, 2] : List Int))
    qr.1.toArray.toList = [-1, 2] ∧ qr.2.toArray.toList = [5]

-- Monic pseudo-division specializes to ordinary monic division.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 0, 1] : List Int))
        (ofList ([1, 1] : List Int))
    qr.1.toArray.toList = [-1, 1] ∧ qr.2.toArray.toList = [2]

-- Early cancellation still scales the quotient for every unused round.
#guard
    let qr := pseudoDivMod
        (ofList ([0, 0, 1] : List Int))
        (ofList ([0, 2] : List Int))
    qr.1.toArray.toList = [0, 2] ∧ qr.2.toArray.toList = []

-- A degree drop greater than one retains the residual leading-coefficient scaling.
-- `4*X^3 = (2*X)*(2*X^2 + 1) - 2*X`.
#guard
    let qr := pseudoDivMod
        (ofList ([0, 0, 0, 1] : List Int))
        (ofList ([1, 0, 2] : List Int))
    qr.1.toArray.toList = [0, 2] ∧ qr.2.toArray.toList = [0, -2]

-- Division by a constant uses all `degree(f) + 1` scaling rounds.
-- `27*(X^2 + 1) = (9*X^2 + 9)*3`.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 0, 1] : List Int))
        (ofList ([3] : List Int))
    qr.1.toArray.toList = [9, 0, 9] ∧ qr.2.toArray.toList = []

-- Equal-degree inputs take one round: `2*(X + 1) = 2*X + 3 - 1`.
#guard
    let qr := pseudoDivMod
        (ofList ([1, 1] : List Int))
        (ofList ([3, 2] : List Int))
    qr.1.toArray.toList = [1] ∧ qr.2.toArray.toList = [-1]

-- An already-smaller dividend is returned unchanged as the remainder.
#guard
    let qr := pseudoDivMod
        (ofList ([3] : List Int))
        (ofList ([1, 1] : List Int))
    qr.1.toArray.toList = [] ∧ qr.2.toArray.toList = [3]

-- The zero dividend takes the smaller-degree branch for a nonconstant divisor.
#guard
    let qr := pseudoDivMod 0 (ofList ([1, 1] : List Int))
    qr.1.toArray.toList = ([] : List Int) ∧ qr.2.toArray.toList = []

-- The documented zero-divisor junk case is total and leaves the dividend alone.
#guard
    let qr := pseudoDivMod (ofList ([1, 0, 1] : List Int)) 0
    qr.1.toArray.toList = ([] : List Int) ∧ qr.2.toArray.toList = [1, 0, 1]

end Hex.DensePoly
