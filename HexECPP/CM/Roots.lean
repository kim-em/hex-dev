/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.CM
public import HexECPP.CM.ClassPolynomials

public section

/-!
# Bounded roots of the fixed linear/quadratic portfolio

The quadratic formula needs one Tonelli–Shanks call and no random splits.
Every returned residue is checked by Horner evaluation, even over composite
moduli. `rootWork` reserves a modular-operation upper bound before invocation;
it is linear in exponent bits plus quadratic in the two-adic valuation.
No class polynomial generation, general polynomial factorization or external
process occurs during native production.
-/

namespace Hex.ECPP.CM

/-- Horner evaluation modulo the subject, for ascending coefficients. -/
def evaluate (n x : Nat) (coefficients : List Int) : Nat :=
  coefficients.foldr (fun c acc => (residue n c + x * acc) % n) 0

/-- Conservative modular-operation reservation for one closed-form root call.
For Tonelli–Shanks, at most `s` iterations each use at most `3*s+3`
operations; four initial exponentiations use at most eight subject-bit lengths.
The remaining margin covers root construction and two Horner checks. -/
def rootWork (n : Nat) (p : ClassPolynomial) : Nat :=
  if p.coefficients.length ≤ 2 then 8 else
    let s := (Hex.Nat.oddSplit (n - 1)).1
    12 * (HexArith.bitLength n + 1) + 3 * (s + 1) ^ 2 + 64

/-- Checked canonical roots of a monic polynomial of degree at most two.
Other polynomial shapes are rejected. The explicit operation reservation is
checked by the caller before executing this bounded algorithm. -/
def roots? (n z : Nat) (p : ClassPolynomial) : List Nat := Id.run do
  if n ≤ 2 || n % 2 == 0 then return []
  let candidates ← match p.coefficients with
    | [c, 1] => pure [residue n (-c)]
    | [c, b, 1] =>
        let some half := inverse? n 2 | return []
        let discriminant := residue n (b * b - 4 * c)
        let some r := sqrt? n z discriminant | return []
        let minusB := residue n (-b)
        pure [((minusB + r) * half) % n, (modSub n minusB r * half) % n]
    | _ => return []
  return (candidates.filter fun r => r < n && evaluate n r p.coefficients == 0).eraseDups

/-- The original nine invariants as linear polynomials, in the same order. -/
def originalPolynomials : List ClassPolynomial :=
  portfolio.map fun inv => ⟨inv.d, [-inv.j, 1]⟩

end Hex.ECPP.CM
