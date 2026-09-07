/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexConway.Api
public import HexConway.Power
public import HexPrimality.Cert

public section

/-!
Tier 2: primitivity of the committed Conway entries.

A Conway polynomial is required to be *primitive*: the residue of `x` in
`F_p[x] / (C(p, n))` must generate the multiplicative group, so its order is
exactly `N = p^n - 1` rather than a proper divisor.

# Why this is checkable

Order `N` is established by the standard test: `α ^ N = 1`, and
`α ^ (N / q) ≠ 1` for every prime `q` dividing `N`. Both halves are needed —
the first alone only says the order divides `N`.

The committed power data uses binary digits. Structural Horner evaluation
keeps the multiplication count logarithmic in the exponent, independently of
the characteristic. The generator searches for factorizations offline;
Pocklington certificates from `HexPrimality` prove their prime factors.

# What the check establishes, and what it does not

`primitiveCheck` validates all of its supplied data before using it: that their product with the multiplicities really is
`p^n - 1`, and that each digit list really decodes to the exponent it is meant
to be. Only then does it run the two power conditions.

The product test is what makes the prime list trustworthy, and it is worth
saying why. If the supplied `q_i` are prime and `∏ q_i ^ e_i = N`, then by
unique factorization the `q_i` are *exactly* the prime divisors of `N` — there
is no room for a missing one. So checking `α ^ (N / q) ≠ 1` across the supplied
list really does cover every prime divisor, and a caller cannot weaken the test
by handing it a short list: the product would come out wrong.

Given all of it, the multiplicative order of `α` is `N`. The transport that
states this in Mathlib's terms is in `HexGFqMathlib.Primitivity`, which carries
these structural powers to Mathlib powers along `ofPolyHom` and supplies the
exhaustiveness of the prime list.

This module defines the checker; the generated primitivity facts are in
`HexConway.Primitivity`, including the trivial group at `C(2, 1)`.
-/

namespace Hex

namespace Conway

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- Structural modular power: `k` multiplications, each followed by reduction.
Linear in `k`, and only ever called with `k ≤ p`. -/
@[expose]
def linPowMod (f : FpPoly p) (hm : DensePoly.Monic f) (x : FpPoly p) :
    Nat → FpPoly p
  | 0 => 1
  | k + 1 => FpPoly.modByMonic f (linPowMod f hm x k * x) hm

omit [ZMod64.PrimeModulus p] in
/-- The structural linear helper agrees with the polynomial library's power. -/
theorem linPowMod_eq (f : FpPoly p) (hm : DensePoly.Monic f) (x : FpPoly p)
    (k : Nat) : linPowMod f hm x k = FpPoly.powModMonicLinear x f hm k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [linPowMod, FpPoly.powModMonicLinear, ih]

/-- A reduced representative of the generator raised to a supplied exponent. -/
@[expose] def powerResidue (f : FpPoly p) (hm : DensePoly.Monic f) (k : Nat) : FpPoly p :=
  FpPoly.modByMonic f (powMod FpPoly.X f hm k) hm

/-- Horner over base-`q` digits, most significant first: raises the accumulator
to the `q`-th power and multiplies in `x ^ d` at each digit. -/
@[expose]
def digitPowMod (f : FpPoly p) (hm : DensePoly.Monic f) (q : Nat) (x : FpPoly p)
    (acc : FpPoly p) : List Nat → FpPoly p
  | [] => acc
  | d :: ds =>
      digitPowMod f hm q x
        (FpPoly.modByMonic f (linPowMod f hm acc q * linPowMod f hm x d) hm) ds

/-- The product of `qs` raised to the matching multiplicities in `es`. -/
@[expose]
def primePowerProduct : List Nat → List Nat → Nat
  | [], _ => 1
  | _, [] => 1
  | q :: qs, e :: es => q ^ e * primePowerProduct qs es

/-- The value of a base-`q` digit list, most significant first. This is what
ties a digit list to the exponent it is supposed to encode. -/
@[expose]
def digitsValue (q : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d * q ^ ds.length + digitsValue q ds

/--
The Tier 2 primitivity check for a committed entry.

`fullDigits` is `p^n - 1` in base `2`, most significant first, and
`perPrimeDigits` holds `(p^n - 1) / q` in the same form, in the same order as
`qs`; `es` carries the multiplicities.

Every piece of supplied data is validated before it is used, except the
primality of `qs`, which is carried as a hypothesis by
`Primitive` instead. Deciding primality inline does not scale:
the generated proofs replay `HexPrimality` certificates for the factors. Given
primality, the product check forces `qs` to be *all* the prime divisors, by
unique factorization. The digit lists are checked to decode to `p^n - 1` and to each
`(p^n - 1) / q`, so a caller cannot pass exponents that are easy to satisfy.
Only then are the two power conditions run.
-/
@[expose]
def primitiveCheck (f : FpPoly p) (hm : DensePoly.Monic f) (n : Nat)
    (qs es : List Nat) (fullDigits : List Nat)
    (perPrimeDigits : List (List Nat)) : Bool :=
  let order := p ^ n - 1
  -- The supplied factorization is a factorization of `p^n - 1` into primes.
  (primePowerProduct qs es == order) &&
  -- The supplied digit lists decode to the exponents they are meant to be.
  (digitsValue 2 fullDigits == order) &&
  (perPrimeDigits.length == qs.length) &&
  ((qs.zip perPrimeDigits).all (fun qd => digitsValue 2 qd.2 == order / qd.1)) &&
  -- `α ^ (p^n - 1) = 1`, and `α ^ ((p^n - 1) / q) ≠ 1` for each such prime.
  (powerResidue f hm (digitsValue 2 fullDigits) == 1) &&
  perPrimeDigits.all (fun ds => !(powerResidue f hm (digitsValue 2 ds) == 1))

/--
The committed entry `C(p, n)` is primitive: the residue of `x` has
multiplicative order exactly `p^n - 1`, witnessed by the supplied
factorization and power data.
-/
structure Primitive (p n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (h : SupportedEntry p n) (qs es : List Nat) (fullDigits : List Nat)
    (perPrimeDigits : List (List Nat)) : Prop where
  /-- The supplied divisors are prime. Together with the product check inside
  `primitiveCheck` this makes them exactly the prime divisors of `p^n - 1`. -/
  primes : ∀ q ∈ qs, Hex.Nat.Prime q
  /-- The arithmetic and the two power conditions, all decidable. -/
  check : primitiveCheck (conwayPoly p n h) (conwayPoly_monic p n h) n qs es
    fullDigits perPrimeDigits = true


end Conway
end Hex
