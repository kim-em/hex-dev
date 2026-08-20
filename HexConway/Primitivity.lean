/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexConway.Api
import HexArith.Nat.Prime

/-!
Tier 2: primitivity of the committed Conway entries.

A Conway polynomial is required to be *primitive*: the residue of `x` in
`F_p[x] / (C(p, n))` must generate the multiplicative group, so its order is
exactly `N = p^n - 1` rather than a proper divisor.

# Why this is checkable

Order `N` is established by the standard test: `α ^ N = 1`, and
`α ^ (N / q) ≠ 1` for every prime `q` dividing `N`. Both halves are needed —
the first alone only says the order divides `N`.

The exponents are large (`4826808` at `(13, 6)`), so they are not replayed by
repeated multiplication. Writing the exponent in base `p` and running Horner
costs `n` steps, each one `p` squarings-by-multiplication plus at most `p - 1`
more, so a whole check is a few hundred modular multiplications instead of
millions. Everything below is structurally recursive because the kernel has to
run it; `GFqField.pow` is square-and-multiply over well-founded recursion and
does not reduce.

# What the check establishes, and what it does not

`primitiveCheck` validates all of its supplied data before using it: that the
primes really are prime, that their product with the multiplicities really is
`p^n - 1`, and that each digit list really decodes to the exponent it is meant
to be. Only then does it run the two power conditions.

The product test is what makes the prime list trustworthy, and it is worth
saying why. If the supplied `q_i` are prime and `∏ q_i ^ e_i = N`, then by
unique factorization the `q_i` are *exactly* the prime divisors of `N` — there
is no room for a missing one. So checking `α ^ (N / q) ≠ 1` across the supplied
list really does cover every prime divisor, and a caller cannot weaken the test
by handing it a short list: the product would come out wrong.

Given all of it, the multiplicative order of `α` is `N`. That last step is not
formalised here, and the obstacle is worth naming: `GFq` carries both Hex's
`Pow` and the `npowRec` that Mathlib's `Field` instance installs, and the two
are not definitionally equal. So a statement written with `^` on the field side
picks up whichever instance elaboration reaches first, and the power lemmas
then fail to match. Getting to `orderOf` means pinning that down — either by
keeping every power on the `FpPoly` side, where the scoped `CommRing` makes `^`
unambiguous, or by reconciling the two instances on `GFq`. Mathlib supplies the
group theory itself (`orderOf_eq_of_pow_and_pow_div_prime`) and
`HexGFqMathlib.ofPolyHom` supplies the ring homomorphism; it is the diamond in
between that needs settling.

What this file provides is the verified computational content, for all
thirty-seven committed entries with `p^n > 2`.
-/

namespace Hex

namespace Conway

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- Structural modular power: `k` multiplications, each followed by reduction.
Linear in `k`, and only ever called with `k ≤ p`. -/
def linPowMod (f : FpPoly p) (hm : DensePoly.Monic f) (x : FpPoly p) :
    Nat → FpPoly p
  | 0 => 1
  | k + 1 => FpPoly.modByMonic f (linPowMod f hm x k * x) hm

/-- Horner over base-`q` digits, most significant first: raises the accumulator
to the `q`-th power and multiplies in `x ^ d` at each digit. -/
def digitPowMod (f : FpPoly p) (hm : DensePoly.Monic f) (q : Nat) (x : FpPoly p)
    (acc : FpPoly p) : List Nat → FpPoly p
  | [] => acc
  | d :: ds =>
      digitPowMod f hm q x
        (FpPoly.modByMonic f (linPowMod f hm acc q * linPowMod f hm x d) hm) ds

/-- The product of `qs` raised to the matching multiplicities in `es`. -/
def primePowerProduct : List Nat → List Nat → Nat
  | [], _ => 1
  | _, [] => 1
  | q :: qs, e :: es => q ^ e * primePowerProduct qs es

/-- The value of a base-`q` digit list, most significant first. This is what
ties a digit list to the exponent it is supposed to encode. -/
def digitsValue (q : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d * q ^ ds.length + digitsValue q ds

/--
The Tier 2 primitivity check for a committed entry.

`fullDigits` is `p^n - 1` in base `p`, most significant first, and
`perPrimeDigits` holds `(p^n - 1) / q` in the same form, in the same order as
`qs`; `es` carries the multiplicities.

Every piece of supplied data is validated before it is used, except the
primality of `qs`, which is carried as a hypothesis by
`Primitive` instead. Deciding primality inline does not scale:
the divisors of `p^n - 1` reach five digits, and the linear instance is far too
slow there — `Hex.Nat.prime_of_bounded` is what those proofs use. Given
primality, the product check forces `qs` to be *all* the prime divisors, by
unique factorization. The digit lists are checked to decode to `p^n - 1` and to each
`(p^n - 1) / q`, so a caller cannot pass exponents that are easy to satisfy.
Only then are the two power conditions run.
-/
def primitiveCheck (f : FpPoly p) (hm : DensePoly.Monic f) (n : Nat)
    (qs es : List Nat) (fullDigits : List Nat)
    (perPrimeDigits : List (List Nat)) : Bool :=
  let order := p ^ n - 1
  -- The supplied factorization is a factorization of `p^n - 1` into primes.
  (primePowerProduct qs es == order) &&
  -- The supplied digit lists decode to the exponents they are meant to be.
  (digitsValue p fullDigits == order) &&
  (perPrimeDigits.length == qs.length) &&
  ((qs.zip perPrimeDigits).all (fun qd => digitsValue p qd.2 == order / qd.1)) &&
  -- `α ^ (p^n - 1) = 1`, and `α ^ ((p^n - 1) / q) ≠ 1` for each such prime.
  (digitPowMod f hm p FpPoly.X 1 fullDigits == 1) &&
  perPrimeDigits.all (fun ds => !(digitPowMod f hm p FpPoly.X 1 ds == 1))

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

/-! # The committed primitivity facts

One theorem for each committed entry with `p ^ n > 2`; thirty-seven in all.
`C(2, 1)` is excluded because its multiplicative group is trivial, so there is
no order condition to state.
-/

-- The three largest entries (11^6, 13^5, 13^6) exceed the default heartbeat
-- budget; the rest are well inside it. Raised for the block rather than
-- per-theorem since every theorem here is the same kind of kernel replay.
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- `C(2, 2)` is primitive: the residue of `x` has order `2^2 - 1 = 3`. -/
theorem primitive_2_2 :
    Primitive 2 2 supportedEntry_2_2 [3] [1]
      [1, 1]
      [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(2, 3)` is primitive: the residue of `x` has order `2^3 - 1 = 7`. -/
theorem primitive_2_3 :
    Primitive 2 3 supportedEntry_2_3 [7] [1]
      [1, 1, 1]
      [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(2, 4)` is primitive: the residue of `x` has order `2^4 - 1 = 15`. -/
theorem primitive_2_4 :
    Primitive 2 4 supportedEntry_2_4 [3, 5] [1, 1]
      [1, 1, 1, 1]
      [[1, 0, 1], [1, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(2, 5)` is primitive: the residue of `x` has order `2^5 - 1 = 31`. -/
theorem primitive_2_5 :
    Primitive 2 5 supportedEntry_2_5 [31] [1]
      [1, 1, 1, 1, 1]
      [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 31 5 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(2, 6)` is primitive: the residue of `x` has order `2^6 - 1 = 63`. -/
theorem primitive_2_6 :
    Primitive 2 6 supportedEntry_2_6 [3, 7] [2, 1]
      [1, 1, 1, 1, 1, 1]
      [[1, 0, 1, 0, 1], [1, 0, 0, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(2, 7)` is primitive: the residue of `x` has order `2^7 - 1 = 127`. -/
theorem primitive_2_7 :
    Primitive 2 7 supportedEntry_2_7 [127] [1]
      [1, 1, 1, 1, 1, 1, 1]
      [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 127 11 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(2, 8)` is primitive: the residue of `x` has order `2^8 - 1 = 255`. -/
theorem primitive_2_8 :
    Primitive 2 8 supportedEntry_2_8 [3, 5, 17] [1, 1, 1]
      [1, 1, 1, 1, 1, 1, 1, 1]
      [[1, 0, 1, 0, 1, 0, 1], [1, 1, 0, 0, 1, 1], [1, 1, 1, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 17 4 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(3, 1)` is primitive: the residue of `x` has order `3^1 - 1 = 2`. -/
theorem primitive_3_1 :
    Primitive 3 1 supportedEntry_3_1 [2] [1]
      [2]
      [[1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(3, 2)` is primitive: the residue of `x` has order `3^2 - 1 = 8`. -/
theorem primitive_3_2 :
    Primitive 3 2 supportedEntry_3_2 [2] [3]
      [2, 2]
      [[1, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(3, 3)` is primitive: the residue of `x` has order `3^3 - 1 = 26`. -/
theorem primitive_3_3 :
    Primitive 3 3 supportedEntry_3_3 [2, 13] [1, 1]
      [2, 2, 2]
      [[1, 1, 1], [2]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 13 3 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(3, 4)` is primitive: the residue of `x` has order `3^4 - 1 = 80`. -/
theorem primitive_3_4 :
    Primitive 3 4 supportedEntry_3_4 [2, 5] [4, 1]
      [2, 2, 2, 2]
      [[1, 1, 1, 1], [1, 2, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(3, 5)` is primitive: the residue of `x` has order `3^5 - 1 = 242`. -/
theorem primitive_3_5 :
    Primitive 3 5 supportedEntry_3_5 [2, 11] [1, 2]
      [2, 2, 2, 2, 2]
      [[1, 1, 1, 1, 1], [2, 1, 1]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 11 3 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(3, 6)` is primitive: the residue of `x` has order `3^6 - 1 = 728`. -/
theorem primitive_3_6 :
    Primitive 3 6 supportedEntry_3_6 [2, 7, 13] [3, 1, 1]
      [2, 2, 2, 2, 2, 2]
      [[1, 1, 1, 1, 1, 1], [1, 0, 2, 1, 2], [2, 0, 0, 2]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 13 3 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(5, 1)` is primitive: the residue of `x` has order `5^1 - 1 = 4`. -/
theorem primitive_5_1 :
    Primitive 5 1 supportedEntry_5_1 [2] [2]
      [4]
      [[2]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(5, 2)` is primitive: the residue of `x` has order `5^2 - 1 = 24`. -/
theorem primitive_5_2 :
    Primitive 5 2 supportedEntry_5_2 [2, 3] [3, 1]
      [4, 4]
      [[2, 2], [1, 3]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(5, 3)` is primitive: the residue of `x` has order `5^3 - 1 = 124`. -/
theorem primitive_5_3 :
    Primitive 5 3 supportedEntry_5_3 [2, 31] [2, 1]
      [4, 4, 4]
      [[2, 2, 2], [4]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 31 5 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(5, 4)` is primitive: the residue of `x` has order `5^4 - 1 = 624`. -/
theorem primitive_5_4 :
    Primitive 5 4 supportedEntry_5_4 [2, 3, 13] [4, 1, 1]
      [4, 4, 4, 4]
      [[2, 2, 2, 2], [1, 3, 1, 3], [1, 4, 3]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 13 3 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(5, 5)` is primitive: the residue of `x` has order `5^5 - 1 = 3124`. -/
theorem primitive_5_5 :
    Primitive 5 5 supportedEntry_5_5 [2, 11, 71] [2, 1, 1]
      [4, 4, 4, 4, 4]
      [[2, 2, 2, 2, 2], [2, 1, 1, 4], [1, 3, 4]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 11 3 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 71 8 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(5, 6)` is primitive: the residue of `x` has order `5^6 - 1 = 15624`. -/
theorem primitive_5_6 :
    Primitive 5 6 supportedEntry_5_6 [2, 3, 7, 31] [3, 2, 1, 1]
      [4, 4, 4, 4, 4, 4]
      [[2, 2, 2, 2, 2, 2], [1, 3, 1, 3, 1, 3], [3, 2, 4, 1, 2], [4, 0, 0, 4]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 31 5 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(7, 1)` is primitive: the residue of `x` has order `7^1 - 1 = 6`. -/
theorem primitive_7_1 :
    Primitive 7 1 supportedEntry_7_1 [2, 3] [1, 1]
      [6]
      [[3], [2]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(7, 2)` is primitive: the residue of `x` has order `7^2 - 1 = 48`. -/
theorem primitive_7_2 :
    Primitive 7 2 supportedEntry_7_2 [2, 3] [4, 1]
      [6, 6]
      [[3, 3], [2, 2]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(7, 3)` is primitive: the residue of `x` has order `7^3 - 1 = 342`. -/
theorem primitive_7_3 :
    Primitive 7 3 supportedEntry_7_3 [2, 3, 19] [1, 2, 1]
      [6, 6, 6]
      [[3, 3, 3], [2, 2, 2], [2, 4]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 19 4 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(7, 4)` is primitive: the residue of `x` has order `7^4 - 1 = 2400`. -/
theorem primitive_7_4 :
    Primitive 7 4 supportedEntry_7_4 [2, 3, 5] [5, 1, 2]
      [6, 6, 6, 6]
      [[3, 3, 3, 3], [2, 2, 2, 2], [1, 2, 5, 4]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(7, 5)` is primitive: the residue of `x` has order `7^5 - 1 = 16806`. -/
theorem primitive_7_5 :
    Primitive 7 5 supportedEntry_7_5 [2, 3, 2801] [1, 1, 1]
      [6, 6, 6, 6, 6]
      [[3, 3, 3, 3, 3], [2, 2, 2, 2, 2], [6]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2801 52 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(7, 6)` is primitive: the residue of `x` has order `7^6 - 1 = 117648`. -/
theorem primitive_7_6 :
    Primitive 7 6 supportedEntry_7_6 [2, 3, 19, 43] [4, 2, 1, 1]
      [6, 6, 6, 6, 6, 6]
      [[3, 3, 3, 3, 3, 3], [2, 2, 2, 2, 2, 2], [2, 4, 0, 2, 4], [1, 0, 6, 5, 6]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 19 4 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 43 6 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(11, 1)` is primitive: the residue of `x` has order `11^1 - 1 = 10`. -/
theorem primitive_11_1 :
    Primitive 11 1 supportedEntry_11_1 [2, 5] [1, 1]
      [10]
      [[5], [2]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(11, 2)` is primitive: the residue of `x` has order `11^2 - 1 = 120`. -/
theorem primitive_11_2 :
    Primitive 11 2 supportedEntry_11_2 [2, 3, 5] [3, 1, 1]
      [10, 10]
      [[5, 5], [3, 7], [2, 2]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(11, 3)` is primitive: the residue of `x` has order `11^3 - 1 = 1330`. -/
theorem primitive_11_3 :
    Primitive 11 3 supportedEntry_11_3 [2, 5, 7, 19] [1, 1, 1, 1]
      [10, 10, 10]
      [[5, 5, 5], [2, 2, 2], [1, 6, 3], [6, 4]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 19 4 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(11, 4)` is primitive: the residue of `x` has order `11^4 - 1 = 14640`. -/
theorem primitive_11_4 :
    Primitive 11 4 supportedEntry_11_4 [2, 3, 5, 61] [4, 1, 1, 1]
      [10, 10, 10, 10]
      [[5, 5, 5, 5], [3, 7, 3, 7], [2, 2, 2, 2], [1, 10, 9]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 61 7 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(11, 5)` is primitive: the residue of `x` has order `11^5 - 1 = 161050`. -/
theorem primitive_11_5 :
    Primitive 11 5 supportedEntry_11_5 [2, 5, 3221] [1, 2, 1]
      [10, 10, 10, 10, 10]
      [[5, 5, 5, 5, 5], [2, 2, 2, 2, 2], [4, 6]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3221 56 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(11, 6)` is primitive: the residue of `x` has order `11^6 - 1 = 1771560`. -/
theorem primitive_11_6 :
    Primitive 11 6 supportedEntry_11_6 [2, 3, 5, 7, 19, 37] [3, 2, 1, 1, 1, 1]
      [10, 10, 10, 10, 10, 10]
      [[5, 5, 5, 5, 5, 5], [3, 7, 3, 7, 3, 7], [2, 2, 2, 2, 2, 2], [1, 6, 3, 1, 6, 3], [6, 4, 0, 6, 4], [3, 2, 10, 7, 8]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 19 4 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 37 6 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(13, 1)` is primitive: the residue of `x` has order `13^1 - 1 = 12`. -/
theorem primitive_13_1 :
    Primitive 13 1 supportedEntry_13_1 [2, 3] [2, 1]
      [12]
      [[6], [4]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(13, 2)` is primitive: the residue of `x` has order `13^2 - 1 = 168`. -/
theorem primitive_13_2 :
    Primitive 13 2 supportedEntry_13_2 [2, 3, 7] [3, 1, 1]
      [12, 12]
      [[6, 6], [4, 4], [1, 11]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(13, 3)` is primitive: the residue of `x` has order `13^3 - 1 = 2196`. -/
theorem primitive_13_3 :
    Primitive 13 3 supportedEntry_13_3 [2, 3, 61] [2, 2, 1]
      [12, 12, 12]
      [[6, 6, 6], [4, 4, 4], [2, 10]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 61 7 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(13, 4)` is primitive: the residue of `x` has order `13^4 - 1 = 28560`. -/
theorem primitive_13_4 :
    Primitive 13 4 supportedEntry_13_4 [2, 3, 5, 7, 17] [4, 1, 1, 1, 1]
      [12, 12, 12, 12]
      [[6, 6, 6, 6], [4, 4, 4, 4], [2, 7, 10, 5], [1, 11, 1, 11], [9, 12, 3]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 5 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 17 4 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(13, 5)` is primitive: the residue of `x` has order `13^5 - 1 = 371292`. -/
theorem primitive_13_5 :
    Primitive 13 5 supportedEntry_13_5 [2, 3, 30941] [2, 1, 1]
      [12, 12, 12, 12, 12]
      [[6, 6, 6, 6, 6], [4, 4, 4, 4, 4], [12]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 30941 175 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

/-- `C(13, 6)` is primitive: the residue of `x` has order `13^6 - 1 = 4826808`. -/
theorem primitive_13_6 :
    Primitive 13 6 supportedEntry_13_6 [2, 3, 7, 61, 157] [3, 2, 1, 1, 1]
      [12, 12, 12, 12, 12, 12]
      [[6, 6, 6, 6, 6, 6], [4, 4, 4, 4, 4, 4], [1, 11, 1, 11, 1, 11], [2, 10, 0, 2, 10], [1, 0, 12, 11, 12]] where
  primes := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 2 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 3 1 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 7 2 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 61 7 (by decide) (by decide) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Hex.Nat.prime_of_bounded 157 12 (by decide) (by decide) (by decide)
    exact absurd hq (by simp)
  check := by decide

end Conway

end Hex
