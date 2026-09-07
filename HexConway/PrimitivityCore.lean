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

Structural square-and-multiply keeps the multiplication count logarithmic
in the exponent, independently of
the characteristic. The generator searches for factorizations offline;
Pocklington certificates from `HexPrimality` prove their prime factors.

# What the check establishes, and what it does not

`primitiveCheck` validates that the supplied primes, raised to their
multiplicities, multiply to `p^n - 1`. It computes the full and prime-divided
exponents directly before checking their power residues.

The product test is what makes the prime list trustworthy, and it is worth
saying why. If the supplied `q_i` are prime and `∏ q_i ^ e_i = N`, then by
unique factorization every prime divisor of `N` occurs among the `q_i`.
Extra primes with zero multiplicity can only add power obligations. So checking `α ^ (N / q) ≠ 1` across the supplied
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
A proof helper for induction; executable certificate replay uses `powMod`. -/
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

/-- The product of `qs` raised to the matching multiplicities in `es`. -/
@[expose]
def primePowerProduct : List Nat → List Nat → Nat
  | [], _ => 1
  | _, [] => 1
  | q :: qs, e :: es => q ^ e * primePowerProduct qs es

/-- The Tier 2 primitivity check validates the factorization of `p^n - 1`
and checks the full power and each prime-divided power. Primality of the
supplied factors is carried separately by `Primitive`. -/
@[expose]
def primitiveCheck (f : FpPoly p) (hm : DensePoly.Monic f) (n : Nat)
    (qs es : List Nat) : Bool :=
  let order := p ^ n - 1
  (primePowerProduct qs es == order) &&
  (powerResidue f hm order == 1) &&
  qs.all (fun q => !(powerResidue f hm (order / q) == 1))

/--
The committed entry `C(p, n)` is primitive: the residue of `x` has
multiplicative order exactly `p^n - 1`, witnessed by the supplied
factorization and power data.
-/
structure Primitive (p n : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (h : SupportedEntry p n) (qs es : List Nat) : Prop where
  /-- The supplied divisors are prime. Together with the product check inside
  `primitiveCheck` this ensures they include every prime divisor of `p^n - 1`. -/
  primes : ∀ q ∈ qs, Hex.Nat.Prime q
  /-- The arithmetic and the two power conditions, all decidable. -/
  check : primitiveCheck (conwayPoly p n h) (conwayPoly_monic p n h) n qs es = true


end Conway
end Hex
