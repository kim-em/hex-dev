/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexIntFactor
import HexIntFactorMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexIntFactor: certified integer factorization" =>
%%%
tag := "hex-int-factor"
%%%

# Introduction
%%%
tag := "hex-int-factor-intro"
%%%

`HexIntFactor` factors natural numbers and turns the result into divisor,
square-decomposition, multiplicative-order, and primitive-root data. Search is
an explicitly bounded, untrusted producer. Its results become theorem inputs
only after a small Boolean checker has replayed every prime certificate and
the complete prime-power product.

The executable library is Mathlib-free. It depends on `HexPrimality` for
kernel-replayable primality certificates and modular-order infrastructure,
and on `HexArith` and `HexBasic` for bounded arithmetic and explicit random
state. The companion `HexIntFactorMathlib` proves correspondence with
Mathlib's factorization, divisor, squarefree, and `ZMod` order APIs.

# Complete certificates
%%%
tag := "hex-int-factor-certificates"
%%%

A {name}`Hex.Nat.PrimePower` stores an exponent and a
`HexPrimality` certificate. Its base is the subject of that certificate, so
the two cannot disagree. A {name}`Hex.Nat.Factorization` is raw data: its
subject and factor list are trusted only after replay.

{docstring Hex.Nat.PrimePower.prime}

{docstring Hex.Nat.checkFactorization}

{name}`Hex.Nat.CheckedFactorization` ties accepted raw data to the subject
requested by its caller. The checker requires a positive subject, positive
exponents, strictly ascending prime bases, successful primality replay, and an
exact product. Product accumulation is bounded by the claimed subject, so an
attacker-chosen exponent cannot first construct an arbitrarily large power.

The checked facts are exposed as characterizing theorems rather than requiring
callers to unfold the checker:

{docstring Hex.Nat.checkFactorization_prod}

{docstring Hex.Nat.checkFactorization_prime}

{docstring Hex.Nat.checkFactorization_primeSupport}

{docstring Hex.Nat.checkFactorization_multiplicity}

The support theorem is complete because the checker proves both the product
identity and primality of every listed base. Strict ordering additionally
makes the representation canonical and makes each recorded exponent the exact
multiplicity.

# Checked arithmetic from a factorization
%%%
tag := "hex-int-factor-arithmetic"
%%%

Once a factorization is checked, divisor enumeration and the usual arithmetic
functions require no further search. Divisors are returned in ascending order;
the count and generalized divisor sum use prime-power product formulas rather
than enumerating the entire list.

{docstring Hex.Nat.divisors}

{docstring Hex.Nat.numDivisors}

{docstring Hex.Nat.sigma}

{docstring Hex.Nat.totient}

{docstring Hex.Nat.radical}

The square decomposition writes the subject as a squarefree factor times the
square of a greatest possible divisor.

{docstring Hex.Nat.squarefreePart}

{docstring Hex.Nat.squareDivisor}

{docstring Hex.Nat.squarefreePart_mul_square}

{docstring Hex.Nat.squareDivisor_spec}

# Worked example
%%%
tag := "hex-int-factor-example"
%%%

The following block is elaborated with the manual. The certificate for
`12 = 2² · 3` uses the small-prime certificates supplied by
`HexPrimality`; ordinary kernel reduction checks the factorization before any
arithmetic consumer can use it.

```lean
open Hex Hex.Nat

namespace HexIntFactorChapter

set_option maxRecDepth 100000

def twelve : CheckedFactorization 12 :=
  ⟨⟨12, [⟨2, .small 2⟩, ⟨1, .small 3⟩]⟩,
    rfl, by decide⟩

#guard checkFactorization twelve.raw
#guard divisors twelve == #[1, 2, 3, 4, 6, 12]
#guard sigma twelve 1 == 28
#guard totient twelve == 4
#guard radical twelve == 6
#guard squarefreePart twelve == 3
#guard squareDivisor twelve == 2

end HexIntFactorChapter
```

# Search, fuel, and failure
%%%
tag := "hex-int-factor-search"
%%%

{docstring Hex.Nat.factor?}

`factor?` first applies structural reductions and table trial division, then
uses primality search, Brent rho, Pollard `p − 1`, and stage-one ECM as the
input requires. Its `Hex.Rand` argument and returned random state make every
random draw explicit. The default fuel scales with bit length but does not
claim to make a partial search total.

{docstring Hex.Nat.defaultFuel}

The {name}`Hex.Nat.FactorStop` cases distinguish zero, ordinary exhaustion,
and rejection of a producer's output by a checker. A
{name}`Hex.Nat.FactorFailure` retains exact attempt accounting, the advanced
random state, and either the last checked partial snapshot or the rejected raw
candidate. This makes retry policy observable without treating exhaustion as
a false mathematical result.

{docstring Hex.Nat.factorPartial?}

{docstring Hex.Nat.checkPartial}

{docstring Hex.Nat.checkPartial_prod}

A partial factorization certifies every listed prime power and the exact
residual product, but makes no primality claim about the residual. Residual
one promotes directly to a complete certificate without replaying the entire
checker:

{docstring Hex.Nat.checkFactorization_of_checkPartial}

Specialized entry points expose the split routes for callers that need route
control or diagnostics. `factorPower?` adds a checked cyclotomic pre-split for
numbers of the form `b ^ n − 1` or `b ^ n + 1`; failed subproblems may fall
back to generic search, while checker rejection is propagated.

# Orders, primitive roots, and Carmichael exponents
%%%
tag := "hex-int-factor-orders"
%%%

An {name}`Hex.Nat.OrderCert` claims that a residue has a specified least
positive order. Its factorization field must be a complete checked
factorization of that order. The checker verifies the full power is one and
that removing each distinct prime divisor from the exponent is not.

{docstring Hex.Nat.checkOrder}

{docstring Hex.Nat.checkOrder_iff}

{docstring Hex.Nat.order_eq_of_checkOrder}

For a certified prime `p`, {name}`Hex.Nat.isPrimitiveRoot` specializes this
criterion to order `p − 1`; {name}`Hex.Nat.primitiveRoot?` performs a
fuel-bounded ascending search and returns the checked order certificate with
the generator.

{docstring Hex.Nat.isPrimitiveRoot_iff}

{docstring Hex.Nat.primitiveRoot?_spec}

The Carmichael exponent is computed by taking the least common multiple of
the prime-power exponents. Its correctness is stated both as a power law and
as the divisibility bound on every multiplicative order.

{docstring Hex.Nat.carmichael}

{docstring Hex.Nat.pow_carmichael}

{docstring Hex.Nat.orderOf_dvd_carmichael}

# The Mathlib correspondence
%%%
tag := "hex-int-factor-mathlib"
%%%

`HexIntFactorMathlib` is correspondence-only: it neither searches for factors
nor replays certificates. It identifies values already computed and checked
by `HexIntFactor` with Mathlib's canonical definitions.

{docstring Hex.Nat.CheckedFactorization.factorization_eq}

{docstring Hex.Nat.CheckedFactorization.primeFactorsList_eq}

{docstring Hex.Nat.divisors_eq}

{docstring Hex.Nat.totient_eq}

{docstring Hex.Nat.isSquarefree_iff_squarefree}

For modular orders, the bridge first identifies the Mathlib-free natural
order with the order of the corresponding unit in `ZMod n`, then specializes
that equality to accepted order certificates.

{docstring Hex.Nat.orderOf_unitOfCoprime}

{docstring Hex.Nat.orderOf_eq}

# Cross-references
%%%
tag := "hex-int-factor-cross-references"
%%%

* {ref "hex-primality"}[`HexPrimality`] supplies the primality certificates,
  order computation, and shared rho and `p − 1` primitives.
* {ref "hex-arith"}[`HexArith`] supplies bounded powers, modular arithmetic,
  primality foundations, and exact gcd infrastructure.
* `HexConway` can consume complete prime support for multiplicative-group
  orders when its committed table grows beyond hand-maintained
  factorizations.
