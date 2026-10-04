/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexIntFactor
import HexIntFactorMathlib
import HexIntFactor.Frozen.Case3
import HexIntFactor.Frozen.Case5
import HexIntFactor.Mixed.Frozen.Small
import HexIntFactorMathlib.Mixed

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

The bounded ECM provider {name}`Hex.Nat.ecmFactorSearch` constructs primality
certificates for the secp256k1, P-384 and Curve448 field primes. See
{ref "tutorial-field-primes"}[the field-prime tutorial] for the three proofs
and instructions for saving the generated certificates.

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

After `import HexIntFactor`, plain `primality?` first uses HexPrimality's
construction route, then retries with {name}`Hex.Nat.ecmConstructionFactor`
only on exhaustion with attempts left. This provider uses
{name}`Hex.Nat.ecmFactorSearch`, which tries core factoring before bounded
ECM stages 1 and 2. Explicit `factor :=` syntax selects a provider directly:

{docstring Hex.Nat.ecmFactorSearch}

Its defaults are `b₁ = 32768`, `b₂ = 524288`, and `curves = 64`.
ECM attempts with stage bounds above 524288 and 4194304 respectively decline
without work, and the curve count is capped at 64. Set `trace := true` to display curve
outcomes. The tactic's `maxAttempts` allowance is shared across factor search,
recursive certificates and witnesses. A stage-1 attempt and a stage-2
continuation each consume one attempt. For example,
`primality? (factor := Hex.Nat.ecmFactorSearch (curves := 16))`
uses fewer curves, which may exhaust on inputs supported by the default
64-curve provider.

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

# Optional external production and frozen replay
%%%
tag := "hex-int-factor-external"
%%%

The pure {name}`Hex.Nat.importFactors` API accepts signed integer
factor/multiplicity proposals for an explicitly requested subject. It validates
products before sorting and merging duplicates. Missing factors and uncertified
bases remain in a checked residual. Supplied certificates are checked; labels
such as “probable prime” are never evidence.

```lean
open Hex Hex.Nat

namespace HexIntFactorChapter

def completeImport : Bool := match importFactors {} 72
    ⟨72, [(3, 2, none), (2, 3, none)]⟩ (Rand.ofSeed 72) with
  | .ok result => result.value.raw.residual == 1 &&
      result.value.raw.factors.map
        (fun e => (e.prime, e.exponent)) == [(2, 3), (3, 2)]
  | .error _ => false

def partialImport : Bool := match importFactors
    { completion := { maxAttempts := 0 } } 12
    ⟨12, [(2, 2, some (.small 2)), (3, 1, none)]⟩
    (Rand.ofSeed 12) with
  | .ok result => result.value.raw.residual == 3 &&
      checkPartial result.value.raw
  | .error _ => false

#guard completeImport
#guard partialImport

end HexIntFactorChapter
```

Install PARI/GP separately to opt into production. A batch source file importing
`HexIntFactor.Export` can contain `#int_factor for 72`, or
`#int_factor_export MyFactors.Product cert for 72` to exclusively create
`MyFactors/Product.lean`. Run `lake build +YourModule`, then remove the
production command. Set the environment variable `HEX_INT_FACTOR_GP` to select
an executable. The language server gives batch instructions and performs no
production or file writing. Ordinary native APIs use no external process.

Generated modules publicly import only `HexIntFactor.Replay` and expose both
raw data and a subject-indexed checked value. These committed examples build
without GP or any factor search:

```lean
open Hex.Nat

example : CheckedFactorization
    (926510094425921 * 1363620137403810529 *
      2305843009213693951 * 18446744069414584321) :=
  Hex.IntFactorFrozen.case3_checked

example : CheckedPartialFactorization (2 ^ 255 - 19) :=
  Hex.IntFactorFrozen.case5_checked
```

The first subject has a complete checked result even though the recorded native
worklist allocation of four exhausts. For the second, GP discovers the base but
native primality completion exhausts its 128-attempt allocation. Its frozen
residual therefore carries no primality claim. Discovery and certification have
separate allocations and diagnostics.

The initial producer supports POSIX platforms, subjects through 256 bits,
64 entries, 78 digits per number, exponents through 256, a 30-second process
limit, and bounded output. Import also bounds certificate syntax and depth.
Missing GP or rejected proposals trigger a separate finite native fallback;
certified partial progress and backend diagnostics survive. Larger inputs may
exhaust either discovery or certificate completion; there is no blanket promise
of 60-digit factorization. Source generation is capped at 262144 bytes. The
capability report records discovery, parsing, completion, checking, source size,
and fresh-module replay separately.

# Opt-in SQUFOF
%%%
tag := "hex-int-factor-squfof"
%%%

Both {name}`Hex.Nat.factor?` and {name}`Hex.Nat.factorPartial?` accept
`squfof := .first limits` to try deterministic bounded SQUFOF before rho.
Structural reductions and composite filtering run first. The policy applies
to recursive cofactors and nested certificate search. On bounded SQUFOF
failure, the existing rho, p−1, and ECM routes remain available.
`squfof := .rescue limits` instead runs SQUFOF after those routes fail.
The default is `.off`.

This 56-bit example has factors differing by about 19%. The result is a
complete checked factorization, ready for consumers such as
{name}`Hex.Nat.totient`:

```lean (name := squfofComplete)
open Hex Hex.Nat

set_option maxRecDepth 100000 in
#eval (factor? 40249308338448479
  (Rand.ofSeed 40249308338448479)
  (squfof := .first
    { multipliers := 2, steps := 65536 })).map
    fun (F, _) =>
      (F.raw.factors.map (fun (e : PrimePower) =>
        (e.prime, e.exponent)), totient F)
```
```leanOutput squfofComplete
Except.ok ([(184185251, 1), (218526229, 1)], 40249307935737000)
```

The close 64-bit pair is a deliberately favorable case and needs only a
small recurrence cap:

```lean (name := squfofComplete64)
open Hex Hex.Nat

set_option maxRecDepth 100000 in
#eval (factor? 16212959431627901207
  (Rand.ofSeed 16212959431627901207)
  (squfof := .first
    { multipliers := 1, steps := 128 })).map
    fun (F, _) => F.raw.factors.map
      (fun (e : PrimePower) => (e.prime, e.exponent))
```
```leanOutput squfofComplete64
Except.ok [(4026531853, 1), (4026532019, 1)]
```

On the shared measurement host, eight adjacent paired trials measured
median complete-factorization times of 8.71 ms with the default portfolio
and 1.40 ms with this policy. For the close 64-bit pair in
{ref "hex-primality-squfof"}[the splitting example], the complete times were
20.69 ms and 2.25 ms using one multiplier with 128 steps. These measurements
include prime-certificate construction and checked acceptance; they describe
these selected examples rather than a general speed guarantee.

Small factors just above the trial table can favor rho strongly, even when
the product is large. Input bit length does not reveal factor balance, so
SQUFOF is explicitly selected rather than enabled automatically. Limits
bound multiplier attempts, combined recurrence steps per multiplier, and
queue capacity. A zero multiplier or step limit does no SQUFOF work. The
counted API retains route diagnostics and charges every started multiplier,
while SQUFOF itself leaves the random state unchanged.

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
the Carmichael value of each certified prime power. Its correctness is stated
both as a power law and as the divisibility bound on every multiplicative
order.

{docstring Hex.Nat.carmichael}

{docstring Hex.Nat.pow_carmichael}

{docstring Hex.Nat.orderOf_dvd_carmichael}

# The Mathlib correspondence
%%%
tag := "hex-int-factor-mathlib"
%%%

`HexIntFactorMathlib` neither searches for factors
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

# Optional mixed primality evidence
%%%
tag := "hex-int-factor-mixed"
%%%

The explicit `HexIntFactor.Mixed.Replay` extension accepts both legacy
`PrimeCert` and ECPP evidence, bound to each proposed base and the caller's
subject. Its product, order and positive-exponent facts are computational.
Its primality and prime-support theorems take an explicit ECPP soundness
hypothesis. Import `HexIntFactorMathlib.Mixed` to discharge that hypothesis
with the existing ECPP soundness theorem and obtain unconditional
`Nat.factorization` correspondence.

{docstring Hex.Nat.Mixed.checkEvidence}

{docstring Hex.Nat.Mixed.CheckedFactorization.factorization_eq}

{docstring Hex.Nat.Mixed.CheckedPartialFactorization.factorization_eq}

A partial residual can contain further powers of a listed prime. The partial
correspondence adds the residual's factorization; listed exponents are lower
bounds and become exact when the corresponding prime does not divide the residual.

```lean
namespace HexIntFactorMixedChapter

open Hex.Nat.Mixed

example : Hex.Nat.Mixed.CheckedFactorization 34 :=
  Frozen.small_checked
example :
    Hex.Nat.Mixed.CheckedPartialFactorization 578 :=
  Frozen.partialOverlap_checked

#guard checkAt 34 Frozen.small
#guard !checkAt 35 Frozen.small
#guard checkPartialAt 578 Frozen.partialOverlap
#guard Frozen.partialOverlap.residual == 17

example (p : Nat) : (34 : Nat).factorization p =
    (Frozen.small.factors.find?
      fun e => e.prime == p).elim 0 (·.exponent) :=
  Frozen.small_checked.factorization_eq p

example (p : Nat) : (578 : Nat).factorization p =
    (Frozen.partialOverlap.factors.find?
      fun e => e.prime == p).elim 0 (·.exponent) +
      Frozen.partialOverlap.residual.factorization p :=
  Frozen.partialOverlap_checked.factorization_eq p

end HexIntFactorMixedChapter
```

`HexIntFactor.Mixed.Import` adds pure supplied-proposal import. ECPP completion
is off by default. Select `ecppBits := some 256` or `some 512` to try the native
producer after bounded legacy completion. Defaults admit a 4096-bit subject,
512-bit bases, 64 entries and exponents through 4096. Legacy completion has
128 attempts per base and 8192 shared attempts; ECPP reserves at most two
independent public-policy calls. Failed calls are charged. ECPP seeds use
`ecppSeed + callIndex` independently of legacy randomness. The result retains
both histories and useful checked partial progress.

For batch suggestions, import `HexIntFactor.Mixed.Export` and write
`#int_factor_mixed (ecpp := 512) for 34 using proposal`. The optional
`(method := pari)` variant obtains arithmetic proposals from the existing
256-bit process route. Pure completion calls no subprocess. Supplied data must
be closed, exposed constructor data; the batch subject must be a numeral or
an exposed numeral alias. `#int_factor_mixed_export MyFactors.Mixed cert for 34
using proposal` exclusively creates public replay data after a fresh kernel
check. Both commands are gated out of editor execution. Frozen replay imports
neither Mathlib nor search.

Supplied ECPP data admits 20 rows, 32 constructor nodes including terminal
legacy evidence, and 1024 inverses per row. Batch admission also bounds expanded
syntax, source size, reification and kernel replay. The frozen acceptance report
records two mixed complete products of 513 and 514 bits where the legacy route
exhausts, plus a checked partial result after native ECPP exhaustion.

Legacy divisor, totient, order and square-decomposition APIs still take the
legacy representation. `ofLegacy` embeds it into mixed data; checked `toLegacy`
replays legacy acceptance and succeeds only when every entry carries legacy
evidence. ECPP entries require an explicit arithmetic API extension.
