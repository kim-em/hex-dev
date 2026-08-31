/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPrimality
import HexPrimalityMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPrimality: certified primality at scale" =>
%%%
tag := "hex-primality"
%%%

# Introduction
%%%
tag := "hex-primality-intro"
%%%

`HexPrimality` decides primality far past trial division and proves its
positive answers in the kernel. The engine is the Pocklington
certificate: an untrusted, randomized search factors `n - 1`, assembles
a certificate, and the kernel replays a Boolean checker on that
certificate by reduction alone. Nothing about the search — randomness,
fuel, Pollard rho — appears in the proof term.

The library is Mathlib-free and states its results for the
project-local {name}`Hex.Nat.Prime` predicate. The companion library
`HexPrimalityMathlib` transports everything to Mathlib's `Nat.Prime`,
extends the `primality` tactic to goals stated with it, and registers
an explicitly opted-in `norm_num` policy.

# Deciding primality
%%%
tag := "hex-primality-decide"
%%%

{name}`Hex.Nat.isPrime` is the total convenience decision: the committed
table below `10^4`, exact trial division below `10^8`, and certificate
search above.

```lean (name := isPrimeEval)
#eval Hex.Nat.isPrime 1945555039024054273  -- 27 · 2^56 + 1
```
```leanOutput isPrimeEval
true
```

```lean (name := isPrimeCarmichael)
#eval Hex.Nat.isPrime 561  -- a Carmichael number
```
```leanOutput isPrimeCarmichael
false
```

{docstring Hex.Nat.isPrime}

Callers that need a real time bound use the resumable form, which
returns the advanced random state on failure instead of silently
retrying:

{docstring Hex.Nat.isPrime?}

Compositeness is filtered by Miller-Rabin before any certificate work
begins. The test is deliberately not exposed to proofs — it appears
in no proof term — but it is available as a runtime filter:

{docstring Hex.Nat.isProbablePrime}

# The `primality` tactic
%%%
tag := "hex-primality-tactic"
%%%

The bare tactic closes a {name}`Hex.Nat.Prime` goal on a numeral; the
search runs compiled at elaboration time and the kernel replays only
the certificate check:

```lean
example : Hex.Nat.Prime 2147483647 := by primality
```

It is also a term elaborator, and with an explicit numeral in tactic
mode it adds a hypothesis (`this`, or a chosen name):

```lean
example : Hex.Nat.Prime 2147483647 := primality 2147483647

example : True := by
  primality 65537
  primality fermat : 257
  exact trivial
```

On a composite input the tactic fails with the witness that refutes
primality:

```lean +error (name := primalityComposite)
example : Hex.Nat.Prime 561 := primality 561
```
```leanOutput primalityComposite
primality: 561 is not prime (Miller-Rabin witness 2)
```

# `Nat.Prime`, `norm_num`, and the companion
%%%
tag := "hex-primality-mathlib"
%%%

The two predicates agree, and the companion registers a handler on the
same syntax kind, so the tactic closes Mathlib-stated goals directly:

```lean
example : Nat.Prime 2147483647 := by primality
```

{docstring Hex.Nat.prime_iff}

An ordinary import leaves Mathlib's `Nat.Prime` `norm_num` behavior
unchanged: its trial-division extension registered before Hex's and is
therefore consulted first. A module that wants the supported Hex policy
opts in explicitly. Numerals below `2^24` then use a guarded trial-division
alias, while 25-bit and larger numerals use bounded certificate search:

```lean
use_hex_primality_norm_num

example : Nat.Prime 2147483647 := by norm_num
example : ¬ Nat.Prime 2147483649 := by norm_num
example : Nat.Prime 101 := by norm_num
```

The choice is per-module and does not persist across imports. If bounded
certificate or factor search exhausts above the threshold, the Hex policy
fails rather than falling back to a large trial-division computation.

# Certificates
%%%
tag := "hex-primality-certs"
%%%

The tactic is a convenience wrapper; the underlying objects are public.
A certificate is plain data, and the checker is one structural Boolean
function, so certificates can be built by hand, stored, or produced by
an external tool and replayed later. Each Pocklington factor list must be in
strictly ascending order of the child certificates' subjects:

{docstring Hex.Nat.PrimeCert}

{docstring Hex.Nat.checkPrime}

```lean (name := certReplay)
def certM31 : Hex.Nat.PrimeCert :=
  .pock 2147483647
    [(1745337962, 0, .small 2), (1371693800, 1, .small 3),
     (1615909500, 0, .small 7), (447824900, 0, .small 11),
     (505209180, 0, .small 31), (1783259301, 0, .small 151),
     (904659249, 0, .small 331)]

theorem certM31_replays :
    Hex.Nat.checkPrime certM31 = true := by
  decide +kernel
```

Soundness turns a successful replay into primality of the certificate's
subject; the tactic emits exactly this composition:

{docstring Hex.Nat.prime_of_checkPrimeAt}

The certificate search itself is available as a runtime function
returning a {name}`Hex.Nat.CheckedPrimeCert`, a certificate bundled
with the proof that it is about the requested number:

{docstring Hex.Nat.primeCert?}

The search factors `n - 1` with trial division against the table
followed by Brent's variant of Pollard rho; the rho primitive is public,
reused by hex-int-factor, and validates every factor it returns:

{docstring Hex.Nat.rhoFactor?}

# The prime table and initial segments
%%%
tag := "hex-primality-table"
%%%

A committed table of the 1229 primes below `10^4` anchors the small
end: membership is binary search, and both directions of correctness
are proved against a kernel-replayed sieve run (the batched
verification is regenerated, never hand-edited, via the
`#rebuild_primeTable` command).

{docstring Hex.Nat.isTablePrime}

Arbitrary initial segments come from trial division, with no upper
bound tied to the table:

```lean (name := segmentEval)
#eval Hex.Nat.primesIn 0 100
```
```leanOutput segmentEval
#[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
```

{docstring Hex.Nat.primesIn}

# Reach
%%%
tag := "hex-primality-reach"
%%%

What the certificate tier can do depends on how much of `n - 1` the
untrusted search can factor:

* Inputs whose `n - 1` is smooth or nearly so — Proth and Fermat
  numbers, `k · 2^m + 1` generally — certify in milliseconds at
  hundreds of bits, and kernel replay of a 511-bit certificate takes
  about a second.
* Random primes certify reliably to roughly 192 bits with the default
  fuel; past 256 bits the rho factorization of `n - 1` dominates and
  the search becomes hit-or-miss.
* Negative answers are cheap whenever one of the thirteen fixed
  Miller-Rabin bases refutes primality, which covers essentially every
  composite in practice; a composite that survived all of them would
  fall through to certificate search and fail slowly.
