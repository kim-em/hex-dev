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
table below `10^5`, exact trial division below `6 · 10^6`, and certificate
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

{docstring Hex.Nat.isPrime_iff}

Callers that need a real time bound use the resumable form, which
returns the advanced random state on failure instead of silently
retrying:

{docstring Hex.Nat.isPrime?}

{docstring Hex.Nat.isPrime?_spec}

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

# Reusable certificates with `primality?`
%%%
tag := "hex-primality-construction"
%%%

The explicitly requested construction tactic `primality?` uses a larger,
finite search profile. It proves the Curve25519 field prime and offers a
clickable `Try this:` replacement containing the complete checked certificate.
This example checks the entire suggestion text, so changes to the generated
certificate or its formatting are detected:

```lean
/--
info: Try this:
  [apply] exact
    Hex.Nat.prime_of_checkPrimeAt (c :=
      Hex.Nat.PrimeCert.pock 57896044618658097711785492504343953926634992332820282019728792003956564819949
        [(2, 0,
            Hex.Nat.PrimeCert.pock3 74058212732561358302231226437062788676166966415465897661863160754340907
              2028478494862525422475607 22304740449229861598212 2028478494862525422475606
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353),
                (2, 0, Hex.Nat.PrimeCert.small 57467),
                (2, 0,
                  Hex.Nat.PrimeCert.pock3 31757755568855353 4028945 289 4028944
                    [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 223),
                      (2, 0, Hex.Nat.PrimeCert.small 4153)])])])
      (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime (2 ^ 255 - 19) := by
  primality?

```

Apply the suggestion to keep certificate search out of subsequent builds. The
replacement uses {name}`Hex.Nat.prime_of_checkPrimeAt` and `decide +kernel`;
the kernel still replays the certificate. A standalone file containing the
replacement needs only `import HexPrimality.Cert`. The goal retains the
expression `2 ^ 255 - 19`. With `HexPrimalityMathlib` imported, `primality?`
also handles `Nat.Prime` and suggests the corresponding bridge theorem.

Construction supports inputs through 512 bits, recursive depth 32, and a
shared limit of 1024 attempts. `primality? (maxAttempts := 29)` sets a smaller
limit; Curve25519 succeeds at 29 and exhausts at 28. It uses
stage-one Pollard `p - 1` up to 524288, bounded rho work, and deterministic
small witnesses before random candidates. Every limit is finite; exhaustion
reports the seed, attempts, and resource profile. Success depends on finding
enough factors of predecessors for Pocklington, rather than on bit length
alone. The ordinary `primality` policy keeps its existing smaller budget.

The Curve25519 result has three non-leaf certificate nodes and eight factor
entries. Kernel replay reads the already verified sieve bitset for table
leaves, and compiled prime enumeration reads 64 candidate bits at a time.
Both changes are proved equal to their original implementations.

The fixed-corpus comparison measured Curve25519 native decision at
0.57 seconds and a fresh complete `primality?` build from its numeral at
1.63 seconds, including Lake overhead and kernel replay. Paired runs using
the original `2 ^ 255 - 19` expression took 2.17–2.29 seconds, compared with
7.01–10.41 seconds before these optimizations. FLINT and PARI native decisions
took 25.9 and 55.4 milliseconds respectively. The native timings use a
standalone executable; the full tactic currently runs search through Lean’s
interpreter before kernel checking. All completed samples are
retained. These are host-specific observations, not latency guarantees. The
[measurement report](https://github.com/kim-em/hex-dev/blob/main/reports/hex-primality-construction.md)
records every sample, certificate sizes, and the comparison with the larger
reference certificate.

The fixed comparison corpus also includes standard cryptographic field
primes. The current construction profile finds P-256 and the structured
511/512-bit benchmark primes. It exhausts on secp256k1, P-384, and Curve448;
P-521 exceeds its input ceiling. This is not a general-purpose prover for
arbitrary cryptographic-size primes.

The first cactus plot compares native exact primality decisions with the
complete `primality?` build. Native timings exclude Lean proof emission and
kernel replay, imports, and input conversion. Hex uses certificate
construction and a compiled self-check internally to decide primality;
FLINT and PARI return exact decisions through their native algorithms. The
dashed curve includes the full fresh Lake build: certificate construction,
proof emission, imports, and kernel checking.

![Native decision and complete Lean proof](https://kim-em.github.io/hex-dev/figures/hex-primality-complete-cactus.svg)

The second plot times kernel checking directly, excluding imports, search,
and proof elaboration. It checks complete proof bodies, including expanded
local auxiliary proofs. Curve25519 takes about 9.6 milliseconds for Hex and
19.2 milliseconds for PrimeCert, an observed 2.0-fold Hex advantage.
Hex is faster on five of the seven shared inputs. The 31-bit case is
effectively tied; PrimeCert is faster at 61 bits. The
[replay report](https://github.com/kim-em/hex-dev/blob/main/reports/hex-primality-windowed-replay.md)
records the windowed arithmetic and bounded-multiplication measurements.
The measurements use Hex on Lean 4.34.0 and PrimeCert on Lean 4.33.0.

The direct comparison shows both matched inputs and independently sorted
cactus curves. Missing certificates count as unsolved. The corpus is small
and structured; the report records exact inputs, versions, and every sample.

![Direct kernel certificate comparison](https://kim-em.github.io/hex-dev/figures/hex-primality-kernel-direct.svg)

# The Mathlib correspondence
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

{docstring Hex.Nat.rhoFactor?_spec}

# The prime table and initial segments
%%%
tag := "hex-primality-table"
%%%

A committed table of the 9,592 primes below `10^5` anchors the small
end: compiled membership uses binary search, while kernel replay reads a
bit from the verified final sieve state. Both lookup paths are proved equal
at every input. Both directions of correctness are proved against a
kernel-replayed sieve run (the batched
verification is regenerated, never hand-edited, via the
`#rebuild_primeTable` command).

{docstring Hex.Nat.isTablePrime}

The verified compiled sieve also provides a list of every prime strictly
below a requested bound, including the exceptional primes 2 and 3. Its
membership and strict ordering theorems are independent of the committed
table. Pollard `p - 1` and ECM use this runtime source for their stage primes:

{docstring Hex.Nat.primesBelow}

{docstring Hex.Nat.mem_primesBelow}

{docstring Hex.Nat.primesBelow_pairwise_lt}

The interval API still uses trial division, with no upper bound tied to the
table:

```lean (name := segmentEval)
#eval Hex.Nat.primesIn 0 100
```
```leanOutput segmentEval
#[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
```

{docstring Hex.Nat.primesIn}

{docstring Hex.Nat.mem_primesIn}

# Reach
%%%
tag := "hex-primality-reach"
%%%

What the certificate tier can do depends on how much of `n - 1` the
untrusted search can factor:

* The supported elaboration ceiling is 512 bits. The release probes include
  table-smooth certificates from 31 through 511 bits and a 512-bit certificate
  whose search discovers an above-table factor with bounded rho work.
* The bounded search reports exhaustion rather than claiming compositeness. A
  separate 512-bit probable-prime probe exercises this path, while a 513-bit
  input is rejected before search begins.
* Negative answers are conclusive only when a size check, table lookup, exact
  trial decision, or one of the thirteen fixed Miller-Rabin bases supplies a
  witness. Passing all fixed bases is not itself a primality result.

# Cross-references
%%%
tag := "hex-primality-cross-references"
%%%

* {ref "hex-arith"}[`HexArith`] supplies the Mathlib-free prime predicate,
  modular exponentiation, gcd, and exact trial-division foundation.
* {ref "hex-basic"}[`HexBasic`] supplies the explicit reproducible random state
  used by every bounded randomized search.
* {ref "hex-int-factor"}[`HexIntFactor`] reuses primality certificates and the
  factor-search primitives to certify complete natural-number factorizations.
