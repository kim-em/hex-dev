/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexIntFactor

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

-- The complete certificate contains indivisible numerals of up to 78 digits.
set_option verso.code.warnLineLength 100
set_option pp.rawOnError true

#doc (Manual) "Proving the secp256k1, P-384 and Curve448 field primes" =>
%%%
tag := "tutorial-field-primes"
%%%

The field primes for secp256k1, P-384 and Curve448 have short formulas but
hundreds of bits. Hex can discover primality certificates for all three and
prove them in Lean. You supply the number, and the tactic finds the factors
and recursively proves the smaller primality statements it needs.

# Start here
%%%
tag := "tutorial-field-primes-setup"
%%%

Use a checkout of the
[`hex-dev` repository](https://github.com/kim-em/hex-dev). The ECM provider is
part of `HexIntFactor`, which is not yet included in the published split
libraries. Start a Lean file with these imports:

```imports
import HexIntFactor
```

The examples use {name}`Hex.Nat.Prime`, so they need no Mathlib import.
To state the same goals with `Nat.Prime`, also import `HexPrimalityMathlib`.
The same tactic syntax then applies.

Put the examples in a section with local options:

```lean
section
set_option maxHeartbeats 4000000
```

The finite heartbeat allowance accommodates certificate construction. All three
examples pass with this option alone; it is a tested allowance, not a measured
minimum. It does not increase the factor search's shared 1024-attempt budget.
Lean 4.34.0 may warn that the powers with exponents 384 and 448 exceed its
shortcut threshold of 256. The goals still normalize and the proofs succeed;
these examples leave that warning visible.

# Three proofs
%%%
tag := "tutorial-field-primes-proofs"
%%%

The secp256k1 field prime is `2^256 - 2^32 - 977`:

```
example : Hex.Nat.Prime (2 ^ 256 - 2 ^ 32 - 977) := by
  primality?
```

The P-384 field prime is `2^384 - 2^128 - 2^96 + 2^32 - 1`:

```
example : Hex.Nat.Prime
    (2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1) := by
  primality?
```

The Curve448 field prime is `2^448 - 2^224 - 1`:

```
example : Hex.Nat.Prime (2 ^ 448 - 2 ^ 224 - 1) := by
  primality?
```

Close the section after the examples:

```lean
end
```

Each proof produces a `Try this:` suggestion containing a complete
certificate. Apply the suggestion to replace the search with a proof that
replays that certificate. This is particularly useful when sharing a file:
other people can check the proof without repeating the factor search.

The standard import makes bounded ECM available automatically. Construction
first tries HexPrimality's own methods. If they exhaust with attempts left,
it retries with ECM, carrying forward the random state and charging both
routes to the same allowance. P-521 and Curve25519 finish on the first route.
You do not need to supply factors, curve parameters, seeds or certificates.
The expert override `primality? (factor := Hex.Nat.ecmFactorSearch)` selects
that provider directly and bypasses automatic selection.

If Lean reports a heartbeat limit, include the local option from the setup.
A message saying that certificate construction exhausted its attempts instead
refers to the factor search budget and identifies the unresolved subject.
The {ref "hex-int-factor-search"}[factor-search reference] describes the
optional bounds, curve count and tracing arguments.

Build note: the three construction examples and their exact `Try this:`
suggestions are checked in
[the field construction tests](https://github.com/kim-em/hex-dev/blob/main/conformance/HexIntFactor/FieldConstruction.lean).
Run `lake build HexIntFactorFieldConformance` to check them together.
The manual build checks the saved proof below without repeating the searches.

# What the saved proof looks like
%%%
tag := "tutorial-field-primes-replay"
%%%

Here is a saved secp256k1 certificate in full, with abbreviated constructor
names. This standalone proof needs only `import HexPrimality.Cert` and uses the
numeral to avoid the options for normalizing powers:

```lean
example : Hex.Nat.Prime
    115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  exact Hex.Nat.prime_of_checkPrimeAt (c :=
    .pock 115792089237316195423570985008687907853269984665640564039457584007908834671663
      [(2, 0,
        .pock 205115282021455665897114700593932402728804164701536103180137503955397371
          [(2, 0,
            .pock3 255515944373312847190720520512484175977
              185873736969223 6447496504 185873736969222
              [(3, 2, .small 2), (2, 0, .small 4423),
                (2, 0, .small 41201), (2, 0, .small 96557)])])])
    (by decide +kernel)
```

The kernel checks the certificate through
{name}`Hex.Nat.prime_of_checkPrimeAt`. The search is untrusted: finding a
factor is not enough to establish primality, and every necessary recursive
certificate must pass the same checker. The
[complete saved certificates](https://github.com/kim-em/hex-dev/blob/main/conformance/HexIntFactor/FieldReplay.lean)
also include P-384 and Curve448.

# How long does it take?
%%%
tag := "tutorial-field-primes-cost"
%%%

Allow a few minutes to try all three searches in Lean. The tactic runs
search through Lean's interpreter, so compiled search timings alone do not
predict the time spent in the editor.

The recorded shared-host experiments measured compiled construction at
18–19 seconds for secp256k1, 37–39 seconds for P-384, and 24–25 seconds for
Curve448. Direct kernel replay of the saved proofs took about 4–15
milliseconds per proof, excluding imports and elaboration. These are
host-specific observations, not time limits or guarantees. See the
[ECM construction report](https://github.com/kim-em/hex-dev/blob/main/reports/hex-primality-ecm-stage2.md)
for separate construction, rendering and kernel measurements.

The search has a fixed, bounded schedule and can still exhaust on other
primes. The
{ref "hex-primality-construction"}[primality construction reference]
explains reusable certificates and the available budget override.
