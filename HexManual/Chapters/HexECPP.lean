/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexECPP
import HexECPPTheory
import HexECPPTheory.Native
import HexECPPTheory.Pari

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexECPP: proving primality with elliptic curves" =>
%%%
tag := "hex-ecpp"
file := "HexECPP___-bounded-elliptic-curve-certificates"
%%%

# Introduction

How can we prove that a large integer is prime without trying every
possible divisor? *Elliptic curve primality proving*, or *ECPP*, uses
arithmetic on elliptic curves to build such a proof. Hex can search for
these proofs and turn them into Lean theorems of the form `Nat.Prime n`.
You can also save a proof's mathematical data and check it again in a
later build, without repeating the search.

The idea is to find a curve and a point whose order is a sufficiently
large prime `q`. If the integer `n` we want to prove prime were composite,
it would have a prime divisor `p ≤ √n`. Reducing the curve and point
modulo `p` would force the curve to have too many points over the finite
field with `p` elements, contradicting Hasse's bound. The primality of
`q` is proved in turn, giving a chain that ends with primes we can check
by simpler methods.

Factorization enters when searching for a suitable `q`: we partially
factor a proposed curve order and look for a large prime factor. This
gives ECPP a choice of auxiliary integers to factor, from different
curves. It complements the Pocklington method in
{ref "hex-primality"}[HexPrimality], which uses factors of `n - 1`.

A *primality certificate* is the finite collection of curves, points,
auxiliary prime certificates and modular arithmetic witnesses needed
to verify the argument. Finding a certificate may be difficult; checking
one does not require repeating that search. Hex provides a built-in
search and an optional connection to PARI/GP. Both produce certificates
that Lean checks before accepting a primality theorem.

For Mathlib users, the main entry points are:

:::table +header
* * Import
  * What it provides
* * `HexECPPTheory`
  * Proofs from previously supplied certificates.
* * `HexECPPTheory.Native`
  * Built-in search for a certificate, followed by a proof.
* * `HexECPPTheory.Pari`
  * Certificate search using the external PARI/GP program,
    followed by a proof.
:::

The computational library `HexECPP` supplies the certificate checker
and built-in search without importing Mathlib. Its companion
`HexECPPTheory` connects the calculation to Mathlib's elliptic curves
and supplies the theorem that accepted certificates prove primality.

# Proving primality in Lean

Import `HexECPPTheory.Native` to ask Hex to find a certificate. The
following example proves a 128-bit integer prime, using only the integer
and a seed for the search:

```lean
example : Nat.Prime
    177080666831933235355717939809840315427 := by
  primality? (method := ecpp) (seed := 0)
```

The tactic closes the goal and offers a `Try this:` replacement containing
the certificate it found. Apply that suggestion to save the certificate
in your proof. Subsequent builds then check the saved data instead of
searching for it again.

Here is the same workflow for 17, small enough that we can display the
whole suggestion:

```lean (name := nativeSeventeen)
example : Nat.Prime 17 := by
  primality? (method := ecpp)
```

```leanOutput nativeSeventeen (whitespace := Lean.Elab.Tactic.GuardMsgs.WhitespaceMode.lax)
Try this:
  [apply] ecpp using
    (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
```

```lean -show
/-- info: Try this:
  [apply] ecpp using
    (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
-/
#guard_msgs (whitespace := lax) in
example : Nat.Prime 17 := by
  primality? (method := ecpp)
```

The replacement is a complete proof:

```lean
example : Nat.Prime 17 := by
  ecpp using (ecpp_cert% "17" using (.small 17))
```

This small example uses a direct small-prime certificate. Larger examples
can contain elliptic curve steps, as we will see below. A file using the
saved replacement only needs `import HexECPPTheory`; neither the
optional search import nor an external program is needed to check it.

Search is requested explicitly with `(method := ecpp)`. Importing the
library does not change what ordinary `primality` or `norm_num` does.
The integer in the goal must be a closed expression that Lean can
reduce to a numeral, such as a literal or `2 ^ 127 - 1`.

# Why elliptic curves prove primality

Suppose `n > 3` is coprime to 6. Choose coefficients for a short
Weierstrass equation

`E : y² = x³ + a x + b`,

and do arithmetic modulo `n`. Require `4a³ + 27b²` to be invertible
modulo `n`. This ensures that for every prime divisor `p` of `n`,
reducing the equation modulo `p` gives a nonsingular elliptic curve
over the field `𝔽_p`.

Next find a finite point `Q` and a prime `q < n` such that scalar
multiplication gives `q • Q = O`, where `O` is the point at infinity.
Every division used in this calculation must have a verified inverse
modulo `n`. The calculation therefore remains valid after reduction
modulo every prime divisor `p` of `n`.

The reduced point is finite, so it is not the identity. Since `q` is
prime, its order is exactly `q`. Consequently,

`q ≤ #E(𝔽_p) ≤ (√p + 1)²`.

The second inequality is Hasse's bound. We use Chris Birkbeck's
formal proof in [AINTLIB](https://github.com/CBirkbeck/AINTLIB/blob/ab1451487da02cd4483d0e2cdb2cc9e44bbbac17/projects/HasseWeil/HasseWeil/HasseBound.lean),
imported as {name}`HasseWeil.WeilPairing.hasse_bound`.
If we also require

`q > (n^(1/4) + 1)²`,

there can be no prime divisor `p ≤ √n`: such a divisor would give
`(√p + 1)² ≤ (n^(1/4) + 1)² < q`, a contradiction.
Every composite integer greater than 1 has a prime divisor at most its
square root, so `n` must be prime.

We do not assume that `n` is prime in order to use an elliptic curve
group over `𝔽_p`. The argument takes place over fields associated with
the prime divisors of `n`. This is what lets the method prove primality.

The certificate includes a proof certificate for the smaller prime
`q`. That certificate may use another elliptic curve, or one of
HexPrimality's small-prime or Pocklington certificates. Repeating this
construction produces a finite proof of the original integer's
primality.

## Finding the curve and point

Hex's search uses *complex multiplication* to propose curves with
useful orders. Here this means using a fixed collection of special
elliptic curves for which number-theoretic calculations suggest the
number of points. We partially factor a proposed order `m = s q`,
find a point `P`, and try `Q = s • P` as a point of order `q`.
The search then tries to prove `q` prime recursively.

These proposed orders guide the search; they are not mathematical
assumptions in the final proof. The checker directly verifies the
curve, point and equation `q • Q = O` needed for the Hasse argument.
Understanding complex multiplication is therefore unnecessary for
using or checking a saved certificate.

# What a primality certificate contains

The type {name}`Hex.ECPP.Cert` represents either a certificate from
HexPrimality or an elliptic curve step with a certificate for its
auxiliary prime. Here is a complete elliptic curve certificate for 17:

```lean
namespace HexECPPChapter

def certificate : Hex.ECPP.Cert :=
  .step 17 2 3 3 6 6 [10, 13, 3, 13]
    (.base (.small 11))

example : Nat.Prime 17 := by ecpp using certificate
```

The curve is `y² = x³ + 2x + 3` modulo 17, and the point is
`Q = (3, 6)`. The smaller prime is 11, certified by `.small 11`.
The final 6 before the list is an inverse of `4 · 2³ + 27 · 3²`
modulo 17. The list contains the inverses used in calculating `11 • Q`.
The checker verifies each inverse and that the calculation ends at
infinity. No claimed curve order needs to be included.

An inverse is supplied as a witness so that checking a division needs
only a modular multiplication: to justify dividing by `d`, we supply
`u` and check `d u = 1` modulo `n`. This matters while primality is
still unknown, since division by an arbitrary nonzero residue modulo
a composite integer is not valid.

The `ecpp using` tactic reads the certificate's constructor data,
checks that it is for the integer in the goal, and
produces a proof using the soundness theorem. A stored certificate
must consist of data, with no uncomputed search calls or local
hypotheses.

## Checking a certificate as a computation

The computational checker can also be called directly:

```lean
#guard Hex.ECPP.checkAt 17 certificate
#guard !Hex.ECPP.checkAt 19 certificate
```

The first check accepts the certificate for 17. The second rejects it
because this certificate says nothing about the primality of 19.
The certificate itself records the integer whose primality it proves.

{docstring Hex.ECPP.check}
{docstring Hex.ECPP.checkAt}

Each elliptic step verifies the curve equation, nonsingularity,
the size of the auxiliary prime, and every addition in the scalar
calculation. It also checks the auxiliary prime's certificate.
Coordinates and inverse witnesses must be residues between 0 and
`n - 1`, and the calculation must use exactly the supplied inverses.

The real-valued size condition above is implemented with exact integer
inequalities. With `r = q - 1`, the checker requires
`n < r²` and `16 n q < (r² - n)²`. These are equivalent to the stated
size condition for `q ≥ 2`; equality is not enough for this argument.

{docstring Hex.ECPP.sizeBound}

# Saving and reusing a proof

Writing out every modular inverse soon becomes inconvenient.
`ecpp_cert%` gives a shorter representation of the same mathematical
data. For the certificate above:

```lean
example : Nat.Prime 17 := by
  ecpp using
    (ecpp_cert% "[[17,7,1,2,[3,6]]]" using (.small 11))

end HexECPPChapter
```

The string records a curve and point in PARI's row format. The
expression after `using` proves the prime that ends the chain.
During elaboration, Hex reconstructs the modular inverses and builds
an ordinary `Hex.ECPP.Cert`. Lean then verifies that certificate in
the same way as the explicit one. The compact expression does not
invoke PARI or repeat the curve search.

There are two convenient ways to retain a generated certificate:
apply the tactic's `Try this:` suggestion in your proof, or export
the certificate to a separate Lean module.

## Exporting a certificate to a module

In a file importing `HexECPPTheory.Native`, add:

```lean -show
run_cmd do
  match Lean.Parser.runParserCategory (← Lean.getEnv)
      `command
      "#ecpp_export (method := ecpp) MyCertificates.Prime cert for 17" with
  | .ok _ => pure ()
  | .error e => throwError "{e}"
```

```
#ecpp_export (method := ecpp) MyCertificates.Prime cert for 17
```

Build the file with `lake build`. The command searches for a
certificate, checks the resulting proof in Lean's kernel, and creates
`MyCertificates/Prime.lean` containing `MyCertificates.Prime.cert`.
It refuses to overwrite an existing file. When used in the editor,
the command displays the batch-build instructions instead of writing
a file.

Remove the export command after generation. Import the new module
and use its certificate in subsequent proofs:

```
module
public import MyCertificates.Prime

example : Nat.Prime 17 := by
  ecpp using MyCertificates.Prime.cert
```

The exported module imports `HexECPPTheory.Compact`, which provides
the checker, soundness theorem and compact certificate notation.
Checking an exported certificate needs neither native search nor GP.
This is useful when several files need the same prime, or when you
want to preserve a successful search independently of later changes
to the search procedure.

# Using PARI/GP

[PARI/GP](https://pari.math.u-bordeaux.fr/) is an external computer
algebra system with its own elliptic curve primality prover. Import
`HexECPPTheory.Pari` and install its `gp` executable on your `PATH`
to use it for certificate search. Then write
`primality? (method := pari)` in a primality proof. Hex asks GP for a
certificate, converts the result, and checks it before accepting the
proof or offering a saved replacement.

This route requires a POSIX system for generation. Once the
certificate is saved, it is ordinary Lean data: checking it does not
require GP. The export command for this route is
`#ecpp_export MyCertificates.Prime cert for 17`, with the same
build-and-import workflow as above.

## Using an existing PARI certificate

If you already have PARI certificate text, you can use `ecpp_cert%`
without installing GP. Each row has the form `[n,t,s,a,P]`:

- `n` is the integer to be proved prime.
- `m = n + 1 - t` is the proposed curve order, and `s` is its
  cofactor, so the next prime in the chain is `q = m / s`.
- `a` is the coefficient of `x` in the curve equation. The other
  coefficient is recovered from the supplied point `P`.
- `P` is an affine or homogeneous point; conversion computes
  `Q = s • P` and checks the required scalar multiplication by `q`.

The row in the example for 17 has `m = 17 + 1 - 7 = 11` and
cofactor 1, so `P` is already the point `Q` of order 11. The curve
itself has 22 points; the saved row records the point's order 11,
which is enough for the proof. A saved row is an encoding of the
certificate calculation: the field `t` need not be the actual
Frobenius trace of the curve. Hex verifies the required point-order
calculation instead of trusting a claimed point count.

PARI certificates end with a prime below PARI's own cutoff. Hex
still requires a proof certificate for that last integer; in the
example, it is `.small 11`. It does not assume primality merely
because PARI stopped its chain there.

Programmatic users can call {name}`Hex.ECPP.convertText` with a
string and the certificate for the last prime. It returns either
an accepted Hex certificate or an error. Conversion accepts signed
coordinates and reduces them modulo `n`. For homogeneous coordinates,
the denominator must be invertible modulo `n`.

{docstring Hex.ECPP.convertText}

# Search limits and unsuccessful attempts

Certificate search tries finitely many curves, points and auxiliary
factorizations. It can stop without finding a proof, even when the
integer is prime. An exhausted search therefore proves nothing
about compositeness. Its error reports the unresolved integer and
the stage or limit at which the search stopped.

The built-in search accepts integers through 256 bits by default.
Select the larger policy with
`primality? (method := ecpp) (bits := 512) (seed := 0)` for integers
through 512 bits. In an export command, put `(bits := 512)` before
the optional seed in the same way. The 512-bit policy tries an
additional collection of curves from fixed linear and quadratic
class polynomials. Neither policy guarantees success for every
prime within its size limit; production above 512 bits is unsupported.

The seed controls the search's point and witness choices. Reusing
the same seed makes the search reproducible. Changing it may find
a certificate when an earlier attempt failed. It does not change
which certificates the checker accepts.

Checking supplied certificates has separate limits. The public
proof commands accept integers through 512 bits, at most 20 compact
elliptic rows, and at most 32 certificate nodes in total. That total
includes the elliptic steps, the wrapper around the last
HexPrimality certificate, and every node of that certificate.
There are also limits on the amount of source text and the number
of modular inverses. These keep parsing and proof construction
finite; the 512-bit search accounts for the row and node limits
while trying alternative certificates.

## Calling the search from a program

The function {name}`Hex.ECPP.produce` returns the certificate and
search statistics, or a failure with its diagnostic. Its
{name}`Hex.ECPP.SearchBudget` argument controls the work allowed
for the whole search, including the recursive proofs of smaller
primes. Work already spent on an unsuccessful curve remains counted
when the search moves to another curve.

```lean
open Hex.ECPP in
#guard (produce 17 0).result.toOption.any (checkAt 17)
```

{docstring Hex.ECPP.produce}

The function's `.ok` result is a checked certificate. A Lean theorem
of primality is obtained by applying the companion's soundness
theorem to the checker equation, as described below.

## Limits when importing certificate text

{name}`Hex.ECPP.ImportBudget` controls how much input a conversion
may process: the length of the text, the number and size of the
integers and rows, and the work spent calculating inverses or
proving the last prime. The standard
{name}`Hex.ECPP.defaultImportBudget` is used by `ecpp_cert%`.
The input is checked against these limits before expensive
conversion or prime search begins.

{docstring Hex.ECPP.ImportBudget}

For a program that needs to read the format separately,
{name}`Hex.ECPP.parsePari` parses the certificate and
{name}`Hex.ECPP.preflight` checks its size limits.
{name}`Hex.ECPP.convertCounted` can search for the proof of the
last prime when that proof has not been supplied. The saved
compact notation always supplies it explicitly, so checking a
saved proof does not need that search.

# The Mathlib correspondence

The soundness theorem connects the executable checker to Mathlib's
`Nat.Prime`. Its only premise is that the checker accepts the
certificate; it does not require a separate assumption that any
proposed curve order, auxiliary prime or search result is correct.

```lean
example (c : Hex.ECPP.Cert)
    (h : Hex.ECPP.check c = true) : Nat.Prime c.subject :=
  Hex.ECPP.natPrime_of_check h

example (n : Nat) (c : Hex.ECPP.Cert)
    (h : Hex.ECPP.checkAt n c = true) : Nat.Prime n :=
  Hex.ECPP.natPrime_of_checkAt h
```

{docstring Hex.ECPP.natPrime_of_check}
{docstring Hex.ECPP.natPrime_of_checkAt}

The proof follows the mathematical argument given above. For every
prime divisor `p` of the candidate integer, it interprets the
coordinates as Mathlib points on an elliptic curve over `ZMod p`.
{name}`Hex.ECPP.startingPoint_rep` shows that the starting point
is not the identity; {name}`Hex.ECPP.add_rep` shows that each
accepted addition agrees with Mathlib's group law.
{name}`Hex.ECPP.replay_zero` then identifies the computed scalar
multiple with `q • Q = 0` in that group.

The order of the point divides the number of points on the curve.
The bound supplied by {name}`Hex.ECPP.hasse_sq_zmod` contradicts
the existence of a prime divisor at most `√n`. The Hasse theorem
is imported from Chris Birkbeck's AINTLIB development. Its
dependencies, and those of the primality theorems, are audited to
allow only Lean's standard `propext`, `Classical.choice` and
`Quot.sound` axioms.

The companion also relates the curve's points over the prime field
to points fixed by Frobenius over any extension field, in particular
an algebraic closure. The
equivalences {name}`Hex.ECPP.rationalPointsEquivFixed` and
{name}`Hex.ECPP.rationalPointsEquivKer` express that correspondence
as fixed points and as the kernel of `1 - Frobenius`, respectively.

Certificate search runs during elaboration, but its computations
are not trusted as proofs. The generated data is turned into
explicit certificate constructors. Lean's kernel checks the
equation asserting that the checker returns `true`, and the proved
soundness theorem supplies `Nat.Prime n`. The native and PARI
routes check the exact saved certificate before suggesting it or
writing an export file.

For users of the computational API, {name}`Hex.ECPP.produce_ok`
and {name}`Hex.ECPP.convert_ok` establish that successful search
and conversion results pass the checker. The unconditional
primality implication remains in the theory companion, where
the elliptic curve and Hasse arguments are available.

For more on the mathematics, see
[Sutherland's notes on elliptic curve primality proving](https://math.mit.edu/classes/18.783/2023/LectureNotes11.pdf).
For the external certificate format, see
[PARI's `primecert` documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#primecert).
