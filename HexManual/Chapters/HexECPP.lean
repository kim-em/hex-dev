/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexECPP
import HexECPPMathlib
import HexECPPMathlib.Native
import HexECPPMathlib.Pari

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexECPP: bounded elliptic-curve certificates" =>
%%%
tag := "hex-ecpp"
%%%

# Introduction

`HexECPP` checks arithmetic certificates, converts supplied PARI
vectors, and offers an explicitly bounded native CM producer. It uses
{name}`HexArith.bitLength` from {ref "hex-arith"}[HexArith] and terminal
{name}`Hex.Nat.PrimeCert` certificates from {ref "hex-primality"}[HexPrimality].
The implementation imports no Mathlib module. Production is opt-in:
ordinary `primality` does not automatically fall back to ECPP.

An accepted certificate establishes the arithmetic premises used by ECPP.
The unconditional primality implication additionally needs the curve
semantics and Hasse bound owned by `HexECPPMathlib`.

# Certificates and subject binding

{name}`Hex.ECPP.Cert` has a terminal certificate constructor and an
elliptic step. A step records the modulus, curve coefficients, a finite
point, a discriminant inverse and an inverse transcript. Its scalar is
always its child's subject. There is no separately claimed curve order
or scalar in the raw certificate.

```lean
open Hex.ECPP
namespace HexECPPChapter

def smallCertificate : Cert := .base (.small 17)
#guard checkAt 17 smallCertificate
#guard !checkAt 19 smallCertificate

def curveCertificate : Cert :=
  .step 17 2 3 3 6 6 [10, 13, 3, 13]
    (.base (.small 11))
#guard checkAt 17 curveCertificate
```

{docstring Hex.ECPP.check}
{docstring Hex.ECPP.checkAt}
{docstring Hex.ECPP.checkAt_eq_true_iff}

The checker rejects noncanonical residues, nonunit division witnesses,
unconsumed inverses and both equality boundaries of the strict ECPP size
bound. It derives the binary schedule from the child subject, performs
checked affine additions and requires the final point to be infinity.

{docstring Hex.ECPP.replayDone_eq_true_iff}
{docstring Hex.ECPP.sizeBound_eq_true_iff}

# Supplied PARI conversion

{name}`Hex.ECPP.ImportBudget` bounds text bytes and decimal digits,
every supplied integer magnitude, rows, scalar bits, inverse operations
and endpoint search fuel. Parsed-input preflight precedes endpoint
construction. Row errors preserve their original vector index; the
endpoint occupies the index immediately after the rows.

```lean
#guard (convertText defaultImportBudget
  "[[17,7,1,2,[3,6]]]" (.small 11)).isOk
#guard (convertText defaultImportBudget
  "17" (.small 17)).isOk

def importExhausted : Bool := match convertCounted
    { defaultImportBudget with maxIntegerBits := 2 }
    Hex.Nat.defaultPrimeCertBudget
    (Hex.Rand.ofSeed 1) 10 ⟨[], 15⟩ with
  | .error e => e.kind == .exhausted
  | _ => false
#guard importExhausted
```

Signed PARI coordinates are reduced during conversion. Homogeneous
coordinates require a unit denominator. Raw certificates themselves must
already contain canonical residues. PARI's integer terminal representation
is replaced with an accepted Hex primality certificate, never assumed
prime because it lies below PARI's cutoff.

{docstring Hex.ECPP.parsePari}
{docstring Hex.ECPP.preflight}
{docstring Hex.ECPP.convertText}
{docstring Hex.ECPP.convertCounted}
{docstring Hex.ECPP.convert_ok}

# Bounded native production

{name}`Hex.ECPP.produce` accepts a subject, deterministic seed and
{name}`Hex.ECPP.SearchBudget`. Its finite CM portfolio proposes roots,
curves and orders; checking remains the authority. Shared allocations
survive local retries and recursive backtracking. Failed point proposals
leave other twists and orders available. Complete local portfolio
exhaustion and an unresolved recursive child have distinct diagnostics.

```lean
#guard (produce 17 0).result.toOption.any (checkAt 17)
def bitsExhausted : Bool :=
  match (produce 17 0 { maxBits := 4 }).result with
  | .error e => e.resource == .inputBits
  | _ => false
#guard bitsExhausted
def depthExhausted : Bool :=
  match (produce 17 0 { maxDepth := 0 }).result with
  | .error e => e.resource == .depth
  | _ => false
#guard depthExhausted

end HexECPPChapter
```

Exhaustion is not a compositeness verdict. The supported native policy
admits subjects through 256 bits by default. Explicit
{name}`Hex.ECPP.native512Budget` admits 512 bits with 33 additional fixed
linear or quadratic class polynomials. {name}`Hex.ECPP.public512Budget`
also accounts for public replay row and node limits during backtracking.
Production above 512 bits is unsupported. Callers can inspect cumulative resource
charges and backtracking statistics in the returned search state.

{docstring Hex.ECPP.produce}
{docstring Hex.ECPP.produce_ok}
{docstring Hex.ECPP.SearchBudget}

# The Mathlib correspondence

`HexECPPMathlib` owns interpretation over every prime divisor of the
candidate modulus, affine and scalar correspondence, and the proved
Hasse bound imported from AINTLIB. Raw checker acceptance is the only
premise of the unconditional primality theorems.

{docstring Hex.ECPP.natPrime_of_check}
{docstring Hex.ECPP.natPrime_of_checkAt}

```lean
namespace HexECPPMathlibChapter

example (c : Hex.ECPP.Cert)
    (h : Hex.ECPP.check c = true) : Nat.Prime c.subject :=
  Hex.ECPP.natPrime_of_check h

@[expose] def certificate : Hex.ECPP.Cert :=
  .step 17 2 3 3 6 6 [10, 13, 3, 13]
    (.base (.small 11))

example : Nat.Prime 17 := by ecpp using certificate
example : Nat.Prime 17 := by
  ecpp using
    (ecpp_cert% "[[17,7,1,2,[3,6]]]" using (.small 11))
```

The starting point and every accepted addition represent actual group
points over each prime divisor, even when the parent modulus is
composite. A nonzero point annihilated by the prime child has that exact
order. Its order divides the finite point count, and the Hasse bound
together with the checker's strict inequalities excludes small prime
divisors. Recursive acceptance then proves primality.

{docstring Hex.ECPP.startingPoint_rep}
{docstring Hex.ECPP.add_rep}
{docstring Hex.ECPP.hasse_sq_zmod}
{docstring Hex.ECPP.rationalPointsEquivFixed}
{docstring Hex.ECPP.rationalPointsEquivKer}

Import `HexECPPMathlib.Native` explicitly to produce a certificate.
The native route takes a closed subject, optional `bits` policy (256 or 512,
default 256) and optional seed. Use `primality? (method := ecpp) (bits := 512)
(seed := 0)` to select bounded 512-bit production. Its exact
suggestion is checked below, followed by replay of that suggested text.

```lean
/-- info: Try this:
  [apply] ecpp using
    (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)
-/
#guard_msgs (whitespace := lax) in
example : Nat.Prime 17 := by
  primality? (method := ecpp)

example : Nat.Prime 17 := by
  ecpp using (ecpp_cert% "17" using (.small 17))

end HexECPPMathlibChapter
```

Replay admits supplied certificates through 512 bits. Native production
defaults to 256 bits and explicitly admits 512 bits with `(bits := 512)`.
It may exhaust its finite allocation. A successful proposal must also fit replay: the 32-node
ceiling counts every elliptic step, the ECPP base wrapper and all nodes
of its terminal primality certificate. The 512-bit producer checks these row and node limits during
backtracking, and generation validates the exact frozen data before publication. Exhaustion is not a compositeness verdict.

For source export, import `HexECPPMathlib.Native` and put
`#ecpp_export (method := ecpp) MyCertificates.Prime cert for 17`
in a module built with `lake build`; add `(bits := 512)` before the optional
seed to select the 512-bit policy. The command kernel-checks the frozen
certificate before exclusively creating `MyCertificates/Prime.lean`.
Remove the export command and add `public import MyCertificates.Prime`;
`ecpp using MyCertificates.Prime.cert` then replays the frozen data.
The exported module publicly imports only `HexECPPMathlib.Compact`.
Replay does not invoke native search or GP. The language server displays
batch-build instructions instead of writing files.

The optional `HexECPPMathlib.Pari` import provides
`primality? (method := pari)` and
`#ecpp_export MyCertificates.Prime cert for 17`. This generator calls
PARI/GP on POSIX under finite time and output allocations, then completes
and kernel-checks the proposed certificate. It uses the same frozen
export/replay workflow. GP is needed only during generation. Ordinary
`primality` behavior and `norm_num` dispatch do not change.
