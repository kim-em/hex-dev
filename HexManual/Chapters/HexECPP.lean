/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexECPP

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

#guard match convertCounted
    { defaultImportBudget with maxIntegerBits := 2 }
    Hex.Nat.defaultPrimeCertBudget
    (Hex.Rand.ofSeed 1) 10 ⟨[], 15⟩ with
  | .error e => e.kind == .exhausted
  | _ => false
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
#guard match (produce 17 0 { maxBits := 4 }).result with
  | .error e => e.resource == .inputBits
  | _ => false
#guard match (produce 17 0 { maxDepth := 0 }).result with
  | .error e => e.resource == .depth
  | _ => false
```

Exhaustion is not a compositeness verdict. The supported native policy
admits subjects through 256 bits. Supplied-certificate checking and
conversion have separate evidence through 512 bits; that does not extend
native search to those sizes. Callers can inspect cumulative resource
charges and backtracking statistics in the returned search state.

{docstring Hex.ECPP.produce}
{docstring Hex.ECPP.produce_ok}
{docstring Hex.ECPP.SearchBudget}

# The Mathlib correspondence

`HexECPPMathlib` owns interpretation over every prime divisor of the
candidate modulus, affine and scalar correspondence, the Hasse bound and
the resulting primality theorem. Its companion phase audits and
correspondence documentation are tracked separately. The executable
checker and conversion guarantees above are available without that bridge.
