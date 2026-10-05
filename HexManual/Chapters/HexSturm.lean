/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexSturmMathlib
import HexRealRootsMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexSturm: signed root sums and root counts" =>
%%%
tag := "hex-sturm"
%%%

# Sturm–Tarski queries

`HexSturm` computes a signed sum over the distinct roots of a polynomial
in an open interval. For a head polynomial `P` and query polynomial `F`,
each root of `P` contributes the sign of `F` there: `-1`, `0` or `1`.
Querying `1` therefore counts the roots. A general query can return zero
even when the interval contains roots, because opposite signs cancel.

The computational import is `HexSturm`. It is Mathlib-free and uses the
shared signed-remainder and certificate-checking kernel from
{ref "hex-real-roots"}[HexRealRoots]. Import `HexSturmMathlib` for the
proofs relating those computations to mathematical root sets. Mathlib and
Tau Ceti belong to the companion; neither is a computational dependency.
Both Sturm libraries are development libraries in `hex-dev` and have not
yet been published as split packages.

This frontend counts and queries roots without enumerating them. Complete
sign tables and Thom encodings belong to sign determination; root isolation
and adjoining a selected root belong to the real-closure library. The
integer isolator documented in {ref "hex-real-roots"}[HexRealRoots]
remains a separate entry point.

# Coefficients, endpoints and the success domain

Polynomials use {name}`Hex.DensePoly`, with coefficients stored in ascending
degree order. {name}`Hex.Endpoint` represents a finite coefficient value,
negative infinity or positive infinity. Intervals are open: a finite endpoint
does not belong to the queried interval.

The query accepts an explicit total sign function on coefficients. Canonical
ordered coefficients can use the following function:

{docstring Hex.Sturm.orderSign}

For the mathematical interpretation, a valid domain requires a nonzero,
squarefree head, strictly ordered endpoints, and no head root at either
finite endpoint. Nonzero constants are valid heads and give zero roots.
The query polynomial does not affect domain validity: it can be zero,
share roots with the head, or have higher degree than the head.

{docstring Hex.Sturm.query}

Here `P = X²-1` has roots `-1` and `1`. The queries of `X` and `X-1`
illustrate cancellation and a zero contribution at a shared root:

```lean
open Hex
namespace SturmQueries

def x : DensePoly Rat :=
  DensePoly.ofCoeffs #[0, 1]
def p : DensePoly Rat :=
  DensePoly.ofCoeffs #[-1, 0, 1]

#guard Sturm.query Sturm.orderSign p 1
  .negInf .posInf = some 2
#guard Sturm.query Sturm.orderSign p x
  .negInf .posInf = some 0
#guard Sturm.query Sturm.orderSign
  p (x - 1) .negInf .posInf = some (-1)
#guard Sturm.query Sturm.orderSign p 0
  .negInf .posInf = some 0
```

`none` means that the head or interval is invalid. It is not a refinement
timeout or an inconclusive sign. In particular, a zero query does not make
an invalid head acceptable:

```lean
#guard Sturm.query Sturm.orderSign
  (0 : DensePoly Rat) 0
  .negInf .posInf = none
#guard Sturm.query Sturm.orderSign
  (DensePoly.natPow (x - 1) 2) 1
  .negInf .posInf = none
#guard Sturm.rootCount Sturm.orderSign p
  (.finite 1) .posInf = none
#guard Sturm.rootCount Sturm.orderSign
  (DensePoly.C 5 : DensePoly Rat)
  .negInf .posInf = some 0
```

The sign callback and coefficient arithmetic must be total and lawful.
A bounded approximation attempt from
{ref "hex-ordered-fn"}[HexOrderedFn] does not by itself supply this
interface. Registered real extensions justify total sign search using
their additional containment, width and relative-transcendence laws.

# Prepare a head once

{name}`Hex.Sturm.PreparedDomain` stores the sign function, head, endpoints
and the head's validated squarefree chain. Its constructor is private.
Preparation validates the domain; subsequent prepared queries reuse the
squarefree chain while computing the chain for their own query polynomial.

{docstring Hex.Sturm.PreparedDomain}

{docstring Hex.Sturm.prepare}

{docstring Hex.Sturm.queryPrepared}

Querying `1` has a further specialization: the stored squarefree chain
serves in both certificate positions, avoiding a second chain construction.
The result remains an integer; its nonnegativity is a semantic theorem.

{docstring Hex.Sturm.countPrepared}

The prepared count belongs to its current interval. To reuse the same head
on another interval, retarget the endpoints and check their guards again:

{docstring Hex.Sturm.PreparedDomain.withEndpoints?}

```lean
def splitCounts :
    Option (Int × Int) := do
  let whole ← Sturm.prepare
    Sturm.orderSign p .negInf .posInf
  let left ← whole.withEndpoints?
    .negInf (.finite 0)
  let right ← whole.withEndpoints?
    (.finite 0) .posInf
  pure (Sturm.countPrepared left,
    Sturm.countPrepared right)

#guard splitCounts = some (1, 1)
```

{name}`Hex.Sturm.PreparedDomain.withEndpoints_eq` proves that retargeting
returns the same whole result as fresh preparation. The binding theorem
preserves the literal head, sign and squarefree chain and records the new
endpoints. Old endpoint signs, counts and certificates are not proofs
about the retargeted interval.

For already proved chain data, {name}`Hex.Sturm.PreparedDomain.ofChecked`
restores a domain using endpoint validity, a constant-terminal proof and
equality with the actual producer's chain. Serialized chain data alone
do not meet those requirements. {name}`Hex.Sturm.prepare_ofChecked`
characterizes the restored value. Equal-operation transport through
{name}`Hex.Sturm.PreparedDomain.changeOps` preserves those proofs and
the stored data without repeating preparation.

# Produce and check literal certificates

`certify` returns a finite {name}`Hex.TarskiCertificate` containing the
head and query, endpoints, remainder identities, signs and claimed value.
It also records a caller-supplied context. `check` takes all these expected
bindings separately, including the claimed integer. It checks the proposed
certificate rather than regenerating the producer's chains.

{docstring Hex.Sturm.certify}

{docstring Hex.Sturm.check}

```lean
abbrev Packet :=
  TarskiCertificate Rat Rat Nat

def packet : Option Packet :=
  Sturm.certify Sturm.orderSign (7 : Nat) p 1
    .negInf .posInf

#guard packet.map (fun cert =>
  Sturm.check Sturm.orderSign 7 p 1
    .negInf .posInf 2 cert) = some true

#guard packet.map (fun cert =>
  Sturm.check Sturm.orderSign 8 p 1
    .negInf .posInf 2 cert) = some false
end SturmQueries
```

The second check rejects the foreign context even though the mathematical
polynomial and interval are unchanged. Accepted replay retains every literal
binding through {name}`Hex.Sturm.check_bindings`. This is separate from
the theorem assigning the accepted value its mathematical meaning.

`certifyPrepared` adds a context to a prepared query;
`certifyCountPrepared` specializes it to query `1` and the stored chain.
Their equality and value lemmas expose agreement with ordinary certification
and querying. {name}`Hex.Sturm.checkCached_eq` proves that optional reuse of
checked domain evidence preserves the complete checker result, including
rejection and cache misses.

Certificate rejection only rejects that proposed evidence. It does not prove
that the mathematical query is undefined. Conversely, a successful example
from the producer is not the general soundness proof for arbitrary supplied
certificates.

# Reduce a large query before computing its value

At a root of `P`, the value of `F` equals the value of its remainder modulo
`P`. `queryReduced` uses the existing remainder-only division worker before
the shared query producer, avoiding a retained high-degree quotient.

{docstring Hex.Sturm.queryReduced}

The companion's {name}`HexSturmMathlib.queryReduced_eq` proves equality
with the ordinary query's entire `Option`, including failure. Its hypotheses
include lawful interpretation of coefficient division. The prepared version
has the corresponding value equality.

These are value APIs. When evidence must bind the original unreduced query,
use the ordinary certificate APIs. Reduction does not provide a certificate
with different inputs that can be replayed as the original one.

For the earlier head `X²-1`, the eighth power has value `1` at each root:

```lean
namespace SturmQueries
#guard Sturm.queryReduced Sturm.orderSign
  p (DensePoly.natPow x 8)
  .negInf .posInf = some 2
end SturmQueries
```

# The Mathlib correspondence

The semantic field is an ordered real closed field. It can be
non-Archimedean; an ordinary real embedding is not required. Coefficient
storage itself need not have a field or order instance: an interpretation
into that semantic field must preserve the supplied operations and signs
and reflect zero. Zero reflection does not require injectivity on all
stored representatives.

Producer theorems also require lawful negation and inversion because they
justify the field normalization. The arbitrary-certificate theorem needs
the operations used to check the supplied identities and signs; it does
not assume that the producer made the certificate.

{name}`HexSturmMathlib.Domain` states the head and endpoint conditions.
The complete query theorem gives both producer success on that domain and
the meaning of every returned integer:

{docstring HexSturmMathlib.query_iff}

For example, specialize the public theorem to the ordinary real field.
This uses `HexSturmMathlib` together with `HexRealRootsMathlib`, whose
umbrella supplies the real-closed-field instance for `ℝ`. Both are ordinary
public imports:

The local instance makes the executable operations use the field dictionary
induced by Mathlib's `Field`, matching this theorem specialization.

```lean
namespace SturmSemantics
open HexPolyMathlib.Interpret HexRealRootsMathlib
attribute [local instance 2000]
  Field.toGrindField
noncomputable section

variable (p q : DensePoly ℝ)
variable (a b : Endpoint ℝ)

example
    (value : Int) :
    Sturm.query Sturm.orderSign p q a b = some value ↔
      HexSturmMathlib.Domain id (fun _ => Iff.rfl)
        p a b ∧
      value = Tarski.rootSum
        (interpret id (fun _ => Iff.rfl) p)
        (interpret id (fun _ => Iff.rfl) q)
        (a.map id) (b.map id) := by
  exact HexSturmMathlib.query_iff
    id (fun _ => Iff.rfl)
    rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    Sturm.orderSign HexSturmMathlib.orderSign_eq
    (fun _ => rfl) (fun _ => rfl) p q a b value
end
end SturmSemantics
```

{docstring HexSturmMathlib.check_sound}

That theorem proves domain validity and the signed sum for any accepted
certificate. The independent {name}`HexSturmMathlib.certify_checks` theorem
proves acceptance of produced certificates. `check_sound` gives any accepted
certificate its meaning, while `query_iff` proves that the producer succeeds
exactly on valid domains. A few successful outputs cannot establish those
general statements.

{name}`HexSturmMathlib.queryPrepared_sound` gives prepared-query semantics;
`countPrepared_sound` identifies the actual prepared integer count with the
cardinality of the current interval's root set. `countPrepared_nonneg`
justifies its nonnegativity before natural-number conversion.

{docstring HexSturmMathlib.rootCount_eq}

`rootCount_isSome` preserves the same domain as querying. Although the
executable operation uses `Int.toNat`, `query_nonneg` and `rootCount_query`
prove that no lawful count is clamped. `rootCount_map` identifies the whole
result after casting back to integers. These counts concern distinct roots
of a squarefree head, not multiplicities of an arbitrary polynomial.

`query_bound` bounds the absolute signed sum by the root count and the head
degree. `query_sign` identifies the answer with the sign at a selected root
when the interval's semantic root set is exactly that singleton; the query
does not itself select or isolate such a root.

# Representation changes and the integer frontend

{name}`HexSturmMathlib.query_congr` compares representations interpreted
in a common ordered field. It preserves the entire query result at
corresponding finite or infinite endpoints, allowing positive scaling of
both input polynomials. It does not construct a common field or an ordinary
real realization of an arbitrary ordered extension.

For rational coefficients and a finite ordered dyadic interval,
{name}`HexSturmMathlib.query_rat_eq` identifies the result with
`ZPoly.tarskiQuery` after positive denominator clearing. The equality
includes invalid `none` cases; differently normalized certificates need
not be identical. Integer queries retain their finite-interval API.

The executable translations are
{name}`Hex.TarskiCertificate.clearDenominators` and
{name}`Hex.TarskiCertificate.toRat`, supplied by `HexSturm.Transport`.
The companion proves that translations of accepted certificates are accepted, preserving
the literal context and claimed value without rerunning the producer.

Finally, {name}`HexSturmMathlib.rootCount_sturm` connects successful
finite-dyadic counts to the existing integer half-open Sturm count.
Success includes both root-free endpoint guards; this theorem does not
change the older API's behavior when its upper endpoint is a root.

```lean
variable (p : DensePoly Rat)
variable (interval : DyadicInterval)

example (n : Nat)
    (answer : Sturm.rootCount Sturm.orderSign p
      (.finite interval.lower.toRat)
      (.finite interval.upper.toRat) = some n) :
    (n : Int) =
      ZPoly.sturmCount (ZPoly.clearDenominators p).2
        interval :=
  HexSturmMathlib.rootCount_sturm
    p interval n answer
```
