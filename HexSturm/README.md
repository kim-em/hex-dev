# hex-sturm

`HexSturm` is part of [Hex](https://github.com/kim-em/hex-dev), executable
computer algebra for Lean 4 developed from specifications and verified APIs.
It computes ordered-field Sturm–Tarski queries and distinct-root counts through
the shared `HexRealRoots` kernel.

This development library depends on `HexPoly` and `HexRealRoots`, is Mathlib-free,
and is not yet released. `HexSturmMathlib` supplies its mathematical correspondence.

The [manual chapter](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-sturm)
walks through signed queries, prepared domains, literal certificates and the
Mathlib correspondence with checked examples.

# Quickstart

Use these imports from the `hex-dev` monorepo; there is no released package yet.

```lean
import HexSturm
open Hex

def p : DensePoly Rat := DensePoly.ofCoeffs #[-1, 0, 1]

#guard Sturm.query Sturm.orderSign p 1 .negInf .posInf = some 2
#guard Sturm.rootCount Sturm.orderSign p (.finite 0) .posInf = some 1
```

# Functionality

`Hex.Sturm.query sign p f a b` returns `Option Int` for finite or infinite
endpoints. `sign` is the exact coefficient sign; canonical ordered coefficients
can use `Hex.Sturm.orderSign`. Noncanonical coefficients supply ordinary total
operations and their own sign without a field or order instance on storage.
Field remainders are divided by their positive absolute leading coefficient;
negative leading signs are retained. Integers use the separate content backend.

`prepare` validates a head and its endpoints once; `queryPrepared` reuses the
squarefree chain. Prepared domains have a private constructor.
`PreparedDomain.ofChecked` restores a domain from its exact producer equation,
endpoint validity and constant-terminal proof; `prepare_ofChecked` identifies
that domain with actual preparation. `PreparedDomain.changeOps` retains its
fields along proved equalities of coefficient operations. These interfaces
reuse proved data without preparing another chain. `certify` and
`certifyPrepared` retain finite evidence with the caller's full literal context;
`check` checks that evidence through the shared checker.
`certify_value` and `certifyPrepared_value` relate certificates with any context
to their query results; `check_bindings` exposes the exact bindings
established by acceptance.

`queryReduced` and `queryReducedPrepared` first reduce the query modulo the
head with the existing remainder-only division worker, then invoke the shared
Tarski producer. They avoid retaining the high-degree quotient. The companion
proves equality with the ordinary value APIs, including the exact success
domain, when coefficient division has its lawful field interpretation. Use the
ordinary certificate APIs for evidence bound to the unreduced query.

`domain.withEndpoints? lower upper` reuses the same literal head, sign operation
and squarefree chain after checking the new endpoints. It returns `none` for
root endpoints, equal or reversed bounds, or other failed endpoint guards. It agrees
with fresh preparation; it does not reuse an interval's old count or endpoint
signs. A changed head requires separate preparation.

`countPrepared domain` returns an `Int` by evaluating the query `1` using the stored chain in both
certificate positions. `certifyCountPrepared context domain` produces its
literal certificate with freshly computed endpoint signs. Both agree with the
ordinary prepared query/certificate APIs. For example, retargeting a domain
for `X² − 1` to `(-∞, 0)` and `(0, +∞)` gives count one on each side; the
whole-line certificate cannot be replayed as either child certificate.
Compare integer counts directly or establish nonnegativity before converting
to `Nat`; unexpected negative results must not be clamped.

# Verification

The companion proves exact domain equivalence and produced-certificate
acceptance, whole-Option backend agreement and certificate transport.
`HexSturm.Transport` exports `TarskiCertificate.clearDenominators` for finite
dyadic intervals and `TarskiCertificate.toRat` including infinities.
The development semantic companion proves root sums, arbitrary-certificate
soundness, singleton signs and bounds using the pinned Tau Ceti foundation.
`rootCount` returns an `Option Nat` on exactly the valid domains, with
nonnegativity proved before conversion. Remaining Phase-4 evidence is
specified; see [the specification](SPEC/hex-sturm.md).

# Contributing

Development happens in [hex-dev](https://github.com/kim-em/hex-dev).
Contributions are welcome as PRs to `SPEC/`: describe the behavior you want.
