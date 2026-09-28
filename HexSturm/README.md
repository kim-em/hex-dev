# hex-sturm

Ordered-field Sturm–Tarski queries through the shared `HexRealRoots` kernel.
This development library is Mathlib-free and is not yet released.

`Hex.Sturm.query sign p f a b` returns `Option Int` for finite or infinite
endpoints. `sign` is the exact coefficient sign; canonical ordered coefficients
can use `Hex.Sturm.orderSign`. Noncanonical coefficients supply ordinary total
operations and their own sign without a field or order instance on storage.
Field remainders are divided by their positive absolute leading coefficient;
negative leading signs are retained. Integers use the separate content backend.

`prepare` validates a head and its endpoints once; `queryPrepared` reuses the
squarefree chain. Prepared domains have a private constructor. `certify` and
`certifyPrepared` retain finite evidence with the caller's full literal context;
`check` checks that evidence through the shared checker.
`certify_value` and `certifyPrepared_value` relate certificates with any context
to their query results; `check_bindings` exposes the exact bindings
established by acceptance.

`domain.withEndpoints? lower upper` reuses the same literal head, sign operation
and squarefree chain after checking the new endpoints. It returns `none` for
root endpoints, reversed bounds or other failed endpoint guards. It agrees
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

The companion proves exact domain equivalence and produced-certificate
acceptance, whole-Option backend agreement and certificate transport.
`HexSturm.Transport` exports `TarskiCertificate.clearDenominators` for finite
dyadic intervals and `TarskiCertificate.toRat` including infinities.
The development semantic companion proves root sums, arbitrary-certificate
soundness, singleton signs and bounds using the pinned Tau Ceti foundation.
`rootCount` returns an `Option Nat` on exactly the valid domains, with
nonnegativity proved before conversion. Remaining Phase-4 evidence is
specified; see [the specification](SPEC/hex-sturm.md).
