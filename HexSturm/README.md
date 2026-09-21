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

The companion proves exact domain equivalence and produced-certificate
acceptance, whole-Option backend agreement and certificate transport.
`HexSturm.Transport` exports `TarskiCertificate.clearDenominators` for finite
dyadic intervals and `TarskiCertificate.toRat` including infinities.
Root-sum and replay semantics, the root-count API, singleton/sign
bounds and Phase-4 evidence remain
required; see [the specification](SPEC/hex-sturm.md).
