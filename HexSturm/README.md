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
squarefree chain. Prepared values have a private constructor. `certify` and
`certifyPrepared` retain finite evidence with the caller's full literal context;
`Replay.check` checks that evidence through the shared checker.
`certify_value` and `certifyPrepared_value` relate certificates with any context
to their query results; `Replay.check_bindings` exposes the exact bindings
established by acceptance.

The companion proves exact domain equivalence and produced-certificate
acceptance. Root-sum and replay semantics, the root-count API, singleton/sign
bounds, rational/integer backend correspondence and Phase-4 evidence remain
required; see [the specification](SPEC/hex-sturm.md).
