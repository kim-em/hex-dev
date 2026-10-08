# hex-sturm

The implemented surface records Phase 4 in `libraries.yml`. The
[readiness audit](../reports/real-closure-prerequisites.md) documents proved APIs,
verification and performance limits. Split-package publication is separate.

`HexSturm` is part of [Hex](https://github.com/kim-em/hex-dev), a computer
algebra library for Lean 4. The aim is fast executable code, fully verified,
built with spec-driven development.

It computes ordered-field Sturm–Tarski queries and distinct-root counts using
`HexPoly` and `HexRealRoots`. It is Mathlib-free. The mathematical correspondence
lives in `HexSturmMathlib`. Both libraries are unreleased development libraries.
The [manual](https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-sturm)
explains the API with checked examples.

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

- `Sturm.query` computes a signed sum over distinct roots in an open interval;
  `rootCount` returns their natural count. Endpoints may be finite or infinite.
  Ordered coefficients can use `Sturm.orderSign`; other representations supply
  lawful total arithmetic and sign operations.
- `prepare`, `queryPrepared` and `countPrepared` reuse a validated squarefree
  chain. `PreparedDomain.withEndpoints?` checks new endpoint guards and agrees
  with fresh preparation. It preserves the head and chain, not an old count.
- `PreparedDomain.ofChecked` restores a domain from its exact producer equation,
  endpoint validity and constant-terminal proof. `changeOps` transports that
  evidence along proved equalities of coefficient operations.
- `certify`, `certifyPrepared` and `certifyCountPrepared` produce finite evidence
  bound to the caller's literal context and inputs. `check` replays that evidence;
  `check_bindings` exposes the bindings established by acceptance.
- `queryReduced` and `queryReducedPrepared` compute the value after remainder-only
  reduction modulo the head. Use ordinary certificate APIs when evidence must
  bind the original unreduced query.
- `HexSturm.Transport` exports `TarskiCertificate.clearDenominators` for finite
  dyadic intervals and `TarskiCertificate.toRat`, including infinite endpoints.

# Verification

`HexSturmMathlib.query_iff` proves both exact domain validity and root-sum
semantics. The head must be nonzero and squarefree, endpoints strictly ordered,
and each finite endpoint root-free. The query polynomial may be zero or share
roots with the head. Counts concern distinct roots, not arbitrary multiplicities.

The companion also proves arbitrary-certificate soundness, acceptance of produced
certificates, prepared-count nonnegativity, whole-`Option` backend agreement and
acceptance-preserving certificate transport. Reduced-query agreement requires
lawful coefficient division. Mathlib and Tau Ceti are confined to proof libraries.
See [the specification](SPEC/hex-sturm.md) for the full contracts.

# Contributing

Development happens in [hex-dev](https://github.com/kim-em/hex-dev).
Contributions are welcome as PRs to `SPEC/`: describe the behavior you want.
