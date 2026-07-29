# HexMvPoly consumer acceptance

`setup_hex_mv_poly_consumers.py` clones the audited revisions of
`leanprover/sos` and `Verified-zkEVM/CompPoly`, replaces their
multivariate-polynomial integration surfaces, pins their Lake dependency to
the requested Hex source tree, and builds the acceptance targets. CompPoly
also receives one theorem-preserving toolchain compatibility edit:
`ofPoly_zero` is reproved through its public ring equivalence because the
pinned proof unfolds support internals that do not elaborate with Hex's Lean
toolchain.

```sh
python3 scripts/bench/setup_hex_mv_poly_consumers.py /tmp/hex-mvpoly-consumers
```

The pinned revisions are recorded in the setup script. The SOS adapter covers
the search-facing polynomial API and the verifier's kernel certificate path.
The CompPoly adapters cover its univariate and bivariate recursive-view
consumers. A full SOS executable link may additionally require system
BLAS/LAPACK libraries through CSDP; the acceptance command deliberately builds
the verifier object target and all affected Lean modules without adding that
host-library requirement.
