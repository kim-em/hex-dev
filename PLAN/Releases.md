# Releases

The project ships four progressive releases, each unlocking a new user
story. A release is a named set of libraries plus an integration
example that exercises the advertised user story end-to-end.

## Release ladder

### Release 1: Finite-field constructor

- **Libraries:** `HexModArith`, `HexPoly`, `HexPolyFp`, `HexGFqRing`,
  `HexGFqField`, `HexGF2`
- **User story:** Users can construct quotient rings `F_p[x]/f` for any
  `f`, and finite fields `GF(p^n)` from a user-supplied irreducibility
  proof.
- **Integration example:** `Examples/Release1.lean` — construct
  `GF(2^8)` (AES field) and `F_p[x]/(x^2+1)` for a small prime, verify
  a handful of field identities at runtime.
- **Tutorials:** AES byte arithmetic (anchored to `hex-gf2`).
- **Explicit non-claim:** this release does *not* claim that the
  project can yet generate irreducibility evidence on demand.

### Release 2: Irreducibility engine

- **Libraries:** Release 1 + `HexBerlekamp`, `HexBerlekampMathlib`,
  `HexConway`, `HexGFq`
- **User story:** Users can check irreducibility over `F_p` and use it
  to instantiate `FiniteField p f hf hirr`.
- **Integration example:** `Examples/Release2.lean` — end-to-end
  construction of `GF(p^n)` with no external irreducibility input,
  using `hex-berlekamp`'s Rabin test or `hex-conway`'s tabulated
  polynomials.
- **Tutorials:** AES modulus irreducibility (anchored to
  `hex-berlekamp`); prime splitting via Kummer-Dedekind (anchored to
  `hex-gfq`).

### Release 3: Integer factoring support

- **Libraries:** Release 2 + `HexPolyZ`, `HexHensel`,
  `HexBerlekampZassenhaus`
- **User story:** Berlekamp-Zassenhaus supports irreducibility and
  factoring workflows that start from integer polynomials, replacing
  external CAS dependencies in downstream number-theory projects.
- **Integration example:** `Examples/Release3.lean` — factor a handful
  of integer polynomials end-to-end, including at least one case that
  benefits from Hensel lifting beyond the baseline `mod p` step.

### Release 4: Polynomial-time capstone

- **Libraries:** Release 3 + `HexLLL` (integrated into the
  Berlekamp-Zassenhaus pipeline)
- **User story:** The full polynomial-time Berlekamp-Zassenhaus
  pipeline is available, and finite-field/irreducibility workflows no
  longer depend on the exponential recombination fallback.
- **Integration example:** `Examples/Release4.lean` — factor
  polynomials where LLL-assisted recombination is the only tractable
  path, demonstrating the exponential fallback would time out.
- **Tutorials:** LLL in cryptanalysis / Coppersmith toy (anchored to
  `hex-lll`).

## Release readiness predicate

A release `R` is ready when, computed from `libraries.yml`:

> **every library `L` in `R.libraries` has `done_through ≥ 7`**
> **and `R.integration-example` builds and its test passes in CI**.

`scripts/status.py release <N>` evaluates this predicate.

This is the only release-level gate. Per-library requirements that
were previously stated as project-wide release criteria (the
computational path runs natively in Lean, irreducibility/field claims
backed by Lean-checked evidence) now live in
[Phase6.md](Phase6.md)'s exit criteria, where they are enforced
per-library. Similarly, tutorial completion is subsumed by each anchor
library's Phase 7 exit — so `done_through ≥ 7` for every library in
`R.libraries` implies every anchored tutorial is done.

## Release-level artifacts

Per release:

- A Git tag (e.g. `v0.1-finite-field-constructor`) on the commit where
  the release predicate first becomes true.
- The integration example committed under `Examples/Release<N>.lean`
  and exercised in CI.
- A rendered copy of `HexManual` including every chapter for the
  release's library set, with anchored tutorials linked from the
  release entry point.
- A short release notes entry listing the libraries, the user story,
  and the integration example.
