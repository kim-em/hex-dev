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
  release's library set. The manual is continuously rendered and
  published to GitHub Pages from `main` (see *Rendering and publishing
  the manual* below); a release tags the snapshot live at the release
  commit.
- A short release notes entry listing the libraries, the user story,
  and the integration example.

## Rendering and publishing the manual

`HexManual` is a Verso document. `lake build HexManual` only *typechecks*
it -- every `{docstring}`, `{ref}`, `#eval`/`leanOutput`, and `#guard` is
checked as the chapters elaborate. To produce the browsable site, the
`hexmanual` executable (`Main.lean`) renders it to static HTML:

    lake exe hexmanual --output _out

The multi-page site lands in `_out/html-multi`; open its `index.html`, or
serve it with `python3 -m http.server -d _out/html-multi`.

`.github/workflows/pages.yml` runs that render on every push to `main`
(and on `workflow_dispatch`) and deploys the result to GitHub Pages at
<https://kim-em.github.io/hex-dev/>. It does not run on pull requests:
it is a publish step, not a merge gate (the chapters' content is checked
whenever `lake build HexManual` elaborates them). Rendering needs the
full Mathlib-backed build, so the job fetches the Mathlib cache exactly
as `ci.yml` does.

Publishing requires the repository's Pages source to be set to *GitHub
Actions* once (Settings -> Pages -> Build and deployment -> Source).

## Published libraries

"Release" above means a milestone. Separately, several libraries are
*published* as standalone repositories under `kim-em/`, so they can be
used without the whole monorepo. `hex-dev` is the single source of
truth: all development happens here, and a workflow regenerates each
published repo from this tree. A published repo is a mirror — never
hand-edit one; change it here and let the sync publish.

### The published set

In dependency order (`scripts/release/released.yml`):

`hex-test-kit`, `hex-matrix`, `hex-row-reduce`, `hex-determinant`,
`hex-bareiss`, `hex-matrix-mathlib`, `hex-row-reduce-mathlib`,
`hex-determinant-mathlib`, `hex-bareiss-mathlib`, `hex-gram-schmidt`,
`hex-gram-schmidt-mathlib`, `hex-lll`, `hex-lll-mathlib`.

This is the current set, not a permanent one; more sublibraries may be
published later. The computational repos are Mathlib-free; the
`*-mathlib` repos are the bridge layers.

### Uniform per-library layout

Every library uses the same layout, so publishing is a near-mechanical
copy:

- `HexX/` — source plus the `HexX.lean` umbrella.
- `HexX/SPEC/hex-x.md` — the library's SPEC.
- `bench/HexX/Bench.lean` — bench driver.
- `conformance/HexX/{Conformance,EmitFixtures}.lean` — conformance drivers.
- `conformance-fixtures/HexX/*.jsonl`, `scripts/oracle/<lib>_*.py`.

The bench and conformance drivers stay in the root Lake package (via
`srcDir`), not in sub-packages: a sub-package would re-resolve and
duplicate the whole Mathlib checkout.

### The publish mechanism

Four pieces, under `scripts/release/` and `.github/workflows/`:

- `released.yml` — a per-repo manifest: which paths to copy, which
  oracles to ship, and which upstream repos to pin, in dependency order.
- `sync_released.py` — the driver. For each repo it clones `main`,
  overwrites the managed paths from this tree, rewrites the cross-repo
  Lake revisions, and commits to `main`. `--dry-run` prints the planned
  changes without pushing; run it first.
- `synced.json` — the baseline seed (see below).
- `sync-released.yml` — a manual workflow (`workflow_dispatch`, dry by
  default). One dispatch drives the whole publish.

Rewriting the cross-repo revisions touches **every** lakefile and
`lake-manifest.json` in a repo — the root and the `bench/` and
`conformance/` sub-projects — updating both `rev` and `inputRev`. Lake
trusts the manifest, so a stale lockfile would otherwise rebuild against
the old revision.

### Baseline and the uncoordinated-commit guard

The sync records, per repo, the `main` commit this monorepo was last
synced from. If a published repo's `main` has moved off that baseline,
the sync refuses to overwrite it — it reports the divergence and skips
(`--force` overrides) — so an out-of-band commit is never silently lost.

Reconciling means re-seeding: bring that library's content here up to
the published `main`, rebuild the whole graph green, then re-run the
sync. The baseline lives on the unprotected `release-sync-baseline`
branch, which the workflow reads and advances on every real run;
`scripts/release/synced.json` is the seed used before that branch
exists.
