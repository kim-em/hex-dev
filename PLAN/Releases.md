# Releases

The project ships five progressive releases, each unlocking a new user
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

### Release 3: Certified integer factorization

- **Libraries:** Release 2 + `HexPolyZ`, `HexHensel`,
  `HexBerlekampZassenhaus`, and `HexBerlekampZassenhausMathlib`, together
  with their transitive dependencies.
- **User story:** Every integer polynomial has a sound, total factorization
  through the production cascade. The result may use the exponential exact
  backstop; this release makes no polynomial-time claim.
- **Integration example:** `Examples/Release3.lean` — factor a handful
  of integer polynomials end-to-end, including at least one case that
  benefits from Hensel lifting beyond the baseline `mod p` step.

### Release 4: Conditional lattice factorization

- **Libraries:** The Release 3 set. `HexLLL` is already a transitive
  dependency of `HexBerlekampZassenhaus`.
- **User story:** The LLL-assisted pipeline has a proved success theorem under
  its explicit admissibility and precision hypotheses. For inputs satisfying
  that contract, a dedicated no-fallback entry point returns a factorization
  without exponential recombination. This is a conditional guarantee, not an
  unconditional polynomial-time claim for every integer polynomial.
- **Integration example:** `Examples/Release4.lean` — factor
  a high modular-factor-count polynomial and assert that the production trace
  selects the LLL-assisted lattice tier without invoking the trial backstop.
- **Tutorials:** LLL in cryptanalysis / Coppersmith toy (anchored to
  `hex-lll`).

### Release 5: Certified root isolation

- **Libraries:** `HexRoots`, `HexRootsMathlib`, `HexRealRoots`, and
  `HexRealRootsMathlib`, together with their transitive dependencies.
- **User story:** Users can isolate every complex root of a nonzero squarefree
  integer polynomial and every distinct real root of an arbitrary nonzero
  integer polynomial. Results carry checked coverage, uniqueness,
  disjointness, count, and precision guarantees.
- **Integration example:** `Examples/Release5.lean` — use the none-free
  `HexRootsMathlib.isolate!` wrapper for complex roots and the
  `isolate_roots` elaborator for repeated real roots.

## Release readiness predicate

A release `R` is ready when, computed from `libraries.yml`:

> **every named library and transitive dependency `L` in `R.libraries` has
> `done_through ≥ 7`**
> **and `R.integration-example` builds and its test passes in CI**.

`scripts/status.py release <N>` computes the dependency closure from
`libraries.yml` and evaluates this predicate.

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

"Release" above means a milestone. Separately, libraries are
*published* as standalone repositories under `leanprover/`, so they can be
used without the whole monorepo. `hex-dev` is the single source of
truth: all development happens here, and a workflow regenerates each
published repo from this tree. A published repo is a mirror — never
hand-edit one; change it here and let the sync publish.

### The published set

The authoritative dependency order is `scripts/release/released.yml`; read it
rather than any count restated here. Broadly it contains:

- the shared `hex-basic` and `hex-test-kit` foundations;
- the arithmetic/polynomial stack from `hex-arith` through `hex-gfq-ring`,
  `hex-hensel`, and their Mathlib bridges;
- `hex-roots`, `hex-real-roots`, and their Mathlib bridges;
- the matrix, determinant, Gram--Schmidt, and LLL repositories already
  published by the earlier release work; and
- `hex-berlekamp`, `hex-berlekamp-zassenhaus`, and their Mathlib bridges.

`python3 scripts/release/check_released_manifest.py` checks the set, managed
paths, pin closure, and publication order without network access.

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

In this monorepo, all bench and conformance drivers build in the shared root
Lake graph. Published mirrors use the corresponding root and sidecar skeletons
documented in `scripts/release/BOOTSTRAP.md`; the sync manages source and
rewrites every lockfile but deliberately leaves those Lake skeletons intact.

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

### Publishing a new library: widen the token first

The sync authenticates with the `RELEASED_SYNC_PAT` secret, currently a
fine-grained token named `hex-publishing` owned by @kim-em. It is scoped to an
explicit list of repositories, deliberately not to every repository, so
publishing a new library takes three steps in this order:

1. create the repository under `leanprover` and give it the un-managed Lake
   and CI skeleton (`scripts/release/BOOTSTRAP.md`); the sync clones but never
   creates;
2. add that repository to the selected repositories of the token behind
   `RELEASED_SYNC_PAT` with `Contents: Read and write`, and have an
   organization owner approve the request at
   https://github.com/organizations/leanprover/settings/personal-access-token-requests;
   the current token is at
   https://github.com/settings/personal-access-tokens/16433897, but find it
   under https://github.com/settings/personal-access-tokens if it has since
   been rotated; then
3. add its entry to `released.yml` here and run the sync.

The repository has to exist before step 2 can name it, which is why step 1
comes first; nothing in this order is circular. Step 2 is the one with a
human in the loop, so start it early. Rotating the token means redoing step 2
for every published repository at once, so keep the secret and the token
identified by name rather than by that numeric URL.

Skipping step 2 used to fail partway through a publish, after earlier
repositories had already been pushed: the token simply cannot see a repository
outside its list, so the clone succeeds from public https and only the push
returns `403 Permission to leanprover/<repo>.git denied`. `sync_released.py`
now preflights every target repository before the first push and refuses to
start, naming the repositories to add and both URLs above. A dry run does not
preflight, having no token and pushing nothing.

**What the preflight does not prove.** It checks that each repository is in
the token's selection, and nothing stronger. `GET /repos` needs only
`Metadata: read`, and the `permissions` it returns describe the authenticated
user's role rather than this token's grants, so a token holding only
`Contents: read` on a selected repository still looks fine to it. Nor does it
know whether branch protection or a ruleset on a mirror's `main` would reject
the push. Those failures still surface only at push time; the invariant the
mirrors rely on is that `main` takes direct pushes from the release actor.

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
