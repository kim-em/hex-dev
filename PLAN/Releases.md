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
  `hex-berlekamp`).

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
- **Tutorials:** prime splitting via Kummer-Dedekind (anchored to
  `hex-berlekamp-zassenhaus`, per the anchor table in
  [Phase7.md](Phase7.md)).

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
The mirrors' CI workflows are managed centrally in
`scripts/release/released-ci.yml` and published by the same guarded sync.

### The publish mechanism

Five pieces, under `scripts/release/` and `.github/workflows/`:

- `released.yml` — a per-repo manifest: which paths to copy, which
  oracles to ship, and which upstream repos to pin, in dependency order.
- `released-ci.yml` — the complete per-repository mirror workflows. Their
  repository-specific build, conformance, oracle, and bench commands remain
  explicit while cache setup and policy are uniform. The explicit cache covers
  each root/sidecar build plus published Hex dependency builds, while excluding
  the separately fetched Mathlib cache.
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

### Publishing a new library: widen a token first

The sync authenticates with the `RELEASED_SYNC_PAT` and `RELEASED_SYNC_PAT_2`
secrets, currently fine-grained tokens named `hex-publishing` and
`hex-publishing-2` owned by @kim-em. Each is scoped to an explicit list of
repositories, deliberately not to every repository, and a fine-grained token
caps how many repositories it can select — which is why there is more than
one. The sync does not care which token carries which repository: for each
target its preflight probes the tokens in order until one can see it, and
routes that repository's clone and push through that token, so a new library
goes on whichever token has room. Publishing one takes three steps in this
order:

1. create the repository under `leanprover`, give it the un-managed Lake
   skeleton, and add its managed CI workflow in hex-dev
   (`scripts/release/BOOTSTRAP.md`); the sync clones but never creates;
2. add that repository to the selected repositories of a token with room,
   with `Contents: Read and write` and `Workflows: Read and write`, and have an
   organization owner approve
   the request at
   https://github.com/organizations/leanprover/settings/personal-access-token-requests;
   find the current tokens under
   https://github.com/settings/personal-access-tokens; then
3. add its entry to `released.yml` here and run the sync.

A new source-bearing entry must name a library at `done_through: 7`; the
manifest checker rejects an entry created before the library completes the
phase pipeline. This is an admission rule, not a permanent claim that a
published library remains valid through Phase 7. If a later audit triggers the
normal rollback described in [Conventions](Conventions.md#rollback-is-a-normal-action),
keep its manifest entry so fixes continue to publish to the existing split
repository. The checker distinguishes that case from premature admission by
reading the repository names in the live `release-sync-baseline` branch, with
`scripts/release/synced.json` as the bootstrap fallback. The CI checkout must
therefore retain `fetch-depth: 0`. An entry that has never completed a real sync
still requires Phase 7 even if its intended split repository already exists.

The repository has to exist before step 2 can name it, which is why step 1
comes first; nothing in this order is circular. Step 2 is the one with a
human in the loop, so start it early. Rotating a token means redoing step 2
for everything on that token at once, so keep the secrets and the tokens
identified by name.

Skipping step 2 used to fail partway through a publish, after earlier
repositories had already been pushed: a fine-grained token simply cannot see a
repository outside its list, so the clone succeeds from public https and only
the push returns `403 Permission to leanprover/<repo>.git denied`.
`sync_released.py` now preflights every target repository against the tokens
before the first push and refuses to start, naming the repositories no token
covers. A dry run does not preflight, using no token and pushing nothing.

**What the preflight does not prove.** Its receive-pack probe verifies that a
token can push ordinary content to the selected repository. GitHub checks the
separate `Workflows: write` permission only when a push changes a workflow, so
that grant still has to be configured on every publishing token. Nor does the
probe know whether branch protection or a ruleset on a mirror's `main` would
reject the push. Those failures still surface only at push time; the invariant
the mirrors rely on is that `main` takes direct pushes from the release actor.

### Token inventory

The authoritative source for each token's selected repositories is the
GitHub UI (https://github.com/settings/personal-access-tokens); this
inventory is the durable record of that state, kept current by rule:
whoever widens a token records the change here in the same working
session. A fine-grained token selects at most 50 repositories.
Snapshot verified against the live tokens on 2026-09-03 (routing
measured by a branch-only debug step on the sync workflow counting
`route_tokens`' output; selections confirmed from the UI).

`hex-publishing` carries every repository in `released.yml` except the
four listed under `hex-publishing-2` below: 43 of 50.

`hex-publishing-2` carries 44 of 50:

- released: `hex-primality`, `hex-primality-mathlib`,
  `hex-sparse-poly`, `hex-sparse-poly-mathlib`;
- created for publication, not yet in `released.yml`:
  `hex-resultant`, `hex-resultant-mathlib`, `hex-modular`,
  `hex-modular-mathlib`, `hex-mv-gcd`, `hex-mv-gcd-mathlib`,
  `hex-mv-hensel`, `hex-mv-hensel-mathlib`, `hex-mv-factor`,
  `hex-mv-factor-mathlib`, `hex-poly-z-gcd`,
  `hex-poly-z-gcd-mathlib`, `hex-cyclotomic`,
  `hex-cyclotomic-mathlib`, `hex-finite-field`,
  `hex-finite-field-mathlib`, `hex-hermite`, `hex-hermite-mathlib`,
  `hex-int-factor`, `hex-int-factor-mathlib`,
  `hex-invariant-factors`, `hex-invariant-factors-mathlib`,
  `hex-min-poly`, `hex-min-poly-mathlib`, `hex-modular-matrix`,
  `hex-modular-matrix-mathlib`, `hex-padics`, `hex-padics-mathlib`,
  `hex-poly-smith`, `hex-poly-smith-mathlib`, `hex-smith`,
  `hex-smith-mathlib`, `hex-summation`, `hex-summation-mathlib`,
  `hex-truncated-series`, `hex-truncated-series-mathlib`,
  `hex-char-poly`, `hex-char-poly-mathlib`, `hex-graph-iso`,
  `hex-graph-iso-mathlib` (the last two pending organization-owner
  approval).

`hex-publishing-2` additionally holds organization-level permissions;
`hex-publishing` holds none.

With `hex-publishing-2` at 44, the next widening beyond six more
repositories needs a third token (`hex-publishing-3`, a new
`RELEASED_SYNC_PAT_3` secret, and one line in
`.github/workflows/sync-released.yml` and `sync_released.py`'s token
list). The sync's per-repository routing makes the split invisible to
everything else.


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
