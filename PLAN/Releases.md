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
  `HexRootsMathlib.isolateComplexRoots` wrapper for complex roots and the
  `isolate_roots` elaborator for repeated real roots.

## Release readiness predicate

A release `R` is ready when, computed from `libraries.yml`:

> **every named library and transitive dependency `L` in `R.libraries` has
> `done_through ≥ 7`**
> **and `R.integration-example` builds and its test passes in CI**.

`scripts/status.py release <N>` computes the dependency closure from
`libraries.yml` and evaluates this predicate without building anything:
it checks that the integration example exists and is in the
`HexReleaseExamples` target that `ci.yml` builds, so the build half of
the predicate is the CI result for the commit being released.

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
checked as the chapters elaborate. To produce the browsable site, run
`Main.lean` in the interpreter, which renders it to static HTML:

    lake build HexManual HexManual.Theme
    lake env lean --run Main.lean --output _out

Rendering through the interpreter avoids compiling Mathlib and every Hex
library imported by the manual to C, which a native executable requires.
Verso's own modules are precompiled, so the render still runs Verso natively.

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

The first two lines are the product; a mirror receives them and nothing else,
plus the library's README. The rest are development instruments: they build in
this monorepo's shared root Lake graph, run in this monorepo's CI, and are
never published. A mirror is therefore a single root Lake project whose Lake
file the sync generates on every publish (see *The generated Lake file* below);
`scripts/release/BOOTSTRAP.md` documents the few files a new mirror starts
with. The mirrors' CI workflows are managed centrally in
`scripts/release/released-ci.yml` and published by the same guarded sync.

"Nothing else" is computed, not listed. `allowed_paths` in `sync_released.py`
derives what each mirror may contain from its manifest entry — the managed
paths, the workflows `released-ci.yml` declares for it, and the generated Lake
file and the few skeleton files the sync does not author — and `prune_unmanaged` deletes the rest of the clone
before anything is copied in, so a library admitted to the manifest inherits
the policy without a cleanup list of its own. Nothing else under `.github/`
survives, so a mirror cannot accumulate a workflow beside its build-only
one, and a mirror carries neither a `reports/` tree nor `.claude/` notes beyond
the figures its entry names. The `pins_only` aggregate is exempt, since its
umbrella module, lakefile and documentation tree live only in the released
repository, though its lakefile and umbrella module are generated too.
`keep_paths` is the
escape hatch for a mirror-local file outside both sets; one entry uses it, for
`hex-test-kit`'s fixed `HexTestKit.lean` umbrella. Because it can only
preserve, a forgotten entry appears as a deletion in the dry run instead of as
an over-published mirror, which is the failure mode a per-entry deletion list
had backwards.

### The publish mechanism

Six pieces, under `scripts/release/` and `.github/workflows/`:

- `released.yml` — a per-repo manifest: which paths to copy, which mirror-local
  paths to keep, and which upstream repos to pin, in dependency order.
- `released-ci.yml` — the complete per-repository mirror workflows. Each entry
  under `workflows:` is one
  ubuntu job that builds the published library and its regression target;
  repository-specific build commands remain explicit while cache setup and
  policy are uniform. The explicit cache covers the library build plus
  published Hex dependency builds, while excluding the separately fetched
  Mathlib cache.
- `sync_released.py` — the driver. For each repo it clones `main`, deletes
  everything outside the entry's allowance, overwrites the managed paths from
  this tree, rewrites the cross-repo Lake revisions, and commits to `main`.
  `--dry-run` prints the planned changes, one line per deletion, without
  pushing; run it first.
- `synced.json` — the baseline seed (see below).
- `sync-released.yml` — a manual workflow (`workflow_dispatch`, dry by
  default). One dispatch drives the whole publish.
- `consumer_check.py` — builds a fresh downstream Lake project against the
  trees a dry run stages with `--stage`, the way a user would `require` and
  `import` them. `sync-released.yml` runs it on Ubuntu, macOS and Windows and
  publishes only after it passes; see
  [SPEC/CI.md §Release consumer check](../SPEC/CI.md#release-consumer-check).

Each mirror's own CI runs on the sync's push, so a mirror whose published tree
does not build reports it directly, on the commit that caused it. That CI builds
each mirror as a root package, which cannot show what a downstream user meets;
the consumer check covers that, before anything is pushed.

### The generated Lake file

Each mirror's Lake file is rendered by `render_lakefile` in `sync_released.py`
on every publish, from `released.yml` and this monorepo's `lakefile.lean`;
nothing in it is maintained by hand. It contains:

- the package, with native Verso docstrings enabled;
- a `require` at the shared release version for every published library the
  library depends on (per `libraries.yml`) or its sources import directly, and
  one for Mathlib, Batteries or Tau Ceti when the sources import them, at this
  monorepo's locked inputs;
- the library's `lean_lib` with this monorepo's build settings
  (`precompileModules`, link objects and arguments), and any declarations the
  entry lists under `lake_declarations` (native targets, and carrier libraries
  such as `HexArithNative`), copied verbatim;
- a `lean_lib` for any library shipped through `extra_paths`, and the
  `<Lib>Tests`, `<Lib>Modules` and executable targets for the entry's
  `test_modules`, `build_modules` and `executables`.

The `hex` aggregate's lakefile requires every `aggregate:` library, and its
`Hex.lean` imports each of them, so a newly published library reaches the
aggregate in the same publish. The format (TOML or Lean) follows the entry's
`lakefile` field, because downstream lockfiles record which file to read; an
entry whose build settings only Lean can express must use `lakefile: lean`, and
`check_released_manifest.py` renders every entry to catch that before a
release. How a library is built is therefore decided in one place, this
monorepo's `lakefile.lean`, and a mirror cannot keep a stale target, lose a
setting, or miss a dependency.

The lockfile is rewritten, not generated: Hex packages move to the release tag
and its exact commit, external packages to this monorepo's locked revisions, a
published dependency the lockfile has never seen is appended, and each
package's `inherited` flag follows whether the generated Lake file requires it
directly.

### The Lake cache

hex-dev publishes its own compiled oleans to a Cloudflare R2 bucket from
`.github/workflows/ci.yml`, and a consumer can fetch them with `lake cache get`.
The released mirrors briefly did the same. They no longer do, because measuring
it showed the fetch cost more than the reuse saved.

The bucket is `hex-cache`. Uploads are signed against R2's S3 API; downloads are
plain unauthenticated GETs, because Lake's fetcher sends no credentials, so they
go through the bucket's public host instead. Hence two endpoint pairs, and hence
the bucket must stay publicly readable.

Each mirror still carries the credentials, so re-enabling publishing is a change
to `released-ci.yml` alone rather than a re-provisioning exercise:

| name | kind | purpose |
| --- | --- | --- |
| `HEX_LAKE_CACHE_KEY` | secret | R2 token, `<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>` |
| `HEX_LAKE_CACHE_ARTIFACT_ENDPOINT` | variable | signed S3 host, uploads |
| `HEX_LAKE_CACHE_REVISION_ENDPOINT` | variable | signed S3 host, uploads |
| `HEX_LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` | variable | public host, downloads |
| `HEX_LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` | variable | public host, downloads |

The names are Hex-specific because a bare `LAKE_CACHE_KEY` would collide with
any other Lean project in the organization.
`scripts/release/provision_cache_secrets.sh` sets all five on every repository in
`released-ci.yml`, plus hex-dev; it is idempotent, and `--check` takes no token
and reports what is unprovisioned. The token lives at
`~/.config/hex/lake-cache-key`, mode 600. R2 shows a secret key once, so a lost
file means minting a replacement: run the script with no token and it prints
that procedure, including how to verify the new token first.

#### Why the mirrors stopped publishing

Publishing worked. All 56 mirrors uploaded, the objects were publicly readable,
and a consumer fetched every map and all 1128 artifacts they referenced. The
problem was on the consuming side, and it was quantitative rather than a
failure. Against a downloads-only cache with every Hex build directory wiped:

| package | modules recompiled | time |
| --- | ---: | ---: |
| HexMatrix | 0 | 2s |
| HexModArith | 2 of 96 | 43s |
| HexGF2 | 10 | 171s |
| HexGraphIso | 64 of 91 | 367s |

Restoration is real, but the modules that fail to restore are consistently the
expensive ones, so the wall clock barely moves while the fetch adds two to three
minutes. End to end in the blog's CI, measured twice with identical results: 41
minutes with the cache against about 31 without.

What distinguishes the modules that never restore is still unknown. It is not
`native_decide` (one module in the whole graph uses it), not a Mathlib revision
difference (identical), not the upstream pins, and not `precompileModules`. Nor
is it a root-versus-dependency effect: a minimal two-package reproducer, one
published as root and consumed as a dependency, restores perfectly, with and
without `precompileModules`, so cross-workspace reuse is supported.

Anyone picking this up again should start by identifying what those expensive
modules have in common, not by re-checking the transport, which is sound.

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

1. create the repository under `leanprover` with the starting files
   `scripts/release/BOOTSTRAP.md` lists, and add its managed CI workflow in hex-dev
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
When preparing a new mirror, the agent must choose one token using this
inventory and the 50-repository limit, record the allocation, and give the
user clickable [token settings](https://github.com/settings/personal-access-tokens)
and [Leanprover approval](https://github.com/organizations/leanprover/settings/personal-access-token-requests)
links. Name the selected token explicitly; do not offer alternatives or ask
the user to track allocations or capacity. Keep requested allocations distinct
from confirmed selections and approved grants. If the token's numeric ID is
available, link directly to its edit page.

Snapshot verified against the live tokens on 2026-09-03 (routing
measured by a branch-only debug step on the sync workflow counting
`route_tokens`' output; selections confirmed from the UI) and updated
from the UI on 2026-09-05 for the number-field batch.

`hex-publishing` carries the previously released repositories in
`released.yml` except the ten existing mirrors listed under
`hex-publishing-2` below: 48 of 50. The ECPP repositories are selected on
`hex-publishing-2`, as listed below. The
number-field batch (`hex-number-field`, `hex-number-field-mathlib`,
`hex-number-field-tower`, `hex-number-field-tower-mathlib`, `hex-rcf`)
is on this token.

`hex-publishing-2` has 50 confirmed selected repositories, filling its
50-repository limit:

`hex-ecpp` and `hex-ecpp-mathlib` are selected. Their Leanprover organization
approval is pending; the token owner cannot approve
their own request. The new `hex-lattice-enum` and
`hex-lattice-enum-mathlib` empty repositories are also selected on this token
and awaiting organization approval. The existing `hex-perm-group` and
`hex-perm-group-mathlib` mirrors are also selected. Both lattice libraries
are at Phase 7; repository
reservation alone does not publish their sources or admit them into the
release manifest.

- selected for publication, approval pending: `hex-ecpp`,
  `hex-ecpp-mathlib`, `hex-lattice-enum`, `hex-lattice-enum-mathlib`,
  `hex-perm-group`, `hex-perm-group-mathlib`;
- released: `hex-primality`, `hex-primality-mathlib`,
  `hex-sparse-poly`, `hex-sparse-poly-mathlib`, `hex-resultant`,
  `hex-resultant-mathlib`, `hex-graph-iso`, `hex-graph-iso-mathlib`;
- created for publication, not yet in `released.yml`: `hex-modular`,
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
  `hex-char-poly`, `hex-char-poly-mathlib`.

The ECPP, lattice and permutation-group additions on `hex-publishing-2`
are awaiting
[organization-owner approval](https://github.com/organizations/leanprover/settings/personal-access-token-requests).
The token owner cannot approve their own request. Each publishing token needs
Contents and Workflows read/write; the latter permits changes to the mirrors'
managed `.github/workflows/ci.yml`. Keep selected repositories and approved
write grants distinct in this inventory.

`hex-publishing-2` additionally holds organization-level permissions;
`hex-publishing` holds none.

The [last real publishing preflight](https://github.com/kim-em/hex-dev/actions/runs/34687426921)
reported no Contents write grant for `hex-perm-group` or
`hex-perm-group-mathlib` on either token.
Their baseline entries and release tags do not prove publishing-token
coverage; failed preflights can still advance the baseline branch. The error
cannot distinguish an unselected repository from a pending or read-only
grant. Approved access must be checked separately from confirmed selections.

`hex-publishing-2` has no free slots. Allocate new batches of up to two
repositories to `hex-publishing`, which has two remaining slots; larger batches
need a third token
(`hex-publishing-3`, a new `RELEASED_SYNC_PAT_3` secret, and one line in
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

## Bootstrapping a split mirror

A new manifest entry needs an existing public repository and a publishing
write grant before it can join the release graph. Its initial unmanaged
skeleton contains the Lake configuration, `lean-toolchain`, license,
`.gitignore` and a `lake-manifest.json` generated by `lake update`. The
companion template in
[`scripts/release/skeletons/hex-ecpp-mathlib`](../scripts/release/skeletons/hex-ecpp-mathlib)
provides the Lake files, lock and toolchain, with explicit Mathlib and AINTLIB
requirements and the native IO sidecar. Copy the root license and add the
mirror’s `.gitignore` separately.
Keep Mathlib last when resolving this template so its compatible transitive
pins win over AINTLIB's older dependency lock; the sync preserves that order
when adding Hex requirements.

Add the repository to either fine-grained publishing token with Contents and
Workflows read/write, and approve the organization grant. The managed mirror
CI, library sources, README and SPEC are then supplied by the ordinary sync.
Validate a standalone build and published trust-test target against compatible
published upstreams, followed by the guarded dry run against the live release
baseline. A local prospective source split does not discharge that upstream
publication gate. Initial skeleton preparation does not publish the library.
