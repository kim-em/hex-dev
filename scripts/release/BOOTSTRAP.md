# Bootstrapping new released repos

`scripts/release/released.yml` lists every repo the publish sync
(`sync_released.py`, driven by `.github/workflows/sync-released.yml`)
regenerates from this monorepo. The sync **clones each repo's `main`**, overwrites
its *managed* paths, rewrites its cross-repo Hex pins, and pushes. It does **not**
create repos and does **not** author their non-managed skeleton (root lakefile,
`lean-toolchain`, `lake-manifest.json`, LICENSE, README, CI). A new repo must be
bootstrapped with that skeleton **before** its first sync.

`synced.json` is deliberately **not** seeded for new repos: a repo absent from the
baseline has no uncoordinated-commit guard, so the first real sync publishes it and
advances the baseline (committed to the `release-sync-baseline` branch). Never seed
a placeholder/zero SHA — any truthy baseline that differs from the cloned `main`
HEAD makes the sync skip the repo.

## The six repos added for the HexMatrix split

Computational (Mathlib-free), then their Mathlib bridges:

| repo | lib | direct upstream `require`s | lakefile |
|---|---|---|---|
| `hex-row-reduce` | `HexRowReduce` | `hex-matrix`, batteries | toml |
| `hex-determinant` | `HexDeterminant` | `hex-matrix`, batteries | toml |
| `hex-bareiss` | `HexBareiss` | `hex-determinant`, batteries | toml |
| `hex-row-reduce-mathlib` | `HexRowReduceMathlib` | `hex-row-reduce`, `hex-matrix-mathlib`, mathlib | toml |
| `hex-determinant-mathlib` | `HexDeterminantMathlib` | `hex-determinant`, `hex-bareiss`, `hex-matrix-mathlib`, mathlib | toml |
| `hex-bareiss-mathlib` | `HexBareissMathlib` | `hex-determinant-mathlib`, mathlib | toml |

`require`s list only **direct** dependencies; Lake pulls the rest transitively.
The full transitive Hex closure that the sync keeps pinned is the `pins:` list for
each repo in `released.yml`.

## Procedure (per repo)

Model the skeleton on the closest existing released repo: `hex-gram-schmidt` for a
computational lib that pins an upstream Hex repo, `hex-matrix-mathlib` for a
Mathlib bridge.

1. `gh repo create kim-em/<repo> --public`
2. Author the skeleton on `main`:
   - `lean-toolchain` — copy from `hex-matrix` (`leanprover/lean4:v4.30.0-rc2`).
   - `lakefile.toml` — `name`, `defaultTargets = ["<Lib>"]`, a `[[require]]` per
     direct upstream (batteries and/or mathlib, plus each upstream Hex repo by its
     `github.com/kim-em/<repo>.git` URL), and `[[lean_lib]] name = "<Lib>"`.
   - `lake-manifest.json` — for a **computational** repo, copy `hex-gram-schmidt`'s
     (two packages) and adjust the Hex entries. For a **Mathlib bridge**, copy
     `hex-matrix-mathlib`'s manifest verbatim (the mathlib transitive closure is
     identical at this toolchain) and add/adjust the Hex package entries. The Hex
     revs are placeholders here — the sync rewrites them on first publish.
   - LICENSE, README.md, AGENTS.md, `.gitignore`, `.github/` CI, `.claude/` — copy
     from the closest existing released repo.
   - The bench/conformance sub-project lakefiles, if `bench`/`conformance` is true
     for the repo in `released.yml`, mirroring the matching sub-project skeleton.
3. Commit and push `main` (the skeleton does not build standalone until its
   upstream Hex repos have been published — that is expected).

## First publish

Once all six repos exist with `main`:

1. Ensure this monorepo is at or ahead of every released repo's `main`.
2. Dispatch `.github/workflows/sync-released.yml` with `dry_run=true`; confirm the
   planned managed-path writes and pin rewrites for all thirteen repos, with no
   uncoordinated-commit skips.
3. Dispatch again with `dry_run=false`. The topological order in `released.yml`
   guarantees each upstream is published (and its new SHA known) before its
   downstream consumers are pinned. The run advances the baseline on the
   `release-sync-baseline` branch.

Finally, update the released-set list in the top-level `.claude/CLAUDE.md` to name
the six new repos.
