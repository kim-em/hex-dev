# Released repos migrated from kim-em to leanprover

## Accomplished

Moved the released hex family from the `kim-em` account to the
`leanprover` org and repointed everything to match.

- **Transfers (16 repos):** `hex`, `fplll` (renamed from `fplll-ffi`),
  `hex-basic`, and the 13 splits transferred into `leanprover`. GitHub
  transfers preserve every ref, so released `main` HEADs (and the sync
  baseline) were unchanged. `hex-dev`, `lean-bench`, and the tool repos
  (`pod`, `bubble`, `lean-bench-samply`) stayed at `kim-em`.
- **Access:** a leanprover owner (Leo) granted admin via a `hex` team and
  approved the fine-grained sync PAT (write is gated on org approval,
  confirmed by a create-ref probe that 403'd pre-approval, succeeded
  after). Token stored as the `RELEASED_SYNC_PAT` secret in `kim-em/hex-dev`.
- **Sync retarget (#8505):** `rewrite_pins`/`rewrite_manifest` now match
  either owner and rewrite to the owner `released.yml` declares (the single
  source of truth) — a no-op until `released.yml` flips, so the two PRs
  compose cleanly.
- **Cutover retarget (#8506):** every `kim-em/hex*` + `fplll` reference →
  `leanprover` across READMEs, SPECs, `released.yml`, the bench doc, and
  the `fplll` oracle setup script. `hex-dev`/`lean-bench` left at `kim-em`;
  the `.claude/CLAUDE.md` symlink and the `progress/`/`reports/` journal
  untouched. Forward-looking links to not-yet-released libs
  (`hex-berlekamp-zassenhaus`) point at `leanprover`.
- **Real sync:** dispatched `sync-released.yml` (dry_run=false); published
  all 14 released repos with real `leanprover/` pins and advanced the
  `release-sync-baseline` branch.
- **Aggregate (`leanprover/hex#3`):** repointed its own lakefile/manifest
  pins to `leanprover` (same revs).
- **Bootstrap seed (#8524):** refreshed `scripts/release/synced.json` to
  the post-migration baseline (adds `hex-basic`); fallback hygiene only.
- **Branch protection:** normalized all 16 to gate merges on their actual
  CI context — `build` on the Lean libs, `build,build-macos` on `hex-lll`,
  `linux,macos` on `fplll`; `enforce_admins=false`, no required reviews.

## Current frontier

Migration is complete and verified: pins read `github.com/leanprover/...`
directly (not via transfer redirect), the sync targets `leanprover`, and
protection is consistent across the family.

## Next step

Optional tail only:
- Reservoir index entries re-point (if listed; redirects cover them meanwhile).
- Consider a family-wide review requirement if desired (none set today).

## Blockers

- **Annual PAT re-approval:** the fine-grained sync token expires (<=1yr);
  each renewal needs a leanprover owner to re-approve. Remove by switching
  the sync credential to a leanprover-owned GitHub App, or by an owner
  dropping the org's fine-grained-PAT approval requirement.
