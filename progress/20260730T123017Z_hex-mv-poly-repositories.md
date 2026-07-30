# HexMvPoly release repositories

## Accomplished

- Created the public `leanprover/hex-mv-poly` repository.
- Confirmed that GitHub immediately granted `kim-em` direct repository-admin
  permission despite the organization-level member role.
- Created the public `leanprover/hex-mv-poly-mathlib` repository and confirmed
  the same direct admin permission independently.
- Left both repositories empty so their first commits can be the intentional
  release skeletons rather than disposable placeholders.

## Current frontier

Both destination repositories exist and are administrable by `kim-em`. Neither
has a team attached, a commit, or a default-branch protection rule yet.

## Next step

Prepare and push the standard unmanaged skeletons, grant the `hex` team admin
access, then land the monorepo manifest changes and exercise the release-sync
dry run.

## Blockers

The stored release token's access to these newly created repositories remains
unknown until the sync dry run or a purpose-built authenticated check exercises
it.
