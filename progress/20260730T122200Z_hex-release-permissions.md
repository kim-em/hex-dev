# Hex release permissions

## Accomplished

- Confirmed that `kim-em` is an active member of the `leanprover`
  organization and can create both public and private repositories.
- Confirmed direct repository-admin access on the existing Hex repositories
  and maintainer membership in the `hex` team.
- Confirmed that the `hex` team has admin access to the released Hex
  repositories and that a repository admin can attach the same team to newly
  created repositories.
- Verified that `RELEASED_SYNC_PAT` exists in `kim-em/hex-dev`.

## Current frontier

No organization-owner grant appears necessary to create and administer the
two new repositories. After creation, they should be attached to the `hex`
team with admin permission and checked for direct `kim-em` admin access.

## Next step

Create the repositories only when the release-preparation branch is ready,
attach the `hex` team, install the standard skeletons and branch protection,
then exercise the sync dry run.

## Blockers

GitHub does not expose the stored release token's type or repository
selection. If `RELEASED_SYNC_PAT` is fine-grained and restricted to selected
repositories, an organization owner may need to approve or extend it to the
new repositories.
