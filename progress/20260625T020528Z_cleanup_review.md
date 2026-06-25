# Cleanup PR dangling-reference review

## Accomplished

Reviewed the post-extraction cleanup surface for over-deletion and dangling
references involving the extracted Matrix, Gram-Schmidt, LLL, and bridge
libraries. Checked current oracle scripts, conformance fixture targets, CI
workflows, SPEC links, report links, and retained shared oracle helpers.

## Current frontier

The cleanup is mostly correct for executable CI/oracle wiring, but live SPEC
prose and some report drafts still contain local relative links to files that
were deleted or moved to extracted repositories.

## Next step

Patch the remaining live SPEC/report links to external repository URLs or remove
the stale references from monorepo-level documentation.

## Blockers

No blockers for this review.
