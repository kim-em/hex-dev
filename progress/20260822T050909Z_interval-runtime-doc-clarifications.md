# Interval runtime contract clarifications

## Accomplished

- Corrected the SPEC to describe `Executable.Limits.maxQuoteCells` as an aggregate quotation-body cell cap.
- Clarified that `Runtime.FactStep.proposed` is a package annotation which need not equal the installed update fact and requires independent later proof correlation.

## Current frontier

The approved typed-runtime edge now states both quotation accounting and fact-proposal authority exactly, without changing executable semantics.

## Next step

Run focused documentation and static checks, amend the single feature commit, and update PR #9377 with an explicit lease.

## Blockers

None.
