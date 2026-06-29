# LLL directives: SPEC-codification sections added

## Accomplished

Amended all four LLL-performance directives (#6741–#6744) with a
"SPEC codification (separate PR, only after go/no-go passes)" section, per
Kim's instruction: once the measured performance gain is confirmed, the
worker opens a separate SPEC PR, written timelessly, that makes
SPEC/Libraries/hex-lll.md *demand* the issue's trick — the acceptance test
being that a clean-room re-implementation from the SPEC alone would
reproduce the behaviour. Each section lists the minimum clauses the amended
SPEC must require, including one complexity sentence per issue that forces a
clean-room implementer to rediscover the mechanism. The in-implementation-PR
SPEC deliverables were repointed: implementation PRs now leave the SPEC
untouched, and the SPEC PR merges immediately before the implementation PR.

## Current frontier

Issues are final; no implementation started.

## Next step

Workers claim #6741 / #6742 (independent); #6743 and #6744 unblock after
#6742 merges.

## Blockers

None.
