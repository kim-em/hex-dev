# Accomplished

- Preserved the generic shared-host default of eight whole-pair retries while
  raising the explicit hard cap to 32.
- Opted only the HexRCF proof sweep into that cap because its preregistered
  double-degree-50 magnitude control is the longest arm and exhausted all nine
  attempts in the first schema-v6 collection attempt.
- Kept every admission threshold, accounting identity, preflight gate, and
  fail-closed partial-artifact rule unchanged.
- Added a suite-level retry bound to `SweepSpec`, so a shared-host run must use
  the exact preregistered value: 32 for HexRCF and the default 8 elsewhere.
- Added parser tests for the default, canonical and alias forms of the hard
  cap, rejection outside the valid range, exact 33-attempt exhaustion, and the
  HexRCF canonical command.
- Passed all 73 shared sweep tests plus Phase-4, DAG, and diff checks.
- Obtained an independent exact-diff GO; the admission gates and audit trail
  remain unchanged.

# Current frontier

The retry-headroom change is prepared as a separate milestone stacked after
the schema-v6 contract correction.

# Next step

Review and validate the narrow change, merge it after the contract PR, then
run the complete schema-v6 artifact from the resulting clean main commit.

# Blockers

None.
