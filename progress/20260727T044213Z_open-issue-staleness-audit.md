# Open-issue staleness audit

**Accomplished**

- Audited the nine unclaimed issues other than HexNumberField M2 against
  current `origin/main`, issue comments, merged PRs, SPEC commitments, and
  current implementation surfaces.
- Confirmed that #8851, #8852, and #8744 still describe present implementation
  gaps; #8853 is current but deliberately a non-claimable tracking issue.
- Confirmed that #8751 remains current under its owner-comment reframe, while
  its original Phase-4-blocking premise is obsolete.
- Identified substantive directive drift in #8664 and #8569: #8664's BZ
  consumer/gate and one-final-reduction shape no longer match the evidence or
  current HexMatrix SPEC, while #8569's dependencies have landed and its
  harness/report still use the retired `Hex.factor` surface.
- Confirmed #8369 and #8370 remain real SPEC gaps but are intentionally parked;
  their current owner comments provide the required post-refactor name mapping.

**Current frontier**

- No audited issue is wholly superseded with all deliverables complete.
- #8664 needs a major rewrite (or closure and replacement) before it is safe to
  claim; #8569 needs a smaller rebase/rewrite before execution.
- #8369/#8370 should remain out of the near-term worker queue until the lattice
  tier stabilizes, and #8853 should remain outside it until its stage-zero
  architecture decisions are made.

**Next step**

- If requested, update the stale issue bodies/comments and labels, then produce
  a reduced claimable queue containing only current directives.

**Blockers**

- None for the audit. The `coordination` helper remains unavailable, but this
  pass concerns directive validity rather than active claims.
