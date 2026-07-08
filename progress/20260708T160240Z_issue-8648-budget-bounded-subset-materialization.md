**Accomplished**

Fixed #8648 (eager size-level materialization in the classical size loop).
The surviving cases from #8535/#8537 were quotient sub-searches (and
non-default-budget callers) inheriting a mid-level budget: the size loop
built all `C(r-1, d)` splits of an unaffordable level via
`(subsetsOfSizeWithComplement tail d).map`, then tried only a handful.

Chose the value-preserving option (lazy materialization) over re-aligning the
sub-search budget, because re-alignment shifts the decline boundary and needs
trace-baseline regeneration, whereas the bounded generator changes nothing the
search actually tries.

- `HexBerlekampZassenhaus/Recombination.lean`: added `subsetsOfSizeWithComplementTake`,
  a budget-bounded generator that builds at most `n` splits and never enumerates
  the level above `n` (0-budget subtrees return immediately). Size loop now feeds
  it the running `budget`. Existing size-loop soundness proofs are generic over
  the split list, so unchanged.
- `HexBerlekampZassenhausMathlib/RecombinationCandidate.lean`: proved
  `subsetsOfSizeWithComplementTake_eq` (= `(...).take n`),
  `subsetsOfSizeWithComplementTake_length_le`, and
  `scaledRecombinationSmartCandLoop_take` (candidate loop over `splits.take n`
  equals over `splits` when `budget ≤ n`; the loop consumes at most `budget`).
- `HexBerlekampZassenhausMathlib/SmartSearchCoverage.lean`: in the two size-loop
  coverage proofs, realign the now-bounded `hcand` back to the full enumeration
  via the two bridging lemmas, leaving the covering-subset argument unchanged.

**Current frontier**

Full `lake build` green (4143 jobs). Regenerated `bz.jsonl` fixtures are
byte-identical to committed (`diff` empty), so `bz_trace_gate.py` passes with no
baseline change — the decline boundary is provably unchanged. Generator is
empirically efficient: first 5 of `C(40,20)` instantly, full `C(12,6)=924` when
budget exceeds the level. Second opinion (Codex) found no correctness issues;
addressed its one Low flag by tightening the docstring and adding the
`length_le` lemma.

**Next step**

Open the PR from branch `issue-8648`; FLINT oracle (`bz_flint.py`) runs in CI
(python-flint not installed locally). Watch CI for the classical-tier bench
wallclock step.

**Blockers**

None.
