# hex-primality: the kernel-reducible sieve (milestone 1, second half)

## Accomplished

- `HexPrimality/Sieve.lean` (583 lines, no sorries): the bitset sieve
  over residues coprime to 6, fully `@[expose]`d and structurally
  recursive, with `sieve_testBit_iff` proved with the SPEC's four
  load-bearing hypotheses. The lemma stack: exact index arithmetic
  (`numOfIndex_lt_iff` with a corrected width formula), coprime-to-6
  closure lemmas, `testBit_doubleRounds` with a per-round-truncation
  invariant, `testBit_markMask`, the bridging `mem_markPair_iff` (the
  hard center: progression membership ↔ divisibility-above-square,
  via a direct index computation instead of induction), the fold
  invariant, and `sieveGoRange_add` (the chaining lemma the batched
  replay elaborator will stand on).
- One executable-design correction discovered by the guards: the
  SPEC's unconditioned 32 doubling rounds would materialise numbers of
  `step · 2^31` bits (a native `Nat.shiftl` panic); each round now
  truncates to the width and skips shifts that alone exceed it, which
  also gives the proof its `< 2^width` invariant. Recorded in the
  SPEC, along with the exact-width mask hypothesis
  (`indexWidth bound ≤ 2^32`).
- Runtime cross-checks: the sieve at bound 100 agrees with trial
  division on every represented index (`#guard`), and at bound 10^4
  reproduces the committed 1229-entry table exactly (checked in a
  scratch run).

## Current frontier

Only PR5 remains from the plan: the `rebuild_primeTable?` batched
replay elaborator and the swap of the table's verification internals
onto the sieve.

## Next step

PR5: SieveElab.lean and the Table.lean verification swap.

## Blockers

Stacked on the bench PR (branch lineage only).
