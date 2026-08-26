# hex-primality: manual chapter

## Accomplished

- New `HexManual/Chapters/HexPrimality.lean` reference chapter,
  registered in `HexManual.lean` under the unreleased-drafts section
  (first among drafts; it depends only on hex-arith/hex-basic).
  Sections: the decision surface (`isPrime` / `isPrime?` with checked
  `#eval` output, Miller-Rabin's filter-only role), the `primality`
  tactic (all syntax forms, the composite failure message as a
  checked `+error` block), the Mathlib companion (`prime_iff`,
  `Nat.Prime` goals, the per-file `norm_num` opt-in with worked
  examples), certificates (a hand-committed Mersenne-31 `PrimeCert`
  replayed by `decide +kernel` in the chapter itself,
  `prime_of_checkPrimeAt`, `primeCert?`, `rhoFactor?`), the table and
  `primesIn` (checked segment output), and a short "Reach" section
  recording the measured size guidance.
- `scripts/release/check_manual_split.py` passes (19 released, 9
  draft); `lake build HexManual` green with no warnings from the new
  chapter.

## Current frontier

Chapter content tracks the implemented surface at the tip of the
primality stack. The `#rebuild_primeTable` command is mentioned but
not demonstrated (running it in the manual would print a 4-state
verification block).

## Next step

When hex-primality is released, the include moves from the drafts
section to the released list (ordering enforced by
`check_manual_split.py`).

## Blockers

None.
