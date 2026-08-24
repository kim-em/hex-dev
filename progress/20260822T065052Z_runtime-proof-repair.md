# Typed runtime proof adapter review repair

## Accomplished

- Renamed the supported companion to HexIntervalMathlib.RuntimeProof and
  added it to the empty sealed-import-all allowlist with ownerless
  conformance/bench unit cases and ordinary-import constructor guards.
- Reworked tree quotation into an index-ordered node fold. Each split child is
  seeded with its parent's post-chronology executable assembly, including the
  exact extended program and generation after a parent instance transition.
- Replaced quadratic chronology appends with reverse-list accumulation and
  one linear transition-bucketing pass.
- Bound each checked bundle to the exact sealed registry and removed replay's
  second quotation/decoder pass. The theorem fold retains its independent
  retained-tree and proof-limit check.
- Removed the unused bare callback quotation API, split malformed diagnostics
  by quote/event/transition/tree seam, and clarified admission/non-preemption
  and structural-transport authority in module/SPEC documentation.
- Added a conformance canary where the root instantiates before splitting and
  both children restart from the inherited extended assembly, then replay
  equality, fact, transport, and target closure. Added explicit ordinary-import
  constructor failures and clarified the guarded fallback and equality proof.
- Verified the focused target and lake build HexIntervalMathlib
  HexConformance (9627 jobs), plus DAG/unit, copyright, line-count,
  trust-surface, factor-freshness, Mathlib-free bench, and whitespace gates.

## Current frontier

- The reviewed proof-adapter blockers and relevant pre-release findings are
  repaired on the isolated local stack.

## Next step

- Restack/review the repair commit and obtain the requested exact second
  review before opening or updating the upstream PR.

## Blockers

- None.
