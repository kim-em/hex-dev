# LLL verified end-to-end

Interactive session (Kim): audited LLL verification, drove all remaining
work to completion via `pod once`.

## Accomplished

LLL is now verified end-to-end on `main` (c0120073). ZERO sorry / axiom /
native_decide across HexLLL, HexLLLMathlib, HexGramSchmidt,
HexGramSchmidtMathlib.

Started from 5 sorries (after discovering the checkout was 3 commits stale;
the GramSchmidt 6463 sorry was already closed upstream). Closed all of them
plus proved genuine end-to-end correctness:

- Termination sorry: replaced well-founded recursion (unimplementable in the
  Mathlib-free layer) with fuel-bounded structural recursion (#6568), then
  proved the fuel always suffices: swapStep preservation (#6575), swap
  strict-decrease (#6579), fuel sufficiency `lllLoop_fuel_sufficient`
  (#6586).
- gramDetVecEntry leading-prefix (#6561), mem_latticeSubmodule_iff (#6560),
  short-vector Steps 1/3/transport (#6559/#6569/#6573).
- SPEC correction: `SPEC/Libraries/hex-lll.md` termination section rewritten
  to the as-built fuel design with the rationale for rejecting WF recursion
  (#6578) — so a clean-room implementer follows a faithful blueprint.
- End-to-end capstone: loop-invariant pieces (#6591/#6592/#6593) composed
  into `lll_isLLLReduced` (output is reduced) and
  `lll_first_row_norm_sq_le_unconditional` (unconditional short-vector
  bound on lll's actual output), plus the EuclideanSpace transport (#6594).

Key end-to-end theorems (HexLLLMathlib/Independent.lean):
- `lllLoop_fuel_sufficient` — fuel bound always suffices.
- `lll_isLLLReduced` — `lll` output is LLL-reduced for independent input.
- `lll_first_row_norm_sq_le_unconditional` — first row of `lll` output is a
  short lattice vector, no isLLLReduced hypothesis.

## Process notes

- Worked from /tmp/hex-work + GitHub to avoid disturbing the uncommitted
  `fmaAddDivExact` perf experiment in the main checkout.
- Closed superseded GramSchmidt issues #6423/#6424/#6425; replanned #6382.
- Reaped two ~2-day zombie pod sessions (#2567, #6418) to free leases.
- Three workers correctly diagnosed under-scoped directives (swapStep_valid
  needed unchanged-entry lemmas #6572; capstone too large -> decomposed into
  #6587-6590). Fixed a backwards depends-on the decomposition introduced.

## Current frontier / Next step

LLL is complete. Open item for the owner: directive #6440 (Schur rewrite)
proof content shipped via #6554; only bench/report deliverables may remain
— close or re-scope.

## Blockers

None.
