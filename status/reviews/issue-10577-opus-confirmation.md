No merge-blocking correctness bug, but the PR is not ready to merge yet. It has three evidence and contract problems that are cheap to fix, and HexSturm is not Phase-3 eligible.

I reviewed HEAD `4b0ab3f5b` plus the ceiling and `rootCount_sturm` commit `5c04decbb`. I couldn't build, run Python, fetch, or read the PR body or CI, because those commands were denied, so this comes from the source and the retained artifacts. The Codex session log does show both conformance modules building after the last errors were fixed.

## Fixes to fix before merge

1. **The bench-verify time claim gives the wrong cap and leaves out a tripped warning** (`reports/hex-real-algebraic-performance.md:15-18`).
   - The report says 37 s "against the 600-second operational cap". CI actually sets `BENCH_VERIFY_HARD_CAP_SECONDS: "360"` (`.github/workflows/ci.yml:479`); 600 is only the script's default.
   - The retained log shows `hexrealalgebraic_bench verify took 32s (> 30s soft threshold)` (`prerequisite-verify-budget.log:564`). That was on the shared host; GitHub runners are typically 2–3× slower.
   - `SPEC/benchmarking.md` §Time budget says a library that trips either budget must tighten its fast-path verify settings or file an issue. Neither was done.
   - Most of that time is `runHard{Add,Sub}` and their bare arms, about 6.5 s per call. State the real cap, record the warning, and either act on it or list it as an open item under #10577.

2. **The readiness report overstates Phase 3.** `reports/real-closure-prerequisites.md:73` says "Full required CI gates Phase-3 recording", which reads as if only CI stands between these libraries and Phase 3. The gaps under the Phase 3 heading below say otherwise; reword it.

3. **The conformance docstrings still don't follow the required format.** `SPEC/testing.md` §Per-library module contract says every library at `done_through ≥ 2` MUST open with labelled **Oracle:**, **Mode:**, **Covered operations:**, **Covered properties:** and **Covered edge cases:** fields, as bulleted lists.
   - This PR raises HexSturm to 2 and HexRealAlgebraic to 2.
   - Both modules use prose labels instead ("Operations:", "Properties:", "Edges:", and an inline "oracle none, mode always"): `conformance/HexSturm/Conformance.lean:19-29` and `conformance/HexRealAlgebraic/Conformance.lean:9-25`.
   - About 60 other conformance modules use the labelled form. The content is now right; only the format needs changing.

## Smaller issues

- `bench/HexSturm/Frontend.lean:494-496`: the `runFractionalBits` comment still says "mode 2" and "fractional endpoints exercise GMP multiplication". The report now calls this family unadmitted with no profile of its own. The ten translated families were relabelled in the source; this one was missed.
- `reports/hex-sturm-performance.md:741` still says "The candidate family passes above".
- `hex-real-algebraic-performance.md:24` puts "negative/near-zero branches" in the Registrations column, but no registration has that name.
- `hex-real-algebraic-performance.md:16` says "smoke-gate log", which uses two words on the banned-vocabulary list.
- **Consistency to settle in Phase 4, not caused by this PR.** The translated families are now unadmitted because their profiles are dominated by `addmul_1`, copies and single-limb work, with no caller attribution.
  - The headline `runReplay` mode-2 O(n⁴) pass (`hex-sturm-performance.md:6`, `523-536`) rests on a profile of the same shape.
  - That pass is admitted through an explicit total-work bound: products plus O(n³) storage. The same kind of argument would cover the fixed-degree translated families.
  - Pick one admission rule and apply it to both.
- **Hard-arithmetic provenance.** The new sentence says the runs used the default degree and separation settings. The best support for that is not mentioned: the observed hashes match the current fixed expected hashes (`Add-0-Hard.log:6` and `Bench.lean:597`, both `0x7cc18faa80303c8`). Cite it.
- The scaffolding-reviewed tokens cite source commits from before the ceiling rewrite. They could also cite `status/reviews/issue-10577-opus-final.md`.

## Previous findings, checked

| Finding | Status |
| --- | --- |
| HexSturm contract content, `checkCached`, `normalize` | Fixed in content, format still open (item 3). |
| Real constructor, scalar, sqrt and polynomial-conversion cases | Added, three values each (zero, −3/2, irrational). |
| `sturm_semantics_sweep.py` paths | Fixed. |
| Benchmark names | Fixed. Every name in the table is registered; `runSqrtTotal` and `runProjections` are in. |
| Historical baseline | Fixed. The timeouts are now labelled as coming from the executable before the ceiling fix, and the report says no replacement baseline exists. |
| Translated and fractional families | Unadmitted in the report and the cost model. The fractional source comment is still stale. |

- **`checkCached` coverage:** it covers a hit, no cache, and a miss on a foreign context, plus rejection of the wrong context, stale endpoints, and a corrupted identity on the hit path.
- **`normalize` coverage:** expected values follow from the SPEC, including a negative leading coefficient.
- **Ceiling:** correct. `ceil_toReal` is proved by cases on `toRat?`, `FloorRing` uses the executable ceiling, and `ceil_eq` was moved to the companion with no remaining Mathlib-free user. The `some` branch still relies on Mathlib's internal Rat definition lemmas, which is a style point.
- **`rootCount_sturm`:** sound. It derives squarefreeness from the query succeeding and handles nonzero constants through the empty chain.

## Phase 3

Both cores have their dependencies at Phase 3 or later (HexPoly at 4; HexRealRoots and HexNumberField at 7). The companions must wait for their cores, and for them Phase 3 is just a green build.

**HexRealAlgebraic: close.** What remains:
- **Natural casts:** no case at all.
- **Integer casts:** only in the compiled `Checks.integerRounding` (`Checks.lean:79-82`). That runs in the emitter, not at elaboration, so the "≥1 elaboration-time check" rule is not met.
- **Polynomial conversion** (`Conformance.lean:163-168`): only checks two constructors against each other. Both use the same `AlgebraicPoly.ofArray` normalization, and no case has irrational coefficients or trailing zeros going through `ofAlgebraic?`.
- **re/im:** the elaboration-time check only uses real inputs, but the oracle-checked emitter fixtures cover nonreal ones, so this is acceptable.

**HexSturm: not yet.** What remains:
- **`certifyPrepared`:** one case only (`Conformance.lean:71-78`).
- **Transport steps:** `RemainderStep.clearDenominators` and `SignedRemainderChain.clearDenominators` are only exercised indirectly.
- **Head degree:**
  - Every head is degree 2 or less: `Fixtures.lean:17`, plus `TarskiTests.p` and the noncanonical head.
  - So no chain ever has more than one three-term step. `SPEC/testing.md` §Profile sizes expects degree 8–12, or a comment explaining the smaller size.
  - Add at least one degree-8 or higher head with irrational roots and analytically known counts, for example a Chebyshev polynomial.
- **Docstring format** (item 3).

Phase 4 stays incomplete as stated, and nothing here argues for a blanket rerun or closing #10577.
