## Review of PR #10580 at `6d78bf3e1` (Refs #10577)

My earlier Phase-2 conditions are met. The problem is the Phase-4 evidence. The new Chebyshev head-degree registrations look like they pass, but they don't count as mode-1 evidence. The harness never fitted a slope, and the ladder crosses Lean's small-`Int` boundary partway up. The array models are fine, and so is the prepared-query degree work (though that run isn't committed yet). No HexRealAlgebraic operation has a mode or budget yet. For the fixed wrapper operations, mode 3 can be inherited from the parent for arithmetic and root isolation, but not for comparison, square roots or rounding.

What I couldn't check: `lake`, `gh` and most shell commands were denied. So I did not build, check CI or read the PR body. Everything below comes from the sources, the committed artifacts and the untracked worktree artifacts.

## Phase-2 conditions

| Library | Condition at `4f44b8060` | Status at `6d78bf3e1` |
|---|---|---|
| HexSturm | none | still justified |
| HexSturmMathlib | SPEC marks adapter ownership and cites #10575; `query_sound` gets the domain conjunct | **Met.** The preamble names `HexQuerySemantics` and #10575 (`HexSturmMathlib/SPEC/hex-sturm-mathlib.md:181-187`). `query_spec` (`adapters/HexSturmMathlib/Soundness.lean:103-114`) adds the conjunct and keeps `query_sound`. Its axiom guard is in `Replay/Semantics.lean:155-157`. |
| HexRealAlgebraic | none | still justified. The `abs` fallback comment cites `normSq_nonneg` and `sqrt?_isSome`; both exist. |
| HexRealAlgebraicMathlib | fix `Audit.lean` | **Met.** It is out of the umbrella. The duplicate and tautological probes are gone, and the docstring is accurate. One caveat is finding 5. |

Follow-ups:
- **Done:** `ceil` (`Order.lean:84-87`), the shared SPEC's sqrt text, the `Roots.lean` docstring, and the `sturmCount` agreement (finding 4).
- **Still open:** the `sqrt?` double guard (`HexRealAlgebraic/Roots.lean:126-131`), `rootCount` routed through `query … 1` (`HexSturm/Basic.lean:157-159`), Tau-Ceti-free lemmas still in adapters, and no `K →+* R` corollary.
- **Phase 2 exit:** `PLAN/Phase2.md:96-101` expects follow-up issues for these. Open them or list them in the PR.
- **Token wording:** the tokens cite source `4f44b8060`, but describe the fixed state as if it were unconditional. Add a line saying the conditions were confirmed at `6d78bf3e1`.

## Findings

### 1. High: the head-degree Chebyshev registrations are not mode-1 evidence

**Where:**
- `bench/HexSturm/Frontend.lean:9-19, 105-236`: the 11 new frontend registrations.
- The same defect applies to the existing head-degree registrations `runInteger`, `runRational`, `runDomain`, `runChain`, `runEndpoints`, `runSigns`, `runInitial` and `runClearing`. `reports/hex-sturm-performance.md:628-629` counts these as mode-1 passes.

**The verdicts came from a fallback, not a slope fit:**
- With five rungs, `verdictWarmupFraction = 0.2` drops n=8. The remaining span is ln(20/10) = 0.69, which is under 1, so `fitSlope` returns none (`.lake/packages/lean-bench/LeanBench/Stats.lean:121`).
- The verdict then falls back to cMax/cMin ≤ max(1.50, e^(0.15·0.69)) = 1.50 (`Stats.lean:181-191`; defaults at `Core.lean:278,286,298`). Every verdict in `sturm.log` shows β unfitted.
- Over a 2× range, that check accepts any exponent within ±0.585 of the declared one. Two registrations were very close to failing even so: `runEmbed` had a ratio of 1.481 and `runRetarget` 1.457.
- I fitted the slope myself (OLS) over the retained rungs. Against the declared model, the slopes are:
  - `runCount` −0.20
  - `runPrepared` −0.19
  - `runEmbed` −0.58
  - `runRetarget` +0.56
  - `runPreparedCount` −0.11

  At the 0.15 tolerance, most of these would be inconclusive.

**The "bounded coefficient" premise is false inside the ladder:**
- On this toolchain `LEAN_MAX_SMALL_INT` is `INT_MAX` (`lean4-v4.35.0-rc3/include/lean/lean.h:1826`). So any `Int`, including a `Rat` numerator, at or above 2³¹ is a GMP bignum.
- The chain is T_n, U_{n-1}, …, U_0, up to positive scale. After normalization, U_k's coefficients are ±C(k−j,j)/4^j. Coefficients therefore have Θ(k) bits, not bounded height.
- Endpoint values at ±2:
  - T_20(2) ≈ 1.4·10¹¹, about 2³⁷;
  - T_16(2) ≈ 7·10⁸.

  So the head's endpoint values cross 2³¹ between n=16 and n=20, the top rung.
- Retargeting evaluates at ±3:
  - T_12(3) ≈ 7.7·10⁸;
  - T_16(3) ≈ 8.9·10¹¹.

  The measured `runRetarget` C jumps from 447 to 578 exactly between n=12 and n=16, a local time exponent of 1.89 against a declared 1.
- The PR's own n=20 profile shows 38.1% of leaf samples in GMP and 38.4% in allocation (`prerequisite-readiness-profiles/sturm-head.summary.json:226-230`).
- The existing report already says this:
  - the head ladder uses the range check (`hex-sturm-performance.md:58-61`);
  - replay operands reach 31, 42 and 57 bits at n = 12, 16 and 20 (`:105-109`);
  - unit-cost models "do not establish the wall-time characterizations on these mixed arithmetic regimes" (`:110-115, 318-324`).

**Uniform bit cost:** the stored chain is Θ(n²) coefficients of Θ(n) bits, so Θ(n³) bits. Endpoint Horner passes are Θ(n³) bits. Retargeting is Θ(n²) bits, not Θ(n). Rational gcd normalization can add more on top.

**The timed bodies also hash every coefficient:** `certHash` and `integerHash` allocate and visit each boxed value, so the work of consuming the result grows with bit size too.

**Fix:** follow the precedent already set for `runReplay` (`hex-sturm-performance.md:342-425, 502-552`).
- Use one arithmetic regime with at least one retained log unit of span, for example n ∈ {128, 256, 512, 1024}. With four rungs nothing is dropped, and the span is ln 8.
- Derive the model from the closed-form chain above.
- If allocation versus limb work rules out a single power law before measurement, declare mode 2 with GMP's schoolbook bound, as `runReplay` does.
- Relabel the 8–20 registrations as finite-regime anchors that do not provide coverage, or remove them.
- Rewrite the commit message's "Measurements do not fit these declarations", which reads as the opposite of what is meant.

### 2. Medium: query-degree evidence is uncommitted, and the top rung peaks at 34 GB RSS

**Where:** `Frontend.lean:256-286`, with the run in the untracked `reports/bench-results/prerequisite-prepared-query-degree/`.

**Evidence:**
- The m² model is sound and matches the validated `runRationalHigh` (`hex-sturm-performance.md:427-435`).
- The untracked run passes with real slope fits: β = −0.066 and −0.077 over ln 8.
- Peak RSS at m = 2²⁰ is 33.8 GB (`prepared-query.log:22`). The value-only `queryPrepared` builds the whole certificate, so it keeps the Θ(m²)-bit quotient: about m²/4 bits, which is about 34 GB.
- The qqbar comparison runs are also untracked.

**Fix:** commit both directories. List the memory behaviour of the value path as a Concern.

### 3. Medium: HexRealAlgebraic has no operation with a mode or budget

**Where:** `bench/HexRealAlgebraic/Bench.lean:102-107, 323-398`. Every fixed case uses a 1 s operational cap, and its comment says it makes no performance claim. That is accurate.

**What's missing:**
- The owned SPEC has no Phase-4 or comparator section. Grep finds nothing in `HexRealAlgebraic/SPEC/hex-real-algebraic.md`. Shared SPEC lines 570-650 are the excluded forward extension.
- There is no `phase4` block (`libraries.yml:1506-1515`).
- There is no `reports/hex-real-algebraic-performance.md`.

**Array models are sound:**
- `runPolyConstructors`, `runMembership` and `runRootSet` have fitted slopes over ln 8 (β = −0.115, −0.107 and 0.000).
- Their values ofRat(1..n+1) have about log₂ n bits, so they stay scalar until n ≈ 2³¹. Here the finite-regime result and the word-RAM result agree.
- One wording fix: "bounded-height" should be "word-size height".

### 4. Low-medium: `rootCount_sturm` carries premises it does not need

**Where:** `HexSturmMathlib/Rational.lean:188-210`, and the SPEC sentence edited to match at `hex-sturm-mathlib.md:254-258`.

**Problem:**
- The `squarefree` premise follows from `result`. The query domain requires a squarefree head, and you can get there via `query_rat_domain` and `squareFreeRat_iff`.
- `degree` rules out nonzero constants, which the domain explicitly admits (`:130-131`). On those, both sides are 0.
- The docstring says success "supplies" the endpoint guards, but the proof never uses them. `query_rat_count` is already half-open.

**Fix:** derive squarefreeness, handle degree 0 separately, and restore the SPEC sentence.

### 5. Low: `Audit.lean` sits in a banned location (my earlier advice was wrong)

**Where:** `conformance/HexRealAlgebraicMathlib/Audit.lean`, built through `lakefile.lean:1152`.

**Problem:** `SPEC/testing.md:341-351` bans conformance sources owned by proof-only `*Mathlib` libraries. The repo already breaks this rule in places (`HexSturmMathlib.Replay`, `HexSignDetMathlib.*`).

**Fix:** use a compliant home instead:
- in-file guards, as `Laws.lean:65` and `RealClosed.lean:53` do; or
- a `Hex*Tests` default-target library, as in `lakefile.lean:513-515`.

### 6. Low: smaller issues

- **Cache hit:** `runCachedReplay` never asserts that the cache actually hits. Make `prepare` fail when `i.cache` is none (`Frontend.lean:49-50, 95-98`).
- **Close fixture:**
  - `HEX_REAL_BENCH_SHIFT` changes the Lean close pair, but the qqbar side always uses 2⁻⁵⁰ (`scripts/oracle/real_algebraic_bench.py:18`). The comparison hash (0, 1 or 2) cannot detect that the fixtures differ.
  - The overlap check is skipped when the shift is under 50 (`Bench.lean:54-56`).
- **Lint:** in `runBareNeg`, `runBareInv`, `runBareNatPow` and `runBareIntPow`, `b` is bound but never used, which will trigger unused-variable lint warnings (`Bench.lean:296-321`).
- **Profile metadata:** `prerequisite-readiness-profiles/metadata.json` lists one case out of six. The other manifests do carry their commands.
- **Root-arrays profile:** it was taken at n = 32768, outside the 16–256 ladder.

## Phase 4: what is still required

These exclude the forward comparison strategies, publication, and theorem-only timing.

**Both computational libraries:**
- Phase 3 first. Phase 4 needs `done_through ≥ 3` (`PLAN/Phase4.md:3-5`).
- The Mathlib companions follow their computational dependencies and have no Phase-4 deliverables (`PLAN/Phase4.md:218-225`).

**HexSturm:**
- Finding 1, for both the new and the existing head-degree registrations.
- Commit the query-degree evidence (finding 2).
- Register the remaining axes as cases with a mode. Today the axis run (`hex-sturm-performance.md:223-255`) is descriptive only. The required axes are:
  - endpoint size, which HexSignDet varies;
  - infinite endpoints, which nothing registers;
  - coefficient size.
- Assert the cache hit.
- Add `phase4.comparators` to `libraries.yml`. python-flint and Z3 can be declared per surface as `no-comparable-surface-in-named-comparator`. The rational-versus-integer `compare` group must report `allAgreed`.
- Add a query-degree frontend profile (`:653-654`).
- Update the report:
  - Bench targets (`:619-624`) omits the 13 frontend registrations;
  - give a per-mode rationale under Verdicts;
  - empty the Concerns section.

**HexRealAlgebraic:**
- Write a shipped-surface Phase-4 section in the owned SPEC.
- Add `phase4` with five input families, matching the existing profiles, and comparators. Declare qqbar informational.
- Write the headline report.
- Give each operation a mode, using the plan below.
- Record these Concerns:
  - Rational arithmetic costs about 1.4 ms per call, and 91.8% of that is spent in `ZPoly.isolateComplexRoots?` (`rational-recognition.summary.json:161-166`). That code belongs to HexNumberField.
  - The `sqrt?` double guard.

## Mode-3 assessment for the fixed wrapper operations

**What the profiles show:**
- `runAdd`: 99.8% inside the owner's isolation and exactification.
- `runCloseCompare`: 97.8% in the owner's `realCompare` refinement.
- `runRoots`: 96.5% in `isolateComplexRoots?`.

That is enough for the Attribution rule. It is not enough for mode 3 by itself. Mode 3 needs, for each operation, attempted parameterisations that failed, a canonical hard input, and a ceiling with a stated justification (`SPEC/benchmarking.md:118-133`).

| Group | Can it inherit mode 3 now? | What is needed |
|---|---|---|
| add, sub, mul, div, inv | **Yes**, through the parent's failed `runLazyAddLadder` and `runExact*`/`runCanonicalRepLadder` (`hex-number-field-performance.md:364-372, 674-682`). | Cite those ladders as this operation's attempts, and argue that the wrapper adds only the O(1) `pack` tag test. Use the real member of the parent's top-rung input, not √2/√3. Budget: the parent's declared ceiling on that input, as a reference requirement. Run an adjacent AB/BA `runX`/`runBareX` pair; both already use `algebraicChecksum`, so set equal `expectedHash` values. |
| neg, natPow, intPow, smul | **No** matching parent mode-3 ladder. | Attempt one first: exponent bit-length for pow, degree for neg. Inherit only if neg reuses the exactify route. |
| compare, `<`, `≤`, min, max, sign, floor, ceil, the negative branch of `abs` | **No**: the parent has no LeanBench `realCompare` registration. | Register a separation ladder s ∈ {64, …, 2048}: (a, a+2⁻ˢ), a·2⁻ˢ, 1+a·2⁻ˢ, prebuilt, asserting which branch runs at each rung. Try mode 1. Use mode 2 only with a bound that covers the implemented Taylor/Newton refinement. Otherwise use mode 3 on the shipped Mignotte fixture (`SPEC/Libraries/hex-real-algebraic.md:751-754`), with a ceiling from qqbar (protocol-subtracted, same pair) or from a baseline plus a stated margin. The disjoint-interval branch gets a mode-1 constant model over a degree ladder. |
| sqrt?, sqrt, complex `abs` | **No**: the owner's `nthRoot` is unregistered. | Ladder over radicand bit length, then mode 3 with a qqbar `sqrt` ceiling. |
| roots, `realAlgebraicRoots` | **Isolation only**, via `runAlgebraicRootsLadder`. | The wrapper's per-root exactification is separable work: `realRoots` → `ofRoot?` accounts for 48% inclusive (`real-polynomial-roots.summary.json:193-210`). Run a ladder over r, the number of roots, on prebuilt root sets, generalizing `runFilterRoots`. Use the eight-root product as the end-to-end mode-3 input. |
| ofRat and casts | **No.** | Ladder over rational bit length, plus the Concern above. |
| conj, toRat?, toAlgebraic, ofAlgebraic?, accessors, re/im on real input, Repr | **Not applicable.** | These should be mode 1, not anchors: model `1`, or linear for Repr, over a degree ladder, as `runRootSet` already does. |

**Budget order:**
1. When the input is the parent's own canonical input, use the parent's ceiling.
2. Otherwise, use the paired bare-route median times (1 + a margin), with the margin taken from the retained AB/BA spread.
3. Record qqbar ratios as information only (`SPEC/Libraries/hex-real-algebraic.md:633`).
