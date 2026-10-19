I'd approve recording Phase 3 for all four libraries, provided the final CI on the whole revision passes. One problem should be fixed before merge: the new benchmark leaves CI's shared bench time cap with almost no headroom. The other findings are documentation wording. I could only read source, reports and retained artifacts: shell commands other than read-only `git` were denied, so I couldn't build anything, run Python, or see the PR body and CI logs.

## Is Phase 3 justified?

**Yes.**
- **Dependencies:** both cores have every direct dependency at 3 or higher (HexPoly 4; HexRealRoots and HexNumberField 7). The Mathlib-side dependencies are all at 7. Each core is bumped before its companion (`4a1a21035`, then `de0c7b28a`).
- **HexRealAlgebraic conformance:**
  - The module has the labelled contract docstring and at least three cases per operation, with expected values that don't come from running the code under test.
  - The shared SPEC's required core cases are all present: the Mignotte close roots, the eight sorted roots, `sqrt? (a*a) = some a.abs` for both signs of √2, the order sanity table, and the `X²+1` and coefficient-`i` rejections.
  - Every operation the fixture emitter writes has a handler and a required case set in `real_algebraic_flint.py`.
- **HexSturm conformance:**
  - It has analytic expected values: the ±1 queries, the eight Chebyshev T₈ roots, and the `F=1,-1,0,x,x-1` table.
  - It checks the rational frontend's results against the integer query, and covers transport, `checkCached` and `certifyPrepared`.
- **Companions:** per `PLAN/Phase3.md` §theory libraries, a green build is enough.
  - Neither has a conformance module, which is correct.
  - Both test targets are in `HEX_LIB_TARGETS`.
  - There are 34 axiom guards in the HexRealAlgebraicTheory tests and 50 across the Sturm tests and adapters.
  - The four libraries and the Sturm adapters contain no `sorry`, `axiom` or `native_decide`.
- **Phase 4 is not waived anywhere.** The reports, the SPECs and the evidence JSON all say it is incomplete.

## Blocking

**1. The bench verify step is close to its hard cap (High).**
- **Location:** `reports/hex-real-algebraic-performance.md:20-22` and `reports/bench-results/prerequisite-phase3-verification.json` (`benchmark_verification`).
- **The numbers:** the PR changes `ci.yml` and `lakefile.lean`, so its run was unfiltered and 336 s is the real full-suite total.
  - That leaves 24 s under the 360 s cap.
  - `hexrealalgebraic_bench` is new in this PR and takes 60 s on CI, twice the 30 s per-library soft threshold.
  - Pushes to `main` always run the full suite, and `SPEC/benchmarking.md` itself calls 2-3× run-to-run noise on GitHub runners normal.
- **Why it blocks:**
  - `SPEC/benchmarking.md` §Time budget says that when a library trips either budget, you tighten its verify-path settings. Parking this under #10577, which stays open for Phase 4, doesn't do that.
  - Phase-3 exit criterion 3 also needs the conformance tail to stay green on `main`, and an intermittently failing bench step undermines that for every later PR.
- **Fix, in this PR and without touching Phase 4 scope:** make the verify run of the `runHard*` registrations cheaper while leaving scientific/`run` settings alone. The report puts `runHard{Add,Sub}` and their bare arms at about 6.5 s per call, roughly 26 of the 32 s local verify time. Then record the new CI time. If you'd rather accept the risk, at least file a dedicated issue rather than relying on #10577.

## Non-blocking

**2. The companions' Phase-4 boundary reads as if it were only the core dependency (Medium).**
- **Location:** `reports/real-closure-prerequisites.md:17,19` ("Core-dependent Phase-4 attestation") and `HexSturmTheory/SPEC/hex-sturm-theory.md:44`.
- **What's missing:** `PLAN/Conventions.md` §Headline correctness theorem requires the headline theorem to live in the theory companion once a library reaches `done_through ≥ 4`.
  - HexSturm's semantic theorems (`query_spec`, `rootCount_eq`, …) live in `adapters/` (built through `HexQuerySemantics`), outside the `HexSturmTheory` target, until #10575 lands.
  - None of the four SPECs names a headline theorem.
- **Fix:** add this to the Phase-4 column, or say why the adapters are enough. This is a documentation fix only, not work to do now.

**3. The HexRealAlgebraicTheory SPEC contradicts itself (Low).**
- **Location:** `HexRealAlgebraicTheory/SPEC/hex-real-algebraic-theory.md`.
- **The contradiction:** lines 23-27 say the array obligations are unimplemented and excluded. Lines 52-53 still say "The new array obligations have conformance and performance evidence in `HexRealAlgebraic`".
- **Made worse here:** the new Phase-3 sentence is appended directly after line 53.
- **Fix:** put lines 52-53 in future tense ("will need … when implemented").

**4. Stale and hard-coded phase wording (Low).**
- `HexSturmTheory/README.md:53-55` still says ordinary-kernel correctness checks "remain required".
- `HexSturmTheory/SPEC/hex-sturm-theory.md:42-43` says scaffolding is "attested at Phase 2 in `libraries.yml`", but the file now records 3.
- All four SPECs gain "The library records Phase 3 in `libraries.yml`". `HexSturm/SPEC/hex-sturm.md:26` already defers to `libraries.yml`, and the project's CLAUDE.md asks SPECs to state design rather than status, so these lines go stale at the next bump.
- **Fix:** keep only the pointer to `libraries.yml`.

**5. The HexSturm oracle "Mode" line overstates coverage (Low).**
- **Location:** `conformance/HexSturm/Conformance.lean:20-22` says "required (shared CI oracle)".
- **Why it overstates:**
  - HexSturm has no entry in `run_oracles.sh`, so under `SPEC/testing.md:188-190` a HexSturm-only PR runs no oracle at all.
  - The shared oracle checks HexRealRoots' `ZPoly.tarskiQuery`, not HexSturm's own code.
- **Fix:** say "none for HexSturm-owned code; checked against `ZPoly.tarskiQuery`, whose integer fixtures `realroots_flint.py` checks on HexRealRoots PRs and on `main`."

**6. SPEC-edit rationale (verify only).**
- `1a103e78c` (sqrt) and `5c04decbb` (ceiling) edit `SPEC/Libraries/hex-real-algebraic.md`.
- `PLAN/Conventions.md` §SPEC immutability requires a stated rationale in the PR description for such edits. I couldn't read the PR body to confirm it's there.

## Evidence chain

- **What the green CI covers:** run 36972953823 tested `54fd06b`.
- **What changed after it:** `4dd0014c9` edited both conformance modules, and `8545f2012` changed `HexRealAlgebraic/Roots.lean` and `HexRealAlgebraicTheory/Sqrt.lean`.
- **What the local runs cover:** the recorded local builds after those commits cover conformance, adapters, the bench, the fixture emitter and the companion tests.
- **What only the final CI will cover:** the full graph, including the `HexManual` chapter that calls `sqrt?`. The 15412-job full build predates the sqrt change.

The reports already say the final CI is what makes the bump stick, so merge has to wait for it, and #10577 should stay open.

## Response and verification boundary

The documentation findings are incorporated: the readiness matrix lists headline correctness and bridge-target reconciliation; forward array obligations use future tense; SPECs point at phase metadata; ordinary-kernel checks are named; and the oracle contract describes ownership filtering. The PR description gives the ceiling/square-root SPEC rationale.

The bench-cap concern is retained, with a narrower assessment of the available remedy. `LeanBench.Verify.verifyFixedOne` already invokes the runner once in-process with no warmup or tuning, so lowering repeats or tuning cannot reduce these calls. `SPEC/benchmarking.md` expressly forbids replacing a canonical fixed input with an easier smoke input. The same policy labels the 30-second threshold a soft warning, and requires the full-suite cap to pass. The current hard-call costs and the 24-second headroom remain documented under the assigned performance/readiness issue #10577; no workaround decomposition issue, easier-input substitution, cap increase, or verification bypass is introduced. Final required CI remains the merge gate. Phase 4 remains incomplete.
