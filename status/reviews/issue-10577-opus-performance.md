I didn't modify anything. Bash, `gh` and `lake` were mostly denied, so I didn't build or run anything. Everything below comes from the sources, the retained artifacts and the Codex transcript. The transcript shows `lake build` of all five libraries succeeding and `hexrealalgebraic_bench verify` passing all 67 targets.

## Bottom line

- **Sturm:** neither `runRetarget` nor `runPreparedCount` can honestly move to mode 2, with the same bounds or otherwise. The retained wide-ladder profile also undermines mode 2 for the whole Rat-chain n⁴ group. Both bit-size axes (coefficient and endpoint) are degenerate. `runSigns` is slower than declared.
- **HexRealAlgebraic:** citing the parent can supply the *reason* modes 1 and 2 fail for its isolator and exactifier. It cannot supply attempts, a budget or "identical computation" for `runHard*` as written. The compare family needs new measured attempts.
- **ceil and `rootCount_sturm`:** both are sound; they need only small documentation fixes.

## 1. Sturm: can `runRetarget` and `runPreparedCount` use mode 2?

**No. Three independent reasons.**

1. **Procedure.** Both were pre-registered as mode 1. The retained snapshot `prerequisite-sturm-head-wide/sturm-bit-cost-models.md.txt:343-350` shows this. A faster-than-declared result passes only for a registration that "independently qualified for mode 2 before measurement" (`SPEC/benchmarking.md:149-153, 1300-1305`). Relabelling now would choose the mode from the result. Both runs stay as failures of their declared models.

2. **Mode 2's conditions fail.**
   - The replay precedent rests on multiplying two growing integers, where GMP switches algorithms at size thresholds (`sturm-bit-cost-models.md:249-256`). These two operations never do that:
     - `withEndpoints?` evaluates only the head at ±3 (`HexSturm/Basic.lean:46-51`), so every Horner step multiplies a big number by a small one.
     - Prepared count walks a stored monic chain whose denominators are powers of two.
   - So tight bit-cost models do exist. What the derivations left out is the fixed cost of each operation (allocation, boxing, the GMP call itself). On this ladder the operands are only 2 to 26 limbs, so that fixed cost dominates.
   - The retained profile confirms this: `prerequisite-readiness-profiles/sturm-wide.summary.json`, taken on `runFieldReplay`, which uses the same Rat-chain machinery.
     - Allocation is 52.06% of samples.
     - GMP is 33.64%, but its leaves are `__gmpz_add`, `init_set`, `gcd` (2.57%), `divexact_1`, `modexact_1c_odd`, `mul_2exp` and `copyi`.
     - There is no `mul_basecase`, Toom or general gcd.
   - The cited schoolbook-multiplication and quadratic-gcd bounds therefore cover work that is absent from the profile. `SPEC/benchmarking.md:103-105` says that is not evidence.
   - My own estimate (not a measurement): at n=1024 the limb work is on the order of 1% of the 942 ms per call.

3. **For `runRetarget`, mode 2 would actively mislead.**
   - The medians are 120.4 µs, 248.4 µs, 695.9 µs and 3.205 ms. The local exponents are 1.04, 1.49 and **2.20**.
   - So the top doubling already grows faster than the proposed n² bound. The global β = −0.431 comes from the low rungs, where fixed overhead dominates.
   - `runPreparedCount`'s local exponents are 2.37, 2.31 and 2.22: falling, and never close to 3.

**What to do instead:**

- **Record the counterexample.** Put the omitted per-operation term and the limb ranges into `sturm-bit-cost-models.md`, keep the old declarations and samples, and re-derive before measuring again (`SPEC:1317-1324`).
- **`runRetarget`: mode 1 is reachable on a larger regime.**
  - It can't get there on Chebyshev. `prepare` builds a certificate, a domain, an integer certificate and a cache, and the stored chain is about n³/6 bits: roughly 90 GB at n=16384.
  - Register a new case with a prep that builds only the domain, on a head with a short chain, for example Xⁿ−2 at ±3.
  - Every step still multiplies a Θ(n)-bit accumulator by 3, so there is no short-circuit, and the work is Θ(n²).
  - Choose the ladder a priori from limb counts, for example 16384 to 131072 (about 400 to 3200 limbs). Keep the Chebyshev registration and its failure on record.
- **`runPreparedCount` and `runEndpoints`: no admissible mode on the head-degree axis.**
  - The cubic term can't dominate within memory, and no published bound covers work dominated by allocation. So use mode 3 on the top Chebyshev rung, citing both failed declarations as the attempts.
  - Add a mode-1 coefficient-size registration: a fixed short chain with b-bit coefficients at ±2 is Θ(b) linear-limb work, and reachable around b ≈ 10⁵.
- **`runInitial` and `runClearing`: raise the schedule.** Their local exponents (0.98, 1.09, 1.59 and 1.03, 1.04, 1.53) are the expected transition from n to n². Their timed bodies only need the head, so a lighter prep makes n up to 2¹⁴ to 2¹⁶ feasible. Keep n².
- **`runSigns`: a slow-direction failure (+0.483).**
  - From 512 to 1024 the time jumps 10.6×, with a 25.5% spread; one trial ran 2³ inner repeats instead of 2².
  - Use the single permitted unchanged rerun, then profile at 512 and 1024. Memory-hierarchy effects are a plausible hypothesis, but that hypothesis does not change the declared model.
- **n⁴ mode-2 group.**
  - **Rat chain** (`runPrepared`, `runCount`, `runCertificate`, the prepared variants, `runFieldReplay`, `runCachedReplay`, `runInfinite`, `runRational`, `runDomain`): don't report "within declared upper bound (observed faster)". Do a source census of the operations, as `sturm_replay_costs.py` does for replay. If it confirms there are no growing-by-growing products, give these the same treatment as prepared count.
  - **Integer chain** (`runInteger`, `runChain`, `runClear`, `runEmbed`): general `Int.mul` on growing operands does occur here, so mode 2 can stand if a profile at n=1024 shows basecase multiplication as a material share. The report must state that every observed segment is about n^1.9 to n^2.5, so the bound cannot detect a regression up to nearly n⁴.
  - **`runInfinite`'s comment** (`Frontend.lean:292-297`) reads as a two-sided derivation and has no mode-2 label.
- **Bit-size axes are degenerate** (`Frontend.lean:369-414`), so mode 2's condition 3 fails.
  - **Endpoints:** `Dyadic.ofInt (±2^b)` canonicalizes to `ofOdd (±1) (−b)` (toolchain `Init/Data/Dyadic/Basic.lean:140-146`). `hornerDyadic` then multiplies by ±1 and otherwise shifts (`HexRealRoots/Basic.lean:65-71`).
  - **Coefficients:** in (2^b+1)X²−2, P′ normalizes to X and the remainder is a constant.
  - Both are therefore Θ(b). The observed per-doubling exponents are 0.31, 0.50, 0.76, 0.73 and 0.51, 0.71, 0.79, 0.93.
  - **Fix:** use odd b-bit endpoint mantissas (and a separate fractional endpoint), and a squarefree cubic with unrelated odd b-bit coefficients. Otherwise declare mode 1 with the model `bits`.
- **Still missing:** `reports/hex-sturm-performance.md` is untouched and still counts the 8 to 20 runs as passes. `libraries.yml` has no `phase4` block. The query-degree and wide-profile artifacts are untracked.

My previous review recommended this 128 to 1024 ladder, with mode 2 "as runReplay does". For these linear-limb operations that advice was wrong.

## 2. HexRealAlgebraic: reaching Phase 4

**Does citing the parent's failed attempts satisfy mode 3?** Only for the *reason*: HexRoots' driver has only a heuristic contract (`hex-number-field-performance.md:58-97`). That is a property of the algorithm, so the citation transfers to any phase that is the same code. It applies only if the delegate's own profile on its canonical input shows that phase dominating. For `runHard*`, the claim of an identical computation fails three ways:

1. **Different root.**
   - The parent takes `isolations[0]` of `X^6-2` and a static √3 (`bench/HexNumberField/Bench.lean:972-976, 1447-1448`). HexRealAlgebraic uses `rootNear … (11/10)` (`bench/HexRealAlgebraic/Bench.lean:552-558`).
   - The eliminant isolation is the same polynomial; the subtraction eliminant is too, since X²−3 is even. Root selection differs.
   - Compare the two roots' checksums before claiming the parent's input.
2. **Different operation.**
   - The parent's 12 s ceiling times the lazy `AlgebraicRoot.add?`. Real `+` is that lazy add followed by `.exact`.
   - Canonical add measures 6.49 to 6.67 s, against the parent's 2.24 s (same-tree, single repeat) and 4.54 s (historical). So a large share of the time is outside the parent's ceiling.
   - The 12 s ceiling is therefore not a reference requirement for this operation, and exactification needs its own attribution.
3. **Nothing to inherit for the other operations.** The parent covers `AlgebraicNumber.{sub,mul,div,neg,inv,pow}` only with anchors (`report:290-304, 376-378`).

**Per arithmetic operation, what's needed:**
- a measured canonical input with an even number of AB/BA blocks;
- a profile splitting eliminant, isolation and exactification;
- the parent's reasons cited per dominant phase;
- the bare arm as a wrapper-overhead control. For Add this already works: equal hashes and indistinguishable times;
- a budget from a measured baseline plus a margin rule stated in advance. qqbar is informational and can't set the budget.

**`neg` is a Concern to resolve before budgeting.**
- `AlgebraicNumber.neg = a.toRoot.neg.exact` (`HexNumberField/Lazy.lean:333-334`) re-exactifies a value whose minimal polynomial is already known. `inv` does the same (`Lazy.lean:338-339`).
- The ceil pairs imply that negating 1+√2/2⁵⁰ costs about 0.4 to 0.6 s (408 to 589 ms before, against 9.7 to 15.2 µs after). Budgeting `neg` or `abs` would certify that cost.
- The earlier `ofRat` Concern (isolating a linear polynomial) is the same kind.

**Compare, order and rounding** (`compare`, `<`, `≤`, `min`, `max`, `sign`, the floor branch, `abs`'s test) need new measured attempts:
- The dominant code is `realCompare` (`Nearest.lean:57-67`) calling `refineTo?`, which is floored at `mahlerPrec` and runs a Newton pass with the full driver as fallback (`IsolateAll.lean:96-105`, `Refine.lean:33-39`).
- Citing the parent covers why mode 2 fails for the fallback driver. Measurement is still required because:
  - the owned SPEC already names the families: Mignotte with the bit length of a swept, cross-polynomial pairs, and point comparisons (`SPEC/Libraries/hex-real-algebraic.md:578-583`), plus the `X^8-2(256X-1)^2` fixture (`:751-754`);
  - nothing yet shows the `realCompareExact` fallback, or the driver as opposed to the Newton pass. The sweep should assert which branch each rung takes, since single-branch inputs are the best-case anti-pattern;
  - the current √2 versus √2+2⁻⁵⁰ pair (21 µs) is not a credible hard input.
- For floor and ceil, sweep n + √2·2⁻ˢ.
- Attempt a mode-1 derivation wherever the Newton pass provably succeeds.

**sqrt:** `nthRoot` isolates and exactifies every root of a degree-2d polynomial, then selects one (`Radical.lean:35-49`). That needs a radicand-degree ladder with a per-phase profile, plus attribution of the per-root exactification. The double `a < 0` guard is still there.

**Rational construction:** first attempt a source-level model in rational bit length (Newton is exact on a linear polynomial), then run a cheap bit-length ladder.

**Registrations that look like mode-1 evidence but aren't:**
- **`runExactifyRoots`** (`:462-490`) repeats the same √2 witness n times. It is a hand-rolled repetition loop, and it can only show that `Array.map` is linear.
- **`runLeafChecks`** (`:518-545`): the parameter never reaches the operations, unlike `runRootSet`. Drive the leaf instead, for example with the real root of Xⁿ−2.
- **`runSortRoots`** is valid evidence for the merge phase, but all its comparisons take the stored-interval path.

**`runHard*` hygiene:**
- None of the 16 registrations has an `expectedHash`.
- `HEX_REAL_BENCH_DEGREE` (`:554`) and `HEX_REAL_BENCH_SHIFT` silently change the canonical input.
- The AB/BA run has 3 blocks, which is odd. Only Add is measured, and `Add-2-HardBare.json` is missing although its log says it was exported.
- `verify` runs each body once. That is about 6.5 s per Add arm, and `natPow` is unknown. Measure the wall time against the 30 s soft warning before committing.

## 3. ceil

- **Correct.** `toRat?` is complete (`toRat?_eq_some`), so a non-rational value's ceiling is its floor plus one.
- **Proof and instance.** The proof structure is sound. `FloorRing` now supplies `ceil` directly, and `⌈a⌉ = a.ceil := rfl` (`Rounding.lean:142`) holds.
- **`ceil_eq`.** It moved to the companion, and there are no Mathlib-free users.
- **Evidence.** The adjacent before/after pairs have matching hashes, and the new conformance guard carries real content.
- **Fixes:**
  - add `ceil_eq` to the dictionary row (`hex-real-algebraic.md:406`);
  - document ceil's algorithm in §Rational recognition (`:296-312`);
  - the `some` branch closes by `rfl` through how Mathlib defines ceiling on ℚ. Prefer a named lemma.

## 4. `rootCount_sturm`

- **Sound.** Squarefreeness is derived from the domain via separability from ℝ to ℚ. Degree 0 is handled through `sturmChain = #[]`. No callers break.
- **Fixes:**
  - The docstring (`Rational.lean:184-187`) still says success supplies the endpoint guards. What it actually supplies is squarefreeness.
  - Its axiom guard still sits in the banned `conformance/HexSturmMathlib/Replay/Semantics.lean:159-161`.

## 5. Status tokens

The tokens say the follow-up at `6d78bf3e1` "confirms all Phase-2 exit conditions". That review listed follow-up issues as an outstanding exit action (`PLAN/Phase2.md:96-101`). Unless those issues exist, the sentence overstates.

## Priority order

1. Withdraw the mode-2 relabel idea. Record the source-level counterexample.
2. Register retarget on a short-chain family. Give prepared count mode 3 on head degree plus mode 1 on coefficient size. Raise the `runInitial` and `runClearing` schedules.
3. Do the Rat-chain operation census, and profile the integer chain at n=1024.
4. Redesign the coefficient and endpoint bit-size families.
5. Rerun `runSigns` once, then profile it.
6. For `runHard*`: add hashes, remove the env knobs, use even blocks, profile each operation, and record budgets.
7. File the `neg`, `inv` and `ofRat` Concerns against HexNumberField.
8. Run the compare, rounding, sqrt and rational sweeps.
9. Withdraw or rework `runExactifyRoots` and `runLeafChecks`.
10. Update the reports, `libraries.yml`, the SPEC rows and the token wording, and commit the untracked artifacts.
