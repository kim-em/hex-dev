# Review of PR #10580 (Refs #10577)

I reviewed the committed head `4f44b8060`. The worktree also contains uncommitted changes that are not in the PR: an untracked `bench/HexSturm/Frontend.lean` with 11 `setup_benchmark` registrations, an untracked `reports/bench-results/prerequisite-readiness-models/`, and edits to `bench/HexRealAlgebraic/Bench.lean`, `bench/HexSturm/Bench.lean`, `lakefile.lean` and `scripts/check_dag.py`. These are presumably the live Codex session's next step. None of them is evidence for this PR until committed. With them excluded, the report's statement that the Sturm frontend operations are "unregistered" is accurate.

Overall: the PR is honest about not claiming Phase 4. The `done_through: 1` bumps for HexSturm and HexSturmTheory are justified. Its main defects are a few evidence claims that overstate what was delivered, and a benchmark file whose docstring doesn't match some timed bodies.

## Findings on the PR itself

**1. Medium: "independent rational fast path" overstates the code.**
- **Where:** `reports/real-closure-prerequisites.md` (HexRealAlgebraic row) and the `HexRealAlgebraicTheory/Audit.lean` docstring.
- **Problem:** rational arithmetic has no fast path. `ofRat` goes through `rational?`, which runs `ofEliminant?` and `exact?` (`HexNumberField/Roots.lean:334-341`). `+`, `-`, `*`, `neg` and `inv` all run a lazy eliminant and then exactify (`HexNumberField/Lazy.lean:321-343`). The baseline shows about 380 µs per `ofRat` and about 1.45 ms for `runRational`.
- **What does exist:** rational recognition through `toRat?`, and `toRat?`-first rounding (`Order.lean:70-72`). The new `#guard`s show that results stay at degree 1, which says nothing about speed.
- **Fix:** reword the claim to "rational recognition and `toRat?`-first rounding". A real arithmetic short-circuit would belong to HexNumberField, not to this wrapper.

**2. Medium: `Audit.lean` claims more than it checks, and is in the wrong place.**
- **Docstring:** it says the checks run "independently of the field law witness". `#print axioms` cannot establish that. It says it covers "total wrapper fallbacks", but the `*_isReal` closure lemmas behind `Internal.pack` are not guarded. "Ordinary-kernel trust checks" also misdescribes what `#print axioms` does.
- **Examples:** example 2 is a tautology (`toRat?_eq_some.mpr rfl`). Example 1 is an unnamed copy of the SPEC's required `realCompare_eq_exact` corollary (`SPEC/Libraries/hex-real-algebraic.md:452-454`).
- **Duplicate guards:** three guards repeat existing ones: `realCompare_eq` (`HexNumberFieldTheory/Nearest.lean:383`), `instLaws` (`Laws.lean:65`) and `instIsRealClosed` (`RealClosed.lean:53`). Two guard HexNumberFieldTheory's own theorems.
- **Placement:** it is `public import`ed into the published umbrella `HexRealAlgebraicTheory.lean:26`. The only precedent for that is `HexRationalFnTheory.Tests`.
- **Fix:**
  - Move it to a conformance or test module, following the `conformance/HexSturmTheory/Replay/Semantics.lean` pattern.
  - Drop the duplicates and the tautological example.
  - Correct the docstring.
  - Leave `realCompare_eq_exact` to its owner, HexNumberFieldTheory. It sits in the forward-specified comparison section, so it should not be filled in here as an anonymous example.

**3. Medium: problems in `bench/HexRealAlgebraic/Bench.lean`.**
- **Vacuous registration:** `runRootSet` times `realRoots (.finite #[])`, a closed empty set (46 ns). It exercises none of the wrapper's exactify, filter and sort work. Replace it with a prebuilt nonempty `RootSet` held in an `IO.Ref`, including nonreal roots.
- **Docstring contradicts the bodies:** it says operand construction is outside timed bodies, but four bodies include it:
  - `runRational` times `ofRat`, about 26% of its median.
  - `runRepeatedRoots` times `ofRat`, two multiplications and a negation.
  - `runRoots` times `-a`, about 0.93 ms.
  - `runComplexAbs` times `ofPoint`.
- **Comparison coverage:** `runCompare` uses √2 against √3. Their stored intervals are disjoint, so it only ever exercises the first branch of `realCompare` (425 ns). Bounded refinement and the `realCompareExact` fallback are never reached. The SPEC's Mignotte close pair (`hex-real-algebraic.md:751-754`) is the obvious fixture.
- **Single-branch fixtures:** `runSign` and `runAbs` only take positive input. The negative branch of `abs` does a full canonical negation.
- **Missing registrations:** `AlgebraicNumber.re`, `im` and `ofReal` (`HexRealAlgebraic/Complex.lean`) are not registered. `normSq` only gets real input.
- **Hashes:** no registration sets `expectedHash`. The local `checksum` also differs from the owner's `algebraicChecksum` in `bench/HexNumberField/Bench.lean`. Using the owner's checksum would let a wrapper case reproduce the owner's hash for the same input, a free cross-check.
- **Caps:** 30 s `maxSecondsPerCall` with `killGraceMs := 0` across 31 cases. The owner uses 0.5 to 0.75 s caps. Tighter caps would bound the cost of a hang in CI `verify`.
- **Dangling reference:** every registration comment says "audited in the report", but there is no `reports/hex-real-algebraic-performance.md` and no `phase4` block for HexRealAlgebraic in `libraries.yml`.

**4. Medium: the HexSturmTheory SPEC contradicts itself about where theorems live.**
- `HexSturmTheory/SPEC/hex-sturm-theory.md:181` says "Theorems below live under `HexSturmTheory`".
- But six rows in that table are proved only in `adapters/HexSturmTheory/Soundness.lean`, outside the library target: `query_sound`, `queryPrepared_sound`, `countPrepared_sound`, `countPrepared_nonneg`, `rootCount_eq` and `query_sign`. The status section and `hex-sturm.md:258-262` say so correctly.
- `query_sound` (`Soundness.lean:103-105`) concludes only the value equation. SPEC line 190 requires the `Domain(P;a,b) ∧` conjunct as well, which `check_sound` does provide.
- A Phase-1 deferral is acceptable because #10575 owns publication. Fix:
  - Mark the adapter-owned rows and cite #10575 in the SPEC.
  - Add the conjunct to `query_sound`, or amend the SPEC row.

**5. Low to medium: the new Sturm report sections are thin.**
- **Ownership:** most rows in the new "Bench targets" table time HexRealRoots operations, not HexSturm ones: `runInteger`, `runInitial`, `runChain`, `runEndpoints`, `runReplay` and the `*High` variants. Only `runRational` (`query`) and `runDomain` (`prepare`) measure HexSturm code.
- **Comparator ratios:** the section contains a promise, not ratios.
- **Concerns:** there is one item, pointing at the issue this PR itself references.
- **Fix:** list the actual concerns, all of which follow from Phase 4 below:
  - frontend operations with no committed registration;
  - no `comparators` block at `libraries.yml:1570-1575`;
  - no frontend profile;
  - unswept axes: endpoint size, coefficient size, infinite endpoints.

**6. Low: SPEC and README wording.**
- `HexSturm/SPEC/hex-sturm.md:25-27` now says "Remaining Phase-4 evidence is required" and then repeats it.
- Phase counters in SPEC prose ("Scaffolding is attested at Phase 1") go stale. The repo's convention is current design in the SPEC and phase state in `libraries.yml`. Drop the counters from the prose.

**7. Low: PR body and report style against your rules.**
- The title has no `<type>:` prefix.
- The body doesn't open with "This PR …".
- The PR body and the report both say "smoke cases", a banned word.
- The PR body says "Full local build and compiled conformance/oracle verification are running". That will be stale once they finish, so update it then.
- `cli-failure-*` records a usage typo (`--export`), not a measurement. Keeping it is harmless.

## Phase-2 token verdicts

I checked every library against the Phase-2 rules: grep for `sorry`, `axiom`, `native_decide`, `@[extern]`, `implemented_by` and the banned placeholder words; trivial or placeholder bodies; algorithm shape; and imports against the declared dependencies. **All four came back clean, with no blockers.**

| Library | Token justified? | Conditions and follow-ups |
|---|---|---|
| **HexSturm** | **Yes** | See below. |
| **HexSturmTheory** | **Yes, once the SPEC is reconciled** | See below. |
| **HexRealAlgebraic** | **Yes** | See below. |
| **HexRealAlgebraicTheory** | **Yes, once `Audit.lean` is fixed** | See below. |

**HexSturm.**
- Every operation in the SPEC table has a real body in `HexSturm/Basic.lean`: `prepare`, `withEndpoints?`, `query`, `queryPrepared`, `countPrepared`, `rootCount`, `certify`, `certifyPrepared`, `certifyCountPrepared` and `check`.
- The ordering guarantees match the SPEC: guards run before the shortcuts, the squarefree test checks for a constant terminal remainder, and normalization divides by the positive absolute leading coefficient.
- Optional follow-ups:
  - `rootCount` (`Basic.lean:157-159`) goes through `query … 1`. The shared `certify` then builds `build p 1` twice (`HexRealRoots/Tarski.lean:147-149`). Route it through `prepare` and `countPrepared` instead.
  - `Transport.lean:18-36` recomputes `ZPoly.clearDenominators` several times per chain entry. Compute it once per entry.

**HexSturmTheory.**
- Every theorem in the SPEC table is proved. Downstream callers already satisfy the interpretation hypotheses (for example `adapters/HexSignDetTheory/RootModel.lean:76`).
- `query_nonneg` and `rootCount_map` justify the `Int.toNat` in `rootCount` with no clamping.
- **Conditions:** finding 4, meaning the SPEC table marks adapter ownership and cites #10575, and the `query_sound` conjunct is fixed.
- **Follow-ups:**
  - `rootCount_isSome`, `orderSign_eq` and `sign_spec` don't need Tau Ceti. Move them into the published `Domain.lean`.
  - The agreement theorem with `ZPoly.sturmCount` that `hex-sturm-theory.md:156-158` requires does not exist. Either add it or drop the sentence.
  - Add a canonical `K →+* R` specialization corollary, which HexRealClosureTheory will want.

**HexRealAlgebraic.**
- The carrier, checked constructors, pack-and-recheck arithmetic, square-and-multiply powers, `compare = realCompare` (`Order.lean:20`) and the root-solving shape (exactify, filter, then merge-sort by `realCompare`) all match the SPEC.
- Imports stay inside HexNumberField's closure, so it stays independent of the real-closure family.
- **Follow-ups:**
  - `sqrt?` repeats `sqrtRoot?`'s `a < 0` guard (`Roots.lean:126-131`), so it runs two exact comparisons. The SPEC wants `sqrtRoot?` to be the pure root selection.
  - `ceil` is `-(-a).floor` (`Order.lean:81`), so every irrational `ceil` pays a canonical negation and exactification. In the baseline, `runRounding` (928 µs) roughly equals `runNeg` (929 µs). Computing `ceil` directly from the same precision-2 enclosure avoids that.
  - The shared SPEC (line 244) says square roots use "the real-root API". The code and the owned SPEC use the complex principal square root. Align the two texts.
  - The `abs` fallback in `Norm.lean:24` lacks its unreachable-by-pipeline-invariant classification.

**HexRealAlgebraicTheory.**
- Every name in the inventory at SPEC lines 398-408 is present, and each statement is at least as strong as the SPEC requires:
  - `contains_roots_iff` holds for all real `x`.
  - `roots_multiplicity` uses `rootMultiplicity`.
  - `roots_sorted` is strict.
  - `roots_all_iff` is an iff.
- **Condition:** finding 2.
- **Minor:** fix the stale docstrings at `Roots.lean:120` ("nonzero" on an unconditional statement) and `HexNumberFieldTheory/Nearest.lean:193`.

**Excluded-extension boundary.** The PR places the excluded material "at the end of" Exact comparison strategies. In fact the whole section is forward-specified (`SPEC/Libraries/hex-real-algebraic.md:414-650`), except the "Existing canonical comparison" subsection (431-458). That subsection is the shipped `realCompare`, and `realCompare_eq` fully covers it. The `sort_perm`, `min?_eq`, `compareArray_eq` and `compareIndex_eq` obligations in the owned `HexRealAlgebraicTheory/SPEC` belong to the excluded part, but that file doesn't say so. Add a forward marker there so a later reviewer doesn't flag them as missing Phase-1 declarations.

## Phase 4: what owner evidence covers, and what needs new evidence

### HexRealAlgebraic

**Arithmetic is genuinely a thin wrapper.** `pack` adds only an O(1) side-tag test (`HexNumberField/IntegerRoots.lean:41-42`). On the same √2/√3 inputs the wrapper is within 1 to 3.5% of the owner: add, sub, mul, div, neg, inv and natPow. The owner timings come from `hex-number-field-api-surface-fixed.json`, a different session, so treat the comparison as orientation only.

**There is less owner evidence to cite than it looks.**
- HexNumberField's `runAlgebraic*` API registrations are modeless fixed checks with 0.5 to 0.75 s safety caps. Under PLAN/Phase4.md:160-163 they cannot satisfy operation coverage.
- What is citable is the phase-level evidence:
  - `runAddEliminantLadder` (mode 1);
  - `runLazyAddLadder` and the `runExact*` and `runCanonicalRepLadder` ladders (mode 3);
  - `runQAdjoinApprox` (mode 3);
  - `runAlgebraicPolyOfArray` and `runAlgebraicPolyBeq` (mode 1);
  - `runAlgebraicRootsLadder` (mode 3).
- `realCompare` and `nthRoot`/`sqrt` have no owner LeanBench registration at all, only the custom `algebraic-fast-compare` subcommand.

**Local registrations are required either way.** PLAN/Phase4.md:155-157 requires them in the library's own Bench exe, so citing the owner cannot replace them.

| Group | What it needs |
|---|---|
| add, sub, mul, div, neg, inv, natPow, intPow, smul, ofRoot?, approx, `==`, `ofArray` | **Owner covers the cost.** Cite the owner phase registrations above as the attribution argument, plus the O(1) pack test. Register locally in mode 3, with the budget set to the owner-route time on the same input plus a stated margin. A `compare` group pairing each wrapper op with the bare `AlgebraicNumber` op is the strongest evidence. |
| ofRat and casts | Owner coverage is modeless and weak; about 380 µs each. |
| compare, <, ≤, min, max | **New evidence.** All three branches, using the Mignotte close-pair family, with preconstructed and cached runs kept separate (SPEC:606-608). Mode 1 if a refinement model can be derived, otherwise mode 3 with a qqbar-derived budget. |
| sign, abs | **New evidence.** Needs near-zero and negative inputs. |
| floor, ceil | **New evidence.** Needs near-integer irrational inputs; the `ceil` negation cost is a candidate Concern. |
| sqrt?, sqrt, complex `abs` | **New evidence.** Mode 3; the owner `nthRoot` is unregistered. |
| RealAlgebraicPoly.roots, ZPoly.realAlgebraicRoots | **New evidence.** The wrapper's exactify-every-root, filter and sort costs are separable work, so the Attribution rule needs its own registration. Run against the owner's `runAlgebraicRootsZ` on the same quartic, alternating AB/BA, to attribute the sort cost. Include the SPEC's eight-root product. |
| re, im, ofReal | **New evidence.** Currently not registered at all. |
| conj, toRat?, ofAlgebraic(?), toAlgebraic, Repr, RealRootSet accessors | **Fixed anchors only**, labelled as such. |

**Comparators.**
- python-flint's qqbar is already the pinned conformance oracle and exposes a comparable surface for arithmetic, comparison, `sqrt`, `floor`/`ceil` and roots. Declare it, at least as informational, and use it as the source for mode-3 budgets.
- `structural-layer` does not apply: the owner declares `no-comparable-surface-in-named-comparator` against PARI.

### HexSturm

**Covered by delegation:**
- `rootCount` is `query p 1` plus an O(1) map.
- `certify` and `query` are the same computation, so `runRational` and `runRationalHigh` cover both.
- `queryPrepared` equals `certifyPrepared`'s value, and `countPrepared` equals `certifyCountPrepared`'s.
- A `checkCached` miss is just `check`.

**Genuinely needs new evidence:**
- `queryPrepared` and `certifyPrepared` with F ≠ 1, on a query-degree sweep. HexSignDet calls `certifyPrepared` with varying F (`HexSignDet/Produce.lean:114`), and PLAN/Phase4.md:142-149 requires the sweep to cover downstream call patterns.
- `withEndpoints?`.
- Field `check`. The integer replay on the same ladder went inconclusive and ended up as mode 2 at n⁴, so expect the same issue.
- The `checkCached` hit path, with an assertion that the cache actually hits.
- Transport `clearDenominators` and `toRat`, with coefficient bit sizes modelled.
- Infinite endpoints.
- The endpoint-size and coefficient-size axes from SPEC lines 342-351.
- A frontend profile for each input family.

**Watch for this in the uncommitted `Frontend.lean`:** its `n` model for `runRetarget` evaluates Chebyshev heads at ±3. T₂₀(3) is about 2⁵¹, past the small-int boundary. That is the same unit-cost trap that broke the original registrations.

**Comparators:** neither python-flint nor Z3 exposes a Tarski-query surface. Declare `no-comparable-surface-in-named-comparator` per surface, and keep the rational/integer `compare` group as the correctness agreement check.

### HexSturmTheory and HexRealAlgebraicTheory

These have no Phase-4 deliverable under PLAN/Phase4.md §theory libraries. Their ordinary-kernel tests and axiom guards are correctness evidence only.
