I found no merge-blocking problem in this partial delivery. Once CI is green, HexSturm is eligible for Phase 3 as it stands. HexRealAlgebraic needs a one-line `#guard` first (item 1 below). Each companion then follows its core with a green build.

I reviewed HEAD `54fd06b40` from the source and the retained artifacts. My first command worked; every later shell command was denied. So I couldn't build, run CI, or read the PR body or #10577. I'm relying on your report that `lake build HexConformance HexQuerySemantics` is green.

## The five things you asked me to verify

| Item | Verdict |
| --- | --- |
| Contract labels | **Met.** Both modules now open with the labelled Oracle, Mode, Covered operations, Covered properties and Covered edge cases fields, as bulleted lists (`conformance/HexSturm/Conformance.lean:19-35`, `conformance/HexRealAlgebraic/Conformance.lean:9-29`). |
| Nat/Int casts | **Met.** Each has three elaboration-time cases (`HexRealAlgebraic/Conformance.lean:175-178`), checked against an independent cast into `Rat`. |
| Polynomial conversion | **Met.** Expected coefficient arrays are written out literally rather than derived from a second constructor. The cases are empty, `[-3/2,0,0]` and `[-√2,0,1,0,0]`, and `r*r == 2` pins down √2 (`:180-193`). |
| `certifyPrepared` on T₈ | **Met.** The coefficients are correct for 128x⁸−256x⁶+160x⁴−32x²+1, and the expected values (8, 0, 8) follow from the roots cos((2k−1)π/16). Each query is also checked against the ordinary query path. The test asserts `steps.size > 1`, so the chain really has several steps, and degree 8 meets the bottom of the profile-size range (`HexSturm/Conformance.lean:92-106`). |
| Step and chain transport | **Met.** `RemainderStep.clearDenominators` is tested on three identities that hold by construction, including a wrong right-hand scale rejected in both domains, and no chain producer runs (`:295-313`). `SignedRemainderChain.clearDenominators` is checked on its own over singleton chains, a proper common factor and a full chain (`:329-330`). |

The SPEC's adversarial checker cases (wrong degree evidence, missing or extra steps, oversized chains, negative scales, missing terminal) are in `HexRealRoots/TarskiTests.lean:53-120`. The SPEC delegates shared replay cases to that library, which is fine.

## Performance evidence

- **Benchmark time warning and cap:** now reported honestly (`hex-real-algebraic-performance.md:15-20`). It gives the 600 s script default, the 360 s CI cap, and the 32 s run that exceeded the 30 s soft threshold. The follow-up is tracked under #10577. I couldn't confirm the #10577 body mentions it; if it doesn't, add a comment there.
- **Profile inventory:** complete, failed captures included. The fractional capture passes its diagnostics. Its call stacks reach `ZPoly.evalDyadic` and show `mul_n` and the Toom multiplication routines. It stays explicitly unadmitted in the report (`:633`, `:659`, `:721-728`), the cost model (`:409-411`) and the source comment (`Frontend.lean:494-496`). No Phase-4 claim is made.
- **Historical `runReplay` result:** the report states it is suspended (`hex-sturm-performance.md:3-6`).
- The earlier wording problems are fixed: "candidate passes above", the "smoke-gate" wording, the made-up registration name, and the readiness wording at `real-closure-prerequisites.md:73-74`.

## Before recording Phase 3

1. **HexRealAlgebraic: "root multiplicities" has no `#guard`.** The docstring lists it under Covered properties, but multiplicity is only checked in the compiled `Checks.repeatedRoots` (`Checks.lean:75`). The Phase-3 checklist requires a `#guard` for every listed property. This is the same reasoning I applied to integer casts last round. The fix is to add `roots.toArray.all (·.multiplicity == 2)` to the existing repeated-root guard at `Conformance.lean:124-127`, or drop the claim.
2. **HexSturm: the Oracle line doesn't match its SPEC.** `hex-sturm.md:302-303` requires rational and integer fixtures to be compared across both frontends and against python-flint exact signs at the roots. The module says "Oracle: none". The cross-frontend comparisons do exist (`:205-217`), and the integer frontend is checked against FLINT/qqbar in `realroots_flint.py`, so the requirement is met jointly. Name that in the Oracle line rather than "none". This is wording only.

## Other small issues

- `real-closure-prerequisites.md:10`: the HexSturm row still says "finish public-operation coverage". Update it when the phase is bumped.
- `hex-sturm-performance.md:508-510`: the `runReplay` table row still reads "within declared upper bound" without the suspension note from line 3.
- The 360 s CI cap covers the whole benchmark-verification step, not one library. Real-algebraic's roughly 32 s locally, likely 2–3× that on GitHub runners, takes headroom on unfiltered runs. CI will show whether it matters.

## Phase 3 order

All dependencies are at the required level: HexPoly 4, HexRealRoots 7, HexNumberField 7, and HexPolyTheory, HexNumberFieldTheory and HexRealRootsTheory all 7.

1. **Cores:** HexSturm now; HexRealAlgebraic after item 1.
2. **Companions:** HexSturmTheory and HexRealAlgebraicTheory, each after its core. Neither owns a conformance module, so a green build is enough.

Phase 4 remains incomplete and #10577 should stay open.

I edited nothing and wrote no review file. If you want this saved, it would go alongside `status/reviews/issue-10577-opus-confirmation.md`.
