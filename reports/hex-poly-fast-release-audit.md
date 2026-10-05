# Fast polynomial release audit

## Proof and conformance boundary

`HexPolyFast.lean` and `HexPolyFast/` contain no Lean `sorry`, `axiom`, or
`native_decide`. The library builds on the pinned toolchain. Its native fixture
emitter reproduces the committed corpus, and the FLINT/exact-Python oracle
checks all 120 cases. The oracle is a development check, not a runtime
dependency. The library makes no irreducibility or field-construction claim.
This meets the Phase 5 exit criteria in [PLAN/Phase5.md](../PLAN/Phase5.md).

## API and declaration review

The Phase 6 triage issues [9744](https://github.com/kim-em/hex-dev/issues/9744),
[9745](https://github.com/kim-em/hex-dev/issues/9745),
[9746](https://github.com/kim-em/hex-dev/issues/9746),
[9747](https://github.com/kim-em/hex-dev/issues/9747), and
[9748](https://github.com/kim-em/hex-dev/issues/9748) are closed. The API is
organized around multiplication plans, reverse/series bridges, cached division,
Euclidean transformations, product/remainder trees, evaluation/interpolation,
and Padé approximation. Plans expose correctness and capacity lemmas; private
implementation fields are accessed through characterizing lemmas. Logical
reference definitions and checked `csimp` equalities preserve both stable proof
semantics and native implementations.

The declaration scan covers 442 explicitly named definitions, theorems,
abbreviations and structures, including 135 private definitions/theorems.
Every private declaration has a reference in its own file after comments are
removed. No unreferenced executable definition was found. Twenty public
theorems have no explicit name reference in the library, its bridge-facing
consumers, benchmarks, conformance modules or manual: five are compiler
simplification rules, one is the `@[simp]` identity `GcdStep.one_compose`, and
the remaining fourteen are exported characterizing lemmas for slices, reversal,
reciprocal multiplication, cyclic products, division, tree nodes and failed
interpolation. These are the supported proof API, rather than obsolete helpers.
The root/fold characterization also supports the Hensel consumer.

`DensePoly.Monic.mul` remains here because product trees work over a general
commutative ring, including the zero ring; `HexPoly.mul_monic` assumes a field.
`foldl_monomials_eq`, `size_low_le`, and `low_eq_self_of_size_le` are used in
cyclic-remainder and Padé proofs. Their current ownership avoids broadening this
release change into a base-library API migration. Generic operations live here;
coefficient-specific multiplication kernels remain owned by `HexPolyZ` and
`HexPolyFp`. There is no separate `HexPolyFastMathlib` layer: correctness reduces
to `HexPoly` and `HexTruncatedSeries` semantics, with correspondence provided by
their existing bridge libraries.

All default Batteries/Mathlib declaration checks and theorem docstring coverage
pass in [HexPolyFast.Lint](../conformance/HexPolyFast/Lint.lean), retained in the
monorepo conformance target. The upstream `structureInType` check constructs
projection names that fail for private fields; the replacement performs the
same predicate using recorded projection names. The other checks are unchanged.
All 64 benchmark registrations also pass the correctness smoke verification.

## Performance regression evidence

The retained full Phase 4 baseline identifies source revision `53ef234e9c`.
Its pinned binary (arm A) is compared with source revision `005b8a182b` (arm B)
on `chungus2`, CPU 20, selected through the shared-host CPU lease. The fixed
schedule is one AB block followed by one BA block per representative target;
each arm uses the target's declared parameter schedule and three outer trials.
All completed samples are retained. Host load is recorded before and after
every arm in [protocol.json](bench-results/hex-poly-fast-release-regression/protocol.json)
and was not used to reject samples. There were no reruns.

Both binaries use their own pinned toolchains and benchmark harness revisions:
A uses Lean `v4.34.0-rc2` and lean-bench `fa30c2763cf5`; B uses Lean
`v4.35.0-rc3` and lean-bench `8a37daf1074c`. Thus this checks the released native
path against the previous retained baseline; it does not isolate the constant
factor attributable to an individual library edit. The five registered inputs,
operations and result checksums agree at every matched parameter. All twenty
arms are consistent with their declared complexity.

Ratios below are current/baseline per-call times, using the median of three
trials at each input. The block columns are geometric means over matched
parameters. The final column retains the largest ratio from either block.

| Target | Largest input | AB ratio | BA ratio | Largest point ratio |
|---|---:|---:|---:|---:|
| `runKaratsubaMod` | 16384 | 0.568 | 0.562 | 0.787 |
| `runRepeatedCachedDivision` | 1024 | 0.581 | 0.562 | 0.725 |
| `runHalfGcd` | 2048 | 0.393 | 0.394 | 0.502 |
| `runRepeatedMultipointEval` | 2048 | 0.664 | 0.654 | 0.871 |
| `runHalfGcdPade` | 1024 | 0.437 | 0.449 | 0.542 |

No matched point regresses against the baseline, including cutoff-adjacent
inputs and the largest registered inputs. These are shared-host observations,
not universal speedup claims. Every arm's raw trials and configuration are in
[the retained exports](bench-results/hex-poly-fast-release-regression/).
To reproduce, build both source revisions on their pinned toolchains, lease
one CPU with `scripts/bench/cpu_lease.py`, and run each target in AB then BA order:

```sh
taskset -c "$measurement_cpu" "$arm_binary" run "Hex.PolyFastBench.$target"   --outer-trials 3 --export-file "$arm_export"
```

## Manual and README

The full manual builds and renders. The fast-polynomial chapter has been
inspected at desktop (1440 px) and mobile (390 px) widths, including code,
theorem statements and navigation. Its `HexPoly` and `HexTruncatedSeries`
references resolve to the rendered chapters. It states the native computational
and proof/correspondence boundary. The README follows [SPEC/readme.md](../SPEC/readme.md)
and its complete quickstart builds. The manual code blocks typecheck during the
chapter build. This meets [PLAN/Phase7.md](../PLAN/Phase7.md).

## Publication boundary

The manifest admits all four dependency mirrors in topological order and
validates their exact transitive pins, umbrella import closure, mirror workflows
and aggregate imports. The Mathlib bridge has no `component` label: aggregate
component labels describe computational libraries, as required by the manifest
checker and README specification. All four mirror skeletons contain generated
Lake lockfiles and the required starting files, with mirror-specific agent
instructions.

Token selection is distinct from organization approval. Both existing tokens
have fifty selections; `leanprover/fplll` accounts for the additional selection
on `hex-publishing` outside the manifest. Real publication requires approval of
the four new grants and the maintainer's go-ahead after the dry-run consumer
builds. The fast kernels return to published umbrellas in a separate change
after successful publication.
