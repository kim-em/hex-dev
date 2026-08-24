# Frontend initial context

## Accomplished

- Added bounded node-indexed `Frontend.InitialContext` data with absent facts materialized as `whole`, exact row/node authentication, and a separate positional containment authority tied through `Result.valuation`.
- Added `inputInitialWithin`, the `Contains.ofForall₂` Meta bridge, generalized initial-containment and `closeInitial` theorem families, and retained the source-only `inputWithin`/`Result.initial_contains` route as a compatibility wrapper.
- Added conformance for a bounded computed-node initial fact, default-top behavior, exact closing, row/count/program/result/source-expression mutations, fact/proof correlation mutations, all one-under frontend resource caps, and oversized initial-row refusal.
- Verified `HexIntervalMathlib.FrontendConformance` and `HexIntervalMathlib.TacticConformance`; the published trust-surface check and changed-file static guards pass.

## Current frontier

The isolated generalized initial-context prerequisite is complete. The public tactic can now quote one initial row per retained node, materialize selected computed-node facts, and close through kernel-checked positional containment without changing the source-only API.

## Next step

Use `InitialContext` from the public tactic's complete arithmetic context/target/syntax layer, keeping rational parsing and new target forms outside this prerequisite.

## Blockers

The final whole-monorepo `lake build` reached 9,927 of 9,975 targets and then failed in unrelated `HexBerlekampZassenhausMathlib.KernelFactorTactic` output creation because the shared filesystem was full. The relevant frontend and tactic conformance targets are green. Generated local build artifacts were cleared and the frontend conformance target was rebuilt successfully.
