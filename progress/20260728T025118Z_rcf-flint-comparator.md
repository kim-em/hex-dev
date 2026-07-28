# HexRCF python-flint decision comparator

## Accomplished

- Exposed the conformance oracle's independent sentence decider and reused it
  from the shared persistent python-flint benchmark driver without duplicating
  the root or cell algorithm.
- Added the `rcf/decide` request protocol and focused Python tests covering the
  public decision entry point, shared dispatch, malformed requests, and
  continued service after an error frame.
- Added an exact Mathlib-free encoder for the version-1 reflected sentence
  schema, pinned its complete vocabulary with build guards, and precomputed
  the five shared Sentence/request-line inputs at carrier degrees 16, 20, 24,
  28, and 32 outside every timed body.
- Registered paired fixed Lean and FLINT Boolean decisions at all five rungs,
  with one shared five-repeat and 0.2-second steady-state config, a pinned true
  hash, and matched per-child warmups.
- Corrected the persistent-driver lifetime documentation: LeanBench creates a
  fresh child for each outer fixed warmup or repeat, while the Python process
  is warmed and reused across the auto-tuned inner batch inside that child.
- Built `hexrcf_bench`, exercised all twenty registrations through `verify`
  with python-flint 0.9.0, passed the 360-second smoke budget in 12 seconds
  including incremental build, and rechecked all thirty conformance sentences.

## Current frontier

- Directive #9021 is implementation-complete locally and is undergoing a
  read-only preflight before commit and draft PR publication.
- The comparator is structural wiring only. No scheduled scientific timing,
  performance report, or release artifact has been produced.

## Next step

- Address any preflight findings, rerun the repository checks from the committed
  state, publish the draft PR, and obtain the requested fresh Claude review.
- Rebase the milestone as the HexRCF stack advances.

## Blockers

- None for registration or routine CI verification.
- Informational ratios still require the named scheduled benchmark host and a
  release-quality run; that work is intentionally outside this directive.
