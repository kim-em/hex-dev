# Accomplished

- Added the generic `HexRootsMathlib.isolate_spec` proof-facing API. It
  bundles driver completeness with the returned atom count, exact complex-root
  enumeration, and requested-precision guarantee.
- Added `HexRootsMathlib.Examples.isolate_q` for `q(x) = x⁴ - 1`. The theorem
  proves that isolation succeeds, returns four atoms, and that their selected
  roots are exactly `{1, -1, i, -i}`.
- Kept the runnable `x⁵ - x + 1` demonstration and linked its documentation to
  the proof-facing example.
- Built `HexRootsMathlib`, built and ran `hexroots_demo`, and ran the repository
  DAG, copyright, line-count, conformance-target, and diff checks.

# Current frontier

The executable and theorem demonstrations are complete. The generic bundled
API keeps downstream isolation proofs to one completeness/soundness call.

# Next step

Publish the demo and bundled API in the next HexRootsMathlib PR.

# Blockers

None.
