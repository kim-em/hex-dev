# Metadata-driven proof-probe owners

## Accomplished

- Opened #8985 to replace the proof-probe directory suffix heuristic with the
  canonical `libraries.yml` `mathlib: true` ownership declaration.
- Updated the benchmark lint to recognize `bench/HexRCF/` and every other
  exact manifest-declared Mathlib owner while leaving Mathlib-free libraries
  outside the exception.
- Added strict duplicate-library and duplicate-field prechecks before the
  shared manifest parser, classified both lexical and physically resolved
  probe paths to close `..` and symlink aliases, and retained the existing
  suffix-based prohibition on proof-only bridge bench surfaces.
- Hardened probe scans for attributed registrations, attributed or modified
  `def`/`opaque`/`abbrev` main declarations, escaped/root main names, and
  qualified or unqualified monotonic clocks after comment stripping.
- Updated the benchmarking SPEC to describe metadata-based owners and the
  current root/import traversal.
- Expanded the lint suite from 11 to 20 tests. Unit tests, the real 21-exe /
  3-probe traversal, DAG, Python compilation, and diff checks pass.

## Current frontier

The policy can now safely admit future build-only `bench/HexRCF/` tactic probes
without relying on a false `Mathlib` name suffix or leaving them unlinted.

## Next step

Rebase this slice and the existing #8980/#8983 child branches onto the newly
merged conformance parent on `main`, then publish #8985 as its own focused PR.

## Blockers

None for this slice. The policy change does not itself authorize a probe or
advance HexRCF Phase 4; #8973 still governs that evidence contract.
