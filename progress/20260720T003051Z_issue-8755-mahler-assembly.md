# Accomplished

- Extracted the exponent-independent Mahler root-separation assembly into the
  HexRoots-independent theorem `HexPolyZMathlib.one_le_mahlerDist`.
- Refactored both `HexRootsMathlib.mahlerPrec_separates` and
  `HexRealRootsMathlib.sepPrec_separates` to retain only their distinct
  coefficient bounds, executable exponent arithmetic, and final constants.
- Removed the duplicated discriminant lower bound, separable-root
  enumeration, Vandermonde/Hadamard estimate, and Mahler-product assembly from
  both consumers (a net reduction despite adding the shared theorem).
- Verified both focused targets, a full build, the import DAG, line-count and
  copyright checks, and the absence of banned proof constructs.

# Current frontier

The shared separation assembly is complete locally and ready to rebase onto
current `main` and receive its required independent Opus review.

# Next step

Rebase, rerun affected/full builds, address the review, then publish and merge
the #8779 pull request while the driver-completeness PR is in CI.

# Blockers

None.
