# matrixEquiv_principalSubmatrix dedup + released-repo metadata

## Accomplished

- **Released-repo GitHub metadata** (applied directly, live now):
  - Set the *website* on all 15 repos to their manual page. Chapter
    repos point at their Verso permalink
    (`…/find/?domain=Verso.Genre.Manual.section&name=<tag>`); `hex`,
    `hex-basic`, `hex-test-kit` (no dedicated chapter) point at the
    manual home `https://kim-em.github.io/hex-dev/`.
  - Rewrote the *About* texts: dropped the em-dashes (`hex`,
    `hex-matrix`, `hex-gram-schmidt`, `hex-lll`), replaced "bridge"
    with "correspondence proofs" (the three determinant/row-reduce/
    bareiss `*-mathlib` repos), refreshed the out-of-date `hex-matrix`
    blurb (no longer claims Bareiss/RREF, now generic not integer),
    and de-slopped the fresh rewrites ("core", "general-purpose").

- **`HexMatrix/README.md`**: second example now writes `B` explicitly
  with one-line `#m[1, 2; 3, 4; 5, 6]` (types as `Matrix Int 3 2`);
  de-slopped the "pure data transforms" row-ops comment.

- **Duplicate-lemma fix** (`HexDeterminantMathlib/CoreTransport.lean`):
  `matrixEquiv_principalSubmatrix` was declared in the
  `HexMatrixMathlib` namespace in *both* `HexMatrixMathlib/Submatrix.lean`
  and here. Each library built alone, but the `hex` aggregate's
  `HexAll` (which loads both umbrellas) failed with a duplicate-decl
  error, so the released closure did not compose. Fixed by importing
  `HexMatrixMathlib.Submatrix` and reusing the existing lemma (deleted
  the local copy; the one downstream `rw` now closes with a trailing
  `rfl` since `Fin.castLE hk` is defeq to the explicit lambda). Updated
  `HexDeterminantMathlib/README.md` to stop listing the moved lemma.
  Full `lake build` green (4081 jobs; the two pre-existing
  HexBerlekampZassenhausMathlib sorries are unrelated).

## Current frontier

Done end to end. The dedup fix is on `main` (e2aecad9) and was
republished by a real `sync-released` run (14 repos, from
`hex-dev@e2aecad9`, baseline advanced). The `kim-em/hex` aggregate was
bumped to the new released HEADs (`lake update` also moved it to
v4.32.0-rc1), its README now lists the full 13-library closure, and its
`HexAll` build is green both locally and on the aggregate's CI.

## Next step

Nothing outstanding for this line of work.

## Blockers

None.
