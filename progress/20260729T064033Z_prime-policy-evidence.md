# Prime-policy performance evidence

## Accomplished

- Added direct compile-time guards for every branch of the bounded prime-probe
  policy and rebuilt its library, diagnostic service, and CI spike target.
- Refreshed the affected no-decline classical, lattice, and kernel-factor
  measurements on `chungus2`; retained the already-current PARI, NTL, FLINT,
  and Isabelle exports without rerunning them.
- Recomputed the cross-system and same-system comparisons, regenerated all 25
  factorization figures, and corrected the canonical performance reports with
  the clean artifact revisions and SHA-256 hashes.
- Independently reviewed the implementation and evidence. The review found no
  correctness, proof, API, or termination blocker; its stale-comparator,
  missing-policy-test, CI-coverage, trace, and provenance findings were fixed.
- Passed `lake build` (9,629 jobs), the targeted benchmark builds, DAG,
  Mathlib-free bench, copyright, line-count, diff checks, JSON validation, and
  105 benchmark-script tests.

## Current frontier

The current public factorizer reaches parity with verified Isabelle BZ: 244
eligible rows have a 0.996x Hex/Isabelle median and split 123/121 wins. That
headline is sensitive to the protocol floor (1.082x at the preceding floor),
so it is not yet a convincing lead. The refreshed public/classical comparison
has a 1.015x median; classical wins 171/240 ordinary eligible rows, while public
retains the harder tail and uniquely solves `sd6`.

## Next step

Publish and merge the bounded prime-width/evidence PR after CI. Continue from
the merged revision by profiling the remaining shared classical-core losses,
starting with Chebyshev, Legendre, and the worst Conway rows against Isabelle,
then implement and measure the smallest generally useful hot-path reduction.

## Blockers

None.
