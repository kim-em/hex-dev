# Phase 4/5/6 checkpoint 50

Scope: checkpoint for merged work after summarize issue #5885, covering the
current BZ/HO-1, HexMatrix, HexPolyZMathlib, and HexLLL frontiers.

## Landed work

### BZ/HO-1 and factorization packaging

The Berlekamp-Zassenhaus stream continued moving from fallback-tolerant
execution toward explicit contracts for the public factorization surface.

- #5889, #5902, and #5904 exposed product and optional-factor record contracts.
- #5895, #5896, #5914, and #5920 packaged the headline factor clauses around
  scalar, multiplicity, primitive, positive-leading, and no-associates facts.
- #5907 removed the old fallback-backed prime-choice executable surface from
  `HBZ/Basic.lean`.
- #5918 audited factorization edge-case coverage and found the current
  conformance/oracle suite already covers the signed scalar and repeated-factor
  cases under review.

The direct HO-1/BZ directive remains blocked rather than discharged. The useful
near-term work is now bridge cleanup and clause assembly, not another broad
headline issue. Open PR #5938 threads `choosePrimeData` success witnesses
through `IntReductionMod`, and the blocked BZMathlib issue #5926 is the visible
successor once that repair lands.

### HexMatrix Plucker chain

The Plucker-minor proof stack advanced from basis-row expansion toward the raw
ordered determinant kernel.

- #5883 added `mDet` expansion helpers.
- #5897 checkpointed the fold-level basis-vector assembly and left the
  arbitrary basis row as the hard remaining case.
- #5921 bridged the ordered `q > p3` basis-vector case through the existing
  signed `nDet` API.

The raw ordered `nDet` kernel was decomposed after #5919 into smaller active
issues. Open PR #5937 adds the cofactor row-pairing bridge, while #5936,
#5929, and #5930 track the remaining determinant identity layers. Downstream
#5917 and #5912 should stay behind that chain.

### HexPolyZMathlib Schmeisser chain

The all-degree Schmeisser/de Bruijn-Springer route has been narrowed to a
degree-two exact-degree path.

- #5894 added the quadratic Schur-Szego root substrate.
- #5913 added the exact-degree Schmeisser source API.
- The stale derivative-specialization issue #5525 is no longer accurate:
  prerequisite #5559 was closed as obsolete, not as a landed radius-one
  derivative theorem.

The live path is now #5932 for the exact-degree-two zero-control theorem, then
#5924 for degree-two root-product packaging, then the blocked downstream
degree-two consumers. Open PR #5941 is the current quadratic roots bridge.
Issues #5939 and #5940 are blocked follow-ups in the same narrowed route.

### HexLLL benchmarking

HexLLL Phase 4 now has fresh evidence for the formerly inconclusive parametric
registrations.

- #5906 resolved the parametric verdicts by adjusting benchmark model
  registrations and caps.
- #5934 recorded the committed rerun artifact for the five formerly
  inconclusive targets and kept `HexLLL.done_through` at `3`.

The remaining Phase 4 gate is the densified Lean/Isabelle comparator sweep in
#5933. That issue needs quiet or dedicated hardware, or an intentionally
narrowed measurement plan if the fixed Isabelle targets remain too expensive.

## Current frontier

Open PRs:

- #5937, `feat: add cofactor row pairing bridge`.
- #5938, `fix: thread choosePrimeData witnesses in IntReductionMod`.
- #5941, `HexPolyZMathlib: add exact quadratic roots bridge`.
- #2656, draft SPEC PR for real roots and Sturm.

Open directives:

- #2564, HO-1/BZ headline correctness, currently blocked.
- #2567, HO-4/BHKS Theorem 5.2, blocked on #2564.
- #2637, Factorization record API and sign/multiplicity bugs, blocked on its
  prerequisite chain.

Ready status remains broad: Phase 6 polish is open for the mature
Mathlib-free libraries, Phase 5 remains ready for `HexGramSchmidt`, `HexPolyZ`,
`HexMatrixMathlib`, and `HexModArithMathlib`, and Phase 4 remains ready for
`HexLLL`, `HexBerlekamp`, `HexGramSchmidtMathlib`, `HexPolyZMathlib`,
`HexHenselMathlib`, and `HexGF2Mathlib`. `HexBerlekampZassenhaus` is still at
Phase 1 readiness, while `HexGFqRing` remains fully done.

## Recommended next actions

1. Let #5938 settle, then resume #5926 or the next narrow BZMathlib bridge
   repair before assembling the final HO-1 headline theorem.
2. Continue the Plucker chain through #5937, #5936, #5929, and #5930 before
   returning to #5917 or #5912.
3. Keep Schmeisser work on the exact-degree-two route: #5941/#5932 first,
   then #5924 and its blocked consumers. Do not revive #5525 until a valid
   derivative-specialization prerequisite exists.
4. Run #5933 only in an environment suitable for the densified Lean/Isabelle
   comparator sweep, or narrow the benchmark plan explicitly and leave
   `HexLLL.done_through` unchanged if the gate still fails.
5. Dispatch additional Phase 6 work as narrow polish or review issues; avoid
   duplicate umbrella issues for the existing BZ, Plucker, Schmeisser, and
   HexLLL chains.
