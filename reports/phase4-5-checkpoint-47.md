# Phase 4/5 checkpoint 47

Scope: checkpoint for merged work after summarize issue #5228 closed at
2026-05-19T03:35:21Z, through the claim-time queue snapshot for #5714 on
2026-05-21T03:00Z. The merge window contains 177 PRs.

## Landed work

### Phase 6 API polish across Mathlib-free libraries

The dominant landed stream was Phase 6 theorem-surface cleanup. The work
mostly added caller-facing wrappers, simp lemmas, and review reports without
changing algorithms.

- `HexArith`: Nat exponent/divisibility wrappers, carry/borrow predicate and
  projection lemmas, `powMod` identity/exponent wrappers, and a completed
  Nat-level API audit (#5698).
- `HexPoly`: dense constructor and operation API polish, coefficient wrapper
  fixes, monomial/support/zero-law wrappers, compose/derivative/constant
  wrappers, and a constructor API review (#5681).
- `HexMatrix`: row/column operation readback lemmas, multiplication/row-echelon
  automation, row-echelon span polish, and the row-echelon/RREF review (#5708).
- `HexModArith`: representative API polish, operator-level aliases, inverse
  and arithmetic wrappers, Barrett and Montgomery hot-loop facts, pow theorem
  surface cleanup, and hot-loop review work now tracked by #5713.
- `HexGF2`, `HexGFq`, and `HexGFqField`: representative and packed-operation
  wrappers for arithmetic, casts, powers, division/inversion, quotient
  operations, and finite-field wrapper review.
- `HexPolyFp` and `HexPolyMathlib`: quotient/Frobenius/compose reviews,
  bounded-degree and divisibility iff wrappers, `ofPolynomial` /
  `toPolynomial` simp wrappers, and Euclidean gcd/xgcd bridge review.
- `HexHensel`: quadratic multifactor polish, bridge normalizers, positive
  precision wrappers, polyProduct normalizers, and the broader lift API review
  now tracked by #5715.
- `HexConway`: lookup miss review plus supported-entry exposure for several
  primes.

No new Phase 6 follow-up needs to be invented from this checkpoint. The two
unclaimed Phase 6 review issues at snapshot time are #5713 and #5715.

### BHKS / HO directive chains

The BHKS and HO work remains active but is still dependency-gated.

- Directive #2564 remains open and blocked. Its HO-1 rewrite/rollback path is
  not superseded: the project still treats the current BZ recombination lattice
  as the wrong fast-path architecture until the van Hoeij CLD rewrite lands.
- Directive #2567 remains open and blocked on #2564. The D1 termination theorem
  is still a leaf theorem; it should not be used to block public `factor`
  correctness work that can route through the slow fallback.
- Directive #2637 remains open and blocked. The Factorization record/sign and
  multiplicity chain is separate from the CLD fast-path chain and should not be
  collapsed into HO-1.

Landed BHKS/D1 support in this window includes resultant/Hadamard audit work,
bad-vector theorem shaping, executable `bhksBound` and CLD supporting lemmas,
projected-vector and finite Cauchy-Schwarz helpers, auxiliary-polynomial
coefficient formulas, and support-indicator/recovery wrapper lemmas. The
current D1 issue chain is already represented by #5204, #5216, #5223, #5224,
#5237, #5512, and #5709.

The HO-1 Gap 1 monicised-core line advanced through executable monicised-core
transforms, routing exhaustive Hensel lifting through that core, partial
migration of exhaustive bridges, and the new monicised Hensel correspondence
surface. The active frontier is #5675, with dependent issues #5636, #5689,
and the broader blocked HO/BZ bridge cluster still waiting behind the directive
chain.

### HexGramSchmidt Phase 5

HexGramSchmidt moved from local helper exposure into the Bareiss/Gram singular
proof chain.

Landed work includes signed scaled-coefficients diagonal helpers, the Mathlib
bridge proof of `scaledCoeffs_diag`, Gram determinant Bareiss prefix helpers,
non-circular Gram Bareiss bridge publication, orthogonal GS norm lower bound,
pivot-search zero-suffix converse, row-combination prefix-span truncation,
highest-coordinate identities for lattice combinations, and Bareiss row update
linearity lemmas.

The active open PRs and blockers define the next path:

- #5693 has an open PR (#5707) for one-step Bareiss Gram row invariant
  preservation.
- #5704 has an open PR (#5710) for the row-combination GS reconstruction
  lemma.
- #5694, #5677, #5668, #5655, and #5705 are blocked successors. Do not create
  duplicate Gram singularity or row-reconstruction umbrella issues.

### HexPolyZMathlib Schmeisser / Boyd / Grace-Walsh-Szego

The Schmeisser/de Bruijn-Springer route advanced substantially. Landed work
defined Robinson forms and Schur/Szego composition scaffolding, packaged
Gauss-Lucas and boundary Mahler helpers, reduced derivative root-product goals
to Schmeisser radius-one and general-radius source wrappers, split source
substrates, added root-count/radius-product wrappers, and formalized several
local algebraic bridge steps.

This work has produced several deliberate blocked chains rather than one
monolithic proof. Existing open issues cover the remaining route:

- #5701 and #5702 for the Grace-Walsh-Szego/source-free
  `rootsRadiusProduct` path.
- #5525, #5559, #5570, #5506, #5413, #5409, #5401, #5337, #5318, and #5266
  for the Schmeisser/Boyd/global derivative Mahler chain.

Avoid resurrecting the Schur-reflection counterexample path as a proof route:
the later Schmeisser/de Bruijn-Springer plan supersedes it.

### Factorization residual reviews and substrate polish

Several review/report PRs landed around BZ Factorization residuals, HO-1
Gap 1, stale dependency links, and resultant infrastructure. These reports did
not close the directives, but they narrowed implementation work into existing
issue chains.

Relevant landed reports include:

- `reports/bhks-bad-vector-theorem-shape.md`
- `reports/schmeisser-debruijn-lean-plan.md`
- Factorization residual and HO-1 Gap 1 review reports
- BHKS resultant/Hadamard infrastructure audit work

Follow-up should link those reports to existing issues rather than generating
new duplicate tasks.

## Current frontier

### Queue snapshot

At claim time, the unclaimed work queue contained only:

- #5713 `HexModArith Phase 6: audit hot-loop modular API quality`
- #5715 `HexHensel Phase 6: audit lifting API quality`

Claimed work:

- #5714, this checkpoint.
- #5675, `HO-1 Gap 1: package IntReductionMod monicised-core transport
  theorem`.

Open PRs:

- #5716, `feat: prove degree-zero Grace-Walsh-Szego source case`, failing CI.
- #5712, `doc: audit BHKS resultant infrastructure`.
- #5711, `HO-1 substrate: expose non-circular lifted Hensel descent primitive`.
- #5710, `feat: add Gram-Schmidt row reconstruction lemma`.
- #5707, `HexGramSchmidt Phase 5: package one-step Bareiss Gram invariant`.
- #2656, draft SPEC PR for real roots and Sturm.

Issues with PRs that should be allowed to merge before successors are claimed:
#5709, #5704, #5693, and #5688.

### Blocked chains to respect

The current blocked set is intentional. Important chains:

- HO/BZ bridge and Factorization chain: #4170, #4172, #4680, #4818, #4819,
  #4821, #4825, #4830, #4831, #4832, #4880, #5214, #5215, #5636, and #5689.
- BHKS D1 chain: #5204, #5216, #5223, #5224, #5237, and #5512.
- Schmeisser/Boyd chain: #5266, #5318, #5337, #5401, #5409, #5413, #5506,
  #5525, #5559, #5570, and #5702.
- HexGramSchmidt chain: #5655, #5668, #5677, #5694, and #5705.

The status script still reports many Phase 6 libraries ready and
`HexGramSchmidt -> Phase 5` ready. The ready list should drive narrow issue
creation, but the blocked chains above should not be bypassed with duplicate
umbrella issues.

## Recommended next actions

1. Let repair handle #5716 before downstream Schmeisser issues depend on it.
2. Let #5711/#5688 and #5675 settle before claiming #5689 or #5636.
3. Let #5707/#5693 and #5710/#5704 settle before claiming #5694 or #5705.
4. Dispatch #5713 and #5715 as bounded Phase 6 reviews.
5. Do not file new BHKS D1, HO-1, Schmeisser/Boyd, or Gram singularity umbrella
   issues unless an existing blocked issue is closed as stale or superseded.
