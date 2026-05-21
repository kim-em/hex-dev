# Phase 4/5/6 checkpoint 48

Scope: checkpoint for merged work after summarize issue #5714, through the
claim-time queue snapshot for #5745. The merge window contains 13 PRs.

## Landed work

### HexGramSchmidt Phase 5

The Gram-Schmidt Phase 5 chain moved from invariant setup into the singular
pivot/Bareiss bridge.

- #5724 closed #5694 by packaging `Matrix.noPivotLoop` preservation and
  initial-state specializations for the Bareiss Gram row invariant.
- #5727 closed #5705 by proving the lattice-vector norm lower bound after
  row-combination reconstruction.
- #5736 made partial progress on #5677 by adding executable pivot-search
  packaging lemmas: one aligning the initial no-pivot Gram prefix state at
  column `s`, and one turning a proved suffix-zero column into
  `Matrix.findPivot? = none`.

The active frontier is still #5677. The remaining proof is the actual singular
Gram pivot column-zero suffix: combine the row-vector invariant, zero pivot,
integer self-orthogonality, and trailing-block symmetry, then feed the result
to the new `findPivot? = none` wrapper. Downstream #5668 and #5655 remain
blocked behind that result.

### HO-1 monicised-core transport

The HO-1 Gap 1 monicised-core line advanced in two layers.

- #5718 closed #5675 by adding a `MonicisedCoreTransportPackage` in
  `HexBerlekampZassenhausMathlib/IntReductionMod.lean`. The package collects
  normalized square-free core facts, monicised-core degree/nonzero facts,
  correspondence and partition constructors, scaled recovery, and the scaled
  exhaustive-membership bridge.
- #5728 closed #5689 by adding the choose-prime-data success Hensel
  correspondence needed by downstream exhaustive-branch work.
- #5740 closed #5730 by adding the monicised-core prime-data surface required
  for lifted-factor facts without assuming the original core is monic.

The immediate active work is now #5731, which is claimed. Its deliverable is to
prove monicity, positive natDegree, and injectivity for lifted factors of
`Hex.monicisedCoreLiftData` or the adjacent wrapper. #5733 and #5723 are
blocked consumers that should wait for #5731 rather than rebuilding those facts
locally.

The broader HO/BZ directive chain remains blocked. #2564 still cannot be
claimed because coordination reports unresolved dependencies; #2567 and #2637
remain open directives behind that chain.

### HexPolyZMathlib Schmeisser / de Bruijn-Springer

The Schmeisser route gained source surfaces but not the positive-degree
analytic theorem.

- #5716 made partial progress on #5701 by proving the degree-zero
  Grace-Walsh-Szego source case.
- #5744 made partial progress on #5732 by adding a derivative-free open-domain
  zero-control surface: strict exterior root counts over `Polynomial.roots`,
  open source hypotheses, a degree-zero open witness, and wrappers from open
  source hypotheses to strict radius-count domination.

The next mathematical frontier is still the positive-degree
de Bruijn-Springer/Grace-Walsh-Szego source theorem behind
`graceWalshSzegoOpenZeroControlAtDegree n`. Mathlib does not currently expose
that theorem as a reusable result, so this should be treated as a proof-plan or
further-decomposition target rather than a small assembly step. #5734 and
#5735 are blocked behind #5732; #5702 was skipped as stale because the all-degree
source theorem promised by its dependency is still absent.

The downstream Schmeisser/Boyd chain remains represented by existing blocked
issues: #5570, #5559, #5525, #5506, #5413, #5409, #5401, #5337, #5318, and
#5266. Do not create another umbrella for this route unless one of those issues
is closed as stale or superseded.

### Phase 6 API reviews and polish

Recent Phase 6 work focused on API quality for hot-loop arithmetic and Hensel
lifting.

- #5725 closed #5713 by adding `reports/hex-mod-arith-hotloop-api-phase6-review.md`.
  The review found no correctness defect in the current hot-loop modular API
  and identified focused polish around Barrett/Montgomery context construction
  and automation.
- #5726 closed #5715 by adding `reports/hex-hensel-lift-api-phase6-review.md`.
  The review concluded that the quadratic production path is usable by current
  downstream consumers without unfolding algorithms, while the linear reference
  path still deserves narrower constructor and ergonomics follow-up.
- #5741 closed #5738 with a Montgomery hot-loop context constructor.
- #5742 closed #5737 with a Barrett context smart constructor.
- #5743 closed #5739 by adding `reports/hex-arith-barmont-api-phase6-review.md`.
  That report found no correctness findings for public Barrett/Montgomery
  theorem shapes and recommended narrow follow-ups for `grind` coverage and
  named constructor characterisation lemmas.

No broad Phase 6 issue needs to be invented from these reviews. The actionable
follow-ups are narrow constructor-characterisation and automation-polish tasks
if the planner wants more HexArith/HexModArith Phase 6 work.

## Current frontier

### Queue snapshot

At checkpoint time there were no ordinary unclaimed work items.

Claimed work:

- #5745, this checkpoint.
- #5731, HO-1 monicised-core lifted-factor facts.
- #5677, Gram singular pivot column-zero suffix.
- #4334, HexLLL inconclusive scientific benchmark verdicts.

Open PRs:

- #2656, draft SPEC PR for real roots and Sturm.

The HexLLL benchmark issue #4334 is still environmental rather than a Lean
proof task: prior attempts reported noisy host load and unstable spawn-floor
measurements. Phase 4 promotion still needs quiet or dedicated hardware for
scientific benchmark reruns.

### Status script

`scripts/status.py` still reports ready work across many libraries:

- Phase 6: `HexArith`, `HexPoly`, `HexMatrix`, `HexModArith`, `HexGF2`,
  `HexPolyFp`, `HexGfqField`, `HexHensel`, `HexConway`, `HexGfq`,
  `HexPolyMathlib`.
- Phase 5: `HexGramSchmidt`, `HexPolyZ`, `HexMatrixMathlib`,
  `HexModArithMathlib`.
- Phase 4: `HexLLL`, `HexBerlekamp`, `HexGramSchmidtMathlib`,
  `HexPolyZMathlib`, `HexHenselMathlib`, `HexGF2Mathlib`.
- Phase 1: `HexBerlekampZassenhaus`.

`HexGfqRing` remains fully done. The planned-but-deferred libraries remain
`HexRoots`, `HexRootsMathlib`, `HexResultant`, `HexResultantMathlib`,
`HexNumberField`, and `HexNumberFieldMathlib`.

### Blocked chains to respect

- Gram-Schmidt: #5677 is the next proof frontier; #5668 and #5655 wait behind
  it.
- HO-1 Gap 1: #5731 is the next substrate; #5733 and #5723 wait behind it.
- Schmeisser/de Bruijn-Springer: #5732 remains the analytic source frontier;
  #5734 and #5735 wait behind it.
- BHKS D1: #5224, #5204, #5216, #5512, and #5237 remain blocked pieces of the
  termination chain, with the final theorem still a leaf relative to public
  `factor` correctness.
- HO/BZ directives: #2564, #2567, and #2637 remain open directives, but current
  coordination state marks their dependency chains as blocked.

## Recommended next actions

1. Let the claimed workers finish or release #5677 and #5731 before creating
   successors for the Gram and HO-1 Gap 1 chains.
2. For Schmeisser/de Bruijn-Springer, plan the positive-degree analytic source
   theorem explicitly; small source-free wrappers should wait until the source
   theorem exists.
3. Treat #4334 as a hardware/measurement scheduling item, not a normal proof
   or code task, unless a quiet benchmark host is available.
4. Use the Phase 6 review reports to dispatch narrow polish issues only; avoid
   broad duplicate review umbrellas for hot-loop arithmetic or Hensel lifting.
