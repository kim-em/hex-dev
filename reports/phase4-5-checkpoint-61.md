# Phase 4/5/6 checkpoint 61

Scope: checkpoint for the 45 PRs merged after summarize issue #7795 (closed
2026-06-17T18:21:37Z) through PR #7918 (`package BHKS short-vector data from
non-monic recovered lifts`). Two threads dominate this window. First, the GF(2)
Mathlib transport reached a milestone: the executable `GF2Poly` is now
sorry-free as a *ring equivalence* to `FpPoly 2`, and the entire HexGFqMathlib
scaffolding layer was cleared. Second, the fast-BHKS van Hoeij CLD producer chain
under directive #2564 / capstone #6672 advanced from "recovered lift package" all
the way to a non-monic short-vector data package, while leaving the headline HO-1
correctness `sorry`s open. The Berlekamp irreducibility transport also closed its
remaining Mathlib-bridge `sorry`, retiring the
`irreducible_of_mem_berlekampFactor` obligation that checkpoint 60 still listed
open.

## Landed work

45 PRs merged after checkpoint 60 (range #7798–#7918). Grouped by topic.

### GF(2)/GF(q) Mathlib transport (dominant theme)

The proof-facing bridge from the executable packed `GF2Poly`/`GFq` surface to
Mathlib `Polynomial (ZMod 2)` / finite-field facts. This window cleared
HexGFqMathlib from 14 `sorry`s to 0 and HexGF2Mathlib/Basic.lean from 11 to 0:

- **`GF2Poly ≃+* FpPoly 2` ring equivalence.** #7902 close 4 of the 5 structural
  ring-equivalence obligations; #7907 close the final `toFpPoly_mul` leg via a
  carryless-convolution coefficient lemma. The equivalence is now sorry-free.
  Supporting packed groundwork: #7885 (packed `toNat` bit equivalence), #7891
  (`toNat` degree bound and packed index inverses), #7863 (GF2 packed decoder
  index lemmas), #7834 (`RingEquiv.symm` preservation).
- **HexGFqMathlib Phase 5 cleared.** #7844 (FpPoly base-`p` index encode/decode
  bijection), #7848 (packed↔generic Conway field `RingEquiv` in GF2q.lean), #7888
  (reduced-representative equivalence), #7911 (Phase 6 docs for finite-cardinality
  bridges). HexGFqMathlib carries no `sorry`.
- **HexGFq executable Phase 6.** #7849 (nontrivial committed `PackedGF2Entry`
  instances), #7858 (ergonomic committed-entry GFq constructor layer).

### Berlekamp factor irreducibility (executable + Mathlib bridge)

- #7818 prove Berlekamp factor irreducibility for non-monic outputs (executable
  `HexBerlekamp/`). #7807 repair the HexBerlekamp FLINT comparator eligibility.
- #7842 discharge the positive-degree Mathlib Berlekamp factor irreducibility
  bridge. This retired the `irreducible_of_mem_berlekampFactor` `sorry`
  (`HexBerlekampMathlib/Basic.lean:960`) that checkpoint 60 listed as one of three
  capstone-gated bridges. HexBerlekampMathlib now carries no `sorry`.

### Fast-path BHKS CLD recombination chain (directive #2564 / capstone #6672)

The van Hoeij CLD route feeding the fast-BHKS raw-irreducibility disjunct
advanced from the recovered-lift package to a non-monic short-vector data
package:

- **RecoveredLift producers.** #7810 (recovered BHKS lift package), #7852 (expose
  fast-core recovery witnesses for `TrueFactorLift`), #7864 (derive
  `RecoveredLift` from fast-core recovery witnesses), #7865 (fast-core reassembly
  completeness for raw irreducibility), #7906 (`toMonic` recovered-lift producer),
  #7913 (monic-lattice `RecoveredLift` family from fast-core indicator-candidate
  success — prerequisite (A), `LiftBridge.lean:391`).
- **CLD residue / cut / norm-bound aggregation.** #7840 (aggregate-cut CLD tail
  helper), #7871 (period-aware aggregate `psiCut` carry lemma), #7873 (aggregate
  CLD residue from `RecoveredLift`, monic coordinate), #7883 (generalize BHKS cut
  projection short vectors), #7884 (period-corrected true-factor CLD vector + tight
  norm bound), #7887 (aggregate-tail CLD lattice path for `RecoveredLift`).
- **Partition / short-vector data.** #7914 (produce fast lifted-support partition
  count from core facts), #7918 (package BHKS short-vector data from non-monic
  recovered lifts).

### Phase-completion records, audits, docs, guards

- Phase records: #7814/#7830 (HexGramSchmidtMathlib Phase 4/5), #7815/#7828
  (HexHenselMathlib Phase 4/5), #7822 (HexGF2Mathlib Phase 4), #7824
  (HexPolyZMathlib Phase 4), #7825 (HexLLLMathlib Phase 4), #7832 (HexGFqMathlib
  Phase 4), #7833 (HexModArithMathlib Phase 5).
- Phase-6 audits/docs: #7877 (HexPoly final audit + done_through bump), #7896/#7898
  (HexGramSchmidt Basic/Int simp/grind + docs), #7899 (HexModArithMathlib
  docstrings + automation audit), #7911 (HexGFqMathlib finite-cardinality docs).
- Reviews: #7811 (audit live HO-1 directive dependency graph), #7904 (audit BZ CLD
  surfaces against directive).
- Boundary-skill docs: #7859 (recovery→TrueFactorLift centered/raw trap), #7868
  (RecoveredLift CLD period trap).
- Conformance guards: #7798 (heavy-split irreducible backstops — `swinnerton_dyer_sd3`,
  `phi15` — through `factorSlowModular`).

## Phase state

`scripts/status.py` reports the executable dispatch front at Phase 6 across the
mature libraries: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt,
HexGF2, HexPolyZ, HexLLL, HexPolyFp, HexGFqField, HexHensel, HexGFq. `HexBerlekamp`
is at Phase 4. `HexGFqRing` is fully done.

Mathlib-side queues:

- Phase 6 ready: HexModArithMathlib, HexGramSchmidtMathlib, HexHenselMathlib,
  HexGFqMathlib.
- Phase 5 ready (implementation work loop): HexPolyZMathlib, HexLLLMathlib,
  HexGF2Mathlib.
- Blocked: HexBerlekampMathlib (Phase 4, waits on `HexBerlekamp.done_through ≥ 4`),
  HexBerlekampZassenhausMathlib (Phase 3, waits on
  `HexBerlekampZassenhaus.done_through ≥ 3`).

HexRoots/HexResultant/HexNumberField and their Mathlib counterparts remain
SPEC-ready but implementation-deferred. Directive #2564's `done_through: 2 → 0`
rollback on `HexBerlekampZassenhaus` still stands; the bridge stays at
`done_through: 3` per the directive.

## Quality metrics

Repository-wide `git grep` over `*.lean` (excluding `.lake/`) at HEAD `42714423`:

- `sorry`: **17 raw grep hits, of which 14 are genuine tactic `sorry`s** and 3 are
  prose (a `single localised sorry.` line in
  `HexBerlekampZassenhausMathlib/Basic.lean:231`, the forbidden-token checklist
  line in `HexBerlekampZassenhausMathlib/IntReductionMod.lean:1288`, and the
  `bareiss_eq_det` reference comment in `HexMatrixMathlib/Determinant.lean:24`).

  This is down from 40 genuine at checkpoint 60. The drop is real progress, not a
  counting change: HexGFqMathlib (14 → 0), HexGF2Mathlib/Basic.lean (11 → 0), and
  HexBerlekampMathlib/Basic.lean (1 → 0) were all cleared this window.

  The 14 genuine tactic `sorry`s split as:
  - **12 in `HexGF2Mathlib/Field.lean`** — the pre-existing field-structure
    cluster (`modulusFpPoly_degree_pos` and the `ofGeneric`/`toGeneric`
    round-trip/homomorphism obligations per namespace). Not on the directive #2564
    critical path. PR #7919 (open) is closing 3 of the 4 modulus-transport
    `sorry`s and adds the shared `toFpPoly` transport bridges; #7922 (unclaimed,
    gated on #7919) targets the fourth.
  - **2 capstone-gated bridges** on the directive #2564 chain:
    `Hex.ZPoly.isIrreducible_iff` (`HexBerlekampZassenhausMathlib/Basic.lean:235`,
    #4818) and `factor_irreducible_of_nonUnit`
    (`HexBerlekampZassenhausMathlib/FactorSoundness.lean:20`, #6672).

  No `sorry` exists in any Mathlib-free executable library. The two Mathlib bridge
  layers that still carry `sorry`s compile (a `sorry` is a warning, not an error),
  so `ci.yml`'s build of `HexBerlekampZassenhausMathlib` stays green while these
  obligations remain open.

- `axiom`: **0 real declarations** (`git grep -nE '^\s*axiom '` reports none).

- `native_decide`: **0 real tactic uses.** The 2 grep hits are both comment text —
  a line in `HexArith/Nat/Prime.lean:344` stating the code does *not* depend on
  `native_decide`, and the forbidden-token checklist line in
  `HexBerlekampZassenhausMathlib/IntReductionMod.lean:1288`.

## Blocking structure for directive #2564

The headline gap is unchanged from checkpoint 60: the directive #2564 capstone is
the two `HexBerlekampZassenhausMathlib` `sorry`s (`factor_irreducible_of_nonUnit`,
#6672; `Hex.ZPoly.isIrreducible_iff`, #4818), both still open. The directive
itself is `blocked` (on #4818 and #4172), which in turn block on capstone #6672,
which blocks on the BHKS cut-package producer chain.

This window built substantial substrate toward the fast-BHKS front without
retiring either headline `sorry`:

1. **Fast-BHKS RecoveredLift producer chain.** Prerequisite (A), the monic-lattice
   `recoveredLift_family_of_indicatorCandidates` family
   (`LiftBridge.lean:391`), landed (#7913, building on #7906/#7864). #7918 packaged
   BHKS short-vector data from non-monic recovered lifts, and #7914 produced the
   fast lifted-support partition count. The producer issue #7894 ("derive BHKS cut
   package from successful indicator candidates") remains **blocked/parked**: per
   two independent premise checks recorded on the issue, the cut package cannot be
   derived as a single substrate theorem from indicator-candidate success alone —
   it needs the non-monic `RecoveredLift` producer (A, landed), the `trueSupports`
   + `CutProjectionHypotheses` producer (B, short-vector / separation side at
   #6779), and fast-path coverage for `hpartition` (C). The live critical-path
   issue is #7921 (claimed), which builds the array-index → `trueSupports` bridge
   from the (A) family into the line-714 endpoint
   `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredLift`,
   conditional on partition coverage and precision adequacy.

2. **Open precision-soundness gap.** The `hsep`/`hthr` residuals (a-priori Mignotte
   adequacy `bhksCoeffBound … ≤ k'`) become dischargeable only once the
   precision-soundness theorem (`PartitionRefinement.lean:447`, success ⟹
   cap/Mignotte precision) lands. With partition coverage, this is the remaining
   gate between the conditional fast-disjunct assembly and an unconditional fast
   raw-irreducibility substrate for #6672.

The HO-1 capstone #6672 (`factor_irreducible_of_nonUnit` assembly) consumes
whichever raw-irreducibility front lands first; it remains blocked on #7894.

## Current frontier

Open PRs at checkpoint time:

- #7919 feat: close 3/4 GF2Mathlib modulus-transport `sorry`s + repair
  `toFpPoly_mul` (mergeable, in the auto-merge queue).
- #2656 spec: add hex-real-roots and hex-sturm (status: planned).

Unclaimed issues (excluding this summarize issue): #7894 (BHKS cut package,
blocked/parked on producers A/B/C), #7922 (GF2nPoly modulus positive-degree, gated
on #7919). #7921 (the `trueSupports` bridge) is claimed and on the critical path.
Directive #2564 remains the open umbrella, blocked on #4818 and #4172.

## Recommended next actions

1. Land PR #7919, then dispatch #7922 (the fourth GF2Mathlib modulus `sorry`) —
   the cleanest route to retiring the `HexGF2Mathlib/Field.lean` cluster, the
   largest remaining genuine-`sorry` concentration. Note the #7922 premise
   correction: `Hex.GF2Poly.Irreducible` admits the unit `f = 1`, so positive
   degree must come from a carried wrapper invariant or a strengthened predicate,
   not from irreducibility directly.
2. Drive the #7921 → #7894 → #6672 critical path: complete the array-index →
   `trueSupports` bridge (#7921), then re-scope #7894 against the landed (A) family
   and the #7918 short-vector data, identifying which of (B)/(C) are now derivable
   and which remain genuine residuals. Do not re-bundle the indexing bridge or the
   per-factor Hensel package as free hypotheses — building them from (A) +
   `toMonicPrimeData?` success is the point.
3. Plan or schedule the BHKS precision-soundness theorem
   (`PartitionRefinement.lean:447`): it is the remaining gate (with partition
   coverage) between the conditional fast disjunct and an unconditional fast
   raw-irreducibility substrate for the HO-1 capstone.
4. Continue the executable→Mathlib transport thread opportunistically; it remains
   the highest-yield recent vein (GF(2)/GF(q) cleared 25 genuine `sorry`s this
   window), with the HexGF2Mathlib/Field.lean field-structure cluster the next
   natural target.
