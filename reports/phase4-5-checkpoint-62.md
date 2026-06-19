# Phase 4/5/6 checkpoint 62

Scope: checkpoint for the ~85 PRs merged after summarize issue #7912 (sixty-first
checkpoint, closed 2026-06-18T12:56:25Z) — the window running from #7919 through
#8111. Two threads dominate. First, the **Phase 6 grind-automation sweep** reached
near-completion across both the executable libraries and the `*Mathlib` bridge
layers: equation-shaped public `@[simp]` lemmas were promoted to
`@[simp, grind =]` (annotation-only) library by library, and the clean
public-equation targets are now essentially exhausted. Second, the
**HexGF2Mathlib/Field.lean field-structure `sorry` cluster was fully cleared** (12
genuine `sorry`s → 0), which is the headline correctness reduction this window:
the repository is now down to **2 genuine `sorry`s**, both capstone-gated on the
HO-1 / directive #2564 chain. The fast-BHKS van Hoeij CLD raw-irreducibility
substrate also advanced substantially and the old capstone issue #6672 closed,
but the two headline `sorry`s themselves remain open.

## Landed work

~85 PRs merged after checkpoint 61 (#7919–#8111). Grouped by theme.

### Phase 6 grind-automation sweep (dominant by PR count)

Promotion of equation-shaped public `@[simp]` lemmas to `@[simp, grind =]` so
`grind` can E-match them, leaving `↔`/`<`/`≤`/`Ne`/`Associated`/conjunction/
`let`-binder shapes as `@[simp]`-only. This is annotation-only and risk-bounded
(each promoted rule strictly reduces RHS term structure, so it terminates).

- **Executable libraries.** HexPolyZ (#7956, #7994), HexPolyFp (#7958, #7986,
  #7997, #8002, #8005, #8007), HexLLL (#7962), HexGramSchmidt (#7964, #8052),
  HexMatrix (#7966, #7993, #8026 RREF, #8031), HexHensel (#7968, #7999, #8009,
  #8027 quadratic multifactor), HexModArith (#7971, #8021, #8041 HotLoop, #8055
  Montgomery context), HexGFq (#7972), HexConway (#7976), HexGF2 (#7977, #8004,
  #8013, #8019, #8046 Field.lean GF2nPoly cluster, #8047 Euclid, #8087 Clmul),
  HexArith (#7984 ExtGcd, #8025 UInt64 Wide, #8033/#8038 Barrett, #8049 choose,
  #8091 ReduceNat), HexPoly (#8011 Dense, #8043 Euclid), HexGFqRing (#8015,
  #8020 Operations), HexGFqField (#8036 repr cluster), HexBerlekamp (#8017
  DistinctDegree, #8087 RabinSoundness).
- **Mathlib bridge layers** (merge-gating via `ci.yml`). HexPolyMathlib (#8075),
  GramSchmidt mathlib rows (#8077), HexPolyZMathlib (#8080, #8093 SchurSzego,
  #8095 RobinsonForm/Mignotte), Factor.lean (#8088), HexGF2Mathlib (#8098),
  HexGFqMathlib (#8100), HexMatrixMathlib (#8105 Basic/Determinant/Core),
  HexModArithMathlib (#8107), HexBerlekampMathlib (#8109),
  HexBerlekampZassenhausMathlib (#8111 Lattice).

The remaining unswept files now carry only excluded shapes (`↔`/`≠`) or `private`
lemmas, or are the small unclaimed leftovers #8104 (HexMatrixMathlib
RankSpanNullspace, 3 lemmas) and #8112 (HexGFqMathlib GF2q.lean, 1 lemma).

### HexGF2Mathlib/Field.lean field-structure cluster cleared (headline `sorry` reduction)

Checkpoint 61 carried 12 genuine `sorry`s in `HexGF2Mathlib/Field.lean` (the
`modulusFpPoly_degree_pos` + `ofGeneric`/`toGeneric` round-trip/homomorphism
obligations across the GF2n and GF2nPoly namespaces). This window cleared all of
them:

- #7919 close 3 of the 4 modulus-transport `sorry`s and repair `toFpPoly_mul`.
- #7927 make `GF2nPoly.modulusFpPoly_degree_pos` (the fourth modulus `sorry`);
  note the recorded premise correction — `Hex.GF2Poly.Irreducible` admits the
  unit `f = 1`, so positive degree comes from a carried wrapper invariant, not
  from irreducibility directly.
- #7942 close the `GF2n.toGeneric` RingEquiv obligations.
- #7948 close the `GF2nPoly.toGeneric` RingEquiv obligations.

`HexGF2Mathlib/Field.lean` now carries no `sorry`. (The library's `status.py`
phase counter still reads Phase 5; the counter bump has not yet been recorded.)

### Fast-BHKS van Hoeij CLD raw-irreducibility chain (directive #2564)

The fast-path raw-irreducibility substrate advanced from short-vector data to an
assembled fast raw guarded irreducibility across branches:

- **Producers / recovered lifts.** #7929 (recovered-lift Hensel semantics from
  `toMonicPrimeData`), #7935 (emitted-indicator support bridge), #7954 (monic
  recovered-lift wrapper), #8059 (non-monic primitive recovery from `toMonic`
  lifts), #8060 (package BHKS recovered-lift cut hypotheses), #8069 (fast-core
  hsize witness), #8071 (fast-support partition equality).
- **Precision / CLD-adequacy gating.** #7938 (correct the fast-core precision
  schedule), #7959 (CLD-adequacy acceptance gate to fast-core), #7980 (derive
  BHKS `hsep`/`hthr` from the CLD-adequacy gate), #7981 (discharge `hfloor`,
  `cldCoeffFloor ≤ factorFastPrecisionCap`).
- **Assembly.** #8073 (assemble BHKS fast raw irreducibility from cut data),
  #8083 (correct the fast raw irreducibility contract for recorded entries),
  #8101 (quadratic branch), #8103 (small-mod singleton branch). #8039 (closed
  primitive headline for nonzero factor inputs) and #8045 (FactorSoundness
  non-associated headline contract) shaped the consuming contract.
- **Scaffolding / review.** #8061 (HexBerlekampZassenhaus Phase 1 bounded
  factorization wrappers), #8085 (review confirming the fast raw irreducibility
  cut assembly is sound).

The old capstone issue #6672 (`assemble factor_irreducible_of_nonUnit from branch
proofs`) and its residual #4172/#4170/#4819/#7894/#7921 closed this window. The
two underlying code `sorry`s are nonetheless still open (see Quality metrics);
the live successor gates are now #8068 and #4818 (see Blocking structure).

### Perf

- #8065 speed up the DensePoly long-division runtime path.
- #8066 first-suitable prime selection and plain-remainder gcd.
- #8076 skip and hoist the van Hoeij fast-core precision floor.

### Docs / boundary skills

- #7930 (fast-path `liftData.k` double-log collapse), #7950 (post-#7938
  `hsep`/`hthr` success-precision trap persistence), #7991 (floor-gate-vs-cap
  bad-vector-exclusion gap), #7911/#7931 (HexGFqMathlib Phase 6 docs), #7953
  (HexPolyZMathlib Phase 5 completion record).

## Phase state

`scripts/status.py` at HEAD `b0e3d93f`:

- **Executable front.** Phase 6 (proof polishing) across HexArith, HexMatrix,
  HexModArith, HexGramSchmidt, HexGF2, HexPolyZ, HexLLL, HexPolyFp, HexGFqField,
  HexHensel, HexConway, HexGFq. HexPoly is at Phase 7 (user-facing docs).
  HexBerlekamp is at Phase 4. HexBerlekampZassenhaus shows Phase 1 (scaffolding)
  ready — the directive #2564 rollback is still in force.
- **Mathlib front.** Phase 7 ready: HexGFqMathlib, HexModArithMathlib. Phase 6
  ready: HexPolyMathlib, HexGramSchmidtMathlib, HexPolyZMathlib, HexHenselMathlib.
  Phase 5 (implementation loop): HexMatrixMathlib, HexLLLMathlib, HexGF2Mathlib.
- **Blocked.** HexBerlekampMathlib (Phase 4, waits on `HexBerlekamp.done_through
  ≥ 4`); HexBerlekampZassenhausMathlib (Phase 3, waits on
  `HexBerlekampZassenhaus.done_through ≥ 3`).
- **Done.** HexGFqRing.
- **Deferred (SPEC-ready).** HexRoots, HexResultant, HexNumberField and their
  Mathlib counterparts.

## Quality metrics

Repository-wide `git grep` over `*.lean` at HEAD `b0e3d93f`:

- `sorry`: **2 genuine tactic `sorry`s.** A raw `git grep -nw sorry` reports 5
  hits; 3 are prose/comment mentions (`single localised sorry.` at
  `HexBerlekampZassenhausMathlib/Basic.lean:231`, the forbidden-token checklist
  line at `HexBerlekampZassenhausMathlib/IntReductionMod.lean:1288`, and the
  `bareiss_eq_det` reference comment at `HexMatrixMathlib/Determinant.lean:24`).
  The 2 genuine `sorry`s, both capstone-gated on directive #2564, are:
  - `Hex.ZPoly.isIrreducible_iff` (`HexBerlekampZassenhausMathlib/Basic.lean:235`,
    issue #4818).
  - `factor_irreducible_of_nonUnit`
    (`HexBerlekampZassenhausMathlib/FactorSoundness.lean:20`, issue #8068).

  This is down from 14 genuine at checkpoint 61. The drop is real progress: the
  12-`sorry` `HexGF2Mathlib/Field.lean` cluster was cleared (see above). No
  `sorry` exists in any Mathlib-free executable library; the single Mathlib
  bridge layer that still carries `sorry`s (HexBerlekampZassenhausMathlib)
  compiles (a `sorry` is a warning, not an error), so `ci.yml`'s transitive build
  stays green.

  Note: the #8114 planner snapshot listed `sorry: 5`; that count included the
  three comment/docstring mentions above plus an over-count of `Basic.lean`. The
  authoritative genuine count is **2**.

- `axiom`: **0 real declarations** (`git grep -nE '^[[:space:]]*axiom '` reports
  none).

- `native_decide`: **0 real tactic uses.** The 2 grep hits are comment text — the
  not-depends-on note at `HexArith/Nat/Prime.lean:344` and the forbidden-token
  checklist line at `HexBerlekampZassenhausMathlib/IntReductionMod.lean:1288`.

## Blocking structure for directive #2564

The headline gap is unchanged in shape: the directive #2564 capstone is the two
`HexBerlekampZassenhausMathlib` `sorry`s, both still open. The old capstone issue
#6672 closed once the fast raw-irreducibility *substrate* landed
(#8073/#8083/#8085/#8101/#8103), but closing the issue did not retire the code
`sorry`s — that work moved to live successor gates:

- **#4818** (`Hex.ZPoly.isIrreducible_iff`, open) — the executable irreducibility
  checker ⟺ predicate bridge, a declared dependency of directive #2564.
- **#8068** (`close default factor irreducibility from raw branch proofs`, open) —
  the successor to #6672 that actually discharges `factor_irreducible_of_nonUnit`.
  It blocks on **#6779** (`B-builder — BadVectorBridge / B8 separation over all of
  L' minus W`, open), the fast-BHKS separation (B) producer.

So this window assembled the fast raw-irreducibility disjunct and closed the
assembly-tracking issues, but the remaining genuine gates are the B-side
separation producer (#6779) feeding #8068, and the executable iff (#4818).
Directive #2564 itself remains `blocked`. Do not overstate readiness: the HO-1
headline correctness theorem is not discharged.

## Current frontier

- **Open PRs:** #8113 (HexPolyMathlib/Euclid.lean grind coverage), #2656 (spec:
  hex-real-roots and hex-sturm, status: planned).
- **Unclaimed issues** (excluding this summarize issue): #8104
  (HexMatrixMathlib/RankSpanNullspace grind, 3 lemmas), #8112 (HexGFqMathlib
  GF2q.lean grind, 1 lemma) — the last clean public-equation grind leftovers.
- **Directive #2564** remains the open umbrella, blocked on #4818; the
  `factor_irreducible_of_nonUnit` route runs #6779 → #8068.

## Recommended next actions

1. Land the two grind leftovers (#8104, #8112) to close out the Phase 6
   public-equation sweep; after that the clean grind targets are exhausted and
   further grind work needs the harder `↔`/`Ne` shapes or `private`-lemma scope,
   which is lower yield.
2. Record the HexGF2Mathlib phase-counter bump now that `Field.lean` is
   `sorry`-free, and re-survey whether HexGF2Mathlib/HexMatrixMathlib/HexLLLMathlib
   can advance off Phase 5.
3. Drive the directive #2564 critical path: #6779 (B-side BadVectorBridge / B8
   separation) → #8068 (`factor_irreducible_of_nonUnit` from the now-assembled raw
   branch proofs), and #4818 (`isIrreducible_iff`). These two genuine `sorry`s are
   the entire remaining correctness gap; everything else in the tree is `sorry`-free.
4. Continue perf work on the van Hoeij / DensePoly hot paths opportunistically;
   it does not gate correctness but improves the bench wallclock budget.
