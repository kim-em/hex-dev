# Phase 4/5/6 checkpoint 56

Scope: checkpoint for the 40 PRs merged after summarize issue #7034 (closed
2026-06-14T04:46:23Z). Two threads dominate: the directive #2564 HO-1 substrate
(van Hoeij CLD rewrite, the scale→dilate / monic-lift migration, and the CLD
resultant / syzygy valuation chain) and a broad Phase 6 docstring + linter
cleanup across the executable libraries. The frontier remains directive #2564
and its HO-1 support chain.

## Landed work

Forty PRs merged after checkpoint 55. Grouped by topic rather than listed
one-by-one.

### HO-1 substrate: scale→dilate and monic-lift migration

The BZ recombination proof model continued migrating off the stale scaled-
recombination framing toward monic, recovered-coordinate data and the dilate
transform. This is the live substrate for directive #2564.

- #7045 added the `RecoveredAtLift` monic-coordinate bound producer.
- #7050 migrated monic partition consumers to lifted candidate equality (#7036).
- #7060 partially migrated the fast BHKS path to the monic lift.
- #7081 migrated the primitive scaled search to `liftedRecoveryCandidate`.
- #7085 derived the empty-prefix modulus bound without scale recovery (1 of the
  7 `HexBerlekampZassenhausMathlib` `Basic.lean` errors).
- #7105 added the cap-specialized pointwise auxiliary bound wrappers.

### HO-1 substrate: CLD resultant / syzygy valuation chain

The CLD (coefficient-of-logarithmic-derivative) chain advanced the BHKS Lemma
3.2 resultant-divisibility substrate.

- #7048 added the BHKS auxiliary CLD bridge.
- #7053 proved the CLD Sylvester column-image and syzygy column-divisibility
  lemmas.
- #7075 assembled the CLD syzygy resultant-divisibility theorem and its ZPoly
  bridge.
- #7074 derived the `liftedTrueSupports` B8 partition count from the
  support-factor bijection.
- #7100 derived the bad-vector resultant bridge.

### Phase 6 docstring and linter cleanup

The Phase 6 polish queue stayed broad; many narrow, library-local slices landed.

- HexPolyFp: #7049 (closed `SquareFree` public product + coprime wrappers),
  #7061 `Basic.lean`, #7064 `Compose.lean`, #7065 `SquareFree.lean`,
  #7080 `Quotient.lean`.
- HexGF2: #7073 `Field.lean`, #7096 remaining `Basic`/`Field`/`Irreducibility`.
- HexGramSchmidt: #7052 (linter), #7069 `Basic.lean`.
- HexLLL: #7051 (linter), #7078 `Basic.lean`, #7119 `Bench.lean`.
- HexPolyZ: #7063 (linter), #7077 `Mignotte.lean`.
- HexHensel: #7086 `Linear.lean`.
- HexGFq: #7087 `Basic.lean`.
- HexPolyMathlib: #7090 and #7095 `Basic.lean`.
- HexConway: #7093 `Basic.lean`.
- HexArith: #7102 `ExtGcd.lean`.
- HexMatrix: #7101 (determinant simp lemmas), #7108 `Basic.lean`.
- HexModArith: #7114 and #7115 `Basic.lean`, #7117 `Ring.lean`.

### Process, tooling, and diagnosis

- #7079 fixed the bench to measure the Isabelle-certified floor in-run so
  `n=15` survives the adjustment.
- #7106 recorded a skill note on the `#check` probe for additive wrappers in
  red files.
- #7107 documented the HexPoly bench rung adapters.
- #7123 recorded the #7110 premise diagnosis and the `set_option` placement
  gotcha.

## Phase state

`scripts/status.py` reports the executable dispatch front largely in Phase 6
proof-polishing: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt,
HexGF2, HexPolyZ, HexLLL, HexPolyFp, HexGFqField, HexHensel, HexConway,
HexGFq, and HexPolyMathlib are all Phase-6 ready. `HexBerlekamp` is at Phase 4.
`HexBerlekampZassenhaus` remains at Phase 1 (library scaffolding).

Mathlib-side queues stay split by dependency:

- Phase 5 ready: HexMatrixMathlib, HexModArithMathlib.
- Phase 4 ready: HexGramSchmidtMathlib, HexPolyZMathlib, HexHenselMathlib,
  HexGF2Mathlib.
- Blocked: HexLLLMathlib (waits on HexGramSchmidtMathlib >= 4),
  HexBerlekampMathlib (waits on HexBerlekamp >= 4), HexGFqMathlib (waits on
  HexGF2Mathlib >= 4), and HexBerlekampZassenhausMathlib (Phase 3, waits on
  `HexBerlekampZassenhaus.done_through >= 3`).

HexGFqRing is fully done. HexRoots/HexResultant/HexNumberField and their
Mathlib counterparts remain SPEC-ready but implementation-deferred.

## Quality metrics

Repository-wide Lean grep (excluding `.lake/`):

- `sorry`: 68, all confined to the non-CI-built Mathlib-side layers:
  HexGF2Mathlib 23, HexBerlekampMathlib 19, HexGFqMathlib 15,
  HexHenselMathlib 6, HexBerlekampZassenhausMathlib 4, HexMatrixMathlib 1.
  No `sorry` exists in any CI-built executable library; the count is unchanged
  from checkpoint 55.
- `axiom`: 0 real declarations. The grep hits are all docstring/comment
  mentions, not `axiom` declarations. (The planning-time count for this issue
  noted axioms "down from 9 at the prior checkpoint"; the real declaration
  count was already 0 at checkpoint 55 and remains 0.)
- `native_decide`: 0 real tactic uses. The 2 grep hits are both comment text
  (a checklist line in `HexBerlekampZassenhausMathlib/IntReductionMod.lean` and
  a line in `HexArith/Nat/Prime.lean` stating the code does *not* depend on
  `native_decide`).
- `TODO`/`FIXME`: 1, a comment match, not an open work marker on a proof.

The headline gap between goals and current state is unchanged: every remaining
`sorry` sits in the Mathlib boundary layers, which CI does not build, so a
whole-library `lake build` of those targets is expected to surface them. The
executable Mathlib-free stack carries no proof debt.

## Current frontier

Open PRs:

- #7126 `fix: transport factorFast schedule recovery from henselLiftData to
  toMonicLiftData` (closes #7122) — currently in merge conflict.
- #7124 `feat: derive dilated-centered-lift reconstruction from
  RepresentsIntegerFactorAtLift` (repair-claimed) — currently in merge conflict.
- #7125 `doc: record #7121/#7122 scale→dilate reroute premise diagnosis`.
- #2656 draft SPEC PR for real roots and Sturm.

The #7110 re-scope (per #7123 diagnosis) split that issue into two independent
migrations:

- #7121 `fix: remove unsound scale congruence and reroute recovery consumers to
  the dilate model` — `scale c p` (coeff `c·pₙ`) is not `dilate c p` (coeff
  `cⁿ·pₙ`), so `productCongruence_of_representsIntegerFactorAtLift` is unsound
  as stated and must be removed and rerouted, not patched.
- #7122 `fix: transport factorFast schedule recovery from henselLiftData to
  toMonicLiftData` — the executable
  `factorFast_ne_none_of_core_recovery_on_schedule` now expects
  `toMonicLiftData` while the producer still builds `henselLiftData`.

## Blocking structure for directive #2564

- **Dependency cycle to untangle.** `coordination orient` currently shows
  #7044 (`migrate the fast BHKS path lift to the monic transform`) blocked on
  #7121 and #7122, while #7121 and #7122 are each blocked on #7044. This is a
  self-referential cycle: nothing in the trio is dispatchable until the next
  planner/replan cycle breaks it (most likely by removing the #7121/#7122 →
  #7044 back-edges, since the two re-scoped halves are the prerequisites for the
  #7044 migration, not the other way around).
- The HO-1 capstone #6672 (`assemble factor_irreducible_of_nonUnit`) and the
  FactorSoundness headline packaging (#6867 raw primitive package, #6868
  non-associated headline contract) remain blocked behind #6771/#6774 and the
  CLD/resultant chains.
- The B-builder fan-out (#6786, #6783, #6779, #6777, #6771) is blocked behind
  #7044, #7120, and each other.
- The HO-1 CI required-check #6866 stays blocked on #7121/#7122 and ultimately
  until `HexBerlekampZassenhausMathlib` builds green, currently impossible while
  its 4 `sorry`s and the upstream Mathlib-layer debt remain.

## Recommended next actions

1. Break the #7044 ↔ #7121/#7122 cycle first: a planner should drop the
   #7121/#7122 → #7044 back-edges so the two re-scoped migrations become
   dispatchable, then keep #7044 blocked on them.
2. Repair or supersede the conflicting PRs #7126 and #7124; both are on the
   scale→dilate / monic-lift front and are currently wedged on merge conflicts,
   so the substrate cannot advance until one lands.
3. Drive the CLD/resultant chain (#7048/#7053/#7075/#7074/#7100 landed) into
   its downstream consumers without reintroducing a direct shortcut from
   "shared factor mod `p^k`" to `p^(k*d)` divisibility.
4. Keep #6866 parked until `HexBerlekampZassenhausMathlib` is `sorry`-free and
   builds; requiring HO-1 before then would wedge CI.
5. Keep Phase 6 polish slices narrow and library-local; the two open docstring
   issues (#7128 HexHensel `Quadratic.lean`, #7129 HexPoly `Euclid.lean`) are
   the right granularity.
