# issue-8606: kernel-friendly ZMod64/DensePoly specs with @[csimp] impls

Session type: feature (issue #8606), branch `issue-8606`.

## Accomplished

- `ZMod64.add`/`sub` (HexModArith/Basic.lean) are now one-line `ofNat`
  specifications; the branchy division-free machine-word bodies moved to
  `addImpl`/`subImpl` with proved `@[csimp]` equalities. `toNat_add`/`toNat_sub`
  statements unchanged, proofs now one-liners; the old branch analyses back the
  impl lemmas.
- `DensePoly.mul` (HexPoly/Operations.lean) is now a head-first list-walking
  convolution (`mulRow`/`mulRows`); the in-place `Array` loop moved to
  `mulImpl` with a proved `@[csimp]` equality. The list spec performs the same
  additions in the same order as the array loop, so `mul_eq_mulImpl` needs no
  algebraic laws on `R`. `coeff_mul` statement unchanged. Added generic
  `DensePoly.size_mul_le`, replacing HexPolyZ's private array-fold size lemmas.
- `@[csimp]` theorems are registered *before* the operator instances so the
  compiled instance closures reference the impl bodies (verified in generated
  C: `instMulOfAdd` → `mulImpl`, `instAdd` → `addImpl`).
- HexGFq/CrossCheck.lean `maxHeartbeats` overrides lowered 10M/5M → 1M
  (400k is too low: the line-999 check needs more).
- SPECs: new design principle 11 (kernel-facing spec, `@[csimp]` runtime impl)
  in SPEC/design-principles.md; hex-mod-arith SPEC operations section updated;
  HexPolyFp/Packed.lean header comment updated.

## Measurements

- `HexGFq.CrossCheck`: 313 s → 32 s elaboration (same machine, same build),
  with no changes to the cross-check proofs themselves. Tree's slowest module
  is now HexBerlekampZassenhaus.BhksCandidates (49 s), unrelated.
- Full `lake build`: 4157 jobs green, no new warnings.
- Bench verify: hexmodarith 13/13, hexgfq 6/6, hexpoly Lean-side all ok
  (incl. mul/add/sub checksums, i.e. the csimp'd operations reproduce the
  recorded values); the 44 hexpoly FLINT-runner failures are
  `python-flint not available` on this machine only (CI installs it).

## Current frontier

Implementation complete and verified locally; PR being opened.

## Next step

Second opinion, then PR closing #8606. Possible follow-up (not this PR): the
remaining 32 s in HexGFq.CrossCheck is spread across the ~50 checks
(elaboration + kernel); the domain-aware trim-skip from the issue's follow-up
note was judged unnecessary once the O(n³) array walking was gone.

## Blockers

None.
