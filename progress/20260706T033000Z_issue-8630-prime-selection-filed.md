# Prime-selection profiling done; perf issue #8630 filed

## Accomplished

- Added RELIFT_PROFILE=prime mode to the spike (on PR #8628's branch):
  choosePrimeData? costs 0.8/2.1/5.4/10.4/18.7 ms at split deg
  8/12/16/20/24 (~cubic), phi15 0.48 ms, SD4 8.4 ms; a single
  isGoodPrime check at deg 24 costs 424 us (should be ~1 us of word
  arithmetic). perf: closure dispatch ~12%, allocator ~15%, box/unbox
  shims, generic nullspace, Int-extgcd inverse fallbacks.
- Root cause: the whole selection path (DensePoly.gcd in isGoodPrime and
  the Berlekamp constant sweep, fixedSpaceKernel matrix/nullspace) runs
  boxed typeclass-generic ZMod64 arithmetic. HexPolyFp/Packed.lean already
  has the packed-kernel + csimp pattern; its documented modByMonic swap
  never landed.
- Filed https://github.com/kim-em/hex-dev/issues/8630 with four
  deliverables (land the modByMonic csimp swap; packed FpPoly gcd; packed
  ZMod64 nullspace; word-arithmetic ZMod64 inverse), all output-preserving.
- Report section "Prime selection breakdown" added; cross-linked on #8625.

## Current frontier

PR #8628 CI pending on the latest push (monitor active).

## Next step

Confirm CI green on #8628. #8630 is ready to claim as the next perf item;
then #8621; then re-measure the per-remainder recursion.

## Blockers

None.
