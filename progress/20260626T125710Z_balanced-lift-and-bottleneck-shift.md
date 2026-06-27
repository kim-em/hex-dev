# Balanced Hensel tree: modest win; real low-precision bottleneck is choosePrimeData?

## Accomplished

Added a balanced product-tree Hensel lift to the spike (`balancedLift`): split
mod-p factors in half, lift the 2-way split via `henselLiftQuadratic`, recurse.
O(log r) depth vs the library's sequential O(n.r) `multifactorLiftQuadraticList`.
Correct on the corpus (recovers all n factors).

seq vs balanced, us/call (100 reps, 16 distinct inputs/degree):
| deg | seq Mignotte | balanced Mignotte | ratio | seq k=4 | balanced k=4 |
|----:|-------------:|------------------:|------:|--------:|-------------:|
|  8  |  3103 |  2548 | 1.22x |  1750 |  1655 |
| 12  | 10776 |  8210 | 1.31x |  4530 |  3930 |
| 16  | 30423 | 22161 | 1.37x | 11640 |  9948 |
| 20  | 58495 | 40300 | 1.45x | 20919 | 17608 |
| 24  | 98307 | 68025 | 1.44x | 38739 | 31947 |

## Findings

1. Balanced tree = modest constant-factor + slight-asymptotic win (1.22x at deg8
   -> 1.44x at deg24) at full Mignotte precision; nearly nothing at k=4. The
   lift's TREE SHAPE was not the main lever.
2. The bottleneck is precision-dependent:
   - At conservative Mignotte precision, the lift dominates (huge p^k arithmetic).
   - At the low precision we actually want (k=4, sound by exactQuotient?), the
     lift shrinks and choosePrimeData? becomes ~80% (e.g. deg16: choose ~8 ms of
     ~10 ms total). choosePrimeData? = squarefreeness gcd-checks over F_p (rejects
     primes < root-spread) + Berlekamp factorization at the good prime.
3. Best current spike config (balanced + k=4) vs Isabelle:
   - deg16: 9.95 ms vs 1.55 ms -> 6.4x
   - deg24: 31.9 ms vs 3.47 ms -> 9.2x
   So ~6-9x off with everything turned on. Architecture validated; remaining gap
   is core mod-p arithmetic (Berlekamp/gcd) and per-op lift cost.

## Current frontier

Next lever is choosePrimeData?/Berlekamp (dominant at low precision), not the
lift. Berlekamp at deg16 is inherently ~ms with current FpPoly arithmetic
(Frobenius powering O(n^2) mults + nullspace O(n^3)); Isabelle's is faster on
constants. These are core PROVEN components (HexBerlekamp/*, HexPolyFp/*), so
optimizing them is proof-sensitive.

## Decision point for Kim

To close the last ~6-9x and beat Isabelle, the work moves into the core mod-p
arithmetic (Berlekamp, F_p gcd, FpPoly mul/div) and the lift's per-op cost. This
is bounded but touches heavily-proven library code. Options: (a) optimize the
proven core in place (risk: many proof breakages, big rebuilds); (b) build a fast
unproven core in the spike to PROVE we can beat Isabelle end-to-end first, then
port + reprove; (c) accept ~Isabelle-parity-within-10x as the practical target.

## Next step

Pinpoint choosePrimeData?'s internal split (gcd-scan vs Berlekamp) and prototype
a faster Berlekamp / squarefree test in the spike; re-measure vs Isabelle.

## Blockers
None. All spike work is unproven and isolated in HexBench/.
