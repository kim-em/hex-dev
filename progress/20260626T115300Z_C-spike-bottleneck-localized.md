# C spike: smart recombination is free; bottleneck is prime-scan + Hensel lift

Built a minimal end-to-end classical Berlekamp-Zassenhaus spike (UNPROVEN,
`HexBench/ClassicalSpike.lean`, lean_exe `hex_classical_spike`) reusing the
library's `choosePrimeData?` + `henselLiftData` and replacing the materialized-
powerset recombination with a smart, size-ordered, factor-removing search.
Correctness sanity-checked via #eval: (x-1)..(x-6) -> six linear factors,
Phi_15 -> left irreducible (deg 8), (x-1)..(x-12) -> twelve linear.

## Accomplished

CRITICAL harness lesson: the first "1.76 us/call at deg24" was a loop-invariant
HOISTING artifact (`classicalFactorInt f` with fixed `f` lifted out of the timing
loop; I was partly timing `degreeSignature`'s mergeSort). Hardened the harness to
factor a family of distinct shifted inputs and checksum real factor coefficients.

Honest end-to-end (un-hoisted), Int variant, 16 distinct inputs/degree:
| input | per-call |
|---|---|
| (x-a)..(x-a-3)  deg4  | 0.41 ms |
| deg8  | 3.1 ms |
| deg12 | 10.9 ms |
| deg16 | 30.6 ms |
| deg20 | 56.9 ms |
| Phi_15 deg8 | (irreducible, fast) |

Per-phase breakdown (cumulative; differenced):
| phase | deg8 | deg12 | deg16 |
|---|---|---|---|
| choosePrimeData? (94-prime scan) | 1.2 ms | 3.0 ms | 8.1 ms |
| henselLiftData (lift only)       | 1.8 ms | 7.4 ms | 20.9 ms |
| recombination (the new smart code) | ~8 us | ~83 us | ~83 us |

Over-precision ruled out: computed precision is already minimal (k=8/12/16);
fixed k=24 is no faster. Hensel cost is the lift's per-operation cost x #factors x
growing modulus, not excess precision.

## Findings

1. The smart-recombination CLASSICAL-BZ ARCHITECTURE IS CORRECT and the
   recombination is essentially FREE (~80 us even at deg16). The earlier
   "implementation is useless" worry does not apply to the algorithm shape.
2. The entire cost is two REUSED library subroutines: `choosePrimeData?`
   (scores up to 94 primes, factoring mod p for each) and, dominantly,
   `henselLiftData` (the Hensel lift). Both are independent of the
   Int-vs-machine-word axis.
3. Machine-word (single UInt64) is a DEAD END for this problem: f's own
   coefficients exceed 2^63 by deg~20 (24! ~ 6e23); the lift modulus p^k exceeds
   2^63 by deg16 (17^16 ~ 5e19); and mod-p^k `mulmod` needs modulus < 2^32
   (overflow of the 64-bit product), reached by deg~10. So machine words cannot
   reach the input sizes that matter. Int (GMP), as in the LLL path that already
   beats Isabelle, is the correct substrate.

## Current frontier

To beat Isabelle the targets are now concrete and Int-native:
- choosePrimeData?: stop at first good prime (or score far fewer) instead of
  scanning all 94 — 8 ms at deg16 for prime selection is pure waste.
- henselLiftData: make the lift fast — likely faster DensePoly arithmetic and/or
  an incremental lift-and-try-recombination loop that stops at the lowest
  precision where recombination succeeds (classical BZ early-exit), instead of
  computing the full conservative Mignotte precision up front.

## Next step

Attack the Hensel lift (dominant cost) and the prime scan. Both reused by the
BHKS path too, so wins compound. Recombination is done.

## Blockers

None. Spikes (`HexBench/ArithFloor.lean`, `HexBench/ClassicalSpike.lean`) are
untracked evidence artifacts; `lakefile.lean` has two throwaway lean_exe entries.
