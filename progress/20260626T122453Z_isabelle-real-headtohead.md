# Isabelle is ms-scale at real degrees: we are ~4-11x off, not ~1000x

## The correction that reframes everything

Every prior "we are ~1000x slower / fundamental floor / useless implementation"
claim rested on an UNMEASURED assumption: that the verified Isabelle/AFP BZ stays
microsecond-fast at high degree. It does NOT. The earlier ~8us figure was deg6
only, and IPC-dominated. Driving the SAME cached wrapper directly (Python,
persistent subprocess, distinct shifted inputs, R=3000) gives Isabelle's real
per-call wall:

| deg | Isabelle | our spike k=4 | our spike Mignotte-k | k=4 ratio |
|----:|---------:|--------------:|---------------------:|----------:|
|  8  |  419 us  |  1.75 ms |  3.1 ms  |  4.2x |
| 12  |  755 us  |  4.5 ms  | 10.8 ms  |  6.0x |
| 16  | 1.55 ms  | 11.9 ms  | 30.4 ms  |  7.7x |
| 20  | 2.39 ms  | 22.2 ms  | 59.5 ms  |  9.3x |
| 24  | 3.47 ms  | 39.2 ms  | 101 ms   | 11.3x |

(Isabelle wall includes ~17us Python IPC per call, negligible >=deg8; Lean
numbers are pure in-process compute. IPC baseline [1]: 17 us/call.)

## Reading

- We are ~4-11x slower than the verified Isabelle reference with the smart
  classical algorithm + low-precision (k=4) lift. NOT 1000x. The gap is
  constant-factor + scaling, not a language/substrate floor.
- The ratio GROWS with degree (4x -> 11x), so on top of constant factors there is
  an asymptotic gap: our sequential split-tree Hensel lift is ~O(n^2) and
  recomputes `Array.polyProduct rest` each step; a balanced product tree is
  ~O(n log^2 n). choosePrimeData?/Berlekamp scaling also contributes.
- The low-precision (k=4) lift is correct on the corpus (recovers all n linear
  factors at every degree) and gives ~2.6x over the conservative Mignotte
  precision. It needs an incremental-with-Mignotte-backstop formulation to be
  sound in general, but the direction is validated.

## Closing the ~10x to beat Isabelle (all Int-native, substrate is fine)

1. Hensel lift: balanced product-tree instead of sequential split; precompute
   subproduct tree once; incremental precision with early stop + Mignotte
   backstop. (Biggest single item; dominates at Mignotte-k, large at k=4.)
2. choosePrimeData?: dominant at low precision (~8 ms at deg16). Speed up the
   squarefreeness gcd checks and Berlekamp; FpPoly is already ZMod64 (machine
   word), so this is per-op DensePoly overhead + op-count, not substrate.
3. DensePoly per-op overhead: revisit after 1-2; the ArithFloor microbench's
   per-op story needs re-measuring in context (the standalone numbers were
   inflated by per-iteration operand/checksum overhead).

## Caveats / honesty

- Corpus so far is split (x-a)..(x-a-(n-1)) plus Phi_15. Need adversarial
  many-mod-p-factor inputs (Swinnerton-Dyer) where recombination and high
  precision actually bite, for a fair worst-case head-to-head.
- These spike numbers are UNPROVEN code. Integration + proofs come after we
  confirm we can beat Isabelle.

## Next step

Rewrite the Hensel lift as a balanced product tree (unproven, in the spike) and
re-measure vs Isabelle. Then attack choosePrimeData?/Berlekamp.
