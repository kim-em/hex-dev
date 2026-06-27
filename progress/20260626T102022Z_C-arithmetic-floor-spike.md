# C feasibility spike: the arithmetic floor, not the algorithm or loop style

User directive: pursue C only (fast verified classical Berlekamp-Zassenhaus that
beats the verified Isabelle/AFP reference; delete everything slower). Before
committing the architecture, measured the per-operation arithmetic floor in
compiled Lean — the crux of whether C can beat Isabelle at all.

## Accomplished

Built a standalone compiled microbench `HexBench/ArithFloor.lean` (lean_exe
`hex_arith_floor`) timing schoolbook polynomial multiply at deg 8/16/24/48,
200k iters, warmup, perturbed inputs to defeat hoisting. Three variants:
- `DensePoly.mul` — the proven library op (functional: `List.range` folds +
  `acc[k]?` Option-indexing).
- `mulFast` — same algorithm, tight `Array` loop (`for in [0:n]`, `set!`/`[k]!`,
  no Lists, no Option).
- `mulFastU64` — identical tight loop over `Array UInt64` (machine words).

Results (ns per multiply):
| deg | DensePoly.mul Int | mulFast Int | mulFast UInt64 |
|----:|------------------:|------------:|---------------:|
|  8  | 12964 | 11652 |  1275 |
| 16  | 42760 | 40431 |  3561 |
| 24  | 91896 | 87008 |  6842 |
| 48  | 349698 | 352303 | 25446 |

Findings:
1. Functional vs tight-loop Int: ~6% only. The allocation-heavy style is NOT the
   bottleneck. (My initial hypothesis was wrong.)
2. Int vs UInt64: ~10-14x, widening with degree. Lean `Int` arithmetic (non-
   inlined `lean_int_*` extern calls + boxing/overflow dispatch) is the dominant
   per-op cost vs GHC's inlined/unboxed machine ints in the exported Isabelle.
3. A single deg-24 Int multiply (92 us) alone exceeds Isabelle's whole deg-24
   factorization (~8 us). The gap is the arithmetic substrate + the heavy
   full-degree work of the BHKS lattice path, not loop microstyle.

## Current frontier

C architecture verdict: idiomatic Lean `Int`/DensePoly arithmetic cannot beat
Isabelle. A competitive classical BZ must keep hot arithmetic in machine-word
modular form (reuse the existing native ZMod64 substrate for mod-p; Hensel-lift
and recombine in UInt64 modular arithmetic while p^k < 2^63, escalating to a
small fixed multi-word bignum only when forced) and use smart incremental
recombination (size-ordered, factor removal) instead of the materialized
powerset in `subsetSplitsWithFirst`.

Real cost of C, honestly: a machine-word implementation does NOT inherit the
existing Int/DensePoly soundness proofs directly — correctness must be re-proven
for the new representation (the math lemmas port; the executable bridge does
not). This is the genuine price.

## Next step

Build a minimal end-to-end classical BZ spike (unproven): reuse
`berlekampFactorsModP` + Hensel, machine-word modular arithmetic, smart
recombination; benchmark end-to-end vs the cached Isabelle wrapper on
(x-1)...(x-n) and Phi_15. Confirm we can actually beat Isabelle before investing
in the (large, partly-portable) correctness proofs.

## Blockers

None. Open strategic question for Kim: commit to a machine-word arithmetic
substrate (and the proof rework it implies) as the foundation of C?
