# Berlekamp–Zassenhaus: classical-vs-BHKS performance findings (2026-06-26)

This report records a focused performance investigation comparing the current
`Hex.factor` (BHKS van Hoeij CLD lattice path) and a minimal classical
Berlekamp–Zassenhaus prototype against the verified Isabelle/AFP reference
(`factor_int_poly`, exported to Haskell, GHC -O2). It supersedes the
Isabelle-comparator numbers in
[hex-berlekamp-zassenhaus-performance.md](hex-berlekamp-zassenhaus-performance.md),
which were measured against a per-call JVM-startup artifact (~820 ms/call) and
are retracted.

## Headline

The earlier framing — "Lean is ~1000× slower than Isabelle / the implementation
may be useless" — was wrong in both directions, for two separate reasons:

1. The retracted report's ~820 ms Isabelle figure was a per-call startup
   artifact; the real reference is much faster (µs at deg6, ms at deg16–24).
2. The contrary "Lean N× faster" verdicts derived from that 820 ms were equally
   invalid.

Measured honestly on the same hardware, a classical BZ prototype with smart
recombination, in plain `Int` arithmetic, is **within ~6–9× of the verified
Isabelle reference** — a constant-factor gap, not a language/substrate wall.
The architecture is sound; closing the remaining gap is deep, proof-sensitive
core-arithmetic work and is deferred.

## Method

- Reference: the cached wrapper `.cache/oracles/bz-isabelle/wrapper/bz_isabelle`,
  driven as a persistent subprocess over newline-delimited JSON
  (`{"coeffs":[...]}`, ascending), so per-call cost excludes process startup.
- Inputs: families of distinct shifted split polynomials
  `(x−1−s)…(x−n−s)` and `Φ₁₅`. Distinct inputs per call are essential — an
  early "1.76 µs/call at deg24" result was a loop-invariant **hoisting artifact**
  (a fixed input let the compiler lift the whole factorization out of the timing
  loop). All numbers below factor a rotating family and checksum real factor
  coefficients.
- Lean numbers are in-process compute (no IPC). Isabelle numbers are end-to-end
  wall including ~17 µs Python IPC per call, negligible at deg ≥ 8.
- Prototype: `HexBench/ClassicalSpike.lean` (`lean_exe hex_classical_spike`),
  unproven, reusing the library's `choosePrimeData?` and Hensel primitives with a
  new smart recombination and an optional balanced product-tree lift.

## Numbers (µs per factorization)

Verified Isabelle reference:

| deg | 4 | 8 | 12 | 16 | 20 | 24 |
|---|---|---|---|---|---|---|
| Isabelle | 144 | 419 | 755 | 1552 | 2394 | 3467 |

Classical prototype (Int), sequential vs balanced lift, conservative Mignotte
precision vs low precision k=4 (k=4 is correct on this corpus — it recovers all
n factors, since recombination's exact ℤ-division only ever accepts real
divisors):

| deg | seq Mignotte | balanced Mignotte | seq k=4 | balanced k=4 |
|---|---|---|---|---|
| 8  | 3103 | 2548 | 1750 | 1655 |
| 12 | 10776 | 8210 | 4530 | 3930 |
| 16 | 30423 | 22161 | 11640 | 9948 |
| 20 | 58495 | 40300 | 20919 | 17608 |
| 24 | 98307 | 68025 | 38739 | 31947 |

Best prototype config (balanced + k=4) vs Isabelle: **6.4× at deg16, 9.2× at
deg24.**

For contrast, the current BHKS public `factor` on the same split family is
~3.3 s at deg11 and exceeds an 8 s cap by deg15 (it uses a low Mignotte cap, the
CLD fast path misses, and it falls back to exponential 2^n subset recombination).
`factorFast` (full BHKS cap) stays polynomial but is ~130 ms at deg24 — ~40× the
classical prototype and ~37× Isabelle.

## Where the time goes (classical prototype)

- **Smart recombination is essentially free** (~80 µs even at deg16). Size-ordered
  search with factor removal peels split factors in ~O(r²) trial divisions; it is
  not the cost. (The library's old recombination materialized the powerset, hence
  the exponential BHKS fallback.)
- **The bottleneck moves with precision.** At conservative Mignotte precision the
  Hensel lift dominates (large p^k integer arithmetic). At the low precision we
  actually want, the lift shrinks and **`choosePrimeData?` (Berlekamp + per-prime
  squarefreeness gcd-checks over F_p) becomes ~80%** (≈8 ms of ≈10 ms at deg16).
- **Balanced product-tree lift** (O(log r) depth vs the library's sequential
  O(n·r) split) is a modest 1.2–1.4× win at full precision, growing slightly with
  degree; negligible at low precision.
- **Low precision is sound and a ~2.6× win.** Lifting to k=4 instead of the full
  Mignotte bound recovers all factors on this corpus. A general algorithm needs
  incremental precision with a Mignotte backstop, but the direction holds.

## Substrate notes

- `Int` (GMP) is the correct substrate, consistent with the project's Int-heavy
  LLL beating Isabelle. A standalone microbench (`HexBench/ArithFloor.lean`)
  initially suggested `Int` ops were ~10–14× a machine word, but those numbers
  were inflated by per-iteration harness overhead; in the factorization context
  the substrate is not the limiter.
- Single-word machine arithmetic is a **dead end** for this problem: `f`'s own
  coefficients exceed 2⁶³ by deg ≈ 20 (24! ≈ 6×10²³); the lift modulus p^k exceeds
  2⁶³ by deg16 (17¹⁶ ≈ 5×10¹⁹); and mod-p^k `mulmod` needs modulus < 2³² (64-bit
  product overflow), reached by deg ≈ 10. The mod-p layer (`FpPoly`/`ZMod64`) is
  already machine-word and still ms-scale, so the gap is per-operation overhead
  and op-count, not the substrate.

## Conclusion and deferred work

The classical-BZ-with-smart-recombination architecture is the right one and lands
within ~6–9× of the verified Isabelle reference in plain `Int`. Closing the last
~6–9× means optimizing the core mod-p arithmetic (Berlekamp, F_p gcd, `FpPoly`
mul/div) and the lift's per-op cost — bounded but touching heavily-proven library
components, with diminishing returns. That work is **deferred**; this report banks
the architecture finding and the prototype.

Concrete levers, in priority order, if the work resumes:
1. `choosePrimeData?` / Berlekamp (dominant at low precision).
2. Incremental-precision lift with Mignotte backstop (folds in the ~2.6× and the
   balanced tree).
3. Per-op `FpPoly`/`DensePoly` arithmetic throughput.
4. An adversarial worst-case input (Swinnerton-Dyer: irreducible over ℤ, splits
   into many factors mod every prime) for an honest worst-case head-to-head; the
   corpus here is split products plus Φ₁₅, the easy case for recombination.

## Artifacts (unproven prototypes; isolated under `HexBench/`)

- `HexBench/ClassicalSpike.lean` — classical BZ prototype + benchmarks.
- `HexBench/ArithFloor.lean` — polynomial-arithmetic floor microbench.
- `lean_exe hex_classical_spike`, `lean_exe hex_arith_floor` in `lakefile.lean`.
