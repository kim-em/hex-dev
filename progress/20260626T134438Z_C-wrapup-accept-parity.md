# C investigation wrap-up: accept within-10x parity, banked

## Decision
Kim chose: accept ~6-9x-of-Isabelle parity for now. Bank the architecture win and
the prototype; defer beating Isabelle outright (it requires deep, proof-sensitive
core-arithmetic optimization with diminishing returns).

## Delivered (committed f1efa772, perf-investigation only; soundness changes on
this branch left untouched)
- reports/bz-classical-spike-findings.md — honest same-hardware head-to-head,
  methodology, bottleneck analysis, deferred-work levers.
- Banner pointer added atop reports/hex-berlekamp-zassenhaus-performance.md
  (legacy ratio ladders superseded).
- HexBench/ClassicalSpike.lean (lean_exe hex_classical_spike) — unproven classical
  BZ prototype: smart recombination + balanced/sequential lift + low-precision.
- HexBench/ArithFloor.lean (lean_exe hex_arith_floor) — arithmetic floor microbench.
- Two lean_exe entries in lakefile.lean.

## Headline numbers (in-process compute vs cached Isabelle wrapper)
- Isabelle: 419 us (deg8) -> 3.47 ms (deg24).
- Classical prototype best (balanced + k=4): 1.66 ms (deg8) -> 31.9 ms (deg24);
  ~6.4x (deg16) / 9.2x (deg24) of Isabelle.
- Old BHKS public factor: exponential on many-factor splits (3.3 s deg11, cap by
  deg15); factorFast ~130 ms deg24.

## If resumed (priority order)
1. choosePrimeData?/Berlekamp (dominant at low precision, ~8 ms deg16).
2. Incremental-precision lift with Mignotte backstop (folds in ~2.6x + balanced).
3. FpPoly/DensePoly per-op throughput.
4. Add Swinnerton-Dyer adversarial input for an honest worst-case head-to-head.

## Notes / open
- Prototypes are UNPROVEN and isolated under HexBench/; the library factor is
  unchanged. Integration + reproving is the deferred "beat Isabelle" work.
- The separate, pre-existing exponential-fallback bug in public `factor` (low cap
  -> CLD miss -> 2^n) remains; the surgical fix (use full BHKS cap) is documented
  in the findings report but not applied.
- This commit sits on feat/factor-soundness-coreLiftData-swap; consider moving to
  its own branch to keep PR scope clean.

## Blockers
None.
