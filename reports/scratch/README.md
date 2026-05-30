# Scratch evidence for the BZ-vs-Isabelle investigation

Evidence artefacts supporting `../bz-vs-isabelle-investigation.md`.
None of these compile or run as part of the project build; they live
here for reproducibility of the post-mortem rather than as durable
project surfaces.

To exercise any of the Lean files, add the corresponding
`lean_exe scratch_<name>` stanza to `lakefile.lean` temporarily, then
revert after running.

## Lean diagnostics (executable on demand)

- `BZBench.lean` — times `Hex.factor` on the split-linear product
  ladder `(x-1)(x-2)…(x-n)` for `n ∈ [2, 24]`. Forces evaluation via
  a coefficient-hash checksum so DCE doesn't elide the call.
- `FactorDemo.lean` — runs `Hex.factor` on a small fixture set and
  prints results, used to confirm the wrong-output bug on
  `(x-1)…(x-5)` first.
- `FactorTrace.lean` — per-input trace of `factorFast` vs `factor`
  (combinator), `choosePrime` vs `choosePrimeData`, the precision
  cap, and the per-call wall time. Source of the
  "factor takes 6s, returns 3 reducible factors" data point at
  degree 24.
- `PrimeProbe.lean` — direct `@Hex.isGoodPrime f p _` probe for every
  prime in `smallPrimeCandidates`, across the same input ladder.
  Confirms every candidate is rejected for the wrong-output cases.
- `GcdProbe.lean` — single-case demonstration of the root cause:
  `DensePoly.gcd (f mod 13) (f' mod 13) = [4]` for
  `f = (x-1)…(x-11)`, a unit in F₁₃ but not equal to the literal
  polynomial `1`, so `gcd == 1` fails.
- `GcdMatrix.lean` — same probe broadened to `n × p` matrix.
- `LLLBench.lean`, `LLLBenchTiny.lean` — `Hex.lllUnchecked` timing
  on the random-bounded LLL ladder; produces the basis stream that
  the fpylll and Isabelle/AFP comparators consume.

## Python comparators (used by the plots)

- `bz_flint_times.py` — re-runs each BZ Lean fixture through
  `python-flint`'s `fmpz_poly.factor()`. Produces
  `/tmp/bz-merged.jsonl`.
- `lll_fpylll_times.py` — re-runs each LLL Lean basis through
  `fpylll.LLL.reduction`. Produces `/tmp/lll-merged.jsonl`.
- `lll_isabelle_times.py` — pipes each LLL Lean basis through the
  AFP-extracted `svp_verified` binary (set up by
  `scripts/oracle/setup_lll_isabelle.sh`) with adaptive subprocess-
  startup overhead amortisation. Produces
  `/tmp/lll-isabelle-times.jsonl`.

## Plots

- `plot_bz.py` — hex vs FLINT BZ ladder (log-y).
- `plot_bz_isa.py` — hex vs Isabelle/AFP BZ ladder (log-y); the
  headline plot of the investigation.
- `plot_lll.py` — hex vs fpylll LLL.
- `plot_lll_triple.py` — hex vs Isabelle vs fpylll LLL.
