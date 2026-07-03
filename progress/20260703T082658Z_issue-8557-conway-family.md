# Issue #8557: Conway polynomials (Lübeck) as a factorization cactus family

Added lifted Conway polynomials from Frank Lübeck's tables as a new
`conway` family in the cross-system factorization sweep and cactus plots,
plus a monotonic early-termination feature for the sweep harness.

## Accomplished

- **Cache**: rewrote `scripts/oracle/update_luebeck_conway_cache.py` to
  fetch a per-prime slice (`SLICE`: small primes 2/3/5/7 to degree 40 for
  the degree axis; high primes 11/13/97/521/65537 to degree ≤8 for the
  height axis), tolerating Lübeck's table gaps. Regenerated
  `luebeck_conway_cache.json` to 186 entries, keeping the CI core
  (p∈{2,3,5,7,11,13}, n≤6) intact — the conformance oracle passes both
  legs (72 comparisons, 0 failures).
- **Corpus**: added `family_conway()` to `scripts/bench/gen_factor_corpus.py`,
  lifting the ascending 𝔽_p coefficients (representatives `0..p-1`) verbatim
  to monic integer polynomials with `expectedFactorDegrees = [n]`.
  Regenerated `hexbz-factor-corpus.jsonl` to 391 instances (186 conway);
  `--check` is byte-identical.
- **Premise confirmed**: FLINT and PARI both factor all 186 lifts as a
  single degree-`n` factor, agreeing with each other and the `[n]` labels
  (zero mismatches). "monic + irreducible mod p ⇒ irreducible over ℤ"
  holds on every entry.
- **Sweep**: ran the full 9-system carica sweep (hex ×4, FLINT, NTL, PARI,
  Isabelle BZ + LLL) at 10s over the new corpus, full-fidelity
  (`--no-early-terminate`). Committed
  `hexbz-factor-sweep-bc958d84-carica.json`; removed the stale
  `cc203779` record (old corpus SHA can't merge). **Cross-check passed:
  all nine systems agree on all 391 instances.**
- **Finding**: production `hex-factor`/`hex-lattice`/`hex-classical`,
  FLINT/NTL/PARI, and verified `isabelle-bz` each solve all 186 conway
  (good prime choice ⇒ immediate irreducibility). `hex-fast` (82/186)
  and `isabelle-lll` (167/186) are where conway bites — the prime-
  selection probe the issue predicted. hex-fast's solves span every
  degree 1–40 (non-monotonic: times out on C_{2,12}, solves C_{2,16}).
- **Early termination** (Kim's request): `factor_sweep.py` now stops a
  system on a monotonic family after `--early-terminate-run` consecutive
  timeouts (default 3), recording the rest as `early_terminated`
  timeouts. Result-preserving for strictly monotonic families;
  conway is included under the consecutive-run threshold (rides over
  isolated prime-lucky solves). Validated: hex-fast/conway/2s caps
  exactly at the 3rd consecutive timeout, no solve mislabeled.
- **Charts + docs**: regenerated all 23 figures (now including PARI and
  the two new `hexbz-*-conway.svg`); updated `reports/hexbz-factor-sweep.md`
  (corpus, methodology, early-termination, conway family observations,
  recorded-sweep tables, artifact SHA).

## Current frontier

All change-list items done. Corpus deterministic, conformance green,
cross-check green, charts regenerated.

## Next step

Second opinion (Codex), then open the PR; check merge/CI.

## Blockers

None. Note the committed sweep record's env shows commit `bc958d84`
with a dirty tree (the run predates this branch's commit); the corpus
SHA is the reproducible pin.
