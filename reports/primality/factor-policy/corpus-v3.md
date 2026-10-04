# Interleaved factor search on independent prime subjects

The `interleaved` experimental policy restores the longer Pollard p−1 searches
that the `balanced` policy omitted. For composite residuals of at most 192 bits,
it tries bounds 262144 and 524288 before ECM. For larger residuals, it tries
eight random ECM curves first, then those p−1 bounds, then the remaining 42
curves of the first round, the existing fixed-parameter round, and the larger
random round. The two parts of the first ECM round share their prepared tables.
All work consumes the same 1024-attempt construction allowance. No production
policy or public tactic changes.

Curve25519 explains why the larger p−1 bounds matter: proving its primality
requires a recursive prime whose predecessor has factor 31757755568855353.
That factor's predecessor is
`2^3 * 3 * 31 * 107 * 223 * 4153 * 430751`. The existing stage-1 bound 524288
finds it; the shortened ladder ending at 32768 does not. The interleaved policy
finds the same frozen certificate without ECM. CI checks the exact certificate,
its attempt accounting, and factor reconstruction under small resource limits.
ECM's expensive schedules already allocate lazily in the shared implementation;
creating a prepared handle does not enumerate primes.

## Corpus and comparison protocol

`corpus-v3.json` contains 400 independently generated prime subjects: 100 each
at 128, 256, 384 and 512 bits. The first 25 indices of each size are tuning
subjects; the other 75 are validation subjects. SHAKE256 of a fixed domain,
size, index and rejection counter determines each odd candidate. Selection
uses rejection sampling rather than rounding to the next prime. PARI 2.17.3's
unconditional `isprime` verifies every accepted subject. The file includes the
complete generator source and PARI version. Hash-derived candidates are
reproducible; no ideal randomness claim is made.

Generation supplies no predecessor factors, witnesses or certificates. No
factor-search policy runs while choosing subjects. The corpus is frozen before
measurement. The candidate's source and executable are frozen before validation;
validation outcomes do not select bounds or schedules for this version.

The offline runner accepts `--corpus` and `--split`. Every subject receives the
same 180-second process limit. Profiles run adjacent on one automatically leased
CPU; order reverses across subjects and across timing trials. Executables are
copied and hash-checked before each native sample. Completed samples, exhaustion,
errors and timeouts all remain in the report. Host activity is recorded context.
The four-block standard-field comparison supplies repeated paired timings;
the one-trial random-prime sweep measures bounded coverage. Generation excludes
Lean elaboration and kernel replay. PrimeCert generation includes its ordinary
Python/SymPy startup and uses the unmodified pinned upstream generator.

The replay script links every positive sample to its exact generated term.
Hex literals become probes under
`bench/HexPrimalityMathlib/ProofProbe/FactorCorpus/`, built by the existing
`HexPrimalityMathlibProofProbe` CI target. PrimeCert terms are built separately
against their pinned upstream environment. Both routes guard their theorem
axioms to `propext`, `Classical.choice` and `Quot.sound`.

Reproduce corpus generation with:

```sh
python3 scripts/bench/primality_factor_corpus.py --gp /path/to/gp --output /tmp/corpus.json
```

Reproduce a validation sweep with:

```sh
python3 scripts/bench/primality_factor_experiment.py \
  --corpus reports/primality/factor-policy/corpus-v3.json --split validation \
  --mode construct --profiles baseline interleaved primecert \
  --primecert /path/to/pinned/PrimeCert --jobs 16 --output /tmp/validation.json
```

## Complementary upstream cases

[PrimeCert's example certificates](https://github.com/b-mehta/PrimeCert/blob/0803c2f6bd289c09704c7d352bb8fcf770cbb9b2/PrimeCertTest/PrimeListTest.lean)
provide named examples and intermediate recursive primes.
[Math::Prime::Util's proof tests](https://github.com/danaj/Math-Prime-Util-GMP/blob/master/t/16-provableprime.t)
exercise several proving methods, but explicitly filter some subjects to remove
slow cases; they are unsuitable as the sole performance sample.
[FLINT's ECPP tests](https://github.com/flintlib/flint/blob/main/src/ecpp/test/t-prove.c)
provide a random-prime and corrupted-certificate testing pattern.
[Feitsma–Galway's pseudoprime tables](https://www.cecm.sfu.ca/Pseudoprimes/)
provide composite rejection controls, not successful-proof benchmarks.

The earlier corpus's discriminant-based “difficult” stratum describes ECPP
search, not Pocklington factorization difficulty.
