# Fixed finite-field F4 performance corpus

This corpus fixes inputs and a comparison protocol before measurements or tuning against it. It contains no timing result and establishes no performance milestone. The primary route is ordinary prime-field polynomial rings with grevlex order and complete monic reduced output. No characteristic-two field equations are added.

## Inputs

The primary corpus contains 90 systems: ten equally weighted families, three cases per family in each of F₂, F₃₂₀₀₃ and F₂₁₄₇₄₈₃₆₄₇. Published hard systems include Cyclic-9/10, Katsura-14/15 and Eco-14/15. Public cases overlap existing development inputs at the smaller sizes; they are not described as held out.

| Family | Cases per field | Systems across fields |
|---|---|---:|
| cyclic | cyclic7, cyclic9, cyclic10 | 9 |
| dense-quadratic | dense-quadratic6, dense-quadratic8, dense-quadratic10 | 9 |
| eco | eco11, eco14, eco15 | 9 |
| kat | kat8, kat14, kat15 | 9 |
| minrank | minrank_d_2_p_2_q_4_r_2, minrank_d_2_p_2_q_6_r_2, minrank_d_2_p_2_q_7_r_2 | 9 |
| noon | noon5, noon6, noon7 | 9 |
| positive-dimensional | positive-dimensional6, positive-dimensional8, positive-dimensional10 | 9 |
| reimer | reimer6, reimer7, reimer8 | 9 |
| sparse-structured | KLYZ12, KLYZ13, KLYZ22 | 9 |
| triangular | triangular6, triangular8, triangular10 | 9 |

Nine additional triangular systems use lex order and are reported separately for comparators that support that exact order. Twenty-seven additional dense-quadratic, sparse structured and positive-dimensional systems are held out: their sizes and seeds are fixed, but they must not select implementation policies or thresholds. Positive-dimensional systems leave two free variables by successive polynomial substitution.

Public examples and their GPL-3.0 license are retained from [GamBa `f18c2db3a288f20f63f752b44e0171cf1cb86163`](https://github.com/gblanco92/gamba/tree/f18c2db3a288f20f63f752b44e0171cf1cb86163/examples). GamBa’s `-2` filename suffix denotes the two-bit prime 3. F₂ cases instead use explicit integer coefficients from characteristic-zero examples where available, or written integer lifts of the 32003 examples. Cross-characteristic lifts define new systems; they do not claim a field homomorphism. Every case records its actual source characteristic, path, hash, variable precedence, target field and order. Generated inputs record their exact seeds and generator.

## Measurement protocol

Each process has 300 seconds of wall time, 8 GiB of address space and 256 MiB per output file. Use two initial adjacent pairs in trial-major order, alternating AB/BA. Lease a CPU for single-thread runs and retain every completed sample, outlier, failure, timeout, memory observation and host-activity record. One unchanged repeat is permitted after inconclusive results. Never wait for a quiet core or discard a completed sample.

The Hex batch size is fixed at 64. Internal work and storage counters have explicit 2⁵⁰ ceilings instead of the smaller development-sweep defaults. The common wall-time and address-space limits apply in addition. The variable cap is 1,000,000. Record any internal exhaustion separately from process timeouts, allocation failures and invalid inputs.

A collector killed before writing RSS leaves that observation unknown. For an interrupted campaign, retain the original fragment and continue with `--start-index` in the fixed process schedule. A fragment reports missing processes and cannot establish full coverage. Join fragments only with identical inputs, policies and executable hashes, retain each original source/CPU record, and reject duplicate schedule positions. Censored failures remain failures and receive no invented elapsed time or memory observation.

Measure candidate production through complete reduced output with parsing, setup and launch included consistently. Match coefficient field, variable precedence, order, deterministic guarantees and output. Record exact source revisions, licenses, compiler/runtime versions, flags, ISA availability, thread environment and executable hashes. Single-thread and equal-thread 2/4/8-thread results are separate; the corpus does not assert that Hex currently implements parallel elimination. Unsupported routes remain explicit.

For each comparator, take the geometric mean of jointly solved Hex/comparator ratios within each family across fields, then the geometric mean with equal family weights. Also report field-width strata, per-instance and per-family losses, solved counts, cactus data and peak RSS. Missing families, timeouts and coverage losses remain visible: jointly solved ratios cannot establish leadership if Hex loses solved coverage under matched resource limits.

Candidate production yields unchecked candidates. Compare every coefficient and exponent of complete bases outside candidate timing. Certificate generation, independent native verification, kernel checking and complete checked calls need separate results. Minimum comparator coverage is msolve, Groebner.jl, Giac and Singular, supplemented by faster fully open-source engines. GamBa, Magma and FGb remain additional targets where usable. No CI timing supports a scientific performance claim.

## Replay

Corpus capsule `f4-fixed-corpus-v1.tar.xz`: SHA-256 `1884d16bf293f053c6b22c943136cb6181f7bc3b081a1ba24aa24f93f3b93256`. All inputs, original public examples, license and generator have individual SHA-256 bindings. The generator requires the pinned public checkout and SymPy 1.14.0. Reproduction uses:

```bash
python3 scripts/bench/groebner_corpus.py --gamba /path/to/pinned/gamba --output /new/corpus
python3 scripts/bench/groebner_corpus_report.py \
  --archive reports/bench-results/raw/f4-fixed-corpus-v1.tar.xz \
  --report reports/bench-results/hexgroebner-corpus.md --check
```

Add `--current` to bind replay to the archived generator. Field-boundary, characteristic-two, canonicalization, seeded-support and positive-dimension checks run with `python3 -m unittest scripts.bench.test_groebner_corpus`.

[Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
