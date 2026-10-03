# Bounded native ECPP at 512 bits

This experiment is the computational evidence for #10636. The default 256-bit
policy is preserved. The explicit public 512-bit policy has four successes in
eight independently generated held-out primes, each with genuine elliptic steps;
full current Pocklington construction including its registered ECM retry exhausts
on all eight. Exhaustion is not a compositeness verdict or a completeness claim.

## Corpus and allocation contract

[corpus-v1.json](corpus-v1.json) freezes eight tuning primes, eight holdout primes
and sixteen controls. Candidate strings are SHA-512 hashes of
`hex-native-ecpp-10636/v1/{split}/{stratum}/{index}/{counter}`, with the top bit
set. PARI/GP 2.17.3 independently checks the candidates, retaining all rejected
candidates. Each split has six ordinary primes and two primes with at most two
splitting discriminants in the original nine-entry portfolio. The generator is
`scripts/bench/ecpp_native512_corpus.py`; the corpus SHA-256 is
`f637736faaa474ef32ab61b9a146f52c3d6c83e96b730dbef0dc14f87669bce2`.

[allocations-v1.json](allocations-v1.json) preceded tuning. The finite expanded
portfolio and all v2 allocations are in [allocations-v2.json](allocations-v2.json).
[search-freeze-v2.json](search-freeze-v2.json), committed before holdout execution,
records the producer, arithmetic, allocation, corpus, toolchain and executable
hashes. The held-out subjects did not guide producer or allocation tuning.

The additional portfolio contains 33 fixed monic linear or quadratic class
polynomials for negative discriminants of absolute value at most 500 and class
number at most two, excluding the original nine. Data comes from PARI 2.17.3
`polclass(-d,0)`, source archive SHA-256
`8d9c4fcd584c468d27e0f23c36836587284452094c4b1c404c20c4b810462dcb`.
The independent oracle reconstructs every polynomial from primitive reduced
forms and analytic j-values at 160 and 240 decimal digits (mpmath 1.3.0), and
checks the compiled root fixtures. Runtime roots use the quadratic formula,
checked square roots and Horner verification, without general polynomial search.

Public search permits 512 bits, depth 21, 20 elliptic rows, 32 total nodes,
8192 candidates, 32768 roots, 16384 nonresidues and points, 131072 factor-work
units, 8 million scalar-work units, 8 million output data bits and 128 memo
entries. Terminal construction has 512 bits, depth 8 and 64 attempts; order
factorization retains four attempts. Polynomial work is charged before each
call, with 1048576 per-call and 16777216 shared limits. No allocation refunds
occur during backtracking. Exact package values and schedules are machine-readable
in the allocation artifact.

## Diagnosis and tuning

[diagnosis-baseline-v1.json](diagnosis-baseline-v1.json) changes only the baseline
subject ceiling to 512 while retaining the original nine discriminants and
256-bit terminal policy. All eight tuning cases exhaust: four at portfolio and
four at the 2-million-bit output ceiling. The stage-instrumented run in
[diagnosis-stages-v1.json](diagnosis-stages-v1.json) agrees exactly with every
original verdict, counter and random state. Norm coverage, eligible order factors,
recursive child failures, terminal calls and output rejects are separately visible.
The output failures exceed the actual data ceiling, rather than a traversal limit.

The initial allocation extension succeeds on three tuning subjects. The final
finite portfolio succeeds on five. Every distinct accepted certificate, including
longer core-only variants that exceed public row limits, is independently checked
and kernel-replayed in the tuning validation artifacts. Public search backtracks
from certificates that exceed replay row or node limits; memo reuse observes the
remaining limits. All failed outcomes and resource charges are retained.

## Holdout results

[comparison-holdout-v2.json](comparison-holdout-v2.json) retains two trial-major
adjacent native/construction comparisons, alternating NC/CN order with trial and
case index. The table shows trial zero; rows/terminal nodes/total nodes are
separate counts. Construction has 1024 total attempts, its full smooth-factor
profile, and ECM at 64 curves with B1=32768 and B2=524288 on remaining attempts.
Its deterministic seed is the subject, matching ordinary elaborator construction.

| Subject | Native seed | Outcome | Rows / terminal / total | Search ms | Full construction attempts (exhausted) |
|---|---:|---|---|---:|---:|
| ordinary-0 | 0 | success | 20 / 10 / 31 | 1543.78 | 180 |
| ordinary-1 | 1 | portfolio | — | 66.47 | 179 |
| ordinary-2 | 2 | portfolio | — | 145.03 | 196 |
| ordinary-3 | 3 | success | 19 / 8 / 28 | 2015.23 | 156 |
| ordinary-4 | 4 | portfolio | — | 136.33 | 1024 |
| ordinary-5 | 5 | success | 17 / 14 / 32 | 1353.57 | 1024 |
| difficult-0 | 6 | success | 17 / 7 / 25 | 904.60 | 156 |
| difficult-1 | 7 | candidates | — | 22897.59 | 156 |

[holdout-v2-validation.json](holdout-v2-validation.json) checks every distinct
successful certificate independently: modular inverse transcripts, curve points,
scalar multiplication, strict integer bounds, PARI elliptic arithmetic, and
primality of every child and terminal subject. Fresh Lean modules kernel-check the
same complete constructor data without native search. The current elaborator,
including extension discovery and ECM participation, separately confirms all four
gains in [elaborator-construction-v2.json](elaborator-construction-v2.json).

## Measurements and regression

[public-acceptance-v2.json](public-acceptance-v2.json) confirms that every public
export contains exactly the frozen search rows, binding endpoint acceptance to
the predeclared holdout results.

Every completed sample is retained with CPU selection, host context and raw output.
Host activity is context, not a filtering criterion. No quiet-core preflight or
retry-until-clean schedule is used. Construction comparisons measure capability;
they are not same-result verification latency ratios.

[endpoints-v2.json](endpoints-v2.json) measures fixed production, frozen conversion
and checking on holdout ordinary-0 in five repetitions. Median times are
1560.326 ms, 142.405 ms and 28.417 ms respectively, within predeclared distinct
5 s, 300 ms and 80 ms operation budgets. Output rendering is separately recorded
in the whole-corpus driver; it is not certificate checking.
[profile-v2-profile-native-production-512.json](profile-v2-profile-native-production-512.json)
retains a representative Phase-4 attribution: 7820 samples, 96.92% classified,
56.74% GMP, 32.23% allocation, 6.79% Lean runtime and 1.16% Lean own code.

[regression-v2.json](regression-v2.json) has four trial-major adjacent AB/BA
comparisons on all 32 existing 128/256-bit subjects. Every verdict, certificate,
original resource counter and random state agrees. Median paired search ratios
are 1.002 at 128 bits and 0.999 at 256 bits. All 256 timing samples are retained;
identical non-timing payloads are stored once and addressed by hash.
[split-v2.json](split-v2.json) records a fresh generated Mathlib-free client,
verbatim README quickstart and compiled 512-bit producer probe using exact staged
prerequisites and the real publication source transformations.


[proof-phases-timed-v2.json](proof-phases-timed-v2.json) retains four fixed
trial-major fresh-module schedules on the complete ordinary-0 certificate.
Reification plus expression type inference is timed inside the meta operation
(median 44.150 ms); replay preflight, including a
separate reification, is median 45.961 ms. Fresh kernel
proof-module wall time is 17.619 s, with a matched import/
numeral baseline of 3.820 s. These wall times include
Lake/import/module overhead and are not a pure kernel reduction estimate.
The earlier uninstrumented schedule in [proof-phases-v2.json](proof-phases-v2.json)
is also retained.

## Public generation and replay

Public endpoint evidence is retained in `public-*-v2.json`. Generation kernel-checks
the exact frozen representation before suggesting or exporting it. Each successful
endpoint builds fresh Nat.Prime and Hex.Nat.Prime suggestions, an exported module,
and verbatim frozen replay with native generation absent and GP blocked. The
unchanged replay limits include 131072 inspected syntax nodes and 1024 inverse
witnesses per step.

[public-ordinary-0-v2.json](public-ordinary-0-v2.json) retains the initial public
failure: frontend OfNat wrappers exceeded the syntax-node limit. The reifier now
uses raw natural literals for ECPP fields and inverse witnesses, preserving their
values and the inspection ceiling. This representation correction does not change
the frozen producer or allocation. [public-default-regression-v2.json](public-default-regression-v2.json) retains
the seed-only parser failure after adding the optional bit policy; an atomic
option prefix preserves the existing syntax. The corrected default endpoint is
[public-default-atomic-v2.json](public-default-atomic-v2.json). The corrected
ordinary-0 endpoint is
[public-ordinary-0-raw-v2.json](public-ordinary-0-raw-v2.json). The committed
`HexECPPMathlib.Tests.Native512` pins its exact suggestion with `#guard_msgs`;
`HexECPPMathlib.Tests.Frozen512` replays the same text without importing Native.

[public-final-ordinary-0-v2.json](public-final-ordinary-0-v2.json) rechecks the
final parser/reifier sources with their hashes. Fresh generation/export and
frozen-replay module wall times are retained for all four gains.

Reproduction uses `lake build`, then the scripts under `scripts/bench/` and
`scripts/ci/check_ecpp_native.py --bits 512 --subject N --seed S --output NEW.json`.
Use fresh output paths: the runners refuse to overwrite completed observations.
The companion's proof audits and generated release metadata remain owned by #10586;
this experiment adds computational and public endpoint evidence only.
