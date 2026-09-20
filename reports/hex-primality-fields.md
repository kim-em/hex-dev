# Standard field prime construction

`primality?` constructs P-521 with the existing p−1/rho portfolio after raising
the input ceiling to 521 bits and the candidate-factor cap to 32. The existing
4096-subset cap, 1024-attempt cap, depth 32, worklist fuel, witness schedule,
divisor-sieve cap, and factoring budgets are unchanged. This brings the fixed
corpus to **nine of twelve** constructed inputs. secp256k1, P-384, and Curve448
still exhaust; this report does not claim constructor support for them.

The follow-up [ECM stage-2 investigation](hex-primality-ecm-stage2.md) supplies
an explicitly selected downstream factor provider that constructs the remaining
three primes. Plain `primality?` retains the policy and coverage described here.

The change is confined to untrusted search policy. The checker, certificate
language, soundness theorems, ordinary `primality` policy, and HexIntFactor
portfolio are unchanged. No production tactic invokes an external factorizer.

## Reproduction and measurement boundaries

```sh
python3 scripts/bench/primality_field_sweep.py --diagnostics \
  --output /tmp/fields.json
lake build HexPrimality.Conformance hexprimality_bench
.lake/build/bin/hexprimality_bench verify
```

The committed record is
[`bench-results/hex-primality-fields-issue-10291.json`](bench-results/hex-primality-fields-issue-10291.json).
The separate [exploratory record](bench-results/hex-primality-fields-exploration-issue-10291.json)
retains the preliminary observations and offline factorization output; its
unpaired timings do not enter the table below.
The runner chooses a CPU automatically, pins every measured subprocess, and
runs two trial-major blocks with adjacent before/after arms in AB/BA order.
It retains every completed sample, host load, source hashes, executable hash,
commands, output, certificates, and generated proof sources. There is no
activity rejection or unchanged rerun. The before arm explicitly uses
`(maxBits, maxFactors, rhoSteps) = (512, 12, 32768)`; the after arm uses
`(521, 32, 32768)` in the same compiled implementation. The original record's `commit` identifies the checkout's baseline parent,
`cc2baf89e`; the measurements were collected with uncommitted source changes.
Its `source_sha256` fields identify the measured sources, which are preserved
in the initial implementation. The record also embeds the original sweep
driver verbatim, including its matching hash. Later driver
changes add cross-arm certificate assertions and the separate failure case;
they do not change the timed operations. Integration with the explicit-producer
API changes tactic dispatch in `Elab.lean`, while the timed construction and rendering operations remain unchanged.
These records do not measure the separate `primality? using` route. Kernel
samples precede the cube-root optimization in
[the replay attribution](hex-primality-replay-attribution.md), which supplies
its own before/after evidence. P-521's tree contains only square-root nodes,
so that optimization does not change its replay path; compiled checking also
retains its original arithmetic implementation. These two budget fields are
the entire production change, so this also controls compiler/build differences.

Native construction includes its final compiled self-check, but excludes
process startup, parsing, and certificate formatting. Compiled checker replay
is timed separately. Rendering and literal elaboration are timed together
inside Lean, after imports. Direct kernel replay expands all local proof
constants, drains pending asynchronous checks, and times a fresh kernel
checker against the complete goal. Invalid equality, changed-subject, and
zero-witness controls must be rejected before timing. Rendering and replay
measurements build through Lake and retain the exact source. Missing
certificates have no rendering/replay observation; exhaustion is not a
zero-cost proof. No asymptotic claim is drawn from these four named inputs.

## Deterministic failure paths

Every construction starts at `Rand.ofSeed n`, with the budgets recorded in
the command. The `trace` mode wraps the production `FactorSearch` callback;
it prints the exact predecessor, candidate factors, unresolved residual,
attempts, and remaining allowance at every recursive call. Trace I/O is
excluded from the paired construction measurements.

### secp256k1

For `n = 2^256 - 2^32 - 977`, table division gives

```
n - 1 = 2 * 3 * 7 * 13441 * q
q = 205115282021455665897114700593932402728804164701536103180137503955397371
q - 1 = 6040389990 * R
R = 33957291228054575644562761185877073266390894853717235429717263
```

The root's probable-prime cofactor `q` enters the candidate list without any
factor attempts. Every sufficient root subset includes it. Its predecessor
exposes only `2 * 3 * 5 * 29^2 * 31 * 7723 = 6040389990`, a 33-bit product
for a 237-bit obligation. Even sieve bound 64 cannot meet the size condition.
The full p−1 ladder and two rho restarts leave `R` unresolved in 14 attempts.
The constructor tries 16 root subsets containing `q`, advancing rho's random
state each time, and exhausts in 272 total attempts. The overall attempt limit,
factor count, recursion depth, witness search, and rendering are not the first
barrier. Caching these failures as permanent impossibility would be incorrect:
the failed randomized streams differ between subsets.

The diagnostic split of `R` has factors
`132896956044521568488119` (77 bits) and
`255515944373312847190720520512484175977` (128 bits). The former's predecessor
contains `22149492674086928081353`; the latter's predecessor contains both
`7240687` and `107590001`, beyond the stage-1 cap of 524288. The measured bases
find neither factor. The bounded rho increase and ECM stage-1 probes below do
not remove this barrier.

### P-384

For `n = 2^384 - 2^128 - 2^96 + 2^32 - 1`, the first barrier is root factoring:

```
n - 1 = 2546 * R
2546 = 2 * 19 * 67
R = 15476043282165938418020047172090971643786229092877237497230280205909552934602070042830819359096205028225297318583
```

The 12-bit known product is insufficient, and search exhausts in 14 attempts.
This is neither an MR rejection nor a subset/witness failure. ECM stage 1 at
sigma 6, bound 4096, validates and returns `807145746439`; its predecessor has
the factor `2862218959`, outside the p−1 cap. This demonstrates a useful ECM
step, but does **not** establish P-384 construction support.

The remaining 334-bit factor is
`q = 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097`.
Direct Hex construction for `q` passes screening and finds

```
q - 1 = (2^4 * 11^3 * 8389 * 38557 * 312289) * S
S = 8913326561311260411185427017705935207065736969962576881302563771106887371009673983
```

It exhausts in 19 attempts with only a 61-bit known product. Diagnostic
factors of `S` are `1357291859799823621` (61 bits),
`529709925838459440593` (69 bits), and
`12397338596863679689524759770405177749801411` (134 bits). The stronger rho
and stage-1 ECM probes do not complete this recursive obligation. Merely
wiring the demonstrated root ECM call into the tactic would therefore add
cost and dependencies without reaching this named target.

### Curve448

For `n = 2^448 - 2^224 - 1`, the production search finds

```
F = 2 * 641 * 18287 * 196687 * 1466449 * 2916841 * 6700417
n - 1 = F * R
R = 5499843854549273892319703537820711808983983221387696175495353456336512485964978717225063928271651228087
```

`F` is only 107 bits for a 448-bit root. No candidate subset meets the size
condition, even with the allowed divisor sieve. Search stops after 67 factor
attempts, before child certification, witness search, or rendering. The
remaining diagnostic factors are 71, 78, 79, and 115 bits:

```
1469495262398780123809
167773885276849215533569
596242599987116128415063
37414057161322375957408148834323969
```

The existing supplied fixture uses the first two, along with 2 and 641. Their
product would suffice; the missing step is discovering them. The first has
`3402277943` in its predecessor and the second has `97859369123353`, explaining
why increasing stage-1 bounds within the existing cap does not address their
full predecessor smoothness. The existing fixture continues to establish
representability and replay, independently of constructor coverage.

### P-521

For `n = 2^521 - 1`, the original policy rejects the input before screening.
Raising only the bit ceiling still exhausts: the cheap table path has 17
candidates, and full factor search yields 25, both beyond the old 12-factor
cap. The callback consumes 94 attempts and retains unresolved residual
`1647519855571282873631511502892048832068481089740271`.

With the 32-factor cap, the existing truncated subset enumeration includes
the full mask. Its product exceeds the square-root threshold; the unresolved
residual is not needed. Eight non-table children have sufficient table-factored
predecessors, and all witnesses are among the configured small bases. Hex
constructs and checks a Pocklington tree of nine non-leaf nodes and 39 factor
entries in 170 attempts. No recursive factoring improvement, extra rho work,
new witness budget, or factor supplied from outside Hex is needed.

The exact `#guard_msgs` example in `ConstructionConformance.lean` pins the
complete `Try this:` certificate. The expression `2 ^ 521 - 1` requires local
`maxRecDepth = 1024` and `exponentiation.threshold = 521` to normalize Lean's
original goal. The numeral and literal replay succeed with default options.
A separate 522-bit guard pins the next unsupported input size. The native fixed
benchmarks `runP521Construction` and `runP521Checker` check expected hashes for
170 attempts and successful replay, respectively; their five-second caps are
operational safeguards, not scientific latency guarantees.

## Portfolio decision

The diagnostic factorizations were obtained offline with PARI 2.17.3 and
are included as explicit inputs in the runner. Its `validate` mode checks
range, divisibility, and exact reconstruction inside Hex before using them
as diagnostic evidence. Their asserted primality is never used for acceptance;
all actual construction successes recursively certify their chosen children
and pass the existing public checker.

The default p−1 ladder already visits both bases at every declared bound,
including the primitive's 524288 cap. The paired rho diagnostic compares
32768 and 262144 steps per restart on the recursive secp256k1 and P-384
obligations. Both arms exhaust. ECM compares eight deterministic Suyama
parameters 6 through 13 at bounds 4096 and 32768, stopping at a proper factor.
Only P-384's root residual splits; its recursive residual and the secp256k1
and Curve448 residuals do not. Every completed call, including failures, is
retained. These finite observations do not prove that every other seed or
larger stage-1 allocation fails.

The accepted change removes the two demonstrated P-521 policy barriers.
There is no measured rationale here to raise the factoring budgets, increase
the divisor-sieve cap, or move ECM into the primality dependency graph. For
the remaining obligations, a concrete next factoring method is **ECM stage 2**:
it admits a large prime in the curve order beyond the stage-1 smooth bound,
which the current implementation cannot use. A measured two-stage ECM
portfolio would still require enough curves for these 61–79-bit smaller
factors; support is not guaranteed by adding the method alone. **ECPP** is a
separate certification alternative that avoids dependence on factoring these
particular predecessors and would require a new, sound certificate checker.
Neither method is implemented or claimed by this change. The issue's design
decision is to leave these three targets honestly exhausted rather than
inflate the current budgets speculatively.

## Paired performance results

The table below reports means of the two retained samples per arm (also their
two-sample medians), rounded to three significant figures.
Construction and replay remain separate observations; the former already
includes one compiled self-check. Exact samples and source sizes are in the
linked JSON record. The eight previously constructed certificates are
identical across policy arms.

| Input | Search before (ms) | Search after (ms) | Render/elab before → after (ms) | Kernel replay before → after (ms) |
|---|---:|---:|---:|---:|
| family-31 | 0.182 | 0.179 | 2.36 → 2.14 | 0.796 → 0.805 |
| family-61 | 0.205 | 0.207 | 1.8 → 1.55 | 0.692 → 0.813 |
| family-123 | 0.93 | 0.934 | 1.79 → 1.72 | 1.44 → 1.13 |
| family-256 | 2.27 | 2.32 | 1.83 → 1.89 | 2.12 → 2.1 |
| family-511 | 5.44 | 5.43 | 2.01 → 1.92 | 4.6 → 4.18 |
| family-512 | 15.7 | 16.5 | 2.67 → 2.77 | 4.36 → 5.02 |
| Curve25519 | 582 | 592 | 7.04 → 6.43 | 13.1 → 8.68 |
| secp256k1 | 1.51e+04 (exhausted) | 1.53e+04 (exhausted) | — → — | — → — |
| P-256 | 23.8 | 22.5 | 7.36 → 6.17 | 20.5 → 19.1 |
| P-384 | 1.11e+03 (exhausted) | 1.12e+03 (exhausted) | — → — | — → — |
| Curve448 | 1.7e+03 (exhausted) | 1.34e+03 (exhausted) | — → — | — → — |
| P-521 | bit rejection | 1.47e+03 | — → 13.9 | — → 53.6 |

P-521 construction takes 1.57 / 1.38 s; compiled checker replay
takes 12.5 / 11.5 ms, rendering/elaboration 14.4 / 13.3 ms, and
direct kernel replay 58.0 / 49.2 ms. These samples justify admitting the
input with the unchanged factoring budgets. The run used `chungus2`, CPU 4,
Lean 4.34.0. The substantial between-block shifts on unchanged certificates
show why these are host observations, not precise speedup estimates. In
particular, the Curve448 timing difference is not an algorithm improvement.
There is no before-policy P-521 certificate to replay.

The extra ECM root split for P-384 takes 20.5 / 20.2 ms at bound 4096,
versus 173 / 163 ms at 32768, returning the same factor. Higher
stage-1 work supplies no further coverage in this diagnostic. Eight failed
curves at 32768 take about 1.2–1.4 seconds per residual. The report therefore
keeps the default factoring budgets and downstream ECM placement.

## Truncated-enumeration failure cost

The separate fixed failure probe is a 507-bit screen-passing input whose
predecessor has 18 table factors, the primes from 2 through 61, with product
`117288381359406970983270`. Its remaining cofactor is a product of two
216-bit factors; Hex validates the complete predecessor reconstruction in
the record. Neither p−1 nor rho splits the residual, and the known product is
insufficient. Both arms exhaust after 14 attempts. The old cap rejects both
18-factor candidate lists; the new cap scans 4096 masks on each list without
finding a sufficient subset.

The two adjacent AB/BA blocks retain before times **878 / 867 ms** and after
times **895 / 881 ms** (means **872 / 888 ms**). This records the additional
cost of a failing truncated scan; it is not a worst-case wallclock bound for
all possible inputs. The SPEC states the independent enumeration limits:
up to two passes per node, at most 4096 masks per pass, 32 bounded product
multiplications and 63 divisor checks per mask, plus bounded child-cost
estimates. This work is finite but outside the semantic attempt counter.
No extra attempt budget or failure cache is introduced.

The exact input, factor validation, trace, commands, hashes, and every sample
are in [the failure record](bench-results/hex-primality-field-failure-issue-10291.json),
measured from pre-rebase source commit `88b1c74ee` (published as `93a5a3a2a`
after rebasing; all measured source hashes are unchanged). Reproduce with:

```sh
python3 scripts/bench/primality_field_sweep.py --failure-only \
  --output /tmp/field-failure.json
```

The registered five-repeat mode-3 results for construction, checker replay,
and the policy sieve endpoint are also included in the
[headline performance report](hex-primality-performance.md), with their
budgets, observed hashes, and raw lean-bench export.
