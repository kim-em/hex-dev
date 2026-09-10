# HexPrimalityMathlib performance

`HexPrimalityMathlib` is an executable proof/tactic bridge, not a
correspondence-only layer. `HexPrimality` owns the transported primality
computation. This report prices the bridge-owned `Nat.Prime` elaboration,
registration dispatch, certificate expression construction, transport theorem,
kernel replay, bounded negative path, and public tactic costs. There is no
Mathlib benchmark executable.

The headline verdict is that every supported bridge route passes the 10-second
absolute fresh-module gate through 512 bits. The measured `2^24` `norm_num`
boundary remains the policy: trial division handles at most 24 bits and the
bounded certificate extension handles 25 through 512 bits. Bare `primality`
and opted-in `norm_num` have indistinguishable large-input cost at this noise
resolution, so their choice is based on goal shape and opt-in semantics rather
than a performance ranking.

## Bench Targets

The bridge uses proof/tactic evidence in place of compiled targets. These
fresh-module probes explicitly replace a LeanBench executable, `list`/`verify`
entries, complexity verdicts, and timed-region sampling profiles. Its
build-only root is `HexPrimalityMathlibProofProbe`. Every module in the new
component matrix is a fresh importer of the same precompiled
`ProofProbe.Support` module and no measured module imports another measured
module; the inherited policy and negative modules import
`HexPrimalityMathlib` directly.

| evidence family | reference → candidate | what is included |
|---|---|---|
| `proof-track-components`, representative table-smooth 31-bit input | `Baseline → Input31`; `Input31 → Literal31`; `Literal31 → Reify31`; `Literal31 → Replay31`; `Baseline → Primality31` | import, numeral input, emitted literal, production reifier in its bridge emission context, bridge theorem plus kernel replay, and full bare tactic |
| `proof-track-components`, ceiling | `Baseline → Input512`; `Input512 → Literal512`; `Literal512 → Reify512`; `Literal512 → Replay512`; `Baseline → Primality512` | the same decomposition at the exact accepted 512-bit ceiling |
| `threshold-routes` | `Baseline → NormNumTrial`, `NormNumThreshold`, or `NormNum512` | full opted-in `norm_num` immediately below/above `2^24` and at 512 bits |
| `negative-boundedness` | `MathlibBaseline → Negative25`, `Negative32`, `Negative64`, `Negative65`, `Negative512`, `Negative512Odd`, or `NegativeExhausted512`; `Negative64Null → Negative64Null` is the elevated control | 25-, 32-, 64-, 65-, and 512-bit composites, parity and odd-factor ceiling inputs, and balanced exhaustion |
| `failure-policy` | `MathlibBaseline → MathlibExhausted/MathlibOverBudget` | bounded 512-bit exhaustion and rejection before search at 513 bits |

The `Reify*` candidates deliberately re-elaborate the fixed certificate syntax
before invoking the production `reifyPrimeCert` and checking definitional
equality. Their deltas are therefore inclusive upper estimates for reification,
not pure reifier micro-measurements. The `Replay*` rows use
`by decide +kernel` to force the same Boolean checker through the bridge theorem;
they are kernel-replay proxies rather than byte-identical replicas of the
production elaborator's emitted `Eq.refl true` witness.

Core certificate search is intentionally not timed a second time. Both public
bridge entry points call the core-owned `primeCertCountedWith?` with the same
seed, fuel, and `PrimeCertBudget`. Its Phase-4 performance owners are
`Hex.PrimalityBench.runCertSearch` and `runCertSearch512` in the core headline
report, together with the matched `search` rows in
`reports/bench-results/hex-primality-core-proof-issue-9762-chungus2.json`.
The shared policy-selection evidence for the seed, fuel, and budget is
`reports/bench-results/hex-primality-fuel-issue-9784-chungus2.json` (SHA-256
`0d772cb92479b0b8b8e0852491af42ec361bfb0cf02c729df79623001b8e7269`).
The bridge's earlier complete policy evidence remains in
`hex-primality-elaborator-policy-issue-9779-chungus2.json` (SHA-256
`7a6e169cdfc91b35d404c77b15271f6cfa8d8d8ad7f9e4bc7f54c627106a78a9`),
and bounded composite evidence remains in
`hex-primality-negative-policy-issue-9803-chungus2.json` (SHA-256
`87d9e2a2e958e197a5ee445183cd40254bde6dbeed3cef6985f3a65f022d2906`).

Build and structural reproduction:

```bash
lake build HexPrimalityMathlibProofProbe
python3 -m unittest scripts.bench.test_primality_mathlib_proof_sweep \
  scripts.bench.test_primality_negative_sweep \
  scripts.bench.test_primality_policy_sweeps
```

Release-quality rotated measurement:

```bash
python3 scripts/bench/primality_mathlib_proof_sweep.py --samples 6 \
  --shared-host --expected-host chungus2 --cpu 22 --timeout 30 \
  --warm-timeout 600 --max-pair-retries 32 \
  --output reports/bench-results/hex-primality-mathlib-proof-probes-issue-9765-chungus2.json
```

The runner invalidates exactly one measured module's generated artifacts,
builds it with `lake build +<module>:olean`, retains warm imports, rotates pair
order, alternates reference/candidate orientation, and retries the complete
adjacent pair after contamination.

## Verdicts

Times are seconds. Deltas are signed `candidate - reference` medians. An
unresolved component means its delta lies within the interpolated null
envelope; it is not evidence of zero cost. The release contract is the
candidate's absolute wall time, not an import-subtracted delta, and all rows
pass the 10-second gate.

| pair | median reference | median candidate | median delta | max candidate | null resolution | gate |
|---|---:|---:|---:|---:|---|---|
| `input-31` | 1.895087295 | 1.913741934 | -0.049873978 | 2.020672900 | unresolved | pass |
| `literal-31` | 1.864503917 | 1.896126381 | +0.092062274 | 2.780323094 | unresolved | pass |
| `reify-31` | 1.991211671 | 1.904612154 | -0.109137364 | 2.041918703 | unresolved | pass |
| `replay-31` | 1.880860687 | 3.683658824 | +1.917981649 | 4.639464443 | resolved | pass |
| `primality-31` | 1.824788561 | 3.301473551 | +1.637762758 | 4.326842194 | resolved | pass |
| `input-512` | 1.879161289 | 1.895341902 | +0.006233071 | 2.116918249 | unresolved | pass |
| `literal-512` | 1.930163440 | 1.923968104 | -0.013697760 | 3.074602822 | unresolved | pass |
| `reify-512` | 1.916927641 | 1.945788538 | +0.154555610 | 3.533526693 | unresolved | pass |
| `replay-512` | 2.028851401 | 3.389806566 | +1.603466181 | 4.142504522 | resolved | pass |
| `primality-512` | 1.768701229 | 3.776713829 | +1.791507295 | 4.525257842 | resolved | pass |
| `norm-num-trial` | 1.921612072 | 1.962851239 | +0.041239167 | 2.234748306 | unresolved | pass |
| `norm-num-threshold` | 1.859722118 | 3.620794963 | +1.744100140 | 4.229398244 | resolved | pass |
| `norm-num-512` | 1.868875642 | 3.420015923 | +1.561029150 | 4.539353512 | resolved | pass |

The resolved replay and full-tactic rows show that kernel checking, rather
than numeral or literal construction, is the visible bridge-local cost. The
production reifier's incremental deltas do not resolve above noise even at
512 bits. This is compatible with the emitted certificate being small while
`checkPrime` performs modular arithmetic during replay; no subtraction or
causal percentage is inferred from non-additive fresh-module pairs.

The independent negative record has candidate maxima of 3.137086 s at the
25-bit composite, 2.235051 s for the 32-bit strong pseudoprime, 2.285776 s at
64 bits, 2.422631 s at 65 bits, 2.131473 s for ceiling parity, 2.434728 s for
the ceiling odd factor, and 3.317787 s for balanced ceiling exhaustion. The
shared policy record gives a 3.026820 s maximum for accepted 512-bit
`Nat.Prime`, 1.627793 s for bounded exhaustion, and 1.528474 s for immediate
513-bit rejection. Its accepted row is the same public operation as the new
`primality-512` row measured in a separate run; the new component-matrix record
and its 4.525258 s maximum are the release contract for this report.
Unsupported, non-numeral, open, composite-bare-tactic, and unsolved opted-in
failure shapes are pinned by
`conformance/HexPrimalityMathlib/Conformance.lean` and
`conformance/HexPrimalityMathlibConformance/OptIn.lean`; timing
those deterministic diagnostic branches would not add a performance owner.

Policy verdict: retain `natPrimeCertThreshold = 2^24`. The same-input crossover
study in the SPEC, which ran trial and certificate routes separately on each
numeral, locates the crossover region and establishes the boundary; this matrix
validates the selected 24-bit trial and 25-bit certificate endpoints under the
Phase-4 protocol rather than treating their different inputs as a causal route
comparison. At larger inputs the bounded route supplies the required
termination and kernel-depth behavior. At 512 bits, the 0.357 s difference
between the `primality` and `norm_num` medians is below their approximately
0.9–1.0 s matched null envelopes, so neither wrapper is declared faster.

## Comparator Ratios

The SPEC declares `no-comparable-surface-in-named-comparator` for this proof
track: there is no honest external ratio. PrimeCert is relevant
to the core certificate-search/checker report, but it uses a different Lean
toolchain and does not exercise this repository's `Nat.Prime` registration,
Mathlib `norm_num` dispatch, bridge theorem, or exact emitted proof term.
Mathlib's default trial extension is part of the measured range-policy decision,
not an external proof-producing comparator with a common supported range: its
generated proof exceeds the pinned default kernel recursion limit on the
31-bit Mersenne prime.

A ratio between `HexPrimality` and `HexPrimalityMathlib` would also double-count
the same certificate search and misstate ownership. Consequently the report
records direct fresh-module costs and the threshold decision, with no synthetic
comparator ratio.

## Profile

Timed-region sampling does not apply to this proof track; the fresh-module
record supplies the required profile evidence. The primary artifact is
`reports/bench-results/hex-primality-mathlib-proof-probes-issue-9765-chungus2.json`,
SHA-256 `7f202b08f1a7ebc5d7ae26cb4b2f6ba0e3b1d2e3123aed4c4565fd45b302f71c`.
It records every build, process-accounting observation, rejected attempt,
preflight window, source hash, dependency checkout, axiom set, and artifact
size. Every raw sample below is `orientation; reference / candidate / signed
delta`, in seconds.

| pair | round 1 | round 2 | round 3 | round 4 | round 5 | round 6 |
|---|---|---|---|---|---|---|
| `import-null` | R→C; 1.822556594 / 1.618454988 / -0.204101606 | C→R; 1.914384486 / 1.921556185 / +0.007171699 | R→C; 2.379057561 / 1.901456215 / -0.477601346 | C→R; 1.525211697 / 1.699450171 / +0.174238474 | R→C; 1.718488609 / 1.712649685 / -0.005838924 | C→R; 2.026145403 / 1.968728166 / -0.057417237 |
| `replay-512-null` | R→C; 3.489821937 / 3.119544729 / -0.370277208 | C→R; 4.227399028 / 3.224157530 / -1.003241498 | R→C; 3.970180603 / 3.621048204 / -0.349132399 | C→R; 3.417322289 / 2.931597576 / -0.485724713 | R→C; 5.048563406 / 4.469309479 / -0.579253927 | C→R; 3.665974404 / 3.994113852 / +0.328139448 |
| `input-31` | R→C; 1.813053429 / 1.625790715 / -0.187262714 | C→R; 1.874965093 / 2.020672900 / +0.145707807 | R→C; 1.919198015 / 1.920380054 / +0.001182039 | C→R; 1.915209498 / 1.814279503 / -0.100929995 | R→C; 2.171498506 / 1.907103815 / -0.264394691 | C→R; 1.820297157 / 1.923628573 / +0.103331416 |
| `literal-31` | R→C; 1.814595817 / 1.719943205 / -0.094652612 | C→R; 1.783185350 / 1.978275082 / +0.195089732 | R→C; 1.914412017 / 1.813977681 / -0.100434336 | C→R; 1.528887605 / 1.517922421 / -0.010965184 | R→C; 2.260803637 / 2.703960536 / +0.443156899 | C→R; 2.072470256 / 2.780323094 / +0.707852838 |
| `reify-31` | R→C; 1.713191023 / 1.818927832 / +0.105736809 | C→R; 1.976833012 / 1.885924538 / -0.090908474 | R→C; 2.974295726 / 1.995770949 / -0.978524777 | C→R; 1.758281232 / 1.519782969 / -0.238498263 | R→C; 2.005590331 / 2.041918703 / +0.036328372 | C→R; 2.050666024 / 1.923299770 / -0.127366254 |
| `replay-31` | R→C; 1.848114715 / 3.015415114 / +1.167300399 | C→R; 1.913606660 / 4.267544959 / +2.353938299 | R→C; 1.958352741 / 3.053110045 / +1.094757304 | C→R; 1.809836710 / 3.320287576 / +1.510450866 | R→C; 1.721517640 / 4.047030072 / +2.325512432 | C→R; 1.956374227 / 4.639464443 / +2.683090216 |
| `primality-31` | R→C; 1.816386122 / 2.739122820 / +0.922736698 | C→R; 1.833191000 / 4.224542730 / +2.391351730 | R→C; 2.095549089 / 3.186986008 / +1.091436919 | C→R; 1.716921449 / 3.117459371 / +1.400537922 | R→C; 1.540973500 / 3.415961094 / +1.874987594 | C→R; 1.838236222 / 4.326842194 / +2.488605972 |
| `input-512` | R→C; 1.811325569 / 1.830627276 / +0.019301707 | C→R; 1.614821828 / 1.931615073 / +0.316793245 | R→C; 1.840204370 / 1.854963917 / +0.014759547 | C→R; 1.918118209 / 1.915824805 / -0.002293404 | R→C; 2.382181744 / 2.116918249 / -0.265263495 | C→R; 2.260359886 / 1.874859000 / -0.385500886 |
| `literal-512` | R→C; 1.871465664 / 1.842848678 / -0.028616986 | C→R; 2.059781170 / 1.954467965 / -0.105313205 | R→C; 1.820134160 / 1.926411279 / +0.106277119 | C→R; 1.914817852 / 1.911406431 / -0.003411421 | R→C; 2.510351152 / 3.074602822 / +0.564251670 | C→R; 1.945509029 / 1.921524930 / -0.023984099 |
| `reify-512` | R→C; 1.862206633 / 1.955304168 / +0.093097535 | C→R; 1.720259222 / 1.936272908 / +0.216013686 | R→C; 2.190694393 / 2.857379332 / +0.666684939 | C→R; 1.918870694 / 1.915961517 / -0.002909177 | R→C; 2.765051177 / 3.533526693 / +0.768475516 | C→R; 1.914984589 / 1.920325366 / +0.005340777 |
| `replay-512` | R→C; 1.972264772 / 3.360305892 / +1.388041120 | C→R; 1.722198149 / 3.318444038 / +1.596245889 | R→C; 2.531818048 / 4.142504522 / +1.610686474 | C→R; 1.719526418 / 3.419307240 / +1.699780822 | R→C; 2.085438031 / 3.353816149 / +1.268378118 | C→R; 2.102404031 / 3.713347017 / +1.610942986 |
| `primality-512` | R→C; 1.711559779 / 3.237204709 / +1.525644930 | C→R; 1.717263045 / 3.415410479 / +1.698147434 | R→C; 1.630384923 / 4.525257842 / +2.894872919 | C→R; 1.820139413 / 3.705006570 / +1.884867157 | R→C; 2.305094816 / 3.848421089 / +1.543326273 | C→R; 1.937014518 / 4.020485921 / +2.083471403 |
| `norm-num-trial` | R→C; 1.922915823 / 1.923656123 / +0.000740300 | C→R; 1.817444557 / 2.024063729 / +0.206619172 | R→C; 2.044860709 / 2.234748306 / +0.189887597 | C→R; 1.920308322 / 2.002046356 / +0.081738034 | R→C; 1.818657259 / 1.816392985 / -0.002264274 | C→R; 1.952802049 / 1.918180077 / -0.034621972 |
| `norm-num-threshold` | R→C; 1.860370564 / 3.727162895 / +1.866792331 | C→R; 1.844040628 / 3.430848547 / +1.586807919 | R→C; 1.714600777 / 4.118424787 / +2.403824010 | C→R; 1.893019081 / 3.514427031 / +1.621407950 | R→C; 1.859073672 / 3.268036029 / +1.408962357 | C→R; 2.213285501 / 4.229398244 / +2.016112743 |
| `norm-num-512` | R→C; 2.119590726 / 3.426652449 / +1.307061723 | C→R; 1.714900795 / 3.312945980 / +1.598045185 | R→C; 1.824661189 / 4.539353512 / +2.714692323 | C→R; 1.921660914 / 3.413379397 / +1.491718483 | R→C; 1.822155894 / 3.346169009 / +1.524013115 | C→R; 1.913090095 / 4.324483598 / +2.411393503 |

The import null has a 0.651839820 s signed span, -0.031628080 s median,
0.477601346 s zero-centred robust envelope, and 9.17% relative robust spread at
a 1.868470540 s build magnitude. The replay null has a 1.331380946 s span,
-0.428000960 s median, 1.003241498 s envelope, and 5.28% relative robust spread
at 3.818077503 s.
Nulls are descriptive only: medians are not subtracted, envelopes do not widen
the absolute gate, and they are not significance tests.

All theorem-bearing candidates reported exactly `[propext,
Classical.choice, Quot.sound]`; import, input, literal, and reification-only
modules reported no theorem axiom set. Candidate `.olean` sizes were 2,936 B
for the baseline; 6,544–7,288 B for inputs; 49,072–53,768 B for literals and
reification; 54,144–58,248 B for replay; 11,184–12,800 B for certificate-backed
full tactics; and 787,408 B for the Mathlib trial proof. The artifact contains
the corresponding `.ilean` and source sizes; this toolchain emitted no private
or server sidecars for these modules.

Provenance: commit `08db89c90f311622d84e3fd751c4a71f75907802`,
clean repository and clean dependency checkouts, Lean
`leanprover/lean4:v4.34.0-rc2`, host `chungus2`, machine ID
`8be29815875342aeaae06e62d60f6b03`, AMD EPYC 9455 48-Core Processor,
Linux 6.12.100 x86_64, Python 3.14.6, `LEAN_NUM_THREADS=1`, CPU 22 (SMT sibling
70), six samples, 30 s arm timeout, 600 s warm timeout, and 32 retry allowance.
The run rejected 187 preflight windows and 42 complete pair attempts, exhausted
no pair, observed no protocol violation, and was classified release-quality.
The maximum admitted frequency spread was 1.1151%; the maximum quiet-window
wait was 158.123 s. The timeout policy is fail-closed: a timed-out arm emits no
proof and invalidates that row rather than changing tactic behavior.
The measurement commit contains every measured source hash. Of those hashed
inputs, the publishing commit changes only the SPEC, to record these results;
the probe modules, runner, Lake target, bridge implementation, and imported
dependencies remain byte-identical to the recorded sources.

## Concerns

None.
