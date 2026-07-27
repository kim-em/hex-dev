# Hex interval D2 representation experiment

## Question

The first D2 microexperiment asks whether carrying a proof of raw-cut
consistency changes the compiled hot value, and measures the cost of checking
plain normalized data at a handoff boundary. It also installs a downstream
kernel-reduction canary for the common constructor path.

This experiment does **not** freeze the public `Hex.Interval` representation.
In particular, it does not yet compare serialized proof-carrying interval
literals against a reflected trace. The generated replay values below project
the bundled candidate to its raw view, so this is a newtype/validation-scan
microprobe rather than the complete D2 trace-layout comparison.

## Experiment

[`HexInterval/Basic.lean`](../HexInterval/Basic.lean) defines the shared exact
dyadic `Lower`, `Upper`, and `Raw` types, the Boolean consistency predicate,
and canonical normalization.  The two provisional candidates in
[`Representation.lean`](../HexInterval/Experiment/Representation.lean) are:

- `Bundled`, a one-live-field structure containing normalized `Raw` plus a
  proof of `Raw.CutConsistent`;
- `Checked`, an abbreviation for normalized `Raw`, validated by a Boolean
  scan when it crosses the replay boundary.

The deterministic workload cycles through empty, whole, one-sided unbounded,
proper finite, reversed, open-singleton, and closed-singleton inputs.  The
compiled driver stores candidate values in arrays.  The downstream replay
probes use a transparent `List`/`Nat` encoding and prove the 433-element
answer with `decide +kernel` under the default limits. These generated values
exercise construction and projection, but do not serialize one proof field per
interval; the next vertical experiment must measure literal trace bytes and
proof-expression nodes separately.

The committed record is
[`hex-interval-d2-representation.json`](bench-results/hex-interval-d2-representation.json).
It contains five independent processes per compiled or replay case, the exact
environment, raw samples, peak RSS where available, artifact sizes, and axiom
sets. Candidate order rotates between samples to reduce machine-load drift,
and the record hashes all 24 source, build, and toolchain inputs. Run it again
with:

```sh
python3 scripts/bench/interval_representation_sweep.py \
  --samples 5 --sizes 433 4096
```

The harness builds every proof probe through Lake and never uses
`native_decide`.

## Results

### Compiled representation

Median compiled time per complete arena construction and checksum was:

| Values | Bundled | Checked | Bundled boundary | Checked boundary |
| ---: | ---: | ---: | ---: | ---: |
| 433 | 39.0 µs | 38.5 µs | 38.7 µs | 43.5 µs |
| 4096 | 384.3 µs | 382.4 µs | 383.3 µs | 429.2 µs |

Construction differs by about one percent or less in this run.  Inspecting the
generated C explains why: the proof field is erased, the one-live-field
`Bundled` wrapper is a newtype, and both `Bundled.ofTrustedRaw` and
`Checked.ofTrustedRaw` compile to the same call to `Raw.normalizeUnchecked`.
`Bundled.view` is the identity.

The externally checked boundary costs about 12–13% at these sizes because it
performs an additional full consistency scan.  This is a
real cost, but it is paid at handoff rather than on each propagation update.
Every value in this timing was first canonicalized, so the scan is deliberately
redundant validation of a valid handoff, not normalization of an untrusted raw
trace. Separate conformance guards ensure malformed raw elements are rejected.

The shape cycle is intentionally broad rather than comparison-heavy. At the
boundary, two of every eight normalized values have two finite endpoints and
therefore run `Dyadic.blt`; the other six are empty or have an unbounded side.
An all-finite 256/1024-bit workload remains necessary before estimating the
production cost of endpoint-heavy traces.

Peak RSS varied between roughly 4 and 8 MiB even for definitionally identical
paths.  It is too coarse to distinguish the layouts.  The installed Lean
runtime exposes no portable allocation counter, so this experiment makes no
allocation-byte claim.

### Ordinary kernel replay

The import-only Lake baseline had median wall time 1.165 s. The candidate
module medians and baseline-subtracted margins were:

| Candidate | Total wall | Baseline-subtracted | Peak RSS |
| --- | ---: | ---: | ---: |
| Bundled | 2.131 s | 0.966 s | 791 MiB |
| Checked | 1.968 s | 0.803 s | 792 MiB |

Lake startup and module loading dominate these small proofs, and individual
candidate samples ranged from 1.564 s to 2.647 s. Whole fresh-module timings
remain load-sensitive. Both generated-constructor canaries are feasible at 433
values, and this projected-value workload does not justify closing the
trace-layout design space.

The independent `Lean.Kernel.whnf` canaries also reduce to `true` under the
default limits. Directly timing the forced `Lean.Kernel.whnf` calls gave
medians of 729.3 ms for bundled and 804.7 ms for checked. Their whole
fresh-module times were 2.523 s and 2.507 s respectively, against an
import-matched 1.734 s
baseline; the corresponding signed margins were 0.789 s and 0.774 s. The
direct timer isolates the reduction call; the whole-module number includes
process startup, imports, and elaboration.

The candidate compiled artifacts were identical in size; their small source
files differ in length:

| Artifact | Bundled | Checked |
| --- | ---: | ---: |
| source | 701 B | 712 B |
| `.olean` | 4448 B | 4448 B |
| `.ilean` | 758 B | 758 B |
| generated C | 2790 B | 2790 B |
| object | 3976 B | 3976 B |
| incremental importer `.olean` | 1568 B | 1568 B |

Each proof's `.olean` is 584 bytes larger than the import-only baseline.  Both
transitive axiom sets are exactly `[propext, Quot.sound]`; neither contains
`sorryAx` or any execution-trust axiom.

### Mathlib-free rational replay

[`Rational.lean`](../HexInterval/Experiment/Rational.lean) tests two ways to
avoid depending on Mathlib's `norm_num`:

- exposed wrappers around core `Rat.normalize`, related to ordinary rational
  operations by `Rat.add_def`, `Rat.sub_def`, `Rat.mul_def`, and `Rat.inv_def`;
- untrusted signed numerator/denominator literals whose addition, subtraction,
  multiplication, and inverse claims are checked by integer cross-products.

The latter has generic Mathlib-free soundness theorems into `Rat`, including
Lean's total convention `0⁻¹ = 0`. Its fold-level soundness theorem composes
successful checked edges to the exposed rational fold.

Both microprobes concern the same 433 additions, but their measured workloads
are deliberately different. The exposed arm constructs and normalizes every
intermediate `Rat`; the checked arm validates numerator/denominator literals
that a planner has already supplied. Thus the latter isolates certificate
verification and excludes certificate production. Both replay with ordinary
`decide +kernel`:

| Encoding | Total wall | Baseline-subtracted | `.olean` | Axioms |
| --- | ---: | ---: | ---: | --- |
| Exposed normalization | 1.431 s | 0.079 s | 4920 B | `propext`, `Classical.choice`, `Quot.sound` |
| Cross-product checks | 1.564 s | 0.212 s | 4376 B | none |

The rational import baseline was 1.352 s; margins remain signed rather than
being clamped at zero. Separate forced WHNF calls reached `true` in median
92.7 ms and 157.0 ms respectively. Their whole fresh-module medians were
1.971 s and 2.058 s, against an import-matched 1.868 s baseline; the signed
margins were 0.104 s and 0.190 s. The forced-call timing is the useful
comparison. This small
repeated-addition case favors exposed normalization for reduction time, while
cross-products produce a smaller and axiom-free proof module. It does not
select the rational representation: end-to-end certificate production,
high-precision denominator growth, validating shared nodes once instead of
once per edge, and an identical arithmetic DAG must still be measured.
Mathlib-side `norm_num` remains a useful third arm for frontend leaves, not a
dependency of the shared engine.

### Replay encoding remains open

The successful canary deliberately uses explicit public constructors and a
transparent `List`/`Nat` fold rather than the compiled arena's arrays and
machine words. It establishes that this conservative proof boundary reduces
downstream. It does not establish that every array-backed checker would fail,
or measure proof-bearing interval literals. The next vertical experiment must
hold the planner output fixed and compare direct literal proofs against a
reflected trace, including certificate bytes and proof-expression nodes.

## Related endpoint findings

Lean core's `Dyadic` representation is already canonical: a nonzero value has
an odd mantissa and an arbitrary signed exponent.  Interval normalization must
normalize only interval shape, not add another numeric normalization layer.

Two endpoint risks need explicit follow-up experiments:

1. Dyadic comparison and addition align exponents by shifting a mantissa. A
   huge exponent gap can request a huge allocation. The shared layer now
   exposes `Raw.normalizeWithin`, which computes mantissa bits, exponent
   magnitude, encoded exponent bits, and alignment shift before normalization;
   its conformance suite rejects a compactly encoded gap of one billion as a
   `resourceLimit` without comparing the endpoints. The unchecked
   `Raw.normalizeUnchecked` remains only the exact operation for trusted or
   already preflighted values. Every later arithmetic rule still needs the
   same guard.
2. Core `Rat.add`, `Rat.mul`, `Rat.sub`, and `Rat.inv` are opaque through their
   ordinary operation instances, so a bare `decide +kernel` does not unfold
   them. This is an encoding constraint, not an obstacle to Mathlib-free
   rational replay. Core supplies reducible normalization together with
   `Rat.add_def`, `Rat.sub_def`, `Rat.mul_def`, and `Rat.inv_def`; a replay
   layer can expose those computations or check numerator/denominator
   cross-products. The companion may instead use `norm_num` for isolated
   frontend leaves. D2 must compare these encodings on the same traces.

Neither issue is solved by, or permits, `native_decide`.

## Decision and next experiment

The raw cut shape, exact canonicalizer, and resource-safe normalization entry
point are ready to carry forward. The backing representation remains open.
Compiled newtype erasure makes a bundle inexpensive in this workload, while a
separate validation scan has measurable handoff cost. Neither result predicts
serialized proof size. A hybrid—plain `Raw` in traces or hot arenas, with a
bundled canonical value at a mathematical API boundary—remains a hypothesis,
not a selection.

The next D2 PR should compare direct theorem leaves against a reflected Boolean
checker on the same small arithmetic DAG.  Its mandatory case adds the centered
form `1/4 - (x - 1/2)^2`, transports its bound across the equality
`x * (1 - x) = 1/4 - (x - 1/2)^2`, and proves `x * (1 - x) ≤ 1/4` for
`x ∈ [0,1]`.  Run that case across bundled/plain and dyadic/rational working
facts before selecting a trace representation.  The BKLNW fold organization,
branch-state storage, and high-precision transcendental certificate remain
separate D2 decisions.
