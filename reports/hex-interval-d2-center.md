# Hex interval D2 centered-instantiation experiment

## Question

This D2 vertical asks whether a bounded instantiation rule can add a useful
alternate expression, prove an equality back to the original expression, and
transport an interval through that equality using an untrusted trace checked
by ordinary Lean kernel reduction.

The fixed case starts with `x * (1 - x)`, introduces
`1 / 4 - (x - 1 / 2) ^ 2`, and proves
`0 ≤ x * (1 - x) ≤ 1 / 4` from `0 ≤ x ≤ 1`. It also compares a downstream
reflected proof with an elementary direct proof having the same theorem type.

This experiment establishes a complete small vertical. It does not select the
production fact store, general generation algorithm, or endpoint backend, and
it provides no scaling evidence beyond one nine-node program and ten facts.

## Experiment

[`Center.lean`](../HexInterval/Experiment/Center.lean) is a Mathlib-free,
proof-facing checker with:

- a typed, topologically checked SSA program;
- a versioned `centerV1` recipe adding five nodes at one generation;
- an exact checked equality edge from the product node to the centered form;
- finite-closed literal, subtraction, four-corner multiplication, square, and
  equality-transport facts;
- caller-supplied base boundary, source rows, target row, endpoint limits, and
  structural/work limits; and
- bounded collection preflight and arithmetic-allocation preflight before
  exact endpoint work.

The certificate owns only the proposed program, selected recipe, equality
table, fact table, and result index. Thus it cannot choose its own hypotheses
or theorem. Every equality recipe is checked against the same caller-owned
base boundary and generation cap, and the selected recipe must contribute its
exact edge. The fact accumulator is a transparent newest-first `List`.
Indexed program, source, equality, prior-fact, and final-result lookups charge
each traversed list constructor to `maxLookupSteps`; sequential program,
source, equality, and fact scans are bounded separately by their structural
caps. This is a reduction canary rather than the production storage or unified
work-accounting choice.

[`CenterConformance.lean`](../conformance/HexInterval/CenterConformance.lean)
checks the accepted fixture and adversarial changes to every structural cap,
base/generation metadata, topology, trigger shape, equality linkage, fact
reference, rule result, transport orientation/range, source/target identity,
range shape, endpoint height, and alignment shift. A dead oversized literal is
also rejected before recipe comparison. Appended self-referential topology and
an unused malformed source row are tested separately from the selected recipe
and selected source fact, so those guards isolate whole-table validation.

[`HexIntervalMathlib/Experiment/Center.lean`](../HexIntervalMathlib/Experiment/Center.lean)
interprets the exact raw interval shapes over `ℝ`, proves the finite-closed
arithmetic rules for every sign case, proves equality-edge and generic trace
soundness, constructs a concrete valuation of all nine fixed nodes, and
derives the unconditional expression theorem. Program semantics are relational
over a total valuation but constrain nodes only through exact successful
optional lookups; there is no default value for a malformed node. Generic
`Row.Holds` and `RowsHold` characterizations make
`Certificate.sound` usable from a downstream module without exposing private
implementation bodies.

The three semantic probes share the theorem statement and imported semantic
library:

- the baseline imports only the library;
- the reflected arm constructs the ten-fact certificate locally, proves its
  Boolean check by `decide +kernel`, and applies generic
  `Certificate.sound`; and
- the direct arm proves nonnegativity by signs and the upper bound from the
  centered identity and nonnegativity of a square.

Both arms therefore reuse the already-compiled generic algebraic identity and
soundness library. The measurement is downstream theorem replay, not the
one-time cost of compiling that library.

The committed record is
[`hex-interval-d2-center.json`](bench-results/hex-interval-d2-center.json). It
contains five samples, raw timings, peak RSS, artifacts, axiom reports where a
probe emits one, the exact environment, and SHA-256 hashes of all 16 inputs.
Variant order rotates between samples, exact probe artifacts are removed before
each Lake build, and the harness aborts if a measured input changes. Reproduce
it with:

```sh
python3 scripts/bench/interval_center_sweep.py \
  --samples 5 --repeats 100000
```

The harness invokes Lean only through Lake and never uses `native_decide`.

## Results

### Compiled checker

The compiled driver checks one certificate per call through a non-inlined
generic boundary. Median time over 100,000 calls in each fresh process was:

| Variant | Result | Median per check | Median peak RSS |
| --- | --- | ---: | ---: |
| accepted fixture | accept | 4.850 µs | 8.1 MiB |
| one-step-short lookup budget | reject | 4.702 µs | 8.2 MiB |
| selected equality edge missing | reject | 0.352 µs | 8.1 MiB |
| dead oversized literal | reject | 0.088 µs | 8.2 MiB |

The exact indexed-lookup budget is 74 traversed list constructors; 73 reaches
nearly the end and costs about as much as acceptance. Missing-edge and
literal-resource failures occur at earlier validation stages and are
correspondingly cheaper. All samples returned stable checksums. RSS is
process-level and too coarse to compare these small variants.

One complete accepted check of this fixed certificate took a median 4.850 µs.
There is no preflight-free control, so this experiment does not attribute a
separate cost to trust-boundary hardening. It also does not predict asymptotic
behavior: the list layout intentionally has charged linear lookups, and the
checker does not yet contain a general worklist or instantiation registry.

### Ordinary kernel replay

The import-only core baseline had median fresh-module wall time 0.839 s. The
checked proposition had median wall time 0.999 s and a median paired signed
margin of 0.100 s. Fresh-module samples are noisy: paired margins ranged from
-0.050 s to +0.281 s.

The separate forced `Lean.Kernel.whnf` canary reduced the checked proposition
to `true` in median 30.3 ms. Its whole-module median was 1.400 s against a
1.302 s matched baseline, with a median paired signed margin of 92.7 ms.

The checked theorem's axiom set is exactly `[propext, Quot.sound]`; it contains
neither `sorryAx` nor an execution-trust axiom. The forced-WHNF probe executes
a command and declares no theorem whose axioms could be printed, so its axiom
field is deliberately `null`, not an asserted empty set. The checked replay's
public `.olean` is 3,912 bytes versus 1,640 for the import-only baseline; its
`.olean.private` is 2,520 bytes versus 96, and its `.olean.server` is 1,176
bytes versus 784.

### Reflected versus direct semantic proof

The Mathlib import-only baseline had median fresh-module wall time 4.764 s.

| Proof | Median total wall | Median paired signed margin | Median peak RSS |
| --- | ---: | ---: | ---: |
| reflected certificate | 4.974 s | +0.195 s | 2875 MiB |
| elementary direct | 4.905 s | +0.096 s | 2866 MiB |

Machine load remains material in this small comparison, and the 69 ms
difference between the two total medians is not stable evidence of a winner.
The justified conclusion is that both downstream proof styles are feasible at
this size.

Both theorem axiom sets are exactly
`[propext, Classical.choice, Quot.sound]`. Both public `.olean` files are
10,952 bytes and both `.olean.server` files are 1,176 bytes. The private proof
artifacts differ: reflected is 26,672 bytes and direct is 14,168 bytes, versus
96 bytes for the import-only baseline. The reflected source is also longer,
and its `.ilean` is 11,611 bytes versus 2,999 bytes for the direct arm. Their
erased object files are approximately 4 KiB. These are compiler-artifact facts
for this fixture, not a general storage verdict; peak RSS differs by less than
one percent and supports no finer claim.

## Soundness and resource findings

The vertical closes several trust-boundary questions that apply regardless of
the eventual physical representation.

1. Sources, target, immutable base boundary, and budgets belong outside the
   untrusted certificate. The checker proves exactly those caller-selected
   rows.
2. A locally valid alternate recipe is insufficient: every recipe must use the
   same trusted base boundary and recomputed one-generation classification,
   and the selected witness must be linked to an exact retained equality edge.
3. Structural lengths must be bounded before traversal. Endpoint preflight
   must cover the whole retained program, not merely the backwards proof slice,
   because recipe comparison may inspect otherwise unused literals.
4. Retained endpoint height and temporary arithmetic work are separate.
   Subtraction preflights all required alignment pairs before computing either
   result. Multiplication predicts mantissa growth and uses the signed exponent
   sum before allocation, preserving useful exponent cancellation.
5. Exact optional lookups and exact selected-row equality avoid default-value
   and target-substitution failures. A production trace layout should add an
   explicit theorem relating its stored indices to original derivation order.
6. Source rows may soundly bind composite nodes, not only variables, because
   their truth is a caller hypothesis. Whether the tactic exposes that
   generality by default remains a frontend-policy question.

The soundness argument covers program evaluation, the centered equality, fact
induction, newest-first lookup, equality transport, and caller-target
selection. The fixed-program valuation closes the final reification step rather
than leaving the result conditional on an assumed `Program.Holds`. Raw open,
closed, empty, and unbounded semantics are covered, while this first arithmetic
replay intentionally accepts only finite closed rows.

## Decision and next experiment

Carry forward the caller-bound certificate interface, exact equality linkage,
checked one-generation boundary, whole-program literal preflight, separate
structural and arithmetic budgets, and generic downstream semantic API. The
small transparent list remains a proof-facing reference implementation only;
general generation recurrence still needs per-node provenance and scaling
evidence.

Do not select reflected versus direct proof construction, list versus array or
arena storage, or dyadic versus rational working facts from this fixture. The
next comparison should reuse the same trace semantics on a parameterized
family with growing node/fact counts, duplicate and irrelevant instantiation
proposals, multiple generations, and both accepted and early-rejected traces.
It should measure certificate production and serialization as well as checking
and semantic replay. A separate vertical should extend arithmetic facts to
open and unbounded ranges before the public interval API is frozen.
