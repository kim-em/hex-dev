# hex-interval-mathlib specification

`hex-interval-mathlib` is the Mathlib companion to the Mathlib-free
`hex-interval` computational library. It owns interpretations into Mathlib
types and ordinary-kernel proofs of the public interval operations; it does not
perform planner search or turn runtime checks into proof evidence.

## Supported surface

The foundational supported module is `HexIntervalMathlib.Interval`. It defines the
real value of a dyadic endpoint and membership for every public interval cut:
strict or closed finite ends, independent unbounded ends, and canonical empty.
`HexIntervalMathlib.Addition`, `HexIntervalMathlib.Subtraction`, and
`HexIntervalMathlib.Multiplication` add the public arithmetic image theorems,
while `HexIntervalMathlib.MinMax` supplies selected-cut and real-image
enclosure theorems for minimum and maximum, and
`HexIntervalMathlib.Absolute` supplies the corresponding absolute-value
theorems. `HexIntervalMathlib.Power` supplies exact selected-cut semantics
and a one-way real-image theorem for checked natural power.
`HexIntervalMathlib.Split` proves exact closed-left/strict-right membership
for transactional splitting. `HexIntervalMathlib.Inverse` proves the computed
connected-cut characterization and sound total-real-inverse enclosure, while
`HexIntervalMathlib.Division` proves the computed first-slice quotient cuts and
sound total-real-division enclosure. `HexIntervalMathlib.Regularize` proves
exact rounded-cut semantics, outward containment, and raw-cut idempotence.

For every successful resource-checked public operation it proves:

- `contains_intersectWithin`: membership in the result is equivalent to
  membership in both inputs;
- `contains_hullWithin`: membership in the result is exactly the selected-cut
  interval closure, with explicit empty identities and no false set-union
  claim;
- `contains_hullWithin_left` and `contains_hullWithin_right`: each input is
  contained in the result;
- `contains_negWithin`: membership of `x` in the result is equivalent to
  membership of `-x` in the input;
- `contains_addWithin`: exact successful-result membership in the independently
  summed Minkowski cuts, with empty absorption, unbounded sides, and endpoint
  strictness;
- `add_mem_addWithin`: two input members add to a member of every successful
  result;
- `contains_subWithin`: exact successful-result membership in the crossed
  difference cuts, including empty absorption and independent unbounded
  sides;
- `sub_mem_subWithin`: two input members subtract to a member of every
  successful result;
- `contains_minWithin` and `contains_maxWithin`: exact membership in the
  computed selected cuts;
- `min_mem_minWithin` and `max_mem_maxWithin`: pointwise real minimum and
  maximum of two input members belong to every successful result;
- `contains_absWithin`: exact membership in the normalized selected absolute
  value cuts;
- `contains_absUnchecked`: raw absolute-value cuts contain `|x|` whenever the
  source raw interval contains `x`; this is a one-way image theorem, not a
  converse characterization;
- `abs_mem_absWithin`: the absolute value of every input member belongs to every
  successful result;
- `contains_mulWithin`: exact successful-result membership in the explicit
  selected lower and upper candidate cuts after normalization, including
  empty, unbounded, strict, closed, and zero-attainment cases;
- `mul_mem_mulWithin`: two input members multiply to a member of every
  successful result. This is an enclosure theorem; no separate image-tightness
  converse is claimed;
- `contains_powWithin`: exact membership in the normalized direct cuts selected
  for exponent zero, positive odd powers, and positive even powers;
- `pow_mem_powWithin`: every source member raised to the caller's natural
  exponent belongs to every successful result;
- `contains_regularizeWithin`: exact membership in the normalized Core-rounded
  cuts;
- `contains_regularizeUnchecked` and `mem_regularizeWithin`: every source
  member remains in the raw and checked outward views;
- `regularizeUnchecked_idem`: repeating the same requested precision leaves
  every computed raw cut unchanged, without claiming global grid tightness;
- `contains_splitWithin_left` and `contains_splitWithin_right`: exact child
  membership as source membership conjoined with `x ≤ point` or `point < x`;
- `splitWithin_contained`, `splitWithin_cover`, and `splitWithin_disjoint`:
  both children remain in the source, jointly cover it, and do not overlap;
- `splitWithin_point_left` and `splitWithin_point_not_right`: the cut point is
  left-owned exactly when it belonged to the source and never right-owned;
- `contains_invWithin`: membership in a successful reciprocal is exactly the
  normalized computed outward-cut predicate; this does not identify the
  connected hull with the generally-disconnected exact image;
- `inv_mem_invWithin`: every real source member maps under Lean's total
  reciprocal into the successful enclosure, including `0⁻¹ = 0`;
- `contains_divWithin`: membership in successful division is exactly its
  computed singleton outward cuts or explicit whole-line fallback;
- `div_mem_divWithin`: both source memberships are consumed to place their
  Lean-total real quotient in every successful enclosure.

These theorems depend on the exact successful result equation: `BuildResult`
or `Arithmetic.Result` for unary/binary images, and transactional
`SplitResult` for splitting. A resource refusal has no set interpretation and
is never treated as an empty interval. The proofs use the public operation's
checked view-characterization
theorems and independently establish the complete raw-cut semantics; they do
not import the experimental propagation fact domain.

## Boundary

The public companion grows only with the supported `Hex.Interval` API. Its
`Program` module gives exact meanings to the supported decoded SSA program,
and its `Proof` module owns function-agnostic package schemas, chronological
typed replay, target closure, and the kernel-checked `Expr` emission boundary.
Runtime search state, callbacks, payload bytes, and traces are untrusted and
cannot enter `Proof.Evidence`. The concrete package registry, goal reifier,
search-to-proof quotation, and tactic syntax remain experimental and are not
re-exported here. Further arithmetic images and useful bounded
nonsingleton division require their own
operation-specific semantic theorems before promotion. An image operation must
at least prove successful-result cut semantics and sound real-image enclosure;
it claims a tightness converse only when that converse is separately proved.
Public reciprocal is sound but
conservatively closes finite rounded cuts; endpoint attainment, grid
optimality, and disconnected interval-set precision remain future work.
Public division directly encloses two nonzero finite singletons, handles empty
and total-zero cases exactly, and deliberately returns whole for every other
nonempty shape. No tightness converse or bounded nonsingleton quotient is
claimed.

The supported proof limits cap retained package and schema counts, certificate
body cells, ordered dependencies, and chronology. They do not claim to
preempt full `Program.check` or registration validation, equality on arbitrary
caller facts, schema decoding, or package theorem callbacks. Authenticated
search output must first pass the Mathlib-free `Search` envelope; a direct
trusted caller of `Proof` is responsible for bounding its program and package
assembly before replay.

`HexIntervalMathlib.Experiment.PntLogRational` is a fixed-source acceptance
provider rather than public interval arithmetic. It proves the original
strength of seventeen pinned PNT+ direct-log declarations over fifteen
rational inputs from an authenticated dyadic reduction, eight-term atanh sum,
geometric tail, and checked `log 2` bounds. The runtime accepts exact source
rows only; arbitrary rational inputs, generated precision/endpoints, table
persistence, and every admitted LeanCert-owned public bound remain outside its
claim.

`HexIntervalMathlib.Experiment.PntExpPoint` proves the nine remaining pinned
exponential statements from one rational Taylor/power theorem. Each source row
fixes a signed rational input, a step in `[-1, 1]`, a positive natural
multiplier, one checked side of a fourteen-term Taylor enclosure, and the final
rational cut. The result preserves the source statements and does not import a
LeanCert theorem. It is not a public arbitrary-input exponential operation.

`HexIntervalMathlib.Experiment.PntNestedLogTwo` proves the two pinned
`log (log 2)` statements through two chronological checked log events. The
first establishes a strict positive two-sided `log 2` enclosure; the second
consumes both endpoints in fourteen-term rational remainder checks. The
ordinary replay theorem is strictly stronger than both source statements, and
zero-touching or bypassed inner facts reject.

`HexIntervalMathlib.Experiment.PntPiPoint` interprets a provider-agnostic
constant operation as `Real.pi`, authenticates the exact `315 / 100` cut, and
uses the axiom-clean `Real.pi_lt_d2` theorem from `Analysis.Real.Pi.Bounds`.
It does not import Mathlib's Chudnovsky development; the latter's
`proof_wanted` sum-to-`π⁻¹` identity is not migration evidence.

Together with the other source-pinned providers, these slices cover every
actual pinned `LogTables.lean` tactic site after localized rewrites or stronger
results. They do not provide LeanCert API parity, arbitrary input/precision
support, persistent tables, or table-scale performance evidence.

## Conformance

`HexIntervalMathlib.IntervalConformance` pins both directions of intersection
membership, exact hull closure and both input inclusions, negation transport,
addition, subtraction, and multiplication cut exactness and image transport,
exact split membership/coverage/disjointness/point ownership, and the exact
regularization cut semantics/outward containment/idempotence, together with the
ordinary-kernel axiom surface. It also pins reciprocal computed-cut exactness
and total-real-inverse enclosure, plus division computed-cut exactness and
total-real-division enclosure, without tightness converses.
`HexIntervalMathlib.MinMaxConformance` separately pins exact selected cuts,
both image enclosures, and their axiom surfaces; it does not assert a set-image
converse.
The interval conformance module also pins absolute-value cut exactness, image
transport, and its ordinary-kernel axiom surface, together with natural-power
cut exactness and image transport. The power theorem is one-way: no unproved
set-image converse is exported.
The Mathlib-free companion tests separately pin representative strict, closed,
unbounded, and empty shapes together with pre-allocation resource refusal. The
semantic theorem itself is exhaustive over the complete cut language.
`HexIntervalMathlib.ProgramProofConformance` independently pins exact operation
alignment and a live instance → fact → equality → transport chronology,
including body/source/version/final-state mutations, refuter ownership, a
nonvacuous ordinary theorem with a guarded axiom report, and transactional
Meta-state restoration after a wrongly typed emitter.
`HexIntervalMathlib.PntLogRationalConformance` additionally runs all fifteen
fixed rows and sends the representative large-shift `32e12` certificate through
generic planning, payload authentication, chronological replay, and the proof
frontend, with source, reduction, term-count, cross-row, window, and false-cut
rejection guards.
`HexIntervalMathlib.PntExpPointConformance` runs all nine fixed exponential
rows and sends the tight `exp 20` certificate through generic planning,
payload authentication, chronological replay, and the proof frontend. It also
pins source, Taylor-step, natural-power, term-count, cross-row, and false-cut
rejection.
`HexIntervalMathlib.PntNestedLogTwoConformance` pins the two-event dependency
chain, positive-domain rejection, both exact source wrappers, and generic
proof-frontend closure of the stronger two-sided theorem.
`HexIntervalMathlib.PntPiPointConformance` pins the exact constant certificate,
wrong-source and false-endpoint rejection, the ordinary π-bound axiom surface,
and generic proof-frontend closure.
