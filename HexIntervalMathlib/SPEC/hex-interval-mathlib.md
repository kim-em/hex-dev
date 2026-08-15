# hex-interval-mathlib specification

`hex-interval-mathlib` is the Mathlib companion to the Mathlib-free
`hex-interval` computational library. It owns interpretations into Mathlib
types and ordinary-kernel proofs of the public interval operations; it does not
perform planner search or turn runtime checks into proof evidence.

## Supported surface

The foundational supported module is `HexIntervalMathlib.Interval`. It defines the
real value of a dyadic endpoint and membership for every public interval cut:
strict or closed finite ends, independent unbounded ends, and canonical empty.
`HexIntervalMathlib.Addition` and `HexIntervalMathlib.Subtraction` add the
public arithmetic image theorems, while `HexIntervalMathlib.MinMax` supplies
selected-cut and real-image enclosure theorems for minimum and maximum, and
`HexIntervalMathlib.Absolute` supplies the corresponding absolute-value
theorems.

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
  successful result.
- `contains_minWithin` and `contains_maxWithin`: exact membership in the
  computed selected cuts;
- `min_mem_minWithin` and `max_mem_maxWithin`: pointwise real minimum and
  maximum of two input members belong to every successful result.
- `contains_absWithin`: exact membership in the normalized selected absolute
  value cuts;
- `abs_mem_absWithin`: the absolute value of every input member belongs to
  every successful result.

These theorems depend on the exact successful `BuildResult` equation. A
resource refusal has no set interpretation and is never treated as an empty
interval. The proofs use the public operation's checked view-characterization
theorems and independently establish the complete raw-cut semantics; they do
not import the experimental propagation fact domain.

## Boundary

The public companion grows only with the supported `Hex.Interval` API. The
existing modules under `HexIntervalMathlib/Experiment` remain evidence for
future operations, replay schemas, transcendental providers, and tactics, but
are not re-exported here. Further arithmetic images, powers, splitting,
regularization, and precision-indexed reciprocal/division require their own
operation-specific semantic theorems before promotion. An image operation must
at least prove successful-result cut semantics and sound real-image enclosure;
it claims a tightness converse only when that converse is separately proved.

## Conformance

`HexIntervalMathlib.IntervalConformance` pins both directions of intersection
membership, exact hull closure and both input inclusions, negation transport,
addition and subtraction cut exactness and image transport, and the exact
ordinary-kernel axiom surface. `HexIntervalMathlib.MinMaxConformance` separately
pins exact selected cuts, both image enclosures, and their axiom surfaces; it
does not assert a set-image converse. The interval conformance module also pins
absolute-value cut exactness, image transport, and its ordinary-kernel axiom
surface.
The Mathlib-free companion tests separately pin representative strict, closed,
unbounded, and empty shapes together with pre-allocation resource refusal. The
semantic theorem itself is exhaustive over the complete cut language.
