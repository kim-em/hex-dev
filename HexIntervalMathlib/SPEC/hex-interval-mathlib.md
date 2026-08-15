# hex-interval-mathlib specification

`hex-interval-mathlib` is the Mathlib companion to the Mathlib-free
`hex-interval` computational library. It owns interpretations into Mathlib
types and ordinary-kernel proofs of the public interval operations; it does not
perform planner search or turn runtime checks into proof evidence.

## Supported surface

The first supported module is `HexIntervalMathlib.Interval`. It defines the
real value of a dyadic endpoint and membership for every public interval cut:
strict or closed finite ends, independent unbounded ends, and canonical empty.

For every successful resource-checked public operation it proves:

- `contains_intersectWithin`: membership in the result is equivalent to
  membership in both inputs;
- `contains_negWithin`: membership of `x` in the result is equivalent to
  membership of `-x` in the input.

These theorems depend on the exact successful `BuildResult` equation. A
resource refusal has no set interpretation and is never treated as an empty
interval. The proofs use the public operation's checked view-characterization
theorems and independently establish the complete raw-cut semantics; they do
not import the experimental propagation fact domain.

## Boundary

The public companion grows only with the supported `Hex.Interval` API. The
existing modules under `HexIntervalMathlib/Experiment` remain evidence for
future operations, replay schemas, transcendental providers, and tactics, but
are not re-exported here. Hull, arithmetic images, powers, splitting,
regularization, and precision-indexed reciprocal/division require their own
set-enclosure and stated tightness theorems before promotion.

## Conformance

`HexIntervalMathlib.IntervalConformance` pins both directions of intersection
membership, negation transport, and the exact ordinary-kernel axiom surface.
The Mathlib-free companion tests separately pin representative strict, closed,
unbounded, and empty shapes together with pre-allocation resource refusal. The
semantic theorem itself is exhaustive over the complete cut language.
