# hex-det

One production determinant entry point for square `Hex.Matrix` values over
supported commutative rings. `hex-det` chooses a computation from
`hex-bareiss`, `hex-char-poly`, and eventually `hex-modular-matrix`.
`hex-determinant` retains the Leibniz reference definition `Hex.Matrix.det`
and its determinant identities. The short name `det` names the operation
consumers request, while `determinant` names that existing foundational
library. The new entry point is `Hex.Det.det`, so neither the library nor
the Lean declaration replaces or overloads the reference definition.

This is a specification, with a [Mathlib companion](hex-det-mathlib.md).
It adds no determinant implementation. Noncommutative rings, approximate
floating-point determinants, rank, and characteristic-polynomial dispatch
are outside its scope.

## API and selection evidence

The following is the proposed public surface, not existing declarations:

```lean
namespace Hex.Det

inductive Arm where
  | small | bareiss | elimination | berkowitz | modular | divisor

structure Result (R : Type u) where
  value : R
  selected : Arm
  completed : Arm
  attempts : List Arm

class DetOps (R : Type u) [Lean.Grind.CommRing R] where
  run : {n : Nat} → Hex.Matrix R n n → Result R

def det [Lean.Grind.CommRing R] [DetOps R]
    (A : Hex.Matrix R n n) : R := (DetOps.run A).value

end Hex.Det
```

`DetOps.run` computes once and returns both the value and the route.
`det` is its value projection, not an independently dispatched computation.
`selected` is the initial choice, `completed` is the arm that supplies the
answer, and `attempts` is a nonempty, ordered list starting at `selected`
and ending at `completed`. An ordinary call records a singleton. A modular
attempt that exhausts its fuel and completes through Bareiss records
`[modular, bareiss]`. A divisor attempt can record an intermediate modular
attempt before Bareiss. The route records determinant algorithms only, not
every modular image or subsidiary solve.

Each producer sets the route in the branch that actually returns the value.
In particular, a wrapper must not label the opaque result of a total modular
routine `modular` when that routine may have used Bareiss internally. The
modular integration requires either a result-with-route API below dispatch,
or composition of its partial operations with the same documented total
fallback. No determinant is computed twice to discover its route.

The companion states correctness for the value and for the completed arm.
These laws are separate from `DetOps`: an arbitrary user-supplied instance
is executable code, not a proof of correctness. Selection metadata is also
ordinary data and cannot establish a determinant equation by itself.

## Selection rule

All rows first use `small` for `n = 0, 1, 2`, returning respectively `1`,
`A[(0,0)]`, and `A[(0,0)] * A[(1,1)] - A[(0,1)] * A[(1,0)]`.
This is a mathematical size case, not a tuned crossover. The following
choices apply at larger sizes. The five carrier rows reproduce the surface
of [hex-bareiss's carrier table](../../HexBareiss/SPEC/hex-bareiss.md#supported-coefficient-carriers),
with `Int` and the generic cases stated separately.

| Carrier | Required operations and laws | Selection after the small cases | Instance module in `HexDet` |
|---|---|---|---|
| `Int` | existing integer operations and native `Hex.Matrix.exactDiv` | Bareiss below the measured crossover, modular above it once available and measured | `Int.lean` |
| `Rat` | core `Lean.Grind.Field` and decidable equality | measured choice between division elimination and Bareiss | `Field.lean` |
| `ZMod64 p` | `[ZMod64.Bounds p] [ZMod64.PrimeModulus p]`, field instance from `HexPolyFp.PrimeField` | field policy measured separately from `Rat` | `Field.lean` |
| `DensePoly F` | `[Lean.Grind.Field F] [DecidableEq F]`, polynomial division and `Hex.instExactDivLawsDensePoly` from `HexResultant.ExactDiv` | Bareiss with `Hex.exactDiv`, exercising both `F = Rat` and `F = ZMod64 p` | `Poly.lean` |
| `ZPoly` (`DensePoly Int`) | recursive dense-polynomial exact division over `Hex.instExactDivLawsInt` | Bareiss with `Hex.exactDiv` | `Poly.lean` |
| `MvPoly k R cmp` | the complete coefficient and order context below, with division from `HexMvGcd.Divide` | Bareiss with `Hex.exactDiv`, exercising `R = Int` and `R = Rat` | `MvPoly.lean` |
| other fields `F` | `[Lean.Grind.Field F] [DecidableEq F]` | field constructor accepts a recorded policy choosing elimination or Bareiss | explicit constructor in `Field.lean` |
| other exact-quotient commutative rings `R` | `[Lean.Grind.CommRing R] [DecidableEq R]`, `quot` and its cancellation law below | Bareiss | explicit constructor in `Basic.lean` |
| remaining commutative rings `R` | `[Lean.Grind.CommRing R] [DecidableEq R]` | Berkowitz, `(-1 : R)^n * (Hex.Matrix.charPoly A).coeff 0` | low-priority default in `Basic.lean` |

The `MvPoly` context is `[Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
[Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R]
[Hex.GcdOps R] [Hex.IsMonomialOrder cmp] [Hex.LawfulGcdOps R]`, as required
by the provider. The exact quotient contract is
`∀ a b : R, b ≠ 0 → quot (a * b) b = a`, not merely the presence of `Div R`.
For the listed non-integer Bareiss instances it is supplied by
`fun a b hb => Hex.exactDiv_mul_right a hb` from `HexBasic/ExactDiv.lean`.
No nonzero-determinant or nonzero-leading-minors precondition is allowed.

Concrete carrier instances take precedence over the Berkowitz default.
Generic field and exact-quotient policies are explicit constructors of
`DetOps`, installed locally or by a carrier's integration module. They are
not competing blanket instances: importing a division provider must not
silently change an existing carrier's policy. In particular, exact division
over `Rat` does not override the measured field choice. The umbrella
imports all listed concrete instances. A custom carrier can always use the
Berkowitz default without a quotient. Decidable equality is needed by the
current polynomial computation even on this division-free route.

`ZPoly` shares the `DensePoly Int` instance and receives no second instance
through the alias. A field of polynomial coefficients is not a field of
polynomials. Composite-modulus rings lacking the prime-field assumptions
use Berkowitz when their commutative-ring and equality instances exist.
Zero divisors do not satisfy the exact-quotient law in general.

### Field elimination

The field arm uses forward elimination with row pivoting, accumulating the
product of the unnormalized pivots and the sign of the row permutation.
A failed pivot column returns zero. It does not compute a determinant of
an auxiliary transform or recurse through dispatch.

`Hex.Matrix.rowReduce` in `HexRowReduce/Loop.lean` computes full reduced row
echelon form and a transform, but its result does not carry the determinant
of that transform. Multiplying the normalized diagonal of that result is
not a determinant algorithm. A determinant-specific elimination operation,
including the pivot and sign bookkeeping, must be supplied below dispatch
in `HexRowReduce` before this arm is enabled. Its determinant correctness
belongs in this companion, which can import `HexDeterminant` through the
appropriate dependency paths. This does not add an upward dependency from
`HexRowReduce` to dispatch. Until this operation exists and has measurements,
the field constructor uses Bareiss as its explicit initial policy.

### Integer modular integration

[hex-modular-matrix](hex-modular-matrix.md) specifies the modular and divisor
algorithms but has no registered library or implementation today. Initial
integer dispatch therefore uses Bareiss at every `n > 2`. Enable modular
selection only after the lower algorithm, route reporting, correctness
integration, and crossover measurement exist. This initial availability
rule is not a claim that Bareiss wins for large matrices.

The eventual policy selects Bareiss below a measured cutoff and modular
at or above it. Dimension and input coefficient bit length may determine
the measured region. `detViaDivisor` is an optional measured choice inside
that region, not an unconditional extra solve on every input. Its seeds and
fuel settings are deterministic, recorded policy parameters. The lower
library owns reconstruction, its bound, and finite-fuel fallback. Dispatch
must preserve those contracts, including the `LawfulDetBound` proof required
for modular correctness in the companion. Stabilization of residues alone
never certifies an answer.

## Dependencies and files

Register `HexDet` as planned, with direct dependencies on `HexBareiss`,
`HexCharPoly`, `HexRowReduce`, `HexPolyFp`, `HexResultant`, and `HexMvGcd`.
`HexMatrix`, `HexDeterminant`, `HexBasic`, and `HexPoly` are reachable through
those dependencies. The carrier instance modules live here, above both
matrix algorithms and quotient providers. Neither `HexBareiss` nor a
quotient provider acquires a dependency on `HexDet`.

The intended files are `HexDet/{Basic,Int,Field,Poly,MvPoly}.lean` and the
`HexDet.lean` umbrella. `Basic` owns the public protocol, small cases,
Berkowitz default, and generic exact-quotient constructor. The other modules
own carrier policies and instances. This issue creates only the SPECs and
planned metadata, not these source files or Lake targets.

When registered and implemented, add `HexModularMatrix` to `HexDet.deps`,
and `HexModularMatrixMathlib` to the companion's dependencies. Neither
modular library may depend on `HexDet`. The lower modular API must use a
namespace distinct from the existing `Hex.Matrix.det` and new `Hex.Det.det`.
The `det` signatures in its SPEC describe planned operations, not existing
callable names. Adding these edges preserves the topological order because
both modular libraries depend only on libraries below dispatch.

`scripts/check_dag.py` checks registered dependencies and actual imports,
not Markdown arrows. The planned entries make the current graph checkable.
The deferred modular edges must be registered and checked when their targets
exist. `hex-matrix-tactic` is a downstream consumer, with no reverse edge.

## Correctness and tactic use

Every shipped arm must equal `Hex.Matrix.det A`. All dispatch correctness
statements and proofs in the first version live in
[hex-det-mathlib](hex-det-mathlib.md), including statements whose two sides
are Mathlib-free expressions. A Mathlib-free executable is not thereby a
Mathlib-free proof. A Mathlib-free proof of the Berkowitz determinant arm
is future work. No axiom, `native_decide`, or invented lower-layer proof
fills that gap.

[hex-matrix-tactic (#10151)](https://github.com/kim-em/hex-dev/issues/10151)
consumes `DetOps.run` and follows `completed`, retaining `selected` and
`attempts` for diagnostics and reproducible strategy measurements. Small
forms permit direct normalization, Bareiss and elimination permit their
correspondence plus kernel replay or a separately proved certificate,
and Berkowitz can use characteristic-polynomial certificate machinery.
A modular answer requires the reconstruction and bound correctness route,
or a separate verified recomputation. Dispatch promises no cheap modular
determinant certificate. A tag or compiled value is never proof evidence.

The tactic separately chooses between kernel replay and certificate
construction, measuring coefficient size and symbolic growth as well as
matrix dimension. It does not maintain a second table choosing the
production determinant algorithm. If a proof strategy is unavailable for
the completed arm, the tactic reports that limitation or explicitly checks
the value by another sound strategy. It cannot pretend a Bareiss certificate
was returned by a modular run. The Mathlib-free tactic can compute values
but cannot import these companion theorems as Mathlib-free correctness.

## Conformance and measured policies

`HexDet` owns conformance and performance. Compare dispatch and every
available forced arm on identical matrices, including empty and tiny
matrices, row swaps, singular matrices, zero pivot columns, odd and even
sizes, and the trivial ring where `1 = 0`. Check both values and actual
route transitions, especially forced modular exhaustion. Exercise each
carrier in the table, nonconstant polynomial pivots, and a commutative ring
with zero divisors through Berkowitz. Compare against Leibniz at small
sizes only. Larger oracle comparisons use python-flint for integers,
rationals, and prime residues, and SymPy's explicit Berkowitz method over
identical exact polynomial domains for polynomial carriers.

The required Phase-4 input families are:

| Family | Sweep and compared arms |
|---|---|
| `integer` | dimension and entry bit length on dense, tridiagonal, triangular, singular, low-rank, and unimodular matrices: Bareiss, modular, and divisor when available |
| `field` | dimension, rational numerator/denominator bit lengths, and prime modulus: forward elimination versus Bareiss, with Berkowitz as a reference on feasible sizes |
| `dense-poly` | dimension, entry degree, and coefficient size over `Rat`, prime `ZMod64`, and `Int`: Bareiss versus Berkowitz, including exact division by nonconstant pivots |
| `mv-poly` | dimension, variable count, total degree, support, and coefficient size over `Int` and `Rat`: Bareiss versus Berkowitz, including nonconstant pivots and expression growth |
| `dispatch` | tiny dimensions, both sides of each measured cutoff, modular fallback, and rings with zero divisors: dispatch overhead versus its selected direct arm |

Crossovers are benchmark outputs, never numerical SPEC constants. Record
each enabled cutoff, coefficient-size region, tie rule, seed, and fuel
setting with the source revision, fixture identifiers, command, host context,
raw measurements, and adjacent-arm ratios in
`reports/hex-det-performance.md`. Register these families under
`HexDet.phase4.input_families` in `libraries.yml`. When a policy is enabled
or changed, update the corresponding family's `description` with the exact
policy constant names and values and a reference to the report's policy
table. This uses the existing `phase4` schema, which has no `crossovers`
field. The report and executable policy must agree with that record.

Use the shared-host discipline in [benchmarking](../benchmarking.md):
automatically select and pin a CPU when supported, retain host context and
all completed samples, use fixed trial-major schedules for scaling, and
adjacent alternating AB/BA arms for comparisons. Allow at most one unchanged
rerun of an inconclusive comparison. Never tune a cutoff without recorded
measurements. An inconclusive comparison keeps the existing policy. The
initial availability policies above must be labeled unmeasured until the
first evidence is collected.

Internal comparisons determine selection. External comparators are
informational because their algorithm selection and process overhead differ.
Ordinary Mathlib-free bench targets verify bounded fixture outputs and route
agreement. Timing runs are manual, extending the existing benchmark setup
under its CI wall-clock cap, with no new workflow jobs. Tactic elaboration,
certificate construction, kernel checking, and proof-size measurements are
owned by the tactic library, not substituted for these producer timings.
