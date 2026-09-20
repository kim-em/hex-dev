# Named-constant point proof boundary

This is the analytic source slice of #10342, paired with the bounded runtime
work in #10334. It does not implement an interval solver, a runtime point
provider, or an OrderedFn registration. Whole-library phase counters are
unchanged.

## Existing containment API

All names below are in `Hex.Interval` and available through the public
`HexIntervalMathlib` umbrella. No second interval representation or arithmetic
soundness layer is needed.

| Operation | Public semantic artifact |
| --- | --- |
| Dyadic cuts | `toReal`, `Lower.Contains`, `Upper.Contains`, `Raw.Contains`, `Contains` in `Interval.lean` |
| Canonicalization | `contains_normalize` |
| Intersection | `contains_intersectWithin` gives the conjunction of the two input memberships, including openness |
| Addition | `add_mem_addWithin` |
| Subtraction | `sub_mem_subWithin` |
| Multiplication | `mul_mem_mulWithin` |
| Regularization | `mem_regularizeWithin` preserves containment on successful outward rounding |
| Reciprocal | `inv_mem_invWithin`, with nonzero input and successful checked operation |
| Division | `div_mem_divWithin`, with nonzero denominator and successful checked operation |

The corresponding `contains_*Within` theorems identify the checked computed
cuts. Success hypotheses matter: resource exhaustion is not an empty interval.
`contains_ofOrderedBoundsUnchecked` interprets already ordered cuts; it is not
a resource-safe constructor. Existing regularization proves containment and
idempotence, but explicitly does not prove optimal rounding or a width bound.
The effective provider contract must also control the *amount* of rounding.
Horner composition and coefficient refinement remain in HexOrderedFnMathlib.

## Analytic sources

The audited Mathlib pin is `1cf325a0cf67aca2b04d76b5380ff6a9e410aefa`
from `lake-manifest.json`.

For π, `Elementary/Constants.lean` uses
`Real.four_mul_arctan_inv_5_sub_arctan_inv_239` from
`Analysis/SpecialFunctions/Trigonometric/Arctan.lean`,
`Real.hasSum_arctan` from `Analysis/SpecialFunctions/Complex/Arctan.lean`, and
`norm_sub_le_of_geometric_bound_of_hasSum` from
`Analysis/SpecificLimits/Normed.lean`. These are proved declarations, not the
unproved Chudnovsky identity. With

```
S_n(x) = sum (i < n), (-1)^i * x^(2*i+1) / (2*i+1)
R_n(x) = x * (x^2)^n / (1-x^2)
P_n    = 16*S_n(1/5) - 4*S_n(1/239)
E_n    = 16*R_n(1/5) + 4*R_n(1/239)
```

`Pi.arctan_bound` proves the geometric majorant for `0 ≤ x < 1`.
`Pi.bounds` authenticates `P_n-E_n ≤ Real.pi ≤ P_n+E_n` for every `n`,
including zero. Reconstruction uses both signs correctly: the second
arctangent is subtracted, so its upper cut contributes to π's lower cut.
`Pi.enclosure` transports these cuts through exact outward comparisons.
`Pi.error_le` bounds the radius by `4/2^n`; `Pi.width_le` proves
that order `k+4` gives analytic width at most `2^(-(k+1))`.

For exp(1), `Elementary/ExpLog.lean` uses `Real.exp_bound` from
`Analysis/Complex/Exponential.lean`. Its rational formulas are

```
P_n = sum (i < n), 1/i!
E_n = (n+1)/(n!*n), n > 0.
```

`ExpOne.bounds` and `ExpOne.enclosure` authenticate both cuts. The argument
is exactly one, so reduction and reconstruction are the identity. The positive
order premise is essential; the formula at zero is not a valid remainder.
`ExpOne.error_le` uses `Nat.factorial_mul_pow_le_factorial` to prove
`E_(n+1) ≤ 2/2^n`. `ExpOne.width_le` proves that order `k+4` gives analytic
width at most `2^(-(k+1))`, reserving half the requested width for rounding.

The existing `Experiment/PntExpPoint.lean` and `PntExpNegative.lean` already
use exponential remainders plus `Real.exp_nat_mul` for fixed source families.
Their lookup tables do not establish an arbitrary-order point provider.
`Experiment/PntPiPoint.lean` authenticates its fixed bound with
`Real.pi_lt_d2`; that useful theorem is not a precision schedule.
The new source proofs do not import the experiment registry or source tables.

## Minimal runtime certificate and replay obligation

For each of these fixed formulas, a compact certificate needs a source/version
tag, requested `k`, approximation order `n`, and two finite dyadic endpoints.
The reduction arguments and reconstruction coefficients are fixed by the
source tag; they need not be supplied as untrusted variable fields. The
remainder witness can be its exact formula at `n`, recomputed by the checker.
An implementation may store intermediate sums, rational remainders, or a
division trace for efficient replay, but each such field adds an equality
obligation against the formula above. It cannot certify its own value.

The runtime owner chooses the concrete names and encoding. Its accepted
certificate must establish:

1. Exact source identity and version, and equality of the certificate's
   requested precision with the request. The exp source is `Real.exp 1`, not
   general exp at an unchecked argument.
2. Positive exp order; valid exact arithmetic denominators and recomputed
   centers/remainders.
3. Both exact outward inequalities `lower ≤ P_n-E_n` and
   `P_n+E_n ≤ upper`, plus `upper-lower ≤ 2^(-k)`.
4. Finite admitted endpoints and successful checked interval construction.
5. Preflighted approximation order, integer work/size, allocation, endpoint
   height/alignment/precision, and literal replay limits on arbitrary inputs.

The companion must connect successful checker output to these source
theorems by exact rational casts and dyadic semantics, then quote that theorem
with the *same* source, endpoints and precision. The source theorem's premises
are exact arithmetic facts, never the desired named-real containment fact.
Neither a Boolean returned by compiled evaluation nor a quoted unchecked
endpoint is a proof.

## Remaining integration and verification

The analytic width estimate is not the full effective provider contract.
That contract must prove a computable resource envelope makes production and
literal replay succeed for each `k`, including integer intermediate sizes and
endpoint limits. Rounding on the `2^(-(k+2))` grid contributes at most two
grid units, provided its per-cut rounding error is proved. Generic rejection
of insufficient resources must remain distinct from mathematical failure.

The next runtime-dependent tranche is the cast/rounding bridge and soundness
of the concrete #10334 checker, followed by its full resource/progress proof.
Required tests then include wrong subjects/versions/precision, altered sums
or remainders, either inward cut, malformed payloads, zero and insufficient
budgets, and unavailable precision requests. Producer and executable checker
measurements belong to HexInterval; literal proof reconstruction and fresh
kernel-build measurements belong here. OrderedFn source registration is
downstream and must bind these exact theorems.

## Source-proof verification

`bench/HexIntervalMathlib/Constants/Precision{2,8,16}.lean` imports the public
umbrella and replays both outward cuts with ordinary `norm_num` proofs. Each
fixture has width exactly `2^(-k)`, proves `π-4<0` and `2<exp(1)<3`, and
checks the theorem axiom sets against `{propext, Classical.choice, Quot.sound}`.
The smallest probe also demonstrates why the exp theorem must reject order
zero: its formal zero-order cuts would be `[0,0]`. The largest probe audits
every public source theorem, including the two width schedules.

`scripts/oracle/interval_constants_arb.py` reads the exact cuts from these
Lean declarations and checks that independently computed 256-bit Arb balls
lie strictly inside them. It checks each fixture's requested width separately.
CI uses the existing python-flint 0.9.0 pin and existing conformance job.
These checks validate numerical source fixtures, not a generated runtime
certificate or its resource behavior.

`scripts/bench/interval_constants_sweep.py --shared-host` uses the shared
fresh-module runner: four retained adjacent AB/BA pairs per precision,
matched public-import baselines, a leased CPU, source/toolchain/host provenance,
compiler output, artifact sizes, and axiom sets. Its 60-second fresh-build
ceiling is an operational host-specific bound. There is no compiled producer
or executable checker in this analytic slice to time; those evidence tracks
remain assigned to the #10334 runtime tranche. No performance claim about a
complete provider follows from these source-proof measurements.
