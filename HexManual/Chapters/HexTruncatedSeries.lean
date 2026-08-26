/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexTruncatedSeriesMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexTruncatedSeries: fixed-precision series" =>
%%%
tag := "hex-truncated-series"
%%%

# Introduction
%%%
tag := "hex-truncated-series-intro"
%%%

`HexTruncatedSeries` provides executable power series whose precision is
fixed in the type. A value of precision `n` stores exactly the coefficients
below degree `n`; every operation discards higher terms. This makes the
precision contract explicit while keeping the representation suitable for
bounded multiplication and Newton iteration.

The computational library is Mathlib-free and depends only on
{ref "hex-basic"}[`HexBasic`]. It supplies arithmetic, precision changes,
inverse, square root, exponential, logarithm, composition, and reversion.
`HexTruncatedSeriesMathlib`, described in
{ref "hex-truncated-series-mathlib"}[the correspondence section], identifies
the representation with Mathlib power series modulo `X ^ n`.

# Representation and arithmetic
%%%
tag := "hex-truncated-series-representation"
%%%

{docstring Hex.TSeries}

{docstring Hex.TSeries.coeff}

Coefficient access is total: an index outside the represented precision
reads as zero. Tabulation and extensionality are the main constructor and
equality principle.

{docstring Hex.TSeries.ofFn}

{docstring Hex.TSeries.ext}

The usual notation is available for addition, subtraction, multiplication,
and powers. Constants and the indeterminate have explicit constructors, and
`mulUpTo` computes only the requested prefix.

{docstring Hex.TSeries.C}

{docstring Hex.TSeries.X}

{docstring Hex.TSeries.mulUpTo}

This finite geometric series demonstrates that multiplication is always
interpreted modulo the precision.

```lean
open Hex Hex.TSeries

def geometric : TSeries Int 6 :=
  ofFn fun _ => 1

#guard (geometric * (1 - X)).coeff 0 == 1
#guard (geometric * (1 - X)).coeff 4 == 0
```

# Precision-changing operations
%%%
tag := "hex-truncated-series-precision"
%%%

Truncation and zero extension change the precision in the type. Multiplying
or dividing by a power of `X` shifts coefficients; division is partial
because discarded low coefficients must be zero. `valuation?` reports the
first represented nonzero coefficient and returns `none` for the zero
truncated series.

{docstring Hex.TSeries.truncate}

{docstring Hex.TSeries.extend}

{docstring Hex.TSeries.divXPow?}

{docstring Hex.TSeries.valuation?}

```lean
open Hex Hex.TSeries

def shifted : TSeries Int 6 :=
  ofFn fun i => if i = 2 then 7 else 0

#guard shifted.valuation? == some 2
#guard
  (shifted.divXPow? 2).map (fun q => q.coeff 0) ==
    some 7
```

Differentiation loses one coefficient of precision. Integration adds a
zero constant coefficient and requires only the finitely many natural
inverses needed at the chosen precision.

{docstring Hex.TSeries.deriv}

{docstring Hex.TSeries.integrate}

{docstring Hex.TSeries.NatInverses}

# Newton operations
%%%
tag := "hex-truncated-series-newton"
%%%

The main algorithms accept algebraic witnesses rather than searching the
coefficient ring. Optional wrappers use `UnitOps` when executable unit
detection is available. Bounded variants expose the prefixes used by Newton
doubling, and their agreement theorems connect those implementations to the
full operations.

{docstring Hex.TSeries.UnitOps}

{docstring Hex.TSeries.invOfUnit}

{docstring Hex.TSeries.inv?}

{docstring Hex.TSeries.invOfUnit_mul}

Square-root lifting takes a chosen constant root `r` and an inverse of
`2 * r`; it proves both the square equation and uniqueness above that root.

{docstring Hex.TSeries.sqrtOfRoot}

{docstring Hex.TSeries.sqrtOfRoot_sq}

{docstring Hex.TSeries.sqrt_unique}

Formal exponential and logarithm use `NatInverses R (n - 1)`, so the core
API states exactly which scalar divisions are required rather than assuming
characteristic zero.

{docstring Hex.TSeries.exp}

{docstring Hex.TSeries.log}

{docstring Hex.TSeries.log_exp}

{docstring Hex.TSeries.exp_log}

# Composition and reversion
%%%
tag := "hex-truncated-series-composition"
%%%

Composition uses a Brent--Kung implementation and requires a zero constant
coefficient for its algebraic laws. Reversion lifts an inverse of the linear
coefficient by Newton iteration. A direct Lagrange implementation provides
an independent route when the required natural inverses exist.

{docstring Hex.TSeries.comp}

{docstring Hex.TSeries.comp_spec}

{docstring Hex.TSeries.revOfUnit}

{docstring Hex.TSeries.revOfUnit_comp}

{docstring Hex.TSeries.revLagrange}

{docstring Hex.TSeries.revLagrange_eq}

Here `x - x²` has invertible linear coefficient. Both reversion algorithms
produce the same series, and substitution recovers `x` at precision six.

```lean
open Hex Hex.TSeries

def reversible : TSeries Rat 6 :=
  X - X ^ 2

#guard
  comp reversible (revOfUnit reversible 1) == X
#guard
  revLagrange reversible 1 ==
    revOfUnit reversible 1
```

# The Mathlib correspondence
%%%
tag := "hex-truncated-series-mathlib"
%%%

Everything above is executable and Mathlib-free. The companion installs
Mathlib's `CommRing` API using those same operations and defines coefficient
truncation from `PowerSeries R` as a surjective ring homomorphism.

{docstring HexTruncatedSeriesMathlib.ofPowerSeries}

{docstring HexTruncatedSeriesMathlib.ofPowerSeriesHom}

Its kernel is the ideal generated by `X ^ n`, giving the headline quotient
equivalence.

{docstring HexTruncatedSeriesMathlib.ker_ofPowerSeriesHom}

{docstring HexTruncatedSeriesMathlib.quotEquiv}

The correspondence covers powers, precision changes, differentiation,
inverse, substitution, reversion, exponential, and logarithm. Square roots
have a direct existence-and-uniqueness theorem because Mathlib has no
matching power-series square-root operation with a supplied root.

{docstring HexTruncatedSeriesMathlib.deriv_ofPowerSeries}

{docstring HexTruncatedSeriesMathlib.ofPowerSeries_invOfUnit}

{docstring HexTruncatedSeriesMathlib.ofPowerSeries_subst}

{docstring HexTruncatedSeriesMathlib.ofPowerSeries_substInvOfIsUnit}

{docstring HexTruncatedSeriesMathlib.ofPowerSeries_exp}

{docstring HexTruncatedSeriesMathlib.ofPowerSeries_logOf}

{docstring HexTruncatedSeriesMathlib.exists_unique_sq}

# Cross-references
%%%
tag := "hex-truncated-series-cross-references"
%%%

* {ref "hex-basic"}[`HexBasic`] supplies the kernel-reducible vector and
  fold helpers used by the fixed-length representation and convolution.
* `HexTruncatedSeriesMathlib` is the proof boundary: it imports Mathlib,
  while `HexTruncatedSeries` and executable consumers do not.
* Polynomial reversal and fast polynomial division belong above this
  library in the dependency graph; the truncated-series API deliberately
  names no polynomial representation.
