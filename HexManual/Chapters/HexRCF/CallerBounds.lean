/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import VersoManual

public import HexRCF
public import HexRCF.RealCoefficients
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import HexRealClosure
public import HexSignDet
public import HexSignDetMathlib.SelectedProducer
public import HexSignDetMathlib.CompletionProducer
public import HexSignDetMathlib.TableProducer
public import HexSignDetMathlib.ReencodingProducer
public import HexSignDetMathlib.ReencodingRefinement
public import HexSignDetMathlib.ThomReencoding
public import HexSignDetMathlib.ThomRoots
public import HexRationalFn
public import HexOrderedFn.Infinitesimal
public import HexSignDetMathlib.ComparisonProducer
public import HexSignDetMathlib.Convert
public import HexRealAlgebraicMathlib.FieldSign
public import HexRealClosureMathlib.LocalSample

public import HexSignDetMathlib.QueryHandle

public import HexSignDetMathlib.RootList

public section

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Hex Hex.RCF.RealCoefficients

#doc (Manual) "Caller-supplied finite bounds" =>
%%%
tag := "hex-rcf-registered-bounds"
%%%

The optional import also accepts a caller's registered closed real subject.
A {name}`Hex.RCF.RealCoefficients.Registration` contains an executable
approximation and a separate containment theorem for that exact subject.
The `rcf_constant` attribute registers its declaration. Registrations persist
beyond sections and through imports. Subjects match by
reducible definitional equality; duplicate matches among used subjects are
rejected. Unused providers are not evaluated or included in the certificate.
A registered whole expression is tried before its arithmetic constituents.
In a Lean module, mark the registration and its computational definitions
`@[expose]` so their frozen-result equalities reduce in the ordinary kernel.
A consuming module also needs `meta import` of the caller's registration
module to execute its approximation.
The callback must be total and executable, and its returned literal must be
reducible by the ordinary kernel. Registration checks its declaration's type;
it does not execute or establish those computational properties at import time.
Divisors inside a registered expression must themselves be closed reals or
rationals. Divisions depending on an internal binder, or over another carrier,
are unsupported; their variables are never exported as closed source guards.

This example uses the existing theorem that a sine lies in `[-1,1]`. The
caller supplies that fixed bound; the tactic does not construct an analytic
approximation procedure. The bound suffices for a square plus `2 + sin 1`.

```lean
open Hex.OrderedFn.Oracle

private def callerBounds (_ : Rat) : Bounds := ⟨-1, 1, by decide⟩

private theorem callerContainment
    (δ : Rat) (_ : 0 < δ) :
    Contains (callerBounds δ) (Real.sin 1) := by
  simpa [Contains, callerBounds] using
    And.intro (Real.neg_one_le_sin 1) (Real.sin_le_one 1)

@[rcf_constant] private def callerRegistration :
    Registration (Real.sin 1) where
  version := 1
  approximation := callerBounds
  containment := callerContainment

example : ∀ x : ℝ, x ^ 2 + 2 + Real.sin 1 > 0 := by rcf
example : ∃ x : ℝ,
    x = Real.sin 1 ∧ -2 < x ∧ x < 2 := by rcf

example : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 2 + Real.sin 1 > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.sqrt 2 + Real.sin 1) > 0 := by rcf
```

Registered bounds also compose with unregistered algebraic coefficients.
For the last two examples, the algebraic approximation proposes rational
endpoints for the selected positive square root. The existing exact algebraic
frontend proves containment by literal replay before those bounds enter the
finite arithmetic. The supplied sine bound then separates the original
divisor from zero. The frozen proof does not rerun algebraic approximation or
root production. Whole-subject registrations still take priority. This
composition remains bounded: an unsupported field presentation or an
unresolved combined enclosure is a failure, not a completeness claim.
Rational values keep exact bounds when the rational frontend recognizes them,
including perfect-square radicals. Within one preparation, repeated identical
closed expressions reuse their checked enclosure proof; the original divisor
checks still run before proof search. Distinct aliases do not automatically
share an enclosure or supply an equality proof.

The finite path requests width `1/16` once. The actual width here is `2`;
containment does not assert that the request was met. A requested-width theorem
has the separate type
{name}`Hex.OrderedFn.Oracle.ApproximationWidth`, applied to
{name}`Hex.OrderedFn.Oracle.Approximation.ofConstant` with `callerBounds`.
Convergence and relative transcendence are separate hypotheses for total
search. This fixed bound makes no such claim. Finite proofs from containment
need neither hypothesis.

For the named constants below, the caller uses existing Mathlib theorems
to supply `π ∈ [3, 63/20]` and `exp 1 ∈ [5/2, 11/4]`. These bounds suffice
for the displayed finite proofs, including the original nonzero divisor
`4 − π`. The imports are `Mathlib.Analysis.Real.Pi.Bounds` and
`Mathlib.Analysis.Complex.ExponentialBounds`. These constant callbacks do
not certify arbitrary requested widths or a convergent search.

```lean
private def callerPiBounds (_ : Rat) : Bounds :=
  ⟨3, mkRat 63 20, by norm_num⟩
private def callerExpBounds (_ : Rat) : Bounds :=
  ⟨mkRat 5 2, mkRat 11 4, by norm_num⟩

@[rcf_constant] private def callerPi :
    Registration Real.pi where
  version := 1
  approximation := callerPiBounds
  containment δ _ := by
    norm_num [Contains, callerPiBounds]
    constructor
    · exact Real.pi_gt_three.le
    · linarith [Real.pi_lt_d2]

@[rcf_constant] private def callerExp :
    Registration (Real.exp 1) where
  version := 1
  approximation := callerExpBounds
  containment δ _ := by
    norm_num [Contains, callerExpBounds]
    constructor
    · linarith [Real.exp_one_gt_d9]
    · linarith [Real.exp_one_lt_d9]

example : ∀ x : ℝ, x ^ 2 > Real.pi - 4 := by rcf
example : ∀ x : ℝ, x ^ 2 + Real.exp 1 > 2 := by rcf
example : ∃ x : ℝ,
    x = Real.exp 1 ∧ 2 < x ∧ x < 3 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + 1 / (4 - Real.pi) > 0 := by rcf

section
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

example : ∀ x : ℝ,
    x ^ 2 + Real.pi -
      Real.sqrt (Real.sqrt 2) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + Real.exp 1 -
      Real.sqrt (3 + Real.sqrt 2) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + Real.pi -
      (3 + Real.sqrt 2) ^ (1 / 3 : ℝ) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + Real.pi - Real.sqrt
      (1 / (4 + Real.sqrt 2)) > 0 := by rcf
example : ∀ x : ℝ,
    x ^ 2 + 1 /
      (Real.pi - Real.sqrt (Real.sqrt 2)) > 0 := by rcf

@[rcf_constant] private def callerInner :
    Registration (Real.sqrt 2) where
  version := 1
  approximation _ := ⟨1, 2, by decide⟩
  containment _ _ := by
    simp only [Contains]
    constructor
    · norm_num [Real.le_sqrt]
    · norm_num [Real.sqrt_le_iff]

example : ∀ x : ℝ,
    x ^ 2 + Real.pi -
      Real.sqrt (Real.sqrt 2) > 0 := by rcf
end

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 0 / (Real.pi - Real.pi) ≥ 0 := by rcf
```

These additional examples combine supplied bounds with square and cube roots
of algebraic bases. The real-power example takes the positive cube root of
`3 + √2`; its exact source authentication uses that non-rational base rather
than a rational-root shortcut. Before proposing an enclosure, the frontend
authenticates the source and its selected embedding, checking every original
divisor inside the base. Ordinary literal replay then proves containment in
the proposed rational interval. The mixed-division example also checks that the combined
bounds separate its original divisor from zero. Neither step treats a registered
constant as an executable ordered field, and frozen replay does not repeat
the algebraic search. An unsupported base, exhausted admission or unresolved
divisor remains a failure of this bounded finite path. The final registration
also illustrates a registered subterm inside an algebraic root. The root must
still authenticate exactly without using the subterm provider's bounds;
registering π does not admit `Real.sqrt Real.pi`. The finite certificate retains
and checks the matched provider's frozen subject, request and version.
A registration for the whole coefficient takes precedence over its subterms.

All original divisors are checked before cancellation, coefficient abstraction
or proof search. Thus even an erased division by `sin 1 - sin 1` is invalid.
The supplied interval also cannot certify that `sin 1` is nonzero: a bound
containing zero proves neither equality to zero nor a strict sign.

```lean
/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 2 + Real.sin 1 +
      0 / (Real.sin 1 - Real.sin 1) > 0 := by
  rcf

/-- error: rcf: original closed divisor remains unresolved in supplied bounds -/
#guard_msgs in
example : ∀ x : ℝ,
    x ^ 2 + 2 + Real.sin 1 + 0 / Real.sin 1 > 0 := by
  rcf
```

For direct proof construction, {name}`Hex.RCF.RealCoefficients.Finite.prepare`
returns the shared source formula/equivalence, fixed coefficient order, frozen
bounds and checked original guards. {name}`Hex.RCF.RealCoefficients.Finite.build`
constructs a proof of the source using the frozen facts and checked alias
hypotheses, then transports it to the shared schema. Unrelated caller
hypotheses are excluded from this proof search.
{name}`Hex.RCF.RealCoefficients.Finite.check` checks it and transports it back to
the original goal. The certificate binds the source, used registry/provider versions,
precision request, coefficient subjects and guards. Checking validates ordinary
proofs and frozen callback identities; it does not repeat approximation or root
search. Source coefficients and guards retain the same selected real values.

The existing algebraic handlers retain their documented inputs, including
registered small algebraic composites. Before exact reification, a registered
whole subject outside the exact scalar syntax or exponent envelope selects the
supplied frontend. Once an eligible backend starts, budget and replay failures
stop dispatch. Only providers used by source coefficients and original guards
are evaluated and bound into finite evidence.

This finite path uses nonlinear proof reconstruction from the supplied bounds,
with conjunctions and a proposed ordinary real existential witness. The current
witness is the first collected coefficient, or zero when there are none; it
does not search for witnesses. The precision request stays at `1/16`, without
refinement. It may fail
on a true statement, and such a failure is an unresolved proof attempt, not a
false verdict. False and unresolved goals can both fail proof reconstruction;
this path does not distinguish them by a decision verdict.
Lean's execution limits can also interrupt it. Failures restore
caller state and stop handler dispatch. The existing algebraic cell solver
continues to handle its documented inputs. Registrations alone do not complete
the general coefficient-field decision procedure.

The CI-built examples in `bench/HexRCF/ProofProbe/Registered/` also prove
`∀ x, x² > π-4`, `∀ x, x²+exp 1 > 2`,
`∃ x, x=exp 1 ∧ 2<x ∧ x<3`, and the guarded
`∀ x, x²+1/(4-π)>0`. Their callers supply coarse bounds
`π ∈ [3,63/20]` and `exp 1 ∈ [27/10,14/5]`, with containment proved from
Mathlib's existing numerical inequalities. These are test registrations;
the optional library supplies no such providers. All four quoted theorem
dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`.

CI builds this four-proof module through `HexRCFProofProbe`. Its guarded axiom
reports check the ordinary-kernel dependency surface on every PR. These examples
show that the coarse caller enclosures suffice without root/cell construction;
they make no timing, convergence or completeness claim.

