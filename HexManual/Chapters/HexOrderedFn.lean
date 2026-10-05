/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexOrderedFnMathlib
import HexOrderedFnMathlib.Tests
import HexOrderedFnMathlib.LiouvilleTests

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexOrderedFn: real constants and infinitesimals" =>
%%%
tag := "hex-ordered-fn"
%%%

# Ordered rational-function extensions

`HexOrderedFn` orders exact rational functions in a new indeterminate. The
indeterminate can represent a positive infinitesimal, or a real constant
with caller-supplied rational approximations. Arithmetic uses the canonical
fractions from {ref "hex-rational-fn"}[HexRationalFn]; normalization and
equality remain exact. The computational library is Mathlib-free. Import
`HexOrderedFnMathlib` for the interpretation and order proofs.

The two constructions answer different questions. An infinitesimal is
positive and smaller than every positive predecessor coefficient. A real
constant is interpreted in `ℝ`: containment proofs justify its finite sign
checks, while narrowing bounds and relative transcendence justify a total
ordered field. At each real extension, relative transcendence means that
no nonzero polynomial over the entire predecessor field vanishes at the
new constant.

# Positive infinitesimals

For a nonzero fraction `P/Q`, the infinitesimal sign is the product of the
signs of the lowest nonzero coefficients of `P` and `Q`. The denominator
coefficient matters even though the denominator is monic. Zero is detected
from the canonical numerator without calling the predecessor sign.

{docstring Hex.OrderedFn.Infinitesimal.sign}

{docstring Hex.OrderedFn.Infinitesimal.compare}

Opening the infinitesimal scope enables comparisons on `RationalFn K`.
The snippets here use `import HexOrderedFnMathlib`. For computation alone,
use `import HexOrderedFn` and omit the local Mathlib dictionary selection.
Here the denominator `ε-1` and its inverse are both negative:

```lean
open Hex Hex.OrderedFn
namespace OrderedFnInfinitesimals
open scoped Hex.OrderedFn.Infinitesimal
attribute [local instance 2000]
  Field.toGrindField

def epsilon : RationalFn Rat := RationalFn.X

#guard 0 < epsilon
#guard epsilon < RationalFn.C (1/100 : Rat)
#guard Infinitesimal.sign orderSign
  (1 / (epsilon - 1)) = -1
#guard Infinitesimal.compare orderSign
  epsilon (RationalFn.C (1 : Rat)) = .lt
end OrderedFnInfinitesimals
```

The explicit `sign` and `compare` functions accept a predecessor sign
function. The companion proves the order laws when that function agrees
with the predecessor's order. It does not install a global order on every
rational-function carrier.

With the companion import, that same scope also installs its proved
`LinearOrder`, `IsStrictOrderedRing` and core `Lean.Grind.OrderedRing`
instances. These make ordinary ordered-field lemmas available on the
executable carrier.

The examples select `Field.toGrindField` locally before forming their
carriers. This keeps the coefficient arithmetic dictionary consistent with
the companion's Mathlib field. When transporting fractions formed with the
core rational dictionary, `HexRationalFnMathlib.ratField_eq` transports to
the companion dictionary. The generic
`HexRationalFnMathlib.coreField_eq` identifies the field induced on a
rational-function carrier with its original core field.

# Successive infinitesimals

At a second level, coefficients are themselves rational functions in the
first infinitesimal. The new indeterminate `δ` is smaller than every
positive element of the preceding field, including every natural power
of `ε`:

```lean
namespace OrderedFnSuccessive
open scoped Hex.OrderedFn.Infinitesimal
attribute [local instance 2000]
  Field.toGrindField

abbrev First := RationalFn Rat
abbrev Second := RationalFn First

def epsilon : First := RationalFn.X
def delta : Second := RationalFn.X

#guard 0 < delta
#guard delta < RationalFn.C (epsilon ^ 3)

example (n : ℕ) :
    delta < RationalFn.C (epsilon ^ n) :=
  Infinitesimal.X_lt_pow n

example (n : ℤ) : (n : First) < epsilon⁻¹ :=
  Infinitesimal.intCast_lt_inv_X n
end OrderedFnSuccessive
```

`RationalFn.C` embeds a predecessor value; `RationalFn.X` introduces
the current level's indeterminate. These two operations distinguish `ε`
from `δ` even though both are written as `X` in their own fields.

# Exact bounds and finite signs

{name}`Hex.OrderedFn.Oracle.Bounds` stores rational lower and upper
endpoints with a proof that they are ordered. It does not itself assert
containment of a real value. Addition and four-endpoint multiplication
compute exact enclosures; `Bounds.div?` requires the denominator bound
to exclude zero.

{docstring Hex.OrderedFn.Oracle.Bounds.sign?}

{docstring Hex.OrderedFn.Oracle.Bounds.exactSign?}

{name}`Hex.OrderedFn.Oracle.Approximation` contains two procedures:
one bounds a predecessor coefficient, and one bounds the new constant.
Each receives a requested rational width. `Approximation.ofConstant`
starts over rational coefficients using exact singleton bounds.

{docstring Hex.OrderedFn.Real.enclose}

{docstring Hex.OrderedFn.Real.sign?}

Consider a constant known to lie between `7/5` and `3/2`. Those bounds
separate `X-1` and `X-2` from zero, but leave `X²-2` unresolved. A finite
query can use the same bounds at every trial:

```lean
namespace OrderedFnFinite
attribute [local instance 2000]
  Field.toGrindField
open Oracle

def source : Approximation Rat :=
  .ofConstant (fun _ =>
    ⟨7/5, 3/2, by norm_num⟩)

def linear (q : Rat) : RationalFn Rat :=
  RationalFn.ofPoly (#p[-q, 1])

#guard Real.sign? source (linear 1) 1 =
  some 1
#guard Real.sign? source (linear 2) 1 =
  some (-1)
#guard Real.sign? source
  (RationalFn.ofPoly (#p[-2, 0, 1])) 4 = none

theorem source_correct : ApproximationCorrect
    (Rat.castHom ℝ) (_root_.Real.sqrt 2) source :=
  SemanticTests.sqrt_correct

example : (1 : Int) =
    sgn (Real.eval (Rat.castHom ℝ)
      (_root_.Real.sqrt 2)
      (linear 1)) :=
  (Real.sign?_sound source_correct _ 1
    (by decide +kernel)).1
end OrderedFnFinite
```

The computation needs only endpoint data; its mathematical conclusion
needs a containment proof for this provider, subject and embedding.
Here `source_correct` reuses the companion test's proof for `Real.sqrt 2`.
That algebraic subject is suitable for finite checks, but cannot supply a
transcendental registration. Fuel exhaustion returns `none`, as does a
denominator that cannot be separated from zero. A zero-containing interval
does not prove a zero value; an exact singleton zero can do so.

{docstring Hex.OrderedFn.Real.sign?_sound}

The theorem also proves that the normalized denominator evaluates to a
nonzero value. A source expression may have additional divisor conditions
that normalization removed. For example, formal cancellation makes
`(X-2)/(X-2)` equal to one, but at the real subject `2` the original
division is `0/0`. Expression consumers must retain the original divisor
hypotheses when interpreting that cancellation.

# Registered real extensions

{name}`Hex.OrderedFn.Real.Registration` fixes the provider together with
termination proofs for every sign and approximation query. The companion's
{name}`Hex.OrderedFn.Real.Valid` supplies sufficient semantic hypotheses:
containment, requested-width guarantees, and transcendence relative to the
chosen predecessor embedding. Its `registration` constructor derives the
termination proofs for the actual refinement search.

To extend an already ordered predecessor field, also require the chosen
embedding `ι` to be strictly monotone. `Valid` does not include that
condition: it justifies the real interpretation's order, which can differ
from a previously chosen order on the predecessor. `Extension.C_lt` uses
`StrictMono ι` to prove agreement on embedded coefficients.

{docstring Hex.OrderedFn.Real.Extension.C_lt}

{docstring Hex.OrderedFn.Real.registration}

{name}`Hex.OrderedFn.Real.Extension` wraps a canonical fraction with this
fixed registration. `Extension.C` embeds a predecessor coefficient and
`Extension.X` represents the registered real constant. The wrapper keeps
its real order when used as the coefficient field for an infinitesimal.

{docstring Hex.OrderedFn.Real.Extension.sign}

{docstring Hex.OrderedFn.Real.Extension.approx}

For a nonzero formal fraction, sign refinement narrows bounds for both
numerator and denominator until each has a strict sign. Formal zero
returns immediately. The termination proofs erase from compiled execution;
they do not impose a fuel limit. Positive approximation requests return
bounds of at most the requested width. Nonpositive requests instead ask
for width one, while still preserving containment.

Each trial computes fresh coefficient and constant bounds at precision
`2^(-n)`. At a further real level, coefficient approximations themselves
run refinement searches; their cost depends on the caller's providers.

A further real registration uses `Extension.approximation` to obtain bounds
for its predecessor coefficients. Each new real constant needs relative
transcendence over that entire predecessor field. Separate transcendence
of two constants over the rationals does not establish this condition.
The fixture's `LiouvilleTests.second_valid` constructs such a second
registration under explicit hypotheses on its new constant and provider.
For a fixed relatively transcendental subject, containment proofs for both
providers and the same embedding suffice to preserve order through
`Extension.transport_lt`.

# The Mathlib correspondence

The infinitesimal embedding maps canonical fractions into the
lexicographically ordered Hahn field with integer exponents. Its leading
coefficient order agrees with the executable scan. The public theorems
`Infinitesimal.X_pos` and `X_lt_C` establish positivity and the comparison
with every positive predecessor coefficient; `X_lt_pow` supplies the
successive-level law used above. `Infinitesimal.towerEmbed` and
`towerEmbed_lt` identify the two-level field with its iterated Hahn model.

{docstring Hex.OrderedFn.Infinitesimal.embed}

{docstring Hex.OrderedFn.Infinitesimal.mapHom_sign}

Coefficient transport preserves signs and order under an ordered field
embedding. The Hahn model is not real closed: an integer-exponent series
cannot provide a square root of its exponent-one monomial. Algebraic
adjunctions belong to the
[real-closure contract](https://github.com/kim-em/hex-dev/blob/main/SPEC/Libraries/hex-real-closure.md),
whose full tower implementation and acceptance are separate obligations.

For a registered real extension, `Extension.evalHom` maps fractions into
`ℝ` and is injective under relative transcendence. Containment proves that
the executable sign and order agree with this interpretation. The companion
supplies Mathlib field and order laws for the same computational arithmetic.

{docstring Hex.OrderedFn.Real.Extension.sign_eq}

{docstring Hex.OrderedFn.Real.Extension.approx_contains}

A successful finite trial can also prove the total sign using
`Extension.sign_of_attempt`. This lets the kernel check a supplied finite
success without reducing the unbounded search or its termination proof.

The existing test-local Liouville provider illustrates a complete real
registration: rational partial sums and tail bounds have proved containment
and requested width, and `liouvilleNumber 2` has proved transcendence. The
fixture defines `positive = X-5/4`, `negative = X-2` and their quotient.
Its `preparedPositive` stores an explicit normalized fraction. A finite
successful trial proves that prepared value's total sign from containment.
The fixture identifies the arithmetic-built `positive` with it using
`positive_eq`, proved through injective real evaluation under transcendence.

For an already registered carrier, `Extension.OrderValid` requires
containment and relative transcendence; it does not request the width
guarantee again. Install the real order structures as local instances:

```lean
namespace OrderedFnLiouville
attribute [local instance 2000]
  Field.toGrindField
open Hex.OrderedFn.Real
open Hex.OrderedFn.LiouvilleTests

example :
    Extension.sign preparedPositive = 1 :=
  Extension.sign_of_attempt source_correct _
    (n := 2) (by decide +kernel)

local instance : LinearOrder E :=
  Extension.linearOrder
    ⟨Rat.castHom ℝ, liouvilleNumber 2,
      source_correct, transcendence⟩

local instance : IsStrictOrderedRing E :=
  Extension.strictOrderedRing
    source_correct transcendence

local instance : Lean.Grind.OrderedRing E :=
  Extension.orderedRing
    source_correct transcendence

example : (0 : E) < positive :=
  (Extension.sign_pos_iff source_correct
    transcendence positive).mp positive_sign

example : Extension.sign quotient = -1 :=
  quotient_sign
end OrderedFnLiouville
```

This fixture is imported explicitly from
`HexOrderedFnMathlib.LiouvilleTests`; it is not a bundled analytic provider
in the ordinary library umbrella. The library supplies no providers for
π or e. The companion's compiled `hexorderedfn_liouville_test` exercises
the total search, approximation and a subsequent infinitesimal extension.

The real-closure specification prescribes order-preserving predecessor
embeddings and stages in the order real constants, infinitesimals, then
algebraic extensions. A positive infinitesimal over the rationals has no
order-preserving real embedding. A later real registration could choose a
different real interpretation of the formal rational functions, but its
order would not extend that infinitesimal order. It therefore cannot serve
as a subsequent stage with the prescribed order preservation. General
tower-building and ordinary-real realization remain separate obligations.
