/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRealClosure
import HexRealClosureMathlib.TowerRoots
import HexRealClosureMathlib.RootCollection

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexRealClosure: selected roots and algebraic towers" =>
%%%
tag := "hex-real-closure"
%%%

# Extending an ordered coefficient context

`HexRealClosure` computes roots and builds finite algebraic towers over
an ordered coefficient context. A root carries its selected embedding;
a value carries the immutable context in which its arithmetic is valid.
The library combines the polynomial kernels, {ref "hex-sturm"}[Sturm queries],
{ref "hex-sign-det"}[sign determination] and
{ref "hex-ordered-fn"}[ordered rational-function extensions].

Import `HexRealClosure` for the Mathlib-free computational API. The
`HexRealClosureMathlib` umbrella supplies the base-model proofs; the tower
root and collection theorems below additionally require
`HexRealClosureMathlib.TowerRoots` and `HexRealClosureMathlib.RootCollection`.
Those semantic modules belong to the `HexQuerySemantics` Lake target under
`adapters/` in the development tree. They build in `hex-dev`, but are not
therefore available from a published companion. Both libraries are unreleased;
Tau Ceti belongs only to their Mathlib proof layer.

The API describes finite constructed extensions. It does not identify
raw polynomial quotients with fields, compute multivariate quantifier
elimination, or install an ordinary-real interpretation of a positive
infinitesimal. General finite ordinary-real realization and the full
end-to-end family contract have separate proof requirements.

# Real prefixes, infinitesimals and selected roots

A base starts with rational coefficients, may extend them with registered
real constants, and may then adjoin successive positive infinitesimals.
A real constant has a caller-supplied rational bound provider. Its progress
witnesses refer to the exact source formed from that provider and the
predecessor's bounds. Semantic validity requires containment, narrowing
widths and relative transcendence over the entire predecessor field.
No bundled provider for π or e is supplied.

{docstring Hex.RealClosure.BaseContext.RealContext.constant}

The real prefix ends before the first infinitesimal. The base chain has
no constructor adding a real constant after an infinitesimal. Algebraic
extensions then use validated selected-root descriptors over their actual
predecessor contexts.

```lean
open Hex Hex.RealClosure
namespace TowerBase

def registry : BaseContext.Registry :=
  fun _ => none

def rationals :=
  BaseContext.Context.real
    (BaseContext.RealContext.rational registry)

def infinitesimal := rationals.infinitesimal

def parent := Tower.Context.base infinitesimal

end TowerBase
```

A `Tower.Context` hides its concrete native coefficient carrier behind
{name}`Hex.RealClosure.Tower.Context.Value`. Use its total `sign`,
`compare` and `equal` operations. Representation equality is not the
criterion for mathematical equality of arbitrary selected-root values.
The semantic companion interprets the supplied operations in an ordered
field and reflects zero; it does not require injectivity of every stored
representative.

# Complete roots and original multiplicities

The generic root API takes a coefficient sign function and a literal
context. Under the companion's coefficient-model laws, it returns the
all-roots case exactly for zero, and a finite list otherwise. A nonzero
constant and a root-free polynomial give an empty finite list.

{docstring Hex.RealClosure.Roots.roots}

Zero extraction and Yun decomposition recover multiplicities from the
original polynomial, before sorting roots across factors. Entries retain
positive multiplicity labels. Squarefree decomposition is an internal
step: a repeated-root input is valid here, unlike a raw Sturm query head.

The following small example reuses the cases checked by the owner's
root-factor suite. The polynomial `X²(X-1)³` has two distinct roots with
multiplicities two and three:

```lean
namespace CompleteRoots

def x : DensePoly Rat :=
  DensePoly.ofCoeffs #[0, 1]

def labels : List Nat :=
  match Hex.RealClosure.Roots.roots
      (Sturm.orderSign : Rat → Int) (7 : Nat)
      (x * x * (x - 1) * (x - 1) * (x - 1)) with
  | .all => []
  | .finite entries =>
    entries.map (·.multiplicity)

#guard labels = [2, 3]
#guard (match Hex.RealClosure.Roots.roots
    (Sturm.orderSign : Rat → Int)
    (7 : Nat) (0 : DensePoly Rat) with
  | .all => true
  | .finite _ => false)

end CompleteRoots
```

The diagnostic operation {name}`Hex.RealClosure.Roots.roots?` exposes
internal producer errors for arbitrary coefficient operations. The ordinary
operation has a diagnostic panic fallback of `.all`, inherited by the
tower and rational wrappers. Outside the coefficient-model laws, this
fallback must not be taken as proof that the input was zero. Use `roots?`
to retain explicit errors. The companion proves that the actual construction
succeeds under its interpretation laws; an example's successful output
cannot discharge that general obligation.

# Native root contexts and coefficient embeddings

{docstring Hex.RealClosure.Tower.Context.roots}

A native root is either a predecessor coefficient point or a selected
root in the child actually returned by adjoining its descriptor. Each
entry keeps the original multiplicity. A point stays in the parent;
a selected root stores the descriptor, child context and selected generator.

Use {name}`Hex.RealClosure.Tower.Root.context` and
{name}`Hex.RealClosure.Tower.Root.value` together. To enter that context,
map predecessor coefficients with {name}`Hex.RealClosure.Tower.Root.embed`.
{name}`Hex.RealClosure.Tower.Root.embedPoly` maps a polynomial's coefficients,
and {name}`Hex.RealClosure.Tower.Root.signAt` evaluates it at the stored root.
`Root.compare` compares roots of the shared input context while keeping
their different child ownership explicit. Its diagnostic panic fallback is
`.eq`; use {name}`Hex.RealClosure.Tower.Root.compare?` to retain errors.
The companion's model laws exclude this fallback.

{docstring Hex.RealClosure.Tower.Context.adjoin}

The low-level selected algebraic carrier represents a polynomial's value
at one root. Its defining polynomial may be reducible. The carrier stores zero canonically,
and every other element carries a checked nonzero sign. The companion derives
zero reflection from the predecessor laws with
{name}`Hex.RealClosure.Algebraic.Element.denote_eq_zero`, so `a ≠ 0` implies
a nonzero value. Nonzero values can still have several stored representatives. The quotient
by the whole defining polynomial need not be a field, so xgcd inversion
modulo that polynomial is insufficient. Inversion uses selected-root tests
and the appropriate cofactor. The semantic proofs justify the actual
operation rather than granting a field instance to raw representatives.

Clean monic definitions allow stored remainder reduction. Non-monic or
unclean definitions retain their raw policy; scaled pseudo-remainders
must not be substituted for value-preserving remainders. This policy changes
representation and costs, while the companion proves value preservation
for the transformations that actually apply.

# Enlargement and live transport

Adding an infinitesimal below an existing algebraic suffix requires
rebuilding that suffix over the extended base. A descriptor, polynomial
or value from the old context does not automatically acquire the new binding.

{docstring Hex.RealClosure.Tower.Context.enlargeWithParameter?}

The result contains the actual conversion and its new parameter. Use
the returned conversion for old values; compose conversions explicitly
for later extensions. Its cached parameter uses the same reconstructed
suffix and does not trigger another reconstruction.

Consumers gathering several live values must include every required
owner, coefficient and root dependency. Preserving one selected value
is weaker than all-live preservation. The merged enlargement and
transport theorems have explicit source/target models and dependency
premises; they do not by themselves construct all arithmetic facts needed
for an arbitrary accepted serialized tower.

# Exact stored data and exploration

Context-bound serialization records the ordered base signature, selected
descriptors and recursively encoded coefficients. This is reconstructible
data, not a decimal approximation of the selected root.

{name}`Hex.RealClosure.Tower.Context.write` and
{name}`Hex.RealClosure.Tower.Context.read` use the exact whole-context binding.
{name}`Hex.RealClosure.Tower.Context.read_write` proves the value roundtrip;
{name}`Hex.RealClosure.Tower.Context.read_stale` proves rejection of a
different binding. Polynomial read/write has its own roundtrip theorem,
{name}`Hex.RealClosure.Tower.Context.readPoly_write`.

A {name}`Hex.RealClosure.Tower.Catalog` resolves previously installed
context handles before reading values. Unknown algebraic signatures reject;
the reader does not manufacture missing progress proofs or roots.
Hash lookup still checks the full literal binding. A successful payload
roundtrip is separate from mathematical certificate acceptance.

For univariate exploration, {name}`Hex.RealClosure.Tower.Sample.family`
orders and deduplicates root handles before constructing sections and open
sectors. Sections and rays reuse their root's cached context; a bounded sector
collects only its two endpoint roots, and the root-free line stays in the input
context. This does not build a shared arithmetic context for the whole family.
{name}`Hex.RealClosure.Tower.Sample.partition` instead collects all boundaries
in one native arithmetic context. Samples retain the coefficient inclusion
and requested sign order. Zero polynomials contribute no boundary, since
their sign is identically zero. The converse, that only zero produces `.all`,
requires the model laws. A diagnostic `.all` or `.eq` fallback would lose
boundaries or merge distinct ones. `Context.collect` also has a diagnostic
panic fallback to an empty collection, which would lose collected boundaries
and invalidate bounded sectors. Use {name}`Hex.RealClosure.Tower.Context.collect?`
to retain failure; {name}`Hex.RealClosure.Tower.Context.collect?_success`
excludes it under the common model laws. The family semantics require the
laws excluding each of these fallbacks. Cell membership,
coverage and sign constancy belong to the companion's family theorems;
a sample data structure alone does not prove these claims. This interface
does not provide full CAD or multivariate coverings.

# The Mathlib correspondence

{name}`Hex.RealClosure.Tower.Model` interprets one native context in a
field with a linear order, binding zero reflection, arithmetic and sign.
The root theorems additionally require ordered-ring laws and real closedness.
The `TowerRoots` development import supplies `Model` and its constructors.
Models are built from lawful base interpretations with
{name}`Hex.RealClosure.Tower.Model.base` and extended at selected roots with
{name}`Hex.RealClosure.Tower.Model.adjoin`. Their hypotheses bind the actual
operations and selected embeddings. A model is a mathematical consumer
hypothesis, not a runtime root-constructor argument.

{docstring Hex.RealClosure.Tower.Context.roots_spec}

{name}`Hex.RealClosure.Tower.Context.roots_all` characterizes the zero
polynomial; {name}`Hex.RealClosure.Tower.Context.roots?_success` proves
actual diagnostic success; {name}`Hex.RealClosure.Tower.Context.roots_sorted`
proves strict order of the returned native values. Their common model is
essential. It does not give an ordinary-real embedding of an infinitesimal.

This example reuses the downstream tower consumer's composition. Given
a nonzero interpreted polynomial, the actual native producer returns a
finite strictly sorted list; no successful-output premise is supplied.

```lean
open Hex.RealClosure.Tower
open HexPolyMathlib.Interpret
namespace TowerCoverage

variable {registry : BaseContext.Registry}
variable {parent : Context registry}
variable {K : Type u}
variable [Field K] [LinearOrder K]
variable [DecidableEq K]
variable [IsStrictOrderedRing K]
variable [IsRealClosed K]

example (model : Model parent K)
    (p : DensePoly parent.Value)
    (nonzero : interpret model.value
      model.zero_iff p ≠ 0) :
    ∃ out, parent.roots p = .finite out ∧
      List.Pairwise (· < ·)
        (out.map (·.denote model)) := by
  cases returned : parent.roots p with
  | all =>
    exact False.elim (nonzero
      ((Context.roots_all model p).mp returned))
  | finite out =>
    exact ⟨out, rfl,
      Context.roots_sorted model p returned⟩

end TowerCoverage
```

For rational input, {name}`Hex.RealClosure.Trivial.Rational.roots`
converts generic roots to the independent real-algebraic carrier, retaining
the all-roots case, order and multiplicities. This is an agreement and
differential-testing route, not the fastest entry point: generic isolation
and canonical conversion have separate costs. Use the real-algebraic
backend directly when that conversion is unnecessary.

Ordinary-real tactic proofs belong to the existing real-coefficient `rcf`
adapter and its {ref "hex-rcf"}[manual]. Its source-expression guards,
selected embeddings and accepted-certificate realization remain separate
from the root-model hypotheses here. Existing owner Lean tests and conformance
cover non-monic definitions,
reducible inversion, nested roots, stale evidence and transport. Transport
controls include small executable build-time guards. The deep four-level
fixture is type-checked; its execution is outside routine CI. Exact
Z3/python-flint oracles separately check the emitted arithmetic and root
fixtures. Retained tower and clean/eager
measurements supply computational evidence; these examples and theorem
applications do not replace it.
