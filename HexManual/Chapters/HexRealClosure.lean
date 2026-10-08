/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import VersoManual
public import HexRealClosure
public import HexRealClosureMathlib.TowerRoots
public import HexRealClosureMathlib.RootCollection
public import HexRealClosureMathlib.ReconciledCatalog
public import HexRealClosureMathlib.SuppliedInverse

public section

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
The catalog gathering laws use `HexRealClosureMathlib.ReconciledCatalog`.
The finite inverse laws use `HexRealClosureMathlib.SuppliedInverse`.
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

# Checking a supplied inverse

A retained inverse can certify two different things. An
{name Hex.RealClosure.Algebraic.Packing.Inverse}`Inverse` record binds the
output's original polynomial to the native algorithm's actual candidate.
Its {name Hex.RealClosure.Algebraic.Packing.Inverse.native}`Inverse.native` theorem identifies
the packed output with the native inverse. A
{name Hex.RealClosure.Algebraic.Packing.Inverse.Equation}`Inverse.Equation` record instead
checks that a supplied output is an inverse at the selected root. It retains
the operand and checked signs of the operand and the residual
`operand · output - 1`. Those signs must be the operand's nonzero cached sign and zero.
This permits an inverse with a different polynomial representation.

{docstring Hex.RealClosure.Algebraic.Packing.Inverse.Equation.make?}

Use {name Hex.RealClosure.Algebraic.Packing.Inverse.Equation.readMemo?}`Inverse.Equation.readMemo?`
to obtain that record from an already checked sign graph. The reader binds
the operand, supplied output and selected root through the exact query slice;
it does not produce new sign evidence or compute an inverse candidate.
{name Hex.RealClosure.Algebraic.Packing.Inverse.Equation.make?_self}`Inverse.Equation.make?_self`
proves rechecking a retained record succeeds. An existing native inverse
record can be converted with
{name Hex.RealClosure.Algebraic.Packing.Inverse.toEquation}`Inverse.toEquation`, retaining
its operand and literal replay evidence.

The existing {name Hex.RealClosure.Algebraic.InverseFact}`InverseFact`
dictionaries and
{name Hex.RealClosure.Algebraic.Element.replayInverse}`Element.replayInverse`
and {name Hex.RealClosure.Algebraic.Element.replayQuotient}`Element.replayQuotient`
operations require the native record. A supplied equation proves a value
equation at the selected root, not equality of stored `Element` representatives,
and cannot replace that record in these operations.

The supplied-equation semantics have two useful interfaces.
{name Hex.RealClosure.Algebraic.Packing.Inverse.Equation.denote_inv}`Inverse.Equation.denote_inv`
proves the inverse law under a lawful predecessor interpretation into an
ordered real-closed field. For a reader justified only on reached coefficients,
{name Hex.RealClosure.Algebraic.Packing.Inverse.Equation.eval_inv}`Inverse.Equation.eval_inv`
instead uses zero and unit preservation, the reached product and subtraction
relations, and the two observed signs at a chosen point.

{name Hex.RealClosure.Algebraic.Packing.Inverse.Equation.atPoint}`Inverse.Equation.atPoint`
places the output and operand at the descriptor's shared finite selected
point in an ordered real-closed field. Its premises are zero and unit preservation, reached
descriptor data and
{name Hex.RealClosure.Algebraic.Packing.Inverse.Equation.Data}`Inverse.Equation.Data`.
The latter supplies the original packing's replay and subtraction relation,
the inverse equation's replay, and the reached product and subtraction
relations. The conclusion gives the original packing equation, the inverse
law and both cached signs at that same point. The stronger native record's
finite data converts with
{name Hex.RealClosure.Algebraic.Packing.Inverse.Data.toEquation}`Inverse.Data.toEquation`.
These interfaces require the caller to supply their semantic premises;
assembling them recursively through a whole tower remains a separate task.
Canonical zero uses {name Hex.RealClosure.Algebraic.Element.inv_zero}`Element.inv_zero`
and does not need a nonzero inverse record. Source-expression divisor guards
remain an obligation of the expression consumer.

The existing `InversePackingTests` runs both readers on monic and
non-monic reducible defining polynomials. It checks acceptance of a supplied alternate
inverse and rejection of a bad inverse, changed operand, wrong root domain,
out-of-range memo index and zero operand. These finite controls complement
the general conditional laws; they do not construct their semantic premises
for an arbitrary tower.

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

# Gathering owners into one context

A {name}`Hex.RealClosure.Tower.Live.Request` records the live operands
and root descriptors that must move together. Gathering retains each
requested owner's ancestry. Use {name}`Hex.RealClosure.Tower.Live.Request.gatherReconciled?`
with an explicit packed base: it gathers those owners, transports the
requested operands and revalidates the descriptors in one returned context.
The result retains both the original request and the checked conversions.
Its {name}`Hex.RealClosure.Tower.Live.Request.gatherReconciled?_shared` law
identifies the actual successful owner gather used by the live collection.

This route permits different orders of registered provider keys. It preserves
the existing ordered conversion when one is available; otherwise it uses the
checked provider reconciliation. Key coverage and infinitesimal depth are
checked on both paths. The reordering fallback and catalog selection also
check key distinctness; on the ordered path, distinctness follows from the
target's realization. A matching key list alone does not supply the providers'
semantic laws.

For automatic base selection, use
{name}`Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?` with a
{name}`Hex.RealClosure.BaseContext.Catalog` of installed real prefixes.
This is the base-provider catalog, distinct from the tower-handle catalog
used to read stored values. The operation selects the first key-compatible
prefix in catalog order: the rational prefix comes first, then installed
prefixes from newest to oldest. It extends that prefix to the maximum
infinitesimal depth of the owners' bases and performs the checked live gather.
Later prefixes are not retried after gathering fails. It searches the supplied
catalog rather than creating a new joint real-provider field. `none` reports
failure of this gathering attempt.

The semantic laws require {name}`Hex.RealClosure.BaseContext.Catalog.Models`:
every installed prefix has some {name}`Hex.RealClosure.BaseContext.RealPrefix.Model`
of that exact prefix. This is a mathematical premise, not a runtime model check.
{name}`Hex.RealClosure.BaseContext.Catalog.Models.empty` supplies this law
for {name}`Hex.RealClosure.BaseContext.Catalog.empty`, whose only prefix is rational.
{name}`Hex.RealClosure.BaseContext.Catalog.Models.insert`
preserves it when the context of a supplied provider model is successfully installed.
Under this premise, {name}`Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_success`
proves actual gathering success whenever an installed prefix contains every
owner's duplicate-free key list. The selected prefix need not be the particular
prefix used to establish that coverage. Thus a modeled catalog does not fail
to gather after selecting a compatible prefix.
{name}`Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_history`
records an installed prefix, a provider model of it and a staged realization,
together with the common target, owner and cache model.
{name}`Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_models`
gives the model-existence conclusion alone. The
{name}`Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_realize` law
states a prefix/provider history together with an ordinary-real reader and
domain for the original and refreshed finite live inventories. Use its returned
history and reader together with their accompanying evidence. This is a scoped
reader conclusion, not an ordinary-real embedding of the whole infinitesimal
field. It also does not supply a recursive exporter for arbitrary serialized
tower evidence.

The existing examples are in the library's `BaseTests`, `ReconciledGatherTests`
and `ReconciledBaseTests`, and the semantic `ReconciledCatalogTests` and
`ReconciledEnlargementTests`. Their executable selection, gathering and
conditional provider-model theorems exercise different parts of this interface;
the success theorem above supplies the general producer guarantee.

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
