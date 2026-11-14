# Hex algebraic reflection and tactics

This document specifies the common reflection and tactic facilities for Hex.
The Mathlib-free implementation uses `Lean.Meta.Sym.Arith` as its source
expression service and runs in `SymM`. Hex adds computational providers,
conversions to Hex data, verified algorithms, result conditions, and tactic
frontends. It does not copy the ring parser from Grind.

The corresponding Lean work is specified in the
[proposal for `Lean.Meta.Sym.Arith`](../lean4-sym-arith.md). Hex can use the
ring and semiring facilities which already exist. After Grind's migration is
complete, Lean can expose the existing noncommutative semantics through the
standalone interface and add fixed rational, additive, module, and
symbolic-exponent views.

The intended operations include:

- numerical, additive, ring, and module normalization;
- determinant, rank, and characteristic-polynomial computation;
- univariate and multivariate polynomial factorization;
- factorization of ordinary Lean ring expressions, with other subexpressions
  represented as variables;
- rational-expression transformations such as `together`, `cancel`, and
  `apart`;
- standalone term, tactic, and programmatic interfaces;
- selected Grind normalizers and propagators using the same reflection and
  verified algorithms.

## Decisions

The following decisions determine the design.

1. `SymM` owns source-expression sharing, canonicalization, algebraic
   classification, and reification into Lean's fixed algebraic languages.
2. A Hex state transformer over the caller's symbolic monad owns providers,
   derived views, conversions, conditions, proof provenance, and budgets.
3. A standalone invocation calls `SymM.run` once. A Grind invocation uses the
   `SymM` already underneath its `GoalM`. It does not start a nested symbolic
   session.
4. Lean's algebraic languages are closed. Hex imports do not register new
   operation recognizers or change which terms Lean treats as variables.
5. Hex's computational providers are extensible. A user type can provide only
   the fragments which have executable operations and proofs.
6. The source `Lean.Expr` and the session's variable identities connect
   specialized typed views. Hex does not define one inductive type containing
   every algebraic language.
7. Conversions operate directly on typed reflected values. They do not denote
   an intermediate Lean expression and send it through another parser.
8. Conditional transformations retain their hypotheses. Division in Lean is
   total, so cancellation and common-denominator identities are not generally
   unconditional.
9. Hex algorithms and certificate checkers do not depend on a tactic state or
   an e-graph.
10. Expensive computations are requested explicitly and carry budgets.
11. Computational libraries remain Mathlib-free. `*-mathlib` libraries add
    Mathlib-facing input translations and correspondence theorems.
12. Existing factorization searches and verified checkers remain in use. The
    shared facilities replace their duplicated expression parsers and
    dispatch conventions.

## Goals

### Closed computation

For concrete input over standard types, the frontends compute a result and
prove that result in Lean. Initial required examples are:

- the determinant of an `Int` matrix;
- the rank over `Rat` of an `Int` matrix after entrywise casting;
- the characteristic polynomial of an `Int` matrix;
- supported factorizations of integer and finite-field polynomials;
- the numerical and algebraic normal forms required by those computations.

The APIs are not restricted to `Int`. A finite field, rational
implementation, modular integer type, or user type participates when its
providers supply the required operations and correctness theorems.

### Symbolic computation

For a matrix whose entries are expressions in the commutative-ring language,
one batch reflection produces polynomial entries over a shared variable
environment. Hex then computes and proves the determinant or characteristic
polynomial in that formal polynomial domain.

After verified multivariate factorization is available, the same process
factors an ordinary ring expression. Subexpressions outside the ring language
become formal variables. Interpreting the returned factors proves that their
product is the original expression.

### Shared normalization

Hex supplies the common session, provider, conversion, and proof interfaces
needed by operations analogous to `norm_num`, `ring`, `ring_nf`, `abel`, and
module normalization. These remain different commands because they request
different languages, algorithms, result formats, and side-goal behavior. They
must not retain independent parsers for their shared subexpressions.

### Partial user capabilities

A user-defined type can register any useful subset of:

- closed scalar evaluation;
- additive normalization;
- commutative-ring normalization;
- decidable zero testing;
- field operations;
- exact quotients;
- Euclidean division, gcd, or extended gcd;
- univariate or multivariate factorization;
- conversion between the source type and an executable representation.

A consumer asks for the capabilities it needs. Resolution either selects a
provider or returns a structured explanation of the missing capability.

## Non-goals

This work does not require:

- one tactic which automatically tries every algebraic algorithm;
- an extensible grammar in `Lean.Meta.Sym.Arith`;
- a Hex copy of the current Grind ring reifier;
- creation of a mostly disabled Grind goal for standalone reflection;
- complete symbolic rank case analysis in the first release;
- multivariate partial fractions in the first release;
- a Mathlib dependency in computational packages;
- replacement of a mature Mathlib tactic before behavior, diagnostics, and
  performance have been compared;
- trusting a compiled search procedure, an external program, or a Meta
  registration as a proof.

## Execution architecture

Standalone and Grind callers enter the same Hex facilities through different
outer monads:

```text
standalone command, term, or tactic
              |
              v
           SymM.run
              |
              +--------------------+
                                   |
Grind GoalM over its existing SymM |
              |                    |
              +--------------------+
                                   v
                    Hex reflection state transformer
                                   |
                      Lean.Meta.Sym.Arith views
                                   |
                  cached conversion to Hex data
                                   |
                  verified algorithm or checker
                                   |
                equality, property, or conditional result
```

The standalone form is conceptually:

```lean
abbrev HexReflectM := StateRefT Hex.Reflect.State SymM
```

The implementation may generalize this alias over any monad with the required
`Sym.Arith` interfaces. The public API must not expose a transformer ordering
which prevents the same operation from running over `GoalM`.

The important property is that one invocation has one `SymM`. A Grind adapter
does not call `SymM.run` inside `GoalM`, and a standalone caller does not
construct Grind's e-graph or solver states.

## Use of `Lean.Meta.Sym.Arith`

### Facilities used immediately

Current Lean provides the following reusable operations:

- `SymM.run` for a standalone symbolic session;
- `Sym.canon` and the shared-expression facilities in `SymM`;
- cached algebraic classification through `Sym.Arith.classify?`;
- cached canonical operation expressions in `Sym.Arith.Functions`;
- `reifyRing?` and `reifySemiring?`;
- variable allocation and lookup through `MonadMkVar` and `MonadGetVar`;
- denotation of reflected expressions;
- pure polynomial and variable-renaming operations.

The first Hex implementation defines a small invocation-local state which
implements `MonadMkVar` and `MonadGetVar`. It uses the current Lean reifier
unchanged and caches conversions from its public result types.

### Lean additions requested by Hex

The Lean work has a strict order. Its first milestone is entirely about
current Grind behavior:

- exact copying of Grind's classifier into `Sym.Arith`, including
  semiring-envelope setup, registered instances, characteristic and
  no-zero-divisor handling, and `PowIdentity`, before Grind switches to it;
- migration of Grind's duplicate ring and semiring reifier to `Sym.Arith`;
- copying all selected reusable normalization and proof construction into
  `Sym.Arith` while Grind still uses its originals;
- a minimal adapter which switches Grind to those copies;
- deletion of the duplicate Grind code after behavioral and performance
  parity is established.

Hex does not add requirements to that milestone. In particular, the migration
does not need batching, a default standalone variable session, Hex result
types, provider hooks, matrix clients, or new expression languages.
Compatibility runs over
[`leanprover/downstream-lean4`](https://github.com/leanprover/downstream-lean4)
and Hex are part of validating existing numeral and canonicalization behavior,
not downstream feature work. Exact diagnostic wording need not be preserved.

Only after the Grind migration is complete does Hex request:

- a supported default standalone variable session;
- batch reification with stable variable identities;
- downstream-facing normalization results and equality proofs;
- a Grind atom adapter which can use e-graph representatives when allocating
  variables;
- standalone access to the existing noncommutative semantics;
- fixed rational, additive, module, and symbolic-exponent views as later
  additions.

After that boundary, Hex should exercise the new APIs as a downstream client.
This gives the later batch interface a determinant client and the conversion
API a factorization client without making either one part of Grind's
migration.

### Work which does not wait for Lean changes

Hex can start all of the following against the existing `Sym.Arith` API:

1. Define the Hex session state, provider protocol, conditions, and budgets.
2. Implement `MonadMkVar` and `MonadGetVar` for a standalone batch.
3. Reify ring and semiring expressions with the current Lean functions.
4. Seal a batch variable environment and convert a reflected ring expression
   directly to `Hex.MvPoly`.
5. Prove that conversion commutes with interpretation.
6. Add standard scalar providers and closed matrix frontends.
7. Add symbolic determinant and characteristic-polynomial frontends.
8. Adapt existing factorization dispatch and polynomial input translations.

This work remains in Hex and uses the Lean API as it exists. It does not
change the scope or sequencing of the Grind migration, and it must not make a
Hex abstraction a prerequisite for that migration. Hex can adjust its local
adapter after the shared Lean implementation is settled.

Hex must not implement a temporary source parser for a later `Sym.Arith`
language. The pure rational, additive, and module normalizers can be developed
against explicit reflected data before Lean exposes their source views. Their
general Lean-expression frontends wait for those views.

## Reflection session

### Lifetime

A reflection session belongs to one tactic invocation, one programmatic batch,
or one Grind adapter for a goal. It can retain local declaration references
and `Lean.Expr` values, so it is not stored in a process-global cache.

Its state contains:

- current `Sym.Arith` view results;
- variable environments needed until Lean supplies the default session;
- sealed batch environments;
- cached conversions to Hex representations;
- the typed relationships among scalar, polynomial, module, and matrix data;
- selected providers and the exact structure instances they use;
- accumulated conditions and proof provenance;
- computation and proof-reconstruction budgets;
- structured diagnostics.

The `SymM` state remains authoritative for source canonicalization,
classification, operation expressions, and reflected Lean values. Hex does
not duplicate those caches.

### Cache identity

A derived-view cache key includes every choice which can change meaning:

- the canonical source expression or reflected value identity;
- the requested view or Hex representation;
- the carrier type;
- the exact algebraic structure instances;
- the coefficient representation and interpretation map;
- the scalar action or algebra homomorphism, when applicable;
- the variable environment and its sealed size;
- relevant normalization options.

Type name alone is not a sufficient key. Lean permits multiple structure
instances and scalar actions on one carrier.

### Variable allocation and batch sealing

`MonadMkVar` is a storage interface, not a syntax extension. Lean invokes it
only after the selected fixed reifier has classified a subexpression as a
variable.

The standalone implementation assigns growing natural identifiers and keeps
an array of canonical source expressions. Repeated variables use the same
identifier. A future Grind implementation may map e-graph-equivalent atoms to
one identifier while retaining proofs required for interpretation.

Many Hex representations use `Fin n` variables. A batch therefore has two
stages:

1. Reify every input while the environment can grow.
2. Seal the environment once, convert every variable to the same `Fin n`, and
   cache all resulting Hex values.

A matrix never reifies each entry with a separate variable numbering.

### Typed domain relationships

The session records typed domains and explicit interpretation maps. This is
necessary when more than one sort occurs.

For a module `M` over a ring `R`, module atoms have type `M` and scalar
coefficients have type `R`. If `R` is itself an algebra over `S`, a conversion
from an `S` normal form to an `R` coefficient requires a named map and proof.
The relationship is not inferred by putting expressions of several types in
one untyped atom table.

For a characteristic polynomial, the polynomial variable is also distinct
from variables which came from matrix entries. An implementation can use
`DensePoly (MvPoly n C cmp)` so these roles cannot collide.

### Direct conversions

A conversion accepts a reflected value and produces:

- the target Hex value;
- an interpretation of that value in the source type;
- a theorem relating the source view to that interpretation;
- any conditions introduced by the conversion.

The conversion is cached. No conversion denotes a `Lean.Expr` merely to call
another expression parser.

The first important conversion is from `Sym.Arith`'s commutative-ring result
to `Hex.MvPoly`. It must preserve the variable environment and the target
ring's characteristic. Module coefficients later reuse this conversion
instead of invoking ring reflection again.

## Providers and capabilities

### Separation from Lean's grammar

A Hex provider supplies executable operations and proofs for a type. It does
not affect `Sym.Arith` recognition.

There are two interface levels:

- theorem-level records used by Mathlib-free algorithms;
- Meta registrations which locate those records, quote executable values, and
  build checked proof terms.

An environment extension or attribute can register providers. Registration
order must be deterministic. Importing a provider can change which Hex
algorithm handles a request, but it cannot change which source expressions
Lean parses as addition, multiplication, division, scalar multiplication, or
power.

### Capability fragments

The initial vocabulary contains small, composable capabilities:

| Capability | Operations enabled |
| --- | --- |
| scalar evaluation | closed numerals and supported scalar operations |
| additive normalization | `abel`-like normalization |
| commutative-ring normalization | polynomial normal forms and symbolic entries |
| decidable zero | trimming, pivot selection, and cheap conditions |
| field operations | row reduction and rational coefficients |
| exact quotient | fraction-free elimination and exact cancellation |
| Euclidean division | univariate division and Euclidean gcd |
| gcd with laws | lowest-term rational normalization |
| extended gcd | Bezout certificates and partial fractions |
| univariate factorization | `factor_poly` and univariate `apart` |
| multivariate factorization | factorization of formal ring expressions |
| matrix translation | batch conversion from an external matrix type |

These are not fields of one large typeclass. Exact quotient is useful without
a Euclidean algorithm. A specialized finite-field factorizer need not pretend
to implement every operation of a general coefficient hierarchy.

Each algorithm requests the weakest suitable set. `together` requires
addition, multiplication, and a conditional rational interpretation, but no
gcd. `cancel` additionally requires a gcd or specialized cancellation
provider. Bareiss requires exact quotients and their laws. Samuelson-Berkowitz
does not require division.

### Provider outcomes

Provider selection uses four outcomes:

- `notApplicable`: this provider does not handle the request;
- `declined`: the provider applies in principle, but a documented condition
  such as a literal modulus or budget is not satisfied;
- `success`: the provider supplies checked data and proof provenance;
- `failure`: the provider registration or returned evidence is malformed.

Dispatch may continue after `notApplicable`. A frontend may try a lower
priority provider after `declined` when its contract allows fallback.
`failure` is reported immediately with the provider identity and context.

Search exhaustion is `declined`, not evidence that a factor or decomposition
does not exist.

### User-defined types

A package supporting a user type defines an executable representation and
theorems relating its operations to source operations, then registers the
available fragments.

For example, a quotient ring may register scalar evaluation, addition,
multiplication, equality, and zero testing, but no exact quotient, gcd, or
factorization. Ring normalization and division-free characteristic
polynomials then work. Bareiss, cancellation, and factorization report the
specific missing capabilities.

Providers are keyed by the carrier and exact relevant structure instances.
This prevents accidental use of a provider with a different multiplication
or scalar action on the same type.

## Results and conditions

Every frontend uses a common result protocol.

### Equality results

An unconditional normalization returns:

- the source expression;
- the reflected or quoted result;
- a proof that they are equal;
- presentation data such as the variable environment.

Proof construction may be delayed, but a tactic obtains the proof before it
rewrites a target or closes a goal.

### Conditional equality results

A conditional transformation returns:

- the transformed expression;
- an ordered collection of hypotheses;
- a theorem proving equality under those hypotheses;
- provenance used to deduplicate conditions.

A tactic handles conditions in this order:

1. Check definitional equality and local hypotheses.
2. Run explicitly configured cheap normalizers.
3. If already inside Grind, query facts known to that goal.
4. Create side goals if the command's contract permits them.
5. Otherwise decline without changing the goal.

A term or programmatic API returns the conditions rather than creating goals.
The ordering is deterministic so tests and error messages remain stable.

### Property and certificate results

Factorization, rank, and similar computations return their library-specific
property certificate in addition to any display expression. A frontend does
not replace a failed property check with a weaker claim about the displayed
value.

For expensive searches, a result also records the budget used and the most
specific decline reason.

## Scalar and numerical normalization

`Sym.Arith.EvalNum` evaluates ground natural and integer expressions needed to
construct algebraic classification data. It is not a general replacement for
`norm_num`.

Hex therefore has a narrow, extensible scalar evaluator. A scalar provider
recognizes operations within its declared fragment, computes in an executable
representation, and supplies theorems which reconstruct a source equality or
property. The initial providers should cover only operations needed by real
Hex algorithms and standard types.

The design borrows two useful properties from Mathlib `norm_num`:

- operation-specific extensions can decline without making the whole
  evaluator unsound;
- every successful evaluation constructs a proof from registered theorems.

Hex need not reproduce Mathlib's complete extension collection. A Mathlib
companion can adapt existing `norm_num` procedures for Mathlib types. The
Mathlib-free evaluator remains sufficient for the Lean and Hex types used by
the computational libraries.

Scalar evaluation occurs before or during conversion of a `Sym.Arith` view.
It does not register another ring grammar. A source subexpression outside the
selected Lean language remains a variable unless a proved source translation
was explicitly requested first.

## Algebraic views and normalizers

### Commutative rings and semirings

This path is implementable now. `Sym.Arith.reifyRing?` and
`reifySemiring?` recognize the fixed source grammar and allocate variables.
Hex converts the result directly to a characteristic-aware polynomial
representation.

An equality-closing frontend compares normalized reflected values. A
rewriting frontend denotes a chosen normal form and proves equality with the
canonical source. These provide the shared implementation for behavior
analogous to `ring` and `ring_nf`.

Algorithms which need `Hex.MvPoly` request the cached conversion. A simple
ring equality need not pay for every Hex polynomial representation.

### Additive expressions

An additive view represents zero, addition, subtraction, negation, integer
multiples, and atoms over an additive commutative group or monoid. It does not
require multiplication on the carrier.

The source frontend should use a fixed `Sym.Arith` additive view. Until Lean
provides it, Hex may develop pure normalization and proof theorems over an
explicit additive expression type, but it does not add a second general
`Lean.Expr` parser.

This view supplies behavior analogous to `abel`. It is also a component of
module reflection.

### Noncommutative rings

The noncommutative view preserves multiplication order and normalizes only by
valid semiring or ring laws. Lean already distinguishes commutative and
noncommutative structures during classification, but reusable standalone
normalization and proof production must be completed in `Sym.Arith`.

No conversion may turn this view into a commutative `MvPoly` by forgetting
order. Consumers either use a noncommutative normal form or treat products as
atoms in a weaker view.

### Modules

For a module `M` over a ring `R`, a normal form is conceptually a sparse map
from module atoms to scalar normal forms:

```text
module atom in M |-> normalized coefficient in R
```

This is a two-sort view. It records the exact additive operations on `M`, ring
operations on `R`, and action of `R` on `M`. If several actions are available,
the caller selects one explicitly or receives an ambiguity diagnostic.

The coefficients use cached scalar views from the same session. The module
normalizer does not store raw coefficient expressions and later call a ring
tactic on each one.

Identity normalization and consequence solving are separate operations.
Gaussian elimination can solve relations over a field. Module membership and
syzygy algorithms require additional capabilities over suitable scalar
rings. A request declines when those capabilities are absent.

### Symbolic natural exponents

Literal natural powers remain on the ordinary polynomial path. An exponent
such as `m + n` uses a nested natural-number expression view and an explicit
symbolic power node.

The representation must not claim that `x ^ m` is an ordinary polynomial in
the two variables `x` and `m`. Consumers can normalize the exponent, apply
valid power laws, or treat the entire power as an atom when their target
representation cannot express it.

The natural exponent view shares `SymM` canonicalization and caches with the
outer ring view. It has its own typed variable identities.

## Rational expressions

A rational view represents a quotient of polynomial normal forms and records
the nonzero conditions required for its interpretation. It uses Lean's future
fixed rational-expression view rather than a Hex parser.

The tempting identity

```text
1 / x + 1 / y = (x + y) / (x * y)
```

is not unconditional for totalized field inversion. The result must retain
the required hypotheses on `x` and `y`, or use a theorem whose exact
totalized-field semantics justify a weaker condition.

### `together`

`together` computes a common numerator and denominator by addition and
multiplication. It requires no gcd. The pure rational algorithm and its
theorems can be implemented before the Lean source view lands.

The tactic returns side goals for the conditions allowed by its contract. A
programmatic call returns the conditions and conditional equality theorem.

### `cancel`

`cancel` normalizes numerator and denominator by a verified gcd and exact
division. The multivariate operation depends on `hex-mv-gcd` or a specialized
provider with equivalent laws.

Cancellation does not erase the original denominator condition. If the
rewritten denominator introduces a differently stated condition, the result
records and relates both through checked theorems.

### `apart`

The first `apart` operation is univariate. It factors the denominator and uses
extended gcd or an equivalent verified construction to produce partial
fractions. Conditions state when the interpreted denominators are nonzero.

Multivariate partial fractions require a separate specification which chooses
a decomposition notion and ideal machinery. The rational view alone does not
provide that algorithm.

## Matrix computations

### Input conversion

The Mathlib-free frontend accepts `Hex.Matrix` and related executable inputs.
A Mathlib companion enumerates finite Mathlib matrix indices, constructs the
Hex input, and proves entrywise correspondence.

Every matrix entry is reflected in one batch. The result records matrix shape,
entry order, the shared sealed variable environment, coefficient
interpretation, and the location of any failed conversion.

### Determinant

Initial algorithm selection is:

| Input and available laws | Algorithm |
| --- | --- |
| closed `Int` matrix | fraction-free Bareiss |
| commutative-ring matrix without exact quotient | Samuelson-Berkowitz constant coefficient |
| symbolic polynomial entries with certified exact quotient | polynomial Bareiss |
| symbolic polynomial entries without exact quotient | Samuelson-Berkowitz constant coefficient |

For symbolic input, the proof proceeds through the shared polynomial domain:

1. Reify every entry with one variable environment.
2. Convert the entries to `Hex.MvPoly` and prove each interpretation equality.
3. Compute a determinant in the polynomial domain.
4. Interpret the resulting polynomial in the source ring.
5. Apply determinant preservation under the entrywise interpretation map.

Intermediate matrix operations do not construct and reparse Lean ring
expressions. The final result expression is denoted once when the frontend
needs one.

Paul Cadman's Bird determinant tactic remains a useful compatibility and
differential reference. Hex should cover its literal-matrix inputs and extend
the same user operation to ordinary matrices and symbolic entries. A
Mathlib-facing wrapper can delegate to Hex after the new path has comparable
behavior, diagnostics, and proof size.

### Characteristic polynomial

The initial algorithm is Samuelson-Berkowitz from
[hex-char-poly](hex-char-poly.md). It is division-free over a commutative ring.

Closed `Int` input produces `Hex.DensePoly Int`. The Mathlib companion proves
agreement with `Matrix.charpoly` under the chosen sign convention.

For symbolic entries, coefficients lie in the shared multivariate polynomial
domain. The characteristic variable remains structurally separate, for
example in `DensePoly (MvPoly n C cmp)`. It is not allocated as another source
atom.

### Rank

Rank requests state their scalar domain. For an `Int` matrix, the operation
called integer rank means the rank over `Rat` after entrywise casting. It does
not refer to an unspecified rank for an `Int` module.

For matrices over a field, verified row reduction returns a rank and
certificate. Another domain can participate through a provider whose theorem
states its rank convention.

Symbolic rank is not normally one unconditional natural number. A
specialization can make pivots or minors vanish. The planned results are:

- generic rank over the fraction field of the polynomial domain;
- conditional rank with explicit vanishing and nonvanishing hypotheses;
- later, piecewise rank obtained by budgeted case splitting.

The first symbolic implementation may provide only generic rank. It must not
present generic rank as valid for every specialization.

## Polynomial and expression factorization

### Existing algorithms and checkers

`hex-berlekamp`, `hex-berlekamp-zassenhaus`, and related libraries retain
their search algorithms, certificate types, Boolean checkers, soundness
theorems, and result conventions. The tactic work changes input conversion and
provider dispatch.

Compiled search produces candidate data. The final theorem uses the existing
verified checker and interpretation results. The search implementation never
appears as a trusted premise in the theorem.

### Typed polynomial inputs

A generic ring reifier normally treats constructors such as a library's
polynomial `X` and `C` as variables. A `factor_poly` frontend therefore needs
a typed polynomial adapter in addition to outer ring reflection.

The adapter:

1. recognizes the selected polynomial type and its exact coefficient
   structure;
2. translates its constructors or public coefficient enumeration to the Hex
   executable polynomial type;
3. proves an interpretation theorem for that translation;
4. invokes the registered factorization provider;
5. replays the candidate through the existing checker.

Mathlib `Polynomial` and `MvPolynomial` recognition belongs in a Mathlib
companion. Mathlib-free polynomial types use adapters in their owning Hex
libraries.

During migration, the current parser-with-proof and the new
`Sym.Arith`-based path are compared on their shared input grammar. Search and
certificate checking do not change at the same time as source conversion.

### Arbitrary ring expressions

When multivariate factorization is available, the expression frontend:

1. reifies an ordinary commutative-ring expression with `Sym.Arith`;
2. seals its variable environment;
3. converts the result to `Hex.MvPoly`;
4. factors that formal polynomial;
5. verifies the product and claimed factor properties in the formal domain;
6. interprets the factors back into the source ring.

The unconditional transferable fact is that the interpreted factors multiply
to the source expression. Irreducibility of a formal polynomial does not in
general imply irreducibility after arbitrary substitution. A frontend reports
formal irreducibility separately unless the interpretation map satisfies
additional proved hypotheses.

## Grind integration

Hex operations are not all implemented as Grind tactics. Grind supplies
equality propagation, congruence closure, hypotheses, and case splitting.
Standalone term and tactic clients also require the same computations.

A Grind adapter runs a Hex state transformer over the existing `GoalM`. Calls
to `Sym.Arith` reach the existing underlying `SymM`, so classification,
canonicalization, and source-expression sharing are retained. There is no
nested `SymM.run`.

An operation can participate in Grind as:

- a normalizer, adding a proved equality with a normal form;
- a propagator, adding a proved property such as a closed determinant value;
- a splitter, proposing cases for conditions such as a symbolic pivot being
  zero or nonzero.

Default policy follows expected cost:

| Operation | Grind policy |
| --- | --- |
| scalar, additive, and ring normalization | available under ordinary arithmetic budgets |
| current guarded inverse reasoning | retain existing behavior |
| determinant and characteristic polynomial | demand-driven and size-bounded |
| closed rank | demand-driven and size-bounded |
| `together` and `cancel` | run when conditions are known, unless side goals were requested |
| factorization | opt-in |
| symbolic rank splitting | opt-in with an explicit split budget |
| `apart` | explicit request |

Grind may choose an e-graph representative when `MonadMkVar` allocates an
atom. The adapter must retain enough proof information for the denotation
theorem. The standalone implementation uses ordinary symbolic
canonicalization and definitional equality.

Imported providers can give Grind stronger computations for recognized
types. Their registration changes provider choice, not Lean's fixed source
grammar.

## Relationship to existing tactics

### Mathlib `norm_num`

Mathlib `norm_num` demonstrates useful extension dispatch and local
proof-producing evaluation. The Mathlib companion should reuse its procedures
when that is the best support for a Mathlib type. Hex does not copy the whole
extension collection or depend on it from Mathlib-free code.

### Mathlib `ring`, `ring_nf`, `abel`, and module normalization

These tactics define important compatibility cases, supported syntax, and
diagnostics. Hex should compare against them while introducing shared
reflection and conversions.

The main architectural difference concerns repeated reflection. A module
coefficient which has already received a scalar view remains that cached
view. Module normalization does not call a separate ring tactic which parses
the same coefficient again.

Compatibility commands or delegation from existing names are later adoption
decisions. They require demonstrated coverage and acceptable build cost,
runtime, proof size, and messages.

### Grind ring normalization

Grind and Hex should use the same `Sym.Arith` ring and semiring reifier. Grind
retains its constraint basis, equality and disequality queues, inverse facts,
and hypothesis-dependent derivations. Hex uses reusable normalization results
and proof constructors, not those solver states.

### Existing `factor_poly`

The existing factor tactics supply mature examples of provider-like outcomes,
compiled search, and checked replay. Their useful protocols should be adapted
rather than discarded. Fixed-name extension discovery and duplicated
source-expression parsing are the pieces to replace.

## Mathlib-free and Mathlib-facing libraries

### Mathlib-free responsibilities

Mathlib-free packages own:

- the Hex state transformer over `SymM` or another compatible symbolic monad;
- provider keys, capability requests, outcomes, and registration;
- batch variables, derived-view caches, conditions, and budgets;
- direct conversion from public `Sym.Arith` results to Hex data;
- standard providers for Lean and Hex types;
- verified algorithms and certificate checkers;
- frontends for Mathlib-free source types.

They may depend on Lean's Meta API and the smallest relevant Hex libraries.
They do not import Mathlib to recognize a standard type.

### Mathlib companion responsibilities

`*-mathlib` packages add:

- translations for Mathlib matrices, polynomials, scalar types, actions, and
  homomorphisms;
- correspondence theorems between Hex executable results and Mathlib
  definitions;
- optional scalar providers using Mathlib `norm_num`;
- Mathlib tactic syntax and result presentation;
- compatibility adapters after sufficient parity testing.

General Mathlib recognition useful to several algorithms belongs in a shared
package such as `hex-reflect-mathlib`. An algorithm-specific theorem remains
in the corresponding companion, such as `hex-char-poly-mathlib`.

An optional `hex-tactics-mathlib` package can import common companions. Users
and Mathlib can instead import one narrow package. This produces concrete
evidence about dependency size and maintenance before broader adoption.

## Proposed library organization

The final package list belongs in `libraries.yml` and
`scripts/release/released.yml`. The intended responsibilities are:

### `hex-reflect`

Owns the Hex state transformer, provider protocol, conditions, budgets,
variable sealing, and cached conversions from current public `Sym.Arith`
views. Until Lean supplies the standard variable session, it also owns the
small `MonadMkVar` and `MonadGetVar` implementation.

It contains no alternate ring parser. It does not depend on determinant,
row-reduction, characteristic-polynomial, gcd, or factorization packages.

### `hex-reflect-mathlib`

Owns general translations for Mathlib carriers, operations, matrices,
polynomials, actions, and homomorphisms. It can register Mathlib scalar
providers. It owns no algebraic search algorithm.

### `hex-matrix-tactic`

Owns matrix batch conversion, algorithm selection, result reconstruction, and
frontends for determinant, rank, and characteristic polynomial. It depends on
`hex-reflect` and the relevant matrix computation libraries.

Its Mathlib companion relates the results to `Matrix.det`, `Matrix.rank`, and
`Matrix.charpoly`.

### `hex-rational-tactic`

Owns consumers of the future `Sym.Arith` rational view and the `together`
algorithm. Cancellation and partial fractions can be separate provider-driven
modules so the base package does not create cycles with gcd and factorization
packages.

### Existing factor packages

Existing factor tactic packages adopt the shared state and provider outcomes
without moving their searches or checkers into `hex-reflect`.

### `hex-tactics`

An optional umbrella imports stable Mathlib-free frontends and common
providers. It contains no implementation which belongs in an algorithm
package.

## Trust and proof construction

The project-wide ban on `native_decide` applies to every provider and
frontend.

The preferred pattern for an expensive algorithm is:

1. Compiled Lean or an optional external routine searches for candidate data.
2. Shape validation rejects malformed data.
3. A verified checker checks the candidate against reflected input.
4. A soundness theorem proves the requested property.
5. Interpretation theorems transfer the property to the source expression.

An executable algorithm with a direct correctness theorem can omit the
candidate and checker separation. In both cases, Lean's kernel checks the
final proof.

Reflection retains compact provenance and reconstructs source proofs only
when requested. Matrix and polynomial algorithms should reason over
executable data. They cross back to source expressions through named
interpretation theorems rather than inserting a large Lean expression at each
intermediate operation.

No provider may introduce an axiom or treat a Boolean result from untrusted
code as a proof.

## Diagnostics and budgets

Every potentially expensive request carries an explicit budget. Dimensions
include:

- reflected syntax nodes;
- variables in a sealed environment;
- matrix dimensions;
- polynomial terms and degrees;
- coefficient sizes;
- factor-search effort;
- proof-reconstruction size;
- Grind case splits.

A provider can add an algorithm-specific dimension. Budget exhaustion returns
`declined` with usage information.

A diagnostic identifies:

- the requested operation;
- the first unsupported expression and its type;
- the carrier and exact structure instance when relevant;
- the missing capability;
- the provider which declined and its reason;
- outstanding conditions;
- consumed budget after exhaustion.

Nested locations are retained. A matrix failure names the entry index. A
module failure distinguishes a scalar coefficient from a module atom. A
rational failure identifies the denominator responsible for a condition.

## Validation

### Foundational clients

The following clients validate increasingly rich parts of the design:

1. A symbolic determinant validates batch ring reflection, variable sealing,
   `MvPoly` conversion, algorithm execution, and interpretation in one scalar
   sort.
2. A closed characteristic polynomial validates a division-free matrix path
   and polynomial result reconstruction.
3. `together` validates conditional results without requiring gcd.
4. A module identity with polynomial coefficients validates two sorts, a
   scalar action, nested cached views, and no repeated coefficient parsing.
5. Expression factorization validates direct conversion from a ring view to a
   multivariate factorizer and checked interpretation of the product.

The session API is not stable until these clients can use it without access to
private representation fields.

### Differential tests

Compare accepted inputs, results, and diagnostics with:

- current Grind ring and semiring behavior;
- Mathlib `norm_num`, `ring`, `ring_nf`, `abel`, and module normalization;
- Paul Cadman's Bird determinant tactic on its supported inputs;
- current `factor_poly` input adapters and extension drivers;
- external algebra systems only as untrusted test oracles where existing Hex
  policy permits them.

An intentional semantic difference requires a named test and documentation.

Provider tests must confirm the grammar boundary. Importing a Hex provider or
Mathlib companion can change which computation is selected. It cannot change
the `Sym.Arith` view or the source subexpression which Lean classifies as a
variable.

### Performance evidence

Benchmarks report:

- source reification time separately from algorithm time;
- number of expressions requested and view-cache hit rates;
- batch allocation and elapsed time;
- conversion cost for `Sym.Arith` values to Hex data;
- proof size and kernel checking time;
- standalone `SymM` cost compared with constructing a mostly disabled
  `GoalM`;
- Grind cost with and without the relevant Hex adapter;
- behavior against existing tactics on overlapping inputs;
- import and build cost of each package and Mathlib companion.

Evidence for Mathlib adoption includes representative successes, declines,
and diagnostics. A narrow import with measured benefit is more useful than an
umbrella benchmark alone.

## Implementation sequence

The upstream sequence in the
[`Sym.Arith` proposal](../lean4-sym-arith.md#proposed-work-sequence) takes
priority over every downstream-facing Lean request in this section. Lean first
copies the current classifier exactly and then copies the remaining selected
machinery into `Sym.Arith`, switches Grind to it, and deletes the old Grind
implementations. Policy flags for a cleaner standalone classifier come only
after the exact copy is established. No Hex batch API, provider interface,
matrix client, or new expression view is part of that work.

Hex-only implementation can proceed against the current public API or against
explicit Hex data. Such work must not constrain the upstream migration. Any
change requested in Lean for a Hex phase below waits until the migration phase
is complete.

### H0. Adopt current `Sym.Arith`

Define the Hex state transformer, provider outcomes, conditions, budgets, and
standalone variable environment. Reify one batch with current
`reifyRing?` and prove a direct conversion to `Hex.MvPoly`. No new source
parser is permitted. Keep all of this work in Hex and adapt it as necessary
after Grind's migration is complete.

### H1. Closed standard computations

Register the required `Int` and rational providers. Connect closed determinant,
rank, characteristic-polynomial, and supported polynomial-factorization
computations to proof-producing frontends.

### H2. Symbolic matrix computations

Reflect all matrix entries in one batch. Implement symbolic determinant and
characteristic-polynomial proof transport through `Hex.MvPoly`. Measure source
reification, conversion, algorithm time, and proof checking separately.

### H3. Factor tactic migration

Adapt one existing `factor_poly` frontend to the provider outcomes and typed
input translations. Compare it with the old path, then remove duplicated
parsing for that input after parity is established. Retain all existing search
and certificate checks.

### H4. Shared normalization frontends

Expose ring equality and rewriting operations using `Sym.Arith` normalization
proofs. Add scalar evaluation providers needed by existing algorithms. Add
additive and module frontends when their fixed Lean views are available.

### H5. Rational algorithms

Implement the pure conditional rational representation and `together`
theorems. Connect the source frontend after Lean adds the rational view. Add
`cancel` through multivariate gcd and univariate `apart` through factorization
and extended-gcd providers.

### H6. Grind adapters

After Grind uses the shared `Sym.Arith` reifier, add selected normalizer and
propagator adapters over the existing `GoalM`. Keep costly operations
demand-driven. Measure default configurations before enabling any additional
automatic work.

### H7. Additive, module, and exponent views

Connect pure Hex normalizers to Lean's fixed additive, general module, and
symbolic-exponent views. Verify that module coefficients reuse cached ring
views. Add consequence-solving algorithms as separate consumers.

### H8. Multivariate expression factorization

After verified multivariate factorization is available, factor arbitrary ring
expressions as formal polynomials. State product equality unconditionally and
state transferred irreducibility only under proved hypotheses on the
interpretation.

### H9. Mathlib adoption

Add narrow Mathlib translations and correspondence theorems. Compare against
mature tactics, provide compatibility frontends where useful, and propose
Mathlib imports with measured build and maintenance costs.

## Open implementation choices

The boundaries above are fixed. The following representation choices require
measurements.

### State transformer interface

The initial standalone type can be `StateRefT Hex.Reflect.State SymM`, but
operations should be polymorphic enough to run over Grind's existing monad.
The exported interface should specify required capabilities rather than a
particular transformer order.

### Polynomial conversion

The session can retain the public `Sym.Arith` reflected polynomial and convert
lazily to `Hex.MvPoly`, or construct a Hex value immediately after sealing the
batch. Start with one explicit cached conversion. Direct construction is
justified only if profiling shows that conversion dominates clients.

### Coefficient representation

There is no universal coefficient type. Characteristic-zero clients may use
`Int`; finite fields use their existing executable representations. Each
provider supplies an interpretation map and theorems showing that computation
respects it. `Rat` must not become a universal default.

### Proof granularity

Per-node proofs simplify some initial implementations. Delayed reconstruction
can reduce allocation for matrix batches. Consumers should observe only the
final proof request so the choice can change after measurement.

### Provider priority

A generic field algorithm and a specialized finite-field implementation can
both apply. Version one uses deterministic registration priority and an
explicit override. Automatic selection by estimated cost requires benchmark
data and is deferred.

## Completion criteria

The first releasable family satisfies all of the following:

- closed `Int` determinant, rational rank, characteristic polynomial, and
  supported polynomial factorization have proof-producing frontends;
- symbolic determinant and characteristic polynomial use one batch variable
  environment for all matrix entries;
- a user type can register a partial computational fragment and obtain both
  useful successes and precise missing-capability declines;
- `together` returns explicit denominator conditions;
- at least one existing `factor_poly` frontend uses the shared provider and
  reflection protocol without weakening its certificate path;
- numerical, ring, additive, and module operations use shared session views
  whenever those fixed Lean views exist;
- module coefficients are cached rather than reparsed;
- standalone and Grind callers share `Sym.Arith` and Hex algorithms while
  retaining separate goal, budget, and atom policies;
- no Hex import changes Lean's recognized algebraic language;
- no Mathlib module is imported by the computational packages;
- Mathlib companions prove representative Matrix, Polynomial, and scalar
  correspondences;
- conformance, runtime, proof-size, kernel-checking, and import-cost results
  are recorded for compatibility cases.

Multivariate expression factorization, univariate `apart`, general module
consequence solving, piecewise symbolic rank, and delegation from every
mature Mathlib tactic may follow the first release. The interfaces above
reserve the required distinctions without making the first implementation
depend on all of those algorithms.
