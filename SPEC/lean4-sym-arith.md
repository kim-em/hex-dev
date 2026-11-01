# Proposal: complete `Lean.Meta.Sym.Arith` as the shared algebraic reflection service

Lean already has the right home for reusable algebraic reflection:
`Lean.Meta.Sym.Arith`. It classifies algebraic structures, caches their
operation expressions, reifies ring and semiring expressions, assigns
variables through a monad interface, denotes reflected expressions back into
Lean syntax, and provides pure polynomial utilities. It runs in `SymM`, the
symbolic-computation monad underneath Grind, without constructing a Grind
goal.

The proposed Lean work begins by making Grind use this service. Each reusable
piece which should live in `Sym.Arith` is copied there with its present
semantics. Grind then switches to the copy, and the old Grind implementation
is deleted. This migration is completed before work begins on standalone
conveniences, batch interfaces, downstream requirements, or new expression
languages.

Only after that migration is complete should Lean extend the service. The
later work adds a supported standalone interface, batch operations, and fixed
rational, additive, module, and symbolic-exponent views.

This proposal does not put determinant, rank, characteristic-polynomial, gcd,
or factorization algorithms in Lean. Downstream packages such as Hex use
`Sym.Arith` to obtain a shared, proved interpretation of source expressions and
then invoke their own verified algorithms.

## Current architecture

The relevant monads form this hierarchy:

```text
MetaM
  ^
SymM
  ^
GrindM = Grind configuration, simplifier, methods, and shared Grind state
  ^
GoalM  = Grind goal, e-graph, facts, E-matching, splits, and solver states
  ^
RingM and SemiringM = one Grind algebraic solver domain
```

`SymM` is already an invocation-local symbolic session. It provides maximally
shared expressions, canonicalization caches, type and level caches, instance
overrides, issue reporting, and typed state slots registered by symbolic
modules. `SymM.run` needs a Meta context but no metavariable goal.

`GoalM` has a different purpose. It adds a specific `MVarId`, an e-graph,
congruence closure, fact queues, E-matching state, splitting state, and the
state of every registered Grind solver. Constructing a Grind goal also creates
distinguished e-nodes and initializes every solver state. Configuration flags
can make solvers decline work, but they do not turn `GoalM` into a small
reflection session.

Standalone algebraic reflection should therefore run in `SymM`. Grind uses the
same operations through instances and adapters in `GoalM`.

## What `Sym.Arith` already provides

The existing modules establish most of the representation boundary.

### Algebraic classification

`Sym.Arith.classify?` detects the strongest supported structure on a type in
this order:

1. `Lean.Grind.CommRing`;
2. `Lean.Grind.Ring`;
3. `Lean.Grind.CommSemiring`;
4. `Lean.Grind.Semiring`.

The result is cached by canonical type expression. Classification records the
exact structure instances, universe level, characteristic information, and
relevant optional laws. Commutative rings also record available field and
no-natural-zero-divisor evidence. Commutative semirings use the existing ring
envelope.

### Cached operation expressions

The operation getters synthesize and cache the exact `+`, `*`, `-`, negation,
power, natural-cast, integer-cast, and inverse expressions associated with a
classified structure. Each getter verifies that the synthesized instance is
definitionally equal to the instance supplied by the algebraic law record.

Recognition compares an application against these canonical operation
expressions. Two different multiplication instances on the same carrier are
not silently interpreted as one ring.

### Fixed ring and semiring reification

`Sym.Arith.reifyRing?` recognizes numerals, natural and integer casts,
addition, subtraction, negation, multiplication, and powers with literal
natural exponents. `Sym.Arith.reifySemiring?` recognizes the corresponding
semiring fragment. Unsupported subexpressions become variables.

The variable operation is abstracted by `MonadMkVar`. Denotation uses
`MonadGetVar`. A standalone state can implement these with an array and an
expression-to-variable map. A future Grind adapter can preserve Grind's
current internalization and e-graph behavior.

The language recognized by these functions is fixed. `MonadMkVar` is invoked
only after the recognizer has classified a subexpression as a variable. It
does not add syntax to the language.

### Denotation and pure polynomial operations

`denoteRingExpr`, `denotePoly`, and related operations reconstruct Lean syntax
using the cached structure operations and variable environment. The current
round-trip tests check that reification followed by denotation is
definitionally equal to the canonical source expression.

The reflected polynomial, monomial, power, variable-renaming, and quoting
utilities are independent of Grind's goal state. Kernel-facing reflected types
and theorems remain in `Lean.Grind.CommRing` where moving them would create
unnecessary churn.

### Monad abstractions

`MonadCanon`, `MonadRing`, `MonadCommRing`, `MonadSemiring`,
`MonadCommSemiring`, `MonadMkVar`, and `MonadGetVar` let the same algorithms run
over a small standalone state or a richer Grind state. They are execution and
storage abstractions. They are not a registration mechanism for new algebraic
grammars.

## What remains Grind-specific

The shared implementation is not yet a complete replacement for Grind's
commutative-ring module.

Grind still has its own versions of ring and semiring reification. Its
`RingM` and `SemiringM` state also contain solver-specific data which does not
belong in `Sym.Arith`, including:

- mappings from terms to Grind ring identifiers;
- e-graph solver-term markings;
- denotation maps used during internalization;
- equality and disequality queues;
- constraint bases and polynomial derivations;
- inverse facts and power-identity bookkeeping;
- solver step counts and resource diagnostics.

Characteristic-aware safe polynomial conversion and the proof construction
for normalized equalities also remain in the Grind module. Some of that code
is general normalization machinery. Constraint-basis maintenance and proofs
which depend on hypotheses are Grind solver machinery.

The migration must separate these roles rather than moving the entire Grind
ring solver into `Sym.Arith`.

## Decisions

### Complete migration before generalization

The first group of changes has one purpose: make `Sym.Arith` the location of
the reusable algebraic machinery which Grind already uses. It preserves the
current accepted grammar, normalization semantics, proof terms up to expected
implementation variation, resource behavior, and solver results.

This group includes moving reusable normalization and proof construction,
adapting Grind to the shared monad interfaces, making the `Sym.Arith`
classification state authoritative, and deleting the duplicate Grind
reifiers. It does not include a default standalone session, a batch API, a new
result vocabulary designed for downstream clients, or another expression
language.

Part I needs only the narrow declarations required for Grind to call the moved
code. Decisions about a polished public API, snapshots, delayed proof
requests, or downstream conversion hooks belong to Part II, even when the
moved implementation will eventually support them.

This is a hard phase boundary. No later feature should be included in a
migration change merely because it would make a downstream application
easier. The completed migration gives later work one implementation to extend
and keeps unrelated design choices out of the review of Grind's existing
behavior.

### Use `SymM`, not a dormant Grind goal

The standalone API runs in `SymM` or in a small state transformer over
`SymM`. It does not construct `GoalM` with most configuration flags disabled.

This avoids an otherwise unnecessary `MVarId`, e-graph, E-matching state,
split state, all registered solver states, theorem activation, and recursive
Grind internalization of atoms. It also makes command elaborators, term
elaborators, and batch Meta clients natural users of the API.

When already inside Grind, the adapter runs in the existing `GoalM`, whose
underlying monad is the same `SymM`. This permits shared canonicalization and
classification state without making every standalone call create a theorem
prover state.

### Keep the algebraic languages closed

`Sym.Arith` is not an extensible parser framework. Its view kinds and operation
recognizers are fixed by the Lean version. Imports must not change which
operation heads are recognized, which terms become variables, or which
coefficient syntax belongs to a view.

The service remains open in three ordinary ways:

- user types provide instances of the fixed algebraic law classes;
- a caller supplies storage for variables through the existing monad
  interfaces;
- a downstream package converts a public reflected value to its own data type
  and caches that conversion in its own session.

`SymExtension` may allocate typed state used by a fixed symbolic module. It
must not become a registry for algebraic grammars, recognition callbacks, or
downstream algorithms.

An operation outside a selected fixed language becomes a variable. A
downstream package may perform a proved source translation before reification.
That translation is not installed into Lean's recognizer.

### Keep algorithms outside the reflection service

The public service classifies, reifies, normalizes its fixed languages, and
constructs interpretation proofs. It does not discover determinant,
factorization, exact-division, gcd, or matrix providers. Those capabilities
belong to downstream libraries.

This distinction keeps Lean's result deterministic under imports and prevents
the symbolic session from becoming a general computer algebra dispatcher.

### Share typed views, not one universal expression type

The original `Lean.Expr` remains the shared source expression. `SymM` and a
small algebraic session cache typed views of it. Ring, semiring, rational,
additive, module, and natural-exponent expressions remain specialized types
with their own interpretation theorems.

A conversion operates directly on a typed view. It does not denote a Lean
expression and send that expression through a second parser. Lean provides
stable view and variable identities so downstream packages can key their own
conversion caches.

## Goals

The migration milestone should provide:

- one ring and semiring reifier used by both `Sym.Arith` and Grind;
- one authoritative classification and operation-expression cache;
- reusable characteristic-aware polynomial normalization and equality proof
  construction in `Sym.Arith`;
- Grind adapters which preserve current e-graph and solver behavior;
- deletion of the corresponding duplicate Grind implementations;
- differential tests establishing current behavior before and after the
  change.

After the migration milestone, later work should provide:

- a supported standalone session over `SymM` with default variable storage;
- single-expression and batch reification entry points;
- stable access to classified structure data, variables, and reflected
  expressions;
- direct, cached conversion from reflected expressions to normalized
  polynomials;
- equality proofs between a canonical source expression and a denoted or
  normalized result;
- delayed proof construction where this materially reduces allocation;
- structured unsupported, resource-limit, and internal-error results;
- fixed follow-up views for rational expressions, additive expressions,
  modules over general scalar rings, and symbolic natural-valued exponents;
- complete standalone access to the existing noncommutative reflection and
  normalization facilities.

## Non-goals

The proposal does not ask Lean to provide:

- determinant, rank, characteristic-polynomial, gcd, or factorization
  algorithms;
- Mathlib's algebraic hierarchy;
- a provider registry for computational types;
- a registration API for view kinds, syntax recognizers, or coefficient
  evaluators;
- automatic execution of expensive algebraic algorithms in Grind;
- a public interface to Grind's constraint rows, basis, queues, or splitting
  state;
- one inductive syntax covering every algebraic theory;
- a namespace migration for every existing kernel-facing theorem in the first
  change.

## Standalone session

This section describes work after the Grind migration milestone. The
standalone session is not part of the initial relocation and deletion work.

The low-level `Sym.Arith` functions should remain compositional over their
current monad classes. Most downstream users should also receive a supported
default session.

An illustrative shape is:

```lean
namespace Lean.Meta.Sym.Arith

structure SessionConfig where
  expThreshold : Nat := 8
  limits       : Limits := {}

structure Atom where
  expr : Expr

structure SessionState where
  atoms       : Array Atom := #[]
  atomMap     : PHashMap ExprPtr Var := {}
  viewCache   : ViewCache := {}
  polyCache   : PolyCache := {}
  proofCache  : ProofCache := {}

abbrev SessionM := StateRefT SessionState SymM

def SessionM.run (config : SessionConfig) (x : SessionM α) : MetaM (α × Snapshot)

def reifyRing
    (expectedType : Expr) (e : Expr) : SessionM (Result RingView)

def reifyRingBatch
    (expectedType : Expr) (es : Array Expr) : SessionM (Result (Array RingView))

end Lean.Meta.Sym.Arith
```

These names are illustrative. The important decisions are the state lifetime,
batch sharing, fixed result languages, and separation from `GoalM`.

The default `MonadMkVar` implementation interns the canonical variable
expression in the session. `MonadGetVar` reads the same array. The proof API
relies on this lawful pairing. Low-level callers may provide their own monad
instances, but the proof-producing runner does not treat arbitrary variable
assignments as trusted evidence.

The session is invocation-local. It may contain local declarations and Lean
expressions, so it is never placed in a process-global cache.

## Batch behavior and cache identity

Batching is a downstream requirement and begins only after Grind uses the
shared implementation. It must not affect the scope of the migration changes.

Batch entry points are required for matrices and systems of equations. All
expressions in a batch share:

- canonicalized carrier and structure instances;
- one type-classification result;
- one variable environment per sort;
- cached operation expressions;
- normalized polynomial conversions;
- proof reconstruction caches.

A cache key includes the source expression, fixed view kind, canonical carrier,
exact structure instances, variable environment, and relevant configuration.
Expression identity alone is insufficient when a carrier has several
algebraic instances.

Variable identifiers remain stable for the session lifetime. A downstream
package that needs `Fin n` variables first reifies the whole batch, then seals
the variable environment once. It can cache the resulting conversion without
changing `Sym.Arith`.

## Normal forms and proof production

### Current boundary

`Sym.Arith` currently reifies and denotes expressions. The round-trip tests
establish definitional equality after canonicalization, but a standalone
consumer still needs an API which proves equality with a computed polynomial
normal form.

Grind already has the necessary kernel-facing reflection theorems and a
proof-producing normalizer. The reusable part should move behind
`Sym.Arith` interfaces. The constraint-solver part remains in Grind.

### Post-migration public result

The following result design belongs to Part II. Part I can preserve the
existing internal inputs and outputs while relocating their implementations.

A normalized view records:

- the canonical source expression;
- the classified algebraic domain;
- the reflected expression;
- the variable environment;
- the normalized polynomial or noncommutative normal form;
- sufficient provenance to construct an interpretation equality.

A caller may inspect and convert the normalized value without immediately
constructing the final Lean proof. When requested, the service produces a
kernel-checked theorem relating the canonical source to the denoted normal
form. The theorem from the caller's original source to the canonical source is
composed at this boundary.

### What moves out of Grind

The following are general enough for `Sym.Arith`:

- characteristic-aware conversion of one reflected expression to a safe
  polynomial;
- comparison of two normalized expressions;
- proof construction for equality of expressions with equal normal forms;
- proof caches for reflected expressions, monomials, and polynomials;
- noncommutative normalization equality proofs;
- semiring-envelope interpretation needed by standalone normalization.

The following remain Grind-owned:

- equality and disequality constraints derived from hypotheses;
- polynomial derivation histories for basis simplification and
  superposition;
- unsatisfiability proofs which combine several input facts;
- propagation into the e-graph;
- inverse case facts, split requests, and solver scheduling;
- solver-specific step counts and basis limits.

This boundary permits `ring`-like normalization without exposing or copying
Grind's decision procedure.

## Grind unification

### Reification adapter

Grind should invoke the shared `Sym.Arith` recognizer. Its monad instances
adapt the variable operation to existing behavior:

1. canonicalize using Grind's current equality information;
2. internalize the variable expression when required by the e-graph;
3. allocate or find the ring variable;
4. record Grind's term-to-ring identifier;
5. mark the solver term;
6. retain the information used by proof reconstruction.

The shared recognizer does not know that these steps exist. After the
migration, a standalone session can implement the same `MonadMkVar` request
with a local map.

The e-graph generation used when Grind internalizes an atom is adapter state,
not an input to algebraic recognition. A Grind-local reader or equivalent
context carries it to `MonadMkVar`; the shared `MonadMkVar` interface does not
need a generation parameter. A transitional adapter may project Grind's ring
state into the shared ring state and copy updated operation caches back.

### Classification state

`Sym.Arith.State` in the underlying `SymM` should be the authoritative cache
for algebraic classification and operation expressions. Grind's ring solver
stores only its additional per-domain constraint state, keyed by the shared
classification identity or another stable domain identifier.

During migration, an adapter may project the shared classification into the
existing Grind structure. The final state must not keep two independently
updated copies of structure instances and cached operation functions.

The present `Sym.Arith` classifier is not yet a behavioral replacement for
Grind's classifier. Before any classifier call site moves, copy Grind's exact
classification behavior into `Sym.Arith`, including its fast path and instance
registration for semiring envelopes, conditional characteristic and
no-natural-zero-divisor evidence, and `PowIdentity` discovery. Leave Grind on
its original classifier while the two paths are compared.

Do not make this initial copy configurable. After Grind uses the shared
classifier and the duplicate has been deleted, a later change may factor
these choices behind explicit flags whose defaults preserve Grind's behavior.

### Behavioral parity

The shared recognizer and the existing Grind recognizer differ in small
details, including assumptions about numeral canonicalization. Migration
requires differential tests for every currently supported form before the
duplicate is deleted.

Parity covers:

- natural and integer literal encodings;
- casts and their exact instances;
- semiring envelopes;
- positive and zero characteristic;
- commutative and noncommutative structures;
- unsupported top-level terms and nested variables;
- wrong operation instances;
- power limits and power-identity handling;
- variable numbering and denotation;
- the conditions which report issues, and resource limits.

The first migration change should not intentionally change Grind's accepted
language or generated facts. Diagnostic wording may adopt shared,
caller-neutral terminology; exact message text is not a parity requirement.

Core tests are not sufficient evidence for the numeral-recognition boundary.
The shared recognizer assumes canonical literal forms, while the old Meta
recognizer accepts additional raw and wrapped forms. Test the migration against
the package corpus in
[`leanprover/downstream-lean4`](https://github.com/leanprover/downstream-lean4),
as well as focused differential cases for raw literals, metadata wrappers,
nested `OfNat` forms, casts, and generated powers. Downstream testing here is
compatibility validation for existing behavior, not permission to add a
downstream-facing feature to Part I.

## Fixed follow-up views

These views begin only after every Part I criterion holds. Their grammars are
fixed by Lean, and each reuses the post-migration session, variables, caches,
and interpretation proofs.

### Rational expressions

A rational view returns numerator and denominator polynomials plus the
nonzero conditions required by totalized field division. Conditions are
explicit result data. Coefficients remain characteristic-aware rather than
using rationals universally.

### Additive expressions

An additive view recognizes zero, addition, subtraction, negation, integer
multiples, and variables without requiring multiplication. It supports
`abel`-like normalization and provides the additive component used by module
views.

### Noncommutative rings

`Sym.Arith` already classifies noncommutative rings and its `RingExpr`
preserves multiplication order. The follow-up exposes the moved
noncommutative normalizer through the standalone result and proof API. It does
not permit conversion to a commutative polynomial.

### Modules over general scalar rings

A module view is multi-sorted. For `M` over `R`, it records the exact scalar
action and represents a normal form as:

```text
module variable in M |-> scalar normal form in R
```

Scalar normal forms are cached `Sym.Arith` views, not expressions submitted to
another parser. Ambiguous scalar actions produce a diagnostic. Linear solving,
module membership, and syzygies remain downstream algorithms.

### Symbolic natural-valued exponents

Literal natural exponents retain the current polynomial path. An exponent
such as `m + n` receives a nested natural semiring view and remains an
explicit symbolic power. It is not represented as an ordinary polynomial in
`x` and `m`, and normalization must avoid exponential expansion.

## Algebraic law classes

The reflection theorems currently use law classes in `Lean.Grind`. That
namespace does not prevent the Meta implementation from living in
`Lean.Meta.Sym.Arith`.

The general module view will probably require fixed semimodule and module law
classes parameterized by scalar and module types. Add only the laws used by
normalization.

Exact quotient and Euclidean-division interfaces may later support
fraction-free elimination, gcd, and rational simplification. They should be
separate operation and law records. Exact quotient does not imply that a type
offers a Euclidean algorithm. Add either interface to Lean only after several
Lean or downstream consumers demonstrate a stable common contract.

Keep existing law classes in `Lean.Grind` during reifier unification. A later
proposal may move generally useful classes to `Lean.Arith`. A namespace move
is not required for any work in this document.

## Proposed work sequence

The sequence has two parts. Part I is the prerequisite migration. Part II is
all generalization and downstream-facing work. No Part II change is folded
into Part I.

### Part I: migrate current Grind machinery

#### S0. Build the migration inventory and parity harness

Before changing call sites, inventory every declaration or coherent group
which should leave Grind. For each, record its current location,
`Sym.Arith` destination or counterpart, Grind callers, excluded
solver-specific data, and deletion test. Cover the reifiers, safe-polynomial
conversion, algebraic classification and operation caches, normalized equality
comparison and proofs, reusable proof caches, noncommutative normalization
proofs, and semiring-envelope interpretation.

Add a harness which runs both implementations on the same canonical input
with matched variable allocation. Compare success, decline, issues, reflected
expressions up to declared variable renaming, denotation, normalized
polynomials, generated equalities, and kernel checking. Include
characteristic, semiring-envelope, noncommutative, and resource-limit cases.
If necessary, add the smallest test-only entry point and delete it in S3.

Record end-to-end Grind behavior and performance, and classify every existing
difference. S0 adds no batching, public result type, grammar, or downstream
API.

#### S1. Copy reusable Grind machinery into `Sym.Arith`

Copy every S0 item into `Sym.Arith`, leaving Grind and its call sites unchanged.
Where a counterpart already exists, including ring and semiring reification,
fill its parity gaps instead of creating a third implementation. Both paths
must remain independently testable.

The classifier is the first S1 slice. Copy the current Grind implementation
exactly, including semiring-envelope setup, registered instances,
characteristic and no-zero-divisor handling, and `PowIdentity`. Do not add
flags, clean up its policy, or switch Grind during this copy. Switch only after
focused differential classification tests pass.

Preserve the current grammar, inputs, normal forms, proof strategy, issue
conditions, and resource behavior. Diagnostic wording may become
caller-neutral. Abstract a signature only to remove Grind state which the
computation does not use semantically. Do not add modes, accepted inputs, or a
polished standalone result API.

Do not copy constraint bases, hypothesis-derived polynomial derivations,
inverse case reasoning, e-graph propagation, or solver scheduling. Narrow
declarations used only by the later Grind adapter are sufficient.

#### S2. Switch Grind to the `Sym.Arith` copies

Add the minimum Grind monad adapters and switch its call sites to the shared
classification data, operation caches, reifiers, normalizers, and proof
constructors. Keep the originals only for differential testing. The adapters
preserve variable internalization, term identifiers, e-graph markings,
denotation maps, constraint state, and scheduling. No production path may
still call an implementation scheduled for deletion.

#### S3. Delete the unused Grind implementations

After each call-site switch and parity test, delete the old implementation and
its test-only entry point. Remove state fields, imports, and adapters used only
by the duplicate path, while retaining the listed solver-specific code.

Run the Grind test suite and compare runtime, allocation, proof size, and
kernel checking with the S0 baseline. Before deleting a recognizer whose
literal handling differs, run the relevant `downstream-lean4` package builds
and tests against the change and investigate any new failure as a possible
canonicalization or numeral-shape regression. Resolve regressions without
adding a new feature. Part I ends only when every inventory row reaches S3,
Grind uses the `Sym.Arith` implementation, all duplicates are gone, and every
current behavioral difference is accounted for. Part II cannot begin earlier.

### Part II: extend the shared service

#### S4. Add the supported standalone session

Provide the default variable environment, result vocabulary, single-expression
entry points, snapshots, limits, and direct access to classified domains and
reflected values. Use only the ring and semiring languages available at the
end of Part I.

#### S5. Add batch behavior

Add batch entry points, stable session variables, and caches for repeated
expressions. Validate them with a downstream client which reflects a symbolic
matrix, converts its entries to `Hex.MvPoly`, computes a determinant, and
transports the result through interpretation. No matrix algorithm belongs in
Lean.

#### S6. Complete standalone noncommutative normalization

Expose the existing noncommutative semantics through the post-migration
session and proof interfaces.

#### S7. Add conditional rational views

Represent numerator, denominator, and nonzero conditions without invoking a
goal manager.

#### S8. Add additive and general module views

Add the fixed additive view, then introduce only the semimodule or module law
classes needed by the fixed multi-sorted normalizer.

#### S9. Add symbolic exponent views

Reuse the nested natural-number semiring view and retain the literal-exponent
fast path.

#### S10. Reconsider class namespaces and division interfaces

Use evidence from Grind and downstream clients before moving law classes or
adding exact-division and Euclidean-division contracts.

## Validation and acceptance criteria

Part I is complete when:

- Grind calls the `Sym.Arith` ring and semiring recognizer and normalizer;
- the duplicated Grind reifier has been removed;
- each S0 inventory item has one surviving reusable implementation, located
  in `Sym.Arith`;
- Grind retains its existing accepted language, e-graph behavior, and solver
  results;
- current classification, characteristic, semiring-envelope,
  noncommutative, proof, issue-triggering, and resource-limit cases have
  parity, without requiring identical diagnostic wording;
- focused literal-shape tests and the relevant `downstream-lean4` package
  builds and tests show no unexplained compatibility regression;
- Grind's performance has no unexplained regression;
- no standalone-session, batch, rational, additive, module, or
  symbolic-exponent feature is required to complete the migration.

Part II acceptance criteria include:

- standalone reification runs through `SymM` without constructing a `Goal` or
  synthetic `MVarId`;
- Grind and standalone clients call one fixed recognizer;
- importing an unrelated package does not change the fixed algebraic grammar;
- single and batch clients share classification, operation, variable, and
  normalized-view caches;
- two distinct structure instances on one carrier do not share a view;
- normalized results have kernel-checked interpretation equalities;
- proof construction can be delayed until requested;
- an external package uses only supported APIs for a symbolic batch
  computation.

Part I performance evaluation reports Grind runtime, allocation, proof size,
and kernel checking before and after migration on the existing test cases.

Part II performance evaluation additionally reports:

- classification and reification time;
- variable-map and normalized-view cache hits;
- allocation on repeated-subterm and matrix batches;
- proof-term size and kernel checking time;
- standalone `SymM` cost against a fresh mostly-disabled `GoalM`.

## Risks and responses

**Downstream requirements delay the Grind migration.** Treat Part I as a
closed parity project. Do not require batching, a convenience session, a Hex
conversion, or a new algebraic language before deleting the Grind duplicates.
Evaluate those requirements only after the migration completion criteria hold.

**The standalone session duplicates `SymM`.** Keep only algebraic variables,
views, conversions, and proofs in `SessionState`. Expression sharing,
canonicalization, instance caching, and issues remain `SymM` responsibilities.

**`MonadMkVar` becomes a syntax extension.** Invoke it only in the fixed
recognizer's variable branch. Its result is one variable regardless of the
source expression's shape.

**An arbitrary variable implementation invalidates proofs.** Make the
proof-producing runner use a controlled `MonadMkVar` and `MonadGetVar` pair.
Treat the low-level monad classes as an implementation interface, not as
trusted evidence of a denotation theorem.

**Grind loses useful internalization behavior.** Implement that behavior in
the Grind adapter and require differential tests before removing the old
path.

**General proof extraction exposes the constraint solver.** Move only
single-expression normalization and equality proofs. Keep constraint bases,
derivations from hypotheses, and propagation APIs private to Grind.

**`Sym.Arith` becomes a downstream algorithm registry.** Keep view languages
closed and keep determinant, factorization, matrix, gcd, and exact-division
dispatch outside Lean.

**Later views recreate independent parsers.** Require rational, additive,
module, and symbolic-exponent views to reuse `SymM` classification, variables,
and nested view caches. Add each as a fixed first-party language with
interpretation theorems.

This plan completes the direction already present in Lean. It gives Grind a
single reusable implementation, gives downstream packages a small symbolic
session, and avoids constructing a full Grind goal for computations which do
not use congruence closure or proof search.
