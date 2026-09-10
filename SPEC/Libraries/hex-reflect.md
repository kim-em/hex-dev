# hex-reflect (shared algebraic reflection, depends on hex-mv-poly + hex-basic)

`hex-reflect` is the only Hex library which imports
`Lean.Meta.Sym.Arith`. It turns a batch of commutative-ring expressions into
`Hex.MvPoly` values over one sealed variable environment and proves that the
conversion preserves interpretation. It also defines the provider outcomes,
conditions, result records, budgets, and decline reasons used by symbolic Hex
frontends.

This is a specification. It does not add an implementation.

## Boundary

Lean owns the source language. `Lean.Meta.Sym.Arith` canonicalizes Lean
expressions, classifies their algebraic structures, caches the corresponding
operation expressions, recognizes the fixed ring and semiring languages, and
denotes reflected expressions. Hex does not copy those functions and does not
add a second parser for the same language.

Hex owns the invocation-local variable environment, conversion to executable
Hex values, interpretation proofs for those conversions, provider selection,
conditions, and resource accounting. Every direct reference to
`Lean.Meta.Sym.Arith` is confined to this library. Consumers use
`Hex.Reflect` types and functions, so a later Lean API change affects this
adapter rather than every tactic.

The fixed ring language currently recognizes addition, multiplication,
subtraction, negation, natural and integer casts, numerals, and powers with a
literal natural exponent. A subexpression outside that language is one atom.
Importing a Hex provider cannot change this decision.

## H0 scope

This specification extracts H0, "Adopt current `Sym.Arith`", from the draft
shared-tactics plan. H0 consists of the first five items in that draft's
"Work which does not wait for Lean changes" list:

1. Define the Hex session state, provider protocol, conditions, and budgets.
2. Implement `MonadMkVar` and `MonadGetVar` for a standalone batch.
3. Reify ring and semiring expressions with the current Lean functions.
4. Seal one batch environment and convert a reflected commutative-ring
   expression directly to `Hex.MvPoly`.
5. Prove that conversion commutes with interpretation.

The remaining items from that list are consumers of this library, not H0.
Standard scalar providers and closed matrix frontends come later. Symbolic
determinant and characteristic-polynomial frontends belong in
`hex-matrix-tactic`. Factorization dispatch and typed polynomial translations
remain with the factorization libraries.

H0 does not wait for the planned copy-switch-delete migration of Grind's
remaining arithmetic implementation. Nothing in Hex is a prerequisite for
that migration. When Lean changes its API, only the private adapter in this
library changes.

## Dependencies

The computational library has exactly these immediate Hex dependencies:

- `hex-mv-poly`, for `Hex.MvPoly`, its constructors, and evaluation;
- `hex-basic`, for the shared collection utilities used by the session.

It does not depend on determinant, row reduction, characteristic polynomial,
gcd, or factorization libraries. `Lean.Meta.Sym.Arith` is part of the pinned
Lean toolchain rather than a Hex library dependency.

```text
hex-basic ────┐
              ├── hex-reflect ──> symbolic consumers
hex-mv-poly ──┘
```

The direction is deliberate. For example, `hex-matrix-tactic` may depend on
`hex-reflect`, but `hex-reflect` does not know about matrices.

## Session and monad

The standalone form is conceptually:

```lean
abbrev ReflectM := StateRefT Hex.Reflect.State Lean.Meta.Sym.SymM
```

A public operation is polymorphic over the capabilities it uses. It must not
fix a transformer order that prevents a future adapter from running the same
operation over Grind's existing `GoalM`. A standalone invocation calls
`SymM.run` exactly once around the whole batch. A Grind caller uses the
`SymM` already below `GoalM` and never starts a nested `SymM.run`.

The Hex state stores:

- the current growing or sealed atom environment;
- the selected `Sym.Arith` classification identity for each active view;
- reflected-view and converted-value caches;
- provider selections and their exact instance expressions;
- conditions and their provenance;
- initial, remaining, and consumed budgets;
- structured declines and failures.

It does not copy `Sym.Arith.State` records. In particular, an active
commutative-ring view stores the ring ID returned by `classify?`. Its
`MonadRing` and `MonadCommRing` implementations read and update the
corresponding entry in `Sym.Arith.State`. The cached operation expressions in
`Functions.lean` therefore remain authoritative in `SymM`.

The same rule applies to semiring views. Hex supplies the monad instances
needed to call the current reifier, but the instances refer to Lean's
classification state rather than maintaining a second classification cache.

### Lifetime and metavariables

A session belongs to one tactic invocation or one programmatic batch. It may
contain free variables and other expressions valid only in the current local
context. It is never stored in a process-global cache, and a result containing
Meta expressions is not reused after that local context ends.

Before cache lookup or pointer-based operation recognition, an entry point:

1. instantiates assigned metavariables in the source expression, carrier, and
   requested structure data;
2. declines if any relevant metavariable remains unresolved;
3. canonicalizes the carrier and source expression with `Sym.canon`;
4. calls `Sym.Arith.classify?` on the canonical carrier;
5. uses the exact instances recorded in that classification.

This ordering is required because the current reifier compares operation
instances with cached canonical expressions using pointer equality. Calling
it on raw syntax is not supported. A cache entry may not survive a later
metavariable assignment by treating the old expression as a stable key.

## Atom allocation

The standalone `MonadMkVar` implementation canonicalizes the proposed atom in
the same `SymM`, interns it in the growing environment, and assigns consecutive
`Nat` identifiers. The environment contains both an array from identifier to
canonical source expression and a map from canonical expression identity to
identifier. Repeated canonical atoms receive the same identifier.

`MonadGetVar` reads the same array and reports an internal failure for an
invalid identifier. The proof-producing runner always installs this lawful
pair. The monad classes are storage interfaces, not proof assumptions and not
syntax-extension points.

Atom identity in a standalone session is identity of the canonical Lean
expression under `SymM` sharing. It is not pretty-printed text, a user-facing
name, or definitional equality tested independently for every lookup. A future
Grind adapter may use an e-graph representative, provided it retains the proof
which relates that representative to the source expression.

## Batch reification and sealing

A batch has two phases.

1. While the environment is growing, canonicalize and reify every input with
   the selected view. `reifyRing?` is called with top-level variables enabled,
   so an otherwise unrecognized ring-valued expression becomes one atom.
2. Seal the environment once at size `n`. Convert every stored variable index
   to the corresponding `Fin n` and convert every reflected input against that
   same environment.

No `Hex.MvPoly` conversion is available before sealing. No new atom may be
allocated after sealing. A variable identifier outside `n` is an internal
failure, not a value reduced modulo `n`.

A matrix frontend passes all entries as one batch. It must not invoke the
single-expression runner once per entry, because that would give equal atoms
different numberings and make polynomial matrix operations meaningless. An
empty batch seals at `n = 0`.

The sealed result retains the ordered atom array. This is both presentation
data and the valuation used by the interpretation theorem. Reordering or
dropping unused atoms requires an explicit renaming and its proof. It is not a
cache optimization.

## Recognition details

### Exact instances

The reifier accepts an operation only when its instance argument is the cached
canonical operation instance for the classified domain. A different addition,
multiplication, cast, or power instance on the same carrier is not silently
accepted. Provider lookup uses the same exact instance expressions.

### Casts and coefficients

Natural and integer casts are recognized only through the exact cached cast
functions and only when the source value has the literal form accepted by the
pinned reifier. Other casts become atoms. Conversion keeps `.num`, `.natCast`,
and `.intCast` distinct until the characteristic-aware normalization theorem
justifies their coefficient value.

A coefficient provider supplies an executable coefficient type, a map from
reflected integer coefficients, an interpretation into the source carrier,
and the laws needed by `Hex.MvPoly.eval₂`. There is no universal rational
coefficient type.

### Characteristic

`Sym.Arith.CommRing.charInst?` contains the exact `IsCharP` proof and
characteristic when Lean can synthesize them. When it is present, conversion
uses `Lean.Grind.CommRing.Expr.toPolyC` and its `denote_toPolyC` theorem,
including the `c = 0` case. Otherwise it uses `Expr.toPoly` and
`denote_toPoly`.

The characteristic, the proof expression, the coefficient provider, and the
coefficient interpretation are part of conversion identity. A polynomial
normalized modulo one characteristic is never reused for another carrier or
another `IsCharP` instance.

### Powers

Only literal natural exponents recognized by `reifyRing?` are polynomial
powers. A symbolic exponent makes the whole power application an atom. The
reflection-node, exponent, output-term, and proof-reconstruction budgets are
checked before an accepted literal power can cause excessive expansion.

### Division and other operations

The current ring reifier has no division or inverse node. Division,
inversion, transcendental functions, and any other unrecognized operation
become atoms. For example, `x / y` is one atom rather than a rational
expression and is not assigned a nonzero hypothesis.

Hex does not parse inside such an atom. A later conditional rational view must
come from a fixed Lean view. H0 does not implement a temporary rational,
additive, module, or symbolic-exponent parser.

## Direct conversion to `Hex.MvPoly`

The conversion consumes the reflected value directly. It never denotes a
`Lean.Expr` and submits that expression to another parser.

For a sealed environment of size `n`, the initial conversion path is:

1. normalize `RingExpr` with `Expr.toPolyC c` when characteristic evidence is
   available, and with `Expr.toPoly` otherwise;
2. traverse the resulting `Lean.Grind.CommRing.Poly`;
3. translate each ordered `Nat` variable and exponent to a `Hex.Mono n`;
4. map each integer coefficient through the selected coefficient provider;
5. construct `Hex.MvPoly n C cmp` with its canonical constructors.

The monomial comparator is an explicit requested parameter and is part of the
cache key. The conversion checks every variable bound even though lawful
batch construction already implies it.

The result retains:

- the source reflected expression;
- the sealed atom environment;
- the characteristic choice;
- the coefficient type and interpretation;
- the resulting `Hex.MvPoly`;
- enough data to request the source interpretation proof.

### Soundness theorem

The Mathlib-free library proves a value-level theorem of this shape, with the
actual typeclass arguments made explicit:

```lean
eval₂ coeffInterpret atomInterpret (convert ringExpr sealed) =
  ringExpr.denote sourceContext
```

The theorem is proved from the public `Lean.Grind.CommRing` denotation
theorems and the evaluation laws of `Hex.MvPoly`. Its characteristic-aware
arm uses `Expr.denote_toPolyC`; the other arm uses `Expr.denote_toPoly`.

The Meta proof returned to a caller is assembled as follows:

1. Quote the concrete reflected syntax, sealed environment, and converted
   polynomial.
2. Establish that running the pure conversion on that concrete syntax gives
   the quoted polynomial. This is a kernel equality of finite reflected data,
   discharged by reduction or by kernel `decide`.
3. Apply the general conversion soundness theorem.
4. Use `denoteRingExpr` and definitional equality to relate the reflected
   syntax and atom array to the canonical source expression.
5. Compose with the definitional equality between the caller's instantiated
   source and its canonical form.

Kernel `decide` is not applied to an evaluation equality containing symbolic
atoms. Such atoms can be local variables or opaque terms, so evaluating both
sides is neither an appropriate proof method nor a reliable reduction path.
Only equality of the concrete reflected data is computed. The general
soundness theorem carries the symbolic interpretation.

## Cache identity

A view or conversion cache key contains every choice which can change its
meaning:

- canonical source-expression identity;
- requested view;
- canonical carrier expression;
- exact ring, semiring, addition, multiplication, cast, power, and other
  relevant structure instances;
- coefficient representation and coefficient interpretation;
- characteristic and its exact evidence;
- sealed environment identity and size;
- target monomial comparator and relevant normalization options.

The sealed size is required even when two environments currently share an
atom prefix, because their variable types are `Fin n`. A type name alone is
never a key. Cache hits must compare all semantic fields before relying on
pointer identity for the canonical expression fields.

Caches are invocation-local. They may retain local declarations and canonical
expression pointers without imposing a lifetime discipline on callers.

## Provider protocol

A provider supplies executable operations together with the theorems needed
to interpret them. Provider registration is separate from
`Sym.Arith` recognition. It can change which verified computation handles a
request, but it cannot change the fixed source grammar or atom allocation.

There are two levels:

- theorem-level records, used by Mathlib-free computations, containing
  operations, interpretations, and laws;
- Meta registrations, used to recognize a carrier and its exact instances,
  quote values, construct proofs, and select the theorem-level record.

Providers are small capability records rather than one all-or-nothing
hierarchy. The shared vocabulary initially distinguishes scalar evaluation,
commutative-ring normalization, decidable zero, field operations, exact
quotient, Euclidean division, gcd, extended gcd, univariate factorization,
multivariate factorization, and source-type translation. Algorithms request
only the capabilities they need.

Registration order and explicit priority determine lookup deterministically.
Provider identity includes its declaration name and versioned configuration,
so diagnostics and condition provenance remain stable.

Provider selection has four outcomes:

- `notApplicable`: the provider does not recognize this request;
- `declined`: it recognizes the request but cannot satisfy a stated condition
  or budget;
- `success`: it returns checked data and proof provenance;
- `failure`: its registration, quoted value, or evidence is malformed.

Dispatch may continue after `notApplicable`. A frontend may continue after
`declined` only when its documented fallback policy permits it. A `failure` is
reported immediately. Search exhaustion is a decline, never a proof that a
mathematical object does not exist.

## Shared results and conditions

All symbolic frontends use the result records from `Hex.Reflect`.

An unconditional equality result contains the source expression, result
expression or quoted value, an equality proof, and presentation data such as
the sealed atom environment. It contains no hidden assumptions.

A conditional equality result contains:

- the transformed expression or quoted value;
- an ordered list of proposition expressions;
- a theorem proving the equality under exactly those propositions;
- provenance for each condition.

Provenance identifies the provider, source subexpression, operation, and
reason that introduced the condition. Deduplication uses provenance together
with canonical proposition identity. It preserves the first occurrence, so
side-goal order and diagnostics are deterministic. Reification into
independent variables never implies that an atom is nonzero. Any consumer
which needs a pivot, denominator, or minor to be nonzero must return that fact
as a condition.

A tactic processes conditions in this order:

1. definitional equality and matching local hypotheses;
2. explicitly configured cheap normalizers;
3. facts already known to the current Grind goal, when applicable;
4. side goals, only if the frontend contract permits them;
5. otherwise, decline without changing the goal.

Term and programmatic interfaces return unresolved conditions instead of
creating goals.

A property result contains the computed display value, the
library-specific property, and either a checked certificate plus its soundness
theorem or a direct correctness theorem. It may also contain conditions. A
failed certificate is never replaced with a weaker claim about the display
value.

Every successful or declined expensive request reports its consumed budget.

## Budgets and declines

The common budget has independently bounded dimensions for:

- source syntax nodes and batch entries;
- atoms in the growing environment;
- reflected nodes and literal exponent size;
- converted monomials and polynomial terms;
- coefficient size;
- proof-reconstruction nodes and quoted expression size.

Consumers may extend it with dimensions such as matrix size, factor-search
effort, or case splits. Nested operations debit the caller's budget rather than
starting an unbounded child budget. A check occurs before an operation whose
cost can exceed the remaining amount. Exhaustion returns a decline containing
the dimension, limit, consumed amount, and requested increment.

Shared decline reasons distinguish at least unsupported view, unsupported
carrier, unresolved metavariable, missing capability, ambiguous provider,
unsupported source type, and budget exhaustion. An unrecognized operation
inside a valid ring expression is normally an atom, not a decline. Invalid
provider evidence, an out-of-range sealed variable, and an ill-typed generated
proof are failures rather than ordinary declines.

Diagnostics name the requested operation, carrier, exact relevant instances,
provider, unsupported source location, outstanding conditions, and consumed
budget where applicable. A batch consumer adds its own location, such as a
matrix entry index.

## Mathlib companion

The companion is specified in
[hex-reflect-mathlib](hex-reflect-mathlib.md). It supplies translations for
Mathlib carriers and relates the conversion to
`MvPolynomial (Fin n) R`. It contains no determinant, row-reduction,
characteristic-polynomial, gcd, or factorization algorithm.

## First consumers and parser adoption

The first symbolic consumers are `det` and `char_poly` in the planned
`hex-matrix-tactic` library. They reify all entries in one batch, run the
existing verified matrix algorithm over `Hex.MvPoly`, and interpret the result
through this library's soundness theorem. The characteristic-polynomial
variable remains the `DensePoly` variable. It is not added to the environment
of matrix-entry atoms.

The three existing structural polynomial parsers have different futures:

- `HexRCF/Reify.lean` contains the duplicate parser for scalar ring syntax.
  Its ring-structural part is the parser this library is intended to replace.
  H0 does not remove it, because the current RCF frontend also recognizes
  rational coefficients and division by a closed nonzero scalar. Migration
  waits for proved scalar preprocessing or Lean's fixed rational view. The RCF
  quantifier, Boolean-formula, denominator-clearing, and certificate code stays
  in `hex-rcf`.
- `HexPolyZMathlib/PolyParse.lean` parses values of the source type
  `Polynomial R` into `Hex.ZPoly`. It is a typed polynomial translation, not a
  parser for scalar ring expressions, and stays until the factorization
  frontend adopts a proved typed translation.
- `HexCharPolyMathlib/CharPolyElab.lean` parses a user-supplied
  `Polynomial Int` result and constructs its existing characteristic-polynomial
  certificate. It stays until `hex-matrix-tactic` replaces that frontend's
  literal and result reconstruction. `hex-reflect` does not parse
  `Polynomial.X` or `Polynomial.C` as part of its scalar language.

No parser is deleted as part of this documentation issue or H0 itself.

## Pinned Lean declaration audit

This audit is against `leanprover/lean4:v4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. All paths below are relative to
`src/lean/Lean/Meta/Sym/Arith/` unless stated otherwise.

The current API is available in the pinned toolchain but remains unstable.
Lean's pending Grind migration may change names, types, namespaces, and
behavior. Public here means visible from the module, not promised stable by
Lean.

| File | declarations checked for the H0 boundary | status in the pinned source |
| --- | --- | --- |
| `Types.lean` | `RingExpr`, `SemiringExpr`, `Ring`, `CommRing`, `Semiring`, `CommSemiring`, `ClassifyResult`, `getArithState`, `modifyArithState` | Public. The expression types are abbreviations for `Lean.Grind.CommRing.Expr`; all are unstable. |
| `Classify.lean` | `classify?` | Public and cached in `Sym.Arith.State`; unstable. `getIsCharInst?`, `getNoZeroDivInst?`, and every `try*` helper are private and must not be used. |
| `MonadCanon.lean` | `MonadCanon`, `canonExpr`, `MonadCanon.synthInstance` | Public monad interface; unstable. H0 supplies the standalone implementation with `Sym.canon` and `Sym.synthInstance?`. |
| `MonadRing.lean` | `MonadRing`, `MonadCommRing`, `getRing`, `modifyRing`, `getCommRing`, `modifyCommRing` | Public monad interfaces; unstable. Their generic lift instances are public. |
| `MonadSemiring.lean` | `MonadSemiring`, `MonadCommSemiring`, `getSemiring`, `modifySemiring`, `getCommSemiring`, `modifyCommSemiring` | Public monad interfaces; unstable. Their generic lift instances are public. |
| `MonadVar.lean` | `MonadMkVar`, `mkVar`, `MonadGetVar`, `getVar` | Public monad interfaces; unstable. The lawful standalone pairing is owned by Hex. |
| `Functions.lean` | `getAddFn`, `getMulFn`, `getSubFn`, `getNegFn`, `getPowFn`, `getIntCastFn`, `getNatCastFn`, `getAddFn'`, `getMulFn'`, `getPowFn'`, `getNatCastFn'` | Public cached getters; unstable. `checkInst` and all `mk*Fn` helpers are private. Hex normally reaches the getters through reification and denotation. Public `getInvFn` was checked but is not used because division and inversion are atoms. |
| `Reify.lean` | `reifyRing?`, `reifySemiring?` | Public partial definitions; unstable. Both require caller-supplied monad instances. The two reporting helpers are private. |
| `DenoteExpr.lean` | `denoteRingExpr` | Public; unstable. `denoteRingExprCore` is private and must not be used. Public `denotePoly` is not needed by the initial proof route. |
| `ToExpr.lean` | `ofRingExpr` and the `ToExpr Lean.Grind.CommRing.Expr` instance | Public; unstable. They quote the concrete reflected syntax used by proof reconstruction. |
| `VarRename.lean` | no required declaration | Public `Lean.Grind.CommRing.Expr.renameVars` and `Expr.collectVars` were checked. They remain in the Grind namespace and are optional utilities, not substitutes for sealing checks. |
| `Poly.lean` | no required declaration | Its public `Lean.Grind.CommRing.Mon` and `Poly` utilities were checked. The initial conversion instead uses the normalization functions and soundness theorems in `Init/Grind/Ring/CommSolver.lean`. |

`Lean.Meta.Sym.SymM`, `SymM.run`, and `Sym.canon` are checked in
`Lean/Meta/Sym/SymM.lean` and `Lean/Meta/Sym/Canon.lean`. They are outside the
`Arith/` directory but are part of the required execution boundary.

The pure normalization and soundness declarations used by conversion are
`Lean.Grind.CommRing.Expr.toPoly`, `Expr.toPolyC`,
`Expr.denote_toPoly`, and `Expr.denote_toPolyC` in
`src/lean/Init/Grind/Ring/CommSolver.lean`. They are public under that file's
`@[expose] public section`, but their namespace and representation are also
unstable until the Grind migration is complete.

`EvalNum.lean` was inspected because classification uses its public
`evalNat?`. H0 does not call `evalNat?` or `evalInt?` directly. The
`ToExpr.lean` quoting instance is only for concrete syntax. It is not the
semantic proof boundary.

## Verification requirements

An implementation is accepted only when all of the following hold:

- a standalone batch enters `SymM.run` once, while a test adapter over a richer
  monad uses no nested run;
- canonicalization occurs before classification, cache lookup, and reification;
- unresolved relevant metavariables decline before state is cached;
- repeated atoms share one index, different atoms remain different, and every
  batch result uses one `Fin n`;
- wrong operation instances become atoms and do not reuse a view cached for a
  different instance;
- characteristic-zero, positive-characteristic, casts, literal powers,
  symbolic powers, division-as-atom, and empty-environment cases exercise the
  soundness theorem;
- conversion proof tests use concrete reflected-data equality plus the
  soundness theorem, with no kernel decision of symbolic evaluation;
- cache tests distinguish every field listed under "Cache identity";
- conditional-result tests preserve order and deduplicate by provenance;
- budget exhaustion is a decline with exact usage, and malformed evidence is a
  failure;
- importing a provider changes provider selection only, never the
  `Sym.Arith` view;
- source imports show immediate Hex dependencies only on `HexMvPoly` and
  `HexBasic`, consistent with `scripts/check_dag.py`;
- no `native_decide`, axiom, alternate ring parser, or copied Grind reifier is
  introduced.

## Explicitly deferred work

H0 does not provide rational, additive, module, noncommutative, or symbolic
exponent source views. It does not implement symbolic matrix frontends,
factorization adapters, rational-expression tactics, Grind propagation, or
case splitting. It does not ask Lean to change `Sym.Arith` and does not depend
on the tentative API proposed in the draft `SPEC/lean4-sym-arith.md`.

Those features may consume the session and result protocol later. They may
not add temporary `Lean.Expr` parsers while waiting for fixed Lean views.
