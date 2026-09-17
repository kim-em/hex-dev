# hex-poly-det-mathlib

The symbolic arm of the `det` tactic: a second handler attached to the
`det` syntax kind that [hex-bareiss-mathlib](../../HexBareissMathlib/SPEC/hex-bareiss-mathlib.md)
owns, accepting a Mathlib matrix whose entries are ring expressions,
certifying the determinant of the reified polynomial matrix through
[hex-poly-det](hex-poly-det.md), and closing `A.det = e` against the
user's expression. It is the Mathlib companion of hex-poly-det and the
determinant analogue of
[hex-generic-rank-mathlib](hex-generic-rank-mathlib.md). It lives here and
not in hex-bareiss-mathlib because that library is a published mirror
whose import closure may not reach hex-reflect, hex-reflect-mathlib or
hex-mv-gcd (`scripts/release/check_released_manifest.py`,
`published_import_closure_violations`); the generic witness and checker
stay in hex-bareiss, and the numeric `det` stays in hex-bareiss-mathlib.

Dependencies: `HexPolyDet`, `HexBareissMathlib`, `HexReflect`,
`HexReflectMathlib`, `HexMvPolyMathlib`, `HexMatrixMathlib`, plus Mathlib;
not `correspondence_only`, since it implements a handler and owns proof
probes. Implementing the packed arm additionally depends on
`HexKroneckerMathlib` for product-check soundness; register that downward
dependency when the planned library is implemented. This SPEC-only amendment
changes neither the library registry nor the released manifest.

## Input and dispatch

- **Any commutative ring as the target.** Determinant transport is
  `RingHom.map_det`, which needs no injectivity, so the user's carrier `F`
  is any `CommRing`; `CharZero` is unnecessary for this transport. With integer coefficients the arm is sound
  over every commutative ring and complete over rings without additive
  torsion; in characteristic `p` a true goal can be declined when `d` and
  the target agree only modulo `p`, which the residue provider and the
  residue list form remove (for primes below `2^31`, the provider's
  range). The certificate fragment is: a square literal over any
  commutative ring whose entries and target are ring expressions in the
  same atoms, with fixed natural exponents, within the reflection budgets.
  `norm_det` followed by `ring` also closes targets that mention atoms
  absent from the matrix (`x + y - y`) and identities with variable
  exponents (`2 * 2 ^ m`), which this arm declines; those inputs are
  preserved only through the fallback, which is scope kept, not scope
  won.
- **Closed forms first.** For `n ≤ 3` the handler does not reify: for
  `!![…]` and `Matrix.of ![…]` literals it rewrites with Mathlib's
  `Matrix.det_fin_two_of` / `Matrix.det_fin_three` (and `det_fin_one_of`,
  `det_fin_zero`); for `fun i j => …` and `Matrix.ofArray` inputs and
  unfolded definitions it uses the general `det_fin_two` / `det_fin_one`
  and reduces the entry accesses explicitly; then it closes with `ring`.
  The small-size `det%` returns the closed-form value with that proof,
  since this route has no batch and no polynomial `d`. This is where the
  certificate route pays reification and packing costs it cannot amortise
  and where the first pilot lost to `norm_det`; the probes measure the
  closed-form route on the `2 × 2` and `3 × 3` rungs against `norm_det`
  rather than assuming it wins.
- **Opt-in until measured.** The symbolic handler is not placed in the
  default `Hex.norm_det` fallback chain. It ships as the `det` handler and
  `det%` term form for symbolic input, and enters the simp-set chain only
  for the size regime where the sweep below shows a win, if one exists.

### Certificate routes

The packed extension applies after the existing numeric and `n ≤ 3` guards.
It leaves the closed-form route and its separate
[small-determinant work](https://github.com/kim-em/hex-dev/issues/10264)
unchanged. For larger symbolic inputs, retain the same reified matrix,
canonical lists and `DetWitness` for either checker. After compiled witness
production, run [the executable preflight](hex-poly-det.md#bounds-and-selection)
on all witness products before emitting the certificate proof. Existing
reflection/producer budgets are checked at their earlier boundaries; the
witness-dependent packing bound cannot be known from matrix entries alone.

| Condition | Route |
|---|---|
| Numeric fragment | Delegate to the existing numeric handler |
| Symbolic `n ≤ 3` | Existing closed form |
| Malformed supplied certificate, including its quotient payload | `failure` |
| Symbolic capability or overall budget unavailable | Existing decline and Mathlib fallback |
| Supported certificate, every packed product within digit/bit limits and covered by the crossover table | `checkDetPolyPacked`, or `checkDetPolyPackedMod` with residue quotients |
| Packing budget exceeded, crossover absent/selects sparse, or residue quotient payload absent | `checkDetPolyList` with the appropriate integer/residue operations |

The packing configuration embeds `Hex.Kronecker.Budget`, with preregistered
limits `65536` dense digits and `16777216` packed bits. Its size report and
mode selection follow hex-poly-det; `signedPacked` requires the independent
Kronecker product crossover evidence. No second kernel attempt runs after a
packed rejection. After preflight, the compiled side validates using the
selected checker on exactly the quoted payload, as specified by hex-poly-det.
An unexpected `false` is a hard certificate failure before proof emission;
it is not a budget decline. The optional quotient preparation is compiled,
budgeted work; inability to afford it selects residue lists before proof emission.

When packing exceeds a limit, use the diagnostic
`det: packed certificate declined: dense box requires <D> digits and <N> packed bits (limits <Dmax> digits, <Nmax> bits); using term lists`.
Include the product row, per-atom degrees, and `limitingStage`; saturated
bounds print `at least <limit + 1>`. Missing crossover coverage or missing
quotients have distinct reasons (`no measured packed regime` or
`residue quotient payload unavailable`). These are declines of the packed
arm, not of the entire symbolic attempt when the list checker succeeds.
If residue lists are unavailable too, use the existing carrier decline.

The certificate trace records `term-list`, `packed/plain`, or
`packed/signedPacked`, plus integer/residue encoding, each product's
`SizeBound`, quotient support where present, and any packing-decline reason.
Retain the existing `closed-form` and `fallback` routes. Trace the chosen
checker in tactic, term and simproc forms, including composed fallbacks, so
the sweep cannot count a sparse or Mathlib success as a packed success.

## Prerequisites and input classification

The shared prerequisites are the same as
[hex-generic-rank-mathlib §Prerequisite changes](hex-generic-rank-mathlib.md#prerequisite-changes-in-other-libraries):
canonical list arithmetic in hex-mv-poly and its denotation theorem in
hex-mv-poly-mathlib block the kernel route (the list form has landed);
the numeric handlers' `throwUnsupportedSyntax` refactor has landed
(https://github.com/kim-em/hex-dev/issues/10230); and the residue coefficient
provider in hex-reflect-mathlib blocks positive characteristic. The
polynomial producer generalisation belongs to hex-bareiss, its determinant
soundness to this companion. These are implementation obligations, not
claims that the proposed declarations already exist. Both residue checker
arms also require #10257's canonical residue lists, validity, equality and
nonzero tests. Supplying quotient polynomials does not remove that dependency.

Two frontend adaptations are also required: a proved pass clearing closed
rational coefficients, and batch quotation using the canonical list
layer's denotation constructor. Neither is provided by the current ring
reifier. They belong to the symbolic frontend and its reflection bridge;
they do not extend hex-reflect's fixed ring language with symbolic division.
This library imports `HexReflect`, `HexReflectMathlib`, `HexMvPolyMathlib`
and, through `HexPolyDet`, `HexMvGcd`; hex-bareiss and hex-bareiss-mathlib
import no polynomial provider. The `det` syntax kind remains owned by
`HexBareissMathlib/Tactic.lean`; this library's handler attaches to it
without redeclaring the syntax, and answers `throwUnsupportedSyntax` for
input outside its fragment.

Input classification is shared with
[the symbolic `rank` arm](hex-generic-rank-mathlib.md#input-classification).
Handler order is registration order in reverse, so a handler registered by
this library runs *before* hex-bareiss-mathlib's numeric handler and its
diagnostic fallback. The symbolic handler therefore begins by classifying
the numeric fragment itself and throws `throwUnsupportedSyntax` for it, so
numeric inputs reach the numeric handler with no symbolic work, exactly as
`HexGenericRankMathlib/Tactic.lean` does for `rank`; it is registered with
`@[tactic HexMatrixMathlib.Det.detTac, no_fallback]`. The term form has its
own registration on `HexMatrixMathlib.Det.detTerm` with the same numeric
guard, since the numeric `det%` elaborator raises an ordinary error on its
`notApplicable` rather than delegating; the two elaborators never both
run on one input. For a square literal of dimension at most three the
symbolic handler takes the closed-form route above and never reifies. Otherwise it reads the square matrix through the
shared literal layer, including definitions
unfolded within budget. It canonicalises and reifies all entries with
`reifyRing?`, with top-level variables enabled, in one hex-reflect batch.
For symbolic `fun` and `Matrix.ofArray` inputs, literal recognition is
shared but proof identification uses finite extensionality and the batch's
entry interpretation proofs, with structural unfolding of the literal's
indexing. It must not use the numeric `entriesEq`/`decide` route, which
requires reducible `DecidableEq F`. No equality decision on symbolic values
is needed; these entrywise identification proofs are measured separately.
The batch seals its environment at `k` atoms, converts with the
characteristic-aware conversion when `Sym.Arith` supplies the characteristic
and the plain conversion otherwise, and uses `cmp := Hex.Mono.grevlex`.
It yields

```text
P : Hex.Matrix (Hex.MvPoly k C cmp) n n
v : Fin k → F
ι : C →+* F
```

and an interpretation proof `eval₂ ι v P[i, j] = A i j` for every entry.
Here `F` is the user's carrier and `C` the coefficient provider's carrier.
Routing is by the converted polynomials: any nonconstant entry selects the
symbolic arm; if all entries convert to constants after cancellation, the
same arm handles the resulting constant matrix, even with `k > 0`.

Atoms are independent indeterminates. Expressions outside the fixed ring
language, including `x / y`, opaque constants, `Real.exp t` and symbolic
powers, become atoms. No hypotheses or algebraic relations between atoms
are used: `hx : x = 0` does not change the polynomial for `x`. Atomisation
can prove polynomial identities involving these terms, but cannot prove
relations between them. The budgets are hex-reflect's (atoms, terms,
coefficient bits and proof nodes), plus matrix dimension and certificate
size; exhaustion returns `declined` naming the exhausted budget.

In equality mode the user's expression `e` is reified in the same batch,
using the matrix's atoms. Record the atoms allocated by the entries;
reifying `e` must not allocate additional atoms. Seal once after both have
been reified and convert both with that sealed environment. An expression
which cannot be reified as a ring expression in those atoms declines with
`det: symbolic determinant declined: target is not a ring expression in the matrix atoms`.
This includes an opaque term appearing only in `e`.

## Kernel certificate and soundness

The compiled producer returns transform rows and a value `d : MvPoly k C cmp`,
or a polynomial left kernel vector with value zero. Its meaning is always
`Hex.Matrix.det P = d`, including when the determinant is identically zero;
a matrix which becomes singular only at some atom valuations still has a
nonzero polynomial determinant. All witness entries lie in the polynomial
ring, never in a chosen specialisation or in the fraction field.

The term-list arm checks `checkDetPolyList` on the row lists of canonical
polynomial term lists and the witness in the same representation. Coefficients are
encoded by `Int` for the integer arm and canonical `Nat` residues for the
residue arm; exponent vectors are lists of `Nat`. Shape, canonicality,
nonzero diagonals, vanishing products and the determinant value identity
are checked as specified on the executable side. In particular the final
value check uses `l₀ = 1`, `lᵢ₊₁ = uᵢ` and `d = sign σ * uₙ₋₁`
(`d = 1` when `n = 0`), without expanding the product of pivot polynomials.
Polynomial equality uses the list layer's `beq_iff` contract, not evaluation at sample points.

The existing `checkDetPolyList_sound` in this library identifies a passing
check with `Hex.Matrix.det P = d`, where `P` and `d` denote the supplied
lists and `Hex.Matrix.det` is the Leibniz reference. It uses the list
arithmetic denotation theorem, `HexMatrixMathlib.det_eq`, row permutation
signs and the triangular determinant lemmas, just as `det_eq_of_checkList`
does. Require `[CommRing C] [IsDomain C] [DecidableEq C]` on the
coefficient carrier, in addition to the producer's lawful GCD/order context.
Transport through `HexMvPolyMathlib.equiv` to `MvPolynomial (Fin k) C`,
whose existing domain instance supplies cancellation and the singular-vector
argument; no existing `IsDomain (MvPoly …)` instance is assumed. The
transform's diagonal product is nonzero there. Its cancellation is a
propositional argument using the checked adjacent-diagonal equalities, not
an expansion of the product by the kernel. The singular branch uses
`Matrix.exists_vecMul_eq_zero_iff` over that domain to prove determinant zero.
Neither argument requires the vector or diagonal product to stay nonzero after
specialisation.

### Packed soundness

`checkDetPolyPacked_sound` has the same conclusion as
`checkDetPolyList_sound`: a passing check implies `Hex.Matrix.det P = d`
for the denoted input and witness value (zero for `.singular`). It takes
the budget and mode as checker parameters, without trusting a producer
correctness claim or external bound hypothesis. Its integer polynomial
model is a domain; subsequent evaluation transports the conclusion to
**any** commutative ring, without `CharZero` or injectivity at the atoms.

Factor the determinant argument into one statement about the witness
identities: valid shapes and swaps, nonzero transform diagonals and the
row-prefix product equalities with the adjacent-diagonal/value conditions,
or a nonzero vector whose product with the matrix is zero. The list checker
derives these with its arithmetic denotation laws. The packed checker
derives the same identities with
[`checkMulTerms_sound`](../../HexKroneckerMathlib/SPEC/hex-kronecker-mathlib.md#denotation-and-polynomial-model),
instantiated in `MvPolynomial (Fin k) Int` at the indeterminates, and the
existing `HexMvPolyMathlib.equiv` bridge. This shares the permutation,
triangular determinant, cancellation and singular-vector proof above; it
neither re-runs `checkDetPolyList` in the kernel nor duplicates determinant
algebra. Extracting that shared statement from the current `Decode.sound`
is an implementation obligation.

`checkDetPolyPackedMod_sound` uses `checkMulTermsMod_sound` in the residue
polynomial model for each supplemental quotient row. It recovers the
integer identity `M̃ Ã − C̃ = p Q`, then transports to characteristic `p`
through the residue coefficient laws, including
`HexReflectMathlib.residueHom` for target evaluation. The determinant
argument still requires a coefficient domain (prime characteristic for the
residue producer); the final target only needs `CommRing` and `CharP`.
Neither nonzero polynomials nor nonzero transform diagonals are assumed to
remain nonzero after that evaluation. Quotient shape/canonicality/bounds
and the integer identities are checked premises, not producer assertions.

The rational row-clearing route may use the integer packed checker for the
scaled matrix `B`. Target comparison remains the existing canonical-list
comparison (`d = q`, or `t * dB = D * qZ` after scaling), with its existing
budgets and nonzero-scale proof. The term form still avoids comparing its
value with itself. Packing changes witness products only; it does not add
another reification, target normalization or small closed-form solver.

The batch must quote `P` with each entry *defined to be* the canonical
list layer's denotation applied to its quoted entry list. Thus the batch's
`P` and the checker's denoted row matrix contain the same constructor
applications, giving definitional identification without evaluating them.
This is a quotation contract, not a claim that independently constructed
`MvPoly` trees are definitionally equal. Today's `HexReflect/Session.lean`
quotes `ofIntTerms`; the list prerequisite must supply the bridge from
conversion terms to canonical exponent lists and adapt that quotation and
its entry interpretation proofs. A compiled `MvPoly` matrix is still built
for the producer, but its tree representation is never quoted as a second
matrix for the kernel to compare. The denotation lemmas justify list
arithmetic without reducing reference polynomial operations or rebuilding
trees; conversion, quotation and identification costs are recorded in the
proof probes. Every definition on the arithmetic path is `@[expose]`, uses
structural recursion on lists of `Nat`/`Int`, and obeys
[matrix-tactics §Kernel discipline](../matrix-tactics.md#kernel-discipline).
In particular the kernel never evaluates `bareissWith`, `detWitness`, a
reference checker, or `Hex.Matrix.det` on `Hex.Matrix (MvPoly …)`. The
reference determinant occurs in soundness statements only; neither `Array`,
`Vector`, `Fin`, `Finset`, matrix indexing nor well-founded polynomial
arithmetic is reduced to check a certificate. The packed checkers of
[hex-bareiss §Packed evaluation](../../HexBareiss/SPEC/hex-bareiss.md#packed-evaluation)
are sound through `checkDetList_of_packed` and `checkDetRat_of_packed`:
`triangularCheckPacked_eq` and `zeroDotsPacked_eq` identify the packed
walk with the plain one under the entry bounds, by `dotIntPacked_eq` of
[hex-matrix-mathlib §Kronecker-packed dot products](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#kronecker-packed-dot-products),
and the columns of the arranged matrix inherit the bounds of the rows
(`mem_applySwaps`, `columns_bound`); `det_eq_of_checkListPacked'` and
`det_eq_of_checkRatPacked'` are the plain theorems after the implication.
One auxiliary lemma is
checked synchronously through the literal layer's `addClosedProof`; there
is no elaborator `Kernel.whnf` pre-check, no elaborator type check of the
proof before the kernel's, and no `native_decide`.

## Transport and result reconstruction

Write `E := HexMatrixMathlib.matrixEquiv` (to avoid confusing the matrix
equivalence with the user's expression `e`) and
`φ := HexMvPolyMathlib.eval₂MathlibHom ι v`. The entry proofs and
`eval₂MathlibHom_apply` give `A = (E P).map φ`. Determinant correspondence
and `RingHom.map_det` then give

```text
A.det = φ (Hex.Matrix.det P) = φ d.
```

If `q` is the polynomial reified from `e`, its batch proof gives `φ q = e`.
The tactic checks equality of the canonical term lists of `d` and `q` in
the kernel, uses `beq_iff` and denotation to obtain `d = q`, and composes
these equalities. It proves agreement with the user's expression, without
printing a polynomial and asking `ring` to prove it equal. A mismatch is a
`declined` outcome displaying `φ d` and explaining that the target is not
a polynomial identity in the sealed atoms; it is not evidence that the
specialised target is false. For example, `!![x].det = 0` under `hx : x = 0`
requires substitution before this arm can close it.

The accepted goals are `A.det = e` and `e = A.det`, the latter by symmetry.
With no target expression, `det% A` returns the existing
`HexMatrixMathlib.Certified Matrix.det A`, with `value := φ d` and
`proof : A.det = value`; the value is the denoted computed polynomial in
`F`, not a polynomial object or an unproved pretty-printed expression.
These results are unconditional. Even if a pivot polynomial vanishes at
`v`, determinant transport is valid: unlike symbolic rank, this arm has no
nonvanishing condition to discharge or leave as a goal. The empty matrix
returns one.

## Carriers and composition

The integer arm uses the integer provider (`C := Int`,
`ι := Int.castRingHom F`) for any `[CommRing F]`: `RingHom.map_det` needs
no injectivity, and there is no assumption that evaluation of polynomials
at the atoms is injective. Soundness is unconditional. Completeness holds
whenever `ι` is injective on the coefficients that occur; in positive
characteristic a polynomial identity that holds only modulo `p` is not
found by the integer arm and the residue arm below is the complete one.

Rational coefficients use row scaling as `checkDetRat` does. Before ring
reification, a proved coefficient-normalisation pass over `ℚ` recognises
closed rational scalars and clears their denominators in each row. It
returns positive integer scales `sᵢ` and integer polynomial expressions
for `B`, with entry proofs `eval₂ ι v B[i, j] = sᵢ * A i j`. The pass
shares the atom environment with matrix and target reification and treats
division by symbolic terms as atoms; it does not rewrite `x / y` into
polynomial division. Current `reifyRing?` atomises division, including
`1 / 2`, so this pass is an explicit additional implementation obligation.
Until it exists, denominator-clearing requests decline with
`det: symbolic determinant declined: rational coefficient normalisation unavailable`;
ordinary polynomial identities in atomised division terms remain sound.

Certify the integer polynomial matrix `B` by the selected list or packed
checker. If `D := ∏ sᵢ` and `dB` is its certified determinant, the entry proofs and
row-scaling theorem give `D * A.det = φ dB`. This arm requires `[Field F] [CharZero F]` on
the target, unlike the integer arm: cross-multiplication needs the scales
`t * D` to be cancellable and the term form needs division, and `CharZero`
alone does not give cancellation in a commutative ring (in `ℤ × ZMod 2`
the element `2` kills `(0, 1)`). Positivity and `CharZero` then prove
`(D : F) ≠ 0`. Apply the same proved pass to
the target to obtain a positive integer `t` and integer polynomial `qZ`
with `φ qZ = t * e`. Kernel list equality checks
`t * dB = D * qZ`, again with nonzero integer scales interpreted in `ℚ`.
The term form returns `φ dB / D`. All computational checks use integer
lists; the entry/scalar normalisation proofs establish the scaling equations,
so no rational polynomial list representation is assumed. Nonzero closed
scalar denominators are proved by the normalisation pass, never left as
user side goals.

Positive characteristic uses the residue provider
(https://github.com/kim-em/hex-dev/issues/10255, merged) with the residue
list form of https://github.com/kim-em/hex-dev/issues/10257, the Mathlib
ring/domain bridge and the lawful exact quotient at `MvPoly`. For `ZMod64 p`, this includes both
`ZMod64.Bounds p` and `ZMod64.PrimeModulus p`; a composite modulus does not
satisfy the domain contract. Characteristic-aware conversion reduces
coefficients, not exponents or polynomial functions: `X³ - X` over
`ZMod 3` is not the zero polynomial. The residue term-list arm is enabled:
`Hex.PolyDet.opsMod` instantiates `checkDetPolyList`, `Residue.decode` supplies
its `denoteMod` laws, and `Residue.target` transports the checked determinant
through `HexReflectMathlib.residueHom`. Entry replay uses the shared
`HexReflect.Kernel.ringListMod`. Kernel tests cover the formal `X³ - X`,
4×4 multivariate determinants, singular witnesses, and malformed residues.
The packed residue arm remains a separate implementation obligation (#10274).

hex-bareiss-mathlib's simproc `Hex.norm_det` (renamed from `hex_norm_det`;
tactic and simproc names carry no `hex_` prefix, the namespace does the
work) tries the numeric certificate, then the unmodified Mathlib
`norm_det` fallback in the same simp set. This library provides a second
simproc, `Hex.normPolyDet`, that tries the symbolic certificate and falls
back to `norm_det`; it is opt-in and not added to the default chain until
the sweep below shows the regime in which it wins, at which point the
chain dispatches on that regime. A symbolic success rewrites to `φ d`; a
decline leaves the original expression available to Mathlib. Check budgets
before invoking the producer, and preserve the attempt's outcome/batch
within the invocation: a tactic decline must not re-enter the same symbolic
attempt through the simproc. No input `norm_det` accepts today regresses. Unsupported goals return `notApplicable`;
capability or budget declines retain
`det: symbolic determinant declined: <reason>`, including carrier or entry
coordinate where relevant, for reporting if the composed tactic fails.
A malformed or rejected producer certificate is `failure`, never a weaker
result disguised as success. The axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`, as for the numeric arm.

## Proof probes and shipping bar

Add symbolic probes under `bench/HexPolyDetMathlib/ProofProbe`, with the
executable producer measurements owned by hex-poly-det. Sweep dimensions
`2, 4, 8`, atom counts `1, 2, 4`, total entry degrees `1, 2, 4` and entry
supports `1, 4, 16`, recording the actual canonical degree and support.
Use all feasible combinations: a requested support larger than the number
of monomials of the given degree bound and arity is marked infeasible,
not silently generated with smaller support. Include dense, structured,
pivot-swap and identically singular matrices, rational coefficient variants,
and valuations at which a nonzero polynomial determinant becomes zero.

The closed-algebraic family uses `ℚ(√2)` blocks, including
`!![α, 1; 2, α]`. The shared polynomial target is `α² - 2`; both arms
must be measured on that target with `α` treated as an atom. The target
zero using `α² = 2` is a separate scope probe: independent-atom reification
cannot use that relation, in Hex as in `norm_det`. Record the decline;
do not claim an algebraic-number scope win without a separate certified
coefficient provider that can prove the relation. Strictly larger scope
must instead be demonstrated on accepted surfaces such as the shared
literal layer's `fun i j => …`/`Matrix.ofArray` forms and `det%`.

Compare against the unmodified pinned `norm_det` from
`Mathlib/Tactic/NormDet.lean` on identical targets, with the same residual
ring normalisation if the Mathlib arm needs it, in fresh modules against
matched import-only baselines. Use `scripts/bench/fresh_module_sweep.py`:
six samples, adjacent pairs, alternating `AB`/`BA`, retaining all completed
runs on the shared host. Record batch reification, producer, list conversion,
kernel check, entrywise identification and total elaboration separately,
plus proof node count, `.olean` size, realised minor support/degree and
coefficient bits. Record
one kernel-only profile per family and median ratios in this SPEC before
shipping; these are planned measurements, not inferred timing results.
Preregister per-case cleanup timeouts and proof-build ceilings in the runner
manifest; a timeout is reported as such and never removed from the ladder.
Measure the full composed invocation on declines too, including work before
fallback, so no decline can hide a regression against bare `norm_det`.

Bird's `O(n⁴)` ring-normalised certificate chain is expected to lose as
matrix dimension grows while minor support remains modest: the fraction-free
list check uses about `n³ / 3` polynomial products (or `n²` for a singular
vector), and never replays pivot search or division. With many variables,
higher degrees or dense support, expanded minors and intermediate products
can swell enough to reverse that advantage; small matrices can also be
dominated by reification and list conversion. Report those losses and
budget declines rather than extrapolating scalar operation counts to time.

The shipping rule is the opt-in exception recorded in
[matrix-tactics §The bar against Mathlib](../matrix-tactics.md#the-bar-against-mathlib):
this arm does not clear the strict bar, since its certificate fragment
is not strictly larger than `norm_det`'s and a shared family may lose. The handler and term
form ship regardless, as opt-in; the simproc enters the default chain only
for families where the fresh-module median is smaller than `norm_det`'s,
and the table records every family either way. Fallback preserves scope
but does not establish a runtime win; a win on selected rungs enables the
chain on those rungs only.

### Packed-arm comparison

The packed implementation reruns the shared families in
[the recorded report](../../reports/hex-poly-det-mathlib-performance.md),
retaining its infeasible cases, failures and declines. For every certificate
case compare forced term lists and forced packed checking on the same
witness and proposition. Fix the sparse/packed crossover table from those
measurements first, with the mode-selection table supplied by Kronecker's
product benchmark. Then run fresh comparisons of the full automatic dispatch
using the fixed tables against unmodified `norm_det`. An empty-table dispatch
run is a sparse-fallback control, not evidence about packed dispatch. Forced
packing still obeys the hard limits; an ineligible case records a decline, not a packed timing. Keep the `n ≤ 3`
controls on their existing route. Extend the certificate grid to dimensions
`4, 8, 16`, atoms `1, 2, 3, 4` and degrees `2, 4, 8, 16`, retaining the
original support ladder and recording actual per-atom degrees. Add matrices
with independent atoms to exercise early packing declines, as well as
prime-residue quotient cases and missing-payload fallback cases. Residue
comparisons include a small prime and a prime near the provider's `2^31`
upper bound, with `p` and quotient support recorded alongside packed bits.

Classify the grid by actual product/witness bounds before timing: large
three- and four-atom identities often exceed the digit envelope stated in
hex-poly-det. Keep these rows as expected declines, distinct from infeasible
support requests or timeouts. They measure the preflight and composed fallback,
not forced packed evaluation. Retain the full shared ladder and report the
accepted few-atom region explicitly; do not omit losing or declined cells.

Use the existing fresh-module runner with matched import-only baselines,
six adjacent pairs per comparison and alternating `AB`/`BA` order on one
automatically selected CPU where supported. Retain every completed run and
host context, with at most one unchanged rerun if inconclusive. Preregister
the cases, crossover keys and the existing 45-second cleanup/proof ceilings
before collecting samples. Time quotient generation, preflight and list
conversion, repeated inner/outer packing, integer multiplication, kernel
check, identification, total elaboration and composed fallback separately where applicable; record proof
nodes, `.olean` size, support, degree bounds, packed bits and route. Collect
one representative kernel profile per family, not a profile per change.

The implementation updates the report and this SPEC with per-family medians
for term lists, packed checking, automatic dispatch and Mathlib, plus
completion counts, ratios and an explicit `default-on` / `opt-in` decision.
The crossover table is fixed from the preregistered comparisons before
activation. Reconsider `Hex.normPolyDet` under
[matrix-tactics §The bar against Mathlib](../matrix-tactics.md#the-bar-against-mathlib):
only an identifiable family whose full dispatched invocation has a smaller
median than `norm_det`, including decline/fallback costs, may enter the
default chain. Every other family remains opt-in. Faster packed kernel work
alone does not satisfy this rule. The SPEC amendment enables no family by
default; the existing measurements below contain no packed-arm results and
cannot establish its wins.

## Declaration inventory

Existing declarations used by this design:

| declarations | source |
|---|---|
| `Hex.Matrix.DetWitness`, `checkDetList`, `checkDetRat`, `detWitness` | `HexBareiss/Kernel.lean` (integer witness and producer today) |
| `HexMatrixMathlib.det_eq_of_checkList`, `det_eq_of_checkRat` | `HexBareissMathlib/Kernel.lean` |
| `Hex.norm_det`, `det` and `det%` syntax | `HexBareissMathlib/Tactic.lean` |
| `HexMatrixMathlib.Certified` | `HexMatrixMathlib/Literal.lean` |
| `HexMvPolyMathlib.eval₂MathlibHom`, `eval₂MathlibHom_apply` | `HexMvPolyMathlib/Aeval.lean` |
| `HexMatrixMathlib.det_eq` | `HexDeterminantMathlib/CoreTransport.lean` |
| `RingHom.map_det` | Mathlib `LinearAlgebra/Matrix/Determinant/Basic.lean` |
| `Matrix.det_of_isLowerTriangular`, `det_of_isUpperTriangular` | Mathlib `LinearAlgebra/Matrix/Block.lean` |

The domain proof additionally uses `HexMvPolyMathlib.equiv` and
`instCommRingMvPoly` (`HexMvPolyMathlib/Equiv.lean`) and
`Matrix.exists_vecMul_eq_zero_iff` (Mathlib
`LinearAlgebra/Matrix/ToLinearEquiv.lean`). Batch quotation is in
`HexReflect/Session.lean`, sealing in `HexReflect/State.lean`, and
`convertTerms?`/`ofIntTerms` in `HexReflect/Convert.lean`.

`checkDetPolyList`, `checkDetPolyList_sound`, the polynomial generalisation
of `detWitness`, and the canonical list layer's `beq_iff`/denotation API
are implemented. `checkDetPolyPacked` / `checkDetPolyPackedMod` and their
soundness theorems are implemented, with the packed checkers owned by
hex-poly-det and the proofs here. The generic list checker stays Mathlib-free
in hex-bareiss, its `MvPoly` instantiation in hex-poly-det, and its determinant soundness
in this library.

## File organisation

```
HexPolyDetMathlib/
  Sound.lean        -- shared witness identities, list soundness, transport
  Packed.lean       -- checkDetPolyPacked_sound and residue variant
  Certificate.lean  -- compiled selection, self-check, quotation, and trace
  Scaling.lean      -- rational scaling transport
  Normalize.lean    -- proved coefficient normalization
  Frontend.lean     -- reification and certificate preparation
  Small.lean        -- closed forms
  Tactic.lean       -- the handler on hex-bareiss-mathlib's `det` syntax kind, det% for symbolic input, Hex.normPolyDet
  Tests.lean
HexPolyDetMathlib.lean
```

When the packed implementation lands, the `libraries.yml` entry becomes

```yaml
  HexPolyDetMathlib:
    deps: [HexPolyDet, HexBareissMathlib, HexReflect, HexReflectMathlib, HexMvPolyMathlib, HexMatrixMathlib, HexKroneckerMathlib]
    mathlib: true
    proof_probes: [bench/HexPolyDetMathlib/ProofProbe]
    done_through: 3
    status: active
```

## Implementation and verification

The executable instantiation is `HexPolyDet/Basic.lean`; the companion separates
`Sound.lean`, `Scaling.lean`, `Normalize.lean`, `Frontend.lean`, `Small.lean`, and
`Tactic.lean`. Integer polynomial certificates transport to any `CommRing`.
The proved denominator-normalisation frontend currently operates on `Rat`;
divisions over other carriers remain eligible atoms. `Residue.lean` instantiates `Decode` with the shared Nat residue operations
and proves determinant transport. The closed checker contains no `ZMod64`
arithmetic.

Producer-side grevlex terms are converted to canonical list order by merge sort.
Generated value expressions use balanced sums, and entry identification uses
direct list denotation, avoiding a round trip through the Hex matrix data.
The term form does not replay a reflexive comparison of its own value list.

Limits are 16 rows, 65,536 certificate terms, 100,000 intermediate terms and
source nodes, 4,096 coefficient bits, exponent 64, and 1,000,000 proof nodes.
The manifest preregisters 45-second cleanup/proof ceilings and six samples per
arm. The main 2/4/8 ladder contains 48 feasible dense combinations and 33
infeasible combinations; separate 3×3 cases measure the closed-form route.
Dense rows are scaled copies of seeded integer rows, so entries within one row
share a polynomial. This correlation is part of the measured input family.

`HexPolyDetMathlib.Tests` includes certificate-only tests beyond the small route,
nonconstant exact division, rational scaling, singularity, local let bindings,
composite-characteristic targets, and term forms. Its axiom audits include
integer, rational, singular and term-form proofs. Heavy fresh-module probes
belong to the manual sweep; merge-gating CI builds the bounded regression tests.
The symbolic simproc remains opt-in until the recorded sweep establishes a
smaller median for a size regime; no default integration is claimed here.

All Hex sweep modules emit the route taken (closed formula, polynomial
certificate, or fallback), including the reason for a budget decline. The
packed implementation extends certificate traces as specified above. The
conservative preflight bound declines some high-degree, four-variable 8×8
cases before elimination; their complete composed calls remain in the ladder.
The sweep reports faster cases separately from the opt-in release decision.
Its 70 cases include 4×4 function and array literals and a certificate whose
nonzero polynomial determinant vanishes at a stated atom valuation.

Rational addition, subtraction and row clearing use least common multiples
of their positive scales. Products and powers multiply scales as required.
Compiled comparison against the selected integer or residue list replay
checks conversion before quoting an entry proof. Composite-characteristic
requests decline the residue provider and use the universal integer certificate.
The same route preserves certificates over commutative rings lacking a domain
instance; it may decline identities that require coefficient reduction.

## Recorded measurement outcome

The handler and term form ship through the opt-in exception. The symbolic
simproc remains outside the default chain. The complete 840-sample schedule
and 14 profiles, including every failure and timeout, are retained in
[the report](../../reports/hex-poly-det-mathlib-performance.md) and its linked
raw data. N-prefixed rows below are the correlated row-scaled family
(except N2K4D1S1); these ratios do not describe independent dense entries.
Times are fresh-module, baseline-subtracted medians in milliseconds. All six
samples are required; ratios use positive medians only.

| Case | Mathlib ms | Hex ms | M/H | Completed M/H | Hex route |
|---|---:|---:|---:|---:|---|
| N2K1D1S1 | 41.33 | 89.80 | 0.460 | 6/6 | closed-form |
| N2K1D2S1 | 3.04 | 110.29 | 0.028 | 6/6 | closed-form |
| N2K1D4S1 | 74.68 | 102.87 | 0.726 | 6/6 | closed-form |
| N2K1D4S4 | 187.01 | 256.81 | 0.728 | 6/6 | closed-form |
| N2K2D1S1 | 90.42 | 103.44 | 0.874 | 6/6 | closed-form |
| N2K2D2S1 | 92.18 | 106.16 | 0.868 | 6/6 | closed-form |
| N2K2D2S4 | 112.02 | 188.86 | 0.593 | 6/6 | closed-form |
| N2K2D4S1 | 89.59 | 100.17 | 0.894 | 6/6 | closed-form |
| N2K2D4S4 | 198.88 | 286.75 | 0.694 | 6/6 | closed-form |
| N2K4D1S1 | 44.69 | 65.44 | 0.683 | 6/6 | unobserved |
| N2K4D1S4 | 101.81 | 157.70 | 0.646 | 6/6 | closed-form |
| N2K4D2S1 | 74.55 | 98.74 | 0.755 | 6/6 | closed-form |
| N2K4D2S4 | 190.64 | 197.10 | 0.967 | 6/6 | closed-form |
| N2K4D4S1 | 92.16 | 104.74 | 0.880 | 6/6 | closed-form |
| N2K4D4S4 | 188.84 | 197.71 | 0.955 | 6/6 | closed-form |
| N2K4D4S16 | 2788.30 | 1895.34 | 1.471 | 6/6 | closed-form |
| N4K1D1S1 | 101.54 | 297.30 | 0.342 | 6/6 | certificate |
| N4K1D2S1 | 279.68 | 412.29 | 0.678 | 6/6 | certificate |
| N4K1D4S1 | 240.79 | 406.35 | 0.593 | 6/6 | certificate |
| N4K1D4S4 | 1191.72 | 2005.28 | 0.594 | 6/6 | certificate |
| N4K2D1S1 | 103.55 | 293.17 | 0.353 | 6/6 | certificate |
| N4K2D2S1 | 291.93 | 481.72 | 0.606 | 6/6 | certificate |
| N4K2D2S4 | 1121.42 | 2293.34 | 0.489 | 6/6 | certificate |
| N4K2D4S1 | 293.59 | 426.24 | 0.689 | 6/6 | certificate |
| N4K2D4S4 | 2100.48 | 4077.43 | 0.515 | 6/6 | certificate |
| N4K4D1S1 | 150.07 | 288.65 | 0.520 | 6/6 | certificate |
| N4K4D1S4 | 692.92 | 1800.87 | 0.385 | 6/6 | certificate |
| N4K4D2S1 | 288.94 | 486.34 | 0.594 | 6/6 | certificate |
| N4K4D2S4 | 2098.92 | 4668.53 | 0.450 | 6/6 | certificate |
| N4K4D4S1 | 287.76 | 495.23 | 0.581 | 6/6 | certificate |
| N4K4D4S4 | 2256.02 | 4804.17 | 0.470 | 6/6 | certificate |
| N4K4D4S16 | — | — | — | 0/0 | unobserved |
| N8K1D1S1 | 690.61 | 999.66 | 0.691 | 6/6 | certificate |
| N8K1D2S1 | 2693.22 | 3196.05 | 0.843 | 6/6 | certificate |
| N8K1D4S1 | 2699.85 | 3146.19 | 0.858 | 6/6 | certificate |
| N8K1D4S4 | 36220.70 | — | — | 6/4 | fallback |
| N8K2D1S1 | 1074.74 | 1007.27 | 1.067 | 6/6 | certificate |
| N8K2D2S1 | 3049.37 | 3190.55 | 0.956 | 6/6 | certificate |
| N8K2D2S4 | — | — | — | 0/0 | unobserved |
| N8K2D4S1 | 2993.95 | 3207.48 | 0.933 | 6/6 | certificate |
| N8K2D4S4 | — | — | — | 0/0 | unobserved |
| N8K4D1S1 | 2066.74 | 1097.77 | 1.883 | 6/6 | certificate |
| N8K4D1S4 | — | — | — | 0/0 | unobserved |
| N8K4D2S1 | 4090.38 | 4253.46 | 0.962 | 6/6 | fallback |
| N8K4D2S4 | — | — | — | 0/0 | unobserved |
| N8K4D4S1 | 4010.25 | 4254.07 | 0.943 | 6/6 | fallback |
| N8K4D4S4 | — | — | — | 0/0 | unobserved |
| N8K4D4S16 | — | — | — | 0/0 | unobserved |
| N3K1D1S1 | 86.70 | 194.35 | 0.446 | 6/6 | closed-form |
| N3K2D2S4 | 392.63 | 595.00 | 0.660 | 6/6 | closed-form |
| N3K4D4S16 | — | — | — | 0/0 | unobserved |
| Rational2 | 175.98 | 207.96 | 0.846 | 6/6 | closed-form |
| Singular2 | 65.41 | 84.25 | 0.776 | 6/6 | closed-form |
| Algebraic2 | 2.02 | 83.58 | 0.024 | 6/6 | closed-form |
| Rational3 | 400.42 | 504.31 | 0.794 | 6/6 | closed-form |
| Singular3 | -0.62 | 191.08 | — | 6/6 | closed-form |
| Algebraic3 | 1.46 | 106.08 | 0.014 | 6/6 | closed-form |
| Rational4 | 2191.95 | 2395.61 | 0.915 | 6/6 | certificate |
| Singular4 | 103.02 | 259.09 | 0.398 | 6/6 | certificate |
| Algebraic4 | 104.85 | 293.94 | 0.357 | 6/6 | certificate |
| Rational8 | — | — | — | 0/0 | unobserved |
| Singular8 | 985.34 | 909.28 | 1.084 | 6/6 | certificate |
| Algebraic8 | 214.23 | 651.98 | 0.329 | 6/6 | certificate |
| Swaps | 90.46 | 195.88 | 0.462 | 6/6 | certificate |
| Tridiagonal | 91.97 | 197.33 | 0.466 | 6/6 | certificate |
| Function4 | — | 199.96 | — | 0/6 | certificate |
| Array4 | — | 190.34 | — | 0/6 | certificate |
| AlgebraicScope | 97.61 | 105.21 | 0.928 | 6/6 | unobserved |
| Valuation | 38.42 | 86.67 | 0.443 | 6/6 | closed-form |
| Valuation4 | 47.03 | 197.61 | 0.238 | 6/6 | certificate |
