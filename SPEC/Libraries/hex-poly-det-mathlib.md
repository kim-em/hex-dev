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
probes.

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
claims that the proposed declarations already exist.

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

The kernel checks `checkDetPolyList` on the row lists of canonical polynomial
term lists and the witness in the same representation. Coefficients are
encoded by `Int` for the integer arm and canonical `Nat` residues for the
residue arm; exponent vectors are lists of `Nat`. Shape, canonicality,
nonzero diagonals, vanishing products and the determinant value identity
are checked as specified on the executable side. In particular the final
value check uses `l₀ = 1`, `lᵢ₊₁ = uᵢ` and `d = sign σ * uₙ₋₁`
(`d = 1` when `n = 0`), without expanding the product of pivot polynomials.
Polynomial equality uses the list layer's `beq_iff` contract, not evaluation at sample points.

The proposed `checkDetPolyList_sound` in this library identifies a passing
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

Certify the integer polynomial matrix `B` by `checkDetPolyList`. If
`D := ∏ sᵢ` and `dB` is its certified determinant, the entry proofs and
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
`ZMod 3` is not the zero polynomial. Until the residue list form exists this arm's kernel tests are documented
non-tests and the integer arm handles such carriers soundly but
incompletely, as described above.

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
are implemented. The checker stays Mathlib-free in hex-bareiss,
its `MvPoly` instantiation in hex-poly-det, and its determinant soundness
in this library.

## File organisation

```
HexPolyDetMathlib/
  Sound.lean        -- checkDetPolyList_sound at MvPoly, transport, rational scaling
  Tactic.lean       -- the handler on hex-bareiss-mathlib's `det` syntax kind, det% for symbolic input, Hex.normPolyDet
  Tests.lean
HexPolyDetMathlib.lean
```

`libraries.yml` gains

```yaml
  HexPolyDetMathlib:
    deps: [HexPolyDet, HexBareissMathlib, HexReflect, HexReflectMathlib, HexMvPolyMathlib, HexMatrixMathlib]
    mathlib: true
    proof_probes: [bench/HexPolyDetMathlib/ProofProbe]
    done_through: 0
    status: planned
```

## Implementation and verification

The executable instantiation is `HexPolyDet/Basic.lean`; the companion separates
`Sound.lean`, `Scaling.lean`, `Normalize.lean`, `Frontend.lean`, `Small.lean`, and
`Tactic.lean`. Integer polynomial certificates transport to any `CommRing`.
The proved denominator-normalisation frontend currently operates on `Rat`;
divisions over other carriers remain eligible atoms. The reduced-Nat residue
adapter remains a documented non-test pending #10257; `Decode` supplies its
validity, arithmetic, equality and domain-transport contract.

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
