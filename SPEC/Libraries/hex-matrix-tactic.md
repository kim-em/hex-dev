# hex-matrix-tactic

Proof-producing `det`, `rank`, and `char_poly` frontends for executable Hex
matrices. The [Mathlib companion](hex-matrix-tactic-mathlib.md) accepts
Mathlib matrices and integrates with `norm_det` and `norm_rank`. These are
independent tactics with plain names; duplicating a Mathlib tactic is allowed.
The performance objective is a measured, reproducible speedup on named
families, with slower cases driving optimisation. Benchmarking determines
strategy and documents coverage; it does not decide whether a tactic may ship.

This SPEC specifies future implementation, not an implemented API. It follows
[the matrix design in PR #9437](https://github.com/kim-em/hex-dev/pull/9437),
with numeric support independent of the separately specified
[hex-reflect](hex-reflect.md).

## Boundary and dependencies

`HexMatrixTactic` owns Hex literal recognition, entry-model selection, matrix
batch conversion, algorithm selection, result reconstruction, and syntax.
It accepts `Hex.Matrix R n m`, with concrete natural dimensions, through the
public `ofFn`, `ofRows`, row and entry APIs and the library's notation. It
must not access the private backing buffer or recognize Mathlib syntax.

Its direct dependencies are `HexMatrix`, `HexBareiss`, `HexRowReduce`,
`HexCharPoly`, and the planned `HexRank`. `HexDeterminant`, `HexPoly`,
`HexArith`, and `HexBasic` are available transitively. It imports Lean's
elaborator API, but no Mathlib. The companion sits above this library and the
corresponding Mathlib bridges. Neither numeric library imports `HexReflect`
or `HexReflectMathlib`.

The `libraries.yml` entries are `status: planned`, `done_through: 0`, with no
Lake targets or umbrella files until activation. These edges follow
`scripts/check_dag.py` and its `libgraph.may_import` dependency closure.
The existing lower libraries must never import either frontend. Symbolic
integration will live in the future `HexMatrixReflect` library, depending on
this frontend and reflection, with `HexMatrixReflectMathlib` above their
companions. These extension libraries are outside the numeric activation.
It cannot be an optional file in the numeric library whose import would
silently expand that library's dependency closure.

Activation must first make `HexRank` active, then activate `HexMatrixTactic`;
the Mathlib path likewise requires active `HexRankMathlib` before
`HexMatrixTacticMathlib`. Here active means the dependency's scaffolding and
Lake registration exist, not that all its implementation phases are complete.
Determinant and characteristic-polynomial work can then proceed while rank's
certificate implementation is developed. No migration imports a planned
library before this activation order is satisfied.

## Entry models and conversion

A computation model mirrors `Mathlib.Tactic.Echelon.BareissExt`: a Meta-level
lookup on the carrier returns a producer or declines. The executable value
type, arithmetic, preparation/restoration and quotation are separate pieces.
A model records zero, one, multiplication, subtraction, a zero test and,
when available, an exact quotient. It also supplies the addition and
interpretation laws needed by Hex algorithms. Preparation converts a whole
matrix, retaining dimensions, row-major order, original entry expressions,
and one proof of each entry's interpretation. Restoration accounts for every
row scale or coefficient conversion, not just the returned scalar.

Lookup and caches include the exact carrier, algebraic instances,
interpretation map, configuration and, for symbolic input, sealed variable
environment. Matching only a type name is insufficient. Discovery and
quotation are untrusted; an executable zero test is not a proof of its answer.

| Entry model | Accepted fragment and proof obligation |
|---|---|
| Closed `Int`, `Rat` | Kernel-transparent arithmetic and equality; rational denominators are nonzero and any denominator clearing has a proved restoration. |
| Closed `ZMod n`, `Fin n` | Literal modulus, kernel-decidable equality and lawful ring operations. `ZMod` recognition belongs in the companion; `Fin n` requires positive `n` for its modular ring. Determinant and characteristic polynomial allow composite moduli; rank requires a domain/field model, normally prime modulus, and cannot assume primality. `ZMod 0` follows its integer model. |
| Literals in `ℝ`, `ℂ` | The companion proves entries equal to images of computable values using `norm_num` and registered interpretation lemmas. Rational-valued literals use `Rat`; complex literals involving `I` need an explicit computable extension. Never run kernel equality on classical real or complex instances. |
| Closed algebraic entries | A registered computable number-field or real-algebraic carrier and certified embedding, with nonzero preservation for rank. This is a numeric provider extension, independent of symbolic reflection. |
| Symbolic entries (future `HexMatrixReflect` extension) | A later `hex-reflect` provider converts the entire matrix in one batch, seals variables once and supplies interpretation equalities. Intermediate polynomial matrices are not printed and reparsed. |

Determinant and characteristic polynomial commute with a ring homomorphism;
rank additionally needs injectivity or explicit proofs that the chosen minor
remains nonzero under interpretation. A symbolic polynomial nonzero before
specialization may become zero afterwards. Generic rank must name the
polynomial domain or its fraction field; conditional specialized rank retains
all nonvanishing conditions. Unconditional rank of arbitrary specializations
is not promised. Piecewise rank and case splitting are later work. The
symbolic rank arm is specified in [§Symbolic rank](#symbolic-rank).

## Frontends and results

The term forms `det% A`, `rank% A`, and `char_poly A` return dependent records
with fields `value` and `proof`, the latter asserting that the requested
operation on the original matrix equals `value`. Determinant values are in
the source carrier, rank values in `Nat`, and characteristic-polynomial
values in `Hex.DensePoly R` or the companion's `Polynomial R`.

The `%` distinguishes result-producing term syntax from ordinary `det A` and
`rank A` function applications. The tactics remain plain `det`, `rank` and
`char_poly`. Importing a frontend must not reserve bare `det` or `rank` as a
term keyword or change existing name resolution; opening both matrix
namespaces can already require qualifying their identically named functions.

The goal forms close determinant equality, rank equality or either inequality,
and characteristic-polynomial equality. On Hex inputs determinant goals name
`Hex.Matrix.det`, `bareiss`, or
`bareissWith` with its quotient law, and characteristic-polynomial goals name
`Hex.Matrix.charPoly`. Field-rank goals name `Hex.Matrix.rowReduce_rank`
(`[Lean.Grind.Field R] [DecidableEq R]`, `HexRowReduce/Api.lean`);
domain-rank goals name the planned `Hex.Matrix.rankWith quot` with its exact
quotient law, or its integer specialization `Hex.Matrix.rank`, from
`hex-rank`. The integer result agrees with rank after casting to `Rat` via
the companion's scalar-extension theorem. Each rank operation admits equality
and the two inequality forms. The companion gives the Mathlib statements.
Square shape is required for determinant and characteristic
polynomial; rank supports rectangular and empty matrices. Empty square
matrices have determinant `1`, rank `0`, and characteristic polynomial `1`.

An equality tactic checks the requested right-hand side against the certified
result, including coefficientwise polynomial equality. Rank inequalities use
the certified equality followed by a checked natural-number comparison; a
one-sided minor or spanning certificate may avoid computing the opposite bound
when its soundness theorem suffices. A false target remains unproved.

The common internal protocol distinguishes `notApplicable` (wrong fragment),
`declined` (unsupported capability or exhausted budget), `success` (value and
proof, or explicitly conditional result), and `failure` (malformed output or
failed certificate). A tactic closes a goal only after every condition is
proved. Programmatic conditional results expose an ordered condition list and
a proof depending on it; unconditional term forms decline unresolved
conditions. Diagnostics identify the operation, carrier, entry coordinate,
missing capability or exceeded budget. No failure substitutes a weaker goal.

## Algorithms and proof strategy

Initial determinant selection is:

| Input and laws | Producer |
|---|---|
| Closed `Int` | Row-pivoted fraction-free Bareiss |
| Closed field with certified exact quotient | Bareiss, with denominator restoration when working integrally |
| Commutative ring without exact quotient | Samuelson–Berkowitz, returning `(-1)^n` times the constant coefficient of `det(X I - A)` |
| Symbolic polynomial entries with certified exact quotient (future extension) | Polynomial Bareiss |
| Symbolic polynomial entries without exact quotient (future extension) | Samuelson–Berkowitz with the same sign correction |

Characteristic polynomial uses Samuelson–Berkowitz. The characteristic
variable stays separate from reflected entry variables, for example in
`DensePoly (MvPoly k C cmp)`. Rank uses verified field row reduction or the
two-sided domain certificate and fraction-free producer specified by
[hex-rank](hex-rank.md). That certificate and its companion's soundness are
planned dependencies, not existing declarations.

There are two proof strategies:

- **Transport and kernel evaluation.** Materialize a Hex input, transport by
  correspondence, then prove a closed executable equality by kernel `decide`
  (`Lean.Meta.mkDecideProof`, or `decide +kernel` in source examples).
  For Bareiss the equality must mention `bareiss`/`bareissWith`; reducing
  `Hex.Matrix.det` instead evaluates its Leibniz definition. Either way,
  evaluating a producer equality in the kernel replays that producer.
- **Certificates.** Compiled code proposes intermediate values; kernel checks
  local equations or a smaller result certificate, and a soundness theorem
  yields the result. Keep the existing Berkowitz certificate path. Rank's
  nonzero minor and column-expression certificate can check in `O(n m r)`
  arithmetic operations at fixed rank, avoiding full elimination. Determinant
  step certificates still verify elimination arithmetic: no generally cheaper
  determinant certificate is assumed.

Selection is provisional until Phase 4 measures it. Record dimensions and
rank, maximum coefficient numerator/denominator bit lengths, estimated minor
bit growth, and predicted certificate size. For symbolic matrices also record
variable count, degree, support and intermediate support growth. Small
matrices with bounded coefficients initially use direct replay; larger
coefficients, costly kernel division or repeated polynomial expansion favour
local checks; low-rank inputs favour the two-sided certificate. Dimension
alone is never a cutoff. Model-specific thresholds, proof-size and search
budgets are fixed from the benchmark tables before claiming Phase 4 and
reported with the chosen strategy. Provide a diagnostic strategy override for
matched measurements and reproducibility.

## Symbolic rank

This section is the rank arm of the future `HexMatrixReflect` extension and
its companion `HexMatrixReflectMathlib`: what `rank` returns when entries are
ring expressions rather than literals, and how each output is certified. It
is not a numeric-activation obligation. The outputs are the three fixed by
[hex-rank §Generic rank is not a specialised rank](hex-rank.md#generic-rank-is-not-a-specialised-rank):
generic rank, conditional rank and rank locus. The arm never presents a
generic rank as the rank of a specialised matrix, and no path below closes an
equality or lower-bound goal about the user's matrix without the certificate's
condition being either proved or left as a visible goal.

### Input classification

The numeric arm runs first. When its literal recogniser answers
`notApplicable` for some entry and the extension is imported, the whole
matrix is reified as one [hex-reflect](hex-reflect.md#batch-reification-and-sealing)
batch: every entry is canonicalised and reified with `reifyRing?` (top-level
variables enabled), the environment is sealed at `k` atoms, and each entry is
converted to `Hex.MvPoly k C cmp` with `Expr.toPolyC` when `Sym.Arith`
supplies the characteristic and `Expr.toPoly` otherwise. `C` is the
coefficient provider's carrier and `cmp` is fixed by the extension. The batch
yields the *polynomial matrix* `P : Hex.Matrix (MvPoly k C cmp) n m`, the
atom valuation `v : Fin k → F` (the sealed atom array, `F` the carrier of the
user's matrix `A`), the coefficient interpretation `ι : C → F`, and one
interpretation proof per entry, `eval₂ ι v P[i, j] = A i j`, from the
hex-reflect soundness theorem. Building `P` reads no hypotheses; hypotheses
enter only when a condition is discharged.

Routing is by the converted polynomials, not by syntax:

- A matrix in which some entry converts to a non-constant polynomial is
  handled here. One such entry is enough.
- A matrix in which every entry converts to a constant polynomial is a
  numeric matrix over `C` that the numeric arm did not recognise (a closed
  expression such as `(2 : ℝ) + 3`, or an atom that cancelled). It is handled
  here without a special case: `k` may be positive, the certificate's
  `denom` is a constant, and the single condition is a closed proposition
  discharged at step 2 of the order below.
- A subexpression outside the fixed ring language (`x / y`, `Real.exp t`, a
  symbolic power, an opaque constant) becomes one atom, and an atom is an
  independent indeterminate for the rest of the arm. Reification never
  implies that an atom is nonzero (hex-reflect §Shared results and
  conditions), and the arm never assumes an atom is zero either: with
  `hx : x = 0` in context the polynomial matrix still contains the
  indeterminate for `x`, and the user substitutes first. Unknown
  nonzeroness of an atom is therefore not a decline reason and is never
  asked about. The generic rank of `[x / y]` is `1` exactly as for `[x]`,
  its condition reads `x / y ≠ 0`, and whether that is discharged depends
  only on the local context. The condition returned below is the only
  nonvanishing fact any output depends on, so this is the whole treatment
  of atoms of unknown nonzeroness.

The batch debits the hex-reflect budget (source nodes, atoms, reflected
nodes, exponent, terms, coefficient bits, proof nodes) and two dimensions
the extension adds: matrix size, and `caseSplits`, reserved for
[piecewise rank](#piecewise-rank-later-extension) and fixed at `0` until that
extension exists. Exhaustion is a `declined` outcome naming the dimension.

### The certificate at `MvPoly`

The producer is hex-rank's `rankCertWith Hex.exactDiv` at
`R = MvPoly k C cmp`, with the exact quotient `Hex.MvPoly.instDiv` and its
law `Hex.MvPoly.instExactDivLaws` from `HexMvGcd/Divide.lean`
(`[LawfulGcdOps C]`, supplied for `Int`, `Rat` and `ZMod64 p`), and the
checker is hex-rank's `checkRank P c`. `DomainLaws (MvPoly k C cmp)` is
`DomainLaws.of_exactDivLaws` with `LawfulGcdOps.one_ne_zero`. This is the
one-line instantiation that
[hex-rank §Placement](hex-rank.md#placement) assigns to this consumer, so
`HexMatrixReflect` depends on `HexMvGcd` as well as on `HexMatrixTactic`,
`HexReflect` and `HexRank`; nothing carrier-specific is added to `HexRank`.

The certificate `c : RankCert (MvPoly k C cmp) n m` is closed data:
`c.rank = r`, `c.denom` a nonzero polynomial `d` (an `r × r` minor of `P`),
`c.adj` a polynomial matrix. `checkRank P c = true` is a closed Boolean over
polynomial arithmetic, proved by kernel `decide` per the certificate strategy
of [§Algorithms and proof strategy](#algorithms-and-proof-strategy); its
cost is the checker's `n · r · m` polynomial products at the certificate's
realised support, and it is the only place where polynomial arithmetic is
replayed. The producer's pivot search and exact divisions are never replayed.
Kernel `decide` is applied to `P`, `c` and `checkRank P c` only, never to a
statement containing the atoms
([hex-reflect §Soundness theorem](hex-reflect.md#soundness-theorem)). All
three outputs are read off the same `c`; in particular `d` *is* the
condition of output 2.

### Output 1: generic rank

The generic rank is a statement about `P`, or about its Mathlib image

```lean
S := (e P).map HexMvPolyMathlib.equiv : Matrix (Fin n) (Fin m) (MvPolynomial (Fin k) C)
```

(`e` is `HexMatrixMathlib.matrixEquiv`), never about `A`.

**Mathlib-free.** With `checkRank P c = true`, hex-rank's
`RankCert.det_ne_zero` and `RankCert.det_succ_eq_zero` at `P` say that `r`
is the largest size of a nonzero minor of `P`; that is the Mathlib-free
content of "generic rank". The Mathlib-free goal form is the domain-rank
form of [§Frontends and results](#frontends-and-results) at the `MvPoly`
carrier, `Hex.Matrix.rankWith Hex.exactDiv P = r` (and either inequality)
for a closed literal `P`, proved by kernel replay of the producer, since
producer correctness (`rankWith P = c.rank`) is a companion theorem. Replay
evaluates multivariate exact division in the kernel and is for small
inputs; the certificate route is the one the companion uses.

**Companion.** `HexMatrixReflectMathlib` proves `S.rank = r` from
hex-rank-mathlib's `checkRank_sound_map` at
`φ := HexMvPolyMathlib.equiv.toRingHom`, injective as a ring equivalence,
using the Mathlib instance `HexMvPolyMathlib.instCommRingMvPoly` on the
source and `MvPolynomial`'s domain instance on the target (`C` a domain
with `DecidableEq`). For any `[IsFractionRing (MvPolynomial (Fin k) C) K]`,
`rank_map_eq` gives `(S.map (algebraMap _ K)).rank = r`;
`FractionRing (MvPolynomial (Fin k) C)` is the field `Frac(C)(x_1, …, x_k)`
of [hex-rank §MvPoly](hex-rank.md#mvpoly).

The companion closes a goal `M.rank = r` (or either inequality) with the
generic rank only when the goal's matrix is the symbolic matrix itself:
the carrier of `M` is `MvPolynomial σ C` for a domain `C`, every atom of the
batch is `MvPolynomial.X i` for a literal `i : σ`, the atoms are pairwise
distinct, and the coefficient interpretation `ι` is injective (it is for
`Int` into a characteristic-zero domain and for the residue carrier into a
characteristic-`p` domain, the registered cases). Then the interpretation
map is `MvPolynomial.map ι` composed with `MvPolynomial.rename` along the
atom-to-index map, injective by `MvPolynomial.map_injective` and
`MvPolynomial.rename_injective`, and `checkRank_sound_map` at that map
closes the goal. A goal over `MvPolynomial σ C` whose atoms include anything
else (`MvPolynomial.C a` for a local `a`, a `rename`, an opaque term) is a
specialised matrix like any other and goes to output 2: two distinct atoms
may be equal in the carrier, and the interpretation need not be injective.
The fraction-field form
`(M.map (algebraMap (MvPolynomial σ C) K)).rank = r` is accepted under the
same atom condition through `rank_map_eq`.

The term form is `generic_rank% A` (proposed). It returns `value := r`, the
sealed atom array, the quoted `P`, the checked `c`, and in the companion the
proofs `S.rank = value` and `A = S.map (MvPolynomial.eval₂Hom ι v)`, the
latter assembled from the batch interpretation proofs through
`HexMvPolyMathlib.eval₂MathlibHom_apply`. Its `proof` field is about `S`,
and its type says so; `rank% A` never returns a generic rank.

### Output 2: conditional rank

For `A : Matrix (Fin n) (Fin m) F` over a domain `F`, write
`ψ := MvPolynomial.eval₂Hom ι v : MvPolynomial (Fin k) C →+* F` and
`φ := HexMvPolyMathlib.eval₂MathlibHom ι v = ψ.comp equiv.toRingHom`, so
that the batch gives `A = (e P).map φ = S.map ψ`. The certificate specialised
at `v` has one condition,

```text
Condition.proposition := φ c.denom ≠ 0
```

displayed as the interpreted polynomial in the source atoms (`x ^ 2 - 1 ≠ 0`
below), with provenance `provider` the extension's rank provider, `source`
the matrix expression, `operation` `"rank"`, and `reason` naming the
certificate denominator as a nonzero `r × r` minor of the polynomial matrix.
There is exactly one condition per invocation, so deduplication and ordering
are trivial. The theorem is

```lean
theorem checkRank_sound_at [CommRing R] [CommRing S] [IsDomain S] [DecidableEq R]
    (φ : R →+* S) (h : Hex.Matrix.checkRank A c = true) (hd : φ c.denom ≠ 0) :
    ((e A).map φ).rank = c.rank
```

proposed in `HexMatrixReflectMathlib`. Its proof is that of
`checkRank_sound_map`, whose injectivity hypothesis is used only to obtain
`φ c.denom ≠ 0`; hex-rank-mathlib may adopt it as the general form, with
`checkRank_sound_map` as the corollary, and until then the extension
companion proves it from hex-rank-mathlib's transport lemmas. It is the
statement "rank exactly `r` wherever `denom` does not vanish" of
hex-rank §Generic rank is not a specialised rank.

The condition is sufficient, not necessary. `V(I_r(P)) ⊆ V(d)` and the
inclusion is strict in general: `!![x, y]` has generic rank `1` with pivot
minor `x`, so the condition is `x ≠ 0`, while the rank is `1` wherever
`(x, y) ≠ (0, 0)`. The arm does not search for a minor whose nonvanishing
is easier to discharge; that search, and the exact set, belong to output 3
and to the later extension. Consequently the arm can fail to close a true
goal (`!![x, y].rank = 1` from `hy : y ≠ 0`), and the diagnostic then names
the condition, the generic rank and `rank_locus`.

The upper bound needs no condition. Over a field `F`,
hex-determinantal-ideal-mathlib's `rank_map_le_rank_fractionRing` at `ψ`
(applied to `e.symm S`) and `rank_map_eq_rank_fractionRing` give
`A.rank ≤ S.rank = r`. That theorem is stated over a field; over a domain
that is not a field the upper bound passes through `rank_map_eq` at the
domain's fraction field first, which is also how integer rank is defined in
[§Frontends and results](#frontends-and-results). `checkRank_sound_at`
needs only a domain.

Tactic-mode goal forms, with `r` the generic rank and `r'` the user's
number:

| Goal | Condition | Behaviour of `rank` |
|---|---|---|
| `A.rank = r'`, `r' = r` | `φ d ≠ 0` | closes; an undischarged condition becomes the first remaining goal |
| `r' ≤ A.rank`, `r' ≤ r` | `φ d ≠ 0` | as above, weakened from `r ≤ A.rank` |
| `A.rank ≤ r'`, `r' ≥ r` | none | closes unconditionally |
| `A.rank = r'`, `r' ≠ r` | | fails: the arm proves nothing about it, and the diagnostic reports `r` |
| `r' ≤ A.rank`, `r' > r` | | fails, and the diagnostic states that `A.rank ≤ r` is provable |
| `A.rank ≤ r'`, `r' < r` | | fails; the target may be true (`[x]` at `x = 0`) |

A failing row is a decline, not a `failure`: no weaker statement is
substituted, and `A.rank = 0` for `[x]` under `hx : x = 0` is reached by
substituting `hx` and using the numeric arm, not by this arm. The term form
`rank% A` has no `r'`: it returns `value := r` with proof `A.rank = r` when
the condition is discharged at steps 1 and 2 below, and otherwise declines
with the condition displayed. The programmatic interface returns a
`ConditionalResult` whose `conditions` array holds the one condition and
whose `proof` depends on it; it never creates goals.

Conditions are processed in the hex-reflect order and nowhere else:

1. definitional equality and matching local hypotheses (a hypothesis whose
   type is definitionally the displayed proposition);
2. explicitly configured cheap normalisers; the Mathlib-free extension's
   default list is empty, the companion's default list contains only
   `norm_num` on closed propositions, so a constant denominator is
   discharged and everything else is opt-in configuration;
3. facts known to the current Grind goal, when a Grind adapter runs the
   arm; not applicable to the standalone tactic;
4. a side goal, in tactic mode only: the main goal is closed with a proof
   depending on the side goal, which is left first among the remaining
   goals with the displayed proposition as its type;
5. otherwise decline without changing the goal. The decline diagnostic
   shows the condition, the generic rank, and the interpreted `P`.

The arm does not test whether a condition is refutable; a false side goal
is the user's signal, as in the finite-field example below. What the arm
must never do is close `A.rank = r` or `r ≤ A.rank` with only
`checkRank_sound_map` at an injective map that does not exist: `ψ` is not
injective, and `S.rank = r` is never rewritten into a statement about `A`.

### Output 3: rank locus

The exact set of points where the rank drops below `r` is the zero set of
the determinantal ideal `I_r(P)`, and the tactic that produces it is
`rank_locus` (later SPEC; see
[hex-determinantal-ideal §Consumers](hex-determinantal-ideal.md#consumers)).
The `rank` tactic never states a locus. The handoff is programmatic:
`rank_locus` invoked without an explicit `r` calls the extension's
generic-rank provider, receives the `ProviderOutcome` carrying `P`, `c` and
the sealed environment, takes `r := c.rank`, and runs `detIdealGens r P` on
that same `P`, so its generators are over the same atoms as the `rank`
diagnostics. The default `r` is therefore the generic rank, and the default
locus is "rank drops below the generic rank", `InLocus c.rank P p` in
hex-determinantal-ideal's terms. Choosing `r` is the whole of this arm's
part; the locus goal forms, `mem_zeroLocus_iff_rank_lt`, and the display of
generators belong to `rank_locus`.

### Piecewise rank (later extension)

Piecewise rank splits on the vanishing of `d`: rank `r` where `d ≠ 0`, and
on `V(d)` a recursive certificate over the quotient by the vanishing
condition or over the remaining minors, producing a finite case list whose
conditions partition the parameter space. It is a later extension, not
promised here, and it is where a search among minors for a dischargeable
condition would also live. Its hook is the `caseSplits` budget dimension
above: the first implementation fixes the limit at `0` and returns
`declined` naming that dimension whenever a split would be needed, so the
later extension raises a limit rather than adding a protocol. Its syntax is
fixed by its own SPEC.

### Three examples

**`[x]`**, `x : F` a field element. `k = 1`, `P = [X_0]`, `r = 1`,
`d = X_0`.

1. Generic: `S = !![X 0]` over `MvPolynomial (Fin 1) ℤ` has rank `1`;
   `generic_rank% !![x]` returns `1` with that proof.
2. Conditional: `!![x].rank = 1` closes with side goal `x ≠ 0`, or
   outright from `hx : x ≠ 0`; `!![x].rank ≤ 1` closes with no condition;
   `!![x].rank = 0` is not this arm's.
3. Locus: `rank_locus !![x]` takes `r = 1` and `I_1 = (X_0)`; the rank drops
   below `1` exactly where `x = 0`.

**`!![x, 1; 1, x]`**, generic rank `2` with a rank-`1` specialisation.
`P = !![X_0, 1; 1, X_0]`; the producer pivots on `X_0`, eliminates to
`(0, X_0² − 1)`, and the certificate has `r = 2` and `d = X_0² − 1` up to
the sign of the second pass.

1. Generic: `S.rank = 2` over `MvPolynomial (Fin 1) ℤ`, and
   `(S.map (algebraMap _ K)).rank = 2` over its fraction field.
2. Conditional: `!![x, 1; 1, x].rank = 2` closes with side goal
   `x ^ 2 - 1 ≠ 0`, which is false at `x = 1`, where the matrix is
   `!![1, 1; 1, 1]` of rank `1`; `!![x, 1; 1, x].rank ≤ 2` closes
   unconditionally.
3. Locus: `I_2 = (X_0² − 1)`, so the rank drops below `2` exactly at
   `x = ±1`; `I_1 = (X_0, 1) = (1)`, so it never drops below `1`.

**`[x ^ q − x]`** over `𝔽_q`, the finite-field example of hex-rank; take
`x : ZMod 3` and the entry `x ^ 3 - x`. Characteristic-aware conversion
(`toPolyC 3`) reduces coefficients, not exponents, so `P = [X_0³ − X_0]`,
`r = 1`, `d = X_0³ − X_0`.

1. Generic: `S = !![X 0 ^ 3 - X 0]` over `MvPolynomial (Fin 1) (ZMod 3)`
   has rank `1`. This is true and unconditional.
2. Conditional: `!![x ^ 3 - x].rank = 1` closes only with the side goal
   `x ^ 3 - x ≠ 0`, which is false for every `x : ZMod 3`; the true
   statement `!![x ^ 3 - x].rank = 0` needs the Frobenius identity, which
   is not in the ring language, and is not produced here.
   `!![x ^ 3 - x].rank ≤ 1` closes unconditionally.
3. Locus: `I_1 = (X_0³ − X_0)`, and `rank_locus` states that the rank drops
   below `1` exactly where `x ^ 3 - x = 0`, which is everywhere; the
   equivalence is correct at each point and asserts nothing about the
   complement.

### Symbolic benchmark

The `symbolic` fixture family of [§Phase-4 evidence](#phase-4-evidence),
in `conformance-fixtures/HexMatrixReflect/matrices.jsonl`, is the rank
arm's family: dimensions `2, 4, 8`, variables `1, 2, 4, 8`, degree
`1, 2, 4`, support `1, 4, 16`, with generic full rank, known low rank
(products of `n × r` and `r × m` polynomial factors, so `r` and a nonzero
`r`-minor are known at generation), and repeated subexpressions for batch
sharing. The three examples above are fixtures. Each record stores the
realised support of the entries, the expected generic rank, and the
expected `denom` up to sign. Mathlib translations of the fixtures belong to
`HexMatrixReflectMathlib`.

There is no comparator for this arm: `norm_rank`, the companion's declared
rank comparator, requires kernel-decidable equality of entries and declines
symbolic atoms, and neither `rank_locus` nor any other Lean tactic states a
conditional rank. The absence is declared as
**no-comparable-surface-in-named-comparator**, scoped to the symbolic rank
targets, per [benchmarking](../benchmarking.md). The report
`reports/hex-matrix-reflect-performance.md` therefore records absolute
measurements and no ratio, and Phase 4 for this arm is a measurement
report, not a speedup claim. The tables record, per rung: batch reification
and conversion time; producer time (`rankCertWith Hex.exactDiv`); `checkRank`
time in compiled code and in the kernel; the certificate size as the term
count and maximum degree of `denom`, the total term count of `adj`, and the
serialised bytes of `c`; realised intermediate support of the producer; and
proof-expression node count, `.olean` size and total elaboration, all as
fresh-module proof evidence with the matched baselines of
§Phase-4 evidence. Compiled registrations in
`bench/HexMatrixReflect/Bench.lean` (Mathlib-free) register conversion,
producer and checker separately, with checker preparation holding a
precomputed certificate; support and degree ladders are not one cubic
model, so each registration states its mode under
[benchmarking §Choosing the complexity claim](../benchmarking.md#choosing-the-complexity-claim)
and the fixed-workload registrations use mode 3 with preregistered
absolute ceilings from the first measurement. Proof probes in
`bench/HexMatrixReflectMathlib/ProofProbe` cover, on the smallest rung of
every family, the three outputs: generic rank on a `MvPolynomial` goal,
conditional rank with the condition discharged from a hypothesis, and
conditional rank leaving a side goal; each has the 120 s cleanup timeout,
and a preregistered 30 s full-proof-build ceiling per case recorded in the
external proof-runner manifest beside the numeric checks.

## Trust and migration

No `native_decide`, new axioms or trusted runtime verdicts. Kernel `decide`
proves transparent entry equalities, finite shape/index checks, arithmetic
leaves, Boolean checker acceptance and direct producer equalities. Certificate
soundness theorems prove the advertised operation from those checks.
Transport lemmas prove input reconstruction, operation correspondence and
coefficient interpretation. Noncomputable-source equalities use proved
normalization and interpretation, never evaluation of classical equality.
Audit accepted theorem axiom sets for unexpected dependencies.

Move the frontend machinery from `HexCharPoly/CharPolyElab.lean` into this
library, and its Mathlib literal enumeration, `RowCertificate` /
`MatrixCertificate` construction and RHS recognition from
`HexCharPolyMathlib/CharPolyElab.lean` into the companion's shared conversion
layer. Keep `Hex.Matrix.charPoly`, Berkowitz computation, its local certificate
checks and soundness, and `HexCharPolyMathlib.equiv_charPoly` in their owning
algorithm libraries. Generalize or reuse those checks rather than replacing
them by full kernel recomputation. Numeric polynomial reconstruction remains
available without reflection; the symbolic adapter later supplies shared
polynomial normalization instead of the bespoke structural matcher.

Current result fields are `poly` and `charPoly_eq`, not literally `value` and
`proof`. Preserve compatibility projections and the existing goal/term forms
while introducing the uniform records. Compatibility imports must be
restructured without a lower-library import of `HexMatrixTactic`: an old
frontend import may need migration to the new umbrella. Importing both
umbrellas must register each syntax handler only once.

The migration change updates `HexCharPoly/SPEC/hex-char-poly.md` and
`HexCharPolyMathlib/SPEC/hex-char-poly-mathlib.md` to name the new frontend
imports; their current umbrella promises remain accurate until that change.
Move `HexCharPoly/CharPolyElabTests.lean` and
`HexCharPolyMathlib/CharPolyElabTests.lean` into the respective
`HexMatrixTactic` and `HexMatrixTacticMathlib` directories, updating the
`HexCharPolyTests` globs in `lakefile.lean` and the corresponding build-root
allowlist. A build-only target does not exempt a test under a lower library's
directory from that library's import boundary.

## Phase-4 evidence

Follow [benchmarking](../benchmarking.md), especially fresh-module proof
evidence and the headline report format. Reports are
`reports/hex-matrix-tactic-performance.md` and
`reports/hex-matrix-tactic-mathlib-performance.md`, with **Bench targets**,
**Verdicts**, **Comparator ratios**, **Profile**, and **Concerns**
sections. The companion owns its Mathlib proof probes; it is not a
correspondence-only layer because it implements frontends and adapters.

**Fixtures.** Commit deterministic seeds, exact entries, dimensions, expected
results and hashes in `conformance-fixtures/HexMatrixTactic/matrices.jsonl`;
companion notation/interpretation cases live in
`conformance-fixtures/HexMatrixTacticMathlib/literals.jsonl`. The JSON records
contain carrier-neutral entry data; base registrations use
only Mathlib-free representations. Use the following named numeric fixture
families in the Phase-4 tables. The symbolic row reserves an extension-owned
family for later work, not a numeric Phase-4 obligation:

| Family | Parameter ladder and purpose |
|---|---|
| `dense` | Seeded full-rank square `Int` matrices, dimensions `2,4,8,16,32`, entry bits `8,32`; rational variants with denominator bits `4,16`. |
| `structured` | Tridiagonal and Vandermonde matrices on the same dimension ladder; include required pivot swaps. |
| `singular` | Duplicate rows and products of certified rank `n-1`, including a late failed pivot, on that ladder. |
| `low-rank` | Products of `n × r` and `r × m` factors with a known nonsingular `r`-minor, `n,m = 8,16,32,64`, `r = 1,2,4`; include nonleading pivot columns and rectangular shapes. |
| `large-coefficients` | Dense and rank-2 inputs, dimensions `2,4,8,16`, entry bits `64,256,1024`; record intermediate bit lengths. |
| `finite-carriers` | Base cases use `Fin 7` and `Fin 8`; companion cases in `literals.jsonl` use `ZMod 7` and `ZMod 8`. Composite cases test only determinant and characteristic polynomial. |
| `closed-algebraic` | Blocks `[[α,1],[1,α]]` with `α²=2`, and block-coupled variants, dimensions `2,4,8,16`; see companion for exact embeddings and comparator obligations. |
| `symbolic` (future `HexMatrixReflect` fixtures) | Dimensions `2,4,8`, variables `1,2,4,8`, degree `1,2,4`, support `1,4,16`; include repeated subexpressions, generic full rank and known low rank. Record realized support, not just generation limits. |

`symbolic` fixtures belong in
`conformance-fixtures/HexMatrixReflect/matrices.jsonl` with Mathlib translations
owned by `HexMatrixReflectMathlib`. Their later Phase-4 metadata and reports
own the symbolic provider measurements; the numeric frontend does not acquire
reflection imports or symbolic activation gates.

**Compiled registrations.** `bench/HexMatrixTactic/Bench.lean` remains
Mathlib-free. Register producer, certificate construction and checker
separately; checker preparation holds a precomputed certificate. Reuse the
underlying libraries' complexity claims on identical families and parameters;
frontend-specific irregular fixed workloads use mode 3 with a preregistered
comparator-anchored ceiling, explaining why modes 1 and 2 do not apply. Do not
claim one cubic time model across bit-size and symbolic-support ladders.

**Proof probes.** Reserve `bench/HexMatrixTactic/ProofProbe` and
`bench/HexMatrixTacticMathlib/ProofProbe` in each owner's `proof_probes` metadata.
Use external fresh `lake build +<module>:olean` runs with warm dependencies,
matched import-only and construction-only baselines, and variants for entry
conversion, producer-only search, certificate construction, literal emission,
replay and full elaboration. Separate construction from producer discovery;
report matched differences as attribution estimates, not additive exact
clocks. No clocks, timing loops, executables or LeanBench imports inside
probes. Record producer time, certificate construction, kernel checking,
proof-expression node count/serialized bytes, `.olean` size, and total
elaboration separately. Include one representative compiled profile per
declared numeric input family;
proof-track attribution uses the matched builds above.

The companion's metadata groups these probes as `literal-conversion`,
`certificate-replay`, and `tactic-comparison`, each spanning the applicable
numeric fixture families above. Its Profile section cites fresh-build
attribution, not compiled timed-region sampling. With two declared
comparators, it supplies the required plots
`reports/figures/hex-matrix-tactic-mathlib-comparator-<family>.svg` for these
three probe families, generated by
`scripts/plots/hex-matrix-tactic-mathlib-comparator.py` from the retained raw
samples. Here one invocation means one fresh module elaboration: plot total
wall time and baseline-adjusted elaboration time on a log-y axis across each
fixture ladder. Use separate panels for determinant and rank; component
panels compare matched conversion/replay variants with the shared full-tactic
references. Label the quantity as fresh-build time, never compiled call time.
Retain ratios and inapplicability markers for every shared case.

**Comparators.** In the companion, unmodified pinned `norm_det`/`eval_det` and
`norm_rank`/`eval_rank` are gating comparators: wiring, coverage and reported
ratios are mandatory. Run them without the Hex extensions imported, alongside
separate Hex-enabled adapter arms. Hex's current `char_poly` is the
characteristic-polynomial regression comparator; no nonexistent Mathlib
`norm_char_poly` is assumed. Compare identical literal inputs and targets;
report additional notation conversion separately. Unsupported comparator
fragments are recorded with the diagnostic and a matched supported subfamily,
never fabricated timings.

**Required checks and ceilings.** The external proof-runner manifest records
these fixed correctness/regression obligations before measurement; they are
operational limits, not portable scientific budgets:

| Check | Canonical input | Ceiling / required result |
|---|---|---|
| `syntax-compatibility` | Both frontend umbrellas, existing `det`/`rank` function names under each matrix namespace | Bare function application retains existing resolution; `det%`, `rank%`, `char_poly` return records. |
| `literal-roundtrip` | All four Mathlib syntaxes, `0 × 0`, `0 × 3`, `3 × 0`, and `2 × 2` | Exact shape and entry proofs; reject transposed/incorrect entries. |
| `numeric-proof` | `dense` dimension 4, 8-bit entries, each operation and rank inequality | Full proof-build median ≤ 10 s per case; theorem axiom audit passes. |
| `large-proof` | `large-coefficients` dimension 4, 256-bit entries | Full proof-build median ≤ 30 s per case; serialized proof ≤ 32 MiB. |
| `certificate-rejection` | Wrong value, changed pivot/minor/column coefficient, wrong size or modulus | Rejection without a theorem; median ≤ 10 s per case. |
| `algebraic-proof` | One `α²=2` block and rational literals in `ℝ`, `ℂ` | Kernel-checked transported result, median ≤ 30 s per case. |
| `bench-verify` | Smallest rung of each compiled registration | Per-library `Bench verify` 30 s soft warning; stay within the existing combined hard cap and extend the existing script only. |

Every fresh build has a 120 s cleanup timeout; timeout or incomplete pair
invalidates that evidence. Scheduled larger rungs retain timeouts as outcomes
and cannot be reported as passing samples. Recalibrate fixed ceilings only
with documented evidence, not merely to make a failure pass. Keep required
CI checks small; timing-sensitive scientific runs are manual on the shared
host, with no extra CI jobs or workflows.

Collect an even preregistered number of rounds (initially eight), adjacent
comparator/Hex pairs, alternating AB/BA. Retain every completed sample,
record host load, and automatically select one CPU when supported. Do not
wait for quiet or reject busy-host samples; allow at most one unchanged
rerun after inconclusive evidence. Record pristine commit and source hashes,
toolchain and Mathlib pin, commands, options, seeds, CPU/OS, all raw timings,
paired deltas and the exact strategy decision.

The Phase-4 target is a reproducible total-elaboration speedup over **each**
of `norm_det` and `norm_rank` on explicitly named families and eligible
rungs, with a resolved paired effect rather than a universal speed claim.
Tables contain every shared rung and list the selected strategy, each phase,
proof size, both totals, ratio and uncertainty. Set a numerical improvement
target from the baseline before optimisation; do not select only winning
samples. If there is no measured win yet, report the unmet target and planned
optimisation rather than prohibiting the frontend. Slower cases name evidence
for the cause and a remedy: kernel elimination replay → local arithmetic
certificates or a different producer; rank multiplication cost → the smaller
minor/column certificate or blocked checks; certificate size → shared literals
and coarser checked blocks; elaboration overhead → shared entry conversion and
proof caches; symbolic expansion → certified exact quotients or representation
changes. Revise the provisional strategy table from these measurements.
