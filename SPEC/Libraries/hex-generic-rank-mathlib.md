# hex-generic-rank-mathlib

The symbolic arm of the `rank` tactic and the three outputs it may produce
for a Mathlib matrix whose entries are ring expressions rather than
literals: the generic rank of the reified polynomial matrix, the rank of
the user's matrix under one nonvanishing condition, and the handoff to the
rank locus. It is the Mathlib companion of
[hex-generic-rank](hex-generic-rank.md), and it attaches a second handler to
the `rank` syntax kind that [hex-rank-mathlib](../../HexRankMathlib/SPEC/hex-rank-mathlib.md)
owns, per [matrix-tactics §Placement](../matrix-tactics.md#placement). It
adds no algorithm and no library named for being a tactic.

The outputs are the three fixed by
[hex-rank §Generic rank is not a specialised rank](../../HexRank/SPEC/hex-rank.md#generic-rank-is-not-a-specialised-rank).
The arm never presents a generic rank as the rank of a specialised matrix,
and no path below closes an equality or lower-bound goal about the user's
matrix without the certificate's condition being either proved or left as
a visible goal.

Dependencies: `HexGenericRank`, `HexRankMathlib`, `HexReflect`,
`HexReflectMathlib`, `HexMvPolyMathlib`, `HexDeterminantalIdealMathlib`,
`HexMatrixMathlib`, plus Mathlib. `libraries.yml` records the planned
entry; the library is not `correspondence_only`, since it implements a
tactic handler and owns proof probes.

## Prerequisite changes in other libraries

None of these is this library's to write, and each blocks a named part of
it.

- **`HexRankMathlib/Tactic.lean` answers `throwUnsupportedSyntax` outside
  its fragment.** Today the numeric handler throws ordinary errors for a
  matrix with free variables or a non-integer carrier
  (`Tactic.lean`, the decline branches), so a second handler on the same
  syntax kind never runs. The refactor is the one
  [matrix-tactics §Placement](../matrix-tactics.md#placement) prescribes:
  the numeric handler classifies, and outside its fragment it throws
  `throwUnsupportedSyntax` so the next handler is tried. Blocks the
  tactic; the term forms and the programmatic interface do not need it.
- **A list form of `MvPoly` arithmetic in hex-mv-poly**, with its
  denotation theorem in hex-mv-poly-mathlib: canonical term lists
  (ordered exponent-vector lists with coefficients in the carrier's kernel
  representation), addition, multiplication, scalar multiplication and
  equality by structural recursion, and the theorem identifying the list
  form with `MvPoly`'s reference operations. Blocks the kernel route
  below. Shared with `rank_locus`.
- **A residue coefficient provider in hex-reflect-mathlib.** Today
  `HexReflectMathlib/Carrier.lean` supplies the universal integer
  interpretation and a `CharP` translation theorem that is deliberately not
  a global instance; there is no provider whose carrier is a residue ring,
  and `ZMod64 p` has no global Mathlib `CommRing` instance. Until the
  provider exists, the positive-characteristic arm is specified but not
  implementable, and the finite-field example below is a statement of what
  the provider must deliver. Note that `LawfulGcdOps (ZMod64 p)` needs
  both `ZMod64.Bounds p` and `ZMod64.PrimeModulus p`
  (`HexMvGcd/Instances.lean`).

## Input classification

hex-rank-mathlib's numeric handler runs first and answers `notApplicable`
for a matrix with an entry that is not a closed literal
([matrix-tactics §Outcome protocol](../matrix-tactics.md#outcome-protocol-and-diagnostics)).
When this library is imported, its handler on the same syntax kind then
reifies the whole matrix as one
[hex-reflect batch](../../HexReflect/SPEC/hex-reflect.md#batch-reification-and-sealing):
every entry is canonicalised and reified with `reifyRing?` (top-level
variables enabled), the environment is sealed at `k` atoms, and each entry
is converted to `Hex.MvPoly k C cmp` with the characteristic-aware
conversion when `Sym.Arith` supplies the characteristic and the plain one
otherwise. `C` is the coefficient provider's carrier and `cmp` is
`Hex.Mono.grevlex`. The batch yields the *polynomial matrix*
`P : Hex.Matrix (MvPoly k C cmp) n m`, the atom valuation `v : Fin k → F`
(the sealed atom array, `F` the carrier of the user's matrix `A`), the
coefficient interpretation `ι : C → F`, and one interpretation proof per
entry, `eval₂ ι v P[i, j] = A i j`, from the
[hex-reflect soundness theorem](../../HexReflect/SPEC/hex-reflect.md#soundness-theorem).
Building `P` reads no hypotheses; hypotheses enter only when a condition
is discharged.

Routing is by the converted polynomials, not by syntax:

- A matrix in which some entry converts to a non-constant polynomial is
  handled here. One such entry is enough.
- A matrix in which every entry converts to a constant polynomial is a
  numeric matrix over `C` that the numeric handler did not recognise (a
  closed expression such as `(2 : ℝ) + 3`, or an atom that cancelled). It is
  handled here without a special case: `k` may be positive, the
  certificate's `denom` is a constant, and the single condition is a closed
  proposition discharged at step 2 of the order below.
- A subexpression outside the fixed ring language (`x / y`, `Real.exp t`, a
  symbolic power, an opaque constant) becomes one atom, and an atom is an
  independent indeterminate for the rest of the arm. Reification never
  implies that an atom is nonzero
  ([hex-reflect §Shared results and conditions](../../HexReflect/SPEC/hex-reflect.md#shared-results-and-conditions)),
  and the arm never assumes an atom is zero either: with `hx : x = 0` in
  context the polynomial matrix still contains the indeterminate for `x`,
  and the user substitutes first. Unknown nonzeroness of an atom is
  therefore not a decline reason, and neither classification nor the
  generic rank ever asks about it; it can surface only inside the one
  condition of output 2. The generic rank of `[x / y]` is `1` exactly as for
  `[x]`, its condition reads `x / y ≠ 0`, and whether that is discharged
  depends only on the local context.

The batch debits the hex-reflect budget (source nodes, atoms, reflected
nodes, exponent, terms, coefficient bits, proof nodes) and two dimensions
this library adds: matrix size, and `caseSplits`, reserved for
[piecewise rank](#piecewise-rank-later-extension) and fixed at `0` until
that extension exists. Exhaustion is a `declined` outcome naming the
dimension.

## The certificate and its kernel route

The producer is `Hex.GenericRank.genericCert P`
([hex-generic-rank](hex-generic-rank.md#the-certificate-at-mvpoly)), run in
compiled code; `c : RankCert (MvPoly k C cmp) n m` is closed data with
`c.rank = r` and `c.denom = d`. All three outputs are read off the same
`c`; in particular `d` *is* the condition of output 2.

`checkRank P c = true` is the single Boolean every soundness theorem below
consumes, and it has three parts: `d ≠ 0`; the pivot-block identity
`B * adj = d • I` for `B` the selected `r × r` block; and the all-column
identity `d • P = P_cols * (adj * P_rows)`. The conditional output needs
all three, because `checkRank_sound_at` transports the pivot-block
identity along the specialisation to obtain the lower bound wherever
`φ d ≠ 0`; no witness about some other specialisation can replace it. So
the kernel checks all three, as polynomial identities, and nothing else.

What the kernel checks is governed by
[matrix-tactics §Kernel discipline](../matrix-tactics.md#kernel-discipline):
never the producer, and never a matrix identity stated on `Hex.Matrix`.
The reference `checkRank P c` on `Hex.Matrix (MvPoly …)` is therefore
never evaluated by the kernel, at any size; a measurement cannot license
it. The kernel form is `checkRankPolyList`, the polynomial analogue of
hex-rank's `checkRankList`: the matrix as a list of rows of canonical term
lists, the certificate as `rows`, `cols`, `denom` and `adj` in the same
representation, and the three identities checked by structural recursion
with the list form of `MvPoly` arithmetic from hex-mv-poly (a prerequisite
above). Its soundness theorem, `checkRankPolyList_sound`, identifies a
passing list check with `checkRank P c = true` on the `MvPoly` values the
lists denote, through hex-mv-poly-mathlib's denotation theorem, and the
quoted `P` produced by the batch is identified with its row list
definitionally, entry by entry, exactly as `ofLists` does for integer
literals. Kernel evaluation is applied to the lists and the check only,
never to a statement containing the atoms.

Cost is the checker's `n · r · m` polynomial products at the certificate's
realised support, plus `r³` for the pivot block; the producer's pivot
search and exact divisions are never replayed. Reducing that cost by
checking an identity at sample points is not sound as a proof of the
identity and is not adopted; the realised cost is what
[§Proof probes](#proof-probes) records.

## Output 1: generic rank

The generic rank is a statement about `P`, or about its Mathlib image

```lean
S := (e P).map HexMvPolyMathlib.equiv : Matrix (Fin n) (Fin m) (MvPolynomial (Fin k) C)
```

(`e` is `HexMatrixMathlib.matrixEquiv`), never about `A`.

`S.rank = r` follows from hex-rank-mathlib's `checkRank_sound_map` at
`φ := HexMvPolyMathlib.equiv.toRingHom`, injective as a ring equivalence,
using `HexMvPolyMathlib.instCommRingMvPoly` on the source and
`MvPolynomial`'s domain instance on the target (`C` a domain with
`DecidableEq`). For any `[IsFractionRing (MvPolynomial (Fin k) C) K]`,
hex-rank-mathlib's `rank_map_eq` gives `(S.map (algebraMap _ K)).rank = r`;
`FractionRing (MvPolynomial (Fin k) C)` is the field `Frac(C)(x_1, …, x_k)`
of [hex-rank §MvPoly](../../HexRank/SPEC/hex-rank.md#mvpoly).

The handler closes a goal `M.rank = r` (or either inequality) with the
generic rank only when the goal's matrix is the symbolic matrix itself: the
carrier of `M` is `MvPolynomial σ D` for a domain `D`; every atom of the
batch is `MvPolynomial.X i` for a literal `i : σ`, so the atom valuation is
`X ∘ f` for a map `f : Fin k → σ`, and `f` is injective (the literals are
pairwise distinct); and the coefficient interpretation factors as
`ι = MvPolynomial.C.comp ι₀` for an injective `ι₀ : C →+* D`. The
registered providers satisfy the last condition: in characteristic zero
`ι` is `Int.cast` into `MvPolynomial σ D`, which is `C ∘ Int.cast` with
`Int.cast : ℤ → D` injective, and in characteristic `p` it is `C` composed
with the residue carrier's injective map into `D`. An arbitrary injective
`ι : C →+* MvPolynomial σ D` would not do, since its image could meet the
atom variables. Under these conditions the interpretation map is
`MvPolynomial.rename f ∘ MvPolynomial.map ι₀ ∘ HexMvPolyMathlib.equiv`,
injective by `MvPolynomial.rename_injective`, `MvPolynomial.map_injective`
and `RingEquiv.injective`, and `checkRank_sound_map` at that map closes the
goal. A goal over `MvPolynomial σ C` whose atoms include anything else
(`MvPolynomial.C a` for a local `a`, a `rename`, an opaque term) is a
specialised matrix like any other and goes to output 2: two distinct atoms
may be equal in the carrier, and the interpretation need not be injective.
So is a goal whose carrier is `MvPolynomial σ D` but whose coefficient
provider does not factor through `C` as above. The fraction-field form
`(M.map (algebraMap (MvPolynomial σ C) K)).rank = r` is accepted under the
same atom condition through `rank_map_eq`.

The term form is `generic_rank% A`. It returns `value := r`, the sealed
atom array, the quoted `P`, the checked `c`, and the proofs `S.rank = value`
and `A = S.map (MvPolynomial.eval₂Hom ι v)`, the latter assembled from the
batch interpretation proofs through `HexMvPolyMathlib.eval₂MathlibHom_apply`.
Its `proof` field is about `S`, and its type says so; `rank% A` never
returns a generic rank.

## Output 2: conditional rank

For `A : Matrix (Fin n) (Fin m) F` over a domain `F`, write
`ψ := MvPolynomial.eval₂Hom ι v : MvPolynomial (Fin k) C →+* F` and
`φ := HexMvPolyMathlib.eval₂MathlibHom ι v = ψ.comp equiv.toRingHom`, so
that the batch gives `A = (e P).map φ = S.map ψ`. The certificate
specialised at `v` has one condition,

```text
Condition.proposition := φ c.denom ≠ 0
```

displayed as the interpreted polynomial in the source atoms (`x ^ 2 - 1 ≠ 0`
below), with provenance `provider` this library's rank provider, `source`
the matrix expression, `operation` `"rank"`, and `reason` naming the
certificate denominator as a nonzero signed `r × r` minor of the polynomial
matrix. There is exactly one condition per invocation, so deduplication
and ordering are trivial. The theorem is

```lean
theorem checkRank_sound_at [CommRing R] [CommRing S] [IsDomain S] [DecidableEq R]
    (φ : R →+* S) (h : Hex.Matrix.checkRank A c = true) (hd : φ c.denom ≠ 0) :
    ((e A).map φ).rank = c.rank
```

Its proof is that of hex-rank-mathlib's `checkRank_sound_map`, whose
injectivity hypothesis is used only to obtain `φ c.denom ≠ 0`; the domain
hypothesis is on the target `S` only, and none is needed on the source.
hex-rank-mathlib should adopt it as the general form, with
`checkRank_sound_map` as the corollary, and until then this library proves
it from hex-rank-mathlib's transport lemmas. It is the statement "rank exactly `r` wherever `denom`
does not vanish" of hex-rank §Generic rank is not a specialised rank.

The condition is sufficient, not necessary. `d` is a unit multiple of the
minor `det B ∈ I_r(P)`, so `V(I_r(P)) ⊆ V(d)`, and the inclusion is strict
in general: `!![x, y]` has generic rank `1` with pivot minor `x`, so the
condition is `x ≠ 0`, while the rank is `1` wherever `(x, y) ≠ (0, 0)`.
The arm does not search for a minor whose nonvanishing is easier to
discharge; that search, and the exact set, belong to output 3 and to the
later extension. Consequently the arm can fail to close a true goal
(`!![x, y].rank = 1` from `hy : y ≠ 0`), and the diagnostic then names the
condition, the generic rank and `rank_locus`.

The upper bound needs no condition. Over a field `F`,
hex-determinantal-ideal-mathlib's `rank_map_le_rank_fractionRing` at `ψ`
(applied to `e.symm S`) and hex-rank-mathlib's `rank_map_eq_rank_fractionRing`
give `A.rank ≤ S.rank = r`. That theorem is stated over a field; over a
domain that is not a field the upper bound passes through `rank_map_eq`
at the domain's fraction field first, which is also how integer rank is
defined in hex-rank-mathlib. `checkRank_sound_at` needs only a domain.

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
substituting `hx` and using the numeric handler, not by this arm. The term
form `rank% A` has no `r'`: it returns `value := r` with proof `A.rank = r`
when the condition is discharged at steps 1 and 2 below, and otherwise
declines with the condition displayed, the rule that an unconditional term
form declines unresolved conditions. The programmatic interface returns a
`ConditionalResult` whose `conditions` array holds the one condition and
whose `proof` depends on it. Neither creates goals, as
[hex-reflect §Shared results and conditions](../../HexReflect/SPEC/hex-reflect.md#shared-results-and-conditions)
requires of term and programmatic interfaces.

Conditions are processed in the hex-reflect order and nowhere else:

1. definitional equality and matching local hypotheses (a hypothesis whose
   type is definitionally the displayed proposition);
2. explicitly configured cheap normalisers; the default list contains only
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

## Output 3: rank locus

The exact set of points where the rank drops below `r` is the zero set of
the determinantal ideal `I_r(P)`, and the tactic that produces it is
`rank_locus` (later SPEC; see
[hex-determinantal-ideal §Consumers](../../HexDeterminantalIdeal/SPEC/hex-determinantal-ideal.md#consumers)).
The `rank` tactic never states a locus. The handoff is programmatic:
`rank_locus` invoked without an explicit `r` calls this library's
generic-rank provider, receives the `ProviderOutcome` carrying `P`, `c` and
the sealed environment, takes `r := c.rank`, and runs `detIdealGens r P` on
that same `P`, so its generators are over the same atoms as the `rank`
diagnostics. The default `r` is therefore the generic rank, and the default
locus is "rank drops below the generic rank". Note the types: `P` has
coefficients in `C` and the user's atoms take values in `F` through
`ι : C →+* F`, while hex-determinantal-ideal's `InLocus` and
`mem_zeroLocus_iff_rank_lt` today take a matrix over `MvPoly k F cmp` and
a point in the same field. The locus statement the user needs is the
headline theorem at `φ := eval₂Hom ι v`, which `rank_lt_iff_minors_map_eq_zero`
already provides for any ring homomorphism into a field; the `eval₂`
form of the zero-locus statement, and the `FractionRing F` passage when
`F` is a domain that is not a field, are the `rank_locus` SPEC's to add to
hex-determinantal-ideal-mathlib. Choosing `r` is the whole of this arm's
part; the locus goal forms and the display of generators belong to
`rank_locus`.

## Piecewise rank (later extension)

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

## Three examples

**`[x]`**, `x : F` an element of a characteristic-zero field, so the
coefficient provider is `Int`. `k = 1`, `P = [X_0]`, `r = 1`, `d = X_0`.

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
reduces coefficients, not exponents, so `P = [X_0³ − X_0]`, `r = 1`,
`d = X_0³ − X_0`. The coefficient carrier `C` is the residue provider's
carrier (a prerequisite above): it must supply `LawfulGcdOps C` for the
producer, which `ZMod64 p` does under `ZMod64.Bounds p` and
`ZMod64.PrimeModulus p` (`HexMvGcd/Instances.lean`), and for the companion
a Mathlib `CommRing C` with an injective `C →+* ZMod 3`, which `ZMod64 p`
does not have today (`HexModArithMathlib.ZMod64.equiv` is the ring
equivalence, but the global `CommRing` instance is absent, as
[hex-det-mathlib](hex-det-mathlib.md) records). Until that provider
exists this example is the statement of what it must deliver, not a test.

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

## Proof probes

The bar of [matrix-tactics §The bar against Mathlib](../matrix-tactics.md#the-bar-against-mathlib)
has two parts. The accepted fragment is strictly larger by construction:
`eval_rank` requires kernel-decidable equality of entries and declines
symbolic atoms, and no Lean tactic states a conditional rank, so the
comparator absence is declared as
**no-comparable-surface-in-named-comparator**, scoped to the symbolic
targets, per [benchmarking](../benchmarking.md). The speed half is
therefore a measurement report with absolute numbers and preregistered
ceilings, not a ratio.

Proof probes in `bench/HexGenericRankMathlib/ProofProbe` cover, on the
smallest rung of every family of
[hex-generic-rank §Benchmarking](hex-generic-rank.md#benchmarking) and on
the three examples above, the three outputs: generic rank on a
`MvPolynomial` goal, conditional rank with the condition discharged from a
hypothesis, and conditional rank leaving a side goal. Each records, as
fresh-module proof evidence with matched import-only baselines: batch
reification and conversion time; producer time; the kernel time of
`checkRankPolyList`, split between the pivot-block identity and the
all-column identity, so the realised cost of list-form polynomial
arithmetic is on record; proof-expression node count, `.olean` size and
total elaboration. Each probe has the 120 s cleanup timeout and a
preregistered 30 s full-proof-build ceiling per case recorded in the
external proof-runner manifest beside the numeric checks. The report is
`reports/hex-generic-rank-mathlib-performance.md`.

## File organisation

```
HexGenericRankMathlib/
  Transport.lean    -- S, the atom-condition lemmas, eval₂ transport
  Sound.lean        -- checkRank_sound_at, generic-rank and fraction-field forms
  Kernel.lean       -- checkRankPolyList, checkRankPolyList_sound, list identification of the batch's P
  Provider.lean     -- the hex-reflect provider, conditions, budgets
  Tactic.lean       -- the handler on hex-rank-mathlib's `rank` syntax kind; generic_rank%, rank%
  Tests.lean
HexGenericRankMathlib.lean
```

`libraries.yml` gains

```yaml
  HexGenericRankMathlib:
    deps: [HexGenericRank, HexRankMathlib, HexReflect, HexReflectMathlib, HexMvPolyMathlib, HexDeterminantalIdealMathlib, HexMatrixMathlib]
    mathlib: true
    proof_probes: [bench/HexGenericRankMathlib/ProofProbe]
    done_through: 0
    status: planned
```

## Mathlib inventory

Checked against the pinned Mathlib by name: `MvPolynomial.rename_injective`,
`MvPolynomial.map_injective`, `MvPolynomial.eval₂Hom`, `RingEquiv.injective`,
`IsFractionRing`, `FractionRing`. Hex names used: `checkRank_sound_map`,
`rank_map_eq`, `rank_map_eq_rank_fractionRing` (`HexRankMathlib/Extension.lean`),
`rank_map_le_rank_fractionRing` (`HexDeterminantalIdealMathlib/Rank.lean`),
`InLocus` (`HexDeterminantalIdeal/MvPoly.lean`), `mem_zeroLocus_iff_rank_lt`
(`HexDeterminantalIdealMathlib/Locus.lean`), `detIdealGens`
(`HexDeterminantalIdeal/Minors.lean`), `eval₂MathlibHom`
(`HexMvPolyMathlib/Aeval.lean`), `instCommRingMvPoly`
(`HexMvPolyMathlib/Equiv.lean`), `RankWitness`, `checkRankList`
(`HexRank/Kernel.lean`), `rank_eq_of_checkList` (`HexRankMathlib/Kernel.lean`),
`rankCertWith_check` (`HexRankMathlib/Cert.lean`), `syntax (name := rankTac)`
(`HexRankMathlib/Tactic.lean`). An implementer re-runs these searches when
the pins move.
