# hex-finite-field (a generic finite field interface, and equal-degree splitting)

A Mathlib-free interface describing what a type has to supply to be used
as `F_q` by the factoring algorithms, instances for the two finite field
representations the tree already has, the generic quotient-arithmetic
layer the algorithms run over, and the equal-degree stage
(Cantor-Zassenhaus) that the interface makes worth having.

This SPEC expands the "Generic finite fields, and equal-degree
splitting" entry in [future-work](../future-work.md), which describes
three items in dependency order: genericity, an explicit equal-degree
stage, and Cantor-Zassenhaus. It keeps that order. Only the first item
is a new library; the second and third are specified here as amendments
to [hex-berlekamp](../../HexBerlekamp/SPEC/hex-berlekamp.md), for the
reason set out under "Where the equal-degree stage lives".

Three claims in that entry need correcting before anything is built,
and all three are corrected below.

- **The linear algebra is already generic.** The entry lists "the
  linear algebra Berlekamp's kernel step uses" among the things the
  interface has to cover. `Matrix.nullspace` in
  `HexRowReduce/Api.lean:88` is already stated for
  `[Lean.Grind.Field R] [DecidableEq R]`, and `DensePoly.gcd`,
  `xgcd`, `divMod`, and `modByMonic` in `HexPoly/Euclid/DivGcd.lean`
  are already stated for a bare operation list. Nothing in the
  interface needs to mention linear algebra.
- **`GFq p n` is not the type to generalise over.** `GFq p n h` in
  `HexGFq/Basic.lean:446` takes a `Conway.SupportedEntry p n`, and the
  committed table covers `p ∈ {2, 3, 5, 7, 11, 13}` with `n ≤ 6`. The
  type that admits an arbitrary finite field is
  `GFqField.FiniteField f hf hp hirr`, which takes any irreducible
  modulus. The interface is instantiated at that type; `GFq p n h` gets
  it by inheritance.
- **There is no existing pattern of separating a random draw from a
  deterministic function.** The entry says the explicit-argument
  convention follows one. No production library in the tree consumes
  randomness; the only pseudorandom streams are deterministic LCGs in
  bench and conformance drivers (`bench/HexResultant/Bench.lean:42`,
  `conformance/HexGF2/CrossCheck.lean:60`), which are fixture
  generators rather than algorithm inputs. This item introduces the
  convention rather than following it, so it also has to introduce the
  generator. See "Randomness".

## Why this library exists

**hex-berlekamp is written against one field.** Every declaration in
`HexBerlekamp/` carries `{p : Nat} [ZMod64.Bounds p]` and operates on
`FpPoly p = DensePoly (ZMod64 p)`. Nothing in the algorithms needs
that: the Berlekamp matrix is the matrix of a `q`-linear map, the
kernel step is a nullspace over the coefficient field, and the split
step is a gcd. What the algorithms need of the coefficient type is a
short list, and this library writes it down.

**The extension-field case already exists and is unused.**
`GFqField.FiniteField f hf hp hirr` has `Lean.Grind.Field`
(`HexGFqField/Operations.lean:1085`), `Lean.Grind.IsCharP _ p`
(`:1117`), `DecidableEq` through `GFqRing.PolyQuotient`
(`HexGFqRing/Basic.lean:88`), and `frob = (· ^ p)` definitionally
(`frob_eq_pow`). So `DensePoly (FiniteField f hf hp hirr)` is already a
polynomial ring with division, gcd, and extended gcd, and matrices over
it already row-reduce. What is missing is the arithmetic that mentions
`q`: the `q`-power Frobenius, the cardinality, an enumeration, and a
source of random elements.

**The constant sweep does not survive the extension case.**
`berlekampFactor` splits with `kernelWitnessSplit?`
(`HexBerlekamp/Factor.lean:308`), which sweeps `c` over all `p` field
constants in `gcd(f, w - c)`. At `p ≤ 500`, the range the
Berlekamp-Zassenhaus prime list uses, that is fine. Over `F_{2^{64}}`
it is not a slow algorithm, it is not an algorithm. Equal-degree
splitting is what replaces it, and it is the reason the genericity item
is worth doing rather than being a refactor for its own sake.

**Distinct-degree factorization is exported and unused.**
`distinctDegreeFactor` (`HexBerlekamp/DistinctDegree.lean:178`) is
referenced only by `bench/HexBerlekamp/Bench.lean` and the two
conformance drivers. No factorization path calls it. So the pipeline
this SPEC describes is not a rearrangement of code that already runs
in that order; it is the first consumer of a component the library
already ships.

## Scope

In scope for `hex-finite-field`: the `FiniteFieldOps` and
`LawfulFiniteField` classes, instances for `ZMod64 p` and
`GFqField.FiniteField f hf hp hirr`, the deterministic pseudorandom
generator the Las Vegas algorithms consume, generic `q`-power Frobenius
on `DensePoly K` and on `K` itself, and the generic Frobenius matrix.

In scope as amendments elsewhere: moving field-generic modular powering
out of hex-poly-fp into hex-poly, adding the two instances at their
types, and the equal-degree stage and Cantor-Zassenhaus in
hex-berlekamp.

Not in scope: normal bases, Zech logarithms, `fq_zech`-style
small-field representations, field extension towers (that is
hex-number-field-tower's subject over `ℚ`, and has no `F_q` analogue in
this tree yet), discrete logarithms, and the packed `GF(2^n)` path,
which stays in hex-gf2 with its own optimised arithmetic and receives
an instance rather than a reimplementation.

## Prerequisites

Five things have to exist before the interface can be stated, let alone
instantiated. Each was found by checking the source rather than the
SPECs, and each is a real development rather than a relocation. They are
listed here, at the front, because an earlier draft of this SPEC called
the whole item "the best-aligned on the list" on the strength of
components that turn out not to compose.

1. **A quotient-representation bridge for `pow_card`**, as set out
   above. Without it the extension-field instance has no proof.

2. **Generic `DensePoly.DivModLaws` and `DensePoly.GcdLaws`.** The
   executable `divMod`, `modByMonic`, `xgcd`, and `gcd` are generic in
   their operation lists, but every theorem about them is stated under
   these two law classes, and the Mathlib-free instances are for
   `ZMod64 p` (`HexPolyFp/Field.lean:710`, `:824`) and `Rat`
   (`HexPolyZ/Rational.lean:1196`, `:1269`) only. The one generic
   instance, `instDivModLawsField` / `instGcdLawsField`
   (`HexPolyMathlib/Euclid.lean:190`, `:252`), is on the Mathlib side
   and requires a Mathlib `Field`. So a Mathlib-free
   `[Lean.Grind.Field K] [DecidableEq K] → DivModLaws K` and the
   matching `GcdLaws K` are prerequisites, in hex-poly. Until they
   exist, "the polynomial operations are already generic" is true of
   the code and false of the proofs.

3. **The prime-field algebraic instances are in the wrong library for
   the dependency list.** `DecidableEq (ZMod64 p)`
   (`HexPolyFp/Field.lean:45`) and `Lean.Grind.Field (ZMod64 p)`
   (`HexPolyFp/PrimeField.lean:100`) live in hex-poly-fp, not
   hex-mod-arith. Either they move down, or hex-finite-field depends on
   hex-poly-fp. This SPEC takes the second option, because moving a
   field instance out of the library that proves it is a larger change
   than adding an edge, and because hex-berlekamp already sits above
   hex-poly-fp so no new constraint is introduced.

4. **Generic square-free decomposition.**
   `FpPoly.squareFreeDecomposition` (`HexPolyFp/SquareFree.lean:40`) is
   a large `FpPoly`-specific development (six files, roughly 8000
   lines, `HexPolyFp/SquareFree/`). Yun in characteristic `p` also
   needs a coefficient `p`-th root when a derivative vanishes, which
   over `F_q` is the inverse Frobenius `x ↦ x^(q/p)` and is not in the
   interface above. Generalising it is its own milestone, not a
   consequence of generalising the factorizer.

5. **The packed `GF(2^n)` algebraic tower.** `GF2n`
   (`HexGF2/Field.lean`) has the arithmetic operations and
   `mul_inv_cancel`, but no `DecidableEq`, no `Lean.Grind.Field`, and
   no `Lean.Grind.IsCharP`. It cannot satisfy the generic context until
   those exist. The `GF2n` instance is therefore a milestone with its
   own acceptance criteria, not a line in a table.

None of these is a reason not to do the item. All five are reasons the
item is larger than one library plus two amendments, and the milestone
list at the end reflects them.

## The interface

Two classes, split the way [hex-mv-gcd](hex-mv-gcd.md) splits `GcdOps`
from `LawfulGcdOps`: operations a consumer may compute with, and laws a
consumer may prove with.

```lean
namespace Hex

/-- The executable data a type must supply to be used as `F_q` by the
factoring algorithms. `char` is the characteristic and `deg` the degree
over the prime field, so the cardinality is `char ^ deg`; both are
`Nat` fields rather than derived quantities, because a Mathlib-free
library has no `Fintype`. -/
class FiniteFieldOps (K : Type u) where
  char : Nat
  deg  : Nat
  /-- The `char`-power Frobenius. Cheap where the representation makes
  it cheap: the identity on a prime field, one modular powering on an
  extension, a squaring on `GF(2^n)`. -/
  frob : K → K
  /-- Index the field. `ofIndex` is a bijection from `[0, card)` onto
  `K`; `toIndex` inverts it. Used by the constant sweep and by the
  random draw, and by nothing else. -/
  ofIndex : Nat → K
  toIndex : K → Nat

/-- The cardinality of `K`. -/
@[expose] def card (K : Type u) [FiniteFieldOps K] : Nat :=
  FiniteFieldOps.char K ^ FiniteFieldOps.deg K
```

```lean
/-- The algebraic facts the algorithms use. Separated from the
operations so a consumer may compute without them, and so the
instances may be discharged one at a time. -/
class LawfulFiniteField (K : Type u) [Lean.Grind.Field K] [DecidableEq K]
    [FiniteFieldOps K]
    extends Lean.Grind.IsCharP K (FiniteFieldOps.char K) : Prop where
  char_prime  : Hex.Nat.Prime (FiniteFieldOps.char K)
  deg_pos     : 0 < FiniteFieldOps.deg K
  frob_eq_pow : ∀ x : K, FiniteFieldOps.frob x = x ^ FiniteFieldOps.char K
  /-- The defining identity of `F_q`. Everything below rests on it. -/
  pow_card    : ∀ x : K, x ^ card K = x
  /-- `ofIndex` and `toIndex` are mutually inverse on the index range. -/
  toIndex_lt      : ∀ x : K, toIndex x < card K
  ofIndex_toIndex : ∀ x : K, ofIndex (toIndex x) = x
  toIndex_ofIndex : ∀ i, i < card K → toIndex (ofIndex i) = i
```

`LawfulFiniteField` **extends** `Lean.Grind.IsCharP K (FiniteFieldOps.char K)`.
An earlier draft left it out, on the grounds that a consumer could ask
for it separately. That is wrong: the freshman's dream
`(a + b)^p = a^p + b^p` is what makes every Frobenius argument below
work, it is not implied by the other fields, and every generic
algorithm in this SPEC needs it. Both instances already have it
(`HexGFqField/Operations.lean:1117` for the extension case), so
bundling costs nothing.

`pow_card` is the load-bearing law and it is the one worth checking is
dischargeable before committing to the class. It is:

- **`ZMod64 p`** -- Fermat's little theorem, which hex-arith has as
  `Hex.Nat.pow_prime_mod` (`HexArith/Nat/Prime.lean:527`), transported
  along `ZMod64.toNat`. Here `deg = 1` and `card = p`.
- **`FiniteField f hf hp hirr`** -- **not immediate, and this is the
  prerequisite that gates the whole library.** hex-poly-fp proves
  exactly the right theorem,
  `FpPoly.Quotient.pow_card_eq_self_of_irreducible`
  (`HexPolyFp/Quotient.lean:1660`), but for the *wrong representation*:
  it is stated for `FpPoly.Quotient g hmonic hg_pos`, which carries a
  monicity hypothesis, while `GFqField.FiniteField f hf hp hirr` wraps
  `GFqRing.PolyQuotient f hf` (`HexGFqField/Basic.lean:30`), whose
  modulus is only of positive degree and irreducible. No bridge between
  the two quotient representations exists.

An earlier draft of this SPEC claimed this instance needed "no new
mathematics" by citing the weaker propagation lemma
`pow_pPowN_eq_self_of_pow_pPowN_X_eq_X`
(`HexPolyFp/QuotientFrobenius.lean:381`), which only pushes the
hypothesis `X^(p^n) = X` out to every element and does not derive it
from irreducibility. That claim was wrong twice over: the stronger
theorem exists, and neither applies to the type the instance is for.

The prerequisite is therefore one of three, and the choice should be
made before milestone 1 starts:

1. an equivalence `GFqRing.PolyQuotient f hf ≃ FpPoly.Quotient (toMonic f) _ _`
   with `pow_card` transported along it, which is the smallest change
   and the one this SPEC assumes;
2. a direct Mathlib-free cardinality argument for
   `GFqRing.PolyQuotient`, duplicating the existing proof; or
3. changing `FiniteField` to use the already-proved quotient type,
   which is a representation change in an `active`, `done_through: 7`
   library.

Option 1 is a real development -- the two quotient types have different
reduction functions and different canonical-form invariants -- and it is
listed in "Prerequisites" below rather than waved at.

`ofIndex` and `toIndex` are a bijection with `[0, card)` and nothing
more. They are **not** a ring map, they are not required to be
monotone, and no algorithm may use them for anything but enumeration
and random draws. Stating them as an indexing rather than as an
`Array K` of all elements is deliberate: `Array K` of size `q` is
representable at `q = 500` and is not representable at `q = 2^{64}`,
and the class must not be shaped by the small case.

`hex-gfq-field`'s SPEC says that "`Fintype` and cardinality belong in
the Mathlib companion, not here". `FiniteFieldOps.card` does not
contradict that: it is a `Nat` a consumer supplies, not a theorem about
the size of the type. The theorem `Fintype.card K = card K` is the
companion's, and hex-gfq-mathlib already promises it as
`card_finiteField`.

## Instances

```lean
instance (p : Nat) [ZMod64.Bounds p] : FiniteFieldOps (ZMod64 p) where
  char := p
  deg  := 1
  frob := id                      -- Fermat; see `frob_eq_pow` below
  ofIndex := ZMod64.ofNat p
  toIndex := ZMod64.toNat

instance {f : FpPoly p} {hf : 0 < FpPoly.degree f} {hirr : FpPoly.Irreducible f} :
    FiniteFieldOps (GFqField.FiniteField f hf hp hirr) where
  char := p
  deg  := FpPoly.degree f
  frob := GFqField.frob
  ofIndex := ...                  -- base-`p` digits of `i` as coefficients
  toIndex := ...                  -- the coefficient vector read in base `p`
```

`frob = id` on the prime field is the point of having `frob` in the
class at all: `frob_eq_pow` then says `x = x ^ p`, which is Fermat, and
every generic algorithm that iterates Frobenius pays nothing on the
prime field instead of paying a `log p`-step modular powering. The
existing `FpPoly.frobeniusXMod` computes `X^p mod f` by
square-and-multiply on the exponent `p`; the generic code must not
inherit that cost when `deg = 1`.

`GF2n` from hex-gf2 gets an instance too, with `frob` the squaring
map, `char = 2`, and `ofIndex` the packed word; `GF2q n` is an
abbreviation declared in hex-gfq (`HexGFq/Basic.lean:800`) and inherits
it. Prerequisite 5 is what that instance waits on. That instance
is the reason the class is stated over an abstract `K` rather than
being a structure of functions on `FpPoly`: hex-gf2's representation is
a packed `UInt64` vector, not a coefficient array, and the whole point
is that the factoring algorithms should run over it unchanged. It goes
in `hex-gf2` rather than here, so that hex-finite-field does not
acquire a dependency on hex-gf2.

**Where each instance lives.** The class lives here. The `ZMod64 p`
instance lives here (this library depends on hex-mod-arith). The
`FiniteField` instance lives in **hex-gfq-field**, and the `GF2n`
instance in **hex-gf2**, each next to its type. Splitting class from
instance across libraries is what keeps the DAG acyclic and is
discussed under "Placement in the DAG".

## Placement in the DAG

The DAG constrains this design more than the future-work entry
suggests, and the constraint is worth stating because it is easy to get
backwards.

`libraries.yml` declares `HexGFqField: deps: [HexGFqRing, HexBerlekamp]`.
The source dependency is only `HexGFqRing` -- `HexGFqField/Basic.lean`
and `HexGFqField/Operations.lean` import `HexModArith.Prime`,
`HexGFqRing.Basic`, `HexGFqRing.Operations`, and `Init.Grind.Ring.Field`,
and nothing from hex-berlekamp. The declared dependency is real but it
comes from the test surface: `conformance/HexGFqField/Conformance.lean`,
`conformance/HexGFqField/EmitFixtures.lean`, and
`bench/HexGFqField/Bench.lean` each import
`HexBerlekamp.RabinSoundness` to produce the irreducibility witnesses
their fixtures need.

The consequence: **hex-gfq-field is above hex-berlekamp**, so a library
containing both the interface and the extension-field instance would
also be above hex-berlekamp, and hex-berlekamp could not be written
against the interface. The resolution is the standard one -- the class
goes below hex-berlekamp, the instance goes at its type -- and it is
why the instance list above is split.

```
hex-arith ── hex-mod-arith ── hex-poly-fp ─┐
hex-poly ──────────────────────────────────┼── hex-finite-field
hex-matrix ────────────────────────────────┘        │
                                                    ├── hex-berlekamp
                                                    ├── hex-gfq-field (instance)
                                                    └── hex-gf2      (instance)
```

`hex-finite-field` deps:
`[HexArith, HexModArith, HexPoly, HexPolyFp, HexMatrix, HexBasic]`.
hex-poly-fp is needed for `DecidableEq (ZMod64 p)` and
`Lean.Grind.Field (ZMod64 p)`, which live there rather than in
hex-mod-arith (prerequisite 3); hex-matrix for `frobeniusMatrix`. This
is the one authoritative dependency list; the `libraries.yml` block at
the end repeats it and nothing else in this file states it again.

## The generic quotient layer

Everything the factoring algorithms do in `F_q[x]/(f)` reduces to
modular powering, modular composition, and the `q`-power Frobenius.
The first two are field-generic already in their bodies but are sited
at `FpPoly p`; the third is new.

### Required amendment to hex-poly

`FpPoly.powModMonicAux`, `powModMonic`, and `powModMonicLinear`
(`HexPolyFp/Frobenius.lean:32`, `:50`, `:66`) use only `modByMonic`,
`*`, and `1`. `DensePoly.modByMonic` is already generic
(`HexPoly/Euclid/DivGcd.lean:1065`). So these three belong in
**hex-poly**, next to `modByMonic`, stated for `DensePoly R` over the
same operation list `divMod` takes. `FpPoly.powModMonic` becomes an
abbreviation, so no hex-poly-fp caller changes.

`FpPoly.composeModMonic` (`HexPolyFp/ModCompose.lean:64`) and its
`@[csimp]` twin `composeModMonicImpl` move the same way and for the
same reason.

`FpPoly.linearPow` (`HexPolyFp/Degree.lean:1216`) stays where it is:
it is the kernel-reducible specification twin, its lemma surface is
`ZMod64`-specific in places, and no generic algorithm calls it.

This is a relocation, not a generalisation of an algorithm, and it is
the only change hex-poly needs.

### The `q`-power Frobenius

```lean
namespace Hex.FiniteField

variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
  [FiniteFieldOps K] [LawfulFiniteField K]

/-- `X^q mod f`, by square-and-multiply on the exponent `card K`. -/
def frobeniusXMod (f : DensePoly K) (hmonic : DensePoly.Monic f) : DensePoly K

/-- The matrix of `h ↦ h^q mod f` in the basis `1, X, …, X^{n-1}`,
built from `frobeniusXMod` by `n` modular multiplications. -/
def frobeniusMatrix (f : DensePoly K) (hmonic : DensePoly.Monic f) :
    Matrix K (DensePoly.degree f) (DensePoly.degree f)

/-- Apply the `q`-power Frobenius to a reduced representative. -/
def frobeniusApply (Q : Matrix K n n) (h : DensePoly K) : DensePoly K
```

**Only the `q`-power map is `K`-linear, and this is the place to be
careful.** On `K[x]/(f)` the map `x ↦ x^q` satisfies
`(a+b)^q = a^q + b^q` in characteristic `p` and `(c·a)^q = c^q a^q = c a^q`
for `c ∈ K`, the second step using `pow_card` on the coefficient field.
So it is `K`-linear, it has a matrix over `K`, and iterating it is one
matrix-vector product at `O(n²)`.

The `p`-power map is **not** `K`-linear when `deg K > 1`: it is
`p`-semilinear, `(c·a)^p = c^p a^p`, and `c^p ≠ c` in general. It has no
matrix over `K`, and an earlier draft of this SPEC proposed building one
and iterating it. That was wrong, and the same error appeared in the
characteristic-two trace, which is `F_2`-linear rather than `K`-linear.
`FiniteFieldOps.frob` is a coefficientwise operation, and any algorithm
that wants the `p`-power map on the quotient has to compose it with a
modular composition, never with a `Matrix K`.

**One algorithm, not three.** An earlier draft described `frobeniusXMod`
as `deg K` modular multiplications in one place, as modular compositions
or matrix-vector products in another, and as one square-and-multiply in
the complexity table. Those are different algorithms. The specified v1 is
the last: `frobeniusXMod = powModMonic X f hmonic (card K)`, costing
`O(log q)` modular squarings at `O(n²)` each, so `O(n² log q)`. On the
prime field `card K = p` and this is exactly what
`FpPoly.frobeniusXMod` does today, so the prime-field path is unchanged.

`frobeniusMatrix` then costs `n` modular multiplications, `O(n³)`, and
every subsequent Frobenius application is `O(n²)`. That is the whole
Frobenius story, and any faster `p`-power path (coefficient Frobenius
plus Brent-Kung composition) is an optimisation with its own SPEC
amendment, not an alternative reading of this one.

**Modular composition is Horner today.** `composeModMonicImpl`
(`HexPolyFp/ModCompose.lean:71`) is an `Array.foldr` Horner loop, so
`g(h) mod f` costs `n` modular multiplications, `O(n³)`. Repeating that
per distinct-degree step would be `O(n⁴)`, which is why the matrix is
the specified route rather than one of two equally good options. The
Brent-Kung composition that [future-work](../future-work.md) lists under
"Fast polynomial arithmetic" would change that, and this library is the
consumer that entry names.

## Randomness

The tree has no randomness. `Hex.Rand` is new, and it is small.

```lean
namespace Hex

/-- A splitmix64 state. Deterministic, seedable, and reproducible
across runs and platforms; this is a source of arbitrary values for
Las Vegas search, not a cryptographic generator, and nothing in the
tree may treat it as one. -/
structure Rand where
  state : UInt64

def Rand.next (r : Rand) : UInt64 × Rand
/-- Uniform on `[0, bound)` by rejection sampling over enough words to
cover `bound`. Not `next % bound`, which is biased, and not one word,
which cannot reach `bound > 2^64`. -/
def Rand.nat (r : Rand) (bound : Nat) : Nat × Rand
def Rand.ofSeed (seed : Nat) : Rand
```

Sampling a field element is `FiniteFieldOps.ofIndex` applied to
`Rand.nat r (card K)`, and sampling a polynomial of degree below `n` is
`n` independent element draws. Both need `Rand.nat` to be uniform on a
bound that may exceed `2^64`: `card K` is `2^64` for `GF(2^{64})` and
`card K ^ n` is far larger. Rejection sampling over `⌈log₂ bound / 64⌉`
words is the specified implementation, and the bias of `% bound` is the
reason it is specified rather than left open.

`Rand` belongs in **hex-basic**, not here. It has no dependencies, and
it has a second consumer already specified: [hex-mv-gcd](hex-mv-gcd.md)
route 4 draws random evaluation points for Zippel's interpolation, and
says so. Two consumers in different subtrees is the argument for a root
library.

The discipline, which this item sets rather than follows:

- Every randomised function takes `Rand` as an explicit argument and
  returns the advanced state. No monad, no `IO`, no global generator.
- The seed is a parameter of the public entry point with a documented
  default, so a failing input can be replayed exactly.
- Randomness affects **how long** a Las Vegas algorithm runs, never
  **what** it returns. Every randomised result passes the same checker
  the deterministic path would.
- Fuel is explicit and finite. Fuel exhaustion is a documented
  outcome, reported in the return type, never as a wrong answer and
  never as a nonterminating loop.
- **Probability statements are about ideal draws, not about
  splitmix64.** Every bound below (`2^{1-r}` per attempt, and the union
  bounds derived from it) is a statement about independent uniform
  draws. A fixed seeded stream is deterministic, so those bounds
  describe the algorithm's design and the expected behaviour over
  seeds; they are not theorems about a particular run, and nothing in
  the tree may treat them as such.

## Where the equal-degree stage lives

The equal-degree stage and Cantor-Zassenhaus go in **hex-berlekamp**,
not in this library and not in a new one. Three reasons, in order of
weight:

1. **The `factor_poly` and `irreducibility` tactic drivers are in
   hex-berlekamp** (`FactorPolyElab.lean`, `IrreducibilityElab.lean`,
   `TacticCore.lean`), and their native `FpPoly p` arm calls the
   factorizer directly. A better factorizer above them would have to
   reach the tactic through the `Hex.FactorTactic.Provider` hook, which
   exists for *other input types* rather than for a better algorithm on
   the same type. Routing `FpPoly p` through a provider to reach a
   faster implementation of the same function is the wrong use of that
   mechanism.
2. **Distinct-degree factorization is already there.** EDF consumes DDF
   output. Splitting them across libraries puts the two halves of one
   pipeline on either side of a release boundary.
3. **The Berlekamp kernel stays in the pipeline.** It is not replaced;
   it is the small-`q` path and the source of the factor count `r`,
   which EDF uses for its own early exit. Two algorithms that call each
   other belong together.

What goes where is therefore: the interface, the instances, the generic
Frobenius, and `Rand` are new; the algorithms are hex-berlekamp
amendments. The rest of this SPEC specifies those amendments.

## Amendment 1: generalising hex-berlekamp

Not mechanical, and an earlier draft of this SPEC called it that. It
splits into four stages with separate acceptance criteria, because they
have separate risks.

### 1a. Executable genericization

Every declaration in `HexBerlekamp/Basic.lean`,
`HexBerlekamp/DistinctDegree.lean`, `HexBerlekamp/Factor.lean`, and
`HexBerlekamp/Irreducibility.lean` currently binds
`{p : Nat} [ZMod64.Bounds p]` and works on `FpPoly p`. The generic form
binds

```lean
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
    [FiniteFieldOps K] [LawfulFiniteField K]
```

and works on `DensePoly K`, with `p` replaced by `card K` in every
exponent. `FpPoly p` entry points remain as specialisations.

Three places need more than a substitution.

- **`berlekampColumn`** builds columns from `FpPoly.frobeniusXMod`,
  which becomes `FiniteField.frobeniusXMod`. Over an extension field the
  `p`-power Frobenius is the wrong map: its fixed field is `F_p`, not
  `F_q`, so `Q_p - I` has the wrong nullspace and the factorization is
  silently wrong rather than ill-typed. This is the one place where a
  careless generalisation type-checks and lies, and the conformance
  suite carries a case for it.
- **`kernelWitnessSplit?`'s constant sweep** is bounded by the literal
  `p` in `cachedSplitAux f witness reduced p 0`
  (`HexBerlekamp/Factor.lean:308`). Generically it is `card K`, and it
  is guarded: the sweep runs only below a measured threshold and is
  otherwise skipped in favour of EDF.
- **Rabin's test** holds with `q` for `p` throughout and `n` the degree
  over `F_q`.

Acceptance: the generic code compiles, the `FpPoly` specialisations are
definitionally the old ones, and the existing conformance fixtures pass
unchanged.

### 1b. Proof genericization

The blocker. `divMod`, `modByMonic`, `xgcd`, and `gcd` are generic
executables whose theorems all sit under `DensePoly.DivModLaws` and
`DensePoly.GcdLaws`, and `HexBerlekamp/Factor.lean:187` hardcodes the
`ZMod64` instances. Prerequisite 2 supplies the generic instances; this
stage rewrites hex-berlekamp's proofs to take them as instance
arguments.

Acceptance: no `ZMod64`-specific instance is named anywhere in
`HexBerlekamp/` outside the specialisation wrappers.

### 1c. Certificates and the tactic: prime-field only, for now

**This SPEC does not generalise the certificate or the tactic**, and an
earlier draft that proposed adding one field to
`IrreducibilityCertificate` badly understated the work.
`Berlekamp.IrreducibilityCertificate` stores `Array (FpPoly p)` and an
array of `RabinBezoutWitness p` whose own fields are `FpPoly p`
(`HexBerlekamp/Irreducibility.lean:101`), and
`FactorPolyElab.lean:43` hardcodes the reified cover entry as
`FpPoly p × ZMod64 p × IrreducibilityCertificate`. Generalising that is
a new certificate type, a new reifier, and a new replay path.

So the scope decision, stated once and honoured everywhere below:

- **Over `F_p`**, everything is as it is today: `factor_poly` and
  `irreducibility` produce `FpPoly.Factored` with `factors_irred`,
  backed by Rabin certificate replay.
- **Over a general `F_q`**, this library supplies a *runtime*
  factorization API and no theorem-producing elaborator. The product
  identity is checkable; per-factor irreducibility is not, because
  there is no generic certificate to replay.

A generic irreducibility certificate is a follow-on item with its own
SPEC. It is not in scope here, and `FpPoly.Factored`'s `factors_irred`
field is precisely why: a product-only check cannot construct that
structure.

hex-conway's committed table stores 36 certificates
(35 in `HexConway/Certificates.lean`, `cert_2_1` in
`HexConway/Table.lean:279`) and is untouched by this decision, since it
is entirely prime-field.

### 1d. Square-free decomposition

Prerequisite 4. Not part of this amendment, and not a consequence of
it.

## Amendment 2: the equal-degree stage

### The pipeline

The factorizer becomes four stages instead of two.

```
f  ──squarefree──▶  (fᵢ, i)  ──DDF──▶  (f_{i,d}, d)  ──EDF──▶  irreducibles
                                              │
                                              └── if card K is small:
                                                  Berlekamp kernel + sweep
```

1. **Square-free decomposition**, which hex-poly-fp already has as
   `FpPoly.squareFreeDecomposition` (`HexPolyFp/SquareFree.lean:40`),
   generalised along with everything else. Its output is
   multiplicity-tagged square-free pieces.
2. **Distinct-degree factorization**, already present as
   `distinctDegreeFactor`, generalised to `q`. Its output is
   `DegreeBucket` values, each recording a product of irreducibles of
   one known degree.
3. **Equal-degree factorization** of each bucket, which is new.
4. **Certificate emission**, unchanged in shape.

The gain is not asymptotic in the parameter that dominates today. It is
that stage 3's cost is independent of `q`, where the sweep's is linear
in it, and that stages 1 and 2 make stage 3's input a polynomial all of
whose factors have the same known degree, which is what makes a
one-in-two split probability available at all.

**A bucket with `deg f_{i,d} = d` is already irreducible** and skips
stage 3 entirely. This is where most of the win on ordinary inputs
comes from: DDF alone finishes the job whenever the factor degrees are
distinct, which is the common case, and the current factorizer pays a
`p`-wide sweep per witness to learn the same thing.

### `Hex.Berlekamp.equalDegreeSplit`

```lean
namespace Hex.Berlekamp

/-- What a failed split has to report so the caller can resume. -/
structure SplitFailure where
  attempts : Nat
  rand     : Rand

/-- Split a monic square-free `f`, all of whose irreducible factors
have degree exactly `d`, into two proper factors. A failure is fuel
exhaustion, never a claim that `f` is irreducible: the caller
establishes `d < DensePoly.degree f` before calling. -/
def equalDegreeSplit (f : DensePoly K) (hmonic : DensePoly.Monic f)
    (d : Nat) (r : Rand) (fuel : Nat) :
    Except SplitFailure (DensePoly K × DensePoly K × Rand)

/-- Fully split a bucket into its irreducible factors. -/
def equalDegreeFactor (f : DensePoly K) (hmonic : DensePoly.Monic f)
    (d : Nat) (r : Rand) (fuel : Nat) :
    Except SplitFailure (List (DensePoly K) × Rand)
```

`Except`, not `Option`. An earlier draft returned
`Option (result × Rand)`, which hands back the advanced generator only
on success and therefore cannot support the prose promise that a
failure is reported with its seed and attempt count so the caller can
resume from where it stopped.

`d` is an explicit argument and is **not** inferred. Calling with the
wrong `d` is the caller's obligation, discharged by DDF having produced
the bucket, and **the product identity does not catch a wrong `d`**: a
split obtained under the wrong `d` can still multiply back to `f`
exactly, and a wrong `d` need not exhaust fuel either, since it may
produce a valid split by accident. What catches it is checking each
returned leaf has degree `d`, which `equalDegreeFactor` does before
returning. An earlier draft claimed the product check sufficed and
required a conformance case asserting fuel exhaustion on a wrong `d`;
both are removed.

### Cantor-Zassenhaus, odd characteristic

For `q` odd. Draw `a ∈ F_q[x]/(f)` uniformly, `deg a < deg f`.

```
g ← gcd(f, a)                        -- a lucky non-unit split, cheap
if 1 < deg g < deg f then split
b ← a^((q^d − 1)/2) mod f
g ← gcd(f, b − 1)
if 1 < deg g < deg f then split
otherwise retry with the next draw
```

The powering is the cost: exponent `(q^d − 1)/2` has `d · log q` bits,
so one attempt is `d log q` modular squarings at `O(n²)` each, `n` the
degree of the bucket.

Why it works, stated because this is where an implementation and an
earlier draft of this SPEC both go wrong. Write `f = ∏_{j<r} f_j` with
each `f_j` irreducible of degree `d`, and `Q = q^d`. By CRT,
`F_q[x]/(f) ≅ ∏_j F_Q`, and `a` is a uniform independent element of
each coordinate. In `F_Q` with `Q` odd, `x^{(Q−1)/2}` is `0` at `x = 0`
and `±1` otherwise, taking each sign on exactly half the nonzero
elements.

The subset of coordinates where `b − 1` vanishes is **not**
unconditionally uniform, because a coordinate with `a = 0` gives
`b = 0`, not `b = ±1`. The earlier draft asserted uniformity and drew
the bound from it. The first `gcd(f, a)` step is what handles those
coordinates -- it is not an optimisation and must not be dropped -- and
conditioning on all coordinates being nonzero gives the exact
per-attempt failure probability

```
Q^{-r} + 2^{1-r} (1 - Q^{-1})^r  ≤  2^{1-r}
```

so the `2^{1−r}` bound survives, by a different argument than the one
that was written down.

### Cantor-Zassenhaus, characteristic two

For `q = 2^m`, `(q^d − 1)/2` is not an integer and the odd-characteristic
step is unavailable. The replacement is the absolute trace
`T : F_{q^d} → F_2`,

```
T(a) = a + a² + a⁴ + ⋯ + a^{2^{dm−1}}
g ← gcd(f, T(a) mod f)
```

`T` is `F_2`-linear and surjective onto `F_2`, so it takes each value
on exactly half of `F_{q^d}`, and the same coordinate argument gives
the same `2^{1−r}` failure bound.

**How to compute it.** Squaring is `F_2`-linear, not `K`-linear, so
there is no `Matrix K` implementing it and an earlier draft's "`dm − 1`
applications of the squaring Frobenius matrix" is not an available
algorithm. Two routes are:

- `dm − 1` squarings and additions directly in `F_q[x]/(f)`, at
  `O(d m n²)`; or
- trace transitivity,
  `Tr_{F_{q^d}/F_2} = Tr_{K/F_2} ∘ Tr_{F_{q^d}/K}`, computing the
  relative trace `a + a^q + ⋯ + a^{q^{d−1}}` with `d − 1` applications
  of the `q`-Frobenius matrix (which does exist), then applying the
  coefficient-field absolute trace elementwise.

The second is specified, because it costs `d` matrix-vector products
rather than `dm` quotient squarings and it reuses the matrix the
distinct-degree stage already built.

Dispatch is on `FiniteFieldOps.char K = 2`, decided once at the top of
`equalDegreeSplit?`. The two branches share the draw, the gcd, the
retry loop, and the fuel accounting, and differ only in the map applied
to `a`. They are one function with two arms, not two functions.

The trace arm generalises to any `char = p` as
`T(a) = a + a^q + a^{q²} + ⋯ + a^{q^{d−1}}` (the `F_q`-trace), followed
by `gcd(f, T(a) − c)` swept over `c ∈ F_p`. That is a `p`-wide sweep
again, so it is worth having only for `p = 2` where the sweep is one
value. The SPEC specifies the `p = 2` case and records the general
form here so the next reader does not rediscover it and mistake it for
an improvement.

### Totality, and what a failure means

`equalDegreeFactor` returns `Except`, and the failure propagates to the
generic public entry point:

```lean
def factor (f : DensePoly K) (hmonic : DensePoly.Monic f)
    (r : Rand) (fuel : Nat) :
    Except SplitFailure (Factorization K × Rand)
```

This is the third remedy design principle 8 names: propagate the
failure upward until the public API takes responsibility for it. No
total form of `equalDegreeSplit` is introduced, and none should be.

The existing total `berlekampFactor : FpPoly p → Factorization p` stays
exactly as it is, and stays total. On a prime field the sweep is a
complete deterministic algorithm, so nothing is lost. The generic entry
point can fail because over a large extension field there is no
practical deterministic fallback: deterministic polynomial-time
factorization over `F_q` for large `q` is open without GRH, and a
`card K`-wide sweep at `q = 2^{64}` is not a fallback.

**Fuel is per attempted split**, and the union bound follows from that
rather than being asserted. A bucket with `r` irreducible factors needs
`r − 1` successful splits; each split gets `fuel` attempts; each
attempt fails with probability at most `2^{-1}`. So a bucket fails with
probability at most `(r − 1) · 2^{-fuel}`, and an input whose buckets
have `r_1, …, r_t` factors fails with probability at most
`(Σ (r_i − 1)) · 2^{-fuel} ≤ deg f · 2^{-fuel}`. An earlier draft said
`2^{-fuel}` flat and did not say what fuel was measured per; both are
fixed. `fuel = 40` puts the bound below `2^{-30}` for any input this
tree will see, and the default is stated in terms of that bound rather
than picked.

### Certificates

Nothing new is needed **over `F_p`**, which is worth stating explicitly
because it is the reason the prime-field half of this item is cheap. A
factorization is certified by the product identity plus one Rabin
certificate per distinct factor, exactly as hex-berlekamp emits today.
The randomised search sits entirely outside that: `equalDegreeSplit`
proposes two factors, the product check accepts them, and no property
of the draw, the fuel, or the seed enters any proof term.

**Over a general `F_q` there is no certificate**, per the scope
decision in Amendment 1c. The generic API returns a decomposition whose
product identity is checkable and whose factors are irreducible because
the algorithm is correct, not because anything replays. Callers that
need a proof use the prime-field path.

Two additions on the prime-field path:

- EDF output carries the bucket degree `d`, and the pipeline checks
  `DensePoly.degree g = d` for each returned factor. This is what
  catches a wrong `d`, as set out above, and it is cheap where the
  irreducibility replay is not.
- The `Factored` structure and the `factor_poly` term-level contract
  (`scalar`, `factors`, `factors_mul`, `factors_irred`) are unchanged.

## Complexity

Counting field operations, with setup and per-step costs separated
because an earlier draft of this SPEC conflated them. `n` is the degree
of the input, `q = card K`, `r` the number of irreducible factors of a
bucket, `d` a bucket degree, `m = deg K`.

**Setup, once per input.**

| stage | cost |
|---|---|
| `frobeniusXMod` (`powModMonic X f q`) | `O(n² log q)` |
| `frobeniusMatrix` from it | `O(n³)` |

**Per step.**

| stage | cost | note |
|---|---|---|
| square-free, per Yun level | `O(n²)` | unchanged |
| DDF, per degree | `O(n²)` | one matrix-vector product plus one gcd |
| DDF, all degrees | `O(n³)` | at most `n/2` steps |
| Berlekamp kernel | `O(n³)` | row reduction of `Q - I` |
| constant sweep, per witness | `O(q n²)` | **the term this item removes** |
| CZ attempt, odd `q` | `O(d n² log q)` | one modular powering |
| CZ attempt, `q = 2^m` | `O(d n²)` + one absolute trace | `d` matrix-vector products |

**Totals.** Splitting one bucket of `r` factors costs `r − 1` splits at
an expected two attempts each. Factoring one input is setup plus DDF
plus the sum over buckets.

Three things the table is careful about, each because the earlier
version was not:

- **The matrix route is asymptotically better, not equal.** Horner
  modular composition costs `O(n³)` *per composition*, so driving DDF
  with it is `O(n⁴)` against the matrix's `O(n³)` setup plus `O(n³)`
  total stepping.
- **`log q = m · log p`**, so a degree-64 extension of `F_2` carries a
  factor of 64 into every modular powering. That is exactly the regime
  where the characteristic-two trace arm, which does no powering at
  all, is the one that runs.
- **The characteristic-two row counts `q`-Frobenius applications**, not
  quotient squarings, per the trace-transitivity implementation above.

## Kernel exposure
## Kernel exposure

The kernel replay closure is unchanged: `DensePoly.beqCoeffs`, the
product check, and `Berlekamp.checkMonicCert` / `checkIrredCover`. It
stays prime-field only, per Amendment 1c, so the existing budget guard
`deg · p ≤ 2^{26}` (`HexBerlekamp/TacticCore.lean:156`) is unchanged
too.

An earlier draft proposed replacing `p` with `card K` and claimed that
"therefore refuses every extension field". It does not: `F_4` and `F_8`
pass a cost bound comfortably. The guard is a cost limit and nothing
else, and the restriction to coefficient-field degree one is a separate,
explicit check with its own error message.

Nothing in `equalDegreeSplit?`, `Rand`, `frobeniusMatrix`, or the DDF
loop is in the closure, and none of it should be `@[expose]`.

`FiniteFieldOps.ofIndex` and `toIndex` are `@[expose]`, because the
guarded constant sweep reaches them on the prime-field path that
already replays in the kernel.

## Conformance

Per [SPEC/testing.md](../testing.md). The generic algorithms live in
hex-berlekamp, so its existing driver and fixture file extend rather
than a new tuple being added:
`conformance/HexBerlekamp/EmitFixtures.lean` gains fixture kinds, and
`scripts/oracle/berlekamp_flint.py` gains the matching arms. A new
tuple is appended to `ORACLES` in `scripts/ci/run_oracles.sh` only for
`HexFiniteField` itself:

```
"HexFiniteField|hexfinitefield_emit_fixtures|scripts/oracle/finitefield_flint.py|conformance-fixtures/HexFiniteField/finitefield.jsonl"
```

Fixture kinds: `ffops` (cardinality, index round trip, Frobenius on
sampled elements), `frobmat` (the Frobenius matrix of a given modulus),
and, in hex-berlekamp, `edf` (bucket, degree, factor list).

Cases that must be present, chosen because each catches a specific way
this can be wrong:

- **`p`-power versus `q`-power Frobenius.** A polynomial over
  `F_{p^2}` whose factorization differs from the answer the `p`-power
  Berlekamp matrix would give. This is the one silent failure mode of
  Amendment 1, and the fixture exists to catch it.
- **A bucket that is already irreducible** (`deg f = d`), which must
  not enter `equalDegreeSplit?` at all.
- **A bucket with `r = 2`**, the worst case for the split probability.
- **A bucket with `r` large** and `d = 1`, so the answer is a full
  linear factorization.
- **Characteristic two** at `m = 1` (so `q = 2` and the trace is over
  `F_2` directly) and at `m > 1`, since the trace length is `dm` and an
  implementation that uses `d` passes the first and fails the second.
- **`q = 3` and `q = 5`**, small odd `q`, where `(q^d − 1)/2` is small
  and an off-by-one in the exponent is visible.
- **A wrong `d`**, supplied deliberately, checking the leaf-degree
  validation rejects it. Not a fuel-exhaustion case: a wrong `d` may
  produce a valid-looking split, and the product identity does not
  notice.
- **Seed reproducibility**: the same seed gives the same factor list in
  the same order, on every platform.
- **Prime-field agreement**: for every existing hex-berlekamp fixture,
  the generic path at `deg K = 1` returns the same factor multiset as
  `berlekampFactor`. Checked in Lean, not against the oracle, since
  both sides are ours.

**Oracle choice.** FLINT's `fq_default_poly_factor` covers factoring
over `F_q` for both prime and extension fields, and
`fq_default_poly_factor_equal_deg` covers the equal-degree stage
directly, so the EDF surface has a like-for-like oracle rather than an
end-to-end one. `nmod_poly_factor_distinct_deg`, already wired for
`runDistinctDegreeChecksum`, covers the DDF stage. Factor lists are
compared as multisets after monic normalisation, since neither side
promises an order that the other shares.

**An end-to-end fixture cannot catch a broken EDF.** If
`equalDegreeSplit?` never succeeds, the pipeline falls through to the
sweep on a small field and returns the right answer. So the suite needs
route-level tests in Lean asserting that EDF produced the split, that
the sweep did not run, and that the attempt count was within the
expected range for the seed. This is the same split
[hex-mv-gcd](hex-mv-gcd.md) makes between route-level tests and oracle
fixtures, and for the same reason.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers extending
`bench/HexBerlekamp/Bench.lean` and a new `bench/HexFiniteField/Bench.lean`.
Native only; the kernel path is certificate replay, which
hex-berlekamp's existing suite measures.

Families:

- **Prime-field regression**, the existing `runBerlekampFactorChecksum`
  inputs through the new pipeline. The required property is that the
  restructuring does not make the `p ≤ 500` case slower. This is the
  family that decides whether the sweep threshold is set correctly, and
  a regression here blocks the change regardless of how good the
  extension-field numbers are.
- **Sweep crossover**, one input family swept over `q` from `3` to the
  largest prime the `ZMod64` bounds allow, timing the sweep path and
  the EDF path separately on the same inputs. The output is the
  measured threshold, which is then committed as the guard constant.
- **Extension-field factoring**, `F_{p^m}` for `m` from `2` to the
  largest committed Conway degree, and `F_{2^m}` through hex-gf2's
  packed representation for `m` up to `64`. There is no prior art in
  this tree to regress against; the comparator is FLINT.
- **DDF-only inputs**, where all factor degrees are distinct so EDF
  never runs. Measures the pipeline's overhead on the common case.
- **Equal-degree stress**, `r` copies of degree-`d` irreducibles for
  `r` from `2` to `32`, which is the family where the `2^{1−r}` bound
  is exercised and where a wrong retry policy shows up as variance
  rather than as a wrong answer.
- **Characteristic two**, the trace arm, at `m = 1, 8, 32, 64`.

**Comparators.** FLINT `fq_default_poly_factor` via python-flint,
**gating** on the extension-field family: it is the same operation with
the same algorithm class, and there is no structural reason for a gap.
FLINT `nmod_poly_factor` remains gating on the prime-field family as it
is today. FLINT `fq_default_poly_factor_equal_deg` is **informational**
on the equal-degree family: it is the same algorithm, but FLINT selects
between Cantor-Zassenhaus and Kaltofen-Shoup by a tuned crossover this
SPEC does not specify, so a required ratio would be a check on an
algorithm that is not implemented here.

No advance ratio is claimed on the characteristic-two family: hex-gf2's
packed representation and FLINT's `fq_zech` are different
representations of the same field, and which wins is the measurement.

## The Mathlib layer

`hex-finite-field-mathlib` is small and its job is to say that the
interface means what its name says.

```lean
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
  [FiniteFieldOps K] [LawfulFiniteField K]

instance : Fintype K
theorem card_eq : Fintype.card K = Hex.card K
theorem charP : CharP K (FiniteFieldOps.char K)
theorem frob_eq_frobenius : FiniteFieldOps.frob = frobenius K (FiniteFieldOps.char K)
```

`Fintype K` follows from `ofIndex` / `toIndex` being mutually inverse
on `[0, card)`, which is why those are laws rather than conveniences:
without them the class describes a field with a `Nat` attached and
proves nothing. `charP` is a transport of the `Lean.Grind.IsCharP`
that `LawfulFiniteField` now extends, not a consequence of the other
fields.

**The concrete transports do not live here.** hex-gfq-mathlib is above
hex-gfq (`libraries.yml`), and the generic companion is below both and
must stay there, so the `GFq`/`GaloisField` transport cannot be in
`hex-finite-field-mathlib`. The split is: generic finiteness,
cardinality, and characteristic statements here; the `ZMod64 p ≃+* ZMod p`
transport already in hex-mod-arith-mathlib; the `FiniteField` and `GFq`
transports in hex-gfq-mathlib, which already promises
`Fintype (FiniteField p f hf hirr)` and `card = p ^ f.degree`. An
earlier draft put all of them here and would have inverted the graph.

The factoring correctness statements stay in
**hex-berlekamp-mathlib**, generalised the same way the executable
layer is: `irreducible_of_mem_berlekampFactor` and `rabin_irreducible`
over `Polynomial K` for `K` a Mathlib `Field` with `Fintype`, rather
than over `Polynomial (ZMod p)`. Mathlib's `Polynomial.roots`,
`Polynomial.expand`, and the `ZMod p`-specific arguments in the current
proofs are the places that will resist; the general statements
Mathlib supports are `FiniteField.pow_card`, `FiniteField.card`, and
`Polynomial.card_nthRoots`, which is what the generic proof should be
built from.

**The equal-degree stage needs no new Mathlib-side theorem.** It
returns a decomposition that the existing product check and existing
per-factor irreducibility certificate certify. The `2^{1−r}` probability
bound is a statement about the running time and appears in no proof
term, which is the point of the Las Vegas design and the reason it is
cheap here.

## Milestones

The prerequisites come first, and they are most of the work. Numbering
them as milestones rather than listing them as assumptions is the main
correction this SPEC made after review.

0. **Prerequisites.** The quotient-representation bridge for
   `pow_card`; Mathlib-free `DivModLaws` / `GcdLaws` from
   `Lean.Grind.Field`; `Hex.Rand` in hex-basic with rejection sampling;
   the hex-poly relocation of `powModMonic` and `composeModMonic`, each
   with its kernel-facing name, runtime twin, and `@[csimp]` equality
   restated after the move.

1. **The interface and the prime-field instance.** `FiniteFieldOps`,
   `LawfulFiniteField` (extending `IsCharP`), and the `ZMod64 p`
   instance with `pow_card` from `Hex.Nat.pow_prime_mod`. Complete when
   the instance typechecks with no `sorry`.

2. **The extension-field instance**, on top of milestone 0's bridge.

3. **The generic quotient layer.** `frobeniusXMod` as
   `powModMonic X f (card K)`, `frobeniusMatrix`, `frobeniusApply`, and
   the `frob = id` prime-field fast path, with the `ffops` and
   `frobmat` conformance fixtures.

4. **Amendment 1a and 1b.** hex-berlekamp generalised in executables
   and then in proofs, `FpPoly p` entry points preserved. The
   prime-field regression benchmark family decides whether this lands:
   it does so only if the existing numbers hold.

5. **Amendment 2, odd characteristic.** `equalDegreeSplit`,
   `equalDegreeFactor`, the four-stage pipeline, the guarded sweep, and
   the measured threshold.

6. **Generic square-free decomposition** (prerequisite 4), including
   the inverse-Frobenius coefficient `p`-th root. Needed before the
   generic pipeline is complete on inputs with repeated factors.

7. **The packed `GF(2^n)` tower** (prerequisite 5): `DecidableEq`,
   `Lean.Grind.Field`, and `Lean.Grind.IsCharP` for `GF2n`, then the
   instance. `GF2q` inherits it as an abbreviation; any explicit
   `GF2q` API stays in hex-gfq.

8. **Amendment 2, characteristic two.** The trace arm, via trace
   transitivity, on top of milestone 7.

9. **The companion.** `Fintype`, `card_eq`, `charP`, and the
   generalisation of hex-berlekamp-mathlib's correctness theorems.
   Begins after milestone 1 and runs in parallel with 3 onward.

A generic irreducibility certificate and a generic `factor_poly` are
**not** on this list; see Amendment 1c.

## File organisation

```
HexFiniteField/
  Ops.lean          -- FiniteFieldOps, LawfulFiniteField, card
  Prime.lean        -- the ZMod64 p instance and pow_card
  Frobenius.lean    -- frobeniusXMod, frobeniusMatrix, frobeniusApply
HexFiniteField.lean
HexFiniteFieldMathlib/
  Card.lean         -- Fintype, card_eq, charP, frob_eq_frobenius
HexFiniteFieldMathlib.lean
```

New files in existing libraries:

```
HexBasic/Rand.lean                  -- splitmix64
HexGFqField/FiniteFieldOps.lean     -- the extension-field instance
HexGF2/FiniteFieldOps.lean          -- the packed GF(2^n) instance
HexBerlekamp/EqualDegree.lean       -- equalDegreeSplit?, equalDegreeFactor?
HexBerlekamp/Pipeline.lean          -- the four-stage dispatch
```

Relocations: `powModMonicAux`, `powModMonic`, `powModMonicLinear`,
`composeModMonic`, `composeModMonicImpl` from `HexPolyFp/Frobenius.lean`
and `HexPolyFp/ModCompose.lean` into `HexPoly/Euclid/DivGcd.lean`'s
neighbourhood, with `FpPoly` abbreviations left behind.

`libraries.yml` gains:

```yaml
  HexFiniteField:
    deps: [HexArith, HexModArith, HexPoly, HexPolyFp, HexMatrix, HexBasic]
    mathlib: false
    done_through: 0
    status: draft
  HexFiniteFieldMathlib:
    deps: [HexFiniteField, HexModArithMathlib, HexPolyMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

and the following existing entries gain a dependency: `HexBerlekamp`
on `HexFiniteField`, `HexGFqField` on `HexFiniteField`, `HexGF2` on
`HexFiniteField`.

`HexGF2` currently depends on `[HexPoly, HexBasic]`, so adding
`HexFiniteField` puts it above hex-mod-arith and hex-poly-fp, which it
does not use today. If that is unwelcome, the alternative is to leave
the packed instance out of hex-gf2 and site it in a small library above
both; the SPEC takes the direct route and records the alternative here.

`scripts/check_dag.py` reads every Lean file a library owns, including
its conformance and bench drivers, so these edges are checked against
the whole tree rather than against production sources only. That is why
`HexGFqField` already declares a dependency on `HexBerlekamp` it does
not import in `HexGFqField/`.

## Open questions

- **Whether `deg` belongs in `FiniteFieldOps` or is derived.** It is
  needed to compute `card` and to size the trace, and no operation
  produces it, so it is a field. If a future instance has a cheap
  cardinality but an awkward degree (a Zech-logarithm representation,
  say), `card` becomes the field and `deg` the derived quantity. Nothing
  above depends on which way round it is.
- **Whether `frobeniusMatrix` or modular composition should drive DDF.**
  The matrix costs `O(n³)` once and `O(n²)` per step; Horner composition
  costs `O(n³)` per step; Brent-Kung would cost less than either and
  does not exist. The default above is the matrix. The DDF-only
  benchmark family settles it, and the answer may differ between the
  prime-field and extension-field cases.
- **The sweep threshold.** Guarded at a measured constant. The
  measurement is the "sweep crossover" family; until it is taken, the
  guard is `card K ≤ 64`, chosen to be safely below any plausible
  crossover rather than to be right.
- **Whether the trace arm should cover odd characteristic.** The
  `F_q`-trace plus a `p`-wide sweep is a third algorithm that beats the
  powering arm when `p` is tiny and `d log q` is large. It is a small
  addition to a function that already exists and it is not specified
  above, because no input family in the benchmark set is in that regime.
- **Whether `Rand` should be `Nat`-backed rather than `UInt64`-backed.**
  Nothing here needs more than 64 bits of state. [hex-mv-gcd](hex-mv-gcd.md)
  draws points in `ZMod64 p`, so it does not either. A future consumer
  that wants random integers of unbounded size would want a different
  generator, and that is the point at which to revisit it.
- **Whether the `IrreducibilityCertificate` change should carry a
  version tag.** [future-work](../future-work.md)'s "Certificate
  serialization and caching" entry proposes an envelope with a schema
  version, and this is the first change that would break a stored
  certificate. Adding the field without a version is a one-off cost;
  adding the envelope is the cross-cutting project that entry
  describes. This SPEC takes the one-off cost and flags the coincidence.
