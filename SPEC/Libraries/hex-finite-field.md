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

Three source-level constraints refine that entry.

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

The executable factorizer is accompanied by generic product, monicity,
and irreducibility theorems.  These are ordinary correctness theorems
about the Mathlib-free algorithm; they are distinct from the reflected
certificates used by `factor_poly`.  The reflected certificate and tactic
remain prime-field-only.

Not in scope: normal bases, Zech logarithms, `fq_zech`-style
small-field representations, field extension towers (that is
hex-number-field-tower's subject over `ℚ`, and has no `F_q` analogue in
this tree yet), discrete logarithms, and reimplementing the packed `GF(2^n)` path,
which stays in hex-gf2 with its own optimised arithmetic and receives
an instance rather than a reimplementation.

## Prerequisites

Five things have to exist before the interface can be stated, let alone
instantiated. Each was found by checking the source rather than the
SPECs, and each is a real development rather than a relocation. They are
listed here because the existing executable components do not yet
compose at their proof and representation boundaries.

1. **A quotient-representation bridge for `pow_card`**, as set out
   above. Without it the extension-field instance has no proof.

2. **Generic polynomial field algebra.** `DensePoly.DivModLaws` and
   `DensePoly.GcdLaws` have to be available Mathlib-free from
   `[Lean.Grind.Field K] [DecidableEq K]`. The
   executable `divMod`, `modByMonic`, `xgcd`, and `gcd` are generic in
   their operation lists, but every theorem about them is stated under
   these two law classes, and the Mathlib-free instances are for
   `ZMod64 p` (`HexPolyFp/Field.lean:710`, `:824`) and `Rat`
   (`HexPolyZ/Rational.lean:1196`, `:1269`) only. The one generic
   instance, `instDivModLawsField` / `instGcdLawsField`
   (`HexPolyMathlib/Euclid.lean:190`, `:252`), is on the Mathlib side
   and requires a Mathlib `Field`. So a Mathlib-free
   `[Lean.Grind.Field K] [DecidableEq K] → DivModLaws K` and the
   matching `GcdLaws K` are prerequisites, in hex-poly. The same
   milestone moves the algebraic definition of irreducibility from the
   `FpPoly` namespace to a generic `DensePoly.Irreducible` (leaving the
   old name as an abbreviation), and generalises
   `FpPoly.normalizeMonic` and `FpPoly.monicGcd` to `DensePoly`.  The
   generic executable predicate
   `DensePoly.SquareFree f := DensePoly.monicGcd f f.derivative = 1`
   (with the existing nonzero/nonconstant conventions made explicit)
   lives beside them. Over an arbitrary field, hex-poly proves only the
   unconditional direction from this gcd criterion to absence of a
   repeated irreducible divisor. The converse is false over imperfect
   fields: over `F_2(t)`, `X²-t` is irreducible but has zero derivative.
   Hex-finite-field proves the converse under `LawfulFiniteField`, using
   finiteness/perfectness from `pow_card`. The
   following laws are required, not optional conveniences: reconstruction
   by the extracted leading coefficient, monicity and nonzeroness of the
   normalised polynomial for nonzero input, divisibility equivalence up to
   a unit, and monicity of `monicGcd` when the gcd is nonzero. Until they
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
   over `F_q` is the inverse Frobenius `x ↦ x^(q/p)`. The generic
   quotient layer derives this as `frobInv` by iterating the class's
   coefficient Frobenius. Generalising Yun is still its own milestone, not a
   consequence of generalising the factorizer. It lives in
   `HexBerlekamp/SquareFree.lean`, above both hex-poly-fp and
   hex-finite-field. It cannot stay in hex-poly-fp: making that library
   import hex-finite-field would form a cycle because hex-finite-field
   already imports hex-poly-fp.

5. **The binary-field algebraic towers.** `GF2n`
   (`HexGF2/Field.lean`) has the arithmetic operations and
   `mul_inv_cancel`, but no `DecidableEq`, no `Lean.Grind.Field`, and
   no `Lean.Grind.IsCharP`. It cannot satisfy the generic context until
   those exist. Moreover, `GF2n` is defined only under `n < 64`; it
   cannot represent degree 64. Both binary representations therefore
   receive the missing field/characteristic tower and a finite-field
   instance (`GF2nPoly` already has `DecidableEq`):
   `GF2n` for `n < 64`, and `GF2nPoly` for arbitrary positive modulus
   degree. Benchmarks at degree 64 use `GF2nPoly`, never `GF2n` or
   `GF2q`. These instances are a milestone with their own acceptance
   criteria, not lines in a table.

None of these is a reason not to do the item. All five are reasons the
item is larger than one library plus two amendments, and the milestone
list at the end reflects them.

## The interface

Two classes, split the way [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) splits `GcdOps`
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
    [FiniteFieldOps K] : Prop where
  /-- Kept as data, not a global parent instance: `IsCharP`'s
  characteristic parameter is an `outParam`. Consumers install this
  projection as a local instance. -/
  isCharP     : Lean.Grind.IsCharP K (FiniteFieldOps.char K)
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

`LawfulFiniteField` **carries** `Lean.Grind.IsCharP K
(FiniteFieldOps.char K)`, but does not extend it. `IsCharP` declares its
characteristic parameter as an `outParam`; an inherited global instance
could compete with the concrete `ZMod64` and `GFqField` instances and
select a non-definitionally-equal instance family. Modules that use the
freshman's dream install `LawfulFiniteField.isCharP` locally. Leaving
the fact out entirely would also be wrong: `(a + b)^p = a^p + b^p`
is what makes every Frobenius argument below work. Both concrete types
already have the fact (`HexGFqField/Operations.lean:1117` for the
extension case), so carrying it as data costs nothing while keeping
instance search stable.

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

The weaker propagation lemma
`pow_pPowN_eq_self_of_pow_pPowN_X_eq_X`
(`HexPolyFp/QuotientFrobenius.lean:381`), which only pushes the
hypothesis `X^(p^n) = X` out to every element and does not derive it
from irreducibility, does not discharge the instance. The stronger
theorem exists, but neither theorem applies directly to the target
representation.

The prerequisite is therefore one of three, and the choice should be
made before milestone 1 starts:

1. a ring isomorphism
   `GFqRing.PolyQuotient f hf ≃+* FpPoly.Quotient (toMonic f) _ _`
   with `pow_card` transported along it, which is the smallest change
   and the one this SPEC assumes. Its proof includes
   `degree (toMonic f) = degree f` so the exponents agree and transports
   irreducibility using the existing scalar-normalisation theorem; a
   bare type equivalence is insufficient because it need not preserve
   powers;
2. a direct Mathlib-free cardinality argument for
   `GFqRing.PolyQuotient`, duplicating the existing proof; or
3. changing `FiniteField` to use the already-proved quotient type,
   which is a representation change in an `active`, `done_through: 7`
   library.

Option 1 is a real development -- the two quotient types have different
reduction functions and different canonical-form invariants -- and it is
listed explicitly in the prerequisites.

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

`frob = id` on the prime field makes the coefficient `p`-th-root
operation below free. It does **not** accelerate `X^p mod f`: that is a
quotient computation and still uses square-and-multiply. The class
stores coefficient Frobenius because generic square-free decomposition
uses its inverse and because the Mathlib companion identifies it with
Mathlib's Frobenius, not as a hidden quotient fast path.

`GF2n` from hex-gf2 gets an instance too, with `frob` the squaring
map, `char = 2`, and `ofIndex` the packed word; `GF2q n` is an
abbreviation declared in hex-gfq (`HexGFq/Basic.lean:800`) and inherits
it when `n < 64`. `GF2nPoly` gets the same interface with polynomial
bit indexing and covers arbitrary positive degrees, including 64.
Prerequisite 5 is what those instances wait on. Those instances are
the reason the class is stated over an abstract `K` rather than
being a structure of functions on `FpPoly`: hex-gf2's representation is
a packed `UInt64` vector, not a coefficient array, and the whole point
is that the factoring algorithms should run over it unchanged. It goes
in `hex-gf2` rather than here, so that hex-finite-field does not
acquire a dependency on hex-gf2.

**Where each instance lives.** The class lives here. The `ZMod64 p`
instance lives here (this library depends on hex-mod-arith). The
`FiniteField` instance lives in **hex-gfq-field**, and the `GF2n`
and `GF2nPoly` instances in **hex-gf2**, each next to its type. Splitting class from
instance across libraries is what keeps the DAG acyclic and is
discussed under "Placement in the DAG".

The base-`p` encoder and decoder used by the `FiniteField` instance are
currently embedded in `HexGFqMathlib/Basic.lean` as part of its
`Fintype` construction. Their definitions move to a Mathlib-free
`HexGFqField/Index.lean`, but this is not a mechanical relocation: the
current inverse proofs use Mathlib's `Nat.ofDigits`, `Fin`, and
`Finset`. Milestone 2 reproves Mathlib-free versions of
`coeffIndex_lt`, `coeffIndex_ofIndexBelowDegree`, and
`ofIndexBelowDegree_coeffIndex`, plus the `reduceMod`-idempotence witness
needed by `GFqRing.PolyQuotient`'s canonical-representative subtype. The
companion then reuses this codec rather than maintaining a second
enumeration.

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

Extension-field integration tests cannot live in hex-finite-field or
hex-berlekamp: the `FiniteFieldOps (GFqField.FiniteField ...)` instance
lives in hex-gfq-field, while hex-gfq-field's conformance and bench
surface already depends on hex-berlekamp to construct Rabin witnesses.
Such a test below both libraries would create a cycle. End-to-end tests
using the concrete extension and packed binary instances therefore live
in **hex-gfq**, which is already above hex-gfq-field, hex-gf2, and
hex-berlekamp. Hex-berlekamp tests exercise the generic algorithms with
the prime-field instance and locally defined small test fields only.

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

This is a relocation, not a generalisation of an algorithm. It is the
quotient-arithmetic part of hex-poly's milestone-0 work; the generic
law instances, irreducibility/square-free predicates, and monic
normalisation listed in prerequisite 2 are additional changes.

### The `q`-power Frobenius

```lean
namespace Hex.FiniteField

variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
  [FiniteFieldOps K] [LawfulFiniteField K]

local instance : Lean.Grind.IsCharP K (FiniteFieldOps.char K) :=
  LawfulFiniteField.isCharP

/-- Inverse coefficient Frobenius, obtained by iterating `frob`
`deg K - 1` times. -/
def frobInv (x : K) : K

theorem frobInv_pow_char (x : K) :
    frobInv x ^ FiniteFieldOps.char K = x

/-- `X^q mod f`, by square-and-multiply on the exponent `card K`. -/
def frobeniusXMod (f : DensePoly K) (hmonic : DensePoly.Monic f) : DensePoly K

/-- The matrix of `h ↦ h^q mod f` in the basis `1, X, …, X^{n-1}`,
built from `frobeniusXMod` by `n` modular multiplications. -/
def frobeniusMatrix (f : DensePoly K) (hmonic : DensePoly.Monic f) :
    Matrix K (f.degree?.getD 0) (f.degree?.getD 0)

/-- Apply a Frobenius matrix to a representative that fits its basis. -/
def frobeniusApply (Q : Matrix K n n) (h : DensePoly K)
    (hsize : h.size ≤ n) : DensePoly K

theorem frobeniusApply_matrix
    (f : DensePoly K) (hmonic : DensePoly.Monic f)
    (h : DensePoly K) (hsize : h.size ≤ f.degree?.getD 0) :
    frobeniusApply (frobeniusMatrix f hmonic) h hsize =
      DensePoly.powModMonic h f hmonic (card K)
```

`frobInv` is the coefficient `p`-th root required when Yun reaches a
zero derivative. Its proof uses `frob_eq_pow`, `pow_card`, and
`deg_pos`; at `deg K = 1` it is the identity. It is an operation derived
from the class, not another class field.

`DensePoly` has `degree?`, not a total `degree`; all displayed APIs in
this SPEC use `degree?.getD 0` (or `size`) accordingly. The size
hypothesis on `frobeniusApply` is essential: without it the matrix drops
high coefficients and the advertised correctness statement is false.

**Only the `q`-power map is `K`-linear, and this is the place to be
careful.** On `K[x]/(f)` the map `x ↦ x^q` satisfies
`(a+b)^q = a^q + b^q` in characteristic `p` and `(c·a)^q = c^q a^q = c a^q`
for `c ∈ K`, the second step using `pow_card` on the coefficient field.
So it is `K`-linear, it has a matrix over `K`, and iterating it is one
matrix-vector product at `O(n²)`.

The `p`-power map is **not** `K`-linear when `deg K > 1`: it is
`p`-semilinear, `(c·a)^p = c^p a^p`, and `c^p ≠ c` in general. It has no
matrix over `K`. The characteristic-two trace is likewise `F_2`-linear
rather than `K`-linear.
`FiniteFieldOps.frob` is a coefficientwise operation, and any algorithm
that wants the `p`-power map on the quotient has to compose it with a
modular composition, never with a `Matrix K`.

**The specified v1 algorithm.** `frobeniusXMod` is
`powModMonic X f hmonic (card K)`, costing
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

A matrix is tied to one modulus and one basis dimension. The matrix
built for a square-free parent during DDF is therefore not passed to
EDF for a proper bucket, and an EDF matrix for a bucket is not reused
after that bucket is split into smaller moduli. Any characteristic-two
split node builds the matrix for its own current modulus once and reuses
it only across the random attempts at that node. Restricting a parent
matrix to a factor could be an optimisation, but no such restriction
map or correctness theorem exists in v1.

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

inductive RandError where
  | zeroBound
  | exhausted (attempts : Nat) (rand : Rand)

/-- Form a candidate from enough 64-bit words and use rejection
sampling. `fuel` bounds rejection retries, including the initial
candidate. -/
def Rand.nat (r : Rand) (bound fuel : Nat) :
    Except RandError (Nat × Rand)
def Rand.ofSeed (seed : Nat) : Rand
```

Sampling a field element binds
`Rand.nat r (card K) sampleFuel` and applies
`FiniteFieldOps.ofIndex` to the successful bounded index; sampling a polynomial of degree below `n` is
`n` successive element draws. Each draw is bounded by `card K`; no
algorithm samples one integer below `card K ^ n`. Rejection sampling
forms a candidate from `⌈log₂ bound / 64⌉` words and rejects the
incomplete top interval, avoiding the additional modulo bias of
`next % bound`. `bound = 0` returns `zeroBound`. Rejection is not hidden
inside an allegedly total recursive definition: exhaustion returns the
advanced state in `RandError.exhausted`, and all callers propagate it.

This concrete function is **not specified as mathematically uniform or
independent**. A deterministic generator with only 64 bits of state has
at most `2^64` possible streams and cannot induce a uniform draw on an
arbitrary larger `Nat` bound; successive values are deterministic once
the seed is fixed. Its contract is instead executable and testable:
range correctness, deterministic replay, explicit state advancement,
no modulo reduction of an incomplete interval, and bounded termination.
The Cantor-Zassenhaus probability analysis below is carried out against
a separate ideal model of independent uniform coefficient draws. It
motivates the retry budget but is not a theorem about splitmix64.

`Rand` belongs in **hex-basic**, not here. It has no dependencies, and
it has a second consumer already specified: [hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md)
route 4 draws random evaluation points for Zippel's interpolation, and
says so. Two consumers in different subtrees is the argument for a root
library.

The discipline, which this item sets rather than follows:

- Every randomised function takes `Rand` as an explicit argument and
  returns the advanced state. No monad, no `IO`, no global generator.
- `factorWithRand` is the composable public entry point. A convenience
  `factor` wrapper accepts `seed : Nat := 0` and constructs the initial
  state, so the documented default exists in the API rather than only
  in prose.
- Randomness affects **how long** a Las Vegas algorithm runs, never
  **what** it returns. Every randomised result passes the same checker
  the deterministic path would.
- Fuel is explicit and finite. Fuel exhaustion is a documented
  outcome, reported in the return type, never as a wrong answer and
  never as a nonterminating loop.
- **Probability statements are about the ideal sampler, not about
  splitmix64.** Every bound below (`2^{1-r}` per attempt, and the union
  bounds derived from it) explicitly assumes independent uniform field
  coefficients. No theorem transfers those bounds to the concrete PRNG.

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
   it is the small-`q` path alongside DDF/EDF. Keeping both dispatch
   routes in one library avoids duplicating factor-list assembly and
   proof infrastructure.

What goes where is therefore: the interface, the instances, the generic
Frobenius, and `Rand` are new; the algorithms are hex-berlekamp
amendments. The rest of this SPEC specifies those amendments.

## Amendment 1: generalising hex-berlekamp

The generalisation splits into four stages with separate acceptance criteria, because they
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

The public executable result type is generalised at the same time:

```lean
structure Factorization (K : Type u) where
  input   : DensePoly K
  factors : List (DensePoly K)
```

The existing `Factorization p`, which is indexed by a characteristic
`Nat`, is not reused with `K` in place of `p`; that expression is
ill-typed today. Existing prime-field callers migrate to
`Factorization (ZMod64 p)`, with a compatibility abbreviation if source
compatibility warrants it.

Four places need more than a substitution.

- **`berlekampColumn`** builds columns from `FpPoly.frobeniusXMod`,
  which becomes `FiniteField.frobeniusXMod`. Over an extension field the
  unchanged construction computes the `K`-linear substitution
  `h(X) ↦ h(X^p)`, not the quotient Frobenius `h ↦ h^q`. It still has
  a matrix over `K`, so the mistake typechecks, but `Q-I` has the wrong
  nullspace. This differs from the genuinely `p`-semilinear map
  discussed below. The extension conformance case pins the matrix as
  well as the final factor multiset so this silent error cannot be
  masked downstream.
- **`kernelWitnessSplit?`'s constant sweep** is bounded by the literal
  `p` in `cachedSplitAux f witness reduced p 0`
  (`HexBerlekamp/Factor.lean:308`). Generically it is `card K`, and it
  is guarded: the sweep runs only below a measured threshold and is
  otherwise skipped in favour of EDF.
- **Rabin's test** holds with `q` for `p` throughout and `n` the degree
  over `F_q`.
- **Every gcd entering a factor list or a DDF bucket is normalised.**
  `DensePoly.gcd` is deliberately unnormalised (`gcd X (2*X) = 2*X`
  over `F_3`), so raw gcd output cannot supply the `Monic` hypotheses
  needed by recursive EDF. DDF and both Cantor-Zassenhaus arms use the
  generic `DensePoly.monicGcd`; the complementary quotient is
  normalised as well, and the unit is reconciled using the
  reconstruction theorem. Buckets, work-list entries, and final factors
  are monic by construction.

Acceptance: the generic code compiles, compatibility wrappers preserve
the old `FpPoly` behaviour, every stored nonconstant factor is monic,
and the existing conformance fixtures pass unchanged. The wrappers need
not be definitionally identical after mandatory monic normalisation;
factor multisets and the existing public theorem contracts are the
compatibility criterion.

### 1b. Proof genericization

The blocker. `divMod`, `modByMonic`, `xgcd`, and `gcd` are generic
executables whose theorems all sit under `DensePoly.DivModLaws` and
`DensePoly.GcdLaws`, and `HexBerlekamp/Factor.lean:187` hardcodes the
`ZMod64` instances. Prerequisite 2 supplies the generic instances; this
stage rewrites hex-berlekamp's proofs to take them as instance
arguments.

Acceptance: no `ZMod64`-specific instance is named anywhere in
`HexBerlekamp/` outside the specialisation wrappers.

This stage proves the generic algebraic lemmas needed by DDF and the
later split proofs, including monic-gcd divisibility and quotient
reconstruction. The EDF and full-pipeline theorem names are introduced
with the executable definitions in milestones 5 and 6 rather than
being promised before their statements exist.

### 1c. Certificates and the tactic: prime-field only, for now

**This SPEC does not generalise the certificate or the tactic.** Doing
so is not a one-field change to `IrreducibilityCertificate`:
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
- **Over a general `F_q`**, this library supplies a runtime
  factorization API and generic correctness theorems, but no
  theorem-producing elaborator. A caller can use the theorems in an
  ordinary Lean proof. There is no reflected certificate/reifier that
  turns a computed extension-field factorization into a compact kernel
  term automatically.

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
   generalised in `HexBerlekamp/SquareFree.lean`. Its output is
   multiplicity-tagged square-free pieces.
2. **Distinct-degree factorization**, already present as
   `distinctDegreeFactor`, generalised to `q`. Its output is
   `DegreeBucket` values, each recording a product of irreducibles of
   one known degree.
3. **Equal-degree factorization** of each bucket, which is new.
4. **Result assembly and correctness**, expanding multiplicities and
   proving the product and irreducibility contracts. Prime-field tactic
   certificate emission remains unchanged in shape.

The pipeline-facing DDF result contains only valid buckets and proves
that their product is its monic square-free input. The current bounded
`DistinctDegreeFactorization` exposes a separate `residual`; in the
generic pipeline, a non-unit residual left after the `d ≤ n/2` loop is
normalised and appended as the final bucket with its remaining degree,
with the standard theorem that it is irreducible. A compatibility view
may continue exposing `residual`, but the pipeline may not silently drop
it or pass it to EDF without a `DegreeBucket.Valid` proof.
Accordingly, the proof-bearing DDF entry point takes both
`DensePoly.Monic f` and `DensePoly.SquareFree f`; an unchecked
compatibility view may retain the old monic-only signature but cannot
export `distinctDegreeFactor_valid`.

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

/-- One monic DDF bucket. -/
structure DegreeBucket (K : Type u) where
  degree : Nat
  factor : DensePoly K

/-- The semantic contract established by DDF: the bucket is nontrivial,
monic and square-free, and every irreducible divisor has exactly the
recorded degree. -/
def DegreeBucket.Valid (b : DegreeBucket K) : Prop :=
  0 < b.degree ∧
  DensePoly.Monic b.factor ∧
  DensePoly.SquareFree b.factor ∧
  (∃ r, 0 < r ∧ b.factor.degree? = some (r * b.degree)) ∧
  ∀ g, DensePoly.Irreducible g → g ∣ b.factor →
    g.degree? = some b.degree

/-- A bounded sampler or split-search failure. The caller still knows
the bucket it supplied; this value records diagnostics and the next
stream state, not a hidden recursive checkpoint. -/
inductive SplitFailure where
  | random (error : RandError)
  | exhausted (attempts : Nat) (rand : Rand)

/-- A successful split, including the erased proof payload needed by
recursive EDF. -/
structure DegreeSplit (parent : DegreeBucket K) where
  left right : DensePoly K
  product     : left * right = parent.factor
  leftValid   : ({ degree := parent.degree, factor := left } : DegreeBucket K).Valid
  rightValid  : ({ degree := parent.degree, factor := right } : DegreeBucket K).Valid
  left_lt     : left.degree?.getD 0 < parent.factor.degree?.getD 0
  right_lt    : right.degree?.getD 0 < parent.factor.degree?.getD 0

/-- Split a valid bucket whose factor has degree greater than the bucket
degree into two proper monic factors. -/
def equalDegreeSplit (b : DegreeBucket K) (hvalid : b.Valid)
    (hsplit : b.degree < b.factor.degree?.getD 0)
    (r : Rand) (fuel sampleFuel : Nat) :
    Except SplitFailure (DegreeSplit b × Rand)

/-- Fully split a bucket into its irreducible factors. -/
def equalDegreeFactor (b : DegreeBucket K) (hvalid : b.Valid)
    (r : Rand) (fuel sampleFuel : Nat) :
    Except SplitFailure (List (DensePoly K) × Rand)
```

`Except`, not `Option`. Failures preserve the advanced generator state
for diagnostics or a new retry, but do not claim to contain the
recursive factor work-list. Exact replay restarts from the original
seed; continuation from an internal recursive checkpoint is not part of
this API.

The degree is explicit in `DegreeBucket`, but it is not accepted without
its proof. Calling a bare `(f, d)` pair is unsound: for
`f = (X-a)(X-b)`, supplying `d = 2` makes the degree-based early exit
return the reducible `f`, and checking that the returned leaf has degree
`d` does not detect the mistake. Degree `d` implies irreducibility only
under `DegreeBucket.Valid`. DDF therefore exports
`distinctDegreeFactor_valid`, and the pipeline passes that theorem into
EDF. There is no public unchecked entry point and no conformance test
claiming arbitrary wrong degrees can be detected at runtime.

`equalDegreeFactor` checks the leaf degree as a defensive executable
invariant, but its irreducibility theorem relies on `hvalid`, not on the
check alone. Recursive calls use `DegreeSplit.leftValid` and
`rightValid`; termination is by `b.factor.degree?.getD 0`, decreasing
through `left_lt` and `right_lt`. The early exit is taken only after the
validity proof is available.

Milestone 5 exports `split_product`, `split_proper`,
`split_valid_left`, `split_valid_right`,
`equalDegreeFactor_product`, `equalDegreeFactor_monic`, and
`equalDegreeFactor_irreducible`. The exact statements quantify over a
successful `Except.ok` result and `DegreeBucket.Valid`; the properness
and inherited-validity facts are required to elaborate the recursive
definition, not merely post-hoc documentation. Milestone 6 adds
`factor_product`, `factor_monic`, and `factor_irreducible` for the full
pipeline.

### Cantor-Zassenhaus, odd characteristic

For `q` odd. The executable sampler draws the next reproducible
`a ∈ F_q[x]/(f)`, `deg a < deg f`; the analysis below models `a` as
uniform, as specified in the ideal sampler contract.

```
g ← gcd(f, a)                        -- a lucky non-unit split, cheap
if 0 < deg g < deg f then split
b ← a^((q^d − 1)/2) mod f
g ← gcd(f, b − 1)
if 0 < deg g < deg f then split
otherwise retry with the next draw
```

Both tests mean "non-unit proper divisor" and agree with the existing
`isNontrivialSplitFactor`: a degree-one gcd is a valid split and must
not be rejected. This is essential for every `d = 1` bucket.

The powering is the cost: exponent `(q^d − 1)/2` has `d · log q` bits,
so one attempt is `d log q` modular squarings at `O(n²)` each, `n` the
degree of the bucket.

Why it works: write `f = ∏_{j<r} f_j` with
each `f_j` irreducible of degree `d`, and `Q = q^d`. By CRT,
`F_q[x]/(f) ≅ ∏_j F_Q`, and `a` is a uniform independent element of
each coordinate **under the ideal sampler model**. In `F_Q` with `Q`
odd, `x^{(Q−1)/2}` is `0` at `x = 0`
and `±1` otherwise, taking each sign on exactly half the nonzero
elements.

The subset of coordinates where `b − 1` vanishes is **not**
unconditionally uniform, because a coordinate with `a = 0` gives
`b = 0`, not `b = ±1`. The first `gcd(f, a)` step handles those
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
there is no `Matrix K` implementing it. Two routes are:

- `dm − 1` squarings and additions directly in `F_q[x]/(f)`, at
  `O(d m n²)`; or
- trace transitivity,
  `Tr_{F_{q^d}/F_2} = Tr_{K/F_2} ∘ Tr_{F_{q^d}/K}`, computing the
  relative trace `a + a^q + ⋯ + a^{q^{d−1}}` with `d − 1` applications
  of the `q`-Frobenius matrix for the **current bucket modulus**, then
  computing `t + t² + ⋯ + t^{2^{m-1}}` by `m − 1` squarings in
  that same quotient.

The second is specified. It costs one matrix construction per split
node, `d − 1` matrix-vector products per attempt, and `m − 1`
quotient squarings per attempt. The matrix is reused across attempts at
that node, but is neither the DDF parent matrix nor reusable by child
factors.

Applying `Tr_{K/F_2}` **coefficientwise is forbidden**. A quotient
element fixed componentwise by the `q`-Frobenius need not be represented
by a polynomial whose coefficients can be traced independently. For
example, with `K = F_4`, `ω²+ω+1=0`,
`f = X(X+ω)`, and `a=X`, the relative trace for `d=1` is `X`, while
the coefficientwise trace sends it to zero because
`Tr_{K/F_2}(1)=0`; the correct quotient absolute trace is
`X+X² mod f = ω²X`. The quotient squarings in the specified
algorithm are therefore mathematically necessary.

Dispatch is on `FiniteFieldOps.char K = 2`, decided once at the top of
`equalDegreeSplit`. The two branches share the draw, the gcd, the
retry loop, and the fuel accounting, and differ only in the map applied
to `a`. They are one function with two arms, not two functions.

The trace arm generalises to any `char = p` as
`T(a) = a + a^q + a^{q²} + ⋯ + a^{q^{d−1}}` (the `F_q`-trace), followed
by `gcd(f, T(a) − c)` swept over `c ∈ F_p`. That is a `p`-wide sweep
again, so it is worth having only for `p = 2` where the sweep is one
value. The SPEC specifies the `p = 2` case and records the general
form here as an explicitly deferred variant.

### Totality, and what a failure means

`equalDegreeFactor` returns `Except`, and both sampler and split
exhaustion propagate to the generic public entry point:

```lean
def factorWithRand (f : DensePoly K) (hmonic : DensePoly.Monic f)
    (r : Rand) (fuel sampleFuel : Nat) :
    Except SplitFailure (Factorization K × Rand)

def factor (f : DensePoly K) (hmonic : DensePoly.Monic f)
    (seed : Nat := 0) (fuel : Nat := 40)
    (sampleFuel : Nat := 128) :
    Except SplitFailure (Factorization K)
```

This is the third remedy design principle 8 names: propagate the
failure upward until the public API takes responsibility for it. No
total form of `equalDegreeSplit` is introduced, and none should be.

The existing total `berlekampFactor` remains as a compatibility wrapper
returning `Factorization (ZMod64 p)`, and stays total. It first runs the
guarded pipeline; if that returns `SplitFailure`, it runs the existing
complete, unguarded prime-field sweep. This single fallback site is
classified as `audited-emergency-value` under design principle 8: the
fallback is deterministic and mathematically complete, its product is
checked before return, its correctness theorem is retained, and the
prime-field tactic still replays irreducibility certificates. No other
caller converts `SplitFailure` to a value. The prime-field regression
benchmarks this public wrapper, including cases on both sides of the
sweep threshold.

The generic entry
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
`(Σ (r_i − 1)) · 2^{-fuel} ≤ deg f · 2^{-fuel}`. `fuel = 40`
puts the ideal-model bound at or below `2^{-30}`
for input degree at most `2^10`. Callers requiring the same bound at
larger degree choose `fuel ≥ 30 + ⌈log₂ (deg f)⌉`; the API exposes
the parameter rather than claiming 40 is universally sufficient.

`sampleFuel` is a separate engineering bound for the concrete
rejection sampler. It does not enter the ideal Cantor-Zassenhaus
probability bound. A failure returns the advanced generator and can be
retried for the same known split input. `equalDegreeFactor` does not
claim to preserve a hidden recursive checkpoint: retrying its public
call restarts the work-list, either from the original seed for exact
replay or from the returned state for a different deterministic run.

### Certificates

Nothing new is needed **over `F_p`**, which is worth stating explicitly
because it is the reason the prime-field half of this item is cheap. A
factorization is certified by the product identity plus one Rabin
certificate per distinct factor, exactly as hex-berlekamp emits today.
The randomised search sits entirely outside that: `equalDegreeSplit`
proposes two factors, the product check accepts them, and no property
of the draw, the fuel, or the seed enters any proof term.

**Over a general `F_q` there is no reflected certificate**, per the
scope decision in Amendment 1c. There are nevertheless generic Lean
correctness theorems. For a successful `factorWithRand` result they
prove the stored product equals the monic input and every stored factor
is monic and `DensePoly.Irreducible`. The proof composes the generic
square-free, DDF-validity, split-product, and valid-bucket leaf theorems;
it does not appeal to the sentence "the algorithm is correct" as an
unstated assumption. Callers that want automatic compact kernel replay
use the prime-field tactic path.

Two additions on the prime-field path:

- EDF output carries the bucket degree `d`, and the pipeline checks
  `g.degree? = some d` for each returned factor as a defensive
  invariant. The proof that this makes the leaf irreducible uses
  `DegreeBucket.Valid`; the check is not advertised as validating an
  arbitrary caller-supplied `d`.
- The `Factored` structure and the `factor_poly` term-level contract
  (`scalar`, `factors`, `factors_mul`, `factors_irred`) are unchanged.

## Complexity

Counting field operations, with setup and per-step costs separated.
`n` is the degree
of the input, `q = card K`, `r` the number of irreducible factors of a
bucket, `d` a bucket degree, `m = deg K`.

**DDF setup, once per square-free component.** If the input is already
square-free this is once; repeated-factor inputs may have several
component moduli.

| stage | cost |
|---|---|
| `frobeniusXMod` (`powModMonic X f q`) | `O(n² log q)` |
| `frobeniusMatrix` from it | `O(n³)` |

**Per step.**

| stage | cost | note |
|---|---|---|
| square-free, ordinary Yun level | `O(n²)` | derivative/gcd/division |
| square-free, zero-derivative root | `O(n m C_frob)` | `frobInv` on at most `n` coefficients; `C_frob` is one coefficient Frobenius |
| DDF, per degree | `O(n²)` | one matrix-vector product plus one gcd |
| DDF, all degrees | `O(n³)` | at most `n/2` steps |
| Berlekamp kernel | `O(n³)` | row reduction of `Q - I` |
| constant sweep, per witness | `O(q n²)` | **the term this item removes** |
| CZ attempt, odd `q` | `O(d n² log q)` | one modular powering |
| binary CZ setup, per split node | `O(n³)` | matrix for that node's modulus |
| CZ attempt, `q = 2^m` | `O((d + m)n²)` | `d` matrix-vector products plus `m` quotient squarings |

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
- **The characteristic-two row counts both operations required by trace
  transitivity**: `q`-Frobenius applications for the relative trace and
  quotient squarings for the absolute trace. It also charges a fresh
  matrix setup after every successful split because the modulus changes.

## Kernel exposure

The kernel replay closure is unchanged: `DensePoly.beqCoeffs`, the
product check, and `Berlekamp.checkMonicCert` / `checkIrredCover`. It
stays prime-field only, per Amendment 1c, so the existing budget guard
`deg · p ≤ 2^{26}` (`HexBerlekamp/TacticCore.lean:156`) is unchanged
too.

The tactic remains statically specialised to `FpPoly p`, so extension
fields never reach this guard and `p` is not replaced by `card K`.
There is consequently no new runtime "coefficient degree one" check to
specify. A future generic tactic would need both a representation check
and a separately measured cost guard; neither is inferred from this
SPEC.

Nothing in `equalDegreeSplit`, `Rand`, `frobeniusMatrix`, or the DDF
loop is in the closure, and none of it should be `@[expose]`.

`FiniteFieldOps.ofIndex` and `toIndex` are runtime enumeration
operations and are not marked `@[expose]` merely for this project. The
prime-field kernel replay keeps using its existing direct `ZMod64`
constant construction; the random sampler and generic enumeration do
not enter the replay closure. Any future generic tactic must specify and
measure a new closure before changing these annotations.

## Conformance

Per [SPEC/testing.md](../testing.md). The generic algorithms live in
hex-berlekamp, so its existing prime-field driver and fixture file
extend rather than a new tuple being added:
`conformance/HexBerlekamp/EmitFixtures.lean` gains fixture kinds, and
`scripts/oracle/berlekamp_flint.py` gains the matching arms. A new
tuple is appended to `ORACLES` in `scripts/ci/run_oracles.sh` only for
`HexFiniteField` itself:

```
"HexFiniteField|hexfinitefield_emit_fixtures|scripts/oracle/polyfp_flint.py|conformance-fixtures/HexFiniteField/finitefield.jsonl"
```

HexFiniteField can instantiate only `ZMod64 p`, so the tuple uses the
existing `scripts/oracle/polyfp_flint.py`, not an `fq_default` driver.
The extension-field arms live in hex-gfq's existing tuple and reuse
`gfq_flint.py` / the persistent `fq_default` codec. There is no second
finite-field encoding implementation.

Fixture kinds: `ffops` (cardinality, index round trip, Frobenius on
sampled elements), `frobmat` (the Frobenius matrix of a given modulus),
and, in hex-berlekamp, `edf` (a DDF-produced valid bucket and factor
list). Concrete extension-field end-to-end fixtures and route tests are
added to hex-gfq's existing conformance driver, the first existing
library above the instance libraries and hex-berlekamp.

Cases that must be present, chosen because each catches a specific way
this can be wrong:

- **`p`-power versus `q`-power Frobenius (HexGFq).** A polynomial over
  `F_{p^2}` whose factorization differs from the answer the `p`-power
  Berlekamp matrix would give. This is the one silent failure mode of
  Amendment 1, and the fixture exists to catch it.
- **A bucket that is already irreducible (HexBerlekamp and HexGFq)**
  (`deg f = d`), which must
  not enter `equalDegreeSplit` at all.
- **A bucket with `r = 2` (HexBerlekamp and HexGFq)**, the worst case
  for the split probability.
- **A bucket with `r` large (HexBerlekamp and HexGFq)** and `d = 1`, so the answer is a full
  linear factorization.
- **Characteristic two**, with `m = 1` in HexBerlekamp and `m > 1` in
  HexGFq. The latter includes the concrete
  `F_4`, `f=X(X+ω)`, `a=X` regression: coefficientwise base-field
  trace returns zero while quotient-level absolute trace returns a
  nonzero split.
- **`q = 3` and `q = 5` (HexBerlekamp)**, small odd `q`, where `(q^d − 1)/2` is small
  and an off-by-one in the exponent is visible.
- **The proof-bearing bucket boundary (HexBerlekamp).** Tests construct EDF inputs only
  through DDF and exercise `distinctDegreeFactor_valid`. There is no
  runtime "wrong `d` is rejected" test, because no such complete
  validation is possible from leaf degree and product checks.
- **Seed reproducibility (HexBerlekamp and HexGFq)**: the same seed gives the same factor list in
  the same order, on every platform.
- **Prime-field agreement (HexBerlekamp)**: for every existing hex-berlekamp fixture,
  the generic path at `deg K = 1` returns the same factor multiset as
  `berlekampFactor`. Checked in Lean, not against the oracle, since
  both sides are ours.
- **Fallback audit (HexBerlekamp)**: above the sweep threshold with
  zero split fuel, `factorWithRand` returns `SplitFailure` while the
  total `berlekampFactor` wrapper takes its sole audited exhaustive-sweep
  fallback, passes the product check, and returns the certified factor
  multiset.

**Oracle choice.** FLINT's `fq_default_poly_factor` covers factoring
over `F_q` for both prime and extension fields. The direct
`fq_default_poly_factor_equal_deg` C entry point covers EDF, but
python-flint exposes full and square-free factorisation rather than this
route-level function. The existing persistent oracle subprocess gains a
small C binding (or equivalent compiled helper) for the direct EDF call;
the SPEC does not pretend a Python method already exists. The binding
enforces FLINT's preconditions that the input be monic, nonconstant, and
square-free. `nmod_poly_factor_distinct_deg`, already wired for
`runDistinctDegreeChecksum`, covers the DDF stage. Factor lists are
compared as multisets after monic normalisation, since neither side
promises an order that the other shares.

**An end-to-end fixture cannot catch a broken EDF.** If
the dispatcher selects the sweep on a small field, EDF is never called
and the pipeline returns the right answer even if EDF is broken. So the suite needs
route-level tests in Lean (in hex-berlekamp for prime fields and
hex-gfq for concrete extensions) asserting that EDF produced the split, that
the sweep did not run, and that the attempt count was within the
expected range for the seed. This is the same split
[hex-mv-gcd](../../HexMvGcd/SPEC/hex-mv-gcd.md) makes between route-level tests and oracle
fixtures, and for the same reason.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md). Prime-field and generic
interface families extend `bench/HexBerlekamp/Bench.lean` and a new
`bench/HexFiniteField/Bench.lean`. Concrete extension-field and binary
families extend `bench/HexGFq/Bench.lean`, which is already above
hex-gfq-field, hex-gf2, and hex-berlekamp; placing them in either lower
driver would create the same cycle avoided by the conformance layout.
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
  largest prime below `2^16`, timing the sweep path and the EDF path
  separately on the same inputs. Exhaustively approaching the
  `ZMod64.Bounds` ceiling near `2^31` would itself require billions of
  sweep gcds and is not a benchmark. The crossover sweep runs on the
  scheduled dedicated-hardware workflow; merge-gating CI retains a
  small regression set around the committed threshold. The guard is
  selected from the measured window and conservatively extrapolated,
  then checked by those regression points.
- **Extension-field factoring**, `F_{p^m}` for `m` from `2` to the
  largest committed Conway degree, and `F_{2^m}` through hex-gf2's
  packed `GF2n` representation for `m ≤ 63`. Degree 64 and larger
  binary cases use `GF2nPoly`. There is no prior art in this tree to
  regress against; the comparator is FLINT.
- **DDF-only inputs**, where all factor degrees are distinct so EDF
  never runs. Measures the pipeline's overhead on the common case.
- **Equal-degree stress**, `r` copies of degree-`d` irreducibles for
  `r` from `2` to `32`, which is the family where the `2^{1−r}` bound
  is exercised and where a wrong retry policy shows up as variance
  rather than as a wrong answer.
- **Characteristic two**, the trace arm, at `m = 1, 8, 32, 63` through
  packed `GF2n`, and at `m = 64` through `GF2nPoly`.

The last two families are owned by `bench/HexGFq/Bench.lean`; neither
hex-finite-field nor hex-berlekamp imports the concrete instance
libraries for benchmarking.

**Comparators.** FLINT `fq_default_poly_factor` via python-flint,
**informational** on the extension-field family. FLINT's full factorizer
selects among tuned algorithms, including Kaltofen-Shoup regimes this
SPEC does not implement, and its representation differs from both Hex
extension representations; a gating ratio would not isolate this
project's algorithm. Correctness fixtures remain gating.
FLINT `nmod_poly_factor` remains gating on the prime-field family as it
is today. FLINT `fq_default_poly_factor_equal_deg` is **informational**
on the equal-degree family. The direct C function has the same semantic
operation, but its implementation and representation are not a stable
like-for-like performance contract.

No advance ratio is claimed on the characteristic-two family: hex-gf2's
packed representation and FLINT's `fq_zech` are different
representations of the same field, and which wins is the measurement.

## The Mathlib layer

`hex-finite-field-mathlib` is small and its job is to say that the
interface means what its name says.

```lean
variable {K : Type u} [Field K] [DecidableEq K]
  [FiniteFieldOps K] [LawfulFiniteField K]

instance (priority := 50) : Fintype K
theorem card_eq : Fintype.card K = Hex.card K
instance (priority := 50) charP : CharP K (FiniteFieldOps.char K)
theorem char_prime : Nat.Prime (FiniteFieldOps.char K)
local instance : Fact (Nat.Prime (FiniteFieldOps.char K)) := ⟨char_prime⟩
theorem frob_eq_frobenius : FiniteFieldOps.frob = frobenius K (FiniteFieldOps.char K)
```

These signatures require Mathlib's `Field K`. Mathlib installs
`Field.toGrindField` at priority 100; there is intentionally no reverse
instance from `Lean.Grind.Field` to `Field`, so the weaker context from
the Mathlib-free layer does not elaborate here. The characteristic
bridge is an instance before `frobenius` is mentioned, and the existing
`HexBerlekampMathlib.nat_prime_of_hex` proof is relocated to
hex-mod-arith-mathlib as the generic `Hex.Nat.Prime → Nat.Prime`
bridge (with a compatibility theorem left behind). Both companions
already need the modular-arithmetic correspondence layer, and this
keeps a fact about `Nat` out of either factoring or finite-field
namespaces. It supplies the local `Fact` used by Mathlib's
`ExpChar`/Frobenius API.

`Fintype K` follows from `ofIndex` / `toIndex` being mutually inverse
on `[0, card)`, which is why those are laws rather than conveniences:
without them the class describes a field with a `Nat` attached and
proves nothing. `charP` is a transport of the locally installed
`LawfulFiniteField.isCharP`, not a consequence of the other fields.

The generic `Fintype` and `CharP` instances have deliberately low priority. Current
`GFqField`/`GFq` and binary Mathlib companions already provide concrete
instances; when both are imported their specialised instances win,
avoiding an instance-choice regression while the concrete companions
are migrated to reuse the generic enumeration.

**The concrete transports do not live here.** hex-gfq-mathlib is above
hex-gfq (`libraries.yml`), and the generic companion is below both and
must stay there, so the `GFq`/`GaloisField` transport cannot be in
`hex-finite-field-mathlib`. The split is: generic finiteness,
cardinality, and characteristic statements here; the `ZMod64 p ≃+* ZMod p`
transport already in hex-mod-arith-mathlib; the `FiniteField` and `GFq`
transports in hex-gfq-mathlib, which already promises
`Fintype (FiniteField p f hf hirr)` and `card = p ^ f.degree`.

The Mathlib correspondence statements stay in
**hex-berlekamp-mathlib**, generalised the same way the executable
layer is: the DensePoly correctness theorems above are transported to
`Polynomial K`, alongside generic versions of
`irreducible_of_mem_berlekampFactor` and `rabin_irreducible`
over `Polynomial K` for `K` a Mathlib `Field` with `Fintype`, rather
than over `Polynomial (ZMod p)`. Mathlib's `Polynomial.roots`,
`Polynomial.expand`, and the `ZMod p`-specific arguments in the current
proofs are the places that will resist; the general statements
Mathlib supports are `FiniteField.pow_card`, `FiniteField.card`, and
`Polynomial.card_nthRoots`, which is what the generic proof should be
built from.

The equal-degree stage therefore does need named generic correspondence
theorems, even though it needs no probability theorem. The required
surface includes `equalDegreeFactor_product`,
`equalDegreeFactor_irreducible`, `factor_product`, and
`factor_irreducible` (or short namespace-equivalent names) for the
Mathlib `Polynomial` view. The `2^{1−r}` probability bound is a
running-time statement under the ideal sampler and appears in no proof
term.

## Milestones

The prerequisites come first, and they are most of the work.

0. **Prerequisites.** The quotient-representation bridge for
   `pow_card`; Mathlib-free `DivModLaws` / `GcdLaws`, generic
   `DensePoly.Irreducible` / `SquareFree`, and generic
   `normalizeMonic` / `monicGcd` with their laws (only the unconditional
   square-free-to-no-repeated-divisor direction is proved here); `Hex.Rand` in
   hex-basic with fuel-bounded rejection sampling and explicit errors;
   the hex-poly relocation of `powModMonic` and `composeModMonic`, each
   with its kernel-facing name, runtime twin, and `@[csimp]` equality
   restated after the move.

1. **The interface and the prime-field instance.** `FiniteFieldOps`,
   `LawfulFiniteField` (carrying `IsCharP` as a non-instance field), and the `ZMod64 p`
   instance with `pow_card` from `Hex.Nat.pow_prime_mod`. Complete when
   the instance typechecks with no `sorry`; proofs may rewrite
   `p ^ 1 = p` and are not required to close by `rfl`.

2. **The extension-field instance**, on top of milestone 0's bridge,
   including the Mathlib-free re-proof of the base-`p` index codec laws
   and quotient canonicality in `HexGFqField/Index.lean`.

3. **The generic quotient layer.** `frobeniusXMod` as
   `powModMonic X f (card K)`, `frobeniusMatrix`, `frobeniusApply`, and
   coefficient `frobInv`, with the `ffops` and
   `frobmat` conformance fixtures.

4. **Amendment 1a and 1b.** hex-berlekamp generalised in executables
   and then in proofs, including the generic `Factorization K`, monic
   DDF buckets, `DegreeBucket.Valid`, `distinctDegreeFactor_valid`, and
   the DDF correctness surface. The finite-field converse connecting
   the square-free gcd criterion to absence of repeated irreducible
   divisors is proved here under `LawfulFiniteField`. `FpPoly p` entry points are
   preserved. The
   prime-field regression benchmark family decides whether this lands:
   it does so only if the existing numbers hold.

5. **Amendment 2, odd characteristic on valid square-free buckets.**
   `equalDegreeSplit`, `equalDegreeFactor`, their product/monicity/
   irreducibility theorems, the guarded sweep, and the measured
   threshold. This milestone does not yet claim an arbitrary-input
   four-stage factorizer.

6. **Generic square-free decomposition** (prerequisite 4), including
   the inverse-Frobenius coefficient `p`-th root, followed by assembly
   of the full four-stage `factorWithRand` / `factor` pipeline and its
   product, monicity, and irreducibility theorems. This ordering makes
   the milestone's arbitrary-input claim true.

7. **The binary-field towers** (prerequisite 5): `DecidableEq` for
   `GF2n` (already present for `GF2nPoly`), and
   `Lean.Grind.Field` / `Lean.Grind.IsCharP` for both types, then both
   finite-field instances. `GF2q` inherits the
   packed instance only in its existing `n < 64` range; degree 64 uses
   `GF2nPoly`.

8. **Amendment 2, characteristic two.** The trace arm, via trace
   transitivity with quotient-level squarings, on top of milestone 7.
   Acceptance includes the `F_4` coefficientwise-trace counterexample
   and rebuilds the Frobenius matrix for each changed modulus.

9. **The companions, in dependency order.** The low-priority generic
   `Fintype`, `card_eq`, `CharP` instance, and Frobenius
   correspondence in hex-finite-field-mathlib may begin after milestone
   1; the generic `Hex.Nat.Prime → Nat.Prime` bridge moves first to
   hex-mod-arith-mathlib. The hex-berlekamp-mathlib product and irreducibility
   correspondence theorems begin only after the executable statements
   they mention exist (milestone 5 for EDF and milestone 6 for the full
   pipeline; milestone 8 for the binary trace arm).

A generic irreducibility certificate and a generic `factor_poly` are
**not** on this list; see Amendment 1c.

## File organisation

```
HexFiniteField/
  Ops.lean          -- FiniteFieldOps, LawfulFiniteField, card
  Prime.lean        -- the ZMod64 p instance and pow_card
  Frobenius.lean    -- frobInv, frobeniusXMod/matrix/apply
HexFiniteField.lean
HexFiniteFieldMathlib/
  Card.lean         -- Fintype, card_eq, charP, frob_eq_frobenius
HexFiniteFieldMathlib.lean
```

New files in existing libraries:

```
HexBasic/Rand.lean                  -- splitmix64
HexModArithMathlib/Prime.lean       -- Hex.Nat.Prime to Nat.Prime
HexGFqField/Index.lean              -- Mathlib-free base-p index codec
HexGFqField/FiniteFieldOps.lean     -- the extension-field instance
HexGF2/FiniteFieldOps.lean          -- GF2n and GF2nPoly instances
HexBerlekamp/SquareFree.lean        -- generic square-free decomposition
HexBerlekamp/EqualDegree.lean       -- equalDegreeSplit, equalDegreeFactor
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
    status: planned
  HexFiniteFieldMathlib:
    deps: [HexFiniteField, HexModArithMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`status: planned` records that the API contracts, correctness
obligations, dependency placement, failure semantics, and acceptance
tests are now closed. The measured sweep threshold is a milestone
output, not a design blocker.

The following existing entries gain a dependency: `HexBerlekamp`
on `HexFiniteField`, `HexGFqField` on `HexFiniteField`, `HexGF2` on
`HexFiniteField`, and `HexBerlekampMathlib` on
`HexFiniteFieldMathlib`. The latter edge is required by the generic
`CharP`, cardinality, and Frobenius correspondence used in its proofs.

`lakefile.lean` changes in the same milestone: it gains
`lean_lib HexFiniteField`, default target
`lean_lib HexFiniteFieldMathlib`, and
`lean_exe hexfinitefield_emit_fixtures` rooted at
`HexFiniteField.EmitFixtures`, plus `lean_exe hexfinitefield_bench`
rooted at `HexFiniteField.Bench`. These declarations are part of the DAG
acceptance check; updating only `libraries.yml` fails
`libgraph.check_lakefile_alignment`.

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

## Fixed v1 choices and deferred optimisations

- **`deg` stays in `FiniteFieldOps`.** It is
  needed to compute `card` and to size the trace, and no operation
  produces it, so it is a field. If a future instance has a cheap
  cardinality but an awkward degree (a Zech-logarithm representation,
  say), `card` becomes the field and `deg` the derived quantity. Nothing
  above depends on which way round it is.
- **`frobeniusMatrix` drives DDF in v1.**
  The matrix costs `O(n³)` once and `O(n²)` per step; Horner composition
  costs `O(n³)` per step; Brent-Kung would cost less than either and
  does not exist. The default above is the matrix. The DDF-only
  benchmark family settles it, and the answer may differ between the
  prime-field and extension-field cases.
- **The sweep threshold.** Guarded at a measured constant. The
  measurement is the "sweep crossover" family; until it is taken, the
  guard is `card K ≤ 64`, chosen to be safely below any plausible
  crossover rather than to be right.
- **The trace arm does not cover odd characteristic in v1.** The
  `F_q`-trace plus a `p`-wide sweep is a third algorithm that beats the
  powering arm when `p` is tiny and `d log q` is large. It is a small
  addition to a function that already exists and it is not specified
  above, because no input family in the benchmark set is in that regime.
- **`Rand` remains `UInt64`-state-backed.** Its contract is
  deterministic replay rather than exact uniformity. Consumers needing
  a distribution theorem or a larger state space must introduce a
  different generator and an explicit refinement theorem; they must not
  strengthen this class's claims retrospectively.
