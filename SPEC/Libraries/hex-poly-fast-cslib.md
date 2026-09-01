# hex-poly-fast-cslib (operation counts, depends on hex-poly-fast and cslib)

This planned library proves coefficient-operation bounds for the
operation-parametric multiplication workers specified by
[hex-poly-fast](../../HexPolyFast/SPEC/hex-poly-fast.md). It uses the query
complexity definitions from
[cslib](https://github.com/leanprover/cslib). `HexPolyFast` remains free of
Mathlib and cslib.

## Complexity-layer classification

The library will have classification `complexity_layer: true`.

- Computational conformance owner: `HexPolyFast`.
- Computational performance owner: `HexPolyFast`.

A complexity layer contains proofs and definitions used by those proofs. It
does not own executable polynomial operations, conformance targets, external
oracles, benchmark targets, or a performance report. Its library entry names
the computational owners whose tests and measurements cover the operations
under study. This classification is defined in
[benchmarking](../benchmarking.md#comparator-naming) and
[testing](../testing.md#where-cross-check-content-lives).

The specified results concern base-ring additions, subtractions, and
multiplications issued by the proof-facing workers. They do not estimate
elapsed time, allocation, machine instructions, or packed-word operations.

## Motivation

The complexity table in `HexPolyFast` constrains implementation structure and
benchmark behaviour. It does not itself prove an operation count. A proof is
useful for the Schönhage recursion because the bound depends on parameter
selection at every recursive level, including the amount of padding and the
balance between the transform length and the inner modulus length.

Output equality alone cannot support such a result. Every lawful `MulPlan`
returns schoolbook multiplication, regardless of its implementation. The
counted definitions must therefore expose the operations performed by the
specific worker being analysed. `HexPolyFast` supplies one worker body
parametric in its coefficient operations. The identity interpretation gives
the proof-facing definition. The free interpretation gives the program whose
queries this library counts.

The raw array definitions selected by `@[csimp]` are separate definitions.
Their current theorems prove output equality with the proof-facing
definitions. They do not prove equality of operation traces or costs. No bound
in this SPEC applies to those raw definitions. A later change could define
each raw runtime as an erasure of its worker and prove cost preservation, but
that is not required here.

## Dependency and pin policy

cslib depends on Mathlib, so this library will follow the build restrictions
for proof-only libraries that import Mathlib. It will have no
`precompileModules` setting and no benchmark or conformance target.
Computational libraries may not import it.

Until cslib PR
[#401](https://github.com/leanprover/cslib/pull/401) merges, development uses
commit `36e098cfc04fbb8e9b44086d64ce433514ee18d4`. The integration check replaced
cslib's Mathlib pin with hex-dev revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The
`Cslib.Algorithms.Lean.Query.*` modules required here built at that revision.
A build of the complete `Cslib` target did not succeed: unrelated
modules under `Cslib.Foundations.Data.OmegaSequence` and
`Cslib.Foundations.Combinatorics.InfiniteGraphRamsey` require
`Mathlib.Data.Set.Lattice.Bounded`, which is absent at the hex-dev revision.
This library therefore imports the query modules directly and never imports
the `Cslib` umbrella module.

Publication requires a merged cslib revision or a maintained revision with a
stable source. A commit from an unmerged pull-request branch is permitted for
monorepo development only.

## Query model

The counted program type is `Cslib.FreeM (ArithQuery R) α`. The query type is:

```lean
inductive ArithQuery (R : Type) : Type → Type where
  | add (a b : R) : ArithQuery R R
  | sub (a b : R) : ArithQuery R R
  | mul (a b : R) : ArithQuery R R
```

`ArithQuery.honest` returns the corresponding ring operation. The cost
function `ArithQuery.weight c_add c_mul` assigns `c_add` to addition and
subtraction and assigns `c_mul` to multiplication. This is the only weight
family used by the obliviousness and upper-bound theorems.

The free interpretation of `CoeffOps` is:

```lean
def freeOps : CoeffOps (FreeM (ArithQuery R)) R where
  add a b := FreeM.lift (.add a b)
  sub a b := FreeM.lift (.sub a b)
  mul a b := FreeM.lift (.mul a b)
```

The fixed-length triadic operations expand into queries over `R`. Carrier
addition and subtraction issue one query for each affected coefficient.
Multiplication by a power of `y` issues additions or subtractions according
to the triadic fold. A pointwise carrier product calls the same recursive
worker. Quotient-ring operations are not counted as primitive queries.

If the upstream arithmetic example changes before the dependency is updated,
this library may define an equivalent local query type. The public cost
statements retain separate addition and multiplication weights.

## Specialization

Each worker will have an interpretation theorem. The Karatsuba theorem has
the following required form, with the actual worker arguments retained in the
implemented statement:

```lean
theorem karatsubaWorker_eval (cutoff fuel : Nat) (a b : Array R) :
    (karatsubaWorker freeOps cutoff fuel a b).eval ArithQuery.honest =
      karatsubaWorker idOps cutoff fuel a b
```

There is an analogous theorem for `schoenhageWorker` with the counted
Karatsuba base. The proof interprets each `FreeM.lift` by the corresponding
identity operation and follows the worker recursion. These theorems identify
the result of the free program under the honest oracle with the proof-facing
worker. They make no statement about a raw `@[csimp]` replacement.

## Cost obliviousness

Queries contain their operands. An arbitrary oracle can change an operand
used by a later query, so query values and complete query traces need not be
oracle-independent. The required property concerns only the
constructor-determined weight:

```lean
def CostOblivious (p : FreeM (ArithQuery R) α)
    (c_add c_mul : Nat) : Prop :=
  ∀ o₁ o₂,
    p.cost o₁ (ArithQuery.weight c_add c_mul) =
      p.cost o₂ (ArithQuery.weight c_add c_mul)
```

The Karatsuba program and the Schönhage program with that counted Karatsuba
base must satisfy `CostOblivious` for every pair of natural weights. Their
branches may depend on array lengths, cutoffs, and schedule data. They must not
depend on coefficient values or oracle answers. Fixed-length triadic values
are necessary for this statement because trimming an intermediate value would
introduce coefficient-dependent branches.

No theorem claims obliviousness for an arbitrary function on `ArithQuery`.
Such a function could inspect the operands stored in a query.

## Bounds

cslib's `UpperBound` counts queries with unit weight. This library also needs
a weighted form:

```lean
def WeightedBound {T : Type} [AddMonoid T] [LE T]
    (prog : α → FreeM Q β) (size : α → Nat)
    (weight : {ι : Type} → Q ι → T) (bound : Nat → T) : Prop :=
  ∀ (oracle : {ι : Type} → Q ι → ι) (n : Nat) (x : α),
    size x ≤ n → (prog x).cost oracle weight ≤ bound n
```

The implemented statements may use a pair of natural numbers to record
addition and multiplication counts before applying
`ArithQuery.weight c_add c_mul`. Either formulation must imply the weighted
inequalities below for all natural `c_add` and `c_mul`.

### Karatsuba

The first result covers the proof-facing dispatcher, including its balanced,
blocked, and unbalanced paths. If `m ≥ n > 0` and the cutoff is `c`, its cost
is bounded by

```text
ceil(m / n) * (A(c) * 3 ^ Nat.clog 2 n + B(c) * n)
```

after multiplication and addition weights are incorporated into the explicit
functions `A` and `B`. The proof states their definitions. A theorem for only
the balanced textbook recurrence does not satisfy this contract.

### Schönhage

Write `K = 3^k`. For any valid `SchoenhageSchedule N`, the triadic worker
satisfies a recurrence of the form

```text
T(N) ≤ 2 * K * T(L) + A * K * L * k + B * K * L + D * N
```

where `A`, `B`, and `D` are explicit functions of `c_add` and `c_mul`. The
term `K * L * k` counts the coefficient operations in the two radix-3
transforms and their inverse transforms. This term cannot be replaced by
`N * k` for an arbitrary value of `SchoenhageSchedule N`.

The chooser supplies the facts needed to solve the recurrence. There are
positive constants `C0`, `cK0`, `cK1`, `cL0`, and `cL1`, and a threshold
`s0`, such that every requested product length `s ≥ s0` has a padded
half-length `N` and schedule `σ` satisfying:

```text
s ≤ 2 * N ≤ C0 * s
schedule? N = some σ
N ≤ cK0 * σ.K * σ.K
σ.K * σ.K ≤ cK1 * N
N ≤ cL0 * σ.L * σ.L
σ.L * σ.L ≤ cL1 * N
```

Thus `K` and `L` are within constant factors of `sqrt N`, and the transform
term is bounded by a constant multiple of `N * k`. The chooser also proves
recursive completeness: whenever a generated `L` remains above the
Karatsuba cutoff, `schedule? L` returns a schedule satisfying the same
balance inequalities. These facts bound the number of schedule steps by an
explicit constant multiple of
`Nat.clog 3 (Nat.clog 3 N + 1) + 1`.

The global theorem will fix the base case to the counted Karatsuba worker with
cutoff `c`. For inputs whose two lengths are at most `n`, it supplies an
explicit constant `C` depending on `c`, `c_add`, `c_mul`, and the chooser
constants such that the cost is at most

```text
C * n * (Nat.clog 3 n + 1) *
  (Nat.clog 3 (Nat.clog 3 n + 1) + 1)
```

for every `n`. The added ones cover zero, constant, and other small inputs.
The public `schoenhagePlan` may accept any lawful base plan, and its
correctness theorem applies to that general form. No operation bound follows
for a caller-supplied base plan unless it has its own parametric worker,
specialization theorem, obliviousness theorem, and weighted bound.

## Non-claims

- The theorems do not bound the raw array definitions selected by `@[csimp]`.
- The theorems do not bound `GF2Poly` word operations. One word XOR represents
  64 coefficient additions, and the packed base cases use carry-less
  multiplication.
- The theorems do not bound time or memory.
- No lower bound is claimed. cslib's general lower-bound lemma requires finite
  query response types, which excludes `ArithQuery R` for an arbitrary
  infinite ring.

## External comparators

No external comparator is required. The permitted reason is
`complexity-layer`: this library has no benchmark target, and `HexPolyFast`
owns the relevant performance measurements.

## Infrastructure

Implementation of this planned library requires the following changes:

- `lakefile.lean` requires cslib at the selected revision.
- `libraries.yml` records `cslib: true`, `complexity_layer: true`, and the
  computational owners. The schema parser and validators must accept these
  fields and require zero benchmark and conformance targets for a complexity
  layer.
- `scripts/libgraph.py` recognizes `Cslib` as an external import root.
  `scripts/check_dag.py` permits `Cslib.*` imports only in libraries marked
  `cslib: true` and applies the Mathlib-importing build restrictions to them.
- The library builds in the existing CI job. No workflow or additional job is
  added.

The release code already obtains external revisions from
`lake-manifest.json`. The release manifest is amended only after the project
chooses a release convention for cslib companions.

## Milestones

1. **Query definitions and Karatsuba.** Add the cslib dependency and
   complexity-layer metadata. Define `freeOps`, `CostOblivious`, and
   `WeightedBound`. Refactor the proof-facing Karatsuba definition through
   `karatsubaWorker`, then prove specialization, obliviousness, and the
   dispatcher bound.
2. **Schönhage.** Prove specialization and obliviousness for
   `schoenhageWorker`. Prove the per-schedule recurrence, bounded padding,
   chooser balance, recursive completeness, and the global bound with the
   counted Karatsuba base.
3. **cslib update.** Propose `CostOblivious` and `WeightedBound` upstream if
   they are useful outside Hex. Replace local definitions with accepted cslib
   definitions when their statements agree, then update to a merged revision.

The obliviousness and chooser theorems are part of the corresponding bound
milestone. An honest-oracle-only inequality does not complete either
milestone.

## File organisation

```text
HexPolyFastCslib/
  Query.lean        -- freeOps, CostOblivious, WeightedBound
  Karatsuba.lean    -- specialization, obliviousness, dispatcher bound
  Schoenhage.lean   -- specialization, recurrence, chooser facts, global bound
HexPolyFastCslib.lean
```

The eventual library entry has this shape:

```yaml
  HexPolyFastCslib:
    deps: [HexPolyFast]
    mathlib: true
    cslib: true
    complexity_layer: true
    computational_owners: [HexPolyFast]
    done_through: 0
    status: planned
```

## References

- cslib PR [#401, query complexity framework](https://github.com/leanprover/cslib/pull/401):
  `FreeM`, `eval`, `cost`, `countQueries`, `UpperBound`, and `ArithQuery`.
- Arnold Schönhage, *Schnelle Multiplikation von Polynomen über Körpern
  der Charakteristik 2*, Acta Informatica 7 (1977), 395-398.
- Richard P. Brent, Pierrick Gaudry, Emmanuel Thomé, and Paul Zimmermann,
  [*Faster Multiplication in GF(2)[x]*](https://doi.org/10.1007/978-3-540-79456-1_10),
  ANTS-VIII (2008), LNCS 5011, 153-166.
