# hex-poly-fast-cslib (operation-count bounds, depends on hex-poly-fast and cslib)

Proved coefficient-operation bounds for the generic multiplication
algorithms of
[hex-poly-fast](../../HexPolyFast/SPEC/hex-poly-fast.md), built on the
query-complexity framework of the Lean computer-science library
[cslib](https://github.com/leanprover/cslib). This is the first `-cslib`
companion library. It plays the same architectural role for complexity
that the `-mathlib` companions play for Mathlib correspondence: the
computational library stays free of the external dependency, and the
companion proves theorems about it.

## Complexity-layer classification

This library is a `complexity-layer`.

Computational conformance owner: `HexPolyFast`
Computational performance owner: `HexPolyFast`

A complexity-layer library contains no algorithms of its own, no
conformance fixtures, no oracles, and no benchmarks. Its theorems bound
the number of coefficient operations performed by programs that are, by
the specialization theorems below, the algorithms its computational owner
executes. It claims nothing about wall-clock time; benchmarks in the
owning library remain the only evidence of speed.

## Why this library exists

**hex-poly-fast enforces complexity by body shape and benchmarks, and that
enforcement has no theorem.** Its complexity-contract table is a review
obligation: a quadratic body violates the SPEC, but nothing in the build
proves the bound. For most of the library that is the right trade, because
the contracts are simple enough to check by reading. The Schönhage
recursion is not: its bound depends on a schedule invariant
(`L` near `sqrt N` at every level), and an implementation that satisfies
every local body-shape rule can still lose the global bound by choosing
schedules badly. A proved operation count is the review tool that scales.

**The bound must be a theorem about the shipped algorithm.** Every lawful
`MulPlan` returns the same polynomial, so a bound proved about a program
that merely agrees with the plan's output is vacuous. hex-poly-fast
therefore defines its counted algorithms once, as operation-parametric
workers, and executes them at the identity monad. This library
instantiates the same workers at a free monad and counts. The two
instantiations are connected by a specialization theorem, not by output
equality.

**The dependency must stay out of the computational graph.** cslib
requires Mathlib. Placing operation counts in the computational libraries
would pull both into every consumer, which is the exact failure the
`-mathlib` split exists to prevent. The companion pattern already solves
this, and this library extends it to a second external proof dependency.

hex-poly-fast's SPEC previously assigned any future asymptotic theorem to
"that consumer or a documentation proof". This library is the considered
replacement of that position, and hex-poly-fast's §The Mathlib layer now
points here.

## Dependency and pin policy

This library requires cslib, and cslib requires Mathlib. It is therefore
marked and treated like a `-mathlib` library: proof-only, no
`precompileModules`, no benches, and outside the Mathlib-free build
surface.

Until cslib PR
[#401](https://github.com/leanprover/cslib/pull/401) merges, the lakefile
pins cslib to a recorded commit of that PR's branch (at SPEC time,
`36e098cfc04fbb8e9b44086d64ce433514ee18d4`). The pin is updated by ordinary
dependency bumps. The verified compatibility state at SPEC time:

- cslib's and hex-dev's Lean toolchains agree (`v4.34.0-rc2`).
- cslib pins a newer Mathlib than hex-dev. Lake resolves dependencies from
  the root manifest, so cslib builds against hex-dev's Mathlib revision.
  The `Cslib.Algorithms.Lean.Query.*` modules this library imports build
  cleanly against that revision. A handful of unrelated cslib modules
  (the omega-sequence topology corner) import a Mathlib file that does not
  exist at hex-dev's revision; they are not imported here and are never
  built as dependencies.
- This library imports only `Cslib.Algorithms.Lean.Query.*` and the
  `FreeM` foundations they re-export, never the `Cslib` umbrella module.

Releasing or publishing this library requires a merged cslib revision (or
a maintained fork with a stable branch); a floating PR commit is
acceptable only inside the monorepo.

## The query model

Programs are `Cslib.FreeM Q α` values over cslib's arithmetic query type:

```lean
inductive ArithQuery (α : Type) : Type → Type where
  | add (a b : α) : ArithQuery α α
  | sub (a b : α) : ArithQuery α α
  | mul (a b : α) : ArithQuery α α
```

with cslib's `honest` oracle interpreting queries by the actual ring
operations, `FreeM.eval` for results, and `FreeM.cost` with
`ArithQuery.weight c_add c_mul` for weighted counts (subtraction weighs as
addition; multiplication weighs separately, because multiplications drive
the recursions). If the upstream `Arith` files change shape before the pin
is next moved, an equivalent local query type replaces them with no change
to the theorem statements; the pin makes this a scheduled decision rather
than a build break.

The instantiation record is one definition:

```lean
def freeOps : CoeffOps (FreeM (ArithQuery R)) R where
  add a b := FreeM.lift (.add a b)
  sub a b := FreeM.lift (.sub a b)
  mul a b := FreeM.lift (.mul a b)
```

`CoeffOps` and the workers are hex-poly-fast's; this library adds no
algorithm text. Every quotient-ring operation of the Schönhage recursion
is scalar-expanded: `Triadic` elements are fixed-shape data, their
additions and twiddle folds issue base-ring queries coefficient by
coefficient, and pointwise products recurse through the same worker. The
bounds therefore count base-ring operations, which is the standard
algebraic complexity measure and what the headline inequality means.

## Specialization

For each worker, the specialization theorem identifies running the free
program under the honest oracle with the executable algorithm:

```lean
theorem karatsubaWorker_eval (cutoff fuel : Nat) (a b : Array R) :
    (karatsubaWorker freeOps cutoff fuel a b).eval ArithQuery.honest =
      karatsubaWorker idOps cutoff fuel a b
```

and likewise for the Schönhage worker. The proof is induction over the
worker body (or one generic lemma about interpreting `freeOps` through
`FreeM.liftM`). Because hex-poly-fast *defines* its recursions as the
`idOps` instantiations, this theorem makes every count below a statement
about the algorithm hex-poly-fast executes. The raw array runtimes are
connected to those definitions by output-equality `@[csimp]` theorems
only, and no operation count is claimed for them.

## Cost obliviousness

Query traces are not oracle-independent: queries embed operands, and a
dishonest oracle changes the operands of later queries. What holds for
these workers is the weaker, sufficient property that the *cost* does not
depend on the oracle:

```lean
def CostOblivious {T : Type} [AddMonoid T]
    (weight : {ι : Type} → Q ι → T) (p : FreeM Q α) : Prop :=
  ∀ o₁ o₂, p.cost o₁ weight = p.cost o₂ weight
```

Each worker's program is proved `CostOblivious` for every weight: its
control flow (splits, schedule choice, recursion depth, base-case entry)
depends only on sizes and the schedule, never on coefficient values. This
is a real design constraint on hex-poly-fast's workers, and it is the
reason its `Triadic` carrier is never normalized mid-transform. With
`CostOblivious` proved, bounds quantified over all oracles follow from the
honest-oracle count; without it, a bound would be honest-oracle only.

## Bounds

cslib's `UpperBound` counts queries. Weighted bounds need the analogue
over `cost`, defined here and a candidate for upstreaming:

```lean
def WeightedBound {T : Type} [AddMonoid T] [LE T]
    (prog : α → FreeM Q β) (size : α → Nat)
    (weight : {ι : Type} → Q ι → T) (bound : Nat → T) : Prop :=
  ∀ (oracle : {ι : Type} → Q ι → ι) (n : Nat) (x : α),
    size x ≤ n → (prog x).cost oracle weight ≤ bound n
```

**Karatsuba (milestone 1).** The bound covers the public dispatcher, both
operand sizes, and the cutoff, in integer form with no real exponents:
for sizes `m ≥ n` and cutoff `c`, the query count of the dispatcher
worker is at most

```text
ceil(m/n) * (A(c) * 3 ^ Nat.clog 2 n + B(c) * n)
```

with `A` and `B` explicit polynomials in `c` fixed by the proof. The
balanced case is the `ceil(m/n) = 1` row. A bound for the textbook
balanced recursion alone does not discharge this milestone: the point of
the warm-up is to validate the worker architecture against the dispatch
structure hex-poly-fast actually has.

**Schönhage (milestone 2).** The recurrence is stated over the schedule:
for a valid `SchoenhageSchedule N`, the count for the triadic product
worker at half-length `N` is at most `2 * 3^k` times the count at
half-length `L` plus an explicit `O(N * k)` transform term. The chooser's
balance property (`L` within a constant factor of `sqrt N` whenever a
schedule exists) then closes the recurrence to the headline bound: an
explicit constant `C` with query count at most

```text
C * n * Nat.clog 3 n * (Nat.clog 3 (Nat.clog 3 n) + 1)
```

for the full-product worker at input size `n`, all stated in `Nat`. The
`log log` factor is the recursion depth; the proof tracks it as the
number of schedule steps until `schedule?` returns `none`.

## What is not claimed

- Nothing about wall-clock time or memory; benchmarks in hex-poly-fast
  and hex-gf2 remain the speed evidence.
- Nothing about the raw array runtimes or the packed `GF2Poly` kernel.
  One packed XOR performs 64 coefficient additions at once, so a
  word-level cost model is a different theorem, reserved for a possible
  later hex-gf2-cslib.
- No lower bounds. cslib's decision-tree lemma requires finite query
  response types; `ArithQuery R` over an infinite ring is outside it.

## External comparators

No external comparator is required. Justification: `complexity-layer`,
analogous to `correspondence-only-layer` per
[SPEC/benchmarking.md §Comparator naming](../benchmarking.md); the
computational owner carries the comparators.

## Infrastructure amendments

Implemented with the library, not by this SPEC-only change:

- `lakefile.lean` gains the cslib `require` at the pinned revision.
  `scripts/release/sync_released.py` reads external pins generically from
  `lake-manifest.json`, so released-repo pin rewriting needs no change.
- `libraries.yml` gains a `cslib: true` field on this library. The schema
  is enforced, so this touches the parser and validation in
  `scripts/libgraph.py` and `scripts/check_dag.py` (`LIBRARY_FIELDS`,
  `LibraryInfo`, and the field validators), not only the DAG check.
- `Cslib` joins `EXTERNAL_IMPORT_ROOTS` in `scripts/libgraph.py`, and
  `check_dag.py` restricts `Cslib.*` imports to libraries marked
  `cslib: true`, exactly as `Mathlib.*` imports are restricted to
  `mathlib: true` libraries. A library marked `cslib: true` is implicitly
  Mathlib-adjacent for every build rule (`precompileModules` ban, no
  benches, proof-only runtime exemptions).
- `SPEC/design-principles.md` extends "No Mathlib in the computational
  core" to cslib in one paragraph.
- CI: cslib modules build inside the existing single job. cslib has no
  olean cache service, but the imported Query modules and their Mathlib
  dependencies are covered by the Mathlib cache plus a small residual
  build, measured before the library is activated.

## Milestones

1. **Framework and Karatsuba.** The cslib pin, `freeOps`,
   `CostOblivious`, `WeightedBound`, the Karatsuba specialization and
   cost-obliviousness theorems, and the dispatcher-covering Karatsuba
   bound. This milestone validates the worker architecture end to end on
   an algorithm whose mathematics is finished, before any of it is on the
   Schönhage critical path.
2. **Schönhage.** Specialization and cost obliviousness for the Schönhage
   worker, the schedule recurrence, the chooser balance property, and the
   headline bound.
3. **Upstreaming review.** Offer `CostOblivious` and `WeightedBound` to
   cslib; adopt the upstream forms if accepted; re-pin to merged cslib.

No milestone may weaken a bound statement to an honest-oracle-only form
as a shortcut: cost obliviousness is part of milestones 1 and 2, not a
follow-up.

## File organisation

```text
HexPolyFastCslib/
  Query.lean        -- freeOps, CostOblivious, WeightedBound
  Karatsuba.lean    -- specialization, obliviousness, dispatcher bound
  Schoenhage.lean   -- specialization, obliviousness, recurrence, bound
HexPolyFastCslib.lean
```

`libraries.yml` eventually gains, after cslib is pinned and the
hex-poly-fast workers exist:

```yaml
  HexPolyFastCslib:
    deps: [HexPolyFast]
    mathlib: true
    cslib: true
    done_through: 0
    status: planned
```

The release manifest is updated only when a release shape for `-cslib`
companions is decided, never by this SPEC-only change.

## References

- cslib PR [#401, query complexity framework](https://github.com/leanprover/cslib/pull/401):
  `FreeM` programs, oracles, `cost`, `countQueries`, `UpperBound`, and the
  `ArithQuery` example this library builds on.
- Arnold Schönhage, *Schnelle Multiplikation von Polynomen über Körpern
  der Charakteristik 2*, Acta Informatica 7 (1977), 395-398.
- Richard P. Brent, Pierrick Gaudry, Emmanuel Thomé, and Paul Zimmermann,
  [*Faster Multiplication in GF(2)[x]*](https://doi.org/10.1007/978-3-540-79456-1_10),
  ANTS-VIII (2008), LNCS 5011, 153-166.
