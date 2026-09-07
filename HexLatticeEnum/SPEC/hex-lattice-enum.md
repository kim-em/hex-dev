# hex-lattice-enum

Exact enumeration of integer lattice vectors in a closed Euclidean ball,
shortest nonzero vectors, and closest vectors to a rational target.
Fincke-Pohst enumeration uses Schnorr-Euchner coefficient ordering and exact
rational inequalities. Every complete answer proves exhaustion of the search,
including all ties. A budgeted answer distinguishes a checked candidate from
a proved optimum.

## Scope and dependencies

The first version accepts an independent integer row basis, with any ambient
dimension, a rational target, and a rational squared radius. The basis need
not be square, integral-orthogonal, or initially LLL-reduced. Enumeration
works in the lattice's real span while retaining the target's orthogonal
residual in every distance bound.

The computational library depends on `HexLLL`, `HexGramSchmidt`, `HexMatrix`
and `HexBasic` and remains Mathlib-free. It uses the existing integer
Gram-Schmidt data, matrix/vector arithmetic and checked same-lattice
transformations. LLL is optional preprocessing, not a hypothesis of the
enumeration theorem. Its default parameters and any existing candidate
provider retain the contracts of [hex-lll](../../HexLLL/SPEC/hex-lll.md).
This library introduces no new extern or external candidate provider.

`HexLatticeEnumMathlib` depends on this library, `HexLLLMathlib`,
`HexGramSchmidtMathlib` and `HexMatrixMathlib`. Its contract is below.
No dependency on intervals, permutation groups or lattice isometry is needed.

Dependent generating lists, arbitrary rational Gram matrices without an
integer embedding, Voronoi cells, successive minima, BKZ, sieving and lattice
isometry are separate extensions. A dependent matrix is rejected rather than
silently enumerated with duplicate coefficient representations. A later
Hermite-normal-form adapter can compute a basis and prove lattice equality.

### Execution and proof ownership

`HexLatticeEnum` owns every executable definition: input checks, exact data
preparation, integer bounds, coefficient ordering, enumeration, optimization,
budgets, basis transformations, certificate production, decoding and checking.
All public operations run with only this library imported. Their definitions
and termination arguments must not depend on the Mathlib companion.

`HexLatticeEnumMathlib` owns the unconditional correctness proofs for those
definitions, including preparation validity, enumeration completeness,
optimality, certificate soundness and acceptance of generated certificates.
It also identifies the results with integer spans and real Euclidean geometry.
The theorem obligations below belong to this companion unless explicitly
identified as computational termination obligations. Elementary arithmetic,
reconstruction and traversal lemmas may stay in the computational library
when their proofs use only its existing dependencies.

Prepared data and their validity predicates may be defined in the
computational library. Local search lemmas may assume that validity; the
companion proves it for data produced from every accepted independent input
and discharges it in the public theorems. Callers supply no additional
Gram-Schmidt correctness witness to execute the public operations or use
their unconditional guarantees. Runtime validation alone does not establish
that preparation always succeeds on supported inputs.

This follows the existing LLL split: executable integer Gram-Schmidt data
are computed without Mathlib, while their determinant and norm correspondence
is proved in `HexGramSchmidtMathlib`. Follow the
[Bareiss proof-placement boundary](../../HexBareiss/SPEC/hex-bareiss.md#mathlib-free-vs-mathlib-bridge-proof-surface)
for these proofs. The companion proves properties of the computational
definitions directly; it does not provide a second search implementation.

## Basis, coefficients and result identity

Use the namespace `Hex.LatticeEnum`. The required input shape is:

```lean
namespace Hex.LatticeEnum

structure Basis (n m : Nat) where
  rows : Hex.Matrix Int n m
  independent : Hex.Matrix.independent rows

end Hex.LatticeEnum
```

`ofMatrix?` checks the independence predicate and returns this input exactly
when it holds. For `b : Basis n m` and `z : Vector Int n`, `vector b z`
is the ambient integer vector `sum_i z_i * b_i`. Prove `vector_injective`
from independence. Define `distanceSq b t z` as the sum of squares of
`(vector b z : Vector Rat m) - t`. The result is a nonnegative rational.

Search visits coefficient vectors in the working basis. Public answers retain
coefficients in the original input basis, the corresponding ambient vector,
and its exact squared distance. These fields have reconstruction theorems.
Sort complete lists lexicographically by ambient integer coordinates, removing
dependence on the search order. There are no duplicates. A deterministic tie
choice, where needed, is the first element of this sorted list. Output lists
for different bases of the same lattice agree in ambient vectors and distances,
not necessarily in their coefficient fields.

Rank zero is supported: its lattice is `{0}`, and its coefficient vector is
empty. A ball contains that vector exactly when `||t||² ≤ radiusSq`. A
negative squared radius gives an empty complete ball. `shortest` returns
`none` exactly at rank zero. `closest` always has at least the zero vector
as a candidate, including for rank zero and targets outside the span.

## Exact Gram-Schmidt data

For rows `b_i`, write `b_i*` for the orthogonalized rows, `mu[i,j]` for
the lower-triangular Gram-Schmidt coefficients, and `d_i = ||b_i*||²`.
Independence implies `d_i > 0`. Use
`Hex.GramSchmidt.Int.data`, whose leading determinants `D` and scaled
coefficients `nu` give `d_i = D[i+1]/D[i]` and
`mu[i,j] = nu[i,j]/D[j+1]` for `j < i`.

Reconstruct the rational orthogonalized vectors by the triangular recurrence
`b_i* = b_i - sum_{j<i} mu[i,j] * b_j*`. This is executable rational
arithmetic. The semantic `GramSchmidt.Rat.basis` API contains noncomputable
wrappers around the executable `GramSchmidt.basisMatrix` and `coeffMatrix`
kernels. The preparation routine uses the integer data and the triangular
recurrence above; its agreement with the semantic basis is proved in
`HexLatticeEnumMathlib` using the integer data's correspondence theorems
and the existing orthogonality and reconstruction lemmas.

In particular, `GramSchmidt.Int.gramDetVec_eq_gramDet` consumes a
`StepWitness`, whose general constructor `StepWitness.ofGram` is in
`HexGramSchmidtMathlib`. The norm-ratio theorem `basis_normSq` and
scaled-coefficient correspondence `scaledCoeffs_eq` also live there.
Use these in the companion to prove that `prepare` yields the stated
coefficients and positive norms for every `Basis`; the executable routine
does not take these proofs as additional inputs. Any internal preparation
validation-failure branch must be proved unreachable for such inputs and
must not add a public failure case.

Compute `tau_i = <t,b_i*>/d_i` and
`t_perp = t - sum_i tau_i*b_i*`. Prove orthogonality of `t_perp` to every
basis row and the exact identity

```text
distanceSq b t z = ||t_perp||²
  + sum_i d_i * (z_i + sum_{j>i} mu[j,i]*z_j - tau_i)².
```

This identity is required for rectangular bases. Omitting `||t_perp||²`
would incorrectly accept points for targets outside the span.

`prepare` computes these data once for each basis/target pair. A basis-only
prepared value may reuse the orthogonalization across targets, with explicit
basis identity in its type. No stale cache may be reused for another basis.

## Enumeration and exact integer bounds

Fix a suffix `z_{i+1}, ..., z_{n-1}` and its accumulated squared cost `s`.
At level `i`, set

```text
c = tau_i - sum_{j>i} mu[j,i]*z_j
R = radiusSq - ||t_perp||² - s.
```

If `R < 0`, this branch is empty. Otherwise the next coefficient must satisfy
`d_i*(z_i-c)² ≤ R`. Compute the complete integer interval without an
approximate square root. Write `c = u/v` with `v > 0` and
`R/d_i = A/B` with `A ≥ 0`, `B > 0`. Set

```text
T = floor_sqrt(floor(A*v²/B))
lo = ceil((u-T)/v)
hi = floor((u+T)/v).
```

Here all floors, ceilings and square roots are exact integer operations.
Prove `bounds_iff`: an integer `z` satisfies the quadratic inequality
exactly when `lo ≤ z ∧ z ≤ hi`. The proof uses that `(v*z-u)²` is an
integer. Negative numerators use mathematical floor/ceiling division, not
truncation toward zero. An empty interval has `hi < lo` and contributes no
children. Equality at the boundary is always included.

Visit this interval in nondecreasing `|z-c|`, with the smaller integer first
on ties. Implement Schnorr-Euchner ordering by merging two finite streams:
descending from `min hi (floor c)`, and ascending from
`max lo (floor c + 1)`, each restricted to `[lo,hi]`. Compare distances
using integers after clearing the positive denominator. The two streams are
disjoint and cover the interval, including integral and half-integral centres.
Do not sort or allocate the entire interval before visiting its first child.

Descend from `n-1` to zero, add `d_i*(z_i-c)²` to the suffix cost, and
emit a leaf when all coefficients have been chosen. Termination follows from
decreasing remaining dimension and finite child intervals. The loop invariant
identifies the visited suffix and its exact cost and characterizes every
possible completion. Prove that every pruned suffix violates the radius
bound, and that every coefficient vector satisfying the bound is reached once.

No Gaussian-heuristic cutoff or probabilistic pruning coefficient is allowed
in the complete operation. Floating-point estimates may be added later to
order work, but may not remove a branch without an exact bound proving it
empty. The initial implementation uses exact arithmetic for ordering too.

## Public operations and completeness

The API names and result contracts are:

| Operation | Result and contract |
| --- | --- |
| `enumerate b t radiusSq` | Sorted complete list of every lattice vector in the closed ball. |
| `enumerateWith budget b t radiusSq` | Either that complete result or a checked partial list with remaining search work. |
| `babai b t` | One checked candidate obtained by nearest-plane rounding. No optimality claim. |
| `shortest b` | `none` at rank zero, otherwise every shortest nonzero vector and their common squared norm. |
| `shortestWith budget b` | Complete shortest-vector answer or incomplete progress with an incumbent when available. |
| `closest b t` | Every closest lattice vector and their common squared distance. |
| `closestWith budget b t` | Complete closest-vector answer or incomplete progress with an incumbent. |

The companion theorem `enumerate_spec` states both directions for the
computational `enumerate`, with no extra preparation-validity hypothesis or
unmentioned hypothesis on the target:

```text
v occurs in the returned ambient vectors ↔
  b.rows.memLattice v ∧ sum_j ((v_j : Rat) - t_j)² ≤ radiusSq.
```

It also states no duplicates and reconstruction of every reported coefficient
vector. `shortest_spec` excludes zero, proves that every returned norm is the
minimum among all nonzero lattice vectors, and includes every vector attaining
that norm. `closest_spec` has the analogous theorem over all lattice vectors.
These are global minima, not merely minima among the visited vectors.

For shortest vectors at positive rank, choose an initial nonzero row of
minimum norm. For closest vectors, use Babai's candidate: recursively round
the same centres as enumeration, taking the smaller integer on a tie.
These candidates give finite initial squared radii. An initial candidate
radius is a proved upper bound even for a poor basis.

Find the optimum by branch-and-bound, replacing the incumbent when an exact
smaller distance is found. Prune only when a suffix's lower bound exceeds
the current incumbent. The invariant includes incumbent membership and
states why a discarded branch cannot contain a better vector. Then run a
fixed-radius enumeration at the attained radius to recover all ties and a
complete certificate. For shortest vectors discard zero only when selecting
nonzero minima, not from ordinary ball enumeration. An implementation may
retain all ties during the first pass after proving the corresponding
coverage invariant, but may not return only the first optimum found.

## Budgets and preprocessing

`Budget` counts visited search nodes, stored answers and certificate nodes
separately. Deterministic limits are part of the executable result contract.
An external wallclock cancellation is handled as incomplete execution, not
as mathematical failure. Complete and incomplete results are different
constructors. A partial result contains only directly checked points, an
incumbent if found, and enough traversal state to describe pending work.
It claims no globally exhausted radius merely because some branches finished.
Resuming traversal is not part of the first public API.

Exhausting a budget does not mean the ball is empty, the current vector is
shortest, or a target is outside the lattice. If the optimum was found but
tie enumeration or certificate generation stopped, the result remains
incomplete unless a separate accepted optimum certificate is actually present.
`enumerate` and the unbudgeted optimization operations are total mathematical
algorithms with finite searches, with no claim of practical feasibility at
arbitrary rank. Their totality proofs must not rely on choosing a large fuel
constant experimentally.

Executable traversal must terminate by decreasing remaining dimension and
finite child intervals, independently of the Mathlib correctness proofs.
Optimization updates the incumbent within the finite initial search and
then performs a finite search for ties. Any internal handling of invalid
prepared data must also terminate; the companion proves that the public
operations on `Basis` inputs take the valid branches and exhaust precisely
the required search. Budget exhaustion and external cancellation remain the
sources of incomplete results in the budgeted operations on supported inputs.

When preprocessing returns `B' = U*B` and `B = V*B'`, replay the existing
`Matrix.sameLatticeCert`. Keep the original input in every public result.
For coefficients represented as columns, `z` in `B'` becomes `Uᵀ*z` in
`B`. Prove reconstruction and, using independence, injectivity of this map.
Sorting ambient vectors makes the complete answer independent of LLL choices.
There is no requirement that shortest-vector coefficients themselves be small
or canonical across different bases.

## Certificate replay

Checking membership and norm of a proposed point proves only those two facts.
The first certificate of completeness is a finite enumeration tree for a
fixed squared radius. It contains the working basis, checked transforms if
preprocessing was used, rational Gram-Schmidt data and a tree of integer
coefficient choices. Each node identifies the current suffix. Child labels
must cover exactly the interval recomputed by the checker, without duplicates.
A missing branch, a repeated branch or an unsupported pruning marker rejects
the certificate. Reject malformed dimensions and nonpositive Gram-Schmidt norms.

The checker verifies triangular basis reconstruction, orthogonality, positive
norms, the target projection and its residual, and the exact bounds at each
node. It verifies a pruned node only when the residual budget is negative or
its exact interval is empty. A dimension-zero leaf checks the distance
directly, including negative-radius and rank-zero queries. It
reconstructs leaf vectors and compares their complete sorted list with the
claimed output. Data are finite and decoded with explicit node/size limits.
The checker does not trust a stored radius bound, cached suffix cost or a
candidate's claimed Gram-Schmidt coefficients.

The checker and native producer are defined in `HexLatticeEnum`. The companion's
`checkEnumeration_sound` proves the complete membership, reconstruction and
uniqueness contract of `enumerate_spec` for the output of any accepted
certificate, without assuming that the certificate came from the native
producer. The companion also proves that every finished fixed-radius run on
supported inputs supplies an accepted certificate. Certificate replay can require
asymptotically as many nodes as enumeration. This SPEC does not promise a
compact polynomial-size proof of an exhaustive search.

An optimum certificate additionally supplies a lattice point of squared
distance `r` and a complete fixed-radius certificate at `r`. For shortest
vectors the supplied point is nonzero, and every nonzero leaf must have norm
`r`. For closest vectors every leaf must have distance `r`. This excludes
every strictly better point, proves attainment and includes all ties.
The rank-zero shortest answer has its own direct proof.

Proof-producing callers import the companion's `checkEnumeration_sound` or
optimum-checker theorem, execute the computational search outside the kernel,
and replay literal certificates through the computational checker. Expose
the integer/rational checking operations for kernel reduction, with
separate limits for generation, decoding and replay. `native_decide` and new
axioms are forbidden. No generic certificate-cache format is introduced here.

## Mathlib companion

`HexLatticeEnumMathlib` proves correctness of the executable API as well as
its correspondence with Mathlib. It establishes preparation validity,
`vector_injective`, the exact distance decomposition, exhaustive search and
all-ties optimality, and certificate-checker soundness and producer acceptance.
Its public `enumerate_spec`, `shortest_spec` and `closest_spec` theorems apply
to the operations in `Hex.LatticeEnum` with only their stated input contracts.
Internal validity hypotheses are discharged using the existing integer
Gram-Schmidt correspondence. No executable operation moves into this library.

The lattice is the **integer span** of the basis rows, not their rational or
real span. `HexLatticeEnumMathlib` identifies it with a `Submodule ℤ` of the
rational coordinate space and with its image in real Euclidean space. A
`Submodule ℚ` generated by a nonzero row would contain arbitrarily short
rational multiples and would invalidate shortest-vector claims.

Alongside the computational API's headline theorems, prove their integer-span
and real squared-distance formulations, including global shortest and closest
minima with list completeness as well as soundness. Coordinate casts preserve the
exact rational squared distances. Prove discreteness from the integer
embedding and independence rather than assuming that every finitely generated
real additive subgroup is discrete.

For positive rank and shortest squared norm `s`, derive packing radius
`sqrt(s)/2` within the real span and kissing number equal to the cardinality
of the complete shortest-vector list. Include both signs. No packing-radius
formula is asserted for the zero lattice. Successive minima and covering
radius remain outside this SPEC.

The companion is to be classified `correspondence_only: true` when activated.
Its comparator absence class is **correspondence-only-layer**. Runtime
conformance and performance belong to the computational owner below.
Build-only examples under `HexLatticeEnumMathlib/Tests.lean` exercise the
preparation theorem, unconditional search contracts, kernel certificate replay,
transport and geometric consequences, with no runtime benchmark declarations.

Computational conformance owner: `HexLatticeEnum`.

Computational performance owner: `HexLatticeEnum`.

## Conformance and benchmarks

Add `conformance/HexLatticeEnum/{Conformance,EmitFixtures}.lean`,
`conformance-fixtures/HexLatticeEnum/latticeenum.jsonl`, and
`scripts/oracle/lattice_enum.py`. Fixtures record basis dimensions and rows,
the rational target and squared radius, original-basis coefficients, all
ambient vectors and exact distances, and complete/incomplete status.

For small ranks, the always-available independent oracle uses Python integer
and `fractions.Fraction` arithmetic and Cartesian enumeration in a proved
coefficient box. Derive that box independently from the rational left inverse
of the basis map and a coordinate bound on the ambient ball. Do not copy the
Gram-Schmidt recursion into the oracle. Use exact distance filtering. Validate
all returned vectors rather than comparing only their number or best norm.
Concretely, for positive rank let `L = (B*Bᵀ)⁻¹*B`, so coefficients of
`v = Bᵀ*z` satisfy `z = L*v`. For nonnegative radius choose a nonnegative
integer `h` with `h² ≥ radiusSq`. Then `|v_j| ≤ ceil(|t_j|)+h` and the
triangle inequality bounds each `|z_i|` by the corresponding weighted row sum
of `|L|`. These bounds do not use the search's Gram-Schmidt data.

Required cases include rank/ambient dimension zero, a non-square basis,
dependent-input rejection, negative and zero radii, a target outside the span,
integer and half-integer centres, a radius exactly touching a vector, large
negative coefficients, ties, and a case where Babai is not optimal. Test
unreduced and checked LLL-reduced bases and changes of basis with determinant
`-1`. Force every budget limit. Corrupt transforms, Gram-Schmidt data, one
interval endpoint and a missing leaf in certificate regression tests.

[fplll](https://github.com/fplll/fplll) supplies `shortest_vector` and
`closest_vector` for external comparisons. Require `SVPM_PROVED` and
`CVPM_PROVED` explicitly. Its
[CVP contract](https://github.com/fplll/fplll/blob/master/fplll/svpcvp.h)
requires an independent basis LLL-reduced at `LLL_DEF_DELTA` and
`LLL_DEF_ETA`. Supply that basis, and record preprocessing separately from
search on both sides. Pin these choices in the driver and record status
codes. For a square full-rank integer basis
and a rational target with denominator `q`, scale both basis and target by
`q` for integer-target CVP and divide squared distances by `q²` afterward.
Cross-check exact minima and candidate membership, not tie choices. Restrict
the comparison to inputs the selected API supports.

The fplll comparator is **informational**. It uses floating-point
Gram-Schmidt with error control, while Hex uses exact rationals, and its SVP/
CVP calls return a candidate rather than the complete list and Lean
certificate. Time Hex's optimum-search pass separately from tie enumeration
and certificate generation. Full-ball and all-ties enumeration, certificate
generation/replay and Babai-only calls have
**no-comparable-surface-in-named-comparator** under this selected fplll API.
Their correctness is independently checked by the Cartesian oracle.

Required families in `bench/HexLatticeEnum/Bench.lean`:

| Family | Parameter and purpose |
| --- | --- |
| `rank-radius` | Vary rank and squared radius separately, reporting visited nodes and output count. |
| `basis-quality` | Same lattice with unimodularly sheared bases, with and without LLL. |
| `coefficient-height` | Fixed rank and shape with increasing integer and rational bit lengths. |
| `rectangular-target` | Fixed rank with increasing ambient dimension and nonzero orthogonal residual. |
| `ties-boundary` | Many shortest/closest vectors and exact closed-ball boundary cases. |
| `babai-gap` | Targets where nearest-plane rounding misses the optimum. |
| `certificate-replay` | Separate data preparation, search, tie enumeration, certificate generation and replay. |

State arithmetic work in visited nodes, dimension, emitted vectors and bit
lengths. The search is exponential in general and has an output-size lower
bound. Do not fit a universal polynomial in rank to a small easy ladder.
Follow the ordered modes in [benchmarking](../../SPEC/benchmarking.md), with
independently derived models or explicit canonical hard inputs and budgets.
The exact integer-bound routine and coefficient-order iterator get separate
attribution when profiling identifies them as significant costs.

Keep computational benches Mathlib-free and extend the existing CI scripts
and jobs for conformance and oracles. Scientific measurements use the existing
scheduled hardware workflow. No additional workflow or matrix is introduced.

## Placement and implementation order

1. `HexLatticeEnum/Basic.lean` defines independent inputs, coefficients,
   ambient vectors and distance. `GramSchmidt.lean` implements exact data
   preparation and its validity predicate. In
   `HexLatticeEnumMathlib/GramSchmidt.lean`, prove preparation validity,
   coefficient injectivity and the distance decomposition using the existing
   Gram-Schmidt correspondence.
2. `Bounds.lean` defines exact integer intervals and Schnorr-Euchner order.
   `HexLatticeEnum/Enumerate.lean` implements fixed-radius search and its
   structural termination argument. `HexLatticeEnumMathlib/Enumerate.lean`
   proves bounds, ordering and search completeness, reusing elementary lemmas
   from the computational library where available.
3. `HexLatticeEnum/Closest.lean` implements Babai and optimization.
   `Shortest.lean` handles nonzero minima. Budgeted forms share the same
   traversal. The companion's `Closest.lean` and `Shortest.lean` prove the
   candidate, budget and unconditional all-ties optimality contracts.
4. `HexLatticeEnum/Cert.lean` implements fixed-radius and optimum checkers,
   native certificate production and bounded decoding. The companion's
   `Cert.lean` proves checker soundness and producer acceptance;
   `HexLatticeEnumMathlib/Tests.lean` includes kernel replay proofs.
5. `HexLatticeEnumMathlib/Correspondence.lean` establishes integer-span and
   real-distance formulations of the correctness theorems. `Geometry.lean`
   proves the packing-radius and kissing-number consequences. Add umbrellas,
   computational conformance and benchmarks, and the manual under the ordinary
   phase rules.

The first manual example is an integer least-squares problem with a
nonoptimal Babai candidate, followed by a certified closest vector. For a
geometric example use the integer basis `(1,-1,0), (0,1,-1)` of `A₂` in
three-dimensional space. It has six shortest vectors of squared norm `2`,
so the general algorithm demonstrates the hexagonal lattice without assuming
that a regular hexagonal basis has integer coordinates in the plane.

Activation preserves the computational/Mathlib separation and requires the full
stated proof obligations. The current phase attestations live in `libraries.yml`.
Published repositories are generated from this monorepo only after release
readiness, using the existing manifest and guarded synchronization process.

## Total-helper invariants

Internal fallback values are `unreachable-by-pipeline-invariant` on completed
native runs. `ball_complete` proves that unlimited fixed-radius traversal
produces a tree; `optimize_spec` and `optimize_tree` establish the completed
tie pass used by optimum certificates. `enumerationCertificate_check`,
`closestCertificate_check` and `shortestCertificate_check` prove native
producer acceptance. `lllPreprocess_rows` proves that every positive-rank
LLL result passes independence and both recovered transformation checks;
`lllPreprocess_reduced` identifies the resulting reduced basis. Its identity
case at rank zero is the specified empty-basis operation. These total helpers
introduce no caller-visible failure case or weakened input contract.
