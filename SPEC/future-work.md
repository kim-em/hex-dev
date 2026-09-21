# Further work

Sketches for libraries and algorithms that do not yet have a SPEC. Each item
records enough scope, dependencies, and correctness obligations to start a
SPEC; it is not itself a specification.

[Libraries/README.md](Libraries/README.md) indexes work that has a SPEC, and
[libraries.yml](../libraries.yml) records the libraries currently registered in
the monorepo. Once an item below gains a SPEC, remove it from this file.

The usual certificate discipline applies: checking an equality, divisibility,
or decomposition establishes only that positive claim. Minimality,
maximality, irreducibility, uniqueness, nonexistence, and completeness each
need their own witness or theorem.

Computational libraries remain Mathlib-free, with correspondence theorems in
Mathlib companions where appropriate. Manual examples must be independently
written from mathematical definitions, public standards, openly licensed
data, or new synthetic inputs rather than adapted from proprietary manuals.

## Matrix and linear algebra

### Certified eigenpair enclosures

Run an untrusted numerical eigensolver and verify an approximate eigenpair
with interval arithmetic, using a fixed-point or contraction argument to
enclose a true eigenpair.

Scope the first version to simple isolated eigenpairs of symmetric matrices.
Multiple or defective eigenvalues, singular values, rectangular matrices,
phase conventions, pivoted QR, and interval inverse bounds should remain
separate extensions. The verified layer depends on `hex-interval-mathlib` and
the matrix correspondence API; `hex-char-poly`, `hex-roots`, and
`hex-number-field` provide independent spectral cross-checks and exact names
for algebraic eigenvalues.

The SPEC must choose an enclosure theorem whose hypotheses are executable to
check and decide how an untrusted solver supplies candidates. An in-Lean
floating-point implementation and an FFI solver are equivalent from the
trusted layer's point of view.

### Determinantal ideals and rank loci

[hex-determinantal-ideal](../HexDeterminantalIdeal/SPEC/hex-determinantal-ideal.md) specifies
executable minors of every size over any commutative ring, the generating
list of the determinantal ideal `I_r(A)`, and the theorem that a matrix over
a field has rank below `r` exactly when every `r × r` minor vanishes, with a
Mathlib-free proof through the row-reduced echelon certificate, Cauchy-Binet
and the Laplace expansion. Its companion
[hex-determinantal-ideal-mathlib](../HexDeterminantalIdealMathlib/SPEC/hex-determinantal-ideal-mathlib.md)
states the theorem for `Matrix.rank` under any ring homomorphism into a
field, so the locus where a polynomial matrix's rank drops below `r` is the
zero set of `I_r(A)`, and proves that `I_r(A)` is unchanged by invertible
row and column operations. Fitting ideals, whose presentation independence
is a theorem about modules rather than matrices, and Gröbner-basis questions
about `I_r(A)` (membership, radical, dimension) remain future work. The
pinned Mathlib has neither Fitting ideals nor a rank-versus-minors lemma.

### Sparse matrices

Add a canonical sparse representation alongside the dense matrix type, with
`toDense` as its specification function. The first SPEC should choose among a
coordinate builder, compressed sparse row storage, or a builder/frozen pair.
The representation invariant must exclude duplicate positions and stored
zeros and must support extensionality through `toDense`.

The initial operation set should include construction, lookup, addition,
scalar multiplication, transpose, sparse-by-sparse multiplication, and
sparse-by-dense products. Correctness is expressed by `toDense` commuting
with each operation. Benchmarks need a named consumer and input family where
dense storage is genuinely the constraint before the project commits to a
second matrix ecosystem.

Sparse elimination is a separate project. Fill-in makes a frozen CSR layout a
poor update structure and introduces pivot-order questions such as Markowitz
selection. It should follow the representation library and be compared with
black-box methods on the finite-field workloads that motivate it.

### Black-box linear algebra

Specify Wiedemann and block Wiedemann algorithms over finite fields, treating
a matrix as a linear map rather than stored entries. Intended operations are
solving `A x = b`, producing kernel vectors, and recovering Krylov minimal
polynomials for large sparse systems.

The trusted result checks a proposed solution or kernel vector with a single
matrix-vector product. Claims about rank, nullity, minimality, or exhaustive
kernel bases need additional certificates. The library should depend on the
generic finite-field interface and the minimal-polynomial vocabulary without
requiring the sparse-matrix representation.

## Discrete structures and optimization

### Graphs and networks

`hex-graph` should provide immutable simple directed and undirected graphs,
maps, subgraphs, and basic traversal. Vertices are canonical indices. An
optional bijection records external vertex names without making equality or
hashing depend on an arbitrary label type.
`hex-graph-shortest-path` should provide breadth-first search, Bellman-Ford,
and Dijkstra's algorithm. `hex-graph-network-flow` should provide Dinic's
maximum-flow algorithm. `hex-graph-matching` should provide Hopcroft-Karp
bipartite matching. `hex-graph-assignment` should provide the Hungarian
algorithm for weighted bipartite assignment. `hex-graph-spanning-tree` should
contain Kruskal minimum spanning forests, `hex-graph-planarity` should contain
Boyer-Myrvold planarity testing. Add Mathlib
companions where correspondence or abstract mathematical theorems require
them, rather than automatically creating one for every algorithm library.

The base representation should not depend on matrices or permutation groups.
All the graph algorithms above depend on `hex-graph`. The Hungarian algorithm
uses the base bipartite representation but does not depend on Hopcroft-Karp.

The initial representation uses sorted duplicate-free adjacency arrays. An
edge-list builder checks bounds, removes duplicate edges, and freezes to that
representation. Vertex data and edge weights, capacities, costs, or colours
are separate typed maps indexed by the graph, rather than untyped properties
stored inside it. Directed and undirected graphs are different types. Loops
and parallel edges require later pseudograph and multigraph types because
degree, incidence, planarity, and flow statements change in their presence.
Conversions from edge lists and adjacency matrices prove equality of the
represented edge relation. Dense bit matrices may be private execution data
for canonical labelling, but `hex-graph` should not introduce a storage-backend
typeclass before another public representation is needed.

The representation theorems prove that adjacency lookup, edge iteration,
transpose, induced subgraphs, and graph maps agree with the corresponding
finite relations. Breadth-first search proves that each reported level is the
minimum number of edges from the source. Dijkstra proves that each reported
distance is the minimum path weight under an explicit nonnegativity
hypothesis. Bellman-Ford returns either shortest distances and predecessor
paths for all vertices reachable from the source, or a reachable negative
cycle. Its completeness theorem proves that the cycle case occurs exactly
when no finite shortest-distance labelling exists. Tarjan's strongly connected
component algorithm is also in `hex-graph`. Its result partitions the
vertices, and two vertices occur in the same component exactly when each is
reachable from the other. Kahn's topological-sort decision returns either an
ordering in which every edge goes forward or a directed cycle. The
completeness theorem proves that the second case is returned exactly when no
topological ordering exists.

A maximum-flow result contains a feasible flow and a cut. The checker proves
capacity bounds, flow conservation, equality of flow value and cut capacity,
and hence maximality by weak duality. A maximum bipartite matching result
contains a matching and a vertex cover of the same cardinality. The checker
proves maximality by weak duality. Hopcroft-Karp correctness proves that its
alternating-path construction always supplies such a cover, which is the
algorithmic content of Kőnig's theorem. The Hungarian assignment result
contains a perfect matching and feasible row and column potentials with equal
primal and dual objective values. This proves optimality for integral or
rational costs. A rectangular instance is handled by explicit dummy vertices
and proves the corresponding partial-assignment statement. Kruskal returns a
minimum spanning forest together with the accepted-edge order and component
partition. Correctness proves that each component tree spans exactly one input
component and has minimum total weight by the cut-and-exchange argument,
including tied weights.
A spanning-tree operation returns `none` precisely when the graph is
disconnected.

General matching remains a later extension of `hex-graph-matching`. It should
use Edmonds' blossom algorithm and return a matching together with a
Tutte-Berge witness whose odd-component count gives the same upper bound.
The checker proves optimality from that equality, and the completeness theorem
proves that the algorithm always constructs such a witness.

After maximum flow, `hex-graph-network-flow` can add minimum-cost
transshipment for integral lower and upper capacities, costs, and vertex
balances. A fixed-value source-to-sink flow is the special case with opposite
balances at its endpoints. Eliminate lower bounds by adjusting the balances,
then add an auxiliary source and sink to reduce feasibility to maximum flow.
A negative answer contains the auxiliary cut witnessing that some required
balance cannot be met.

For a feasible instance, replace each negative-cost edge by its reversed
slack variable, folding the saturated original edge into the balances. All
transformed costs are then nonnegative. Use successive shortest augmenting
paths with Dijkstra and maintain nonnegative reduced costs by updating vertex
potentials. A result contains the feasible flow and vertex potentials proving
that every residual edge has nonnegative reduced cost. The companion proves
that absence of a negative residual cycle is equivalent to minimum cost among
flows with those balances. Equality of optimal-flow results is equality of
their edge flows. Potentials are noncanonical optimality witnesses.

Define planarity by the existence of an orientable genus-zero rotation system.
A positive result contains such a rotation system and its complete face
traversal. The checker proves the dart incidences and the Euler characteristic
`V - E + F = 2` separately
for every connected component containing an edge. Thus each induced
orientable cellular embedding has genus zero. Isolated vertices are added in
faces afterward. A negative result contains subdivisions of `K_5` or `K_3,3`.
The companion proves that these two graphs are not planar and that subdivision
preserves nonplanarity, connecting the obstruction to the same definition.
The Boyer-Myrvold implementation must prove that it returns one of these two
certificates for every finite input. Canonical labelling must prove the full
biconditional: two finite graphs have equal canonical forms exactly when they
are isomorphic. Checking a proposed relabelling proves only the forward
isomorphism claim.

Canonical labelling and complete automorphism generators are covered by
[hex-graph-iso](../HexGraphIso/SPEC/hex-graph-iso.md) and
[hex-graph-iso-mathlib](../HexGraphIsoMathlib/SPEC/hex-graph-iso-mathlib.md).
Explicit isomorphism cosets remain a further extension: return one
transporter and the source automorphism group, and prove that every
isomorphism is uniquely the transporter composed with an automorphism.
A request for an explicit list expands that coset only under a
caller-supplied cardinality budget.

The first graph chapter should analyse a data pipeline containing one
accidental dependency cycle, then return both its strongly connected
components and a valid order after that cycle is removed. A shortest-path
example should route a maintenance cart through a small warehouse map with
nonnegative traversal times. A maximum-flow example should model four rooms,
two exits, and capacity-limited corridors, returning an evacuation flow and a
cut of equal capacity. For assignment, match inspectors to machine
inspections using costs derived from travel time and qualifications, then
check the matching against the Hungarian row and column potentials.

A minimum-cost-flow tutorial should route weekly supplies from depots to
clinics with integral demands, route capacities, and per-crate costs. It should
check the result using residual vertex potentials and contrast it with a more
expensive feasible flow. A planarity chapter should construct a sensor
interconnect, verify its rotation system, then add specified links that
produce a `K_3,3` subdivision returned by the negative certificate.

## Polynomial computation

### Swappable polynomial representations (deferred)

Do not introduce a `PolyOps` or `LawfulPolyOps` abstraction solely because
dense and sparse polynomials both exist. Their useful operations, complexity,
and normalization behaviour differ, and gcd or division of sparse inputs
usually becomes dense. Keep explicit conversions until several real consumers
show which operations a common interface must support.

### Positive-characteristic multivariate squarefree decomposition

Amend `hex-mv-gcd` with squarefree decomposition over perfect fields of
positive characteristic. The characteristic-zero Yun recursion is
insufficient because every formal derivative may vanish. The replacement
needs multi-derivative splitting, detection of `p`-th powers, coefficient
`p`-th roots supplied by the finite-field interface, and a recursion whose
measure accounts for the degree drop after extracting a `p`-th root.

The SPEC must state whether it supports arbitrary perfect fields or only the
project's finite-field instances and must distinguish squarefree factor
decomposition from irreducible factorization.

### Gröbner bases

A Hex Gröbner engine is justified only at the performance of the open-source
industrial engines. Lean's `grind` already contains a Gröbner-basis-based
commutative-ring solver for small ideal-membership goals, exposed as the
`grobner` tactic, and `linear_combination` checks any externally produced
cofactor certificate (`polyrith`'s external service has been shut down), so a
Buchberger implementation with pair criteria adds nothing that is not already
available. The sources to
follow are msolve (F4 over prime fields with a tracer and multi-modular
reconstruction over `ℚ`, plus a signature-based variant), giac's modular F4,
Singular's `std`, `slimgb`, and `sba`, GBLA for the specialized F4 linear
algebra, and the Eder–Faugère survey of signature-based algorithms.

That engine needs its own substrate: packed-exponent sparse polynomials over
word-size prime fields, Macaulay-matrix construction with hybrid sparse and
dense row reduction over `𝔽ₚ`, and a tracer-driven multi-modular lift.
`hex-mv-poly`'s tree-map representation remains the certificate and kernel
form, not the engine. Applications include ideal membership, intersection,
quotient, elimination, implicitization, and radical membership through the
Rabinowitsch trick.

Ideal membership has a compact trusted boundary: return cofactors witnessing
`p = sum_i h_i * g_i`, an identity `hex-kronecker` and `hex-reflect` already
check in the kernel. Non-membership requires more. A nonzero remainder is
conclusive only after the divisor set is certified to be a Gröbner basis and
connected to the original generators: two-way cofactor identities, a
reduction-to-zero trace for every S-pair, and the Buchberger criterion proved
once. The pinned Mathlib has the multivariate division algorithm with respect
to a monomial order and not the criterion. Treat positive and negative
decisions as separate certificate types with separate budgets.

The computational layer depends on `hex-mv-poly` for the certificate form;
coefficient-domain hypotheses and monomial order must be explicit.
Zero-dimensional solving and root reconstruction are downstream work rather
than part of the first basis library.

### Boolean polynomial systems

Build a specialized Boolean polynomial representation rather than treating
the equations `x_i^2 = x_i` as ordinary generators that every operation must
carry. `hex-boolean-poly` should store a monomial as a bit set and a polynomial
in algebraic normal form as a canonical set of monomials, with addition by
symmetric difference and multiplication by union followed by cancellation.
It provides evaluation, substitution, restriction of variables, derivatives,
and the fast Möbius transform between algebraic normal form and truth tables.
Its dependencies are `hex-basic`, `hex-gf2`, and the fixed-arity vocabulary of
`hex-mv-poly`, but it remains a distinct representation.

The computational correctness theorem identifies each stored polynomial with
its function `(Fin n -> Bool) -> Bool`. It proves that normalization preserves
evaluation and that addition, multiplication, substitution, and the Möbius
transform agree with Boolean function operations. `hex-boolean-poly-mathlib`
identifies this type with the quotient of `MvPolynomial (Fin n) (ZMod 2)` by
the ideal generated by `X i ^ 2 - X i`, and proves that evaluation gives an
equivalence between that finite quotient and all Boolean-valued functions on
`n` bits. This equivalence supplies extensional equality instead of relying
on testing a sample of assignments.

`hex-boolean-groebner` should follow the generic Gröbner-basis library. It
implements Boolean F4: symbolic preprocessing constructs Boolean Macaulay
matrices, packed `GF(2)` row reduction produces new reducers, and the usual
F4 selection loop continues until the checked S-pair criterion holds. The
checker expands every Boolean reduction by the field polynomials
`X i ^ 2 - X i` and applies the generic Buchberger criterion to the augmented
ideal, so optimized search does not enlarge the trusted surface.
`hex-boolean-solve` then converts a zero-dimensional basis to
lexicographic order with FGLM and enumerates the resulting triangular system.
Its result theorem states that the returned assignments are pairwise distinct
and are exactly the common zeros. An empty answer needs either the certified
identity `1` in the ideal or the completeness theorem for the enumeration.

The first manual chapter should prove equivalence of two independently
written parity-control circuits by reducing the XOR of their outputs. A
tutorial can recover the unknown inputs of a new four-bit substitution box
from algebraic input/output constraints, with a second deliberately
ambiguous trace that returns every consistent key. A hardware-diagnosis
example can find all stuck-at faults consistent with a small collection of
observations.

### Ideal invariants, syzygies, and decomposition

`hex-monomial-ideal` should store the divisibility antichain of minimal
monomial generators. It provides membership, sum, intersection, quotient,
radical, standard-monomial enumeration by degree, and recursive irreducible
decomposition. Normalization proves equality with the generated monomial
ideal, and every operation proves the corresponding membership biconditional.
`hex-hilbert` and `hex-ideal-decomp` both depend on this library rather than
implementing separate traversals of leading ideals.

`hex-hilbert` should compute Hilbert functions, Hilbert series, Hilbert
polynomials, dimension, and degree from a leading monomial ideal. The initial
grading assigns a positive integer weight to each variable. Recursive
standard-monomial decomposition with memoization computes the series
numerator. Finite differences compute the eventual polynomial in the standard
grading. The executable theorem proves that each series coefficient counts
precisely the standard monomials of that weighted degree and that the
denominator is the product of `1 - t ^ w_i`. `hex-hilbert-mathlib` identifies
that count with the dimension of the corresponding graded quotient component
and proves the dimension and degree interpretations. Gradings by a free
abelian group require a later multivariate-series representation.

`hex-syzygy` should own finite graded free modules, homogeneous module maps,
submodules by generators, and subquotient presentations. Polynomial ideals
enter this API as submodules of a rank-one free module, and quotient rings as
cyclic presentations. This permits Hilbert functions, syzygies, and
resolutions to share one representation without making the first primary-
decomposition implementation operate on arbitrary modules.

`hex-syzygy` should implement Schreyer's algorithm. Starting with a checked
Gröbner basis, it records the relations obtained by reducing every
S-polynomial to zero. Schreyer's theorem proves that these relations already
form a Gröbner basis of the first syzygy module in the Schreyer order.
Iteration gives a finite free resolution when the coefficient domain and
grading support the required termination theorem. Correctness proves that
every emitted column lies in the kernel of the presentation map and that those
columns generate the whole
kernel. The Mathlib companion identifies the executable kernel and image
with submodules and proves exactness at every reported position. A
minimization pass performs homogeneous basis changes and cancels a summand
whenever a differential contains an invertible constant entry. It proves that
homogeneous basis changes identify the original complex with the direct sum
of the smaller complex and a contractible two-term complex. The final
differentials have entries in the irrelevant ideal. Betti numbers and
Castelnuovo-Mumford regularity are computed only from this checked minimal
resolution.

These libraries depend on the planned `hex-groebner` and `hex-mv-poly`.
`hex-syzygy` additionally uses `hex-row-reduce` for coefficient-space
calculations. `hex-ideal-decomp` adds multivariate factorization, resultants,
and exact finite-field or rational coefficient operations.

`hex-ideal-decomp` should first decompose monomial ideals. Recursive
irreducible decomposition returns an intersection of ideals generated by pure
powers. Components with the same radical are then intersected. Termination is
combinatorial, and the result supplies a complete primary decomposition.

For general ideals over `Q` and finite fields, implement both the
Gianni-Trager-Zacharias and Shimoyama-Yokoyama algorithms. They may share
localization, saturation, ideal quotient, elimination, and factorization
operations, but remain separately selectable search procedures because their
termination and performance differ by coefficient field and input. Each
successful result is a list of pairs `(Q_i, P_i)`, where `Q_i` is primary and
`P_i` is its checked prime radical. A budgeted strategy may return `unknown`.
A total operation claiming that every input returns a decomposition requires
a termination proof for its chosen domain and strategy.

A certified result proves that the intersection of the `Q_i` is the input
ideal, each `P_i` is prime, each `Q_i` is `P_i`-primary, the associated primes
are distinct, and the decomposition is irredundant. Minimal associated primes
are identified separately from embedded ones. Embedded primary components are
not canonical, so equality of two certified result records must not be part
of the public theorem. A primality certificate for `P_i` chooses a maximal
independent set and constructs a homomorphism from the polynomial ring into a
checked iterated algebraic extension of the corresponding rational-function
field. Elimination proves that the homomorphism's kernel is exactly `P_i`, so
the quotient embeds into a field and is a domain. Candidate generation may
use an external system, but all ideal equalities, radical claims,
primality claims, and primary claims are replayed in Lean.

Manual examples should be driven by applications rather than by standard
benchmark families. One chapter can compute the Hilbert series of a small
graded model for constrained polynomial features. Another
can derive the syzygies among redundant calibration equations. A tutorial can
decompose the steady-state ideal of a new two-reaction network and explain
which components correspond to boundary and non-boundary states. A small
planar linkage can demonstrate how ideal dimension distinguishes isolated
configurations from a one-parameter motion.

### Rational-expression tactics

Specify three related but separable operations:

- `Together`: combine ring operations and division into one quotient. This
  needs common-denominator arithmetic but no gcd.
- `cancel`: reduce a quotient to lowest terms. The multivariate form depends
  on `hex-mv-gcd`.
- `Apart`: partial fractions. The univariate rational form can use existing
  factorization and polynomial extended gcd; multivariate variants require
  substantially more machinery.

Denominator nonvanishing cannot be inferred for free indeterminates. Tactics
should emit explicit side goals, following `field_simp`, and term-level APIs
should return both the normalized expression and the hypotheses under which
it equals the input.

The univariate fraction representation and arithmetic are specified in
[hex-rational-fn](../HexRationalFn/SPEC/hex-rational-fn.md). Its normalization removes
removable singularities, so an expression tactic must retain the original
denominator conditions separately.

### Holonomic functions

Extend [hex-summation](Libraries/hex-summation.md) with closure operations for
sequences and functions satisfying linear recurrences or differential
equations with polynomial coefficients. Candidate operations include sum,
product, specialization, definite summation, differentiation, and integration,
with executable recurrence certificates for each closure step.

The first SPEC should choose either the recurrence or differential-equation
side and define normalization, initial-value obligations, singular indices,
and equality from a shared operator. It should reuse summation's certificate
checker rather than enlarge the trusted surface of its search algorithms.

## Codes and finite sequences

### Linear error-correcting codes

`hex-linear-code` should represent a code over a lawful finite field by the
canonical reduced row basis of its generator space. It provides construction
from generator and parity-check matrices, encoding, membership, syndromes,
duals, sums, intersections, direct sums, puncturing, shortening, extension,
and coordinate permutations. Minimum distance is an exact but potentially
exponential operation using information-set enumeration. A budgeted search
may return upper and lower bounds, but may not label an upper bound as the
minimum.

The base correctness theorem says that canonicalization preserves the row
span and that two representations are equal exactly when their codeword sets
are equal. Encoding is linear, lands in the code, and is injective for the
stored full-row-rank basis. A word has zero syndrome exactly when it is a
codeword. The computed dual is precisely the orthogonal complement, and each
code transformation has the expected image or preimage description.
`hex-linear-code-mathlib` identifies the executable code with a finite
dimensional submodule of `Fin n -> K`, its dimension with module rank, and its
dual with the Mathlib orthogonal submodule. An exact distance result proves
both that the reported word has that weight and that no nonzero codeword has
smaller weight.

The exact distance implementation should use the Brouwer-Zimmermann algorithm
rather than a single generator-basis enumeration. It constructs systematic
generator matrices from several disjoint information sets, enumerates
information vectors by increasing weight, and maintains an upper bound from
the lightest word found and a lower bound for every unvisited word. Correctness
proves the lower bound from the information-set cover and reports a minimum
only when the bounds meet. Complete enumeration also produces the Hamming
weight enumerator. `hex-linear-code-mathlib` proves the MacWilliams identity
between the checked enumerators of a code and its dual, providing an
independent check on dualization and distance.

A Reed-Solomon, BCH, Goppa, punctured, or extended code should retain its
construction data and provide a proved conversion to `hex-linear-code`.
Reducing every family immediately to a generator matrix discards the
evaluation points, defining roots, Goppa polynomial, decoder radius, and
other hypotheses needed by its algorithms. A derived construction preserves
this data when it has a theorem transporting it. Otherwise its result is an
ordinary linear code.

Encoding is not part of code equality. An encoder records a message space, a
linear bijection onto the code, and its inverse on codewords. The row-basis
encoder is available for every linear code, while polynomial evaluation and
cyclic systematic encoders belong to their family libraries. A decoder always
names its input space, target code, metric, promised radius or agreement
threshold, and connected encoder when it returns messages. Do not replace
these contracts with informal decoder labels. Unique bounded-distance,
complete list, and heuristic decoders have different result types and
different completeness theorems.

`hex-code-equivalence` depends on `hex-linear-code`, finite fields, and
permutation groups. It first handles monomial equivalence: row-basis change,
coordinate permutation, and multiplication of coordinates by nonzero field
elements. Use Feulner's partition-refinement algorithm on projective columns,
refined by incidences with a canonically selected set of low-weight codewords.
The result contains a canonical row space, a transporter from the input, and
generators for its full monomial automorphism group. Correctness proves that
two codes have equal canonical forms exactly when they are monomially
equivalent and that every stabilizing monomial transformation lies in the
returned group. Semilinear equivalence adds checked Frobenius actions only
after the monomial case is complete. Refinement may remove a search branch
only after an equivariant invariant proves that the branch cannot contain a
smaller representative.

`hex-linear-code` depends on `hex-matrix`, `hex-row-reduce`, and
`hex-finite-field`. `hex-cyclic-code` adds `hex-poly`. `hex-reed-solomon` adds
`hex-poly-fast`. `hex-bch` adds `hex-gfq`, `hex-cyclic-code`, and
`hex-linear-recurrence`.
`hex-goppa-code` adds `hex-gfq`, `hex-poly-fp`, and `hex-linear-code`.
`hex-ldpc` depends on the sparse-matrix representation. A small `hex-pauli`
library should own canonical phase-annotated finite Pauli operators,
multiplication, weight, and the binary symplectic encoding.
`hex-stabilizer-code` then depends on `hex-pauli` and the binary linear-code
operations.

`hex-cyclic-code` should represent a length-`n` cyclic code by a monic divisor
of `x^n - 1`. It implements generator and check polynomials, cyclic encoding,
syndrome computation, and conversion to and from a generator matrix. Its
correspondence theorem identifies cyclic shift with multiplication by `x` in
`K[x] / (x^n - 1)` and proves that the generated words are exactly the
multiples of the generator polynomial modulo `x^n - 1`.

The code-family libraries provide these decoders:

- `hex-reed-solomon` constructs generalized Reed-Solomon codes by evaluating
  degree-`< k` polynomials at distinct field points. It uses the fast
  multipoint operations from `hex-poly-fast`. Gao decoding interpolates the
  received word, applies half-GCD to the interpolation polynomial and the
  vanishing polynomial, and accepts only an exact message quotient satisfying
  the degree and agreement bounds. Correctness proves the MDS distance
  `n - k + 1`, proves successful decoding for at most
  `floor ((n - k) / 2)` errors, and proves uniqueness in that radius.
  A later Guruswami-Sudan decoder constructs a nonzero bivariate interpolation
  polynomial with the configured multiplicities, then uses Roth-Ruckenstein
  root finding to recover every degree-`< k` message polynomial meeting the
  agreement threshold. The checker verifies all interpolation conditions and
  every returned factor. Completeness proves that every message meeting the
  configured threshold occurs in the returned duplicate-free list. It is not
  inferred from checking the candidates that happened to be found.
- `hex-bch` constructs narrow-sense and offset BCH codes from the least common
  multiple of the minimal polynomials of consecutive powers of a primitive
  `n`-th root of unity, where `n` divides the multiplicative-group order of
  the extension field. Decoding uses syndrome evaluation, Berlekamp-Massey
  for the error locator, Chien search for locations, and Forney's formula for
  magnitudes.
  Correctness proves that every defining root annihilates every codeword, the
  BCH designed-distance bound, and recovery whenever the actual number of
  errors does not exceed the configured radius. The locator-root and
  magnitude statements are separate so repeated or missing roots cannot be
  hidden by a final syndrome check.
- `hex-goppa-code` constructs binary squarefree Goppa codes and implements
  Patterson decoding. The algorithm computes the syndrome inverse modulo the
  Goppa polynomial, the characteristic-two square root of that inverse plus
  `x`, the constrained extended-GCD solution, and the error-locator roots.
  Correctness proves the parity-check description, the lower bound `2t + 1`
  for a degree-`t` squarefree binary Goppa polynomial, and correction of every
  error pattern of weight at most `t`.

Unique decoders return a record containing the decoded word, error positions,
and a message only through their selected encoder. Every record checker proves
membership, reconstruction of the received word, and the radius bound. List
decoders return duplicate-free checked records together with a completeness
theorem for their agreement threshold. These checks establish soundness. The
family-specific theorems above establish that every correctable input actually
produces the promised result. A timeout or a failed algebraic precondition
returns `none`, never an arbitrary word.

`hex-ldpc` can later provide sparse parity-check matrices, regular and
irregular constructions, and sum-product and min-sum belief-propagation
decoders. These iterative decoders are heuristics. The library proves that
each message update implements the stated recurrence and that any accepted
word has zero syndrome. It makes no theorem that a failed iteration is
uncorrectable, that an accepted word is nearest, or that an ensemble reaches
a channel threshold. Exact small-code enumeration may provide independently
verified distance and decoding comparisons.

`hex-stabilizer-code` should represent stabilizer and CSS codes by independent,
phase-annotated Pauli generators and their binary symplectic matrix. The
checker proves pairwise commutation, independence, and exclusion of `-I` from
the generated subgroup. It proves that the encoded dimension is
`n` minus the generator rank and that exact distance enumeration finds the
minimum-weight element of the normalizer outside the stabilizer. Its Mathlib
companion states the corresponding finite-dimensional quantum code and proves
the error-correction condition for the reported radius. No analytic
noise-model claim belongs in the initial library.

The manual should begin with a new erasure-storage example that reconstructs
missing shards using a generalized Reed-Solomon code. Its erasure decoder uses
interpolation on the surviving evaluation points and proves reconstruction
when at least `k` distinct symbols remain. A later errors-and-erasures decoder
states and proves the unique-decoding bound `2 * errors + erasures <= n - k`.
A telemetry frame can then use BCH decoding to locate and repair a chosen
burst of flipped bits. A second chapter should compare an exact
minimum-distance result with a mere sampled upper bound. Tutorials can
construct a small binary Goppa code, verify one complete Patterson trace, and
show how the same finite-field and polynomial operations support a toy
code-based public-key experiment. The experiment must be labelled as
unsuitable for production and use freshly generated small parameters. A
stabilizer-code tutorial should derive its
syndrome table from the symplectic checks.

### Linear recurrences and finite-field sequences

`hex-linear-recurrence` should contain finite prefixes, normalized connection
polynomials, and streams generated by a recurrence over a field.
Berlekamp-Massey computes a least-degree connection polynomial for a finite
prefix. Bostan-Mori computes the term at a large index in
`O(M(k) log n)` field operations for recurrence order `k`. The quadratic
recurrence is useful as a small-input base case, not as the large-input
implementation. This library supplies the scalar recurrence solver required
by Wiedemann's algorithm without making black-box matrices depend on
cryptographic sequence types. Block Wiedemann additionally requires a later
matrix-sequence minimal-generator algorithm, such as matrix Berlekamp-Massey
or approximant-basis computation, with its own minimality theorem.
Its dependencies should be `hex-poly`, `hex-poly-fast`, and the lawful
finite-field interface. `hex-lfsr` sits above it and `hex-gf2`.
`hex-sequence-correlation` sits above `hex-lfsr` and the multiplication plans
whose root-of-unity hypotheses it can actually discharge.

Correctness of Berlekamp-Massey proves that the returned polynomial annihilates
the supplied prefix and that no lower-degree normalized polynomial does so.
It does not assert unconditional uniqueness, which can fail for a short
prefix. A separate theorem gives uniqueness when a sequence of linear
complexity `L` is observed for a sufficient prefix, including the usual
`2L` condition. Bostan-Mori proves that its coefficient extraction equals the
term obtained by iterating the recurrence.

`hex-lfsr` should provide Fibonacci and Galois LFSR state transitions,
jump-ahead by modular exponentiation of `x`, period computation, decimation,
and conversion between state and output conventions. Its theorems identify
the output stream with the associated connection polynomial, prove that
jump-ahead equals repeated stepping, and prove that a nonzero degree-`d` LFSR
has period `q^d - 1` when the characteristic polynomial is primitive. The
converse must include the nonzero-state and convention hypotheses.
`hex-sequence-correlation` should initially compute exact cyclic
auto-correlation and cross-correlation of binary sequences after the bipolar
map `0 |-> 1`, `1 |-> -1`, so values lie in `Int`. It uses direct evaluation
at small sizes and integer convolution at large sizes, with a theorem equating
both implementations to the defining finite sum. Character correlations for
general finite fields require an explicit additive character and exact
cyclotomic values and belong in a later extension.

The manual should recover a recurrence from a synthetic sensor stream, use
jump-ahead to divide a reproducible simulation into independent index ranges,
and compare the correlations of newly generated finite-field sequences. A
cryptanalysis tutorial may reconstruct a deliberately small LFSR from output
bits. It must state that linear complexity and correlation are measured
properties, not proofs that a generator is cryptographically secure.

## Cryptographic algebra

### Elliptic curves over finite fields

`hex-elliptic-curve` should first support short Weierstrass curves over fields
of characteristic other than `2` and `3`, with a checked nonzero discriminant.
It stores affine points for the public specification and uses Jacobian
coordinates for addition, doubling, and scalar multiplication.
Exceptional cases, including the point at infinity, inverse points, zero
coordinates, and incomplete addition formulas, must be handled explicitly.
General Weierstrass equations and optimized binary curves require different
formulas and characteristic hypotheses and are excluded from the initial
library.

The base library depends on `hex-finite-field`, `hex-poly`, and `hex-arith`.
`hex-ec-finite-field` adds `hex-gfq` and `hex-int-factor`.
`hex-ec-point-count` adds polynomial factorization and `hex-modular`.
`hex-isogeny` and `hex-ec-pairing` depend on curve arithmetic but not on point
counting. `hex-ec-params` depends on curve arithmetic, point counting, and
integer primality. `hex-ec-crypto` depends on checked parameters, not on
isogenies or pairings.

The computational library proves that every constructor and operation returns
a point on the curve, that Jacobian normalization preserves the represented
affine point, and that the executable formulas agree with affine chord-and-
tangent addition in every exceptional case. Double-and-add, fixed-window
scalar multiplication, and a Montgomery-ladder schedule each prove that the
result is the mathematical multiple `n P`. Equality of schedules is a
functional theorem only. It is not a constant-time or side-channel theorem.
`hex-elliptic-curve-mathlib` identifies the executable curve and points with
Mathlib's nonsingular Weierstrass cubic, transports the abelian group law, and
proves that the executable scalar operation agrees with `nsmul` and `zsmul`.

`hex-ec-finite-field` should provide complete enumeration for small fields,
random-point generation by checked square-root extraction, point order,
subgroup membership, quadratic twists, and the finite abelian group structure.
Enumeration proves that the returned list is duplicate-free and contains
exactly all rational points. Point-order results include a factorization of
the candidate order and the usual prime-divisor tests, so minimality follows
rather than merely `n P = 0`. The first group-structure algorithm uses the
enumerated group table, deterministic subgroup generation, and exact point
orders to construct generators of invariant factors `Z/m x Z/n`. Its checker
proves the generator orders, `m` divides `n`, injectivity of the product map,
and equality of its cardinality with the enumerated curve. Faster relation-
matrix and Smith-normal-form methods can follow without changing this result
type.

`hex-ec-point-count` should implement Schoof's algorithm first and the
Schoof-Elkies-Atkin refinement second. For each auxiliary prime `ell`, the
certificate records the division-polynomial computation and the resulting
Frobenius trace constraint modulo `ell`. An Elkies step additionally records a
checked modular-polynomial root and kernel polynomial and yields a single
residue. An Atkin step records the modular-polynomial factorization pattern
and the resulting finite set of possible residues. Its checker proves that
the true trace residue belongs to that set. Exhaustive CRT matching combines
these sets and discards a candidate only through a proved-incompatible
congruence or the Hasse interval.

The companion must first prove that finite-field Frobenius satisfies its
quadratic characteristic equation, that `curveCardinality = q + 1 - trace`,
and the Hasse bound on the trace. These theorems connect the checked torsion
calculations to point counting. Reconstruction proves that exactly one integer
in the Hasse interval satisfies all accumulated residue constraints. A product
of moduli or collection of Atkin constraints that leaves several candidates
yields an incomplete result, not a guessed count. Untrusted polynomial
factorization or an external point counter may propose a certificate, but
native Schoof remains the fallback.

`hex-isogeny` should implement separable isogenies from finite kernels using
Vélu's formulas, dual isogenies for supported degrees, composition, and
Frobenius. Correctness proves that the rational functions map the source curve
to the target, preserve the point at infinity and addition, have the claimed
kernel and degree, and compose as reported. `hex-ec-pairing` should implement
Miller's algorithm for Weil and reduced Tate pairings. Its companion proves
agreement with the divisor definition, bilinearity, alternation where
applicable, and nondegeneracy under the exact torsion and root-of-unity
hypotheses. A successful final exponentiation alone does not prove these
properties.

`hex-ec-params` should store versioned named parameter sets separately from
curve arithmetic. A parameter record contains the field, curve coefficients,
base point, subgroup order, cofactor, encoding identifier, and source
provenance. Loading it checks field and subgroup primality, nonsingularity,
base-point membership, exact base-point order, and the equation
`curveCardinality = cofactor * subgroupOrder`. A name lookup returns only the
checked record. Adding a published parameter set requires conformance fixtures
from its public standard and does not make the standard file trusted.

`hex-ec-crypto` should provide standard point encoding with strict decoding
and subgroup checks, public-key validation, deterministic algebraic
test-vector generation, ECDH shared-point calculation, and ECDSA verification.
Theorems prove round-trip serialization,
rejection of noncanonical or off-curve encodings, subgroup membership of
accepted public keys, equality of the two honest ECDH computations, and the
usual ECDSA verification equation under its nonzero and range hypotheses.
Production signing, secret-dependent scalar multiplication, and claims of
protocol security remain out of scope until the repository has an explicit
side-channel and randomness policy.

The first manual chapter should derive the group table of a small curve chosen
for the chapter and check its cardinality both by enumeration and by a
point-count certificate. Tutorials should demonstrate invalid-point rejection
in a toy key agreement, verify an independently generated signature fixture,
construct a small-degree isogeny and check its kernel, and evaluate a pairing
identity on a different small curve. Public-standard test vectors may be added
as conformance fixtures with citations, but the explanatory examples and
Lean code must be written independently.

### Discrete logarithms

The finite-field library is specified in
[hex-discrete-log](Libraries/hex-discrete-log.md) and
[hex-discrete-log-mathlib](Libraries/hex-discrete-log-mathlib.md). It provides
complete baby-step giant-step, Pohlig-Hellman with certified order
factorization, and bounded Pollard rho. Exact base order, canonical
exponents, prepared tables and the distinction between nonmembership and
exhaustion are explicit contracts. The computational algorithms use a small
lawful commutative-group interface, with canonical finite-field adapters;
elliptic-curve adapters can follow without changing those proofs.

`hex-index-calculus` should target prime fields. It implements factor-base
selection, relation collection by smoothness testing, sparse
linear solving modulo prime-power factors of `p - 1`, and individual-log
descent. Every accepted relation is re-evaluated in the field. A solved factor
base table proves all recorded logarithm equations, and a descent certificate
proves the target factorization into that base. The final theorem is still the
simple equation `g^x = h`. Rank or uniqueness of the relation system is needed
only when the library claims a complete reusable log table. This library is a
named consumer for the planned sparse and black-box linear algebra.

The manual should audit a newly generated small Diffie-Hellman group: certify
the generator order, show how Pohlig-Hellman exploits a deliberately smooth
order, and contrast it with a large-prime subgroup. Another tutorial can
recover a shift between two finite-field recurrence streams and later repeat
the same generic call on a toy elliptic-curve subgroup. All parameters are
educational and newly generated. The text must not present these routines as
permission to attack systems or as evidence that a production parameter set
is secure.

## Number fields, curves, and groups

### Exact p-adic numbers

Add an inverse-limit or lazy exact `Z_p` and `Q_p` type above
[hex-padics](Libraries/hex-padics.md). Exact equality cannot be decided from a
finite approximation, so the API must distinguish observation at a requested
precision from mathematical equality. Arithmetic should refine precision on
demand and expose nontermination or undecidability honestly where zero-testing
is required.

Do not introduce a shared valued-approximation typeclass until both the
fixed-precision p-adic and truncated-series APIs have enough consumers to
identify a useful common contract.

### Ring of integers

Build the maximal order `O_K` of a number field, with an integral basis and
field discriminant, using a Round 2/Pohst-Zassenhaus-style algorithm. The
library depends on `hex-number-field`, `hex-number-field-tower`, and
`hex-int-factor` for the discriminant's squarefree part.

Factorization may run out of budget. The result type must distinguish a proved
maximal order from an order conditional on an incomplete factorization and
must retain the residual factorization data rather than silently asserting
maximality.

### Unit and class groups

Build the unit group, regulator, and ideal class group on top of the maximal
order. Relation collection produces checkable individual relations, but a set
of relations is not by itself a completeness proof for the relation lattice.

The SPEC must choose between unconditional enumeration bounded by Minkowski
with an explicit completeness certificate and conditional algorithms whose
hypotheses, including any GRH assumption used for factor-base sufficiency, are
present in the theorem statements. Unit completeness, regulator
certification, and class-group completeness are distinct obligations.

### Algebraic function fields and curves

The coefficient field `K(x)` is specified in
[hex-rational-fn](../HexRationalFn/SPEC/hex-rational-fn.md), with its correspondence to
Mathlib in [hex-rational-fn-mathlib](../HexRationalFnMathlib/SPEC/hex-rational-fn-mathlib.md).

`hex-function-field` should represent a finite separable extension of `K(x)`
by a monic irreducible polynomial in a second variable. Elements use the power
basis and reduction modulo the defining polynomial. Inversion uses polynomial
extended gcd over `K(x)`. Towers and nonsimple presentations are later
extensions. Trace and norm are computed from the trace and determinant of the
multiplication matrix. The minimal polynomial is obtained from the first exact
linear dependence among powers. The executable theorems prove the field laws
conditionally on the checked irreducibility and separability data, identify
the representation matrices, and prove these trace, norm, and minimal-
polynomial results. Embeddings and constant-field extensions are later
projects. `hex-function-field-mathlib` identifies the representation with the
corresponding simple field extension and proves its transcendence degree and
finite extension degree.
`hex-rational-fn` sits below `hex-function-field`, followed by
`hex-function-field-order`, then `hex-function-field-divisor`,
`hex-function-field-diff`, and `hex-riemann-roch`. `hex-plane-curve` uses the
field, order, divisor, Gröbner, and ideal-decomposition libraries.
`hex-hyperelliptic` uses the divisor interface but remains independent of
general plane-curve normalization.

`hex-function-field-order` should compute finite and infinite maximal orders
for global separable function fields over finite constants. Use a Round 2
integral-basis algorithm, local `p`-maximal enlargement, and Hermite reduction
of module bases. Correctness proves integrality of every basis element,
closure under multiplication, equality of the fraction field, and local
maximality at every prime considered. Global maximality additionally requires
a certified complete factorization of the discriminant. An unfinished
factorization returns an order with explicit unresolved primes, following the
same policy as the planned number-field maximal-order library.

`hex-function-field-divisor` should construct finite places from prime ideals
of a maximal order and infinite places from the transformed infinite order.
It implements valuations of elements and ideals, principal divisors, divisor
arithmetic, degree, support, and pullback and pushforward along checked finite
maps. Theorems prove the valuation laws, finite support, additivity of the
principal-divisor map, and degree zero of principal divisors over the exact
constant field. Equality of two divisor representations is coefficientwise,
while linear equivalence requires a function witnessing their difference.

`hex-function-field-diff` should represent Kähler differentials as `f dx`
relative to the chosen separating transcendence element. It computes the
different, the divisor of a differential, a canonical divisor, local residues,
and bases of spaces `Omega(D) = {w | div(w) >= D}`. Change of separating
element is accompanied by the checked derivative factor, so the represented
differential is independent of that choice. Correctness proves the residue and
valuation laws and that the reported canonical divisor is the divisor of a
nonzero differential.

`hex-riemann-roch` should implement Hess's ideal-arithmetic algorithm for the
space `L(D)`. It intersects the fractional ideals imposing the finite and
infinite valuation bounds and returns a reduced constant-field basis.
Correctness has two directions: every returned function satisfies
`div(f) + D >= 0`, and every function satisfying those inequalities is in the
span. `hex-riemann-roch-mathlib` identifies this executable space with the
divisor's Riemann-Roch space and proves the reported dimension. The general
Riemann-Roch dimension formula compares the checked bases of `L(D)` and
`Omega(D)`. Define the genus as `g = dim Omega(0)`, the dimension of regular
differentials. The formula then proves
`l(D) - dim Omega(D) = deg(D) + 1 - g`. It may discharge a dimension
calculation, but it cannot replace the explicit spanning proof for either
computed basis. The companion also derives that a canonical divisor has
degree `2g - 2`, rather than using that equality to define `g`. Residues then
support a later proof that evaluation and differential algebraic-geometric
codes are dual under the stated divisor and point-disjointness hypotheses.

`hex-plane-curve` should connect an integral affine or projective plane curve
to its normalized function field. It computes singular points from the
Jacobian ideal and performs normalization by Grauert-Remmert iteration. At
each step it computes the endomorphism ring of the chosen test ideal by ideal
quotients and adjoins a witnessed integral element until the endomorphism ring
equals the current algebra. It obtains geometric genus from the space of
regular differentials. Correctness proves every enlargement integral,
preserves the fraction field, and proves normality from the termination test.
A map of curves is accepted only with checked homogeneous coordinate degrees
and a proof that the defining equations vanish after substitution. The
companion proves agreement of the computed function field, local branches,
genus, and divisor maps with the corresponding algebraic curve.

`hex-hyperelliptic` should initially support smooth hyperelliptic curves whose
affine equation `y^2 + h(x)y = f(x)` has odd degree and whose smooth projective
model has one chosen rational place at infinity. Reduced Mumford pairs `(u,v)`
satisfy that `u` is monic, `u | f - h*v - v^2`, and
`degree v < degree u <= g`. Cantor composition and reduction preserve these
invariants and the represented degree-zero divisor class. Correctness also
proves that Cantor addition agrees with addition in the divisor class group.
Identity, inverse, associativity, and scalar multiplication follow through
that correspondence. Even-degree models and curves without a rational base
point require a different divisor representation. `hex-hyperelliptic` does
not expose a general Jacobian interface. General Jacobian arithmetic requires
the divisor representation and Riemann-Roch operations above.

Manual examples should construct a new quadratic function field, factor a
few finite places, and verify that a chosen principal divisor has degree zero.
A second chapter should compute `L(D)` twice, from the ideal algorithm and by
direct enumeration on a small field, and compare the complete bases. A
tutorial can perform Cantor arithmetic on a genus-two curve chosen for the
chapter. The coding manual can then construct a small algebraic-geometric
evaluation code from this Riemann-Roch basis, giving an application shared by
the two library families.

### Permutation groups

The initial library is specified in
[hex-perm-group](Libraries/hex-perm-group.md) and
[hex-perm-group-mathlib](Libraries/hex-perm-group-mathlib.md). It provides
checked deterministic stabilizer chains, constructive membership, exact
order, sign and cycle type, rank/unrank and supplied-index sampling,
finite actions with images and kernels, and complete set/subgroup search.
It includes block systems and primitivity, normal closure, core and derived
series, direct and imprimitive wreath products, and bounded element/coset
enumeration. It extracts the shared permutation representation from graph
isomorphism and proves completeness of checked chains and subgroup search.

Transitive-group data required by resolvent methods remain a later extension.
Classification tables need versioned provenance, checked embeddings and a
separate completeness policy. The initial computational library is useful
independently and supplies infrastructure for certified Galois-group work.

### Matrix groups and finite-dimensional modules

`hex-algebra-module` should represent a finite-dimensional module over a
finitely generated matrix algebra by the matrices giving the action of its
generators. The convention is a left action on column vectors. It provides the
spinning algorithm for the submodule generated by vectors, invariant-subspace
tests, sums, intersections, quotients, direct sums, and spaces of
homomorphisms. Homomorphisms are computed by solving all intertwining
equations `X A_i = B_i X` at once with `hex-row-reduce`. The linear dual is a
right module over the opposite algebra, not another left module with an
unstated action.

It depends on `hex-matrix`, `hex-row-reduce`, and `hex-char-poly`, and is
parameterized by an effective field. `hex-meataxe` adds `hex-finite-field` and
finite-field polynomial factorization.
`hex-matrix-group` depends on matrix arithmetic and the planned permutation
groups. `hex-group-module` depends on both `hex-algebra-module` and a group
representation with checked generator correspondence. `hex-character` comes
after group modules, matrix groups, and conjugacy classes and additionally
uses exact cyclotomic number-field arithmetic.

The base theorems prove that spinning returns exactly the least invariant
subspace containing the seeds, quotient action matrices are well-defined,
and each module construction has the stated universal or elementwise action.
For `Hom(U,V)`, every reported matrix intertwines every generator and every
intertwiner lies in the returned span. `hex-algebra-module-mathlib` identifies
these executable spaces with submodules, quotient modules, opposite-module
duals, and `LinearMap` spaces.

`hex-group-module` should pair generators of a finite group with invertible
action matrices and a checked homomorphism from that group. It provides the
contragredient dual through inverse transposes and the diagonal tensor action.
The first complete checker enumerates the finite group's canonical normal
forms, evaluates the proposed generator images, and checks multiplication on
every pair. Later checkers may use a proved-complete presentation or
stabilizer chain. Theorems prove that the dual and tensor constructions
respect multiplication and identify their underlying algebra modules. A list
of matrices with no correspondence to group elements remains an algebra
module and cannot be used to compute a group character.

`hex-meataxe` should implement MeatAxe decomposition over finite fields. It
factors characteristic and minimal polynomials of selected algebra elements,
spins kernels of the resulting primary factors, uses the dual module to detect
quotient structure, and recurses on any proper invariant subspace found.
Its principal fast irreducibility certificate is Norton's test. Choose an
algebra element `theta` and an irreducible factor `p` of its characteristic
polynomial such that `ker p(theta)` is nonzero and has dimension `degree p`.
Check that one nonzero vector in this kernel spins to the whole module and that
one nonzero vector in the transpose kernel spins to the whole transpose
module. The irreducibility theorem proves that these conditions exclude every
proper submodule. Random algebra elements may accelerate the search for such
a certificate, but failure of random trials proves nothing.

The proved-complete fallback enumerates one representative of every
one-dimensional subspace, spins each representative, and declares
irreducibility only when each nonzero seed generates the whole module. This is
exponential but exact. A later deterministic MeatAxe may replace the fallback
after its completeness theorem is available.

Correctness of the MeatAxe proves that a returned subspace is nonzero, proper,
and invariant, and that an `irreducible` answer means no such subspace exists.
A composition-series result proves that adjacent terms are invariant, the
series starts at zero and ends at the whole module, and every successive
quotient is irreducible. A direct-sum decomposition additionally supplies
inclusions and projections whose composites give the identity and whose
cross-composites vanish. `hex-meataxe-mathlib` identifies the executable
factors with simple quotient modules and proves a Jordan-Hölder multiset
statement. Absolute irreducibility is a separate decision after scalar
extension. It must not be inferred merely from irreducibility over the base
field.

`hex-matrix-group` should represent a finitely generated subgroup of
`GL(n,q)` and reuse the planned permutation-group algorithms through checked
actions. A group element is not a bare matrix: it records its parent group,
matrix value, and a straight-line word in the original generators. Group
operations evaluate and compose these words. A membership query accepts a
bare invertible matrix and returns such an element or a proved-negative
result.

The first faithful action is on the finite vector space itself. It is not the
scalable choice, but it gives a complete implementation for small `q^n`.
Membership checks the returned word against the target matrix. Order and
subgroup claims are transported from the faithful permutation action. Later
implementations can use actions on projective points or subspaces, with an
explicit kernel calculation so that lost scalar matrices do not invalidate
membership or order.

Constructive recognition of classical groups, conjugacy classes, maximal
subgroups, and character tables should remain separate projects. They require
classification data and much larger correctness arguments. If a database of
standard groups or representations is imported, each entry needs versioned
provenance and executable checks of its generators and claimed relations.
`hex-character` can begin only after conjugacy classes are available. Its
first algorithm should compute ordinary characters afforded by explicit
modules over a checked characteristic-zero splitting field and decompose them
using the checked class inner product. Finite-field modules enter this API only
through a checked lift of their eigenvalue roots to characteristic-zero roots
of unity, under the hypothesis that the field characteristic is coprime to the
group order. When the characteristic divides the group order, Brauer
characters and decomposition matrices are a separate project. Completeness of
an irreducible ordinary-character table requires orthogonality, degree-sum,
and class-count arguments, not only pairwise orthogonality of the rows found.

The first manual should decompose a cyclic-shift action on a finite signal
space, compute all intertwiners between two small modules, and
check the direct-sum maps. A matrix-group tutorial can certify the order and
membership of a small generated group by its faithful vector action, then
show why the projective action needs a scalar-kernel correction. A coding
chapter can use module decomposition to explain a symmetry of a small linear
code.

### Galois groups

Compute the Galois group of an irreducible polynomial over `Q` as a
permutation group on its roots, using Stauduhar-style resolvent descent.
Dependencies include permutation groups, `hex-roots`, `hex-resultant`,
univariate factorization, and `hex-number-field-tower`.

Subgroup containment can be witnessed by an invariant polynomial in the roots
taking a rational value. Full group identification additionally needs exact
stabilizer data, a fixed root labelling, separation of distinct coset
resolvent values, and certified non-containment at rejected branches.

## Lattices and real algebra

### Ordered real algebraic numbers

[hex-real-algebraic](Libraries/hex-real-algebraic.md) implements the real subtype
of canonical `AlgebraicNumber`, with exact comparison, field arithmetic,
square roots, ordered polynomial real roots, floor and ceil, rational
recognition, and dyadic approximation. Its companion supplies the ordered-field
structure, the order embedding into `ℝ`, and `IsRealClosed`. The design reuses
`hex-number-field` and fixes `realCompare` as the comparison semantics. It also
uses Mathlib-free core instances parameterized by a law package proved in the
companion. Root completeness, multiplicities, strict ordering, and representation
round trips are proved in the companion.
Companion proofs do not become computational dependencies. The number-field
layer also provides tag-based conjugation, the complex partial order, principal
complex radicals, common-field coordinate recovery, and `IsAlgClosure ℚ`
in the companion. Typed real and imaginary projections belong to the real
library, keeping this dependency graph acyclic. These APIs are covered in the
manual's number-field and real-algebraic chapters.

Stored-interval comparison and bounded refinement fast paths are specified in
the number-field library. General comparison of lazy roots and
Tarski queries remain separate extensions behind the same order contract.
An unconditional Mathlib-free law witness additionally needs proof
infrastructure for exactification, canonical equality, and root separation.
Exact value ordering of the real prefix of `ZPoly.algebraicRoots` remains
a separate improvement: exactification reselects stored
representatives at each minimal polynomial's precision before sorting their
centres, and no value-sortedness theorem establishes that cross-factor order.
The new real-root API explicitly sorts with `realCompare`.
This library provides exact real values for later sign determination and
algebraic sample points without depending on a quantifier-elimination tactic.

### Real closures of ordered fields

This family extends exact real computation to the real closure of
`ℚ(τ₁,…,τₘ)(ε₁,…,εₙ)`, with computable real constants `τᵢ` and successive
positive infinitesimals `εᵢ`. Its design follows [de Moura–Passmore, CADE
2013](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf) and is tracked by
[#10143](https://github.com/kim-em/hex-dev/issues/10143). The family section
fixes shared contracts; the directives below write the individual SPECs. It
does not register or implement these libraries.

#### Existing components and library boundaries

[hex-rational-fn](../HexRationalFn/SPEC/hex-rational-fn.md) already represents
`K(X)` by coprime `DensePoly K` numerators and monic denominators, over
`Lean.Grind.Field` with decidable equality. `HexPoly.Field` supplies division,
gcd and extended gcd. Generic characteristic-zero Yun decomposition over
`DensePoly K` is missing; `hex-real-closure` owns its specification, including
multiplicities over lawful exact coefficient fields.
[hex-real-roots](../HexRealRoots/SPEC/hex-real-roots.md#tarski-queries) owns
integer Sturm chains and the specified, not yet implemented,
`ZPoly.tarskiQuery` and `TarskiReplay`. Its ordinary root counts and
`hex-rcf`'s derivative-seeded `SturmReplay` cannot certify general Tarski
queries. Transcendental sign refinement consumes a caller-supplied approximation
procedure. `hex-ordered-fn` owns the small exact finite-bound representation and
arithmetic needed for polynomial evaluation; it has no dependency on
`hex-interval` or its companion. An adapter to another enclosure library is
separate future work, not a prerequisite or deliverable of this family.

[hex-number-field](../HexNumberField/SPEC/hex-number-field.md) specifies
fixed-field Tarski and approximation comparisons and fixed-embedding
`NumberTower` signs. Neither its irreducible, complex-embedded towers nor
`SimpleRealRoot`'s rational separation bounds model infinitesimals.
[hex-real-algebraic](Libraries/hex-real-algebraic.md) remains the independent
fast path over `ℚ`; this family must agree with its `realCompare` and
`RealAlgebraicPoly.roots` rather than changing their semantics.

Keep four computational libraries and four companions. Sturm queries have
consumers needing no BKR matrix machinery, so `hex-sturm` and `hex-sign-det`
remain separate. The two rational-function orders share their representation
and arithmetic, so they stay in `hex-ordered-fn`, in separate modules.

| Mathlib-free library | Responsibility | Mathlib companion |
| --- | --- | --- |
| [hex-sturm](Libraries/hex-sturm.md) | Ordered-field query frontend, coefficient-operation adapters, generic endpoints and root counts | `hex-sturm-mathlib`: frontend correspondence and replay composition |
| [hex-sign-det](Libraries/hex-sign-det.md) | BKR sign determination, complete sign tables, Thom root identity and comparison | [hex-sign-det-mathlib](Libraries/hex-sign-det-mathlib.md): sign-table correctness, Thom identity and order correspondence |
| [hex-ordered-fn](Libraries/hex-ordered-fn.md) | Transcendental and infinitesimal orders on `RationalFn`, approximation protocol | [hex-ordered-fn-mathlib](Libraries/hex-ordered-fn-mathlib.md): order laws, real evaluation and infinitesimal model |
| [hex-real-closure](Libraries/hex-real-closure.md) | Algebraic extension arithmetic, dynamic splitting, root isolation, staged towers and exploration | [hex-real-closure-mathlib](Libraries/hex-real-closure-mathlib.md): selected-root semantics, field laws, root completeness and trivial-tower agreement |

Arrows point from dependencies to consumers. Additional direct imports must
respect this graph, including the existing transitive dependencies of each
input library:

```text
hex-poly ──────────> hex-real-roots ──> hex-sturm ──> hex-sign-det
    │                                      │               │
    └─> hex-rational-fn ──> hex-ordered-fn   │               │
                                  │        │               │
                                  └────────┴───────────────> hex-real-closure
hex-real-algebraic ────────────────────────────────────────> hex-real-closure
```

The additional matrix inputs to hex-sign-det are hex-matrix, hex-row-reduce
and hex-rank; their companions supply the corresponding linear-algebra
results. These existing inputs do not depend on the real-closure family.

Each companion imports its computational library and the companions of the
computational dependencies it uses, plus Mathlib. Only companions may import
Tau Ceti. There is no reverse dependency from `hex-poly`, `hex-rational-fn`,
`hex-real-roots` or `hex-real-algebraic` into this family. Neither
`hex-interval` nor `hex-interval-mathlib` is an input to this family.
CAD, coverings and tactic integration are downstream clients, never imports of
these computational libraries. Reuse existing total `DensePoly` and
`RationalFn` arithmetic over canonical prealgebraic fields. Algebraic
coefficients use the [shared execution contract](real-closure-execution.md):
canonical-zero representations and ordinary total operations reuse `DensePoly`;
companions prove their noninjective interpretation and semantic field laws.
Ordinary ordered-domain pseudo-division is the missing lower arithmetic.

#### Execution policy and implementation boundary

The [shared execution contract](real-closure-execution.md) fixes ordinary
operation instances including natural casts, an explicit total sign, unique
stored zero, and semantic polynomial equality through zero differences.
For monic clean algebraic definitions retain the remainder already computed
during zero testing; general non-monic definitions retain raw representatives.
A checked irreducibility fact permits a remainder-only fast path but is never
a requirement to factor every defining polynomial. Batch only inside justified
ring-operation buffers; leading-zero tests in division remain mandatory.

Persistent refinement creates a new immutable context and transports the
requested dependency closure in predecessor order: later polynomials,
endpoints, selected roots, values and evidence. Old contexts stay valid.
Reject stale context bindings in the new context, including unchanged
operand literals, unless explicit checked transport or recomputation is supplied.

Experiments provide design evidence; the owning SPECs define APIs, proof
hypotheses and acceptance criteria; production implementation follows those
revised contracts. The initial rational selected-root arithmetic/sign and
transport slice uses existing ℝ Sturm results, with no reverse import from
hex-real-algebraic. It does not discharge abstract-field Sturm/BKR, general
tower transport, or real-closure semantics. Implementation directives should
bundle coherent computational/companion outcomes and preserve these proof
gates; closing a SPEC or an experiment does not close its implementation.

#### One Sturm–Tarski primitive

The [hex-sturm SPEC](Libraries/hex-sturm.md) fixes the frontend API, failure
and termination contracts, replay and evidence requirements, and coordinated
prerequisite contracts in hex-poly and hex-real-roots. The shared clauses
below also govern the other family directives. The
[hex-sturm-mathlib SPEC](Libraries/hex-sturm-mathlib.md) fixes the companion
statements and the shared theorem contract in hex-real-roots-mathlib.

For semantic fields use Lean core's existing field/order classes, with
compatible Mathlib instances in companions. Do not install them on raw
selected-root representatives or on a bounded sign attempt.

The [execution contract](real-closure-execution.md) separates ordinary total
representation operations from semantic field laws. Canonical-zero storage
lets the existing `DensePoly` kernels use honest structural `DecidableEq`;
nonzero representations need not be canonical. Semantic identities and replay
use zero differences. Companions prove noninjective interpretation, zero
reflection and operation/sign preservation, then quotient field laws.
Algebraic constructors and readers do not require those proofs to execute.
There is no second Tarski primitive, fallible arithmetic record or benchmark
import exception. Transcendental refinement keeps an erased caller progress
premise; finite per-input benchmarks can prove it by a checked successful
precision without claiming a universal transcendental field registration.

Generalize the arithmetic primitive **in place below the family**: one
positive-scaled signed-remainder/query-replay kernel in `hex-real-roots`, over
an ordinary ordered commutative domain. It does not require division or a field, so integer
arithmetic is an actual instance. `hex-sturm` owns the general ordered-field
frontend: domain checks, squarefreeness, finite `K` and infinite endpoint
adapters, coefficient evidence composition and root-count APIs.
`ZPoly.tarskiQuery` remains the integer/dyadic frontend of the same kernel,
retaining optimized integer content and Horner operations. Both frontends
share the initial reduction and remainder recurrence, not independent query
implementations. A specialized backend must prove equality to that kernel.
Clear denominators of rational `p` and `f` separately by positive integers;
the rational/dyadic frontend must equal `ZPoly.tarskiQuery`, with a
translation of its replay certificates.

The shared abstract signed-remainder/replay soundness theorem lives in
`hex-real-roots-mathlib`, importing the Tau Ceti foundation there. That
companion retains ownership of `ZPoly.tarskiQuery_eq` and
`TarskiReplay.check_sound`, derived by integer specialization of the shared
theorem. `hex-sturm-mathlib` consumes it to prove the general frontend's
guards, endpoint adapters and coefficient-evidence composition sound. Thus
neither the primitive nor its foundational soundness proof is duplicated, and
no upstream library imports the family. The two Sturm directives must specify
this coordinated generalization of the existing real-roots SPECs.

For nonzero squarefree `p`, the query of `f` on `(a,b)` is the integer sum of
`sign(f(α))` over the distinct roots of `p` there. Endpoints are finite `K`
values or `±∞`; finite endpoints must not be roots of `p`, and `a < b`.
Nonzero constant `p` gives zero. Zero/nonsquarefree `p`, reversed intervals
and root endpoints are rejected before shortcuts. `f=0`, a zero initial
remainder and a nonconstant terminal gcd are valid cases. First reduce `f*p'`
modulo `p`; all subsequent nonzero remainder degrees strictly decrease. Replay
checks positive-scaled initial and three-term identities, the terminal zero
remainder, domain guards, signs and variations, with leading-coefficient and
degree parity signs at infinity. Coefficient signs themselves need
certificates when coefficients are extension elements. A runtime comparison
alone is not proof evidence.

The root count is the query of `1`. Preserve today's separate half-open
Sturm-count API, which admits a root at its upper endpoint. Leave the existing
`Sturm.IsSturmChain` proofs over `Polynomial ℝ` intact; do not make their
refactoring a prerequisite for this family. The shared
signed-remainder/Cauchy-index theorem must include common factors; it is not a
corollary of derivative-chain root counting.

#### Sign determination and encoded roots

The [hex-sign-det SPEC](Libraries/hex-sign-det.md) fixes the complete-table
API, recursive support certificates, descriptor operations, failure and
termination contracts, and production/replay evidence bounds. The shared
clauses below continue to govern the other family directives.

For squarefree nonzero `p`, an interval `I` and polynomials `q₁,…,qₛ`, return
every realized sign vector `σ ∈ {-1,0,1}ˢ` with its positive root count. The
empty polynomial list has the one empty condition with count equal to the root
count, unless that count is zero. Counts concern distinct roots;
multiplicities belong to squarefree decomposition in the root API.

For exponent rows `e ∈ {0,1,2}ˢ`, let `M[e,σ] = ∏ᵢ σᵢ^eᵢ` (including `0^0 =
1`) and `t[e] = TaQ(∏ᵢ qᵢ^eᵢ, p; I)`. The certificate carries the Tarski
replays, nonnegative integral counts, `M*c=t`, and a checked invertibility
witness (e.g. an integer matrix `A` and nonzero integer `d` with `A*M=d*Id`).

BKR uses reduced matrices. Its additional **support-completeness invariant**
is: every root of `p` in `I` realizes a listed candidate condition before the
reduced system is solved. Leaves have complete ternary tables. At a recursive
combination, completeness of both children puts every realized parent vector
in their Cartesian product. Each pruning step must certify zero counts or use
a proved support-preserving reduction; arbitrary omitted columns are
forbidden. Carry the recursive tables and reduction evidence in the replay.
Only then does invertibility establish all counts and justify dropping zero
rows from the output. Total count agreement alone is not a substitute.

A root descriptor contains `p`, an interval with possibly infinite endpoints,
and signs of selected derivatives. Validity means **exactly one** root
satisfies both interval and sign constraints. Full Thom encodings guarantee
identity without a rational separation bound; partial encodings need a checked
count-one condition. Complete partial derivative encodings by sign
determination before comparing roots of the same polynomial by Thom's ordering
rule; do not compare sign arrays lexicographically. Different defining
polynomials require a common squarefree product and re-encoding, or an
equivalent certified joint sign determination; matching raw vectors is not
equality. This is the BKR sign-determination library, not a multivariate
quantifier-elimination algorithm; see the [BKR
analysis](../reports/decision-procedures-alignment.md#ben-orkozenreif).

The [hex-sign-det-mathlib SPEC](Libraries/hex-sign-det-mathlib.md) fixes the
imported moment, recursive reduction and Thom theorem shapes, local replay
correspondence, descriptor completion and changed-polynomial transport. The
shared support, coefficient and termination contracts here continue to govern
the downstream tower directives.

#### Ordered rational functions and termination

The individual [hex-ordered-fn SPEC](Libraries/hex-ordered-fn.md) specifies
ordinary exact fraction arithmetic, user approximation laws, sign proofs and
executable total-search construction. The companion
[hex-ordered-fn-mathlib SPEC](Libraries/hex-ordered-fn-mathlib.md) specifies
real evaluation, the Hahn-series model, arithmetic correspondence and the
laws supplied to that adapter. The clauses here remain the shared contract
for both libraries and the downstream tower directives.

For a new infinitesimal, require `0 < ε < a` for every positive `a` in the
preceding field. The sign of `p(ε)/q(ε)` is the product of the signs of the
lowest-degree nonzero coefficients of `p` and `q`; zero numerator is zero.
Monicity does not make the denominator positive at `ε`. Iterating gives `ε₂`
smaller than every positive element of `K(ε₁)`, including every positive power
of `ε₁`.

Choose the companion model `Lex (HahnSeries ℤ K)`, with constants at exponent
zero and `ε` at exponent one, iterated for successive infinitesimals. The
[pinned Mathlib](../lake-manifest.json) revision
`1cf325a0cf67aca2b04d76b5380ff6a9e410aefa` provides the lexicographic ordered
ring in `Mathlib/RingTheory/HahnSeries/Lex.lean` and the field structure in
`Mathlib/RingTheory/HahnSeries/Summable.lean`. Reuse the existing `RatFunc`
embedding into `LaurentSeries K` and `RatFunc.coe_X` in
`Mathlib/RingTheory/LaurentSeries.lean`, composed with Hex's rational-function
correspondence. Prove lowest-coefficient sign correspondence, order laws and
the infinitesimal inequality in Hex. Obtaining a real closed ambient field for
this model is a separate existence obligation described below; a Hahn field
with exponent group `ℤ` is not itself real closed.

For a real constant `τ`, the caller supplies `approx : Rat → Bounds`,
plus separate containment and width proof functions. For every positive
rational request `δ`, the returned interval must contain that specific `τ`
and have width at most `δ`. Both guarantees are required; approximation
execution itself calls only the data function. Requesting `δ=2^(-n)` gives
the effective convergence schedule. Refinement must
also enclose all preceding real coefficients. Refine numerator and denominator
until their signs are separated from zero, handling formal zero first. The
semantic hypothesis is transcendence over the **embedded preceding field**,
not merely over `ℚ`. It makes evaluation injective and excludes denominator
zeros. Store constant identities and oracle provenance, not arbitrary
callbacks whose outputs the kernel would trust. The computational interface
uses exact rational or dyadic finite endpoints with a checked order, and the
few exact bound operations needed by Horner evaluation. The caller owns
constant-specific approximation algorithms, containment proofs and effective
progress; the generic companion proves their composition. No bundled π/e
producer, interval solver, interval-library admission or analytic-provider
benchmark is required. A future optional adapter may instantiate the same
interface without changing the family import graph.

The ordinary ordered-field sign operation searches for separation of a
formally nonzero rational function. Algebraic equality detects formal zero
before refinement. Correct enclosures, effective convergence and relative
transcendence prove eventual separation. The computational library accepts
the corresponding Prop termination law; the companion derives it from those
semantic hypotheses. A well-founded search on this proof gives an executable
total sign without a user threshold or guessed separation bound. The erased
termination proof is not an oracle supplying a numerical answer.

An optional finite `sign?` attempt reports a sign or `none`; its successful
nonzero claims need containment, not transcendence. Exact evaluation
identities, including a certified singleton `[0,0]`, may prove zero. This
interface neither supplies a total field comparison nor propagates budgets
through polynomial arithmetic. Without the hypotheses for an exact ordered
field, clients can check finite enclosure/identity certificates but cannot
invoke the generic tower decision procedure as if that field were available.
`RationalFn K` retains its ordinary exact arithmetic over a lawful base `K`;
there is no bounded rational-function arithmetic implementation.

The pin contains only the analytic part of Lindemann–Weierstrass, not proofs
of `Transcendental ℚ Real.pi` or `Transcendental ℚ (Real.exp 1)`. Treat those
as explicit hypotheses for totality. Even proofs of both separately would not
justify a total `ℚ(π,e)` adapter: adjoining the second constant requires
relative transcendence (algebraic independence of the pair). The bounded,
certified-enclosure API can still handle both constants together whenever its
required signs are separated, and prove formal identities when all original
denominator nonvanishing obligations are certified.

#### Algebraic towers, normalization and sampling

The [hex-real-closure SPEC](Libraries/hex-real-closure.md) fixes the staged
context and selected-root APIs, Yun decomposition, splitting/transport, complete
root isolation, shared samples, failures and evidence requirements. The clauses
below remain shared contracts for the companion and downstream directives.
The [hex-real-closure-mathlib SPEC](Libraries/hex-real-closure-mathlib.md)
fixes relative and ambient-existence semantics, live splitting/enlargement
transport, compatible-union proofs, finite-sign specialization and replay bounds.

Enforce stages `transcendental ≺ infinitesimal ≺ algebraic` in the tower API.
Creating a finite tower does not make it real closed; real closure is the
union of finite compatible algebraic extensions, with new roots adjoined on
demand. Each algebraic level has squarefree `p` and a valid selected-root
descriptor. Elements have polynomial representatives `q(α)` with semantic
equality at that root. Since `p` need not be irreducible, **do not install a
field instance on `K[X]/(p)`** or use equality of remainder arrays as field
equality. Equality of values is the certified zero sign of the difference at
`α`. Executable elements have canonical zero and ordinary total operations,
with structural equality kept distinct from semantic equality. The companion
constructs the semantic quotient field and proves correspondence; executable
contexts do not take its law proofs. An inverse may recompute a split purely; persisting splits
is a context optimization whose denotation invariance must be proved.

For inversion, establish `q(α) ≠ 0` first, then compute `g = gcd(p,q)`. If `g`
is nonconstant, the selected root lies in `p/g`, since it is not a root of
`g`. Replace the defining constraint with this smaller factor, re-encode the
selected root using derivatives of the new polynomial (retaining the old
descriptor as transport evidence), and use extended gcd there to obtain the
inverse. Preserve denotations of all live elements and downstream levels under
this refinement; versioned contexts or explicit transport must prevent stale
certificates. Degree decrease bounds splitting. Specify zero inversion
consistently with the field API and a checked nonzero wrapper.

Clean representations preserve integral coefficients at the base and,
recursively, denominator-one polynomials with clean coefficients. Use signed
pseudo-remainders and positive scaling witnesses. Reduce algebraic expressions
by monic clean defining polynomials when useful; do not eagerly reduce by
non-monic defining polynomials or force them monic. Thus stored expressions
may have degree above `deg p`. This is compatible with canonical `RationalFn`
at transcendental/infinitesimal levels: a clean denominator-one polynomial is
already in that normal form. Root search clears denominators with recorded
nonzero/sign data; changes of scale must preserve query signs.

Root isolation uses a new characteristic-zero Yun adapter to obtain squarefree
factors and multiplicities, removes zero roots separately, and returns a
complete ordered list with multiplicities. A finite dyadic Cauchy bound
permits bisection as a fast path; it does **not** guarantee dyadic separation
in a non-Archimedean field. Use a deterministic degree-based bound on
bisection work, then full derivative sign determination on every unresolved
interval. Bound estimation is itself bounded work: infinite, unavailable or
unresolved dyadic bounds go directly to sign determination; no search for a
finite bound may delay the fallback indefinitely. Roots encountered at split
points are emitted once and excluded from subsequent open intervals. For
example, at most `2*(deg p+1)` bisection nodes precede the fallback;
correctness is independent of that policy because the finite BKR fallback
handles all remaining roots. No user accuracy threshold controls completeness.
The executable uses structural or internally size-bounded recursion. Prove
adequacy and completeness under the lawful semantic interpretation. Degree
descent, finite BKR recursion, bounded bisection and coefficient-sign progress
are separate obligations; see the [execution contract](real-closure-execution.md).

`hex-sign-det` owns single-polynomial root descriptors, their identity, order,
sign evaluation and replay. `hex-real-closure` owns the tower-level sample
interface built from these operations. The shared interface for CAD lifting
and [coverings](Libraries/hex-coverings.md)
exposes opaque contexts, coefficient embeddings, ordered roots with
multiplicities, root equality/order, polynomial sign at a root, and
section/sector sample construction with replay evidence. A sector request
includes the finite family of polynomials whose signs must be preserved and
its adjacent root boundaries. A sample `r+ε` or `±1/ε` must come with signs
and a theorem realizing those finitely many signs at an ordinary point of the
intended cell; an infinitesimal itself is not a real witness. A fresh
infinitesimal after an algebraic sample requires rebuilding an enlarged
infinitesimal base and transporting the selected algebraic roots into its real
closure, preserving their order. It cannot simply append an out-of-stage
extension. The simpler dyadic/midpoint backend remains available.
[#10301](https://github.com/kim-em/hex-dev/issues/10301) measures these
alternatives. The [coverings SPEC](Libraries/hex-coverings.md#literal-samples-and-checked-export)
fixes a literal integer-polynomial and isolated-parameter replay format,
with a selected-root coefficient adapter to the shared Sturm interface.
This family can supply alternate sample producers and root/sign evidence
through checked export and correspondence to that format.

#### Proof ownership and public surface

Consume the abstract real algebra requested by
[#10300](https://github.com/kim-em/hex-dev/issues/10300) from Tau Ceti; do not
rederive that foundation independently in Hex. The following are mathematical
statement shapes, not claims that the named Lean declarations already exist.
Let `R` have `[Field R] [LinearOrder R] [IsStrictOrderedRing R]` and
`[IsRealClosed R]`, and let `ι : K →+* R` be an order-preserving embedding.
Canonical fields retain the existing polynomial correspondence. For
representation coefficients `E`, first interpret `DensePoly E` in `Polynomial K`
with operation preservation and zero reflection; that map need not be
injective. Then map along `ι`. Zero reflection, not representative uniqueness,
preserves degree.

| Owner/consumer | Imported statement from Tau Ceti | Correspondence proved in Hex |
| --- | --- | --- |
| Shared foundation in `hex-real-roots-mathlib`, consumed by `hex-sturm-mathlib` | Polynomial IVT on `[a,b]` and Rolle between distinct roots; signed-remainder/Cauchy-index identity equating variation drop to `∑ sign(f(α))` on root-free `(a,b)`, also at infinities and with a common gcd; root count as `f=1` | In real-roots: ordinary polynomial correspondence, positive pseudo-remainder/replay soundness, integer specialization and `IsRealClosed ℝ`. In sturm: field frontend, endpoint semantics and coefficient-certificate composition |
| `hex-sign-det-mathlib` | Thom injectivity and root-order rule; for finite `Q`, the moment identity `t=M*c` for actual sign counts and correctness of the recursive support-preserving BKR reduction | Literal matrix/replay checks imply exact counts and complete support; validity and comparison of partial descriptors, including different polynomials |
| `hex-ordered-fn-mathlib` | No additional abstract real-closed-field theorem: uses Mathlib rational functions, real analysis and Hahn series | Real evaluation under relative transcendence; enclosure soundness and eventual success; Hahn embedding, sign rule and ordered-field laws |
| `hex-real-closure-mathlib` | Existence of an algebraic real closed ordered extension of every ordered field (an explicit additional foundation requested alongside #10300); polynomial IVT/Rolle and Thom/sign determination through the preceding companions | Selected-root arithmetic and splitting transport, termination, ordered complete root lists, compatible-tower semantics and real-closedness of their algebraic union, trivial-tower agreement, finite-sign sector realization |

The companion semantics are conditional on this ambient field and embedding
until their existence is discharged. The pin has neither real-closure
existence nor an `IsRealClosed ℝ` instance. Make these obligations explicit:
use Hex's existing `IsRealClosed RealAlgebraicNumber` for the rational base;
use the implemented `Real.instIsRealClosed` in `hex-real-roots-mathlib`,
proved from Mathlib real square roots and polynomial order/IVT lemmas, for
both integer specialization and the real transcendental base; consume the ordered real-closure existence
theorem from Tau Ceti for infinitesimal bases. The required existence shape
is: for every linearly ordered field `K`, there exist an ordered real closed
field `R` and order-preserving field embedding `ι : K →+* R` with `R`
algebraic over `ι(K)`. This is additional to the univariate theorem list
currently requested by #10300, not an assertion that the roadmap or pin
already supplies it. The real-closure companion SPEC must record that
foundational requirement before proof work starts.

Within that supplied ambient field, Hex proves the compatible-tower model:
positive square roots and odd-degree roots lie in the algebraic union, and
every element is algebraic over the fixed base. This is a relative
construction, not a second absolute proof of existence of real closures.
Finite-sign sector realization is also a Hex obligation, with its base field
and embedding stated. For a real root `r` and a finite family of real
polynomials, the signs at `r+ε` can already be realized near `r` using finite
Taylor coefficients and real continuity; that fragment does not need
real-closure existence for a Hahn field. Nested algebraic infinitesimal
samples require the ambient model above. Nested replay costs are accepted: a
level's coefficient-sign evidence may contain BKR/Tarski replays at lower
levels. The SPECs must bound and benchmark these compositions, and `rcf` emits
only evidence needed for the final real-valued coefficient or finite-sign
realization claims. Foundation references are [Cohen–Mahboubi, LMCS
2012](https://lmcs.episciences.org/844) and [Vermande, CPP
2026](https://doi.org/10.1145/3779031.3779100). All companion SPECs name these
imported assumptions and remain planned where those results are missing;
writing the SPECs does not wait for their proofs.

The exploration API offers caller-registered constants, staged infinitesimal
construction, arithmetic, comparison, polynomial `roots` and a reconstructible `Repr`,
modeled on [Z3's Python RCF
API](https://github.com/Z3Prover/z3/blob/master/src/api/python/z3/z3rcf.py).
Printed syntax includes the context, named constants, polynomial, interval and
Thom signs needed to reconstruct a root; a registered oracle name must resolve
to the same constant. Round trips preserve denotation and root identity, not
incidental cache state. A caller can register `π` or `e` by supplying the same
approximation/evidence interface; these are not bundled providers. Any total
mode remains conditional as above. Generic infinitesimal examples
are `#eval` demonstrations, with no nonstandard-analysis tactic claims.

The downstream [`rcf` coefficient extension](../HexRCF/SPEC/hex-rcf.md#planned-real-coefficient-extension)
is specified in the owning HexRCF SPEC: univariate sentences over `ℝ` with
fixed real algebraic embeddings and authenticated caller-supplied constants,
using the shared RealFormula frontend and kernel certificates with coefficient
signs.
Its optional import preserves the integer/rational fast path; the SPEC lists
the actual implementation and semantic prerequisites without advancing a phase.
That integration is new work; the integer-only replay cannot consume these
contexts unchanged. Without transcendence proofs it can certify the fragment
where every required nonzero sign is separated by caller-supplied certified
enclosures and all zero signs have algebraic/identity proofs. For example `∀ x : ℝ, x² > π - 4` needs only a certified `π < 4` and
nonnegativity of squares. No completeness claim covers unresolved relations
between constants. Infinitesimal search samples require the finite-sign
realization bridge before contributing evidence about `ℝ`.

#### Sanity checks, conformance and evidence

The paper's Example 3 factors as `ε²x⁵ − εx³ − εx² + 1 = (εx²−1)(εx³−1)`. Its
three ordered real roots are `−ε^(-1/2)`, `ε^(-1/3)`, `ε^(-1/2)`. Both
positive roots exceed every rational. For `p'''(x)=60ε²x²−6ε`, the sign at
`ε^(-1/3)` is the sign of `6ε*(10ε^(1/3)−1)`, hence negative, while at
`ε^(-1/2)` it is `54ε>0`. Thus `(0,+∞)` plus the third-derivative sign
distinguishes them; interval overlap alone does not. Also `0<ε<1` implies
`√ε>ε` by comparing squares, and for every positive integer `n`, `ε<1/n`
implies `1/ε>n` (the nonpositive case is immediate). Test multiple
infinitesimal levels, including `ε₂<ε₁^m` for every fixed positive integer
`m`.

Conformance uses Z3 `MkInfinitesimal`, `MkRoots` and comparisons; `Pi`/`E`
comparisons apply only when a caller-supplied provider is available,
with a pinned version and recorded fixture provenance. Reproduce the paper's
`basic.py`, degree-15 MetiTarski and `y³+x³+1` cases from `nlsat.py`,
`tower8.py`, and Rioboo/Strzeboński examples. Record any constant-provider
inputs explicitly; their production is outside this family. Generic oracle
contract tests use small supplied certified bounds and malformed or
nonprogressing test procedures, not a new analytic library. Use python-flint
and the existing `hex-real-algebraic` API for the rational-only cases. Require exact
agreement of signs, sorted roots, multiplicities and arithmetic; printed
decimals do not establish agreement. Test exhausted or invalid approximation
inputs, root endpoints, shared gcds, dynamic splits and stale replay
rejection, plus negative certificate cases with an omitted realizable sign
condition.

The trivial-tower backend delegates to `hex-real-algebraic` where applicable;
its generic backend must additionally agree by correspondence theorem and
conformance. Benchmarks separate query production, BKR matrices, coefficient
signs, isolation and kernel replay. Phase 4 reports `tower8` isolation and a
clean-versus-eager normalization ablation, including coefficient sizes and gcd
work. The paper's 0.28 s versus 30-minute timeout is a historical observation,
not a host-independent target. Follow the shared-host, alternating adjacent
comparison discipline in [benchmarking.md](benchmarking.md), retain every
completed sample, and keep all bench imports Mathlib-free.

#### SPEC directives

Each computational library and each companion has its own SPEC directive.
Their initial planned SPECs live in `SPEC/Libraries/hex-*.md`, matching other
planned libraries; per-library directories are introduced with implementation.
All eight depend on this family design; companion directives also depend on
their computational contract. Implementations, publication, CAD/coverings and
tactic extensions remain later work. The links below are the issue tracker;
the dependency diagram above is the library import contract.

| Computational SPEC | Companion SPEC |
| --- | --- |
| [hex-sturm SPEC](Libraries/hex-sturm.md) ([#10311](https://github.com/kim-em/hex-dev/issues/10311)) | [hex-sturm-mathlib SPEC](Libraries/hex-sturm-mathlib.md) ([#10312](https://github.com/kim-em/hex-dev/issues/10312)) |
| [hex-sign-det SPEC](Libraries/hex-sign-det.md) ([#10313](https://github.com/kim-em/hex-dev/issues/10313)) | [hex-sign-det-mathlib SPEC](Libraries/hex-sign-det-mathlib.md) ([#10314](https://github.com/kim-em/hex-dev/issues/10314)) |
| [hex-ordered-fn #10315](https://github.com/kim-em/hex-dev/issues/10315) ([SPEC](Libraries/hex-ordered-fn.md)) | [hex-ordered-fn-mathlib #10316](https://github.com/kim-em/hex-dev/issues/10316) ([SPEC](Libraries/hex-ordered-fn-mathlib.md)) |
| [hex-real-closure SPEC](Libraries/hex-real-closure.md) ([#10317](https://github.com/kim-em/hex-dev/issues/10317)) | [hex-real-closure-mathlib SPEC](Libraries/hex-real-closure-mathlib.md) ([#10318](https://github.com/kim-em/hex-dev/issues/10318)) |

### Lattice applications beyond factor recombination

Build certified APIs on top of `hex-lll` for:

- Minimal-polynomial recovery from an exact algebraic target, a certified
  approximation error, and degree and height bounds.
- Integer-relation detection for exact real targets with certified
  approximations and coefficient bounds.
- Stronger reduction such as deep-insertion LLL or BKZ, once benchmarks show
  that reduction quality rather than reduction time is the limiting factor.

An enclosure around a candidate root or relation is not sufficient. Recovery
needs a separation theorem ruling out every competing polynomial or relation
within the stated bounds.

### Exact lattice search and geometry

Exact ball enumeration and all shortest/closest vectors are specified in
[hex-lattice-enum](../HexLatticeEnum/SPEC/hex-lattice-enum.md), with correctness proofs and
integer-span and Euclidean-distance correspondence in
[hex-lattice-enum-mathlib](../HexLatticeEnumMathlib/SPEC/hex-lattice-enum-mathlib.md).
Successive minima remain an extension: they need an independence certificate
at each threshold and a proof that no smaller radius contains the required
number of independent vectors.

`hex-lattice-voronoi` should be restricted initially to positive-definite
integral lattices of modest rank. It enumerates Voronoi-relevant vectors,
constructs the rational half-space description of the cell, and computes
vertices by exact linear solving. The initial enumeration visits every coset
of `2L` in `L` and uses the exact closest-vector search to find all shortest
representatives. A nonzero vector is retained precisely when its two signs are
the unique shortest representatives of its coset. The companion proves the
Voronoi-relevant-vector characterization, which makes the finite enumeration
complete. Correctness then proves both inclusions between the returned
polytope and the set of points at least as close to zero as to any other
lattice point. Covering radius and deep holes follow only after all vertices
and relevant inequalities are certified complete.

`hex-lattice-iso` should initially support positive-definite integral lattices
and implement Plesken-Souvignier backtracking after short-vector and
orthogonal-decomposition invariants have reduced the search. An isometry
result carries the integral change-of-basis matrix and proves it
is unimodular and preserves the Gram matrix. An automorphism-group result uses
the planned permutation-group machinery on a certified characteristic set of
short vectors. Completeness proves that restriction to this set is faithful
and that every Gram-preserving automorphism occurs in the generated group. A
failed backtracking search proves non-isometry only when its partition and
branch exhaustion are part of the verified algorithm.

Manual examples should solve an integer least-squares problem arising from a
new small lattice-coded communication channel and compare Babai's candidate
with the certified closest vector. A geometry chapter can enumerate the
shortest vectors and Voronoi cell of the two-dimensional hexagonal lattice,
where the answer is easy to visualize but the computation still uses the
general certificates. A later tutorial can distinguish two same-determinant
lattices by their certified short-vector data and compute the automorphisms of
one of them. Named lattices such as `E_8` may be used when the exposition and
Lean code are independently written.

### Cylindrical algebraic decomposition

Extend the univariate decision procedure of `hex-rcf` to sentences and
quantifier elimination in a small number of variables. The compiled pipeline
decomposes into components that largely exist:

- Projection. View a level-`k+1` polynomial as univariate in its main variable
  over `MvPoly k` (`toUnivariate`). Collins' operator takes, for every
  reductum `r` of every polynomial `p` (truncations of `p` by successive
  leading terms, which cover the degree drops when leading coefficients
  vanish), the coefficients of `r`, the principal subresultant coefficients of
  `(r, r')`, and the principal subresultant coefficients of `(r, s)` for
  reducta `s` of the other polynomials; the chains come from `hex-resultant`
  over `MvPoly` coefficients (`hex-mv-gcd` supplies the exact-division law
  and already runs that chain), after squarefree and irreducible basis
  reduction from `hex-mv-gcd` and `hex-mv-factor`. Use Collins' operator
  first. McCallum, Brown, and Lazard shrink the projection set but change the
  theorem, its side conditions, and (for Lazard) the lifting step, so each is
  a separately certified variant rather than a search-time option.
- Base phase. `ZPoly.realAlgebraicRoots` and dyadic samples between roots.
- Lifting. Substitute a sample point into each next-level polynomial to obtain
  a `RealAlgebraicPoly`, take `RealAlgebraicPoly.roots`, and choose samples
  between roots. Canonical `AlgebraicNumber` coordinates re-canonicalize at
  every substitution, which is the known performance cliff; lazy
  `AlgebraicRoot`s, `NumberTower` coordinates, and Thom encodings are the
  alternatives. That choice is shared with
  [#10142](https://github.com/kim-em/hex-dev/issues/10142) and
  [#10143](https://github.com/kim-em/hex-dev/issues/10143) and should be made
  once.
- Sign evaluation at samples. Exact `RealAlgebraicNumber` arithmetic.
- Cell semantics, sign rows, Boolean and quantifier folds. `hex-rcf`'s, by
  induction on levels; cylindricity carries the fold across a quantifier
  block boundary.

Correctness has one deep theorem and a large amount of replayable arithmetic.
The theorem is delineability: over a connected cell on which the projection
set is sign-invariant, each level polynomial either vanishes identically on
the cylinder over the cell or has real roots given by finitely many
continuous functions of constant multiplicity that never cross. For Collins'
operator it needs continuity of the complex roots of a polynomial in its
coefficients (the pinned Mathlib has the monic equal-degree case,
`Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt`; multiplicity
control, root functions, and the degree-drop cases remain), the relation
between the first nonvanishing principal subresultant coefficient and the
degree of the gcd (`hex-resultant-mathlib` has the resultant-zero and
specialization facts only), and connectedness of sections and sectors over
connected cells. Over `ℝ` that connectedness is topological; over an
arbitrary real closed field intervals are not connected and the statement
must use semialgebraic connectedness, so the first target is `ℝ`. Vermande's
Rocq/MathComp proof (CPP 2026), the first formal correctness proof of CAD, is
the reference for the statement shapes. The theorem is independent of every
implementation choice and is the long pole; it belongs in a Tau Ceti roadmap,
and the Hex companion that consumes it will import Tau Ceti. Nothing in this
entry can be certified without it.

The certificate must convince the kernel that the sample points meet every
sign-invariant cell of the atom polynomials and that the atom signs at the
samples are as claimed. Sign claims replay per sample. Completeness is the
delineability theorem applied to literal polynomials that the kernel has
checked are the required subresultant coefficients and leading coefficients:
replay the subresultant chains with their multiplication-only recurrence
witnesses level by level, as `hex-rcf` replays Sturm chains. Root isolation
at each level over algebraic coefficients is then a Sturm replay over `ℚ(α)`,
or a Thom-encoding replay with Tarski queries; this component has no Hex
precedent and is the likely limit on replay cost. `hex-rcf`'s univariate
replay already costs seconds per goal, and a multivariate design budgets from
that baseline.

Sequencing: first the delineability theorem; in parallel an unverified
compiled prototype of projection and lifting, measured on the standard small
examples (Collins' circle and parabola pairs, Kahan's ellipse in the unit
circle, a Davenport–Heintz family for the blowup) to fix the sample
representation; then the certificate SPEC. Reserve full decompositions for
quantifier elimination with alternations and for exploration. The tactic case
(universal goals, and existential goals without alternation) should use
[covering refutation](Libraries/hex-coverings.md), which shares the theorem,
projection arithmetic, and lifting primitive but certifies only the cells a
search visited.

Dependencies: `hex-mv-poly`, `hex-mv-gcd`, `hex-mv-factor`, `hex-resultant`,
`hex-real-roots`, `hex-real-algebraic`, `hex-number-field`, `hex-reflect`, and
the shared [real-arithmetic formula language](Libraries/hex-real-formula.md).

## Cross-cutting infrastructure

### Certificate serialization and caching

Define a shared envelope for expensive certificates while leaving each
library's payload format under its own versioning. The envelope should include
the checker and schema versions, toolchain and ABI identifiers, a hash of the
certified input, and a payload type tag.

A cache hit supplies untrusted data and validation always replays the checker.
The SPEC must decide content addressing, version skew, storage location, and
resource limits for decoding and replay. `hex-conway`'s stored database and
the interval certificate schema are useful first consumers, but neither
should become a universal payload representation.

Direct radical extraction, certified principal-root approximation, cyclotomic
construction and recognition, and reduction of canonicalization's all-roots
isolation cost have a complete
[owning design](../HexNumberField/SPEC/hex-number-field.md#direct-certified-radicals-and-cyclotomic-embeddings), with
[companion proof obligations](../HexNumberFieldMathlib/SPEC/hex-number-field-mathlib.md#direct-radical-proof-obligations)
and [manual requirements](../HexManual/README.md#direct-radical-design-requirements).
Implementation remains future work. The polynomial generator follows the
[cyclotomic SPEC](Libraries/hex-cyclotomic.md); broader comparison work in
[#10142](https://github.com/kim-em/hex-dev/issues/10142) remains separate.
The [quadratic construction report](../reports/hex-number-field-quadratic.md)
records the fix for the independent integer-root memory bug
[#10156](https://github.com/kim-em/hex-dev/issues/10156) and the remaining
trial-factorization allocation costs; preserve its regression when migrating
canonical constructors.
