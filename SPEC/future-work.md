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
Boyer-Myrvold planarity testing, and `hex-graph-iso` should contain
individualization-refinement graph canonical labelling. Add Mathlib
companions where correspondence or abstract mathematical theorems require
them, rather than automatically creating one for every algorithm library.

The base representation should not depend on matrices or permutation groups.
All the graph algorithms above depend on `hex-graph`. The Hungarian algorithm
uses the base bipartite representation but does not depend on Hopcroft-Karp.
`hex-graph-iso` initially depends only on `hex-graph`. An implementation using
complete stabilizer or group operations may later add the permutation-group
library. The first canonical-labelling release does not require that
dependency.

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

The first `hex-graph-iso` release exposes a canonical form, its canonical
label, a checked isomorphism when one exists, and positive and negative
`graph_iso` tactic proofs. The canonical-form theorem is for ordered-coloured
graphs. Two such graphs are isomorphic exactly when their canonical forms are
equal. The detailed computational and Mathlib-facing contracts are in
[hex-graph-iso](Libraries/hex-graph-iso.md) and
[hex-graph-iso-mathlib](Libraries/hex-graph-iso-mathlib.md).

Complete automorphism-group generators are a later extension. Rather than
enumerate every isomorphism between two graphs, that extension returns one
transporter and the source automorphism group. It proves that every
isomorphism is uniquely the transporter composed with an automorphism. A
request for an explicit list expands that coset only under a caller-supplied
cardinality budget. Automorphism-group completeness uses the same canonical
search tree, not merely verification that each reported permutation preserves
edges.

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

### Fast multiplication in characteristic two, follow-ups

The generic radix-3 algorithm and its triadic semantics are specified in
[hex-poly-fast](../HexPolyFast/SPEC/hex-poly-fast.md). The packed
characteristic-two implementation is specified in
[hex-gf2](../HexGF2/SPEC/hex-gf2.md). Its generic coefficient-operation bound
is specified in
[hex-poly-fast-cslib](Libraries/hex-poly-fast-cslib.md). Those SPECs leave the
following separate projects:

- Specify and compare additive FFT multiplication, including Cantor and
  Gao-Mateer variants, for `F_2[x]` and `F_(2^k)[x]`.
- Specify the wrapped-product splitting reconstruction from §3.3 of Brent,
  Gaudry, Thomé, and Zimmermann. It may reduce the performance discontinuities
  caused by padding to an admissible schedule.
- Instantiate the generic radix-3 plan for `F_(2^k)[x]` in the hex-gfq
  libraries. The existing word-prime radix-2 NTT does not apply directly to
  those coefficient fields.
- Give integer Schönhage-Strassen multiplication its own motivation and SPEC.
  Current large integer products use GMP through Lean's runtime.
- Specify a possible hex-gf2-cslib library for packed word-operation bounds.
  The generic coefficient count cannot express that one word XOR processes
  64 coefficients or that a base product uses CLMUL.
- Apply the `-cslib` pattern to another library only after identifying a
  concrete theorem that justifies the dependency. Turing-machine complexity
  is not planned.

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

`hex-groebner` should start with Buchberger's algorithm and the
Gebauer-Möller pair criteria. Add F4 only if benchmarks justify it.
Applications include ideal membership,
intersection, quotient, elimination, implicitization, and radical membership
through the Rabinowitsch trick.

Ideal membership has a compact trusted boundary: return cofactors witnessing
`p = sum_i h_i * g_i`. Non-membership requires more. A nonzero remainder is
conclusive only after the divisor set is certified to be a Gröbner basis and
connected to the original generators, including the required S-pair
criterion. Treat positive and negative decisions as separate certificate
types with separate budgets.

The computational layer depends on `hex-mv-poly`; coefficient-domain
hypotheses and monomial order must be explicit. Zero-dimensional solving and
root reconstruction are downstream work rather than part of the first basis
library.

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

The first `hex-discrete-log` implementation should use the finite-field
multiplicative group. Once elliptic-curve subgroups are also consumers, expose
an explicit lawful finite cyclic-group interface carrying equality,
multiplication, inversion, exponentiation, a generator, and a supplied exact
order. The finite-field implementation depends on `hex-gfq`, `hex-int-factor`,
and `hex-modular`. The elliptic-curve instance later adds only
`hex-elliptic-curve`. `hex-index-calculus` additionally consumes the planned
sparse and black-box linear algebra.

Implement Shanks baby-step giant-step as the deterministic first algorithm.
Its table covers one factor of a rectangular decomposition of the supplied
order, and its giant-step loop covers the other. Correctness proves soundness
of every returned exponent and completeness for every target in the generated
subgroup. The canonical result is the least nonnegative exponent modulo the
exact generator order. If only an upper bound on the order is supplied, the
result type must retain that weaker input and must not assert canonicality.

Pohlig-Hellman follows in the same library and depends on `hex-int-factor`.
For every prime-power factor of the group order, it performs digit lifting by
small discrete logarithms and combines the residues with `hex-modular`.
Correctness proves each lifted congruence, the CRT reconstruction, and equality
with the original target. Completeness requires a certified complete
factorization of the exact order. Partial factorization may reduce the
remaining problem but cannot justify a final uniqueness claim.

Pollard rho supplies a lower-memory Las Vegas search. A collision is useful
only when the resulting linear congruence is solvable and the candidate passes
the final exponentiation check. Exhausting the walk budget returns `none`.
There is no functional theorem promising success for a chosen budget. A
separate probabilistic analysis may bound expected collision time for an
explicit random-walk model.

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

`hex-rational-fn` should provide normalized fractions in `K[x]`: numerator
and denominator are coprime, the denominator is monic, and zero has denominator
one. Arithmetic uses polynomial gcd and exact division. Correctness proves
that normalization preserves the fraction relation and gives a unique
representative. This library can later share code with the univariate part of
the planned rational-expression project, but neither should depend on the
multivariate `Together` or `Apart` tactics merely to obtain a field of
coefficients.

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

Provide finite permutation groups with orbits, stabilizers, subgroup
containment, cosets, and the transitive-group data required by resolvent
methods. Executable certificates should cover membership and subgroup
relations; classification tables and their trust boundary need an explicit
data policy.

This library is independently useful and is a prerequisite for certified
Galois-group computation.

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

`hex-lattice-enum` should depend on `hex-lll` and implement
Fincke-Pohst enumeration with Schnorr-Euchner coefficient ordering. It uses an
exact rational Gram-Schmidt decomposition for pruning, with interval or
floating-point values allowed only to choose the next branch. Its operations
enumerate every vector of squared norm at most a rational bound, find all
shortest vectors, and solve closest-vector problems relative to a rational
target and bound. A closest-vector search begins from a Babai nearest-plane
candidate but proves optimality by complete enumeration.

The enumeration invariant describes the affine interval for every remaining
coefficient after fixing a suffix. Correctness proves that pruning removes
only vectors whose exact lower bound exceeds the radius. The result list is
duplicate-free and contains exactly the lattice vectors in the closed ball.
The shortest-vector theorem supplies a nonzero vector of minimum norm and
proves that no shorter nonzero vector exists. The closest-vector theorem proves
membership of the reported lattice point and minimal distance to the target.
If enumeration is stopped by a budget, the result retains the explored radius
and incumbent but makes no optimality claim.

`hex-lattice-enum-mathlib` identifies the row lattice with the corresponding
`Submodule` of a rational inner-product space. It transports exact norms and
proves that the executable minima agree with the mathematical minimum over
the discrete lattice. This layer also proves packing-radius and kissing-number
statements from complete shortest-vector enumeration. Successive minima need
an additional independence certificate for each threshold and a proof that no
smaller radius contains the required number of independent vectors.

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

Extend the univariate real-closed-field decision procedure to quantifier
elimination in a small number of variables. The intended components include a
projection operator, multivariate subresultant chains in a distinguished
variable, exact algebraic sample points, and sign determination for
polynomials with algebraic coefficients.

Dependencies include `hex-mv-poly`, `hex-mv-factor`, `hex-resultant`,
`hex-real-roots`, `hex-number-field`, and `hex-number-field-tower`. Scope the
first version to two or three variables. Before fixing a public API, prototype
the projection phase and a certificate that carries a complete cell
decomposition with the sign-invariance evidence needed for a negative as well
as a positive decision.

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
