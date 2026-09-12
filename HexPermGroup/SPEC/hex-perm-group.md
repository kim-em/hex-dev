# hex-perm-group

Finite permutation groups on a fixed indexed set, represented by generators
and a checked stabilizer chain. The first version provides constructive
membership, exact group order, finite actions, point and set stabilizers,
subgroup search, block systems, normal and derived subgroups, direct and
wreath products, and bounded element/coset enumeration. Deterministic
Schreier-Sims construction and subgroup search produce certificates whose
completeness is checked independently of the construction.

## Scope and dependencies

`HexPermGroup` depends only on `HexBasic` and is Mathlib-free. It owns
`Hex.Perm n`, an executable permutation of `Fin n`, and group operations in
the namespace `Hex.PermGroup`. It has no graph, matrix, polynomial or
classification-table dependency. `HexPermGroupMathlib` depends on
`HexPermGroup` and Mathlib and relates these objects to `Equiv.Perm (Fin n)`
and its subgroups.

The existing `Hex.GraphIso.Perm` supplies the representation and much of
the elementary permutation API. Extract that type and its graph-independent
lemmas into `HexPermGroup/Perm.lean`. The current module imports
`HexGraph.Basic`, but the general permutation library must not acquire that
dependency. `GraphIso.Label`, whose inverse direction is meaningful for
canonical labelling, stays in `HexGraphIso`.

Graph-isomorphism migration reuses the extracted type, with compatibility
aliases where required by consumers. Its dependency becomes
`HexGraphIso -> HexPermGroup`, never the reverse. The corresponding
`Perm.toEquiv` and `ofEquiv` conversions currently in
`HexGraphIsoMathlib/Encode.lean` are owned by `HexPermGroupMathlib` after
migration. Graph-specific conversion theorems remain in their original library.
Update the affected Lake pins and release manifest through the monorepo when
that migration is implemented. Do not duplicate the permutation representation
or hand-edit a published repository.

The represented groups act faithfully on `Fin n`. Further finite actions
include tuples, subsets, partitions, block systems and cosets; their induced
representations need not be faithful. The scope includes exact sampling from
a supplied uniform index source, but no cryptographic random-number source.
Conjugacy-class enumeration, abstract group isomorphism, character tables
and transitive-group databases remain later extensions. There is no claim
that a generator list is canonical under conjugacy.

## Permutations and composition

`Hex.Perm n` stores a `Vector (Fin n) n` of images with proofs that its
entries are duplicate-free and contain every point. Equality compares image
arrays, with proof irrelevance for the invariant fields. The convention is
function composition and a left action:

```text
(p * q)(i) = p(q(i)).
```

The rightmost factor acts first. This is the convention of the existing
`GraphIso.Perm.comp`. Use it consistently for words, Schreier generators,
cosets, transporters and Mathlib correspondence. Oracle adapters must translate
other action conventions explicitly.

Provide checked construction from raw image arrays, identity, composition,
inverse, natural powers, point application, support, canonical disjoint cycle
decomposition and permutation order. A raw array must have exactly `n`
entries, every entry must be below `n`, and entries must be distinct. Do not
silently reduce out-of-range images modulo `n` or infer the degree from the
largest moved point.

Compiled checked construction uses linear time and linear auxiliary storage
in the degree: scatter a candidate inverse and check both inverse identities.
Prove equality with the duplicate-free, complete-array specification so the
compiler replacement preserves rejection as well as successful results.

Cycles omit fixed points, begin with their least point, follow the permutation's
direction and are ordered by their first point. Prove that the disjoint cycles
reconstruct the permutation. `Perm.order` is the lcm of the cycle lengths,
with empty lcm one. Prove both `p^order = 1` and minimality among positive
exponents. No integer factorization is required. The degree-zero permutation
is the identity and has order one.

Provide `cycleType`, the sorted list of all cycle lengths, including a one
for every fixed point, and `sign : Perm n -> Int` with values in `{-1,1}`.
Compute sign as `(-1)^(n-c)`, where `c` counts all cycles. Prove that cycle
type is invariant under conjugation, that sign is multiplicative, and that
sign agrees with the parity of a transposition decomposition. Degree zero
has empty cycle type and sign one. Fixed points omitted by the disjoint-cycle
serialization must still contribute to cycle type.

## Generated subgroups and words

The input is an ordered array `S : Array (Perm n)`. Its semantic membership
predicate `Generated S p` is closure of these generators under identity,
composition and inverse. Define it without Mathlib, and prove equivalence
with evaluation of a finite word in the input generators and their inverses.

Certificates encode words as finite straight-line programs. A node is identity,
an original-generator index, the inverse of an earlier node, or the product
of two earlier nodes. Each reference must be strictly earlier in the array.
The root is an in-bounds node. Evaluation checks indices and returns the
permutation, and `checkWord S p program` compares it with `p`.
`checkWord_sound` proves membership. Shared subexpressions prevent expansion
of repeatedly composed words into enormous flat lists. Decode with explicit
node and byte limits and reject cycles, forward references and bad indices.

`Chain n` is raw certificate data described below. The checked group shape is:

```text
Group n:
  generators : Array (Perm n)
  chain      : Chain n
  valid      : checkChain generators chain = true.
```

`ofGenerators S` retains the original generator array and produces a checked
chain for exactly its generated subgroup. Duplicates and identity generators
are permitted in the input. The construction may sort and deduplicate its
working generators, but word indices continue to refer to the original array.

An element `Element G` is a permutation with a propositional proof of
`Generated G.generators p`. Its equality is equality of permutations, and
group operations preserve membership. A word is separate certificate data,
not part of element identity. `word? G p` returns a checked membership program
exactly when `p` belongs to `G`.

Two different generator arrays or chains can define the same subgroup. Lean
record equality is not used to express that fact. Define `SameGroup G H`
as equality of their membership predicates and decide it by two subgroup
containment tests. There is no structural `BEq Group` advertised as a
mathematical group-equality operation.

## Orbits and Schreier generators

For a generator array `S`, its symmetric working array contains the nonidentity
generators and their inverses, sorted and deduplicated by image arrays. Run
breadth-first search from a point `a`. Store each discovered point once and
record a parent edge labelled by a working generator. This proves reachability
as well as supplying a transporter.

For every point `x` in the orbit, let `t_x` be the resulting permutation with
`t_x(a)=x` and `t_a=1`. Each `t_x` has a word in `S`. The orbit checker
verifies those words, the images of `a`, and closure of the point set under
every working generator. Reachability proves that the set is contained in the
orbit. Closure proves the reverse inclusion, including any negative answer
to a point-transporter query.

For `s` in the symmetric generators and `x` in the orbit, the Schreier
generator is

```text
h(s,x) = t_(s(x))⁻¹ * s * t_x.
```

It fixes `a`. Prove Schreier's lemma with this multiplication order: these
elements generate the full stabilizer of `a` in the subgroup generated by
`S`. The proof rewrites a word fixing `a` as a product of such generators,
using the successive images of `a`. Verification that each returned generator
fixes `a` alone proves only one inclusion and does not complete this theorem.

## Complete stabilizer chains

The first version fixes the base to `0,1,...,n-1`. It stores singleton
orbits for fixed base points and does not require a minimal base. This avoids
a hidden assumption that some caller-supplied short base is faithful.
Variable bases and base-change optimizations are later work.

Let `S_i` be the generators at level `i`, and `G_i = <S_i>`. A complete
chain proves

```text
G_0 = <S>
G_(i+1) = {g in G_i | g(i)=i}
G_n = {1}.
```

Every generator at level `i` fixes the earlier points. Level `i` contains
the full orbit `O_i` of `i` under `S_i` and representatives `t_x` as above.
Raw data include the level generators, orbit arrays and lookup tables,
representatives, and word programs establishing their provenance. The public
checker verifies:

1. `S_0` is exactly the normalized symmetric input array, with checked
   original-generator references. Every later generator has a checked word
   in the preceding level's generators and fixes the next required point.
   Every level's working array is sorted, duplicate-free, excludes identity
   and is closed under inverses; the checker verifies these conditions.
2. The orbit is duplicate-free, contains its base point, and its stored
   lookup table agrees with its entries. Representatives have words in that
   level's generators, map the base point to the listed points, and use the
   identity at the base point.
3. The orbit is closed under every symmetric generator. The checker recomputes
   every `h(s,x)` and verifies that it sifts to identity through the suffix
   chain. No list of selected Schreier pairs supplied by the producer is
   accepted as exhaustive.
4. Terminal generators are identities, and there are exactly `n` levels.
   All shapes, references, permutation arrays and fixed-point conditions
   are validated before use.

Prove `checkChain_sound` by induction from the terminal level upward. The
already-verified suffix makes its successful sifts membership proofs.
Schreier's lemma proves that the whole stabilizer is in the next group.
The next generators' provenance proves the reverse inclusion. Only after this
induction may a failed sift certify nonmembership in the original group.

### Sifting and order

To sift `p`, start with residual `r=p`. At level `i`, compute `x=r(i)`.
If `x` is absent from `O_i`, stop with a negative verdict. Otherwise replace
`r` by `t_x⁻¹*r`, which fixes `i` and all previous base points. After the
last level accept exactly when `r=1`. The successful decomposition is

```text
p = t_(x_0) * t_(x_1) * ... * t_(x_(n-1)).
```

Prove `sift_iff`: acceptance is equivalent to `Generated S p` for an accepted
chain. A successful sift gives a program in the original generators through
the checked representative words. A failed sift carries the first missing
orbit image or a nonidentity residual and is replayed against the complete
chain. A failed sift against an unfinished chain is not a nonmembership proof.

The Cartesian product of the orbit choices maps bijectively to the group by
the displayed product. Prove injectivity using the first base point where two
choices differ, and surjectivity by sifting. `order G : Nat` is
`product_i |O_i|` and equals the exact cardinality of the generated subgroup.
Use arbitrary-precision natural arithmetic. Group order is not the number of
discovered generators, an orbit size, or a machine-word approximation.

## Deterministic construction

`ofGenerators` uses deterministic Schreier-Sims construction with exact
generator filtering. At level `i`, compute the full orbit and representatives
of `i` under the supplied `S_i`, in the fixed generator/BFS order. Start the
suffix as a complete chain for the trivial subgroup. Stream the Schreier
generators `h(s,x)` in that fixed order.

For each such generator, sift against the current **complete** suffix chain.
If it is already a member, omit it. Otherwise add it to the suffix generator
array and rebuild the suffix recursively at level `i+1`. Preserve words in
`S_i` for the retained generators and representatives. Once all pairs have
been processed, the retained generators generate the full stabilizer and
the suffix is complete. Normalize symmetric working arrays when rebuilding.

This specifies an implementable deterministic first algorithm. It does not
enumerate all elements of `Sym(n)` or all elements of the input group merely
to establish membership or order. Termination is by remaining base length
for recursive calls and finite orbit/generator loops at each level. Each
insertion strictly enlarges the current suffix subgroup, which bounds
insertions within one level-construction call by `log₂(n!)`. This is not a
polynomial-time claim for the whole recursive rebuild implementation.
Record repeated rebuilding in profiles.
An incremental implementation may replace rebuilding once it proves the same
chain invariants and demonstrates its improvement on the required families.

Prove `ofGenerators_checks` for every well-formed generator array, without
assuming a successful randomized trial, a known group order or a complete
classification table. The optional `buildWith budget S` counts point visits,
Schreier pairs, sift steps and certificate nodes. It returns either a group
with a passing chain for exactly `S`, or an incomplete result. Incomplete
results may report verified words or subgroups discovered so far, but expose
no final negative membership answer or exact order of `<S>`.

## Group operations

| Operation | Required result |
| --- | --- |
| `contains G p` | Boolean equivalent to membership, using the checked chain. |
| `word? G p` | A checked program in the original generators exactly when membership holds. |
| `order G` | Exact cardinality from the chain. |
| `orbit G a`, `orbits G` | Sorted point orbits, with all fixed points retained. |
| `transporter? G a b` | A group element sending `a` to `b`, or proof that none exists. |
| `stabilizer G a` | A checked generated group equal to the complete point stabilizer. |
| `pointwise G points` | The subgroup fixing every listed point, by iterated point stabilizers. |
| `isSubgroup H G` | True exactly when every element of `H` belongs to `G`. |
| `sameGroup G H` | True exactly when the generated subgroups are equal. |
| `conjugate p G` | The group generated by `p*s*p⁻¹`, with that membership correspondence. |
| `join G H` | The least subgroup containing both, generated by concatenating their generators. |
| `isTransitive G` | True exactly when the natural action is nonempty and has one orbit. |
| `isNormal H G h` | Normality of `H` in `G`, with `h` proving containment. |
| `isAbelian G` | True exactly when all group elements commute. |
| `rank G p`, `unrank G k` | Inverse maps between `Element G` and `Fin (order G)`. |
| `sampleWith draw G` | Unrank one index supplied by `draw` for the positive bound `order G`. |
| `elementsWith cap G` | Every group element once if `order G ≤ cap`, otherwise an explicit size-limit result. |
| `leftCosetsWith cap G H h` | A complete left transversal when `h` proves `H ≤ G` and the index fits the cap. |

`orbit` and `transporter?` can use the generator BFS and its checked orbit
certificate without constructing a new chain. For `stabilizer`, use the
complete Schreier generators at the requested point, then construct a checked
chain for them. It is not enough to filter the original generators for those
that happen to fix the point. Repeated points in `pointwise` do not change
the result.

Subgroup containment checks the original generators of `H` for membership in
`G`. Positive certificates provide their word programs in `G`; a negative
certificate identifies one original generator of `H` and replays its failed
sift against `G`'s complete chain. These two directions establish decidability
of containment. `sameGroup` is containment in both directions. It is not a
decision for abstract isomorphism or conjugacy of subgroups.

`join` rebuilds a checked chain from the concatenated generators and proves
the least-upper-bound property for membership. `isNormal` checks
`s*h*s⁻¹ ∈ H` for every symmetric generator `s` of `G` and original
generator `h` of `H`. Prove this equivalent to invariance under conjugation
by every element of `G`. `isAbelian` checks commutation of every pair of
original generators and proves that this suffices for the entire group.
Negative answers retain a failing generator pair and its checked computation.
Neither test enumerates all elements. Empty and singleton actions have
`isTransitive` false and true respectively; every trivial group is abelian.

### Ranking and sampling

Use the stored orbit order at each chain level as the digit order, with
level zero most significant. If `d_i` is the index of the representative
selected by sifting and `o_i = |O_i|`, define

```text
rank(p) = sum_i d_i * product_(j>i) o_j.
```

`unrank` obtains the digits by exact division and remainder and multiplies
the representatives in the sifting order. All radices are positive. Prove
both inverse equations and the rank bound without enumerating the group.
The unique element of a trivial group has rank zero, including at degree
zero. Checked raw-index and raw-permutation entry points reject out-of-range
indices and nonmembers. Ranking is relative to the stored chain, and need
not agree for different presentations of the same group or with the
lexicographically sorted output of `elementsWith`.

`sampleWith` takes an effectful bounded-index source returning an element of
`Fin (order G)` and applies `unrank`. It preserves any explicit source
failure. Its mathematical uniformity contract is conditional on a uniform
input index: every group element has exactly one preimage and thus
probability `1 / order G`. The computational library proves the bijection;
the companion proves the corresponding finite-distribution statement.
This does not assert that a pseudorandom seed is a source of true uniform
randomness. Do not obtain bounded indices by a biased modular reduction.

Element enumeration uses the orbit-choice bijection, not a second closure
algorithm, and sorts image arrays lexicographically for the public result.
The cap is tested against the exact order before allocation. A size-limit
answer is not an empty group or an empty list.

### Left cosets

`leftCosetsWith` uses cosets `gH`. For representatives `x,y` in `G`,
`xH=yH` exactly when `y⁻¹*x` belongs to `H`. Start from `H` and perform
BFS under **left** multiplication by the symmetric generators of `G`.
Compare a new coset with stored representatives using that membership test.
This is a well-defined left action, even when `H` is not normal.

Prove that the resulting cosets are disjoint and cover `G`, and that their
number satisfies `order G = count * order H`. The index computed from the
two exact orders is a natural number by this finite-group theorem. Compare
it with the cap before enumeration. An optional runtime cancellation returns
an incomplete traversal and makes no coverage claim. Representatives are
deterministic for the input presentation, but are not a canonical transversal
of the abstract subgroup. Equality of outputs from different presentations
is equality of coset sets, not equality of representative lists.

Inverting a left transversal produces a right transversal. Do not silently
compare left representatives with an oracle's right transversal, and do not
construct a quotient group unless normality has separately been proved.

## Finite actions and induced representations

An `Action G α` contains an executable action of `Element G` on `α`, with
proofs of the identity and left-composition laws. The action depends on the
permutation value, not its membership word. Supplying permutations for the
original generators alone does not establish an action: all relations of
`G` must be respected. Built-in action constructors prove the laws directly.

Provide componentwise actions on tuples (including repeated entries),
subsets represented by bit vectors, and partitions represented by canonical
block labels. A partition covers all points by nonempty disjoint blocks;
labels are assigned by least member. The empty partition is valid exactly
at degree zero. The partition action permutes blocks as an unordered family;
an ordered tuple of subsets has the distinct componentwise action.

Generalize orbit BFS, transporters and Schreier's lemma to such actions,
retaining words as permutations of the original `Fin n`. Equality and any
hash/ordering operations on action objects must be proved consistent.
An orbit certificate again proves reachability and generator closure.
Schreier generators give the full stabilizer of the object in the original
group, even if the action has a kernel.

For a finite invariant domain, supplied as a duplicate-free array of
objects, `actionImage` returns a checked group on the array indices and
the homomorphism induced by the action. Check closure under symmetric input
generators before constructing index permutations. The returned group is
exactly the image, with a preimage word for each image generator. It need
not be isomorphic to `G`. `actionKernel` computes the intersection of the
object stabilizers by successive Schreier stabilizer computations in the
original group. Prove `kernel = {g | every domain object is fixed}`,
`order G = order kernel * order image`, and injectivity precisely when the
kernel is trivial. The action on an empty domain has trivial image and
kernel `G`. Enumeration order is part of the returned identification with
`Fin k`; it must not depend on an unrecorded hash-table traversal order.

Do not allocate every tuple, subset or partition to run a single orbit
query. Orbit discovery has an explicit object budget; `actionImage` has an
explicit domain/allocation budget. A complete orbit can supply its own
invariant domain. Budget exhaustion returns incomplete data and cannot
justify an absent transporter or a final kernel/image claim.

## Set stabilizers and complete subgroup search

All group arguments in this section have the same natural action degree.
Provide the following operations with exact membership characterizations:

| Operation | Membership or transporter contract |
| --- | --- |
| `setStabilizer G A` | `g ∈ G` and `g(A)=A`. |
| `setTransporter? G A B` | A `g ∈ G` with `g(A)=B`, or a complete proof that none exists. |
| `intersection G H` | Membership in both `G` and `H`. |
| `centralizer G H` | `g ∈ G` commuting with every element of `H`. |
| `normalizer G H` | `g ∈ G` with `g H g⁻¹ = H`. |

For centralizers and normalizers, `H` need not be contained in `G`.
Centralizing one permutation is the cyclic-subgroup specialization.
The center is `centralizer G G`. If a set transporter `t` exists, all
transporters form `t * setStabilizer G A`; prove this coset description.
Unequal subset cardinalities give immediate nonexistence. Empty and full
subsets have stabilizer `G`, including at degree zero.

Use deterministic backtracking through the checked base and stabilizer
chain, with constraint refinement on partial point images. At depth `i`,
a prefix representative `p` describes exactly the coset `p G_i`; all its
elements agree with `p` on the preceding base points. Children extend by
every representative in the next stored orbit. Prove this is a disjoint
decomposition of the parent, inherited from the orbit-choice bijection.

Required constraint tests include:

- For set stabilizers and transporters, prescribed membership colours on
  each assigned source/target pair. For every point orbit `O` of `G_i`, require
  `|A ∩ O| = |B ∩ p(O)|` (with `B=A` for a stabilizer).
- For intersection, simultaneous extension of the assigned images in `H`.
  Maintain a transporter coset in `H` using successive point stabilizers
  and orbit tests. Failure proves no element of `H` extends that prefix.
- For centralizers, `p(h(x))=h(p(x))` for each generator `h` whenever the
  relevant images are assigned; propagate forced images and reject conflicts.
- For normalizers, preservation of the `H`-orbit equivalence relation and
  orbit cardinalities under the partial map. At leaves check conjugates of
  all `H` generators, using subgroup equality or finite-order equality to
  prove normalization. Orbit agreement alone is not sufficient.

Each pruning rule proves that no satisfying element extends the rejected
prefix. Invariant refinements must respect the operation: a normalizer may
permute the orbits of `H`, so assigning each such orbit a fixed colour is
unsound. The algorithm refines while descending and does not first enumerate
the whole group or the power set and filter it.

For subgroup outputs, accumulate a checked subgroup `K` from successful
leaves, adding a generator only when it is not already in `K`. Each such
generator passes the defining predicate, and the predicate is proved closed
under the group operations. A subtree `p G_i` can also be skipped when
`p ∈ K` and `G_i ≤ K`; the checker validates both membership claims.
This rule accounts for a subtree whose solutions are already represented.

The completeness certificate records every child, a checked impossibility
reason, or checked containment in the final `K`. The checker reconstructs
all child choices, validates the defining predicate on `K`'s generators,
and replays every prune. Prove `checkSearch_spec`: the accepted subgroup
contains exactly the elements satisfying the defining predicate. A checked
chain for `K` alone does not prove this equality. For a negative transporter
answer every branch must be excluded; a positive answer needs only a checked
word and the action equation.

Exact forms terminate on the finite chain tree. `...With budget` forms count
visited nodes, refinement work, sifts and certificate nodes; exhaustion is
explicitly incomplete. Discovered subgroups are lower bounds only. There is
no polynomial runtime or polynomial certificate-size promise for this search.
General finite-action orbit/Schreier computations provide a separate useful
route when the orbit is small; their full orbit-closure certificate supplies
the same completeness guarantee.

## Block systems and primitivity

`blocks G pairs` computes the least `G`-invariant equivalence relation on
`Fin n` containing the supplied point pairs. Return its canonical partition
and prove both generator invariance and minimality among invariant
equivalence relations containing those pairs. Its classes form a block
system; in a transitive action they have equal sizes. Empty seeds yield
singletons, and seeds joining all points yield the indiscrete partition.

Use union-find with a queue of pairs. Each effective merge of classes
containing `x,y` enqueues `(s(x),s(y))` for every symmetric generator `s`.
Termination follows from at most `n-1` effective merges for positive `n`,
plus the finite initial seed queue. Prove generator invariance at the fixed
point and that each merge is forced in every admissible equivalence relation.
This proves minimality without enumerating all set partitions. Certificate
replay checks forced merges and final closure, not just the output partition.

The public `isPrimitive` convention requires degree at least two and
transitivity. At a fixed point `a`, compute the minimal block system seeded
by `(a,b)` for every `b != a`. The action is primitive exactly when every
one of these systems is indiscrete. Prove this criterion: every nontrivial
block system of a transitive group has a nonsingleton block containing `a`.
Return either a complete primitivity certificate, a nontrivial invariant
partition, or the explicit small-degree/intransitivity obstruction. Degrees
zero and one are not primitive under this convention; correspondence with
other conventions must retain the degree hypothesis.

`blockAction` numbers the blocks canonically, checks that each generator
permutes them, and returns the induced image and kernel as for finite
actions. Intransitive groups may have invariant partitions with unequal
block sizes; do not silently assume transitivity in this constructor.
The kernel fixes each block setwise and may permute points inside it.

## Normal closure, core and derived series

For `H ≤ G`, `normalClosure G H` is the least normal subgroup of `G`
containing `H`. Start from `H` and insert conjugates of current subgroup
generators by symmetric generators of `G`, using membership to omit redundant
insertions and rebuilding complete chains when the subgroup grows. Stop only
when a full pass adds nothing. Every insertion lies in the desired normal
closure, while terminal generator checks prove normality. Together these
prove minimality, rather than just closure of the returned subgroup.

`core G H` is the greatest normal subgroup of `G` contained in `H`. Start
from `H` and repeatedly intersect the current subgroup with its conjugates
by symmetric generators of `G`, until a full pass is unchanged. Each step
retains every normal subgroup contained in `H`, and the fixed point is
normal. Require complete intersection certificates for the steps. A
strict increase or decrease of finite subgroups changes order by a factor
of at least two; this supplies a termination bound for both iterations.
The action on left cosets `G/H` has kernel `core G H`; prove this link
using the coset action, with its domain-size budget.

Fix `[x,y] = x*y*x⁻¹*y⁻¹`. `derived G` is the normal closure in `G` of
commutators of original generator pairs. Prove that this equals the subgroup
generated by commutators of all group elements. Merely generating the listed
commutators without normal closure is insufficient. `derivedSeries` iterates
this operation until the subgroup is trivial or two consecutive subgroups
are equal. `isSolvable` is true exactly in the former case. A nontrivial
fixed point is a perfect subgroup; retain its equality certificate and the
complete preceding series for a negative answer. Prove termination and the
usual solvability equivalence. Budget exhaustion cannot mean nonsolvable.

Certificate replay checks the inclusions, complete search results and terminal
normality/equality tests of these constructions. A purported normal closure
with extraneous elements, or a purported core omitting valid elements, must
be rejected even if the proposed result happens to be normal.

## Direct and wreath products

`directProduct G H`, for degrees `n,m`, acts on `Fin (n+m)` using disjoint
consecutive supports. Return checked factor embeddings and projections and
prove that their images commute, intersect trivially and generate the output.
Prove the unique factor decomposition and order `order G * order H`.
Degree-zero factors are permitted. Preserve all explicitly declared fixed
points in the embeddings.

`wreathProduct G H` uses the imprimitive action of `G wr H`, with `G` of
degree `n > 0` and `H` of degree `m`. Label `(i,j)` by `j*n+i`, so each
block has size `n`. For `f : Fin m -> Element G` and `h : Element H`, set

```text
(f,h)(i,j) = (f_(h(j))(i), h(j))
(f,h) * (g,k) = (l, h*k),  where l_j = f_j * g_(h⁻¹(j)).
```

Generate one copy of every `G` generator in every block, and lifts of the
`H` generators that permute blocks without changing the within-block index.
Include all blocks even when `H` is intransitive. Prove the multiplication
formula, injective embeddings of each base factor and the top group, the
unique decomposition, and order `(order G)^m * order H`. The projection
onto `H` has kernel the base group, with conjugation permuting its factors.
The companion identifies this with the semidirect product `G^m ⋊ H`.

Nonempty blocks are a necessary hypothesis: at `n=0` the action loses the
top group. Reject that raw request explicitly; do not claim the abstract
wreath product has been represented faithfully on an empty set. At `m=0`
the specified product is trivial. Degree one for `G` is permitted. The
product action on functions is outside this constructor's contract.

## Edge cases and graph-isomorphism integration

At degree zero, `ofGenerators #[]` is the trivial group of order one, with an
empty chain and no point orbits. At every degree an empty generator array
defines the trivial group and every point is fixed. Singleton orbits do not
disappear when the largest moved point is small. Chains and coset budgets
must handle order one, cap zero, and stabilizer equal to the whole group.

The first consumer is the subgroup generated by graph automorphisms found by
`HexGraphIso`. If each input generator is checked to preserve the graph,
this library proves that the generated subgroup consists of automorphisms
and gives its exact order. It does **not** prove that every automorphism of
the graph is in that subgroup. That equality requires the canonical-search
completeness theorem in `HexGraphIso`, independently of Schreier-Sims.
Neither nauty's reported order nor a matching orbit partition discharges it.

The initial library imports no transitive-group catalogue and assigns no
database identifier as a group classification. A later Galois-group library
may use membership and subgroup containment here, but a database of candidate
subgroups needs versioned provenance, checked embeddings and stabilizers,
and a separate completeness policy. Named test groups below are constructed
from explicit permutations and mathematical definitions.

## Mathlib companion and trust boundary

`HexPermGroupMathlib` provides a multiplicative equivalence
`Hex.Perm n ≃* Equiv.Perm (Fin n)`. For `S`, define the mathematical group
as `Subgroup.closure` of the converted input generators. The headline
`checkChain_spec` states that an accepted chain decides membership in this
subgroup and that its orbit-size product is the subgroup's cardinality.
The producer corollary applies to every `ofGenerators S` result.

Transport the orbit and transporter biconditionals, stabilizer equality,
containment/equality decisions, element-list completeness and left-coset
coverage. Identify `Element G` with the elements of the Mathlib subgroup.
Prove permutation-order agreement with `orderOf`, including degree zero.
Every mathematical statement retains the explicit action degree.

Extend correspondence to sign and cycle type, joins, normality and
abelianness, and the rank/unrank equivalence. Transport uniform measure on
`Fin (order G)` across that equivalence to prove the sampling contract.
Identify finite actions with Mathlib actions and their induced monoid
homomorphisms, retaining the image and kernel rather than asserting
injectivity. Relate checked set search to set stabilizers and transporter
cosets, intersections to subgroup infima, and centralizers and normalizers
to their defining subgroup predicates. The companion theorem
`checkSearch_spec` transports complete search to these mathematical groups.

Prove correspondence for invariant equivalence relations, minimal block
systems and primitivity under the stated degree/transitivity conventions.
Identify normal closure, core, derived subgroup and solvability by their
universal properties or defining membership predicates. Finally give
multiplicative equivalences for direct products and the stated wreath
semidirect product, compatible with all embeddings, projections and actions.
These are required parts of the library's scope, not optional examples.

The companion is to be classified `correspondence_only: true` at activation,
with absence class **correspondence-only-layer** and build-only examples in
`HexPermGroupMathlib/Tests.lean`. Runtime tests and performance are owned below.

Computational conformance owner: `HexPermGroup`.

Computational performance owner: `HexPermGroup`.

Expose permutation operations, straight-line-program evaluation and chain
checks for kernel replay. A compiled producer supplies untrusted certificate
data. A kernel proof applies `checkChain_sound` and the Mathlib correspondence
to an accepted literal check. Replay budgets are separate from search budgets.
For large groups, fail explicitly when the certificate is too expensive.
There is no `native_decide`, new axiom, trusted external group-order call or
unverified classification table. Checker completeness includes the whole
Schreier-pair family, not merely the words the producer elected to return.
Action closure, search-tree coverage, forced block merges and normal-subgroup
iterations are also replayable; action laws supplied as proofs remain
kernel-checked. An external image table with no action-law proof cannot
cross this boundary just because each generator image is a permutation.

## Conformance and comparisons

Create `conformance/HexPermGroup/{Conformance,EmitFixtures}.lean`,
`conformance-fixtures/HexPermGroup/permgroup.jsonl`, and
`scripts/oracle/perm_group_gap.py`. The always-available small-degree reference
enumerates closure of the generator set by a simple queue and full image-array
equality. It must not implement stabilizer chains. It independently checks
membership, order, every point orbit, point stabilizers and coset partitions.
Extend this reference by filtering the enumerated elements for subgroup
search, by using all conjugates for normal closure/core and all element
commutators for derived subgroups. Enumerate set partitions only at small
degrees to independently check minimal block systems and primitivity. It
must not reuse the production backtracking prunes or union-find algorithm.

The required external oracle in the existing `oracles` profile is
[GAP](https://gap-system.github.io/gap/doc/ref/chap43_mj.html). Use explicit
image permutations via `PermList`, `Group`, `StabChain` with deterministic
settings, `Size`, membership, `Orbits`, `Stabilizer`, `IsSubgroup`, and
`RightTransversal`. Supply `[1..n]` explicitly for point-orbit operations so
GAP's moved-point convention does not omit fixed points. Translate between
zero-based and one-based indices. In GAP permutations act on the right, so
replay a Hex product by reversing the GAP multiplication order. Test this
adapter on two noncommuting permutations, not only cycles in an abelian group.
Convert right transversals by inversion before comparing left-coset partitions.

Use the following additional GAP operations on their shared domains. See
the [actions reference](https://gap-system.github.io/gap/doc/ref/chap41_mj.html),
[groups reference](https://gap-system.github.io/gap/doc/ref/chap39_mj.html) and
[products reference](https://gap-system.github.io/gap/doc/ref/chap49_mj.html).

| Hex surface | GAP oracle/comparator |
| --- | --- |
| Sign, cycle type, joins, elementary predicates | `SignPerm`, `CycleLengths` with the explicit domain, `ClosureGroup`, `IsTransitive`, `IsNormal`, `IsAbelian`. |
| Finite actions and kernels | `Orbit`, `Stabilizer`, `ActionHomomorphism`, `Image`, `Kernel`, with `OnTuples`, `OnSets` or the corresponding partition action. |
| Set search and subgroup search | `Stabilizer` with `OnSets`, `RepresentativeAction`, `Intersection`, `Centralizer`, `Normalizer`. |
| Blocks and primitivity | Seeded `Blocks` on transitive domains, `IsPrimitive`, and `ActionHomomorphism` on the returned blocks. |
| Normal and derived subgroups | `NormalClosure`, `Core`, `DerivedSubgroup`, `DerivedSeries`, `IsSolvableGroup`. |
| Products | `DirectProduct`, `WreathProductImprimitiveAction`, `Embedding`, `Projection`. |

GAP's `Blocks` requires transitivity; intransitive invariant-equivalence
queries use the independent partition reference. Its seed puts all listed
points in one block: compare single-pair seed queries, and use the independent
reference for arbitrary independent pair constraints. Check minimality on
the small fixtures before comparing seeded partitions; for an unseeded
witness do not expect an arbitrary choice of block system to match.
Translate small-degree transitivity/primitivity conventions explicitly.
Product comparison must
record the domain identification furnished by the factor embeddings.
GAP may omit declared fixed points: use explicitly lifted image generators
for such cases, and time its native product constructors only on domains
where their representation agrees with the recorded identification.

Rank numbers are presentation-dependent and need not match GAP enumeration
indices. Test both inverse equations and exhaustive bijectivity on small
groups. For sampling feed every possible bounded index exactly once and
check that every element occurs once; statistical frequency tests are not
a replacement for the proof. GAP `Enumerator` indexed access and `Random`
are informational throughput comparisons only, with setup and random-source
costs separated from prepared-group access. Record their methods; do not
claim that a timed random method supplies the same uniformity proof.

Fixtures record schema version, action degree, original generator arrays,
operation, query permutations or points, exact order, orbit partitions, and
complete/limited status. For membership and transporters compare truth and
verify returned witnesses, not program text. For stabilizers compare subgroup
membership rather than arbitrary generator lists. For transversals compare
cosets, not choices of representatives. Store the complete raw input for
replaying every failure.
Action fixtures also record the domain ordering, object encoding, induced
generator images and kernel; product fixtures record factor degrees and
embeddings. Ranking fixtures record the chain, index and expected image
array. Normalize partitions and cycle types before comparison.

Cover the trivial group, cyclic and dihedral actions, symmetric and alternating
groups from explicit generators, direct products on disjoint point sets, and
intransitive groups with fixed points. Include duplicate generators, inverses,
noncommuting products, a group with order exceeding 64 bits, and two different
presentations of the same subgroup. Use a point stabilizer requiring a
Schreier generator absent from the original list.

Include sign multiplicativity on noncommuting inputs, fixed-point cycle
types, redundant joins, nonnormal subgroups and nonabelian generator pairs.
Test tuple repetitions, empty subsets, unordered partitions whose blocks
are exchanged, and actions with nontrivial kernels. Use primitive and
imprimitive transitive groups, intransitive partitions with unequal block
sizes, and block seeds that force several rounds of merging. Include a
normalizer element swapping two `H` orbits to catch unsound fixed colours.
Compare every positive and negative set-transporter verdict at small degrees.

Normal-structure examples include the core of a point stabilizer in `S_3`,
the normal closure of a transposition, the derived series of `S_4`, and the
nontrivial perfect group `A_5`, all from explicit permutations. Test direct
products with empty-degree factors, `C_2 wr C_2`, a nonabelian base group,
and a top group with several orbits and fixed blocks. Check the displayed
wreath multiplication formula on arbitrary factor elements, not just orders.

Corrupt a representative, a word index, one orbit entry, a lookup table,
one stabilizer generator and a terminal stage. An incomplete chain for a
proper subgroup must not certify the larger group's order or a negative
membership result. Test a nonnormal subgroup's left cosets to detect
multiplication-direction mistakes. Force construction and output budgets.
Also corrupt a search prune, omit one search child, delete a needed block
merge, forge generator closure of an action domain, swap an induced image,
and propose an incorrect normal closure/core that is nevertheless normal.
The checker must reject each corruption. Exercise every new search, action
and iteration budget without turning incomplete output into a negative
mathematical answer.
The companion also proves that no action of `C_2` can send its generator
to a three-cycle. This build-only counterexample exercises the relation-law
requirement on action constructors; generator bijectivity is insufficient.

The GAP throughput comparator is **informational**, using the same named
operations through a persistent process. GAP has different permutation storage,
chain heuristics and group-specific methods, and does not emit Lean replay
certificates. Time construction on fresh groups and membership/order on
already prepared groups separately. Report the methods and options actually
used, including any recognized special-group shortcut. Do not time cached
GAP order against a fresh Hex construction.

Permutation array operations are covered by GAP's permutation operations and
`Order`; cycle serialization is outside the timed region. Certificate
generation and kernel replay have
**no-comparable-surface-in-named-comparator** for this protocol and require
their own native and kernel measurements. All arithmetic uses exact integers.

## Complexity, benchmarks and placement

A permutation composition or inverse costs `O(n)` image operations. A sift
through the fixed base costs `O(n²)` with full residual permutations and
constant-time orbit lookup. A point orbit without materialized transporter
permutations costs `O(n*r)` point actions for `r` symmetric generators.
Materializing all its representatives adds up to `O(n²)` image operations.
Certificate program evaluation costs `O(n*W)` for `W` program nodes.

If level `i` has `r_i` symmetric generators and `o_i` orbit points, checking
all Schreier pairs requires `sum_i o_i*r_i` pair checks, each including a
suffix sift. State the resulting upper bound in these actual dimensions,
plus the sizes of the provenance programs. Chain construction's recursive
rebuilds are separate measured work. Do not claim a standard optimized
Schreier-Sims complexity for this specific implementation without a proof.
Element enumeration is at least output-linear in `n*|G|`, and transversal
enumeration in the index. The first coset BFS may compare against every
stored coset, so its membership-test count can be quadratic in the index.

Ranking and unranking use `O(n²)` image operations plus `O(n)` exact
mixed-radix arithmetic operations on integers of `O(log₂(|G|+1))` bits,
with suffix products prepared once. Sign and cycle-length histograms are
linear in degree. Abelianness uses a quadratic number of generator-pair
commutation checks; normality uses the product of the two generator counts
in conjugation/membership checks.

For an action orbit of size `q` and `r` symmetric generators, charge
`O(q*r)` object actions separately from object equality, storage and word
construction. Search cost is measured by visited prefixes, constraint work
and sifts, including complete certificate replay. Both may be exponential
in the natural action degree. Optimizations must preserve complete coverage.
Union-find block closure uses at most `n-1` effective merges and
`O(k+r*n)` queued pairs for `k` seeds; with union by rank and path compression
the union-find work is `O((k+r*n)*α(n))`. Primitivity repeats the pair-seeded
closure at most `n-1` times after checking transitivity.

For normal closure/core/derived series, record strict subgroup changes,
conjugations, intersections and chain rebuilds; the finite-order bound on
changes does not bound the cost of an individual intersection. Product
construction materializes `r_G+r_H` generators of degree `n+m` for a direct
product, and `m*r_G+r_H` generators of degree `n*m` for a wreath product,
before chain construction. Include these allocations and their explicit
degree limits in bounded constructors.

Required families in `bench/HexPermGroup/Bench.lean`:

| Family | Work exercised |
| --- | --- |
| `degree-generators` | Degree and redundant generator count varied separately. |
| `chain-shape` | Cyclic, dihedral, symmetric, alternating and intransitive groups with different stabilizer depths. |
| `membership` | Positive words and negative queries failing at early and late chain levels. |
| `stabilizers` | Arbitrary point and pointwise stabilizers with nontrivial Schreier generators. |
| `containment` | Equal presentations, strict inclusions and failed inclusions. |
| `enumeration` | Element count and subgroup index, with output limits enforced. |
| `element-access` | Sign, cycle type, rank/unrank and supplied-index sampling, including orders above 64 bits. |
| `finite-actions` | Tuple, subset and partition orbits; image and kernel with varied domain size. |
| `subgroup-search` | Set transporters/stabilizers, intersections, centralizers and normalizers with varied pruning effectiveness. |
| `blocks` | Minimal invariant equivalences and primitivity, varying degree, seed count and block sizes. |
| `normal-structure` | Joins, normality, abelianness, normal closure, core and derived series of soluble and nonsoluble groups. |
| `products` | Direct and imprimitive wreath products, varying both factor degrees, generator counts and top-group orbits. |
| `certificate-replay` | Construction, program generation and kernel replay separated by certificate size. |

Use [benchmarking](../../SPEC/benchmarking.md)'s ordered complexity modes, named
hardware and complete output checks. Profile orbit construction, full-array
composition, sifting, suffix rebuilding and word storage. Benches remain
Mathlib-free. Extend existing conformance/oracle scripts and the single CI
job, with scientific timing on the existing dedicated hardware workflow.

Implement in this order:

1. `HexPermGroup/Perm.lean`: extract the shared permutation representation,
   elementary operations, cycles and order. Adapt graph-isomorphism imports
   without changing its canonical-search behavior.
2. `Word.lean` and `Orbit.lean`: generated-subgroup semantics, checked programs,
   BFS, transporters and Schreier's lemma.
3. `Chain.lean` and `Check.lean`: raw chain data, sifting, complete checking,
   and the membership/cardinality theorems.
4. `Build.lean`: deterministic construction and its acceptance theorem.
   `Subgroup.lean`, `Coset.lean` and `Rank.lean`: basic subgroup operations,
   cosets, elementary predicates, rank/unrank and supplied-index sampling.
5. `Action.lean`: proof-bearing finite actions, generic orbits and Schreier
   stabilizers, induced images and kernels.
6. `Search.lean`: complete backtracking and checkers for set transporters,
   set stabilizers, intersection, centralizer and normalizer.
7. `Blocks.lean` and `Normal.lean`: invariant equivalence closure,
   primitivity, normal closure/core and derived series.
8. `Product.lean`: direct and imprimitive wreath products with their maps.
9. Corresponding modules in `HexPermGroupMathlib/`, conformance, benchmarks
   and `HexManual/Chapters/HexPermGroup.lean` complete every surface above.
   Develop each correspondence and its tests alongside the relevant
   computational module; this ordering does not defer all proofs to the end.

The manual should use rotations and reflections of an indexed polygon to
compute a point stabilizer, distinguish orbit size from group order, and
construct a membership word. A second example gives the same subgroup by
different generators and compares its nonnormal-subgroup cosets. A graph
example explicitly distinguishes the subgroup of known automorphisms from
the theorem that this subgroup is the entire automorphism group.
Further examples show the dihedral action on opposite-vertex blocks and
its kernel, a set transporter, a rank/unrank round trip, the derived series
of `S_4`, and the four-point action of `C_2 wr C_2` with explicit embeddings.

Both libraries start planned at phase zero. Activation and graph-isomorphism
migration must satisfy its existing conformance and benchmark requirements,
including the required cactus sweep for source changes. Release the new
dependency before changing the published graph-isomorphism pins, through the
monorepo's release manifest and guarded synchronization workflow.
