# hex-perm-group

Finite permutation groups on a fixed indexed set, represented by generators
and a checked stabilizer chain. The first version provides constructive
membership, exact group order, point orbits and stabilizers, subgroup
containment, equality of generated subgroups, and bounded element/coset
enumeration. Deterministic Schreier-Sims construction produces certificates
whose completeness is checked independently of the construction.

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

The initial group operations are for the natural action on `Fin n` only.
Setwise stabilizers, subgroup intersection, normalizers, centralizers,
conjugacy classes, group isomorphism, general action interfaces, character
tables, random element generation and transitive-group databases are later
extensions. Conjugating a given subgroup by a given permutation is in scope.
There is no claim that a generator list is canonical under conjugacy.

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

Cycles omit fixed points, begin with their least point, follow the permutation's
direction and are ordered by their first point. Prove that the disjoint cycles
reconstruct the permutation. `Perm.order` is the lcm of the cycle lengths,
with empty lcm one. Prove both `p^order = 1` and minimality among positive
exponents. No integer factorization is required. The degree-zero permutation
is the identity and has order one.

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
polynomial-time claim for the whole recursive rebuild implementation. Record repeated rebuilding in profiles.
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

## Conformance and comparisons

Create `conformance/HexPermGroup/{Conformance,EmitFixtures}.lean`,
`conformance-fixtures/HexPermGroup/permgroup.jsonl`, and
`scripts/oracle/perm_group_gap.py`. The always-available small-degree reference
enumerates closure of the generator set by a simple queue and full image-array
equality. It must not implement stabilizer chains. It independently checks
membership, order, every point orbit, point stabilizers and coset partitions.

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

Fixtures record schema version, action degree, original generator arrays,
operation, query permutations or points, exact order, orbit partitions, and
complete/limited status. For membership and transporters compare truth and
verify returned witnesses, not program text. For stabilizers compare subgroup
membership rather than arbitrary generator lists. For transversals compare
cosets, not choices of representatives. Store the complete raw input for
replaying every failure.

Cover the trivial group, cyclic and dihedral actions, symmetric and alternating
groups from explicit generators, direct products on disjoint point sets, and
intransitive groups with fixed points. Include duplicate generators, inverses,
noncommuting products, a group with order exceeding 64 bits, and two different
presentations of the same subgroup. Use a point stabilizer requiring a
Schreier generator absent from the original list.

Corrupt a representative, a word index, one orbit entry, a lookup table,
one stabilizer generator and a terminal stage. An incomplete chain for a
proper subgroup must not certify the larger group's order or a negative
membership result. Test a nonnormal subgroup's left cosets to detect
multiplication-direction mistakes. Force construction and output budgets.

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

Required families in `bench/HexPermGroup/Bench.lean`:

| Family | Work exercised |
| --- | --- |
| `degree-generators` | Degree and redundant generator count varied separately. |
| `chain-shape` | Cyclic, dihedral, symmetric, alternating and intransitive groups with different stabilizer depths. |
| `membership` | Positive words and negative queries failing at early and late chain levels. |
| `stabilizers` | Arbitrary point and pointwise stabilizers with nontrivial Schreier generators. |
| `containment` | Equal presentations, strict inclusions and failed inclusions. |
| `enumeration` | Element count and subgroup index, with output limits enforced. |
| `certificate-replay` | Construction, program generation and kernel replay separated by certificate size. |

Use [benchmarking](../benchmarking.md)'s ordered complexity modes, named
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
   `Subgroup.lean` and `Coset.lean`: the remaining group operations.
5. `HexPermGroupMathlib/Correspondence.lean`, conformance, benchmarks and
   `HexManual/Chapters/HexPermGroup.lean`.

The manual should use rotations and reflections of an indexed polygon to
compute a point stabilizer, distinguish orbit size from group order, and
construct a membership word. A second example gives the same subgroup by
different generators and compares its nonnormal-subgroup cosets. A graph
example explicitly distinguishes the subgroup of known automorphisms from
the theorem that this subgroup is the entire automorphism group.

Both libraries start planned at phase zero. Activation and graph-isomorphism
migration must satisfy its existing conformance and benchmark requirements,
including the required cactus sweep for source changes. Release the new
dependency before changing the published graph-isomorphism pins, through the
monorepo's release manifest and guarded synchronization workflow.
