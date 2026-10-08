# Sturm proof and API review

The [computational assessment](computational.md) treats all 48 handwritten
declarations in the four production modules exported by `HexSturm`.
The [companion assessment](companion.md) treats all 78 handwritten declarations
in the seven production modules exported by `HexSturmMathlib`, including their
private helpers. Generated record projections and elaborator declarations are
not separate entries. The prepared-domain fields are assessed with their
structure. The [manifest](manifest.json) records the reviewed module hashes and
declaration names at source commit
`3052375699bc4a94b56c8b4cd839bb916c9c0a5e`. The documentation changes accompanying
this assessment do not change their definitions, statements or proof bodies.

## Contracts and public imports

The computational modules require explicit coefficient operations and sign
functions. They do not install field or order laws on storage. Their equalities
characterize the executed operations and literal bindings. Semantic guarantees
require the companion's zero-reflecting interpretations and arithmetic/sign
laws. Domain correspondence works over ordered fields; general root-sum
semantics additionally requires a real-closed target.

Producer domain/totality and arbitrary-certificate soundness have separate
proof routes. `query_isSome` characterizes when the actual query succeeds;
`query_iff` gives its full domain/value contract. `check_sound` assumes only
accepted literal replay, not producer provenance, and proves both domain and
value. Prepared objects retain their exact producer equation, whereas arbitrary
certificates can use different valid chains. The review does not replace these
contracts with successful fixtures.

`import HexSturm` exports preparation, queries, counting, remainder reduction
and certificate translation. `import HexSturmMathlib` exports the seven
reviewed semantic modules in the monorepo. Some shared Tarski semantic inputs
still live under `adapters/`; a successful development import does not establish
their availability from candidate published companion packages. Their migration
and pins remain in the [publication plan](../real-closure-publication.md).
Computation stays independent of Mathlib and Tau Ceti.

## Polishing and validation

The restoration projections use `simp` to expose literal fields without opening
the private constructor. Retargeting, prepared query/count agreement, cache
agreement and operation transport have explicit characterizing lemmas. Semantic
theorems retain their hypotheses rather than asking automation to choose an
interpretation. The short names distinguish mathematical domain, produced
queries and accepted replay within their owning namespaces. No computational
implementation is duplicated by the companion.

The source documentation covers the public restoration projections and the
non-obvious private clearing/embedding helpers. Scaling identities allow zero
input factors; the separate positivity lemma supplies the conditions needed by
accepted chain translation. Sturm count agreement uses root-free **endpoints**,
not a root-free interval.

The existing `HexSturmMathlibTests` target builds canonical and noninjective
domain/query examples, accepted and rejected literal replay, stale context
rejection, rational/integer certificate translation, endpoint retargeting and
prepared count laws. Its ordinary-kernel axiom guards cover representative
public contracts. The semantic replay examples in
`HexSturmMathlib.Tests.Replay.Semantics`, built by `HexQuerySemantics`, additionally
exercise real-root meaning and the complete noninjective query contract. The
reduced-query module has its own axiom guards. This source review reuses these
controls; it adds no alternate conformance implementation or performance timing.
`HexSturm.Conformance` supplies the computational acceptance/refusal controls
and field/integer differential cases. Its differential comparisons are not an
independent semantic oracle; the integer oracle belongs to `HexRealRoots`.

## Remaining phase acceptance

This assessment prepares proof/API acceptance against merged contracts. Both
libraries remain Phase 3: [#10577](https://github.com/kim-em/hex-dev/issues/10577)
owns their prerequisite/performance readiness. Phase 5 requires that owner's
Phase-4 attestation, a sorry-free build and passing conformance. Phase 6 also
requires final lint/docstring/use assessment and the declared computational
regression check. A source assessment or kernel axiom guard does not establish
those performance requirements. The existing chapter supplies documentation
without advancing Phase 7 ahead of Phase 6.
