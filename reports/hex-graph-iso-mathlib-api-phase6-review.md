# HexGraphIsoMathlib API Phase 6 Review

## Scope

Reviewed the Mathlib bridge surface for coloured graph isomorphism against
`HexGraphIsoMathlib/SPEC/hex-graph-iso-mathlib.md` and `PLAN/Phase6.md`, in
preparation for the `leanprover/hex-graph-iso-mathlib` split release.

This review covered:

- `HexGraphIsoMathlib/Basic.lean`, the Mathlib-facing coloured graph and
  isomorphism types;
- `HexGraphIsoMathlib/Encode.lean`, the finite encoding and its correspondence
  theorems;
- `HexGraphIsoMathlib/TacticSupport.lean`, the transport lemmas the tactic
  applies;
- `HexGraphIsoMathlib/Tactic.lean`, the `graph_iso` extension;
- the root import `HexGraphIsoMathlib.lean`.

57 public declarations, 40 documented, 70%. This is materially better coverage
than the computational library it bridges.

## Summary

The bridge is well shaped and small, which is the right size for it. The
division of labour is clean: `Basic.lean` provides the Mathlib-facing types,
`Encode.lean` the encoding and the correspondence theorems that justify it,
`TacticSupport.lean` the transport lemmas stated in exactly the goal shapes
the tactic meets, and `Tactic.lean` the shape matcher and the extension
registration.

`colored_iso_iff_canon_eq` (`Encode.lean:165`) is the theorem the layer
exists to prove, and it is stated as a biconditional over the encoded graphs
rather than as two one-sided transport lemmas. `encode_iso_iff` is its
companion in the other direction. Together they let a caller move between
`SimpleGraph.Iso` and the executable decision without unfolding `encode`.

The design decision worth endorsing explicitly: this layer extends the
existing `graph_iso` tactic through `HexGraphIso.Tactic.Extension` rather than
introducing a second tactic name. A user who imports the bridge gets a tactic
that handles both `Isomorphic` and `SimpleGraph` goals, which is what they
want; a second name would have made them choose based on which library a graph
came from.

Two things are worth noting about the release shape rather than the API. This
layer is correctly **not** `correspondence_only` in `libraries.yml`: it carries
an executable proof/tactic route with real elaboration cost, and it owns
Phase-4 proof probes accordingly (see
`reports/hex-graph-iso-mathlib-performance.md`). And its released mirror ships
the library only, so nothing in this review depends on a sidecar the mirror
carries.

I found three polish gaps. None is a correctness issue.

## Findings

### 1. A superseded four-lemma family

`not_isomorphic_of_decideIso?` (`TacticSupport.lean:107`),
`isEmpty_coloredIso_of_decideIso?` (`:116`),
`isEmpty_iso_of_decideIso?` (`:125`) and
`not_nonempty_iso_of_decideIso?` (`:135`) form a complete family covering the
four negative goal shapes through the verified pairwise decision. No tactic
and no consumer references any of them; the only cross-references are within
the family. `Tactic.lean:284-295` applies the parallel
`*_of_not_encode_iso` family instead, which covers the same four shapes.

Two whole families for four goal shapes is one too many. Either the
`_of_decideIso?` route is intended and the tactic should use it for goals
where the pairwise decision is the cheaper kernel obligation, mirroring the
cost-based route selection the computational tactic already does; or it is
superseded and should be deleted. The four lemmas are documented as a family
in the SPEC's Tests section, so this is a design question rather than a
cleanup, and it should be answered before release rather than shipped as two
parallel unexplained surfaces.

Recommended follow-up: `HexGraphIsoMathlib Phase 6: resolve the duplicate
negative transport families`.

### 2. Undocumented public declarations

Seven in `TacticSupport.lean`: `isEmpty_coloredIso_of_decideIso?`:116,
`isEmpty_iso_of_decideIso?`:125, `not_nonempty_iso_of_decideIso?`:135,
`isEmpty_coloredIso_of_not_encode_iso`:154, `isEmpty_iso_of_not_encode_iso`:162,
`not_nonempty_iso_of_not_encode_iso`:171, `isEmpty_coloredIso_of_card_ne`:191.
The pattern is that the first member of each family is documented and the
siblings are not, which reads as an oversight rather than a decision. Since
the families are the tactic's contract with itself, a one-line docstring on
each saying which goal shape it serves would make the tactic's dispatch
readable from the lemmas alone.

Five in `Encode.lean`: `Perm.toEquiv_apply`:37, `Perm.get_ofEquiv`:45,
`encode_adj`:77, `encode_color`:90, `decodePerm_apply`:111. `encode_adj` and
`encode_color` are the primed pair's unprimed halves and are the
characterisation lemmas a caller reaches for first; those two are the ones
that matter.

Three in `Tactic.lean`: `parseGoal?`:100, `mkSide`:164, `proveShape`:238.
These are the three main steps of the extension and are the file's structure.

Two in `Basic.lean`: `Colored.Isomorphic.intro`:64 and `.elim`:68, whose names
carry their statements. Low value.

Recommended follow-up: `HexGraphIsoMathlib Phase 6: document the transport
families and the extension steps`.

### 3. `xOfY` construction names that restate their result type

`coloredIsoOfCheckIso?` (`TacticSupport.lean:70`), `isoOfCheckIso?` (`:79`),
`isoOfCardZero` (`:89`), `coloredIsoOfCardZero` (`:98`) and `isoOfIsIso`
(`Encode.lean:120`) each name the thing they build and then the thing they
build it from, in a namespace that already says what kind of object is in
play. Mathlib's convention for exactly this is a dot-notation constructor:
`Colored.Iso.ofCheckIso?`, `Colored.Iso.ofCardZero`, `Iso.ofIsIso`. The
result type is then carried by the namespace and the name is just the input,
which is shorter and reads at the use site.

This is a five-name rename with a small number of call sites, so it is
cheap; it is recorded rather than done because it belongs with the same pass
that resolves finding 1, which touches the same file and may delete some of
the surrounding lemmas.

## No Follow-Up Needed

No follow-up is needed for the encoding design. `encode` maps an arbitrary
`Fintype`/`DecidableRel` vertex type into `Colored n k` through `listEquiv`,
and `encode_adj`, `encode_color`, `encode_iso_iff` and `canon_encode_indep`
together say that the answer does not depend on the enumeration chosen. That
last one is the lemma that makes the whole approach legitimate and it is
present and documented.

No follow-up is needed for the cheap negative paths.
`isEmpty_iso_of_card_ne` and `not_isomorphic_of_card_color_ne` short-circuit
on vertex-count and colour-class-count mismatches before any search runs,
which is the right optimisation to state as a lemma rather than bury in the
tactic.

No follow-up is needed for the root import. It re-exports exactly `Basic`,
`Encode`, `TacticSupport` and `Tactic`, and carries a module docstring that
describes the layer in four lines. It is what the computational library's
umbrella should look like.

No follow-up is needed for naming in `Basic.lean`, `Encode.lean` or
`Tactic.lean` beyond finding 3. `Shape`, `Side`, `mkSide`, `encodeSide`,
`proveShape`, `vertexType`, `extension` are short verb-noun forms with their
qualifiers in namespaces, which is the house style.

## Verdict

`HexGraphIsoMathlib` meets Phase 6. The correspondence theorems are stated at
the right generality, the tactic extension is the right mechanism, docstring
coverage is 70% with the gaps concentrated in sibling lemmas of documented
families, and there are no dead declarations outside the one superseded family
in finding 1.

That family is the one thing that should be settled before release rather
than after: two parallel four-lemma negative transport surfaces, one of them
unused, is a question a reader will ask and the SPEC currently does not
answer. It is a small question with a cheap answer either way.
