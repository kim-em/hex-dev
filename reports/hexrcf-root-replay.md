# Frozen root-table extraction

[`RootReplay`](../adapters/HexRCF/RealCoefficients/RootReplay.lean) checks one
supplied graph for an exact parent context, polynomial and open query domain.
It derives the full derivative queries from the head and preflights every
supplied original divisor before decoding. The owner graph reader checks all
entries, positional fields, versions and earlier-only references; independent
replay checks the complete support and query certificates. No root producer,
isolation, gcd, BKR search or approximation procedure is called.

Positive-degree extraction consumes the already accepted shared table through
`Descriptor.rootsFromTable`. Its correspondence theorem retains the exact
`Descriptor.rootsFrom` equation in the returned result. Constants use the
literal extraction branch. Every successful result preserves all table words,
their uniqueness, the original head/endpoints/full derivative slots and finite
comparator order. The actual owner laws prove the mathematical query domain
and that each emitted descriptor denotes a root of the bound polynomial in
that interval. These conclusions take an actual ordinary-real parent model;
there is no field instance on the representation syntax.

The query domain proves a nonzero squarefree head and root-free open endpoints.
A repeated polynomial requires the owner's decomposition and transport before
this reader. Zero source atoms do not justify a zero query head. Source Ioc
domains remain guard atoms and are separate from the open query domain.
Guard preflight includes constants, empty tables and malformed packets.
Evidence errors are distinct from divisor errors and never mean that no roots
exist. This component does not bind a whole source sentence or authenticate
arbitrary coefficients; the surrounding source/context assembly must do so.

The [frozen fixture](../conformance-fixtures/HexRCF/root-replay.json) contains
four actual owner-produced graphs: X²−2 in (1,2), X²−2 over the whole real line,
the constant 1 and X²+1. Its
[constructor renderer](../scripts/rcf/selected_literals.py) performs no
certificate production. The
[conformance module](../conformance/HexRCF/RootReplayConformance.lean) checks
acceptance, the positive word [1,1], both whole-line words [-1,1]/[1,1], and both
empty output lists. Each checked acceptance/control declaration activates
ordinary kernel diagnostics and rejects unfolding native producers or the
per-descriptor `ofReplay?` path. The reader itself uses shared table extraction.

Changed head/domain/context, omitted BKR support, cyclic references and stale
versions produce the exact structured evidence error. Mutation controls also
confirm that the changed records remain arrays. A zero original divisor gives
the exact divisor error before parsing, even for a zero polynomial. These are
certificate checks, not total-search or false-sentence tests.

The [fresh compilation unit](../conformance/HexRCF/RootReplayOrdinaryConformance.lean)
proves `∃ x : ℝ, x²=2 ∧ 1<x ∧ x<2` from an emitted descriptor, its checked
domain and the owner root interpretation. Local body markers retain the actual
replay laws and reject native producers. Twenty-eight API/fixture inventories
and the fresh source inventory permit only `propext`, `Classical.choice` and
`Quot.sound`; the source uses exactly those three. Imported proof declarations
are leaves in local body scans, not rechecked imported bodies. The generic
adapter uses ordinary public module imports; concrete decoder fixtures retain
the pinned toolchain's non-module import closure.

Default adapter, optional umbrella, existing conformance targets and the
[existing source manual chapter](../HexManual/Chapters/HexRCF/NativeSources.lean)
include this surface. The published rational umbrella remains independent of
the family. There are no AGENTS.md/PLAN.md or workflow/job edits.

Complete interpreted-root coverage, value Nodup and mathematical ordering
still require the SignDet owner's semantic exports for arbitrary supplied
replay. `buildRoots_coverage` and `buildRoots_ordered` presently assume native
production; that equation is not a frozen certificate premise. The precise
[coverage request](https://github.com/kim-em/hex-dev/issues/10331#issuecomment-6126809036)
and [ordering follow-up](https://github.com/kim-em/hex-dev/issues/10331#issuecomment-6129572591)
remain with the coordinator and owner. No generic owner proof is copied here.
General recursive history restoration, complete frozen cell replay, all-live
transport, automatic source/common-field certification and accepted algebraic
completeness remain part of #10358. This is neither a new handler nor closure
of that issue. #10633/#10634's delivered fixed-field interfaces are preserved.

The [validation manifest](data/hexrcf-root-replay/context.json) separates
source-bound integration records from the offline proposal source/output.
Those records are correctness/build observations. No new performance or
scaling claim is made; the retained point/section comparison measures its own
earlier source and does not measure this reader.
