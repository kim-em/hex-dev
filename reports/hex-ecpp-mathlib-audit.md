# HexECPPMathlib audit

The owned contract is `HexECPPMathlib/SPEC/hex-ecpp-mathlib.md`. The companion
owns mathematical interpretation, unconditional soundness, explicit replay,
compact decoding and optional native/PARI elaboration. Core completion is
independent of this bridge; companion phase gates require the core's matching
phase. The independent skeptical source review is retained in
`ecpp/companion-audit/phase2-review.txt` and `phase2-followup.txt`.
The follow-up confirms all nine initial findings resolved. Its remaining
source concerns are addressed by acknowledged stop-file shutdown, preserving
kill errors, bounded expression expansion before evaluation, a complete pinned AINTLIB module-root inventory for the
graph freshness closure, and a cross-module auxiliary-name collision probe.
The conformance contract and proof-track assignment are explicit.


## Mathematics and trust

For every prime divisor `p` of the subject, the gcd-of-six check excludes
characteristic two and three, and the discriminant unit check supplies the
elliptic curve. `startingPoint_rep` and `add_rep` interpret accepted points
and all accepted affine interpreter branches in Mathlib's actual point
group. Failed inverse checks provide no correspondence claim. Concrete
composite tests use `n = 35`, `p = 5, 7` and `n = 49`, `p = 7`.

The prime-divisor order argument uses binary replay, finite group cardinality
and the pinned AINTLIB Hasse capstone. The strict size guard is checked before
natural subtraction; its inequalities contradict the least-prime-divisor
bound for composite subjects. `natPrime_of_check` and `natPrime_of_checkAt`
have raw checker acceptance as their sole mathematical premise. Published
kernel dependency guards allow only `propext`, `Classical.choice` and
`Quot.sound` in the upstream Hasse capstone, bridge bounds and headline
primality theorems.

The independently justified Frobenius API is retained. It reuses Mathlib's
point/group and finite-field theory and provides equivalences for rational
points, Frobenius fixed points and the kernel of one minus Frobenius. Its
normalizing lemma supports `simp` without unfolding its definition.

## Executable boundaries

Explicit replay accepts only closed exposed constructor data with checked
subject binding. Compiled replacements, hidden constants, metavariables and
proof gaps are rejected before evaluation. Persistent let environments and
fuel-charged variable lookup bound both raw syntax traversal and expanded
constructor-data traversal. Shared trees cannot bypass the total-node bound.

Compact certificates expose constructor data to importing module files;
export instructions specify `public import`. Auxiliary definitions retain
Lean's fresh-name indices and separate module prefixes with a numeric
component. Native and PARI generation validate raw data, convert it to the
frozen representation and kernel-check that exact representation before a
suggestion or exclusive file write. Language-server elaboration does not
spawn generation or write exports.

PARI readers use bounded non-blocking polls and observe cancellation even
when a descendant escapes the process group while holding a pipe. Exceptional
cleanup kills the owned unreaped group, cancels and collects both readers,
then reaps the leader. A kill failure still collects readers and attempts a
non-blocking reap, preserving the original operation error; waiting
unconditionally for a live process after an OS kill failure would violate
bounded cleanup. No kill or wait follows a successful reap. Windows is
rejected before spawning. Escaped-descendant tests use private stop files
rather than signaling a reparented PID.

## API and verification

The base umbrella imports mathematical correspondence, explicit elaboration
and compact decoding. Native and PARI are explicit optional imports and
explicit Lake build roots. The POSIX pipe sidecar alone is precompiled and
owns its native archive; the bridge has the usual non-precompiled Mathlib
settings. Public declarations have docstrings, the actual companion module
prefix is checked by the Mathlib linter, and published regression tests
exercise its characterizing API.

`ecpp/companion-proof-surface.md` maps public surfaces to the declared proof
probe root and ordinary executable conformance. Retained 65/256/512-bit
replays and native corpus evidence are credited. There are no admitted proof
gaps or new axioms. Both protocol scripts check generated certificate text,
fresh importing modules, frozen replay and exclusive export behavior.

## Standalone publication gates

The prepared Lake skeleton directly requires Mathlib and AINTLIB at the
compatible monorepo commits; AINTLIB supplies `HasseWeil`. AINTLIB is pinned to upstream main commit
`ab1451487da02cd4483d0e2cdb2cc9e44bbbac17`, which provides the module-compatible
Hasse import boundary. Mathlib is required last so a fresh Lake update selects its compatible
transitive revisions rather than AINTLIB's older dependency lock. A local
source-split build of the prospective closure passes the companion and its
published test target, including frozen importing-module replay and axiom
guards. The release dependency closure contains the core
and primality bridge, with no HexIntFactor prerequisite.

Publication requires a fresh standalone build against the published core,
the published trust-test target and a guarded publishing dry run. The companion mirror contains its approved initial Lake skeleton, including
the exact dependency lock. A guarded dry run against the live release baseline
plus the actual new bootstrap heads passes without a force override or push.
The core mirror currently contains only its bootstrap skeleton. Local
source-split preparation does not satisfy the build-against-published-core
gate. Both new repositories also need approved publishing-token grants for
Contents and Workflows read/write before a real release. Those publication
obligations remain in issue 10586 after source phase completion.
