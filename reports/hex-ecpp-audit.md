# HexECPP computational audit

The owned contract is `HexECPP/SPEC/hex-ecpp.md`. Computational ownership
ends at arithmetic acceptance; prime-divisor curve semantics, Hasse and
unconditional primality are owned by `HexECPPMathlib` and #10586. Every
computational dependency is already at phase 7. The core has no Mathlib
import, external runtime oracle, axiom, proof placeholder or native-decision
proof step.

## Declaration and contract inventory

| Module | Reviewed surface | Contract and downstream interface |
| --- | --- | --- |
| Data | `Cert`, `Cert.subject` | Complete raw constructors; the recursive child supplies the sole scalar. No independently claimed order or trace enters checking. |
| Affine | `Point`, `modSub`, `onCurve`, point predicates, `addWithInverse`, `add?`, `checkedAdd?`; four arithmetic lemmas | Canonical residues, unit witnesses, exact vertical/tangent branches and witness consumption. Checked addition returns canonical points satisfying the curve equation. These executable guards remain part of the arithmetic boundary. |
| Replay | `replayBits`, `replay`, `replayDone`, `sizeBound`; prefix facts, bit decomposition and acceptance lemmas | Structural high-to-low `Nat.testBit` schedule; no inverse search; infinity and an empty transcript at completion. Both strict integer inequalities are characterized together, with positivity before subtraction. |
| Cert | `checkStep`, `check`, `checkAt`; constructor equations, canonical/fact projections and subject-binding lemmas | Canonical fields, coprimality to six, discriminant unit, child range, exact size bound, successful scalar replay and checked terminal certificates. `checkAt_eq_true_iff` separates subject binding and arithmetic acceptance. |
| Import | Budget/diagnostic/row structures, `residue`, `inverse?`, normalization, inverse/affine/scalar proposals, row preflight, conversion, parsing and counted conversion | Text bytes/digits/nesting are bounded before JSON allocation; all seven supplied row integer magnitudes, endpoint and row count precede endpoint search. Signed normalization belongs only to conversion. Every resulting complete certificate is checked once at the public boundary. `convert_ok` exposes that guarantee. |
| CM | `jacobi`, `symbol`, `rootValid`, `sqrt?`, `Invariant`, `portfolio`, `normValid`, `norm?`, `traces`, `curves`; bounded private Tonelli–Shanks and Cornacchia loops | Fixed class-number-one proposals; returned roots/norms satisfy their integer equations. Ordinary quadratic, exceptional quartic and sextic twists remain complete within the bounded portfolio. No general class polynomial generator is advertised. |
| Search | Resource/budget/state/result types, fixed leaf/order packages, `charge`, `primeBits`, `certBits`, `replayWork`, `search`, `produce`, `frozenRows`; private proposal/backtracking helpers | Deterministic bounded production through 256 bits. Shared reservations persist across all failed candidates and recursive backtracking. Local point failures permit later twists/orders. Recursive-child diagnostics survive ancestor exhaustion. Size traversal reports failure explicitly. Memoized successes support stateful reuse. `produce_ok` characterizes subject-bound checker acceptance. |

The parser's public kind-only API remains `parsePari`; conversion uses the
located parser so diagnostics retain vector indices. `convertRow` checks
one local step against a supplied child; `convert` checks the complete
chain, avoiding quadratic repeated prefix checking. Native production
likewise charges local proposals and one complete final replay.

The existing binary-length bound in `HexArith.Montgomery.Context` is shared
rather than duplicated. Its public visibility permits the companion to use
it without adding mathematical bridge facts to the computational library.
All nontrivial declarations have source docstrings. Private helpers state
why their fuel, witness order or arithmetic guard is required. Public
constructor and acceptance lemmas keep ordinary callers from unfolding
checker implementations. Point-group interpretation remains a bridge task.

## Conformance inventory

`conformance/HexECPP/Conformance.lean` covers small-prime affine operations,
vertical/tangent and nonunit branches, canonical residues, discriminant
witnesses, subject substitution, inverse corruption/consumption, recursive
terminal acceptance, exact size boundaries and the supplied 65/256/512-bit
chains. `EmitFixtures.lean` feeds independently generated small-modulus
operations and checker cases to `scripts/oracle/ecpp_pari.py`.

`ImportConformance.lean` covers signed/projective normalization, malformed
rows, nonunit denominators, endpoint and child binding, inclusive byte/digit/
integer/row/scalar/inverse limits and each immediate allocation failure.
Oversized endpoints, rows and every row field are distinguished from an
invalid endpoint within budget; input exhaustion precedes endpoint fuel and
search. Located malformed and arithmetic rows retain their original indices.
Excessive bracket nesting is rejected before generic parsing.

`NativeConformance.lean` covers Jacobi/root/norm proposals, all exceptional
twists, nonsquarefree/nonunit rejections, deterministic positive production,
every resource constructor and accounting across backtracking. Zero local
point retries still visits other twists/orders; a capped shared candidate
allocation witnesses that continuation. Recursive-child local diagnostics
are retained against parent portfolio/depth exhaustion. Reusing a successful
stateful memo leaves random state and factor-work charges unchanged.

The complete corpora, successful raw certificates, kernel confirmations,
independent PARI checks and exhausted outcomes remain in `reports/ecpp/native/`.
Native 256-bit capability and supplied 512-bit replay have different contracts.
No native 512-bit support or general success-rate promise follows from either.

## Independent skeptical review

The independent Opus audit and its follow-up are retained verbatim in
`reports/ecpp/audit/phase2-{review,followup}.txt`. The follow-up found no
remaining SPEC blocker. The author verified its findings against source
and current-toolchain builds rather than treating the opinion as authority.

Repeated child-chain checking, lost row diagnostics, parser nesting and
certificate-size traversal findings are resolved in the computational
modules. Conversion additionally binds its final check and `convert_ok` to
`PariCertificate.subject`, rather than using the returned subject tautologically.
Lexical failures now retain their row and ASCII offset; generic JSON failures
retain the parser's location diagnostic. A single pre-parser scan replaces
the duplicate public/private scans, with no external callers of the removed
helper.

A completed portfolio remains the final node-level failure after point
retries, while `SearchStats.lastRetry` retains the distinct local retry
location/resource. This permits continued search across twists/orders and
still exposes local exhaustion. Smaller child obligations take priority over
local retries because checked candidates require `q < n`; choosing among
unrelated failed children is not constrained by the SPEC. Stateful `search`
counters and diagnostics are cumulative by design; callers can reset stats
while preserving the successful memo. `produce` always starts fresh.

The review's proposed removal of checked curve guards and rejection of an
entire twist after one failed point are optional optimizations, not missing
infrastructure. The guards establish the current arithmetic invariant; a
failed point over an arbitrary candidate modulus does not exclude every
other point of that twist. Curve/group proofs remain companion obligations.
The full-memo failure and over-limit endpoint fuel rejection implement the
specified finite allocations. Their documentation states the actual policy.

The Mathlib/Batteries declaration linter passes on the core's imported
modules. `reports/ecpp/audit/lint.json` retains the exact temporary probe,
source fingerprints, toolchain, command and successful result. The probe
imports Mathlib for auditing only; no published computational module does.

## Phase 3 evidence

`audit/conformance.json` records the current-toolchain builds, benchmark
registration checks and all 6,457 independent oracle cases.
`audit/native-corpora.json` reconciles all 32 frozen subjects: 27 accepted
certificates have exactly the retained complete rows and terminal witnesses,
and the five exhausted outcomes agree. The existing kernel replays therefore
remain applicable; unchanged successful measurements are reused. All resource
limits and the local/portfolio/child priority regressions build in the existing
conformance targets. No operation or edge-case coverage obligation remains.

## Proof and API attestation

The complete core build and conformance targets are green on the pinned
Lean toolchain, with zero proof placeholders, axioms or native-decision
steps. Phase 5 requires no additional mathematical bridge proofs.

The declaration inventory above is the substantive Phase 6 review. Each
public operation has a docstring and a downstream purpose; constructor and
acceptance equations characterize ordinary proof use. The old digit scanner
and duplicate bit-length lemma were removed rather than preserved unused.
Checked curve predicates remain executable arithmetic checks, not hidden
Mathlib group-law assumptions. The imported declaration linter is clean.
The adjacent baseline comparison and every operation-specific performance
budget pass, as detailed in `hex-ecpp-performance.md` and its retained
`audit/regression-current-summary.json`. Shared-host observations are not
universal latency guarantees.

## Documentation and split validation

The dedicated core-only Verso chapter builds inside `HexManual`, with live
bounded native search, supplied conversion, checker and resource-exhaustion
examples. The README has the required released-package sections and its
verbatim quickstart builds in a fresh Lake client. The fresh coordinated
split stages exact monorepo prerequisites, carries the public Lake settings
and links native arithmetic without any Mathlib directory or dependency.
`audit/split.json` retains all source fingerprints and build output;
`scripts/release/check_ecpp_split.py` reproduces that validation. The companion
correspondence section is reserved for #10586 and coordinated on that issue.

The managed mirror workflow, closure pins and aggregate/manual integration
pass the release manifest checks. `audit/release-dry-run.json` retains the
successful guarded GitHub workflow and local preview, using the live baseline
and no force override. The initial repository contains only its unmanaged
Lake skeleton; no published managed source was edited. A real coordinated
sync must publish current prerequisites first and have the new repository
selected in an approved publishing token, as required by `PLAN/Releases.md`.
