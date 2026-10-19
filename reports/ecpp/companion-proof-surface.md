# Companion proof and executable surfaces

`HexECPPMathlib` takes the proof track. Its computational partner owns the
compiled benchmarks and scientific performance evidence. There is no
Mathlib-linked benchmark executable or companion timed-region profile.

`libraries.yml` declares `bench/HexECPPMathlib/ProofProbe`; the
`HexECPPMathlibProofProbe` Lake target explicitly lists the modules in that root
and the existing single CI job builds that target on every PR.

| Public surface | CI proof probes | Executable or protocol checks |
| --- | --- | --- |
| `ecpp using` literal/exposed data | `Ecpp17`, `Direct65`, `NativeDirect` | `Conformance`, `ModuleImports`, `Reject`; subject substitution, closed terms, hidden data and compiled replacements |
| `ecpp_cert%` compact reification | `Reify65`, `NativeReify`, `Replay65`, `Replay256`, `Replay512` | `CompactFixtures`, `CompactReject`, `NodeBudget`; malformed text, inverse transcript, node and syntax allocations |
| Native suggestion/generation | `NativeGeneration` runs the native tactic; frozen replay uses `Native128_0`, `Native256_0`–`Native256_2`, `NativeHoldout`, `NativeValidation`, `NativeUpdated` | `NativeConformance`, `NativeFixtures`, `scripts/ci/check_ecpp_native.py`; exact generated suggestions replayed in fresh modules, search exhaustion, exclusive exports and language-server policy |
| PARI suggestion/generation/export | `Replay65`, `Replay256`, `Replay512` cover frozen replay only; generation/export evidence is the protocol | `scripts/ci/check_ecpp_pari.py`; actual generated suggestion text, fresh exported importing module, absent GP and duplicate export; `PariProcess` covers budgets, cancellation, timeout and pipe-holding descendants |
| Frozen replay | `Replay65`, `Replay256`, `Replay512`, native frozen corpus | Both protocol scripts replay with GP/search absent; `HexECPPMathlib.Tests.ModuleReplay` imports an exposed certificate from a module |
| Soundness/correspondence | `Ecpp17`, replay probes | `HasseAudit`, `SoundnessAudit`, `CompositeDivisors`; published `HexECPPMathlib.Tests` guards upstream Hasse and both headline theorem dependencies |

The remaining probe files supply matched import/reification baselines and
shared fixture support. `Pock17` records the adjacent primality route for
comparison; it is not credited as ECPP acceptance. The native corpus reports
and retained replay measurements in this directory provide the existing
fresh-module evidence; they are not new compiled performance claims.

The protocol scripts build the generated certificate source and replay the
exact returned `Try this:` text. Proof existence alone is insufficient. The
published test target additionally pins an exact native suggestion with
`#guard_msgs`, checks frozen module replay and runs the companion API linter.
The 512-bit extension adds `Tests.Native512` for the exact full generated
suggestion, `Tests.Frozen512` for verbatim replay with generation absent, and
`Native512Baseline`, `Native512Reify`, `Native512Direct` for separate fresh-module
phase measurements in [native512/proof-phases-v2.json](native512/proof-phases-v2.json).
The 512-bit protocol script is retained as manually collected generation/export
evidence. CI builds the two acceptance modules once each, without duplicating
the protocol script's three generation calls and three frozen proofs.
Measured endpoint evidence admits these guards under SPEC/CI.md: each module
completed in 12–16 seconds locally; together they add roughly 30 seconds to the
existing single build job, outside the separately capped Bench verify step.
The full protocol takes roughly one to three minutes in the retained
shared-host observations and remains manual. Both acceptance modules use the default heartbeat allocation.

Replay admits 512-bit subjects and 32 total certificate nodes. Native search
defaults to 256-bit subjects; the explicit 512-bit policy enforces at most
twenty ECPP rows and 32 total nodes during backtracking. An embedded terminal
`PrimeCert` consumes its full tree allocation as well; row depth and total
nodes are independent. `NodeBudget` tests acceptance at 32 nodes, rejection
at 33, shared constructor-data preflight and shared expression expansion.
Generation validates the complete raw certificate before compact conversion
and kernel-checks the exact frozen representation before suggesting or writing.
