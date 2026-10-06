# hex-ecpp-mathlib

The Mathlib companion interprets checked HexECPP arithmetic over every prime
divisor of a candidate and proves unconditional `Nat.Prime` soundness. Its
[computational prerequisite](../../HexECPP/SPEC/hex-ecpp.md) remains
Mathlib-free.

## Proof obligations and missing infrastructure

Use the nonsingular affine point type and abelian group law from
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`. Its point constructors
distinguish infinity from an affine point with a nonsingularity proof. The
bridge must prove the Hasse bound it uses; an available upstream proof may be
imported after checking that its statement and dependencies meet this SPEC.
The required bridge obligations are not consequences of a checksum or of
primality correspondence:

1. **Reduction and addition.** For each prime `p ∣ n`, construct the short
   curve `y²=x³+a*x+b` over `ZMod p`; derive `p > 3` and nonzero
   discriminant from the checked unit equations. Interpret accepted raw
   points as Mathlib nonsingular points. Prove the addition and scalar
   correspondence along the actual checker branches.
2. **Finite points and Hasse.** Derive finiteness from
   `WeierstrassCurve.Affine.nonsingularPointEquiv`, and prove for every
   prime `p > 3` and every nonsingular short curve over `ZMod p` the
   integer inequality `t*t ≤ 4*p`, where
   `t = (p : ℤ) + 1 - (#E(ZMod p) : ℤ)`. This is the Hasse bound;
   in real notation it implies `#E(ZMod p) ≤ (sqrt p + 1)^2`.

   The intended proof route constructs the degree of endomorphisms over an
   algebraic closure and proves its nonnegativity, the parallelogram law,
   `deg [m] = m²`, `deg Frobenius = p`, and
   `deg(1-Frobenius) = #E(ZMod p)`. The last identity requires separability
   of `1-Frobenius` and identification of its kernel with the rational points.
   Derive `deg([m]-[k]Frobenius) = m²-t*m*k+p*k²`; nonnegativity for all
   integers `m,k` then gives `t² ≤ 4p`. This is a substantial mathematical
   infrastructure milestone, not a local consequence of the point group.

   Coordinate-ring norm/degree arguments and division-polynomial degree
   formulas may support this proof, but they do not by themselves establish
   the isogeny/endomorphism degree theory or Frobenius/kernel-count identity.
   Develop the missing bridge modules, checking for compatible proved upstream
   work before duplicating it; import or inline with attribution when
   available. An alternative complete Hasse proof is admissible. Empirical
   point counts and caller-supplied Hasse hypotheses do not close the milestone.
3. **Order and size.** If `q` is prime, `Q ≠ 0`, and `q • Q = 0`, then
   `Q` has exact order `q`, hence `q ∣ #E(ZMod p)`. Derive `q ≤ #E(ZMod p)`
   using finiteness and nonempty cardinality. Combining Hasse with the exact
   integer bound excludes every prime divisor `p` satisfying `p*p ≤ n`.
4. **Primality and recursion.** A composite natural `n > 1` has such a
   prime divisor. Induct over the certificate, using the existing bridge
   theorem for bases, to obtain the unconditional headline theorems:

   ```lean
   theorem natPrime_of_check {c : Hex.ECPP.Cert}
       (h : Hex.ECPP.check c = true) : Nat.Prime c.subject

   theorem natPrime_of_checkAt {n : Nat} {c : Hex.ECPP.Cert}
       (h : Hex.ECPP.checkAt n c = true) : Nat.Prime n
   ```

These theorem names live in `Hex.ECPP`; reserve `prime_of_check` and
`prime_of_checkAt` for the optional `Hex.Nat.Prime` transports. Their only
premise is acceptance;
there is no hidden hypothesis that the subject is prime, that Hasse holds,
that a provider was correct, or that the child has an independently asserted
subject. No declaration using `sorry` or an axiom closes this milestone.
Do not expose a working-looking primality tactic before all these obligations
are proved. A standalone arithmetic checker can be developed first, but
its successful execution is not yet the promised primality API.

## Proved Hasse infrastructure

The bridge imports the proved `WeierstrassCurve.hasse_bound` from
TauCeti and restates its integer-square formulation for `Fintype.card` in
`Hasse/Degree.lean`; `Hasse.lean` specializes it to `ZMod p`. The imported
proof computes, over an algebraic closure, the degree of `r π − s` for the
Frobenius isogeny `π` as the binary quadratic form `q r² − a r s + s²`
whenever the characteristic does not divide `s`, and bounds the
discriminant `a² − 4q` of this nonnegative form by zero. The exact imported
source is selected by the lockfile.
`Hasse/Frobenius.lean` independently identifies rational points with the
fixed points and kernel of `1 − Frobenius` under base change.
`#print axioms` on the restricted Hasse and headline soundness theorems
allows only `propext`, `Classical.choice`, and `Quot.sound`.

## Explicit proof elaboration

Provide an opt-in bridge tactic `ecpp using c` for a closed literal `n` and
a closed certificate literal or an exposed constant `c` containing such data,
targeting `Nat.Prime n`. In `module` files, cross-module certificate constants and every checker
definition needed by replay must be `@[expose]`. Restrict the accepted term
form to constructor data and exposed data constants; reject arbitrary
computations. Bound traversal, unfolding, numeral size and total certificate
nodes, including embedded `PrimeCert` data, before evaluating the checker.
Constructor-data let bindings charge every occurrence after substitution.
Shared terminal trees are traversed with a decreasing node allocation before
reification or checker evaluation.
It evaluates `checkAt` using compiled code as an untrusted preflight, reifies the certificate, and emits
`natPrime_of_checkAt` with kernel-replayed acceptance. The emitted Boolean
proof must reduce through exposed Lean definitions and existing approved
arithmetic fallbacks. A failing preflight, resource interruption, or failed
kernel replay emits no proof. The supplied-certificate Elab module registers
no `norm_num` handler or automatic primality fallback.


The explicit `ecpp using c` policy admits subjects and individual
certificate numerals through 512 bits, at most 131072 inspected syntax nodes,
32 total certificate nodes including embedded `PrimeCert` nodes, and 1024
inverse witnesses per ECPP step. The frozen 65-, 256- and 512-bit certificates
have fresh-module kernel proof probes. These bounds constrain replay; they
do not guarantee successful production for every prime of these sizes.

## Compact certificates and explicit PARI production

`HexECPPMathlib.Compact` provides `ecpp_cert% "rows" using leaf`. The string
is a bounded PARI vector or integer, and the leaf is explicit closed
`Hex.Nat.PrimeCert` constructor data. Conversion uses the existing core
converter with `defaultImportBudget`, checks the result and reifies the full
raw constructor certificate. An auxiliary exposed data definition keeps the
enclosing term small without requiring users to change recursion options.
The auxiliary body has no compiled replacement or proof assumptions.
No PARI invocation or terminal certificate search runs during replay.

PARI generation is POSIX-only and rejects other platforms before spawning.
Users explicitly import `HexECPPMathlib.Pari` to enable
`primality? (method := pari)` for `Nat.Prime` and `Hex.Nat.Prime` goals. The
generator runs `gp` from PATH with `-q -f`, passing only the evaluated natural
numeral to `primecert` in a private temporary request file. Null stdin keeps
the original process-group handle intact; remove the request file on every
exit path. It uses no shell and ignores GP startup files. The initial PARI
stack is 64000000 bytes; GP startup preferences cannot
enable automatic stack growth. The process is limited to 30000 milliseconds,
16448 stdout bytes and 4096 stderr bytes. On POSIX, cancellation and exhaustion
terminate the process group with KILL and reap the child. If the OS rejects
the kill, collect readers and attempt a nonblocking reap, then report cleanup
failure alongside the original error; do not wait indefinitely for a live
process. Collect both pipe
readers before reaping the leader, and never wait or kill that PID again after
reaping it. Readers poll fresh, nonblocking POSIX pipe descriptors and observe
cooperative cancellation independently of EOF, including pipes retained by
descendants outside the original process group. The small Mathlib-free IO
sidecar is precompiled; the mathematical bridge is not. Missing
executables, process failures, framing errors, conversion diagnostics and
timeout are reported distinctly. Conversion failure alone proves no
compositeness.

Before offering a suggestion or writing a file, verify subject-bound
acceptance and the resulting proof with the Lean kernel. The suggestion
contains compact frozen data and its explicit Hex leaf, so applying it removes
both the CAS call and endpoint search. The producer and converter are not
proof dependencies. Ordinary `primality` imports and behavior are unchanged;
the PARI module registers no automatic fallback or `norm_num` handler.

`#ecpp_export MyCertificates.Prime cert for n` writes
`MyCertificates/Prime.lean`, relative to the process working directory. The
file uses the module system, publicly imports `HexECPPMathlib.Compact`, and
contains one `@[expose] public` certificate declaration named
`MyCertificates.Prime.cert`. After generation, remove the command, put
the file under the project's Lean source root, use `public import MyCertificates.Prime`,
and use `ecpp using MyCertificates.Prime.cert`. Parent directories may be
created; existing files are never overwritten. The command runs only in batch
builds: the language server displays instructions to run `lake build +Module`
and performs no process invocation or file write. This prevents partially typed
subjects from creating files. Exclusive creation enforces
that rule even when another process creates the path concurrently. Export is
an explicit source-generation operation, not an ordinary build dependency.

## Conformance and evidence

Before fixing an elaborator policy, measure kernel replay of the 65-bit
fixture, then successive chain lengths and subject sizes. The single CI job
kernel-replays the admitted frozen certificates and small branch/boundary
probes. Promote larger fixtures to kernel proofs only after fresh-module
evidence establishes their fit within the existing CI budget. Compiled-only
coverage does not establish an elaborator size ceiling or fast kernel replay.
If the first fixture exceeds the budget, keep the elaborator unreleased and
optimize replay with proved equivalence before promising a supported ceiling.

The bridge adds actual kernel proofs for its admitted replay fixtures, rejects
subject substitution and corrupted witnesses, and exercises reductions at
small prime divisors without assuming the parent subject prime. Audit the
headline theorem's dependencies and imports; no core module or runtime bench
may import Mathlib. Oracle comparison uses independently generated PARI
certificates and primality results, not PARI's Boolean validator as a proof
or as an oracle that must agree on every malformed certificate.

Measure proposal conversion, compiled checking, certificate size, reification,
and kernel replay separately. Fresh importing modules measure end-to-end
`Nat.Prime` proof production alongside the existing Pocklington route on
shared supported subjects; hard inputs report its bounded exhaustion rather
than forcing an unfair total fallback. Compare compiled verification with
PARI verification on the same accepted subjects and disclose the stronger
Hex leaf checking and differing formats. No external program emits the same
Lean kernel proof, so external validation is not a proof-production comparator.

Select replay/parser policy defaults only from measured endpoint evidence;
keep the mathematical checker total independently of those public budgets.
Document exact limits and failure outcomes before enabling the elaborator.
Follow the fixed trial-major and adjacent alternating `AB`/`BA` schedules in
[benchmarking](../../SPEC/benchmarking.md), retain every completed shared-host run,
and keep runtime benches Mathlib-free. Extend the existing single CI job's
conformance/oracle script; add no workflow or matrix.


## Implementation ownership

`HexECPPMathlib/{Reduction,Hasse,Order,Soundness,Elab}.lean` and
`HexECPPMathlib/Hasse/{Degree,Frobenius}.lean` own the bridge. The degree and
Frobenius infrastructure may come from a proved compatible upstream library;
its exact version is recorded by `lake-manifest.json`, not this SPEC. The
bridge's source registration does not by itself imply release or phase
progress.

## References

- [Sutherland, elliptic-curve primality proving, Lecture 11](https://math.mit.edu/classes/18.783/2023/LectureNotes11.pdf): prime-order certificates and the Hasse argument.
- [PARI `primecert` documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#primecert): supplied certificate format and terminal prime conventions.
- [PARI ECPP implementation](https://pari.math.u-bordeaux.fr/lcov-report/basemath/ecpp.c.gcov.html): exact integer size comparison and strong-nonzero check.
- [Mathlib affine points](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean): group-law interface; use the project's lockfile for the version built here.

## Native search elaboration

`HexECPPMathlib/Native.lean` provides the explicit
`primality? (method := ecpp)` route and certificate export. Its executable
producer is owned by the computational SPEC. It validates raw data and
kernel-checks the unconditional proof before suggesting or exporting compact
frozen data. It introduces no registration on ordinary `primality` and no
CM proof dependency. The native search ceiling is admitted separately from
the supplied-certificate replay ceiling. Both native public commands accept
optional `(bits := 256)` or `(bits := 512)` before the optional seed; omission
selects 256, and other policy values fail before search. The 512-bit policy is
`Hex.ECPP.public512Budget`; importing Native alone does not change ordinary
primality dispatch.

Native row depth and replay node counts are separate allocations. The bridge
clamps the default native depth to the converter's 20-row ceiling. For the
512-bit policy it allows a terminal call after 20 rows (search depth 21), and
enforces at most 20 rows and 32 total nodes during search and memo reuse. Replay additionally
counts every embedded terminal `PrimeCert` node and its ECPP base wrapper:
rows + 1 + terminal nodes must be at most 32. A shallow terminal tree can
therefore exhaust replay even when both search depth limits were respected.
Generation passes the complete proposal through `certProof` and its replay
preflight before any suggestion or export; this exhaustion is a clean resource
failure. Reified ECPP natural fields and inverse lists use raw natural
literals, avoiding frontend `OfNat` wrappers while preserving the values and
the unchanged 131072-node inspection ceiling. Conformance includes an accepted 31-node terminal with its base
wrapper, both literal and compact replay, and rejection when a row raises the
total to 33.

## Automatic native fallback

`HexECPPMathlib.Auto` is a separate optional module. Importing it enables a
bounded native ECPP fallback for ordinary `primality?` on both `Nat.Prime` and
`Hex.Nat.Prime` goals, via the upstream version-1 `SuggestionExtension`
boundary. The ordinary ECPPMathlib umbrella, `Native`, `Pari`, core ECPP and
upstream primality umbrellas do not import Auto. Enablement follows transitive
imports, so a downstream public import of Auto enables it in its own importers.
Register Auto in the monorepo Lake roots and the release manifest build modules.
It introduces no GP invocation,
`norm_num` handler, ordinary `primality` handler, integer-factorization route,
or change to SQUFOF dispatch. This fallback does not depend on publication.

Pocklington construction and its registered factor providers run first with
their existing policies. A success retains its certificate and exact suggestion.
Only ordinary non-composite exhaustion permits ECPP. An exhausted 521-bit
construction remains outside ECPP's 512-bit production ceiling; the extension
must decline before search and explain its ceiling. All other validation and
interruption rules at the upstream boundary apply unchanged.

A single Mathlib-free `Hex.ECPP.autoBudget (bits : Nat)` definition owns the
automatic allocation and is shared by Auto and its compiled experiment driver.
The initial automatic policy is one native seed, 0, for every admitted subject,
with no subject-specific seeds, factors, certificates or discriminants. Use
`public512Budget` for 257--512 bits and the existing default native policy for
smaller inputs with the existing public 20-row depth clamp, reducing both
to at most 1024 candidates, 8192 roots, 4096
nonresidue draws, 4096 point draws, 4096 factor-work units and 1000000 scalar
additions. The 512-bit policy additionally caps polynomial and root work at
1048576 each. Retain their existing finite depth, memo, output, row, total-node,
terminal, order and local retry limits; do not enlarge smaller-input limits.
A zero Pocklington attempt limit disables automatic ECPP. A larger desired
ECPP allocation uses explicit `primality? (method := ecpp)` instead; show that
hint only for shared-allocation exhaustion, not local/portfolio decline.
There is no new tactic budget option. Replay limits remain unchanged. Search
retains its initial bounded terminal-construction call, charging its reserved
factor package even if the preceding larger construction failed. This can
produce a terminal-only success; a genuine elliptic success has at least one row.

All recursive native work consumes one allocation. Return its charged counters,
resource cause and unresolved subject on bounded exhaustion. The final diagnostic
retains the Pocklington attempt count and original unresolved obligation and
separately names the ECPP seed, actual allocation, spent counters and failure.
Do not sum different methods' counters or describe ECPP exhaustion as evidence
of compositeness. Successful native proposals go through the existing compact
conversion and exact finite replay preflight. The producer returns only the
complete frozen suggestion. The upstream caller elaborates that exact syntax
and kernel-checks one auxiliary theorem before assigning the original goal,
with no separate `checkWithKernel`. Syntax elaboration retains the existing
bounded internal data-recursion ceiling of 65536 used by Compact and Elab;
final auxiliary-theorem acceptance runs outside that internal override under
the caller's recursion setting. Preserve caller heartbeats and cancellation,
with system checks at the phase boundaries specified upstream. Do not create
a fresh task/process to escape accounting or silently raise arithmetic evaluator
thresholds. User-controlled finite resource settings must be documented for
acceptance examples which require them. No evidence with `maxHeartbeats 0`
attests automatic acceptance.

The generated suggestion contains `ecpp using (ecpp_cert% "rows" using leaf)`
for `Nat.Prime`, or the existing `Hex.Nat.prime_iff` transport for the core
predicate. It contains every replay row and its explicit terminal `PrimeCert`;
it invokes neither Auto nor native production. Exact `#guard_msgs` examples
must pin the complete suggestions for both predicates, including a genuine
elliptic success where full current Pocklington/ECM construction exhausts.
Replay those verbatim in fresh modules importing Compact without Auto or Native,
with GP unavailable. Preserve exact successful Pocklington suggestions.

Before claiming the initial policy as an accepted automatic route, retain
experiments over the frozen native512 tuning/holdout corpus and existing
128/256-bit corpus, including bounded unsuccessful cases. Register the
allocation and fixed seed before runs. Retain every completed shared-host
sample with its CPU and host context; compare construction alone with the
complete optional portfolio using adjacent alternating arms. Measure native
search, compact conversion/preflight, and kernel proof/replay separately using
the existing proof-probe discipline, and include the complete fresh-module cost and phase heartbeat deltas.
The explicit 512-bit production evidence alone does not attest this smaller
policy. Require at least one held-out genuine elliptic success beyond full
current construction; if the declared allocation fails this gate, record the
result and revise the SPEC before changing the policy. Native unsuccessful holdout search must finish within a preregistered 5-second
operational cap on the measurement host, retaining all completed observations
regardless of activity. The claim reports both coverage and the full failure-cost
distribution; this is not a universal wall-clock guarantee. Kernel replay must pass
with declared finite Lean options and existing syntax, row and node ceilings. The initial fixed-seed reduced512
computational feasibility evidence is retained in
[the automatic-fallback report](../../reports/ecpp/auto/README.md); it does not
replace whole-portfolio and finite-option proof acceptance.

Conformance must cover absent registrations, wrong ABI/type/missing producers,
both supported goal predicates, unsupported/open subject rejection, input-bit
boundaries, zero construction allowance and finite search allocations, composite refusal, exhausted construction,
ECPP bounded exhaustion, pre-invocation cancellation and interruption at phase boundaries, failed
preflight/replay, power-expression goals and their arithmetic warnings, and
unchanged explicit `using`/`factor :=`/ECPP/PARI routes. Verify that already
successful construction does not invoke the optional producer. Extend the
existing single CI job and declared proof/conformance targets.

Construction-exhaustion evidence identifies the factor provider, allocation and
source revision. When the automatic provider changes, re-attest the relevant
current-route comparisons; retain older outcomes with their historical policy
labels. A process timeout does not establish construction exhaustion.

## Proof-track evidence

This Mathlib companion has no compiled benchmark track. Literal `ecpp using`,
compact `ecpp_cert%`, native/PARI suggestions and source export, and frozen
replay take the proof track. `libraries.yml` declares the explicit
`bench/HexECPPMathlib/ProofProbe` root built by CI; the public generation/export
routes additionally have protocol conformance that builds generated source
and replays the exact certificate suggestion in fresh modules. The surface
inventory is `reports/ecpp/companion-proof-surface.md`. Existing replay and
native corpus evidence is retained. `NativeGeneration` runs the native tactic
on a representative 128-bit subject. PARI generation/export uses the protocol
script as its evidence because GP is optional; replay probes alone do not
attest generation. The computational partner owns compiled
performance claims and profiles.

## Mixed integer-factorization integration

`HexIntFactorMathlib.Mixed` explicitly imports `HexECPPMathlib.Soundness` and
uses `Hex.ECPP.natPrime_of_checkAt` for every ECPP-bearing factor entry. This
companion gains no dependency on HexIntFactor or HexIntFactorMathlib. Mixed
computational exports import only their computational replay boundary; they
carry checked data, while unconditional primality and `Nat.factorization`
correspondence require the designated factorization companion. Existing ECPP
replay/production policies and legacy primality certificate semantics remain
unchanged. The new consumer separately measures its combined certificate and
subject replay allocations; existing ECPP corpus success alone does not
discharge that integration evidence.

The raw-data reifier and bounded syntax auditor are shared from the explicitly
imported Mathlib-free `HexECPP.ElabData`, with numeral/replay limits in
`HexECPP.Policy`. `HexECPPMathlib.Policy` re-exports the latter for compatibility.
The existing ECPP proof elaborator retains its accepted syntax and admission
policy while this extraction lets mixed computational exports validate data
without importing mathematical soundness.
