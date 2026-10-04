# hex-ecpp

Kernel-replayed elliptic-curve primality certificates. A certificate for `n`
reduces primality to a smaller prime `q`, using an explicitly checked
nonzero point of order `q` on a nonsingular short Weierstrass curve modulo
`n`. The executable verifier is Mathlib-free. The elliptic-curve semantics,
Hasse bound, and resulting primality theorem belong to [its Mathlib companion](../../HexECPPMathlib/SPEC/hex-ecpp-mathlib.md).

## Scope and placement

This SPEC owns the `HexECPP` and `HexECPPMathlib` pair. They provide
certificate verification, conversion of supplied
PARI certificates, explicit certificate elaboration, and an opt-in bounded
native CM certificate producer. General Hilbert class polynomial generation,
arbitrary point counting, native CM completeness, automatic search fallback,
and cryptographic curve APIs are outside this scope. Core conversion consumes supplied data. The optional bridge can
explicitly invoke PARI to obtain a certificate, then freeze its inputs for
replay without an external program. Bounded production may exhaust on a prime.

The dependencies are:

| Library | Dependencies | Owns |
| --- | --- | --- |
| `HexECPP` | `HexPrimality`, `HexArith` | raw data, modular arithmetic, inverse-witness replay, recursive Boolean checking, bounded conversion |
| `HexECPPMathlib` | `HexECPP`, `HexPrimalityMathlib`, Mathlib | interpretation over prime fields, scalar correspondence, Hasse bound, unconditional primality soundness, proof elaboration |

There is no dependency from `HexPrimality` back to ECPP and no constructor
added to its existing `Hex.Nat.PrimeCert`. A terminal ECPP certificate embeds
that existing type. The core `prime_of_checkPrime` remains entirely
Mathlib-free. The new executable checker establishes arithmetic facts in the
core; its unconditional primality theorem is available only with the bridge.
A bridge theorem may also transport the result to `Hex.Nat.Prime`, without
claiming that proof is importable from the core library.

The generic field-only curve library proposed in
[future work](../../SPEC/future-work.md#elliptic-curves-over-finite-fields) cannot be
instantiated at `ZMod n` by assuming that the candidate `n` is prime. ECPP
uses partial arithmetic on natural residues and proves its meaning separately
over **every prime divisor** of `n`. No future point-counting or generic
curve package is an implicit prerequisite. Reuse its proved arithmetic later
only if the same composite-modulus and kernel-replay contracts are met.

## Certificate and exact arithmetic

Use namespace `Hex.ECPP`. The following is the intended data shape; helper
structures can factor the fields without changing their meaning:

```lean
inductive Cert where
  | base (c : Hex.Nat.PrimeCert)
  | step (n a b x y discrInv : Nat)
      (inverses : List Nat) (child : Cert)

Cert.subject : Cert → Nat
check : Cert → Bool
checkAt (n : Nat) (c : Cert) : Bool := c.subject == n && check c
```

The subject of a base is `c.subject`; the subject of a step is its `n`.
The step's `q` is **only** `child.subject`, never an independent claimed
prime. Require `3 < n`, `n % 6 = 1 ∨ n % 6 = 5`, and `2 ≤ q < n`.
Bases use the existing `Hex.Nat.checkPrime`, including its small-table and
Pocklington variants. Neither a probable-prime verdict nor the PARI
64-bit cutoff is an admissible base.

The natural fields `a,b,x,y,discrInv` and every used inverse are strictly
below `n`. Reject noncanonical raw data instead of silently reducing the
certificate. Operations reduce their results modulo `n`; signed differences
use a proved modular subtraction, never truncated natural subtraction.
Check

```text
y² ≡ x³ + a*x + b                         (mod n)
(4*a³ + 27*b²) * discrInv ≡ 1             (mod n).
```

Together with coprimality to 6, the second equation ensures good reduction
at every prime divisor. It is a checked unit witness, not an assumption
that the curve is nonsingular because `n` is prime.

Use the standard strict ECPP bound `q > (n^(1/4) + 1)^2`. Replay uses only
integer arithmetic:

```text
n < (q - 1)^2
c := (q - 1)^2 - n
16*n*q < c*c.
```

Prove that these exact inequalities compose with the integer Hasse bound,
including both strict boundaries. Equivalence to the displayed real-root
inequality for `n > 1` and `q ≥ 2` is an optional explanatory bridge lemma.
No floating-point root or kernel evaluation of `Nat.sqrt` is part of checking. The positivity guard
precedes natural subtraction; dropping it makes squaring unsound.

Derive the scalar bits from `child.subject` using the exposed
`HexArith.bitLength` and core `Nat.testBit` operations already used by
kernel-facing modular exponentiation. The replay loop recurses structurally
on the remaining bit count, visiting indices `L-1, …, 0` for
`L = HexArith.bitLength q`. There is no independently supplied scalar,
bit list, or addition chain to bind to `q`.

The certificate contains no purported curve order, trace, cofactor, or
complex-multiplication discriminant: none is necessary to check the
primality implication.

## Affine scalar replay over a candidate modulus

The replay point type is `infinity | affine x y`; infinity has no coordinates.
The initial point `Q = affine x y` must pass the equation check above, so
its reduction is nonidentity at every prime divisor. Begin with `R = infinity`.
For each scalar bit, replace `R` by `R+R`, then by `R+Q` if the bit is one.
At termination require `R = infinity` and **all** inverse witnesses consumed.
The scalar loop and witness-list processing are structurally recursive and
exposed; the checker must not run an inverse algorithm, search, or an
unexposed well-founded recursive helper during kernel replay.

Each addition takes the next witness only when an inverse is needed:

1. Adding infinity returns the other point and consumes no witness.
2. For affine inputs `(x₁,y₁),(x₂,y₂)` with equal `x`, if
   `(y₁+y₂) % n = 0`, return infinity without a witness. This includes
   doubling a point with `y=0`.
3. Otherwise, if both input coordinates are equal, use
   `d = 2*y₁ % n`, `v = (3*x₁²+a) % n`.
4. Otherwise, if their `x` coordinates differ, use
   `d = (x₂-x₁) % n`, `v = (y₂-y₁) % n`, with modular subtraction.
5. Equal `x` with neither opposite nor equal `y` rejects. For cases 3 and 4,
   require a next `u < n` with `d*u % n = 1`; missing or invalid witnesses
   reject. Set `λ=v*u % n`, `x₃=(λ²-x₁-x₂) % n`, and
   `y₃=(λ*(x₁-x₃)-y₁) % n`.

An inequality of residues modulo `n` alone does not establish inequality
modulo a prime divisor. The unit witness is what justifies each division
after reduction. Mixed exceptional cases over different prime factors may
reject; there is no completeness claim for composite-modulus arithmetic.
Prove that accepted additions preserve the curve equation and canonical
residues. The bridge proves each accepted branch is the Mathlib group sum
modulo every prime divisor, then proves the scalar loop represents `q • Q`.

Inverses are a compact arithmetic transcript, not trusted operations.
For an `L`-bit child the schedule executes at most `2L` additions and consumes
at most that many inverses, each of at most the subject's bit length. Thus
node replay has `O(L)` modular ring operations and the inverse data has
`O(L log n)` bits. These operation counts are not measured kernel latency.

## Supplied-certificate conversion and proof elaboration

A separate bounded converter accepts a parsed PARI ECPP vector. Each row
`[n,t,s,a,P]` supplies `m=n+1-t`, a positive divisor `s` of positive `m`, and
`q=m/s`. Perform the divisions in signed/exact arithmetic, reject remainders,
and bind `q` to the next row's subject. Recover
`b=y(P)^2-x(P)^3-a*x(P) mod n`, compute `Q=[s]P` as an untrusted proposal,
and normalize it to affine coordinates using a checked unit inverse.
A projective proposal with nonunit final `Z` is rejected; merely `Z ≠ 0`
is insufficient. Recompute the entire affine inverse transcript for `qQ`,
canonicalize proposal residues before constructing the raw certificate,
and run `checkAt` on the resulting certificate.

The row's trace bounds and format invariants may be checked for PARI
compatibility, but neither a claimed trace nor a claimed total curve order
enters the soundness argument. PARI may terminate with a bare integer up to
64 bits or with a larger partial-certificate endpoint. Such an endpoint
must be replaced by an accepted existing `PrimeCert`, supplied by the caller
or obtained with the existing `Hex.Nat.Internal.primeCertCountedWith?`
using explicit `PrimeCertBudget`, `Rand`, and fuel. An elaborator convenience
wrapper uses the existing `withinPrimalityBudget`, `primalityFuel`, and
`primalitySearchBudget` policy definitions rather than copying their constants.
Exhaustion is a conversion failure; do not fall back to total trial division, deterministic Miller--Rabin,
or trusting PARI's leaf. Supplied endpoint subjects must match exactly.

Conversion runs with explicit limits on input bytes, integer bits, rows,
scalar bits, inverse operations, and endpoint search fuel. Enforce the byte
and digit limits while parsing, before constructing arbitrary-size integers.
Use a structured result distinguishing malformed input, budget exhaustion,
unsupported format, invalid arithmetic, and success. A conversion failure
alone is not a compositeness proof; a discovered proper factor can be recorded as diagnostic data but must be separately checked by
any consumer claiming compositeness. Preserve enough location information
to identify the row or witness that failed. No `@[extern]` or external process
is required by this API; an offline script may produce the input artifact.

Provide an opt-in bridge tactic `ecpp using c` for a closed literal `n` and
a closed certificate literal or an exposed constant `c` containing such data,
targeting `Nat.Prime n`. In `module` files, cross-module certificate constants and every checker
definition needed by replay must be `@[expose]`. Restrict the accepted term
form to constructor data and exposed data constants; reject arbitrary
computations. Bound traversal, unfolding, numeral size and total certificate
nodes, including embedded `PrimeCert` data, before evaluating the checker.
It evaluates `checkAt` using compiled code as an untrusted preflight, reifies the certificate, and emits
`natPrime_of_checkAt` with kernel-replayed acceptance. The emitted Boolean
proof must reduce through exposed Lean definitions and existing approved
arithmetic fallbacks. A failing preflight, resource interruption, or failed
kernel replay emits no proof. No `norm_num` registration or automatic fallback
from the existing `primality` tactic is changed by this SPEC.

`defaultImportBudget` permits at most 16384 input bytes, 170 digits per
integer, 20 rows, 512 bits per integer and scalar, 1200 inverse operations
per scalar replay, and 200 endpoint-search fuel. These bounds admit the
frozen 512-bit supplied PARI vector. Direct callers can provide smaller
explicit budgets; the mathematical checker itself has no size policy.

The bridge's compact `ecpp_cert% "rows" using leaf` representation freezes
the PARI rows and an explicit checked Hex terminal certificate. Conversion
reconstructs the inverse transcript during elaboration and emits exposed raw
constructor data. No terminal search or external process runs when replaying
this representation. Its proof still uses the complete raw checker, rather
than trusting the row format or conversion code.

Explicit process invocation and certificate-file export belong to
`HexECPPMathlib.Pari`; they do not add a dependency to the core or change the
ordinary `primality` tactic. See the companion SPEC for the process contract.

## Bounded native production

`HexECPP/CM.lean` owns bounded Jacobi, modular square-root and Cornacchia
proposals and the fixed class number one invariants for discriminants
`-3, -4, -7, -8, -11, -19, -43, -67, -163`.
`HexECPP/Search.lean` owns deterministic production from a natural subject,
seed and finite allocation. Search first tries the existing bounded
`PrimeCert` constructor. CM orders are proposals only: partial factor search
selects descending children satisfying `sizeBound`, curves and twists yield
points, and the existing scalar schedule generates checked inverse witnesses.
Every returned certificate passes subject-bound `checkAt`. Roots and norm
equations are checked by arithmetic even for composite moduli. The `j=0`
sextic and `j=1728` quartic twist families are handled explicitly.
For odd discriminants, norm search tries both primitive solutions modulo
`4*n` and the equation `x² + d*y² = n`, whose doubled coordinates supply
solutions with both coordinates even.

One allocation is shared across recursion and backtracking. It bounds input
bits, depth, discriminant and order candidates, root and nonresidue attempts,
point attempts, factor work, scalar additions, certificate size and memoized
entries. Failed candidates consume their work and advance the random stream.
Exhaustion reports the unresolved subject and resource, and makes no
compositeness claim. A compositeness diagnostic requires a separately checked
witness. Neither CM theory nor a probable-prime filter is a proof dependency.
Diagnostics distinguish screening, exhausted local point/nonresidue retries,
the complete portfolio and exhausted shared allocations. A failed recursive
child takes diagnostic priority over an earlier local retry failure.

`HexECPPMathlib/Native.lean` owns `primality? (method := ecpp)` and explicit
export. It shares frozen compact data and kernel replay with the PARI route.
Frozen output contains curve and point proposals and an explicit checked
terminal certificate; replay performs no CM search and invokes no external
program. Ordinary `primality` imports and its fallback behavior are unchanged.
Native frozen rows use an already found child-order point and cofactor one:
the stored field `t = n + 1 - q` encodes the child and is not a Frobenius
trace. Conversion reconstructs and checks the certificate arithmetic. The
elaborator caps its recursion allocation to the compact interface's row
limit and verifies conversion before elaborating the kernel proof.

The default allocation admits 256 input bits, depth 32, 2048 combined
discriminant/order candidates, 8192 root calls, 4096 nonresidue attempts,
4096 point attempts, 32768 reserved factor-work units, one million scalar
additions, two million bits of certificate data and 128 memoized successes.
Local point and nonresidue retry limits are eight and 64, respectively. A
root call has a quadratic modular-operation ceiling in input bits, with
fuel also bounding Jacobi and Euclidean descent. Scalar work reserves the
bit schedule's maximum additions, including compiled checker replays.

Factor-work units are allocation units, not elapsed time or exact operation
counts. A terminal construction call reserves 64 attempts under a fixed
profile: depth at most eight and no greater than the remaining native
recursion allocation, 16 factors, 32 subsets, 16 factor worklist entries,
one rho restart of at most 2048 steps, and p-minus-one bounds 64 and 512
with base two. An order call reserves four attempts with the same rho and
smooth bounds, a 16-entry worklist and no recursive primality search. Each
package therefore bounds zero-attempt trial division and all per-attempt
work independently. Reservations, including unused allowances, are charged
before invocation and never refunded. Memoized certificates are individually
subject to the output-size bound, so the memo entry and output bounds also
bound retained data. The total mathematical checker remains independent of
all these search policies.

Acceptance requires complete native successes above 128 bits, including
recursive ECPP chains and kernel proofs, on subjects where the full current
`primality?` construction route (including applicable factor extensions)
exhausts under recorded budgets. Freeze separate tuning and holdout corpora,
retain every verdict, and report whole-corpus success and exhaustion rates.
The admitted default native route remains bounded to 256 bits. The opt-in
512-bit contract below requires separate capability and public-interface
evidence. If the class number one portfolio cannot establish this
gain at the newly admitted size, extend it with an attributed finite table of
low-degree class
polynomials and bounded root finding before claiming completion.

Measure native search, conversion, compiled checking, compact and expanded
source size, reification and kernel replay separately under the shared-host
protocol. Record source versions and parameter values in build configuration
and reports. Conformance covers composites, nonsquarefree moduli, nonunits,
bad root/norm proposals, exceptional twists, recursive backtracking and each
allocation's exhaustion. Independent oracle checks and fresh-module frozen
replay with PARI absent complement the existing dependency audits.

### Opt-in native production through 512 bits

`Hex.ECPP.produce n seed budget` remains the Mathlib-free computational
entry point. `SearchBudget` defaults retain the existing 128/256-bit policy;
`native512Budget` supplies an explicit finite allocation for subjects through
512 bits. The optional companion exposes that allocation with
`primality? (method := ecpp) (bits := 512)` and
`#ecpp_export (method := ecpp) (bits := 512)`, with the existing optional seed.
The only accepted explicit `bits` values are 256 and 512; the option selects
the corresponding allocation independently of the subject's actual size.
Omitting `bits` retains the 256-bit allocation. These companion entry points
reject subjects above their selected limit and invoke no external
factorization or certificate generation. Ordinary `primality` dispatch is
unchanged. Direct `produce` callers retain their explicit-budget API; there
is no native support claim above 512 bits.

The initial 512-bit allocation is:

| Resource | Limit |
| --- | ---: |
| Subject bits | 512 |
| Native recursion depth | 32 |
| Combined discriminant/order candidates | 8192 |
| Modular-root calls | 32768 |
| Nonresidue draws | 16384 |
| Point draws | 16384 |
| Reserved factor-work units | 131072 |
| Reserved scalar additions, including checking | 8000000 |
| Literal bits per retained certificate | 8000000 |
| Memoized successes | 128 |
| Local point/nonresidue retries | 8 / 64 |

The public 512-bit allocation additionally has a 20-row and 32-total-node
limit. Its recursive search depth is at most 21, since a base consumes one
depth level: 20 ECPP steps require 21 levels. The 256-bit default retains its
current behavior. Diagnosis records both the current public clamp (depth 20,
at most 19 rows) and this explicit 512-bit allocation. For public production,
count rows and embedded terminal nodes during search; candidates exceeding
the remaining allowance fail with charged work and permit backtracking.
Memo reuse must respect the remaining depth, row and node allowances.

Every factor package is explicit in the allocation and the campaign manifest.
The initial terminal package uses the existing 64-attempt profile, depth at
most eight and no greater than the remaining native depth, 16 factors,
32 subsets, a 16-entry worklist, one rho restart of at most 2048 steps,
and p-minus-one bounds 64 and 512 with base two. Its subject limit is 512,
instead of the default terminal package's 256. Order proposals initially
retain the existing four-attempt package with the same rho and smooth bounds,
a 16-entry worklist and no recursive primality search. The terminal size
change is a search-policy change, recorded separately from the top-level bit
limit. Package reservations, failed proposals and unused allowances are
charged before invocation and never refunded. Changes to these finite
profiles require a versioned, frozen allocation manifest before measurement.
Charges derive from the selected packages, including an explicit finite
`some k` order-attempt limit; no implicit unlimited-attempt profile is
admitted. Terminal output traversal derives its fuel from the selected
terminal depth, rather than the previous fixed `leafBudget` constant.

Diagnose the current producer first with an experimental allocation that
changes only `SearchBudget.maxBits` to 512, retaining the nine-discriminant
portfolio and its fixed 256-bit terminal package. Restrict diagnosis and
tuning, including construction comparisons, to tuning subjects and controls;
neither holdout arm runs before the implementation/allocation freeze.
Report separately missing CM norm/portfolio coverage, order-factorization
failures, unresolved recursive
children, root/nonresidue/point retries, output exhaustion, frozen-conversion
and replay-preflight failures, and arithmetic cost. Record bits dropped at
each step and rows used; treat insufficient descent under the row ceiling
as a factor-package/recursive-depth restriction, distinct from CM coverage.
The order-factor package is an explicit tuning lever. Retain cumulative work,
the unresolved subject and advanced random state for every outcome. Raising
fuel or changing only a size guard does not establish the supported extension.

`HexECPP/CM.lean` owns Jacobi, square-root and norm proposals. The
512-bit portfolio extends its nine invariants with the 33 entries in
`HexECPP/CM/ClassPolynomials.lean`: all remaining negative discriminants
with absolute value at most 500 and class number at most two. The linear
and quadratic Hilbert j-polynomials come from PARI/GP 2.17.3, whose source
release SHA256 is recorded beside the table. An independent oracle enumerates
primitive reduced forms and computes the analytic j-polynomial coefficients
at 160 and 240 decimal digits; it also checks compiled root fixtures.

`HexECPP/CM/Roots.lean` uses the quadratic formula and bounded Tonelli–Shanks,
then checks canonical roots by Horner evaluation. It needs no random splitting
attempts. Each call has a 1048576 modular-operation ceiling and charges the
shared root counter and a 16777216-operation allocation before invocation.
The reservation is eight operations for a linear polynomial and
`12*(bits(n)+1) + 3*(v₂(n-1)+1)² + 64` for a quadratic polynomial. This bounds
the exponentiations, at most `v₂(n-1)` Tonelli–Shanks iterations and the two
root checks; unused reservations are not refunded. Norm roots also consume
the shared root allocation.

Fifteen added discriminants are non-fundamental orders whose possible traces
overlap maximal orders already represented: 12, 16, 27, 28, 32, 36, 48, 60,
64, 72, 75, 99, 100, 112 and 147. The table supplies additional checked curve
and factoring proposals, not 33 independent sets of group orders. Distinct
j-roots can repeat an unresolved child search using the advanced random stream;
these retries consume the same shared allocation. Failed children are not memoized.
Successful children are memoized subject to the remaining row/node/depth limits.

The fixed 33-entry table is within the design
ceiling of 64 additional entries of degree at most four. A future splitting
implementation must enforce the per-call 32-attempt and shared
1048576-attempt ceilings and use the shared, advancing random stream.

Each discriminant and order candidate consumes the shared candidate allowance.
The ordered table, coefficients, source release and allocations are frozen
before tuning. No general class-polynomial generator runs in production.
Roots, norm equations, curve proposals and inverse witnesses are checked by
arithmetic, including over composite moduli; CM data contributes no theorem
assumption. All new computational modules remain Mathlib-free.

Native success and public proof generation have distinct output policies.
The public route enforces the existing compact ceilings: 16384 row bytes,
170 digits per integer, 20 rows, 512-bit integers/scalars and 1200 inverse
operations per scalar conversion. Explicit replay also permits at most
131072 inspected syntax nodes, 32 total certificate nodes and 1024 inverse
witnesses per ECPP step. Count every ECPP step, the base wrapper and every
embedded terminal `PrimeCert` node: rows + 1 + terminal nodes must be at most
32. Search depth and terminal depth alone do not enforce that inequality.
The bridge caps row depth, verifies frozen conversion and subject-bound
acceptance, and kernel-checks the exact frozen representation before any
suggestion or source write. A core success that exhausts a public conversion
or replay limit is reported as such and is not a public-generation success.
Increasing these measured replay ceilings requires separate endpoint evidence
and a coordinated companion SPEC change.

### Frozen 512-bit acceptance campaign

Before tuning, commit reproducible prime subjects, independent primality
checks, allocations, seeds, comparison arms and success criteria. The initial
corpus has eight tuning and eight disjoint holdout subjects, each containing
six ordinary and two deliberately difficult 512-bit primes. The input to
SHA512 is
`hex-native-ecpp-10636/v1/{split}/{stratum}/{index}/{counter}`
encoded as UTF-8 with no newline, decimal indices/counters without leading
zeros, literal splits `tuning`/`holdout` and strata `ordinary`/`difficult`.
Use indices 0–5 within the ordinary stratum and 0–1 within the difficult
stratum. Interpret the 64-byte digest as an unsigned big-endian integer, and
set its top bit
to obtain a 512-bit starting integer. PARI `nextprime` proposes
the subject and `isprime` independently verifies it. Advance `counter` from
zero for rejected overflow/duplicate subjects. Difficult subjects additionally
have at most two of the nine original negative discriminants with
`kronecker(-d, n) = 1`; advance the counter until that fixed coverage criterion
holds. Record all rejected candidates and the oracle version. The native seed
is the case
index within the split (ordinary 0–5, difficult 6–7), fixed before tuning.
Corpus generation supplies no certificate, factorization, trace, root, curve
or point to native search.

Freeze composite and size-boundary controls alongside the prime corpus,
including squares/products and inputs on both sides of the 256/512-bit
boundaries. Composites must never produce an accepted certificate; a subject
above the selected bit limit must report `inputBits` without search. In-range
controls report their actual bounded outcome, with no completeness promise.
Preserve all existing 128/256-bit corpora and frozen fixtures.
Run every subject under the recorded finite allocation and retain success,
exhaustion and public replay outcomes. Freeze the selected implementation and
allocation before evaluating the holdout. An unsuccessful holdout remains
evidence; any further tuning based on it requires a new untouched holdout
version before claiming held-out acceptance.

Acceptance requires genuine recursive ECPP successes on held-out 512-bit
subjects, with at least two distinct held-out subjects where the full current
`primality?` construction route, including applicable factor extensions,
exhausts under its recorded finite allocation. A terminal-only Pocklington
success does not count: a counted success contains at least one ECPP step
with a recursively certified child, rather than only `Cert.base`.
Compare against the actual construction schedule and its ordinary
subject-derived seed, record its source and complete allocation,
and disclose allocation differences. Every advertised success requires
independent step-arithmetic and subject-primality checks, successful public
generation, and fresh-module kernel replay. Report every corpus outcome and
whole-corpus success/exhaustion rates; neither a favorable subset nor an
increased bit limit replaces this criterion. If the initial portfolio fails,
retain the diagnosis and improve the bounded portfolio without weakening it.

Public acceptance includes deterministic `#guard_msgs` tests pinning the
exact generated `Try this:` certificate and verbatim suggestion replay in a
fresh importing module with native generation and GP unavailable. Export
contains public, exposed constructor data, passes kernel checking before an
exclusive source write, and replays through the compact interface alone.
Coordinate native policy and acceptance tests in
`HexECPPMathlib/Native.lean` with the companion's existing audit/release work;
the implementation PR updates the companion's native-elaboration SPEC and
builds on the module/export fixes in #10625 after that PR lands. The core
SPEC change can land independently. Full 512-bit generation guards initially
live in manually built acceptance modules; promote them into CI only after
measured endpoint evidence establishes their fit in its wallclock budget.
The core acquires no dependency on that downstream library.

Retain separate native-search, inverse/row-conversion, compiled-checking,
compact/expanded output-size, reification and fresh-kernel-replay evidence.
Compare current 256-bit behavior as well as the full construction route.
Use automatically selected CPU affinity, fixed trial-major samples and
adjacent alternating AB/BA arms; retain every completed sample and host
context. Record corpus/allocation versions and source/executable hashes.
The repaired GMP extended-GCD route is the arithmetic baseline; the former
signed C fallback is not a GMP measurement. Re-attest affected phase
obligations, update core and coordinated companion documentation with actual
support and unsuccessful cases, and extend existing conformance/oracle/CI
scripts. Larger CI kernel fixtures require measured endpoint evidence first.

## Conformance and evidence

Core tests cover every addition branch, inverse consumption, canonicality,
zero and unit denominators, on-curve and discriminant checks, scalar schedules,
subject binding, descending child subjects, both strict size inequalities,
malformed or exhausted conversion, invalid endpoints, and empty/trailing
witness lists. Exhaustive small-prime tests compare every accepted operation
and scalar schedule against an independent implementation; they are
conformance evidence rather than the group-law proof.

Keep a concrete strong-nonzero regression: modulo `35`, on `y²=x³+3`, the
projective point `(15:16:15)` reduces to infinity modulo `5` and to `(1,2)`
of order `13` modulo `7`. It has `13Q=0`, passes the strict size inequality
for `q=13`, and has nonzero `Z=15`, but `gcd(Z,35)=5`. The discriminant is a
unit. An importer must reject this point; accepting it would certify a
composite. Include nonsquarefree composite moduli as well as this squarefree
case. Include a bound-equality case such as `n=16,q=9`.

A useful positive fixture is `n=18446744073709551629`, `a=1`, `b=0`,
`Q=(4259338134586203595,6314297132686212034)`,
`q=115013243398093`. Its deterministic scalar schedule uses 68 inverses.
Its child can use a Pocklington node with
`F = 2²*3*13*167*26041 = 678420132`, cofactor `169531`, and respective bases
`2,11,2,2,2`; every prime factor is in the existing stored table.
Supply the actual accepted `PrimeCert`, rather than treating the displayed
prime numeral as a leaf proof. Add multi-step chains, a 256-bit and a 512-bit
accepted subject, and a prime outside the Pocklington search policy's coverage.
Freeze complete certificates and expected outcomes so conformance never
requires live external ECPP generation.

For bridge elaboration policy, measure kernel replay of the 65-bit
fixture, then successive chain lengths and subject sizes. The single CI job
kernel-replays the admitted frozen certificates and small branch/boundary
probes. Promote larger fixtures to CI kernel proofs only after fresh-module
evidence establishes their fit within the existing CI budget. Compiled-only coverage
does not establish an elaborator size ceiling or claim fast kernel replay.
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

`HexECPP/{Data,Affine,Replay,Cert,Import}.lean` owns the executable checker,
conversion, and their arithmetic invariants. It imports no Mathlib module.
`HexECPP/CM.lean` and `HexECPP/Search.lean` own native proposals and bounded
production; the optional low-degree table and root modules are assigned in
the 512-bit contract above.
The [bridge SPEC](../../HexECPPMathlib/SPEC/hex-ecpp-mathlib.md) owns Hasse,
reduction, group-law correspondence, unconditional soundness, and elaboration.
Source registration does not by itself imply release or phase progress.

## References

- [Sutherland, elliptic-curve primality proving, Lecture 11](https://math.mit.edu/classes/18.783/2023/LectureNotes11.pdf): prime-order certificates and the Hasse argument.
- [PARI `primecert` documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#primecert): supplied certificate format and terminal prime conventions.
- [PARI ECPP implementation](https://pari.math.u-bordeaux.fr/lcov-report/basemath/ecpp.c.gcov.html): exact integer size comparison and strong-nonzero check.
- [Mathlib affine points](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean): group-law interface; use the project's lockfile for the version built here.

## Reduced automatic-search allocation

`Hex.ECPP.autoBudget (bits : Nat)` is a Mathlib-free allocation definition
for the optional downstream automatic primality suggestion route. It selects
the native policy through 256 bits with the existing public 20-row depth
clamp, or `public512Budget` above that threshold, then lowers its finite candidate/root/nonresidue/point/factor/scalar
allocations as specified by
[hex-ecpp-mathlib](../../HexECPPMathlib/SPEC/hex-ecpp-mathlib.md#automatic-native-fallback).
Only the larger policy lowers polynomial and root-work caps to 1048576. The
compiled feasibility driver and optional Auto module use this single definition.
The subject ceiling remains at most 512 bits; the caller checks it before work.
This definition imports no Mathlib, registers no tactic and makes no coverage
claim. The default `produce`, explicit native256/native512 policies, search
algorithm and checker remain unchanged.

## Mixed integer-factorization integration

The optional `HexIntFactor.Mixed` modules consume `Cert`, `checkAt` and the
existing bounded native `produce`; ownership and allocations are specified in
[HexIntFactor](../../HexIntFactor/SPEC/hex-int-factor.md#optional-mixed-primality-evidence).
ECPP gains no dependency on HexIntFactor and no new certificate semantics,
producer, fallback in ordinary primality dispatch or external certificate
backend. Terminal certificates still embed legacy `PrimeCert`. Computational
factor replay requires only `HexECPP.Cert`; optional completion imports search
separately. Factor-base and whole-factorization subject limits are independent.
Unconditional mixed primality is discharged in HexIntFactorMathlib through
HexECPPMathlib, never asserted in the computational replay closure.

`HexECPP.Policy` and `HexECPP.ElabData` own the Mathlib-free numeral/replay
limits, raw certificate reifier and bounded constructor-data syntax auditor,
including persistent let scopes and rejection of compiled overrides. The auditor
accepts an explicit extension whitelist and finite syntax/numeral allocation
for larger enclosing data types; certificate admission remains independently
bounded. `HexECPPMathlib.Elab` and `HexIntFactor.Mixed.Export` reuse this shared
code. These meta modules are explicitly imported and excluded from certificate
replay; extracting them changes no checker semantics or native search default.
`Hex.ECPP.public256Budget` adds an explicit output-bounded search profile for
mixed completion: default 256-bit work counters, depth 21, 20 rows, 32 nodes
and output backtracking. The existing explicit Native 256-bit route retains
its current policy.
