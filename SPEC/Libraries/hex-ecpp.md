# hex-ecpp

Kernel-replayed elliptic-curve primality certificates. A certificate for `n`
reduces primality to a smaller prime `q`, using an explicitly checked
nonzero point of order `q` on a nonsingular short Weierstrass curve modulo
`n`. The executable verifier is Mathlib-free. The elliptic-curve semantics,
Hasse bound, and resulting primality theorem belong to its Mathlib companion.

## Scope and placement

This SPEC owns the proposed `HexECPP` and `HexECPPMathlib` pair. Their first
implementation delivers certificate verification, conversion of supplied
PARI certificates, and explicit certificate elaboration. Native complex
multiplication search, Hilbert class polynomials, point counting, ECM,
automatic search fallback, and cryptographic curve APIs are outside this
scope. Conversion consumes supplied data; ordinary proof elaboration does
not invoke an external program. This is an ECPP verification service, not a
promise to generate certificates for arbitrary primes.

The dependencies are:

| Library | Dependencies | Owns |
| --- | --- | --- |
| `HexECPP` | `HexPrimality`, `HexArith` | raw data, modular arithmetic, inverse-witness replay, recursive Boolean checking, bounded conversion |
| `HexECPPMathlib` | `HexECPP`, `HexPrimalityMathlib`, Mathlib | interpretation over prime fields, scalar correspondence, Hasse bound, unconditional primality soundness, proof elaboration |

There is no dependency from `HexPrimality` back to ECPP and no constructor
added to its existing `Hex.Nat.PrimeCert`. A terminal ECPP certificate embeds
that existing type. The current core `prime_of_checkPrime` remains entirely
Mathlib-free. The new executable checker establishes arithmetic facts in the
core; its unconditional primality theorem is available only with the bridge.
A bridge theorem may also transport the result to `Hex.Nat.Prime`, without
claiming that proof is importable from the core library.

The generic field-only curve library proposed in
[future work](../future-work.md#elliptic-curves-over-finite-fields) cannot be
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

## Proof obligations and missing infrastructure

At Mathlib revision `85e3a25e006c35636f0e53b0e9296caca2685bc0`,
`Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` provides nonsingular
points and their abelian group law. Its point constructors distinguish
infinity from an affine point with a nonsingularity proof. It does not
provide the Hasse bound needed here. The required new bridge obligations
are part of this implementation, not consequences of a checksum or of
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

   At the pin, `Affine/Point.lean` has coordinate-ring norm/degree arguments
   used to establish the group law, and `DivisionPolynomial/Degree.lean`
   has division-polynomial degree formulas. Neither supplies the required
   isogeny/endomorphism degree theory or the Frobenius/kernel-count argument.
   Develop these bridge modules, checking for compatible proved upstream
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
targeting `Nat.Prime n`. Cross-module certificate constants and every checker
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
accepted subject, and a prime outside the current Pocklington search policy's coverage.
Freeze complete certificates and expected outcomes so conformance never
requires live external ECPP generation.

Before fixing an elaborator policy, measure kernel replay of the 65-bit
fixture, then successive chain lengths and subject sizes. The initial single
CI job kernel-replays that fixture and small branch/boundary probes. The
256-bit and 512-bit fixtures initially exercise compiled checking and oracle
comparison; promote them to CI kernel proofs only after fresh-module evidence
establishes their fit within the existing CI budget. Compiled-only coverage
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
[benchmarking](../benchmarking.md), retain every completed shared-host run,
and keep runtime benches Mathlib-free. Extend the existing single CI job's
conformance/oracle script; add no workflow or matrix.

## Implementation order and files

First establish the restricted Hasse theorem against the pinned Mathlib and
record its proved dependency surface. Then implement the affine arithmetic,
certificate checker and replay correspondence, compose unconditional
soundness, and finally enable bounded conversion and elaboration with their
conformance and measured policies. These are milestones of the one SPEC;
no phase-complete claim may hide the missing Hasse prerequisite.

Suggested module ownership:

```text
HexECPP/{Data,Affine,Replay,Cert,Import}.lean
HexECPPMathlib/{Reduction,Hasse,Order,Soundness,Elab}.lean
HexECPPMathlib/Hasse/{Degree,Frobenius}.lean
conformance/HexECPP/{Conformance,EmitFixtures}.lean
conformance/HexECPPMathlib/Conformance.lean
bench/HexECPP/Bench.lean
bench/HexECPPMathlib/ProofProbe/
```

Register the actual libraries and their dependency edges when source is
introduced; this design alone does not advance a library's phase or release
status. At that point split this planned pair SPEC into
`HexECPP/SPEC/hex-ecpp.md` and `HexECPPMathlib/SPEC/hex-ecpp-mathlib.md`,
preserving the explicit ownership above and updating the index and links.
Add released-repository manifest entries only as part of a separately
qualified release, not as a consequence of adding source. The pair can later
share proved curve infrastructure without making integer primality depend on integer factorization or on its own ECM consumer.

## References

- [Sutherland, elliptic-curve primality proving, Lecture 11](https://math.mit.edu/classes/18.783/2023/LectureNotes11.pdf): prime-order certificates and the Hasse argument.
- [PARI `primecert` documentation](https://pari.math.u-bordeaux.fr/dochtml/html-stable/Arithmetic_functions.html#primecert): supplied certificate format and terminal prime conventions.
- [PARI ECPP implementation](https://pari.math.u-bordeaux.fr/lcov-report/basemath/ecpp.c.gcov.html): exact integer size comparison and strong-nonzero check.
- [Pinned Mathlib affine points](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean): existing group-law interface.
