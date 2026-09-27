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

The bridge imports the proved `HasseWeil.WeilPairing.hasse_bound` from
AINTLIB and derives its integer-square formulation in `Hasse/Degree.lean`;
`Hasse.lean` specializes it to `ZMod p`. The imported proof uses
Frobenius Weil-pairing scaling, scaling for `1 − Frobenius` and coprime
pencils, a nonnegative quadratic form built from kernel cardinalities, and
the rational-point fixed-point count. This complete route avoids the
separate isogeny-degree point-count residual appearing elsewhere in that
upstream development. The exact imported source is selected by the lockfile.
`Hasse/Frobenius.lean` independently identifies rational points with the
fixed points and kernel of `1 − Frobenius` under base change.
`#print axioms` on the restricted Hasse and headline soundness theorems
allows only `propext`, `Classical.choice`, and `Quot.sound`.

## Explicit proof elaboration

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


The explicit `ecpp using c` policy admits subjects and individual
certificate numerals through 65 bits, at most 8192 inspected syntax nodes,
32 total certificate nodes including embedded `PrimeCert` nodes, and 128
inverse witnesses per ECPP step. These limits admit the frozen 65-bit
certificate and its fresh-module kernel proof. The 256-bit and 512-bit
fixtures are compiled-checking and oracle inputs; their kernel replay is
not part of the supported tactic policy.

## Conformance and evidence

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
