# hex-real-roots-theory

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Mathlib semantics and a one-call elaborator for
[`hex-real-roots`](https://github.com/leanprover/hex-real-roots).

This package proves the half-open form of Sturm's theorem, connects the
executable signed-remainder chain to `Polynomial ℝ`, proves soundness and
completeness of the isolator, transports through squarefree cores, and presents
the result as ordinary rational intervals with proof fields.
It also exports `Real.instIsRealClosed`, constructed from real square roots
and odd-degree polynomial root existence, through `HexRealRootsTheory.RealClosed`
and the umbrella import.

The public umbrella exports the general Sturm–Tarski root-sum theorem and
integer query semantics through `TarskiSoundness` and `TarskiReal`. The shared
foundation imports pinned Tau Ceti in this theory companion. These modules
are integrated in the development source; availability in a published version
requires the maintainer’s next package sync.

# Quickstart

```toml
[[require]]
name = "hex-real-roots-theory"
git = "https://github.com/leanprover/hex-real-roots-theory.git"
rev = "main"
```

```lean
import HexRealRootsTheory

open Hex Polynomial

noncomputable def roots :=
  isolate_roots ((X - 1) ^ 2 * (X - 3) : Polynomial ℤ)

example : roots.intervals =
    #v[((0 : ℚ), (2 : ℚ)), ((2 : ℚ), (4 : ℚ))] := rfl
```

# Root counts

For a closed squarefree polynomial over `ℚ` with integer coefficients and positive
degree, `real_root_count` proves the exact number of distinct real roots:

```lean
import HexRealRootsTheory.RealRootCount

open Polynomial

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by
  real_root_count
```

The term form `real_root_count (X ^ 5 - 4 * X + 2 : ℚ[X])` is also available.
Hex proposes a signed remainder chain. Polynomial identities, positive scalar
factors, and sign variations are checked in Lean. A nonzero constant at the end
of the chain certifies separability as well as the root count.

The general Sturm theorems use only Mathlib types. `Sturm.IsSturmChain.sturm_Ioc`
counts roots on `(a, b]`, including equal endpoints, and `Sturm.IsSturmChain.sturm`
counts roots on the real line. Their hypothesis is that the multiset of real
roots has no duplicates. The variation counts use Mathlib’s `List.signVariations`;
`HexRealRootsTheory.signVar_eq_list` identifies the Mathlib-free executable counter
with this API.

The corresponding Mathlib sources can be checked with
`python3 scripts/check_sturm_sync.py /path/to/mathlib` from `hex-dev`.

# Functionality

The input may be a closed `Hex.ZPoly` or a closed integer-coefficient
`Polynomial ℤ`, `Polynomial ℚ`, or `Polynomial ℝ` expression. Repeated roots
are handled automatically by isolating the squarefree core and transporting
the result back. The zero polynomial is rejected because it has infinitely many
real roots.

An optional exact width refines every interval:

```lean
noncomputable def tight :=
  isolate_roots (width := 2 ^ (-20 : ℤ))
    (X ^ 4 - 2 : Polynomial ℝ)
```

The result is `Hex.IsolatedRealRoots P n`, whose fields state:

- `unique_root`: interval `i` contains exactly one real root;
- `covers`: every real root lies in one returned interval; and
- `ordered`: intervals are sorted and pairwise disjoint.

The interval vector is literal data, so endpoint extraction is often `rfl` and
the semantic fields can be consumed directly by `simp`, `grind`, or ordinary
proof terms.

# Signed-query correspondence

`TarskiInterpret` transports the shared producer and literal checker through
zero-reflecting, possibly noninjective coefficient interpretations. It proves
positive signed identities, degree bounds, sufficiency of the internal bound
and acceptance of produced chains. `TarskiInteger.integer_certify_checks`
proves acceptance and value agreement for produced integer/dyadic certificates.
`TarskiGcd` identifies the terminal gcd and proves that the constant-tail check
is equivalent to squarefreeness. Query production succeeds exactly when that
condition and the executable endpoint guards hold. `TarskiDomain` completes the
integer/dyadic endpoint interpretation, proves exact mathematical domain
equivalence, and extracts that domain from accepted replay.

`TarskiCompare` proves that arbitrary accepted chains for positively scaled
inputs have equal lengths and entrywise positive scaling. `TarskiSigns` proves
finite and infinite endpoint sign-array agreement and extracts the checked
variation value.
Together they support the rational/integer whole-`Option` agreement theorem
in hex-sturm-theory without assuming root-sum semantics.

`TarskiFoundation`, `TarskiSoundness` and `TarskiReal` import the proved
signed-remainder theorem and polynomial IVT/Rolle foundation from Tau Ceti.
`Tarski.check_rootSum` proves soundness of arbitrary accepted certificates
over an ordered real closed field. `Hex.ZPoly.tarskiQuery_eq` and
`Hex.IntTarskiCertificate.check_sound` specialize it to integer inputs and
real roots. Singleton-sign and arbitrary ordered-field count consequences
are public too; the algebraic replay results above do not need the foundation.

`TarskiSum.lean` defines the mathematical sum over distinct roots in an open
interval, allowing infinite endpoints. It proves singleton and constant cases,
query `1` as cardinality, zero/divisible queries, removal of common-root zero
contributions, and absolute-value/cardinality/degree bounds with existing
algebra. These lemmas do not identify the executable query with that sum.
`Tarski.check_singleton` and `Tarski.check_constant` separately prove zero
answers for those accepted literal certificates without an analytic foundation.

`TarskiCount.lean` connects checked integer derivative chains to the existing
real Sturm theorem. Accepted query-one certificates count roots on finite
dyadic intervals and on the whole real line; the actual integer producer is
therefore nonnegative on query `1`. The rational companion transports the
finite-interval result. `rootsIn_card` identifies the legacy half-open count
with the open distinct-root set under the accepted domain;
`integer_check_rootSum` and `integer_query_rootSum` give the actual query-one
root-sum identity. The arbitrary ordered-field count theorem and its general wrapper use the
shared Tau Ceti foundation exposed by this companion.

# Verification

The elaborator runs compiled search, reifies the Sturm chain and intervals, and
emits a small proof term whose count checks reduce in the kernel. It does not
ask the kernel to repeat bisection. Descartes search is never trusted: every
output interval and the final root total are certified by Sturm counts.

See the [SPEC](SPEC/hex-real-roots-theory.md) and the Hex manual's real-roots
chapter for the theorem chain and checked examples.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
