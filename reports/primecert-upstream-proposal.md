# Upstreaming Hex primality work to PrimeCert

## Recommended order

Prefer small contributions to PrimeCert's existing architecture, followed by a
shared Mathlib-free core. Hex can then become a compatibility layer. There is
no requirement to retain separate implementations or Hex ownership.

The source audit uses PrimeCert master
[`0803c2f`](https://github.com/b-mehta/PrimeCert/tree/0803c2f)
and Lean's draft [powMod PR #15167](https://github.com/leanprover/lean4/pull/15167).
The [current certificate comparison](hex-primality-windowed-replay.md) predates
the proposed ports. Its speedups are not predictions for the final combination.

### 1. Windowed modular exponentiation

[PrimeCert PR #172](https://github.com/b-mehta/PrimeCert/pull/172).

Port the window worker, correctness proof, and measured dispatch into
`PrimeCert/PowMod.lean`, preserving `powModK_eq` and the existing public API.
Keep the accumulator helper lemmas for clients that use them. This contribution
needs no dependency on Hex. Once PrimeCert can use the Lean release containing
#15167, replace the local implementation with `Nat.powMod` and its theorem.
PrimeCert and Lean agree on modulus zero; Hex's special zero result must not
be copied into this API.

Credit Bhavik Mehta for `powModK`, Joachim Breitner for help developing it,
and the existing copyright holders. Use direct kernel checks and complete
PrimeCert certificate builds to measure the result. The comparison should use
the same Lean version in both arms. Retain every completed paired sample.
This is the first performance PR: it isolates the main arithmetic improvement
before deciding which remaining checker changes are useful.

### 2. Optional interval witness for the cube-root criterion

[PrimeCert PR #170](https://github.com/b-mehta/PrimeCert/pull/170).

Hex can establish that a nonnegative discriminant is not a square by checking
`w*w < D` and `D < (w+1)*(w+1)`, using a supplied integer `w`. PrimeCert's
`pock3` currently supports zero, negative discriminant, or a prime quadratic
non-residue witness. Add an interval mode alongside those existing modes if
measurements show a benefit. The producer's square-root calculation is
untrusted; the theorem checks both inequalities. Preserve the existing
generalized cube-root criterion and syntax.

This is a small mathematical extension, independent of certificate search.
It may remove a non-residue search and its extra prime proof. It is not
automatically faster than a small existing non-residue witness: compare both.

### 3. Bounded Lean certificate construction and reusable suggestions

[PrimeCert PR #171](https://github.com/b-mehta/PrimeCert/pull/171).

Port the useful pieces of `HexPrimality/Construction.lean` and its supporting
factor search: explicit finite profiles, deterministic seeds, Pollard `p - 1`
through 524288, bounded rho, validated partial factorization, and deterministic
subset selection that accounts for recursive child cost. Add the ECM route
only as a separate contribution if wanted; Curve25519 does not require it.
The optional construction route can coexist with PrimeCert's Python tool.

Use the existing `PrimeDict` and certificate ladder. A suggested working name
is `prime_cert?`, emitting the explicit `prime_cert` ladder through `TryThis`.
Applying it must remove factor/certificate search. Pin the entire Curve25519
suggestion with `#guard_msgs`, plus honest exhaustion and malformed-input tests.
Keep the search's numeric subject separate from the user's original expression.

The adapter is not a constructor renaming: Hex permits a different witness
base per factor, while PrimeCert uses a common root at each node. Search for
a common root with a finite budget, then check the final emitted certificate.
The cube-root witness representations also differ. The existing
[Curve25519 PrimeCert fixture](bench-results/hex-primality-compact-primecert/Curve25519.lean)
already demonstrates a valid compact ladder with common witnesses.

Avoid copying features PrimeCert already has. `PrimeDict` already shares child
proofs, and its Pocklington interface already separates the node's Fermat
condition from the factor-specific conditions. Hex's adjacent-base Fermat
cache is therefore not a standalone improvement to that interface. PrimeCert's
Python producer already selects factors before recursing and tries small roots;
the new contribution is bounded Lean construction and recursive-cost selection.

### 4. Share the core instead of maintaining two libraries

Deferred for discussion with Bhavik; this is outside the three PRs above.

Extract the reusable certificate data/checker, soundness proof, verified prime
enumeration, and finite search into a Mathlib-free package owned by PrimeCert.
Its dependency graph must actually exclude Mathlib; a source module inside a
package whose Lake manifest requires Mathlib does not achieve that packaging
goal. Keep the existing PrimeCert Mathlib API as the bridge, and let Hex's
computational library depend on the shared core with compatibility aliases.
The core needs its own Mathlib-free primality predicate, with a proved
equivalence to Mathlib's `Nat.Prime` in the bridge, as Hex already provides.

This package split is a design agreement with the maintainer, not a prerequisite
for the first arithmetic PR. Compare the existing proof ladder with a data
checker before standardizing either representation. Import cost, dependency
weight, literal size, kernel replay, and build time all matter.

## Coordinate with work already in progress

PrimeCert already has a certified sieve through one million. Its coprime-to-six
sieve statement landed in [#169](https://github.com/b-mehta/PrimeCert/pull/169).
The active sequence [#156](https://github.com/b-mehta/PrimeCert/pull/156),
[#164](https://github.com/b-mehta/PrimeCert/pull/164),
[#166](https://github.com/b-mehta/PrimeCert/pull/166), and
[#167](https://github.com/b-mehta/PrimeCert/pull/167) covers word popcount,
packed-entry validation, running bit counts, and enumeration completeness.
Build on those rather than opening a competing sieve implementation. Hex's
runtime enumeration and endpoint tests can supply cases for that work.

For each PR, keep syntax compatibility tests, exact certificates, arbitrary
input soundness proofs, and kernel-only replay. Separate native search,
literal elaboration, direct kernel checking, and whole proof builds in reports.
