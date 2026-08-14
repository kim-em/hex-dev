# Modular techniques SPECs

## Accomplished

Wrote three library SPECs from the "Modular techniques" entry in
`SPEC/future-work.md`, which listed five bullets and no library
structure:

- `SPEC/Libraries/hex-modular.md`: symmetric representatives, incremental
  Chinese remaindering for a scalar and for a residue vector sharing a
  modulus, rational reconstruction (checked signature, uniqueness,
  completeness, the common-denominator vector form, the maximal-quotient
  heuristic), the modulus supply, and the loop combinator that adds
  moduli until a caller's check accepts.
- `SPEC/Libraries/hex-modular-matrix.md`: the multi-modular determinant
  with the Hadamard bound as a discharged hypothesis, the
  Abbott-Bronstein-Mulders determinant divisor, the two-sided rank
  certificate, the Dixon `p`-adic solve, and the rational kernel basis.
- `SPEC/Libraries/hex-poly-z-gcd.md`: modular gcd for `ℤ[x]` with
  cofactors, the modular coprimality witness and its unconditional
  soundness proof, exact division, and the four routes (structural,
  coprime fast path, heuristic, Brown, subresultant fallback).

Each names its prerequisite relocations, records what is out of scope,
and carries the `libraries.yml` block it would add.

Updated `SPEC/Libraries/README.md` (descriptions, both dependency lists,
index, and a paragraph on why the three split the way they do) and
replaced the `SPEC/future-work.md` entry with a pointer plus four
corrections. Relinked the four cross-references elsewhere in
`future-work.md` and `hex-mv-gcd.md` that named the item.

## Findings that changed the design

- **Primality is not what the checkers need.** The future-work entry
  named "primality and distinctness of the moduli" as the checker's
  obligations. Reduction modulo any `m` is a ring homomorphism, so the
  determinant and gcd arguments never use primality; what elimination
  needs is invertible pivots, which the extended gcd discovers. And
  distinct moduli need not be coprime, which is the property the
  reconstruction actually uses. This is why the determinant may use
  31-bit moduli found at runtime rather than a certified table.
- **Kernel-replayed primality is priced by `√p`, measured here.**
  `decide +kernel` on `Hex.Nat.isPrimeTrial`, against a 0.81 s
  import-only baseline: 0.04 s at 16 bits, 0.08 s at 20, 0.42 s at 24,
  and 6.2 s at 31. So a certificate whose checker names a prime should
  name a small one, and the gcd certificate does. `hex-primality`'s
  Pocklington certificate would remove the constraint.
- **The three operations differ in whether they have a checker**, and
  that drives the whole matrix SPEC. The linear solve is checked by one
  matrix-vector product. The rank has a complete two-sided certificate (a
  nonzero minor modulo one modulus for the lower bound, a rational
  expression of the remaining columns for the upper). The determinant has
  no cheap checker, so it is a proved algorithm, it carries the group's
  only analytic hypothesis, and certified dispatch to an external
  implementation is unavailable for it while available for the other two.
- **The determinant divisor is rigorous, not heuristic, but only after a
  reduction step.** `d ∣ det A` needs `gcd(gcd_i y_i, d) = 1`, and
  Dixon's reconstruction returns a common denominator that need not be
  least. Omitting the reduction gives a wrong determinant with no
  symptom.
- **`zmod64FieldOfPrime` is in the wrong library.** The
  `Lean.Grind.Field (ZMod64 p)` instance and `ZMod64.intPow` live in
  `HexPolyFp/PrimeField.lean`; the instance is about a hex-mod-arith type
  and its only polynomial import is `HexPolyFp.Degree`. Any library doing
  linear algebra over `F_p` currently has to depend on hex-poly-fp for
  it.
- **Hadamard's inequality is in the wrong library too.**
  `Matrix.norm_det_le_prod_norm_column` is in `HexPolyZMathlib/Hadamard.lean`,
  and `HexRealRootsMathlib/Hadamard.lean` already exists solely as a
  compatibility import of it. It is a determinant inequality and belongs
  in hex-matrix-mathlib.
- **The univariate gcd certificate is unconditionally sound**, unlike
  hex-mv-gcd's. The multivariate checker finishes with "so `d` divides
  both contents", whose justification is the multivariate gcd's own
  maximality one variable down, so its soundness is conditional on
  `LawfulContent`. In one variable the corresponding fact is
  `Int.dvd_gcd`. Maximality itself is also within Mathlib-free reach
  here, through `DensePoly.content_mul` (Gauss, `HexPoly/Euclid.lean:675`)
  and the rational Euclidean gcd.
- **The measured Bareiss gap is the motivation and the target.**
  `reports/hex-bareiss-performance.md` records an adjusted ratio of
  `0.049x` to `0.057x` against FLINT's multi-modular determinant at
  `n = 320 … 512`. hex-bareiss classifies that comparator
  `informational` because the algorithms differ; implementing the same
  algorithm makes it like-for-like, so the new SPEC classifies it
  `gating` with a written-down threshold.
- **Other missing infrastructure**, each named in the SPECs: no entrywise
  `Matrix.mapEntries`; `floorSqrt` / `ceilSqrt` under the `Hex.ZPoly`
  namespace in `HexPolyZ/Mignotte.lean`; no integer CRT anywhere (only
  `polyCRT` for polynomials); `Hex.Int.extGcd` returning the final Bézout
  pair only, so the truncated remainder sequence rational reconstruction
  needs is new; and `permutationVectors` with no `length = n !` lemma,
  which is why the crude Leibniz determinant bound is not the default.

## Second opinion, and what it changed

Codex (read-only, full repo access) reviewed the three drafts
adversarially and returned 22 findings. It endorsed the three-way split,
and did not dispute the rational-reconstruction uniqueness proof, the
derivation of `gcd(q, m) = 1`, the necessity of Garner's outer `symMod`,
determinant reduction over arbitrary moduli, the soundness of a nonzero
minor modulo a composite modulus, the two-sided rank argument, Dixon's
exact division, the univariate coprimality checker's unconditional
soundness, or the Mathlib-free route to maximality. Everything below is
now fixed in the SPECs.

**Five findings were errors that changed a design rather than a
sentence.**

- **The `2^31` modulus bound breaks three totality claims.** With
  `L = lcm(1, …, 2^31 - 1)`, every allowed modulus divides `L`, and so
  does every product of pairwise coprime allowed moduli. On `[L]` the
  determinant loop never reaches its bound, the rank certificate does not
  exist (every minor residue is zero), and for `f = x`, `h = x + L` no
  modular coprimality witness exists. So `det` now falls back to
  `Hex.Matrix.bareiss`, `RankCert.modulus` is an arbitrary `Nat` checked
  in `Int` arithmetic rather than a `ZMod64` modulus, and the gcd
  certificate gained a `constant` constructor carrying
  `u f' + v h' = C k` with `k ≠ 0`, which the extended subresultant chain
  always produces. hex-modular records the shared cause once.
- **hex-poly-z-gcd's milestone 6 was a dependency cycle.** It proposed
  rewriting `HexPolyZ.primitiveSquareFreeDecomposition` to call a library
  that depends on hex-poly-z. The fast squarefree entry point is now
  `ZPoly.sqfDecomp` in hex-poly-z-gcd, with the existing implementation
  left below as the reference and the benchmark baseline.
- **`Crt` could be driven into an inconsistent state.**
  `Crt.init.push 1 0` passes the coprimality test, because
  `gcd(1, 0) = 1`, and then `push_modulus`, `push_le`, and
  `push_congr_new` are jointly unsatisfiable. Positivity and the
  symmetric bound are now structure invariants and `push` rejects
  `m ≤ 1`.
- **The common-denominator vector reconstruction was incomplete.** At
  `m = 101`, `P = 2`, `Q = 4`, the residues of `(1/2, 1/4)` reconstruct
  entrywise to denominators `2` and `4`; multiplying them gives `d = 8`
  and numerators outside the bounds, where `lcm` gives the correct
  `(2, 1)/4`. The combination step now uses `lcm` and reduces the whole
  pair, and the SPEC says that `Q` must bound the *common* denominator.
- **The Dixon numerator bound named one replaced column.** Cramer's rule
  uses all of them: for `A = [[1, N], [0, 1]]` and `b = (0, 1)` the
  solution is `(-N, 1)` while the second replaced column bounds at `1`.
  `P` is now the maximum over `i`.

**Six more were real errors of statement.** `detMod?` must return
`some 0` on an all-zero pivot column and `none` only on a nonzero
nonunit, or `det` of a singular matrix never terminates (found
independently before the review landed). `checkRank_sound` named the
function it was meant to certify, so it now targets `ratRank`, defined as
row reduction over `Rat`. `kernel?` had an unbound `r` and returned
neither the rank nor the denominator, so it returns a structure. The rank
producer handed an `n × r` block to a square solver; it now solves the
`r × r` minor and checks against all `n` rows. `gcd f h = 1` for a
nonzero constant `h` is false (`gcd(2, 2x) = 2`), so the contract is now
an integer gcd against the content. And the determinant divisor needs
`d⁻¹ mod m`, so moduli sharing a factor with `d` are skipped.

**Four were misstatements about the tree**, all verified: the public name
is `HexArith.Int.extGcd`, not `Hex.Int.extGcd`; `Dvd (DensePoly R)`
already exists (`HexPoly/Euclid/DivGcd.lean:1077`) so the proposed `Dvd
ZPoly` instance was a duplicate; `HexBerlekampZassenhaus.exactQuotient?`
(`Records.lean:452`) is already exact integer-polynomial division, so
`divExact?` belongs in hex-poly-z with both consumers importing it; and
`Rat.mk'` is the raw constructor, not the normalising one
(`Rat.normalize` is).

**Two were structural.** The modulus supply belongs in hex-mod-arith
beside `ZMod64`, not here, which leaves hex-modular depending on
hex-arith alone and dissolves this SPEC's original "why not inside
hex-arith" argument; the section now gives the honest reason (subject
separation, and not reopening a `done_through: 7` library) and records
the alternative. And "a prime preserving both cofactor degrees works" is
false: `f' = x`, `h' = x + 2` at `p = 2` preserves both and admits no
Bézout pair, so the producer must compute the image gcd and retry.

**Two were fair pushback on confidence.** The benchmark thresholds were
stated as required checks with no prototype behind either number; the
"faster at every rung `n ≥ 64`" requirement also guessed a crossover in
the same document that says it will not guess one. The Bareiss
requirement is now the `n = 512` ratio with the crossover measured, and
the FLINT figure is a target that becomes required after the first
measurement. Separately, three conformance cases did not test what they
claimed: the CRT suite had no outer-reduction regression (push `1 mod 3`
then `0 mod 2`), nothing exercised a successful composite modulus, and a
unit-diagonal triangular matrix is unimodular, so it is the determinant
divisor's worst case rather than a demonstration of it.

One finding strengthened a claim rather than weakening it: the Gauss
descent step for Mathlib-free maximality already exists as
`ZPoly.dvd_of_toRatPoly_dvd_of_primitive`
(`HexPolyZ/Decomposition.lean:797`), so that milestone is assembling
three existing pieces.

## Current frontier

The SPECs are drafts in the sense that none of the six libraries is in
`libraries.yml`; each SPEC carries the block it would add, following the
`hex-mv-poly` precedent. All three are marked `status: planned` rather
than `draft`, since every dependency is `active` at `done_through: 7`
except `HexResultant` (`done_through: 1`), which only route 4 of the gcd
needs and which milestone 2 there is arranged around.

A second session was writing `hex-finite-field`, `hex-primality`, and
`hex-int-factor` in the same worktree during this turn, and those SPECs
are not in this change. Where the two sets meet, this one refers to the
`future-work` entry rather than to an unlanded file: the modulus supply
wants Miller-Rabin and a Pocklington certificate from whatever library
owns "Better primality", and the determinant divisor wants the seedable
generator that the equal-degree splitting item calls for. `hex-mv-gcd`
gains a pointer to `hex-poly-z-gcd` for its arity-one case.

Nothing is committed.

## Next step

The sequencing the three SPECs argue for:

1. The five relocations, each independently justified and each doable
   before any commit here: `zmod64FieldOfPrime` and `SmallPrimeCandidate`
   into hex-mod-arith, `floorSqrt` / `ceilSqrt` and `exactDiv` into
   hex-arith, `Matrix.mapEntries` into hex-matrix, and Hadamard's
   inequality into hex-matrix-mathlib.
2. hex-modular milestones 1 to 3 (`symMod`, `Crt`, `ratRecon?`, the
   vector forms, the modulus supply). Completeness of `ratRecon?` may
   lag; no consumer's soundness depends on it.
3. hex-modular-matrix milestones 1 and 2, giving a correct determinant
   with no performance claim, then milestone 3 (Dixon) and milestone 4
   (the determinant divisor), which is where the benchmark numbers come
   from.
4. hex-poly-z-gcd milestones 1 and 2 in parallel, since they need only
   hex-modular milestone 1, followed by Brown once the modulus supply
   exists.
5. The rank certificate and the rewrite of
   `primitiveSquareFreeDecomposition` last, since both are consumers of
   everything above.

## Blockers

None.
