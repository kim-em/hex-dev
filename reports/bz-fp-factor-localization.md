# Localizing the F_p Berlekamp factorization bottleneck

Investigation for [#8267](https://github.com/kim-em/hex/issues/8267)
("speed up single Berlekamp factorization of f mod p").

## Summary

The ~90 % `factorFast` cost that #8062 item 4 and #8267 attribute to
`choosePrimeData?` is **not** in the Berlekamp matrix build or the
nullspace (Frobenius / Q-matrix) step, as deliverable 2 hypothesized.
It is almost entirely in the **equal-degree split loop**
(`berlekampFactorLoop` → `splitFirstFactor?` → `kernelWitnessSplit?`),
which runs a full p-constant `gcd(factor, witness − c)` sweep for every
(current factor, kernel witness) pair — including the many *futile*
pairs where the witness is constant modulo the factor, which is **every**
witness once a factor is already irreducible.

A value-preserving guard that skips the constant sweep when
`witness mod factor` is constant takes a single deg-12 factorization over
F₁₃ from **76 ms to 6 ms (12.7×)** with **bit-identical factor output**.

## Method

A standalone profiling executable (linked against
`HexBerlekampZassenhaus.Basic` and `HexBerlekamp.Factor`) timed each
stage on the family `(X−(1+s))…(X−(12+s))`, `s = 0…31` — degree-12
integer polynomials that are squarefree mod 13 and select `p = 13` as the
first good prime (they have repeated roots mod 3, 5, 7, 11). Each timed
iteration consumes a *different* member of the family, indexed by the loop
counter, to defeat the loop-invariant hoisting / common-subexpression
elimination that silently collapses a fixed-input micro-benchmark to a
constant (an early fixed-input version reported the full factorization at
37 ns — the compiler had computed it once and reused the value).

Measured on the dev machine (Darwin arm64, Opus session worktree).

## Per-stage breakdown (deg-12 input, p = 13)

| Stage | Time | Share |
|---|---|---|
| `factorFast` (whole pipeline) | ~86 ms | 100 % |
| `choosePrimeData?` | ~74 ms | ~86 % |
| `isGoodPrime` over all scanned primes (3, 5, 7, 11, 13) | ~0.09 ms | 0.1 % |
| `monicModularImage` (mod-p reduction + monic normalize) | ~0.003 ms | <0.01 % |
| Berlekamp matrix build (`berlekampMatrix`) | ~0.09 ms | 0.1 % |
| Berlekamp matrix **+ nullspace** (`fixedSpaceKernel`) | ~1.76 ms | 2.3 % |
| Berlekamp factorization (`berlekampFactor`, full) | ~76 ms | — |
| → equal-degree **split loop** (full − kernel) | **~74 ms** | **97.7 % of the factorization** |

Key conclusions for deliverable 1:

- **(a) `isGoodPrime`'s gcd / squarefree test is negligible** (~0.1 %).
  The first-suitable prime change (the existing
  `choosePrimeDataScoreStep` comment) already removed the
  factor-at-every-prime cost; a single factorization remains.
- **(b) The Berlekamp matrix build + nullspace is small** (~2 %). The
  Frobenius column recurrence and the `HexMatrix` RREF nullspace are not
  the bottleneck; deliverable 2's "Q-matrix construction via repeated
  squaring vs naive powering" hypothesis is not where the time goes.
- **(c) The distinct/equal-degree split dominates** (~98 % of the
  factorization, ~86 % of `factorFast`).

The residual `factorFast − choosePrimeData?` (~12 ms) is the integer-side
work (Hensel lifting + van Hoeij recombination, the #8064 core); with the
split fixed it becomes the next visible cost.

## Why the split loop is slow

`berlekampFactor` computes the fixed-space kernel basis once (the `r`
witnesses, where `r` = number of irreducible factors), then repeatedly
calls `splitFirstFactor?`, which for the current factor tries every
witness, and for every witness runs `kernelWitnessSplit?` — a sweep of
`gcd(factor, witness − c)` over all `c ∈ F_p`.

The waste: a witness `w` yields a nontrivial split of `factor` **iff
`w mod factor` is non-constant**. Once a factor is irreducible, *every*
kernel witness is constant modulo it (that is the defining property of the
kernel mod an irreducible factor). So for each of the `r` final
irreducible factors, every `splitFirstFactor?` pass spends `r` witnesses ×
`p` constants = `r·p` futile gcds (here 12 × 13 ≈ 156) finding nothing,
and the loop makes `O(r)` passes. The total is `Θ(r²·p)` gcds, the
overwhelming majority futile. For the deg-12 / 12-factor case at p = 13
that is ~2×10⁴ gcd calls; at ~3 µs each (degree-12 dense EEA gcd with
allocation) this is the measured ~74 ms.

For comparison, FLINT / NTL factor the same input in microseconds. The
structural differences (deliverable 2):

- They use Cantor–Zassenhaus equal-degree splitting with **modular
  exponentiation** (`gcd(f, X^((p^d−1)/2) − 1)`), separating *all*
  factors of a given degree per gcd, instead of a per-constant linear
  sweep that re-tests every (witness, factor) pair.
- They never re-scan a factor already proved irreducible.

The hex implementation is deterministic Berlekamp (null space + linear
constant sweep), which is correct and proof-friendly but pays the
`Θ(r²·p)`-gcd tax. The matrix/null-space substrate is already fast.

## Validated fix (deliverable 3, designed + validated; landed via #8269)

The cheapest value-preserving win, prototyped and measured: in
`kernelWitnessSplit?`, reduce the witness modulo the factor once and skip
the entire constant sweep when the remainder is constant:

```
def kernelWitnessSplit? (f witness : FpPoly p) : Option (SplitResult p) :=
  if (witness % f).size ≤ 1 then none
  else kernelWitnessSplitAux f witness p 0
```

This is value-preserving: if `witness mod f` is a constant `k`, then for
every `c`, `gcd(f, witness − c) = gcd(f, (witness mod f) − c) =
gcd(f, k − c)`, which is `f` (when `c = k`) or a unit (otherwise) — never
a nontrivial split. So the guard returns `none` exactly when the full
sweep would have. Prototype measurement (guarded reimplementation of the
whole split loop, same kernel basis):

| | full split loop | with guard |
|---|---|---|
| `berlekampFactor`, deg-12 / p=13 | ~70–76 ms | **~6 ms** |

with **0 factor-multiset mismatches over 32 distinct inputs** (product of
per-factor checksums identical to the library `berlekampFactor`).

### Proof obligation for landing the fix

The guard is referenced by load-bearing lemmas (`RabinSoundness.lean`
consumes `kernelWitnessSplit?_some_of_nontrivial_splitFactorAt` and
`kernelWitnessSplit?_none_scale`), so it needs a completeness lemma:

> `(witness % f).size ≤ 1 → ∀ c, isNontrivialSplitFactor f
> (splitFactorAt f witness c) = false`

A clean divisibility proof (avoids unfolding `gcdAux`): let
`g = gcd f (witness − C c)`, `r = witness % f` with `r.size ≤ 1`.

- `g ∣ f` (`gcd_dvd_left`) and `g ∣ (witness − C c)` (`gcd_dvd_right`).
- `f ∣ (witness − r)` (`div_mul_add_mod` + `dvd_mul_left_poly`), so
  `g ∣ (witness − r)` (dvd-trans).
- `g ∣ ((witness − C c) − (witness − r)) = r − C c` (`dvd_sub_poly`),
  where `(r − C c).size ≤ 1`.
- If `r − C c ≠ 0`: `g ∣` a nonzero constant ⟹ `g.size ≤ 1` ⟹ not
  nontrivial (degree 0 or zero).
- If `r − C c = 0`: `f ∣ (witness − C c)`, so `f ∣ g` (`dvd_gcd`) and
  `g ∣ f`; mutual dvd ⟹ `g.size = f.size` ⟹ not (`g.size < f.size`).

Missing helper lemmas to build first (the FpPoly degree-additivity
`HexPolyFp.Basic.size_mul_eq_add_sub_one` and
`degree?_mul_eq_add_degree?` exist; these follow from them):

- `dvd → size_le` (`g ∣ h → h ≠ 0 → g.size ≤ h.size`);
- mutual-dvd ⟹ size equal;
- dvd-transitivity for `FpPoly` (inline via the `Dvd` unfolding);
- a size bound for subtraction of two `size ≤ 1` polynomials.

The four existing `kernelWitnessSplit?` lemmas (`_product_spec`,
`_nontrivial`, `_size_lt`, `_none_scale`) need the trivial `if`-split
update, and `_none_scale` additionally needs
`p % (scale c q) = p % q` for `c ≠ 0`.

The whole `HexBerlekampZassenhausMathlib` chain (CI-gated) rebuilds
unchanged because the factor output is bit-identical.
