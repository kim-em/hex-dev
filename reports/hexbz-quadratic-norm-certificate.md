# Certifying irreducibility through iterated quadratic norms

Swinnerton-Dyer polynomials factor into quadratics modulo every prime, so
Berlekamp-Zassenhaus recombination has to search `2^(w-1)` supports at modular
width `w`. `sd5` has `w = 16` and visits 32,768 support nodes to find one
divisor; `sd6` has `w = 32`, exceeds the recombination budget outright, and is
answered by the CLD lattice tier, which is where nearly all of its 7.95 s goes. This page is issue #9133's record:
what the class of polynomials in question actually is, the theorem and finite
certificate that decide irreducibility for it directly, a prototype outside
production, and the go/no-go measurement.

The verdict is **go**, on both the mathematics and the numbers. The theorem
holds for every iterated quadratic norm with multiplicatively independent
radicands -- an infinite class of which the corpus contains only Swinnerton-Dyer
instances and quadratics -- the certificate is two decidable checks, and on the
committed corpus the certificate is 861x faster than the production cascade on
`sd5` and 24,990x on `sd6`, at a median miss overhead of 0.14 us.

The gate that matters most is not either of those. Simulated onto the combined
cactus, the certificate alone takes the worst Hex/Isabelle cumulative ratio over
ranks 125 through 140 from 1.178x to 0.802x, which is #9126's success criterion.
Restricting the model to the three `sd5` rows still gives 0.829x, so the
conclusion does not rest on the whole certified set.

What is *not* delivered here is the Mathlib correspondence. The certificate is
checkable today and its meaning is proved below on paper; `Irreducible` is not
yet a Lean theorem about it. The final section says exactly what remains.

## Before starting: where Swinnerton-Dyer stands after #9129 and #9130

The issue asks for these numbers before any implementation, and for the issue to
be closed as a no-go if the general reconstruction already meets #9126's target
and `sd6` is no longer a material tail. Neither holds.

Source records: `reports/bench-results/hexbz-factor-sweep-596e9ce8-hex-chungus2.json`
(Hex, measured at this branch's revision `596e9ce8`, which changes no production
code -- the prototype is bench-only -- so it is also the post-#9129/#9130 state
the issue asks about) and
`reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json` (every other
system, reused unchanged), plus
`reports/bench-results/hexbz-phase-profile-a5e0ebe4-chungus2.json` and the
phase profiles taken for this page.

### Total times and the paired Isabelle gap

| row | degree | Hex | Isabelle | Isabelle / Hex |
|---|---:|---:|---:|---:|
| `sd4` | 16 | 0.868 ms | 1.196 ms | 1.38x |
| `sd4_shift1` | 16 | 0.804 ms | 1.233 ms | 1.53x |
| `sd4_shift3` | 16 | 0.874 ms | 1.211 ms | 1.39x |
| `sd4_x_phi17` | 32 | 6.669 ms | 4.567 ms | 0.68x |
| `sd4_x_phi35` | 40 | 17.677 ms | 26.190 ms | 1.48x |
| `sd4_x_sd4shift1` | 32 | 17.873 ms | 10.803 ms | 0.60x |
| `sd5` | 32 | 71.237 ms | 22.610 ms | **0.32x** |
| `sd5_shift1` | 32 | 66.235 ms | 14.815 ms | **0.22x** |
| `sd5_shift2` | 32 | 68.767 ms | 14.716 ms | **0.21x** |
| `sd5_x_phi11` | 42 | 140.592 ms | 27.545 ms | **0.20x** |
| `sd5_x_phi45` | 56 | 322.643 ms | timeout | -- |
| `sd5_x_sd5shift1` | 64 | timeout | timeout | -- |
| `sd6` | 64 | 7.953 s | timeout | -- |
| `sd6_shift1`, `sd6_shift5` | 64 | timeout | timeout | -- |
| `sd6_x_phi13`, `sd6_x_phi105`, `sd6_x_sd6shift1` | 76--128 | timeout | timeout | -- |
| `sd7`, `hoeij_S7` | 128 | timeout | timeout | -- |
| `hoeij_S8`, `hoeij_S9` | 256, 512 | timeout | timeout | -- |

A ratio below 1 is a row where Isabelle is faster. The four bolded rows are the
worst paired deficits anywhere in the elbow: nothing else in ranks 125--140 is
below 0.43x. `sd6_shift1` does terminate, at 22.33 s, well past the 10 s sweep
cutoff.

### Modular width, support nodes, rejections, and exact divisions

From the phase profile at `a5e0ebe4`, all at prime 29:

| row | width | lifted degrees | support nodes | cheap-filter rejections | products built | exact divisions |
|---|---:|---|---:|---:|---:|---:|
| `sd5` | 16 | all 2 | 32,768 | 32,639 | 129 | 1 |
| `sd5_shift1` | 16 | all 2 | 32,768 | 32,767 | 1 | 1 |
| `sd5_shift2` | 16 | all 2 | 32,768 | 32,767 | 1 | 1 |
| `sd4_x_sd4shift1` | 16 | all 2 | 10,540 | 10,530 | 10 | 2 |
| `sd5_x_phi11` | 17 | 2 and 10 | 65,522 | 65,264 | 258 | 2 |

This is the shape #9130 already recorded: the metadata-only prefilters reject
essentially everything, exact division runs once or twice, and the cost is the
traversal itself. #9130 moved `sd5` by 0.942x for exactly that reason. `sd6` has
width 32, so `2^31` supports exceed the 262,144-node budget; classical
recombination declines and the CLD lattice answers, taking 7.941 s of `sd6`'s
7.986 s. Nothing in the recombination line of work reaches either case: the
first is a traversal whose size is set by the modular width, the second is not a
traversal at all.

### #9126's target is not met

Cumulative Hex/Isabelle over the combined mixture, from
`scripts/bench/cactus_rank_table.py`:

| rank | 125 | 128 | 130 | 133 | 135 | 138 | 140 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Hex / Isabelle | 0.78x | 0.92x | 1.01x | 1.16x | 1.18x | 0.86x | 0.61x |

The criterion is at most 0.85x at every rank from 125 through 140. The worst
point is 1.178x at rank 135, and ranks 130--138 all fail. Swinnerton-Dyer rows
occupy Hex ranks 134, 135, 136, and 138 and contribute 347 ms of the 862 ms
cumulative at rank 138 against Isabelle's 79.7 ms for the same four inputs.

So the no-go branch in the issue body does not apply, and neither does treating
`sd6` as immaterial: it is the single slowest solved row in the corpus.

## The mathematics

### The construction

For `d ∈ ℤ` and monic `g ∈ ℤ[X]`, the **quadratic norm** of `g` at `d` is the
norm of `g(X - t)` along `ℤ[t]/(t² - d) → ℤ`:

    N_d(g)(X) = g(X - t) · g(X + t),   t² = d.

Writing `g(X - t) = A(X) + t·B(X)` with `A, B ∈ ℤ[X]`, this is `A² - d·B²`, so
it lies in `ℤ[X]`; it is monic of degree `2·deg g`; and its roots are `β ± √d`
as `β` runs over the roots of `g`. Iterating from `X - c`,

    F(c; d₁, …, dₙ) := N_{dₙ}(⋯ N_{d₁}(X - c) ⋯)
                      = ∏_{ε ∈ {±1}ⁿ} (X - c - ∑ᵢ εᵢ √dᵢ),

a monic integer polynomial of degree `2ⁿ`. `SD_n` is `F(0; p₁, …, pₙ)` and the
corpus's shifted rows are `F(-k; p₁, …, pₙ)`, but the definition asks nothing of
the radicands beyond being integers.

### The independence hypothesis is not optional

`F(c; d)` is *not* irreducible for arbitrary radicands, and the failure is not
exotic. Take `d = (2, 3, 6)`. Then `ℚ(√2, √3, √6) = ℚ(√2, √3)` has degree 4, not
8, and `F(0; 2, 3, 6)` has degree 8. Feeding it to `Hex.ZPoly.factorize`:

| radicands | subproduct that is a square | degree | production factor degrees |
|---|---|---:|---|
| `2, 3, 6` | `2·3·6 = 36` | 8 | 4, 4 |
| `12, 20, 45` | `20·45 = 900` | 8 | 4, 4 |
| `2, 3, 5` | none | 8 | 8 |

The second row is the one to keep in mind: `12, 20, 45` are pairwise distinct,
none is a square, and no two of them look related, yet `20·45 = 900`. Any
certificate that checks only "each `dᵢ` is a nonsquare" or only pairwise
conditions accepts a reducible polynomial. The correct hypothesis is on the
whole subgroup the radicands generate.

**Independence.** `d₁, …, dₙ ∈ ℤ` are *independent square classes* when no
nonempty subproduct `d_T = ∏_{i∈T} dᵢ` is a perfect square. Equivalently, their
images generate a subgroup of order `2ⁿ` in `ℚ*/(ℚ*)²`: an integer is a rational
square exactly when it is a perfect square, so the two statements are the same
statement. A zero radicand (`0 = 0²`) and a repeated radicand (`dᵢ·dⱼ = dᵢ²`) are
both excluded by it, as they must be.

### The tower theorem

**Theorem.** Let `d₁, …, dₙ ∈ ℤ` be independent square classes and `c ∈ ℤ`. Put
`K = ℚ(√d₁, …, √dₙ)` and `α = c + ∑ᵢ √dᵢ`. Then

1. `[K : ℚ] = 2ⁿ`;
2. `ℚ(α) = K`;
3. `F(c; d₁, …, dₙ)` is the minimal polynomial of `α` over `ℚ`, and is therefore
   irreducible in `ℚ[X]`; being monic with integer coefficients, it is
   irreducible in `ℤ[X]`.

*Lemma A.* Let `F` be a field of characteristic `≠ 2`, `a ∈ F` not a square in
`F`, and `K = F(√a)`. If `b ∈ F` is a square in `K`, then `b` or `a·b` is a
square in `F`.

*Proof.* Write `b = (x + y√a)² = (x² + a y²) + 2xy√a` with `x, y ∈ F`. As
`{1, √a}` is an `F`-basis of `K` and `char F ≠ 2`, `xy = 0`. If `y = 0` then
`b = x²`; if `x = 0` then `b = a y²`, so `a·b = (a y)²`. ∎

*Proof of (1).* Let `K_m = ℚ(√d₁, …, √d_m)`, and let `Claim(m)` be: for every
`T ⊆ [n]` meeting `{m+1, …, n}`, `d_T` is not a square in `K_m`.

`Claim(0)` is the independence hypothesis, since a rational square that is an
integer is a perfect square. Assume `Claim(m-1)`. Taking `T = {m}`, which meets
`{m, …, n}`, gives that `d_m` is not a square in `K_{m-1}`, so
`[K_m : K_{m-1}] = 2` and Lemma A applies with `F = K_{m-1}`, `a = d_m`. Let `T`
meet `{m+1, …, n}` and suppose `d_T` were a square in `K_m`. Then `d_T` or
`d_m·d_T` is a square in `K_{m-1}`. Now `d_m·d_T` differs from `d_{T Δ {m}}` by
the square factor `d_m²` when `m ∈ T`, and equals it otherwise. Both `T` and
`T Δ {m}` still meet `{m+1, …, n}`, hence meet `{m, …, n}`, so `Claim(m-1)`
refuses both. Contradiction, so `Claim(m)` holds.

`Claim(m-1)` with `T = {m}` gives `[K_m : K_{m-1}] = 2` for every `m`, and the
tower law gives `[K : ℚ] = 2ⁿ`. ∎

*Proof of (2).* `K` is the splitting field over `ℚ` of `∏ᵢ (X² - dᵢ)` and
`char ℚ = 0`, so `K/ℚ` is Galois with `|G| = 2ⁿ` for `G = Gal(K/ℚ)`. Each `σ ∈ G`
is determined by the signs `εᵢ(σ)` in `σ(√dᵢ) = εᵢ(σ)√dᵢ`, so `σ ↦ (εᵢ(σ))` is an
injection `G → {±1}ⁿ` between sets of size `2ⁿ`, hence a bijection.

Suppose `σ(α) = α` for `σ ≠ 1`, flipping exactly the nonempty set `S`. Then
`∑_{i ∈ S} √dᵢ = 0`. Pick `j ∈ S`: then `√d_j ∈ ℚ(√dᵢ : i ∈ S \ {j})`, which is
contained in `ℚ(√dᵢ : i ≠ j)`. The independence hypothesis is symmetric in the
indices, so (1) applies with `j` placed last and says `d_j` is not a square in
`ℚ(√dᵢ : i ≠ j)`. Contradiction. So `Gal(K/ℚ(α)) = Stab_G(α) = 1`, and the
Galois correspondence gives `ℚ(α) = K`. ∎

*Proof of (3).* The same trivial-stabilizer argument shows the `2ⁿ` values
`c + ∑ εᵢ√dᵢ` are pairwise distinct, so the Galois orbit of `α` has exactly `2ⁿ`
elements and `∏_{β ∈ orbit}(X - β) = F(c; d)`. That product is the minimal
polynomial of `α`, of degree `2ⁿ = [ℚ(α) : ℚ]` by (2), hence irreducible over
`ℚ`. A monic integer polynomial irreducible over `ℚ` and of positive degree is
irreducible in `ℤ[X]`, its content being 1. ∎

Note where each hypothesis is used: independence gives (1) directly, and (2)
needs it again *after reordering the indices*, which is why the hypothesis has
to be a statement about all subsets rather than about the tower as built. A
certificate carrying only "each successive extension is nontrivial" would prove
(1) and not (2).

### The certificate

A certificate for `f ∈ ℤ[X]` is a pair `(c; d₁, …, dₙ)`, checked by:

* **independence** -- for each of the `2ⁿ - 1` nonempty `T ⊆ [n]`, `d_T` is not a
  perfect square;
* **identification** -- `F(c; d₁, …, dₙ) = f` coefficientwise.

By the theorem, a certificate that passes both proves `f` irreducible. Both
checks are decidable by integer arithmetic with no number field constructed, no
factorization of the radicands, and no floating point: the first is `2ⁿ - 1`
integer square tests on products of the `dᵢ`, the second is `n` quadratic norms
and an array comparison.

Two things the identification check settles by construction, which the issue
asks to be explicit about. *Translation* is a certificate field, not a
normalization step: `F(c; d)` carries it. *Sign and content*: every `F(c; d)` is
monic, so the certificate applies to `f` exactly when `f` is `±` a monic integer
polynomial. A primitive integer polynomial with leading coefficient outside
`{1, -1}` is never `± F(c; d)`, and negation is a unit of `ℤ[X]`, so the whole
normalization is "negate if the leading coefficient is `-1`, then compare". No
scaling, no content division, no reordering: the identification is literal
coefficient equality.

### Recovering the certificate

The search side need not be trusted -- a wrong guess dies in the check -- but it
has a closed form, which is what makes the recogniser mathematics rather than a
table.

Summing over sign patterns, `∑_ε exp(t·α_ε) = 2ⁿ ∏ᵢ cosh(t√dᵢ)`. Let `p_k` be
the power sums of the roots of the centred polynomial `f(X + c)`, where
`c = -a_{N-1}/N` with `N = 2ⁿ`, and put `u_k = p_{2k} / (N·(2k)!)`. Then

    ∑_k u_k sᵏ = ∏ᵢ C(dᵢ·s),    C(z) = cosh √z = ∑_j zʲ/(2j)!.

Taking logarithms turns the product into a sum. Writing `γ_k = [w^{2k}] log cosh w`
-- a nonzero rational independent of the input, `1/2, -1/12, 1/45, -17/2520, …` --
the coefficient of `sᵏ` on the right is `γ_k · ∑ᵢ dᵢᵏ`, so

    ∑ᵢ dᵢᵏ = ([sᵏ] log ∑_k u_k sᵏ) / γ_k,   k = 1, …, n.

Newton's identities turn those power sums into `∏ᵢ (y - dᵢ)`, whose integer
roots are the radicands. Every step is exact rational arithmetic on the top
`2n + 1` coefficients of `f`, and `∑ᵢ dᵢ²` bounds each `|dᵢ|`, which bounds the
root search. A polynomial outside the class fails at the first structural test
it meets -- degree not a power of two, `2ⁿ ∤ a_{N-1}`, a non-integral
intermediate, or too few integer roots -- and the measured cost of that failure
is in the miss table below.

## The prototype

`bench/HexBench/QuadraticNorm.lean`, reachable only from the benchmark service.
It is not imported by `HexBerlekampZassenhaus` and `Hex.ZPoly.factorize` is
unchanged; issue #9133 asks for the gate to be decided outside production, and
it was.

`hexbz_factor_service --entry quadraticNormProbe` times one production
factorization and the four certificate stages on the same input in the same
process. `--entry quadraticNormCertificate` runs the certificate stages alone,
for the rows the production cascade does not finish and for the corpus-wide miss
sweep. Each stage folds its result into a reported witness before its closing
mark; without that the compiler sinks each pure `let` to its only use and the
whole certificate cost lands in whichever span is last.

`scripts/bench/quadratic_norm_probe.py` drives both and writes
`reports/bench-results/hexbz-quadratic-norm-certificate-chungus2.json`.
`scripts/bench/quadratic_norm_witnesses.py` builds off-corpus cases from an
independent Python implementation of the iterated norm and checks the Lean
implementation against them, writing
`reports/bench-results/hexbz-quadratic-norm-witnesses.json`.

### Revision and protocol

* Source revision as recorded in each record's `env.git_commit`, Lean toolchain
  `leanprover/lean4:v4.33.0-rc1`.
* Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores; harness and service
  pinned to CPU 0 with `taskset -c 0`.
* Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`; the
  combined mixture the cactus plots is its 160 `combined` rows.
* Each span is the median of five calls. The paired production span follows the
  sweep's own policy: median of five when one call is under a second, a single
  call otherwise.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-quadratic-norm-certificate-chungus2.json` | `5b5db6c69fbaf229b27a22479af794d64d182caa51f150ef6fbcacd3ac9a1990` |
| `reports/bench-results/hexbz-quadratic-norm-witnesses.json` | `64723966d0122d231d56304fd2567befb15e3c6bb4232517c624ea6117d8b44e` |
| `reports/bench-results/hexbz-quadratic-norm-cactus-model.json` | `8f390e1ed9f204257c751c5aada829a11b001fd7042477bdaf3d0d21413ae26e` |

All three were measured at revision `d1b39951`, against the sweep committed
here, with no modified source. Each carries the SHA-256 of the service binary it measured, which
pins the code more tightly than the commit does. The cactus model additionally
records the two sweeps and the certificate record it read.

## Measured effect

### Certified rows, construction and checking separately

All times in microseconds; `production` is the paired in-process factorization,
and the ratio is the median of the per-observation ratios rather than a ratio of
two medians, so both sides describe one execution.

| row | degree | recovery | independence | construction | equality | certificate | paired | production | ratio |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `conway_p3_n2` | 2 | 2.8 | 0.2 | 0.2 | 0.1 | 3.3 | 3.1 | 0.017 ms | 5x |
| `conway_p65537_n2` | 2 | 2.9 | 0.2 | 0.2 | 0.1 | 3.4 | 3.4 | 0.029 ms | 8x |
| `sd2` | 4 | 7.7 | 0.5 | 0.3 | 0.1 | 8.6 | 7.2 | 0.037 ms | 5x |
| `sd3` | 8 | 10.7 | 1.4 | 0.6 | 0.1 | 12.8 | 13.1 | 0.152 ms | 11x |
| `sd4` | 16 | 17.4 | 4.3 | 1.4 | 0.1 | 23.2 | 25.1 | 0.846 ms | 34x |
| `sd4_shift3` | 16 | 17.5 | 4.3 | 5.2 | 0.1 | 27.2 | 29.5 | 0.877 ms | 30x |
| `sd5` | 32 | 36.2 | 11.3 | 22.1 | 0.3 | 69.8 | 80.1 | 68.755 ms | **861x** |
| `sd5_shift1` | 32 | 52.9 | 10.8 | 58.1 | 0.4 | 122.2 | 130.6 | 64.104 ms | 493x |
| `sd5_shift2` | 32 | 52.9 | 10.6 | 61.2 | 0.4 | 125.1 | 141.6 | 66.949 ms | 474x |
| `sd6` | 64 | 100.7 | 25.4 | 157.1 | 0.5 | 283.6 | 323.1 | 8.075 s | **24990x** |
| `sd6_shift1` | 64 | 194.1 | 25.5 | 363.2 | 0.9 | 583.7 | 651.6 | 22.088 s | 33898x |
| `sd6_shift5` | 64 | 204.7 | 25.6 | 442.0 | 0.9 | 673.2 | -- | timeout | -- |
| `hoeij_S7` | 128 | 366.6 | 61.3 | 855.9 | 1.0 | 1284.7 | -- | timeout | -- |
| `sd7` | 128 | 367.9 | 61.5 | 859.9 | 1.0 | 1290.4 | -- | timeout | -- |
| `hoeij_S8` | 256 | 1379.5 | 142.6 | 3801.0 | 2.1 | 5325.1 | -- | timeout | -- |
| `hoeij_S9` | 512 | 5985.3 | 330.6 | 17619.2 | 6.4 | 23941.5 | -- | timeout | -- |

The four stage columns come from a certificate-only process, which is what
classifies every row and what the whole-corpus miss sweep uses. `paired` is the
same total measured inside the *paired* process, alongside the production
factorization it is being divided into; it reads a little slower there, and it
is the column the ratio uses, so both sides of every ratio describe one
execution rather than two runs subtracted.

Twenty-four of the corpus's 392 rows certify: eighteen Swinnerton-Dyer rows and
translates, and six degree-two Conway polynomials, which are the `n = 1` case of
the theorem. The gate asks for at least 5x on `sd5` and a material reduction on
`sd6`; the measurements are 861x and 24,990x. Four rows the production cascade
cannot finish inside the cutoff --
`sd6_shift5`, `sd7`/`hoeij_S7`, `hoeij_S8`, `hoeij_S9` -- certify in under 24 ms,
`hoeij_S9` at degree 512.

Cost splits as expected: recovery is `O(n²)` rational operations on the top
`2n+1` coefficients and dominates at small degree; the iterated-norm
construction is `O(N²)` big-integer multiplications and dominates from degree 32
up; the independence test is `2ⁿ - 1` square tests on integers below 510,510 and
never exceeds 331 us, all of it at degree 512; the equality test is under seven
microseconds everywhere,
because by the time it runs both sides are already built.

### Miss overhead

Over the 368 declining rows: **median 0.14 us, maximum 85.9 us.** The median is
the degree test -- most of the corpus does not have power-of-two degree, and
those rows are refused in a few hundred nanoseconds. The rows that pay anything
are those with power-of-two degree *and* `2ⁿ | a_{N-1}`, which then run the
rational recovery to a contradiction:

| declining row | degree | cost |
|---|---:|---:|
| `cyclo_phi256` | 128 | 85.9 us |
| `laguerre_L32` | 32 | 72.4 us |
| `cyclo_phi128` | 64 | 42.1 us |
| `conway_p2_n32` | 32 | 26.4 us |
| `wilkinson_32` | 32 | 0.2 us |

`wilkinson_32` is the shape of the common case: degree 32 is a power of two, but
its roots sum to 528 and `32 ∤ 528`, so it is refused before any series
arithmetic. This is why the median is what it is, and it is why the recogniser
should still be budget-gated rather than unconditional: `cyclo_phi128` factors in
about a millisecond, so 42 us on it is 4%, well above the 1% the gate asks for
even though the corpus median is far below it.

### Breadth: the class is not the benchmark

Of the 24 certifying corpus rows, 18 are Swinnerton-Dyer polynomials or
translates -- and `hoeij_S7`--`hoeij_S9` are `SD_7`--`SD_9` vendored from
Hart-van Hoeij-Novocin, so they are the same family under another name -- while
the other six are degree-two Conway polynomials, which are the `n = 1` case and
so are the weakest possible evidence of breadth. The corpus therefore cannot by
itself distinguish "recognises the mathematics" from "recognises that shape".
`scripts/bench/quadratic_norm_witnesses.py` supplies the distinction: 15
off-corpus cases built from an independent implementation, each checked against
what the theorem says the answer must be.

| witness | degree | radicands | expected | got |
|---|---:|---|---|---|
| `gaussian_sqrt2` | 4 | `-1, 2` | certify | certify |
| `negative_pair` | 4 | `-2, -5`, translation 3 | certify | certify |
| `composite_coprime` | 8 | `6, 10, 21`, translation 7 | certify | certify |
| `descending_primes` | 64 | `13, 11, 7, 5, 3, 2` | certify | certify |
| `mixed_signs` | 16 | `-1, 6, 35, 22`, translation -11 | certify | certify |
| `large_translation` | 8 | `2, 3, 5`, translation 1000003 | certify | certify |
| `nonconsecutive_primes` | 16 | `3, 17, 101, 1009` | certify | certify |
| `deg1024` | 1024 | first ten primes, translation 3 | certify | certify |
| `squarefull_radicands` | 8 | `12, 20, 45` | refuse | refuse |
| `dependent_product` | 8 | `2, 3, 6` | refuse | refuse |
| `dependent_pair` | 4 | `7, 28` | refuse | refuse |
| `dependent_squarefull` | 16 | `2, 3, 5, 30` | refuse | refuse |
| `repeated_radicand` | 8 | `2, 3, 2` | refuse | refuse |
| `zero_radicand` | 4 | `2, 0` | refuse | refuse |
| `perturbed_sd6` | 64 | one coefficient moved by 1 | refuse | refuse |

Negative radicands, composite radicands, radicands sharing prime support,
descending tower order, a translation of a million, and degree 1024 all
certify; every dependent set is refused, and so is a certified polynomial with a
single coefficient perturbed. Each certified case also recovers the same square
classes it was built from. The recogniser reads the coefficients, not the name.

### The theorem against the production factorizer

The same driver's randomized pass is the sharper check, because it puts the
theorem itself to an independent decision procedure. For 250 random
(translation, radicand-tuple) pairs drawn from a pool of negative, prime,
composite, and square-full radicands, it compares three verdicts: the
arithmetic independence test, the certificate, and whether
`Hex.ZPoly.factorize` returns a single factor of full degree.

**All 250 agree, in both directions**, 199 of them certified. A
certified-but-reducible case would refute the theorem outright. An
independent-but-reducible case would refute it too. And a
dependent-but-irreducible case would show the independence hypothesis is
strictly stronger than irreducibility needs -- there is none, so on this sample
the hypothesis is exactly right rather than merely sufficient.

The seed is fixed, so the run reproduces; `--random 0` disables it and
`--seed` changes the sample.

### Modelled effect on the combined cactus

The certificate is not on the production path, so its effect on the cactus is a
model. `scripts/bench/quadratic_norm_cactus_model.py` *is* that model: it reads
the pinned sweeps and the certificate record, states its replacement rule in
code, measures the retained phases per row, and prints the tables below, so
nothing here is a hand-carried number.

The replacement rule is: a certified row keeps the phases the placement names,
measured by `--entry factorPhaseProfile`, and the certificate replaces the
Hensel lift, recombination, proposal replay, and the CLD lattice. A row the
sweep does not solve is left exactly as measured, because `factorPhaseProfile`
runs the whole cascade and cannot be taken on it -- so the model never credits
an improvement it has not priced.

**Post-prime**, the conservative placement: the row runs normalization and the
bounded good-prime walk exactly as today, and the certificate is attempted once
the modular factorization is in hand. Say plainly what this is *not*: it is not
gated on the existing 262,144-node recombination budget, which `sd5`'s
32,768-node walk sits under and would never trip. Whatever predicate a
production integration uses has to admit `sd5`, and the price of admitting it
is the miss overhead above, paid by every row that reaches the same point and
declines.

| row | now | modelled | retained | certificate |
|---|---:|---:|---:|---:|
| `sd4` | 0.868 ms | 0.426 ms | 0.402 ms | 23.2 us |
| `sd5` | 71.237 ms | 6.777 ms | 6.707 ms | 69.8 us |
| `sd5_shift1` | 66.235 ms | 7.330 ms | 7.207 ms | 122.2 us |
| `sd5_shift2` | 68.767 ms | 9.110 ms | 8.985 ms | 125.1 us |
| `sd6` | 7.953 s | 27.845 ms | 27.561 ms | 283.6 us |

The retained column is the whole cost in every row: the certificate is two to
four orders of magnitude below the prime walk it follows. Cumulative
Hex/Isabelle over ranks 125--140:

| rank | 125 | 128 | 130 | 133 | 135 | 138 | 140 |
|---|---:|---:|---:|---:|---:|---:|---:|
| now | 0.78x | 0.92x | 1.01x | 1.16x | 1.18x | 0.86x | 0.61x |
| modelled | 0.69x | 0.73x | 0.75x | 0.80x | 0.79x | 0.56x | 0.45x |

Worst ratio over ranks 125--140: **1.178x now, 0.802x modelled**, against
#9126's 0.85x criterion. The certificate alone clears it, with the rows #9126
named as also needing parity -- `x^n - 1`, `cyclo_phi179`,
`cyclo_phi64_x_phi105` -- untouched.

That conclusion does not rest on the whole certified set. Restricting the
replacement to the three `sd5` rows with `--only sd5,sd5_shift1,sd5_shift2`
gives a worst ratio of **0.829x**, still under the target. The `sd4` and `sd6`
rows widen the margin; they do not create it.

**Post-normalization**, the permissive placement: the certificate is attempted
after normalization, behind the free structural pre-gate, so a certified row
skips the prime walk too. Worst ratio 0.682x on the same priced rows.

Two things this model deliberately does not claim. It does not credit the six
rows the cascade cannot finish -- `sd6_shift1`, `sd6_shift5`, `sd7`,
`hoeij_S7`, `hoeij_S8`, `hoeij_S9` -- with becoming solved, even though each
certifies in between 0.6 and 23.7 ms, because their retained phases cannot be
measured through an entry that runs the cascade to completion. A
post-normalization integration would very likely solve all six and take the
solved count from 145 to 151, but that is a projection, not a modelled result.
And it is a model over measured times, not a measurement: the fresh sweep an
implementation PR owes is what settles it.

## Go/no-go

| gate | verdict |
|---|---|
| theorem applies to a natural class broader than the benchmark rows | **yes** -- all independent radicands and translations; 8 off-corpus witnesses including negative, composite, and degree-1024 cases |
| covers SD5 and SD6 from their mathematical input data without case tables | **yes** -- radicands recovered from the top `2n+1` coefficients; `sd7`, `hoeij_S8`, `hoeij_S9` too |
| certificate generation plus checking at least 5x faster than SD5, materially reduces SD6 | **yes** -- 861x and 24,990x, both sides read off the same paired in-process observations |
| small, reviewable trust surface | **executable side yes** (see below); the Mathlib proof is the open cost |
| unsuccessful detection under 1% median overhead, preferably opt-in | **yes** on the median -- 0.14 us against a maximum of 85.9 us -- but see the placement discussion: the post-prime placement's predicate has to admit `sd5`, so it is not simply the existing recombination budget, and whatever predicate is chosen decides which rows pay the 87 us tail |

The executable trust surface is `quadNorm`, `iteratedNorm`,
`isPerfectSquare`, `independentSquareClasses`, and one array comparison: about
60 lines, no floating point, no primality testing, no factorization, no
randomness. Recovery is outside it entirely -- it may return anything, and a
wrong answer is refused by the check.

The mathematical surface is the theorem above. Lemma A is three lines, the
`Claim(m)` induction is elementary and needs no Kummer theory, and the Galois
input is that a multiquadratic field is the splitting field of a separable
polynomial. What it does need from Mathlib is the Galois correspondence for
`ℚ(α) = Fix(Stab α)` and `minpoly` as the orbit product.

## What an implementation still owes

The certificate is checkable and its meaning is proved on paper. Turning that
into `Irreducible` inside Lean is the remaining work, and it is not small:

1. **The tower theorem** -- Lemma A, the `Claim(m)` induction, and `[K:ℚ] = 2ⁿ`
   (#9167); then the trivial-stabilizer argument, `ℚ(α) = K`, and
   `minpoly α = F(c; d)` (#9169). Mathlib-facing, and the largest piece.
2. **The norm correspondence** -- that the executable `quadNorm` over
   `ℤ[t]/(t² - d)` maps to `g(X - √d)·g(X + √d)` in `K[X]`, and that the iterate
   is the product over sign patterns (#9168). This is where the dense-array
   representation meets `Polynomial`, the boundary
   `.claude/skills/hex-lean-mathlib-boundary` is about.
3. **The decidable checks** -- `independentSquareClasses ds = true` implies no
   nonempty subproduct is a rational square, and coefficient equality implies
   polynomial equality. Both are small, and both ride along with #9168.
4. **Production integration** -- a `Certificate` in the Mathlib-free layer, the
   checker on the singleton-irreducibility path so a success returns the same
   `Factorization` as every other proof, and the budget gate (#9170). Failure
   must fall through to the one existing path.
5. **A fresh sweep and regenerated plots** at the integrated revision, with all
   regressions above 5% reported; also #9170, and what #9126's acceptance run
   will read.

Nothing above needs `axiom`, `sorry`, or `native_decide`; the check is a `Bool`
and the theorem is about it being `true`.

## Regeneration

```
lake build hexbz_factor_service

# Certificate spans for every corpus row, paired against production where the
# cascade finishes. Pin to an idle core; other work shares this host.
taskset -c 0 python3 scripts/bench/quadratic_norm_probe.py \
    --output reports/bench-results/hexbz-quadratic-norm-certificate-chungus2.json

# Off-corpus witnesses, checked against an independent implementation.
taskset -c 0 python3 scripts/bench/quadratic_norm_witnesses.py \
    --output reports/bench-results/hexbz-quadratic-norm-witnesses.json

# The fresh Hex sweep this page's before-numbers read, and the figures it
# invalidates. `--check` fails until the SVGs are regenerated.
taskset -c 0 python3 scripts/bench/factor_sweep.py --systems hex-factor \
    --cutoff 10 \
    --output reports/bench-results/hexbz-factor-sweep-596e9ce8-hex-chungus2.json
python3 scripts/plots/hexbz-cactus.py
python3 scripts/plots/hexbz-cactus.py --check

# The elbow the model is against, and the model itself. `--only` and
# `--placement` reproduce the restricted and permissive variants.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 145
taskset -c 0 python3 scripts/bench/quadratic_norm_cactus_model.py \
    --output reports/bench-results/hexbz-quadratic-norm-cactus-model.json
taskset -c 0 python3 scripts/bench/quadratic_norm_cactus_model.py \
    --only sd5,sd5_shift1,sd5_shift2
taskset -c 0 python3 scripts/bench/quadratic_norm_cactus_model.py \
    --placement post-normalization

```
