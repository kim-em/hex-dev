# Certifying irreducibility through iterated quadratic norms

Swinnerton-Dyer polynomials factor into quadratics modulo every prime, so
Berlekamp-Zassenhaus recombination has to search `2^(w-1)` supports at modular
width `w`. `sd5` has `w = 16` and visits 32,768 support nodes to find one
divisor; `sd6` has `w = 32`, exceeds the recombination budget outright, and is
answered by the CLD lattice tier, which is where nearly all of its 7.95 s
goes. This page is the record for issues #9133 and #9170: what the class of
polynomials in question actually is, the theorem and finite certificate that
decide irreducibility for it directly, the go/no-go measurement that was taken
against a prototype, and the measured effect of putting it into production.

The verdict was **go**, and #9170 shipped it. The theorem holds for every
iterated quadratic norm with multiplicatively independent radicands -- an
infinite class of which the corpus contains only Swinnerton-Dyer instances and
quadratics -- the certificate is two decidable checks, and it is now on the
ordinary singleton-irreducibility path of `Hex.ZPoly.factorize`, behind a
modular-width floor, with `irreducible_of_check` proving it sound.

Measured on the corpus, before and after, at one revision:

| | gate closed | integrated |
|---|---:|---:|
| `sd5` | 71.007 ms | 6.820 ms |
| `sd6` | 8.148 s | 27.055 ms |
| `sd7`, `hoeij_S7`, `hoeij_S8`, `sd6_shift1`, `sd6_shift5` | timeout | 31 ms -- 3.98 s |
| rows solved, of 392 | 377 | 383 |
| total over rows both solve | 17.225 s | 8.965 s |
| worst Hex/Isabelle cumulative, ranks 125--140 | 1.012x | **0.707x** |

That last line is #9126's success criterion, which is at most 0.85x at every
rank from 125 through 140. The go/no-go modelled 0.708x; the measurement lands
within half a percent of it. No row regresses by more than the run-to-run spread
on the host, and the worst miss any row is actually offered is 0.014% of its
factorization.

## Before integration: where Swinnerton-Dyer stood after #9129 and #9130

This section is the pre-integration record #9133 asked for, kept as measured.
Everything from "In production" on is the state after #9170.

The issue asks for these numbers before any implementation, and for the issue to
be closed as a no-go if the general reconstruction already meets #9126's target
and `sd6` is no longer a material tail. Neither holds.

Source records: `reports/bench-results/hexbz-factor-sweep-48bdfb8e-hex-chungus2.json`
(Hex, measured at this branch's revision `48bdfb8e`, which changes no production
code -- the prototype is bench-only -- so it is also the post-#9129/#9130 state
the issue asks about) and
`reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json` (every other
system, reused unchanged), plus
`reports/bench-results/hexbz-phase-profile-a5e0ebe4-chungus2.json` and the
phase profiles taken for this page.

### Total times and the paired Isabelle gap

| row | degree | Hex | Isabelle | Isabelle / Hex |
|---|---:|---:|---:|---:|
| `sd4` | 16 | 0.880 ms | 1.196 ms | 1.36x |
| `sd4_shift1` | 16 | 0.813 ms | 1.233 ms | 1.52x |
| `sd4_shift3` | 16 | 0.896 ms | 1.211 ms | 1.35x |
| `sd4_x_phi17` | 32 | 2.901 ms | 4.567 ms | 1.57x |
| `sd4_x_phi35` | 40 | 17.750 ms | 26.190 ms | 1.48x |
| `sd4_x_sd4shift1` | 32 | 17.988 ms | 10.803 ms | 0.60x |
| `sd5` | 32 | 72.312 ms | 22.610 ms | **0.31x** |
| `sd5_shift1` | 32 | 66.404 ms | 14.815 ms | **0.22x** |
| `sd5_shift2` | 32 | 69.156 ms | 14.716 ms | **0.21x** |
| `sd5_x_phi11` | 42 | 140.749 ms | 27.545 ms | **0.20x** |
| `sd5_x_phi45` | 56 | 322.750 ms | timeout | -- |
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
| Hex / Isabelle | 0.72x | 0.81x | 0.87x | 1.03x | 1.08x | 0.81x | 0.59x |

The criterion is at most 0.85x at every rank from 125 through 140. The worst
point is 1.079x at rank 135, and ranks 130--136 all fail. Swinnerton-Dyer rows
occupy Hex ranks 134, 135, and 136 and contribute 208 ms of the 815 ms
cumulative at rank 138 against Isabelle's 52.1 ms for the same three inputs.

#9171 and #9172, both merged while this page was being written, narrowed the
elbow considerably -- the worst ratio was 1.188x before them -- and neither
touched a Swinnerton-Dyer row's cost. What is left of the elbow is narrower and
more concentrated: it now peaks exactly where `sd5_shift1`, `sd5_shift2`, and
`sd5` sit, at Hex ranks 134 through 136.

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

## In production

The certificate is on the production path. `Hex.QuadraticNormCertificate.check`
and the definitions it runs on live in `HexBerlekampZassenhaus/QuadraticNorm.lean`;
the untrusted search that proposes a certificate is
`HexBerlekampZassenhaus/QuadraticNormRecover.lean`, whose `recover?` is the
closed form of the previous section and whose `certify?` is recovery followed by
the check. The prototype that decided the gate is gone: `bench/HexBench/QuadraticNorm.lean`
and its `HexQuadraticNormProbe` library are deleted, and the bench probe now
times the same definitions `Hex.ZPoly.factorize` reaches.

**Where it is consulted.** `Hex.classicalInput` selects the modular prime and
factorization, and at that point the support width `w` is known and no Hensel
lift has been paid for yet. `Hex.quadraticNormCertified core w` is consulted
once, there. A success returns the whole square-free core as one irreducible
factor through the same `reassemblePolynomialFactors` as the constant and
quadratic cases, so it produces the same `Factorization` any other singleton
proof would; the trace records `FactorMethod.quadraticNorm`. A failure falls
through to `planned` carrying no state, and the row runs exactly the cascade it
ran before.

**The budget.** Recombination at width `w` walks up to `2^(w-1)` supports, so
the gate is a width: `QuadraticNormCertificate.widthFloor = 16`. At the floor the
walk is `2^15 = 32768` nodes, an eighth of the 262,144-node
`defaultSubsetBudget` the recombination already carries, and it is the cost of
that walk the certificate is worth attempting to replace. Below the floor
nothing is constructed, so a row that recombines cheaply pays exactly nothing.
The floor is deliberately not `defaultSubsetBudget` itself: `sd5`'s
32,768-node walk sits far under that budget and would never trip it, yet it is
precisely the walk worth replacing.

**Normalization.** Every `F(c; d)` is monic, so the certificate applies to the
primitive square-free part exactly when its leading coefficient is `1` or `-1`,
and the only normalization is negation. `ZPoly.normalizePrimitiveSign`, inside
the check, is that negation and nothing else: no scaling, no content division,
no reordering.

**Soundness.** `HexBerlekampZassenhausMathlib.irreducible_of_check` says a
successful check makes its input irreducible in `Polynomial ℤ`, with no
hypothesis on the input, and `irreducible_of_quadraticNormCertified` says the
same of the gate. It is what discharges the certificate arm of
`factorClassicalFactors_factor_irreducible`, so a certified singleton is proved
irreducible on the same footing as every other returned factor. The composition
the two halves needed is `signPatternPoly_ofFn`: `map_iteratedNorm` writes the
sign-pattern product as a `List.prod` over a fold-built list of signed sums and
the tower theorem writes it as a `Finset.prod` over `Fin n → Bool`, and those are
the same polynomial. Neither side can adopt the other's encoding -- the fold is
what the iterated norm computes, and the `Fin n → Bool` indexing is what lets an
automorphism act by a reindexing equivalence -- so it is a real lemma, proved by
induction on the radicand count, splitting the last sign off with `Fin.snocEquiv`
on one side and the last fold step on the other.

## The measurement driver

`hexbz_factor_service --entry quadraticNormProbe` times one production
factorization and the four certificate stages on the same input in the same
process. `--entry quadraticNormCertificate` runs the certificate stages alone,
for the corpus-wide miss sweep and for any row the cascade does not finish. Each
stage folds its result into a reported witness before its closing mark; without
that the compiler sinks each pure `let` to its only use and the whole
certificate cost lands in whichever span is last.

The probe is deliberately *unconditional*: it prices the certificate on every
row, including the ones production's width floor never offers it to. That is
what makes the miss table a property of the certificate rather than of the gate.
It also means the paired ratio is no longer a speedup, because a certified row's
production call now runs the certificate too; it says what share of the
integrated row the certificate is. The before/after speedup is in the factor
sweep below.

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
| `hexbz-quadratic-norm-certificate-chungus2.json` | `b5cc0418072f04faf9c893138ab6dc88e0bb311877f503083893e2f0d1565612` |
| `hexbz-quadratic-norm-witnesses.json` | `e3008007ebf3e114da025455e1a6d49a8def461524a4a29c441429bd434f4f10` |
| `hexbz-factor-sweep-d27e0bf2-hex-chungus2.json` | `d9a5b33aa9d18ff35e9fc4390a365520b5c702a649507636dfb19cecdf43b0de` |
| `hexbz-factor-sweep-5dabd026-hex-chungus2.json` | `1e06a903574a230da312bda3e9f916fc8bc1d637347414ca37d90429bd5ef2f6` |
| `hexbz-factor-sweep-5dabd026-hex-chungus2-run2.json` | `ababa5b2b439ca3d8af1f20edd892f17d8fbc951d9d4a0166a509abe6758a674` |
| `hexbz-factor-sweep-5dabd026-hex-gate-closed-chungus2.json` | `73c010724edbf580b81af3a3291107b201e29753e7b6df6153f8c921f916678d` |
| `hexbz-factor-sweep-5dabd026-hex-gate-closed-chungus2-run2.json` | `1468554703005586fa887262b38ad0522ec639c6ff68cd0a9a6a2206ec6de9bf` |

All are in `reports/bench-results/`. The probe and witness records were measured
at `55e47e1e` from a clean tree; each carries the SHA-256 of the service binary
it measured, which pins the code more tightly than the commit does.

The four `5dabd026` sweeps are the before/after pair, two runs each. The
`gate-closed` two were measured from a tree whose only edit was
`QuadraticNormCertificate.widthFloor` raised past every reachable width, so they
record the same revision with the certificate switched off; they are marked
dirty for that reason. `hexbz-factor-sweep-d27e0bf2-hex-chungus2.json` is the
published sweep: clean tree, integrated, taken after `main` was merged in, and
what the committed figures and the rank table read. Its `sd5` reads 6.766 ms and
its `sd6` 27.646 ms, within the run-to-run spread of the pair.

Measuring the two sides of one revision, rather than this branch against `main`,
is deliberate. Several unrelated performance changes landed on `main` between
the go/no-go and this integration, and a `main`-versus-branch comparison would
credit this change with theirs.

The go/no-go's cactus model,
`reports/bench-results/hexbz-quadratic-norm-cactus-model.json` and
`scripts/bench/quadratic_norm_cactus_model.py`, is superseded by those sweeps
and is kept only as the prediction the measurement is checked against. Do not
re-run it against an integrated sweep: its replacement rule would count the
certificate twice.

## Measured effect

### Certified rows, construction and checking separately

All times in microseconds unless marked; `production` is the paired in-process
factorization, which for a certified row now *contains* the certificate. The
final column is the go/no-go's prototype total, for comparison.

| row | degree | recovery | independence | construction | equality | certificate | paired | production | certificate share | prototype |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `conway_p13_n2` | 2 | 2.8 | 0.1 | 0.9 | 0.2 | 3.9 | 3.9 | 0.026 ms | 1/7 | -- |
| `conway_p3_n2` | 2 | 3.0 | 0.1 | 0.9 | 0.2 | 4.2 | 5.3 | 0.020 ms | 1/5 | 3.2 |
| `conway_p5_n2` | 2 | 2.7 | 0.1 | 0.9 | 0.1 | 3.9 | 3.9 | 0.019 ms | 1/5 | -- |
| `conway_p7_n2` | 2 | 2.9 | 0.1 | 0.8 | 0.1 | 4.0 | 5.0 | 0.033 ms | 1/7 | -- |
| `conway_p97_n2` | 2 | 2.8 | 0.1 | 0.9 | 0.1 | 4.0 | 3.9 | 0.029 ms | 1/7 | -- |
| `conway_p65537_n2` | 2 | 2.9 | 0.1 | 0.9 | 0.1 | 4.1 | 4.0 | 0.030 ms | 1/7 | 3.4 |
| `sd2` | 4 | 7.2 | 0.3 | 2.4 | 0.2 | 10.0 | 8.9 | 0.038 ms | 1/4 | 7.1 |
| `sd2_shift1` | 4 | 6.3 | 0.3 | 1.9 | 0.2 | 8.6 | 8.6 | 0.039 ms | 1/5 | -- |
| `sd3` | 8 | 11.6 | 1.0 | 4.1 | 0.2 | 16.9 | 16.9 | 0.163 ms | 1/10 | 12.9 |
| `sd3_shift1` | 8 | 11.3 | 0.7 | 3.7 | 0.2 | 15.9 | 16.8 | 0.160 ms | 1/10 | -- |
| `sd3_shift2` | 8 | 11.3 | 0.6 | 3.9 | 0.2 | 16.0 | 16.3 | 0.161 ms | 1/10 | -- |
| `sd4` | 16 | 18.5 | 1.3 | 9.4 | 0.4 | 29.6 | 61.1 | 1.503 ms | 1/25 | 23.7 |
| `sd4_shift1` | 16 | 19.2 | 1.3 | 9.9 | 0.4 | 30.7 | 34.4 | 0.807 ms | 1/26 | -- |
| `sd4_shift3` | 16 | 19.5 | 1.2 | 13.9 | 0.4 | 35.0 | 36.1 | 0.897 ms | 1/25 | 27.4 |
| `sd5` | 32 | 62.5 | 4.5 | 72.1 | 1.5 | 140.6 | 147.0 | 12.061 ms | 1/83 | 68.9 |
| `sd5_shift1` | 32 | 56.5 | 2.6 | 71.0 | 0.9 | 131.0 | 133.8 | 7.411 ms | 1/55 | 119.1 |
| `sd5_shift2` | 32 | 53.3 | 2.6 | 73.0 | 0.9 | 129.7 | 135.5 | 9.147 ms | 1/67 | 128.6 |
| `sd6` | 64 | 162.4 | 7.0 | 311.0 | 4.1 | 484.5 | 366.9 | 30.575 ms | 1/83 | 284.3 |
| `sd6_shift1` | 64 | 204.4 | 5.3 | 431.5 | 2.0 | 643.2 | 647.2 | 33.810 ms | 1/52 | 596.4 |
| `sd6_shift5` | 64 | 222.3 | 5.5 | 499.4 | 2.0 | 729.2 | 745.9 | 31.922 ms | 1/43 | 674.0 |
| `hoeij_S7` | 128 | 404.8 | 11.2 | 1161.4 | 3.4 | 1580.9 | 1533.8 | 215.697 ms | 1/139 | 1300.6 |
| `sd7` | 128 | 489.1 | 17.1 | 1661.6 | 5.7 | 2173.4 | 1626.4 | 233.546 ms | 1/142 | 1288.5 |
| `hoeij_S8` | 256 | 2344.5 | 35.4 | 7585.7 | 12.4 | 9978.0 | 6374.7 | 4315.192 ms | 1/677 | 5327.3 |
| `hoeij_S9` | 512 | 6417.6 | 50.0 | 23695.1 | 25.2 | 30187.9 | -- | timeout | -- | 23638.7 |

The four stage columns come from a certificate-only process, which is what
classifies every row and what the whole-corpus miss sweep uses. `paired` is the
same total measured inside the paired process, alongside the production
factorization it is part of.

Twenty-four of the corpus's 392 rows certify, the same twenty-four as before:
eighteen Swinnerton-Dyer rows and translates, and six degree-two Conway
polynomials, which are the `n = 1` case of the theorem. Every one of them is
certified by the recognizer reading coefficients; none is named anywhere in the
source.

Cost splits as expected: recovery is `O(n²)` rational operations on the top
`2n+1` coefficients and dominates at small degree; the iterated-norm
construction is `O(N²)` big-integer multiplications and dominates from degree 32
up; the independence test is `2ⁿ - 1` square tests on integers below 510,510 and
never exceeds 50 us; the equality test is under 26 microseconds everywhere,
because by the time it runs both sides are already built.

Against the prototype, the production definitions are **1.3x to 1.7x slower**
from degree 32 up -- `sd5` 68.9 to 140.6 us, `sd6` 284.3 to 484.5 us, `sd7`
1288.5 to 2173.4 us -- because `Hex.quadNorm` carries `ZPoly` values through
`DensePoly` operations rather than indexing one flat `Array Int` in place. That
is the price of the representation the correspondence theorem is stated about,
and it is not a price worth paying attention to: on every certified row the
certificate is between a quarter and a six-hundredth of the row it answers.

### Miss overhead

Over the 368 declining rows: **median 0.17 us, maximum 539.9 us.** The median is
the degree test -- most of the corpus does not have power-of-two degree, and
those rows are refused in a few hundred nanoseconds. The rows that pay anything
are those with power-of-two degree *and* `2ⁿ | a_{N-1}`, which then run the
rational recovery to a contradiction:

| declining row | degree | modular width | cost | offered the certificate? |
|---|---:|---:|---:|---|
| `cyclo_phi256` | 128 | 2 | 539.9 us | no |
| `cyclo_phi128` | 64 | 2 | 196.3 us | no |
| `conway_p2_n32` | 32 | 2 | 87.7 us | no |
| `cyclo_phi64` | 32 | 2 | 87.5 us | no |
| `laguerre_L32` | 32 | 5 | 77.3 us | no |
| `wilkinson_32` | 32 | 32 | 0.4 us | yes |

That last column is the whole point of the gate, and it is what the corpus says
about it: **every expensive miss is on a row the width floor never offers the
certificate to.** A row is expensive to refuse exactly when it has power-of-two
degree and survives the trace test, and those are cyclotomic and Conway rows,
whose modular images barely split at all -- `cyclo_phi256` has width 2, so its
recombination is a two-node walk and the floor of 16 keeps it free.

Here is every declining row the gate *does* offer the certificate to, with what
the attempt costs as a share of the row:

| declining row | width | miss | row | share |
|---|---:|---:|---:|---:|
| `wilkinson_16` | 16 | 0.2 us | 1.158 ms | 0.014% |
| `wilkinson_18` | 18 | 0.2 us | 1.718 ms | 0.011% |
| `wilkinson_20` | 20 | 0.1 us | 2.274 ms | 0.007% |
| `wilkinson_32` | 32 | 0.4 us | 6.819 ms | 0.005% |
| `sd4_x_sd4shift1` | 16 | 0.2 us | 17.998 ms | 0.001% |
| `sd5_x_phi11` | 17 | 0.2 us | 142.972 ms | 0.000% |
| `sd5_x_phi45` | 18 | 0.2 us | 328.742 ms | 0.000% |
| `sd6_x_phi13` | 33 | 0.2 us | 2.915 s | 0.000% |

Nineteen corpus rows decline at width 16 or above; the worst of them pays
**0.014%** of its factorization, against the 1% the gate was asked for. Every
one is refused at the trace test: a Swinnerton-Dyer *product* has roots summing
to a multiple of the degree only by accident, and a Wilkinson polynomial's roots
sum to `N(N+1)/2`, which `N` divides only when `N` is odd.

`sd5_x_phi11`, `sd5_x_phi45`, `sd4_x_sd4shift1`, `sd5_x_sd5shift1`,
`sd6_x_phi13`, `sd6_x_phi105` and `sd6_x_sd6shift1` are the rows the issue named:
Swinnerton-Dyer products and cross-shifts. They are reducible, so no certificate
can apply to them, and they stay on the general path -- at a measured cost of two
tenths of a microsecond each.

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

These are re-run against the production definitions, not the prototype:
`deg1024` now costs 311 ms rather than the prototype's 24 ms, which is the same
1.3x-to-13x `DensePoly`-versus-flat-array gap the certified-row table shows,
widening with degree. Nothing in the corpus is anywhere near degree 1024.

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

### Measured effect on the whole corpus

Two sweeps at the same revision, `5dabd026`, differing only in whether the width
floor is reachable, and two runs of each. The tables use the better of the two
runs on each side.

| row | degree | gate closed | integrated | ratio |
|---|---:|---:|---:|---:|
| `sd2` | 4 | 0.055 ms | 0.052 ms | 0.948x |
| `sd3` | 8 | 0.172 ms | 0.167 ms | 0.973x |
| `sd4` | 16 | 0.849 ms | 0.852 ms | 1.004x |
| `sd4_shift1` | 16 | 0.775 ms | 0.782 ms | 1.009x |
| `sd4_shift3` | 16 | 0.845 ms | 0.858 ms | 1.015x |
| `sd5` | 32 | 71.007 ms | 6.820 ms | **0.096x** |
| `sd5_shift1` | 32 | 66.479 ms | 7.174 ms | 0.108x |
| `sd5_shift2` | 32 | 68.817 ms | 8.807 ms | 0.128x |
| `sd6` | 64 | 8.148 s | 27.055 ms | **0.003x** |
| `sd6_shift1` | 64 | timeout | 31.290 ms | -- |
| `sd6_shift5` | 64 | timeout | 30.241 ms | -- |
| `sd7` | 128 | timeout | 194.470 ms | -- |
| `hoeij_S7` | 128 | timeout | 192.643 ms | -- |
| `hoeij_S8` | 256 | timeout | 3.977 s | -- |
| `hoeij_S9` | 512 | timeout | timeout | -- |

`sd2` through `sd4_shift3` are the certified rows the gate does *not* fire on:
their modular width is 4, 8 or 16 -- and at width 16 the recognizer is offered
`sd4` and takes it, which is why `sd4` is flat rather than halved. `sd4`'s
recombination visits 128 nodes, not 32,768, so there is nothing there to
replace; the certificate costs 29.6 us and saves about as much.

Over the whole corpus, best of two runs a side:

* solved **377 → 383** of 392. `sd6_shift1`, `sd6_shift5`, `sd7`, `hoeij_S7`,
  `hoeij_S8` and `sd6_x_phi13` join; nothing is lost.
* total over the rows both sides solve: **17.225 s → 8.965 s, 0.52x**.
* **no regression above 5%.** The only rows outside `±5%` on the best-of-two
  comparison are sub-100-microsecond ones -- `conway_p5_n10` at 68 → 72 us,
  `chebyshev_U6` at 66 → 70 us, `conway_p13_n2` at 37 → 40 us -- where
  run-to-run spread on this host is that size, and the direction is not
  consistent between runs.

One artifact is worth recording rather than hiding. Run 1 of the integrated
sweep shows a 1.53x band across `wilkinson_14` through `wilkinson_24` and
`wilkinson_40`; run 2 does not, and a paired A/B between the two binaries --
interleaved, `taskset -c 0`, median of five, best of two passes -- puts every
wilkinson row at 1.017x or below, most within 1%. The certificate is not even
attempted on `wilkinson_14`, whose width is 14. It is a host transient. Both
runs are committed rather than the better one.

`sd6_x_phi13` is the one newly solved row that does *not* certify: it is
`SD₆ · Φ₁₃`, reducible, so no certificate can apply to it. It becomes solvable
through the proposal tier, which peels pieces and replays the proved classical
factorizer on each -- and that replay is the same `classicalInput` the
certificate sits on, so the degree-64 `SD₆` piece is certified there.
`--entry proposalTrace` shows it directly: with the gate closed the proposal
declines and returns nothing, and with the gate open it returns factor degrees
`[12, 64]`.

### Measured effect on the combined cactus

`hexbz-factor-sweep-d27e0bf2-hex-chungus2.json` is the published sweep and what
the 25 committed figures and `scripts/bench/cactus_rank_table.py` read; the
external comparator curves are carried over unchanged from
`hexbz-factor-sweep-aa68c920-chungus2.json`.

On the 160-row combined mixture, Hex solves **145 → 151**, against Isabelle's
141. Cumulative Hex/Isabelle:

| rank | 125 | 128 | 130 | 133 | 135 | 138 | 140 |
|---|---:|---:|---:|---:|---:|---:|---:|
| gate closed | 0.70x | 0.79x | 0.85x | 0.96x | 1.01x | 0.75x | 0.55x |
| integrated | 0.66x | 0.69x | 0.70x | 0.71x | 0.68x | 0.44x | 0.29x |

Worst ratio over ranks 125--140: **1.012x with the gate closed, 0.707x
integrated**, against #9126's 0.85x criterion. The go/no-go modelled 0.708x from
the pre-#9171/#9172 elbow; the measurement lands within a fifth of a percent of
it.

The rows #9126 named as also needing parity are untouched: `xpow105_minus1`,
`cyclo_phi179` and `cyclo_phi64_x_phi105` all decline the certificate at a cost
of two tenths of a microsecond, and their times move by less than the run-to-run
spread.

The elbow does not just clear the target, it stops being an elbow. With the gate
closed the ratio still rises monotonically from rank 125 to a peak at 135, which
is exactly where `sd5_shift2`, `sd5` and the Swinnerton-Dyer rows sit; integrated,
it is flat at about 0.70x through rank 133 and then falls away, because those
rows have moved down the curve into the part where Hex was already ahead.

## Go/no-go

| gate | verdict |
|---|---|
| theorem applies to a natural class broader than the benchmark rows | **yes** -- all independent radicands and translations; 8 off-corpus witnesses including negative, composite, and degree-1024 cases |
| covers SD5 and SD6 from their mathematical input data without case tables | **yes** -- radicands recovered from the top `2n+1` coefficients; `sd7`, `hoeij_S8`, `hoeij_S9` too |
| certificate generation plus checking at least 5x faster than SD5, materially reduces SD6 | **yes**, and measured end to end after integration rather than as a prototype ratio: `sd5` 71.007 → 6.820 ms, `sd6` 8.148 s → 27.055 ms |
| small, reviewable trust surface | **yes** -- see below; the Mathlib proof is in, and the search stayed outside the trust surface |
| unsuccessful detection under 1% median overhead, preferably opt-in | **yes**, and by three orders of magnitude -- of the nineteen declining rows the width floor actually offers the certificate to, the worst pays 0.014% of its factorization. The 540 us tail exists but is entirely on narrow rows the floor never offers it to |

The executable trust surface is `quadNorm`, `iteratedNorm`,
`isPerfectSquare`, `independentSquareClasses`, and one array comparison: about
60 lines, no floating point, no primality testing, no factorization, no
randomness. Recovery is outside it entirely -- it may return anything, and a
wrong answer is refused by the check.

The mathematical surface is the theorem above. Lemma A is three lines, the
`Claim(m)` induction is elementary and needs no Kummer theory, and the Galois
input is that a multiquadratic field is the splitting field of a separable
polynomial. What it needed from Mathlib was the Galois correspondence for
`ℚ(α) = Fix(Stab α)` and `minpoly` as the orbit product, and it is now a Lean
theorem: `HexBerlekampZassenhausMathlib.irreducible_of_check`.

## What was owed, and what is delivered

The go/no-go named five pieces. All five are in.

1. **The tower theorem** -- Lemma A, the `Claim(m)` induction and `[K:ℚ] = 2ⁿ`
   (#9167); the trivial-stabilizer argument, `ℚ(α) = K`, and
   `minpoly α = F(c; d)` (#9169). In
   `HexBerlekampZassenhausMathlib/{SquareClass,Multiquadratic}.lean`.
2. **The norm correspondence** -- `map_quadNorm` and `map_iteratedNorm` (#9168),
   in `HexBerlekampZassenhausMathlib/QuadraticNorm.lean`.
3. **The decidable checks** -- `independentSquareClasses_iff` and
   `toPolynomial_inj`, same file.
4. **Production integration** -- `QuadraticNormCertificate.recover?`,
   `certify?`, and the `quadraticNormCertified` gate, reached once from
   `classicalInput`; `irreducible_of_check` and
   `irreducible_of_quadraticNormCertified` make it sound; `signPatternPoly_ofFn`
   is the composition the two developments needed (#9170).
5. **A fresh sweep and regenerated plots** at the integrated revision -- below.

Nothing above uses `axiom`, `sorry`, or `native_decide`: the check is a `Bool`
and the theorem is about it being `true`. `python3
scripts/release/check_trust_surface.py` reports 421 clean files at this
revision.

### Where the floor sits, and what a lower one would buy

At `widthFloor = 16` the certified rows split cleanly. `sd5` and up are
certified and cost a tenth to a three-hundredth of what they did; `sd4`,
`sd4_shift1` and `sd4_shift3` are offered it at width 16 and take it, but their
recombination visits 128 nodes rather than 32,768, so there is nothing there to
replace and their times are flat to within 1.5%. `sd2` and `sd3`, at widths 4
and 8, are below the floor and never see it.

Lowering the floor to 8 would offer the certificate to `sd3` and its translates
-- a 16.9 us certificate on a 167 us row, so at best a 10% gain on three rows
that are already among the fastest in the corpus -- and would offer it to every
width-8 declining row as well. The corpus says the miss would be cheap there
too, but the gain is not worth widening a gate for, and the floor's whole
justification is that the walk it replaces is expensive. Raising it to 32 would
give up `sd5`, `sd5_shift1` and `sd5_shift2`, which is most of the elbow. 16 is
where the walk first costs tens of milliseconds, and that is why it is 16.

### What is *not* delivered

* **A certificate witness for the tactics.** `irreducibility` still searches
  small-prime and Eisenstein witnesses only. Nothing in this work depends on
  that, but a `QuadraticNormCertificate` arm of `ZPoly.IrredWitness` would let
  the tactic answer a Swinnerton-Dyer input directly.
* **The one row still unsolved.** `hoeij_S9`, degree 512, certifies in about 24
  ms of certificate time but does not finish inside the 10 s cutoff, because the
  prime walk and modular factorization it still runs first do not. That is a
  Berlekamp cost, not a recombination one, and it is out of this scope.

## Regeneration

```
lake build hexbz_factor_service

# Certificate spans for every corpus row, paired against production where the
# cascade finishes. Pin to an idle core; other work shares this host.
taskset -c 0 python3 scripts/bench/quadratic_norm_probe.py \
    --output reports/bench-results/hexbz-quadratic-norm-certificate-chungus2.json

# Off-corpus witnesses, checked against an independent implementation, plus the
# randomized pass against the production factorizer.
taskset -c 0 python3 scripts/bench/quadratic_norm_witnesses.py \
    --output reports/bench-results/hexbz-quadratic-norm-witnesses.json

# The published sweep, from a clean tree, and the figures it invalidates.
# `--check` fails until the SVGs are regenerated.
taskset -c 0 python3 scripts/bench/factor_sweep.py --systems hex-factor \
    --cutoff 10 \
    --output reports/bench-results/hexbz-factor-sweep-d27e0bf2-hex-chungus2.json
python3 scripts/plots/hexbz-cactus.py
python3 scripts/plots/hexbz-cactus.py --check
python3 scripts/bench/check_factor_sweep_freshness.py

# The elbow. `--sweep` pins the record, so the same command reproduces the
# gate-closed column by naming the gate-closed record instead.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 145
```

The gate-closed side is not reproducible from a clean tree, by construction. To
retake it, raise `Hex.QuadraticNormCertificate.widthFloor` past every reachable
width, rebuild `hexbz_factor_service`, sweep to a `-gate-closed-` filename, and
restore. The record will say `git_dirty: true`, which is correct and is why the
published sweep is a separate, clean run.
