# Decision procedures for real and complex algebra: alignment with Hex

This report aligns the "Survey of Decision Procedures and Verification"
(Gemini transcript, PDF in the repository root) with what Hex has
implemented, what has a SPEC, and what `SPEC/future-work.md` already
sketches. It corrects the survey where it is wrong, and for the priority
items (CAD, BKR, Cohen–Hörmander, Weispfenning, NLSAT) it says concretely
which Hex components each one consumes, what is missing, and what the
kernel-checkable certificate would be.

## Scope decisions

| Survey item | Decision | Note |
| --- | --- | --- |
| Congruence closure | out | `grind`/`cc` in Lean core. |
| Dutertre–de Moura simplex | out of Hex | Compare against [leanprover/lp](https://github.com/leanprover/lp); see the section on it below. Farkas certificates are its business. |
| Fourier–Motzkin | out | `linarith` territory. |
| Cooper / Omega | out | `omega` in Lean core. |
| Sum of squares | out of Hex | [leanprover/sos](https://github.com/leanprover/sos); hex-mv-poly's SPEC already names `sos` as its first consumer. |
| Delta-decidability / ICP | skipped | hex-interval is the closest thing and its SPEC disclaims completeness by design. |
| Wu's method | mention only | Pseudo-division (hex-resultant, hex-mv-gcd) is the primitive; the certificate is one pseudo-remainder identity plus the nondegeneracy conditions. Not a Hex goal. |
| Gröbner bases | conditional | Only at industrial (F4-class) performance; see below. |
| CAD, BKR, Cohen–Hörmander, Weispfenning, NLSAT | priority | Detailed sections below. |

## What Hex already has that these procedures consume

Phase numbers are `done_through` in `libraries.yml` (7 = fully done).

- **hex-real-roots (7), hex-real-roots-mathlib (7).** Real root isolation
  for `ℤ[x]`: Sturm chains seeded by `(p, p')`, Descartes/Möbius bisection
  with Sturm witnesses, refinement, separation bounds. The companion proves
  Sturm's theorem in counting form (`Sturm.IsSturmChain.sturm_Ioc`). The
  `IsSturmChain` structure hard-codes the derivative flank (the product of
  the first two entries goes from negative to positive at each root), so it
  gives root *counts* only. There is no Sturm–Tarski theorem (signed count
  of `q` over the roots of `p` from the chain of `(p, p'q)`), which is the
  Tarski query that BKR and every sign-determination method rest on.
- **hex-rcf (7).** The `rcf` tactic: univariate sentences with one quantifier
  over `ℝ` or a dyadic `Ioc`, decided by squarefree carrier, root isolation,
  cell decomposition, sign matrix, Boolean fold, quantifier fold, all replayed
  in the kernel from a multiplication-only certificate. Its own SPEC says the
  multivariate case "needs cylindrical algebraic decomposition and is out of
  scope". Measured fresh-module tactic cost (from the SPEC's Phase-4 table):
  quadratic 0.26 s, a three-atom degree-10 goal (degree-30 carrier) 4.4 s,
  sparse degree-50 4.3 s, dominated by kernel replay. This is the baseline any
  multivariate design has to reckon with: kernel replay of *univariate*
  certificates is already seconds, not milliseconds.
- **hex-real-algebraic (1), hex-real-algebraic-mathlib.** Exact ordered real
  algebraic numbers as the real subtype of canonical `AlgebraicNumber`, with
  comparison, field operations, `sqrt`, `floor`/`ceil`, dyadic approximation,
  and, crucially, `RealAlgebraicPoly.roots`: the sorted real roots, with
  multiplicities, of a polynomial whose coefficients are real algebraic
  numbers. That is exactly the CAD lifting primitive. The companion proves
  `IsRealClosed` and the embedding into the algebraic reals. The SPEC
  explicitly defers "lazy `AlgebraicRoot` comparison, Tarski queries, and
  quantifier elimination". Exact comparison is still open as
  [#10142](https://github.com/kim-em/hex-dev/issues/10142) "spec: exact
  comparison of real algebraic numbers". Canonical arithmetic (eliminant,
  factorization, exactification at every operation) is known to be expensive;
  the SPEC's complexity section claims no constant-time comparison bound.
- **hex-number-field (7), hex-number-field-tower (7).** Canonical algebraic
  numbers, factorization-lazy `AlgebraicRoot`, roots of polynomials with
  algebraic coefficients, towers with Trager factorization and primitive-element
  flattening. All with a fixed embedding into `ℂ`, which is what
  [#10143](https://github.com/kim-em/hex-dev/issues/10143) notes does not
  survive infinitesimals.
- **hex-resultant (7), hex-resultant-mathlib.** Subresultant pseudo-remainder
  sequences over any exact-division domain, with `R = ZPoly` (bivariate)
  exercised and `R = NumberTower.Elem` consumed by the tower library.
  hex-mv-gcd supplies `ExactDivLaws (MvPoly n R cmp)` and already runs
  subresultant sequences over `MvPoly` coefficients (`HexMvGcd/Prs.lean`),
  so the projection-phase arithmetic of CAD (resultants, discriminants,
  principal subresultant coefficients of `p, q ∈ ℤ[y][x]`) is available
  today. The companion has agreement with `Polynomial.resultant`,
  specialization, and discriminant theorems. It does not have the theory
  relating the first nonvanishing principal subresultant coefficient to the
  degree of the gcd, which the CAD projection theorem needs.
- **hex-mv-poly (4), hex-mv-gcd (3), hex-mv-factor (3).** Multivariate
  polynomials with `toUnivariate` in a chosen main variable, content and
  primitive part, squarefree decomposition, exact division, and irreducible
  factorization over `ℤ` with a separate irreducibility certificate. The
  mv-factor SPEC already lists "the projection phase of cylindrical algebraic
  decomposition" as a consumer that needs *irreducible* factors. hex-mv-poly
  has a designed kernel form (`Kernel.PolyList`) for `decide +kernel` replay
  of polynomial identities.
- **hex-reflect (1).** Reifies batches of commutative-ring expressions into
  `MvPoly` with interpretation proofs, via `Lean.Meta.Sym.Arith`. This is the
  multivariate reifier every procedure below would use; the comparison and
  Boolean layer that `HexRCF/Reify.lean` does by hand for one variable would
  sit on top of it.
- **hex-interval (0), hex-interval-mathlib.** Exact dyadic intervals, a
  budgeted propagation engine, the `interval` tactic. Useful as an untrusted
  pruning heuristic for any of the searches below; not a decision procedure.
- **Pinned Mathlib.** `IsRealClosed` exists
  (`Mathlib/FieldTheory/IsRealClosed/Basic.lean`, one file: squares, odd
  roots, `nonneg_iff_isSquare`); no Sturm, no Thom's lemma, no continuity of
  roots in the coefficients, no CAD-related topology. Gröbner:
  `Mathlib/RingTheory/MvPolynomial/Groebner.lean` has only the multivariate
  division algorithm with respect to a `MonomialOrder`; no Buchberger
  criterion.
- **Planning already on file.**
  - `SPEC/future-work.md` § "Cylindrical algebraic decomposition": two or
    three variables, projection operator, multivariate subresultants, exact
    algebraic sample points, sign determination with algebraic coefficients;
    prototype projection and the certificate before fixing an API.
  - [#10143](https://github.com/kim-em/hex-dev/issues/10143) (open umbrella)
    "real closures of ordered fields with infinitesimals and transcendentals",
    after de Moura–Passmore (CADE 2013, Z3's `RCF` module). It proposes
    `hex-sturm` (Tarski queries over an ordered field), `hex-sign-det`
    (BKR sign determination and Thom encodings), `hex-ordered-fn`
    (infinitesimals and transcendentals), `hex-real-closure`. That issue is
    where the survey's "BKR" belongs; see below.
  - `SPEC/future-work.md` § "Gröbner bases": Buchberger with Gebauer–Möller,
    "F4 only if benchmarks justify it". This conflicts with the stated bar
    (industrial or nothing) and should be rewritten or parked.
  - No entry anywhere for virtual substitution, for a shared multivariate
    formula language, or for an NLSAT-style search.

## Cylindrical algebraic decomposition

### What the survey gets right and wrong

Right: full first-order QE, doubly exponential, no succinct certificate for a
general QE answer, and every existing formal development stops short.
Mahboubi implemented CAD inside Coq (MSCS 2007) but the correctness proof
was never completed; the Cohen–Mahboubi QE (LMCS 2012) that *was* verified is
a projection-free, sign-determination-based Tarski-style algorithm, not CAD.

Wrong or misleading: "the most viable path is fully formally verifying the
algorithm itself". For Hex's architecture that is the wrong dichotomy. CAD has
one deep theorem (delineability from sign-invariance of the projection set,
proved once) and a large amount of exact arithmetic whose *results* are
certifiable per instance. The kernel never has to see the projection operator
run; it has to see enough identities to apply the theorem.

### Components and their Hex status

Take a sentence over `ℤ[x₁,…,xₙ]`, atoms `p ⊳ 0`.

1. **Projection** (`ℤ[x₁,…,xₖ][xₖ₊₁] → ℤ[x₁,…,xₖ]`): leading coefficients,
   discriminants (or principal subresultant coefficients of `(p, p')`), and
   resultants (psc's of `(p, q)`) of the level-`k+1` polynomials, after
   squarefree/irreducible basis reduction. Arithmetic: all present
   (`toUnivariate`, subresultant chain over `MvPoly`, hex-mv-gcd,
   hex-mv-factor). Missing: the operator itself (small) and the choice of
   operator:
   - *Collins*: all psc's of `(p, p')` and `(p, q)`, all reducta. Largest
     set, most elementary proof.
   - *McCallum*: discriminants, resultants, coefficients; needs
     well-orientedness (fails on nullification) and the proof goes through
     order-invariance and Zariski's theorem on analytic delineability.
   - *Lazard*: like McCallum but total; validity proof only in 2019
     (McCallum–Parusiński–Paunescu, JSC) via Puiseux series.
   - *Brown*: McCallum minus most coefficients; same proof basis.
   For a verified pipeline, Collins is the safe default; McCallum/Brown as
   optimizations require certifying well-orientedness per input.
2. **Base phase** (univariate over `ℚ`): `ZPoly.realAlgebraicRoots`,
   between-root dyadic samples. Present (hex-real-roots, hex-real-algebraic).
3. **Lifting**: over each sample `(α₁,…,αₖ)`, substitute into every level
   `k+1` polynomial to get a `RealAlgebraicPoly`, take `RealAlgebraicPoly.roots`,
   choose samples between roots. Present in principle. This is the
   performance cliff: the sample coordinates are canonical
   `AlgebraicNumber`s, so every substitution re-canonicalizes (eliminant,
   factorization, exactification). Modern CAD implementations (QEPCAD B,
   Z3's `algebraic_numbers`, Maple's `RegularChains`) never canonicalize;
   they keep `(defining polynomial, isolating interval)` pairs with lazy
   refinement, or work in `ℚ(α)` as a tower. Hex has both alternatives
   half-built: lazy `AlgebraicRoot` (comparison still open, #10142) and
   `NumberTower` (whose sign needs its complex embedding). Expect the first
   prototype to be correct and slow; whether lifting should switch to a
   tower/Thom-encoding representation is the main design question, and it is
   the same question #10143 raises for infinitesimals.
4. **Sign evaluation at samples**: exact `RealAlgebraicNumber` arithmetic.
   Present.
5. **Truth values and quantifier folds**: the cell semantics, sign rows,
   Boolean fold, and quantifier fold of hex-rcf (steps 6, 8–10 of its
   algorithm) generalize by induction on levels; cylindricity is what makes
   the fold sound across a quantifier block boundary.

### The certificate

What the kernel must be convinced of is: the finite set of sample points
meets every sign-invariant cell of the atom polynomials (completeness), and
the sign of each atom at each sample (correctness). Correctness is cheap
per sample once the sample is kernel-representable. Completeness is
delineability at every level, which the projection theorem gives *provided
the kernel knows* that specific polynomials are the required psc's,
resultants, and coefficients of the level above. Two ways to supply that:

- Replay the subresultant chains with hex-resultant's multiplication-only
  Brown recurrence witnesses, level by level (the same trick as rcf's Sturm
  replay). Then the theorem applies to literal polynomials the kernel has
  checked.
- Or state the projection theorem directly in terms of `resultant` and
  `discriminant` as Mathlib functions and let the kernel compute them by
  reduction. Far slower; ruled out at any interesting size.

Then per level and per sample, the kernel needs root isolation data for a
polynomial with algebraic coefficients. With canonical coordinates that is a
Sturm replay over `ℚ(α)`, i.e. polynomial arithmetic over a number field in
the kernel. This is the item with no Hex precedent and the one most likely to
make replay cost explode. Thom encodings (see BKR below) replace interval
data by derivative signs and would let the kernel work with sign conditions
only, at the price of more Tarski queries.

### The theorem

Delineability for Collins' operator needs, in Mathlib terms:

- continuity of the complex roots of a polynomial in its coefficients
  (multiset form, or the "roots stay in small discs" form): not in Mathlib;
- the subresultant theory: the number of distinct common roots, and the
  degree of the gcd, read off from the first nonvanishing psc; hex-resultant
  has the resultant-zero-iff-common-root and specialization results but not
  the psc/gcd-degree statement;
- connectedness arguments over cells, where cells are graphs and bands of
  continuous root functions over lower cells; the topology is elementary but
  the bookkeeping is heavy;
- for QE with alternations, the cylindricity argument.

This is the long pole, and it is independent of every implementation
choice. Basu–Pollack–Roy chapter 11 is the reference; Mahboubi's thesis is
the closest formal attempt and it stopped exactly here.

### Recommendation

Keep the future-work entry but sharpen it:

- Start with the *theorem*, not the code: a Mathlib-facing development of
  continuity of roots plus the psc/gcd-degree lemma, stated for Collins'
  operator. If that stalls, nothing else in CAD can be certified and the
  effort should go to virtual substitution instead.
- Prototype the compiled pipeline unverified in parallel (projection over
  `MvPoly`, lifting via `RealAlgebraicPoly.roots`) to measure the lifting
  cost on the standard small examples (Collins' circle/parabola pairs,
  Kahan's ellipse-in-circle, Davenport–Heintz for the blowup). The
  future-work entry already asks for a projection prototype; the lifting
  prototype is at least as informative.
- Decide the sample representation (canonical, lazy interval, tower, Thom)
  from those measurements together with #10142/#10143 rather than
  independently.
- Reserve full CAD for genuine QE and `#eval`-level exploration. For the
  tactic use case (universal goals, existential goals with no alternation)
  build the NLSAT/covering variant described below on the same theorem.

## Ben-Or–Kozen–Reif

### What the survey conflates

Three different things carry the name:

1. **Univariate sign determination.** Given `p` and `q₁,…,qₛ`, compute the
   realizable sign vectors `(sign q₁(α),…,sign qₛ(α))` over the roots `α`
   of `p`, with their counts, from Tarski queries
   `TaQ(q, p) = #{p=0, q>0} − #{p=0, q<0}` computed by Sturm–Tarski
   sequences of `(p, p'q)`. The naive version solves a `3ˢ × 3ˢ` linear
   system; BKR's contribution is a divide-and-conquer that keeps only the
   realizable conditions (Basu–Pollack–Roy Algorithm 10.11).
2. **The multivariate "parallel" QE algorithm** of the 1986 paper, which
   applies (1) with parametric coefficients recursively. It gave the first
   single-exponential space bound and was improved by Canny and Renegar. It
   is not used by any practical system; the practical single-exponential
   line is the critical-point method (Basu–Pollack–Roy chapters 13–14, RAGlib),
   which is a different algorithm and also unimplemented in any prover.
3. **Thom encodings** (Coste–Roy 1988), which identify a root of `p` by the
   signs of `p', p'', …` at it. These combine with (1) to compare roots and to
   represent algebraic numbers without intervals, and are what de Moura and
   Passmore use in Z3's `RCF` module. The survey attributes Thom's lemma to
   Cohen–Hörmander, which is wrong (see below).

### The survey's verification verdict is wrong

"Extremely difficult; no kernel-checkable certificates" is contradicted by
the record. Cordwell, Tan and Platzer verified univariate BKR in Isabelle
(ITP 2021) and Kosaian, Tan and Platzer extended it to a complete (and, by
their own account, impractical) multivariate QE procedure (CPP 2023). And the
certificate story is good, not bad:

- A Tarski query value is certified by a Sturm–Tarski chain replay: the same
  literal three-term recurrence hex-rcf already checks by multiplication,
  with the seed `s₁ = p'·q` (up to a positive scale) instead of `s₁ = p'`,
  plus sign-variation counts at `±∞` or at dyadic endpoints.
- The sign-determination step is a linear identity `M · c = t` between the
  claimed count vector `c`, the Tarski query vector `t`, and a matrix `M`
  that is a tensor power of one fixed `3×3` matrix (or a certified
  invertible submatrix of it, with its inverse supplied). The kernel checks
  it by integer multiplication.
- Thom-encoding comparison of two roots is a finite case analysis on sign
  vectors, kernel-decidable once the encodings are certified.

So univariate BKR is *more* certificate-friendly than isolation-based
methods, because no dyadic approximation or separation bound is involved.

### Hex status and what is missing

- Sturm–Tarski theorem: generalize `IsSturmChain` (or add a sibling) so the
  root flank of `(p, p'q)` counts `+1` where `q > 0` and `−1` where `q < 0`;
  the proof is the existing local-crossing induction with a signed increment.
- Executable Tarski queries: hex-rcf's `SturmBuilder` instruments the
  pseudo-remainder loop for an arbitrary chain; only its check that the second
  entry is the derivative needs to accept `derivative p * q`.
- Sign determination with the BKR divide-and-conquer and the matrix
  certificate; hex-row-reduce/hex-modular-matrix supply the linear algebra.
- Thom encodings, Thom's lemma (Rolle-based induction; Mathlib has Rolle),
  and encoded-root ordering (Basu–Pollack–Roy Proposition 2.28).
- The ordered-field generalization (`DensePoly K` for an ordered `K`), which
  is #10143's `hex-sturm`.

All of this is already itemized in #10143 as `hex-sturm` and `hex-sign-det`.

### Where BKR actually pays off

Not as a decision procedure for sentences over `ℚ`: there, `rcf`'s
isolate-and-evaluate route is faster and already certified. It pays off
where numeric isolation is unavailable or awkward:

- ordered fields with no Archimedean bound (`ℚ(ε)`, #10143);
- parametric coefficients (the Tarski/Cohen–Hörmander recursion and
  Kosaian–Tan–Platzer's complete QE);
- CAD lifting with Thom-encoded roots, avoiding interval refinement and
  separation bounds at every level;
- sign of a tower element, replacing the complex-embedding numerics of
  hex-number-field-tower.

Recommendation: pursue BKR as the sign-determination library of the #10143
family, not as "BKR the QE algorithm". Item 2 above should be mentioned only
as history.

## Cohen–Hörmander: from `rcf` to the full procedure

### Correcting the survey

Hörmander's algorithm (Bochnak–Coste–Roy §1.4; Harrison, *Handbook of
Practical Logic and Automated Reasoning* §5.9; McLaughlin–Harrison CADE
2005) does not use Thom's lemma and does not isolate roots. Its object is
the **sign matrix** of a finite set of univariate polynomials: the ordered
list of all their real roots, interleaved with the open intervals between,
and the sign of each polynomial on each. The recursion: to get the sign
matrix of `{p, q₁,…,qₖ}` with `deg p` maximal, compute the sign matrix of
`{p', q₁,…,qₖ, r₀, r₁,…,rₖ}` where `r₀ = rem(p, p')` and `rᵢ = rem(p, qᵢ)`
(a smaller problem by degree), then read off the signs of `p` at the roots
of the others (from the remainders), and the roots of `p` in each interval
(at most one, since `p'` has constant sign there; presence decided by the
endpoint signs). Roots are positional, never numeric. With parametric
coefficients the algorithm case-splits on the signs of coefficient
polynomials of the outer variables (because degrees, leading signs and the
scaling in pseudo-division all depend on them), producing a quantifier-free
formula as a disjunction over the leaves. Its complexity is a tower of
exponentials in the number of variables; the proof-producing HOL Light
version handles two- and three-variable low-degree examples, and the output
formulas are unsimplified and large. It is the textbook "simple" QE, not a
practical one.

### How `rcf` relates

`rcf` is Tarski's one-variable decision by root isolation and dyadic
samples, with a kernel certificate. Its univariate *method* is not
Hörmander's. What transfers to a Cohen–Hörmander library is the outer
shape and its proofs:

- `Formula`/`Sentence` semantics and the reifier pattern (`Syntax.lean`,
  `Language.lean`, `Reify.lean`);
- the size-indexed `Cell` type, `Cell.Sem`, the partition theorem, the
  sign-row cache and Boolean fold, and the quantifier-fold soundness
  (`Cells*.lean`, `SignMatrix*.lean`, `Soundness.lean`);
- the certificate discipline: compiled search, multiplication-only replay,
  `check_sound`, no `false` verdict ever proved.

What does not transfer: the carrier, isolation, separation, and
common-root packages, all of which exist to make numeric samples work.

### Work items for full Cohen–Hörmander

1. **Language.** Prenex formulas over `MvPoly n Int` atoms with a
   quantifier prefix and `toProp` over `ℝⁿ`. Reification through hex-reflect
   for the ring layer, plus the comparison/Boolean layer. This language
   should be shared with virtual substitution and CAD.
2. **Univariate-over-coefficient-ring layer.** `MvPoly (n+1)` as
   `DensePoly (MvPoly n)` via `toUnivariate` (exists). Pseudo-remainder over
   that ring (hex-resultant's pseudo-division and hex-mv-gcd's
   `ExactDivLaws` instance exist). Degree and leading coefficient *under a
   sign hypothesis*: the degree of `p(y, x)` in `x` depends on which
   coefficients vanish at `y`, so every use of `deg`/`lc` is a case split.
3. **Sign-matrix engine.** The inference "sign matrix of
   `{p', qᵢ, rᵢ}` ⟹ sign matrix of `{p, qᵢ}`". Certificate content: the
   division identities `c · p = quot · g + rem` with `c` a power of a
   coefficient whose sign is a recorded hypothesis; the sign matrices
   themselves are recomputed by the checker from the child matrix, or
   supplied and checked cell by cell (cheap either way).
4. **Semantics and soundness.** `Realizes S M : Prop`: there exist
   `t₁ < … < tₘ` that are exactly the real roots of the polynomials in `S`,
   with the listed signs at the `tⱼ` and on the open intervals, covering
   `ℝ`. Theorem: the inference of item 3 preserves `Realizes`. This is
   the mathematical heart and is elementary (IVT, Rolle-type monotonicity,
   evaluation at roots through the remainder identity); hex-real-roots-mathlib
   already has the sign-constancy lemmas. Size comparable to hex-rcf's
   `Cells`/`SignMatrix`/`Soundness` layer.
5. **Parametric layer.** Hypotheses are finite sign conditions on
   `MvPoly n` (outer variables). Items 3 and 4 relativize to
   `∀ y, H(y) → Realizes (S(y,·)) M`. A case tree splits on `<`, `=`, `>`
   of one coefficient polynomial per node, so exhaustiveness is trichotomy
   and needs no proof search. The result of eliminating `x`:
   `∃ x, φ(y,x) ↔ ⋁_leaves (H_leaf(y) ∧ [some column of M_leaf true])`.
6. **Recursion outward.** The quantifier-free output has atoms that are
   coefficients, remainder coefficients, and so on; feed it to item 2 for
   the next quantifier. The *outermost* variable can use `rcf`'s numeric
   route instead of the symbolic one; that is the one place where the
   existing pipeline plugs in directly.
7. **Pruning is not free.** Dropping a leaf whose hypothesis is
   unsatisfiable is a negative claim and needs its own proof, obtained only
   by running the procedure on the hypothesis set. Untrusted heuristics
   (hex-interval, rational sample evaluation) can *order* the work but
   cannot remove leaves from a universal goal's obligation. This is the
   structural reason CAD scales better: its samples make every cell
   manifestly nonempty.
8. **Testing.** Oracle: Harrison's OCaml `real.ml` from the Handbook (open
   source, exactly this algorithm) for verdicts and output formulas; QEPCAD B
   or Redlog for verdicts on larger inputs.

### Verdict

A full Cohen–Hörmander is a new library that reuses `rcf`'s formula, cell,
fold, and certificate layers and adds the parametric sign-matrix engine
with an elementary soundness theorem. It needs no delineability theorem and
no algebraic numbers, which makes it the cheapest route to a *complete*
multivariate procedure with a kernel certificate. Its scale is toy: two or
three variables, low degree, exponentially many leaves with no sound pruning.
If the goal is a complete QE in Lean at any cost, this is the shortest path;
if the goal is a usable multivariate tactic, virtual substitution first and
then the NLSAT/covering route on the CAD theorem dominate it. Scope any first
version to sentences (all variables quantified) with the outermost variable
delegated to `rcf`.

## Weispfenning: virtual substitution

### What it is

For a quantified variable of degree at most 2 in every atom, `∃x φ` is
equivalent to a finite disjunction `⋁_{t ∈ E} φ[x // t]` where `E` is the
elimination set: `−∞`, each real root of each atom's polynomial (as a
formal expression `(−b ± √(b²−4ac)) / 2a` with guards `a ≠ 0`,
`b² − 4ac ≥ 0`, plus the linear case), and each root plus an infinitesimal
`ε`. The substitution is *virtual*: `√·`, `1/a`, `ε`, `∞` never appear in the
result; a fixed rule set rewrites `p(x) ⊳ 0` under each test point into a
quantifier-free formula in the remaining variables (for `r + ε`, by the signs
of successive derivatives; for `−∞`, by leading-coefficient signs). Linear
and quadratic: Loos–Weispfenning 1993, Weispfenning 1997; cubic: Weispfenning
1994 and Košta's 2016 thesis (the accessible full treatment, with clustering).
Industrial implementations: Redlog inside REDUCE (open source since 2008),
SMT-RAT, and preprocessors in Z3 and Mathematica. Formal prior art:
Nipkow's verified linear QE (Isabelle, 2008/2010) and Cordwell–Tan–Platzer's
verified quadratic virtual substitution (Isabelle, FM 2021, AFP
`Virtual_Substitution`, with exported executable code).

### Why it fits Hex now

Everything is polynomial arithmetic over `MvPoly` plus formula
manipulation. No algebraic numbers, no root isolation, no resultants beyond
the discriminant. The correctness content is one theorem per test-point
kind (the elimination-set theorem), proved once over an ordered field, plus
the derivative rule for `ε`. It composes with `rcf`: eliminate inner
quantified variables that are at most quadratic, then hand a univariate
residue to `rcf`, or evaluate a closed formula over `ℚ` in the kernel.
Degrees grow under substitution, so the second elimination often exceeds the
degree bound; Redlog falls back to CAD at that point, and so would Hex.

### Certificate versus reflection

- *Reflection*: run a verified `vs : Formula → Formula` in the kernel on the
  reflected formula. hex-mv-poly's kernel form was designed for this. Cost
  is kernel polynomial arithmetic on a formula of size roughly
  `(2·atoms + 1)` per eliminated variable, multiplicatively. Fine for a
  handful of atoms and two or three variables; this is what the Isabelle
  work does.
- *Certificate*: the compiled side chooses the test points and the
  simplified result; the kernel checks each virtual substitution as a
  polynomial identity (`p[x // (a + b√d)/c]` clears to `A + B√d` over
  `cᵏ`, an identity between `MvPoly`s) and applies the once-proved rules.
  Simplification is the delicate part: for a universal goal every disjunct
  must be refuted, so a simplifier may only *weaken* a disjunct (drop
  conjuncts, constant-fold, take `linear_combination`-style consequences),
  each step a checkable implication. Full Dolzmann–Sturm simplification
  (which uses equivalences) is not available to the trusted side, but it can
  guide the untrusted search.

### Work items

1. Shared formula language and reifier (item 1 of Cohen–Hörmander).
2. Test-point computation from `toUnivariate` in the quantified variable,
   with degree case splits on the leading coefficients (symbolic
   coefficients again).
3. The substitution rules for `−∞`, roots, and `root + ε`, and their
   soundness over `ℝ` (or any real closed field); the derivative rule for
   `ε` is where most of the proof lives.
4. Executable elimination with an untrusted simplifier and a checkable
   weakening trace.
5. Composition with `rcf` for the outermost variable and with kernel
   evaluation over `ℚ` for closed residues.
6. Oracle: Redlog `rlqe` (scriptable REDUCE), and the exported Isabelle
   code for the quadratic case.
7. Later: cubic virtual substitution following Košta, whose rules are far
   more numerous.

Recommendation: this is the first multivariate real-arithmetic tactic to
build. It has no dependency on the CAD theorem, a small proof, direct prior
art with source, and covers the linear and quadratic goals that dominate
tactic use. Add a future-work entry; none exists.

## NLSAT, MCSAT, and cylindrical algebraic coverings

### What the survey gets right and what it misses

Right: NLSAT (Jovanović–de Moura 2012) is MCSAT with CAD-based explanations;
quantifier-free; the projection theory is CAD's. Missing: the structure of
its proofs, which is exactly what matters for certificates.

An NLSAT run assigns real algebraic values variable by variable. On a
conflict it calls `explain`, which builds a single CAD cell around the
current sample (projection of the conflicting polynomials *at that sample*,
not globally) and learns the clause "not in this cell, or not all these
literals". Later refinements shrink that cell (Brown–Košta single-cell
construction, JSC 2015; levelwise construction, Nalbach et al., JSC 2024).
cvc5 instead uses cylindrical algebraic coverings (Ábrahám, Davenport,
England, Kremer, JLAMP 2021): a recursive covering of the real line at each
level by intervals each carrying the polynomials that exclude it.

For an unsatisfiable input (the negation of a universal goal), the run is a
propositional resolution refutation over the input clauses and the learned
cell clauses. That *is* a certificate: the resolution part is checkable with
the LRAT machinery Lean already trusts for `bv_decide`; each cell clause is
an instance of the single-cell delineability theorem whose side conditions
are concrete signs and root orders at an algebraic sample. The covering
variant produces an even more direct object: a tree of intervals with
reasons, which is a proof by exhaustion of the line at each level.

So the correction to "it inherits the same lack of succinct certificates" is:
the certificate exists and is small in *structure*; its cost is concentrated
in the per-clause algebraic arithmetic the kernel must replay (roots of
polynomials with algebraic coefficients, signs at algebraic points), and in
the one deep theorem, which is the same delineability theorem CAD needs but
stated for one cell. For a satisfiable input the certificate is the model,
an algebraic tuple checked by evaluation.

### Relation to CAD for the tactic use case

Same theorem, same projection arithmetic, same lifting primitive, minus the
full decomposition and cylindricity, minus quantifier alternation, plus a
CDCL core (or an external SAT solver with LRAT output) and the
single-cell/covering construction. Only the cells the search visited are
certified, typically a tiny fraction of the full decomposition. The
scepticism in the prompt is right about the ceiling, not the shape: replay
of algebraic sample data is what bounds the reachable size, and `rcf`'s
seconds-per-goal for univariate replay says the ceiling is low. The choice
of sample representation (interval versus Thom encoding versus tower) is
therefore the design decision shared with CAD lifting and #10143.

### Recommendation

Do not build a full-CAD tactic for universal goals. Once the delineability
theorem exists, build the covering/NLSAT-style refutation on it and certify
cell clauses individually. Until then, virtual substitution plus `rcf` is
the deliverable.

## Gröbner bases

The bar stated for this project is: only if Hex can be competitive with
industrial engines, and only if accessible sources exist to follow. They do:

- **msolve** (Berthomieu, Eder, Safey El Din, ISSAC 2021): open-source C,
  F4 over prime fields with a tracer and multi-modular reconstruction over
  `ℚ`, signature-based variant included, well documented, actively
  maintained. The best single source to follow.
- **giac** (Parisse, arXiv 1309.4044): modular F4 competitive with Magma on
  standard benchmarks; open source.
- **Singular** `std`/`slimgb`/`sba`; **GBLA** (Boyer, Eder, Faugère,
  Lachartre, Martani, ISSAC 2016) for the specialized F4 linear algebra;
  Eder–Faugère's JSC 2017 survey for F5/GVW.

What it would take: the engine cannot be hex-mv-poly's `ExtTreeMap`
representation. F4-class performance needs packed-exponent sparse
polynomials over word-size `𝔽ₚ` (Monagan–Pearce style arithmetic),
Macaulay-matrix construction with specialized sparse/dense hybrid row
reduction over `𝔽ₚ`, then multi-modular lifting to `ℚ` with a tracer. That is
a new executable substrate; hex-mv-poly stays the certificate/kernel form.

Certificates are the easy part and mostly exist: ideal membership and the
Nullstellensatz are cofactor identities, which hex-kronecker and hex-reflect
already check in the kernel (and which `polyrith`/`linear_combination` cover
today with Sage as the oracle). Negative claims (non-membership, dimension,
elimination ideals) need the basis `G`, two-way cofactor identities between
`G` and the generators, a reduction-to-zero trace for every S-pair, and the
Buchberger criterion proved once; Mathlib has only the division algorithm.
Note also that Lean core's `grind` already contains a Gröbner-basis-based
commutative-ring solver for small goals, so a Hex engine is justified only
at msolve scale.

Recommendation: rewrite the future-work entry to state the bar and the
msolve-shaped design, or park it. "Buchberger first, F4 if benchmarks
justify" is the plan the bar rules out.

## leanprover/lp against the Dutertre–de Moura simplex

The survey's linear-real-arithmetic item is Dutertre and de Moura's simplex
for DPLL(T) (CAV 2006): a tableau of fixed linear equalities over slack
variables whose only mutable state is a pair of bounds per variable, so that
asserting or retracting an atom is cheap, with Bland's rule for termination,
`δ`-rationals for strict bounds, conflict explanations read off a failing
row, and cheap bound propagation. It is a satisfiability engine designed to
sit inside a SAT search, not an optimizer.

What `lp` is. Six Lake packages: `lp-core` (the `Problem`/`Certificate`
vocabulary), `lp-verify` (a pure-Lean Farkas/dual certificate checker with
soundness lemmas and a denominator budget), `lp-tactic` (`lp` and `maximize`
plus a backend registry), and three untrusted backends: SoPlex through FFI
(default), SoPlex through a JSON subprocess, and `lp-backend-pure`, a
two-phase primal tableau simplex on `Rat` with Dantzig pivoting and a Bland
fallback, documented as slow beyond toy sizes. The `lp` tactic handles a
`Π₂` fragment: `Rat`-affine atoms under `∧`, `∃`, and inner guarded `∀`,
over `Rat`, `Int`, `Nat`, `Dyadic`, and `Real` carriers; strict atoms are
tracked through a strict-aware Farkas certificate; the proof is an explicit
weighted-sum identity the kernel only typechecks; measured at about twice
`linarith`'s speed on dense rational goals, with `linarith` failing at 100
variables where `lp` finishes. Every backend is untrusted and every result
is checked, so on the survey's "verification and certificates" axis `lp`
already has the complete answer.

What `lp` lacks relative to Dutertre–de Moura is the solver architecture, not
the certificate:

- Incrementality. There is no assert/retract/backtrack interface; every call
  is a fresh solve of a full LP. Dutertre–de Moura's whole point is that the
  tableau is built once and only bounds move.
- Explanations. The Farkas multipliers identify the rows used, but nothing
  minimizes the infeasible subset or exposes it as an interface for a
  surrounding search.
- Theory propagation. No implied bounds are derived from rows.
- Disjunctions and disequalities. The fragment has no `∨`, `¬`, or `≠`, and
  no SAT integration in which the `≠` case split would live; out-of-fragment
  hypotheses are silently ignored.
- Strict models. Refutation with strict atoms works through the certificate,
  but models come from SoPlex vertices; there is no `δ`-rational model
  construction for strict systems.
- Integers. `lp` over `Int` proves only `ℚ`-valid implications and says so;
  branch-and-bound and cuts are left to `omega` and `cutsat`.

Lean core's `grind` does not fill the gap either: its `linarith` module is a
model-based search that assigns variables in order from best bounds and
backtracks on conflict, and `cutsat` handles integers; neither is a
bounds-tableau simplex. So the survey's item, read as "an in-process
incremental exact simplex usable as a theory solver", exists in neither
repository. Whether it belongs in `lp` as a fourth backend with an
incremental interface, or in `grind`, is a `leanprover` question. Nothing in
it touches Hex.

## Proposed repository changes

1. `SPEC/future-work.md` § "Cylindrical algebraic decomposition": replace
   with the component/theorem/certificate breakdown above; name Collins'
   operator as the default and the delineability theorem as the first
   milestone; add the covering/NLSAT refutation as the tactic-facing variant;
   cross-reference #10142 and #10143 for the sample representation.
2. `SPEC/future-work.md`: new entry "Virtual substitution" (linear and
   quadratic first, cubic later), with the composition with `rcf`.
3. `SPEC/future-work.md`: new entry "Real-arithmetic formula language", the
   shared prenex `MvPoly` language and hex-reflect-based reifier that
   virtual substitution, Cohen–Hörmander, and CAD all need.
4. `SPEC/future-work.md` § "Gröbner bases": re-scope per the bar or park.
5. `HexRCF/SPEC/hex-rcf.md` § "What `rcf` does not decide": replace "needs
   cylindrical algebraic decomposition" with a pointer to the three routes
   (virtual substitution, Cohen–Hörmander, CAD/covering).
6. `SPEC/prior-art.md`: add the real-algebra prior art (Isabelle: BKR,
   quadratic virtual substitution, complete QE; Coq: Cohen–Mahboubi QE,
   Mahboubi's unfinished CAD; HOL Light: McLaughlin–Harrison; Z3: nlsat and
   the `RCF` module).
7. #10143: no change needed; it already owns Tarski queries, BKR sign
   determination, and Thom encodings. Its CAD paragraph should gain the
   remark that CAD lifting may consume Thom-encoded samples.

## References

- Basu, Pollack, Roy. *Algorithms in Real Algebraic Geometry*, 2nd ed.
  Chapters 2, 10, 11.
- Bochnak, Coste, Roy. *Real Algebraic Geometry*, §1.4 (Hörmander).
- Ben-Or, Kozen, Reif. "The complexity of elementary algebra and geometry."
  JCSS 1986.
- Coste, Roy. "Thom's lemma, the coding of real algebraic numbers and the
  computation of the topology of semi-algebraic sets." JSC 1988.
- Collins. "Quantifier elimination for real closed fields by cylindrical
  algebraic decomposition." 1975. McCallum 1988, 1998; Brown 2001; Lazard
  1994; McCallum, Parusiński, Paunescu, "Validity proof of Lazard's method
  for CAD construction." JSC 2019.
- Weispfenning. "Quantifier elimination for real algebra: the cubic case."
  ISSAC 1994; "the quadratic case and beyond." AAECC 1997. Loos,
  Weispfenning 1993. Košta, PhD thesis, Saarland 2016. Dolzmann, Sturm,
  "Simplification of quantifier-free formulae over ordered fields." JSC 1997.
- Jovanović, de Moura. "Solving non-linear arithmetic." IJCAR 2012. de Moura,
  Passmore. "Computation in real closed infinitesimal and transcendental
  extensions of the rationals." CADE 2013. Brown, Košta, JSC 2015. Ábrahám,
  Davenport, England, Kremer, JLAMP 2021. Nalbach et al., JSC 2024.
- McLaughlin, Harrison. "A proof-producing decision procedure for real
  arithmetic." CADE 2005. Harrison, *Handbook of Practical Logic and
  Automated Reasoning*, §5.9.
- Cohen, Mahboubi. "Formal proofs in real algebraic geometry: from ordered
  fields to quantifier elimination." LMCS 2012. Mahboubi, "Implementing the
  cylindrical algebraic decomposition within the Coq system." MSCS 2007.
- Cordwell, Tan, Platzer. "A verified decision procedure for univariate real
  arithmetic with the BKR algorithm." ITP 2021; "Verified quadratic virtual
  substitution for real arithmetic." FM 2021. Kosaian, Tan, Platzer, "A
  first complete algorithm for real quantifier elimination in Isabelle/HOL."
  CPP 2023. Nipkow, "Linear quantifier elimination." JAR 2010. Li, Passmore,
  Paulson, "Deciding univariate polynomial problems using untrusted
  certificates in Isabelle/HOL." JAR 2019.
- Berthomieu, Eder, Safey El Din. "msolve: a library for solving polynomial
  systems." ISSAC 2021. Parisse, arXiv 1309.4044. Boyer, Eder, Faugère,
  Lachartre, Martani, "GBLA." ISSAC 2016. Eder, Faugère, "A survey on
  signature-based algorithms for computing Gröbner bases." JSC 2017.
