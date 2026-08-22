# HexPolyFpMathlib Phase 2 scaffolding review

## Accomplished

Independent Phase 2 review of HexPolyFpMathlib per `PLAN/Phase2.md`, by an
agent other than the author of the scaffolding. Read
`HexPolyFpMathlib/Basic.lean` (411 lines, the only module) and
`HexPolyFpMathlib.lean` in full against
`HexPolyFpMathlib/SPEC/hex-poly-fp-mathlib.md`, and read the consumer surface:
`HexBerlekampMathlib/Irreducibility.lean` (re-export block and first use
sites), `HexGF2Mathlib/Basic.lean` (`equivPolynomial`),
`HexGFqMathlib/Subfield.lean` and `HexGFqMathlib/Primitivity.lean`.

Committed `status/hex-poly-fp-mathlib.scaffolding-reviewed` and updated the
SPEC's Contents section.

### Phase 1 prohibitions: clean

- No `sorry`, no `axiom`, no `@[extern]`, no `ffi/` directory.
- Grep for `scaffold`, `for now`, `eventual`, `placeholder`, `Phase 1`,
  `bridge for` across `HexPolyFpMathlib/`: the only hits are
  `Mathlib.Algebra.Ring.MinimalAxioms` and the `CommRing.ofMinimalAxioms`
  application, both substring accidents.
- No placeholder or trivial-return body. The library has exactly two
  data-level definitions, `fpPolyToPolynomial` (a `Finset.sum` of monomials)
  and `polynomialToFpPoly` (`DensePoly.ofList` over `List.range (natDegree +
  1)`), plus `fpPolyEquiv` bundling them. Each computes what its name says.
- No wrong-complexity body: the whole library sits inside a `noncomputable
  section` and states correspondences. The one place where an executable
  complexity claim could leak, `commRing`'s `npow` defaulting to `npowRec`, is
  handled by `linearPow_eq_pow`, which keeps callers on hex-poly-fp's
  structural `linearPow` and only identifies it with the monoid power for
  `map_pow`.
- No native-numeric wrong-shape declaration: nothing here names `UInt64`,
  `Fin n` or `Float`.

### DAG and imports

`libraries.yml[HexPolyFpMathlib].deps = [HexPolyFp, HexPolyMathlib,
HexModArithMathlib]` matches `Basic.lean`'s imports exactly (plus
`Mathlib.Algebra.Ring.MinimalAxioms`). `python3 scripts/check_dag.py` exits 0.
The SPEC header names the same three plus Mathlib.

### SPEC-promised declarations: none missing

The Contents section promised `fpPolyToPolynomial`, `polynomialToFpPoly`,
`fpPolyEquiv`, and `toMathlibPolynomial` with coefficient, monicity and `simp`
lemmas. All present: `Basic.lean:43, 48, 164, 219`, `coeff_toMathlibPolynomial`
at `:234`, `toMathlibPolynomial_monic` at `:257`, `fpPolyEquiv_apply` /
`fpPolyEquiv_symm_apply` at `:223, :228`.

`SPEC/Libraries/README.md:88` still advertises degree transport, which the
library does not have. This is corrected by the open PR #9367 (`doc: correct
SPEC and record staleness ahead of the finite-field release`, not merged as of
this review), so it is recorded here rather than filed as an issue.

### SPEC Contents update made

Three implemented families were under-described and are now listed:

- the transport lemma family `toMathlibPolynomial_{derivative, mul, add, sub,
  C, monomial_one, X, dvd}` (`Basic.lean:289-355`);
- `commRing : CommRing (Hex.FpPoly p)` (`Basic.lean:385`), with the reason it
  is a prerequisite rather than a convenience;
- `linearPow_eq_pow` (`Basic.lean:403`) and `primeModulus_of_fact`
  (`Basic.lean:360`).

Also corrected a prose claim in the Ownership section: it said "Lemmas that do
need `p` prime, such as the coprimality transports, say so in their own
hypotheses", but no coprimality transport lives here. The lemmas it describes
(`isCoprime_toMathlibPolynomial_of_isUnitPolynomial_gcd`,
`toMathlibPolynomial_squareFree_coprime`) are in
`HexBerlekampMathlib/Irreducibility.lean`, correctly, since they name
`isUnitPolynomial`. The sentence now points at `primeModulus_of_fact`, which is
the library's only primality-dependent declaration.

This edit does not touch the comparator-justification lines that PR #9367
rewrites, so the two do not conflict.

### Consumer fit

`HexBerlekampMathlib/Irreducibility.lean:38-44` re-exports 19 names. Every one
resolves to a public declaration of this library, and the export list is
exactly the public non-`private` surface minus `commRing` and
`linearPow_eq_pow`. Those two are genuinely not needed under the
`HexBerlekampMathlib.` prefix (an instance resolves without `export`, and
`linearPow_eq_pow` postdates the re-export block's compatibility purpose), so
the omission is coherent rather than an oversight.

`HexGF2Mathlib/Basic.lean:828-853` composes `fpPolyEquiv`, and uses
`polynomialToFpPoly`, `fpPolyEquiv_apply` and `coeff_toMathlibPolynomial`. All
public API, no reaching around.

`HexGFqMathlib/Subfield.lean` is the one place where a consumer does reach
around, and it is symptomatic rather than sloppy. See gap 1.

`HexGFqMathlib/Subfield.lean:32` and `HexGFqMathlib/Primitivity.lean:31` both
say `open scoped HexPolyFpMathlib`. HexPolyFpMathlib declares nothing `scoped`
(no `scoped instance`, no `scoped notation`, no notation or macro at all), so
both lines are no-ops. The presumable intent was to bring `commRing` into
scope, which is unnecessary because it is a global instance. Folded into gap 3
as a cleanup.

## Gaps, with drafted follow-up issues

Not filed: this session was instructed to draft rather than file.

---

### Issue 1

**Title:** `feat(hex-poly-fp-mathlib): complete the transport surface to match the generic DensePoly correspondence`

**Body:**

This library exists because the generic `DensePoly R ≃+* Polynomial R` in
hex-poly-mathlib cannot be reused for `FpPoly p`: `Hex.FpPoly p` is an abbrev
for `Hex.DensePoly (Hex.ZMod64 p)` (`HexPolyFp/Field.lean:848`), and every
lemma in `HexPolyMathlib/PolynomialEquivalence.lean` carries `[Semiring R]
[DecidableEq R]`, which `Hex.ZMod64 p` deliberately does not have. The
consequence the SPEC does not acknowledge is that the FpPoly layer has to
re-establish that surface itself, and it currently re-establishes about a
third of it.

The generic layer proves, and this library does not:

- `coeff_ofPolynomial` — the inverse-direction coefficient lemma. There is no
  `coeff_polynomialToFpPoly : (polynomialToFpPoly P).coeff n = ZMod64.ofZMod
  (P.coeff n)` here at all, so every consumer working backwards across the
  equivalence has to route through `RingEquiv.symm_apply_eq` and the forward
  lemma by hand.
- `ofPolynomial_{zero, one, C, neg, sub, add, monomial}` — the whole inverse
  direction of the transport family.
- `toPolynomial_monomial` at a general coefficient. This library has only
  `toMathlibPolynomial_monomial_one` (`Basic.lean:331`), the coefficient-`1`
  special case, which is a corollary of the general lemma rather than the
  primitive.
- `toPolynomial_neg`. The library has `sub` but not `neg`, which is odd given
  that `commRing` goes out of its way to pin `neg` to the executable
  `DensePoly.neg`.
- `eval₂_toPolynomial` and `toPolynomial_compose`.
- `toPolynomial_dvd_iff`. This library has only the forward direction
  (`toMathlibPolynomial_dvd`, `Basic.lean:352`). The reverse direction is what
  lets a Mathlib divisibility fact be reflected back onto the executable
  representation, which is what a decision procedure needs.
- `natDegree_toPolynomial` and `leadingCoeff_toPolynomial` — see issue 2,
  filed separately because its evidence is different.

This is not hypothetical. `HexGFqMathlib/Subfield.lean:167-183` re-derives the
general inverse monomial transport inline:

```lean
have hsym : HexPolyFpMathlib.fpPolyEquiv.symm (Polynomial.monomial k c) =
    (Hex.DensePoly.monomial k (HexModArithMathlib.ZMod64.ofZMod c) :
      Hex.FpPoly p) := by
  rw [RingEquiv.symm_apply_eq]
  apply Polynomial.ext
  intro i
  rw [HexPolyFpMathlib.fpPolyEquiv_apply,
    HexPolyFpMathlib.coeff_toMathlibPolynomial,
    Hex.DensePoly.coeff_monomial, Polynomial.coeff_monomial]
  ...
```

Seventeen lines of representation-level coefficient reasoning inside a file
about Conway subfield embeddings. With a general
`toMathlibPolynomial_monomial` it is `rw [RingEquiv.symm_apply_eq,
toMathlibPolynomial_monomial]`. The enclosing theorem,
`ofPolyHom_compose_eq_eval₂` (`Subfield.lean:153`), is itself doing by hand,
via a bespoke `Polynomial.induction_on'`, work that
`HexPolyMathlib.toPolynomial_compose` and `eval₂_toPolynomial` do generically.

`HexGF2Mathlib.coeff_equivPolynomial` (`Basic.lean:850`) is the mild version
of the same thing: it exists because "unfolding through both legs leaves a
`toZMod` applied to an `if`", which is the sort of thing the missing forward
lemmas would absorb.

Suggested scope: add the inverse-direction coefficient lemma first, since the
rest of the `symm` family follows from it, then the general monomial, `neg`,
`dvd_iff`, `eval₂`, and `compose`. Whether to reach them by re-proving or by a
shared abstraction over the two correspondence layers is an implementation
choice; the constraint is that `ZMod64` must not acquire a Mathlib `Semiring`
instance, which is the deliberate design decision the SPEC records.

Found in the Phase 2 scaffolding review of HexPolyFpMathlib.

---

### Issue 2

**Title:** `feat(hex-poly-fp-mathlib): own the degree and leadingCoeff transport now proved in hex-berlekamp-mathlib`

**Body:**

`HexBerlekampMathlib/Irreducibility.lean:52-96` proves

```lean
theorem natDegree_toMathlibPolynomial_eq_basisSize [Nontrivial (ZMod p)]
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f) :
    (toMathlibPolynomial f).natDegree = Hex.Berlekamp.basisSize f
```

Only the last two lines of that proof mention Berlekamp: `unfold
Hex.Berlekamp.basisSize Hex.DensePoly.degree?; simp [Nat.ne_of_gt hsize_pos]`,
where `basisSize f = f.degree?.getD 0` (`HexBerlekamp/BerlekampMatrix.lean:32`).
The preceding thirty-eight lines establish `(toMathlibPolynomial f).natDegree =
f.size - 1` for monic `f` over a nontrivial `ZMod p`, which is a fact about the
representation, not about factoring.

hex-poly-fp-mathlib's own SPEC states the ownership rule this violates: "A
lemma that mentions Berlekamp's `basisSize`, `isUnitPolynomial`, or Rabin's
test belongs in hex-berlekamp-mathlib even when its conclusion is about
`toMathlibPolynomial`, because it is a fact about the factoring algorithm
rather than about the representation." By the contrapositive, the degree fact
belongs here, and the Berlekamp theorem should be its two-line corollary.

The Ownership section states the cost of not doing this: "None of them should
have to depend on a factoring library to reach Mathlib." Today any consumer
needing the degree relation must either depend on hex-berlekamp-mathlib or
re-prove it. Neither hex-gf2-mathlib nor hex-gfq-mathlib currently needs it, so
this is a latent rather than realised cost, but hex-gfq-mathlib is the obvious
next claimant: the degree of a modulus is what makes a residue field the right
size.

For the shape to aim at, the generic layer has
`HexPolyMathlib.natDegree_toPolynomial` (`PolynomialEquivalence.lean:560`),
which is unconditional — `(toPolynomial p).natDegree = p.degree?.getD 0` — and
`leadingCoeff_toPolynomial` (`:586`). The unconditional form should be available
here too. What the generic proof uses in place of the
monicity-plus-nontriviality argument is
`Hex.DensePoly.coeff_last_ne_zero_of_pos_size` (`HexPoly/Dense.lean:417`),
which assumes only `[Zero R] [DecidableEq R]` and so applies to `ZMod64 p`
directly; the one extra step here is transporting `f.coeff (f.size - 1) ≠ 0`
across `toZMod`, which is injective because `ZMod64.equiv` is an equivalence.
So this library can state the hypothesis-free version and let Berlekamp keep
its `[Nontrivial]`-guarded specialisation, or drop that hypothesis too.

The central index line in `SPEC/Libraries/README.md` currently advertises
degree transport for this library. PR #9367 removes that claim because the
lemma is absent; if this issue is done instead, the claim becomes true and the
#9367 hunk should be dropped. Sequence the two deliberately rather than
letting one silently revert the other.

Found in the Phase 2 scaffolding review of HexPolyFpMathlib. Related to issue 1
(same root cause, different evidence).

---

### Issue 3

**Title:** `refactor(hex-poly-fp-mathlib): drop the redundant coeff_toMathlibPolynomial_equiv and its duplicated proof`

**Body:**

Three small cleanups in `HexPolyFpMathlib/Basic.lean`, all instances of the
duplication patterns `PLAN/Phase2.md` asks a scaffolding review to flag.

1. `coeff_toMathlibPolynomial_equiv` (`Basic.lean:247-250`) should be deleted.
   It is `@[simp, grind =]` with left-hand side `(toMathlibPolynomial f).coeff
   n`, syntactically identical to `coeff_toMathlibPolynomial`'s
   (`Basic.lean:233`), and a right-hand side `ZMod64.equiv (f.coeff n)` that is
   not in simp normal form: `HexModArithMathlib.ZMod64.equiv_apply`
   (`ZMod64Equiv.lean:229`) is itself `@[simp]` and rewrites `equiv a` to
   `toZMod a`. So the lemma adds a second simp rule with the same trigger whose
   output the simp set immediately undoes. It has no consumer: the only
   occurrence outside its own declaration is its name in
   `HexBerlekampMathlib/Irreducibility.lean:40`'s `export` list, so deleting it
   costs one name there. Its `_equiv` suffix also names the spelling of the
   right-hand side rather than the thing, which is the "name restating use-site
   context" smell from `.claude/CLAUDE.md`.

2. `coeff_toMathlibPolynomial`'s proof (`Basic.lean:236-245`) is a verbatim
   copy of `coeff_fpPolyToPolynomial`'s (`Basic.lean:58-66`), ten lines
   reproduced after a `show` that makes the two goals definitionally the same.
   `coeff_fpPolyToPolynomial` earns its place: the equivalence's `left_inv`,
   `right_inv`, `map_mul'` and `map_add'` fields all use it, so it must exist
   before `fpPolyEquiv` does, and its docstring says so. But
   `coeff_toMathlibPolynomial` should then be `coeff_fpPolyToPolynomial f n`
   rather than a second copy of the argument.

3. `HexGFqMathlib/Subfield.lean:32` and `HexGFqMathlib/Primitivity.lean:31`
   both say `open scoped HexPolyFpMathlib`. HexPolyFpMathlib declares nothing
   `scoped` — no `scoped instance`, no notation, no macro — so both lines have
   no effect. If the intent was to bring `commRing` into scope, that is
   unnecessary: it is a global instance. Delete both lines, or, if a future
   change does want the instance scoped, make it `scoped instance` and keep
   them.

None of these is a correctness problem; item 1 is the one with a behavioural
consequence, a redundant rule in a `simp` set that downstream files inherit.

Found in the Phase 2 scaffolding review of HexPolyFpMathlib.

---

## Current frontier

Phase 2 is satisfied for HexPolyFpMathlib: the library is read, the token is
committed, the SPEC Contents matches the implemented surface, and the three
gaps are drafted for filing. The gaps are additive-surface and hygiene issues,
not scaffolding violations; nothing in the tree needs to be deleted or
rewritten before the token stands.

## Next step

A second agent continues on this branch to record phases 1 through 5 in
`libraries.yml` with per-phase evidence. Two things it will want:

- `libraries.yml[HexPolyFpMathlib].done_through` is currently `0`, with a
  comment explaining that the extraction from HexBerlekampMathlib deliberately
  did not inherit phase state.
- Phase 4 for a correspondence-only mathlib layer requires the SPEC to declare
  comparator absence with the `correspondence-only-layer` reason
  (`PLAN/Phase4.md:218-222`). The SPEC currently says `proof-only-layer`. The
  open PR #9367 makes exactly that edit, so recording Phase 4 on this branch
  either waits on #9367 or duplicates its hunk; this session did not duplicate
  it, to keep the two from conflicting.

## Blockers

None. Issues 1 to 3 are drafted rather than filed, per the session's
instructions; they need a human or a follow-up session to file them.
