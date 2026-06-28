# hex-berlekamp-mathlib (depends on hex-berlekamp + hex-poly-mathlib + hex-mod-arith-mathlib + Mathlib)

Proves the full correctness of Berlekamp's algorithm and Rabin's test
by transferring to `Polynomial (ZMod p)` and using Mathlib's Euclidean
domain theory.

**Key theorems:**
```lean
theorem irreducible_of_mem_berlekampFactor (f : FpPoly p) (hf : squareFree f) :
    ∀ g ∈ berlekampFactor f, Irreducible g

theorem rabin_irreducible (f : FpPoly p) (hf : f.degree = n) :
    rabinTest f = true ↔ Irreducible f

instance [Fact (Nat.Prime p)] : DecidablePred (Irreducible · : Polynomial (ZMod p) → Prop)
```

**Proof strategy for `irreducible_of_mem_berlekampFactor`:**

The proof proceeds by contrapositive: if `g` is reducible, we
construct a nonconstant Berlekamp kernel element, which means the
algorithm would have split `g` further.

The proof works through the ring equivalence
`FpPoly p ≃+* Polynomial (ZMod p)` (from hex-poly-mathlib +
hex-mod-arith-mathlib). Steps 1-3 use Euclidean domain theory
that Mathlib provides for `Polynomial (ZMod p)`:

- `Polynomial.dvd_iff_isRoot` (factor theorem)
- `IsCoprime.mul_dvd` (coprime divisibility)
- `Irreducible.prime` (irreducible ⟹ prime in UFD)
- `ZMod.pow_card` (Fermat's little theorem for `ZMod p`)

**Step 1. `X^p - X = ∏_{c ∈ F_p} (X - c)` over F_p.**
From Fermat's little theorem (already in `hex-arith`): every `c ∈ F_p`
is a root of `X^p - X`, there are `p` of them, and `deg(X^p - X) = p`,
so the factorization follows by leading coefficient comparison.

**Step 2. Reducible squarefree polynomials have nonconstant kernel
elements.**
If `g` is reducible, write `g = a * b` with `a, b` nontrivial. Since
`g` is squarefree, `gcd(a, b) = 1`. By `polyCRT` (from `hex-poly`),
find `h` with `h ≡ 0 (mod a)` and `h ≡ 1 (mod b)`, reduced mod `g`.
Then:
- `a | h`, so `a | h^p - h` (since `0^p - 0 = 0`)
- `b | h - 1`, so `b | h^p - h` (since `1^p - 1 = 0`)
- `gcd(a, b) = 1`, so `g = a * b | h^p - h`

And `h` is nonconstant mod `g`: `h ≡ 0 (mod a)` but `h ≡ 1 (mod b)`.

Note: this does NOT require factoring `g` into irreducibles — any
nontrivial coprime splitting works.

**Step 3. Nonconstant kernel elements produce nontrivial GCD splits.**
If `g` is squarefree and `g | h^p - h` with `h` nonconstant mod `g`:
by step 1, `h^p - h = ∏_{c ∈ F_p} (h - c)`, so
`g | ∏_{c ∈ F_p} (h - c)`. The factors `(h - c)` are pairwise coprime
(they differ by nonzero constants). Each irreducible factor of `g`
divides exactly one `(h - c)`, so `g = ∏_{c ∈ F_p} gcd(g, h - c)`
(using `g` squarefree). Since `h` is nonconstant, the irreducible
factors of `g` distribute among at least two values of `c`, so
`gcd(g, h - c)` is nontrivial for some `c`.

**Step 4. Kernel of `f` surjects onto kernel of `g | f`.**
If `g | f` with `gcd(g, f/g) = 1` (which holds since `f` is
squarefree), then for any `h` with `g | h^p - h`, `polyCRT` gives
`h'` with `h' ≡ h (mod g)` and `h' ≡ 0 (mod f/g)`. Then
`g | h'^p - h'` and `(f/g) | h'^p - h'`, so `f | h'^p - h'`.
The element `h' mod f` is in the Berlekamp kernel of `f` and maps to
`h mod g` under reduction.

**Step 5. Completeness.**
The algorithm computes a basis `{h₁, …, hₖ}` of the Berlekamp kernel
of `f` (nullspace of `Q_f - I`), then for each `h_i` and each
`c ∈ F_p`, splits current factors via `gcd(factor, h_i - c)`.

After processing all basis elements, every output factor `g` has the
property that each `h_i` is constant mod `g`. This is because: when
`h_i` was processed, either `g` itself was in the factor list and
wasn't split by `h_i` (so `g | h_i - c₀` for some `c₀`), or an
ancestor `g' ⊇ g` was present with `g' | h_i - c₀`, giving
`g | h_i - c₀` too.

Since every basis element is constant on `g`, and the basis spans the
kernel of `f`, the image of the kernel of `f` under reduction mod `g`
consists only of constants. By surjectivity (step 4), the kernel of `g`
itself consists only of constants. If `g` were reducible, step 2 would
give a nonconstant kernel element — contradiction. So `g` is
irreducible.

**Note on representatives.** The `polyCRT` construction builds
`h = u · t · b + v · s · a`, which can have degree up to
`deg(a) + deg(b) - 1`, exceeding `deg(f)` or `deg(g)`. All
operations should use `h mod f` (or `h mod g`) as the representative.
This is safe because kernel membership depends only on the residue
class: `f | h^p - h` iff `f | (h mod f)^p - (h mod f)`, and GCD
computations respect reduction: `gcd(g, h - c) = gcd(g, (h mod g) - c)`.

**Proof strategy for `rabin_irreducible`:**

Unlike Berlekamp's completeness proof (which avoids finite field
theory entirely), both directions of Rabin's theorem require the
theory of finite field extensions.

The theorem statement needs `[Fact (Nat.Prime p)]` and `0 < n`.

**(→) test passes ⟹ irreducible.** By contrapositive: assume `f`
is reducible and both test conditions hold. The first condition
`f | X^(p^n) - X` is already satisfied, so we derive a contradiction
from the coprimality checks. Pick an irreducible factor `g | f` with
degree `d < n`. Then `g | X^(p^n) - X`, so by the degree lemma
(step 5 below) `d | n`. Since `d < n`, pick a prime `q | n/d`; then
`q | n` and `d | n/q`. Therefore `g | X^(p^(n/q)) - X`, so
`g | gcd(f, X^(p^(n/q)) - X)`, meaning the gcd is nontrivial and
the coprimality check rejects.

Note: `reducible f` alone does not give `d | n` — we need the
test's divisibility condition `f | X^(p^n) - X` to get
`g | X^(p^n) - X` first.

**(←) irreducible ⟹ test passes.** Two parts:

- `f | X^(p^n) - X`: the quotient `F_p[x]/(f)` is a field with
  `p^n` elements. Every element `a` satisfies `a^(p^n) = a` by
  `FiniteField.pow_card_pow`. So `X^(p^n) - X` vanishes in the
  quotient, i.e. `f | X^(p^n) - X`.

- `gcd(f, X^(p^(n/q)) - X) = 1` for each prime `q | n`: if the
  gcd were nontrivial, since `f` is irreducible (hence prime in
  `(ZMod p)[X]`), we'd have `f | X^(p^(n/q)) - X`. Applying the
  degree lemma (step 5 below) gives `n | n/q`, impossible for
  prime `q | n`.

**Finite field theory used** (all in Mathlib; step 5 is
assembled from (1)+(4)):

1. Irreducible `f` of degree `n` ⟹ `F_p[x]/(f)` is a field.
   `AdjoinRoot.instField` (`Mathlib.RingTheory.AdjoinRoot`): gives
   `Field (AdjoinRoot f)` when `[Fact (Irreducible f)]`.

2. `|F_p[x]/(f)| = p^n`.
   `FiniteField.pow_finrank_eq_natCard`
   (`Mathlib.FieldTheory.Finite.GaloisField`):
   `p ^ Module.finrank (ZMod p) k = Nat.card k`.
   `AdjoinRoot.powerBasis` provides the basis `{1, root, …, root^(n-1)}`
   and `PowerBasis.dim` gives `finrank = natDegree`.

3. `a^(p^n) = a` for all `a ∈ GF(p^n)`.
   `FiniteField.pow_card` (`Mathlib.FieldTheory.Finite.Basic`):
   `a ^ q = a` for any element of a finite field of order `q`.
   Iterated: `FiniteField.pow_card_pow`.

4. `GF(p^m) ⊆ GF(p^n)` iff `m | n`.
   `FiniteField.nonempty_algHom_iff_finrank_dvd`
   (`Mathlib.FieldTheory.Finite.GaloisField`):
   `Nonempty (K →ₐ[F] L) ↔ Module.finrank F K ∣ Module.finrank F L`.

5. `g` irreducible of degree `d`, `g | X^(p^n) - X` ⟹ `d | n`.
   Assembled from (1)+(4): the hypothesis `g | X^(p^n) - X` means
   `X^(p^n) - X` vanishes in `AdjoinRoot g`, so `root g` lies in
   (the image of) `GF(p^n)`; use `AdjoinRoot.liftAlgHom` to build
   an embedding `AdjoinRoot g →ₐ[ZMod p] GF(p^n)`. Then (4) gives
   `Module.finrank (ZMod p) (AdjoinRoot g) ∣ Module.finrank (ZMod p) (GF(p^n))`,
   which is `d ∣ n`.

**Additional useful Mathlib API:**
- `GaloisField` = `SplittingField (X ^ p ^ n - X)`, with
  `GaloisField.card`: `Nat.card (GaloisField p n) = p ^ n`
- `GaloisField.algEquivGaloisField`: any finite field with `p^n`
  elements is isomorphic to `GaloisField p n`
- `FiniteField.roots_X_pow_card_sub_X`: all elements of `K` are
  roots of `X^|K| - X`
- `FiniteField.galois_poly_separable`: `X^q - X` is separable

**Local glue lemmas needed** (not one-liners from Mathlib):
- `AdjoinRoot.mk_eq_zero`: turn `f | P` into `P(root f) = 0` in
  `AdjoinRoot f`
- Build `AdjoinRoot g →ₐ[ZMod p] GF(p^n)` from `g | X^(p^n) - X`
  via `AdjoinRoot.liftAlgHom`
- `finrank (ZMod p) (AdjoinRoot g) = g.natDegree` from
  `AdjoinRoot.powerBasis` and `PowerBasis.dim`
- gcd ↔ divisibility bridge: `gcd(f, P) ≠ 1` plus `Irreducible f`
  gives `f | P` in `Polynomial (ZMod p)`, via Euclidean-domain / prime API
- Divisibility arithmetic: from `d | n` and `d < n`, choose a prime
  `q | n/d` and derive `d | n/q` and `q | n`
- Computational bridge: `rabinTest f = true` unfolds to the exact
  divisibility check `f | X^(p^n) - X` plus coprimality of
  `f` with `X^(p^(n/q)) - X` for each prime `q | n`
