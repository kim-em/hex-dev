# hex-sparse-poly-mathlib (depends on hex-sparse-poly + hex-poly-mathlib + Mathlib)

The Mathlib correspondence layer for the canonical, Mathlib-free sparse
univariate polynomials in
[hex-sparse-poly](../../HexSparsePoly/SPEC/hex-sparse-poly.md). It
identifies `Hex.SparsePoly R` with `Polynomial R` while the executable
operations and the canonical representation stay in the core library.

## Scope

The layer owns correspondence only:

- `denseEquiv`, the ring equivalence between `Hex.SparsePoly R` and
  `Hex.DensePoly R`, packaging the core library's `toDense`/`ofDense`
  conversions, round trips, and homomorphism laws;
- `equiv`, the ring equivalence with `Polynomial R`, defined as
  `denseEquiv.trans HexPolyMathlib.equiv`;
- one correspondence lemma per public core operation: `coeff_equiv`,
  `equiv_toDense`, `equiv_support`, `equiv_eval`, `equiv_derivative`,
  `equiv_compose`, `equiv_substPow`, `equiv_substScale`,
  `equiv_monomial`, `equiv_C`, `equiv_X`, `equiv_natDegree`,
  `equiv_leadingCoeff`, and `equiv_monic`. Ring-structural images
  (zero, one, addition, multiplication, negation, powers,
  divisibility) are free from the `RingEquiv` via `map_*` and are
  deliberately not restated.

Following the project split, no theorem about `SparsePoly` itself
belongs here: representation facts (including `mem_support_iff`, which
`equiv_support` consumes) live in `hex-sparse-poly`, and dense-side
facts live in `hex-poly` / `hex-poly-mathlib`.

## Principal equivalence

```lean
def denseEquiv [CommRing R] [DecidableEq R] :
    Hex.SparsePoly R ≃+* Hex.DensePoly R
def equiv [CommRing R] [DecidableEq R] :
    Hex.SparsePoly R ≃+* Polynomial R :=
  denseEquiv.trans HexPolyMathlib.equiv
```

Both are stated at Mathlib's `[CommRing R]`. The parent SPEC records
that the core's multiplicative transport laws (`toDense_mul` and the
laws derived from it) sit at `Lean.Grind.CommRing` because the dense
layer proves its own multiplication laws there; `denseEquiv.map_mul'`
reuses that transport, so the equivalence inherits the class. Every
consumer type in the project is a `CommRing`. If the dense laws are
ever weakened to semirings, these statements follow at no cost.

## Headline correctness theorem

The headline is `equiv`: the executable sparse representation *is*
Mathlib's polynomial ring, exactly. Its semantic content is fixed by
two clauses:

```lean
theorem coeff_equiv (s : Hex.SparsePoly R) (e : Nat) :
    (equiv s).coeff e = s.coeff e
theorem equiv_support (s : Hex.SparsePoly R) :
    (equiv s).support = s.support.toList.toFinset
```

`coeff_equiv` pins the ring identification coefficientwise, so `equiv`
is the unique coefficient-preserving map and every further
correspondence lemma is a consequence of coefficient extensionality.
`equiv_support` is the statement that is genuinely about this
representation rather than transported through the dense one: the
stored exponents are exactly Mathlib's `support`, which is the sense in
which the representation is sparse. It needs both canonical-form
invariant halves, via the core library's `mem_support_iff`.

## Verification

Every conversion theorem is proved from coefficient extensionality on
one side or the other. The conformance target checks representative
round trips and operation correspondence against Mathlib's
`Polynomial` by `decide`/`#guard` on concrete inputs, mirroring the
`hex-mv-poly-mathlib` conformance module.

## External comparators

`correspondence-only-layer`: this library is a correspondence-only
mathlib layer with zero bench targets, so there is no surface of its
own to compare. The computational performance owners whose bench
targets carry the evidence for the operations it transports are
`hex-sparse-poly` (the sparse operations) and `hex-poly` (the dense
representation `denseEquiv` lands in).
