# hex-gfq-ring (GF(q) as a ring, depends on hex-poly-fp)

Canonical quotient-ring implementation for `F_p[x] / (f)`.

We only form quotient rings by a nonconstant modulus. Concretely, the
public quotient type should carry a hypothesis `0 < f.degree`, so the
canonical-representative invariant "degree < deg(f)" is meaningful and
we do not need to special-case `f = 0` or constant moduli throughout the
API.

**Contents:**
- `reduceMod (f : FpPoly p) : FpPoly p → FpPoly p` — canonical remainder
  on division by `f`
- `PolyQuotient p f hf` — quotient elements, represented by a reduced
  polynomial modulo `f`
- Smart constructor `ofPoly : FpPoly p → PolyQuotient p f hf`
- Projection `repr : PolyQuotient p f hf → FpPoly p`
- Ring operations: addition, multiplication, negation, subtraction,
  exponentiation; every operation reduces via `reduceMod`.
  `pow x n` is square-and-multiply (`O(log n)` quotient-ring
  multiplications). `nsmul n x` and `natCast n` use binary
  decomposition with the same complexity; the textbook
  `n+1 ↦ pred + 1` recursion is forbidden.
- `Lean.Grind.CommRing (PolyQuotient p f hf)` instance

Representation choice: the stored representative is canonical, and the
type says so. `PolyQuotient` is a subtype carrying `IsReduced`, so a raw
`FpPoly` cannot be passed where a quotient element is expected. Callers
do not manage reduction manually; `ofPoly` and all ring operations
normalize through `reduceMod`. Equality of quotient elements is therefore
equality of canonical representatives, not a separate setoid-style
relation.

`PolyQuotient` takes `[ZMod64.PrimeModulus p]`, so a quotient element
cannot be formed over a composite modulus at all. That restriction is
real rather than defensive: at composite `p` the long-division step
divides by a leading coefficient that need not be a unit, `reduceMod` is
then not a canonical form, and two values would represent one residue
class. `isReduced_iff_degree_lt` states the contract the hypothesis
buys.

Primality is sufficient rather than necessary. A monic modulus needs no
coefficient inversion and would be canonical over any `p`; the uniform
prime hypothesis is the deliberate choice, since every modulus this
library serves is over a prime field. Generalizing to monic moduli over
a general coefficient ring would need a division-law package that does
not exist yet.

`reduceMod` itself stays general, along with its degree-short-circuit
lemmas; it is the quotient type that carries the canonicality claim, so
it is the quotient type that is restricted.

This does NOT require `f` to be irreducible — the quotient is always a
ring. When `f` is irreducible, the same underlying representation
supports a field structure; that extension belongs to hex-gfq-field.

**Key properties:**
- `repr (ofPoly a) = reduceMod f a`
- `degree (repr x) < degree f`
- `ofPoly (reduceMod f a) = ofPoly a`
- `reduceMod f (a + b) = reduceMod f (reduceMod f a + reduceMod f b)`
- `reduceMod f (a * b) = reduceMod f (reduceMod f a * reduceMod f b)`
- Ring axioms for `PolyQuotient p f hf`

## Fast-arithmetic adoption

The quotient multiplication operation now calls `FpPoly.mulFast`; its
coefficient-owner dispatcher retains schoolbook multiplication below 16
coefficients and selects packed or NTT-backed multiplication above the measured
boundaries. Square-and-multiply exponentiation inherits that choice. Canonical
representatives and every `reduceMod` theorem are unchanged because
`FpPoly.mulFast_eq` identifies the selected product with `DensePoly.mul`.

Three warm outer trials on `chungus2`, Lean `4.34.0-rc2`, over `F_65537` give
these representative medians; all result hashes agree:

| operation | degree | retained | selected/candidate |
|---|---:|---:|---:|
| quotient multiplication | 32 | 44.670 µs | 39.602 µs |
| quotient multiplication | 128 | 641.710 µs | 499.139 µs |
| quotient power | 32 | 467.483 µs | 388.016 µs |
| quotient power | 128 | 9.359 ms | 6.688 ms |
| quotient power | 256 | 39.840 ms | 30.304 ms |
| one-shot reduction | 32 | 28.308 µs | 2.879 ms |
| one-shot reduction | 256 | 1.495 ms | 74.109 ms |

The first two operation families adopt fast multiplication. The one-shot
Newton `DivPlan` candidate loses by a wide margin on every rung from 32 through
256, so `reduceMod` remains the monic long-division implementation. Reproduce
the screens with `lake exe hexgfqring_bench compare` and the paired
`runMulSchoolbookChecksum`/`runMulChecksum`,
`runPowSchoolbookChecksum`/`runPowChecksum`, and
`runReduceModChecksum`/`runReduceFastChecksum` targets, adding
`--outer-trials 3`.

## External comparators

No external comparator is required.

**Justification:** `structural-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. HexGFqRing's semantic
domain is `F_p[x]/(f)` for *any* nonconstant `f`, including reducible
moduli (see the contents section: "This does NOT require `f` to be
irreducible — the quotient is always a ring"). The natural FLINT
primitive `fq_default` rejects reducible moduli at `ctx` construction
time (FLINT internally selects between `fq_nmod` and `fq_zech`
representations, both of which assume a field), so it cannot serve as
a reference implementation for HexGFqRing's actual scope.

Other FLINT primitives (`nmod_poly` with explicit `nmod_poly_divrem`
per multiplication) cover the general quotient case but do not measure
the comparison HexGFqRing's design point is targeting — they pay
reduction overhead on every operation and do not exploit the
fixed-modulus structure, so the ratio carries no information about
quotient-ring constant-factor parity.

Coverage at the finite-field subset of HexGFqRing's domain is provided
upstream by HexGFqField's external comparator declaration (FLINT
`fq_default`, informational), which exercises HexGFqRing's quotient
arithmetic transitively through `FiniteField p f hf hirr`'s thin
wrapper over `PolyQuotient p f hf`. The irreducibility precondition
that breaks the declaration at this layer is naturally satisfied at
the field layer.
