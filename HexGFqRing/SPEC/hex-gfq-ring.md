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

Representation choice: the stored representative is always canonical.
Callers do not manage reduction manually; `ofPoly` and all ring
operations normalize through `reduceMod`. Equality of quotient elements
is therefore equality of canonical representatives, not a separate
setoid-style relation.

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
