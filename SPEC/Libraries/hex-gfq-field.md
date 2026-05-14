# hex-gfq-field (GF(q) as a field, depends on hex-gfq-ring)

Field structure on top of the canonical quotient-ring implementation
from hex-gfq-ring. Takes any irreducible polynomial as parameter — not
tied to Conway polynomials.

The key layering decision is that this library does not introduce a
separate representation. `FiniteField p f hf hirr` should be a thin
wrapper over `PolyQuotient p f hf`, or reuse that same underlying data
with stronger assumptions. There is one quotient representation, one
canonical reduction function, and one equality story across the ring and
field libraries.

**Contents:**
- `FiniteField p f hf hirr` — the field `F_p[x]/(f)`, where `hf : 0 <
  f.degree` and `hirr : Irreducible f`
- Coercions or conversion functions to and from `PolyQuotient p f hf`
- Multiplicative inverse via extended GCD in `F_p[x]`
- Division and exponentiation. `pow x n` is square-and-multiply
  (`O(log n)` field multiplications); the textbook `n+1 ↦ pow n * x`
  recursion is forbidden because cryptographic exponents (e.g. `n =
  p` for Frobenius, with `p ≈ 2^31`) make linear-time `pow`
  non-terminating.
- Frobenius map `frob : FiniteField p f hf hirr → FiniteField p f hf hirr`,
  computed as `pow x p` (and therefore inheriting the
  square-and-multiply complexity)
- `Lean.Grind.Field (FiniteField p f hf hirr)` instance
- `IsCharP (FiniteField p f hf hirr) p`

The irreducibility proof `hirr` may come from hex-berlekamp (either via
the algorithm or via a certificate), but this library should not depend
on hex-berlekamp for its core API. It works for any supplied proof of
irreducibility. For a canonical choice of irreducible modulus, see
hex-gfq.

`Fintype` and cardinality belong in the Mathlib bridge, not here. The
computational library should expose the concrete field operations and
their algebraic laws, while `hex-gfq-mathlib` supplies finiteness,
cardinality, and correspondence with Mathlib's abstract finite fields.

**Key properties:**
- `inv a * a = 1` for `a ≠ 0`
- `a / b = a * b⁻¹`
- `frob(a) = a ^ p`
- Field axioms for `FiniteField p f hf hirr`

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fq_default` arithmetic via python-flint | informational | bench targets exercising finite-field arithmetic: addition, multiplication, reduction modulo `f`, inversion, division, exponentiation, Frobenius |

FLINT's `fq_default` is the standard reference for finite-field
arithmetic and covers the same operations as HexGfqField:
reduction modulo a fixed irreducible modulus polynomial, addition,
multiplication, inversion, division, and exponentiation. FLINT
internally selects between representations (`fq_nmod` for word-size
primes, `fq_zech` for small fields) via crossover heuristics that
Hex does not replicate; the constant-factor gap is structural rather
than algorithmic. Classification is `informational`.

The irreducibility precondition `hirr : Irreducible f` carried by
`FiniteField p f hf hirr` matches the precondition `fq_default`
imposes at `ctx` construction time — bench fixtures generated from
the field type satisfy this automatically. This is the layer at
which the FLINT primitive's contract aligns with Hex's; the
underlying quotient-ring arithmetic in HexGfqRing handles the
general (reducible-modulus) case for which no clean FLINT primitive
exists, and is covered transitively through this declaration on
fixtures whose moduli are irreducible.

Wired via a persistent-subprocess Python driver per
`SPEC/benchmarking.md §"External comparators" §"Process call"`.

Structured metadata in `libraries.yml: HexGfqField.phase4.comparators`.
