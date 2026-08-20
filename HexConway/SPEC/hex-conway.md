# hex-conway (Conway polynomial database, depends on hex-berlekamp)

Conway polynomials are canonical irreducible polynomials `C(p, n)` for
each prime `p` and degree `n`, satisfying compatibility conditions
across degree divisors: if `m | n`, then the image of a root of
`C(p, n)` under the norm map `GF(p^n) → GF(p^m)` is a root of
`C(p, m)`. This ensures that embeddings `GF(p^m) ↪ GF(p^n)` are
coherent.

This library has three distinct service tiers with very different
performance expectations. The implementation and API must keep these
tiers separate rather than presenting them as one undifferentiated
"compute a Conway polynomial" operation.

## Tier 1: imported database entries with irreducibility proofs

For many commonly used `(p, n)` pairs, import a known Conway polynomial
from Frank Lübeck's tables (or another explicit public source with the
same conventions). For these entries, the minimum contract is:

- store the polynomial coefficients
- prove `Irreducible (conwayPoly p n)` in Lean

This is the default path for finite field construction. Empirically,
checking irreducibility of a *given* polynomial over `F_p` is cheap
compared to either integer polynomial factorization or searching for new
Conway polynomials. Therefore this tier should be treated as the
baseline supported mode, not as a temporary fallback.

The intended engineering model is:

- the committed Lübeck slice is generated into a definition such as
  `luebeckConwayPolynomial? : (p n : Nat) → Option (FpPoly p)`
- the generated code is ordinary Lean code checked by the kernel
- support may change over time by regenerating this definition from a
  chosen finite manifest or bound policy
- regeneration should be driven by a command-level metaprogram rather
  than by manually editing the generated definition

The intended metaprogram interface is a command named
`rebuild_luebeckConwayPolynomial?`. It should take a scope specification
for the desired Lübeck slice, consume the immediately following command,
check that this following command is a definition of
`luebeckConwayPolynomial?`, and emit a `Try this:` replacement for that
definition.

The emitted replacement should contain:

- a new generated definition of `luebeckConwayPolynomial?` for the
  requested scope
- the rebuilding command itself, but commented out, immediately above
  the generated definition so the file remains self-rebuilding

The point of this interface is that the committed table remains ordinary
Lean code, while regeneration is still one command away and leaves a
clear audit trail in the source file.

The size of the committed Lübeck slice is determined by proof-checking
budget, not by mathematical coverage alone. The project should include
as much of the Lübeck table as possible subject to the requirement that
the generated Tier 1 correctness theorems (for example,
`luebeckConwayPolynomial?_irreducible`) still check in only a few
minutes of runtime on the benchmark machine.

## Tier 2: imported database entries with full Conway verification

For imported entries, a stronger contract is to verify that the imported
polynomial is not merely irreducible but actually satisfies the Conway
conditions relative to already-imported divisor-degree entries:

- irreducible
- primitive
- compatible with `C(p, m)` for each proper divisor `m | n`

This tier certifies the imported table itself. It is still much cheaper
than searching for new Conway polynomials from scratch, so the spec
should aim to cover all committed table entries at this level whenever
practical.

The same proof-budget rule applies here as the table grows: the
committed Tier 2 verification story should remain within a "few
minutes" regime for the generated correctness theorems on the benchmark
machine. If necessary, Tier 2 may temporarily cover a smaller subset of
the committed Tier 1 table while the stronger checker is optimized.

## Tier 3: on-demand Conway search

For `(p, n)` pairs not covered by the committed table, one may search
for the lexicographically smallest monic irreducible polynomial of
degree `n` over `F_p` satisfying the Conway compatibility conditions
with all `C(p, m)` for `m | n`.

This is a separate feature, not the default field-construction path.
The performance profile is much worse and much less predictable than
Tier 1 or Tier 2. In particular, "verify an imported Conway polynomial"
and "find a new Conway polynomial" must not be conflated in planning,
benchmarking, or user-facing expectations.

**Sources of Conway polynomials:**

1. **Hardcoded database** — commonly used `(p, n)` pairs, sourced from
   Frank Lübeck's tables. The required baseline is Tier 1. The intended
   target is Tier 2 for all committed entries.

2. **On-demand computation** — for `(p, n)` pairs not in the database,
   search for the lexicographically smallest monic irreducible polynomial
   of degree `n` over `F_p` satisfying the compatibility condition with
   all `C(p, m)` for `m | n`. This uses hex-berlekamp for irreducibility
   testing. The result is deterministic (the definition of Conway
   polynomial specifies "lexicographically smallest").

**API:**
```lean
/-- A committed table hit, packaging the polynomial with its primality witness
    and a proof that the lookup resolves to it. Unconstructible for an
    uncommitted pair, which is how `conwayPoly` stays total only where the
    table covers. -/
structure SupportedEntry (p n : Nat) [ZMod64.Bounds p]

theorem conwayPoly_nonconstant (p n : Nat) : 0 < (conwayPoly p n).degree
theorem conwayPoly_irreducible (p n : Nat) : Irreducible (conwayPoly p n)
```

**Tier 2, as shipped.** `HexConway/Compatibility.lean` proves divisor
compatibility for every committed pair `(p, m, n)` with `m ∣ n` and `m < n`:
fifty-two theorems `compat_p_m_n : Compatible p m n`, plus
`not_compatible_11_4_6` as a negative control so the check is visibly not
vacuous.

`Compatible` is a decidable `Bool` statement about the norm

```
N(α) = α ^ ((p^n - 1) / (p^m - 1))
```

being a root of `C(p, m)`. The exponent reaches `402234` at `(13, 1, 6)`, which
would be a poor thing to hand the kernel; it does not have to be, because that
exponent is `1 + p^m + ... + p^((k-1)m)`, so the norm is a product of Frobenius
images and each Frobenius step is a modular composition. The whole block costs
seventeen seconds, against minutes for the Tier 1 certificates.

`eval_conwayPoly_subfieldGen_eq_zero` promotes the computation to a statement
about field elements: `C(p, m)` evaluated at `subfieldGen`, an element of
`F_p[x] / (C(p, n))`, is zero. The promotion goes through
`FpPoly.Quotient.eval_reduce_eq_reduce_composeModMonic`, which says modular
composition on representatives is evaluation in the quotient.

**What Tier 2 still owes.** Primitivity of each committed entry is not proved.
It needs the multiplicative order of the generator, hence a factorization of
`p^n - 1` carried as checkable data and an order predicate over the executable
field, and the Mathlib-free stack has neither.

The subfield embedding `GFq p m →+* GFq p n` is built, in hex-gfq-mathlib
(`HexGFqMathlib/Subfield.lean`), because `→+*` is a Mathlib notion. Given `m ∣ n`
and compatibility of the two committed entries, `conwayEmbed` substitutes the
norm element for the generator, and it is canonical because the target is the
Conway norm rather than an arbitrary root of `C(p, m)`: two callers embedding
`GF(p^m)` into `GF(p^n)` land on the same copy.

Multiplicativity is Mathlib's rather than ours. `Polynomial.eval₂RingHom` is a
ring homomorphism by construction, and `ofPolyHom_compose_eq_eval₂` identifies
it with the executable substitution using `Polynomial.induction_on'`, which
needs only `compose_add` and `compose_monomial`. No `compose_mul` is involved.
The descent to residues is Hex's own division identity plus the vanishing fact,
which is Tier 2 compatibility.

The API should expose the tiers explicitly rather than hiding them all
behind one partial-performance promise. Concretely:

- `conwayPoly` should be total only for committed table entries
- a separate API may request Tier 3 search explicitly
- callers that only need a verified irreducible modulus for `GF(p^n)`
  should be able to use Tier 1 entries without paying for Conway search

In particular, this library must not promise that every `(p, n)` is
handled quickly. The committed database and the search functionality are
different products.

The intended proof style for imported-table correctness is checker-based
but must not use `native_decide`. Project-wide, `native_decide` is
banned. The `hex-conway` table proofs should instead use explicit
verified checkers/tactics whose runtime is benchmarked and whose scaling
determines how much of the table is committed.

**hex-gfq** then defines
`GFq p n := FiniteField p (conwayPoly p n) (conwayPoly_nonconstant p n)
(conwayPoly_irreducible p n)`. When a user asks for `GF(p^n)`, the
Conway polynomial is chosen automatically *when a committed entry is
available*. For degrees outside the committed table, a separate explicit
search API may be used.

## External comparators

No external comparator is required.

**Justification:** `input-source-only` per
`SPEC/benchmarking.md §"Comparator naming"`. The only published
external reference for HexConway is Lübeck's Conway polynomial
database, and that database is the **input source** rather than an
executable comparator: HexConway verifies that committed table
entries are irreducible (Tier 1) and additionally satisfy the
primitivity / compatibility properties (Tier 2), and searches for
missing entries (Tier 3). The search direction has no
algorithmically distinct external implementation to race against —
GAP exposes the same Lübeck data, not a separately-engineered
search; and SageMath / FLINT either consume the same table or run
ad-hoc search code that is not packaged as a benchmarkable API.
The Phase-4 evidence is therefore the declared-complexity verdict
of HexConway's own bench targets across the three tiers.
