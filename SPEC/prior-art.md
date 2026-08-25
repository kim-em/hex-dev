# Prior art

**Isabelle/HOL** (the gold standard): The Innsbruck group verified the
entire Berlekamp-Zassenhaus + LLL pipeline. Degree-500 polynomials factor
at 2.5x Mathematica speed. ~44K lines across multiple AFP entries.

**Baanen et al. (Lean 4)**: Certificate-based irreducibility checking for
the rings-of-integers project. Uses `decide`/`native_decide` on list-based
polynomials. Works but doesn't scale beyond small degrees. Our project
does not adopt this proof strategy: `native_decide` is banned, so large
computational proofs must instead run through explicit verified
checkers.

**Conway-polynomial ecosystem**: Frank Lübeck's public tables currently
contain `47,090` Conway polynomials, covering `10,453` primes up to
`109987`, with deep degree coverage only for comparatively small primes
(for example `p=2` up to degree `409`, `p=3` up to `263`, `p=5` up to
`251`, `p=97` up to `127`, but `p=65537` only up to `7`). Experiments
with GAP and PARI suggest a sharp three-way split that is important for
our design: checking irreducibility of a *given* finite-field polynomial
is extremely cheap; verifying that an imported table entry is genuinely
Conway (irreducible + primitive + divisor-compatibility) is still cheap
enough to treat as a practical certification task for committed tables;
but searching for missing Conway polynomials has steep and irregular
performance cliffs just beyond the known tables. This is why `hex-conway`
distinguishes imported entries with irreducibility proofs, imported
entries with full Conway verification, and explicit on-demand search.

**CoqEAL (Coq)**: Verified Karatsuba, Strassen, Bareiss, Smith normal form.
Refinement-based approach.

**FLINT (C)**: The performance target. Dense `nmod_poly` and `fmpz_poly`
with Barrett reduction, Karatsuba, NTT. Not verified.

**Harvey's practical multiplication kernels**: The fast-polynomial SPEC uses
only three pieces of this line of work: multipoint Kronecker substitution
(KS2/KS3/KS4), redundant-residue Shoup butterflies for word-sized NTTs, and
the Karatsuba polynomial middle product underlying the integer middle-product
paper. The exact algorithms, bounds, and references are recorded in
[hex-poly-fast](Libraries/hex-poly-fast.md); the rest of Harvey's publication
list is not part of that roadmap.
