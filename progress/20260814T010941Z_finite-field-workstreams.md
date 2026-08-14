# Finite-field libraries: Conway regeneration, the GF(2) correspondence, Phase 7 checks

Continues `progress/20260814T000741Z_finite-field-audit-w0.md`, which recorded
the audit of `hex-gf2`, `hex-gf2-mathlib`, `hex-gfq-field`, `hex-conway`,
`hex-gfq`, `hex-gfq-mathlib` and the first slice of work. This file covers the
three slices after it.

## Accomplished

Four branches, each its own PR, all stacked on `ff-audit-w0`.

**`ff-audit-w0`** (#9242) — the accuracy slice from the previous file, plus a
correction. It originally claimed `HexGF2Mathlib` and `HexGFqMathlib` were not
built by the required check. That was wrong: `ci.yml` builds `HexManual`, whose
`HexGFq` chapter imports `HexGFqMathlib`, which imports `HexGF2Mathlib`. The
grep behind the claim ran against an older worktree, from before `ci.yml`
gained its `Build HexManual` step. Both libraries were already built; what they
were not is cached. The change stands on that smaller footing and the commit
message, PR body, and prior progress file are all corrected.

**`ff-audit-w1`** (#9246) — Conway table regeneration and a wider table.

- `HexConway/Rebuild.lean` supplies `rebuild_luebeckConwayPolynomial?`, the
  command the SPEC names. It takes a scope, reads the committed Lübeck cache,
  consumes the `luebeckConwayCoeffs?` definition below it, and offers the
  regenerated definition as a `Try this:` replacement carrying its own
  invocation commented out above. Regenerating at the previous scope reproduced
  the committed table byte for byte.
- The scope is a maximum degree per prime, matching the `SLICE` in
  `update_luebeck_conway_cache.py`. Certificate cost grows with both the prime
  and the degree, so a uniform bound is the wrong shape.
- `HexConway/EntrySource.lean` generates the rest of a widening. Per entry that
  is a literal, monic and degree facts, a hit lemma, a Rabin certificate, its
  kernel check, the irreducibility theorem, two coefficient-list transports, a
  `SupportedEntry`, and an arm in each aggregate. All mechanical except the
  certificate, which `Berlekamp.buildIrreducibilityCertificate?` computes.
- The binary column now runs to degree 8, so `GF(2^8)` is a committed Conway
  field and the AES tutorial has one to use. 38 entries, up from 36.
- `reports/hex-conway-performance.md` gains the proof-budget measurement the
  SPEC's sizing rule depends on and that had never been taken: 31s for 38
  entries, against a "few minutes" rule.

**`ff-audit-w2`** (#9248) — the GF(2) correspondence now uses Mathlib's
`RingEquiv`. The local records were the only ones in the repository, the
justification in their docstring was false (the file imports Mathlib, and
Mathlib's `RingEquiv` wants the same typeclass context), and the SPEC's central
claim that Mathlib theorems apply was false with them. `equivGFq` collapses to a
single `trans` and loses a file-scoped 800k heartbeat bump. Four `noncomputable`
markers turn out to be unnecessary. Net 78 lines removed.

**`ff-audit-w6`** (#9249) — `scripts/check_phase7.py` enforces the Phase 7
chapter and anchored-tutorial obligations, which nothing checked. The
Kummer-Dedekind tutorial is re-anchored from `hex-gfq` to
`hex-berlekamp-zassenhaus`, matching its own primary-library list. `HexGF2`
rolls back to 6 because its AES tutorial does not exist; `HexGFq` stays at 7
because re-anchoring leaves it with no outstanding tutorial.

## Current frontier

Done: workstreams 0, 1a, 1b, 2a, part of 2d, and 6 of the plan in
`~/.claude/plans/give-me-a-really-moonlit-rivest.md`.

Not started, in rough value order:

1. **1c/1d, Conway Tier 2 and the subfield embeddings.** The generator and the
   budget measurement now make widening mechanical, so this is the next real
   mathematics. Tier 2 needs primitivity, hence the multiplicative order of a
   root, hence the factorization of `p^n - 1`; check `HexArith`'s prime
   machinery first, and see `SPEC/future-work.md` § "Better primality". The
   payoff is `conwayPoly_compat` and `GFq p m →+* GFq p n` for `m ∣ n`, which is
   the entire reason for preferring Conway polynomials and is undelivered.
2. **5g, the AES tutorial.** Now unblocked by `GF(2^8)` being committed, and it
   is what returns `HexGF2` to Phase 7. The chapter already contains an
   embryonic version at `Chapters/HexGF2.lean:188-213`.
3. **3a, the `Lean.Grind` instances for `GF2Poly`, `GF2n`, `GF2nPoly`.** Worth
   correcting the plan here: this is not the assembly job it was scoped as.
   `HexGFqField` builds its instances by delegating each law to the quotient
   ring's own `Lean.Grind.CommRing`; `GF2Poly` has no such underlying structure,
   so every field of `Lean.Grind.Semiring` has to be discharged from the bare
   theorems. Several (`pow_zero`, `pow_succ`, the `nsmul` and `natCast` laws) do
   not obviously exist yet.
4. **3b, the CLMUL extern paths.** `lakefile.lean:24` omits `-mpclmul`, so
   x86-64 builds compile only the portable fallback and Apple silicon only
   `vmull_p64`. Each machine tests one path and neither tests the other,
   contrary to an explicit SPEC requirement.
5. **2b**, `hex-poly-fp-mathlib` as the home for
   `FpPoly p ≃+* Polynomial (ZMod p)`, currently owned by `HexBerlekampMathlib`
   at `done_through: 3`. Blast radius outside these libraries; own branch.
6. **4**, reconciling the SPECs with the shipped API, and the remaining Phase 6
   items.
7. **5b-5f**, the manual build-out.

## Next step

Tier 2 (1c), or the AES tutorial (5g) if a visible deliverable is wanted first.
5g is much the smaller of the two and closes a Phase 7 rollback.

## Blockers

None. Two process notes:

- `lake build HexManual` belongs in the verification for any change touching a
  library the manual documents. Leaving it out of the Conway branch's checks let
  a stale `#guard` on `C(2, 7)` reach CI, which caught it.
- Never run two `lake` invocations against one worktree. Doing so produced a
  one-off failure in an unrelated module that did not reproduce.

## Verification

Per branch, all clean: `lake build` over the touched libraries plus
`HexConformance` and the bench and emit-fixture executables (9461 jobs on
`ff-audit-w1`, 9362 on `ff-audit-w2`), `lake build HexManual` (9719 jobs), and
`check_dag`, `check_phase4`, `check_phase7`, `check_file_line_counts`,
`check_copyright_headers`. `scripts/oracle/conway_luebeck.py` checks all 38
committed entries against Lübeck's published table.
