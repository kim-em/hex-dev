# BZ Mathlib bridge module-system migration (Phase 1b, #8598)

## Accomplished
Migrated `HexBerlekampZassenhausMathlib/` (13 files + umbrella) onto the
Lean 4 module system, the Phase-1b follow-up to #8597 (executable side).

Per file: `module`, `import X` -> `public import X`, `public section` +
`set_option backward.{proofsInPublic,privateInPublic} true` where private
decls are referenced in public. Then the exposure/meta work:

- **`@[expose]` pass (89 defs).** Exported `rfl`/`simp`/`unfold`/`change`/
  `decide`/`rw`-on-def proofs in the bridge reduce through executable and
  Mathlib-side defs; each surfaced as "Expected a definition with an exposed
  body" / "not unfolded because not exposed" / "not an inductive datatype".
  Exposed the flagged defs at their definition sites, driven outward from the
  first error until green. Sites span the executable `HexBerlekampZassenhaus/
  Basic.lean` (the bulk), `HexHensel/{Basic,Multifactor,QuadraticMultifactor}`,
  the Mathlib-side `HexBerlekampMathlib/Basic.lean` (`fpPolyEquiv`,
  `toMathlibPolynomial`), `HexPolyZMathlib/Mignotte.lean` (`l2norm`), and the
  bridge's own `Basic`/`Lattice`/`SignatureClasses`.
- **Meta tactic files.** `IrreducibleCert.lean` needed
  `public meta import ...CertReify` and its eval/match helpers marked `meta`
  (they run at elaboration inside the `irreducible_cert` elaborator);
  `IrreducibleCertTest.lean` needed `public meta import ...IrreducibleCert`
  and `roundTrips` marked `meta`.
- **Certificate kernel replay.** The `irreducible_cert` proofs attach
  `Eq.refl true` per certificate check, so the kernel must reduce
  `checkIrreducibleCertLinear` and its Berlekamp pow-chain replay plus the
  `Array`/`DensePoly` `==` comparisons. Handled in `IrreducibleCertTest.lean`
  with `import all HexBerlekampZassenhaus.Basic`, `import all
  HexBerlekamp.Irreducibility`, and `import all Init.Data.Array.DecidableEq`
  (the recipe's kernel-reduction tool, mirroring the executable side).
- **Two proof-text repairs**, both in the `monicModPImage`-zero branch of
  `existsUnique_modPFactorSubset...` in `Basic.lean`: a `simp [hzero]` that
  started leaving a spurious `SemigroupWithZero ?m` became `rw [if_pos hzero]`,
  and `exact dvd_zero _` on `toMathlibPolynomial 0` now rewrites through an
  inline `toMathlibPolynomial 0 = 0` (the file's `Polynomial.ext` idiom, since
  `map_zero` does not synthesize on `fpPolyEquiv`). No theorem statements
  changed.

## Current frontier
Full `lake build` green (4088 jobs), `HexBerlekampZassenhausMathlib` green,
`HexConformance` green, BZ bench/emit exes green, `scripts/check_dag.py` exit 0,
no `sorry`/`axiom`/`native_decide` in the diff.

## Next step
Second opinion, then open the PR. Phase 2 (splitting the 22k-line
`HexBerlekampZassenhausMathlib/Basic.lean`) is now unblocked and tracked
separately.

## Blockers
None.
