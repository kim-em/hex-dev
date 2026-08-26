# issue #8854: reusable transport layer COMPLETE (green); Quadratic.lean assembly remains

## Accomplished (all committed on issue-8854, green, no sorry/axiom)

The entire reusable Mathlib-free transport infrastructure is done:

- `HexPoly/Euclid/MonicUnique.lean`: `DensePoly.divMod_eq_of_reconstruction`
  (monic-division uniqueness).
- `HexHensel/WordStep.lean`: `Lean.Grind.CommRing (WordMod ctx)` + scalar bridge
  (toNat injective, ofNat_toNat, intModNat_add/mul/sub).
- `HexHensel/WordTransport.lean`: `toWP`/`ofWP` with the FULL ring-hom transport:
  toWP_add, toWP_sub, toWP_mul (the convolution crux — residue relation carried
  through the mulCoeffSum nested fold on a common range), toWP_one, toWP_zero,
  toWP_congr, toWP_reduceModPow, ofWP_toWP_of_canonical, and toWP
  size/monic/degree preservation.

Measured earlier (reverted from tree, on the issue): word kernel byte-identical
(5 #guards); interleaved SD4 A/B ~3.5-4%; isolated lift ~13% of factorLattice.

## Current frontier — the final assembly in HexHensel/Quadratic.lean

Written but reverted (hit Mathlib-free tactic walls, needs redo): the guarded
dispatch + byte-identity proof. Design (validated in pieces):

- Kernel `quadraticHenselStepWord?` with guard `m*m<2^64 ∧ odd ∧ 1<m*m ∧
  leadingCoeff g = 1 ∧ 0<deg g`, computing the step over `toWP`-mapped inputs and
  reading back with `ofWP`.
- `quadraticHenselStepBignum` = current body; `quadraticHenselStep` = dispatch;
  reroute the 5 spec theorems through `quadraticHenselStep_eq_bignum`.
- Per-op transport helpers `toWP_{add,sub,mul}ModSquare`,
  `toWP_reduceModSquare`, `ofWP_toWP_reduceModSquare` (canonical readback), and
  `toWP_divModMonicModSquare` (division transport via MonicUnique + the private
  `divModMonicModSquare_reconstruct_congr` and `..._remainder_coeff_eq_zero_of_monic`;
  MUST be placed AFTER those private lemmas, i.e. just before the spec theorems).
- Assembly: `toWP(bignum intermediate) = word intermediate` chained through the
  13 ops (g' done: monic + 0<deg via leading-coeff-at-g.size-1 argument), then
  `ofWP(word out) = bignum out` by canonical round-trip.

### Mathlib-free gotchas for the redo
- NO `set` (use `generalize h : e = x`), NO `ring`/`push_cast`/`nlinarith`/
  `by_contra`/`interval_cases`. Use `grind` for WordMod ring goals but it chokes
  on `Zero.zero` (rw `show (Zero.zero:_)=0 from rfl` first, or a `sub_self` lemma).
- Int emod: dvd-witness + `grind` idiom (`rcases ... ⟨c,hc⟩; exact ⟨witness, by grind⟩`),
  NOT `Int.ModEq` (absent in module prelude). `Int.dvd_add/sub`, `Int.emod_eq_of_lt`,
  `Int.emod_emod_of_dvd _ ⟨1,(Int.mul_one _).symm⟩` for self-mod.
- `m*m` vs `m^2` (reduceModPow uses `m^2`): bridge with `Nat.pow_two` + `exact_mod_cast`.

## Next step

Redo the Quadratic.lean assembly with the above (generalize-based). ~150 lines,
mechanical given the committed transport. Then re-measure SD4.
