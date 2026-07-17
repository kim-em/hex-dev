# Descartes sign-variation parity (two-circle campaign TC-2)

## Accomplished

Added `HexRealRootsMathlib/DescartesParity.lean` (Hex-free, `public import
Mathlib` only), the parity companion to Mathlib's inequality
`Polynomial.roots_countP_pos_le_signVariations`. Main result:

- `signVariations_parity (P : ℝ[X]) (hP : P ≠ 0) :
  P.roots.countP (0 < ·) ≡ P.signVariations [MOD 2]`.

Both sides are shown congruent mod two to the same end-sign indicator
`if sign P.leadingCoeff = sign P.trailingCoeff then 0 else 1`:

- `signVariations_modTwo` — induction over `eraseLead` via
  `signVariations_eq_eraseLead_add_ite`, using the new structural lemma
  `trailingCoeff_eraseLead` (eraseLead leaves the trailing coeff fixed).
- `countP_pos_modTwo` — reduce to monic (`C u * P`, `u = (lc)⁻¹`), then
  `countP_pos_modTwo_monic` peels monic factors of degree 1 or 2 via
  `IsMonicOfDegree.eq_isMonicOfDegree_one_or_two_mul`. Degree-1 leaf: root
  sign vs `sign(-r)`. Degree-2 leaf: split case reuses the degree-1 leaf;
  irreducible case shows `trailingCoeff > 0` via `discrim < 0`
  (`exists_quadratic_eq_zero` + `Real.sqrt`).

Exported consequences for TC-5:
- `countP_pos_eq_zero_of_signVariations_eq_zero`
- `countP_pos_eq_one_of_signVariations_eq_one`

Appended the umbrella import line to `HexRealRootsMathlib.lean`.

## Current frontier

`lake build HexRealRootsMathlib` green; `check_dag.py` exit 0;
`#print axioms signVariations_parity` = `[propext, Classical.choice,
Quot.sound]` (sorry-free). Stated over `ℝ`.

## Next step

TC-5 can now cite the two consequence lemmas from the engine termination
proof.

## Blockers

None.
