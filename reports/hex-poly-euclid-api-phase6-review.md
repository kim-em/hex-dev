# HexPoly Euclid/GCD API Phase 6 Review

## Scope

Reviewed the executable Euclidean-algorithm surface in `HexPoly/Euclid.lean`
against `SPEC/Libraries/hex-poly.md` and `PLAN/Phase6.md`. The sibling report
`reports/hex-poly-operations-api-phase6-review.md` already covered arithmetic
operations; this review focuses on:

- `leadingCoeff` / `Monic` predicate;
- field-style long division (`divMod`, `divModArray`, `div`, `mod`) and the
  monic variant (`divModMonic`, `modByMonic`);
- gcd and extended gcd (`gcd`, `xgcd`, `XGCDResult`);
- the `DivModLaws` and `GcdLaws` law packages;
- integer content / primitive-part helpers (`content`, `primitivePart`);
- the existential polynomial CRT construction (`polyCRT`) and its `mod` /
  `modByMonic` reductions;
- downstream consumers in `HexPolyFp/`, `HexPolyZ/`, `HexPolyMathlib/`,
  `HexHensel/`, `HexBerlekamp/`, and `HexBerlekampZassenhaus/`.

This is a review-only Phase 6 slice. It does not edit Lean source.

## Summary

The Euclidean layer follows the same general shape as the arithmetic layer:
executable definitions ship with characterizing theorems, and downstream
correctness goes through law-package classes (`DivModLaws`, `GcdLaws`) so
consumers reason via named lemmas rather than by unfolding loops. Concretely:

- `divMod_spec`, `gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`, `xgcd_bezout` are
  exposed and stated under the class assumption; coefficient libraries
  (`HexPolyZ/Basic.lean`, `HexPolyFp/Basic.lean`) construct the law instances by
  unfolding the executable definitions exactly once at the law-package
  construction site.
- `polyCRT_mod_fst`, `polyCRT_mod_snd`, `polyCRT_modByMonic_fst`,
  `polyCRT_modByMonic_snd`, plus the underlying `polyCRT_congr_fst` /
  `polyCRT_congr_snd`, give downstream consumers (`HexBerlekamp/RabinSoundness`,
  `HexHensel/Multifactor`) clean access to the CRT residue conditions without
  touching the executable `polyCRT` formula.
- The integer content / Gauss surface (`content_mul`, `content_mul_of_primitive`,
  `content_mul_primitivePart`, `content_dvd_coeff`, `primitivePart_primitive`,
  `primitivePart_eq_self_of_content_eq_one`, `coeff_dvd_of_primitive_mul_coeff_dvd`,
  `exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff`) covers
  Gauss's lemma in both content-multiplicativity and McCoy-annihilator forms.

I found six concrete Phase 6 polish gaps. None are correctness issues.

## Follow-Up Recommendations

### 1. Add named `leadingCoeff` characterizations and `leadingCoeff_mul`

Filed as #6148.

Consumers currently work around the missing characterizations:

- `HexBerlekamp/RabinSoundness.lean:621` reproves
  `(0 : FpPoly p).leadingCoeff = 0` inline.
- `HexBerlekamp/RabinSoundness.lean:1823` unfolds
  `leadingCoeff_eq_coeff_last` plus a local size lemma to compute the leading
  coefficient of `(1 : FpPoly p)`.
- `HexBerlekamp/RabinSoundness.lean:1731-1750` defines a private
  `leadingCoeff_mul_fpoly` proving
  `leadingCoeff (a * b) = leadingCoeff a * leadingCoeff b` for nonzero
  arguments. This is a fundamental polynomial fact and belongs in
  `HexPoly/Euclid.lean`.
- `HexHensel/Linear.lean:1300`, `HexHensel/Quadratic.lean:441`, `:665`, `:2091`,
  and `HexHensel/Basic.lean:353`, `:394` all do
  `simp [DensePoly.leadingCoeff, DensePoly.size]` to reduce to coefficient form.

Recommended additions to `HexPoly/Euclid.lean` near `leadingCoeff`:

- `leadingCoeff_zero : (0 : DensePoly R).leadingCoeff = 0` with `@[simp]`;
- `leadingCoeff_C [DecidableEq R] (c : R) : (C c).leadingCoeff = c` with
  `@[simp]` (or a `_of_ne_zero` variant if normalization complicates this);
- `leadingCoeff_one [One R] [DecidableEq R] : (1 : DensePoly R).leadingCoeff = 1`
  with `@[simp]` (specialised from `leadingCoeff_C`);
- `leadingCoeff_mul` (or `leadingCoeff_mul_of_ne_zero`) over a commutative ring
  with the nonzero-factor hypothesis, replacing the private
  `leadingCoeff_mul_fpoly` in `HexBerlekamp/RabinSoundness.lean`.

Target declaration cluster: `HexPoly/Euclid.lean` `leadingCoeff` block
(lines ~20-48).

### 2. Add a `Monic ↔ leadingCoeff = 1` characterization

Filed as #6149.

`Monic` is `def Monic ... := p.leadingCoeff = 1`. Consumers repeatedly unfold
the definition:

- `HexHensel/Linear.lean:1303`, `:1368`;
- `HexHensel/Quadratic.lean:668`, `:2094`.

Each call site does `simpa [DensePoly.Monic] using hmonic` or similar. A small
forwarding lemma would let consumers keep `Monic` opaque:

```lean
theorem leadingCoeff_eq_one_of_monic [One R] {p : DensePoly R}
    (hp : p.Monic) : p.leadingCoeff = 1 := hp

theorem monic_iff_leadingCoeff_eq_one [One R] {p : DensePoly R} :
    p.Monic ↔ p.leadingCoeff = 1 := Iff.rfl
```

Alternatively, marking `Monic` `@[reducible]` or attaching `@[simp]` to a
definitional equation would also work. The current shape forces every
`Monic` consumer to spell out the unfolding manually.

Target declaration cluster: `HexPoly/Euclid.lean` `Monic` block
(lines ~28-31).

### 3. Add a public `gcd_eq_xgcd_gcd` (or vice versa) bridge

Filed as #6150.

Consumers convert between `DensePoly.gcd p q` and `(DensePoly.xgcd p q).gcd`
by unfolding:

- `HexBerlekamp/RabinSoundness.lean:186` does
  `simpa [DensePoly.gcd] using hgcd` to turn `gcd a b = 1` into
  `(xgcd a b).gcd = 1` so that `xgcd_bezout` can be applied.
- `HexPolyMathlib/Euclid.lean:76` does the same `simpa [Hex.DensePoly.gcd]`
  conversion for the Mathlib-side associated-gcd bridge.

The current `def gcd p q := (xgcd p q).gcd` makes this `rfl`, but exposing it
as a named theorem (e.g. `gcd_eq_xgcd_gcd` or a `@[simp]` equation lemma
`gcd_def`) would keep consumers from reaching into the definition. The same
`xgcd_bezout` call in `HexBerlekamp/RabinSoundness.lean:180-187`
(`xgcd_bezout_of_gcd_eq_one`) is the canonical consumer that this lemma
would simplify.

Target declaration cluster: `HexPoly/Euclid.lean` `gcd` / `xgcd` block
(lines ~826-839).

### 4. Tune `@[simp]` annotations across the Euclidean surface

Filed (jointly with recommendation 5) as #6151.

The Euclidean layer currently has only two `@[simp]` annotations in 5635 lines
(`gcd_zero_zero` at line 837 and `mod_mod` at line 1126). Many obvious
normalization lemmas are candidates:

- `mod_eq_divMod` (line 939): `p % q = (divMod p q).2` — this is the
  definitional reduction for `%` and is used implicitly throughout.
- `modByMonic_eq_divModMonic` (line 921): same `rfl`-level reduction for
  `modByMonic`.
- `modByMonic_eq_mod` (line 1118): collapses monic division to field-style
  `%` under `Monic`.
- `modByMonic_zero` (line 927): `modByMonic 0 q hq = 0`.
- `zero_mod_eq_zero_core` (line 945): `0 % m = 0`.
- `mod_self_eq_zero` (private, line 4761) and the public `DivModLaws.mod_self_eq_zero`
  channel: `m % m = 0`.
- `mod_eq_zero_of_dvd` (line 1113): `q ∣ p → p % q = 0`.
- `div_mul_add_mod` (line 1107): the Euclidean identity — typically not a
  `simp` lemma because it's an introduction, but worth a `@[grind =]`.

Recommended implementation shape:

- annotate the rfl-level reductions (`mod_eq_divMod`, `modByMonic_eq_divModMonic`,
  `mod_eq_divMod` etc.) `@[simp]`;
- annotate the cancellation lemmas (`modByMonic_zero`, `zero_mod_eq_zero_core`,
  `mod_self_eq_zero`, `mod_eq_zero_of_dvd`) `@[simp]`;
- audit each candidate in isolation before landing — `mod` chains can loop
  if `mod_mul_mod` or `mod_add_mod` are added without care.

Target declaration cluster: `HexPoly/Euclid.lean` `divMod` / `mod` /
`modByMonic` blocks (lines ~780-1130).

### 5. Tune `@[grind]` annotations on the algebra-wrapper layer

Filed (jointly with recommendation 4) as #6151.

The Euclidean file currently has zero `@[grind]` annotations. The
operations-side review filed #5971 for the arithmetic layer; the Euclidean
layer has its own `mul_comm_poly`, `mul_assoc_poly`, `mul_add_right_poly`,
`mul_add_left_poly`, `mul_one_right_poly`, `add_comm_poly`, `add_assoc_poly`,
`add_zero_poly`, `sub_eq_add_neg_poly`, `neg_mul_right_poly`, `zero_mul`,
`zero_add`, `dvd_refl_poly`, `dvd_zero_poly`, `dvd_mul_left_poly`,
`dvd_add_poly`, `dvd_sub_poly` cluster (lines ~1405-2700, ~2660-2700) that is a
natural extension of the same annotation review. Many of these are imported
into long proofs in `HexBerlekamp/`, `HexHensel/`, and `HexPolyZ/` and would
benefit from `@[grind =]` on the commute / unit / cancellation directions.

Recommended implementation shape:

- audit `mul_comm_poly`, `mul_assoc_poly`, `add_comm_poly`, `add_assoc_poly`,
  `zero_mul`, `zero_add`, `add_zero_poly`, `mul_one_right_poly`,
  `sub_eq_add_neg_poly`, `neg_mul_right_poly`;
- try conservative `@[grind =]` annotations on directed-rewrite candidates;
- leave any theorem unannotated if it loops or expands search.

Target declaration cluster: `HexPoly/Euclid.lean` commutative-ring algebra
block (lines ~1405-2700).

### 6. Fill docstring gaps on the public Euclidean / Gauss surface

Filed as #6152.

A pass over the file finds ~36 public declarations without docstrings,
out of ~111. Most are clear from name (the algebra wrappers
`mul_comm_poly`, `add_assoc_poly`, etc.), but several `_core` / `_of_divModLaws`
variants are non-obvious without context:

- `divMod_remainder_degree_lt_of_pos_degree_core` (line 668);
- `divMod_remainder_eq_zero_of_degree_zero_core` (line 683);
- `divMod_remainder_eq_self_of_size_zero_core` (line 751);
- `divMod_eq_zero_self_of_size_zero_core` (line 766);
- `divModMonic_eq_divMod_of_monic_core` (line 1059);
- `xgcd_bezout_of_divModLaws` (line 2777);
- `gcd_dvd_left_of_divModLaws` (line 2879);
- `gcd_dvd_right_of_divModLaws` (line 2892);
- `dvd_gcd_of_divModLaws` (line 2905);
- `zero_mod_eq_zero_core` (line 945);
- `divModArray_remainder_degree_lt_of_pos_degree` (line 541);
- `divModArray_eq_zero_self_of_degree_lt` (line 1005);
- the public `XGCDResult` structure (line 807) has a docstring but its fields
  do not.

The `_of_divModLaws` cluster in particular needs documentation explaining its
intended use (proving `GcdLaws` instances from `DivModLaws` + a one-off
`hsmall` hypothesis about degree-zero divisors).

The integer-content lemma cluster (`content_zero`, `content_C`,
`content_mul_primitivePart`, `content_scale_neg_one`, `scale_neg_one_zero`,
`primitivePart_eq_zero_of_content_eq_zero`, and the four
`dvd_content_of_nat_dvd_coeff` / `nat_eq_one_of_content_eq_one_of_nat_dvd_coeff`
variants between lines 4310-4621) also need short docstrings; their names
are mostly self-explanatory but each has a sign / nonzero precondition that
is worth noting.

Recommended implementation shape:

- one-line docstrings on each non-obvious `_core` / `_of_divModLaws`
  variant explaining the "weak hypothesis, used to build the law instance"
  role;
- a sentence each on the `content_*` and `primitivePart_*` cluster naming
  the precondition;
- structure-field docstrings on `XGCDResult.gcd`, `.left`, `.right`.

Target declaration cluster: file-wide, but concentrated in the
`_of_divModLaws` cluster (lines ~2777-2911), the `_core` variants in the
field-division block (lines ~668-1059), and the `content_*` /
`primitivePart_*` block (lines ~4310-4646).

## No Follow-Up Needed

No follow-up is needed for:

- The law-package design (`DivModLaws`, `GcdLaws`): the class-based split
  cleanly separates executable arithmetic from correctness obligations, and
  downstream consumers (`HexPolyFp/Basic.lean`, `HexPolyZ/Basic.lean`) build
  instances exactly once at the coefficient library boundary.
- The `polyCRT` API surface: `polyCRT_congr_fst`, `polyCRT_congr_snd`,
  `polyCRT_mod_fst`, `polyCRT_mod_snd`, `polyCRT_modByMonic_fst`,
  `polyCRT_modByMonic_snd` cover both the `mod` and `modByMonic` consumer
  needs, and `HexBerlekamp/RabinSoundness.lean` uses them cleanly.
- The Gauss/McCoy content surface: the file exposes both the
  content-multiplicativity form (`content_mul`, `content_mul_of_primitive`)
  and the McCoy annihilator form
  (`exists_scalar_annihilator_of_mul_coeff_dvd_of_exists_not_dvd_coeff`,
  `coeff_dvd_of_primitive_mul_coeff_dvd`). Consumers in `HexPolyZ/Basic.lean`
  thread through the named theorems.
- The `Congr` / `mod_eq_mod_iff_congr` characterization: the equivalence
  is exposed in both directions and is used cleanly by Hensel and Berlekamp
  consumers.
- Imports: the file imports only `Init.Grind.Ring.Basic`,
  `Init.Data.List.Lemmas`, and `HexPoly.Operations`, and stays under
  `Hex.DensePoly`. No namespace pollution.

## Verification

Checked for overlapping open follow-up work with:

- `coordination list-unclaimed`
- `gh issue list --state open --label agent-plan --search "HexPoly Phase 6"`
- `gh issue list --state open --search "DensePoly leadingCoeff"`
- `gh issue list --state open --search "polyCRT OR xgcd_gcd OR Monic_iff"`

Before filing the follow-ups (#6148-#6152), the only open Phase-6 HexPoly
issue was this review (#6140). The operations-side companion follow-ups
(#5970, #5971) are independent — #5971 addresses arithmetic-layer
`@[grind]` annotations, while #6151 above proposes the parallel pass on
the Euclidean-layer algebra wrappers.
