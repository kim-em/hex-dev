# Stage 3b: squarefree-core root transfer

## Accomplished

- Proved `HexRealRootsMathlib.aevalIff_squareFreeCore` (SPEC contract in
  `SPEC/Libraries/hex-real-roots-mathlib.md`): a nonzero integer polynomial
  and its executable square-free core share exactly the same real roots,
  through `aeval` at real points. No `sorry`/`axiom`/`native_decide`; the
  proof cone is `[propext, Classical.choice, Quot.sound]`.
- New module `HexRealRootsMathlib/SquareFreeCore.lean`, added to the umbrella.
  Contains:
  - `isRoot_left_iff_of_mul_of_dvd_derivative` — the field-generic, Hex-free
    lemma (char-zero field, `q = c * r`, `r ∣ q'` ⇒ `c` and `q` share roots),
    a clean root-multiplicity argument. Upstreamable to Mathlib as stated.
  - cast helpers `aeval_eq_eval_toPolyℝ`, `toPolyℝ_mul`,
    `toPolyℝ_eq_map_toPolyℚ`, and `toPolyℝ_repeatedPart_dvd_derivative`
    (executable ℚ divisibility → ℝ).
- Executable support lemmas in `HexPolyZ/Decomposition.lean`:
  `squareFreeCore_ne_zero`, `squareFreeRat_squareFreeCore`,
  `toRatPoly_repeatedPart_dvd_derivative` (repeated part is a rational
  associate of `gcd(prim, prim')`, which divides `prim'`), plus the
  definitional bridge `squareFreeCore_eq`. Exposed `squareFreeCore` in
  `HexPolyZ/Core.lean`.

## Current frontier

- `lake build` (full) verification in progress; per-module builds of
  `HexPolyZ.Decomposition` and `HexRealRootsMathlib.SquareFreeCore` are green.

## Next step

- Stage 3c/elaborator work (`IsolateRoots.lean`, `IsolatedRealRoots`,
  `isolate_roots` term elaborator) consumes `aevalIff_squareFreeCore` +
  the two support lemmas via `congrRoots` — separate unit.

## Blockers

- None. Key Mathlib lemmas that did the heavy lifting:
  `Polynomial.rootMultiplicity_mul`, `derivative_rootMultiplicity_of_root`
  (CharZero), `rootMultiplicity_le_rootMultiplicity_of_dvd`,
  `eq_C_of_derivative_eq_zero`.
