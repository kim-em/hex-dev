/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

-- PLAIN `public import` only: NO `import all`. The emitted `decide`s must reduce
-- in the kernel through the exposed count-check closure and the `SturmChainCert` /
-- `orderedAdjacent` certificates alone, exactly as a downstream `module` consumer
-- of the `isolate_roots` elaborator would see them.
public import HexRealRootsMathlib.IsolateRootsElab

public section

open Hex Polynomial HexRealRootsMathlib

namespace HexRealRootsMathlib.ElabTests

/-! ## `x⁴ − 2` -/

/-- `x⁴ − 2` as a `Hex.ZPoly`. -/
def x4m2 : ZPoly := DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1]

/-- Bare isolation of `x⁴ − 2` as a `ZPoly`. -/
noncomputable def iso_zpoly := isolate_roots x4m2

/-- `x⁴ − 2` over `Polynomial ℝ`, bare. -/
noncomputable def iso_real := isolate_roots (X ^ 4 - 2 : Polynomial ℝ)

/-- `x⁴ − 2`, every root refined to width `2^(-20)`. -/
noncomputable def iso_w20 := isolate_roots (width := 2 ^ (-20 : ℤ)) (X ^ 4 - 2 : Polynomial ℝ)

/-- `x⁴ − 2`, width `1/1000`. -/
noncomputable def iso_w1000 := isolate_roots (width := 1 / 1000) (X ^ 4 - 2 : Polynomial ℝ)

/-- `x⁴ − 2`, width `10^(-2)`. -/
noncomputable def iso_w100 := isolate_roots (width := 10 ^ (-2 : ℤ)) (X ^ 4 - 2 : Polynomial ℝ)

/-- `x⁴ − 2` as a `ZPoly`, refined to width `2^(-20)`. -/
noncomputable def iso_zpoly_w20 := isolate_roots (width := 2 ^ (-20 : ℤ)) x4m2

/-! ## Coefficient rings -/

/-- Wilkinson-6 `∏_{i=1}^{6}(x − i)` over `Polynomial ℤ`. -/
noncomputable def iso_wilkinson :=
  isolate_roots ((X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5) * (X - 6) : Polynomial ℤ)

/-- A `Polynomial ℚ` case: `2x² − 3x + 1 = (2x − 1)(x − 1)`. -/
noncomputable def iso_rat := isolate_roots (2 * X ^ 2 - 3 * X + 1 : Polynomial ℚ)

/-! ## Non-squarefree (exercises the core transport) -/

/-- `(x − 1)²(x − 3)` over `Polynomial ℤ`: two distinct real roots. -/
noncomputable def iso_nonsqfree :=
  isolate_roots ((X - 1) ^ 2 * (X - 3) : Polynomial ℤ)

/-! ## Nonzero constant -/

/-- A nonzero constant has no real roots: the empty isolation. -/
noncomputable def iso_const := isolate_roots (7 : Polynomial ℝ)

/-! ## Consumption demos -/

/-- `obtain` the four fields directly out of the elaborator's result. -/
example : True := by
  obtain ⟨v, hu, hc, ho⟩ := isolate_roots (X ^ 4 - 2 : Polynomial ℝ)
  trivial

/-- A `have` binding of the result, then use of a field. -/
example : True := by
  have H := isolate_roots x4m2
  have := H.covers
  trivial

/-- Feed the isolation's fields to `grind`. `grind` digests the `ordered` field
into the pairwise-disjointness statement (the `covers`/`unique_root` existentials
are consumed with `exact`, as `grind` does not synthesise their witnesses). -/
example : True := by
  have H := isolate_roots (X ^ 4 - 2 : Polynomial ℝ)
  have hord := H.ordered
  have _key : ∀ i j : Fin H.intervals.toArray.size, i < j →
      (H.intervals[i].2 : ℚ) ≤ (H.intervals[j].1 : ℚ) := by grind
  trivial

/-! ## Error taxonomy (deliverable 6)

Each distinct diagnostic is pinned with `#guard_msgs`. The internal
certificate-mismatch path (`radicalCert` reassembly failure) is a defensive code
assertion that cannot fire on valid input without a contrived hook, so it is
documented rather than tested. -/

section Errors
variable (p : Hex.ZPoly) (w : ℚ)

/-- info: isolate_roots: the zero polynomial (every real number is a root, so there is no finite isolation) -/
#guard_msgs in
#check_failure (isolate_roots (0 : Polynomial ℤ))

/--
info: isolate_roots: non-integer coefficient
  1 / 2
-/
#guard_msgs in
#check_failure (isolate_roots (X + Polynomial.C (1 / 2 : ℚ) : Polynomial ℚ))

/--
info: isolate_roots: unsupported polynomial syntax
  (monomial 2) 3
-/
#guard_msgs in
#check_failure (isolate_roots (Polynomial.monomial 2 3 : Polynomial ℤ))

/--
info: isolate_roots: the polynomial must be a closed term (no free variables or metavariables)
  p
-/
#guard_msgs in
#check_failure (isolate_roots p)

/--
info: isolate_roots: the width must be a closed rational (no free variables or metavariables)
  w
-/
#guard_msgs in
#check_failure (isolate_roots (width := w) (X ^ 2 - 2 : Polynomial ℤ))

/-- info: isolate_roots: the width must be strictly positive -/
#guard_msgs in
#check_failure (isolate_roots (width := 0) (X ^ 2 - 2 : Polynomial ℤ))

/-- info: isolate_roots: pathological width (finer than 2^-4096); the isolation would be astronomically large. Refine the result manually if you truly need this. -/
#guard_msgs in
#check_failure (isolate_roots (width := 2 ^ (-5000 : ℤ)) (X ^ 2 - 2 : Polynomial ℤ))

end Errors

end HexRealRootsMathlib.ElabTests

/-! ### Review-hardening tests: dispatch, certification link, and taxonomy
completeness (from the Codex review of #8843). -/

/-- error: isolate_roots: expected a closed `Hex.ZPoly` or `Polynomial ℤ/ℚ/ℝ` term, but the argument has type
  ℕ -/
#guard_msgs in
noncomputable example := isolate_roots (37 : Nat)

/-- error: isolate_roots: unsupported coefficient ring
  ℕ
expected `Polynomial ℤ`, `Polynomial ℚ`, or `Polynomial ℝ` (with integer coefficients) -/
#guard_msgs in
noncomputable example := isolate_roots ((Polynomial.X : Polynomial ℕ) + 1)

@[irreducible] private def secretExp : Nat := 2

/-- error: isolate_roots: not a Nat literal
  secretExp -/
#guard_msgs in
noncomputable example := isolate_roots ((Polynomial.X : Polynomial ℤ) ^ secretExp - 2)

@[irreducible] private def hiddenZ : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 1]

/-- error: isolate_roots: cannot certify that the evaluated polynomial is definitionally the supplied term (is the definition irreducible?)
⊢ ∀ (x : ℝ),
    (aeval x) (HexPolyZMathlib.toPolynomial (DensePoly.ofCoeffs #[-2, 0, 0, 0, 1])) = 0 ↔
      (aeval x) (HexPolyZMathlib.toPolynomial hiddenZ) = 0 -/
#guard_msgs in
noncomputable example := isolate_roots hiddenZ

/-- A plain (delta-reducible) named `ZPoly` def: the result is stated over
the USER'S name, with the evaluation certified by the kernel's defeq check. -/
private def openZ : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[-2, 0, 0, 0, 1]

noncomputable example :
    Hex.IsolatedRealRoots (HexPolyZMathlib.toPolynomial openZ) 2 :=
  isolate_roots openZ

/-- The `intervals` field is definitionally a literal vector of pretty
rationals: extraction is `rfl`, even for refined (fractional) endpoints.
No `Rat` normalization stands between the user and the endpoints. -/
noncomputable example : Hex.IsolatedRealRoots (X ^ 4 - 2 : Polynomial ℝ) 2 :=
  isolate_roots (X ^ 4 - 2 : Polynomial ℝ)

example :
    (isolate_roots (X ^ 4 - 2 : Polynomial ℝ) :
      Hex.IsolatedRealRoots (X ^ 4 - 2 : Polynomial ℝ) 2).intervals =
    #v[((-4 : ℚ), (0 : ℚ)), ((0 : ℚ), (4 : ℚ))] := rfl

example :
    (isolate_roots (width := 2 ^ (-20 : ℤ)) (X ^ 4 - 2 : Polynomial ℝ) :
      Hex.IsolatedRealRoots (X ^ 4 - 2 : Polynomial ℝ) 2).intervals =
    #v[((-1246975 / 2 ^ 20 : ℚ), (-623487 / 2 ^ 19 : ℚ)),
       ((623487 / 2 ^ 19 : ℚ), (1246975 / 2 ^ 20 : ℚ))] := rfl

/-- A nonconstant polynomial with no real roots: `n = 0`, and the empty
interval vector still extracts by `rfl`. -/
example :
    (isolate_roots ((X : Polynomial ℝ) ^ 2 + 1) :
      Hex.IsolatedRealRoots ((X : Polynomial ℝ) ^ 2 + 1) 0).intervals =
    #v[] := rfl

/-- `rfl` extraction through BOTH `congrRoots` layers: a non-squarefree
input takes the radical-certificate transport and the Polynomial input
takes the evaluation transport, and the intervals stay literal. -/
example :
    (isolate_roots ((X - 1) ^ 2 * (X - 3) : Polynomial ℝ) :
      Hex.IsolatedRealRoots ((X - 1) ^ 2 * (X - 3) : Polynomial ℝ) 2).intervals =
    #v[((0 : ℚ), (2 : ℚ)), ((2 : ℚ), (4 : ℚ))] := rfl
