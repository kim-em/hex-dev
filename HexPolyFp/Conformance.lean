import HexPolyFp.Frobenius
import HexPolyFp.ModCompose
import HexPolyFp.SquareFree

/-!
Core conformance checks for the `HexPolyFp` Frobenius, modular-composition,
and square-free decomposition surface.

Oracle: none
Mode: always
Covered operations:
- `powModMonic`
- `frobeniusXMod`
- `frobeniusXPowMod`
- `composeModMonic`
- `squareFreeDecomposition`
- `weightedProduct`
Covered properties:
- modular exponentiation by exponent zero returns the quotient-ring identity
- Frobenius-power exponent zero agrees with reduction of `X`
- composition with the identity polynomial reduces the source polynomial
- composition of the zero polynomial is zero
- square-free decompositions reconstruct the input from the unit and weighted factors
- weighted products respect positive multiplicities
Covered edge cases:
- constant monic modulus `1`
- the indeterminate `X` and constant polynomial inputs
- reductions modulo `x^2 + 2` over `F_5`
- linear modulus `x + 3` over `F_5`
- reductions modulo a degree-6 modulus (matches the SPEC `core`
  finite-field-extension upper end)
- degree-10 polynomial inputs to `powModMonic`, `composeModMonic`,
  `squareFreeDecomposition`, and `weightedProduct` (matches the SPEC
  `core` polynomial-degree upper end)
- sparse inputs with internal zero coefficients at degree 10
- square-free decomposition with mixed multiplicities `(2, 3)` from a
  product of four distinct linear factors
- square-free, repeated-factor, derivative-zero, zero, and scalar square-free inputs
-/

namespace Hex
namespace FpPoly

private instance conformanceBoundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem one_ne_zero_five : (1 : ZMod64 5) ≠ 0 := by
  intro h
  have hm := (ZMod64.natCast_eq_natCast_iff (p := 5) 1 0).mp h
  simp at hm

private theorem prime_five : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private def polyFive (coeffs : Array Nat) : FpPoly 5 :=
  ofCoeffs (coeffs.map (fun n => ZMod64.ofNat 5 n))

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def sfFactorFive (coeffs : Array Nat) (multiplicity : Nat) : SquareFreeFactor 5 :=
  { factor := polyFive coeffs, multiplicity }

private def sfSummary (d : SquareFreeDecomposition 5) : Nat × List (List Nat × Nat) :=
  (d.unit.toNat, d.factors.map (fun sf => (coeffNats sf.factor, sf.multiplicity)))

private def sfReconstruction (d : SquareFreeDecomposition 5) : FpPoly 5 :=
  DensePoly.C d.unit * weightedProduct d.factors

private def constModulus : FpPoly 5 :=
  { coeffs := #[(1 : ZMod64 5)]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem constModulus_monic : DensePoly.Monic constModulus := by
  rfl

private def linearModulus : FpPoly 5 :=
  { coeffs := #[(3 : ZMod64 5), 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem linearModulus_monic : DensePoly.Monic linearModulus := by
  rfl

private def quadModulus : FpPoly 5 :=
  { coeffs := #[(2 : ZMod64 5), 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem quadModulus_monic : DensePoly.Monic quadModulus := by
  rfl

-- `#eval` requires all of `DensePoly`'s propositional fields to be
-- non-sorry; `DensePoly.ofCoeffs` currently has a sorry-backed proof field.
/-- info: [0, 1] -/
#guard_msgs in
#eval! coeffNats (powModMonic (polyFive #[1, 1]) quadModulus quadModulus_monic 3)

#guard coeffNats (powModMonic (polyFive #[4, 2]) constModulus constModulus_monic 5) = []
#guard coeffNats (powModMonic (polyFive #[0, 0, 1]) quadModulus quadModulus_monic 0) = [1]
#guard coeffNats (powModMonic (polyFive #[0, 0, 1]) quadModulus quadModulus_monic 4) = [1]

/-- info: [0, 4] -/
#guard_msgs in
#eval! coeffNats (frobeniusXMod quadModulus quadModulus_monic)

#guard coeffNats (frobeniusXMod constModulus constModulus_monic) = []
#guard coeffNats (frobeniusXMod linearModulus linearModulus_monic) = [2]

/-- info: [0, 1] -/
#guard_msgs in
#eval! coeffNats (frobeniusXPowMod quadModulus quadModulus_monic 0)

#guard coeffNats (frobeniusXPowMod constModulus constModulus_monic 3) = []
#guard coeffNats (frobeniusXPowMod linearModulus linearModulus_monic 2) = [2]

/-- info: [4, 4] -/
#guard_msgs in
#eval! coeffNats
    (composeModMonic (polyFive #[3, 2, 1]) (polyFive #[1, 1]) quadModulus
      quadModulus_monic)

#guard coeffNats
    (composeModMonic (polyFive #[2, 4]) (polyFive #[3, 1]) constModulus
      constModulus_monic) = []
#guard coeffNats (composeModMonic (polyFive #[0, 0, 1]) X quadModulus quadModulus_monic) =
  [3]
#guard composeModMonic 0 (polyFive #[1, 1]) quadModulus quadModulus_monic = 0
#guard composeModMonic (polyFive #[0, 0, 1]) X quadModulus quadModulus_monic =
  modByMonic quadModulus (polyFive #[0, 0, 1]) quadModulus_monic

/-- info: [1, 1, 1] -/
#guard_msgs in
#eval! coeffNats (weightedProduct [sfFactorFive #[4, 4, 4] 1, sfFactorFive #[2] 2])

#guard coeffNats (weightedProduct [sfFactorFive #[1, 1] 2]) = [1, 2, 1]
#guard coeffNats (weightedProduct [sfFactorFive #[1, 1] 5]) = [1, 0, 0, 0, 0, 1]
#guard coeffNats (weightedProduct ([] : List (SquareFreeFactor 5))) = [1]

/-- info: (1, [([4, 4, 4], 1), ([2], 2)]) -/
#guard_msgs in
#eval! sfSummary (squareFreeDecomposition prime_five (polyFive #[1, 1, 1]))

#guard
  let f := polyFive #[1, 1, 1]
  coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

/-- info: (1, [([4], 1), ([2, 2], 2)]) -/
#guard_msgs in
#eval! sfSummary (squareFreeDecomposition prime_five (polyFive #[1, 2, 1]))

#guard
  let f := polyFive #[1, 2, 1]
  coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

/-- info: (1, [([1, 1], 5)]) -/
#guard_msgs in
#eval! sfSummary (squareFreeDecomposition prime_five (polyFive #[1, 0, 0, 0, 0, 1]))

#guard
  let f := polyFive #[1, 0, 0, 0, 0, 1]
  coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

#guard sfSummary (squareFreeDecomposition prime_five (0 : FpPoly 5)) = (0, [])
#guard
  let f := polyFive #[3]
  sfSummary (squareFreeDecomposition prime_five f) = (3, []) ∧
    coeffNats (sfReconstruction (squareFreeDecomposition prime_five f)) = coeffNats f

/-!
Degree-10 / extension-degree-6 fixtures matching the SPEC `core`
profile-size upper end (polynomial degrees `8-12`, finite-field
extensions up to degree `6`). These scale the typical / edge /
adversarial cases above without dropping any of the smaller cases.

- `bigModulus` — degree-6 monic `x^6 + 2x + 3`, the upper end of the
  finite-field extension band.
- `bigInput` — typical degree-10 polynomial `x^10 + 2x^5 + 3` (dense
  enough to exercise reduction beyond the modulus degree).
- `bigSparse` — adversarial degree-10 polynomial with internal zeros
  `2x^10 + 3x^4 + x` (shape mirrors the smaller sparse fixtures).
- `sfBigFactors` — four distinct linear factors with mixed
  multiplicities `(x+1)^2 (x+2)^3 (x+3)^2 (x+4)^3`. The product has
  degree 10; same-multiplicity factors aggregate as
  `((x+1)(x+3))^2 ((x+2)(x+4))^3 = (x^2+4x+3)^2 (x^2+x+3)^3`.
-/

private def bigModulus : FpPoly 5 :=
  -- x^6 + 2x + 3
  { coeffs := #[(3 : ZMod64 5), 2, 0, 0, 0, 0, 1]
    normalized := by
      right
      simpa using one_ne_zero_five }

private theorem bigModulus_monic : DensePoly.Monic bigModulus := by
  rfl

private def bigInput : FpPoly 5 :=
  -- x^10 + 2x^5 + 3
  polyFive #[3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1]

private def bigSparse : FpPoly 5 :=
  -- 2x^10 + 3x^4 + x
  polyFive #[0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 2]

private def sfBigFactors : List (SquareFreeFactor 5) :=
  [sfFactorFive #[1, 1] 2,  -- (x + 1)^2
   sfFactorFive #[2, 1] 3,  -- (x + 2)^3
   sfFactorFive #[3, 1] 2,  -- (x + 3)^2
   sfFactorFive #[4, 1] 3]  -- (x + 4)^3

private def sfBigInput : FpPoly 5 := weightedProduct sfBigFactors

/-- info: [3, 2, 0, 0, 0, 0, 1] -/
#guard_msgs in
#eval! coeffNats bigModulus

/-- info: [3, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1] -/
#guard_msgs in
#eval! coeffNats bigInput

/-- info: [0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 2] -/
#guard_msgs in
#eval! coeffNats bigSparse

#guard coeffNats (powModMonic bigInput bigModulus bigModulus_monic 0) = [1]
#guard coeffNats (powModMonic 0 bigModulus bigModulus_monic 7) = []

-- `bigInput` reduces from degree 10 down into the degree-6 quotient ring.
/-- info: [3, 0, 0, 0, 2] -/
#guard_msgs in
#eval! coeffNats (powModMonic bigInput bigModulus bigModulus_monic 1)

/-- info: [3, 0, 1, 2, 3, 4] -/
#guard_msgs in
#eval! coeffNats (powModMonic bigInput bigModulus bigModulus_monic 5)

/-- info: [2, 0, 4, 4, 1, 1] -/
#guard_msgs in
#eval! coeffNats (powModMonic bigSparse bigModulus bigModulus_monic 3)

-- `frobeniusXMod` returns `x^5` (degree 5 < 6) so no modular reduction occurs.
/-- info: [0, 0, 0, 0, 0, 1] -/
#guard_msgs in
#eval! coeffNats (frobeniusXMod bigModulus bigModulus_monic)

-- `frobeniusXPowMod _ _ 2` returns `x^25 mod (x^6 + 2x + 3)`, exercising the
-- degree-25 → degree-≤5 reduction loop.
/-- info: [0, 1, 1, 1, 1, 1] -/
#guard_msgs in
#eval! coeffNats (frobeniusXPowMod bigModulus bigModulus_monic 2)

#guard coeffNats (frobeniusXPowMod bigModulus bigModulus_monic 0) = [0, 1]

-- `composeModMonic bigInput X` is `bigInput mod bigModulus` since `f ∘ X = f`.
/-- info: [3, 0, 0, 0, 2] -/
#guard_msgs in
#eval! coeffNats (composeModMonic bigInput X bigModulus bigModulus_monic)

-- `composeModMonic bigInput (x + 1)` is `bigInput(x + 1) mod bigModulus`,
-- exercising both the substitution and the modular reduction.
/-- info: [1, 0, 0, 0, 2, 2] -/
#guard_msgs in
#eval! coeffNats (composeModMonic bigInput (polyFive #[1, 1]) bigModulus bigModulus_monic)

#guard composeModMonic 0 bigInput bigModulus bigModulus_monic = 0

-- `sfBigInput = (x+1)^2 (x+2)^3 (x+3)^2 (x+4)^3` is degree 10 over F_5.
/-- info: [3, 1, 1, 0, 4, 3, 3, 0, 3, 1, 1] -/
#guard_msgs in
#eval! coeffNats sfBigInput

-- Same-multiplicity factors aggregate: mult-2 part is
-- `3·((x+1)(x+3)) = 3·(x^2 + 4x + 3)` and mult-3 part is
-- `4·((x+2)(x+4)) = 4·(x^2 + x + 3)`. Unit `3^2·4^3 = 576 ≡ 1 (mod 5)`.
/-- info: (1, [([4, 2, 3], 2), ([2, 4, 4], 3)]) -/
#guard_msgs in
#eval! sfSummary (squareFreeDecomposition prime_five sfBigInput)

#guard
  coeffNats (sfReconstruction (squareFreeDecomposition prime_five sfBigInput)) =
    coeffNats sfBigInput

end FpPoly
end Hex
